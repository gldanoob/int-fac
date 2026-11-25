import Cogentic.BackSubstitutionBounds

namespace Cogentic.Elimination

/-- Dot product with one rational multiplication and addition per term. -/
private def countedDot : (n : ℕ) → (Fin n → ℤ) → (Fin n → ℚ) → ℚ × ℕ
  | 0, _, _ => (0, 0)
  | n+1, a, x =>
    let tail := countedDot n (fun i => a i.succ) (fun i => x i.succ)
    ((a 0 : ℚ)*x 0 + tail.1, 2+tail.2)

private theorem countedDot_eq (n : ℕ) (a : Fin n → ℤ) (x : Fin n → ℚ) :
    countedDot n a x = (∑ i, (a i : ℚ)*x i, 2*n) := by
  induction n with
  | zero => simp [countedDot]
  | succ n ih => simp [countedDot, ih, Fin.sum_univ_succ, Nat.mul_succ, Nat.add_comm]

/-- An instrumented fill function for the same returned family. Its counter
measures rational addition, subtraction, multiplication and division. -/
structure FillCounter (n : ℕ) where
  family : Family n
  fill : (Fin family.free → ℚ) → Vector ℚ n × ℕ
  value : ∀ y, (fill y).1 = family.fill y
  work : ∀ y, (fill y).2 ≤ n*(n+1)
  arity : family.free ≤ n

private def FillCounter.empty : FillCounter 0 where
  family := emptyFamily
  fill := fun _ => (Vector.ofFn Fin.elim0, 0)
  value := fun _ => rfl
  work := fun _ => by decide
  arity := by decide

private def FillCounter.freeLift {n : ℕ} (c : FillCounter n) : FillCounter (n+1) where
  family := Elimination.freeLift c.family
  fill := fun y =>
    let tail := c.fill (fun i => y i.succ)
    (Vector.ofFn (Fin.cons (y (0 : Fin (c.family.free+1))) tail.1.get), tail.2)
  value := fun y => by simp [Elimination.freeLift, c.value]
  work := fun y => by
    have h := c.work (fun i => y i.succ)
    dsimp only
    nlinarith
  arity := Nat.succ_le_succ c.arity

private def FillCounter.pivotLift {n : ℕ} (p : Row (n+1)) (c : FillCounter n) : FillCounter (n+1) where
  family := Elimination.pivotLift p c.family
  fill := fun y =>
    let tail := c.fill y
    let dot := countedDot n p.drop.coeffs.get tail.1.get
    let head := ((p.rhs : ℚ)-dot.1)/p.head
    (Vector.ofFn (Fin.cons head tail.1.get), tail.2+dot.2+2)
  value := fun y => by
    simp only [countedDot_eq, Elimination.pivotLift, Row.recover, Row.eval]
    rw [c.value y]
  work := fun y => by
    simp only [countedDot_eq]
    have h := c.work y
    nlinarith
  arity := Nat.le_succ_of_le c.arity

/-- Attach the instrumented closures at exactly the free and pivot lifts taken
by solve. No closure is returned when the solver reports inconsistency. -/
def solveWithFillCounter : (n : ℕ) → List (Row n) → Option (FillCounter n)
  | 0, rows => if rows.all (fun r => r.rhs == 0) then some .empty else none
  | n+1, rows =>
    match rows.find? (fun r => r.head != 0) with
    | none => (solveWithFillCounter n (rows.map Row.drop)).map FillCounter.freeLift
    | some p => (solveWithFillCounter n (rows.map p.reduce)).map (FillCounter.pivotLift p)

theorem solveWithFillCounter_value (n : ℕ) (rows : List (Row n)) :
    (solveWithFillCounter n rows).map FillCounter.family = solve n rows := by
  induction n with
  | zero => simp only [solveWithFillCounter, solve]; split <;> rfl
  | succ n ih =>
    rw [solveWithFillCounter, solve]
    cases rows.find? (fun r => r.head != 0) with
    | none =>
      rw [← ih (rows.map Row.drop)]
      simp [Option.map_map, Function.comp_def, FillCounter.freeLift]
    | some p =>
      dsimp only
      rw [← ih (rows.map p.reduce)]
      simp [Option.map_map, Function.comp_def, FillCounter.pivotLift]

def FillCounter.point {n} (c : FillCounter n) : Vector ℚ n × ℕ := c.fill (fun _ => 0)

def FillCounter.direction {n} (c : FillCounter n) (j : Fin c.family.free) : Vector ℚ n × ℕ :=
  let unit := c.fill (fun i => if i=j then 1 else 0)
  let zero := c.point
  (Vector.ofFn (fun i => unit.1.get i - zero.1.get i), unit.2+zero.2+n)

/-- A materialized point needs one fill. A materialized direction uses the
two fills in Family.direction plus one rational subtraction per coordinate. -/
theorem FillCounter.point_direction_cost {n} (c : FillCounter n) :
    (∀ i, c.point.1.get i = c.family.point i) ∧ c.point.2 ≤ n*(n+1) ∧
    ∀ j, (∀ i, (c.direction j).1.get i = c.family.direction j i) ∧
      (c.direction j).2 ≤ 2*n*(n+1)+n := by
  refine ⟨fun i => ?_, c.work _, fun j => ⟨fun i => ?_, ?_⟩⟩
  · simp [FillCounter.point, Family.point, Family.values, c.value]
  · simp [FillCounter.direction, FillCounter.point, Family.direction, Family.point,
      Family.values, c.value, Vector.get_eq_getElem]
  · have h := c.work (fun i => if i=j then 1 else 0)
    have z := c.work (fun _ => 0)
    dsimp only [FillCounter.direction, FillCounter.point]
    nlinarith

/-- An exponent bounding the common-denominator height of a filled family. -/
def fillExponent (n m H : ℕ) : ℕ :=
  (n+1).size*(n+1) + ((m+1).size+H.size)*(m+1)*n

private theorem factorial_exp (k : ℕ) : k.factorial ≤ 2^(k.size*k) := by
  calc
    _ ≤ k^k := Nat.factorial_le_pow _
    _ ≤ (2^k.size)^k := Nat.pow_le_pow_left (Nat.lt_size_self k).le _
    _ = _ := by rw [←pow_mul]

theorem fill_height_exp (n m H : ℕ) :
    (n+1).factorial*((m+1).factorial*H^(m+1))^n ≤ 2^(fillExponent n m H) := by
  have hH : H^(m+1) ≤ 2^(H.size*(m+1)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_size_self H).le _
  have hC := Nat.mul_le_mul (factorial_exp (m+1)) hH
  rw [←pow_add, ←Nat.add_mul] at hC
  have cap := Nat.mul_le_mul (factorial_exp (n+1)) (Nat.pow_le_pow_left hC n)
  simpa only [fillExponent, ←pow_mul, ←pow_add] using cap

private theorem fraction_num_den_bits {n h E : ℕ} {x : Fin n → ℚ}
    (frac : BoundedFraction x (h : ℤ)) (bound : h ≤ 2^E) (i : Fin n) :
    (x i).num.natAbs.size ≤ E+1 ∧ (x i).den.size ≤ E+1 := by
  have ⟨num, den⟩ := frac.reduced i
  rw [Int.abs_eq_natAbs] at num
  have hn : (x i).num.natAbs ≤ h := by exact_mod_cast num
  have hd : (x i).den ≤ h := by exact_mod_cast den
  have one (z : ℕ) (hz : z ≤ h) : z.size ≤ E+1 := by
    exact (Nat.size_le_size (hz.trans bound)).trans_eq Nat.size_pow
  exact ⟨one _ hn, one _ hd⟩

private theorem BoundedFraction.difference {n : ℕ} {x y : Fin n → ℚ} {h : ℤ}
    (hx : BoundedFraction x h) (hy : BoundedFraction y h) :
    BoundedFraction (fun i => x i - y i) (2*h^2) := by
  obtain ⟨D, dn, hd, a, ha, ax⟩ := hx
  obtain ⟨F, fnz, hf, b, hb, by'⟩ := hy
  have hn := (abs_nonneg D).trans hd
  have bd {u v : ℤ} (hu : |u| ≤ h) (hv : |v| ≤ h) : |u*v| ≤ h^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hv (abs_nonneg _) hn
  refine ⟨D*F, mul_ne_zero dn fnz, ?_, fun i => a i*F-b i*D, ?_, ?_⟩
  · have prod := bd hd hf
    nlinarith [sq_nonneg h]
  · intro i
    exact (abs_sub ..).trans (by linarith [bd (ha i) hf, bd (hb i) hd])
  · intro i
    push_cast
    rw [sub_mul, ←mul_assoc, ax, mul_comm (D : ℚ) (F : ℚ), ←mul_assoc, by']

/-- Bit lengths and work of one materialized fill at any successful suffix
for integer free coordinates of magnitude at most one. -/
theorem solve_fill_bits_work {N H n : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H)
    {rows : List (Row n)} (reached : SolveStep base rows)
    {c : FillCounter n} (ok : solveWithFillCounter n rows = some c)
    (y : Fin c.family.free → ℤ) (hy : ∀ j, |y j| ≤ 1) :
    let result := c.fill (fun i => (y i : ℚ))
    result.1 = c.family.fill (fun i => (y i : ℚ)) ∧ result.2 ≤ n*(n+1) ∧
    ∀ i, (result.1.get i).num.natAbs.size ≤ fillExponent n base.length H+1 ∧
      (result.1.get i).den.size ≤ fillExponent n base.length H+1 := by
  have same := solveWithFillCounter_value n rows
  rw [ok] at same
  have frac := solve_back_substitution_height base hp input reached same.symm y hy
  refine ⟨c.value _, c.work _, ?_⟩
  rw [c.value]
  exact fraction_num_den_bits frac (fill_height_exp ..)

private theorem solve_direction_fraction {N H n : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H)
    {rows : List (Row n)} (reached : SolveStep base rows)
    {f : Family n} (ok : solve n rows = some f) (j : Fin f.free) :
    let h := (n+1).factorial*((base.length+1).factorial*H^(base.length+1))^n
    BoundedFraction (f.direction j) ((2*h^2 : ℕ) : ℤ) := by
  let unit (k : Fin f.free) : ℤ := if k=j then 1 else 0
  have one := solve_back_substitution_height base hp input reached ok unit
    (fun k => by simp [unit]; split <;> decide)
  have zero := solve_back_substitution_height base hp input reached ok (fun _ => 0) (by simp)
  change BoundedFraction (fun i => f.direction j i) _
  simpa [Family.direction, Family.point, unit, apply_ite] using one.difference zero

private theorem direction_height_exp (n m H : ℕ) :
    let E := fillExponent n m H
    let h := (n+1).factorial*((m+1).factorial*H^(m+1))^n
    2*h^2 ≤ 2^(2*E+1) := by
  dsimp only
  calc
    _ ≤ 2*(2^fillExponent n m H)^2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (fill_height_exp ..) 2)
    _ = _ := by rw [←pow_mul, pow_succ]; ring_nf

/-- For a direction, subtracting the zero assignment from its unit assignment
gives a common denominator and numerator of at most twice the squared fill height. -/
theorem solve_direction_bits {N H n : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H)
    {rows : List (Row n)} (reached : SolveStep base rows)
    {c : FillCounter n} (ok : solveWithFillCounter n rows = some c) (j : Fin c.family.free)
    (i : Fin n) :
    let value := (c.direction j).1.get i
    value.num.natAbs.size ≤ 2*fillExponent n base.length H+2 ∧
      value.den.size ≤ 2*fillExponent n base.length H+2 := by
  have same := solveWithFillCounter_value n rows
  rw [ok] at same
  have frac := solve_direction_fraction base hp input reached same.symm j
  dsimp only
  rw [(c.point_direction_cost.2.2 j).1 i]
  exact fraction_num_den_bits frac (direction_height_exp ..) i

/-- For any common denominator, the lcm used by integerVector divides its
magnitude. Reducing that denominator also reduces every integer coordinate. -/
theorem BoundedFraction.integer_bounds {n : ℕ} {x : Fin n → ℚ} {h : ℤ}
    (frac : BoundedFraction x h) :
    (integerScale x : ℤ) ≤ h ∧ ∀ i, |(integerVector x).get i| ≤ h := by
  obtain ⟨D, dn, hd, z, hz, eq⟩ := frac
  have divides : integerScale x ∣ D.natAbs := by
    apply Finset.lcm_dvd
    intro i _
    have div : x i = Rat.divInt (z i) D := by
      rw [Rat.divInt_eq_div]
      exact (eq_div_iff (Int.cast_ne_zero.mpr dn)).mpr (eq i)
    obtain ⟨k, _, hk⟩ := Rat.num_den_mk dn div
    rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.dvd_mul_left _ _
  have le := Nat.le_of_dvd (Int.natAbs_pos.mpr dn) divides
  have leInt : (integerScale x : ℤ) ≤ |D| := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast le
  refine ⟨leInt.trans hd, fun i => ?_⟩
  have leQ : (integerScale x : ℚ) ≤ |(D : ℚ)| := by exact_mod_cast leInt
  have entry : |(((integerVector x).get i : ℤ) : ℚ)| ≤ |(z i : ℚ)| := by
    calc
      _ = |x i| * (integerScale x : ℚ) := by rw [integerVector_spec, abs_mul, abs_of_nonneg (show (0 : ℚ) ≤ integerScale x from Nat.cast_nonneg _)]
      _ ≤ |x i| * |(D : ℚ)| := mul_le_mul_of_nonneg_left leQ (abs_nonneg _)
      _ = _ := by rw [←abs_mul, eq]
  exact (show |(integerVector x).get i| ≤ |z i| by exact_mod_cast entry).trans (hz i)

private theorem BoundedFraction.integer_bits {n h E : ℕ} {x : Fin n → ℚ}
    (frac : BoundedFraction x (h : ℤ)) (bound : h ≤ 2^E) :
    (integerScale x).size ≤ E+1 ∧ ∀ i, ((integerVector x).get i).natAbs.size ≤ E+1 := by
  have ⟨scale, entry⟩ := frac.integer_bounds
  have bits (z : ℕ) (hz : z ≤ h) : z.size ≤ E+1 :=
    (Nat.size_le_size (hz.trans bound)).trans_eq Nat.size_pow
  refine ⟨bits _ (by exact_mod_cast scale), fun i => bits _ ?_⟩
  have bi := entry i
  rw [Int.abs_eq_natAbs] at bi
  exact_mod_cast bi

/-- Widths of all scalar and vector entries of the returned integer family. -/
theorem solve_integer_family_bits {N H n : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H)
    {rows : List (Row n)} (reached : SolveStep base rows)
    {f : Family n} (ok : solve n rows = some f) :
    let E := fillExponent n base.length H
    f.integers.scale.size ≤ E+1 ∧
    (∀ i, (f.integers.particular.get i).natAbs.size ≤ E+1) ∧
    ∀ j, (f.integers.scales.get j).size ≤ 2*E+2 ∧
      ∀ i, ((f.integers.directions.get j).get i).natAbs.size ≤ 2*E+2 := by
  let h := (n+1).factorial*((base.length+1).factorial*H^(base.length+1))^n
  let E := fillExponent n base.length H
  have height : h ≤ 2^E := fill_height_exp ..
  have zero := solve_back_substitution_height base hp input reached ok (fun _ => 0) (by simp)
  have point : BoundedFraction f.point ((h : ℕ) : ℤ) := by simpa [Family.point, h] using zero
  have bp := point.integer_bits height
  refine ⟨bp.1, bp.2, fun j => ?_⟩
  change Fin f.free at j
  have frac := solve_direction_fraction base hp input reached ok j
  have bounds := frac.integer_bits (direction_height_exp ..)
  change ((Vector.ofFn (fun k => integerScale (f.direction k))).get j).size ≤ _ ∧
    ∀ i, (((Vector.ofFn (fun k => integerVector (f.direction k))).get j).get i).natAbs.size ≤ _
  simpa [Vector.get_eq_getElem] using bounds

end Cogentic.Elimination

#print axioms Cogentic.Elimination.solveWithFillCounter_value
#print axioms Cogentic.Elimination.FillCounter.point_direction_cost

#print axioms Cogentic.Elimination.solve_fill_bits_work
#print axioms Cogentic.Elimination.solve_direction_bits
#print axioms Cogentic.Elimination.solve_integer_family_bits
