import Cogentic.FractionFreeBounds

namespace Cogentic.Elimination

/-- First matching row and the number of comparisons made before returning. -/
private def findWithCount {α : Type*} (p : α → Bool) : List α → Option α × ℕ
  | [] => (none, 0)
  | a :: as =>
    if p a then (some a, 1) else
      let tail := findWithCount p as
      (tail.1, 1 + tail.2)

private theorem findWithCount_value {α : Type*} (p : α → Bool) (xs : List α) :
    (findWithCount p xs).1 = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons a as ih => cases h : p a <;> simp [findWithCount, List.find?, h, ih]

private theorem findWithCount_le {α : Type*} (p : α → Bool) (xs : List α) :
    (findWithCount p xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [findWithCount]
  | cons a as ih =>
    cases h : p a
    · simp [findWithCount, h]
      omega
    · simp [findWithCount, h]

private theorem rhsCheck {n : ℕ} (rows : List (Row n)) :
    (findWithCount (fun r => r.rhs != 0) rows).1.isNone = rows.all (fun r => r.rhs == 0) := by
  induction rows with
  | nil => rfl
  | cons r rs ih => by_cases h : r.rhs = 0 <;> simp [findWithCount, h, ih]


/-- Euclidean gcd paired with the number of remainder operations. -/
def gcdWithCount (a b : ℕ) : ℕ × ℕ :=
  if h : a = 0 then (b, 0) else
    let tail := gcdWithCount (b % a) a
    (tail.1, tail.2 + 1)
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem gcdWithCount_value (a b : ℕ) : (gcdWithCount a b).1 = a.gcd b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    rw [gcdWithCount]
    split
    · next ha => simp [ha]
    · next ha => rw [Nat.gcd_rec]; exact ih _ (Nat.mod_lt _ (Nat.pos_of_ne_zero ha)) _

private theorem rem_half {a r : ℕ} (rpos : 0 < r) (rlt : r < a) :
    2*(a % r) ≤ a := by
  by_cases h : 2*r ≤ a
  · have hmod := Nat.mod_lt a rpos
    omega
  · rw [Nat.mod_eq_sub_mod rlt.le, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Every two nonterminal steps reduce the first argument by at least half. -/
theorem gcdWithCount_le (a b : ℕ) : (gcdWithCount a b).2 ≤ 2*a.size := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    rw [gcdWithCount]
    split
    · simp
    · next ha =>
      have apos := Nat.pos_of_ne_zero ha
      let r := b % a
      have rlt : r < a := Nat.mod_lt _ apos
      change (gcdWithCount r a).2 + 1 ≤ _
      rw [gcdWithCount]
      split
      · simp
        have pos := Nat.size_pos.mpr apos
        omega
      · next hr =>
        have rpos := Nat.pos_of_ne_zero hr
        have half := rem_half rpos rlt
        have size : (a % r).size < a.size := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.size_pos.mpr apos))
          rw [hk, Nat.lt_succ_iff, Nat.size_le]
          have al := Nat.lt_size_self a
          rw [hk, pow_succ] at al
          omega
        have tail := ih _ ((Nat.mod_lt a rpos).trans rlt) r
        dsimp only
        omega

private def gcdFold : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | a :: as =>
    let rest := gcdFold as
    let step := gcdWithCount a rest.1
    (step.1, step.2 + rest.2)

private theorem dvd_gcdFold (d : ℕ) (xs : List ℕ) :
    d ∣ (gcdFold xs).1 ↔ ∀ a ∈ xs, d ∣ a := by
  induction xs with
  | nil => simp [gcdFold]
  | cons a as ih => simp [gcdFold, Nat.dvd_gcd_iff, ih]

private theorem gcdFold_le (xs : List ℕ) (B : ℕ) (bounded : ∀ a ∈ xs, a.size ≤ B) :
    (gcdFold xs).2 ≤ xs.length*(2*B) := by
  induction xs with
  | nil => simp [gcdFold]
  | cons a as ih =>
    have one := (gcdWithCount_le a (gcdFold as).1).trans
      (Nat.mul_le_mul_left 2 (bounded a (by simp)))
    have rest := ih (fun x h => bounded x (by simp [h]))
    simpa [gcdFold, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add one rest

/-- Compute the row content and count Euclidean remainders used by the fold. -/
def Row.contentWithRemainders {n : ℕ} (r : Row n) : ℕ × ℕ :=
  gcdFold (r.rhs.natAbs :: List.ofFn (fun i => (r.coeffs.get i).natAbs))

@[simp] theorem Row.contentWithRemainders_value {n : ℕ} (r : Row n) :
    r.contentWithRemainders.1 = r.content := by
  have hd (d : ℕ) : d ∣ r.contentWithRemainders.1 ↔ d ∣ r.content := by
    simp [Row.contentWithRemainders, dvd_gcdFold, Row.content, Nat.dvd_gcd_iff,
      Finset.dvd_gcd_iff, List.mem_ofFn]
  exact Nat.dvd_antisymm ((hd _).mp dvd_rfl) ((hd _).mpr dvd_rfl)

theorem Row.contentWithRemainders_le {n : ℕ} (r : Row n) (B : ℕ)
    (bounded : ∀ j, (r.aug j).natAbs.size ≤ B) :
    r.contentWithRemainders.2 ≤ (n+1)*(2*B) := by
  unfold Row.contentWithRemainders
  apply (gcdFold_le _ B ?_).trans (by simp)
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact bounded none
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact bounded (some i)

/-- Entries materialized by a pivot before removing the content. -/
def Row.rawPivot {n : ℕ} (p r : Row (n+1)) : Row n :=
  ⟨Vector.ofFn (fun i => p.head*r.coeffs.get i.succ-r.head*p.coeffs.get i.succ),
    p.head*r.rhs-r.head*p.rhs⟩

/-- Count two multiplications, a subtraction, an absolute value and one gcd
per augmented entry, one content test per row, and one division per augmented
entry precisely when the content is nonzero. When expanding gcds, their
initial unit pays for the terminal zero test, and each Euclidean iteration
adds a nonterminal zero test and a remainder operation. -/
def Row.reduceWithCount {n : ℕ} (p r : Row (n+1)) (expandGcd : Bool := false) : Row n × ℕ :=
  let raw := p.rawPivot r
  let content := if expandGcd then raw.contentWithRemainders else (raw.content, 0)
  let cost := 5*(n+1)+1+2*content.2
  if content.1 = 0 then (raw, cost) else
    (⟨Vector.ofFn (fun i => raw.coeffs.get i / (content.1 : ℤ)), raw.rhs / (content.1 : ℤ)⟩,
      cost + (n+1))

@[simp] theorem Row.reduceWithCount_value {n : ℕ} (p r : Row (n+1)) (mode : Bool) :
    (p.reduceWithCount r mode).1 = p.reduce r := by
  change (p.reduceWithCount r mode).1 = (p.rawPivot r).primitive
  cases mode <;> by_cases h : (p.rawPivot r).content = 0 <;>
    simp [Row.reduceWithCount, Row.primitive, h]

theorem Row.reduceWithCount_le {n : ℕ} (p r : Row (n+1)) :
    (p.reduceWithCount r).2 ≤ 6*(n+1)+1 := by
  by_cases h : (p.rawPivot r).content = 0
  · simp [Row.reduceWithCount, h]
  · simp [Row.reduceWithCount, h]
    omega

private theorem Row.reduceWithGcdCount {n : ℕ} (p r : Row (n+1)) :
    (p.reduceWithCount r true).2 =
      (p.reduceWithCount r).2 + 2*(p.rawPivot r).contentWithRemainders.2 := by
  by_cases h : (p.rawPivot r).content = 0 <;> simp [Row.reduceWithCount, h, Nat.add_right_comm]

private def countedMap {α β : Type*} (f : α → β × ℕ) : List α → List β × ℕ
  | [] => ([], 0)
  | a :: as =>
    let (b, k) := f a
    let (bs, ks) := countedMap f as
    (b :: bs, k + ks)

private theorem countedMap_value {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    (countedMap f xs).1 = xs.map (fun a => (f a).1) := by
  induction xs <;> simp_all [countedMap]

private theorem countedMap_le {α β : Type*} (f : α → β × ℕ) (k : ℕ)
    (xs : List α) (bound : ∀ a ∈ xs, (f a).2 ≤ k) :
    (countedMap f xs).2 ≤ xs.length*k := by
  induction xs with
  | nil => simp [countedMap]
  | cons a as ih =>
    have one := bound a (by simp)
    have rest := ih (fun x hx => bound x (by simp [hx]))
    simpa [countedMap, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add one rest

/-- Forward elimination, retaining the original solver's success or failure.
The counter covers scalar arithmetic and tests, up to construction of the
solution family. Subsequent applications of its fill function are separate. -/
def forwardWithCount (expandGcd : Bool) : (n : ℕ) → List (Row n) → Option (Family n) × ℕ
  | 0, rows =>
    let check := findWithCount (fun r => r.rhs != 0) rows
    (if check.1.isNone then some emptyFamily else none, check.2)
  | n+1, rows =>
    let scan := findWithCount (fun r => r.head != 0) rows
    match scan.1 with
    | none =>
      let tail := forwardWithCount expandGcd n (rows.map Row.drop)
      (tail.1.map freeLift, scan.2 + tail.2)
    | some p =>
      let reduced := countedMap (fun r => p.reduceWithCount r expandGcd) rows
      let tail := forwardWithCount expandGcd n reduced.1
      (tail.1.map (pivotLift p), scan.2 + reduced.2 + tail.2)

abbrev solveWithCount := forwardWithCount false

@[simp] theorem forwardWithCount_value (mode : Bool) (n : ℕ) (rows : List (Row n)) :
    (forwardWithCount mode n rows).1 = solve n rows := by
  induction n with
  | zero => simp [forwardWithCount, solve, rhsCheck]
  | succ n ih =>
    rw [forwardWithCount, solve]
    simp only [findWithCount_value]
    cases rows.find? (fun r => r.head != 0) <;> simp [ih, countedMap_value]

@[simp] theorem solveWithCount_value (n : ℕ) (rows : List (Row n)) :
    (solveWithCount n rows).1 = solve n rows := forwardWithCount_value ..

private theorem forwardWithCount_bound {N : ℕ} (base : List (Row N)) (mode : Bool) (B : ℕ)
    (step : ∀ {n} {rows : List (Row (n+1))}, SolveStep base rows →
      ∀ p ∈ rows, ∀ r ∈ rows, (p.reduceWithCount r mode).2 ≤ (6+2*B)*(n+1)+1)
    {n} {rows : List (Row n)} (reached : SolveStep base rows) :
    (forwardWithCount mode n rows).2 ≤ (4+B)*rows.length*(n+1)^2 := by
  induction n with
  | zero =>
    change (findWithCount _ rows).2 ≤ _
    have h := findWithCount_le (fun r : Row 0 => r.rhs != 0) rows
    nlinarith [Nat.zero_le (B*rows.length)]
  | succ n ih =>
    have tests := findWithCount_le (fun r : Row (n+1) => r.head != 0) rows
    rw [forwardWithCount]
    split
    · rename_i found
      have miss : rows.find? (fun r => r.head != 0) = none := by simpa [findWithCount_value] using found
      have tailBound := ih (SolveStep.drop reached miss)
      simp only [List.length_map] at tailBound
      dsimp only
      nlinarith [Nat.zero_le (rows.length*n), Nat.zero_le (B*rows.length), Nat.zero_le (B*rows.length*n)]
    · rename_i p found
      let reduce := fun r => p.reduceWithCount r mode
      let reduced := countedMap reduce rows
      have hit : rows.find? (fun r => r.head != 0) = some p := by simpa [findWithCount_value] using found
      have pm := List.mem_of_find?_eq_some hit
      have eq : reduced.1 = rows.map p.reduce := by simp [reduced, reduce, countedMap_value]
      have len : reduced.1.length = rows.length := by simp [eq]
      have cost : reduced.2 ≤ rows.length*((6+2*B)*(n+1)+1) :=
        countedMap_le _ _ _ (step reached p pm)
      have reached' : SolveStep base reduced.1 := eq.symm ▸ (SolveStep.pivot reached hit)
      have tailBound := ih reached'
      rw [len] at tailBound
      change _ + reduced.2 + (forwardWithCount mode n reduced.1).2 ≤ _
      nlinarith [Nat.zero_le (rows.length*n), Nat.zero_le (B*rows.length), Nat.zero_le (B*rows.length*n)]

/-- Uniform scalar-operation bound regardless of rank or consistency. -/
theorem solveWithCount_le (n : ℕ) (rows : List (Row n)) :
    (solveWithCount n rows).2 ≤ 4*rows.length*(n+1)^2 := by
  apply forwardWithCount_bound rows false 0 _ SolveStep.start
  intro k rs _ p _ r _
  exact Row.reduceWithCount_le p r

/-- The forward work and the size of every raw entry it normalizes, for both
outcomes of the original solver. -/
theorem solve_forward_bounds {N H : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H) :
    (solveWithCount N base).1 = solve N base ∧
    (solveWithCount N base).2 ≤ 4*base.length*(N+1)^2 ∧
    ∀ {n : ℕ} {rows : List (Row (n+1))}, SolveStep base rows →
      ∀ p ∈ rows, ∀ r ∈ rows, ∀ j, ((p.rawPivot r).aug j).natAbs.size ≤
        2*(((base.length+1).size+H.size)*(base.length+1))+2 := by
  refine ⟨solveWithCount_value .., solveWithCount_le .., ?_⟩
  intro n rows reached p pm r rm j
  have b := solve_cross_product_bits base hp input reached p r pm rm j
  cases j <;> simpa [Row.rawPivot, Row.aug, Vector.get_eq_getElem] using b

/-- Euclidean remainder count in each individual content computation reached
by the solver, including a pivot row with zero content. -/
theorem solve_pivot_remainders {N n H : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H)
    {rows : List (Row (n+1))} (reached : SolveStep base rows)
    (p r : Row (n+1)) (pm : p ∈ rows) (rm : r ∈ rows) :
    (p.rawPivot r).contentWithRemainders.2 ≤
      (n+1)*(2*(2*(((base.length+1).size+H.size)*(base.length+1))+2)) := by
  exact Row.contentWithRemainders_le _ _ ((solve_forward_bounds base hp input).2.2 reached p pm r rm)

/-- Count all forward scalar operations with explicit Euclidean remainders on
every branch. B is the raw product-difference width guaranteed by the height
bound. The counted output of this implementation is exactly the solver output. -/
theorem solve_forward_remainder_bound {N H : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H) :
    let B := 2*(((base.length+1).size+H.size)*(base.length+1))+2
    (forwardWithCount true N base).1 = solve N base ∧
    (forwardWithCount true N base).2 ≤ (4+2*B)*base.length*(N+1)^2 := by
  dsimp only
  refine ⟨forwardWithCount_value .., forwardWithCount_bound base true _ ?_ SolveStep.start⟩
  intro n rows reached p pm r rm
  rw [Row.reduceWithGcdCount]
  have bound := Nat.add_le_add (Row.reduceWithCount_le p r)
    (Nat.mul_le_mul_left 2 (solve_pivot_remainders base hp input reached p r pm rm))
  exact bound.trans_eq (by ring)

/-- Apply the count to the system assembled by marking. -/
theorem stageTwo_forward_count (s : Marking.Relations) :
    ((solveWithCount _ (relationRows s)).1.map Family.integers = stageTwo s) ∧
    (solveWithCount _ (relationRows s)).2 ≤ 4*(s.rows.length+1)*(s.marks.length+1)^2 := by
  exact ⟨by simp [stageTwo], by simpa [relationRows] using solveWithCount_le _ (relationRows s)⟩

end Cogentic.Elimination

#print axioms Cogentic.Elimination.solve_forward_bounds
#print axioms Cogentic.Elimination.stageTwo_forward_count
#print axioms Cogentic.Elimination.solve_forward_remainder_bound
