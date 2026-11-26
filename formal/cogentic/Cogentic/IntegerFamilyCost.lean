import Cogentic.CollectorCost
import Cogentic.BackSubstitutionWork
import Cogentic.PerturbationCost

namespace Cogentic.BinaryIntegerFamily
open Elimination BinaryDivision BinaryCollector BinaryPivot Finset

private def denominator {n : ℕ} (ds : Fin n → List Bool) : List (Fin n) → List Bool × ℕ
  | [] => ((1 : ℕ).bits, 0)
  | i :: is =>
    let tail := denominator ds is
    let out := lcmBits tail.1 (ds i)
    (out.1, tail.2 + out.2)

private theorem denominator_spec {n W : ℕ} (x : Fin n → ℚ) (xs : List (Fin n))
    (width : (integerScale x).size ≤ W) :
    (denominator (fun i => (x i).den.bits) xs).1 = (xs.toFinset.lcm (fun i => (x i).den)).bits ∧
    (denominator (fun i => (x i).den.bits) xs).2 ≤ xs.length * lcmBudget W := by
  let D (s : Finset (Fin n)) := s.lcm (fun i => (x i).den)
  have positive (s) : 0 < D s := Nat.pos_of_ne_zero (by simp [D, Finset.lcm_eq_zero_iff])
  have divides (s) : D s ∣ integerScale x :=
    Finset.lcm_dvd fun i _ => Finset.dvd_lcm (Finset.mem_univ i)
  have dw (s) := (Nat.size_le_size (Nat.le_of_dvd (integerScale_pos x) (divides s))).trans width
  induction xs with
  | nil => simp [denominator]
  | cons i xs ih =>
    have wi := (Nat.size_le_size (Nat.le_of_dvd (integerScale_pos x)
      (show (x i).den ∣ integerScale x from Finset.dvd_lcm (Finset.mem_univ i)))).trans width
    obtain ⟨value, cost⟩ := lcm_spec (D xs.toFinset) (x i).den W (positive _) (dw _) wi
    simp only [denominator, ih.1, List.toFinset_cons, Finset.lcm_insert, List.length_cons]
    exact ⟨value.trans (by rw [Nat.lcm_comm]; rfl),
      (Nat.add_le_add ih.2 cost).trans_eq (Nat.succ_mul ..).symm⟩

private def coordinate (scale : List Bool) (x : SignedWord × List Bool) : SignedWord × ℕ :=
  let q := divide x.2 scale
  let p := multiply x.1.digits q.quotient
  let w := BinaryPerturbation.normal ⟨x.1.negative,p.1⟩
  (w.1, q.gates + p.2 + w.2)

private theorem coordinate_spec (scale W : ℕ) (x : ℚ) (hs : scale.size ≤ W)
    (hn : x.num.natAbs.size ≤ W) (hd : x.den.size ≤ W) :
    (coordinate scale.bits (BinaryPivot.encode x.num,x.den.bits)).1 = BinaryPivot.encode (x.num * (scale / x.den : ℕ)) ∧
    (coordinate scale.bits (BinaryPivot.encode x.num,x.den.bits)).2 ≤ W*(20*W+1) + 16*W^2 + 9*W+2 := by
  let q := divide x.den.bits scale.bits
  obtain ⟨quot,_,gates⟩ := divide_naturals scale x.den x.den_pos
  have len : q.quotient.length = scale.size :=
    (BinaryIndexCap.quotient_length ..).trans (Nat.size_eq_bits_len _)
  obtain ⟨val,pl,cost⟩ := multiply_spec x.num.natAbs.bits q.quotient
  change value (multiply x.num.natAbs.bits q.quotient).1 = _ at val
  change value q.quotient = _ at quot
  rw [quot,value_bits] at val
  have num : signed (decide (x.num < 0)) x.num.natAbs = x.num := by
    simpa only [BinaryPivot.encode,SignedWord.decode,value_bits] using decode_encode x.num
  let raw : SignedWord := ⟨decide (x.num < 0),(multiply x.num.natAbs.bits q.quotient).1⟩
  obtain ⟨norm,_,nc⟩ := BinaryPerturbation.normal_spec raw
  constructor
  · apply norm.trans
    apply congrArg BinaryPivot.encode
    change signed (decide (x.num < 0)) (value (multiply _ q.quotient).1) = _
    rw [val,Nat.mul_comm]
    conv_rhs => rw [← num]
    cases decide (x.num < 0) <;> simp [signed]
  · rw [len,Nat.size_eq_bits_len] at cost
    have c := cost.trans (show scale.size * (x.num.natAbs.size+5*(x.num.natAbs.size+2*scale.size)) ≤
        W*(W+5*(W+2*W)) by gcongr)
    have d := gates.trans (show scale.size*(10*(x.den.size+scale.size)+1) ≤ W*(20*W+1) by apply Nat.mul_le_mul hs; omega)
    change q.gates + (multiply x.num.natAbs.bits q.quotient).2 + (BinaryPerturbation.normal raw).2 ≤ _
    rw [nc]
    rw [len,Nat.size_eq_bits_len] at pl
    have cb : (multiply x.num.natAbs.bits q.quotient).2 ≤ 16*W^2 := c.trans_eq (by ring)
    change q.gates ≤ W*(20*W+1) at d
    dsimp only [raw]
    omega

/-- Materialize one rational column over its least common denominator. The
denominator is computed once and shared across all coordinate divisions. -/
def integerizeWords {n : ℕ} (x : Fin n → SignedWord × List Bool) : (List Bool × Vector SignedWord n) × ℕ :=
  let m := denominator (fun i => (x i).2) (List.finRange n)
  let cs := Vector.ofFn (fun i => coordinate m.1 (x i))
  ((m.1,cs.map Prod.fst),m.2 + ∑ i, (cs.get i).2)

def integerize {n : ℕ} (x : Fin n → ℚ) :=
  integerizeWords (fun i => (BinaryPivot.encode (x i).num,(x i).den.bits))

def columnBudget (n W : ℕ) := n*(lcmBudget W + W*(20*W+1) + 16*W^2 + 9*W+2)

theorem integerize_spec {n W : ℕ} (x : Fin n → ℚ) (hs : (integerScale x).size ≤ W)
    (hn : ∀ i, (x i).num.natAbs.size ≤ W) :
    (integerize x).1.1 = (integerScale x).bits ∧
    (∀ i, ((integerize x).1.2).get i = BinaryPivot.encode ((integerVector x).get i)) ∧
    (integerize x).2 ≤ columnBudget n W := by
  obtain ⟨scale,cost⟩ := denominator_spec x (List.finRange n) hs
  have full : (List.finRange n).toFinset = univ := by ext; simp
  rw [full] at scale
  change _ = (integerScale x).bits at scale
  rw [List.length_finRange] at cost
  have row (i) := coordinate_spec (integerScale x) W (x i) hs (hn i)
    ((Nat.size_le_size (Nat.le_of_dvd (integerScale_pos x)
      (show (x i).den ∣ integerScale x from Finset.dvd_lcm (Finset.mem_univ i)))).trans hs)
  refine ⟨scale,fun i => ?_,?_⟩
  · simpa only [integerize,integerizeWords,integerVector,scale,Vector.get_eq_getElem,
      Vector.getElem_ofFn,Vector.getElem_map] using (row i).1
  · have total := sum_le_sum (s:=univ) (fun i _ => (row i).2)
    simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at total
    simp only [integerize,integerizeWords,scale,Vector.get_eq_getElem,Vector.getElem_ofFn]
    exact (Nat.add_le_add cost total).trans_eq (by unfold columnBudget; ring)

def encodedColumn {n : ℕ} (x : Fin n → ℚ) :=
  ((integerScale x).bits,(integerVector x).map BinaryPivot.encode)

theorem integerize_value {n : ℕ} (x : Fin n → ℚ) :
    (integerize x).1 = encodedColumn x := by
  let W := (integerScale x).size + ∑ j,(x j).num.natAbs.size
  have num (i : Fin n) : (x i).num.natAbs.size ≤ W :=
    (single_le_sum (f:=fun j => (x j).num.natAbs.size)
      (fun _ _ => Nat.zero_le _) (mem_univ i)).trans (Nat.le_add_left ..)
  obtain ⟨scale,cs,_⟩ := integerize_spec x (Nat.le_add_right .. : (integerScale x).size ≤ W) num
  apply Prod.ext scale
  apply Vector.ext
  intro i hi
  simpa only [encodedColumn,Vector.get_eq_getElem,Vector.getElem_map] using cs ⟨i,hi⟩

/-- Turning the solver's recovered point and all of its directions into integer
vectors pays for one binary LCM fold and one division per coordinate per vector. -/
def familyWork {n : ℕ} (f : Family n) : ℕ :=
  (integerize f.point).2 + ∑ j, (integerize (f.direction j)).2

theorem solve_integerization_gates {n H : ℕ} (rows : List (Row n)) (hp : 1 ≤ H)
    (input : ∀ r ∈ rows, ∀ j, (r.aug j).natAbs ≤ H)
    {f : Family n} (ok : Elimination.solve n rows = some f) :
    let W := 2*fillExponent n rows.length H + 2
    familyWork f ≤ (n+1)*columnBudget n W := by
  intro W
  have agree := solveWithFillCounter_value n rows
  cases found : solveWithFillCounter n rows with
  | none => simp [found,ok] at agree
  | some c =>
    have same : c.family = f := by simpa [found,ok] using agree
    subst f
    have ints := solve_integer_family_bits rows hp input .start ok
    have hb : fillExponent n rows.length H+1 ≤ W := by dsimp only [W]; omega
    have pw (i) : (c.family.point i).num.natAbs.size ≤ W := by
      have h := (solve_fill_bits_work rows hp input .start found (fun _ => 0) (by simp)).2.2 i
      rw [c.value] at h
      exact (show (c.family.point i).num.natAbs.size ≤ _ by simpa [Family.point,Family.values] using h.1).trans hb
    have dw (j i) : (c.family.direction j i).num.natAbs.size ≤ W := by
      have h := (solve_direction_bits rows hp input .start found j i).1
      rwa [(c.point_direction_cost.2.2 j).1 i] at h
    have point := (integerize_spec c.family.point (ints.1.trans hb) pw).2.2
    have dirs := sum_le_sum (s:=univ) (fun j _ => (integerize_spec (c.family.direction j)
      (by simpa only [Family.integers,Vector.get_eq_getElem,Vector.getElem_ofFn] using (ints.2.2 j).1 : (integerScale (c.family.direction j)).size ≤ W) (dw j)).2.2)
    simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at dirs
    exact (Nat.add_le_add point (dirs.trans (Nat.mul_le_mul_right _ c.arity))).trans_eq (by ring)

end Cogentic.BinaryIntegerFamily

#print axioms Cogentic.BinaryIntegerFamily.integerize_spec

#print axioms Cogentic.BinaryIntegerFamily.solve_integerization_gates
