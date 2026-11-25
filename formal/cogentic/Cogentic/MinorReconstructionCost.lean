import Cogentic.ColumnAccuracy
import Cogentic.BackSubstitutionWork
import Cogentic.ReconstructionCost

namespace Cogentic.Concrete
open Elimination Finset

private theorem unique_width {d H : ℕ} (rows : List (Row d)) (hp : 1≤H)
    (bound : ∀ r∈rows, ∀ j, (r.aug j).natAbs≤H) {x : Fin d → ℚ}
    (found : uniqueSolution rows=some x) (i : Fin d) :
    (x i).num.natAbs.size≤fillExponent d rows.length H+1 ∧
    (x i).den.size≤fillExponent d rows.length H+1 := by
  cases eq : solveWithFillCounter d rows with
  | none =>
    have same := solveWithFillCounter_value d rows
    simp only [eq,Option.map_none] at same
    simp [uniqueSolution,←same] at found
  | some c =>
    have same := solveWithFillCounter_value d rows
    simp only [eq,Option.map_some] at same
    simp only [uniqueSolution,←same] at found
    split at found <;> simp_all only [Option.some.injEq,reduceCtorEq]
    subst x
    obtain ⟨_,_,width⟩ := solve_fill_bits_work rows hp bound .start eq
      (fun _=>0) (by simp)
    have hi := width i
    rw [c.value] at hi
    simpa [Family.point,Family.values] using hi

/-- Every returned solution of an enumerated minor, including one which fails
the modular check, has bounded numerator and denominator bit lengths. -/
theorem minor_solution_width {d free H : ℕ} {rhs : Vector ℤ d}
    {cols : Vector (Vector ℤ d) free} (hp : 1≤H)
    (rhsBound : ∀ i, (rhs.get i).natAbs≤H) (colsBound : ∀ j i, ((cols.get j).get i).natAbs≤H)
    {indices : List (Fin free)} {x : Fin d → ℚ} (found : solveColumns rhs cols indices=some x) (i : Fin d) :
    (x i).num.natAbs.size≤fillExponent d d H+1 ∧ (x i).den.size≤fillExponent d d H+1 := by
  unfold solveColumns at found
  split at found
  next size =>
    let choice := (Vector.ofFn indices.get).cast size
    let rows := minorRows rhs cols choice
    have bound (r) (hr : r∈rows) (j) : (r.aug j).natAbs≤H := by
      obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hr
      cases j with
      | none => simpa [Row.aug] using rhsBound a
      | some k => simpa [Row.aug,Vector.get_eq_getElem] using colsBound (choice.get k) a
    have result := unique_width rows hp bound found i
    simpa [rows,minorRows] using result
  next => contradiction

/-- Bound the exact integer observations formed from dyadic mark columns before
the rounded linear system is solved. -/
theorem observation_height {m d T C : ℕ} (cols : Vector (Vector ℚ d) m)
    (coeff : Vector ℤ m) (P : ℕ)
    (hc : ∀ j i, |(cols.get j).get i| ≤ (C:ℚ))
    (ht : ∀ j, |coeff.get j| ≤ (T:ℤ)) (i : Fin d) :
    ((observation cols coeff P).get i).natAbs ≤ m*T*C*2^P+1 := by
  let y := ∑ j : Fin m, (coeff.get j:ℚ)*(cols.get j).get i
  have hy : |y|≤(m:ℚ)*T*C := calc
    _ ≤ ∑ j : Fin m, |(coeff.get j:ℚ)*(cols.get j).get i| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _j : Fin m, (T:ℚ)*C := sum_le_sum fun j _=>by
      rw [abs_mul]
      exact mul_le_mul (by exact_mod_cast ht j) (hc j i) (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring
  have h := mul_le_mul_of_nonneg_right hy (show 0≤(2:ℚ)^P by positivity)
  rw [←abs_of_nonneg (show 0≤(2:ℚ)^P by positivity),←abs_mul] at h
  rw [abs_of_nonneg (show 0≤(2:ℚ)^P by positivity)] at h
  have lr := abs_le.mp h
  let z := ⌊y*(2:ℚ)^P+1/2⌋
  have lo := Int.floor_le (y*(2:ℚ)^P+1/2)
  have hi := Int.lt_floor_add_one (y*(2:ℚ)^P+1/2)
  simp only [observation,Vector.get_eq_getElem,Vector.getElem_ofFn]
  change z.natAbs ≤ _
  have hz : |(z:ℚ)| ≤ (m:ℚ)*T*C*2^P+1 := by
    dsimp [z]; exact abs_le.mpr ⟨by linarith [lr.1],by linarith [lr.2]⟩
  have zi : |z|≤((m*T*C*2^P+1:ℕ):ℤ) := by exact_mod_cast hz
  rw [Int.abs_eq_natAbs] at zi
  exact_mod_cast zi

/-- The full rounded matrix and right-hand side are bounded before a minor
is selected, so this input bound also covers singular and inconsistent minors. -/
theorem constructed_observation_height {n ell u v w z : ℕ} (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b:=n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
        w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel → ∀ {lat}, stageTwo rel=some lat →
    ∀ {cols}, markColumns s rel=some cols →
    let d := 2*s.degree-2
    let P := TryPair.localBits s rel
    let H := rel.marks.length*(rel.rows.length+1).factorial*(2*s.degree*(s.L₀+1)+1)*2^P+1
    (∀ i,((observation cols lat.particular P).get i).natAbs≤H) ∧
    ∀ j i,(((lat.directions.map (fun direction=>observation cols direction P)).get j).get i).natAbs≤H := by
  intro s rel stage lat solved cols computed d P H
  obtain ⟨roots,cols',_,good,acc⟩ := Construction.constructed_column_accuracy hn big target box stage
  cases Option.some.inj (good.symm.trans computed)
  have small (j k) : |(cols.get j).get k| ≤ ((2*s.degree*(s.L₀+1)+1:ℕ):ℚ) := by
    obtain ⟨err,amp⟩ := acc j k
    have perturb := (abs_sub_abs_le_abs_sub _ _).trans err
    have power : (1/2:ℝ)^P≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    have realBound : |((cols.get j).get k:ℝ)|≤((2*s.degree*(s.L₀+1)+1:ℕ):ℝ) := by
      push_cast; linarith
    exact_mod_cast realBound
  have height := stageTwo_height solved
  constructor
  · exact observation_height _ _ P small height.1.2
  · intro j k
    simpa only [Vector.get_eq_getElem,Vector.getElem_map] using
      observation_height _ _ P small (height.2 j).2 k

/-- The observed archimedean system supplies the coordinate heights required by
binary reconstruction for every candidate minor that returns a solution. -/
theorem constructed_minor_width {n ell u v w z : ℕ} (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b:=n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
        w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel → ∀ {lat}, stageTwo rel=some lat →
    ∀ {cols}, markColumns s rel=some cols →
    let d := 2*s.degree-2
    let P := TryPair.localBits s rel
    let H := rel.marks.length*(rel.rows.length+1).factorial*(2*s.degree*(s.L₀+1)+1)*2^P+1
    ∀ {indices x}, solveColumns (observation cols lat.particular P)
        (lat.directions.map (fun direction=>observation cols direction P)) indices=some x →
      ∀ i, (x i).num.natAbs.size ≤ fillExponent d d H+1 ∧ (x i).den.size ≤ fillExponent d d H+1 := by
  intro s rel stage lat solved cols computed d P H indices x found i
  obtain ⟨rhs,columns⟩ := constructed_observation_height hn big target box stage solved computed
  exact minor_solution_width (H:=H) (by dsimp [H];omega) rhs columns found i

end Cogentic.Concrete
