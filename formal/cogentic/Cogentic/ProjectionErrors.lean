import Cogentic.Concrete
import Cogentic.EliminationBounds

namespace Cogentic.Concrete
open ArchNumerics Finset

noncomputable def exactProjection (j : ℕ) (L : ℕ → ℝ) :=
  Real.sqrt (1/((j:ℝ)*(j+1)))*((∑ k ∈ range j, L k)-(j:ℝ)*L j)

private theorem weighted_sum_error {ι : Type*} [Fintype ι] {a b : ι → ℝ} {T e : ℝ}
    (bound : ∀ i, |a i| ≤ T) (close : ∀ i, |b i| ≤ e) :
    |∑ i, a i*b i| ≤ (Fintype.card ι:ℝ)*(T*e) := by
  calc
    _ ≤ ∑ i, |a i*b i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, T*e := sum_le_sum (fun i _ => by
      rw [abs_mul]; exact mul_le_mul (bound i) (close i) (abs_nonneg _) ((abs_nonneg _).trans (bound i)))
    _ = _ := by simp

theorem projection_error {d : ℕ} (q : Vector ℚ d) (j bits : ℕ) (positive : 1 ≤ j)
    (L : ℕ → ℝ) (e M : ℝ) (close : ∀ k ≤ j, |(((q.toArray[k]?.getD 0):ℚ):ℝ)-L k| ≤ e)
    (bound : ∀ k ≤ j, |L k| ≤ M) :
    |(projection q j bits:ℝ)-exactProjection j L| ≤ 2*j*(e+M*(1/2:ℝ)^bits) := by
  let u (k : ℕ) : ℝ := ((q.toArray[k]?.getD 0:ℚ):ℝ)
  let t := (∑ k ∈ range j, L k) - (j:ℝ)*L j
  let approx := (∑ k ∈ range j, u k) - (j:ℝ)*u j
  let h := Real.sqrt (1/((j:ℝ)*(j+1)))
  let r := (approxSqrt 1 (j*(j+1)) bits:ℝ)
  have err (k : ℕ) (hk : k ∈ range j) := close k (mem_range.mp hk).le
  have sumError : |(∑ k ∈ range j, (u k-L k))| ≤ j*e := by
    apply (abs_sum_le_sum_abs ..).trans
    simpa [u] using sum_le_sum err
  have absSum : |∑ k ∈ range j, L k| ≤ j*M := by
    apply (abs_sum_le_sum_abs ..).trans
    simpa using sum_le_sum (fun k (hk : k ∈ range j) => bound k (mem_range.mp hk).le)
  have jpos := Nat.cast_nonneg (α := ℝ) j
  have dif : |approx-t| ≤ 2*j*e := by
    have eq : approx-t = (∑ k ∈ range j, (u k-L k))-(j:ℝ)*(u j-L j) := by
      rw [sum_sub_distrib]; dsimp [approx,t]; ring
    rw [eq]
    refine (abs_sub ..).trans ?_
    rw [abs_mul,abs_of_nonneg jpos]
    linarith [mul_le_mul_of_nonneg_left (close j le_rfl) jpos]
  have absT : |t| ≤ 2*j*M := by
    refine (abs_sub ..).trans ?_
    rw [abs_mul,abs_of_nonneg jpos]
    linarith [mul_le_mul_of_nonneg_left (bound j le_rfl) jpos]
  have den : 0 < j*(j+1) := Nat.mul_pos positive (Nat.succ_pos j)
  have hr := approxSqrt_error (u := 1) den bits
  simp only [Nat.cast_mul, Nat.cast_one, Nat.cast_add] at hr
  change 0 ≤ h-r ∧ h-r < (1/2:ℝ)^bits at hr
  have r0 : 0 ≤ r := by dsimp [r,approxSqrt]; positivity
  have h1 : h ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    apply (div_le_one (by positivity)).mpr
    have : (1:ℝ) ≤ j := by exact_mod_cast positive
    nlinarith
  have r1 : |r| ≤ 1 := by rw [abs_of_nonneg r0]; linarith [hr.1]
  have hrE : |r-h| ≤ (1/2:ℝ)^bits := by rw [abs_sub_comm,abs_of_nonneg hr.1]; exact hr.2.le
  have eq : (projection q j bits:ℝ)-exactProjection j L = r*(approx-t)+(r-h)*t := by
    dsimp [projection,exactProjection,r,h,t,approx,u]; push_cast; ring
  rw [eq]
  refine (abs_add_le ..).trans ?_
  rw [abs_mul,abs_mul]
  have e0 := (abs_nonneg _).trans (close j le_rfl)
  have p := mul_le_mul r1 dif (abs_nonneg _) (by norm_num)
  have q' := mul_le_mul hrE absT (abs_nonneg _) (by positivity)
  linarith

theorem roundDyadic_real (q : ℚ) (bits : ℕ) :
    |(roundDyadic q bits:ℝ)-(q:ℝ)| ≤ (1/2:ℝ)^bits/2 := by
  simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using
    ((Rat.cast_le (K := ℝ)).mpr (roundDyadic_error q bits))

/-- Propagate the actual integer kernel coefficients and the last dyadic
    rounding through a complete observed column of the approximate solve. -/
theorem observation_error {marks dim : ℕ} (cols : Vector (Vector ℚ dim) marks)
    (coeffs : Vector ℤ marks) (row : Fin dim) (bits : ℕ) (L : Fin marks → ℝ) (T e : ℝ)
    (bound : ∀ i, |(coeffs.get i:ℝ)| ≤ T) (close : ∀ i, |((cols.get i).get row:ℝ)-L i| ≤ e) :
    |((observation cols coeffs bits).get row:ℝ)/(2:ℝ)^bits-
        ∑ i, (coeffs.get i:ℝ)*L i| ≤ (1/2:ℝ)^bits/2 + marks*(T*e) := by
  let value := ∑ i : Fin marks, (coeffs.get i:ℚ)*(cols.get i).get row
  have eq : ((observation cols coeffs bits).get row:ℝ)/(2:ℝ)^bits = (roundDyadic value bits:ℝ) := by
    simp [observation,Vector.get_eq_getElem,numerator, roundDyadic,value]
  have diff : |(value:ℝ)-(∑ i, (coeffs.get i:ℝ)*L i)| ≤ marks*(T*e) := by
    have weight := weighted_sum_error (a := fun i => (coeffs.get i:ℝ))
      (b := fun i => ((cols.get i).get row:ℝ)-L i) bound close
    dsimp [value]; push_cast
    simpa only [mul_sub,Finset.sum_sub_distrib,Fintype.card_fin] using weight
  rw [eq]
  exact (abs_sub_le _ (value:ℝ) _).trans (add_le_add (roundDyadic_real ..) diff)

theorem lattice_observation_error {rel : Marking.Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (ok : Elimination.stageTwo rel = some out) {dim : ℕ} (cols : Vector (Vector ℚ dim) rel.marks.length)
    (row : Fin dim) (bits : ℕ) (L : Fin rel.marks.length → ℝ) (e : ℝ)
    (close : ∀ i, |((cols.get i).get row:ℝ)-L i| ≤ e) :
    let bound := (1/2:ℝ)^bits/2 + rel.marks.length*((rel.rows.length+1).factorial*e)
    let err (v : Vector ℤ rel.marks.length) :=
      |((observation cols v bits).get row:ℝ)/(2:ℝ)^bits - ∑ i, (v.get i:ℝ)*L i|
    err out.particular ≤ bound ∧ ∀ k, err (out.directions.get k) ≤ bound := by
  have heights := stageTwo_height ok
  constructor
  · apply observation_error _ _ _ _ _ _ _ _ close
    intro i; exact_mod_cast heights.1.2 i
  · intro k
    apply observation_error _ _ _ _ _ _ _ _ close
    intro i; exact_mod_cast (heights.2 k).2 i

end Cogentic.Concrete
