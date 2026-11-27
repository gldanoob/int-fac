import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedFixedMoebius

noncomputable def denominator (z : ℂ) : ℂ := 12 * z + 7

/-- The linear-fractional map of the matrix with rows (7,4) and (12,7). -/
noncomputable def transform (z : ℂ) : ℂ := (7 * z + 4) / denominator z

private theorem normSq_denominator (z : ℂ) :
    Complex.normSq (denominator z) = 144 * Complex.normSq z + 168 * z.re + 49 := by
  simp [denominator, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private theorem normSq_numerator (z : ℂ) :
    Complex.normSq (7 * z + 4) = 49 * Complex.normSq z + 56 * z.re + 16 := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem denominator_normSq_ge {z : ℂ} (hz : 0 ≤ z.re) :
    49 ≤ Complex.normSq (denominator z) := by
  rw [normSq_denominator]
  linarith only [Complex.normSq_nonneg z, hz]

private theorem denominator_normSq_pos {z : ℂ} (hz : 0 ≤ z.re) :
    0 < Complex.normSq (denominator z) :=
  lt_of_lt_of_le (by norm_num) (denominator_normSq_ge hz)

theorem denominator_ne_zero {z : ℂ} (hz : 0 ≤ z.re) : denominator z ≠ 0 :=
  Complex.normSq_pos.mp (denominator_normSq_pos hz)

theorem transform_im (z : ℂ) :
    (transform z).im = z.im / Complex.normSq (denominator z) := by
  rw [transform, Complex.div_im, ← sub_div]
  congr 1
  simp [denominator, Complex.mul_re, Complex.mul_im]
  ring

private theorem transform_re (z : ℂ) :
    (transform z).re =
      (84 * Complex.normSq z + 97 * z.re + 28) / Complex.normSq (denominator z) := by
  rw [transform, Complex.div_re, ← add_div]
  congr 1
  simp [denominator, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- On the closed right half-plane the real part lies between the two
column slopes of the fixed matrix. -/
theorem transform_re_bounds {z : ℂ} (hz : 0 ≤ z.re) :
    (4 : ℝ) / 7 ≤ (transform z).re ∧ (transform z).re < (7 : ℝ) / 12 := by
  rw [transform_re]
  constructor
  · apply (le_div_iff₀ (denominator_normSq_pos hz)).2
    rw [normSq_denominator]
    linarith only [Complex.normSq_nonneg z, hz]
  · apply (div_lt_iff₀ (denominator_normSq_pos hz)).2
    rw [normSq_denominator]
    linarith only [hz]

theorem transform_normSq_lt {z : ℂ} (hz : 0 ≤ z.re) :
    Complex.normSq (transform z) < ((7 : ℝ) / 12) ^ 2 := by
  rw [transform, Complex.normSq_div]
  apply (div_lt_iff₀ (denominator_normSq_pos hz)).2
  rw [normSq_numerator, normSq_denominator]
  norm_num
  linarith only [hz]

theorem transform_im_bounds {z : ℂ} (hz : 0 ≤ z.re) (hy : 0 < z.im) :
    0 < (transform z).im ∧ (transform z).im ≤ z.im / 49 := by
  rw [transform_im]
  exact ⟨div_pos hy (denominator_normSq_pos hz),
    div_le_div_of_nonneg_left hy.le (by norm_num) (denominator_normSq_ge hz)⟩

theorem transform_sub {z w : ℂ} (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    transform z - transform w = (z - w) / (denominator z * denominator w) := by
  simp only [transform]
  field_simp [denominator_ne_zero hz, denominator_ne_zero hw]
  unfold denominator
  ring

private theorem seven_le_norm_denominator {z : ℂ} (hz : 0 ≤ z.re) :
    7 ≤ ‖denominator z‖ := by
  calc
    _ ≤ (denominator z).re := by
      simp [denominator, Complex.mul_re]
      linarith only [hz]
    _ ≤ _ := Complex.re_le_norm _

/-- The same map contracts Euclidean distances by a factor at most 1/49. -/
theorem transform_norm_sub_le {z w : ℂ} (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    ‖transform z - transform w‖ ≤ ‖z - w‖ / 49 := by
  rw [transform_sub hz hw, Complex.norm_div, Complex.norm_mul]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num)
  calc
    49 = (7 : ℝ) * 7 := by norm_num
    _ ≤ ‖denominator z‖ * ‖denominator w‖ :=
      mul_le_mul (seven_le_norm_denominator hz) (seven_le_norm_denominator hw)
        (by norm_num) (norm_nonneg _)

#print axioms transform_im
#print axioms transform_re_bounds
#print axioms transform_normSq_lt
#print axioms transform_im_bounds
#print axioms transform_norm_sub_le

end Cogentic.RandomizedFixedMoebius
