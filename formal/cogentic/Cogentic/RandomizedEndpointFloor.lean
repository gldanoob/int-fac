import Cogentic.RandomizedScheduleFloor
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Cogentic.Randomized

/-- Rescaling the private grid preserves the gate costs and rescales both sides of its
moment constraint by `1 / Z^2`. The physical height uses `x = 2 / (3 * curve^2)`
and the original endpoint `Z`. -/
theorem finite_grid_schedule_floor_of_endpoint {n : ℕ} (z w : ℕ → ℝ)
    (b δ curve h ratio v height Z : ℝ) (hb : 0 < b) (hd : 0 < δ) (hc : 0 < curve)
    (hZ : 0 < Z) (hh : curve ≤ h) (hz0 : z 0 = 0) (hzn : z n = Z)
    (hstep : ∀ i < n, z i ≤ z (i + 1))
    (htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ 10773/5000 - b - h * z (i + 1))
    (hmoment : 4 / (9 * curve^2) ≤ ∑ i ∈ Finset.range n, z (i + 1)^2 * w i)
    (hslope : 0 ≤ 2 * (b / δ) - 1 / 3)
    (hheight : (1 + δ * Z^2 / (2 * (2 / (3 * curve^2)))) / δ^3 ≤ height)
    (hbox : height + v ≤ ratio * (b / δ))
    (hmean : ratio / 3 + 1 / (3 * δ^2 * b) ≤ 2 * v - b / δ)
    (hraw : b + δ * ratio / 3 + 1 / (3 * δ * b) ≤ 10773/5000) : False := by
  refine finite_grid_schedule_floor (n := n) (fun i ↦ z i / Z) w b δ (curve * Z) (h * Z)
    ratio v height hb hd (mul_pos hc hZ) (mul_le_mul_of_nonneg_right hh hZ.le)
    (by simp [hz0]) (by simp [hzn, hZ.ne']) ?_ ?_ ?_ hslope ?_ hbox hmean hraw
  · exact fun i hi ↦ div_le_div_of_nonneg_right (hstep i hi) hZ.le
  · intro i hi
    have he : h * Z * (z (i + 1) / Z) = h * z (i + 1) := by field_simp
    simpa only [he] using htail i hi
  · have he (i : ℕ) : (z (i + 1) / Z)^2 * w i = (z (i + 1)^2 * w i) / Z^2 := by
      rw [div_pow, div_mul_eq_mul_div]
    simp_rw [he]
    have hscale : 4 / (9 * (curve * Z)^2) = (4 / (9 * curve^2)) / Z^2 := by
      field_simp
    rw [hscale]
    simpa only [div_eq_mul_inv, Finset.sum_mul] using
      div_le_div_of_nonneg_right hmoment (sq_nonneg Z)
  · have he : δ / (2 * (2 / (3 * (curve * Z)^2))) =
        δ * Z^2 / (2 * (2 / (3 * curve^2))) := by
      field_simp
    simpa only [he] using hheight

end Cogentic.Randomized

#print axioms Cogentic.Randomized.finite_grid_schedule_floor_of_endpoint
