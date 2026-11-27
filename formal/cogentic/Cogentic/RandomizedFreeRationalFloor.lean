import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Cogentic

/-- The reduced full-population constraints fail at coefficient 1.95 even when
testing the rational candidates is free. -/
theorem randomizedFreeRationalFloor {v δ b : ℝ}
    (hv : 0 < v) (hδ : 0 < δ) (hb : 0 < b)
    (population : b + 4 / (9 * v ^ 2) + 2 * v / 3 ≤ 39 / 20)
    (height : 3 * v ^ 2 / 2 + 2 / δ + 1 / (3 * b) + (39 / 20) * δ ≤
      6 * b * (39 / 20 - b)) :
    False := by
  have v_tangent : (48 / 25 : ℝ) - (192 / 125) * v ≤ 4 / (9 * v ^ 2) := by
    apply (le_div_iff₀ (show 0 < 9 * v ^ 2 by positivity)).mpr
    have h := mul_nonneg (sq_nonneg (v - 5 / 6)) (show 0 ≤ 2 * v + 5 / 6 by positivity)
    nlinarith only [h]
  have b_tangent : (8 / 9 : ℝ) - (16 / 27) * b ≤ 1 / (3 * b) := by
    apply (le_div_iff₀ (show 0 < 3 * b by positivity)).mpr
    nlinarith only [sq_nonneg (b - 3 / 4)]
  have δ_bound : (987 / 250 : ℝ) ≤ 2 / δ + (39 / 20) * δ := by
    have h : (987 / 250 : ℝ) - (39 / 20) * δ ≤ 2 / δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith only [sq_nonneg (δ - (987 / 975 : ℝ))]
    linarith only [h]
  have weighted : 3 * v ^ 2 / 2 + 3 * (48 / 25 - (192 / 125) * v) +
      2 * v + 6 * b ^ 2 + (3 - 6 * (39 / 20)) * b + 8 / 9 -
      (16 / 27) * b + 987 / 250 - 3 * (39 / 20) ≤ 0 := by
    nlinarith only [population, height, v_tangent, b_tangent, δ_bound]
  nlinarith only [weighted, sq_nonneg (v - 326 / 375), sq_nonneg (b - 2509 / 3240)]

end Cogentic
