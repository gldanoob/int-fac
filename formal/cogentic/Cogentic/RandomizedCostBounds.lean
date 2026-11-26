import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace Cogentic.Randomized

/-- In the elliptic recognition budget the two terms are work per curve and
the exponent of the number of curves. The inequality concerns that budget. -/
theorem elliptic_recognition_cost_floor (c : ℝ) (hc : 0 < c) :
    Real.sqrt 2 ≤ c + 1 / (2 * c) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : 0 < 2 * c := by linarith
  have hi : 1 / (2 * c) * (2 * c) = 1 := by
    field_simp
  apply le_of_mul_le_mul_right (a := 2 * c) _ hp
  nlinarith [sq_nonneg (2 * c - Real.sqrt 2)]

theorem elliptic_recognition_cost_attained :
    let c := Real.sqrt 2 / 2
    0 < c ∧ c + 1 / (2 * c) = Real.sqrt 2 := by
  dsimp only
  have hp := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · linarith
  · field_simp
    nlinarith

/-- Eliminating the terminal box height from the smoothness and local-mean
constraints of a two-coordinate descent gives this necessary inequality. -/
theorem terminal_ratio_cost_floor (β a height mean v parent ratio : ℝ)
    (hparent : β ≤ parent)
    (hsmooth : height + v ≤ ratio * β)
    (hmean : ratio / 3 + a / (3 * β) + mean ≤ 2 * v - parent) :
    β + 2 * height + a / (3 * β) + mean ≤ (2 * β - 1 / 3) * ratio := by
  linarith

/-- An exact necessary tradeoff between private search and terminal raw trials
in the reduced two-term cost model. -/
theorem terminal_budget_tradeoff (b δ x c C : ℝ) (hb : 0 < 6 * b - δ)
    (hC : (6 * b^2 + 1 / x + 4 / δ + c * δ^2) / (6 * b - δ) ≤ C) :
    1 / x + 4 / δ + C * δ + c * δ^2 ≤ 6 * b * (C - b) := by
  have h := (div_le_iff₀ hb).mp hC
  linarith

end Cogentic.Randomized
