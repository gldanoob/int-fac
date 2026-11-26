import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

/-- The two-cost model's terminal slack bounds the private slack at an exact
stationary point, with weight given by the terminal parabola's slope. -/
theorem stationary_terminal_slack (u C s b₀ b δ v : ℝ)
    (hu : 0 < u) (hd : 0 < δ) (hv : 0 < v) (hsq : s^2 = C)
    (hb₀ : b₀ = C - (4/(9*u^2) + 2*u/3)) (hgap : 0 < C - 2*b₀)
    (hvalue : 6*b₀*(C-b₀) = 3*u^2/2 + 4*s)
    (hslope : 6*(C-2*b₀)*(2/3-8/(9*u^3)) = -3*u) :
    6*(C-2*b₀)*(C - (b + 4/(9*v^2) + 2*v/3)) ≤
      3*v^2/2 + 4/δ + C*δ - 6*b*(C-b) := by
  have hδ : 4*s ≤ 4/δ + C*δ := by
    have he : (4/δ + C*δ)*δ = 4 + C*δ^2 := by field_simp
    apply le_of_mul_le_mul_right (a := δ) _ hd
    rw [he, ← hsq]
    nlinarith only [sq_nonneg (s*δ-2)]
  have hinv : 3/u^2 - 2*v/u^3 ≤ 1/v^2 := by
    field_simp
    nlinarith only [mul_nonneg (sq_nonneg (v-u)) (show 0 ≤ 2*v+u by positivity)]
  have hprivate : 4/(9*u^2) + 2*u/3 + (2/3-8/(9*u^3))*(v-u) ≤
      4/(9*v^2) + 2*v/3 := by
    have he : 4/(9*u^2) + 2*u/3 + (2/3-8/(9*u^3))*(v-u) =
        (4/9)*(3/u^2 - 2*v/u^3) + 2*v/3 := by
      field_simp
      ring
    have hv' : 4/(9*v^2) = (4/9)*(1/v^2) := by ring
    rw [he, hv']
    exact add_le_add_left (mul_le_mul_of_nonneg_left hinv (show 0 ≤ (4/9 : ℝ) by norm_num)) _
  have hweight : 0 < 6*(C-2*b₀) := by positivity
  have hprivate' := mul_le_mul_of_nonneg_left hprivate hweight.le
  have hstationary := congrArg (fun a : ℝ ↦ a*(v-u)) hslope
  have hbudget := congrArg (fun a : ℝ ↦ 6*(C-2*b₀)*a) hb₀
  nlinarith only [hδ, hprivate', hstationary, hbudget, hvalue,
    sq_nonneg (b-b₀), sq_nonneg (v-u)]

/-- A strict private improvement over the stationary ceiling cannot satisfy
the terminal cost bound. -/
theorem stationary_schedule_floor (u C s b₀ b δ v : ℝ)
    (hu : 0 < u) (hd : 0 < δ) (hv : 0 < v) (hsq : s^2 = C)
    (hb₀ : b₀ = C - (4/(9*u^2) + 2*u/3)) (hgap : 0 < C - 2*b₀)
    (hvalue : 6*b₀*(C-b₀) = 3*u^2/2 + 4*s)
    (hslope : 6*(C-2*b₀)*(2/3-8/(9*u^3)) = -3*u)
    (hprivate : b + 4/(9*v^2) + 2*v/3 < C)
    (hterminal : 3*v^2/2 + 4/δ + C*δ ≤ 6*b*(C-b)) : False := by
  have h := stationary_terminal_slack u C s b₀ b δ v hu hd hv hsq hb₀ hgap hvalue hslope
  have hpos : 0 < 6*(C-2*b₀)*(C - (b + 4/(9*v^2) + 2*v/3)) :=
    mul_pos (by positivity) (sub_pos.mpr hprivate)
  linarith only [h, hpos, hterminal]

end Cogentic.Randomized
