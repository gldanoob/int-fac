import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Cogentic.Randomized

/-- Rational witnesses can separate the private and terminal cost constraints
even when the terminal tradeoff retains only the radix height. -/
theorem radix_schedule_floor_of_witness (b δ v C a s : ℝ)
    (hd : 0 < δ) (hv : 0 < v) (ha : 0 ≤ a) (ha3 : a^3 ≤ 4/3)
    (hC : C ≤ 2*a) (hs : s^2 ≤ C) (hsep : 6*a*(C-a) < 4*s)
    (hprivate : b + 4/(9*v^2) + 2*v/3 ≤ C)
    (hterminal : 4/δ + C*δ ≤ 6*b*(C-b)) : False := by
  have hprod : 0 ≤ 6*(v-a)^2*(v+a/2) := by positivity
  have hprivateMin : a ≤ 4/(9*v^2) + 2*v/3 := by
    field_simp
    nlinarith only [hprod, ha3]
  have hb₀ : b ≤ C-a := by linarith only [hprivateMin, hprivate]
  have hb₁ : b ≤ a := by linarith only [hb₀, hC]
  have hright : 6*b*(C-b) ≤ 6*a*(C-a) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hb₀) (sub_nonneg.mpr hb₁)]
  have hleft : 4*s ≤ 4/δ + C*δ := by
    have he : (4/δ + C*δ)*δ = 4 + C*δ^2 := by field_simp
    apply le_of_mul_le_mul_right (a := δ) _ hd
    rw [he]
    nlinarith only [sq_nonneg (s*δ-2), mul_le_mul_of_nonneg_right hs (sq_nonneg δ)]
  exact (not_lt_of_ge (hleft.trans (hterminal.trans hright))) hsep

/-- A ceiling of 1.94548659 is infeasible in the radix-only height model. -/
theorem radix_schedule_floor (b δ v : ℝ) (hd : 0 < δ) (hv : 0 < v)
    (hprivate : b + 4/(9*v^2) + 2*v/3 ≤ 194548659/100000000)
    (hterminal : 4/δ + (194548659/100000000)*δ ≤ 6*b*(194548659/100000000-b)) :
    False := by
  apply radix_schedule_floor_of_witness b δ v _ (1100642416/1000000000) (1394807008/1000000000)
    hd hv _ _ _ _ _ hprivate hterminal <;> norm_num

end Cogentic.Randomized
