import Cogentic.RandomizedWidthOneGate
import Mathlib.Analysis.Real.Sqrt

namespace Cogentic.RandomizedWidthOneGate

/-- Use the same rational coefficient for the curve count and the per-curve
work. Here 1/(9·moment) is 2y₀/(3δ), since y₀=1/(2κ) and moment=κδ/3. -/
theorem fixed_curve_allowance :
    let s : ℝ := 707106781187 / 10^12
    1/Real.sqrt 2 < s ∧ (s+s) * Real.sqrt (1/(9*moment)) < curve := by
  dsimp only
  constructor
  · rw [one_div, ← Real.sqrt_inv, Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  · apply (sq_lt_sq₀ (by positivity) (by norm_num [curve])).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num [moment])]
    norm_num [curve, moment]

#print axioms fixed_curve_allowance

end Cogentic.RandomizedWidthOneGate
