import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

namespace Cogentic.RandomizedBudgetLimit

open Filter
open scoped Topology

variable {ι : Type*} {l : Filter ι} {H x y : ι → ℝ} {a b : ℝ}

/-- Normalized logarithmic costs add when the costs are multiplied. -/
theorem product_limit (hx : ∀ᶠ n in l, 0 < x n) (hy : ∀ᶠ n in l, 0 < y n)
    (ha : Tendsto (fun n ↦ Real.log (x n) / H n) l (𝓝 a))
    (hb : Tendsto (fun n ↦ Real.log (y n) / H n) l (𝓝 b)) :
    Tendsto (fun n ↦ Real.log (x n * y n) / H n) l (𝓝 (a + b)) := by
  apply (ha.add hb).congr'
  filter_upwards [hx, hy] with n hxn hyn
  simp [Real.log_mul hxn.ne' hyn.ne', add_div]

/-- Adding positive costs has the larger normalized logarithmic limit. -/
theorem sum_limit (hH : Tendsto H l atTop)
    (hx : ∀ᶠ n in l, 0 < x n) (hy : ∀ᶠ n in l, 0 < y n)
    (ha : Tendsto (fun n ↦ Real.log (x n) / H n) l (𝓝 a))
    (hb : Tendsto (fun n ↦ Real.log (y n) / H n) l (𝓝 b)) :
    Tendsto (fun n ↦ Real.log (x n + y n) / H n) l (𝓝 (max a b)) := by
  have hmax := ha.max hb
  have hupper : Tendsto
      (fun n ↦ max (Real.log (x n) / H n) (Real.log (y n) / H n) + Real.log 2 / H n)
      l (𝓝 (max a b)) := by
    simpa only [add_zero] using hmax.add (hH.const_div_atTop (Real.log 2))
  apply hmax.squeeze' hupper
  · filter_upwards [hx, hy, hH.eventually_gt_atTop 0] with n hxn hyn hHn
    exact max_le
      (div_le_div_of_nonneg_right (Real.log_le_log hxn (le_add_of_nonneg_right hyn.le)) hHn.le)
      (div_le_div_of_nonneg_right (Real.log_le_log hyn (le_add_of_nonneg_left hxn.le)) hHn.le)
  · filter_upwards [hx, hy, hH.eventually_gt_atTop 0] with n hxn hyn hHn
    have hm : 0 < max (x n) (y n) := hxn.trans_le (le_max_left _ _)
    calc
      Real.log (x n + y n) / H n ≤ Real.log (2 * max (x n) (y n)) / H n := by
        apply div_le_div_of_nonneg_right _ hHn.le
        apply Real.log_le_log (add_pos hxn hyn)
        simpa only [two_mul] using add_le_add (le_max_left (x n) (y n)) (le_max_right _ _)
      _ = Real.log (max (x n) (y n)) / H n + Real.log 2 / H n := by
        rw [Real.log_mul (by norm_num) hm.ne', add_div, add_comm]
      _ ≤ _ := by
        apply add_le_add_left
        rcases le_total (x n) (y n) with h | h
        · rw [max_eq_right h]
          exact le_max_right _ _
        · rw [max_eq_left h]
          exact le_max_left _ _

end Cogentic.RandomizedBudgetLimit

#print axioms Cogentic.RandomizedBudgetLimit.product_limit
#print axioms Cogentic.RandomizedBudgetLimit.sum_limit
