import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedPrivateGates

open Finset
open scoped BigOperators

theorem step_weight_nonneg {h a b : ℝ} (hh : 0 ≤ h) (hab : a ≤ b) :
    0 ≤ h * (b - a) :=
  mul_nonneg hh (sub_nonneg.mpr hab)

theorem step_weight_pos {h a b : ℝ} (hh : 0 < h) (hab : a < b) :
    0 < h * (b - a) :=
  mul_pos hh (sub_pos.mpr hab)

/-- The stage cost and the remaining gap weights telescope to the final stage cost. -/
theorem gate_equalization (z : ℕ → ℝ) (h terminal : ℝ) {i n : ℕ} (hi : i ≤ n) :
    h * z i + (∑ j ∈ Ico i n, h * (z (j + 1) - z j)) + terminal =
      h * z n + terminal := by
  simp_rw [mul_sub]
  rw [sum_Ico_eq_sub _ hi, sum_range_sub (fun j ↦ h * z j),
    sum_range_sub (fun j ↦ h * z j)]
  linarith

/-- The size-weighted interior stages are bounded by the integral of the squared cutoff. -/
theorem weighted_gap_sum_le (z : ℕ → ℝ) {h : ℝ} {n : ℕ} (hh : 0 ≤ h)
    (hstep : ∀ j < n, z j ≤ z (j + 1)) (hzero : ∀ j < n, 0 ≤ z j) :
    (∑ j ∈ range n, (z j) ^ 2 * (h * (z (j + 1) - z j))) ≤
      (h / 3) * ((z n) ^ 3 - (z 0) ^ 3) := by
  calc
    _ ≤ ∑ j ∈ range n, (h / 3) * ((z (j + 1)) ^ 3 - (z j) ^ 3) := by
      apply sum_le_sum
      intro j hj
      have ha := hzero j (mem_range.mp hj)
      have hb := ha.trans (hstep j (mem_range.mp hj))
      apply sub_nonneg.mp
      calc
        0 ≤ (h / 3) * (z (j + 1) - z j) ^ 2 * (z (j + 1) + 2 * z j) := by
          exact mul_nonneg (mul_nonneg (div_nonneg hh (by norm_num)) (sq_nonneg _))
            (add_nonneg hb (mul_nonneg (by norm_num) ha))
        _ = _ := by ring
    _ = _ := by rw [← mul_sum, sum_range_sub (fun j ↦ (z j) ^ 3)]

/-- A strict budget above the cubic bound leaves a positive terminal weight. -/
theorem terminal_weight_pos (z : ℕ → ℝ) {h budget : ℝ} {n : ℕ} (hh : 0 ≤ h)
    (hstep : ∀ j < n, z j ≤ z (j + 1)) (hzero : ∀ j < n, 0 ≤ z j)
    (hbudget : (h / 3) * ((z n) ^ 3 - (z 0) ^ 3) < budget) :
    0 < budget - ∑ j ∈ range n, (z j) ^ 2 * (h * (z (j + 1) - z j)) :=
  sub_pos.mpr ((weighted_gap_sum_le z hh hstep hzero).trans_lt hbudget)

end Cogentic.RandomizedPrivateGates

#print axioms Cogentic.RandomizedPrivateGates.step_weight_nonneg
#print axioms Cogentic.RandomizedPrivateGates.step_weight_pos
#print axioms Cogentic.RandomizedPrivateGates.gate_equalization
#print axioms Cogentic.RandomizedPrivateGates.weighted_gap_sum_le
#print axioms Cogentic.RandomizedPrivateGates.terminal_weight_pos
