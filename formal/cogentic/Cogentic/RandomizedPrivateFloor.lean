import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The finite-grid lower bound for the private screening budget. -/

namespace Cogentic

open scoped BigOperators

/-- Tail caps at the right endpoints imply the integrated private screening bound. -/
theorem finite_stage_private_floor {n : ℕ} (z w : ℕ → ℝ) {h P : ℝ}
    (hh : 0 ≤ h) (hz0 : z 0 = 0) (hzn : z n = 1)
    (hstep : ∀ i < n, z i ≤ z (i + 1))
    (htail : ∀ i < n, (∑ j ∈ Finset.Ico i n, w j) ≤ P - h * z (i + 1)) :
    (∑ i ∈ Finset.range n, z (i + 1) ^ 2 * w i) + 2 * h / 3 ≤ P := by
  let tail (i : ℕ) := ∑ j ∈ Finset.Ico i n, w j
  have tail_step (i : ℕ) (hi : i < n) : tail i = w i + tail (i + 1) := by
    exact Finset.sum_eq_sum_Ico_succ_bot hi w
  have hz : ∀ i ≤ n, 0 ≤ z i := by
    intro i
    induction i with
    | zero => simp [hz0]
    | succ i ih =>
      intro hi
      exact (ih (Nat.le_of_succ_le hi)).trans (hstep i (Nat.lt_of_succ_le hi))
  have hparts : (∑ i ∈ Finset.range n, z (i + 1) ^ 2 * w i) =
      ∑ i ∈ Finset.range n, (z (i + 1) ^ 2 - z i ^ 2) * tail i := by
    calc
      _ = ∑ i ∈ Finset.range n, ((z (i + 1) ^ 2 - z i ^ 2) * tail i -
          (z (i + 1) ^ 2 * tail (i + 1) - z i ^ 2 * tail i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [tail_step i (Finset.mem_range.mp hi)]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => z i ^ 2 * tail i)]
        simp [tail, hz0]
  have hbound : (∑ i ∈ Finset.range n, (z (i + 1) ^ 2 - z i ^ 2) * tail i) ≤
      ∑ i ∈ Finset.range n,
        (P * (z (i + 1) ^ 2 - z i ^ 2) - (2 * h / 3) * (z (i + 1) ^ 3 - z i ^ 3)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hin := Finset.mem_range.mp hi
    have hleft := hz i hin.le
    have hright := hz (i + 1) (Nat.succ_le_of_lt hin)
    have hinc := hstep i hin
    have hsq : 0 ≤ z (i + 1) ^ 2 - z i ^ 2 :=
      sub_nonneg.mpr (pow_le_pow_left₀ hleft hinc 2)
    have hres : 0 ≤ (z (i + 1) - z i) ^ 2 * (z (i + 1) + 2 * z i) / 3 := by
      positivity
    have hcubic : (2 : ℝ) / 3 * (z (i + 1) ^ 3 - z i ^ 3) ≤
        (z (i + 1) ^ 2 - z i ^ 2) * z (i + 1) := by
      nlinarith only [hres]
    calc
      _ ≤ (z (i + 1) ^ 2 - z i ^ 2) * (P - h * z (i + 1)) :=
        mul_le_mul_of_nonneg_left (htail i hin) hsq
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hcubic hh]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_range_sub (fun i => z i ^ 2), Finset.sum_range_sub (fun i => z i ^ 3),
    hz0, hzn] at hbound
  rw [hparts]
  linarith only [hbound]

end Cogentic
