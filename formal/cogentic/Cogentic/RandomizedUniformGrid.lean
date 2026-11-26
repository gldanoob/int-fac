import Cogentic.RandomizedPrivateGates

/-! Exact arithmetic for uniform private screening grids. -/

namespace Cogentic.RandomizedUniformGrid

open Finset
open scoped BigOperators

/-- The second moment of the first `m` points of an arithmetic progression. -/
theorem sum_uniform_grid_sq (m : ℕ) (a d : ℝ) :
    (∑ i ∈ range m, (a + (i : ℝ) * d) ^ 2) =
      (m : ℝ) * a ^ 2 + a * d * (m : ℝ) * ((m : ℝ) - 1) +
        d ^ 2 * (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring

/-- Assigning the unused size-weighted budget to the endpoint equalizes the gates. -/
theorem uniform_grid_remainder_gate (a d h budget : ℝ) {i m : ℕ}
    (hi : i ≤ m) (hendpoint : a + (m : ℝ) * d = 1) :
    h * (a + (i : ℝ) * d) + (∑ _j ∈ Ico i m, h * d) +
        (budget - h * d * ∑ j ∈ range m, (a + (j : ℝ) * d) ^ 2) =
      h + (budget - h * d * ∑ j ∈ range m, (a + (j : ℝ) * d) ^ 2) := by
  have hgap (j : ℕ) :
      h * ((a + ((j + 1 : ℕ) : ℝ) * d) - (a + (j : ℝ) * d)) = h * d := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  simpa only [hgap, hendpoint, mul_one] using
    RandomizedPrivateGates.gate_equalization (fun j ↦ a + (j : ℝ) * d) h
      (budget - h * d * ∑ j ∈ range m, (a + (j : ℝ) * d) ^ 2) hi

end Cogentic.RandomizedUniformGrid
