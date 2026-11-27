import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic

open scoped BigOperators

private theorem sum_succ_squares (k : ℕ) :
    (∑ i ∈ Finset.range k, ((i : ℝ) + 1) ^ 2) =
      (k : ℝ) * (k + 1) * (2 * (k : ℝ) + 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_succ]
    ring

/-- A grid with k + 1 stages realizes the exact moment W.
Every gate equals the continuum value plus the displayed error. -/
theorem uniform_private_grid_upper (k : ℕ) {h W : ℝ}
    (hh : 0 < h) (hW : h / 3 < W) :
    let n : ℝ := (k : ℝ) + 1
    let z : ℕ → ℝ := fun i => (i : ℝ) / n
    let error := h / (2 * n) - h / (6 * n ^ 2)
    ∃ w : ℕ → ℝ,
      (∀ i < k, w i = h * (z (i + 2) - z (i + 1))) ∧
      (∀ i < k + 1, 0 < w i) ∧
      (∑ i ∈ Finset.range (k + 1), z (i + 1) ^ 2 * w i) = W ∧
      (∀ i < k + 1,
        h * z (i + 1) + (∑ j ∈ Finset.Ico i (k + 1), w j) = W + 2 * h / 3 + error) ∧
      0 ≤ error ∧ error ≤ h / n := by
  dsimp only
  let n : ℝ := (k : ℝ) + 1
  let z : ℕ → ℝ := fun i => (i : ℝ) / n
  let error := h / (2 * n) - h / (6 * n ^ 2)
  have hn : 0 < n := by dsimp [n]; positivity
  have hn₁ : 1 ≤ n := le_add_of_nonneg_left (Nat.cast_nonneg k)
  let interior := ∑ i ∈ Finset.range k, z (i + 1) ^ 2 * (h / n)
  let w (i : ℕ) := if i < k then h / n else W - interior
  have hz : z (k + 1) = 1 := by simp [z, n, show (k : ℝ) + 1 ≠ 0 from hn.ne']
  have hinterior : interior = h / 3 - error := by
    have hfactor (i : ℕ) : z (i + 1) ^ 2 * (h / n) =
        (h / n ^ 3) * ((i : ℝ) + 1) ^ 2 := by
      simp only [z, Nat.cast_add, Nat.cast_one]
      field_simp
    simp_rw [interior, hfactor]
    rw [← Finset.mul_sum, sum_succ_squares]
    dsimp [error, n]
    field_simp
    ring
  have herror : 0 ≤ error := by
    dsimp [error]
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hprod := mul_nonneg (mul_nonneg hh.le hn.le) (sub_nonneg.mpr hn₁)
    nlinarith only [hprod, mul_nonneg hh.le hn.le]
  have hterminal : 0 < W - interior := by linarith only [hW, hinterior, herror]
  have winterior (i : ℕ) (hi : i < k) : w i = h / n := if_pos hi
  have wterminal : w k = W - interior := if_neg (Nat.lt_irrefl _)
  change ∃ w : ℕ → ℝ,
      (∀ i < k, w i = h * (z (i + 2) - z (i + 1))) ∧
      (∀ i < k + 1, 0 < w i) ∧
      (∑ i ∈ Finset.range (k + 1), z (i + 1) ^ 2 * w i) = W ∧
      (∀ i < k + 1,
        h * z (i + 1) + (∑ j ∈ Finset.Ico i (k + 1), w j) = W + 2 * h / 3 + error) ∧
      0 ≤ error ∧ error ≤ h / n
  refine ⟨w, ?_, ?_, ?_, ?_, herror, ?_⟩
  · intro i hi
    rw [winterior i hi]
    simp only [z, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  · intro i hi
    by_cases hlt : i < k
    · rw [winterior i hlt]
      exact div_pos hh hn
    · have e : i = k := by omega
      simpa only [e, wterminal] using hterminal
  · rw [Finset.sum_range_succ, hz, one_pow, one_mul, wterminal]
    have e : (∑ i ∈ Finset.range k, z (i + 1) ^ 2 * w i) = interior := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [winterior i (Finset.mem_range.mp hi)]
    rw [e]
    ring
  · intro i hi
    have hik : i ≤ k := by omega
    have e : (∑ j ∈ Finset.Ico i k, w j) = (k - i : ℕ) * (h / n) := by
      calc
        _ = ∑ _j ∈ Finset.Ico i k, h / n := by
          refine Finset.sum_congr rfl fun j hj => ?_
          exact winterior j (Finset.mem_Ico.mp hj).2
        _ = _ := by simp [Nat.card_Ico]
    rw [Finset.sum_Ico_succ_top hik, e, wterminal, Nat.cast_sub hik]
    simp only [z, Nat.cast_add, Nat.cast_one]
    have hn_mul : n * (h / n) = h := by field_simp
    have he : h * (((i : ℝ) + 1) / n) + ((k : ℝ) - i) * (h / n) = h := by
      calc
        _ = n * (h / n) := by dsimp [n]; ring
        _ = h := hn_mul
    linarith only [he, hinterior]
  · have hhalf : h / (2 * n) ≤ h / n := by
      exact div_le_div_of_nonneg_left hh.le hn (by linarith only [hn])
    have hlast : 0 ≤ h / (6 * n ^ 2) := by positivity
    dsimp [error]
    linarith only [hhalf, hlast]

end Cogentic
