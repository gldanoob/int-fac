import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- A conditional failure bound of one quarter gives geometric survival. -/
theorem quarter_survival_le (p : ℕ → ℝ) (h₀ : p 0 ≤ 1)
    (hstep : ∀ j, p (j + 1) ≤ (1/4 : ℝ) * p j) :
    ∀ j, p j ≤ (1/4 : ℝ)^j := by
  intro j
  induction j with
  | zero => simpa using h₀
  | succ j ih =>
    calc
      p (j + 1) ≤ (1/4 : ℝ) * p j := hstep j
      _ ≤ (1/4 : ℝ) * (1/4 : ℝ)^j := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1/4 : ℝ)^(j + 1) := by rw [pow_succ, mul_comm]

/-- Exact total budget of the first `m` deterministic dyadic phases. -/
theorem dyadic_restart_prefix_sum (a : ℝ) (m : ℕ) :
    (∑ j ∈ range m, a * (2 : ℝ)^j) = a * ((2 : ℝ)^m - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- The prefix through phase `m` costs at most twice that phase's budget. -/
theorem dyadic_restart_prefix_sum_le (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    (∑ j ∈ range (m + 1), a * (2 : ℝ)^j) ≤ 2 * (a * (2 : ℝ)^m) := by
  rw [dyadic_restart_prefix_sum, pow_succ]
  linarith only [ha]

private theorem dyadic_restart_term_le (T p : ℝ) (hT : 0 ≤ T) (j : ℕ)
    (hp : p ≤ (1/4 : ℝ)^j) : T * (2 : ℝ)^j * p ≤ T * (1/2 : ℝ)^j := by
  calc
    T * (2 : ℝ)^j * p ≤ T * (2 : ℝ)^j * (1/4 : ℝ)^j :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = T * (1/2 : ℝ)^j := by rw [mul_assoc, ← mul_pow]; norm_num

/-- Expected cost through a finite number of restart phases, counting phase
zero with budget `T`. The geometric envelope is attained for exact survival. -/
theorem dyadic_restart_tail_sum_le (T : ℝ) (hT : 0 ≤ T) (p : ℕ → ℝ)
    (hp : ∀ j, p j ≤ (1/4 : ℝ)^j) (n : ℕ) :
    (∑ j ∈ range n, T * (2 : ℝ)^j * p j) ≤ 2 * T * (1 - (1/2 : ℝ)^n) := by
  calc
    _ ≤ ∑ j ∈ range n, T * (1/2 : ℝ)^j :=
      sum_le_sum fun j _ ↦ dyadic_restart_term_le T (p j) hT j (hp j)
    _ = _ := by
      rw [← mul_sum, geom_sum_eq (by norm_num : (1/2 : ℝ) ≠ 1)]
      ring

/-- The uncapped restart cost is summable and bounded by twice the first
restart budget. -/
theorem dyadic_restart_tail_tsum_le (T : ℝ) (hT : 0 ≤ T) (p : ℕ → ℝ)
    (hnonneg : ∀ j, 0 ≤ p j) (hp : ∀ j, p j ≤ (1/4 : ℝ)^j) :
    Summable (fun j : ℕ ↦ T * (2 : ℝ)^j * p j) ∧
      (∑' j : ℕ, T * (2 : ℝ)^j * p j) ≤ 2*T := by
  have hgeom := hasSum_geometric_two.mul_left T
  have hterm (j : ℕ) := dyadic_restart_term_le T (p j) hT j (hp j)
  have hsum := Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (by positivity) (hnonneg j))
    hterm hgeom.summable
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' j : ℕ, T * (1/2 : ℝ)^j := hsum.tsum_le_tsum hterm hgeom.summable
    _ = 2*T := by rw [hgeom.tsum_eq, mul_comm]

/-- The phases strictly before `m` are a deterministic prefix. From phase
`m` onward the survival-weighted phases start with budget `a * 2^m`. -/
theorem dyadic_restart_total_tsum_le (a : ℝ) (ha : 0 ≤ a) (m : ℕ) (p : ℕ → ℝ)
    (hnonneg : ∀ j, 0 ≤ p j) (hp : ∀ j, p j ≤ (1/4 : ℝ)^j) :
    (∑ j ∈ range m, a * (2 : ℝ)^j) +
      (∑' j : ℕ, (a * (2 : ℝ)^m) * (2 : ℝ)^j * p j) ≤ 3 * (a * (2 : ℝ)^m) := by
  have htail := (dyadic_restart_tail_tsum_le (a * (2 : ℝ)^m) (by positivity) p hnonneg hp).2
  rw [dyadic_restart_prefix_sum]
  linarith only [ha, htail]

end Cogentic.Randomized
