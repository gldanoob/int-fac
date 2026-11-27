import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedReductionSteps

/-- A centered strict swap that retains at least half the leading coefficient
leaves the trailing coefficient at least the new lead after every shear. -/
theorem heavy_swap_terminal {a b c : ℤ} (hc : c < a) (hhalf : a ≤ 2 * c)
    (hcenter : |2 * b| ≤ a) (k : ℤ) : c ≤ a - 2 * k * b + k ^ 2 * c := by
  have hcpos : 0 < c := by omega
  by_cases hk : k = 0
  · simpa [hk] using hc.le
  have hkn : 1 ≤ |k| := by
    have hpos := abs_pos.mpr hk
    omega
  have hcross : 2 * k * b ≤ |k| * a := by
    calc
      2 * k * b = k * (2 * b) := by ring
      _ ≤ |k * (2 * b)| := le_abs_self _
      _ = |k| * |2 * b| := abs_mul _ _
      _ ≤ |k| * a := mul_le_mul_of_nonneg_left hcenter (abs_nonneg k)
  have hprod := mul_le_mul_of_nonpos_left hhalf (sub_nonpos.mpr hkn)
  have hsq := mul_nonneg (sq_nonneg (|k| - 1)) hcpos.le
  have hpow : |k| ^ 2 = k ^ 2 := sq_abs k
  nlinarith only [hcross, hprod, hsq, congrArg (fun p : ℤ => p * c) hpow]

/-- Rotating an equal-lead tie with negative middle coefficient already
centers it, and the unique next centered shear is zero. -/
theorem negative_tie_rotation {a b : ℤ} (ha : 0 < a) (hb : b < 0)
    (hcenter : -a < 2 * b) :
    0 ≤ -b ∧ -a < 2 * (-b) ∧ 2 * (-b) ≤ a ∧
      ∀ k : ℤ, -a < 2 * (-b + k * a) → 2 * (-b + k * a) ≤ a → k = 0 := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro k hklo hkhi
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h := mul_le_mul_of_nonneg_right (show k ≤ -1 by omega) ha.le
    nlinarith only [h, hklo, hcenter]
  · exact hk
  · have h := mul_le_mul_of_nonneg_right (show 1 ≤ k by omega) ha.le
    nlinarith only [h, hkhi, ha, hb]

/-- All but the last strict swap halve a positive natural-valued leading coefficient. -/
theorem strict_swap_count_le_log2 {n : ℕ} (a : ℕ → ℕ)
    (hpos : ∀ i < n, 0 < a i)
    (hhalf : ∀ i, i + 1 < n → 2 * a (i + 1) ≤ a i) :
    n ≤ (a 0).log2 + 1 := by
  cases n with
  | zero => omega
  | succ n =>
    have hbound (i : ℕ) (hi : i ≤ n) : 2 ^ i * a i ≤ a 0 := by
      induction i with
      | zero => simp
      | succ i ih =>
        calc
          2 ^ (i + 1) * a (i + 1) = 2 ^ i * (2 * a (i + 1)) := by rw [pow_succ, mul_assoc]
          _ ≤ 2 ^ i * a i := Nat.mul_le_mul_left _ (hhalf i (by omega))
          _ ≤ a 0 := ih (by omega)
    have hn : 1 ≤ a n := hpos n (by omega)
    have hp : 2 ^ n ≤ a 0 := by
      simpa using (Nat.mul_le_mul_left (2 ^ n) hn).trans (hbound n le_rfl)
    have hlog := (Nat.le_log2 (Nat.ne_of_gt (hpos 0 (by omega)))).2 hp
    omega

/-- The leading coefficients in a Gauss reduction trace give at most
`log2 (a 0) + 1` strict swaps. -/
theorem gauss_strict_swap_count_le_log2 {n : ℕ} (a : ℕ → ℕ) (b : ℕ → ℤ)
    (hpos : ∀ i < n, 0 < a i)
    (hcenter : ∀ i < n, |2 * b i| ≤ (a i : ℤ))
    (hswap : ∀ i < n, a (i + 1) < a i)
    (hnext : ∀ i, i + 1 < n → ∃ k : ℤ,
      (a (i + 2) : ℤ) = (a i : ℤ) - 2 * k * b i + k ^ 2 * (a (i + 1) : ℤ)) :
    n ≤ (a 0).log2 + 1 := by
  apply strict_swap_count_le_log2 a hpos
  intro i hi
  by_contra! hhalf
  obtain ⟨k, hk⟩ := hnext i hi
  have hstop := heavy_swap_terminal
    (show (a (i + 1) : ℤ) < (a i : ℤ) by exact_mod_cast hswap i (by omega))
    (show (a i : ℤ) ≤ 2 * (a (i + 1) : ℤ) by exact_mod_cast hhalf.le)
    (hcenter i (by omega)) k
  rw [← hk] at hstop
  exact (not_le_of_gt (hswap (i + 1) hi)) (by exact_mod_cast hstop)

end Cogentic.RandomizedReductionSteps
