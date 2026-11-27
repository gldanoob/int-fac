import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cogentic

open scoped BigOperators

/-- Integers whose affine images lie in a window of halfwidth T have bounded
cardinality, for either sign of the nonzero slope. -/
theorem randomizedAffineWindowCard {s : Finset ℤ} {a c T : ℝ}
    (ha : a ≠ 0)
    (window : ∀ x ∈ s, |a * (x : ℝ) - c| ≤ T) :
    s.card ≤ ⌊2 * T / |a|⌋₊ + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let lo := s.min' hs
    let hi := s.max' hs
    have hlo : lo ∈ s := s.min'_mem hs
    have hhi : hi ∈ s := s.max'_mem hs
    have horder : lo ≤ hi := s.min'_le_max' hs
    have spanCard : (s.card : ℤ) ≤ hi + 1 - lo := by
      have subset : s ⊆ Finset.Icc lo hi := by
        intro x hx
        exact Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
      rw [← Int.card_Icc_of_le lo hi (show lo ≤ hi + 1 by omega)]
      exact_mod_cast Finset.card_le_card subset
    have loBounds := abs_le.mp (window lo hlo)
    have hiBounds := abs_le.mp (window hi hhi)
    have hspan : ((hi : ℝ) - (lo : ℝ)) * |a| ≤ 2 * T := by
      have hdiff : 0 ≤ (hi : ℝ) - (lo : ℝ) := sub_nonneg.mpr (by exact_mod_cast horder)
      calc
        _ = |a * ((hi : ℝ) - (lo : ℝ))| := by
          rw [abs_mul, abs_of_nonneg hdiff, mul_comm]
        _ ≤ _ := by
          apply abs_le.mpr
          constructor <;> linarith only [loBounds.1, loBounds.2, hiBounds.1, hiBounds.2]
    have spanReal : (s.card : ℝ) ≤ (hi : ℝ) + 1 - (lo : ℝ) := by
      exact_mod_cast spanCard
    have cardPos : 0 < s.card := Finset.card_pos.mpr hs
    have predBound : ((s.card - 1 : ℕ) : ℝ) ≤ 2 * T / |a| := by
      rw [Nat.cast_sub cardPos, Nat.cast_one]
      apply (le_div_iff₀ (abs_pos.mpr ha)).2
      exact (mul_le_mul_of_nonneg_right (by linarith only [spanReal]) (abs_nonneg a)).trans hspan
    have hfloor := Nat.le_floor predBound
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- A finite weighted sample with maximum atom M has this much mass in the
affine window. The weights may in particular be probability masses. -/
theorem randomizedAffineWindowMass {s : Finset ℤ} {a c T M : ℝ} {weight : ℤ → ℝ}
    (ha : a ≠ 0) (hM : 0 ≤ M)
    (atom : ∀ x ∈ s, weight x ≤ M) :
    ∑ x ∈ s.filter (fun x : ℤ => |a * (x : ℝ) - c| ≤ T), weight x ≤
      ((⌊2 * T / |a|⌋₊ : ℕ) + 1 : ℝ) * M := by
  classical
  let inside := s.filter (fun x : ℤ => |a * (x : ℝ) - c| ≤ T)
  have cardBound : inside.card ≤ ⌊2 * T / |a|⌋₊ + 1 :=
    randomizedAffineWindowCard ha fun x hx => (Finset.mem_filter.mp hx).2
  calc
    _ ≤ ∑ _x ∈ inside, M := Finset.sum_le_sum fun x hx => atom x (Finset.mem_filter.mp hx).1
    _ = (inside.card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast cardBound) hM

end Cogentic
