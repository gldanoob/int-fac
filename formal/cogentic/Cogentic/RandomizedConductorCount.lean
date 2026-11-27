import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedConductorCount

/-- In a saturated prefix only the valuation digits remain. -/
theorem saturated_prefix {h v b T : ℕ} (hb : 0 < b) (hv : b ^ v ≤ T) :
    b ^ (h - h + min v h) ≤ T := by
  simpa using (Nat.pow_le_pow_right hb (min_le_left v h)).trans hv

/-- Failure of the separation inequality at the next prefix length bounds
the number of free digits, including the case where no prefix was certified. -/
theorem unsaturated_prefix {h k v b L T : ℕ} (hb : 0 < b) (hk : k ≤ h)
    (hnext : L * b ^ v ≤ 2 * T ^ 2 * b ^ (k + 1)) :
    L * b ^ (h - k + min v k) ≤ 2 * T ^ 2 * b ^ (h + 1) := by
  calc
    L * b ^ (h - k + min v k) = (L * b ^ min v k) * b ^ (h - k) := by
      rw [pow_add]
      ring
    _ ≤ (L * b ^ v) * b ^ (h - k) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (min_le_left v k)))
    _ ≤ (2 * T ^ 2 * b ^ (k + 1)) * b ^ (h - k) := Nat.mul_le_mul_right _ hnext
    _ = 2 * T ^ 2 * b ^ (h + 1) := by
      rw [Nat.mul_assoc, ← pow_add, show k + 1 + (h - k) = h + 1 by omega]

end Cogentic.RandomizedConductorCount
