import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedRootFractionIdentity

variable {R : Type*} [CommRing R]

def crossNumerator (b₁ b₂ u₁ u₂ : R) : R := b₁ * u₂ - b₂ * u₁

def interaction (p g u₁ u₂ b₁ b₂ c₁ c₂ : R) : R :=
  2 * p * g * (c₁ * u₂ + c₂ * u₁) - b₁ * b₂

theorem crossNumerator_mul_g {g n₁ n₂ u₁ u₂ b₁ b₂ : R}
    (hn₁ : n₁ = g * u₁) (hn₂ : n₂ = g * u₂) :
    b₁ * n₂ - b₂ * n₁ = g * crossNumerator b₁ b₂ u₁ u₂ := by
  rw [hn₁, hn₂]
  unfold crossNumerator
  ring

theorem crossNumerator_sq {p g u₁ u₂ b₁ b₂ c₁ c₂ D₁ D₂ : R}
    (h₁ : b₁ ^ 2 = D₁ + 4 * p * g * u₁ * c₁)
    (h₂ : b₂ ^ 2 = D₂ + 4 * p * g * u₂ * c₂) :
    crossNumerator b₁ b₂ u₁ u₂ ^ 2 =
      D₁ * u₂ ^ 2 + D₂ * u₁ ^ 2 + 2 * u₁ * u₂ * interaction p g u₁ u₂ b₁ b₂ c₁ c₂ := by
  calc
    _ = b₁ ^ 2 * u₂ ^ 2 + b₂ ^ 2 * u₁ ^ 2 - 2 * u₁ * u₂ * b₁ * b₂ := by
      unfold crossNumerator
      ring
    _ = _ := by rw [h₁, h₂]; unfold interaction; ring

/-- The product-discriminant congruence with an explicit divisibility witness. -/
theorem four_mul_mul_dvd_interaction_sq_sub {p g u₁ u₂ b₁ b₂ c₁ c₂ D₁ D₂ : R}
    (h₁ : b₁ ^ 2 = D₁ + 4 * p * g * u₁ * c₁)
    (h₂ : b₂ ^ 2 = D₂ + 4 * p * g * u₂ * c₂) :
    4 * p * g ∣ interaction p g u₁ u₂ b₁ b₂ c₁ c₂ ^ 2 - D₁ * D₂ := by
  let S := c₁ * u₂ + c₂ * u₁
  refine ⟨p * g * S ^ 2 - S * b₁ * b₂ + u₁ * c₁ * b₂ ^ 2 + u₂ * c₂ * D₁, ?_⟩
  calc
    _ = 4 * p * g * (p * g * S ^ 2 - S * b₁ * b₂) +
          (b₁ ^ 2 - D₁) * b₂ ^ 2 + D₁ * (b₂ ^ 2 - D₂) := by
      unfold interaction S
      ring
    _ = _ := by rw [h₁, h₂]; ring

/-- At the boundary K = −D with equal negative discriminants, both the
cross numerator and the denominator difference vanish. -/
theorem crossNumerator_zero_and_u_eq_of_interaction_eq_neg
    {p g u₁ u₂ b₁ b₂ c₁ c₂ D : ℤ} (hD : D < 0)
    (h₁ : b₁ ^ 2 = D + 4 * p * g * u₁ * c₁)
    (h₂ : b₂ ^ 2 = D + 4 * p * g * u₂ * c₂)
    (hK : interaction p g u₁ u₂ b₁ b₂ c₁ c₂ = -D) :
    crossNumerator b₁ b₂ u₁ u₂ = 0 ∧ u₁ = u₂ := by
  have hsquare : crossNumerator b₁ b₂ u₁ u₂ ^ 2 = D * (u₁ - u₂) ^ 2 := by
    rw [crossNumerator_sq h₁ h₂, hK]
    ring
  have hu : u₁ = u₂ := by
    by_contra hne
    have hneg := mul_neg_of_neg_of_pos hD (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    rw [← hsquare] at hneg
    exact (not_lt_of_ge (sq_nonneg _)) hneg
  have ht : crossNumerator b₁ b₂ u₁ u₂ ^ 2 = 0 := by
    simpa only [hu, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hsquare
  exact ⟨sq_eq_zero_iff.mp ht, hu⟩

#print axioms crossNumerator_sq
#print axioms four_mul_mul_dvd_interaction_sq_sub
#print axioms crossNumerator_zero_and_u_eq_of_interaction_eq_neg

end Cogentic.RandomizedRootFractionIdentity
