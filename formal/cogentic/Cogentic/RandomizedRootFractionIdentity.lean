import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Prime.Defs
import Mathlib.Data.Int.Basic
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

/-- A positive interaction in the short range cannot select the negative
root of the product-discriminant congruence. -/
theorem eq_neg_of_prime_dvd_sq_sub_sq {p K D : ℤ} (hp : Prime p)
    (hD : D < 0) (hK : 0 < K) (hsmall : K + |D| < p)
    (hdiv : p ∣ K ^ 2 - D ^ 2) : K = -D := by
  have hgap : K - D < p := by
    simpa only [abs_of_neg hD, sub_eq_add_neg] using hsmall
  have hproduct : p ∣ (K - D) * (K + D) := by
    rw [show (K - D) * (K + D) = K ^ 2 - D ^ 2 by ring]
    exact hdiv
  rcases hp.dvd_mul.mp hproduct with hminus | hplus
  · have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ K - D by omega) hgap hminus
    omega
  · have habs : |K + D| < p :=
      (abs_add_le K D).trans_lt (by rwa [abs_of_pos hK])
    have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg _) habs
      ((dvd_abs _ _).mpr hplus)
    have heq := abs_eq_zero.mp hzero
    omega

/-- In the equal-discriminant near-pair range, the reduced denominators
agree and the two fractions have equal cross products. -/
theorem near_pair_crossNumerator_zero_and_u_eq {p g u₁ u₂ b₁ b₂ c₁ c₂ D : ℤ}
    (hp : Prime p) (hD : D < 0)
    (h₁ : b₁ ^ 2 = D + 4 * p * g * u₁ * c₁)
    (h₂ : b₂ ^ 2 = D + 4 * p * g * u₂ * c₂)
    (hK : 0 < interaction p g u₁ u₂ b₁ b₂ c₁ c₂)
    (hsmall : interaction p g u₁ u₂ b₁ b₂ c₁ c₂ + |D| < p) :
    crossNumerator b₁ b₂ u₁ u₂ = 0 ∧ u₁ = u₂ := by
  have hpdiv : p ∣ 4 * p * g := ⟨4 * g, by ring⟩
  have hdiv : p ∣ interaction p g u₁ u₂ b₁ b₂ c₁ c₂ ^ 2 - D ^ 2 :=
    hpdiv.trans (by simpa only [pow_two] using four_mul_mul_dvd_interaction_sq_sub h₁ h₂)
  exact crossNumerator_zero_and_u_eq_of_interaction_eq_neg hD h₁ h₂
    (eq_neg_of_prime_dvd_sq_sub_sq hp hD hK hsmall hdiv)

theorem numerator_eq_of_crossNumerator_zero_of_u_eq {u₁ u₂ b₁ b₂ : ℤ}
    (hu : u₁ = u₂) (hu₀ : u₁ ≠ 0) (hcross : crossNumerator b₁ b₂ u₁ u₂ = 0) :
    b₁ = b₂ := by
  apply mul_right_cancel₀ hu₀
  apply sub_eq_zero.mp
  simpa only [crossNumerator, ← hu] using hcross

#print axioms crossNumerator_sq
#print axioms four_mul_mul_dvd_interaction_sq_sub
#print axioms crossNumerator_zero_and_u_eq_of_interaction_eq_neg
#print axioms eq_neg_of_prime_dvd_sq_sub_sq
#print axioms near_pair_crossNumerator_zero_and_u_eq
#print axioms numerator_eq_of_crossNumerator_zero_of_u_eq

end Cogentic.RandomizedRootFractionIdentity
