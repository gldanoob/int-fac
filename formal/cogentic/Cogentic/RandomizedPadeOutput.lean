import Cogentic.RandomizedPadeNormalize

open scoped Polynomial

namespace Cogentic.Randomized

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- Divide both Padé candidates by their Euclidean gcd, then scale both
by the inverse constant term of the reduced denominator. -/
noncomputable def padeNormalize (B R : K[X]) : K[X] × K[X] :=
  let g := EuclideanDomain.gcd B R
  let b := B/g
  let c := C (b.eval 0)⁻¹
  (c*b, c*(R/g))

/-- The quotient-and-scale operation recovers the coprime normalized
candidate, including when the raw denominator has constant term zero. -/
theorem padeNormalize_eq_of_valid {n : ℕ} {A B B₀ R R₀ : K[X]}
    (hcop : IsCoprime B₀ R₀) (hunit : B₀.eval 0 = 1) (hnz : B ≠ 0)
    (hB : B.degree ≤ n) (hB₀ : B₀.degree ≤ n)
    (hR : R.degree < n) (hR₀ : R₀.degree < n)
    (hA : X^(2*n) ∣ B*A-R) (hA₀ : X^(2*n) ∣ B₀*A-R₀) :
    padeNormalize B R = (B₀, R₀) := by
  obtain ⟨h, hh, ⟨u, hu⟩, hBfac, hRfac⟩ :=
    pade_exists_gcd_mul_of_normalized hcop hunit hnz hB hB₀ hR hR₀ hA hA₀
  let g := EuclideanDomain.gcd B R
  change g * (↑u : K[X]) = h at hu
  have hg : g ≠ 0 := by
    intro hg
    exact hh (by rw [← hu, hg, zero_mul])
  have hb : B/g = (↑u : K[X])*B₀ := by
    rw [hBfac, ← hu, mul_assoc, mul_div_cancel_left₀ _ hg]
  have hr : R/g = (↑u : K[X])*R₀ := by
    rw [hRfac, ← hu, mul_assoc, mul_div_cancel_left₀ _ hg]
  have huC : (↑u : K[X]) = C ((↑u : K[X]).eval 0) := by
    rw [← coeff_zero_eq_eval_zero]
    exact eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit u.isUnit)
  have hu0 : (↑u : K[X]).eval 0 ≠ 0 := by
    intro hzero
    apply Units.ne_zero u
    rw [huC, hzero, C_0]
  have hc : C (((↑u : K[X]).eval 0)⁻¹) * (↑u : K[X]) = 1 := by
    conv_lhs => rhs; rw [huC]
    rw [← C_mul, inv_mul_cancel₀ hu0, C_1]
  change (C ((B/g).eval 0)⁻¹ * (B/g), C ((B/g).eval 0)⁻¹ * (R/g)) = (B₀, R₀)
  rw [hb, hr, eval_mul, hunit, mul_one]
  simp only [← mul_assoc, hc, one_mul]

end Cogentic.Randomized
