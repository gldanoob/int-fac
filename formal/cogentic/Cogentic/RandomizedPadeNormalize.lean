import Cogentic.RandomizedPadeUniqueness
import Mathlib.RingTheory.PrincipalIdealDomain

open scoped Polynomial

namespace Cogentic.Randomized

open Polynomial

variable {K : Type*} [Field K]

/-- Every valid nonzero candidate is a single polynomial multiple of a
coprime normalized candidate. -/
theorem pade_exists_mul_of_normalized {n : ℕ} {A B B₀ R R₀ : K[X]}
    (hcop : IsCoprime B₀ R₀) (hunit : B₀.eval 0 = 1) (hnz : B ≠ 0)
    (hB : B.degree ≤ n) (hB₀ : B₀.degree ≤ n)
    (hR : R.degree < n) (hR₀ : R₀.degree < n)
    (hA : X^(2*n) ∣ B*A-R) (hA₀ : X^(2*n) ∣ B₀*A-R₀) :
    ∃ h : K[X], h ≠ 0 ∧ B = h*B₀ ∧ R = h*R₀ := by
  have hcross := pade_cross_mul_eq hB hB₀ hR hR₀ hA hA₀
  have hb₀ : B₀ ≠ 0 := by
    intro h
    simp [h] at hunit
  obtain ⟨h, hh⟩ := hcop.dvd_of_dvd_mul_right (show B₀ ∣ B*R₀ from ⟨R, hcross⟩)
  refine ⟨h, ?_, hh.trans (mul_comm _ _), ?_⟩
  · intro hz
    exact hnz (by simp [hh, hz])
  · apply mul_left_cancel₀ hb₀
    calc
      B₀*R = B*R₀ := hcross.symm
      _ = B₀*(h*R₀) := by rw [hh, mul_assoc]

/-- The multiple relating a raw Padé candidate to the normalized pair is
associated to the raw pair's gcd, even if the raw denominator vanishes at zero. -/
theorem pade_exists_gcd_mul_of_normalized [DecidableEq K] {n : ℕ} {A B B₀ R R₀ : K[X]}
    (hcop : IsCoprime B₀ R₀) (hunit : B₀.eval 0 = 1) (hnz : B ≠ 0)
    (hB : B.degree ≤ n) (hB₀ : B₀.degree ≤ n)
    (hR : R.degree < n) (hR₀ : R₀.degree < n)
    (hA : X^(2*n) ∣ B*A-R) (hA₀ : X^(2*n) ∣ B₀*A-R₀) :
    ∃ h : K[X], h ≠ 0 ∧ Associated (EuclideanDomain.gcd B R) h ∧
      B = h*B₀ ∧ R = h*R₀ := by
  obtain ⟨h, hh, hb, hr⟩ := pade_exists_mul_of_normalized hcop hunit hnz hB hB₀ hR hR₀ hA hA₀
  refine ⟨h, hh, associated_of_dvd_dvd ?_ ?_, hb, hr⟩
  · obtain ⟨s, t, hst⟩ := hcop
    have hdvd := dvd_add (dvd_mul_of_dvd_right (EuclideanDomain.gcd_dvd_left B R) s)
      (dvd_mul_of_dvd_right (EuclideanDomain.gcd_dvd_right B R) t)
    have heq : s*B+t*R = h := by
      calc
        s*B+t*R = h*(s*B₀+t*R₀) := by rw [hb, hr]; ring
        _ = h := by rw [hst, mul_one]
    exact heq ▸ hdvd
  · exact EuclideanDomain.dvd_gcd ⟨B₀, hb⟩ ⟨R₀, hr⟩

/-- A polynomial whose constant term is nonzero can be canceled from a
divisibility condition modulo any power of `X`. -/
theorem pade_dvd_cancel_of_eval_ne_zero {g f : K[X]} {N : ℕ}
    (hg : g.eval 0 ≠ 0) (hdvd : X^N ∣ g*f) : X^N ∣ f := by
  classical
  have hnot : ¬ (X : K[X]) ∣ g := by
    rintro ⟨p, rfl⟩
    simp [eval_mul] at hg
  have hcop : IsCoprime (X : K[X]) g := (prime_X (R := K)).coprime_iff_not_dvd.mpr hnot
  exact hcop.pow_left.dvd_of_dvd_mul_left hdvd

/-- Removing a common gcd and scaling both quotients to denominator
constant one preserves the degree bounds and the truncated congruence. -/
theorem pade_exists_normalized [DecidableEq K] {n : ℕ} {A B R : K[X]}
    (hunit : B.eval 0 ≠ 0) (hB : B.degree ≤ n) (hR : R.degree < n)
    (hA : X^(2*n) ∣ B*A-R) :
    ∃ h B₀ R₀ : K[X], Associated (EuclideanDomain.gcd B R) h ∧
      B = h*B₀ ∧ R = h*R₀ ∧ IsCoprime B₀ R₀ ∧ B₀.eval 0 = 1 ∧
      B₀.degree ≤ n ∧ R₀.degree < n ∧ X^(2*n) ∣ B₀*A-R₀ := by
  let g := EuclideanDomain.gcd B R
  obtain ⟨b, hb⟩ : g ∣ B := EuclideanDomain.gcd_dvd_left B R
  obtain ⟨r, hr⟩ : g ∣ R := EuclideanDomain.gcd_dvd_right B R
  have hu : g.eval 0 * b.eval 0 ≠ 0 := by simpa [hb, eval_mul] using hunit
  have hg : g.eval 0 ≠ 0 := (mul_ne_zero_iff.mp hu).1
  have hb0 : b.eval 0 ≠ 0 := (mul_ne_zero_iff.mp hu).2
  let c := C (b.eval 0)
  let ci := C (b.eval 0)⁻¹
  have hc : c * ci = 1 := by simp [c, ci, ← C_mul, hb0]
  have hcunit : IsUnit c := (isUnit_iff_ne_zero.mpr hb0).map C
  obtain ⟨u, huc⟩ := hcunit
  let h := g*c
  let B₀ := ci*b
  let R₀ := ci*r
  have hassoc : Associated g h := ⟨u, by rw [huc]⟩
  have hheval : h.eval 0 ≠ 0 := by simpa [h, c, eval_mul] using hu
  have hhnz : h ≠ 0 := by
    intro heq
    exact hheval (by simp [heq])
  have hBn : B = h*B₀ := by
    rw [hb]
    change g*b = (g*c)*(ci*b)
    rw [mul_assoc g, ← mul_assoc c, hc, one_mul]
  have hRn : R = h*R₀ := by
    rw [hr]
    change g*r = (g*c)*(ci*r)
    rw [mul_assoc g, ← mul_assoc c, hc, one_mul]
  refine ⟨h, B₀, R₀, hassoc, hBn, hRn, ?_, ?_, ?_, ?_, ?_⟩
  · let s := EuclideanDomain.gcdA B R
    let t := EuclideanDomain.gcdB B R
    have hbez : g = B*s + R*t := EuclideanDomain.gcd_eq_gcd_ab B R
    refine ⟨c*s, c*t, mul_left_cancel₀ (a := g) ?_ ?_⟩
    · intro heq
      exact hg (by simp [heq])
    · calc
        g * (c*s*B₀+c*t*R₀) = (h*B₀)*s+(h*R₀)*t := by dsimp [h]; ring
        _ = B*s+R*t := by rw [← hBn, ← hRn]
        _ = g*1 := by rw [← hbez, mul_one]
  · simp [B₀, ci, eval_mul, hb0]
  · apply le_trans _ hB
    rw [hBn, mul_comm]
    exact degree_le_mul_left _ hhnz
  · apply lt_of_le_of_lt _ hR
    rw [hRn, mul_comm]
    exact degree_le_mul_left _ hhnz
  · apply pade_dvd_cancel_of_eval_ne_zero hheval
    convert hA using 1
    rw [hBn, hRn]
    ring

end Cogentic.Randomized
