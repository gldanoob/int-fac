import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

open scoped Polynomial

namespace Cogentic.Randomized

open Polynomial

variable {K : Type*} [Field K]

/-- Two Padé candidates agreeing with the same data modulo `X^(2*n)`
and with degrees below `n) in the numerator and at most `n` in the
denominator have equal cross products. -/
theorem pade_cross_mul_eq {n : ℕ} {A B B' R R' : K[X]}
    (hB : B.degree ≤ n) (hB' : B'.degree ≤ n)
    (hR : R.degree < n) (hR' : R'.degree < n)
    (hA : X^(2*n) ∣ B*A-R) (hA' : X^(2*n) ∣ B'*A-R') :
    B*R' = B'*R := by
  have hdvd : X^(2*n) ∣ B*R'-B'*R := by
    have h := dvd_sub (dvd_mul_of_dvd_right hA B') (dvd_mul_of_dvd_right hA' B)
    convert h using 1
    ring
  have hmul {b r : K[X]} (hb : b.degree ≤ n) (hr : r.degree < n) :
      (b*r).degree < ((2*n : ℕ) : WithBot ℕ) := by
    calc
      (b*r).degree ≤ (n : WithBot ℕ) + r.degree := degree_mul_le_of_le hb le_rfl
      _ < (n : WithBot ℕ) + n := WithBot.add_lt_add_left WithBot.coe_ne_bot hr
      _ = ((2*n : ℕ) : WithBot ℕ) := by simp [two_mul]
  apply sub_eq_zero.mp
  apply eq_zero_of_dvd_of_degree_lt hdvd
  rw [degree_X_pow]
  exact (degree_sub_le _ _).trans_lt (max_lt (hmul hB hR') (hmul hB' hR))

/-- Coprime Padé candidates with denominators normalized to one at zero
are uniquely determined by their cross product. -/
theorem pade_normalized_unique_of_cross_mul {B B' R R' : K[X]}
    (hcop : IsCoprime B R) (hcop' : IsCoprime B' R')
    (hB : B.eval 0 = 1) (hB' : B'.eval 0 = 1)
    (hcross : B*R' = B'*R) : B = B' ∧ R = R' := by
  have hdvd : B ∣ B' := hcop.dvd_of_dvd_mul_right ⟨R', hcross.symm⟩
  have hdvd' : B' ∣ B := hcop'.dvd_of_dvd_mul_right ⟨R, hcross⟩
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hdvd hdvd'
  have hu0 : eval 0 (↑u : K[X]) = 1 := by
    have h := congrArg (eval 0) hu
    simpa [eval_mul, hB, hB'] using h
  have huone : (↑u : K[X]) = 1 := by
    rw [eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit u.isUnit),
      coeff_zero_eq_eval_zero, hu0, C_1]
  have heq : B = B' := by simpa [huone] using hu
  have hnz : B ≠ 0 := by
    intro h
    simp [h] at hB
  exact ⟨heq, (mul_left_cancel₀ hnz (heq ▸ hcross)).symm⟩

end Cogentic.Randomized
