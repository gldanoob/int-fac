import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedSplitWork

open scoped ArithmeticFunction.Omega BigOperators

/-- A finite probability distribution on ordered proper decompositions of `n`. -/
structure SplitLaw (n : ℕ) where
  outcomes : Finset (ℕ × ℕ)
  weight : ℕ × ℕ → ℝ
  nonneg : ∀ p ∈ outcomes, 0 ≤ weight p
  normalized : ∑ p ∈ outcomes, weight p = 1
  proper : ∀ p ∈ outcomes, 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 * p.2 = n

noncomputable def SplitLaw.expectedChildCharge {n : ℕ} (s : SplitLaw n) (E : ℕ → ℝ) : ℝ :=
  ∑ p ∈ s.outcomes, s.weight p * (E p.1 + E p.2)

/-- The count of prime factors with multiplicity is at most the binary logarithm. -/
theorem cardFactors_le_log2 (n : ℕ) : Ω n ≤ n.log2 := by
  by_cases hn : n = 0
  · simp [hn]
  apply (Nat.le_log2 hn).2
  rw [ArithmeticFunction.cardFactors_apply]
  exact (List.pow_card_le_prod n.primeFactorsList 2 fun _ hp =>
    (Nat.prime_of_mem_primeFactorsList hp).two_le).trans_eq (Nat.prod_primeFactorsList hn)

section ExpectedCharge

variable (E T : ℕ → ℝ)
variable (split : ∀ n, 2 ≤ n → ¬n.Prime → SplitLaw n)
variable (hE : ∀ n, 0 ≤ E n) (hT : Monotone T)
variable (hprime : ∀ n, n.Prime → E n ≤ T n)
variable (hrec : ∀ n (hn : 2 ≤ n) (hp : ¬n.Prime),
  E n ≤ T n + (split n hn hp).expectedChildCharge E)

include hT hprime hrec in
/-- A one-step conditional expected-work inequality lifts to the full
binary decomposition with at most twice the prime-factor count minus one
charged calls. The caller supplies the split law and the recurrence. -/
theorem expected_work_le_cardFactors :
    ∀ n, 2 ≤ n → E n ≤ (2 * (Ω n : ℝ) - 1) * T n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hp : n.Prime
    · have h : (2 : ℝ) - 1 = 1 := by norm_num
      simpa [ArithmeticFunction.cardFactors_apply_prime hp, h] using hprime n hp
    let s := split n hn hp
    let childBudget := (2 * (Ω n : ℝ) - 2) * T n
    have hpoint (p : ℕ × ℕ) (hp' : p ∈ s.outcomes) :
        E p.1 + E p.2 ≤ childBudget := by
      obtain ⟨ha, hb, hab⟩ := s.proper p hp'
      have hal : p.1 < n :=
        hab ▸ lt_mul_of_one_lt_right (by omega : 0 < p.1) (by omega)
      have hbl : p.2 < n :=
        hab ▸ lt_mul_of_one_lt_left (by omega : 0 < p.2) (by omega)
      have haΩ : (1 : ℝ) ≤ Ω p.1 := by
        exact_mod_cast (ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega : 1 < p.1))
      have hbΩ : (1 : ℝ) ≤ Ω p.2 := by
        exact_mod_cast (ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega : 1 < p.2))
      have hΩ : Ω n = Ω p.1 + Ω p.2 :=
        hab ▸ ArithmeticFunction.cardFactors_mul (by omega : p.1 ≠ 0) (by omega : p.2 ≠ 0)
      calc
        _ ≤ (2 * (Ω p.1 : ℝ) - 1) * T p.1 + (2 * (Ω p.2 : ℝ) - 1) * T p.2 :=
          add_le_add (ih p.1 hal ha) (ih p.2 hbl hb)
        _ ≤ (2 * (Ω p.1 : ℝ) - 1) * T n + (2 * (Ω p.2 : ℝ) - 1) * T n :=
          add_le_add (mul_le_mul_of_nonneg_left (hT hal.le) (by linarith only [haΩ]))
            (mul_le_mul_of_nonneg_left (hT hbl.le) (by linarith only [hbΩ]))
        _ = _ := by simp only [childBudget, hΩ, Nat.cast_add]; ring
    have hchild : s.expectedChildCharge E ≤ childBudget := calc
      _ ≤ ∑ p ∈ s.outcomes, s.weight p * childBudget :=
        Finset.sum_le_sum fun p hp' => mul_le_mul_of_nonneg_left (hpoint p hp') (s.nonneg p hp')
      _ = _ := by rw [← Finset.sum_mul, s.normalized, one_mul]
    have h := (hrec n hn hp).trans (add_le_add le_rfl hchild)
    dsimp only [childBudget] at h
    nlinarith only [h]

include hE hT hprime hrec in
theorem expected_work_le_log2 (n : ℕ) (hn : 2 ≤ n) :
    E n ≤ (2 * (n.log2 : ℝ) - 1) * T n := by
  have hT₀ := (hE 2).trans ((hprime 2 Nat.prime_two).trans (hT hn))
  have hΩ : (Ω n : ℝ) ≤ n.log2 := by exact_mod_cast cardFactors_le_log2 n
  exact (expected_work_le_cardFactors E T split hT hprime hrec n hn).trans
    (mul_le_mul_of_nonneg_right (by linarith only [hΩ]) hT₀)

end ExpectedCharge

#print axioms cardFactors_le_log2
#print axioms expected_work_le_cardFactors
#print axioms expected_work_le_log2

end Cogentic.RandomizedSplitWork
