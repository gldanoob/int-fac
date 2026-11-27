import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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

private theorem SplitLaw.fst_lt {n : ℕ} (s : SplitLaw n) {p : ℕ × ℕ}
    (hp : p ∈ s.outcomes) : p.1 < n := by
  obtain ⟨ha, hb, hab⟩ := s.proper p hp
  exact hab ▸ lt_mul_of_one_lt_right (by omega : 0 < p.1) (by omega)

private theorem SplitLaw.snd_lt {n : ℕ} (s : SplitLaw n) {p : ℕ × ℕ}
    (hp : p ∈ s.outcomes) : p.2 < n := by
  obtain ⟨ha, hb, hab⟩ := s.proper p hp
  exact hab ▸ lt_mul_of_one_lt_left (by omega : 0 < p.2) (by omega)

/-- The given real weights, viewed as a PMF on certified outcomes. -/
noncomputable def SplitLaw.toPMF {n : ℕ} (s : SplitLaw n) : PMF ↥s.outcomes :=
  PMF.ofFintype (fun p => ENNReal.ofReal (s.weight p.val)) (by
    change (∑ p ∈ s.outcomes.attach, ENNReal.ofReal (s.weight p.val)) = 1
    calc
      _ = ∑ p ∈ s.outcomes, ENNReal.ofReal (s.weight p) :=
        Finset.sum_attach s.outcomes (fun p => ENNReal.ofReal (s.weight p))
      _ = _ := by rw [← ENNReal.ofReal_sum_of_nonneg s.nonneg, s.normalized, ENNReal.ofReal_one])

@[simp] theorem SplitLaw.toPMF_apply_toReal {n : ℕ} (s : SplitLaw n) (p : ↥s.outcomes) :
    (s.toPMF p).toReal = s.weight p.val :=
  ENNReal.toReal_ofReal (s.nonneg _ p.property)

theorem SplitLaw.mem_support_toPMF_iff {n : ℕ} (s : SplitLaw n) (p : ↥s.outcomes) :
    p ∈ s.toPMF.support ↔ 0 < s.weight p.val := by
  rw [← PMF.apply_pos_iff, SplitLaw.toPMF, PMF.ofFintype_apply, ENNReal.ofReal_pos]

/-- The one-step work recurrence uses expectation under the same split law. -/
theorem SplitLaw.expectedChildCharge_eq_toPMF_sum {n : ℕ} (s : SplitLaw n) (E : ℕ → ℝ) :
    s.expectedChildCharge E =
      ∑ p : ↥s.outcomes, (s.toPMF p).toReal * (E p.val.1 + E p.val.2) := by
  simp only [SplitLaw.toPMF_apply_toReal]
  exact (Finset.sum_attach s.outcomes (fun p => s.weight p * (E p.1 + E p.2))).symm

private abbrev CertifiedPrimeList (n : ℕ) :=
  {l : List ℕ // l.prod = n ∧ ∀ p ∈ l, p.Prime}

private noncomputable def certifiedPrimeListLaw
    (split : ∀ n, 2 ≤ n → ¬n.Prime → SplitLaw n) (n : ℕ) (hn : 2 ≤ n) :
    PMF (CertifiedPrimeList n) :=
  if hp : n.Prime then
    PMF.pure ⟨[n], by simp [hp]⟩
  else
    let s := split n hn hp
    s.toPMF.bind fun p =>
      (certifiedPrimeListLaw split p.val.1 (s.proper p.val p.property).1).bind fun left =>
        (certifiedPrimeListLaw split p.val.2 (s.proper p.val p.property).2.1).map fun right =>
          ⟨left.val ++ right.val, by
            constructor
            · rw [List.prod_append, left.property.1, right.property.1]
              exact (s.proper p.val p.property).2.2
            · intro a ha
              rcases List.mem_append.mp ha with ha | ha
              · exact left.property.2 a ha
              · exact right.property.2 a ha⟩
termination_by n
decreasing_by
  all_goals first | exact s.fst_lt p.property | exact s.snd_lt p.property

/-- Recursively sample a prime list using the supplied proper-split law. -/
noncomputable def primeListLaw
    (split : ∀ n, 2 ≤ n → ¬n.Prime → SplitLaw n) (n : ℕ) (hn : 2 ≤ n) :
    PMF (List ℕ) :=
  (certifiedPrimeListLaw split n hn).map Subtype.val

theorem primeListLaw_of_prime (split : ∀ n, 2 ≤ n → ¬n.Prime → SplitLaw n)
    {n : ℕ} (hn : 2 ≤ n) (hp : n.Prime) :
    primeListLaw split n hn = PMF.pure [n] := by
  rw [primeListLaw, certifiedPrimeListLaw, dif_pos hp, PMF.pure_map]

theorem primeListLaw_of_composite (split : ∀ n, 2 ≤ n → ¬n.Prime → SplitLaw n)
    {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime) :
    let s := split n hn hp
    primeListLaw split n hn = s.toPMF.bind fun p =>
      (primeListLaw split p.val.1 (s.proper p.val p.property).1).bind fun left =>
        (primeListLaw split p.val.2 (s.proper p.val p.property).2.1).map (left ++ ·) := by
  dsimp only
  unfold primeListLaw
  conv_lhs => rw [certifiedPrimeListLaw, dif_neg hp]
  simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp]
  rfl

/-- Every supported list consists of primes and has the prescribed product. -/
theorem primeListLaw_support_correct (split : ∀ n, 2 ≤ n → ¬n.Prime → SplitLaw n)
    {n : ℕ} (hn : 2 ≤ n) {l : List ℕ} (hl : l ∈ (primeListLaw split n hn).support) :
    l.prod = n ∧ ∀ p ∈ l, p.Prime := by
  obtain ⟨l', _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hl
  exact l'.property

/-- Supported lists have the canonical prime multiplicities, up to order. -/
theorem primeListLaw_support_perm (split : ∀ n, 2 ≤ n → ¬n.Prime → SplitLaw n)
    {n : ℕ} (hn : 2 ≤ n) {l : List ℕ} (hl : l ∈ (primeListLaw split n hn).support) :
    l.Perm n.primeFactorsList :=
  (primeListLaw_support_correct split hn hl).elim Nat.primeFactorsList_unique

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
      have hal := s.fst_lt hp'
      have hbl := s.snd_lt hp'
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

#print axioms SplitLaw.expectedChildCharge_eq_toPMF_sum
#print axioms primeListLaw_of_prime
#print axioms primeListLaw_of_composite
#print axioms primeListLaw_support_correct
#print axioms primeListLaw_support_perm
#print axioms cardFactors_le_log2
#print axioms expected_work_le_cardFactors
#print axioms expected_work_le_log2

end Cogentic.RandomizedSplitWork
