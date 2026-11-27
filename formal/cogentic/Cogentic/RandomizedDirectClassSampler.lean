import Cogentic.RandomizedFactoredProposal
import Cogentic.RandomizedDeficientWeights
import Cogentic.RandomizedFiniteSupportTV
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedDirectClassSampler

open Finset
open scoped BigOperators ArithmeticFunction.omega
open Cogentic.RandomizedFactoredProposal
open Cogentic.RandomizedSamplerTransfer
open Cogentic.RandomizedFiniteSupportTV

/-!
# Direct Reduced-Class Sampler, Sequential Retry Invariance, and Missing-Class TV Bound

This module formalizes the equal-weight direct reduced-class sampler of
`research/keybreak-direct-reduced-class-sampler.md`:

1. Elementary harmonic, squarefree-divisor, and prime-product bounds.
2. Concrete modular square-root counts `modNegSqRootCount m A = #{b mod A : b^2 = -m}`,
   including CRT multiplicativity, coprime upper bounds `≤ 2^(ω(A)+1)`, and local prime-power
   series bounds `S_p ≤ 4 / (p - 1)`.
3. Step 1 (`dyadicProposalPMF`): dyadic factored integer sampling giving exact mass
   `2^(ω(A)) / (2 * 2^J * (J + 1))` to every `A ∈ [1, U]`.
4. Steps 2–3 (`directProposalOutcomePMF` and `directProposalPMF`): gcd exit / rejection and
   modular-root acceptance yielding exact unconditional mass `1 / (4 * 2^J * (J + 1))` on
   every coprime canonical primitive reduced form.
5. Sequential retry invariance (`retryOutcomePMF`, `retryOptionPMF`): repeating independent
   attempts up to any cap `J₀ ≥ 1` gives every coprime form identical probability
   `(1 / (4 * 2^J * (J + 1))) * ∑_{k < J₀} r^k`, so conditioning on returning a form is
   exactly uniform on the coprime canonical reduced forms.
6. Total variation distance and missing-count bounds, including `∏_{q | N} (1 + 4/(q-1)) ≤ (log(2N))^80`.
7. One-attempt gcd exit probability bound `≤ ∑_{p | N} 1 / p`.
-/

section AnalyticBounds

/-- Elementary harmonic sum bound `∑_{d=1}^X 1/d ≤ 1 + log X` for `X ≥ 1`. -/
theorem harmonic_le_one_add_log {X : ℕ} (hX : 1 ≤ X) :
    (∑ d ∈ Finset.Icc 1 X, (1 : ℝ) / (d : ℝ)) ≤ 1 + Real.log (X : ℝ) := by
  induction X with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp
    | succ m =>
      have hm1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
      have hih := ih hm1
      have hsplit : Finset.Icc 1 (m + 2) = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : m + 2 ∉ Finset.Icc 1 (m + 1) := by simp
      rw [hsplit, Finset.sum_insert hnotmem]
      have hmpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have hm2pos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
      have hratio : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) :=
        div_pos hmpos hm2pos
      have hlog : Real.log (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤
          ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hratio
      rw [Real.log_div hmpos.ne' hm2pos.ne'] at hlog
      have hstep : (1 : ℝ) / ((m + 2 : ℕ) : ℝ) ≤
          Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
        have hsub : ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 =
            -((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
          push_cast
          field_simp
          ring
        linarith
      linarith

/-- Squarefree-divisor weighting bound `∑_{m=1}^X 2^{ω(m)} ≤ X (1 + log X)` for `X ≥ 1`. -/
theorem sum_two_pow_omega_le {X : ℕ} (hX : 1 ≤ X) :
    (∑ m ∈ Finset.Icc 1 X, (2 : ℝ) ^ m.primeFactors.card) ≤
      (X : ℝ) * (1 + Real.log (X : ℝ)) := by
  have hnat : (∑ m ∈ Finset.Icc 1 X, 2 ^ m.primeFactors.card) ≤
      ∑ d ∈ Finset.Icc 1 X, X / d := by
    have hstep1 : (∑ m ∈ Finset.Icc 1 X, 2 ^ m.primeFactors.card) ≤
        ∑ m ∈ Finset.Icc 1 X, m.divisors.card := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 : m ≠ 0 := by
        have := (Finset.mem_Icc.mp hm).1
        omega
      have hcard := squarefree_divisor_count hm0
      rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
        Nat.toFinset_factors] at hcard
      rw [← hcard]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    refine hstep1.trans ?_
    have hswap : (∑ m ∈ Finset.Icc 1 X, m.divisors.card) =
        ∑ d ∈ Finset.Icc 1 X, ((Finset.Icc 1 X).filter (fun m => d ∣ m)).card := by
      have h1 : (∑ m ∈ Finset.Icc 1 X, m.divisors.card) =
          ∑ m ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X, if d ∣ m then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hmX : m ≤ X := (Finset.mem_Icc.mp hm).2
        have hsub : m.divisors = (Finset.Icc 1 X).filter (fun d => d ∣ m) := by
          ext d
          simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨hd, hm0⟩
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
            have hdle : d ≤ m := Nat.le_of_dvd (by omega) hd
            exact ⟨⟨hdpos, hdle.trans hmX⟩, hd⟩
          · rintro ⟨_, hd⟩
            exact ⟨hd, by omega⟩
        rw [hsub, Finset.card_filter]
      rw [h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.card_filter]
    rw [hswap]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hbij : ((Finset.Icc 1 X).filter (fun m => d ∣ m)).card ≤ (Finset.Icc 1 (X / d)).card := by
      refine Finset.card_le_card_of_injOn (fun m => m / d) ?_ ?_
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
        obtain ⟨⟨hm1, hmX⟩, hdm⟩ := hm
        have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdm
        exact ⟨Nat.div_pos hdle (by omega), Nat.div_le_div_right hmX⟩
      · intro m₁ hm₁ m₂ hm₂ hEq
        simp only [Finset.mem_coe, Finset.mem_filter] at hm₁ hm₂
        have h1 := Nat.mul_div_cancel' hm₁.2
        have h2 := Nat.mul_div_cancel' hm₂.2
        rw [← h1, ← h2]
        exact congrArg (d * ·) hEq
    simpa [Nat.card_Icc] using hbij
  have hreal : (∑ m ∈ Finset.Icc 1 X, (2 : ℝ) ^ m.primeFactors.card) ≤
      ∑ d ∈ Finset.Icc 1 X, ((X / d : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (∑ m ∈ Finset.Icc 1 X, (2 : ℝ) ^ m.primeFactors.card)
      ≤ ∑ d ∈ Finset.Icc 1 X, ((X / d : ℕ) : ℝ) := hreal
    _ ≤ ∑ d ∈ Finset.Icc 1 X, (X : ℝ) / (d : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdpos : (0 : ℝ) < (d : ℝ) := by
          have := (Finset.mem_Icc.mp hd).1
          positivity
        rw [le_div_iff₀ hdpos]
        exact_mod_cast Nat.div_mul_le_self X d
    _ = (X : ℝ) * ∑ d ∈ Finset.Icc 1 X, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
    _ ≤ (X : ℝ) * (1 + Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log hX) (Nat.cast_nonneg X)

/-- For `N ≥ 2`, `1 < log (2 * N)`. -/
theorem one_lt_log_two_mul {N : ℕ} (hN : 2 ≤ N) :
    1 < Real.log (2 * (N : ℝ)) := by
  have hexp : Real.exp 1 < 2 * (N : ℝ) := by
    have h4 : (4 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    linarith [Real.exp_one_lt_d9]
  have := Real.log_lt_log (Real.exp_pos 1) hexp
  rwa [Real.log_exp] at this

/-- For `N ≥ 2`, `1 / 4 < log (log (2 * N))`. -/
theorem quarter_lt_log_log_two_mul {N : ℕ} (hN : 2 ≤ N) :
    (1 : ℝ) / 4 < Real.log (Real.log (2 * (N : ℝ))) := by
  have hL4 : Real.log 4 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_le_log (by norm_num)
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog4 : (1.38 : ℝ) < Real.log 4 := by
    have h4eq : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [h4eq, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9]
  have hexpq : Real.exp ((1 : ℝ) / 4) < 1.38 := by
    have hpow : (Real.exp ((1 : ℝ) / 4)) ^ (4 : ℕ) < (1.38 : ℝ) ^ (4 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
      linarith [Real.exp_one_lt_d9]
    exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) hpow
  have hexpL : Real.exp ((1 : ℝ) / 4) < Real.log (2 * (N : ℝ)) :=
    hexpq.trans (hlog4.trans_le hL4)
  have := Real.log_lt_log (Real.exp_pos _) hexpL
  rwa [Real.log_exp] at this

/-- The number of distinct prime factors of `N ≥ 1` is at most `log N / log 2`. -/
theorem primeFactors_card_le_log_div_log_two {N : ℕ} (hN : 1 ≤ N) :
    (N.primeFactors.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
  have hpow : 2 ^ N.primeFactors.card ≤ N := by
    calc
      2 ^ N.primeFactors.card
        = ∏ _p ∈ N.primeFactors, (2 : ℕ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ N.primeFactors, p := by
          apply Finset.prod_le_prod'
          intro p hp
          exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ ∏ p ∈ N.primeFactors, p ^ (N.factorization p) := by
          apply Finset.prod_le_prod'
          intro p hp
          have hpos : 1 ≤ N.factorization p := by
            have hmem : p ∈ N.factorization.support := by
              simpa [Nat.support_factorization] using hp
            exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
          exact Nat.le_self_pow (by omega) p
      _ = N := by
          have h0 : N ≠ 0 := by omega
          simpa [Finsupp.prod, Nat.support_factorization] using
            Nat.factorization_prod_pow_eq_self h0
  have hpowR : (2 : ℝ) ^ N.primeFactors.card ≤ (N : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).2 hlog

/-- Reciprocal sum over prime factors of `N ≥ 2`: splitting at `⌈log (2N)⌉`. -/
theorem primeFactors_recip_sum_le {N : ℕ} (hN : 2 ≤ N) :
    (∑ q ∈ N.primeFactors, (1 : ℝ) / (q : ℝ)) ≤
      Real.log (Real.log (2 * (N : ℝ))) + Real.log 2 + 1 / Real.log 2 := by
  set L : ℝ := Real.log (2 * (N : ℝ))
  have hL1 : 1 < L := one_lt_log_two_mul hN
  have hLpos : 0 < L := zero_lt_one.trans hL1
  set M : ℕ := Nat.ceil L
  have hML : L ≤ (M : ℝ) := Nat.le_ceil L
  have hMlt : (M : ℝ) < L + 1 := Nat.ceil_lt_add_one hLpos.le
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < (M : ℝ) := hL1.trans_le hML
    exact_mod_cast this.le
  let small := N.primeFactors.filter (fun q => q ≤ M)
  let large := N.primeFactors.filter (fun q => ¬ q ≤ M)
  have hsplit : (∑ q ∈ N.primeFactors, (1 : ℝ) / (q : ℝ)) =
      (∑ q ∈ small, (1 : ℝ) / (q : ℝ)) + (∑ q ∈ large, (1 : ℝ) / (q : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (fun q => q ≤ M)]
  rw [hsplit]
  have hsmall : (∑ q ∈ small, (1 : ℝ) / (q : ℝ)) ≤ Real.log L + Real.log 2 := by
    have hsub : small ⊆ Finset.Icc 2 M := by
      intro q hq
      simp only [small, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      exact ⟨(Nat.prime_of_mem_primeFactors hq.1).two_le, hq.2⟩
    have hIcc : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot1 : 1 ∉ Finset.Icc 2 M := by simp
    have hharm := harmonic_le_one_add_log hM1
    rw [hIcc, Finset.sum_insert hnot1] at hharm
    have hIcc2 : (∑ d ∈ Finset.Icc 2 M, (1 : ℝ) / (d : ℝ)) ≤ Real.log (M : ℝ) := by
      norm_num at hharm
      simp only [one_div]
      linarith
    have hM2L : (M : ℝ) ≤ 2 * L := by linarith
    have hlogM : Real.log (M : ℝ) ≤ Real.log L + Real.log 2 := by
      have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
      calc
        Real.log (M : ℝ) ≤ Real.log (2 * L) := Real.log_le_log hMpos hM2L
        _ = Real.log 2 + Real.log L := Real.log_mul (by norm_num) hLpos.ne'
        _ = Real.log L + Real.log 2 := add_comm _ _
    calc
      (∑ q ∈ small, (1 : ℝ) / (q : ℝ))
        ≤ ∑ d ∈ Finset.Icc 2 M, (1 : ℝ) / (d : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ Real.log (M : ℝ) := hIcc2
      _ ≤ Real.log L + Real.log 2 := hlogM
  have hlarge : (∑ q ∈ large, (1 : ℝ) / (q : ℝ)) ≤ 1 / Real.log 2 := by
    have hterm : ∀ q ∈ large, (1 : ℝ) / (q : ℝ) ≤ 1 / L := by
      intro q hq
      have hqgt : M < q := Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2
      have hqL : L < (q : ℝ) := hML.trans_lt (by exact_mod_cast hqgt)
      exact one_div_le_one_div_of_le hLpos hqL.le
    have hcard : (large.card : ℝ) ≤ (N.primeFactors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hN1 : 1 ≤ N := by omega
    have hlogN : Real.log (N : ℝ) ≤ L := by
      apply Real.log_le_log (by positivity)
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have homega : (N.primeFactors.card : ℝ) ≤ L / Real.log 2 :=
      (primeFactors_card_le_log_div_log_two hN1).trans
        (div_le_div_of_nonneg_right hlogN (Real.log_pos (by norm_num)).le)
    calc
      (∑ q ∈ large, (1 : ℝ) / (q : ℝ))
        ≤ ∑ _q ∈ large, (1 / L) := Finset.sum_le_sum hterm
      _ = (large.card : ℝ) * (1 / L) := by simp [nsmul_eq_mul]
      _ ≤ (L / Real.log 2) * (1 / L) :=
          mul_le_mul_of_nonneg_right (hcard.trans homega) (by positivity)
      _ = 1 / Real.log 2 := by
          field_simp [hLpos.ne']
  linarith

/-- Product bound `∏_{q | N} (1 + 4/(q-1)) ≤ exp(18) * (log(2N))^8` for `N ≥ 2`. -/
theorem primeFactors_local_prod_le_exp_mul_log_pow {N : ℕ} (hN : 2 ≤ N) :
    (∏ q ∈ N.primeFactors, (1 + 4 / ((q : ℝ) - 1))) ≤
      Real.exp 18 * (Real.log (2 * (N : ℝ))) ^ (8 : ℕ) := by
  set L : ℝ := Real.log (2 * (N : ℝ))
  have hLpos : 0 < L := zero_lt_one.trans (one_lt_log_two_mul hN)
  have hfactor : ∀ q ∈ N.primeFactors,
      (1 : ℝ) + 4 / ((q : ℝ) - 1) ≤ Real.exp (8 * ((1 : ℝ) / (q : ℝ))) := by
    intro q hq
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le
    have hq1pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
    have h48 : 4 / ((q : ℝ) - 1) ≤ 8 * ((1 : ℝ) / (q : ℝ)) := by
      rw [mul_one_div, div_le_div_iff₀ hq1pos hqpos]
      linarith
    calc
      1 + 4 / ((q : ℝ) - 1)
        ≤ 1 + 8 * ((1 : ℝ) / (q : ℝ)) := by linarith
      _ ≤ Real.exp (8 * ((1 : ℝ) / (q : ℝ))) := by
          linarith [Real.add_one_le_exp (8 * ((1 : ℝ) / (q : ℝ)))]
  have hnonneg : ∀ q ∈ N.primeFactors, (0 : ℝ) ≤ 1 + 4 / ((q : ℝ) - 1) := by
    intro q hq
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le
    have : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    positivity
  have hprod : (∏ q ∈ N.primeFactors, (1 + 4 / ((q : ℝ) - 1))) ≤
      Real.exp (8 * ∑ q ∈ N.primeFactors, (1 : ℝ) / (q : ℝ)) := by
    calc
      (∏ q ∈ N.primeFactors, (1 + 4 / ((q : ℝ) - 1)))
        ≤ ∏ q ∈ N.primeFactors, Real.exp (8 * ((1 : ℝ) / (q : ℝ))) :=
          Finset.prod_le_prod hnonneg hfactor
      _ = Real.exp (∑ q ∈ N.primeFactors, 8 * ((1 : ℝ) / (q : ℝ))) :=
          (Real.exp_sum N.primeFactors _).symm
      _ = Real.exp (8 * ∑ q ∈ N.primeFactors, (1 : ℝ) / (q : ℝ)) := by
          rw [← Finset.mul_sum]
  have hconst : 8 * (Real.log 2 + 1 / Real.log 2) ≤ 18 := by
    have hlo : (0.693 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hhi : Real.log 2 < 0.694 := by linarith [Real.log_two_lt_d9]
    have hinv : 1 / Real.log 2 < 1 / 0.693 :=
      one_div_lt_one_div_of_lt (by norm_num) hlo
    linarith
  have hexp_arg : 8 * (∑ q ∈ N.primeFactors, (1 : ℝ) / (q : ℝ)) ≤ 18 + 8 * Real.log L := by
    have hrec := primeFactors_recip_sum_le hN
    linarith
  calc
    (∏ q ∈ N.primeFactors, (1 + 4 / ((q : ℝ) - 1)))
      ≤ Real.exp (8 * ∑ q ∈ N.primeFactors, (1 : ℝ) / (q : ℝ)) := hprod
    _ ≤ Real.exp (18 + 8 * Real.log L) := Real.exp_le_exp.mpr hexp_arg
    _ = Real.exp 18 * Real.exp ((8 : ℕ) * Real.log L) := by rw [Real.exp_add]; norm_num
    _ = Real.exp 18 * (Real.exp (Real.log L)) ^ (8 : ℕ) := by rw [Real.exp_nat_mul]
    _ = Real.exp 18 * L ^ (8 : ℕ) := by rw [Real.exp_log hLpos]

/-- Fixed-power product bound `∏_{q | N} (1 + 4/(q-1)) ≤ (log(2N))^80` for all `N ≥ 2`. -/
theorem primeFactors_local_prod_le_log_pow {N : ℕ} (hN : 2 ≤ N) :
    (∏ q ∈ N.primeFactors, (1 + 4 / ((q : ℝ) - 1))) ≤
      (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by
  set L : ℝ := Real.log (2 * (N : ℝ))
  have hLpos : 0 < L := zero_lt_one.trans (one_lt_log_two_mul hN)
  have hq : (1 : ℝ) / 4 < Real.log L := quarter_lt_log_log_two_mul hN
  have h18 : Real.exp 18 ≤ L ^ (72 : ℕ) := by
    have h18le : (18 : ℝ) ≤ (72 : ℕ) * Real.log L := by
      push_cast
      linarith
    calc
      Real.exp 18 ≤ Real.exp ((72 : ℕ) * Real.log L) := Real.exp_le_exp.mpr h18le
      _ = (Real.exp (Real.log L)) ^ (72 : ℕ) := Real.exp_nat_mul _ _
      _ = L ^ (72 : ℕ) := by rw [Real.exp_log hLpos]
  calc
    (∏ q ∈ N.primeFactors, (1 + 4 / ((q : ℝ) - 1)))
      ≤ Real.exp 18 * L ^ (8 : ℕ) := primeFactors_local_prod_le_exp_mul_log_pow hN
    _ ≤ L ^ (72 : ℕ) * L ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_right h18 (pow_nonneg hLpos.le _)
    _ = L ^ (80 : ℕ) := by rw [← pow_add]

/-- Local prime-power series bound: if `R(p^k) ≤ 2 * p^(k/2)` for all `k ≥ 1`, then
`∑_{k ≥ 1} R(p^k) / p^k` is summable and bounded by `4 / (p - 1)`. -/
theorem local_series_summable_and_le {p : ℕ} (hp : 2 ≤ p) (R : ℕ → ℕ)
    (hR : ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2)) :
    Summable (fun k : ℕ => (R (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1)) ∧
      (∑' k : ℕ, (R (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1)) ≤ 4 / ((p : ℝ) - 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  let f : ℕ → ℝ := fun k => (R (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1)
  have hf_nonneg : ∀ k, 0 ≤ f k := fun k => by positivity
  have hterm : ∀ k, f k ≤ 2 * ((p : ℝ)⁻¹) ^ (k / 2 + 1) := by
    intro k
    have hRk : (R (p ^ (k + 1)) : ℝ) ≤ 2 * (p : ℝ) ^ ((k + 1) / 2) := by
      exact_mod_cast hR (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
    have hsub : (k + 1) / 2 + (k / 2 + 1) = k + 1 := by omega
    calc
      f k ≤ (2 * (p : ℝ) ^ ((k + 1) / 2)) / (p : ℝ) ^ (k + 1) :=
        div_le_div_of_nonneg_right hRk (pow_nonneg hppos.le _)
      _ = 2 * ((p : ℝ) ^ ((k + 1) / 2) / ((p : ℝ) ^ ((k + 1) / 2) * (p : ℝ) ^ (k / 2 + 1))) := by
        rw [← pow_add, hsub, mul_div_assoc]
      _ = 2 * ((p : ℝ)⁻¹) ^ (k / 2 + 1) := by
        rw [inv_pow]
        have hne : (p : ℝ) ^ ((k + 1) / 2) ≠ 0 := pow_ne_zero _ hppos.ne'
        field_simp [hne]
  have hpartial : ∀ M : ℕ, (∑ k ∈ Finset.range M, f k) ≤ 4 / ((p : ℝ) - 1) := by
    intro M
    have hle2 : (∑ k ∈ Finset.range M, f k) ≤ ∑ k ∈ Finset.range (2 * M), f k :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun k _ _ => hf_nonneg k)
    refine hle2.trans ?_
    have hpair : ∀ n : ℕ,
        (∑ k ∈ Finset.range (2 * n), (2 : ℝ) * ((p : ℝ)⁻¹) ^ (k / 2 + 1)) =
          4 * ∑ j ∈ Finset.range n, ((p : ℝ)⁻¹) ^ (j + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ m ihm =>
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, ihm, Finset.sum_range_succ]
        have h1 : (2 * m) / 2 = m := by omega
        have h2 : (2 * m + 1) / 2 = m := by omega
        rw [h1, h2]
        ring
    have hgeom : (∑ j ∈ Finset.range M, ((p : ℝ)⁻¹) ^ (j + 1)) ≤ 1 / ((p : ℝ) - 1) := by
      have hpull : (∑ j ∈ Finset.range M, ((p : ℝ)⁻¹) ^ (j + 1)) =
          (p : ℝ)⁻¹ * ∑ j ∈ Finset.range M, ((p : ℝ)⁻¹) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_succ']
      rw [hpull]
      have hne1 : (p : ℝ)⁻¹ ≠ 1 := by
        intro h
        have : (p : ℝ) = 1 := inv_eq_one.mp h
        linarith
      rw [geom_sum_eq hne1]
      have hneg : (p : ℝ)⁻¹ - 1 = -(((p : ℝ) - 1) / (p : ℝ)) := by
        field_simp [hppos.ne']
        ring
      have hnum : ((p : ℝ)⁻¹) ^ M - 1 = -(1 - ((p : ℝ)⁻¹) ^ M) := by ring
      rw [hneg, hnum, neg_div_neg_eq]
      have hpow0 : 0 ≤ ((p : ℝ)⁻¹) ^ M := by positivity
      have hle1 : 1 - ((p : ℝ)⁻¹) ^ M ≤ 1 := by linarith
      have hdenpos : 0 < ((p : ℝ) - 1) / (p : ℝ) := div_pos hp1pos hppos
      calc
        (p : ℝ)⁻¹ * ((1 - ((p : ℝ)⁻¹) ^ M) / (((p : ℝ) - 1) / (p : ℝ)))
          ≤ (p : ℝ)⁻¹ * (1 / (((p : ℝ) - 1) / (p : ℝ))) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hle1 hdenpos.le) (by positivity)
        _ = 1 / ((p : ℝ) - 1) := by field_simp [hppos.ne', hp1pos.ne']
    calc
      (∑ k ∈ Finset.range (2 * M), f k)
        ≤ ∑ k ∈ Finset.range (2 * M), 2 * ((p : ℝ)⁻¹) ^ (k / 2 + 1) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = 4 * ∑ j ∈ Finset.range M, ((p : ℝ)⁻¹) ^ (j + 1) := hpair M
      _ ≤ 4 * (1 / ((p : ℝ) - 1)) := mul_le_mul_of_nonneg_left hgeom (by norm_num)
      _ = 4 / ((p : ℝ) - 1) := by ring
  refine ⟨summable_of_sum_range_le hf_nonneg hpartial, ?_⟩
  exact Real.tsum_le_of_sum_range_le hf_nonneg hpartial

end AnalyticBounds

/-! ## Concrete Modular Square-Root Counts -/

section ModularRoots

/-- Finite set of solutions `b ∈ ZMod A` to `b^2 = -m`. -/
def modNegSqRoots (m A : ℕ) [NeZero A] : Finset (ZMod A) :=
  Finset.univ.filter (fun b : ZMod A => b ^ 2 = -(m : ZMod A))

/-- Count `R(A) = #{b mod A : b^2 ≡ -m (mod A)}` (defined as `0` for `A = 0`). -/
def modNegSqRootCount (m A : ℕ) : ℕ :=
  if h : A = 0 then 0
  else
    haveI : NeZero A := ⟨h⟩
    (modNegSqRoots m A).card

theorem modNegSqRootCount_of_ne_zero (m A : ℕ) [NeZero A] :
    modNegSqRootCount m A = (modNegSqRoots m A).card := by
  unfold modNegSqRootCount
  rw [dif_neg (NeZero.ne A)]

theorem modNegSqRootCount_one (m : ℕ) : modNegSqRootCount m 1 = 1 := by
  rw [modNegSqRootCount_of_ne_zero]
  have h : modNegSqRoots m 1 = Finset.univ := by
    ext x
    simp [modNegSqRoots, Subsingleton.elim (x ^ 2) (-(m : ZMod 1))]
  rw [h]
  simp

/-- CRT multiplicativity of `modNegSqRootCount m`. -/
theorem modNegSqRootCount_mul_coprime (m : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    modNegSqRootCount m (a * b) = modNegSqRootCount m a * modNegSqRootCount m b := by
  by_cases ha : a = 0
  · subst ha
    simp [modNegSqRootCount]
  by_cases hb : b = 0
  · subst hb
    simp [modNegSqRootCount]
  haveI : NeZero a := ⟨ha⟩
  haveI : NeZero b := ⟨hb⟩
  haveI : NeZero (a * b) := ⟨mul_ne_zero ha hb⟩
  rw [modNegSqRootCount_of_ne_zero, modNegSqRootCount_of_ne_zero, modNegSqRootCount_of_ne_zero]
  let e : ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder hab
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_product, modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and]
    have hmap : e (x ^ 2) = e (-(m : ZMod (a * b))) := congrArg e hx
    simp only [map_pow, map_neg, map_natCast, Prod.ext_iff, Prod.pow_fst, Prod.pow_snd,
      Prod.fst_neg, Prod.snd_neg, Prod.fst_natCast, Prod.snd_natCast] at hmap
    exact hmap
  · intro x₁ _ x₂ _ hEq
    exact e.injective hEq
  · intro y hy
    simp only [Finset.mem_product, modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and]
    apply e.injective
    simp only [map_pow, map_neg, map_natCast, e.apply_symm_apply, Prod.ext_iff, Prod.pow_fst,
      Prod.pow_snd, Prod.fst_neg, Prod.snd_neg, Prod.fst_natCast, Prod.snd_natCast]
    exact hy

private lemma zmod_eq_zero_iff_dvd_val {n : ℕ} [NeZero n] (x : ZMod n) :
    x = 0 ↔ n ∣ x.val := by
  constructor
  · rintro rfl
    simp
  · intro h
    have hlt : x.val < n := x.val_lt
    have hv0 : x.val = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
    exact (ZMod.val_eq_zero x).mp hv0

/-- For an odd prime `p` not dividing `m`, there are at most 2 roots of `b^2 ≡ -m (mod p^k)`. -/
theorem modNegSqRootCount_odd_prime_pow_coprime {m p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hpm : ¬ p ∣ m) (k : ℕ) :
    modNegSqRootCount m (p ^ k) ≤ 2 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  rw [modNegSqRootCount_of_ne_zero]
  by_cases hne : (modNegSqRoots m (p ^ k)).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hsub : modNegSqRoots m (p ^ k) ⊆ ({x₀, -x₀} : Finset (ZMod (p ^ k))) := by
      intro x hx
      simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx₀
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hk : k = 0
      · subst hk
        left
        haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
        exact Subsingleton.elim x x₀
      have hdiff : (x - x₀) * (x + x₀) = 0 := by
        have : (x - x₀) * (x + x₀) = x ^ 2 - x₀ ^ 2 := by ring
        rw [this, hx, hx₀, sub_self]
      have hdvd_prod : p ^ k ∣ (x - x₀).val * (x + x₀).val := by
        have hcast : (((x - x₀).val * (x + x₀).val : ℕ) : ZMod (p ^ k)) = 0 := by
          push_cast
          simpa [ZMod.natCast_zmod_val] using hdiff
        exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
      have hnot_both : ¬ (p ∣ (x - x₀).val ∧ p ∣ (x + x₀).val) := by
        rintro ⟨h1, h2⟩
        have hsum : p ∣ (x - x₀).val + (x + x₀).val := dvd_add h1 h2
        have hcast0 : (((x - x₀).val + (x + x₀).val : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr hsum
        have hp_dvd : p ∣ p ^ k := dvd_pow_self p hk
        let f : ZMod (p ^ k) →+* ZMod p := ZMod.castHom hp_dvd (ZMod p)
        have hf : f (2 * x) = 0 := by
          have hfx : f (x - x₀) + f (x + x₀) = f (2 * x) := by
            rw [← map_add]
            congr 1
            ring
          rw [← hfx]
          have h1' : f (x - x₀) = (((x - x₀).val : ℕ) : ZMod p) := by
            simpa [f] using (ZMod.castHom_apply (x - x₀)).symm
          have h2' : f (x + x₀) = (((x + x₀).val : ℕ) : ZMod p) := by
            simpa [f] using (ZMod.castHom_apply (x + x₀)).symm
          rw [h1', h2']
          simpa [Nat.cast_add] using hcast0
        have hfx0 : f x = 0 := by
          haveI : Fact p.Prime := ⟨hp⟩
          have h2ne : (2 : ZMod p) ≠ 0 := by
            intro h20
            have h2dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h20)
            have := (Nat.dvd_prime Nat.prime_two).mp h2dvd
            rcases this with h | h
            · exact hp.ne_one h
            · exact hp2 h
          rw [map_mul, map_ofNat] at hf
          exact (mul_eq_zero.mp hf).resolve_left h2ne
        have hfx2 : f (x ^ 2) = 0 := by rw [map_pow, hfx0, zero_pow (by norm_num)]
        rw [hx, map_neg, map_natCast, neg_eq_zero] at hfx2
        exact hpm ((ZMod.natCast_eq_zero_iff m p).mp hfx2)
      have hcop_or : p ^ k ∣ (x - x₀).val ∨ p ^ k ∣ (x + x₀).val := by
        by_cases h1 : p ∣ (x - x₀).val
        · have h2 : ¬ p ∣ (x + x₀).val := fun h2 => hnot_both ⟨h1, h2⟩
          have hcop : Nat.Coprime (p ^ k) (x + x₀).val :=
            (hp.coprime_iff_not_dvd.mpr h2).pow_left k
          exact Or.inl (hcop.dvd_of_dvd_mul_right hdvd_prod)
        · have hcop : Nat.Coprime (p ^ k) (x - x₀).val :=
            (hp.coprime_iff_not_dvd.mpr h1).pow_left k
          exact Or.inr (hcop.dvd_of_dvd_mul_left hdvd_prod)
      rcases hcop_or with h1 | h2
      · left
        have := (zmod_eq_zero_iff_dvd_val (x - x₀)).mpr h1
        exact sub_eq_zero.mp this
      · right
        have := (zmod_eq_zero_iff_dvd_val (x + x₀)).mpr h2
        exact eq_neg_of_add_eq_zero_left this
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- For odd `m`, there are at most 4 roots of `b^2 ≡ -m (mod 2^k)`. -/
theorem modNegSqRootCount_two_pow_odd {m : ℕ} (hm : Odd m) (k : ℕ) :
    modNegSqRootCount m (2 ^ k) ≤ 4 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [modNegSqRootCount_of_ne_zero]
  by_cases hk : k ≤ 2
  · calc
      (modNegSqRoots m (2 ^ k)).card ≤ Fintype.card (ZMod (2 ^ k)) := Finset.card_le_univ _
      _ = 2 ^ k := ZMod.card (2 ^ k)
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
      _ = 4 := by norm_num
  have hk3 : 3 ≤ k := by omega
  by_cases hne : (modNegSqRoots m (2 ^ k)).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let half : ZMod (2 ^ k) := ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k))
    have hsub : modNegSqRoots m (2 ^ k) ⊆ ({x₀, x₀ + half, -x₀, -x₀ + half} : Finset (ZMod (2 ^ k))) := by
      intro x hx
      simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx₀
      have hdiff : (x - x₀) * (x + x₀) = 0 := by
        have : (x - x₀) * (x + x₀) = x ^ 2 - x₀ ^ 2 := by ring
        rw [this, hx, hx₀, sub_self]
      have hdvd_prod : 2 ^ k ∣ (x - x₀).val * (x + x₀).val := by
        have hcast : (((x - x₀).val * (x + x₀).val : ℕ) : ZMod (2 ^ k)) = 0 := by
          push_cast
          simpa [ZMod.natCast_zmod_val] using hdiff
        exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
      have hnot4 : ¬ (4 ∣ (x - x₀).val ∧ 4 ∣ (x + x₀).val) := by
        rintro ⟨h1, h2⟩
        have hsum : 4 ∣ (x - x₀).val + (x + x₀).val := dvd_add h1 h2
        have hcast0 : (((x - x₀).val + (x + x₀).val : ℕ) : ZMod 4) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr hsum
        have h4dvd : 4 ∣ 2 ^ k := by
          have : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
          simpa using this
        let f : ZMod (2 ^ k) →+* ZMod 4 := ZMod.castHom h4dvd (ZMod 4)
        have hf : f (2 * x) = 0 := by
          have hfx : f (x - x₀) + f (x + x₀) = f (2 * x) := by
            rw [← map_add]
            congr 1
            ring
          rw [← hfx]
          have h1' : f (x - x₀) = (((x - x₀).val : ℕ) : ZMod 4) := by
            simpa [f] using (ZMod.castHom_apply (x - x₀)).symm
          have h2' : f (x + x₀) = (((x + x₀).val : ℕ) : ZMod 4) := by
            simpa [f] using (ZMod.castHom_apply (x + x₀)).symm
          rw [h1', h2']
          simpa [Nat.cast_add] using hcast0
        have h2dvd : 2 ∣ (f x).val := by
          have h4mul : 4 ∣ 2 * (f x).val := by
            have : ((2 * (f x).val : ℕ) : ZMod 4) = 0 := by
              push_cast
              simpa [ZMod.natCast_zmod_val, map_mul, map_ofNat] using hf
            exact (ZMod.natCast_eq_zero_iff _ _).mp this
          omega
        have hx2_even : 2 ∣ ((f x) ^ 2).val := by
          have hsq : ((f x).val ^ 2 : ℕ) % 4 = ((f x) ^ 2).val := by
            have := ZMod.val_natCast 4 ((f x).val ^ 2)
            simpa [ZMod.natCast_zmod_val] using this.symm
          have h4sq : 4 ∣ (f x).val ^ 2 := by
            obtain ⟨t, ht⟩ := h2dvd
            exact ⟨t ^ 2, by rw [ht]; ring⟩
          omega
        have hfx2 : (f x) ^ 2 = -(m : ZMod 4) := by
          rw [← map_pow, hx, map_neg, map_natCast]
        rw [hfx2] at hx2_even
        obtain ⟨t, ht⟩ := hm
        have hnegm : (-(m : ZMod 4)).val % 2 = 1 := by
          have hm4 : (-(m : ZMod 4)) = -((2 * t + 1 : ℕ) : ZMod 4) := by rw [ht]
          have hmod : (2 * t + 1) % 4 = 1 ∨ (2 * t + 1) % 4 = 3 := by omega
          have hcast : ((2 * t + 1 : ℕ) : ZMod 4) = (((2 * t + 1) % 4 : ℕ) : ZMod 4) := by
            rw [ZMod.natCast_mod]
          rw [hm4, hcast]
          rcases hmod with h | h <;> rw [h] <;> decide
        omega
      have hdvd_half : 2 ^ (k - 1) ∣ (x - x₀).val ∨ 2 ^ (k - 1) ∣ (x + x₀).val := by
        have hfactor_dvd : ∀ a b : ℕ, 2 ^ k ∣ a * b → ¬ (4 ∣ b) → 2 ^ (k - 1) ∣ a := by
          intro a b hab hb4
          by_cases hb2 : 2 ∣ b
          · obtain ⟨b', rfl⟩ := hb2
            have hb'odd : ¬ 2 ∣ b' := fun h => hb4 (by obtain ⟨c, rfl⟩ := h; exact ⟨c, by ring⟩)
            have hcop : Nat.Coprime (2 ^ (k - 1)) b' :=
              (Nat.prime_two.coprime_iff_not_dvd.mpr hb'odd).pow_left (k - 1)
            have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
              rw [← pow_succ', show k - 1 + 1 = k by omega]
            rw [h2k] at hab
            have hab' : 2 ^ (k - 1) ∣ a * b' := by
              have : 2 * 2 ^ (k - 1) ∣ 2 * (a * b') := by
                simpa [mul_left_comm, mul_assoc] using hab
              exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
            exact hcop.dvd_of_dvd_mul_right hab'
          · have hcop : Nat.Coprime (2 ^ k) b :=
              (Nat.prime_two.coprime_iff_not_dvd.mpr hb2).pow_left k
            exact (Nat.pow_dvd_pow 2 (by omega)).trans (hcop.dvd_of_dvd_mul_right hab)
        by_cases h4 : 4 ∣ (x - x₀).val
        · exact Or.inl (hfactor_dvd _ _ hdvd_prod (fun h => hnot4 ⟨h4, h⟩))
        · exact Or.inr (hfactor_dvd _ _ (by rwa [mul_comm]) h4)
      have hhalf_cases : ∀ y : ZMod (2 ^ k), 2 ^ (k - 1) ∣ y.val → y = 0 ∨ y = half := by
        intro y hy
        obtain ⟨q, hq⟩ := hy
        have hylt : y.val < 2 ^ k := y.val_lt
        have h2k : 2 ^ k = 2 ^ (k - 1) * 2 := by
          rw [← pow_succ, show k - 1 + 1 = k by omega]
        have hqlt : q < 2 := by
          have hpos : 0 < 2 ^ (k - 1) := by positivity
          nlinarith
        have hq01 : q = 0 ∨ q = 1 := by omega
        rcases hq01 with rfl | rfl
        · left
          exact (ZMod.val_eq_zero y).mp (by simpa using hq)
        · right
          have hyval : y.val = 2 ^ (k - 1) := by simpa using hq
          rw [← ZMod.natCast_zmod_val y, hyval]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hdvd_half with h1 | h2
      · rcases hhalf_cases (x - x₀) h1 with h | h
        · left; exact sub_eq_zero.mp h
        · right; left; exact eq_add_of_sub_eq' h
      · rcases hhalf_cases (x + x₀) h2 with h | h
        · right; right; left; exact eq_neg_of_add_eq_zero_left h
        · right; right; right
          have : x = half - x₀ := eq_sub_of_add_eq h
          rw [this, sub_eq_neg_add]
    calc
      (modNegSqRoots m (2 ^ k)).card
        ≤ ({x₀, x₀ + half, -x₀, -x₀ + half} : Finset (ZMod (2 ^ k))).card :=
          Finset.card_le_card hsub
      _ ≤ 4 := by
          calc
            ({x₀, x₀ + half, -x₀, -x₀ + half} : Finset (ZMod (2 ^ k))).card
              ≤ ({x₀ + half, -x₀, -x₀ + half} : Finset (ZMod (2 ^ k))).card + 1 :=
                Finset.card_insert_le _ _
            _ ≤ ({-x₀, -x₀ + half} : Finset (ZMod (2 ^ k))).card + 1 + 1 :=
                Nat.add_le_add_right (Finset.card_insert_le _ _) 1
            _ ≤ 2 + 1 + 1 := by
                have := Finset.card_le_two (a := -x₀) (b := -x₀ + half)
                omega
            _ = 4 := by norm_num
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- For odd `N` and `m = 2 * N`, there is at most 1 root of `b^2 ≡ -2N (mod 2^k)`. -/
theorem modNegSqRootCount_two_pow_two_mul_odd {N : ℕ} (hN : Odd N) (k : ℕ) :
    modNegSqRootCount (2 * N) (2 ^ k) ≤ 1 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [modNegSqRootCount_of_ne_zero]
  match k with
  | 0 =>
    calc
      (modNegSqRoots (2 * N) 1).card ≤ Fintype.card (ZMod 1) := Finset.card_le_univ _
      _ = 1 := ZMod.card 1
  | 1 =>
    have hsub : modNegSqRoots (2 * N) 2 ⊆ ({0} : Finset (ZMod 2)) := by
      intro x hx
      simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_singleton]
      have h2N : ((2 * N : ℕ) : ZMod 2) = 0 := by
        rw [Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
      rw [h2N, neg_zero] at hx
      fin_cases x
      · rfl
      · exfalso; revert hx; decide
    exact (Finset.card_le_card hsub).trans (by simp)
  | k + 2 =>
    have hempty : modNegSqRoots (2 * N) (2 ^ (k + 2)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have h4dvd : 4 ∣ 2 ^ (k + 2) := by
        have : 2 ^ 2 ∣ 2 ^ (k + 2) := Nat.pow_dvd_pow 2 (by omega)
        simpa using this
      let f : ZMod (2 ^ (k + 2)) →+* ZMod 4 := ZMod.castHom h4dvd (ZMod 4)
      have hfx : (f x) ^ 2 = -((2 * N : ℕ) : ZMod 4) := by
        rw [← map_pow, hx, map_neg, map_natCast]
      obtain ⟨t, ht⟩ := hN
      have h2N4 : -((2 * N : ℕ) : ZMod 4) = (2 : ZMod 4) := by
        have : (2 * N) % 4 = 2 := by omega
        have hcast : ((2 * N : ℕ) : ZMod 4) = (((2 * N) % 4 : ℕ) : ZMod 4) := by
          rw [ZMod.natCast_mod]
        rw [hcast, this]
        decide
      rw [h2N4] at hfx
      generalize f x = y at hfx
      fin_cases y <;> (revert hfx; decide)
    rw [hempty]
    simp

/-- Global coprime root bound `R(A) ≤ 2^{ω(A) + 1}` for odd `m` and `Coprime A m`. -/
theorem modNegSqRootCount_le_two_pow_omega_succ_of_odd {m A : ℕ} (hm : Odd m)
    (hA : A ≠ 0) (hcop : Nat.Coprime A m) :
    modNegSqRootCount m A ≤ 2 ^ (A.primeFactors.card + 1) := by
  have hprod_eq : A = ∏ p ∈ A.primeFactors, p ^ (A.factorization p) := by
    simpa [Finsupp.prod, Nat.support_factorization] using
      (Nat.factorization_prod_pow_eq_self hA).symm
  have hmult : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      modNegSqRootCount m (∏ p ∈ s, p ^ (A.factorization p)) =
        ∏ p ∈ s, modNegSqRootCount m (p ^ (A.factorization p)) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp [modNegSqRootCount_one]
    | @insert p s hp ih =>
      intro hprimes
      rw [Finset.prod_insert hp, Finset.prod_insert hp]
      have hcop_ps : Nat.Coprime (p ^ (A.factorization p))
          (∏ q ∈ s, q ^ (A.factorization q)) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        have hp' := hprimes p (Finset.mem_insert_self p s)
        have hq' := hprimes q (Finset.mem_insert_of_mem hq)
        have hne : p ≠ q := fun h => hp (h ▸ hq)
        exact ((Nat.coprime_primes hp' hq').mpr hne).pow _ _
      rw [modNegSqRootCount_mul_coprime m hcop_ps,
        ih (fun q hq => hprimes q (Finset.mem_insert_of_mem hq))]
  conv_lhs => rw [hprod_eq]
  rw [hmult A.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  by_cases h2 : 2 ∈ A.primeFactors
  · rw [← Finset.mul_prod_erase A.primeFactors _ h2]
    have h2le : modNegSqRootCount m (2 ^ (A.factorization 2)) ≤ 4 :=
      modNegSqRootCount_two_pow_odd hm (A.factorization 2)
    have hrest : (∏ p ∈ A.primeFactors.erase 2, modNegSqRootCount m (p ^ (A.factorization p))) ≤
        ∏ _p ∈ A.primeFactors.erase 2, (2 : ℕ) := by
      apply Finset.prod_le_prod'
      intro p hp
      have hp_mem : p ∈ A.primeFactors := Finset.mem_of_mem_erase hp
      have hp_ne2 : p ≠ 2 := Finset.ne_of_mem_erase hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpm : ¬ p ∣ m := by
        intro hpm
        have hpdvd : p ∣ A := Nat.dvd_of_mem_primeFactors hp_mem
        have : p ∣ Nat.gcd A m := Nat.dvd_gcd hpdvd hpm
        rw [hcop.gcd_eq_one] at this
        exact hp_prime.ne_one (Nat.dvd_one.mp this)
      exact modNegSqRootCount_odd_prime_pow_coprime hp_prime hp_ne2 hpm (A.factorization p)
    rw [Finset.prod_const, Finset.card_erase_of_mem h2] at hrest
    have hpos : 1 ≤ A.primeFactors.card := Finset.card_pos.mpr ⟨2, h2⟩
    calc
      modNegSqRootCount m (2 ^ (A.factorization 2)) *
          ∏ p ∈ A.primeFactors.erase 2, modNegSqRootCount m (p ^ (A.factorization p))
        ≤ 4 * 2 ^ (A.primeFactors.card - 1) := Nat.mul_le_mul h2le hrest
      _ = 2 ^ (A.primeFactors.card + 1) := by
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_add, show 2 + (A.primeFactors.card - 1) =
            A.primeFactors.card + 1 by omega]
  · have hall : (∏ p ∈ A.primeFactors, modNegSqRootCount m (p ^ (A.factorization p))) ≤
        ∏ _p ∈ A.primeFactors, (2 : ℕ) := by
      apply Finset.prod_le_prod'
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_ne2 : p ≠ 2 := fun h => h2 (h ▸ hp)
      have hpm : ¬ p ∣ m := by
        intro hpm
        have hpdvd : p ∣ A := Nat.dvd_of_mem_primeFactors hp
        have : p ∣ Nat.gcd A m := Nat.dvd_gcd hpdvd hpm
        rw [hcop.gcd_eq_one] at this
        exact hp_prime.ne_one (Nat.dvd_one.mp this)
      exact modNegSqRootCount_odd_prime_pow_coprime hp_prime hp_ne2 hpm (A.factorization p)
    rw [Finset.prod_const] at hall
    exact hall.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))

/-- Global coprime root bound `R(A) ≤ 2^{ω(A) + 1}` for even discriminant `m = 2 * N` (`Odd N`)
and `Coprime A N`. -/
theorem modNegSqRootCount_le_two_pow_omega_succ_of_two_mul_odd {N A : ℕ} (hN : Odd N)
    (hA : A ≠ 0) (hcop : Nat.Coprime A N) :
    modNegSqRootCount (2 * N) A ≤ 2 ^ (A.primeFactors.card + 1) := by
  have hprod_eq : A = ∏ p ∈ A.primeFactors, p ^ (A.factorization p) := by
    simpa [Finsupp.prod, Nat.support_factorization] using
      (Nat.factorization_prod_pow_eq_self hA).symm
  have hmult : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      modNegSqRootCount (2 * N) (∏ p ∈ s, p ^ (A.factorization p)) =
        ∏ p ∈ s, modNegSqRootCount (2 * N) (p ^ (A.factorization p)) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => intro _; simp [modNegSqRootCount_one]
    | @insert p s hp ih =>
      intro hprimes
      rw [Finset.prod_insert hp, Finset.prod_insert hp]
      have hcop_ps : Nat.Coprime (p ^ (A.factorization p))
          (∏ q ∈ s, q ^ (A.factorization q)) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        have hp' := hprimes p (Finset.mem_insert_self p s)
        have hq' := hprimes q (Finset.mem_insert_of_mem hq)
        have hne : p ≠ q := fun h => hp (h ▸ hq)
        exact ((Nat.coprime_primes hp' hq').mpr hne).pow _ _
      rw [modNegSqRootCount_mul_coprime (2 * N) hcop_ps,
        ih (fun q hq => hprimes q (Finset.mem_insert_of_mem hq))]
  conv_lhs => rw [hprod_eq]
  rw [hmult A.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  have hall : (∏ p ∈ A.primeFactors, modNegSqRootCount (2 * N) (p ^ (A.factorization p))) ≤
      ∏ _p ∈ A.primeFactors, (2 : ℕ) := by
    apply Finset.prod_le_prod'
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    by_cases hp2 : p = 2
    · subst hp2
      exact (modNegSqRootCount_two_pow_two_mul_odd hN (A.factorization 2)).trans (by norm_num)
    · have hp2N : ¬ p ∣ 2 * N := by
        intro h
        rcases hp_prime.dvd_mul.mp h with h2 | hN'
        · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
          · exact hp_prime.ne_one h1
          · exact hp2 h2'
        · have hpdvd : p ∣ A := Nat.dvd_of_mem_primeFactors hp
          have : p ∣ Nat.gcd A N := Nat.dvd_gcd hpdvd hN'
          rw [hcop.gcd_eq_one] at this
          exact hp_prime.ne_one (Nat.dvd_one.mp this)
      exact modNegSqRootCount_odd_prime_pow_coprime hp_prime hp2 hp2N (A.factorization p)
  rw [Finset.prod_const] at hall
  exact hall.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))

/-- For any odd prime `p`, nonzero `m`, and `k ≥ 1`, `modNegSqRootCount m (p^k) ≤ 2 * p^(k/2)`. -/
theorem modNegSqRootCount_odd_prime_pow_le {m p : ℕ} (hm : m ≠ 0) (hp : Nat.Prime p)
    (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    modNegSqRootCount m (p ^ k) ≤ 2 * p ^ (k / 2) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  rw [modNegSqRootCount_of_ne_zero]
  set w := m.factorization p
  by_cases hkw : k ≤ w
  · -- When `k ≤ v_p(m)`, `x^2 ≡ -m ≡ 0 (mod p^k)` forces `p^((k+1)/2) ∣ x.val`.
    have hpk_m : p ^ k ∣ m :=
      (Nat.pow_dvd_pow p hkw).trans (Nat.ordProj_dvd m p)
    have hcard_le : (modNegSqRoots m (p ^ k)).card ≤ (Finset.range (p ^ (k / 2))).card := by
      refine Finset.card_le_card_of_injOn (fun x : ZMod (p ^ k) => x.val / p ^ ((k + 1) / 2)) ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_range]
        have hlt : x.val < p ^ k := x.val_lt
        have hpow : p ^ (k / 2) * p ^ ((k + 1) / 2) = p ^ k := by
          rw [← pow_add, show k / 2 + (k + 1) / 2 = k by omega]
        rw [Nat.div_lt_iff_lt_mul (pow_pos hp.pos _), hpow]
        exact hlt
      · intro x₁ hx₁ x₂ hx₂ hEq
        have hdvd_half : ∀ x ∈ modNegSqRoots m (p ^ k), p ^ ((k + 1) / 2) ∣ x.val := by
          intro x hx
          simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have hxm0 : (m : ZMod (p ^ k)) = 0 := (ZMod.natCast_eq_zero_iff m (p ^ k)).mpr hpk_m
          rw [hxm0, neg_zero] at hx
          have hpk_x2 : p ^ k ∣ x.val ^ 2 := by
            have : ((x.val ^ 2 : ℕ) : ZMod (p ^ k)) = 0 := by
              push_cast
              simpa [ZMod.natCast_zmod_val] using hx
            exact (ZMod.natCast_eq_zero_iff _ _).mp this
          by_cases hx0 : x.val = 0
          · rw [hx0]; exact dvd_zero _
          have hx20 : x.val ^ 2 ≠ 0 := pow_ne_zero 2 hx0
          have hv : k ≤ (x.val ^ 2).factorization p := by
            have h := (Nat.Prime.pow_dvd_iff_le_factorization hp hx20).mp hpk_x2
            exact h
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hv
          have hv' : (k + 1) / 2 ≤ x.val.factorization p := by omega
          exact (Nat.Prime.pow_dvd_iff_le_factorization hp hx0).mpr hv'
        have h1 := Nat.mul_div_cancel' (hdvd_half x₁ hx₁)
        have h2 := Nat.mul_div_cancel' (hdvd_half x₂ hx₂)
        apply ZMod.val_injective (p ^ k)
        rw [← h1, ← h2]
        exact congrArg (p ^ ((k + 1) / 2) * ·) hEq
    simpa [Finset.card_range] using hcard_le.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  · -- When `w < k`, write `m = p^w * m'` with `¬ p ∣ m'`.
    have hwk : w < k := Nat.lt_of_not_ge hkw
    have hpw_m : p ^ w ∣ m := Nat.ordProj_dvd m p
    set m' := m / p ^ w
    have hm_eq : m = p ^ w * m' := (Nat.mul_div_cancel' hpw_m).symm
    have hpm' : ¬ p ∣ m' := by
      intro hd
      have hpw1 : p ^ (w + 1) ∣ m := by
        rw [hm_eq, pow_succ]
        exact Nat.mul_dvd_mul_left (p ^ w) hd
      have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp hm).mp hpw1
      omega
    by_cases hweven : Even w
    · obtain ⟨t, ht⟩ := hweven
      have h2t : w = 2 * t := by omega
      have ht_le : t ≤ k / 2 := by omega
      haveI : NeZero (p ^ (k - w)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      -- Map each root `x` to `(u mod p^(k-w), quotient)` where `x.val = p^t * u`.
      let phi : ZMod (p ^ k) → ZMod (p ^ (k - w)) × ℕ :=
        fun x => (((x.val / p ^ t : ℕ) : ZMod (p ^ (k - w))),
                  (x.val / p ^ t) / p ^ (k - w))
      have hdvd_pt : ∀ x ∈ modNegSqRoots m (p ^ k), p ^ t ∣ x.val := by
        intro x hx
        simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        by_cases hx0 : x.val = 0
        · rw [hx0]; exact dvd_zero _
        have hpk_sum : p ^ k ∣ x.val ^ 2 + m := by
          have : ((x.val ^ 2 + m : ℕ) : ZMod (p ^ k)) = 0 := by
            push_cast
            rw [ZMod.natCast_zmod_val, hx, neg_add_cancel]
          exact (ZMod.natCast_eq_zero_iff _ _).mp this
        have hpw_x2 : p ^ w ∣ x.val ^ 2 := by
          have h1 : p ^ w ∣ x.val ^ 2 + m :=
            (Nat.pow_dvd_pow p hwk.le).trans hpk_sum
          exact (Nat.dvd_add_left hpw_m).mp h1
        have hv : w ≤ (x.val ^ 2).factorization p :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp (pow_ne_zero 2 hx0)).mp hpw_x2
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hv
        have hvt : t ≤ x.val.factorization p := by omega
        exact (Nat.Prime.pow_dvd_iff_le_factorization hp hx0).mpr hvt
      have hcard_le : (modNegSqRoots m (p ^ k)).card ≤
          (modNegSqRoots m' (p ^ (k - w)) ×ˢ Finset.range (p ^ t)).card := by
        refine Finset.card_le_card_of_injOn phi ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe] at hx
          have hpt := hdvd_pt x hx
          set u := x.val / p ^ t
          have hxu : x.val = p ^ t * u := (Nat.mul_div_cancel' hpt).symm
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, phi]
          constructor
          · simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            have hpk_sum : p ^ k ∣ x.val ^ 2 + m := by
              have : ((x.val ^ 2 + m : ℕ) : ZMod (p ^ k)) = 0 := by
                push_cast
                rw [ZMod.natCast_zmod_val, hx, neg_add_cancel]
              exact (ZMod.natCast_eq_zero_iff _ _).mp this
            have hfac : x.val ^ 2 + m = p ^ w * (u ^ 2 + m') := by
              rw [hxu, hm_eq, mul_pow, ← pow_mul, show t * 2 = w by omega]
              ring
            have hpk_eq : p ^ k = p ^ w * p ^ (k - w) := by
              rw [← pow_add, show w + (k - w) = k by omega]
            rw [hfac, hpk_eq] at hpk_sum
            have hdvd_u : p ^ (k - w) ∣ u ^ 2 + m' :=
              (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos w)).mp hpk_sum
            have hzero : ((u ^ 2 + m' : ℕ) : ZMod (p ^ (k - w))) = 0 :=
              (ZMod.natCast_eq_zero_iff _ _).mpr hdvd_u
            push_cast at hzero
            exact eq_neg_of_add_eq_zero_left hzero
          · have hult : u < p ^ (k - t) := by
              rw [Nat.div_lt_iff_lt_mul (pow_pos hp.pos t)]
              have hpow : p ^ (k - t) * p ^ t = p ^ k := by
                rw [← pow_add, show k - t + t = k by omega]
              rw [hpow]
              exact x.val_lt
            rw [Nat.div_lt_iff_lt_mul (pow_pos hp.pos (k - w))]
            have hpow : p ^ t * p ^ (k - w) = p ^ (k - t) := by
              rw [← pow_add, show t + (k - w) = k - t by omega]
            rw [hpow]
            exact hult
        · intro x₁ hx₁ x₂ hx₂ hEq
          simp only [Finset.mem_coe] at hx₁ hx₂
          have h1 := hdvd_pt x₁ hx₁
          have h2 := hdvd_pt x₂ hx₂
          simp only [phi, Prod.mk.injEq] at hEq
          have hmod : (x₁.val / p ^ t) % p ^ (k - w) = (x₂.val / p ^ t) % p ^ (k - w) := by
            have := congrArg ZMod.val hEq.1
            simpa [ZMod.val_natCast] using this
          have hdiv : (x₁.val / p ^ t) / p ^ (k - w) = (x₂.val / p ^ t) / p ^ (k - w) := hEq.2
          have hu : x₁.val / p ^ t = x₂.val / p ^ t := by
            rw [← Nat.div_add_mod (x₁.val / p ^ t) (p ^ (k - w)),
              ← Nat.div_add_mod (x₂.val / p ^ t) (p ^ (k - w)), hdiv, hmod]
          apply ZMod.val_injective (p ^ k)
          rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, hu]
      rw [Finset.card_product, Finset.card_range,
        ← modNegSqRootCount_of_ne_zero m' (p ^ (k - w))] at hcard_le
      have hunit := modNegSqRootCount_odd_prime_pow_coprime hp hp2 hpm' (k - w)
      calc
        (modNegSqRoots m (p ^ k)).card
          ≤ modNegSqRootCount m' (p ^ (k - w)) * p ^ t := hcard_le
        _ ≤ 2 * p ^ t := Nat.mul_le_mul_right _ hunit
        _ ≤ 2 * p ^ (k / 2) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hp.pos ht_le)
    · -- When `w` is odd and `w < k`, no root exists!
      have hempty : modNegSqRoots m (p ^ k) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [modNegSqRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hpk_sum : p ^ k ∣ x.val ^ 2 + m := by
          have : ((x.val ^ 2 + m : ℕ) : ZMod (p ^ k)) = 0 := by
            push_cast
            rw [ZMod.natCast_zmod_val, hx, neg_add_cancel]
          exact (ZMod.natCast_eq_zero_iff _ _).mp this
        have hpw1_sum : p ^ (w + 1) ∣ x.val ^ 2 + m :=
          (Nat.pow_dvd_pow p hwk).trans hpk_sum
        have hpw_x2 : p ^ w ∣ x.val ^ 2 :=
          (Nat.dvd_add_left hpw_m).mp ((Nat.pow_dvd_pow p hwk.le).trans hpk_sum)
        by_cases hx0 : x.val = 0
        · rw [hx0, zero_pow (by norm_num), zero_add] at hpw1_sum
          have := (Nat.Prime.pow_dvd_iff_le_factorization hp hm).mp hpw1_sum
          omega
        have hv : w ≤ (x.val ^ 2).factorization p :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp (pow_ne_zero 2 hx0)).mp hpw_x2
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hv
        have hv_strict : w + 1 ≤ 2 * x.val.factorization p := by
          by_contra hlt
          have heq : w = 2 * x.val.factorization p := by omega
          exact hweven ⟨x.val.factorization p, by omega⟩
        have hpw1_x2 : p ^ (w + 1) ∣ x.val ^ 2 := by
          refine (Nat.Prime.pow_dvd_iff_le_factorization hp (pow_ne_zero 2 hx0)).mpr ?_
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
          exact hv_strict
        have hpw1_m : p ^ (w + 1) ∣ m := (Nat.dvd_add_right hpw1_x2).mp hpw1_sum
        have := (Nat.Prime.pow_dvd_iff_le_factorization hp hm).mp hpw1_m
        omega
      rw [hempty]
      simp

end ModularRoots

/-! ## Step 1: Dyadic Factored Integer Proposal -/

section DyadicProposal

private lemma Icc_one_two_pow_nonempty (n : ℕ) : (Finset.Icc 1 (2 ^ n)).Nonempty :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, Nat.one_le_two_pow⟩⟩

/-- Step 1 of the direct sampler: draw uniform `j ∈ {0, ..., J}`, uniform `d ∈ [1, 2^(j+1)]`,
and uniform `e ∈ [1, 2^(J - j)]`, and accept `(d, e)` iff `d` is squarefree, `2^j ≤ d < 2^(j+1)`,
and `d * e ≤ U`. -/
noncomputable def dyadicProposalPMF (J U : ℕ) : PMF (Option ℕ) :=
  (PMF.uniformOfFintype (Fin (J + 1))).bind fun j =>
    (PMF.uniformOfFinset (Finset.Icc 1 (2 ^ (j.val + 1))) (Icc_one_two_pow_nonempty _)).bind fun d =>
      (PMF.uniformOfFinset (Finset.Icc 1 (2 ^ (J - j.val))) (Icc_one_two_pow_nonempty _)).map fun e =>
        if Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e ≤ U then
          some (d * e)
        else
          none

/-- Exact mass of `some A` under Step 1: every `A ∈ [1, U]` has mass
`2^(A.primeFactors.card) / (2 * 2^J * (J + 1))` when `U ≤ 2^J`. -/
theorem dyadicProposalPMF_apply_some {J U A : ℕ} (hA1 : 1 ≤ A) (hAU : A ≤ U) (hUJ : U ≤ 2 ^ J) :
    dyadicProposalPMF J U (some A) =
      ((2 ^ A.primeFactors.card : ℕ) : ENNReal) / ((2 * 2 ^ J * (J + 1) : ℕ) : ENNReal) := by
  classical
  unfold dyadicProposalPMF
  simp only [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    PMF.uniformOfFinset_apply, Fintype.card_fin]
  rw [tsum_fintype]
  have hterm : ∀ j : Fin (J + 1),
      ((J + 1 : ℕ) : ENNReal)⁻¹ *
        ∑' d, (if d ∈ Finset.Icc 1 (2 ^ (j.val + 1))
          then ((Finset.Icc 1 (2 ^ (j.val + 1))).card : ENNReal)⁻¹ else 0) *
          ∑' e, (if some A = (if Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e ≤ U
            then some (d * e) else none) then
            (if e ∈ Finset.Icc 1 (2 ^ (J - j.val))
              then ((Finset.Icc 1 (2 ^ (J - j.val))).card : ENNReal)⁻¹ else 0) else 0) =
      (((Finset.Icc 1 (2 ^ (j.val + 1))).filter
        (fun d => Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d ∣ A)).card : ENNReal) /
        ((2 * 2 ^ J * (J + 1) : ℕ) : ENNReal) := by
    intro j
    have hcard1 : (Finset.Icc 1 (2 ^ (j.val + 1))).card = 2 ^ (j.val + 1) := by
      simp [Nat.card_Icc]
    have hcard2 : (Finset.Icc 1 (2 ^ (J - j.val))).card = 2 ^ (J - j.val) := by
      simp [Nat.card_Icc]
    have hd_sum :
        (∑' d, (if d ∈ Finset.Icc 1 (2 ^ (j.val + 1))
          then ((Finset.Icc 1 (2 ^ (j.val + 1))).card : ENNReal)⁻¹ else 0) *
          ∑' e, (if some A = (if Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e ≤ U
            then some (d * e) else none) then
            (if e ∈ Finset.Icc 1 (2 ^ (J - j.val))
              then ((Finset.Icc 1 (2 ^ (J - j.val))).card : ENNReal)⁻¹ else 0) else 0)) =
        ∑ d ∈ Finset.Icc 1 (2 ^ (j.val + 1)),
          ((2 ^ (j.val + 1) : ℕ) : ENNReal)⁻¹ *
            if Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d ∣ A then
              ((2 ^ (J - j.val) : ℕ) : ENNReal)⁻¹
            else 0 := by
      rw [tsum_eq_sum (s := Finset.Icc 1 (2 ^ (j.val + 1))) (fun d hd => by simp [hd])]
      apply Finset.sum_congr rfl
      intro d hd
      rw [if_pos hd, hcard1]
      congr 1
      have he_eq :
          (∑' e, (if some A = (if Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e ≤ U
            then some (d * e) else none) then
            (if e ∈ Finset.Icc 1 (2 ^ (J - j.val))
              then ((Finset.Icc 1 (2 ^ (J - j.val))).card : ENNReal)⁻¹ else 0) else 0)) =
          ∑ e ∈ Finset.Icc 1 (2 ^ (J - j.val)),
            if Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e = A then
              ((2 ^ (J - j.val) : ℕ) : ENNReal)⁻¹
            else 0 := by
        rw [tsum_eq_sum (s := Finset.Icc 1 (2 ^ (J - j.val))) (fun e he => by
          split_ifs <;> simp [he])]
        apply Finset.sum_congr rfl
        intro e he
        rw [if_pos he, hcard2]
        by_cases hc : Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e = A
        · have hleU : d * e ≤ U := hc.2.2.2 ▸ hAU
          have hc' : Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e ≤ U :=
            ⟨hc.1, hc.2.1, hc.2.2.1, hleU⟩
          rw [if_pos hc, if_pos hc', if_pos (congrArg some hc.2.2.2.symm)]
        · rw [if_neg hc]
          by_cases h1 : Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e ≤ U
          · rw [if_pos h1]
            have hne : ¬ (some A = some (d * e)) := fun h2 =>
              hc ⟨h1.1, h1.2.1, h1.2.2.1, (Option.some.inj h2).symm⟩
            rw [if_neg hne]
          · rw [if_neg h1]
            exact if_neg (Option.some_ne_none A)
      rw [he_eq]
      by_cases hcond : Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d ∣ A
      · rw [if_pos hcond]
        have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
        have hquot_mem : A / d ∈ Finset.Icc 1 (2 ^ (J - j.val)) := by
          rw [Finset.mem_Icc]
          have hdleA : d ≤ A := Nat.le_of_dvd (by omega) hcond.2.2.2
          have hpow : 2 ^ j.val * 2 ^ (J - j.val) = 2 ^ J := by
            rw [← pow_add, show j.val + (J - j.val) = J by omega]
          have hqle : A / d ≤ 2 ^ (J - j.val) := by
            rw [Nat.div_le_iff_le_mul_add_pred hdpos]
            have h1 : A ≤ 2 ^ J := hAU.trans hUJ
            have h2 : 2 ^ J ≤ d * 2 ^ (J - j.val) := by
              rw [← hpow]
              exact Nat.mul_le_mul_right _ hcond.2.1
            omega
          exact ⟨Nat.div_pos hdleA hdpos, hqle⟩
        rw [Finset.sum_eq_single (A / d)]
        · rw [if_pos ⟨hcond.1, hcond.2.1, hcond.2.2.1, Nat.mul_div_cancel' hcond.2.2.2⟩]
        · intro e _ hne
          rw [if_neg]
          intro h
          apply hne
          rw [← h.2.2.2, Nat.mul_div_cancel_left e hdpos]
        · intro hnot
          exact (hnot hquot_mem).elim
      · rw [if_neg hcond]
        apply Finset.sum_eq_zero
        intro e _
        rw [if_neg]
        intro h
        exact hcond ⟨h.1, h.2.1, h.2.2.1, ⟨e, h.2.2.2.symm⟩⟩
    rw [hd_sum, Finset.mul_sum]
    have hmass : ((J + 1 : ℕ) : ENNReal)⁻¹ *
        (((2 ^ (j.val + 1) : ℕ) : ENNReal)⁻¹ * ((2 ^ (J - j.val) : ℕ) : ENNReal)⁻¹) =
        ((2 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ := by
      have hpow : 2 ^ (j.val + 1) * 2 ^ (J - j.val) = 2 * 2 ^ J := by
        rw [← pow_add, show j.val + 1 + (J - j.val) = J + 1 by omega, pow_succ']
      rw [← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inr (by simp)),
        ← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inr (by simp))]
      congr 1
      norm_cast
      rw [hpow, mul_comm]
    calc
      (∑ d ∈ Finset.Icc 1 (2 ^ (j.val + 1)),
          ((J + 1 : ℕ) : ENNReal)⁻¹ *
            (((2 ^ (j.val + 1) : ℕ) : ENNReal)⁻¹ *
              if Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d ∣ A then
                ((2 ^ (J - j.val) : ℕ) : ENNReal)⁻¹
              else 0))
        = ∑ d ∈ (Finset.Icc 1 (2 ^ (j.val + 1))).filter
            (fun d => Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d ∣ A),
            ((2 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro d _
          split_ifs with hc
          · rw [← mul_assoc, mul_assoc ((J + 1 : ℕ) : ENNReal)⁻¹, hmass]
          · simp
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  refine (Finset.sum_congr (g := fun j : Fin (J + 1) =>
      (((Finset.Icc 1 (2 ^ (j.val + 1))).filter
        (fun d => Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d ∣ A)).card : ENNReal) /
        ((2 * 2 ^ J * (J + 1) : ℕ) : ENNReal)) rfl fun j _ => ?_).trans ?_
  · convert hterm j
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  -- The filtered sets across `j : Fin (J + 1)` partition `A.divisors.filter Squarefree`.
  have hpart : (∑ j : Fin (J + 1),
      ((Finset.Icc 1 (2 ^ (j.val + 1))).filter
        (fun d => Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d ∣ A)).card) =
      (A.divisors.filter Squarefree).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext d
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
        Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨j, ⟨⟨_, _⟩, hsq, _, _, hdA⟩⟩
        exact ⟨⟨hdA, by omega⟩, hsq⟩
      · rintro ⟨⟨hdA, _⟩, hsq⟩
        have hAtop : A < 2 ^ (J + 1) := by
          have : A ≤ 2 ^ J := hAU.trans hUJ
          have hpos : 0 < 2 ^ J := by positivity
          rw [pow_succ']
          omega
        obtain ⟨j, ⟨hjle, hjlo, hjhi, _, _⟩, _⟩ := unique_divisor_bucket (by omega) hAtop hdA
        have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdA (by omega)
        exact ⟨⟨j, Nat.lt_succ_of_le hjle⟩, ⟨hdpos, hjhi.le⟩, hsq, hjlo, hjhi, hdA⟩
    · intro j₁ _ j₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro d hd₁ hd₂
      simp only [Finset.mem_filter] at hd₁ hd₂
      have hlog₁ := Nat.log_eq_of_pow_le_of_lt_pow hd₁.2.2.1 hd₁.2.2.2.1
      have hlog₂ := Nat.log_eq_of_pow_le_of_lt_pow hd₂.2.2.1 hd₂.2.2.2.1
      exact hne (Fin.ext (hlog₁.symm.trans hlog₂))
  have hsqcount := squarefree_divisor_count (t := A) (by omega)
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors] at hsqcount
  exact_mod_cast (hpart.trans hsqcount)

theorem dyadicProposalPMF_apply_some_toReal {J U A : ℕ} (hA1 : 1 ≤ A) (hAU : A ≤ U)
    (hUJ : U ≤ 2 ^ J) :
    (dyadicProposalPMF J U (some A)).toReal =
      (2 : ℝ) ^ A.primeFactors.card / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) := by
  rw [dyadicProposalPMF_apply_some hA1 hAU hUJ, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  push_cast
  rfl

theorem dyadicProposalPMF_apply_some_zero_of_not_Icc {J U A : ℕ}
    (hA : A ∉ Finset.Icc 1 U) :
    dyadicProposalPMF J U (some A) = 0 := by
  classical
  unfold dyadicProposalPMF
  simp only [PMF.bind_apply, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro j
  apply mul_eq_zero_of_right
  apply ENNReal.tsum_eq_zero.mpr
  intro d
  by_cases hd : d ∈ Finset.Icc 1 (2 ^ (j.val + 1))
  · apply mul_eq_zero_of_right
    apply ENNReal.tsum_eq_zero.mpr
    intro e
    by_cases he : e ∈ Finset.Icc 1 (2 ^ (J - j.val))
    · by_cases h1 : Squarefree d ∧ 2 ^ j.val ≤ d ∧ d < 2 ^ (j.val + 1) ∧ d * e ≤ U
      · rw [if_pos h1, if_neg]
        intro h2
        have hde : d * e = A := (Option.some.inj h2).symm
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
        have hA1 : 1 ≤ A := hde ▸ Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
        exact hA (Finset.mem_Icc.mpr ⟨hA1, hde ▸ h1.2.2.2⟩)
      · rw [if_neg h1, if_neg (Option.some_ne_none A)]
    · simp [PMF.uniformOfFinset_apply, he]
  · simp [PMF.uniformOfFinset_apply, hd]

theorem dyadicProposalPMF_apply_some_eq_zero_of_not_mem {J U A : ℕ}
    (hA : A = 0 ∨ U < A) :
    dyadicProposalPMF J U (some A) = 0 := by
  apply dyadicProposalPMF_apply_some_zero_of_not_Icc
  intro hmem
  rcases Finset.mem_Icc.mp hmem with ⟨h1, h2⟩
  omega

end DyadicProposal

/-! ## Steps 2 & 3: Direct Equal-Weight Reduced-Class Proposal -/

section DirectProposal

/-- Clean parameterized interface for canonical primitive reduced forms of discriminant `-4m`,
decoupled from any particular form representation so Wave 2 can instantiate it directly. -/
structure DirectFormSpec (Form : Type*) [DecidableEq Form] where
  /-- Modulus `N` to be factored. -/
  N : ℕ
  /-- Upper bound `U` on leading coefficients of canonical reduced forms. -/
  U : ℕ
  /-- Canonical integer representatives `b` of roots of `b^2 ≡ -m (mod A)`. -/
  roots : ℕ → Finset ℤ
  /-- Coprime root-count bound `R(A) ≤ 2^(ω(A) + 1)`. -/
  roots_card_le : ∀ A, 1 ≤ A → A ≤ U → Nat.Coprime A N →
    (roots A).card ≤ 2 ^ (A.primeFactors.card + 1)
  /-- Form constructor & canonicality/primitivity filter from `(A, b)`. -/
  buildForm : ℕ → ℤ → Option Form
  /-- Finite set of all canonical primitive reduced forms. -/
  allForms : Finset Form
  /-- Leading coefficient `A` of a form. -/
  leadCoeff : Form → ℕ
  /-- Canonical middle half-coefficient `b` of a form. -/
  midCoeff : Form → ℤ
  /-- Every canonical form has `1 ≤ A ≤ U`. -/
  leadCoeff_pos : ∀ f ∈ allForms, 1 ≤ leadCoeff f
  leadCoeff_le : ∀ f ∈ allForms, leadCoeff f ≤ U
  /-- Every canonical form's middle coefficient is a modular root mod `A`. -/
  midCoeff_mem_roots : ∀ f ∈ allForms, midCoeff f ∈ roots (leadCoeff f)
  /-- A canonical form is uniquely determined by `(leadCoeff f, midCoeff f)`. -/
  coeff_injective : Set.InjOn (fun f => (leadCoeff f, midCoeff f)) (allForms : Set Form)
  /-- Exact characterization of accepted coprime `(A, b)` pairs. -/
  buildForm_eq_some_iff : ∀ A b f, 1 ≤ A → A ≤ U → Nat.Coprime A N → b ∈ roots A →
    (buildForm A b = some f ↔ f ∈ allForms ∧ leadCoeff f = A ∧ midCoeff f = b)

/-- The canonical primitive reduced forms whose leading coefficient is coprime to `N`. -/
def DirectFormSpec.coprimeForms {Form : Type*} [DecidableEq Form] (spec : DirectFormSpec Form) :
    Finset Form :=
  spec.allForms.filter (fun f => Nat.Coprime (spec.leadCoeff f) spec.N)

/-- The omitted canonical primitive reduced forms whose leading coefficient shares a factor with `N`. -/
def DirectFormSpec.omittedForms {Form : Type*} [DecidableEq Form] (spec : DirectFormSpec Form) :
    Finset Form :=
  spec.allForms.filter (fun f => ¬ Nat.Coprime (spec.leadCoeff f) spec.N)

/-- Outcome of one attempt of the direct sampler, separating accepted forms, gcd exits,
and rejections. -/
inductive DirectProposalOutcome (Form : Type*)
  | accepted (f : Form)
  | gcdExit (g : ℕ)
  | rejected
  deriving DecidableEq

/-- Forget gcd exits to view one attempt as an `Option Form` proposal. -/
def DirectProposalOutcome.toOption {Form : Type*} : DirectProposalOutcome Form → Option Form
  | .accepted f => some f
  | .gcdExit _ => none
  | .rejected => none

private lemma rootAcceptProb_le_one {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {A : ℕ} (hA1 : 1 ≤ A) (hAU : A ≤ spec.U)
    (hcop : Nat.Coprime A spec.N) :
    ((spec.roots A).card : NNReal) / ((2 ^ (A.primeFactors.card + 1) : ℕ) : NNReal) ≤ 1 := by
  have hpos : (0 : NNReal) < ((2 ^ (A.primeFactors.card + 1) : ℕ) : NNReal) := by positivity
  rw [div_le_one hpos]
  exact_mod_cast spec.roots_card_le A hA1 hAU hcop

/-- Step 3 for a fixed coprime leading coefficient `A ∈ [1, U]`:
accept with probability `R(A) / 2^(ω(A) + 1)`, sample a uniform root `b ∈ roots A`,
and keep canonical primitive reduced forms. -/
noncomputable def rootStepPMF {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (A : ℕ) (hA1 : 1 ≤ A) (hAU : A ≤ spec.U)
    (hcop : Nat.Coprime A spec.N) : PMF (DirectProposalOutcome Form) :=
  if hR : (spec.roots A).Nonempty then
    (PMF.bernoulli
      (((spec.roots A).card : NNReal) / ((2 ^ (A.primeFactors.card + 1) : ℕ) : NNReal))
      (rootAcceptProb_le_one spec hA1 hAU hcop)).bind fun ok =>
      if ok then
        (PMF.uniformOfFinset (spec.roots A) hR).map fun b =>
          match spec.buildForm A b with
          | some f => DirectProposalOutcome.accepted f
          | none => DirectProposalOutcome.rejected
      else
        PMF.pure DirectProposalOutcome.rejected
  else
    PMF.pure DirectProposalOutcome.rejected

/-- Full 3-step direct sampler attempt returning `DirectProposalOutcome Form`. -/
noncomputable def directProposalOutcomePMF {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (J : ℕ) : PMF (DirectProposalOutcome Form) :=
  (dyadicProposalPMF J spec.U).bind fun oA =>
    match oA with
    | none => PMF.pure DirectProposalOutcome.rejected
    | some A =>
      if hrange : 1 ≤ A ∧ A ≤ spec.U then
        if hcop : Nat.Coprime A spec.N then
          rootStepPMF spec A hrange.1 hrange.2 hcop
        else
          PMF.pure (DirectProposalOutcome.gcdExit (Nat.gcd A spec.N))
      else
        PMF.pure DirectProposalOutcome.rejected

/-- Full 3-step direct sampler attempt on `Option Form`. -/
noncomputable def directProposalPMF {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (J : ℕ) : PMF (Option Form) :=
  (directProposalOutcomePMF spec J).map DirectProposalOutcome.toOption

/-- Any gcd exit returned with positive probability yields a verified proper divisor of `N`
when `U < N`. -/
theorem directProposalOutcomePMF_gcdExit_proper_divisor {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (J g : ℕ) (hUN : spec.U < spec.N)
    (hpos : directProposalOutcomePMF spec J (.gcdExit g) ≠ 0) :
    1 < g ∧ g ∣ spec.N ∧ g < spec.N := by
  unfold directProposalOutcomePMF at hpos
  rw [PMF.bind_apply] at hpos
  have hex : ∃ oA, dyadicProposalPMF J spec.U oA *
      (match oA with
        | none => PMF.pure DirectProposalOutcome.rejected
        | some A =>
          if hrange : 1 ≤ A ∧ A ≤ spec.U then
            if hcop : Nat.Coprime A spec.N then
              rootStepPMF spec A hrange.1 hrange.2 hcop
            else
              PMF.pure (DirectProposalOutcome.gcdExit (Nat.gcd A spec.N))
          else
            PMF.pure DirectProposalOutcome.rejected) (.gcdExit g) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hpos (ENNReal.tsum_eq_zero.mpr hall)
  obtain ⟨oA, hoA⟩ := hex
  cases oA with
  | none =>
    simp [PMF.pure_apply] at hoA
  | some A =>
    dsimp only at hoA
    split_ifs at hoA with hrange hcop
    · exfalso
      have hroot0 : rootStepPMF spec A hrange.1 hrange.2 hcop (.gcdExit g) = 0 := by
        unfold rootStepPMF
        split_ifs with hR
        · rw [PMF.bind_apply]
          apply ENNReal.tsum_eq_zero.mpr
          intro ok
          cases ok with
          | false => simp [PMF.pure_apply]
          | true =>
            apply mul_eq_zero_of_right
            rw [if_pos rfl, PMF.map_apply]
            apply ENNReal.tsum_eq_zero.mpr
            intro b
            cases spec.buildForm A b <;> simp
        · simp [PMF.pure_apply]
      simp [hroot0] at hoA
    · have hg_eq : g = Nat.gcd A spec.N := by
        have hne : PMF.pure (DirectProposalOutcome.gcdExit (Nat.gcd A spec.N)) (.gcdExit g) ≠ 0 :=
          right_ne_zero_of_mul hoA
        rw [PMF.pure_apply] at hne
        split_ifs at hne with h
        · exact DirectProposalOutcome.gcdExit.inj h
        · exact (hne rfl).elim
      subst hg_eq
      have hne1 : Nat.gcd A spec.N ≠ 1 := hcop
      have hpos_g : 0 < Nat.gcd A spec.N := Nat.gcd_pos_of_pos_left spec.N (by omega)
      have hleA : Nat.gcd A spec.N ≤ A := Nat.gcd_le_left spec.N (by omega)
      exact ⟨by omega, Nat.gcd_dvd_right A spec.N, hleA.trans_lt (hrange.2.trans_lt hUN)⟩
    · simp [PMF.pure_apply] at hoA

/-- Conditional probability of accepting a specific form `f` in Step 3 given `A`. -/
theorem rootStepPMF_accepted {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {A : ℕ} (hA1 : 1 ≤ A) (hAU : A ≤ spec.U)
    (hcop : Nat.Coprime A spec.N) (f : Form) :
    rootStepPMF spec A hA1 hAU hcop (.accepted f) =
      if f ∈ spec.allForms ∧ spec.leadCoeff f = A then
        ((2 ^ (A.primeFactors.card + 1) : ℕ) : ENNReal)⁻¹
      else 0 := by
  classical
  unfold rootStepPMF
  split_ifs with hR hcond hcond
  · rw [PMF.bind_apply, tsum_bool]
    simp only [PMF.bernoulli_apply, cond_true, cond_false, PMF.pure_apply,
      reduceCtorEq, ↓reduceIte, mul_zero, add_zero, zero_add]
    rw [PMF.map_apply]
    have hb_mem : spec.midCoeff f ∈ spec.roots A := by
      rw [← hcond.2]
      exact spec.midCoeff_mem_roots f hcond.1
    rw [show (∑' b : ℤ, _) = ((spec.roots A).card : ENNReal)⁻¹ from ?htsum]
    case htsum =>
      rw [tsum_eq_single (spec.midCoeff f)]
      · have hbuild : spec.buildForm A (spec.midCoeff f) = some f :=
          (spec.buildForm_eq_some_iff A (spec.midCoeff f) f hA1 hAU hcop hb_mem).mpr
            ⟨hcond.1, hcond.2, rfl⟩
        rw [hbuild, if_pos rfl, PMF.uniformOfFinset_apply, if_pos hb_mem]
      · intro b hne
        by_cases hb : b ∈ spec.roots A
        · split_ifs with hEq
          · exfalso
            cases hbf : spec.buildForm A b with
            | none => rw [hbf] at hEq; simp at hEq
            | some f' =>
              rw [hbf] at hEq
              have hff' : f = f' := DirectProposalOutcome.accepted.inj hEq
              subst hff'
              have hspec := (spec.buildForm_eq_some_iff A b f hA1 hAU hcop hb).mp hbf
              exact hne hspec.2.2.symm
          · rfl
        · simp [PMF.uniformOfFinset_apply, hb]
    have hMne : ((2 ^ (A.primeFactors.card + 1) : ℕ) : NNReal) ≠ 0 := by positivity
    have hRne : ((spec.roots A).card : ENNReal) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hR).ne'
    have hRtop : ((spec.roots A).card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [ENNReal.coe_div hMne, ENNReal.coe_natCast, ENNReal.coe_natCast,
      div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel hRne hRtop, one_mul]
  · rw [PMF.bind_apply, tsum_bool]
    simp only [PMF.pure_apply, reduceCtorEq, ↓reduceIte, mul_zero, add_zero, zero_add]
    apply mul_eq_zero_of_right
    rw [PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    by_cases hb : b ∈ spec.roots A
    · split_ifs with hEq
      · exfalso
        cases hbf : spec.buildForm A b with
        | none => rw [hbf] at hEq; simp at hEq
        | some f' =>
          rw [hbf] at hEq
          have hff' : f = f' := DirectProposalOutcome.accepted.inj hEq
          subst hff'
          have hspec := (spec.buildForm_eq_some_iff A b f hA1 hAU hcop hb).mp hbf
          exact hcond ⟨hspec.1, hspec.2.1⟩
      · rfl
    · simp [PMF.uniformOfFinset_apply, hb]
  · exfalso
    have hb_mem : spec.midCoeff f ∈ spec.roots A := by
      rw [← hcond.2]
      exact spec.midCoeff_mem_roots f hcond.1
    exact hR ⟨spec.midCoeff f, hb_mem⟩
  · simp [PMF.pure_apply]

/-- **EXACT EQUAL-WEIGHT THEOREM** (outcome form): every coprime canonical primitive reduced form
has exact unconditional probability `1 / (4 * 2^J * (J + 1))`, and non-coprime or non-canonical
forms have probability `0`. -/
theorem directProposalOutcomePMF_accepted {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J : ℕ} (hUJ : spec.U ≤ 2 ^ J) (f : Form) :
    directProposalOutcomePMF spec J (.accepted f) =
      if f ∈ spec.coprimeForms then
        ((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹
      else 0 := by
  classical
  unfold directProposalOutcomePMF
  rw [PMF.bind_apply]
  by_cases hf : f ∈ spec.coprimeForms
  · rw [if_pos hf]
    have hfall : f ∈ spec.allForms := (Finset.mem_filter.mp hf).1
    have hfcop : Nat.Coprime (spec.leadCoeff f) spec.N := (Finset.mem_filter.mp hf).2
    have hf1 : 1 ≤ spec.leadCoeff f := spec.leadCoeff_pos f hfall
    have hfU : spec.leadCoeff f ≤ spec.U := spec.leadCoeff_le f hfall
    rw [tsum_eq_single (some (spec.leadCoeff f))]
    · dsimp only
      rw [dif_pos ⟨hf1, hfU⟩, dif_pos hfcop, rootStepPMF_accepted,
        if_pos ⟨hfall, rfl⟩, dyadicProposalPMF_apply_some hf1 hfU hUJ]
      set k := (spec.leadCoeff f).primeFactors.card
      have h2k_ne : ((2 ^ k : ℕ) : ENNReal) ≠ 0 := by positivity
      have h2k_top : ((2 ^ k : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hpow : ((2 ^ (k + 1) : ℕ) : ENNReal) = 2 * ((2 ^ k : ℕ) : ENNReal) := by
        rw [pow_succ']
        push_cast
        rfl
      rw [hpow, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inr h2k_ne), div_eq_mul_inv]
      have hcancel : ((2 ^ k : ℕ) : ENNReal) * ((2 ^ k : ℕ) : ENNReal)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel h2k_ne h2k_top
      have hY : ((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ =
          (2 : ENNReal)⁻¹ * ((2 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        congr 1
        push_cast
        ring
      rw [hY]
      calc
        _ = (((2 ^ k : ℕ) : ENNReal) * ((2 ^ k : ℕ) : ENNReal)⁻¹) *
            ((2 : ENNReal)⁻¹ * ((2 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹) := by ring
        _ = _ := by rw [hcancel, one_mul]
    · intro oA hne
      cases oA with
      | none => simp [PMF.pure_apply]
      | some A =>
        have hAne : A ≠ spec.leadCoeff f := fun h => hne (congrArg some h)
        dsimp only
        split_ifs with hrange hcop
        · rw [rootStepPMF_accepted, if_neg (fun h => hAne h.2.symm), mul_zero]
        · simp [PMF.pure_apply]
        · simp [PMF.pure_apply]
  · rw [if_neg hf]
    apply ENNReal.tsum_eq_zero.mpr
    intro oA
    cases oA with
    | none => simp [PMF.pure_apply]
    | some A =>
      dsimp only
      split_ifs with hrange hcop
      · rw [rootStepPMF_accepted, if_neg, mul_zero]
        rintro ⟨hfall, hAeq⟩
        exact hf (Finset.mem_filter.mpr ⟨hfall, hAeq.symm ▸ hcop⟩)
      · simp [PMF.pure_apply]
      · simp [PMF.pure_apply]

/-- **EXACT EQUAL-WEIGHT THEOREM** (`Option Form` form): every coprime canonical primitive
reduced form has exact unconditional mass `1 / (4 * 2^J * (J + 1))`. -/
theorem directProposalPMF_some {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J : ℕ} (hUJ : spec.U ≤ 2 ^ J) (f : Form) :
    directProposalPMF spec J (some f) =
      if f ∈ spec.coprimeForms then
        ((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹
      else 0 := by
  unfold directProposalPMF
  rw [PMF.map_apply, tsum_eq_single (DirectProposalOutcome.accepted f)]
  · rw [if_pos (show some f = (DirectProposalOutcome.accepted f).toOption from rfl)]
    exact directProposalOutcomePMF_accepted spec hUJ f
  · intro o hne
    cases o with
    | accepted f' =>
      have hff' : f ≠ f' := fun h => hne (congrArg DirectProposalOutcome.accepted h.symm)
      simp [DirectProposalOutcome.toOption, hff']
    | gcdExit g => simp [DirectProposalOutcome.toOption]
    | rejected => simp [DirectProposalOutcome.toOption]

theorem directProposalPMF_some_toReal {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J : ℕ} (hUJ : spec.U ≤ 2 ^ J)
    {f : Form} (hf : f ∈ spec.coprimeForms) :
    (directProposalPMF spec J (some f)).toReal =
      1 / (4 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) := by
  rw [directProposalPMF_some spec hUJ f, if_pos hf, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    one_div]
  push_cast
  rfl

end DirectProposal

/-! ## Sequential Retry Invariance -/

section SequentialRetry

/-- Repeat independent attempts of `step` up to `J₀` times, stopping on the first accepted form
or gcd exit (continuing only on `rejected`). -/
noncomputable def retryOutcomePMF {Form : Type*}
    (step : PMF (DirectProposalOutcome Form)) : ℕ → PMF (DirectProposalOutcome Form)
  | 0 => PMF.pure DirectProposalOutcome.rejected
  | k + 1 =>
    step.bind fun o =>
      match o with
      | .rejected => retryOutcomePMF step k
      | .accepted f => PMF.pure (.accepted f)
      | .gcdExit g => PMF.pure (.gcdExit g)

/-- Exact formula for returning an accepted form under `J₀` independent attempts stopping on
the first accepted form or gcd exit. -/
theorem retryOutcomePMF_accepted {Form : Type*} [DecidableEq Form]
    (step : PMF (DirectProposalOutcome Form)) (J₀ : ℕ) (f : Form) :
    retryOutcomePMF step J₀ (.accepted f) =
      step (.accepted f) * ∑ k ∈ Finset.range J₀, (step .rejected) ^ k := by
  induction J₀ with
  | zero =>
    simp [retryOutcomePMF, PMF.pure_apply]
  | succ n ih =>
    unfold retryOutcomePMF
    rw [PMF.bind_apply]
    have hsplit : (∑' o, step o *
        (match o with
          | .rejected => retryOutcomePMF step n
          | .accepted f' => PMF.pure (.accepted f')
          | .gcdExit g => PMF.pure (.gcdExit g)) (.accepted f)) =
        step (.accepted f) + step .rejected * retryOutcomePMF step n (.accepted f) := by
      have hfin : ∀ o, o ∉ ({DirectProposalOutcome.accepted f, DirectProposalOutcome.rejected} :
          Finset (DirectProposalOutcome Form)) →
          step o * (match o with
            | .rejected => retryOutcomePMF step n
            | .accepted f' => PMF.pure (.accepted f')
            | .gcdExit g => PMF.pure (.gcdExit g)) (.accepted f) = 0 := by
        intro o ho
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ho
        cases o with
        | accepted f' =>
          have hne : f ≠ f' := fun h => ho.1 (congrArg DirectProposalOutcome.accepted h.symm)
          simp [PMF.pure_apply, hne]
        | gcdExit g => simp [PMF.pure_apply]
        | rejected => exact (ho.2 rfl).elim
      rw [tsum_eq_sum hfin]
      rw [Finset.sum_pair (by simp)]
      simp [PMF.pure_apply]
    rw [hsplit, ih, Finset.sum_range_succ']
    simp only [pow_succ, ← Finset.sum_mul]
    ring

/-- Repeat independent attempts of an `Option Form` proposal up to `J₀` times, stopping on the
first `some f`. -/
noncomputable def retryOptionPMF {Form : Type*}
    (step : PMF (Option Form)) : ℕ → PMF (Option Form)
  | 0 => PMF.pure none
  | k + 1 =>
    step.bind fun o =>
      match o with
      | none => retryOptionPMF step k
      | some f => PMF.pure (some f)

/-- Exact formula for returning `some f` under `J₀` independent attempts of an `Option Form`
proposal. -/
theorem retryOptionPMF_some {Form : Type*} [DecidableEq Form]
    (step : PMF (Option Form)) (J₀ : ℕ) (f : Form) :
    retryOptionPMF step J₀ (some f) =
      step (some f) * ∑ k ∈ Finset.range J₀, (step none) ^ k := by
  induction J₀ with
  | zero =>
    simp [retryOptionPMF, PMF.pure_apply]
  | succ n ih =>
    unfold retryOptionPMF
    rw [PMF.bind_apply]
    have hfin : ∀ o, o ∉ ({some f, none} : Finset (Option Form)) →
        step o * (match o with
          | none => retryOptionPMF step n
          | some f' => PMF.pure (some f')) (some f) = 0 := by
      intro o ho
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ho
      cases o with
      | none => exact (ho.2 rfl).elim
      | some f' =>
        have hne : f ≠ f' := fun h => ho.1 (congrArg some h.symm)
        simp [PMF.pure_apply, hne]
    rw [tsum_eq_sum hfin, Finset.sum_pair (Option.some_ne_none f)]
    simp only [PMF.pure_apply, ↓reduceIte, mul_one, ih]
    rw [Finset.sum_range_succ']
    simp only [pow_succ, ← Finset.sum_mul]
    ring

/-- **EQUAL-WEIGHT RETRY PROBABILITY**: for any deterministic cap `J₀`, every coprime canonical
form has identical probability `(1 / (4 * 2^J * (J + 1))) * ∑_{k < J₀} r^k` where `r` is the
continuation probability `directProposalOutcomePMF spec J .rejected`. -/
theorem directRetryOutcomePMF_accepted_toReal {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ} (hUJ : spec.U ≤ 2 ^ J)
    {f : Form} (hf : f ∈ spec.coprimeForms) :
    (retryOutcomePMF (directProposalOutcomePMF spec J) J₀ (.accepted f)).toReal =
      (1 / (4 * (2 : ℝ) ^ J * ((J : ℝ) + 1))) *
        ∑ k ∈ Finset.range J₀, ((directProposalOutcomePMF spec J .rejected).toReal) ^ k := by
  rw [retryOutcomePMF_accepted, directProposalOutcomePMF_accepted spec hUJ f, if_pos hf]
  have hr_ne_top : directProposalOutcomePMF spec J .rejected ≠ ⊤ := PMF.apply_ne_top _ _
  have hsum_ne_top : (∑ k ∈ Finset.range J₀, (directProposalOutcomePMF spec J .rejected) ^ k) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun k _ => ENNReal.pow_ne_top hr_ne_top)
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div,
    ENNReal.toReal_sum (fun k _ => ENNReal.pow_ne_top hr_ne_top)]
  simp only [ENNReal.toReal_pow]
  push_cast
  rfl

/-- Total probability that `retryOutcomePMF` returns some accepted form. -/
noncomputable def retryAcceptedMass {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (J J₀ : ℕ) : ENNReal :=
  ∑ f ∈ spec.coprimeForms, retryOutcomePMF (directProposalOutcomePMF spec J) J₀ (.accepted f)

theorem retryAcceptedMass_eq {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ} (hUJ : spec.U ≤ 2 ^ J) :
    retryAcceptedMass spec J J₀ =
      (spec.coprimeForms.card : ENNReal) *
        (((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
          ∑ k ∈ Finset.range J₀, (directProposalOutcomePMF spec J .rejected) ^ k) := by
  unfold retryAcceptedMass
  have hcongr : ∀ f ∈ spec.coprimeForms,
      retryOutcomePMF (directProposalOutcomePMF spec J) J₀ (.accepted f) =
        ((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
          ∑ k ∈ Finset.range J₀, (directProposalOutcomePMF spec J .rejected) ^ k := by
    intro f hf
    rw [retryOutcomePMF_accepted, directProposalOutcomePMF_accepted spec hUJ f, if_pos hf]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]

/-- Conditional distribution on `Form` given that `retryOutcomePMF` returns an accepted form. -/
noncomputable def directRetryConditionalPMF {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ} (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) : PMF Form :=
  ⟨fun f => retryOutcomePMF (directProposalOutcomePMF spec J) J₀ (.accepted f) /
      retryAcceptedMass spec J J₀, by
    have hfactor_ne0 :
        (((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
          ∑ k ∈ Finset.range J₀, (directProposalOutcomePMF spec J .rejected) ^ k) ≠ 0 := by
      apply mul_ne_zero
      · exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
      · have h0mem : 0 ∈ Finset.range J₀ := Finset.mem_range.mpr (by omega)
        have hge : (1 : ENNReal) ≤ ∑ k ∈ Finset.range J₀,
            (directProposalOutcomePMF spec J .rejected) ^ k := by
          calc
            (1 : ENNReal) = (directProposalOutcomePMF spec J .rejected) ^ 0 := (pow_zero _).symm
            _ ≤ ∑ k ∈ Finset.range J₀, (directProposalOutcomePMF spec J .rejected) ^ k :=
                Finset.single_le_sum (fun _ _ => zero_le) h0mem
        exact (lt_of_lt_of_le zero_lt_one hge).ne'
    have hfactor_top :
        (((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
          ∑ k ∈ Finset.range J₀, (directProposalOutcomePMF spec J .rejected) ^ k) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr (by positivity)
      · exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.pow_ne_top (PMF.apply_ne_top _ _))
    have hmass_ne0 : retryAcceptedMass spec J J₀ ≠ 0 := by
      rw [retryAcceptedMass_eq spec hUJ]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hcop).ne') hfactor_ne0
    have hmass_top : retryAcceptedMass spec J J₀ ≠ ⊤ := by
      rw [retryAcceptedMass_eq spec hUJ]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfactor_top
    have hsupp : ∀ f ∉ spec.coprimeForms,
        retryOutcomePMF (directProposalOutcomePMF spec J) J₀ (.accepted f) /
          retryAcceptedMass spec J J₀ = 0 := by
      intro f hf
      rw [retryOutcomePMF_accepted, directProposalOutcomePMF_accepted spec hUJ f, if_neg hf,
        zero_mul, ENNReal.zero_div]
    have hs : HasSum (fun f => retryOutcomePMF (directProposalOutcomePMF spec J) J₀ (.accepted f) /
        retryAcceptedMass spec J J₀) 1 := by
      have hsum_eq : (∑ f ∈ spec.coprimeForms,
          retryOutcomePMF (directProposalOutcomePMF spec J) J₀ (.accepted f) /
            retryAcceptedMass spec J J₀) = 1 := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        rw [← div_eq_mul_inv]
        exact ENNReal.div_self hmass_ne0 hmass_top
      rw [← hsum_eq]
      exact hasSum_sum_of_ne_finset_zero hsupp
    exact hs⟩

/-- **SEQUENTIAL RETRY INVARIANCE**: conditional on returning a form, `J₀ ≥ 1` independent
attempts of the direct sampler (stopping on the first accepted form or gcd exit) have the
**EXACT UNIFORM** distribution on `spec.coprimeForms`. -/
theorem directRetryConditionalPMF_eq_uniform {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ} (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) :
    directRetryConditionalPMF spec hUJ hJ₀ hcop =
      PMF.uniformOfFinset spec.coprimeForms hcop := by
  ext f
  change retryOutcomePMF (directProposalOutcomePMF spec J) J₀ (.accepted f) /
      retryAcceptedMass spec J J₀ = PMF.uniformOfFinset spec.coprimeForms hcop f
  rw [PMF.uniformOfFinset_apply, retryOutcomePMF_accepted,
    directProposalOutcomePMF_accepted spec hUJ f, retryAcceptedMass_eq spec hUJ]
  by_cases hf : f ∈ spec.coprimeForms
  · rw [if_pos hf, if_pos hf]
    set c : ENNReal := ((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
      ∑ k ∈ Finset.range J₀, (directProposalOutcomePMF spec J .rejected) ^ k
    have hc0 : c ≠ 0 := by
      apply mul_ne_zero (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      have h0mem : 0 ∈ Finset.range J₀ := Finset.mem_range.mpr (by omega)
      have hge : (1 : ENNReal) ≤ ∑ k ∈ Finset.range J₀,
          (directProposalOutcomePMF spec J .rejected) ^ k :=
        (pow_zero _).symm.trans_le (Finset.single_le_sum (fun _ _ => zero_le) h0mem)
      exact (lt_of_lt_of_le zero_lt_one hge).ne'
    have hctop : c ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by positivity))
        (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.pow_ne_top (PMF.apply_ne_top _ _)))
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hcop).ne'))
      (Or.inr hc0), mul_comm ((spec.coprimeForms.card : ENNReal)⁻¹), ← mul_assoc,
      ENNReal.mul_inv_cancel hc0 hctop, one_mul]
  · rw [if_neg hf, if_neg hf, zero_mul, ENNReal.zero_div]

/-- Conditional distribution when retrying `directProposalPMF` on `Option Form` (treating gcd
exits as rejections). -/
noncomputable def directRetryOptionConditionalPMF {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ} (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) : PMF Form :=
  let total : ENNReal := ∑ f ∈ spec.coprimeForms,
    retryOptionPMF (directProposalPMF spec J) J₀ (some f)
  ⟨fun f => retryOptionPMF (directProposalPMF spec J) J₀ (some f) / total, by
    have htotal : total = (spec.coprimeForms.card : ENNReal) *
        (((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
          ∑ k ∈ Finset.range J₀, (directProposalPMF spec J none) ^ k) := by
      dsimp only [total]
      have hcongr : ∀ f ∈ spec.coprimeForms,
          retryOptionPMF (directProposalPMF spec J) J₀ (some f) =
            ((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
              ∑ k ∈ Finset.range J₀, (directProposalPMF spec J none) ^ k := by
        intro f hf
        rw [retryOptionPMF_some, directProposalPMF_some spec hUJ f, if_pos hf]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
    have hc0 : (((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
        ∑ k ∈ Finset.range J₀, (directProposalPMF spec J none) ^ k) ≠ 0 := by
      apply mul_ne_zero (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      have h0mem : 0 ∈ Finset.range J₀ := Finset.mem_range.mpr (by omega)
      have hge : (1 : ENNReal) ≤ ∑ k ∈ Finset.range J₀,
          (directProposalPMF spec J none) ^ k :=
        (pow_zero _).symm.trans_le (Finset.single_le_sum (fun _ _ => zero_le) h0mem)
      exact (lt_of_lt_of_le zero_lt_one hge).ne'
    have hctop : (((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
        ∑ k ∈ Finset.range J₀, (directProposalPMF spec J none) ^ k) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by positivity))
        (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.pow_ne_top (PMF.apply_ne_top _ _)))
    have hmass_ne0 : total ≠ 0 := by
      rw [htotal]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hcop).ne') hc0
    have hmass_top : total ≠ ⊤ := by
      rw [htotal]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hctop
    have hsum_eq : (∑ f ∈ spec.coprimeForms,
        retryOptionPMF (directProposalPMF spec J) J₀ (some f) / total) = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [← div_eq_mul_inv]
      exact ENNReal.div_self hmass_ne0 hmass_top
    rw [← hsum_eq]
    exact hasSum_sum_of_ne_finset_zero (fun f hf => by
      rw [retryOptionPMF_some, directProposalPMF_some spec hUJ f, if_neg hf, zero_mul,
        ENNReal.zero_div])⟩

theorem directRetryOptionConditionalPMF_eq_uniform {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ} (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) :
    directRetryOptionConditionalPMF spec hUJ hJ₀ hcop =
      PMF.uniformOfFinset spec.coprimeForms hcop := by
  ext f
  change retryOptionPMF (directProposalPMF spec J) J₀ (some f) /
      (∑ g ∈ spec.coprimeForms, retryOptionPMF (directProposalPMF spec J) J₀ (some g)) =
    PMF.uniformOfFinset spec.coprimeForms hcop f
  rw [PMF.uniformOfFinset_apply]
  have htotal : (∑ g ∈ spec.coprimeForms,
      retryOptionPMF (directProposalPMF spec J) J₀ (some g)) =
      (spec.coprimeForms.card : ENNReal) *
        (((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
          ∑ k ∈ Finset.range J₀, (directProposalPMF spec J none) ^ k) := by
    have hcongr : ∀ g ∈ spec.coprimeForms,
        retryOptionPMF (directProposalPMF spec J) J₀ (some g) =
          ((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
            ∑ k ∈ Finset.range J₀, (directProposalPMF spec J none) ^ k := by
      intro g hg
      rw [retryOptionPMF_some, directProposalPMF_some spec hUJ g, if_pos hg]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
  rw [htotal, retryOptionPMF_some, directProposalPMF_some spec hUJ f]
  by_cases hf : f ∈ spec.coprimeForms
  · rw [if_pos hf, if_pos hf]
    set c : ENNReal := ((4 * 2 ^ J * (J + 1) : ℕ) : ENNReal)⁻¹ *
      ∑ k ∈ Finset.range J₀, (directProposalPMF spec J none) ^ k
    have hc0 : c ≠ 0 := by
      apply mul_ne_zero (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      have h0mem : 0 ∈ Finset.range J₀ := Finset.mem_range.mpr (by omega)
      have hge : (1 : ENNReal) ≤ ∑ k ∈ Finset.range J₀,
          (directProposalPMF spec J none) ^ k :=
        (pow_zero _).symm.trans_le (Finset.single_le_sum (fun _ _ => zero_le) h0mem)
      exact (lt_of_lt_of_le zero_lt_one hge).ne'
    have hctop : c ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by positivity))
        (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.pow_ne_top (PMF.apply_ne_top _ _)))
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hcop).ne'))
      (Or.inr hc0), mul_comm ((spec.coprimeForms.card : ENNReal)⁻¹), ← mul_assoc,
      ENNReal.mul_inv_cancel hc0 hctop, one_mul]
  · rw [if_neg hf, if_neg hf, zero_mul, ENNReal.zero_div]

end SequentialRetry

/-! ## Total Variation Distance and Missing-Class Count Bounds -/

section MissingClassTV

private lemma sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {s : Finset ι} {t : ι → Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ s.biUnion t, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    rw [Finset.biUnion_insert] at hf
    have hf' : ∀ x ∈ s.biUnion t, 0 ≤ f x := fun x hx => hf x (Finset.mem_union_right _ hx)
    have hinter := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hnn : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x :=
      Finset.sum_nonneg fun x hx => hf' x (Finset.mem_inter.mp hx).2
    linarith [ih hf']

/-- **EXACT TOTAL VARIATION DISTANCE** between the uniform law on a finite nonempty type `Ω`
and the uniform law on a nonempty subset `S ⊆ Ω`, proved via `RandomizedDeficientWeights`
and `RandomizedFiniteSupportTV`. -/
theorem pmfTotalVariation_uniformOfFinset_uniformOfFintype
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (S : Finset Ω) (hS : S.Nonempty) :
    pmfTotalVariation (PMF.uniformOfFinset S hS) (PMF.uniformOfFintype Ω) =
      ((Fintype.card Ω - S.card : ℕ) : ℝ) / (Fintype.card Ω : ℝ) := by
  rw [pmfTotalVariation_eq_totalVariation]
  have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hΩpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hp_eq : (fun z : Ω => (PMF.uniformOfFinset S hS z).toReal) =
      fun z => (if z ∈ S then (1 : ℝ) else 0) / (∑ y : Ω, if y ∈ S then (1 : ℝ) else 0) := by
    ext z
    have hsum : (∑ y : Ω, if y ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum, PMF.uniformOfFinset_apply]
    by_cases hz : z ∈ S
    · rw [if_pos hz, if_pos hz, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
    · rw [if_neg hz, if_neg hz, ENNReal.toReal_zero, zero_div]
  have hq_eq : (fun z : Ω => (PMF.uniformOfFintype Ω z).toReal) =
      fun _ => (1 : ℝ) / (Fintype.card Ω : ℝ) := by
    ext z
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  rw [hp_eq, hq_eq]
  have hupper : totalVariation
      (fun z => (if z ∈ S then (1 : ℝ) else 0) / (∑ y : Ω, if y ∈ S then (1 : ℝ) else 0))
      (fun _ => 1 / (Fintype.card Ω : ℝ)) ≤
      ((Fintype.card Ω - S.card : ℕ) : ℝ) / (Fintype.card Ω : ℝ) := by
    have hEcard : (Finset.univ \ S).card = Fintype.card Ω - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
    rw [← hEcard]
    refine deficient_weights_totalVariation_le
      (fun z => if z ∈ S then (1 : ℝ) else 0) 1 (Finset.univ \ S)
      zero_lt_one ?_ ?_ ?_ ?_
    · intro z; split_ifs <;> norm_num
    · intro z; split_ifs <;> norm_num
    · intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hz
      rw [if_pos hz]
    · have hsum : (∑ y : Ω, if y ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hsum]
      exact hSpos
  have hlower : ((Fintype.card Ω - S.card : ℕ) : ℝ) / (Fintype.card Ω : ℝ) ≤
      totalVariation
        (fun z => (if z ∈ S then (1 : ℝ) else 0) / (∑ y : Ω, if y ∈ S then (1 : ℝ) else 0))
        (fun _ => 1 / (Fintype.card Ω : ℝ)) := by
    have hsum1 : (∑ z : Ω, (if z ∈ S then (1 : ℝ) else 0) /
        (∑ y : Ω, if y ∈ S then (1 : ℝ) else 0)) = 1 := by
      rw [← Finset.sum_div]
      have hsum : (∑ y : Ω, if y ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hsum, div_self hSpos.ne']
    have hout := uniform_mass_outside_le_totalVariation S
      (fun z => (if z ∈ S then (1 : ℝ) else 0) / (∑ y : Ω, if y ∈ S then (1 : ℝ) else 0))
      hsum1 (fun z hz => by rw [if_neg hz, zero_div])
    have heq : (∑ _z ∈ Finset.univ \ S, (1 : ℝ) / (Fintype.card Ω : ℝ)) =
        ((Fintype.card Ω - S.card : ℕ) : ℝ) / (Fintype.card Ω : ℝ) := by
      rw [Finset.sum_const, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
        nsmul_eq_mul, mul_one_div]
    rwa [heq] at hout
  exact le_antisymm hupper hlower

/-- Exact TV distance between `PMF.uniformOfFinset CoprimeForms` and `PMF.uniformOfFinset AllForms`
in an arbitrary ambient type `Form`. -/
theorem pmfTotalVariation_uniformOfFinset_subset {Form : Type*} [DecidableEq Form]
    {CoprimeForms AllForms : Finset Form} (hsub : CoprimeForms ⊆ AllForms)
    (hC : CoprimeForms.Nonempty) (hA : AllForms.Nonempty) :
    pmfTotalVariation (PMF.uniformOfFinset CoprimeForms hC)
      (PMF.uniformOfFinset AllForms hA) =
      ((AllForms.card - CoprimeForms.card : ℕ) : ℝ) / (AllForms.card : ℝ) := by
  have hCpos : (0 : ℝ) < (CoprimeForms.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have hApos : (0 : ℝ) < (AllForms.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hCleA : (CoprimeForms.card : ℝ) ≤ (AllForms.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  unfold pmfTotalVariation
  have htsum : (∑' z : Form,
      |(PMF.uniformOfFinset CoprimeForms hC z).toReal -
        (PMF.uniformOfFinset AllForms hA z).toReal|) =
      ∑ z ∈ AllForms,
        |(PMF.uniformOfFinset CoprimeForms hC z).toReal -
          (PMF.uniformOfFinset AllForms hA z).toReal| := by
    apply tsum_eq_sum
    intro z hz
    have hzC : z ∉ CoprimeForms := fun h => hz (hsub h)
    simp [PMF.uniformOfFinset_apply, hz, hzC]
  rw [htsum, ← Finset.sum_sdiff hsub]
  have hpart1 : (∑ z ∈ AllForms \ CoprimeForms,
      |(PMF.uniformOfFinset CoprimeForms hC z).toReal -
        (PMF.uniformOfFinset AllForms hA z).toReal|) =
      ((AllForms.card - CoprimeForms.card : ℕ) : ℝ) / (AllForms.card : ℝ) := by
    have hcongr : ∀ z ∈ AllForms \ CoprimeForms,
        |(PMF.uniformOfFinset CoprimeForms hC z).toReal -
          (PMF.uniformOfFinset AllForms hA z).toReal| = 1 / (AllForms.card : ℝ) := by
      intro z hz
      obtain ⟨hzA, hzC⟩ := Finset.mem_sdiff.mp hz
      rw [PMF.uniformOfFinset_apply, PMF.uniformOfFinset_apply, if_neg hzC, if_pos hzA,
        ENNReal.toReal_zero, ENNReal.toReal_inv, ENNReal.toReal_natCast, zero_sub, abs_neg,
        abs_of_nonneg (by positivity), one_div]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_sdiff_of_subset hsub, nsmul_eq_mul,
      mul_one_div]
  have hpart2 : (∑ z ∈ CoprimeForms,
      |(PMF.uniformOfFinset CoprimeForms hC z).toReal -
        (PMF.uniformOfFinset AllForms hA z).toReal|) =
      ((AllForms.card - CoprimeForms.card : ℕ) : ℝ) / (AllForms.card : ℝ) := by
    have hcongr : ∀ z ∈ CoprimeForms,
        |(PMF.uniformOfFinset CoprimeForms hC z).toReal -
          (PMF.uniformOfFinset AllForms hA z).toReal| =
          1 / (CoprimeForms.card : ℝ) - 1 / (AllForms.card : ℝ) := by
      intro z hz
      have hzA := hsub hz
      rw [PMF.uniformOfFinset_apply, PMF.uniformOfFinset_apply, if_pos hz, if_pos hzA,
        ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
        one_div, one_div]
      apply abs_of_nonneg
      exact sub_nonneg.mpr (inv_anti₀ hCpos hCleA)
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul,
      Nat.cast_sub (Finset.card_le_card hsub)]
    field_simp [hCpos.ne', hApos.ne']
  rw [hpart1, hpart2]
  ring

/-- Local prime-power sum `S_p = ∑_{k ≥ 1} R(p^k) / p^k`. -/
noncomputable def localPrimeSeries (R : ℕ → ℕ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, (R (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1)

private lemma multiplicative_prod_prime_pow {R : ℕ → ℕ}
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) (e : ℕ → ℕ) :
    R (∏ p ∈ s, p ^ (e p)) = ∏ p ∈ s, R (p ^ (e p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hR1]
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp]
    have hcop : Nat.Coprime (p ^ (e p)) (∏ q ∈ s, q ^ (e q)) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hp' := hs p (Finset.mem_insert_self p s)
      have hq' := hs q (Finset.mem_insert_of_mem hq)
      have hne : p ≠ q := fun h => hp (h ▸ hq)
      exact ((Nat.coprime_primes hp' hq').mpr hne).pow _ _
    rw [hRmul _ _ hcop, ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))]

/-- **EXACT MISSING-COUNT SUM BOUND** from local prime-power sums `S_p`:
`∑_{A ≤ U, ¬ Coprime A N} R(A) ≤ 2 * U * (1 + log U) * (∑_{p | N} S_p) * ∏_{q | N} (1 + S_q)`. -/
theorem missing_root_sum_le_local_series {N U : ℕ} (hN : N ≠ 0) (hU : 1 ≤ U)
    (R : ℕ → ℕ) (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRsumm : ∀ p ∈ N.primeFactors,
      Summable (fun k : ℕ => (R (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1))) :
    (∑ A ∈ (Finset.Icc 1 U).filter (fun A => ¬ Nat.Coprime A N), (R A : ℝ)) ≤
      2 * (U : ℝ) * (1 + Real.log (U : ℝ)) *
        (∑ p ∈ N.primeFactors, localPrimeSeries R p) *
        ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) := by
  classical
  have hlogU_nn : 0 ≤ 1 + Real.log (U : ℝ) := by
    have hU1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
    linarith [Real.log_nonneg hU1]
  -- Step 1: Union bound over primes `p ∈ N.primeFactors`.
  have hunion :
      (∑ A ∈ (Finset.Icc 1 U).filter (fun A => ¬ Nat.Coprime A N), (R A : ℝ)) ≤
        ∑ p ∈ N.primeFactors, ∑ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A), (R A : ℝ) := by
    have hsub : (Finset.Icc 1 U).filter (fun A => ¬ Nat.Coprime A N) ⊆
        N.primeFactors.biUnion (fun p => (Finset.Icc 1 U).filter (fun A => p ∣ A)) := by
      intro A hA
      simp only [Finset.mem_filter, Finset.mem_Icc] at hA
      have hgne1 : Nat.gcd A N ≠ 1 := hA.2
      set p := Nat.minFac (Nat.gcd A N)
      have hp_prime : Nat.Prime p := Nat.minFac_prime hgne1
      have hp_gcd : p ∣ Nat.gcd A N := Nat.minFac_dvd _
      have hpA : p ∣ A := hp_gcd.trans (Nat.gcd_dvd_left A N)
      have hpN : p ∣ N := hp_gcd.trans (Nat.gcd_dvd_right A N)
      rw [Finset.mem_biUnion]
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp_prime, hpN, hN⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hA.1, hpA⟩⟩
    calc
      (∑ A ∈ (Finset.Icc 1 U).filter (fun A => ¬ Nat.Coprime A N), (R A : ℝ))
        ≤ ∑ A ∈ N.primeFactors.biUnion (fun p => (Finset.Icc 1 U).filter (fun A => p ∣ A)),
            (R A : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ∑ p ∈ N.primeFactors, ∑ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A), (R A : ℝ) :=
          sum_biUnion_le_of_nonneg (f := fun A => (R A : ℝ)) (by intro _ _; positivity)
  -- Step 2: Bound each prime `p ∈ N.primeFactors` by factoring `A = a * m`.
  have hper_prime : ∀ p ∈ N.primeFactors,
      (∑ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A), (R A : ℝ)) ≤
        2 * (U : ℝ) * (1 + Real.log (U : ℝ)) * localPrimeSeries R p *
          ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) := by
    intro p hp
    -- Define the `N`-smooth part `smoothPart A = ∏ q ∈ N.primeFactors, q ^ (A.factorization q)`.
    let smoothPart : ℕ → ℕ := fun A => ∏ q ∈ N.primeFactors, q ^ (A.factorization q)
    let SmoothDiv := (Finset.Icc 1 U).filter (fun a => p ∣ a ∧ a.primeFactors ⊆ N.primeFactors)
    have hsmooth_props : ∀ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A),
        smoothPart A ∈ SmoothDiv ∧ smoothPart A ∣ A ∧
          Nat.Coprime (smoothPart A) (A / smoothPart A) ∧
          Nat.Coprime (A / smoothPart A) N := by
      intro A hA
      simp only [Finset.mem_filter, Finset.mem_Icc] at hA
      have hA0 : A ≠ 0 := by omega
      have hAprod : A = ∏ q ∈ A.primeFactors, q ^ (A.factorization q) := by
        simpa [Finsupp.prod, Nat.support_factorization] using
          (Nat.factorization_prod_pow_eq_self hA0).symm
      have hsplitA : A = (∏ q ∈ A.primeFactors ∩ N.primeFactors, q ^ (A.factorization q)) *
          (∏ q ∈ A.primeFactors \ N.primeFactors, q ^ (A.factorization q)) := by
        conv_lhs => rw [hAprod]
        rw [← Finset.prod_union (Finset.disjoint_sdiff_inter _ _).symm, Finset.union_comm,
          Finset.sdiff_union_inter]
      have hsmooth_eq : smoothPart A =
          ∏ q ∈ A.primeFactors ∩ N.primeFactors, q ^ (A.factorization q) := by
        dsimp only [smoothPart]
        symm
        apply Finset.prod_subset Finset.inter_subset_right
        intro q hq hqnot
        have hqnotA : q ∉ A.primeFactors := fun h => hqnot (Finset.mem_inter.mpr ⟨h, hq⟩)
        have hzero : A.factorization q = 0 := by
          by_contra hne
          exact hqnotA (by simpa [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hne)
        rw [hzero, pow_zero]
      have hdvd : smoothPart A ∣ A := by
        rw [hsmooth_eq]
        exact ⟨_, hsplitA⟩
      have hsmooth_pos : 1 ≤ smoothPart A :=
        Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hsmooth_le : smoothPart A ≤ U :=
        (Nat.le_of_dvd (by omega) hdvd).trans hA.1.2
      have hp_dvd_smooth : p ∣ smoothPart A := by
        dsimp only [smoothPart]
        have hpos_exp : 1 ≤ A.factorization p := by
          have hmem : p ∈ A.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hA.2, hA0⟩
          have : p ∈ A.factorization.support := by simpa [Nat.support_factorization] using hmem
          exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp this)
        exact (dvd_pow_self p (by omega)).trans
          (Finset.dvd_prod_of_mem (fun q => q ^ (A.factorization q)) hp)
      have hsmooth_pf : (smoothPart A).primeFactors ⊆ N.primeFactors := by
        intro r hr
        have hr_prime := Nat.prime_of_mem_primeFactors hr
        have hr_dvd : r ∣ ∏ q ∈ N.primeFactors, q ^ (A.factorization q) :=
          Nat.dvd_of_mem_primeFactors hr
        obtain ⟨q, hq, hrq⟩ := (hr_prime.prime.dvd_finsetProd_iff _).mp hr_dvd
        have hrq' := hr_prime.dvd_of_dvd_pow hrq
        have hq_prime := Nat.prime_of_mem_primeFactors hq
        have heq : r = q := (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp hrq'
        exact heq ▸ hq
      have hquot_eq : A / smoothPart A =
          ∏ q ∈ A.primeFactors \ N.primeFactors, q ^ (A.factorization q) := by
        have hpos : 0 < smoothPart A := hsmooth_pos
        have h := hsplitA
        rw [← hsmooth_eq] at h
        exact Nat.div_eq_of_eq_mul_right hpos h
      have hcop_mN : Nat.Coprime (A / smoothPart A) N := by
        rw [hquot_eq]
        refine Nat.Coprime.prod_left fun q hq => ?_
        have hqA : q ∈ A.primeFactors := (Finset.mem_sdiff.mp hq).1
        have hqnotN : q ∉ N.primeFactors := (Finset.mem_sdiff.mp hq).2
        have hq_prime := Nat.prime_of_mem_primeFactors hqA
        have hqnotdvd : ¬ q ∣ N := fun hd =>
          hqnotN (Nat.mem_primeFactors.mpr ⟨hq_prime, hd, hN⟩)
        exact (hq_prime.coprime_iff_not_dvd.mpr hqnotdvd).pow_left _
      have hcop_am : Nat.Coprime (smoothPart A) (A / smoothPart A) := by
        rw [hquot_eq, hsmooth_eq]
        refine Nat.Coprime.prod_left fun q₁ hq₁ => Nat.Coprime.prod_right fun q₂ hq₂ => ?_
        have hq₁_p := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq₁).1
        have hq₂_p := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq₂).1
        have hne : q₁ ≠ q₂ := by
          rintro rfl
          exact (Finset.mem_sdiff.mp hq₂).2 (Finset.mem_inter.mp hq₁).2
        exact ((Nat.coprime_primes hq₁_p hq₂_p).mpr hne).pow _ _
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hsmooth_pos, hsmooth_le⟩,
        hp_dvd_smooth, hsmooth_pf⟩, hdvd, hcop_am, hcop_mN⟩
    -- Group `A` by `(a, m) = (smoothPart A, A / smoothPart A)`.
    have hgroup :
        (∑ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A), (R A : ℝ)) ≤
          ∑ a ∈ SmoothDiv, (R a : ℝ) *
            ∑ m ∈ (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N), (R m : ℝ) := by
      have hpair_sum :
          (∑ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A), (R A : ℝ)) ≤
            ∑ x ∈ SmoothDiv.sigma (fun a => (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N)),
              (R x.1 : ℝ) * (R x.2 : ℝ) := by
        · have hinj : Set.InjOn (fun A => (⟨smoothPart A, A / smoothPart A⟩ : Σ _ : ℕ, ℕ))
              (((Finset.Icc 1 U).filter (fun A => p ∣ A) : Finset ℕ) : Set ℕ) := by
            intro A₁ hA₁ A₂ hA₂ hEq
            have hd1 := (hsmooth_props A₁ hA₁).2.1
            have hd2 := (hsmooth_props A₂ hA₂).2.1
            have h1 : smoothPart A₁ = smoothPart A₂ := congrArg Sigma.fst hEq
            have h2 : A₁ / smoothPart A₁ = A₂ / smoothPart A₂ := by
              simpa using congrArg Sigma.snd hEq
            rw [← Nat.mul_div_cancel' hd1, ← Nat.mul_div_cancel' hd2, h2, h1]
          have hmaps : ∀ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A),
              (⟨smoothPart A, A / smoothPart A⟩ : Σ _ : ℕ, ℕ) ∈
                SmoothDiv.sigma (fun a => (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N)) := by
            intro A hA
            obtain ⟨hsa, hdvd, _, hcop⟩ := hsmooth_props A hA
            have hA1 : 1 ≤ A := (Finset.mem_Icc.mp (Finset.mem_filter.mp hA).1).1
            have hAU : A ≤ U := (Finset.mem_Icc.mp (Finset.mem_filter.mp hA).1).2
            have ha1 : 1 ≤ smoothPart A := (Finset.mem_Icc.mp (Finset.mem_filter.mp hsa).1).1
            have haleA : smoothPart A ≤ A := Nat.le_of_dvd (by omega) hdvd
            rw [Finset.mem_sigma]
            exact ⟨hsa, Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos haleA ha1, Nat.div_le_div_right hAU⟩, hcop⟩⟩
          have hval : ∀ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A),
              (R A : ℝ) = (R (smoothPart A) : ℝ) * (R (A / smoothPart A) : ℝ) := by
            intro A hA
            obtain ⟨_, hdvd, hcop, _⟩ := hsmooth_props A hA
            have hprod := (Nat.mul_div_cancel' hdvd).symm
            conv_lhs => rw [hprod]
            rw [hRmul _ _ hcop]
            push_cast
            rfl
          rw [Finset.sum_congr rfl hval]
          have himg := Finset.sum_image (f := fun x : Σ _ : ℕ, ℕ => (R x.1 : ℝ) * (R x.2 : ℝ)) hinj
          rw [← himg]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
            exact hmaps A hA
          · intro _ _ _; positivity
      refine hpair_sum.trans_eq ?_
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    -- Bound the inner `m`-sum using `sum_two_pow_omega_le`.
    have hinner : ∀ a ∈ SmoothDiv,
        (∑ m ∈ (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N), (R m : ℝ)) ≤
          2 * ((U : ℝ) / (a : ℝ)) * (1 + Real.log (U : ℝ)) := by
      intro a ha
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      have haU : a ≤ U := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
      have hUa1 : 1 ≤ U / a := Nat.div_pos haU ha1
      have hUa_le : U / a ≤ U := Nat.div_le_self U a
      have hstep1 :
          (∑ m ∈ (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N), (R m : ℝ)) ≤
            2 * ∑ m ∈ Finset.Icc 1 (U / a), (2 : ℝ) ^ m.primeFactors.card := by
        calc
          (∑ m ∈ (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N), (R m : ℝ))
            ≤ ∑ m ∈ (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N),
                2 * (2 : ℝ) ^ m.primeFactors.card := by
              apply Finset.sum_le_sum
              intro m hm
              have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
              have hmcop : Nat.Coprime m N := (Finset.mem_filter.mp hm).2
              exact_mod_cast hRcop m hm1 hmcop
          _ ≤ ∑ m ∈ Finset.Icc 1 (U / a), 2 * (2 : ℝ) ^ m.primeFactors.card :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => by positivity)
          _ = 2 * ∑ m ∈ Finset.Icc 1 (U / a), (2 : ℝ) ^ m.primeFactors.card := by
              rw [Finset.mul_sum]
      have hdiv_le : ((U / a : ℕ) : ℝ) ≤ (U : ℝ) / (a : ℝ) := by
        have hapos : (0 : ℝ) < (a : ℝ) := by positivity
        rw [le_div_iff₀ hapos]
        exact_mod_cast Nat.div_mul_le_self U a
      have hlog_le : Real.log ((U / a : ℕ) : ℝ) ≤ Real.log (U : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hUa_le)
      calc
        (∑ m ∈ (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N), (R m : ℝ))
          ≤ 2 * ∑ m ∈ Finset.Icc 1 (U / a), (2 : ℝ) ^ m.primeFactors.card := hstep1
        _ ≤ 2 * (((U / a : ℕ) : ℝ) * (1 + Real.log ((U / a : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (sum_two_pow_omega_le hUa1) (by norm_num)
        _ ≤ 2 * (((U : ℝ) / (a : ℝ)) * (1 + Real.log (U : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have hnn : 0 ≤ 1 + Real.log ((U / a : ℕ) : ℝ) := by
              have : (1 : ℝ) ≤ ((U / a : ℕ) : ℝ) := by exact_mod_cast hUa1
              linarith [Real.log_nonneg this]
            exact mul_le_mul hdiv_le (by linarith) hnn (by positivity)
        _ = 2 * ((U : ℝ) / (a : ℝ)) * (1 + Real.log (U : ℝ)) := by ring
    -- Bound the outer `SmoothDiv` sum by the Euler product of local series.
    have hsmooth_sum :
        (∑ a ∈ SmoothDiv, (R a : ℝ) / (a : ℝ)) ≤
          localPrimeSeries R p * ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) := by
      -- Map each `a ∈ SmoothDiv` injectively to its exponent vector `q ↦ a.factorization q`
      -- inside `Π q ∈ N.primeFactors, (if q = p then Icc 1 U else Icc 0 U)`.
      let box : Finset (∀ q : ℕ, q ∈ N.primeFactors → ℕ) :=
        Finset.pi N.primeFactors (fun q => if q = p then Finset.Icc 1 U else Finset.Icc 0 U)
      let term : ℕ → ℕ → ℝ := fun q k => (R (q ^ k) : ℝ) / (q : ℝ) ^ k
      have hmap_sum :
          (∑ a ∈ SmoothDiv, (R a : ℝ) / (a : ℝ)) ≤
            ∑ f ∈ box, ∏ q ∈ N.primeFactors.attach, term q.1 (f q.1 q.2) := by
        let phi : ℕ → (∀ q : ℕ, q ∈ N.primeFactors → ℕ) := fun a q _ => a.factorization q
        have hphi_mem : ∀ a ∈ SmoothDiv, phi a ∈ box := by
          intro a ha
          simp only [SmoothDiv, Finset.mem_filter, Finset.mem_Icc] at ha
          have ha0 : a ≠ 0 := by omega
          rw [Finset.mem_pi]
          intro q hq
          have hq_prime := Nat.prime_of_mem_primeFactors hq
          have hexp_le : a.factorization q ≤ U := by
            have hq2 : 2 ≤ q := hq_prime.two_le
            have hpow_le : 2 ^ (a.factorization q) ≤ a := by
              calc
                2 ^ (a.factorization q) ≤ q ^ (a.factorization q) :=
                  Nat.pow_le_pow_left hq2 _
                _ ≤ a := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd a q)
            have hlin : a.factorization q < 2 ^ (a.factorization q) := Nat.lt_two_pow_self
            omega
          split_ifs with hqp
          · subst hqp
            have hpos : 1 ≤ a.factorization q := by
              have hmem : q ∈ a.primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, ha.2.1, ha0⟩
              have : q ∈ a.factorization.support := by simpa [Nat.support_factorization] using hmem
              exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp this)
            exact Finset.mem_Icc.mpr ⟨hpos, hexp_le⟩
          · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hexp_le⟩
        have hphi_inj : Set.InjOn phi (SmoothDiv : Set ℕ) := by
          intro a₁ ha₁ a₂ ha₂ hEq
          simp only [Finset.mem_coe, SmoothDiv, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
          have ha₁0 : a₁ ≠ 0 := by omega
          have ha₂0 : a₂ ≠ 0 := by omega
          have hprod : ∀ a, a ≠ 0 → a.primeFactors ⊆ N.primeFactors →
              a = ∏ q ∈ N.primeFactors, q ^ (a.factorization q) := by
            intro a ha0 hpf
            have h1 : a = ∏ q ∈ a.primeFactors, q ^ (a.factorization q) := by
              simpa [Finsupp.prod, Nat.support_factorization] using
                (Nat.factorization_prod_pow_eq_self ha0).symm
            conv_lhs => rw [h1]
            apply Finset.prod_subset hpf
            intro q _ hqnot
            have hzero : a.factorization q = 0 := by
              by_contra hne
              exact hqnot (by simpa [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hne)
            rw [hzero, pow_zero]
          rw [hprod a₁ ha₁0 ha₁.2.2, hprod a₂ ha₂0 ha₂.2.2]
          apply Finset.prod_congr rfl
          intro q hq
          have hqeq : a₁.factorization q = a₂.factorization q :=
            congrFun (congrFun hEq q) hq
          rw [hqeq]
        have hval : ∀ a ∈ SmoothDiv,
            (R a : ℝ) / (a : ℝ) = ∏ q ∈ N.primeFactors.attach, term q.1 (phi a q.1 q.2) := by
          intro a ha
          simp only [SmoothDiv, Finset.mem_filter, Finset.mem_Icc] at ha
          have ha0 : a ≠ 0 := by omega
          have ha_eq : a = ∏ q ∈ N.primeFactors, q ^ (a.factorization q) := by
            have h1 : a = ∏ q ∈ a.primeFactors, q ^ (a.factorization q) := by
              simpa [Finsupp.prod, Nat.support_factorization] using
                (Nat.factorization_prod_pow_eq_self ha0).symm
            conv_lhs => rw [h1]
            apply Finset.prod_subset ha.2.2
            intro q _ hqnot
            have hzero : a.factorization q = 0 := by
              by_contra hne
              exact hqnot (by simpa [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hne)
            rw [hzero, pow_zero]
          have hRa : R a = ∏ q ∈ N.primeFactors, R (q ^ (a.factorization q)) := by
            conv_lhs => rw [ha_eq]
            exact multiplicative_prod_prime_pow hR1 hRmul N.primeFactors
              (fun q hq => Nat.prime_of_mem_primeFactors hq) (fun q => a.factorization q)
          rw [hRa]
          conv_lhs => arg 2; rw [ha_eq]
          rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
          rw [← Finset.prod_attach N.primeFactors (fun q => (R (q ^ (a.factorization q)) : ℝ) /
            ((q ^ (a.factorization q) : ℕ) : ℝ))]
          apply Finset.prod_congr rfl
          intro q _
          simp [term, phi]
        rw [Finset.sum_congr rfl hval]
        have himg := Finset.sum_image
          (f := fun f : (∀ q : ℕ, q ∈ N.primeFactors → ℕ) =>
            ∏ q ∈ N.primeFactors.attach, term q.1 (f q.1 q.2)) hphi_inj
        rw [← himg]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro f hf
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
          exact hphi_mem a ha
        · intro _ _ _
          exact Finset.prod_nonneg (fun _ _ => by positivity)
      -- Expand `∑ f ∈ box, ∏ q, term q (f q)` as `∏ q ∈ N.primeFactors, ∑ k, term q k`.
      have hprod_sum :
          (∑ f ∈ box, ∏ q ∈ N.primeFactors.attach, term q.1 (f q.1 q.2)) =
            ∏ q ∈ N.primeFactors,
              ∑ k ∈ (if q = p then Finset.Icc 1 U else Finset.Icc 0 U), term q k := by
        simpa [box] using (Finset.prod_sum N.primeFactors
          (fun q => if q = p then Finset.Icc 1 U else Finset.Icc 0 U)
          (fun q k => term q k)).symm
      -- Bound each factor by `localPrimeSeries R p` (for `q = p`) or `1 + localPrimeSeries R q`.
      have hIcc1_le : ∀ q ∈ N.primeFactors,
          (∑ k ∈ Finset.Icc 1 U, term q k) ≤ localPrimeSeries R q := by
        intro q hq
        have hshift : (∑ k ∈ Finset.Icc 1 U, term q k) =
            ∑ k ∈ Finset.range U, (R (q ^ (k + 1)) : ℝ) / (q : ℝ) ^ (k + 1) := by
          refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
          · intro k hk
            simp only [Finset.mem_Icc] at hk
            exact Finset.mem_range.mpr (by omega)
          · intro k₁ hk₁ k₂ hk₂ hEq
            simp only [Finset.mem_Icc] at hk₁ hk₂
            omega
          · intro k hk
            simp only [Finset.mem_range] at hk
            exact ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro k hk
            simp only [Finset.mem_Icc] at hk
            have hk1 : k - 1 + 1 = k := by omega
            simp [term, hk1]
        rw [hshift, localPrimeSeries]
        exact (hRsumm q hq).sum_le_tsum (Finset.range U) (fun _ _ => by positivity)
      have hIcc0_le : ∀ q ∈ N.primeFactors,
          (∑ k ∈ Finset.Icc 0 U, term q k) ≤ 1 + localPrimeSeries R q := by
        intro q hq
        have hsplit0 : Finset.Icc 0 U = insert 0 (Finset.Icc 1 U) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hsplit0, Finset.sum_insert (by simp)]
        have hterm0 : term q 0 = 1 := by simp [term, hR1]
        rw [hterm0]
        linarith [hIcc1_le q hq]
      have hprod_le :
          (∏ q ∈ N.primeFactors,
              ∑ k ∈ (if q = p then Finset.Icc 1 U else Finset.Icc 0 U), term q k) ≤
            localPrimeSeries R p * ∏ q ∈ N.primeFactors.erase p, (1 + localPrimeSeries R q) := by
        rw [← Finset.mul_prod_erase N.primeFactors _ hp, if_pos rfl]
        apply mul_le_mul (hIcc1_le p hp)
        · apply Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
          intro q hq
          rw [if_neg (Finset.ne_of_mem_erase hq)]
          exact hIcc0_le q (Finset.mem_of_mem_erase hq)
        · exact Finset.prod_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
        · exact tsum_nonneg (fun _ => by positivity)
      have herase_le :
          (∏ q ∈ N.primeFactors.erase p, (1 + localPrimeSeries R q)) ≤
            ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) := by
        rw [← Finset.mul_prod_erase N.primeFactors _ hp]
        have hp_ge1 : 1 ≤ 1 + localPrimeSeries R p := by
          have : 0 ≤ localPrimeSeries R p := tsum_nonneg (fun _ => by positivity)
          linarith
        have hrest_nn : 0 ≤ ∏ q ∈ N.primeFactors.erase p, (1 + localPrimeSeries R q) :=
          Finset.prod_nonneg (fun q _ => by
            have : 0 ≤ localPrimeSeries R q := tsum_nonneg (fun _ => by positivity)
            linarith)
        calc
          ∏ q ∈ N.primeFactors.erase p, (1 + localPrimeSeries R q)
            = 1 * ∏ q ∈ N.primeFactors.erase p, (1 + localPrimeSeries R q) := (one_mul _).symm
          _ ≤ (1 + localPrimeSeries R p) *
              ∏ q ∈ N.primeFactors.erase p, (1 + localPrimeSeries R q) :=
              mul_le_mul_of_nonneg_right hp_ge1 hrest_nn
      calc
        (∑ a ∈ SmoothDiv, (R a : ℝ) / (a : ℝ))
          ≤ ∑ f ∈ box, ∏ q ∈ N.primeFactors.attach, term q.1 (f q.1 q.2) := hmap_sum
        _ = ∏ q ∈ N.primeFactors,
              ∑ k ∈ (if q = p then Finset.Icc 1 U else Finset.Icc 0 U), term q k := hprod_sum
        _ ≤ localPrimeSeries R p * ∏ q ∈ N.primeFactors.erase p, (1 + localPrimeSeries R q) :=
            hprod_le
        _ ≤ localPrimeSeries R p * ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) :=
            mul_le_mul_of_nonneg_left herase_le (tsum_nonneg (fun _ => by positivity))
    -- Combine `hgroup`, `hinner`, and `hsmooth_sum`.
    calc
      (∑ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A), (R A : ℝ))
        ≤ ∑ a ∈ SmoothDiv, (R a : ℝ) *
            ∑ m ∈ (Finset.Icc 1 (U / a)).filter (fun m => Nat.Coprime m N), (R m : ℝ) := hgroup
      _ ≤ ∑ a ∈ SmoothDiv, (R a : ℝ) * (2 * ((U : ℝ) / (a : ℝ)) * (1 + Real.log (U : ℝ))) :=
          Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hinner a ha) (Nat.cast_nonneg _))
      _ = 2 * (U : ℝ) * (1 + Real.log (U : ℝ)) * ∑ a ∈ SmoothDiv, (R a : ℝ) / (a : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
      _ ≤ 2 * (U : ℝ) * (1 + Real.log (U : ℝ)) *
            (localPrimeSeries R p * ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q)) :=
          mul_le_mul_of_nonneg_left hsmooth_sum (by positivity)
      _ = 2 * (U : ℝ) * (1 + Real.log (U : ℝ)) * localPrimeSeries R p *
            ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) := by ring
  calc
    (∑ A ∈ (Finset.Icc 1 U).filter (fun A => ¬ Nat.Coprime A N), (R A : ℝ))
      ≤ ∑ p ∈ N.primeFactors, ∑ A ∈ (Finset.Icc 1 U).filter (fun A => p ∣ A), (R A : ℝ) := hunion
    _ ≤ ∑ p ∈ N.primeFactors,
          (2 * (U : ℝ) * (1 + Real.log (U : ℝ)) * localPrimeSeries R p *
            ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q)) :=
        Finset.sum_le_sum hper_prime
    _ = 2 * (U : ℝ) * (1 + Real.log (U : ℝ)) *
          (∑ p ∈ N.primeFactors, localPrimeSeries R p) *
          ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) := by
        rw [Finset.mul_sum, Finset.sum_mul]

/-- Combining the missing-root sum bound with `S_p ≤ 4 / (p - 1)` and the fixed log-power
product bound `(log(2N))^80` for `N ≥ 2`. -/
theorem missing_root_sum_le_log_pow {N U : ℕ} (hN : 2 ≤ N) (hU : 1 ≤ U)
    (R : ℕ → ℕ) (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2)) :
    (∑ A ∈ (Finset.Icc 1 U).filter (fun A => ¬ Nat.Coprime A N), (R A : ℝ)) ≤
      2 * (U : ℝ) * (1 + Real.log (U : ℝ)) *
        (∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1)) *
        (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by
  have hN0 : N ≠ 0 := by omega
  have hlogU_nn : 0 ≤ 1 + Real.log (U : ℝ) := by
    have hU1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
    linarith [Real.log_nonneg hU1]
  have hloc : ∀ p ∈ N.primeFactors,
      Summable (fun k : ℕ => (R (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1)) ∧
        localPrimeSeries R p ≤ 4 / ((p : ℝ) - 1) := by
    intro p hp
    exact local_series_summable_and_le (Nat.prime_of_mem_primeFactors hp).two_le R (hRloc p hp)
  have hmain := missing_root_sum_le_local_series hN0 hU R hR1 hRmul hRcop (fun p hp => (hloc p hp).1)
  have hsum_le : (∑ p ∈ N.primeFactors, localPrimeSeries R p) ≤
      ∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1) :=
    Finset.sum_le_sum (fun p hp => (hloc p hp).2)
  have hprod_le : (∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q)) ≤
      (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by
    refine (Finset.prod_le_prod ?_ ?_).trans (primeFactors_local_prod_le_log_pow hN)
    · intro q _
      have : 0 ≤ localPrimeSeries R q := tsum_nonneg (fun _ => by positivity)
      linarith
    · intro q hq
      linarith [(hloc q hq).2]
  have hsum_nn : 0 ≤ ∑ p ∈ N.primeFactors, localPrimeSeries R p :=
    Finset.sum_nonneg (fun _ _ => tsum_nonneg (fun _ => by positivity))
  have hprod_nn : 0 ≤ ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) :=
    Finset.prod_nonneg (fun q _ => by
      have : 0 ≤ localPrimeSeries R q := tsum_nonneg (fun _ => by positivity)
      linarith)
  have h4sum_nn : 0 ≤ ∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1) := by
    apply Finset.sum_nonneg
    intro p hp
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hLpos : 0 ≤ Real.log (2 * (N : ℝ)) :=
    (zero_lt_one.trans (one_lt_log_two_mul hN)).le
  calc
    (∑ A ∈ (Finset.Icc 1 U).filter (fun A => ¬ Nat.Coprime A N), (R A : ℝ))
      ≤ 2 * (U : ℝ) * (1 + Real.log (U : ℝ)) *
          (∑ p ∈ N.primeFactors, localPrimeSeries R p) *
          ∏ q ∈ N.primeFactors, (1 + localPrimeSeries R q) := hmain
    _ ≤ 2 * (U : ℝ) * (1 + Real.log (U : ℝ)) *
          (∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1)) *
          (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by
        rw [mul_assoc (2 * (U : ℝ) * (1 + Real.log (U : ℝ))),
          mul_assoc (2 * (U : ℝ) * (1 + Real.log (U : ℝ)))]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hsum_le hprod_le hprod_nn h4sum_nn) (by positivity)

/-- Connecting `DirectFormSpec.omittedForms` to the non-coprime root count sum. -/
theorem omittedForms_card_le_root_sum {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) :
    spec.omittedForms.card ≤
      ∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N), (spec.roots A).card := by
  classical
  have hcard :
      spec.omittedForms.card ≤
        (((Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N)).sigma
          (fun A => spec.roots A)).card := by
    refine Finset.card_le_card_of_injOn (fun f => ⟨spec.leadCoeff f, spec.midCoeff f⟩) ?_ ?_
    · intro f hf
      simp only [Finset.mem_coe, DirectFormSpec.omittedForms, Finset.mem_filter] at hf
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨spec.leadCoeff_pos f hf.1, spec.leadCoeff_le f hf.1⟩, hf.2⟩,
        spec.midCoeff_mem_roots f hf.1⟩
    · intro f₁ hf₁ f₂ hf₂ hEq
      simp only [Finset.mem_coe, DirectFormSpec.omittedForms, Finset.mem_filter] at hf₁ hf₂
      apply spec.coeff_injective hf₁.1 hf₂.1
      exact Prod.ext (congrArg Sigma.fst hEq) (by simpa using congrArg Sigma.snd hEq)
  simpa [Finset.card_sigma] using hcard

/-- End-to-end TV distance bound for the direct sampler: after any retry cap `J₀ ≥ 1`,
the TV distance between the conditional returned-form law and uniform on `spec.allForms`
is at most the omitted root count divided by `spec.allForms.card`. -/
theorem directRetryConditionalPMF_tv_le {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ} (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2)) :
    pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
      (PMF.uniformOfFinset spec.allForms hall) ≤
      (2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
        (∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1)) *
        (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ)) / (spec.allForms.card : ℝ) := by
  rw [directRetryConditionalPMF_eq_uniform spec hUJ hJ₀ hcop,
    pmfTotalVariation_uniformOfFinset_subset
      (show spec.coprimeForms ⊆ spec.allForms from Finset.filter_subset _ _) hcop hall]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hdiff_eq : spec.allForms.card - spec.coprimeForms.card = spec.omittedForms.card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := spec.allForms) (p := fun f => Nat.Coprime (spec.leadCoeff f) spec.N)
    change spec.coprimeForms.card + spec.omittedForms.card = spec.allForms.card at hpart
    omega
  rw [hdiff_eq]
  have h1 : (spec.omittedForms.card : ℝ) ≤
      ∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N), (R A : ℝ) := by
    calc
      (spec.omittedForms.card : ℝ)
        ≤ ∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N),
            ((spec.roots A).card : ℝ) := by exact_mod_cast omittedForms_card_le_root_sum spec
      _ ≤ ∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N), (R A : ℝ) :=
          Finset.sum_le_sum (fun A hA => by exact_mod_cast hR_ge A (Finset.mem_filter.mp hA).1)
  exact h1.trans (missing_root_sum_le_log_pow hN hU R hR1 hRmul hRcop hRloc)

end MissingClassTV

/-! ## One-Attempt GCD Exit Probability Bound -/

section GcdExitBound

/-- Total one-attempt probability of hitting a nontrivial gcd exit `1 < gcd(A, N)`. -/
noncomputable def gcdExitProb {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (J : ℕ) : ENNReal :=
  ∑' g : ℕ, directProposalOutcomePMF spec J (.gcdExit g)

/-- The one-attempt gcd exit probability equals the Step 1 mass on `A ∈ [1, U]`
not coprime to `N`. -/
theorem gcdExitProb_eq_dyadic_noncoprime {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (J : ℕ) :
    gcdExitProb spec J =
      ∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N),
        dyadicProposalPMF J spec.U (some A) := by
  classical
  unfold gcdExitProb directProposalOutcomePMF
  simp only [PMF.bind_apply]
  rw [ENNReal.tsum_comm]
  have hterm : ∀ oA : Option ℕ,
      (∑' g : ℕ, dyadicProposalPMF J spec.U oA *
        (match oA with
          | none => PMF.pure DirectProposalOutcome.rejected
          | some A =>
            if hrange : 1 ≤ A ∧ A ≤ spec.U then
              if hcop : Nat.Coprime A spec.N then
                rootStepPMF spec A hrange.1 hrange.2 hcop
              else
                PMF.pure (DirectProposalOutcome.gcdExit (Nat.gcd A spec.N))
            else
              PMF.pure DirectProposalOutcome.rejected) (.gcdExit g)) =
      match oA with
      | none => 0
      | some A =>
        if A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N) then
          dyadicProposalPMF J spec.U (some A)
        else 0 := by
    intro oA
    cases oA with
    | none =>
      simp [PMF.pure_apply]
    | some A =>
      dsimp only
      by_cases hrange : 1 ≤ A ∧ A ≤ spec.U
      · rw [dif_pos hrange]
        by_cases hcop : Nat.Coprime A spec.N
        · rw [dif_pos hcop]
          have hzero : ∀ g, rootStepPMF spec A hrange.1 hrange.2 hcop (.gcdExit g) = 0 := by
            intro g
            unfold rootStepPMF
            split_ifs with hR
            · rw [PMF.bind_apply]
              apply ENNReal.tsum_eq_zero.mpr
              intro ok
              cases ok with
              | false => simp [PMF.pure_apply]
              | true =>
                apply mul_eq_zero_of_right
                rw [if_pos rfl, PMF.map_apply]
                apply ENNReal.tsum_eq_zero.mpr
                intro b
                cases spec.buildForm A b <;> simp
            · simp [PMF.pure_apply]
          have hnotmem : A ∉ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N) := by
            simp [hcop]
          rw [if_neg hnotmem]
          simp [hzero]
        · rw [dif_neg hcop]
          have hmem : A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N) :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hrange, hcop⟩
          rw [if_pos hmem, tsum_eq_single (Nat.gcd A spec.N)]
          · simp [PMF.pure_apply]
          · intro g hne
            simp [PMF.pure_apply, hne]
      · rw [dif_neg hrange]
        have hnotmem : A ∉ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N) := by
          intro h
          exact hrange (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1)
        rw [if_neg hnotmem]
        simp [PMF.pure_apply]
  rw [tsum_congr hterm]
  let S : Finset (Option ℕ) :=
    ((Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N)).image some
  rw [tsum_eq_sum (s := S)]
  · rw [Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)]
    apply Finset.sum_congr rfl
    intro A hA
    dsimp only
    rw [if_pos hA]
  · intro oA hoA
    cases oA with
    | none => rfl
    | some A =>
      have hnot : A ∉ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N) := by
        intro h
        exact hoA (Finset.mem_image_of_mem some h)
      dsimp only
      rw [if_neg hnot]

/-- Scaled one-attempt gcd exit bound:
`P(1 < gcd(A, N)) ≤ (U * (1 + log U) / (2^J * (J + 1))) * ∑_{p | N} 1/p`. -/
theorem gcdExitProb_toReal_le_scaled {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J : ℕ} (hN : spec.N ≠ 0) (hU : 1 ≤ spec.U)
    (hUJ : spec.U ≤ 2 ^ J) :
    (gcdExitProb spec J).toReal ≤
      ((spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) / ((2 : ℝ) ^ J * ((J : ℝ) + 1))) *
        ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ) := by
  classical
  rw [gcdExitProb_eq_dyadic_noncoprime]
  rw [ENNReal.toReal_sum (fun A _ => PMF.apply_ne_top _ _)]
  have hlogU_nn : 0 ≤ 1 + Real.log (spec.U : ℝ) := by
    have hU1 : (1 : ℝ) ≤ (spec.U : ℝ) := by exact_mod_cast hU
    linarith [Real.log_nonneg hU1]
  have hterm_eq : ∀ A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N),
      (dyadicProposalPMF J spec.U (some A)).toReal =
        (2 : ℝ) ^ A.primeFactors.card / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) := by
    intro A hA
    have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hA).1
    exact dyadicProposalPMF_apply_some_toReal hIcc.1 hIcc.2 hUJ
  rw [Finset.sum_congr rfl hterm_eq]
  -- Union bound over `p ∈ spec.N.primeFactors`.
  have hunion :
      (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N),
          (2 : ℝ) ^ A.primeFactors.card / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1))) ≤
        ∑ p ∈ spec.N.primeFactors,
          ∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A),
            (2 : ℝ) ^ A.primeFactors.card / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) := by
    have hsub : (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N) ⊆
        spec.N.primeFactors.biUnion (fun p => (Finset.Icc 1 spec.U).filter (fun A => p ∣ A)) := by
      intro A hA
      simp only [Finset.mem_filter, Finset.mem_Icc] at hA
      set p := Nat.minFac (Nat.gcd A spec.N)
      have hp_prime : Nat.Prime p := Nat.minFac_prime hA.2
      have hp_gcd : p ∣ Nat.gcd A spec.N := Nat.minFac_dvd _
      rw [Finset.mem_biUnion]
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp_prime, hp_gcd.trans (Nat.gcd_dvd_right _ _), hN⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hA.1, hp_gcd.trans (Nat.gcd_dvd_left _ _)⟩⟩
    calc
      _ ≤ ∑ A ∈ spec.N.primeFactors.biUnion (fun p => (Finset.Icc 1 spec.U).filter (fun A => p ∣ A)),
            (2 : ℝ) ^ A.primeFactors.card / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ _ := sum_biUnion_le_of_nonneg (by intro _ _; positivity)
  have hper_prime : ∀ p ∈ spec.N.primeFactors,
      (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A),
          (2 : ℝ) ^ A.primeFactors.card / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1))) ≤
        ((spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) / ((2 : ℝ) ^ J * ((J : ℝ) + 1))) *
          ((1 : ℝ) / (p : ℝ)) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_pos : 0 < p := hp_prime.pos
    rw [← Finset.sum_div]
    -- Reindex `A = p * m` for `m ∈ Icc 1 (U / p)`.
    have hsum_pm :
        (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A), (2 : ℝ) ^ A.primeFactors.card) ≤
          2 * ∑ m ∈ Finset.Icc 1 (spec.U / p), (2 : ℝ) ^ m.primeFactors.card := by
      have hbij :
          (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A), (2 : ℝ) ^ A.primeFactors.card) =
            ∑ m ∈ Finset.Icc 1 (spec.U / p), (2 : ℝ) ^ (p * m).primeFactors.card := by
        refine Finset.sum_bij (fun A _ => A / p) ?_ ?_ ?_ ?_
        · intro A hA
          simp only [Finset.mem_filter, Finset.mem_Icc] at hA ⊢
          have hpA : p ≤ A := Nat.le_of_dvd (by omega) hA.2
          exact ⟨Nat.div_pos hpA hp_pos, Nat.div_le_div_right hA.1.2⟩
        · intro A₁ hA₁ A₂ hA₂ hEq
          simp only [Finset.mem_filter] at hA₁ hA₂
          rw [← Nat.mul_div_cancel' hA₁.2, ← Nat.mul_div_cancel' hA₂.2, hEq]
        · intro m hm
          simp only [Finset.mem_Icc] at hm
          have hpm_pos : 1 ≤ p * m := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp_prime.ne_zero (by omega))
          have hpm_le : p * m ≤ spec.U := by
            calc
              p * m ≤ p * (spec.U / p) := Nat.mul_le_mul_left p hm.2
              _ ≤ spec.U := Nat.mul_div_le spec.U p
          exact ⟨p * m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpm_pos, hpm_le⟩, dvd_mul_right p m⟩,
            Nat.mul_div_cancel_left m hp_pos⟩
        · intro A hA
          simp only [Finset.mem_filter] at hA
          rw [Nat.mul_div_cancel' hA.2]
      rw [hbij, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      have hm0 : m ≠ 0 := by
        have := (Finset.mem_Icc.mp hm).1
        omega
      have hcard : (p * m).primeFactors.card ≤ m.primeFactors.card + 1 := by
        rw [Nat.primeFactors_mul hp_prime.ne_zero hm0, hp_prime.primeFactors,
          Finset.singleton_union]
        exact Finset.card_insert_le p m.primeFactors
      calc
        (2 : ℝ) ^ (p * m).primeFactors.card
          ≤ (2 : ℝ) ^ (m.primeFactors.card + 1) := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) hcard
        _ = 2 * (2 : ℝ) ^ m.primeFactors.card := by rw [pow_succ']
    by_cases hUp : 1 ≤ spec.U / p
    · have hdiv_le : ((spec.U / p : ℕ) : ℝ) ≤ (spec.U : ℝ) / (p : ℝ) := by
        have hpR : (0 : ℝ) < (p : ℝ) := by positivity
        rw [le_div_iff₀ hpR]
        exact_mod_cast Nat.div_mul_le_self spec.U p
      have hlog_le : Real.log ((spec.U / p : ℕ) : ℝ) ≤ Real.log (spec.U : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.div_le_self spec.U p)
      have hbound :
          (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A), (2 : ℝ) ^ A.primeFactors.card) ≤
            2 * ((spec.U : ℝ) / (p : ℝ)) * (1 + Real.log (spec.U : ℝ)) := by
        have hnn : 0 ≤ 1 + Real.log ((spec.U / p : ℕ) : ℝ) := by
          have : (1 : ℝ) ≤ ((spec.U / p : ℕ) : ℝ) := by exact_mod_cast hUp
          linarith [Real.log_nonneg this]
        calc
          _ ≤ 2 * ∑ m ∈ Finset.Icc 1 (spec.U / p), (2 : ℝ) ^ m.primeFactors.card := hsum_pm
          _ ≤ 2 * (((spec.U / p : ℕ) : ℝ) * (1 + Real.log ((spec.U / p : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left (sum_two_pow_omega_le hUp) (by norm_num)
          _ ≤ 2 * (((spec.U : ℝ) / (p : ℝ)) * (1 + Real.log (spec.U : ℝ))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hdiv_le (by linarith) hnn (by positivity)) (by norm_num)
          _ = 2 * ((spec.U : ℝ) / (p : ℝ)) * (1 + Real.log (spec.U : ℝ)) := by ring
      calc
        (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A), (2 : ℝ) ^ A.primeFactors.card) /
            (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1))
          ≤ (2 * ((spec.U : ℝ) / (p : ℝ)) * (1 + Real.log (spec.U : ℝ))) /
              (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hbound (by positivity)
        _ = ((spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) / ((2 : ℝ) ^ J * ((J : ℝ) + 1))) *
              ((1 : ℝ) / (p : ℝ)) := by field_simp
    · have hUp0 : spec.U / p = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_le hUp)
      have hzero : (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A),
          (2 : ℝ) ^ A.primeFactors.card) ≤ 0 := by
        simpa [hUp0] using hsum_pm
      have hle0 : (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A),
          (2 : ℝ) ^ A.primeFactors.card) / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hzero (by positivity)
      exact hle0.trans (by positivity)
  calc
    (∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => ¬ Nat.Coprime A spec.N),
        (2 : ℝ) ^ A.primeFactors.card / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1)))
      ≤ ∑ p ∈ spec.N.primeFactors,
          ∑ A ∈ (Finset.Icc 1 spec.U).filter (fun A => p ∣ A),
            (2 : ℝ) ^ A.primeFactors.card / (2 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) := hunion
    _ ≤ ∑ p ∈ spec.N.primeFactors,
          ((spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) / ((2 : ℝ) ^ J * ((J : ℝ) + 1))) *
            ((1 : ℝ) / (p : ℝ)) := Finset.sum_le_sum hper_prime
    _ = ((spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) / ((2 : ℝ) ^ J * ((J : ℝ) + 1))) *
          ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ) := by rw [← Finset.mul_sum]

/-- **ONE-ATTEMPT GCD EXIT BOUND**: the probability of hitting `1 < gcd(A, N)` in a single
attempt is at most `∑_{p | N} 1 / p` (explicit constant `1`). -/
theorem gcdExitProb_toReal_le {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J : ℕ} (hN : spec.N ≠ 0) (hU : 1 ≤ spec.U)
    (hUJ : spec.U ≤ 2 ^ J) :
    (gcdExitProb spec J).toReal ≤ ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ) := by
  have hscale : (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) /
      ((2 : ℝ) ^ J * ((J : ℝ) + 1)) ≤ 1 := by
    have hden_pos : (0 : ℝ) < (2 : ℝ) ^ J * ((J : ℝ) + 1) := by positivity
    rw [div_le_one hden_pos]
    have hUle : (spec.U : ℝ) ≤ (2 : ℝ) ^ J := by exact_mod_cast hUJ
    have hlogU : Real.log (spec.U : ℝ) ≤ (J : ℝ) := by
      have h1 : Real.log (spec.U : ℝ) ≤ Real.log ((2 : ℝ) ^ J) :=
        Real.log_le_log (by positivity) hUle
      rw [Real.log_pow] at h1
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      calc
        Real.log (spec.U : ℝ) ≤ (J : ℝ) * Real.log 2 := h1
        _ ≤ (J : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg J)
        _ = (J : ℝ) := mul_one _
    have hlogU_nn : 0 ≤ 1 + Real.log (spec.U : ℝ) := by
      have hU1 : (1 : ℝ) ≤ (spec.U : ℝ) := by exact_mod_cast hU
      linarith [Real.log_nonneg hU1]
    exact mul_le_mul hUle (by linarith) hlogU_nn (by positivity)
  have hsum_nn : 0 ≤ ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    (gcdExitProb spec J).toReal
      ≤ ((spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) / ((2 : ℝ) ^ J * ((J : ℝ) + 1))) *
          ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ) :=
        gcdExitProb_toReal_le_scaled spec hN hU hUJ
    _ ≤ 1 * ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ) :=
        mul_le_mul_of_nonneg_right hscale hsum_nn
    _ = ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ) := one_mul _

end GcdExitBound

#print axioms dyadicProposalPMF_apply_some
#print axioms modNegSqRootCount_le_two_pow_omega_succ_of_odd
#print axioms modNegSqRootCount_le_two_pow_omega_succ_of_two_mul_odd
#print axioms modNegSqRootCount_odd_prime_pow_le
#print axioms directProposalOutcomePMF_gcdExit_proper_divisor
#print axioms directProposalOutcomePMF_accepted
#print axioms directProposalPMF_some
#print axioms directRetryOutcomePMF_accepted_toReal
#print axioms directRetryConditionalPMF_eq_uniform
#print axioms directRetryOptionConditionalPMF_eq_uniform
#print axioms pmfTotalVariation_uniformOfFinset_uniformOfFintype
#print axioms pmfTotalVariation_uniformOfFinset_subset
#print axioms missing_root_sum_le_local_series
#print axioms missing_root_sum_le_log_pow
#print axioms primeFactors_local_prod_le_log_pow
#print axioms directRetryConditionalPMF_tv_le
#print axioms gcdExitProb_toReal_le_scaled
#print axioms gcdExitProb_toReal_le

end Cogentic.RandomizedDirectClassSampler
