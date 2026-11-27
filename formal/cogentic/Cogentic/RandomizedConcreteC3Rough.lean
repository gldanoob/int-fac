import Cogentic.RandomizedConcreteC3Budget
import Cogentic.RandomizedSmallPrimePrepass

/-!
# The real C3 budget on rough moduli

`RandomizedConcreteC3Budget` shows that the real C3 budget is controlled by the
sampler-free expression

`criticalLineGcdBudget N = 8 log N * missingRootMass N / sqrt N + ∑_{p | N} 1/p`

once the critical-line class-number lower bound is available.  For general `N`
this expression does not tend to zero: a small prime divisor such as `3`
contributes `1/3` to the reciprocal-prime sum, and the missing-root numerator
contains `(log (2N))^80`.

On the rough branch all prime divisors are larger than
`B = roughThreshold n = exp((log n)^(2/3))`.  Then

* `∑_{p | n} 1/p ≤ (log n / log B) / B`, and
* `∑_{p | n} 4/(p-1) ≤ 8 (log n / log B) / B`,

so both terms of the budget acquire a `1/B` saving.  The remaining numerator is
a fixed power of `log (2n)`, which is eventually dominated by
`B log B = exp((log n)^(2/3)) (log n)^(2/3)`.  Consequently the budget tends to
zero along the rough branch.

The main arithmetic statement is `rough_budget_tendsto_zero`; the reduction to
the C3 small-budget inequality is
`eventually_heps_le_of_rough` and the packaged input record is
`eventually_concreteC3RealInputs_of_rough`.

There is no `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose`.
-/

noncomputable section

namespace Cogentic.RandomizedConcreteC3Rough

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Finset Filter
open Cogentic.RandomizedConcreteC3Budget
open Cogentic.RandomizedConcreteC3Real
open Cogentic.RandomizedConcreteC3Real.ConcreteC3RealInputs
open Cogentic.RandomizedConcreteFormSpec
open Cogentic.RandomizedDirectClassSampler
open Cogentic.RandomizedEpochTV
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedSmallPrimePrepass
open scoped BigOperators ENNReal Topology

/-! ## Section 1: Rough bounds on the two prime sums -/

/-- On a `B`-rough integer with `B ≥ 2`, the missing-root prime sum satisfies
`∑_{p | n} 4/(p - 1) ≤ 8 (log n / log B) / B`. -/
theorem sum_four_div_pred_le_rough {B : ℝ} {n : ℕ} (hB : 2 ≤ B)
    (hrough : ∀ p ∈ n.primeFactors, B ≤ (p : ℝ)) :
    ∑ p ∈ n.primeFactors, 4 / ((p : ℝ) - 1) ≤
      8 * (Real.log n / Real.log B) / B := by
  have hB1 : 1 < B := by linarith
  have hBpos : 0 < B := by linarith
  have hBm1pos : 0 < B - 1 := by linarith
  have hstep : ∀ p ∈ n.primeFactors, 4 / ((p : ℝ) - 1) ≤ 8 / B := by
    intro p hp
    have hpge : B ≤ (p : ℝ) := hrough p hp
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    have h1 : 4 / ((p : ℝ) - 1) ≤ 4 / (B - 1) :=
      div_le_div_of_nonneg_left (by norm_num) hBm1pos (sub_le_sub_right hpge 1)
    have h2 : 4 / (B - 1) ≤ 8 / B := by
      have hhalf : B / 2 ≤ B - 1 := by linarith
      have hhalfpos : 0 < B / 2 := by positivity
      calc
        4 / (B - 1) ≤ 4 / (B / 2) :=
          div_le_div_of_nonneg_left (by norm_num) hhalfpos hhalf
        _ = 8 / B := by ring
    exact h1.trans h2
  calc
    ∑ p ∈ n.primeFactors, 4 / ((p : ℝ) - 1)
        ≤ ∑ _p ∈ n.primeFactors, 8 / B := Finset.sum_le_sum hstep
    _ = (n.primeFactors.card : ℝ) * (8 / B) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.log n / Real.log B) * (8 / B) := by
      exact mul_le_mul_of_nonneg_right
        (primeFactors_card_le_log_div hB1 hrough) (by positivity)
    _ = 8 * (Real.log n / Real.log B) / B := by ring

/-! ## Section 2: The rough upper bound for the sampler-free budget -/

/-- The normalized rough upper bound for the sampler-free critical-line budget. -/
noncomputable def roughBudgetBound (n : ℕ) : ℝ :=
  1024 * (Real.log (2 * (n : ℝ))) ^ (83 : ℕ) /
    (roughThreshold n * logB n)

/-- On the rough branch, the sampler-free critical-line budget is at most
`1024 (log (2n))^83 / (B log B)`, with `B = roughThreshold n`.

The numerator `directMissingRootMass (realSpec n hN)` is exactly the right-hand
side of `missing_root_sum_le_log_pow` at the real specification, and
`criticalLineGcdBudget` already contains the critical-line class-number lower
bound `reducedForms_card_lower_from_critical_line` in its denominator. -/
theorem criticalLineGcdBudget_le_rough {n : ℕ} (hN : Odd n) (h2 : 2 ≤ n)
    (hB : 2 ≤ roughThreshold n) (hrough : IsRough (roughThreshold n) n) :
    criticalLineGcdBudget n hN ≤ roughBudgetBound n := by
  set B : ℝ := roughThreshold n with hBdef
  set L : ℝ := Real.log (2 * (n : ℝ)) with hLdef
  have hnposNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
  have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hLpos : 0 < L := by
    rw [hLdef]
    exact zero_lt_one.trans (one_lt_log_two_mul h2)
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    exact (one_lt_log_two_mul h2).le
  have hBpos : 0 < B := by rw [hBdef]; linarith
  have hB1 : 1 < B := by linarith
  have hlogBpos : 0 < Real.log B := Real.log_pos hB1
  have hlogB_eq : Real.log B = logB n := by
    rw [hBdef]
    exact Real.log_exp _
  have hlogBnpos : 0 < logB n := by
    rw [← hlogB_eq]
    exact hlogBpos
  have hlogBnne : logB n ≠ 0 := hlogBnpos.ne'
  have hdenpos : 0 < B * logB n := mul_pos hBpos hlogBnpos
  have hroughle : ∀ p ∈ n.primeFactors, B ≤ (p : ℝ) := by
    intro p hp
    rw [hBdef]
    exact (hrough p hp).le
  have hsumOne :
      ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) ≤ Real.log n / (B * logB n) := by
    have h := sum_inv_primeFactors_le hB1 hroughle
    rw [hlogB_eq] at h
    calc
      ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)
          ≤ (Real.log n / logB n) / B := h
      _ = Real.log n / (B * logB n) := by
        field_simp [hBpos.ne', hlogBnne]
  have hsumFour :
      ∑ p ∈ n.primeFactors, 4 / ((p : ℝ) - 1) ≤
        8 * Real.log n / (B * logB n) := by
    have h := sum_four_div_pred_le_rough hB hroughle
    rw [hlogB_eq] at h
    calc
      ∑ p ∈ n.primeFactors, 4 / ((p : ℝ) - 1)
          ≤ 8 * (Real.log n / logB n) / B := h
      _ = 8 * Real.log n / (B * logB n) := by
        field_simp [hBpos.ne', hlogBnne]
  set U : ℝ := (leadingBound n : ℝ) with hUdef
  have hU1 : 1 ≤ U := by
    rw [hUdef]
    exact_mod_cast one_le_leadingBound h2
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hU_le : U ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [hUdef]
    exact leadingBound_le_two_sqrt hnposNat
  have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt hnpos.le, Real.sqrt_nonneg (n : ℝ)]
  have hlogU_le : Real.log U ≤ L := by
    rw [hLdef]
    apply Real.log_le_log hUpos
    calc
      U ≤ 2 * Real.sqrt (n : ℝ) := hU_le
      _ ≤ 2 * (n : ℝ) := by linarith
  have h1logU_le : 1 + Real.log U ≤ 2 * L := by linarith
  have hUfac : 2 * U * (1 + Real.log U) ≤ 8 * Real.sqrt (n : ℝ) * L := by
    calc
      2 * U * (1 + Real.log U) = (2 * U) * (1 + Real.log U) := by ring
      _ ≤ (4 * Real.sqrt (n : ℝ)) * (2 * L) := by
        refine mul_le_mul ?_ h1logU_le ?_ ?_
        · linarith
        · positivity
        · positivity
      _ = 8 * Real.sqrt (n : ℝ) * L := by ring
  have hSnn : 0 ≤ ∑ p ∈ n.primeFactors, 4 / ((p : ℝ) - 1) := by
    apply Finset.sum_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hM :
      directMissingRootMass (realSpec n hN) ≤
        64 * Real.sqrt (n : ℝ) * Real.log n * L ^ (81 : ℕ) / (B * logB n) := by
    rw [directMissingRootMass_realSpec]
    calc
      2 * (leadingBound n : ℝ) * (1 + Real.log (leadingBound n : ℝ)) *
          (∑ p ∈ n.primeFactors, 4 / ((p : ℝ) - 1)) * L ^ (80 : ℕ)
          = (2 * U * (1 + Real.log U)) *
              (∑ p ∈ n.primeFactors, 4 / ((p : ℝ) - 1)) * L ^ (80 : ℕ) := by
            rw [hUdef]
      _ ≤ (8 * Real.sqrt (n : ℝ) * L) *
            (8 * Real.log n / (B * logB n)) * L ^ (80 : ℕ) := by
            refine mul_le_mul ?_ le_rfl ?_ ?_
            · exact mul_le_mul hUfac hsumFour hSnn (by positivity)
            · positivity
            · positivity
      _ = 64 * Real.sqrt (n : ℝ) * Real.log n * L ^ (81 : ℕ) /
            (B * logB n) := by
            rw [show (81 : ℕ) = 80 + 1 by norm_num, pow_succ]
            field_simp [hBpos.ne', hlogBnne]
            ring
  have hlogNnonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg h1n.le
  have hcoef : 0 ≤ 8 * Real.log (n : ℝ) / Real.sqrt (n : ℝ) := by
    apply div_nonneg
    · linarith
    · positivity
  have hterm1 :
      8 * Real.log (n : ℝ) * directMissingRootMass (realSpec n hN) /
          Real.sqrt (n : ℝ) ≤
        512 * (Real.log (n : ℝ)) ^ 2 * L ^ (81 : ℕ) / (B * logB n) := by
    calc
      8 * Real.log (n : ℝ) * directMissingRootMass (realSpec n hN) /
          Real.sqrt (n : ℝ)
          = (8 * Real.log (n : ℝ) / Real.sqrt (n : ℝ)) *
              directMissingRootMass (realSpec n hN) := by ring
      _ ≤ (8 * Real.log (n : ℝ) / Real.sqrt (n : ℝ)) *
            (64 * Real.sqrt (n : ℝ) * Real.log n * L ^ (81 : ℕ) /
              (B * logB n)) :=
          mul_le_mul_of_nonneg_left hM hcoef
      _ = 512 * (Real.log (n : ℝ)) ^ 2 * L ^ (81 : ℕ) / (B * logB n) := by
          have hsqrtne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
          have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
            rw [← sq, Real.sq_sqrt hnpos.le]
          field_simp [hsqrtne, hBpos.ne', hlogBnne]
          nlinarith [hsq]
  have hlog_le_L : Real.log (n : ℝ) ≤ L := by
    rw [hLdef]
    apply Real.log_le_log hnpos
    linarith
  have hnum1 : 512 * (Real.log (n : ℝ)) ^ 2 * L ^ (81 : ℕ) ≤ 512 * L ^ (83 : ℕ) := by
    have hsq : (Real.log (n : ℝ)) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ hlogNnonneg hlog_le_L 2
    calc
      512 * (Real.log (n : ℝ)) ^ 2 * L ^ (81 : ℕ)
          = 512 * ((Real.log (n : ℝ)) ^ 2 * L ^ (81 : ℕ)) := by ring
      _ ≤ 512 * (L ^ 2 * L ^ (81 : ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hsq (pow_nonneg hLpos.le _)
      _ = 512 * L ^ (83 : ℕ) := by
          congr 1
          rw [← pow_add]
  have hnum2 : Real.log (n : ℝ) ≤ L ^ (83 : ℕ) := by
    have hLL : L ≤ L ^ (83 : ℕ) := by
      calc
        L = L ^ (1 : ℕ) := (pow_one L).symm
        _ ≤ L ^ (83 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
    exact hlog_le_L.trans hLL
  have hcombined :
      512 * (Real.log (n : ℝ)) ^ 2 * L ^ (81 : ℕ) / (B * logB n) +
          Real.log (n : ℝ) / (B * logB n) ≤
        1024 * L ^ (83 : ℕ) / (B * logB n) := by
    have h1 := div_le_div_of_nonneg_right hnum1 hdenpos.le
    have h2 := div_le_div_of_nonneg_right hnum2 hdenpos.le
    have htotal := add_le_add h1 h2
    have hL83pos : 0 < L ^ (83 : ℕ) := pow_pos hLpos _
    calc
      512 * (Real.log (n : ℝ)) ^ 2 * L ^ (81 : ℕ) / (B * logB n) +
          Real.log (n : ℝ) / (B * logB n)
          ≤ 512 * L ^ (83 : ℕ) / (B * logB n) +
              L ^ (83 : ℕ) / (B * logB n) := htotal
      _ = 513 * L ^ (83 : ℕ) / (B * logB n) := by ring
      _ ≤ 1024 * L ^ (83 : ℕ) / (B * logB n) := by
          apply div_le_div_of_nonneg_right _ hdenpos.le
          nlinarith
  calc
    criticalLineGcdBudget n hN
        = 8 * Real.log (n : ℝ) * directMissingRootMass (realSpec n hN) /
            Real.sqrt (n : ℝ) +
            (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)) :=
          criticalLineGcdBudget_eq n hN h2
    _ ≤ 512 * (Real.log (n : ℝ)) ^ 2 * L ^ (81 : ℕ) / (B * logB n) +
          Real.log (n : ℝ) / (B * logB n) := add_le_add hterm1 hsumOne
    _ ≤ 1024 * L ^ (83 : ℕ) / (B * logB n) := hcombined
    _ = roughBudgetBound n := by
          unfold roughBudgetBound
          rw [hBdef, hLdef]

/-! ## Section 3: The rough budget tends to zero -/

/-- **The key rough arithmetic estimate.**  `1024 (log (2n))^83 / (B log B)`
tends to zero, where `B = roughThreshold n = exp((log n)^(2/3))`. -/
theorem rough_budget_tendsto_zero : Tendsto roughBudgetBound atTop (𝓝 0) := by
  have hpoly := poly_log_two_mul_div_exp_logB_tendsto_zero 83
  have hpoly' :
      Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ)) ^ (83 : ℕ) / roughThreshold n)
        atTop (𝓝 0) := by
    simpa [roughThreshold] using hpoly
  have hinv : Tendsto (fun n : ℕ => (logB n)⁻¹) atTop (𝓝 0) :=
    logB_grows.inv_tendsto_atTop
  have hprod :
      Tendsto (fun n : ℕ =>
        (Real.log (2 * (n : ℝ)) ^ (83 : ℕ) / roughThreshold n) * (logB n)⁻¹)
        atTop (𝓝 0) := by
    simpa using hpoly'.mul hinv
  have htarget :
      Tendsto (fun n : ℕ =>
        1024 * ((Real.log (2 * (n : ℝ)) ^ (83 : ℕ) / roughThreshold n) *
          (logB n)⁻¹)) atTop (𝓝 0) := by
    simpa using hprod.const_mul 1024
  have heq : roughBudgetBound =ᶠ[atTop]
      (fun n : ℕ =>
        1024 * ((Real.log (2 * (n : ℝ)) ^ (83 : ℕ) / roughThreshold n) *
          (logB n)⁻¹)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos h1n
    have hlogBne : logB n ≠ 0 := (Real.rpow_pos_of_pos hlogpos _).ne'
    have hBne : roughThreshold n ≠ 0 := (Real.exp_pos _).ne'
    unfold roughBudgetBound
    field_simp [hBne, hlogBne]
  exact (tendsto_congr' heq).mpr htarget

/-! ## Section 4: The budget inequality on the rough branch -/

/-- Eventually, every odd `n ≥ 2` with `roughThreshold n`-rough prime factors
has sampler-free critical-line budget at most `1/32`. -/
theorem eventually_criticalLineGcdBudget_le_one_div_thirty_two :
    ∀ᶠ n : ℕ in atTop, ∀ (hN : Odd n), 2 ≤ n →
      IsRough (roughThreshold n) n → criticalLineGcdBudget n hN ≤ 1 / 32 := by
  have hsmall : ∀ᶠ n : ℕ in atTop, roughBudgetBound n ≤ 1 / 32768 :=
    rough_budget_tendsto_zero.eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 32768))
  filter_upwards [hsmall, eventually_ge_atTop 2,
    roughThreshold_grows.eventually_ge_atTop 2] with n hsmall_n hn2 hB2 hN h2 hrough
  have hbound := criticalLineGcdBudget_le_rough hN h2 hB2 hrough
  linarith

/-- **Eventual `heps_le` on the rough branch.**  Under
`DirichletLZerosOnLine`, every sufficiently large odd `n ≥ 3` whose prime
factors all exceed `roughThreshold n` satisfies the real C3 small-budget
inequality. -/
theorem eventually_heps_le_of_rough (line : DirichletLZerosOnLine) :
    ∀ᶠ n : ℕ in atTop, ∀ (hN : Odd n), 3 ≤ n →
      IsRough (roughThreshold n) n →
        directSamplerEpsilon (realSpec n hN) realEta (realGcdMass n hN) ≤ 1 / 32 := by
  obtain ⟨N₀, hN₀⟩ := heps_le_of_criticalLineGcdBudget line
  filter_upwards [eventually_criticalLineGcdBudget_le_one_div_thirty_two,
    eventually_ge_atTop N₀] with n hbudget hnN₀ hN h3 hrough
  exact hN₀ n hnN₀ hN (by omega) (hbudget hN (by omega) hrough)

/-- The same statement in terms of the residual real budget
`realBudget n hN = missing-root ratio + gcd-exit mass`. -/
theorem eventually_realBudget_le_of_rough (line : DirichletLZerosOnLine) :
    ∀ᶠ n : ℕ in atTop, ∀ (hN : Odd n), 3 ≤ n →
      IsRough (roughThreshold n) n → realBudget n hN ≤ 1 / 32 := by
  filter_upwards [eventually_heps_le_of_rough line] with n hn hN h3 hrough
  exact (heps_le_iff_realBudget n hN).mp (hn hN h3 hrough)

/-- **Eventual real C3 inputs on the rough branch.**  Under
`DirichletLZerosOnLine`, every sufficiently large odd `n ≥ 2` whose prime
factors all exceed `roughThreshold n` carries a fully discharged
`ConcreteC3RealInputs` record. -/
theorem eventually_concreteC3RealInputs_of_rough (line : DirichletLZerosOnLine) :
    ∀ᶠ n : ℕ in atTop, ∀ (hN : Odd n) (h2 : 2 ≤ n),
      IsRough (roughThreshold n) n → Nonempty (ConcreteC3RealInputs n hN h2) := by
  filter_upwards [eventually_heps_le_of_rough line] with n hn hN h2 hrough
  have h3 : 3 ≤ n := by
    rcases hN with ⟨k, rfl⟩
    omega
  exact ⟨RealC3BudgetInputs.toConcreteC3RealInputs ⟨hn hN h3 hrough⟩⟩

/-! ## Section 5: Axiom audit -/

#print axioms Cogentic.RandomizedConcreteC3Rough.sum_four_div_pred_le_rough
#print axioms Cogentic.RandomizedConcreteC3Rough.criticalLineGcdBudget_le_rough
#print axioms Cogentic.RandomizedConcreteC3Rough.rough_budget_tendsto_zero
#print axioms Cogentic.RandomizedConcreteC3Rough.eventually_criticalLineGcdBudget_le_one_div_thirty_two
#print axioms Cogentic.RandomizedConcreteC3Rough.eventually_heps_le_of_rough
#print axioms Cogentic.RandomizedConcreteC3Rough.eventually_realBudget_le_of_rough
#print axioms Cogentic.RandomizedConcreteC3Rough.eventually_concreteC3RealInputs_of_rough

end Cogentic.RandomizedConcreteC3Rough
