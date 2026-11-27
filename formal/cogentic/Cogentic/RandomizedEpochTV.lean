import Cogentic.RandomizedEpochAssembly
import Cogentic.RandomizedDirectClassSampler
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete total-variation budget for an epoch built from the direct class sampler

This module turns the direct reduced-class sampler estimates of
`Cogentic.RandomizedDirectClassSampler` into the explicit `ε` field consumed by
`HardEpochData.assembledAttempt_hit_prob_ge` and hence by
`HardEpochAsymptoticBound`.

The main concrete budget is

```
directSamplerEpsilon spec η gcdMass
  = directMissingRootMass spec / #(spec.allForms) + gcdMass + η
```

where

* `directMissingRootMass spec` is the missing-root numerator supplied by
  `directRetryConditionalPMF_tv_le`, further bounded by
  `2 * U * (1 + log U) * (log (2N))^160` using
  `primeFactors_local_prod_le_log_pow`;
* `gcdMass` is an explicit budget for the one-attempt gcd-exit probability
  `(gcdExitProb spec J).toReal`.  The estimate is kept as a hypothesis: the
  shared source `RandomizedDirectClassSampler.lean` currently has two failed
  tactic proofs in `gcdExitProb_toReal_le_scaled`, so those declarations are not
  available without `sorryAx`.  The conditional-law TV bound below does not
  consume this term (a caller may set `gcdMass = 0`), but the additive shape
  `missing-root + gcd-exit + finite-sampling` is the one used by the blueprint;
* `η` is the finite-sampling error, i.e. the TV distance between the ideal class
  law and the uniform law on `spec.allForms`.  When the ideal law is uniform on
  the whole finite type, `η` is exactly `finiteSamplingError spec` by
  `pmfTotalVariation_uniformOfFinset_uniformOfFintype`.

The last section composes the estimate with
`HardEpochData.assembledAttempt_hit_prob_ge`: if an epoch's actual law is the
direct sampler and its ideal law is `η`-close to uniform on the class group,
then the verified-split lower bound `γ / 2 - ε` holds with the concrete `ε`
above.  No `sorry`, `admit`, `axiom`, `native_decide`, or use of the broken
`gcdExitProb_toReal_le{,_scaled}` lemmas occurs in this file.

Build note.  At the pinned commit the shared module
`RandomizedDirectClassSampler` has two failing proofs inside
`gcdExitProb_toReal_le_scaled` (the `ring` and `omega` steps around lines
2926–2927 under the pinned toolchain), so its `.olean` cannot be produced from
the committed source as-is.  This file only uses the earlier declarations
(`directRetryConditionalPMF_tv_le`, `missing_root_sum_le_log_pow`,
`primeFactors_local_prod_le_log_pow`, `pmfTotalVariation_uniformOfFinset_subset`,
etc.), which elaborate cleanly; the gcd-exit estimate is an explicit hypothesis.
No shared source file was modified.
-/

namespace Cogentic.RandomizedEpochTV

open Cogentic.RandomizedDirectClassSampler
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedSamplerTransfer
open scoped BigOperators

/-! ## Total-variation infrastructure -/

/-- Triangle inequality for the discrete total-variation distance. -/
theorem pmfTotalVariation_triangle {B : Type*} [Fintype B] (p q r : PMF B) :
    pmfTotalVariation p r ≤ pmfTotalVariation p q + pmfTotalVariation q r := by
  rw [pmfTotalVariation_eq_totalVariation, pmfTotalVariation_eq_totalVariation,
    pmfTotalVariation_eq_totalVariation]
  unfold totalVariation
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro z _
  have h : (p z).toReal - (r z).toReal =
      ((p z).toReal - (q z).toReal) + ((q z).toReal - (r z).toReal) := by ring
  rw [h]
  exact abs_add_le _ _

/-- Symmetry of the discrete total-variation distance. -/
theorem pmfTotalVariation_comm {B : Type*} (p q : PMF B) :
    pmfTotalVariation p q = pmfTotalVariation q p := by
  unfold pmfTotalVariation
  congr 1
  exact tsum_congr fun z => abs_sub_comm _ _

/-- Total variation of a law with itself vanishes. -/
theorem pmfTotalVariation_self {B : Type*} (p : PMF B) :
    pmfTotalVariation p p = 0 := by
  unfold pmfTotalVariation
  simp

/-- For a finite family of nonnegative reals, the sum is at most the product of
`1 + x i`.  This is the elementary step that turns the reciprocal-prime sum in
`directRetryConditionalPMF_tv_le` into the product bounded by
`primeFactors_local_prod_le_log_pow`. -/
theorem Finset.sum_le_prod_one_add {ι : Type*} (s : Finset ι) {x : ι → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, x i) ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hP : 1 ≤ ∏ i ∈ s, (1 + x i) :=
      Finset.one_le_prod (s := s) (f := fun i => 1 + x i)
        (fun i hi => by linarith [hs i hi])
    have hsum : (∑ i ∈ s, x i) ≤ ∏ i ∈ s, (1 + x i) := ih hs
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have hxm : x a ≤ x a * ∏ i ∈ s, (1 + x i) := by
      have hnn : 0 ≤ x a * (∏ i ∈ s, (1 + x i) - 1) :=
        mul_nonneg hxa (by linarith)
      nlinarith
    nlinarith

/-! ## The explicit missing-root mass -/

/-- The missing-root numerator from `directRetryConditionalPMF_tv_le`:
`2 U (1 + log U) * (∑_{p | N} 4/(p-1)) * (log (2N))^80`. -/
noncomputable def directMissingRootMass {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) : ℝ :=
  2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
    (∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1)) *
    (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ)

/-- The missing-root numerator is nonnegative for `N ≥ 2`, `U ≥ 1`. -/
theorem directMissingRootMass_nonneg {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U) :
    0 ≤ directMissingRootMass spec := by
  unfold directMissingRootMass
  have hU1 : (1 : ℝ) ≤ (spec.U : ℝ) := by exact_mod_cast hU
  have hlogU : 0 ≤ 1 + Real.log (spec.U : ℝ) := by
    linarith [Real.log_nonneg hU1]
  have hL : 0 < Real.log (2 * (spec.N : ℝ)) :=
    zero_lt_one.trans (one_lt_log_two_mul hN)
  have hsum : 0 ≤ ∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1) := by
    apply Finset.sum_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  positivity

/-- The missing-root numerator is at most `2 U (1 + log U) * (log (2N))^160`.
The reciprocal-prime sum is absorbed into the product
`∏_{p | N} (1 + 4/(p-1))`, bounded by `(log (2N))^80`. -/
theorem directMissingRootMass_le_log_pow {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (hN : 2 ≤ spec.N) :
    directMissingRootMass spec ≤
      2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
        (Real.log (2 * (spec.N : ℝ))) ^ (160 : ℕ) := by
  unfold directMissingRootMass
  have hLpos : 0 < Real.log (2 * (spec.N : ℝ)) :=
    zero_lt_one.trans (one_lt_log_two_mul hN)
  have hterm_nn : ∀ p ∈ spec.N.primeFactors, 0 ≤ 4 / ((p : ℝ) - 1) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hsum_nn : 0 ≤ ∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1) :=
    Finset.sum_nonneg hterm_nn
  have hsum_prod :
      (∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1)) ≤
        ∏ p ∈ spec.N.primeFactors, (1 + 4 / ((p : ℝ) - 1)) :=
    Finset.sum_le_prod_one_add spec.N.primeFactors hterm_nn
  have hprod := primeFactors_local_prod_le_log_pow hN
  have hsum_le :
      (∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1)) ≤
        (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ) := hsum_prod.trans hprod
  have hAU : 0 ≤ 2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) := by
    rcases Nat.eq_zero_or_pos spec.U with h0 | hpos
    · simp [h0]
    · have hU1 : (1 : ℝ) ≤ (spec.U : ℝ) := by exact_mod_cast hpos
      have : 0 ≤ 1 + Real.log (spec.U : ℝ) := by
        linarith [Real.log_nonneg hU1]
      positivity
  have hpow_nn : 0 ≤ (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ) := pow_nonneg hLpos.le _
  calc
    2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
        (∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1)) *
        (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ)
      ≤ 2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
          (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ) *
          (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ hpow_nn
        exact mul_le_mul_of_nonneg_left hsum_le hAU
    _ = 2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
          (Real.log (2 * (spec.N : ℝ))) ^ (160 : ℕ) := by
        rw [mul_assoc, ← pow_add]

/-- **Explicit direct-sampler TV bound against the uniform law on the class
group.**  This is `directRetryConditionalPMF_tv_le` with the missing-root
numerator packaged as `directMissingRootMass spec`. -/
theorem directRetryConditionalPMF_tv_le_directMissingRootMass {Form : Type*}
    [DecidableEq Form] (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2)) :
    pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
      (PMF.uniformOfFinset spec.allForms hall) ≤
      directMissingRootMass spec / (spec.allForms.card : ℝ) := by
  simpa [directMissingRootMass] using
    directRetryConditionalPMF_tv_le spec hUJ hJ₀ hcop hall hN hU R hR_ge hR1 hRmul
      hRcop hRloc

/-- The same bound with the fully explicit `(log (2N))^160` numerator. -/
theorem directRetryConditionalPMF_tv_le_log_pow {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2)) :
    pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
      (PMF.uniformOfFinset spec.allForms hall) ≤
      (2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
        (Real.log (2 * (spec.N : ℝ))) ^ (160 : ℕ)) /
        (spec.allForms.card : ℝ) := by
  refine (directRetryConditionalPMF_tv_le_directMissingRootMass spec hUJ hJ₀ hcop hall hN
    hU R hR_ge hR1 hRmul hRcop hRloc).trans ?_
  exact div_le_div_of_nonneg_right (directMissingRootMass_le_log_pow spec hN)
    (Nat.cast_nonneg _)

/-! ## Finite-sampling error and the full `ε` budget -/

/-- Finite-sampling error: TV between the uniform law on `spec.allForms` and the
uniform law on the whole finite type. -/
noncomputable def finiteSamplingError {Form : Type*} [DecidableEq Form] [Fintype Form]
    (spec : DirectFormSpec Form) : ℝ :=
  ((Fintype.card Form - spec.allForms.card : ℕ) : ℝ) / (Fintype.card Form : ℝ)

/-- The concrete TV budget `ε = missing-root + gcd-exit + finite-sampling`. -/
noncomputable def directSamplerEpsilon {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (η gcdMass : ℝ) : ℝ :=
  directMissingRootMass spec / (spec.allForms.card : ℝ) + gcdMass + η

/-- The same budget with the missing-root numerator replaced by its explicit
`(log (2N))^160` upper bound. -/
noncomputable def directSamplerEpsilonLogPow {Form : Type*} [DecidableEq Form]
    (spec : DirectFormSpec Form) (η gcdMass : ℝ) : ℝ :=
  (2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
    (Real.log (2 * (spec.N : ℝ))) ^ (160 : ℕ)) /
      (spec.allForms.card : ℝ) + gcdMass + η

/-- **Direct sampler against `uniformOfFintype`.**  The conditional returned-form
law is within missing-root mass plus finite-sampling error of the uniform law on
the whole finite class type. -/
theorem directRetryConditionalPMF_tv_uniformOfFintype_le {Form : Type*}
    [DecidableEq Form] [Fintype Form] [Nonempty Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2)) :
    pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
      (PMF.uniformOfFintype Form) ≤
      directMissingRootMass spec / (spec.allForms.card : ℝ) + finiteSamplingError spec := by
  have htri := pmfTotalVariation_triangle
    (directRetryConditionalPMF spec hUJ hJ₀ hcop)
    (PMF.uniformOfFinset spec.allForms hall)
    (PMF.uniformOfFintype Form)
  have hmiss := directRetryConditionalPMF_tv_le_directMissingRootMass spec hUJ hJ₀ hcop hall
    hN hU R hR_ge hR1 hRmul hRcop hRloc
  have hunif := pmfTotalVariation_uniformOfFinset_uniformOfFintype
    (Ω := Form) (S := spec.allForms) hall
  calc
    pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
        (PMF.uniformOfFintype Form)
      ≤ pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
          (PMF.uniformOfFinset spec.allForms hall) +
        pmfTotalVariation (PMF.uniformOfFinset spec.allForms hall)
          (PMF.uniformOfFintype Form) := htri
    _ ≤ directMissingRootMass spec / (spec.allForms.card : ℝ) + finiteSamplingError spec := by
        rw [hunif]
        exact add_le_add hmiss le_rfl

/-- **Requested concrete shape.**  The conditional direct-sampler law against the
uniform law on the whole finite class type is at most the full budget
`missing-root + gcd-exit + finite-sampling`. -/
theorem directRetryConditionalPMF_tv_uniformOfFintype_le_budget {Form : Type*}
    [DecidableEq Form] [Fintype Form] [Nonempty Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2))
    {gcdMass : ℝ} (hgcd : (gcdExitProb spec J).toReal ≤ gcdMass) :
    pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
      (PMF.uniformOfFintype Form) ≤
      directSamplerEpsilon spec (finiteSamplingError spec) gcdMass := by
  have hgcd_nonneg : 0 ≤ gcdMass := ENNReal.toReal_nonneg.trans hgcd
  refine (directRetryConditionalPMF_tv_uniformOfFintype_le spec hUJ hJ₀ hcop hall hN hU R
    hR_ge hR1 hRmul hRcop hRloc).trans ?_
  unfold directSamplerEpsilon
  linarith

/-- The requested shape with the fully explicit `(log (2N))^160` numerator. -/
theorem directRetryConditionalPMF_tv_uniformOfFintype_le_log_pow {Form : Type*}
    [DecidableEq Form] [Fintype Form] [Nonempty Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2))
    {gcdMass : ℝ} (hgcd : (gcdExitProb spec J).toReal ≤ gcdMass) :
    pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
      (PMF.uniformOfFintype Form) ≤
      directSamplerEpsilonLogPow spec (finiteSamplingError spec) gcdMass := by
  have hgcd_nonneg : 0 ≤ gcdMass := ENNReal.toReal_nonneg.trans hgcd
  have hmiss := directRetryConditionalPMF_tv_le_log_pow spec hUJ hJ₀ hcop hall hN hU R
    hR_ge hR1 hRmul hRcop hRloc
  have hunif := pmfTotalVariation_uniformOfFinset_uniformOfFintype
    (Ω := Form) (S := spec.allForms) hall
  have htri := pmfTotalVariation_triangle
    (directRetryConditionalPMF spec hUJ hJ₀ hcop)
    (PMF.uniformOfFinset spec.allForms hall)
    (PMF.uniformOfFintype Form)
  have hbound : pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
      (PMF.uniformOfFintype Form) ≤
      (2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
        (Real.log (2 * (spec.N : ℝ))) ^ (160 : ℕ)) /
        (spec.allForms.card : ℝ) + finiteSamplingError spec := by
    calc
      _ ≤ pmfTotalVariation (directRetryConditionalPMF spec hUJ hJ₀ hcop)
            (PMF.uniformOfFinset spec.allForms hall) +
          pmfTotalVariation (PMF.uniformOfFinset spec.allForms hall)
            (PMF.uniformOfFintype Form) := htri
      _ ≤ _ := by
          rw [hunif]
          exact add_le_add hmiss le_rfl
  refine hbound.trans ?_
  unfold directSamplerEpsilonLogPow
  linarith

/-- **Generic ideal/actual pair.**  If the actual law is the direct sampler, the
ideal law is within `η` of uniform on the class group, and the one-attempt gcd
exit probability is at most `gcdMass`, then the ideal-to-actual TV is at most
`missing-root + gcd-exit + finite-sampling`.

The gcd-exit estimate is an explicit hypothesis because the two lemmas
`gcdExitProb_toReal_le` and `gcdExitProb_toReal_le_scaled` in the shared source
currently depend on `sorryAx` (their proofs fail to elaborate).  The
conditional-law bound itself does not need the gcd term: a caller may take
`gcdMass := (gcdExitProb spec J).toReal` (with `hgcd := le_rfl`) or any explicit
upper bound, and the nonnegativity of `gcdMass` is derived from `hgcd`. -/
theorem pmfTotalVariation_le_directSamplerEpsilon {Form : Type*} [DecidableEq Form]
    [Fintype Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2))
    {ideal : PMF Form} {η gcdMass : ℝ}
    (hideal : pmfTotalVariation ideal (PMF.uniformOfFinset spec.allForms hall) ≤ η)
    (hgcd : (gcdExitProb spec J).toReal ≤ gcdMass) :
    pmfTotalVariation ideal (directRetryConditionalPMF spec hUJ hJ₀ hcop) ≤
      directSamplerEpsilon spec η gcdMass := by
  have hgcd_nonneg : 0 ≤ gcdMass := ENNReal.toReal_nonneg.trans hgcd
  have htri := pmfTotalVariation_triangle ideal (PMF.uniformOfFinset spec.allForms hall)
    (directRetryConditionalPMF spec hUJ hJ₀ hcop)
  have hmiss := directRetryConditionalPMF_tv_le_directMissingRootMass spec hUJ hJ₀ hcop hall
    hN hU R hR_ge hR1 hRmul hRcop hRloc
  have hmiss' : pmfTotalVariation (PMF.uniformOfFinset spec.allForms hall)
      (directRetryConditionalPMF spec hUJ hJ₀ hcop) ≤
      directMissingRootMass spec / (spec.allForms.card : ℝ) := by
    rw [pmfTotalVariation_comm]
    exact hmiss
  calc
    pmfTotalVariation ideal (directRetryConditionalPMF spec hUJ hJ₀ hcop)
      ≤ pmfTotalVariation ideal (PMF.uniformOfFinset spec.allForms hall) +
        pmfTotalVariation (PMF.uniformOfFinset spec.allForms hall)
          (directRetryConditionalPMF spec hUJ hJ₀ hcop) := htri
    _ ≤ η + directMissingRootMass spec / (spec.allForms.card : ℝ) :=
        add_le_add hideal hmiss'
    _ ≤ directSamplerEpsilon spec η gcdMass := by
        unfold directSamplerEpsilon
        linarith

/-- The generic pair bound with the explicit `(log (2N))^160` numerator. -/
theorem pmfTotalVariation_le_directSamplerEpsilonLogPow {Form : Type*}
    [DecidableEq Form] [Fintype Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2))
    {ideal : PMF Form} {η gcdMass : ℝ}
    (hideal : pmfTotalVariation ideal (PMF.uniformOfFinset spec.allForms hall) ≤ η)
    (hgcd : (gcdExitProb spec J).toReal ≤ gcdMass) :
    pmfTotalVariation ideal (directRetryConditionalPMF spec hUJ hJ₀ hcop) ≤
      directSamplerEpsilonLogPow spec η gcdMass := by
  refine (pmfTotalVariation_le_directSamplerEpsilon spec hUJ hJ₀ hcop hall hN hU R hR_ge
    hR1 hRmul hRcop hRloc hideal hgcd).trans ?_
  unfold directSamplerEpsilon directSamplerEpsilonLogPow
  have hnum := directMissingRootMass_le_log_pow spec hN
  have hcard : (0 : ℝ) ≤ (spec.allForms.card : ℝ) := Nat.cast_nonneg _
  have hterm : directMissingRootMass spec / (spec.allForms.card : ℝ) ≤
      (2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
        (Real.log (2 * (spec.N : ℝ))) ^ (160 : ℕ)) /
        (spec.allForms.card : ℝ) :=
    div_le_div_of_nonneg_right hnum hcard
  linarith

/-- Variant with the gcd-exit estimate in the exact form of
`gcdExitProb_toReal_le`: the extra budget is the reciprocal-prime sum
`∑_{p | N} 1/p`, stated as an explicit hypothesis. -/
theorem pmfTotalVariation_le_directSamplerEpsilon_recip {Form : Type*}
    [DecidableEq Form] [Fintype Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2))
    {ideal : PMF Form} {η : ℝ}
    (hideal : pmfTotalVariation ideal (PMF.uniformOfFinset spec.allForms hall) ≤ η)
    (hgcd : (gcdExitProb spec J).toReal ≤
      ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ)) :
    pmfTotalVariation ideal (directRetryConditionalPMF spec hUJ hJ₀ hcop) ≤
      directMissingRootMass spec / (spec.allForms.card : ℝ) +
        (∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ)) + η := by
  simpa [directSamplerEpsilon] using
    pmfTotalVariation_le_directSamplerEpsilon spec hUJ hJ₀ hcop hall hN hU R hR_ge
      hR1 hRmul hRcop hRloc (η := η)
      (gcdMass := ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ)) hideal hgcd

/-- Fully explicit log-power form of the reciprocal-prime budget: both the
missing-root term and the gcd-exit term are absorbed into powers of `log (2N)`. -/
theorem pmfTotalVariation_le_directSamplerEpsilon_recip_log_pow {Form : Type*}
    [DecidableEq Form] [Fintype Form]
    (spec : DirectFormSpec Form) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hN : 2 ≤ spec.N) (hU : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2))
    {ideal : PMF Form} {η : ℝ}
    (hideal : pmfTotalVariation ideal (PMF.uniformOfFinset spec.allForms hall) ≤ η)
    (hgcd : (gcdExitProb spec J).toReal ≤
      ∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ)) :
    pmfTotalVariation ideal (directRetryConditionalPMF spec hUJ hJ₀ hcop) ≤
      (2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
        (Real.log (2 * (spec.N : ℝ))) ^ (160 : ℕ)) /
        (spec.allForms.card : ℝ) +
        (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ) + η := by
  refine (pmfTotalVariation_le_directSamplerEpsilon_recip spec hUJ hJ₀ hcop hall hN hU R
    hR_ge hR1 hRmul hRcop hRloc hideal hgcd).trans ?_
  have hLpos : 0 < Real.log (2 * (spec.N : ℝ)) :=
    zero_lt_one.trans (one_lt_log_two_mul hN)
  have hrecip_le_four :
      (∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
        ∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_le_div_iff₀ hp0 hp1]
    linarith
  have hterm_nn : ∀ p ∈ spec.N.primeFactors, 0 ≤ 4 / ((p : ℝ) - 1) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hfour_le_log :
      (∑ p ∈ spec.N.primeFactors, 4 / ((p : ℝ) - 1)) ≤
        (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ) :=
    (Finset.sum_le_prod_one_add spec.N.primeFactors hterm_nn).trans
      (primeFactors_local_prod_le_log_pow hN)
  have hrecip_le_log :
      (∑ p ∈ spec.N.primeFactors, (1 : ℝ) / (p : ℝ)) ≤
        (Real.log (2 * (spec.N : ℝ))) ^ (80 : ℕ) :=
    hrecip_le_four.trans hfour_le_log
  have hmiss_le :
      directMissingRootMass spec / (spec.allForms.card : ℝ) ≤
        (2 * (spec.U : ℝ) * (1 + Real.log (spec.U : ℝ)) *
          (Real.log (2 * (spec.N : ℝ))) ^ (160 : ℕ)) /
          (spec.allForms.card : ℝ) :=
    div_le_div_of_nonneg_right (directMissingRootMass_le_log_pow spec hN)
      (Nat.cast_nonneg _)
  linarith

/-! ## Composition with `HardEpochData.assembledAttempt_hit_prob_ge` -/

/-- **Epoch-level composition.**  Suppose the actual law of a hard-input epoch is
the direct sampler and its ideal law is within `η` of uniform on the class group,
with a gcd-exit budget `gcdMass`.  Then the verified-split probability is at
least `γ / 2 - directSamplerEpsilon spec η gcdMass`.  This is exactly
`assembledAttempt_hit_prob_ge` with the concrete TV field supplied by
`pmfTotalVariation_le_directSamplerEpsilon`. -/
theorem assembledAttempt_hit_prob_ge_of_directSampler {N : ℕ} (E : HardEpochData N)
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬IsPrimePow N)
    (hcheck : E.CongruenceCheck) (huniform : E.HiddenUniform)
    [DecidableEq E.Sample] [Fintype E.Sample] [Nonempty E.Sample]
    (spec : DirectFormSpec E.Sample) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hNspec : 2 ≤ spec.N) (hUspec : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2))
    (hactual : E.actual = directRetryConditionalPMF spec hUJ hJ₀ hcop)
    {η gcdMass γ : ℝ}
    (hideal : pmfTotalVariation E.ideal (PMF.uniformOfFinset spec.allForms hall) ≤ η)
    (hgcd : (gcdExitProb spec J).toReal ≤ gcdMass)
    (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (E.ideal.toOuterMeasure {x | observe E.trace x ∈ E.good}).toReal) :
    γ / 2 - directSamplerEpsilon spec η gcdMass ≤
      ((E.actual.map (E.assembledAttempt hN)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
  have hTV : pmfTotalVariation E.ideal E.actual ≤ directSamplerEpsilon spec η gcdMass := by
    rw [hactual]
    exact pmfTotalVariation_le_directSamplerEpsilon spec hUJ hJ₀ hcop hall hNspec hUspec
      R hR_ge hR1 hRmul hRcop hRloc hideal hgcd
  exact E.assembledAttempt_hit_prob_ge hN ho hnot hcheck huniform hγ₀ hγ hTV

/-- Exact-law specialization: if the epoch's actual law is the direct sampler and
its ideal law is exactly uniform on `spec.allForms`, then the concrete missing-root
mass already suffices (no gcd or finite-sampling slack needed). -/
theorem assembledAttempt_hit_prob_ge_of_directSampler_uniform {N : ℕ}
    (E : HardEpochData N) (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬IsPrimePow N)
    (hcheck : E.CongruenceCheck) (huniform : E.HiddenUniform)
    [DecidableEq E.Sample] [Fintype E.Sample] [Nonempty E.Sample]
    (spec : DirectFormSpec E.Sample) {J J₀ : ℕ}
    (hUJ : spec.U ≤ 2 ^ J) (hJ₀ : 1 ≤ J₀)
    (hcop : spec.coprimeForms.Nonempty) (hall : spec.allForms.Nonempty)
    (hNspec : 2 ≤ spec.N) (hUspec : 1 ≤ spec.U)
    (R : ℕ → ℕ) (hR_ge : ∀ A ∈ Finset.Icc 1 spec.U, (spec.roots A).card ≤ R A)
    (hR1 : R 1 = 1) (hRmul : ∀ a b, Nat.Coprime a b → R (a * b) = R a * R b)
    (hRcop : ∀ m, 1 ≤ m → Nat.Coprime m spec.N → R m ≤ 2 * 2 ^ m.primeFactors.card)
    (hRloc : ∀ p ∈ spec.N.primeFactors, ∀ k, 1 ≤ k → R (p ^ k) ≤ 2 * p ^ (k / 2))
    (hactual : E.actual = directRetryConditionalPMF spec hUJ hJ₀ hcop)
    (hideal : E.ideal = PMF.uniformOfFinset spec.allForms hall)
    {γ : ℝ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (E.ideal.toOuterMeasure {x | observe E.trace x ∈ E.good}).toReal) :
    γ / 2 - directMissingRootMass spec / (spec.allForms.card : ℝ) ≤
      ((E.actual.map (E.assembledAttempt hN)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
  have hTV : pmfTotalVariation E.ideal E.actual ≤
      directMissingRootMass spec / (spec.allForms.card : ℝ) := by
    rw [hactual, hideal, pmfTotalVariation_comm]
    exact directRetryConditionalPMF_tv_le_directMissingRootMass spec hUJ hJ₀ hcop hall
      hNspec hUspec R hR_ge hR1 hRmul hRcop hRloc
  exact E.assembledAttempt_hit_prob_ge hN ho hnot hcheck huniform hγ₀ hγ hTV

end Cogentic.RandomizedEpochTV

#print axioms Cogentic.RandomizedEpochTV.pmfTotalVariation_triangle
#print axioms Cogentic.RandomizedEpochTV.directMissingRootMass_le_log_pow
#print axioms Cogentic.RandomizedEpochTV.directRetryConditionalPMF_tv_le_directMissingRootMass
#print axioms Cogentic.RandomizedEpochTV.directRetryConditionalPMF_tv_le_log_pow
#print axioms Cogentic.RandomizedEpochTV.directRetryConditionalPMF_tv_uniformOfFintype_le
#print axioms Cogentic.RandomizedEpochTV.directRetryConditionalPMF_tv_uniformOfFintype_le_budget
#print axioms Cogentic.RandomizedEpochTV.directRetryConditionalPMF_tv_uniformOfFintype_le_log_pow
#print axioms Cogentic.RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilon
#print axioms Cogentic.RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilonLogPow
#print axioms Cogentic.RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilon_recip
#print axioms Cogentic.RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilon_recip_log_pow
#print axioms Cogentic.RandomizedEpochTV.assembledAttempt_hit_prob_ge_of_directSampler
#print axioms Cogentic.RandomizedEpochTV.assembledAttempt_hit_prob_ge_of_directSampler_uniform
