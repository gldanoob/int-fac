import Cogentic.RandomizedConcreteEpoch
import Cogentic.RandomizedEpochTV
import Cogentic.RandomizedEpochWork
import Cogentic.RandomizedEpochAnalyticInputs

/-!
# C3/C4 inputs for the concrete S0–S9 epoch (wave 2, W13)

This file builds the total-variation (C3) and public-work (C4) inputs of
`Cogentic.RandomizedEpochAnalyticInputs` for the concrete solver-driven epoch of
`Cogentic.RandomizedConcreteEpoch`.

The concrete epoch is an `n`-indexed family `D : ∀ n, ConcreteEpochData n`.
Its packaged `HardEpochData` family is

```
concreteCostFamily D n hN = (D n).toHardEpochData.
```

## C3

`ConcreteC3Hypotheses D` collects the explicit data needed by the direct
reduced-class sampler TV estimate:

* a `DirectFormSpec` on the epoch's sample space, one for each `n`;
* the retry parameters `J`, `J₀` and the root-count function `R`, with their
  side conditions;
* the ideal-to-uniform error `η n`, the one-attempt gcd-exit budget
  `gcdMass n`, and the hypotheses `hideal`, `hgcd`;
* the *exact-law* hypothesis `hactual : (D n).actual = directRetryConditionalPMF …`;
* the small-budget condition `directSamplerEpsilon spec η gcdMass ≤ 1/32`.

From these we prove
`ConcreteC3Hypotheses.tv_le`, which is exactly
`RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilon`, and package it as
`C3Inputs (concreteCostFamily D)`.

The same hypotheses feed the epoch-level bridge
`RandomizedEpochTV.assembledAttempt_hit_prob_ge_of_directSampler`; this is
recorded as `ConcreteC3Hypotheses.hit_prob_ge`, which additionally takes the
already-proved C1/C2 predicates and the ideal good-mass lower bound `γ`.

## C4

`ConcreteC4Hypotheses D C` supplies a stage weight `W j n`, a stage exponent
`c j`, and the per-stage eventual mean and weight bounds.  The concrete stage
list is the ten stages `S0`–`S9` of `ConcreteEpochData.stageCosts`, and the
pointwise decomposition is `ConcreteEpochData.pubWork_eq_sum`.  The family-level
`RandomizedEpochWork.StageDecomposition` is built in
`familyStageDecomposition`; the summation engine
`RandomizedEpochWork.mean_pubWork_le_exp_of_stagewise` then produces
`C4Inputs (concreteCostFamily D) C` in `c4Inputs`.

**What is and is not proved.**  The concrete TV estimate, the uniform-law
proximity of the ideal law, the gcd-exit budget, the small-budget condition, the
per-stage mean bounds, and the per-stage weight bounds are explicitly stated
hypotheses.  None of them is asserted as an axiom or hidden behind
`Classical.choose`: they are fields of the two hypothesis structures, with
docstrings pointing at the blueprint leaves.  What *is* proved is the bridge from
those hypotheses and from the concrete stage decomposition to the C3/C4 input
records, and the composition with the epoch-level hit-probability bridge.

The file contains no `sorry`, `admit`, `axiom`, `native_decide`, or
`Classical.choose`.
-/

namespace Cogentic.RandomizedConcreteEpochCost

set_option linter.style.haveILetI false

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedDirectClassSampler
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochTV
open Cogentic.RandomizedEpochWork
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedOneThirdAsymptotic
open Filter Real
open scoped BigOperators ENNReal

/-- A decidable equality on the concrete public coin type, needed because
`DirectFormSpec` is parameterized by `[DecidableEq Form]` while
`ConcreteEpochData` deliberately does not carry a decidable equality on
`Coins`.  This is a decidability instance only; it does not choose any epoch
data. -/
noncomputable local instance instDecEqCoins (D : ∀ n, ConcreteEpochData n)
    (n : ℕ) : DecidableEq ((D n).Coins) :=
  Classical.decEq _

/-! ## Section 1: The packaged epoch family -/

/-- The `n`-indexed `HardEpochData` family obtained from a family of concrete
solver-driven epochs.  The `hN` argument is proof-irrelevant bookkeeping: the
concrete epoch data only depends on `n`. -/
noncomputable def concreteCostFamily (D : ∀ n, ConcreteEpochData n) :
    ∀ n, 3 ≤ n → HardEpochData n :=
  fun n _ => (D n).toHardEpochData

@[simp] theorem concreteCostFamily_apply (D : ∀ n, ConcreteEpochData n)
    (n : ℕ) (hN : 3 ≤ n) :
    concreteCostFamily D n hN = (D n).toHardEpochData := rfl

/-- Decidable equality on the packaged family's sample space, keyed on the
concrete epoch's own sample type. -/
noncomputable local instance instDecEqFamilySample (D : ∀ n, ConcreteEpochData n)
    (n : ℕ) (hN : 3 ≤ n) :
    DecidableEq ((concreteCostFamily D n hN).Sample) :=
  inferInstanceAs (DecidableEq ((D n).Sample))

/-- Finiteness of the packaged family's sample space (`ZMod n` is finite once
`n` is nonzero, which holds on the epoch range `3 ≤ n`). -/
noncomputable local instance instFintypeFamilySample (D : ∀ n, ConcreteEpochData n)
    (n : ℕ) (hN : 3 ≤ n) [NeZero n] :
    Fintype ((concreteCostFamily D n hN).Sample) :=
  inferInstanceAs (Fintype ((D n).Sample))

/-! ## Section 2: C3 from the direct reduced-class sampler -/

/-- Explicit hypotheses for the C3 TV budget of the concrete epoch.

Each field is a *hypothesis*, not a proved theorem.  The docstrings name the
corresponding blueprint leaves and the exact statement that remains to be
supplied by the analytic workstream.
-/
structure ConcreteC3Hypotheses (D : ∀ n, ConcreteEpochData n) where
  /-- The direct reduced-class sampler specification on the public sample space
  `(D n).Coins × ((D n).Label → (ZMod n)ˣ)` of the concrete epoch.  This is the
  `DirectFormSpec` of `RandomizedDirectClassSampler`, instantiated at the epoch's
  own sample type. -/
  spec : ∀ n, DirectFormSpec ((D n).Sample)
  /-- Dyadic proposal depth `J` of the direct sampler. -/
  J : ℕ
  /-- Retry count `J₀` of the direct sampler. -/
  J₀ : ℕ
  /-- L6/L8: the leading-coefficient bound is below the proposal range. -/
  hUJ : ∀ n, (spec n).U ≤ 2 ^ J
  /-- L6: the retry count is positive. -/
  hJ₀ : 1 ≤ J₀
  /-- L6: accepted coprime forms exist. -/
  hcop : ∀ n, (spec n).coprimeForms.Nonempty
  /-- L6: the canonical form universe is nonempty. -/
  hall : ∀ n, (spec n).allForms.Nonempty
  /-- The modulus carried by the specification is at least `2`. -/
  hNspec : ∀ n, 2 ≤ (spec n).N
  /-- The leading-coefficient bound is at least `1`. -/
  hUspec : ∀ n, 1 ≤ (spec n).U
  /-- Root-count majorant `R n A` for the specification at size `n`. -/
  R : ℕ → ℕ → ℕ
  /-- L6: `R` dominates the number of canonical roots for every admissible
  leading coefficient. -/
  hR_ge : ∀ n (A : ℕ), A ∈ Finset.Icc 1 ((spec n).U) →
    ((spec n).roots A).card ≤ R n A
  /-- L6: normalization `R n 1 = 1`. -/
  hR1 : ∀ n, R n 1 = 1
  /-- L6: multiplicativity of `R n` on coprime arguments. -/
  hRmul : ∀ n (a b : ℕ), Nat.Coprime a b → R n (a * b) = R n a * R n b
  /-- L6: the coprime root-count majorant is at most `2 * 2 ^ ω(m)`. -/
  hRcop : ∀ n (m : ℕ), 1 ≤ m → Nat.Coprime m ((spec n).N) →
    R n m ≤ 2 * 2 ^ m.primeFactors.card
  /-- L6: the prime-power root-count majorant is at most `2 * p ^ (k / 2)`. -/
  hRloc : ∀ n (p : ℕ), p ∈ ((spec n).N).primeFactors → ∀ k, 1 ≤ k →
    R n (p ^ k) ≤ 2 * p ^ (k / 2)
  /-- L6-L10: finite-sampling / ideal-law distance to the uniform law on the
  canonical form set.  The concrete direct-sampler estimate is stated against
  `PMF.uniformOfFinset (spec n).allForms`; this field is the `η` of
  `RandomizedEpochTV.directSamplerEpsilon`. -/
  eta : ℕ → ℝ
  /-- L6-L10: one-attempt gcd-exit budget `gcdMass`.  This is the explicit
  hypothesis `hgcd` of `RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilon`;
  the shared source's `gcdExitProb_toReal_le` is not used. -/
  gcdMass : ℕ → ℝ
  /-- L6-L10: the ideal law is within `η n` of uniform on the canonical forms. -/
  hideal : ∀ n,
    pmfTotalVariation (D n).ideal
      (PMF.uniformOfFinset (spec n).allForms (hall n)) ≤ eta n
  /-- L6-L10: the gcd-exit probability is bounded by `gcdMass n`. -/
  hgcd : ∀ n, (gcdExitProb (spec n) J).toReal ≤ gcdMass n
  /-- **Exact-law hypothesis.**  The actual law of the concrete epoch is exactly
  the conditional direct-sampler law of `RandomizedDirectClassSampler`.  This is
  the `hactual` hypothesis of
  `RandomizedEpochTV.assembledAttempt_hit_prob_ge_of_directSampler`; it is the
  modelling input that identifies the concrete sampler stack with the direct
  sampler. -/
  hactual : ∀ n,
    (D n).actual = directRetryConditionalPMF (spec n) (hUJ n) hJ₀ (hcop n)
  /-- L6-L10: the explicit TV budget is at most `1/32`, the constant required by
  the C3 slot of `RandomizedEpochAnalyticInputs.C3Inputs`.  This is a small-budget
  condition on the concrete `directSamplerEpsilon`; it is not derived here. -/
  heps_le : ∀ n, directSamplerEpsilon (spec n) (eta n) (gcdMass n) ≤ 1 / 32

namespace ConcreteC3Hypotheses

variable {D : ∀ n, ConcreteEpochData n}

/-- The real-valued total-variation distance is nonnegative.  This is used only
to extract `0 ≤ η` from the explicit ideal-law proximity hypothesis. -/
theorem pmfTotalVariation_nonneg {B : Type*} (p q : PMF B) :
    0 ≤ pmfTotalVariation p q := by
  unfold pmfTotalVariation
  exact div_nonneg (tsum_nonneg fun z => abs_nonneg _) (by norm_num)

/-- The concrete C3 budget is nonnegative.  The missing-root mass is
nonnegative by `RandomizedEpochTV.directMissingRootMass_nonneg`, the form set is
nonempty, and `η`, `gcdMass` are nonnegative by the explicit hypotheses. -/
theorem epsilon_nonneg (H : ConcreteC3Hypotheses D) (n : ℕ) :
    0 ≤ directSamplerEpsilon (H.spec n) (H.eta n) (H.gcdMass n) := by
  have hmiss : 0 ≤ directMissingRootMass (H.spec n) :=
    directMissingRootMass_nonneg (H.spec n) (H.hNspec n) (H.hUspec n)
  have hcardNat : 0 < ((H.spec n).allForms.card) := (H.hall n).card_pos
  have hcard : (0 : ℝ) < (((H.spec n).allForms.card) : ℝ) := by
    exact_mod_cast hcardNat
  have hgcd : 0 ≤ H.gcdMass n := ENNReal.toReal_nonneg.trans (H.hgcd n)
  have heta : 0 ≤ H.eta n :=
    (pmfTotalVariation_nonneg (D n).ideal _).trans (H.hideal n)
  unfold directSamplerEpsilon
  exact add_nonneg (add_nonneg (div_nonneg hmiss hcard.le) hgcd) heta

/-- **C3 TV estimate for the concrete epoch.**  This is
`RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilon` applied to the
concrete epoch's ideal and exact actual laws.  No analytic estimate is asserted
here: every numeric input is a field of `ConcreteC3Hypotheses`. -/
theorem tv_le (H : ConcreteC3Hypotheses D) {n : ℕ} (hN : 3 ≤ n) :
    pmfTotalVariation (concreteCostFamily D n hN).ideal
        (concreteCostFamily D n hN).actual ≤
      directSamplerEpsilon (H.spec n) (H.eta n) (H.gcdMass n) := by
  change pmfTotalVariation (D n).ideal (D n).actual ≤
    directSamplerEpsilon (H.spec n) (H.eta n) (H.gcdMass n)
  rw [H.hactual n]
  haveI : NeZero n := ⟨by omega⟩
  exact pmfTotalVariation_le_directSamplerEpsilon (H.spec n) (H.hUJ n) H.hJ₀
    (H.hcop n) (H.hall n) (H.hNspec n) (H.hUspec n) (H.R n)
    (fun A hA => H.hR_ge n A hA) (H.hR1 n)
    (fun a b h => H.hRmul n a b h) (fun m hm hc => H.hRcop n m hm hc)
    (fun p hp k hk => H.hRloc n p hp k hk) (H.hideal n) (H.hgcd n)

/-- **Epoch-level hit-probability bridge.**  The concrete C3 hypotheses, the
already-proved C1/C2 predicates, and the ideal good-mass lower bound `γ` give the
verified-split lower bound

`γ / 2 - directSamplerEpsilon spec η gcdMass`

through `RandomizedEpochTV.assembledAttempt_hit_prob_ge_of_directSampler`.

The witness `coinsDefault` is used only to exhibit a nonempty sample space; it is
an explicit function, not a `Classical.choose` of epoch data. -/
theorem hit_prob_ge (H : ConcreteC3Hypotheses D)
    (coinsDefault : ∀ n, (D n).Coins)
    {n : ℕ} (hN : 3 ≤ n) (hhard : HardInput n)
    (hcheck : (concreteCostFamily D n hN).CongruenceCheck)
    (huniform : (concreteCostFamily D n hN).HiddenUniform)
    {γ : ℝ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤
      ((concreteCostFamily D n hN).ideal.toOuterMeasure
        {x | observe (concreteCostFamily D n hN).trace x ∈
          (concreteCostFamily D n hN).good}).toReal) :
    γ / 2 - directSamplerEpsilon (H.spec n) (H.eta n) (H.gcdMass n) ≤
      (((concreteCostFamily D n hN).actual.map
          ((concreteCostFamily D n hN).assembledAttempt hN)).toOuterMeasure
        {o | o.1 ≠ none}).toReal := by
  haveI : Nonempty ((concreteCostFamily D n hN).Sample) :=
    ⟨(coinsDefault n, fun _ => 1)⟩
  haveI : NeZero n := ⟨by omega⟩
  exact assembledAttempt_hit_prob_ge_of_directSampler
    (concreteCostFamily D n hN) hN hhard.1 hhard.2.2 hcheck huniform
    (H.spec n) (H.hUJ n) H.hJ₀ (H.hcop n) (H.hall n)
    (H.hNspec n) (H.hUspec n) (H.R n)
    (fun A hA => H.hR_ge n A hA) (H.hR1 n)
    (fun a b h => H.hRmul n a b h) (fun m hm hc => H.hRcop n m hm hc)
    (fun p hp k hk => H.hRloc n p hp k hk)
    (H.hactual n) (H.hideal n) (H.hgcd n) hγ₀ hγ

end ConcreteC3Hypotheses

/-- **C3 inputs for the concrete epoch.**  The budget is the explicit
`directSamplerEpsilon`, its nonnegativity is proved from the structure fields,
and the TV bound is `ConcreteC3Hypotheses.tv_le`. -/
noncomputable def c3Inputs (D : ∀ n, ConcreteEpochData n)
    (H : ConcreteC3Hypotheses D) :
    C3Inputs (concreteCostFamily D) where
  epsilon := fun n => directSamplerEpsilon (H.spec n) (H.eta n) (H.gcdMass n)
  epsilon_nonneg := H.epsilon_nonneg
  epsilon_le := H.heps_le
  tv_le := fun n hN _ => H.tv_le (n := n) hN

/-! ## Section 3: C4 from the concrete S0–S9 stage decomposition -/

/-- Explicit hypotheses for the C4 public-work budget of the concrete epoch.

`stageWeight` and `stageExponent` are the per-stage work weights and exponents of
blueprint C4 (L11-L16).  The two eventual bounds are the per-stage analytic
inputs; the pointwise decomposition is *not* a hypothesis: it is supplied by the
concrete epoch's `pubWork_eq_sum`. -/
structure ConcreteC4Hypotheses (D : ∀ n, ConcreteEpochData n) (C : ℝ) where
  /-- Expected work weight `W j n` of named stage `j` at size `n`. -/
  stageWeight : Stage → ℕ → ℝ
  /-- Exponential exponent `c j` of named stage `j`. -/
  stageExponent : Stage → ℝ
  /-- L11-L16: every stage exponent is strictly below the ceiling `C`. -/
  exponent_lt : ∀ j, stageExponent j < C
  /-- L11-L16: the actual mean cost of stage `j` is eventually at most its
  weight `W j n`.  This is the per-stage analytic estimate, stated explicitly. -/
  mean_le : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
    mean (concreteCostFamily D n hN).actual
      (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
      ENNReal.ofReal (stageWeight j n)
  /-- L11-L16: the stage weight is eventually at most `exp (c j * scale n)`. -/
  weight_le : ∀ j, ∀ᶠ n : ℕ in atTop,
    stageWeight j n ≤ exp (stageExponent j * scale n)

/-- The family-level `StageDecomposition` of the concrete epoch: the ten concrete
stage costs `S0`–`S9` lifted to the `n`-indexed epoch family.  The pointwise
identity is exactly `ConcreteEpochData.pubWork_eq_sum`. -/
def familyStageDecomposition (D : ∀ n, ConcreteEpochData n) :
    RandomizedEpochWork.StageDecomposition (concreteCostFamily D) Stage where
  cost := fun j n _ x => (D n).stageCosts.cost j x
  pubWork_eq := by
    intro n hN x
    change (D n).toHardEpochData.pubWork x =
      ∑ j : Stage, (D n).stageCosts.cost j x
    exact (D n).pubWork_eq_sum x

@[simp] theorem familyStageDecomposition_cost (D : ∀ n, ConcreteEpochData n)
    (j : Stage) (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost j n hN x = (D n).stageCosts.cost j x := rfl

/-- The family stage decomposition sums to the concrete epoch's public work,
stage by stage.  This is the direct bridge from the concrete `S0`–`S9` list. -/
theorem familyStageDecomposition_pubWork_eq
    (D : ∀ n, ConcreteEpochData n) (n : ℕ) (hN : 3 ≤ n)
    (x : (concreteCostFamily D n hN).Sample) :
    (concreteCostFamily D n hN).pubWork x =
      ∑ j : Stage, (D n).stageCosts.cost j x :=
  (D n).pubWork_eq_sum x

/-- **Public-work summation for the concrete stages.**  This is
`RandomizedEpochWork.mean_pubWork_le_exp_of_stagewise` applied to
`familyStageDecomposition`. -/
theorem mean_pubWork_le_exp_of_concreteStages
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ConcreteC4Hypotheses D C) :
    ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (concreteCostFamily D n hN).actual
        (fun x => ((concreteCostFamily D n hN).pubWork x : ℝ≥0∞)) ≤
        ENNReal.ofReal (exp (C * scale n)) :=
  mean_pubWork_le_exp_of_stagewise (concreteCostFamily D)
    (familyStageDecomposition D) H.stageWeight H.stageExponent H.exponent_lt
    H.mean_le H.weight_le

/-- **C4 inputs for the concrete epoch.**  The stagewise summation engine gives
the mean bound at ceiling `C`; the `C + δ/2` form required by
`C4Inputs.work_le` follows from monotonicity of `exp` on the nonnegative scale
`scale n` (eventually nonnegative by `scale_grows`). -/
theorem c4Inputs (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ConcreteC4Hypotheses D C) :
    C4Inputs (concreteCostFamily D) C where
  work_le := by
    intro δ hδ
    filter_upwards [mean_pubWork_le_exp_of_concreteStages D H,
      scale_grows.eventually_ge_atTop (0 : ℝ)] with n hwork hscale
    intro hN _
    refine (hwork hN).trans (ENNReal.ofReal_le_ofReal ?_)
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + δ / 2) hscale)

/-! ## Section 4: Bundling C3 and C4 -/

/-- The C3/C4 pair for the concrete epoch at work ceiling `C`. -/
structure ConcreteCostInputs (D : ∀ n, ConcreteEpochData n) (C : ℝ) where
  /-- C3: the ideal/actual total-variation budget. -/
  c3 : C3Inputs (concreteCostFamily D)
  /-- C4: the expected public-work budget. -/
  c4 : C4Inputs (concreteCostFamily D) C

/-- **W13 bundle.**  The concrete C3 hypotheses (direct-sampler TV estimate) and
the concrete C4 hypotheses (stagewise mean bounds over `S0`–`S9`) produce both
analytic input records for the concrete epoch. -/
noncomputable def concreteCostInputs (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H3 : ConcreteC3Hypotheses D) (H4 : ConcreteC4Hypotheses D C) :
    ConcreteCostInputs D C :=
  ⟨c3Inputs D H3, c4Inputs D H4⟩

/-- **C3/C4 bundle.**  The concrete C3 hypotheses (direct-sampler TV estimate)
and the concrete C4 hypotheses (stagewise mean bounds over `S0`–`S9`) produce
the bundled cost input record for the concrete epoch. -/
noncomputable def c3_and_c4_inputs_concreteEpoch (D : ∀ n, ConcreteEpochData n)
    {C : ℝ} (H3 : ConcreteC3Hypotheses D) (H4 : ConcreteC4Hypotheses D C) :
    ConcreteCostInputs D C :=
  concreteCostInputs D H3 H4

/-- The concrete C3/C4 inputs, combined with explicit C1, C2 and C5 inputs,
complete `EpochAnalyticInputs` for the concrete epoch.  C1, C2 and C5 are left
as hypotheses: this file only constructs C3 and C4. -/
noncomputable def epochAnalyticInputs_of_concreteCost
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (c1 : C1Inputs (concreteCostFamily D))
    (c2 : C2Inputs (concreteCostFamily D))
    (H3 : ConcreteC3Hypotheses D) (H4 : ConcreteC4Hypotheses D C)
    (c5 : C5Inputs (concreteCostFamily D)) :
    EpochAnalyticInputs (concreteCostFamily D) C where
  c1 := c1
  c2 := c2
  c3 := c3Inputs D H3
  c4 := c4Inputs D H4
  c5 := c5

/-- Composition of the concrete C3/C4 bridge with the existing analytic-input
reduction: explicit C1/C2/C5 plus the concrete cost hypotheses give
`HardEpochAsymptoticBound` for the concrete epoch. -/
theorem hardEpochAsymptoticBound_of_concreteCost
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (c1 : C1Inputs (concreteCostFamily D))
    (c2 : C2Inputs (concreteCostFamily D))
    (H3 : ConcreteC3Hypotheses D) (H4 : ConcreteC4Hypotheses D C)
    (c5 : C5Inputs (concreteCostFamily D)) :
    HardEpochAsymptoticBound (concreteCostFamily D) C :=
  hardEpochAsymptoticBound_of_analyticInputs _ C
    (epochAnalyticInputs_of_concreteCost D c1 c2 H3 H4 c5)

/-! ## Section 5: Axiom audit -/

#print axioms ConcreteC3Hypotheses.pmfTotalVariation_nonneg
#print axioms ConcreteC3Hypotheses.epsilon_nonneg
#print axioms ConcreteC3Hypotheses.tv_le
#print axioms ConcreteC3Hypotheses.hit_prob_ge
#print axioms c3Inputs
#print axioms familyStageDecomposition
#print axioms familyStageDecomposition_pubWork_eq
#print axioms mean_pubWork_le_exp_of_concreteStages
#print axioms c4Inputs
#print axioms concreteCostInputs
#print axioms c3_and_c4_inputs_concreteEpoch
#print axioms epochAnalyticInputs_of_concreteCost
#print axioms hardEpochAsymptoticBound_of_concreteCost

end Cogentic.RandomizedConcreteEpochCost
