import Cogentic.RandomizedP1Sub
import Cogentic.RandomizedL30Sub
import Cogentic.RandomizedL27_1Sub

/-!
# P1 analytic layer: genus-two/ECM success and cost interfaces

`Cogentic/RandomizedP1Sub.lean` reduces the manuscript's P1 prepass to two
paper-level statements, `PrepassSuccess` and `PrepassCostSubexp`.  This file
reduces those statements to the analytic estimates that are already formalized
elsewhere, and isolates the pieces that genuinely remain paper-level.

## What is discharged here

* **Genus-two success.**  `RandomizedL30Sub.FailureData.loss_le_exp_neg` already
  gives `Pr [FAIL] ≤ exp (-B H)` for every `B > 0`.  This is exactly
  `PrepassSuccess`, so `genusTwoPrepassSuccess` discharges the success input
  from the H.3 failure analysis, and `l30PrepassSuccess` does the same for the
  bundled `L30Inputs`.
* **Trial-division success.**  `trialPrepass_paper_success` gives the
  deterministic splitting statement for every cutoff; this file restates it as
  part of the explicit cost obstruction `TrialDivisionCostObstruction`.
* **Cost exponent from a cost envelope.**  The paper's cost is naturally stated
  as `cost ≤ exp (δ H)` for every `δ > 0` (the `exp (o (H))` statement), not as
  a chosen exponent function.  `P1AnalyticInputs` carries this envelope form,
  and `P1AnalyticInputs.toP1SubInputs` converts it to `PrepassCostSubexp`
  using `costExponentOf cost = max 0 (log cost)`, which is little-o of `scale`.

## The explicit analytic sub-Props that remain

* `GenusTwoCostEnvelope I` for `I : RandomizedL30.L30Inputs`: the H.5 total
  cost of the genus-two factorer is `exp (o (H))`.  It is exactly the pair
  `(totalCost_nonneg, cost_sublinear)` already present in `L30Inputs`, so the
  reduction to `P1SubInputs` is complete once that input is supplied.
* `ECMCurveBudgetAllRates I` for `I : RandomizedL27_1.L27_1Inputs`: the
  curve-count selection has to beat `(δ + η) H` for **every** `δ > 0`, not just
  the ledger rate `2 H`.  This is the smallest gap between the existing
  `RandomizedL27_1` estimate (which proves only the `δ = 2` slot,
  `ecmPrepassSuccess_at_two`) and `PrepassSuccess`.  Given this sub-Prop the
  ECM success statement follows from `splitFail_le_exp_of` and
  `LogFactorSubexp`, with no further analysis.
* `ECMCostEnvelope cost`: `RandomizedL27_1` formalizes the LP failure estimate
  only, so the ECM cost is a single explicit envelope input.  There is no
  borrowed cost bound hidden in the ECM failure analysis.

## Trial-division cost obstruction

`TrialDivisionCostObstruction` bundles the proved facts that trial division
splits every input with a small prime factor, that no cutoff reaching
`roughThreshold` is affordable on the `exp (o (H))` budget, and that the
logarithm `trialDivisionExponent` of its proved work envelope is not little-o of
`scale`.  `trialDivisionExponent_not_P1Cost` and
`trialDivision_envelope_obstruction` record the two consequences at the
`P1SubInputs` level: the trial-division exponent cannot be a P1 cost exponent,
and no P1 bundle can charge the trial-division work envelope at
`roughThreshold`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No success
probability or cost is set to zero: the success inputs are genuine `exp (-δ H)`
bounds and the cost exponent is the logarithm of the input cost.
-/

namespace Cogentic.RandomizedP1Analytic

open Filter Real
open Cogentic.RandomizedP1
open Cogentic.RandomizedP1Sub
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSmallPrimePrepass
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub

noncomputable section

/-! ## 1. Cost envelopes and their subexponential exponents -/

/-- A nonnegative cost function that is eventually at most `exp (δ H)` for
every `δ > 0`.  This is the manuscript's `exp (o (H))` cost, stated on the cost
rather than on a chosen exponent. -/
def SubexpCostEnvelope (cost : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ cost n) ∧
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, cost n ≤ Real.exp (δ * scale n)

/-- The canonical exponent of a cost envelope: `max 0 (log (cost n))`. -/
def costExponentOf (cost : ℕ → ℝ) : ℕ → ℝ :=
  fun n => max 0 (Real.log (cost n))

/-- A nonnegative `exp (o (H))` cost has a nonnegative logarithm. -/
theorem costExponentOf_nonneg (cost : ℕ → ℝ) (n : ℕ) :
    0 ≤ costExponentOf cost n :=
  le_max_left 0 _

/-- Taking logarithms of a nonnegative bound by an exponential. -/
private theorem log_le_of_le_exp {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : c ≤ Real.exp s) : Real.log c ≤ s := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0, Real.log_zero]
    exact hs
  · exact (Real.log_le_iff_le_exp hcpos).mpr h

/-- **A cost envelope is an `exp (o (H))` cost.**  The exponent
`max 0 (log cost)` is little-o of `scale`. -/
theorem subexpCostEnvelope_to_littleO {cost : ℕ → ℝ}
    (h : SubexpCostEnvelope cost) :
    PrepassCostSubexp (costExponentOf cost) := by
  change Asymptotics.IsLittleO atTop (costExponentOf cost) scale
  refine Asymptotics.IsLittleO.of_bound fun δ hδ => ?_
  filter_upwards [h.2 δ hδ, scale_grows.eventually_ge_atTop 0] with n hcost hs
  have hδs : 0 ≤ δ * scale n := mul_nonneg hδ.le hs
  have hmax : costExponentOf cost n ≤ δ * scale n :=
    max_le hδs (log_le_of_le_exp (h.1 n) hδs hcost)
  rw [Real.norm_of_nonneg (costExponentOf_nonneg cost n),
    Real.norm_of_nonneg hs]
  exact hmax

/-- The cost is at most the exponential of its canonical exponent. -/
theorem cost_le_exp_costExponentOf (cost : ℕ → ℝ) (h : ∀ n, 0 ≤ cost n)
    (n : ℕ) :
    cost n ≤ Real.exp (costExponentOf cost n) := by
  rcases le_total (cost n) 1 with hle | hge
  · have hexp : costExponentOf cost n = 0 := by
      rw [costExponentOf, max_eq_left (Real.log_nonpos (h n) hle)]
    rw [hexp, Real.exp_zero]
    exact hle
  · have hcpos : 0 < cost n := zero_lt_one.trans_le hge
    have hlog : 0 ≤ Real.log (cost n) := Real.log_nonneg hge
    rw [costExponentOf, max_eq_right hlog, Real.exp_log hcpos]

/-! ## 2. The analytic P1 inputs

`P1AnalyticInputs` is the smallest bundle below `P1SubInputs`: the two
manuscript statements are kept as a success `Prop` and a cost envelope, and the
work bound is stated against the cost itself.  The conversion to
`PrepassCostSubexp` and hence to `P1SubInputs` is proved, not assumed. -/

/-- Explicit analytic inputs for the P1 prepass, with the cost in envelope form.

The success field is the manuscript's `PrepassSuccess`; the cost field is a
nonnegative function bounded by `exp (δ H)` for every `δ > 0`.  All fields are
genuine hypotheses: the structure has no zero-cost or zero-loss default. -/
structure P1AnalyticInputs where
  /-- The prepass cutoff `B n`. -/
  cutoff : ℕ → ℝ
  /-- The cutoff covers the paper's `exp ((log n)^{2/3})` threshold. -/
  cutoff_ge_rough : ∀ᶠ n : ℕ in atTop, roughThreshold n ≤ cutoff n
  /-- The miss probability of the prepass. -/
  miss : ℕ → ℝ
  /-- A failure probability is nonnegative. -/
  miss_nonneg : ∀ n, 0 ≤ miss n
  /-- A failure probability is at most one. -/
  miss_le_one : ∀ n, miss n ≤ 1
  /-- **Success input** (KB Prop. H.3 / LP Thm 7.1), in `PrepassSuccess` form. -/
  success : PrepassSuccess miss
  /-- The cost function, including the exponential part. -/
  cost : ℕ → ℝ
  /-- **Cost input**: the cost is `exp (o (H))`, in envelope form. -/
  cost_subexp : SubexpCostEnvelope cost
  /-- Polynomial overhead degree of the prepass. -/
  overhead : ℕ
  /-- The charged expected work of the prepass. -/
  work : ℕ → ℝ
  /-- Work is nonnegative. -/
  work_nonneg : ∀ n, 0 ≤ work n
  /-- The work is at most a polynomial in the bit length times the cost. -/
  work_le : ∀ n, work n ≤
    ((n.log2 : ℝ) + 1) ^ overhead * cost n

namespace P1AnalyticInputs

variable (A : P1AnalyticInputs)

/-- **The cost envelope gives a `PrepassCostSubexp`.**  The exponent selected
here is `max 0 (log cost)`, not zero. -/
theorem costSubexp : PrepassCostSubexp (costExponentOf A.cost) :=
  subexpCostEnvelope_to_littleO A.cost_subexp

/-- **The analytic P1 bundle reduces to `P1SubInputs`.**  The only change is
that the cost exponent is replaced by the canonical logarithm of the cost
envelope. -/
def toP1SubInputs : P1SubInputs where
  cutoff := A.cutoff
  cutoff_ge_rough := A.cutoff_ge_rough
  miss := A.miss
  miss_nonneg := A.miss_nonneg
  miss_le_one := A.miss_le_one
  success := A.success
  costExponent := costExponentOf A.cost
  costExponent_nonneg := costExponentOf_nonneg A.cost
  cost_subexp := A.costSubexp
  work := A.work
  work_nonneg := A.work_nonneg
  overhead := A.overhead
  work_le := fun n => by
    calc
      A.work n ≤ ((n.log2 : ℝ) + 1) ^ A.overhead * A.cost n := A.work_le n
      _ ≤ ((n.log2 : ℝ) + 1) ^ A.overhead *
            Real.exp (costExponentOf A.cost n) :=
        mul_le_mul_of_nonneg_left
          (cost_le_exp_costExponentOf A.cost A.cost_subexp.1 n)
          (by positivity)

/-- The manuscript's `D^{-B}` success statement. -/
theorem subexpLoss : SubexpLoss A.miss := A.toP1SubInputs.subexpLoss

/-- The `δ = 2` C5 slot. -/
theorem slot :
    ∀ᶠ n : ℕ in atTop, A.miss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  A.toP1SubInputs.slot

/-- The sublinear cost consequence. -/
theorem costExponent_sublinear :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      costExponentOf A.cost n ≤ δ * scale n :=
  A.toP1SubInputs.costExponent_sublinear

/-- The P1 leaf obtained from the analytic inputs. -/
def toP1Leaf : Cogentic.RandomizedPaperLeafStatements.P1Leaf :=
  A.toP1SubInputs.toP1Leaf

/-- Expected repeated work, including the retries, fits in `exp (ε H)`. -/
theorem repeated_work_add_one_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      A.work n / successMass A.miss n + 1 ≤ Real.exp (ε * scale n) :=
  A.toP1SubInputs.repeated_work_add_one_le_exp hε

end P1AnalyticInputs

/-- **The analytic P1 reduction.**  An explicit success statement, an
`exp (o (H))` cost envelope, and a polynomial overhead bound give the full P1
sub-bundle, hence the manuscript's loss slot and the success-to-cost bound. -/
theorem p1Analytic_reduction (A : P1AnalyticInputs) :
    SubexpLoss A.miss ∧
      (∀ᶠ n : ℕ in atTop, A.miss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        costExponentOf A.cost n ≤ δ * scale n) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        A.work n / successMass A.miss n + 1 ≤ Real.exp (ε * scale n)) :=
  p1Sub_reduction A.toP1SubInputs

/-! ## 3. Genus-two success interface (KB Proposition H.3) -/

/-- **Genus-two prepass success, discharged from H.3.**  The `FailureData`
analysis of `RandomizedL30Sub` proves
`Pr [FAIL] ≤ 2 n exp (-64 L_c)`, and `confidence_dominates` makes this at most
`exp (-δ H)` for every `δ > 0`.  This is exactly `PrepassSuccess`. -/
theorem genusTwoPrepassSuccess (F : FailureData) :
    PrepassSuccess F.loss :=
  fun δ hδ => F.loss_le_exp_neg δ hδ

/-- The same success statement for the bundled `L30Inputs`. -/
theorem l30PrepassSuccess (I : L30Inputs) : PrepassSuccess I.loss :=
  fun δ hδ => I.loss_le_exp_neg δ hδ

/-! ## 4. Genus-two cost interface (KB (H.5) + `exp (o (H))`) -/

/-- **The genus-two cost sub-Prop.**  The total cost of the bounded genus-two
factorer is `exp (o (H))`.  In `L30Inputs` this is exactly the pair
`(totalCost_nonneg, cost_sublinear)`; it is not derived from the failure
analysis and is not set to zero. -/
def GenusTwoCostEnvelope (I : L30Inputs) : Prop :=
  SubexpCostEnvelope I.totalCost

/-- The cost sub-Prop holds for any `L30Inputs`: its `cost_sublinear` field is
the paper's `exp (o (H))` total-cost input. -/
theorem genusTwoCostEnvelope (I : L30Inputs) : GenusTwoCostEnvelope I :=
  ⟨I.totalCost_nonneg, I.cost_sublinear⟩

/-- The genus-two cost has an explicit little-o exponent `log totalCost`. -/
theorem genusTwoCostSubexp (I : L30Inputs) :
    PrepassCostSubexp (costExponentOf I.totalCost) :=
  subexpCostEnvelope_to_littleO (genusTwoCostEnvelope I)

/-- **The genus-two P1 analytic inputs.**  Success comes from H.3, cost from
the H.5 total-cost bound, and the `L30Inputs` work is charged directly against
that cost.  The miss probability is clamped at one only to satisfy the
probability-range field; it is still bounded by the genuine failure
probability. -/
def genusTwoAnalyticInputs (I : L30Inputs) : P1AnalyticInputs where
  cutoff := roughThreshold
  cutoff_ge_rough := Eventually.of_forall fun _ => le_rfl
  miss := fun n => min (I.loss n) 1
  miss_nonneg := fun n => le_min (I.loss_nonneg n) zero_le_one
  miss_le_one := fun n => min_le_right _ _
  success := fun δ hδ => by
    filter_upwards [I.loss_le_exp_neg δ hδ] with n hn
    exact (min_le_left _ _).trans hn
  cost := I.totalCost
  cost_subexp := genusTwoCostEnvelope I
  overhead := 0
  work := I.totalCost
  work_nonneg := I.totalCost_nonneg
  work_le := fun n => by
    rw [pow_zero, one_mul]

/-- **The genus-two reduction to the P1 sub-bundle.** -/
def genusTwoP1SubInputs (I : L30Inputs) : P1SubInputs :=
  (genusTwoAnalyticInputs I).toP1SubInputs

/-- The genus-two P1 leaf. -/
def genusTwoP1Leaf (I : L30Inputs) : P1Leaf :=
  (genusTwoAnalyticInputs I).toP1Leaf

/-! ## 5. ECM interfaces (LP Theorem 7.1) -/

/-- **The smallest ECM success sub-Prop.**  The curve-count selection must beat
`(δ + η) H` for every `δ > 0`.  The bundled `RandomizedL27_1.CurveBudget` is
the single-rate case `δ = 2`, which is why it yields only the `δ = 2` slot.
This Prop is strictly the curve-budget side: no curve count, group law, or
Deuring estimate is assumed beyond the existing `L27_1Inputs` and its two
paper-level `Prop`s. -/
def ECMCurveBudgetAllRates (I : L27_1Inputs) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    (δ + I.η) * scale n ≤ I.cRate * I.rate n

/-- The all-rates curve budget implies the single-rate `CurveBudget` at
`δ = 2`. -/
theorem curveBudget_of_allRates (I : L27_1Inputs)
    (h : ECMCurveBudgetAllRates I) : CurveBudget I.p I.y I.psi I.curves I.κ I.η := by
  filter_upwards [h 2 (by norm_num)] with n hn
  simpa [L27_1Inputs.cRate, L27_1Inputs.rate, L27_1Inputs.D, density] using hn

/-- **ECM success at every rate.**  The existing split-failure bound
`splitFail ≤ exp (-(κ/4) · rate)`, the `log₂` subexponential multiplier, and
the all-rates curve budget give `PrepassSuccess`. -/
theorem ecmPrepassSuccess_of_budget (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I)
    (hbudget : ECMCurveBudgetAllRates I) (hlog : LogFactorSubexp I.cofactor) :
    PrepassSuccess I.loss := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ32 : 0 < 3 * δ / 2 := by positivity
  filter_upwards [hbudget (3 * δ / 2) hδ32, hlog (δ / 2) hδ2,
    scale_grows.eventually_ge_atTop 0] with n hb hl hs
  have hηS : 0 ≤ I.η * scale n := mul_nonneg I.η_pos.le hs
  have hb' : (3 * δ / 2) * scale n ≤ I.cRate * I.rate n := by nlinarith
  have hfail := splitFail_le_exp_of I hdeuring hell n
  calc
    I.loss n = ((I.cofactor n).log2 : ℝ) * I.splitFail n := rfl
    _ ≤ Real.exp ((δ / 2) * scale n) *
          Real.exp (-(I.cRate * I.rate n)) :=
      mul_le_mul hl hfail (splitFail_nonneg_of I n) (Real.exp_pos _).le
    _ = Real.exp ((δ / 2) * scale n - I.cRate * I.rate n) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-(δ) * scale n) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- **The ECM estimate as currently formalized gives only the `δ = 2` slot.**
This is `RandomizedL27_1Sub.reduced_ledger`; it is a theorem, not an input. -/
theorem ecmPrepassSuccess_at_two (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  reduced_ledger I hdeuring hell hbudget hlog

/-- **The ECM cost sub-Prop.**  `RandomizedL27_1` formalizes the LP failure
estimate only, so the `exp (o (H))` cost is carried as this single explicit
envelope. -/
def ECMCostEnvelope (cost : ℕ → ℝ) : Prop :=
  SubexpCostEnvelope cost

/-- An ECM cost envelope gives an explicit little-o cost exponent. -/
theorem ecmCostSubexp {cost : ℕ → ℝ} (h : ECMCostEnvelope cost) :
    PrepassCostSubexp (costExponentOf cost) :=
  subexpCostEnvelope_to_littleO h

/-- **The ECM P1 analytic inputs**, given the all-rates success sub-Prop and the
separate cost envelope.  This is the exact interface that upgrades the existing
`δ = 2` ECM estimate to a full P1 bundle. -/
def ecmAnalyticInputs (I : L27_1Inputs) (hsuccess : PrepassSuccess I.loss)
    (cost : ℕ → ℝ) (hcost : ECMCostEnvelope cost)
    (overhead : ℕ) (work : ℕ → ℝ) (hwork_nonneg : ∀ n, 0 ≤ work n)
    (hwork_le : ∀ n, work n ≤
      ((n.log2 : ℝ) + 1) ^ overhead * cost n) :
    P1AnalyticInputs where
  cutoff := roughThreshold
  cutoff_ge_rough := Eventually.of_forall fun _ => le_rfl
  miss := fun n => min (I.loss n) 1
  miss_nonneg := fun n => le_min (loss_nonneg_of I n) zero_le_one
  miss_le_one := fun n => min_le_right _ _
  success := fun δ hδ => by
    filter_upwards [hsuccess δ hδ] with n hn
    exact (min_le_left _ _).trans hn
  cost := cost
  cost_subexp := hcost
  overhead := overhead
  work := work
  work_nonneg := hwork_nonneg
  work_le := hwork_le

/-- **The ECM reduction to the P1 sub-bundle.** -/
def ecmP1SubInputs (I : L27_1Inputs) (hsuccess : PrepassSuccess I.loss)
    (cost : ℕ → ℝ) (hcost : ECMCostEnvelope cost)
    (overhead : ℕ) (work : ℕ → ℝ) (hwork_nonneg : ∀ n, 0 ≤ work n)
    (hwork_le : ∀ n, work n ≤
      ((n.log2 : ℝ) + 1) ^ overhead * cost n) :
    P1SubInputs :=
  (ecmAnalyticInputs I hsuccess cost hcost overhead work hwork_nonneg
    hwork_le).toP1SubInputs

/-- The ECM bundle obtained directly from the all-rates curve budget. -/
def ecmP1SubInputs_of_budget (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I) (hell : EllipticCurveGroupLaw I)
    (hbudget : ECMCurveBudgetAllRates I) (hlog : LogFactorSubexp I.cofactor)
    (cost : ℕ → ℝ) (hcost : ECMCostEnvelope cost)
    (overhead : ℕ) (work : ℕ → ℝ) (hwork_nonneg : ∀ n, 0 ≤ work n)
    (hwork_le : ∀ n, work n ≤
      ((n.log2 : ℝ) + 1) ^ overhead * cost n) :
    P1SubInputs :=
  ecmP1SubInputs I
    (ecmPrepassSuccess_of_budget I hdeuring hell hbudget hlog)
    cost hcost overhead work hwork_nonneg hwork_le

/-! ## 6. The trial-division cost obstruction -/

/-- **The trial-division cost obstruction.**  Trial division succeeds
deterministically on every input with a prime factor below its cutoff, but at
any cutoff reaching `roughThreshold` it is not affordable on the `exp (o (H))`
budget, and the logarithm of its proved work envelope is not little-o of
`scale`. -/
def TrialDivisionCostObstruction : Prop :=
  (∀ B : ℕ → ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      HardInput n → HasSmallPrimeFactor (B n : ℝ) n →
        (trialPrepass (B n) n).1 ≠ none) ∧
    (∀ B : ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, roughThreshold n ≤ (B n : ℝ)) →
        ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          (B n : ℝ) ≤ Real.exp (ε * scale n))) ∧
      ¬ PrepassCostSubexp trialDivisionExponent

/-- The obstruction is proved from the counted trial-division analysis. -/
theorem trialDivisionCostObstruction : TrialDivisionCostObstruction :=
  trialDivisionGap_sub

/-- **The trial-division exponent cannot be a P1 cost exponent.**  Every
`P1SubInputs` carries an `exp (o (H))` cost, while the trial-division envelope
is eventually larger than every multiple of `scale`. -/
theorem trialDivisionExponent_not_P1Cost (S : P1SubInputs)
    (hcost : S.costExponent = trialDivisionExponent) : False := by
  have hsub := S.cost_subexp
  rw [hcost] at hsub
  exact trialDivision_cost_not_subexp hsub

/-- **No P1 bundle can charge the trial-division work envelope.**  If the
charged work dominates the proved trial-division envelope
`54 · roughThreshold · n.size²`, then the polynomial overhead and the
`exp (o (H))` cost cannot both hold.

This is the work-level form of the trial-division obstruction: the cost
envelope is `exp ((log n)^{2/3} + O (log log n))`, whose logarithm exceeds any
fixed multiple of `scale`. -/
theorem trialDivision_envelope_obstruction (S : P1SubInputs)
    (hwork : ∀ᶠ n : ℕ in atTop,
      54 * roughThreshold n * (n.size : ℝ) ^ 2 ≤ S.work n) : False := by
  have hδ : 0 < (1 / 4 : ℝ) := by norm_num
  have hpoly :=
    eventually_bitPoly_le_exp (A := (1 : ℝ)) (ε := (1 / 4 : ℝ)) hδ S.overhead
  have hcost := S.costExponent_sublinear (1 / 4) hδ
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hwork, hpoly, hcost,
      eventually_logB_sub_log_two_le_trialDivisionExponent,
      eventually_scale_lt_logB_sub_log_two,
      scale_grows.eventually_ge_atTop 0, eventually_ge_atTop (1 : ℕ)]
      with n hw hp hc hlogB hscale hs hn1
    have hPpos : 0 < ((n.log2 : ℝ) + 1) ^ S.overhead := by positivity
    have hsize : (0 : ℝ) < (n.size : ℝ) := by
      exact_mod_cast Nat.size_pos.mpr (by omega : 0 < n)
    have hpos : 0 < 54 * roughThreshold n * (n.size : ℝ) ^ 2 :=
      mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (pow_pos hsize 2)
    have hexp_eq : Real.exp (trialDivisionExponent n) =
        54 * roughThreshold n * (n.size : ℝ) ^ 2 := by
      rw [trialDivisionExponent, Real.exp_log hpos]
    have hbig : Real.exp (trialDivisionExponent n) ≤
        ((n.log2 : ℝ) + 1) ^ S.overhead * Real.exp (S.costExponent n) := by
      calc
        Real.exp (trialDivisionExponent n)
            = 54 * roughThreshold n * (n.size : ℝ) ^ 2 := hexp_eq
        _ ≤ S.work n := hw
        _ ≤ ((n.log2 : ℝ) + 1) ^ S.overhead * Real.exp (S.costExponent n) :=
          S.work_le n
    have hlog := Real.log_le_log (Real.exp_pos (trialDivisionExponent n)) hbig
    rw [Real.log_exp] at hlog
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne'] at hlog
    rw [Real.log_exp] at hlog
    have hlogP :
        Real.log (((n.log2 : ℝ) + 1) ^ S.overhead) ≤ (1 / 4) * scale n :=
      (Real.log_le_iff_le_exp hPpos).mpr (by simpa using hp)
    have hTDE : trialDivisionExponent n ≤ (1 / 2) * scale n := by
      linarith
    have hhalf : (1 / 2) * scale n ≤ scale n := by linarith
    linarith
  obtain ⟨n, hn⟩ := hcontra.exists
  exact hn

/-! ## 7. Combined P1 analytic reduction -/

/-- **The P1 analytic reduction, in one statement.**  Genus-two success and
cost give a `P1SubInputs`; the ECM route is available under its two explicit
sub-Props; and the trial-division route is obstructed at both the exponent and
the work-envelope level. -/
theorem p1Analytic_reduction_summary (I : L30Inputs) :
    SubexpLoss (genusTwoAnalyticInputs I).miss ∧
      (∀ᶠ n : ℕ in atTop,
        (genusTwoAnalyticInputs I).miss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      PrepassCostSubexp (costExponentOf I.totalCost) ∧
      TrialDivisionCostObstruction :=
  ⟨(genusTwoAnalyticInputs I).subexpLoss,
    (genusTwoAnalyticInputs I).slot,
    genusTwoCostSubexp I,
    trialDivisionCostObstruction⟩

/-! ## Axiom audit -/

#print axioms subexpCostEnvelope_to_littleO
#print axioms cost_le_exp_costExponentOf
#print axioms P1AnalyticInputs.costSubexp
#print axioms P1AnalyticInputs.toP1SubInputs
#print axioms P1AnalyticInputs.subexpLoss
#print axioms P1AnalyticInputs.slot
#print axioms P1AnalyticInputs.costExponent_sublinear
#print axioms P1AnalyticInputs.toP1Leaf
#print axioms P1AnalyticInputs.repeated_work_add_one_le_exp
#print axioms p1Analytic_reduction
#print axioms genusTwoPrepassSuccess
#print axioms l30PrepassSuccess
#print axioms genusTwoCostEnvelope
#print axioms genusTwoCostSubexp
#print axioms genusTwoAnalyticInputs
#print axioms genusTwoP1SubInputs
#print axioms genusTwoP1Leaf
#print axioms curveBudget_of_allRates
#print axioms ecmPrepassSuccess_of_budget
#print axioms ecmPrepassSuccess_at_two
#print axioms ecmCostSubexp
#print axioms ecmAnalyticInputs
#print axioms ecmP1SubInputs
#print axioms ecmP1SubInputs_of_budget
#print axioms trialDivisionCostObstruction
#print axioms trialDivisionExponent_not_P1Cost
#print axioms trialDivision_envelope_obstruction
#print axioms p1Analytic_reduction_summary

end

end Cogentic.RandomizedP1Analytic
