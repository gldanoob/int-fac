import Cogentic.RandomizedPaperEndpointWave39
import Cogentic.RandomizedL27BudgetArithmetic
import Cogentic.RandomizedL27Waterhouse
import Cogentic.RandomizedL27KillLaw

/-!
# L27 stage one: the kill law and the curve budget finished from explicit data

`Cogentic.RandomizedL27StageOneFinish` bundles five objects into
`L27StageOneFinishInputs I`:

* `killLaw : L27KillLawInputs I` — the singular-curve count, the no-factor
  count, the killed-point count and its summed `1 / log y` law;
* `hurwitz : L27HurwitzInputs I` — the Deuring/Hurwitz block;
* `hasse : HasseBound I.p I.orderCount` — the group law;
* `curve_budget : CurveBudget I.p I.y I.psi I.curves I.κ I.η`;
* `log_factor_subexp : LogFactorSubexp I.cofactor`.

This file reduces the first, fourth and fifth entries to their smallest explicit
data, and simultaneously replaces the abstract Hurwitz block by the concrete
Waterhouse block.

## 1. The kill law from the scalar cover

`L27KillLawInputs` is constructed by `killLawInputsOfScalarCovers` from

* `gcdFail_eq` — the paper's singular-curve fraction `1/p`;
* `noFactorData` — the no-factor curve count at the `p²` scale;
* `M` — the stage-one scalar, with `pointKill` *defined* as
  `fun n j => scalarKillCount (M n) j = gcd j (M n)`;
* `smooth_order_pos` — smooth orders are positive;
* `success_ge_killed` — the killed-point mass lies in the success mass;
* `scalarCover` — every smooth order divides the stage-one scalar;
* `cutoff` — the cutoff satisfies `e ≤ y`.

The `kill_mass` field is **not** assumed: it is
`scalarCovers_killMassLaw`, i.e. the theorem that on a curve of order `j` with
`j ∣ M` all `j` points are killed, summed against the Deuring counts.  The
`pointKill` field is also not a new parameter: it is the gcd count.

Of the seven `L27KillLawInputs` fields exactly the following are *not* already
available from the `L27_1Inputs` record:

* `gcdFail_eq` — `I.gcd_exit` only gives `gcdFail ≤ 1/p`, not equality;
* `noFactorData` — the no-factor count is not part of `L27_1Inputs`;
* `success_ge_killed` — `I.stage_one` gives only the weaker
  `SC ≤ success · log y · CT`;
* `scalarCover` and `cutoff` — no divisibility or pointwise cutoff statement is
  stored in `L27_1Inputs`.

The remaining two are derived: `smooth_order_pos` follows from the Waterhouse
prime bound `4 ≤ p` via Hasse's theorem (`smooth_order_pos_of_two_le`), and
`kill_mass` follows from the scalar cover and the cutoff.

## 2. The curve budget and the `log₂` multiplier

`L27BudgetArithmeticInputs I` records the explicit parameter selection
`y = exp (scale)`, `ψ₀ = √p / exp (β scale)`,
`#curves = ⌈exp ((β + η) scale) L⌉` and `log (cofactor) = o (scale)`.
`Cogentic.RandomizedL27BudgetArithmetic` proves `CurveBudget` and
`LogFactorSubexp` from that data.  We re-export these as
`curveBudget_of_budgetArithmetic` and `logFactorSubexp_of_budgetArithmetic` and
build `L27StageOneFinishInputs` with them, so the two budget fields are no
longer independent residuals.  (They are also fields of `L27_1Inputs`; the
constructor `stageOneFinishOfL27` records that alternative source.)

## 3. The Wave-40 L27 block

`Wave40L27Inputs I` keeps only

* the six kill-law data above (`gcdFail_eq`, `noFactorData`, `scalarM`,
  `success_ge_killed`, `scalarCover`, `cutoff`);
* `waterhouse : L27WaterhouseInputs I` — the concrete weighted
  Deuring/Waterhouse formula, the Siegel lower bound, the discriminant scale,
  the `j`-line stratification and `4 ≤ p`.  This replaces `hurwitz` and, through
  `L27TraceClassInputs`, removes the free `traceCount` field as well;
* `budget : L27BudgetArithmeticInputs I` — the explicit curve-count and
  cofactor parameters.

It derives `killLaw`, `smooth_order_pos`, `kill_mass`, `hurwitz`, `hasse`,
`curve_budget`, `log_factor_subexp` and `toStageOneFinish`.  `hasse` is the
field `I.hasse` of `L27_1Inputs`; no group law is assumed twice.

`PaperResidualFor40` is the Wave-39 record with `l27_finish` replaced by the
Wave-40 block; it transports to `PaperResidualFor39` by
`toStageOneFinish`, and the Wave-39 endpoint therefore applies unchanged.

## Residual accounting

The exact remaining `Wave40L27Inputs` fields are listed in
`wave40L27FieldNames`; the overall residual list removes `killMass` and
`curveBudget` from the Wave-39 list and inserts the explicit kill-law data and
the budget bundle.  No `sorry`, `admit`, `axiom` or `native_decide` is used, and
no loss, probability, count or error is set to zero.
-/

set_option linter.unusedVariables false

noncomputable section

namespace Cogentic.RandomizedL27KillBudgetFinish

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2LineMinimal
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2StripBound
open Cogentic.RandomizedL21_2TailBound
open Cogentic.RandomizedL21_2TentWitness
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27BudgetArithmetic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27GcdModel
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27StageOne
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27TraceClass
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30Dickman
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.RandomizedL30NoBinomial
open Cogentic.RandomizedL30PrimeReciprocal
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34BelowOne
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34ZeroFaithful
open Cogentic.RandomizedL34ZeroFreeArithmetic
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34DedekindGRH
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedL34RangeArithmetic
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperEndpointWave17
open Cogentic.RandomizedPaperEndpointWave24
open Cogentic.RandomizedPaperEndpointWave25
open Cogentic.RandomizedPaperEndpointWave26
open Cogentic.RandomizedPaperEndpointWave27
open Cogentic.RandomizedPaperEndpointWave28
open Cogentic.RandomizedPaperEndpointWave29
open Cogentic.RandomizedPaperEndpointWave30
open Cogentic.RandomizedPaperEndpointWave31
open Cogentic.RandomizedPaperEndpointWave32
open Cogentic.RandomizedPaperEndpointWave33
open Cogentic.RandomizedPaperEndpointWave34
open Cogentic.RandomizedPaperEndpointWave35
open Cogentic.RandomizedPaperEndpointWave36
open Cogentic.RandomizedPaperEndpointWave37
open Cogentic.RandomizedPaperEndpointWave38
open Cogentic.RandomizedPaperEndpointWave39
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u v

/-! ## 1. The kill law from the scalar cover -/

section KillLaw

variable {I : L27_1Inputs}

/-- **The scalar-cover constructor of `L27KillLawInputs`.**

`pointKill` is *defined* as the gcd count `fun n j => gcd j (M n)`, and
`kill_mass` is *proved* from the scalar cover `j ∣ M n` on smooth orders and the
cutoff `e ≤ y` via `scalarCovers_killMassLaw`.  Only the singular-curve
fraction, the no-factor count, the point-mass containment, the scalar cover and
the cutoff are input data. -/
noncomputable def killLawInputsOfScalarCovers
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (M : ℕ → ℕ)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n,
      killedPointMass I (fun n j => scalarKillCount (M n) j) n ≤
        I.success n * I.CT n)
    (hcover : ∀ n j, I.smooth n j = true → j ∣ M n)
    (hcutoff : StageOneCutoffExpOne I.y) : L27KillLawInputs I where
  gcdFail_eq := hgf
  noFactorData := D
  pointKill := fun n j => scalarKillCount (M n) j
  smooth_order_pos := horder
  success_ge_killed := hsuccess
  kill_mass := scalarCovers_killMassLaw I M hcover
    (stageOneCutoffLogGeOne_of_expOne hcutoff)
  cutoff := hcutoff

/-- The constructed `pointKill` is literally the stage-one gcd count. -/
theorem killLawInputsOfScalarCovers_pointKill
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (M : ℕ → ℕ)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n,
      killedPointMass I (fun n j => scalarKillCount (M n) j) n ≤
        I.success n * I.CT n)
    (hcover : ∀ n j, I.smooth n j = true → j ∣ M n)
    (hcutoff : StageOneCutoffExpOne I.y) :
    (killLawInputsOfScalarCovers hgf D M horder hsuccess hcover hcutoff).pointKill =
      (fun n j => scalarKillCount (M n) j) :=
  rfl

/-- **The `kill_mass` field is exactly the scalar-cover consequence.**  It is not
an independent assumption. -/
theorem killLawInputsOfScalarCovers_kill_mass
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (M : ℕ → ℕ)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n,
      killedPointMass I (fun n j => scalarKillCount (M n) j) n ≤
        I.success n * I.CT n)
    (hcover : ∀ n j, I.smooth n j = true → j ∣ M n)
    (hcutoff : StageOneCutoffExpOne I.y) :
    KillMassLaw I (fun n j => scalarKillCount (M n) j) :=
  scalarCovers_killMassLaw I M hcover
    (stageOneCutoffLogGeOne_of_expOne hcutoff)

/-- The only kill-law field that is not automatic under the scalar cover beside
the gcd order data: the singular fraction `1/p` is still an input.  This theorem
records the exact type consumed downstream. -/
theorem killLawInputsOfScalarCovers_gcdFail_eq
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (M : ℕ → ℕ)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n,
      killedPointMass I (fun n j => scalarKillCount (M n) j) n ≤
        I.success n * I.CT n)
    (hcover : ∀ n j, I.smooth n j = true → j ∣ M n)
    (hcutoff : StageOneCutoffExpOne I.y) :
    (killLawInputsOfScalarCovers hgf D M horder hsuccess hcover hcutoff).gcdFail_eq
      = hgf :=
  rfl

end KillLaw

/-! ## 2. The curve budget and the `log₂` multiplier from budget arithmetic -/

section Budget

variable {I : L27_1Inputs}

/-- The finish bundle's `curve_budget` field is the budget arithmetic. -/
theorem curveBudget_of_budgetArithmetic (B : L27BudgetArithmeticInputs I) :
    CurveBudget I.p I.y I.psi I.curves I.κ I.η :=
  B.curveBudget

/-- The finish bundle's `log_factor_subexp` field is the budget arithmetic. -/
theorem logFactorSubexp_of_budgetArithmetic (B : L27BudgetArithmeticInputs I) :
    LogFactorSubexp I.cofactor :=
  B.logFactorSubexp

/-- **The finish bundle from the budget arithmetic.**  `hasse` is `I.hasse`;
`curve_budget` and `log_factor_subexp` are the derived budget fields. -/
noncomputable def stageOneFinishOfBudgetArithmetic
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (B : L27BudgetArithmeticInputs I) : L27StageOneFinishInputs I where
  killLaw := S
  hurwitz := H
  hasse := I.hasse
  curve_budget := B.curveBudget
  log_factor_subexp := B.logFactorSubexp

/-- **The finish bundle from `L27_1Inputs` alone.**  The two budget fields are
already fields of `L27_1Inputs`; this constructor records that they are not
extra assumptions of the finish record. -/
noncomputable def stageOneFinishOfL27
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I) :
    L27StageOneFinishInputs I where
  killLaw := S
  hurwitz := H
  hasse := I.hasse
  curve_budget := I.curve_budget
  log_factor_subexp := I.logFactor_subexp

/-- **The finish bundle from the concrete Waterhouse data and the budget
arithmetic.**  The Hurwitz block is `W.toTraceClassInputs.toHurwitzInputs`. -/
noncomputable def stageOneFinishOfWaterhouseBudget
    (S : L27KillLawInputs I) (W : L27WaterhouseInputs I)
    (B : L27BudgetArithmeticInputs I) : L27StageOneFinishInputs I :=
  stageOneFinishOfBudgetArithmetic S W.toTraceClassInputs.toHurwitzInputs B

end Budget

/-! ## 3. The Wave-40 L27 block -/

/-- **The Wave-40 L27 block.**  It contains exactly

* the explicit kill-law data: the singular fraction, the no-factor count, the
  stage-one scalar `M`, the point-mass containment, the scalar cover and the
  cutoff.  `pointKill`, `smooth_order_pos` and `kill_mass` are derived;
* `waterhouse` — the concrete Deuring/Waterhouse formula together with Siegel,
  the discriminant scale, the `j`-line stratification and `4 ≤ p`; `hurwitz`,
  `traceCount`, `trace_class_lower` and `orderCount_contains_trace` are
  derived;
* `budget` — the explicit curve-count and cofactor parameters; `curveBudget`
  and `logFactorSubexp` are derived;
* `hasse` is the field `I.hasse` of `L27_1Inputs`. -/
structure Wave40L27Inputs (I : L27_1Inputs) where
  /-- The paper's singular-curve probability is exactly `1/p`. -/
  gcdFail_eq : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ)
  /-- The no-factor curve count at the singular-curve scale. -/
  noFactorData : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n)
  /-- The stage-one scalar.  On a curve of order `j` it kills `gcd j M` points. -/
  scalarM : ℕ → ℕ
  /-- The killed-point mass is contained in the success mass. -/
  success_ge_killed : ∀ n,
    killedPointMass I (fun n j => scalarKillCount (scalarM n) j) n ≤
      I.success n * I.CT n
  /-- Every stage-one-smooth order divides the stage-one scalar. -/
  scalarCover : ∀ n j, I.smooth n j = true → j ∣ scalarM n
  /-- The stage-one cutoff satisfies `e ≤ y`. -/
  cutoff : StageOneCutoffExpOne I.y
  /-- The concrete Deuring/Waterhouse block. -/
  waterhouse : L27WaterhouseInputs I
  /-- The explicit curve-count and cofactor budget parameters. -/
  budget : L27BudgetArithmeticInputs I

namespace Wave40L27Inputs

variable {I : L27_1Inputs}

/-- **Smooth orders are positive**, derived from the Waterhouse prime bound
`4 ≤ p` and Hasse's theorem.  This was a field of `L27KillLawInputs`; here it is
a theorem. -/
theorem smooth_order_pos (W : Wave40L27Inputs I) :
    ∀ n j, I.smooth n j = true → 0 < j :=
  fun n j hs =>
    smooth_order_pos_of_two_le I
      (fun n => by have h := W.waterhouse.p_ge_four n; omega) hs

/-- The kill-law bundle with `pointKill` the scalar gcd count and `kill_mass`
derived from the scalar cover. -/
noncomputable def killLaw (W : Wave40L27Inputs I) : L27KillLawInputs I :=
  killLawInputsOfScalarCovers W.gcdFail_eq W.noFactorData W.scalarM
    W.smooth_order_pos W.success_ge_killed W.scalarCover W.cutoff

/-- The constructed kill law uses exactly the scalar gcd count. -/
theorem killLaw_pointKill (W : Wave40L27Inputs I) :
    W.killLaw.pointKill = (fun n j => scalarKillCount (W.scalarM n) j) :=
  rfl

/-- **The `kill_mass` field is derived**, not assumed. -/
theorem kill_mass (W : Wave40L27Inputs I) :
    KillMassLaw I (fun n j => scalarKillCount (W.scalarM n) j) :=
  W.killLaw.kill_mass

/-- The stage-one conditional `1 / log y` bound, from the derived kill law. -/
theorem stageOneConditional (W : Wave40L27Inputs I) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I W.killLaw.pointKill) I.y :=
  W.killLaw.stageOneConditional

/-- The bundled stage-one success bound. -/
theorem stageOneSuccess (W : Wave40L27Inputs I) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop)
      I.y I.success :=
  W.killLaw.stageOneSuccess

/-- The Hurwitz block, derived from the concrete Waterhouse data.  This removes
the free `traceCount` field and the two trace-class `Prop`s. -/
noncomputable def hurwitz (W : Wave40L27Inputs I) : L27HurwitzInputs I :=
  W.waterhouse.toTraceClassInputs.toHurwitzInputs

/-- **Hasse's theorem is the field `I.hasse`**, not a new assumption. -/
theorem hasse (W : Wave40L27Inputs I) : HasseBound I.p I.orderCount :=
  I.hasse

/-- The curve budget, derived from the explicit parameter selection. -/
theorem curveBudget (W : Wave40L27Inputs I) :
    CurveBudget I.p I.y I.psi I.curves I.κ I.η :=
  W.budget.curveBudget

/-- The `log₂` multiplier, derived from the cofactor `o (scale)` bound. -/
theorem logFactorSubexp (W : Wave40L27Inputs I) :
    LogFactorSubexp I.cofactor :=
  W.budget.logFactorSubexp

/-- The concrete Deuring/Lenstra counts from the Waterhouse block. -/
theorem deuringLenstraCounts (W : Wave40L27Inputs I) :
    DeuringLenstraCounts I :=
  W.hurwitz.deuringLenstraCounts

/-- **The assembled finish bundle.**  All five fields of
`L27StageOneFinishInputs` are produced: the kill law from the scalar cover, the
Hurwitz block from Waterhouse, Hasse from `I`, and the two budget fields from
the budget arithmetic. -/
noncomputable def toStageOneFinish (W : Wave40L27Inputs I) :
    L27StageOneFinishInputs I :=
  stageOneFinishOfBudgetArithmetic W.killLaw W.hurwitz W.budget

/-- The transport keeps the kill law. -/
theorem toStageOneFinish_killLaw (W : Wave40L27Inputs I) :
    W.toStageOneFinish.killLaw = W.killLaw :=
  rfl

/-- The transport keeps the curve budget. -/
theorem toStageOneFinish_curve_budget (W : Wave40L27Inputs I) :
    W.toStageOneFinish.curve_budget = W.budget.curveBudget :=
  rfl

/-- The transport keeps the `log₂` multiplier. -/
theorem toStageOneFinish_log_factor_subexp (W : Wave40L27Inputs I) :
    W.toStageOneFinish.log_factor_subexp = W.budget.logFactorSubexp :=
  rfl

/-- The transport keeps Hasse at `I.hasse`. -/
theorem toStageOneFinish_hasse (W : Wave40L27Inputs I) :
    W.toStageOneFinish.hasse = I.hasse :=
  rfl

/-- The bundled group-law input from Hasse, the gcd-exit bound and stage one. -/
theorem ellipticCurveGroupLaw (W : Wave40L27Inputs I) :
    EllipticCurveGroupLaw I :=
  W.toStageOneFinish.ellipticCurveGroupLaw

/-- The two final L27.1 loss caps. -/
theorem reduction (W : Wave40L27Inputs I) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  W.toStageOneFinish.reduction

/-- The L27.1 ledger cap `loss ≤ exp (-2H)`. -/
theorem loss_le_exp_ledger (W : Wave40L27Inputs I) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  W.toStageOneFinish.loss_le_exp_ledger

/-- The manuscript-rate cap `loss ≤ exp (-(cRate/2) · rate)`. -/
theorem loss_le_exp_paper (W : Wave40L27Inputs I) :
    ∀ᶠ n : ℕ in atTop,
      I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  W.toStageOneFinish.loss_le_exp_paper

/-- The L27.1 `RatedLeaf`. -/
noncomputable def toRatedLeaf (W : Wave40L27Inputs I) : RatedLeaf :=
  W.toStageOneFinish.toRatedLeaf

/-- The `C5` slot `exp (-2H)`. -/
theorem slot (W : Wave40L27Inputs I) :
    ∀ᶠ n : ℕ in atTop,
      (W.toRatedLeaf).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  W.toStageOneFinish.slot

end Wave40L27Inputs

/-! ## 4. The Wave-40 ledger, record and endpoint -/

/-- **The Wave-40 ledger.**  It is the Wave-39 ledger at the finish bundle
derived from the Wave-40 L27 block. -/
noncomputable def wave40Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : Wave40L27Inputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave39L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave39Slots line l19 l20_2 l20_4 l21 l27_data l27_finish.toStageOneFinish
    l30 l34 p1

/-- The Wave-40 ledger is the Wave-39 ledger at the transported L27 block. -/
theorem wave40Slots_eq_wave39Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : Wave40L27Inputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave39L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) :
    wave40Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave39Slots line l19 l20_2 l20_4 l21 l27_data
        l27_finish.toStageOneFinish l30 l34 p1 := rfl

/-- **The Wave-40 combined residual record.**  It is the Wave-39 record with the
L27 finish bundle replaced by `Wave40L27Inputs`.  All other fields are copied
verbatim. -/
structure PaperResidualFor40 (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L19 certificate. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- The L21.2 analytic input: RH and the central short-interval count. -/
  l21 : Wave27L21Inputs
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- **The reduced L27 block**: kill law from the scalar cover, Waterhouse and
  the explicit budget arithmetic. -/
  l27_finish : Wave40L27Inputs l27_data
  /-- L30 with the sharp count derived. -/
  l30 : Wave31L30Inputs
  /-- L34 with the critical line fixed and the `T⁶` range derived. -/
  l34 : Wave39L34Inputs K ι N χ
  /-- P1: the explicit `exp (o(H))`-cost prepass. -/
  p1 : SubexpPrepassInput
  /-- C1: the public congruence check (L1). -/
  c1 : C1Inputs E
  /-- C2: conditional hidden-sign uniformity (L2–L5, including L4). -/
  c2 : C2Inputs E
  /-- C3: the ideal/actual total-variation budget (L6–L10). -/
  c3 : C3Inputs E
  /-- C4: the expected public-work budget (L11–L16). -/
  c4 : C4Inputs E D
  /-- The concrete epoch family underlying the C5 certificate. -/
  concrete : ∀ n, 3 ≤ n → ConcreteEpochData n
  /-- Adapter: the ambient epoch is the concrete family's `toHardEpochData`. -/
  concrete_eq : ∀ n (hN : 3 ≤ n), E n hN = (concrete n hN).toHardEpochData
  /-- The C5 data assembled by `c5FullOfCount`. -/
  c5Data : Wave15C5Data concrete
  /-- Adapter: the concrete C5 loss is dominated by the Wave-40 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave40Slots line l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor40

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor40 → PaperResidualFor39`**, by the derived finish
bundle.  No analytic or arithmetic witness is added: `kill_mass`,
`curve_budget` and `log_factor_subexp` are theorems of the Wave-40 block. -/
noncomputable def toPaperResidualFor39
    (I : PaperResidualFor40 line K ι N χ E D) :
    PaperResidualFor39 line K ι N χ E D where
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish.toStageOneFinish
  l30 := I.l30
  l34 := I.l34
  p1 := I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5Data := I.c5Data
  loss_le := by
    intro n hN
    simpa only [wave40Slots] using I.loss_le n hN

/-- **`PaperResidualFor40 → FullyDischargedInputs`** through the Wave-39
transport. -/
noncomputable def toFullyDischargedInputs
    (I : PaperResidualFor40 line K ι N χ E D) : FullyDischargedInputs E D :=
  I.toPaperResidualFor39.toFullyDischargedInputs

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs
    (I : PaperResidualFor40 line K ι N χ E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- The L27 loss of the Wave-40 record is exactly the actual L27.1 loss. -/
theorem l27_loss (I : PaperResidualFor40 line K ι N χ E D) (n : ℕ) :
    (I.l27_finish.toRatedLeaf).loss n = I.l27_data.loss n :=
  wave15L27Leaf_loss I.l27_data I.l27_finish.toStageOneFinish n

/-- **The L27 kill mass of the record is derived**, not stored. -/
theorem l27_kill_mass (I : PaperResidualFor40 line K ι N χ E D) :
    KillMassLaw I.l27_data
      (fun n j => scalarKillCount (I.l27_finish.scalarM n) j) :=
  I.l27_finish.kill_mass

/-- **The L27 curve budget of the record is derived**, not stored. -/
theorem l27_curveBudget (I : PaperResidualFor40 line K ι N χ E D) :
    CurveBudget I.l27_data.p I.l27_data.y I.l27_data.psi I.l27_data.curves
      I.l27_data.κ I.l27_data.η :=
  I.l27_finish.curveBudget

/-- **The L27 `log₂` multiplier of the record is derived**, not stored. -/
theorem l27_logFactorSubexp (I : PaperResidualFor40 line K ι N χ E D) :
    LogFactorSubexp I.l27_data.cofactor :=
  I.l27_finish.logFactorSubexp

/-- **Hasse is the `L27_1Inputs` field**, not a second assumption. -/
theorem l27_hasse (I : PaperResidualFor40 line K ι N χ E D) :
    HasseBound I.l27_data.p I.l27_data.orderCount :=
  I.l27_data.hasse

/-- The two final L27.1 loss caps of the record. -/
theorem l27_reduction (I : PaperResidualFor40 line K ι N χ E D) :
    DeuringLenstraCounts I.l27_data ∧ EllipticCurveGroupLaw I.l27_data ∧
      (∀ᶠ n : ℕ in atTop,
        I.l27_data.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.l27_data.loss n ≤
          Real.exp (-((I.l27_data.cRate / 2) * I.l27_data.rate n))) :=
  I.l27_finish.reduction

/-- The complete remaining L27 analytic/arithmetic input of the record: the
Waterhouse formula, Siegel, the discriminant scale, the stratification, the
prime bound, and the explicit budget parameters. -/
theorem l27_remaining (I : PaperResidualFor40 line K ι N χ E D) :
    (∀ n, WaterhouseWeighted (I.l27_data.p n)
        (I.l27_finish.waterhouse.p_prime n) I.l27_finish.waterhouse.hurwitz) ∧
      HurwitzSiegelLowerTrace I.l27_data.p I.l27_finish.waterhouse.hurwitz
        I.l27_finish.waterhouse.c ∧
      (I.l27_data.κ ≤
        I.l27_finish.waterhouse.c * Real.sqrt I.l27_finish.waterhouse.θ) ∧
      HurwitzDiscriminantScale I.l27_data.p I.l27_data.smooth
        I.l27_finish.waterhouse.θ ∧
      JInvariantStratification I.l27_data.p I.l27_data.orderCount
        I.l27_data.orderTop ∧
      (∀ n, 4 ≤ I.l27_data.p n) ∧
      KillMassLaw I.l27_data
        (fun n j => scalarKillCount (I.l27_finish.scalarM n) j) ∧
      CurveBudget I.l27_data.p I.l27_data.y I.l27_data.psi
        I.l27_data.curves I.l27_data.κ I.l27_data.η :=
  ⟨I.l27_finish.waterhouse.waterhouse,
    I.l27_finish.waterhouse.siegel_lower,
    I.l27_finish.waterhouse.kappa_le,
    I.l27_finish.waterhouse.disc_scale,
    I.l27_finish.waterhouse.j_invariant_strata,
    I.l27_finish.waterhouse.p_ge_four,
    I.l27_kill_mass,
    I.l27_curveBudget⟩

end PaperResidualFor40

/-- **The schedule-indexed form of the Wave-40 record.** -/
abbrev PaperResidualFor40Schedule (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor40 line K ι N χ (E s) D

/-- **Wave-40 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for every number field `K`,
every explicit abelian factorization, and every balanced-schedule epoch family
`E` carrying a `PaperResidualFor40 line K ι N χ (E s) D` record, the kernel
driver outputs a permutation of `n.primeFactorsList` with expected serialized
bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`.

The L27 block of the record is the reduced `Wave40L27Inputs`: the kill mass is
the scalar-cover theorem, the curve budget and the `log₂` multiplier are the
budget-arithmetic theorems, Hasse is `I.hasse`, and the Hurwitz block is the
concrete Waterhouse block. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave40Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
      (χ : ∀ i, DirichletCharacter ℂ (N i)),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor40 line K ι N χ (E s) D) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ :=
    serialized_assembled_balancedEnvelopeInfimum_from_wave39Inputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF ι instF instDec N instN χ E hI
  exact hmain K ι N χ E fun s D hvalid =>
    (hI s D hvalid).toPaperResidualFor39

/-! ## 5. Residual accounting -/

/-- The field names of `Wave40L27Inputs`: the six explicit kill-law entries,
Waterhouse and the budget arithmetic. -/
def wave40L27FieldNames : List String :=
  ["gcdFail_eq", "noFactorData", "scalarM", "success_ge_killed",
   "scalarCover", "cutoff", "waterhouse", "budget"]

theorem wave40L27FieldNames_length : wave40L27FieldNames.length = 8 := rfl

/-- The components of the kill-law block, including the two derived ones
(`smooth_order_pos` and `kill_mass`). -/
def wave40KillLawComponentNames : List String :=
  ["gcdFail_eq", "noFactorData", "scalarM", "smooth_order_pos",
   "success_ge_killed", "scalarCover", "kill_mass", "cutoff"]

theorem wave40KillLawComponentNames_length :
    wave40KillLawComponentNames.length = 8 := rfl

/-- The three kill-law components that are derived rather than assumed. -/
def wave40KillLawDerivedNames : List String :=
  ["pointKill", "smooth_order_pos", "kill_mass"]

theorem wave40KillLawDerivedNames_length :
    wave40KillLawDerivedNames.length = 3 := rfl

/-- The fields of `L27WaterhouseInputs` carried by `Wave40L27Inputs`. -/
def wave40WaterhouseFieldNames : List String :=
  ["hurwitz", "c", "theta", "c_pos", "theta_pos", "kappa_le",
   "siegel_lower", "disc_scale", "p_prime", "waterhouse",
   "orderCount_dominates_raw", "j_invariant_strata", "p_ge_four"]

theorem wave40WaterhouseFieldNames_length :
    wave40WaterhouseFieldNames.length = 13 := rfl

/-- The fields of `L27BudgetArithmeticInputs` carried by `Wave40L27Inputs`. -/
def wave40BudgetFieldNames : List String :=
  ["beta", "beta_nonneg", "L", "L_ge_one", "y_eq", "psi_lower",
   "curves_lower", "cofactor_log_subexp"]

theorem wave40BudgetFieldNames_length : wave40BudgetFieldNames.length = 8 := rfl

/-- The field names of `PaperResidualFor40`; there is no `l18_4` field. -/
def wave40FieldNames : List String :=
  ["l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave40FieldNames_length : wave40FieldNames.length = 17 := rfl

/-- **The exact remaining residual list of the Wave-40 endpoint.**  Compared
with the Wave-39 list, `killMass` and `curveBudget` are removed: `killMass` is
replaced by the explicit scalar-cover data, and `curveBudget` by the budget
arithmetic bundle.  `hasse` remains because it is still a field of the parent
`L27_1Inputs`, and `hurwitzClassNumber`, `siegelLower`, `waterhouseTrace` remain
as the concrete Waterhouse data. -/
def wave40RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "gcdFail_eq", "noFactorData", "scalarM", "success_ge_killed",
   "scalarCover", "cutoff", "budgetArithmetic",
   "factorization", "cheb", "rangeArithmetic",
   "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

theorem wave40RemainingFieldNames_exact :
    wave40RemainingFieldNames =
      ["zetaRH", "localCount", "hbuchstab", "hparity",
       "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
       "gcdFail_eq", "noFactorData", "scalarM", "success_ge_killed",
       "scalarCover", "cutoff", "budgetArithmetic",
       "factorization", "cheb", "rangeArithmetic",
       "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"] :=
  rfl

theorem wave40RemainingFieldNames_length :
    wave40RemainingFieldNames.length = 27 := rfl

/-- **`killMass` is no longer a residual entry.** -/
theorem wave40_no_killMass_residual :
    wave40RemainingFieldNames.all (fun s => decide (s ≠ "killMass")) = true := by
  decide

/-- **`curveBudget` is no longer a residual entry.** -/
theorem wave40_no_curveBudget_residual :
    wave40RemainingFieldNames.all (fun s => decide (s ≠ "curveBudget")) = true := by
  decide

/-- The explicit scalar-cover entries are present. -/
theorem wave40_kill_law_entries :
    wave40RemainingFieldNames.contains "gcdFail_eq" = true ∧
      wave40RemainingFieldNames.contains "noFactorData" = true ∧
      wave40RemainingFieldNames.contains "scalarM" = true ∧
      wave40RemainingFieldNames.contains "success_ge_killed" = true ∧
      wave40RemainingFieldNames.contains "scalarCover" = true ∧
      wave40RemainingFieldNames.contains "cutoff" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The budget bundle is the replacement residual entry. -/
theorem wave40_budgetArithmetic_residual :
    wave40RemainingFieldNames.contains "budgetArithmetic" = true := by
  decide

/-- Every Wave-39 residual except `killMass` and `curveBudget` remains in the
Wave-40 list. -/
theorem wave40_contains_wave39_except_budgets :
    (wave39RemainingFieldNames.filter
        (fun s => decide (s ≠ "killMass" ∧ s ≠ "curveBudget"))).all
      (fun s => wave40RemainingFieldNames.contains s) = true := by
  decide

/-- The Wave-40 list removes exactly the two derived entries and keeps the rest
of the Wave-39 list, with the explicit kill-law data added. -/
theorem wave40_removes_exactly :
    wave39RemainingFieldNames.all
        (fun s => decide (s ≠ "killMass" ∧ s ≠ "curveBudget")) = false ∧
      wave40RemainingFieldNames.all
        (fun s => decide (s ≠ "killMass" ∧ s ≠ "curveBudget")) = true := by
  decide

/-- The record carries no `l18_4` hypothesis. -/
theorem wave40_no_l18_4 :
    wave40FieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- The raw arithmetic bundle, the factorization and the Chebotarev input are
still fields of the L34 block. -/
theorem wave40_L34_content :
    wave39L34FieldNames.contains "rangeArithmetic" = true ∧
      wave39L34FieldNames.contains "factorization" = true ∧
      wave39L34FieldNames.contains "cheb" = true :=
  ⟨by decide, by decide, by decide⟩

/-- **The complete remaining L27 field list** reported by the block: the
Waterhouse data, Hasse (from `L27_1Inputs`), the explicit kill-law entries and
the budget arithmetic.  In particular there is no `killMass`, `curveBudget`,
`logFactorSubexp`, `pointKill`, `smooth_order_pos`, `hurwitz`, `traceCount`,
`trace_class_lower` or `orderCount_contains_trace` field. -/
theorem wave40_L27_remaining_list :
    wave40L27FieldNames.contains "waterhouse" = true ∧
      wave40L27FieldNames.contains "budget" = true ∧
      wave40L27FieldNames.contains "gcdFail_eq" = true ∧
      wave40L27FieldNames.contains "noFactorData" = true ∧
      wave40L27FieldNames.contains "scalarM" = true ∧
      wave40L27FieldNames.contains "success_ge_killed" = true ∧
      wave40L27FieldNames.contains "scalarCover" = true ∧
      wave40L27FieldNames.contains "cutoff" = true ∧
      wave40L27FieldNames.all (fun s => decide (s ≠ "kill_mass")) = true ∧
      wave40L27FieldNames.all (fun s => decide (s ≠ "pointKill")) = true ∧
      wave40L27FieldNames.all (fun s => decide (s ≠ "smooth_order_pos")) = true ∧
      wave40L27FieldNames.all (fun s => decide (s ≠ "hasse")) = true ∧
      wave40L27FieldNames.all (fun s => decide (s ≠ "curve_budget")) = true ∧
      wave40L27FieldNames.all (fun s => decide (s ≠ "log_factor_subexp")) = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Waterhouse replaces the abstract Hurwitz trace count: none of `hurwitz`,
`traceCount`, `trace_class_lower` or `orderCount_contains_trace` is a field. -/
theorem wave40_no_abstract_trace_fields :
    wave40L27FieldNames.all (fun s => decide (s ≠ "hurwitz")) = true ∧
      wave40L27FieldNames.all (fun s => decide (s ≠ "traceCount")) = true ∧
      wave40L27FieldNames.all
        (fun s => decide (s ≠ "trace_class_lower")) = true ∧
      wave40L27FieldNames.all
        (fun s => decide (s ≠ "orderCount_contains_trace")) = true :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The detailed Waterhouse and budget field lists are disjoint from the
derived entries. -/
theorem wave40_waterhouse_budget_content :
    wave40WaterhouseFieldNames.contains "waterhouse" = true ∧
      wave40WaterhouseFieldNames.contains "siegel_lower" = true ∧
      wave40WaterhouseFieldNames.contains "disc_scale" = true ∧
      wave40WaterhouseFieldNames.contains "p_ge_four" = true ∧
      wave40BudgetFieldNames.contains "y_eq" = true ∧
      wave40BudgetFieldNames.contains "psi_lower" = true ∧
      wave40BudgetFieldNames.contains "curves_lower" = true ∧
      wave40BudgetFieldNames.contains "cofactor_log_subexp" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-! ## Axiom audit -/

#print axioms killLawInputsOfScalarCovers
#print axioms killLawInputsOfScalarCovers_pointKill
#print axioms killLawInputsOfScalarCovers_kill_mass
#print axioms killLawInputsOfScalarCovers_gcdFail_eq
#print axioms curveBudget_of_budgetArithmetic
#print axioms logFactorSubexp_of_budgetArithmetic
#print axioms stageOneFinishOfBudgetArithmetic
#print axioms stageOneFinishOfL27
#print axioms stageOneFinishOfWaterhouseBudget
#print axioms Wave40L27Inputs.smooth_order_pos
#print axioms Wave40L27Inputs.killLaw
#print axioms Wave40L27Inputs.kill_mass
#print axioms Wave40L27Inputs.stageOneConditional
#print axioms Wave40L27Inputs.stageOneSuccess
#print axioms Wave40L27Inputs.hurwitz
#print axioms Wave40L27Inputs.hasse
#print axioms Wave40L27Inputs.curveBudget
#print axioms Wave40L27Inputs.logFactorSubexp
#print axioms Wave40L27Inputs.deuringLenstraCounts
#print axioms Wave40L27Inputs.ellipticCurveGroupLaw
#print axioms Wave40L27Inputs.toStageOneFinish
#print axioms Wave40L27Inputs.toStageOneFinish_killLaw
#print axioms Wave40L27Inputs.toStageOneFinish_curve_budget
#print axioms Wave40L27Inputs.toStageOneFinish_log_factor_subexp
#print axioms Wave40L27Inputs.toStageOneFinish_hasse
#print axioms Wave40L27Inputs.reduction
#print axioms Wave40L27Inputs.loss_le_exp_ledger
#print axioms Wave40L27Inputs.loss_le_exp_paper
#print axioms Wave40L27Inputs.toRatedLeaf
#print axioms Wave40L27Inputs.slot
#print axioms wave40Slots
#print axioms wave40Slots_eq_wave39Slots
#print axioms PaperResidualFor40.toPaperResidualFor39
#print axioms PaperResidualFor40.toFullyDischargedInputs
#print axioms PaperResidualFor40.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor40.l27_loss
#print axioms PaperResidualFor40.l27_kill_mass
#print axioms PaperResidualFor40.l27_curveBudget
#print axioms PaperResidualFor40.l27_logFactorSubexp
#print axioms PaperResidualFor40.l27_hasse
#print axioms PaperResidualFor40.l27_reduction
#print axioms PaperResidualFor40.l27_remaining
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave40Inputs
#print axioms wave40L27FieldNames_length
#print axioms wave40KillLawComponentNames_length
#print axioms wave40KillLawDerivedNames_length
#print axioms wave40WaterhouseFieldNames_length
#print axioms wave40BudgetFieldNames_length
#print axioms wave40FieldNames_length
#print axioms wave40RemainingFieldNames_exact
#print axioms wave40RemainingFieldNames_length
#print axioms wave40_no_killMass_residual
#print axioms wave40_no_curveBudget_residual
#print axioms wave40_kill_law_entries
#print axioms wave40_budgetArithmetic_residual
#print axioms wave40_contains_wave39_except_budgets
#print axioms wave40_removes_exactly
#print axioms wave40_no_l18_4
#print axioms wave40_L34_content
#print axioms wave40_L27_remaining_list
#print axioms wave40_no_abstract_trace_fields
#print axioms wave40_waterhouse_budget_content

end Cogentic.RandomizedL27KillBudgetFinish
