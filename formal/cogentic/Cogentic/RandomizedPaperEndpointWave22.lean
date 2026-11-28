import Cogentic.RandomizedPaperEndpointWave21
import Cogentic.RandomizedPaperEndpointWave18L34
import Cogentic.RandomizedL21_2ConcreteLeaf
import Cogentic.RandomizedL34FactorialBudgets

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 22: the combined L21.2 and L34 residual record

`Cogentic.RandomizedPaperEndpointWave21.PaperResidualInputsL21` collapses the
24 L21.2 fields of `PaperResidualInputs` (`zetaRH` plus the 23 `l21*` fields)
into the two-component `ConcreteLeafResidual`:

```
l21 : ConcreteLeafResidual :=
  { zeta : ZetaSide, localCount : ShortIntervalSmoothCountLower ... }
```

but it still carries the bundled L34 field `l34 : L34EffectiveChebotarevInputs`,
whose two arithmetic components `error_log` and `degree_log` are the logarithmic
factorial budgets.

`Cogentic.RandomizedPaperEndpointWave18L34.PaperResidualInputsL34` exposes the
raw Chebotarev parameters and *derives* those two budgets from the explicit
thresholds of `Cogentic.RandomizedL34FactorialBudgets`.

This file combines both reductions in one record:

```
structure PaperResidualInputsFinal (D : ℝ) where
  line : DirichletLZerosOnLine
  l21  : ConcreteLeafResidual
  -- L30, L27, raw L34, L18.4, L19, L20, P1 and C1–C4, unchanged
```

The raw L34 block is copied verbatim from `PaperResidualInputsL34`, including
the uniform threshold hypothesis `l34BudgetThreshold`.  The two factorial
budgets are **not** fields: they are derived by the Wave-18 L34 adapter
`PaperResidualInputsL34.toL34` (which invokes
`chebotarevErrorLogBudget_of_threshold` and
`degreeLossLogBudget_of_threshold` from `RandomizedL34FactorialBudgets`).

## Field count

```
PaperResidualInputs       73 fields
PaperResidualInputsL21    50 fields  (= 73 - 24 + 1)
PaperResidualInputsL34   111 fields  (= 73 -  1 + 39)
PaperResidualInputsFinal  88 fields  (= 50 -  1 + 39 = 73 - 24 + 1 - 1 + 39)
```

The first 24 L21.2 fields (`zetaRH` and the 23 `l21*` fields) are replaced by
the single field `l21`; the L34 bundle (1 field) is replaced by 39 raw fields.
The two L34 budgets `error_log` and `degree_log` are among the derived data and
are not fields of the final record.

## Main reductions

* `PaperResidualInputsFinal.toL21` builds `PaperResidualInputsL21` by reusing
  the Wave-21 L21.2 leaf and the Wave-18L34 `toL34` adapter;
* `PaperResidualInputsFinal.toPaperResidualInputs` composes with the Wave-21
  transport `PaperResidualInputsL21.toPaperResidualInputs`;
* `serialized_assembled_balancedEnvelopeInfimum_from_wave22Inputs` is the
  endpoint, obtained by applying the Wave-21 endpoint to the `toL21` family.

No field is re-assumed: `l21` is passed to `wave17InputsOfResidual` and the raw
L34 block is passed to `PaperResidualInputsL34.toL34`.  No `sorry`, `admit`,
`axiom` or `native_decide` is used, and no loss, count, probability or error is
set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave22

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2LineMinimal
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2TailBound
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27ClassNumber
open Cogentic.RandomizedL27Fiber
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27HurwitzAssembly
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27LOneSiegel
open Cogentic.RandomizedL27Scale
open Cogentic.RandomizedL27Siegel
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Stratification
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL27Weighted
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30UpperDensity
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34LogIntegral
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34EffectiveChebotarev
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedL34FactorialBudgets
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperEndpointWave17
open Cogentic.RandomizedPaperEndpointWave18
open Cogentic.RandomizedPaperEndpointWave18L34
open Cogentic.RandomizedPaperEndpointWave21
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit
open Cogentic.RandomizedWave18Audit
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver

universe u

/-! ## The final combined residual record -/

/-- **The Wave-22 final residual inputs.**

This is the Wave-21 record with the L34 bundle replaced by the raw Chebotarev
parameters of the Wave-18L34 record.  Concretely:

* the whole L21.2 block is the two-component `ConcreteLeafResidual`;
* the L34 block consists of the raw parameters `l34Beta0` … `l34PTrialLeOne`
  (including the uniform threshold `l34BudgetThreshold`), while the factorial
  factor `F = (2d)!`, the real degree `fun n => (l34Degree n : ℝ)`, the bracket
  constant `cbr = 1/16`, the `T → ∞` fact and the two logarithmic factorial
  budgets are **derived** by the adapter;
* L30, L27, L18.4, L19, L20.2, L20.4, P1 and C1–C4 are copied verbatim. -/
structure PaperResidualInputsFinal (D : ℝ) where
  /-- **GRH for Dirichlet `L`-functions.** -/
  line : DirichletLZerosOnLine
  /-- **The whole L21.2 analytic input**: the zeta side (RH, zero-freeness on
  `Re s = 2/3`, and the two-sided line estimate with a raw constant) together
  with the literal central short-interval smooth count. -/
  l21 : ConcreteLeafResidual

  -- L30
  /-- The prime whose genus-two order is counted. -/
  l30p : ℕ → ℝ
  /-- Paper density growth of `l30p`. -/
  l30Growth : PaperDensityGrowth l30p
  /-- The `1 + o(1)` relative error. -/
  l30ε : ℝ
  /-- `ε > 0`. -/
  l30ε_pos : 0 < l30ε
  /-- The relative short-interval density constant. -/
  l30A : ℝ
  /-- The global smooth lower-bound constant. -/
  l30B : ℝ
  /-- `B > 0`. -/
  l30B_pos : 0 < l30B
  /-- `B ≤ 1/8`. -/
  l30B_le_eighth : l30B ≤ 1 / 8
  /-- `4 ≤ A B`. -/
  l30AB_ge_four : 4 ≤ l30A * l30B
  /-- The paper short-count constant. -/
  l30c : ℝ
  /-- The global odd upper-density constant. -/
  l30C : ℝ
  /-- `A > 0`. -/
  l30A_pos : 0 < l30A
  /-- `32 ≤ A`. -/
  l30A_ge_32 : 32 ≤ l30A
  /-- `A C ≤ c`. -/
  l30AC_le : l30A * l30C ≤ l30c
  /-- `C > 0`. -/
  l30C_pos : 0 < l30C
  /-- **The sharp paper-scale global odd upper density.**  The exponential
  factor is the true Dickman exponent `u log u`. -/
  l30SharpUpper : GlobalOddUpperDensitySharp l30C l30p l30ε
  /-- **The sharp central Younis interval count**, with the same exponent
  `u log u` on the local lower-bound side. -/
  l30SharpCentral : YounisOddPaperSharpIntervalCount l30c l30p l30ε
  /-- **The eventual explicit binomial lower bound.** -/
  l30Binomial : EventuallyGlobalOddBinomialCount l30B l30p
    (paperT l30p) (paperError l30ε)
  /-- The Cantor/H.5 cost and correctness data. -/
  l30Cantor : CantorCostInputs
  /-- The actual H.3 failure data. -/
  l30Failure : FailureData

  -- L27
  /-- The parent ECM data. -/
  l27Data : L27_1Inputs
  /-- The quadratic `L`-value `L(1, χ_D)`. -/
  l27L1 : ℤ → ℝ
  /-- **Siegel's constant lower bound.** -/
  l27Siegel : SiegelLOneLower l27L1
  /-- The Hurwitz class number `H(-D)`. -/
  l27Hurwitz : ℤ → ℝ
  /-- **The Dirichlet class-number formula** and positivity data. -/
  l27ClassNumber : DirichletClassNumberInput l27Hurwitz l27L1
  /-- The nondegeneracy fraction. -/
  l27θ : ℝ
  /-- `θ > 0`. -/
  l27θ_pos : 0 < l27θ
  /-- The Hasse-scale constant is below the Siegel constant at scale `√θ`. -/
  l27KappaLe : l27Data.κ ≤
    (classNumberFormulaConstant * Classical.choose l27Siegel) * Real.sqrt l27θ
  /-- Smooth orders lie in the central trace window. -/
  l27CentralTrace : CentralTraceWindow l27Data.p l27Data.smooth l27θ
  /-- The target prime is prime. -/
  l27Prime : ∀ n, (l27Data.p n).Prime
  /-- **The Waterhouse weighted model count.** -/
  l27WeightedModel : ∀ n,
    WaterhouseWeightedModelCount (l27Data.p n) (l27Prime n) l27Hurwitz
  /-- The order count dominates the raw curve count. -/
  l27OrderDominates : ∀ n j,
    rawCurveOrderCount l27Data.p l27Prime n j ≤ l27Data.orderCount n j
  /-- The `j`-line fibre count. -/
  l27Fiber : JLineFiberInput l27Data.p l27Data.orderCount l27Data.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  l27PGeFour : ∀ n, 4 ≤ l27Data.p n
  /-- **The finite-sum kill law.** -/
  l27KillLaw : L27KillLawInputs l27Data
  /-- **Hasse's theorem.** -/
  l27Hasse : HasseBound l27Data.p l27Data.orderCount
  /-- **The paper's curve-count budget.** -/
  l27CurveBudget : CurveBudget l27Data.p l27Data.y l27Data.psi l27Data.curves
    l27Data.κ l27Data.η
  /-- The L27.2 `log₂` multiplier. -/
  l27LogFactor : LogFactorSubexp l27Data.cofactor

  -- L34: raw data
  /-- The possible exceptional real zero `β₀`. -/
  l34Beta0 : ℕ → ℝ
  /-- The real part of a generic zero of `ζ_E`. -/
  l34ZeroRealPart : ℕ → ℝ
  /-- The absolute degree `2d`, as a natural number. -/
  l34Degree : ℕ → ℕ
  /-- `log |Δ_E|`. -/
  l34DiscLog : ℕ → ℝ
  /-- The polynomial input parameter `T`. -/
  l34T : ℕ → ℝ
  /-- A cumulative Chebotarev count. -/
  l34Count : ℕ → ℝ
  /-- The cumulative inert count. -/
  l34InertCount : ℕ → ℝ
  /-- The degree-one inert count after discarding small / higher-degree ideals. -/
  l34DegreeOneInert : ℕ → ℝ
  /-- `Li x`. -/
  l34LiX : ℕ → ℝ
  /-- `Li x^{β₀}`. -/
  l34LiBeta0 : ℕ → ℝ
  /-- The per-trial detection probability. -/
  l34PTrial : ℕ → ℝ
  /-- The actual failure probability of the probe stage. -/
  l34ActualMiss : ℕ → ℝ
  /-- The number of nonrational classes. -/
  l34ClassCount : ℕ → ℝ
  /-- The number of probes `R`. -/
  l34R : ℕ → ℕ
  /-- The range constant. -/
  l34K : ℝ
  /-- The constant `C` in the effective error. -/
  l34C : ℝ
  /-- The constant `c` in the effective error. -/
  l34cZ : ℝ
  /-- The zero-free-region constant `c_z`. -/
  l34cz : ℝ
  /-- The per-ideal selection constant. -/
  l34csel : ℝ
  /-- The polynomial constant in `h* ≤ Ch T³`. -/
  l34Ch : ℝ
  /-- The Dedekind zero-free region in its smallest form. -/
  l34ZeroFree : DedekindZeroFreeInput l34Beta0 l34ZeroRealPart l34cz l34DiscLog
  /-- The classical Stark exceptional-zero input, at the paper factorial factor
  `F = (2d)! = absoluteFactorialFactor l34Degree`. -/
  l34Stark : StarkExceptionalZeroInput l34Beta0
    (absoluteFactorialFactor l34Degree) l34DiscLog
  /-- The explicit `T^6` range input at the natural-number degree. -/
  l34Range : ChebotarevT6RangeInput l34K l34T
    (fun n => (l34Degree n : ℝ)) l34DiscLog
  /-- The polynomial parameter is at least one. -/
  l34T_ge_one : ∀ n, 1 ≤ l34T n
  /-- **The standard effective Chebotarev statement** at the cutoff
  `x = 2^{T⁶}`. -/
  l34Effective : EffectiveChebotarevStatement l34K l34C l34cZ (cutoff l34T)
    (fun n => (l34Degree n : ℝ)) l34DiscLog l34Count l34LiX l34LiBeta0
  /-- The inert count contains the counted nonidentity class. -/
  l34InertGeCount : ∀ n, l34Count n ≤ l34InertCount n
  /-- Stark's bound converted to the dyadic bracket, at `cbr = 1/16`. -/
  l34Bracket : LogIntegralBracket (1 / 16) (cutoff l34T)
    (absoluteFactorialFactor l34Degree) l34T l34LiX l34LiBeta0
  /-- **The uniform threshold for the pointwise factorial budgets.**  The raw
  parameter `T` dominates both explicit analytic thresholds at every index.
  The two budgets are derived from this growth condition. -/
  l34BudgetThreshold : ∀ n,
    max (errorLogBudgetThreshold l34C l34cZ (1 / 16))
        (degreeLossLogBudgetThreshold (1 / 16)) ≤ l34T n
  /-- The degree-one reduction. -/
  l34DegreeOneReduction : DegreeOneInertReduction l34InertCount l34DegreeOneInert
    (fun n => (l34Degree n : ℝ)) (cutoff l34T)
  /-- Probe selection at `1/(d x)` per eligible ideal. -/
  l34Selection : ProbeSelectionLowerBound l34csel (cutoff l34T)
    (fun n => (l34Degree n : ℝ)) l34DegreeOneInert l34PTrial
  /-- The paper's budget `R = F T¹⁰`, at `F = (2d)!`. -/
  l34ProbeBudget : ProbeBudget l34R (absoluteFactorialFactor l34Degree) l34T
  /-- There is at least one nonrational class. -/
  l34ClassCountPos : ∀ n, 0 < l34ClassCount n
  /-- The cubic class-count input. -/
  l34ClassCubic : ClassCountCubicInput l34Ch l34ClassCount l34T
  /-- The probe constant beats the class-count entropy constant. -/
  l34ConstantMargin : l34Ch * Real.log 2 < l34csel * (1 / 16) / 4
  /-- The probe exponent `T³` eventually dominates the ledger scale. -/
  l34ScaleCubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (l34csel * (1 / 16) / 4 - l34Ch * Real.log 2) * l34T n ^ 3
  /-- The actual failure probability is nonnegative. -/
  l34ActualMissNonneg : ∀ n, 0 ≤ l34ActualMiss n
  /-- The probe union bound. -/
  l34UnionBound : ProbeMissUnionBound l34ActualMiss l34PTrial l34ClassCount l34R
  /-- The per-trial probability is nonnegative. -/
  l34PTrialNonneg : ∀ n, 0 ≤ l34PTrial n
  /-- The per-trial probability is at most one. -/
  l34PTrialLeOne : ∀ n, l34PTrial n ≤ 1

  -- L18.4 and L19
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate, with the L19.6 thin slot built from lattice
  data. -/
  l19 : Wave15L19Inputs

  -- L20.2 and L20.4
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source.{0}

  -- P1 and C1–C4
  /-- P1: the explicit `exp (o(H))`-cost prepass. -/
  p1 : SubexpPrepassInput
  /-- C1: the public congruence check. -/
  c1 : C1Inputs Egood
  /-- C2: conditional hidden-sign uniformity. -/
  c2 : C2Inputs Egood
  /-- C3: the ideal/actual total-variation budget. -/
  c3 : C3Inputs Egood
  /-- C4: the expected public-work budget. -/
  c4 : C4Inputs Egood D

namespace PaperResidualInputsFinal

variable {D : ℝ}

/-! ## The L21.2 leaf -/

/-- **The L21.2 leaf produced by the final residual.**  This is exactly
`wave17InputsOfResidual R.l21`, so all numerical, structural and two-scale
fields are the theorems of `RandomizedL21_2ConcreteLeaf`. -/
noncomputable def toL21_2 (R : PaperResidualInputsFinal D) : Wave17L21_2Inputs :=
  wave17InputsOfResidual R.l21

/-- The final leaf keeps the elementary profile. -/
theorem toL21_2_profile (R : PaperResidualInputsFinal D) :
    R.toL21_2.profile = elementaryProfile :=
  wave17InputsOfResidual_profile R.l21

/-- The final leaf keeps the elementary stage-one constant. -/
theorem toL21_2_c (R : PaperResidualInputsFinal D) :
    R.toL21_2.c = elementaryC := by
  simpa only [toL21_2] using wave17InputsOfResidual_c R.l21

/-- The final leaf keeps the elementary Perron exponent. -/
theorem toL21_2_Cper (R : PaperResidualInputsFinal D) :
    R.toL21_2.Cper = elementaryCper := by
  simpa only [toL21_2] using wave17InputsOfResidual_Cper R.l21

/-- The final leaf keeps the centre sequence `p = X`. -/
theorem toL21_2_p (R : PaperResidualInputsFinal D) :
    R.toL21_2.p = elementaryX := by
  simpa only [toL21_2] using wave17InputsOfResidual_p R.l21

/-- The stored vertical-tail constant of the final leaf. -/
theorem toL21_2_Ktail (R : PaperResidualInputsFinal D) :
    R.toL21_2.Ktail = tailK / Real.pi := by
  simpa only [toL21_2] using wave17InputsOfResidual_Ktail R.l21

/-! ## The raw L34 record and the derived bundle -/

/-- **The raw L34 record assembled from the final record.**

This is the bridge that lets us reuse, without re-assuming anything, the
Wave-18L34 adapter `PaperResidualInputsL34.toL34`.  The L21.2 fields are the
same ones produced by `wave17InputsOfResidual R.l21`; all L30, L27 and raw L34
fields come verbatim from the final record. -/
noncomputable def toL34Record (R : PaperResidualInputsFinal D) :
    PaperResidualInputsL34 D :=
  let W := R.toL21_2
  { line := R.line
    zetaRH := W.hRH
    l21Profile := W.profile
    l21c := W.c
    l21Cper := W.Cper
    l21Ktail := W.Ktail
    l21p := W.p
    l21X_gt_one := W.X_gt_one
    l21c_pos := W.c_pos
    l21c_le_one := W.c_le_one
    l21U_ge_three := W.U_ge_three
    l21Cper_ge_three := W.Cper_ge_three
    l21Ktail_nonneg := W.Ktail_nonneg
    l21ZeroFree := R.l21.zeta.zeroFree
    l21ClassicalLine := classicalLogDerivLineBoundOn_of_zetaSide R.l21.zeta
    l21VerticalTail := W.verticalTail
    l21p_gt_one := W.p_gt_one
    l21CentralCount := W.localCount
    l21b_le_B := W.b_le_B
    l21a_ge_log_two := W.a_ge_log_two
    l21FourierLow := W.fourierLow
    l21FourierMiddle := W.fourierMiddle
    l21FourierTail := W.fourierTail
    l21U_dominates := W.U_dominates
    l21U_le_exp := W.U_le_exp
    l30p := R.l30p
    l30Growth := R.l30Growth
    l30ε := R.l30ε
    l30ε_pos := R.l30ε_pos
    l30A := R.l30A
    l30B := R.l30B
    l30B_pos := R.l30B_pos
    l30B_le_eighth := R.l30B_le_eighth
    l30AB_ge_four := R.l30AB_ge_four
    l30c := R.l30c
    l30C := R.l30C
    l30A_pos := R.l30A_pos
    l30A_ge_32 := R.l30A_ge_32
    l30AC_le := R.l30AC_le
    l30C_pos := R.l30C_pos
    l30SharpUpper := R.l30SharpUpper
    l30SharpCentral := R.l30SharpCentral
    l30Binomial := R.l30Binomial
    l30Cantor := R.l30Cantor
    l30Failure := R.l30Failure
    l27Data := R.l27Data
    l27L1 := R.l27L1
    l27Siegel := R.l27Siegel
    l27Hurwitz := R.l27Hurwitz
    l27ClassNumber := R.l27ClassNumber
    l27θ := R.l27θ
    l27θ_pos := R.l27θ_pos
    l27KappaLe := R.l27KappaLe
    l27CentralTrace := R.l27CentralTrace
    l27Prime := R.l27Prime
    l27WeightedModel := R.l27WeightedModel
    l27OrderDominates := R.l27OrderDominates
    l27Fiber := R.l27Fiber
    l27PGeFour := R.l27PGeFour
    l27KillLaw := R.l27KillLaw
    l27Hasse := R.l27Hasse
    l27CurveBudget := R.l27CurveBudget
    l27LogFactor := R.l27LogFactor
    l34Beta0 := R.l34Beta0
    l34ZeroRealPart := R.l34ZeroRealPart
    l34Degree := R.l34Degree
    l34DiscLog := R.l34DiscLog
    l34T := R.l34T
    l34Count := R.l34Count
    l34InertCount := R.l34InertCount
    l34DegreeOneInert := R.l34DegreeOneInert
    l34LiX := R.l34LiX
    l34LiBeta0 := R.l34LiBeta0
    l34PTrial := R.l34PTrial
    l34ActualMiss := R.l34ActualMiss
    l34ClassCount := R.l34ClassCount
    l34R := R.l34R
    l34K := R.l34K
    l34C := R.l34C
    l34cZ := R.l34cZ
    l34cz := R.l34cz
    l34csel := R.l34csel
    l34Ch := R.l34Ch
    l34ZeroFree := R.l34ZeroFree
    l34Stark := R.l34Stark
    l34Range := R.l34Range
    l34T_ge_one := R.l34T_ge_one
    l34Effective := R.l34Effective
    l34InertGeCount := R.l34InertGeCount
    l34Bracket := R.l34Bracket
    l34BudgetThreshold := R.l34BudgetThreshold
    l34DegreeOneReduction := R.l34DegreeOneReduction
    l34Selection := R.l34Selection
    l34ProbeBudget := R.l34ProbeBudget
    l34ClassCountPos := R.l34ClassCountPos
    l34ClassCubic := R.l34ClassCubic
    l34ConstantMargin := R.l34ConstantMargin
    l34ScaleCubic := R.l34ScaleCubic
    l34ActualMissNonneg := R.l34ActualMissNonneg
    l34UnionBound := R.l34UnionBound
    l34PTrialNonneg := R.l34PTrialNonneg
    l34PTrialLeOne := R.l34PTrialLeOne
    l18_4 := R.l18_4
    l19 := R.l19
    l20_2 := R.l20_2
    l20_4 := R.l20_4
    p1 := R.p1
    c1 := R.c1
    c2 := R.c2
    c3 := R.c3
    c4 := R.c4 }

/-- **The L34 effective-Chebotarev bundle, with both factorial budgets
derived.**  This is literally the Wave-18L34 adapter applied to
`R.toL34Record`; hence `F = (2d)!`, `cbr = 1/16`, and `error_log`,
`degree_log` are the theorems of `RandomizedL34FactorialBudgets`, not
hypotheses. -/
noncomputable def toL34 (R : PaperResidualInputsFinal D) :
    L34EffectiveChebotarevInputs :=
  Cogentic.RandomizedPaperEndpointWave18L34.PaperResidualInputsL34.toL34
    R.toL34Record

/-- The derived bundle has the raw degree. -/
theorem toL34_degree (R : PaperResidualInputsFinal D) :
    R.toL34.degree = fun n => (R.l34Degree n : ℝ) := rfl

/-- The derived bundle has the raw polynomial parameter `T`. -/
theorem toL34_T (R : PaperResidualInputsFinal D) :
    R.toL34.T = R.l34T := rfl

/-- The derived bundle has the paper factorial factor `F = (2d)!`. -/
theorem toL34_F (R : PaperResidualInputsFinal D) :
    R.toL34.F = absoluteFactorialFactor R.l34Degree := rfl

/-- The derived bundle has the Stark bracket constant `cbr = 1/16`. -/
theorem toL34_cbr (R : PaperResidualInputsFinal D) :
    R.toL34.cbr = 1 / 16 := rfl

/-- **The error factorial budget, derived** by
`chebotarevErrorLogBudget_of_threshold` through the Wave-18L34 adapter. -/
theorem toL34_error_log (R : PaperResidualInputsFinal D) :
    ChebotarevErrorLogBudget R.toL34.C R.toL34.cZ R.toL34.cbr R.toL34.F
      R.toL34.T R.toL34.degree :=
  R.toL34.error_log

/-- **The discarded-ideal factorial budget, derived** by
`degreeLossLogBudget_of_threshold` through the Wave-18L34 adapter. -/
theorem toL34_degree_log (R : PaperResidualInputsFinal D) :
    DegreeLossLogBudget R.toL34.cbr R.toL34.degree R.toL34.F R.toL34.T :=
  R.toL34.degree_log

/-! ## Reduction to the Wave-21 record -/

/-- **`PaperResidualInputsFinal → PaperResidualInputsL21`.**

The L21.2 field is passed through unchanged, the L34 field is `R.toL34`, and
every other field is copied verbatim. -/
noncomputable def toL21 (R : PaperResidualInputsFinal D) :
    PaperResidualInputsL21 D :=
  { line := R.line
    l21 := R.l21
    l30p := R.l30p
    l30Growth := R.l30Growth
    l30ε := R.l30ε
    l30ε_pos := R.l30ε_pos
    l30A := R.l30A
    l30B := R.l30B
    l30B_pos := R.l30B_pos
    l30B_le_eighth := R.l30B_le_eighth
    l30AB_ge_four := R.l30AB_ge_four
    l30c := R.l30c
    l30C := R.l30C
    l30A_pos := R.l30A_pos
    l30A_ge_32 := R.l30A_ge_32
    l30AC_le := R.l30AC_le
    l30C_pos := R.l30C_pos
    l30SharpUpper := R.l30SharpUpper
    l30SharpCentral := R.l30SharpCentral
    l30Binomial := R.l30Binomial
    l30Cantor := R.l30Cantor
    l30Failure := R.l30Failure
    l27Data := R.l27Data
    l27L1 := R.l27L1
    l27Siegel := R.l27Siegel
    l27Hurwitz := R.l27Hurwitz
    l27ClassNumber := R.l27ClassNumber
    l27θ := R.l27θ
    l27θ_pos := R.l27θ_pos
    l27KappaLe := R.l27KappaLe
    l27CentralTrace := R.l27CentralTrace
    l27Prime := R.l27Prime
    l27WeightedModel := R.l27WeightedModel
    l27OrderDominates := R.l27OrderDominates
    l27Fiber := R.l27Fiber
    l27PGeFour := R.l27PGeFour
    l27KillLaw := R.l27KillLaw
    l27Hasse := R.l27Hasse
    l27CurveBudget := R.l27CurveBudget
    l27LogFactor := R.l27LogFactor
    l34 := R.toL34
    l18_4 := R.l18_4
    l19 := R.l19
    l20_2 := R.l20_2
    l20_4 := R.l20_4
    p1 := R.p1
    c1 := R.c1
    c2 := R.c2
    c3 := R.c3
    c4 := R.c4 }

/-- The Wave-21 record keeps the Dirichlet-GRH field. -/
theorem toL21_line (R : PaperResidualInputsFinal D) :
    R.toL21.line = R.line := rfl

/-- The Wave-21 record keeps the two-component L21.2 residual. -/
theorem toL21_l21 (R : PaperResidualInputsFinal D) :
    R.toL21.l21 = R.l21 := rfl

/-- The Wave-21 record's L34 field is the derived bundle. -/
theorem toL21_l34 (R : PaperResidualInputsFinal D) :
    R.toL21.l34 = R.toL34 := rfl

/-- **Every non-L21 field is transported verbatim** into the Wave-21 record.
This records that L30, L27, the raw-to-derived L34 bundle, L18.4, L19, L20,
P1 and C1–C4 are unchanged. -/
theorem toL21_data (R : PaperResidualInputsFinal D) :
    R.toL21.line = R.line ∧
      R.toL21.l21 = R.l21 ∧
      R.toL21.l30p = R.l30p ∧
      R.toL21.l30Growth = R.l30Growth ∧
      R.toL21.l30ε = R.l30ε ∧
      R.toL21.l30A = R.l30A ∧
      R.toL21.l30B = R.l30B ∧
      R.toL21.l30c = R.l30c ∧
      R.toL21.l30C = R.l30C ∧
      R.toL21.l27Data = R.l27Data ∧
      R.toL21.l27L1 = R.l27L1 ∧
      R.toL21.l27θ = R.l27θ ∧
      R.toL21.l34 = R.toL34 ∧
      R.toL21.l18_4 = R.l18_4 ∧
      R.toL21.l19 = R.l19 ∧
      R.toL21.l20_2 = R.l20_2 ∧
      R.toL21.l20_4 = R.l20_4 ∧
      R.toL21.p1 = R.p1 ∧
      R.toL21.c1 = R.c1 ∧
      R.toL21.c2 = R.c2 ∧
      R.toL21.c3 = R.c3 ∧
      R.toL21.c4 = R.c4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The Wave-21 leaf inherited from the final record agrees with the direct
`wave17InputsOfResidual R.l21` on all loss/structural data. -/
theorem toL21_toL21_2_data (R : PaperResidualInputsFinal D) :
    R.toL21.toL21_2.profile = R.toL21_2.profile ∧
      R.toL21.toL21_2.c = R.toL21_2.c ∧
      R.toL21.toL21_2.Cper = R.toL21_2.Cper ∧
      R.toL21.toL21_2.Ktail = R.toL21_2.Ktail ∧
      R.toL21.toL21_2.p = R.toL21_2.p :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Reduction to the Wave-18 record -/

/-- **`PaperResidualInputsFinal → PaperResidualInputs`.**

This composes the Wave-21 transport with the final-to-Wave-21 reduction.  The
L21.2 fields come from `wave17InputsOfResidual R.l21` (with the classical line
field derived from the zeta side), and the L34 field is the derived bundle. -/
noncomputable def toPaperResidualInputs (R : PaperResidualInputsFinal D) :
    PaperResidualInputs D :=
  R.toL21.toPaperResidualInputs

/-- The transported Wave-18 record keeps the Dirichlet-GRH field. -/
theorem toPaperResidualInputs_line (R : PaperResidualInputsFinal D) :
    R.toPaperResidualInputs.line = R.line := rfl

/-- The transported Wave-18 record keeps the L34 bundle derived by
`R.toL34`. -/
theorem toPaperResidualInputs_l34 (R : PaperResidualInputsFinal D) :
    R.toPaperResidualInputs.l34 = R.toL34 := rfl

/-- The transported Wave-18 record keeps the concrete profile. -/
theorem toPaperResidualInputs_l21Profile (R : PaperResidualInputsFinal D) :
    R.toPaperResidualInputs.l21Profile = elementaryProfile := rfl

/-- The transported Wave-18 record keeps the stage-one constant. -/
theorem toPaperResidualInputs_l21c (R : PaperResidualInputsFinal D) :
    R.toPaperResidualInputs.l21c = elementaryC :=
  PaperResidualInputsL21.toPaperResidualInputs_l21c R.toL21

/-- The transported Wave-18 record keeps the Perron exponent. -/
theorem toPaperResidualInputs_l21Cper (R : PaperResidualInputsFinal D) :
    R.toPaperResidualInputs.l21Cper = elementaryCper :=
  PaperResidualInputsL21.toPaperResidualInputs_l21Cper R.toL21

/-- The transported Wave-18 record's central count is the literal count. -/
theorem toPaperResidualInputs_l21CentralCount (R : PaperResidualInputsFinal D) :
    R.toPaperResidualInputs.l21CentralCount = R.l21.localCount := rfl

/-- **The transported Wave-18 record is inhabited from the final residual.** -/
theorem nonempty_paperResidualInputs (R : PaperResidualInputsFinal D) :
    Nonempty (PaperResidualInputs D) :=
  ⟨R.toPaperResidualInputs⟩

/-- The Wave-17 inputs are inhabited through the final transport. -/
theorem nonempty_wave17Inputs (R : PaperResidualInputsFinal D) :
    Nonempty (Wave17Inputs Egood D) :=
  PaperResidualInputs.nonempty_wave17Inputs R.toPaperResidualInputs

end PaperResidualInputsFinal

/-! ## Field names and field counts -/

/-- The 73 field names of `PaperResidualInputs`, in declaration order. -/
def paperFieldNames : List String :=
  ["line", "zetaRH",
   "l21Profile", "l21c", "l21Cper", "l21Ktail", "l21p",
   "l21X_gt_one", "l21c_pos", "l21c_le_one", "l21U_ge_three",
   "l21Cper_ge_three", "l21Ktail_nonneg", "l21ZeroFree",
   "l21ClassicalLine", "l21VerticalTail", "l21p_gt_one",
   "l21CentralCount", "l21b_le_B", "l21a_ge_log_two",
   "l21FourierLow", "l21FourierMiddle", "l21FourierTail",
   "l21U_dominates", "l21U_le_exp",
   "l30p", "l30Growth", "l30ε", "l30ε_pos", "l30A", "l30B",
   "l30B_pos", "l30B_le_eighth", "l30AB_ge_four", "l30c", "l30C",
   "l30A_pos", "l30A_ge_32", "l30AC_le", "l30C_pos", "l30SharpUpper",
   "l30SharpCentral", "l30Binomial", "l30Cantor", "l30Failure",
   "l27Data", "l27L1", "l27Siegel", "l27Hurwitz", "l27ClassNumber",
   "l27θ", "l27θ_pos", "l27KappaLe", "l27CentralTrace", "l27Prime",
   "l27WeightedModel", "l27OrderDominates", "l27Fiber", "l27PGeFour",
   "l27KillLaw", "l27Hasse", "l27CurveBudget", "l27LogFactor",
   "l34", "l18_4", "l19", "l20_2", "l20_4",
   "p1", "c1", "c2", "c3", "c4"]

/-- The 50 field names of `PaperResidualInputsL21`. -/
def l21FieldNames : List String :=
  ["line", "l21",
   "l30p", "l30Growth", "l30ε", "l30ε_pos", "l30A", "l30B",
   "l30B_pos", "l30B_le_eighth", "l30AB_ge_four", "l30c", "l30C",
   "l30A_pos", "l30A_ge_32", "l30AC_le", "l30C_pos", "l30SharpUpper",
   "l30SharpCentral", "l30Binomial", "l30Cantor", "l30Failure",
   "l27Data", "l27L1", "l27Siegel", "l27Hurwitz", "l27ClassNumber",
   "l27θ", "l27θ_pos", "l27KappaLe", "l27CentralTrace", "l27Prime",
   "l27WeightedModel", "l27OrderDominates", "l27Fiber", "l27PGeFour",
   "l27KillLaw", "l27Hasse", "l27CurveBudget", "l27LogFactor",
   "l34", "l18_4", "l19", "l20_2", "l20_4",
   "p1", "c1", "c2", "c3", "c4"]

/-- The 39 raw L34 field names of `PaperResidualInputsL34` and of the final
record, in declaration order. -/
def l34RawFieldNames : List String :=
  ["l34Beta0", "l34ZeroRealPart", "l34Degree", "l34DiscLog", "l34T",
   "l34Count", "l34InertCount", "l34DegreeOneInert", "l34LiX",
   "l34LiBeta0", "l34PTrial", "l34ActualMiss", "l34ClassCount", "l34R",
   "l34K", "l34C", "l34cZ", "l34cz", "l34csel", "l34Ch",
   "l34ZeroFree", "l34Stark", "l34Range", "l34T_ge_one", "l34Effective",
   "l34InertGeCount", "l34Bracket", "l34BudgetThreshold",
   "l34DegreeOneReduction", "l34Selection", "l34ProbeBudget",
   "l34ClassCountPos", "l34ClassCubic", "l34ConstantMargin",
   "l34ScaleCubic", "l34ActualMissNonneg", "l34UnionBound",
   "l34PTrialNonneg", "l34PTrialLeOne"]

/-- The 20 L30 field names. -/
def l30FieldNames : List String :=
  ["l30p", "l30Growth", "l30ε", "l30ε_pos", "l30A", "l30B",
   "l30B_pos", "l30B_le_eighth", "l30AB_ge_four", "l30c", "l30C",
   "l30A_pos", "l30A_ge_32", "l30AC_le", "l30C_pos", "l30SharpUpper",
   "l30SharpCentral", "l30Binomial", "l30Cantor", "l30Failure"]

/-- The 18 L27 field names. -/
def l27FieldNames : List String :=
  ["l27Data", "l27L1", "l27Siegel", "l27Hurwitz", "l27ClassNumber",
   "l27θ", "l27θ_pos", "l27KappaLe", "l27CentralTrace", "l27Prime",
   "l27WeightedModel", "l27OrderDominates", "l27Fiber", "l27PGeFour",
   "l27KillLaw", "l27Hasse", "l27CurveBudget", "l27LogFactor"]

/-- The 9 tail field names (`l18_4` … `c4`). -/
def tailFieldNames : List String :=
  ["l18_4", "l19", "l20_2", "l20_4", "p1", "c1", "c2", "c3", "c4"]

/-- The 111 field names of `PaperResidualInputsL34`: line, `zetaRH`, the 23
L21.2 fields, L30, L27, the 39 raw L34 fields, and the 9 tail fields. -/
def l34FieldNames : List String :=
  ["line", "zetaRH"] ++
    ["l21Profile", "l21c", "l21Cper", "l21Ktail", "l21p",
     "l21X_gt_one", "l21c_pos", "l21c_le_one", "l21U_ge_three",
     "l21Cper_ge_three", "l21Ktail_nonneg", "l21ZeroFree",
     "l21ClassicalLine", "l21VerticalTail", "l21p_gt_one",
     "l21CentralCount", "l21b_le_B", "l21a_ge_log_two",
     "l21FourierLow", "l21FourierMiddle", "l21FourierTail",
     "l21U_dominates", "l21U_le_exp"] ++
    l30FieldNames ++ l27FieldNames ++ l34RawFieldNames ++ tailFieldNames

/-- The 88 field names of `PaperResidualInputsFinal`: `line`, `l21`, L30, L27,
the 39 raw L34 fields, and the 9 tail fields. -/
def finalFieldNames : List String :=
  ["line", "l21"] ++ l30FieldNames ++ l27FieldNames ++
    l34RawFieldNames ++ tailFieldNames

/-- The 24 L21.2-specific fields that the final record no longer assumes:
`zetaRH` and the 23 `l21*` fields.  They are replaced by the single field
`l21 : ConcreteLeafResidual`. -/
def l21StructuralFieldNames : List String :=
  ["zetaRH", "l21Profile", "l21c", "l21Cper", "l21Ktail", "l21p",
   "l21X_gt_one", "l21c_pos", "l21c_le_one", "l21U_ge_three",
   "l21Cper_ge_three", "l21Ktail_nonneg", "l21ZeroFree",
   "l21ClassicalLine", "l21VerticalTail", "l21p_gt_one",
   "l21CentralCount", "l21b_le_B", "l21a_ge_log_two",
   "l21FourierLow", "l21FourierMiddle", "l21FourierTail",
   "l21U_dominates", "l21U_le_exp"]

/-- The two L34 factorial budgets that are derived rather than assumed. -/
def l34BudgetFieldNames : List String := ["error_log", "degree_log"]

/-- **The exact residual field list of `PaperResidualInputsFinal`, grouped.**
The L21.2 block contributes only `line` and `l21`; the L34 block contributes the
39 raw parameters; every other block is unchanged. -/
def residualAnalyticFields : List String :=
  ["line", "l21"] ++ l30FieldNames ++ l27FieldNames ++
    l34RawFieldNames ++ tailFieldNames

theorem paperFieldNames_length : paperFieldNames.length = 73 := rfl

theorem l21FieldNames_length : l21FieldNames.length = 50 := rfl

theorem l34FieldNames_length : l34FieldNames.length = 111 := rfl

theorem finalFieldNames_length : finalFieldNames.length = 88 := rfl

theorem l21StructuralFieldNames_length : l21StructuralFieldNames.length = 24 := rfl

theorem l34BudgetFieldNames_length : l34BudgetFieldNames.length = 2 := rfl

theorem l34RawFieldNames_length : l34RawFieldNames.length = 39 := rfl

theorem residualAnalyticFields_eq_final : residualAnalyticFields = finalFieldNames := rfl

theorem residualAnalyticFields_length : residualAnalyticFields.length = 88 := rfl

/-- **The Wave-21 collapse, counted**: the 73 fields of `PaperResidualInputs`
lose the 24 structural L21.2 fields and gain the single `l21` field. -/
theorem l21_field_count_comparison :
    l21FieldNames.length = paperFieldNames.length - 24 + 1 := by
  rw [paperFieldNames_length, l21FieldNames_length]

/-- **The L34 expansion, counted**: the single L34 bundle of
`PaperResidualInputsL21` is replaced by 39 raw fields. -/
theorem final_field_count_comparison :
    finalFieldNames.length = l21FieldNames.length - 1 + 39 := by
  rw [l21FieldNames_length, finalFieldNames_length]

/-- **The combined field-count identity**:
`88 = 73 - 24 + 1 - 1 + 39`. -/
theorem final_vs_paper_field_count :
    finalFieldNames.length = paperFieldNames.length - 24 + 1 - 1 + 39 := by
  rw [paperFieldNames_length, finalFieldNames_length]

/-- The raw L34 record itself has `111 = 73 - 1 + 39` fields. -/
theorem l34_vs_paper_field_count :
    l34FieldNames.length = paperFieldNames.length - 1 + 39 := by
  rw [paperFieldNames_length, l34FieldNames_length]

/-- The final record is the L34 record with its 24 L21.2 fields collapsed to
the single `l21` field: `88 = 111 - 24 + 1`. -/
theorem final_vs_l34_field_count :
    finalFieldNames.length = l34FieldNames.length - 24 + 1 := by
  rw [l34FieldNames_length, finalFieldNames_length]

/-- None of the 24 structural L21.2 fields is a field of the final record. -/
theorem l21Structural_not_in_final :
    l21StructuralFieldNames.all
      (fun s => decide (s ∉ finalFieldNames)) = true := by
  decide

/-- Neither of the two L34 factorial budgets is a field of the final record. -/
theorem l34Budget_not_in_final :
    l34BudgetFieldNames.all
      (fun s => decide (s ∉ finalFieldNames)) = true := by
  decide

/-- The final field list is exactly the residual analytic list. -/
theorem finalFieldNames_eq_residual :
    finalFieldNames = residualAnalyticFields := rfl

/-! ## The endpoint -/

/-- **Wave-22 paper endpoint.**  Given, for every balanced-schedule ceiling `D`,
the final residual inputs — the L21.2 block collapsed to `ConcreteLeafResidual`
and the L34 bundle replaced by raw Chebotarev parameters with both factorial
budgets derived — there is one universal serialized factoring algorithm such
that, on the standard one-point epoch family,

* the kernel-checked driver always outputs a permutation of
  `n.primeFactorsList`;
* the expected serialized bit cost is eventually at most
  `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
  `balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof reduces each final record to `PaperResidualInputsL21` via
`PaperResidualInputsFinal.toL21` and invokes the Wave-21 endpoint. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave22Inputs
    (R : ∀ D : ℝ, PaperResidualInputsFinal D) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (Cogentic.RandomizedPaperEndpointWave21.EgoodSchedule s))
            (fun s => epochAttempt (Cogentic.RandomizedPaperEndpointWave21.EgoodSchedule s))) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (Cogentic.RandomizedPaperEndpointWave21.EgoodSchedule s))
            (fun s => epochAttempt (Cogentic.RandomizedPaperEndpointWave21.EgoodSchedule s))) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) :=
  Cogentic.RandomizedPaperEndpointWave21.serialized_assembled_balancedEnvelopeInfimum_from_wave21Inputs
    (fun D => (R D).toL21)

/-! ## Axiom audit -/

#print axioms PaperResidualInputsFinal.toL21_2
#print axioms PaperResidualInputsFinal.toL34Record
#print axioms PaperResidualInputsFinal.toL34
#print axioms PaperResidualInputsFinal.toL34_degree
#print axioms PaperResidualInputsFinal.toL34_T
#print axioms PaperResidualInputsFinal.toL34_F
#print axioms PaperResidualInputsFinal.toL34_cbr
#print axioms PaperResidualInputsFinal.toL34_error_log
#print axioms PaperResidualInputsFinal.toL34_degree_log
#print axioms PaperResidualInputsFinal.toL21
#print axioms PaperResidualInputsFinal.toPaperResidualInputs
#print axioms PaperResidualInputsFinal.toL21_data
#print axioms PaperResidualInputsFinal.toL21_toL21_2_data
#print axioms PaperResidualInputsFinal.nonempty_paperResidualInputs
#print axioms PaperResidualInputsFinal.nonempty_wave17Inputs
#print axioms finalFieldNames_length
#print axioms l21Structural_not_in_final
#print axioms l34Budget_not_in_final
#print axioms residualAnalyticFields_length
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave22Inputs

end Cogentic.RandomizedPaperEndpointWave22
