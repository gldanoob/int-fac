import Cogentic.RandomizedPaperEndpointWave18
import Cogentic.RandomizedL34FactorialBudgets

/-!
# Wave 18, L34: the effective Chebotarev bundle from raw range data

`Cogentic.RandomizedPaperEndpointWave18.PaperResidualInputs` still contains the
bundled L34 field

```
l34 : L34EffectiveChebotarevInputs
```

whose two arithmetic fields `error_log` and `degree_log` are the logarithmic
factorial budgets.  `Cogentic.RandomizedL34FactorialBudgets` proves those
budgets from the paper's raw parameters:

* `F = (2d)! = absoluteFactorialFactor degree`,
* `cbr = 1/16` (the Stark bracket constant),
* the explicit `T⁶` range input `ChebotarevT6RangeInput`, and
* `T n → ∞`.

This file exposes that raw data as a structure `PaperResidualInputsL34`, a
variant of `PaperResidualInputs` in which the L34 bundle is *not* assumed but
*constructed*:

* the effective Chebotarev statement, the Dedekind zero-free region, Stark's
  exceptional-zero input and the `T⁶` range input are kept as named fields;
* `F`, `degree` (as a real function) and `cbr` are derived from the raw
  `degree : ℕ → ℕ` and the paper constant `cbr = 1/16`;
* the two logarithmic budgets are derived with
  `chebotarevErrorLogBudget_of_threshold` and
  `degreeLossLogBudget_of_threshold` (the threshold forms of
  `RandomizedL34FactorialBudgets`), and the eventual form is also derived from
  `exists_threshold_budgets_of_rangeInput`.

## The exact extra hypothesis

`exists_threshold_budgets_of_rangeInput` produces the two budgets only on a
tail (`∃ N, ∀ n ≥ N`), whereas `L34EffectiveChebotarevInputs.error_log` and
`degree_log` are pointwise (`∀ n`).  The range input gives `d ≤ T` but no lower
bound on `T` at a fixed index, so the pointwise budgets cannot be recovered
from `T → ∞` alone.  The precise missing hypothesis is the uniform lower bound

```
∀ n, max (errorLogBudgetThreshold C cZ (1/16))
        (degreeLossLogBudgetThreshold (1/16)) ≤ T n
```

recorded as `l34BudgetThreshold`.  It is a growth condition on the raw
parameter `T`, not one of the budgets: both budgets are *derived* from it by the
pointwise threshold lemmas.  The `T → ∞` hypothesis needed by
`exists_threshold_budgets_of_rangeInput` is *not* assumed separately: it is
derived as `l34T_tendsto` from the probe growth field `l34ScaleCubic` and
`scale_grows`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count or
error is set to zero.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace Cogentic.RandomizedPaperEndpointWave18L34

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
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2LineMinimal
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Sub
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
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34LogIntegral
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34Dedekind
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
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver

universe u

/-! ## The variant with raw L34 data -/

/-- **The Wave-18 residual inputs with the L34 bundle replaced by raw data.**

All non-L34 fields are copied verbatim from
`Cogentic.RandomizedPaperEndpointWave18.PaperResidualInputs`.  The bundled
field `l34 : L34EffectiveChebotarevInputs` is replaced by:

* the Dedekind zero-free region, Stark's exceptional-zero input and the explicit
  `T⁶` range input;
* the standard effective Chebotarev statement;
* the raw constants `K`, `C`, `cZ`, `cz`, `csel`, `Ch` and the raw integer
  degree function `l34Degree : ℕ → ℕ` and `T`, `discLog`;
* all the remaining counting/probe fields of the L34 bundle, stated for the
  derived `F = absoluteFactorialFactor l34Degree` and `cbr = 1/16`;
* the exact uniform threshold hypothesis under which the two factorial budgets
  are derived (`l34BudgetThreshold`).  The companion `T → ∞` hypothesis is not
  an extra field: it is derived from `l34ScaleCubic`. -/
structure PaperResidualInputsL34 (D : ℝ) where
  /-- **GRH for Dirichlet `L`-functions.** -/
  line : DirichletLZerosOnLine
  /-- GRH for the Riemann zeta function, the specialization consumed by the
  L21.2 Perron contour. -/
  zetaRH : RiemannZetaZerosOnLine

  -- L21.2
  /-- The Fourier/tent discrepancy profile. -/
  l21Profile : TentProfile
  /-- The stage-one constant. -/
  l21c : ℝ
  /-- The final Perron exponent. -/
  l21Cper : ℝ
  /-- The given vertical-tail constant. -/
  l21Ktail : ℝ
  /-- The centre sequence of the short-interval count. -/
  l21p : ℕ → ℝ
  /-- The profile is above one at every band. -/
  l21X_gt_one : ∀ n, 1 < l21Profile.X n
  /-- `c > 0`. -/
  l21c_pos : 0 < l21c
  /-- `c ≤ 1`. -/
  l21c_le_one : l21c ≤ 1
  /-- `log X ≥ 3`. -/
  l21U_ge_three : ∀ n, 3 ≤ bandLog l21Profile.X n
  /-- `Cper ≥ 3`. -/
  l21Cper_ge_three : 3 ≤ l21Cper
  /-- The tail constant is nonnegative. -/
  l21Ktail_nonneg : 0 ≤ l21Ktail
  /-- **The open zero-free line input**: `ζ` has no zero on
  `Re s = 2/3`, `|Im s| ≤ 2 X³`. -/
  l21ZeroFree : ZetaLineZeroFree l21Profile.X
  /-- **The classical `O (log²)` line bound** on the same height range. -/
  l21ClassicalLine : ClassicalLogDerivLineBoundOn l21Profile.X
  /-- The genuine vertical-tail estimate at the given constant. -/
  l21VerticalTail : VerticalTailBound l21Profile.X (fun _ => l21Ktail)
    (l21Cper - 1)
  /-- The centre is eventually larger than one. -/
  l21p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < l21p n
  /-- **The literal central short-interval smooth count.** -/
  l21CentralCount : ShortIntervalSmoothCountLower l21p l21c l21Profile.X
  /-- `b ≤ B` for the paper parameters. -/
  l21b_le_B : ∀ᶠ n : ℕ in atTop,
    bOf l21Profile.X l21c n ≤ logCutoff l21c l21Profile.X n
  /-- `e^a ≥ 2`. -/
  l21a_ge_log_two : ∀ᶠ n : ℕ in atTop,
    Real.log 2 ≤ aOf l21Profile.X l21c n
  /-- Low-frequency Fourier energy bound. -/
  l21FourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.lowEnergy n ≤
      Real.exp (-(((2 * l21c) / 3) - δ) * paperRate l21Profile.X n)
  /-- Middle-frequency Fourier energy bound. -/
  l21FourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.middleEnergy n ≤
      Real.exp (-((1 / l21c) - δ) * paperRate l21Profile.X n)
  /-- High-frequency Fourier energy bound. -/
  l21FourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.tailEnergy n ≤ Real.exp (-δ * paperRate l21Profile.X n)
  /-- Two-scale separation. -/
  l21U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog l21Profile.X n
  /-- `log X ≤ exp (scale n)`. -/
  l21U_le_exp : ∀ᶠ n : ℕ in atTop,
    bandLog l21Profile.X n ≤ Real.exp (scale n)

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
  factor is the true Dickman exponent `u log u`, not the unsound
  `exp (-(1+ε)t_p)`. -/
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
  /-- The absolute degree `2d`, as a natural number.  The real degree used by
  the L34 bundle is `fun n => (l34Degree n : ℝ)`. -/
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
  /-- **The exact extra hypothesis for the pointwise factorial budgets.**  The
  raw parameter `T` dominates both explicit analytic thresholds at every
  index.  This is a growth condition on `T`, not one of the budgets: the
  budgets are derived from it. -/
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

/-! ## Deriving the L34 bundle -/

namespace PaperResidualInputsL34

variable {D : ℝ}

/-- **The pointwise error factorial budget, derived.**  `T` dominating the
explicit threshold `errorLogBudgetThreshold C cZ (1/16)` at every index makes the
error budget hold at every index, with `F = (2d)!`. -/
theorem error_log (R : PaperResidualInputsL34 D) :
    ChebotarevErrorLogBudget R.l34C R.l34cZ (1 / 16)
      (absoluteFactorialFactor R.l34Degree) R.l34T
      (fun n => (R.l34Degree n : ℝ)) :=
  chebotarevErrorLogBudget_of_threshold
    (C := R.l34C) (cZ := R.l34cZ) (cbr := 1 / 16)
    R.l34Effective.C_pos R.l34Effective.cZ_pos (by norm_num)
    (fun n => by
      have h := R.l34Range.degree_pos n
      exact_mod_cast h)
    R.l34Range.degree_le_T
    (fun n => le_trans (le_max_left _ _) (R.l34BudgetThreshold n))

/-- **The pointwise discarded-ideal factorial budget, derived.** -/
theorem degree_log (R : PaperResidualInputsL34 D) :
    DegreeLossLogBudget (1 / 16) (fun n => (R.l34Degree n : ℝ))
      (absoluteFactorialFactor R.l34Degree) R.l34T :=
  degreeLossLogBudget_of_threshold
    (cbr := 1 / 16) (degree := R.l34Degree) (T := R.l34T)
    (by norm_num)
    (fun n => by
      have h := R.l34Range.degree_pos n
      exact_mod_cast h)
    R.l34Range.degree_le_T
    (fun n => le_trans (le_max_right _ _) (R.l34BudgetThreshold n))

/-- **`T → ∞`, derived.**  The probe growth field `l34ScaleCubic`, whose slope
is positive by `l34ConstantMargin`, together with `scale → ∞`, forces `T → ∞`.
Thus the `T → ∞` hypothesis of `exists_threshold_budgets_of_rangeInput` is not
an extra input. -/
theorem l34T_tendsto (R : PaperResidualInputsL34 D) :
    Tendsto R.l34T atTop atTop := by
  let c : ℝ := R.l34csel * (1 / 16) / 4 - R.l34Ch * Real.log 2
  have hc : 0 < c := sub_pos.mpr R.l34ConstantMargin
  have hscale : Tendsto (fun n : ℕ => 2 * scale n) atTop atTop :=
    scale_grows.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hcubic_mul : Tendsto (fun n : ℕ => c * R.l34T n ^ 3) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hscale.eventually_ge_atTop b, R.l34ScaleCubic] with n hb hT
    dsimp only [c]
    linarith
  have hcubic : Tendsto (fun n : ℕ => R.l34T n ^ 3) atTop atTop :=
    hcubic_mul.atTop_of_const_mul₀ hc
  rw [tendsto_atTop] at hcubic ⊢
  intro b
  filter_upwards [hcubic ((max b 0) ^ 3)] with n hn
  have hmax0 : 0 ≤ max b 0 := le_max_right b 0
  have hT0 : 0 ≤ R.l34T n := by
    by_contra hneg
    have hneg' : R.l34T n < 0 := not_le.mp hneg
    have hsq : 0 < R.l34T n ^ 2 := sq_pos_of_ne_zero (ne_of_lt hneg')
    have hneg3 : R.l34T n ^ 3 < 0 := by
      calc
        R.l34T n ^ 3 = R.l34T n * R.l34T n ^ 2 := by ring
        _ < 0 := mul_neg_of_neg_of_pos hneg' hsq
    have hmax3 : 0 ≤ (max b 0) ^ 3 := pow_nonneg hmax0 3
    linarith
  by_cases hb : 0 ≤ b
  · have hb3 : b ^ 3 ≤ R.l34T n ^ 3 := by
      calc
        b ^ 3 ≤ (max b 0) ^ 3 := pow_le_pow_left₀ hb (le_max_left b 0) 3
        _ ≤ R.l34T n ^ 3 := hn
    exact (pow_le_pow_iff_left₀ hb hT0 (by norm_num : (3 : ℕ) ≠ 0)).mp hb3
  · have hb' : b < 0 := not_le.mp hb
    linarith

/-- **The eventual form of the two budgets**, obtained directly from the raw
range input and the derived `T → ∞` via
`exists_threshold_budgets_of_rangeInput`.  This is the form supplied by the
factorial-budget file; the pointwise forms above use the stronger
`l34BudgetThreshold` because `L34EffectiveChebotarevInputs` asks for all
indices. -/
theorem exists_threshold_budgets (R : PaperResidualInputsL34 D) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Real.log (R.l34C * (absoluteFactorialFactor R.l34Degree n * R.l34T n ^ 6) /
          ((1 / 16) / 8)) ≤
        R.l34cZ * Real.sqrt ((R.l34T n) ^ 6 * Real.log 2 /
          (2 * (R.l34Degree n : ℝ)))) ∧
      (Real.log ((R.l34Degree n : ℝ) * absoluteFactorialFactor R.l34Degree n *
          R.l34T n ^ 6 / ((1 / 16) / 8)) ≤
        (R.l34T n) ^ 6 / 2 * Real.log 2) :=
  exists_threshold_budgets_of_rangeInput
    (K := R.l34K) (C := R.l34C) (cZ := R.l34cZ)
    R.l34Range R.l34Effective.C_pos R.l34Effective.cZ_pos R.l34T_tendsto

/-- **The L34 effective-Chebotarev bundle constructed from raw data.**  The
factorial factor is `F = (2d)!`, `cbr = 1/16`, and the two arithmetic budgets
are the derived theorems `error_log` and `degree_log`; every other field is
passed through from the raw data. -/
noncomputable def toL34 (R : PaperResidualInputsL34 D) : L34EffectiveChebotarevInputs where
  beta0 := R.l34Beta0
  zeroRealPart := R.l34ZeroRealPart
  degree := fun n => (R.l34Degree n : ℝ)
  discLog := R.l34DiscLog
  F := absoluteFactorialFactor R.l34Degree
  T := R.l34T
  count := R.l34Count
  inertCount := R.l34InertCount
  degreeOneInert := R.l34DegreeOneInert
  liX := R.l34LiX
  liBeta0 := R.l34LiBeta0
  pTrial := R.l34PTrial
  actualMiss := R.l34ActualMiss
  classCount := R.l34ClassCount
  R := R.l34R
  K := R.l34K
  C := R.l34C
  cZ := R.l34cZ
  cz := R.l34cz
  cbr := 1 / 16
  csel := R.l34csel
  Ch := R.l34Ch
  zeroFree := R.l34ZeroFree
  stark := R.l34Stark
  range := R.l34Range
  T_ge_one := R.l34T_ge_one
  effective := R.l34Effective
  inert_ge_count := R.l34InertGeCount
  bracket := R.l34Bracket
  error_log := R.error_log
  degree_log := R.degree_log
  degree_one_reduction := R.l34DegreeOneReduction
  selection := R.l34Selection
  budget := R.l34ProbeBudget
  classCount_pos := R.l34ClassCountPos
  classCubic := R.l34ClassCubic
  constant_margin := R.l34ConstantMargin
  scale_cubic := R.l34ScaleCubic
  actualMiss_nonneg := R.l34ActualMissNonneg
  union_bound := R.l34UnionBound
  pTrial_nonneg := R.l34PTrialNonneg
  pTrial_le_one := R.l34PTrialLeOne

/-- **The paper residual inputs with the constructed L34 bundle.**  All
non-L34 fields are transported verbatim; the L34 field is `R.toL34`. -/
noncomputable def toPaperResidualInputs (R : PaperResidualInputsL34 D) :
    PaperResidualInputs D where
  line := R.line
  zetaRH := R.zetaRH
  l21Profile := R.l21Profile
  l21c := R.l21c
  l21Cper := R.l21Cper
  l21Ktail := R.l21Ktail
  l21p := R.l21p
  l21X_gt_one := R.l21X_gt_one
  l21c_pos := R.l21c_pos
  l21c_le_one := R.l21c_le_one
  l21U_ge_three := R.l21U_ge_three
  l21Cper_ge_three := R.l21Cper_ge_three
  l21Ktail_nonneg := R.l21Ktail_nonneg
  l21ZeroFree := R.l21ZeroFree
  l21ClassicalLine := R.l21ClassicalLine
  l21VerticalTail := R.l21VerticalTail
  l21p_gt_one := R.l21p_gt_one
  l21CentralCount := R.l21CentralCount
  l21b_le_B := R.l21b_le_B
  l21a_ge_log_two := R.l21a_ge_log_two
  l21FourierLow := R.l21FourierLow
  l21FourierMiddle := R.l21FourierMiddle
  l21FourierTail := R.l21FourierTail
  l21U_dominates := R.l21U_dominates
  l21U_le_exp := R.l21U_le_exp
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
  c4 := R.c4

/-- The constructed L34 bundle has exactly the raw degree and `T`. -/
theorem toL34_data (R : PaperResidualInputsL34 D) :
    R.toL34.degree = (fun n => (R.l34Degree n : ℝ)) ∧
      R.toL34.T = R.l34T ∧
      R.toL34.F = absoluteFactorialFactor R.l34Degree ∧
      R.toL34.cbr = 1 / 16 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The non-L34 data is transported verbatim. -/
theorem toPaperResidualInputs_data (R : PaperResidualInputsL34 D) :
    R.toPaperResidualInputs.line = R.line ∧
      R.toPaperResidualInputs.l21Profile = R.l21Profile ∧
      R.toPaperResidualInputs.l30p = R.l30p ∧
      R.toPaperResidualInputs.l27Data = R.l27Data ∧
      R.toPaperResidualInputs.l34 = R.toL34 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end PaperResidualInputsL34

/-! ## The endpoint -/

/-- **Wave-18 paper endpoint from raw L34 inputs.**  Given, for every
balanced-schedule ceiling `D`, the residual inputs with the L34 bundle replaced
by raw Chebotarev/range data, there is one universal serialized factoring
algorithm with the same guarantees as the Wave-18 endpoint. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave18L34Inputs
    (R : ∀ D : ℝ, PaperResidualInputsL34 D) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (EgoodSchedule s))
            (fun s => epochAttempt (EgoodSchedule s))) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (EgoodSchedule s))
            (fun s => epochAttempt (EgoodSchedule s))) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) :=
  Cogentic.RandomizedPaperEndpointWave18.serialized_assembled_balancedEnvelopeInfimum_from_wave18Inputs
    (fun D => (R D).toPaperResidualInputs)

/-! ## Axiom audit -/

#print axioms PaperResidualInputsL34.error_log
#print axioms PaperResidualInputsL34.degree_log
#print axioms PaperResidualInputsL34.l34T_tendsto
#print axioms PaperResidualInputsL34.exists_threshold_budgets
#print axioms PaperResidualInputsL34.toL34
#print axioms PaperResidualInputsL34.toPaperResidualInputs
#print axioms PaperResidualInputsL34.toL34_data
#print axioms PaperResidualInputsL34.toPaperResidualInputs_data
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave18L34Inputs

end Cogentic.RandomizedPaperEndpointWave18L34
