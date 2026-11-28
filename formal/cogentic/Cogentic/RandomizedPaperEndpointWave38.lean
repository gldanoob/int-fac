import Cogentic.RandomizedPaperEndpointWave36
import Cogentic.RandomizedL34RangeArithmetic

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 38: the L34 block with the `T⁶` range input derived from raw arithmetic

The Wave-36 L34 block `Wave36L34Inputs` still carried

```
range : ChebotarevT6RangeInput K T degree discLog
```

as an assumption.  `Cogentic.RandomizedL34RangeArithmetic` shows that this
packaged input is *not* an independent analytic assumption: it follows from the
paper's raw parameter arithmetic

* `0 < K ≤ 1` (the paper's `K = O(1)`),
* `1 ≤ C` (the exponent in `T = exp (C (log |Δ_E|)²)`),
* `0 < degree n` (genuine positivity of the absolute degree),
* `degree n ≤ discLog n` (the paper's `2d ≤ log |Δ_E|`),
* `Real.exp 1 ≤ discLog n` (the size condition `1 ≤ log log |Δ_E|`), and
* `T n = paperRangeT C discLog n` (the paper's parameter choice),

together with the Wave-36 fields `degree_one_reduction`, `selection`,
`constant_margin` and `scale_cubic`, which are exactly the remaining fields of
`L34RawRangeInput`.  The theorem
`L34RawRangeInput.toChebotarevT6RangeInput` assembles the packaged range input
from precisely these data.

This file removes `range` from the L34 block and replaces it by the **single**
bundled field

```
rangeArithmetic : L34RangeExponentArithmetic K C T degree discLog
```

which stores exactly the seven genuinely independent arithmetic propositions
above.  In particular `discLog_pos` is a *theorem*, not a field: it follows from
`Real.exp 1 ≤ discLog n`.  Every other field of the Wave-36 block is kept
verbatim, so the zero-free content is still the factorization-derived strip
packet and the L34 loss is still exactly the actual probe miss.

## What is proved

* `L34RangeExponentArithmetic.toChebotarevT6RangeInput` — the raw arithmetic
  gives `ChebotarevT6RangeInput K T degree discLog` (through the raw-record
  route `L34RawRangeInput.toChebotarevT6RangeInput`).
* `Wave38L34Inputs.toRange` — the **derived** `range` field of the block.
* `Wave38L34Inputs.toWave36L34Inputs` — transport to the Wave-36 block, filling
  `range` with `toRange`.
* `PaperResidualFor38.toPaperResidualFor36` and
  `PaperResidualFor38.toFullyDischargedInputs` — the record transports.
* `serialized_assembled_balancedEnvelopeInfimum_from_wave38Inputs` — the paper
  endpoint, proved from the Wave-36 endpoint.

## Residual accounting

`range` is derived, so it is **not** a field and not a residual.  The residual
list of Wave 38 is the Wave-36 list with `range` replaced by the single bundled
arithmetic entry `rangeArithmetic`.  See `wave38RemainingFieldNames`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss,
probability, count or error is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave38

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
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27StageOneFinish
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
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u v

/-! ## 1. The raw arithmetic that derives the range input -/

/-- **The genuinely independent arithmetic content of the `T⁶` range input.**

These are exactly the hypotheses of
`Cogentic.RandomizedL34RangeArithmetic.L34RawRangeInput` that are *not* already
fields of the Wave-36 L34 block.  The remaining `L34RawRangeInput` fields
(`l34DegreeOneReduction`, `l34Selection`, `l34ConstantMargin`,
`l34ScaleCubic`) are supplied by the Wave-36 fields `degree_one_reduction`,
`selection`, `constant_margin` and `scale_cubic`.

`discLog_pos` is deliberately absent: it follows from
`Real.exp 1 ≤ discLog n`.  The note in `RandomizedL34RangeArithmetic` explains
why `degree_pos` cannot be recovered from the degree-one reduction or the
selection inequality (Lean's `x / 0 = 0` makes both vacuous at `degree n = 0`),
so it is kept as the smallest explicit positivity input. -/
structure L34RangeExponentArithmetic (K C : ℝ) (T degree discLog : ℕ → ℝ) : Prop where
  /-- The range constant is positive. -/
  K_pos : 0 < K
  /-- The paper's range constant is at most one. -/
  K_le_one : K ≤ 1
  /-- The exponent constant in `T = exp (C (log |Δ_E|)²)` is at least one. -/
  C_ge_one : 1 ≤ C
  /-- **Genuinely independent positivity of the absolute degree.** -/
  degree_pos : ∀ n, 0 < degree n
  /-- **The degree / discriminant relation** `d ≤ log |Δ_E|`. -/
  degree_le_discLog : ∀ n, degree n ≤ discLog n
  /-- **The size condition** `log |Δ_E| ≥ e`, i.e. `1 ≤ log log |Δ_E|`. -/
  discLog_ge_exp_one : ∀ n, Real.exp 1 ≤ discLog n
  /-- **The paper's parameter choice** `T = exp (C (log |Δ_E|)²)`. -/
  T_eq : ∀ n, T n = paperRangeT C discLog n

namespace L34RangeExponentArithmetic

variable {K C : ℝ} {T degree discLog : ℕ → ℝ}
variable (A : L34RangeExponentArithmetic K C T degree discLog)
include A

/-- `log |Δ_E|` is positive, from `exp 1 ≤ log |Δ_E|`. -/
theorem discLog_pos (n : ℕ) : 0 < discLog n :=
  lt_of_lt_of_le (Real.exp_pos 1) (A.discLog_ge_exp_one n)

/-- `1 ≤ log log |Δ_E|`, from the size condition `exp 1 ≤ log |Δ_E|`. -/
theorem log_discLog_ge_one (n : ℕ) : 1 ≤ Real.log (discLog n) :=
  (Real.le_log_iff_exp_le (A.discLog_pos n)).mpr (A.discLog_ge_exp_one n)

/-- The raw `T` is literally the paper's exponential choice. -/
theorem T_eq_paperRangeT : T = paperRangeT C discLog :=
  funext A.T_eq

/-- **The packaged `T⁶` range input from the raw arithmetic.**  This is exactly
the conclusion of `L34RawRangeInput.toChebotarevT6RangeInput`, obtained here
from the seven raw atoms directly. -/
theorem toChebotarevT6RangeInput :
    ChebotarevT6RangeInput K T degree discLog := by
  rw [A.T_eq_paperRangeT]
  exact paperRangeInput A.K_pos A.K_le_one A.C_ge_one A.degree_pos A.discLog_pos
    A.degree_le_discLog A.log_discLog_ge_one

end L34RangeExponentArithmetic

/-! ## 2. The Wave-38 L34 block: `range` removed, one arithmetic field added -/

/-- **The Wave-38 L34 block.**  It is `Wave36L34Inputs` with the packaged field

```
range : ChebotarevT6RangeInput K T degree discLog
```

removed and replaced by the single raw arithmetic field `rangeArithmetic`.
Every other data and analytic field is copied verbatim, so the zero-free content
is still the factorization-derived strip packet and the loss is still exactly the
actual probe miss.  The range input itself is derived as `toRange`. -/
structure Wave38L34Inputs (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) where
  /-- The possible exceptional real zero `β₀`. -/
  beta0 : ℕ → ℝ
  /-- The absolute degree `2d` of `E = K(√γ)`. -/
  degree : ℕ → ℝ
  /-- `log |Δ_E|`. -/
  discLog : ℕ → ℝ
  /-- The factorial factor `F = (2d)!`. -/
  F : ℕ → ℝ
  /-- The polynomial input parameter `T`. -/
  T : ℕ → ℝ
  /-- A cumulative Chebotarev count. -/
  count : ℕ → ℝ
  /-- The cumulative inert count. -/
  inertCount : ℕ → ℝ
  /-- The degree-one inert count after discarding small / higher-degree ideals. -/
  degreeOneInert : ℕ → ℝ
  /-- `Li x`. -/
  liX : ℕ → ℝ
  /-- `Li x^{β₀}`. -/
  liBeta0 : ℕ → ℝ
  /-- The per-trial detection probability. -/
  pTrial : ℕ → ℝ
  /-- The actual failure probability of the probe stage. -/
  actualMiss : ℕ → ℝ
  /-- The number of nonrational classes. -/
  classCount : ℕ → ℝ
  /-- The number of probes `R`. -/
  R : ℕ → ℕ
  /-- The zero-free-region constant `c_z`. -/
  cz : ℝ
  /-- The zero-free-region constant is positive. -/
  cz_pos : 0 < cz
  /-- **The explicit abelian factorization**: away from the pole, `ζ_K` is the
  product of the Dirichlet `L`-functions of `χ`. -/
  factorization : DedekindZetaFactorsIntoDirichletOffPole K ι N χ
  /-- **The half-line arithmetic**: `1/2 ≤ β₀`.  Together with `beta0_le_half`
  this puts the exceptional zero on the critical line. -/
  half_le_beta0 : ∀ n, 1 / 2 ≤ beta0 n
  /-- The range constant. -/
  K : ℝ
  /-- The constant `C` in the effective error (also the exponent constant of
  `T = exp (C (log |Δ_E|)²)`). -/
  C : ℝ
  /-- The constant `c` in the effective error. -/
  cZ : ℝ
  /-- The bracket constant. -/
  cbr : ℝ
  /-- The per-ideal selection constant. -/
  csel : ℝ
  /-- The polynomial constant in `h* ≤ Ch T³`. -/
  Ch : ℝ
  /-- **The raw arithmetic deriving the `T⁶` range input.**  This replaces the
  former packaged `range` field; `toRange` derives the packaged input. -/
  rangeArithmetic : L34RangeExponentArithmetic K C T degree discLog
  /-- The polynomial parameter is at least one. -/
  T_ge_one : ∀ n, 1 ≤ T n
  /-- The canonical Chebotarev error slack. -/
  cheb : ChebotarevResidualInput C cZ (cutoff T) degree count liX liBeta0
  /-- The inert count contains the counted nonidentity class. -/
  inert_ge_count : ∀ n, count n ≤ inertCount n
  /-- Stark's bound converted to the dyadic bracket. -/
  bracket : LogIntegralBracket cbr (cutoff T) F T liX liBeta0
  /-- The Chebotarev error is negligible against the bracket, in scalar form. -/
  error_scalar : ChebotarevErrorScalarBound C cZ cbr F T degree
  /-- Discarding small / higher-degree ideals is negligible, in scalar form. -/
  degree_loss_scalar : DegreeLossScalarBound cbr degree F T
  /-- The degree-one reduction. -/
  degree_one_reduction : DegreeOneInertReduction inertCount degreeOneInert degree (cutoff T)
  /-- Probe selection at `1/(d x)` per eligible ideal. -/
  selection : ProbeSelectionLowerBound csel (cutoff T) degree degreeOneInert pTrial
  /-- The paper's budget `R = F T¹⁰`. -/
  budget : ProbeBudget R F T
  /-- There is at least one nonrational class. -/
  classCount_pos : ∀ n, 0 < classCount n
  /-- The cubic class-count input. -/
  classCubic : ClassCountCubicInput Ch classCount T
  /-- The probe constant beats the class-count entropy constant. -/
  constant_margin : Ch * Real.log 2 < csel * cbr / 4
  /-- The probe exponent `T³` eventually dominates the ledger scale. -/
  scale_cubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (csel * cbr / 4 - Ch * Real.log 2) * T n ^ 3
  /-- The actual failure probability is nonnegative. -/
  actualMiss_nonneg : ∀ n, 0 ≤ actualMiss n
  /-- The probe union bound. -/
  union_bound : ProbeMissUnionBound actualMiss pTrial classCount R
  /-- The per-trial probability is nonnegative. -/
  pTrial_nonneg : ∀ n, 0 ≤ pTrial n
  /-- The per-trial probability is at most one. -/
  pTrial_le_one : ∀ n, pTrial n ≤ 1
  /-- The factorial factor is positive. -/
  starkF_pos : ∀ n, 0 < F n
  /-- **The exact GRH residual**: the exceptional zero is at most the critical
  line. -/
  beta0_le_half : ∀ n, beta0 n ≤ 1 / 2
  /-- **The paper's arithmetic side condition** `1/2 ≤ paperBeta0 F discLog`. -/
  paperBeta0_ge_half : ∀ n, 1 / 2 ≤ paperBeta0 F discLog n

namespace Wave38L34Inputs

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}

/-- **The raw range record of the Wave-38 block.**  Its data fields are the
Wave-38 fields; its carried hypotheses are the Wave-38 `degree_one_reduction`,
`selection`, `constant_margin` and `scale_cubic`; its genuinely independent
arithmetic is `rangeArithmetic`. -/
noncomputable def toRawRange (S : Wave38L34Inputs K ι N χ) : L34RawRangeInput where
  l34K := S.K
  l34C := S.C
  l34csel := S.csel
  l34cbr := S.cbr
  l34Ch := S.Ch
  l34T := S.T
  l34Degree := S.degree
  l34DiscLog := S.discLog
  l34InertCount := S.inertCount
  l34DegreeOneInert := S.degreeOneInert
  l34PTrial := S.pTrial
  l34X := cutoff S.T
  l34K_pos := S.rangeArithmetic.K_pos
  l34K_le_one := S.rangeArithmetic.K_le_one
  l34C_ge_one := S.rangeArithmetic.C_ge_one
  l34Degree_pos := S.rangeArithmetic.degree_pos
  l34DiscLog_pos := S.rangeArithmetic.discLog_pos
  l34Degree_le_discLog := S.rangeArithmetic.degree_le_discLog
  l34DiscLog_ge_exp_one := S.rangeArithmetic.discLog_ge_exp_one
  l34T_eq := S.rangeArithmetic.T_eq
  l34DegreeOneReduction := S.degree_one_reduction
  l34Selection := S.selection
  l34ConstantMargin := S.constant_margin
  l34ScaleCubic := S.scale_cubic

/-- **The `T⁶` range input is derived**, not assumed.  This is the packaged
`ChebotarevT6RangeInput` obtained from the raw arithmetic through
`L34RawRangeInput.toChebotarevT6RangeInput`. -/
theorem toRange (S : Wave38L34Inputs K ι N χ) :
    ChebotarevT6RangeInput S.K S.T S.degree S.discLog :=
  S.toRawRange.toChebotarevT6RangeInput

/-- **`degree_pos`, derived.** -/
theorem degree_pos (S : Wave38L34Inputs K ι N χ) (n : ℕ) : 0 < S.degree n :=
  S.toRange.degree_pos n

/-- **`discLog_pos`, derived.** -/
theorem discLog_pos (S : Wave38L34Inputs K ι N χ) (n : ℕ) : 0 < S.discLog n :=
  S.toRange.discLog_pos n

/-- **`degree_le_T`, derived.** -/
theorem degree_le_T (S : Wave38L34Inputs K ι N χ) (n : ℕ) :
    S.degree n ≤ S.T n :=
  S.toRange.degree_le_T n

/-- **`discLog_le_T`, derived.** -/
theorem discLog_le_T (S : Wave38L34Inputs K ι N χ) (n : ℕ) :
    S.discLog n ≤ S.T n :=
  S.toRange.discLog_le_T n

/-- **The pointwise `T⁶` range budget**, derived. -/
theorem rangeT6 (S : Wave38L34Inputs K ι N χ) (n : ℕ) :
    S.K * S.degree n * (S.discLog n) ^ 2 ≤
      Real.log 2 * (S.T n) ^ 6 :=
  S.toRange.toChebotarevRangeT6 n

/-- **Transport to the Wave-36 L34 block**, filling the former `range` field
with the derived `toRange`.  Every other field is copied verbatim. -/
noncomputable def toWave36L34Inputs (S : Wave38L34Inputs K ι N χ) :
    Wave36L34Inputs K ι N χ where
  beta0 := S.beta0
  degree := S.degree
  discLog := S.discLog
  F := S.F
  T := S.T
  count := S.count
  inertCount := S.inertCount
  degreeOneInert := S.degreeOneInert
  liX := S.liX
  liBeta0 := S.liBeta0
  pTrial := S.pTrial
  actualMiss := S.actualMiss
  classCount := S.classCount
  R := S.R
  cz := S.cz
  cz_pos := S.cz_pos
  factorization := S.factorization
  half_le_beta0 := S.half_le_beta0
  K := S.K
  C := S.C
  cZ := S.cZ
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  range := S.toRange
  T_ge_one := S.T_ge_one
  cheb := S.cheb
  inert_ge_count := S.inert_ge_count
  bracket := S.bracket
  error_scalar := S.error_scalar
  degree_loss_scalar := S.degree_loss_scalar
  degree_one_reduction := S.degree_one_reduction
  selection := S.selection
  budget := S.budget
  classCount_pos := S.classCount_pos
  classCubic := S.classCubic
  constant_margin := S.constant_margin
  scale_cubic := S.scale_cubic
  actualMiss_nonneg := S.actualMiss_nonneg
  union_bound := S.union_bound
  pTrial_nonneg := S.pTrial_nonneg
  pTrial_le_one := S.pTrial_le_one
  starkF_pos := S.starkF_pos
  beta0_le_half := S.beta0_le_half
  paperBeta0_ge_half := S.paperBeta0_ge_half

/-- The Wave-36 transport preserves the actual probe miss. -/
theorem toWave36L34Inputs_actualMiss (S : Wave38L34Inputs K ι N χ) :
    S.toWave36L34Inputs.actualMiss = S.actualMiss := rfl

/-- **The all-zeros strip packet**, derived exactly as in Wave 36. -/
theorem toZeroStrip (line : DirichletLZerosOnLine)
    (S : Wave38L34Inputs K ι N χ) :
    DedekindZetaStripInput K S.beta0 S.cz S.discLog :=
  S.toWave36L34Inputs.toZeroStrip line

/-- The literal `RatedLeaf` of the Wave-38 block, through the Wave-36
transport. -/
noncomputable def ratedLeaf (line : DirichletLZerosOnLine)
    (S : Wave38L34Inputs K ι N χ) :
    Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  S.toWave36L34Inputs.ratedLeaf line

/-- **The Wave-38 L34 loss is exactly the actual probe miss.** -/
theorem ratedLeaf_loss_eq (line : DirichletLZerosOnLine)
    (S : Wave38L34Inputs K ι N χ) (n : ℕ) :
    (S.ratedLeaf line).loss n = S.actualMiss n := by
  simpa only [ratedLeaf, toWave36L34Inputs_actualMiss] using
    S.toWave36L34Inputs.ratedLeaf_loss_eq line n

/-- The loss is nonnegative. -/
theorem ratedLeaf_loss_nonneg (line : DirichletLZerosOnLine)
    (S : Wave38L34Inputs K ι N χ) (n : ℕ) :
    0 ≤ (S.ratedLeaf line).loss n :=
  (S.ratedLeaf line).loss_nonneg n

/-- **A genuine nonzero loss.** -/
theorem ratedLeaf_loss_pos (line : DirichletLZerosOnLine)
    (S : Wave38L34Inputs K ι N χ) {n : ℕ} (h : 0 < S.actualMiss n) :
    0 < (S.ratedLeaf line).loss n := by
  have h' : 0 < S.toWave36L34Inputs.actualMiss n := by
    simpa only [toWave36L34Inputs_actualMiss] using h
  simpa only [ratedLeaf] using S.toWave36L34Inputs.ratedLeaf_loss_pos line h'

/-- The L34 ledger slot. -/
theorem ratedLeaf_slot (line : DirichletLZerosOnLine)
    (S : Wave38L34Inputs K ι N χ) :
    ∀ᶠ n : ℕ in atTop,
      (S.ratedLeaf line).loss n ≤ exp (-(2 : ℝ) * scale n) :=
  (S.ratedLeaf line).slot

/-- On the half-line, `β₀` is exactly the critical line. -/
theorem beta0_eq_half (S : Wave38L34Inputs K ι N χ) (n : ℕ) :
    S.beta0 n = 1 / 2 :=
  le_antisymm (S.beta0_le_half n) (S.half_le_beta0 n)

end Wave38L34Inputs

/-! ## 3. The Wave-38 ledger -/

/-- **The Wave-38 ledger.**  It is the fully discharged ledger at the
constructed L18.4 certificate and the Wave-38 L34 leaf. -/
noncomputable def wave38Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave38L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  fullyDischargedSlots (paperCertificate line) l19.toL19FullCertificate
    (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf l21.toL21_2LeafData)
    (wave15L27Leaf l27_data l27_finish) l30.toWave26L30Inputs.toSubexpLeaf
    (l34.ratedLeaf line) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
    (wave14P1Leaf p1)

/-- The Wave-38 ledger is the Wave-36 ledger at the transported block. -/
theorem wave38Slots_eq_wave36Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave38L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) :
    wave38Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave36Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave36L34Inputs p1 := rfl

/-- The Wave-38 ledger total, term by term. -/
theorem wave38Slots_total_eq {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave38L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave38Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
      (paperCertificate line).toInputs.loss n +
        l19.toL19FullCertificate.toL19Inputs.poisson.loss n +
        l19.toL19FullCertificate.toL19Inputs.zeroMode.loss n +
        l19.toL19FullCertificate.toL19Inputs.thin.loss n +
        (wave14L20_2Leaf l20_2).loss n + l20_4.toSubexpLeaf.loss n +
        (wave14L21_2Leaf l21.toL21_2LeafData).loss n +
        (wave15L27Leaf l27_data l27_finish).loss n +
        l30.toWave26L30Inputs.toSubexpLeaf.loss n + (l34.ratedLeaf line).loss n +
        (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget).loss n +
        (wave14P1Leaf p1).loss n := by
  simpa only [wave38Slots] using
    fullyDischargedSlots_total_eq (paperCertificate line) l19.toL19FullCertificate
      (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
      (wave14L21_2Leaf l21.toL21_2LeafData)
      (wave15L27Leaf l27_data l27_finish) l30.toWave26L30Inputs.toSubexpLeaf
      (l34.ratedLeaf line) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
      (wave14P1Leaf p1) n

/-- **The Wave-38 and Wave-36 ledger totals agree.**  The only difference
between the two blocks is the range field, which is derived in Wave 38. -/
theorem wave38Slots_total_eq_wave36Slots_total
    {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave38L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave38Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
      (wave36Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave36L34Inputs p1).total n := by
  rw [wave38Slots_eq_wave36Slots]

/-- **The L34 loss of the Wave-38 ledger is exactly the actual probe miss.** -/
theorem wave38Slots_l34_loss_eq {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l34 : Wave38L34Inputs K ι N χ) (n : ℕ) :
    (l34.ratedLeaf line).loss n = l34.actualMiss n :=
  l34.ratedLeaf_loss_eq line n

/-! ## 4. The combined residual record -/

/-- **The Wave-38 combined residual record.**

It is the Wave-36 record with the L34 block replaced by `Wave38L34Inputs`, whose
packaged `range` field is derived from the raw arithmetic.  All other fields are
copied from the Wave-36 record, and the ledger is `wave38Slots` at the new L34
leaf. -/
structure PaperResidualFor38 (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L19 certificate, with the L19.6 thin slot built from lattice
  data. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- **The L21.2 analytic input**: the Riemann hypothesis and the literal
  central short-interval smooth count. -/
  l21 : Wave27L21Inputs
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- **L30 with the sharp count derived** from the Buchstab estimate and the
  parity fraction. -/
  l30 : Wave31L30Inputs
  /-- **L34 with the `T⁶` range input derived** from the raw arithmetic. -/
  l34 : Wave38L34Inputs K ι N χ
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
  /-- **The C5 data assembled by `c5FullOfCount`.** -/
  c5Data : Wave15C5Data concrete
  /-- Adapter: the concrete C5 loss is dominated by the Wave-38 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave38Slots line l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor38

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor38 → FullyDischargedInputs` directly.**  The L34 leaf is
the Wave-38 leaf; the ledger is `wave38Slots`, definitionally the fully
discharged ledger at that leaf. -/
noncomputable def toFullyDischargedInputs
    (I : PaperResidualFor38 line K ι N χ E D) : FullyDischargedInputs E D where
  l18_4 := paperCertificate line
  l19 := I.l19.toL19FullCertificate
  l20_2 := wave14L20_2Leaf I.l20_2
  l20_4 := I.l20_4.toSubexpLeaf
  l21_2 := wave14L21_2Leaf I.l21.toL21_2LeafData
  l27_1 := wave15L27Leaf I.l27_data I.l27_finish
  l30 := I.l30.toWave26L30Inputs.toSubexpLeaf
  l34 := I.l34.ratedLeaf line
  l4_l25_l36 := wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget
  p1 := wave14P1Leaf I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5 := I.c5Data.toC5
  loss_le := by
    intro n hN
    simpa only [wave38Slots] using I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs
    (I : PaperResidualFor38 line K ι N χ E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- **`PaperResidualFor38 → PaperResidualFor36`**, filling the removed `range`
field with the derived `toRange`.  No extra witness is needed: the range input
is arithmetic, not analytic. -/
noncomputable def toPaperResidualFor36
    (I : PaperResidualFor38 line K ι N χ E D) :
    PaperResidualFor36 line K ι N χ E D where
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34.toWave36L34Inputs
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
    rw [← wave38Slots_total_eq_wave36Slots_total line I.l19 I.l20_2 I.l20_4
      I.l21 I.l27_data I.l27_finish I.l30 I.l34 I.p1 n]
    exact I.loss_le n hN

/-- The L34 loss of the Wave-38 record is exactly the actual probe miss. -/
theorem l34_loss_eq (I : PaperResidualFor38 line K ι N χ E D) (n : ℕ) :
    (I.l34.ratedLeaf line).loss n = I.l34.actualMiss n :=
  I.l34.ratedLeaf_loss_eq line n

/-- **The `T⁶` range input of the Wave-38 record is derived**, not a field. -/
theorem range_derived (I : PaperResidualFor38 line K ι N χ E D) :
    ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog :=
  I.l34.toRange

/-- **The zero-free datum of the Wave-38 record is the strip packet**, derived
from the critical line and the factorization. -/
theorem zeroStrip_derived (I : PaperResidualFor38 line K ι N χ E D) :
    DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog :=
  I.l34.toZeroStrip line

/-- The Stark field is derived, not stored. -/
theorem stark_derived (I : PaperResidualFor38 line K ι N χ E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  I.l34.toWave36L34Inputs.toStark

end PaperResidualFor38

/-- **The schedule-indexed form of the Wave-38 record.** -/
abbrev PaperResidualFor38Schedule (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor38 line K ι N χ (E s) D

/-! ## 5. The endpoint -/

/-- **Wave-38 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K`, every explicit abelian factorization `ζ_K = ∏ L(·, χ)` away from the pole,
and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor38 line K ι N χ (E s) D` record, the kernel-checked
driver outputs a permutation of `n.primeFactorsList` and has expected serialized
bit cost eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`.

The L34 block carries **no packaged range input**: `range` is derived from the
raw arithmetic.  The endpoint is proved from the Wave-36 endpoint through the
`range`-filling transport `PaperResidualFor38.toPaperResidualFor36`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave38Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
      (χ : ∀ i, DirichletCharacter ℂ (N i)),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor38 line K ι N χ (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave36Inputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF ι instF instDec N instN χ E hI
  exact hmain K ι N χ E fun s D hvalid => (hI s D hvalid).toPaperResidualFor36

/-! ## 6. Residual accounting -/

/-- The field names of `Wave38L34Inputs`.  The packaged `range` field is gone;
the raw arithmetic appears as the single bundled entry `rangeArithmetic`. -/
def wave38L34FieldNames : List String :=
  ["beta0", "degree", "discLog", "F", "T", "count",
   "inertCount", "degreeOneInert", "liX", "liBeta0", "pTrial", "actualMiss",
   "classCount", "R", "cz", "cz_pos", "factorization", "half_le_beta0",
   "K", "C", "cZ", "cbr", "csel", "Ch", "rangeArithmetic", "T_ge_one",
   "cheb", "inert_ge_count", "bracket", "error_scalar", "degree_loss_scalar",
   "degree_one_reduction", "selection", "budget", "classCount_pos", "classCubic",
   "constant_margin", "scale_cubic", "actualMiss_nonneg", "union_bound",
   "pTrial_nonneg", "pTrial_le_one", "starkF_pos", "beta0_le_half",
   "paperBeta0_ge_half"]

theorem wave38L34FieldNames_length : wave38L34FieldNames.length = 45 := rfl

/-- **`range` is not a field any more.** -/
theorem wave38_no_range_field :
    wave38L34FieldNames.all (fun s => decide (s ≠ "range")) = true := by
  decide

/-- The single raw arithmetic entry is present instead. -/
theorem wave38_rangeArithmetic_field :
    wave38L34FieldNames.contains "rangeArithmetic" = true := by
  decide

/-- The field list is the Wave-36 list with `range` renamed to
`rangeArithmetic`. -/
theorem wave38L34FieldNames_eq_wave36_replace :
    wave38L34FieldNames =
      wave36L34FieldNames.map
        (fun s => if s = "range" then "rangeArithmetic" else s) := by
  decide

/-- The field names of `PaperResidualFor38`. -/
def wave38FieldNames : List String :=
  ["l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave38FieldNames_length : wave38FieldNames.length = 17 := rfl

/-- **The exact Wave-38 residual list.**  It is the Wave-36 list with the
packaged `range` entry replaced by the single raw arithmetic bundle
`rangeArithmetic`.  In particular `range` no longer appears. -/
def wave38RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "factorization", "cheb", "rangeArithmetic", "half_le_beta0", "beta0_le_half",
   "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

/-- The residual list literally is the displayed list. -/
theorem wave38RemainingFieldNames_exact :
    wave38RemainingFieldNames =
      ["zetaRH", "localCount", "hbuchstab", "hparity",
       "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
       "killMass", "curveBudget",
       "factorization", "cheb", "rangeArithmetic", "half_le_beta0", "beta0_le_half",
       "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"] :=
  rfl

theorem wave38RemainingFieldNames_length :
    wave38RemainingFieldNames.length = 24 := rfl

/-- **The Wave-38 residual list is the Wave-36 list with `range` replaced by
`rangeArithmetic`.** -/
theorem wave38RemainingFieldNames_eq_wave36_replace :
    wave38RemainingFieldNames =
      wave36RemainingFieldNames.map
        (fun s => if s = "range" then "rangeArithmetic" else s) := by
  decide

/-- **No packaged `range` entry survives in the residual list.** -/
theorem wave38_no_range_residual :
    wave38RemainingFieldNames.all (fun s => decide (s ≠ "range")) = true := by
  decide

/-- The raw arithmetic bundle is the replacement residual entry. -/
theorem wave38_rangeArithmetic_residual :
    wave38RemainingFieldNames.contains "rangeArithmetic" = true := by
  decide

/-- The residual list contains the Buchstab/parity, factorization, half-line and
remaining certificate entries. -/
theorem wave38_residual_blocks :
    wave38RemainingFieldNames.contains "hbuchstab" = true ∧
      wave38RemainingFieldNames.contains "hparity" = true ∧
      wave38RemainingFieldNames.contains "factorization" = true ∧
      wave38RemainingFieldNames.contains "half_le_beta0" = true ∧
      wave38RemainingFieldNames.contains "cheb" = true ∧
      wave38RemainingFieldNames.contains "rangeArithmetic" = true ∧
      wave38RemainingFieldNames.contains "beta0_le_half" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The complete remaining L34 analytic input is the factorization and the
half-line arithmetic**, with the strip packet derived and the range input
derived. -/
theorem wave38_l34_remaining (I : PaperResidualFor38 line K ι N χ E D) :
    DedekindZetaFactorsIntoDirichletOffPole K ι N χ ∧
      (∀ n, 1 / 2 ≤ I.l34.beta0 n) ∧
      DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog ∧
      0 < I.l34.cz ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog ∧
      (∀ n, I.l34.beta0 n ≤ 1 / 2) :=
  ⟨I.l34.factorization, I.l34.half_le_beta0, I.zeroStrip_derived, I.l34.cz_pos,
    I.l34.cheb, I.range_derived, I.l34.beta0_le_half⟩

/-! ## Axiom audit -/

#print axioms L34RangeExponentArithmetic.discLog_pos
#print axioms L34RangeExponentArithmetic.log_discLog_ge_one
#print axioms L34RangeExponentArithmetic.T_eq_paperRangeT
#print axioms L34RangeExponentArithmetic.toChebotarevT6RangeInput
#print axioms Wave38L34Inputs.toRawRange
#print axioms Wave38L34Inputs.toRange
#print axioms Wave38L34Inputs.degree_pos
#print axioms Wave38L34Inputs.discLog_pos
#print axioms Wave38L34Inputs.degree_le_T
#print axioms Wave38L34Inputs.discLog_le_T
#print axioms Wave38L34Inputs.rangeT6
#print axioms Wave38L34Inputs.toZeroStrip
#print axioms Wave38L34Inputs.toWave36L34Inputs
#print axioms Wave38L34Inputs.ratedLeaf_loss_eq
#print axioms Wave38L34Inputs.ratedLeaf_loss_pos
#print axioms wave38Slots
#print axioms wave38Slots_total_eq
#print axioms wave38Slots_total_eq_wave36Slots_total
#print axioms wave38Slots_l34_loss_eq
#print axioms PaperResidualFor38.toFullyDischargedInputs
#print axioms PaperResidualFor38.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor38.toPaperResidualFor36
#print axioms PaperResidualFor38.l34_loss_eq
#print axioms PaperResidualFor38.range_derived
#print axioms PaperResidualFor38.zeroStrip_derived
#print axioms PaperResidualFor38.stark_derived
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave38Inputs
#print axioms wave38L34FieldNames_length
#print axioms wave38_no_range_field
#print axioms wave38_rangeArithmetic_field
#print axioms wave38L34FieldNames_eq_wave36_replace
#print axioms wave38RemainingFieldNames_exact
#print axioms wave38RemainingFieldNames_length
#print axioms wave38RemainingFieldNames_eq_wave36_replace
#print axioms wave38_no_range_residual
#print axioms wave38_rangeArithmetic_residual
#print axioms wave38_residual_blocks
#print axioms wave38_l34_remaining

end Cogentic.RandomizedPaperEndpointWave38
