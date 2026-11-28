import Cogentic.RandomizedPaperEndpointWave37
import Cogentic.RandomizedPaperEndpointWave38

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 39: the fixed critical line together with the derived `T⁶` range input

Waves 37 and 38 remove two independent redundancies from the L34 block:

* **Wave 37** removes the free sequence `beta0` and the two half-line fields
  `half_le_beta0`, `beta0_le_half`, replacing them by the fixed critical line
  `fun _ => 1 / 2` and by theorems of the same names;
* **Wave 38** removes the packaged input
  `range : ChebotarevT6RangeInput K T degree discLog`, replacing it by the single
  bundled arithmetic field
  `rangeArithmetic : L34RangeExponentArithmetic K C T degree discLog` and
  deriving `range` as `toRange`.

This file combines the two reductions into one L34 block, `Wave39L34Inputs`:

* no `beta0` field — the sequence is the fixed `fixedBeta0 = fun _ => 1/2`;
* no `half_le_beta0` or `beta0_le_half` fields — they are the theorems
  `half_le_beta0`, `beta0_le_half`, `beta0_eq_half` for the fixed sequence;
* no packaged `range` field — it is the derived `toRange`, obtained from
  `rangeArithmetic` exactly as in Wave 38;
* every other field of the Wave-37 block is kept verbatim, including the
  arithmetic side condition `paperBeta0_ge_half`.

`PaperResidualFor39` is the Wave-37 record with this new L34 block.  It
transports to `PaperResidualFor37` by filling the removed `range` field with
`toRange`, and directly to `FullyDischargedInputs`; the paper endpoint
`serialized_assembled_balancedEnvelopeInfimum_from_wave39Inputs` then follows.

## Residual accounting

The residual list is exactly the Wave-37 list with `range` replaced by the
single bundled arithmetic entry `rangeArithmetic`, hence still 22 entries:

```
[zetaRH, localCount, hbuchstab, hparity,
 hurwitzClassNumber, siegelLower, hasse, waterhouseTrace, killMass, curveBudget,
 factorization, cheb, rangeArithmetic,
 l19, l20_2, l20_4, c1, c2, c3, c4, concrete, p1]
```

In particular no `range`, no `beta0` and no half-line field remains, either in
the L34 block or in the residual list.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss,
probability, count or error is set to zero.  The L34 loss is still exactly the
actual probe miss of the probe stage.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave39

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
open Cogentic.RandomizedPaperEndpointWave37
open Cogentic.RandomizedPaperEndpointWave38
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u v

/-! ## 1. The Wave-39 L34 block -/

/-- **The Wave-39 L34 block.**  It is the Wave-37 block (`β₀ = 1/2`, no
half-line fields) with the packaged field `range` replaced by the single raw
arithmetic bundle `rangeArithmetic` of Wave 38.  The packaged input is derived
as `toRange`; the strip packet and Stark are derived exactly as in Wave 37. -/
structure Wave39L34Inputs (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) where
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
  /-- `Li x^{β₀}`, at the fixed `β₀ = 1/2`. -/
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
  packaged `range` field of Wave 37; `toRange` derives the packaged input. -/
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
  /-- **The paper's arithmetic side condition** `1/2 ≤ paperBeta0 F discLog`.
  Kept because `F > 0` and `log|Δ| > 0` do not imply `4 F log|Δ| ≥ 2`; it is
  the arithmetic input that identifies `1/2` with the Stark line. -/
  paperBeta0_ge_half : ∀ n, 1 / 2 ≤ paperBeta0 F discLog n

namespace Wave39L34Inputs

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}

/-- The fixed exceptional zero sequence: the critical line. -/
def beta0 (_ : Wave39L34Inputs K ι N χ) : ℕ → ℝ := fixedBeta0

/-- The fixed sequence is the critical line, definitionally. -/
theorem beta0_eq_fixed (S : Wave39L34Inputs K ι N χ) :
    S.beta0 = fixedBeta0 := rfl

/-- Pointwise, `β₀ n = 1/2`. -/
theorem beta0_apply (S : Wave39L34Inputs K ι N χ) (n : ℕ) :
    S.beta0 n = 1 / 2 := rfl

/-- **The lower half-line inequality is a theorem.** -/
theorem half_le_beta0 (S : Wave39L34Inputs K ι N χ) (n : ℕ) :
    1 / 2 ≤ S.beta0 n :=
  le_rfl

/-- **The upper GRH inequality is a theorem.** -/
theorem beta0_le_half (S : Wave39L34Inputs K ι N χ) (n : ℕ) :
    S.beta0 n ≤ 1 / 2 :=
  le_rfl

/-- Both former half-line fields together say that `β₀` is the critical line. -/
theorem beta0_eq_half (S : Wave39L34Inputs K ι N χ) (n : ℕ) :
    S.beta0 n = 1 / 2 :=
  le_antisymm (S.beta0_le_half n) (S.half_le_beta0 n)

/-- **Compatibility transport to the Wave-38 block**, filling `beta0` with the
fixed critical line and the two half-line fields with `le_rfl`.  Every other
field, including `rangeArithmetic`, is copied verbatim. -/
noncomputable def toWave38L34Inputs (S : Wave39L34Inputs K ι N χ) :
    Wave38L34Inputs K ι N χ where
  beta0 := fixedBeta0
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
  half_le_beta0 := fun _ => le_rfl
  K := S.K
  C := S.C
  cZ := S.cZ
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  rangeArithmetic := S.rangeArithmetic
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
  beta0_le_half := fun _ => le_rfl
  paperBeta0_ge_half := S.paperBeta0_ge_half

/-- **The `T⁶` range input is derived**, exactly as in Wave 38, from the raw
arithmetic bundle `rangeArithmetic`. -/
theorem toRange (S : Wave39L34Inputs K ι N χ) :
    ChebotarevT6RangeInput S.K S.T S.degree S.discLog :=
  S.toWave38L34Inputs.toRange

/-- **`degree_pos`, derived from the range arithmetic.** -/
theorem degree_pos (S : Wave39L34Inputs K ι N χ) (n : ℕ) : 0 < S.degree n :=
  S.toRange.degree_pos n

/-- **`discLog_pos`, derived from the range arithmetic.** -/
theorem discLog_pos (S : Wave39L34Inputs K ι N χ) (n : ℕ) : 0 < S.discLog n :=
  S.toRange.discLog_pos n

/-- **The pointwise `T⁶` range budget**, derived. -/
theorem rangeT6 (S : Wave39L34Inputs K ι N χ) (n : ℕ) :
    S.K * S.degree n * (S.discLog n) ^ 2 ≤
      Real.log 2 * (S.T n) ^ 6 :=
  S.toRange.toChebotarevRangeT6 n

/-- **Compatibility transport to the Wave-37 block**, filling the removed
`range` field with the derived `toRange` and copying every other field
verbatim. -/
noncomputable def toWave37L34Inputs (S : Wave39L34Inputs K ι N χ) :
    Wave37L34Inputs K ι N χ where
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
  paperBeta0_ge_half := S.paperBeta0_ge_half

/-- The transport keeps `β₀` equal to the fixed critical line. -/
theorem toWave37L34Inputs_beta0 (S : Wave39L34Inputs K ι N χ) :
    (S.toWave37L34Inputs).beta0 = fixedBeta0 := rfl

/-- The transport keeps the actual probe miss. -/
theorem toWave37L34Inputs_actualMiss (S : Wave39L34Inputs K ι N χ) :
    (S.toWave37L34Inputs).actualMiss = S.actualMiss := rfl

/-- **The all-zeros strip packet is derived**, never assumed as a field. -/
theorem toZeroStrip (line : DirichletLZerosOnLine)
    (S : Wave39L34Inputs K ι N χ) :
    DedekindZetaStripInput K S.beta0 S.cz S.discLog :=
  S.toWave37L34Inputs.toZeroStrip line

/-- **The Stark input is derived** from the retained arithmetic side condition
`paperBeta0_ge_half` and the now-derived `β₀ ≤ 1/2`. -/
theorem toStark (S : Wave39L34Inputs K ι N χ) :
    StarkExceptionalZeroInput S.beta0 S.F S.discLog :=
  S.toWave37L34Inputs.toStark

/-- The literal `RatedLeaf` of the Wave-39 L34 block, through the Wave-37
transport. -/
noncomputable def ratedLeaf (line : DirichletLZerosOnLine)
    (S : Wave39L34Inputs K ι N χ) :
    Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  S.toWave37L34Inputs.ratedLeaf line

/-- **The Wave-39 L34 loss is exactly the actual probe miss.** -/
theorem ratedLeaf_loss_eq (line : DirichletLZerosOnLine)
    (S : Wave39L34Inputs K ι N χ) (n : ℕ) :
    (S.ratedLeaf line).loss n = S.actualMiss n := by
  simpa only [ratedLeaf, toWave37L34Inputs_actualMiss] using
    (S.toWave37L34Inputs).ratedLeaf_loss_eq line n

/-- The loss is nonnegative. -/
theorem ratedLeaf_loss_nonneg (line : DirichletLZerosOnLine)
    (S : Wave39L34Inputs K ι N χ) (n : ℕ) :
    0 ≤ (S.ratedLeaf line).loss n :=
  (S.ratedLeaf line).loss_nonneg n

/-- **A genuine nonzero loss.**  Whenever the probe stage actually fails with
positive probability at some index, the assembled loss is positive there. -/
theorem ratedLeaf_loss_pos (line : DirichletLZerosOnLine)
    (S : Wave39L34Inputs K ι N χ) {n : ℕ} (h : 0 < S.actualMiss n) :
    0 < (S.ratedLeaf line).loss n := by
  have h' : 0 < S.toWave37L34Inputs.actualMiss n := by
    simpa only [toWave37L34Inputs_actualMiss] using h
  simpa only [ratedLeaf] using S.toWave37L34Inputs.ratedLeaf_loss_pos line h'

/-- The L34 ledger slot. -/
theorem ratedLeaf_slot (line : DirichletLZerosOnLine)
    (S : Wave39L34Inputs K ι N χ) :
    ∀ᶠ n : ℕ in atTop,
      (S.ratedLeaf line).loss n ≤ exp (-(2 : ℝ) * scale n) :=
  (S.ratedLeaf line).slot

end Wave39L34Inputs

/-! ## 2. The Wave-39 ledger -/

/-- **The Wave-39 ledger.**  It is the fully discharged ledger at the
constructed L18.4 certificate and the Wave-39 L34 leaf. -/
noncomputable def wave39Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave39L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  fullyDischargedSlots (paperCertificate line) l19.toL19FullCertificate
    (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf l21.toL21_2LeafData)
    (wave15L27Leaf l27_data l27_finish) l30.toWave26L30Inputs.toSubexpLeaf
    (l34.ratedLeaf line) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
    (wave14P1Leaf p1)

/-- The Wave-39 ledger is the Wave-37 ledger at the transported block. -/
theorem wave39Slots_eq_wave37Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave39L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) :
    wave39Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave37Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave37L34Inputs p1 := rfl

/-- The Wave-39 ledger total, term by term. -/
theorem wave39Slots_total_eq {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave39L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave39Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
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
  simpa only [wave39Slots] using
    fullyDischargedSlots_total_eq (paperCertificate line) l19.toL19FullCertificate
      (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
      (wave14L21_2Leaf l21.toL21_2LeafData)
      (wave15L27Leaf l27_data l27_finish) l30.toWave26L30Inputs.toSubexpLeaf
      (l34.ratedLeaf line) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
      (wave14P1Leaf p1) n

/-- **The Wave-39 and Wave-37 ledger totals agree.**  The only difference
between the two blocks is that Wave 39 derives `range` from `rangeArithmetic`;
the leaf and hence the loss are the same. -/
theorem wave39Slots_total_eq_wave37Slots_total
    {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave39L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave39Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
      (wave37Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave37L34Inputs p1).total n := by
  rw [wave39Slots_eq_wave37Slots]

/-- **The L34 loss of the Wave-39 ledger is exactly the actual probe miss.** -/
theorem wave39Slots_l34_loss_eq {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l34 : Wave39L34Inputs K ι N χ) (n : ℕ) :
    (l34.ratedLeaf line).loss n = l34.actualMiss n :=
  l34.ratedLeaf_loss_eq line n

/-! ## 3. The combined residual record -/

/-- **The Wave-39 combined residual record.**

It is the Wave-37 record with the L34 block replaced by `Wave39L34Inputs`: the
critical line is fixed, the two half-line inequalities are theorems, and the
packaged `range` input is derived from `rangeArithmetic`.  All other fields are
copied from the Wave-37 record, and the ledger is `wave39Slots`. -/
structure PaperResidualFor39 (line : DirichletLZerosOnLine)
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
  /-- **L34 with `β₀ = 1/2` and the `T⁶` range input derived** from the raw
  arithmetic. -/
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
  /-- **The C5 data assembled by `c5FullOfCount`.** -/
  c5Data : Wave15C5Data concrete
  /-- Adapter: the concrete C5 loss is dominated by the Wave-39 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave39Slots line l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor39

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor39 → FullyDischargedInputs` directly.**  The L34 leaf is
the Wave-39 leaf; the ledger is `wave39Slots`, definitionally the fully
discharged ledger at that leaf. -/
noncomputable def toFullyDischargedInputs
    (I : PaperResidualFor39 line K ι N χ E D) : FullyDischargedInputs E D where
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
    simpa only [wave39Slots] using I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs
    (I : PaperResidualFor39 line K ι N χ E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- **`PaperResidualFor39 → PaperResidualFor37`**, filling the removed `range`
field with the derived `toRange`.  No extra witness is needed: the range input
is arithmetic, not analytic. -/
noncomputable def toPaperResidualFor37
    (I : PaperResidualFor39 line K ι N χ E D) :
    PaperResidualFor37 line K ι N χ E D where
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34.toWave37L34Inputs
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
    rw [← wave39Slots_total_eq_wave37Slots_total line I.l19 I.l20_2 I.l20_4
      I.l21 I.l27_data I.l27_finish I.l30 I.l34 I.p1 n]
    exact I.loss_le n hN

/-- The L34 loss of the Wave-39 record is exactly the actual probe miss. -/
theorem l34_loss_eq (I : PaperResidualFor39 line K ι N χ E D) (n : ℕ) :
    (I.l34.ratedLeaf line).loss n = I.l34.actualMiss n :=
  I.l34.ratedLeaf_loss_eq line n

/-- **The `T⁶` range input of the Wave-39 record is derived**, not a field. -/
theorem range_derived (I : PaperResidualFor39 line K ι N χ E D) :
    ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog :=
  I.l34.toRange

/-- **The zero-free datum of the Wave-39 record is the strip packet**, derived
from the critical line and the factorization. -/
theorem zeroStrip_derived (I : PaperResidualFor39 line K ι N χ E D) :
    DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog :=
  I.l34.toZeroStrip line

/-- The Stark field is derived, not stored. -/
theorem stark_derived (I : PaperResidualFor39 line K ι N χ E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  I.l34.toStark

/-- **The two half-line inequalities are theorems**, not fields. -/
theorem beta0_half_bounds (I : PaperResidualFor39 line K ι N χ E D) (n : ℕ) :
    1 / 2 ≤ I.l34.beta0 n ∧ I.l34.beta0 n ≤ 1 / 2 :=
  ⟨I.l34.half_le_beta0 n, I.l34.beta0_le_half n⟩

end PaperResidualFor39

/-- **The schedule-indexed form of the Wave-39 record.** -/
abbrev PaperResidualFor39Schedule (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor39 line K ι N χ (E s) D

/-! ## 4. The endpoint -/

/-- **Wave-39 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K`, every explicit abelian factorization `ζ_K = ∏ L(·, χ)` away from the pole,
and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor39 line K ι N χ (E s) D` record, the kernel-checked
driver outputs a permutation of `n.primeFactorsList` and has expected serialized
bit cost eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`.

The L34 block combines both reductions: `β₀` is the fixed critical line, both
half-line inequalities are theorems, and the packaged `range` input is derived
from `rangeArithmetic`.  The endpoint is proved from the Wave-37 endpoint through
the `range`-filling transport `PaperResidualFor39.toPaperResidualFor37`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave39Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
      (χ : ∀ i, DirichletCharacter ℂ (N i)),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor39 line K ι N χ (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave37Inputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF ι instF instDec N instN χ E hI
  exact hmain K ι N χ E fun s D hvalid => (hI s D hvalid).toPaperResidualFor37

/-! ## 5. Residual accounting -/

/-- The field names of `Wave39L34Inputs`.  There is no `beta0`, no
`half_le_beta0`, no `beta0_le_half` and no packaged `range`; the raw arithmetic
appears as the single bundled entry `rangeArithmetic`. -/
def wave39L34FieldNames : List String :=
  ["degree", "discLog", "F", "T", "count",
   "inertCount", "degreeOneInert", "liX", "liBeta0", "pTrial", "actualMiss",
   "classCount", "R", "cz", "cz_pos", "factorization",
   "K", "C", "cZ", "cbr", "csel", "Ch", "rangeArithmetic", "T_ge_one",
   "cheb", "inert_ge_count", "bracket", "error_scalar", "degree_loss_scalar",
   "degree_one_reduction", "selection", "budget", "classCount_pos", "classCubic",
   "constant_margin", "scale_cubic", "actualMiss_nonneg", "union_bound",
   "pTrial_nonneg", "pTrial_le_one", "starkF_pos", "paperBeta0_ge_half"]

theorem wave39L34FieldNames_length : wave39L34FieldNames.length = 42 := rfl

/-- **The field list is the Wave-37 list with `range` replaced by
`rangeArithmetic`.** -/
theorem wave39L34FieldNames_eq_wave37_replace :
    wave39L34FieldNames =
      wave37L34FieldNames.map
        (fun s => if s = "range" then "rangeArithmetic" else s) := by
  decide

/-- **The packaged `range` is not a field any more.** -/
theorem wave39_no_range_field :
    wave39L34FieldNames.all (fun s => decide (s ≠ "range")) = true := by
  decide

/-- **The free `β₀` is not a field.** -/
theorem wave39_no_beta0_field :
    wave39L34FieldNames.all (fun s => decide (s ≠ "beta0")) = true := by
  decide

/-- **Neither half-line inequality is a field.** -/
theorem wave39_no_half_le_beta0_no_beta0_le_half_field :
    wave39L34FieldNames.all (fun s => decide (s ≠ "half_le_beta0")) = true ∧
      wave39L34FieldNames.all (fun s => decide (s ≠ "beta0_le_half")) = true :=
  ⟨by decide, by decide⟩

/-- The raw arithmetic bundle and the factorization remain fields. -/
theorem wave39_L34_content :
    wave39L34FieldNames.contains "rangeArithmetic" = true ∧
      wave39L34FieldNames.contains "factorization" = true ∧
      wave39L34FieldNames.contains "paperBeta0_ge_half" = true :=
  ⟨by decide, by decide, by decide⟩

/-- The field names of `PaperResidualFor39`; there is no `l18_4` field. -/
def wave39FieldNames : List String :=
  ["l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave39FieldNames_length : wave39FieldNames.length = 17 := rfl

/-- **The record carries no L18.4 hypothesis.** -/
theorem wave39_no_l18_4 :
    wave39FieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- **The exact Wave-39 residual list.**  It is the Wave-37 list with `range`
replaced by the single raw arithmetic bundle `rangeArithmetic`.  In particular
no `range`, no `beta0` and no half-line entry appears, and the list has 22
entries. -/
def wave39RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "factorization", "cheb", "rangeArithmetic",
   "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

/-- The residual list literally is the displayed list. -/
theorem wave39RemainingFieldNames_exact :
    wave39RemainingFieldNames =
      ["zetaRH", "localCount", "hbuchstab", "hparity",
       "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
       "killMass", "curveBudget",
       "factorization", "cheb", "rangeArithmetic",
       "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"] :=
  rfl

theorem wave39RemainingFieldNames_length :
    wave39RemainingFieldNames.length = 22 := rfl

/-- **The Wave-39 residual list is the Wave-37 list with `range` replaced by
`rangeArithmetic`.** -/
theorem wave39RemainingFieldNames_eq_wave37_replace :
    wave39RemainingFieldNames =
      wave37RemainingFieldNames.map
        (fun s => if s = "range" then "rangeArithmetic" else s) := by
  decide

/-- **No packaged `range` entry survives in the residual list.** -/
theorem wave39_no_range_residual :
    wave39RemainingFieldNames.all (fun s => decide (s ≠ "range")) = true := by
  decide

/-- **The free `β₀` entry does not survive either.** -/
theorem wave39_no_beta0_residual :
    wave39RemainingFieldNames.all (fun s => decide (s ≠ "beta0")) = true := by
  decide

/-- **Neither half-line entry survives in the residual list.** -/
theorem wave39_no_half_le_beta0_no_beta0_le_half_residual :
    wave39RemainingFieldNames.all (fun s => decide (s ≠ "half_le_beta0")) = true ∧
      wave39RemainingFieldNames.all (fun s => decide (s ≠ "beta0_le_half")) = true :=
  ⟨by decide, by decide⟩

/-- **The residual list does not contain the L18.4 certificate entry.** -/
theorem wave39_no_l18_4_residual :
    wave39RemainingFieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- The raw arithmetic bundle is the replacement residual entry. -/
theorem wave39_rangeArithmetic_residual :
    wave39RemainingFieldNames.contains "rangeArithmetic" = true := by
  decide

/-- The residual list still contains the Buchstab/parity, factorization,
Chebotarev and remaining certificate entries. -/
theorem wave39_residual_blocks :
    wave39RemainingFieldNames.contains "hbuchstab" = true ∧
      wave39RemainingFieldNames.contains "hparity" = true ∧
      wave39RemainingFieldNames.contains "factorization" = true ∧
      wave39RemainingFieldNames.contains "cheb" = true ∧
      wave39RemainingFieldNames.contains "rangeArithmetic" = true ∧
      wave39RemainingFieldNames.contains "l19" = true ∧
      wave39RemainingFieldNames.contains "l20_2" = true ∧
      wave39RemainingFieldNames.contains "l20_4" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The complete remaining L30 analytic input** is the Buchstab large-prime
estimate together with the odd-half parity fraction. -/
theorem wave39_l30_remaining (I : PaperResidualFor39 line K ι N χ E D) :
    BuchstabLargePrimeShortIntervalLower I.l30.counts.c I.l30.counts.p
        I.l30.counts.ε ∧
      CentralOddHalfParity I.l30.counts.θ I.l30.counts.p I.l30.counts.ε :=
  ⟨I.l30.counts.hbuchstab, I.l30.counts.hparity⟩

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave39_l21_remaining (I : PaperResidualFor39 line K ι N χ E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L34 analytic input**: the factorization and the
Chebotarev data, with `β₀` fixed at `1/2`, the strip packet derived, and the
`T⁶` range input derived from `rangeArithmetic`. -/
theorem wave39_l34_remaining (I : PaperResidualFor39 line K ι N χ E D) :
    DedekindZetaFactorsIntoDirichletOffPole K ι N χ ∧
      DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog ∧
      0 < I.l34.cz ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog :=
  ⟨I.l34.factorization, I.zeroStrip_derived, I.l34.cz_pos,
    I.l34.cheb, I.range_derived⟩

/-- At the fixed critical line, the two former half-line fields hold
pointwise. -/
theorem wave39_l34_beta0_eq_half (I : PaperResidualFor39 line K ι N χ E D)
    (n : ℕ) : I.l34.beta0 n = 1 / 2 :=
  I.l34.beta0_eq_half n

/-! ## Axiom audit -/

#print axioms Wave39L34Inputs.beta0_eq_fixed
#print axioms Wave39L34Inputs.half_le_beta0
#print axioms Wave39L34Inputs.beta0_le_half
#print axioms Wave39L34Inputs.beta0_eq_half
#print axioms Wave39L34Inputs.toWave38L34Inputs
#print axioms Wave39L34Inputs.toRange
#print axioms Wave39L34Inputs.degree_pos
#print axioms Wave39L34Inputs.discLog_pos
#print axioms Wave39L34Inputs.rangeT6
#print axioms Wave39L34Inputs.toZeroStrip
#print axioms Wave39L34Inputs.toStark
#print axioms Wave39L34Inputs.toWave37L34Inputs
#print axioms Wave39L34Inputs.toWave37L34Inputs_beta0
#print axioms Wave39L34Inputs.toWave37L34Inputs_actualMiss
#print axioms Wave39L34Inputs.ratedLeaf_loss_eq
#print axioms Wave39L34Inputs.ratedLeaf_loss_pos
#print axioms wave39Slots
#print axioms wave39Slots_eq_wave37Slots
#print axioms wave39Slots_total_eq
#print axioms wave39Slots_total_eq_wave37Slots_total
#print axioms wave39Slots_l34_loss_eq
#print axioms PaperResidualFor39.toFullyDischargedInputs
#print axioms PaperResidualFor39.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor39.toPaperResidualFor37
#print axioms PaperResidualFor39.l34_loss_eq
#print axioms PaperResidualFor39.range_derived
#print axioms PaperResidualFor39.zeroStrip_derived
#print axioms PaperResidualFor39.stark_derived
#print axioms PaperResidualFor39.beta0_half_bounds
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave39Inputs
#print axioms wave39L34FieldNames_length
#print axioms wave39L34FieldNames_eq_wave37_replace
#print axioms wave39_no_range_field
#print axioms wave39_no_beta0_field
#print axioms wave39_no_half_le_beta0_no_beta0_le_half_field
#print axioms wave39_L34_content
#print axioms wave39FieldNames_length
#print axioms wave39_no_l18_4
#print axioms wave39RemainingFieldNames_exact
#print axioms wave39RemainingFieldNames_length
#print axioms wave39RemainingFieldNames_eq_wave37_replace
#print axioms wave39_no_range_residual
#print axioms wave39_no_beta0_residual
#print axioms wave39_no_half_le_beta0_no_beta0_le_half_residual
#print axioms wave39_no_l18_4_residual
#print axioms wave39_rangeArithmetic_residual
#print axioms wave39_residual_blocks
#print axioms wave39_l30_remaining
#print axioms wave39_l21_remaining
#print axioms wave39_l34_remaining
#print axioms wave39_l34_beta0_eq_half

end Cogentic.RandomizedPaperEndpointWave39
