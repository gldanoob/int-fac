import Cogentic.RandomizedPaperEndpointWave36

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 37: the L34 block with `β₀` fixed at the critical line

The Wave-36 L34 block `Wave36L34Inputs` still carried the free sequence
`beta0 : ℕ → ℝ` together with the two arithmetic fields

```
half_le_beta0 : ∀ n, 1 / 2 ≤ beta0 n
beta0_le_half : ∀ n, beta0 n ≤ 1 / 2
```

whose conjunction forces `beta0 = fun _ => 1/2` at every index
(`Wave36L34Inputs.beta0_eq_half`).  Keeping both as fields therefore stores two
redundant data whose only consistent value is the critical line.

This file removes that redundancy:

* the free sequence `beta0` is replaced by the fixed `fun _ => 1 / 2`;
* `half_le_beta0` and `beta0_le_half` are no longer fields — they are the
  theorems `Wave37L34Inputs.half_le_beta0` and `Wave37L34Inputs.beta0_le_half`
  (and `beta0_eq_half`) for the fixed sequence;
* every other field of `Wave36L34Inputs` is kept verbatim, including the
  arithmetic side condition `paperBeta0_ge_half`.

On the last point: `paperBeta0_ge_half` is *not* a consequence of the remaining
data.  `paperBeta0 F discLog = 1 - 1/(4 F log|Δ|)`, so `paperBeta0 ≥ 1/2`
requires `4 F log|Δ| ≥ 2`; positivity of `F` and `log|Δ|` alone (for instance
`F = 1`, `log|Δ| = 1/8`) gives a negative value.  The field is therefore kept as
the genuine arithmetic side condition that turns the critical-line threshold
into Stark's exceptional-zero input; it is not an analytic residual and it is
not listed in the residual accounting below, exactly as in Waves 33–36.

`Wave37L34Inputs.toWave36L34Inputs` transports the fixed block back to the
Wave-36 record (the two deleted inequalities being `le_rfl` at `1/2`), and
`PaperResidualFor37.toFullyDischargedInputs` gives the endpoint directly.

`PaperResidualFor37` is the Wave-36 record with `l34 : Wave37L34Inputs`;
`serialized_assembled_balancedEnvelopeInfimum_from_wave37Inputs` is the endpoint.

## The remaining residual list

It is the Wave-36 list with `half_le_beta0` and `beta0_le_half` deleted, hence
22 entries:

```
[zetaRH, localCount, hbuchstab, hparity,
 hurwitzClassNumber, siegelLower, hasse, waterhouseTrace, killMass, curveBudget,
 factorization, cheb, range,
 l19, l20_2, l20_4, c1, c2, c3, c4, concrete, p1]
```

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss,
probability, count or error is set to zero.  The L34 loss is still exactly the
actual probe miss of the probe stage.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave37

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

/-! ## 1. The Wave-37 L34 block: `β₀ = 1/2` -/

/-- The fixed exceptional zero: the critical line. -/
def fixedBeta0 : ℕ → ℝ := fun _ => 1 / 2

/-- **The Wave-37 L34 block.**  It is `Wave36L34Inputs` with

* the free sequence `beta0` replaced by the fixed `fixedBeta0 = fun _ => 1/2`;
* the fields `half_le_beta0` and `beta0_le_half` deleted, since for the fixed
  sequence they are the theorems `half_le_beta0`, `beta0_le_half`; and
* every other field, including the arithmetic side condition
  `paperBeta0_ge_half`, kept verbatim.

The zero-free content is still the factorization-derived strip packet
(`toZeroStrip`), and Stark is still derived from `paperBeta0_ge_half`
(`toStark`). -/
structure Wave37L34Inputs (K : Type u) [Field K] [NumberField K]
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
  /-- The constant `C` in the effective error. -/
  C : ℝ
  /-- The constant `c` in the effective error. -/
  cZ : ℝ
  /-- The bracket constant. -/
  cbr : ℝ
  /-- The per-ideal selection constant. -/
  csel : ℝ
  /-- The polynomial constant in `h* ≤ Ch T³`. -/
  Ch : ℝ
  /-- The explicit `T^6` range input. -/
  range : ChebotarevT6RangeInput K T degree discLog
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

namespace Wave37L34Inputs

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}

/-- The fixed exceptional zero sequence of the Wave-37 block. -/
def beta0 (_ : Wave37L34Inputs K ι N χ) : ℕ → ℝ := fixedBeta0

/-- The fixed sequence is the critical line, definitionally. -/
theorem beta0_eq_fixed (S : Wave37L34Inputs K ι N χ) :
    S.beta0 = fixedBeta0 := rfl

/-- Pointwise, `β₀ n = 1/2`. -/
theorem beta0_apply (S : Wave37L34Inputs K ι N χ) (n : ℕ) :
    S.beta0 n = 1 / 2 := rfl

/-- **The lower half-line inequality is now a theorem.**  For the fixed
sequence it is reflexivity at `1/2`. -/
theorem half_le_beta0 (S : Wave37L34Inputs K ι N χ) (n : ℕ) :
    1 / 2 ≤ S.beta0 n :=
  le_rfl

/-- **The upper GRH inequality is now a theorem.**  For the fixed sequence it is
reflexivity at `1/2`. -/
theorem beta0_le_half (S : Wave37L34Inputs K ι N χ) (n : ℕ) :
    S.beta0 n ≤ 1 / 2 :=
  le_rfl

/-- Both former fields together say that `β₀` is the critical line. -/
theorem beta0_eq_half (S : Wave37L34Inputs K ι N χ) (n : ℕ) :
    S.beta0 n = 1 / 2 :=
  le_antisymm (S.beta0_le_half n) (S.half_le_beta0 n)

/-- **The all-zeros strip packet is derived**, never assumed as a field. -/
theorem toZeroStrip (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) :
    DedekindZetaStripInput K S.beta0 S.cz S.discLog :=
  DedekindZetaStripInput_of_GRH_of_factorization line S.factorization
    S.half_le_beta0 S.cz S.discLog

/-- **The Stark input is derived** from the retained arithmetic side condition
`paperBeta0_ge_half` and the now-derived `β₀ ≤ 1/2`. -/
theorem toStark (S : Wave37L34Inputs K ι N χ) :
    StarkExceptionalZeroInput S.beta0 S.F S.discLog :=
  starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0
    S.starkF_pos S.range.discLog_pos S.beta0_le_half S.paperBeta0_ge_half

/-- **The strip-based Chebotarev-side input.**  Every data field is passed
through with `beta0 := S.beta0`; the zero-free field is the derived all-zeros
packet `S.toZeroStrip line`, and Stark is the derived arithmetic replacement. -/
noncomputable def toL34ChebotarevSidesInputsStrip
    (line : DirichletLZerosOnLine) (S : Wave37L34Inputs K ι N χ) :
    L34ChebotarevSidesInputsStrip K where
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
  K := S.K
  C := S.C
  cZ := S.cZ
  cz := S.cz
  cz_pos := S.cz_pos
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  zeroStrip := S.toZeroStrip line
  stark := S.toStark
  range := S.range
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

/-- The strip-based input carries the same actual probe miss. -/
theorem toL34ChebotarevSidesInputsStrip_actualMiss
    (line : DirichletLZerosOnLine) (S : Wave37L34Inputs K ι N χ) :
    (S.toL34ChebotarevSidesInputsStrip line).actualMiss = S.actualMiss := rfl

/-- The strip-based core assembled from the Wave-37 block. -/
noncomputable def toL34SidesCore (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) : L34SidesCoreStrip K :=
  (S.toL34ChebotarevSidesInputsStrip line).toL34SidesCore

/-- The literal `RatedLeaf` of the Wave-37 L34 block. -/
noncomputable def ratedLeaf (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) :
    Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  (S.toL34ChebotarevSidesInputsStrip line).ratedLeaf

/-- **The Wave-37 L34 loss is exactly the actual probe miss.** -/
theorem ratedLeaf_loss_eq (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) (n : ℕ) :
    (S.ratedLeaf line).loss n = S.actualMiss n := by
  simpa only [ratedLeaf, toL34ChebotarevSidesInputsStrip_actualMiss] using
    (S.toL34ChebotarevSidesInputsStrip line).ratedLeaf_loss_eq n

/-- The loss is nonnegative. -/
theorem ratedLeaf_loss_nonneg (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) (n : ℕ) :
    0 ≤ (S.ratedLeaf line).loss n :=
  (S.ratedLeaf line).loss_nonneg n

/-- **A genuine nonzero loss.**  Whenever the probe stage actually fails with
positive probability at some index, the assembled loss is positive there. -/
theorem ratedLeaf_loss_pos (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) {n : ℕ} (h : 0 < S.actualMiss n) :
    0 < (S.ratedLeaf line).loss n := by
  simpa only [ratedLeaf, toL34ChebotarevSidesInputsStrip_actualMiss] using
    (S.toL34ChebotarevSidesInputsStrip line).ratedLeaf_loss_pos h

/-- The L34 ledger slot. -/
theorem ratedLeaf_slot (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) :
    ∀ᶠ n : ℕ in atTop,
      (S.ratedLeaf line).loss n ≤ exp (-(2 : ℝ) * scale n) :=
  (S.ratedLeaf line).slot

/-- **The strip packet is still derived**, not a field of the Wave-37 block. -/
theorem zeroStrip_derived (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) :
    DedekindZetaStripInput K S.beta0 S.cz S.discLog :=
  S.toZeroStrip line

/-- **Compatibility transport to the Wave-36 block.**  The two inequalities that
Wave 36 stores as fields are here the theorems `half_le_beta0` and
`beta0_le_half`; every other field is passed through. -/
noncomputable def toWave36L34Inputs (S : Wave37L34Inputs K ι N χ) :
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
  range := S.range
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

/-- The transport keeps `β₀` equal to the fixed critical line. -/
theorem toWave36L34Inputs_beta0 (S : Wave37L34Inputs K ι N χ) :
    (S.toWave36L34Inputs).beta0 = fixedBeta0 := rfl

/-- The transport keeps the actual probe miss. -/
theorem toWave36L34Inputs_actualMiss (S : Wave37L34Inputs K ι N χ) :
    (S.toWave36L34Inputs).actualMiss = S.actualMiss := rfl

/-- Transporting to Wave 36 and reading the leaf still gives the actual probe
miss. -/
theorem toWave36L34Inputs_ratedLeaf_loss_eq (line : DirichletLZerosOnLine)
    (S : Wave37L34Inputs K ι N χ) (n : ℕ) :
    ((S.toWave36L34Inputs).ratedLeaf line).loss n = S.actualMiss n :=
  (S.toWave36L34Inputs).ratedLeaf_loss_eq line n

end Wave37L34Inputs

/-! ## 2. The Wave-37 ledger -/

/-- **The Wave-37 ledger.**  It is the fully discharged ledger at the constructed
L18.4 certificate and the Wave-37 L34 leaf, whose `β₀` is the fixed critical
line. -/
noncomputable def wave37Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave37L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  fullyDischargedSlots (paperCertificate line) l19.toL19FullCertificate
    (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf l21.toL21_2LeafData)
    (wave15L27Leaf l27_data l27_finish) l30.toWave26L30Inputs.toSubexpLeaf
    (l34.ratedLeaf line) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
    (wave14P1Leaf p1)

/-- The Wave-37 ledger total, term by term. -/
theorem wave37Slots_total_eq {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave37L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave37Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
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
  simpa only [wave37Slots] using
    fullyDischargedSlots_total_eq (paperCertificate line) l19.toL19FullCertificate
      (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
      (wave14L21_2Leaf l21.toL21_2LeafData)
      (wave15L27Leaf l27_data l27_finish) l30.toWave26L30Inputs.toSubexpLeaf
      (l34.ratedLeaf line) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
      (wave14P1Leaf p1) n

/-- **The Wave-37 and Wave-36 ledger totals agree** at the transported block.
The only difference between the two ledgers is the L34 leaf, and both leaves
have loss exactly the same actual probe miss. -/
theorem wave37Slots_total_eq_wave36Slots_total
    {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave37L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave37Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
      (wave36Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30
        (l34.toWave36L34Inputs) p1).total n := by
  rw [wave37Slots_total_eq, wave36Slots_total_eq]
  simp only [Wave37L34Inputs.ratedLeaf_loss_eq,
    Wave36L34Inputs.ratedLeaf_loss_eq]
  rfl

/-- **The L34 loss of the Wave-37 ledger is exactly the actual probe miss.** -/
theorem wave37Slots_l34_loss_eq {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l34 : Wave37L34Inputs K ι N χ) (n : ℕ) :
    (l34.ratedLeaf line).loss n = l34.actualMiss n :=
  l34.ratedLeaf_loss_eq line n

/-! ## 3. The combined residual record with `β₀` fixed -/

/-- **The Wave-37 combined residual record.**

It is the Wave-36 record with the L34 block replaced by `Wave37L34Inputs`, where
`β₀` is the fixed critical line and the two half-line inequalities are theorems
rather than fields.  All other fields are copied from the Wave-36 record, and
the ledger is `wave37Slots` at the new L34 leaf. -/
structure PaperResidualFor37 (line : DirichletLZerosOnLine)
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
  /-- **L34 with `β₀ = 1/2`**: the half-line inequalities are derived, and the
  strip packet is derived from the factorization. -/
  l34 : Wave37L34Inputs K ι N χ
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
  /-- Adapter: the concrete C5 loss is dominated by the Wave-37 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave37Slots line l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor37

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor37 → FullyDischargedInputs` directly.**  The L34 leaf is
the Wave-37 fixed-`β₀` leaf; the ledger is `wave37Slots`, definitionally the
fully discharged ledger at that leaf. -/
noncomputable def toFullyDischargedInputs
    (I : PaperResidualFor37 line K ι N χ E D) : FullyDischargedInputs E D where
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
    simpa only [wave37Slots] using I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs
    (I : PaperResidualFor37 line K ι N χ E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- The L34 loss of the Wave-37 record is exactly the actual probe miss. -/
theorem l34_loss_eq (I : PaperResidualFor37 line K ι N χ E D) (n : ℕ) :
    (I.l34.ratedLeaf line).loss n = I.l34.actualMiss n :=
  I.l34.ratedLeaf_loss_eq line n

/-- **The zero-free datum of the Wave-37 record is the strip packet**, derived
from the critical line and the factorization. -/
theorem zeroStrip_derived (I : PaperResidualFor37 line K ι N χ E D) :
    DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog :=
  I.l34.toZeroStrip line

/-- The Stark field is derived from `paperBeta0_ge_half`, not stored. -/
theorem stark_derived (I : PaperResidualFor37 line K ι N χ E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  I.l34.toStark

/-- **The two half-line inequalities are theorems**, not fields. -/
theorem beta0_half_bounds (I : PaperResidualFor37 line K ι N χ E D) (n : ℕ) :
    1 / 2 ≤ I.l34.beta0 n ∧ I.l34.beta0 n ≤ 1 / 2 :=
  ⟨I.l34.half_le_beta0 n, I.l34.beta0_le_half n⟩

/-- **`PaperResidualFor37 → PaperResidualFor36`**, by transporting the L34 block
to the Wave-36 record where the two inequalities are fields again (filled with
the derived theorems). -/
noncomputable def toPaperResidualFor36
    (I : PaperResidualFor37 line K ι N χ E D) :
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
    rw [← wave37Slots_total_eq_wave36Slots_total line I.l19 I.l20_2 I.l20_4
      I.l21 I.l27_data I.l27_finish I.l30 I.l34 I.p1 n]
    exact I.loss_le n hN

end PaperResidualFor37

/-- **The schedule-indexed form of the Wave-37 record.** -/
abbrev PaperResidualFor37Schedule (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor37 line K ι N χ (E s) D

/-! ## 4. The endpoint -/

/-- **Wave-37 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K`, every explicit abelian factorization `ζ_K = ∏ L(·, χ)` away from the pole,
and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor37 line K ι N χ (E s) D` record, the kernel-checked
driver outputs a permutation of `n.primeFactorsList` and has expected serialized
bit cost eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`.

The L34 block carries the fixed `β₀ = 1/2`: the two half-line inequalities that
Wave 36 stored as fields are now theorems, and the zero-free content is the
all-zeros strip packet derived from `line` and the factorization.  The endpoint
is proved from the fully discharged endpoint at the Wave-37 L34 leaf. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave37Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
      (χ : ∀ i, DirichletCharacter ℂ (N i)),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor37 line K ι N χ (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF ι instF instDec N instN χ E hI
  exact hmain E fun s D hvalid => (hI s D hvalid).toFullyDischargedInputs

/-! ## 5. Residual accounting -/

/-- The field names of `Wave37L34Inputs`.  The free sequence `beta0` and the two
half-line fields `half_le_beta0`, `beta0_le_half` are absent; they are replaced
by the fixed `fixedBeta0` and the theorems of the same names. -/
def wave37L34FieldNames : List String :=
  ["degree", "discLog", "F", "T", "count",
   "inertCount", "degreeOneInert", "liX", "liBeta0", "pTrial", "actualMiss",
   "classCount", "R", "cz", "cz_pos", "factorization",
   "K", "C", "cZ", "cbr", "csel", "Ch", "range", "T_ge_one",
   "cheb", "inert_ge_count", "bracket", "error_scalar", "degree_loss_scalar",
   "degree_one_reduction", "selection", "budget", "classCount_pos", "classCubic",
   "constant_margin", "scale_cubic", "actualMiss_nonneg", "union_bound",
   "pTrial_nonneg", "pTrial_le_one", "starkF_pos", "paperBeta0_ge_half"]

theorem wave37L34FieldNames_length : wave37L34FieldNames.length = 42 := rfl

/-- **The free `β₀` is not a field.** -/
theorem wave37_no_beta0_field :
    wave37L34FieldNames.all (fun s => decide (s ≠ "beta0")) = true := by
  decide

/-- **Neither half-line inequality is a field.** -/
theorem wave37_no_half_le_beta0_no_beta0_le_half_field :
    wave37L34FieldNames.all (fun s => decide (s ≠ "half_le_beta0")) = true ∧
      wave37L34FieldNames.all (fun s => decide (s ≠ "beta0_le_half")) = true :=
  ⟨by decide, by decide⟩

/-- The factorization and the arithmetic side condition remain fields. -/
theorem wave37_L34_content :
    wave37L34FieldNames.contains "factorization" = true ∧
      wave37L34FieldNames.contains "paperBeta0_ge_half" = true :=
  ⟨by decide, by decide⟩

/-- The field names of `PaperResidualFor37`; there is no `l18_4` field. -/
def wave37FieldNames : List String :=
  ["l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave37FieldNames_length : wave37FieldNames.length = 17 := rfl

/-- **The record carries no L18.4 hypothesis.** -/
theorem wave37_no_l18_4 :
    wave37FieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- **The exact Wave-37 residual list.**  It is the Wave-36 list with the two
half-line entries `half_le_beta0` and `beta0_le_half` removed, because for the
fixed `β₀ = 1/2` they are theorems. -/
def wave37RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "factorization", "cheb", "range",
   "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

/-- The residual list literally is the displayed list. -/
theorem wave37RemainingFieldNames_exact :
    wave37RemainingFieldNames =
      ["zetaRH", "localCount", "hbuchstab", "hparity",
       "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
       "killMass", "curveBudget",
       "factorization", "cheb", "range",
       "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"] :=
  rfl

theorem wave37RemainingFieldNames_length :
    wave37RemainingFieldNames.length = 22 := rfl

/-- **The Wave-37 residual list is the Wave-36 list with the two half-line
entries filtered out.** -/
theorem wave37RemainingFieldNames_eq_wave36_filter :
    wave37RemainingFieldNames =
      wave36RemainingFieldNames.filter
        (fun s => decide (s ≠ "half_le_beta0") && decide (s ≠ "beta0_le_half")) := by
  decide

/-- **Neither `half_le_beta0` nor `beta0_le_half` survives in the residual
list**, because both are now theorems. -/
theorem wave37_no_half_le_beta0_no_beta0_le_half_residual :
    wave37RemainingFieldNames.all (fun s => decide (s ≠ "half_le_beta0")) = true ∧
      wave37RemainingFieldNames.all (fun s => decide (s ≠ "beta0_le_half")) = true :=
  ⟨by decide, by decide⟩

/-- **The free `β₀` entry does not survive either.** -/
theorem wave37_no_beta0_residual :
    wave37RemainingFieldNames.all (fun s => decide (s ≠ "beta0")) = true := by
  decide

/-- **The residual list does not contain the L18.4 certificate entry.** -/
theorem wave37_no_l18_4_residual :
    wave37RemainingFieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- The residual list still contains the Buchstab/parity, factorization,
Chebotarev, range and remaining certificate entries. -/
theorem wave37_residual_blocks :
    wave37RemainingFieldNames.contains "hbuchstab" = true ∧
      wave37RemainingFieldNames.contains "hparity" = true ∧
      wave37RemainingFieldNames.contains "factorization" = true ∧
      wave37RemainingFieldNames.contains "cheb" = true ∧
      wave37RemainingFieldNames.contains "range" = true ∧
      wave37RemainingFieldNames.contains "l19" = true ∧
      wave37RemainingFieldNames.contains "l20_2" = true ∧
      wave37RemainingFieldNames.contains "l20_4" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The complete remaining L30 analytic input** is the Buchstab large-prime
estimate together with the odd-half parity fraction. -/
theorem wave37_l30_remaining (I : PaperResidualFor37 line K ι N χ E D) :
    BuchstabLargePrimeShortIntervalLower I.l30.counts.c I.l30.counts.p
        I.l30.counts.ε ∧
      CentralOddHalfParity I.l30.counts.θ I.l30.counts.p I.l30.counts.ε :=
  ⟨I.l30.counts.hbuchstab, I.l30.counts.hparity⟩

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave37_l21_remaining (I : PaperResidualFor37 line K ι N χ E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L34 analytic input is the factorization and the
Chebotarev/range data**, with `β₀` fixed at `1/2` and the strip packet derived. -/
theorem wave37_l34_remaining (I : PaperResidualFor37 line K ι N χ E D) :
    DedekindZetaFactorsIntoDirichletOffPole K ι N χ ∧
      DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog ∧
      0 < I.l34.cz ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog :=
  ⟨I.l34.factorization, I.zeroStrip_derived, I.l34.cz_pos,
    I.l34.cheb, I.l34.range⟩

/-- At the fixed critical line, the two former half-line fields hold
pointwise. -/
theorem wave37_l34_beta0_eq_half (I : PaperResidualFor37 line K ι N χ E D)
    (n : ℕ) : I.l34.beta0 n = 1 / 2 :=
  I.l34.beta0_eq_half n

/-! ## Axiom audit -/

#print axioms Wave37L34Inputs.beta0_eq_fixed
#print axioms Wave37L34Inputs.half_le_beta0
#print axioms Wave37L34Inputs.beta0_le_half
#print axioms Wave37L34Inputs.beta0_eq_half
#print axioms Wave37L34Inputs.toZeroStrip
#print axioms Wave37L34Inputs.toStark
#print axioms Wave37L34Inputs.toL34ChebotarevSidesInputsStrip
#print axioms Wave37L34Inputs.ratedLeaf_loss_eq
#print axioms Wave37L34Inputs.ratedLeaf_loss_pos
#print axioms Wave37L34Inputs.toWave36L34Inputs
#print axioms Wave37L34Inputs.toWave36L34Inputs_ratedLeaf_loss_eq
#print axioms wave37Slots
#print axioms wave37Slots_total_eq
#print axioms wave37Slots_total_eq_wave36Slots_total
#print axioms wave37Slots_l34_loss_eq
#print axioms PaperResidualFor37.toFullyDischargedInputs
#print axioms PaperResidualFor37.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor37.l34_loss_eq
#print axioms PaperResidualFor37.zeroStrip_derived
#print axioms PaperResidualFor37.stark_derived
#print axioms PaperResidualFor37.beta0_half_bounds
#print axioms PaperResidualFor37.toPaperResidualFor36
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave37Inputs
#print axioms wave37L34FieldNames_length
#print axioms wave37_no_beta0_field
#print axioms wave37_no_half_le_beta0_no_beta0_le_half_field
#print axioms wave37_L34_content
#print axioms wave37FieldNames_length
#print axioms wave37_no_l18_4
#print axioms wave37RemainingFieldNames_exact
#print axioms wave37RemainingFieldNames_length
#print axioms wave37RemainingFieldNames_eq_wave36_filter
#print axioms wave37_no_half_le_beta0_no_beta0_le_half_residual
#print axioms wave37_no_beta0_residual
#print axioms wave37_no_l18_4_residual
#print axioms wave37_residual_blocks
#print axioms wave37_l30_remaining
#print axioms wave37_l21_remaining
#print axioms wave37_l34_remaining
#print axioms wave37_l34_beta0_eq_half

end Cogentic.RandomizedPaperEndpointWave37
