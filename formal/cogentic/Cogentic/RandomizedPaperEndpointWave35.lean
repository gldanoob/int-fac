import Cogentic.RandomizedPaperEndpointWave34

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 35: the Wave-34 residual record with `zeroStrip` derived from GRH

The Wave-33 L34 block `Wave33L34Inputs K` still carried the faithful strip
packet as an explicit field

```
zeroStrip : DedekindZetaStripInput K beta0 cz discLog,
```

even though `RandomizedL34DedekindGRH` proves that it follows from

* the critical-line hypothesis `DirichletLZerosOnLine`,
* the explicit abelian factorization
  `DedekindZetaFactorsIntoDirichletOffPole K ι N χ`, and
* the half-line arithmetic `∀ n, 1/2 ≤ beta0 n`.

This file removes `zeroStrip` from the L34 block of the Wave-34 record and
replaces it by those three inputs.  The strip packet is then *derived*:

`Wave35L34Inputs.toZeroStrip line S` is
`DedekindZetaStripInput_of_GRH_of_factorization line S.factorization
S.half_le_beta0 S.cz S.discLog`.

The Wave-34 record already derived the Stark and sequence-indexed
`zeroFree` inputs; Wave 35 derives the remaining strip input as well.  The
factorization is an arithmetic property of abelian number fields, and the
half-line inequality `1/2 ≤ beta0` together with the retained
`beta0_le_half` identifies the exceptional zero with the critical line; no
zero-free statement about `ζ_K` is asserted.

## What is proved

* `Wave35L34Inputs` — the Wave-33 L34 fields with `zeroStrip` deleted and the
  fields `factorization` and `half_le_beta0` added; `toZeroStrip` and
  `toWave33L34Inputs` derive the removed strip packet.
* `wave35Slots` — the Wave-34 ledger at the decoded Wave-33 block.
* `PaperResidualFor35` — the Wave-34 record whose `l34` field is
  `Wave35L34Inputs`; `toPaperResidualFor34` fills `zeroStrip` with the derived
  packet.
* `serialized_assembled_balancedEnvelopeInfimum_from_wave35Inputs` — the
  endpoint, at the same interval for `balancedEnvelopeInfimum`.
* The exact residual list and the fact that `zeroStrip` is no longer a field.

## The exact residual list

The Wave-34 list (25 entries) with `zeroStrip` replaced by `factorization` and
`half_le_beta0`, hence 26 entries:

```
[zetaRH, localCount, hbuchstab, hparity,
 hurwitzClassNumber, siegelLower, hasse, waterhouseTrace, killMass, curveBudget,
 factorization, zeroSeq, zeroSeq_lt_one, cheb, range, half_le_beta0, beta0_le_half,
 l19, l20_2, l20_4, c1, c2, c3, c4, concrete, p1]
```

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss,
probability or error is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave35

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
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u v

/-! ## 1. The Wave-35 L34 block without `zeroStrip` -/

/-- **The Wave-35 L34 block.**  It carries every Wave-33 L34 data field except
the faithful strip packet `zeroStrip`, which is replaced by

* `factorization : DedekindZetaFactorsIntoDirichletOffPole K ι N χ` — the
  explicit finite abelian factorization of `ζ_K` away from the pole, and
* `half_le_beta0 : ∀ n, 1/2 ≤ beta0 n` — the half-line arithmetic.

The strip packet is then a theorem (`toZeroStrip`), obtained from the
critical-line hypothesis, the factorization and the half-line inequality.  No
`zeroFree` and no `stark` field is present; both remain derived by the Wave-33
block. -/
structure Wave35L34Inputs (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) where
  /-- The possible exceptional real zero `β₀`. -/
  beta0 : ℕ → ℝ
  /-- The real part of a generic zero of `ζ_K`. -/
  zeroRealPart : ℕ → ℝ
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
  product of the Dirichlet `L`-functions of `χ`.  (Declared before the range
  constant `K : ℝ` so that `K` here is the number field.) -/
  factorization : DedekindZetaFactorsIntoDirichletOffPole K ι N χ
  /-- **The half-line arithmetic**: the exceptional zero is at least the
  critical line.  Together with `beta0_le_half` this puts it exactly on the
  line, which is what the strip argument needs. -/
  half_le_beta0 : ∀ n, 1 / 2 ≤ beta0 n
  /-- **A genuine zero sequence** of `ζ_K`. -/
  zeroSeq : ZetaZeroSequence (NumberField.dedekindZeta K)
  /-- The sequence's real parts are the recorded `zeroRealPart`. -/
  zeroSeq_realPart : zeroSeq.realPart = zeroRealPart
  /-- **The nontriviality condition**: the recorded zeros have real part `< 1`.
  This excludes Mathlib's junk value `ζ_K 1 = 0` from the sequence. -/
  zeroSeq_lt_one : ∀ n, zeroRealPart n < 1
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
  /-- **The exact GRH residual**: the exceptional zero is at most the critical
  line. -/
  beta0_le_half : ∀ n, beta0 n ≤ 1 / 2
  /-- **The paper's arithmetic side condition** `1/2 ≤ paperBeta0 F discLog`. -/
  paperBeta0_ge_half : ∀ n, 1 / 2 ≤ paperBeta0 F discLog n

namespace Wave35L34Inputs

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}

/-- **The faithful strip packet is derived**, never assumed as a field.  GRH
gives no zeros with `1/2 < Re z < 1`, the half-line inequality upgrades
`β₀ n < Re z` to `1/2 < Re z`, and the factorization transfers the Dirichlet
nonvanishing to `ζ_K`. -/
theorem toZeroStrip (line : DirichletLZerosOnLine)
    (S : Wave35L34Inputs K ι N χ) :
    DedekindZetaStripInput K S.beta0 S.cz S.discLog :=
  DedekindZetaStripInput_of_GRH_of_factorization line S.factorization
    S.half_le_beta0 S.cz S.discLog

/-- **The Wave-33 L34 block, with the strip packet decoded.**  Every retained
data field is passed through; only the removed `zeroStrip` field is
reconstructed by `toZeroStrip`. -/
noncomputable def toWave33L34Inputs (line : DirichletLZerosOnLine)
    (S : Wave35L34Inputs K ι N χ) : Wave33L34Inputs K where
  beta0 := S.beta0
  zeroRealPart := S.zeroRealPart
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
  zeroStrip := S.toZeroStrip line
  zeroSeq := S.zeroSeq
  zeroSeq_realPart := S.zeroSeq_realPart
  zeroSeq_lt_one := S.zeroSeq_lt_one
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

/-- **The transported strip field is the derived packet**, not an
assumption. -/
theorem toWave33L34Inputs_zeroStrip (line : DirichletLZerosOnLine)
    (S : Wave35L34Inputs K ι N χ) :
    (S.toWave33L34Inputs line).zeroStrip = S.toZeroStrip line := rfl

/-- The transport leaves the retained data fields unchanged. -/
theorem toWave33L34Inputs_data (line : DirichletLZerosOnLine)
    (S : Wave35L34Inputs K ι N χ) :
    (S.toWave33L34Inputs line).beta0 = S.beta0 ∧
      (S.toWave33L34Inputs line).zeroRealPart = S.zeroRealPart ∧
      (S.toWave33L34Inputs line).cz = S.cz ∧
      (S.toWave33L34Inputs line).actualMiss = S.actualMiss ∧
      (S.toWave33L34Inputs line).discLog = S.discLog :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The derived Wave-33 block has the same loss, exactly the actual probe
miss. -/
theorem toWave33L34Inputs_loss_eq (line : DirichletLZerosOnLine)
    (S : Wave35L34Inputs K ι N χ) (n : ℕ) :
    (wave15L34Leaf
        (S.toWave33L34Inputs line).toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
      S.actualMiss n :=
  Wave33L34Inputs.toWave28L34Inputs_loss_eq (S.toWave33L34Inputs line) n

/-- The derived Wave-33 block still has no `zeroFree` field: it is a
theorem there as well. -/
theorem toZeroFree (line : DirichletLZerosOnLine)
    (S : Wave35L34Inputs K ι N χ) :
    DedekindZeroFreeInput S.beta0 S.zeroRealPart S.cz S.discLog :=
  Wave33L34Inputs.toZeroFree (S.toWave33L34Inputs line)

/-- The derived Wave-33 block still has no `stark` field: it is a theorem
there as well. -/
theorem toStark (line : DirichletLZerosOnLine)
    (S : Wave35L34Inputs K ι N χ) :
    StarkExceptionalZeroInput S.beta0 S.F S.discLog :=
  Wave33L34Inputs.toStark (S.toWave33L34Inputs line)

end Wave35L34Inputs

/-! ## 2. The Wave-35 ledger -/

/-- **The Wave-35 ledger.**  It is the Wave-34 ledger at the Wave-33 block
decoded from the Wave-35 block by deriving `zeroStrip`. -/
noncomputable def wave35Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave35L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave34Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30
    (l34.toWave33L34Inputs line) p1

/-- The Wave-35 ledger is definitionally the Wave-34 ledger at the decoded
block. -/
theorem wave35Slots_eq_wave34Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave35L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) :
    wave35Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave34Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30
        (l34.toWave33L34Inputs line) p1 := rfl

/-! ## 3. The combined residual record without `zeroStrip` -/

/-- **The Wave-35 combined residual record.**

It is the Wave-34 record with the `zeroStrip` field of the L34 block removed:

* `l34 : Wave35L34Inputs K ι N χ` — the Wave-33 L34 data without `zeroStrip`,
  carrying the explicit factorization `DedekindZetaFactorsIntoDirichletOffPole`
  and the half-line arithmetic `1/2 ≤ β₀` in its place; the strip packet is
  derived;
* `l30 : Wave31L30Inputs` — the Buchstab/parity L30 leaf;
* `l21 : Wave27L21Inputs` — only `zetaRH` and the literal central count;
* the L18.4 certificate is **not a field**: it is the constructed
  `paperCertificate line`.

All other fields are copied verbatim from the Wave-34 record.  The ledger is
`wave35Slots line …`, which is definitionally the Wave-34 ledger at the decoded
block. -/
structure PaperResidualFor35 (line : DirichletLZerosOnLine)
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
  /-- **L34 without `zeroStrip`**: the factorization and half-line arithmetic
  replace the strip packet, which is derived. -/
  l34 : Wave35L34Inputs K ι N χ
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
  /-- Adapter: the concrete C5 loss is dominated by the Wave-35 ledger, i.e. the
  Wave-34 ledger at the decoded block. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave35Slots line l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor35

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor35 line K ι N χ E D → PaperResidualFor34 line K E D`.**
The only change is the L34 block: `zeroStrip` is filled with the derived packet
`I.l34.toZeroStrip line`.  The C5 adapter is unchanged because `wave35Slots` is
definitionally `wave34Slots` at that decoded block. -/
noncomputable def toPaperResidualFor34 (I : PaperResidualFor35 line K ι N χ E D) :
    PaperResidualFor34 line K E D where
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34.toWave33L34Inputs line
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
    simpa only [wave35Slots] using I.loss_le n hN

/-- The transported strip packet is the derived one. -/
theorem toPaperResidualFor34_zeroStrip
    (I : PaperResidualFor35 line K ι N χ E D) :
    (I.toPaperResidualFor34).l34.zeroStrip = I.l34.toZeroStrip line := rfl

/-- The transport leaves the C5 loss adapter unchanged. -/
theorem toPaperResidualFor34_loss_le
    (I : PaperResidualFor35 line K ι N χ E D) (n : ℕ) (hN : 3 ≤ n) :
    c5TotalLoss hN (I.concrete n hN) (I.c5Data.toC5 n hN) ≤
      (wave34Slots line I.l19 I.l20_2 I.l20_4 I.l21
        I.l27_data I.l27_finish I.l30 (I.l34.toWave33L34Inputs line) I.p1).total n :=
  I.loss_le n hN

/-- **`PaperResidualFor35 … → FullyDischargedInputs E D` directly**, through
the Wave-34 record. -/
noncomputable def toFullyDischargedInputs
    (I : PaperResidualFor35 line K ι N χ E D) : FullyDischargedInputs E D :=
  I.toPaperResidualFor34.toFullyDischargedInputs

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs
    (I : PaperResidualFor35 line K ι N χ E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- **`zeroStrip` is derived in the Wave-35 record**, not stored. -/
theorem zeroStrip_derived (I : PaperResidualFor35 line K ι N χ E D) :
    DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog :=
  I.l34.toZeroStrip line

/-- The Stark field remains derived from the Wave-33 block. -/
theorem stark_derived (I : PaperResidualFor35 line K ι N χ E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  I.l34.toStark line

/-- The old `zeroFree` field remains derived from the faithful data. -/
theorem zeroFree_derived (I : PaperResidualFor35 line K ι N χ E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz
      I.l34.discLog :=
  I.l34.toZeroFree line

/-- The L30 loss is exactly the H.3 failure probability and the L34 loss is
exactly the actual probe miss. -/
theorem losses (I : PaperResidualFor35 line K ι N χ E D) (n : ℕ) :
    (wave15L34Leaf
        (I.l34.toWave33L34Inputs line).toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
        I.l34.actualMiss n ∧
      I.l30.toSubexpLeaf.loss n = I.l30.failure.failure n :=
  ⟨I.l34.toWave33L34Inputs_loss_eq line n, Wave31L30Inputs.loss_eq I.l30 n⟩

end PaperResidualFor35

/-- **The schedule-indexed form of the Wave-35 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor35Schedule (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor35 line K ι N χ (E s) D

/-! ## 4. The E-generic endpoint -/

/-- **Wave-35 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K`, every explicit abelian factorization `ζ_K = ∏ L(·, χ)` away from the pole,
and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor35 line K ι N χ (E s) D` record, the kernel-checked
driver outputs a permutation of `n.primeFactorsList` and has expected
serialized bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The record carries **no `zeroStrip` hypothesis**: the strip packet is derived
from `line` and the factorization.  The remaining blocks are the Wave-31 L30
leaf, the Wave-33 faithful/stark-derived L34 data and the Wave-27 RH-only L21.2
leaf.  The epoch family `E` is quantified inside the conclusion. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave35Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
      (χ : ∀ i, DirichletCharacter ℂ (N i)),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor35 line K ι N χ (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave34Inputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF ι instF instDec N instN χ E hI
  exact hmain (K := K) E fun s D hvalid => (hI s D hvalid).toPaperResidualFor34

/-! ## 5. Residual accounting -/

/-- The field names of `Wave35L34Inputs`.  The strip packet `zeroStrip` is
absent; the two new fields are `factorization` and `half_le_beta0`. -/
def wave35L34FieldNames : List String :=
  ["beta0", "zeroRealPart", "degree", "discLog", "F", "T", "count",
   "inertCount", "degreeOneInert", "liX", "liBeta0", "pTrial", "actualMiss",
   "classCount", "R", "cz", "cz_pos", "zeroSeq", "zeroSeq_realPart",
   "zeroSeq_lt_one", "K", "C", "cZ", "cbr", "csel", "Ch", "range", "T_ge_one",
   "cheb", "inert_ge_count", "bracket", "error_scalar", "degree_loss_scalar",
   "degree_one_reduction", "selection", "budget", "classCount_pos", "classCubic",
   "constant_margin", "scale_cubic", "actualMiss_nonneg", "union_bound",
   "pTrial_nonneg", "pTrial_le_one", "starkF_pos", "beta0_le_half",
   "paperBeta0_ge_half", "factorization", "half_le_beta0"]

theorem wave35L34FieldNames_length : wave35L34FieldNames.length = 49 := rfl

/-- **`zeroStrip` is no longer a field of the L34 block.** -/
theorem wave35_no_zeroStrip_field :
    wave35L34FieldNames.all (fun s => decide (s ≠ "zeroStrip")) = true := by
  decide

/-- The two replacement fields are genuine fields. -/
theorem wave35_L34_replacement_fields :
    wave35L34FieldNames.contains "factorization" = true ∧
      wave35L34FieldNames.contains "half_le_beta0" = true :=
  ⟨by decide, by decide⟩

/-- The gone `zeroFree` and `stark` fields are still absent. -/
theorem wave35_no_zeroFree_no_stark_field :
    wave35L34FieldNames.all (fun s => decide (s ≠ "zeroFree")) = true ∧
      wave35L34FieldNames.all (fun s => decide (s ≠ "stark")) = true :=
  ⟨by decide, by decide⟩

/-- The field names of `PaperResidualFor35`; there is no `l18_4` field and the
L34 block itself has no `zeroStrip` field. -/
def wave35FieldNames : List String :=
  ["l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave35FieldNames_length : wave35FieldNames.length = 17 := rfl

/-- **The record no longer carries an L18.4 hypothesis.** -/
theorem wave35_no_l18_4 :
    wave35FieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- **The exact Wave-35 residual list.**  It is the Wave-34 list with
`zeroStrip` replaced by `factorization` and `half_le_beta0`. -/
def wave35RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "factorization", "zeroSeq", "zeroSeq_lt_one", "cheb", "range",
   "half_le_beta0", "beta0_le_half",
   "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

/-- The residual list literally is the displayed list. -/
theorem wave35RemainingFieldNames_exact :
    wave35RemainingFieldNames =
      ["zetaRH", "localCount", "hbuchstab", "hparity",
       "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
       "killMass", "curveBudget",
       "factorization", "zeroSeq", "zeroSeq_lt_one", "cheb", "range",
       "half_le_beta0", "beta0_le_half",
       "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"] :=
  rfl

theorem wave35RemainingFieldNames_length :
    wave35RemainingFieldNames.length = 26 := rfl

/-- **The Wave-35 residual list is exactly the Wave-34 list with `zeroStrip`
replaced by the factorization and the half-line arithmetic.** -/
theorem wave35RemainingFieldNames_eq_wave34_replace :
    wave35RemainingFieldNames.filter
        (fun s => decide (s ≠ "factorization") && decide (s ≠ "half_le_beta0")) =
      wave34RemainingFieldNames.filter (fun s => decide (s ≠ "zeroStrip")) := by
  decide

/-- **`zeroStrip` is no longer in the residual list.** -/
theorem wave35_no_zeroStrip_residual :
    wave35RemainingFieldNames.all (fun s => decide (s ≠ "zeroStrip")) = true := by
  decide

/-- **The residual list does not contain the L18.4 certificate entry.** -/
theorem wave35_no_l18_4_residual :
    wave35RemainingFieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- The residual list still does not contain the vacuous sequence-indexed
`zeroFree` field nor the Stark exceptional-zero field. -/
theorem wave35_no_zeroFree_no_stark_residual :
    wave35RemainingFieldNames.all (fun s => decide (s ≠ "zeroFree")) = true ∧
      wave35RemainingFieldNames.all (fun s => decide (s ≠ "stark")) = true :=
  ⟨by decide, by decide⟩

/-- The residual list contains the explicit Buchstab/parity, factorization,
half-line, faithful-sequence and remaining certificate entries. -/
theorem wave35_residual_blocks :
    wave35RemainingFieldNames.contains "hbuchstab" = true ∧
      wave35RemainingFieldNames.contains "hparity" = true ∧
      wave35RemainingFieldNames.contains "factorization" = true ∧
      wave35RemainingFieldNames.contains "half_le_beta0" = true ∧
      wave35RemainingFieldNames.contains "zeroSeq" = true ∧
      wave35RemainingFieldNames.contains "zeroSeq_lt_one" = true ∧
      wave35RemainingFieldNames.contains "beta0_le_half" = true ∧
      wave35RemainingFieldNames.contains "l19" = true ∧
      wave35RemainingFieldNames.contains "l20_2" = true ∧
      wave35RemainingFieldNames.contains "l20_4" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The complete remaining L30 analytic input** is the Buchstab large-prime
estimate together with the odd-half parity fraction. -/
theorem wave35_l30_remaining (I : PaperResidualFor35 line K ι N χ E D) :
    BuchstabLargePrimeShortIntervalLower I.l30.counts.c I.l30.counts.p
        I.l30.counts.ε ∧
      CentralOddHalfParity I.l30.counts.θ I.l30.counts.p I.l30.counts.ε :=
  ⟨I.l30.counts.hbuchstab, I.l30.counts.hparity⟩

/-- **The sharp central count is derived** with the effective constant
`θ * c`. -/
theorem wave35_l30_short_interval_derived
    (I : PaperResidualFor35 line K ι N χ E D) :
    YounisOddPaperSharpIntervalCount
      (I.l30.counts.θ * I.l30.counts.c) I.l30.counts.p I.l30.counts.ε :=
  I.l30.counts.short_interval

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave35_l21_remaining (I : PaperResidualFor35 line K ι N χ E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L34 analytic input is the factorization and the
half-line arithmetic**, with `zeroStrip` derived and the faithful sequence
retained. -/
theorem wave35_l34_remaining (I : PaperResidualFor35 line K ι N χ E D) :
    DedekindZetaFactorsIntoDirichletOffPole K ι N χ ∧
      (∀ n, 1 / 2 ≤ I.l34.beta0 n) ∧
      DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog ∧
      0 < I.l34.cz ∧
      (∀ n, I.l34.zeroRealPart n < 1) ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog ∧
      (∀ n, I.l34.beta0 n ≤ 1 / 2) :=
  ⟨I.l34.factorization, I.l34.half_le_beta0, I.zeroStrip_derived, I.l34.cz_pos,
    I.l34.zeroSeq_lt_one, I.l34.cheb, I.l34.range, I.l34.beta0_le_half⟩

/-- The sequence carries genuine zeros of `ζ_K` with the recorded real parts. -/
theorem wave35_l34_zeroSeq (I : PaperResidualFor35 line K ι N χ E D) :
    (∀ n, NumberField.dedekindZeta K (I.l34.zeroSeq.zero n) = 0) ∧
      I.l34.zeroSeq.realPart = I.l34.zeroRealPart :=
  ⟨I.l34.zeroSeq.isZero, I.l34.zeroSeq_realPart⟩

/-- On the half-line, `β₀` is exactly the critical line. -/
theorem wave35_l34_beta0_eq_half (I : PaperResidualFor35 line K ι N χ E D)
    (n : ℕ) : I.l34.beta0 n = 1 / 2 :=
  le_antisymm (I.l34.beta0_le_half n) (I.l34.half_le_beta0 n)

/-! ## Axiom audit -/

#print axioms Wave35L34Inputs.toZeroStrip
#print axioms Wave35L34Inputs.toWave33L34Inputs
#print axioms Wave35L34Inputs.toWave33L34Inputs_zeroStrip
#print axioms Wave35L34Inputs.toWave33L34Inputs_data
#print axioms Wave35L34Inputs.toWave33L34Inputs_loss_eq
#print axioms Wave35L34Inputs.toZeroFree
#print axioms Wave35L34Inputs.toStark
#print axioms wave35Slots
#print axioms wave35Slots_eq_wave34Slots
#print axioms PaperResidualFor35.toPaperResidualFor34
#print axioms PaperResidualFor35.toPaperResidualFor34_zeroStrip
#print axioms PaperResidualFor35.toPaperResidualFor34_loss_le
#print axioms PaperResidualFor35.toFullyDischargedInputs
#print axioms PaperResidualFor35.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor35.zeroStrip_derived
#print axioms PaperResidualFor35.stark_derived
#print axioms PaperResidualFor35.zeroFree_derived
#print axioms PaperResidualFor35.losses
#print axioms PaperResidualFor35Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave35Inputs
#print axioms wave35L34FieldNames_length
#print axioms wave35_no_zeroStrip_field
#print axioms wave35_L34_replacement_fields
#print axioms wave35_no_zeroFree_no_stark_field
#print axioms wave35FieldNames_length
#print axioms wave35_no_l18_4
#print axioms wave35RemainingFieldNames_exact
#print axioms wave35RemainingFieldNames_length
#print axioms wave35RemainingFieldNames_eq_wave34_replace
#print axioms wave35_no_zeroStrip_residual
#print axioms wave35_no_l18_4_residual
#print axioms wave35_no_zeroFree_no_stark_residual
#print axioms wave35_residual_blocks
#print axioms wave35_l30_remaining
#print axioms wave35_l30_short_interval_derived
#print axioms wave35_l21_remaining
#print axioms wave35_l34_remaining
#print axioms wave35_l34_zeroSeq
#print axioms wave35_l34_beta0_eq_half

end Cogentic.RandomizedPaperEndpointWave35
