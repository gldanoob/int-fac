import Cogentic.RandomizedPaperEndpointWave29
import Cogentic.RandomizedL34ZeroFaithful

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 30: the vacuous sequence-indexed zero-free field is replaced by the
faithful strip packet

The Wave-28 L34 record `Wave28L34Inputs` still carried

```
zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog,
```

which is only a statement about the *chosen* sequence of real parts: since
`ZetaZeroSequence` has no completeness field, the sequence can simply omit every
inconvenient zero.  `Cogentic.RandomizedL34ZeroFaithful` isolated this failure
and supplied the faithful interfaces.

This file replaces the field by the faithful packet.  The L34 block
`Wave30L34Inputs K` (for a number field `K`) keeps every Wave-28 data field and
replaces `zeroFree` by

* `cz_pos : 0 < cz` (the positivity half of the old field),
* `zeroStrip : DedekindZetaStripInput K beta0 cz discLog` — the **all-zeros**
  strip packet, and
* a genuine zero sequence `zeroSeq : ZetaZeroSequence (ζ_K)` with
  `zeroSeq.realPart = zeroRealPart` and the nontriviality condition
  `∀ n, zeroRealPart n < 1`, which excludes Mathlib's junk value `ζ_K 1 = 0`.

## What is proved

1. **Faithful implies the old field.**
   `Wave30L34Inputs.toZeroFree` derives
   `DedekindZeroFreeInput beta0 zeroRealPart cz discLog` from the faithful
   packet.  For indices with `β₀ n < Re ρ n` the sequence condition supplies
   `Re ρ n < 1`, so the all-zeros strip gives the bound; indices with
   `Re ρ n ≤ β₀ n` are vacuous.  No half-plane and no completeness are needed.

2. **The faithful packet is consistent.**
   `faithfulZeroPacket_satisfiable` exhibits a model of the replaced fields
   (with an `f` that vanishes everywhere, including at the junk point `1`) using
   a constant sequence at `0`; `zeroFunction_lt_one_sequence_misses_one` shows
   that the sequence omits the zero `1`, which is exactly why the junk value is
   harmless.  Conversely,
   `completeZetaZeroSequence_not_lt_one_of_junk_one` shows that a *complete*
   sequence can never satisfy `∀ n, r n < 1` when `ζ_K 1 = 0`, so the design
   deliberately keeps the incomplete `ZetaZeroSequence` and puts the honest
   all-zeros content in `zeroStrip`.

3. **The Wave-30 record and endpoint.**
   `PaperResidualFor30 K E D` is the Wave-29 record with `l34` replaced by
   `Wave30L34Inputs K`; `PaperResidualFor30.toPaperResidualFor29` transports it
   back (the ledger only reads the actual probe miss), and

   `serialized_assembled_balancedEnvelopeInfimum_from_wave30Inputs`

   is the E-generic (and now K-generic) endpoint.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-free claim is used: the
strip packet is a hypothesis of the record, never a theorem about `ζ_K`.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave30

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
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34Dedekind
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
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## 1. The faithful strip packet implies the old sequence field -/

/-- **The faithful all-zeros packet, together with `Re < 1` on the sequence,
gives the old sequence-indexed input.**  On the strip `β₀ < Re < 1` the
all-zeros packet gives the bound; on `Re ≤ β₀` the implication is vacuous.  The
`Re < 1` hypothesis is supplied by the sequence property rather than by a
half-plane, so no half-plane residual is needed. -/
theorem dedekindZeroFreeInput_of_strip_of_lt_one
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZeroFreeInputComplete f beta0 cz discLog)
    (Z : ZetaZeroSequence f) (hZ : ∀ n, Z.realPart n < 1) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog := by
  refine
    { cz_pos := C.cz_pos
      above_beta := DedekindZeroFreeAboveBetaStrip.toAboveBeta
        (C.toAboveBetaStrip Z) (fun n _ => hZ n) }

/-- The variant where the strip packet is stated as `DedekindZetaStripInput`
together with the positivity of `cz`. -/
theorem dedekindZeroFreeInput_of_zetaStrip_of_lt_one
    (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} (hcz : 0 < cz)
    (hstrip : DedekindZetaStripInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (hZ : ∀ n, Z.realPart n < 1) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog :=
  dedekindZeroFreeInput_of_strip_of_lt_one
    (⟨hcz, hstrip⟩ : DedekindZeroFreeInputComplete
      (NumberField.dedekindZeta K) beta0 cz discLog) Z hZ

/-! ## 2. The Wave-30 L34 block -/

/-- **The Wave-30 L34 inputs.**  Every Wave-28 data field is kept verbatim; the
vacuous field

```
zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog
```

is replaced by the faithful packet:

* `cz_pos` — positivity of the zero-free constant,
* `zeroStrip` — the all-zeros `DedekindZetaStripInput K beta0 cz discLog`,
* `zeroSeq` and `zeroSeq_realPart` — a genuine zero sequence of `ζ_K` whose
  real parts are the recorded `zeroRealPart`, and
* `zeroSeq_lt_one` — every recorded zero has real part `< 1` (so the junk value
  `ζ_K 1 = 0` cannot occur in the sequence).

The field named `K : ℝ` below is the Wave-28 range constant; the number field
is the structure parameter `K`.  The faithful fields are declared before the
range constant so that `K` in their types means the number field. -/
structure Wave30L34Inputs (K : Type u) [Field K] [NumberField K] where
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
  /-- The zero-free-region constant is positive.  (This is the `cz_pos` half of
  the removed field, not a new analytic input.) -/
  cz_pos : 0 < cz
  /-- **The faithful zero-free packet**: every zero of `ζ_K` in the strip
  `β₀ < Re < 1` lies on the zero-free side.  This quantifies over *all* zeros,
  unlike the removed sequence-indexed field. -/
  zeroStrip : DedekindZetaStripInput K beta0 cz discLog
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

namespace Wave30L34Inputs

variable {K : Type u} [Field K] [NumberField K]

/-- **The original sequence-indexed zero-free field, derived faithfully.**  The
strip packet covers the nonzero branch and the sequence condition `Re < 1`
covers the `Re ≥ 1` branch; this is exactly the replacement of the removed
`zeroFree` field. -/
theorem toZeroFree (S : Wave30L34Inputs K) :
    DedekindZeroFreeInput S.beta0 S.zeroRealPart S.cz S.discLog := by
  have hC : DedekindZeroFreeInputComplete (NumberField.dedekindZeta K) S.beta0
      S.cz S.discLog :=
    ⟨S.cz_pos, S.zeroStrip⟩
  have hstrip := hC.toAboveBetaStrip S.zeroSeq
  have hstrip' : DedekindZeroFreeAboveBetaStrip S.beta0 S.zeroRealPart S.cz
      S.discLog := by
    intro n h1 h2
    have h1' : S.beta0 n < S.zeroSeq.realPart n := by
      rw [S.zeroSeq_realPart]; exact h1
    have h2' : S.zeroSeq.realPart n < 1 := by
      rw [S.zeroSeq_realPart]; exact h2
    have h := hstrip n h1' h2'
    rwa [S.zeroSeq_realPart] at h
  exact
    { cz_pos := S.cz_pos
      above_beta := DedekindZeroFreeAboveBetaStrip.toAboveBeta hstrip'
        (fun n _ => S.zeroSeq_lt_one n) }

/-- **The Wave-28 L34 record, with the faithful packet decoded.**  Every data
field is passed through; only the removed `zeroFree` field is reconstructed by
`toZeroFree`. -/
noncomputable def toWave28L34Inputs (S : Wave30L34Inputs K) :
    Wave28L34Inputs where
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
  K := S.K
  C := S.C
  cZ := S.cZ
  cz := S.cz
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  zeroFree := S.toZeroFree
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

/-- **The transported `zeroFree` field is the derived one**, not an assumption. -/
theorem toWave28L34Inputs_zeroFree (S : Wave30L34Inputs K) :
    S.toWave28L34Inputs.zeroFree = S.toZeroFree := rfl

/-- The transport leaves the data fields unchanged. -/
theorem toWave28L34Inputs_data (S : Wave30L34Inputs K) :
    S.toWave28L34Inputs.beta0 = S.beta0 ∧
      S.toWave28L34Inputs.zeroRealPart = S.zeroRealPart ∧
      S.toWave28L34Inputs.discLog = S.discLog ∧
      S.toWave28L34Inputs.cz = S.cz ∧
      S.toWave28L34Inputs.actualMiss = S.actualMiss ∧
      S.toWave28L34Inputs.R = S.R :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The transported L34 loss is still exactly the actual probe miss. -/
theorem toWave28L34Inputs_loss_eq (S : Wave30L34Inputs K) (n : ℕ) :
    (wave15L34Leaf S.toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
      S.actualMiss n :=
  wave15L34Leaf_loss_eq S.toWave28L34Inputs.toL34ChebotarevSidesInputs n

end Wave30L34Inputs

/-! ## 3. The faithful packet is not refuted -/

/-- **A zero below `1` produces a sequence whose real parts are all below `1`.**
This is the sequence-property constructor: no completness is needed, and the
sequence may omit any zero (in particular a junk value at `1`). -/
theorem exists_zetaZeroSequence_realPart_lt_one {f : ℂ → ℂ} {z : ℂ}
    (hz : f z = 0) (hlt : z.re < 1) :
    ∃ Z : ZetaZeroSequence f, ∀ n, Z.realPart n < 1 :=
  ⟨constantZeroSequence f z hz, fun _ => hlt⟩

/-- **The sequence condition is satisfiable even when the function has a zero
at `1`.**  The identically-zero function is the extreme case: every point,
including `1`, is a zero, yet the constant sequence at `0` has real parts below
`1`. -/
theorem zeroFunction_exists_zetaZeroSequence_lt_one :
    ∃ Z : ZetaZeroSequence zeroFunction, ∀ n, Z.realPart n < 1 :=
  exists_zetaZeroSequence_realPart_lt_one (f := zeroFunction) (z := 0) rfl (by norm_num)

/-- **The same sequence omits the junk zero `1`.**  This is precisely the
incompleteness that makes `∀ n, r n < 1` consistent with `f 1 = 0`. -/
theorem zeroFunction_lt_one_sequence_misses_one :
    ∃ Z : ZetaZeroSequence zeroFunction,
      (∀ n, Z.realPart n < 1) ∧ zeroFunction 1 = 0 ∧ ¬ ∃ n, Z.zero n = 1 := by
  refine ⟨constantZeroSequence zeroFunction 0 rfl, ?_, rfl, ?_⟩
  · intro n
    simp [constantZeroSequence]
  · rintro ⟨n, hn⟩
    have h : (0 : ℂ) = 1 := by simpa only [constantZeroSequence] using hn
    norm_num at h

/-- **A complete zero sequence cannot satisfy `∀ n, r n < 1` when `ζ_K 1 = 0`.**
This is exactly the junk-value obstruction: completeness would force the junk
zero `1` into the sequence, violating the strict inequality.  The Wave-30 block
therefore keeps the incomplete `ZetaZeroSequence` and states the honest content
in `zeroStrip`. -/
theorem completeZetaZeroSequence_not_lt_one_of_junk_one
    {K : Type*} [Field K] [NumberField K]
    (h1 : NumberField.dedekindZeta K 1 = 0)
    (Z : CompleteZetaZeroSequence (NumberField.dedekindZeta K)) :
    ¬ ∀ n, Z.realPart n < 1 := by
  intro h
  obtain ⟨n, hn⟩ := Z.complete 1 h1
  have hre : Z.realPart n = 1 := by
    rw [Z.realPart_eq n, hn]
    norm_num
  linarith [h n]

/-- **Dropping `Re < 1` would break the old field at the junk index.**  If the
sequence contains the point `1` and `β₀ n < 1`, `cz > 0`, `log |Δ| n > 0`, then
the sequence-indexed input is false.  This shows the `zeroSeq_lt_one` field is
not cosmetic. -/
theorem not_dedekindZeroFreeInput_of_zero_eq_one
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} {n : ℕ}
    (h1 : Z.zero n = 1) (hβ : beta0 n < 1) (hcz : 0 < cz) (hd : 0 < discLog n) :
    ¬ DedekindZeroFreeInput beta0 Z.realPart cz discLog := by
  intro h
  have hre : Z.realPart n = 1 := by
    rw [Z.realPart_eq n, h1]
    norm_num
  have hb : beta0 n < Z.realPart n := by
    rw [hre]
    exact hβ
  have hle := h.above_beta n hb
  rw [hre] at hle
  have hpos : 0 < cz / discLog n := div_pos hcz hd
  linarith

/-- **The replaced faithful packet is jointly satisfiable.**  There is a model
with `β₀ = 1`, `cz = 1`, `log|Δ| = 1`, an all-zeros strip packet, a genuine
zero sequence at `0` (so `zeroRealPart = 0`), the sequence property
`0 < 1`, and the resulting `DedekindZeroFreeInput`.  The function is the
identically-zero function, so its zero set contains `1`; the sequence omits it,
just as it omits the junk value of `ζ_K`.  Hence the new fields are consistent
and do not encode a contradiction. -/
theorem faithfulZeroPacket_satisfiable :
    ∃ (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) (r : ℕ → ℝ),
      0 < cz ∧
      DedekindZeroFreeInputComplete zeroFunction beta0 cz discLog ∧
      (∃ Z : ZetaZeroSequence zeroFunction, Z.realPart = r) ∧
      (∀ n, r n < 1) ∧
      DedekindZeroFreeInput beta0 r cz discLog := by
  refine ⟨fun _ => 1, 1, fun _ => 1, fun _ => 0, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact ⟨by norm_num, fun n s _ hb hlt => by linarith⟩
  · exact ⟨constantZeroSequence zeroFunction 0 rfl, rfl⟩
  · intro n
    norm_num
  · refine { cz_pos := by norm_num, above_beta := ?_ }
    intro n hb
    linarith

/-! ## 4. The Wave-30 ledger and residual record -/

/-- **The Wave-30 ledger.**  It is the Wave-29 ledger at the Wave-28 record
obtained by decoding the faithful packet (`toWave28L34Inputs`).  The L34 leaf
reads only the actual probe miss, which is unchanged. -/
noncomputable def wave30Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
    l34.toWave28L34Inputs p1

/-- The Wave-30 ledger is definitionally the Wave-29 ledger at the decoded
faithful packet. -/
theorem wave30Slots_eq_wave29Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave30Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave28L34Inputs p1 := rfl

/-- The L34 loss of the Wave-30 ledger is exactly the actual probe miss. -/
theorem wave30Slots_l34_loss_eq {K : Type u} [Field K] [NumberField K]
    (l34 : Wave30L34Inputs K) (n : ℕ) :
    (wave15L34Leaf l34.toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
      l34.actualMiss n :=
  l34.toWave28L34Inputs_loss_eq n

/-- **The Wave-30 E-generic residual record.**  It is the Wave-29 record with
`l34 : Wave28L34Inputs` replaced by `l34 : Wave30L34Inputs K`, whose zero-free
field is the faithful strip packet rather than the vacuous sequence index.  All
other fields are copied verbatim. -/
structure PaperResidualFor30 (K : Type u) [Field K] [NumberField K]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
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
  /-- **L30 with both density fields derived**. -/
  l30 : Wave26L30Inputs
  /-- **L34 with the faithful zero-free strip packet**, the genuine zero
  sequence and the nontriviality condition `Re < 1`. -/
  l34 : Wave30L34Inputs K
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
  /-- Adapter: the concrete C5 loss is dominated by the wave-30 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave30Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor30

variable {K : Type u} [Field K] [NumberField K]
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor30 K E D → PaperResidualFor29 E D`.**  The L34 block is
decoded by `toWave28L34Inputs`; the ledger is definitionally the Wave-29 ledger,
so the C5 loss adapter transfers unchanged. -/
noncomputable def toPaperResidualFor29 (I : PaperResidualFor30 K E D) :
    PaperResidualFor29 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34.toWave28L34Inputs
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
    simpa only [wave30Slots] using I.loss_le n hN

/-- The transport replaces only the L34 block. -/
theorem toPaperResidualFor29_l34 (I : PaperResidualFor30 K E D) :
    (I.toPaperResidualFor29).l34 = I.l34.toWave28L34Inputs := rfl

/-- The transported `zeroFree` field is derived from the faithful packet. -/
theorem toPaperResidualFor29_l34_zeroFree (I : PaperResidualFor30 K E D) :
    (I.toPaperResidualFor29).l34.zeroFree = I.l34.toZeroFree := rfl

/-- The transport keeps the L21 and L30 blocks. -/
theorem toPaperResidualFor29_l21_l30 (I : PaperResidualFor30 K E D) :
    (I.toPaperResidualFor29).l21 = I.l21 ∧
      (I.toPaperResidualFor29).l30 = I.l30 :=
  ⟨rfl, rfl⟩

/-- The transport leaves the actual probe miss unchanged. -/
theorem toPaperResidualFor29_l34_actualMiss (I : PaperResidualFor30 K E D) :
    (I.toPaperResidualFor29).l34.actualMiss = I.l34.actualMiss := rfl

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor30 K E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toPaperResidualFor29.toFullyDischargedInputs⟩

end PaperResidualFor30

/-- **The schedule-indexed form of the Wave-30 record.** -/
abbrev PaperResidualFor30Schedule (K : Type u) [Field K] [NumberField K]
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor30 K (E s) D

/-! ## 5. The E-generic endpoint -/

/-- **Wave-30 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K` and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor30 K (E s) D` record, the kernel-checked driver
outputs a permutation of `n.primeFactorsList` and has expected serialized bit
cost eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The L34 block of the record now carries the faithful zero-free packet: the
all-zeros Dedekind strip input, a genuine zero sequence of `ζ_K`, and the
nontriviality condition `Re < 1`.  The vacuous `DedekindZeroFreeInput` field is
*derived*, not assumed. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave30Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor30 K (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave29Inputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF E hI
  exact hmain E fun s D hvalid => (hI s D hvalid).toPaperResidualFor29

/-! ## 6. Residual accounting -/

/-- The field names of `Wave30L34Inputs`.  The vacuous `zeroFree` field is
absent; the four added fields are `cz_pos`, `zeroStrip`, `zeroSeq` and the
sequence properties `zeroSeq_realPart`, `zeroSeq_lt_one`. -/
def wave30L34FieldNames : List String :=
  ["beta0", "zeroRealPart", "degree", "discLog", "F", "T", "count",
   "inertCount", "degreeOneInert", "liX", "liBeta0", "pTrial", "actualMiss",
   "classCount", "R", "cz", "cz_pos", "zeroStrip", "zeroSeq",
   "zeroSeq_realPart", "zeroSeq_lt_one", "K", "C", "cZ", "cbr", "csel", "Ch",
   "range", "T_ge_one", "cheb", "inert_ge_count", "bracket", "error_scalar",
   "degree_loss_scalar", "degree_one_reduction", "selection", "budget",
   "classCount_pos", "classCubic", "constant_margin", "scale_cubic",
   "actualMiss_nonneg", "union_bound", "pTrial_nonneg", "pTrial_le_one",
   "starkF_pos", "beta0_le_half", "paperBeta0_ge_half"]

theorem wave30L34FieldNames_length : wave30L34FieldNames.length = 48 := rfl

/-- **There is no vacuous `zeroFree` field in the Wave-30 L34 record.** -/
theorem wave30L34_no_zeroFree_field :
    wave30L34FieldNames.all (fun s => decide (s ≠ "zeroFree")) = true := by
  decide

/-- The field names of `PaperResidualFor30`. -/
def wave30FieldNames : List String :=
  ["l18_4", "l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave30FieldNames_length : wave30FieldNames.length = 18 := rfl

/-- **The exact combined residual list (analytic fields only).**  Compared with
Wave 29, the single `zeroFree` entry is replaced by the faithful components
`zeroStrip` (all-zeros Dedekind strip), `zeroSeq` (a genuine zero sequence) and
`zeroSeq_lt_one` (the nontriviality condition excluding the junk zero at `1`).
The number field `K` is a parameter of the record, not a residual. -/
def wave30RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "short_interval",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "zeroStrip", "zeroSeq", "zeroSeq_lt_one", "cheb", "range", "beta0_le_half",
   "l18_4", "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

theorem wave30RemainingFieldNames_length :
    wave30RemainingFieldNames.length = 25 := rfl

variable {K : Type u} [Field K] [NumberField K]
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The complete remaining L34 analytic input is the faithful packet**, not
the vacuous sequence field. -/
theorem wave30_l34_remaining (I : PaperResidualFor30 K E D) :
    DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog ∧
      0 < I.l34.cz ∧
      (∀ n, I.l34.zeroRealPart n < 1) ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog ∧
      (∀ n, I.l34.beta0 n ≤ 1 / 2) :=
  ⟨I.l34.zeroStrip, I.l34.cz_pos, I.l34.zeroSeq_lt_one, I.l34.cheb,
    I.l34.range, I.l34.beta0_le_half⟩

/-- The sequence carries genuine zeros of `ζ_K` with the recorded real parts. -/
theorem wave30_l34_zeroSeq (I : PaperResidualFor30 K E D) :
    (∀ n, NumberField.dedekindZeta K (I.l34.zeroSeq.zero n) = 0) ∧
      I.l34.zeroSeq.realPart = I.l34.zeroRealPart :=
  ⟨I.l34.zeroSeq.isZero, I.l34.zeroSeq_realPart⟩

/-- **The old zero-free field is derived from the faithful packet.** -/
theorem wave30_l34_zeroFree_derived (I : PaperResidualFor30 K E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz I.l34.discLog :=
  I.l34.toZeroFree

/-- The L34 loss of the record is exactly the actual probe miss. -/
theorem wave30_l34_loss (I : PaperResidualFor30 K E D) (n : ℕ) :
    (wave15L34Leaf I.l34.toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
      I.l34.actualMiss n :=
  wave30Slots_l34_loss_eq I.l34 n

/-- The faithful packet implies the Wave-29 L34 analytic residual with the
derived `zeroFree`. -/
theorem wave29_l34_remaining_of_wave30 (I : PaperResidualFor30 K E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz I.l34.discLog ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog ∧
      (∀ n, I.l34.beta0 n ≤ 1 / 2) :=
  wave29_l34_remaining I.toPaperResidualFor29

/-! ## Axiom audit -/

#print axioms dedekindZeroFreeInput_of_strip_of_lt_one
#print axioms dedekindZeroFreeInput_of_zetaStrip_of_lt_one
#print axioms Wave30L34Inputs.toZeroFree
#print axioms Wave30L34Inputs.toWave28L34Inputs
#print axioms Wave30L34Inputs.toWave28L34Inputs_zeroFree
#print axioms Wave30L34Inputs.toWave28L34Inputs_data
#print axioms Wave30L34Inputs.toWave28L34Inputs_loss_eq
#print axioms exists_zetaZeroSequence_realPart_lt_one
#print axioms zeroFunction_exists_zetaZeroSequence_lt_one
#print axioms zeroFunction_lt_one_sequence_misses_one
#print axioms completeZetaZeroSequence_not_lt_one_of_junk_one
#print axioms not_dedekindZeroFreeInput_of_zero_eq_one
#print axioms faithfulZeroPacket_satisfiable
#print axioms wave30Slots
#print axioms wave30Slots_eq_wave29Slots
#print axioms wave30Slots_l34_loss_eq
#print axioms PaperResidualFor30.toPaperResidualFor29
#print axioms PaperResidualFor30.toPaperResidualFor29_l34
#print axioms PaperResidualFor30.toPaperResidualFor29_l34_zeroFree
#print axioms PaperResidualFor30.toPaperResidualFor29_l21_l30
#print axioms PaperResidualFor30.toPaperResidualFor29_l34_actualMiss
#print axioms PaperResidualFor30.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor30Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave30Inputs
#print axioms wave30L34FieldNames_length
#print axioms wave30L34_no_zeroFree_field
#print axioms wave30FieldNames_length
#print axioms wave30RemainingFieldNames_length
#print axioms wave30_l34_remaining
#print axioms wave30_l34_zeroSeq
#print axioms wave30_l34_zeroFree_derived
#print axioms wave30_l34_loss
#print axioms wave29_l34_remaining_of_wave30

end Cogentic.RandomizedPaperEndpointWave30
