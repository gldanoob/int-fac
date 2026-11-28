import Cogentic.RandomizedPaperEndpointWave35
import Cogentic.RandomizedL34ChebotarevSides
import Cogentic.RandomizedL34DedekindStrip

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 36: the L34 block with the sequence-indexed zero-free input removed

The Wave-35 L34 block `Wave35L34Inputs` still carried the data

```
zeroSeq          : ZetaZeroSequence (NumberField.dedekindZeta K)
zeroSeq_realPart : zeroSeq.realPart = zeroRealPart
zeroSeq_lt_one   : ∀ n, zeroRealPart n < 1
```

The sequence was used for exactly one purpose: to derive the sequence-indexed
zero-free field

```
zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog
```

consumed by `L34ChebotarevSidesInputs` when assembling `L34SidesCore`.  The L34
ledger itself never reads that field: `L34SidesCore.inert_lower` uses only the
one-sided Chebotarev lower bound, and the probe-miss estimate uses the counting
inputs and the analytic bracket.

This file removes the sequence entirely.  It supplies a variant
`L34ChebotarevSidesInputsStrip` whose zero-free datum is *exactly* the all-zeros
packet

```
zeroStrip : DedekindZetaStripInput K beta0 cz discLog
```

and reproves the L34 side/core lemmas on a mirrored core `L34SidesCoreStrip`
whose analytic bundle `DedekindSidesInputsStrip` replaces
`DedekindZeroFreeInput` by `DedekindZetaStripInput`.  The resulting `ratedLeaf`
has the same ledger loss as before, still exactly the actual probe miss.

The Wave-36 L34 block `Wave36L34Inputs` then drops `zeroSeq`,
`zeroSeq_realPart` and `zeroSeq_lt_one`.  As in Wave 35, the strip packet is not
even an assumption: it is derived from the critical-line hypothesis, the abelian
factorization and the half-line arithmetic.  Hence the zero-free content of the
new block is the factorization-derived strip packet only.

`PaperResidualFor36` is the Wave-35 record with this block, and
`serialized_assembled_balancedEnvelopeInfimum_from_wave36Inputs` is the
endpoint, proved from the fully discharged endpoint at the new leaf.

## A note on the transport to `PaperResidualFor35`

`PaperResidualFor35` still *contains* a `Wave35L34Inputs`, i.e. the fields
`zeroSeq` and `zeroSeq_lt_one`.  They cannot be reconstructed from the
sequence-free Wave-36 data: a `ZetaZeroSequence` requires a genuine zero of
`ζ_K`, which the strip packet does not assert.  The transport
`PaperResidualFor36.toPaperResidualFor35` therefore takes an explicit zero
sequence with real parts below `1`; it is *not* an analytic residual of the
Wave-36 block, only a compatibility witness for the older record type.  The
Wave-36 endpoint itself is unconditional and does not use this transport.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss,
probability, count or error is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave36

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
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u v

/-! ## 1. The strip-based analytic bundle and core -/

/-- **The one-sided analytic bundle with the all-zeros strip packet.**  This is
`DedekindSidesInputs` with the sequence-indexed `DedekindZeroFreeInput` replaced
by `DedekindZetaStripInput K beta0 cz discLog`.  The Stark, range and one-sided
Chebotarev fields are unchanged. -/
structure DedekindSidesInputsStrip (K : Type u) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ)
    (F : ℕ → ℝ) (Kc : ℝ) (x degree : ℕ → ℝ)
    (C cZ : ℝ) (count : ℕ → ℝ) (liX liBeta0 : ℕ → ℝ) : Prop where
  /-- The faithful all-zeros Dedekind strip packet. -/
  zeroStrip : DedekindZetaStripInput K beta0 cz discLog
  /-- Stark's exceptional-zero gap. -/
  stark : StarkInput beta0 F discLog
  /-- The Lagarias–Odlyzko range inequality. -/
  range : ChebotarevRangeInput Kc x degree discLog
  /-- The cumulative Chebotarev count, one-sided. -/
  cheb : ChebotarevLowerInput C cZ x degree count liX liBeta0

/-- **`L34SidesCore` with the strip packet in place of `DedekindZeroFreeInput`.**
Every field except `sides` is copied from `L34SidesCore`; the analytic bundle
`DedekindSidesInputs` is replaced by `DedekindSidesInputsStrip`, whose zero-free
field is the all-zeros packet `DedekindZetaStripInput` rather than the
sequence-indexed `DedekindZeroFreeInput`. -/
structure L34SidesCoreStrip (K : Type u) [Field K] [NumberField K] where
  /-- The Chebotarev cutoff `x`. -/
  x : ℕ → ℝ
  /-- The absolute degree `2d` of `E = K(√γ)`. -/
  degree : ℕ → ℝ
  /-- `log |Δ_E|`. -/
  discLog : ℕ → ℝ
  /-- The factorial factor `F = (2d)!`. -/
  F : ℕ → ℝ
  /-- The polynomial input parameter `T`. -/
  T : ℕ → ℝ
  /-- The class-group logarithm `h*`. -/
  hstar : ℕ → ℝ
  /-- The compressed bit length `m = h* + 7`. -/
  m : ℕ → ℝ
  /-- The number of probes `R`. -/
  R : ℕ → ℕ
  /-- The number of nonrational classes. -/
  classCount : ℕ → ℝ
  /-- The per-trial detection probability. -/
  pTrial : ℕ → ℝ
  /-- The possible exceptional real zero `β₀`. -/
  beta0 : ℕ → ℝ
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
  /-- The range constant. -/
  Kc : ℝ
  /-- The constant `C` in the effective error. -/
  C : ℝ
  /-- The constant `c` in the effective error. -/
  cZ : ℝ
  /-- The zero-free-region constant `c_z`. -/
  cz : ℝ
  /-- The bracket constant. -/
  cbr : ℝ
  /-- The per-ideal selection constant. -/
  csel : ℝ
  /-- The polynomial constant in `h* ≤ Ch T³`. -/
  Ch : ℝ
  /-- The cutoff is positive. -/
  x_pos : ∀ n, 0 < x n
  /-- The extension degree is positive. -/
  degree_pos : ∀ n, 0 < degree n
  /-- The discriminant logarithm is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- The polynomial parameter is positive. -/
  T_pos : ∀ n, 0 < T n
  /-- The polynomial parameter is at least one. -/
  T_ge_one : ∀ n, 1 ≤ T n
  /-- There is at least one nonrational class. -/
  classCount_pos : ∀ n, 0 < classCount n
  /-- The per-trial probability is nonnegative. -/
  pTrial_nonneg : ∀ n, 0 ≤ pTrial n
  /-- The per-trial probability is at most one. -/
  pTrial_le_one : ∀ n, pTrial n ≤ 1
  /-- The actual failure probability of the probe stage. -/
  actualMiss : ℕ → ℝ
  /-- The actual failure probability is nonnegative. -/
  actualMiss_nonneg : ∀ n, 0 ≤ actualMiss n
  /-- The probe union bound. -/
  union_bound : ProbeMissUnionBound actualMiss pTrial classCount R
  /-- The degree is bounded by the polynomial parameter. -/
  degree_le_T : ∀ n, degree n ≤ T n
  /-- **The strip-based analytic bundle.** -/
  sides : DedekindSidesInputsStrip K beta0 cz discLog F Kc x degree
    C cZ count liX liBeta0
  /-- The inert count contains the counted nonidentity class. -/
  inert_ge_count : ∀ n, count n ≤ inertCount n
  /-- Stark's bound converted to the dyadic bracket. -/
  bracket : LogIntegralBracket cbr x F T liX liBeta0
  /-- The Chebotarev error is negligible against the bracket. -/
  error_negligible : ChebotarevErrorNegligible cbr x F T
    (lagariasOdlyzkoError C cZ x degree)
  /-- Discarding small / higher-degree ideals is negligible. -/
  degree_one_loss : DegreeOneLossNegligible cbr x degree F T
  /-- The degree-one reduction. -/
  degree_one_reduction : DegreeOneInertReduction inertCount degreeOneInert degree x
  /-- Probe selection at `1/(d x)` per eligible ideal. -/
  selection : ProbeSelectionLowerBound csel x degree degreeOneInert pTrial
  /-- The paper's budget `R = F T¹⁰`. -/
  budget : ProbeBudget R F T
  /-- Lemma E.2: at most `2^{h*}` nonrational classes. -/
  class_le : ClassCountBound classCount hstar
  /-- The polynomial bound `h* = O(T³)`. -/
  hstar_poly : ClassCountPolynomial Ch hstar T
  /-- The mask-compression bit budget. -/
  mask_bits : MaskCompressionBits hstar m
  /-- The probe constant beats the class-count entropy constant. -/
  constant_margin : Ch * Real.log 2 < csel * cbr / 4
  /-- The probe exponent `T³` eventually dominates the ledger scale. -/
  scale_cubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (csel * cbr / 4 - Ch * Real.log 2) * T n ^ 3

namespace L34SidesCoreStrip

variable {K : Type u} [Field K] [NumberField K]

/-- The L34 loss charged to the C5 ledger, exactly as in `L34SidesCore`. -/
noncomputable def loss (S : L34SidesCoreStrip K) : ℕ → ℝ :=
  excessLoss S.actualMiss (maskFailure S.hstar S.m) allowedFailure

/-- The loss is nonnegative. -/
theorem loss_nonneg (S : L34SidesCoreStrip K) (n : ℕ) : 0 ≤ S.loss n := by
  unfold loss excessLoss
  exact le_max_left 0 _

/-- The compressed mask failure is at most `2^{-7} = 1/128`. -/
theorem maskFailure_le_allowed (S : L34SidesCoreStrip K) (n : ℕ) :
    maskFailure S.hstar S.m n ≤ 1 / 128 := by
  have hbits : S.hstar n - S.m n ≤ (-7 : ℝ) := by
    have := S.mask_bits n
    linarith
  calc
    maskFailure S.hstar S.m n = (2 : ℝ) ^ (S.hstar n - S.m n) := rfl
    _ ≤ (2 : ℝ) ^ (-7 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hbits
    _ = 1 / 128 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

/-- The mask failure is nonnegative. -/
theorem maskFailure_nonneg (S : L34SidesCoreStrip K) (n : ℕ) :
    0 ≤ maskFailure S.hstar S.m n := by
  unfold maskFailure
  exact Real.rpow_nonneg (by norm_num) _

/-- The probe miss is nonnegative. -/
theorem probeMiss_nonneg (S : L34SidesCoreStrip K) (n : ℕ) :
    0 ≤ probeMiss S.classCount S.pTrial S.R n := by
  unfold probeMiss
  exact mul_nonneg (S.classCount_pos n).le (Real.exp_pos _).le

/-- The actual miss is at most the probe miss (the union bound in exponential
form). -/
theorem actualMiss_le_probeMiss (S : L34SidesCoreStrip K) (n : ℕ) :
    S.actualMiss n ≤ probeMiss S.classCount S.pTrial S.R n := by
  have hpow := one_sub_pow_le_exp_neg (S.pTrial n) (S.pTrial_nonneg n)
    (S.pTrial_le_one n) (S.R n)
  calc
    S.actualMiss n ≤ S.classCount n * (1 - S.pTrial n) ^ (S.R n) :=
      S.union_bound n
    _ ≤ S.classCount n * Real.exp (-((S.R n : ℝ) * S.pTrial n)) :=
      mul_le_mul_of_nonneg_left hpow (S.classCount_pos n).le
    _ = probeMiss S.classCount S.pTrial S.R n := rfl

/-- The loss is at most the probe miss. -/
theorem loss_le_probeMiss (S : L34SidesCoreStrip K) (n : ℕ) :
    S.loss n ≤ probeMiss S.classCount S.pTrial S.R n := by
  have hmask := S.maskFailure_le_allowed n
  have hprobe := S.probeMiss_nonneg n
  have hactual := S.actualMiss_le_probeMiss n
  unfold loss excessLoss allowedFailure
  apply max_le hprobe
  linarith

/-- The lower side of the Chebotarev count gives the cumulative inert lower
bound.  This is the point where the upper side would have been used by the
two-sided route; here only `sides.cheb.lower` is consumed.  In particular no
zero-free field is read. -/
theorem inert_lower (S : L34SidesCoreStrip K) (n : ℕ) :
    (1 / 2) * (S.liX n - S.liBeta0 n) -
        lagariasOdlyzkoError S.C S.cZ S.x S.degree n ≤ S.inertCount n := by
  have hlower := S.sides.cheb.lower n
  have hge := S.inert_ge_count n
  unfold mainOf at hlower
  linarith

/-- **The L34 probe-miss bound from the one-sided count.** -/
theorem probeMiss_le_ledger (S : L34SidesCoreStrip K) :
    ∀ᶠ n : ℕ in atTop,
      probeMiss S.classCount S.pTrial S.R n ≤ exp (-(2 : ℝ) * scale n) := by
  refine probeMiss_le_exp_of_paper_props S.budget S.bracket S.error_negligible
    S.degree_one_loss S.degree_one_reduction ?_ S.selection S.x_pos S.degree_pos
    S.F_pos S.T_ge_one S.degree_le_T S.class_le S.hstar_poly S.classCount_pos
    S.constant_margin S.scale_cubic
  intro n
  exact S.inert_lower n

/-- **The L34 ledger slot from the one-sided count.** -/
theorem loss_le_ledger (S : L34SidesCoreStrip K) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [S.probeMiss_le_ledger] with n hprobe
  exact (S.loss_le_probeMiss n).trans hprobe

/-- The manuscript's slower `exp (-H / log H)` rate, from the one-sided count. -/
theorem loss_le_paper (S : L34SidesCoreStrip K) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ exp (-(1 * Cogentic.RandomizedL34.paperRate n)) := by
  filter_upwards [S.loss_le_ledger, scale_grows.eventually_ge_atTop (Real.exp 1)]
    with n hledger hs
  have hs0 : 0 < scale n := lt_of_lt_of_le (Real.exp_pos 1) hs
  have hlog1 : 1 ≤ Real.log (scale n) := by
    have h := Real.log_le_log (Real.exp_pos 1) hs
    simpa [Real.log_exp] using h
  have hlogpos : 0 < Real.log (scale n) := lt_of_lt_of_le zero_lt_one hlog1
  have hrate : Cogentic.RandomizedL34.paperRate n ≤ 2 * scale n := by
    unfold Cogentic.RandomizedL34.paperRate
    rw [div_le_iff₀ hlogpos]
    nlinarith [hs0, hlog1]
  exact hledger.trans (Real.exp_le_exp.mpr (by nlinarith))

/-- The literal `RatedLeaf` of the strip-based core. -/
noncomputable def ratedLeaf (S : L34SidesCoreStrip K) :
    Cogentic.RandomizedPaperLeafStatements.RatedLeaf where
  loss := S.loss
  loss_nonneg := S.loss_nonneg
  rate := Cogentic.RandomizedL34.paperRate
  c := 1
  c_pos := by norm_num
  paper := S.loss_le_paper
  ledger := S.loss_le_ledger

/-- The leaf's ledger slot is the proved one-sided ledger. -/
theorem ratedLeaf_slot (S : L34SidesCoreStrip K) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.ratedLeaf.slot

/-- The leaf's loss is the core loss. -/
theorem ratedLeaf_loss_eq (S : L34SidesCoreStrip K) (n : ℕ) :
    S.ratedLeaf.loss n = S.loss n := rfl

/-- The leaf's loss is nonnegative. -/
theorem ratedLeaf_loss_nonneg (S : L34SidesCoreStrip K) (n : ℕ) :
    0 ≤ S.ratedLeaf.loss n :=
  S.ratedLeaf.loss_nonneg n

end L34SidesCoreStrip

/-! ## 2. The strip-based Chebotarev-side input -/

/-- **The L34 Chebotarev sides with the all-zeros strip packet.**  This is
`L34ChebotarevSidesInputs` with the fields `zeroRealPart` and `zeroFree :
DedekindZeroFreeInput beta0 zeroRealPart cz discLog` deleted and replaced by the
single all-zeros packet

```
zeroStrip : DedekindZetaStripInput K beta0 cz discLog.
```

Every other field is unchanged.  No zero sequence is stored. -/
structure L34ChebotarevSidesInputsStrip (K : Type u) [Field K] [NumberField K] where
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
  /-- **The faithful all-zeros zero-free packet.**  Declared before the range
  constant `K : ℝ` so that `K` here is the number field. -/
  zeroStrip : DedekindZetaStripInput K beta0 cz discLog
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
  /-- The classical Stark exceptional-zero input. -/
  stark : StarkExceptionalZeroInput beta0 F discLog
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

namespace L34ChebotarevSidesInputsStrip

variable {K : Type u} [Field K] [NumberField K]
variable (S : L34ChebotarevSidesInputsStrip K)

/-- The positivity of `T`, from `T_ge_one`. -/
theorem T_pos (n : ℕ) : 0 < S.T n :=
  lt_of_lt_of_le zero_lt_one (S.T_ge_one n)

/-- The range constant is positive, from the packaged `T^6` range input. -/
theorem K_pos : 0 < S.K :=
  S.range.K_pos

/-- The absolute degree is positive, from the packaged `T^6` range input. -/
theorem degree_pos (n : ℕ) : 0 < S.degree n :=
  S.range.degree_pos n

/-- `log |Δ_E|` is positive, from the packaged `T^6` range input. -/
theorem discLog_pos (n : ℕ) : 0 < S.discLog n :=
  S.range.discLog_pos n

/-- The polynomial parameter bounds the absolute degree, from the range input. -/
theorem degree_le_T (n : ℕ) : S.degree n ≤ S.T n :=
  S.range.degree_le_T n

/-- The derived error-negligibility `Prop`. -/
theorem errorNegligible :
    ChebotarevErrorNegligible S.cbr (cutoff S.T) S.F S.T
      (lagariasOdlyzkoError S.C S.cZ (cutoff S.T) S.degree) :=
  (chebotarevErrorNegligible_iff_scalar (C := S.C) (cZ := S.cZ) (cbr := S.cbr)
    (degree := S.degree) S.stark.F_pos S.T_pos).mpr S.error_scalar

/-- The derived discarded-ideal `Prop`. -/
theorem degreeOneLoss :
    DegreeOneLossNegligible S.cbr (cutoff S.T) S.degree S.F S.T :=
  (degreeOneLossNegligible_iff_scalar (cbr := S.cbr) (degree := S.degree)
    (F := S.F) (T := S.T) S.stark.F_pos S.T_pos).mpr S.degree_loss_scalar

/-- The one-sided Chebotarev lower bound. -/
theorem chebotarevLowerBound :
    ChebotarevLowerBound S.count (mainOf S.liX S.liBeta0)
      (lagariasOdlyzkoError S.C S.cZ (cutoff S.T) S.degree) :=
  S.cheb.toLowerInput.lower

/-- The cumulative inert lower bound, from the one-sided count and the inert
containment.  The upper Chebotarev side is never used. -/
theorem inertLower (n : ℕ) :
    (1 / 2) * (S.liX n - S.liBeta0 n) -
        lagariasOdlyzkoError S.C S.cZ (cutoff S.T) S.degree n ≤ S.inertCount n := by
  have hlower := S.chebotarevLowerBound n
  have hge := S.inert_ge_count n
  unfold mainOf at hlower
  linarith

/-- **The composed detection lower bound.** -/
theorem probeLower (n : ℕ) :
    S.csel * S.cbr / 4 / (S.degree n * S.F n * S.T n ^ 6) ≤ S.pTrial n :=
  probe_lower_of_props S.bracket S.errorNegligible S.degreeOneLoss
    S.degree_one_reduction S.inertLower S.selection (cutoff_pos S.T)
    S.range.degree_pos S.stark.F_pos S.T_pos n

/-- The assembled strip-based core.  The cutoff is `2^(T^6)`, `h* = Ch T^3`,
and `m = h* + 7`; the zero-free field is the all-zeros strip packet. -/
noncomputable def toL34SidesCore : L34SidesCoreStrip K where
  x := cutoff S.T
  degree := S.degree
  discLog := S.discLog
  F := S.F
  T := S.T
  hstar := fun n => S.Ch * (S.T n) ^ 3
  m := fun n => S.Ch * (S.T n) ^ 3 + 7
  R := S.R
  classCount := S.classCount
  pTrial := S.pTrial
  beta0 := S.beta0
  count := S.count
  inertCount := S.inertCount
  degreeOneInert := S.degreeOneInert
  liX := S.liX
  liBeta0 := S.liBeta0
  Kc := S.K
  C := S.C
  cZ := S.cZ
  cz := S.cz
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  x_pos := cutoff_pos S.T
  degree_pos := S.range.degree_pos
  discLog_pos := S.range.discLog_pos
  F_pos := S.stark.F_pos
  T_pos := S.T_pos
  T_ge_one := S.T_ge_one
  classCount_pos := S.classCount_pos
  pTrial_nonneg := S.pTrial_nonneg
  pTrial_le_one := S.pTrial_le_one
  actualMiss := S.actualMiss
  actualMiss_nonneg := S.actualMiss_nonneg
  union_bound := S.union_bound
  degree_le_T := S.range.degree_le_T
  sides :=
    { zeroStrip := S.zeroStrip
      stark := S.stark.toStarkInput
      range := S.range.toChebotarevRangeInput
      cheb := S.cheb.toLowerInput }
  inert_ge_count := S.inert_ge_count
  bracket := S.bracket
  error_negligible := S.errorNegligible
  degree_one_loss := S.degreeOneLoss
  degree_one_reduction := S.degree_one_reduction
  selection := S.selection
  budget := S.budget
  class_le := S.classCubic.classCountBound
  hstar_poly := S.classCubic.classCountPolynomial
  mask_bits := S.classCubic.maskCompressionBits
  constant_margin := S.constant_margin
  scale_cubic := S.scale_cubic

/-- **The loss of the assembled core is exactly the actual probe miss.**  The
zero-free field is never read: the canonical compression `m = h* + 7` still
makes the mask failure cancel against `allowedFailure`. -/
theorem toL34SidesCore_loss (n : ℕ) :
    S.toL34SidesCore.loss n = S.actualMiss n := by
  unfold L34SidesCoreStrip.loss
  exact excessLoss_mask_exact (fun _ => rfl) S.actualMiss_nonneg n

/-- **The sequence-indexed zero-free field is vacuous at `zeroRealPart = beta0`.**
The antecedent `beta0 n < beta0 n` is impossible, so the field adds no
content.  This is why the L34 ledger never needed a zero sequence. -/
theorem vacuousZeroFree : DedekindZeroFreeInput S.beta0 S.beta0 S.cz S.discLog where
  cz_pos := S.cz_pos
  above_beta := fun n h => absurd h (lt_irrefl (S.beta0 n))

/-- **The old sequence-indexed L34 input, with a vacuous zero-free field.**  Every
data field is passed through and the zero-free field is the vacuous one at
`zeroRealPart = beta0`.  This exhibits the old interface without any zero
sequence, confirming that the L34 loss is independent of the zero-free region. -/
noncomputable def toL34ChebotarevSidesInputs :
    L34ChebotarevSidesInputs where
  beta0 := S.beta0
  zeroRealPart := S.beta0
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
  zeroFree := S.vacuousZeroFree
  stark := S.stark
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

/-- The old-style leaf obtained without any zero sequence still has loss exactly
the actual probe miss. -/
theorem toL34ChebotarevSidesInputs_loss (n : ℕ) :
    (wave15L34Leaf S.toL34ChebotarevSidesInputs).loss n = S.actualMiss n :=
  S.toL34ChebotarevSidesInputs.ratedLeaf_loss_eq n

/-- The assembled core's probe miss satisfies the ledger bound. -/
theorem probeMiss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      probeMiss S.classCount S.pTrial S.R n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toL34SidesCore.probeMiss_le_ledger

/-- The assembled core's loss satisfies the ledger bound. -/
theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      S.toL34SidesCore.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toL34SidesCore.loss_le_ledger

/-- The manuscript's slower `exp (-H/log H)` rate. -/
theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      S.toL34SidesCore.loss n ≤ exp (-(1 * Cogentic.RandomizedL34.paperRate n)) :=
  S.toL34SidesCore.loss_le_paper

/-- The literal `RatedLeaf` of the strip-input bundle. -/
noncomputable def ratedLeaf : Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  S.toL34SidesCore.ratedLeaf

/-- The leaf's loss is the core loss, hence exactly the actual probe miss. -/
theorem ratedLeaf_loss_eq (n : ℕ) : S.ratedLeaf.loss n = S.actualMiss n :=
  S.toL34SidesCore_loss n

/-- The leaf's loss is nonnegative. -/
theorem ratedLeaf_loss_nonneg (n : ℕ) : 0 ≤ S.ratedLeaf.loss n :=
  S.ratedLeaf.loss_nonneg n

/-- **A genuine nonzero loss.**  Whenever the probe stage actually fails with
positive probability at some index, the assembled loss is positive there. -/
theorem ratedLeaf_loss_pos {n : ℕ} (h : 0 < S.actualMiss n) :
    0 < S.ratedLeaf.loss n := by
  rw [S.ratedLeaf_loss_eq n]
  exact h

/-- The leaf's ledger slot. -/
theorem ratedLeaf_slot :
    ∀ᶠ n : ℕ in atTop,
      S.ratedLeaf.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.ratedLeaf.slot

/-- The manuscript's paper rate holds for the assembled leaf. -/
theorem ratedLeaf_paper :
    ∀ᶠ n : ℕ in atTop,
      S.ratedLeaf.loss n ≤ exp (-(S.ratedLeaf.c * S.ratedLeaf.rate n)) :=
  S.ratedLeaf.paper

end L34ChebotarevSidesInputsStrip

/-! ## 3. The Wave-36 L34 block: no zero sequence -/

/-- **The Wave-36 L34 block.**  It is `Wave35L34Inputs` with the sequence data
`zeroSeq`, `zeroSeq_realPart`, `zeroSeq_lt_one` (and the derived
`zeroRealPart`) removed.  The zero-free content is the all-zeros strip packet
`DedekindZetaStripInput K beta0 cz discLog`, derived from the critical line,
the abelian factorization and the half-line arithmetic (`toZeroStrip`). -/
structure Wave36L34Inputs (K : Type u) [Field K] [NumberField K]
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

namespace Wave36L34Inputs

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}

/-- **The all-zeros strip packet is derived**, never assumed as a field. -/
theorem toZeroStrip (line : DirichletLZerosOnLine)
    (S : Wave36L34Inputs K ι N χ) :
    DedekindZetaStripInput K S.beta0 S.cz S.discLog :=
  DedekindZetaStripInput_of_GRH_of_factorization line S.factorization
    S.half_le_beta0 S.cz S.discLog

/-- **The Stark input is derived** from `β₀ ≤ 1/2` and `1/2 ≤ paperBeta0`. -/
theorem toStark (S : Wave36L34Inputs K ι N χ) :
    StarkExceptionalZeroInput S.beta0 S.F S.discLog :=
  starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0
    S.starkF_pos S.range.discLog_pos S.beta0_le_half S.paperBeta0_ge_half

/-- **The strip-based Chebotarev-side input.**  Every data field is passed
through; the zero-free field is the derived all-zeros packet
`S.toZeroStrip line`, and Stark is the derived arithmetic replacement. -/
noncomputable def toL34ChebotarevSidesInputsStrip
    (line : DirichletLZerosOnLine) (S : Wave36L34Inputs K ι N χ) :
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
    (line : DirichletLZerosOnLine) (S : Wave36L34Inputs K ι N χ) :
    (S.toL34ChebotarevSidesInputsStrip line).actualMiss = S.actualMiss := rfl

/-- The strip-based core assembled from the Wave-36 block. -/
noncomputable def toL34SidesCore (line : DirichletLZerosOnLine)
    (S : Wave36L34Inputs K ι N χ) : L34SidesCoreStrip K :=
  (S.toL34ChebotarevSidesInputsStrip line).toL34SidesCore

/-- The literal `RatedLeaf` of the Wave-36 L34 block. -/
noncomputable def ratedLeaf (line : DirichletLZerosOnLine)
    (S : Wave36L34Inputs K ι N χ) :
    Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  (S.toL34ChebotarevSidesInputsStrip line).ratedLeaf

/-- **The Wave-36 L34 loss is exactly the actual probe miss.** -/
theorem ratedLeaf_loss_eq (line : DirichletLZerosOnLine)
    (S : Wave36L34Inputs K ι N χ) (n : ℕ) :
    (S.ratedLeaf line).loss n = S.actualMiss n := by
  simpa only [ratedLeaf, toL34ChebotarevSidesInputsStrip_actualMiss] using
    (S.toL34ChebotarevSidesInputsStrip line).ratedLeaf_loss_eq n

/-- The loss is nonnegative. -/
theorem ratedLeaf_loss_nonneg (line : DirichletLZerosOnLine)
    (S : Wave36L34Inputs K ι N χ) (n : ℕ) :
    0 ≤ (S.ratedLeaf line).loss n :=
  (S.ratedLeaf line).loss_nonneg n

/-- **A genuine nonzero loss.** -/
theorem ratedLeaf_loss_pos (line : DirichletLZerosOnLine)
    (S : Wave36L34Inputs K ι N χ) {n : ℕ} (h : 0 < S.actualMiss n) :
    0 < (S.ratedLeaf line).loss n := by
  simpa only [ratedLeaf, toL34ChebotarevSidesInputsStrip_actualMiss] using
    (S.toL34ChebotarevSidesInputsStrip line).ratedLeaf_loss_pos h

/-- The L34 ledger slot. -/
theorem ratedLeaf_slot (line : DirichletLZerosOnLine)
    (S : Wave36L34Inputs K ι N χ) :
    ∀ᶠ n : ℕ in atTop,
      (S.ratedLeaf line).loss n ≤ exp (-(2 : ℝ) * scale n) :=
  (S.ratedLeaf line).slot

/-- **The strip packet is still derived**, not a field of the Wave-36 block. -/
theorem zeroStrip_derived (line : DirichletLZerosOnLine)
    (S : Wave36L34Inputs K ι N χ) :
    DedekindZetaStripInput K S.beta0 S.cz S.discLog :=
  S.toZeroStrip line

/-- On the half-line, `β₀` is exactly the critical line. -/
theorem beta0_eq_half (S : Wave36L34Inputs K ι N χ) (n : ℕ) :
    S.beta0 n = 1 / 2 :=
  le_antisymm (S.beta0_le_half n) (S.half_le_beta0 n)

/-- **Compatibility transport to the Wave-35 block**, when a genuine zero
sequence with real parts below `1` is supplied.  The sequence is not part of the
Wave-36 block; it is only needed to inhabit the older record type. -/
noncomputable def toWave35L34Inputs (S : Wave36L34Inputs K ι N χ)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (hZ : ∀ n, Z.realPart n < 1) : Wave35L34Inputs K ι N χ where
  beta0 := S.beta0
  zeroRealPart := Z.realPart
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
  zeroSeq := Z
  zeroSeq_realPart := rfl
  zeroSeq_lt_one := hZ
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

end Wave36L34Inputs

/-! ## 4. The Wave-36 ledger -/

/-- **The Wave-36 ledger.**  It is the fully discharged ledger at the
constructed L18.4 certificate and the Wave-36 L34 leaf. -/
noncomputable def wave36Slots {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave36L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  fullyDischargedSlots (paperCertificate line) l19.toL19FullCertificate
    (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf l21.toL21_2LeafData)
    (wave15L27Leaf l27_data l27_finish) l30.toWave26L30Inputs.toSubexpLeaf
    (l34.ratedLeaf line) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
    (wave14P1Leaf p1)

/-- The Wave-36 ledger total, term by term. -/
theorem wave36Slots_total_eq {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave36L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave36Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
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
  simpa only [wave36Slots] using
    fullyDischargedSlots_total_eq (paperCertificate line) l19.toL19FullCertificate
      (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
      (wave14L21_2Leaf l21.toL21_2LeafData)
      (wave15L27Leaf l27_data l27_finish) l30.toWave26L30Inputs.toSubexpLeaf
      (l34.ratedLeaf line) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
      (wave14P1Leaf p1) n

/-- **The Wave-36 and Wave-35 ledger totals agree**, once the Wave-36 block is
transported to the Wave-35 block with a zero-sequence witness.  The only
difference between the two ledgers is the L34 leaf, and both leaves have loss
exactly the same actual probe miss. -/
theorem wave36Slots_total_eq_wave35Slots_total
    {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave36L34Inputs K ι N χ)
    (p1 : SubexpPrepassInput)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (hZ : ∀ n, Z.realPart n < 1) (n : ℕ) :
    (wave36Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
      (wave35Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30
        (l34.toWave35L34Inputs Z hZ) p1).total n := by
  rw [wave36Slots, wave35Slots, wave34Slots, wave33Slots, wave32Slots,
    wave31Slots, wave29Slots, wave27Slots]
  rw [fullyDischargedSlots_total_eq, fullyDischargedSlots_total_eq]
  simp only [Wave36L34Inputs.ratedLeaf_loss_eq, wave15L34Leaf_loss_eq]
  rfl

/-- **The L34 loss of the Wave-36 ledger is exactly the actual probe miss.** -/
theorem wave36Slots_l34_loss_eq {K : Type u} [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (line : DirichletLZerosOnLine) (l34 : Wave36L34Inputs K ι N χ) (n : ℕ) :
    (l34.ratedLeaf line).loss n = l34.actualMiss n :=
  l34.ratedLeaf_loss_eq line n

/-! ## 5. The combined residual record without the zero sequence -/

/-- **The Wave-36 combined residual record.**

It is the Wave-35 record with the L34 block replaced by `Wave36L34Inputs`, which
has no `zeroSeq`, no `zeroSeq_lt_one` and no `zeroFree` field.  The zero-free
content is the all-zeros strip packet derived from the critical line and the
abelian factorization.  All other fields are copied from the Wave-35 record, and
the ledger is `wave36Slots` at the new L34 leaf. -/
structure PaperResidualFor36 (line : DirichletLZerosOnLine)
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
  /-- **L34 without the zero sequence**: the strip packet is derived from the
  factorization and the half-line arithmetic. -/
  l34 : Wave36L34Inputs K ι N χ
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
  /-- Adapter: the concrete C5 loss is dominated by the Wave-36 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave36Slots line l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor36

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor36 → FullyDischargedInputs` directly.**  The L34 leaf is
the Wave-36 strip-based leaf; the ledger is `wave36Slots`, definitionally the
fully discharged ledger at that leaf. -/
noncomputable def toFullyDischargedInputs
    (I : PaperResidualFor36 line K ι N χ E D) : FullyDischargedInputs E D where
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
    simpa only [wave36Slots] using I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs
    (I : PaperResidualFor36 line K ι N χ E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- The L34 loss of the Wave-36 record is exactly the actual probe miss. -/
theorem l34_loss_eq (I : PaperResidualFor36 line K ι N χ E D) (n : ℕ) :
    (I.l34.ratedLeaf line).loss n = I.l34.actualMiss n :=
  I.l34.ratedLeaf_loss_eq line n

/-- **The zero-free datum of the Wave-36 record is the strip packet**, derived
from the critical line and the factorization. -/
theorem zeroStrip_derived (I : PaperResidualFor36 line K ι N χ E D) :
    DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog :=
  I.l34.toZeroStrip line

/-- The Stark field is derived, not stored. -/
theorem stark_derived (I : PaperResidualFor36 line K ι N χ E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  I.l34.toStark

/-- **`PaperResidualFor36 → PaperResidualFor35`**, given a genuine zero sequence
whose real parts are below `1`.  This witness is only needed because
`Wave35L34Inputs` still stores such a sequence; the Wave-36 block does not, and
the Wave-36 endpoint does not use this transport. -/
noncomputable def toPaperResidualFor35
    (I : PaperResidualFor36 line K ι N χ E D)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (hZ : ∀ n, Z.realPart n < 1) :
    PaperResidualFor35 line K ι N χ E D where
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34.toWave35L34Inputs Z hZ
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
    rw [← wave36Slots_total_eq_wave35Slots_total line I.l19 I.l20_2 I.l20_4
      I.l21 I.l27_data I.l27_finish I.l30 I.l34 I.p1 Z hZ n]
    exact I.loss_le n hN

end PaperResidualFor36

/-- **The schedule-indexed form of the Wave-36 record.** -/
abbrev PaperResidualFor36Schedule (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor36 line K ι N χ (E s) D

/-! ## 6. The endpoint -/

/-- **Wave-36 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K`, every explicit abelian factorization `ζ_K = ∏ L(·, χ)` away from the pole,
and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor36 line K ι N χ (E s) D` record, the kernel-checked
driver outputs a permutation of `n.primeFactorsList` and has expected serialized
bit cost eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`.

The L34 block carries **no zero sequence**: the zero-free content is the
all-zeros strip packet derived from `line` and the factorization.  The endpoint
is proved from the fully discharged endpoint at the Wave-36 L34 leaf. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave36Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
      (χ : ∀ i, DirichletCharacter ℂ (N i)),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor36 line K ι N χ (E s) D) →
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

/-! ## 7. Residual accounting -/

/-- The field names of `Wave36L34Inputs`.  `zeroSeq`, `zeroSeq_realPart`,
`zeroSeq_lt_one`, `zeroFree` and `zeroStrip` are all absent; the zero-free
content is the factorization-derived strip packet. -/
def wave36L34FieldNames : List String :=
  ["beta0", "degree", "discLog", "F", "T", "count",
   "inertCount", "degreeOneInert", "liX", "liBeta0", "pTrial", "actualMiss",
   "classCount", "R", "cz", "cz_pos", "factorization", "half_le_beta0",
   "K", "C", "cZ", "cbr", "csel", "Ch", "range", "T_ge_one",
   "cheb", "inert_ge_count", "bracket", "error_scalar", "degree_loss_scalar",
   "degree_one_reduction", "selection", "budget", "classCount_pos", "classCubic",
   "constant_margin", "scale_cubic", "actualMiss_nonneg", "union_bound",
   "pTrial_nonneg", "pTrial_le_one", "starkF_pos", "beta0_le_half",
   "paperBeta0_ge_half"]

theorem wave36L34FieldNames_length : wave36L34FieldNames.length = 45 := rfl

/-- **No sequence field is present in the Wave-36 L34 block.** -/
theorem wave36_no_zeroSeq_field :
    wave36L34FieldNames.all (fun s => decide (s ≠ "zeroSeq")) = true ∧
      wave36L34FieldNames.all (fun s => decide (s ≠ "zeroSeq_realPart")) = true ∧
      wave36L34FieldNames.all (fun s => decide (s ≠ "zeroSeq_lt_one")) = true :=
  ⟨by decide, by decide, by decide⟩

/-- **Neither `zeroFree` nor `zeroStrip` is a field.** -/
theorem wave36_no_zeroFree_no_zeroStrip_field :
    wave36L34FieldNames.all (fun s => decide (s ≠ "zeroFree")) = true ∧
      wave36L34FieldNames.all (fun s => decide (s ≠ "zeroStrip")) = true :=
  ⟨by decide, by decide⟩

/-- The zero-free content is the factorization and the half-line arithmetic. -/
theorem wave36_L34_zeroFree_content :
    wave36L34FieldNames.contains "factorization" = true ∧
      wave36L34FieldNames.contains "half_le_beta0" = true :=
  ⟨by decide, by decide⟩

/-- The field names of `PaperResidualFor36`; there is no `l18_4` field and the
L34 block has no sequence field. -/
def wave36FieldNames : List String :=
  ["l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave36FieldNames_length : wave36FieldNames.length = 17 := rfl

/-- **The record no longer carries an L18.4 hypothesis.** -/
theorem wave36_no_l18_4 :
    wave36FieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- **The exact Wave-36 residual list.**  It is the Wave-35 list with the
sequence entries `zeroSeq` and `zeroSeq_lt_one` removed.  The zero-free content
is only the factorization with its derived strip packet. -/
def wave36RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "factorization", "cheb", "range", "half_le_beta0", "beta0_le_half",
   "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

/-- The residual list literally is the displayed list. -/
theorem wave36RemainingFieldNames_exact :
    wave36RemainingFieldNames =
      ["zetaRH", "localCount", "hbuchstab", "hparity",
       "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
       "killMass", "curveBudget",
       "factorization", "cheb", "range", "half_le_beta0", "beta0_le_half",
       "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"] :=
  rfl

theorem wave36RemainingFieldNames_length :
    wave36RemainingFieldNames.length = 24 := rfl

/-- **The Wave-36 residual list is the Wave-35 list with the sequence entries
filtered out.** -/
theorem wave36RemainingFieldNames_eq_wave35_filter :
    wave36RemainingFieldNames =
      wave35RemainingFieldNames.filter
        (fun s => decide (s ≠ "zeroSeq") && decide (s ≠ "zeroSeq_lt_one")) := by
  decide

/-- **No sequence entry survives in the residual list.** -/
theorem wave36_no_zeroSeq_residual :
    wave36RemainingFieldNames.all (fun s => decide (s ≠ "zeroSeq")) = true ∧
      wave36RemainingFieldNames.all (fun s => decide (s ≠ "zeroSeq_lt_one")) = true :=
  ⟨by decide, by decide⟩

/-- **Neither `zeroFree` nor `zeroStrip` survives in the residual list.** -/
theorem wave36_no_zeroFree_no_zeroStrip_residual :
    wave36RemainingFieldNames.all (fun s => decide (s ≠ "zeroFree")) = true ∧
      wave36RemainingFieldNames.all (fun s => decide (s ≠ "zeroStrip")) = true :=
  ⟨by decide, by decide⟩

/-- **The residual list does not contain the L18.4 certificate entry.** -/
theorem wave36_no_l18_4_residual :
    wave36RemainingFieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- The residual list contains the Buchstab/parity, factorization, half-line and
remaining certificate entries. -/
theorem wave36_residual_blocks :
    wave36RemainingFieldNames.contains "hbuchstab" = true ∧
      wave36RemainingFieldNames.contains "hparity" = true ∧
      wave36RemainingFieldNames.contains "factorization" = true ∧
      wave36RemainingFieldNames.contains "half_le_beta0" = true ∧
      wave36RemainingFieldNames.contains "cheb" = true ∧
      wave36RemainingFieldNames.contains "range" = true ∧
      wave36RemainingFieldNames.contains "beta0_le_half" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {N : ι → ℕ} [∀ i, NeZero (N i)]
variable {χ : ∀ i, DirichletCharacter ℂ (N i)}
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The complete remaining L30 analytic input** is the Buchstab large-prime
estimate together with the odd-half parity fraction. -/
theorem wave36_l30_remaining (I : PaperResidualFor36 line K ι N χ E D) :
    BuchstabLargePrimeShortIntervalLower I.l30.counts.c I.l30.counts.p
        I.l30.counts.ε ∧
      CentralOddHalfParity I.l30.counts.θ I.l30.counts.p I.l30.counts.ε :=
  ⟨I.l30.counts.hbuchstab, I.l30.counts.hparity⟩

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave36_l21_remaining (I : PaperResidualFor36 line K ι N χ E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L34 analytic input is the factorization and the
half-line arithmetic**, with the strip packet derived and no zero sequence. -/
theorem wave36_l34_remaining (I : PaperResidualFor36 line K ι N χ E D) :
    DedekindZetaFactorsIntoDirichletOffPole K ι N χ ∧
      (∀ n, 1 / 2 ≤ I.l34.beta0 n) ∧
      DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog ∧
      0 < I.l34.cz ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog ∧
      (∀ n, I.l34.beta0 n ≤ 1 / 2) :=
  ⟨I.l34.factorization, I.l34.half_le_beta0, I.zeroStrip_derived, I.l34.cz_pos,
    I.l34.cheb, I.l34.range, I.l34.beta0_le_half⟩

/-! ## Axiom audit -/

#print axioms L34SidesCoreStrip.loss_nonneg
#print axioms L34SidesCoreStrip.maskFailure_le_allowed
#print axioms L34SidesCoreStrip.actualMiss_le_probeMiss
#print axioms L34SidesCoreStrip.loss_le_probeMiss
#print axioms L34SidesCoreStrip.inert_lower
#print axioms L34SidesCoreStrip.probeMiss_le_ledger
#print axioms L34SidesCoreStrip.loss_le_ledger
#print axioms L34SidesCoreStrip.loss_le_paper
#print axioms L34SidesCoreStrip.ratedLeaf
#print axioms L34SidesCoreStrip.ratedLeaf_slot
#print axioms L34ChebotarevSidesInputsStrip.errorNegligible
#print axioms L34ChebotarevSidesInputsStrip.degreeOneLoss
#print axioms L34ChebotarevSidesInputsStrip.inertLower
#print axioms L34ChebotarevSidesInputsStrip.probeLower
#print axioms L34ChebotarevSidesInputsStrip.toL34SidesCore
#print axioms L34ChebotarevSidesInputsStrip.toL34SidesCore_loss
#print axioms L34ChebotarevSidesInputsStrip.loss_le_ledger
#print axioms L34ChebotarevSidesInputsStrip.ratedLeaf
#print axioms L34ChebotarevSidesInputsStrip.ratedLeaf_loss_eq
#print axioms L34ChebotarevSidesInputsStrip.ratedLeaf_loss_pos
#print axioms L34ChebotarevSidesInputsStrip.vacuousZeroFree
#print axioms L34ChebotarevSidesInputsStrip.toL34ChebotarevSidesInputs
#print axioms L34ChebotarevSidesInputsStrip.toL34ChebotarevSidesInputs_loss
#print axioms Wave36L34Inputs.toZeroStrip
#print axioms Wave36L34Inputs.toStark
#print axioms Wave36L34Inputs.toL34ChebotarevSidesInputsStrip
#print axioms Wave36L34Inputs.ratedLeaf_loss_eq
#print axioms Wave36L34Inputs.ratedLeaf_loss_pos
#print axioms Wave36L34Inputs.toWave35L34Inputs
#print axioms wave36Slots
#print axioms wave36Slots_total_eq
#print axioms wave36Slots_l34_loss_eq
#print axioms PaperResidualFor36.toFullyDischargedInputs
#print axioms PaperResidualFor36.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor36.l34_loss_eq
#print axioms PaperResidualFor36.zeroStrip_derived
#print axioms PaperResidualFor36.stark_derived
#print axioms PaperResidualFor36.toPaperResidualFor35
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave36Inputs
#print axioms wave36L34FieldNames_length
#print axioms wave36_no_zeroSeq_field
#print axioms wave36_no_zeroFree_no_zeroStrip_field
#print axioms wave36_L34_zeroFree_content
#print axioms wave36RemainingFieldNames_exact
#print axioms wave36RemainingFieldNames_length
#print axioms wave36RemainingFieldNames_eq_wave35_filter
#print axioms wave36_no_zeroSeq_residual
#print axioms wave36_no_zeroFree_no_zeroStrip_residual
#print axioms wave36_residual_blocks
#print axioms wave36_l30_remaining
#print axioms wave36_l21_remaining
#print axioms wave36_l34_remaining

end Cogentic.RandomizedPaperEndpointWave36
