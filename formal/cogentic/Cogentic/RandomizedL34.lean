import Cogentic.RandomizedPaperLeafStatements

/-!
# L34: effective Chebotarev, Stark's exceptional zero, and the ledger reduction

`Cogentic.RandomizedPaperLeafStatements.RatedLeaf` records the L34 paper rate
and a separate `ledger` estimate.  This file decomposes the paper rate into its
actual analytic and counting inputs and proves the `RatedLeaf`/ledger
reduction.  Nothing here proves a theorem of analytic number theory: the
effective Chebotarev theorem and the exceptional-zero bound are explicit `Prop`
fields, exactly as in the manuscript.

## The decomposition

The chain follows `research/keybreak-cumulative-character-probes.md` and KB
E.3 p.87-88:

1. `DedekindZeroFreeRegion` is the zero-free region of `ζ_E` away from a
   possible exceptional real zero `β₀` (Lagarias-Odlyzko Theorem 1.3).
2. `StarkExceptionalZeroBound` is Stark's bound
   `1 - β₀ ≥ (4 F log |Δ_E|)⁻¹` for that possible zero.
3. `EffectiveChebotarevRange` and `LagariasOdlyzkoError` are the range
   condition `log x ≫ d (log |Δ_E|)²` and the error
   `C x exp (-c sqrt (log x / (2d)))` of Lagarias-Odlyzko Theorem 1.3.
   `EffectiveChebotarev` is the resulting cumulative count estimate.
4. `CumulativeInertLowerBound` turns the two Chebotarev counts into
   `½ (Li x - Li x^{β₀}) - error ≤ inertCount`.
5. `LogIntegralBracket` is the consequence of Stark's bound on the dyadic
   interval, `≫ x/(F T⁶)`.
6. `ChebotarevErrorNegligible` and `DegreeOneLossNegligible` are the two
   explicit negligibility steps (the theorem error and the discarded small /
   higher-degree prime ideals).
7. `DegreeOneInertReduction` and `ProbeSelectionLowerBound` give the per-trial
   detection probability `≫ 1/(d F T⁶)`.
8. `ProbeBudget` is the paper's `R = F T¹⁰`; `ClassCountBound` and
   `ClassCountPolynomial` are Lemma E.2 plus the polynomial bound on `h*`.
9. `MaskCompressionBits` is the `m = h* + 7` compression giving mask failure
   `≤ 1/128`.

The paper's `1/128` is a *slack*, not the ledger loss: the L34 ledger charges
only the excess of the probe failure over that slack.  Since the mask failure is
at most `1/128`, the excess is at most the probe miss probability, which the
probe-count budget bounds by `exp (-2H)`.  This is the "headroom" recorded by
`RatedLeaf.ledger`.

The main definitions/theorems are

* `EffectiveChebotarevInputs`, the bundle of explicit paper-level inputs;
* `EffectiveChebotarevInputs.degreeOneInert_lower`, the Chebotarev + Stark +
  negligibility chain;
* `EffectiveChebotarevInputs.probe_lower`, the `1/(d F T⁶)` selection bound;
* `EffectiveChebotarevInputs.probeMiss_le_ledger`, the `D^{-2}` probe bound;
* `EffectiveChebotarevInputs.loss_le_ledger`, the ledger slot;
* `EffectiveChebotarevInputs.ratedLeaf`, the literal `RatedLeaf`;
* `EffectiveChebotarevInputs.loss_le_paper`, the manuscript's slower
  `exp (-H/log H)` rate.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No loss, mass, count
or error is set to zero: the slack `1/128` cancels against the explicit mask
failure, and every remaining parameter is a positive field.
-/

namespace Cogentic.RandomizedL34

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedEpochAssembly

/-! ## 1. Paper-level analytic statements -/

/-- **Dedekind zeta zero-free region** (Lagarias-Odlyzko Theorem 1.3, zero-free
form).  Away from the possible exceptional real zero `β₀`, no zero of `ζ_E` has
real part larger than `1 - c_z / log |Δ_E|`.  `zeroRealPart` is the real part
of an arbitrary zero of `ζ_E`, and `discLog` is `log |Δ_E|`. -/
def DedekindZeroFreeRegion
    (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  0 < cz ∧
    ∀ n, 1 - cz / discLog n < zeroRealPart n → zeroRealPart n ≤ beta0 n

/-- **Stark's exceptional-zero bound** (as used in KB E.3): for the possible
exceptional real zero `β₀` of `ζ_E`,
`1 - β₀ ≥ (4 F log |Δ_E|)⁻¹`, where `F = (2d)!` is the manuscript's factorial
factor and `discLog = log |Δ_E|`. -/
def StarkExceptionalZeroBound
    (beta0 F discLog : ℕ → ℝ) : Prop :=
  ∀ n, 0 < 4 * F n * discLog n ∧
    1 / (4 * F n * discLog n) ≤ 1 - beta0 n

/-- **The range condition of Lagarias-Odlyzko Theorem 1.3**:
`log x ≥ K d (log |Δ_E|)²`.  The constant `K` is explicit. -/
def EffectiveChebotarevRange
    (K : ℝ) (x degree discLog : ℕ → ℝ) : Prop :=
  0 < K ∧
    ∀ n, K * degree n * (discLog n) ^ 2 ≤ Real.log (x n)

/-- **The explicit Lagarias-Odlyzko error**:
`C x exp (-c sqrt (log x / (2d)))`.  The constants `C` and `c` are positive and
explicit; `degree` is the absolute degree `2d` of the quadratic extension
`E = K(√γ)`. -/
def LagariasOdlyzkoError
    (C c : ℝ) (x degree error : ℕ → ℝ) : Prop :=
  0 < C ∧ 0 < c ∧
    ∀ n, error n =
      C * x n * Real.exp (-(c * Real.sqrt (Real.log (x n) / (2 * degree n))))

/-- **Effective Chebotarev**, cumulative form: the count in a fixed conjugacy
class differs from its main term by at most the explicit error. -/
def EffectiveChebotarev (count main error : ℕ → ℝ) : Prop :=
  ∀ n, |count n - main n| ≤ error n

/-- **Cumulative inert lower bound.**  For the quadratic extension `E/K` the
nonidentity class has relative size `1/2` (also the coefficient of the possible
exceptional term), so the cumulative inert count is at least
`½ (Li x - Li x^{β₀}) - error`. -/
def CumulativeInertLowerBound
    (inertCount liX liBeta0 error : ℕ → ℝ) : Prop :=
  ∀ n, (1 / 2) * (liX n - liBeta0 n) - error n ≤ inertCount n

/-- The dyadic bracket term `c x / (F T⁶)`. -/
noncomputable def bracketTerm (cbr : ℝ) (x F T : ℕ → ℝ) (n : ℕ) : ℝ :=
  cbr * x n / (F n * T n ^ 6)

/-- **The logarithmic-integral bracket** on `[x^{β₀}, x]`.  On that interval the
integrand is at least `1/log x`, so Stark's bound gives
`Li x - Li x^{β₀} ≫ x min {1/log x, 1/(F T)}`; in particular, with the
manuscript's `log x ≪ F T⁶`, it is `≫ x/(F T⁶)`.  The explicit constant is
`cbr`. -/
def LogIntegralBracket
    (cbr : ℝ) (x F T liX liBeta0 : ℕ → ℝ) : Prop :=
  0 < cbr ∧
    ∀ n, bracketTerm cbr x F T n ≤ liX n - liBeta0 n

/-- **The effective-Chebotarev error is negligible** against the bracket: it is
at most `(cbr/8) x/(F T⁶)`.  This is the range/negligibility step in E.3,
where `sqrt (log x/(2d)) ≫ T^{5/2}` dominates `log F = O(T log T)`. -/
def ChebotarevErrorNegligible
    (cbr : ℝ) (x F T error : ℕ → ℝ) : Prop :=
  ∀ n, error n ≤ bracketTerm (cbr / 8) x F T n

/-- **Discarding small and higher-degree prime ideals is negligible.**  At most
`d sqrt x` ideals of norm at most `sqrt x` or of absolute residue degree greater
than one are lost, and this is at most `(cbr/8) x/(F T⁶)`. -/
def DegreeOneLossNegligible
    (cbr : ℝ) (x degree F T : ℕ → ℝ) : Prop :=
  ∀ n, degree n * Real.sqrt (x n) ≤ bracketTerm (cbr / 8) x F T n

/-- **Degree-one reduction.**  The remaining degree-one inert ideals number at
least the full inert count minus the discarded `d sqrt x` ideals. -/
def DegreeOneInertReduction
    (inertCount degreeOneInert degree x : ℕ → ℝ) : Prop :=
  ∀ n, inertCount n - degree n * Real.sqrt (x n) ≤ degreeOneInert n

/-- **Probe selection.**  Each eligible degree-one ideal is selected with
probability at least `csel/(d x)` per trial, so the probability of selecting one
of `degreeOneInert` eligible ideals is `≥ csel * degreeOneInert/(d x)`. -/
def ProbeSelectionLowerBound
    (csel : ℝ) (x degree degreeOneInert pTrial : ℕ → ℝ) : Prop :=
  0 < csel ∧
    ∀ n, csel * degreeOneInert n / (degree n * x n) ≤ pTrial n

/-- **The paper's trial budget** `R = F T¹⁰`. -/
def ProbeBudget (R : ℕ → ℕ) (F T : ℕ → ℝ) : Prop :=
  ∀ n, (R n : ℝ) = F n * T n ^ 10

/-- **Lemma E.2 / the S-unit bound**: the number of nonrational classes is at
most `2^{h*}`. -/
def ClassCountBound (classCount hstar : ℕ → ℝ) : Prop :=
  ∀ n, classCount n ≤ (2 : ℝ) ^ (hstar n)

/-- **Polynomial bound on the class-group logarithm**: `h* = O(T³)`. -/
def ClassCountPolynomial (Ch : ℝ) (hstar T : ℕ → ℝ) : Prop :=
  0 < Ch ∧ ∀ n, hstar n ≤ Ch * T n ^ 3

/-- **Mask-compression bit budget**: `m = h* + 7`, so the simultaneous failure
of the compressed coordinates is at most `2^{h*-m} ≤ 1/128`. -/
def MaskCompressionBits (hstar m : ℕ → ℝ) : Prop :=
  ∀ n, hstar n + 7 ≤ m n

/-- **The probe union bound.**  The actual failure probability of the
`R`-trial probe stage is at most `classCount * (1 - pTrial)^R`: each of the at
most `classCount` classes survives one trial with probability `1 - pTrial`, and
the union bound over the classes costs the factor `classCount`. -/
def ProbeMissUnionBound
    (actualMiss pTrial classCount : ℕ → ℝ) (R : ℕ → ℕ) : Prop :=
  ∀ n, actualMiss n ≤ classCount n * (1 - pTrial n) ^ (R n)

/-- The standard exponential form of the per-class miss probability:
`(1 - p)^R ≤ exp (-R p)` for a probability `p`. -/
theorem one_sub_pow_le_exp_neg (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : ℕ) :
    (1 - p) ^ R ≤ Real.exp (-(R * p)) := by
  have hbase : 0 ≤ 1 - p := by linarith
  have hle : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
  calc
    (1 - p) ^ R ≤ (Real.exp (-p)) ^ R := pow_le_pow_left₀ hbase hle R
    _ = Real.exp (-(R * p)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The probe miss probability, in the exponential form of the union bound:
`classCount * exp (-R pTrial)`. -/
noncomputable def probeMiss
    (classCount pTrial : ℕ → ℝ) (R : ℕ → ℕ) (n : ℕ) : ℝ :=
  classCount n * Real.exp (-((R n : ℝ) * pTrial n))

/-- The compressed mask failure `2^{h*-m}`. -/
noncomputable def maskFailure (hstar m : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (hstar n - m n)

/-- The `1/128` slack already carried by the paper's character-separation
statement. -/
noncomputable def allowedFailure (_ : ℕ) : ℝ := 1 / 128

/-- The ledger loss: the excess of the actual failure over the `1/128` slack.
The max is not a loss set to zero; it records that the paper only charges the
part above the already accepted `1/128`. -/
noncomputable def excessLoss (probe mask allowed : ℕ → ℝ) (n : ℕ) : ℝ :=
  max 0 (probe n + mask n - allowed n)

/-- The manuscript's slower rate `H / log H` used for the L34 paper statement. -/
noncomputable def paperRate (n : ℕ) : ℝ := scale n / Real.log (scale n)

/-! ## 2. The explicit input bundle -/

/-- **The L34 effective-Chebotarev input bundle.**

Every field is either a paper-level `Prop` (the Dedekind zero-free region,
Stark's bound, Lagarias-Odlyzko's range and error, the cumulative count and the
probe-count inputs) or an explicit positivity / growth condition.  No field is a
restatement of the ledger inequality `loss ≤ exp (-2H)`. -/
structure EffectiveChebotarevInputs where
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
  /-- The real part of a generic zero of `ζ_E`. -/
  zeroRealPart : ℕ → ℝ
  /-- A cumulative Chebotarev count. -/
  count : ℕ → ℝ
  /-- Its main term. -/
  main : ℕ → ℝ
  /-- The Lagarias-Odlyzko error. -/
  error : ℕ → ℝ
  /-- The cumulative inert count. -/
  inertCount : ℕ → ℝ
  /-- The degree-one inert count after discarding small / higher-degree ideals. -/
  degreeOneInert : ℕ → ℝ
  /-- `Li x`. -/
  liX : ℕ → ℝ
  /-- `Li x^{β₀}`. -/
  liBeta0 : ℕ → ℝ
  /-- The range constant in Lagarias-Odlyzko Theorem 1.3. -/
  K : ℝ
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
  /-- Lagarias-Odlyzko: the Dedekind zero-free region. -/
  zero_free : DedekindZeroFreeRegion beta0 zeroRealPart cz discLog
  /-- Stark's exceptional-zero bound. -/
  stark : StarkExceptionalZeroBound beta0 F discLog
  /-- Lagarias-Odlyzko: the range condition. -/
  cheb_range : EffectiveChebotarevRange K x degree discLog
  /-- Lagarias-Odlyzko: the explicit error. -/
  cheb_error : LagariasOdlyzkoError C cZ x degree error
  /-- Lagarias-Odlyzko: the cumulative Chebotarev count. -/
  cheb_count : EffectiveChebotarev count main error
  /-- The Chebotarev main term is the exceptional-zero logarithmic integral. -/
  main_eq : ∀ n, main n = (1 / 2) * (liX n - liBeta0 n)
  /-- The inert count contains the counted nonidentity class. -/
  inert_ge_count : ∀ n, count n ≤ inertCount n
  /-- Stark's bound converted to the dyadic bracket. -/
  bracket : LogIntegralBracket cbr x F T liX liBeta0
  /-- The Chebotarev error is negligible against the bracket. -/
  error_negligible : ChebotarevErrorNegligible cbr x F T error
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

namespace EffectiveChebotarevInputs

variable (I : EffectiveChebotarevInputs)

/-- The combined probe constant `csel * cbr / 4`: one half from the cumulative
inert count, one quarter from the two `1/8` negligibility budgets. -/
noncomputable def cProbe : ℝ := I.csel * I.cbr / 4

/-- The L34 loss charged to the C5 ledger. -/
noncomputable def loss : ℕ → ℝ :=
  excessLoss I.actualMiss (maskFailure I.hstar I.m) allowedFailure

/-- The probe miss probability is nonnegative. -/
theorem probeMiss_nonneg (n : ℕ) :
    0 ≤ probeMiss I.classCount I.pTrial I.R n := by
  unfold probeMiss
  exact mul_nonneg (I.classCount_pos n).le (Real.exp_pos _).le

/-- The mask failure is nonnegative. -/
theorem maskFailure_nonneg (n : ℕ) : 0 ≤ maskFailure I.hstar I.m n := by
  unfold maskFailure
  exact Real.rpow_nonneg (by norm_num) _

/-- The loss is nonnegative: it is the positive part of the excess. -/
theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n := by
  unfold loss excessLoss
  exact le_max_left 0 _

/-! ### 2.1 The mask compression and the `1/128` slack -/

/-- The compressed mask failure is at most `2^{-7} = 1/128`. -/
theorem maskFailure_le_allowed (n : ℕ) :
    maskFailure I.hstar I.m n ≤ 1 / 128 := by
  have hbits : I.hstar n - I.m n ≤ (-7 : ℝ) := by
    have := I.mask_bits n
    linarith
  calc
    maskFailure I.hstar I.m n = (2 : ℝ) ^ (I.hstar n - I.m n) := rfl
    _ ≤ (2 : ℝ) ^ (-7 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hbits
    _ = 1 / 128 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

/-- The ledger loss is a genuine part of the total failure: it never exceeds
`actualMiss + maskFailure`.  The `1/128` slack is subtracted only because the
paper's success statement already accepts it. -/
theorem loss_le_failure (n : ℕ) :
    I.loss n ≤ I.actualMiss n + maskFailure I.hstar I.m n := by
  unfold loss excessLoss
  apply max_le
  · exact add_nonneg (I.actualMiss_nonneg n) (I.maskFailure_nonneg n)
  · have h : 0 ≤ allowedFailure n := by
      unfold allowedFailure
      norm_num
    linarith

/-- **The union bound in exponential form.**  The actual miss probability is at
most the probe miss `classCount * exp (-R pTrial)`. -/
theorem actualMiss_le_probeMiss (n : ℕ) :
    I.actualMiss n ≤ probeMiss I.classCount I.pTrial I.R n := by
  have hpow := one_sub_pow_le_exp_neg (I.pTrial n) (I.pTrial_nonneg n)
    (I.pTrial_le_one n) (I.R n)
  calc
    I.actualMiss n ≤ I.classCount n * (1 - I.pTrial n) ^ (I.R n) :=
      I.union_bound n
    _ ≤ I.classCount n * Real.exp (-((I.R n : ℝ) * I.pTrial n)) :=
      mul_le_mul_of_nonneg_left hpow (I.classCount_pos n).le
    _ = probeMiss I.classCount I.pTrial I.R n := rfl

/-- **The loss is at most the probe miss.**  The mask failure is absorbed by
the paper's `1/128` slack, so only the excess over the slack is charged. -/
theorem loss_le_probeMiss (n : ℕ) :
    I.loss n ≤ probeMiss I.classCount I.pTrial I.R n := by
  have hmask := I.maskFailure_le_allowed n
  have hprobe := I.probeMiss_nonneg n
  have hactual := I.actualMiss_le_probeMiss n
  unfold loss excessLoss allowedFailure
  apply max_le hprobe
  linarith

/-! ### 2.2 The Chebotarev + Stark + negligibility chain -/

/-- Stark's gap, in the form consumed by the dyadic bracket. -/
theorem stark_gap (n : ℕ) :
    1 / (4 * I.F n * I.discLog n) ≤ 1 - I.beta0 n :=
  (I.stark n).2

/-- The zero-free region in point form: any zero whose real part exceeds
`1 - c_z/log|Δ_E|` must be the exceptional zero `β₀`. -/
theorem zero_free_above (n : ℕ) :
    1 - I.cz / I.discLog n < I.zeroRealPart n → I.zeroRealPart n ≤ I.beta0 n :=
  I.zero_free.2 n

/-- The Lagarias-Odlyzko range condition. -/
theorem range_condition (n : ℕ) :
    I.K * I.degree n * (I.discLog n) ^ 2 ≤ Real.log (I.x n) :=
  I.cheb_range.2 n

/-- **The cumulative inert lower bound from effective Chebotarev.**  The
Chebotarev count for the nonidentity class lies within `error` of
`½ (Li x - Li x^{β₀})`, and the inert count contains that class. -/
theorem inert_lower (n : ℕ) :
    (1 / 2) * (I.liX n - I.liBeta0 n) - I.error n ≤ I.inertCount n := by
  have hcount := (abs_le.mp (I.cheb_count n)).1
  have hmain := I.main_eq n
  have hge := I.inert_ge_count n
  rw [hmain] at hcount
  linarith

/-- The degree-one inert count still satisfies the bracket with one quarter of
the constant: one half from the inert count, minus the two `1/8` budgets. -/
theorem degreeOneInert_lower (n : ℕ) :
    bracketTerm (I.cbr / 4) I.x I.F I.T n ≤ I.degreeOneInert n := by
  let B := bracketTerm I.cbr I.x I.F I.T n
  have hbracket : B ≤ I.liX n - I.liBeta0 n := I.bracket.2 n
  have hinert : (1 / 2) * (I.liX n - I.liBeta0 n) - I.error n ≤ I.inertCount n :=
    I.inert_lower n
  have herror : I.error n ≤ B / 8 := by
    have := I.error_negligible n
    have h8 : bracketTerm (I.cbr / 8) I.x I.F I.T n = B / 8 := by
      unfold B bracketTerm
      ring
    rw [h8] at this
    exact this
  have hloss : I.degree n * Real.sqrt (I.x n) ≤ B / 8 := by
    have := I.degree_one_loss n
    have h8 : bracketTerm (I.cbr / 8) I.x I.F I.T n = B / 8 := by
      unfold B bracketTerm
      ring
    rw [h8] at this
    exact this
  have hred : I.inertCount n - I.degree n * Real.sqrt (I.x n) ≤ I.degreeOneInert n :=
    I.degree_one_reduction n
  have hquarter : bracketTerm (I.cbr / 4) I.x I.F I.T n = B / 4 := by
    unfold B bracketTerm
    ring
  rw [hquarter]
  nlinarith

/-! ### 2.3 The `1/(d F T⁶)` selection bound -/

/-- **The probe-per-trial lower bound.**  Composing the degree-one inert count
with the `csel/(d x)` selection probability gives
`(csel cbr / 4)/(d F T⁶) ≤ pTrial`. -/
theorem probe_lower (n : ℕ) :
    I.cProbe / (I.degree n * I.F n * I.T n ^ 6) ≤ I.pTrial n := by
  have hdeg := I.degreeOneInert_lower n
  have hsel := I.selection.2 n
  have hcsel : 0 ≤ I.csel := (I.selection.1).le
  have hx : 0 < I.x n := I.x_pos n
  have hd : 0 < I.degree n := I.degree_pos n
  have hF : 0 < I.F n := I.F_pos n
  have hT : 0 < I.T n := I.T_pos n
  have hnum : I.csel * bracketTerm (I.cbr / 4) I.x I.F I.T n ≤
      I.csel * I.degreeOneInert n :=
    mul_le_mul_of_nonneg_left hdeg hcsel
  have hfrac :
      I.csel * bracketTerm (I.cbr / 4) I.x I.F I.T n / (I.degree n * I.x n) ≤
        I.csel * I.degreeOneInert n / (I.degree n * I.x n) :=
    (div_le_div_iff_of_pos_right (by positivity)).mpr hnum
  have heq :
      I.csel * bracketTerm (I.cbr / 4) I.x I.F I.T n / (I.degree n * I.x n) =
        I.csel * I.cbr / 4 / (I.degree n * I.F n * I.T n ^ 6) := by
    unfold bracketTerm
    field_simp [hx.ne', hd.ne', hF.ne', hT.ne']
  calc
    I.cProbe / (I.degree n * I.F n * I.T n ^ 6)
        = I.csel * bracketTerm (I.cbr / 4) I.x I.F I.T n /
            (I.degree n * I.x n) := by
          rw [show I.cProbe = I.csel * I.cbr / 4 from rfl]
          exact heq.symm
    _ ≤ I.csel * I.degreeOneInert n / (I.degree n * I.x n) := hfrac
    _ ≤ I.pTrial n := hsel

/-! ### 2.4 The probe miss bound -/

/-- **The probe miss is `≤ exp (-2H)`.**  The probe budget `R = F T¹⁰` and the
selection bound give `R pTrial ≥ cProbe T³`; the polynomial bound `h* = O(T³)`
and `scale_cubic` make this dominate `h* log 2 + 2H`. -/
theorem probeMiss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      probeMiss I.classCount I.pTrial I.R n ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [I.scale_cubic] with n hcubic
  have hprobe := I.probe_lower n
  have hT : 0 < I.T n := I.T_pos n
  have hF : 0 < I.F n := I.F_pos n
  have hd : 0 < I.degree n := I.degree_pos n
  have hcProbe : 0 < I.cProbe := by
    unfold cProbe
    exact div_pos (mul_pos I.selection.1 I.bracket.1) (by norm_num)
  -- `R p ≥ cProbe T⁴ / d`
  have hRp1 : I.cProbe * I.T n ^ 4 / I.degree n ≤
      (I.R n : ℝ) * I.pTrial n := by
    rw [I.budget n]
    have hEq :
        I.cProbe * I.T n ^ 4 / I.degree n =
          (I.F n * I.T n ^ 10) *
            (I.cProbe / (I.degree n * I.F n * I.T n ^ 6)) := by
      field_simp [hT.ne', hF.ne', hd.ne']
    rw [hEq]
    exact mul_le_mul_of_nonneg_left hprobe (by positivity)
  -- `cProbe T³ ≤ R p`, since `d ≤ T`
  have hRp : I.cProbe * I.T n ^ 3 ≤ (I.R n : ℝ) * I.pTrial n := by
    have hT4 : I.cProbe * I.T n ^ 3 = I.cProbe * I.T n ^ 4 / I.T n := by
      field_simp [hT.ne']
    have hmono : I.cProbe * I.T n ^ 4 / I.T n ≤
        I.cProbe * I.T n ^ 4 / I.degree n :=
      div_le_div_of_nonneg_left (mul_nonneg hcProbe.le (by positivity)) hd
        (I.degree_le_T n)
    exact hT4.trans_le (hmono.trans hRp1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstar_le : I.hstar n ≤ I.Ch * I.T n ^ 3 := I.hstar_poly.2 n
  have h1 : I.hstar n * Real.log 2 ≤
      (I.Ch * I.T n ^ 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hstar_le hlog2.le
  have h2 : (I.Ch * I.T n ^ 3) * Real.log 2 ≤
      I.csel * I.cbr / 4 * I.T n ^ 3 := by
    have hT3 : 0 ≤ I.T n ^ 3 := by positivity
    nlinarith [I.constant_margin]
  have hExp : I.hstar n * Real.log 2 + 2 * scale n ≤
      (I.R n : ℝ) * I.pTrial n := by
    calc
      I.hstar n * Real.log 2 + 2 * scale n
          ≤ (I.Ch * I.T n ^ 3) * Real.log 2 +
              (I.csel * I.cbr / 4 - I.Ch * Real.log 2) * I.T n ^ 3 :=
            add_le_add h1 hcubic
      _ = I.csel * I.cbr / 4 * I.T n ^ 3 := by ring
      _ ≤ (I.R n : ℝ) * I.pTrial n := by
        rw [show I.csel * I.cbr / 4 = I.cProbe from rfl]
        exact hRp
  have hlogclass : Real.log (I.classCount n) ≤ I.hstar n * Real.log 2 := by
    calc
      Real.log (I.classCount n) ≤ Real.log ((2 : ℝ) ^ (I.hstar n)) :=
        Real.log_le_log (I.classCount_pos n) (I.class_le n)
      _ = I.hstar n * Real.log 2 := by
        rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  calc
    probeMiss I.classCount I.pTrial I.R n
        = I.classCount n * Real.exp (-((I.R n : ℝ) * I.pTrial n)) := rfl
    _ ≤ Real.exp (I.hstar n * Real.log 2) *
          Real.exp (-((I.R n : ℝ) * I.pTrial n)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        rw [← Real.exp_log (I.classCount_pos n)]
        exact Real.exp_le_exp.mpr hlogclass
    _ = Real.exp (I.hstar n * Real.log 2 - (I.R n : ℝ) * I.pTrial n) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(2 : ℝ) * scale n) :=
        Real.exp_le_exp.mpr (by linarith)

/-! ### 2.5 The ledger and the paper rate -/

/-- **The L34 ledger slot**: the excess loss is eventually `≤ exp (-2H)`. -/
theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [I.probeMiss_le_ledger] with n hprobe
  exact (I.loss_le_probeMiss n).trans hprobe

/-- **The manuscript's own rate.**  Since the loss is at most the probe miss,
which is `≤ exp (-2H)`, it is also `≤ exp (-H/log H)` for large `H`.  This is
the `RatedLeaf.paper` field; it is weaker than the ledger by design. -/
theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ exp (-(1 * paperRate n)) := by
  filter_upwards [I.loss_le_ledger, scale_grows.eventually_ge_atTop (Real.exp 1)]
    with n hledger hs
  have hs0 : 0 < scale n := lt_of_lt_of_le (Real.exp_pos 1) hs
  have hlog1 : 1 ≤ Real.log (scale n) := by
    have h := Real.log_le_log (Real.exp_pos 1) hs
    simpa [Real.log_exp] using h
  have hlogpos : 0 < Real.log (scale n) := lt_of_lt_of_le zero_lt_one hlog1
  have hrate : paperRate n ≤ 2 * scale n := by
    unfold paperRate
    rw [div_le_iff₀ hlogpos]
    nlinarith [hs0, hlog1]
  exact hledger.trans (Real.exp_le_exp.mpr (by nlinarith))

/-- **The literal `RatedLeaf`.**  `paper` is the manuscript's `H/log H` rate,
`ledger` is the explicit `D^{-2}` estimate obtained from the probe budget. -/
noncomputable def ratedLeaf : RatedLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  rate := paperRate
  c := 1
  c_pos := by norm_num
  paper := I.loss_le_paper
  ledger := I.loss_le_ledger

/-- The `RatedLeaf.slot` of the constructed leaf is exactly the proved ledger. -/
theorem ratedLeaf_slot :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  I.ratedLeaf.slot

end EffectiveChebotarevInputs

/-! ## Axiom audit -/

#print axioms EffectiveChebotarevInputs.probeMiss_nonneg
#print axioms EffectiveChebotarevInputs.maskFailure_nonneg
#print axioms EffectiveChebotarevInputs.loss_nonneg
#print axioms EffectiveChebotarevInputs.maskFailure_le_allowed
#print axioms EffectiveChebotarevInputs.loss_le_failure
#print axioms one_sub_pow_le_exp_neg
#print axioms EffectiveChebotarevInputs.actualMiss_le_probeMiss
#print axioms EffectiveChebotarevInputs.loss_le_probeMiss
#print axioms EffectiveChebotarevInputs.stark_gap
#print axioms EffectiveChebotarevInputs.zero_free_above
#print axioms EffectiveChebotarevInputs.range_condition
#print axioms EffectiveChebotarevInputs.inert_lower
#print axioms EffectiveChebotarevInputs.degreeOneInert_lower
#print axioms EffectiveChebotarevInputs.probe_lower
#print axioms EffectiveChebotarevInputs.probeMiss_le_ledger
#print axioms EffectiveChebotarevInputs.loss_le_ledger
#print axioms EffectiveChebotarevInputs.loss_le_paper
#print axioms EffectiveChebotarevInputs.ratedLeaf
#print axioms EffectiveChebotarevInputs.ratedLeaf_slot

end Cogentic.RandomizedL34

/-! ## 3. Integration with the paper-leaf ledger -/

namespace Cogentic.RandomizedPaperLeafStatements

open Filter Real
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic

/-- Replace the L34 field of `PaperAnalyticAssumptions` by a `RatedLeaf` derived
from the effective-Chebotarev inputs.  All other paper leaves are untouched. -/
def PaperAnalyticAssumptions.withL34
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (L : RatedLeaf) :
    PaperAnalyticAssumptions E C :=
  { P with l34 := L }

@[simp] theorem PaperAnalyticAssumptions.withL34_l34
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (L : RatedLeaf) :
    (P.withL34 L).l34 = L := rfl

@[simp] theorem PaperAnalyticAssumptions.withL34_slots_characterSeparation
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (L : RatedLeaf) :
    (P.withL34 L).slots .characterSeparation = L.loss := rfl

/-- The replaced paper assumption still satisfies the L34 ledger slot. -/
theorem PaperAnalyticAssumptions.withL34_slot
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (L : RatedLeaf) :
    ∀ᶠ n : ℕ in atTop,
      (P.withL34 L).slots .characterSeparation n ≤ exp (-(2 : ℝ) * scale n) :=
  L.slot

/-- Replacing L34 leaves every other slot unchanged. -/
theorem PaperAnalyticAssumptions.withL34_slots_of_ne
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (L : RatedLeaf) {k : C5Leaf}
    (hk : k ≠ C5Leaf.characterSeparation) :
    (P.withL34 L).slots k = P.slots k := by
  cases k <;>
    simp_all [PaperAnalyticAssumptions.slots, PaperAnalyticAssumptions.withL34]

/-- Replacing L34 preserves every other ledger slot: the unaffected slots are
still those of `P`, and the L34 slot is the new leaf's `slot`. -/
theorem PaperAnalyticAssumptions.withL34_slot_le
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (L : RatedLeaf) (k : C5Leaf) :
    ∀ᶠ n : ℕ in atTop,
      (P.withL34 L).slots k n ≤ exp (-(2 : ℝ) * scale n) := by
  by_cases hk : k = C5Leaf.characterSeparation
  · subst k
    simpa [PaperAnalyticAssumptions.slots, PaperAnalyticAssumptions.withL34]
      using L.slot
  · rw [PaperAnalyticAssumptions.withL34_slots_of_ne P L hk]
    exact P.slot_le k

#print axioms PaperAnalyticAssumptions.withL34
#print axioms PaperAnalyticAssumptions.withL34_l34
#print axioms PaperAnalyticAssumptions.withL34_slots_characterSeparation
#print axioms PaperAnalyticAssumptions.withL34_slot
#print axioms PaperAnalyticAssumptions.withL34_slots_of_ne
#print axioms PaperAnalyticAssumptions.withL34_slot_le

end Cogentic.RandomizedPaperLeafStatements
