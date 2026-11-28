import Cogentic.RandomizedL34Sides
import Cogentic.RandomizedL34Range
import Cogentic.RandomizedL34ClassicalStark
import Cogentic.RandomizedL34DedekindStrip

/-!
# L34: the Chebotarev sides reduced to explicit counting inputs

`Cogentic.RandomizedL34Sides` assembled `L34SidesCore` from a one-sided
Chebotarev count.  The remaining fields of that core were still parameterised by
arbitrary functions `x`, `hstar`, `m`, and by the paper-level `Prop`s
`ChebotarevErrorNegligible`, `DegreeOneLossNegligible`, `ClassCountBound`,
`ClassCountPolynomial` and `MaskCompressionBits`.  This file fixes the
incarnation `x = 2^(T^6)`, eliminates `hstar`, `m` and the mask/class-count
bookkeeping, and isolates the genuinely analytic Chebotarev estimates as the
smallest explicit `Prop`s.

## The reductions

1. **Cutoff.**  `cutoff T = fun n => 2^((T n)^6)`.  Positivity, the logarithm
   `log (cutoff T n) = (T n)^6 log 2`, and the square-root
   `sqrt (cutoff T n) = 2^((T n)^6 / 2)` are proved unconditionally.

2. **Range.**  `ChebotarevT6RangeInput K T degree discLog` gives the paper's
   range condition for `x = 2^(T^6)` by the existing
   `ChebotarevT6RangeInput.toChebotarevRangeInput`; no new analytic input is
   needed.

3. **Error slack.**  `ChebotarevResidualInput` is the canonical error slack
   `|count - ½(Li x - Li x^β₀)| ≤ lagariasOdlyzkoError C cZ x degree`, with the
   two positivity constants.  It is equivalent to `ChebotarevErrorSlack`
   (`chebotarevResidualInput_iff_slack`) and gives the one-sided
   `ChebotarevLowerInput` (`…toLowerInput`).

4. **Error negligibility.**  With `x = 2^(T^6)` the Lagarias-Odlyzko envelope
   is `C 2^(T^6) exp (-cZ sqrt ((T^6 log 2)/(2d)))`.  Since `2^(T^6) > 0`, the
   error-negligibility `Prop` is *exactly* the scalar inequality
   `C F T^6 exp (-cZ sqrt ((T^6 log 2)/(2d))) ≤ cbr/8`
   (`chebotarevErrorNegligible_iff_scalar`).  This is the smallest explicit
   form: it has cancelled the common positive factor `x`.

5. **Discarded ideals.**  Similarly, `degree sqrt x ≤ (cbr/8) x/(F T^6)` is
   exactly the scalar inequality
   `degree F T^6 2^(T^6/2) ≤ (cbr/8) 2^(T^6)`
   (`degreeOneLossNegligible_iff_scalar`).  The square-root identity above is
   the only arithmetic used.

6. **Class count and mask.**  Instead of carrying `hstar`, `m`, Lemma E.2 and
   the mask-compression bits separately, the file takes the single counting
   input `classCount ≤ 2^(Ch T^3)` (`ClassCountCubicInput`).  Setting
   `hstar = Ch T^3` and `m = hstar + 7` makes `ClassCountBound`,
   `ClassCountPolynomial` and `MaskCompressionBits` definitional, and makes the
   mask failure exactly `1/128`.  Consequently the ledger loss is *exactly* the
   actual probe miss (`toL34SidesCore_loss`), a genuine nonzero loss whenever
   the probe stage has a positive failure probability.

7. **Inert / detection / probe counts.**  The explicit counting inputs are
   `count ≤ inertCount`, the degree-one reduction
   `inertCount - degree sqrt x ≤ degreeOneInert`, and the per-ideal selection
   `csel degreeOneInert/(degree x) ≤ pTrial`.  The composed detection bound
   `csel cbr/4 / (degree F T^6) ≤ pTrial` is proved unconditionally from these
   plus the error-negligibility and discarded-ideal bounds
   (`L34ChebotarevSidesInputs.probeLower`), reusing the elementary chain of
   `Cogentic.RandomizedL34Sub`.

8. **Probe count.**  The paper's budget is kept as the explicit input
   `ProbeBudget R F T`, i.e. `R = F T^10`.

## The bundle

`L34ChebotarevSidesInputs` collects these inputs.  Its `toL34SidesCore`
constructs a genuine `L34SidesCore`, and `ratedLeaf` constructs the literal
`RatedLeaf`.  The ledger slot and the manuscript rate are inherited from
`L34SidesCore`.

The unavailable Chebotarev estimates are *not* asserted: they are the explicit
`Prop` fields `ChebotarevResidualInput`, `ChebotarevErrorScalarBound` and
`DegreeLossScalarBound` (plus the analytic `LogIntegralBracket`), each with a
proved reduction to its paper-level form.  No `sorry`, `admit`, `axiom`, or
`native_decide` is used, and no loss, count, error or mass is set to zero.
-/

namespace Cogentic.RandomizedL34ChebotarevSides

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The cutoff `x = 2^(T^6)` -/

/-- The paper's cutoff `x = 2^(T^6)`. -/
abbrev cutoff (T : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((T n) ^ 6)

/-- The cutoff is positive. -/
theorem cutoff_pos (T : ℕ → ℝ) (n : ℕ) : 0 < cutoff T n :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The logarithm of the cutoff is `(T n)^6 log 2`. -/
theorem cutoff_log (T : ℕ → ℝ) (n : ℕ) :
    Real.log (cutoff T n) = (T n) ^ 6 * Real.log 2 := by
  unfold cutoff
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

/-- The square root of the cutoff is `2^((T n)^6 / 2)`.  This is the only
square-root arithmetic used by the discarded-ideal reduction. -/
theorem cutoff_sqrt (T : ℕ → ℝ) (n : ℕ) :
    Real.sqrt (cutoff T n) = (2 : ℝ) ^ ((T n) ^ 6 / 2) := by
  rw [Real.sqrt_eq_rpow]
  unfold cutoff
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((T n) ^ 6) (1 / 2)]
  congr 1
  ring

/-- The paper case: `x = 2^(T^6)` is the prerequisite cutoff of
`ChebotarevT6RangeInput`. -/
theorem cutoff_eq_rpow (T : ℕ → ℝ) :
    cutoff T = fun n => (2 : ℝ) ^ ((T n) ^ 6) :=
  rfl

/-! ## 2. The Chebotarev error slack -/

/-- **The smallest explicit Chebotarev error slack.**  The cumulative count is
within the canonical Lagarias-Odlyzko envelope of its main term
`½ (Li x - Li x^{β₀})`.  The existential witness of `ChebotarevErrorSlack` is
replaced by the canonical absolute residual. -/
structure ChebotarevResidualInput (C cZ : ℝ) (x degree : ℕ → ℝ)
    (count liX liBeta0 : ℕ → ℝ) : Prop where
  /-- The error constant is positive. -/
  C_pos : 0 < C
  /-- The error exponent is positive. -/
  cZ_pos : 0 < cZ
  /-- `|count - ½(Li x - Li x^{β₀})| ≤ lagariasOdlyzkoError C cZ x degree`. -/
  residual : ∀ n,
    |count n - mainOf liX liBeta0 n| ≤
      lagariasOdlyzkoError C cZ x degree n

namespace ChebotarevResidualInput

/-- The canonical residual is nonnegative. -/
theorem residual_nonneg {C cZ : ℝ} {x degree count liX liBeta0 : ℕ → ℝ}
    (H : ChebotarevResidualInput C cZ x degree count liX liBeta0) (n : ℕ) :
    0 ≤ lagariasOdlyzkoError C cZ x degree n - |count n - mainOf liX liBeta0 n| := by
  have h := abs_nonneg (count n - mainOf liX liBeta0 n)
  linarith [H.residual n]

/-- The residual input gives the one-sided Chebotarev lower bound. -/
theorem toLowerInput {C cZ : ℝ} {x degree count liX liBeta0 : ℕ → ℝ}
    (H : ChebotarevResidualInput C cZ x degree count liX liBeta0) :
    ChebotarevLowerInput C cZ x degree count liX liBeta0 where
  C_pos := H.C_pos
  cZ_pos := H.cZ_pos
  lower := by
    intro n
    have h := (abs_le.mp (H.residual n)).1
    unfold mainOf at h ⊢
    linarith

/-- The residual input is exactly the slack Chebotarev error. -/
theorem toSlack {C cZ : ℝ} {x degree count liX liBeta0 : ℕ → ℝ}
    (H : ChebotarevResidualInput C cZ x degree count liX liBeta0) :
    ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0) :=
  chebotarevErrorSlack_iff_residual_le.mpr
    ⟨H.C_pos, H.cZ_pos, fun n => H.residual n⟩

/-- Every slack Chebotarev error yields the canonical residual input. -/
theorem ofSlack {C cZ : ℝ} {x degree count liX liBeta0 : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0)) :
    ChebotarevResidualInput C cZ x degree count liX liBeta0 where
  C_pos := E.C_pos
  cZ_pos := E.cZ_pos
  residual := (chebotarevErrorSlack_iff_residual_le.mp E).2.2

end ChebotarevResidualInput

/-- **The canonical residual and the slack bundle are equivalent.**  The
existential error of `ChebotarevErrorSlack` therefore adds no content. -/
theorem chebotarevResidualInput_iff_slack {C cZ : ℝ}
    {x degree count liX liBeta0 : ℕ → ℝ} :
    ChebotarevResidualInput C cZ x degree count liX liBeta0 ↔
      ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0) :=
  ⟨ChebotarevResidualInput.toSlack, ChebotarevResidualInput.ofSlack⟩

/-! ## 3. The Chebotarev error at the concrete cutoff -/

/-- The Lagarias-Odlyzko envelope at `x = 2^(T^6)`. -/
theorem lagariasOdlyzkoError_cutoff {C cZ : ℝ} {T degree : ℕ → ℝ} (n : ℕ) :
    lagariasOdlyzkoError C cZ (cutoff T) degree n =
      C * cutoff T n *
        Real.exp (-(cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 /
          (2 * degree n)))) := by
  unfold lagariasOdlyzkoError
  rw [cutoff_log]

/-- The scaled error `exp (-cZ sqrt ((T^6 log 2)/(2d)))`, the factor left after
cancelling `x = 2^(T^6)`. -/
def scaledError (cZ : ℝ) (T degree : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * degree n))))

/-- **The smallest explicit error-negligibility input.**  After cancelling the
positive common factor `x = 2^(T^6)`, the Chebotarev error is bounded by
`cbr/8` of `x/(F T^6)` exactly when
`C F T^6 exp (-cZ sqrt ((T^6 log 2)/(2d))) ≤ cbr/8`. -/
def ChebotarevErrorScalarBound (C cZ cbr : ℝ) (F T degree : ℕ → ℝ) : Prop :=
  ∀ n, C * (F n * T n ^ 6) * scaledError cZ T degree n ≤ cbr / 8

/-- Pointwise form of the error-negligibility reduction. -/
theorem error_le_eighth_bracket_cutoff_iff {C cZ cbr : ℝ} {F T degree : ℕ → ℝ}
    {n : ℕ} (hF : 0 < F n) (hT : 0 < T n) :
    lagariasOdlyzkoError C cZ (cutoff T) degree n ≤
        bracketTerm (cbr / 8) (cutoff T) F T n ↔
      C * (F n * T n ^ 6) * scaledError cZ T degree n ≤ cbr / 8 := by
  rw [lagariasOdlyzkoError_cutoff]
  unfold bracketTerm scaledError
  set x := cutoff T n with hxdef
  set D := F n * T n ^ 6 with hDdef
  set E := Real.exp (-(cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 /
    (2 * degree n)))) with hEdef
  have hx : 0 < x := by
    rw [hxdef]
    exact cutoff_pos T n
  have hD : 0 < D := by
    rw [hDdef]
    exact mul_pos hF (pow_pos hT 6)
  constructor
  · intro h
    have h1 : C * x * E * D ≤ (cbr / 8 * x / D) * D :=
      mul_le_mul_of_nonneg_right h hD.le
    have h2 : (cbr / 8 * x / D) * D = cbr / 8 * x := by
      field_simp [hD.ne']
    have h3 : C * x * E * D = (C * (F n * T n ^ 6) * E) * x := by
      rw [hDdef]
      ring
    rw [h2, h3] at h1
    exact (mul_le_mul_iff_of_pos_right hx).mp h1
  · intro h
    have h1 : (C * (F n * T n ^ 6) * E) * x ≤ (cbr / 8) * x :=
      mul_le_mul_of_nonneg_right h hx.le
    have h3 : (C * (F n * T n ^ 6) * E) * x = C * x * E * D := by
      rw [hDdef]
      ring
    rw [h3] at h1
    rw [le_div_iff₀ hD]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1

/-- **The error-negligibility `Prop` is exactly the scalar input.**  This is
the unconditional arithmetic reduction: no analytic content is used beyond the
definition of the Lagarias-Odlyzko envelope and `log (2^s) = s log 2`. -/
theorem chebotarevErrorNegligible_iff_scalar {C cZ cbr : ℝ} {F T degree : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n) :
    ChebotarevErrorNegligible cbr (cutoff T) F T
        (lagariasOdlyzkoError C cZ (cutoff T) degree) ↔
      ChebotarevErrorScalarBound C cZ cbr F T degree := by
  unfold ChebotarevErrorNegligible ChebotarevErrorScalarBound
  exact forall_congr' (fun n => error_le_eighth_bracket_cutoff_iff (hF n) (hT n))

/-! ## 4. The discarded small / higher-degree ideals at the concrete cutoff -/

/-- **The smallest explicit discarded-ideal input.**  After using
`sqrt (2^(T^6)) = 2^(T^6/2)` and cancelling `F T^6`, the discarded-ideal
inequality is `degree F T^6 2^(T^6/2) ≤ (cbr/8) 2^(T^6)`. -/
def DegreeLossScalarBound (cbr : ℝ) (degree F T : ℕ → ℝ) : Prop :=
  ∀ n, degree n * F n * T n ^ 6 * (2 : ℝ) ^ ((T n) ^ 6 / 2) ≤
    (cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6)

/-- Pointwise form of the discarded-ideal reduction. -/
theorem degreeOneLoss_cutoff_iff {cbr : ℝ} {degree F T : ℕ → ℝ} {n : ℕ}
    (hF : 0 < F n) (hT : 0 < T n) :
    degree n * Real.sqrt (cutoff T n) ≤
        bracketTerm (cbr / 8) (cutoff T) F T n ↔
      degree n * F n * T n ^ 6 * (2 : ℝ) ^ ((T n) ^ 6 / 2) ≤
        (cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6) := by
  rw [cutoff_sqrt]
  unfold bracketTerm
  set x := (2 : ℝ) ^ ((T n) ^ 6) with hxdef
  set D := F n * T n ^ 6 with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    exact mul_pos hF (pow_pos hT 6)
  have hleft : degree n * (2 : ℝ) ^ ((T n) ^ 6 / 2) * D =
      degree n * F n * T n ^ 6 * (2 : ℝ) ^ ((T n) ^ 6 / 2) := by
    rw [hDdef]
    ring
  constructor
  · intro h
    rw [le_div_iff₀ hD] at h
    rw [hleft] at h
    simpa [hxdef] using h
  · intro h
    rw [le_div_iff₀ hD]
    rw [hleft]
    simpa [hxdef] using h

/-- **The discarded-ideal `Prop` is exactly the scalar input.** -/
theorem degreeOneLossNegligible_iff_scalar {cbr : ℝ} {degree F T : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n) :
    DegreeOneLossNegligible cbr (cutoff T) degree F T ↔
      DegreeLossScalarBound cbr degree F T := by
  unfold DegreeOneLossNegligible DegreeLossScalarBound
  exact forall_congr' (fun n => degreeOneLoss_cutoff_iff (hF n) (hT n))

/-! ## 5. The class count and the mask -/

/-- **The smallest explicit class-count input.**  Lemma E.2 and the polynomial
bound `h* = O(T^3)` are combined into `classCount ≤ 2^(Ch T^3)`, with `Ch > 0`.
The auxiliary sequence `h*` and the compression length `m` are reconstructed
below as `Ch T^3` and `Ch T^3 + 7`. -/
structure ClassCountCubicInput (Ch : ℝ) (classCount T : ℕ → ℝ) : Prop where
  /-- The polynomial constant is positive. -/
  Ch_pos : 0 < Ch
  /-- `classCount ≤ 2^(Ch T^3)`. -/
  cubic : ∀ n, classCount n ≤ (2 : ℝ) ^ (Ch * (T n) ^ 3)

namespace ClassCountCubicInput

/-- The canonical `h* = Ch T^3` satisfies Lemma E.2. -/
theorem classCountBound {Ch : ℝ} {classCount T : ℕ → ℝ}
    (H : ClassCountCubicInput Ch classCount T) :
    ClassCountBound classCount (fun n => Ch * (T n) ^ 3) :=
  H.cubic

/-- The canonical `h* = Ch T^3` satisfies the polynomial bound. -/
theorem classCountPolynomial {Ch : ℝ} {classCount T : ℕ → ℝ}
    (H : ClassCountCubicInput Ch classCount T) :
    ClassCountPolynomial Ch (fun n => Ch * (T n) ^ 3) T :=
  ⟨H.Ch_pos, fun _ => le_rfl⟩

/-- The canonical `m = h* + 7` satisfies the mask-compression budget. -/
theorem maskCompressionBits {Ch : ℝ} {classCount T : ℕ → ℝ}
    (_H : ClassCountCubicInput Ch classCount T) :
    MaskCompressionBits (fun n => Ch * (T n) ^ 3)
      (fun n => Ch * (T n) ^ 3 + 7) :=
  fun _ => le_rfl

/-- With `m = h* + 7` the mask failure is exactly the paper's `1/128`. -/
theorem maskFailure_eq {Ch : ℝ} {classCount T : ℕ → ℝ}
    (_H : ClassCountCubicInput Ch classCount T) (n : ℕ) :
    maskFailure (fun n => Ch * (T n) ^ 3)
      (fun n => Ch * (T n) ^ 3 + 7) n = 1 / 128 :=
  maskFailure_eq_inv128 (fun _ => rfl) n

end ClassCountCubicInput

/-! ## 6. The reduced input bundle -/

/-- **The L34 Chebotarev sides from explicit counting inputs.**

Every analytic Chebotarev estimate is one of the explicit `Prop`s:
`ChebotarevResidualInput` (error slack), `ChebotarevErrorScalarBound`
(error negligibility after cancelling `x`), `LogIntegralBracket` (the
Stark/log-integral bracket), and `DegreeLossScalarBound` (the discarded
ideals).  The counting inputs are the inert containment, the degree-one
reduction, the per-ideal selection, the cubic class count, and the probe
budget `R = F T^10`.  The cutoff is fixed to `2^(T^6)` and the range comes from
`ChebotarevT6RangeInput`. -/
structure L34ChebotarevSidesInputs where
  /-- The possible exceptional real zero `β₀`. -/
  beta0 : ℕ → ℝ
  /-- The real part of a generic zero of `ζ_E`. -/
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
  /-- The range constant. -/
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
  /-- The Dedekind zero-free region in its smallest form. -/
  zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog
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

namespace L34ChebotarevSidesInputs

variable (S : L34ChebotarevSidesInputs)

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

/-- **The range condition in the paper's `T^6` form.**  The existing `T^6`
range input, together with `log (2^(T^6)) = T^6 log 2`, gives
`K d (log |Δ_E|)^2 ≤ T^6 log 2` unconditionally. -/
theorem rangeT6 (n : ℕ) :
    S.K * S.degree n * (S.discLog n) ^ 2 ≤ (S.T n) ^ 6 * Real.log 2 := by
  have h := S.range.toChebotarevRangeInput.range n
  rwa [cutoff_log] at h

/-- The derived error-negligibility `Prop`, obtained from the scalar input by
the unconditional cancellation of `x = 2^(T^6)`. -/
theorem errorNegligible :
    ChebotarevErrorNegligible S.cbr (cutoff S.T) S.F S.T
      (lagariasOdlyzkoError S.C S.cZ (cutoff S.T) S.degree) :=
  (chebotarevErrorNegligible_iff_scalar (C := S.C) (cZ := S.cZ) (cbr := S.cbr)
    (degree := S.degree) S.stark.F_pos S.T_pos).mpr S.error_scalar

/-- The derived discarded-ideal `Prop`, obtained from the scalar input by the
square-root identity and the cancellation of `F T^6`. -/
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

/-- **The composed detection lower bound.**  The degree-one inert count still
contains `bracketTerm (cbr/4)`, and the per-ideal selection probability turns
this into `(csel cbr/4)/(d F T^6) ≤ pTrial`.  This is the unconditional
composition of the explicit inert/detection counting inputs with the two
Chebotarev negligibility estimates. -/
theorem probeLower (n : ℕ) :
    S.csel * S.cbr / 4 / (S.degree n * S.F n * S.T n ^ 6) ≤ S.pTrial n :=
  probe_lower_of_props S.bracket S.errorNegligible S.degreeOneLoss
    S.degree_one_reduction S.inertLower S.selection (cutoff_pos S.T)
    S.range.degree_pos S.stark.F_pos S.T_pos n

/-- The assembled `L34SidesCore`.  The cutoff is `2^(T^6)`, the auxiliary
class-count logarithm is `h* = Ch T^3`, and the compression length is
`m = h* + 7`; the range, class-count and mask fields are discharged
definitionally. -/
noncomputable def toL34SidesCore : L34SidesCore where
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
  zeroRealPart := S.zeroRealPart
  count := S.count
  inertCount := S.inertCount
  degreeOneInert := S.degreeOneInert
  liX := S.liX
  liBeta0 := S.liBeta0
  K := S.K
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
  sides := DedekindSidesInputs.ofSlack S.zeroFree S.stark.toStarkInput
    S.range.toChebotarevRangeInput S.cheb.toSlack
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
canonical compression `m = h* + 7` makes the mask failure exactly the paper's
`1/128` slack, so it cancels against `allowedFailure` and leaves the probe
miss, not a loss set to zero. -/
theorem toL34SidesCore_loss (n : ℕ) :
    S.toL34SidesCore.loss n = S.actualMiss n := by
  unfold L34SidesCore.loss
  exact excessLoss_mask_exact (fun _ => rfl) S.actualMiss_nonneg n

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

/-- The manuscript's slower `exp (-H/log H)` rate for the assembled core. -/
theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      S.toL34SidesCore.loss n ≤ exp (-(1 * paperRate n)) :=
  S.toL34SidesCore.loss_le_paper

/-- The literal `RatedLeaf` of the explicit-input bundle. -/
noncomputable def ratedLeaf : Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  S.toL34SidesCore.ratedLeaf

/-- The leaf's loss is the core loss, hence exactly the actual probe miss. -/
theorem ratedLeaf_loss_eq (n : ℕ) : S.ratedLeaf.loss n = S.actualMiss n :=
  S.toL34SidesCore_loss n

/-- The leaf's loss is nonnegative. -/
theorem ratedLeaf_loss_nonneg (n : ℕ) : 0 ≤ S.ratedLeaf.loss n :=
  S.ratedLeaf.loss_nonneg n

/-- **A genuine nonzero loss.**  Whenever the probe stage actually fails with
positive probability at some index, the assembled loss is positive there.  This
is not a vacuous zero loss: `toL34SidesCore_loss` identifies it with
`actualMiss`. -/
theorem ratedLeaf_loss_pos {n : ℕ} (h : 0 < S.actualMiss n) :
    0 < S.ratedLeaf.loss n := by
  rw [S.ratedLeaf_loss_eq n]
  exact h

/-- The leaf's ledger slot is the proved explicit-input ledger. -/
theorem ratedLeaf_slot :
    ∀ᶠ n : ℕ in atTop,
      S.ratedLeaf.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.ratedLeaf.slot

/-- The manuscript's paper rate holds for the assembled leaf. -/
theorem ratedLeaf_paper :
    ∀ᶠ n : ℕ in atTop,
      S.ratedLeaf.loss n ≤ exp (-(S.ratedLeaf.c * S.ratedLeaf.rate n)) :=
  S.ratedLeaf.paper

end L34ChebotarevSidesInputs

/-! ## 7. A concrete range instance

The paper's concrete case `K ≤ 1`, `T ≥ 2` gives `ChebotarevT6RangeInput`
unconditionally from the parameter bounds (`RandomizedL34Range`).  We record the
specialized constructor so that the only remaining range input is the scalar
comparison `K ≤ 1`. -/

/-- **The concrete `T^6` range input.**  If `K ≤ 1` and `T ≥ 2`, together with
the two parameter bounds `d ≤ T`, `log |Δ_E| ≤ T`, the packaged range input
holds. -/
theorem rangeInput_of_le_one_of_two_le {K : ℝ} {T degree discLog : ℕ → ℝ}
    (hK0 : 0 < K) (hK1 : K ≤ 1)
    (hdeg : ∀ n, 0 < degree n) (hD : ∀ n, 0 < discLog n)
    (hdegT : ∀ n, degree n ≤ T n) (hDT : ∀ n, discLog n ≤ T n)
    (hT : ∀ n, 2 ≤ T n) :
    ChebotarevT6RangeInput K T degree discLog :=
  chebotarevT6RangeInput_of_le_one_of_two_le hK0 hK1 hdeg hD hdegT hDT hT

/-- The concrete range input gives the paper-level range condition at
`x = 2^(T^6)`. -/
theorem effectiveRange_of_le_one_of_two_le {K : ℝ} {T degree discLog : ℕ → ℝ}
    (hK0 : 0 < K) (hK1 : K ≤ 1)
    (hdeg : ∀ n, 0 < degree n) (hD : ∀ n, 0 < discLog n)
    (hdegT : ∀ n, degree n ≤ T n) (hDT : ∀ n, discLog n ≤ T n)
    (hT : ∀ n, 2 ≤ T n) :
    EffectiveChebotarevRange K (cutoff T) degree discLog :=
  (rangeInput_of_le_one_of_two_le hK0 hK1 hdeg hD hdegT hDT hT)
    |>.toEffectiveChebotarevRange

/-! ## 8. Interface to the classical strip input

The zero-free field of the bundle is already the smallest explicit
`DedekindZeroFreeInput`.  The classical strip distance input of
`Cogentic.RandomizedL34DedekindStrip` supplies it once the half-plane at `1`
and a zero sequence are available.  This records that the zero-free side is
also reduced, and keeps the Dedekind-strip interface visible to downstream
users. -/

/-- **The smallest explicit Dedekind strip input supplies the zero-free
field.**  Under the half-plane at `1`, the division-free strip inequality
gives `DedekindZeroFreeInput` for the zero sequence's real parts. -/
theorem zeroFreeInput_of_stripDistance
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (D : DedekindZetaStripDistanceInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog :=
  D.toDedekindZeroFreeInput K hK Z

/-! ## 9. A non-vacuous loss witness -/

/-- **The loss is not forced to be zero.**  The probe stage with one class,
per-trial probability `1/2`, one trial, and actual miss `1/2` satisfies the
union bound and has excess loss `1/2` over the paper's `1/128` slack (the mask
contributes exactly `1/128`, which cancels).  This is the loss shape used by
`L34ChebotarevSidesInputs.toL34SidesCore_loss`. -/
theorem excessLoss_probe_witness :
    excessLoss (fun _ => (1 : ℝ) / 2)
      (maskFailure (fun _ => (0 : ℝ)) (fun _ => 7)) allowedFailure 0 = 1 / 2 := by
  unfold excessLoss allowedFailure
  rw [maskFailure_eq_inv128 (hstar := fun _ => (0 : ℝ)) (m := fun _ => 7)
    (fun _ => by norm_num) 0]
  norm_num

/-- The same probe-stage data satisfy the union bound. -/
theorem probeUnionBound_witness :
    ProbeMissUnionBound (fun _ => (1 : ℝ) / 2) (fun _ => (1 : ℝ) / 2)
      (fun _ => (1 : ℝ)) (fun _ => 1) := by
  intro n
  norm_num

/-! ## Axiom audit -/

#print axioms cutoff_pos
#print axioms cutoff_log
#print axioms cutoff_sqrt
#print axioms cutoff_eq_rpow
#print axioms ChebotarevResidualInput.residual_nonneg
#print axioms ChebotarevResidualInput.toLowerInput
#print axioms ChebotarevResidualInput.toSlack
#print axioms ChebotarevResidualInput.ofSlack
#print axioms chebotarevResidualInput_iff_slack
#print axioms lagariasOdlyzkoError_cutoff
#print axioms error_le_eighth_bracket_cutoff_iff
#print axioms chebotarevErrorNegligible_iff_scalar
#print axioms degreeOneLoss_cutoff_iff
#print axioms degreeOneLossNegligible_iff_scalar
#print axioms ClassCountCubicInput.classCountBound
#print axioms ClassCountCubicInput.classCountPolynomial
#print axioms ClassCountCubicInput.maskCompressionBits
#print axioms ClassCountCubicInput.maskFailure_eq
#print axioms L34ChebotarevSidesInputs.T_pos
#print axioms L34ChebotarevSidesInputs.K_pos
#print axioms L34ChebotarevSidesInputs.degree_pos
#print axioms L34ChebotarevSidesInputs.discLog_pos
#print axioms L34ChebotarevSidesInputs.degree_le_T
#print axioms L34ChebotarevSidesInputs.rangeT6
#print axioms L34ChebotarevSidesInputs.errorNegligible
#print axioms L34ChebotarevSidesInputs.degreeOneLoss
#print axioms L34ChebotarevSidesInputs.chebotarevLowerBound
#print axioms L34ChebotarevSidesInputs.inertLower
#print axioms L34ChebotarevSidesInputs.probeLower
#print axioms L34ChebotarevSidesInputs.toL34SidesCore
#print axioms L34ChebotarevSidesInputs.toL34SidesCore_loss
#print axioms L34ChebotarevSidesInputs.probeMiss_le_ledger
#print axioms L34ChebotarevSidesInputs.loss_le_ledger
#print axioms L34ChebotarevSidesInputs.loss_le_paper
#print axioms L34ChebotarevSidesInputs.ratedLeaf
#print axioms L34ChebotarevSidesInputs.ratedLeaf_loss_eq
#print axioms L34ChebotarevSidesInputs.ratedLeaf_loss_nonneg
#print axioms L34ChebotarevSidesInputs.ratedLeaf_loss_pos
#print axioms L34ChebotarevSidesInputs.ratedLeaf_slot
#print axioms L34ChebotarevSidesInputs.ratedLeaf_paper
#print axioms rangeInput_of_le_one_of_two_le
#print axioms effectiveRange_of_le_one_of_two_le
#print axioms zeroFreeInput_of_stripDistance
#print axioms excessLoss_probe_witness
#print axioms probeUnionBound_witness

end

end Cogentic.RandomizedL34ChebotarevSides
