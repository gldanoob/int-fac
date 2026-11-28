import Cogentic.RandomizedL21_2Remainder
import Cogentic.RandomizedL21_2Tent
import Cogentic.RandomizedL21_2Abel
import Cogentic.RandomizedL21_2PaperLocal

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# L21.2: the assembled `RatedLeaf`

This file closes the L21.2 leaf from the *reduced* analytic data:

* the exact contour identity `zetaShiftContourIdentity` of
  `Cogentic.RandomizedL21_2Remainder`;
* the horizontal/vertical/reference-Perron decomposition
  `perronShiftRemainder_of_bounds`, with the horizontal estimate reduced to the
  single explicit `HorizontalRemainderBound`;
* the vertical-strip line bound `VerticalLineBound` and the reduction
  `perronShift_of_lineBound_of_log_ge`;
* the finite Fourier/tent profile of `Cogentic.RandomizedL21_2Tent`, which
  supplies the Chebyshev count and the mean-square comparison;
* the Abel/partial-summation reduction of `Cogentic.RandomizedL21_2Abel`, which
  defines the Fourier gap as the Abel transform and proves the sup bound;
* the literal short-interval smooth count `ShortIntervalSmoothCountLower` of
  `Cogentic.RandomizedL21_2PaperLocal`, which supplies the density
  normalization.

The assembled leaf is

```
loss n = (# bad sampled centres at band n) / (# sampled centres at band n),
```

a genuine quotient of two explicit counts (never zero by fiat), with the
manuscript rate `exp (-(c/64) * T_X)` and the `D^{-B}` ledger.

## What remains analytic

The explicitly named hypotheses are:

* `RiemannZetaZerosOnLine` (the paper's RH assumption);
* `VerticalLineBound` (the standard `ζ'/ζ` strip bound at `Re s = 2/3`);
* `ReferencePerronBound` (the truncated Perron/Abel approximation);
* `VerticalTailBound` (the elementary vertical-tail cost);
* `HorizontalRemainderBound`, which is equivalent to
  `ContourRemainderBound` by the proved contour identity;

together with the finite-count input `ShortIntervalSmoothCountLower` (a literal
finite-set cardinality lower bound).

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2LeafAssembly

open Filter Real
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Density
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2Fourier
open Cogentic.RandomizedL21_2Abel
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The bounded Perron constant and the horizontal remainder -/

/-- The absolute constant produced by absorbing the logarithm of the contour
height into one extra power of `U = log X`.  With the line bound at exponent
`Cper - 1`, `perronConst Kline` multiplies `v^{2/3} U^{Cper}`. -/
def perronConst (Kline : ℝ) : ℝ := 36 * Kline / Real.pi

theorem perronConst_nonneg {Kline : ℝ} (h : 0 ≤ Kline) :
    0 ≤ perronConst Kline := by
  unfold perronConst
  exact div_nonneg (mul_nonneg (by norm_num) h) Real.pi_pos.le

/-- **The horizontal remainder estimate.**  This is the `L¹` bound on the two
horizontal segments of the rectangle `[2/3, refRe v] × [-(X^3+1), X^3+1]`.
By the exact contour identity it is *equivalent* to
`ContourRemainderBound`; the equivalence is proved in
`contourRemainderBound_of_horizontal`. -/
def HorizontalRemainderBound (X : ℕ → ℝ) (c : ℝ) (K : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖horizRemainder v t (X n ^ 3 + 1)‖ ≤
        shiftHorizontal (K n) (bandLog X n) C (X n) v

/-- **The contour identity reduces the horizontal estimate to
`ContourRemainderBound`.**  The difference
`refZetaSum - verticalZetaSum - twistedMain` is exactly `horizRemainder` by
`zetaShiftContourIdentity`, so the `L¹` norm bound transfers verbatim. -/
theorem contourRemainderBound_of_horizontal
    {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ} {C : ℝ}
    (hX : ∀ n, 1 < X n) (hRH : RiemannZetaZerosOnLine)
    (hH : HorizontalRemainderBound X c K C) :
    ContourRemainderBound X c K C := by
  filter_upwards [hH] with n hn
  intro v t hv hvB ht
  have hv1 : 1 < v := lt_of_lt_of_le (by norm_num) hv
  have hT : 0 < X n ^ 3 + 1 := by
    have h3 : 0 ≤ X n ^ 3 := pow_nonneg (by linarith [hX n] : (0 : ℝ) ≤ X n) 3
    linarith
  have ht' : |t| < X n ^ 3 + 1 := by
    have h3 : 0 ≤ X n ^ 3 := pow_nonneg (by linarith [hX n] : (0 : ℝ) ≤ X n) 3
    linarith
  have hid := zetaShiftContourIdentity (v := v) (t := t) (T := X n ^ 3 + 1)
    hv1 hT ht' (stripNoZeros_of_RH hRH)
  rw [hid]
  exact hn v t hv hvB ht

/-! ## Absorption of the contour-height logarithm -/

/-- **From the line-bound Perron shift to the bounded three-term shift.**

The line-bound reduction gives the three-error estimate with constant
`3 (Kline/π)(1 + log (X^3 / (2/3)))` and exponent `Cper - 1`.  For
`U = log X ≥ 324` the logarithm satisfies
`1 + log (X^3 / (2/3)) ≤ 4 U`, and one extra power of `U` absorbs it, while the
prime-power term is absorbed using `log (2v) ≤ U` (from `v ≤ exp (U/3)`) and
`Cper ≥ 3`.  The result has the *bounded* constant `36 Kline / π` and exponent
`Cper`, which is the form consumed by the Fourier/Abel step. -/
theorem perronShift_absorbed
    {X : ℕ → ℝ} {c Kline Cper : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hX : ∀ n, 1 < X n)
    (hKline : 0 ≤ Kline) (hC3 : 3 ≤ Cper)
    (hlog324 : ∀ᶠ n : ℕ in atTop, 324 ≤ bandLog X n)
    (hRaw : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
      v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
        ‖twistedPrimeSum v t - twistedMain v t‖ ≤
          (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
            (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ (Cper - 1)
              + v * (bandLog X n) ^ (Cper - 1) / X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2)) :
    ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
      v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
        ‖twistedPrimeSum v t - twistedMain v t‖ ≤
          perronConst Kline *
            (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
              + v * (bandLog X n) ^ Cper / X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
  have hKbound_nonneg : 0 ≤ 12 * Kline / Real.pi :=
    div_nonneg (mul_nonneg (by norm_num) hKline) Real.pi_pos.le
  have hcoef_nonneg : 0 ≤ 3 * Kline / Real.pi :=
    div_nonneg (mul_nonneg (by norm_num) hKline) Real.pi_pos.le
  filter_upwards [hRaw, hlog324] with n hraw hU324
  intro v t hv hvB ht
  set U : ℝ := bandLog X n with hUdef
  have hU3 : 3 ≤ U := by simpa [hUdef] using le_trans (by norm_num) hU324
  have hUpos : 0 < U := by linarith
  have hU1 : (1 : ℝ) ≤ U := by linarith
  have hXpos : 0 < X n := lt_trans zero_lt_one (hX n)
  have hX3pos : 0 < X n ^ 3 := pow_pos hXpos 3
  have hpr : 0 < perronRe := by norm_num [perronRe]
  have hv0 : 0 ≤ v := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hsqrt_le : Real.sqrt v ≤ v ^ (2 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  -- Absorb the height logarithm: `1 + log (X^3/perronRe) ≤ 4U`.
  have hlogdiv : Real.log (X n ^ 3 / perronRe) = 3 * U - Real.log perronRe := by
    rw [Real.log_div (ne_of_gt hX3pos) (ne_of_gt hpr), Real.log_pow]
    simp [bandLog, hUdef]
  have hlog32 : Real.log ((3 : ℝ) / 2) ≤ 1 / 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (3 : ℝ) / 2 by norm_num)
    linarith
  have hlogpr : -1 ≤ Real.log perronRe := by
    have h : Real.log perronRe = -Real.log ((3 : ℝ) / 2) := by
      rw [perronRe, show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
    rw [h]
    linarith
  have hL : 1 + Real.log (X n ^ 3 / perronRe) ≤ 4 * U := by
    rw [hlogdiv]
    linarith
  have hKV :
      3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe))) ≤
        (12 * Kline / Real.pi) * U := by
    have hstep := mul_le_mul_of_nonneg_left hL hcoef_nonneg
    calc
      3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))
          = (3 * Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)) := by
            ring
      _ ≤ (3 * Kline / Real.pi) * (4 * U) := hstep
      _ = (12 * Kline / Real.pi) * U := by ring
  -- The one-power absorption `U^(Cper-1) * U = U^Cper`.
  have hpow : U ^ (Cper - 1) * U = U ^ Cper := by
    have h := Real.rpow_add hUpos (Cper - 1) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  -- Term 1: `v^{2/3} U^{Cper-1}`.
  have hTerm1 :
      (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
          (v ^ (2 / 3 : ℝ) * U ^ (Cper - 1)) ≤
        (12 * Kline / Real.pi) * (v ^ (2 / 3 : ℝ) * U ^ Cper) := by
    have hnn : 0 ≤ v ^ (2 / 3 : ℝ) * U ^ (Cper - 1) :=
      mul_nonneg (Real.rpow_nonneg hv0 _) (Real.rpow_nonneg hUpos.le _)
    calc
      (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
            (v ^ (2 / 3 : ℝ) * U ^ (Cper - 1))
          ≤ ((12 * Kline / Real.pi) * U) *
              (v ^ (2 / 3 : ℝ) * U ^ (Cper - 1)) :=
            mul_le_mul_of_nonneg_right hKV hnn
      _ = (12 * Kline / Real.pi) *
            (v ^ (2 / 3 : ℝ) * (U ^ (Cper - 1) * U)) := by ring
      _ = (12 * Kline / Real.pi) * (v ^ (2 / 3 : ℝ) * U ^ Cper) := by
            rw [hpow]
  -- Term 2: `v U^{Cper-1} / X^3`.
  have hTerm2 :
      (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
          (v * U ^ (Cper - 1) / X n ^ 3) ≤
        (12 * Kline / Real.pi) * (v * U ^ Cper / X n ^ 3) := by
    have hnn : 0 ≤ v * U ^ (Cper - 1) / X n ^ 3 :=
      div_nonneg (mul_nonneg hv0 (Real.rpow_nonneg hUpos.le _)) (le_of_lt hX3pos)
    calc
      (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
            (v * U ^ (Cper - 1) / X n ^ 3)
          ≤ ((12 * Kline / Real.pi) * U) * (v * U ^ (Cper - 1) / X n ^ 3) :=
            mul_le_mul_of_nonneg_right hKV hnn
      _ = (12 * Kline / Real.pi) *
            (v * (U ^ (Cper - 1) * U) / X n ^ 3) := by
            field_simp [ne_of_gt hX3pos]
      _ = (12 * Kline / Real.pi) * (v * U ^ Cper / X n ^ 3) := by
            rw [hpow]
  -- Term 3: the prime-power term.
  have hvExp : v ≤ Real.exp (U / 3) := by
    have h := smoothCutoff_le_exp_third hc0 hc1 (by simpa [hUdef] using hU324)
    exact hvB.trans (by simpa [hUdef] using h)
  have h2v : 2 * v ≤ Real.exp U := by
    have h2 : 2 * v ≤ 2 * Real.exp (U / 3) :=
      mul_le_mul_of_nonneg_left hvExp (by norm_num)
    have hlog2 : Real.log 2 ≤ (2 / 3 : ℝ) * U := by
      have h2le : Real.log 2 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      nlinarith
    calc
      2 * v ≤ 2 * Real.exp (U / 3) := h2
      _ = Real.exp (Real.log 2) * Real.exp (U / 3) := by
            rw [Real.exp_log (by norm_num)]
      _ = Real.exp (Real.log 2 + U / 3) := by rw [← Real.exp_add]
      _ ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)
  have hlog2v : Real.log (2 * v) ≤ U := by
    have h2vpos : 0 < 2 * v := by positivity
    exact (Real.log_le_iff_le_exp h2vpos).mpr h2v
  have hlog2v_nonneg : 0 ≤ Real.log (2 * v) :=
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * v)
  have hsqlog : (Real.log (2 * v)) ^ 2 ≤ U ^ 2 := by nlinarith
  have hU3_le_UC : U ^ 3 ≤ U ^ Cper := by
    rw [← Real.rpow_natCast U 3]
    exact Real.rpow_le_rpow_of_exponent_le hU1 hC3
  have hlogsq_bound : U * (Real.log (2 * v)) ^ 2 ≤ U ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hsqlog hUpos.le
    calc
      U * (Real.log (2 * v)) ^ 2 ≤ U * U ^ 2 := hmul
      _ = U ^ 3 := by ring
  have hTerm3 :
      (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
          (Real.sqrt v * (Real.log (2 * v)) ^ 2) ≤
        (12 * Kline / Real.pi) * (v ^ (2 / 3 : ℝ) * U ^ Cper) := by
    have hnn : 0 ≤ Real.sqrt v * (Real.log (2 * v)) ^ 2 :=
      mul_nonneg hsqrt_nonneg (sq_nonneg _)
    calc
      (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
            (Real.sqrt v * (Real.log (2 * v)) ^ 2)
          ≤ ((12 * Kline / Real.pi) * U) *
              (Real.sqrt v * (Real.log (2 * v)) ^ 2) :=
            mul_le_mul_of_nonneg_right hKV hnn
      _ = (12 * Kline / Real.pi) *
            (Real.sqrt v * (U * (Real.log (2 * v)) ^ 2)) := by ring
      _ ≤ (12 * Kline / Real.pi) * (Real.sqrt v * U ^ 3) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hlogsq_bound hsqrt_nonneg) hKbound_nonneg
      _ ≤ (12 * Kline / Real.pi) * (v ^ (2 / 3 : ℝ) * U ^ Cper) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hsqrt_le hU3_le_UC
                (pow_nonneg hUpos.le 3)
                (Real.rpow_nonneg hv0 (2 / 3 : ℝ)))
              hKbound_nonneg
  -- Sum the three terms.
  have hfirst_nonneg : 0 ≤ v ^ (2 / 3 : ℝ) * U ^ Cper :=
    mul_nonneg (Real.rpow_nonneg hv0 _) (Real.rpow_nonneg hUpos.le _)
  have hsecond_nonneg : 0 ≤ v * U ^ Cper / X n ^ 3 :=
    div_nonneg (mul_nonneg hv0 (Real.rpow_nonneg hUpos.le _)) (le_of_lt hX3pos)
  have hthird_nonneg : 0 ≤ Real.sqrt v * (Real.log (2 * v)) ^ 2 :=
    mul_nonneg hsqrt_nonneg (sq_nonneg _)
  have htotal :
      (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
          (v ^ (2 / 3 : ℝ) * U ^ (Cper - 1)
            + v * U ^ (Cper - 1) / X n ^ 3
            + Real.sqrt v * (Real.log (2 * v)) ^ 2)
        ≤ 3 * (12 * Kline / Real.pi) *
          (v ^ (2 / 3 : ℝ) * U ^ Cper
            + v * U ^ Cper / X n ^ 3
            + Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
    have hexpand :
        (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
            (v ^ (2 / 3 : ℝ) * U ^ (Cper - 1)
              + v * U ^ (Cper - 1) / X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2)
          = (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
                (v ^ (2 / 3 : ℝ) * U ^ (Cper - 1))
            + (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
                (v * U ^ (Cper - 1) / X n ^ 3)
            + (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
                (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by ring
    have hrhs :
        3 * (12 * Kline / Real.pi) *
            (v ^ (2 / 3 : ℝ) * U ^ Cper
              + v * U ^ Cper / X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2)
          = 3 * ((12 * Kline / Real.pi) * (v ^ (2 / 3 : ℝ) * U ^ Cper))
            + 3 * ((12 * Kline / Real.pi) * (v * U ^ Cper / X n ^ 3))
            + 3 * ((12 * Kline / Real.pi) *
                (Real.sqrt v * (Real.log (2 * v)) ^ 2)) := by ring
    rw [hexpand, hrhs]
    nlinarith [hTerm1, hTerm2, hTerm3, hfirst_nonneg, hsecond_nonneg,
      hthird_nonneg, hKbound_nonneg]
  have hraw := hraw v t hv hvB ht
  calc
    ‖twistedPrimeSum v t - twistedMain v t‖
        ≤ (3 * ((Kline / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
            (v ^ (2 / 3 : ℝ) * U ^ (Cper - 1)
              + v * U ^ (Cper - 1) / X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2) := hraw
    _ ≤ 3 * (12 * Kline / Real.pi) *
          (v ^ (2 / 3 : ℝ) * U ^ Cper
            + v * U ^ Cper / X n ^ 3
            + Real.sqrt v * (Real.log (2 * v)) ^ 2) := htotal
    _ = perronConst Kline *
          (v ^ (2 / 3 : ℝ) * U ^ Cper
            + v * U ^ Cper / X n ^ 3
            + Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
          unfold perronConst
          ring

/-! ## The assembled data -/

/-- **The reduced L21.2 analytic data.**  It contains the finite tent profile,
the short-interval count, the four zeta-side estimates (line bound, reference
Perron, horizontal remainder, vertical tail), and the Fourier band bounds.
Every other ingredient (the Abel transform, the Chebyshev count, the parameter
identities, the density normalization) is proved downstream. -/
structure L21_2LeafData where
  /-- The finite Fourier/tent discrepancy profile. -/
  profile : TentProfile
  /-- The stage-one constant `c`. -/
  c : ℝ
  /-- The final Perron exponent.  The line bound is taken at `Cper - 1`. -/
  Cper : ℝ
  /-- The absolute vertical-line constant. -/
  Kline : ℝ
  /-- Reference-Perron constant. -/
  Kref : ℕ → ℝ
  /-- Horizontal-remainder constant. -/
  Kcont : ℕ → ℝ
  /-- Vertical-tail constant. -/
  Ktail : ℕ → ℝ
  /-- The centre sequence of the short-interval count. -/
  p : ℕ → ℝ
  X_gt_one : ∀ n, 1 < profile.X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3`. -/
  U_ge_three : ∀ n, 3 ≤ bandLog profile.X n
  /-- `Cper ≥ 3`. -/
  Cper_ge_three : 3 ≤ Cper
  Kline_nonneg : 0 ≤ Kline
  Kref_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Kref n
  Kcont_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Kcont n
  Ktail_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Ktail n
  /-- The Perron remainder constants fit under the vertical constant. -/
  Ksum_le : ∀ᶠ n : ℕ in atTop,
    Kref n + Kcont n + Ktail n ≤
      (Kline / Real.pi) * (1 + Real.log (profile.X n ^ 3 / perronRe))
  /-- The Riemann hypothesis for `ζ`, as used by the contour identity. -/
  hRH : RiemannZetaZerosOnLine
  /-- The standard `ζ'/ζ` line bound at `Re s = 2/3`. -/
  lineBound : VerticalLineBound profile.X (fun _ => Kline) (Cper - 1)
  /-- The truncated Perron/Abel approximation. -/
  referencePerron : ReferencePerronBound profile.X c Kref (Cper - 1)
  /-- The horizontal contour estimate. -/
  horizontalRemainder : HorizontalRemainderBound profile.X c Kcont (Cper - 1)
  /-- The vertical-tail estimate. -/
  verticalTail : VerticalTailBound profile.X Ktail (Cper - 1)
  /-- The centre is eventually larger than one. -/
  p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < p n
  /-- The literal short-interval smooth count. -/
  localCount : ShortIntervalSmoothCountLower p c profile.X
  /-- `b ≤ B`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf profile.X c n ≤ logCutoff c profile.X n
  /-- `e^a ≥ 2`. -/
  a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf profile.X c n
  /-- Low-frequency energy bound. -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.lowEnergy n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n)
  /-- Middle-frequency energy bound. -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.middleEnergy n ≤ Real.exp (-((1 / c) - δ) * paperRate profile.X n)
  /-- High-frequency energy bound. -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n)
  /-- Two-scale separation. -/
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog profile.X n
  /-- `log X ≤ exp (scale n)`. -/
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog profile.X n ≤ Real.exp (scale n)

namespace L21_2LeafData

variable (D : L21_2LeafData)

/-! ## The Perron shift -/

/-- The dyadic centre bound. -/
abbrev X (n : ℕ) : ℝ := D.profile.X n

/-- `U = log X`. -/
abbrev U (n : ℕ) : ℝ := bandLog D.X n

/-- `T_X = sqrt (U log U)`. -/
abbrev T (n : ℕ) : ℝ := paperRate D.X n

/-- The vertical Perron constant produced by the line bound. -/
abbrev Kvert (n : ℕ) : ℝ :=
  (D.Kline / Real.pi) * (1 + Real.log (D.X n ^ 3 / perronRe))

/-- The final bounded Perron constant. -/
abbrev KperAbs : ℝ := perronConst D.Kline

/-- The large-`U` range needed to absorb the prime-power term, derived from the
two-scale separation. -/
theorem eventually_U_ge_324 : ∀ᶠ n : ℕ in atTop, 324 ≤ D.U n := by
  have hdom := D.U_dominates 1 zero_lt_one
  have hscale : ∀ᶠ n : ℕ in atTop, (18 : ℝ) ≤ scale n :=
    scale_grows.eventually_ge_atTop 18
  filter_upwards [hdom, hscale] with n hn hs
  have hsq : (18 : ℝ) ^ 2 ≤ scale n ^ 2 := by nlinarith
  calc
    (324 : ℝ) = 1 * (18 : ℝ) ^ 2 := by norm_num
    _ ≤ 1 * scale n ^ 2 := by gcongr
    _ ≤ D.U n := by simpa [U] using hn

/-- The horizontal estimate is the contour remainder estimate. -/
theorem contourRemainder :
    ContourRemainderBound D.X D.c D.Kcont (D.Cper - 1) :=
  contourRemainderBound_of_horizontal D.X_gt_one D.hRH D.horizontalRemainder

/-- The three-term Perron remainder, from the reference Perron step, the
horizontal estimate and the vertical tail. -/
theorem perronRemainder :
    PerronShiftRemainder D.X D.c D.Kvert (D.Cper - 1) :=
  perronShiftRemainder_of_bounds D.X_gt_one D.referencePerron D.contourRemainder
    D.verticalTail D.Kref_nonneg D.Kcont_nonneg D.Ktail_nonneg D.Ksum_le

/-- The line-bound Perron shift, before the height logarithm is absorbed. -/
theorem perronShiftRaw :
    ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
      v ≤ smoothCutoff D.c D.X n → |t| ≤ D.X n ^ 3 →
        ‖twistedPrimeSum v t - twistedMain v t‖ ≤
          (3 * D.Kvert n) *
            (v ^ (2 / 3 : ℝ) * (D.U n) ^ (D.Cper - 1)
              + v * (D.U n) ^ (D.Cper - 1) / D.X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2) :=
  perronShift_of_lineBound_of_log_ge D.X_gt_one D.c_pos D.c_le_one
    (fun _ => D.Kline_nonneg) D.U_ge_three (by linarith [D.Cper_ge_three])
    D.eventually_U_ge_324 D.lineBound D.perronRemainder

/-- **The bounded three-term Perron shift.**  This is the form consumed by the
Fourier/Abel step. -/
theorem perronShift :
    ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
      v ≤ smoothCutoff D.c D.X n → |t| ≤ D.X n ^ 3 →
        ‖twistedPrimeSum v t - twistedMain v t‖ ≤
          D.KperAbs *
            (v ^ (2 / 3 : ℝ) * (D.U n) ^ D.Cper
              + v * (D.U n) ^ D.Cper / D.X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2) :=
  perronShift_absorbed D.c_pos D.c_le_one D.X_gt_one D.Kline_nonneg
    D.Cper_ge_three D.eventually_U_ge_324 D.perronShiftRaw

/-! ## The Abel bundle -/

/-- **The L21.2 data assembled into the Abel bundle.**  The `perronShift` field
is the bounded shift proved above, the density normalization is the
short-interval count of `RandomizedL21_2PaperLocal`, and the mean-square field
is the finite Plancherel comparison of the tent profile. -/
def toAbelInputs : L21_2AbelInputs where
  X := D.X
  c := D.c
  KperAbs := D.KperAbs
  Cper := D.Cper
  smoothCount := smoothCountNear D.p D.c D.X
  lowTerm := D.profile.lowEnergy
  middleTerm := D.profile.middleEnergy
  tailTerm := D.profile.tailEnergy
  polyExp := 3
  N := D.profile.N
  deficit := D.profile.deficit
  X_gt_one := D.X_gt_one
  c_pos := D.c_pos
  c_le_one := D.c_le_one
  U_ge_three := D.U_ge_three
  KperAbs_nonneg := perronConst_nonneg D.Kline_nonneg
  Cper_ge_two := by linarith [D.Cper_ge_three]
  polyExp_ge_three := le_rfl
  smoothCount_nonneg := fun n => smoothCountNear_nonneg D.p D.c D.X n
  lowTerm_nonneg := fun n => by
    letI := D.profile.neZero n
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (D.profile.coeff n j)
  middleTerm_nonneg := fun n => by
    letI := D.profile.neZero n
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (D.profile.coeff n j)
  tailTerm_nonneg := fun n => by
    letI := D.profile.neZero n
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (D.profile.coeff n j)
  N_pos := D.profile.N_pos
  perronShift := D.perronShift
  a_ge_log_two := D.a_ge_log_two
  b_le_B := D.b_le_B
  densityNormalization := by
    have h := localSmoothCountLower_of_shortInterval D.p_gt_one D.localCount
    simpa [LocalSmoothCountLower, smoothCountNear] using h
  fourierLow := D.fourierLow
  fourierMiddle := D.fourierMiddle
  fourierTail := D.fourierTail
  tentMeanSquare := Eventually.of_forall fun n =>
    D.profile.meanSquare_le_energy n
  U_dominates := D.U_dominates
  U_le_exp := D.U_le_exp

/-! ## The rated leaf -/

/-- **The assembled L21.2 `RatedLeaf`.** -/
def ratedLeaf : RatedLeaf := D.toAbelInputs.toRatedLeaf

/-- The loss is the genuine exceptional fraction `badCount / (X + 1)`. -/
theorem ratedLeaf_loss_eq_badFraction (n : ℕ) :
    D.ratedLeaf.loss n =
      D.toAbelInputs.toFourierInputs.badCount n /
        (D.toAbelInputs.toFourierInputs.X n + 1) := rfl

/-- The loss written as the fraction of bad sampled centres. -/
theorem ratedLeaf_loss_eq_card_fraction (n : ℕ) :
    D.ratedLeaf.loss n =
      ((D.toAbelInputs.toFourierInputs.badSet n).card : ℝ) /
        (D.profile.N n : ℝ) := by
  rw [D.ratedLeaf_loss_eq_badFraction n]
  exact L21_2FourierInputs.badCount_div D.toAbelInputs.toFourierInputs n

theorem ratedLeaf_loss_nonneg (n : ℕ) : 0 ≤ D.ratedLeaf.loss n :=
  D.ratedLeaf.loss_nonneg n

/-- The loss is positive as soon as the bad set is nonempty: it is a genuine
count, not a sequence set to zero. -/
theorem ratedLeaf_loss_pos_of_badSet_nonempty {n : ℕ}
    (h : (D.toAbelInputs.toFourierInputs.badSet n).Nonempty) :
    0 < D.ratedLeaf.loss n := by
  rw [D.ratedLeaf_loss_eq_card_fraction n]
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr h)
    (by exact_mod_cast D.profile.N_pos n)

/-- The loss of the assembled leaf is the loss of the Fourier reduction. -/
theorem ratedLeaf_loss_eq_fourierReduced (n : ℕ) :
    D.ratedLeaf.loss n =
      D.toAbelInputs.toFourierInputs.toPerronInputs.toReducedInputs.loss n := rfl

/-- The manuscript rate `loss ≤ exp (-(c/64) T_X)`. -/
theorem ratedLeaf_loss_le_manuscript :
    ∀ᶠ n : ℕ in atTop,
      D.ratedLeaf.loss n ≤ Real.exp (-((D.c / 64) * D.T n)) := by
  have h := L21_2FourierInputs.loss_le_paper D.toAbelInputs.toFourierInputs
  filter_upwards [h] with n hn
  rw [D.ratedLeaf_loss_eq_fourierReduced n]
  exact hn

/-- The manuscript rate in the exact `RatedLeaf` form. -/
theorem ratedLeaf_paper :
    ∀ᶠ n : ℕ in atTop,
      D.ratedLeaf.loss n ≤ Real.exp (-(D.ratedLeaf.c * D.ratedLeaf.rate n)) :=
  D.ratedLeaf.paper

/-- The `D^{-B}` ledger slot at `B = 2`. -/
theorem ratedLeaf_loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      D.ratedLeaf.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  D.ratedLeaf.ledger

/-- The `C5Leaf.ellipticExceptional` ledger slot carries this loss. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = D.ratedLeaf.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  rw [h]
  exact D.ratedLeaf.ledger

/-- The eleven remaining leaves plus the assembled L21.2 leaf give the full
paper assumptions. -/
def paperAssumptions
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2AbelInputs.paperAssumptions_of_abel D.toAbelInputs P

end L21_2LeafData

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2LeafAssembly.perronConst_nonneg
#print axioms Cogentic.RandomizedL21_2LeafAssembly.contourRemainderBound_of_horizontal
#print axioms Cogentic.RandomizedL21_2LeafAssembly.perronShift_absorbed
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.contourRemainder
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.eventually_U_ge_324
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.perronRemainder
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.perronShiftRaw
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.perronShift
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.toAbelInputs
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.ratedLeaf
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.ratedLeaf_loss_eq_card_fraction
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.ratedLeaf_loss_pos_of_badSet_nonempty
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.ratedLeaf_loss_le_manuscript
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.ratedLeaf_paper
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.ratedLeaf_loss_le_ledger
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.slot_le
#print axioms Cogentic.RandomizedL21_2LeafAssembly.L21_2LeafData.paperAssumptions

end Cogentic.RandomizedL21_2LeafAssembly
