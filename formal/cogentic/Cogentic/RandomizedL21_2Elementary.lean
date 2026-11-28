import Cogentic.RandomizedPaperEndpointWave16
import Cogentic.RandomizedL21_2LeafAssembly
import Cogentic.RandomizedL21_2Abel
import Cogentic.RandomizedL21_2Tent

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# L21.2: the numerically elementary fields of the wave-16 record

`Cogentic.RandomizedPaperEndpointWave16.Wave16L21_2Inputs` still carries the
elementary parameter fields

* `c_pos`, `c_le_one`;
* `U_ge_three`;
* `Kline_nonneg`, `Ktail_nonneg`;
* `b_le_B`, `a_ge_log_two`;
* `U_dominates`, `U_le_exp`;
* `Ksum_le`.

This file fixes the paper's parameter choices

```
c      = 1 / sqrt 2,
Cper   = 3,
U n    = |scale n|^3 + 3,
X n    = exp (U n),
```

and proves every one of those fields from the definitions and from
`scale n -> infinity`.  It also supplies the bookkeeping fields `X_gt_one`,
`Cper_ge_three` and `p_gt_one` (with `p = X`).  The only remaining genuinely
analytic inputs are

* `RiemannZetaZerosOnLine`;
* the uniform zeta line bound `VerticalLineBound`;
* the vertical tail `VerticalTailBound`;
* the literal short-interval smooth count `ShortIntervalSmoothCountLower`;
* the three Fourier band bounds.

## The line constant

The `Ksum_le` comparison has the form

```
wave16Kref X n + (3 e / pi) * stripK + Ktail n
  <= (Kline / pi) * (1 + log (X n ^ 3 / perronRe)).
```

Since `wave16Kref X n` grows like `X n * (log X n)^2` while the right-hand
side grows like `Kline * log X n`, no *single real* `Kline` can satisfy this
once `log X n -> infinity`.  The wave-16 record therefore has to carry the line
constant as a sequence.  We define the explicit positive sequence

```
elementaryKline X Ktail n
  = max 1 (pi * (wave16Kref X n + (3 e / pi) * stripK + Ktail n)
             / (1 + log (X n ^ 3 / perronRe)))
```

and prove `Ksum_le` for it by construction.  The structure
`Wave16L21_2Shape` below is `Wave16L21_2Inputs` with `Kline : ℕ → ℝ`; the
reduction `ElementaryInputs.toShape` fills all its fields.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count,
mass or error is set to zero.
-/

namespace Cogentic.RandomizedL21_2Elementary

open Filter Real
open scoped BigOperators ENNReal

open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Abel
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2StripBound
open Cogentic.RandomizedL21_2ReferenceBound
open Cogentic.RandomizedL21_2Fourier
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperLeafStatements

noncomputable section

/-! ## The explicit parameter choices -/

/-- The paper's stage-one constant `c = 1 / sqrt 2`. -/
def elementaryC : ℝ := 1 / Real.sqrt 2

/-- The Perron exponent used by the elementary record. -/
def elementaryCper : ℝ := 3

/-- The explicit scale `U = log X`, chosen to dominate every fixed power of
`scale` while staying below `exp (scale)`. -/
def elementaryU (n : ℕ) : ℝ := |scale n| ^ 3 + 3

/-- The explicit dyadic bound `X = exp U`. -/
def elementaryX (n : ℕ) : ℝ := Real.exp (elementaryU n)

/-- The vertical-tail constant, made nonnegative by taking a positive part. -/
def elementaryKtail (K : ℕ → ℝ) (n : ℕ) : ℝ := max 0 (K n)

/-- The explicit line constant.  It is a *sequence*, not a single real: the
reference-Perron constant grows like `X (log X)^2`, so a constant cannot work
on an unbounded band. -/
def elementaryKline (X : ℕ → ℝ) (Ktail : ℕ → ℝ) (n : ℕ) : ℝ :=
  max 1
    (Real.pi * (wave16Kref X n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n)
      / (1 + Real.log (X n ^ 3 / perronRe)))

/-! ## Elementary positivity and normalisation -/

theorem elementaryC_pos : 0 < elementaryC := by
  unfold elementaryC
  positivity

theorem elementaryC_le_one : elementaryC ≤ 1 := by
  unfold elementaryC
  rw [div_le_one (Real.sqrt_pos.mpr (by norm_num))]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem elementaryU_ge_three (n : ℕ) : 3 ≤ elementaryU n := by
  unfold elementaryU
  have h : 0 ≤ |scale n| ^ 3 := pow_nonneg (abs_nonneg _) 3
  linarith

theorem elementaryX_gt_one (n : ℕ) : 1 < elementaryX n := by
  unfold elementaryX
  have h : 0 < elementaryU n := by linarith [elementaryU_ge_three n]
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < Real.exp (elementaryU n) := Real.exp_lt_exp.mpr h

/-- The paper's `U = log X` at the explicit `X`. -/
theorem bandLog_elementaryX (n : ℕ) : bandLog elementaryX n = elementaryU n := by
  unfold bandLog elementaryX
  rw [Real.log_exp]

theorem elementaryKtail_nonneg (K : ℕ → ℝ) (n : ℕ) : 0 ≤ elementaryKtail K n := by
  unfold elementaryKtail
  exact le_max_left _ _

theorem elementaryKline_nonneg (X : ℕ → ℝ) (Ktail : ℕ → ℝ) (n : ℕ) :
    0 ≤ elementaryKline X Ktail n := by
  unfold elementaryKline
  exact le_trans zero_le_one (le_max_left _ _)

theorem elementaryKline_pos (X : ℕ → ℝ) (Ktail : ℕ → ℝ) (n : ℕ) :
    0 < elementaryKline X Ktail n := by
  unfold elementaryKline
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-! ## Growth of the scale -/

theorem elementaryU_grows : Tendsto elementaryU atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ scale_grows
  filter_upwards [scale_grows.eventually_ge_atTop 1] with n hn
  have h0 : 0 ≤ scale n := by linarith
  have hcube : scale n ≤ scale n ^ 3 := by
    have h1 : 0 ≤ scale n - 1 := by linarith
    have h2 : 0 ≤ scale n ^ 2 + scale n + 1 := by positivity
    have h3 : 0 ≤ (scale n - 1) * (scale n ^ 2 + scale n + 1) :=
      mul_nonneg h1 h2
    nlinarith
  have habs : scale n ^ 3 ≤ |scale n| ^ 3 := by
    rw [abs_of_nonneg h0]
  unfold elementaryU
  linarith

theorem elementaryT_pos (n : ℕ) : 0 < paperRate elementaryX n := by
  unfold paperRate
  rw [bandLog_elementaryX]
  apply Real.sqrt_pos.mpr
  have hU : 0 < elementaryU n := by linarith [elementaryU_ge_three n]
  have hlog : 0 < Real.log (elementaryU n) :=
    Real.log_pos (by linarith [elementaryU_ge_three n])
  exact mul_pos hU hlog

theorem elementaryT_grows :
    Tendsto (fun n => paperRate elementaryX n) atTop atTop := by
  have hlog : Tendsto (fun n => Real.log (elementaryU n)) atTop atTop :=
    Real.tendsto_log_atTop.comp elementaryU_grows
  have hmul : Tendsto (fun n => elementaryU n * Real.log (elementaryU n))
      atTop atTop := elementaryU_grows.atTop_mul_atTop₀ hlog
  have hsqrt : Tendsto
      (fun n => Real.sqrt (elementaryU n * Real.log (elementaryU n)))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hmul
  refine hsqrt.congr' ?_
  filter_upwards with n
  unfold paperRate
  rw [bandLog_elementaryX]

theorem elementaryT_div_U_tendsto_zero :
    Tendsto (fun n => paperRate elementaryX n / elementaryU n) atTop (nhds 0) := by
  have h := Scale.tendsto_t_div_u elementaryU_grows
  refine h.congr' ?_
  filter_upwards with n
  unfold Scale.t paperRate
  rw [bandLog_elementaryX]

/-- `U / T -> infinity`, the reciprocal of `T / U -> 0`. -/
theorem elementaryU_div_T_tendsto_atTop :
    Tendsto (fun n => elementaryU n / paperRate elementaryX n) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  by_cases hb : b ≤ 0
  · filter_upwards [elementaryU_grows.eventually_gt_atTop 0] with n hU0
    have hT0 : 0 < paperRate elementaryX n := elementaryT_pos n
    have hnonneg : 0 ≤ elementaryU n / paperRate elementaryX n :=
      div_nonneg hU0.le hT0.le
    linarith
  · have hbpos : 0 < b := lt_of_not_ge hb
    have hsmall : ∀ᶠ n : ℕ in atTop,
        paperRate elementaryX n / elementaryU n < 1 / (b + 1) :=
      elementaryT_div_U_tendsto_zero.eventually
        (Iio_mem_nhds (one_div_pos.mpr (by linarith)))
    filter_upwards [hsmall, elementaryU_grows.eventually_gt_atTop 0] with n hn hU0
    have hT0 : 0 < paperRate elementaryX n := elementaryT_pos n
    have hb1 : 0 < b + 1 := by linarith
    rw [div_lt_iff₀ hU0] at hn
    have hfrac : b / (b + 1) < 1 := by
      rw [div_lt_one hb1]
      linarith
    have hbT : b * paperRate elementaryX n < elementaryU n := by
      calc
        b * paperRate elementaryX n
            < b * (1 / (b + 1) * elementaryU n) :=
          mul_lt_mul_of_pos_left hn hbpos
        _ = (b / (b + 1)) * elementaryU n := by field_simp [hb1.ne']
        _ < 1 * elementaryU n := mul_lt_mul_of_pos_right hfrac hU0
        _ = elementaryU n := by ring
    rw [le_div_iff₀ hT0]
    exact le_of_lt hbT

/-- `r = (U + 1) / (c T) -> infinity`. -/
theorem elementaryr_tendsto_atTop :
    Tendsto (fun n => rOf elementaryX elementaryC n) atTop atTop := by
  have hlow : Tendsto
      (fun n => (1 / elementaryC) * (elementaryU n / paperRate elementaryX n))
      atTop atTop :=
    Tendsto.const_mul_atTop (one_div_pos.mpr elementaryC_pos)
      elementaryU_div_T_tendsto_atTop
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [elementaryU_grows.eventually_gt_atTop 0] with n hU0
  have hden : 0 < elementaryC * paperRate elementaryX n :=
    mul_pos elementaryC_pos (elementaryT_pos n)
  rw [rOf, UOf, BOf, logCutoff, bandLog_elementaryX]
  calc
    (1 / elementaryC) * (elementaryU n / paperRate elementaryX n)
        = elementaryU n / (elementaryC * paperRate elementaryX n) := by
      field_simp
    _ ≤ (elementaryU n + 1) / (elementaryC * paperRate elementaryX n) :=
      div_le_div_of_nonneg_right (by linarith) hden.le

/-! ## The two-scale inequalities -/

theorem elementaryU_dominates :
    ∀ m : ℝ, 0 < m →
      ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog elementaryX n := by
  intro m hm
  by_cases hm0 : m ≤ 0
  · filter_upwards with n
    rw [bandLog_elementaryX]
    unfold elementaryU
    have hsq : 0 ≤ scale n ^ 2 := sq_nonneg _
    have hcube : 0 ≤ |scale n| ^ 3 := pow_nonneg (abs_nonneg _) 3
    nlinarith
  · have hmpos : 0 < m := lt_of_not_ge hm0
    filter_upwards [scale_grows.eventually_ge_atTop (max 1 (m + 1))] with n hn
    have h1 : 1 ≤ scale n := le_trans (le_max_left _ _) hn
    have hmle : m ≤ scale n - 1 := by
      have h2 : m + 1 ≤ scale n := le_trans (le_max_right _ _) hn
      linarith
    rw [bandLog_elementaryX]
    unfold elementaryU
    rw [abs_of_nonneg (by linarith : 0 ≤ scale n)]
    have hsq : 0 ≤ scale n ^ 2 := sq_nonneg _
    have hmul : m * scale n ^ 2 ≤ (scale n - 1) * scale n ^ 2 :=
      mul_le_mul_of_nonneg_right hmle hsq
    have hnonneg : 0 ≤ scale n ^ 3 + 3 - (scale n - 1) * scale n ^ 2 := by
      nlinarith [sq_nonneg (scale n), h1]
    linarith

theorem elementaryU_le_exp :
    ∀ᶠ n : ℕ in atTop, bandLog elementaryX n ≤ Real.exp (scale n) := by
  have hdiv : Tendsto (fun n => Real.exp (scale n) / scale n ^ 3) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 3).comp scale_grows
  have hge : ∀ᶠ n : ℕ in atTop,
      2 ≤ Real.exp (scale n) / scale n ^ 3 := hdiv.eventually_ge_atTop 2
  have hexp : ∀ᶠ n : ℕ in atTop, 6 ≤ Real.exp (scale n) :=
    (Real.tendsto_exp_atTop.comp scale_grows).eventually_ge_atTop 6
  filter_upwards [hge, hexp, scale_grows.eventually_ge_atTop 1] with n hge hn hpos
  have hcube : 0 < scale n ^ 3 := pow_pos (by linarith) 3
  have h2 : 2 * scale n ^ 3 ≤ Real.exp (scale n) := by
    rw [le_div_iff₀ hcube] at hge
    linarith
  rw [bandLog_elementaryX]
  unfold elementaryU
  rw [abs_of_nonneg (by linarith : 0 ≤ scale n)]
  nlinarith

/-! ## The parameter bounds `b <= B` and `a >= log 2` -/

/-- The explicit abbreviations used by the parameter arithmetic. -/
abbrev eU (n : ℕ) : ℝ := bandLog elementaryX n
abbrev eT (n : ℕ) : ℝ := paperRate elementaryX n
abbrev eB (n : ℕ) : ℝ := logCutoff elementaryC elementaryX n
abbrev eR (n : ℕ) : ℝ := rOf elementaryX elementaryC n
abbrev eK (n : ℕ) : ℝ := kOf elementaryX elementaryC n
abbrev eM (n : ℕ) : ℝ := mOf elementaryX elementaryC n
abbrev eA (n : ℕ) : ℝ := aOf elementaryX elementaryC n
abbrev eBb (n : ℕ) : ℝ := bOf elementaryX elementaryC n

theorem eU_ge_three (n : ℕ) : 3 ≤ eU n := by
  rw [eU, bandLog_elementaryX]
  exact elementaryU_ge_three n

theorem eT_pos (n : ℕ) : 0 < eT n := elementaryT_pos n

theorem eB_pos (n : ℕ) : 0 < eB n := by
  rw [eB, logCutoff]
  exact mul_pos elementaryC_pos (eT_pos n)

/-- The elementary bound `b <= B`.  It only uses `log X >= 3` and `c <= 1`:
write `b = m (1 + 1 / log k)`, use `log k >= log r` and
`(log X + log 2 / 2) / (log X + 1) <= 1`, and cancel the exact identity
`k = r (1 + 2 / log r)`. -/
theorem eBb_le_eB (n : ℕ) : eBb n ≤ eB n := by
  have hU3 : 3 ≤ eU n := eU_ge_three n
  have hU0 : 0 < eU n := by linarith
  have hlogU : 0 < Real.log (eU n) := Real.log_pos (by linarith)
  have hT0 : 0 < eT n := eT_pos n
  have hB0 : 0 < eB n := eB_pos n
  have hT_lt : eT n < eU n + 1 := by
    have hTsq : eT n ^ 2 = eU n * Real.log (eU n) := by
      rw [show eT n = Real.sqrt (eU n * Real.log (eU n)) from rfl]
      exact Real.sq_sqrt (mul_nonneg hU0.le hlogU.le)
    have hlog_le : Real.log (eU n) ≤ eU n := Real.log_le_self hU0.le
    have hlt : eU n * Real.log (eU n) < (eU n + 1) ^ 2 := by
      nlinarith
    calc
      eT n = Real.sqrt (eT n ^ 2) := (Real.sqrt_sq (le_of_lt hT0)).symm
      _ < Real.sqrt ((eU n + 1) ^ 2) :=
        Real.sqrt_lt_sqrt (sq_nonneg _) (by rw [hTsq]; exact hlt)
      _ = eU n + 1 := Real.sqrt_sq (by linarith)
  have hr1 : 1 < eR n := by
    rw [show eR n = (eU n + 1) / eB n from rfl, one_lt_div hB0]
    calc
      eB n = elementaryC * eT n := rfl
      _ ≤ 1 * eT n := mul_le_mul_of_nonneg_right elementaryC_le_one hT0.le
      _ = eT n := one_mul _
      _ < eU n + 1 := hT_lt
  have hr0 : 0 < eR n := lt_trans zero_lt_one hr1
  have hlogr : 0 < Real.log (eR n) := Real.log_pos hr1
  have hk_eq : eK n = eR n * (1 + 2 / Real.log (eR n)) := rfl
  have hfac_gt : 1 < 1 + 2 / Real.log (eR n) := by
    have h : 0 < 2 / Real.log (eR n) := div_pos (by norm_num) hlogr
    linarith
  have hk_gt : eR n < eK n := by
    rw [hk_eq]
    calc
      eR n = eR n * 1 := (mul_one _).symm
      _ < eR n * (1 + 2 / Real.log (eR n)) :=
        mul_lt_mul_of_pos_left hfac_gt hr0
  have hk1 : 1 < eK n := lt_trans hr1 hk_gt
  have hlogk : 0 < Real.log (eK n) := Real.log_pos hk1
  have hlogk_ge : Real.log (eR n) ≤ Real.log (eK n) :=
    Real.log_le_log hr0 hk_gt.le
  have hm0 : 0 < eM n := by
    rw [show eM n = (eU n + Real.log 2 / 2) / eK n from rfl]
    apply div_pos
    · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    · exact lt_trans zero_lt_one hk1
  have hb_le : eBb n ≤ eM n * (1 + 2 / Real.log (eR n)) := by
    rw [show eBb n = eM n + eM n / Real.log (eK n) from rfl]
    have hcoef : 1 + 1 / Real.log (eK n) ≤ 1 + 2 / Real.log (eR n) := by
      have h1 : 1 / Real.log (eK n) ≤ 1 / Real.log (eR n) :=
        one_div_le_one_div_of_le hlogr hlogk_ge
      have h2 : 1 / Real.log (eR n) ≤ 2 / Real.log (eR n) :=
        div_le_div_of_nonneg_right (by norm_num) hlogr.le
      linarith
    have hmul : eM n + eM n / Real.log (eK n) =
        eM n * (1 + 1 / Real.log (eK n)) := by ring
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hcoef hm0.le
  have hmfac : eM n * (1 + 2 / Real.log (eR n)) =
      (eU n + Real.log 2 / 2) / eR n := by
    rw [show eM n = (eU n + Real.log 2 / 2) / eK n from rfl,
      show eK n = eR n * (1 + 2 / Real.log (eR n)) from rfl]
    have hfac_ne : (1 + 2 / Real.log (eR n)) ≠ 0 := by positivity
    field_simp [hfac_ne]
  have hdiv : (eU n + Real.log 2 / 2) / eR n =
      (eU n + Real.log 2 / 2) * eB n / (eU n + 1) := by
    rw [show eR n = (eU n + 1) / eB n from rfl]
    field_simp [hB0.ne']
  have hcoef : eU n + Real.log 2 / 2 ≤ eU n + 1 := by
    have h2 : Real.log 2 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hfinal : (eU n + Real.log 2 / 2) * eB n / (eU n + 1) ≤ eB n := by
    rw [div_le_iff₀ (by linarith : 0 < eU n + 1)]
    nlinarith [hcoef, le_of_lt hB0]
  calc
    eBb n ≤ eM n * (1 + 2 / Real.log (eR n)) := hb_le
    _ = (eU n + Real.log 2 / 2) / eR n := hmfac
    _ = (eU n + Real.log 2 / 2) * eB n / (eU n + 1) := hdiv
    _ ≤ eB n := hfinal

theorem eBb_le_logCutoff :
    ∀ᶠ n : ℕ in atTop, eBb n ≤ eB n :=
  Eventually.of_forall eBb_le_eB

theorem elementary_b_le_B :
    ∀ᶠ n : ℕ in atTop,
      bOf elementaryX elementaryC n ≤ logCutoff elementaryC elementaryX n :=
  eBb_le_logCutoff

/-- `a = m (1 - 1 / log k) -> infinity`.  Coarsely, `k <= 2 r` once
`log r >= 2`, hence `m >= c T / 4`, and therefore `a >= c T / 8`. -/
theorem elementary_a_ge_log_two :
    ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ eA n := by
  filter_upwards [elementaryr_tendsto_atTop.eventually_ge_atTop (Real.exp 2),
    elementaryT_grows.eventually_ge_atTop (8 * Real.log 2 / elementaryC)] with n hr hT
  have hU3 : 3 ≤ eU n := eU_ge_three n
  have hU0 : 0 < eU n := by linarith
  have hT0 : 0 < eT n := eT_pos n
  have hB0 : 0 < eB n := eB_pos n
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr1 : 1 < eR n := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hr
  have hr0 : 0 < eR n := lt_trans zero_lt_one hr1
  have hlogr2 : 2 ≤ Real.log (eR n) := by
    calc
      (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (eR n) := Real.log_le_log (Real.exp_pos 2) hr
  have hlogr : 0 < Real.log (eR n) := by linarith
  have hk_eq : eK n = eR n * (1 + 2 / Real.log (eR n)) := rfl
  have hk_ge : eR n ≤ eK n := by
    rw [hk_eq]
    calc
      eR n = eR n * 1 := (mul_one _).symm
      _ ≤ eR n * (1 + 2 / Real.log (eR n)) := by
        apply mul_le_mul_of_nonneg_left _ hr0.le
        have h : 0 ≤ 2 / Real.log (eR n) := div_nonneg (by norm_num) hlogr.le
        linarith
  have hk1 : 1 < eK n := lt_of_lt_of_le hr1 hk_ge
  have hlogk2 : 2 ≤ Real.log (eK n) :=
    le_trans hlogr2 (Real.log_le_log hr0 hk_ge)
  have hlogk : 0 < Real.log (eK n) := by linarith
  have hfac_le : 1 + 2 / Real.log (eR n) ≤ 2 := by
    have h : 2 / Real.log (eR n) ≤ 1 := by
      rw [div_le_iff₀ hlogr]
      linarith
    linarith
  have hk_le : eK n ≤ 2 * eR n := by
    rw [hk_eq]
    calc
      eR n * (1 + 2 / Real.log (eR n)) ≤ eR n * 2 :=
        mul_le_mul_of_nonneg_left hfac_le hr0.le
      _ = 2 * eR n := by ring
  have hm_eq : eM n = (eU n + Real.log 2 / 2) / eK n := rfl
  have hnum0 : 0 < eU n + Real.log 2 / 2 := by linarith
  have hstep1 : (eU n + Real.log 2 / 2) / (2 * eR n) ≤ eM n := by
    rw [hm_eq]
    have hinv : 1 / (2 * eR n) ≤ 1 / eK n :=
      one_div_le_one_div_of_le (lt_trans zero_lt_one hk1) hk_le
    calc
      (eU n + Real.log 2 / 2) / (2 * eR n)
          = (eU n + Real.log 2 / 2) * (1 / (2 * eR n)) := by ring
      _ ≤ (eU n + Real.log 2 / 2) * (1 / eK n) :=
        mul_le_mul_of_nonneg_left hinv hnum0.le
      _ = (eU n + Real.log 2 / 2) / eK n := by ring
  have hrewrite : (eU n + Real.log 2 / 2) / (2 * eR n) =
      (eU n + Real.log 2 / 2) * eB n / (2 * (eU n + 1)) := by
    rw [show eR n = (eU n + 1) / eB n from rfl]
    field_simp [hB0.ne']
  have hcoef : (1 : ℝ) / 4 ≤
      (eU n + Real.log 2 / 2) / (2 * (eU n + 1)) := by
    rw [le_div_iff₀ (by positivity : 0 < 2 * (eU n + 1))]
    nlinarith [hU0, hlog2pos]
  have hstep2 : elementaryC * eT n / 4 ≤
      (eU n + Real.log 2 / 2) / (2 * eR n) := by
    rw [hrewrite]
    calc
      elementaryC * eT n / 4 = (1 / 4) * (elementaryC * eT n) := by ring
      _ ≤ ((eU n + Real.log 2 / 2) / (2 * (eU n + 1))) *
            (elementaryC * eT n) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (eU n + Real.log 2 / 2) * eB n / (2 * (eU n + 1)) := by
        rw [show eB n = elementaryC * eT n from rfl]
        ring
  have hm_ge : elementaryC * eT n / 4 ≤ eM n := le_trans hstep2 hstep1
  have hm0 : 0 < eM n := lt_of_lt_of_le (by positivity) hm_ge
  have ha_eq : eA n = eM n * (1 - 1 / Real.log (eK n)) := by
    rw [show eA n = eM n - eM n / Real.log (eK n) from rfl]
    ring
  have hcoef2 : (1 : ℝ) / 2 ≤ 1 - 1 / Real.log (eK n) := by
    have h : 1 / Real.log (eK n) ≤ 1 / 2 := by
      rw [div_le_iff₀ hlogk]
      linarith
    linarith
  have ha_ge : elementaryC * eT n / 8 ≤ eA n := by
    rw [ha_eq]
    calc
      elementaryC * eT n / 8 = (elementaryC * eT n / 4) * (1 / 2) := by ring
      _ ≤ eM n * (1 - 1 / Real.log (eK n)) :=
        mul_le_mul hm_ge hcoef2 (by norm_num) hm0.le
  have h8 : 8 * Real.log 2 ≤ elementaryC * eT n := by
    calc
      8 * Real.log 2 = elementaryC * ((8 * Real.log 2) / elementaryC) := by
        field_simp [elementaryC_pos.ne']
      _ ≤ elementaryC * eT n :=
        mul_le_mul_of_nonneg_left hT elementaryC_pos.le
  have hfinal : Real.log 2 ≤ elementaryC * eT n / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    linarith
  exact le_trans hfinal ha_ge

/-! ## The constant-compatibility inequality -/

/-- **The `Ksum_le` inequality at the explicit constants.**  The line constant
is the sequence `elementaryKline`; the inequality holds for every `n`, by the
definition of the positive part and of the `max`. -/
theorem elementaryKsum_le (X : ℕ → ℝ) (hX : ∀ n, 1 < X n) (Ktail : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      wave16Kref X n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n ≤
        (elementaryKline X Ktail n / Real.pi) *
          (1 + Real.log (X n ^ 3 / perronRe)) := by
  refine Eventually.of_forall ?_
  intro n
  set D := 1 + Real.log (X n ^ 3 / perronRe) with hD
  have hX0 : 0 < X n := lt_trans zero_lt_one (hX n)
  have hX3 : 1 < X n ^ 3 := by
    have h2 : 1 < X n ^ 2 := by nlinarith [hX n, sq_nonneg (X n)]
    have h3 : X n < X n ^ 3 := by
      calc
        X n = X n * 1 := (mul_one _).symm
        _ < X n * X n ^ 2 := mul_lt_mul_of_pos_left h2 hX0
        _ = X n ^ 3 := by ring
    linarith [hX n]
  have hpr : 0 < perronRe := by norm_num [perronRe]
  have hratio : 1 < X n ^ 3 / perronRe := by
    rw [one_lt_div hpr]
    norm_num [perronRe]
    linarith
  have hlogpos : 0 < Real.log (X n ^ 3 / perronRe) := Real.log_pos hratio
  have hDpos : 0 < D := by rw [hD]; linarith
  have hDne : D ≠ 0 := hDpos.ne'
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmax : Real.pi *
        (wave16Kref X n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n) / D ≤
      elementaryKline X Ktail n := by
    unfold elementaryKline
    exact le_max_right _ _
  calc
    wave16Kref X n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n
        = (Real.pi *
              (wave16Kref X n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n) / D)
            / Real.pi * D := by
          field_simp [hDne, hpi.ne']
    _ ≤ (elementaryKline X Ktail n / Real.pi) * D := by
      apply mul_le_mul_of_nonneg_right _ hDpos.le
      exact div_le_div_of_nonneg_right hmax hpi.le
    _ = (elementaryKline X Ktail n / Real.pi) *
          (1 + Real.log (X n ^ 3 / perronRe)) := by rw [hD]

/-! ## The reduced record -/

/-- `Wave16L21_2Inputs` with the line constant allowed to be a sequence.
All the numerical fields are now theorems; the analytic fields are exactly
`hRH`, `lineBound`, `verticalTail`, `localCount` and the three Fourier band
bounds. -/
structure Wave16L21_2Shape where
  profile : TentProfile
  c : ℝ
  Cper : ℝ
  Kline : ℕ → ℝ
  Ktail : ℕ → ℝ
  p : ℕ → ℝ
  X_gt_one : ∀ n, 1 < profile.X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  U_ge_three : ∀ n, 3 ≤ bandLog profile.X n
  Cper_ge_three : 3 ≤ Cper
  Kline_nonneg : ∀ n, 0 ≤ Kline n
  Ktail_nonneg : ∀ n, 0 ≤ Ktail n
  Ksum_le : ∀ᶠ n : ℕ in atTop,
    wave16Kref profile.X n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n ≤
      (Kline n / Real.pi) * (1 + Real.log (profile.X n ^ 3 / perronRe))
  hRH : RiemannZetaZerosOnLine
  lineBound : VerticalLineBound profile.X Kline (Cper - 1)
  verticalTail : VerticalTailBound profile.X Ktail (Cper - 1)
  p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < p n
  localCount : ShortIntervalSmoothCountLower p c profile.X
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf profile.X c n ≤ logCutoff c profile.X n
  a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf profile.X c n
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.lowEnergy n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n)
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.middleEnergy n ≤ Real.exp (-((1 / c) - δ) * paperRate profile.X n)
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n)
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog profile.X n
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog profile.X n ≤ Real.exp (scale n)

namespace Wave16L21_2Shape

variable (S : Wave16L21_2Shape)

/-- The shape carries the same ten elementary fields, now with a sequence
line constant. -/
theorem elementary_fields :
    0 < S.c ∧ S.c ≤ 1 ∧ (∀ n, 3 ≤ bandLog S.profile.X n) ∧
      (∀ n, 0 ≤ S.Kline n) ∧ (∀ n, 0 ≤ S.Ktail n) ∧
      (∀ᶠ n : ℕ in atTop, bOf S.profile.X S.c n ≤ logCutoff S.c S.profile.X n) ∧
      (∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf S.profile.X S.c n) ∧
      (∀ m : ℝ, 0 < m →
        ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog S.profile.X n) ∧
      (∀ᶠ n : ℕ in atTop, bandLog S.profile.X n ≤ Real.exp (scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        wave16Kref S.profile.X n + (3 * Real.exp 1 / Real.pi) * stripK + S.Ktail n ≤
          (S.Kline n / Real.pi) *
            (1 + Real.log (S.profile.X n ^ 3 / perronRe))) :=
  ⟨S.c_pos, S.c_le_one, S.U_ge_three, S.Kline_nonneg, S.Ktail_nonneg,
    S.b_le_B, S.a_ge_log_two, S.U_dominates, S.U_le_exp, S.Ksum_le⟩

end Wave16L21_2Shape

/-- **The genuinely analytic inputs.**  Everything else is proved below. -/
structure ElementaryInputs where
  /-- The finite Fourier/tent profile. -/
  profile : TentProfile
  /-- The band parameter is the explicit `elementaryX`. -/
  X_eq : profile.X = elementaryX
  /-- The raw vertical-tail constant; its positive part is used. -/
  KtailRaw : ℕ → ℝ
  /-- The Riemann hypothesis for `ζ`. -/
  hRH : RiemannZetaZerosOnLine
  /-- The standard `ζ'/ζ` line bound at `Re s = 2/3`, at the explicit
  sequence line constant. -/
  lineBound : VerticalLineBound profile.X
    (elementaryKline profile.X (elementaryKtail KtailRaw)) (elementaryCper - 1)
  /-- The vertical-tail estimate. -/
  verticalTail : VerticalTailBound profile.X (elementaryKtail KtailRaw)
    (elementaryCper - 1)
  /-- The literal short-interval smooth count. -/
  localCount : ShortIntervalSmoothCountLower elementaryX elementaryC profile.X
  /-- Low-frequency energy bound. -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.lowEnergy n ≤
      Real.exp (-(((2 * elementaryC) / 3) - δ) * paperRate profile.X n)
  /-- Middle-frequency energy bound. -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.middleEnergy n ≤
      Real.exp (-((1 / elementaryC) - δ) * paperRate profile.X n)
  /-- High-frequency energy bound. -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.tailEnergy n ≤
      Real.exp (-δ * paperRate profile.X n)

namespace ElementaryInputs

variable (I : ElementaryInputs)

/-- **Exactly the fields that remain analytic.**  Apart from the bookkeeping
identification `profile.X = elementaryX`, the record carries only the zeta-side
line and tail estimates, the literal short-interval count, and the three
Fourier band bounds. -/
theorem remaining_analytic_inputs :
    RiemannZetaZerosOnLine ∧
      VerticalLineBound I.profile.X
        (elementaryKline I.profile.X (elementaryKtail I.KtailRaw))
        (elementaryCper - 1) ∧
      VerticalTailBound I.profile.X (elementaryKtail I.KtailRaw)
        (elementaryCper - 1) ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC I.profile.X ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        I.profile.lowEnergy n ≤
          Real.exp (-(((2 * elementaryC) / 3) - δ) * paperRate I.profile.X n)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        I.profile.middleEnergy n ≤
          Real.exp (-((1 / elementaryC) - δ) * paperRate I.profile.X n)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        I.profile.tailEnergy n ≤ Real.exp (-δ * paperRate I.profile.X n)) :=
  ⟨I.hRH, I.lineBound, I.verticalTail, I.localCount, I.fourierLow,
    I.fourierMiddle, I.fourierTail⟩

/-- **The reduction.**  From the five analytic inputs, the explicit parameter
choices satisfy every numerical field of the wave-16 L21.2 record. -/
noncomputable def toShape : Wave16L21_2Shape where
  profile := I.profile
  c := elementaryC
  Cper := elementaryCper
  Kline := elementaryKline I.profile.X (elementaryKtail I.KtailRaw)
  Ktail := elementaryKtail I.KtailRaw
  p := elementaryX
  X_gt_one := by
    intro n
    rw [I.X_eq]
    exact elementaryX_gt_one n
  c_pos := elementaryC_pos
  c_le_one := elementaryC_le_one
  U_ge_three := by
    intro n
    rw [I.X_eq, bandLog_elementaryX]
    exact elementaryU_ge_three n
  Cper_ge_three := by
    unfold elementaryCper
    norm_num
  Kline_nonneg := elementaryKline_nonneg _ _ 
  Ktail_nonneg := elementaryKtail_nonneg I.KtailRaw
  Ksum_le := by
    rw [show I.profile.X = elementaryX from I.X_eq]
    exact elementaryKsum_le elementaryX elementaryX_gt_one
      (elementaryKtail I.KtailRaw)
  hRH := I.hRH
  lineBound := I.lineBound
  verticalTail := I.verticalTail
  p_gt_one := by
    filter_upwards with n
    exact elementaryX_gt_one n
  localCount := I.localCount
  b_le_B := by
    rw [show I.profile.X = elementaryX from I.X_eq]
    exact elementary_b_le_B
  a_ge_log_two := by
    rw [show I.profile.X = elementaryX from I.X_eq]
    exact elementary_a_ge_log_two
  fourierLow := I.fourierLow
  fourierMiddle := I.fourierMiddle
  fourierTail := I.fourierTail
  U_dominates := by
    intro m hm
    rw [show I.profile.X = elementaryX from I.X_eq]
    exact elementaryU_dominates m hm
  U_le_exp := by
    rw [show I.profile.X = elementaryX from I.X_eq]
    exact elementaryU_le_exp

/-- The reduced record has every numerical field. -/
theorem toShape_elementary_fields :
    0 < I.toShape.c ∧ I.toShape.c ≤ 1 ∧
      (∀ n, 3 ≤ bandLog I.toShape.profile.X n) ∧
      (∀ n, 0 ≤ I.toShape.Kline n) ∧ (∀ n, 0 ≤ I.toShape.Ktail n) ∧
      (∀ᶠ n : ℕ in atTop,
        bOf I.toShape.profile.X I.toShape.c n ≤
          logCutoff I.toShape.c I.toShape.profile.X n) ∧
      (∀ᶠ n : ℕ in atTop,
        Real.log 2 ≤ aOf I.toShape.profile.X I.toShape.c n) ∧
      (∀ m : ℝ, 0 < m → ∀ᶠ n : ℕ in atTop,
        m * scale n ^ 2 ≤ bandLog I.toShape.profile.X n) ∧
      (∀ᶠ n : ℕ in atTop,
        bandLog I.toShape.profile.X n ≤ Real.exp (scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        wave16Kref I.toShape.profile.X n +
            (3 * Real.exp 1 / Real.pi) * stripK + I.toShape.Ktail n ≤
          (I.toShape.Kline n / Real.pi) *
            (1 + Real.log (I.toShape.profile.X n ^ 3 / perronRe))) :=
  I.toShape.elementary_fields

end ElementaryInputs

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Elementary.elementaryC_pos
#print axioms Cogentic.RandomizedL21_2Elementary.elementaryC_le_one
#print axioms Cogentic.RandomizedL21_2Elementary.elementaryU_ge_three
#print axioms Cogentic.RandomizedL21_2Elementary.elementaryKline_nonneg
#print axioms Cogentic.RandomizedL21_2Elementary.elementaryKline_pos
#print axioms Cogentic.RandomizedL21_2Elementary.elementaryKtail_nonneg
#print axioms Cogentic.RandomizedL21_2Elementary.elementaryU_dominates
#print axioms Cogentic.RandomizedL21_2Elementary.elementaryU_le_exp
#print axioms Cogentic.RandomizedL21_2Elementary.elementary_b_le_B
#print axioms Cogentic.RandomizedL21_2Elementary.elementary_a_ge_log_two
#print axioms Cogentic.RandomizedL21_2Elementary.elementaryKsum_le
#print axioms Cogentic.RandomizedL21_2Elementary.ElementaryInputs.remaining_analytic_inputs
#print axioms Cogentic.RandomizedL21_2Elementary.ElementaryInputs.toShape
#print axioms Cogentic.RandomizedL21_2Elementary.ElementaryInputs.toShape_elementary_fields

end

end Cogentic.RandomizedL21_2Elementary
