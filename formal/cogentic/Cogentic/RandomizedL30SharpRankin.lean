import Cogentic.RandomizedL30Sharp
import Cogentic.RandomizedL30UpperDensity

set_option maxHeartbeats 4000000

/-!
# L30: the sharp Rankin/saddle-point upper bound

`Cogentic/RandomizedL30Sharp` defines the *sharp* paper-scale upper predicates

* `PaperScaleSmoothUpperSharp C p ε`,
* `GlobalOddUpperDensitySharp C p ε`,
* `YounisOddPaperSharpCount c p ε` and its interval form,

with the true Dickman exponent `u log u`, `u = 2 log p / ((1+ε)t_p)`.  This file
supplies the missing analytic upper-bound half: the Rankin/saddle-point estimate
gives the sharp exponent with the explicit constant `C = 1`.

## The Rankin bound and the saddle

The explicit Rankin bound of `Cogentic.Randomized.smoothCount_rankin_upper` is

`Ψ(p², Y) ≤ (p²)^α ∏_{q ≤ Y} (1 - q^{-α})^{-1}`,   `0 < α < 1`.

Write `L = log (p²)`, `S = log Y = (1+ε)t_p`, `u = L / S`.  If the Euler product
obeys the saddle envelope

`log ∏_{q ≤ Y}(1 - q^{-α})^{-1} ≤ A · Y^{1-α} / ((1-α) log Y)`

and the saddle logarithm is

`s = (1-α) S = log u + log log u + 1`,

then

`α L + log ∏ ≤ L - s u + A e^s / s`.

Since `e^s / s = e · u · log u / (log u + log log u + 1) ≤ e u` and
`log log u + 1 ≥ A e` eventually, the right-hand side is at most
`L - u log u`.  Exponentiating gives the sharp estimate `Ψ ≤ p² exp(-u log u)`,
i.e. `PaperScaleSmoothUpperSharp 1 p ε`.

The analytic input is isolated as the predicate `RankinEulerSaddleUpper A p ε`,
which records the Euler-product envelope for every tilt `α ∈ (1/2, 1)`.  The
file proves that the optimal saddle tilt is eventually admissible (it lies in
`(1/2,1)`), derives the pointwise predicate `RankinSaddlePointUpper A p ε`, and
then proves

* `eventually_rankinSaddle_exponent_le` — the pure scalar saddle absorption,
* `eventually_two_mul_rankinSaddleS_lt_log_cutoff` — the optimal tilt lies in
  `(1/2, 1)`, and `eventually_rankinSaddleS_lt_log_cutoff` for `(0,1)`,
* `rankinSaddlePointUpper_of_eulerSaddle` — the general envelope gives the
  optimal-tilt input,
* `rankinSharpUpper_one_of_saddle` — the sharp Rankin expression with `C = 1`,
* `paperScaleSmoothUpperSharp_of_rankinSharp` — Rankin ⇒ sharp smooth upper,
* `paperScaleSmoothUpperSharp_one_of_saddle` — the combined sharp upper bound,
* `paperScaleSmoothUpperSharp_one_of_eulerSaddle` — the same from the general
  Euler-product envelope,
* `globalOddUpperDensitySharp_one_of_saddle` / `..._one_of_eulerSaddle` — the
  odd-density transfer.

## The lossy `(1-δ)` exponent

The Rankin bound with a fixed loss `δ > 0` yields only
`exp (-(1-δ) u log u)`, whose exponential factor is *larger* than the sharp
factor (for `δ > 0`).  The file records the exact direction of the comparison:

* `paperScaleSmoothUpperSharp_of_delta` holds only for `δ ≤ 0`,
* `paperScaleSmoothUpperSharpDelta_of_sharp` holds for `δ ≥ 0`,
* `not_delta_factor_le_sharp_factor` shows the comparison needed for
  `δ > 0` is false.

For a positive loss the honest conclusion is the matching-exponent relative
chain `paperRelative_of_deltaUpper`, which is the direct `δ`-analogue of
`paperRelative_of_sharpUpper`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or error
is set to zero.
-/

namespace Cogentic.RandomizedL30SharpRankin

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.RandomizedL30UpperDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.Randomized

noncomputable section

/-! ## 1. The Rankin product and the sharp Rankin predicate -/

/-- The explicit Euler product appearing in the Rankin bound. -/
def rankinEulerProduct (t err : ℕ → ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  ∏ q ∈ (Finset.Icc 2 ⌊smoothCutoff t err n⌋₊).filter Nat.Prime,
    (1 - (q : ℝ) ^ (-α))⁻¹

/-- **The sharp paper-scale Rankin upper bound.**  At every large scale there is
a tilt `α ∈ (0,1)` for which the explicit Rankin expression is already at most
`C p² exp (-(u log u))`.  This is the sharp-exponent analogue of
`RankinPaperUpper`. -/
def RankinPaperSharpUpper (C : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    (p n ^ 2) ^ α * rankinEulerProduct (paperT p) (paperError ε) α n ≤
      C * p n ^ 2 *
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n)))

/-- The saddle logarithm `s = log u + log log u + 1`.  It is the choice of
`(1-α) log Y` that makes the Rankin exponent `-s u + A e^s / s` absorb into
`-u log u` with a *constant* loss. -/
def rankinSaddleS (u : ℝ) : ℝ :=
  Real.log u + Real.log (Real.log u) + 1

/-- **The Rankin/saddle-point analytic input at a fixed tilt.**  For every tilt
`α ∈ (1/2, 1)` the Euler product is at most the standard saddle envelope
`A · Y^{1-α} / ((1-α) log Y)`.  This is the explicit form of the classical
Rankin/Chebyshev estimate for the `Y`-smooth Euler product.  The lower bound
`α > 1/2` is harmless: the optimal tilt tends to `1`. -/
def RankinEulerSaddleUpper (A : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ α : ℝ, 1 / 2 < α → α < 1 →
    Real.log (rankinEulerProduct (paperT p) (paperError ε) α n) ≤
      A * Real.exp ((1 - α) *
          Real.log (smoothCutoff (paperT p) (paperError ε) n)) /
        ((1 - α) * Real.log (smoothCutoff (paperT p) (paperError ε) n))

/-- **The Rankin/saddle-point analytic input.**  At the optimal tilt
`α = 1 - s / log Y` the Euler product is bounded by the saddle envelope
`A exp s / s`, and the tilt lies in `(0,1)`.  This is exactly the
Euler-product half of the Rankin saddle-point method; the counting half is
supplied by `smoothCount_rankin_upper`. -/
def RankinSaddlePointUpper (A : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∃ α : ℝ,
    0 < α ∧ α < 1 ∧
      (1 - α) * Real.log (smoothCutoff (paperT p) (paperError ε) n) =
        rankinSaddleS (paperDensityU p ε n) ∧
      Real.log (rankinEulerProduct (paperT p) (paperError ε) α n) ≤
        A * Real.exp (rankinSaddleS (paperDensityU p ε n)) /
          rankinSaddleS (paperDensityU p ε n)

/-! ## 2. The scalar saddle absorption -/

/-- `e^s / s ≤ e u` at the saddle `s = log u + log log u + 1`. -/
theorem rankinSaddleS_exp_div_le {u : ℝ} (hu : 1 < u)
    (hl1 : 1 ≤ Real.log u) :
    Real.exp (rankinSaddleS u) / rankinSaddleS u ≤ Real.exp 1 * u := by
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hl : 0 < Real.log u := zero_lt_one.trans_le hl1
  have hm : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hl1
  have hs_eq : rankinSaddleS u = Real.log u + Real.log (Real.log u) + 1 := rfl
  have hs_pos : 0 < rankinSaddleS u := by
    rw [hs_eq]
    linarith
  have hle : Real.log u ≤ rankinSaddleS u := by
    rw [hs_eq]
    linarith
  have hexp : Real.exp (rankinSaddleS u) =
      Real.exp 1 * u * Real.log u := by
    rw [hs_eq, Real.exp_add, Real.exp_add, Real.exp_log hu0, Real.exp_log hl]
    ring
  rw [hexp, div_le_iff₀ hs_pos]
  have heu : 0 ≤ Real.exp 1 * u := by positivity
  calc
    Real.exp 1 * u * Real.log u
        ≤ Real.exp 1 * u * rankinSaddleS u :=
          mul_le_mul_of_nonneg_left hle heu
    _ = Real.exp 1 * u * rankinSaddleS u := rfl

/-- **The saddle exponent absorption.**  With `s = log u + log log u + 1`,
`-s u + A e^s / s ≤ -u log u` as soon as `A e ≤ log log u + 1`. -/
theorem rankinSaddle_exponent_le {u s A : ℝ} (hu : 1 < u)
    (hl1 : 1 ≤ Real.log u) (hs : s = rankinSaddleS u)
    (hA : 0 ≤ A) (hm : A * Real.exp 1 ≤ Real.log (Real.log u) + 1) :
    -(s * u) + A * Real.exp s / s ≤ -(u * Real.log u) := by
  subst hs
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hl : 0 < Real.log u := zero_lt_one.trans_le hl1
  have hloglog_nonneg : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hl1
  have hs_eq : rankinSaddleS u = Real.log u + Real.log (Real.log u) + 1 := rfl
  have hs_pos : 0 < rankinSaddleS u := by rw [hs_eq]; linarith
  have hexp := rankinSaddleS_exp_div_le hu hl1
  have hAexp : A * (Real.exp (rankinSaddleS u) / rankinSaddleS u) ≤
      A * (Real.exp 1 * u) := mul_le_mul_of_nonneg_left hexp hA
  have hAexp' : A * Real.exp (rankinSaddleS u) / rankinSaddleS u ≤ A * Real.exp 1 * u := by
    calc
      A * Real.exp (rankinSaddleS u) / rankinSaddleS u
          = A * (Real.exp (rankinSaddleS u) / rankinSaddleS u) := by ring
      _ ≤ A * (Real.exp 1 * u) := hAexp
      _ = A * Real.exp 1 * u := by ring
  have hmain : -(rankinSaddleS u * u) + A * Real.exp 1 * u ≤
      -(u * Real.log u) := by
    have hmul : u * (A * Real.exp 1) ≤ u * (Real.log (Real.log u) + 1) :=
      mul_le_mul_of_nonneg_left hm hu0.le
    rw [hs_eq]
    nlinarith [hmul, hu0]
  linarith [hAexp', hmain]

/-- Eventual form of the saddle absorption for the paper sequence. -/
theorem eventually_rankinSaddle_exponent_le {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    ∀ᶠ n in atTop,
      -(rankinSaddleS (paperDensityU p ε n) * paperDensityU p ε n) +
          A * Real.exp (rankinSaddleS (paperDensityU p ε n)) /
            rankinSaddleS (paperDensityU p ε n) ≤
        -(paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
  have hu := tendsto_paperDensityU_of_growth h hε
  have hlu : Tendsto (fun n => Real.log (paperDensityU p ε n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu
  have hllu : Tendsto (fun n => Real.log (Real.log (paperDensityU p ε n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlu
  filter_upwards [hu.eventually_gt_atTop 1,
    hlu.eventually_ge_atTop 1,
    hllu.eventually_ge_atTop (A * Real.exp 1)] with n hu1 hl1 hm
  exact rankinSaddle_exponent_le hu1 hl1 rfl hA (by linarith)

/-- **The optimal saddle tilt is eventually admissible.**  At the paper scale,
`2 s < log Y = (1+ε)t_p` for `s = log u + log log u + 1`, so the optimal tilt
`α = 1 - s / log Y` eventually lies in `(1/2, 1)`.  The proof uses
`log u ≤ (1/2) u log u ≤ t_p/(2(1+ε))` and `log t_p = o(t_p)`. -/
theorem eventually_two_mul_rankinSaddleS_lt_log_cutoff {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      2 * rankinSaddleS (paperDensityU p ε n) <
        Real.log (smoothCutoff (paperT p) (paperError ε) n) := by
  let c : ℝ := ε * (2 + ε) / (1 + ε)
  have hc : 0 < c := by dsimp [c]; positivity
  have hαpos : 0 < 1 + ε := by positivity
  have h2αpos : 0 < 2 * (1 + ε) := by positivity
  have ht_tend := tendsto_paperT_of_growth h
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have hlu_tend : Tendsto (fun n => Real.log (paperDensityU p ε n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu_tend
  have hlogt_ratio : Tendsto (fun n => Real.log (paperT p n) / paperT p n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht_tend
  have hmul := eventually_paperDensityU_mul_log_le_paperT h hε
  have hlogt_lt : ∀ᶠ n in atTop, Real.log (paperT p n) < (c / 4) * paperT p n := by
    have hsmall := (tendsto_order.mp hlogt_ratio).2 (c / 4) (by positivity)
    filter_upwards [hsmall, eventually_paperT_pos_of_growth h] with n hn ht
    rw [div_lt_iff₀ ht] at hn
    exact hn
  have hconst_le : ∀ᶠ n in atTop,
      2 * (1 - Real.log (2 * (1 + ε))) ≤ (c / 2) * paperT p n := by
    have htbig := ht_tend.eventually_ge_atTop
      (max 1 (4 * (1 - Real.log (2 * (1 + ε))) / c))
    filter_upwards [htbig] with n hn
    have ht2 : 4 * (1 - Real.log (2 * (1 + ε))) / c ≤ paperT p n :=
      le_trans (le_max_right _ _) hn
    have ht2' : 4 * (1 - Real.log (2 * (1 + ε))) ≤ c * paperT p n := by
      simpa only [mul_comm] using (div_le_iff₀ hc).mp ht2
    nlinarith
  filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
    hu_tend.eventually_ge_atTop 2, hlu_tend.eventually_ge_atTop 1,
    hmul, hlogt_lt, hconst_le] with n hp ht hu2 hlu1 hmul_n hlogt_n hconst_n
  have hlogu_pos : 0 < Real.log (paperDensityU p ε n) := Real.log_pos (by linarith)
  have hlogu_half : Real.log (paperDensityU p ε n) ≤
      (1 / 2) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
    have h1 : (1 : ℝ) ≤ paperDensityU p ε n / 2 := by linarith
    have h := mul_le_mul_of_nonneg_left h1 hlogu_pos.le
    have h' : 1 * Real.log (paperDensityU p ε n) ≤
        (paperDensityU p ε n / 2) * Real.log (paperDensityU p ε n) := by
      simpa [mul_comm] using h
    calc
      Real.log (paperDensityU p ε n) = 1 * Real.log (paperDensityU p ε n) := by ring
      _ ≤ (paperDensityU p ε n / 2) * Real.log (paperDensityU p ε n) := h'
      _ = (1 / 2) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by ring
  have hulogu_le : paperDensityU p ε n * Real.log (paperDensityU p ε n) ≤
      paperT p n / (1 + ε) := by
    rw [le_div_iff₀ hαpos]
    linarith [hmul_n]
  have hlogu_le : Real.log (paperDensityU p ε n) ≤
      paperT p n / (2 * (1 + ε)) := by
    calc
      Real.log (paperDensityU p ε n)
          ≤ (1 / 2) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) :=
            hlogu_half
      _ ≤ (1 / 2) * (paperT p n / (1 + ε)) :=
            mul_le_mul_of_nonneg_left hulogu_le (by norm_num)
      _ = paperT p n / (2 * (1 + ε)) := by
            field_simp [hαpos.ne']
  have hloglogu_le : Real.log (Real.log (paperDensityU p ε n)) ≤
      Real.log (paperT p n / (2 * (1 + ε))) := by
    apply Real.log_le_log hlogu_pos
    exact hlogu_le
  have hlogdiv : Real.log (paperT p n / (2 * (1 + ε))) =
      Real.log (paperT p n) - Real.log (2 * (1 + ε)) := by
    rw [Real.log_div ht.ne' h2αpos.ne']
  have hs_bound : rankinSaddleS (paperDensityU p ε n) ≤
      paperT p n / (2 * (1 + ε)) +
        (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 1 := by
    unfold rankinSaddleS
    linarith [hlogu_le, hloglogu_le, hlogdiv]
  have hsum : 2 * (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 2 <
      c * paperT p n := by
    nlinarith [hlogt_n, hconst_n]
  have hc_eq : (1 : ℝ) / (1 + ε) + c = 1 + ε := by
    dsimp [c]
    field_simp [hαpos.ne']
    ring
  have hrate : 2 * (paperT p n / (2 * (1 + ε)) +
      (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 1) <
        (1 + ε) * paperT p n := by
    have hdouble : 2 * (paperT p n / (2 * (1 + ε))) = paperT p n / (1 + ε) := by
      field_simp [hαpos.ne']
    have hsplit : 2 * (paperT p n / (2 * (1 + ε)) +
        (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 1) =
        paperT p n / (1 + ε) +
          (2 * (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 2) := by
            calc
              2 * (paperT p n / (2 * (1 + ε)) +
                  (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 1)
                  = 2 * (paperT p n / (2 * (1 + ε))) +
                      (2 * (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 2) := by ring
              _ = paperT p n / (1 + ε) +
                      (2 * (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 2) := by
                    rw [hdouble]
    rw [hsplit]
    calc
      paperT p n / (1 + ε) +
          (2 * (Real.log (paperT p n) - Real.log (2 * (1 + ε))) + 2)
          < paperT p n / (1 + ε) + c * paperT p n := by linarith
      _ = ((1 : ℝ) / (1 + ε) + c) * paperT p n := by ring
      _ = (1 + ε) * paperT p n := by rw [hc_eq]
  have hlogy : Real.log (smoothCutoff (paperT p) (paperError ε) n) =
      (1 + ε) * paperT p n := by
    unfold smoothCutoff paperError
    rw [Real.log_exp]
  rw [hlogy]
  linarith [mul_le_mul_of_nonneg_left hs_bound (by norm_num : (0 : ℝ) ≤ 2), hrate]

/-- The weaker `s < log Y` form, convenient for the `(0,1)` tilt condition. -/
theorem eventually_rankinSaddleS_lt_log_cutoff {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      rankinSaddleS (paperDensityU p ε n) <
        Real.log (smoothCutoff (paperT p) (paperError ε) n) := by
  have h2 := eventually_two_mul_rankinSaddleS_lt_log_cutoff h hε
  have hu := tendsto_paperDensityU_of_growth h hε
  have hlu : Tendsto (fun n => Real.log (paperDensityU p ε n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu
  filter_upwards [h2, hu.eventually_ge_atTop 2, hlu.eventually_ge_atTop 1] with
    n hn hu2 hlu1
  have hlogu : 0 < Real.log (paperDensityU p ε n) := Real.log_pos (by linarith)
  have hllu : 0 ≤ Real.log (Real.log (paperDensityU p ε n)) := Real.log_nonneg hlu1
  have hs_pos : 0 < rankinSaddleS (paperDensityU p ε n) := by
    unfold rankinSaddleS
    linarith
  linarith

/-- **The general Euler-product saddle envelope gives the optimal-tilt
predicate.**  Choosing `α = 1 - s / log Y` and using the admissibility lemma
`eventually_rankinSaddleS_lt_log_cutoff` produces `RankinSaddlePointUpper`. -/
theorem rankinSaddlePointUpper_of_eulerSaddle
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε A : ℝ} (hε : 0 < ε)
    (hE : RankinEulerSaddleUpper A p ε) :
    RankinSaddlePointUpper A p ε := by
  have htilt := eventually_two_mul_rankinSaddleS_lt_log_cutoff h hε
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have hlu_tend : Tendsto (fun n => Real.log (paperDensityU p ε n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu_tend
  filter_upwards [hE, htilt, hu_tend.eventually_gt_atTop 1,
    hlu_tend.eventually_ge_atTop 1] with n hEn htilt_n hu1 hlu1
  set u : ℝ := paperDensityU p ε n with hu_def
  set y : ℝ := smoothCutoff (paperT p) (paperError ε) n with hy_def
  set s : ℝ := rankinSaddleS u with hs_def
  have hlogy_pos : 0 < Real.log y := by
    have hs_pos : 0 < s := by
      rw [hs_def]
      unfold rankinSaddleS
      have hllu : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hlu1
      linarith
    linarith [htilt_n, hs_pos]
  have hs_pos : 0 < s := by
    rw [hs_def]
    unfold rankinSaddleS
    have hllu : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hlu1
    linarith
  have hs_lt : s < Real.log y := by linarith [htilt_n]
  have hs_ratio : s / Real.log y < 1 / 2 := by
    rw [div_lt_iff₀ hlogy_pos]
    linarith [htilt_n]
  have hα0 : 1 / 2 < 1 - s / Real.log y := by linarith
  have hα1 : 1 - s / Real.log y < 1 := by
    rw [sub_lt_self_iff]
    positivity
  have htilt_eq : (1 - (1 - s / Real.log y)) * Real.log y = s := by
    field_simp [hlogy_pos.ne']
    ring
  have hbound := hEn (1 - s / Real.log y) hα0 hα1
  refine ⟨1 - s / Real.log y, by linarith, hα1, htilt_eq, ?_⟩
  have hexp_eq : Real.exp ((1 - (1 - s / Real.log y)) * Real.log y) =
      Real.exp s := by rw [htilt_eq]
  rw [hexp_eq, htilt_eq] at hbound
  simpa [hs_def, hu_def, hy_def] using hbound

/-! ## 3. The Rankin product: positivity and the sharp reduction -/

/-- The Rankin Euler product is strictly positive for `α > 0`. -/
theorem rankinEulerProduct_pos {t err : ℕ → ℝ} {α : ℝ} {n : ℕ} (hα : 0 < α) :
    0 < rankinEulerProduct t err α n := by
  unfold rankinEulerProduct
  refine Finset.prod_pos fun q hq => ?_
  have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqprime.two_le
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hlt : (q : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  exact inv_pos.mpr (sub_pos.mpr hlt)

/-- The paper parameter `u = log (p²) / log Y` in terms of the actual cutoff. -/
theorem paperDensityU_eq_log_sq_div_log_cutoff {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (_hp : 0 < p n) (ht : 0 < paperT p n) (hε : 0 < ε) :
    paperDensityU p ε n =
      Real.log (p n ^ 2) /
        Real.log (smoothCutoff (paperT p) (paperError ε) n) := by
  have hL : Real.log (p n ^ 2) = 2 * Real.log (p n) := by
    rw [Real.log_pow]
    push_cast
    ring
  have hY : Real.log (smoothCutoff (paperT p) (paperError ε) n) =
      (1 + ε) * paperT p n := by
    unfold smoothCutoff paperError
    rw [Real.log_exp]
  rw [hL, hY]
  unfold paperDensityU
  have hα : (1 + ε) ≠ 0 := by positivity
  field_simp [ht.ne', hα]

/-- **The Rankin saddle bound gives the sharp Rankin expression with `C = 1`.**
This is the optimisation step: the tilt `α` is the one supplied by
`RankinSaddlePointUpper`, and the scalar absorption converts
`-s u + A e^s / s` into `-u log u`. -/
theorem rankinSharpUpper_one_of_saddle
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    {A : ℝ} (hA : 0 ≤ A) (hS : RankinSaddlePointUpper A p ε) :
    RankinPaperSharpUpper 1 p ε := by
  have hexp := eventually_rankinSaddle_exponent_le h hε hA
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have hlu_tend : Tendsto (fun n => Real.log (paperDensityU p ε n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu_tend
  filter_upwards [hS, hexp, h.eventually_sixteen,
    eventually_paperT_pos_of_growth h, hu_tend.eventually_gt_atTop 1,
    hlu_tend.eventually_ge_atTop 1] with
    n hn hexpn hp ht hu1 hlu1
  obtain ⟨α, hα0, hα1, htilt, hlog⟩ := hn
  have hp0 : 0 < p n := by linarith
  have hp2 : 0 < p n ^ 2 := by positivity
  have hp2one : (1 : ℝ) < p n ^ 2 := by nlinarith
  have hy : 0 < smoothCutoff (paperT p) (paperError ε) n := Real.exp_pos _
  have hprod := rankinEulerProduct_pos (t := paperT p) (err := paperError ε)
    (n := n) hα0
  have hu_eq : paperDensityU p ε n =
      Real.log (p n ^ 2) /
        Real.log (smoothCutoff (paperT p) (paperError ε) n) :=
    paperDensityU_eq_log_sq_div_log_cutoff hp0 ht hε
  set u : ℝ := paperDensityU p ε n with hu_def
  set y : ℝ := smoothCutoff (paperT p) (paperError ε) n with hy_def
  set s : ℝ := rankinSaddleS u with hs_def
  set L : ℝ := Real.log (p n ^ 2) with hL_def
  have hs_pos : 0 < s := by
    rw [hs_def]
    unfold rankinSaddleS
    have hllu : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hlu1
    linarith
  have hlogy_pos : 0 < Real.log y := by
    have hprod_pos : 0 < (1 - α) * Real.log y := by
      rw [htilt]
      exact hs_pos
    have hcoef : 0 < 1 - α := by linarith
    by_contra hle
    have hle' : Real.log y ≤ 0 := le_of_not_gt hle
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef.le hle']
  have hu_eq' : u = L / Real.log y := by
    rw [hu_def, hL_def, hy_def]
    exact hu_eq
  have halphaL : α * L = L - s * u := by
    have hsu : s * u = (1 - α) * L := by
      rw [htilt.symm, hu_eq']
      field_simp [hlogy_pos.ne']
    rw [hsu]
    ring
  have hlog_eq : Real.log
      ((p n ^ 2) ^ α * rankinEulerProduct (paperT p) (paperError ε) α n) =
      α * L + Real.log (rankinEulerProduct (paperT p) (paperError ε) α n) := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hp2 α).ne' hprod.ne',
      Real.log_rpow hp2]
  have hbound_log : Real.log
      ((p n ^ 2) ^ α * rankinEulerProduct (paperT p) (paperError ε) α n) ≤
      L - u * Real.log u := by
    rw [hlog_eq]
    have hlog' : Real.log (rankinEulerProduct (paperT p) (paperError ε) α n) ≤
        A * Real.exp s / s := by
      simpa [s, u] using hlog
    have hexp' : -(s * u) + A * Real.exp s / s ≤ -(u * Real.log u) := by
      simpa [s, u] using hexpn
    calc
      α * L + Real.log (rankinEulerProduct (paperT p) (paperError ε) α n)
          ≤ α * L + A * Real.exp s / s := by linarith [hlog']
      _ = L - s * u + A * Real.exp s / s := by rw [halphaL]
      _ ≤ L - u * Real.log u := by linarith [hexp']
  have hZpos : 0 < (p n ^ 2) ^ α *
      rankinEulerProduct (paperT p) (paperError ε) α n :=
    mul_pos (Real.rpow_pos_of_pos hp2 α) hprod
  have hZle : (p n ^ 2) ^ α *
      rankinEulerProduct (paperT p) (paperError ε) α n ≤
        Real.exp (L - u * Real.log u) := by
    rw [← Real.log_le_iff_le_exp hZpos]
    exact hbound_log
  have hexpL : Real.exp L = p n ^ 2 := Real.exp_log hp2
  refine ⟨α, hα0, hα1, ?_⟩
  calc
    (p n ^ 2) ^ α * rankinEulerProduct (paperT p) (paperError ε) α n
        ≤ Real.exp (L - u * Real.log u) := hZle
    _ = Real.exp L * Real.exp (-(u * Real.log u)) := by
          rw [← Real.exp_add]
          ring_nf
    _ = p n ^ 2 * Real.exp (-(u * Real.log u)) := by rw [hexpL]
    _ = 1 * p n ^ 2 * Real.exp (-(u * Real.log u)) := by ring

/-! ## 4. From the sharp Rankin expression to the sharp smooth upper bound -/

/-- **The Rankin bound with the sharp exponent implies the sharp paper-scale
smooth upper estimate.**  This is the sharp-exponent analogue of
`paperScaleSmoothUpper_of_rankin`; the only counting input is the existing
`smoothCount_rankin_upper`. -/
theorem paperScaleSmoothUpperSharp_of_rankinSharp
    {C : ℝ} (_hC : 0 < C) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (hR : RankinPaperSharpUpper C p ε) :
    PaperScaleSmoothUpperSharp C p ε := by
  filter_upwards [hR, h.eventually_sixteen,
    eventually_paperSmoothCutoff_ge_two p h hε] with n hn hp hy
  obtain ⟨α, hα0, hα1, hbound⟩ := hn
  have hp1 : (1 : ℝ) ≤ p n ^ 2 := by
    have h16 : (16 : ℝ) ≤ p n := hp
    nlinarith [sq_nonneg (p n - 4), h16]
  have hcard := smoothCount_rankin_upper
    (x := p n ^ 2) (y := smoothCutoff (paperT p) (paperError ε) n)
    hp1 hy hα0 hα1
  have hfilter : (Finset.Icc 1 ⌊p n ^ 2⌋₊).filter
        (IsSmoothUpTo (smoothCutoff (paperT p) (paperError ε) n)) =
      (Finset.Icc 1 ⌊p n ^ 2⌋₊).filter
        (fun m : ℕ => ∀ q ∈ m.primeFactors,
          (q : ℝ) ≤ smoothCutoff (paperT p) (paperError ε) n) := by
    apply Finset.filter_congr
    intro m _
    rfl
  have hcard' : ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
      (p n ^ 2) ^ α *
        rankinEulerProduct (paperT p) (paperError ε) α n := by
    rw [globalSmoothOrders, hfilter]
    simpa [rankinEulerProduct] using hcard
  exact hcard'.trans hbound

/-- **The sharp smooth upper bound from the Rankin saddle-point input with the
explicit constant `C = 1`.** -/
theorem paperScaleSmoothUpperSharp_one_of_saddle
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    {A : ℝ} (hA : 0 ≤ A) (hS : RankinSaddlePointUpper A p ε) :
    PaperScaleSmoothUpperSharp 1 p ε :=
  paperScaleSmoothUpperSharp_of_rankinSharp one_pos h hε
    (rankinSharpUpper_one_of_saddle h hε hA hS)

/-- **The odd-density transfer at the sharp exponent, with `C = 1`.** -/
theorem globalOddUpperDensitySharp_one_of_saddle
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    {A : ℝ} (hA : 0 ≤ A) (hS : RankinSaddlePointUpper A p ε) :
    GlobalOddUpperDensitySharp 1 p ε :=
  globalOddUpperDensitySharp_of_paperScaleSharp h
    (paperScaleSmoothUpperSharp_one_of_saddle h hε hA hS)

/-- **The sharp Rankin expression from the general Euler-product saddle
envelope.** -/
theorem rankinSharpUpper_one_of_eulerSaddle
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε A : ℝ} (hε : 0 < ε)
    (hA : 0 ≤ A) (hE : RankinEulerSaddleUpper A p ε) :
    RankinPaperSharpUpper 1 p ε :=
  rankinSharpUpper_one_of_saddle h hε hA
    (rankinSaddlePointUpper_of_eulerSaddle h hε hE)

/-- **The sharp paper-scale smooth upper bound from the general Rankin saddle
envelope, with the explicit constant `C = 1`.** -/
theorem paperScaleSmoothUpperSharp_one_of_eulerSaddle
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε A : ℝ} (hε : 0 < ε)
    (hA : 0 ≤ A) (hE : RankinEulerSaddleUpper A p ε) :
    PaperScaleSmoothUpperSharp 1 p ε :=
  paperScaleSmoothUpperSharp_of_rankinSharp one_pos h hε
    (rankinSharpUpper_one_of_eulerSaddle h hε hA hE)

/-- **The sharp odd-density transfer from the general Rankin saddle envelope,
with `C = 1`.** -/
theorem globalOddUpperDensitySharp_one_of_eulerSaddle
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε A : ℝ} (hε : 0 < ε)
    (hA : 0 ≤ A) (hE : RankinEulerSaddleUpper A p ε) :
    GlobalOddUpperDensitySharp 1 p ε :=
  globalOddUpperDensitySharp_of_paperScaleSharp h
    (paperScaleSmoothUpperSharp_one_of_eulerSaddle h hε hA hE)

/-- The odd-density transfer from the sharp Rankin expression with an arbitrary
positive constant. -/
theorem globalOddUpperDensitySharp_of_rankinSharp
    {C : ℝ} (hC : 0 < C) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (hR : RankinPaperSharpUpper C p ε) :
    GlobalOddUpperDensitySharp C p ε :=
  globalOddUpperDensitySharp_of_paperScaleSharp h
    (paperScaleSmoothUpperSharp_of_rankinSharp hC h hε hR)

/-- **The saddle upper bound feeds the sharp relative-density chain of
`RandomizedL30Sharp`.**  With `C = 1` the constant condition of
`paperRelative_of_sharpUpper` is `A ≤ c`. -/
theorem paperRelative_of_saddleUpper
    {A c A₀ : ℝ} {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    (hA₀ : 0 ≤ A₀) (hS : RankinSaddlePointUpper A₀ p ε)
    (hA : 0 ≤ A) (hAC : A * 1 ≤ c)
    (hcount : YounisOddPaperSharpIntervalCount c p ε) :
    EventuallyYounisOddSharpRelativeShortInterval A p ε :=
  paperRelative_of_sharpUpper hA hAC hcount
    (globalOddUpperDensitySharp_one_of_saddle h hε hA₀ hS)

/-! ## 5. The lossy `(1-δ)` exponent -/

/-- The paper-scale smooth upper bound with the lossy exponent
`exp (-(1-δ) (u log u))`. -/
def PaperScaleSmoothUpperSharpDelta (C δ : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
      C * p n ^ 2 *
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n)))

/-- The global odd upper density with the lossy exponent. -/
def GlobalOddUpperDensitySharpDelta (C δ : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 ≤
      C * Real.exp (-(1 - δ) * (paperDensityU p ε n *
        Real.log (paperDensityU p ε n)))

/-- The sharp local interval count with the lossy exponent. -/
def YounisOddPaperSharpIntervalCountDelta (c δ : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n))) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n

/-- The relative short-interval density at matching lossy exponents.  The
relative inequality itself has no exponent, so this is the same shape as
`EventuallyYounisOddSharpRelativeShortInterval`; the `δ` records that the
inputs were stated with the lossy exponent. -/
def EventuallyYounisOddSharpRelativeShortIntervalDelta
    (A _δ : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n

/-- The two exponential factors differ by `exp (δ (u log u))`. -/
theorem delta_factor_eq (δ u : ℝ) :
    Real.exp (-(1 - δ) * (u * Real.log u)) =
      Real.exp (-(u * Real.log u)) * Real.exp (δ * (u * Real.log u)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- For `δ > 0` and `u log u > 0`, the lossy factor is *strictly larger* than
the sharp factor.  Hence the lossy upper bound cannot be used to prove the
sharp one by monotonicity, and no constant `C` can absorb the gap because
`exp (δ u log u) → ∞`. -/
theorem not_delta_factor_le_sharp_factor {δ u : ℝ}
    (hu : 0 < u) (hlogu : 0 < Real.log u) (hδ : 0 < δ) :
    ¬ Real.exp (-(1 - δ) * (u * Real.log u)) ≤
        Real.exp (-(u * Real.log u)) := by
  have hX : 0 < u * Real.log u := mul_pos hu hlogu
  have hlt : -(u * Real.log u) < -(1 - δ) * (u * Real.log u) := by
    nlinarith [mul_pos hδ hX]
  exact not_le_of_gt (Real.exp_lt_exp.mpr hlt)

/-- For `δ ≤ 0` the lossy exponent is at least the sharp one, so the lossy
upper bound implies the sharp upper bound (for `C ≥ 0`). -/
theorem paperScaleSmoothUpperSharp_of_delta
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : δ ≤ 0) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (hD : PaperScaleSmoothUpperSharpDelta C δ p ε) :
    PaperScaleSmoothUpperSharp C p ε := by
  have hu := tendsto_paperDensityU_of_growth h hε
  have hlu : Tendsto (fun n => Real.log (paperDensityU p ε n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu
  filter_upwards [hD, hu.eventually_gt_atTop 1,
    hlu.eventually_ge_atTop 0] with n hn hu1 hlu1
  have hX : 0 ≤ paperDensityU p ε n * Real.log (paperDensityU p ε n) :=
    mul_nonneg (zero_lt_one.trans hu1).le hlu1
  have hcoef : 1 ≤ 1 - δ := by linarith
  have hrate : 1 * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) ≤
      (1 - δ) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hcoef hX
  have hfactor : Real.exp (-(1 - δ) * (paperDensityU p ε n *
        Real.log (paperDensityU p ε n))) ≤
      Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) := by
    apply Real.exp_le_exp.mpr
    linarith [hrate]
  exact hn.trans (mul_le_mul_of_nonneg_left hfactor (by positivity))

/-- For `δ ≥ 0` the sharp upper bound implies the lossy upper bound. -/
theorem paperScaleSmoothUpperSharpDelta_of_sharp
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (hS : PaperScaleSmoothUpperSharp C p ε) :
    PaperScaleSmoothUpperSharpDelta C δ p ε := by
  have hu := tendsto_paperDensityU_of_growth h hε
  have hlu : Tendsto (fun n => Real.log (paperDensityU p ε n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu
  filter_upwards [hS, hu.eventually_gt_atTop 1,
    hlu.eventually_ge_atTop 0] with n hn hu1 hlu1
  have hX : 0 ≤ paperDensityU p ε n * Real.log (paperDensityU p ε n) :=
    mul_nonneg (zero_lt_one.trans hu1).le hlu1
  have hcoef : 1 - δ ≤ 1 := by linarith
  have hrate : (1 - δ) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) ≤
      1 * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hcoef hX
  have hfactor : Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) ≤
      Real.exp (-(1 - δ) * (paperDensityU p ε n *
        Real.log (paperDensityU p ε n))) := by
    apply Real.exp_le_exp.mpr
    linarith [hrate]
  exact hn.trans (mul_le_mul_of_nonneg_left hfactor (by positivity))

/-- The parity transfer for the lossy exponent. -/
theorem globalOddUpperDensitySharpDelta_of_paperScaleSharpDelta
    {C δ : ℝ} {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ}
    (hD : PaperScaleSmoothUpperSharpDelta C δ p ε) :
    GlobalOddUpperDensitySharpDelta C δ p ε := by
  filter_upwards [hD, h.eventually_sixteen] with n hn hp
  have hp2 : 0 < p n ^ 2 := by
    have : 0 < p n := by linarith
    positivity
  have hsub : globalOddSmoothOrders p (paperT p) (paperError ε) n ⊆
      globalSmoothOrders p (paperT p) (paperError ε) n := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hcard : globalOddSmoothCount p (paperT p) (paperError ε) n ≤
      ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
    unfold globalOddSmoothCount
    exact_mod_cast Finset.card_le_card hsub
  rw [div_le_iff₀ hp2]
  calc
    globalOddSmoothCount p (paperT p) (paperError ε) n
        ≤ ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := hcard
    _ ≤ C * p n ^ 2 *
          Real.exp (-(1 - δ) * (paperDensityU p ε n *
            Real.log (paperDensityU p ε n))) := hn
    _ = C * Real.exp (-(1 - δ) * (paperDensityU p ε n *
            Real.log (paperDensityU p ε n))) * p n ^ 2 := by ring

/-- **The matching-exponent relative chain for the lossy exponent.**  This is
the exact sharp/local chain supported by a `(1-δ)` Rankin upper bound: the same
loss `δ` must be used on the local lower bound.  It is the `δ`-analogue of
`paperRelative_of_sharpUpper`; the case `δ = 0` is the sharp chain. -/
theorem paperRelative_of_deltaUpper {A c C δ : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hA : 0 ≤ A) (hAC : A * C ≤ c)
    (hcount : YounisOddPaperSharpIntervalCountDelta c δ p ε)
    (hupper : GlobalOddUpperDensitySharpDelta C δ p ε) :
    EventuallyYounisOddSharpRelativeShortIntervalDelta A δ p ε := by
  filter_upwards [hcount, hupper] with n hc hu
  have hI : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  have he : (0 : ℝ) ≤
      Real.exp (-(1 - δ) * (paperDensityU p ε n *
        Real.log (paperDensityU p ε n))) := (Real.exp_pos _).le
  have hstep1 : A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (C * Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n)))) :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  have hstep2 : A * ((centralOrderInterval p n).card : ℝ) *
        (C * Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n)))) ≤
      c * ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n))) := by
    have hmul := mul_le_mul_of_nonneg_right hAC
      (by positivity : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n))))
    calc
      A * ((centralOrderInterval p n).card : ℝ) *
          (C * Real.exp (-(1 - δ) * (paperDensityU p ε n *
            Real.log (paperDensityU p ε n))))
          = (A * C) * (((centralOrderInterval p n).card : ℝ) *
              Real.exp (-(1 - δ) * (paperDensityU p ε n *
                Real.log (paperDensityU p ε n)))) := by ring
      _ ≤ c * (((centralOrderInterval p n).card : ℝ) *
              Real.exp (-(1 - δ) * (paperDensityU p ε n *
                Real.log (paperDensityU p ε n)))) := hmul
      _ = c * ((centralOrderInterval p n).card : ℝ) *
              Real.exp (-(1 - δ) * (paperDensityU p ε n *
                Real.log (paperDensityU p ε n))) := by ring
  exact hstep1.trans (hstep2.trans hc)

/-- At `δ = 0` the lossy predicate is exactly the sharp predicate. -/
theorem paperScaleSmoothUpperSharpDelta_zero_iff
    (C : ℝ) (p : ℕ → ℝ) (ε : ℝ) :
    PaperScaleSmoothUpperSharpDelta C 0 p ε ↔ PaperScaleSmoothUpperSharp C p ε := by
  simp [PaperScaleSmoothUpperSharpDelta, PaperScaleSmoothUpperSharp]

/-! ## Axiom audit -/

#print axioms rankinSaddleS_exp_div_le
#print axioms rankinSaddle_exponent_le
#print axioms eventually_rankinSaddle_exponent_le
#print axioms eventually_two_mul_rankinSaddleS_lt_log_cutoff
#print axioms eventually_rankinSaddleS_lt_log_cutoff
#print axioms rankinSaddlePointUpper_of_eulerSaddle
#print axioms paperDensityU_eq_log_sq_div_log_cutoff
#print axioms rankinSharpUpper_one_of_saddle
#print axioms paperScaleSmoothUpperSharp_of_rankinSharp
#print axioms paperScaleSmoothUpperSharp_one_of_saddle
#print axioms globalOddUpperDensitySharp_one_of_saddle
#print axioms rankinSharpUpper_one_of_eulerSaddle
#print axioms paperScaleSmoothUpperSharp_one_of_eulerSaddle
#print axioms globalOddUpperDensitySharp_one_of_eulerSaddle
#print axioms globalOddUpperDensitySharp_of_rankinSharp
#print axioms paperRelative_of_saddleUpper
#print axioms not_delta_factor_le_sharp_factor
#print axioms paperScaleSmoothUpperSharp_of_delta
#print axioms paperScaleSmoothUpperSharpDelta_of_sharp
#print axioms paperRelative_of_deltaUpper
#print axioms paperScaleSmoothUpperSharpDelta_zero_iff

end

end Cogentic.RandomizedL30SharpRankin



