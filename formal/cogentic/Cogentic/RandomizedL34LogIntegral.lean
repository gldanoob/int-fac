import Cogentic.RandomizedL34ChebotarevSides
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# L34: the log-integral bracket, the probe budget and the cubic class count

`Cogentic.RandomizedL34ChebotarevSides` reduced the L34 leaf to a bundle of
explicit inputs.  Three of them were still stated as abstract `Prop`s over
arbitrary sequences:

* `LogIntegralBracket cbr (cutoff T) F T liX liBeta0`, the Stark/log-integral
  bracket `cbr x/(F T⁶) ≤ Li x - Li x^{β₀}`;
* `ProbeBudget R F T`, the paper's probe count `R = F T¹⁰`;
* `ClassCountCubicInput Ch classCount T`, the cubic class-count input.

This file discharges them for the paper's parameters.

## The logarithmic integral

`Li x = ∫₂ˣ dt / log t` is the literal logarithmic integral.  The quantitative
monotonicity `Li b - Li a ≥ (b - a)/log b` for `1 < a ≤ b` is proved from the
pointwise bound `1/log t ≥ 1/log b` on `[a,b]`; the ordinary monotonicity on
`[2,∞)` follows.  No analytic continuation or principal value is used: below `1`
the definition is the ordinary interval integral, and the bracket proof only
evaluates it above `1`.

## The Stark bracket at `x = 2^{T⁶}`

The paper's parameters are

* `x = 2^{T⁶}`, hence `log x = T⁶ log 2` (`cutoff_log`);
* `β₀ ≤ 1 - 1/(4 F log |Δ_E|)` (the classical Stark exceptional-zero bound);
* `log |Δ_E| ≤ T`, `T ≥ 2`, `F ≥ 1`, `0 < β₀`.

Then `x - x^{β₀} = x (1 - e^{-u})` with
`u = (1 - β₀) log x ≥ T⁵ log 2/(4F)`.  The elementary inequality
`1 - e^{-u} ≥ min(u/2, 1/2)` gives

`x log 2/(16F) ≤ x - x^{β₀}`,

and `Li x - Li x^{β₀} ≥ (x - x^{β₀})/log x` gives the bracket with the explicit
constant `cbr = 1/16`.  The only remaining input beyond Stark and the paper's
parameter bounds is `0 < β₀` (the exceptional zero is a genuine real zero); it is
isolated as `ExceptionalZeroPositive`.

## Probe count and class count

For integer-valued `F` and `T`, `paperProbeCount F T = F * T¹⁰` satisfies
`ProbeBudget` definitionally.  The smallest explicit remaining `Prop` is
`ProbeBudgetIntegral`, i.e. the paper's real product is integral at every index;
`exists_probeBudget_iff` proves it is exactly the existence of a probe count.

The class count is instantiated at `h* = Ch T³` and `classCount = 2^{Ch T³}`, so
Lemma E.2, the polynomial bound and the mask compression are definitional.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no loss, count,
error or mass is set to zero.
-/

namespace Cogentic.RandomizedL34LogIntegral

open Filter Real MeasureTheory intervalIntegral
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34ChebotarevSides

noncomputable section

/-! ## 1. The logarithmic integral -/

/-- The logarithmic integral `Li x = ∫₂ˣ dt / log t`. -/
noncomputable def Li (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

/-- `1/log t` is continuous on `[a,b]` when `1 < a`. -/
theorem continuousOn_inv_log_Icc {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc a b) := by
  refine ContinuousOn.inv₀ ?_ ?_
  · exact Real.continuousOn_log.mono (by
      intro x hx
      exact ne_of_gt (lt_trans zero_lt_one (lt_of_lt_of_le ha hx.1)))
  · intro x hx
    exact Real.log_ne_zero_of_pos_of_ne_one
      (lt_trans zero_lt_one (lt_of_lt_of_le ha hx.1))
      (by intro h; linarith [hx.1])

/-- `1/log t` is interval integrable on `[a,b]` when `1 < a ≤ b`. -/
theorem intervalIntegrable_inv_log_of_one_lt {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume a b :=
  (continuousOn_inv_log_Icc (b := b) ha).intervalIntegrable_of_Icc hab

/-- `1/log t` is interval integrable on `[2,b]` for every `1 < b`. -/
theorem intervalIntegrable_inv_log_two {b : ℝ} (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume (2 : ℝ) b := by
  rcases le_or_gt 2 b with h | h
  · exact intervalIntegrable_inv_log_of_one_lt (by norm_num) h
  · exact (intervalIntegrable_inv_log_of_one_lt hb (le_of_lt h)).symm

/-- **Quantitative monotonicity of `Li`.**  For `1 < a ≤ b`,
`Li b - Li a ≥ (b - a)/log b`.  On `[a,b]` the integrand `1/log t` is at least
`1/log b`. -/
theorem Li_sub_ge {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ Li b - Li a := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hfi_b := intervalIntegrable_inv_log_two hb
  have hfi_a := intervalIntegrable_inv_log_two ha
  have hsub : Li b - Li a = ∫ t in a..b, (Real.log t)⁻¹ := by
    unfold Li
    exact integral_interval_sub_left hfi_b hfi_a
  have hfi_ab := intervalIntegrable_inv_log_of_one_lt ha hab
  have hpoint : ∀ t ∈ Set.Icc a b, (Real.log b)⁻¹ ≤ (Real.log t)⁻¹ := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    have hle : Real.log t ≤ Real.log b := Real.log_le_log (by linarith) ht.2
    simpa [one_div] using one_div_le_one_div_of_le hlogt hle
  have hmono : (∫ t in a..b, (Real.log b)⁻¹) ≤
      ∫ t in a..b, (Real.log t)⁻¹ :=
    integral_mono_on (μ := volume) (a := a) (b := b) hab
      intervalIntegrable_const hfi_ab hpoint
  have hconst : (∫ t in a..b, (Real.log b)⁻¹) = (b - a) * (Real.log b)⁻¹ := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [hsub]
  calc
    (b - a) / Real.log b = (b - a) * (Real.log b)⁻¹ := by rw [div_eq_mul_inv]
    _ = ∫ t in a..b, (Real.log b)⁻¹ := hconst.symm
    _ ≤ ∫ t in a..b, (Real.log t)⁻¹ := hmono

/-- **Monotonicity of `Li` on `[2,∞)`.** -/
theorem Li_mono {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : Li a ≤ Li b := by
  have h := Li_sub_ge (lt_of_lt_of_le one_lt_two ha) hab
  have hlog : 0 < Real.log b := Real.log_pos (by linarith)
  have hnonneg : 0 ≤ (b - a) / Real.log b := div_nonneg (by linarith) hlog.le
  linarith

/-- `Li 2 = 0`. -/
theorem Li_two : Li 2 = 0 := by
  simp [Li]

/-! ## 2. Elementary exponential inequalities -/

/-- For `0 ≤ u ≤ 1`, `1 - e^{-u} ≥ u/2`.  The proof uses `e^u ≥ 1 + u`, hence
`e^{-u} ≤ 1/(1+u)`, and `u/(1+u) ≥ u/2`. -/
theorem one_sub_exp_neg_ge_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have h1 : (1 : ℝ) + u ≤ Real.exp u := by
    linarith [Real.add_one_le_exp u]
  have hpos : (0 : ℝ) < 1 + u := by linarith
  have hexp : Real.exp (-u) ≤ 1 / (1 + u) := by
    have h : 1 / Real.exp u ≤ 1 / (1 + u) := one_div_le_one_div_of_le hpos h1
    rw [Real.exp_neg]
    simpa [one_div] using h
  have hfrac : 1 - 1 / (1 + u) = u / (1 + u) := by
    field_simp
    ring
  have hle : u / 2 ≤ u / (1 + u) :=
    div_le_div_of_nonneg_left hu0 hpos (by linarith)
  linarith

/-- For `u ≥ log 2`, `1 - e^{-u} ≥ 1/2`. -/
theorem one_sub_exp_neg_ge_half_of_log_two_le {u : ℝ} (hu : Real.log 2 ≤ u) :
    (1 : ℝ) / 2 ≤ 1 - Real.exp (-u) := by
  have hexp : Real.exp (-u) ≤ 1 / 2 := by
    have h : Real.exp (-u) ≤ Real.exp (-(Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(Real.log 2)) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    linarith
  linarith

/-! ## 3. The Stark gap at `x = 2^{T⁶}` -/

/-- **The Stark/log-integral gap.**  Under the paper's parameters, the dyadic
cutoff satisfies `x log 2/(16F) ≤ x - x^{β₀}`.  This is the arithmetic core of
the bracket: after multiplying by `log x = T⁶ log 2` it becomes
`x/(16 F T⁶) log x ≤ x - x^{β₀}`. -/
theorem rpow_sub_ge_of_stark {X F T D β : ℝ}
    (hXpos : 0 < X) (hxlog : Real.log X = T ^ 6 * Real.log 2)
    (hT : 2 ≤ T) (hF : 0 < F) (hF1 : 1 ≤ F)
    (hD : 0 < D) (hDT : D ≤ T)
    (hβ0 : 0 < β) (hβ : β ≤ 1 - 1 / (4 * F * D)) :
    X * (Real.log 2 / (16 * F)) ≤ X - X ^ β := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < Real.log X := by
    rw [hxlog]
    exact mul_pos (by positivity) hlog2pos
  have hLnonneg : 0 ≤ Real.log X := hLpos.le
  have hdenpos : 0 < 4 * F * D := by
    have h4F : 0 < 4 * F := by nlinarith
    exact mul_pos h4F hD
  have hbeta_gap : 1 / (4 * F * D) ≤ 1 - β := by linarith
  have hgap_pos : 0 < 1 - β := by
    have hpos : 0 < 1 / (4 * F * D) := one_div_pos.mpr hdenpos
    linarith
  have hbeta_le_one : β ≤ 1 := by linarith
  set u : ℝ := (1 - β) * Real.log X with hu
  have hu_nonneg : 0 ≤ u := by
    rw [hu]
    exact mul_nonneg hgap_pos.le hLnonneg
  have hu_pos : 0 < u := by
    rw [hu]
    exact mul_pos hgap_pos hLpos
  have hu_ge : T ^ 5 * Real.log 2 / (4 * F) ≤ u := by
    have h4F : 0 ≤ 4 * F := by nlinarith
    have hdenle : 4 * F * D ≤ 4 * F * T :=
      mul_le_mul_of_nonneg_left hDT h4F
    have hfrac : 1 / (4 * F * T) ≤ 1 / (4 * F * D) :=
      one_div_le_one_div_of_le hdenpos hdenle
    have hmul := mul_le_mul_of_nonneg_right hfrac hLnonneg
    rw [hxlog] at hmul
    have hprod_nonneg : 0 ≤ T ^ 6 * Real.log 2 :=
      mul_nonneg (by positivity) hlog2pos.le
    have hstep2 : (1 / (4 * F * D)) * (T ^ 6 * Real.log 2) ≤ u := by
      rw [hu, hxlog]
      exact mul_le_mul_of_nonneg_right hbeta_gap hprod_nonneg
    have hstep1 : T ^ 5 * Real.log 2 / (4 * F) =
        (1 / (4 * F * T)) * (T ^ 6 * Real.log 2) := by
      field_simp
    calc
      T ^ 5 * Real.log 2 / (4 * F)
          = (1 / (4 * F * T)) * (T ^ 6 * Real.log 2) := hstep1
      _ ≤ (1 / (4 * F * D)) * (T ^ 6 * Real.log 2) := hmul
      _ ≤ u := hstep2
  have hxsub : X - X ^ β = X * (1 - Real.exp (-u)) := by
    have hp : X ^ β = X * Real.exp (-u) := by
      rw [Real.rpow_def_of_pos hXpos]
      have hL : Real.log X * β = Real.log X + -u := by
        rw [hu]
        ring
      rw [hL, Real.exp_add, Real.exp_log hXpos]
    rw [hp]
    ring
  have hA1 : Real.log 2 / (16 * F) ≤ T ^ 5 * Real.log 2 / (8 * F) := by
    have hT5 : (32 : ℝ) ≤ T ^ 5 := by
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hT 5
      norm_num at h ⊢
      linarith
    have hscalar : Real.log 2 / 16 ≤ T ^ 5 * Real.log 2 / 8 := by nlinarith
    calc
      Real.log 2 / (16 * F) = (Real.log 2 / 16) / F := by field_simp
      _ ≤ (T ^ 5 * Real.log 2 / 8) / F :=
          div_le_div_of_nonneg_right hscalar hF.le
      _ = T ^ 5 * Real.log 2 / (8 * F) := by field_simp
  have hA2 : Real.log 2 / (16 * F) ≤ 1 / 2 := by
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have h16 : (2 : ℝ) ≤ 16 * F := by nlinarith
    have h1 : Real.log 2 / (16 * F) ≤ 1 / (16 * F) :=
      div_le_div_of_nonneg_right hlog2le (by positivity)
    have h2 : 1 / (16 * F) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) h16
    linarith
  by_cases hu1 : u ≤ 1
  · have hge : u / 2 ≤ 1 - Real.exp (-u) := one_sub_exp_neg_ge_half hu_nonneg hu1
    have hfirst : X * (Real.log 2 / (16 * F)) ≤
        X * (T ^ 5 * Real.log 2 / (8 * F)) :=
      mul_le_mul_of_nonneg_left hA1 hXpos.le
    have hhalf : T ^ 5 * Real.log 2 / (8 * F) =
        (T ^ 5 * Real.log 2 / (4 * F)) / 2 := by
      field_simp
      ring
    have hsecond : X * (T ^ 5 * Real.log 2 / (8 * F)) ≤ X * (u / 2) := by
      apply mul_le_mul_of_nonneg_left _ hXpos.le
      rw [hhalf]
      linarith
    have hthird : X * (u / 2) ≤ X * (1 - Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hge hXpos.le
    linarith [hxsub]
  · have hu_gt : 1 < u := not_le.mp hu1
    have hlog2leu : Real.log 2 ≤ u := by
      have h : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      linarith
    have hge : (1 : ℝ) / 2 ≤ 1 - Real.exp (-u) :=
      one_sub_exp_neg_ge_half_of_log_two_le hlog2leu
    have hfirst : X * (Real.log 2 / (16 * F)) ≤ X * (1 / 2) :=
      mul_le_mul_of_nonneg_left hA2 hXpos.le
    have hsecond : X * (1 / 2) ≤ X * (1 - Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hge hXpos.le
    linarith [hxsub]

/-! ## 4. The paper's log-integral bracket -/

/-- The paper's `Li x` sequence at `x = 2^{T⁶}`. -/
noncomputable def paperLiX (T : ℕ → ℝ) : ℕ → ℝ :=
  fun n => Li (cutoff T n)

/-- The paper's `Li x^{β₀}` sequence at `x = 2^{T⁶}`. -/
noncomputable def paperLiBeta0 (beta0 T : ℕ → ℝ) : ℕ → ℝ :=
  fun n => Li ((cutoff T n) ^ (beta0 n))

/-- **The isolated real-zero condition.**  The possible exceptional zero is a
genuine real zero, hence strictly positive.  With the Stark line it implies
`β₀ ∈ (0,1)`, which is exactly what the log-integral bracket needs. -/
def ExceptionalZeroPositive (beta0 : ℕ → ℝ) : Prop :=
  ∀ n, 0 < beta0 n

/-- **The log-integral bracket for the paper's parameters.**  Stark's
exceptional-zero bound, the parameter bounds `log |Δ_E| ≤ T`, `T ≥ 2`,
`F ≥ 1`, and the single real-zero condition `0 < β₀` prove
`LogIntegralBracket (1/16) (cutoff T) F T (Li x) (Li x^{β₀})`. -/
theorem logIntegralBracket_paper {beta0 F T discLog : ℕ → ℝ}
    (hstark : StarkExceptionalZeroInput beta0 F discLog)
    (hT : ∀ n, 2 ≤ T n)
    (hbeta : ExceptionalZeroPositive beta0)
    (hDT : ∀ n, discLog n ≤ T n)
    (hF1 : ∀ n, 1 ≤ F n) :
    LogIntegralBracket (1 / 16) (cutoff T) F T
      (paperLiX T) (paperLiBeta0 beta0 T) := by
  have hβstark : ∀ n, beta0 n ≤ 1 - 1 / (4 * F n * discLog n) := by
    intro n
    simpa [starkLine] using not_lt.mp (hstark.no_exceptional_above n)
  refine ⟨by norm_num, ?_⟩
  intro n
  have hXpos : 0 < cutoff T n := cutoff_pos T n
  have hxlog : Real.log (cutoff T n) = (T n) ^ 6 * Real.log 2 := cutoff_log T n
  have hlogXpos : 0 < Real.log (cutoff T n) := by
    rw [hxlog]
    exact mul_pos (pow_pos (by linarith [hT n]) 6) (Real.log_pos (by norm_num))
  have hcore := rpow_sub_ge_of_stark (X := cutoff T n) (F := F n) (T := T n)
    (D := discLog n) (β := beta0 n) hXpos hxlog (hT n) (hstark.F_pos n) (hF1 n)
    (hstark.discLog_pos n) (hDT n) (hbeta n) (hβstark n)
  -- `x^β > 1` and `x^β ≤ x`.
  have hX1 : 1 < cutoff T n := by
    have hT6 : 0 < (T n) ^ 6 := pow_pos (by linarith [hT n]) 6
    have h := Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 2) hT6
    simpa [cutoff] using h
  have hY1 : 1 < (cutoff T n) ^ (beta0 n) := by
    rw [Real.rpow_def_of_pos hXpos]
    have hexp : 0 < Real.log (cutoff T n) * beta0 n :=
      mul_pos hlogXpos (hbeta n)
    calc
      (1 : ℝ) = Real.exp 0 := by simp
      _ < Real.exp (Real.log (cutoff T n) * beta0 n) := Real.exp_lt_exp.mpr hexp
  have hYX : (cutoff T n) ^ (beta0 n) ≤ cutoff T n := by
    have hb1 : beta0 n ≤ 1 := by
      have hden : 0 < 4 * F n * discLog n := by
        have h4F : 0 < 4 * F n := by nlinarith [hstark.F_pos n]
        exact mul_pos h4F (hstark.discLog_pos n)
      have hpos : 0 < 1 / (4 * F n * discLog n) := one_div_pos.mpr hden
      have := hβstark n
      linarith
    have hX1le : 1 ≤ cutoff T n := le_of_lt hX1
    simpa [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX1le hb1
  have hstep : bracketTerm (1 / 16) (cutoff T) F T n * Real.log (cutoff T n) ≤
      cutoff T n - (cutoff T n) ^ (beta0 n) := by
    have heq : bracketTerm (1 / 16) (cutoff T) F T n * Real.log (cutoff T n)
        = cutoff T n * (Real.log 2 / (16 * F n)) := by
      unfold bracketTerm
      rw [hxlog]
      have hFne : F n ≠ 0 := ne_of_gt (hstark.F_pos n)
      have hTne : T n ≠ 0 := ne_of_gt (by linarith [hT n])
      field_simp
    rw [heq]
    exact hcore
  have hle_div : bracketTerm (1 / 16) (cutoff T) F T n ≤
      (cutoff T n - (cutoff T n) ^ (beta0 n)) / Real.log (cutoff T n) :=
    (le_div_iff₀ hlogXpos).mpr hstep
  exact hle_div.trans (Li_sub_ge hY1 hYX)

/-- **The bracket from the existing `T⁶` range input.**  The packaged range
input supplies `log |Δ_E| ≤ T`, so the log-integral bracket is a consequence of
the range input, Stark's exceptional-zero bound, `T ≥ 2`, `F ≥ 1` and `0 < β₀`. -/
theorem logIntegralBracket_of_rangeInput {K : ℝ} {beta0 F T degree discLog : ℕ → ℝ}
    (hstark : StarkExceptionalZeroInput beta0 F discLog)
    (range : ChebotarevT6RangeInput K T degree discLog)
    (hT : ∀ n, 2 ≤ T n)
    (hbeta : ExceptionalZeroPositive beta0)
    (hF1 : ∀ n, 1 ≤ F n) :
    LogIntegralBracket (1 / 16) (cutoff T) F T
      (paperLiX T) (paperLiBeta0 beta0 T) :=
  logIntegralBracket_paper hstark hT hbeta range.discLog_le_T hF1

/-- **The bracket at the paper's literal factorial scale `F = (2d)!`.**  The
factorial factor is at least one, so `logIntegralBracket_paper` applies directly
to `StarkFactorialExceptionalZeroInput`. -/
theorem logIntegralBracket_factorial {beta0 : ℕ → ℝ} {degree : ℕ → ℕ}
    {discLog T : ℕ → ℝ}
    (hstark : StarkFactorialExceptionalZeroInput beta0 degree discLog)
    (hT : ∀ n, 2 ≤ T n)
    (hbeta : ExceptionalZeroPositive beta0)
    (hDT : ∀ n, discLog n ≤ T n) :
    LogIntegralBracket (1 / 16) (cutoff T) (absoluteFactorialFactor degree) T
      (paperLiX T) (paperLiBeta0 beta0 T) := by
  have hF1 : ∀ n, 1 ≤ absoluteFactorialFactor degree n := by
    intro n
    unfold absoluteFactorialFactor
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (2 * degree n)))
  have hstarkAbs : StarkExceptionalZeroInput beta0 (absoluteFactorialFactor degree)
      discLog :=
    StarkExceptionalZeroInput.ofStarkBetaUpper (absoluteFactorialFactor_pos degree)
      hstark.discLog_pos hstark.toStarkBetaUpper_absolute
  exact logIntegralBracket_paper hstarkAbs hT hbeta hDT hF1

/-! ## 5. The range arithmetic `log x ≤ F T⁶` -/

/-- **The log-integral range arithmetic.**  For `F ≥ 1`, the cutoff logarithm
`log (2^{T⁶}) = T⁶ log 2` is at most the bracket denominator `F T⁶`.  This is the
only range input used by the bracket beyond `T ≥ 2`. -/
theorem cutoff_log_le_bracket_denominator {F T : ℕ → ℝ}
    (hF1 : ∀ n, 1 ≤ F n) (n : ℕ) :
    Real.log (cutoff T n) ≤ F n * (T n) ^ 6 := by
  rw [cutoff_log]
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hT6 : 0 ≤ (T n) ^ 6 := by positivity
  calc
    (T n) ^ 6 * Real.log 2 ≤ (T n) ^ 6 * 1 :=
      mul_le_mul_of_nonneg_left hlog2le hT6
    _ = (T n) ^ 6 := by ring
    _ ≤ F n * (T n) ^ 6 := by
      simpa using mul_le_mul_of_nonneg_right (hF1 n) hT6

/-- **The paper's `T⁶` range budget at the cutoff.**  The existing range input
gives `K d (log |Δ_E|)² ≤ T⁶ log 2`, the form consumed by the effective
Chebotarev theorem. -/
theorem rangeT6_of_input {K : ℝ} {T degree discLog : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog) (n : ℕ) :
    K * degree n * (discLog n) ^ 2 ≤ (T n) ^ 6 * Real.log 2 := by
  have h := A.toChebotarevRangeInput.range n
  rwa [cutoff_log] at h

/-! ## 6. The probe-count budget `R = F T¹⁰` -/

/-- The paper's integer probe count `R = F T¹⁰` for integer-valued `F` and `T`. -/
def paperProbeCount (F T : ℕ → ℕ) (n : ℕ) : ℕ :=
  F n * T n ^ 10

/-- **The probe budget at the paper's integer parameters.**  `R = F T¹⁰` is
satisfied definitionally. -/
theorem paperProbeCount_budget (F T : ℕ → ℕ) :
    ProbeBudget (paperProbeCount F T) (fun n => (F n : ℝ)) (fun n => (T n : ℝ)) := by
  intro n
  unfold paperProbeCount
  push_cast
  ring

/-- The exact content of `ProbeBudget`: the real probe count is `F T¹⁰`. -/
theorem probeBudget_iff (R : ℕ → ℕ) (F T : ℕ → ℝ) :
    ProbeBudget R F T ↔ ∀ n, (R n : ℝ) = F n * T n ^ 10 :=
  Iff.rfl

/-- **The smallest remaining probe-count input.**  The paper's real product
`F T¹⁰` is integral at every index.  It holds automatically for integer-valued
`F`, `T` by `paperProbeCount_budget`. -/
def ProbeBudgetIntegral (F T : ℕ → ℝ) : Prop :=
  ∀ n, ∃ k : ℕ, F n * T n ^ 10 = (k : ℝ)

/-- **A probe count exists exactly when the paper's product is integral.** -/
theorem exists_probeBudget_iff {F T : ℕ → ℝ} :
    (∃ R : ℕ → ℕ, ProbeBudget R F T) ↔ ProbeBudgetIntegral F T := by
  constructor
  · rintro ⟨R, hR⟩ n
    exact ⟨R n, (hR n).symm⟩
  · intro h
    choose R hR using h
    exact ⟨R, fun n => (hR n).symm⟩

/-- The integral probe budget gives an explicit probe count. -/
theorem probeBudget_of_integral {F T : ℕ → ℝ} (h : ProbeBudgetIntegral F T) :
    ∃ R : ℕ → ℕ, ProbeBudget R F T :=
  exists_probeBudget_iff.mpr h

/-! ## 7. The cubic class-count input -/

/-- **The cubic class-count input at `h* = Ch T³`.**  With
`classCount = 2^{Ch T³}`, Lemma E.2 is an equality. -/
theorem classCountCubicInput_paper {Ch : ℝ} (hCh : 0 < Ch) (T : ℕ → ℝ) :
    ClassCountCubicInput Ch (fun n => (2 : ℝ) ^ (Ch * (T n) ^ 3)) T where
  Ch_pos := hCh
  cubic := fun _ => le_rfl

/-- Lemma E.2 at the paper's parameter identity. -/
theorem classCountBound_paper (Ch : ℝ) (T : ℕ → ℝ) :
    ClassCountBound (fun n => (2 : ℝ) ^ (Ch * (T n) ^ 3))
      (fun n => Ch * (T n) ^ 3) :=
  fun _ => le_rfl

/-- The polynomial bound `h* = O(T³)` at `h* = Ch T³`. -/
theorem classCountPolynomial_paper {Ch : ℝ} (hCh : 0 < Ch) (T : ℕ → ℝ) :
    ClassCountPolynomial Ch (fun n => Ch * (T n) ^ 3) T :=
  ⟨hCh, fun _ => le_rfl⟩

/-- The mask-compression budget at `m = h* + 7`. -/
theorem maskCompressionBits_paper (Ch : ℝ) (T : ℕ → ℝ) :
    MaskCompressionBits (fun n => Ch * (T n) ^ 3)
      (fun n => Ch * (T n) ^ 3 + 7) :=
  fun n => by linarith

/-! ## Axiom audit -/

#print axioms continuousOn_inv_log_Icc
#print axioms intervalIntegrable_inv_log_of_one_lt
#print axioms intervalIntegrable_inv_log_two
#print axioms Li_sub_ge
#print axioms Li_mono
#print axioms Li_two
#print axioms one_sub_exp_neg_ge_half
#print axioms one_sub_exp_neg_ge_half_of_log_two_le
#print axioms rpow_sub_ge_of_stark
#print axioms logIntegralBracket_paper
#print axioms logIntegralBracket_of_rangeInput
#print axioms logIntegralBracket_factorial
#print axioms cutoff_log_le_bracket_denominator
#print axioms rangeT6_of_input
#print axioms paperProbeCount_budget
#print axioms probeBudget_iff
#print axioms exists_probeBudget_iff
#print axioms probeBudget_of_integral
#print axioms classCountCubicInput_paper
#print axioms classCountBound_paper
#print axioms classCountPolynomial_paper
#print axioms maskCompressionBits_paper

end

end Cogentic.RandomizedL34LogIntegral
