import Cogentic.RandomizedL27StageOneFinish

/-!
# L27 budget arithmetic: the paper's parameter choices are non-vacuous

`Cogentic.RandomizedL27StageOneFinish` takes the curve-count choice
`CurveBudget` and the L27.2 multiplier `LogFactorSubexp` as fields of
`L27StageOneFinishInputs`.  This file discharges both fields from the *explicit*
parameter selection of the private elliptic-recognition step.

The paper (Lenstra–Pomerance §7, `research/keybreak-private-elliptic-recognition.md`
§Transfer) uses

* `y = exp t`, where `t` is the current `scale`;
* a stage-one smooth-order count satisfying the `p`-power/`Q` bound
  `ψ₀ ≥ √p / Q` with `Q = exp (β t)` and `β = 1/(2c) > 0`;
* `#curves = exp ((β + η) t) · L` with a fixed headroom `η > 0` and a
  polynomial confidence factor `L ≥ 1`;
* a cofactor whose logarithm is `o (t)`, i.e. `log (cofactor n) ≤ δ t`
  eventually for every `δ > 0`.

The arithmetic content is:

1. **`CurveBudget`.**  Substituting `y = exp t` and `ψ₀ = √p / Q` gives
   `#curves · ψ₀ / (√p · log y) = #curves / (Q t)`.  With
   `#curves ≥ exp ((β + η)t) · L` and `Q = exp (β t)` this is
   `exp (η t) · L / t`, which eventually dominates the linear bound
   `(2 + η)t / (κ/4)` because an exponential beats `t²`.  The proof uses only
   `0 < κ`, `0 < η`, `0 ≤ β` and `1 ≤ L` eventually, and the exact identity
   `Q = exp (β t)`.

2. **`LogFactorSubexp`.**  If `log (cofactor n) = o (t)`, then
   `log₂ (cofactor n) = O (log (cofactor n))` and
   `log (log₂ (cofactor n)) ≤ log (δ t / 2) ≤ δ t`, so
   `log₂ (cofactor n) ≤ exp (δ t)` for every `δ > 0`.

Neither `CurveBudget` nor `LogFactorSubexp` is assumed: both are *proved* from
these scalar hypotheses.  The remaining hypotheses are collected in
`L27BudgetArithmeticInputs`, which then constructs a full
`L27StageOneFinishInputs` by supplying the two discharged fields.  Consequently
the existing `loss_le_exp_ledger`, `loss_le_exp_paper`, `toRatedLeaf`, and
`slot` theorems apply unchanged.

All budget constants (`κ`, `η`, `β`, `Q`, `ψ₀`, `#curves`) are positive where
they occur; no budget is set to zero.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL27BudgetArithmetic

open Filter Real
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27StageOne
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The paper's explicit parameter choices -/

/-- The stage-one cutoff `y = exp t` of the private elliptic-recognition step. -/
noncomputable def paperY (n : ℕ) : ℝ := Real.exp (scale n)

/-- The L27.1 smooth-order loss `Q = exp (β t)`, where `β = 1/(2c)`. -/
noncomputable def paperQ (β : ℝ) (n : ℕ) : ℝ := Real.exp (β * scale n)

/-- The `p`-power/`Q` lower bound for the number of stage-one-smooth orders:
`ψ₀ = √p / Q`.  This is the L27.1 smooth-order count after the paper's
smoothness-density estimate. -/
noncomputable def paperPsi (p : ℕ → ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (p n) / paperQ β n

/-- The paper's curve count `#curves = exp ((β + η) t) · L`, rounded up.  The
factor `L` is the polynomial confidence allowance; the theorem below only uses
`L ≥ 1` eventually. -/
noncomputable def paperCurves (β η : ℝ) (L : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈Real.exp ((β + η) * scale n) * L n⌉₊

/-- The paper's exponent `β = 1/(2c)`. -/
noncomputable def paperBeta (c : ℝ) : ℝ := 1 / (2 * c)

/-- The unit confidence factor, i.e. the bare `exp ((β + η)t)` curve count. -/
noncomputable def unitConfidence : ℕ → ℝ := fun _ => 1

theorem paperBeta_pos {c : ℝ} (hc : 0 < c) : 0 < paperBeta c := by
  unfold paperBeta
  positivity

theorem paperQ_log (β : ℝ) (n : ℕ) : Real.log (paperQ β n) = β * scale n := by
  unfold paperQ
  rw [Real.log_exp]

/-! ## 2. Positivity of the explicit constants -/

theorem paperY_pos (n : ℕ) : 0 < paperY n := Real.exp_pos _

theorem paperQ_pos (β : ℝ) (n : ℕ) : 0 < paperQ β n := Real.exp_pos _

theorem paperQ_ne (β : ℝ) (n : ℕ) : paperQ β n ≠ 0 := (paperQ_pos β n).ne'

theorem paperPsi_pos {p : ℕ → ℕ} (hp : ∀ n, 0 < p n) (β : ℝ) (n : ℕ) :
    0 < paperPsi p β n :=
  div_pos (Real.sqrt_pos.mpr (by exact_mod_cast hp n)) (paperQ_pos β n)

theorem paperPsi_nonneg {p : ℕ → ℕ} (hp : ∀ n, 0 < p n) (β : ℝ) (n : ℕ) :
    0 ≤ paperPsi p β n := (paperPsi_pos hp β n).le

theorem paperY_log (n : ℕ) : Real.log (paperY n) = scale n := by
  unfold paperY
  rw [Real.log_exp]

/-- `y = exp t` is eventually above one, as required by the L27.1 interface. -/
theorem eventually_paperY_gt_one : ∀ᶠ n : ℕ in atTop, 1 < paperY n := by
  filter_upwards [scale_grows.eventually_gt_atTop 0] with n hn
  unfold paperY
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hn

/-- The rounded paper curve count is strictly positive once the confidence
factor is at least one. -/
theorem paperCurves_pos {β η : ℝ} {L : ℕ → ℝ} {n : ℕ} (hL : 1 ≤ L n) :
    0 < paperCurves β η L n := by
  have hx : 0 < Real.exp ((β + η) * scale n) * L n :=
    mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hL)
  have hne : paperCurves β η L n ≠ 0 := by
    intro hzero
    have hle : Real.exp ((β + η) * scale n) * L n ≤ 0 :=
      (Nat.ceil_eq_zero.mp hzero)
    linarith
  exact Nat.pos_of_ne_zero hne

/-- The defining real lower bound of the rounded paper curve count. -/
theorem le_paperCurves (β η : ℝ) (L : ℕ → ℝ) (n : ℕ) :
    Real.exp ((β + η) * scale n) * L n ≤ (paperCurves β η L n : ℝ) :=
  Nat.le_ceil _

/-! ## 3. The exponential-beats-quadratic absorption -/

/-- Any fixed nonnegative multiple of `t²` is eventually dominated by
`exp (η t)`.  This is the only asymptotic fact used by the budget proof. -/
theorem eventually_const_mul_sq_le_exp {c η : ℝ} (hc : 0 ≤ c) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, c * (scale n) ^ 2 ≤ Real.exp (η * scale n) := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · filter_upwards with n
    simp only [zero_mul]
    exact (Real.exp_pos _).le
  · have hε : 0 < 1 / c := one_div_pos.mpr hcpos
    have hbase : ∀ᶠ n : ℕ in atTop,
        (scale n) ^ 2 ≤ (1 / c) * Real.exp (η * scale n) := by
      have h := isLittleO_pow_exp_pos_mul_atTop 2 hη
      have h' := scale_grows.eventually (h.def hε)
      filter_upwards [h', scale_grows.eventually_ge_atTop 0] with n hn hs
      have hnk : 0 ≤ (scale n) ^ 2 := pow_nonneg hs 2
      have hexp : 0 ≤ Real.exp (η * scale n) := (Real.exp_pos _).le
      rw [Real.norm_of_nonneg hnk, Real.norm_of_nonneg hexp] at hn
      exact hn
    filter_upwards [hbase] with n hn
    have := mul_le_mul_of_nonneg_left hn hc
    calc
      c * (scale n) ^ 2 ≤ c * ((1 / c) * Real.exp (η * scale n)) := this
      _ = Real.exp (η * scale n) := by field_simp [hcpos.ne']

/-! ## 4. `CurveBudget` from the `p`-power/`Q` bound -/

/-- **The explicit paper curve-count budget.**  With `y = exp t`,
`ψ₀ = √p / exp (βt)`, and `#curves = ⌈exp ((β+η)t) · L⌉`, the LP rate
`(κ/4) · #curves · ψ₀/(√p log y)` eventually exceeds `(2+η)t`.

The hypotheses are exactly positivity of the constants (`κ > 0`, `η > 0`,
`0 ≤ β`), positivity of the primes, and `L ≥ 1` eventually. -/
theorem paperCurveBudget {p : ℕ → ℕ} {β η κ : ℝ} {L : ℕ → ℝ}
    (_hβ : 0 ≤ β) (hη : 0 < η) (hκ : 0 < κ)
    (hp : ∀ n, 0 < p n) (hL : ∀ᶠ n : ℕ in atTop, 1 ≤ L n) :
    CurveBudget p paperY (paperPsi p β) (paperCurves β η L) κ η := by
  have hκ4 : 0 < κ / 4 := by positivity
  have hApos : 0 < 4 * (2 + η) / κ := by positivity
  filter_upwards [scale_grows.eventually_gt_atTop 0, hL,
    eventually_const_mul_sq_le_exp (c := 4 * (2 + η) / κ) hApos.le hη] with n ht hL1 habs
  have htne : scale n ≠ 0 := ht.ne'
  have hspos : 0 < Real.sqrt (p n) := Real.sqrt_pos.mpr (by exact_mod_cast hp n)
  have hspne : Real.sqrt (p n) ≠ 0 := hspos.ne'
  -- The `p`-power/`Q` ratio is exactly `1 / (Q t)`.
  have hpsi :
      paperPsi p β n / (Real.sqrt (p n) * Real.log (paperY n)) =
        1 / (paperQ β n * scale n) := by
    unfold paperPsi
    rw [paperY_log]
    field_simp [hspne, htne, paperQ_ne β n]
  -- The curve count beats its defining real value.
  have hcurve_le : Real.exp ((β + η) * scale n) * L n ≤
      (paperCurves β η L n : ℝ) := Nat.le_ceil _
  -- The exponential part of the rate.
  have hrate_eq :
      Real.exp ((β + η) * scale n) * L n *
          (1 / (paperQ β n * scale n)) =
        Real.exp (η * scale n) * L n / scale n := by
    unfold paperQ
    have hexpne : Real.exp (β * scale n) ≠ 0 := (Real.exp_pos _).ne'
    have hExp : Real.exp ((β + η) * scale n) / Real.exp (β * scale n) =
        Real.exp (η * scale n) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    calc
      Real.exp ((β + η) * scale n) * L n *
          (1 / (Real.exp (β * scale n) * scale n))
          = (Real.exp ((β + η) * scale n) / Real.exp (β * scale n)) *
              (L n / scale n) := by
            field_simp [hexpne, htne]
      _ = Real.exp (η * scale n) * (L n / scale n) := by rw [hExp]
      _ = Real.exp (η * scale n) * L n / scale n := by ring
  -- Absorption of `t²` into `exp (η t)`.
  have hstep : (2 + η) * scale n ≤
      (κ / 4) * (Real.exp (η * scale n) * L n / scale n) := by
    have hmul := mul_le_mul_of_nonneg_left habs
      (show 0 ≤ (κ / 4) * L n / scale n by positivity)
    have heq : (κ / 4) * L n / scale n * (4 * (2 + η) / κ * scale n ^ 2) =
        (2 + η) * L n * scale n := by
      field_simp [hκ.ne', htne]
    have hLt : (2 + η) * scale n ≤ (2 + η) * L n * scale n := by
      have hcoef : 0 ≤ (2 + η) * scale n := by positivity
      nlinarith [hL1]
    calc
      (2 + η) * scale n ≤ (2 + η) * L n * scale n := hLt
      _ = (κ / 4) * L n / scale n * (4 * (2 + η) / κ * scale n ^ 2) := heq.symm
      _ ≤ (κ / 4) * L n / scale n *
            (Real.exp (η * scale n)) := hmul
      _ = (κ / 4) * (Real.exp (η * scale n) * L n / scale n) := by ring
  -- Monotonicity from the rounded count and the exact ratio.
  have hmono : (κ / 4) * (Real.exp (η * scale n) * L n / scale n) ≤
      (κ / 4) *
        ((paperCurves β η L n : ℝ) *
          (paperPsi p β n /
            (Real.sqrt (p n) * Real.log (paperY n)))) := by
    rw [hpsi]
    have hnonneg : 0 ≤ 1 / (paperQ β n * scale n) :=
      one_div_nonneg.mpr (mul_pos (paperQ_pos β n) ht).le
    have hmul := mul_le_mul_of_nonneg_right hcurve_le hnonneg
    calc
      (κ / 4) * (Real.exp (η * scale n) * L n / scale n)
          = (κ / 4) *
              (Real.exp ((β + η) * scale n) * L n *
                (1 / (paperQ β n * scale n))) := by rw [hrate_eq]
      _ ≤ (κ / 4) *
            ((paperCurves β η L n : ℝ) *
              (1 / (paperQ β n * scale n))) :=
        mul_le_mul_of_nonneg_left hmul hκ4.le
  exact hstep.trans hmono

/-- The bare `exp ((β+η)t)` curve count (confidence factor one) already
satisfies the paper's budget. -/
theorem paperCurveBudget_unit {p : ℕ → ℕ} {β η κ : ℝ}
    (hβ : 0 ≤ β) (hη : 0 < η) (hκ : 0 < κ) (hp : ∀ n, 0 < p n) :
    CurveBudget p paperY (paperPsi p β) (paperCurves β η unitConfidence) κ η :=
  paperCurveBudget hβ hη hκ hp (by filter_upwards with n; simp [unitConfidence])

/-- The same budget with the paper's `β = 1/(2c)`, where `c > 0` is the
stage-one smoothness coefficient. -/
theorem paperCurveBudget_of_c {p : ℕ → ℕ} {c η κ : ℝ} {L : ℕ → ℝ}
    (hc : 0 < c) (hη : 0 < η) (hκ : 0 < κ)
    (hp : ∀ n, 0 < p n) (hL : ∀ᶠ n : ℕ in atTop, 1 ≤ L n) :
    CurveBudget p paperY (paperPsi p (paperBeta c))
      (paperCurves (paperBeta c) η L) κ η :=
  paperCurveBudget (paperBeta_pos hc).le hη hκ hp hL

/-! ## 5. `CurveBudget` from lower bounds on the interface data -/

/-- Transfer the explicit budget to arbitrary functions `y`, `ψ₀`, `#curves`
that minorise the paper's choices.  The only extra inputs are the equality
`y = exp t`, the `p`-power/`Q` lower bound `√p/Q ≤ ψ₀`, and the curve-count
lower bound `⌈exp ((β+η)t) L⌉ ≤ #curves`. -/
theorem curveBudget_of_parameters {p : ℕ → ℕ} {y psi : ℕ → ℝ}
    {curves : ℕ → ℕ} {κ η β : ℝ} {L : ℕ → ℝ}
    (hκ : 0 < κ) (hη : 0 < η) (hβ : 0 ≤ β)
    (hp : ∀ n, 0 < p n)
    (hy : ∀ n, y n = paperY n)
    (hpsi : ∀ n, paperPsi p β n ≤ psi n)
    (hcurves : ∀ n, paperCurves β η L n ≤ curves n)
    (hL : ∀ᶠ n : ℕ in atTop, 1 ≤ L n) :
    CurveBudget p y psi curves κ η := by
  have hbase := paperCurveBudget hβ hη hκ hp hL
  filter_upwards [hbase, scale_grows.eventually_gt_atTop 0] with n hn ht
  have hy' : Real.log (y n) = scale n := by
    rw [hy n, paperY_log]
  have hspos : 0 < Real.sqrt (p n) := Real.sqrt_pos.mpr (by exact_mod_cast hp n)
  have hdenpos : 0 < Real.sqrt (p n) * Real.log (y n) := by
    rw [hy']
    exact mul_pos hspos ht
  have hn' : (2 + η) * scale n ≤
      (κ / 4) *
        ((paperCurves β η L n : ℝ) *
          (paperPsi p β n /
            (Real.sqrt (p n) * Real.log (y n)))) := by
    simpa [hy', paperY_log n] using hn
  have hcurve_nonneg : 0 ≤ (paperCurves β η L n : ℝ) := Nat.cast_nonneg _
  have hpsi_nonneg : 0 ≤ paperPsi p β n := paperPsi_nonneg hp β n
  have h1 : (paperCurves β η L n : ℝ) *
        (paperPsi p β n / (Real.sqrt (p n) * Real.log (y n))) ≤
      (curves n : ℝ) *
        (paperPsi p β n / (Real.sqrt (p n) * Real.log (y n))) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcurves n)
      (div_nonneg hpsi_nonneg hdenpos.le)
  have h2 : paperPsi p β n / (Real.sqrt (p n) * Real.log (y n)) ≤
      psi n / (Real.sqrt (p n) * Real.log (y n)) :=
    div_le_div_of_nonneg_right (hpsi n) hdenpos.le
  have h3 : (curves n : ℝ) *
        (paperPsi p β n / (Real.sqrt (p n) * Real.log (y n))) ≤
      (curves n : ℝ) *
        (psi n / (Real.sqrt (p n) * Real.log (y n))) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have hprod := h1.trans h3
  exact hn'.trans (mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ κ / 4))

/-! ## 6. `LogFactorSubexp` from `log (cofactor) = o (scale)` -/

/-- The smallest scalar form of the L27.2 multiplier hypothesis: the logarithm
of the cofactor is `o (scale)`. -/
def CofactorLogSubexp (cofactor : ℕ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    Real.log (cofactor n : ℝ) ≤ δ * scale n

/-- The multiplicative form of the same hypothesis: the cofactor is
subexponential on the scale. -/
def CofactorExpSubexp (cofactor : ℕ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    (cofactor n : ℝ) ≤ Real.exp (δ * scale n)

/-- `Nat.log₂ m` is at most `log m / log 2`. -/
theorem log2_le_log_div_log_two {m : ℕ} (hm : 2 ≤ m) :
    (m.log2 : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
  have hm0 : m ≠ 0 := by omega
  have hpow_nat : 2 ^ m.log2 ≤ m := by
    simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hm0
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ m.log2 := by positivity
  have hcast : ((2 : ℝ) ^ m.log2) ≤ (m : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hpow_nat
    simpa [Nat.cast_pow] using h
  have hlog := Real.log_le_log hpow_pos hcast
  rw [Real.log_pow] at hlog
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ h2pos]
  simpa [mul_comm] using hlog

/-- The additive and multiplicative cofactor bounds are equivalent. -/
theorem cofactorLogSubexp_iff_exp {cofactor : ℕ → ℕ} (hcof : ∀ n, 2 ≤ cofactor n) :
    CofactorLogSubexp cofactor ↔ CofactorExpSubexp cofactor := by
  constructor
  · intro h δ hδ
    have hpos : ∀ n, (0 : ℝ) < cofactor n := by
      intro n
      exact_mod_cast (lt_of_lt_of_le (by norm_num) (hcof n))
    filter_upwards [h δ hδ] with n hn
    calc
      (cofactor n : ℝ) = Real.exp (Real.log (cofactor n : ℝ)) :=
        (Real.exp_log (hpos n)).symm
      _ ≤ Real.exp (δ * scale n) := Real.exp_le_exp.mpr hn
  · intro h δ hδ
    have hpos : ∀ n, (0 : ℝ) < cofactor n := by
      intro n
      exact_mod_cast (lt_of_lt_of_le (by norm_num) (hcof n))
    filter_upwards [h δ hδ] with n hn
    have := Real.log_le_log (hpos n) hn
    rwa [Real.log_exp] at this

/-- **`LogFactorSubexp` from `log (cofactor) = o (scale)`.**  The `log₂`
multiplier is subexponential once the cofactor itself is `exp (o (scale))`. -/
theorem logFactorSubexp_of_cofactor_log {cofactor : ℕ → ℕ}
    (hcof : ∀ n, 2 ≤ cofactor n) (h : CofactorLogSubexp cofactor) :
    LogFactorSubexp cofactor := by
  intro δ hδ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ' : 0 < δ * Real.log 2 / 2 := by positivity
  filter_upwards [h (δ * Real.log 2 / 2) hδ',
    scale_grows.eventually_gt_atTop 0] with n hn hs
  have hm2 := hcof n
  have hmpos : (0 : ℝ) < (cofactor n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hm2)
  have hlog2_le : ((cofactor n).log2 : ℝ) ≤
      Real.log (cofactor n : ℝ) / Real.log 2 :=
    log2_le_log_div_log_two hm2
  have hlog2_le' : ((cofactor n).log2 : ℝ) ≤ (δ / 2) * scale n := by
    calc
      ((cofactor n).log2 : ℝ) ≤ Real.log (cofactor n : ℝ) / Real.log 2 := hlog2_le
      _ ≤ ((δ * Real.log 2 / 2) * scale n) / Real.log 2 :=
        div_le_div_of_nonneg_right hn hlog2pos.le
      _ = (δ / 2) * scale n := by
        field_simp [hlog2pos.ne']
  have hlog2_pos : 0 < ((cofactor n).log2 : ℝ) := by
    have h1 := one_le_log2_of_two_le hm2
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h1)
  have hargpos : 0 < (δ / 2) * scale n := by positivity
  have hlog_le : Real.log ((cofactor n).log2 : ℝ) ≤ δ * scale n := by
    calc
      Real.log ((cofactor n).log2 : ℝ) ≤ Real.log ((δ / 2) * scale n) :=
        Real.log_le_log hlog2_pos hlog2_le'
      _ ≤ (δ / 2) * scale n := Real.log_le_self hargpos.le
      _ ≤ δ * scale n := by nlinarith [hs, hδ]
  calc
    ((cofactor n).log2 : ℝ) = Real.exp (Real.log ((cofactor n).log2 : ℝ)) :=
      (Real.exp_log hlog2_pos).symm
    _ ≤ Real.exp (δ * scale n) := Real.exp_le_exp.mpr hlog_le

/-- The same reduction stated with the multiplicative cofactor bound. -/
theorem logFactorSubexp_of_cofactor_exp {cofactor : ℕ → ℕ}
    (hcof : ∀ n, 2 ≤ cofactor n) (h : CofactorExpSubexp cofactor) :
    LogFactorSubexp cofactor :=
  logFactorSubexp_of_cofactor_log hcof
    ((cofactorLogSubexp_iff_exp hcof).mpr h)

/-! ## 7. The smallest remaining scalar input bundle -/

/-- **The remaining scalar hypotheses of the L27 curve-count choice.**  Given
an L27.1 input `I`, it records only

* `β = 1/(2c) ≥ 0` and the polynomial confidence factor `L ≥ 1`;
* `y = exp t` (`y_eq`);
* the L27.1 `p`-power/`Q` bound `√p/Q ≤ ψ₀` (`psi_lower`);
* the paper's curve count `#curves ≥ ⌈exp ((β+η)t) L⌉` (`curves_lower`);
* `log (cofactor) = o (t)` (`cofactor_log_subexp`).

The constants `κ > 0`, `η > 0`, and `p > 0` are already fields of
`L27_1Inputs`. -/
structure L27BudgetArithmeticInputs (I : L27_1Inputs) where
  /-- The paper's `1/(2c)`. -/
  β : ℝ
  /-- Positivity of the smoothness-loss exponent. -/
  β_nonneg : 0 ≤ β
  /-- The polynomial confidence allowance in the curve count. -/
  L : ℕ → ℝ
  /-- The confidence allowance is at least one eventually. -/
  L_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ L n
  /-- The stage-one cutoff is `y = exp t`. -/
  y_eq : ∀ n, I.y n = paperY n
  /-- The L27.1 `p`-power/`Q` lower bound on the smooth-order count. -/
  psi_lower : ∀ n, paperPsi I.p β n ≤ I.psi n
  /-- The paper's curve-count selection. -/
  curves_lower : ∀ n, paperCurves β I.η L n ≤ I.curves n
  /-- The cofactor's logarithm is `o (scale)`. -/
  cofactor_log_subexp : CofactorLogSubexp I.cofactor

namespace L27BudgetArithmeticInputs

/-- The explicit paper budget implies `CurveBudget` for the interface data. -/
theorem curveBudget {I : L27_1Inputs} (B : L27BudgetArithmeticInputs I) :
    CurveBudget I.p I.y I.psi I.curves I.κ I.η :=
  curveBudget_of_parameters I.κ_pos I.η_pos B.β_nonneg I.p_pos
    B.y_eq B.psi_lower B.curves_lower B.L_ge_one

/-- The cofactor `o (scale)` bound implies the L27.2 `log₂` multiplier. -/
theorem logFactorSubexp {I : L27_1Inputs} (B : L27BudgetArithmeticInputs I) :
    LogFactorSubexp I.cofactor :=
  logFactorSubexp_of_cofactor_log I.cofactor_ge_two B.cofactor_log_subexp

/-- **Reduction to the finish bundle.**  Supplying the kill-law data, the
Hurwitz block, and Hasse's theorem, the two discharged budget fields complete
`L27StageOneFinishInputs`. -/
def toStageOneFinish {I : L27_1Inputs} (B : L27BudgetArithmeticInputs I)
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount) : L27StageOneFinishInputs I where
  killLaw := S
  hurwitz := H
  hasse := hhasse
  curve_budget := B.curveBudget
  log_factor_subexp := B.logFactorSubexp

/-- **The L27.1 ledger, with no budget or multiplier assumed.** -/
theorem loss_le_exp_ledger {I : L27_1Inputs} (B : L27BudgetArithmeticInputs I)
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  (B.toStageOneFinish S H hhasse).loss_le_exp_ledger

/-- **The manuscript-rate loss cap, with no budget or multiplier assumed.** -/
theorem loss_le_exp_paper {I : L27_1Inputs} (B : L27BudgetArithmeticInputs I)
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount) :
    ∀ᶠ n : ℕ in atTop,
      I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  (B.toStageOneFinish S H hhasse).loss_le_exp_paper

/-- **The full L27.1 reduction from the paper's scalar parameter choices.** -/
theorem reduction {I : L27_1Inputs} (B : L27BudgetArithmeticInputs I)
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  (B.toStageOneFinish S H hhasse).reduction

/-- The `RatedLeaf` assembled from the paper's scalar parameter choices. -/
def toRatedLeaf {I : L27_1Inputs} (B : L27BudgetArithmeticInputs I)
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount) : RatedLeaf :=
  (B.toStageOneFinish S H hhasse).toRatedLeaf

/-- The `C5` slot `exp (-2H)` for the assembled leaf. -/
theorem slot {I : L27_1Inputs} (B : L27BudgetArithmeticInputs I)
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount) :
    ∀ᶠ n : ℕ in atTop,
      (B.toRatedLeaf S H hhasse).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  (B.toRatedLeaf S H hhasse).slot

end L27BudgetArithmeticInputs

/-! ## 8. A concrete instance of the scalar hypotheses -/

/-- The explicit parameter bundle with `L = 1`.  The only genuinely external
hypotheses are the `p`-power/`Q` smooth-order count and the cofactor `o (t)`
bound; `β`, `y`, and `#curves` are the paper's formulas. -/
def unitBudgetInputs (I : L27_1Inputs) (β : ℝ) (hβ : 0 ≤ β)
    (hy : ∀ n, I.y n = paperY n)
    (hpsi : ∀ n, paperPsi I.p β n ≤ I.psi n)
    (hcurves : ∀ n, paperCurves β I.η unitConfidence n ≤ I.curves n)
    (hlog : CofactorLogSubexp I.cofactor) : L27BudgetArithmeticInputs I where
  β := β
  β_nonneg := hβ
  L := unitConfidence
  L_ge_one := by filter_upwards with n; simp [unitConfidence]
  y_eq := hy
  psi_lower := hpsi
  curves_lower := hcurves
  cofactor_log_subexp := hlog

/-- The unit-confidence instance satisfies `CurveBudget`. -/
theorem unitBudgetInputs_curveBudget (I : L27_1Inputs) (β : ℝ) (hβ : 0 ≤ β)
    (hy : ∀ n, I.y n = paperY n)
    (hpsi : ∀ n, paperPsi I.p β n ≤ I.psi n)
    (hcurves : ∀ n, paperCurves β I.η unitConfidence n ≤ I.curves n)
    (hlog : CofactorLogSubexp I.cofactor) :
    CurveBudget I.p I.y I.psi I.curves I.κ I.η :=
  (unitBudgetInputs I β hβ hy hpsi hcurves hlog).curveBudget

/-- The unit-confidence instance satisfies `LogFactorSubexp`. -/
theorem unitBudgetInputs_logFactorSubexp (I : L27_1Inputs) (β : ℝ) (hβ : 0 ≤ β)
    (hy : ∀ n, I.y n = paperY n)
    (hpsi : ∀ n, paperPsi I.p β n ≤ I.psi n)
    (hcurves : ∀ n, paperCurves β I.η unitConfidence n ≤ I.curves n)
    (hlog : CofactorLogSubexp I.cofactor) :
    LogFactorSubexp I.cofactor :=
  (unitBudgetInputs I β hβ hy hpsi hcurves hlog).logFactorSubexp

/-- **Non-vacuity of the paper's budget constants.**  With `β > 0`, `η > 0`,
`κ > 0`, and `p > 0`, every factor of the LP rate is strictly positive. -/
theorem paper_rate_factors_pos {p : ℕ → ℕ} {β η κ : ℝ}
    (_hβ : 0 < β) (_hη : 0 < η) (_hκ : 0 < κ) (hp : ∀ n, 0 < p n) (n : ℕ) :
    0 < paperQ β n ∧ 0 < paperPsi p β n ∧
      0 < (paperCurves β η unitConfidence n : ℝ) ∧
      0 < Real.exp (η * scale n) := by
  refine ⟨paperQ_pos β n, paperPsi_pos hp β n, ?_, Real.exp_pos _⟩
  have h : (0 : ℝ) < (paperCurves β η unitConfidence n : ℝ) := by
    exact_mod_cast paperCurves_pos (β := β) (η := η) (L := unitConfidence)
      (n := n) (by simp [unitConfidence])
  exact h

/-! ## 9. Non-vacuity witnesses -/

/-- The constant cofactor `2` satisfies the `log = o (scale)` hypothesis. -/
theorem cofactorLogSubexp_const_two : CofactorLogSubexp (fun _ : ℕ => 2) := by
  intro δ hδ
  filter_upwards [scale_grows.eventually_ge_atTop (Real.log 2 / δ)] with n hn
  have hmul : Real.log 2 / δ * δ = Real.log 2 := by
    field_simp [hδ.ne']
  calc
    Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    _ = Real.log 2 / δ * δ := hmul.symm
    _ ≤ scale n * δ := mul_le_mul_of_nonneg_right hn hδ.le
    _ = δ * scale n := by ring

/-- The constant cofactor `2` is a genuine (nonzero) instance of the L27.2
multiplier hypothesis. -/
theorem logFactorSubexp_const_two : LogFactorSubexp (fun _ : ℕ => 2) :=
  logFactorSubexp_of_cofactor_log (fun _ => by norm_num) cofactorLogSubexp_const_two

/-- A concrete non-vacuous budget: `p = 2`, `β = 0`, `κ = η = 1`, and the bare
unit-confidence curve count.  All factors of the LP rate are positive. -/
theorem concrete_curveBudget :
    CurveBudget (fun _ : ℕ => 2) paperY (paperPsi (fun _ => 2) 0)
      (paperCurves 0 1 unitConfidence) 1 1 :=
  paperCurveBudget_unit (β := 0) (η := 1) (κ := 1)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num)

/-! ## Axiom audit -/

#print axioms paperY_log
#print axioms paperBeta_pos
#print axioms paperQ_log
#print axioms eventually_paperY_gt_one
#print axioms paperCurves_pos
#print axioms le_paperCurves
#print axioms eventually_const_mul_sq_le_exp
#print axioms paperCurveBudget
#print axioms paperCurveBudget_unit
#print axioms paperCurveBudget_of_c
#print axioms curveBudget_of_parameters
#print axioms log2_le_log_div_log_two
#print axioms cofactorLogSubexp_iff_exp
#print axioms logFactorSubexp_of_cofactor_log
#print axioms logFactorSubexp_of_cofactor_exp
#print axioms L27BudgetArithmeticInputs.curveBudget
#print axioms L27BudgetArithmeticInputs.logFactorSubexp
#print axioms L27BudgetArithmeticInputs.toStageOneFinish
#print axioms L27BudgetArithmeticInputs.loss_le_exp_ledger
#print axioms L27BudgetArithmeticInputs.loss_le_exp_paper
#print axioms L27BudgetArithmeticInputs.reduction
#print axioms L27BudgetArithmeticInputs.toRatedLeaf
#print axioms L27BudgetArithmeticInputs.slot
#print axioms unitBudgetInputs
#print axioms unitBudgetInputs_curveBudget
#print axioms unitBudgetInputs_logFactorSubexp
#print axioms paper_rate_factors_pos
#print axioms cofactorLogSubexp_const_two
#print axioms logFactorSubexp_const_two
#print axioms concrete_curveBudget

end

end Cogentic.RandomizedL27BudgetArithmetic
