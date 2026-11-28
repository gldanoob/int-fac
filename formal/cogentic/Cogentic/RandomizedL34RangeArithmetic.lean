import Cogentic.RandomizedL34Range
import Cogentic.RandomizedOneThirdAsymptotic

/-!
# L34: the `T⁶` range input from the paper's raw parameter choice

`Cogentic.RandomizedL34Range` reduced the paper's Chebotarev range condition to
the pointwise `T⁶` budget

`K d (log |Δ_E|)² ≤ (log 2) T⁶`

and showed that the two parameter bounds `d ≤ T`, `log |Δ_E| ≤ T` plus the scalar
comparison `K ≤ (log 2) T³` imply it.  That file still took `d ≤ T`,
`log |Δ_E| ≤ T` and `K ≤ (log 2) T³` as the packaged
`ChebotarevT6RangeInput`.

This file derives that packaged input from the *raw* arithmetic data of the
Wave-18/29 record:

* the paper's polynomial parameter choice
  `T n = exp (C * (log |Δ_E| n)²)`,
* the absolute-degree / discriminant relation `d n ≤ log |Δ_E| n`
  (the paper's `2d ≤ log |Δ_E|`),
* the size condition `log |Δ_E| n ≥ e` (i.e. `1 ≤ log log |Δ_E| n`),
* the range constant bound `K ≤ 1` (the paper's `K = O(1)`),
* the Wave-18 constant margin `Ch log 2 < csel cbr / 4`, and
* the Wave-18 scale-cubic growth
  `2 scale n ≤ (csel cbr / 4 - Ch log 2) T n³`.

## What is derived and what is genuinely independent

The two parameter bounds are *not* independent once `T = exp(C (log |Δ|)²)`:

* `log log |Δ| ≥ 1` gives `(log |Δ|)² ≥ log |Δ|`, so
  `T ≥ |Δ| ≥ log |Δ|` (`discLog_le_T`);
* `d ≤ log |Δ|` then gives `d ≤ T` (`degree_le_T`);
* `(log |Δ|)² ≥ 1` gives `T ≥ e > 2`, hence `K ≤ 1` gives
  `K ≤ (log 2) T³` (`constant_le`).

The genuinely independent arithmetic inequalities are therefore exactly

`0 < d n`, `d n ≤ log |Δ_E| n`, and `1 ≤ log log |Δ_E| n`

(the last is `exp 1 ≤ log |Δ_E| n`).  In particular `degree_pos` cannot be
recovered from the Wave-18 `l34DegreeOneReduction` / `l34Selection` fields:
those are stated with a division by `degree n`, and Lean's convention
`x / 0 = 0` makes both inequalities automatic at `degree n = 0`.  This file
carries those two fields unchanged for compatibility, but keeps `0 < degree n`
as the smallest explicit positivity input.

## The scale-cubic field

`l34ScaleCubic` is not needed for the *pointwise* input (the exponent choice
already gives `T ≥ 2` at every index).  It is used for the two genuine
consequences recorded here:

* `l34T_tendsto` — `T → ∞`, because the slope
  `csel cbr / 4 - Ch log 2` is positive by the constant margin;
* `eventually_rangeT6` — an *eventual* form of the range budget obtained from
  `l34ScaleCubic` and the two parameter bounds, replacing the pointwise scalar
  comparison `K ≤ (log 2) T³` by the scale-cubic-derived eventual one.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no loss, count,
error or mass is set to zero.
-/

namespace Cogentic.RandomizedL34RangeArithmetic

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The paper's parameter choice `T = exp (C (log |Δ|)²)` -/

/-- **The paper's polynomial parameter.**  `paperRangeT C D n` is
`exp (C * (log (D n))²)`, the exact choice used for `log |Δ_E| = D n`. -/
def paperRangeT (C : ℝ) (D : ℕ → ℝ) : ℕ → ℝ :=
  fun n => Real.exp (C * (Real.log (D n)) ^ 2)

/-- The defining equation of `paperRangeT`. -/
theorem paperRangeT_def (C : ℝ) (D : ℕ → ℝ) (n : ℕ) :
    paperRangeT C D n = Real.exp (C * (Real.log (D n)) ^ 2) := rfl

/-- `paperRangeT` is positive. -/
theorem paperRangeT_pos (C : ℝ) (D : ℕ → ℝ) (n : ℕ) :
    0 < paperRangeT C D n := Real.exp_pos _

/-- The logarithm of the paper's parameter is `C (log |Δ|)²`. -/
theorem log_paperRangeT (C : ℝ) (D : ℕ → ℝ) (n : ℕ) :
    Real.log (paperRangeT C D n) = C * (Real.log (D n)) ^ 2 :=
  Real.log_exp _

/-- **`T ≥ 2` from the exponent size.**  If `1 ≤ C` and `1 ≤ log D`, then
`C (log D)² ≥ 1`, so `T = exp (C (log D)²) ≥ exp 1 > 2`. -/
theorem paperRangeT_ge_two {C : ℝ} {D : ℕ → ℝ} (hC : 1 ≤ C)
    {n : ℕ} (hL : 1 ≤ Real.log (D n)) :
    2 ≤ paperRangeT C D n := by
  have hL0 : 0 ≤ Real.log (D n) := le_trans zero_le_one hL
  have hL2 : 1 ≤ (Real.log (D n)) ^ 2 := by nlinarith
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hCL2 : 1 ≤ C * (Real.log (D n)) ^ 2 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * (Real.log (D n)) ^ 2 :=
          mul_le_mul hC hL2 (by norm_num) hC0
  exact le_of_lt
    (lt_of_lt_of_le Real.exp_one_gt_two (Real.exp_le_exp.mpr hCL2))

/-- **The discriminant logarithm is bounded by `T`.**  For `1 ≤ C` and
`1 ≤ log D`, one has `C (log D)² ≥ log D`, so
`D = exp (log D) ≤ exp (C (log D)²) = T`. -/
theorem discLog_le_paperRangeT {C : ℝ} {D : ℕ → ℝ} (hC : 1 ≤ C)
    {n : ℕ} (hD : 0 < D n) (hL : 1 ≤ Real.log (D n)) :
    D n ≤ paperRangeT C D n := by
  have hL0 : 0 ≤ Real.log (D n) := le_trans zero_le_one hL
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hCL : 1 ≤ C * Real.log (D n) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * Real.log (D n) :=
          mul_le_mul hC hL (by norm_num) hC0
  have hsq : Real.log (D n) ≤ C * (Real.log (D n)) ^ 2 := by
    calc
      Real.log (D n) = 1 * Real.log (D n) := by ring
      _ ≤ (C * Real.log (D n)) * Real.log (D n) :=
          mul_le_mul_of_nonneg_right hCL hL0
      _ = C * (Real.log (D n)) ^ 2 := by ring
  calc
    D n = Real.exp (Real.log (D n)) := (Real.exp_log hD).symm
    _ ≤ Real.exp (C * (Real.log (D n)) ^ 2) := Real.exp_le_exp.mpr hsq
    _ = paperRangeT C D n := rfl

/-- **`log |Δ| ≤ T`.**  The elementary bound `log D ≤ D` and the previous
estimate give `log D ≤ T`. -/
theorem log_discLog_le_paperRangeT {C : ℝ} {D : ℕ → ℝ} (hC : 1 ≤ C)
    {n : ℕ} (hD : 0 < D n) (hL : 1 ≤ Real.log (D n)) :
    Real.log (D n) ≤ paperRangeT C D n :=
  (Real.log_le_self hD.le).trans (discLog_le_paperRangeT hC hD hL)

/-- **The packaged `T⁶` range input from the paper's parameter choice.**  The
only genuinely arithmetic inputs are `0 < K ≤ 1`, `0 < d`, `d ≤ log |Δ|`, and
`exp 1 ≤ log |Δ|`. -/
theorem paperRangeInput {K C : ℝ} {degree D : ℕ → ℝ}
    (hK0 : 0 < K) (hK1 : K ≤ 1) (hC : 1 ≤ C)
    (hdeg : ∀ n, 0 < degree n)
    (hD : ∀ n, 0 < D n)
    (hdegD : ∀ n, degree n ≤ D n)
    (hL : ∀ n, 1 ≤ Real.log (D n)) :
    ChebotarevT6RangeInput K (paperRangeT C D) degree D where
  K_pos := hK0
  degree_pos := hdeg
  discLog_pos := hD
  degree_le_T := fun n =>
    (hdegD n).trans (discLog_le_paperRangeT hC (hD n) (hL n))
  discLog_le_T := fun n =>
    discLog_le_paperRangeT hC (hD n) (hL n)
  constant_le := fun n =>
    constant_le_of_le_one_of_two_le hK1 (paperRangeT_ge_two hC (hL n))

/-- **The `C = 1` paper case `T = exp ((log |Δ|)²)`.**  The size condition is
just `exp 1 ≤ log |Δ|`. -/
theorem paperRangeInput_exp_sq {K : ℝ} {degree D : ℕ → ℝ}
    (hK0 : 0 < K) (hK1 : K ≤ 1)
    (hdeg : ∀ n, 0 < degree n)
    (hD : ∀ n, 0 < D n)
    (hdegD : ∀ n, degree n ≤ D n)
    (hDe : ∀ n, Real.exp 1 ≤ D n) :
    ChebotarevT6RangeInput K (paperRangeT 1 D) degree D :=
  paperRangeInput hK0 hK1 le_rfl hdeg hD hdegD
    (fun n => (Real.le_log_iff_exp_le (hD n)).mpr (hDe n))

/-- **The paper's `T⁶` range budget from the parameter choice.**  This is the
literal inequality `K d (log |Δ|)² ≤ (log 2) T⁶`. -/
theorem paperRangeT6 {K C : ℝ} {degree D : ℕ → ℝ}
    (hK0 : 0 < K) (hK1 : K ≤ 1) (hC : 1 ≤ C)
    (hdeg : ∀ n, 0 < degree n)
    (hD : ∀ n, 0 < D n)
    (hdegD : ∀ n, degree n ≤ D n)
    (hL : ∀ n, 1 ≤ Real.log (D n)) (n : ℕ) :
    K * degree n * (D n) ^ 2 ≤ Real.log 2 * (paperRangeT C D n) ^ 6 :=
  (paperRangeInput hK0 hK1 hC hdeg hD hdegD hL).toChebotarevRangeT6 n

/-! ## 2. The scale-cubic consequence `T → ∞` -/

/-- **A cubic lower bound on `T` forces `T → ∞`.**  This is the standalone form
of `PaperResidualInputsL34.l34T_tendsto`: if `0 < c` and eventually
`2 scale n ≤ c (T n)³`, then `T n → ∞`. -/
theorem tendsto_atTop_of_scaleCubic {c : ℝ} {T : ℕ → ℝ}
    (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, 2 * scale n ≤ c * T n ^ 3) :
    Tendsto T atTop atTop := by
  have hscale : Tendsto (fun n : ℕ => 2 * scale n) atTop atTop :=
    scale_grows.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hcubic_mul : Tendsto (fun n : ℕ => c * T n ^ 3) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hscale.eventually_ge_atTop b, h] with n hb hT
    linarith
  have hcubic : Tendsto (fun n : ℕ => T n ^ 3) atTop atTop :=
    hcubic_mul.atTop_of_const_mul₀ hc
  rw [tendsto_atTop] at hcubic ⊢
  intro b
  filter_upwards [hcubic ((max b 0) ^ 3)] with n hn
  have hmax0 : 0 ≤ max b 0 := le_max_right b 0
  have hT0 : 0 ≤ T n := by
    by_contra hneg
    have hneg' : T n < 0 := not_le.mp hneg
    have hsq : 0 < T n ^ 2 := sq_pos_of_ne_zero (ne_of_lt hneg')
    have hneg3 : T n ^ 3 < 0 := by
      calc
        T n ^ 3 = T n * T n ^ 2 := by ring
        _ < 0 := mul_neg_of_neg_of_pos hneg' hsq
    have hmax3 : 0 ≤ (max b 0) ^ 3 := pow_nonneg hmax0 3
    linarith
  by_cases hb : 0 ≤ b
  · have hb3 : b ^ 3 ≤ T n ^ 3 := by
      calc
        b ^ 3 ≤ (max b 0) ^ 3 := pow_le_pow_left₀ hb (le_max_left b 0) 3
        _ ≤ T n ^ 3 := hn
    exact (pow_le_pow_iff_left₀ hb hT0 (by norm_num : (3 : ℕ) ≠ 0)).mp hb3
  · have hb' : b < 0 := not_le.mp hb
    linarith

/-- **The scale-cubic estimate makes `T³ ≥ 1 / log 2` eventually.**  Since
`scale → ∞`, eventually `scale ≥ c / (2 log 2)`; the cubic bound then gives
`T³ ≥ 1 / log 2`. -/
theorem eventually_one_le_log_two_mul_cube_of_scaleCubic {c : ℝ} {T : ℕ → ℝ}
    (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, 2 * scale n ≤ c * T n ^ 3) :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log 2 * T n ^ 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  filter_upwards [scale_grows.eventually_ge_atTop (c / (2 * Real.log 2)), h]
    with n hs hT
  have htwo : 2 * (c / (2 * Real.log 2)) = c / Real.log 2 := by
    field_simp [hlog2ne]
  have h1 : c / Real.log 2 ≤ 2 * scale n := by
    rw [← htwo]
    exact mul_le_mul_of_nonneg_left hs (by norm_num)
  have h2 : c / Real.log 2 ≤ c * T n ^ 3 := h1.trans hT
  have h3 : (1 : ℝ) / Real.log 2 ≤ T n ^ 3 := by
    have h2' : c * (1 / Real.log 2) ≤ c * T n ^ 3 := by
      simpa [div_eq_mul_inv] using h2
    exact (mul_le_mul_iff_of_pos_left hc).mp h2'
  calc
    (1 : ℝ) = Real.log 2 * (1 / Real.log 2) := by
      field_simp [hlog2ne]
    _ ≤ Real.log 2 * T n ^ 3 :=
        mul_le_mul_of_nonneg_left h3 hlog2.le

/-! ## 3. The raw Wave-18/29 parameter growth record -/

/-- **The raw range data of the Wave-18/29 record.**

The arithmetic content is the paper's parameter choice (`l34T_eq`), the degree
/ discriminant relation (`l34Degree_le_discLog`), the size condition
`exp 1 ≤ log |Δ|`, and `0 < K ≤ 1`.  The Wave-18 constant margin and scale-cubic
growth are carried verbatim; the latter yields `T → ∞` and the eventual range
budget.  The degree-one reduction and the per-ideal selection are carried for
compatibility with the Wave-18/29 bundle, but they do not imply `d > 0`: both
are inequalities through a division by `d`, which Lean evaluates as `0` at
`d = 0`.  Hence `l34Degree_pos` is kept as the smallest explicit positivity
input. -/
structure L34RawRangeInput where
  /-- The range constant. -/
  l34K : ℝ
  /-- The exponent constant in `T = exp (C (log |Δ|)²)`. -/
  l34C : ℝ
  /-- The per-ideal selection constant. -/
  l34csel : ℝ
  /-- The bracket constant. -/
  l34cbr : ℝ
  /-- The cubic class-count constant. -/
  l34Ch : ℝ
  /-- The polynomial input parameter `T`. -/
  l34T : ℕ → ℝ
  /-- The absolute degree `2d` of `E = K(√γ)`. -/
  l34Degree : ℕ → ℝ
  /-- `log |Δ_E|`. -/
  l34DiscLog : ℕ → ℝ
  /-- A cumulative inert count (carried from the Wave-18/29 record). -/
  l34InertCount : ℕ → ℝ
  /-- The degree-one inert count (carried from the Wave-18/29 record). -/
  l34DegreeOneInert : ℕ → ℝ
  /-- The per-trial detection probability (carried). -/
  l34PTrial : ℕ → ℝ
  /-- The cutoff `x` used by the degree-one reduction and selection (carried). -/
  l34X : ℕ → ℝ
  /-- The range constant is positive. -/
  l34K_pos : 0 < l34K
  /-- The paper's range constant is at most one. -/
  l34K_le_one : l34K ≤ 1
  /-- The paper's exponent constant is at least one. -/
  l34C_ge_one : 1 ≤ l34C
  /-- **Genuinely independent positivity of the absolute degree.** -/
  l34Degree_pos : ∀ n, 0 < l34Degree n
  /-- `log |Δ_E|` is positive. -/
  l34DiscLog_pos : ∀ n, 0 < l34DiscLog n
  /-- **The degree / discriminant relation** `d ≤ log |Δ_E|`. -/
  l34Degree_le_discLog : ∀ n, l34Degree n ≤ l34DiscLog n
  /-- **The size condition** `log |Δ_E| ≥ e`, i.e. `1 ≤ log log |Δ_E|`. -/
  l34DiscLog_ge_exp_one : ∀ n, Real.exp 1 ≤ l34DiscLog n
  /-- **The paper's parameter choice** `T = exp (C (log |Δ_E|)²)`. -/
  l34T_eq : ∀ n, l34T n = paperRangeT l34C l34DiscLog n
  /-- The degree-one reduction, carried verbatim. -/
  l34DegreeOneReduction :
    DegreeOneInertReduction l34InertCount l34DegreeOneInert l34Degree l34X
  /-- The per-ideal selection, carried verbatim. -/
  l34Selection : ProbeSelectionLowerBound l34csel l34X l34Degree l34DegreeOneInert
    l34PTrial
  /-- **The Wave-18 constant margin** `Ch log 2 < csel cbr / 4`. -/
  l34ConstantMargin : l34Ch * Real.log 2 < l34csel * l34cbr / 4
  /-- **The Wave-18 scale-cubic growth** of `T`. -/
  l34ScaleCubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (l34csel * l34cbr / 4 - l34Ch * Real.log 2) * l34T n ^ 3

namespace L34RawRangeInput

variable (R : L34RawRangeInput)

/-- `1 ≤ log log |Δ_E|`, from the size condition `exp 1 ≤ log |Δ_E|`. -/
theorem logDiscLog_ge_one (n : ℕ) : 1 ≤ Real.log (R.l34DiscLog n) :=
  (Real.le_log_iff_exp_le (R.l34DiscLog_pos n)).mpr (R.l34DiscLog_ge_exp_one n)

/-- The raw `T` is literally the paper's exponential choice. -/
theorem T_eq_paperRangeT : R.l34T = paperRangeT R.l34C R.l34DiscLog :=
  funext R.l34T_eq

/-- **The packaged `ChebotarevT6RangeInput`.**  This is `degree_pos`,
`degree_le_T` and `K d (log |Δ|)² ≤ (log 2) T⁶` all at once. -/
theorem toChebotarevT6RangeInput :
    ChebotarevT6RangeInput R.l34K R.l34T R.l34Degree R.l34DiscLog := by
  rw [R.T_eq_paperRangeT]
  exact paperRangeInput R.l34K_pos R.l34K_le_one R.l34C_ge_one
    R.l34Degree_pos R.l34DiscLog_pos R.l34Degree_le_discLog
    R.logDiscLog_ge_one

/-- **`degree_pos`, derived.** -/
theorem degree_pos (n : ℕ) : 0 < R.l34Degree n :=
  R.toChebotarevT6RangeInput.degree_pos n

/-- **`degree_le_T`, derived.** -/
theorem degree_le_T (n : ℕ) : R.l34Degree n ≤ R.l34T n :=
  R.toChebotarevT6RangeInput.degree_le_T n

/-- **`log |Δ_E| ≤ T`, derived.** -/
theorem discLog_le_T (n : ℕ) : R.l34DiscLog n ≤ R.l34T n :=
  R.toChebotarevT6RangeInput.discLog_le_T n

/-- **The `T⁶` range budget**, pointwise. -/
theorem rangeT6 (n : ℕ) :
    R.l34K * R.l34Degree n * (R.l34DiscLog n) ^ 2 ≤
      Real.log 2 * (R.l34T n) ^ 6 :=
  R.toChebotarevT6RangeInput.toChebotarevRangeT6 n

/-- **The slope of the scale-cubic bound is positive.** -/
theorem slope_pos : 0 < R.l34csel * R.l34cbr / 4 - R.l34Ch * Real.log 2 :=
  sub_pos.mpr R.l34ConstantMargin

/-- **`T → ∞`, from the scale-cubic field and the constant margin.** -/
theorem l34T_tendsto : Tendsto R.l34T atTop atTop :=
  tendsto_atTop_of_scaleCubic R.slope_pos R.l34ScaleCubic

/-- **The eventual comparison `1 ≤ (log 2) T³`, from the scale-cubic field.** -/
theorem eventually_one_le_log_two_mul_cube :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log 2 * R.l34T n ^ 3 :=
  eventually_one_le_log_two_mul_cube_of_scaleCubic R.slope_pos R.l34ScaleCubic

/-- **The eventual `T⁶` range budget from the raw growth fields.**  The scale
cubic gives `(log 2) T³ ≥ 1` eventually; with the pointwise bounds `d ≤ T` and
`log |Δ| ≤ T`, and `K ≤ 1`, this closes `K d (log |Δ|)² ≤ (log 2) T⁶` on a
tail.  This route replaces the pointwise scalar comparison `constant_le` of
`ChebotarevT6RangeInput` by the scale-cubic-derived eventual comparison; the two
parameter bounds are still those transported from `toChebotarevT6RangeInput`. -/
theorem eventually_rangeT6 :
    ∀ᶠ n : ℕ in atTop,
      R.l34K * R.l34Degree n * (R.l34DiscLog n) ^ 2 ≤
        Real.log 2 * (R.l34T n) ^ 6 := by
  filter_upwards [R.eventually_one_le_log_two_mul_cube] with n hconst
  have hT0 : 0 ≤ R.l34T n :=
    (R.degree_pos n).le.trans (R.degree_le_T n)
  have hD0 : 0 ≤ R.l34DiscLog n := (R.l34DiscLog_pos n).le
  have hsq : (R.l34DiscLog n) ^ 2 ≤ (R.l34T n) ^ 2 :=
    pow_le_pow_left₀ hD0 (R.discLog_le_T n) 2
  have hprod : R.l34Degree n * (R.l34DiscLog n) ^ 2 ≤ (R.l34T n) ^ 3 := by
    calc
      R.l34Degree n * (R.l34DiscLog n) ^ 2 ≤ R.l34T n * (R.l34T n) ^ 2 :=
        mul_le_mul (R.degree_le_T n) hsq (sq_nonneg _) hT0
      _ = (R.l34T n) ^ 3 := by ring
  have hmul : R.l34K * (R.l34Degree n * (R.l34DiscLog n) ^ 2) ≤
      R.l34K * (R.l34T n) ^ 3 :=
    mul_le_mul_of_nonneg_left hprod R.l34K_pos.le
  have hKcube : R.l34K * (R.l34T n) ^ 3 ≤ 1 * (R.l34T n) ^ 3 :=
    mul_le_mul_of_nonneg_right R.l34K_le_one (pow_nonneg hT0 3)
  calc
    R.l34K * R.l34Degree n * (R.l34DiscLog n) ^ 2
        = R.l34K * (R.l34Degree n * (R.l34DiscLog n) ^ 2) := by ring
    _ ≤ R.l34K * (R.l34T n) ^ 3 := hmul
    _ ≤ 1 * (R.l34T n) ^ 3 := hKcube
    _ = (R.l34T n) ^ 3 := by ring
    _ ≤ (Real.log 2 * R.l34T n ^ 3) * (R.l34T n) ^ 3 := by
        calc
          (R.l34T n) ^ 3 = 1 * (R.l34T n) ^ 3 := by ring
          _ ≤ (Real.log 2 * R.l34T n ^ 3) * (R.l34T n) ^ 3 :=
              mul_le_mul_of_nonneg_right hconst (pow_nonneg hT0 3)
    _ = Real.log 2 * (R.l34T n) ^ 6 := by ring

end L34RawRangeInput

/-! ## Axiom audit -/

#print axioms paperRangeT_pos
#print axioms log_paperRangeT
#print axioms paperRangeT_ge_two
#print axioms discLog_le_paperRangeT
#print axioms log_discLog_le_paperRangeT
#print axioms paperRangeInput
#print axioms paperRangeInput_exp_sq
#print axioms paperRangeT6
#print axioms tendsto_atTop_of_scaleCubic
#print axioms eventually_one_le_log_two_mul_cube_of_scaleCubic
#print axioms L34RawRangeInput.logDiscLog_ge_one
#print axioms L34RawRangeInput.T_eq_paperRangeT
#print axioms L34RawRangeInput.toChebotarevT6RangeInput
#print axioms L34RawRangeInput.degree_pos
#print axioms L34RawRangeInput.degree_le_T
#print axioms L34RawRangeInput.discLog_le_T
#print axioms L34RawRangeInput.rangeT6
#print axioms L34RawRangeInput.slope_pos
#print axioms L34RawRangeInput.l34T_tendsto
#print axioms L34RawRangeInput.eventually_one_le_log_two_mul_cube
#print axioms L34RawRangeInput.eventually_rangeT6

end

end Cogentic.RandomizedL34RangeArithmetic
