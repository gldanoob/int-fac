import Cogentic.RandomizedL34EffectiveChebotarev

/-!
# L34: the factorial growth budgets at the paper's parameters

`Cogentic.RandomizedL34EffectiveChebotarev` isolated the two remaining
*arithmetic* inputs of the L34 ledger as the logarithmic budgets

* `ChebotarevErrorLogBudget C cZ cbr F T degree`:
  `log (C F T⁶ / (cbr/8)) ≤ cZ sqrt (T⁶ log 2/(2d))`;
* `DegreeLossLogBudget cbr degree F T`:
  `log (d F T⁶ / (cbr/8)) ≤ (T⁶/2) log 2`.

The effective Chebotarev theorem says nothing about the factorial factor `F`;
the earlier file exhibited an unbounded `F = exp 1000` for which both budgets
fail.  The present file proves that, at the paper's parameter identities

* `F n = (2 * degree n)!` (`absoluteFactorialFactor`),
* `cbr = 1/16` (the Stark bracket constant of
  `Cogentic.RandomizedL34LogIntegral`),
* `cZ > 0` arbitrary (in particular the paper's effective-Chebotarev constant),
* `T n → ∞`, and `degree n ≤ T n` (supplied by the explicit `T⁶` range input
  `ChebotarevT6RangeInput`, whose range inequality is exactly
  `degree * discLog² ≤ T⁶ log 2`),

the two budgets hold eventually, with explicit thresholds.

## The Stirling-type estimate

The only estimate on the factorial is the elementary Stirling upper bound

`log (k!) ≤ k log k` (`log_factorial_le`),

proved from `Nat.factorial_le_pow` (`k! ≤ k^k`).  For `k = 2d` this gives

`log ((2d)!) ≤ 2d log (2d) ≤ 2T log (2T)`.

## Absorbing `log F`

The range input supplies `d ≤ T`, so `log F = O(T log T)`.  The error budget
only needs `O(T log T) ≪ T^{5/2}`, because `d ≤ T` gives
`sqrt (T⁶ log 2/(2d)) ≥ sqrt (T⁵ log 2/2) = T² sqrt T sqrt (log 2/2)`.
The discarded-ideal budget compares `O(T log T)` with `(T⁶/2) log 2`, which is
even easier.  In both cases `T n → ∞` makes the inequality true on a tail; the
thresholds are the explicit constants `errorLogBudgetThreshold` and
`degreeLossLogBudgetThreshold` below.

## Contents

* `log_factorial_le` and `log_absoluteFactorialFactor_le` — the factorial bound;
* `log_absoluteFactorialFactor_le_of_degree_le` — the bound in terms of `T`;
* `errorLogBudgetThreshold`, `chebotarevErrorLogBudget_of_threshold`,
  `chebotarevErrorLogBudget_eventually`,
  `exists_threshold_chebotarevErrorLogBudget` — the error budget;
* `degreeLossLogBudgetThreshold`, `degreeLossLogBudget_of_threshold`,
  `degreeLossLogBudget_eventually`,
  `exists_threshold_degreeLossLogBudget` — the discarded-ideal budget;
* the specialisations to `cbr = 1/16`, to the paper's `T⁶` range input, and to
  `F = absoluteFactorialFactor degree`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No count, mass,
error or loss is set to zero.
-/

namespace Cogentic.RandomizedL34FactorialBudgets

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34EffectiveChebotarev

noncomputable section

/-! ## 1. The Stirling-type factorial bound -/

/-- **Elementary Stirling upper bound.**  For `k ≥ 1`, `log (k!) ≤ k log k`.
This is the only estimate on the factorial used by the budgets; it follows from
`Nat.factorial_le_pow` (`k! ≤ k^k`) and the monotonicity of `log`. -/
theorem log_factorial_le {k : ℕ} (hk : 0 < k) :
    Real.log (k.factorial : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := by
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    have h := Nat.factorial_le_pow k
    exact_mod_cast h
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hfacpos : (0 : ℝ) < (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  calc
    Real.log (k.factorial : ℝ) ≤ Real.log ((k : ℝ) ^ k) :=
      Real.log_le_log hfacpos hfac
    _ = (k : ℝ) * Real.log (k : ℝ) := Real.log_pow (k : ℝ) k

/-- **The factorial budget for `(2d)!`.**  `log ((2d)!) ≤ 2d log (2d)` for a
positive degree `d`. -/
theorem log_absoluteFactorialFactor_le {degree : ℕ → ℕ} {n : ℕ}
    (hdeg : 0 < degree n) :
    Real.log (absoluteFactorialFactor degree n) ≤
      (2 * (degree n : ℝ)) * Real.log (2 * (degree n : ℝ)) := by
  unfold absoluteFactorialFactor
  have hk : 0 < 2 * degree n := by omega
  have hfac := log_factorial_le (k := 2 * degree n) hk
  push_cast at hfac ⊢
  simpa [mul_comm] using hfac

/-- **The factorial bound in terms of `T`.**  If `0 < d ≤ T`, then
`log ((2d)!) ≤ 2T log (2T)`. -/
theorem log_absoluteFactorialFactor_le_of_degree_le
    {degree : ℕ → ℕ} {T : ℕ → ℝ} {n : ℕ}
    (hdeg : 0 < degree n) (hdegT : (degree n : ℝ) ≤ T n) :
    Real.log (absoluteFactorialFactor degree n) ≤ 2 * T n * Real.log (2 * T n) := by
  have h1 := log_absoluteFactorialFactor_le (degree := degree) hdeg
  have hdpos : (0 : ℝ) < (degree n : ℝ) := by exact_mod_cast hdeg
  have h2dpos : (0 : ℝ) < 2 * (degree n : ℝ) := by positivity
  have hTpos : (0 : ℝ) < T n := lt_of_lt_of_le (by linarith) hdegT
  have h2Tpos : (0 : ℝ) < 2 * T n := by positivity
  have hle : 2 * (degree n : ℝ) ≤ 2 * T n := by linarith
  have hlogmono : Real.log (2 * (degree n : ℝ)) ≤ Real.log (2 * T n) :=
    Real.log_le_log h2dpos hle
  have hlog_nonneg : 0 ≤ Real.log (2 * (degree n : ℝ)) := by
    have hd1 : (1 : ℝ) ≤ (degree n : ℝ) := by exact_mod_cast hdeg
    exact Real.log_nonneg (by linarith)
  have hmul : (2 * (degree n : ℝ)) * Real.log (2 * (degree n : ℝ)) ≤
      (2 * T n) * Real.log (2 * T n) :=
    mul_le_mul hle hlogmono hlog_nonneg h2Tpos.le
  calc
    Real.log (absoluteFactorialFactor degree n)
        ≤ (2 * (degree n : ℝ)) * Real.log (2 * (degree n : ℝ)) := h1
    _ ≤ (2 * T n) * Real.log (2 * T n) := hmul

/-! ## 2. Elementary bounds on the logarithmic factors -/

/-- For `T ≥ 2`, `log (2T) ≤ 2T`. -/
theorem log_two_mul_le {T : ℝ} (hT : 2 ≤ T) : Real.log (2 * T) ≤ 2 * T := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hlog : Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne']
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlogT : Real.log T ≤ T := Real.log_le_self hTpos.le
  calc
    Real.log (2 * T) = Real.log 2 + Real.log T := hlog
    _ ≤ 1 + T := add_le_add hlog2 hlogT
    _ ≤ 2 * T := by linarith

/-- **`log F` is absorbed by `T⁶`.**  Under `d ≤ T` and `T n → ∞`, the
factorial logarithm is eventually at most `T⁶`.  This is the precise sense in
which the Stirling factor is negligible against the `T⁶` polynomial in the
budgets. -/
theorem eventually_log_absoluteFactorialFactor_le_T6
    {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hTend : Tendsto T atTop atTop) :
    ∀ᶠ n : ℕ in atTop, Real.log (absoluteFactorialFactor degree n) ≤ (T n) ^ 6 := by
  filter_upwards [hTend.eventually_ge_atTop (2 : ℝ)] with n hn
  have hbase := log_absoluteFactorialFactor_le_of_degree_le (hdeg n) (hdegT n)
  have hlog2T : Real.log (2 * T n) ≤ 2 * T n := log_two_mul_le hn
  have hstep : 2 * T n * Real.log (2 * T n) ≤ 4 * (T n) ^ 2 := by
    calc
      2 * T n * Real.log (2 * T n) ≤ 2 * T n * (2 * T n) :=
        mul_le_mul_of_nonneg_left hlog2T (by positivity)
      _ = 4 * (T n) ^ 2 := by ring
  have hT4 : (4 : ℝ) ≤ (T n) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn 4
    norm_num at h ⊢
    linarith
  have hpoly : 4 * (T n) ^ 2 ≤ (T n) ^ 6 := by
    have hmul : 4 * (T n) ^ 2 ≤ (T n) ^ 4 * (T n) ^ 2 :=
      mul_le_mul_of_nonneg_right hT4 (sq_nonneg _)
    have hEq : (T n) ^ 4 * (T n) ^ 2 = (T n) ^ 6 := by ring
    linarith
  exact hbase.trans (hstep.trans hpoly)

/-! ## 3. The logarithmic error budget -/

/-- The additive constant in the error budget, before the `T²` absorption. -/
noncomputable def errorLogBudgetConstant (C cbr : ℝ) : ℝ :=
  |Real.log C| + |Real.log (cbr / 8)| + 10

/-- **The explicit threshold for the error budget.**  Once `T` exceeds this
constant, `M T² ≤ cZ T² sqrt T sqrt (log 2/2) ≤ cZ sqrt (T⁶ log 2/(2d))`. -/
noncomputable def errorLogBudgetThreshold (C cZ cbr : ℝ) : ℝ :=
  max 2 ((errorLogBudgetConstant C cbr / (cZ * Real.sqrt (Real.log 2 / 2))) ^ 2)

/-- Splitting the logarithm of the error-budget argument, and replacing
`log F` by the Stirling bound. -/
theorem log_error_argument_le {C cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ} {n : ℕ}
    (hC : 0 < C) (hcbr : 0 < cbr) (hT : 2 ≤ T n)
    (hdeg : 0 < degree n) (hdegT : (degree n : ℝ) ≤ T n) :
    Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / (cbr / 8)) ≤
      Real.log C + 2 * T n * Real.log (2 * T n) + 6 * Real.log (T n) -
        Real.log (cbr / 8) := by
  have hTpos : (0 : ℝ) < T n := by linarith
  have hFpos : (0 : ℝ) < absoluteFactorialFactor degree n :=
    absoluteFactorialFactor_pos degree n
  have hT6pos : (0 : ℝ) < T n ^ 6 := pow_pos hTpos 6
  have hc8 : (0 : ℝ) < cbr / 8 := by positivity
  have hprod : (0 : ℝ) < C * (absoluteFactorialFactor degree n * T n ^ 6) := by
    positivity
  have hFT : (0 : ℝ) < absoluteFactorialFactor degree n * T n ^ 6 := by
    positivity
  have hsplit :
      Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / (cbr / 8)) =
        Real.log C + Real.log (absoluteFactorialFactor degree n) +
          Real.log (T n ^ 6) - Real.log (cbr / 8) := by
    rw [Real.log_div hprod.ne' hc8.ne',
      Real.log_mul hC.ne' hFT.ne',
      Real.log_mul hFpos.ne' hT6pos.ne']
    ring
  rw [hsplit, Real.log_pow]
  have hFbound := log_absoluteFactorialFactor_le_of_degree_le hdeg hdegT
  linarith

/-- **The error budget at an index where `T` exceeds the threshold.** -/
theorem chebotarevErrorLogBudget_pointwise
    {C cZ cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ} {n : ℕ}
    (hC : 0 < C) (hcZ : 0 < cZ) (hcbr : 0 < cbr)
    (hdeg : 0 < degree n) (hdegT : (degree n : ℝ) ≤ T n)
    (hT : errorLogBudgetThreshold C cZ cbr ≤ T n) :
    Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / (cbr / 8)) ≤
      cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ))) := by
  have hT2 : 2 ≤ T n := le_trans (le_max_left _ _) hT
  have hTpos : (0 : ℝ) < T n := by linarith
  have hdpos : (0 : ℝ) < (degree n : ℝ) := by exact_mod_cast hdeg
  have hLpos : (0 : ℝ) < Real.log 2 / 2 := by positivity
  -- Step 1: split the logarithm and use the factorial bound.
  have hbase := log_error_argument_le hC hcbr hT2 hdeg hdegT
  -- Step 2: absorb the logarithmic terms by `M * T²`.
  have hMT : Real.log C + 2 * T n * Real.log (2 * T n) + 6 * Real.log (T n) -
      Real.log (cbr / 8) ≤ errorLogBudgetConstant C cbr * (T n) ^ 2 := by
    have hlogT : Real.log (T n) ≤ T n := Real.log_le_self hTpos.le
    have hlog2T : Real.log (2 * T n) ≤ 2 * T n := log_two_mul_le hT2
    have hprod_le : 2 * T n * Real.log (2 * T n) ≤ 4 * (T n) ^ 2 := by
      calc
        2 * T n * Real.log (2 * T n) ≤ 2 * T n * (2 * T n) :=
          mul_le_mul_of_nonneg_left hlog2T (by positivity)
        _ = 4 * (T n) ^ 2 := by ring
    have hsix_le : 6 * Real.log (T n) ≤ 6 * (T n) ^ 2 := by
      have hTle : T n ≤ (T n) ^ 2 := by nlinarith
      nlinarith
    have hlogC : Real.log C ≤ |Real.log C| := le_abs_self _
    have hlogc : -Real.log (cbr / 8) ≤ |Real.log (cbr / 8)| := neg_le_abs _
    have hT2ge1 : (1 : ℝ) ≤ (T n) ^ 2 := by nlinarith
    have habsC : |Real.log C| ≤ |Real.log C| * (T n) ^ 2 := by
      nlinarith [abs_nonneg (Real.log C)]
    have habsc : |Real.log (cbr / 8)| ≤ |Real.log (cbr / 8)| * (T n) ^ 2 := by
      nlinarith [abs_nonneg (Real.log (cbr / 8))]
    unfold errorLogBudgetConstant
    nlinarith
  -- Step 3: the coefficient comparison `M ≤ cZ sqrt (log 2/2) sqrt T`.
  set A : ℝ := errorLogBudgetConstant C cbr / (cZ * Real.sqrt (Real.log 2 / 2))
    with hAdef
  have hcoefpos : (0 : ℝ) < cZ * Real.sqrt (Real.log 2 / 2) := by positivity
  have hMpos : (0 : ℝ) < errorLogBudgetConstant C cbr := by
    unfold errorLogBudgetConstant
    have := abs_nonneg (Real.log C)
    have := abs_nonneg (Real.log (cbr / 8))
    linarith
  have hAnonneg : 0 ≤ A := le_of_lt (div_pos hMpos hcoefpos)
  have hA2 : A ^ 2 ≤ T n := le_trans (le_max_right _ _) hT
  have hsqrtA : A ≤ Real.sqrt (T n) := by
    have h := Real.sqrt_le_sqrt hA2
    rwa [Real.sqrt_sq hAnonneg] at h
  have hAeq : A * (cZ * Real.sqrt (Real.log 2 / 2)) = errorLogBudgetConstant C cbr := by
    rw [hAdef]
    field_simp
  have hM_le : errorLogBudgetConstant C cbr ≤
      cZ * Real.sqrt (Real.log 2 / 2) * Real.sqrt (T n) := by
    calc
      errorLogBudgetConstant C cbr = A * (cZ * Real.sqrt (Real.log 2 / 2)) := hAeq.symm
      _ ≤ Real.sqrt (T n) * (cZ * Real.sqrt (Real.log 2 / 2)) :=
        mul_le_mul_of_nonneg_right hsqrtA hcoefpos.le
      _ = cZ * Real.sqrt (Real.log 2 / 2) * Real.sqrt (T n) := by ring
  have hMT2 : errorLogBudgetConstant C cbr * (T n) ^ 2 ≤
      (cZ * Real.sqrt (Real.log 2 / 2) * Real.sqrt (T n)) * (T n) ^ 2 :=
    mul_le_mul_of_nonneg_right hM_le (sq_nonneg _)
  -- Step 4: `T² sqrt T sqrt (log 2/2) ≤ sqrt (T⁶ log 2/(2d))`.
  have hinner : (T n) ^ 2 * Real.sqrt (T n) * Real.sqrt (Real.log 2 / 2) ≤
      Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ))) := by
    apply Real.le_sqrt_of_sq_le
    have hmain : (T n) ^ 5 * (Real.log 2 / 2) ≤
        (T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ)) := by
      have hnum : 0 ≤ (T n) ^ 6 * Real.log 2 := by positivity
      have h2dpos : 0 < 2 * (degree n : ℝ) := by positivity
      have hle : 2 * (degree n : ℝ) ≤ 2 * T n := by linarith
      have h := div_le_div_of_nonneg_left hnum h2dpos hle
      rwa [show (T n) ^ 6 * Real.log 2 / (2 * T n) =
        (T n) ^ 5 * (Real.log 2 / 2) by field_simp] at h
    have hsq : ((T n) ^ 2 * Real.sqrt (T n) * Real.sqrt (Real.log 2 / 2)) ^ 2 =
        (T n) ^ 5 * (Real.log 2 / 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hTpos.le, Real.sq_sqrt hLpos.le]
      ring
    rw [hsq]
    exact hmain
  have hstep : (cZ * Real.sqrt (Real.log 2 / 2) * Real.sqrt (T n)) * (T n) ^ 2 =
      cZ * ((T n) ^ 2 * Real.sqrt (T n) * Real.sqrt (Real.log 2 / 2)) := by
    ring
  calc
    Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / (cbr / 8))
        ≤ Real.log C + 2 * T n * Real.log (2 * T n) + 6 * Real.log (T n) -
            Real.log (cbr / 8) := hbase
    _ ≤ errorLogBudgetConstant C cbr * (T n) ^ 2 := hMT
    _ ≤ (cZ * Real.sqrt (Real.log 2 / 2) * Real.sqrt (T n)) * (T n) ^ 2 := hMT2
    _ = cZ * ((T n) ^ 2 * Real.sqrt (T n) * Real.sqrt (Real.log 2 / 2)) := hstep
    _ ≤ cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ))) :=
      mul_le_mul_of_nonneg_left hinner hcZ.le

/-- **The error budget from a uniform threshold.**  If `T` dominates the explicit
threshold `errorLogBudgetThreshold C cZ cbr` at every index, and `d ≤ T`, then
`ChebotarevErrorLogBudget` holds for `F = (2d)!` and `cbr` arbitrary positive. -/
theorem chebotarevErrorLogBudget_of_threshold
    {C cZ cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hC : 0 < C) (hcZ : 0 < cZ) (hcbr : 0 < cbr)
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hT : ∀ n, errorLogBudgetThreshold C cZ cbr ≤ T n) :
    ChebotarevErrorLogBudget C cZ cbr (absoluteFactorialFactor degree) T
      (fun n => (degree n : ℝ)) := by
  intro n
  exact chebotarevErrorLogBudget_pointwise hC hcZ hcbr (hdeg n) (hdegT n) (hT n)

/-- **The error budget holds eventually.**  With `T n → ∞`, `d ≤ T`, and
`F = (2d)!`, the logarithmic error budget holds on a tail. -/
theorem chebotarevErrorLogBudget_eventually
    {C cZ cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hC : 0 < C) (hcZ : 0 < cZ) (hcbr : 0 < cbr)
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hTend : Tendsto T atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / (cbr / 8)) ≤
        cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ))) := by
  filter_upwards [hTend.eventually_ge_atTop (errorLogBudgetThreshold C cZ cbr)]
    with n hn
  exact chebotarevErrorLogBudget_pointwise hC hcZ hcbr (hdeg n) (hdegT n) hn

/-- **The error budget with an explicit index threshold.** -/
theorem exists_threshold_chebotarevErrorLogBudget
    {C cZ cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hC : 0 < C) (hcZ : 0 < cZ) (hcbr : 0 < cbr)
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hTend : Tendsto T atTop atTop) :
    ∃ N : ℕ, ∀ n ≥ N,
      Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / (cbr / 8)) ≤
        cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ))) :=
  Filter.eventually_atTop.mp
    (chebotarevErrorLogBudget_eventually hC hcZ hcbr hdeg hdegT hTend)

/-! ## 4. The discarded-ideal budget -/

/-- The additive constant in the discarded-ideal budget. -/
noncomputable def degreeLossLogBudgetConstant (cbr : ℝ) : ℝ :=
  |Real.log (cbr / 8)| + 11

/-- **The explicit threshold for the discarded-ideal budget.** -/
noncomputable def degreeLossLogBudgetThreshold (cbr : ℝ) : ℝ :=
  max 2 (degreeLossLogBudgetConstant cbr / (Real.log 2 / 2))

/-- Splitting the logarithm of the discarded-ideal argument, and replacing
`log d` and `log F` by their upper bounds. -/
theorem log_degreeLoss_argument_le {cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ} {n : ℕ}
    (hcbr : 0 < cbr) (hT : 2 ≤ T n)
    (hdeg : 0 < degree n) (hdegT : (degree n : ℝ) ≤ T n) :
    Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
        (cbr / 8)) ≤
      Real.log (T n) + 2 * T n * Real.log (2 * T n) + 6 * Real.log (T n) -
        Real.log (cbr / 8) := by
  have hTpos : (0 : ℝ) < T n := by linarith
  have hdpos : (0 : ℝ) < (degree n : ℝ) := by exact_mod_cast hdeg
  have hFpos : (0 : ℝ) < absoluteFactorialFactor degree n :=
    absoluteFactorialFactor_pos degree n
  have hT6pos : (0 : ℝ) < T n ^ 6 := pow_pos hTpos 6
  have hc8 : (0 : ℝ) < cbr / 8 := by positivity
  have hprod : (0 : ℝ) < (degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 := by
    positivity
  have hdF : (0 : ℝ) < (degree n : ℝ) * absoluteFactorialFactor degree n := by
    positivity
  have hsplit :
      Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
          (cbr / 8)) =
        Real.log (degree n : ℝ) + Real.log (absoluteFactorialFactor degree n) +
          Real.log (T n ^ 6) - Real.log (cbr / 8) := by
    rw [Real.log_div hprod.ne' hc8.ne',
      Real.log_mul hdF.ne' hT6pos.ne',
      Real.log_mul hdpos.ne' hFpos.ne']
  rw [hsplit, Real.log_pow]
  have hlogd : Real.log (degree n : ℝ) ≤ Real.log (T n) :=
    Real.log_le_log hdpos hdegT
  have hFbound := log_absoluteFactorialFactor_le_of_degree_le hdeg hdegT
  linarith

/-- **The discarded-ideal budget at an index where `T` exceeds the threshold.** -/
theorem degreeLossLogBudget_pointwise
    {cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ} {n : ℕ}
    (hcbr : 0 < cbr) (hdeg : 0 < degree n) (hdegT : (degree n : ℝ) ≤ T n)
    (hT : degreeLossLogBudgetThreshold cbr ≤ T n) :
    Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
        (cbr / 8)) ≤ (T n) ^ 6 / 2 * Real.log 2 := by
  have hT2 : 2 ≤ T n := le_trans (le_max_left _ _) hT
  have hTpos : (0 : ℝ) < T n := by linarith
  have hbase := log_degreeLoss_argument_le hcbr hT2 hdeg hdegT
  have hMT : Real.log (T n) + 2 * T n * Real.log (2 * T n) +
      6 * Real.log (T n) - Real.log (cbr / 8) ≤
      degreeLossLogBudgetConstant cbr * (T n) ^ 2 := by
    have hlogT : Real.log (T n) ≤ T n := Real.log_le_self hTpos.le
    have hlog2T : Real.log (2 * T n) ≤ 2 * T n := log_two_mul_le hT2
    have hprod_le : 2 * T n * Real.log (2 * T n) ≤ 4 * (T n) ^ 2 := by
      calc
        2 * T n * Real.log (2 * T n) ≤ 2 * T n * (2 * T n) :=
          mul_le_mul_of_nonneg_left hlog2T (by positivity)
        _ = 4 * (T n) ^ 2 := by ring
    have hsix_le : 6 * Real.log (T n) ≤ 6 * (T n) ^ 2 := by
      have hTle : T n ≤ (T n) ^ 2 := by nlinarith
      nlinarith
    have hTle_sq : T n ≤ (T n) ^ 2 := by nlinarith
    have hlogc : -Real.log (cbr / 8) ≤ |Real.log (cbr / 8)| := neg_le_abs _
    have hT2ge1 : (1 : ℝ) ≤ (T n) ^ 2 := by nlinarith
    have habsc : |Real.log (cbr / 8)| ≤ |Real.log (cbr / 8)| * (T n) ^ 2 := by
      nlinarith [abs_nonneg (Real.log (cbr / 8))]
    unfold degreeLossLogBudgetConstant
    nlinarith
  have hcoefpos : (0 : ℝ) < Real.log 2 / 2 := by positivity
  have hMnonneg : 0 ≤ degreeLossLogBudgetConstant cbr := by
    unfold degreeLossLogBudgetConstant
    have := abs_nonneg (Real.log (cbr / 8))
    linarith
  have hTbig : degreeLossLogBudgetConstant cbr / (Real.log 2 / 2) ≤ T n :=
    le_trans (le_max_right _ _) hT
  have hM_le : degreeLossLogBudgetConstant cbr ≤ (Real.log 2 / 2) * (T n) ^ 4 := by
    have h1 : degreeLossLogBudgetConstant cbr ≤ (Real.log 2 / 2) * T n := by
      rw [div_le_iff₀ hcoefpos] at hTbig
      linarith
    have hT1 : (1 : ℝ) ≤ T n := by linarith
    have hTle4 : T n ≤ (T n) ^ 4 := by
      simpa using pow_le_pow_right₀ hT1 (show 1 ≤ 4 by norm_num)
    calc
      degreeLossLogBudgetConstant cbr ≤ (Real.log 2 / 2) * T n := h1
      _ ≤ (Real.log 2 / 2) * (T n) ^ 4 :=
        mul_le_mul_of_nonneg_left hTle4 hcoefpos.le
  have hfinal : degreeLossLogBudgetConstant cbr * (T n) ^ 2 ≤
      (T n) ^ 6 / 2 * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hM_le (sq_nonneg (T n))
    calc
      degreeLossLogBudgetConstant cbr * (T n) ^ 2
          ≤ ((Real.log 2 / 2) * (T n) ^ 4) * (T n) ^ 2 := hmul
      _ = (T n) ^ 6 / 2 * Real.log 2 := by ring
  calc
    Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
        (cbr / 8))
        ≤ Real.log (T n) + 2 * T n * Real.log (2 * T n) + 6 * Real.log (T n) -
            Real.log (cbr / 8) := hbase
    _ ≤ degreeLossLogBudgetConstant cbr * (T n) ^ 2 := hMT
    _ ≤ (T n) ^ 6 / 2 * Real.log 2 := hfinal

/-- **The discarded-ideal budget from a uniform threshold.** -/
theorem degreeLossLogBudget_of_threshold
    {cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hcbr : 0 < cbr)
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hT : ∀ n, degreeLossLogBudgetThreshold cbr ≤ T n) :
    DegreeLossLogBudget cbr (fun n => (degree n : ℝ))
      (absoluteFactorialFactor degree) T := by
  intro n
  exact degreeLossLogBudget_pointwise hcbr (hdeg n) (hdegT n) (hT n)

/-- **The discarded-ideal budget holds eventually.** -/
theorem degreeLossLogBudget_eventually
    {cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hcbr : 0 < cbr)
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hTend : Tendsto T atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
        (cbr / 8)) ≤ (T n) ^ 6 / 2 * Real.log 2 := by
  filter_upwards [hTend.eventually_ge_atTop (degreeLossLogBudgetThreshold cbr)]
    with n hn
  exact degreeLossLogBudget_pointwise hcbr (hdeg n) (hdegT n) hn

/-- **The discarded-ideal budget with an explicit index threshold.** -/
theorem exists_threshold_degreeLossLogBudget
    {cbr : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hcbr : 0 < cbr)
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hTend : Tendsto T atTop atTop) :
    ∃ N : ℕ, ∀ n ≥ N,
      Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
        (cbr / 8)) ≤ (T n) ^ 6 / 2 * Real.log 2 :=
  Filter.eventually_atTop.mp
    (degreeLossLogBudget_eventually hcbr hdeg hdegT hTend)

/-! ## 5. The paper's constants and the `T⁶` range input -/

/-- **The error budget at the paper's bracket constant `cbr = 1/16`.** -/
theorem chebotarevErrorLogBudget_eventually_paper
    {C cZ : ℝ} {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hTend : Tendsto T atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / ((1 / 16) / 8)) ≤
        cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ))) :=
  chebotarevErrorLogBudget_eventually hC hcZ (by norm_num) hdeg hdegT hTend

/-- **The discarded-ideal budget at `cbr = 1/16`.** -/
theorem degreeLossLogBudget_eventually_paper
    {degree : ℕ → ℕ} {T : ℕ → ℝ}
    (hdeg : ∀ n, 0 < degree n) (hdegT : ∀ n, (degree n : ℝ) ≤ T n)
    (hTend : Tendsto T atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
        ((1 / 16) / 8)) ≤ (T n) ^ 6 / 2 * Real.log 2 :=
  degreeLossLogBudget_eventually (by norm_num) hdeg hdegT hTend

/-- **The range inequality carried by the explicit `T⁶` range input.**  Taking
`degree` to be the paper's absolute degree `d`, the packaged input
`ChebotarevT6RangeInput` gives exactly
`K d (log |Δ_E|)² ≤ (log 2) T⁶`, the range condition used by the budgets. -/
theorem rangeInequality_of_rangeInput
    {K : ℝ} {degree : ℕ → ℕ} {T discLog : ℕ → ℝ}
    (range : ChebotarevT6RangeInput K T (fun n => (degree n : ℝ)) discLog) :
    ∀ n, K * (degree n : ℝ) * (discLog n) ^ 2 ≤ Real.log 2 * (T n) ^ 6 :=
  range.toChebotarevRangeT6

/-- **The error budget for the paper's parameters and range input.**  The
packaged range input supplies both `d ≤ T` and the range inequality
`K d (log |Δ_E|)² ≤ (log 2) T⁶`; combined with `T n → ∞` it gives the
logarithmic error budget eventually for `F = (2d)!` and `cbr = 1/16`. -/
theorem chebotarevErrorLogBudget_eventually_of_rangeInput
    {K C cZ : ℝ} {degree : ℕ → ℕ} {T discLog : ℕ → ℝ}
    (range : ChebotarevT6RangeInput K T (fun n => (degree n : ℝ)) discLog)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hTend : Tendsto T atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / ((1 / 16) / 8)) ≤
        cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ))) := by
  have hdeg : ∀ n, 0 < degree n := by
    intro n
    have h := range.degree_pos n
    exact_mod_cast h
  exact chebotarevErrorLogBudget_eventually_paper hC hcZ hdeg range.degree_le_T hTend

/-- **The discarded-ideal budget for the paper's parameters and range input.** -/
theorem degreeLossLogBudget_eventually_of_rangeInput
    {K : ℝ} {degree : ℕ → ℕ} {T discLog : ℕ → ℝ}
    (range : ChebotarevT6RangeInput K T (fun n => (degree n : ℝ)) discLog)
    (hTend : Tendsto T atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
        ((1 / 16) / 8)) ≤ (T n) ^ 6 / 2 * Real.log 2 := by
  have hdeg : ∀ n, 0 < degree n := by
    intro n
    have h := range.degree_pos n
    exact_mod_cast h
  exact degreeLossLogBudget_eventually_paper hdeg range.degree_le_T hTend

/-- **Both budgets for the paper's parameters, with explicit index thresholds.**
This is the combined statement: for `F = (2d)!`, `cbr = 1/16`, arbitrary
positive `C`, `cZ`, and a range input supplying `d ≤ T`, there is `N` such that
both logarithmic budgets hold for all `n ≥ N`. -/
theorem exists_threshold_budgets_of_rangeInput
    {K C cZ : ℝ} {degree : ℕ → ℕ} {T discLog : ℕ → ℝ}
    (range : ChebotarevT6RangeInput K T (fun n => (degree n : ℝ)) discLog)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hTend : Tendsto T atTop atTop) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Real.log (C * (absoluteFactorialFactor degree n * T n ^ 6) / ((1 / 16) / 8)) ≤
        cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * (degree n : ℝ)))) ∧
      (Real.log ((degree n : ℝ) * absoluteFactorialFactor degree n * T n ^ 6 /
        ((1 / 16) / 8)) ≤ (T n) ^ 6 / 2 * Real.log 2) := by
  have hdeg : ∀ n, 0 < degree n := by
    intro n
    have h := range.degree_pos n
    exact_mod_cast h
  obtain ⟨N₁, hN₁⟩ := exists_threshold_chebotarevErrorLogBudget hC hcZ
    (by norm_num : (0 : ℝ) < (1 / 16)) hdeg range.degree_le_T hTend
  obtain ⟨N₂, hN₂⟩ := exists_threshold_degreeLossLogBudget
    (by norm_num : (0 : ℝ) < (1 / 16)) hdeg range.degree_le_T hTend
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  exact ⟨hN₁ n (le_trans (le_max_left _ _) hn),
    hN₂ n (le_trans (le_max_right _ _) hn)⟩

/-! ## Axiom audit -/

#print axioms log_factorial_le
#print axioms log_absoluteFactorialFactor_le
#print axioms log_absoluteFactorialFactor_le_of_degree_le
#print axioms log_two_mul_le
#print axioms eventually_log_absoluteFactorialFactor_le_T6
#print axioms log_error_argument_le
#print axioms chebotarevErrorLogBudget_pointwise
#print axioms chebotarevErrorLogBudget_of_threshold
#print axioms chebotarevErrorLogBudget_eventually
#print axioms exists_threshold_chebotarevErrorLogBudget
#print axioms log_degreeLoss_argument_le
#print axioms degreeLossLogBudget_pointwise
#print axioms degreeLossLogBudget_of_threshold
#print axioms degreeLossLogBudget_eventually
#print axioms exists_threshold_degreeLossLogBudget
#print axioms chebotarevErrorLogBudget_eventually_paper
#print axioms degreeLossLogBudget_eventually_paper
#print axioms rangeInequality_of_rangeInput
#print axioms chebotarevErrorLogBudget_eventually_of_rangeInput
#print axioms degreeLossLogBudget_eventually_of_rangeInput
#print axioms exists_threshold_budgets_of_rangeInput

end

end Cogentic.RandomizedL34FactorialBudgets
