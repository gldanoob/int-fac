import Cogentic.RandomizedL34LogIntegral

/-!
# L34: the standard effective Chebotarev statement and the residual reductions

`Cogentic.RandomizedL34ChebotarevSides` isolated the Chebotarev content of the
L34 ledger as three explicit `Prop`s:

* `ChebotarevResidualInput C cZ x degree count liX liBeta0` — the cumulative
  count is within the canonical Lagarias–Odlyzko envelope
  `C x exp (-c sqrt (log x/(2d)))` of the main term
  `½ (Li x - Li x^{β₀})`;
* `ChebotarevErrorScalarBound C cZ cbr F T degree` — the error is negligible
  against the bracket after cancelling the positive factor `x = 2^{T⁶}`;
* `DegreeLossScalarBound cbr degree F T` — the discarded small / higher-degree
  ideals are negligible after cancelling `F T⁶`.

The present file fixes the *standard* effective Chebotarev theorem of
Lagarias–Odlyzko / Oesterlé as the smallest explicit `Prop`
`EffectiveChebotarevStatement`, and reduces the residual input to it:

`EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0`
extends `ChebotarevResidualInput` with the standard range condition
`x ≥ exp (K (log |Δ_E|)²)` and the positivity `0 < K`.  Thus

* `EffectiveChebotarevStatement.toResidualInput` is the reduction of
  `ChebotarevResidualInput` to the standard statement;
* `effectiveChebotarevRangeCondition_of_rangeInput` proves the statement's
  range condition is exactly what the paper's explicit `ChebotarevT6RangeInput`
  (with the arithmetic fact `1 ≤ degree`) already supplies, so the range is not
  an extra analytic hypothesis;
* `effectiveChebotarevStatement_iff_residual_of_rangeInput` makes the reduction
  lossless at the paper's cutoff: the standard statement is inter-derivable
  with `ChebotarevResidualInput` once the paper's range is fixed;
* `EffectiveChebotarevStatement.toRangeInput` converts the statement's range to
  the paper's `ChebotarevRangeInput` once `K' * degree ≤ K`.

## The two vanishing conditions

The error-negligibility and discarded-ideal steps are *not* consequences of the
standard effective Chebotarev theorem alone: they are arithmetic statements
about the growth of the factorial factor `F = (2d)!` and the polynomial
parameter `T`.  They are isolated here as the exact logarithmic budgets

* `ChebotarevErrorLogBudget C cZ cbr F T degree`:
  `log (C F T⁶ / (cbr/8)) ≤ cZ sqrt (T⁶ log 2/(2d))`;
* `DegreeLossLogBudget cbr degree F T`:
  `log (d F T⁶ / (cbr/8)) ≤ (T⁶/2) log 2`.

`chebotarevErrorScalarBound_iff_logBudget` and
`degreeLossScalarBound_iff_logBudget` prove these are *exactly* the paper's
scalar bounds, and `chebotarevErrorNegligible_of_logBudget` /
`degreeOneLossNegligible_of_logBudget` compose them with the unconditional
cancellation lemmas of `Cogentic.RandomizedL34ChebotarevSides`.  These are the
precise inequalities that the effective Chebotarev theorem does not provide:
`errorLogBudget_not_implied_by_statement` and
`degreeLogBudget_not_implied_by_statement` exhibit the same standard statement
instance with an unconstrained factorial factor `F = exp 1000`, for which both
budgets fail.  The missing content is exactly an upper bound on the growth of
`F` against the exponential gain, not any counting estimate.

## The bundle

`L34EffectiveChebotarevInputs` is `L34ChebotarevSidesInputs` with the three
analytic fields replaced by

* `effective : EffectiveChebotarevStatement K C cZ (cutoff T) degree discLog
  count liX liBeta0`,
* `error_log : ChebotarevErrorLogBudget C cZ cbr F T degree`,
* `degree_log : DegreeLossLogBudget cbr degree F T`,

and `toL34ChebotarevSidesInputs` is the reduction chain.  Every counting,
Stark, zero-free, range and probe field is inherited verbatim.

## Nonvacuity

`effectiveChebotarevStatement_nonvacuous`, `chebotarevErrorScalarBound_nonvacuous`
and `degreeLossScalarBound_nonvacuous` give concrete witnesses with explicit
constants, so none of the isolated statements is vacuous.  The loss is still
the actual probe miss: no loss, count, error or mass is set to zero.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL34EffectiveChebotarev

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
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The standard range condition -/

/-- **The standard range condition of effective Chebotarev.**  The cutoff `x` is
at least the explicit threshold `exp (K (log |Δ_E|)²)`.  The constant `K` is the
range constant of the Lagarias–Odlyzko / Oesterlé theorem; it is allowed to
absorb the degree (for a fixed field `C = K d`), which is why the paper's
`K d (log |Δ_E|)²` condition is a strengthening of this one. -/
def EffectiveChebotarevRangeCondition (K : ℝ) (x discLog : ℕ → ℝ) : Prop :=
  ∀ n, Real.exp (K * (discLog n) ^ 2) ≤ x n

/-- The range condition is exactly the logarithmic range inequality, for
positive cutoffs. -/
theorem effectiveChebotarevRangeCondition_iff_log {K : ℝ}
    {x discLog : ℕ → ℝ} (hx : ∀ n, 0 < x n) :
    EffectiveChebotarevRangeCondition K x discLog ↔
      ∀ n, K * (discLog n) ^ 2 ≤ Real.log (x n) := by
  constructor
  · intro h n
    exact (Real.le_log_iff_exp_le (hx n)).mpr (h n)
  · intro h n
    exact (Real.le_log_iff_exp_le (hx n)).mp (h n)

/-- The range condition at the paper's cutoff, from the paper's explicit
`T⁶` range input.  The extra hypothesis `1 ≤ degree` is the arithmetic fact
`2d ≥ 2` for the absolute degree `2d` of the quadratic extension. -/
theorem effectiveChebotarevRangeCondition_of_rangeInput
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog)
    (hdeg1 : ∀ n, 1 ≤ degree n) :
    EffectiveChebotarevRangeCondition K (cutoff T) discLog := by
  intro n
  have h := A.toChebotarevRangeInput.range n
  have hK : 0 ≤ K := A.K_pos.le
  have hmul : K * (discLog n) ^ 2 ≤ K * degree n * (discLog n) ^ 2 := by
    have h1 : K * 1 ≤ K * degree n :=
      mul_le_mul_of_nonneg_left (hdeg1 n) hK
    have hsq : 0 ≤ (discLog n) ^ 2 := sq_nonneg _
    calc
      K * (discLog n) ^ 2 = (K * 1) * (discLog n) ^ 2 := by ring
      _ ≤ (K * degree n) * (discLog n) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 hsq
      _ = K * degree n * (discLog n) ^ 2 := by ring
  have hlog : K * (discLog n) ^ 2 ≤ Real.log (cutoff T n) := by
    have := hmul.trans h
    simpa [cutoff] using this
  exact (Real.le_log_iff_exp_le (cutoff_pos T n)).mp hlog

/-! ## 2. The standard effective Chebotarev statement -/

/-- **The standard effective Chebotarev theorem** (Lagarias–Odlyzko /
Oesterlé), in the smallest explicit form consumed by L34.

It extends the canonical residual input `ChebotarevResidualInput` with the
positivity `0 < K` of the range constant and the range condition
`x ≥ exp (K (log |Δ_E|)²)`.  The error constants `C, cZ` are the explicit
positive constants of the envelope
`C x exp (-cZ sqrt (log x/(2d)))`.

A single constant `C` serves both the range and the error because, given any
two positive constants `C_range, C_err` for which the theorem holds, it holds
with `C = min C_range C_err`: the range `C (log |Δ|)² ≤ log x` follows from the
smaller constant, and the error `C x exp(...)` is smaller. -/
structure EffectiveChebotarevStatement (K C cZ : ℝ) (x degree discLog : ℕ → ℝ)
    (count liX liBeta0 : ℕ → ℝ) : Prop extends
    ChebotarevResidualInput C cZ x degree count liX liBeta0 where
  /-- The range constant is positive. -/
  K_pos : 0 < K
  /-- The standard range condition `x ≥ exp (K (log |Δ_E|)²)`. -/
  range : EffectiveChebotarevRangeCondition K x discLog

namespace EffectiveChebotarevStatement

variable {K C cZ : ℝ} {x degree discLog count liX liBeta0 : ℕ → ℝ}

/-- **The residual input follows from the standard statement.**  This is the
reduction of `ChebotarevResidualInput` to the effective Chebotarev theorem: the
count envelope is inherited from the parent structure. -/
theorem toResidualInput
    (S : EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0) :
    ChebotarevResidualInput C cZ x degree count liX liBeta0 :=
  S.toChebotarevResidualInput

/-- The standard statement also gives the one-sided lower bound. -/
theorem toLowerInput
    (S : EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0) :
    ChebotarevLowerInput C cZ x degree count liX liBeta0 :=
  S.toChebotarevResidualInput.toLowerInput

/-- The standard statement gives the slack Chebotarev error. -/
theorem toSlack
    (S : EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0) :
    ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0) :=
  S.toChebotarevResidualInput.toSlack

/-- The range condition in logarithmic form. -/
theorem rangeLog
    (S : EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0) (n : ℕ) :
    K * (discLog n) ^ 2 ≤ Real.log (x n) := by
  have hx : 0 < x n := lt_of_lt_of_le (Real.exp_pos _) (S.range n)
  exact (Real.le_log_iff_exp_le hx).mpr (S.range n)

/-- **The standard range gives the paper's range input.**  If the paper's
constant `K'` satisfies `K' * degree ≤ K`, then the range condition of the
standard statement implies `ChebotarevRangeInput K' x degree discLog`. -/
theorem toRangeInput (S : EffectiveChebotarevStatement K C cZ x degree discLog
    count liX liBeta0) {K' : ℝ} (hK : 0 < K')
    (hmargin : ∀ n, K' * degree n ≤ K) :
    ChebotarevRangeInput K' x degree discLog where
  K_pos := hK
  range := by
    intro n
    have hmul : K' * degree n * (discLog n) ^ 2 ≤ K * (discLog n) ^ 2 :=
      mul_le_mul_of_nonneg_right (hmargin n) (sq_nonneg _)
    exact hmul.trans (S.rangeLog n)

end EffectiveChebotarevStatement

/-- A version of the standard statement whose range is exactly the paper's
`T⁶` range, obtained by adding the arithmetic fact `1 ≤ degree`.  This shows
that the range conjunct of `EffectiveChebotarevStatement` is not an additional
analytic hypothesis when the paper's `ChebotarevT6RangeInput` is available. -/
theorem effectiveChebotarevStatement_of_residual_of_rangeInput
    {K C cZ : ℝ} {T degree discLog count liX liBeta0 : ℕ → ℝ}
    (hK : 0 < K)
    (res : ChebotarevResidualInput C cZ (cutoff T) degree count liX liBeta0)
    (A : ChebotarevT6RangeInput K T degree discLog) (hdeg1 : ∀ n, 1 ≤ degree n) :
    EffectiveChebotarevStatement K C cZ (cutoff T) degree discLog count liX liBeta0 where
  C_pos := res.C_pos
  cZ_pos := res.cZ_pos
  residual := res.residual
  K_pos := hK
  range := effectiveChebotarevRangeCondition_of_rangeInput A hdeg1

/-- **The exact content of the standard statement.**  It is precisely the
canonical residual input, the positivity of the range constant, and the range
condition `x ≥ exp (K (log |Δ_E|)²)`.  No further analytic content is hidden in
the bundle. -/
theorem effectiveChebotarevStatement_iff {K C cZ : ℝ}
    {x degree discLog count liX liBeta0 : ℕ → ℝ} :
    EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0 ↔
      ChebotarevResidualInput C cZ x degree count liX liBeta0 ∧
        0 < K ∧ EffectiveChebotarevRangeCondition K x discLog := by
  constructor
  · intro S
    exact ⟨S.toResidualInput, S.K_pos, S.range⟩
  · rintro ⟨res, hK, hrange⟩
    exact ⟨res, hK, hrange⟩

/-- **The standard statement is exactly the residual input at the paper's
cutoff and range.**  Given the paper's explicit `ChebotarevT6RangeInput` and the
arithmetic fact `1 ≤ degree`, the standard effective Chebotarev statement at
`x = 2^{T⁶}` is inter-derivable with `ChebotarevResidualInput`.  Thus the
reduction loses nothing: the standard statement is the residual input plus the
range condition that the paper already verifies. -/
theorem effectiveChebotarevStatement_iff_residual_of_rangeInput
    {K C cZ : ℝ} {T degree discLog count liX liBeta0 : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog)
    (hdeg1 : ∀ n, 1 ≤ degree n) :
    EffectiveChebotarevStatement K C cZ (cutoff T) degree discLog count liX liBeta0 ↔
      ChebotarevResidualInput C cZ (cutoff T) degree count liX liBeta0 := by
  constructor
  · intro S
    exact S.toResidualInput
  · intro res
    exact effectiveChebotarevStatement_of_residual_of_rangeInput A.K_pos res A hdeg1

/-! ## 3. The isolated arithmetic inequalities

The effective Chebotarev theorem controls the counting error but says nothing
about the growth of the factorial factor `F` against the exponential gain in
the error.  The two conditions below are the exact remaining inequalities. -/

/-- **The exact missing inequality for error negligibility.**  After cancelling
the positive cutoff `x = 2^{T⁶}`, the polynomial factor `C F T⁶` divided by the
allowed error `cbr/8` must be at most the exponential gain
`exp (cZ sqrt (T⁶ log 2/(2d)))`.  Taking logarithms gives the stated budget. -/
def ChebotarevErrorLogBudget (C cZ cbr : ℝ) (F T degree : ℕ → ℝ) : Prop :=
  ∀ n, Real.log (C * (F n * T n ^ 6) / (cbr / 8)) ≤
    cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * degree n))

/-- **The exact missing inequality for the discarded ideals.**  After using
`sqrt (2^{T⁶}) = 2^{T⁶/2}`, the factor `d F T⁶` divided by `cbr/8` must be at
most `2^{T⁶/2}`.  Taking logarithms gives the stated budget. -/
def DegreeLossLogBudget (cbr : ℝ) (degree F T : ℕ → ℝ) : Prop :=
  ∀ n, Real.log (degree n * F n * T n ^ 6 / (cbr / 8)) ≤
    (T n) ^ 6 / 2 * Real.log 2

/-- The exponential cancellation `exp a * exp (-a) = 1`. -/
theorem exp_mul_exp_neg (a : ℝ) : Real.exp a * Real.exp (-a) = 1 := by
  rw [← Real.exp_add]
  ring_nf
  simp

/-- **The error scalar bound is exactly the logarithmic budget.** -/
theorem chebotarevErrorScalarBound_iff_logBudget {C cZ cbr : ℝ}
    {F T degree : ℕ → ℝ} (hC : 0 < C) (hcbr : 0 < cbr)
    (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n) :
    ChebotarevErrorScalarBound C cZ cbr F T degree ↔
      ChebotarevErrorLogBudget C cZ cbr F T degree := by
  unfold ChebotarevErrorScalarBound ChebotarevErrorLogBudget
  constructor
  · intro h n
    have hX : 0 < C * (F n * T n ^ 6) := by
      have := hF n
      have := hT n
      positivity
    have hE : 0 < scaledError cZ T degree n := Real.exp_pos _
    have hc8 : 0 < cbr / 8 := by positivity
    have hlog := Real.log_le_log (mul_pos hX hE) (h n)
    have hXE : Real.log (C * (F n * T n ^ 6) * scaledError cZ T degree n) =
        Real.log (C * (F n * T n ^ 6)) -
          cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * degree n)) := by
      rw [Real.log_mul hX.ne' hE.ne']
      unfold scaledError
      rw [Real.log_exp]
      ring
    have hr : Real.log (C * (F n * T n ^ 6) / (cbr / 8)) =
        Real.log (C * (F n * T n ^ 6)) - Real.log (cbr / 8) :=
      Real.log_div hX.ne' hc8.ne'
    rw [hXE, Real.log_div hcbr.ne' (by norm_num : (8 : ℝ) ≠ 0)] at hlog
    rw [hr, Real.log_div hcbr.ne' (by norm_num : (8 : ℝ) ≠ 0)]
    linarith
  · intro h n
    have hX : 0 < C * (F n * T n ^ 6) := by
      have := hF n
      have := hT n
      positivity
    have hc8 : 0 < cbr / 8 := by positivity
    have hratio : 0 < C * (F n * T n ^ 6) / (cbr / 8) := div_pos hX hc8
    have hle : C * (F n * T n ^ 6) / (cbr / 8) ≤
        Real.exp (cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * degree n))) :=
      (Real.log_le_iff_le_exp hratio).mp (h n)
    have hstep : C * (F n * T n ^ 6) * Real.exp
        (-(cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * degree n)))) ≤ cbr / 8 := by
      have hmul := mul_le_mul_of_nonneg_right hle
        (Real.exp_pos (-(cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 /
          (2 * degree n))))).le
      have hcancel : Real.exp (cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 /
            (2 * degree n))) *
          Real.exp (-(cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 /
            (2 * degree n)))) = 1 :=
        exp_mul_exp_neg _
      have hleft : (C * (F n * T n ^ 6) / (cbr / 8)) *
          Real.exp (-(cZ * Real.sqrt ((T n) ^ 6 * Real.log 2 /
            (2 * degree n)))) =
          (C * (F n * T n ^ 6) * Real.exp (-(cZ * Real.sqrt ((T n) ^ 6 *
            Real.log 2 / (2 * degree n))))) / (cbr / 8) := by
        ring
      rw [hleft, hcancel] at hmul
      rwa [div_le_one hc8] at hmul
    simpa [scaledError] using hstep

/-- **The discarded-ideal scalar bound is exactly the logarithmic budget.** -/
theorem degreeLossScalarBound_iff_logBudget {cbr : ℝ}
    {degree F T : ℕ → ℝ} (hcbr : 0 < cbr)
    (hdeg : ∀ n, 0 < degree n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n) :
    DegreeLossScalarBound cbr degree F T ↔
      DegreeLossLogBudget cbr degree F T := by
  unfold DegreeLossScalarBound DegreeLossLogBudget
  constructor
  · intro h n
    have hY : 0 < degree n * F n * T n ^ 6 := by
      have := hdeg n
      have := hF n
      have := hT n
      positivity
    have hc8 : 0 < cbr / 8 := by positivity
    have hr : 0 < (2 : ℝ) ^ ((T n) ^ 6 / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hR : (2 : ℝ) ^ ((T n) ^ 6) =
        (2 : ℝ) ^ ((T n) ^ 6 / 2) * (2 : ℝ) ^ ((T n) ^ 6 / 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hsc := h n
    rw [hR] at hsc
    have hsc' : degree n * F n * T n ^ 6 * (2 : ℝ) ^ ((T n) ^ 6 / 2) ≤
        ((cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6 / 2)) *
          (2 : ℝ) ^ ((T n) ^ 6 / 2) := by
      calc
        degree n * F n * T n ^ 6 * (2 : ℝ) ^ ((T n) ^ 6 / 2)
            ≤ (cbr / 8) * ((2 : ℝ) ^ ((T n) ^ 6 / 2) *
                (2 : ℝ) ^ ((T n) ^ 6 / 2)) := hsc
        _ = ((cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6 / 2)) *
              (2 : ℝ) ^ ((T n) ^ 6 / 2) := by ring
    have hYle : degree n * F n * T n ^ 6 ≤
        (cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6 / 2) :=
      (mul_le_mul_iff_of_pos_right hr).mp hsc'
    have hratio : degree n * F n * T n ^ 6 / (cbr / 8) ≤
        (2 : ℝ) ^ ((T n) ^ 6 / 2) := by
      rw [div_le_iff₀ hc8]
      simpa [mul_comm] using hYle
    have hlog := Real.log_le_log (div_pos hY hc8) hratio
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
    rw [Real.log_div hY.ne' hc8.ne'] at hlog
    rw [Real.log_div hY.ne' hc8.ne']
    exact hlog
  · intro h n
    have hY : 0 < degree n * F n * T n ^ 6 := by
      have := hdeg n
      have := hF n
      have := hT n
      positivity
    have hc8 : 0 < cbr / 8 := by positivity
    have hr : 0 < (2 : ℝ) ^ ((T n) ^ 6 / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hR : (2 : ℝ) ^ ((T n) ^ 6) =
        (2 : ℝ) ^ ((T n) ^ 6 / 2) * (2 : ℝ) ^ ((T n) ^ 6 / 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hlog : Real.log (degree n * F n * T n ^ 6 / (cbr / 8)) ≤
        Real.log ((2 : ℝ) ^ ((T n) ^ 6 / 2)) := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
      exact h n
    have hratio : degree n * F n * T n ^ 6 / (cbr / 8) ≤
        (2 : ℝ) ^ ((T n) ^ 6 / 2) := by
      have hle := (Real.log_le_iff_le_exp (div_pos hY hc8)).mp hlog
      rwa [Real.exp_log hr] at hle
    have hYle : degree n * F n * T n ^ 6 ≤
        (cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6 / 2) := by
      have := (div_le_iff₀ hc8).mp hratio
      simpa [mul_comm] using this
    have hmul : degree n * F n * T n ^ 6 * (2 : ℝ) ^ ((T n) ^ 6 / 2) ≤
        ((cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6 / 2)) *
          (2 : ℝ) ^ ((T n) ^ 6 / 2) :=
      mul_le_mul_of_nonneg_right hYle hr.le
    calc
      degree n * F n * T n ^ 6 * (2 : ℝ) ^ ((T n) ^ 6 / 2)
          ≤ ((cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6 / 2)) *
              (2 : ℝ) ^ ((T n) ^ 6 / 2) := hmul
      _ = (cbr / 8) * ((2 : ℝ) ^ ((T n) ^ 6 / 2) *
            (2 : ℝ) ^ ((T n) ^ 6 / 2)) := by ring
      _ = (cbr / 8) * (2 : ℝ) ^ ((T n) ^ 6) := by rw [← hR]

/-- **The error-negligibility `Prop` follows from the log budget.**  This is
the reduction of the paper's `ChebotarevErrorNegligible`, using only the
unconditional cancellation of `x = 2^{T⁶}`. -/
theorem chebotarevErrorNegligible_of_logBudget {C cZ cbr : ℝ}
    {F T degree : ℕ → ℝ} (hC : 0 < C) (hcbr : 0 < cbr)
    (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (h : ChebotarevErrorLogBudget C cZ cbr F T degree) :
    ChebotarevErrorNegligible cbr (cutoff T) F T
      (lagariasOdlyzkoError C cZ (cutoff T) degree) :=
  (chebotarevErrorNegligible_iff_scalar hF hT).mpr
    ((chebotarevErrorScalarBound_iff_logBudget hC hcbr hF hT).mpr h)

/-- **The discarded-ideal `Prop` follows from the log budget.** -/
theorem degreeOneLossNegligible_of_logBudget {cbr : ℝ}
    {degree F T : ℕ → ℝ} (hcbr : 0 < cbr)
    (hdeg : ∀ n, 0 < degree n) (hF : ∀ n, 0 < F n) (hT : ∀ n, 0 < T n)
    (h : DegreeLossLogBudget cbr degree F T) :
    DegreeOneLossNegligible cbr (cutoff T) degree F T :=
  (degreeOneLossNegligible_iff_scalar hF hT).mpr
    ((degreeLossScalarBound_iff_logBudget hcbr hdeg hF hT).mpr h)

/-! ## 4. Monotonicity and positivity of the Lagarias–Odlyzko error -/

/-- The explicit error is nonnegative for `C ≥ 0` and `x ≥ 0`. -/
theorem lagariasOdlyzkoError_nonneg_of {C cZ : ℝ} {x degree : ℕ → ℝ}
    (hC : 0 ≤ C) (hx : ∀ n, 0 ≤ x n) (n : ℕ) :
    0 ≤ lagariasOdlyzkoError C cZ x degree n :=
  lagariasOdlyzkoError_nonneg hC hx n

/-- The explicit error is positive for `C > 0` and `x > 0`. -/
theorem lagariasOdlyzkoError_pos_of {C cZ : ℝ} {x degree : ℕ → ℝ}
    (hC : 0 < C) (hx : ∀ n, 0 < x n) (n : ℕ) :
    0 < lagariasOdlyzkoError C cZ x degree n :=
  lagariasOdlyzkoError_pos hC hx n

/-- The error is monotone in the constant `C` when `x ≥ 0`. -/
theorem lagariasOdlyzkoError_mono_C {C C' cZ : ℝ} {x degree : ℕ → ℝ}
    (hCC : C ≤ C') (hx : ∀ n, 0 ≤ x n) (n : ℕ) :
    lagariasOdlyzkoError C cZ x degree n ≤
      lagariasOdlyzkoError C' cZ x degree n := by
  unfold lagariasOdlyzkoError
  have hfront : C * x n ≤ C' * x n :=
    mul_le_mul_of_nonneg_right hCC (hx n)
  exact mul_le_mul_of_nonneg_right hfront (Real.exp_pos _).le

/-- The error is antitone in the decay constant `cZ` on nonnegative fronts. -/
theorem lagariasOdlyzkoError_antitone_cZ {C cZ cZ' : ℝ} {x degree : ℕ → ℝ}
    (hc : cZ ≤ cZ') (hCx : ∀ n, 0 ≤ C * x n) (n : ℕ) :
    lagariasOdlyzkoError C cZ' x degree n ≤
      lagariasOdlyzkoError C cZ x degree n := by
  unfold lagariasOdlyzkoError
  have hs : 0 ≤ Real.sqrt (Real.log (x n) / (2 * degree n)) := Real.sqrt_nonneg _
  have hexp : Real.exp (-(cZ' * Real.sqrt (Real.log (x n) / (2 * degree n)))) ≤
      Real.exp (-(cZ * Real.sqrt (Real.log (x n) / (2 * degree n)))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp (hCx n)

/-- **The error is monotone in the absolute degree** when the cutoff logarithm
is nonnegative.  A larger degree shrinks `log x/(2d)`, hence the exponential
decay, so the envelope grows. -/
theorem lagariasOdlyzkoError_mono_degree {C cZ : ℝ} {x degree degree' : ℕ → ℝ}
    (hC : 0 ≤ C) (hx : ∀ n, 0 ≤ x n) (hlog : ∀ n, 0 ≤ Real.log (x n))
    (hcZ : 0 ≤ cZ) (hdeg : ∀ n, 0 < degree n)
    (hdd : ∀ n, degree n ≤ degree' n) (n : ℕ) :
    lagariasOdlyzkoError C cZ x degree n ≤
      lagariasOdlyzkoError C cZ x degree' n := by
  unfold lagariasOdlyzkoError
  have hs : Real.sqrt (Real.log (x n) / (2 * degree' n)) ≤
      Real.sqrt (Real.log (x n) / (2 * degree n)) := by
    apply Real.sqrt_le_sqrt
    have hb : (0 : ℝ) < 2 * degree n := by nlinarith [hdeg n]
    have hbc : 2 * degree n ≤ 2 * degree' n := by nlinarith [hdd n]
    exact div_le_div_of_nonneg_left (hlog n) hb hbc
  have hexp : Real.exp (-(cZ * Real.sqrt (Real.log (x n) / (2 * degree n)))) ≤
      Real.exp (-(cZ * Real.sqrt (Real.log (x n) / (2 * degree' n)))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp (mul_nonneg hC (hx n))

/-- The scaled error is positive. -/
theorem scaledError_pos (cZ : ℝ) (T degree : ℕ → ℝ) (n : ℕ) :
    0 < scaledError cZ T degree n :=
  Real.exp_pos _

/-- The scaled error is at most one for a nonnegative decay constant. -/
theorem scaledError_le_one {cZ : ℝ} {T degree : ℕ → ℝ}
    (hcZ : 0 ≤ cZ) (n : ℕ) : scaledError cZ T degree n ≤ 1 := by
  unfold scaledError
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ Real.sqrt ((T n) ^ 6 * Real.log 2 / (2 * degree n)) :=
    Real.sqrt_nonneg _
  nlinarith

/-- The error at the cutoff is the explicit front times the scaled error. -/
theorem lagariasOdlyzkoError_cutoff_eq {C cZ : ℝ} {T degree : ℕ → ℝ} (n : ℕ) :
    lagariasOdlyzkoError C cZ (cutoff T) degree n =
      C * cutoff T n * scaledError cZ T degree n := by
  rw [lagariasOdlyzkoError_cutoff]
  rfl

/-! ## 5. Nonvacuity of the isolated statements -/

/-- The concrete nonvacuous standard statement instance used by the
nonvacuity and non-implication witnesses. -/
theorem effectiveChebotarevStatement_zero :
    EffectiveChebotarevStatement 1 1 1 (fun _ => Real.exp 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  refine ⟨⟨one_pos, one_pos, ?_⟩, one_pos, ?_⟩
  · intro n
    have hpos : 0 < lagariasOdlyzkoError 1 1 (fun _ => Real.exp 1)
        (fun _ => 1) n :=
      lagariasOdlyzkoError_pos one_pos (fun _ => Real.exp_pos 1) n
    simpa [mainOf] using hpos.le
  · intro n
    simp

/-- **The standard effective Chebotarev statement is nonvacuous.**  Concrete
witnesses: `x = exp 1`, `degree = discLog = 1`, `count = liX = liBeta0 = 0`,
`K = C = cZ = 1`.  The range is an equality and the residual is `0 ≤ error`. -/
theorem effectiveChebotarevStatement_nonvacuous :
    ∃ (K C cZ : ℝ) (x degree discLog count liX liBeta0 : ℕ → ℝ),
      EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0 :=
  ⟨1, 1, 1, (fun _ => Real.exp 1), (fun _ => 1), (fun _ => 1),
    (fun _ => 0), (fun _ => 0), (fun _ => 0), effectiveChebotarevStatement_zero⟩

/-- **The error scalar bound is nonvacuous.**  With `C = 1`, `cZ = 100`,
`cbr = 8`, `F = 1`, `T = 2`, `degree = 1`, the exponential factor is at most
`1/64`, so the error is at most `64/64 = 1 = cbr/8`. -/
theorem chebotarevErrorScalarBound_nonvacuous :
    ChebotarevErrorScalarBound 1 100 8 (fun _ => 1) (fun _ => 2) (fun _ => 1) := by
  intro n
  have hs : (1 : ℝ) ≤ Real.sqrt (32 * Real.log 2) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.log_two_gt_d9]
  have hy : (64 : ℝ) ≤ 100 * Real.sqrt (32 * Real.log 2) := by nlinarith
  have hexp : (64 : ℝ) ≤ Real.exp (100 * Real.sqrt (32 * Real.log 2)) := by
    have := Real.add_one_le_exp (100 * Real.sqrt (32 * Real.log 2))
    linarith
  have hinv : Real.exp (-(100 * Real.sqrt (32 * Real.log 2))) ≤ 1 / 64 := by
    rw [Real.exp_neg]
    simpa [one_div] using
      one_div_le_one_div_of_le (a := (64 : ℝ))
        (b := Real.exp (100 * Real.sqrt (32 * Real.log 2)))
        (by norm_num) hexp
  have harg : ((2 : ℝ) ^ 6 * Real.log 2 / (2 * (1 : ℝ))) = 32 * Real.log 2 := by
    norm_num
    ring
  have hsimp : 1 * (1 * (2 : ℝ) ^ 6) *
      scaledError 100 (fun _ => 2) (fun _ => 1) n =
      64 * Real.exp (-(100 * Real.sqrt (32 * Real.log 2))) := by
    unfold scaledError
    rw [harg]
    norm_num
  rw [hsimp]
  have h64 : 64 * Real.exp (-(100 * Real.sqrt (32 * Real.log 2))) ≤
      64 * (1 / 64) :=
    mul_le_mul_of_nonneg_left hinv (by norm_num)
  norm_num at h64 ⊢
  linarith

/-- **The discarded-ideal scalar bound is nonvacuous.**  With `cbr = 8`,
`degree = F = 1`, `T = 2`, the bound is `64 * 2^32 ≤ 2^64`. -/
theorem degreeLossScalarBound_nonvacuous :
    DegreeLossScalarBound 8 (fun _ => 1) (fun _ => 1) (fun _ => 2) := by
  intro n
  have hr : 0 < (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) := by norm_num
  have hmain : (64 : ℝ) * (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) ≤
      (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) * (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) :=
    mul_le_mul_of_nonneg_right h64 hr.le
  have hpow : (2 : ℝ) ^ ((2 : ℝ) ^ 6) =
      (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) * (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    1 * 1 * (2 : ℝ) ^ 6 * (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2)
        = 64 * (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) := by norm_num
    _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) * (2 : ℝ) ^ ((2 : ℝ) ^ 6 / 2) := hmain
    _ = (2 : ℝ) ^ ((2 : ℝ) ^ 6) := hpow.symm
    _ = (8 / 8) * (2 : ℝ) ^ ((2 : ℝ) ^ 6) := by norm_num

/-- The error log budget is nonvacuous as well, by the scalar witness. -/
theorem chebotarevErrorLogBudget_nonvacuous :
    ChebotarevErrorLogBudget 1 100 8 (fun _ => 1) (fun _ => 2) (fun _ => 1) :=
  (chebotarevErrorScalarBound_iff_logBudget
    (C := 1) (cZ := 100) (cbr := 8)
    (F := fun _ => 1) (T := fun _ => 2) (degree := fun _ => 1)
    one_pos (by norm_num) (fun _ => one_pos) (fun _ => by norm_num)).mp
    chebotarevErrorScalarBound_nonvacuous

/-- The discarded-ideal log budget is nonvacuous as well. -/
theorem degreeLossLogBudget_nonvacuous :
    DegreeLossLogBudget 8 (fun _ => 1) (fun _ => 1) (fun _ => 2) :=
  (degreeLossScalarBound_iff_logBudget
    (cbr := 8) (degree := fun _ => 1) (F := fun _ => 1) (T := fun _ => 2)
    (by norm_num) (fun _ => one_pos) (fun _ => one_pos) (fun _ => by norm_num)).mp
    degreeLossScalarBound_nonvacuous

/-- **The error log budget is genuinely not a consequence of the standard
statement.**  The standard statement does not constrain the factorial factor
`F`.  With `F n = exp 1000` the logarithmic budget fails at every index, while
the concrete instance `effectiveChebotarevStatement_zero` of the standard
statement still holds.  This is why the error-negligibility step is isolated as
a separate arithmetic input rather than derived from the effective theorem. -/
theorem errorLogBudget_not_implied_by_statement :
    ∃ (K C cZ cbr : ℝ) (x degree discLog count liX liBeta0 F T : ℕ → ℝ),
      EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0 ∧
        ¬ ChebotarevErrorLogBudget C cZ cbr F T degree := by
  refine ⟨1, 1, 1, 8, (fun _ => Real.exp 1), (fun _ => 1), (fun _ => 1),
    (fun _ => 0), (fun _ => 0), (fun _ => 0),
    (fun _ => Real.exp 1000), (fun _ => 2), effectiveChebotarevStatement_zero, ?_⟩
  intro h
  have h0 := h 0
  have harg : 1 * (Real.exp 1000 * (2 : ℝ) ^ 6) / (8 / 8) =
      Real.exp 1000 * 64 := by
    norm_num
  rw [harg, Real.log_mul (Real.exp_ne_zero 1000) (by norm_num : (64 : ℝ) ≠ 0),
    Real.log_exp] at h0
  have hsqrt : ((2 : ℝ) ^ 6 * Real.log 2 / (2 * (1 : ℝ))) =
      32 * Real.log 2 := by
    norm_num
    ring
  rw [hsqrt] at h0
  simp only [one_mul] at h0
  have hsqlt : Real.sqrt (32 * Real.log 2) < 32 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 32)]
    nlinarith [Real.log_two_lt_d9]
  have hlog64 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  nlinarith

/-- **The discarded-ideal log budget is genuinely not a consequence of the
standard statement.**  The same unconstrained factorial factor `F = exp 1000`
makes the budget fail, while the standard statement instance still holds. -/
theorem degreeLogBudget_not_implied_by_statement :
    ∃ (K C cZ cbr : ℝ) (x degree discLog count liX liBeta0 F T : ℕ → ℝ),
      EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0 ∧
        ¬ DegreeLossLogBudget cbr degree F T := by
  refine ⟨1, 1, 1, 8, (fun _ => Real.exp 1), (fun _ => 1), (fun _ => 1),
    (fun _ => 0), (fun _ => 0), (fun _ => 0),
    (fun _ => Real.exp 1000), (fun _ => 2), effectiveChebotarevStatement_zero, ?_⟩
  intro h
  have h0 := h 0
  have harg : 1 * Real.exp 1000 * (2 : ℝ) ^ 6 / (8 / 8) =
      Real.exp 1000 * 64 := by
    norm_num
  rw [harg, Real.log_mul (Real.exp_ne_zero 1000) (by norm_num : (64 : ℝ) ≠ 0),
    Real.log_exp] at h0
  have hrhs : ((2 : ℝ) ^ 6 / 2 * Real.log 2) = 32 * Real.log 2 := by
    norm_num
  rw [hrhs] at h0
  have h32 : 32 * Real.log 2 < 32 := by
    nlinarith [Real.log_two_lt_d9]
  have hlog64 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  nlinarith

/-! ## 6. The reduction bundle -/

/-- **The L34 Chebotarev sides from the standard effective Chebotarev
statement.**  This is `L34ChebotarevSidesInputs` with

* `cheb` replaced by `effective : EffectiveChebotarevStatement ...`;
* `error_scalar` replaced by the isolated `error_log : ChebotarevErrorLogBudget`;
* `degree_loss_scalar` replaced by the isolated `degree_log : DegreeLossLogBudget`.

All other fields are inherited verbatim. -/
structure L34EffectiveChebotarevInputs where
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
  /-- **The standard effective Chebotarev statement**, replacing the
  residual input `cheb`. -/
  effective : EffectiveChebotarevStatement K C cZ (cutoff T) degree discLog
    count liX liBeta0
  /-- The inert count contains the counted nonidentity class. -/
  inert_ge_count : ∀ n, count n ≤ inertCount n
  /-- Stark's bound converted to the dyadic bracket. -/
  bracket : LogIntegralBracket cbr (cutoff T) F T liX liBeta0
  /-- **The isolated error-negligibility inequality**, replacing the scalar
  bound `error_scalar`. -/
  error_log : ChebotarevErrorLogBudget C cZ cbr F T degree
  /-- **The isolated discarded-ideal inequality**, replacing the scalar bound
  `degree_loss_scalar`. -/
  degree_log : DegreeLossLogBudget cbr degree F T
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

namespace L34EffectiveChebotarevInputs

variable (S : L34EffectiveChebotarevInputs)

/-- The positivity of `T`, from `T_ge_one`. -/
theorem T_pos (n : ℕ) : 0 < S.T n :=
  lt_of_lt_of_le zero_lt_one (S.T_ge_one n)

/-- **The reduction chain.**  `L34ChebotarevSidesInputs` from the standard
effective Chebotarev statement and the two isolated arithmetic budgets. -/
noncomputable def toL34ChebotarevSidesInputs :
    Cogentic.RandomizedL34ChebotarevSides.L34ChebotarevSidesInputs where
  beta0 := S.beta0
  zeroRealPart := S.zeroRealPart
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
  zeroFree := S.zeroFree
  stark := S.stark
  range := S.range
  T_ge_one := S.T_ge_one
  cheb := S.effective.toResidualInput
  inert_ge_count := S.inert_ge_count
  bracket := S.bracket
  error_scalar :=
    (chebotarevErrorScalarBound_iff_logBudget S.effective.C_pos S.bracket.1
      S.stark.F_pos S.T_pos).mpr S.error_log
  degree_loss_scalar :=
    (degreeLossScalarBound_iff_logBudget S.bracket.1 S.range.degree_pos
      S.stark.F_pos S.T_pos).mpr S.degree_log
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

/-- The reduced bundle's standard statement is consistent with the paper's
explicit range whenever `1 ≤ degree`: the statement's range condition follows
from `range` alone. -/
theorem effective_range_derived (hdeg1 : ∀ n, 1 ≤ S.degree n) :
    EffectiveChebotarevRangeCondition S.K (cutoff S.T) S.discLog :=
  effectiveChebotarevRangeCondition_of_rangeInput S.range hdeg1

/-- The composed detection lower bound, inherited from the reduced bundle. -/
theorem probeLower (n : ℕ) :
    S.csel * S.cbr / 4 / (S.degree n * S.F n * S.T n ^ 6) ≤ S.pTrial n :=
  S.toL34ChebotarevSidesInputs.probeLower n

/-- The assembled core's loss is exactly the actual probe miss. -/
theorem toL34SidesCore_loss (n : ℕ) :
    S.toL34ChebotarevSidesInputs.toL34SidesCore.loss n = S.actualMiss n :=
  S.toL34ChebotarevSidesInputs.toL34SidesCore_loss n

/-- The assembled core's loss satisfies the ledger bound. -/
theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      S.toL34ChebotarevSidesInputs.toL34SidesCore.loss n ≤
        exp (-(2 : ℝ) * scale n) :=
  S.toL34ChebotarevSidesInputs.loss_le_ledger

/-- The manuscript's paper rate for the assembled core. -/
theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      S.toL34ChebotarevSidesInputs.toL34SidesCore.loss n ≤
        exp (-(1 * paperRate n)) :=
  S.toL34ChebotarevSidesInputs.loss_le_paper

/-- The literal `RatedLeaf` of the reduced bundle. -/
noncomputable def ratedLeaf : Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  S.toL34ChebotarevSidesInputs.ratedLeaf

/-- The leaf's loss is the actual probe miss. -/
theorem ratedLeaf_loss_eq (n : ℕ) : S.ratedLeaf.loss n = S.actualMiss n :=
  S.toL34SidesCore_loss n

end L34EffectiveChebotarevInputs

/-! ## Axiom audit -/

#check EffectiveChebotarevRangeCondition
#check EffectiveChebotarevStatement
#check ChebotarevErrorLogBudget
#check DegreeLossLogBudget
#check L34EffectiveChebotarevInputs
#check L34EffectiveChebotarevInputs.toL34ChebotarevSidesInputs

#print axioms effectiveChebotarevRangeCondition_iff_log
#print axioms effectiveChebotarevRangeCondition_of_rangeInput
#print axioms EffectiveChebotarevStatement.toResidualInput
#print axioms EffectiveChebotarevStatement.toLowerInput
#print axioms EffectiveChebotarevStatement.toSlack
#print axioms EffectiveChebotarevStatement.rangeLog
#print axioms EffectiveChebotarevStatement.toRangeInput
#print axioms effectiveChebotarevStatement_of_residual_of_rangeInput
#print axioms effectiveChebotarevStatement_iff
#print axioms effectiveChebotarevStatement_iff_residual_of_rangeInput
#print axioms exp_mul_exp_neg
#print axioms chebotarevErrorScalarBound_iff_logBudget
#print axioms degreeLossScalarBound_iff_logBudget
#print axioms chebotarevErrorNegligible_of_logBudget
#print axioms degreeOneLossNegligible_of_logBudget
#print axioms lagariasOdlyzkoError_nonneg_of
#print axioms lagariasOdlyzkoError_pos_of
#print axioms lagariasOdlyzkoError_mono_C
#print axioms lagariasOdlyzkoError_antitone_cZ
#print axioms lagariasOdlyzkoError_mono_degree
#print axioms scaledError_pos
#print axioms scaledError_le_one
#print axioms lagariasOdlyzkoError_cutoff_eq
#print axioms effectiveChebotarevStatement_zero
#print axioms effectiveChebotarevStatement_nonvacuous
#print axioms chebotarevErrorScalarBound_nonvacuous
#print axioms degreeLossScalarBound_nonvacuous
#print axioms chebotarevErrorLogBudget_nonvacuous
#print axioms degreeLossLogBudget_nonvacuous
#print axioms errorLogBudget_not_implied_by_statement
#print axioms degreeLogBudget_not_implied_by_statement
#print axioms L34EffectiveChebotarevInputs.toL34ChebotarevSidesInputs
#print axioms L34EffectiveChebotarevInputs.effective_range_derived
#print axioms L34EffectiveChebotarevInputs.probeLower
#print axioms L34EffectiveChebotarevInputs.toL34SidesCore_loss
#print axioms L34EffectiveChebotarevInputs.loss_le_ledger
#print axioms L34EffectiveChebotarevInputs.loss_le_paper
#print axioms L34EffectiveChebotarevInputs.ratedLeaf
#print axioms L34EffectiveChebotarevInputs.ratedLeaf_loss_eq

end

end Cogentic.RandomizedL34EffectiveChebotarev
