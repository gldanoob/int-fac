import Cogentic.RandomizedL34Analytic

/-!
# L34: the Dedekind zeta inputs in their smallest explicit form

`Cogentic.RandomizedL34Analytic` reduced the five paper-level analytic `Prop`s
to the bundle `AnalyticSubProps`:

* `DedekindZeroFreeCore` — the Dedekind zero-free region away from `β₀`;
* `StarkGap` — Stark's bound `1 - β₀ ≥ (4 F log |Δ_E|)⁻¹`;
* `ChebotarevRangeInequality` — the range `K d (log |Δ_E|)² ≤ log x`;
* `ChebotarevLowerBound` / `ChebotarevUpperBound` — the two sides of the
  cumulative Chebotarev count.

This file rewrites those four groups in the smallest equivalent forms that are
actually consumed by the paper, and proves that the resulting small bundle is
*equivalent* to `AnalyticSubProps` and hence reduces to `L34AnalyticCore`.

## Reductions

* **Zero-free region.**  `DedekindZeroFreeCore` is equivalent to
  `DedekindZeroFreeAboveBeta` (every zero strictly above `β₀` lies on the
  zero-free side of `1 - c_z / log |Δ_E|`) and to the dichotomy form
  `DedekindZeroFreeMax` (`Re ρ ≤ max β₀ (1 - c_z / log |Δ_E|)`).  See
  `dedekindZeroFreeCore_iff_aboveBeta` and `dedekindZeroFreeCore_iff_max`.
  These are single inequalities, with no nested implication or positivity
  conjunct.

* **Stark's bound.**  `StarkGap` is equivalent to the upper bound
  `β₀ ≤ 1 - (4 F log |Δ_E|)⁻¹` (`StarkBetaUpper`), which is the form used in
  the bracket computation.

* **Range condition.**  `ChebotarevRangeInequality` is equivalent to the
  explicit threshold `exp (K d (log |Δ_E|)²) ≤ x` and, when `x = 2^S`, to the
  purely arithmetic exponent inequality
  `K d (log |Δ_E|)² ≤ (log 2) S`.  This is exactly how the paper chooses
  `x = 2^S`: the analytic range input becomes an exponent budget.

* **Cumulative Chebotarev count.**  The two-sided count is equivalent to the
  pair `ChebotarevSides`, and is implied by the weaker `ChebotarevErrorSlack`
  data: any nonnegative error `err` with `err ≤ C x exp(-c sqrt(log x / 2d))`
  and `|count - main| ≤ err` already gives both sides.  This removes the
  artificial requirement that the error be *exactly* the Lagarias–Odlyzko
  expression.

## What is not reduced

Mathlib has no Dedekind zeta function, no Chebotarev theorem, and no zero
theory for either.  The character and prime-count estimates in
`Cogentic.Window.CharacterEstimate` are for Dirichlet `L`-functions on the
critical line and do not define `ζ_E`, its zeros, or the ideal count `count`.
Consequently `DedekindZeroFreeAboveBeta`, `StarkGap`, the range inequality and
the Chebotarev count remain explicit analytic hypotheses.  They are stated
below as the *smallest* forms we can isolate; no `sorry`, `axiom`, or
`native_decide` is used, and no count, error, or loss is set to zero.

## The reduction to `L34AnalyticCore`

`DedekindAnalyticInputs` assembles the four small sub-`Prop`s.  The theorem
`DedekindAnalyticInputs.toAnalyticSubProps` proves the implication to the
existing reduced bundle, and `AnalyticSubProps.toDedekindAnalyticInputs` proves
the converse, so the rewrite is lossless.  Finally `L34DedekindCore` is
`L34AnalyticCore` with the `sub` field replaced by `DedekindAnalyticInputs`;
`L34DedekindCore.toL34AnalyticCore` performs the reduction and re-exports the
L34 ledger bounds.
-/

namespace Cogentic.RandomizedL34Dedekind

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The Dedekind zero-free region -/

/-- **Zero-free region, "above `β₀`" form.**  Every zero whose real part is
strictly larger than `β₀` lies on the zero-free side of the line
`1 - c_z / log |Δ_E|`.  This is the standard "all but one exceptional zero"
statement, written as a single implication. -/
def DedekindZeroFreeAboveBeta (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n < zeroRealPart n → zeroRealPart n ≤ 1 - cz / discLog n

/-- **Zero-free region, dichotomy form.**  Every zero is at most the larger of
`β₀` and the zero-free line.  This is the form consumed by `max`-based case
splits. -/
def DedekindZeroFreeMax (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, zeroRealPart n ≤ max (beta0 n) (1 - cz / discLog n)

/-- The core inequality is equivalent to its "above `β₀`" form. -/
theorem dedekindZeroFreeCore_iff_aboveBeta {beta0 zeroRealPart : ℕ → ℝ}
    {cz : ℝ} {discLog : ℕ → ℝ} :
    DedekindZeroFreeCore beta0 zeroRealPart cz discLog ↔
      DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog := by
  constructor
  · intro h n hb
    by_contra hnot
    have hz : 1 - cz / discLog n < zeroRealPart n := lt_of_not_ge hnot
    have hle := h n hz
    linarith
  · intro h n hz
    by_contra hnot
    have hb : beta0 n < zeroRealPart n := lt_of_not_ge hnot
    have hle := h n hb
    linarith

/-- The core inequality implies its "above `β₀`" form. -/
theorem dedekindZeroFreeAboveBeta_of_core {beta0 zeroRealPart : ℕ → ℝ}
    {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeCore beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeCore_iff_aboveBeta.mp h

/-- The "above `β₀`" form implies the core inequality. -/
theorem dedekindZeroFreeCore_of_aboveBeta {beta0 zeroRealPart : ℕ → ℝ}
    {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeCore beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeCore_iff_aboveBeta.mpr h

/-- The core inequality is equivalent to the dichotomy form. -/
theorem dedekindZeroFreeCore_iff_max {beta0 zeroRealPart : ℕ → ℝ}
    {cz : ℝ} {discLog : ℕ → ℝ} :
    DedekindZeroFreeCore beta0 zeroRealPart cz discLog ↔
      DedekindZeroFreeMax beta0 zeroRealPart cz discLog := by
  constructor
  · intro h n
    exact dedekindZeroFreeCore_dichotomy h n
  · intro h n hz
    have hmax := h n
    by_contra hnot
    have hb : beta0 n < zeroRealPart n := lt_of_not_ge hnot
    have hlt : max (beta0 n) (1 - cz / discLog n) < zeroRealPart n :=
      max_lt hb hz
    linarith

/-- The core inequality gives the dichotomy form. -/
theorem dedekindZeroFreeMax_of_core {beta0 zeroRealPart : ℕ → ℝ}
    {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeCore beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeMax beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeCore_iff_max.mp h

/-- The dichotomy form gives the core inequality. -/
theorem dedekindZeroFreeCore_of_max {beta0 zeroRealPart : ℕ → ℝ}
    {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeMax beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeCore beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeCore_iff_max.mpr h

/-- **The smallest zero-free input.**  Positivity of the constant together with
the "above `β₀`" statement. -/
structure DedekindZeroFreeInput (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop where
  /-- The zero-free-region constant is positive. -/
  cz_pos : 0 < cz
  /-- Every zero above `β₀` is on the zero-free side. -/
  above_beta : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog

/-- The smallest zero-free input rebuilds the paper-level region. -/
theorem DedekindZeroFreeInput.toDedekindZeroFreeRegion
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : DedekindZeroFreeInput beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeRegion beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeRegion_of_core Z.cz_pos
    (dedekindZeroFreeCore_of_aboveBeta Z.above_beta)

/-- The paper-level region gives the smallest zero-free input. -/
theorem DedekindZeroFreeInput.ofRegion
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeRegion beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeInput beta0 zeroRealPart cz discLog where
  cz_pos := h.1
  above_beta := dedekindZeroFreeAboveBeta_of_core h.2

/-! ## 2. Stark's exceptional-zero bound -/

/-- **Stark's bound, upper-bound form.**  The exceptional zero satisfies
`β₀ ≤ 1 - (4 F log |Δ_E|)⁻¹`. -/
def StarkBetaUpper (beta0 F discLog : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n ≤ 1 - 1 / (4 * F n * discLog n)

/-- `StarkGap` is exactly the upper-bound form. -/
theorem starkGap_iff_betaUpper {beta0 F discLog : ℕ → ℝ} :
    StarkGap beta0 F discLog ↔ StarkBetaUpper beta0 F discLog := by
  constructor <;> intro h n <;> linarith [h n]

/-- Stark's gap in upper-bound form. -/
theorem starkBetaUpper_of_starkGap {beta0 F discLog : ℕ → ℝ}
    (h : StarkGap beta0 F discLog) : StarkBetaUpper beta0 F discLog :=
  starkGap_iff_betaUpper.mp h

/-- The upper-bound form is Stark's gap. -/
theorem starkGap_of_betaUpper {beta0 F discLog : ℕ → ℝ}
    (h : StarkBetaUpper beta0 F discLog) : StarkGap beta0 F discLog :=
  starkGap_iff_betaUpper.mpr h

/-- **The smallest Stark input.**  The gap itself, with no positivity conjunct. -/
structure StarkInput (beta0 F discLog : ℕ → ℝ) : Prop where
  /-- Stark's exceptional-zero gap. -/
  gap : StarkGap beta0 F discLog

/-- The smallest Stark input rebuilds the paper-level bound once `F` and
`log |Δ_E|` are positive. -/
theorem StarkInput.toStarkExceptionalZeroBound {beta0 F discLog : ℕ → ℝ}
    (S : StarkInput beta0 F discLog) (hF : ∀ n, 0 < F n)
    (hD : ∀ n, 0 < discLog n) :
    StarkExceptionalZeroBound beta0 F discLog :=
  starkExceptionalZeroBound_of_gap hF hD S.gap

/-- The paper-level Stark bound gives the smallest Stark input. -/
theorem StarkInput.ofBound {beta0 F discLog : ℕ → ℝ}
    (h : StarkExceptionalZeroBound beta0 F discLog) :
    StarkInput beta0 F discLog where
  gap := starkGap_of_starkExceptionalZeroBound h

/-! ## 3. The Lagarias–Odlyzko range condition -/

/-- The explicit threshold `exp (K d (log |Δ_E|)²)`. -/
noncomputable def chebotarevExpThreshold (K : ℝ) (degree discLog : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  Real.exp (K * degree n * (discLog n) ^ 2)

/-- **Range condition, threshold form.**  The cutoff is at least the explicit
exponential threshold. -/
def ChebotarevRangeThreshold (K : ℝ) (x degree discLog : ℕ → ℝ) : Prop :=
  ∀ n, chebotarevExpThreshold K degree discLog n ≤ x n

/-- The logarithmic range inequality is equivalent to the explicit threshold,
for positive cutoffs. -/
theorem chebotarevRangeInequality_iff_threshold {K : ℝ} {x degree discLog : ℕ → ℝ}
    (hx : ∀ n, 0 < x n) :
    ChebotarevRangeInequality K x degree discLog ↔
      ChebotarevRangeThreshold K x degree discLog := by
  constructor
  · intro h n
    simpa [chebotarevExpThreshold] using
      (Real.le_log_iff_exp_le (hx n)).mp (h n)
  · intro h n
    simpa [chebotarevExpThreshold] using
      (Real.le_log_iff_exp_le (hx n)).mpr (h n)

/-- The range inequality gives the threshold form. -/
theorem chebotarevRangeThreshold_of_inequality {K : ℝ} {x degree discLog : ℕ → ℝ}
    (hx : ∀ n, 0 < x n) (h : ChebotarevRangeInequality K x degree discLog) :
    ChebotarevRangeThreshold K x degree discLog :=
  (chebotarevRangeInequality_iff_threshold hx).mp h

/-- The threshold form gives the range inequality. -/
theorem chebotarevRangeInequality_of_threshold {K : ℝ} {x degree discLog : ℕ → ℝ}
    (hx : ∀ n, 0 < x n) (h : ChebotarevRangeThreshold K x degree discLog) :
    ChebotarevRangeInequality K x degree discLog :=
  (chebotarevRangeInequality_iff_threshold hx).mpr h

/-- **Range condition, exponent form for `x = 2^S`.**  This is the arithmetic
condition the paper actually checks: the exponent `S` dominates
`K d (log |Δ_E|)² / log 2`. -/
def ChebotarevExponentCondition (K : ℝ) (S degree discLog : ℕ → ℝ) : Prop :=
  ∀ n, K * degree n * (discLog n) ^ 2 ≤ Real.log 2 * S n

/-- **The range condition for `x = 2^S` reduces to an exponent inequality.** -/
theorem chebotarevRangeInequality_rpow_two {K : ℝ} {S degree discLog : ℕ → ℝ}
    (h : ChebotarevExponentCondition K S degree discLog) :
    ChebotarevRangeInequality K (fun n => (2 : ℝ) ^ S n) degree discLog := by
  intro n
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  simpa [mul_comm] using h n

/-- Conversely, the range condition for `x = 2^S` is the exponent inequality. -/
theorem chebotarevExponentCondition_of_rpow_two {K : ℝ} {S degree discLog : ℕ → ℝ}
    (h : ChebotarevRangeInequality K (fun n => (2 : ℝ) ^ S n) degree discLog) :
    ChebotarevExponentCondition K S degree discLog := by
  intro n
  have hn := h n
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hn
  simpa [mul_comm] using hn

/-- **The smallest range input.**  Positivity of `K` and the logarithmic
inequality. -/
structure ChebotarevRangeInput (K : ℝ) (x degree discLog : ℕ → ℝ) : Prop where
  /-- The range constant is positive. -/
  K_pos : 0 < K
  /-- The logarithmic range inequality. -/
  range : ChebotarevRangeInequality K x degree discLog

/-- The smallest range input rebuilds the paper-level range condition. -/
theorem ChebotarevRangeInput.toEffectiveChebotarevRange {K : ℝ} {x degree discLog : ℕ → ℝ}
    (R : ChebotarevRangeInput K x degree discLog) :
    EffectiveChebotarevRange K x degree discLog :=
  effectiveChebotarevRange_of_inequality R.K_pos R.range

/-- The paper-level range condition gives the smallest range input. -/
theorem ChebotarevRangeInput.ofEffective {K : ℝ} {x degree discLog : ℕ → ℝ}
    (h : EffectiveChebotarevRange K x degree discLog) :
    ChebotarevRangeInput K x degree discLog where
  K_pos := h.1
  range := chebotarevRangeInequality_of_effective h

/-! ## 4. The cumulative Chebotarev count -/

/-- **The two sides of the cumulative count.**  This is the smallest
two-sided form: the lower and upper inequalities are kept separately because
the L34 ledger only uses the lower side, while the upper side is needed to
rebuild the paper-level `EffectiveChebotarev`. -/
structure ChebotarevSides (count main error : ℕ → ℝ) : Prop where
  /-- `main - error ≤ count`. -/
  lower : ChebotarevLowerBound count main error
  /-- `count ≤ main + error`. -/
  upper : ChebotarevUpperBound count main error

/-- **The two sides are equivalent to the absolute-value count.** -/
theorem chebotarevSides_iff_effective {count main error : ℕ → ℝ} :
    ChebotarevSides count main error ↔ EffectiveChebotarev count main error :=
  ⟨fun h => effectiveChebotarev_of_sides h.lower h.upper,
    fun h => ⟨chebotarevLowerBound_of_effective h,
      chebotarevUpperBound_of_effective h⟩⟩

/-- The two-sided count gives the two sides. -/
theorem chebotarevSides_of_effective {count main error : ℕ → ℝ}
    (h : EffectiveChebotarev count main error) :
    ChebotarevSides count main error :=
  chebotarevSides_iff_effective.mpr h

/-- The two sides give the two-sided count. -/
theorem effectiveChebotarev_of_chebotarevSides {count main error : ℕ → ℝ}
    (h : ChebotarevSides count main error) :
    EffectiveChebotarev count main error :=
  chebotarevSides_iff_effective.mp h

/-- **The cumulative count with a slack error.**  Instead of requiring the
error to be *exactly* the Lagarias–Odlyzko expression, it suffices that some
nonnegative error `err` is bounded by it and that `count` is within `err` of
`main`.  This is the smallest form of the counting input: it is implied by the
exact-error statement and implies both sides. -/
structure ChebotarevErrorSlack (C cZ : ℝ) (x degree : ℕ → ℝ)
    (count main : ℕ → ℝ) : Prop where
  /-- The error constant is positive. -/
  C_pos : 0 < C
  /-- The error exponent is positive. -/
  cZ_pos : 0 < cZ
  /-- Some nonnegative error sequence is bounded by the explicit error and
  captures the count's deviation from the main term. -/
  exists_err : ∃ err : ℕ → ℝ,
    (∀ n, 0 ≤ err n) ∧
    (∀ n, err n ≤ lagariasOdlyzkoError C cZ x degree n) ∧
    (∀ n, |count n - main n| ≤ err n)

/-- A slack Chebotarev error gives the lower side of the count. -/
theorem ChebotarevErrorSlack.lower {C cZ : ℝ} {x degree count main : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count main) :
    ChebotarevLowerBound count main (lagariasOdlyzkoError C cZ x degree) := by
  intro n
  obtain ⟨err, _, hle, hclose⟩ := E.exists_err
  have hlow := (abs_le.mp (hclose n)).1
  have hlee := hle n
  linarith

/-- A slack Chebotarev error gives the upper side of the count. -/
theorem ChebotarevErrorSlack.upper {C cZ : ℝ} {x degree count main : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count main) :
    ChebotarevUpperBound count main (lagariasOdlyzkoError C cZ x degree) := by
  intro n
  obtain ⟨err, _, hle, hclose⟩ := E.exists_err
  have hhigh := (abs_le.mp (hclose n)).2
  have hlee := hle n
  linarith

/-- A slack Chebotarev error gives the two-sided count. -/
theorem ChebotarevErrorSlack.toEffectiveChebotarev {C cZ : ℝ}
    {x degree count main : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count main) :
    EffectiveChebotarev count main (lagariasOdlyzkoError C cZ x degree) :=
  effectiveChebotarev_of_sides E.lower E.upper

/-- The exact-error statement is a special case of the slack statement. -/
theorem ChebotarevErrorSlack.ofExact {C cZ : ℝ} (hC : 0 < C) (hcZ : 0 < cZ)
    {x degree count main : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n)
    (h : EffectiveChebotarev count main (lagariasOdlyzkoError C cZ x degree)) :
    ChebotarevErrorSlack C cZ x degree count main where
  C_pos := hC
  cZ_pos := hcZ
  exists_err :=
    ⟨lagariasOdlyzkoError C cZ x degree,
      lagariasOdlyzkoError_nonneg hC.le hx,
      fun _ => le_rfl,
      h⟩

/-- **The smallest count input.**  The two sides of the cumulative count for
the explicit main term and the explicit Lagarias–Odlyzko error. -/
structure ChebotarevCountInput (C cZ : ℝ) (x degree : ℕ → ℝ)
    (count liX liBeta0 : ℕ → ℝ) : Prop where
  /-- The error constant is positive. -/
  C_pos : 0 < C
  /-- The error exponent is positive. -/
  cZ_pos : 0 < cZ
  /-- `main - error ≤ count`. -/
  lower : ChebotarevLowerBound count (mainOf liX liBeta0)
    (lagariasOdlyzkoError C cZ x degree)
  /-- `count ≤ main + error`. -/
  upper : ChebotarevUpperBound count (mainOf liX liBeta0)
    (lagariasOdlyzkoError C cZ x degree)

/-- The smallest count input rebuilds the paper-level cumulative count. -/
theorem ChebotarevCountInput.toEffectiveChebotarev {C cZ : ℝ} {x degree : ℕ → ℝ}
    {count liX liBeta0 : ℕ → ℝ}
    (Q : ChebotarevCountInput C cZ x degree count liX liBeta0) :
    EffectiveChebotarev count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree) :=
  effectiveChebotarev_of_sides Q.lower Q.upper

/-- A slack error descending from a two-sided count yields the smallest count
input. -/
theorem ChebotarevCountInput.ofSlack {C cZ : ℝ} {x degree count liX liBeta0 : ℕ → ℝ}
    (E : ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0)) :
    ChebotarevCountInput C cZ x degree count liX liBeta0 where
  C_pos := E.C_pos
  cZ_pos := E.cZ_pos
  lower := E.lower
  upper := E.upper

/-- The paper-level cumulative count, together with the positivity of its two
constants, gives the smallest count input. -/
theorem ChebotarevCountInput.ofEffective {C cZ : ℝ} (hC : 0 < C) (hcZ : 0 < cZ)
    {x degree count liX liBeta0 : ℕ → ℝ}
    (h : EffectiveChebotarev count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    ChebotarevCountInput C cZ x degree count liX liBeta0 where
  C_pos := hC
  cZ_pos := hcZ
  lower := chebotarevLowerBound_of_effective h
  upper := chebotarevUpperBound_of_effective h

/-! ## 5. The assembled small analytic bundle -/

/-- **The reduced Dedekind/Stark/Chebotarev inputs.**  Four independent
smallest sub-`Prop`s: the zero-free region, Stark's gap, the range inequality,
and the two sides of the cumulative count.  Every field is a single explicit
inequality with its positivity constant, and no field mentions the error
function (it is reconstructed definitionally by `lagariasOdlyzkoError`). -/
structure DedekindAnalyticInputs
    (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ)
    (F : ℕ → ℝ) (K : ℝ) (x degree : ℕ → ℝ)
    (C cZ : ℝ) (count : ℕ → ℝ) (liX liBeta0 : ℕ → ℝ) : Prop where
  /-- The Dedekind zero-free region in its smallest form. -/
  zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog
  /-- Stark's exceptional-zero gap. -/
  stark : StarkInput beta0 F discLog
  /-- The Lagarias–Odlyzko range inequality. -/
  range : ChebotarevRangeInput K x degree discLog
  /-- The cumulative Chebotarev count, two-sided. -/
  cheb : ChebotarevCountInput C cZ x degree count liX liBeta0

/-- **The small bundle implies `AnalyticSubProps`.**  This is the reduction
step: each smallest sub-`Prop` is converted to the corresponding core field of
`Cogentic.RandomizedL34Analytic.AnalyticSubProps`. -/
theorem DedekindAnalyticInputs.toAnalyticSubProps
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    AnalyticSubProps beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  cz_pos := A.zeroFree.cz_pos
  zero_free := dedekindZeroFreeCore_of_aboveBeta A.zeroFree.above_beta
  stark_gap := A.stark.gap
  K_pos := A.range.K_pos
  range := A.range.range
  C_pos := A.cheb.C_pos
  cZ_pos := A.cheb.cZ_pos
  cheb_lower := A.cheb.lower
  cheb_upper := A.cheb.upper

/-- **Assemble the small bundle from the four independent sub-`Prop`s and a
slack Chebotarev error.**  No exact-error equation is needed. -/
theorem DedekindAnalyticInputs.ofSlack
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (Z : DedekindZeroFreeInput beta0 zeroRealPart cz discLog)
    (St : StarkInput beta0 F discLog)
    (R : ChebotarevRangeInput K x degree discLog)
    (E : ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  zeroFree := Z
  stark := St
  range := R
  cheb := ChebotarevCountInput.ofSlack E

/-- **The paper's `x = 2^S` specialization.**  The range condition is replaced
by the exponent inequality, and the count by a slack error.  This is the
smallest concrete bundle matching the manuscript's choice of cutoff. -/
theorem DedekindAnalyticInputs.ofRpowTwo
    {beta0 zeroRealPart discLog F degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ} {S : ℕ → ℝ}
    (Z : DedekindZeroFreeInput beta0 zeroRealPart cz discLog)
    (St : StarkInput beta0 F discLog)
    (hK : 0 < K) (hExp : ChebotarevExponentCondition K S degree discLog)
    (E : ChebotarevErrorSlack C cZ (fun n => (2 : ℝ) ^ S n) degree count
      (mainOf liX liBeta0)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K
      (fun n => (2 : ℝ) ^ S n) degree C cZ count liX liBeta0 where
  zeroFree := Z
  stark := St
  range :=
    { K_pos := hK
      range := chebotarevRangeInequality_rpow_two hExp }
  cheb := ChebotarevCountInput.ofSlack E

/-- **`AnalyticSubProps` gives the small bundle.**  Together with
`DedekindAnalyticInputs.toAnalyticSubProps` this shows that the rewrite is
lossless: the small bundle is exactly the analytic content of the existing
reduced bundle. -/
theorem AnalyticSubProps.toDedekindAnalyticInputs
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : AnalyticSubProps beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  zeroFree :=
    { cz_pos := A.cz_pos
      above_beta := dedekindZeroFreeAboveBeta_of_core A.zero_free }
  stark := { gap := A.stark_gap }
  range := { K_pos := A.K_pos, range := A.range }
  cheb :=
    { C_pos := A.C_pos
      cZ_pos := A.cZ_pos
      lower := A.cheb_lower
      upper := A.cheb_upper }

/-- **Equivalence of the small and the reduced analytic bundles.** -/
theorem dedekindAnalyticInputs_iff_analyticSubProps
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ} :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
        liX liBeta0 ↔
      AnalyticSubProps beta0 zeroRealPart cz discLog F K x degree C cZ count
        liX liBeta0 :=
  ⟨fun A => A.toAnalyticSubProps,
    fun A => AnalyticSubProps.toDedekindAnalyticInputs A⟩

/-- The small bundle implies the five paper-level `Prop`s of
`PaperLevelInputs`. -/
theorem DedekindAnalyticInputs.toPaperLevel
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0)
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n) :
    PaperLevelInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      (lagariasOdlyzkoError C cZ x degree) count (mainOf liX liBeta0) :=
  A.toAnalyticSubProps.toPaperLevel hF hD

/-- The small bundle gives the paper-level Dedekind zero-free region. -/
theorem DedekindAnalyticInputs.dedekindZeroFreeRegion
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    DedekindZeroFreeRegion beta0 zeroRealPart cz discLog :=
  A.zeroFree.toDedekindZeroFreeRegion

/-- The small bundle gives Stark's paper-level exceptional-zero bound. -/
theorem DedekindAnalyticInputs.starkExceptionalZeroBound
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0)
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n) :
    StarkExceptionalZeroBound beta0 F discLog :=
  A.stark.toStarkExceptionalZeroBound hF hD

/-- The small bundle gives the paper-level range condition. -/
theorem DedekindAnalyticInputs.effectiveChebotarevRange
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    EffectiveChebotarevRange K x degree discLog :=
  A.range.toEffectiveChebotarevRange

/-- The small bundle gives the two-sided paper-level Chebotarev count. -/
theorem DedekindAnalyticInputs.effectiveChebotarev
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    EffectiveChebotarev count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree) :=
  A.cheb.toEffectiveChebotarev

/-- The small bundle gives the lower side of the cumulative count. -/
theorem DedekindAnalyticInputs.chebotarevLowerBound
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    ChebotarevLowerBound count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree) :=
  A.cheb.lower

/-- The small bundle gives the upper side of the cumulative count. -/
theorem DedekindAnalyticInputs.chebotarevUpperBound
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    ChebotarevUpperBound count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree) :=
  A.cheb.upper

/-! ## 6. The reduction to `L34AnalyticCore` -/

/-- **`L34AnalyticCore` with the `sub` field replaced by the small
Dedekind/Stark/Chebotarev bundle.**  All data and all non-analytic bookkeeping
fields are exactly those of `Cogentic.RandomizedL34Analytic.L34AnalyticCore`;
only `sub` has been replaced by `dedekind`. -/
structure L34DedekindCore where
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
  /-- The cumulative inert count. -/
  inertCount : ℕ → ℝ
  /-- The degree-one inert count after discarding small / higher-degree ideals. -/
  degreeOneInert : ℕ → ℝ
  /-- `Li x`. -/
  liX : ℕ → ℝ
  /-- `Li x^{β₀}`. -/
  liBeta0 : ℕ → ℝ
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
  /-- **The small Dedekind/Stark/Chebotarev bundle.** -/
  dedekind : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree
    C cZ count liX liBeta0
  /-- The inert count contains the counted nonidentity class. -/
  inert_ge_count : ∀ n, count n ≤ inertCount n
  /-- Stark's bound converted to the dyadic bracket. -/
  bracket : LogIntegralBracket cbr x F T liX liBeta0
  /-- The Chebotarev error is negligible against the bracket. -/
  error_negligible : ChebotarevErrorNegligible cbr x F T
    (lagariasOdlyzkoError C cZ x degree)
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

namespace L34DedekindCore

/-- **The reduction to `L34AnalyticCore`.**  The small bundle is converted to
`AnalyticSubProps`, and every other field is copied verbatim. -/
def toL34AnalyticCore (S : L34DedekindCore) : L34AnalyticCore where
  x := S.x
  degree := S.degree
  discLog := S.discLog
  F := S.F
  T := S.T
  hstar := S.hstar
  m := S.m
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
  x_pos := S.x_pos
  degree_pos := S.degree_pos
  discLog_pos := S.discLog_pos
  F_pos := S.F_pos
  T_pos := S.T_pos
  T_ge_one := S.T_ge_one
  classCount_pos := S.classCount_pos
  pTrial_nonneg := S.pTrial_nonneg
  pTrial_le_one := S.pTrial_le_one
  actualMiss := S.actualMiss
  actualMiss_nonneg := S.actualMiss_nonneg
  union_bound := S.union_bound
  degree_le_T := S.degree_le_T
  sub := S.dedekind.toAnalyticSubProps
  inert_ge_count := S.inert_ge_count
  bracket := S.bracket
  error_negligible := S.error_negligible
  degree_one_loss := S.degree_one_loss
  degree_one_reduction := S.degree_one_reduction
  selection := S.selection
  budget := S.budget
  class_le := S.class_le
  hstar_poly := S.hstar_poly
  mask_bits := S.mask_bits
  constant_margin := S.constant_margin
  scale_cubic := S.scale_cubic

/-- The rebuilt full bundle of `EffectiveChebotarevInputs`. -/
def toEffectiveChebotarevInputs (S : L34DedekindCore) : EffectiveChebotarevInputs :=
  S.toL34AnalyticCore.toEffectiveChebotarevInputs

/-- The rebuilt bundle carries exactly the five paper-level `Prop`s. -/
theorem toPaperLevel (S : L34DedekindCore) :
    PaperLevelInputs S.beta0 S.zeroRealPart S.cz S.discLog S.F S.K S.x S.degree
      S.C S.cZ (lagariasOdlyzkoError S.C S.cZ S.x S.degree) S.count
      (mainOf S.liX S.liBeta0) :=
  S.toL34AnalyticCore.toPaperLevel

/-- The L34 probe miss bound for the rebuilt bundle. -/
theorem probeMiss_le_ledger (S : L34DedekindCore) :
    ∀ᶠ n : ℕ in atTop,
      probeMiss S.classCount S.pTrial S.R n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toL34AnalyticCore.probeMiss_le_ledger

/-- The L34 ledger slot for the rebuilt bundle. -/
theorem loss_le_ledger (S : L34DedekindCore) :
    ∀ᶠ n : ℕ in atTop,
      S.toEffectiveChebotarevInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toL34AnalyticCore.loss_le_ledger

/-- The manuscript's slower `exp (-H / log H)` rate for the rebuilt bundle. -/
theorem loss_le_paper (S : L34DedekindCore) :
    ∀ᶠ n : ℕ in atTop,
      S.toEffectiveChebotarevInputs.loss n ≤ exp (-(1 * paperRate n)) :=
  S.toL34AnalyticCore.loss_le_paper

/-- The literal `RatedLeaf` of the rebuilt bundle. -/
def ratedLeaf (S : L34DedekindCore) : Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  S.toL34AnalyticCore.ratedLeaf

end L34DedekindCore

/-! ## Axiom audit -/

#print axioms dedekindZeroFreeCore_iff_aboveBeta
#print axioms dedekindZeroFreeCore_iff_max
#print axioms dedekindZeroFreeMax_of_core
#print axioms DedekindZeroFreeInput.toDedekindZeroFreeRegion
#print axioms DedekindZeroFreeInput.ofRegion
#print axioms starkGap_iff_betaUpper
#print axioms StarkInput.toStarkExceptionalZeroBound
#print axioms StarkInput.ofBound
#print axioms chebotarevRangeInequality_iff_threshold
#print axioms chebotarevRangeInequality_rpow_two
#print axioms chebotarevExponentCondition_of_rpow_two
#print axioms ChebotarevRangeInput.toEffectiveChebotarevRange
#print axioms ChebotarevRangeInput.ofEffective
#print axioms chebotarevSides_iff_effective
#print axioms effectiveChebotarev_of_chebotarevSides
#print axioms ChebotarevErrorSlack.lower
#print axioms ChebotarevErrorSlack.upper
#print axioms ChebotarevErrorSlack.toEffectiveChebotarev
#print axioms ChebotarevErrorSlack.ofExact
#print axioms ChebotarevCountInput.toEffectiveChebotarev
#print axioms ChebotarevCountInput.ofSlack
#print axioms ChebotarevCountInput.ofEffective
#print axioms DedekindAnalyticInputs.ofSlack
#print axioms DedekindAnalyticInputs.ofRpowTwo
#print axioms DedekindAnalyticInputs.toAnalyticSubProps
#print axioms AnalyticSubProps.toDedekindAnalyticInputs
#print axioms dedekindAnalyticInputs_iff_analyticSubProps
#print axioms DedekindAnalyticInputs.toPaperLevel
#print axioms DedekindAnalyticInputs.dedekindZeroFreeRegion
#print axioms DedekindAnalyticInputs.starkExceptionalZeroBound
#print axioms DedekindAnalyticInputs.effectiveChebotarevRange
#print axioms DedekindAnalyticInputs.effectiveChebotarev
#print axioms DedekindAnalyticInputs.chebotarevLowerBound
#print axioms DedekindAnalyticInputs.chebotarevUpperBound
#print axioms L34DedekindCore.toL34AnalyticCore
#print axioms L34DedekindCore.toEffectiveChebotarevInputs
#print axioms L34DedekindCore.toPaperLevel
#print axioms L34DedekindCore.probeMiss_le_ledger
#print axioms L34DedekindCore.loss_le_ledger
#print axioms L34DedekindCore.loss_le_paper
#print axioms L34DedekindCore.ratedLeaf

end

end Cogentic.RandomizedL34Dedekind
