import Cogentic.RandomizedL34Sub

/-!
# L34: the analytic reduction of the five paper-level inputs

`Cogentic.RandomizedL34Sub.PaperLevelInputs` bundles five paper-level analytic
`Prop`s:

1. `DedekindZeroFreeRegion` (Lagarias–Odlyzko Theorem 1.3, zero-free form);
2. `StarkExceptionalZeroBound` (Stark's exceptional-zero lemma);
3. `EffectiveChebotarevRange` (the range condition of Theorem 1.3);
4. `LagariasOdlyzkoError` (the explicit error of Theorem 1.3);
5. `EffectiveChebotarev` (the cumulative count of Theorem 1.3).

This file reduces those five to the smallest explicit analytic content that the
L34 ledger actually consumes, and proves the reduction to the full
`EffectiveChebotarevInputs` bundle.  Nothing here proves a theorem of analytic
number theory; the genuinely analytic statements remain explicit hypotheses.

## What is reduced, and how

* **The error (4) is not an analytic input at all.**  `LagariasOdlyzkoError C c x
  degree error` is the single equation
  `error n = C * x n * exp (-(c * sqrt (log (x n) / (2 * degree n))))`.  The
  explicit function `lagariasOdlyzkoError C c x degree` is defined below, the
  `Prop` is *proved* for it from `0 < C`, `0 < c`
  (`lagariasOdlyzkoError_spec`), and any function satisfying the `Prop` is
  *equal* to it (`lagariasOdlyzkoError_unique`).  The error is therefore removed
  from the hypothesis list and reconstructed definitionally in
  `L34AnalyticCore.toEffectiveChebotarevInputs`.

* **The main term is definitional.**  The paper's main term is
  `main = (1/2) (Li x - Li x^{β₀})`; `mainOf liX liBeta0` is exactly that
  function, so `EffectiveChebotarevInputs.main_eq` becomes `rfl`.

* **The positivity conjuncts of (1)-(3) are arithmetic.**  `DedekindZeroFreeRegion`
  is `0 < cz ∧ …`, `StarkExceptionalZeroBound` is `∀ n, 0 < 4 F n discLog n ∧ …`,
  and `EffectiveChebotarevRange` is `0 < K ∧ …`.  The positivity halves follow
  from `cz > 0`, `F > 0`, `discLog > 0` and `K > 0`
  (`dedekindZeroFreeRegion_of_core`, `starkExceptionalZeroBound_of_gap`,
  `effectiveChebotarevRange_of_inequality`).  Only the inequalities
  `DedekindZeroFreeCore`, `StarkGap`, `ChebotarevRangeInequality` remain.

* **The cumulative count (5) is split into its two one-sided inequalities**
  `ChebotarevLowerBound` and `ChebotarevUpperBound`
  (`effectiveChebotarev_of_sides`).  The L34 chain itself only uses the lower
  side (see `inert_lower` in `Cogentic.RandomizedL34`); the upper side is kept
  so that the full two-sided `EffectiveChebotarev` field can be rebuilt without
  loss.

The resulting reduced bundle is `AnalyticSubProps`.  Its only non-elementary
fields are `zero_free` (the Dedekind zero-free region), `stark_gap` (Stark's
bound), `range` (the Chebotarev range condition), and the two sides of the
cumulative count.  This repository does not contain a formal proof of any of
these four: Mathlib has no Chebotarev or Dedekind-zeta zero theory, and the
character/prime-count estimates in `Cogentic.Window.CharacterEstimate` /
`Cogentic.Window.PrimeCount` concern Dirichlet characters on the critical line,
not the Dedekind zeta function of the absolute field `E = K(sqrt γ)`.  They are
therefore kept as the smallest explicit `Prop`s, not silently assumed.

## The reduction

`L34AnalyticCore` keeps all the data and all the non-analytic bookkeeping fields
of `EffectiveChebotarevInputs`, replaces `main` and `error` by their explicit
definitions, removes `main_eq` and the five paper-level `Prop`s, and carries
`AnalyticSubProps` plus the remaining elementary fields.  The theorem
`L34AnalyticCore.toEffectiveChebotarevInputs` rebuilds the full bundle, and
`L34AnalyticCore.probeMiss_le_ledger` / `loss_le_ledger` re-export the existing
L34 ledger bound for the rebuilt bundle.

No `sorry`, `admit`, `axiom`, or `native_decide`.  No loss, mass, count, or error
is set to zero.
-/

namespace Cogentic.RandomizedL34Analytic

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The explicit main term and Lagarias–Odlyzko error -/

/-- The Chebotarev main term `½ (Li x - Li x^{β₀})`, as the manuscript defines
it.  Keeping it a definition removes the `main_eq` field from the input list. -/
def mainOf (liX liBeta0 : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / 2) * (liX n - liBeta0 n)

/-- The explicit Lagarias–Odlyzko error
`C x exp (-c sqrt (log x / (2d)))` of Theorem 1.3.  This is the value the
`LagariasOdlyzkoError` `Prop` prescribes; the `Prop` is proved for it below. -/
def lagariasOdlyzkoError (C c : ℝ) (x degree : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * x n * Real.exp (-(c * Real.sqrt (Real.log (x n) / (2 * degree n))))

/-- **The error `Prop` is satisfied by its own defining expression.**  The only
hypotheses are the positivity of the two constants. -/
theorem lagariasOdlyzkoError_spec {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (x degree : ℕ → ℝ) :
    LagariasOdlyzkoError C c x degree (lagariasOdlyzkoError C c x degree) :=
  ⟨hC, hc, fun _ => rfl⟩

/-- **The error `Prop` determines the function.**  Any `error` satisfying
`LagariasOdlyzkoError C c x degree` equals the explicit expression.  Hence the
`Prop` carries no analytic content beyond the definition of the error. -/
theorem lagariasOdlyzkoError_unique {C c : ℝ} {x degree error : ℕ → ℝ}
    (h : LagariasOdlyzkoError C c x degree error) :
    error = lagariasOdlyzkoError C c x degree := by
  funext n
  simpa [lagariasOdlyzkoError] using h.2.2 n

/-- The explicit error is nonnegative when `C ≥ 0` and `x ≥ 0`. -/
theorem lagariasOdlyzkoError_nonneg {C c : ℝ} {x degree : ℕ → ℝ}
    (hC : 0 ≤ C) (hx : ∀ n, 0 ≤ x n) (n : ℕ) :
    0 ≤ lagariasOdlyzkoError C c x degree n := by
  unfold lagariasOdlyzkoError
  exact mul_nonneg (mul_nonneg hC (hx n)) (Real.exp_pos _).le

/-- The explicit error is positive when `C > 0` and `x > 0`. -/
theorem lagariasOdlyzkoError_pos {C c : ℝ} {x degree : ℕ → ℝ}
    (hC : 0 < C) (hx : ∀ n, 0 < x n) (n : ℕ) :
    0 < lagariasOdlyzkoError C c x degree n := by
  unfold lagariasOdlyzkoError
  exact mul_pos (mul_pos hC (hx n)) (Real.exp_pos _)

/-! ## 2. The four reduced analytic sub-`Prop`s -/

/-- **The Dedekind zero-free region, core inequality.**  This is
`DedekindZeroFreeRegion` with the `0 < cz` conjunct removed: any zero of `ζ_E`
whose real part exceeds `1 - c_z / log |Δ_E|` is the exceptional zero `β₀`. -/
def DedekindZeroFreeCore (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, 1 - cz / discLog n < zeroRealPart n → zeroRealPart n ≤ beta0 n

/-- **Stark's exceptional-zero bound, core inequality.**  This is
`StarkExceptionalZeroBound` with the positivity conjunct removed:
`1 - β₀ ≥ (4 F log |Δ_E|)⁻¹`. -/
def StarkGap (beta0 F discLog : ℕ → ℝ) : Prop :=
  ∀ n, 1 / (4 * F n * discLog n) ≤ 1 - beta0 n

/-- **The range condition, core inequality.**  This is
`EffectiveChebotarevRange` with the `0 < K` conjunct removed:
`K d (log |Δ_E|)² ≤ log x`. -/
def ChebotarevRangeInequality (K : ℝ) (x degree discLog : ℕ → ℝ) : Prop :=
  ∀ n, K * degree n * (discLog n) ^ 2 ≤ Real.log (x n)

/-- The lower side of the cumulative Chebotarev count:
`main - error ≤ count`.  This is the only side used by the L34 ledger. -/
def ChebotarevLowerBound (count main error : ℕ → ℝ) : Prop :=
  ∀ n, main n - error n ≤ count n

/-- The upper side of the cumulative Chebotarev count: `count ≤ main + error`. -/
def ChebotarevUpperBound (count main error : ℕ → ℝ) : Prop :=
  ∀ n, count n ≤ main n + error n

/-! ### 2.1 Rebuilding the paper-level `Prop`s -/

/-- The zero-free region follows from `cz > 0` and the core inequality. -/
theorem dedekindZeroFreeRegion_of_core {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ}
    {discLog : ℕ → ℝ} (hcz : 0 < cz)
    (h : DedekindZeroFreeCore beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeRegion beta0 zeroRealPart cz discLog :=
  ⟨hcz, h⟩

/-- The converse split: a zero-free region gives its positivity and core. -/
theorem dedekindZeroFreeRegion_core {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ}
    {discLog : ℕ → ℝ} (h : DedekindZeroFreeRegion beta0 zeroRealPart cz discLog) :
    0 < cz ∧ DedekindZeroFreeCore beta0 zeroRealPart cz discLog :=
  ⟨h.1, h.2⟩

/-- **The exceptional-zero bound follows from positivity and Stark's gap.** -/
theorem starkExceptionalZeroBound_of_gap {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (h : StarkGap beta0 F discLog) :
    StarkExceptionalZeroBound beta0 F discLog := by
  intro n
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hpos : 0 < 4 * F n * discLog n :=
    mul_pos (mul_pos h4 (hF n)) (hD n)
  exact ⟨hpos, h n⟩

/-- The converse split: the paper-level bound gives Stark's gap. -/
theorem starkGap_of_starkExceptionalZeroBound {beta0 F discLog : ℕ → ℝ}
    (h : StarkExceptionalZeroBound beta0 F discLog) :
    StarkGap beta0 F discLog :=
  fun n => (h n).2

/-- **The range condition follows from `K > 0` and the core inequality.** -/
theorem effectiveChebotarevRange_of_inequality {K : ℝ} {x degree discLog : ℕ → ℝ}
    (hK : 0 < K) (h : ChebotarevRangeInequality K x degree discLog) :
    EffectiveChebotarevRange K x degree discLog :=
  ⟨hK, h⟩

/-- The converse split: the paper-level range condition gives the inequality. -/
theorem chebotarevRangeInequality_of_effective {K : ℝ} {x degree discLog : ℕ → ℝ}
    (h : EffectiveChebotarevRange K x degree discLog) :
    ChebotarevRangeInequality K x degree discLog :=
  h.2

/-- The two-sided cumulative count implies its lower side. -/
theorem chebotarevLowerBound_of_effective {count main error : ℕ → ℝ}
    (h : EffectiveChebotarev count main error) :
    ChebotarevLowerBound count main error := by
  intro n
  have hlow := (abs_le.mp (h n)).1
  linarith

/-- The two-sided cumulative count implies its upper side. -/
theorem chebotarevUpperBound_of_effective {count main error : ℕ → ℝ}
    (h : EffectiveChebotarev count main error) :
    ChebotarevUpperBound count main error := by
  intro n
  have hhigh := (abs_le.mp (h n)).2
  linarith

/-- **The two one-sided inequalities rebuild the paper-level cumulative
count.** -/
theorem effectiveChebotarev_of_sides {count main error : ℕ → ℝ}
    (hlow : ChebotarevLowerBound count main error)
    (hhigh : ChebotarevUpperBound count main error) :
    EffectiveChebotarev count main error := by
  intro n
  rw [abs_le]
  constructor <;> linarith [hlow n, hhigh n]

/-! ### 2.2 Elementary consequences used in the paper's chain -/

/-- Stark's gap is strictly positive. -/
theorem starkGap_pos {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (h : StarkGap beta0 F discLog) (n : ℕ) :
    0 < 1 - beta0 n := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hpos : 0 < 4 * F n * discLog n :=
    mul_pos (mul_pos h4 (hF n)) (hD n)
  exact lt_of_lt_of_le (one_div_pos.mpr hpos) (h n)

/-- **The exceptional zero is strictly below one.**  This is the consequence of
Stark's bound that lets the logarithmic-integral bracket be positive. -/
theorem starkGap_beta0_lt_one {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (h : StarkGap beta0 F discLog) (n : ℕ) :
    beta0 n < 1 := by
  have := starkGap_pos hF hD h n
  linarith

/-- **Dichotomy form of the zero-free region.**  Every zero is either the
exceptional zero `β₀` or lies on the zero-free side of the line
`1 - c_z / log |Δ_E|`.  This is the form used when the paper rules out
nonexceptional zeros near `1`. -/
theorem dedekindZeroFreeCore_dichotomy {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ}
    {discLog : ℕ → ℝ} (h : DedekindZeroFreeCore beta0 zeroRealPart cz discLog)
    (n : ℕ) :
    zeroRealPart n ≤ max (beta0 n) (1 - cz / discLog n) := by
  by_cases hle : zeroRealPart n ≤ 1 - cz / discLog n
  · exact hle.trans (le_max_right _ _)
  · have hlt : 1 - cz / discLog n < zeroRealPart n := lt_of_not_ge hle
    exact (h n hlt).trans (le_max_left _ _)

/-- The range inequality makes `log x` strictly positive. -/
theorem range_log_pos {K : ℝ} {x degree discLog : ℕ → ℝ}
    (hK : 0 < K) (hd : ∀ n, 0 < degree n) (hD : ∀ n, 0 < discLog n)
    (h : ChebotarevRangeInequality K x degree discLog) (n : ℕ) :
    0 < Real.log (x n) := by
  have hdeg : 0 < K * degree n := mul_pos hK (hd n)
  have hsq : 0 < (discLog n) ^ 2 := pow_pos (hD n) 2
  exact lt_of_lt_of_le (mul_pos hdeg hsq) (h n)

/-! ## 3. The smallest explicit analytic bundle -/

/-- **The reduced analytic inputs.**  These are the four genuinely analytic
statements consumed by L34, with every definitional and positivity conjunct
removed:

* `zero_free` — the Dedekind zero-free region away from `β₀`;
* `stark_gap` — Stark's bound `1 - β₀ ≥ (4 F log |Δ_E|)⁻¹`;
* `range` — the Lagarias–Odlyzko range condition `K d (log |Δ_E|)² ≤ log x`;
* `cheb_lower`, `cheb_upper` — the two sides of the cumulative Chebotarev count.

The constants are `cz`, `K`, `C`, `cZ`; the main term and error are the explicit
functions `mainOf` and `lagariasOdlyzkoError`, so no error equation appears. -/
structure AnalyticSubProps
    (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ)
    (F : ℕ → ℝ) (K : ℝ) (x degree : ℕ → ℝ)
    (C cZ : ℝ) (count : ℕ → ℝ) (liX liBeta0 : ℕ → ℝ) : Prop where
  /-- The zero-free-region constant is positive. -/
  cz_pos : 0 < cz
  /-- Lagarias–Odlyzko: the Dedekind zero-free region, core inequality. -/
  zero_free : DedekindZeroFreeCore beta0 zeroRealPart cz discLog
  /-- Stark: the exceptional real zero is bounded away from `1`. -/
  stark_gap : StarkGap beta0 F discLog
  /-- The range constant is positive. -/
  K_pos : 0 < K
  /-- Lagarias–Odlyzko: the range inequality. -/
  range : ChebotarevRangeInequality K x degree discLog
  /-- The error constant is positive. -/
  C_pos : 0 < C
  /-- The error exponent is positive. -/
  cZ_pos : 0 < cZ
  /-- The cumulative count lies above its main term minus the error. -/
  cheb_lower : ChebotarevLowerBound count (mainOf liX liBeta0)
    (lagariasOdlyzkoError C cZ x degree)
  /-- The cumulative count lies below its main term plus the error. -/
  cheb_upper : ChebotarevUpperBound count (mainOf liX liBeta0)
    (lagariasOdlyzkoError C cZ x degree)

/-- **The reduced bundle implies all five paper-level `Prop`s.**  The only extra
hypotheses are the positivity of `F` and `log |Δ_E|` needed to turn Stark's gap
into the paper's conjunction. -/
theorem AnalyticSubProps.toPaperLevel
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : AnalyticSubProps beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0)
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n) :
    PaperLevelInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      (lagariasOdlyzkoError C cZ x degree) count (mainOf liX liBeta0) where
  zeroFree := dedekindZeroFreeRegion_of_core A.cz_pos A.zero_free
  stark := starkExceptionalZeroBound_of_gap hF hD A.stark_gap
  chebRange := effectiveChebotarevRange_of_inequality A.K_pos A.range
  chebError := lagariasOdlyzkoError_spec A.C_pos A.cZ_pos x degree
  chebCount := effectiveChebotarev_of_sides A.cheb_lower A.cheb_upper

/-- **The reduction is lossless.**  Conversely, the five paper-level `Prop`s
(with `main` and `error` fixed to their explicit definitions) rebuild the
reduced analytic bundle.  Together with `AnalyticSubProps.toPaperLevel` this
shows that `AnalyticSubProps` is exactly the analytic content of
`PaperLevelInputs`, with only the definitional and positivity conjuncts split
off. -/
theorem AnalyticSubProps.ofPaperLevel
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (P : PaperLevelInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      (lagariasOdlyzkoError C cZ x degree) count (mainOf liX liBeta0)) :
    AnalyticSubProps beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  cz_pos := P.zeroFree.1
  zero_free := P.zeroFree.2
  stark_gap := starkGap_of_starkExceptionalZeroBound P.stark
  K_pos := P.chebRange.1
  range := chebotarevRangeInequality_of_effective P.chebRange
  C_pos := P.chebError.1
  cZ_pos := P.chebError.2.1
  cheb_lower := chebotarevLowerBound_of_effective P.chebCount
  cheb_upper := chebotarevUpperBound_of_effective P.chebCount

/-- **Equivalence of the reduced and paper-level analytic inputs.**  Given the
positivity of `F` and `log |Δ_E|`, the reduced bundle and the five paper-level
`Prop`s (with explicit `main` and `error`) are inter-derivable.  Hence the
reduction neither weakens nor strengthens the analytic assumptions; it only
removes the definitional error equation and the positivity conjuncts. -/
theorem analyticSubProps_iff_paperLevel
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ} (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n) :
    AnalyticSubProps beta0 zeroRealPart cz discLog F K x degree C cZ count
        liX liBeta0 ↔
      PaperLevelInputs beta0 zeroRealPart cz discLog F K x degree C cZ
        (lagariasOdlyzkoError C cZ x degree) count (mainOf liX liBeta0) :=
  ⟨fun A => A.toPaperLevel hF hD, fun P => AnalyticSubProps.ofPaperLevel P⟩

/-! ## 4. The reduction to `EffectiveChebotarevInputs` -/

/-- **The L34 bundle with the five paper-level `Prop`s reduced.**  All data and
all non-analytic fields of `EffectiveChebotarevInputs` are kept.  `main` and
`error` are not fields: they are the explicit functions `mainOf` and
`lagariasOdlyzkoError`.  `main_eq` and the five analytic `Prop`s are replaced by
the single field `sub : AnalyticSubProps`. -/
structure L34AnalyticCore where
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
  /-- **The reduced analytic content**: the four core `Prop`s plus the
  positivity of their constants. -/
  sub : AnalyticSubProps beta0 zeroRealPart cz discLog F K x degree C cZ count
    liX liBeta0
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

namespace L34AnalyticCore

/-- **The reduction.**  The reduced bundle reconstructs the full
`EffectiveChebotarevInputs`.  The construction is purely definitional for the
data, `main`, `error` and `main_eq`; the five paper-level `Prop`s are supplied
by `AnalyticSubProps.toPaperLevel`. -/
def toEffectiveChebotarevInputs (S : L34AnalyticCore) : EffectiveChebotarevInputs where
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
  main := mainOf S.liX S.liBeta0
  error := lagariasOdlyzkoError S.C S.cZ S.x S.degree
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
  zero_free := dedekindZeroFreeRegion_of_core S.sub.cz_pos S.sub.zero_free
  stark := starkExceptionalZeroBound_of_gap S.F_pos S.discLog_pos S.sub.stark_gap
  cheb_range := effectiveChebotarevRange_of_inequality S.sub.K_pos S.sub.range
  cheb_error := lagariasOdlyzkoError_spec S.sub.C_pos S.sub.cZ_pos S.x S.degree
  cheb_count := effectiveChebotarev_of_sides S.sub.cheb_lower S.sub.cheb_upper
  main_eq := fun _ => rfl
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

/-- The rebuilt bundle carries exactly the five paper-level `Prop`s of
`PaperLevelInputs`. -/
theorem toPaperLevel (S : L34AnalyticCore) :
    PaperLevelInputs S.beta0 S.zeroRealPart S.cz S.discLog S.F S.K S.x S.degree
      S.C S.cZ (lagariasOdlyzkoError S.C S.cZ S.x S.degree) S.count
      (mainOf S.liX S.liBeta0) :=
  S.sub.toPaperLevel S.F_pos S.discLog_pos

/-- The L34 probe miss bound for the rebuilt bundle. -/
theorem probeMiss_le_ledger (S : L34AnalyticCore) :
    ∀ᶠ n : ℕ in atTop,
      probeMiss S.classCount S.pTrial S.R n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toEffectiveChebotarevInputs.probeMiss_le_ledger

/-- The L34 ledger slot for the rebuilt bundle. -/
theorem loss_le_ledger (S : L34AnalyticCore) :
    ∀ᶠ n : ℕ in atTop, S.toEffectiveChebotarevInputs.loss n ≤
      exp (-(2 : ℝ) * scale n) :=
  S.toEffectiveChebotarevInputs.loss_le_ledger

/-- The manuscript's slower `exp (-H / log H)` rate for the rebuilt bundle. -/
theorem loss_le_paper (S : L34AnalyticCore) :
    ∀ᶠ n : ℕ in atTop,
      S.toEffectiveChebotarevInputs.loss n ≤ exp (-(1 * paperRate n)) :=
  S.toEffectiveChebotarevInputs.loss_le_paper

/-- The literal `RatedLeaf` of the rebuilt bundle. -/
def ratedLeaf (S : L34AnalyticCore) : Cogentic.RandomizedPaperLeafStatements.RatedLeaf :=
  S.toEffectiveChebotarevInputs.ratedLeaf

end L34AnalyticCore

/-! ## Axiom audit -/

#print axioms lagariasOdlyzkoError_spec
#print axioms lagariasOdlyzkoError_unique
#print axioms lagariasOdlyzkoError_nonneg
#print axioms lagariasOdlyzkoError_pos
#print axioms dedekindZeroFreeRegion_of_core
#print axioms dedekindZeroFreeRegion_core
#print axioms starkExceptionalZeroBound_of_gap
#print axioms starkGap_of_starkExceptionalZeroBound
#print axioms effectiveChebotarevRange_of_inequality
#print axioms chebotarevRangeInequality_of_effective
#print axioms chebotarevLowerBound_of_effective
#print axioms chebotarevUpperBound_of_effective
#print axioms effectiveChebotarev_of_sides
#print axioms starkGap_pos
#print axioms starkGap_beta0_lt_one
#print axioms dedekindZeroFreeCore_dichotomy
#print axioms range_log_pos
#print axioms AnalyticSubProps.toPaperLevel
#print axioms AnalyticSubProps.ofPaperLevel
#print axioms analyticSubProps_iff_paperLevel
#print axioms L34AnalyticCore.toEffectiveChebotarevInputs
#print axioms L34AnalyticCore.toPaperLevel
#print axioms L34AnalyticCore.probeMiss_le_ledger
#print axioms L34AnalyticCore.loss_le_ledger
#print axioms L34AnalyticCore.loss_le_paper
#print axioms L34AnalyticCore.ratedLeaf

end

end Cogentic.RandomizedL34Analytic
