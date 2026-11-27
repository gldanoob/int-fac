import Cogentic.RandomizedL34Dedekind
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# L34: the three analytic inputs in zero-free / exceptional-zero / range form

`Cogentic.RandomizedL34Dedekind` reduced the paper-level analytic hypotheses to
`DedekindAnalyticInputs`.  This file isolates the three one-line inputs that the
paper actually quotes:

* `DedekindZeroFreeAboveBeta` — every zero of `ζ_E` above the exceptional zero
  `β₀` lies to the left of `1 - c_z / log |Δ_E|`;
* `StarkBetaUpper` — `β₀ ≤ 1 - (4 F log |Δ_E|)⁻¹`;
* `ChebotarevRangeThreshold` — `exp (K d (log |Δ_E|)²) ≤ x`.

Each is already a single inequality, so there is no further logical splitting to
do.  What this file adds is:

1. the *division-free* and *contradiction* forms of the same three inputs, with
   exact equivalence proofs (`dedekindZeroFreeAboveBeta_iff_distance`,
   `dedekindZeroFreeAboveBeta_iff_noAboveBoth`, `starkBetaUpper_iff_product`,
   `chebotarevExponentCondition_iff_budget`);
2. constant-comparison lemmas that let a literature estimate with a stronger
   zero-free constant, a stronger Stark constant, or a stronger range constant
   discharge the exact constants used below
   (`dedekindZeroFreeAboveBeta_of_core_of_le`,
   `starkBetaUpper_of_classical`, `chebotarevRangeInequality_of_le`);
3. the concrete `x = 2^(T^6)` specialization used in
   `research/keybreak-cumulative-character-probes.md`, reduced to the arithmetic
   budget `K d (log |Δ_E|)² ≤ (log 2) T^6`
   (`chebotarevRangeThreshold_T6_of_T6`);
4. the bundle `ZeroFreeAnalyticInputs` containing exactly the three named
   inputs plus the two sides of the Chebotarev count, and the lossless
   reduction `ZeroFreeAnalyticInputs.toDedekindAnalyticInputs` to
   `Cogentic.RandomizedL34Dedekind.DedekindAnalyticInputs`, with a converse
   `ofDedekindAnalyticInputs`.

## What the existing zeta estimates give

Mathlib defines `NumberField.dedekindZeta` but proves only its residue and the
Dirichlet class number formula; it contains no zero-free region and no
Chebotarev theorem for `ζ_E`.  The available zeta estimates are the half-plane
statements

* `riemannZeta_ne_zero_of_one_le_re`,
* `DirichletCharacter.LFunction_ne_zero_of_one_le_re`,

both at `re s ≥ 1`.  They are not effective (they give no `1 - c / log`
region), and neither is a statement about the Dedekind zeta function of the
absolute field `E = K(√γ)`.  The `tree` package's Riemann-hypothesis statement is
a statement about `riemannZeta` and Dirichlet `L`-functions, not about `ζ_E`.
Consequently none of the three paper inputs can be discharged from the modules
in this repository.  The sanity lemma
`dedekindZeroFreeAboveBeta_of_halfPlane_one` records the only deduction the
half-plane estimate does give: when `β₀ ≥ 1` the "above `β₀`" implication is
vacuous.  That is not the paper's `β₀ < 1` case, so the effective inputs remain
explicit.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no loss, count,
or error is set to zero.
-/

namespace Cogentic.RandomizedL34ZeroFree

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind

noncomputable section

/-! ## 0. What an existing half-plane estimate actually gives -/

/-- A zero-free right half-plane for a complex function. -/
def ZeroFreeHalfPlane (f : ℂ → ℂ) (σ : ℝ) : Prop :=
  ∀ s : ℂ, σ ≤ s.re → f s ≠ 0

/-- A sequence of zeros of `f`, together with the real-part sequence consumed by
the paper's zero-free `Prop`. -/
structure ZetaZeroSequence (f : ℂ → ℂ) where
  /-- The zero sequence. -/
  zero : ℕ → ℂ
  /-- Every element really is a zero. -/
  isZero : ∀ n, f (zero n) = 0
  /-- The real parts of the zeros. -/
  realPart : ℕ → ℝ
  /-- The real-part sequence is the real part of the zero sequence. -/
  realPart_eq : ∀ n, realPart n = (zero n).re

/-- Mathlib's Riemann-zeta half-plane estimate, in the form used below. -/
theorem riemannZeta_zeroFreeHalfPlane : ZeroFreeHalfPlane riemannZeta 1 :=
  fun _ hs => riemannZeta_ne_zero_of_one_le_re hs

/-- **The trivial arithmetic core of a half-plane estimate.**  If every zero has
real part below `1` and the exceptional zero is at least `1`, then no zero can
lie strictly above `β₀`; the conclusion of `DedekindZeroFreeAboveBeta` follows
vacuously, for every constant `cz`. -/
theorem dedekindZeroFreeAboveBeta_of_re_lt_one
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hre : ∀ n, zeroRealPart n < 1) (hβ : ∀ n, 1 ≤ beta0 n) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog := by
  intro n hb
  linarith [hre n, hβ n]

/-- **The only deduction available from Mathlib's zeta estimate.**  A zero-free
half-plane at `1` plus `β₀ ≥ 1` gives the "above `β₀`" statement vacuously.
This is recorded to mark the exact boundary of the existing estimates: it does
not cover the paper's `β₀ < 1`, and it gives no effective constant `cz > 0`. -/
theorem dedekindZeroFreeAboveBeta_of_halfPlane_one
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 ≤ beta0 n) (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog := by
  refine dedekindZeroFreeAboveBeta_of_re_lt_one ?_ hβ
  intro n
  rw [Z.realPart_eq n]
  by_contra hnot
  exact hf (Z.zero n) (le_of_not_gt hnot) (Z.isZero n)

/-- The Riemann-zeta instance of the preceding boundary statement. -/
theorem riemannZeta_zeroFreeAboveBeta
    (Z : ZetaZeroSequence riemannZeta) {beta0 : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_halfPlane_one Z riemannZeta_zeroFreeHalfPlane hβ cz discLog

/-! ## 1. The zero-free region in division-free and contradiction forms -/

/-- **Division-free form of the zero-free region.**  Above `β₀`, the gap
`1 - Re ρ` is at least `c_z / log |Δ_E|`. -/
def DedekindZeroFreeDistance (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n < zeroRealPart n → cz ≤ (1 - zeroRealPart n) * discLog n

/-- The division-free form is exactly `DedekindZeroFreeAboveBeta` when
`log |Δ_E| > 0`. -/
theorem dedekindZeroFreeAboveBeta_iff_distance
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog ↔
      DedekindZeroFreeDistance beta0 zeroRealPart cz discLog := by
  constructor
  · intro h n hb
    have hle := h n hb
    have hdiv : cz / discLog n ≤ 1 - zeroRealPart n := by linarith
    exact (div_le_iff₀ (hd n)).mp hdiv
  · intro h n hb
    have hineq : cz ≤ (1 - zeroRealPart n) * discLog n := h n hb
    have hdiv : cz / discLog n ≤ 1 - zeroRealPart n :=
      (div_le_iff₀ (hd n)).mpr hineq
    linarith

/-- The division-free form gives the region. -/
theorem dedekindZeroFreeAboveBeta_of_distance
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeDistance beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog :=
  (dedekindZeroFreeAboveBeta_iff_distance hd).mpr h

/-- The region gives the division-free form. -/
theorem dedekindZeroFreeDistance_of_aboveBeta
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeDistance beta0 zeroRealPart cz discLog :=
  (dedekindZeroFreeAboveBeta_iff_distance hd).mp h

/-- **No-double-exceedance form.**  No zero lies strictly above both `β₀` and
the zero-free line.  This is the contradiction form of the region and is the
form used when an argument splits on `max β₀ (1 - c_z / log |Δ_E|)`. -/
def DedekindZeroFreeNoAboveBoth (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n < zeroRealPart n →
    1 - cz / discLog n < zeroRealPart n → False

/-- The no-double-exceedance form is exactly the "above `β₀`" form. -/
theorem dedekindZeroFreeAboveBeta_iff_noAboveBoth
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog ↔
      DedekindZeroFreeNoAboveBoth beta0 zeroRealPart cz discLog := by
  constructor
  · intro h n hb hlt
    exact (not_lt_of_ge (h n hb)) hlt
  · intro h n hb
    by_contra hnot
    exact h n hb (not_le.mp hnot)

/-- The contradiction form gives the region. -/
theorem dedekindZeroFreeAboveBeta_of_noAboveBoth
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeNoAboveBoth beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeAboveBeta_iff_noAboveBoth.mpr h

/-- The region gives the contradiction form. -/
theorem dedekindZeroFreeNoAboveBoth_of_aboveBeta
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeNoAboveBoth beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeAboveBeta_iff_noAboveBoth.mp h

/-- **A stronger literature zero-free region gives the paper's region.**  If a
classical zero-free region is known with constant `cz'`, then the "above `β₀`"
form holds for every smaller constant `cz ≤ cz'`.  The line
`1 - cz / log |Δ_E|` is then to the right of the classical line, so the
implication is weaker.  This is the form in which a quoted theorem with a
larger explicit zero-free constant is consumed. -/
theorem dedekindZeroFreeAboveBeta_of_core_of_le
    {beta0 zeroRealPart : ℕ → ℝ} {cz cz' : ℝ} {discLog : ℕ → ℝ}
    (hcz : cz ≤ cz') (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeCore beta0 zeroRealPart cz' discLog) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog := by
  intro n hb
  by_contra hnot
  have hlt : 1 - cz / discLog n < zeroRealPart n := not_le.mp hnot
  have hle : 1 - cz' / discLog n ≤ 1 - cz / discLog n := by
    have hdiv : cz / discLog n ≤ cz' / discLog n :=
      div_le_div_of_nonneg_right hcz (le_of_lt (hd n))
    linarith
  have hstrong : 1 - cz' / discLog n < zeroRealPart n := lt_of_le_of_lt hle hlt
  have hβ : zeroRealPart n ≤ beta0 n := h n hstrong
  linarith

/-! ## 2. Stark's exceptional-zero bound in product form -/

/-- **Division-free form of Stark's bound.**  The exceptional zero satisfies
`4 F log |Δ_E| (1 - β₀) ≥ 1`. -/
def StarkBetaProduct (beta0 F discLog : ℕ → ℝ) : Prop :=
  ∀ n, 1 ≤ 4 * F n * discLog n * (1 - beta0 n)

/-- Stark's upper-bound form is exactly its division-free product form, once the
denominator is positive. -/
theorem starkBetaUpper_iff_product
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n) :
    StarkBetaUpper beta0 F discLog ↔ StarkBetaProduct beta0 F discLog := by
  constructor
  · intro h n
    have hden : 0 < 4 * F n * discLog n :=
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (hF n)) (hd n)
    have hgap : 1 / (4 * F n * discLog n) ≤ 1 - beta0 n := by
      linarith [h n]
    exact (div_le_iff₀' hden).mp hgap
  · intro h n
    have hden : 0 < 4 * F n * discLog n :=
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (hF n)) (hd n)
    have hgap : 1 / (4 * F n * discLog n) ≤ 1 - beta0 n :=
      (div_le_iff₀' hden).mpr (h n)
    linarith

/-- The product form gives Stark's upper bound. -/
theorem starkBetaUpper_of_product
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n)
    (h : StarkBetaProduct beta0 F discLog) :
    StarkBetaUpper beta0 F discLog :=
  (starkBetaUpper_iff_product hF hd).mpr h

/-- Stark's upper bound gives the product form. -/
theorem starkBetaProduct_of_betaUpper
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n)
    (h : StarkBetaUpper beta0 F discLog) :
    StarkBetaProduct beta0 F discLog :=
  (starkBetaUpper_iff_product hF hd).mp h

/-- **A classical Stark estimate with constant `c`.**  The literature form
`β₀ ≤ 1 - c / (F log |Δ_E|)`, with the constant `c` kept explicit. -/
def StarkBetaClassical (beta0 F discLog : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ n, beta0 n ≤ 1 - c / (F n * discLog n)

/-- **A classical Stark constant at least `1/4` gives the paper's bound.**  If a
quoted estimate has `β₀ ≤ 1 - c / (F log |Δ_E|)` with `c ≥ 1/4`, then it implies
`β₀ ≤ 1 - (4 F log |Δ_E|)⁻¹`; the paper uses exactly `c = 1/4`. -/
theorem starkBetaUpper_of_classical
    {beta0 F discLog : ℕ → ℝ} {c : ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n)
    (hc : (1 / 4 : ℝ) ≤ c)
    (h : StarkBetaClassical beta0 F discLog c) :
    StarkBetaUpper beta0 F discLog := by
  intro n
  have hden : 0 < F n * discLog n := mul_pos (hF n) (hd n)
  have hfrac : 1 / (4 * F n * discLog n) ≤ c / (F n * discLog n) := by
    rw [div_le_div_iff₀
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (hF n)) (hd n)) hden]
    have hmul := mul_le_mul_of_nonneg_right hc (le_of_lt hden)
    nlinarith
  linarith [h n, hfrac]

/-- The paper's `c = 1/4` instance. -/
theorem starkBetaUpper_of_classical_quarter
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n)
    (h : StarkBetaClassical beta0 F discLog (1 / 4)) :
    StarkBetaUpper beta0 F discLog :=
  starkBetaUpper_of_classical hF hd le_rfl h

/-- The `c = 1/4` classical form is *exactly* `StarkBetaUpper`; the only
difference is the position of the division by `4`. -/
theorem starkBetaClassical_quarter_iff_betaUpper
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hd : ∀ n, 0 < discLog n) :
    StarkBetaClassical beta0 F discLog (1 / 4) ↔
      StarkBetaUpper beta0 F discLog := by
  constructor
  · exact starkBetaUpper_of_classical_quarter hF hd
  · intro h n
    have hden : 0 < F n * discLog n := mul_pos (hF n) (hd n)
    have hEq : (1 / 4 : ℝ) / (F n * discLog n) =
        1 / (4 * F n * discLog n) := by
      field_simp [hden.ne']
    rw [hEq]
    exact h n

/-! ## 3. The Chebotarev range condition -/

/-- **Exponent-budget form of the range condition for `x = 2^S`.**  The exponent
`S` dominates `K d (log |Δ_E|)² / log 2`. -/
def ChebotarevExponentBudget (K : ℝ) (S degree discLog : ℕ → ℝ) : Prop :=
  ∀ n, K * degree n * (discLog n) ^ 2 / Real.log 2 ≤ S n

/-- The paper's exponent inequality is exactly the exponent budget, since
`log 2 > 0`. -/
theorem chebotarevExponentCondition_iff_budget
    {K : ℝ} {S degree discLog : ℕ → ℝ} :
    ChebotarevExponentCondition K S degree discLog ↔
      ChebotarevExponentBudget K S degree discLog := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h n
    exact (div_le_iff₀ hlog).mpr (by simpa [mul_comm] using h n)
  · intro h n
    have := (div_le_iff₀ hlog).mp (h n)
    simpa [mul_comm] using this

/-- **The range threshold for `x = 2^S` follows from the exponent budget.** -/
theorem chebotarevRangeThreshold_rpow_two_of_budget
    {K : ℝ} {S degree discLog : ℕ → ℝ}
    (h : ChebotarevExponentBudget K S degree discLog) :
    ChebotarevRangeThreshold K (fun n => (2 : ℝ) ^ S n) degree discLog := by
  have hcond : ChebotarevExponentCondition K S degree discLog :=
    chebotarevExponentCondition_iff_budget.mpr h
  have hx : ∀ n, 0 < (2 : ℝ) ^ S n :=
    fun n => Real.rpow_pos_of_pos (by norm_num) (S n)
  exact chebotarevRangeThreshold_of_inequality hx
    (chebotarevRangeInequality_rpow_two hcond)

/-- **The threshold and the exponent budget are exactly equivalent for
`x = 2^S`.**  This is the lossless form of the paper's choice of cutoff. -/
theorem chebotarevRangeThreshold_rpow_two_iff_budget
    {K : ℝ} {S degree discLog : ℕ → ℝ} :
    ChebotarevRangeThreshold K (fun n => (2 : ℝ) ^ S n) degree discLog ↔
      ChebotarevExponentBudget K S degree discLog := by
  constructor
  · intro h
    have hx : ∀ n, 0 < (2 : ℝ) ^ S n :=
      fun n => Real.rpow_pos_of_pos (by norm_num) (S n)
    have hineq : ChebotarevRangeInequality K (fun n => (2 : ℝ) ^ S n) degree discLog :=
      chebotarevRangeInequality_of_threshold hx h
    exact (chebotarevExponentCondition_iff_budget).mp
      (chebotarevExponentCondition_of_rpow_two hineq)
  · exact chebotarevRangeThreshold_rpow_two_of_budget

/-- **The concrete `S = T^6` arithmetic budget** used in
`research/keybreak-cumulative-character-probes.md`:
`K d (log |Δ_E|)² ≤ (log 2) T^6`. -/
def ChebotarevRangeT6 (K : ℝ) (T degree discLog : ℕ → ℝ) : Prop :=
  ∀ n, K * degree n * (discLog n) ^ 2 ≤ Real.log 2 * (T n) ^ 6

/-- **The paper's `x = 2^(T^6)` range threshold.**  The only remaining range
input is the arithmetic budget `K d (log |Δ_E|)² ≤ (log 2) T^6`; no logarithm,
exponential, or division by `T` remains in the hypothesis. -/
theorem chebotarevRangeThreshold_T6_of_T6
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (h : ChebotarevRangeT6 K T degree discLog) :
    ChebotarevRangeThreshold K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog := by
  have hcond : ChebotarevExponentCondition K (fun n => (T n) ^ 6) degree discLog := h
  have hx : ∀ n, 0 < (2 : ℝ) ^ ((T n) ^ 6) :=
    fun n => Real.rpow_pos_of_pos (by norm_num) ((T n) ^ 6)
  exact chebotarevRangeThreshold_of_inequality hx
    (chebotarevRangeInequality_rpow_two hcond)

/-- **The `x = 2^(T^6)` threshold is exactly the arithmetic budget.** -/
theorem chebotarevRangeT6_of_threshold
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (h : ChebotarevRangeThreshold K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog) :
    ChebotarevRangeT6 K T degree discLog := by
  have hx : ∀ n, 0 < (2 : ℝ) ^ ((T n) ^ 6) :=
    fun n => Real.rpow_pos_of_pos (by norm_num) ((T n) ^ 6)
  have hineq : ChebotarevRangeInequality K
      (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog :=
    chebotarevRangeInequality_of_threshold hx h
  have hcond : ChebotarevExponentCondition K (fun n => (T n) ^ 6) degree discLog :=
    chebotarevExponentCondition_of_rpow_two hineq
  exact hcond

/-- **A stronger range constant gives the paper's range constant.**  If a
quoted theorem gives `K' d (log |Δ_E|)² ≤ log x` with `K' ≥ K`, then the range
condition with `K` follows.  This is how an explicit Lagarias–Odlyzko range
estimate with a larger constant is consumed. -/
theorem chebotarevRangeInequality_of_le
    {K K' : ℝ} {x degree discLog : ℕ → ℝ}
    (hK : K ≤ K') (hdeg : ∀ n, 0 ≤ degree n)
    (h : ChebotarevRangeInequality K' x degree discLog) :
    ChebotarevRangeInequality K x degree discLog := by
  intro n
  have hsq : 0 ≤ degree n * (discLog n) ^ 2 :=
    mul_nonneg (hdeg n) (sq_nonneg _)
  have hmul : K * (degree n * (discLog n) ^ 2) ≤
      K' * (degree n * (discLog n) ^ 2) :=
    mul_le_mul_of_nonneg_right hK hsq
  have hmul' : K * degree n * (discLog n) ^ 2 ≤
      K' * degree n * (discLog n) ^ 2 := by
    simpa [mul_assoc] using hmul
  exact le_trans hmul' (h n)

/-- The threshold form of the same constant comparison. -/
theorem chebotarevRangeThreshold_of_le
    {K K' : ℝ} {x degree discLog : ℕ → ℝ}
    (hx : ∀ n, 0 < x n) (hK : K ≤ K') (hdeg : ∀ n, 0 ≤ degree n)
    (h : ChebotarevRangeInequality K' x degree discLog) :
    ChebotarevRangeThreshold K x degree discLog :=
  chebotarevRangeThreshold_of_inequality hx
    (chebotarevRangeInequality_of_le hK hdeg h)

/-! ## 4. A classical bundle with explicit stronger constants -/

/-- **Classical Dedekind/Stark/range estimates with explicit constants.**  This
is the source shape of a quoted analytic theorem:

* a zero-free region with constant `cz' ≥ cz`;
* Stark's bound with constant `starkC ≥ 1/4`;
* a range estimate with constant `K' ≥ K`.

The fields `discLog_pos`, `F_pos`, `degree_nonneg` and `x_pos` are the
arithmetic side conditions needed to compare the constants.  No analytic
statement is weakened: each comparison is an exact monotonicity in the
constant. -/
structure ClassicalDedekindEstimates
    (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ)
    (F : ℕ → ℝ) (K : ℝ) (x degree : ℕ → ℝ) : Type where
  /-- The literature zero-free constant. -/
  cz_classical : ℝ
  /-- It is positive. -/
  cz_classical_pos : 0 < cz_classical
  /-- It is at least the paper's constant. -/
  cz_le : cz ≤ cz_classical
  /-- The literature zero-free region, in core form. -/
  zeroFree_classical : DedekindZeroFreeCore beta0 zeroRealPart cz_classical discLog
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- The literature Stark constant. -/
  starkC : ℝ
  /-- It is at least `1/4`. -/
  starkC_ge : (1 / 4 : ℝ) ≤ starkC
  /-- The literature Stark estimate. -/
  stark_classical : StarkBetaClassical beta0 F discLog starkC
  /-- The literature range constant. -/
  K_classical : ℝ
  /-- It is at least the paper's constant. -/
  K_le : K ≤ K_classical
  /-- The absolute degree is nonnegative. -/
  degree_nonneg : ∀ n, 0 ≤ degree n
  /-- The literature range inequality. -/
  range_classical : ChebotarevRangeInequality K_classical x degree discLog

namespace ClassicalDedekindEstimates

/-- A classical zero-free region with a stronger constant gives
`DedekindZeroFreeAboveBeta`. -/
theorem zeroFreeAboveBeta
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    {F : ℕ → ℝ} {K : ℝ} {x degree : ℕ → ℝ}
    (E : ClassicalDedekindEstimates beta0 zeroRealPart cz discLog F K x degree) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_core_of_le E.cz_le E.discLog_pos E.zeroFree_classical

/-- A classical Stark estimate with constant at least `1/4` gives
`StarkBetaUpper`. -/
theorem starkBetaUpper
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    {F : ℕ → ℝ} {K : ℝ} {x degree : ℕ → ℝ}
    (E : ClassicalDedekindEstimates beta0 zeroRealPart cz discLog F K x degree) :
    StarkBetaUpper beta0 F discLog :=
  starkBetaUpper_of_classical E.F_pos E.discLog_pos E.starkC_ge E.stark_classical

/-- A classical range estimate with a stronger constant gives the paper's range
inequality. -/
theorem chebotarevRangeInequality
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    {F : ℕ → ℝ} {K : ℝ} {x degree : ℕ → ℝ}
    (E : ClassicalDedekindEstimates beta0 zeroRealPart cz discLog F K x degree) :
    ChebotarevRangeInequality K x degree discLog :=
  chebotarevRangeInequality_of_le E.K_le E.degree_nonneg E.range_classical

/-- The same range estimate in threshold form. -/
theorem chebotarevRangeThreshold
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    {F : ℕ → ℝ} {K : ℝ} {x degree : ℕ → ℝ}
    (E : ClassicalDedekindEstimates beta0 zeroRealPart cz discLog F K x degree)
    (hx : ∀ n, 0 < x n) :
    ChebotarevRangeThreshold K x degree discLog :=
  chebotarevRangeThreshold_of_inequality hx E.chebotarevRangeInequality

end ClassicalDedekindEstimates

/-! ## 5. The smallest zero-free/Stark/range bundle -/

/-- **The three named analytic inputs, in their smallest explicit form.**  Each
field is a single inequality:

* `zeroFree` — `DedekindZeroFreeAboveBeta`;
* `stark` — `StarkBetaUpper`;
* `range` — `ChebotarevRangeThreshold`.

The fields `cz_pos`, `K_pos`, `x_pos`, `C_pos`, `cZ_pos` are the positivity
side conditions already present in the paper-level `Prop`s, and `cheb` is the
two-sided cumulative Chebotarev count.  No error function or main term is a
field: they are reconstructed definitionally by `mainOf` and
`lagariasOdlyzkoError`. -/
structure ZeroFreeAnalyticInputs
    (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ)
    (F : ℕ → ℝ) (K : ℝ) (x degree : ℕ → ℝ)
    (C cZ : ℝ) (count : ℕ → ℝ) (liX liBeta0 : ℕ → ℝ) : Prop where
  /-- The zero-free-region constant is positive. -/
  cz_pos : 0 < cz
  /-- Every zero above `β₀` lies on the zero-free side. -/
  zeroFree : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog
  /-- Stark's exceptional-zero bound. -/
  stark : StarkBetaUpper beta0 F discLog
  /-- The range constant is positive. -/
  K_pos : 0 < K
  /-- The explicit exponential range threshold. -/
  range : ChebotarevRangeThreshold K x degree discLog
  /-- The cutoff is positive. -/
  x_pos : ∀ n, 0 < x n
  /-- The error constant is positive. -/
  C_pos : 0 < C
  /-- The error exponent is positive. -/
  cZ_pos : 0 < cZ
  /-- The two sides of the cumulative Chebotarev count. -/
  cheb : ChebotarevSides count (mainOf liX liBeta0)
    (lagariasOdlyzkoError C cZ x degree)

namespace ZeroFreeAnalyticInputs

/-- **The main reduction.**  The three named inputs plus the two-sided count
give `DedekindAnalyticInputs`.  The zero-free, Stark and range fields are
translated by the exact equivalence lemmas of
`Cogentic.RandomizedL34Dedekind`; the count is copied fieldwise. -/
theorem toDedekindAnalyticInputs
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : ZeroFreeAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  zeroFree :=
    { cz_pos := A.cz_pos
      above_beta := A.zeroFree }
  stark := { gap := starkGap_of_betaUpper A.stark }
  range :=
    { K_pos := A.K_pos
      range := chebotarevRangeInequality_of_threshold A.x_pos A.range }
  cheb :=
    { C_pos := A.C_pos
      cZ_pos := A.cZ_pos
      lower := A.cheb.lower
      upper := A.cheb.upper }

/-- **The converse.**  `DedekindAnalyticInputs` gives the three named inputs.
The only extra hypothesis is `x > 0`, needed to pass from the logarithmic range
inequality to the exponential threshold. -/
theorem ofDedekindAnalyticInputs
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (A : DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ
      count liX liBeta0)
    (hx : ∀ n, 0 < x n) :
    ZeroFreeAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  cz_pos := A.zeroFree.cz_pos
  zeroFree := A.zeroFree.above_beta
  stark := starkBetaUpper_of_starkGap A.stark.gap
  K_pos := A.range.K_pos
  range := chebotarevRangeThreshold_of_inequality hx A.range.range
  x_pos := hx
  C_pos := A.cheb.C_pos
  cZ_pos := A.cheb.cZ_pos
  cheb := { lower := A.cheb.lower, upper := A.cheb.upper }

/-- **A classical estimate bundle gives the smallest zero-free/Stark/range
bundle.** -/
theorem ofClassical
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (E : ClassicalDedekindEstimates beta0 zeroRealPart cz discLog F K x degree)
    (hcz : 0 < cz) (hK : 0 < K) (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    ZeroFreeAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 where
  cz_pos := hcz
  zeroFree := E.zeroFreeAboveBeta
  stark := E.starkBetaUpper
  K_pos := hK
  range := E.chebotarevRangeThreshold hx
  x_pos := hx
  C_pos := hC
  cZ_pos := hcZ
  cheb := hcheb

end ZeroFreeAnalyticInputs

/-- **Losslessness of the zero-free/Stark/range formulation.**  Given positive
cutoffs, the small bundle is equivalent to `DedekindAnalyticInputs`. -/
theorem zeroFreeAnalyticInputs_iff_dedekindAnalyticInputs
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ} (hx : ∀ n, 0 < x n) :
    ZeroFreeAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
        liX liBeta0 ↔
      DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
        liX liBeta0 :=
  ⟨fun A => A.toDedekindAnalyticInputs,
    fun A => ZeroFreeAnalyticInputs.ofDedekindAnalyticInputs A hx⟩

/-- **Direct assembly of the three named inputs.**  This is the reduction
signature: `DedekindZeroFreeAboveBeta`, `StarkBetaUpper` and
`ChebotarevRangeThreshold`, together with the positivity constants and the
two-sided Chebotarev count, imply `DedekindAnalyticInputs` without any `sorry`,
additional analytic hypothesis, or zero-valued loss. -/
theorem dedekindAnalyticInputs_of_zeroFree
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (hcz : 0 < cz)
    (hz : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog)
    (hs : StarkBetaUpper beta0 F discLog)
    (hK : 0 < K)
    (hr : ChebotarevRangeThreshold K x degree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 :=
  ZeroFreeAnalyticInputs.toDedekindAnalyticInputs
    { cz_pos := hcz
      zeroFree := hz
      stark := hs
      K_pos := hK
      range := hr
      x_pos := hx
      C_pos := hC
      cZ_pos := hcZ
      cheb := hcheb }

/-- **The classical bundle reduces directly to `DedekindAnalyticInputs`.**  This
is the composition of the constant comparisons with the main reduction and is
the theorem to invoke when a paper-level theorem is quoted with its own
explicit constants. -/
theorem dedekindAnalyticInputs_of_classical
    {beta0 zeroRealPart discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (E : ClassicalDedekindEstimates beta0 zeroRealPart cz discLog F K x degree)
    (hcz : 0 < cz) (hK : 0 < K) (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K x degree C cZ count
      liX liBeta0 :=
  (ZeroFreeAnalyticInputs.ofClassical E hcz hK hx hC hcZ hcheb).toDedekindAnalyticInputs

/-- **The concrete `x = 2^(T^6)` instance.**  Starting from the paper's
arithmetic budget `K d (log |Δ_E|)² ≤ (log 2) T^6`, the range input is the
threshold `exp (K d (log |Δ_E|)²) ≤ 2^(T^6)`, and the remaining two inputs are
the explicit zero-free and Stark statements. -/
theorem dedekindAnalyticInputs_of_T6
    {beta0 zeroRealPart discLog F T degree count liX liBeta0 : ℕ → ℝ}
    {cz K C cZ : ℝ}
    (hcz : 0 < cz)
    (hz : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog)
    (hs : StarkBetaUpper beta0 F discLog)
    (hK : 0 < K)
    (hT6 : ChebotarevRangeT6 K T degree discLog)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree)) :
    DedekindAnalyticInputs beta0 zeroRealPart cz discLog F K
      (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree C cZ count liX liBeta0 :=
  dedekindAnalyticInputs_of_zeroFree hcz hz hs hK
    (chebotarevRangeThreshold_T6_of_T6 hT6)
    (fun n => Real.rpow_pos_of_pos (by norm_num) ((T n) ^ 6))
    hC hcZ hcheb

/-! ## Axiom audit -/

#print axioms riemannZeta_zeroFreeAboveBeta
#print axioms dedekindZeroFreeAboveBeta_of_re_lt_one
#print axioms dedekindZeroFreeAboveBeta_of_halfPlane_one
#print axioms dedekindZeroFreeAboveBeta_iff_distance
#print axioms dedekindZeroFreeAboveBeta_of_distance
#print axioms dedekindZeroFreeDistance_of_aboveBeta
#print axioms dedekindZeroFreeAboveBeta_iff_noAboveBoth
#print axioms dedekindZeroFreeAboveBeta_of_noAboveBoth
#print axioms dedekindZeroFreeNoAboveBoth_of_aboveBeta
#print axioms dedekindZeroFreeAboveBeta_of_core_of_le
#print axioms starkBetaUpper_iff_product
#print axioms starkBetaUpper_of_product
#print axioms starkBetaProduct_of_betaUpper
#print axioms starkBetaUpper_of_classical
#print axioms starkBetaUpper_of_classical_quarter
#print axioms starkBetaClassical_quarter_iff_betaUpper
#print axioms chebotarevExponentCondition_iff_budget
#print axioms chebotarevRangeThreshold_rpow_two_of_budget
#print axioms chebotarevRangeThreshold_rpow_two_iff_budget
#print axioms chebotarevRangeThreshold_T6_of_T6
#print axioms chebotarevRangeT6_of_threshold
#print axioms chebotarevRangeInequality_of_le
#print axioms chebotarevRangeThreshold_of_le
#print axioms ClassicalDedekindEstimates.zeroFreeAboveBeta
#print axioms ClassicalDedekindEstimates.starkBetaUpper
#print axioms ClassicalDedekindEstimates.chebotarevRangeInequality
#print axioms ClassicalDedekindEstimates.chebotarevRangeThreshold
#print axioms ZeroFreeAnalyticInputs.toDedekindAnalyticInputs
#print axioms ZeroFreeAnalyticInputs.ofDedekindAnalyticInputs
#print axioms ZeroFreeAnalyticInputs.ofClassical
#print axioms zeroFreeAnalyticInputs_iff_dedekindAnalyticInputs
#print axioms dedekindAnalyticInputs_of_zeroFree
#print axioms dedekindAnalyticInputs_of_classical
#print axioms dedekindAnalyticInputs_of_T6

end

end Cogentic.RandomizedL34ZeroFree
