import Cogentic.RandomizedL20_2CoordinateEnergy

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# L20.2: the coordinate envelope fit in the paper's normalization

`Cogentic.RandomizedL20_2CoordinateEnergy` isolates the one-coordinate input of
the G.10 off-diagonal estimate as

`CoordinateEnvelopeFit env μ crtError charError : ∀ n,
  env n ^ 2 ≤ (crtError n + charError n) * μ n ^ 2`,

together with the two route-specific versions `MellinCoordinateFit` and
`GridPrefixCoordinateFit`.  This file removes the arithmetic content of the fit
and leaves the smallest explicit envelope/mass comparison.

## 1. The paper's normalization

The paper states the coordinate estimate as a *relative* bound: the second
moment of one coordinate is at most `(crtError + charError) · μ²`, where `μ` is
the ideal interior mean and `crtError`, `charError` are the relative CRT and
smooth-character errors.  Dividing by the positive mean gives the equivalent
normalized form

`(env n / μ n) ^ 2 ≤ crtError n + charError n`,

or, after taking square roots,

`env n / μ n ≤ sqrt (crtError n + charError n)`.

`coordinateEnvelopeFit_iff_normalized` and
`coordinateEnvelopeFit_iff_sqrt_normalized` prove these equivalences.  They are
pure algebra: no estimate is hidden and no energy is normalized away.

## 2. The smallest explicit envelope/mass certificate

The remaining content of the fit is the comparison between three explicit
scalar profiles on a common nonnegative scale `H`:

* the envelope growth `env n ≤ exp (c · H n)`;
* the ideal-mass lower bound `exp (η · H n) ≤ μ n`;
* the relative-error lower bound `exp (-cErr · H n) ≤ crtError n + charError n`;

with the exponent inequality `2 c + cErr ≤ 2 η`.  Under these four conditions
`CoordinateEnvelopeFit env μ crtError charError` follows pointwise:
squaring the envelope and the mass gives `exp (2 c H)` against
`exp (-cErr H) · exp (2 η H) = exp ((2 η - cErr) H)`, and the exponent
comparison closes the inequality.  This is
`CoordinateEnvelopeFit` from `CoordinateEnvelopeMassFit`.

The two route-specific versions instantiate `env` with `mellinEnvelope`
(`MellinEnvelopeMassFit`) and `gridPrefixEnvelope`
(`GridPrefixEnvelopeMassFit`).  Composing with the existing critical-line
estimates `mellinEnergy_le_envelope` and `gridPrefixEnergy_le_envelope` then
gives the actual `CoordinateEnergyBudget` for the Mellin and sharp-prefix
energies, not merely for their envelopes.

## 3. The paper's saddle-point normalization

`coordinateEnvelopeFit_of_saddle` specializes the certificate to the paper's
normalization `H n = paperD n * scale n`, taking the mass lower bound from
`SaddlePointMeanLower` and `SaddlePointScaleLower` (Appendix C).  The
envelope-growth and error-lower inputs remain explicit, and the finite initial
segment `scale n < 0` is a separate checkable hypothesis, exactly as in
`RandomizedL19EnergyMass`; the asymptotic content is proved.

No `sorry`, `admit`, `axiom`, or `native_decide`.  No energy or error is set to
zero.
-/

namespace Cogentic.RandomizedL20_2Fit

open Filter Real
open scoped BigOperators Classical
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Char
open Cogentic.RandomizedL20_2CoordinateEnergy
open Cogentic.RandomizedL19Energy
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Window

/-! ## 1. The paper's normalized form -/

/-- **The normalized envelope fit.**  The envelope divided by the ideal mean is
at most the square root of the relative CRT plus smooth-character budget.  This
is the paper's `E ≤ sqrt ρ · μ` written in relative form. -/
def NormalizedEnvelopeFit (env μ crtError charError : ℕ → ℝ) : Prop :=
  ∀ n, env n / μ n ≤ Real.sqrt (crtError n + charError n)

/-- **Division by the positive mean is an equivalence.**  The unnormalized fit
`env² ≤ (crt + char) μ²` is exactly the normalized inequality
`(env / μ)² ≤ crt + char`, with no sign hypothesis on the error budget because
the division lemma only needs a positive denominator. -/
theorem coordinateEnvelopeFit_iff_normalized
    {env μ crtError charError : ℕ → ℝ} (hμ : ∀ n, 0 < μ n) :
    CoordinateEnvelopeFit env μ crtError charError ↔
      ∀ n, (env n / μ n) ^ 2 ≤ crtError n + charError n := by
  constructor
  · intro h n
    rw [div_pow, div_le_iff₀ (pow_pos (hμ n) 2)]
    exact h n
  · intro h n
    have hn := h n
    rw [div_pow, div_le_iff₀ (pow_pos (hμ n) 2)] at hn
    exact hn

/-- **The smallest normalized form.**  For a nonnegative envelope and a
nonnegative error budget, the squared normalized fit is equivalent to the
square-root form `env / μ ≤ sqrt (crt + char)`. -/
theorem coordinateEnvelopeFit_iff_sqrt_normalized
    {env μ crtError charError : ℕ → ℝ}
    (hμ : ∀ n, 0 < μ n) (henv : ∀ n, 0 ≤ env n)
    (hρ : ∀ n, 0 ≤ crtError n + charError n) :
    CoordinateEnvelopeFit env μ crtError charError ↔
      NormalizedEnvelopeFit env μ crtError charError := by
  rw [coordinateEnvelopeFit_iff_normalized hμ]
  constructor
  · intro h n
    exact Real.le_sqrt_of_sq_le (h n)
  · intro h n
    have hdiv : 0 ≤ env n / μ n := div_nonneg (henv n) (hμ n).le
    calc
      (env n / μ n) ^ 2 ≤ (Real.sqrt (crtError n + charError n)) ^ 2 :=
        pow_le_pow_left₀ hdiv (h n) 2
      _ = crtError n + charError n := Real.sq_sqrt (hρ n)

/-- **The fit from the smallest normalized inequality.**  This is the direct
elimination form of `coordinateEnvelopeFit_iff_normalized`. -/
theorem coordinateEnvelopeFit_of_normalized
    {env μ crtError charError : ℕ → ℝ} (hμ : ∀ n, 0 < μ n)
    (h : ∀ n, (env n / μ n) ^ 2 ≤ crtError n + charError n) :
    CoordinateEnvelopeFit env μ crtError charError :=
  (coordinateEnvelopeFit_iff_normalized hμ).2 h

/-- **The fit from the square-root normalized inequality.** -/
theorem coordinateEnvelopeFit_of_sqrt_normalized
    {env μ crtError charError : ℕ → ℝ}
    (hμ : ∀ n, 0 < μ n) (henv : ∀ n, 0 ≤ env n)
    (hρ : ∀ n, 0 ≤ crtError n + charError n)
    (h : NormalizedEnvelopeFit env μ crtError charError) :
    CoordinateEnvelopeFit env μ crtError charError :=
  (coordinateEnvelopeFit_iff_sqrt_normalized hμ henv hρ).2 h

/-! ## 2. The smallest explicit envelope/mass certificate -/

/-- **The four scalar inequalities behind one coordinate fit.**

`H` is any nonnegative common scale.  The envelope grows at most like
`exp (c H)`, the ideal mean is at least `exp (η H)`, and the relative error
budget is at least `exp (-cErr H)`.  The exponent inequality
`2 c + cErr ≤ 2 η` is the whole arithmetic content.  Every field is stated for
the actual envelope, the actual mean, and the actual error budget; none of them
is a placeholder or zero by fiat. -/
structure CoordinateEnvelopeMassFit (env μ crtError charError H : ℕ → ℝ)
    (c η cErr : ℝ) : Prop where
  /-- The common scale is nonnegative. -/
  H_nonneg : ∀ n, 0 ≤ H n
  /-- The envelope is a norm and is nonnegative. -/
  env_nonneg : ∀ n, 0 ≤ env n
  /-- The explicit envelope-growth bound. -/
  env_growth : ∀ n, env n ≤ exp (c * H n)
  /-- The explicit ideal-mass lower bound. -/
  mass_lower : ∀ n, exp (η * H n) ≤ μ n
  /-- The explicit relative-error lower bound. -/
  error_lower : ∀ n, exp (-cErr * H n) ≤ crtError n + charError n
  /-- The exponent comparison `2 c + cErr ≤ 2 η`. -/
  exponent_le : 2 * c + cErr ≤ 2 * η

/-- **The certificate proves the coordinate envelope fit.**  Squaring the
envelope and the mass reduces the fit to
`exp (2 c H) ≤ exp ((2 η - cErr) H)`, which is exactly the exponent
comparison. -/
theorem coordinateEnvelopeFit_of_envelopeMass
    {env μ crtError charError H : ℕ → ℝ} {c η cErr : ℝ}
    (h : CoordinateEnvelopeMassFit env μ crtError charError H c η cErr) :
    CoordinateEnvelopeFit env μ crtError charError := by
  intro n
  have hH : 0 ≤ H n := h.H_nonneg n
  have henv_sq : env n ^ 2 ≤ exp (2 * c * H n) := by
    calc
      env n ^ 2 ≤ (exp (c * H n)) ^ 2 :=
        pow_le_pow_left₀ (h.env_nonneg n) (h.env_growth n) 2
      _ = exp (2 * c * H n) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
  have hmass_sq : exp (2 * η * H n) ≤ μ n ^ 2 := by
    calc
      exp (2 * η * H n) = (exp (η * H n)) ^ 2 := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      _ ≤ μ n ^ 2 := pow_le_pow_left₀ (exp_pos _).le (h.mass_lower n) 2
  have hρ : 0 ≤ crtError n + charError n :=
    (exp_pos (-cErr * H n)).le.trans (h.error_lower n)
  have hprod :
      exp (-cErr * H n) * exp (2 * η * H n) ≤
        (crtError n + charError n) * μ n ^ 2 :=
    mul_le_mul (h.error_lower n) hmass_sq (exp_pos _).le hρ
  have hexp_prod : exp (-cErr * H n) * exp (2 * η * H n) =
      exp ((2 * η - cErr) * H n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcoef : 2 * c ≤ 2 * η - cErr := by linarith only [h.exponent_le]
  have hexp_le : exp (2 * c * H n) ≤ exp ((2 * η - cErr) * H n) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hcoef hH]
  calc
    env n ^ 2 ≤ exp (2 * c * H n) := henv_sq
    _ ≤ exp ((2 * η - cErr) * H n) := hexp_le
    _ = exp (-cErr * H n) * exp (2 * η * H n) := hexp_prod.symm
    _ ≤ (crtError n + charError n) * μ n ^ 2 := hprod

/-- The certificate in the normalized form: the explicit inequalities also
give `(env / μ)² ≤ crt + char` directly. -/
theorem normalized_of_envelopeMass
    {env μ crtError charError H : ℕ → ℝ} {c η cErr : ℝ}
    (h : CoordinateEnvelopeMassFit env μ crtError charError H c η cErr)
    (hμ : ∀ n, 0 < μ n) :
    ∀ n, (env n / μ n) ^ 2 ≤ crtError n + charError n :=
  (coordinateEnvelopeFit_iff_normalized hμ).1
    (coordinateEnvelopeFit_of_envelopeMass h)

/-- The certificate also gives the square-root normalized form. -/
theorem normalizedEnvelopeFit_of_envelopeMass
    {env μ crtError charError H : ℕ → ℝ} {c η cErr : ℝ}
    (h : CoordinateEnvelopeMassFit env μ crtError charError H c η cErr)
    (hμ : ∀ n, 0 < μ n) :
    NormalizedEnvelopeFit env μ crtError charError := by
  intro n
  exact Real.le_sqrt_of_sq_le (normalized_of_envelopeMass h hμ n)

/-- The Mellin envelope is nonnegative for the paper's parameters: `q ≠ 0`,
`K = mellinK line > 0`, and `B i ≥ 2`. -/
theorem mellinEnvelope_nonneg_of (line : DirichletLZerosOnLine) {q : ℕ}
    (hq : q ≠ 0) {ι : Type} [Fintype ι] (B : ι → ℕ) (hB : ∀ i, 2 ≤ B i)
    (t : ℝ) :
    0 ≤ mellinEnvelope q (mellinK line) B t := by
  unfold mellinEnvelope
  apply Finset.prod_nonneg
  intro i _
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq)
  have hB2 : (2 : ℝ) ≤ (B i : ℝ) := by exact_mod_cast hB i
  have harg : (1 : ℝ) ≤ (q : ℝ) * ((B i : ℝ) + |t| + 2) := by
    nlinarith [abs_nonneg t]
  have hlog : 0 ≤ Real.log ((q : ℝ) * ((B i : ℝ) + |t| + 2)) :=
    Real.log_nonneg harg
  have hcube :
      0 ≤ (1 + Real.log ((q : ℝ) * ((B i : ℝ) + |t| + 2))) ^ 3 := by
    positivity
  exact mul_nonneg
    (mul_nonneg (mellinK_pos line).le (Real.sqrt_nonneg _)) hcube

/-- The sharp-prefix envelope is nonnegative for `C ≥ 0`, `K ≥ 0`, `X ≥ 2`,
`U i ≥ 2`, and `m * B ≠ 0`. -/
theorem gridPrefixEnvelope_nonneg_of {ι : Type} [Fintype ι] [DecidableEq ι]
    (m B : ℕ) (hmB : m * B ≠ 0) {C K X : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hX : 2 ≤ X) (A U : ι → ℕ) (hU : ∀ i, 2 ≤ U i) :
    0 ≤ gridPrefixEnvelope m B C K X A U := by
  unfold gridPrefixEnvelope
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hmB1 : (1 : ℝ) ≤ ((m * B : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hmB)
  have hprod : 0 ≤ ∏ i, C * Real.sqrt (U i) *
      (1 + Real.log ((m * B : ℕ) * ((U i : ℝ) + X ^ 3 + 2))) ^ 3 := by
    apply Finset.prod_nonneg
    intro i _
    have hU2 : (2 : ℝ) ≤ (U i : ℝ) := by exact_mod_cast hU i
    have hX3 : (0 : ℝ) ≤ X ^ 3 := by positivity
    have harg : (1 : ℝ) ≤ ((m * B : ℕ) : ℝ) *
        ((U i : ℝ) + X ^ 3 + 2) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (U i)]
    have hlog : 0 ≤ Real.log ((m * B : ℕ) *
        ((U i : ℝ) + X ^ 3 + 2)) := Real.log_nonneg harg
    have hcube : 0 ≤ (1 + Real.log ((m * B : ℕ) *
        ((U i : ℝ) + X ^ 3 + 2))) ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hcube
  have hfirst : 0 ≤ (4 * Real.exp 2 / Real.pi) *
      ((∏ i, C * Real.sqrt (U i) *
        (1 + Real.log ((m * B : ℕ) * ((U i : ℝ) + X ^ 3 + 2))) ^ 3) *
          Real.log X) := by
    positivity
  have hsecond : 0 ≤ (2 * K / X ^ 2) * ((primeBinProducts A U).card : ℝ) := by
    positivity
  exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)

/-! ### 2a. The Mellin route -/

/-- The envelope/mass certificate specialized to the Plancherel Mellin
envelope `mellinEnvelope q (mellinK line) B (t n)`. -/
def MellinEnvelopeMassFit (line : DirichletLZerosOnLine) (q : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → ℕ) (t : ℕ → ℝ)
    (μ crtError charError H : ℕ → ℝ) (c η cErr : ℝ) : Prop :=
  CoordinateEnvelopeMassFit
    (fun n => mellinEnvelope q (mellinK line) B (t n))
    μ crtError charError H c η cErr

/-- **`MellinCoordinateFit` from the explicit certificate.** -/
theorem mellinCoordinateFit_of_envelopeMass
    (line : DirichletLZerosOnLine) (q : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → ℕ) (t : ℕ → ℝ)
    {μ crtError charError H : ℕ → ℝ} {c η cErr : ℝ}
    (h : MellinEnvelopeMassFit line q B t μ crtError charError H c η cErr) :
    MellinCoordinateFit line q B t μ crtError charError :=
  coordinateEnvelopeFit_of_envelopeMass h

/-- **`MellinCoordinateFit` directly from the paper's normalized form.**
The input is `mellinEnvelope / μ ≤ sqrt (crtError + charError)`, with no
intermediate envelope/mass certificate. -/
theorem mellinCoordinateFit_of_normalized
    (line : DirichletLZerosOnLine) (q : ℕ) (hq : q ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → ℕ)
    (hB : ∀ i, 2 ≤ B i) (t : ℕ → ℝ)
    {μ crtError charError : ℕ → ℝ} (hμ : ∀ n, 0 < μ n)
    (hρ : ∀ n, 0 ≤ crtError n + charError n)
    (h : NormalizedEnvelopeFit
      (fun n => mellinEnvelope q (mellinK line) B (t n))
      μ crtError charError) :
    MellinCoordinateFit line q B t μ crtError charError := by
  change CoordinateEnvelopeFit
    (fun n => mellinEnvelope q (mellinK line) B (t n))
    μ crtError charError
  exact (coordinateEnvelopeFit_iff_sqrt_normalized hμ
    (fun n => mellinEnvelope_nonneg_of line hq B hB _) hρ).2 h

/-- **The actual Mellin coordinate energy budget.**  Combining the certificate
with the existing critical-line Plancherel estimate
`mellinEnergy_le_envelope` gives the budget for `mellinEnergy` itself. -/
theorem coordinateEnergyBudget_of_mellinEnvelopeMass
    (line : DirichletLZerosOnLine) (q : ℕ) (hq : q ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ)
    (hB : ∀ i, 2 ≤ B i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (σ t : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    {μ crtError charError H : ℕ → ℝ} {c η cErr : ℝ}
    (h : MellinEnvelopeMassFit line q B t μ crtError charError H c η cErr) :
    CoordinateEnergyBudget
      (fun n => mellinEnergy q hq A B (σ n) (t n))
      μ crtError charError :=
  coordinateEnergyBudget_of_mellinEnvelope line q hq A B hB hAB hdisj
    σ t hσ (mellinCoordinateFit_of_envelopeMass line q B t h)

/-- **The actual Mellin budget from the paper's normalized inequality.**
This is the complete route: the relative inequality
`mellinEnvelope / μ ≤ sqrt (crtError + charError)` together with the existing
Plancherel estimate gives the budget for `mellinEnergy`. -/
theorem coordinateEnergyBudget_of_mellinNormalized
    (line : DirichletLZerosOnLine) (q : ℕ) (hq : q ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ)
    (hB : ∀ i, 2 ≤ B i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (σ t : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    {μ crtError charError : ℕ → ℝ} (hμ : ∀ n, 0 < μ n)
    (hρ : ∀ n, 0 ≤ crtError n + charError n)
    (h : NormalizedEnvelopeFit
      (fun n => mellinEnvelope q (mellinK line) B (t n))
      μ crtError charError) :
    CoordinateEnergyBudget
      (fun n => mellinEnergy q hq A B (σ n) (t n))
      μ crtError charError :=
  coordinateEnergyBudget_of_mellinEnvelope line q hq A B hB hAB hdisj
    σ t hσ (mellinCoordinateFit_of_normalized line q hq B hB t hμ hρ h)

/-! ### 2b. The sharp grid-prefix route -/

/-- The envelope/mass certificate specialized to the sharp-prefix envelope
`gridPrefixEnvelope m B C K (X n) A U`. -/
def GridPrefixEnvelopeMassFit (m B : ℕ) (C K : ℝ) (X : ℕ → ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    (μ crtError charError H : ℕ → ℝ) (c η cErr : ℝ) : Prop :=
  CoordinateEnvelopeMassFit
    (fun n => gridPrefixEnvelope m B C K (X n) A U)
    μ crtError charError H c η cErr

/-- **`GridPrefixCoordinateFit` from the explicit certificate.** -/
theorem gridPrefixCoordinateFit_of_envelopeMass
    (m B : ℕ) (C K : ℝ) (X : ℕ → ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    {μ crtError charError H : ℕ → ℝ} {c η cErr : ℝ}
    (h : GridPrefixEnvelopeMassFit m B C K X A U μ crtError charError
      H c η cErr) :
    GridPrefixCoordinateFit m B C K X A U μ crtError charError :=
  coordinateEnvelopeFit_of_envelopeMass h

/-- **`GridPrefixCoordinateFit` directly from the paper's normalized form.**
The input is `gridPrefixEnvelope / μ ≤ sqrt (crtError + charError)`; the
nonnegativity of the prefix envelope is supplied explicitly. -/
theorem gridPrefixCoordinateFit_of_normalized
    (m B : ℕ) (C K : ℝ) (X : ℕ → ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    {μ crtError charError : ℕ → ℝ} (hμ : ∀ n, 0 < μ n)
    (henv : ∀ n, 0 ≤ gridPrefixEnvelope m B C K (X n) A U)
    (hρ : ∀ n, 0 ≤ crtError n + charError n)
    (h : NormalizedEnvelopeFit
      (fun n => gridPrefixEnvelope m B C K (X n) A U) μ crtError charError) :
    GridPrefixCoordinateFit m B C K X A U μ crtError charError := by
  change CoordinateEnvelopeFit
    (fun n => gridPrefixEnvelope m B C K (X n) A U) μ crtError charError
  exact (coordinateEnvelopeFit_iff_sqrt_normalized hμ henv hρ).2 h

/-- **The actual sharp-prefix coordinate energy budget.**  Combining the
certificate with the existing critical-line prefix estimate
`gridPrefixEnergy_le_envelope` gives the budget for `gridPrefixEnergy` itself. -/
theorem coordinateEnergyBudget_of_gridPrefixEnvelopeMass
    (line : DirichletLZerosOnLine) (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (cop : m.Coprime B) (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ)
    (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    (hU : ∀ i, 2 ≤ U i) (hAU : ∀ i, A i ≤ U i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (U i)) (primeBin (A j) (U j)))
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n →
      X n ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n k, k ∈ primeBinProducts A U →
      X n ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * X n)
    {μ crtError charError H : ℕ → ℝ} {c η cErr : ℝ}
    (h : GridPrefixEnvelopeMassFit m B (prefixC m B hm hB line)
      (prefixK m B hm hB line) X A U μ crtError charError H c η cErr) :
    CoordinateEnergyBudget
      (fun n => gridPrefixEnergy m B hm hB cop (X n) (cutoffs n) (hne n) A U)
      μ crtError charError :=
  coordinateEnergyBudget_of_gridPrefixEnvelope line m B hm hB cop X cutoffs hne
    A U hU hAU hdisj hX heX hcut hP
    (gridPrefixCoordinateFit_of_envelopeMass m B
      (prefixC m B hm hB line) (prefixK m B hm hB line) X A U h)

/-- **The actual sharp-prefix budget from the paper's normalized inequality.**
The relative inequality
`gridPrefixEnvelope / μ ≤ sqrt (crtError + charError)` together with the
existing prefix estimate gives the budget for `gridPrefixEnergy`. -/
theorem coordinateEnergyBudget_of_gridPrefixNormalized
    (line : DirichletLZerosOnLine) (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    (cop : m.Coprime B) (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ)
    (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    (hU : ∀ i, 2 ≤ U i) (hAU : ∀ i, A i ≤ U i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (U i)) (primeBin (A j) (U j)))
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n →
      X n ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n k, k ∈ primeBinProducts A U →
      X n ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * X n)
    {μ crtError charError : ℕ → ℝ} (hμ : ∀ n, 0 < μ n)
    (henv : ∀ n, 0 ≤ gridPrefixEnvelope m B
      (prefixC m B hm hB line) (prefixK m B hm hB line) (X n) A U)
    (hρ : ∀ n, 0 ≤ crtError n + charError n)
    (h : NormalizedEnvelopeFit
      (fun n => gridPrefixEnvelope m B (prefixC m B hm hB line)
        (prefixK m B hm hB line) (X n) A U) μ crtError charError) :
    CoordinateEnergyBudget
      (fun n => gridPrefixEnergy m B hm hB cop (X n) (cutoffs n) (hne n) A U)
      μ crtError charError :=
  coordinateEnergyBudget_of_gridPrefixEnvelope line m B hm hB cop X cutoffs hne
    A U hU hAU hdisj hX heX hcut hP
    (gridPrefixCoordinateFit_of_normalized m B _ _ X A U hμ henv hρ h)

/-! ## 3. The paper's saddle-point normalization -/

/-- **The fit in the paper's normalization.**  Here the common scale is
`H n = paperD n * scale n`, the mass lower bound is the saddle-point lower
bound `μ ≥ exp (η Λ) ≥ exp (η cLam · paperD · scale)`, and the envelope is
allowed to grow only polynomially in `D = paperD`.  The exponent inequality is
`2 cE ≤ 2 η cLam - cErr`.  The only non-asymptotic input is the explicit
finite segment where `scale n < 0`, on which the fit is checked directly. -/
theorem coordinateEnvelopeFit_of_saddle
    {env μ crtError charError Λ : ℕ → ℝ} {cLam η cE cErr : ℝ}
    (hscale : SaddlePointScaleLower Λ cLam)
    (hmean : SaddlePointMeanLower μ Λ η)
    (henv_nonneg : ∀ n, 0 ≤ env n)
    (henv : ∀ n, env n ≤ exp (cE * scale n))
    (herr : ∀ n,
      exp (-cErr * (paperD n * scale n)) ≤ crtError n + charError n)
    (hexp : 2 * cE ≤ 2 * η * cLam - cErr)
    (hA : 0 ≤ 2 * η * cLam - cErr)
    (hinit : ∀ n, scale n < 0 →
      env n ^ 2 ≤ (crtError n + charError n) * μ n ^ 2) :
    CoordinateEnvelopeFit env μ crtError charError := by
  intro n
  by_cases hs : 0 ≤ scale n
  · have hD : 1 ≤ paperD n := by
      unfold paperD
      exact one_le_exp hs
    have hH : 0 ≤ paperD n * scale n :=
      mul_nonneg (paperD_pos n).le hs
    have henv_sq : env n ^ 2 ≤ exp (2 * cE * scale n) := by
      calc
        env n ^ 2 ≤ (exp (cE * scale n)) ^ 2 :=
          pow_le_pow_left₀ (henv_nonneg n) (henv n) 2
        _ = exp (2 * cE * scale n) := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
    have hLam : cLam * (paperD n * scale n) ≤ Λ n := by
      simpa only [mul_assoc] using hscale.2 n
    have hmass_sq : exp (2 * η * cLam * (paperD n * scale n)) ≤ μ n ^ 2 := by
      calc
        exp (2 * η * cLam * (paperD n * scale n)) =
            (exp (η * (cLam * (paperD n * scale n)))) ^ 2 := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
        _ ≤ (exp (η * Λ n)) ^ 2 := by
          apply pow_le_pow_left₀ (exp_pos _).le
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hLam hmean.1.le)
        _ ≤ μ n ^ 2 :=
          pow_le_pow_left₀ (exp_pos _).le (hmean.2 n) 2
    have hρ : 0 ≤ crtError n + charError n :=
      (exp_pos (-cErr * (paperD n * scale n))).le.trans (herr n)
    have hprod :
        exp (-cErr * (paperD n * scale n)) *
            exp (2 * η * cLam * (paperD n * scale n)) ≤
          (crtError n + charError n) * μ n ^ 2 :=
      mul_le_mul (herr n) hmass_sq (exp_pos _).le hρ
    have hcoef : 2 * cE ≤ (2 * η * cLam - cErr) * paperD n := by
      nlinarith only [hexp, hA, hD]
    have hscale_le : 2 * cE * scale n ≤
        (2 * η * cLam - cErr) * (paperD n * scale n) := by
      nlinarith only [mul_le_mul_of_nonneg_right hcoef hs]
    have hexp_le : exp (2 * cE * scale n) ≤
        exp ((2 * η * cLam - cErr) * (paperD n * scale n)) :=
      Real.exp_le_exp.mpr hscale_le
    have hexp_prod :
        exp (-cErr * (paperD n * scale n)) *
            exp (2 * η * cLam * (paperD n * scale n)) =
          exp ((2 * η * cLam - cErr) * (paperD n * scale n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      env n ^ 2 ≤ exp (2 * cE * scale n) := henv_sq
      _ ≤ exp ((2 * η * cLam - cErr) * (paperD n * scale n)) := hexp_le
      _ = exp (-cErr * (paperD n * scale n)) *
            exp (2 * η * cLam * (paperD n * scale n)) := hexp_prod.symm
      _ ≤ (crtError n + charError n) * μ n ^ 2 := hprod
  · exact hinit n (lt_of_not_ge hs)

/-- **The Mellin fit in the paper's normalization.**  This is
`coordinateEnvelopeFit_of_saddle` with `env` the Plancherel envelope. -/
theorem mellinCoordinateFit_of_saddle
    (line : DirichletLZerosOnLine) (q : ℕ) (hq : q ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → ℕ)
    (hB : ∀ i, 2 ≤ B i) (t : ℕ → ℝ)
    {μ crtError charError Λ : ℕ → ℝ} {cLam η cE cErr : ℝ}
    (hscale : SaddlePointScaleLower Λ cLam)
    (hmean : SaddlePointMeanLower μ Λ η)
    (henv : ∀ n, mellinEnvelope q (mellinK line) B (t n) ≤
      exp (cE * scale n))
    (herr : ∀ n,
      exp (-cErr * (paperD n * scale n)) ≤ crtError n + charError n)
    (hexp : 2 * cE ≤ 2 * η * cLam - cErr)
    (hA : 0 ≤ 2 * η * cLam - cErr)
    (hinit : ∀ n, scale n < 0 →
      mellinEnvelope q (mellinK line) B (t n) ^ 2 ≤
        (crtError n + charError n) * μ n ^ 2) :
    MellinCoordinateFit line q B t μ crtError charError :=
  coordinateEnvelopeFit_of_saddle (env := fun n =>
      mellinEnvelope q (mellinK line) B (t n)) hscale hmean
    (fun _ => mellinEnvelope_nonneg_of line hq B hB _)
    henv herr hexp hA hinit

/-- **The sharp-prefix fit in the paper's normalization.**  This is
`coordinateEnvelopeFit_of_saddle` with the prefix envelope and the constants
`prefixC`, `prefixK` supplied by the critical-line theorem. -/
theorem gridPrefixCoordinateFit_of_saddle
    (line : DirichletLZerosOnLine) (m B : ℕ) (hm : m ≠ 0) (hB : B ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ)
    (hU : ∀ i, 2 ≤ U i) (X : ℕ → ℝ) (hX : ∀ n, 2 ≤ X n)
    {μ crtError charError Λ : ℕ → ℝ} {cLam η cE cErr : ℝ}
    (hscale : SaddlePointScaleLower Λ cLam)
    (hmean : SaddlePointMeanLower μ Λ η)
    (henv : ∀ n, gridPrefixEnvelope m B (prefixC m B hm hB line)
      (prefixK m B hm hB line) (X n) A U ≤ exp (cE * scale n))
    (herr : ∀ n,
      exp (-cErr * (paperD n * scale n)) ≤ crtError n + charError n)
    (hexp : 2 * cE ≤ 2 * η * cLam - cErr)
    (hA : 0 ≤ 2 * η * cLam - cErr)
    (hinit : ∀ n, scale n < 0 →
      gridPrefixEnvelope m B (prefixC m B hm hB line)
          (prefixK m B hm hB line) (X n) A U ^ 2 ≤
        (crtError n + charError n) * μ n ^ 2) :
    GridPrefixCoordinateFit m B (prefixC m B hm hB line)
      (prefixK m B hm hB line) X A U μ crtError charError :=
  coordinateEnvelopeFit_of_saddle (env := fun n =>
      gridPrefixEnvelope m B (prefixC m B hm hB line)
        (prefixK m B hm hB line) (X n) A U) hscale hmean
    (fun n => gridPrefixEnvelope_nonneg_of m B (mul_ne_zero hm hB)
      (prefixC_pos m B hm hB line).le (prefixK_pos m B hm hB line).le
      (hX n) A U hU)
    henv herr hexp hA hinit

/-! ## Axiom audit -/

#print axioms coordinateEnvelopeFit_iff_normalized
#print axioms coordinateEnvelopeFit_iff_sqrt_normalized
#print axioms coordinateEnvelopeFit_of_normalized
#print axioms coordinateEnvelopeFit_of_sqrt_normalized
#print axioms coordinateEnvelopeFit_of_envelopeMass
#print axioms normalized_of_envelopeMass
#print axioms normalizedEnvelopeFit_of_envelopeMass
#print axioms mellinEnvelope_nonneg_of
#print axioms gridPrefixEnvelope_nonneg_of
#print axioms mellinCoordinateFit_of_envelopeMass
#print axioms mellinCoordinateFit_of_normalized
#print axioms coordinateEnergyBudget_of_mellinEnvelopeMass
#print axioms coordinateEnergyBudget_of_mellinNormalized
#print axioms gridPrefixCoordinateFit_of_envelopeMass
#print axioms gridPrefixCoordinateFit_of_normalized
#print axioms coordinateEnergyBudget_of_gridPrefixEnvelopeMass
#print axioms coordinateEnergyBudget_of_gridPrefixNormalized
#print axioms coordinateEnvelopeFit_of_saddle
#print axioms mellinCoordinateFit_of_saddle
#print axioms gridPrefixCoordinateFit_of_saddle

end Cogentic.RandomizedL20_2Fit
