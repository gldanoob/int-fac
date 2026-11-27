import Cogentic.RandomizedPaperLeafStatements

/-!
# L21.2: RH smooth numbers near almost all integer centres

`RandomizedPaperLeafStatements.PaperAnalyticAssumptions` has one opaque field
`l21_2 : RatedLeaf`, the elliptic-exceptional deletion fraction of blueprint
§2 C5.a.  This file decomposes that leaf into the explicit analytic inputs of the
manuscript's smooth-number estimate (`research/keybreak-private-elliptic-recognition.md`
§"Smooth numbers near almost all integer centers") and proves the `RatedLeaf`
and C5-loss-slot reductions.

## The manuscript statement

Fix `c > 0`, put `U = log X`, `T_X = sqrt (U log U)`, and `B = c T_X`.  Under RH,
for each sufficiently large `X` all but `O_A (X / (log X)^A)` integer centres
`p ∈ [X, 2X]` satisfy, for every fixed `A > 0`,

```
#{n : |n - p| < sqrt p, P⁺(n) ≤ exp B} ≥ sqrt p · exp (-(1/(2c) + o(1)) T_X).
```

The deletion fraction of the primes in a dyadic band is therefore
`η = exp (-c T_B)` per dyad; blueprint L21 states this as
`η = exp (-c T_B)` and uses it as the C5.a elliptic-exceptional loss.

## What is an input and what is proved

The four named ingredients of the note are represented as explicit
paper-level `Prop`s:

1. **Perron at `Re s = 2/3`** (`perronShift`).  The truncated Perron integral of
   `-ζ'/ζ (s + it)` started at `1 + 1/log v`, with the contour shifted to
   `perronRe = 2/3`, picks up only the residue at `1 - it` and has vertical,
   horizontal and prime-power errors
   `O (v^{2/3} U^C)`, `O (v U^C / X^3)` and `O (v^{1/2} log² (2v))`.
   `twisted_prime_sum` below *proves* the displayed twisted prime sum
   `Σ_{q ≤ v} (log q) q^{-it} = v^{1-it}/(1-it) + O (v^{2/3} U^C)` from it by
   absorbing the three error terms.
2. **Twisted `ζ'/ζ` prime sum** (`twistedPrimeSum`, an explicit finite sum over
   `Nat.Prime`) is the theorem `twisted_prime_sum`.  Partial summation with the
   weight `1/v` turns it into the Fourier gap bound (`fourierSupBound`,
   `fourierGap`, `supEps`); that step is an explicit input, not formalised here.
3. **Fourier `L²` comparison** (`plancherelSplit`, `fourierLow`,
   `fourierMiddle`, `fourierTail`).  These are the three frequency ranges of the
   note's Plancherel computation: `|t| ≤ 1` (the `k ε (1+ε)^{k-1}` term),
   `1 < |t| ≤ X^3` (the `4^k ((Δ|t|)^{-2k} + ε^{2k})` term) and `|t| > X^3`
   (the `h^{-4} X^{-9}` tail).  `l2_comparison` proves their sum is
   `O (exp (-(c/32) T_X))`, the note's `O (exp (-c₁ T_X))`.
4. **Tent smoothing** (`tentSmoothing`, `densityNormalization`).  Chebyshev on
   the `L²`-deficient set with the triangular kernel `K_h`, `h = 1/(10√X)`, and
   the polynomial density normalization give
   `badFraction ≤ polyFactor · l2Term`; the continuous reference count at a good
   centre is `√X exp (-R)` with
   `R = log 40 + log (kΔ) + k log k + k log (b/(2Δ))`.  The parameter arithmetic
   `k log k = (1/(2c) + o(1)) T_X`, `k log (b/(2Δ)) = o(T_X)` and
   `log (kΔ) = o(T_X)` is recorded as `kLogK`, `kLogB`, `kDeltaLog` and is used
   by `smoothCount_ge` to prove the manuscript's count lower bound.

The remaining inputs are growth facts: `U = log X` is much larger than
`log D = scale n` (`U_dominates`, the note's `T_B ≫ (log D)^m`) but at most
`D` (`U_le_exp`), the polynomial density factor is `exp (o(T_X))`
(`polyAbsorbs`), and the product parameters satisfy the paper's order
relations (`b_le_B`, `kLogK`, `kLogB`, `kDeltaLog`).

## The reduction

`loss n = badCount n / (X n + 1)` is the exceptional fraction of the dyad: a
genuine, nonnegative quotient of two explicit quantities, never set to zero.
The proved chain is

```
loss ≤ polyFactor · l2Term ≤ exp (o(T)) · exp (-(c/32) T) ≤ exp (-(c/64) T),
```

which is the manuscript rate `exp (-(c/64) T_X)`, and then, because
`T_X ≫ log D`,

```
loss ≤ exp (-B · scale n)   for every B > 0,
```

the paper's `D^{-B}` counting form.  `toRatedLeaf` packages
`(loss, rate = T_X, c = c/64, paper, ledger)` as the `RatedLeaf` of
`RandomizedPaperLeafStatements`; its `ledger` is the `B = 2` instance, exactly
the `C5Leaf.ellipticExceptional` slot.  `badCount_le_polynomial` restates the
`D^{-B}` form as the manuscript's `O_A (X / (log X)^A)`, and
`smooth_numbers_near_centres` combines it with `smoothCount_ge` into the
displayed smooth-count estimate.

No `sorry`, `admit`, `axiom`, or `native_decide`; the loss is not set to zero.
-/

namespace Cogentic.RandomizedL21_2

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## Explicit scales and the two prime sums -/

/-- `log X`, the paper's `U`. -/
def bandLog (X : ℕ → ℝ) (n : ℕ) : ℝ := Real.log (X n)

/-- The paper's `T_X = sqrt (U log U)`. -/
def paperRate (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (bandLog X n * Real.log (bandLog X n))

/-- The paper's stage-one log cutoff `B = c T_X`. -/
def logCutoff (c : ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ := c * paperRate X n

/-- The smoothness cutoff `y = exp B`. -/
def smoothCutoff (c : ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ := Real.exp (logCutoff c X n)

/-- The Perron contour is shifted to `Re s = 2/3`. -/
def perronRe : ℝ := 2 / 3

/-- The twisted prime sum `Σ_{q ≤ v, q prime} (log q) q^{-it}`, as an explicit
finite sum over `Nat.Prime`. -/
def twistedPrimeSum (v t : ℝ) : ℂ :=
  ∑ q ∈ Finset.range (⌊v⌋₊ + 1),
    if q.Prime then
      (Real.log q : ℂ) * Complex.exp (-(t : ℂ) * Complex.I * (Real.log q : ℂ))
    else 0

/-- The Perron main term `v^{1-it} / (1-it)`. -/
def twistedMain (v t : ℝ) : ℂ :=
  (v : ℂ) * Complex.exp (-(t : ℂ) * Complex.I * (Real.log v : ℂ)) /
    (1 - (t : ℂ) * Complex.I)

/-- The paper's `ε = e^{-a/3} U^{O(1)}`: the supremum of the Fourier gap. -/
def supEps (X a : ℕ → ℝ) (Ceps : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(a n) / 3) * (bandLog X n) ^ Ceps

/-- The logarithmic count loss
`R = log 40 + log (kΔ) + k log k + k log (b/(2Δ))`.  The paper's
`C₀ hX / (kΔ k! (b/(2Δ))^k)` becomes `√X exp (-R)` after `h = 1/(10√X)` and
`k! ≤ k^k`, and `exp (R)` is the density-normalization factor. -/
def representationLog (k spacing b : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log 40 + Real.log (k n * spacing n) + k n * Real.log (k n) +
    k n * Real.log (b n / (2 * spacing n))

/-! ## The decomposed L21.2 inputs -/

/-- The paper-level inputs behind the RH smooth-numbers-near-centres estimate.

The analytic content is the Perron/twisted-prime-sum pair, the Fourier `L²`
comparison, the tent smoothing / density normalization, and the growth
relations between the band size `X`, `log D = scale n` and the paper's
parameters `k, m, Δ, a, b`.  Each field is a manuscript statement; the module
docstring records its exact reading and provenance.

The data fields come first so that later fields can refer to them; the
manuscript inequalities are the eventual (`∀ᶠ n`) fields below. -/
structure L21_2Inputs where
  /-- The dyadic centre bound `X`. -/
  X : ℕ → ℝ
  /-- The stage-one constant `c` (the paper takes `c = 1/√2`). -/
  c : ℝ
  /-- Perron constant in the vertical error `O (v^{2/3} U^C)`. -/
  Kper : ℕ → ℝ
  /-- The absolute exponent `C` of the Perron/twisted-sum errors. -/
  Cper : ℝ
  /-- Exponent in `ε = e^{-a/3} U^{Ceps}`. -/
  Ceps : ℝ
  /-- The Fourier gap `μ̂ (t) - ν̂ (t)` of the discrete log-prime measure `μ`
  and Lebesgue probability measure `ν` on `[a, b]`. -/
  fourierGap : ℕ → ℝ → ℂ
  /-- The number `k` of prime factors, the paper's
  `k = ⌈r (1 + 2/log r)⌉` with `r = (U + 1)/B`. -/
  k : ℕ → ℝ
  /-- The log-centre `m = (U + (log 2)/2)/k`. -/
  m : ℕ → ℝ
  /-- The log-spacing `Δ = m / log k`. -/
  spacing : ℕ → ℝ
  /-- The lower log-cutoff `a = m - Δ`. -/
  a : ℕ → ℝ
  /-- The upper log-cutoff `b = m + Δ`. -/
  b : ℕ → ℝ
  /-- The count of distinct `e^B`-smooth integers in the neighbourhood
  `|n - p| < √p` of a good centre. -/
  smoothCount : ℕ → ℝ
  /-- The number of exceptional integer centres in `[X, 2X]`. -/
  badCount : ℕ → ℝ
  /-- The squared `L²` distance of the smoothed `k`-fold convolutions
  `μ^{*k} * K_h` and `ν^{*k} * K_h` (paper §1, "Mean-square comparison"). -/
  l2Term : ℕ → ℝ
  /-- Low-frequency contribution, `|t| ≤ 1`. -/
  lowTerm : ℕ → ℝ
  /-- Middle-frequency contribution, `1 < |t| ≤ X³`. -/
  middleTerm : ℕ → ℝ
  /-- High-frequency tail, `|t| > X³`. -/
  tailTerm : ℕ → ℝ
  /-- The explicit polynomial factor of the tent/density normalization. -/
  polyFactor : ℕ → ℝ
  /-- `X > 1`. -/
  X_gt_one : ∀ n, 1 < X n
  /-- `c > 0`. -/
  c_pos : 0 < c
  /-- The stage-one constant is at most one, as at the paper's `1/√2`. -/
  c_le_one : c ≤ 1
  /-- The Perron constant is nonnegative. -/
  Kper_nonneg : ∀ n, 0 ≤ Kper n
  /-- `C ≥ 2`: the prime-power error `v^{1/2} log² (2v)` is absorbed by
  `v^{2/3} U^C`. -/
  Cper_ge_two : 2 ≤ Cper
  /-- The exponent of `ε` is nonnegative. -/
  Ceps_nonneg : 0 ≤ Ceps
  /-- `k > 0`. -/
  k_pos : ∀ n, 0 < k n
  /-- `Δ > 0`. -/
  spacing_pos : ∀ n, 0 < spacing n
  /-- `b > 0`. -/
  b_pos : ∀ n, 0 < b n
  /-- The smooth count is nonnegative. -/
  smoothCount_nonneg : ∀ n, 0 ≤ smoothCount n
  /-- The exceptional count is nonnegative. -/
  badCount_nonneg : ∀ n, 0 ≤ badCount n
  /-- The squared distance is nonnegative. -/
  l2Term_nonneg : ∀ n, 0 ≤ l2Term n
  /-- The polynomial factor is positive. -/
  polyFactor_pos : ∀ n, 0 < polyFactor n
  /-- **Perron at `Re s = 2/3`** (paper §1, "Twisted prime sum").  Truncated
  Perron for `-ζ'/ζ (s + it)` at `v' = ⌊v⌋ + 1/2` and height `2X³`, shifted from
  `1 + 1/log v'` to `perronRe = 2/3`, leaves the residue at `1 - it` and the
  three errors: vertical `O (v^{2/3} U^C)` (including the `1/s` integral),
  horizontal `O (v U^C / X^3)`, and the prime-power removal
  `O (v^{1/2} log² (2v))`. -/
  perronShift : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
          + v * (bandLog X n) ^ Cper / X n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)
  /-- `U = log X` is at least `3`, the paper's "large `X`" range. -/
  U_ge_three : ∀ᶠ n : ℕ in atTop, 3 ≤ bandLog X n
  /-- `b ≤ B` eventually, the paper's prime-product cutoff lies below the
  smoothness cutoff `B = c T_X`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, b n ≤ logCutoff c X n
  /-- `B ≤ U/3` eventually: `c sqrt (U log U) ≤ U/3` for large `U`. -/
  B_le_U : ∀ᶠ n : ℕ in atTop, logCutoff c X n ≤ bandLog X n / 3
  /-- **Twisted prime sum by partial summation** (paper §1).  With the weight
  `1/v`, the twisted `ζ'/ζ` estimate gives
  `sup_{|t| ≤ X³} |μ̂ (t) - ν̂ (t)| ≤ ε = e^{-a/3} U^{Ceps}`.  This is the
  partial-summation step from `twisted_prime_sum`; it is an explicit input here. -/
  fourierSupBound : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ X n ^ 3 →
    ‖fourierGap n t‖ ≤ supEps X a Ceps n
  /-- `k > 1` eventually, so `log k > 0`. -/
  k_gt_one : ∀ᶠ n : ℕ in atTop, 1 < k n
  /-- `k log k = (1/(2c) + o(1)) T_X` (paper §1, "Choice of prime
  products").  The `o(1)` is encoded as an eventual bound for every `δ > 0`. -/
  kLogK : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    k n * Real.log (k n) ≤ ((1 / (2 * c)) + δ) * paperRate X n
  /-- `k log (b/(2Δ)) = O (k log log k) = o(T_X)` (paper §1). -/
  kLogB : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    k n * Real.log (b n / (2 * spacing n)) ≤ δ * paperRate X n
  /-- `log (kΔ) + log 40 = o(T_X)`: the polynomial density normalization
  (disjoint integer neighbourhoods and division by the prime density) is
  absorbed by the exponential rate. -/
  kDeltaLog : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    Real.log (k n * spacing n) + Real.log 40 ≤ δ * paperRate X n
  /-- **Tent smoothing and density normalization** (paper §1, "Central
  density", "Mean-square comparison").  With the triangular kernel `K_h` of
  mass one on `[-h, h]`, `h = 1/(10√X)`, the set of centres where the smoothed
  discrete density is below half the continuous reference has fraction at most
  `polyFactor · l2Term`.  `polyFactor` is the explicit polynomial factor
  `(2kΔ)² (1 + U)^{O(1)}` of the density normalization. -/
  tentSmoothing : ∀ᶠ n : ℕ in atTop,
    badCount n / (X n + 1) ≤ polyFactor n * l2Term n
  /-- **The density-normalization count** (paper §1, last paragraph).  At a
  good centre the neighbourhood contains at least
  `√X exp (-R)` distinct smooth integers, `R = log 40 + log (kΔ) + k log k +
  k log (b/(2Δ))`.  This is the paper's
  `C₀ hX / (kΔ k! (b/(2Δ))^k)` after `h = 1/(10√X)` and `k! ≤ k^k`. -/
  densityNormalization : ∀ᶠ n : ℕ in atTop,
    Real.sqrt (X n) * Real.exp (-(representationLog k spacing b n)) ≤ smoothCount n
  /-- **Plancherel range split**: the squared `L²` distance is at most the sum
  of the three frequency contributions. -/
  plancherelSplit : ∀ᶠ n : ℕ in atTop,
    l2Term n ≤ lowTerm n + middleTerm n + tailTerm n
  /-- **Low frequency** (`|t| ≤ 1`): the transform difference before smoothing
  is at most `k ε (1+ε)^{k-1}`, so this term is
  `exp (-(2c/3 + o(1)) T_X)` (paper §1: `2a/3 ~ (2c/3) T_X`). -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    lowTerm n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate X n)
  /-- **Middle frequency** (`1 < |t| ≤ X³`): the square is at most
  `O (4^k) ((Δ|t|)^{-2k} + ε^{2k})`, whose integral is
  `exp (-(1/c + o(1)) T_X)` (paper §1: `2k log (Δ/2) ~ T_X/c`). -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    middleTerm n ≤ Real.exp (-((1 / c) - δ) * paperRate X n)
  /-- **High frequency** (`|t| > X³`): the mass bound and
  `|K̂_h (t)| ≪ (h|t|)^{-2}` give a fixed negative power of `X`, hence
  `exp (-ω (T_X))`: the bound holds for every `δ > 0`. -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    tailTerm n ≤ Real.exp (-δ * paperRate X n)
  /-- **Polynomial absorption**: `(log X)^{O(1)} = exp (o(T_X))`, so the
  density-normalization factor is beaten by `exp (δ T_X)` for every `δ > 0`. -/
  polyAbsorbs : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    polyFactor n ≤ Real.exp (δ * paperRate X n)
  /-- **Two-scale separation**: `log X` dominates every fixed power of
  `log D = scale n`.  The paper's `T_B ≫ (log D)^m` for every fixed `m` is
  stronger; the quadratic domination stated here already gives
  `T_X = sqrt (U log U) ≫ scale n`, which is what the `D^{-B}` ledger needs. -/
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog X n
  /-- `log X` is at most `D = exp (scale n)`, so the polynomial form
  `X (log X)^{-A}` of the exceptional count follows from the `D^{-B}` form. -/
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog X n ≤ Real.exp (scale n)

namespace L21_2Inputs

variable (I : L21_2Inputs)

/-- `U = log X`. -/
abbrev U (n : ℕ) : ℝ := bandLog I.X n

/-- `T_X = sqrt (U log U)`. -/
abbrev T (n : ℕ) : ℝ := paperRate I.X n

/-- `B = c T_X`. -/
abbrev B (n : ℕ) : ℝ := logCutoff I.c I.X n

/-- The Fourier sup bound `ε = e^{-a/3} U^{Ceps}`. -/
abbrev eps (n : ℕ) : ℝ := supEps I.X I.a I.Ceps n

/-- The triangular half-width `h = 1/(10√X)`. -/
abbrev tentWidth (n : ℕ) : ℝ := 1 / (10 * Real.sqrt (I.X n))

/-- Half the continuous reference density `1/(2kΔ)`. -/
abbrev halfRef (n : ℕ) : ℝ := 1 / (4 * I.k n * I.spacing n)

/-- The exceptional fraction of the dyadic band: the number of bad centres
divided by `X + 1`. -/
abbrev badFraction (n : ℕ) : ℝ := I.badCount n / (I.X n + 1)

/-- The L21.2 loss: the elliptic-exceptional deletion fraction. -/
abbrev loss (n : ℕ) : ℝ := I.badFraction n

/-! ## Elementary positivity and identification lemmas -/

theorem X_ge_one (n : ℕ) : 1 ≤ I.X n := le_of_lt (I.X_gt_one n)

theorem X_pos (n : ℕ) : 0 < I.X n := lt_of_lt_of_le zero_lt_one (I.X_ge_one n)

theorem U_pos (n : ℕ) : 0 < I.U n := by
  unfold U bandLog
  exact Real.log_pos (I.X_gt_one n)

theorem T_nonneg (n : ℕ) : 0 ≤ I.T n := by
  unfold T paperRate
  exact Real.sqrt_nonneg _

theorem T_def (n : ℕ) :
    I.T n = Real.sqrt (I.U n * Real.log (I.U n)) := by
  simp [T, U, paperRate, bandLog]

theorem eps_def (n : ℕ) :
    I.eps n = Real.exp (-(I.a n) / 3) * (I.U n) ^ I.Ceps := by
  simp [eps, supEps, U, bandLog]

theorem c_rate_pos : 0 < I.c / 64 := div_pos I.c_pos (by norm_num)

theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n := by
  unfold loss badFraction
  exact div_nonneg (I.badCount_nonneg n) (by linarith [I.X_ge_one n])

/-- `badCount = loss · (X + 1)`: the exceptional fraction is a genuine quotient,
not a freely chosen number. -/
theorem badCount_eq_loss_mul (n : ℕ) : I.badCount n = I.loss n * (I.X n + 1) := by
  unfold loss badFraction
  have hX : (I.X n + 1) ≠ 0 := by linarith [I.X_ge_one n]
  field_simp [hX]

/-- `U = log X` tends to infinity, since `1 · (scale n)² ≤ U n`. -/
theorem U_grows : Tendsto I.U atTop atTop := by
  refine tendsto_atTop_mono' atTop (I.U_dominates 1 zero_lt_one) ?_
  simpa [pow_two, U] using scale_grows.atTop_mul_atTop₀ scale_grows

/-! ## The twisted prime sum from the Perron shift -/

/-- **Twisted `ζ'/ζ` prime sum** (paper §1).  The Perron shift to `Re s = 2/3`
gives, for `2 ≤ v ≤ e^B` and `|t| ≤ X³`,
`Σ_{q ≤ v} (log q) q^{-it} = v^{1-it}/(1-it) + O (v^{2/3} U^C)`.
The three Perron errors are absorbed using `B ≤ U/3` and `U ≥ 3`. -/
theorem twisted_prime_sum :
    ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v → v ≤ smoothCutoff I.c I.X n →
      |t| ≤ I.X n ^ 3 →
        ‖twistedPrimeSum v t - twistedMain v t‖ ≤
          (3 * I.Kper n) * v ^ (2 / 3 : ℝ) * (I.U n) ^ I.Cper := by
  filter_upwards [I.perronShift, I.U_ge_three, I.B_le_U] with n hper hU3 hBU
  intro v t hv hvB ht
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hv1 : 1 ≤ v := le_trans (by norm_num) hv
  have hU3' : 3 ≤ I.U n := by simpa [U] using hU3
  have hU0 : 0 < I.U n := lt_of_lt_of_le (by norm_num) hU3'
  have hU1 : 1 ≤ I.U n := by linarith
  -- `v ≤ exp (U/3)`
  have hvExp : v ≤ Real.exp (I.U n / 3) := by
    have h : smoothCutoff I.c I.X n ≤ Real.exp (I.U n / 3) := by
      rw [smoothCutoff]
      exact Real.exp_le_exp.mpr (by simpa [U] using hBU)
    exact hvB.trans h
  -- `X^3 = exp (3U)`
  have hX3 : I.X n ^ 3 = Real.exp (3 * I.U n) := by
    have hX : I.X n = Real.exp (I.U n) := by
      rw [U, bandLog, Real.exp_log (I.X_pos n)]
    calc I.X n ^ 3 = Real.exp (I.U n) ^ 3 := by rw [hX]
      _ = Real.exp (3 * I.U n) := by
          simpa using (Real.exp_nat_mul (I.U n) 3).symm
  -- `v^{1/3} ≤ X^3`
  have hv13 : v ^ (1 / 3 : ℝ) ≤ I.X n ^ 3 := by
    have hexp : Real.exp (I.U n / 3) ^ (1 / 3 : ℝ) = Real.exp (I.U n / 9) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    have h1 : v ^ (1 / 3 : ℝ) ≤ Real.exp (I.U n / 3) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt hv0) hvExp (by norm_num)
    rw [hexp] at h1
    refine h1.trans ?_
    rw [hX3]
    exact Real.exp_le_exp.mpr (by nlinarith)
  -- `v ≤ v^{2/3} X^3`
  have hvsplit : v ≤ v ^ (2 / 3 : ℝ) * I.X n ^ 3 := by
    have hveq : v = v ^ ((1 / 3 : ℝ) + 2 / 3) := by
      rw [show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
    have hvs : v ^ ((1 / 3 : ℝ) + 2 / 3) = v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) :=
      Real.rpow_add hv0 _ _
    have hm : v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) ≤
        I.X n ^ 3 * v ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hv13 (Real.rpow_nonneg (le_of_lt hv0) _)
    exact hveq.trans_le (hvs.le.trans (hm.trans (le_of_eq (show
  I.X n ^ 3 * v ^ (2 / 3 : ℝ) = v ^ (2 / 3 : ℝ) * I.X n ^ 3 by ring))))
  -- horizontal term
  have hHor : v * (I.U n) ^ I.Cper / I.X n ^ 3 ≤
      v ^ (2 / 3 : ℝ) * (I.U n) ^ I.Cper := by
    have hX3pos : 0 < I.X n ^ 3 := pow_pos (I.X_pos n) 3
    rw [div_le_iff₀ hX3pos]
    have hveq : v * (I.U n) ^ I.Cper =
        (v / I.X n ^ 3) * I.X n ^ 3 * (I.U n) ^ I.Cper := by
      rw [div_mul_cancel₀ v hX3pos.ne']
    have hdiv : v / I.X n ^ 3 ≤ v ^ (2 / 3 : ℝ) := by
      rw [div_le_iff₀ hX3pos]
      exact hvsplit
    have hm : (v / I.X n ^ 3) * I.X n ^ 3 * (I.U n) ^ I.Cper ≤
        (v ^ (2 / 3 : ℝ) * I.X n ^ 3) * (I.U n) ^ I.Cper :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdiv (le_of_lt hX3pos))
        (Real.rpow_nonneg (le_of_lt hU0) _)
    exact hveq.trans_le (hm.trans (le_of_eq (show
  (v ^ (2 / 3 : ℝ) * I.X n ^ 3) * (I.U n) ^ I.Cper =
    v ^ (2 / 3 : ℝ) * (I.U n) ^ I.Cper * I.X n ^ 3 by ring)))
  -- prime-power term
  have hPow : Real.sqrt v * (Real.log (2 * v)) ^ 2 ≤
      v ^ (2 / 3 : ℝ) * (I.U n) ^ I.Cper := by
    have hsqrt : Real.sqrt v ≤ v ^ (2 / 3 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hv1
        (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3)
    have hv2 : 2 * v ≤ Real.exp (I.U n) := by
      have h2 : 2 * v ≤ 2 * Real.exp (I.U n / 3) :=
        mul_le_mul_of_nonneg_left hvExp (by norm_num)
      have hlog2 : Real.log 2 ≤ (2 / 3 : ℝ) * I.U n := by
        have h2le : Real.log 2 ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        nlinarith
      calc 2 * v ≤ 2 * Real.exp (I.U n / 3) := h2
        _ = Real.exp (Real.log 2) * Real.exp (I.U n / 3) := by
            rw [Real.exp_log (by norm_num)]
        _ = Real.exp (Real.log 2 + I.U n / 3) := by rw [← Real.exp_add]
        _ ≤ Real.exp (I.U n) := Real.exp_le_exp.mpr (by linarith)
    have hlogv : Real.log (2 * v) ≤ I.U n := by
      exact (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 2 * v)).mpr hv2
    have hsq : (Real.log (2 * v)) ^ 2 ≤ (I.U n) ^ (2 : ℝ) := by
      have hnn : 0 ≤ Real.log (2 * v) :=
        Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * v)
      rw [Real.rpow_two]
      nlinarith
    have hupow : (I.U n) ^ (2 : ℝ) ≤ (I.U n) ^ I.Cper :=
      Real.rpow_le_rpow_of_exponent_le hU1 I.Cper_ge_two
    have hlog : (Real.log (2 * v)) ^ 2 ≤ (I.U n) ^ I.Cper := hsq.trans hupow
    exact mul_le_mul hsqrt hlog (by positivity)
      (Real.rpow_nonneg (le_of_lt hv0) _)
  have hbracket :
      v ^ (2 / 3 : ℝ) * (I.U n) ^ I.Cper
        + v * (I.U n) ^ I.Cper / I.X n ^ 3
        + Real.sqrt v * (Real.log (2 * v)) ^ 2
      ≤ 3 * (v ^ (2 / 3 : ℝ) * (I.U n) ^ I.Cper) := by
    nlinarith [hHor, hPow]
  exact (hper v t hv hvB ht).trans
    ((mul_le_mul_of_nonneg_left hbracket (I.Kper_nonneg n)).trans_eq (by ring))

/-- **`T_X` dominates every fixed multiple of `log D = scale n`.**  This is the
paper's `T_B ≫ (log D)^m`: `U = log X` is at least `(a+1)² (log D)²`, so
`T_X = sqrt (U log U) ≥ a log D` once `log U ≥ 1`. -/
theorem T_dominates (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, a * scale n ≤ I.T n := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hlogU : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (I.U n) :=
    (Real.tendsto_log_atTop.comp I.U_grows).eventually_ge_atTop 1
  filter_upwards [I.U_dominates (a ^ 2) ha2, hlogU,
    scale_grows.eventually_ge_atTop 0] with n hU hlog hH0
  have hUineq : a ^ 2 * scale n ^ 2 ≤ I.U n := by simpa [U] using hU
  have hU0 : 0 ≤ I.U n :=
    (mul_nonneg ha2.le (sq_nonneg (scale n))).trans hUineq
  have hlog1 : 0 ≤ Real.log (I.U n) := le_trans zero_le_one hlog
  have hsq : a ^ 2 * scale n ^ 2 ≤ I.U n * Real.log (I.U n) := by
    calc a ^ 2 * scale n ^ 2 = (a ^ 2 * scale n ^ 2) * 1 := by ring
      _ ≤ (a ^ 2 * scale n ^ 2) * Real.log (I.U n) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg ha2.le (sq_nonneg _))
      _ ≤ I.U n * Real.log (I.U n) :=
          mul_le_mul_of_nonneg_right hUineq hlog1
  have hsqrt : Real.sqrt (a ^ 2 * scale n ^ 2) ≤ I.T n := by
    unfold T paperRate
    exact Real.sqrt_le_sqrt hsq
  have heq : Real.sqrt (a ^ 2 * scale n ^ 2) = a * scale n := by
    rw [show a ^ 2 * scale n ^ 2 = (a * scale n) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg ha.le hH0)]
  rwa [heq] at hsqrt

/-- `T_X → ∞`, hence it beats every fixed multiple of `log D`. -/
theorem T_grows : Tendsto I.T atTop atTop := by
  have hdom : (fun n => scale n) ≤ᶠ[atTop] I.T := by
    filter_upwards [I.T_dominates 1 zero_lt_one] with n h
    simpa using h
  exact tendsto_atTop_mono' atTop hdom scale_grows

/-! ## The Fourier `L²` comparison -/

/-- **Fourier `L²` comparison** (paper §1, "Mean-square comparison").  The three
Plancherel frequency ranges each contribute at most `exp (-(c/16) T_X)`, so their
sum is at most `exp (-(c/32) T_X)`.  This is the note's
`O (exp (-c₁ T_X))` with `c₁ = c/32`. -/
theorem l2_comparison :
    ∀ᶠ n : ℕ in atTop, I.l2Term n ≤ Real.exp (-((I.c / 32) * I.T n)) := by
  have hc8 : 0 < I.c / 8 := div_pos I.c_pos (by norm_num)
  have hc16 : 0 < I.c / 16 := div_pos I.c_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdom : 0 < 32 * Real.log 3 / I.c :=
    div_pos (mul_pos (by norm_num) hlog3) I.c_pos
  filter_upwards [I.fourierLow (I.c / 8) hc8, I.fourierMiddle (I.c / 8) hc8,
    I.fourierTail (I.c / 16) hc16, I.plancherelSplit,
    I.T_dominates (32 * Real.log 3 / I.c) hdom,
    scale_grows.eventually_ge_atTop 1, Eventually.of_forall I.T_nonneg]
    with n hlow hmid htail hsplit hTdom hH hTnn
  have hlow0 : I.lowTerm n ≤ Real.exp (-((2 * I.c / 3 - I.c / 8) * I.T n)) := by
    refine hlow.trans (le_of_eq ?_)
    congr 1
    ring
  have hmid0 : I.middleTerm n ≤ Real.exp (-((1 / I.c - I.c / 8) * I.T n)) := by
    refine hmid.trans (le_of_eq ?_)
    congr 1
    ring
  have htail0 : I.tailTerm n ≤ Real.exp (-((I.c / 16) * I.T n)) := by
    refine htail.trans (le_of_eq ?_)
    congr 1
    ring
  have hlow' : I.lowTerm n ≤ Real.exp (-((I.c / 16) * I.T n)) := by
    refine hlow0.trans (Real.exp_le_exp.mpr ?_)
    have hcoef : 0 ≤ (2 * I.c / 3 - I.c / 8) - I.c / 16 := by linarith
    nlinarith [mul_nonneg hcoef hTnn]
  have hmid' : I.middleTerm n ≤ Real.exp (-((I.c / 16) * I.T n)) := by
    refine hmid0.trans (Real.exp_le_exp.mpr ?_)
    have hc2 : I.c ^ 2 ≤ 1 := by nlinarith [I.c_pos, I.c_le_one]
    have hcoef : I.c / 16 ≤ 1 / I.c - I.c / 8 := by
      have hcpos : 0 < I.c := I.c_pos
      have hsplit : 1 / I.c - I.c / 8 - I.c / 16 = (16 - 3 * I.c ^ 2) / (16 * I.c) := by
        field_simp [hcpos.ne']
        ring
      have hnonneg : 0 ≤ 1 / I.c - I.c / 8 - I.c / 16 := by
        rw [hsplit]
        exact div_nonneg (by nlinarith) (by positivity)
      linarith
    have hprod : 0 ≤ (1 / I.c - I.c / 8 - I.c / 16) * I.T n :=
      mul_nonneg (by linarith) hTnn
    nlinarith
  have htail' : I.tailTerm n ≤ Real.exp (-((I.c / 16) * I.T n)) := htail0
  have hsum : I.l2Term n ≤ 3 * Real.exp (-((I.c / 16) * I.T n)) := by
    have := hsplit
    nlinarith [hlow', hmid', htail']
  have hTbig : 32 * Real.log 3 / I.c ≤ I.T n := by
    have hpos : 0 ≤ 32 * Real.log 3 / I.c := hdom.le
    have h1 : 32 * Real.log 3 / I.c ≤ (32 * Real.log 3 / I.c) * scale n := by
      nlinarith
    exact h1.trans hTdom
  have h3 : (3 : ℝ) ≤ Real.exp ((I.c / 32) * I.T n) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    apply Real.exp_le_exp.mpr
    have hcpos : 0 < I.c := I.c_pos
    have hcalc : (I.c / 32) * (32 * Real.log 3 / I.c) = Real.log 3 := by
      field_simp [hcpos.ne']
    have hmul : (I.c / 32) * (32 * Real.log 3 / I.c) ≤ (I.c / 32) * I.T n :=
      mul_le_mul_of_nonneg_left hTbig (by positivity)
    linarith
  calc I.l2Term n ≤ 3 * Real.exp (-((I.c / 16) * I.T n)) := hsum
    _ ≤ Real.exp ((I.c / 32) * I.T n) * Real.exp (-((I.c / 16) * I.T n)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = Real.exp (-((I.c / 32) * I.T n)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ## The smooth-count lower bound -/

/-- **The manuscript's smooth-count lower bound.**  For every `δ > 0`, a good
centre has at least `√X exp (-(1/(2c) + δ) T_X)` smooth integers in its
neighbourhood.  This is the paper's
`k log k = (1/(2c) + o(1)) T_X` and `k log (b/(2Δ)) = o(T_X)` applied to the
density-normalization count. -/
theorem smoothCount_ge (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (I.X n) * Real.exp (-((1 / (2 * I.c)) + δ) * I.T n) ≤
        I.smoothCount n := by
  have h3 : 0 < δ / 3 := by linarith
  filter_upwards [I.densityNormalization, I.kLogK (δ / 3) h3, I.kLogB (δ / 3) h3,
    I.kDeltaLog (δ / 3) h3] with n hdens hk hb hkd
  have hlog : representationLog I.k I.spacing I.b n ≤
      ((1 / (2 * I.c)) + δ) * I.T n := by
    unfold representationLog
    nlinarith
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)).trans hdens
  linarith

/-! ## The loss at the manuscript rate and its `D^{-B}` form -/

/-- **The manuscript's rate for the exceptional fraction.**
`loss ≤ exp (-(c/64) T_X)`: the tent-smoothed `L²` comparison gives
`exp (-(c/32) T_X)` and the polynomial density factor costs `exp (o(T_X))`. -/
theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.c / 64) * I.T n)) := by
  have hc64 : 0 < I.c / 64 := div_pos I.c_pos (by norm_num)
  filter_upwards [I.tentSmoothing, I.l2_comparison, I.polyAbsorbs (I.c / 64) hc64]
    with n htent hl2 hpoly
  calc I.loss n ≤ I.polyFactor n * I.l2Term n := htent
    _ ≤ Real.exp ((I.c / 64) * I.T n) * Real.exp (-((I.c / 32) * I.T n)) :=
        mul_le_mul hpoly hl2 (I.l2Term_nonneg n) (Real.exp_pos _).le
    _ = Real.exp (-((I.c / 64) * I.T n)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- The uniform `D^{-B}` form: the exceptional fraction is at most
`exp (-B log D)` for every `B > 0`.  This is the paper's dyadic-counting form
that the `RatedLeaf.ledger` field quotes at `B = 2`. -/
theorem loss_le_exp_neg (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-B * scale n) := by
  have hdom : 0 < 64 * B / I.c := div_pos (mul_pos (by norm_num) hB) I.c_pos
  filter_upwards [I.loss_le_paper, I.T_dominates (64 * B / I.c) hdom] with n hp hT
  refine hp.trans (Real.exp_le_exp.mpr ?_)
  have hcpos : 0 < I.c := I.c_pos
  have hmul : (I.c / 64) * ((64 * B / I.c) * scale n) = B * scale n := by
    field_simp [hcpos.ne']
  have hle : (I.c / 64) * ((64 * B / I.c) * scale n) ≤ (I.c / 64) * I.T n :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  linarith

/-- The `RatedLeaf` rate domination: `B log D ≤ (c/64) T_X`. -/
theorem rate_dominates (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, B * scale n ≤ (I.c / 64) * I.T n := by
  have hdom : 0 < 64 * B / I.c := div_pos (mul_pos (by norm_num) hB) I.c_pos
  filter_upwards [I.T_dominates (64 * B / I.c) hdom] with n hT
  have hcpos : 0 < I.c := I.c_pos
  have hmul : (I.c / 64) * ((64 * B / I.c) * scale n) = B * scale n := by
    field_simp [hcpos.ne']
  have hle : (I.c / 64) * ((64 * B / I.c) * scale n) ≤ (I.c / 64) * I.T n :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  linarith

/-- The `RatedLeaf` ledger: the `B = 2` instance. -/
theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  I.loss_le_exp_neg 2 (by norm_num)

/-- **The manuscript's `O_A (X (log X)^{-A})` exceptional count.**  The `D^{-B}`
form of `loss`, with `B = 2A` and `log X ≤ log D = scale n`, gives at most
`2X (log X)^{-A}` exceptional integer centres in the dyad. -/
theorem badCount_le_polynomial (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop,
      I.badCount n ≤ 2 * I.X n * Real.exp (-(A * Real.log (I.U n))) := by
  have h2A : 0 < 2 * A := by linarith
  filter_upwards [I.loss_le_exp_neg (2 * A) h2A, I.U_le_exp,
    I.U_ge_three] with n hloss hUle hU3
  have hX1 : 0 ≤ I.X n + 1 := by linarith [I.X_ge_one n]
  have hXpos : 0 < I.X n := I.X_pos n
  have hU3' : 3 ≤ I.U n := by simpa [U] using hU3
  have hUpos : 0 < I.U n := lt_of_lt_of_le (by norm_num) hU3'
  have hUle' : I.U n ≤ Real.exp (scale n) := by simpa [U] using hUle
  have hlogU : Real.log (I.U n) ≤ scale n :=
    (Real.log_le_iff_le_exp hUpos).mpr hUle'
  have hexp : Real.exp (-(2 * A) * scale n) ≤
      Real.exp (-(A * Real.log (I.U n))) := by
    apply Real.exp_le_exp.mpr
    have hmul : A * Real.log (I.U n) ≤ A * scale n :=
      mul_le_mul_of_nonneg_left hlogU hA.le
    have hlogU0 : 0 ≤ Real.log (I.U n) :=
      Real.log_nonneg (by linarith : (1 : ℝ) ≤ I.U n)
    nlinarith
  have hmain : I.badCount n = I.loss n * (I.X n + 1) := I.badCount_eq_loss_mul n
  rw [hmain]
  have h1 : I.loss n * (I.X n + 1) ≤ Real.exp (-(2 * A) * scale n) * (I.X n + 1) :=
    mul_le_mul_of_nonneg_right hloss hX1
  have h2 : Real.exp (-(2 * A) * scale n) * (I.X n + 1) ≤
      Real.exp (-(A * Real.log (I.U n))) * (2 * I.X n) := by
    have hXle : I.X n + 1 ≤ 2 * I.X n := by linarith [I.X_ge_one n]
    exact mul_le_mul hexp hXle hX1 (Real.exp_pos _).le
  exact h1.trans (h2.trans (le_of_eq (by ring)))

/-- **The manuscript's smooth-numbers-near-centres estimate.**  For every fixed
`A > 0` and `δ > 0`, at most `2X (log X)^{-A}` integer centres in `[X, 2X]` are
exceptional, and at every good centre the neighbourhood `|n - p| < √p` contains
at least `√X exp (-(1/(2c) + δ) T_X)` smooth integers. -/
theorem smooth_numbers_near_centres (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      I.badCount n ≤ 2 * I.X n * Real.exp (-(A * Real.log (I.U n))) ∧
        Real.sqrt (I.X n) * Real.exp (-((1 / (2 * I.c)) + δ) * I.T n) ≤
          I.smoothCount n := by
  filter_upwards [I.badCount_le_polynomial A hA, I.smoothCount_ge δ hδ] with n h1 h2
  exact ⟨h1, h2⟩

/-! ## The `RatedLeaf` and the C5 loss slot -/

/-- **The L21.2 `RatedLeaf`.**  Its deficit is the exceptional fraction, its
manuscript rate is `T_X = sqrt (log X log log X)`, and its explicit ledger is the
`D^{-B}` counting form proved above. -/
def toRatedLeaf : RatedLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  rate := I.T
  c := I.c / 64
  c_pos := I.c_rate_pos
  paper := I.loss_le_paper
  ledger := I.loss_le_ledger

/-- The `C5Leaf.ellipticExceptional` slot, when identified with this loss, is
eventually at most `exp (-2 * scale n)`. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = I.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  rw [h]
  exact I.loss_le_ledger

end L21_2Inputs

/-! ## Reassembly of the paper assumptions -/

/-- `PaperAnalyticAssumptions` with the L21.2 leaf removed.  The other eleven
fields are exactly those of `PaperAnalyticAssumptions`. -/
structure PaperAnalyticAssumptionsWithoutL21_2
    (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) where
  l18_4 : SubexpLeaf
  l19_4 : SubexpLeaf
  l19_5 : SubexpLeaf
  l19_6 : SubexpLeaf
  l20_2 : ConcentrationLeaf
  l20_4 : SubexpLeaf
  l27_1 : RatedLeaf
  l30 : SubexpLeaf
  l34 : RatedLeaf
  l4_l25_l36 : AlgebraicLeaf
  p1 : P1Leaf

/-- Reassemble the full paper assumptions from the eleven remaining leaves and
an explicit L21.2 `RatedLeaf`. -/
def PaperAnalyticAssumptionsWithoutL21_2.toPaper
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptionsWithoutL21_2 E C) (l21_2 : RatedLeaf) :
    PaperAnalyticAssumptions E C where
  l18_4 := P.l18_4
  l19_4 := P.l19_4
  l19_5 := P.l19_5
  l19_6 := P.l19_6
  l20_2 := P.l20_2
  l20_4 := P.l20_4
  l21_2 := l21_2
  l27_1 := P.l27_1
  l30 := P.l30
  l34 := P.l34
  l4_l25_l36 := P.l4_l25_l36
  p1 := P.p1

/-- The eleven remaining leaves plus the decomposed L21.2 inputs give the full
paper assumptions. -/
def paperAssumptions_of_L21_2Inputs
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptionsWithoutL21_2 E C) (I : L21_2Inputs) :
    PaperAnalyticAssumptions E C :=
  P.toPaper I.toRatedLeaf

/-! ## Axiom audit -/

#print axioms L21_2Inputs.twisted_prime_sum
#print axioms L21_2Inputs.l2_comparison
#print axioms L21_2Inputs.smoothCount_ge
#print axioms L21_2Inputs.loss_le_paper
#print axioms L21_2Inputs.T_dominates
#print axioms L21_2Inputs.loss_le_exp_neg
#print axioms L21_2Inputs.badCount_le_polynomial
#print axioms L21_2Inputs.smooth_numbers_near_centres
#print axioms L21_2Inputs.toRatedLeaf
#print axioms L21_2Inputs.slot_le
#print axioms PaperAnalyticAssumptionsWithoutL21_2.toPaper
#print axioms paperAssumptions_of_L21_2Inputs

end

end Cogentic.RandomizedL21_2
