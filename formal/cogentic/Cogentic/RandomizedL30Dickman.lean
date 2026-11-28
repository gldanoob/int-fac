import Cogentic.RandomizedL30CentralCount
import Cogentic.RandomizedL30SmoothDensity

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# L30: the Dickman/short-interval form of the sharp central count

`Cogentic/RandomizedL30CentralCount` isolated the smallest explicit analytic
field of the L30 endpoint,

```
YounisOddPaperSharpCount c p ε :
  ∀ᶠ n, c p^{3/2} exp (-(u log u)) ≤ centralOddSmoothCount p (paperT p) (paperError ε) n ,
```

with `u = paperDensityU p ε n = 2 log (p n) / ((1 + ε) t_p n)`, and proved that
this `p^{3/2}` form and the interval-length form
`YounisOddPaperSharpIntervalCount` differ only by the forced constant `4`.

This file writes the same estimate in the language of the Dickman/short-interval
density, and records exactly what is *not* available in the current library.

## What is defined

* `dickmanRho u = exp (-(u log u))`, the saddle-point (leading-order) Dickman
  factor.  This is not the exact recursive Dickman function `ρ`, but it is
  precisely the factor appearing in the sharp paper estimate.

* `SharpCentralSmoothCount c p ε`, the density estimate for **all** `y`-smooth
  integers in the central interval `(p² - p^{3/2}/2, p²]`:
  `c p^{3/2} ρ(u) ≤ # {m ∈ interval : m is y-smooth}`.

* `SharpCentralSmoothIntervalDensity c p ε`, the same estimate normalised by
  the interval cardinality.  `sharpCentralSmoothCount_iff_interval` proves the
  two forms are equivalent up to the forced constant `4`, exactly as for the
  odd count.

* `CentralOddHalfParity θ p ε`, the fraction `θ` of the central smooth integers
  that satisfy the odd-half parity `m ≡ 2 (mod 4)`.

* `BuchstabLargePrimeShortIntervalLower c p ε`, the explicit missing analytic
  input: the large-prime (`P > sqrt y`) part of the Buchstab convolution already
  has the sharp size.

## What is proved

* `sharpCentralSmoothCount_of_oddSmoothCount`: the odd-half sharp count implies
  the all-smooth sharp count (the odd-half set is a subset).

* `sharpCentralOddSmoothCount_of_smoothDensity_parity`: the all-smooth sharp
  count together with the parity fraction `θ` gives the odd-half sharp count
  with constant `θ c`.  The special cases `θ = 1/2` and `θ = 3/8` are recorded.

* `buchstabOnePairs_image_subset`, `buchstabOnePairs_injOn` and
  `centralSmoothOrders_subset_buchstabImage`: the one-prime Buchstab map
  `(P, a) ↦ a P`, over pairs with `P` prime and `a` `P`-smooth, is a
  *bijection* onto the central smooth orders (for `p ≥ 2`).  Hence
  `buchstabOnePairs_card_eq_smoothCount` is an exact identity, not an
  inequality.  `centralSmoothOrders_card_eq_large_add_small` splits this count
  exactly into the large-prime (`P > sqrt y`) and small-prime parts.

* `sharpCentralSmoothCount_of_buchstabLargePrimeLower`: a lower bound for the
  `P > sqrt y` Buchstab sub-count of the sharp size implies the all-smooth
  sharp count.

* `sharpCentralOddSmoothCount_iff_oddIntervalDensity`: the odd-half Dickman
  interval density is equivalent to `SharpCentralOddSmoothCount` up to the
  forced constant `4`.

* `buchstabLargePrimeShortIntervalLower_smallWitness`: the residual is
  inhabited at the explicit schedule `p = 9`, `y = 81`, by the pair
  `(P, a) = (71, 1)`; `sharpCentralSmoothCount_smallWitness` is the resulting
  all-smooth density with `c = 1/27`.

## The exact residual

The sharp estimate is **not** proved here.  There are two independent missing
ingredients, both stated as explicit `Prop`s and neither assumed:

1. `BuchstabLargePrimeShortIntervalLower c p ε`: a lower bound of order
   `c p^{3/2} ρ(u)` for the number of pairs `(P, a)` with `P` prime,
   `sqrt y < P ≤ y`, `a` `P`-smooth, and `a P` in the central interval.  This
   is the large-prime Buchstab convolution.  The Rankin/saddle machinery of
   `RandomizedL30SharpRankin` gives only the *upper* bound for the same
   convolution; Mathlib's `Nat.smoothNumbers` API is purely combinatorial and
   contains no Buchstab/de Bruijn lower bound.

2. `CentralOddHalfParity θ p ε` with `θ > 0`: the odd-half (`m % 4 = 2`)
   equidistribution of smooth integers in the central interval.  A lower bound
   for all smooth integers does not imply a lower bound for the `m % 4 = 2`
   subset, so this parity transfer is a separate analytic statement about
   smooth numbers in residue classes.

`sharpCentralOddSmoothIntervalCount_of_buchstabLargePrime_parity` composes the
two reductions and yields `YounisOddPaperSharpIntervalCount (θ c) p ε`.

## Relation to the existing smooth-number files

* `RandomizedSmoothDensity.smoothNumberMass` and
  `RandomizedL20_2Saddle.SmoothNumberCountLower` are *global* statements.
  The mass inequality `smoothNumberMass_ge_count_mul_endpoint` gives
  `count ≤ mass · X^α`, i.e. it converts a mass estimate into an upper bound
  on the count.  The only unconditional `SmoothNumberCountLower` instance
  (`RandomizedL20_2SmoothLower.smoothNumberCountLower_twoPow`) is the
  contrived powers-of-two pair `(X, y) = (2^{⌈exp(cD log D)⌉}, 2)`, not the
  paper-regime pair.  Neither supplies the short-interval lower bound needed
  here.

* `SmoothDerivative.boxed_ordinary_singular_loss_sharp` and
  `SaddleEuler.saddle_euler_log_lower` are identities of the L30
  window/coefficient construction (boxed derivative masses and the Euler mass
  at the saddle band), not convolutions of smooth integers.  They do not
  produce a lower bound for `centralSmoothCount`.

* `RandomizedL30SharpRankin` and `RandomizedL30PrimeReciprocal` prove the
  sharp Rankin/saddle *upper* bound for the same smooth-number counts.  An
  upper bound cannot yield the local lower bound, which is why the Buchstab
  estimate and the parity fraction remain explicit.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or mass
is set to zero.
-/

namespace Cogentic.RandomizedL30Dickman

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30CentralCount
open Cogentic.Randomized

noncomputable section

/-! ## 1. The Dickman saddle factor -/

/-- The saddle-point Dickman factor `exp (-(u log u))`.

This is the leading-order Dickman density at the paper scale, not the exact
recursive Dickman function.  It is exactly the exponential factor in
`YounisOddPaperSharpCount` and `PaperScaleSmoothUpperSharp`. -/
def dickmanRho (u : ℝ) : ℝ := Real.exp (-(u * Real.log u))

theorem dickmanRho_pos (u : ℝ) : 0 < dickmanRho u := Real.exp_pos _

theorem dickmanRho_nonneg (u : ℝ) : 0 ≤ dickmanRho u := (dickmanRho_pos u).le

theorem dickmanRho_one : dickmanRho 1 = 1 := by
  simp [dickmanRho]

/-- At the paper parameter `u = paperDensityU p ε n`, `dickmanRho` is exactly
the exponential factor used by the sharp count. -/
theorem dickmanRho_paperDensityU (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    dickmanRho (paperDensityU p ε n) =
      Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) := rfl

/-- The paper cutoff `smoothCutoff (paperT p) (paperError ε)` is exactly
`paperDensityY p ε = exp ((1+ε) t_p)`. -/
theorem smoothCutoff_eq_paperDensityY (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    smoothCutoff (paperT p) (paperError ε) n = paperDensityY p ε n := by
  rw [← paperDensityY_eq_smoothCutoff]

/-- The paper parameter is the Dickman ratio `u = log (p²) / log y` with
`y = exp ((1+ε) t_p)`. -/
theorem paperDensityU_eq_log_sq_div_log_cutoff (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    paperDensityU p ε n =
      Real.log (p n ^ 2) / Real.log (smoothCutoff (paperT p) (paperError ε) n) := by
  unfold paperDensityU smoothCutoff paperError
  rw [Real.log_pow, Real.log_exp]
  ring

/-- For `u ≥ 1`, the saddle factor is at most one. -/
theorem dickmanRho_le_one {u : ℝ} (hu : 1 ≤ u) : dickmanRho u ≤ 1 := by
  unfold dickmanRho
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  have hprod : 0 ≤ u * Real.log u := mul_nonneg (by linarith) hlog
  linarith

/-- The saddle factor is nonincreasing on `[1, ∞)`. -/
theorem dickmanRho_antitoneOn :
    ∀ {u v : ℝ}, 1 ≤ u → u ≤ v → dickmanRho v ≤ dickmanRho u := by
  intro u v hu huv
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlogv : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  have hmono : u * Real.log u ≤ v * Real.log v :=
    mul_le_mul huv hlogv hlogu hv0.le
  unfold dickmanRho
  exact Real.exp_le_exp.mpr (by linarith)

/-! ## 2. The all-smooth sharp density predicates -/

/-- **The sharp all-smooth central count on the `p^{3/2}` scale.**  Every
`y`-smooth integer in the central Hasse interval contributes; no parity
condition is imposed. -/
def SharpCentralSmoothCount (c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) ≤
      ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ)

/-- The sharp all-smooth central count normalised by the interval cardinality. -/
def SharpCentralSmoothIntervalDensity (c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * ((centralOrderInterval p n).card : ℝ) *
        dickmanRho (paperDensityU p ε n) ≤
      ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ)

/-- The `p^{3/2}` form implies the interval-length form: the interval contains
at most `p^{3/2}` integers. -/
theorem sharpCentralSmoothIntervalDensity_of_count
    {c : ℝ} {p : ℕ → ℝ} (hp : ∀ n, 2 ≤ p n) {ε : ℝ}
    (h : SharpCentralSmoothCount c p ε) :
    SharpCentralSmoothIntervalDensity c p ε := by
  filter_upwards [h] with n hn
  have hK := centralOrderInterval_card_le_three_halves (p := p) (n := n) (hp n)
  have he : (0 : ℝ) ≤ dickmanRho (paperDensityU p ε n) := dickmanRho_nonneg _
  have hI : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  by_cases hc : 0 ≤ c
  · have hmul : c * ((centralOrderInterval p n).card : ℝ) ≤
        c * p n ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hK hc
    exact (mul_le_mul_of_nonneg_right hmul he).trans hn
  · have hc' : c < 0 := lt_of_not_ge hc
    have hleft : c * ((centralOrderInterval p n).card : ℝ) *
        dickmanRho (paperDensityU p ε n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc'.le hI) he
    have hright : (0 : ℝ) ≤
        ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
      positivity
    exact hleft.trans hright

/-- The interval-length form implies the `p^{3/2}` form with the forced
constant `c/4`: the interval contains at least `p^{3/2}/4` integers. -/
theorem sharpCentralSmoothCount_of_intervalDensity
    {c : ℝ} {p : ℕ → ℝ} (hp : ∀ n, 2 ≤ p n) {ε : ℝ}
    (h : SharpCentralSmoothIntervalDensity c p ε) :
    SharpCentralSmoothCount (c / 4) p ε := by
  filter_upwards [h] with n hn
  have hlow := centralOrderInterval_card_ge_quarter (p := p) (n := n) (hp n)
  have hp_pos : (0 : ℝ) < p n := by linarith [hp n]
  have he : (0 : ℝ) ≤ dickmanRho (paperDensityU p ε n) := dickmanRho_nonneg _
  have hcard_non : (0 : ℝ) ≤
      ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
    positivity
  by_cases hc : 0 ≤ c
  · have hmul : (c / 4) * p n ^ ((3 : ℝ) / 2) ≤
        c * ((centralOrderInterval p n).card : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlow hc
      calc
        (c / 4) * p n ^ ((3 : ℝ) / 2) = c * (p n ^ ((3 : ℝ) / 2) / 4) := by
          ring
        _ ≤ c * ((centralOrderInterval p n).card : ℝ) := this
    exact (mul_le_mul_of_nonneg_right hmul he).trans hn
  · have hc' : c < 0 := lt_of_not_ge hc
    have hpow_non : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) :=
      Real.rpow_nonneg hp_pos.le _
    have hleft : (c / 4) * p n ^ ((3 : ℝ) / 2) *
        dickmanRho (paperDensityU p ε n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpow_non) he
    exact hleft.trans hcard_non

/-- **The two all-smooth density normalisations are equivalent up to the
forced constant `4`.** -/
theorem sharpCentralSmoothCount_iff_interval
    {c : ℝ} {p : ℕ → ℝ} (hp : ∀ n, 2 ≤ p n) {ε : ℝ} :
    (SharpCentralSmoothCount c p ε → SharpCentralSmoothIntervalDensity c p ε) ∧
      (SharpCentralSmoothIntervalDensity c p ε →
        SharpCentralSmoothCount (c / 4) p ε) :=
  ⟨fun h => sharpCentralSmoothIntervalDensity_of_count hp h,
    fun h => sharpCentralSmoothCount_of_intervalDensity hp h⟩

/-- The existing `p^{3/2}`/interval equivalence for the odd-half count.  This
is the imported `sharpCentralOddSmoothCount_iff_interval`, restated in the
notation of this file so that both densities can be compared side by side. -/
theorem sharpCentralOddCount_iff_intervalCount
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n) :
    (SharpCentralOddSmoothCount c p ε →
        YounisOddPaperSharpIntervalCount c p ε) ∧
      (YounisOddPaperSharpIntervalCount c p ε →
        SharpCentralOddSmoothCount (c / 4) p ε) :=
  sharpCentralOddSmoothCount_iff_interval hp

/-- The sharp odd-half central density, normalised by the interval cardinality
and written with the Dickman factor `ρ(u)`.  This is the literal short-interval
density form of the target `SharpCentralOddSmoothCount`. -/
def SharpCentralOddSmoothIntervalDensity (c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * ((centralOrderInterval p n).card : ℝ) *
        dickmanRho (paperDensityU p ε n) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n

/-- **The Dickman interval density is equivalent to `SharpCentralOddSmoothCount`
up to the forced constant `4`.**  This is the odd-half analogue of
`sharpCentralSmoothCount_iff_interval`; it is the imported
`sharpCentralOddSmoothCount_iff_interval` with the exponential factor written
as `dickmanRho`. -/
theorem sharpCentralOddSmoothCount_iff_oddIntervalDensity
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n) :
    (SharpCentralOddSmoothCount c p ε →
        SharpCentralOddSmoothIntervalDensity c p ε) ∧
      (SharpCentralOddSmoothIntervalDensity c p ε →
        SharpCentralOddSmoothCount (c / 4) p ε) := by
  constructor
  · intro h
    have h' := (sharpCentralOddSmoothCount_iff_interval hp).1 h
    filter_upwards [h'] with n hn
    simpa only [dickmanRho] using hn
  · intro h
    apply (sharpCentralOddSmoothCount_iff_interval hp).2
    filter_upwards [h] with n hn
    simpa only [dickmanRho] using hn

/-! ## 3. The odd-half parity transfer -/

/-- **The odd-half parity fraction.**  At least a `θ` fraction of the central
smooth integers satisfy `m % 4 = 2`.  This is the exact residue-class input
needed to pass from an all-smooth density to the odd-half count. -/
def CentralOddHalfParity (θ : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    θ * ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n

/-- The odd-half sharp count implies the all-smooth sharp count, because the
odd-half orders are a subset of the central smooth orders. -/
theorem sharpCentralSmoothCount_of_oddSmoothCount
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (h : SharpCentralOddSmoothCount c p ε) :
    SharpCentralSmoothCount c p ε := by
  filter_upwards [h] with n hn
  have hle : centralOddSmoothCount p (paperT p) (paperError ε) n ≤
      ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
    simpa only [smoothOrderCount] using
      centralOddSmoothCount_le_smoothOrderCount p (paperT p) (paperError ε) n
  unfold dickmanRho
  exact hn.trans hle

/-- **All-smooth density plus parity gives the odd-half sharp count.**  The
output constant is exactly `θ c`. -/
theorem sharpCentralOddSmoothCount_of_smoothDensity_parity
    {c θ : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hθ : 0 ≤ θ)
    (hd : SharpCentralSmoothCount c p ε)
    (hpar : CentralOddHalfParity θ p ε) :
    SharpCentralOddSmoothCount (θ * c) p ε := by
  filter_upwards [hd, hpar] with n hdn hparn
  have hmul : θ * (c * p n ^ ((3 : ℝ) / 2) *
        dickmanRho (paperDensityU p ε n)) ≤
      θ * ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) :=
    mul_le_mul_of_nonneg_left hdn hθ
  have hleft : (θ * c) * p n ^ ((3 : ℝ) / 2) *
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) =
      θ * (c * p n ^ ((3 : ℝ) / 2) *
        dickmanRho (paperDensityU p ε n)) := by
    unfold dickmanRho
    ring
  rw [hleft]
  exact hmul.trans hparn

/-- The interval-length version of the all-smooth-plus-parity reduction. -/
theorem sharpCentralOddSmoothIntervalCount_of_smoothDensity_parity
    {c θ : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n) (hθ : 0 ≤ θ)
    (hd : SharpCentralSmoothCount c p ε)
    (hpar : CentralOddHalfParity θ p ε) :
    YounisOddPaperSharpIntervalCount (θ * c) p ε :=
  paperSharpIntervalCount_of_paperSharpCount hp
    (sharpCentralOddSmoothCount_of_smoothDensity_parity hθ hd hpar)

/-- The parity factor `1/2` specialisation. -/
theorem sharpCentralOddSmoothCount_of_smoothDensity_half
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hd : SharpCentralSmoothCount c p ε)
    (hpar : CentralOddHalfParity (1 / 2) p ε) :
    SharpCentralOddSmoothCount ((1 / 2) * c) p ε :=
  sharpCentralOddSmoothCount_of_smoothDensity_parity (by norm_num) hd hpar

/-- The parity factor `3/8` specialisation. -/
theorem sharpCentralOddSmoothCount_of_smoothDensity_three_eighths
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hd : SharpCentralSmoothCount c p ε)
    (hpar : CentralOddHalfParity (3 / 8) p ε) :
    SharpCentralOddSmoothCount ((3 / 8) * c) p ε :=
  sharpCentralOddSmoothCount_of_smoothDensity_parity (by norm_num) hd hpar

/-- The interval-length form of the `1/2` parity specialisation. -/
theorem sharpCentralOddSmoothIntervalCount_of_smoothDensity_half
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n)
    (hd : SharpCentralSmoothCount c p ε)
    (hpar : CentralOddHalfParity (1 / 2) p ε) :
    YounisOddPaperSharpIntervalCount ((1 / 2) * c) p ε :=
  sharpCentralOddSmoothIntervalCount_of_smoothDensity_parity hp (by norm_num) hd hpar

/-- The interval-length form of the `3/8` parity specialisation. -/
theorem sharpCentralOddSmoothIntervalCount_of_smoothDensity_three_eighths
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n)
    (hd : SharpCentralSmoothCount c p ε)
    (hpar : CentralOddHalfParity (3 / 8) p ε) :
    YounisOddPaperSharpIntervalCount ((3 / 8) * c) p ε :=
  sharpCentralOddSmoothIntervalCount_of_smoothDensity_parity hp (by norm_num) hd hpar

/-! ## 4. The Buchstab one-prime convolution -/

/-- The finite set of one-prime Buchstab pairs `(P, a)` for the central
interval:

* `P` is a prime at most `y = smoothCutoff t err n`,
* `a` is a positive integer at most `p²`,
* every prime factor of `a` is at most `P` (`a` is `P`-smooth),
* the product `a P` lies in the central interval.

The product map `(P, a) ↦ a P` is injective on this set and its image consists
of `y`-smooth central orders. -/
def buchstabOnePairs (p : ℕ → ℝ) (t err : ℕ → ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((((Finset.Icc 2 ⌊smoothCutoff t err n⌋₊).filter Nat.Prime).product
      (Finset.Icc 1 ⌊p n ^ 2⌋₊)).filter
    (fun q : ℕ × ℕ =>
      (∀ r ∈ q.2.primeFactors, r ≤ q.1) ∧
        q.2 * q.1 ∈ centralOrderInterval p n))

/-- Membership in `buchstabOnePairs`, unpacked. -/
theorem mem_buchstabOnePairs {p t err : ℕ → ℝ} {n : ℕ} {q : ℕ × ℕ} :
    q ∈ buchstabOnePairs p t err n ↔
      q.1 ∈ Finset.Icc 2 ⌊smoothCutoff t err n⌋₊ ∧ q.1.Prime ∧
        q.2 ∈ Finset.Icc 1 ⌊p n ^ 2⌋₊ ∧
          (∀ r ∈ q.2.primeFactors, r ≤ q.1) ∧
            q.2 * q.1 ∈ centralOrderInterval p n := by
  constructor
  · intro hq
    rw [buchstabOnePairs, Finset.mem_filter] at hq
    obtain ⟨hprod, hsmooth, hI⟩ := hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hprod
    obtain ⟨hq1I, hq1P⟩ := Finset.mem_filter.mp hq1
    exact ⟨hq1I, hq1P, hq2, hsmooth, hI⟩
  · rintro ⟨hq1I, hq1P, hq2, hsmooth, hI⟩
    rw [buchstabOnePairs, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hq1I, hq1P⟩, hq2⟩, hsmooth, hI⟩

/-- The lower endpoint of the central interval is at least `2` for `p ≥ 2`.
This is the elementary estimate `p² - p^{3/2}/2 ≥ p²/2 ≥ 2`, and it shows that
the central interval never contains `1`. -/
theorem two_le_centralInterval_lower {p : ℝ} (hp : 2 ≤ p) :
    (2 : ℝ) ≤ p ^ 2 - p ^ ((3 : ℝ) / 2) / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hmono : p ^ ((3 : ℝ) / 2) ≤ p ^ 2 := by
    rw [← Real.rpow_natCast p 2]
    exact Real.rpow_le_rpow_of_exponent_le hp1
      (by norm_num : ((3 : ℝ) / 2) ≤ (2 : ℝ))
  have hp4 : (4 : ℝ) ≤ p ^ 2 := by
    have hsquare : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    rw [hsquare]
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp 2
  nlinarith

/-- The one-prime Buchstab product lands in the central smooth orders. -/
theorem buchstabOnePairs_image_subset
    {p t err : ℕ → ℝ} {n : ℕ} :
    (buchstabOnePairs p t err n).image (fun q : ℕ × ℕ => q.2 * q.1) ⊆
      centralSmoothOrders p t err n := by
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨q, hq, rfl⟩ := hm
  obtain ⟨hPmem, hPprime, hamem, hsmooth, hI⟩ := mem_buchstabOnePairs.mp hq
  have hPle_floor : q.1 ≤ ⌊smoothCutoff t err n⌋₊ := (Finset.mem_Icc.mp hPmem).2
  have hPle : (q.1 : ℝ) ≤ smoothCutoff t err n :=
    (Nat.cast_le.mpr hPle_floor).trans
      (Nat.floor_le (le_of_lt (Real.exp_pos _)))
  have ha1 : 1 ≤ q.2 := (Finset.mem_Icc.mp hamem).1
  have ha_ne : q.2 ≠ 0 := by omega
  have hP_ne : q.1 ≠ 0 := by
    have := (Finset.mem_Icc.mp hPmem).1
    omega
  refine Finset.mem_filter.mpr ⟨hI, ?_⟩
  unfold IsSmoothUpTo
  intro r hr
  rw [Nat.primeFactors_mul ha_ne hP_ne] at hr
  rcases Finset.mem_union.mp hr with hr | hr
  · exact (Nat.cast_le.mpr (hsmooth r hr)).trans hPle
  · have hrP : r = q.1 := by
      have hsingle : r ∈ ({q.1} : Finset ℕ) := by
        simpa [hPprime.primeFactors] using hr
      simpa using hsingle
    rw [hrP]
    exact hPle

/-- **Every central smooth order is a Buchstab product.**  For `m ≥ 2` in the
central interval and `y`-smooth, take `P` to be the largest prime factor of `m`
and `a = m / P`.  Then `a` is `P`-smooth and `a P = m`, so `m` is in the image
of the one-prime Buchstab map.  Together with `buchstabOnePairs_image_subset`
this makes the Buchstab decomposition an exact bijection on the central smooth
orders (for `p ≥ 2`, where `1` is outside the interval). -/
theorem centralSmoothOrders_subset_buchstabImage
    {p t err : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    centralSmoothOrders p t err n ⊆
      (buchstabOnePairs p t err n).image (fun q : ℕ × ℕ => q.2 * q.1) := by
  intro m hm
  obtain ⟨hmI, hmsmooth⟩ := Finset.mem_filter.mp hm
  have hlow2 : (2 : ℝ) ≤ p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 :=
    two_le_centralInterval_lower hp
  have hceil2 : 2 ≤ ⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ := by
    have hR : (2 : ℝ) ≤
        (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℝ) :=
      hlow2.trans (Nat.le_ceil _)
    exact_mod_cast hR
  have hm_ge : 2 ≤ m := hceil2.trans (Finset.mem_Icc.mp hmI).1
  have hm1 : 1 < m := by omega
  -- The largest prime factor of `m`.
  let P : ℕ := m.primeFactors.max' (Nat.nonempty_primeFactors.mpr hm1)
  have hPmem : P ∈ m.primeFactors := Finset.max'_mem _ _
  have hPprime : P.Prime := Nat.prime_of_mem_primeFactors hPmem
  have hPdvd : P ∣ m := Nat.dvd_of_mem_primeFactors hPmem
  -- The cofactor.
  let a : ℕ := m / P
  have haP : a * P = m := Nat.div_mul_cancel hPdvd
  -- The prime lies in the cutoff range.
  have hPleY : (P : ℝ) ≤ smoothCutoff t err n := hmsmooth P hPmem
  have hPfloor : P ≤ ⌊smoothCutoff t err n⌋₊ := Nat.le_floor hPleY
  have hPmemIcc : P ∈ Finset.Icc 2 ⌊smoothCutoff t err n⌋₊ :=
    Finset.mem_Icc.mpr ⟨hPprime.two_le, hPfloor⟩
  -- The cofactor is positive and below `p²`.
  have ha_ne : a ≠ 0 := by
    intro h0
    have : a * P = 0 := by simp [h0]
    omega
  have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha_ne
  have ha_le_m : a ≤ m := by
    have h1P : 1 ≤ P := hPprime.one_le
    calc
      a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * P := Nat.mul_le_mul_left a h1P
      _ = m := haP
  have ha_floor : a ≤ ⌊p n ^ 2⌋₊ := ha_le_m.trans (Finset.mem_Icc.mp hmI).2
  -- Every prime factor of the cofactor is at most `P`.
  have ha_smooth : ∀ r ∈ a.primeFactors, r ≤ P := by
    intro r hr
    have hrdvd_a : r ∣ a := Nat.dvd_of_mem_primeFactors hr
    have hadvd_m : a ∣ m := ⟨P, haP.symm⟩
    have hrdvd_m : r ∣ m := hrdvd_a.trans hadvd_m
    have hrmem : r ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hr, hrdvd_m, by omega⟩
    exact Finset.le_max' (m.primeFactors) r hrmem
  have hpair : (P, a) ∈ buchstabOnePairs p t err n := by
    refine mem_buchstabOnePairs.mpr ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hPmemIcc
    · exact hPprime
    · exact Finset.mem_Icc.mpr ⟨ha1, ha_floor⟩
    · exact ha_smooth
    · rw [haP]
      exact hmI
  exact Finset.mem_image.mpr ⟨(P, a), hpair, haP⟩

/-- If a prime `P` divides `a * Q` and `a` is `Q`-smooth, then `P ≤ Q`.  This
is the elementary uniqueness step for the Buchstab product. -/
theorem prime_le_of_dvd_mul_of_smooth {P Q a : ℕ} (hP : P.Prime) (hQ : Q.Prime)
    (ha_ne : a ≠ 0) (ha : ∀ r ∈ a.primeFactors, r ≤ Q) (hdvd : P ∣ a * Q) :
    P ≤ Q := by
  rcases hP.dvd_mul.mp hdvd with h | h
  · have hmem : P ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hP, h, ha_ne⟩
    exact ha P hmem
  · rcases (Nat.dvd_prime hQ).mp h with h1 | h1
    · exact absurd h1 hP.ne_one
    · exact le_of_eq h1

/-- **The one-prime Buchstab product is injective.**  If `a₁ P₁ = a₂ P₂` with
both `Pᵢ` prime and `aᵢ` `Pᵢ`-smooth, then `P₁ = P₂` and `a₁ = a₂`. -/
theorem buchstabOnePairs_injOn {p t err : ℕ → ℝ} {n : ℕ} :
    Set.InjOn (fun q : ℕ × ℕ => q.2 * q.1) ↑(buchstabOnePairs p t err n) := by
  intro q hq r hr heq
  change q.2 * q.1 = r.2 * r.1 at heq
  obtain ⟨hPq, hPq_prime, haq, haPq, -⟩ := mem_buchstabOnePairs.mp hq
  obtain ⟨hPr, hPr_prime, har, haPr, -⟩ := mem_buchstabOnePairs.mp hr
  have haq_ne : q.2 ≠ 0 := by
    have := (Finset.mem_Icc.mp haq).1
    omega
  have har_ne : r.2 ≠ 0 := by
    have := (Finset.mem_Icc.mp har).1
    omega
  have hle1 : q.1 ≤ r.1 := by
    apply prime_le_of_dvd_mul_of_smooth hPq_prime hPr_prime har_ne haPr
    rw [← heq]
    exact dvd_mul_left q.1 q.2
  have hle2 : r.1 ≤ q.1 := by
    apply prime_le_of_dvd_mul_of_smooth hPr_prime hPq_prime haq_ne haPq
    rw [heq]
    exact dvd_mul_left r.1 r.2
  have hP : q.1 = r.1 := le_antisymm hle1 hle2
  have hEq : q.2 = r.2 := by
    have h := heq
    change q.2 * q.1 = r.2 * r.1 at h
    rw [hP] at h
    exact Nat.mul_right_cancel (m := r.1) (n := q.2) (k := r.2)
      (Nat.pos_of_ne_zero hPr_prime.ne_zero) h
  exact Prod.ext hP hEq

/-- The Buchstab pair count is at most the central smooth count. -/
theorem buchstabOnePairs_card_le_smoothCount
    {p t err : ℕ → ℝ} {n : ℕ} :
    ((buchstabOnePairs p t err n).card : ℝ) ≤
      ((centralSmoothOrders p t err n).card : ℝ) := by
  have hcard : ((buchstabOnePairs p t err n).image
        (fun q : ℕ × ℕ => q.2 * q.1)).card =
      (buchstabOnePairs p t err n).card :=
    Finset.card_image_of_injOn buchstabOnePairs_injOn
  have hle : ((buchstabOnePairs p t err n).image
        (fun q : ℕ × ℕ => q.2 * q.1)).card ≤
      (centralSmoothOrders p t err n).card :=
    Finset.card_le_card buchstabOnePairs_image_subset
  have hcardle : (buchstabOnePairs p t err n).card ≤
      (centralSmoothOrders p t err n).card := by
    calc
      (buchstabOnePairs p t err n).card =
          ((buchstabOnePairs p t err n).image (fun q : ℕ × ℕ => q.2 * q.1)).card :=
        hcard.symm
      _ ≤ (centralSmoothOrders p t err n).card := hle
  exact_mod_cast hcardle

/-- **The Buchstab decomposition is exact.**  For `p ≥ 2` the one-prime
Buchstab pairs are in bijection with the central smooth orders, so their
cardinalities coincide.  The large-prime restriction in
`BuchstabLargePrimeShortIntervalLower` is therefore the only weakening: it
drops the (`sqrt y`)-smooth small-largest-prime part. -/
theorem buchstabOnePairs_card_eq_smoothCount
    {p t err : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    (buchstabOnePairs p t err n).card =
      (centralSmoothOrders p t err n).card := by
  have hset : (buchstabOnePairs p t err n).image (fun q : ℕ × ℕ => q.2 * q.1) =
      centralSmoothOrders p t err n :=
    Finset.Subset.antisymm buchstabOnePairs_image_subset
      (centralSmoothOrders_subset_buchstabImage hp)
  rw [← hset]
  exact (Finset.card_image_of_injOn buchstabOnePairs_injOn).symm

/-! ## 5. The large-prime Buchstab sub-count -/

/-- The large-prime part of the Buchstab pairs: `P > sqrt y`.  This is the
range in which the largest prime factor dominates the cofactor, the classical
Buchstab split. -/
def buchstabLargePrimePairs (p : ℕ → ℝ) (t err : ℕ → ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (buchstabOnePairs p t err n).filter
    (fun q : ℕ × ℕ => Real.sqrt (smoothCutoff t err n) < (q.1 : ℝ))

theorem buchstabLargePrimePairs_subset
    {p t err : ℕ → ℝ} {n : ℕ} :
    buchstabLargePrimePairs p t err n ⊆ buchstabOnePairs p t err n :=
  Finset.filter_subset _ _

/-- The large-prime Buchstab sub-count is still at most the central smooth
count: injectivity is inherited from `buchstabOnePairs_injOn`. -/
theorem buchstabLargePrimePairs_card_le_smoothCount
    {p t err : ℕ → ℝ} {n : ℕ} :
    ((buchstabLargePrimePairs p t err n).card : ℝ) ≤
      ((centralSmoothOrders p t err n).card : ℝ) := by
  have hsub_coe : (↑(buchstabLargePrimePairs p t err n) : Set (ℕ × ℕ)) ⊆
      ↑(buchstabOnePairs p t err n) := by
    intro q hq
    exact buchstabLargePrimePairs_subset hq
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.2 * q.1)
      ↑(buchstabLargePrimePairs p t err n) :=
    buchstabOnePairs_injOn.mono hsub_coe
  have hcard : ((buchstabLargePrimePairs p t err n).image
        (fun q : ℕ × ℕ => q.2 * q.1)).card =
      (buchstabLargePrimePairs p t err n).card :=
    Finset.card_image_of_injOn hinj
  have hsub : (buchstabLargePrimePairs p t err n).image
        (fun q : ℕ × ℕ => q.2 * q.1) ⊆ centralSmoothOrders p t err n := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨q, hq, rfl⟩ := hm
    exact buchstabOnePairs_image_subset
      (Finset.mem_image.mpr ⟨q, buchstabLargePrimePairs_subset hq, rfl⟩)
  have hle : ((buchstabLargePrimePairs p t err n).image
        (fun q : ℕ × ℕ => q.2 * q.1)).card ≤
      (centralSmoothOrders p t err n).card :=
    Finset.card_le_card hsub
  have hcardle : (buchstabLargePrimePairs p t err n).card ≤
      (centralSmoothOrders p t err n).card := by
    calc
      (buchstabLargePrimePairs p t err n).card =
          ((buchstabLargePrimePairs p t err n).image
            (fun q : ℕ × ℕ => q.2 * q.1)).card := hcard.symm
      _ ≤ (centralSmoothOrders p t err n).card := hle
  exact_mod_cast hcardle

/-- The complementary small-prime part of the Buchstab pairs: `P ≤ sqrt y`.
Its image consists of the central smooth orders whose largest prime factor is
at most `sqrt y`, i.e. the `sqrt y`-smooth part. -/
def buchstabSmallPrimePairs (p : ℕ → ℝ) (t err : ℕ → ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (buchstabOnePairs p t err n).filter
    (fun q : ℕ × ℕ => ¬ Real.sqrt (smoothCutoff t err n) < (q.1 : ℝ))

/-- The one-prime Buchstab pairs split exactly into the large-prime and
small-prime parts. -/
theorem buchstabOnePairs_card_eq_large_add_small
    {p t err : ℕ → ℝ} {n : ℕ} :
    (buchstabOnePairs p t err n).card =
      (buchstabLargePrimePairs p t err n).card +
        (buchstabSmallPrimePairs p t err n).card := by
  classical
  unfold buchstabLargePrimePairs buchstabSmallPrimePairs
  exact (Finset.card_filter_add_card_filter_not
    (s := buchstabOnePairs p t err n)
    (p := fun q : ℕ × ℕ =>
      Real.sqrt (smoothCutoff t err n) < (q.1 : ℝ))).symm

/-- **The exact Buchstab split of the central smooth count.**  For `p ≥ 2` the
central smooth count is the sum of the large-prime and small-prime Buchstab
pair counts.  The target lower bound is therefore exactly the statement that
this sum is at least `c p^{3/2} ρ(u)`; the residual
`BuchstabLargePrimeShortIntervalLower` is the sufficient condition that the
large-prime summand alone already has that size. -/
theorem centralSmoothOrders_card_eq_large_add_small
    {p t err : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    (centralSmoothOrders p t err n).card =
      (buchstabLargePrimePairs p t err n).card +
        (buchstabSmallPrimePairs p t err n).card := by
  rw [← buchstabOnePairs_card_eq_smoothCount hp,
    buchstabOnePairs_card_eq_large_add_small]

/-- **The precise missing analytic estimate.**  The large-prime one-prime
Buchstab convolution already has the sharp size

`c p^{3/2} exp (-(u log u))`.

Equivalently: for most primes `P` in `(sqrt y, y]`, the window
`(p²/P - p^{3/2}/(2P), p²/P]` contains enough `P`-smooth cofactors.  This is a
short-interval Buchstab/de Bruijn lower bound.  It is not implied by the
Rankin/saddle *upper* bound of `RandomizedL30SharpRankin`, and it is not in
Mathlib's combinatorial `Nat.smoothNumbers` API. -/
def BuchstabLargePrimeShortIntervalLower (c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) ≤
      ((buchstabLargePrimePairs p (paperT p) (paperError ε) n).card : ℝ)

/-- The large-prime Buchstab lower bound implies the all-smooth sharp central
count. -/
theorem sharpCentralSmoothCount_of_buchstabLargePrimeLower
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (h : BuchstabLargePrimeShortIntervalLower c p ε) :
    SharpCentralSmoothCount c p ε := by
  filter_upwards [h] with n hn
  exact hn.trans
    (buchstabLargePrimePairs_card_le_smoothCount
      (p := p) (t := paperT p) (err := paperError ε) (n := n))

/-- **The exact composed reduction.**  The large-prime Buchstab lower bound for
the all-smooth count and the odd-half parity fraction `θ` give the sharp
odd-half interval count with constant `θ c`. -/
theorem sharpCentralOddSmoothIntervalCount_of_buchstabLargePrime_parity
    {c θ : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n) (hθ : 0 ≤ θ)
    (hbuchstab : BuchstabLargePrimeShortIntervalLower c p ε)
    (hpar : CentralOddHalfParity θ p ε) :
    YounisOddPaperSharpIntervalCount (θ * c) p ε :=
  sharpCentralOddSmoothIntervalCount_of_smoothDensity_parity hp hθ
    (sharpCentralSmoothCount_of_buchstabLargePrimeLower hbuchstab) hpar

/-! ## 6. A non-vacuous instance of the Buchstab residual

The residual is not an empty statement: at the explicit constant schedule
`p = 9`, `y = 81`, the prime `P = 71` and cofactor `a = 1` give a genuine
large-prime Buchstab pair in the central interval `(81 - 27/2, 81] = (67.5, 81]`.
The Dickman parameter is `u = 2 log 9 / log 81 = 1`, so `ρ(u) = 1`, and the
constant `c = 1/27` makes the residual inequality exactly an equality with the
single pair `(71, 1)`.
-/

/-- The constant prime scale `p = 9` of the non-vacuity witness. -/
def smallWitnessP : ℕ → ℝ := fun _ => 9

/-- The paper scale `t_p` at `p = 9`. -/
def smallWitnessT : ℝ := Real.sqrt (Real.log 9 * Real.log (Real.log 9))

/-- The relative error normalising the paper cutoff to `81 = 9²`. -/
def smallWitnessEps : ℝ := Real.log 81 / smallWitnessT - 1

theorem smallWitnessT_pos : 0 < smallWitnessT := by
  unfold smallWitnessT
  apply Real.sqrt_pos_of_pos
  apply mul_pos
  · exact Real.log_pos (by norm_num)
  · apply Real.log_pos
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by
      nlinarith [Real.exp_one_lt_three])

theorem smallWitness_paperT (n : ℕ) : paperT smallWitnessP n = smallWitnessT := rfl

/-- The witness normalisation `(1+ε)t = log 81`. -/
theorem smallWitness_one_add_eps_mul (n : ℕ) :
    (1 + smallWitnessEps) * paperT smallWitnessP n = Real.log 81 := by
  rw [smallWitness_paperT]
  unfold smallWitnessEps
  field_simp [smallWitnessT_pos.ne']
  ring

theorem smallWitness_cutoff (n : ℕ) :
    smoothCutoff (paperT smallWitnessP) (paperError smallWitnessEps) n = 81 := by
  unfold smoothCutoff
  rw [show (1 + paperError smallWitnessEps n) * paperT smallWitnessP n =
      Real.log 81 from smallWitness_one_add_eps_mul n]
  exact Real.exp_log (by norm_num)

theorem smallWitness_log81_eq : Real.log 81 = 2 * Real.log 9 := by
  rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- The Dickman parameter at the witness is exactly `1`. -/
theorem smallWitness_paperDensityU (n : ℕ) :
    paperDensityU smallWitnessP smallWitnessEps n = 1 := by
  unfold paperDensityU
  rw [smallWitness_paperT]
  have hw : (1 + smallWitnessEps) * smallWitnessT = Real.log 81 := by
    simpa only [smallWitness_paperT] using smallWitness_one_add_eps_mul n
  rw [hw, smallWitness_log81_eq]
  simp only [smallWitnessP]
  have hlog9 : Real.log 9 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

theorem smallWitness_rpow (n : ℕ) :
    smallWitnessP n ^ ((3 : ℝ) / 2) = 27 := by
  unfold smallWitnessP
  rw [rpow_three_halves_eq 9 (by norm_num)]
  rw [show Real.sqrt 9 = 3 by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  norm_num

theorem smallWitness_centralInterval (n : ℕ) :
    centralOrderInterval smallWitnessP n = Finset.Icc 68 81 := by
  unfold centralOrderInterval
  rw [show smallWitnessP n ^ 2 = 81 by norm_num [smallWitnessP],
    smallWitness_rpow]
  norm_num

theorem smallWitness_pair_mem (n : ℕ) :
    (71, 1) ∈ buchstabLargePrimePairs smallWitnessP
      (paperT smallWitnessP) (paperError smallWitnessEps) n := by
  rw [buchstabLargePrimePairs, Finset.mem_filter]
  constructor
  · refine mem_buchstabOnePairs.mpr ⟨?_, by norm_num, ?_, ?_, ?_⟩
    · rw [smallWitness_cutoff]
      norm_num
    · rw [show ⌊smallWitnessP n ^ 2⌋₊ = 81 by norm_num [smallWitnessP]]
      norm_num
    · intro r hr
      simp at hr
    · rw [smallWitness_centralInterval]
      norm_num
  · rw [smallWitness_cutoff]
    rw [show Real.sqrt 81 = 9 by
      rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    norm_num

/-- **The large-prime Buchstab residual is inhabited.** -/
theorem buchstabLargePrimeShortIntervalLower_smallWitness :
    BuchstabLargePrimeShortIntervalLower (1 / 27) smallWitnessP smallWitnessEps := by
  refine Filter.Eventually.of_forall (fun n => ?_)
  have hmem := smallWitness_pair_mem n
  have hcard_pos : 0 < (buchstabLargePrimePairs smallWitnessP
      (paperT smallWitnessP) (paperError smallWitnessEps) n).card :=
    Finset.card_pos.mpr ⟨(71, 1), hmem⟩
  have hcard_ge : (1 : ℝ) ≤
      ((buchstabLargePrimePairs smallWitnessP
        (paperT smallWitnessP) (paperError smallWitnessEps) n).card : ℝ) := by
    exact_mod_cast hcard_pos
  have hleft : (1 / 27) * smallWitnessP n ^ ((3 : ℝ) / 2) *
        dickmanRho (paperDensityU smallWitnessP smallWitnessEps n) = 1 := by
    rw [smallWitness_rpow, smallWitness_paperDensityU, dickmanRho_one]
    norm_num
  rw [hleft]
  exact hcard_ge

/-- The corresponding all-smooth sharp density, obtained from the Buchstab
residual by the reduction of Section 5. -/
theorem sharpCentralSmoothCount_smallWitness :
    SharpCentralSmoothCount (1 / 27) smallWitnessP smallWitnessEps :=
  sharpCentralSmoothCount_of_buchstabLargePrimeLower
    buchstabLargePrimeShortIntervalLower_smallWitness

/-! ## Axiom audit -/

#print axioms smoothCutoff_eq_paperDensityY
#print axioms paperDensityU_eq_log_sq_div_log_cutoff
#print axioms dickmanRho_pos
#print axioms dickmanRho_le_one
#print axioms dickmanRho_antitoneOn
#print axioms sharpCentralSmoothIntervalDensity_of_count
#print axioms sharpCentralSmoothCount_of_intervalDensity
#print axioms sharpCentralSmoothCount_iff_interval
#print axioms sharpCentralOddSmoothCount_iff_oddIntervalDensity
#print axioms sharpCentralSmoothCount_of_oddSmoothCount
#print axioms sharpCentralOddSmoothCount_of_smoothDensity_parity
#print axioms sharpCentralOddSmoothIntervalCount_of_smoothDensity_parity
#print axioms sharpCentralOddSmoothIntervalCount_of_smoothDensity_half
#print axioms sharpCentralOddSmoothIntervalCount_of_smoothDensity_three_eighths
#print axioms mem_buchstabOnePairs
#print axioms two_le_centralInterval_lower
#print axioms buchstabOnePairs_image_subset
#print axioms centralSmoothOrders_subset_buchstabImage
#print axioms prime_le_of_dvd_mul_of_smooth
#print axioms buchstabOnePairs_injOn
#print axioms buchstabOnePairs_card_le_smoothCount
#print axioms buchstabOnePairs_card_eq_smoothCount
#print axioms buchstabLargePrimePairs_card_le_smoothCount
#print axioms buchstabOnePairs_card_eq_large_add_small
#print axioms centralSmoothOrders_card_eq_large_add_small
#print axioms sharpCentralSmoothCount_of_buchstabLargePrimeLower
#print axioms sharpCentralOddSmoothIntervalCount_of_buchstabLargePrime_parity
#print axioms smallWitness_paperDensityU
#print axioms smallWitness_centralInterval
#print axioms smallWitness_pair_mem
#print axioms buchstabLargePrimeShortIntervalLower_smallWitness
#print axioms sharpCentralSmoothCount_smallWitness

end

end Cogentic.RandomizedL30Dickman
