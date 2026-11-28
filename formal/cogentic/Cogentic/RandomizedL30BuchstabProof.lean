import Cogentic.RandomizedL30Dickman
import Cogentic.RandomizedL30RankinEuler
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# L30: the Buchstab large-prime lower bound and the exact obstructions

`Cogentic.RandomizedL30Dickman` decomposed the central smooth count exactly as

```
#centralSmoothOrders = #buchstabLargePrimePairs + #buchstabSmallPrimePairs
```

and isolated `BuchstabLargePrimeShortIntervalLower c p ε` as the statement that
the large-prime one-prime Buchstab part alone has the sharp size
`c p^{3/2} ρ(u)`, `u = paperDensityU p ε`, `ρ u = exp (-(u log u))`.

This file tests the two obvious routes to that statement at the paper schedule
`t_p = sqrt (log p · log log p)`, `y = exp ((1+ε) t_p)` and records exactly what
does and does not close.

## What is proved

* `buchstabSmallPrimePairs_image_subset`, `..._card_le_sqrtSmooth`: the
  small-prime part is contained in the central orders all of whose prime factors
  are at most `sqrt y`.

* `sum_Icc_two_rpow_neg_le`, `primeSum_five_eighths_le`,
  `log_eulerProduct_five_eighths_le`, `eulerProduct_five_eighths_le`: the
  elementary Rankin/Euler-product estimate at tilt `α = 5/8`.  The Euler product
  over primes below `Z` is at most `exp ((32/3) Z^{3/8})`.

* `sqrtSmoothCentral_card_le_rankin`, `sqrtSmoothCentral_card_le_exp`: the
  `sqrt y`-smooth central count is at most
  `p^{5/4} exp ((32/3) (sqrt y)^{3/8})`, via
  `Cogentic.Randomized.smoothCount_rankin_upper`.

* `tendsto_paperT_cube_div_log`, `tendsto_exp_mul_paperT_div_log_atTop`: the
  true paper-schedule asymptotics `t_p^3 / log p → ∞` and
  `exp (a t_p) / log p → ∞` for every `a > 0`.

* `eventually_target_le_rankin_smallBound`: **the Rankin small-prime bound is
  eventually larger than the target scale.**  For every `C > 0`,
  `C p^{3/2} ρ(u)` is eventually at most
  `p^{5/4} exp ((32/3) (sqrt y)^{3/8})`.  Consequently the Rankin estimate
  cannot prove the small-prime part negligible: it controls all `sqrt y`-smooth
  integers up to `p²`, a set of the wrong (`p²` rather than `p^{3/2}`) scale.

* `CentralSqrtSmoothUpper`: the missing **short-interval upper bound** for the
  `sqrt y`-smooth central count.

* `buchstabLargePrimeShortIntervalLower_of_sharp_and_upper`: the exact
  arithmetic transfer: a total central lower bound `SharpCentralSmoothCount C`
  together with `CentralSqrtSmoothUpper D` and `c + D ≤ C` implies
  `BuchstabLargePrimeShortIntervalLower c`.

* `BuchstabLargePrimeSubIntervalLower` and
  `buchstabLargePrimeShortIntervalLower_of_subInterval`: a positive-proportion
  sub-interval of the central interval already suffices, with no constant loss,
  because its Buchstab pairs are a subset of the central large-prime pairs.

## What remains, precisely

The large-prime target is **not** proved here, and it is not implied by the
total central count alone using the estimates available in this library.  The
two inputs that would close it are:

1. `SharpCentralSmoothCount C p ε` (the short-interval *lower* bound for all
   `y`-smooth central orders), and
2. `CentralSqrtSmoothUpper D p ε` (a short-interval *upper* bound for the
   `sqrt y`-smooth central orders), with `c + D ≤ C`.

Item 2 is the genuine obstruction in route (b): the Rankin bound of this file
only gives a global `√y`-smooth count up to `p²`, which
`eventually_target_le_rankin_smallBound` shows is eventually *above* the target
scale, so it cannot supply the required `o (p^{3/2} ρ(u))` control.  Equivalently,
the whole statement is the direct large-prime short-interval Buchstab estimate,
which is stronger than the total central count.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or mass is
set to zero.  The target is not assumed.
-/

namespace Cogentic.RandomizedL30BuchstabProof

open Filter Real
open scoped Classical BigOperators
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30CentralCount
open Cogentic.RandomizedL30Dickman
open Cogentic.RandomizedL30RankinEuler
open Cogentic.Randomized

noncomputable section

/-! ## 1. The small-prime part is `sqrt y`-smooth -/

/-- The image of the small-prime Buchstab pairs consists of central orders all
of whose prime factors are at most `sqrt y`. -/
theorem buchstabSmallPrimePairs_image_subset
    {p t err : ℕ → ℝ} {n : ℕ} :
    (buchstabSmallPrimePairs p t err n).image (fun q : ℕ × ℕ => q.2 * q.1) ⊆
      (centralOrderInterval p n).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n))) := by
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨q, hq, rfl⟩ := hm
  rw [buchstabSmallPrimePairs, Finset.mem_filter] at hq
  obtain ⟨hqone, hPle⟩ := hq
  obtain ⟨hPmem, hPprime, hamem, hasmooth, hI⟩ := mem_buchstabOnePairs.mp hqone
  have hPle' : (q.1 : ℝ) ≤ Real.sqrt (smoothCutoff t err n) := le_of_not_gt hPle
  have ha_ne : q.2 ≠ 0 := by
    have := (Finset.mem_Icc.mp hamem).1
    omega
  have hP_ne : q.1 ≠ 0 := by
    have := (Finset.mem_Icc.mp hPmem).1
    omega
  refine Finset.mem_filter.mpr ⟨hI, ?_⟩
  unfold IsSmoothUpTo
  intro r hr
  rw [Nat.primeFactors_mul ha_ne hP_ne] at hr
  rcases Finset.mem_union.mp hr with hr | hr
  · exact (Nat.cast_le.mpr (hasmooth r hr)).trans hPle'
  · have hrP : r = q.1 := by
      have hsingle : r ∈ ({q.1} : Finset ℕ) := by
        simpa [hPprime.primeFactors] using hr
      simpa using hsingle
    rw [hrP]
    exact hPle'

/-- The small-prime Buchstab count is at most the `sqrt y`-smooth central
count. -/
theorem buchstabSmallPrimePairs_card_le_sqrtSmooth
    {p t err : ℕ → ℝ} {n : ℕ} :
    ((buchstabSmallPrimePairs p t err n).card : ℝ) ≤
      (((centralOrderInterval p n).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))).card : ℝ) := by
  have hsub_coe : (↑(buchstabSmallPrimePairs p t err n) : Set (ℕ × ℕ)) ⊆
      ↑(buchstabOnePairs p t err n) := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.2 * q.1)
      ↑(buchstabSmallPrimePairs p t err n) :=
    buchstabOnePairs_injOn.mono hsub_coe
  have hcard : ((buchstabSmallPrimePairs p t err n).image
        (fun q : ℕ × ℕ => q.2 * q.1)).card =
      (buchstabSmallPrimePairs p t err n).card :=
    Finset.card_image_of_injOn hinj
  have hle : ((buchstabSmallPrimePairs p t err n).image
        (fun q : ℕ × ℕ => q.2 * q.1)).card ≤
      ((centralOrderInterval p n).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))).card :=
    Finset.card_le_card buchstabSmallPrimePairs_image_subset
  calc
    ((buchstabSmallPrimePairs p t err n).card : ℝ)
        = ((buchstabSmallPrimePairs p t err n).image
            (fun q : ℕ × ℕ => q.2 * q.1)).card := by rw [hcard]
    _ ≤ ((centralOrderInterval p n).filter
          (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))).card := by
        exact_mod_cast hle

/-! ## 2. The `sqrt y`-smooth central set is a global smooth set -/

theorem sqrtSmoothCentral_subset_global {p t err : ℕ → ℝ} {n : ℕ}
    (hp : (2 : ℝ) ≤ p n) :
    ((centralOrderInterval p n).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))) ⊆
      (Finset.Icc 1 ⌊p n ^ 2⌋₊).filter
        (fun m : ℕ => ∀ q ∈ m.primeFactors,
          (q : ℝ) ≤ Real.sqrt (smoothCutoff t err n)) := by
  intro m hm
  obtain ⟨hmI, hms⟩ := Finset.mem_filter.mp hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmI
  have hceil : (1 : ℕ) ≤ ⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ := by
    have hreal : (1 : ℝ) ≤
        (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℝ) :=
      (one_le_central_lower hp).trans (Nat.le_ceil _)
    exact_mod_cast hreal
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hceil.trans hlo, hhi⟩, hms⟩

/-- The Rankin upper bound at tilt `5/8` for the `sqrt y`-smooth central set. -/
theorem sqrtSmoothCentral_card_le_rankin {p t err : ℕ → ℝ} {n : ℕ}
    (hp : (2 : ℝ) ≤ p n) (hZ : 2 ≤ Real.sqrt (smoothCutoff t err n)) :
    (((centralOrderInterval p n).filter
      (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))).card : ℝ) ≤
      (p n ^ 2) ^ ((5 : ℝ) / 8) *
        ∏ q ∈ (Finset.Icc 2 ⌊Real.sqrt (smoothCutoff t err n)⌋₊).filter
            Nat.Prime,
          (1 - (q : ℝ) ^ (-((5 : ℝ) / 8)))⁻¹ := by
  have hp0 : (0 : ℝ) < p n := by linarith
  have hp1 : (1 : ℝ) ≤ p n := by linarith
  have hx : (1 : ℝ) ≤ p n ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hp1 2
    simpa using h
  have hcard : (((centralOrderInterval p n).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))).card : ℝ) ≤
      (((Finset.Icc 1 ⌊p n ^ 2⌋₊).filter
        (fun m : ℕ => ∀ q ∈ m.primeFactors,
          (q : ℝ) ≤ Real.sqrt (smoothCutoff t err n))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (sqrtSmoothCentral_subset_global hp)
  have hR := smoothCount_rankin_upper (x := p n ^ 2)
    (y := Real.sqrt (smoothCutoff t err n)) (α := (5 : ℝ) / 8)
    hx hZ (by norm_num) (by norm_num)
  exact hcard.trans (by simpa using hR)

/-! ## 3. The elementary Euler-product estimate at tilt `5/8` -/

/-- Index shift: `∑_{2 ≤ n ≤ N} f n = ∑_{1 ≤ i < N} f (i+1)`. -/
private theorem sum_Icc_two_eq_sum_Ico_one (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 2 N, f n) = ∑ i ∈ Finset.Ico 1 N, f (i + 1) := by
  have hmap : (Finset.Ico 1 N).image (fun i : ℕ => i + 1) = Finset.Icc 2 N := by
    ext n
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_Icc]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      omega
    · intro hn
      exact ⟨n - 1, ⟨by omega, by omega⟩, by omega⟩
  have hinj : Set.InjOn (fun i : ℕ => i + 1)
      (↑(Finset.Ico 1 N) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.succ.inj hab
  have h := Finset.sum_image (s := Finset.Ico 1 N)
    (g := fun i : ℕ => i + 1) (f := f) hinj
  rw [hmap] at h
  exact h

/-- The integral comparison `∑_{2 ≤ n ≤ Z} n^{-5/8} ≤ (8/3) Z^{3/8}`. -/
theorem sum_Icc_two_rpow_neg_le {Z : ℝ} (hZ : 2 ≤ Z) :
    (∑ n ∈ Finset.Icc 2 ⌊Z⌋₊, (n : ℝ) ^ (-((5 : ℝ) / 8))) ≤
      (8 / 3) * Z ^ ((3 : ℝ) / 8) := by
  set N : ℕ := ⌊Z⌋₊ with hN
  have hN2 : 2 ≤ N := by
    rw [hN]
    exact Nat.le_floor hZ
  have hZpos : (0 : ℝ) < Z := by linarith
  rw [sum_Icc_two_eq_sum_Ico_one N (fun n => (n : ℝ) ^ (-((5 : ℝ) / 8)))]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-((5 : ℝ) / 8)))
      (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le zero_lt_one (by simpa using hx.1)) hxy
      (by norm_num : -((5 : ℝ) / 8) ≤ 0)
  have hN1 : (1 : ℕ) ≤ N := le_trans (by norm_num) hN2
  have hmain := AntitoneOn.sum_le_integral_Ico
    (f := fun x : ℝ => x ^ (-((5 : ℝ) / 8))) (a := 1) (b := N) hN1 hanti
  refine hmain.trans ?_
  have hInt := integral_rpow (a := ((1 : ℕ) : ℝ)) (b := (N : ℝ))
    (r := -((5 : ℝ) / 8)) (Or.inl (by norm_num))
  rw [hInt]
  have hpow : (N : ℝ) ^ (-((5 : ℝ) / 8) + 1) = (N : ℝ) ^ ((3 : ℝ) / 8) := by
    congr 1
    ring
  have hone : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
  rw [hpow, hone, Real.one_rpow]
  have hNZ : (N : ℝ) ≤ Z := by
    rw [hN]
    exact Nat.floor_le hZpos.le
  have hNpow : (N : ℝ) ^ ((3 : ℝ) / 8) ≤ Z ^ ((3 : ℝ) / 8) :=
    Real.rpow_le_rpow (by positivity) hNZ (by norm_num)
  have hden : -((5 : ℝ) / 8) + 1 = (3 : ℝ) / 8 := by norm_num
  rw [hden]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (3 : ℝ) / 8)]
  nlinarith [hNpow]

/-- The tilted prime mass at tilt `5/8` is at most `(8/3) Z^{3/8}`. -/
theorem primeSum_five_eighths_le {Z : ℝ} (hZ : 2 ≤ Z) :
    (∑ q ∈ (Finset.Icc 2 ⌊Z⌋₊).filter Nat.Prime,
        (q : ℝ) ^ (-((5 : ℝ) / 8))) ≤
      (8 / 3) * Z ^ ((3 : ℝ) / 8) := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun q _ _ => by positivity)).trans (sum_Icc_two_rpow_neg_le hZ)

/-- The Euler product at tilt `5/8` is at most `exp ((32/3) Z^{3/8})`. -/
theorem log_eulerProduct_five_eighths_le {Z : ℝ} (hZ : 2 ≤ Z) :
    Real.log
        (∏ q ∈ (Finset.Icc 2 ⌊Z⌋₊).filter Nat.Prime,
          (1 - (q : ℝ) ^ (-((5 : ℝ) / 8)))⁻¹) ≤
      (32 / 3) * Z ^ ((3 : ℝ) / 8) := by
  have hlog := log_eulerProduct_le_four_mul_primeSum
    (Y := Z) (α := (5 : ℝ) / 8) (by norm_num)
  have hS := primeSum_five_eighths_le hZ
  nlinarith [hlog, hS]

/-- The Euler product itself, exponentiated. -/
theorem eulerProduct_five_eighths_le {Z : ℝ} (hZ : 2 ≤ Z) :
    (∏ q ∈ (Finset.Icc 2 ⌊Z⌋₊).filter Nat.Prime,
        (1 - (q : ℝ) ^ (-((5 : ℝ) / 8)))⁻¹) ≤
      Real.exp ((32 / 3) * Z ^ ((3 : ℝ) / 8)) := by
  have hpos : 0 < ∏ q ∈ (Finset.Icc 2 ⌊Z⌋₊).filter Nat.Prime,
      (1 - (q : ℝ) ^ (-((5 : ℝ) / 8)))⁻¹ := by
    refine Finset.prod_pos fun q hq => ?_
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqprime.two_le
    have hlt : (q : ℝ) ^ (-((5 : ℝ) / 8)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
        (by norm_num : -((5 : ℝ) / 8) < 0)
    exact inv_pos.mpr (by linarith)
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr (log_eulerProduct_five_eighths_le hZ)

/-! ## 4. The `sqrt y`-smooth central count -/

/-- **`sqrt y`-smooth central count bound** (Rankin at tilt `5/8`). -/
theorem sqrtSmoothCentral_card_le_exp {p t err : ℕ → ℝ} {n : ℕ}
    (hp : (2 : ℝ) ≤ p n) (hZ : 2 ≤ Real.sqrt (smoothCutoff t err n)) :
    (((centralOrderInterval p n).filter
      (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))).card : ℝ) ≤
      p n ^ ((5 : ℝ) / 4) *
        Real.exp (((32 : ℝ) / 3) *
          (Real.sqrt (smoothCutoff t err n)) ^ ((3 : ℝ) / 8)) := by
  have hR := sqrtSmoothCentral_card_le_rankin (p := p) (t := t) (err := err)
    (n := n) hp hZ
  have he := eulerProduct_five_eighths_le hZ
  have hp0 : (0 : ℝ) < p n := by linarith
  have hpoweq : (p n ^ 2) ^ ((5 : ℝ) / 8) = p n ^ ((5 : ℝ) / 4) := by
    rw [← Real.rpow_natCast (p n) 2, ← Real.rpow_mul hp0.le]
    congr 1
    norm_num
  rw [hpoweq] at hR
  exact hR.trans (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hp0.le _))

/-- The small-prime Buchstab count is bounded by the same elementary Rankin
expression. -/
theorem buchstabSmallPrimePairs_card_le_exp {p t err : ℕ → ℝ} {n : ℕ}
    (hp : (2 : ℝ) ≤ p n) (hZ : 2 ≤ Real.sqrt (smoothCutoff t err n)) :
    ((buchstabSmallPrimePairs p t err n).card : ℝ) ≤
      p n ^ ((5 : ℝ) / 4) *
        Real.exp (((32 : ℝ) / 3) *
          (Real.sqrt (smoothCutoff t err n)) ^ ((3 : ℝ) / 8)) :=
  (buchstabSmallPrimePairs_card_le_sqrtSmooth (p := p) (t := t) (err := err)
    (n := n)).trans (sqrtSmoothCentral_card_le_exp hp hZ)

/-! ## 5. The paper square-root cutoff -/

/-- The square-root of the paper cutoff, `sqrt y = exp ((1+ε) t_p / 2)`. -/
def paperZ (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (smoothCutoff (paperT p) (paperError ε) n)

theorem paperZ_eq_exp (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    paperZ p ε n = Real.exp (((1 + ε) * paperT p n) / 2) := by
  unfold paperZ smoothCutoff paperError
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

theorem paperZ_rpow_eight (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    (paperZ p ε n) ^ ((3 : ℝ) / 8) =
      Real.exp (((3 * (1 + ε)) / 16) * paperT p n) := by
  rw [paperZ_eq_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

theorem eventually_paperZ_ge_two {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 2 ≤ paperZ p ε n := by
  have ht := tendsto_paperT_of_growth h
  filter_upwards [ht.eventually_ge_atTop (2 * Real.log 2 / (1 + ε))] with n hn
  rw [paperZ_eq_exp]
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  have hlog : Real.log 2 ≤ ((1 + ε) * paperT p n) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ h1] at hn
    nlinarith
  calc
    (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (((1 + ε) * paperT p n) / 2) := Real.exp_le_exp.mpr hlog

/-! ## 6. True paper-schedule asymptotics -/

theorem tendsto_paperT_cube_div_log {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) :
    Tendsto (fun n => paperT p n ^ 3 / Real.log (p n)) atTop atTop := by
  have ht := tendsto_paperT_of_growth h
  have hloglog : Tendsto (fun n => Real.log (Real.log (p n))) atTop atTop :=
    Real.tendsto_log_atTop.comp h.tendsto_log
  have hratio : Tendsto (fun n => paperT p n ^ 2 / Real.log (p n))
      atTop atTop := by
    refine hloglog.congr' ?_
    filter_upwards [h.eventually_sixteen, eventually_log_log_pos_of_growth h] with
      n hp hll
    have hp1 : (1 : ℝ) < p n := by linarith
    have hL : 0 < Real.log (p n) := Real.log_pos hp1
    have ht2 : paperT p n ^ 2 =
        Real.log (p n) * Real.log (Real.log (p n)) := by
      unfold paperT
      exact Real.sq_sqrt (mul_nonneg hL.le hll.le)
    rw [ht2]
    field_simp [hL.ne']
  have hmul : Tendsto
      (fun n => paperT p n * (paperT p n ^ 2 / Real.log (p n)))
      atTop atTop :=
    ht.atTop_mul_atTop₀ hratio
  refine hmul.congr fun n => ?_
  ring

/-- `exp (a t_p) / log p → ∞` for every `a > 0`.  This is the true asymptotic;
the reciprocal quantity `log p / exp (a t_p)` tends to zero. -/
theorem tendsto_exp_mul_paperT_div_log_atTop {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => Real.exp (a * paperT p n) / Real.log (p n))
      atTop atTop := by
  have ht := tendsto_paperT_of_growth h
  have harg : Tendsto (fun n => a * paperT p n) atTop atTop :=
    ht.const_mul_atTop ha
  have h1 : Tendsto
      (fun n => Real.exp (a * paperT p n) / (a * paperT p n) ^ 3)
      atTop atTop :=
    (tendsto_exp_div_pow_atTop 3).comp harg
  have h2 : Tendsto
      (fun n => (a * paperT p n) ^ 3 / Real.log (p n)) atTop atTop := by
    have h3 := tendsto_paperT_cube_div_log h
    have h3' : Tendsto
        (fun n => a ^ 3 * (paperT p n ^ 3 / Real.log (p n))) atTop atTop :=
      h3.const_mul_atTop (pow_pos ha 3)
    refine h3'.congr fun n => ?_
    ring
  have hprod := h1.atTop_mul_atTop₀ h2
  refine hprod.congr' ?_
  filter_upwards [h.eventually_sixteen] with n hn
  have hp1 : (1 : ℝ) < p n := by linarith
  have htpos : 0 < paperT p n := by
    unfold paperT
    exact Real.sqrt_pos_of_pos
      (mul_pos (Real.log_pos hp1) (Real.log_pos (one_lt_log_of_sixteen hn)))
  have hapos : 0 < a * paperT p n := mul_pos ha htpos
  have hLpos : 0 < Real.log (p n) := Real.log_pos hp1
  field_simp [hapos.ne', hLpos.ne']

/-! ## 7. The Rankin small-prime bound is above the target scale -/

/-- Exponent identity for the target: `C p^{3/2} ρ(u)` is the exponential of
`log C + (3/2) log p - u log u`. -/
theorem exp_log_target_eq {x C u : ℝ}
    (hx : 0 < x) (hC : 0 < C) (_hu : 0 < u) :
    Real.exp (Real.log C + ((3 : ℝ) / 2) * Real.log x - (u * Real.log u)) =
      C * x ^ ((3 : ℝ) / 2) * dickmanRho u := by
  unfold dickmanRho
  rw [show Real.log C + ((3 : ℝ) / 2) * Real.log x - (u * Real.log u) =
      Real.log C + (((3 : ℝ) / 2) * Real.log x + (-(u * Real.log u))) by ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_log hC]
  rw [show ((3 : ℝ) / 2) * Real.log x = Real.log x * ((3 : ℝ) / 2) by ring,
    Real.exp_mul, Real.exp_log hx]
  ring

/-- Exponent identity for the Rankin expression. -/
theorem exp_log_rankin_eq {x : ℝ} {K : ℝ} (hx : 0 < x) :
    Real.exp (((5 : ℝ) / 4) * Real.log x + K) =
      x ^ ((5 : ℝ) / 4) * Real.exp K := by
  rw [Real.exp_add]
  rw [show ((5 : ℝ) / 4) * Real.log x = Real.log x * ((5 : ℝ) / 4) by ring,
    Real.exp_mul, Real.exp_log hx]

/-- **The Rankin small-prime bound is eventually at least the target scale.**
For every `C > 0`, the target `C p^{3/2} ρ(u)` is eventually below the explicit
upper bound `p^{5/4} exp ((32/3) (sqrt y)^{3/8})` produced by the Rankin
estimate.  Hence that estimate cannot prove the small-prime part negligible. -/
theorem eventually_target_le_rankin_smallBound
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in atTop,
      C * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) ≤
        p n ^ ((5 : ℝ) / 4) *
          Real.exp (((32 : ℝ) / 3) * (paperZ p ε n) ^ ((3 : ℝ) / 8)) := by
  have ha : (0 : ℝ) < (3 * (1 + ε)) / 16 := by positivity
  have hdiv := tendsto_exp_mul_paperT_div_log_atTop h ha
  have hK : ∀ᶠ n in atTop,
      Real.log (p n) ≤ ((32 : ℝ) / 3) * (paperZ p ε n) ^ ((3 : ℝ) / 8) := by
    filter_upwards [hdiv.eventually_ge_atTop 1, eventually_log_pos_of_growth h] with
      n hn hL
    rw [paperZ_rpow_eight]
    rw [le_div_iff₀ hL] at hn
    nlinarith [Real.exp_pos (((3 * (1 + ε)) / 16) * paperT p n)]
  have hLC : ∀ᶠ n in atTop,
      Real.log C ≤ ((3 : ℝ) / 4) * Real.log (p n) := by
    have hev := h.tendsto_log.eventually_ge_atTop (max 0 (4 * Real.log C / 3))
    filter_upwards [hev] with n hn
    have h1 : 4 * Real.log C / 3 ≤ Real.log (p n) :=
      le_trans (le_max_right _ _) hn
    linarith
  have hu1 : ∀ᶠ n in atTop, 1 < paperDensityU p ε n :=
    eventually_paperDensityU_gt_one_of_tendsto
      (tendsto_paperDensityU_of_growth h hε)
  filter_upwards [h.eventually_sixteen, hK, hLC, hu1] with n hp hKn hLCn hu1n
  have hp0 : (0 : ℝ) < p n := by linarith
  have hlogu : 0 < Real.log (paperDensityU p ε n) := Real.log_pos hu1n
  have hu_nonneg : 0 ≤ paperDensityU p ε n * Real.log (paperDensityU p ε n) :=
    mul_nonneg (by linarith) hlogu.le
  have hExpIneq : Real.log C + ((3 : ℝ) / 2) * Real.log (p n) -
        (paperDensityU p ε n * Real.log (paperDensityU p ε n)) ≤
      ((5 : ℝ) / 4) * Real.log (p n) +
        ((32 : ℝ) / 3) * (paperZ p ε n) ^ ((3 : ℝ) / 8) := by
    nlinarith [hKn, hLCn, hu_nonneg]
  calc
    C * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n)
        = Real.exp (Real.log C + ((3 : ℝ) / 2) * Real.log (p n) -
            (paperDensityU p ε n * Real.log (paperDensityU p ε n))) :=
          (exp_log_target_eq (x := p n) hp0 hC (by linarith)).symm
    _ ≤ Real.exp (((5 : ℝ) / 4) * Real.log (p n) +
          ((32 : ℝ) / 3) * (paperZ p ε n) ^ ((3 : ℝ) / 8)) :=
        Real.exp_le_exp.mpr hExpIneq
    _ = p n ^ ((5 : ℝ) / 4) *
          Real.exp (((32 : ℝ) / 3) * (paperZ p ε n) ^ ((3 : ℝ) / 8)) :=
        exp_log_rankin_eq (x := p n) hp0

/-! ## 8. The exact conditional transfer -/

/-- The missing short-interval **upper** bound for the `sqrt y`-smooth central
orders: their count is eventually at most `D p^{3/2} ρ(u)`.

This is *not* the Rankin bound of Section 4: that bound controls all
`sqrt y`-smooth integers up to `p²` and is eventually larger than the target
scale.  The present estimate is a genuine short-interval upper bound. -/
def CentralSqrtSmoothUpper (D : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    (((centralOrderInterval p n).filter
      (IsSmoothUpTo (Real.sqrt (smoothCutoff (paperT p) (paperError ε) n)))).card : ℝ) ≤
      D * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n)

/-- **Sharp total lower bound plus a short-interval small-prime upper bound
give the large-prime Buchstab lower bound.**  This is the exact arithmetic
content of the Buchstab split; the constants satisfy `c + D ≤ C`. -/
theorem buchstabLargePrimeShortIntervalLower_of_sharp_and_upper
    {C D c : ℝ} (hCD : c + D ≤ C) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (_hε : 0 < ε) (hsharp : SharpCentralSmoothCount C p ε)
    (hup : CentralSqrtSmoothUpper D p ε) :
    BuchstabLargePrimeShortIntervalLower c p ε := by
  have hp2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ p n := by
    filter_upwards [h.eventually_sixteen] with n hn
    linarith
  filter_upwards [hsharp, hup, hp2] with n hsh hupn hp
  have hsmall : ((buchstabSmallPrimePairs p (paperT p) (paperError ε) n).card : ℝ) ≤
      D * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) :=
    (buchstabSmallPrimePairs_card_le_sqrtSmooth (p := p) (t := paperT p)
      (err := paperError ε) (n := n)).trans (by simpa [paperZ] using hupn)
  have hsplit := centralSmoothOrders_card_eq_large_add_small
    (p := p) (t := paperT p) (err := paperError ε) (n := n) hp
  have hsplitR : ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) =
      ((buchstabLargePrimePairs p (paperT p) (paperError ε) n).card : ℝ) +
        ((buchstabSmallPrimePairs p (paperT p) (paperError ε) n).card : ℝ) := by
    exact_mod_cast hsplit
  let X : ℝ := p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n)
  have hp0 : (0 : ℝ) < p n := by linarith
  have hX0 : 0 ≤ X :=
    mul_nonneg (Real.rpow_nonneg hp0.le _) (dickmanRho_nonneg _)
  have hshX : C * X ≤
      ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
    simpa [X, mul_assoc] using hsh
  have hsmallX :
      ((buchstabSmallPrimePairs p (paperT p) (paperError ε) n).card : ℝ) ≤ D * X := by
    simpa [X, mul_assoc] using hsmall
  have hle : c ≤ C - D := by linarith
  have hCDX : c * X ≤ (C - D) * X := mul_le_mul_of_nonneg_right hle hX0
  have hCDX' : c * X ≤ C * X - D * X := by nlinarith [hCDX]
  have hgoal : c * X ≤
      ((buchstabLargePrimePairs p (paperT p) (paperError ε) n).card : ℝ) := by
    nlinarith only [hshX, hsmallX, hCDX', hsplitR]
  simpa [X, mul_assoc] using hgoal

/-- The large-prime lower bound implies the total central lower bound (the
trivial direction of the Buchstab split). -/
theorem sharpCentralSmoothCount_of_buchstab
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (h : BuchstabLargePrimeShortIntervalLower c p ε) :
    SharpCentralSmoothCount c p ε :=
  sharpCentralSmoothCount_of_buchstabLargePrimeLower h

/-! ## 9. A positive-proportion sub-interval suffices -/

/-- The Buchstab lower bound on the upper sub-interval
`(p² - η p^{3/2}, p²]` of the central interval. -/
def BuchstabLargePrimeSubIntervalLower (η c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) ≤
      (((buchstabLargePrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ =>
          p n ^ 2 - η * p n ^ ((3 : ℝ) / 2) < (q.2 * q.1 : ℝ))).card : ℝ)

/-- **A positive-proportion sub-interval bound implies the central bound, with
no loss in the constant**, because the sub-interval pairs are a subset of the
central large-prime pairs. -/
theorem buchstabLargePrimeShortIntervalLower_of_subInterval
    {η c : ℝ} (_hη : 0 < η) {p : ℕ → ℝ} {ε : ℝ}
    (h : BuchstabLargePrimeSubIntervalLower η c p ε) :
    BuchstabLargePrimeShortIntervalLower c p ε := by
  filter_upwards [h] with n hn
  let S : Finset (ℕ × ℕ) :=
    (buchstabLargePrimePairs p (paperT p) (paperError ε) n).filter
      (fun q : ℕ × ℕ =>
        p n ^ 2 - η * p n ^ ((3 : ℝ) / 2) < (q.2 * q.1 : ℝ))
  have hle : (S.card : ℝ) ≤
      ((buchstabLargePrimePairs p (paperT p) (paperError ε) n).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  simpa [S] using hn.trans hle

/-! ## Axiom audit -/

#print axioms buchstabSmallPrimePairs_image_subset
#print axioms buchstabSmallPrimePairs_card_le_sqrtSmooth
#print axioms sqrtSmoothCentral_subset_global
#print axioms sqrtSmoothCentral_card_le_rankin
#print axioms sum_Icc_two_rpow_neg_le
#print axioms primeSum_five_eighths_le
#print axioms log_eulerProduct_five_eighths_le
#print axioms eulerProduct_five_eighths_le
#print axioms sqrtSmoothCentral_card_le_exp
#print axioms buchstabSmallPrimePairs_card_le_exp
#print axioms paperZ_eq_exp
#print axioms paperZ_rpow_eight
#print axioms eventually_paperZ_ge_two
#print axioms tendsto_paperT_cube_div_log
#print axioms tendsto_exp_mul_paperT_div_log_atTop
#print axioms exp_log_target_eq
#print axioms exp_log_rankin_eq
#print axioms eventually_target_le_rankin_smallBound
#print axioms buchstabLargePrimeShortIntervalLower_of_sharp_and_upper
#print axioms sharpCentralSmoothCount_of_buchstab
#print axioms buchstabLargePrimeShortIntervalLower_of_subInterval

end

end Cogentic.RandomizedL30BuchstabProof
