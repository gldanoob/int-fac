import Cogentic.RandomizedL21_2CentralBin
import Cogentic.RandomizedL30Sharp

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# L30: the central-scale prime-bin strip and the sharp interval count

The Wave-26 endpoint records (`Cogentic/RandomizedPaperEndpointWave26`) leave
exactly one analytic L30 field,

```
YounisOddPaperSharpIntervalCount c p ε ,
```

the sharp short-interval count with the true Dickman exponent `u log u`,
`u = paperDensityU p ε n = 2 log (p n) / ((1 + ε) t_p n)`.

The natural attempt is to rerun the L30 `centeredBinProducts` construction at
the *central* place `p²` instead of the global place `p²/4`.  The L21.2
central-bin analysis (`Cogentic/RandomizedL21_2CentralBin`) showed that this is
impossible for a `√p`-window because the per-bin supply guard fails whenever
`m δ < log (1 + 1/√p)`.  The L30 central interval

```
(p² - p^{3/2}/2, p²]
```

is much wider, of additive length `p^{3/2}`, so the strip *does* fit with
multiplicative width `m δ ≈ p^{-1/2}`.  This file checks whether the
character-sum/insertion argument can now be run at this scale.

It cannot, for a clean quantitative reason.

* `centralStripBase`, `centralStripP`, `centralStripDelta` are the canonical
  central-scale bins: `P^m = p²/2 - p^{3/2}/8` and
  `m δ = log (1 + 1/(4 √p))`.  The doubled strip is
  `2 (P^m, P^m e^{mδ}] ⊆ (p² - p^{3/2}/2, p²]`
  (`centralStrip_lower`, `centralStrip_upper`), and the additive width is
  `p^{3/2}/4`, so the interval genuinely accommodates it.

* `centralSupplyGuard_false_of_strip` is the obstruction.  If
  `P^m ≤ p²/2`, the doubled strip lies in the central interval, `m ≥ u`, and
  `(1+ε) t_p < log p / 2`, then `P < √p`.  The strip condition gives
  `m δ ≤ 1/√p`, hence `δ P < 1/m ≤ 1`, while the guard's left side is at
  least `1`.  So the guard

  ```
  K (1 + log (3y))² √y + 1 ≤ (1/2) δ P exp (-(δ J))
  ```

  is *false* for every `K ≥ 0`, exactly as in the L21.2 window.  The geometric
  reason is that the central strip has `P ≈ y = exp ((1+ε) t_p) = p^{o(1)}`
  and bin width `p^{-1/2+o(1)}`, far below the GRH prime-counting error
  `√y = p^{o(1)}`; there are not enough primes per bin.  The general form
  `centralSupplyGuard_false_of_centralInterval` makes this independent of the
  particular bin construction: *every* strip satisfying the central interval
  containment and `m ≥ u` fails the guard.

* `not_centralWindowPrimeSupply` therefore rules out the direct central
  insertion count.  The residual is not a prime-supply statement at the
  window scale; it is the genuine short-interval *smooth-number* density at
  the sharp exponent.

* `paperSharpCount_of_intervalCount_quarter` and
  `paperSharpIntervalCount_of_paperSharpCount` show that the interval form and
  the explicit `p^{3/2}` form of the sharp count differ only by the forced
  constant `4`.  Hence the smallest explicit analytic input is exactly

  ```
  SharpCentralOddSmoothCount c p ε :
    ∀ᶠ n, c p^{3/2} exp (-(u log u)) ≤ centralOddSmoothCount p (paperT p) (paperError ε) n ,
  ```

  and the file proves both directions of the reduction
  (`sharpCentralOddSmoothCount_iff_interval`).

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, mass or
error is set to zero.
-/

namespace Cogentic.RandomizedL30CentralCount

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL21_2CentralBin
open Cogentic.Randomized

noncomputable section

/-! ## 1. The canonical central-scale strip -/

/-- The doubled strip base `p²/2 - p^{3/2}/8`.  It sits strictly above the
lower endpoint `p²/2 - p^{3/2}/4` of the halved central interval, and leaves
room for the multiplicative width `1 + 1/(4√p)`. -/
def centralStripBase (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  p n ^ 2 / 2 - p n ^ ((3 : ℝ) / 2) / 8

/-- The geometric bin centre `P = (p²/2 - p^{3/2}/8)^{1/m}`. -/
def centralStripP (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (centralStripBase p n) ^ (1 / (paperDensityM p ε n : ℝ))

/-- The window-scale bin width `δ = log (1 + 1/(4√p)) / m`.  The whole strip
has logarithmic width `log (1 + 1/(4√p))`, hence multiplicative width at most
`1 + 1/(4√p)`. -/
def centralStripDelta (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  Real.log (1 + 1 / (4 * Real.sqrt (p n))) / (paperDensityM p ε n : ℝ)

/-- The number of available bins.  The obstruction is independent of `J`; we
use the paper's `paperDensityJ` so that the supply predicate below is concrete. -/
def centralStripJ (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℕ :=
  paperDensityJ p ε n

/-- `p^{3/2} = p √p` for `p > 0`. -/
theorem rpow_three_halves_eq (p : ℝ) (hp : 0 < p) :
    p ^ ((3 : ℝ) / 2) = p * Real.sqrt p := by
  rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num]
  rw [Real.rpow_add hp, Real.rpow_one, Real.sqrt_eq_rpow]

/-- The strip base is positive for `p ≥ 2`. -/
theorem centralStripBase_pos {p : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    0 < centralStripBase p n := by
  have hp0 : (0 : ℝ) < p n := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (p n) := Real.sqrt_pos.mpr hp0
  have hs_le : Real.sqrt (p n) ≤ p n := by
    have hp1 : (1 : ℝ) ≤ p n := by linarith
    calc Real.sqrt (p n) ≤ Real.sqrt (p n ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith
      _ = p n := by rw [Real.sqrt_sq hp0.le]
  have hpow := rpow_three_halves_eq (p n) hp0
  have hbase : centralStripBase p n =
      p n * (4 * p n - Real.sqrt (p n)) / 8 := by
    unfold centralStripBase
    rw [hpow]
    field_simp
    ring
  rw [hbase]
  have hfac : (0 : ℝ) < 4 * p n - Real.sqrt (p n) := by
    nlinarith
  positivity

/-- The defining power identity `P^m = p²/2 - p^{3/2}/8`. -/
theorem centralStripP_pow {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hm : 0 < paperDensityM p ε n) :
    centralStripP p ε n ^ paperDensityM p ε n = centralStripBase p n := by
  have hbase : (0 : ℝ) ≤ centralStripBase p n := (centralStripBase_pos hp).le
  have hmne : ((paperDensityM p ε n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  unfold centralStripP
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hbase]
  have hcancel : (1 / (paperDensityM p ε n : ℝ)) *
      (paperDensityM p ε n : ℝ) = 1 := by field_simp
  rw [hcancel, Real.rpow_one]

/-- The defining width identity `m δ = log (1 + 1/(4√p))`. -/
theorem centralStripDelta_mul_m {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hm : 0 < paperDensityM p ε n) :
    (paperDensityM p ε n : ℝ) * centralStripDelta p ε n =
      Real.log (1 + 1 / (4 * Real.sqrt (p n))) := by
  have hmne : ((paperDensityM p ε n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  unfold centralStripDelta
  field_simp

/-- The width is nonnegative. -/
theorem centralStripDelta_nonneg {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) : 0 ≤ centralStripDelta p ε n := by
  unfold centralStripDelta
  have hs : (0 : ℝ) < Real.sqrt (p n) := Real.sqrt_pos.mpr hp
  have harg : (1 : ℝ) ≤ 1 + 1 / (4 * Real.sqrt (p n)) := by
    have : (0 : ℝ) ≤ 1 / (4 * Real.sqrt (p n)) := by positivity
    linarith
  exact div_nonneg (Real.log_nonneg harg) (Nat.cast_nonneg _)

/-- The doubled strip starts strictly above the lower endpoint. -/
theorem centralStrip_lower {p : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 <
      2 * centralStripBase p n := by
  have hp0 : (0 : ℝ) < p n := by linarith
  have hpowpos : (0 : ℝ) < p n ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hp0 _
  unfold centralStripBase
  linarith

/-- The doubled strip ends at most at the upper endpoint. -/
theorem centralStrip_upper {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hm : 0 < paperDensityM p ε n) :
    2 * (centralStripBase p n *
        Real.exp ((paperDensityM p ε n : ℝ) * centralStripDelta p ε n)) ≤
      p n ^ 2 := by
  have hp0 : (0 : ℝ) < p n := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (p n) := Real.sqrt_pos.mpr hp0
  have hsne : Real.sqrt (p n) ≠ 0 := hs0.ne'
  have hpow := rpow_three_halves_eq (p n) hp0
  have hmδ := centralStripDelta_mul_m (p := p) (ε := ε) hm
  have hexp : Real.exp ((paperDensityM p ε n : ℝ) * centralStripDelta p ε n) =
      1 + 1 / (4 * Real.sqrt (p n)) := by
    rw [hmδ, Real.exp_log]
    have : (0 : ℝ) < 1 + 1 / (4 * Real.sqrt (p n)) := by positivity
    exact this
  rw [hexp]
  have hsq : Real.sqrt (p n) * Real.sqrt (p n) = p n :=
    Real.mul_self_sqrt hp0.le
  have hmain : 2 * (centralStripBase p n * (1 + 1 / (4 * Real.sqrt (p n)))) =
      p n ^ 2 - p n / 16 := by
    unfold centralStripBase
    rw [hpow]
    field_simp [hsne]
    nlinarith [hsq]
  rw [hmain]
  nlinarith [hp0]

/-! ## 2. The central supply guard is unsatisfiable -/

/-- The logarithmic inequality `-log (1 - x) ≤ 2x` for `0 < x ≤ 1/2`. -/
theorem neg_log_one_sub_le_two_mul {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have h1x : 0 < 1 - x := by linarith
  have hpos : 0 < 1 / (1 - x) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hdiv : Real.log (1 / (1 - x)) = -Real.log (1 - x) := by
    rw [Real.log_div one_ne_zero (ne_of_gt h1x), Real.log_one]
    ring
  have hsub : 1 / (1 - x) - 1 = x / (1 - x) := by
    field_simp [ne_of_gt h1x]
    ring
  have hle : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ h1x]
    nlinarith
  rw [hdiv, hsub] at hlog
  linarith

/-- **The central-strip supply obstruction.**

Let `P^m` be a strip base inside the halved central interval
(`p² - p^{3/2}/2 < 2 P^m`), whose doubled top `2 P^m exp (m δ)` stays below
`p²`, and suppose the centre is below `√p`.  Then the insertion guard

```
K (1 + log (3y))² √y + 1 ≤ (1/2) δ P exp (-(δ J))
```

is false for every `K ≥ 0`, every `y`, and every bin count `J`.

This is the L30 analogue of `centralBinGuard_false_of_window`: the interval is
wide enough for the strip, but each individual bin is still narrower than the
GRH prime-supply error. -/
theorem centralSupplyGuard_false_of_strip
    {K P δ y p : ℝ} {J m : ℕ}
    (hp : 1 < p) (hm : 1 ≤ m)
    (hP : 0 < P) (hδ : 0 ≤ δ)
    (hP_le : P < Real.sqrt p)
    (hlo : p ^ 2 - p ^ ((3 : ℝ) / 2) / 2 < 2 * P ^ m)
    (hhi : 2 * (P ^ m * Real.exp ((m : ℝ) * δ)) ≤ p ^ 2)
    (hK : 0 ≤ K) :
    ¬ centralBinGuard K P δ y J m := by
  intro hguard
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  -- `m δ ≤ 1/√p`.
  have hPpow : 0 < P ^ m := pow_pos hP m
  have hden : 0 < p ^ 2 - p ^ ((3 : ℝ) / 2) / 2 := by
    have hpowpos : (0 : ℝ) < p ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
    have hlt' : p ^ ((3 : ℝ) / 2) < p ^ ((2 : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (x := p) (y := (3 : ℝ) / 2) (z := 2)
        hp (by norm_num)
    have hcast : p ^ ((2 : ℝ)) = p ^ 2 := Real.rpow_natCast p 2
    rw [hcast] at hlt'
    linarith
  have hexp_le : Real.exp ((m : ℝ) * δ) ≤
      p ^ 2 / (p ^ 2 - p ^ ((3 : ℝ) / 2) / 2) := by
    rw [le_div_iff₀ hden]
    have hmul := hhi
    nlinarith [hlo, hPpow]
  have hpow := rpow_three_halves_eq p hp0
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hratio : p ^ 2 / (p ^ 2 - p ^ ((3 : ℝ) / 2) / 2) =
      1 / (1 - 1 / (2 * Real.sqrt p)) := by
    have hden_eq : p ^ 2 - p ^ ((3 : ℝ) / 2) / 2 =
        p * (p - Real.sqrt p / 2) := by
      rw [hpow]
      ring
    have hnum_eq : 1 - 1 / (2 * Real.sqrt p) =
        (p - Real.sqrt p / 2) / p := by
      have hdiv : (p - Real.sqrt p / 2) / p = 1 - Real.sqrt p / (2 * p) := by
        field_simp [hp0.ne']
      rw [hdiv]
      have hswap : Real.sqrt p / (2 * p) = 1 / (2 * Real.sqrt p) := by
        field_simp [hp0.ne', hs0.ne']
        nlinarith [hsq]
      rw [hswap]
    rw [hden_eq, hnum_eq]
    field_simp [hp0.ne', hs0.ne']
  have hs1 : (1 : ℝ) ≤ Real.sqrt p := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hp.le
  have hx0 : 0 < 1 / (2 * Real.sqrt p) := by positivity
  have hx1 : 1 / (2 * Real.sqrt p) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt p)]
    nlinarith [hs1]
  have hlogineq := neg_log_one_sub_le_two_mul hx0 hx1
  have hmδ : (m : ℝ) * δ ≤ 1 / Real.sqrt p := by
    have hlog_le : Real.log (Real.exp ((m : ℝ) * δ)) ≤
        Real.log (1 / (1 - 1 / (2 * Real.sqrt p))) := by
      apply Real.log_le_log (Real.exp_pos _)
      simpa only [hratio] using hexp_le
    have hexp_log : Real.log (Real.exp ((m : ℝ) * δ)) = (m : ℝ) * δ :=
      Real.log_exp _
    have hlog_ratio : Real.log (1 / (1 - 1 / (2 * Real.sqrt p))) =
        -Real.log (1 - 1 / (2 * Real.sqrt p)) := by
      rw [Real.log_div one_ne_zero (by linarith : (1 : ℝ) - 1 / (2 * Real.sqrt p) ≠ 0),
        Real.log_one]
      ring
    rw [hexp_log, hlog_ratio] at hlog_le
    have htwo : -Real.log (1 - 1 / (2 * Real.sqrt p)) ≤ 1 / Real.sqrt p := by
      have h := hlogineq
      have heq : 2 * (1 / (2 * Real.sqrt p)) = 1 / Real.sqrt p := by ring
      linarith
    exact hlog_le.trans htwo
  -- Hence `δ P < 1`.
  have hδP : δ * P < 1 := by
    have hδeq : δ = ((m : ℝ) * δ) / (m : ℝ) := by field_simp
    have hstep : δ * P ≤ (1 / Real.sqrt p) * P / (m : ℝ) := by
      rw [hδeq]
      have hdiv : ((m : ℝ) * δ) / (m : ℝ) ≤ (1 / Real.sqrt p) / (m : ℝ) := by
        exact div_le_div_of_nonneg_right hmδ hm0.le
      calc ((m : ℝ) * δ) / (m : ℝ) * P ≤ ((1 / Real.sqrt p) / (m : ℝ)) * P := by
            exact mul_le_mul_of_nonneg_right hdiv hP.le
        _ = (1 / Real.sqrt p) * P / (m : ℝ) := by ring
    have hlt : (1 / Real.sqrt p) * P / (m : ℝ) < 1 := by
      have hP' : (1 / Real.sqrt p) * P < 1 := by
        have heq : (1 / Real.sqrt p) * P = P / Real.sqrt p := by ring
        rw [heq, div_lt_one hs0]
        exact hP_le
      have hmge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hinv : 1 / (m : ℝ) ≤ 1 := by
        rw [div_le_one hm0]
        exact hmge
      have hnonneg : 0 ≤ (1 / Real.sqrt p) * P := by positivity
      calc
        (1 / Real.sqrt p) * P / (m : ℝ) = ((1 / Real.sqrt p) * P) * (1 / (m : ℝ)) := by
          ring
        _ ≤ ((1 / Real.sqrt p) * P) * 1 :=
            mul_le_mul_of_nonneg_left hinv hnonneg
        _ < 1 := by simpa using hP'
    exact hstep.trans_lt hlt
  -- The guard's right side is below one, the left side is at least one.
  have hLHS : (1 : ℝ) ≤
      K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y + 1 := by
    have hnonneg : 0 ≤ K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y :=
      mul_nonneg (mul_nonneg hK (sq_nonneg _)) (Real.sqrt_nonneg _)
    linarith
  have hRHS : (1 - (1 / 2)) * δ * (P * Real.exp (-(δ * (J : ℝ)))) < 1 := by
    have hexp_le_one : Real.exp (-(δ * (J : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      nlinarith [mul_nonneg hδ hJ]
    have hnonneg : 0 ≤ (1 / 2 : ℝ) * δ * P := by positivity
    calc
      (1 - (1 / 2)) * δ * (P * Real.exp (-(δ * (J : ℝ))))
          = ((1 / 2) * δ * P) * Real.exp (-(δ * (J : ℝ))) := by ring
      _ ≤ ((1 / 2) * δ * P) * 1 := by
            exact mul_le_mul_of_nonneg_left hexp_le_one hnonneg
      _ = (1 / 2) * (δ * P) := by ring
      _ < 1 := by nlinarith [hδP]
  have hguard' : K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y + 1 ≤
      (1 - (1 / 2)) * δ * (P * Real.exp (-(δ * (J : ℝ)))) := hguard
  linarith

/-! ## 3. The centre is below `√p` and the guard is eventually false -/

/-- **The central strip centre is below `√p`.**  Since `P^m = p²/2 - p^{3/2}/8
≤ p²` and `m ≥ u = 2 log p / ((1+ε) t_p)`, the centre obeys
`log P ≤ 2 log p / u = (1+ε) t_p`.  The paper scale is `o (log p)`, so
eventually `(1+ε) t_p < log p / 2`, i.e. `P < √p`. -/
theorem centralStripP_lt_sqrt {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (h16 : 16 ≤ p n) (hε : 0 < ε)
    (hm : 1 ≤ paperDensityM p ε n)
    (hu_pos : 0 < paperDensityU p ε n)
    (hmu : paperDensityU p ε n ≤ (paperDensityM p ε n : ℝ))
    (hsmall : (1 + ε) * paperT p n < Real.log (p n) / 2) :
    centralStripP p ε n < Real.sqrt (p n) := by
  have hp0 : (0 : ℝ) < p n := by linarith
  have hmpos_nat : 0 < paperDensityM p ε n :=
    lt_of_lt_of_le Nat.zero_lt_one hm
  have hmpos : (0 : ℝ) < (paperDensityM p ε n : ℝ) := by exact_mod_cast hmpos_nat
  have hPpos : 0 < centralStripP p ε n := by
    unfold centralStripP
    exact Real.rpow_pos_of_pos (centralStripBase_pos hp) _
  have hPpow := centralStripP_pow (p := p) (ε := ε) hp hmpos_nat
  have hbase_le : centralStripBase p n ≤ p n ^ 2 / 2 := by
    unfold centralStripBase
    have hpow_nonneg : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) :=
      Real.rpow_nonneg hp0.le _
    linarith
  have hPm_le : centralStripP p ε n ^ paperDensityM p ε n ≤ p n ^ 2 := by
    rw [hPpow]
    nlinarith [hbase_le]
  have hlog_le : Real.log (centralStripP p ε n ^ paperDensityM p ε n) ≤
      Real.log (p n ^ 2) :=
    Real.log_le_log (pow_pos hPpos _) hPm_le
  have hlogPm : Real.log (centralStripP p ε n ^ paperDensityM p ε n) =
      (paperDensityM p ε n : ℝ) * Real.log (centralStripP p ε n) := by
    rw [Real.log_pow]
  have hlogp2 : Real.log (p n ^ 2) = 2 * Real.log (p n) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogPm, hlogp2] at hlog_le
  have hlogP_le : Real.log (centralStripP p ε n) ≤
      2 * Real.log (p n) / (paperDensityM p ε n : ℝ) := by
    rw [le_div_iff₀ hmpos]
    linarith
  have hlogp_pos : 0 < Real.log (p n) := Real.log_pos (by linarith)
  have hdiv_le : 2 * Real.log (p n) / (paperDensityM p ε n : ℝ) ≤
      2 * Real.log (p n) / paperDensityU p ε n :=
    div_le_div_of_nonneg_left (by positivity) hu_pos hmu
  have hu_def : paperDensityU p ε n =
      2 * Real.log (p n) / ((1 + ε) * paperT p n) := rfl
  have hα : (0 : ℝ) < 1 + ε := by linarith
  have hlog16 : (1 : ℝ) < Real.log (p n) :=
    Cogentic.RandomizedL30SmoothDensity.one_lt_log_of_sixteen h16
  have ht : 0 < paperT p n := by
    unfold paperT
    exact Real.sqrt_pos_of_pos (mul_pos hlogp_pos (Real.log_pos hlog16))
  have hαt_ne : (1 + ε) * paperT p n ≠ 0 :=
    mul_ne_zero hα.ne' ht.ne'
  have hval : 2 * Real.log (p n) / paperDensityU p ε n =
      (1 + ε) * paperT p n := by
    rw [hu_def]
    field_simp
  have hlogP_lt : Real.log (centralStripP p ε n) < Real.log (p n) / 2 := by
    have hle : Real.log (centralStripP p ε n) ≤ (1 + ε) * paperT p n := by
      calc Real.log (centralStripP p ε n)
          ≤ 2 * Real.log (p n) / (paperDensityM p ε n : ℝ) := hlogP_le
        _ ≤ 2 * Real.log (p n) / paperDensityU p ε n := hdiv_le
        _ = (1 + ε) * paperT p n := hval
    linarith
  have hslog : Real.log (Real.sqrt (p n)) = Real.log (p n) / 2 :=
    Real.log_sqrt hp0.le
  rw [← hslog] at hlogP_lt
  calc
    centralStripP p ε n = Real.exp (Real.log (centralStripP p ε n)) :=
      (Real.exp_log hPpos).symm
    _ < Real.exp (Real.log (Real.sqrt (p n))) := Real.exp_lt_exp.mpr hlogP_lt
    _ = Real.sqrt (p n) := Real.exp_log (Real.sqrt_pos.mpr hp0)

/-- Eventually `(1+ε) t_p < log p / 2`.  This is the elementary statement that
`t_p = √(log p · log log p) = o (log p)`. -/
theorem eventually_one_add_mul_paperT_lt_half_log
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (1 + ε) * paperT p n < Real.log (p n) / 2 := by
  have hloglog_o : Asymptotics.IsLittleO atTop
      (fun n => Real.log (Real.log (p n))) (fun n => Real.log (p n)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto h.tendsto_log
  have hratio : Tendsto (fun n => Real.log (Real.log (p n)) /
      Real.log (p n)) atTop (nhds 0) :=
    hloglog_o.tendsto_div_nhds_zero
  have hc : 0 < 1 / (4 * (1 + ε) ^ 2) := by positivity
  filter_upwards [h.eventually_sixteen, h.tendsto_log.eventually_gt_atTop 0,
    (tendsto_order.mp hratio).2 (1 / (4 * (1 + ε) ^ 2)) hc] with n h16 hL hsmall
  have hLpos : 0 < Real.log (p n) := hL
  have hsmall' : Real.log (Real.log (p n)) <
      Real.log (p n) / (4 * (1 + ε) ^ 2) := by
    rw [div_lt_iff₀ hLpos] at hsmall
    calc
      Real.log (Real.log (p n)) <
          (1 / (4 * (1 + ε) ^ 2)) * Real.log (p n) := hsmall
      _ = Real.log (p n) / (4 * (1 + ε) ^ 2) := by ring
  have hαpos : (0 : ℝ) < 1 + ε := by linarith
  have hprod_lt : Real.log (p n) * Real.log (Real.log (p n)) <
      (Real.log (p n) / (2 * (1 + ε))) ^ 2 := by
    have hmul := mul_lt_mul_of_pos_left hsmall' hLpos
    have heq : Real.log (p n) * (Real.log (p n) / (4 * (1 + ε) ^ 2)) =
        (Real.log (p n) / (2 * (1 + ε))) ^ 2 := by
      field_simp
      ring
    linarith [hmul, heq]
  have hb : 0 ≤ Real.log (p n) / (2 * (1 + ε)) := by positivity
  have ht_lt : paperT p n < Real.log (p n) / (2 * (1 + ε)) := by
    calc
      paperT p n = Real.sqrt (Real.log (p n) *
          Real.log (Real.log (p n))) := rfl
      _ < Real.sqrt ((Real.log (p n) / (2 * (1 + ε))) ^ 2) := by
          rw [Real.sqrt_lt_sqrt_iff_of_pos (by positivity :
            (0 : ℝ) < (Real.log (p n) / (2 * (1 + ε))) ^ 2)]
          exact hprod_lt
      _ = Real.log (p n) / (2 * (1 + ε)) := Real.sqrt_sq hb
  have hmul := mul_lt_mul_of_pos_left ht_lt hαpos
  have heq : (1 + ε) * (Real.log (p n) / (2 * (1 + ε))) =
      Real.log (p n) / 2 := by
    field_simp
  linarith [hmul, heq]

/-- **The canonical central-scale strip has no prime supply.**  For every
`K ≥ 0`, the insertion guard of the character-sum argument fails eventually on
the strip `P^m = p²/2 - p^{3/2}/8`, `m δ = log (1 + 1/(4√p))`. -/
theorem eventually_centralStrip_guard_false
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ n in atTop,
      ¬ centralBinGuard K (centralStripP p ε n) (centralStripDelta p ε n)
        (paperDensityY p ε n) (centralStripJ p ε n) (paperDensityM p ε n) := by
  have hu := tendsto_paperDensityU_of_growth h hε
  filter_upwards [h.eventually_sixteen,
    eventually_paperDensityU_gt_one_of_tendsto hu,
    eventually_one_add_mul_paperT_lt_half_log h hε] with n h16 hu1 hsmall
  have hp2 : 2 ≤ p n := by linarith
  have hp1 : 1 < p n := by linarith
  have hp0 : 0 < p n := by linarith
  have hlogu : 0 < Real.log (paperDensityU p ε n) := Real.log_pos hu1
  have hmpos_nat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hm : 1 ≤ paperDensityM p ε n := hmpos_nat
  have hmu : paperDensityU p ε n ≤ (paperDensityM p ε n : ℝ) :=
    paperDensityU_le_paperDensityM p ε n (zero_lt_one.trans hu1) hlogu
  have hPpos : 0 < centralStripP p ε n := by
    unfold centralStripP
    exact Real.rpow_pos_of_pos (centralStripBase_pos hp2) _
  have hP_le : centralStripP p ε n < Real.sqrt (p n) :=
    centralStripP_lt_sqrt hp2 h16 hε hm (zero_lt_one.trans hu1) hmu hsmall
  have hδ : 0 ≤ centralStripDelta p ε n := centralStripDelta_nonneg hp0
  have hlo : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 <
      2 * centralStripP p ε n ^ paperDensityM p ε n := by
    rw [centralStripP_pow (p := p) (ε := ε) hp2 hmpos_nat]
    exact centralStrip_lower hp2
  have hhi : 2 * (centralStripP p ε n ^ paperDensityM p ε n *
      Real.exp ((paperDensityM p ε n : ℝ) * centralStripDelta p ε n)) ≤
      p n ^ 2 := by
    rw [centralStripP_pow (p := p) (ε := ε) hp2 hmpos_nat]
    exact centralStrip_upper (p := p) (ε := ε) hp2 hmpos_nat
  exact centralSupplyGuard_false_of_strip (p := p n)
    (m := paperDensityM p ε n) (P := centralStripP p ε n)
    (δ := centralStripDelta p ε n) (y := paperDensityY p ε n)
    (J := centralStripJ p ε n) hp1 hm hPpos hδ hP_le hlo hhi hK

/-- **Any central strip centre with `P^m ≤ p²/2` and `m ≥ u` is below `√p`.**
This is the abstract form of `centralStripP_lt_sqrt`, and it is what makes the
supply obstruction independent of the particular choice of bins. -/
theorem centre_lt_sqrt_of_le {P p u t ε : ℝ} {m : ℕ}
    (hp : 1 < p) (hm : 0 < m) (hP : 0 < P)
    (hPm : P ^ m ≤ p ^ 2 / 2)
    (hu_pos : 0 < u) (hmu : u ≤ (m : ℝ))
    (hu : u = 2 * Real.log p / ((1 + ε) * t))
    (ht : 0 < t) (hα : 0 < 1 + ε)
    (hsmall : (1 + ε) * t < Real.log p / 2) :
    P < Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlogp_pos : 0 < Real.log p := Real.log_pos hp
  have hPm_le : P ^ m ≤ p ^ 2 := by
    have hp2 : (0 : ℝ) < p ^ 2 / 2 := by positivity
    nlinarith [hPm, hp2]
  have hlog_le : Real.log (P ^ m) ≤ Real.log (p ^ 2) :=
    Real.log_le_log (pow_pos hP _) hPm_le
  have hlogPm : Real.log (P ^ m) = (m : ℝ) * Real.log P := by
    rw [Real.log_pow]
  have hlogp2 : Real.log (p ^ 2) = 2 * Real.log p := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogPm, hlogp2] at hlog_le
  have hlogP_le : Real.log P ≤ 2 * Real.log p / (m : ℝ) := by
    rw [le_div_iff₀ hmpos]
    linarith
  have hdiv_le : 2 * Real.log p / (m : ℝ) ≤ 2 * Real.log p / u :=
    div_le_div_of_nonneg_left (by positivity) hu_pos hmu
  have hαt_ne : (1 + ε) * t ≠ 0 := (mul_pos hα ht).ne'
  have hval : 2 * Real.log p / u = (1 + ε) * t := by
    rw [hu]
    field_simp
  have hlogP_lt : Real.log P < Real.log p / 2 := by
    have hle : Real.log P ≤ (1 + ε) * t := by
      calc Real.log P ≤ 2 * Real.log p / (m : ℝ) := hlogP_le
        _ ≤ 2 * Real.log p / u := hdiv_le
        _ = (1 + ε) * t := hval
    linarith
  have hslog : Real.log (Real.sqrt p) = Real.log p / 2 := Real.log_sqrt hp0.le
  rw [← hslog] at hlogP_lt
  calc
    P = Real.exp (Real.log P) := (Real.exp_log hP).symm
    _ < Real.exp (Real.log (Real.sqrt p)) := Real.exp_lt_exp.mpr hlogP_lt
    _ = Real.sqrt p := Real.exp_log (Real.sqrt_pos.mpr hp0)

/-- **The guard obstruction for an arbitrary central strip.**  This discharges
the abstract centre bound of `centralSupplyGuard_false_of_strip` from the
interval containment, `m ≥ u`, and the paper-scale smallness
`(1+ε) t_p < log p / 2`.  No bin construction satisfying the central interval
containment can have the L30 prime supply. -/
theorem centralSupplyGuard_false_of_centralInterval
    {K P δ y p u t : ℝ} {J m : ℕ} {ε : ℝ}
    (hp : 1 < p) (hm : 1 ≤ m)
    (hP : 0 < P) (hδ : 0 ≤ δ)
    (hlo : p ^ 2 - p ^ ((3 : ℝ) / 2) / 2 < 2 * P ^ m)
    (hhi : 2 * (P ^ m * Real.exp ((m : ℝ) * δ)) ≤ p ^ 2)
    (hu_pos : 0 < u) (hmu : u ≤ (m : ℝ))
    (hu : u = 2 * Real.log p / ((1 + ε) * t))
    (ht : 0 < t) (hα : 0 < 1 + ε)
    (hsmall : (1 + ε) * t < Real.log p / 2)
    (hK : 0 ≤ K) :
    ¬ centralBinGuard K P δ y J m := by
  have hmpos_nat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hPpow_pos : 0 < P ^ m := pow_pos hP m
  have hexp_one : (1 : ℝ) ≤ Real.exp ((m : ℝ) * δ) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hJ : (0 : ℝ) ≤ (m : ℝ) := hmpos.le
    nlinarith [hδ, hJ]
  have hPm_le : P ^ m ≤ p ^ 2 / 2 := by
    have hhalf : P ^ m * Real.exp ((m : ℝ) * δ) ≤ p ^ 2 / 2 := by
      nlinarith [hhi]
    nlinarith [hhalf, hexp_one, hPpow_pos]
  have hP_le : P < Real.sqrt p :=
    centre_lt_sqrt_of_le (P := P) (p := p) (u := u) (t := t) (ε := ε) (m := m)
      hp hmpos_nat hP hPm_le hu_pos hmu hu ht hα hsmall
  exact centralSupplyGuard_false_of_strip (p := p) (m := m) (P := P)
    (δ := δ) (y := y) (J := J) hp hm hP hδ hP_le hlo hhi hK

/-- The central-window prime supply: the per-bin insertion guard of the L30
character-sum argument at the central place `p²/2` and the window width
`m δ = log (1 + 1/(4√p))`.  It is the L30 analogue of
`Cogentic.RandomizedL21_2CentralBin.CentralWindowSupply`. -/
def CentralWindowPrimeSupply (p : ℕ → ℝ) (ε : ℝ) (K : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    centralBinGuard K (centralStripP p ε n) (centralStripDelta p ε n)
      (paperDensityY p ε n) (centralStripJ p ε n) (paperDensityM p ε n)

/-- **No central-window prime supply exists at the L30 central scale.**  This
is the exact central-scale analogue of
`not_eventually_centralWindowSupply`; the interval is wide enough for the
strip, but the bins are below the GRH prime-counting error. -/
theorem not_centralWindowPrimeSupply {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) :
    ¬ CentralWindowPrimeSupply p ε K := by
  intro hsupply
  have hfalse := eventually_centralStrip_guard_false h hε hK
  have hboth : ∀ᶠ n in atTop, False :=
    (hsupply.and hfalse).mono fun _ hn => hn.2 hn.1
  obtain ⟨_, hn⟩ := hboth.exists
  exact hn

/-! ## 4. The strip lies in the central interval -/

/-- **The doubled central strip is made of central odd smooth orders.**  This
is the central-scale instance of
`doubledCenteredBinProducts_subset_centralOddSmoothOrders`: the geometric
containment `hlo`, `hhi` is supplied by `centralStrip_lower` and
`centralStrip_upper`, so only the bin-floor bounds remain as hypotheses. -/
theorem centralStripDoubled_subset_centralOddSmoothOrders
    {p : ℕ → ℝ} {ε : ℝ} {n J a : ℕ}
    (hp : 2 ≤ p n) (hm : 0 < paperDensityM p ε n)
    (hodd : ∀ j < J, 3 ≤ centeredBinFloor (centralStripP p ε n)
      (centralStripDelta p ε n) a (paperDensityM p ε n) j)
    (hfloor : ∀ j < J, (centeredBinFloor (centralStripP p ε n)
      (centralStripDelta p ε n) a (paperDensityM p ε n) (j + 1) : ℝ) ≤
        smoothCutoff (paperT p) (paperError ε) n)
    (hy2 : 2 ≤ smoothCutoff (paperT p) (paperError ε) n) :
    doubledCenteredBinProducts (centralStripP p ε n) (centralStripDelta p ε n)
      J (paperDensityM p ε n) a ⊆
        centralOddSmoothOrders p (paperT p) (paperError ε) n := by
  have hPnonneg : (0 : ℝ) ≤ centralStripP p ε n :=
    (Real.rpow_pos_of_pos (centralStripBase_pos hp) _).le
  have hlo : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 <
      2 * centralStripP p ε n ^ paperDensityM p ε n := by
    rw [centralStripP_pow (p := p) (ε := ε) hp hm]
    exact centralStrip_lower hp
  have hhi : 2 * (centralStripP p ε n ^ paperDensityM p ε n *
      Real.exp ((paperDensityM p ε n : ℝ) * centralStripDelta p ε n)) ≤
      p n ^ 2 := by
    rw [centralStripP_pow (p := p) (ε := ε) hp hm]
    exact centralStrip_upper (p := p) (ε := ε) hp hm
  exact doubledCenteredBinProducts_subset_centralOddSmoothOrders
    (p := p) (t := paperT p) (err := paperError ε) (n := n)
    hPnonneg hm hodd hlo hhi hfloor hy2

/-! ## 5. Reduction to the explicit `p^{3/2}` sharp count -/

/-- The sharp central odd count in its smallest explicit `p^{3/2}` form.  This
is definitionally `YounisOddPaperSharpCount`. -/
abbrev SharpCentralOddSmoothCount (c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  YounisOddPaperSharpCount c p ε

/-- The explicit `p^{3/2}` sharp count gives the interval-length sharp count. -/
theorem sharpCentralOddSmoothCount_implies_intervalCount
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n)
    (h : SharpCentralOddSmoothCount c p ε) :
    YounisOddPaperSharpIntervalCount c p ε :=
  paperSharpIntervalCount_of_paperSharpCount hp h

/-- Conversely, the interval-length sharp count gives the explicit `p^{3/2}`
count with the forced constant `c/4`, because the central interval contains at
least `p^{3/2}/4` integers (`centralOrderInterval_card_ge_quarter`). -/
theorem paperSharpCount_of_intervalCount_quarter
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddPaperSharpIntervalCount c p ε) :
    YounisOddPaperSharpCount (c / 4) p ε := by
  filter_upwards [h] with n hn
  have hlow := centralOrderInterval_card_ge_quarter (p := p) (n := n) (hp n)
  have hp_pos : (0 : ℝ) < p n := by linarith [hp n]
  have he : (0 : ℝ) ≤ Real.exp (-(paperDensityU p ε n *
      Real.log (paperDensityU p ε n))) := (Real.exp_pos _).le
  have hcount_non : (0 : ℝ) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n := by
    unfold centralOddSmoothCount
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
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpow_non) he
    exact hleft.trans hcount_non

/-- **The interval form and the explicit `p^{3/2}` form are equivalent up to
the forced constant `4`.**  This is the precise sense in which
`SharpCentralOddSmoothCount` is the smallest explicit analytic input: no
interval-cardinality information is lost beyond the rounding of the two
endpoints. -/
theorem sharpCentralOddSmoothCount_iff_interval
    {c : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hp : ∀ n, 2 ≤ p n) :
    (SharpCentralOddSmoothCount c p ε →
        YounisOddPaperSharpIntervalCount c p ε) ∧
      (YounisOddPaperSharpIntervalCount c p ε →
        SharpCentralOddSmoothCount (c / 4) p ε) :=
  ⟨fun h => sharpCentralOddSmoothCount_implies_intervalCount hp h,
    fun h => paperSharpCount_of_intervalCount_quarter hp h⟩

/-! ## Axiom audit -/

#print axioms centralStripBase_pos
#print axioms centralStripP_pow
#print axioms centralStripDelta_mul_m
#print axioms centralStrip_lower
#print axioms centralStrip_upper
#print axioms neg_log_one_sub_le_two_mul
#print axioms centralSupplyGuard_false_of_strip
#print axioms centre_lt_sqrt_of_le
#print axioms centralSupplyGuard_false_of_centralInterval
#print axioms centralStripP_lt_sqrt
#print axioms eventually_one_add_mul_paperT_lt_half_log
#print axioms eventually_centralStrip_guard_false
#print axioms not_centralWindowPrimeSupply
#print axioms centralStripDoubled_subset_centralOddSmoothOrders
#print axioms sharpCentralOddSmoothCount_implies_intervalCount
#print axioms paperSharpCount_of_intervalCount_quarter
#print axioms sharpCentralOddSmoothCount_iff_interval

end

end Cogentic.RandomizedL30CentralCount
