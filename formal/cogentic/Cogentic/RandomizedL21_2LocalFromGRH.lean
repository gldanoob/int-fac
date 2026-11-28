import Cogentic.RandomizedL21_2ShortIntervalTransfer
import Cogentic.RandomizedL30SmoothDensity

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-!
# L21.2: the short-interval smooth count from the paper-scale bin count

`Cogentic.RandomizedL21_2ShortIntervalTransfer` reduces the L21.2 local input
`ShortIntervalSmoothCountLower p c X` to a positive prime-bin count together
with the two interval endpoints

```
p - √p  <  P ^ k        and        P ^ k * exp (k δ)  <  p + √p .
```

The paper-scale bin count of `Cogentic.RandomizedL30SmoothDensity` is

```
eventually_paperDensity_binCount :
  (1/8) * p ^ 2 * exp (-(1+ε) t_p)  ≤  #(centeredBinProducts
      (paperDensityP p ε) (paperDensityDelta p ε) (paperDensityJ p ε)
      (paperDensityM p ε) a)
```

with the geometric bin centre satisfying

```
paperDensityP p ε n ^ paperDensityM p ε n = p n ^ 2 / 4 .
```

This file does three things.

## 1. The cutoff match

The L21.2 cutoff is `smoothCutoff c X n = exp (c √(U log U))` with `U = log X`,
while the L30 density cutoff is `paperDensityY p ε n = exp ((1+ε) t_p)`.
We exhibit the explicit L21.2 band scale

```
localX p ε c n = exp (((1+ε) t_p / c) ^ 2)
```

and prove `paperDensityY p ε n ≤ smoothCutoff c (localX p ε c) n` eventually
(`eventually_paperDensityY_le_smoothCutoff_localX`), i.e. the L30 smoothness
cutoff is dominated by the L21.2 one.  For the large-cutoff form we also
exhibit `largeLocalX p c n = exp ((3 log p / c)^2)` and prove both
`p^3 ≤ smoothCutoff c (largeLocalX p c) n` and, for `ε ≤ 2`, the density-cutoff
domination (`largeCutoff_localX_le_smoothCutoff`,
`eventually_paperDensityY_le_smoothCutoff_largeLocalX`).  This discharges the
`p^3 ≤ smoothCutoff` bookkeeping explicitly.

## 2. The conditional transfer from the paper bin count

`shortIntervalSmoothCountLower_of_paperBinCount` uses the paper bin count and
the existing transfer lemma to prove `ShortIntervalSmoothCountLower p c X`.
Two residuals are kept explicit and are *not* hidden:

* `hwin` — the strict **upper window inequality**
  `P^m * exp (m δ) < p + √p` for the bin strip;
* `hdemand` — the L21.2 demand is below the paper-scale bin count,
  `√X exp (-R) ≤ (1/8) p^2 exp (-(1+ε) t_p)`.

The lower window inequality is proved outright
(`paperStrip_lower_lt_window`).  A large-cutoff version
(`shortIntervalSmoothCountLower_of_paperBinCount_largeCutoff`) replaces the bin
floor bookkeeping by the explicit dominance `p^3 ≤ smoothCutoff`.

## 3. What remains: the paper strip sits at `p^2 / 4`, not at `p`

The crucial point is that the L30 geometric bin centre is *not* the L21.2 centre
`p`: its `m`-th power is `p^2/4`.  Hence even the *lower* end of the strip is
`p^2/4`, which eventually exceeds `p + √p`.  Consequently the upper window
inequality `hwin` is **false** for `paperDensityP`, and the paper-scale global
bin count cannot be transferred to the literal `√p`-window by this route.  This
is formalized as

```
not_eventually_paperDensity_strip_upper_window
```

and the precise residual is stated in the docstring and by
`paperDensity_strip_window_obstruction`: a prime-bin construction whose centre
is `p` (the paper's central-density construction), not `p^2/4`, is required.
No count is set to zero: the demand and the bin count are both strictly
positive, and the conditional transfer keeps the short-interval count positive
(`paperBin_shortSmoothCount_pos`).

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2LocalFromGRH

open Filter Real
open Cogentic.Randomized
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Density
open Cogentic.RandomizedL21_2LocalCount
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2ShortIntervalTransfer
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Interval

/-! ## 1. The cutoff match -/

/-- The L21.2 band scale that matches the paper density cutoff.  Its logarithm
is `((1+ε) t_p / c)^2`, so `c * paperRate` is at least `(1+ε) t_p` as soon as
`(1+ε) t_p / c ≥ e`. -/
def localX (p : ℕ → ℝ) (ε c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (((1 + ε) * paperT p n / c) ^ 2)

/-- The large-cutoff L21.2 band scale: its logarithm is `(3 log p / c)^2`, which
makes `smoothCutoff` at least `p^3`. -/
def largeLocalX (p : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((3 * Real.log (p n) / c) ^ 2)

theorem localX_pos (p : ℕ → ℝ) (ε c : ℝ) (n : ℕ) : 0 < localX p ε c n :=
  Real.exp_pos _

theorem largeLocalX_pos (p : ℕ → ℝ) (c : ℝ) (n : ℕ) : 0 < largeLocalX p c n :=
  Real.exp_pos _

theorem bandLog_localX (p : ℕ → ℝ) (ε c : ℝ) (n : ℕ) :
    bandLog (localX p ε c) n = ((1 + ε) * paperT p n / c) ^ 2 := by
  unfold bandLog localX
  rw [Real.log_exp]

theorem bandLog_largeLocalX (p : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    bandLog (largeLocalX p c) n = (3 * Real.log (p n) / c) ^ 2 := by
  unfold bandLog largeLocalX
  rw [Real.log_exp]

/-- **The L30 density cutoff is dominated by the L21.2 cutoff at `localX`.** -/
theorem eventually_paperDensityY_le_smoothCutoff_localX
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε c : ℝ}
    (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      paperDensityY p ε n ≤ smoothCutoff c (localX p ε c) n := by
  have htend := tendsto_paperT_of_growth h
  have hα : 0 < 1 + ε := by positivity
  filter_upwards [eventually_paperT_pos_of_growth h,
    htend.eventually_ge_atTop (Real.exp 1 * c / (1 + ε))] with n ht hbig
  set A : ℝ := (1 + ε) * paperT p n / c with hA
  have hApos : 0 < A := by positivity
  have hAge : Real.exp 1 ≤ A := by
    have hcoe : 0 < (1 + ε) / c := by positivity
    rw [hA]
    calc Real.exp 1 = (Real.exp 1 * c / (1 + ε)) * ((1 + ε) / c) := by
          field_simp [hc.ne', hα.ne']
      _ ≤ paperT p n * ((1 + ε) / c) := by
          exact mul_le_mul_of_nonneg_right hbig hcoe.le
      _ = (1 + ε) * paperT p n / c := by ring
  have hU : bandLog (localX p ε c) n = A ^ 2 := bandLog_localX p ε c n
  have hA2pos : 0 < A ^ 2 := sq_pos_of_pos hApos
  have hlogA : 1 ≤ Real.log A := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log A := Real.log_le_log (Real.exp_pos 1) hAge
  have hlogU : 1 ≤ Real.log (A ^ 2) := by
    rw [Real.log_pow]
    push_cast
    nlinarith
  have hsqrt : A ≤ Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by
    have hmul : A ^ 2 * 1 ≤ A ^ 2 * Real.log (A ^ 2) :=
      mul_le_mul_of_nonneg_left hlogU (sq_nonneg A)
    calc A = Real.sqrt (A ^ 2) := (Real.sqrt_sq hApos.le).symm
      _ ≤ Real.sqrt (A ^ 2 * Real.log (A ^ 2)) :=
          Real.sqrt_le_sqrt (by simpa using hmul)
  have hrate : paperRate (localX p ε c) n = Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by
    unfold paperRate
    rw [hU]
  have hmain : (1 + ε) * paperT p n ≤ c * paperRate (localX p ε c) n := by
    rw [hrate]
    calc (1 + ε) * paperT p n = c * A := by
          rw [hA]
          field_simp [hc.ne']
      _ ≤ c * Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by gcongr
  unfold paperDensityY smoothCutoff logCutoff
  exact Real.exp_le_exp.mpr hmain

/-- **The large-cutoff scale really dominates `p^3`.** -/
theorem largeCutoff_localX_le_smoothCutoff
    {p : ℕ → ℝ} {n : ℕ} (hp : 16 ≤ p n) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    p n ^ 3 ≤ smoothCutoff c (largeLocalX p c) n := by
  have hp0 : 0 < p n := by linarith
  have hL : 1 ≤ Real.log (p n) := (one_lt_log_of_sixteen hp).le
  set A : ℝ := 3 * Real.log (p n) / c with hA
  have hApos : 0 < A := by positivity
  have hAge : (3 : ℝ) ≤ A := by
    rw [hA]
    rw [le_div_iff₀ hc0]
    nlinarith [hL, hc1]
  have hAexp : Real.exp 1 ≤ A := by
    have h3 : Real.exp 1 ≤ (3 : ℝ) := le_of_lt Real.exp_one_lt_three
    linarith
  have hlogA : 1 ≤ Real.log A := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log A := Real.log_le_log (Real.exp_pos 1) hAexp
  have hU : bandLog (largeLocalX p c) n = A ^ 2 := bandLog_largeLocalX p c n
  have hlogU : 1 ≤ Real.log (A ^ 2) := by
    rw [Real.log_pow]
    push_cast
    nlinarith
  have hsqrt : A ≤ Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by
    have hmul : A ^ 2 * 1 ≤ A ^ 2 * Real.log (A ^ 2) :=
      mul_le_mul_of_nonneg_left hlogU (sq_nonneg A)
    calc A = Real.sqrt (A ^ 2) := (Real.sqrt_sq hApos.le).symm
      _ ≤ Real.sqrt (A ^ 2 * Real.log (A ^ 2)) :=
          Real.sqrt_le_sqrt (by simpa using hmul)
  have hrate : paperRate (largeLocalX p c) n = Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by
    unfold paperRate
    rw [hU]
  have hmain : 3 * Real.log (p n) ≤ c * paperRate (largeLocalX p c) n := by
    rw [hrate]
    calc 3 * Real.log (p n) = c * A := by
          rw [hA]
          field_simp [hc0.ne']
      _ ≤ c * Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by gcongr
  calc p n ^ 3 = Real.exp (Real.log (p n ^ 3)) :=
        (Real.exp_log (pow_pos hp0 3)).symm
    _ = Real.exp (3 * Real.log (p n)) := by
        rw [Real.log_pow]
        push_cast
        ring_nf
    _ ≤ Real.exp (c * paperRate (largeLocalX p c) n) := Real.exp_le_exp.mpr hmain
    _ = smoothCutoff c (largeLocalX p c) n := rfl

/-- **The density cutoff is dominated at the large-cutoff scale** when `ε ≤ 2`. -/
theorem eventually_paperDensityY_le_smoothCutoff_largeLocalX
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε c : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 2) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      paperDensityY p ε n ≤ smoothCutoff c (largeLocalX p c) n := by
  filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h] with n hp ht
  have hp0 : 0 < p n := by linarith
  have hL : 1 ≤ Real.log (p n) := (one_lt_log_of_sixteen hp).le
  set A : ℝ := 3 * Real.log (p n) / c with hA
  have hApos : 0 < A := by positivity
  have hAge : (3 : ℝ) ≤ A := by
    rw [hA]
    rw [le_div_iff₀ hc0]
    nlinarith [hL, hc1]
  have hAexp : Real.exp 1 ≤ A := by
    have h3 : Real.exp 1 ≤ (3 : ℝ) := le_of_lt Real.exp_one_lt_three
    linarith
  have hlogA : 1 ≤ Real.log A := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log A := Real.log_le_log (Real.exp_pos 1) hAexp
  have hU : bandLog (largeLocalX p c) n = A ^ 2 := bandLog_largeLocalX p c n
  have hlogU : 1 ≤ Real.log (A ^ 2) := by
    rw [Real.log_pow]
    push_cast
    nlinarith
  have hsqrt : A ≤ Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by
    have hmul : A ^ 2 * 1 ≤ A ^ 2 * Real.log (A ^ 2) :=
      mul_le_mul_of_nonneg_left hlogU (sq_nonneg A)
    calc A = Real.sqrt (A ^ 2) := (Real.sqrt_sq hApos.le).symm
      _ ≤ Real.sqrt (A ^ 2 * Real.log (A ^ 2)) :=
          Real.sqrt_le_sqrt (by simpa using hmul)
  have hrate : paperRate (largeLocalX p c) n = Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by
    unfold paperRate
    rw [hU]
  have hrate_ge : 3 * Real.log (p n) ≤ c * paperRate (largeLocalX p c) n := by
    rw [hrate]
    calc 3 * Real.log (p n) = c * A := by
          rw [hA]
          field_simp [hc0.ne']
      _ ≤ c * Real.sqrt (A ^ 2 * Real.log (A ^ 2)) := by gcongr
  have htL : paperT p n ≤ Real.log (p n) := by
    unfold paperT
    have hlogle : Real.log (Real.log (p n)) ≤ Real.log (p n) :=
      Real.log_le_self (by linarith)
    have hLnn : (0 : ℝ) ≤ Real.log (p n) := by linarith
    calc Real.sqrt (Real.log (p n) * Real.log (Real.log (p n)))
        ≤ Real.sqrt (Real.log (p n) * Real.log (p n)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlogle hLnn)
      _ = Real.log (p n) := Real.sqrt_mul_self hLnn
  have hα : 0 < 1 + ε := by positivity
  have ht_le : (1 + ε) * paperT p n ≤ 3 * Real.log (p n) := by
    have h1 : (1 + ε) * paperT p n ≤ (1 + ε) * Real.log (p n) :=
      mul_le_mul_of_nonneg_left htL hα.le
    have h2 : (1 + ε) * Real.log (p n) ≤ 3 * Real.log (p n) := by
      have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) + ε ≤ 3) (by linarith : (0:ℝ) ≤ Real.log (p n))
      simpa using this
    linarith
  have hmain : (1 + ε) * paperT p n ≤ c * paperRate (largeLocalX p c) n :=
    ht_le.trans hrate_ge
  unfold paperDensityY smoothCutoff logCutoff
  exact Real.exp_le_exp.mpr hmain

/-! ## 2. The paper strip and the `√p`-window -/

/-- The lower end of the paper-scale bin strip lies below the window: the strip
starts at `P^m = p^2/4 ≥ p > p - √p`. -/
theorem paperStrip_lower_lt_window {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 16 ≤ p n) (hm : 0 < paperDensityM p ε n) :
    p n - Real.sqrt (p n) <
      paperDensityP p ε n ^ paperDensityM p ε n := by
  have hp0 : 0 < p n := by linarith
  rw [paperDensityP_pow hp0 hm]
  have hsp : Real.sqrt (p n) ≤ p n / 4 := sqrt_le_quarter hp
  have hspos : 0 < Real.sqrt (p n) := Real.sqrt_pos.mpr hp0
  have hp4 : (4 : ℝ) ≤ p n := by linarith
  have hpp : 4 * p n ≤ p n * p n := by nlinarith
  nlinarith

/-- The upper end of the paper-scale bin strip lies above the window: the strip
ends at `(p^2/4) * exp (m δ) ≥ p^2/4 ≥ p + √p` eventually. -/
theorem paperStrip_upper_ge_window {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 16 ≤ p n) (hm : 0 < paperDensityM p ε n)
    (hδ : 0 ≤ paperDensityDelta p ε n) :
    p n + Real.sqrt (p n) ≤
      paperDensityP p ε n ^ paperDensityM p ε n *
        Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) := by
  have hp0 : 0 < p n := by linarith
  rw [paperDensityP_pow hp0 hm]
  have hexp1 : (1 : ℝ) ≤
      Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hδ)
  have hq : (0 : ℝ) ≤ p n ^ 2 / 4 := by positivity
  have hstep : p n ^ 2 / 4 ≤ p n ^ 2 / 4 *
      Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) := by
    calc p n ^ 2 / 4 = p n ^ 2 / 4 * 1 := by ring
      _ ≤ p n ^ 2 / 4 * Real.exp _ := by gcongr
  have hsp : Real.sqrt (p n) ≤ p n / 4 := sqrt_le_quarter hp
  have hwin : p n + Real.sqrt (p n) ≤ p n ^ 2 / 4 := by
    have hp5 : (5 : ℝ) ≤ p n := by linarith
    nlinarith
  exact hwin.trans hstep

/-- **The exact obstruction.**  For the paper-scale bin centre,
`P^m * exp (m δ) ≥ p^2/4`, so the paper strip is never inside the open
`√p`-window around `p`.  This is what remains: the L30 bin construction is
centred at `p^2/4`, not at the L21.2 centre `p`. -/
theorem paperDensity_strip_window_obstruction
    {p : ℕ → ℝ} {ε : ℝ} (h : PaperDensityGrowth p) (hε : 0 < ε) :
    (∀ᶠ n : ℕ in atTop,
        p n + Real.sqrt (p n) ≤
          paperDensityP p ε n ^ paperDensityM p ε n *
            Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n)) ∧
      ¬ (∀ᶠ n : ℕ in atTop,
          paperDensityP p ε n ^ paperDensityM p ε n *
            Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) <
              p n + Real.sqrt (p n)) := by
  have hu1 : ∀ᶠ n : ℕ in atTop, 1 < paperDensityU p ε n :=
    eventually_paperDensityU_gt_one_of_tendsto
      (tendsto_paperDensityU_of_growth h hε)
  have hmpos : ∀ᶠ n : ℕ in atTop, 0 < paperDensityM p ε n := by
    refine hu1.mono ?_
    intro n hn
    exact paperDensityM_pos hn
  have hJpos : ∀ᶠ n : ℕ in atTop, 0 < paperDensityJ p ε n := by
    refine hmpos.mono ?_
    intro n hn
    exact paperDensityJ_pos hn
  have htpos : ∀ᶠ n : ℕ in atTop, 0 < paperT p n :=
    eventually_paperT_pos_of_growth h
  have hδnn : ∀ᶠ n : ℕ in atTop, 0 ≤ paperDensityDelta p ε n := by
    filter_upwards [hu1, htpos, hJpos] with n hu1n htn hJn
    exact (paperDensityDelta_pos hε htn hJn (Real.log_pos hu1n)).le
  have hge : ∀ᶠ n : ℕ in atTop,
      p n + Real.sqrt (p n) ≤
        paperDensityP p ε n ^ paperDensityM p ε n *
          Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) := by
    filter_upwards [h.eventually_sixteen, hmpos, hδnn] with n hp hm hδ
    exact paperStrip_upper_ge_window hp hm hδ
  refine ⟨hge, ?_⟩
  intro hlt
  obtain ⟨n, hn1, hn2⟩ := (hlt.and hge).exists
  exact (lt_irrefl _ (hn1.trans_le hn2))

/-- The *smallest explicit interval inequality* of the paper-bin route: the
paper-scale bin strip lies strictly inside the L21.2 `√p`-window. -/
def PaperBinWindow (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    paperDensityP p ε n ^ paperDensityM p ε n *
      Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) <
        p n + Real.sqrt (p n)

/-- **`PaperBinWindow` is false at the paper scale.**  The strip is centred at
`p^2/4`, whose lower end already exceeds `p + √p`.  Hence the paper-scale
global bin count cannot provide the local `√p`-window count; the missing
ingredient is a bin construction centred at `p`, not at `p^2/4`. -/
theorem paperBinWindow_false {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) : ¬ PaperBinWindow p ε := by
  intro hw
  exact (paperDensity_strip_window_obstruction h hε).2 hw

/-! ## 3. The conditional transfer from the paper bin count -/

/-- **From the paper-scale prime-bin count to `ShortIntervalSmoothCountLower`.**

The lower endpoint is proved outright (`paperStrip_lower_lt_window`).  The two
displayed hypotheses are the only residuals: the strict upper window inequality
`hwin` and the demand domination `hdemand`.  The density-cutoff domination is
`hcut`; it can be supplied by
`eventually_paperDensityY_le_smoothCutoff_localX`. -/
theorem shortIntervalSmoothCountLower_of_paperBinCount
    (line : DirichletLZerosOnLine)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε c : ℝ} (hε : 0 < ε) (_hc : 0 < c)
    {X : ℕ → ℝ}
    (hwin : ∀ᶠ n : ℕ in atTop,
      paperDensityP p ε n ^ paperDensityM p ε n *
        Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) <
          p n + Real.sqrt (p n))
    (hcut : ∀ᶠ n : ℕ in atTop, paperDensityY p ε n ≤ smoothCutoff c X n)
    (hdemand : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n)) :
    ShortIntervalSmoothCountLower p c X := by
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have ht_tend := tendsto_paperT_of_growth h
  have hu1 : ∀ᶠ n : ℕ in atTop, 1 < paperDensityU p ε n :=
    eventually_paperDensityU_gt_one_of_tendsto hu_tend
  have hmpos : ∀ᶠ n : ℕ in atTop, 0 < paperDensityM p ε n := by
    refine hu1.mono ?_
    intro n hn
    exact paperDensityM_pos hn
  have hJpos : ∀ᶠ n : ℕ in atTop, 0 < paperDensityJ p ε n := by
    refine hmpos.mono ?_
    intro n hn
    exact paperDensityJ_pos hn
  have htpos : ∀ᶠ n : ℕ in atTop, 0 < paperT p n :=
    eventually_paperT_pos_of_growth h
  have hlogu : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (paperDensityU p ε n) := by
    filter_upwards [hu_tend.eventually_ge_atTop (Real.exp 1)] with n hn
    have hlog := Real.log_le_log (Real.exp_pos 1) hn
    rwa [Real.log_exp] at hlog
  have hδnn : ∀ᶠ n : ℕ in atTop, 0 ≤ paperDensityDelta p ε n := by
    filter_upwards [hu1, htpos, hJpos] with n hu1n htn hJn
    exact (paperDensityDelta_pos hε htn hJn (Real.log_pos hu1n)).le
  have hbin := eventually_paperDensity_binCount line p h hε
  filter_upwards [hbin, h.eventually_sixteen, htpos, hu1, hmpos, hJpos,
    hlogu, hδnn, hwin, hcut, hdemand] with n hbn hp16 htn hu1n hmposn hJposn
      hlogun hδn hwin_n hcut_n hdemand_n
  obtain ⟨a, ha, hcard⟩ := hbn
  have hp1 : (1 : ℝ) < p n := by linarith
  have hp0 : (0 : ℝ) < p n := by linarith
  have hP : (0 : ℝ) ≤ paperDensityP p ε n := (paperDensityP_pos hp0).le
  have hlo := paperStrip_lower_lt_window (p := p) (ε := ε) hp16 hmposn
  have hbinUpper := paperDensity_bin_upper (p := p) (ε := ε) hp1 hmposn
    (paperDensityU_mul_le_M p ε n) hlogun htn hε hJposn
  have hfloor : ∀ j < paperDensityJ p ε n,
      (centeredBinFloor (paperDensityP p ε n) (paperDensityDelta p ε n) a
        (paperDensityM p ε n) (j + 1) : ℝ) ≤ smoothCutoff c X n := by
    intro j hj
    have hj1 : ((j + 1 : ℕ) : ℝ) ≤ (paperDensityJ p ε n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hj)
    have hle_endpoint : centeredBinEndpoint (paperDensityP p ε n)
        (paperDensityDelta p ε n) a (paperDensityM p ε n) (j + 1) ≤
          paperDensityP p ε n *
            Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) := by
      unfold centeredBinEndpoint
      apply mul_le_mul_of_nonneg_left _ hP
      apply Real.exp_le_exp.mpr
      have ha_nonneg : (0 : ℝ) ≤ (a : ℝ) / (paperDensityM p ε n : ℝ) := by
        positivity
      nlinarith [hj1, ha_nonneg, hδn]
    have hfloor_le :
        ((centeredBinFloor (paperDensityP p ε n) (paperDensityDelta p ε n) a
          (paperDensityM p ε n) (j + 1) : ℕ) : ℝ) ≤
          centeredBinEndpoint (paperDensityP p ε n)
            (paperDensityDelta p ε n) a (paperDensityM p ε n) (j + 1) :=
      Nat.floor_le (mul_nonneg hP (Real.exp_pos _).le)
    exact hfloor_le.trans (hle_endpoint.trans (hbinUpper.trans hcut_n))
  have hcard_le := card_centeredBinProducts_le_shortSmoothCount (p := p n)
    (y := smoothCutoff c X n) hp1 hP hmposn hlo hwin_n hfloor
  exact hdemand_n.trans (hcard.trans hcard_le)

/-- **Large-cutoff form of the transfer.**  The bin-floor bookkeeping is
replaced by the explicit dominance `p^3 ≤ smoothCutoff c X n`; the residuals
`hwin` and `hdemand` are unchanged. -/
theorem shortIntervalSmoothCountLower_of_paperBinCount_largeCutoff
    (line : DirichletLZerosOnLine)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε c : ℝ} (hε : 0 < ε) (_hc : 0 < c)
    {X : ℕ → ℝ}
    (hwin : ∀ᶠ n : ℕ in atTop,
      paperDensityP p ε n ^ paperDensityM p ε n *
        Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) <
          p n + Real.sqrt (p n))
    (hcut3 : ∀ᶠ n : ℕ in atTop, p n ^ 3 ≤ smoothCutoff c X n)
    (hdemand : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n)) :
    ShortIntervalSmoothCountLower p c X := by
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have hu1 : ∀ᶠ n : ℕ in atTop, 1 < paperDensityU p ε n :=
    eventually_paperDensityU_gt_one_of_tendsto hu_tend
  have hmpos : ∀ᶠ n : ℕ in atTop, 0 < paperDensityM p ε n := by
    refine hu1.mono ?_
    intro n hn
    exact paperDensityM_pos hn
  have hbin := eventually_paperDensity_binCount line p h hε
  filter_upwards [hbin, h.eventually_sixteen, hmpos, hwin, hcut3, hdemand] with
    n hbn hp16 hmposn hwin_n hcut3_n hdemand_n
  obtain ⟨a, ha, hcard⟩ := hbn
  have hp1 : (1 : ℝ) < p n := by linarith
  have hp2 : (2 : ℝ) ≤ p n := by linarith
  have hp0 : (0 : ℝ) < p n := by linarith
  have hP : (0 : ℝ) ≤ paperDensityP p ε n := (paperDensityP_pos hp0).le
  have hlo := paperStrip_lower_lt_window (p := p) (ε := ε) hp16 hmposn
  have hcard_le := card_centeredBinProducts_le_shortSmoothCount_of_largeCutoff
    (P := paperDensityP p ε n) (δ := paperDensityDelta p ε n)
    (J := paperDensityJ p ε n) (k := paperDensityM p ε n) (a := a)
    (p := p n) (y := smoothCutoff c X n) hp1 hp2 hP hmposn hlo hwin_n hcut3_n
  exact hdemand_n.trans (hcard.trans hcard_le)

/-- **Positivity of the transferred short-interval count.**  Under the
conditional hypotheses the demand `√X exp (-R)` is strictly positive, so the
literal short-interval smooth count is strictly positive. -/
theorem paperBin_shortSmoothCount_pos
    (line : DirichletLZerosOnLine)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {X : ℕ → ℝ}
    (hwin : ∀ᶠ n : ℕ in atTop,
      paperDensityP p ε n ^ paperDensityM p ε n *
        Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) <
          p n + Real.sqrt (p n))
    (hcut : ∀ᶠ n : ℕ in atTop, paperDensityY p ε n ≤ smoothCutoff c X n)
    (hdemand : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n))
    (hXpos : ∀ᶠ n : ℕ in atTop, 0 < X n) :
    ∀ᶠ n : ℕ in atTop,
      0 < shortSmoothCount (p n) (smoothCutoff c X n) := by
  have hcount := shortIntervalSmoothCountLower_of_paperBinCount
    line h hε hc hwin hcut hdemand
  filter_upwards [hcount, hXpos] with n hn hXn
  exact lt_of_lt_of_le (demand_pos (c := c) hXn) hn

/-- **The cutoff is discharged at `localX`; only the window and the demand
remain.** -/
theorem shortIntervalSmoothCountLower_localX_of_window
    (line : DirichletLZerosOnLine)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hwin : ∀ᶠ n : ℕ in atTop,
      paperDensityP p ε n ^ paperDensityM p ε n *
        Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) <
          p n + Real.sqrt (p n))
    (hdemand : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (localX p ε c n) * Real.exp (-(repLog c (localX p ε c) n)) ≤
        (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n)) :
    ShortIntervalSmoothCountLower p c (localX p ε c) :=
  shortIntervalSmoothCountLower_of_paperBinCount line h hε hc hwin
    (eventually_paperDensityY_le_smoothCutoff_localX h hε hc) hdemand

/-- **The large-cutoff bookkeeping `p^3 ≤ smoothCutoff` is discharged at
`largeLocalX`; only the window and the demand remain.** -/
theorem shortIntervalSmoothCountLower_largeLocalX_of_window
    (line : DirichletLZerosOnLine)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε c : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hwin : ∀ᶠ n : ℕ in atTop,
      paperDensityP p ε n ^ paperDensityM p ε n *
        Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) <
          p n + Real.sqrt (p n))
    (hdemand : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (largeLocalX p c n) * Real.exp (-(repLog c (largeLocalX p c) n)) ≤
        (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n)) :
    ShortIntervalSmoothCountLower p c (largeLocalX p c) :=
  shortIntervalSmoothCountLower_of_paperBinCount_largeCutoff line h hε hc0 hwin
    (h.eventually_sixteen.mono fun _ hp =>
      largeCutoff_localX_le_smoothCutoff hp hc0 hc1)
    hdemand

end Cogentic.RandomizedL21_2LocalFromGRH

/-! ## Axiom audit -/

namespace Cogentic.RandomizedL21_2LocalFromGRH

#print axioms localX_pos
#print axioms bandLog_localX
#print axioms eventually_paperDensityY_le_smoothCutoff_localX
#print axioms largeCutoff_localX_le_smoothCutoff
#print axioms eventually_paperDensityY_le_smoothCutoff_largeLocalX
#print axioms paperStrip_lower_lt_window
#print axioms paperStrip_upper_ge_window
#print axioms paperDensity_strip_window_obstruction
#print axioms paperBinWindow_false
#print axioms shortIntervalSmoothCountLower_of_paperBinCount
#print axioms shortIntervalSmoothCountLower_of_paperBinCount_largeCutoff
#print axioms paperBin_shortSmoothCount_pos
#print axioms shortIntervalSmoothCountLower_localX_of_window
#print axioms shortIntervalSmoothCountLower_largeLocalX_of_window

end Cogentic.RandomizedL21_2LocalFromGRH
