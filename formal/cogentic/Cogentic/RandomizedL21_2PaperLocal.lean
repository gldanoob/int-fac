import Cogentic.RandomizedL21_2LocalCount

set_option linter.style.haveILetI false

/-!
# L21.2: the paper-regime local smooth-count reduction

`Cogentic.RandomizedL21_2LocalCount` isolates the local smooth-count input

```
LocalSmoothCountLower p c X :
  ∀ᶠ n, √(X n) * exp (-(R n)) ≤ smoothCountNear p c X n
```

and proves it outright for the *bounded* concrete instance `X = e^3`,
`c = 1`, `p n = 4^n`.  This file handles the *growing* paper regime
`X n → ∞`.

The analytic theorem needed there is the smooth-numbers-in-short-intervals
lower bound: the interval `(p - √p, p + √p)` must contain at least
`√X exp (-R)` integers all of whose prime factors are at most
`exp (c √(U log U))`.  This is not derivable from the elementary
powers-of-two construction.  Indeed, in the paper regime the demand

```
√(X n) * exp (-(R n)) = exp (U/2 - R n)
```

tends to infinity (`PaperRegime.demand_tendsto_atTop`), while a `√p`-window
contains only `O (log p)` powers of two.  Consequently `PowTwoCountLower`
is *false* for every growing paper-regime centre with `p ≲ X^A`
(`not_powTwoCountLower_of_paperRegime`): the powers-of-two shortcut is
strictly a bounded-`X` device.

The correct residual is therefore the full explicit count.  We introduce the
literal open short interval

```
shortInterval p = {m : ℕ | p - √p < m < p + √p}
```

and the explicit smooth subset `shortSmoothInterval p y`.  The predicate

```
ShortIntervalSmoothCountLower p c X :
  ∀ᶠ n, √(X n) * exp (-(R n)) ≤ #(shortSmoothInterval (p n) (exp (c T_X)))
```

is the smallest explicit short-interval smooth-count statement.  We prove

* `shortSmoothInterval_eq_sqrtSmoothNeighbours`: for `p > 1` it is exactly the
  `sqrtSmoothNeighbours` set of `RandomizedL21_2Density`;
* `localSmoothCountLower_iff_shortInterval`: it is *equivalent* to
  `LocalSmoothCountLower` (and hence to the explicit set-count input
  `LocalSetCountLower` of `RandomizedL21_2LocalCount`);
* the paper-regime demand grows without bound
  (`PaperRegime.demand_tendsto_atTop`);
* `PowTwoCountLower` fails in that regime
  (`not_powTwoCountLower_of_paperRegime`);
* `L21_2DensityInputs.ofShortInterval`: the full L21.2 density bundle with its
  `localCount` field supplied by the short-interval count, together with the
  downstream `toPerronInputs`/`toRatedLeaf`/`toSubexpLeaf` chain and the paper
  assumptions reassembly.

No `sorry`, `admit`, `axiom` or `native_decide`; every count is a genuine
`Finset.card`, never set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2PaperLocal

open Filter Real
open Cogentic.Randomized
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2Density
open Cogentic.RandomizedL21_2LocalCount

/-! ## 1. The literal open short interval -/

/-- The integers in the open interval `(p - √p, p + √p)`.  The endpoints are
real, so the lower endpoint is the floor and the upper endpoint the ceiling;
`Finset.Ioo` expresses the two strict inequalities exactly. -/
def shortInterval (p : ℝ) : Finset ℕ :=
  Finset.Ioo ⌊p - Real.sqrt p⌋₊ ⌈p + Real.sqrt p⌉₊

/-- The `y`-smooth integers in the open `√p`-neighbourhood of `p`. -/
noncomputable def shortSmoothInterval (p y : ℝ) : Finset ℕ := by
  classical
  exact (shortInterval p).filter (SmoothUpTo y)

/-- The real-valued cardinality of `shortSmoothInterval`. -/
noncomputable def shortSmoothCount (p y : ℝ) : ℝ :=
  ((shortSmoothInterval p y).card : ℝ)

/-- Membership in the explicit open short interval. -/
theorem mem_shortInterval {p : ℝ} {m : ℕ} :
    m ∈ shortInterval p ↔ ⌊p - Real.sqrt p⌋₊ < m ∧ m < ⌈p + Real.sqrt p⌉₊ := by
  simp [shortInterval]

/-- Membership in the explicit smooth short interval. -/
theorem mem_shortSmoothInterval {p y : ℝ} {m : ℕ} :
    m ∈ shortSmoothInterval p y ↔
      ⌊p - Real.sqrt p⌋₊ < m ∧ m < ⌈p + Real.sqrt p⌉₊ ∧ SmoothUpTo y m := by
  simp [shortSmoothInterval, mem_shortInterval, and_assoc]

/-- For nonnegative `r`, the integer comparison with `Nat.floor` is the strict
real comparison.  This is the lower-endpoint conversion used for the open
interval. -/
theorem nat_floor_lt_iff {r : ℝ} (hr : 0 ≤ r) {m : ℕ} :
    ⌊r⌋₊ < m ↔ r < (m : ℝ) := by
  rw [← not_le, Nat.le_floor_iff hr, not_le]

/-- The open short interval is exactly the `√p`-neighbourhood of
`RandomizedL21_2Density` once `p > 1`.  The two definitions differ only in how
they encode the strict endpoints; this theorem removes that difference. -/
theorem shortSmoothInterval_eq_sqrtSmoothNeighbours {p y : ℝ} (hp : 1 < p) :
    shortSmoothInterval p y = sqrtSmoothNeighbours p y := by
  classical
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpnonneg : (0 : ℝ) ≤ p := hp0.le
  have hsqrt_lt : Real.sqrt p < p := Real.sqrt_lt_self_iff.mpr hp
  have hlow_nonneg : 0 ≤ p - Real.sqrt p := by linarith
  ext m
  rw [mem_shortSmoothInterval, mem_sqrtSmoothNeighbours]
  constructor
  · rintro ⟨hlo, hhi, hsmooth⟩
    have hlo' : p - Real.sqrt p < (m : ℝ) := (nat_floor_lt_iff hlow_nonneg).mp hlo
    have hhi' : (m : ℝ) < p + Real.sqrt p := Nat.lt_ceil.mp hhi
    refine ⟨abs_lt.mpr ⟨?_, ?_⟩, hsmooth⟩
    · linarith
    · linarith
  · rintro ⟨hneigh, hsmooth⟩
    have hlo' : p - Real.sqrt p < (m : ℝ) := by
      have := (abs_lt.mp hneigh).1
      linarith
    have hhi' : (m : ℝ) < p + Real.sqrt p := by
      have := (abs_lt.mp hneigh).2
      linarith
    exact ⟨(nat_floor_lt_iff hlow_nonneg).mpr hlo', Nat.lt_ceil.mpr hhi', hsmooth⟩

/-- The smooth short interval is contained in the paper's explicit
`sqrtSmoothNeighbours` set. -/
theorem shortSmoothInterval_subset_sqrtSmoothNeighbours {p y : ℝ} (hp : 1 < p) :
    shortSmoothInterval p y ⊆ sqrtSmoothNeighbours p y := by
  rw [shortSmoothInterval_eq_sqrtSmoothNeighbours hp]

/-- Its cardinality is the paper's `smoothCountNear`. -/
theorem shortSmoothCount_eq_smoothCountNear {p y : ℝ} (hp : 1 < p) :
    shortSmoothCount p y = ((sqrtSmoothNeighbours p y).card : ℝ) := by
  unfold shortSmoothCount
  rw [shortSmoothInterval_eq_sqrtSmoothNeighbours hp]

/-! ## 2. The smallest explicit short-interval count -/

/-- **The smallest explicit short-interval smooth-count input.**  At each band
the literal open short interval around `p n` contains at least
`√(X n) exp (-(R n))` integers that are smooth up to `exp (c T_X)`.

This is the paper's local count with the finite set written out as an honest
integer interval.  It is equivalent to `LocalSmoothCountLower` for `p > 1`,
and is implied by the even weaker explicit-set input `LocalSetCountLower`. -/
def ShortIntervalSmoothCountLower (p : ℕ → ℝ) (c : ℝ) (X : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
      shortSmoothCount (p n) (smoothCutoff c X n)

/-- The short-interval count implies the local smooth-count bound. -/
theorem localSmoothCountLower_of_shortInterval {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (h : ShortIntervalSmoothCountLower p c X) : LocalSmoothCountLower p c X := by
  filter_upwards [hp, h] with n hp1 hn
  unfold ShortIntervalSmoothCountLower at h
  rw [shortSmoothCount_eq_smoothCountNear hp1] at hn
  simpa [smoothCountNear] using hn

/-- Conversely, the local smooth-count bound is the short-interval count. -/
theorem shortIntervalSmoothCountLower_of_localSmoothCountLower
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (h : LocalSmoothCountLower p c X) : ShortIntervalSmoothCountLower p c X := by
  filter_upwards [hp, h] with n hp1 hn
  unfold LocalSmoothCountLower at h
  rw [shortSmoothCount_eq_smoothCountNear hp1]
  simpa [smoothCountNear] using hn

/-- **The local Prop is exactly the explicit short-interval count.** -/
theorem localSmoothCountLower_iff_shortInterval {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n) :
    LocalSmoothCountLower p c X ↔ ShortIntervalSmoothCountLower p c X :=
  ⟨shortIntervalSmoothCountLower_of_localSmoothCountLower hp,
    localSmoothCountLower_of_shortInterval hp⟩

/-- The existing smallest explicit set-count input already gives the
short-interval count. -/
theorem shortIntervalSmoothCountLower_of_setCount {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (h : LocalSetCountLower p c X) : ShortIntervalSmoothCountLower p c X :=
  shortIntervalSmoothCountLower_of_localSmoothCountLower hp
    (localSmoothCountLower_of_setCount h)

/-- Conversely, the short-interval count supplies the explicit-set input. -/
theorem setCount_of_shortIntervalSmoothCountLower {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (h : ShortIntervalSmoothCountLower p c X) : LocalSetCountLower p c X :=
  setCount_of_localSmoothCountLower (localSmoothCountLower_of_shortInterval hp h)

/-- A powers-of-two count is a sufficient (and, in the growing regime, strictly
stronger) form of the short-interval count. -/
theorem shortIntervalSmoothCountLower_of_powTwoCount
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (h : PowTwoCountLower p c X) : ShortIntervalSmoothCountLower p c X :=
  shortIntervalSmoothCountLower_of_localSmoothCountLower hp
    (localSmoothCountLower_of_powTwoCount h)

/-! ## 3. The growing paper regime -/

/-- The growing paper regime at the explicit parameters of L21.2.

`U = log X → ∞`, and the three manuscript identities for `k`, `Δ`, `b` hold in
the sharp `o(T)` form used by the density normalization:

```
k log k      = (1/(2c) + o(1)) T,
k log (b/2Δ) = o(T),
log (kΔ)     = o(T).
```

The centre `p` is only constrained to be eventually `> 1` (in the paper,
`p ∈ [X, 2X]` and `X → ∞`).  All three rate fields are *proved* in
`L21_2ReducedInputs`; `PaperRegime.ofReducedInputs` records that instance. -/
structure PaperRegime (p : ℕ → ℝ) (c : ℝ) (X : ℕ → ℝ) where
  /-- The centre is eventually larger than one, so the short interval is a
  genuine nondegenerate `√p`-window. -/
  p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < p n
  /-- `X > 1` at every band. -/
  X_gt_one : ∀ n, 1 < X n
  /-- `0 < c`. -/
  c_pos : 0 < c
  /-- `c ≤ 1`, as at the paper's `c = 1/√2`. -/
  c_le_one : c ≤ 1
  /-- `U = log X → ∞`, the growing paper regime. -/
  U_grows : Tendsto (fun n => bandLog X n) atTop atTop
  /-- The sharp `k log k` identity. -/
  kLogK : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    kOf X c n * Real.log (kOf X c n) ≤ ((1 / (2 * c)) + δ) * paperRate X n
  /-- The `k log (b/(2Δ))` identity. -/
  kLogB : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    kOf X c n * Real.log (bOf X c n / (2 * spacingOf X c n)) ≤
      δ * paperRate X n
  /-- The `log (kΔ) + log 40` identity. -/
  kDeltaLog : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    Real.log (kOf X c n * spacingOf X c n) + Real.log 40 ≤ δ * paperRate X n

/-- The reduced L21.2 inputs are a paper regime for any centre that is
eventually greater than one.  This is the bridge from the existing
`L21_2ReducedInputs` bundle to the regime structure above. -/
theorem PaperRegime.ofReducedInputs (I : L21_2ReducedInputs) (p : ℕ → ℝ)
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n) : PaperRegime p I.c I.X where
  p_gt_one := hp
  X_gt_one := I.X_gt_one
  c_pos := I.c_pos
  c_le_one := I.c_le_one
  U_grows := I.U_grows
  kLogK δ hδ := I.kLogK δ hδ
  kLogB δ hδ := I.kLogB δ hδ
  kDeltaLog δ hδ := I.kDeltaLog δ hδ

/-- The density-normalization logarithmic loss is `≤ (1/(2c) + 1) T`. -/
theorem PaperRegime.repLog_le (R : PaperRegime p c X) :
    ∀ᶠ n : ℕ in atTop,
      repLog c X n ≤ ((1 / (2 * c)) + 1) * paperRate X n := by
  have hthird : (0 : ℝ) < 1 / 3 := by norm_num
  filter_upwards [R.kLogK (1 / 3) hthird, R.kLogB (1 / 3) hthird,
    R.kDeltaLog (1 / 3) hthird] with n hk hb hd
  unfold repLog representationLog
  nlinarith

/-- `T / U → 0` in the growing paper regime.  This is the elementary fact that
`√(U log U) = o (U)`. -/
theorem PaperRegime.tendsto_paperRate_div_bandLog (R : PaperRegime p c X) :
    Tendsto (fun n => paperRate X n / bandLog X n) atTop (nhds 0) := by
  have h := Scale.tendsto_t_div_u (u := fun n => bandLog X n) R.U_grows
  simpa [Scale.t, paperRate] using h

/-- The paper-regime demand `√X exp (-R)` dominates `exp ((3/8) U)`. -/
theorem PaperRegime.eventually_exp_three_eighths_le_demand (R : PaperRegime p c X) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((3 / 8) * bandLog X n) ≤
        Real.sqrt (X n) * Real.exp (-(repLog c X n)) := by
  have hKpos : 0 < (1 / (2 * c) + 1) := by
    have hc := R.c_pos
    positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,
      paperRate X n / bandLog X n < 1 / (8 * (1 / (2 * c) + 1)) :=
    (tendsto_order.mp R.tendsto_paperRate_div_bandLog).2 _
      (by positivity)
  filter_upwards [R.U_grows.eventually_gt_atTop 0, hsmall, R.repLog_le]
    with n hU0 hsmall_n hR
  have hTsmall : paperRate X n < (1 / (8 * (1 / (2 * c) + 1))) * bandLog X n :=
    (div_lt_iff₀ hU0).mp hsmall_n
  have hRsmall : repLog c X n ≤ (1 / 8) * bandLog X n := by
    have h1 : (1 / (2 * c) + 1) * paperRate X n <
        (1 / (2 * c) + 1) * ((1 / (8 * (1 / (2 * c) + 1))) * bandLog X n) :=
      mul_lt_mul_of_pos_left hTsmall hKpos
    have h2 : (1 / (2 * c) + 1) * ((1 / (8 * (1 / (2 * c) + 1))) * bandLog X n) =
        (1 / 8) * bandLog X n := by
      have hA : (1 / (2 * c) + 1) ≠ 0 := hKpos.ne'
      have hcoef : (1 / (2 * c) + 1) * (1 / (8 * (1 / (2 * c) + 1))) = 1 / 8 := by
        field_simp [hA]
        have hden : (0 : ℝ) < 1 / c + 2 := by
          have hc := R.c_pos
          positivity
        exact div_self hden.ne'
      calc
        (1 / (2 * c) + 1) * ((1 / (8 * (1 / (2 * c) + 1))) * bandLog X n)
            = ((1 / (2 * c) + 1) * (1 / (8 * (1 / (2 * c) + 1)))) *
                bandLog X n := by ring
        _ = (1 / 8) * bandLog X n := by rw [hcoef]
    linarith
  have hsqrt : Real.sqrt (X n) = Real.exp (bandLog X n / 2) := by
    have hXpos : 0 < X n := lt_trans zero_lt_one (R.X_gt_one n)
    refine (Real.sqrt_eq_iff_eq_sq hXpos.le (Real.exp_pos _).le).mpr ?_
    calc
      X n = Real.exp (Real.log (X n)) := (Real.exp_log hXpos).symm
      _ = Real.exp (bandLog X n) := rfl
      _ = (Real.exp (bandLog X n / 2)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hprod : Real.sqrt (X n) * Real.exp (-(repLog c X n)) =
      Real.exp (bandLog X n / 2 - repLog c X n) := by
    calc
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) =
          Real.exp (bandLog X n / 2) * Real.exp (-(repLog c X n)) := by rw [hsqrt]
      _ = Real.exp (bandLog X n / 2 + (-(repLog c X n))) := by rw [← Real.exp_add]
      _ = Real.exp (bandLog X n / 2 - repLog c X n) := by
        congr 1
  rw [hprod]
  apply Real.exp_le_exp.mpr
  linarith

/-- **The paper-regime demand grows without bound.**  Since
`√X exp (-R) ≥ exp ((3/8) U)` and `U → ∞`, no bounded count can satisfy the
local density normalization in the growing regime. -/
theorem PaperRegime.demand_tendsto_atTop (R : PaperRegime p c X) :
    Tendsto (fun n => Real.sqrt (X n) * Real.exp (-(repLog c X n)))
      atTop atTop := by
  have hexp : Tendsto (fun n => Real.exp ((3 / 8) * bandLog X n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (R.U_grows.const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 8))
  exact tendsto_atTop_mono' atTop R.eventually_exp_three_eighths_le_demand hexp

/-! ## 4. Powers of two cannot meet the growing demand -/

/-- A `√p`-window contains at most `log₂ (p + √p) + 1` powers of two. -/
theorem powTwoNeighbours_card_le_log2 {p y : ℝ} (hp : 1 < p) :
    (powTwoNeighbours p y).card ≤ Nat.log 2 ⌊p + Real.sqrt p⌋₊ + 1 := by
  classical
  let N : ℕ := ⌊p + Real.sqrt p⌋₊
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hNpos : 0 < N := by
    dsimp only [N]
    apply Nat.le_floor
    have h1le : (1 : ℝ) ≤ p + Real.sqrt p := by
      have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
      linarith [le_of_lt hp]
    simpa using h1le
  have hsub : powTwoNeighbours p y ⊆
      (Finset.range (Nat.log 2 N + 1)).image (fun j : ℕ => (2 : ℕ) ^ j) := by
    intro m hm
    rw [powTwoNeighbours, Finset.mem_filter] at hm
    obtain ⟨hmS, j, rfl⟩ := hm
    rw [mem_sqrtSmoothNeighbours] at hmS
    have hm_lt : ((2 : ℕ) ^ j : ℝ) < p + Real.sqrt p := by
      have h := (abs_lt.mp hmS.1).2
      have h' : ((2 : ℕ) ^ j : ℝ) - p < Real.sqrt p := by
        simpa [Nat.cast_pow] using h
      linarith
    have hm_le : (2 : ℕ) ^ j ≤ N := by
      dsimp only [N]
      exact Nat.le_floor (by simpa using hm_lt.le)
    have hj : j ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hm_le
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩
  calc
    (powTwoNeighbours p y).card
        ≤ ((Finset.range (Nat.log 2 N + 1)).image (fun j : ℕ => (2 : ℕ) ^ j)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log 2 N + 1)).card := Finset.card_image_le
    _ = Nat.log 2 N + 1 := Finset.card_range _

/-- The real form of the powers-of-two bound. -/
theorem powTwoNeighbours_card_le_log {p y : ℝ} (hp : 1 < p) :
    ((powTwoNeighbours p y).card : ℝ) ≤
      Real.log (p + Real.sqrt p) / Real.log 2 + 1 := by
  classical
  let N : ℕ := ⌊p + Real.sqrt p⌋₊
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hNpos : 0 < N := by
    dsimp only [N]
    apply Nat.le_floor
    have h1le : (1 : ℝ) ≤ p + Real.sqrt p := by
      have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
      linarith [le_of_lt hp]
    simpa using h1le
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log (N : ℝ) ≤ Real.log (p + Real.sqrt p) := by
    apply Real.log_le_log (by positivity)
    dsimp only [N]
    exact Nat.floor_le (by positivity)
  have hjlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    have hpow : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hNpos.ne'
    have hcast : ((2 : ℕ) ^ Nat.log 2 N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpow
    have hlog := Real.log_le_log (by positivity) hcast
    simpa [Nat.cast_pow, Real.log_pow] using hlog
  have hlog_le : (Nat.log 2 N : ℝ) ≤ Real.log (p + Real.sqrt p) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    linarith
  have hcard := powTwoNeighbours_card_le_log2 (p := p) (y := y) hp
  have hcard' : ((powTwoNeighbours p y).card : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by
    exact_mod_cast hcard
  linarith

/-- Under a polynomial centre bound `p ≤ X^A` with `p ≥ 0`, the number of
powers of two in the window is at most linear in `U = log X`. -/
theorem powTwoNeighbours_card_le_linear {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (R : PaperRegime p c X) {A : ℝ} (hA : 0 < A)
    (hp_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ p n)
    (hp_bound : ∀ᶠ n : ℕ in atTop, p n ≤ X n ^ A) :
    ∀ᶠ n : ℕ in atTop,
      ((powTwoNeighbours (p n) (smoothCutoff c X n)).card : ℝ) ≤
        (A / Real.log 2 + 1) * bandLog X n + (Real.log 3 / Real.log 2 + 2) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [R.p_gt_one, hp_nonneg, hp_bound,
    R.U_grows.eventually_gt_atTop 0] with n hp1 hpnn hpb hU0
  have hX1 : (1 : ℝ) < X n := R.X_gt_one n
  have hXpos : 0 < X n := lt_trans zero_lt_one hX1
  have hXA1 : (1 : ℝ) ≤ X n ^ A := Real.one_le_rpow hX1.le hA.le
  have hsqrt_le : Real.sqrt (p n) ≤ p n + 1 := by
    have hs := Real.sq_sqrt hpnn
    nlinarith [Real.sqrt_nonneg (p n), sq_nonneg (p n)]
  have hsum_le : p n + Real.sqrt (p n) ≤ 3 * X n ^ A := by
    nlinarith
  have hlog_le : Real.log (p n + Real.sqrt (p n)) ≤
      Real.log 3 + A * bandLog X n := by
    have hpos : 0 < p n + Real.sqrt (p n) := by
      have := Real.sqrt_nonneg (p n)
      linarith
    calc
      Real.log (p n + Real.sqrt (p n)) ≤ Real.log (3 * X n ^ A) :=
        Real.log_le_log hpos hsum_le
      _ = Real.log 3 + Real.log (X n ^ A) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hXpos A))]
      _ = Real.log 3 + A * bandLog X n := by
        rw [Real.log_rpow hXpos A]
        rfl
  have hcard := powTwoNeighbours_card_le_log (p := p n)
    (y := smoothCutoff c X n) hp1
  have hdiv : Real.log (p n + Real.sqrt (p n)) / Real.log 2 ≤
      (Real.log 3 + A * bandLog X n) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog_le hlog2pos.le
  have hmain : ((powTwoNeighbours (p n) (smoothCutoff c X n)).card : ℝ) ≤
      (A / Real.log 2) * bandLog X n + (Real.log 3 / Real.log 2 + 1) := by
    have hrewrite : (Real.log 3 + A * bandLog X n) / Real.log 2 =
        (A / Real.log 2) * bandLog X n + Real.log 3 / Real.log 2 := by
      field_simp [hlog2pos.ne']
      ring
    linarith
  have hU1 : 0 ≤ bandLog X n := hU0.le
  nlinarith

/-- Linear functions are eventually dominated by `exp ((3/8) U)`. -/
theorem eventually_linear_lt_exp_three_eighths {U : ℕ → ℝ}
    (hU : Tendsto U atTop atTop) (C D : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * U n + D < Real.exp ((3 / 8) * U n) := by
  let x : ℕ → ℝ := fun n => (3 / 8) * U n
  have hx : Tendsto x atTop atTop :=
    hU.const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 8)
  have hexp : Tendsto (fun n => Real.exp (x n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hx
  have hratio : Tendsto (fun n => Real.exp (x n) / x n) atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).comp hx
    simpa [Function.comp_def, pow_one] using h
  have hinv : Tendsto (fun n => x n / Real.exp (x n)) atTop (nhds 0) := by
    have h := hratio.inv_tendsto_atTop
    refine h.congr' ?_
    filter_upwards with n
    change (Real.exp (x n) / x n)⁻¹ = x n / Real.exp (x n)
    rw [inv_div]
  have hdexp : Tendsto (fun n => D / Real.exp (x n)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hexp
  have hCexp : Tendsto (fun n => C * U n / Real.exp (x n)) atTop (nhds 0) := by
    have h : Tendsto (fun n => (C * (8 / 3)) * (x n / Real.exp (x n)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := C * (8 / 3))).mul hinv
    refine h.congr' ?_
    filter_upwards with n
    dsimp only [x]
    field_simp
  have hsum : Tendsto (fun n => (C * U n + D) / Real.exp (x n)) atTop (nhds 0) := by
    have h := hCexp.add hdexp
    simpa only [add_div, zero_add] using h
  have hlt : ∀ᶠ n : ℕ in atTop,
      (C * U n + D) / Real.exp (x n) < 1 :=
    (tendsto_order.mp hsum).2 1 zero_lt_one
  filter_upwards [hlt] with n hn
  rw [div_lt_one (Real.exp_pos _)] at hn
  simpa [x] using hn

/-- **Powers of two are insufficient in the growing paper regime.**  If the
centre is nonnegative and `p n ≤ X n ^ A`, then the powers-of-two count cannot
keep up with the unbounded demand `√X exp (-R)`. -/
theorem not_powTwoCountLower_of_paperRegime {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (R : PaperRegime p c X) {A : ℝ} (hA : 0 < A)
    (hp_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ p n)
    (hp_bound : ∀ᶠ n : ℕ in atTop, p n ≤ X n ^ A) :
    ¬ PowTwoCountLower p c X := by
  intro hcount
  have hcard := powTwoNeighbours_card_le_linear R hA hp_nonneg hp_bound
  have hlin := eventually_linear_lt_exp_three_eighths R.U_grows
    (A / Real.log 2 + 1) (Real.log 3 / Real.log 2 + 2)
  have hdem := R.eventually_exp_three_eighths_le_demand
  have hlt : ∀ᶠ n : ℕ in atTop,
      ((powTwoNeighbours (p n) (smoothCutoff c X n)).card : ℝ) <
        Real.sqrt (X n) * Real.exp (-(repLog c X n)) := by
    filter_upwards [hcard, hlin, hdem] with n hc hl hd
    exact lt_of_le_of_lt hc (lt_of_lt_of_le hl hd)
  obtain ⟨n, hnlt, hnle⟩ := (hlt.and hcount).exists
  exact (not_lt_of_ge hnle) hnlt

/-! ## 5. The density bundle with the short-interval input -/

/-- A paper-regime short-interval count gives `LocalSmoothCountLower`. -/
theorem localSmoothCountLower_of_paperRegime_shortInterval
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ} (R : PaperRegime p c X)
    (h : ShortIntervalSmoothCountLower p c X) : LocalSmoothCountLower p c X :=
  localSmoothCountLower_of_shortInterval R.p_gt_one h

/-- The explicit short-interval count is nonnegative. -/
theorem shortSmoothCount_nonneg (p y : ℝ) : 0 ≤ shortSmoothCount p y := by
  unfold shortSmoothCount
  exact Nat.cast_nonneg _

/-- The short-interval count supplied at a paper-regime centre is eventually
strictly positive: the demand `√X exp (-R)` is positive and the cardinality
dominates it.  This is the "never zero" form of the input. -/
theorem shortSmoothCount_pos_of_shortInterval
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ} (R : PaperRegime p c X)
    (h : ShortIntervalSmoothCountLower p c X) :
    ∀ᶠ n : ℕ in atTop,
      0 < shortSmoothCount (p n) (smoothCutoff c X n) := by
  have hlocal := localSmoothCountLower_of_paperRegime_shortInterval R h
  have hpos := smoothCountNear_pos_of_localCount
    (Eventually.of_forall fun n => lt_trans zero_lt_one (R.X_gt_one n)) hlocal
  filter_upwards [R.p_gt_one, hpos] with n hp1 hn
  rwa [shortSmoothCount_eq_smoothCountNear hp1]

end Cogentic.RandomizedL21_2PaperLocal

namespace Cogentic.RandomizedL21_2Density

open Filter Real
open Cogentic.Randomized
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2PaperLocal

/-- **The L21.2 density bundle with the local count supplied by the explicit
short-interval count.**  Every other field is inherited from `D`; only the
`localCount` slot changes. -/
def L21_2DensityInputs.ofShortInterval (D : L21_2DensityInputs)
    (hp : ∀ᶠ n : ℕ in atTop, 1 < D.p n)
    (h : ShortIntervalSmoothCountLower D.p D.c D.X) :
    L21_2DensityInputs :=
  { D with localCount := localSmoothCountLower_of_shortInterval hp h }

/-- The Perron bundle obtained from the short-interval count. -/
def L21_2DensityInputs.toPerronInputsOfShortInterval (D : L21_2DensityInputs)
    (hp : ∀ᶠ n : ℕ in atTop, 1 < D.p n)
    (h : ShortIntervalSmoothCountLower D.p D.c D.X) :
    L21_2PerronInputs :=
  (D.ofShortInterval hp h).toPerronInputs

/-- The `RatedLeaf` obtained from the short-interval count. -/
def L21_2DensityInputs.toRatedLeafOfShortInterval (D : L21_2DensityInputs)
    (hp : ∀ᶠ n : ℕ in atTop, 1 < D.p n)
    (h : ShortIntervalSmoothCountLower D.p D.c D.X) :
    RatedLeaf :=
  (D.toPerronInputsOfShortInterval hp h).toRatedLeaf

/-- The `D^{-B}` `SubexpLeaf` obtained from the short-interval count. -/
def L21_2DensityInputs.toSubexpLeafOfShortInterval (D : L21_2DensityInputs)
    (hp : ∀ᶠ n : ℕ in atTop, 1 < D.p n)
    (h : ShortIntervalSmoothCountLower D.p D.c D.X) :
    SubexpLeaf :=
  (D.toPerronInputsOfShortInterval hp h).toSubexpLeaf

/-- **Paper assumptions from the explicit short-interval count.**  The remaining
eleven leaves plus the explicit L21.2 density data with `localCount` replaced by
`ShortIntervalSmoothCountLower` give the full paper assumptions. -/
def L21_2DensityInputs.paperAssumptions_of_shortInterval (D : L21_2DensityInputs)
    (hp : ∀ᶠ n : ℕ in atTop, 1 < D.p n)
    (h : ShortIntervalSmoothCountLower D.p D.c D.X)
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (A : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2DensityInputs.paperAssumptions_of_density (D.ofShortInterval hp h) A

end Cogentic.RandomizedL21_2Density

namespace Cogentic.RandomizedL21_2PaperLocal

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2PaperLocal.mem_shortSmoothInterval
#print axioms Cogentic.RandomizedL21_2PaperLocal.shortSmoothInterval_eq_sqrtSmoothNeighbours
#print axioms Cogentic.RandomizedL21_2PaperLocal.shortSmoothCount_eq_smoothCountNear
#print axioms Cogentic.RandomizedL21_2PaperLocal.localSmoothCountLower_iff_shortInterval
#print axioms Cogentic.RandomizedL21_2PaperLocal.shortIntervalSmoothCountLower_of_setCount
#print axioms Cogentic.RandomizedL21_2PaperLocal.setCount_of_shortIntervalSmoothCountLower
#print axioms Cogentic.RandomizedL21_2PaperLocal.PaperRegime.ofReducedInputs
#print axioms Cogentic.RandomizedL21_2PaperLocal.PaperRegime.repLog_le
#print axioms Cogentic.RandomizedL21_2PaperLocal.PaperRegime.eventually_exp_three_eighths_le_demand
#print axioms Cogentic.RandomizedL21_2PaperLocal.PaperRegime.demand_tendsto_atTop
#print axioms Cogentic.RandomizedL21_2PaperLocal.powTwoNeighbours_card_le_log
#print axioms Cogentic.RandomizedL21_2PaperLocal.powTwoNeighbours_card_le_linear
#print axioms Cogentic.RandomizedL21_2PaperLocal.eventually_linear_lt_exp_three_eighths
#print axioms Cogentic.RandomizedL21_2PaperLocal.not_powTwoCountLower_of_paperRegime
#print axioms Cogentic.RandomizedL21_2PaperLocal.localSmoothCountLower_of_paperRegime_shortInterval
#print axioms Cogentic.RandomizedL21_2PaperLocal.shortSmoothCount_nonneg
#print axioms Cogentic.RandomizedL21_2PaperLocal.shortSmoothCount_pos_of_shortInterval
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.ofShortInterval
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toPerronInputsOfShortInterval
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toRatedLeafOfShortInterval
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toSubexpLeafOfShortInterval
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.paperAssumptions_of_shortInterval

end Cogentic.RandomizedL21_2PaperLocal
