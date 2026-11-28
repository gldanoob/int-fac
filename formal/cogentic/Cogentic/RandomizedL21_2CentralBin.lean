import Cogentic.RandomizedL21_2LocalFromGRH

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# L21.2: the *central* prime-bin construction at the centre `p`

`Cogentic.RandomizedL21_2LocalFromGRH` proves that the L30 global bin strip is
centred at `p ^ 2 / 4`, so its floor `P ^ m = p ^ 2 / 4` already lies above the
L21.2 window `p ± √p`.  The present file constructs the missing **central**
version: the geometric bins have

```
P ^ m = p        (not p ^ 2 / 4)
```

and width chosen so that the whole multiplicative strip lies in the literal
open short interval `(p - √p, p + √p)`.  All the existing `centeredBinProducts`
machinery (`centeredBinEndpoint`, `centeredBinFloor`, disjointness, strip
membership, smoothness) is reused verbatim; only the centre changes.

The file is organised as follows.

## 1. The central schedule

`centralU = log p / ((1 + ε) t_p)` is half of the L30 ratio
`paperDensityU = 2 log p / ((1 + ε) t_p)`.  The number of prime factors is

```
centralM = ⌈centralU * (1 + 1 / log centralU)⌉₊ ,
centralP = p ^ (1 / centralM) ,
```

so that `centralP ^ centralM = p` (`centralP_pow`).  The width is

```
centralWindowDelta = (1/4) / (centralM * √p),
```

hence `centralM * centralWindowDelta = 1/(4√p)` and
`p * exp (centralM * centralWindowDelta) < p + √p`
(`central_p_mul_exp_lt_window`).

## 2. The literal short interval

`centralBinProducts_subset_shortSmoothInterval` proves that every product of
the central bins is a genuine member of `shortSmoothInterval p y` whenever the
strip is inside the window and every bin floor is at most `y`.  The scalar
cardinality form is `card_centralBinProducts_le_shortSmoothCount`.

## 3. The insertion count at the central centre

`CentralPrimeSupply` is exactly the per-bin prime-population guard of the
character-sum/insertion argument of `RandomizedL30SmoothDensity`, specialised
to the central centre `centralDensityP = p ^ (1/paperDensityM)`.  It is the
only analytic input that the L30 argument does not prove from
`DirichletLZerosOnLine`; the GRH prime supply is absorbed into it.

`eventually_centralDensity_binCount_of_supply` reruns the L30 insertion
argument with this centre and concludes the positive central-scale count

```
p n * exp (-(t_p n)) ≤ #(centeredBinProducts centralDensityP δ J m a) .
```

The count is strictly positive (`centralDensity_binCount_pos`).

The insertion schedule necessarily uses the L30 bin width
`δ = paperDensityDelta`, for which `m δ ≈ log 2`; this is a *wide* strip
`[p, 2p]`, not the `√p`-window.  The narrow window width is `centralWindowDelta`
of §1, for which `m δ = 1/(4√p)`.  Section 4 shows that the narrow width can
never satisfy the L30 guard, so the wide insertion count is not a short-interval
count and the short-interval strip has no insertion count.

## 4. The precise residual, and why it cannot be met

`centralBinGuard_false_of_window` is the key obstruction: if `P ^ m = p` with
`m ≥ 2` and the strip is inside the `√p`-window (`m δ < log (1 + 1/√p)`),
then for **every** `K ≥ 0` the supply guard

```
K (1 + log (3y))² √y + 1 ≤ (1/2) δ (P exp (-(δ J)))
```

is *false*.  Indeed `m δ < 1/√p` forces `δ P < 1/m ≤ 1/2`, so the right-hand
side is `< 1` while the left-hand side is `≥ 1`.  Consequently the central
window strip is narrower than the GRH prime-supply error in every bin: the L30
character-sum/insertion route cannot produce the central short-interval count.
The remaining estimate is therefore not a routine GRH consequence but a
genuinely stronger central prime supply.  We state this as
`not_eventually_centralWindowSupply`: no positive central prime supply exists
for a window strip.

No `sorry`, `admit`, `axiom` or `native_decide` is used.  Every count below is
a genuine `Finset.card`; nothing is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2CentralBin

open Filter Real
open Cogentic.Randomized
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2ShortIntervalTransfer
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Interval

/-! ## 1. The central schedule -/

/-- The central logarithmic ratio `u = log p / ((1 + ε) t_p)`, i.e. half of the
L30 ratio `paperDensityU`.  Its `m`-th power scale is `p`, not `p²/4`. -/
def centralU (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  Real.log (p n) / ((1 + ε) * paperT p n)

/-- The number of prime factors at the central scale. -/
def centralM (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈centralU p ε n * (1 + 1 / Real.log (centralU p ε n))⌉₊

/-- The geometric bin centre `P = p ^ (1/m)`, so `P ^ m = p`. -/
def centralP (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (p n) ^ (1 / (centralM p ε n : ℝ))

/-- The window-scale bin width `δ = (1/4) / (m √p)`.  It makes the full strip
width `m δ = 1/(4√p)`, comfortably inside the `√p`-window. -/
def centralWindowDelta (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (1 / 4) / ((centralM p ε n : ℝ) * Real.sqrt (p n))

/-- `centralU` is exactly half of the L30 ratio. -/
theorem centralU_eq_half_paperDensityU (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    centralU p ε n = paperDensityU p ε n / 2 := by
  unfold centralU paperDensityU
  ring

/-- `centralU` tends to infinity at the paper scale. -/
theorem tendsto_centralU_of_growth {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => centralU p ε n) atTop atTop := by
  have hbase := tendsto_paperDensityU_of_growth h hε
  have hhalf : Tendsto (fun n => (1 / 2 : ℝ) * paperDensityU p ε n) atTop atTop :=
    hbase.const_mul_atTop (by norm_num)
  refine hhalf.congr fun n => ?_
  rw [centralU_eq_half_paperDensityU]
  ring

/-- Eventually `centralU > 1`. -/
theorem eventually_centralU_gt_one {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 < centralU p ε n :=
  (tendsto_centralU_of_growth h hε).eventually_gt_atTop 1

/-- The number of central prime factors is positive once `centralU > 1`. -/
theorem centralM_pos {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hu : 1 < centralU p ε n) : 0 < centralM p ε n := by
  have hu0 : 0 < centralU p ε n := zero_lt_one.trans hu
  have hlog : 0 < Real.log (centralU p ε n) := Real.log_pos hu
  unfold centralM
  exact Nat.ceil_pos.mpr (mul_pos hu0 (by positivity))

/-- Eventually the central number of factors is positive. -/
theorem eventually_centralM_pos {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 < centralM p ε n :=
  (eventually_centralU_gt_one h hε).mono fun _ hu => centralM_pos hu

/-- Eventually `centralM ≥ 2`; this is the regime in which the bin width is
strictly smaller than `√p`. -/
theorem eventually_centralM_ge_two {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ centralM p ε n := by
  have htend := tendsto_centralU_of_growth h hε
  filter_upwards [htend.eventually_ge_atTop 2,
    htend.eventually_ge_atTop (Real.exp 1)] with n hu2 hlog1
  have hu1 : 1 < centralU p ε n := by linarith
  have hlogpos : 0 < Real.log (centralU p ε n) := Real.log_pos hu1
  have hlogge1 : 1 ≤ Real.log (centralU p ε n) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlog1
    rwa [Real.log_exp] at h
  have hx : (2 : ℝ) ≤ centralU p ε n *
      (1 + 1 / Real.log (centralU p ε n)) := by
    have hfac : (1 : ℝ) ≤ 1 + 1 / Real.log (centralU p ε n) := by
      have : 0 ≤ 1 / Real.log (centralU p ε n) := by positivity
      linarith
    nlinarith
  have hceil : (2 : ℝ) ≤ (centralM p ε n : ℝ) := by
    unfold centralM
    exact hx.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/-- The central centre is positive. -/
theorem centralP_pos {p : ℕ → ℝ} {ε : ℝ} {n : ℕ} (hp : 0 < p n) :
    0 < centralP p ε n := by
  unfold centralP
  exact Real.rpow_pos_of_pos hp _

/-- **The central centre really is `p`:** `P ^ m = p`, not `p²/4`. -/
theorem centralP_pow {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) (hm : 0 < centralM p ε n) :
    centralP p ε n ^ centralM p ε n = p n := by
  have hx : (0 : ℝ) ≤ p n := hp.le
  have hmne : ((centralM p ε n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  unfold centralP
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  have hcancel : (1 / (centralM p ε n : ℝ)) * (centralM p ε n : ℝ) = 1 := by
    field_simp
  rw [hcancel, Real.rpow_one]

/-- The window-scale width is nonnegative. -/
theorem centralWindowDelta_nonneg {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) : 0 ≤ centralWindowDelta p ε n := by
  unfold centralWindowDelta
  positivity

/-- The defining product `m δ = 1/(4 √p)` of the window-scale width. -/
theorem centralM_mul_centralWindowDelta {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) (hm : 0 < centralM p ε n) :
    (centralM p ε n : ℝ) * centralWindowDelta p ε n =
      (1 / 4) / Real.sqrt (p n) := by
  have hmne : ((centralM p ε n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hsne : Real.sqrt (p n) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  unfold centralWindowDelta
  field_simp

/-- The additive width of the central strip is `√p / 4`, hence `≲ √p`. -/
theorem centralWindow_additive_width {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) (hm : 0 < centralM p ε n) :
    p n * ((centralM p ε n : ℝ) * centralWindowDelta p ε n) =
      Real.sqrt (p n) / 4 := by
  have hs0 : 0 < Real.sqrt (p n) := Real.sqrt_pos.mpr hp
  rw [centralM_mul_centralWindowDelta hp hm]
  have hsq : Real.sqrt (p n) * Real.sqrt (p n) = p n :=
    Real.mul_self_sqrt hp.le
  field_simp [hs0.ne']
  nlinarith [hsq]

/-- `log (1 + x) ≥ x/2` for `0 < x ≤ 1`. -/
theorem log_one_add_ge_half {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have hx1pos : (0 : ℝ) < 1 + x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos one_pos hx1pos)
  have hlog_eq : Real.log (1 / (1 + x)) = -Real.log (1 + x) := by
    rw [Real.log_div one_ne_zero hx1pos.ne', Real.log_one]
    ring
  have hsub_eq : 1 / (1 + x) - 1 = -(x / (1 + x)) := by
    field_simp
    ring
  rw [hlog_eq, hsub_eq] at hlog
  have hfrac : x / (1 + x) ≤ Real.log (1 + x) := by linarith
  have hhalf : x / 2 ≤ x / (1 + x) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hx1pos]
    nlinarith [hx0, hx1]
  exact hhalf.trans hfrac

/-- The explicit width bound `1/(4√p) < log (1 + 1/√p)` for `p > 1`. -/
theorem quarter_div_sqrt_lt_log_one_add_inv_sqrt {p : ℝ} (hp : 1 < p) :
    (1 / 4) / Real.sqrt p < Real.log (1 + 1 / Real.sqrt p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hs1 : 1 ≤ Real.sqrt p := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hp.le
  have hx0 : 0 < 1 / Real.sqrt p := by positivity
  have hx1 : 1 / Real.sqrt p ≤ 1 := by
    rw [div_le_one hs0]
    exact hs1
  have hhalf := log_one_add_ge_half hx0 hx1
  have hhalf' : (1 / 2) * (1 / Real.sqrt p) ≤
      Real.log (1 + 1 / Real.sqrt p) := by
    have heq : (1 / 2) * (1 / Real.sqrt p) = (1 / Real.sqrt p) / 2 := by ring
    rw [heq]
    exact hhalf
  have hquarter_lt : (1 / 4) * (1 / Real.sqrt p) <
      (1 / 2) * (1 / Real.sqrt p) := by
    nlinarith [hx0]
  have heq : (1 / 4) / Real.sqrt p = (1 / 4) * (1 / Real.sqrt p) := by ring
  rw [heq]
  exact hquarter_lt.trans_le hhalf'

/-- The central strip upper end is strictly inside the `√p`-window. -/
theorem central_p_mul_exp_lt_window {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 1 < p n) (hm : 0 < centralM p ε n) :
    p n * Real.exp ((centralM p ε n : ℝ) * centralWindowDelta p ε n) <
      p n + Real.sqrt (p n) := by
  have hp0 : 0 < p n := lt_trans zero_lt_one hp
  have hs0 : 0 < Real.sqrt (p n) := Real.sqrt_pos.mpr hp0
  have hquarter : (1 / 4) / Real.sqrt (p n) <
      Real.log (1 + 1 / Real.sqrt (p n)) :=
    quarter_div_sqrt_lt_log_one_add_inv_sqrt hp
  rw [centralM_mul_centralWindowDelta hp0 hm]
  have hexp : Real.exp ((1 / 4) / Real.sqrt (p n)) <
      1 + 1 / Real.sqrt (p n) := by
    calc
      Real.exp ((1 / 4) / Real.sqrt (p n))
          < Real.exp (Real.log (1 + 1 / Real.sqrt (p n))) :=
            Real.exp_lt_exp.mpr hquarter
      _ = 1 + 1 / Real.sqrt (p n) :=
            Real.exp_log (by positivity)
  have hmul := mul_lt_mul_of_pos_left hexp hp0
  have htarget : p n * (1 + 1 / Real.sqrt (p n)) = p n + Real.sqrt (p n) := by
    have hsq : Real.sqrt (p n) * Real.sqrt (p n) = p n :=
      Real.mul_self_sqrt hp0.le
    field_simp [hs0.ne']
    nlinarith [hsq]
  calc
    p n * Real.exp ((1 / 4) / Real.sqrt (p n))
        < p n * (1 + 1 / Real.sqrt (p n)) := hmul
    _ = p n + Real.sqrt (p n) := htarget

/-- The window-scale strip lies strictly above the lower endpoint. -/
theorem central_p_sub_sqrt_lt_p {p : ℝ} (hp : 0 < p) :
    p - Real.sqrt p < p := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  linarith

/-! ## 2. The literal short interval -/

/-- **Central strip containment.**  If `P ^ m = p` and the central strip upper
end `p * exp (m δ)` is still below `p + √p`, then every product of the central
bins is a member of the literal smooth short interval, provided each bin floor
is at most the smoothness cutoff `y`. -/
theorem centralBinProducts_subset_shortSmoothInterval
    {P δ y : ℝ} {J m a : ℕ} {p : ℝ}
    (hp : 1 < p) (hP : 0 ≤ P) (hm : 0 < m)
    (hPpow : P ^ m = p)
    (hwin : p * Real.exp ((m : ℝ) * δ) < p + Real.sqrt p)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a m (j + 1) : ℝ) ≤ y) :
    centeredBinProducts P δ J m a ⊆ shortSmoothInterval p y := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hlo : p - Real.sqrt p < P ^ m := by
    rw [hPpow]
    exact central_p_sub_sqrt_lt_p hp0
  have hhi : P ^ m * Real.exp ((m : ℝ) * δ) < p + Real.sqrt p := by
    rw [hPpow]
    exact hwin
  exact centeredBinProducts_subset_shortSmoothInterval hp hP hm hlo hhi hfloor

/-- The cardinality form of central strip containment. -/
theorem card_centralBinProducts_le_shortSmoothCount
    {P δ y : ℝ} {J m a : ℕ} {p : ℝ}
    (hp : 1 < p) (hP : 0 ≤ P) (hm : 0 < m)
    (hPpow : P ^ m = p)
    (hwin : p * Real.exp ((m : ℝ) * δ) < p + Real.sqrt p)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a m (j + 1) : ℝ) ≤ y) :
    ((centeredBinProducts P δ J m a).card : ℝ) ≤ shortSmoothCount p y := by
  have hsub := centralBinProducts_subset_shortSmoothInterval hp hP hm hPpow hwin hfloor
  unfold shortSmoothCount
  exact_mod_cast Finset.card_le_card hsub

/-! ## 3. The insertion count at the central centre -/

/-- The central-scale insertion centre `p ^ (1/m)` with the L30 value of `m`.
It differs from `paperDensityP` only in the centre: `P ^ m = p` instead of
`p²/4`. -/
def centralDensityP (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (p n) ^ (1 / (paperDensityM p ε n : ℝ))

/-- The per-bin prime-supply guard of the insertion argument, written for an
arbitrary centre `P`, bin count `J`, number of factors `m` and cutoff `y`. -/
def centralBinGuard (K P δ y : ℝ) (J _m : ℕ) : Prop :=
  K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y + 1 ≤
    (1 - (1 / 2)) * δ * (P * Real.exp (-(δ * (J : ℝ))))

/-- **The precise residual at the central centre.**  This is exactly the
prime-population guard of the L30 character-sum/insertion argument, with the
centre changed from `p²/4` to `p`.  It is the only analytic estimate that the
GRH input does not supply. -/
def CentralPrimeSupply (p : ℕ → ℝ) (ε : ℝ) (K : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    centralBinGuard K (centralDensityP p ε n) (paperDensityDelta p ε n)
      (paperDensityY p ε n) (paperDensityJ p ε n) (paperDensityM p ε n)

/-- The central insertion centre is positive. -/
theorem centralDensityP_pos {p : ℕ → ℝ} {ε : ℝ} {n : ℕ} (hp : 0 < p n) :
    0 < centralDensityP p ε n := by
  unfold centralDensityP
  exact Real.rpow_pos_of_pos hp _

/-- **The central insertion centre has `P ^ m = p`.** -/
theorem centralDensityP_pow {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) (hm : 0 < paperDensityM p ε n) :
    centralDensityP p ε n ^ paperDensityM p ε n = p n := by
  have hx : (0 : ℝ) ≤ p n := hp.le
  have hmne : ((paperDensityM p ε n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  unfold centralDensityP
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  have hcancel : (1 / (paperDensityM p ε n : ℝ)) * (paperDensityM p ε n : ℝ) = 1 := by
    field_simp
  rw [hcancel, Real.rpow_one]

/-- The logarithm of the central insertion centre. -/
theorem centralDensityP_logP {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) :
    Real.log (centralDensityP p ε n) =
      Real.log (p n) / (paperDensityM p ε n : ℝ) := by
  unfold centralDensityP
  rw [Real.log_rpow hp]
  ring

/-- **The lower half of the insertion guard is automatic at the central
centre.**  The strip floor `P exp (-(δ J))` eventually exceeds `2`. -/
theorem eventually_centralDensity_lower {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ centralDensityP p ε n *
        Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) := by
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have ht_tend := tendsto_paperT_of_growth h
  filter_upwards [h.eventually_sixteen,
    eventually_paperDensityU_gt_one_of_tendsto hu_tend,
    eventually_paperDensityM_le_two_u_of_growth h hε,
    eventually_paperT_pos_of_growth h,
    hu_tend.eventually_ge_atTop (Real.exp 4),
    ht_tend.eventually_ge_atTop (16 * Real.log 2)] with n hp16 hu1 hm2 ht hubig htbig
  have hp1 : (1 : ℝ) < p n := by linarith
  have hp0 : 0 < p n := by linarith
  have hmposNat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hJposNat : 0 < paperDensityJ p ε n := paperDensityJ_pos hmposNat
  have hmpos : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hmposNat
  have hlogu_pos : 0 < Real.log (paperDensityU p ε n) := Real.log_pos hu1
  have hlogu_ge4 : 4 ≤ Real.log (paperDensityU p ε n) := by
    have hlog := Real.log_le_log (Real.exp_pos 4) hubig
    rwa [Real.log_exp] at hlog
  have hα : 0 < 1 + ε := by positivity
  have htwoL : 2 * Real.log (p n) =
      (1 + ε) * paperT p n * paperDensityU p ε n := by
    unfold paperDensityU
    field_simp
  have hlogP : Real.log (centralDensityP p ε n) =
      Real.log (p n) / (paperDensityM p ε n : ℝ) :=
    centralDensityP_logP (p := p) (ε := ε) hp0
  have hlogP_ge : (1 + ε) * paperT p n / 4 ≤
      Real.log (centralDensityP p ε n) := by
    rw [hlogP, le_div_iff₀ hmpos]
    have hmul := mul_le_mul_of_nonneg_left hm2
      (show 0 ≤ (1 + ε) * paperT p n / 4 by positivity)
    have heq : ((1 + ε) * paperT p n / 4) *
        (2 * paperDensityU p ε n) = Real.log (p n) := by
      calc ((1 + ε) * paperT p n / 4) * (2 * paperDensityU p ε n)
          = ((1 + ε) * paperT p n * paperDensityU p ε n) / 2 := by ring
        _ = (2 * Real.log (p n)) / 2 := by rw [htwoL]
        _ = Real.log (p n) := by ring
    linarith [hmul, heq]
  have hdeltaJ := paperDensityDelta_mul_J hJposNat hlogu_pos.ne'
  have hdeltaJ_le : paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) ≤
      (1 + ε) * paperT p n / 8 := by
    rw [hdeltaJ, div_le_iff₀ hlogu_pos]
    calc
      (1 / 2) * ((1 + ε) * paperT p n)
          = ((1 + ε) * paperT p n / 8) * 4 := by ring
      _ ≤ ((1 + ε) * paperT p n / 8) * Real.log (paperDensityU p ε n) :=
          mul_le_mul_of_nonneg_left hlogu_ge4 (by positivity)
      _ = (1 + ε) * paperT p n / 8 * Real.log (paperDensityU p ε n) := by ring
  have hαt_ge : 16 * Real.log 2 ≤ (1 + ε) * paperT p n := by
    have htle : paperT p n ≤ (1 + ε) * paperT p n := by nlinarith [hε.le, ht.le]
    linarith
  have hlogprod : Real.log (centralDensityP p ε n *
        Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)))) =
      Real.log (centralDensityP p ε n) -
        paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) := by
    rw [Real.log_mul (centralDensityP_pos hp0).ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  have hge : Real.log 2 ≤ Real.log (centralDensityP p ε n) -
      paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) := by
    nlinarith [hlogP_ge, hdeltaJ_le, hαt_ge]
  calc
    (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (Real.log (centralDensityP p ε n) -
          paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) :=
        Real.exp_le_exp.mpr hge
    _ = centralDensityP p ε n *
          Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) := by
        rw [← hlogprod,
          Real.exp_log (mul_pos (centralDensityP_pos hp0) (Real.exp_pos _))]

/-- **The upper half of the insertion guard is automatic at the central
centre.**  The strip ceiling `P exp (δ J)` is below the L30 cutoff `y`. -/
theorem eventually_centralDensity_upper {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      centralDensityP p ε n *
        Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) ≤
          paperDensityY p ε n := by
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  filter_upwards [h.eventually_sixteen,
    eventually_paperDensityU_gt_one_of_tendsto hu_tend,
    eventually_paperT_pos_of_growth h,
    hu_tend.eventually_ge_atTop (Real.exp 2)] with n hp16 hu1 ht hubig
  have hp1 : (1 : ℝ) < p n := by linarith
  have hp0 : 0 < p n := by linarith
  have hmposNat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hJposNat : 0 < paperDensityJ p ε n := paperDensityJ_pos hmposNat
  have hmpos : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hmposNat
  have hlogu_pos : 0 < Real.log (paperDensityU p ε n) := Real.log_pos hu1
  have hlogu_ge2 : 2 ≤ Real.log (paperDensityU p ε n) := by
    have hlog := Real.log_le_log (Real.exp_pos 2) hubig
    rwa [Real.log_exp] at hlog
  have hα : 0 < 1 + ε := by positivity
  have htwoL : 2 * Real.log (p n) =
      (1 + ε) * paperT p n * paperDensityU p ε n := by
    unfold paperDensityU
    field_simp
  have hlogP : Real.log (centralDensityP p ε n) =
      Real.log (p n) / (paperDensityM p ε n : ℝ) :=
    centralDensityP_logP (p := p) (ε := ε) hp0
  have hMu : paperDensityU p ε n ≤ (paperDensityM p ε n : ℝ) :=
    paperDensityU_le_paperDensityM p ε n (zero_lt_one.trans hu1) hlogu_pos
  have hlogP_le : Real.log (centralDensityP p ε n) ≤
      (1 + ε) * paperT p n / 2 := by
    rw [hlogP, div_le_iff₀ hmpos]
    have hmul := mul_le_mul_of_nonneg_left hMu
      (show 0 ≤ (1 + ε) * paperT p n / 2 by positivity)
    have heq : ((1 + ε) * paperT p n / 2) * paperDensityU p ε n =
        Real.log (p n) := by
      calc ((1 + ε) * paperT p n / 2) * paperDensityU p ε n
          = ((1 + ε) * paperT p n * paperDensityU p ε n) / 2 := by ring
        _ = (2 * Real.log (p n)) / 2 := by rw [htwoL]
        _ = Real.log (p n) := by ring
    linarith [hmul, heq]
  have hdeltaJ := paperDensityDelta_mul_J hJposNat hlogu_pos.ne'
  have hdeltaJ_le : paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) ≤
      (1 + ε) * paperT p n / 4 := by
    rw [hdeltaJ, div_le_iff₀ hlogu_pos]
    calc
      (1 / 2) * ((1 + ε) * paperT p n)
          = ((1 + ε) * paperT p n / 4) * 2 := by ring
      _ ≤ ((1 + ε) * paperT p n / 4) * Real.log (paperDensityU p ε n) :=
          mul_le_mul_of_nonneg_left hlogu_ge2 (by positivity)
      _ = (1 + ε) * paperT p n / 4 * Real.log (paperDensityU p ε n) := by ring
  have hsum : Real.log (centralDensityP p ε n) +
      paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) ≤
        (1 + ε) * paperT p n := by
    nlinarith [hlogP_le, hdeltaJ_le, hα, ht]
  have hlogprod : Real.log (centralDensityP p ε n *
        Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) =
      Real.log (centralDensityP p ε n) +
        paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) := by
    rw [Real.log_mul (centralDensityP_pos hp0).ne' (Real.exp_pos _).ne',
      Real.log_exp]
  calc
    centralDensityP p ε n *
        Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))
        = Real.exp (Real.log (centralDensityP p ε n) +
            paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) := by
          rw [← hlogprod,
            Real.exp_log (mul_pos (centralDensityP_pos hp0) (Real.exp_pos _))]
    _ ≤ Real.exp ((1 + ε) * paperT p n) := Real.exp_le_exp.mpr hsum
    _ = paperDensityY p ε n := rfl

/-- **The central-scale prime-bin count from `DirichletLZerosOnLine`.**

This is the L30 character-sum/insertion argument rerun with the centre `p`
instead of `p²/4`.  The only extra input is `CentralPrimeSupply`: the per-bin
prime-population guard at the central centre.  The conclusion is the positive
central-scale lower bound `p * exp (-t_p) ≤ #bins`. -/
theorem eventually_centralDensity_binCount_of_supply
    (line : DirichletLZerosOnLine)
    (p : ℕ → ℝ) (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ (CentralPrimeSupply p ε K →
      ∀ᶠ n : ℕ in atTop,
        ∃ a ∈ Finset.range (paperDensityM p ε n * (paperDensityJ p ε n - 1) + 1),
          p n * Real.exp (-(paperT p n)) ≤
            ((centeredBinProducts (centralDensityP p ε n)
              (paperDensityDelta p ε n) (paperDensityJ p ε n)
              (paperDensityM p ε n) a).card : ℝ)) := by
  obtain ⟨K, hK, hmain⟩ := eventually_centeredBinProducts_density_from_critical_line line
  refine ⟨K, hK, fun hsupply => ?_⟩
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have hPpos : ∀ᶠ n : ℕ in atTop, 0 < centralDensityP p ε n := by
    filter_upwards [h.eventually_sixteen] with n hp
    exact centralDensityP_pos (by linarith)
  have hδnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ paperDensityDelta p ε n := by
    filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
      eventually_paperDensityU_gt_one_of_tendsto hu_tend] with n hp ht hu1
    have hmpos := paperDensityM_pos hu1
    have hJpos := paperDensityJ_pos hmpos
    exact (paperDensityDelta_pos hε ht hJpos (Real.log_pos hu1)).le
  have hy1 : ∀ᶠ n : ℕ in atTop, 1 < paperDensityY p ε n := by
    filter_upwards [eventually_paperT_pos_of_growth h] with n ht
    dsimp [paperDensityY]
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have hJδ : ∀ᶠ n : ℕ in atTop,
      (1 / 2) * Real.log (paperDensityY p ε n) /
          Real.log (paperDensityU p ε n) ≤
        (paperDensityJ p ε n : ℝ) * paperDensityDelta p ε n := by
    filter_upwards [eventually_paperDensityU_gt_one_of_tendsto hu_tend] with n hu1
    have hmpos := paperDensityM_pos hu1
    have hJpos := paperDensityJ_pos hmpos
    have hlogu : Real.log (paperDensityU p ε n) ≠ 0 := (Real.log_pos hu1).ne'
    have hy : Real.log (paperDensityY p ε n) = (1 + ε) * paperT p n := by
      dsimp [paperDensityY]
      rw [Real.log_exp]
    rw [hy]
    rw [mul_comm (paperDensityJ p ε n : ℝ) (paperDensityDelta p ε n)]
    rw [paperDensityDelta_mul_J hJpos hlogu]
  have hJm : ∀ᶠ n : ℕ in atTop,
      ⌈paperDensityU p ε n * (1 + 1 / Real.log (paperDensityU p ε n))⌉₊ ≤
        paperDensityJ p ε n := by
    filter_upwards with n
    exact Nat.le_trans (Nat.le_succ _) (paperDensityJ_ge_m p ε n)
  have hlog := isLittleO_log_m_sq_J_of_growth h hε
  have hlo := eventually_centralDensity_lower h hε
  have hhi := eventually_centralDensity_upper h hε
  have hconc := hmain (u := paperDensityU p ε) (P := centralDensityP p ε)
    (y := paperDensityY p ε) (δ := paperDensityDelta p ε)
    (J := paperDensityJ p ε) (c := (1 / 2 : ℝ)) (cH := (1 / 2 : ℝ)) (ε := ε)
    hu_tend (by norm_num) (by norm_num) hε hPpos hδnonneg hy1 hJδ hJm
    (by simpa only [paperDensityM] using hlog) hlo hhi hsupply
  filter_upwards [hconc, eventually_paperDensityU_mul_log_le_paperT h hε,
    h.eventually_sixteen, eventually_paperDensityU_gt_one_of_tendsto hu_tend] with
      n hc hpowle hp16 hu1
  dsimp only at hc
  obtain ⟨a, ha, hdens, _⟩ := hc
  refine ⟨a, ha, ?_⟩
  have hp0 : 0 < p n := by linarith
  have hmposNat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hPpow := centralDensityP_pow (p := p) (ε := ε) hp0 hmposNat
  have hPpow' : centralDensityP p ε n ^
      ⌈paperDensityU p ε n * (1 + 1 / Real.log (paperDensityU p ε n))⌉₊ = p n := by
    simpa only [paperDensityM] using hPpow
  rw [hPpow'] at hdens
  rw [le_div_iff₀ hp0] at hdens
  rw [mul_comm] at hdens
  have hexp_arg : -(1 + ε) * paperDensityU p ε n *
      Real.log (paperDensityU p ε n) =
        -((1 + ε) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n))) := by ring
  have hexp : Real.exp (-(paperT p n)) ≤
      Real.exp (-(1 + ε) * paperDensityU p ε n *
        Real.log (paperDensityU p ε n)) := by
    apply Real.exp_le_exp.mpr
    rw [hexp_arg]
    linarith [hpowle]
  calc
    p n * Real.exp (-(paperT p n))
        ≤ p n * Real.exp (-(1 + ε) * paperDensityU p ε n *
            Real.log (paperDensityU p ε n)) := by gcongr
    _ ≤ ((centeredBinProducts (centralDensityP p ε n)
          (paperDensityDelta p ε n) (paperDensityJ p ε n)
          (paperDensityM p ε n) a).card : ℝ) := hdens

/-- **Positivity of the central-scale bin count.**  Under the central prime
supply the insertion count is strictly positive: it dominates
`p * exp (-t_p) > 0`. -/
theorem centralDensity_binCount_pos
    (line : DirichletLZerosOnLine)
    (p : ℕ → ℝ) (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ (CentralPrimeSupply p ε K →
      ∀ᶠ n : ℕ in atTop,
        ∃ a ∈ Finset.range (paperDensityM p ε n * (paperDensityJ p ε n - 1) + 1),
          0 < ((centeredBinProducts (centralDensityP p ε n)
            (paperDensityDelta p ε n) (paperDensityJ p ε n)
            (paperDensityM p ε n) a).card : ℝ)) := by
  obtain ⟨K, hK, hcount⟩ := eventually_centralDensity_binCount_of_supply line p h hε
  refine ⟨K, hK, fun hsupply => ?_⟩
  filter_upwards [hcount hsupply, h.eventually_sixteen] with n hn hp16
  obtain ⟨a, ha, hle⟩ := hn
  refine ⟨a, ha, ?_⟩
  have hp0 : 0 < p n := by linarith
  have hpos : 0 < p n * Real.exp (-(paperT p n)) :=
    mul_pos hp0 (Real.exp_pos _)
  exact lt_of_lt_of_le hpos hle

/-! ## 4. The precise residual, and why it cannot be met -/

/-- **The central-prime-supply obstruction.**

If `P ^ m = p`, `m ≥ 2`, and the strip lies in the `√p`-window
(`m δ < log (1 + 1/√p)`), then the supply guard

```
K (1 + log (3y))² √y + 1 ≤ (1/2) δ (P exp (-(δ J)))
```

is false for every `K ≥ 0`.  The reason is elementary: the window forces
`δ P < 1/m ≤ 1/2`, so the right-hand side is `< 1`, while the left-hand side
is always `≥ 1`.  Thus the central window strip is narrower than the GRH
prime-supply error in each bin. -/
theorem centralBinGuard_false_of_window
    {K P δ y p : ℝ} {J m : ℕ}
    (hp : 1 < p) (hm : 2 ≤ m) (hP : 0 < P) (hPpow : P ^ m = p)
    (hδ : 0 ≤ δ) (hwin : (m : ℝ) * δ < Real.log (1 + 1 / Real.sqrt p))
    (hK : 0 ≤ K) :
    ¬ centralBinGuard K P δ y J m := by
  intro hg
  have hLHS : (1 : ℝ) ≤
      K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y + 1 := by
    have hA : 0 ≤ K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y :=
      mul_nonneg (mul_nonneg hK (sq_nonneg _)) (Real.sqrt_nonneg _)
    linarith
  have hRHS_le : (1 - (1 / 2)) * δ * (P * Real.exp (-(δ * (J : ℝ)))) ≤
      (1 / 2) * δ * P := by
    have hexp_le : Real.exp (-(δ * (J : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hJnn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      nlinarith [mul_nonneg hδ hJnn]
    have hcoef : 0 ≤ (1 / 2) * δ := by positivity
    calc
      (1 - (1 / 2)) * δ * (P * Real.exp (-(δ * (J : ℝ))))
          = ((1 / 2) * δ * P) * Real.exp (-(δ * (J : ℝ))) := by ring
      _ ≤ ((1 / 2) * δ * P) * 1 := by gcongr
      _ = (1 / 2) * δ * P := by ring
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hlog_le : Real.log (1 + 1 / Real.sqrt p) ≤ 1 / Real.sqrt p := by
    have hx : 0 < 1 + 1 / Real.sqrt p := by positivity
    have h := Real.log_le_sub_one_of_pos hx
    linarith
  have hmδ_lt : (m : ℝ) * δ < 1 / Real.sqrt p := hwin.trans_le hlog_le
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
  have hδ_lt : δ < 1 / ((m : ℝ) * Real.sqrt p) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) * Real.sqrt p)]
    have hmul := mul_lt_mul_of_pos_right hmδ_lt hs0
    have hss : (1 / Real.sqrt p) * Real.sqrt p = 1 := by
      field_simp [hs0.ne']
    rw [hss] at hmul
    have hstep : ((m : ℝ) * δ) * Real.sqrt p < 1 := hmul
    calc
      δ * ((m : ℝ) * Real.sqrt p) = ((m : ℝ) * δ) * Real.sqrt p := by ring
      _ < 1 := hstep
  have hP1 : 1 < P := by
    by_contra hnot
    have hle : P ≤ 1 := le_of_not_gt hnot
    have hpm : P ^ m ≤ 1 := pow_le_one₀ hP.le hle
    rw [hPpow] at hpm
    linarith
  have hP_le_sqrt : P ≤ Real.sqrt p := by
    have hP2 : P ^ 2 ≤ p := by
      calc
        P ^ 2 ≤ P ^ m := pow_le_pow_right₀ hP1.le hm
        _ = p := hPpow
    calc
      P = Real.sqrt (P ^ 2) := (Real.sqrt_sq hP.le).symm
      _ ≤ Real.sqrt p := Real.sqrt_le_sqrt hP2
  have hδP_lt : δ * P < 1 := by
    calc
      δ * P < (1 / ((m : ℝ) * Real.sqrt p)) * P :=
        mul_lt_mul_of_pos_right hδ_lt hP
      _ ≤ (1 / ((m : ℝ) * Real.sqrt p)) * Real.sqrt p := by gcongr
      _ = 1 / (m : ℝ) := by field_simp [hs0.ne']
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast (show (1 : ℕ) ≤ m by omega)
  have hhalf_lt : (1 / 2) * δ * P < 1 := by nlinarith [hδP_lt]
  have h1 : (1 : ℝ) ≤ (1 / 2) * δ * P :=
    le_trans hLHS (le_trans hg hRHS_le)
  linarith

/-- **No eventual central supply survives a window strip.**  If a family of
central bins has `P n ^ m n = p n`, eventually `m n ≥ 2`, and every strip lies
in the `√p`-window, then `centralBinGuard` fails at infinitely many bands, so
it is not eventually true. -/
theorem not_eventually_centralBinGuard_of_window
    {K : ℝ} {P δ y p : ℕ → ℝ} {J m : ℕ → ℕ}
    (hK : 0 ≤ K)
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (hm : ∀ᶠ n : ℕ in atTop, 2 ≤ m n)
    (hP : ∀ᶠ n : ℕ in atTop, 0 < P n)
    (hPpow : ∀ᶠ n : ℕ in atTop, P n ^ m n = p n)
    (hδ : ∀ᶠ n : ℕ in atTop, 0 ≤ δ n)
    (hwin : ∀ᶠ n : ℕ in atTop,
      (m n : ℝ) * δ n < Real.log (1 + 1 / Real.sqrt (p n))) :
    ¬ (∀ᶠ n : ℕ in atTop,
      centralBinGuard K (P n) (δ n) (y n) (J n) (m n)) := by
  intro hg
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hp, hm, hP, hPpow, hδ, hwin, hg] with
      n hp_n hm_n hP_n hPpow_n hδ_n hwin_n hg_n
    exact centralBinGuard_false_of_window hp_n hm_n hP_n hPpow_n hδ_n hwin_n hK hg_n
  obtain ⟨n, hn⟩ := hfalse.exists
  exact hn

/-- The concrete central-window prime supply: `centralBinGuard` at
`centralP`, `centralWindowDelta`, `centralM`. -/
def CentralWindowSupply (p : ℕ → ℝ) (ε : ℝ) (K : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    centralBinGuard K (centralP p ε n) (centralWindowDelta p ε n)
      (paperDensityY p ε n) (paperDensityJ p ε n) (centralM p ε n)

/-- The central window strip is eventually inside the `√p`-window. -/
theorem eventually_centralWindow {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      p n * Real.exp ((centralM p ε n : ℝ) * centralWindowDelta p ε n) <
        p n + Real.sqrt (p n) := by
  filter_upwards [h.eventually_sixteen, eventually_centralM_pos h hε] with n hp hm
  exact central_p_mul_exp_lt_window (by linarith) hm

/-- **Every central-window bin product is a literal short-interval smooth
integer.**  This is the concrete eventual form of
`centralBinProducts_subset_shortSmoothInterval` at the central parameters
`centralP`, `centralM`, `centralWindowDelta`. -/
theorem eventually_centralWindowProducts_subset_shortSmoothInterval
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    {y : ℕ → ℝ} {J a : ℕ → ℕ}
    (hfloor : ∀ᶠ n : ℕ in atTop, ∀ j < J n,
      (centeredBinFloor (centralP p ε n) (centralWindowDelta p ε n)
        (a n) (centralM p ε n) (j + 1) : ℝ) ≤ y n) :
    ∀ᶠ n : ℕ in atTop,
      centeredBinProducts (centralP p ε n) (centralWindowDelta p ε n)
        (J n) (centralM p ε n) (a n) ⊆
          shortSmoothInterval (p n) (y n) := by
  filter_upwards [h.eventually_sixteen, eventually_centralM_pos h hε,
    eventually_centralWindow h hε, hfloor] with n hp16 hm hwin hfloorn
  have hp1 : 1 < p n := by linarith
  have hp0 : 0 < p n := by linarith
  exact centralBinProducts_subset_shortSmoothInterval hp1
    (centralP_pos hp0).le hm
    (centralP_pow hp0 hm) hwin hfloorn

/-- **The central window has no positive prime supply.**  For every `K ≥ 0`,
the guard needed by the insertion argument fails on the central window strip.
This is the exact sense in which the remaining central estimate is stronger
than the GRH prime supply used by L30. -/
theorem not_eventually_centralWindowSupply {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) :
    ¬ CentralWindowSupply p ε K := by
  apply not_eventually_centralBinGuard_of_window
    (y := paperDensityY p ε) (P := centralP p ε) (δ := centralWindowDelta p ε)
    (p := p) (J := paperDensityJ p ε) (m := centralM p ε) hK
  · filter_upwards [h.eventually_sixteen] with n hp
    linarith
  · exact eventually_centralM_ge_two h hε
  · filter_upwards [h.eventually_sixteen] with n hp
    exact centralP_pos (by linarith)
  · filter_upwards [h.eventually_sixteen, eventually_centralM_pos h hε] with n hp hm
    exact centralP_pow (by linarith) hm
  · filter_upwards [h.eventually_sixteen] with n hp
    exact centralWindowDelta_nonneg (by linarith)
  · filter_upwards [h.eventually_sixteen, eventually_centralM_pos h hε] with n hp hm
    rw [centralM_mul_centralWindowDelta (by linarith) hm]
    exact quarter_div_sqrt_lt_log_one_add_inv_sqrt (by linarith)

end Cogentic.RandomizedL21_2CentralBin

/-! ## Axiom audit -/

namespace Cogentic.RandomizedL21_2CentralBin

#print axioms centralU_eq_half_paperDensityU
#print axioms tendsto_centralU_of_growth
#print axioms centralM_pos
#print axioms eventually_centralM_ge_two
#print axioms centralP_pow
#print axioms centralWindow_additive_width
#print axioms quarter_div_sqrt_lt_log_one_add_inv_sqrt
#print axioms central_p_mul_exp_lt_window
#print axioms centralBinProducts_subset_shortSmoothInterval
#print axioms card_centralBinProducts_le_shortSmoothCount
#print axioms centralDensityP_pow
#print axioms centralDensityP_logP
#print axioms eventually_centralDensity_lower
#print axioms eventually_centralDensity_upper
#print axioms eventually_centralDensity_binCount_of_supply
#print axioms centralDensity_binCount_pos
#print axioms centralBinGuard_false_of_window
#print axioms not_eventually_centralBinGuard_of_window
#print axioms eventually_centralWindow
#print axioms eventually_centralWindowProducts_subset_shortSmoothInterval
#print axioms not_eventually_centralWindowSupply

end Cogentic.RandomizedL21_2CentralBin
