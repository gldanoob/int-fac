import Cogentic.RandomizedL20_2BandScale

set_option linter.style.haveILetI false

/-!
# L20.2: the paper's band numeric regime

`Cogentic.RandomizedL20_2BandScale` reduced the L20.2 prime-bin character
decay to the floor-free scalar inequality `PaperBandFloorFreeCore`:

```
exp (decayExponent / (H/(4δ) - 1)) * 2K (1 + log (3qy))² sqrt y log y
  + Ks (1 + log (3y))² sqrt y
  ≤ δ * (x^(1/k) * exp (-(H/4))) - 1 ,
```

with `δ = log (1+λ)/(2k)`, `P = x^(1/k)` and `H = log (y/P)`.

This file proves that inequality for the paper's actual asymptotics
(`paperD n = exp (scale n)`, `scale n → ∞`).  The paper's top cofactor has
logarithmic scale `log X = D log D`, its smoothness cutoff has logarithmic
scale `log y = D`, and the pattern length is

```
u₀ = log X / log y = log D = scale n ,
k = ⌈u₀ (1 + 1/log u₀)⌉ .
```

We take `λ = 1`, so `δ = log 2/(2k)`.  The important structural fact is that
`P = x^(1/k) = exp (log X / k)` is close to `y = exp D`: writing
`M = log y = D`, `L = log X = M u₀`, one has

```
H = log (y/P) = M - L/k = M (k - u₀)/k .
```

Because `k ≥ u₀ (1 + 1/log u₀)` and `k ≤ u₀ (1 + 2/log u₀)` eventually,
`H` is comparable to `M / log u₀`.  Hence the *floor-free* exponent

```
A = decayExponent / (H/(4δ) - 1)
  = c D log D / (H/(4δ) - 1)
```

is only `O (log log D)`, and the bottom endpoint

```
δ * (P exp (-H/4)) = δ * exp (M - 5H/4)
```

has exponent `M - o(M)`, which dominates the envelope `exp A · sqrt y · (log y)^3`.

## The exact scalar condition

After bounding the two logarithmic factors by `2 log y`, it is enough to prove

```
exp A * (2K + Ks + 1) * (2 log y)^3 * sqrt y + 1
  ≤ δ * (P * exp (-(H/4))) .
```

Writing `A ≤ 4 c (log 2) (log u₀ + 2) ≤ M/32`, `H ≤ 2 M / log u₀`,
`δ ≥ log 2/(4 u₀)` and `sqrt y = exp (M/2)`, and using `H ≤ M/10`
(hence `M - 5H/4 ≥ 7M/8`), this reduces to the single inequality

```
(4 u₀/log 2) * exp A * (2K + Ks + 1) * (2M)^3 * exp (M/2)
  + 4 u₀/log 2
  ≤ exp (7M/8) ,
```

which holds for all sufficiently large `n`: the left side is
`u₀ · exp (O (log log u₀)) · M^3 · exp (M/2)`, i.e. `exp (M/2 + o(M))`, while
the right side is `exp (7M/8)`.  The proof below makes the absorption explicit:
`exp A`, `2K+Ks+1`, `(2M)^3` and `4u₀/log 2` are each at most `exp (M/32)`,
which gives `exp (5M/8)` for the product; the additive `4u₀/log 2` is also at
most `exp (M/32)`, and the final sum is below `exp (7M/8)`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and the width is
never set to zero: the `- 1` floor loss is retained.
-/

namespace Cogentic.RandomizedL20_2BandNumeric

open Filter Real
open Asymptotics
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Decay
open Cogentic.RandomizedL20_2Width
open Cogentic.RandomizedL20_2ScalarWidth
open Cogentic.RandomizedL20_2BandScale
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.Randomized

noncomputable section

/-! ## 1. The paper's numeric band parameters -/

/-- `log y = D = exp (scale n)`. -/
def paperBandLogY (n : ℕ) : ℝ := paperD n

/-- The paper's `u₀ = log X / log y = log D = scale n`. -/
def paperBandU (n : ℕ) : ℝ := scale n

/-- `log X = D log D = u₀ log y`. -/
def paperBandLogX (n : ℕ) : ℝ := paperBandLogY n * paperBandU n

/-- The paper's top cofactor scale `x = X = exp (D log D)`. -/
def paperBandX (n : ℕ) : ℝ := Real.exp (paperBandLogX n)

/-- The paper's smoothness cutoff `y = exp D`. -/
def paperBandY (n : ℕ) : ℝ := Real.exp (paperBandLogY n)

/-- The paper's pattern length `k = ⌈u₀ (1 + 1/log u₀)⌉`. -/
def paperBandK (n : ℕ) : ℕ :=
  Nat.ceil (paperBandU n * (1 + 1 / Real.log (paperBandU n)))

theorem paperBandX_pos (n : ℕ) : 0 < paperBandX n := Real.exp_pos _

theorem paperBandY_pos (n : ℕ) : 0 < paperBandY n := Real.exp_pos _

theorem log_paperBandX (n : ℕ) : Real.log (paperBandX n) = paperBandLogX n :=
  Real.log_exp _

theorem log_paperBandY (n : ℕ) : Real.log (paperBandY n) = paperBandLogY n :=
  Real.log_exp _

theorem paperBandLogY_pos (n : ℕ) : 0 < paperBandLogY n := paperD_pos n

theorem paperBandP_paperBandX (n : ℕ) :
    paperBandP (paperBandX n) (paperBandK n) =
      Real.exp (paperBandLogX n / (paperBandK n : ℝ)) := by
  unfold paperBandP
  rw [Real.rpow_def_of_pos (paperBandX_pos n), log_paperBandX]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- The band height `H = log (y/P)` in the paper's regime. -/
theorem paperBandH_paperBandX (n : ℕ) :
    paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) =
      paperBandLogY n - paperBandLogX n / (paperBandK n : ℝ) := by
  unfold paperBandH
  rw [paperBandP_paperBandX, Real.log_div (paperBandY_pos n).ne' (Real.exp_pos _).ne',
    log_paperBandY, Real.log_exp]

theorem paperBandDelta_one (k : ℕ) :
    paperBandDelta 1 k = Real.log 2 / (2 * (k : ℝ)) := by
  unfold paperBandDelta
  norm_num

/-! ## 2. Abstract absorption: a power is eventually dominated by an exponential -/

/-- If `f → ∞` then `(f n)^k = o (exp (c * f n))`; this is the only asymptotic
input used below. -/
theorem eventually_pow_le_const_mul_exp_of_tendsto
    {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) {k : ℕ} {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (f n) ^ k ≤ ε * Real.exp (c * f n) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop k hc).def hε
  have h' := hf.eventually h
  filter_upwards [h', hf.eventually_ge_atTop 0] with n hn hs
  have hnk : 0 ≤ (f n) ^ k := pow_nonneg hs k
  have hexp : 0 ≤ Real.exp (c * f n) := (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hnk, Real.norm_of_nonneg hexp] at hn
  exact hn

/-- `paperD n = exp (scale n) → ∞`. -/
theorem tendsto_paperD : Tendsto paperD atTop atTop :=
  Real.tendsto_exp_atTop.comp scale_grows

theorem tendsto_paperBandLogY : Tendsto paperBandLogY atTop atTop :=
  tendsto_paperD

theorem tendsto_paperBandU : Tendsto paperBandU atTop atTop :=
  scale_grows

theorem tendsto_log_paperBandU :
    Tendsto (fun n => Real.log (paperBandU n)) atTop atTop :=
  Real.tendsto_log_atTop.comp scale_grows

theorem eventually_const_le_paperBandLogY {C : ℝ} :
    ∀ᶠ n : ℕ in atTop, C ≤ paperBandLogY n :=
  tendsto_paperBandLogY.eventually_ge_atTop C

theorem eventually_paperBandU_pos : ∀ᶠ n : ℕ in atTop, 0 < paperBandU n :=
  tendsto_paperBandU.eventually_gt_atTop 0

theorem eventually_paperBandU_ge_two : ∀ᶠ n : ℕ in atTop, 2 ≤ paperBandU n :=
  tendsto_paperBandU.eventually_ge_atTop 2

theorem eventually_log_paperBandU_ge_two :
    ∀ᶠ n : ℕ in atTop, 2 ≤ Real.log (paperBandU n) :=
  tendsto_log_paperBandU.eventually_ge_atTop 2

theorem eventually_log_paperBandU_ge_twenty :
    ∀ᶠ n : ℕ in atTop, 20 ≤ Real.log (paperBandU n) :=
  tendsto_log_paperBandU.eventually_ge_atTop 20

theorem eventually_log_paperBandU_le_self :
    ∀ᶠ n : ℕ in atTop, Real.log (paperBandU n) ≤ paperBandU n := by
  filter_upwards [eventually_paperBandU_pos] with n hu
  exact Real.log_le_self hu.le

/-! ## 3. Bounds for the paper's `k` and the band height `H` -/

/-- The ceiling defining `k` gives
`u₀ (1 + 1/log u₀) ≤ k ≤ u₀ (1 + 2/log u₀)` eventually. -/
theorem eventually_paperBandK_bounds :
    ∀ᶠ n : ℕ in atTop,
      paperBandU n ≤ (paperBandK n : ℝ) ∧
      paperBandU n * (1 + 1 / Real.log (paperBandU n)) ≤ (paperBandK n : ℝ) ∧
      (paperBandK n : ℝ) ≤ paperBandU n * (1 + 2 / Real.log (paperBandU n)) := by
  filter_upwards [eventually_paperBandU_pos, eventually_paperBandU_ge_two,
    eventually_log_paperBandU_ge_two] with n hu htwo hlog
  have hlogpos : 0 < Real.log (paperBandU n) := by linarith
  have harg_nonneg : 0 ≤ paperBandU n * (1 + 1 / Real.log (paperBandU n)) := by
    positivity
  have hle : paperBandU n * (1 + 1 / Real.log (paperBandU n)) ≤
      (paperBandK n : ℝ) := Nat.le_ceil _
  have hlt : (paperBandK n : ℝ) <
      paperBandU n * (1 + 1 / Real.log (paperBandU n)) + 1 :=
    Nat.ceil_lt_add_one harg_nonneg
  have hu_ge : paperBandU n ≤ paperBandU n * (1 + 1 / Real.log (paperBandU n)) := by
    have h1 : (0 : ℝ) ≤ 1 / Real.log (paperBandU n) := by positivity
    calc
      paperBandU n = paperBandU n * 1 := by ring
      _ ≤ paperBandU n * (1 + 1 / Real.log (paperBandU n)) :=
        mul_le_mul_of_nonneg_left (by linarith) hu.le
  have hlog_le : Real.log (paperBandU n) ≤ paperBandU n := Real.log_le_self hu.le
  have hratio : (1 : ℝ) ≤ paperBandU n / Real.log (paperBandU n) := by
    rw [le_div_iff₀ hlogpos]
    simpa using hlog_le
  have hone : (1 : ℝ) ≤ paperBandU n * (1 / Real.log (paperBandU n)) := by
    rw [mul_one_div]
    exact hratio
  have hstep : paperBandU n * (1 + 1 / Real.log (paperBandU n)) + 1 ≤
      paperBandU n * (1 + 2 / Real.log (paperBandU n)) := by
    have hrewrite : paperBandU n * (1 + 2 / Real.log (paperBandU n)) -
        (paperBandU n * (1 + 1 / Real.log (paperBandU n)) + 1) =
        paperBandU n / Real.log (paperBandU n) - 1 := by
      field_simp [hlogpos.ne']
      ring
    nlinarith [hratio, hrewrite]
  exact ⟨hu_ge.trans hle, hle, hlt.le.trans hstep⟩

/-- The ceiling definition implies `u₀ ≤ k` as soon as `log u₀ ≥ 0`. -/
theorem paperBandU_le_paperBandK (n : ℕ) (hu : 0 < paperBandU n)
    (hlog : 0 ≤ Real.log (paperBandU n)) :
    paperBandU n ≤ (paperBandK n : ℝ) := by
  unfold paperBandK
  have h1 : (0 : ℝ) ≤ 1 / Real.log (paperBandU n) := by positivity
  calc
    paperBandU n = paperBandU n * 1 := by ring
    _ ≤ paperBandU n * (1 + 1 / Real.log (paperBandU n)) :=
      mul_le_mul_of_nonneg_left (by linarith) hu.le
    _ ≤ (Nat.ceil (paperBandU n * (1 + 1 / Real.log (paperBandU n))) : ℝ) :=
      Nat.le_ceil _

/-- `H = M (k - u₀)/k` in the paper's regime. -/
theorem paperBandH_eq_mul_sub {n : ℕ} (_hu : 0 < paperBandU n)
    (hk : 0 < (paperBandK n : ℝ)) :
    paperBandLogY n - paperBandLogX n / (paperBandK n : ℝ) =
      paperBandLogY n * ((paperBandK n : ℝ) - paperBandU n) / (paperBandK n : ℝ) := by
  unfold paperBandLogX
  field_simp [hk.ne']

/-- The band height is bounded below by `M/(log u₀ + 2)`. -/
theorem paperBandH_ge {n : ℕ} (hu : 0 < paperBandU n) (hlog : 2 ≤ Real.log (paperBandU n))
    (hklo : paperBandU n * (1 + 1 / Real.log (paperBandU n)) ≤ (paperBandK n : ℝ)) :
    paperBandLogY n / (Real.log (paperBandU n) + 2) ≤
      paperBandLogY n - paperBandLogX n / (paperBandK n : ℝ) := by
  have hlogpos : 0 < Real.log (paperBandU n) := by linarith
  have hkpos : 0 < (paperBandK n : ℝ) :=
    lt_of_lt_of_le (by positivity) hklo
  have huk := paperBandU_le_paperBandK n hu hlogpos.le
  have hM : 0 ≤ paperBandLogY n := (paperBandLogY_pos n).le
  -- `u₀ (log u₀ + 1) ≤ k log u₀`
  have hmul : paperBandU n * (1 + 1 / Real.log (paperBandU n)) *
        Real.log (paperBandU n) ≤ (paperBandK n : ℝ) * Real.log (paperBandU n) :=
    mul_le_mul_of_nonneg_right hklo hlogpos.le
  have hmul' : paperBandU n * (Real.log (paperBandU n) + 1) ≤
      (paperBandK n : ℝ) * Real.log (paperBandU n) := by
    convert hmul using 1
    field_simp [hlogpos.ne']
  -- `u₀ (log u₀ + 2) ≤ k (log u₀ + 1)`
  have hkey : paperBandU n * (Real.log (paperBandU n) + 2) ≤
      (paperBandK n : ℝ) * (Real.log (paperBandU n) + 1) := by
    nlinarith [hmul', huk, hlogpos]
  have hden : 0 < Real.log (paperBandU n) + 2 := by positivity
  have hfrac : 1 / (Real.log (paperBandU n) + 2) ≤
      ((paperBandK n : ℝ) - paperBandU n) / (paperBandK n : ℝ) := by
    rw [div_le_div_iff₀ hden hkpos]
    nlinarith [hkey]
  calc
    paperBandLogY n / (Real.log (paperBandU n) + 2) =
        paperBandLogY n * (1 / (Real.log (paperBandU n) + 2)) := by ring
    _ ≤ paperBandLogY n * (((paperBandK n : ℝ) - paperBandU n) / (paperBandK n : ℝ)) :=
      mul_le_mul_of_nonneg_left hfrac hM
    _ = paperBandLogY n - paperBandLogX n / (paperBandK n : ℝ) := by
      rw [paperBandH_eq_mul_sub hu hkpos]
      ring

/-- The band height is bounded above by `2M/log u₀`. -/
theorem paperBandH_le {n : ℕ} (hu : 0 < paperBandU n) (hlog : 2 ≤ Real.log (paperBandU n))
    (hkhi : (paperBandK n : ℝ) ≤ paperBandU n * (1 + 2 / Real.log (paperBandU n))) :
    paperBandLogY n - paperBandLogX n / (paperBandK n : ℝ) ≤
      2 * paperBandLogY n / Real.log (paperBandU n) := by
  have hlogpos : 0 < Real.log (paperBandU n) := by linarith
  have huk := paperBandU_le_paperBandK n hu hlogpos.le
  have hkpos : 0 < (paperBandK n : ℝ) := lt_of_lt_of_le hu huk
  have hM : 0 ≤ paperBandLogY n := (paperBandLogY_pos n).le
  -- `k log u₀ ≤ u₀ log u₀ + 2 u₀`
  have hmul : (paperBandK n : ℝ) * Real.log (paperBandU n) ≤
      paperBandU n * (1 + 2 / Real.log (paperBandU n)) * Real.log (paperBandU n) :=
    mul_le_mul_of_nonneg_right hkhi hlogpos.le
  have hmul' : (paperBandK n : ℝ) * Real.log (paperBandU n) ≤
      paperBandU n * Real.log (paperBandU n) + 2 * paperBandU n := by
    have heq : paperBandU n * (1 + 2 / Real.log (paperBandU n)) * Real.log (paperBandU n) =
        paperBandU n * Real.log (paperBandU n) + 2 * paperBandU n := by
      field_simp [hlogpos.ne']
    rw [heq] at hmul
    exact hmul
  -- `(k - u₀) log u₀ ≤ 2 k`
  have hkey : ((paperBandK n : ℝ) - paperBandU n) * Real.log (paperBandU n) ≤
      2 * (paperBandK n : ℝ) := by
    nlinarith [hmul', huk]
  have hfrac : ((paperBandK n : ℝ) - paperBandU n) / (paperBandK n : ℝ) ≤
      2 / Real.log (paperBandU n) := by
    rw [div_le_div_iff₀ hkpos hlogpos]
    nlinarith [hkey]
  calc
    paperBandLogY n - paperBandLogX n / (paperBandK n : ℝ) =
        paperBandLogY n * (((paperBandK n : ℝ) - paperBandU n) / (paperBandK n : ℝ)) := by
      rw [paperBandH_eq_mul_sub hu hkpos]
      ring
    _ ≤ paperBandLogY n * (2 / Real.log (paperBandU n)) :=
      mul_le_mul_of_nonneg_left hfrac hM
    _ = 2 * paperBandLogY n / Real.log (paperBandU n) := by ring

/-! ## 4. The exact scalar condition and the reduction to the core -/

/-- **The exact scalar condition.**  After bounding the two logarithmic factors
by `2 log y`, `PaperBandFloorFreeCore` follows from the single inequality

```
exp A * (2K + Ks + 1) * (2 log y)^3 * sqrt y + 1
  ≤ δ * (P * exp (-(H/4))) ,
```

where `A = decayExponent / (H/(4δ) - 1)`, `P = x^(1/k)` and
`H = log (y/P)`.  This is the scalar statement that the paper's asymptotics
have to satisfy; everything else is monotonicity. -/
theorem paperBandFloorFreeCore_of_logGap
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hy : 1 < y)
    (h2L : 1 ≤ 2 * Real.log y)
    (hE1 : 1 ≤ Real.exp (decayExponent c n / paperBandJLower y x lam k))
    (hlogq : 1 + Real.log (3 * (q : ℝ) * y) ≤ 2 * Real.log y)
    (hlogs : 1 + Real.log (3 * y) ≤ 2 * Real.log y)
    (hgap :
      Real.exp (decayExponent c n / paperBandJLower y x lam k) *
          (2 * K + Ks + 1) * (2 * Real.log y) ^ 3 * Real.sqrt y + 1 ≤
        paperBandDelta lam k *
          (paperBandP x k * Real.exp (-(paperBandH y (paperBandP x k) / 4)))) :
    PaperBandFloorFreeCore K Ks c q n x y lam k := by
  unfold PaperBandFloorFreeCore
  set E : ℝ := Real.exp (decayExponent c n / paperBandJLower y x lam k) with hE
  set L : ℝ := Real.log y with hL
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos hy
  have h2Lpos : 0 < 2 * L := by linarith
  have hsqrt : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbase1 : 0 ≤ 1 + Real.log (3 * (q : ℝ) * y) := by
    have h3 : (1 : ℝ) ≤ 3 * (q : ℝ) * y := by nlinarith [hq1, hy0.le]
    have : 0 ≤ Real.log (3 * (q : ℝ) * y) := Real.log_nonneg h3
    linarith
  have hbase2 : 0 ≤ 1 + Real.log (3 * y) := by
    have h3 : (1 : ℝ) ≤ 3 * y := by nlinarith [hy0.le]
    have : 0 ≤ Real.log (3 * y) := Real.log_nonneg h3
    linarith
  have hB1 : (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 ≤ (2 * L) ^ 2 := by
    rw [hL]
    exact pow_le_pow_left₀ hbase1 hlogq 2
  have hB2 : (1 + Real.log (3 * y)) ^ 2 ≤ (2 * L) ^ 2 := by
    rw [hL]
    exact pow_le_pow_left₀ hbase2 hlogs 2
  have hE1' : 1 ≤ E := by rw [hE]; exact hE1
  have hterm1 :
      E * (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y ≤
        E * K * (2 * L) ^ 3 * Real.sqrt y := by
    calc
      E * (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y =
          E * (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * L := by
        rw [hL]
      _ ≤ E * (2 * K) * (2 * L) ^ 2 * Real.sqrt y * L := by gcongr
      _ = E * K * (2 * L) ^ 3 * Real.sqrt y := by ring
  have hterm2 :
      Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
        Ks * (2 * L) ^ 3 * Real.sqrt y := by
    calc
      Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
          Ks * (2 * L) ^ 2 * Real.sqrt y := by gcongr
      _ ≤ Ks * (2 * L) ^ 3 * Real.sqrt y := by
        have hmono : (2 * L) ^ 2 ≤ (2 * L) ^ 3 := by
          nlinarith [h2L, h2Lpos, sq_nonneg (2 * L)]
        gcongr
  have hcoef : E * K + Ks ≤ E * (2 * K + Ks + 1) := by nlinarith [hE1', hK, hKs]
  have hfac : 0 ≤ (2 * L) ^ 3 * Real.sqrt y := by positivity
  have hcoefmul := mul_le_mul_of_nonneg_right hcoef hfac
  have hsum :
      E * K * (2 * L) ^ 3 * Real.sqrt y + Ks * (2 * L) ^ 3 * Real.sqrt y ≤
        E * (2 * K + Ks + 1) * (2 * L) ^ 3 * Real.sqrt y := by
    calc
      E * K * (2 * L) ^ 3 * Real.sqrt y + Ks * (2 * L) ^ 3 * Real.sqrt y =
          (E * K + Ks) * ((2 * L) ^ 3 * Real.sqrt y) := by ring
      _ ≤ E * (2 * K + Ks + 1) * ((2 * L) ^ 3 * Real.sqrt y) := hcoefmul
      _ = E * (2 * K + Ks + 1) * (2 * L) ^ 3 * Real.sqrt y := by ring
  have hfinal :
      E * (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
          Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
        E * (2 * K + Ks + 1) * (2 * L) ^ 3 * Real.sqrt y := by
    linarith [hterm1, hterm2, hsum]
  have hgap' :
      E * (2 * K + Ks + 1) * (2 * L) ^ 3 * Real.sqrt y + 1 ≤
        paperBandDelta lam k *
          (paperBandP x k * Real.exp (-(paperBandH y (paperBandP x k) / 4))) := by
    rw [hL, hE]
    exact hgap
  linarith [hfinal, hgap']

/-! ## 5. The floor-free bin count and the scalar exponent -/

/-- In the paper's regime the floor-free bin count is at least
`L / (4 log 2 (log u₀ + 2))`, where `L = log x = M u₀`. -/
theorem paperBandJLower_lower {n : ℕ}
    (hu : 0 < paperBandU n) (hlog : 2 ≤ Real.log (paperBandU n))
    (hklo : paperBandU n * (1 + 1 / Real.log (paperBandU n)) ≤ (paperBandK n : ℝ))
    (hLbig : 4 * Real.log 2 * (Real.log (paperBandU n) + 2) ≤ paperBandLogX n) :
    paperBandLogX n / (4 * Real.log 2 * (Real.log (paperBandU n) + 2)) ≤
      paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : 0 < Real.log (paperBandU n) := by linarith
  have hkpos : 0 < (paperBandK n : ℝ) := lt_of_lt_of_le (by positivity) hklo
  have hHge : paperBandLogY n / (Real.log (paperBandU n) + 2) ≤
      paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) := by
    rw [paperBandH_paperBandX]
    exact paperBandH_ge hu hlog hklo
  have hHle' : paperBandLogY n ≤
      paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) *
        (Real.log (paperBandU n) + 2) := by
    have hden : 0 < Real.log (paperBandU n) + 2 := by positivity
    exact (div_le_iff₀ hden).mp hHge
  have huk : paperBandU n ≤ (paperBandK n : ℝ) := paperBandU_le_paperBandK n hu hlogpos.le
  have hprod : paperBandLogY n * paperBandU n ≤
      paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) *
        (Real.log (paperBandU n) + 2) * (paperBandK n : ℝ) := by
    have hnn : 0 ≤ paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) *
        (Real.log (paperBandU n) + 2) :=
      (paperBandLogY_pos n).le.trans hHle'
    exact mul_le_mul hHle' huk hu.le hnn
  have hJeq : paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n) =
      paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) *
        (paperBandK n : ℝ) / (2 * Real.log 2) - 1 := by
    rw [paperBandJLower, paperBandDelta_one]
    field_simp [hkpos.ne', hlog2pos.ne']
    ring
  rw [hJeq]
  have hden : 0 < 4 * Real.log 2 * (Real.log (paperBandU n) + 2) := by positivity
  rw [div_le_iff₀ hden]
  have hexpand : (paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) *
        (paperBandK n : ℝ) / (2 * Real.log 2) - 1) *
        (4 * Real.log 2 * (Real.log (paperBandU n) + 2)) =
      2 * paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) *
          (paperBandK n : ℝ) * (Real.log (paperBandU n) + 2) -
        4 * Real.log 2 * (Real.log (paperBandU n) + 2) := by
    field_simp [hlog2pos.ne']
    ring
  rw [hexpand]
  unfold paperBandLogX at hLbig ⊢
  nlinarith [hprod, hLbig, paperBandLogY_pos n, hu]

/-- **The scalar exponent.**  In the paper's regime the floor-free exponent is at
most `4 c log 2 (log u₀ + 2)`. -/
theorem paperBandExponent_le {n : ℕ} {c : ℝ} (hc : 0 < c)
    (hu : 0 < paperBandU n) (hlog : 2 ≤ Real.log (paperBandU n))
    (hklo : paperBandU n * (1 + 1 / Real.log (paperBandU n)) ≤ (paperBandK n : ℝ))
    (hLbig : 4 * Real.log 2 * (Real.log (paperBandU n) + 2) ≤ paperBandLogX n) :
    decayExponent c n / paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n) ≤
      4 * c * Real.log 2 * (Real.log (paperBandU n) + 2) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : 0 < Real.log (paperBandU n) := by linarith
  have hLpos : 0 < paperBandLogX n := by
    unfold paperBandLogX
    exact mul_pos (paperBandLogY_pos n) hu
  have hdenpos : 0 < paperBandLogX n / (4 * Real.log 2 * (Real.log (paperBandU n) + 2)) := by
    positivity
  have hJ := paperBandJLower_lower hu hlog hklo hLbig
  have hJpos : 0 < paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n) :=
    lt_of_lt_of_le hdenpos hJ
  have hdecay : decayExponent c n = c * paperBandLogX n := by
    unfold decayExponent paperBandLogX paperBandLogY paperBandU
    ring
  rw [hdecay]
  have hnum : 0 ≤ c * paperBandLogX n := by positivity
  have hstep := div_le_div_of_nonneg_left hnum hdenpos hJ
  refine hstep.trans ?_
  have hden : 4 * Real.log 2 * (Real.log (paperBandU n) + 2) ≠ 0 := by positivity
  field_simp [hLpos.ne', hden]
  norm_num

/-- The bottom endpoint supplies at least `(log 2/(4u₀)) exp (7M/8)`. -/
theorem paperBandBottom_lower {n : ℕ}
    (hu : 0 < paperBandU n) (hlog : 20 ≤ Real.log (paperBandU n))
    (hkhi : (paperBandK n : ℝ) ≤ paperBandU n * (1 + 2 / Real.log (paperBandU n)))
    (hHle : paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) ≤
      2 * paperBandLogY n / Real.log (paperBandU n)) :
    Real.log 2 / (4 * paperBandU n) * Real.exp (7 * paperBandLogY n / 8) ≤
      paperBandDelta 1 (paperBandK n) *
        (paperBandP (paperBandX n) (paperBandK n) *
          Real.exp (-(paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) / 4))) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : 0 < Real.log (paperBandU n) := by linarith
  have hkpos : 0 < (paperBandK n : ℝ) := by
    have huk := paperBandU_le_paperBandK n hu hlogpos.le
    exact lt_of_lt_of_le hu huk
  -- `δ ≥ log 2/(4u₀)`
  have hδ : Real.log 2 / (4 * paperBandU n) ≤ paperBandDelta 1 (paperBandK n) := by
    rw [paperBandDelta_one]
    have hk_le : (paperBandK n : ℝ) ≤ 2 * paperBandU n := by
      have hlog2 : 0 < Real.log (paperBandU n) := hlogpos
      have h1 : 1 + 2 / Real.log (paperBandU n) ≤ 2 := by
        have hdiv : 2 / Real.log (paperBandU n) ≤ 1 := by
          rw [div_le_iff₀ hlog2]
          linarith
        linarith
      nlinarith [hkhi, h1, hu.le]
    rw [div_le_div_iff₀ (by positivity : 0 < 4 * paperBandU n)
      (by positivity : 0 < 2 * (paperBandK n : ℝ))]
    nlinarith [hlog2pos, hk_le]
  -- `P exp (-H/4) = exp (L/k - H/4) = exp (7M/8)` lower bound
  have hPexp : Real.exp (7 * paperBandLogY n / 8) ≤
      paperBandP (paperBandX n) (paperBandK n) *
        Real.exp (-(paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) / 4)) := by
    rw [paperBandH_paperBandX n, paperBandP_paperBandX, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hHdef : paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) =
        paperBandLogY n - paperBandLogX n / (paperBandK n : ℝ) := paperBandH_paperBandX n
    have hH : paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) ≤
        2 * paperBandLogY n / Real.log (paperBandU n) := hHle
    have hratio : 2 / Real.log (paperBandU n) ≤ 1 / 10 := by
      rw [div_le_iff₀ hlogpos]
      nlinarith [hlog]
    have hH10 : paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) ≤
        paperBandLogY n / 10 := by
      have hMpos : 0 < paperBandLogY n := paperBandLogY_pos n
      have hmul := mul_le_mul_of_nonneg_right hratio hMpos.le
      have h2M : 2 * paperBandLogY n / Real.log (paperBandU n) =
          (2 / Real.log (paperBandU n)) * paperBandLogY n := by ring
      have hM10 : paperBandLogY n / 10 = (1 / 10) * paperBandLogY n := by ring
      linarith [hH, hmul, h2M, hM10]
    have hsmall : 5 * paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) / 4 ≤
        paperBandLogY n / 8 := by linarith
    nlinarith [hHdef, hsmall]
  have hδpos : 0 < paperBandDelta 1 (paperBandK n) :=
    lt_of_lt_of_le (by positivity) hδ
  calc
    Real.log 2 / (4 * paperBandU n) * Real.exp (7 * paperBandLogY n / 8) ≤
        paperBandDelta 1 (paperBandK n) * Real.exp (7 * paperBandLogY n / 8) :=
      mul_le_mul_of_nonneg_right hδ (Real.exp_pos _).le
    _ ≤ paperBandDelta 1 (paperBandK n) *
        (paperBandP (paperBandX n) (paperBandK n) *
          Real.exp (-(paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) / 4))) :=
      mul_le_mul_of_nonneg_left hPexp hδpos.le

/-! ## 6. The eventful numeric inequality -/

/-- `scale n ≤ C * paperD n` for any positive `C`. -/
theorem eventually_scale_le_const_mul_paperD {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, scale n ≤ C * paperD n := by
  have h := eventually_pow_le_const_mul_exp_of_tendsto (f := scale) scale_grows
    (k := 1) (c := 1) (ε := C) zero_lt_one hC
  filter_upwards [h] with n hn
  simpa [paperBandU, paperBandLogY, paperD] using hn

/-- **The exact scalar gap eventually holds in the paper's regime.** -/
theorem eventually_paperBandLogGap
    {K Ks c : ℝ} (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (decayExponent c n /
          paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n)) *
          (2 * K + Ks + 1) * (2 * Real.log (paperBandY n)) ^ 3 *
          Real.sqrt (paperBandY n) + 1 ≤
        paperBandDelta 1 (paperBandK n) *
          (paperBandP (paperBandX n) (paperBandK n) *
            Real.exp (-(paperBandH (paperBandY n)
              (paperBandP (paperBandX n) (paperBandK n)) / 4))) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set CA : ℝ := 4 * c * Real.log 2 with hCAdef
  have hCApos : 0 < CA := by rw [hCAdef]; positivity
  -- absorption facts
  have hScale1 : ∀ᶠ n : ℕ in atTop,
      paperBandU n ≤ Real.log 2 / 8 * paperBandLogY n :=
    eventually_scale_le_const_mul_paperD (C := Real.log 2 / 8) (by positivity)
  have hScale2 : ∀ᶠ n : ℕ in atTop,
      paperBandU n ≤ paperBandLogY n / (128 * CA) := by
    have h := eventually_scale_le_const_mul_paperD (C := 1 / (128 * CA)) (by positivity)
    simpa [paperBandU, paperBandLogY, paperD, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hScale3 : ∀ᶠ n : ℕ in atTop,
      paperBandU n ≤ paperBandLogY n / (16 * Real.log 2) := by
    have h := eventually_scale_le_const_mul_paperD (C := 1 / (16 * Real.log 2)) (by positivity)
    simpa [paperBandU, paperBandLogY, paperD, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hMleExp : ∀ᶠ n : ℕ in atTop,
      paperBandLogY n ≤ 2 * Real.exp (paperBandLogY n / 32) := by
    have h := eventually_pow_le_const_mul_exp_of_tendsto (f := paperBandLogY)
      tendsto_paperBandLogY (k := 1) (c := 1 / 32) (ε := 2)
      (by norm_num) (by norm_num)
    filter_upwards [h] with n hn
    have harg : (1 / 32 : ℝ) * paperBandLogY n = paperBandLogY n / 32 := by ring
    rw [harg] at hn
    simpa using hn
  have hM3 : ∀ᶠ n : ℕ in atTop,
      (2 * paperBandLogY n) ^ 3 ≤ Real.exp (paperBandLogY n / 32) := by
    have h := eventually_pow_le_const_mul_exp_of_tendsto (f := paperBandLogY)
      tendsto_paperBandLogY (k := 3) (c := 1 / 32) (ε := 1 / 8)
      (by norm_num) (by norm_num)
    filter_upwards [h] with n hn
    have harg : (1 / 32 : ℝ) * paperBandLogY n = paperBandLogY n / 32 := by ring
    rw [harg] at hn
    nlinarith [hn]
  have hC0 : ∀ᶠ n : ℕ in atTop,
      2 * K + Ks + 1 ≤ Real.exp (paperBandLogY n / 32) := by
    have hC : ∀ᶠ n : ℕ in atTop,
        2 * K + Ks + 1 ≤ paperBandLogY n / 32 := by
      have h := eventually_const_le_paperBandLogY (C := 32 * (2 * K + Ks + 1))
      filter_upwards [h] with n hn
      linarith
    filter_upwards [hC] with n hn
    exact hn.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
  have h2e : ∀ᶠ n : ℕ in atTop,
      2 ≤ Real.exp (paperBandLogY n / 32) := by
    have h := eventually_const_le_paperBandLogY (C := 32 * Real.log 2)
    filter_upwards [h] with n hn
    have hlog2 : Real.log 2 ≤ paperBandLogY n / 32 := by linarith
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (paperBandLogY n / 32) := Real.exp_le_exp.mpr hlog2
  have htwoBig : ∀ᶠ n : ℕ in atTop,
      2 ≤ Real.exp (paperBandLogY n / 4) := by
    have h := eventually_const_le_paperBandLogY (C := 4 * Real.log 2)
    filter_upwards [h] with n hn
    have hlog2 : Real.log 2 ≤ paperBandLogY n / 4 := by linarith
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (paperBandLogY n / 4) := Real.exp_le_exp.mpr hlog2
  have hLbig : ∀ᶠ n : ℕ in atTop,
      4 * Real.log 2 * (Real.log (paperBandU n) + 2) ≤ paperBandLogX n := by
    filter_upwards [hScale3, eventually_paperBandU_ge_two,
      eventually_log_paperBandU_le_self] with n hscale htwo hlogle
    have hMpos : 0 < paperBandLogY n := paperBandLogY_pos n
    have hu1 : 1 ≤ paperBandU n := by linarith
    have h1 : Real.log (paperBandU n) + 2 ≤ 3 * paperBandU n := by nlinarith
    have h2 : 4 * Real.log 2 * (Real.log (paperBandU n) + 2) ≤
        12 * Real.log 2 * paperBandU n := by
      nlinarith [h1, hlog2pos.le]
    have h3 : 12 * Real.log 2 * paperBandU n ≤ paperBandLogY n := by
      have h := (le_div_iff₀ (by positivity : 0 < 16 * Real.log 2)).mp hscale
      nlinarith [h]
    have h4 : paperBandLogY n ≤ paperBandLogX n := by
      unfold paperBandLogX
      nlinarith [hMpos, hu1]
    linarith
  have hCAabs : ∀ᶠ n : ℕ in atTop,
      CA * (Real.log (paperBandU n) + 2) ≤ paperBandLogY n / 32 := by
    filter_upwards [hScale2, eventually_paperBandU_ge_two,
      eventually_log_paperBandU_le_self] with n hscale htwo hlogle
    have h1 : Real.log (paperBandU n) + 2 ≤ 3 * paperBandU n := by nlinarith
    have h2 : CA * paperBandU n ≤ paperBandLogY n / 128 := by
      have h := (le_div_iff₀ (by positivity : 0 < 128 * CA)).mp hscale
      nlinarith [h]
    nlinarith [h1, h2, hCApos.le]
  have hCu : ∀ᶠ n : ℕ in atTop,
      4 * paperBandU n / Real.log 2 ≤ Real.exp (paperBandLogY n / 32) := by
    filter_upwards [hScale1, hMleExp] with n hscale hMle
    have hu : paperBandU n ≤ (Real.log 2 / 4) * Real.exp (paperBandLogY n / 32) := by
      calc
        paperBandU n ≤ Real.log 2 / 8 * paperBandLogY n := hscale
        _ ≤ Real.log 2 / 8 * (2 * Real.exp (paperBandLogY n / 32)) := by
          nlinarith [hMle, hlog2pos.le]
        _ = Real.log 2 / 4 * Real.exp (paperBandLogY n / 32) := by ring
    rw [div_le_iff₀ hlog2pos]
    nlinarith [hu, hlog2pos.le]
  -- main filter
  filter_upwards [eventually_paperBandU_pos, eventually_paperBandU_ge_two,
    eventually_log_paperBandU_ge_two, eventually_log_paperBandU_ge_twenty,
    eventually_paperBandK_bounds, hLbig, hCAabs, hCu, hM3, hC0, h2e, htwoBig]
    with n hupos htwo hlog2 hlog20 hkb hLbigN hCAabsN hCuN hM3N hC0N h2eN htwoBigN
  obtain ⟨huk, hklo, hkhi⟩ := hkb
  have hlogpos : 0 < Real.log (paperBandU n) := by linarith
  have hkpos : 0 < (paperBandK n : ℝ) := lt_of_lt_of_le hupos huk
  -- J lower bound and the scalar exponent
  have hJ := paperBandJLower_lower (n := n) hupos hlog2 hklo hLbigN
  have hJpos : 0 < paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n) := by
    have hLpos : 0 < paperBandLogX n := by
      unfold paperBandLogX
      exact mul_pos (paperBandLogY_pos n) hupos
    exact lt_of_lt_of_le (by positivity) hJ
  have hAraw := paperBandExponent_le (n := n) hc hupos hlog2 hklo hLbigN
  have hA32 : decayExponent c n /
      paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n) ≤
      paperBandLogY n / 32 :=
    hAraw.trans (by simpa [hCAdef] using hCAabsN)
  have hexpA : Real.exp (decayExponent c n /
      paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n)) ≤
      Real.exp (paperBandLogY n / 32) := Real.exp_le_exp.mpr hA32
  -- H upper bound
  have hHle : paperBandH (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) ≤
      2 * paperBandLogY n / Real.log (paperBandU n) := by
    rw [paperBandH_paperBandX]
    exact paperBandH_le hupos hlog2 hkhi
  -- bottom bound
  have hbot := paperBandBottom_lower (n := n) hupos hlog20 hkhi hHle
  -- sqrt y = exp (M/2)
  have hsqrt : Real.sqrt (paperBandY n) = Real.exp (paperBandLogY n / 2) := by
    unfold paperBandY
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    ring_nf
  -- abbreviations for the absorbed product
  set X : ℝ := Real.exp (decayExponent c n /
      paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n)) *
      (2 * K + Ks + 1) * (2 * Real.log (paperBandY n)) ^ 3 *
      Real.sqrt (paperBandY n) with hX
  set Cu : ℝ := 4 * paperBandU n / Real.log 2 with hCuDef
  have hCuPos : 0 < Cu := by rw [hCuDef]; positivity
  have hMpos : 0 < paperBandLogY n := paperBandLogY_pos n
  -- `X * Cu + Cu ≤ exp (7M/8)`: four `exp (M/32)` factors times `exp (M/2)`
  have hprodCu : X * Cu + Cu ≤ Real.exp (7 * paperBandLogY n / 8) := by
    rw [hX, hCuDef, hsqrt, log_paperBandY]
    have hstep :
        Real.exp (decayExponent c n /
            paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n)) *
            (2 * K + Ks + 1) * (2 * paperBandLogY n) ^ 3 *
            Real.exp (paperBandLogY n / 2) * (4 * paperBandU n / Real.log 2) ≤
          Real.exp (paperBandLogY n / 32) * Real.exp (paperBandLogY n / 32) *
            Real.exp (paperBandLogY n / 32) * Real.exp (paperBandLogY n / 2) *
            Real.exp (paperBandLogY n / 32) := by
      gcongr
    have hcollapse : Real.exp (paperBandLogY n / 32) * Real.exp (paperBandLogY n / 32) *
          Real.exp (paperBandLogY n / 32) * Real.exp (paperBandLogY n / 2) *
          Real.exp (paperBandLogY n / 32) = Real.exp (5 * paperBandLogY n / 8) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hsum : Real.exp (5 * paperBandLogY n / 8) +
        Real.exp (paperBandLogY n / 32) ≤ Real.exp (7 * paperBandLogY n / 8) := by
      have h1 : Real.exp (paperBandLogY n / 32) ≤ Real.exp (5 * paperBandLogY n / 8) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hMpos]
      have h2 : Real.exp (5 * paperBandLogY n / 8) +
          Real.exp (5 * paperBandLogY n / 8) ≤ Real.exp (7 * paperBandLogY n / 8) := by
        have htwoM : (2 : ℝ) ≤ Real.exp (paperBandLogY n / 4) := htwoBigN
        calc
          Real.exp (5 * paperBandLogY n / 8) + Real.exp (5 * paperBandLogY n / 8) =
              2 * Real.exp (5 * paperBandLogY n / 8) := by ring
          _ ≤ Real.exp (paperBandLogY n / 4) * Real.exp (5 * paperBandLogY n / 8) :=
            mul_le_mul_of_nonneg_right htwoM (Real.exp_pos _).le
          _ = Real.exp (7 * paperBandLogY n / 8) := by
            rw [← Real.exp_add]
            congr 1
            ring
      linarith
    calc
      Real.exp (decayExponent c n /
            paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n)) *
            (2 * K + Ks + 1) * (2 * paperBandLogY n) ^ 3 *
            Real.exp (paperBandLogY n / 2) * (4 * paperBandU n / Real.log 2) +
            4 * paperBandU n / Real.log 2
          ≤ Real.exp (5 * paperBandLogY n / 8) + Real.exp (paperBandLogY n / 32) := by
        rw [hcollapse] at hstep
        linarith [hstep, hCuN]
      _ ≤ Real.exp (7 * paperBandLogY n / 8) := hsum
  -- divide by `Cu`
  have hstep2 : X + 1 ≤ Real.exp (7 * paperBandLogY n / 8) / Cu := by
    have hdiv := div_le_div_of_nonneg_right hprodCu hCuPos.le
    have heq : (X * Cu + Cu) / Cu = X + 1 := by
      field_simp [hCuPos.ne']
    rwa [heq] at hdiv
  have hfinal : X + 1 ≤
      Real.log 2 / (4 * paperBandU n) * Real.exp (7 * paperBandLogY n / 8) := by
    refine hstep2.trans (le_of_eq ?_)
    rw [hCuDef]
    have hupos' : paperBandU n ≠ 0 := hupos.ne'
    field_simp [hupos', hlog2pos.ne']
  calc
    X + 1 ≤ Real.log 2 / (4 * paperBandU n) * Real.exp (7 * paperBandLogY n / 8) := hfinal
    _ ≤ paperBandDelta 1 (paperBandK n) *
        (paperBandP (paperBandX n) (paperBandK n) *
          Real.exp (-(paperBandH (paperBandY n)
            (paperBandP (paperBandX n) (paperBandK n)) / 4))) := hbot

/-! ## 7. The core, width, and scale inequality at the numeric parameters -/

theorem eventually_paperBandL_big :
    ∀ᶠ n : ℕ in atTop,
      4 * Real.log 2 * (Real.log (paperBandU n) + 2) ≤ paperBandLogX n := by
  have hScale3 : ∀ᶠ n : ℕ in atTop,
      paperBandU n ≤ paperBandLogY n / (16 * Real.log 2) := by
    have h := eventually_scale_le_const_mul_paperD (C := 1 / (16 * Real.log 2)) (by positivity)
    simpa [paperBandU, paperBandLogY, paperD, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using h
  filter_upwards [hScale3, eventually_paperBandU_ge_two,
    eventually_log_paperBandU_le_self] with n hscale htwo hlogle
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMpos : 0 < paperBandLogY n := paperBandLogY_pos n
  have hu1 : 1 ≤ paperBandU n := by linarith
  have h1 : Real.log (paperBandU n) + 2 ≤ 3 * paperBandU n := by nlinarith
  have h2 : 4 * Real.log 2 * (Real.log (paperBandU n) + 2) ≤
      12 * Real.log 2 * paperBandU n := by
    nlinarith [h1, hlog2pos.le]
  have h3 : 12 * Real.log 2 * paperBandU n ≤ paperBandLogY n := by
    have h := (le_div_iff₀ (by positivity : 0 < 16 * Real.log 2)).mp hscale
    nlinarith [h]
  have h4 : paperBandLogY n ≤ paperBandLogX n := by
    unfold paperBandLogX
    nlinarith [hMpos, hu1]
  linarith

theorem eventually_paperBandK_pos : ∀ᶠ n : ℕ in atTop, 0 < paperBandK n := by
  filter_upwards [eventually_paperBandU_pos, eventually_paperBandK_bounds] with n hu hkb
  obtain ⟨huk, _, _⟩ := hkb
  exact Nat.cast_pos.mp (lt_of_lt_of_le hu huk)

theorem eventually_paperBandJLower_pos :
    ∀ᶠ n : ℕ in atTop,
      0 < paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n) := by
  filter_upwards [eventually_paperBandU_pos, eventually_log_paperBandU_ge_two,
    eventually_paperBandK_bounds, eventually_paperBandL_big] with n hu hlog hkb hLbig
  obtain ⟨_, hklo, _⟩ := hkb
  have hJ := paperBandJLower_lower (n := n) hu hlog hklo hLbig
  have hLpos : 0 < paperBandLogX n := by
    unfold paperBandLogX
    exact mul_pos (paperBandLogY_pos n) hu
  exact lt_of_lt_of_le (by positivity) hJ

theorem eventually_decay_nonneg {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ decayExponent c n := by
  filter_upwards [eventually_paperBandU_pos] with n hu
  unfold decayExponent paperD
  positivity

theorem eventually_paperBandY_gt_one : ∀ᶠ n : ℕ in atTop, 1 < paperBandY n := by
  filter_upwards [eventually_const_le_paperBandLogY (C := 1)] with n hM
  unfold paperBandY
  exact Real.one_lt_exp_iff.mpr (by linarith)

theorem eventually_two_log_paperBandY_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ 2 * Real.log (paperBandY n) := by
  filter_upwards [eventually_const_le_paperBandLogY (C := 1)] with n hM
  rw [log_paperBandY]
  linarith

theorem eventually_log_factor_q {q : ℕ} (hq : 1 ≤ q) :
    ∀ᶠ n : ℕ in atTop,
      1 + Real.log (3 * (q : ℝ) * paperBandY n) ≤ 2 * Real.log (paperBandY n) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  have h := eventually_const_le_paperBandLogY (C := 1 + Real.log (3 * (q : ℝ)))
  filter_upwards [h] with n hM
  have hypos : 0 < paperBandY n := paperBandY_pos n
  have h3q : (0 : ℝ) < 3 * (q : ℝ) := by positivity
  rw [Real.log_mul h3q.ne' hypos.ne', log_paperBandY]
  linarith

theorem eventually_log_factor_three :
    ∀ᶠ n : ℕ in atTop,
      1 + Real.log (3 * paperBandY n) ≤ 2 * Real.log (paperBandY n) := by
  have h := eventually_const_le_paperBandLogY (C := 1 + Real.log 3)
  filter_upwards [h] with n hM
  have hypos : 0 < paperBandY n := paperBandY_pos n
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hypos.ne', log_paperBandY]
  linarith

theorem eventually_paperBandP_le_Y :
    ∀ᶠ n : ℕ in atTop,
      paperBandP (paperBandX n) (paperBandK n) ≤ paperBandY n := by
  filter_upwards [eventually_paperBandU_pos, eventually_paperBandK_bounds] with n hu hkb
  obtain ⟨huk, _, _⟩ := hkb
  have hkpos : 0 < (paperBandK n : ℝ) := lt_of_lt_of_le hu huk
  rw [paperBandP_paperBandX, paperBandY]
  apply Real.exp_le_exp.mpr
  show paperBandLogX n / (paperBandK n : ℝ) ≤ paperBandLogY n
  rw [div_le_iff₀ hkpos]
  have hMpos : 0 < paperBandLogY n := paperBandLogY_pos n
  unfold paperBandLogX
  nlinarith [huk, hMpos]

/-- **The floor-free core at the paper's numeric parameters.** -/
theorem eventually_paperBandFloorFreeCore
    {K Ks c : ℝ} (hK : 0 ≤ K) (hKs : 0 ≤ Ks) {q : ℕ} (hq : 1 ≤ q) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      PaperBandFloorFreeCore K Ks c q n (paperBandX n) (paperBandY n) 1 (paperBandK n) := by
  have hgap := eventually_paperBandLogGap (K := K) (Ks := Ks) (c := c) hK hKs hc
  have hY := eventually_paperBandY_gt_one
  have h2L := eventually_two_log_paperBandY_ge_one
  have hJpos := eventually_paperBandJLower_pos
  have hdec := eventually_decay_nonneg hc
  have hlogq := eventually_log_factor_q hq
  have hlogs := eventually_log_factor_three
  filter_upwards [hgap, hY, h2L, hJpos, hdec, hlogq, hlogs] with n hg hy h2l hj hd hlq hls
  have hE1 : 1 ≤ Real.exp (decayExponent c n /
      paperBandJLower (paperBandY n) (paperBandX n) 1 (paperBandK n)) := by
    apply Real.one_le_exp
    exact div_nonneg hd hj.le
  exact paperBandFloorFreeCore_of_logGap hK hKs hq hy h2l hE1 hlq hls hg

/-- The core's residual width `δ * (P exp (-H/4)) - 1` is strictly positive. -/
theorem paperBandFloorFreeCore_width_pos
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hK : 0 < K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hy : 1 < y)
    (h : PaperBandFloorFreeCore K Ks c q n x y lam k) :
    0 < paperBandDelta lam k *
      (paperBandP x k * Real.exp (-(paperBandH y (paperBandP x k) / 4))) - 1 := by
  unfold PaperBandFloorFreeCore at h
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hbase : 0 < 1 + Real.log (3 * (q : ℝ) * y) := by
    have h3 : (1 : ℝ) ≤ 3 * (q : ℝ) * y := by nlinarith [hq1, hy0.le]
    have hl : 0 ≤ Real.log (3 * (q : ℝ) * y) := Real.log_nonneg h3
    linarith
  have hmain : 0 < Real.exp (decayExponent c n /
        paperBandJLower y x lam k) * (2 * K) *
        (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y := by
    have hE : 0 < Real.exp (decayExponent c n / paperBandJLower y x lam k) := Real.exp_pos _
    have hsq : 0 < (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 := pow_pos hbase 2
    have h2K : 0 < 2 * K := by positivity
    positivity
  have hsupply : 0 ≤ Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y := by positivity
  linarith [h]

/-- **The residual width is eventually strictly positive at the numeric
parameters.** -/
theorem eventually_paperBandWidth_pos
    {K Ks c : ℝ} (hK : 0 < K) (hKs : 0 ≤ Ks) {q : ℕ} (hq : 1 ≤ q) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      0 < paperBandDelta 1 (paperBandK n) *
        (paperBandP (paperBandX n) (paperBandK n) *
          Real.exp (-(paperBandH (paperBandY n)
            (paperBandP (paperBandX n) (paperBandK n)) / 4))) - 1 := by
  filter_upwards [eventually_paperBandFloorFreeCore hK.le hKs hq hc,
    eventually_paperBandY_gt_one] with n hcore hy
  exact paperBandFloorFreeCore_width_pos hK hKs hq hy hcore

/-- **The paper's scale inequality eventually holds at the numeric
parameters.** -/
theorem eventually_paperBandScaleInequality
    {K Ks c : ℝ} (hK : 0 ≤ K) (hKs : 0 ≤ Ks) {q : ℕ} (hq : 1 ≤ q) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      PaperBandScaleInequality K Ks c q n
        (paperBandJ (paperBandY n) (paperBandP (paperBandX n) (paperBandK n)) 1
          (paperBandK n))
        (paperBandP (paperBandX n) (paperBandK n))
        (paperBandDelta 1 (paperBandK n)) (paperBandY n) := by
  have hcore := eventually_paperBandFloorFreeCore (K := K) (Ks := Ks) (c := c) hK hKs hq hc
  filter_upwards [hcore, eventually_paperBandP_le_Y, eventually_paperBandJLower_pos,
    eventually_decay_nonneg hc, eventually_paperBandY_gt_one,
    eventually_paperBandK_pos] with n hc' hPle hJpos hdec hy hk
  exact paperBandScaleInequality_of_floorFreeCore (paperBandX_pos n) zero_lt_one hk
    hPle hK hy.le hdec hJpos hc'

/-- The eventual statement packaged with an explicit threshold `N`. -/
theorem exists_threshold_paperBandFloorFreeCore
    {K Ks c : ℝ} (hK : 0 ≤ K) (hKs : 0 ≤ Ks) {q : ℕ} (hq : 1 ≤ q) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N,
      PaperBandFloorFreeCore K Ks c q n (paperBandX n) (paperBandY n) 1 (paperBandK n) :=
  Filter.eventually_atTop.mp
    (eventually_paperBandFloorFreeCore hK hKs hq hc)

/-! ## Axiom audit -/

#print axioms paperBandFloorFreeCore_of_logGap
#print axioms paperBandJLower_lower
#print axioms paperBandExponent_le
#print axioms paperBandBottom_lower
#print axioms eventually_paperBandLogGap
#print axioms eventually_paperBandFloorFreeCore
#print axioms exists_threshold_paperBandFloorFreeCore
#print axioms paperBandFloorFreeCore_width_pos
#print axioms eventually_paperBandWidth_pos
#print axioms eventually_paperBandScaleInequality

end

end Cogentic.RandomizedL20_2BandNumeric
