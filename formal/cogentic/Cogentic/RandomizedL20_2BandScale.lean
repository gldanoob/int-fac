import Cogentic.RandomizedL20_2ScalarWidth

set_option linter.style.haveILetI false

/-!
# L20.2: the paper's band scale inequality with the floor removed

`Cogentic.RandomizedL20_2ScalarWidth` reduced the L20.2 character decay to the
single scale inequality

```
exp (decayExponent / J) * 2K (1 + log (3qy))² sqrt y log y
  + Ks (1 + log (3y))² sqrt y
  ≤ δ * paperBandBottom P δ J - 1 ,
```

where the paper's parameters are

```
δ = log (1 + λ) / (2k) ,   P = x^(1/k) ,
H = log (y / P) ,          J = floor (H / (4δ)) .
```

This file removes the last trace of the bin index: the floor defining `J` and
the exponential endpoint `paperBandBottom P δ J = P exp (-δJ)`.

There are two elementary monotonicity facts behind the reduction.

* Since `J = floor (H / (4δ))`, one has `δJ ≤ H / 4`, hence
  `paperBandBottom P δ J = P exp (-δJ) ≥ P exp (-H/4)`.  This is
  `paperBandBottom_ge_exp`; it replaces the exact bottom endpoint by the
  closed-form lower bound `P exp (-H/4) = P^(5/4) y^(-1/4)`
  (`paperBandP_exp_neg_H_eq_rpow`).
* Since `J > H / (4δ) - 1`, for nonnegative `decayExponent` the exponential
  factor is at most `exp (decayExponent / (H/(4δ) - 1))`.

Consequently `PaperBandScaleInequality` at the paper's parameters follows from
`PaperBandFloorFreeCore`, an inequality whose only quantities are `x`, `k`,
`λ`, `y` (and the fixed envelope data `K, Ks, c, q, n`):

```
exp (decayExponent / (log (y / x^(1/k)) / (4 δ) - 1))
    * 2K (1 + log (3qy))² sqrt y log y
  + Ks (1 + log (3y))² sqrt y
  ≤ δ * (x^(1/k) * exp (-(log (y / x^(1/k)) / 4))) - 1 .
```

`paperBandScaleInequality_of_floorFreeCore` is the reduction; the raw
`x, k, λ, y` form is `paperBandScaleInequality_of_rawScalar`.  Dropping the
`1/J` inside the exponential altogether (using only `J ≥ 1`) gives the weaker
`PaperBandSimpleCore`; `paperBandScaleInequality_of_simpleCore` records it.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no width is set
to zero: the `- 1` floor loss is retained throughout.
-/

namespace Cogentic.RandomizedL20_2BandScale

open Filter Real
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Decay
open Cogentic.RandomizedL20_2Width
open Cogentic.RandomizedL20_2ScalarWidth
open Cogentic.Randomized

noncomputable section

/-! ## 1. The exact bottom endpoint and its closed-form lower bound -/

/-- The bottom endpoint written with a single exponential. -/
theorem paperBandBottom_eq_exp_mul (P δ : ℝ) (J : ℕ) :
    paperBandBottom P δ J = P * Real.exp (-(δ * (J : ℝ))) := by
  unfold paperBandBottom
  rw [show δ * (-(J : ℝ)) = -(δ * (J : ℝ)) by ring]

/-- **The floor gives `δJ ≤ H/4`, hence the exact bottom endpoint dominates
`P exp (-H/4)`.** -/
theorem paperBandBottom_ge_exp {P δ H : ℝ} {J : ℕ}
    (hP : 0 ≤ P) (hJδ : (J : ℝ) * δ ≤ H / 4) :
    P * Real.exp (-(H / 4)) ≤ paperBandBottom P δ J := by
  rw [paperBandBottom_eq_exp_mul]
  refine mul_le_mul_of_nonneg_left ?_ hP
  apply Real.exp_le_exp.mpr
  have h : δ * (J : ℝ) ≤ H / 4 := by
    rw [mul_comm]
    exact hJδ
  linarith

/-- The closed-form lower bound is the paper's geometric expression
`P^(5/4) y^(-1/4)`. -/
theorem paperBandP_exp_neg_H_eq_rpow {P y : ℝ} (hP : 0 < P) (hy : 0 < y) :
    P ^ (5 / 4 : ℝ) * y ^ (-(1 / 4) : ℝ) =
      P * Real.exp (-(paperBandH y P / 4)) := by
  have hyP : 0 < y / P := div_pos hy hP
  have hexp : Real.exp (-(paperBandH y P / 4)) = (y / P) ^ (-(1 / 4) : ℝ) := by
    unfold paperBandH
    rw [Real.rpow_def_of_pos hyP]
    congr 1
    ring
  rw [hexp]
  rw [Real.div_rpow hy.le hP.le, Real.rpow_neg hP.le, Real.rpow_neg hy.le]
  have hP54 : P ^ (5 / 4 : ℝ) = P * P ^ (1 / 4 : ℝ) := by
    have hadd := Real.rpow_add hP (1 : ℝ) (1 / 4 : ℝ)
    rw [Real.rpow_one] at hadd
    rw [show (5 : ℝ) / 4 = 1 + 1 / 4 by norm_num]
    exact hadd
  rw [hP54]
  field_simp

/-- **The exact paper bottom endpoint dominates `P^(5/4) y^(-1/4)`.** -/
theorem paperBandBottom_ge_rpow {P y δ H : ℝ} {J : ℕ}
    (hP : 0 < P) (hy : 0 < y) (hH : H = paperBandH y P)
    (hJδ : (J : ℝ) * δ ≤ H / 4) :
    P ^ (5 / 4 : ℝ) * y ^ (-(1 / 4) : ℝ) ≤ paperBandBottom P δ J := by
  subst hH
  rw [paperBandP_exp_neg_H_eq_rpow hP hy]
  exact paperBandBottom_ge_exp hP.le hJδ

/-! ## 2. The gap core: the floor-free bottom, the paper's `J` still in the
exponential -/

/-- The scale inequality with the exact bottom endpoint replaced by the
closed-form bound `P exp (-H/4)`.  The bin count `J` is still the paper's
`floor (H/(4δ))`; only the endpoint has been simplified. -/
def PaperBandGapCore (K Ks c : ℝ) (q n : ℕ) (x y lam : ℝ) (k : ℕ) : Prop :=
  Real.exp (decayExponent c n / (paperBandJ y (paperBandP x k) lam k : ℝ)) *
      (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
    Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
      paperBandDelta lam k *
        (paperBandP x k * Real.exp (-(paperBandH y (paperBandP x k) / 4))) - 1

/-- **The gap core implies the paper's scale inequality.**  The only geometry
used is `δJ ≤ H/4`, i.e. `paperBandJ_mul_delta_le`. -/
theorem paperBandScaleInequality_of_gapCore
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hx : 0 < x) (hlam : 0 < lam) (hk : 0 < k) (hPle : paperBandP x k ≤ y)
    (h : PaperBandGapCore K Ks c q n x y lam k) :
    PaperBandScaleInequality K Ks c q n
      (paperBandJ y (paperBandP x k) lam k) (paperBandP x k) (paperBandDelta lam k) y := by
  unfold PaperBandGapCore at h
  unfold PaperBandScaleInequality
  have hP : 0 < paperBandP x k := paperBandP_pos hx k
  have hδ : 0 < paperBandDelta lam k := paperBandDelta_pos hlam hk
  have hH : 0 ≤ paperBandH y (paperBandP x k) := by
    unfold paperBandH
    apply Real.log_nonneg
    rw [le_div_iff₀ hP]
    simpa using hPle
  have hJδ : ((paperBandJ y (paperBandP x k) lam k : ℕ) : ℝ) * paperBandDelta lam k ≤
      paperBandH y (paperBandP x k) / 4 :=
    paperBandJ_mul_delta_le hH hδ
  have hbot :
      paperBandP x k * Real.exp (-(paperBandH y (paperBandP x k) / 4)) ≤
        paperBandBottom (paperBandP x k) (paperBandDelta lam k)
          (paperBandJ y (paperBandP x k) lam k) :=
    paperBandBottom_ge_exp (P := paperBandP x k) (δ := paperBandDelta lam k)
      (H := paperBandH y (paperBandP x k)) hP.le hJδ
  have hmono :
      paperBandDelta lam k *
          (paperBandP x k * Real.exp (-(paperBandH y (paperBandP x k) / 4))) - 1 ≤
        paperBandDelta lam k *
          paperBandBottom (paperBandP x k) (paperBandDelta lam k)
            (paperBandJ y (paperBandP x k) lam k) - 1 := by
    have := mul_le_mul_of_nonneg_left hbot hδ.le
    linarith
  linarith

/-! ## 3. Removing the floor from the exponential factor -/

/-- The floor-free lower bound `H/(4δ) - 1` for the paper's bin count. -/
noncomputable def paperBandJLower (y x lam : ℝ) (k : ℕ) : ℝ :=
  paperBandH y (paperBandP x k) / (4 * paperBandDelta lam k) - 1

/-- The paper's `J` is strictly larger than `H/(4δ) - 1`. -/
theorem paperBandJLower_lt_paperBandJ {y x lam : ℝ} {k : ℕ} :
    paperBandJLower y x lam k < (paperBandJ y (paperBandP x k) lam k : ℝ) := by
  unfold paperBandJLower paperBandJ
  have := Nat.lt_floor_add_one (paperBandH y (paperBandP x k) / (4 * paperBandDelta lam k))
  linarith

/-- **The smallest explicit scalar inequality in `x, k, λ, y`.**  It is the
paper's scale inequality with `J` replaced by its floor-free lower bound
`H/(4δ) - 1` and the exact bottom endpoint replaced by `P exp (-H/4)`.
No floor appears. -/
def PaperBandFloorFreeCore (K Ks c : ℝ) (q n : ℕ) (x y lam : ℝ) (k : ℕ) : Prop :=
  Real.exp (decayExponent c n / paperBandJLower y x lam k) *
      (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
    Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
      paperBandDelta lam k *
        (paperBandP x k * Real.exp (-(paperBandH y (paperBandP x k) / 4))) - 1

/-- **Removing the floor from the exponential factor.**  Since
`J > H/(4δ) - 1 > 0` and `decayExponent ≥ 0`, replacing `J` by
`H/(4δ) - 1` only increases the exponential factor. -/
theorem paperBandGapCore_of_floorFreeCore
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hK : 0 ≤ K) (hy : 1 ≤ y) (hdecay : 0 ≤ decayExponent c n)
    (hJpos : 0 < paperBandJLower y x lam k)
    (h : PaperBandFloorFreeCore K Ks c q n x y lam k) :
    PaperBandGapCore K Ks c q n x y lam k := by
  unfold PaperBandFloorFreeCore at h
  unfold PaperBandGapCore
  have hJlow := paperBandJLower_lt_paperBandJ (y := y) (x := x) (lam := lam) (k := k)
  have hexpArg :
      decayExponent c n / (paperBandJ y (paperBandP x k) lam k : ℝ) ≤
        decayExponent c n / paperBandJLower y x lam k :=
    div_le_div_of_nonneg_left hdecay hJpos hJlow.le
  have hexp :
      Real.exp (decayExponent c n / (paperBandJ y (paperBandP x k) lam k : ℝ)) ≤
        Real.exp (decayExponent c n / paperBandJLower y x lam k) :=
    Real.exp_le_exp.mpr hexpArg
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hcoeff :
      0 ≤ (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y := by
    positivity
  have hmul :
      Real.exp (decayExponent c n / (paperBandJ y (paperBandP x k) lam k : ℝ)) *
          ((2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y) ≤
        Real.exp (decayExponent c n / paperBandJLower y x lam k) *
          ((2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y) :=
    mul_le_mul_of_nonneg_right hexp hcoeff
  linarith

/-- **The paper's scale inequality from the smallest floor-free scalar
inequality `PaperBandFloorFreeCore`.** -/
theorem paperBandScaleInequality_of_floorFreeCore
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hx : 0 < x) (hlam : 0 < lam) (hk : 0 < k) (hPle : paperBandP x k ≤ y)
    (hK : 0 ≤ K) (hy : 1 ≤ y) (hdecay : 0 ≤ decayExponent c n)
    (hJpos : 0 < paperBandJLower y x lam k)
    (h : PaperBandFloorFreeCore K Ks c q n x y lam k) :
    PaperBandScaleInequality K Ks c q n
      (paperBandJ y (paperBandP x k) lam k) (paperBandP x k) (paperBandDelta lam k) y :=
  paperBandScaleInequality_of_gapCore hx hlam hk hPle
    (paperBandGapCore_of_floorFreeCore hK hy hdecay hJpos h)

/-! ## 4. The coarser floor-free core (only `J ≥ 1`) -/

/-- A coarser but simpler floor-free core: the exponential is bounded by
`exp (decayExponent)`, which uses only `J ≥ 1`. -/
def PaperBandSimpleCore (K Ks c : ℝ) (q n : ℕ) (x y lam : ℝ) (k : ℕ) : Prop :=
  Real.exp (decayExponent c n) *
      (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
    Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
      paperBandDelta lam k *
        (paperBandP x k * Real.exp (-(paperBandH y (paperBandP x k) / 4))) - 1

/-- The bin count is at least one once `H/(4δ) ≥ 1`. -/
theorem one_le_paperBandJ_of_one_le {y P lam : ℝ} {k : ℕ}
    (h : (1 : ℝ) ≤ paperBandH y P / (4 * paperBandDelta lam k)) :
    1 ≤ paperBandJ y P lam k := by
  unfold paperBandJ
  exact (Nat.one_le_floor_iff _).mpr h

/-- **The coarse floor-free core implies the gap core.** -/
theorem paperBandGapCore_of_simpleCore
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hK : 0 ≤ K) (hy : 1 ≤ y) (hdecay : 0 ≤ decayExponent c n)
    (hJ1 : 1 ≤ paperBandJ y (paperBandP x k) lam k)
    (h : PaperBandSimpleCore K Ks c q n x y lam k) :
    PaperBandGapCore K Ks c q n x y lam k := by
  unfold PaperBandSimpleCore at h
  unfold PaperBandGapCore
  have hJ1R : (1 : ℝ) ≤ (paperBandJ y (paperBandP x k) lam k : ℝ) := by
    exact_mod_cast hJ1
  have hexpArg :
      decayExponent c n / (paperBandJ y (paperBandP x k) lam k : ℝ) ≤
        decayExponent c n / (1 : ℝ) :=
    div_le_div_of_nonneg_left hdecay zero_lt_one hJ1R
  have hexpArg' :
      decayExponent c n / (paperBandJ y (paperBandP x k) lam k : ℝ) ≤
        decayExponent c n := by
    simpa using hexpArg
  have hexp :
      Real.exp (decayExponent c n / (paperBandJ y (paperBandP x k) lam k : ℝ)) ≤
        Real.exp (decayExponent c n) :=
    Real.exp_le_exp.mpr hexpArg'
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hcoeff :
      0 ≤ (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y := by
    positivity
  have hmul :
      Real.exp (decayExponent c n / (paperBandJ y (paperBandP x k) lam k : ℝ)) *
          ((2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y) ≤
        Real.exp (decayExponent c n) *
          ((2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y) :=
    mul_le_mul_of_nonneg_right hexp hcoeff
  linarith

/-- **The paper's scale inequality from the coarse floor-free core.** -/
theorem paperBandScaleInequality_of_simpleCore
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hx : 0 < x) (hlam : 0 < lam) (hk : 0 < k) (hPle : paperBandP x k ≤ y)
    (hK : 0 ≤ K) (hy : 1 ≤ y) (hdecay : 0 ≤ decayExponent c n)
    (hH4 : (1 : ℝ) ≤ paperBandH y (paperBandP x k) / (4 * paperBandDelta lam k))
    (h : PaperBandSimpleCore K Ks c q n x y lam k) :
    PaperBandScaleInequality K Ks c q n
      (paperBandJ y (paperBandP x k) lam k) (paperBandP x k) (paperBandDelta lam k) y :=
  paperBandScaleInequality_of_gapCore hx hlam hk hPle
    (paperBandGapCore_of_simpleCore hK hy hdecay
      (one_le_paperBandJ_of_one_le hH4) h)

/-! ## 5. The raw `x, k, λ, y` form -/

/-- **The smallest scalar inequality in the raw paper parameters.**  This is
`PaperBandFloorFreeCore` with every paper quantity written out:
`δ = log (1 + λ)/(2k)`, `P = x^(1/k)` and `H = log (y / P)`. -/
theorem paperBandScaleInequality_of_rawScalar
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hx : 0 < x) (hlam : 0 < lam) (hk : 0 < k) (hPle : paperBandP x k ≤ y)
    (hK : 0 ≤ K) (hy : 1 ≤ y) (hdecay : 0 ≤ decayExponent c n)
    (hJpos : 0 < Real.log (y / x ^ (1 / (k : ℝ))) /
        (4 * (Real.log (1 + lam) / (2 * (k : ℝ)))) - 1)
    (h :
      Real.exp (decayExponent c n /
          (Real.log (y / x ^ (1 / (k : ℝ))) /
            (4 * (Real.log (1 + lam) / (2 * (k : ℝ)))) - 1)) *
          (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
        Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
        (Real.log (1 + lam) / (2 * (k : ℝ))) *
          (x ^ (1 / (k : ℝ)) *
            Real.exp (-(Real.log (y / x ^ (1 / (k : ℝ))) / 4))) - 1) :
    PaperBandScaleInequality K Ks c q n
      (paperBandJ y (paperBandP x k) lam k) (paperBandP x k) (paperBandDelta lam k) y := by
  have hcore : PaperBandFloorFreeCore K Ks c q n x y lam k := by
    simpa [PaperBandFloorFreeCore, paperBandJLower, paperBandDelta, paperBandP, paperBandH]
      using h
  have hJpos' : 0 < paperBandJLower y x lam k := by
    simpa [paperBandJLower, paperBandDelta, paperBandP, paperBandH] using hJpos
  exact paperBandScaleInequality_of_floorFreeCore hx hlam hk hPle hK hy hdecay hJpos' hcore

/-- **The coarser raw `x, k, λ, y` form** (only `J ≥ 1` is used). -/
theorem paperBandScaleInequality_of_rawSimpleScalar
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (hx : 0 < x) (hlam : 0 < lam) (hk : 0 < k) (hPle : paperBandP x k ≤ y)
    (hK : 0 ≤ K) (hy : 1 ≤ y) (hdecay : 0 ≤ decayExponent c n)
    (hH4 : (1 : ℝ) ≤ Real.log (y / x ^ (1 / (k : ℝ))) /
        (4 * (Real.log (1 + lam) / (2 * (k : ℝ)))))
    (h :
      Real.exp (decayExponent c n) *
          (2 * K) * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
        Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
        (Real.log (1 + lam) / (2 * (k : ℝ))) *
          (x ^ (1 / (k : ℝ)) *
            Real.exp (-(Real.log (y / x ^ (1 / (k : ℝ))) / 4))) - 1) :
    PaperBandScaleInequality K Ks c q n
      (paperBandJ y (paperBandP x k) lam k) (paperBandP x k) (paperBandDelta lam k) y := by
  have hcore : PaperBandSimpleCore K Ks c q n x y lam k := by
    simpa [PaperBandSimpleCore, paperBandDelta, paperBandP, paperBandH] using h
  have hH4' : (1 : ℝ) ≤ paperBandH y (paperBandP x k) / (4 * paperBandDelta lam k) := by
    simpa [paperBandDelta, paperBandP, paperBandH] using hH4
  exact paperBandScaleInequality_of_simpleCore hx hlam hk hPle hK hy hdecay hH4' hcore

/-! ## 6. Capstone: the paper's width core from the floor-free scalar -/

/-- **The paper's integer-bin width core from `PaperBandFloorFreeCore`.**  The
centred-bin geometry and the top-endpoint check are supplied by
`primeBinEnvelopeWidthCore_of_paperParameters`; this theorem only feeds it the
reduced scalar inequality. -/
theorem primeBinEnvelopeWidthCore_of_floorFreeCore
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {a k : ℕ}
    (hx : 0 < x) (hlam : 0 < lam) (hk : 0 < k) (hPle : paperBandP x k ≤ y)
    (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hy : 1 ≤ y)
    (hdecay : 0 ≤ decayExponent c n)
    (ha : a ≤ k * paperBandJ y (paperBandP x k) lam k)
    (hB1 : ∀ j < paperBandJ y (paperBandP x k) lam k,
      (1 : ℝ) ≤
        paperBinUpper (paperBandP x k) (paperBandDelta lam k) a k j)
    (hJpos : 0 < paperBandJLower y x lam k)
    (h : PaperBandFloorFreeCore K Ks c q n x y lam k) :
    PrimeBinEnvelopeWidthCore
      (ι := Fin (paperBandJ y (paperBandP x k) lam k)) K Ks c q
      (fun j => paperBinLower (paperBandP x k) (paperBandDelta lam k) a k j)
      (fun j => paperBinUpper (paperBandP x k) (paperBandDelta lam k) a k j) n :=
  primeBinEnvelopeWidthCore_of_paperParameters hx hlam hk hPle hK hKs hq ha hB1
    (paperBandScaleInequality_of_floorFreeCore hx hlam hk hPle hK hy hdecay hJpos h)

/-! ## Axiom audit -/

#print axioms paperBandBottom_eq_exp_mul
#print axioms paperBandBottom_ge_exp
#print axioms paperBandP_exp_neg_H_eq_rpow
#print axioms paperBandBottom_ge_rpow
#print axioms paperBandScaleInequality_of_gapCore
#print axioms paperBandJLower_lt_paperBandJ
#print axioms paperBandGapCore_of_floorFreeCore
#print axioms paperBandScaleInequality_of_floorFreeCore
#print axioms one_le_paperBandJ_of_one_le
#print axioms paperBandGapCore_of_simpleCore
#print axioms paperBandScaleInequality_of_simpleCore
#print axioms paperBandScaleInequality_of_rawScalar
#print axioms paperBandScaleInequality_of_rawSimpleScalar
#print axioms primeBinEnvelopeWidthCore_of_floorFreeCore

end

end Cogentic.RandomizedL20_2BandScale
