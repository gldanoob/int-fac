import Cogentic.RandomizedL20_2SmoothMass

set_option linter.style.haveILetI false

/-!
# L20.2: the paper-regime smooth reciprocal mass

`Cogentic.RandomizedL20_2SmoothMass` proves `SmoothNumberMassLogLower` in the
two elementary regimes `y = X` (self-smooth) and `y = X / 2`, and reduces a
general window count or density estimate to an explicit arithmetic budget.
`Cogentic.RandomizedL20_2SmoothLower` proves the smooth-number count input for
the two-power pair.

This file supplies the remaining *paper-regime* pair.  The manuscript's smooth
product set has a top cofactor of size `X` and a local prime cutoff `y`, with

`u = log X / log y`

bounded (the paper's fixed-power regime).  We take the explicit instance
`u = 4/3`, i.e.

`y = X^(3/4)`,

on the saddle scale

`X n = exp (max 16 (paperD n * scale n))`.

The clipping at `exp 16` only affects the finite initial segment where the
paper's `D log D` scale is below `16`; it makes the elementary interval count
uniform at every ledger index.

## What is proved

* `smoothNumberMassLogLower_of_powCutoff`: for any endpoint `X ≥ exp C` and
  cutoff `y = X^β` with `0 < β ≤ 1`, the mass `∑_{m ≤ X, P⁺(m) ≤ y} m^(-α)`
  obeys the saddle mean as soon as `η < β (1 - α)` and
  `log 2 ≤ (β (1 - α) - η) C`.  The proof uses only that every integer up to
  `y` is `y`-smooth, so the window count is at least `⌊y⌋ ≥ y/2`.
* `smoothNumberCountLower_of_powCutoff`: the same pair also gives
  `exp (c D log D) ≤ #smooth` for every `c < β`, by the same interval count.
* `smoothNumberMassLogLower_of_logScale` and
  `smoothNumberCountLower_of_logScale` phrase the paper-pair identification as
  the single explicit scale equality

  `log (y n) = β * log (X n)`.

  This is the smallest remaining identification: the paper only has to state
  the fixed ratio of the logarithmic cofactor and cutoff scales.
* `paperMassLogLower` and `paperMassCountLower` instantiate the pair
  `(paperMassX, paperMassY) = (exp (max 16 (D log D)), X^(3/4))` with
  `α = 1/2`, `η = 1/8`, and count constant `c = 1/2`.  Both the saddle mean and
  the saddle scale are then genuine inequalities on the actual
  `smoothNumberMass` and `smoothNumberCount`, with no term set to zero.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no mass is set to
zero.
-/

namespace Cogentic.RandomizedL20_2PaperMass

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Saddle
open Cogentic.RandomizedL20_2SmoothMass
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The fixed-power paper regime -/

/-- From `exp C ≤ X` and `log 2 ≤ β C`, with `0 < β`, the cutoff `X^β` is at
least two.  This is what makes the elementary interval count `⌊X^β⌋ ≥ X^β/2`
uniform down to the clipped initial segment. -/
theorem two_le_rpow_of_exp_le {X C β : ℝ} (_hXpos : 0 < X) (hβ0 : 0 < β)
    (hXc : Real.exp C ≤ X) (hlog : Real.log 2 ≤ β * C) :
    (2 : ℝ) ≤ X ^ β := by
  have hC : C ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos C) hXc
    rwa [Real.log_exp] at h
  have htwo : (2 : ℝ) ≤ Real.exp (β * C) := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (β * C) := Real.exp_le_exp.mpr hlog
  have hpow : Real.exp (β * C) ≤ X ^ β := by
    calc
      Real.exp (β * C) = Real.exp (C * β) := by rw [mul_comm]
      _ = (Real.exp C) ^ β := Real.exp_mul C β
      _ ≤ X ^ β := Real.rpow_le_rpow (Real.exp_pos C).le hXc hβ0.le
  exact htwo.trans hpow

/-- Half of a real at least two is at most its floor. -/
theorem half_le_floor {T : ℝ} (hT2 : 2 ≤ T) : T / 2 ≤ (⌊T⌋₊ : ℝ) := by
  have hlt := Nat.lt_floor_add_one T
  have hT1 : T / 2 ≤ T - 1 := by linarith
  linarith

/-- The initial interval up to `⌊X^β⌋` consists entirely of `X^β`-smooth
integers. -/
theorem smoothNumberSet_pow_Icc_subset {X : ℕ → ℝ} {β : ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (_hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Finset.Icc 1 ⌊(X n) ^ β⌋₊ ⊆
      smoothNumberSet X (fun m => (X m) ^ β) n := by
  intro m hm
  obtain ⟨hm1, hmT⟩ := Finset.mem_Icc.mp hm
  have hXpos : 0 < X n := by linarith
  have hTpos : 0 < (X n) ^ β := Real.rpow_pos_of_pos hXpos β
  have hTX : (X n) ^ β ≤ X n := by
    calc
      (X n) ^ β ≤ (X n) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hβ1
      _ = X n := Real.rpow_one _
  have hmT' : (m : ℝ) ≤ (X n) ^ β :=
    (Nat.cast_le.mpr hmT).trans (Nat.floor_le hTpos.le)
  have hmX : (m : ℝ) ≤ X n := hmT'.trans hTX
  rw [smoothNumberSet, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hm1, Nat.le_floor hmX⟩, ?_⟩
  intro p hp
  have hmpos : 0 < m := by omega
  have hp_le_m : p ≤ m := Nat.le_of_dvd hmpos (Nat.dvd_of_mem_primeFactors hp)
  exact (Nat.cast_le.mpr hp_le_m).trans hmT'

/-- The smooth count contains the interval up to `⌊X^β⌋`. -/
theorem smoothNumberCount_pow_ge_floor {X : ℕ → ℝ} {β : ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (⌊(X n) ^ β⌋₊ : ℝ) ≤
      smoothNumberCount X (fun m => (X m) ^ β) n := by
  have hsub := smoothNumberSet_pow_Icc_subset (X := X) (β := β) (n := n) hX hβ0 hβ1
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  unfold smoothNumberCount
  exact_mod_cast hcard

/-- The smooth window up to `X^β` contains the interval up to `⌊X^β⌋`. -/
theorem smoothNumberWindow_pow_Icc_subset {X : ℕ → ℝ} {β : ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Finset.Icc 1 ⌊(X n) ^ β⌋₊ ⊆
      smoothNumberWindow X (fun m => (X m) ^ β) (fun m => (X m) ^ β) n := by
  intro m hm
  have hmem := smoothNumberSet_pow_Icc_subset (X := X) (β := β) (n := n) hX hβ0 hβ1 hm
  have hXpos : 0 < X n := by linarith
  have hTpos : 0 < (X n) ^ β := Real.rpow_pos_of_pos hXpos β
  obtain ⟨hm1, hmT⟩ := Finset.mem_Icc.mp hm
  rw [smoothNumberWindow, Finset.mem_filter]
  exact ⟨hmem, (Nat.cast_le.mpr hmT).trans (Nat.floor_le hTpos.le)⟩

/-- The smooth-window count contains `⌊X^β⌋`. -/
theorem smoothNumberWindowCount_pow_ge_floor {X : ℕ → ℝ} {β : ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (⌊(X n) ^ β⌋₊ : ℝ) ≤
      smoothNumberWindowCount X (fun m => (X m) ^ β) (fun m => (X m) ^ β) n := by
  have hsub := smoothNumberWindow_pow_Icc_subset (X := X) (β := β) (n := n) hX hβ0 hβ1
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  unfold smoothNumberWindowCount
  exact_mod_cast hcard

/-- The smooth-window count is at least half of `X^β`. -/
theorem smoothNumberWindowCount_pow_ge_half {X : ℕ → ℝ} {β : ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hT2 : 2 ≤ (X n) ^ β) :
    (X n) ^ β / 2 ≤
      smoothNumberWindowCount X (fun m => (X m) ^ β) (fun m => (X m) ^ β) n := by
  have hhalf := half_le_floor hT2
  have hcard := smoothNumberWindowCount_pow_ge_floor (X := X) (β := β) (n := n) hX hβ0 hβ1
  linarith

/-- **The logarithmic mass bound in the fixed-power paper regime.**  The mass is
at least `X^(β(1-α)) / 2`, hence its logarithm is at least
`β (1 - α) log X - log 2`. -/
theorem log_smoothNumberMass_ge_pow {X : ℕ → ℝ} {β α : ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hα0 : 0 ≤ α)
    (hT2 : 2 ≤ (X n) ^ β) :
    β * (1 - α) * Real.log (X n) - Real.log 2 ≤
      Real.log (smoothNumberMass X (fun m => (X m) ^ β) (fun _ => α) n) := by
  have hXpos : 0 < X n := by linarith
  have hTpos : 0 < (X n) ^ β := Real.rpow_pos_of_pos hXpos β
  have hwinhalf := smoothNumberWindowCount_pow_ge_half (X := X) (β := β) (n := n)
    hX hβ0 hβ1 hT2
  have hwinpos : 0 < smoothNumberWindowCount X (fun m => (X m) ^ β)
      (fun m => (X m) ^ β) n := by linarith
  have hlogmass := log_smoothNumberMass_ge_log_windowCount_sub
    (X := X) (y := fun m => (X m) ^ β) (α := fun _ => α)
    (T := fun m => (X m) ^ β) (n := n) hTpos hα0 hwinpos
  have hlogwin : Real.log ((X n) ^ β / 2) ≤
      Real.log (smoothNumberWindowCount X (fun m => (X m) ^ β)
        (fun m => (X m) ^ β) n) :=
    Real.log_le_log (by positivity) hwinhalf
  have hlogT : Real.log ((X n) ^ β) = β * Real.log (X n) := Real.log_rpow hXpos β
  have hlogdiv : Real.log ((X n) ^ β / 2) = β * Real.log (X n) - Real.log 2 := by
    rw [Real.log_div hTpos.ne' (by norm_num : (2 : ℝ) ≠ 0), hlogT]
  have hlogwin' : β * Real.log (X n) - Real.log 2 ≤
      Real.log (smoothNumberWindowCount X (fun m => (X m) ^ β)
        (fun m => (X m) ^ β) n) := by
    rw [← hlogdiv]
    exact hlogwin
  rw [hlogT] at hlogmass
  nlinarith only [hlogwin', hlogmass]

/-- **`SmoothNumberMassLogLower` for the fixed-power paper pair.**  The cutoff
is `y = X^β` with `0 < β ≤ 1`, the Rankin exponent satisfies `α < β`, and the
saddle constant satisfies `η < β (1 - α)`.  The explicit scale lower bound
`log 2 ≤ (β (1 - α) - η) C` is the only remaining scalar condition. -/
theorem smoothNumberMassLogLower_of_powCutoff {X : ℕ → ℝ} {β α η C : ℝ}
    (hX : ∀ n, 1 ≤ X n)
    (hXc : ∀ n, Real.exp C ≤ X n)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hα0 : 0 ≤ α) (hη0 : 0 < η)
    (hηβ : η < β * (1 - α))
    (hC : Real.log 2 ≤ (β * (1 - α) - η) * C) :
    SmoothNumberMassLogLower X (fun m => (X m) ^ β) (fun _ => α)
      (smoothSaddleScale X (fun m => (X m) ^ β)) η := by
  refine ⟨hη0, fun n => ?_⟩
  have hXn : 1 ≤ X n := hX n
  have hXpos : 0 < X n := by linarith
  have hlogX : C ≤ Real.log (X n) := by
    have h := Real.log_le_log (Real.exp_pos C) (hXc n)
    rwa [Real.log_exp] at h
  have hcoefnonneg : 0 ≤ β * (1 - α) - η := by linarith
  have hcoefle : β * (1 - α) - η ≤ β := by
    have hβα : 0 ≤ β * α := mul_nonneg hβ0.le hα0
    nlinarith only [hβα, hη0.le]
  have hlog2βC : Real.log 2 ≤ β * C := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCpos : 0 < C := by
      by_contra h
      have hCnonpos : C ≤ 0 := le_of_not_gt h
      have : (β * (1 - α) - η) * C ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoefnonneg hCnonpos
      linarith
    exact hC.trans (mul_le_mul_of_nonneg_right hcoefle hCpos.le)
  have hT2 : 2 ≤ (X n) ^ β :=
    two_le_rpow_of_exp_le hXpos hβ0 (hXc n) hlog2βC
  have hlogmass := log_smoothNumberMass_ge_pow (X := X) (β := β) (α := α) (n := n)
    hXn hβ0 hβ1 hα0 hT2
  have hΛ : smoothSaddleScale X (fun m => (X m) ^ β) n ≤ Real.log (X n) := by
    unfold smoothSaddleScale
    exact Real.log_le_log (smoothNumberCount_pos hXn)
      (smoothNumberCount_le_endpoint hXn)
  have hbudget : Real.log 2 ≤ (β * (1 - α) - η) * Real.log (X n) :=
    hC.trans (mul_le_mul_of_nonneg_left hlogX hcoefnonneg)
  nlinarith only [hlogmass, hΛ, hbudget, hη0.le]

/-- **`SmoothNumberCountLower` for the fixed-power paper pair.**  The same
interval `[1, X^β]` gives `exp (c D log D) ≤ #smooth` whenever `c < β` and the
explicit scale bound `log 2 ≤ (β - c) C` holds. -/
theorem smoothNumberCountLower_of_powCutoff {X : ℕ → ℝ} {β c C : ℝ}
    (hX : ∀ n, 1 ≤ X n)
    (hH : ∀ n, paperD n * scale n ≤ Real.log (X n))
    (hXc : ∀ n, Real.exp C ≤ X n)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hc0 : 0 < c) (hcβ : c < β)
    (hC : Real.log 2 ≤ (β - c) * C) :
    SmoothNumberCountLower X (fun m => (X m) ^ β) c := by
  refine ⟨hc0, fun n => ?_⟩
  have hXn : 1 ≤ X n := hX n
  have hXpos : 0 < X n := by linarith
  have hlogX : C ≤ Real.log (X n) := by
    have h := Real.log_le_log (Real.exp_pos C) (hXc n)
    rwa [Real.log_exp] at h
  have hcoefpos : 0 < β - c := by linarith
  have hcoefle : β - c ≤ β := by linarith
  have hlog2βC : Real.log 2 ≤ β * C := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCpos : 0 < C := by
      by_contra h
      have hCnonpos : C ≤ 0 := le_of_not_gt h
      have : (β - c) * C ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcoefpos.le hCnonpos
      linarith
    exact hC.trans (mul_le_mul_of_nonneg_right hcoefle hCpos.le)
  have hT2 : 2 ≤ (X n) ^ β :=
    two_le_rpow_of_exp_le hXpos hβ0 (hXc n) hlog2βC
  have hfloor := smoothNumberCount_pow_ge_floor (X := X) (β := β) (n := n)
    hXn hβ0 hβ1
  have hhalf := half_le_floor hT2
  have hcountge : (X n) ^ β / 2 ≤
      smoothNumberCount X (fun m => (X m) ^ β) n := hhalf.trans hfloor
  have htwo : (2 : ℝ) ≤ (X n) ^ (β - c) := by
    have hlog : Real.log 2 ≤ (β - c) * Real.log (X n) :=
      hC.trans (mul_le_mul_of_nonneg_left hlogX hcoefpos.le)
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((β - c) * Real.log (X n)) := Real.exp_le_exp.mpr hlog
      _ = (X n) ^ (β - c) := by
        rw [Real.rpow_def_of_pos hXpos, mul_comm]
  have hsplit : (X n) ^ β = (X n) ^ (β - c) * (X n) ^ c := by
    rw [← Real.rpow_add hXpos]
    ring_nf
  have hpowc : (X n) ^ c = Real.exp (c * Real.log (X n)) := by
    rw [Real.rpow_def_of_pos hXpos, mul_comm]
  have hcge : Real.exp (c * Real.log (X n)) ≤ (X n) ^ β / 2 := by
    rw [← hpowc, hsplit]
    nlinarith only [htwo, Real.rpow_pos_of_pos hXpos c]
  have hexp_le : Real.exp (c * paperD n * scale n) ≤
      Real.exp (c * Real.log (X n)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hH n) hc0.le
    linarith only [h]
  exact hexp_le.trans (hcge.trans hcountge)

/-! ## 2. The paper-pair identification as one scale equality -/

/-- **The paper-pair identification for the mass.**  If the paper's pair
satisfies the single explicit logarithmic scale equality
`log (y n) = β log (X n)`, then it is the fixed-power pair and the mass bound
follows.  This is the smallest explicit identification: no separate smooth-count
or density estimate enters. -/
theorem smoothNumberMassLogLower_of_logScale {X y : ℕ → ℝ} {β α η C : ℝ}
    (hX : ∀ n, 1 ≤ X n)
    (hXc : ∀ n, Real.exp C ≤ X n)
    (hypos : ∀ n, 0 < y n)
    (hscale : ∀ n, Real.log (y n) = β * Real.log (X n))
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hα0 : 0 ≤ α) (hη0 : 0 < η)
    (hηβ : η < β * (1 - α))
    (hC : Real.log 2 ≤ (β * (1 - α) - η) * C) :
    SmoothNumberMassLogLower X y (fun _ => α)
      (smoothSaddleScale X y) η := by
  have hy_eq : y = fun n => (X n) ^ β := by
    funext n
    have hXpos : 0 < X n := by
      have := hX n
      linarith
    calc
      y n = Real.exp (Real.log (y n)) := (Real.exp_log (hypos n)).symm
      _ = Real.exp (β * Real.log (X n)) := by rw [hscale n]
      _ = (X n) ^ β := by rw [Real.rpow_def_of_pos hXpos, mul_comm]
  rw [hy_eq]
  exact smoothNumberMassLogLower_of_powCutoff hX hXc hβ0 hβ1 hα0 hη0 hηβ hC

/-- **The paper-pair identification for the count.**  The same scale equality
identifies the paper's cutoff with `X^β` and gives the saddle-scale count
lower bound. -/
theorem smoothNumberCountLower_of_logScale {X y : ℕ → ℝ} {β c C : ℝ}
    (hX : ∀ n, 1 ≤ X n)
    (hH : ∀ n, paperD n * scale n ≤ Real.log (X n))
    (hXc : ∀ n, Real.exp C ≤ X n)
    (hypos : ∀ n, 0 < y n)
    (hscale : ∀ n, Real.log (y n) = β * Real.log (X n))
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hc0 : 0 < c) (hcβ : c < β)
    (hC : Real.log 2 ≤ (β - c) * C) :
    SmoothNumberCountLower X y c := by
  have hy_eq : y = fun n => (X n) ^ β := by
    funext n
    have hXpos : 0 < X n := by
      have := hX n
      linarith
    calc
      y n = Real.exp (Real.log (y n)) := (Real.exp_log (hypos n)).symm
      _ = Real.exp (β * Real.log (X n)) := by rw [hscale n]
      _ = (X n) ^ β := by rw [Real.rpow_def_of_pos hXpos, mul_comm]
  rw [hy_eq]
  exact smoothNumberCountLower_of_powCutoff hX hH hXc hβ0 hβ1 hc0 hcβ hC

/-! ## 3. The manuscript-scale instantiation -/

/-- The explicit normalizer in the paper-regime endpoint. -/
def paperMassC : ℝ := 16

/-- The manuscript's common saddle scale `D log D = paperD n * scale n`. -/
def paperMassH (n : ℕ) : ℝ := paperD n * scale n

/-- The paper-regime upper endpoint, clipped below at `exp 16`. -/
def paperMassX (n : ℕ) : ℝ := Real.exp (max paperMassC (paperMassH n))

/-- The paper-regime cutoff `y = X^(3/4)`, i.e. the paper's
`u = log X / log y = 4/3`. -/
def paperMassY (n : ℕ) : ℝ := (paperMassX n) ^ (3 / 4 : ℝ)

/-- The Rankin exponent used for the paper-regime mass. -/
def paperMassAlpha : ℝ := 1 / 2

/-- The saddle-mean constant used for the paper-regime mass. -/
def paperMassEta : ℝ := 1 / 8

/-- The count constant used for the paper-regime pair. -/
def paperMassCount : ℝ := 1 / 2

theorem paperMassX_ge_one (n : ℕ) : 1 ≤ paperMassX n := by
  unfold paperMassX
  calc
    (1 : ℝ) = Real.exp 0 := by simp
    _ ≤ Real.exp (max paperMassC (paperMassH n)) :=
      Real.exp_le_exp.mpr (le_trans (by norm_num [paperMassC]) (le_max_left _ _))

theorem paperMassX_pos (n : ℕ) : 0 < paperMassX n :=
  lt_of_lt_of_le zero_lt_one (paperMassX_ge_one n)

theorem paperMassX_ge_expC (n : ℕ) : Real.exp paperMassC ≤ paperMassX n := by
  unfold paperMassX
  exact Real.exp_le_exp.mpr (le_max_left _ _)

theorem paperMassH_le_log (n : ℕ) : paperMassH n ≤ Real.log (paperMassX n) := by
  unfold paperMassX paperMassH
  rw [Real.log_exp]
  exact le_max_right _ _

theorem paperMassY_pos (n : ℕ) : 0 < paperMassY n := by
  unfold paperMassY
  exact Real.rpow_pos_of_pos (paperMassX_pos n) (3 / 4 : ℝ)

theorem paperMassLogTwo_le_massBound :
    Real.log 2 ≤ ((3 / 4 : ℝ) * (1 - paperMassAlpha) - paperMassEta) * paperMassC := by
  have hlog : Real.log 2 ≤ (2 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  unfold paperMassAlpha paperMassEta paperMassC
  norm_num
  linarith

theorem paperMassLogTwo_le_countBound :
    Real.log 2 ≤ ((3 / 4 : ℝ) - paperMassCount) * paperMassC := by
  have hlog : Real.log 2 ≤ (2 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  unfold paperMassCount paperMassC
  norm_num
  linarith

/-- **The explicit paper-pair scale equality.**  The cutoff is the `3/4` power
of the endpoint on the logarithmic scale. -/
theorem paperMassScaleRatio (n : ℕ) :
    Real.log (paperMassY n) = (3 / 4 : ℝ) * Real.log (paperMassX n) := by
  unfold paperMassY
  exact Real.log_rpow (paperMassX_pos n) (3 / 4 : ℝ)

theorem paperMassY_ge_two (n : ℕ) : 2 ≤ paperMassY n := by
  have hXe : Real.exp paperMassC ≤ paperMassX n := paperMassX_ge_expC n
  have hpow : (Real.exp paperMassC) ^ (3 / 4 : ℝ) ≤ paperMassY n := by
    unfold paperMassY
    exact Real.rpow_le_rpow (Real.exp_pos paperMassC).le hXe (by norm_num)
  have hbase : (Real.exp paperMassC) ^ (3 / 4 : ℝ) = Real.exp (12 : ℝ) := by
    unfold paperMassC
    rw [← Real.exp_mul]
    norm_num
  have htwo : (2 : ℝ) ≤ Real.exp (12 : ℝ) := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (12 : ℝ) := Real.exp_le_exp.mpr (by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith)
  rw [hbase] at hpow
  exact htwo.trans hpow

theorem paperMassAlpha_pos : 0 < paperMassAlpha := by
  norm_num [paperMassAlpha]

theorem paperMassAlpha_lt_one : paperMassAlpha < 1 := by
  norm_num [paperMassAlpha]

theorem paperMassY_le_X (n : ℕ) : paperMassY n ≤ paperMassX n := by
  unfold paperMassY
  calc
    (paperMassX n) ^ (3 / 4 : ℝ) ≤ (paperMassX n) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (paperMassX_ge_one n) (by norm_num)
    _ = paperMassX n := Real.rpow_one _

/-- **The paper-regime mass lower bound.**  On the pair
`X = exp (max 16 (D log D))`, `y = X^(3/4)`, with `α = 1/2` and `η = 1/8`, the
actual smooth reciprocal mass satisfies `η Λ ≤ log mass` at the saddle scale
`Λ = log #smooth`. -/
theorem paperMassLogLower :
    SmoothNumberMassLogLower paperMassX paperMassY (fun _ => paperMassAlpha)
      (smoothSaddleScale paperMassX paperMassY) paperMassEta :=
  smoothNumberMassLogLower_of_logScale (X := paperMassX) (y := paperMassY)
    (β := (3 / 4 : ℝ)) (α := paperMassAlpha) (η := paperMassEta) (C := paperMassC)
    paperMassX_ge_one paperMassX_ge_expC paperMassY_pos paperMassScaleRatio
    (by norm_num) (by norm_num) (by norm_num [paperMassAlpha])
    (by norm_num [paperMassEta]) (by norm_num [paperMassAlpha, paperMassEta])
    paperMassLogTwo_le_massBound

/-- **The paper-regime count lower bound.**  The same pair satisfies
`exp ((1/2) D log D) ≤ #smooth`, because every integer up to `y = X^(3/4)` is
smooth. -/
theorem paperMassCountLower :
    SmoothNumberCountLower paperMassX paperMassY paperMassCount :=
  smoothNumberCountLower_of_logScale (X := paperMassX) (y := paperMassY)
    (β := (3 / 4 : ℝ)) (c := paperMassCount) (C := paperMassC)
    paperMassX_ge_one paperMassH_le_log paperMassX_ge_expC paperMassY_pos
    paperMassScaleRatio (by norm_num) (by norm_num)
    (by norm_num [paperMassCount]) (by norm_num [paperMassCount])
    paperMassLogTwo_le_countBound

/-- **The four L20.2 smooth-pair fields in one place.**  The paper-regime pair
has the endpoint and cutoff regularity, a positive Rankin exponent below one,
the saddle-scale count lower bound, and the saddle-mean mass lower bound. -/
theorem paperMassInputFields :
    (∀ n, 1 ≤ paperMassX n) ∧ (∀ n, 2 ≤ paperMassY n) ∧
      (∀ _n : ℕ, 0 < paperMassAlpha) ∧ (∀ _n : ℕ, paperMassAlpha < 1) ∧
      SmoothNumberCountLower paperMassX paperMassY paperMassCount ∧
      SmoothNumberMassLogLower paperMassX paperMassY (fun _ => paperMassAlpha)
        (smoothSaddleScale paperMassX paperMassY) paperMassEta :=
  ⟨paperMassX_ge_one, paperMassY_ge_two, fun _ => paperMassAlpha_pos,
    fun _ => paperMassAlpha_lt_one, paperMassCountLower, paperMassLogLower⟩

/-- The paper-regime pair realizes the L20.2 saddle scale. -/
theorem paperMassSaddleScaleLower :
    SaddlePointScaleLower (smoothSaddleScale paperMassX paperMassY) paperMassCount :=
  saddlePointScaleLower_of_smoothNumberCountLower paperMassCountLower

/-- The paper-regime pair realizes the L20.2 saddle mean. -/
theorem paperMassSaddleMeanLower :
    SaddlePointMeanLower
      (smoothNumberMass paperMassX paperMassY (fun _ => paperMassAlpha))
      (smoothSaddleScale paperMassX paperMassY) paperMassEta :=
  saddlePointMeanLower_of_smoothNumberMassLogLower paperMassX_ge_one paperMassLogLower

/-! ## Axiom audit -/

#print axioms two_le_rpow_of_exp_le
#print axioms half_le_floor
#print axioms smoothNumberSet_pow_Icc_subset
#print axioms smoothNumberCount_pow_ge_floor
#print axioms smoothNumberWindowCount_pow_ge_half
#print axioms log_smoothNumberMass_ge_pow
#print axioms smoothNumberMassLogLower_of_powCutoff
#print axioms smoothNumberCountLower_of_powCutoff
#print axioms smoothNumberMassLogLower_of_logScale
#print axioms smoothNumberCountLower_of_logScale
#print axioms paperMassScaleRatio
#print axioms paperMassLogLower
#print axioms paperMassY_ge_two
#print axioms paperMassCountLower
#print axioms paperMassInputFields
#print axioms paperMassSaddleScaleLower
#print axioms paperMassSaddleMeanLower

end

end Cogentic.RandomizedL20_2PaperMass
