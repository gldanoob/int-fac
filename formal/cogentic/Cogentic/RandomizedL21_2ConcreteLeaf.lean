import Cogentic.RandomizedPaperEndpointWave17
import Cogentic.RandomizedL21_2Elementary
import Cogentic.RandomizedL21_2TentWitness
import Cogentic.RandomizedL21_2TailBound
import Cogentic.RandomizedL21_2LineMinimal
import Cogentic.RandomizedL21_2StripBound

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# L21.2: the concrete leaf

This file assembles a `Wave17L21_2Inputs` from

* the elementary parameter profile of `RandomizedL21_2Elementary`
  (`c = 1 / sqrt 2`, `Cper = 3`, `X = exp (|scale|^3 + 3)`),
* the explicit non-vacuous Fourier/tent witness of
  `RandomizedL21_2TentWitness` (three sampled centres, constant amplitude
  `exp (-(T_X)^2 / 2)`, low/middle/tail frequencies `0`, `2`, `X^4`), and
* the proved zeta-side bounds
  `verticalTailBound_of_RH` and
  `verticalLineBound_of_zetaLineEstimate_exponent`.

Every structural and numerical field of `Wave17L21_2Inputs` is discharged by a
theorem; the only remaining analytic content is stated exactly as the `Prop`
`ConcreteLeafResidualProp` (equivalently, the two-field structure
`ConcreteLeafResidual`).  That residual is the conjunction of

1. a zeta-side package `ZetaSide`, consisting of
   * `RiemannZetaZerosOnLine`;
   * `ZetaLineZeroFree elementaryX`;
   * a two-sided line estimate `ZetaLineEstimate elementaryX b B` with
     `∀ n, 0 < b n`, `∀ n, 0 ≤ B n`, and `B n / b n ≤ KlineRaw` eventually;

2. the literal short-interval smooth count
   `ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX`.

The Riemann-hypothesis component is *not* implied by `ZetaLineZeroFree`: the
latter only excludes zeros on the single line `Re s = 2/3`, whereas the record's
`hRH` field asks about all zeros.  It is therefore stated explicitly inside the
single zeta-side package.  `ZetaLineZeroFree` itself is a consequence of the
line estimate (a positive lower bound for `‖ζ‖` rules out zeros), and is
recorded in the package for completeness.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count,
mass or error is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2ConcreteLeaf

open Filter Real
open scoped BigOperators

open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2TentWitness
open Cogentic.RandomizedL21_2TailBound
open Cogentic.RandomizedL21_2LineMinimal
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2StripBound
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedPaperEndpointWave17

/-! ## The explicit profile on the elementary scale `X` -/

/-- The coefficient amplitude `exp (-(T_X)^2 / 2)` at the elementary rate
`T_X = paperRate elementaryX`. -/
def elementaryAmp (n : ℕ) : ℝ :=
  Real.exp (-(paperRate elementaryX n) ^ 2 / 2)

/-- The coefficient energy `a_n^2 = exp (-(T_X)^2)`. -/
def elementaryEnergy (n : ℕ) : ℝ :=
  Real.exp (-(paperRate elementaryX n) ^ 2)

theorem elementaryAmp_pos (n : ℕ) : 0 < elementaryAmp n := Real.exp_pos _

theorem elementaryEnergy_pos (n : ℕ) : 0 < elementaryEnergy n := Real.exp_pos _

theorem elementaryAmp_sq (n : ℕ) :
    elementaryAmp n * elementaryAmp n = elementaryEnergy n := by
  unfold elementaryAmp elementaryEnergy
  rw [← Real.exp_add]
  congr 1
  ring

theorem elementary_normSq_amp (n : ℕ) :
    Complex.normSq (elementaryAmp n : ℂ) = elementaryEnergy n := by
  rw [Complex.normSq_ofReal, elementaryAmp_sq]

/-- Mode `0` is low (`|t| ≤ 1`), mode `1` is middle (`1 < |t| ≤ X^3`) and mode
`2` is above `X^3`. -/
def elementaryFreq (n : ℕ) : ZMod 3 → ℝ :=
  fun j => if j = 0 then 0 else if j = 1 then 2 else elementaryX n ^ 4

/-- **The explicit profile on the elementary parameter scale.**  It is the tent
witness construction with `X` replaced by the `X` of the elementary record, so
that the elementary `b ≤ B`/`a ≥ log 2`/two-scale lemmas apply directly.  It is
an `abbrev` so that `elementaryProfile.N n` is definitionally `3` for the `ZMod`
and `NeZero` instances. -/
abbrev elementaryProfile : TentProfile where
  X := elementaryX
  N := fun _ => 3
  N_pos := by intro n; norm_num
  coeff := fun n _ => (elementaryAmp n : ℂ)
  freq := elementaryFreq

theorem elementaryProfile_X (n : ℕ) : elementaryProfile.X n = elementaryX n := rfl

theorem elementaryProfile_N (n : ℕ) : elementaryProfile.N n = 3 := rfl

/-! ## Elementary bounds for the profile's `X` -/

theorem two_le_elementaryX (n : ℕ) : 2 ≤ elementaryX n := by
  have h3 : 3 ≤ elementaryU n := elementaryU_ge_three n
  have hX : Real.exp 1 ≤ elementaryX n := by
    unfold elementaryX
    exact Real.exp_le_exp.mpr (by linarith)
  calc (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    _ ≤ elementaryX n := hX

theorem two_le_elementaryX_cube (n : ℕ) : 2 ≤ elementaryX n ^ 3 := by
  have hX2 : 2 ≤ elementaryX n := two_le_elementaryX n
  have hX0 : 0 < elementaryX n := lt_trans zero_lt_one (elementaryX_gt_one n)
  have hcube : elementaryX n ≤ elementaryX n ^ 3 := by
    nlinarith [hX2, sq_nonneg (elementaryX n), pow_pos hX0 3]
  linarith

/-! ## The profile's total energy and band memberships -/

theorem elementaryProfile_totalEnergy (n : ℕ) :
    elementaryProfile.totalEnergy n = 3 * elementaryEnergy n := by
  letI := elementaryProfile.neZero n
  unfold TentProfile.totalEnergy
  have h : (∑ j : ZMod (elementaryProfile.N n),
        Complex.normSq (elementaryProfile.coeff n j)) =
      ∑ _j : ZMod (elementaryProfile.N n), elementaryEnergy n := by
    apply Finset.sum_congr rfl
    intro j _
    simpa [elementaryProfile] using elementary_normSq_amp n
  rw [h, Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card (ZMod (elementaryProfile.N n)) = 3 by
    rw [ZMod.card, elementaryProfile_N]]
  norm_num

theorem zero_mem_lowSet (n : ℕ) : (0 : ZMod 3) ∈ elementaryProfile.lowSet n := by
  unfold TentProfile.lowSet
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  show |elementaryFreq n 0| ≤ 1
  rw [show elementaryFreq n 0 = 0 by unfold elementaryFreq; simp]
  norm_num

theorem one_mem_middleSet (n : ℕ) : (1 : ZMod 3) ∈ elementaryProfile.middleSet n := by
  unfold TentProfile.middleSet TentProfile.nonLowSet
  change (1 : ZMod 3) ∈
    (Finset.univ.filter (fun j : ZMod 3 => ¬ |elementaryFreq n j| ≤ 1)).filter
      (fun j => |elementaryFreq n j| ≤ elementaryX n ^ 3)
  rw [Finset.mem_filter, Finset.mem_filter]
  refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · unfold elementaryFreq
    have h10 : (1 : ZMod 3) ≠ 0 := by decide
    rw [if_neg h10, if_pos rfl]
    norm_num
  · unfold elementaryFreq
    have h10 : (1 : ZMod 3) ≠ 0 := by decide
    rw [if_neg h10, if_pos rfl]
    simpa using two_le_elementaryX_cube n

theorem two_mem_tailSet (n : ℕ) : (2 : ZMod 3) ∈ elementaryProfile.tailSet n := by
  unfold TentProfile.tailSet TentProfile.nonLowSet
  change (2 : ZMod 3) ∈
    (Finset.univ.filter (fun j : ZMod 3 => ¬ |elementaryFreq n j| ≤ 1)).filter
      (fun j => ¬ |elementaryFreq n j| ≤ elementaryX n ^ 3)
  rw [Finset.mem_filter, Finset.mem_filter]
  refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · unfold elementaryFreq
    have h20 : (2 : ZMod 3) ≠ 0 := by decide
    have h21 : (2 : ZMod 3) ≠ 1 := by decide
    rw [if_neg h20, if_neg h21]
    have hX0 : 0 < elementaryX n := lt_trans zero_lt_one (elementaryX_gt_one n)
    have h4 : 0 < elementaryX n ^ 4 := pow_pos hX0 4
    rw [abs_of_pos h4]
    intro hle
    have h16 : (2 : ℝ) ^ 4 ≤ elementaryX n ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (two_le_elementaryX n) 4
    norm_num at h16
    linarith
  · unfold elementaryFreq
    have h20 : (2 : ZMod 3) ≠ 0 := by decide
    have h21 : (2 : ZMod 3) ≠ 1 := by decide
    rw [if_neg h20, if_neg h21]
    have hX1 : 1 < elementaryX n := elementaryX_gt_one n
    have h4 : elementaryX n ^ 3 < elementaryX n ^ 4 :=
      pow_lt_pow_right₀ hX1 (by norm_num)
    have hpos : 0 < elementaryX n ^ 4 := pow_pos (lt_trans zero_lt_one hX1) 4
    rw [abs_of_pos hpos]
    intro hle
    exact absurd hle (not_le.mpr h4)

/-! ## Band energies -/

theorem lowEnergy_le_totalEnergy (n : ℕ) :
    elementaryProfile.lowEnergy n ≤ elementaryProfile.totalEnergy n := by
  unfold TentProfile.lowEnergy TentProfile.totalEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => Complex.normSq_nonneg (elementaryProfile.coeff n i))

theorem middleEnergy_le_totalEnergy (n : ℕ) :
    elementaryProfile.middleEnergy n ≤ elementaryProfile.totalEnergy n := by
  unfold TentProfile.middleEnergy TentProfile.middleSet TentProfile.nonLowSet
    TentProfile.totalEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    (fun i _ _ => Complex.normSq_nonneg (elementaryProfile.coeff n i))

theorem tailEnergy_le_totalEnergy (n : ℕ) :
    elementaryProfile.tailEnergy n ≤ elementaryProfile.totalEnergy n := by
  unfold TentProfile.tailEnergy TentProfile.tailSet TentProfile.nonLowSet
    TentProfile.totalEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    (fun i _ _ => Complex.normSq_nonneg (elementaryProfile.coeff n i))

theorem lowEnergy_ge_energy (n : ℕ) :
    elementaryEnergy n ≤ elementaryProfile.lowEnergy n := by
  unfold TentProfile.lowEnergy
  have h := Finset.single_le_sum
    (f := fun j : ZMod 3 => Complex.normSq (elementaryProfile.coeff n j))
    (fun j _ => Complex.normSq_nonneg (elementaryProfile.coeff n j))
    (zero_mem_lowSet n)
  simpa [elementaryProfile, elementary_normSq_amp, elementaryAmp_sq] using h

theorem middleEnergy_ge_energy (n : ℕ) :
    elementaryEnergy n ≤ elementaryProfile.middleEnergy n := by
  unfold TentProfile.middleEnergy
  have h := Finset.single_le_sum
    (f := fun j : ZMod 3 => Complex.normSq (elementaryProfile.coeff n j))
    (fun j _ => Complex.normSq_nonneg (elementaryProfile.coeff n j))
    (one_mem_middleSet n)
  simpa [elementaryProfile, elementary_normSq_amp, elementaryAmp_sq] using h

theorem tailEnergy_ge_energy (n : ℕ) :
    elementaryEnergy n ≤ elementaryProfile.tailEnergy n := by
  unfold TentProfile.tailEnergy
  have h := Finset.single_le_sum
    (f := fun j : ZMod 3 => Complex.normSq (elementaryProfile.coeff n j))
    (fun j _ => Complex.normSq_nonneg (elementaryProfile.coeff n j))
    (two_mem_tailSet n)
  simpa [elementaryProfile, elementary_normSq_amp, elementaryAmp_sq] using h

theorem elementary_lowEnergy_pos (n : ℕ) : 0 < elementaryProfile.lowEnergy n :=
  lt_of_lt_of_le (elementaryEnergy_pos n) (lowEnergy_ge_energy n)

theorem elementary_middleEnergy_pos (n : ℕ) : 0 < elementaryProfile.middleEnergy n :=
  lt_of_lt_of_le (elementaryEnergy_pos n) (middleEnergy_ge_energy n)

theorem elementary_tailEnergy_pos (n : ℕ) : 0 < elementaryProfile.tailEnergy n :=
  lt_of_lt_of_le (elementaryEnergy_pos n) (tailEnergy_ge_energy n)

/-! ## The three Fourier band bounds -/

theorem elementaryT_nonneg (n : ℕ) : 0 ≤ paperRate elementaryX n :=
  (elementaryT_pos n).le

/-- Absorption of the factor `3` and the band exponent at the elementary rate. -/
theorem eventually_three_mul_elementaryEnergy_le_exp (A : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      3 * elementaryEnergy n ≤ Real.exp (-A * paperRate elementaryX n) := by
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      Real.log 3 + 1 + max A 0 ≤ paperRate elementaryX n :=
    elementaryT_grows.eventually_ge_atTop _
  filter_upwards [hthreshold] with n hn
  set R := paperRate elementaryX n with hR
  have hR0 : 0 ≤ R := elementaryT_nonneg n
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hM0 : (0 : ℝ) ≤ max A 0 := le_max_right A 0
  have hMA : A ≤ max A 0 := le_max_left A 0
  have hR1 : 1 ≤ R := by linarith
  have hRlog : Real.log 3 ≤ R := by linarith
  have hexp : Real.log 3 - R ^ 2 ≤ -A * R := by
    by_cases hA : 0 ≤ A
    · have hRA : A + 1 ≤ R := by linarith
      have hquad : Real.log 3 ≤ R ^ 2 - A * R := by
        have hfac : 1 ≤ R - A := by linarith
        have hmul : R ≤ R * (R - A) := by
          calc R = R * 1 := (mul_one _).symm
            _ ≤ R * (R - A) := mul_le_mul_of_nonneg_left hfac hR0
        nlinarith
      linarith
    · have hAneg : A < 0 := lt_of_not_ge hA
      have hsq : Real.log 3 ≤ R ^ 2 := by nlinarith
      have hneg : 0 ≤ -A * R := mul_nonneg (by linarith) hR0
      nlinarith
  have hExpLe : Real.exp (Real.log 3 - R ^ 2) ≤ Real.exp (-A * R) :=
    Real.exp_le_exp.mpr hexp
  have hExpEq : Real.exp (Real.log 3 - R ^ 2) = 3 * elementaryEnergy n := by
    have harg : Real.log 3 - R ^ 2 = Real.log 3 + -(R ^ 2) := by ring
    rw [harg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    unfold elementaryEnergy
    rw [hR]
  rw [hExpEq] at hExpLe
  rw [hR]
  exact hExpLe

/-- Low-frequency bound (`|t| ≤ 1`) for the elementary profile. -/
theorem elementaryProfile_fourierLow (c : ℝ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      elementaryProfile.lowEnergy n ≤
        Real.exp (-(((2 * c) / 3) - δ) * paperRate elementaryProfile.X n) := by
  intro δ hδ
  filter_upwards [eventually_three_mul_elementaryEnergy_le_exp ((2 * c) / 3 - δ)]
    with n hn
  calc elementaryProfile.lowEnergy n ≤ elementaryProfile.totalEnergy n :=
        lowEnergy_le_totalEnergy n
    _ = 3 * elementaryEnergy n := elementaryProfile_totalEnergy n
    _ ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate elementaryX n) := hn
    _ = Real.exp (-(((2 * c) / 3) - δ) * paperRate elementaryProfile.X n) := rfl

/-- Middle-frequency bound (`1 < |t| ≤ X^3`) for the elementary profile. -/
theorem elementaryProfile_fourierMiddle (c : ℝ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      elementaryProfile.middleEnergy n ≤
        Real.exp (-((1 / c) - δ) * paperRate elementaryProfile.X n) := by
  intro δ hδ
  filter_upwards [eventually_three_mul_elementaryEnergy_le_exp (1 / c - δ)] with n hn
  calc elementaryProfile.middleEnergy n ≤ elementaryProfile.totalEnergy n :=
        middleEnergy_le_totalEnergy n
    _ = 3 * elementaryEnergy n := elementaryProfile_totalEnergy n
    _ ≤ Real.exp (-((1 / c) - δ) * paperRate elementaryX n) := hn
    _ = Real.exp (-((1 / c) - δ) * paperRate elementaryProfile.X n) := rfl

/-- High-frequency bound (`|t| > X^3`) for the elementary profile. -/
theorem elementaryProfile_fourierTail :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      elementaryProfile.tailEnergy n ≤
        Real.exp (-δ * paperRate elementaryProfile.X n) := by
  intro δ hδ
  filter_upwards [eventually_three_mul_elementaryEnergy_le_exp δ] with n hn
  calc elementaryProfile.tailEnergy n ≤ elementaryProfile.totalEnergy n :=
        tailEnergy_le_totalEnergy n
    _ = 3 * elementaryEnergy n := elementaryProfile_totalEnergy n
    _ ≤ Real.exp (-δ * paperRate elementaryX n) := hn
    _ = Real.exp (-δ * paperRate elementaryProfile.X n) := rfl

/-! ## Monotonicity of the vertical-tail bound in the exponent -/

/-- A `VerticalTailBound` at exponent `C` gives one at every larger exponent,
because `log X ≥ 3 > 1`. -/
theorem verticalTailBound_mono_exponent {X : ℕ → ℝ} {K : ℕ → ℝ} {C C' : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hK : ∀ᶠ n : ℕ in atTop, 0 ≤ K n) (hCC' : C ≤ C')
    (h : VerticalTailBound X K C) : VerticalTailBound X K C' := by
  filter_upwards [h, hK] with n hn hk
  intro v t hv ht
  have hU1 : 1 ≤ bandLog X n := by linarith [hU n]
  have hpow : (bandLog X n) ^ C ≤ (bandLog X n) ^ C' :=
    Real.rpow_le_rpow_of_exponent_le hU1 hCC'
  have hv0 : 0 ≤ v := by linarith
  have hX0 : 0 ≤ X n := (lt_trans zero_lt_one (hX n)).le
  calc
    ‖verticalZetaSum v t (X n ^ 3 + 1) - verticalZetaSum v t (X n ^ 3)‖
        ≤ shiftHorizontal (K n) (bandLog X n) C (X n) v := hn v t hv ht
    _ ≤ shiftHorizontal (K n) (bandLog X n) C' (X n) v := by
      unfold shiftHorizontal
      apply mul_le_mul_of_nonneg_left ?_ hk
      apply div_le_div_of_nonneg_right ?_ (pow_nonneg hX0 3)
      exact mul_le_mul_of_nonneg_left hpow hv0

/-! ## The residual analytic input -/

/-- The zeta-side analytic package: the Riemann hypothesis (needed by the
record's `hRH` field), its consequence `ZetaLineZeroFree`, and a two-sided line
estimate with a raw line constant `KlineRaw`. -/
structure ZetaSide where
  /-- The Riemann hypothesis for `ζ`. -/
  rh : RiemannZetaZerosOnLine
  /-- Zero-freeness on the segment `Re s = 2/3`. -/
  zeroFree : ZetaLineZeroFree elementaryX
  /-- Lower bound sequence for `ζ` on the line. -/
  b : ℕ → ℝ
  /-- Upper bound sequence for `ζ'` on the line. -/
  B : ℕ → ℝ
  b_pos : ∀ n, 0 < b n
  B_nonneg : ∀ n, 0 ≤ B n
  /-- The two-sided line estimate. -/
  estimate : ZetaLineEstimate elementaryX b B
  /-- The raw line constant. -/
  KlineRaw : ℝ
  KlineRaw_nonneg : 0 ≤ KlineRaw
  /-- The quotient `B / b` is eventually at most `KlineRaw`. -/
  ratio_le : ∀ᶠ n : ℕ in atTop, B n / b n ≤ KlineRaw

/-- **The final residual conjunction.**  It has exactly two analytic components:
the zeta-side package `ZetaSide` and the literal short-interval smooth count. -/
structure ConcreteLeafResidual where
  /-- The zeta-side analytic input. -/
  zeta : ZetaSide
  /-- The literal short-interval smooth count. -/
  localCount : ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX

/-- The zeta-side analytic package in `Prop` form. -/
def ZetaSideProp : Prop :=
  RiemannZetaZerosOnLine ∧
    ZetaLineZeroFree elementaryX ∧
    (∃ b B : ℕ → ℝ,
      (∀ n, 0 < b n) ∧ (∀ n, 0 ≤ B n) ∧
        ZetaLineEstimate elementaryX b B ∧
        ∃ KlineRaw : ℝ,
          0 ≤ KlineRaw ∧ ∀ᶠ n : ℕ in atTop, B n / b n ≤ KlineRaw)

/-- **The final residual conjunction, in `Prop` form.**  It has exactly two
top-level conjuncts: the zeta-side analytic package (RH, `ZetaLineZeroFree`, and
the two-sided line estimate with a raw line constant) and the literal
short-interval smooth count. -/
def ConcreteLeafResidualProp : Prop :=
  ZetaSideProp ∧ ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX

/-- The `Prop` residual is exactly the two-field structure. -/
theorem nonempty_of_residualProp (h : ConcreteLeafResidualProp) :
    Nonempty ConcreteLeafResidual := by
  obtain ⟨⟨hRH, hz, ⟨b, B, hb, hB, hest, KlineRaw, hK, hratio⟩⟩, hcount⟩ := h
  exact ⟨{
    zeta := {
      rh := hRH
      zeroFree := hz
      b := b
      B := B
      b_pos := hb
      B_nonneg := hB
      estimate := hest
      KlineRaw := KlineRaw
      KlineRaw_nonneg := hK
      ratio_le := hratio }
    localCount := hcount }⟩

theorem residualProp_of_nonempty (h : Nonempty ConcreteLeafResidual) :
    ConcreteLeafResidualProp := by
  obtain ⟨R⟩ := h
  exact ⟨⟨R.zeta.rh, R.zeta.zeroFree,
    ⟨R.zeta.b, R.zeta.B, R.zeta.b_pos, R.zeta.B_nonneg,
      R.zeta.estimate, R.zeta.KlineRaw, R.zeta.KlineRaw_nonneg, R.zeta.ratio_le⟩⟩,
    R.localCount⟩

/-- **The residual conjunction is exactly the two-field record.** -/
theorem residualProp_iff : ConcreteLeafResidualProp ↔ Nonempty ConcreteLeafResidual :=
  ⟨nonempty_of_residualProp, residualProp_of_nonempty⟩

/-- The lower bound inside `ZetaLineEstimate` rules out zeros, so the line
estimate gives `ZetaLineZeroFree`.  (Recorded as a check that the zero-free
component of `ZetaSide` carries no extra analytic content beyond the line
estimate.) -/
theorem zetaLineZeroFree_of_estimate {b B : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (h : ZetaLineEstimate elementaryX b B) :
    ZetaLineZeroFree elementaryX := by
  filter_upwards [h] with n hn
  intro u hu hzero
  have hb_le := (hn u hu).1
  rw [hzero, norm_zero] at hb_le
  exact (not_lt_of_ge hb_le) (hb n)

/-! ## The assembled leaf -/

/-- **The concrete `Wave17L21_2Inputs`.**  All numerical, structural and
two-scale fields are the elementary theorems; the line and tail constants are
the ones supplied by the residual. -/
noncomputable def wave17InputsOfResidual (h : ConcreteLeafResidual) :
    Wave17L21_2Inputs := by
  let z := h.zeta
  have hRH : RiemannZetaZerosOnLine := z.rh
  have hb : ∀ n, 0 < z.b n := z.b_pos
  have hB : ∀ n, 0 ≤ z.B n := z.B_nonneg
  have hest : ZetaLineEstimate elementaryX z.b z.B := z.estimate
  have hKline : 0 ≤ z.KlineRaw := z.KlineRaw_nonneg
  have hratio : ∀ᶠ n : ℕ in atTop, z.B n / z.b n ≤ z.KlineRaw := z.ratio_le
  have hcount := h.localCount
  have hU : ∀ n, 3 ≤ bandLog elementaryProfile.X n := by
    intro n
    change 3 ≤ bandLog elementaryX n
    rw [bandLog_elementaryX]
    exact elementaryU_ge_three n
  have hX : ∀ n, 1 < elementaryProfile.X n := by
    intro n
    change 1 < elementaryX n
    exact elementaryX_gt_one n
  have hline : VerticalLineBound elementaryProfile.X
      (fun _ => z.KlineRaw) (elementaryCper - 1) := by
    have hVB : VerticalLineBound elementaryProfile.X
        (fun n => z.B n / z.b n) (elementaryCper - 1) :=
      verticalLineBound_of_zetaLineEstimate_exponent
        (X := elementaryProfile.X) (C := elementaryCper) hX hU
        (by unfold elementaryCper; norm_num) hb hB hest
    exact verticalLineBound_mono (X := elementaryProfile.X) hX hVB hratio
  have htail : VerticalTailBound elementaryProfile.X
      (fun _ => tailK / Real.pi) (elementaryCper - 1) :=
    verticalTailBound_mono_exponent hX hU
      (Eventually.of_forall fun _ => div_nonneg tailK_nonneg Real.pi_pos.le)
      (by unfold elementaryCper; norm_num)
      (verticalTailBound_of_RH (X := elementaryProfile.X) hX hU hRH)
  exact Wave17L21_2Inputs.ofRaw
    (profile := elementaryProfile)
    (c := elementaryC)
    (Cper := elementaryCper)
    (KlineRaw := z.KlineRaw)
    (Ktail := tailK / Real.pi)
    (p := elementaryX)
    hX elementaryC_pos elementaryC_le_one hU
    (by unfold elementaryCper; norm_num)
    hKline
    (div_nonneg tailK_nonneg Real.pi_pos.le)
    hRH
    hline
    htail
    (Eventually.of_forall elementaryX_gt_one)
    hcount
    (by
      simpa only [elementaryProfile_X] using elementary_b_le_B)
    (by
      simpa only [elementaryProfile_X] using elementary_a_ge_log_two)    (elementaryProfile_fourierLow elementaryC)
    (elementaryProfile_fourierMiddle elementaryC)
    elementaryProfile_fourierTail
    (by
      intro m hm
      filter_upwards [elementaryU_dominates m hm] with n hn
      exact hn)
    (by
      filter_upwards [elementaryU_le_exp] with n hn
      exact hn)

/-! ## The reduction `residual → Wave17L21_2Inputs` -/

/-- **The residual reduction.**  The two-input residual implies the concrete
wave-17 L21.2 record. -/
theorem residual_to_wave17Inputs (h : ConcreteLeafResidual) :
    Nonempty Wave17L21_2Inputs :=
  ⟨wave17InputsOfResidual h⟩

/-- **The `Prop`-form residual reduction**, stated exactly as the final
conjunction. -/
theorem residualProp_to_wave17Inputs (h : ConcreteLeafResidualProp) :
    Nonempty Wave17L21_2Inputs :=
  Nonempty.map wave17InputsOfResidual (nonempty_of_residualProp h)

/-- The assembled record keeps the elementary profile. -/
theorem wave17InputsOfResidual_profile (h : ConcreteLeafResidual) :
    (wave17InputsOfResidual h).profile = elementaryProfile := by
  cases h with
  | mk zeta localCount => rfl

/-- The assembled record keeps the elementary stage-one constant. -/
theorem wave17InputsOfResidual_c (h : ConcreteLeafResidual) :
    (wave17InputsOfResidual h).c = elementaryC := by
  cases h with
  | mk zeta localCount => rfl

/-- The assembled record keeps the elementary Perron exponent. -/
theorem wave17InputsOfResidual_Cper (h : ConcreteLeafResidual) :
    (wave17InputsOfResidual h).Cper = elementaryCper := by
  cases h with
  | mk zeta localCount => rfl

/-- The assembled record keeps the elementary centre sequence `p = X`. -/
theorem wave17InputsOfResidual_p (h : ConcreteLeafResidual) :
    (wave17InputsOfResidual h).p = elementaryX := by
  cases h with
  | mk zeta localCount => rfl

/-- The stored vertical-tail constant of the assembled record. -/
theorem wave17InputsOfResidual_Ktail (h : ConcreteLeafResidual) :
    (wave17InputsOfResidual h).Ktail = tailK / Real.pi := by
  cases h with
  | mk zeta localCount => rfl

/-! ## Axiom audit -/

#print axioms elementaryProfile_totalEnergy
#print axioms elementaryProfile_fourierLow
#print axioms elementaryProfile_fourierMiddle
#print axioms elementaryProfile_fourierTail
#print axioms zetaLineZeroFree_of_estimate
#print axioms nonempty_of_residualProp
#print axioms residualProp_of_nonempty
#print axioms residualProp_iff
#print axioms wave17InputsOfResidual
#print axioms residual_to_wave17Inputs
#print axioms residualProp_to_wave17Inputs
#print axioms wave17InputsOfResidual_profile
#print axioms wave17InputsOfResidual_c
#print axioms wave17InputsOfResidual_Cper
#print axioms wave17InputsOfResidual_p
#print axioms wave17InputsOfResidual_Ktail

end Cogentic.RandomizedL21_2ConcreteLeaf

end
