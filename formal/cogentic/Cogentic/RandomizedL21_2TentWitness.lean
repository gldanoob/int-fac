import Cogentic.RandomizedL21_2Tent
import Cogentic.RandomizedTwoFactorFourier

set_option linter.style.haveILetI false

/-!
# L21.2: a concrete, non-vacuous finite Fourier/tent profile

`Cogentic.RandomizedL21_2Tent` proves that any `TentProfile` satisfies the
finite Plancherel / tent mean-square comparison

```
(1/N) Σ_i deficit_i² ≤ lowEnergy + middleEnergy + tailEnergy ,
```

but it leaves the profile itself abstract, so the three frequency-band fields
`fourierLow`, `fourierMiddle`, `fourierTail` of the L21.2 leaf — and the
bad-set fraction built from the profile — could in principle be vacuous.

This file constructs an *explicit* profile and proves every Fourier-side field
for it.

## The explicit data

* `U n = n + 3`, `X n = exp (U n)`, so `log X = U n → ∞` and
  `T_X = paperRate X n = sqrt (U n log U n) → ∞`;
* a three-point sample `N n = 3`;
* the complex coefficient vector is constant,
  `coeff n j = a_n` with `a_n = exp (-(T_X n)² / 2)`, so
  `‖coeff n j‖² = exp (-(T_X n)²)`;
* the real frequencies are
  `freq n 0 = 0` (low band), `freq n 1 = 2` (middle band) and
  `freq n 2 = X n ^ 4` (tail band).

All three bands therefore contain at least one coefficient of energy
`exp (-(T_X n)²) > 0`; none of the three bounds is an empty statement.

## What is proved

* `witness_deficit_zero`: the DFT at the zero frequency is the *explicit*
  nonzero number `3 a_n` — the discrepancy profile is not identically zero;
* `witness_meanSquare_eq_totalEnergy` and `witness_tentComparison`: the
  normalized discrepancy mean square *equals* the total coefficient energy,
  and hence the three band energies (this is the sharp form of
  `TentProfile.meanSquare_le_energy`);
* `witness_lowEnergy_pos`, `witness_middleEnergy_pos`,
  `witness_tailEnergy_pos`, `witness_meanSquare_pos`: all energies and the
  mean square are strictly positive;
* `witness_fourierLow`, `witness_fourierMiddle`, `witness_fourierTail`: the
  three Fourier band bounds with the paper's exponents
  `(2 c / 3) - δ`, `1/c - δ`, `δ`, for every `c` and every `δ > 0`;
* `witness_badFraction_ge_third`: for the profile's Chebyshev threshold
  `τ = a_n` the bad-set fraction `#bad / N` is at least `1/3` (and
  `witness_badFraction_pos` records strict positivity), while
  `witness_badFraction_le_markov` recovers the finite Markov bound used by
  the leaf; `witness_badFraction_pos_of_le` shows that every threshold
  `0 < τ ≤ 3 a_n` gives a strictly positive fraction;
* `witness_badCount_div`, `witness_badCount_nonneg`,
  `witness_badCount_div_pos`: the leaf's loss shape `badCount / (X + 1)` is
  exactly the bad fraction and is strictly positive.

The bad set `witnessBadSet τ` is *the same filter* as
`L21_2FourierInputs.badSet`; at `τ = chebThreshold witnessProfile.X c` it is
literally the leaf's bad set, and at `τ = a_n` the elementary computation
above makes its mass positive.  The three band bounds are proved with the
coefficient energies actually positive, so none of them is an empty
inequality.

The record `FourierWitness` packages the profile together with these proofs,
so it is a direct inhabitant of the Fourier part of the L21.2 leaf.
`concreteFourierWitness` is that inhabitant.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no energy, count
or loss is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2TentWitness

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2Fourier

/-! ## The explicit band scale -/

/-- The explicit band logarithm `U n = n + 3`. -/
def witnessU (n : ℕ) : ℝ := (n : ℝ) + 3

/-- The explicit dyadic bound `X n = exp (U n)`. -/
def witnessX (n : ℕ) : ℝ := Real.exp (witnessU n)

theorem witnessU_ge_three (n : ℕ) : 3 ≤ witnessU n := by
  unfold witnessU
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem witnessU_pos (n : ℕ) : 0 < witnessU n :=
  lt_of_lt_of_le (by norm_num) (witnessU_ge_three n)

theorem witnessX_gt_one (n : ℕ) : 1 < witnessX n := by
  unfold witnessX
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < Real.exp (witnessU n) := Real.exp_lt_exp.mpr (witnessU_pos n)

theorem witnessX_pos (n : ℕ) : 0 < witnessX n :=
  lt_trans zero_lt_one (witnessX_gt_one n)

theorem bandLog_witnessX (n : ℕ) : bandLog witnessX n = witnessU n := by
  unfold bandLog witnessX
  rw [Real.log_exp]

/-- `X n ≥ 2`, the only lower bound needed to place the middle frequency. -/
theorem two_le_witnessX (n : ℕ) : 2 ≤ witnessX n := by
  have h3 : witnessU n ≥ 3 := witnessU_ge_three n
  have hX : Real.exp 1 ≤ witnessX n := by
    unfold witnessX
    exact Real.exp_le_exp.mpr (by linarith)
  calc (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    _ ≤ witnessX n := hX

/-- `X n ^ 3 ≥ 2`, so the middle frequency `2` lies below `X³`. -/
theorem two_le_witnessX_cube (n : ℕ) : 2 ≤ witnessX n ^ 3 := by
  have hX2 : 2 ≤ witnessX n := two_le_witnessX n
  have hX0 : 0 < witnessX n := witnessX_pos n
  have hcube : witnessX n ≤ witnessX n ^ 3 := by
    nlinarith [hX2, sq_nonneg (witnessX n), pow_pos hX0 3]
  linarith

/-! ## The rate `T_X = sqrt (U log U)` -/

/-- The explicit rate `T_X = sqrt (U log U)`. -/
def witnessRate (n : ℕ) : ℝ := Real.sqrt (witnessU n * Real.log (witnessU n))

theorem witnessRate_eq_paperRate (n : ℕ) :
    paperRate witnessX n = witnessRate n := by
  unfold witnessRate paperRate
  rw [bandLog_witnessX]

theorem witnessRate_nonneg (n : ℕ) : 0 ≤ witnessRate n := by
  unfold witnessRate
  exact Real.sqrt_nonneg _

theorem witnessU_grows : Tendsto witnessU atTop atTop := by
  unfold witnessU
  exact tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop

theorem witnessRate_grows : Tendsto witnessRate atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (witnessU n)) atTop atTop :=
    Real.tendsto_log_atTop.comp witnessU_grows
  have hmul : Tendsto (fun n : ℕ => witnessU n * Real.log (witnessU n)) atTop atTop :=
    witnessU_grows.atTop_mul_atTop₀ hlog
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt (witnessU n * Real.log (witnessU n))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hmul
  unfold witnessRate
  exact hsqrt

/-! ## The amplitude and its energy -/

/-- The coefficient amplitude `a_n = exp (-(T_X n)² / 2)`. -/
def witnessAmp (n : ℕ) : ℝ := Real.exp (-(witnessRate n) ^ 2 / 2)

/-- The coefficient energy `a_n² = exp (-(T_X n)²)`. -/
def witnessEnergy (n : ℕ) : ℝ := Real.exp (-(witnessRate n) ^ 2)

theorem witnessAmp_pos (n : ℕ) : 0 < witnessAmp n := Real.exp_pos _

theorem witnessEnergy_pos (n : ℕ) : 0 < witnessEnergy n := Real.exp_pos _

theorem witnessAmp_sq (n : ℕ) : witnessAmp n * witnessAmp n = witnessEnergy n := by
  unfold witnessAmp witnessEnergy
  rw [← Real.exp_add]
  congr 1
  ring

/-- The squared norm of the concrete coefficient is the explicit energy. -/
theorem witness_normSq_amp (n : ℕ) :
    Complex.normSq (witnessAmp n : ℂ) = witnessEnergy n := by
  rw [Complex.normSq_ofReal, witnessAmp_sq]

/-! ## The profile -/

/-- The explicit frequency assignment: mode `0` is low, mode `1` is middle and
mode `2` is above `X³`. -/
def witnessFreq (n : ℕ) : ZMod 3 → ℝ :=
  fun j => if j = 0 then 0 else if j = 1 then 2 else witnessX n ^ 4

/-- **The explicit finite Fourier/tent profile.**  Three sampled centres, the
constant complex coefficient `a_n`, and the three-band frequency assignment.
It is an `abbrev` so that `witnessProfile.N n` is definitionally `3` for the
`ZMod` and `NeZero` instances used below. -/
abbrev witnessProfile : TentProfile where
  X := witnessX
  N := fun _ => 3
  N_pos := by intro n; norm_num
  coeff := fun n _ => (witnessAmp n : ℂ)
  freq := witnessFreq

theorem witnessProfile_X (n : ℕ) : witnessProfile.X n = witnessX n := rfl

theorem witnessProfile_N (n : ℕ) : witnessProfile.N n = 3 := rfl

/-- The rate identification written with the profile's own `X`. -/
theorem witnessRate_paperRate (n : ℕ) :
    paperRate witnessProfile.X n = witnessRate n :=
  witnessRate_eq_paperRate n

theorem witnessFreq_zero (n : ℕ) : witnessFreq n 0 = 0 := by
  unfold witnessFreq
  simp

theorem witnessFreq_one (n : ℕ) : witnessFreq n 1 = 2 := by
  unfold witnessFreq
  have h10 : (1 : ZMod 3) ≠ 0 := by decide
  rw [if_neg h10, if_pos rfl]

theorem witnessFreq_two (n : ℕ) : witnessFreq n 2 = witnessX n ^ 4 := by
  unfold witnessFreq
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  rw [if_neg h20, if_neg h21]

/-! ## The zero-frequency value of the discrepancy -/

/-- The sampled index whose frequency is `0`. -/
def witnessZeroIndex (n : ℕ) : Fin (witnessProfile.N n) :=
  (ZMod.finEquiv (witnessProfile.N n)).symm 0

theorem finEquiv_witnessZeroIndex (n : ℕ) :
    ZMod.finEquiv (witnessProfile.N n) (witnessZeroIndex n) = 0 :=
  (ZMod.finEquiv (witnessProfile.N n)).apply_symm_apply 0

/-- **The DFT at frequency zero.**  The profile is constant, so the discrete
Fourier transform at `0` is the total mass `3 a_n`, a genuinely nonzero real
number. -/
theorem witness_dft_zero (n : ℕ) :
    (ZMod.dft (witnessProfile.coeff n) 0).re = 3 * witnessAmp n := by
  rw [ZMod.dft_apply_zero]
  simp [witnessProfile, Finset.sum_const, ZMod.card]

/-- **The discrepancy at the zero frequency is `3 a_n`.** -/
theorem witness_deficit_zero (n : ℕ) :
    witnessProfile.deficit n (witnessZeroIndex n) = 3 * witnessAmp n := by
  unfold TentProfile.deficit
  rw [finEquiv_witnessZeroIndex]
  exact witness_dft_zero n

theorem witness_deficit_zero_pos (n : ℕ) :
    0 < witnessProfile.deficit n (witnessZeroIndex n) := by
  rw [witness_deficit_zero]
  have h := witnessAmp_pos n
  linarith

/-! ## The total coefficient energy -/

/-- The total coefficient energy is `N a_n² = 3 exp (-(T_X n)²)`. -/
theorem witness_totalEnergy (n : ℕ) :
    witnessProfile.totalEnergy n = 3 * witnessEnergy n := by
  letI := witnessProfile.neZero n
  unfold TentProfile.totalEnergy
  have h : (∑ j : ZMod (witnessProfile.N n),
        Complex.normSq (witnessProfile.coeff n j)) =
      ∑ _j : ZMod (witnessProfile.N n), witnessEnergy n := by
    apply Finset.sum_congr rfl
    intro j _
    simpa [witnessProfile] using witness_normSq_amp n
  rw [h, Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card (ZMod (witnessProfile.N n)) = 3 by
    rw [ZMod.card, witnessProfile_N]]
  norm_num

/-! ## The band memberships -/

theorem zero_mem_lowSet (n : ℕ) : (0 : ZMod 3) ∈ witnessProfile.lowSet n := by
  simp [TentProfile.lowSet, witnessProfile, witnessFreq_zero]
theorem one_mem_middleSet (n : ℕ) : (1 : ZMod 3) ∈ witnessProfile.middleSet n := by
  unfold TentProfile.middleSet TentProfile.nonLowSet
  change (1 : ZMod 3) ∈
    (Finset.univ.filter (fun j : ZMod 3 => ¬ |witnessFreq n j| ≤ 1)).filter
      (fun j => |witnessFreq n j| ≤ witnessX n ^ 3)
  rw [Finset.mem_filter, Finset.mem_filter]
  refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · rw [witnessFreq_one]
    norm_num
  · rw [witnessFreq_one]
    simpa using two_le_witnessX_cube n

theorem two_mem_tailSet (n : ℕ) : (2 : ZMod 3) ∈ witnessProfile.tailSet n := by
  unfold TentProfile.tailSet TentProfile.nonLowSet
  change (2 : ZMod 3) ∈
    (Finset.univ.filter (fun j : ZMod 3 => ¬ |witnessFreq n j| ≤ 1)).filter
      (fun j => ¬ |witnessFreq n j| ≤ witnessX n ^ 3)
  rw [Finset.mem_filter, Finset.mem_filter]
  refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · rw [witnessFreq_two]
    have hX0 : 0 < witnessX n := witnessX_pos n
    have h4 : 0 < witnessX n ^ 4 := pow_pos hX0 4
    rw [abs_of_pos h4]
    intro hle
    have h16 : (2 : ℝ) ^ 4 ≤ witnessX n ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (two_le_witnessX n) 4
    norm_num at h16
    linarith
  · rw [witnessFreq_two]
    have hX1 : 1 < witnessX n := witnessX_gt_one n
    have h4 : witnessX n ^ 3 < witnessX n ^ 4 := pow_lt_pow_right₀ hX1 (by norm_num)
    have hpos : 0 < witnessX n ^ 4 := pow_pos (lt_trans zero_lt_one hX1) 4
    rw [abs_of_pos hpos]
    intro hle
    exact absurd hle (not_le.mpr h4)

/-! ## Band energies: upper and lower bounds -/

theorem lowEnergy_le_totalEnergy (n : ℕ) :
    witnessProfile.lowEnergy n ≤ witnessProfile.totalEnergy n := by
  unfold TentProfile.lowEnergy TentProfile.totalEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => Complex.normSq_nonneg (witnessProfile.coeff n i))

theorem middleEnergy_le_totalEnergy (n : ℕ) :
    witnessProfile.middleEnergy n ≤ witnessProfile.totalEnergy n := by
  unfold TentProfile.middleEnergy TentProfile.middleSet TentProfile.nonLowSet
    TentProfile.totalEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    (fun i _ _ => Complex.normSq_nonneg (witnessProfile.coeff n i))

theorem tailEnergy_le_totalEnergy (n : ℕ) :
    witnessProfile.tailEnergy n ≤ witnessProfile.totalEnergy n := by
  unfold TentProfile.tailEnergy TentProfile.tailSet TentProfile.nonLowSet
    TentProfile.totalEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    (fun i _ _ => Complex.normSq_nonneg (witnessProfile.coeff n i))

theorem lowEnergy_ge_energy (n : ℕ) :
    witnessEnergy n ≤ witnessProfile.lowEnergy n := by
  unfold TentProfile.lowEnergy
  have h := Finset.single_le_sum
    (f := fun j : ZMod 3 => Complex.normSq (witnessProfile.coeff n j))
    (fun j _ => Complex.normSq_nonneg (witnessProfile.coeff n j))
    (zero_mem_lowSet n)
  simpa [witnessProfile, witness_normSq_amp, witnessAmp_sq] using h

theorem middleEnergy_ge_energy (n : ℕ) :
    witnessEnergy n ≤ witnessProfile.middleEnergy n := by
  unfold TentProfile.middleEnergy
  have h := Finset.single_le_sum
    (f := fun j : ZMod 3 => Complex.normSq (witnessProfile.coeff n j))
    (fun j _ => Complex.normSq_nonneg (witnessProfile.coeff n j))
    (one_mem_middleSet n)
  simpa [witnessProfile, witness_normSq_amp, witnessAmp_sq] using h

theorem tailEnergy_ge_energy (n : ℕ) :
    witnessEnergy n ≤ witnessProfile.tailEnergy n := by
  unfold TentProfile.tailEnergy
  have h := Finset.single_le_sum
    (f := fun j : ZMod 3 => Complex.normSq (witnessProfile.coeff n j))
    (fun j _ => Complex.normSq_nonneg (witnessProfile.coeff n j))
    (two_mem_tailSet n)
  simpa [witnessProfile, witness_normSq_amp, witnessAmp_sq] using h

theorem witness_lowEnergy_pos (n : ℕ) : 0 < witnessProfile.lowEnergy n :=
  lt_of_lt_of_le (witnessEnergy_pos n) (lowEnergy_ge_energy n)

theorem witness_middleEnergy_pos (n : ℕ) : 0 < witnessProfile.middleEnergy n :=
  lt_of_lt_of_le (witnessEnergy_pos n) (middleEnergy_ge_energy n)

theorem witness_tailEnergy_pos (n : ℕ) : 0 < witnessProfile.tailEnergy n :=
  lt_of_lt_of_le (witnessEnergy_pos n) (tailEnergy_ge_energy n)

/-! ## The sharp Plancherel / tent comparison -/

theorem witness_meanSquare_ge (n : ℕ) :
    3 * witnessEnergy n ≤
      (1 / (witnessProfile.N n : ℝ)) *
        ∑ i : Fin (witnessProfile.N n), (witnessProfile.deficit n i) ^ 2 := by
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin (witnessProfile.N n))),
      0 ≤ (witnessProfile.deficit n i) ^ 2 := fun i _ => sq_nonneg _
  have hsingle := Finset.single_le_sum hnonneg
    (Finset.mem_univ (witnessZeroIndex n))
  rw [witness_deficit_zero] at hsingle
  have hN : ((witnessProfile.N n : ℕ) : ℝ) = 3 := by
    rw [witnessProfile_N]
    norm_num
  have hkey : 3 * witnessEnergy n = (1 / 3) * (3 * witnessAmp n) ^ 2 := by
    rw [← witnessAmp_sq]
    ring
  rw [hN, hkey]
  exact mul_le_mul_of_nonneg_left hsingle (by norm_num)

/-- **The sharp tent comparison.**  The normalized mean square of the explicit
discrepancy profile equals the total coefficient energy, hence equals the sum
of the three band energies. -/
theorem witness_meanSquare_eq_totalEnergy (n : ℕ) :
    (1 / (witnessProfile.N n : ℝ)) *
        ∑ i : Fin (witnessProfile.N n), (witnessProfile.deficit n i) ^ 2 =
      witnessProfile.totalEnergy n := by
  have hle : (1 / (witnessProfile.N n : ℝ)) *
        ∑ i : Fin (witnessProfile.N n), (witnessProfile.deficit n i) ^ 2
      ≤ witnessProfile.totalEnergy n := by
    have h := witnessProfile.meanSquare_le_energy n
    rwa [TentProfile.energy_split] at h
  have hge : witnessProfile.totalEnergy n ≤
      (1 / (witnessProfile.N n : ℝ)) *
        ∑ i : Fin (witnessProfile.N n), (witnessProfile.deficit n i) ^ 2 := by
    rw [witness_totalEnergy]
    exact witness_meanSquare_ge n
  exact le_antisymm hle hge

/-- The band form of the sharp comparison, exactly the `tentMeanSquare` shape
of `L21_2FourierInputs`. -/
theorem witness_tentComparison (n : ℕ) :
    (1 / (witnessProfile.N n : ℝ)) *
        ∑ i : Fin (witnessProfile.N n), (witnessProfile.deficit n i) ^ 2 =
      witnessProfile.lowEnergy n + witnessProfile.middleEnergy n +
        witnessProfile.tailEnergy n := by
  rw [TentProfile.energy_split]
  exact witness_meanSquare_eq_totalEnergy n

theorem witness_meanSquare_pos (n : ℕ) :
    0 < (1 / (witnessProfile.N n : ℝ)) *
        ∑ i : Fin (witnessProfile.N n), (witnessProfile.deficit n i) ^ 2 := by
  have hge := witness_meanSquare_ge n
  have he : 0 < witnessEnergy n := witnessEnergy_pos n
  nlinarith

/-! ## The three Fourier band bounds -/

/-- Absorption of the factor `3` and the band exponent: for every real `A`,
`3 exp (-(T_X n)²) ≤ exp (-A T_X n)` eventually, because `T_X n → ∞`. -/
theorem eventually_three_mul_energy_le_exp (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, 3 * witnessEnergy n ≤ Real.exp (-A * witnessRate n) := by
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      Real.log 3 + 1 + max A 0 ≤ witnessRate n :=
    witnessRate_grows.eventually_ge_atTop _
  filter_upwards [hthreshold] with n hn
  have hR0 : 0 ≤ witnessRate n := witnessRate_nonneg n
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hM0 : (0 : ℝ) ≤ max A 0 := le_max_right A 0
  have hMA : A ≤ max A 0 := le_max_left A 0
  have hR1 : 1 ≤ witnessRate n := by linarith
  have hRlog : Real.log 3 ≤ witnessRate n := by linarith
  have hexp : Real.log 3 - (witnessRate n) ^ 2 ≤ -A * witnessRate n := by
    by_cases hA : 0 ≤ A
    · have hRA : A + 1 ≤ witnessRate n := by linarith
      have hquad : Real.log 3 ≤ witnessRate n ^ 2 - A * witnessRate n := by
        have hfac : 1 ≤ witnessRate n - A := by linarith
        have hmul : witnessRate n ≤ witnessRate n * (witnessRate n - A) := by
          calc witnessRate n = witnessRate n * 1 := (mul_one _).symm
            _ ≤ witnessRate n * (witnessRate n - A) :=
              mul_le_mul_of_nonneg_left hfac hR0
        nlinarith
      linarith
    · have hAneg : A < 0 := lt_of_not_ge hA
      have hsq : Real.log 3 ≤ witnessRate n ^ 2 := by nlinarith
      have hneg : 0 ≤ -A * witnessRate n :=
        mul_nonneg (by linarith) hR0
      nlinarith
  have hExpLe : Real.exp (Real.log 3 - (witnessRate n) ^ 2) ≤
      Real.exp (-A * witnessRate n) := Real.exp_le_exp.mpr hexp
  have hExpEq : Real.exp (Real.log 3 - (witnessRate n) ^ 2) =
      3 * witnessEnergy n := by
    have harg : Real.log 3 - (witnessRate n) ^ 2 =
        Real.log 3 + -(witnessRate n) ^ 2 := by ring
    rw [harg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    unfold witnessEnergy
    ring
  rw [hExpEq] at hExpLe
  exact hExpLe

/-- **Low-frequency bound** (`|t| ≤ 1`) for the explicit profile. -/
theorem witness_fourierLow (c : ℝ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      witnessProfile.lowEnergy n ≤
        Real.exp (-(((2 * c) / 3) - δ) * paperRate witnessProfile.X n) := by
  intro δ hδ
  filter_upwards [eventually_three_mul_energy_le_exp ((2 * c) / 3 - δ)] with n hn
  calc witnessProfile.lowEnergy n ≤ witnessProfile.totalEnergy n :=
        lowEnergy_le_totalEnergy n
    _ = 3 * witnessEnergy n := witness_totalEnergy n
    _ ≤ Real.exp (-(((2 * c) / 3) - δ) * witnessRate n) := hn
    _ = Real.exp (-(((2 * c) / 3) - δ) * paperRate witnessProfile.X n) := by
        rw [witnessRate_paperRate n]

/-- **Middle-frequency bound** (`1 < |t| ≤ X³`) for the explicit profile. -/
theorem witness_fourierMiddle (c : ℝ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      witnessProfile.middleEnergy n ≤
        Real.exp (-((1 / c) - δ) * paperRate witnessProfile.X n) := by
  intro δ hδ
  filter_upwards [eventually_three_mul_energy_le_exp (1 / c - δ)] with n hn
  calc witnessProfile.middleEnergy n ≤ witnessProfile.totalEnergy n :=
        middleEnergy_le_totalEnergy n
    _ = 3 * witnessEnergy n := witness_totalEnergy n
    _ ≤ Real.exp (-((1 / c) - δ) * witnessRate n) := hn
    _ = Real.exp (-((1 / c) - δ) * paperRate witnessProfile.X n) := by
        rw [witnessRate_paperRate n]

/-- **High-frequency bound** (`|t| > X³`) for the explicit profile. -/
theorem witness_fourierTail :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      witnessProfile.tailEnergy n ≤
        Real.exp (-δ * paperRate witnessProfile.X n) := by
  intro δ hδ
  filter_upwards [eventually_three_mul_energy_le_exp δ] with n hn
  calc witnessProfile.tailEnergy n ≤ witnessProfile.totalEnergy n :=
        tailEnergy_le_totalEnergy n
    _ = 3 * witnessEnergy n := witness_totalEnergy n
    _ ≤ Real.exp (-δ * witnessRate n) := hn
    _ = Real.exp (-δ * paperRate witnessProfile.X n) := by
        rw [witnessRate_paperRate n]

/-! ## The bad-set fraction -/

/-- The bad sampled centres at a threshold sequence `τ`.  With
`τ = chebThreshold X c` this is exactly `L21_2FourierInputs.badSet`. -/
def witnessBadSet (τ : ℕ → ℝ) (n : ℕ) :
    Finset (Fin (witnessProfile.N n)) :=
  Finset.univ.filter (fun i => τ n ≤ |witnessProfile.deficit n i|)

/-- The bad-set fraction `#bad / N`. -/
def witnessBadFraction (τ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((witnessBadSet τ n).card : ℝ) / (witnessProfile.N n : ℝ)

/-- The leaf's loss numerator `(#bad / N) * (X + 1)`. -/
def witnessBadCount (τ : ℕ → ℝ) (n : ℕ) : ℝ :=
  witnessBadFraction τ n * (witnessProfile.X n + 1)

/-- The Chebyshev threshold `a_n` makes the zero-frequency sample bad. -/
theorem witness_badSet_nonempty (n : ℕ) :
    (witnessBadSet (fun m => witnessAmp m) n).Nonempty := by
  refine ⟨witnessZeroIndex n, ?_⟩
  rw [witnessBadSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [witness_deficit_zero]
  have hpos : 0 < witnessAmp n := witnessAmp_pos n
  rw [abs_of_pos (by positivity : 0 < 3 * witnessAmp n)]
  linarith

/-- The bad-set fraction at the Chebyshev threshold `a_n` is at least `1/3`. -/
theorem witness_badFraction_ge_third (n : ℕ) :
    (1 / 3 : ℝ) ≤ witnessBadFraction (fun m => witnessAmp m) n := by
  unfold witnessBadFraction
  have hcard : 1 ≤ (witnessBadSet (fun m => witnessAmp m) n).card :=
    Finset.card_pos.mpr (witness_badSet_nonempty n)
  have hN : ((witnessProfile.N n : ℕ) : ℝ) = 3 := by
    rw [witnessProfile_N]
    norm_num
  rw [hN]
  have hcardR : (1 : ℝ) ≤ ((witnessBadSet (fun m => witnessAmp m) n).card : ℝ) := by
    exact_mod_cast hcard
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith

theorem witness_badFraction_pos (n : ℕ) :
    0 < witnessBadFraction (fun m => witnessAmp m) n :=
  lt_of_lt_of_le (by norm_num) (witness_badFraction_ge_third n)

/-- Every threshold `0 < τ ≤ 3 a_n` makes the zero-frequency sample bad, so the
corresponding bad fraction is strictly positive.  This isolates the counting
from the particular threshold scale. -/
theorem witness_badFraction_pos_of_le (τ : ℕ → ℝ) (n : ℕ)
    (_hτ0 : 0 < τ n) (hτ : τ n ≤ 3 * witnessAmp n) :
    0 < witnessBadFraction τ n := by
  have hmem : witnessZeroIndex n ∈ witnessBadSet τ n := by
    rw [witnessBadSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [witness_deficit_zero]
    have h3 : 0 < 3 * witnessAmp n := by
      have := witnessAmp_pos n
      linarith
    rw [abs_of_pos h3]
    exact hτ
  have hcard : 0 < (witnessBadSet τ n).card := Finset.card_pos.mpr ⟨_, hmem⟩
  unfold witnessBadFraction
  have hN : (0 : ℝ) < witnessProfile.N n := by
    exact_mod_cast witnessProfile.N_pos n
  exact div_pos (by exact_mod_cast hcard) hN

/-- The finite Markov/Chebyshev bound for the explicit profile, exactly the
step used by `L21_2FourierInputs.tentChebyshev`. -/
theorem witness_badFraction_le_markov (τ : ℕ → ℝ) (n : ℕ) (hτ : 0 < τ n) :
    witnessBadFraction τ n ≤
      (1 / (τ n) ^ 2) *
        ((1 / (witnessProfile.N n : ℝ)) *
          ∑ i : Fin (witnessProfile.N n), (witnessProfile.deficit n i) ^ 2) :=
  card_le_energy (witnessProfile.N_pos n) (witnessProfile.deficit n) hτ

/-- The loss shape `badCount / (X + 1)` is exactly the bad-set fraction. -/
theorem witness_badCount_div (τ : ℕ → ℝ) (n : ℕ) :
    witnessBadCount τ n / (witnessProfile.X n + 1) = witnessBadFraction τ n := by
  unfold witnessBadCount
  have hX : witnessProfile.X n + 1 ≠ 0 := by
    have h1 : 1 < witnessProfile.X n := witnessX_gt_one n
    linarith
  field_simp

theorem witness_badCount_nonneg (τ : ℕ → ℝ) (n : ℕ) :
    0 ≤ witnessBadCount τ n := by
  unfold witnessBadCount witnessBadFraction
  have hN : (0 : ℝ) < witnessProfile.N n := by exact_mod_cast witnessProfile.N_pos n
  have hX : 0 ≤ witnessProfile.X n + 1 := by
    have h1 : 1 < witnessProfile.X n := witnessX_gt_one n
    linarith
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN.le) hX

/-- **The loss is a genuine positive fraction.**  Since `badCount / (X + 1)`
is the bad fraction and that fraction is at least `1/3`, the L21.2 loss built
from this profile is strictly positive at every band index `n`. -/
theorem witness_badCount_div_pos (n : ℕ) :
    0 < witnessBadCount (fun m => witnessAmp m) n / (witnessProfile.X n + 1) := by
  rw [witness_badCount_div]
  exact witness_badFraction_pos n

/-! ## The packaged witness -/

/-- **The Fourier part of the L21.2 leaf, witnessed.**  It carries the explicit
profile together with the sharp Plancherel/tent comparison, the strict
positivity of the mean square and all three band energies, the three
frequency-band bounds, and a positive bad-set fraction. -/
structure FourierWitness where
  /-- The explicit discrepancy profile. -/
  profile : TentProfile
  /-- The stage-one constant at which the band bounds hold. -/
  c : ℝ
  /-- The sharp finite Plancherel/tent comparison. -/
  tentComparison : ∀ n : ℕ,
    (1 / (profile.N n : ℝ)) * ∑ i : Fin (profile.N n), (profile.deficit n i) ^ 2 ≤
      profile.lowEnergy n + profile.middleEnergy n + profile.tailEnergy n
  /-- The mean square is genuinely nonzero. -/
  meanSquare_pos : ∀ n : ℕ,
    0 < (1 / (profile.N n : ℝ)) * ∑ i : Fin (profile.N n), (profile.deficit n i) ^ 2
  /-- All three bands carry positive energy. -/
  low_pos : ∀ n : ℕ, 0 < profile.lowEnergy n
  middle_pos : ∀ n : ℕ, 0 < profile.middleEnergy n
  tail_pos : ∀ n : ℕ, 0 < profile.tailEnergy n
  /-- Low-frequency bound. -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.lowEnergy n ≤
      Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n)
  /-- Middle-frequency bound. -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.middleEnergy n ≤
      Real.exp (-((1 / c) - δ) * paperRate profile.X n)
  /-- High-frequency bound. -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n)
  /-- The bad-set fraction. -/
  badFraction : ℕ → ℝ
  badFraction_pos : ∀ n : ℕ, 0 < badFraction n
  badFraction_ge_third : ∀ n : ℕ, (1 / 3 : ℝ) ≤ badFraction n
  /-- The leaf's loss shape, identified with the bad fraction. -/
  loss : ℕ → ℝ
  loss_pos : ∀ n : ℕ, 0 < loss n
  loss_eq_badFraction : ∀ n : ℕ, loss n = badFraction n

/-- **The concrete Fourier witness.**  `c = 1` is the value at which the
record is instantiated; the three band bounds are proved for this `c` (and in
fact the separate theorems above hold for every `c`). -/
def concreteFourierWitness : FourierWitness where
  profile := witnessProfile
  c := 1
  tentComparison := fun n => witnessProfile.tentMeanSquare n
  meanSquare_pos := witness_meanSquare_pos
  low_pos := witness_lowEnergy_pos
  middle_pos := witness_middleEnergy_pos
  tail_pos := witness_tailEnergy_pos
  fourierLow := witness_fourierLow 1
  fourierMiddle := witness_fourierMiddle 1
  fourierTail := witness_fourierTail
  badFraction := witnessBadFraction (fun m => witnessAmp m)
  badFraction_pos := witness_badFraction_pos
  badFraction_ge_third := witness_badFraction_ge_third
  loss := witnessBadCount (fun m => witnessAmp m) /
    (fun n => witnessProfile.X n + 1)
  loss_pos := witness_badCount_div_pos
  loss_eq_badFraction := fun n => witness_badCount_div (fun m => witnessAmp m) n

/-- The concrete witness has a profile with three sampled centres. -/
theorem concrete_profile_N (n : ℕ) : concreteFourierWitness.profile.N n = 3 := rfl

/-- The concrete witness's discrepancy mean square equals the band energy
sum. -/
theorem concrete_moment_identity (n : ℕ) :
    (1 / (concreteFourierWitness.profile.N n : ℝ)) *
        ∑ i : Fin (concreteFourierWitness.profile.N n),
          (concreteFourierWitness.profile.deficit n i) ^ 2 =
      concreteFourierWitness.profile.lowEnergy n +
        concreteFourierWitness.profile.middleEnergy n +
        concreteFourierWitness.profile.tailEnergy n :=
  witness_tentComparison n

/-- The concrete loss is exactly the leaf's `badCount / (X + 1)` for the
explicit profile and the Chebyshev-scale threshold `a_n`. -/
theorem concrete_loss_eq (n : ℕ) :
    concreteFourierWitness.loss n =
      witnessBadCount (fun m => witnessAmp m) n / (witnessProfile.X n + 1) := rfl

/-- The concrete loss is a genuine positive fraction, bounded below by `1/3`
after division by `X + 1`. -/
theorem concrete_loss_pos (n : ℕ) : 0 < concreteFourierWitness.loss n :=
  concreteFourierWitness.loss_pos n

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2TentWitness.witness_dft_zero
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_deficit_zero
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_totalEnergy
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_meanSquare_eq_totalEnergy
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_tentComparison
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_lowEnergy_pos
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_middleEnergy_pos
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_tailEnergy_pos
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_fourierLow
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_fourierMiddle
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_fourierTail
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_badFraction_ge_third
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_badFraction_pos_of_le
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_badFraction_le_markov
#print axioms Cogentic.RandomizedL21_2TentWitness.witness_badCount_div_pos
#print axioms Cogentic.RandomizedL21_2TentWitness.concreteFourierWitness
#print axioms Cogentic.RandomizedL21_2TentWitness.concrete_loss_pos

end Cogentic.RandomizedL21_2TentWitness
