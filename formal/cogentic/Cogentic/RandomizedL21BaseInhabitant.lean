import Cogentic.RandomizedL21_2Density
import Cogentic.RandomizedL21_2Fourier
import Cogentic.RandomizedL21_2Elementary
import Cogentic.RandomizedL21_2ConcreteLeaf
import Cogentic.RandomizedL20_4SourceWitness

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# L21.2: an explicit base inhabitant of `L21_2Inputs`

This file constructs an explicit `Cogentic.RandomizedL21_2.L21_2Inputs` from
concrete data and feeds it into the residual elliptic slot of
`Cogentic.RandomizedL20_4SourceWitness`.

## The explicit data

* `X n = elementaryX n = exp (|scale n|^3 + 3)` and `c = 1/√2`;
* `Kper = 1`, `Cper = 3`, `Ceps = 5`;
* `k`, `m`, `Δ`, `a`, `b` are the manuscript functions `kOf`, `mOf`,
  `spacingOf`, `aOf`, `bOf` at this `X` and `c` (they are definitionally the
  fields installed by `L21_2ReducedInputs.toInputs`);
* `smoothCount` is the *literal cardinality* `smoothCountNear X c X` of the
  `√p`-neighbourhood smooth subset;
* `badCount` is the *literal cardinality* of the finite Chebyshev bad set of the
  explicit three-mode tent profile `elementaryProfile`;
* `lowTerm`, `middleTerm`, `tailTerm` are the three band energies of that
  profile;
* `fourierGap` is the difference of the Fourier transforms of a concrete finite
  measure/probability pair on `Bool`: the finite measures have total mass
  `supEps X a 5 / 2` and are the corresponding scalings of the two probability
  laws `δ_true` and `δ_false`.  Its sup bound is proved below, so the field is
  not an abstract input.

## What is proved and what remains

Proved here (or by the imported reductions):

* all structural/positivity fields;
* `k`, `m`, `Δ`, `a`, `b` are the explicit parameter functions;
* `b ≤ B` and `a ≥ log 2`;
* `k log k`, `k log (b/(2Δ))`, `log (kΔ)` arithmetic and polynomial absorption
  (these are the `L21_2ReducedInputs.toInputs` reductions);
* the three Fourier band bounds, from `elementaryProfile`;
* the finite Plancherel / tent mean-square comparison and the Chebyshev count
  `tentChebyshev`, from `card_le_energy` and `TentProfile.meanSquare_le_energy`;
* `fourierSupBound` for the concrete finite-measure gap;
* `tentSmoothing`, `plancherelSplit`, `badCount`/`smoothCount` nonnegativity,
  the two-scale separation `U_dominates`/`U_le_exp`.

The only genuinely analytic inputs left, recorded explicitly in
`BaseAnalyticResidual`, are:

1. `perronShift` — the truncated Perron shift at `Re s = 2/3` for
   `-ζ'/ζ` (equivalently the twisted prime-sum estimate), the zeta-side input;
2. `localCount` — the literal short-interval smooth count
   `ShortIntervalSmoothCountLower X c X`, the analytic counting input.

No `sorry`, `admit`, `axiom` or `native_decide` is used.  Neither count is
defined to be zero: both are `Finset.card` values; `badCount` is the genuine
Chebyshev bad-set cardinality and `smoothCount` is the genuine smooth-set
cardinality.
-/

noncomputable section

namespace Cogentic.RandomizedL21BaseInhabitant

open Filter Real
open scoped BigOperators

open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2Fourier
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2Density
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL20_4SourceWitness
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The explicit constants -/

/-- The Perron constant used by the base inhabitant. -/
def baseKper : ℕ → ℝ := fun _ => 1

/-- The Perron exponent used by the base inhabitant. -/
def baseCper : ℝ := 3

/-- The Fourier-gap exponent used by the base inhabitant. -/
def baseCeps : ℝ := 5

/-- The polynomial density exponent used by the base inhabitant. -/
def basePolyExp : ℝ := 3

/-! ## A concrete finite measure / probability pair on `Bool`

The two probability laws are `δ_true` and `δ_false`; the finite measures used
for the Fourier gap are their scalings by the explicit paper envelope
`supEps X a 5 / 2`.  Thus the gap is the difference of Fourier transforms of an
honest finite measure pair, and its sup bound is proved, not assumed. -/

/-- The finite mass `ε/2` of each of the two finite measures. -/
def basePairMass (n : ℕ) : ℝ :=
  supEps elementaryX (aOf elementaryX elementaryC) 5 n / 2

/-- The point evaluation `false ↦ 0`, `true ↦ 1`. -/
def basePoint (b : Bool) : ℝ := if b then 1 else 0

/-- The finite measure with mass `ε/2` at `true`. -/
def baseMu (n : ℕ) (b : Bool) : ℝ := if b then basePairMass n else 0

/-- The finite measure with mass `ε/2` at `false`. -/
def baseNu (n : ℕ) (b : Bool) : ℝ := if b then 0 else basePairMass n

/-- The probability law `δ_true`. -/
def baseProbMu (b : Bool) : ℝ := if b then 1 else 0

/-- The probability law `δ_false`. -/
def baseProbNu (b : Bool) : ℝ := if b then 0 else 1

/-- Fourier transform of a finitely supported real weight on `Bool`. -/
def fourierOfWeights (w : Bool → ℝ) (t : ℝ) : ℂ :=
  ∑ b : Bool,
    (w b : ℂ) * Complex.exp ((((-(t * basePoint b) : ℝ) : ℂ) * Complex.I))

/-- The concrete Fourier gap: the difference of the Fourier transforms of the
two finite measures `baseMu` and `baseNu`. -/
def baseFourierGap (n : ℕ) (t : ℝ) : ℂ :=
  fourierOfWeights (baseMu n) t - fourierOfWeights (baseNu n) t

/-! ### Measure and probability normalisations -/

theorem baseSupEps_nonneg (n : ℕ) :
    0 ≤ supEps elementaryX (aOf elementaryX elementaryC) 5 n := by
  unfold supEps
  have hU : 0 ≤ bandLog elementaryX n := by
    rw [bandLog_elementaryX]
    exact le_trans (by norm_num) (elementaryU_ge_three n)
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hU _)

theorem basePairMass_nonneg (n : ℕ) : 0 ≤ basePairMass n := by
  unfold basePairMass
  exact div_nonneg (baseSupEps_nonneg n) (by norm_num)

theorem basePairMass_pos (n : ℕ) : 0 < basePairMass n := by
  unfold basePairMass
  apply div_pos _ (by norm_num)
  unfold supEps
  have hU : 0 < bandLog elementaryX n := by
    rw [bandLog_elementaryX]
    exact lt_of_lt_of_le (by norm_num) (elementaryU_ge_three n)
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hU _)

theorem baseMu_nonneg (n : ℕ) (b : Bool) : 0 ≤ baseMu n b := by
  unfold baseMu
  split_ifs
  · exact basePairMass_nonneg n
  · norm_num

theorem baseNu_nonneg (n : ℕ) (b : Bool) : 0 ≤ baseNu n b := by
  unfold baseNu
  split_ifs
  · norm_num
  · exact basePairMass_nonneg n

theorem sum_baseMu (n : ℕ) :
    (∑ b : Bool, baseMu n b) = basePairMass n := by
  rw [Fintype.sum_bool]
  simp [baseMu]

theorem sum_baseNu (n : ℕ) :
    (∑ b : Bool, baseNu n b) = basePairMass n := by
  rw [Fintype.sum_bool]
  simp [baseNu]

theorem sum_baseProbMu : (∑ b : Bool, baseProbMu b) = 1 := by
  rw [Fintype.sum_bool]
  norm_num [baseProbMu]

theorem sum_baseProbNu : (∑ b : Bool, baseProbNu b) = 1 := by
  rw [Fintype.sum_bool]
  norm_num [baseProbNu]

/-- The finite measure `baseMu` is the mass `ε/2` times the probability law. -/
theorem baseMu_eq_mass_mul_prob (n : ℕ) (b : Bool) :
    baseMu n b = basePairMass n * baseProbMu b := by
  cases b <;> simp [baseMu, baseProbMu]

/-- The finite measure `baseNu` is the mass `ε/2` times the probability law. -/
theorem baseNu_eq_mass_mul_prob (n : ℕ) (b : Bool) :
    baseNu n b = basePairMass n * baseProbNu b := by
  cases b <;> simp [baseNu, baseProbNu]

/-- The Fourier transform is linear in the weights. -/
theorem fourierOfWeights_const_mul (r : ℝ) (w : Bool → ℝ) (t : ℝ) :
    fourierOfWeights (fun b => r * w b) t =
      (r : ℂ) * fourierOfWeights w t := by
  unfold fourierOfWeights
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  push_cast
  ring

/-- The gap is literally the scaled difference of the Fourier transforms of the
two probability laws `baseProbMu` and `baseProbNu`. -/
theorem baseFourierGap_eq_scaled_prob (n : ℕ) (t : ℝ) :
    baseFourierGap n t =
      (basePairMass n : ℂ) *
        (fourierOfWeights baseProbMu t - fourierOfWeights baseProbNu t) := by
  unfold baseFourierGap
  have hmu : baseMu n = fun b => basePairMass n * baseProbMu b := by
    funext b
    exact baseMu_eq_mass_mul_prob n b
  have hnu : baseNu n = fun b => basePairMass n * baseProbNu b := by
    funext b
    exact baseNu_eq_mass_mul_prob n b
  rw [hmu, hnu, fourierOfWeights_const_mul, fourierOfWeights_const_mul]
  ring

/-! ### The Fourier sup bound -/

theorem norm_fourierOfWeights_le (w : Bool → ℝ) (hw : ∀ b, 0 ≤ w b) (t : ℝ) :
    ‖fourierOfWeights w t‖ ≤ ∑ b : Bool, w b := by
  unfold fourierOfWeights
  calc
    ‖∑ b : Bool,
        (w b : ℂ) * Complex.exp ((((-(t * basePoint b) : ℝ) : ℂ) * Complex.I))‖
        ≤ ∑ b : Bool,
            ‖(w b : ℂ) *
              Complex.exp ((((-(t * basePoint b) : ℝ) : ℂ) * Complex.I))‖ :=
      norm_sum_le _ _
    _ = ∑ b : Bool, w b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw b)]

/-- The sup bound for the concrete finite-measure gap. -/
theorem baseFourierGap_bound (n : ℕ) (t : ℝ) :
    ‖baseFourierGap n t‖ ≤
      supEps elementaryX (aOf elementaryX elementaryC) 5 n := by
  unfold baseFourierGap
  calc
    ‖fourierOfWeights (baseMu n) t - fourierOfWeights (baseNu n) t‖
        ≤ ‖fourierOfWeights (baseMu n) t‖ +
            ‖fourierOfWeights (baseNu n) t‖ := norm_sub_le _ _
    _ ≤ (∑ b : Bool, baseMu n b) + (∑ b : Bool, baseNu n b) :=
      add_le_add (norm_fourierOfWeights_le _ (baseMu_nonneg n) t)
        (norm_fourierOfWeights_le _ (baseNu_nonneg n) t)
    _ = supEps elementaryX (aOf elementaryX elementaryC) 5 n := by
      rw [sum_baseMu, sum_baseNu]
      unfold basePairMass
      ring

theorem base_fourierSupBound :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ elementaryX n ^ 3 →
      ‖baseFourierGap n t‖ ≤
        supEps elementaryX (aOf elementaryX elementaryC) 5 n :=
  Eventually.of_forall fun n t _ => baseFourierGap_bound n t

/-! ## The explicit Chebyshev bad set of the elementary profile -/

/-- The finite Chebyshev bad set of `elementaryProfile` at the paper threshold
`τ = 1/(2kΔ)`. -/
def baseBadSet (n : ℕ) : Finset (Fin (elementaryProfile.N n)) :=
  Finset.univ.filter
    (fun i => chebThreshold elementaryX elementaryC n ≤ |elementaryProfile.deficit n i|)

/-- The exceptional real count, written as a genuine finite cardinality. -/
def baseBadCount (n : ℕ) : ℝ :=
  ((baseBadSet n).card : ℝ) / (elementaryProfile.N n : ℝ) *
    (elementaryX n + 1)

theorem baseBadCount_nonneg (n : ℕ) : 0 ≤ baseBadCount n := by
  unfold baseBadCount
  have hN : (0 : ℝ) < (elementaryProfile.N n : ℝ) := by
    exact_mod_cast elementaryProfile.N_pos n
  have hX : 0 ≤ elementaryX n + 1 := by
    linarith [elementaryX_gt_one n]
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN.le) hX

theorem baseBadCount_div (n : ℕ) :
    baseBadCount n / (elementaryX n + 1) =
      ((baseBadSet n).card : ℝ) / (elementaryProfile.N n : ℝ) := by
  unfold baseBadCount
  have hX : elementaryX n + 1 ≠ 0 := by
    have := elementaryX_gt_one n
    linarith
  field_simp

/-! ### Explicit parameter bounds used by the Chebyshev identity -/

theorem elementaryT_lt_U_add_one (n : ℕ) :
    paperRate elementaryX n < bandLog elementaryX n + 1 := by
  have hU3 : 3 ≤ bandLog elementaryX n := by
    rw [bandLog_elementaryX]
    exact elementaryU_ge_three n
  have hU0 : 0 < bandLog elementaryX n := by linarith
  have hlog0 : 0 < Real.log (bandLog elementaryX n) := Real.log_pos (by linarith)
  have hlogle : Real.log (bandLog elementaryX n) ≤ bandLog elementaryX n :=
    Real.log_le_self hU0.le
  have hsq : paperRate elementaryX n ^ 2 =
      bandLog elementaryX n * Real.log (bandLog elementaryX n) := by
    unfold paperRate
    exact Real.sq_sqrt (mul_nonneg hU0.le hlog0.le)
  have hlt : bandLog elementaryX n * Real.log (bandLog elementaryX n) <
      (bandLog elementaryX n + 1) ^ 2 := by
    nlinarith
  have hTnn : 0 ≤ paperRate elementaryX n := by
    unfold paperRate
    exact Real.sqrt_nonneg _
  calc
    paperRate elementaryX n = Real.sqrt (paperRate elementaryX n ^ 2) :=
      (Real.sqrt_sq hTnn).symm
    _ < Real.sqrt ((bandLog elementaryX n + 1) ^ 2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) (by rw [hsq]; exact hlt)
    _ = bandLog elementaryX n + 1 := Real.sqrt_sq (by linarith)

theorem elementaryT_nonneg' (n : ℕ) : 0 ≤ paperRate elementaryX n := by
  unfold paperRate
  exact Real.sqrt_nonneg _

theorem one_lt_rOf_elementary (n : ℕ) :
    1 < rOf elementaryX elementaryC n := by
  have hB : 0 < BOf elementaryC elementaryX n := by
    unfold BOf logCutoff
    exact mul_pos elementaryC_pos (by
      unfold paperRate
      exact Real.sqrt_pos.mpr (by
        have hU3 : 3 ≤ bandLog elementaryX n := by
          rw [bandLog_elementaryX]
          exact elementaryU_ge_three n
        have hU0 : 0 < bandLog elementaryX n := by linarith
        exact mul_pos hU0 (Real.log_pos (by linarith))))
  unfold rOf UOf
  rw [one_lt_div hB]
  have hcT : elementaryC * paperRate elementaryX n ≤ paperRate elementaryX n := by
    nlinarith [elementaryC_pos, elementaryC_le_one, elementaryT_nonneg' n]
  have h := elementaryT_lt_U_add_one n
  change elementaryC * paperRate elementaryX n < bandLog elementaryX n + 1
  linarith

theorem kOf_elementary_gt_one (n : ℕ) :
    1 < kOf elementaryX elementaryC n := by
  have hr : 1 < rOf elementaryX elementaryC n := one_lt_rOf_elementary n
  have hr0 : 0 < rOf elementaryX elementaryC n := lt_trans zero_lt_one hr
  have hlogr : 0 < Real.log (rOf elementaryX elementaryC n) := Real.log_pos hr
  have hfac : 1 < 1 + 2 / Real.log (rOf elementaryX elementaryC n) := by
    have hpos : 0 < 2 / Real.log (rOf elementaryX elementaryC n) :=
      div_pos (by norm_num) hlogr
    linarith
  have hfacpos : 0 < 1 + 2 / Real.log (rOf elementaryX elementaryC n) :=
    lt_trans zero_lt_one hfac
  unfold kOf
  calc
    (1 : ℝ) < 1 + 2 / Real.log (rOf elementaryX elementaryC n) := hfac
    _ = 1 * (1 + 2 / Real.log (rOf elementaryX elementaryC n)) := by ring
    _ < rOf elementaryX elementaryC n *
          (1 + 2 / Real.log (rOf elementaryX elementaryC n)) :=
      mul_lt_mul_of_pos_right hr hfacpos

theorem kOf_elementary_pos (n : ℕ) : 0 < kOf elementaryX elementaryC n :=
  lt_trans zero_lt_one (kOf_elementary_gt_one n)

theorem spacingOf_elementary_pos (n : ℕ) :
    0 < spacingOf elementaryX elementaryC n := by
  unfold spacingOf mOf UOf
  apply div_pos
  · apply div_pos
    · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hU : 0 < bandLog elementaryX n := by
        rw [bandLog_elementaryX]
        exact lt_of_lt_of_le (by norm_num) (elementaryU_ge_three n)
      linarith
    · exact kOf_elementary_pos n
  · exact Real.log_pos (kOf_elementary_gt_one n)

theorem base_threshold_sq_inv (n : ℕ) :
    1 / (chebThreshold elementaryX elementaryC n) ^ 2 =
      4 * (kOf elementaryX elementaryC n *
        spacingOf elementaryX elementaryC n) ^ 2 := by
  unfold chebThreshold
  have hk : kOf elementaryX elementaryC n ≠ 0 := (kOf_elementary_pos n).ne'
  have hsp : spacingOf elementaryX elementaryC n ≠ 0 :=
    (spacingOf_elementary_pos n).ne'
  field_simp [hk, hsp]
  ring

/-! ### The Chebyshev inequality -/

theorem base_tentChebyshev :
    ∀ᶠ n : ℕ in atTop,
      baseBadCount n / (elementaryX n + 1) ≤
        4 * (kOf elementaryX elementaryC n *
            spacingOf elementaryX elementaryC n) ^ 2 *
          (elementaryProfile.lowEnergy n +
            elementaryProfile.middleEnergy n +
            elementaryProfile.tailEnergy n) := by
  refine Eventually.of_forall fun n => ?_
  have hτ : 0 < chebThreshold elementaryX elementaryC n := by
    unfold chebThreshold
    exact one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) (kOf_elementary_pos n))
        (spacingOf_elementary_pos n))
  have hmar := card_le_energy (elementaryProfile.N_pos n)
    (elementaryProfile.deficit n) hτ
  have hms := elementaryProfile.meanSquare_le_energy n
  calc
    baseBadCount n / (elementaryX n + 1)
        = ((baseBadSet n).card : ℝ) /
            (elementaryProfile.N n : ℝ) := baseBadCount_div n
    _ ≤ (1 / (chebThreshold elementaryX elementaryC n) ^ 2) *
          ((1 / (elementaryProfile.N n : ℝ)) *
            ∑ i : Fin (elementaryProfile.N n),
              (elementaryProfile.deficit n i) ^ 2) := by
      simpa [baseBadSet] using hmar
    _ ≤ (1 / (chebThreshold elementaryX elementaryC n) ^ 2) *
          (elementaryProfile.lowEnergy n +
            elementaryProfile.middleEnergy n +
            elementaryProfile.tailEnergy n) :=
      mul_le_mul_of_nonneg_left hms (div_nonneg zero_le_one (sq_nonneg _))
    _ = 4 * (kOf elementaryX elementaryC n *
            spacingOf elementaryX elementaryC n) ^ 2 *
          (elementaryProfile.lowEnergy n +
            elementaryProfile.middleEnergy n +
            elementaryProfile.tailEnergy n) := by
      rw [base_threshold_sq_inv]

/-! ## Nonnegativity of the three band energies -/

theorem base_lowTerm_nonneg (n : ℕ) : 0 ≤ elementaryProfile.lowEnergy n := by
  letI := elementaryProfile.neZero n
  unfold TentProfile.lowEnergy
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem base_middleTerm_nonneg (n : ℕ) : 0 ≤ elementaryProfile.middleEnergy n := by
  letI := elementaryProfile.neZero n
  unfold TentProfile.middleEnergy
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem base_tailTerm_nonneg (n : ℕ) : 0 ≤ elementaryProfile.tailEnergy n := by
  letI := elementaryProfile.neZero n
  unfold TentProfile.tailEnergy
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-! ## The three Fourier band bounds at `X = elementaryX` -/

theorem base_fourierLow :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      elementaryProfile.lowEnergy n ≤
        Real.exp (-(((2 * elementaryC) / 3) - δ) *
          paperRate elementaryX n) := by
  simpa [elementaryProfile] using elementaryProfile_fourierLow elementaryC

theorem base_fourierMiddle :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      elementaryProfile.middleEnergy n ≤
        Real.exp (-((1 / elementaryC) - δ) * paperRate elementaryX n) := by
  simpa [elementaryProfile] using elementaryProfile_fourierMiddle elementaryC

theorem base_fourierTail :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      elementaryProfile.tailEnergy n ≤
        Real.exp (-δ * paperRate elementaryX n) := by
  simpa [elementaryProfile] using elementaryProfile_fourierTail

/-! ## The residual analytic inputs -/

/-- The two genuinely analytic inputs that the base record still consumes. -/
structure BaseAnalyticResidual where
  /-- The truncated Perron shift at `Re s = 2/3` for `-ζ'/ζ`, with concrete
  `Kper = 1` and `Cper = 3`. -/
  perronShift : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff elementaryC elementaryX n → |t| ≤ elementaryX n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        1 * (v ^ (2 / 3 : ℝ) * (bandLog elementaryX n) ^ (3 : ℝ)
          + v * (bandLog elementaryX n) ^ (3 : ℝ) / elementaryX n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)
  /-- The literal short-interval smooth count. -/
  localCount : LocalSmoothCountLower elementaryX elementaryC elementaryX

/-- The two residual inputs in `Prop` form, for reporting and for comparison. -/
def BaseAnalyticResidualProp : Prop :=
  (∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff elementaryC elementaryX n → |t| ≤ elementaryX n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        1 * (v ^ (2 / 3 : ℝ) * (bandLog elementaryX n) ^ (3 : ℝ)
          + v * (bandLog elementaryX n) ^ (3 : ℝ) / elementaryX n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)) ∧
    LocalSmoothCountLower elementaryX elementaryC elementaryX

theorem residualProp_iff :
    BaseAnalyticResidualProp ↔ Nonempty BaseAnalyticResidual := by
  constructor
  · rintro ⟨hper, hcount⟩
    exact ⟨⟨hper, hcount⟩⟩
  · rintro ⟨R⟩
    exact ⟨R.perronShift, R.localCount⟩

/-! ## The explicit `L21_2DensityInputs` from a residual -/

/-- Build the `L21_2DensityInputs` bundle from the two residual analytic inputs.
All other fields are the explicit data of this file. -/
def densityInputsOfResidual (R : BaseAnalyticResidual) : L21_2DensityInputs where
  X := elementaryX
  c := elementaryC
  Kper := baseKper
  Cper := baseCper
  Ceps := baseCeps
  fourierGap := baseFourierGap
  badCount := baseBadCount
  lowTerm := elementaryProfile.lowEnergy
  middleTerm := elementaryProfile.middleEnergy
  tailTerm := elementaryProfile.tailEnergy
  polyExp := basePolyExp
  p := elementaryX
  X_gt_one := elementaryX_gt_one
  c_pos := elementaryC_pos
  c_le_one := elementaryC_le_one
  U_ge_three := by
    intro n
    rw [bandLog_elementaryX]
    exact elementaryU_ge_three n
  Kper_nonneg := by
    intro n
    unfold baseKper
    norm_num
  Cper_ge_two := by
    unfold baseCper
    norm_num
  Ceps_nonneg := by
    unfold baseCeps
    norm_num
  polyExp_ge_three := by
    unfold basePolyExp
    norm_num
  badCount_nonneg := baseBadCount_nonneg
  lowTerm_nonneg := base_lowTerm_nonneg
  middleTerm_nonneg := base_middleTerm_nonneg
  tailTerm_nonneg := base_tailTerm_nonneg
  perronShift := by
    simpa [baseKper, baseCper] using R.perronShift
  fourierSupBound := by
    simpa [baseCeps] using base_fourierSupBound
  b_le_B := elementary_b_le_B
  tentChebyshev := base_tentChebyshev
  localCount := R.localCount
  fourierLow := base_fourierLow
  fourierMiddle := base_fourierMiddle
  fourierTail := base_fourierTail
  U_dominates := elementaryU_dominates
  U_le_exp := elementaryU_le_exp

/-- The full base record `L21_2Inputs`, built from the two residual inputs. -/
def baseInputs (R : BaseAnalyticResidual) : L21_2Inputs :=
  (densityInputsOfResidual R).toInputs

/-! ## Signatures of the concrete fields -/

theorem baseInputs_X (R : BaseAnalyticResidual) :
    (baseInputs R).X = elementaryX := rfl

theorem baseInputs_c (R : BaseAnalyticResidual) :
    (baseInputs R).c = elementaryC := rfl

theorem baseInputs_Kper (R : BaseAnalyticResidual) :
    (baseInputs R).Kper = baseKper := rfl

theorem baseInputs_Cper (R : BaseAnalyticResidual) :
    (baseInputs R).Cper = baseCper := rfl

theorem baseInputs_Ceps (R : BaseAnalyticResidual) :
    (baseInputs R).Ceps = baseCeps := rfl

theorem baseInputs_fourierGap (R : BaseAnalyticResidual) (n : ℕ) (t : ℝ) :
    (baseInputs R).fourierGap n t = baseFourierGap n t := rfl

theorem baseInputs_k (R : BaseAnalyticResidual) :
    (baseInputs R).k = kOf elementaryX elementaryC := rfl

theorem baseInputs_m (R : BaseAnalyticResidual) :
    (baseInputs R).m = mOf elementaryX elementaryC := rfl

theorem baseInputs_spacing (R : BaseAnalyticResidual) :
    (baseInputs R).spacing = spacingOf elementaryX elementaryC := rfl

theorem baseInputs_a (R : BaseAnalyticResidual) :
    (baseInputs R).a = aOf elementaryX elementaryC := rfl

theorem baseInputs_b (R : BaseAnalyticResidual) :
    (baseInputs R).b = bOf elementaryX elementaryC := rfl

theorem baseInputs_smoothCount (R : BaseAnalyticResidual) :
    (baseInputs R).smoothCount =
      smoothCountNear elementaryX elementaryC elementaryX := rfl

theorem baseInputs_badCount (R : BaseAnalyticResidual) :
    (baseInputs R).badCount = baseBadCount := rfl

theorem baseInputs_lowTerm (R : BaseAnalyticResidual) :
    (baseInputs R).lowTerm = elementaryProfile.lowEnergy := rfl

theorem baseInputs_middleTerm (R : BaseAnalyticResidual) :
    (baseInputs R).middleTerm = elementaryProfile.middleEnergy := rfl

theorem baseInputs_tailTerm (R : BaseAnalyticResidual) :
    (baseInputs R).tailTerm = elementaryProfile.tailEnergy := rfl

theorem baseInputs_loss_eq (R : BaseAnalyticResidual) (n : ℕ) :
    (baseInputs R).loss n = baseBadCount n / (elementaryX n + 1) := rfl

/-! ## The manuscript-rate and ledger fields -/

theorem baseInputs_loss_le_paper (R : BaseAnalyticResidual) :
    ∀ᶠ n : ℕ in atTop,
      (baseInputs R).loss n ≤
        Real.exp (-(((baseInputs R).c / 64) * (baseInputs R).T n)) :=
  (baseInputs R).loss_le_paper

theorem baseInputs_loss_le_ledger (R : BaseAnalyticResidual) :
    ∀ᶠ n : ℕ in atTop,
      (baseInputs R).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  (baseInputs R).loss_le_ledger

/-! ## Feeding the residual elliptic slot of `L20_4SourceWitness` -/

/-- The fully sourced L20.4 leaf with the base L21.2 record in its elliptic slot. -/
def sourcedLeafOfBaseResidual (R : BaseAnalyticResidual) :
    L20_4SourcedLeafInputs Bool ℕ :=
  sourcedLeafOfElliptic (baseInputs R)

/-- Hence `L20_4SourcedLeafInputs` is inhabited once the two analytic inputs are
supplied. -/
theorem nonempty_sourcedLeafInputs_of_baseResidual (R : BaseAnalyticResidual) :
    Nonempty (L20_4SourcedLeafInputs Bool ℕ) :=
  ⟨sourcedLeafOfBaseResidual R⟩

/-- The elliptic component of the sourced top data is the base record's loss. -/
theorem sourcedLeafOfBaseResidual_eta (R : BaseAnalyticResidual) :
    (sourcedLeafOfBaseResidual R).top.eta = (baseInputs R).loss := rfl

/-- The remaining analytic fields, explicitly listed. -/
def residualFields : List String :=
  [ "perronShift : truncated Perron at Re s = 2/3 for -ζ'/ζ",
    "localCount : ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX" ]

theorem residualFields_nonempty : residualFields ≠ [] := by
  simp [residualFields]

/-! ## Axiom audit -/

#print axioms basePairMass_pos
#print axioms sum_baseProbMu
#print axioms sum_baseProbNu
#print axioms norm_fourierOfWeights_le
#print axioms baseFourierGap_bound
#print axioms base_fourierSupBound
#print axioms baseBadCount_nonneg
#print axioms base_tentChebyshev
#print axioms base_lowTerm_nonneg
#print axioms base_middleTerm_nonneg
#print axioms base_tailTerm_nonneg
#print axioms base_fourierLow
#print axioms base_fourierMiddle
#print axioms base_fourierTail
#print axioms residualProp_iff
#print axioms densityInputsOfResidual
#print axioms baseInputs
#print axioms baseInputs_loss_le_paper
#print axioms baseInputs_loss_le_ledger
#print axioms sourcedLeafOfBaseResidual
#print axioms nonempty_sourcedLeafInputs_of_baseResidual

#check baseInputs
#check densityInputsOfResidual
#check baseFourierGap
#check sourcedLeafOfBaseResidual
#check nonempty_sourcedLeafInputs_of_baseResidual

end Cogentic.RandomizedL21BaseInhabitant

end
