import Cogentic.RandomizedL20_2Char
import Cogentic.RandomizedSmoothDensity

set_option linter.style.haveILetI false

/-!
# L20.2: the saddle point and the smooth-character budgets

`Cogentic.RandomizedL20_2Sub` reduces the L20.2 interior-concentration inputs to
the four paper-level fields

* `SaddlePointScaleLower`,
* `SaddlePointMeanLower`,
* `SmoothCharacterSumBound`,
* `SmoothCharacterOffDiagonalBudget`.

This file makes the objects behind those four fields explicit and proves the
reductions to `L20_2SubInputs` and `L20_2CharInputs`.

## The reductions

1. **Saddle scale from a smooth-number count.**  `smoothNumberSet` is the
   finite set of `y`-smooth integers in `[1, X]`, the same set that appears in
   `Cogentic.Randomized.smoothCount_rankin_upper`.  The saddle scale is
   `Λ = log (#smooth numbers)`.  The single analytic input is the explicit
   lower bound `exp (c D log D) ≤ #smooth numbers`
   (`SmoothNumberCountLower`).  `saddlePointScaleLower_of_smoothNumberCountLower`
   proves `SaddlePointScaleLower Λ c` from it, and
   `smoothNumberCount_le_rankin` records that the same set is controlled above
   by the existing Rankin estimate.

2. **Saddle mean from a smooth reciprocal mass.**  `smoothNumberMass` is the
   Rankin sum `∑ m^(-α)` over the same smooth set, whose Euler-product upper
   bound is the existing `sum_rpow_neg_le_euler_prod`.  The analytic input is
   the explicit logarithmic lower bound `η Λ ≤ log (smoothNumberMass)`
   (`SmoothNumberMassLogLower`).  `saddlePointMeanLower_of_smoothNumberMassLogLower`
   proves `SaddlePointMeanLower smoothNumberMass Λ η` from it, without setting
   any mass or error to zero.

3. **Smooth-character sums from the existing GRH prime-bin estimate.**
   `primeBinSmoothCharacterData` turns a prime-bin product set into the concrete
   `SmoothCharacterData` object of `RandomizedL20_2Char`.  Its nonprincipal
   character sums are bounded by the GRH envelope
   `primeBinRelativeEnvelope` of `RandomizedPrimeBinBias`, and the only
   remaining analytic input is the explicit decay `PrimeBinCharacterDecay`
   (`smoothCharacterSumBound_of_primeBinReduction`).  The GRH constant is
   extracted from `PrimeBinProductBound` by
   `primeBinCharacterReduction_of_productBound`.

4. **Off-diagonal budget from coordinate energies and the GRH Mellin energy.**
   `smoothCharacterOffDiagonalBudget_of_coordinateEnergy` is the AM–GM
   reduction already used in `RandomizedL20_2Char`.  For prime-bin product sets
   the coordinate energy is the actual Plancherel energy
   `primeBinMellinEnergy`, and `coordinateEnergyBudget_of_mellinEnergy` proves
   the coordinate bound from the existing GRH estimate
   `primeBinProducts_mellin_energy_from_critical_line` together with an
   explicit envelope-fit inequality.

5. **The reduced bundle.**  `L20_2SaddleInputs` replaces the four paper-level
   fields of `L20_2CharInputs` by the explicit sub-`Prop`s above.  The
   construction `toCharInputs` proves the four fields, and `toSubInputs`,
   `toInputs`, `toConcentrationLeaf`, together with the loss and ledger
   statements, rebuild the L20.2 concentration leaf.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no error, mass,
or count is set to zero.
-/

namespace Cogentic.RandomizedL20_2Saddle

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Char
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Window

noncomputable section

/-! ## 1. The explicit smooth-number objects -/

/-- The `y`-smooth integers in `[1, X]`.  This is exactly the finite set used
by `Cogentic.Randomized.smoothCount_rankin_upper`. -/
def smoothNumberSet (X y : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X n⌋₊).filter (fun m : ℕ => ∀ p ∈ m.primeFactors, (p : ℝ) ≤ y n)

/-- The cardinality of the smooth-number set, as a real number. -/
def smoothNumberCount (X y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((smoothNumberSet X y n).card : ℝ)

/-- The Rankin smooth reciprocal mass `∑ m^(-α)` over the smooth-number set. -/
def smoothNumberMass (X y α : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ smoothNumberSet X y n, (m : ℝ) ^ (-(α n))

/-- The smooth-number set contains `1` as soon as the upper endpoint is at
least one. -/
theorem one_mem_smoothNumberSet {X y : ℕ → ℝ} {n : ℕ} (hX : 1 ≤ X n) :
    1 ∈ smoothNumberSet X y n := by
  unfold smoothNumberSet
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨le_rfl, Nat.le_floor (by exact_mod_cast hX)⟩
  · simp

/-- The smooth reciprocal mass is positive: the term `m = 1` contributes `1`. -/
theorem smoothNumberMass_pos {X y α : ℕ → ℝ} (hX : ∀ n, 1 ≤ X n) (n : ℕ) :
    0 < smoothNumberMass X y α n := by
  unfold smoothNumberMass
  have hmem : 1 ∈ smoothNumberSet X y n := one_mem_smoothNumberSet (y := y) (hX n)
  have hnonneg : ∀ m ∈ smoothNumberSet X y n, 0 ≤ (m : ℝ) ^ (-(α n)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    exact Real.rpow_nonneg (by exact_mod_cast (le_trans zero_le_one hm1)) _
  have hge : (1 : ℝ) ≤ ∑ m ∈ smoothNumberSet X y n, (m : ℝ) ^ (-(α n)) := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ (-(α n)) := by simp
      _ ≤ ∑ m ∈ smoothNumberSet X y n, (m : ℝ) ^ (-(α n)) := by
        simpa using Finset.single_le_sum hnonneg hmem
  linarith

/-- **The existing Rankin upper bound applies to the smooth-number set.**  This
shows that `smoothNumberCount` is literally the object of
`Cogentic.Randomized.smoothCount_rankin_upper`. -/
theorem smoothNumberCount_le_rankin {X y : ℕ → ℝ} {n : ℕ} {α : ℝ}
    (hX : 1 ≤ X n) (hy : 2 ≤ y n) (hα0 : 0 < α) (hα1 : α < 1) :
    smoothNumberCount X y n ≤
      X n ^ α * ∏ p ∈ (Finset.Icc 2 ⌊y n⌋₊).filter Nat.Prime,
        (1 - (p : ℝ) ^ (-α))⁻¹ := by
  unfold smoothNumberCount smoothNumberSet
  exact smoothCount_rankin_upper hX hy hα0 hα1

/-- **The existing Euler-product bound applies to the smooth reciprocal mass.**
This is `sum_rpow_neg_le_euler_prod` for the explicit smooth-number set. -/
theorem smoothNumberMass_le_eulerProduct {X y α : ℕ → ℝ} (n : ℕ)
    (hy : 0 ≤ y n) (hα0 : 0 < α n) :
    smoothNumberMass X y α n ≤
      ∏ p ∈ (Finset.Icc 2 ⌊y n⌋₊).filter Nat.Prime,
        (1 - (p : ℝ) ^ (-(α n)))⁻¹ := by
  unfold smoothNumberMass
  apply sum_rpow_neg_le_euler_prod hy hα0
  intro m hm
  obtain ⟨hmIcc, hmsmooth⟩ := Finset.mem_filter.mp hm
  exact ⟨(Finset.mem_Icc.mp hmIcc).1, hmsmooth⟩

/-! ## 2. Saddle-point scale -/

/-- The explicit analytic input for the saddle scale: the number of
`y`-smooth integers in `[1, X]` is at least `exp (c D log D)`.  This is the
Hildebrand–Tenenbaum lower-bound side of the smooth-number saddle point. -/
def SmoothNumberCountLower (X y : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ n, exp (c * paperD n * scale n) ≤ smoothNumberCount X y n

/-- The saddle scale defined by the smooth-number count. -/
def smoothSaddleScale (X y : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (smoothNumberCount X y n)

/-- **`SaddlePointScaleLower` reduced to a smooth-number count lower bound.**
The only analytic content is `SmoothNumberCountLower`; the logarithm and the
constant arithmetic are proved here. -/
theorem saddlePointScaleLower_of_smoothNumberCountLower {X y : ℕ → ℝ} {c : ℝ}
    (h : SmoothNumberCountLower X y c) :
    SaddlePointScaleLower (smoothSaddleScale X y) c := by
  refine ⟨h.1, fun n => ?_⟩
  have hpos : 0 < exp (c * paperD n * scale n) := exp_pos _
  have hlog := Real.log_le_log hpos (h.2 n)
  rwa [Real.log_exp] at hlog

/-! ## 3. Saddle-point mean -/

/-- The explicit analytic input for the saddle mean: the logarithmic mean mass
dominates `η Λ`.  This is the lower-bound form of the Appendix C saddle point,
stated on the actual Rankin mass `smoothNumberMass`. -/
def SmoothNumberMassLogLower (X y α Λ : ℕ → ℝ) (η : ℝ) : Prop :=
  0 < η ∧ ∀ n, η * Λ n ≤ Real.log (smoothNumberMass X y α n)

/-- **`SaddlePointMeanLower` reduced to a logarithmic mass lower bound.**  The
mean is the actual smooth reciprocal mass, not a synthetic sequence. -/
theorem saddlePointMeanLower_of_smoothNumberMassLogLower {X y α Λ : ℕ → ℝ}
    {η : ℝ} (hX : ∀ n, 1 ≤ X n) (h : SmoothNumberMassLogLower X y α Λ η) :
    SaddlePointMeanLower (smoothNumberMass X y α) Λ η := by
  refine ⟨h.1, fun n => ?_⟩
  have hpos : 0 < smoothNumberMass X y α n := smoothNumberMass_pos hX n
  calc
    exp (η * Λ n) ≤ exp (Real.log (smoothNumberMass X y α n)) :=
      exp_le_exp.mpr (h.2 n)
    _ = smoothNumberMass X y α n := exp_log hpos

/-! ## 4. Smooth-character sums from the GRH prime-bin estimate -/

/-- The concrete `SmoothCharacterData` carried by a prime-bin product set: the
support is `primeBinProducts A B`, the weight is the constant weight `1`, and
the mass is the cardinality. -/
def primeBinSmoothCharacterData (q : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hcard : 0 < (primeBinProducts A B).card) : SmoothCharacterData where
  q := q
  support := primeBinProducts A B
  weight := fun _ => 1
  mass := ((primeBinProducts A B).card : ℝ)
  mass_pos := by exact_mod_cast hcard
  total_le := by simp

/-- The explicit GRH smooth-character reduction for a prime-bin product set:
the GRH envelope bound and the manuscript-rate decay of that envelope. -/
def PrimeBinCharacterReduction (K c : ℝ) (q : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (A B : ι → ℕ) : Prop :=
  0 ≤ K ∧
    (∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖twist (primeBinProducts A B) (fun _ => 1) χ‖ ≤
        primeBinRelativeEnvelope K q A B) ∧
    (∀ n, PrimeBinCharacterDecay K c q A B n)

/-- **`SmoothCharacterSumBound` reduced to the prime-bin GRH estimate and its
explicit decay.**  The concrete character error is the normalized nonprincipal
sum over the product set, and the bound is exactly the GRH envelope times the
manuscript decay. -/
theorem smoothCharacterSumBound_of_primeBinReduction {K c : ℝ} (hc : 0 < c)
    {q : ℕ} [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hcard : 0 < (primeBinProducts A B).card)
    (h : PrimeBinCharacterReduction K c q A B) :
    SmoothCharacterSumBound
      (fun _ => smoothCharacterError (primeBinSmoothCharacterData q A B hcard)) c := by
  obtain ⟨_, hbound, hdecay⟩ := h
  refine ⟨hc, fun n => ⟨smoothCharacterError_nonneg _, ?_⟩⟩
  refine smoothCharacterError_le (primeBinSmoothCharacterData q A B hcard) (exp_pos _).le ?_
  intro χ hχ
  exact (hbound χ hχ).trans (hdecay n)

/-- The GRH constant extracted from a `PrimeBinProductBound`. -/
noncomputable def primeBinGRHConstant (hb : PrimeBinProductBound) : ℝ :=
  Classical.choose (primeBinProducts_twist_le hb)

/-- The extracted GRH constant is nonnegative. -/
theorem primeBinGRHConstant_nonneg (hb : PrimeBinProductBound) :
    0 ≤ primeBinGRHConstant hb :=
  (Classical.choose_spec (primeBinProducts_twist_le hb)).1

/-- The extracted GRH constant satisfies the prime-bin envelope bound. -/
theorem primeBinGRHConstant_bound (hb : PrimeBinProductBound) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        ‖twist (primeBinProducts A B) (fun _ => 1) χ‖ ≤
          primeBinRelativeEnvelope (primeBinGRHConstant hb) q A B :=
  (Classical.choose_spec (primeBinProducts_twist_le hb)).2

/-- **The prime-bin reduction from the existing GRH estimate.**  Beyond
`PrimeBinProductBound` (which is itself derived from
`DirichletLZerosOnLine` by `primeBin_product_from_critical_line`), the only
input is the explicit decay of the GRH envelope. -/
theorem primeBinCharacterReduction_of_productBound (hb : PrimeBinProductBound)
    {c : ℝ} {q : ℕ} [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hdecay : ∀ n, PrimeBinCharacterDecay (primeBinGRHConstant hb) c q A B n) :
    PrimeBinCharacterReduction (primeBinGRHConstant hb) c q A B := by
  refine ⟨primeBinGRHConstant_nonneg hb, ?_, hdecay⟩
  intro χ hχ
  exact primeBinGRHConstant_bound hb q χ hχ A B hA hAB hdisj

/-- **`SmoothCharacterSumBound` from the existing prime-bin GRH estimate.**
This is the direct form: the GRH product bound supplies the envelope, and the
only remaining input is the explicit envelope decay `PrimeBinCharacterDecay`. -/
theorem smoothCharacterSumBound_of_primeBinProductBound
    (hb : PrimeBinProductBound) {c : ℝ} (hc : 0 < c)
    {q : ℕ} [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hcard : 0 < (primeBinProducts A B).card)
    (hdecay : ∀ n, PrimeBinCharacterDecay (primeBinGRHConstant hb) c q A B n) :
    SmoothCharacterSumBound
      (fun _ => smoothCharacterError (primeBinSmoothCharacterData q A B hcard)) c :=
  smoothCharacterSumBound_of_primeBinReduction hc A B hcard
    (primeBinCharacterReduction_of_productBound hb A B hA hAB hdisj hdecay)

/-- **`SmoothCharacterSumBound` from the critical-line GRH input.**  Combining
the previous theorem with `primeBin_product_from_critical_line` leaves only the
explicit envelope decay. -/
theorem smoothCharacterSumBound_of_criticalLine (line : DirichletLZerosOnLine)
    {c : ℝ} (hc : 0 < c) {q : ℕ} [NeZero q]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hcard : 0 < (primeBinProducts A B).card)
    (hdecay : ∀ n,
      PrimeBinCharacterDecay (primeBinGRHConstant (primeBin_product_from_critical_line line))
        c q A B n) :
    SmoothCharacterSumBound
      (fun _ => smoothCharacterError (primeBinSmoothCharacterData q A B hcard)) c :=
  smoothCharacterSumBound_of_primeBinProductBound (primeBin_product_from_critical_line line)
    hc A B hA hAB hdisj hcard hdecay

/-! ## 5. The off-diagonal budget from GRH Mellin energy -/

/-- **Coordinate energy from the existing GRH Mellin estimate.**  If the
explicit prime-bin Mellin envelope fits the CRT plus smooth-character budget,
then the square root of the actual Plancherel energy fits the coordinate
budget.  This uses `primeBinProducts_mellin_energy_from_critical_line`. -/
theorem coordinateEnergyBudget_of_mellinEnvelope
    (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
        (A B : ι → ℕ), (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
        (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        ∀ (σ t : ℕ → ℝ), (∀ n, 0 ≤ σ n) →
        ∀ {μ crt char : ℕ → ℝ},
        (∀ n,
          (∏ i, K * Real.sqrt (B i) *
            (1 + Real.log (q * ((B i : ℝ) + |t n| + 2))) ^ 3) ^ 2 ≤
            (crt n + char n) * μ n ^ 2) →
        CoordinateEnergyBudget
          (fun n => Real.sqrt (primeBinMellinEnergy q A B ((σ n : ℂ) + t n * Complex.I)))
          μ crt char := by
  obtain ⟨K, hK, hfit⟩ := primeBinMellinEnergy_le_of_fit line
  refine ⟨K, hK, ?_⟩
  intro q _ ι _ _ A B hB hAB hdisj σ t hσ μ crt char hbudget n
  have hE := hfit q A B hB hAB hdisj (σ n) (t n) (hσ n) (hbudget n)
  have hnonneg : 0 ≤ primeBinMellinEnergy q A B ((σ n : ℂ) + t n * Complex.I) := by
    unfold primeBinMellinEnergy
    positivity
  rwa [Real.sq_sqrt hnonneg]

/-- **`SmoothCharacterOffDiagonalBudget` reduced to the GRH Mellin estimate.**
If both coordinate Mellin envelopes fit the budget, the AM–GM reduction turns
the two coordinate energies into the off-diagonal budget. -/
theorem smoothCharacterOffDiagonalBudget_of_mellinEnvelope
    (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
        (A B : ι → ℕ), (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
        (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        ∀ (σ₁ t₁ σ₂ t₂ : ℕ → ℝ), (∀ n, 0 ≤ σ₁ n) → (∀ n, 0 ≤ σ₂ n) →
        ∀ {μ crt char : ℕ → ℝ},
        (∀ n,
          (∏ i, K * Real.sqrt (B i) *
            (1 + Real.log (q * ((B i : ℝ) + |t₁ n| + 2))) ^ 3) ^ 2 ≤
            (crt n + char n) * μ n ^ 2) →
        (∀ n,
          (∏ i, K * Real.sqrt (B i) *
            (1 + Real.log (q * ((B i : ℝ) + |t₂ n| + 2))) ^ 3) ^ 2 ≤
            (crt n + char n) * μ n ^ 2) →
        SmoothCharacterOffDiagonalBudget
          (fun n => Real.sqrt (primeBinMellinEnergy q A B ((σ₁ n : ℂ) + t₁ n * Complex.I)))
          (fun n => Real.sqrt (primeBinMellinEnergy q A B ((σ₂ n : ℂ) + t₂ n * Complex.I)))
          μ crt char := by
  obtain ⟨K, hK, hcoord⟩ := coordinateEnergyBudget_of_mellinEnvelope line
  refine ⟨K, hK, ?_⟩
  intro q _ ι _ _ A B hB hAB hdisj σ₁ t₁ σ₂ t₂ hσ₁ hσ₂ μ crt char h₁ h₂
  exact smoothCharacterOffDiagonalBudget_of_coordinateEnergy
    (hcoord q A B hB hAB hdisj σ₁ t₁ hσ₁ h₁)
    (hcoord q A B hB hAB hdisj σ₂ t₂ hσ₂ h₂)

/-! ## 6. The reduced L20.2 bundle -/

/-- The L20.2 inputs with the four saddle/character fields replaced by explicit
analytic sub-`Prop`s:

* `count_lower`: the smooth-number count lower bound behind the saddle scale;
* `mass_log_lower`: the logarithmic smooth-mass lower bound behind the saddle
  mean;
* `char_concrete`: the concrete nonprincipal smooth-character sums (which can
  be supplied by `smoothCharacterSumBound_of_primeBinReduction` from GRH);
* `energy₁`, `energy₂`: the coordinate energy budgets (which can be supplied by
  `coordinateEnergyBudget_of_mellinEnvelope` from GRH).

The remaining fields are the arithmetic cells and the coupled-mode bound, as in
`L20_2CharInputs`. -/
structure L20_2SaddleInputs where
  /-- The upper endpoint of the smooth-number range. -/
  X : ℕ → ℝ
  /-- The smoothness cutoff. -/
  y : ℕ → ℝ
  /-- The Rankin exponent in the smooth reciprocal mass. -/
  α : ℕ → ℝ
  /-- The upper endpoint is at least one. -/
  X_ge_one : ∀ n, 1 ≤ X n
  /-- The smoothness cutoff is at least two. -/
  y_ge_two : ∀ n, 2 ≤ y n
  /-- The Rankin exponent is positive. -/
  α_pos : ∀ n, 0 < α n
  /-- The Rankin exponent is less than one. -/
  α_lt_one : ∀ n, α n < 1
  /-- The constant in the smooth-count lower bound. -/
  cLam : ℝ
  /-- The constant in the smooth-mass logarithmic lower bound. -/
  η : ℝ
  /-- The smooth-number count lower bound. -/
  count_lower : SmoothNumberCountLower X y cLam
  /-- The logarithmic smooth-mass lower bound. -/
  mass_log_lower : SmoothNumberMassLogLower X y α (smoothSaddleScale X y) η
  /-- The proxy score bound `L`. -/
  L : ℕ → ℝ
  /-- The smooth-character decay constant. -/
  cChar : ℝ
  /-- The smooth-character decay constant is positive. -/
  cChar_pos : 0 < cChar
  /-- The polynomial exponent constant in `L ≤ exp (cL (log D)^5)`. -/
  cL : ℝ
  /-- `L` is nonnegative. -/
  L_nonneg : ∀ n, 0 ≤ L n
  /-- The polynomial exponent constant is nonnegative. -/
  cL_nonneg : 0 ≤ cL
  /-- The polynomial proxy bound. -/
  L_upper : ∀ n, L n ≤ exp (cL * (scale n) ^ 5)
  /-- The concrete smooth-character data at each ledger index. -/
  charData : ℕ → SmoothCharacterData
  /-- The concrete smooth-character sums at the manuscript rate. -/
  char_concrete : ∀ n (χ : DirichletCharacter ℂ (charData n).q), χ ≠ 1 →
    ‖twist (charData n).support (charData n).weight χ‖ ≤
      exp (-cChar * paperD n * scale n) * (charData n).mass
  /-- The finite interior cell at each ledger index. -/
  cell : ∀ n, CellData n (L n)
  /-- The ideal mean is the actual mean of the cell. -/
  μ_eq : ∀ n, smoothNumberMass X y α n = (cell n).mean (cell n).f
  /-- The proxy mean exceeds the actual mean by the geometric CRT error. -/
  proxy_error : ∀ n, (cell n).mean (cell n).proxy ≤
    smoothNumberMass X y α n + geometricCRTError n
  /-- The CRT error is dominated by the mean. -/
  proxy_error_le_mean : ∀ n, geometricCRTError n ≤ smoothNumberMass X y α n
  /-- The first one-coordinate second-moment envelope. -/
  E₁ : ℕ → ℝ
  /-- The second one-coordinate second-moment envelope. -/
  E₂ : ℕ → ℝ
  /-- The coupled-mode Cauchy–Schwarz bound for the off-diagonal sum. -/
  coupled : OffDiagonalCoupledBound (fun n => (cell n).cross) E₁ E₂
  /-- The first coordinate energy fits the CRT plus smooth-character budget. -/
  energy₁ : ∀ n, E₁ n ^ 2 ≤
    (geometricCRTError n + smoothCharacterError (charData n)) *
      (smoothNumberMass X y α n) ^ 2
  /-- The second coordinate energy fits the CRT plus smooth-character budget. -/
  energy₂ : ∀ n, E₂ n ^ 2 ≤
    (geometricCRTError n + smoothCharacterError (charData n)) *
      (smoothNumberMass X y α n) ^ 2

namespace L20_2SaddleInputs

/-- The saddle scale of the reduced bundle. -/
def Λ (S : L20_2SaddleInputs) : ℕ → ℝ :=
  smoothSaddleScale S.X S.y

/-- The saddle mean of the reduced bundle. -/
def μ (S : L20_2SaddleInputs) : ℕ → ℝ :=
  smoothNumberMass S.X S.y S.α

/-- The saddle-scale field, proved from the smooth-number count lower bound. -/
theorem saddle_scale (S : L20_2SaddleInputs) :
    SaddlePointScaleLower S.Λ S.cLam :=
  saddlePointScaleLower_of_smoothNumberCountLower S.count_lower

/-- The saddle-mean field, proved from the logarithmic smooth-mass bound. -/
theorem saddle_mean (S : L20_2SaddleInputs) :
    SaddlePointMeanLower S.μ S.Λ S.η :=
  saddlePointMeanLower_of_smoothNumberMassLogLower S.X_ge_one S.mass_log_lower

/-- The smooth-character field, proved from the concrete nonprincipal sums. -/
theorem char_sum (S : L20_2SaddleInputs) :
    SmoothCharacterSumBound
      (fun n => smoothCharacterError (S.charData n)) S.cChar :=
  smoothCharacterSumBound_of_concrete S.charData S.cChar_pos S.char_concrete

/-- The off-diagonal field, proved from the two coordinate energy budgets by
AM–GM. -/
theorem offdiag_budget (S : L20_2SaddleInputs) :
    SmoothCharacterOffDiagonalBudget S.E₁ S.E₂ S.μ geometricCRTError
      (fun n => smoothCharacterError (S.charData n)) :=
  smoothCharacterOffDiagonalBudget_of_coordinateEnergy S.energy₁ S.energy₂

/-- The reduced bundle builds `L20_2CharInputs`: the four paper-level fields are
proved from the explicit sub-`Prop`s. -/
def toCharInputs (S : L20_2SaddleInputs) : L20_2CharInputs where
  Λ := S.Λ
  μ := S.μ
  L := S.L
  cLam := S.cLam
  η := S.η
  cChar := S.cChar
  cChar_pos := S.cChar_pos
  cL := S.cL
  saddle_scale := S.saddle_scale
  saddle_mean := S.saddle_mean
  L_nonneg := S.L_nonneg
  cL_nonneg := S.cL_nonneg
  L_upper := S.L_upper
  charData := S.charData
  char_concrete := S.char_concrete
  cell := S.cell
  μ_eq := S.μ_eq
  proxy_error := S.proxy_error
  proxy_error_le_mean := S.proxy_error_le_mean
  E₁ := S.E₁
  E₂ := S.E₂
  coupled := S.coupled
  energy₁ := S.energy₁
  energy₂ := S.energy₂

/-- The reduced bundle builds `L20_2SubInputs`. -/
def toSubInputs (S : L20_2SaddleInputs) : L20_2SubInputs :=
  S.toCharInputs.toSubInputs

/-- The reduced bundle builds the original `L20_2Inputs`. -/
def toInputs (S : L20_2SaddleInputs) : L20_2Inputs :=
  S.toCharInputs.toInputs

/-- The concentration leaf built from the reduced inputs. -/
def toConcentrationLeaf (S : L20_2SaddleInputs) : ConcentrationLeaf :=
  S.toInputs.toConcentrationLeaf

/-- The reduced bundle realizes the parent deficit exactly. -/
theorem toInputs_loss_eq (S : L20_2SaddleInputs) (n : ℕ) :
    S.toInputs.loss n =
      |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| / S.μ n :=
  rfl

/-- The reduced bundle's deficit is nonnegative. -/
theorem loss_nonneg (S : L20_2SaddleInputs) (n : ℕ) : 0 ≤ S.toInputs.loss n :=
  S.toInputs.loss_nonneg n

/-- The `B = 2` ledger slot for the reduced inputs. -/
theorem slot_le (S : L20_2SaddleInputs) :
    ∀ᶠ n : ℕ in atTop,
      S.toInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toInputs.slot_le

end L20_2SaddleInputs

/-! ## Axiom audit -/

#print axioms one_mem_smoothNumberSet
#print axioms smoothNumberMass_pos
#print axioms smoothNumberCount_le_rankin
#print axioms smoothNumberMass_le_eulerProduct
#print axioms saddlePointScaleLower_of_smoothNumberCountLower
#print axioms saddlePointMeanLower_of_smoothNumberMassLogLower
#print axioms smoothCharacterSumBound_of_primeBinReduction
#print axioms primeBinGRHConstant_nonneg
#print axioms primeBinGRHConstant_bound
#print axioms primeBinCharacterReduction_of_productBound
#print axioms smoothCharacterSumBound_of_primeBinProductBound
#print axioms smoothCharacterSumBound_of_criticalLine
#print axioms coordinateEnergyBudget_of_mellinEnvelope
#print axioms smoothCharacterOffDiagonalBudget_of_mellinEnvelope
#print axioms L20_2SaddleInputs.saddle_scale
#print axioms L20_2SaddleInputs.saddle_mean
#print axioms L20_2SaddleInputs.char_sum
#print axioms L20_2SaddleInputs.offdiag_budget
#print axioms L20_2SaddleInputs.toCharInputs
#print axioms L20_2SaddleInputs.toSubInputs
#print axioms L20_2SaddleInputs.toInputs
#print axioms L20_2SaddleInputs.toConcentrationLeaf
#print axioms L20_2SaddleInputs.toInputs_loss_eq
#print axioms L20_2SaddleInputs.loss_nonneg
#print axioms L20_2SaddleInputs.slot_le

end

end Cogentic.RandomizedL20_2Saddle
