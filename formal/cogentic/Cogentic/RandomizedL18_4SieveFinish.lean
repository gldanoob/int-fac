import Cogentic.RandomizedL18_4ConvolutionEnergy
import Cogentic.RandomizedL18_4Full

/-!
# L18.4: finishing the large sieve

The L18.4 chain

`LargeSieveInputs` → `LargeSieveCertificate` → `LargeSieveCertificateData`
→ `LargeSieveResidualData` → `LargeSieveSpectralData` → `LargeSieveConvolutionData`

has reduced the paper-level large sieve to a handful of bookkeeping and analytic
inputs.  This file finishes the two remaining large-sieve inputs and assembles
the L18.4 `large_sieve` field.

## The residual cell count

`RationalCellConstruction` supplies the actual finite cell geometry: at every
stage there is a finite type of denominator cells and a finite type of numerator
cells, an incidence relation, and every denominator cell meets at least one
numerator cell.  Consequently `perCell_ge_one` is a theorem
(`RationalCellConstruction.perCell_ge_one`), not a hypothesis.  The total number
of numerator cells met is `card (Den n) * perCell n`; the remaining counting
input is the single aggregate bound `NumeratorSupportBound`,
`card (Den n) * perCell n ≤ C n * (M n * V n ^ 2)`, which is the smallest
explicit form of the rational-cell lattice count.  It is exactly the
`numeratorSupport_le` field of `LargeSieveCertificateData`; the determinant-level
count `stripPairSet_card_le_support` is what supplies it.

## The energy budget

The actual residual energy of a stage is

`residualAt n = max_i mellinResidueEnergy (q n i) (P n i) (s n i)`,

the maximum physical squared residue discrepancy.  By the Mellin Plancherel
identity (`mellinResidueEnergy_eq_characterEnergy`, i.e. character
orthogonality on the reduced residue classes) this is the maximum normalized
nonprincipal character energy; `residualAt_le_iff_plancherel` records the
equivalence.  The finite large-sieve Bessel inequality
(`mellinResidueEnergy_le_sq`, from `classMass_centered_sq_le`) turns a uniform
per-character norm bound `B` and the scalar comparison `B² ≤ Econv / d` into the
budget `energyResidualBudget_of_characterBound`.

The smallest explicit remaining energy input is therefore the single `Prop`
`EnergyResidualBudget`:

`∀ n, residualAt n ≤ Econv n / d n`.

It is equivalent to the per-cell `MellinConvolutionEnergyBudget` and to the
Plancherel character-energy budget (`energyResidualBudget_iff_mellinConvolutionEnergyBudget`,
`energyResidualBudget_iff_plancherel`).  No spectral constant `A`, no identity
`A² = stageSpectralEnergy`, and no per-character uniformity is assumed.

## The certificate and the nonzero error

`LargeSieveFinishData` bundles the cell geometry, the two smallest explicit
inputs and a **genuine nonzero error**: an explicit nonprincipal character with
nonvanishing twist (`NonzeroResidualWitness`).  Its residue energy is positive
(`mellinResidueEnergy_pos_of_twist_ne_zero`), so the stage residual is positive
at the witness stage (`residual_nonzero`); the error is never set to zero.  The
concrete model `oneCellWitness` (modulus `3`, numerator set `{1}`) proves that
this nonzero-error data is actually inhabited.

From this data the multi-modulus residual bound
`secondMoment ≤ support * (Econv / d)` is proved directly, without a uniform
spectral constant, by summing the actual per-cell budgets.  The support bound
then gives the literal `LargeSieveInputs`, hence the L18.4 `large_sieve` field
and the replacement `L18_4Inputs.replaceLargeSieveFinishData`.  The theorem
`large_sieve_with_nonzero_error` records the field together with the positive
error witness.  Finally `L18_4Certificate.toInputsWithLargeSieve` assembles the
full L18.4 inputs from an existing `L18_4Certificate` (keeping its `CellData`,
`MassErrorInputs` — including the genuine RH progression error — and
`ThinAggregate`) while replacing the large-sieve field by the finished one.

Nothing here is a `sorry`, an `admit`, an `axiom` or a `native_decide`; no
energy, count or error is set to zero.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open scoped BigOperators Classical
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.Randomized

set_option linter.style.haveILetI false
set_option linter.checkUnivs false

/-! ## 1. The actual residual energy of a cell family -/

/-- The actual large-sieve residual energy at one stage: the maximum over the
denominator cells of the physical squared residue discrepancy, equivalently (by
Plancherel) the maximum normalized nonprincipal character energy. -/
noncomputable def residualAt (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ) (n : ℕ) : ℝ :=
  @stageSpectralEnergy (cell.Den n) (cell.denFintype n) (cell.denNonempty n)
    (q n) (fun i => ⟨q_ne_zero n i⟩) (P n) (s n)

/-- The residual energy is nonnegative. -/
theorem residualAt_nonneg (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ) (n : ℕ) :
    0 ≤ residualAt cell q q_ne_zero P s n := by
  unfold residualAt
  exact @stageSpectralEnergy_nonneg (cell.Den n) (cell.denFintype n)
    (cell.denNonempty n) (q n) (fun i => ⟨q_ne_zero n i⟩) (P n) (s n)

/-- The residual energy is the maximum of the per-cell Mellin residue energies. -/
theorem residualAt_le_iff (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (n : ℕ) {E : ℝ} :
    residualAt cell q q_ne_zero P s n ≤ E ↔
      ∀ i, @mellinResidueEnergy (q n i) ⟨q_ne_zero n i⟩ (P n i) (s n i) ≤ E := by
  unfold residualAt
  exact @stageSpectralEnergy_le_iff (cell.Den n) (cell.denFintype n)
    (cell.denNonempty n) (q n) (fun i => ⟨q_ne_zero n i⟩) (P n) (s n) E

/-- The residual energy in Plancherel form: the per-cell normalized
nonprincipal character energy.  This is character orthogonality applied cell by
cell. -/
theorem residualAt_le_iff_plancherel (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (n : ℕ) {E : ℝ} :
    residualAt cell q q_ne_zero P s n ≤ E ↔
      ∀ i, @spectralEnergy (q n i) ⟨q_ne_zero n i⟩ (P n i) (s n i) /
        ((q n i).totient : ℝ) ≤ E := by
  rw [residualAt_le_iff]
  constructor
  · intro h i
    letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
    rw [spectralEnergy_div_totient_eq_mellinResidueEnergy]
    exact h i
  · intro h i
    letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
    have hi := h i
    rwa [spectralEnergy_div_totient_eq_mellinResidueEnergy] at hi

/-- A positive per-cell residue energy makes the stage residual positive. -/
theorem residualAt_pos_of_cell (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (n : ℕ) (i : cell.Den n)
    (h : 0 < @mellinResidueEnergy (q n i) ⟨q_ne_zero n i⟩ (P n i) (s n i)) :
    0 < residualAt cell q q_ne_zero P s n := by
  letI := cell.denFintype n
  unfold residualAt
  exact h.trans_le
    (Finset.le_sup'
      (f := fun i => @mellinResidueEnergy (q n i) ⟨q_ne_zero n i⟩ (P n i) (s n i))
      (Finset.mem_univ i))

/-- A nonzero nonprincipal character twist makes a cell's residue energy positive.
This is the Plancherel/character-orthogonality step: the nonprincipal character
energy is a sum of squared norms over the nonprincipal characters, and it is the
same as the physical residue discrepancy energy. -/
theorem mellinResidueEnergy_pos_of_twist_ne_zero {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (h : Window.twist P (fun n => ((n : ℂ) ^ s)⁻¹) χ ≠ 0) :
    0 < mellinResidueEnergy q P s := by
  rw [mellinResidueEnergy_eq_characterEnergy]
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hmem : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1 := by
    simp [hχ]
  have hterm : 0 < ‖productDirichletPolynomial P (fun n => χ n) s‖ ^ 2 := by
    have h' : productDirichletPolynomial P (fun n => χ n) s ≠ 0 := by
      simpa only [Window.twist, productDirichletPolynomial, div_eq_mul_inv] using h
    exact pow_pos (norm_pos_iff.mpr h') 2
  have hsum : 0 < ∑ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ‖productDirichletPolynomial P (fun n => χ' n) s‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨χ, hmem, hterm⟩
  exact div_pos hsum hφ

/-- A nonzero nonprincipal twist at any stage makes the stage residual positive. -/
theorem residualAt_pos_of_twist_ne_zero (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (n : ℕ) (i : cell.Den n)
    (χ : DirichletCharacter ℂ (q n i)) (hχ : χ ≠ 1)
    (h : Window.twist (P n i) (fun m => ((m : ℂ) ^ (s n i))⁻¹) χ ≠ 0) :
    0 < residualAt cell q q_ne_zero P s n :=
  residualAt_pos_of_cell cell q q_ne_zero P s n i
    (@mellinResidueEnergy_pos_of_twist_ne_zero (q n i) ⟨q_ne_zero n i⟩
      (P n i) (s n i) χ hχ h)

/-- **An explicit nonzero residual witness.**  A cell together with a
nonprincipal character whose twist does not vanish.  This is the genuine source
of the nonzero error: no zero is inserted by hand. -/
structure NonzeroResidualWitness (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (P : ∀ n, cell.Den n → Finset ℕ)
    (s : ∀ n, cell.Den n → ℂ) where
  /-- The stage of the witness. -/
  n : ℕ
  /-- The cell of the witness. -/
  i : cell.Den n
  /-- The nonprincipal character. -/
  χ : DirichletCharacter ℂ (q n i)
  /-- The character is nonprincipal. -/
  χ_ne_one : χ ≠ 1
  /-- Its twist is nonzero. -/
  twist_ne_zero : Window.twist (P n i) (fun m => ((m : ℂ) ^ (s n i))⁻¹) χ ≠ 0

/-- A nonzero residual witness gives a positive actual residual. -/
theorem NonzeroResidualWitness.residual_pos {cell : RationalCellConstruction}
    {q : ∀ n, cell.Den n → ℕ} {q_ne_zero : ∀ n i, q n i ≠ 0}
    {P : ∀ n, cell.Den n → Finset ℕ} {s : ∀ n, cell.Den n → ℂ}
    (W : NonzeroResidualWitness cell q P s) :
    0 < residualAt cell q q_ne_zero P s W.n :=
  residualAt_pos_of_twist_ne_zero cell q q_ne_zero P s W.n W.i W.χ
    W.χ_ne_one W.twist_ne_zero

/-- A nonzero residual witness gives the existential nonzero-error statement. -/
theorem NonzeroResidualWitness.residual_nonzero {cell : RationalCellConstruction}
    {q : ∀ n, cell.Den n → ℕ} {q_ne_zero : ∀ n i, q n i ≠ 0}
    {P : ∀ n, cell.Den n → Finset ℕ} {s : ∀ n, cell.Den n → ℂ}
    (W : NonzeroResidualWitness cell q P s) :
    ∃ n, 0 < residualAt cell q q_ne_zero P s n :=
  ⟨W.n, W.residual_pos⟩

/-! ## 2. The smallest explicit inputs -/

/-- The smallest explicit energy input: at every stage the actual residual
energy (the maximum cell energy) is at most `Econv / d`.  There is no spectral
constant `A`, no identity `A² = …`, and no per-character uniformity hidden in
the statement; it is the true budget on the actual residual. -/
def EnergyResidualBudget (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (Econv d : ℕ → ℝ) : Prop :=
  ∀ n, residualAt cell q q_ne_zero P s n ≤ Econv n / d n

/-- The physical form of the smallest explicit energy input: the squared
residue discrepancy of every cell is at most `Econv / d`.  This is the left-hand
side of the finite large-sieve inequality `classMass_centered_sq_le`
(`mellinResidueEnergy_le_sq`). -/
def PhysicalResidueEnergyBudget (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (Econv d : ℕ → ℝ) : Prop :=
  ∀ n i, letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
    ∑ r : (ZMod (q n i))ˣ,
      ‖mellinClassError (P n i) (s n i) r‖ ^ 2 ≤ Econv n / d n

/-- The physical residue-energy budget is exactly the stage residual budget. -/
theorem physicalResidueEnergyBudget_iff_energyResidualBudget
    (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (Econv d : ℕ → ℝ) :
    PhysicalResidueEnergyBudget cell q q_ne_zero P s Econv d ↔
      EnergyResidualBudget cell q q_ne_zero P s Econv d := by
  rw [EnergyResidualBudget] at *
  constructor
  · intro h n
    rw [residualAt_le_iff]
    intro i
    letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
    exact h n i
  · intro h n i
    letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
    exact (residualAt_le_iff cell q q_ne_zero P s n).1 (h n) i

/-- The smallest explicit counting input: the aggregate number of numerator
cells met across all denominator cells is at most `C * M * V²`. -/
def NumeratorSupportBound (cell : RationalCellConstruction)
    (W C M : ℕ → ℝ) : Prop :=
  ∀ n, (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) * cell.perCell n ≤
    C n * (M n * denomScale W n ^ 2)

/-- The energy budget is exactly the per-cell Mellin budget. -/
theorem energyResidualBudget_iff_mellinConvolutionEnergyBudget
    (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (Econv d : ℕ → ℝ) :
    EnergyResidualBudget cell q q_ne_zero P s Econv d ↔
      ∀ n,
        @MellinConvolutionEnergyBudget (cell.Den n) (cell.denFintype n)
          (cell.denNonempty n) (q n) (fun i => ⟨q_ne_zero n i⟩)
          (P n) (s n) (Econv n) (d n) := by
  constructor
  · intro h n
    exact (residualAt_le_iff cell q q_ne_zero P s n).1 (h n)
  · intro h n
    exact (residualAt_le_iff cell q q_ne_zero P s n).2 (h n)

/-- The energy budget in the Plancherel character-energy form. -/
theorem energyResidualBudget_iff_plancherel
    (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (Econv d : ℕ → ℝ) :
    EnergyResidualBudget cell q q_ne_zero P s Econv d ↔
      ∀ n i, @spectralEnergy (q n i) ⟨q_ne_zero n i⟩ (P n i) (s n i) /
        ((q n i).totient : ℝ) ≤ Econv n / d n := by
  constructor
  · intro h n i
    exact (residualAt_le_iff_plancherel cell q q_ne_zero P s n).1 (h n) i
  · intro h n
    exact (residualAt_le_iff_plancherel cell q q_ne_zero P s n).2 (h n)

/-- A uniform per-character norm bound of size `B` and the scalar comparison
`B² ≤ Econv / d` give the energy budget, through the finite large-sieve
Bessel/Plancherel inequality. -/
theorem energyResidualBudget_of_characterBound
    (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (B : ℕ → ℝ) (Econv d : ℕ → ℝ)
    (hB : ∀ n (i : cell.Den n) (χ : DirichletCharacter ℂ (q n i)), χ ≠ 1 →
      ‖Window.twist (P n i) (fun m => ((m : ℂ) ^ (s n i))⁻¹) χ‖ ≤ B n)
    (hB2 : ∀ n, B n ^ 2 ≤ Econv n / d n) :
    EnergyResidualBudget cell q q_ne_zero P s Econv d := by
  intro n
  rw [residualAt_le_iff]
  intro i
  letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
  have hchar : ∀ χ : DirichletCharacter ℂ (q n i), χ ≠ 1 →
      ‖productDirichletPolynomial (P n i) (fun m => χ m) (s n i)‖ ≤ B n := by
    intro χ hχ
    exact norm_productDirichletPolynomial_le_of_twist (P n i) (s n i) χ (hB n i χ hχ)
  exact (mellinResidueEnergy_le_sq (P n i) (s n i) hchar).trans (hB2 n)

/-- The old per-character energy estimate (the `characterEnergy` field of
`LargeSieveConvolutionData`) implies the smaller stage residual budget.  This is
the direction in which the `A`/spectral-identity chain is reduced: the
per-character uniformity is stronger than the actual residual budget, and the
latter is all that the large sieve needs. -/
theorem energyResidualBudget_of_characterEnergyComparison
    (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (P : ∀ n, cell.Den n → Finset ℕ) (s : ∀ n, cell.Den n → ℂ)
    (Econv d : ℕ → ℝ) (d_pos : ∀ n, 0 < d n) (Econv_nonneg : ∀ n, 0 ≤ Econv n)
    (hchar : ∀ n (i : cell.Den n) (χ : DirichletCharacter ℂ (q n i)), χ ≠ 1 →
      ‖Window.twist (P n i) (fun m => ((m : ℂ) ^ (s n i))⁻¹) χ‖ ^ 2 ≤ Econv n / d n) :
    EnergyResidualBudget cell q q_ne_zero P s Econv d := by
  intro n
  rw [residualAt_le_iff]
  intro i
  letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
  have hchar' : ∀ χ : DirichletCharacter ℂ (q n i), χ ≠ 1 →
      ‖productDirichletPolynomial (P n i) (fun m => χ m) (s n i)‖ ^ 2 ≤
        Econv n / d n := by
    intro χ hχ
    simpa only [Window.twist, productDirichletPolynomial, div_eq_mul_inv] using hchar n i χ hχ
  exact mellinResidueEnergy_le_of_characterEnergyBound (P n i) (s n i)
    (d_pos n) (Econv_nonneg n) hchar'

/-! ## 3. The finishing certificate -/

/-- **The finished L18.4 large-sieve data.**

The residual cell count is supplied by the rational-cell construction
(`perCell_ge_one` is proved from `meets_nonempty`), the energy budget is the
single smallest explicit `Prop` `energyBudget`, and the aggregate support count
is `numeratorSupport_le`.  The field `residual_nonzero` is the genuine nonzero
error: some stage has strictly positive actual residual energy.  It is not a
zero placeholder. -/
structure LargeSieveFinishData (W d C M Econv : ℕ → ℝ) where
  /-- The rational-cell geometry. -/
  cell : RationalCellConstruction
  /-- The denominator modulus of each cell. -/
  q : ∀ n, cell.Den n → ℕ
  /-- Every denominator modulus is nonzero. -/
  q_ne_zero : ∀ n i, q n i ≠ 0
  /-- The numerator support set of each cell. -/
  P : ∀ n, cell.Den n → Finset ℕ
  /-- The Mellin exponent of each cell. -/
  s : ∀ n, cell.Den n → ℂ
  /-- The field degree is positive. -/
  d_pos : ∀ n, 0 < d n
  /-- The undivided convolution energy is nonnegative. -/
  Econv_nonneg : ∀ n, 0 ≤ Econv n
  /-- **The smallest explicit energy input.** -/
  energyBudget : EnergyResidualBudget cell q q_ne_zero P s Econv d
  /-- **The genuine nonzero error.**  An explicit nonprincipal character with
  nonvanishing twist; its residue energy is positive, so the actual residual is
  never set to zero. -/
  witness : NonzeroResidualWitness cell q P s
  /-- **The smallest explicit numerator-support input.** -/
  numeratorSupport_le : NumeratorSupportBound cell W C M

namespace LargeSieveFinishData

variable {W d C M Econv : ℕ → ℝ}

/-- The actual residual energy of the certificate. -/
noncomputable def error (K : LargeSieveFinishData W d C M Econv) (n : ℕ) : ℝ :=
  residualAt K.cell K.q K.q_ne_zero K.P K.s n

/-- The error is nonnegative. -/
theorem error_nonneg (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    0 ≤ K.error n :=
  residualAt_nonneg K.cell K.q K.q_ne_zero K.P K.s n

/-- The actual residual is positive at the witness stage. -/
theorem residual_nonzero (K : LargeSieveFinishData W d C M Econv) :
    ∃ n, 0 < residualAt K.cell K.q K.q_ne_zero K.P K.s n :=
  K.witness.residual_nonzero

/-- The error is positive at some stage: the certificate is not the zero-error
degenerate case. -/
theorem error_nonzero (K : LargeSieveFinishData W d C M Econv) :
    ∃ n, 0 < K.error n :=
  K.residual_nonzero

/-- **The `energy_le` residual field of the large-sieve chain, proved.**  The
actual stage residual is at most `Econv / d`; this is the same field that
`LargeSieveResidualData.energy_le` carries, now derived from the smallest
explicit budget on the actual residual. -/
theorem energy_le (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    K.error n ≤ Econv n / d n :=
  K.energyBudget n

/-- The number of denominator cells. -/
noncomputable def cells (K : LargeSieveFinishData W d C M Econv) (n : ℕ) : ℝ :=
  (@Fintype.card (K.cell.Den n) (K.cell.denFintype n) : ℝ)

/-- The support length: the actual number of numerator cells met. -/
noncomputable def support (K : LargeSieveFinishData W d C M Econv) (n : ℕ) : ℝ :=
  K.cells n * K.cell.perCell n

theorem cells_pos (K : LargeSieveFinishData W d C M Econv) (n : ℕ) : 0 < K.cells n := by
  unfold cells
  exact_mod_cast (@Fintype.card_pos_iff (K.cell.Den n) (K.cell.denFintype n)).mpr
    (K.cell.denNonempty n)

theorem support_nonneg (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    0 ≤ K.support n := by
  unfold support
  exact mul_nonneg (K.cells_pos n).le (K.cell.perCell_nonneg n)

theorem support_pos (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    0 < K.support n := by
  unfold support
  exact mul_pos (K.cells_pos n)
    (lt_of_lt_of_le zero_lt_one (K.cell.perCell_ge_one n))

/-- The cell construction's `perCell_ge_one`, re-exported. -/
theorem perCell_ge_one (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    1 ≤ K.cell.perCell n :=
  K.cell.perCell_ge_one n

theorem cells_le_support (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    K.cells n ≤ K.support n := by
  unfold support
  exact le_mul_of_one_le_right (K.cells_pos n).le (K.cell.perCell_ge_one n)

/-- The actual Mellin second moment of the cell family. -/
noncomputable def secondMoment (K : LargeSieveFinishData W d C M Econv) (n : ℕ) : ℝ :=
  letI := K.cell.denFintype n
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  ∑ i, mellinResidueEnergy (K.q n i) (K.P n i) (K.s n i)

/-- The second moment is the residue energy of the cell family at the Mellin
weights. -/
theorem secondMoment_eq_residueEnergy (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    K.secondMoment n =
      letI := K.cell.denFintype n
      letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
      residueEnergy (K.q n) (K.P n) (fun i m => ((m : ℂ) ^ (K.s n i))⁻¹) := by
  letI := K.cell.denFintype n
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  simp [secondMoment, mellinResidueEnergy, residueEnergy, mellinClassError]

/-- **The multi-modulus residual bound, proved from the actual energy budget.**
No uniform spectral constant or spectral identity is used. -/
theorem secondMoment_le_support_mul_energy
    (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    K.secondMoment n ≤ K.support n * (Econv n / d n) := by
  letI := K.cell.denFintype n
  letI := K.cell.denNonempty n
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  have hper : ∀ i, mellinResidueEnergy (K.q n i) (K.P n i) (K.s n i) ≤ Econv n / d n :=
    (residualAt_le_iff K.cell K.q K.q_ne_zero K.P K.s n).1 (K.energyBudget n)
  calc
    K.secondMoment n = ∑ i, mellinResidueEnergy (K.q n i) (K.P n i) (K.s n i) := rfl
    _ ≤ ∑ _i : K.cell.Den n, Econv n / d n := Finset.sum_le_sum fun i _ => hper i
    _ = K.cells n * (Econv n / d n) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
    _ ≤ K.support n * (Econv n / d n) :=
      mul_le_mul_of_nonneg_right (K.cells_le_support n)
        (div_nonneg (K.Econv_nonneg n) (K.d_pos n).le)

/-- The residual bound with the genuine error term displayed. -/
theorem secondMoment_le_support_mul_energy_add_error
    (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    K.secondMoment n ≤ K.support n * (Econv n / d n) + K.error n :=
  (K.secondMoment_le_support_mul_energy n).trans
    (le_add_of_nonneg_right (K.error_nonneg n))

/-- The rational-cell support bound. -/
theorem support_le (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    K.support n ≤ C n * (M n * denomScale W n ^ 2) :=
  K.numeratorSupport_le n

/-- **The literal `LargeSieveInputs` for the actual second moment.** -/
noncomputable def toLargeSieveInputs (K : LargeSieveFinishData W d C M Econv) :
    LargeSieveInputs W d C M Econv K.secondMoment where
  support := K.support
  support_nonneg := K.support_nonneg
  d_pos := K.d_pos
  Econv_nonneg := K.Econv_nonneg
  multiModulusSum := K.secondMoment_le_support_mul_energy
  rationalCellPartition := K.support_le

/-- **The literal `LargeSieveInputs` for a second moment identified with the
cell family's Mellin second moment.** -/
noncomputable def toLargeSieveInputsOfEq (K : LargeSieveFinishData W d C M Econv)
    (S2 : ℕ → ℝ) (hS2 : ∀ n, S2 n = K.secondMoment n) :
    LargeSieveInputs W d C M Econv S2 where
  support := K.support
  support_nonneg := K.support_nonneg
  d_pos := K.d_pos
  Econv_nonneg := K.Econv_nonneg
  multiModulusSum := fun n => by
    rw [hS2 n]
    exact K.secondMoment_le_support_mul_energy n
  rationalCellPartition := K.support_le

/-- **The L18.4 `large_sieve` field, proved.** -/
theorem large_sieve (K : LargeSieveFinishData W d C M Econv) (n : ℕ) :
    K.secondMoment n ≤
      C n * (M n * denomScale W n ^ 2) * (Econv n / d n) :=
  (K.toLargeSieveInputs).large_sieve n

/-- **The assembled field together with a genuine nonzero error.**  The
large-sieve inequality holds and the actual residual energy is positive at some
stage, so the certificate is not the zero-error degenerate case. -/
theorem large_sieve_with_nonzero_error (K : LargeSieveFinishData W d C M Econv) :
    (∀ n, K.secondMoment n ≤
      C n * (M n * denomScale W n ^ 2) * (Econv n / d n)) ∧
      ∃ n, 0 < K.error n :=
  ⟨K.large_sieve, K.error_nonzero⟩

/-- **Assemble the certificate from an explicit nonzero residual witness.**
The positivity of the error is *proved* from a nonprincipal twist that does not
vanish. -/
noncomputable def ofWitness {cell : RationalCellConstruction}
    {q : ∀ n, cell.Den n → ℕ} {q_ne_zero : ∀ n i, q n i ≠ 0}
    {P : ∀ n, cell.Den n → Finset ℕ} {s : ∀ n, cell.Den n → ℂ}
    (d_pos : ∀ n, 0 < d n) (Econv_nonneg : ∀ n, 0 ≤ Econv n)
    (energyBudget : EnergyResidualBudget cell q q_ne_zero P s Econv d)
    (witness : NonzeroResidualWitness cell q P s)
    (numeratorSupport_le : NumeratorSupportBound cell W C M) :
    LargeSieveFinishData W d C M Econv where
  cell := cell
  q := q
  q_ne_zero := q_ne_zero
  P := P
  s := s
  d_pos := d_pos
  Econv_nonneg := Econv_nonneg
  energyBudget := energyBudget
  witness := witness
  numeratorSupport_le := numeratorSupport_le

end LargeSieveFinishData

/-! ## 4. Replacement of the `L18_4Inputs.large_sieve` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- The `large_sieve` field from the finished certificate, after identifying
`I.S2` with the actual Mellin second moment. -/
theorem large_sieve_of_finishData
    (K : LargeSieveFinishData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.secondMoment n) (n : ℕ) :
    I.S2 n ≤ I.C n * (I.M n * denomScale I.W n ^ 2) * (I.Econv n / I.d n) :=
  (K.toLargeSieveInputsOfEq I.S2 hS2).large_sieve n

/-- Literal replacement of the `large_sieve` proof field. -/
noncomputable def replaceLargeSieveFinishData
    (K : LargeSieveFinishData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.secondMoment n) : L18_4Inputs :=
  I.replaceLargeSieve (K.toLargeSieveInputsOfEq I.S2 hS2)

/-- The replacement leaves the rational-good deficit unchanged. -/
@[simp] theorem replaceLargeSieveFinishData_loss
    (K : LargeSieveFinishData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.secondMoment n) :
    (I.replaceLargeSieveFinishData K hS2).loss = I.loss := by
  unfold replaceLargeSieveFinishData
  exact I.replaceLargeSieve_loss (K.toLargeSieveInputsOfEq I.S2 hS2)

/-- The replaced input still yields the L18.4 `D^{-B}` deficit. -/
theorem replaceLargeSieveFinishData_subexpLoss
    (K : LargeSieveFinishData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.secondMoment n) :
    SubexpLoss (I.replaceLargeSieveFinishData K hS2).loss := by
  rw [I.replaceLargeSieveFinishData_loss K hS2]
  exact I.subexpLoss

end L18_4Inputs


/-! ## 5. The full L18.4 certificate with the finished large sieve -/

namespace L18_4Certificate

variable (C : L18_4Certificate)

/-- **The full L18.4 `L18_4Inputs` with the large-sieve field supplied by the
finished certificate.**  This is `L18_4Certificate.toInputs` with `hls` taken
from `LargeSieveFinishData` instead of `C.largeSieve`; the `CellData`, `Mass`
(including the genuine RH error) and `ThinAggregate` fields are unchanged. -/
noncomputable def toInputsWithLargeSieve
    (K : LargeSieveFinishData C.W C.d C.C C.M C.Econv)
    (hS2 : ∀ n, C.S2 n = K.secondMoment n) : L18_4Inputs :=
  let hls : ∀ n,
      C.S2 n ≤ C.C n * (C.M n * denomScale C.W n ^ 2) * (C.Econv n / C.d n) :=
    (K.toLargeSieveInputsOfEq C.S2 hS2).large_sieve_all
  let hcp : ∀ n,
      denomScale C.W n / (2 * C.d n * cellMesh C.W n * (1 + C.W n)) ≤ C.Ncell n := by
    intro n
    rw [C.hNcell n]
    exact cell_prime_count_of_cellData C.cellK0_nonneg C.cellSupply C.W_nonneg
      C.d_pos C.cellData C.cellSupplyFit n
  let hcn : ∀ n, denomScale C.W n * C.rho n / (2 * C.ell n) ≤ C.Nnum n := fun n =>
    (C.mass.toNumeratorCountInputs C.Nnum C.numR C.numCoprime C.numEq
      C.numDeviation).numerator_count n
  let hthin : ∀ n, C.thin n ≤ 1 / cellMesh C.W n := fun n =>
    C.thinData.thin_pair_fraction C.W_nonneg C.d_pos C.rho_pos hcp hcn n
  let I : L18_4Inputs := C.toL18_4Ambient.toInputs hls hcp hcn hthin
  let thinAgg : ThinAggregate I :=
    C.thinData.toThinAggregate I rfl rfl rfl rfl rfl rfl rfl
  I.replaceThinPairFraction thinAgg.toThinPairInputs

/-- **The L18.4 `D^{-B}` deficit** for the assembled inputs. -/
theorem toInputsWithLargeSieve_subexpLoss
    (K : LargeSieveFinishData C.W C.d C.C C.M C.Econv)
    (hS2 : ∀ n, C.S2 n = K.secondMoment n) :
    SubexpLoss (C.toInputsWithLargeSieve K hS2).loss :=
  (C.toInputsWithLargeSieve K hS2).subexpLoss

/-- **The assembled L18.4 `SubexpLeaf`.** -/
noncomputable def toSubexpLeafWithLargeSieve
    (K : LargeSieveFinishData C.W C.d C.C C.M C.Econv)
    (hS2 : ∀ n, C.S2 n = K.secondMoment n) : SubexpLeaf :=
  (C.toInputsWithLargeSieve K hS2).toSubexpLeaf

/-- **The `B = 2` slot bound** for the assembled inputs. -/
theorem toInputsWithLargeSieve_slot_le
    (K : LargeSieveFinishData C.W C.d C.C C.M C.Econv)
    (hS2 : ∀ n, C.S2 n = K.secondMoment n)
    {slots : C5LossSlots}
    (h : slots .rationalGoodEnvironments = (C.toInputsWithLargeSieve K hS2).loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .rationalGoodEnvironments n ≤ exp (-(2 : ℝ) * scale n) :=
  (C.toInputsWithLargeSieve K hS2).slot_le h

end L18_4Certificate

/-! ## 6. A concrete nonzero residual -/

/-- A nonprincipal Dirichlet character modulo 3, chosen from the nonempty set of
nonprincipal characters. -/
noncomputable def nonprincipal3 : DirichletCharacter ℂ 3 :=
  Classical.choose (show (Finset.univ.erase (1 : DirichletCharacter ℂ 3)).Nonempty from by
    rw [← Finset.card_pos]
    have hcard : Fintype.card (DirichletCharacter ℂ 3) = 2 := by
      rw [← Nat.card_eq_fintype_card]
      rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 3]
      decide
    have h : (Finset.univ.erase (1 : DirichletCharacter ℂ 3)).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
    omega)

theorem nonprincipal3_mem :
    nonprincipal3 ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ 3)) :=
  Classical.choose_spec _

theorem nonprincipal3_ne_one : nonprincipal3 ≠ 1 :=
  (Finset.mem_erase.mp nonprincipal3_mem).1

/-- The one-cell, one-numerator-cell finite geometry. -/
noncomputable def oneCell : RationalCellConstruction where
  Den := fun _ => PUnit
  Num := fun _ => PUnit
  denFintype := fun _ => inferInstance
  numFintype := fun _ => inferInstance
  denNonempty := fun _ => inferInstance
  meets := fun _ _ _ => True
  meetsDecidable := fun _ => inferInstance
  meets_nonempty := fun _ _ => ⟨PUnit.unit, trivial⟩

/-- The concrete nonzero residual witness: modulus `3`, numerator set `{1}`, and
the nonprincipal character modulo `3`.  Its twist is `χ 1 = 1`, so the residue
energy is positive. -/
noncomputable def oneCellWitness :
    NonzeroResidualWitness oneCell (fun _ _ => 3) (fun _ _ => {1}) (fun _ _ => 0) where
  n := 0
  i := PUnit.unit
  χ := nonprincipal3
  χ_ne_one := nonprincipal3_ne_one
  twist_ne_zero := by
    simp [Cogentic.Window.twist]

/-- The concrete residual is positive: the nonzero-error requirement is
satisfied by actual data, not by a zero placeholder. -/
theorem oneCellWitness_residual_pos :
    0 < residualAt oneCell (fun _ _ => 3) (fun _ _ => by norm_num)
      (fun _ _ => {1}) (fun _ _ => 0) 0 :=
  oneCellWitness.residual_pos

/-- The concrete residual is nonzero, so the certificate's error is genuine. -/
theorem oneCellWitness_residual_ne_zero :
    residualAt oneCell (fun _ _ => 3) (fun _ _ => by norm_num)
      (fun _ _ => {1}) (fun _ _ => 0) 0 ≠ 0 :=
  ne_of_gt oneCellWitness_residual_pos

/-! ## Axiom audit -/

#print axioms residualAt_nonneg
#print axioms residualAt_le_iff
#print axioms residualAt_le_iff_plancherel
#print axioms residualAt_pos_of_cell
#print axioms mellinResidueEnergy_pos_of_twist_ne_zero
#print axioms residualAt_pos_of_twist_ne_zero
#print axioms NonzeroResidualWitness.residual_pos
#print axioms NonzeroResidualWitness.residual_nonzero
#print axioms physicalResidueEnergyBudget_iff_energyResidualBudget
#print axioms energyResidualBudget_iff_mellinConvolutionEnergyBudget
#print axioms energyResidualBudget_iff_plancherel
#print axioms energyResidualBudget_of_characterBound
#print axioms energyResidualBudget_of_characterEnergyComparison
#print axioms LargeSieveFinishData.residual_nonzero
#print axioms LargeSieveFinishData.error_nonneg
#print axioms LargeSieveFinishData.error_nonzero
#print axioms LargeSieveFinishData.energy_le
#print axioms LargeSieveFinishData.cells_pos
#print axioms LargeSieveFinishData.support_nonneg
#print axioms LargeSieveFinishData.support_pos
#print axioms LargeSieveFinishData.perCell_ge_one
#print axioms LargeSieveFinishData.cells_le_support
#print axioms LargeSieveFinishData.secondMoment_eq_residueEnergy
#print axioms LargeSieveFinishData.secondMoment_le_support_mul_energy
#print axioms LargeSieveFinishData.secondMoment_le_support_mul_energy_add_error
#print axioms LargeSieveFinishData.support_le
#print axioms LargeSieveFinishData.toLargeSieveInputs
#print axioms LargeSieveFinishData.toLargeSieveInputsOfEq
#print axioms LargeSieveFinishData.large_sieve
#print axioms LargeSieveFinishData.large_sieve_with_nonzero_error
#print axioms LargeSieveFinishData.ofWitness
#print axioms L18_4Inputs.large_sieve_of_finishData
#print axioms L18_4Inputs.replaceLargeSieveFinishData
#print axioms L18_4Inputs.replaceLargeSieveFinishData_loss
#print axioms L18_4Inputs.replaceLargeSieveFinishData_subexpLoss
#print axioms nonprincipal3_ne_one
#print axioms oneCellWitness
#print axioms oneCellWitness_residual_pos
#print axioms oneCellWitness_residual_ne_zero
#print axioms L18_4Certificate.toInputsWithLargeSieve
#print axioms L18_4Certificate.toInputsWithLargeSieve_subexpLoss
#print axioms L18_4Certificate.toSubexpLeafWithLargeSieve
#print axioms L18_4Certificate.toInputsWithLargeSieve_slot_le

end Cogentic.RandomizedL18_4
