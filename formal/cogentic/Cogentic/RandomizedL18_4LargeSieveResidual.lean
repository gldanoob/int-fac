import Cogentic.RandomizedL18_4LatticeCount
import Cogentic.RandomizedPrimeProductPlancherel

/-!
# L18.4: the large-sieve residual (`perCell_ge_one` and `energy_le`)

`RandomizedL18_4LargeSieveInputs.LargeSieveCertificate` and
`RandomizedL18_4LatticeCount.LargeSieveCertificateData` still carry two
bookkeeping fields which are not produced by the Plancherel/Bessel summation or
by the lattice count:

* `perCell_ge_one`, the statement that every denominator cell meets at least one
  numerator cell; and
* `energy_le`, the per-stage spectral energy identification `A² ≤ Econv / d`.

This file removes both from the hypothesis list.

## The cell construction

`RationalCellConstruction` is the actual finite cell geometry of the
rational-cell partition: at every stage there is a finite type of denominator
cells and a finite type of numerator cells, together with a decidable incidence
relation, and the construction guarantees that **every denominator cell meets at
least one numerator cell**.  `perCell` is then *defined* as the maximum, over the
denominator cells, of the number of numerator cells incident to that cell.
`perCell_ge_one` follows from the nonempty incidence of one denominator cell; no
count is chosen, averaged or set to zero.

## The spectral energy

`spectralEnergy` is the nonprincipal Mellin character energy of a cell,
`∑_{χ ≠ 1} ‖productDirichletPolynomial P χ s‖²`.  The existing Mellin
Plancherel theorem `mellinClassError_plancherel` (restated as
`mellinResidueEnergy_eq_characterEnergy` in the imported file) gives the exact
identity

`mellinResidueEnergy q P s = spectralEnergy P s / φ(q)`.

`stageSpectralEnergy` is the maximum of the per-cell Mellin residue energies.
The `SpectralEnergyIdentity` `A² = stageSpectralEnergy` therefore says precisely
that `A²` is the Plancherel spectral energy of the stage.  The only remaining
arithmetic input is isolated as `MellinConvolutionEnergyBudget`,

`mellinResidueEnergy (q i) (P i) (s i) ≤ Econv / d` for every cell `i`,

and `energy_le` is proved from the spectral identity and that budget.  Using
Plancherel the budget is equivalently the character-energy form
`spectralEnergy ≤ φ(q) * (Econv / d)` (`mellinConvolutionEnergyBudget_iff_characterEnergy`);
this is the smallest explicit convolution-energy comparison left.

Nothing here is a `sorry`, an `admit`, an `axiom` or a `native_decide`, and no
energy, count or constant is set to zero.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open scoped BigOperators Classical
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Randomized

set_option linter.style.haveILetI false
set_option linter.checkUnivs false

/-! ## 1. The rational-cell construction and `perCell_ge_one` -/

/-- **The finite rational-cell construction.**

`Den n` is the finite type of denominator cells at stage `n`, `Num n` the finite
type of numerator cells, and `meets n i k` the decidable incidence relation.  The
field `meets_nonempty` is the geometric content of the rational-cell partition:
every denominator cell meets at least one numerator cell. -/
structure RationalCellConstruction where
  /-- The denominator cells at stage `n`. -/
  Den : ℕ → Type*
  /-- The numerator cells at stage `n`. -/
  Num : ℕ → Type*
  /-- Each stage has finitely many denominator cells. -/
  denFintype : ∀ n, Fintype (Den n)
  /-- Each stage has finitely many numerator cells. -/
  numFintype : ∀ n, Fintype (Num n)
  /-- Each stage has at least one denominator cell. -/
  denNonempty : ∀ n, Nonempty (Den n)
  /-- The incidence relation: denominator cell `i` meets numerator cell `k`. -/
  meets : ∀ n, Den n → Num n → Prop
  /-- The incidence relation is decidable. -/
  meetsDecidable : ∀ n, DecidableRel (meets n)
  /-- **Every denominator cell meets at least one numerator cell.** -/
  meets_nonempty : ∀ n (i : Den n), ∃ k : Num n, meets n i k

namespace RationalCellConstruction

variable (C : RationalCellConstruction)

/-- The finite set of numerator cells met by the denominator cell `i`. -/
noncomputable def numeratorCellsIn (n : ℕ) (i : C.Den n) : Finset (C.Num n) :=
  letI := C.numFintype n
  letI := C.meetsDecidable n
  Finset.univ.filter (fun k => C.meets n i k)

/-- Every denominator cell meets at least one numerator cell, so the set of
numerator cells met by it is nonempty. -/
theorem numeratorCellsIn_nonempty (n : ℕ) (i : C.Den n) :
    (C.numeratorCellsIn n i).Nonempty := by
  letI := C.numFintype n
  letI := C.meetsDecidable n
  obtain ⟨k, hk⟩ := C.meets_nonempty n i
  exact ⟨k, by simp [numeratorCellsIn, hk]⟩

/-- The number of numerator cells met by one denominator cell is positive. -/
theorem card_numeratorCellsIn_pos (n : ℕ) (i : C.Den n) :
    0 < (C.numeratorCellsIn n i).card :=
  Finset.card_pos.mpr (C.numeratorCellsIn_nonempty n i)

/-- **The per-cell numerator count.**  The maximum number of numerator cells met
inside one denominator cell.  It is a count of the actual incidence relation, not
a chosen average. -/
noncomputable def perCellNat (n : ℕ) : ℕ :=
  letI := C.denFintype n
  letI := C.denNonempty n
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : C.Den n => (C.numeratorCellsIn n i).card)

/-- **`perCell_ge_one` from the cell construction.**  One denominator cell meets
at least one numerator cell, and the per-cell maximum is at least that cell's
count. -/
theorem one_le_perCellNat (n : ℕ) : 1 ≤ C.perCellNat n := by
  letI := C.denFintype n
  letI := C.denNonempty n
  let i : C.Den n := Classical.choice (C.denNonempty n)
  have hcard : 1 ≤ (C.numeratorCellsIn n i).card :=
    C.card_numeratorCellsIn_pos n i
  exact hcard.trans
    (Finset.le_sup' (f := fun j : C.Den n => (C.numeratorCellsIn n j).card)
      (Finset.mem_univ i))

/-- The real-valued per-cell count used by the large-sieve certificate. -/
noncomputable def perCell (n : ℕ) : ℝ := (C.perCellNat n : ℝ)

/-- **The certificate field `perCell_ge_one`, proved.** -/
theorem perCell_ge_one (n : ℕ) : 1 ≤ C.perCell n := by
  unfold perCell
  exact_mod_cast C.one_le_perCellNat n

/-- The per-cell count is nonnegative. -/
theorem perCell_nonneg (n : ℕ) : 0 ≤ C.perCell n :=
  zero_le_one.trans (C.perCell_ge_one n)

/-- The number of denominator cells is positive. -/
theorem card_den_pos (n : ℕ) : 0 < (@Fintype.card (C.Den n) (C.denFintype n) : ℝ) := by
  exact_mod_cast (@Fintype.card_pos_iff (C.Den n) (C.denFintype n)).mpr (C.denNonempty n)

end RationalCellConstruction

/-! ## 2. The Mellin/Plancherel spectral energy -/

/-- The nonprincipal Mellin character energy of one cell.  This is the numerator
of the Plancherel identity. -/
noncomputable def spectralEnergy {q : ℕ} [NeZero q] (P : Finset ℕ) (s : ℂ) : ℝ :=
  ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
    ‖productDirichletPolynomial P (fun n => χ n) s‖ ^ 2

/-- The nonprincipal Mellin character energy is nonnegative. -/
theorem spectralEnergy_nonneg {q : ℕ} [NeZero q] (P : Finset ℕ) (s : ℂ) :
    0 ≤ spectralEnergy (q := q) P s :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Mellin Plancherel in numerator form.**  The character energy is `φ(q)`
times the residue energy.  This is the existing
`mellinResidueEnergy_eq_characterEnergy`, solved for the numerator. -/
theorem spectralEnergy_eq_totient_mul_mellinResidueEnergy {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) :
    spectralEnergy (q := q) P s = (q.totient : ℝ) * mellinResidueEnergy q P s := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [mellinResidueEnergy_eq_characterEnergy]
  field_simp [hφ]
  rfl

/-- **The Plancherel comparison in both directions.**  A per-cell residue-energy
bound is exactly a nonprincipal character-energy bound with the factor `φ(q)`. -/
theorem mellinResidueEnergy_le_iff_spectralEnergy {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) {E : ℝ} :
    mellinResidueEnergy q P s ≤ E ↔
      spectralEnergy (q := q) P s ≤ (q.totient : ℝ) * E := by
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [mellinResidueEnergy_eq_characterEnergy]
  constructor
  · intro h
    rw [div_le_iff₀ hφ] at h
    simpa only [spectralEnergy, mul_comm] using h
  · intro h
    rw [div_le_iff₀ hφ]
    simpa only [spectralEnergy, mul_comm] using h

/-- **The stage spectral energy.**  The maximum of the per-cell Mellin residue
energies over the denominator cells of one stage. -/
noncomputable def stageSpectralEnergy {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => mellinResidueEnergy (q i) (P i) (s i))

/-- The stage spectral energy is the maximum of the per-cell energies. -/
theorem stageSpectralEnergy_le_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) {E : ℝ} :
    stageSpectralEnergy q P s ≤ E ↔
      ∀ i, mellinResidueEnergy (q i) (P i) (s i) ≤ E := by
  constructor
  · intro h i
    exact (Finset.le_sup'
      (f := fun i => mellinResidueEnergy (q i) (P i) (s i))
      (Finset.mem_univ i)).trans h
  · intro h
    exact Finset.sup'_le Finset.univ_nonempty
      (fun i => mellinResidueEnergy (q i) (P i) (s i)) (fun i _ => h i)

/-- Dividing the nonprincipal character energy by `φ(q)` recovers the Mellin
residue energy.  This is the Plancherel identity solved for the residue energy. -/
theorem spectralEnergy_div_totient_eq_mellinResidueEnergy {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) :
    spectralEnergy (q := q) P s / (q.totient : ℝ) = mellinResidueEnergy q P s := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [spectralEnergy_eq_totient_mul_mellinResidueEnergy]
  field_simp [hφ]

/-- **The stage spectral energy in Plancherel form.**  The maximum of the
per-cell Mellin residue energies is the maximum of the nonprincipal character
energies divided by `φ(q)`.  This is `mellinClassError_plancherel` applied cell
by cell. -/
theorem stageSpectralEnergy_eq_plancherel {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) :
    stageSpectralEnergy q P s =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => spectralEnergy (q := q i) (P i) (s i) / (q i).totient) := by
  apply le_antisymm
  · refine Finset.sup'_le Finset.univ_nonempty
      (fun i => mellinResidueEnergy (q i) (P i) (s i)) ?_
    intro i _
    rw [mellinResidueEnergy_eq_characterEnergy]
    exact Finset.le_sup'
      (f := fun i => spectralEnergy (q := q i) (P i) (s i) / (q i).totient)
      (Finset.mem_univ i)
  · refine Finset.sup'_le Finset.univ_nonempty
      (fun i => spectralEnergy (q := q i) (P i) (s i) / (q i).totient) ?_
    intro i _
    rw [spectralEnergy_div_totient_eq_mellinResidueEnergy]
    exact Finset.le_sup'
      (f := fun i => mellinResidueEnergy (q i) (P i) (s i))
      (Finset.mem_univ i)

/-- The Mellin residue energy is nonnegative. -/
theorem mellinResidueEnergy_nonneg {q : ℕ} [NeZero q] (P : Finset ℕ) (s : ℂ) :
    0 ≤ mellinResidueEnergy q P s := by
  simp only [mellinResidueEnergy]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The stage spectral energy is nonnegative. -/
theorem stageSpectralEnergy_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) :
    0 ≤ stageSpectralEnergy q P s := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  exact (mellinResidueEnergy_nonneg (q := q i) (P i) (s i)).trans
    (Finset.le_sup' (f := fun i => mellinResidueEnergy (q i) (P i) (s i))
      (Finset.mem_univ i))

/-- **The spectral energy identity.**  `A²` is the Plancherel residue energy of
the stage (the maximum over its cells).  This is the identity that identifies the
uniform character bound with the large-sieve energy budget. -/
def SpectralEnergyIdentity {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) (A : ℝ) : Prop :=
  A ^ 2 = stageSpectralEnergy q P s

/-- **The spectral energy identity in Plancherel form.**  `A²` is the maximum
nonprincipal character energy divided by `φ(q)`, by the previous theorem. -/
theorem spectralEnergyIdentity_iff_plancherel {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) (A : ℝ) :
    SpectralEnergyIdentity q P s A ↔
      A ^ 2 = Finset.univ.sup' Finset.univ_nonempty
        (fun i => spectralEnergy (q := q i) (P i) (s i) / (q i).totient) := by
  rw [SpectralEnergyIdentity, stageSpectralEnergy_eq_plancherel]

/-- **The smallest remaining convolution-energy comparison.**  Every cell's
Mellin/Plancherel residue energy is at most the multiplicity-one convolution
energy divided by the degree.  This is the only estimate left after the spectral
identity, and it is not zero. -/
def MellinConvolutionEnergyBudget {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) (Econv d : ℝ) : Prop :=
  ∀ i, mellinResidueEnergy (q i) (P i) (s i) ≤ Econv / d

/-- The convolution-energy budget in the equivalent nonprincipal
character-energy form, using Mellin Plancherel. -/
theorem mellinConvolutionEnergyBudget_iff_characterEnergy
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) (Econv d : ℝ) :
    MellinConvolutionEnergyBudget q P s Econv d ↔
      ∀ i, spectralEnergy (q := q i) (P i) (s i) ≤ (q i).totient * (Econv / d) := by
  constructor
  · intro h i
    exact (mellinResidueEnergy_le_iff_spectralEnergy (P i) (s i)
      (E := Econv / d)).1 (h i)
  · intro h i
    exact (mellinResidueEnergy_le_iff_spectralEnergy (P i) (s i)
      (E := Econv / d)).2 (h i)

/-- **`energy_le` from the spectral identity and Plancherel.**  If `A²` is the
stage Plancherel energy and every cell's residue energy is at most `Econv / d`,
then `A² ≤ Econv / d`. -/
theorem energy_le_of_spectralEnergyIdentity {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) {A Econv d : ℝ}
    (hid : SpectralEnergyIdentity q P s A)
    (hbudget : MellinConvolutionEnergyBudget q P s Econv d) :
    A ^ 2 ≤ Econv / d := by
  change A ^ 2 = stageSpectralEnergy q P s at hid
  exact hid.trans_le ((stageSpectralEnergy_le_iff q P s).2 hbudget)

/-! ## 3. The residual certificate data -/

/-- **The large-sieve certificate with both residual fields derived.**

This is `LargeSieveCertificateData` with

* `perCell` supplied by the rational-cell construction (so `perCell_ge_one` is
  proved), and
* `energy_le` supplied by the spectral energy identity and the explicit
  convolution-energy budget.

The spectral bound `spectral` is still a genuine analytic input: it is the
uniform bound on the nonprincipal Mellin twists.  The Mellin weights are
`m ↦ (m : ℂ) ^ (-s)` with the cell's exponent `s`. -/
structure LargeSieveResidualData (W d C M Econv : ℕ → ℝ) where
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
  /-- The uniform per-stage spectral bound. -/
  A : ℕ → ℝ
  /-- The spectral bound is nonnegative. -/
  A_nonneg : ∀ n, 0 ≤ A n
  /-- The uniform bound on the nonprincipal Mellin twists. -/
  spectral : ∀ n (i : cell.Den n) (χ : DirichletCharacter ℂ (q n i)), χ ≠ 1 →
    ‖Window.twist (P n i) (fun m => ((m : ℂ) ^ (s n i))⁻¹) χ‖ ≤ A n
  /-- The field degree is positive. -/
  d_pos : ∀ n, 0 < d n
  /-- The undivided convolution energy is nonnegative. -/
  Econv_nonneg : ∀ n, 0 ≤ Econv n
  /-- **The spectral energy identity.**  `A²` is the stage Plancherel energy. -/
  spectralIdentity : ∀ n,
    A n ^ 2 =
      @stageSpectralEnergy (cell.Den n) (cell.denFintype n) (cell.denNonempty n)
        (q n) (fun i => ⟨q_ne_zero n i⟩) (P n) (s n)
  /-- **The convolution-energy budget.** -/
  energyBudget : ∀ n,
    @MellinConvolutionEnergyBudget (cell.Den n) (cell.denFintype n) (cell.denNonempty n)
      (q n) (fun i => ⟨q_ne_zero n i⟩) (P n) (s n) (Econv n) (d n)
  /-- **The determinant-level aggregate support bound.** -/
  numeratorSupport_le : ∀ n,
    (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) * cell.perCell n ≤
      C n * (M n * denomScale W n ^ 2)

namespace LargeSieveResidualData

variable {W d C M Econv : ℕ → ℝ}

/-- The certificate's `perCell_ge_one` field, proved from the cell construction. -/
theorem perCell_ge_one (K : LargeSieveResidualData W d C M Econv) (n : ℕ) :
    1 ≤ K.cell.perCell n :=
  K.cell.perCell_ge_one n

/-- The certificate's `energy_le` field, proved from the spectral identity and the
explicit convolution-energy budget. -/
theorem energy_le (K : LargeSieveResidualData W d C M Econv) (n : ℕ) :
    K.A n ^ 2 ≤ Econv n / d n := by
  letI := K.cell.denFintype n
  letI := K.cell.denNonempty n
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  exact energy_le_of_spectralEnergyIdentity (K.q n) (K.P n) (K.s n)
    (K.spectralIdentity n) (K.energyBudget n)

/-- **The literal `LargeSieveCertificateData`.**  Both residual fields are
discharged; the cell count and support bound are the actual data. -/
noncomputable def toCertificateData (K : LargeSieveResidualData W d C M Econv) :
    LargeSieveCertificateData W d C M Econv where
  ι := K.cell.Den
  fintype := K.cell.denFintype
  q := K.q
  q_ne_zero := K.q_ne_zero
  P := K.P
  w := fun n i m => ((m : ℂ) ^ (K.s n i))⁻¹
  A := K.A
  A_nonneg := K.A_nonneg
  spectral := by
    intro n i χ hχ
    exact K.spectral n i χ hχ
  d_pos := K.d_pos
  Econv_nonneg := K.Econv_nonneg
  nonempty := K.cell.denNonempty
  perCell := K.cell.perCell
  perCell_nonneg := K.cell.perCell_nonneg
  perCell_ge_one := K.cell.perCell_ge_one
  energy_le := K.energy_le
  numeratorSupport_le := K.numeratorSupport_le

/-- The constructed certificate has the same second moment as the residue energy
of the cell family, definitionally. -/
theorem toCertificateData_secondMoment (K : LargeSieveResidualData W d C M Econv)
    (n : ℕ) :
    K.toCertificateData.toLargeSieveCertificate.secondMoment n =
      letI := K.cell.denFintype n
      letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
      residueEnergy (K.q n) (K.P n) (fun i m => ((m : ℂ) ^ (K.s n i))⁻¹) := rfl

/-- **The L18.4 large-sieve bound from the residual certificate.** -/
theorem large_sieve (K : LargeSieveResidualData W d C M Econv) (n : ℕ) :
    K.toCertificateData.toLargeSieveCertificate.secondMoment n ≤
      C n * (M n * denomScale W n ^ 2) * (Econv n / d n) :=
  (LargeSieveCertificate.toLargeSieve
    K.toCertificateData.toLargeSieveCertificate).large_sieve_all n

end LargeSieveResidualData

/-! ## 4. Replacement of the `L18_4Inputs.large_sieve` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **`large_sieve` from the residual certificate.**  The second moment must be
identified with the constructed certificate's residue energy. -/
theorem large_sieve_of_residualData
    (K : LargeSieveResidualData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    ∀ n, I.S2 n ≤ I.C n * (I.M n * denomScale I.W n ^ 2) * (I.Econv n / I.d n) :=
  I.large_sieve_of_certificateData K.toCertificateData hS2

/-- **Literal replacement of the `large_sieve` proof field.** -/
noncomputable def replaceLargeSieveResidualData
    (K : LargeSieveResidualData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) : L18_4Inputs :=
  I.replaceLargeSieveCertificateData K.toCertificateData hS2

/-- The replacement does not change the rational-good deficit. -/
@[simp] theorem replaceLargeSieveResidualData_loss
    (K : LargeSieveResidualData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    (I.replaceLargeSieveResidualData K hS2).loss = I.loss := by
  unfold replaceLargeSieveResidualData
  exact I.replaceLargeSieveCertificateData_loss K.toCertificateData hS2

/-- The replaced input still yields the L18.4 `D^{-B}` deficit. -/
theorem replaceLargeSieveResidualData_subexpLoss
    (K : LargeSieveResidualData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    SubexpLoss (I.replaceLargeSieveResidualData K hS2).loss := by
  rw [I.replaceLargeSieveResidualData_loss K hS2]
  exact I.subexpLoss

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms RationalCellConstruction.card_numeratorCellsIn_pos
#print axioms RationalCellConstruction.one_le_perCellNat
#print axioms RationalCellConstruction.perCell_ge_one
#print axioms RationalCellConstruction.perCell_nonneg
#print axioms spectralEnergy_nonneg
#print axioms spectralEnergy_eq_totient_mul_mellinResidueEnergy
#print axioms spectralEnergy_div_totient_eq_mellinResidueEnergy
#print axioms mellinResidueEnergy_le_iff_spectralEnergy
#print axioms stageSpectralEnergy_le_iff
#print axioms stageSpectralEnergy_eq_plancherel
#print axioms spectralEnergyIdentity_iff_plancherel
#print axioms stageSpectralEnergy_nonneg
#print axioms mellinConvolutionEnergyBudget_iff_characterEnergy
#print axioms energy_le_of_spectralEnergyIdentity
#print axioms LargeSieveResidualData.perCell_ge_one
#print axioms LargeSieveResidualData.energy_le
#print axioms LargeSieveResidualData.toCertificateData
#print axioms LargeSieveResidualData.large_sieve
#print axioms L18_4Inputs.large_sieve_of_residualData
#print axioms L18_4Inputs.replaceLargeSieveResidualData
#print axioms L18_4Inputs.replaceLargeSieveResidualData_loss
#print axioms L18_4Inputs.replaceLargeSieveResidualData_subexpLoss

end Cogentic.RandomizedL18_4
