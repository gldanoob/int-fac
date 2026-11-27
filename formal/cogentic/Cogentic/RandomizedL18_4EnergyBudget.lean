import Cogentic.RandomizedL18_4LargeSieveResidual

/-!
# L18.4: the Mellin convolution-energy budget from Plancherel and a scalar comparison

`RandomizedL18_4LargeSieveResidual.LargeSieveResidualData` still carries the
per-cell inequality

`MellinConvolutionEnergyBudget q P s Econv d`,
i.e. `mellinResidueEnergy (q i) (P i) (s i) ≤ Econv / d` for every denominator
cell `i`.

This file removes that field from the input list.  The reduction has exactly two
pieces.

## 1. The spectral Plancherel bound

By `mellinResidueEnergy_eq_characterEnergy`, the residue energy of a cell is the
nonprincipal Mellin character energy divided by `φ(q)`:

`mellinResidueEnergy q P s = (∑_{χ ≠ 1} ‖P(χ, s)‖²) / φ(q)`.

The existing per-character Mellin estimate `mellinResidueEnergy_le_sq` — the
Bessel/Plancherel bound, which costs no factor for the number of characters —
turns a uniform bound `‖P(χ, s)‖ ≤ A` on the nonprincipal twists into

`mellinResidueEnergy q P s ≤ A²`.

In the residual certificate this uniform bound is precisely the `spectral` field
(restated on `productDirichletPolynomial` by
`norm_productDirichletPolynomial_le_of_twist`).

## 2. The scalar convolution-energy comparison

After Step 1 the whole cell family is bounded by the single number `A²`.
Consequently the per-cell budget is implied by the scalar inequality

`A² ≤ Econv / d`   (`ConvolutionEnergyComparison A Econv d`),

which is exactly the paper's comparison of the multiplicity-one product-
convolution energy `Econv` with the sharp spectral energy `A²`, divided by the
field degree `d`.  This is the smallest explicit `Prop` that remains: it has no
cell index and no character index.

With the spectral identity `A² = stageSpectralEnergy` the reduction is moreover
*exact*: the per-cell budget and the scalar comparison are equivalent
(`mellinConvolutionEnergyBudget_iff_convolutionComparison`).  Thus nothing is
lost and nothing is set to zero.

## The certificate

`LargeSieveSpectralData` is `LargeSieveResidualData` with the `energyBudget`
field replaced by the scalar `convolutionComparison`.  Its `energyBudget` is
*proved* from the per-character bound and the scalar comparison, and
`toResidualData` supplies a literal `LargeSieveResidualData`.  All downstream
L18.4 conclusions (`energy_le`, `large_sieve`, and the replacement of the
`L18_4Inputs.large_sieve` field) follow from it unchanged.

For the concrete prime-bin numerator sets the per-character bound is the existing
critical-line Mellin estimate
`primeBinProducts_mellin_energy_from_critical_line`; the corollary
`exists_mellinConvolutionEnergyBudget_primeBinProducts_of_criticalLine` reduces
the budget in that case to an explicit comparison of the Mellin envelope square
with `Econv / d`.

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

/-! ## 1. Per-character Mellin bounds and the Plancherel energy -/

/-- A per-character nonprincipal Mellin bound for a family of cells.  The bound
`A i` is allowed to depend on the cell but not on the character. -/
def MellinCharacterEnergyBound {ι : Type*} (q : ι → ℕ)
    (P : ι → Finset ℕ) (s : ι → ℂ) (A : ι → ℝ) : Prop :=
  ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
    ‖productDirichletPolynomial (P i) (fun n => χ n) (s i)‖ ≤ A i

/-- The residual certificate states the per-character bound on `Window.twist`
with the Mellin weight `m ↦ (m : ℂ) ^ (-s)`.  This is the same quantity as the
product Dirichlet polynomial, so the bound transfers verbatim. -/
theorem norm_productDirichletPolynomial_le_of_twist {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) {A : ℝ}
    (h : ‖Window.twist P (fun n => ((n : ℂ) ^ s)⁻¹) χ‖ ≤ A) :
    ‖productDirichletPolynomial P (fun n => χ n) s‖ ≤ A := by
  simpa only [Window.twist, productDirichletPolynomial, div_eq_mul_inv] using h

/-- **The Plancherel/Bessel per-cell bound.**  A uniform bound on the
nonprincipal product polynomials bounds the whole Mellin residue energy by
`A²`, with no factor for the number of characters. -/
theorem mellinResidueEnergy_le_sq_of_characterBound {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) {A : ℝ}
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖productDirichletPolynomial P (fun n => χ n) s‖ ≤ A) :
    mellinResidueEnergy q P s ≤ A ^ 2 :=
  mellinResidueEnergy_le_sq P s h

/-- **The spectral Plancherel bound.**  The nonprincipal character energy of a
cell is at most `φ(q)` times the square of the per-character Mellin bound.  This
is Plancherel applied to the Bessel bound of `mellinResidueEnergy_le_sq`. -/
theorem spectralEnergy_le_totient_mul_sq_of_characterBound {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) {A : ℝ}
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖productDirichletPolynomial P (fun n => χ n) s‖ ≤ A) :
    spectralEnergy (q := q) P s ≤ (q.totient : ℝ) * A ^ 2 := by
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  calc
    spectralEnergy (q := q) P s = (q.totient : ℝ) * mellinResidueEnergy q P s :=
      spectralEnergy_eq_totient_mul_mellinResidueEnergy P s
    _ ≤ (q.totient : ℝ) * A ^ 2 :=
      mul_le_mul_of_nonneg_left (mellinResidueEnergy_le_sq_of_characterBound P s h) hφ

/-! ## 2. The scalar convolution-energy comparison -/

/-- **The smallest explicit remaining energy input.**  The sharp spectral energy
`A²` is at most the multiplicity-one convolution energy divided by the field
degree.  There is no cell index, no character index and no hidden constant. -/
def ConvolutionEnergyComparison (A Econv d : ℝ) : Prop :=
  A ^ 2 ≤ Econv / d

/-- **The budget from per-character bounds and the scalar comparison.**  This is
the reduction: each cell's Mellin residue energy is bounded by `A i²` through
Plancherel/Bessel, and the scalar comparison bounds `A i²` by `Econv / d`. -/
theorem mellinConvolutionEnergyBudget_of_characterBound {ι : Type*} [Fintype ι]
    [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (s : ι → ℂ)
    (A : ι → ℝ) {Econv d : ℝ}
    (hchar : MellinCharacterEnergyBound q P s A)
    (hcomp : ∀ i, ConvolutionEnergyComparison (A i) Econv d) :
    MellinConvolutionEnergyBudget q P s Econv d := by
  intro i
  exact (mellinResidueEnergy_le_sq_of_characterBound (P i) (s i) (hchar i)).trans
    (hcomp i)

/-- **The budget directly from the residual certificate's `spectral` field.**
The Mellin twist bound is stated on `Window.twist`; it transfers to the product
Dirichlet polynomial and then the scalar comparison gives the budget. -/
theorem mellinConvolutionEnergyBudget_of_twistBound {ι : Type*} [Fintype ι]
    [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (s : ι → ℂ)
    (A : ι → ℝ) {Econv d : ℝ}
    (hspec : ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
      ‖Window.twist (P i) (fun m => ((m : ℂ) ^ (s i))⁻¹) χ‖ ≤ A i)
    (hcomp : ∀ i, ConvolutionEnergyComparison (A i) Econv d) :
    MellinConvolutionEnergyBudget q P s Econv d :=
  mellinConvolutionEnergyBudget_of_characterBound q P s A
    (fun i χ hχ =>
      norm_productDirichletPolynomial_le_of_twist (P i) (s i) χ (hspec i χ hχ))
    hcomp

/-- The same reduction with one uniform stage constant `A`. -/
theorem mellinConvolutionEnergyBudget_of_uniformCharacterBound {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) (A Econv d : ℝ)
    (hchar : ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
      ‖productDirichletPolynomial (P i) (fun n => χ n) (s i)‖ ≤ A)
    (hcomp : ConvolutionEnergyComparison A Econv d) :
    MellinConvolutionEnergyBudget q P s Econv d :=
  mellinConvolutionEnergyBudget_of_characterBound q P s (fun _ => A)
    (fun i => hchar i) (fun _ => hcomp)

/-- **The same reduction through the Plancherel character-energy form.**  Using
`spectralEnergy ≤ φ(q) A²` and the scalar comparison gives the character-energy
bound which is equivalent to the budget. -/
theorem mellinConvolutionEnergyBudget_of_plancherelCharacterBound {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) (A : ι → ℝ) {Econv d : ℝ}
    (hchar : MellinCharacterEnergyBound q P s A)
    (hcomp : ∀ i, ConvolutionEnergyComparison (A i) Econv d) :
    MellinConvolutionEnergyBudget q P s Econv d := by
  rw [mellinConvolutionEnergyBudget_iff_characterEnergy]
  intro i
  calc
    spectralEnergy (q := q i) (P i) (s i) ≤ (q i).totient * A i ^ 2 :=
      spectralEnergy_le_totient_mul_sq_of_characterBound (P i) (s i) (hchar i)
    _ ≤ (q i).totient * (Econv / d) :=
      mul_le_mul_of_nonneg_left (hcomp i) (Nat.cast_nonneg _)

/-! ## 3. The exact scalar form of the budget -/

/-- **The budget is exactly the scalar stage-energy comparison.**  Since
`stageSpectralEnergy` is the maximum of the per-cell residue energies, the
per-cell family of inequalities is the single inequality
`stageSpectralEnergy ≤ Econv / d`. -/
theorem mellinConvolutionEnergyBudget_iff_stageSpectralEnergy_le {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) {Econv d : ℝ} :
    MellinConvolutionEnergyBudget q P s Econv d ↔
      stageSpectralEnergy q P s ≤ Econv / d := by
  constructor
  · intro h
    exact (stageSpectralEnergy_le_iff q P s).2 h
  · intro h
    exact (stageSpectralEnergy_le_iff q P s).1 h

/-- **The budget in the Plancherel spectral form.**  The maximum over the cells
of the normalized nonprincipal character energy is at most `Econv / d`. -/
theorem mellinConvolutionEnergyBudget_iff_plancherelEnergy_le {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) {Econv d : ℝ} :
    MellinConvolutionEnergyBudget q P s Econv d ↔
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => spectralEnergy (q := q i) (P i) (s i) / (q i).totient) ≤
        Econv / d := by
  rw [mellinConvolutionEnergyBudget_iff_stageSpectralEnergy_le,
    stageSpectralEnergy_eq_plancherel]

/-- **Exactness of the reduction.**  With the spectral identity
`A² = stageSpectralEnergy`, the per-cell budget is equivalent to the single
scalar comparison `A² ≤ Econv / d`.  Nothing is lost in passing to the scalar
form. -/
theorem mellinConvolutionEnergyBudget_iff_convolutionComparison {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) {A Econv d : ℝ}
    (hid : A ^ 2 = stageSpectralEnergy q P s) :
    MellinConvolutionEnergyBudget q P s Econv d ↔
      ConvolutionEnergyComparison A Econv d := by
  rw [mellinConvolutionEnergyBudget_iff_stageSpectralEnergy_le, ← hid]
  rfl

/-- The scalar comparison implies the budget as soon as the spectral identity
identifies `A²` with the stage energy.  This form does not require a per-character
bound: it is the exact equivalence above in the forward direction. -/
theorem mellinConvolutionEnergyBudget_of_convolutionComparison {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) {A Econv d : ℝ}
    (hid : A ^ 2 = stageSpectralEnergy q P s)
    (hcomp : ConvolutionEnergyComparison A Econv d) :
    MellinConvolutionEnergyBudget q P s Econv d :=
  (mellinConvolutionEnergyBudget_iff_convolutionComparison q P s hid).2 hcomp

/-! ## 4. The critical-line Mellin envelope supplies the per-character bound -/

/-- **The budget for prime-bin products from the critical-line Mellin envelope.**
For disjoint prime-bin numerator sets the existing theorem
`primeBinProducts_mellin_energy_from_critical_line` supplies the per-character
bound with the explicit envelope.  The only remaining comparison is the scalar
one between the envelope square and `Econv / d`. -/
theorem exists_mellinConvolutionEnergyBudget_primeBinProducts_of_criticalLine
    (line : DirichletLZerosOnLine) {ι : Type} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (A B : ι → ℕ) (hB : ∀ i, 2 ≤ B i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (σ t : ℝ) (hσ : 0 ≤ σ) {Econv d : ℝ} :
    ∃ K : ℝ, 0 < K ∧
      ((∀ i, (∏ j, K * Real.sqrt (B j) *
        (1 + Real.log ((q i) * ((B j : ℝ) + |t| + 2))) ^ 3) ^ 2 ≤ Econv / d) →
      MellinConvolutionEnergyBudget q (fun _ => primeBinProducts (ι := ι) A B)
        (fun _ => (σ : ℂ) + t * Complex.I) Econv d) := by
  obtain ⟨K, hK, hb⟩ :=
    mellinResidueEnergy_primeBinProducts_le_from_critical_line line
  refine ⟨K, hK, fun henv => ?_⟩
  intro i
  exact (hb (q := q i) (A := A) (B := B) hB hAB hdisj σ t hσ).trans (henv i)

/-! ## 5. The certificate with the per-cell budget removed -/

/-- **The large-sieve spectral certificate.**  This is
`LargeSieveResidualData` with the per-cell `energyBudget` field replaced by the
single scalar comparison `convolutionComparison`.  The per-cell Mellin energy
budget is proved below from the per-character `spectral` field and this scalar,
using Plancherel/Bessel. -/
structure LargeSieveSpectralData (W d C M Econv : ℕ → ℝ) where
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
  /-- The uniform bound on the nonprincipal Mellin twists.  This is the
  per-character input of Plancherel/Bessel. -/
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
  /-- **The smallest explicit energy comparison.**  `A²` is at most the
  multiplicity-one convolution energy divided by the degree. -/
  convolutionComparison : ∀ n,
    ConvolutionEnergyComparison (A n) (Econv n) (d n)
  /-- **The determinant-level aggregate support bound.** -/
  numeratorSupport_le : ∀ n,
    (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) * cell.perCell n ≤
      C n * (M n * denomScale W n ^ 2)

namespace LargeSieveSpectralData

variable {W d C M Econv : ℕ → ℝ}

/-- The per-character Plancherel bound attached to a spectral certificate. -/
theorem characterBound (K : LargeSieveSpectralData W d C M Econv) (n : ℕ) :
    @MellinCharacterEnergyBound (K.cell.Den n) (K.q n)
      (K.P n) (K.s n) (fun _ => K.A n) := by
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  intro i χ hχ
  exact norm_productDirichletPolynomial_le_of_twist (K.P n i) (K.s n i) χ
    (K.spectral n i χ hχ)

/-- **The per-cell Mellin convolution-energy budget, proved.**  Plancherel/Bessel
bounds every cell by `A²`, and the scalar comparison bounds `A²` by `Econv / d`. -/
theorem energyBudget (K : LargeSieveSpectralData W d C M Econv) (n : ℕ) :
    @MellinConvolutionEnergyBudget (K.cell.Den n) (K.cell.denFintype n)
      (K.cell.denNonempty n) (K.q n) (fun i => ⟨K.q_ne_zero n i⟩)
      (K.P n) (K.s n) (Econv n) (d n) := by
  letI := K.cell.denFintype n
  letI := K.cell.denNonempty n
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  refine mellinConvolutionEnergyBudget_of_characterBound (K.q n) (K.P n) (K.s n)
    (fun _ => K.A n) ?_ ?_
  · intro i χ hχ
    exact norm_productDirichletPolynomial_le_of_twist (K.P n i) (K.s n i) χ
      (K.spectral n i χ hχ)
  · intro i
    exact K.convolutionComparison n

/-- **The certificate's `energy_le`, proved directly from the scalar
comparison.** -/
theorem energy_le (K : LargeSieveSpectralData W d C M Econv) (n : ℕ) :
    K.A n ^ 2 ≤ Econv n / d n :=
  K.convolutionComparison n

/-- The certificate's `perCell_ge_one`, from the rational-cell construction. -/
theorem perCell_ge_one (K : LargeSieveSpectralData W d C M Econv) (n : ℕ) :
    1 ≤ K.cell.perCell n :=
  K.cell.perCell_ge_one n

/-- **The literal `LargeSieveResidualData`.**  The `energyBudget` field is no
longer an input: it is supplied by `energyBudget` above. -/
noncomputable def toResidualData (K : LargeSieveSpectralData W d C M Econv) :
    LargeSieveResidualData W d C M Econv where
  cell := K.cell
  q := K.q
  q_ne_zero := K.q_ne_zero
  P := K.P
  s := K.s
  A := K.A
  A_nonneg := K.A_nonneg
  spectral := K.spectral
  d_pos := K.d_pos
  Econv_nonneg := K.Econv_nonneg
  spectralIdentity := K.spectralIdentity
  energyBudget := K.energyBudget
  numeratorSupport_le := K.numeratorSupport_le

/-- **The literal `LargeSieveCertificateData`.** -/
noncomputable abbrev toCertificateData (K : LargeSieveSpectralData W d C M Econv) :
    LargeSieveCertificateData W d C M Econv :=
  K.toResidualData.toCertificateData

/-- The constructed certificate has the same second moment as the residue energy
of the cell family, definitionally. -/
theorem toCertificateData_secondMoment (K : LargeSieveSpectralData W d C M Econv)
    (n : ℕ) :
    K.toCertificateData.toLargeSieveCertificate.secondMoment n =
      letI := K.cell.denFintype n
      letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
      residueEnergy (K.q n) (K.P n) (fun i m => ((m : ℂ) ^ (K.s n i))⁻¹) :=
  K.toResidualData.toCertificateData_secondMoment n

/-- **The L18.4 large-sieve bound from the spectral certificate.** -/
theorem large_sieve (K : LargeSieveSpectralData W d C M Econv) (n : ℕ) :
    K.toCertificateData.toLargeSieveCertificate.secondMoment n ≤
      C n * (M n * denomScale W n ^ 2) * (Econv n / d n) :=
  K.toResidualData.large_sieve n

end LargeSieveSpectralData

/-! ## 6. Replacement of the `L18_4Inputs.large_sieve` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **`large_sieve` from the spectral certificate.**  The second moment must be
identified with the constructed certificate's residue energy. -/
theorem large_sieve_of_spectralData
    (K : LargeSieveSpectralData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    ∀ n, I.S2 n ≤ I.C n * (I.M n * denomScale I.W n ^ 2) * (I.Econv n / I.d n) :=
  I.large_sieve_of_residualData K.toResidualData hS2

/-- **Literal replacement of the `large_sieve` proof field.** -/
noncomputable def replaceLargeSieveSpectralData
    (K : LargeSieveSpectralData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) : L18_4Inputs :=
  I.replaceLargeSieveResidualData K.toResidualData hS2

/-- The replacement does not change the rational-good deficit. -/
@[simp] theorem replaceLargeSieveSpectralData_loss
    (K : LargeSieveSpectralData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    (I.replaceLargeSieveSpectralData K hS2).loss = I.loss := by
  unfold replaceLargeSieveSpectralData
  exact I.replaceLargeSieveResidualData_loss K.toResidualData hS2

/-- The replaced input still yields the L18.4 `D^{-B}` deficit. -/
theorem replaceLargeSieveSpectralData_subexpLoss
    (K : LargeSieveSpectralData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    SubexpLoss (I.replaceLargeSieveSpectralData K hS2).loss := by
  rw [I.replaceLargeSieveSpectralData_loss K hS2]
  exact I.subexpLoss

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms norm_productDirichletPolynomial_le_of_twist
#print axioms mellinResidueEnergy_le_sq_of_characterBound
#print axioms spectralEnergy_le_totient_mul_sq_of_characterBound
#print axioms mellinConvolutionEnergyBudget_of_characterBound
#print axioms mellinConvolutionEnergyBudget_of_twistBound
#print axioms mellinConvolutionEnergyBudget_of_uniformCharacterBound
#print axioms mellinConvolutionEnergyBudget_of_plancherelCharacterBound
#print axioms mellinConvolutionEnergyBudget_iff_stageSpectralEnergy_le
#print axioms mellinConvolutionEnergyBudget_iff_plancherelEnergy_le
#print axioms mellinConvolutionEnergyBudget_iff_convolutionComparison
#print axioms mellinConvolutionEnergyBudget_of_convolutionComparison
#print axioms exists_mellinConvolutionEnergyBudget_primeBinProducts_of_criticalLine
#print axioms LargeSieveSpectralData.characterBound
#print axioms LargeSieveSpectralData.energyBudget
#print axioms LargeSieveSpectralData.energy_le
#print axioms LargeSieveSpectralData.toResidualData
#print axioms LargeSieveSpectralData.large_sieve
#print axioms L18_4Inputs.large_sieve_of_spectralData
#print axioms L18_4Inputs.replaceLargeSieveSpectralData
#print axioms L18_4Inputs.replaceLargeSieveSpectralData_loss
#print axioms L18_4Inputs.replaceLargeSieveSpectralData_subexpLoss

end Cogentic.RandomizedL18_4
