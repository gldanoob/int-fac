import Cogentic.RandomizedL18_4EnergyBudget

/-!
# L18.4: the per-character convolution-energy estimate

`RandomizedL18_4EnergyBudget.LargeSieveSpectralData` still carries the scalar
comparison

`ConvolutionEnergyComparison (A n) (Econv n) (d n)`, i.e. `A n ^ 2 ≤ Econv n / d n`,

as a field.  This file removes that field from the certificate.

## The reduction

The scalar comparison is not an independent analytic fact: after the spectral
identity `A n ^ 2 = stageSpectralEnergy` it is exactly the statement that the
maximum cell energy is at most `Econv / d`.  By
`stageSpectralEnergy_le_iff` this is the per-cell family

`mellinResidueEnergy (q i) (P i) (s i) ≤ Econv / d`,

and by Mellin Plancherel
(`mellinResidueEnergy_eq_characterEnergy`) each cell energy is the average over
the reduced residue classes of the nonprincipal character energy.  Hence the
whole scalar comparison follows from the *single-character* estimate

`‖productDirichletPolynomial (P i) (χ ·) (s i)‖ ^ 2 ≤ Econv / d`

for every nonprincipal character `χ`.

This is the smallest explicit per-character energy estimate of the reduction:
there is no cell-level scalar, no uniformity in `A`, and no hidden constant.  Each
character receives one full budget `Econv / d`; there are at most `φ(q i)` of
them, so their total character energy is at most `φ(q i) * (Econv / d)`, and
Plancherel's division by `φ(q i)` returns exactly `Econv / d`.  Nothing is lost
and nothing is set to zero.

## The certificate

`LargeSieveConvolutionData` is `LargeSieveSpectralData` with the
`convolutionComparison` field replaced by the per-character estimate
`characterEnergy`.  The scalar comparison `convolutionComparison` is *proved*
from `spectralIdentity` and `characterEnergy`
(`LargeSieveConvolutionData.convolutionComparison`), and `toSpectralData`
supplies a literal `LargeSieveSpectralData`.  All downstream L18.4 conclusions
(`energyBudget`, `energy_le`, `large_sieve`, and the replacement of the
`L18_4Inputs.large_sieve` field) follow from it unchanged.

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

/-! ## 1. The number of nonprincipal characters -/

/-- The nonprincipal Dirichlet characters number at most `φ(q)`.  This is the
counting input of the Plancherel average: there are exactly `φ(q)` characters in
all, and the principal character is one of them. -/
theorem card_nonprincipal_le_totient (q : ℕ) [NeZero q] :
    ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ (q.totient : ℝ) := by
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
    calc
      (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤
          (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_erase_le
      _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
      _ = q.totient := hcard
  exact_mod_cast h

/-! ## 2. The per-character energy estimate -/

/-- **The smallest explicit per-character energy estimate.**  Every nonprincipal
character twist of a cell contributes at most `Econv / d` squared energy.  This is
the sharp per-character form of the scalar convolution-energy comparison: the
cell has at most `φ(q)` nonprincipal character slots, so summing one budget
`Econv / d` per slot and dividing by `φ(q)` returns exactly `Econv / d`, with no
extra factor and no hidden constant. -/
def CharacterEnergyComparison {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) (Econv d : ℝ) : Prop :=
  ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
    ‖productDirichletPolynomial (P i) (fun n => χ n) (s i)‖ ^ 2 ≤ Econv / d

/-- The per-character estimate stated on the Mellin twist used by the residual
certificate.  It is the same quantity as `CharacterEnergyComparison` after
unfolding `Window.twist` and `productDirichletPolynomial`. -/
def TwistEnergyComparison {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) (Econv d : ℝ) : Prop :=
  ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
    ‖Window.twist (P i) (fun m => ((m : ℂ) ^ (s i))⁻¹) χ‖ ^ 2 ≤ Econv / d

/-- The twist form and the product-polynomial form of the per-character estimate
are literally the same inequality. -/
theorem characterEnergyComparison_of_twistEnergyComparison {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) {Econv d : ℝ}
    (h : TwistEnergyComparison q P s Econv d) :
    CharacterEnergyComparison q P s Econv d := by
  intro i χ hχ
  simpa only [Window.twist, productDirichletPolynomial, div_eq_mul_inv] using h i χ hχ

/-! ## 3. From one character to the cell energy -/

/-- **Summing the per-character estimate.**  If every nonprincipal character of
a single cell contributes at most `E / d` squared energy, the total nonprincipal
character energy is at most `φ(q) * (E / d)`: there are at most `φ(q)` character
slots. -/
theorem spectralEnergy_le_totient_mul_of_characterEnergyBound {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) {E d : ℝ} (hd : 0 < d) (hE : 0 ≤ E)
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖productDirichletPolynomial P (fun n => χ n) s‖ ^ 2 ≤ E / d) :
    spectralEnergy (q := q) P s ≤ (q.totient : ℝ) * (E / d) := by
  have hc : 0 ≤ E / d := div_nonneg hE hd.le
  rw [spectralEnergy]
  calc
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖productDirichletPolynomial P (fun n => χ n) s‖ ^ 2) ≤
        ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, E / d :=
      Finset.sum_le_sum fun χ hχ => h χ (Finset.mem_erase.mp hχ).1
    _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * (E / d) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q.totient : ℝ) * (E / d) :=
      mul_le_mul_of_nonneg_right (card_nonprincipal_le_totient q) hc

/-- **From one character to the Mellin residue energy.**  Dividing the
nonprincipal character energy by `φ(q)` (Mellin Plancherel) and using the
per-character estimate bounds the cell residue energy by `E / d`. -/
theorem mellinResidueEnergy_le_of_characterEnergyBound {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) {E d : ℝ} (hd : 0 < d) (hE : 0 ≤ E)
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖productDirichletPolynomial P (fun n => χ n) s‖ ^ 2 ≤ E / d) :
    mellinResidueEnergy q P s ≤ E / d := by
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hspec := spectralEnergy_le_totient_mul_of_characterEnergyBound P s hd hE h
  rw [mellinResidueEnergy_eq_characterEnergy]
  calc
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖productDirichletPolynomial P (fun n => χ n) s‖ ^ 2) / (q.totient : ℝ) =
        spectralEnergy (q := q) P s / (q.totient : ℝ) := by
      rw [spectralEnergy]
    _ ≤ ((q.totient : ℝ) * (E / d)) / (q.totient : ℝ) :=
      div_le_div_of_nonneg_right hspec hφ.le
    _ = E / d := by
      field_simp [hφ.ne']

/-! ## 4. The scalar comparison, proved -/

/-- **The scalar convolution-energy comparison from the per-character estimate.**
Together with the spectral identity `A² = stageSpectralEnergy`, the per-character
estimate bounds every cell's residue energy, hence the stage maximum, by
`Econv / d`. -/
theorem convolutionEnergyComparison_of_characterEnergyBound {ι : Type*} [Fintype ι]
    [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (s : ι → ℂ)
    {A Econv d : ℝ} (hA : A ^ 2 = stageSpectralEnergy q P s)
    (hd : 0 < d) (hE : 0 ≤ Econv)
    (hchar : CharacterEnergyComparison q P s Econv d) :
    ConvolutionEnergyComparison A Econv d := by
  rw [ConvolutionEnergyComparison, hA]
  exact (stageSpectralEnergy_le_iff q P s).2 fun i =>
    mellinResidueEnergy_le_of_characterEnergyBound (P i) (s i) hd hE (hchar i)

/-- **The scalar comparison from the twist form of the per-character estimate.**
This is the version consumed by the residual certificate, whose spectral input is
stated on `Window.twist`. -/
theorem convolutionEnergyComparison_of_twistEnergyBound {ι : Type*} [Fintype ι]
    [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (s : ι → ℂ)
    {A Econv d : ℝ} (hA : A ^ 2 = stageSpectralEnergy q P s)
    (hd : 0 < d) (hE : 0 ≤ Econv)
    (hchar : TwistEnergyComparison q P s Econv d) :
    ConvolutionEnergyComparison A Econv d :=
  convolutionEnergyComparison_of_characterEnergyBound q P s hA hd hE
    (characterEnergyComparison_of_twistEnergyComparison q P s hchar)

/-- **The scalar comparison is exactly the stage-energy comparison.**  Under the
spectral identity `A² = stageSpectralEnergy`, `ConvolutionEnergyComparison` has no
independent content: it is the single inequality `stageSpectralEnergy ≤ Econv / d`
of the actual stage definition. -/
theorem convolutionEnergyComparison_iff_stageSpectralEnergy_le {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (s : ι → ℂ) {A Econv d : ℝ}
    (hid : A ^ 2 = stageSpectralEnergy q P s) :
    ConvolutionEnergyComparison A Econv d ↔
      stageSpectralEnergy q P s ≤ Econv / d := by
  rw [ConvolutionEnergyComparison, hid]

/-! ## 5. The certificate without the scalar comparison -/

/-- **The large-sieve spectral certificate with the scalar comparison discharged.**

This is `LargeSieveSpectralData` with the `convolutionComparison` field removed
and replaced by the per-character energy estimate `characterEnergy`.  The scalar
comparison is proved below, so this structure contains strictly more explicit
information and no scalar energy input at the stage level. -/
structure LargeSieveConvolutionData (W d C M Econv : ℕ → ℝ) where
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
  /-- **The per-character energy estimate.**  Every nonprincipal character
  contributes at most the full budget `Econv / d`. -/
  characterEnergy : ∀ n (i : cell.Den n) (χ : DirichletCharacter ℂ (q n i)), χ ≠ 1 →
    ‖Window.twist (P n i) (fun m => ((m : ℂ) ^ (s n i))⁻¹) χ‖ ^ 2 ≤
      Econv n / d n
  /-- **The determinant-level aggregate support bound.** -/
  numeratorSupport_le : ∀ n,
    (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) * cell.perCell n ≤
      C n * (M n * denomScale W n ^ 2)

namespace LargeSieveConvolutionData

variable {W d C M Econv : ℕ → ℝ}

/-- The per-character energy estimate attached to the certificate. -/
theorem twistEnergyComparison (K : LargeSieveConvolutionData W d C M Econv) (n : ℕ) :
    @TwistEnergyComparison (K.cell.Den n) (K.cell.denFintype n)
      (K.q n) (fun i => ⟨K.q_ne_zero n i⟩) (K.P n) (K.s n) (Econv n) (d n) := by
  intro i χ hχ
  exact K.characterEnergy n i χ hχ

/-- **The scalar convolution-energy comparison, proved.**  The spectral identity
turns `A²` into the stage maximum, and the per-character estimate bounds every
cell's Mellin residue energy by `Econv / d`. -/
theorem convolutionComparison (K : LargeSieveConvolutionData W d C M Econv)
    (n : ℕ) :
    ConvolutionEnergyComparison (K.A n) (Econv n) (d n) := by
  letI := K.cell.denFintype n
  letI := K.cell.denNonempty n
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  refine convolutionEnergyComparison_of_twistEnergyBound (K.q n) (K.P n) (K.s n)
    (K.spectralIdentity n) (K.d_pos n) (K.Econv_nonneg n) ?_
  intro i χ hχ
  exact K.characterEnergy n i χ hχ

/-- The certificate's `energy_le`, now a theorem rather than a field. -/
theorem energy_le (K : LargeSieveConvolutionData W d C M Econv) (n : ℕ) :
    K.A n ^ 2 ≤ Econv n / d n :=
  K.convolutionComparison n

/-- The per-character Plancherel bound attached to the certificate. -/
theorem characterBound (K : LargeSieveConvolutionData W d C M Econv) (n : ℕ) :
    @MellinCharacterEnergyBound (K.cell.Den n) (K.q n)
      (K.P n) (K.s n) (fun _ => K.A n) := by
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  intro i χ hχ
  exact norm_productDirichletPolynomial_le_of_twist (K.P n i) (K.s n i) χ
    (K.spectral n i χ hχ)

/-- **The per-cell Mellin convolution-energy budget, proved.** -/
theorem energyBudget (K : LargeSieveConvolutionData W d C M Econv) (n : ℕ) :
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

/-- The certificate's `perCell_ge_one`, from the rational-cell construction. -/
theorem perCell_ge_one (K : LargeSieveConvolutionData W d C M Econv) (n : ℕ) :
    1 ≤ K.cell.perCell n :=
  K.cell.perCell_ge_one n

/-- **The literal `LargeSieveSpectralData`.**  The scalar comparison field is
supplied by `convolutionComparison` above, so this no longer assumes it. -/
noncomputable def toSpectralData (K : LargeSieveConvolutionData W d C M Econv) :
    LargeSieveSpectralData W d C M Econv where
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
  convolutionComparison := K.convolutionComparison
  numeratorSupport_le := K.numeratorSupport_le

/-- **The literal `LargeSieveCertificateData`.** -/
noncomputable abbrev toCertificateData (K : LargeSieveConvolutionData W d C M Econv) :
    LargeSieveCertificateData W d C M Econv :=
  K.toSpectralData.toCertificateData

/-- The constructed certificate has the same second moment as the residue energy
of the cell family, definitionally. -/
theorem toCertificateData_secondMoment (K : LargeSieveConvolutionData W d C M Econv)
    (n : ℕ) :
    K.toCertificateData.toLargeSieveCertificate.secondMoment n =
      letI := K.cell.denFintype n
      letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
      residueEnergy (K.q n) (K.P n) (fun i m => ((m : ℂ) ^ (K.s n i))⁻¹) :=
  K.toSpectralData.toCertificateData_secondMoment n

/-- **The L18.4 large-sieve bound from the convolution certificate.** -/
theorem large_sieve (K : LargeSieveConvolutionData W d C M Econv) (n : ℕ) :
    K.toCertificateData.toLargeSieveCertificate.secondMoment n ≤
      C n * (M n * denomScale W n ^ 2) * (Econv n / d n) :=
  K.toSpectralData.large_sieve n

end LargeSieveConvolutionData

/-! ## 6. Replacement of the `L18_4Inputs.large_sieve` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **`large_sieve` from the convolution certificate.** -/
theorem large_sieve_of_convolutionData
    (K : LargeSieveConvolutionData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    ∀ n, I.S2 n ≤ I.C n * (I.M n * denomScale I.W n ^ 2) * (I.Econv n / I.d n) :=
  I.large_sieve_of_spectralData K.toSpectralData hS2

/-- **Literal replacement of the `large_sieve` proof field.** -/
noncomputable def replaceLargeSieveConvolutionData
    (K : LargeSieveConvolutionData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) : L18_4Inputs :=
  I.replaceLargeSieveSpectralData K.toSpectralData hS2

/-- The replacement does not change the rational-good deficit. -/
@[simp] theorem replaceLargeSieveConvolutionData_loss
    (K : LargeSieveConvolutionData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    (I.replaceLargeSieveConvolutionData K hS2).loss = I.loss := by
  unfold replaceLargeSieveConvolutionData
  exact I.replaceLargeSieveSpectralData_loss K.toSpectralData hS2

/-- The replaced input still yields the L18.4 `D^{-B}` deficit. -/
theorem replaceLargeSieveConvolutionData_subexpLoss
    (K : LargeSieveConvolutionData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n =
      K.toCertificateData.toLargeSieveCertificate.secondMoment n) :
    SubexpLoss (I.replaceLargeSieveConvolutionData K hS2).loss := by
  rw [I.replaceLargeSieveConvolutionData_loss K hS2]
  exact I.subexpLoss

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms card_nonprincipal_le_totient
#print axioms characterEnergyComparison_of_twistEnergyComparison
#print axioms spectralEnergy_le_totient_mul_of_characterEnergyBound
#print axioms mellinResidueEnergy_le_of_characterEnergyBound
#print axioms convolutionEnergyComparison_of_characterEnergyBound
#print axioms convolutionEnergyComparison_of_twistEnergyBound
#print axioms convolutionEnergyComparison_iff_stageSpectralEnergy_le
#print axioms LargeSieveConvolutionData.twistEnergyComparison
#print axioms LargeSieveConvolutionData.convolutionComparison
#print axioms LargeSieveConvolutionData.energy_le
#print axioms LargeSieveConvolutionData.characterBound
#print axioms LargeSieveConvolutionData.energyBudget
#print axioms LargeSieveConvolutionData.toSpectralData
#print axioms LargeSieveConvolutionData.toCertificateData_secondMoment
#print axioms LargeSieveConvolutionData.large_sieve
#print axioms L18_4Inputs.large_sieve_of_convolutionData
#print axioms L18_4Inputs.replaceLargeSieveConvolutionData
#print axioms L18_4Inputs.replaceLargeSieveConvolutionData_loss
#print axioms L18_4Inputs.replaceLargeSieveConvolutionData_subexpLoss

end Cogentic.RandomizedL18_4
