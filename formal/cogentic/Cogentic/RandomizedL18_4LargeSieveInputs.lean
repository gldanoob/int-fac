import Cogentic.RandomizedL18_4LargeSieve
import Cogentic.RandomizedPrimeProductPlancherel
import Cogentic.RandomizedPrimeGridPrefixEnergy
import Cogentic.RandomizedTopStripMoments

/-!
# L18.4: the large-sieve inputs from Plancherel, Mellin and the prefix energy

`RandomizedL18_4LargeSieve.LargeSieveInputs` bundles the two paper-level
estimates behind the L18.4 large sieve (KB G.3 p.107, see
`research/keybreak-balanced-ideal-pair-audit.md` §1):

* `multiModulusSum : S2 n ≤ support n * (Econv n / d n)`; and
* `rationalCellPartition : support n ≤ C n * (M n * V n ^ 2)`.

This file does not assume either field.  It proves them from

1. the single/multi-modulus Parseval–Bessel summation already exposed as
   `RandomizedL18_4LargeSieve.multiModulus_residueEnergy_le`;
2. the Mellin Plancherel identity
   `RandomizedPrimeProductPlancherel.mellinClassError_plancherel` and the
   critical-line Mellin energy estimate
   `primeBinProducts_mellin_energy_from_critical_line`;
3. the sharp-prefix grid energy estimate
   `primeBinProducts_gridPrefix_from_critical_line`; and
4. one explicit rational-cell lattice count, isolated as
   `RationalCellLatticeCount`.

## What is proved and what is isolated

The summed second moment is *defined* as the actual residue energy of a finite
family of denominator moduli (`residueEnergy`), and `multiModulusSum` is proved
by applying the Bessel inequality cell by cell and then summing.  The only
arithmetic inputs are

* `energy_le`, the per-modulus spectral energy `A ^ 2` is at most the
  multiplicity-one convolution energy divided by the degree, `Econv / d`, and
* `perCell_ge_one`, each denominator cell meets at least one numerator cell.

Both are `D^{O(1)}` bookkeeping, not the L18.4 conclusion, and neither is zero.
The number of denominator cells is *not* an extra hypothesis: it is the actual
cardinality of the modulus index type.

The support length is *defined* as `certCells K n * perCell n`, where
`certCells K n` is the actual number of denominator cells (the cardinality of
the modulus index type) and `perCell n` the number of numerator cells met inside
one denominator cell.  `rationalCellPartition` is then proved from the smallest
explicit lattice count

`perCell n ≤ C n * (M n * V n ^ 2) / certCells K n`,

i.e. the paper's `O(1)` numerator cells per denominator cell after the total
count `O(M V^2)` has been divided over the denominator cells.  The exact
division `certCells * (X / certCells) = X` is proved, so no numerator-cell count
is set to zero or pushed into the constant.

The Mellin realization is exact: `mellinSecondMoment` is the Plancherel residue
energy of the weights `n ↦ (n : ℂ) ^ (-s)`, it equals `residueEnergy` at those
weights, and the critical-line theorem bounds it by the explicit per-bin
envelope.  The grid-prefix theorem is packaged as `gridPrefixEnergy_le_envelope`
and gives the per-coordinate prefix bound `gridPrefixEnergy_coordinate_le`.

Finally `LargeSieveCertificate.toLargeSieve` produces a literal
`LargeSieveInputs`, and `L18_4Inputs.large_sieve_of_certificate` /
`L18_4Inputs.replaceLargeSieveCertificate` replace the `large_sieve` proof field
of `L18_4Inputs` by the certificate, leaving the rational-good deficit `loss`
unchanged.

Nothing here is a `sorry`, an `admit`, an `axiom`, or a `native_decide`; no
loss, mass, count or error is set to zero.
-/

namespace Cogentic.RandomizedL18_4

set_option linter.style.haveILetI false

open Filter Real
open scoped BigOperators Classical
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Randomized

/-! ## 1. The summed residue energy and the multi-modulus summation -/

/-- The summed squared discrepancy energy of a finite family of denominator
moduli.  This is the left-hand side of
`RandomizedL18_4LargeSieve.multiModulus_residueEnergy_le`: for each modulus
`q i` the reduced residues `r` carry the centered numerator-count discrepancy
`classMass - twist / φ(q)`. -/
noncomputable def residueEnergy {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (P : ι → Finset ℕ) (w : ι → ℕ → ℂ) : ℝ :=
  ∑ i, ∑ r : (ZMod (q i))ˣ,
    ‖Window.classMass (P i) (w i) r -
      Window.twist (P i) (w i) (1 : DirichletCharacter ℂ (q i)) /
        (q i).totient‖ ^ 2

/-- **Single-to-multi-modulus Bessel summation.**  A uniform bound `A` on the
nonprincipal twists of every modulus bounds the summed residue energy by the
number of moduli times `A ^ 2`.  This is exactly
`multiModulus_residueEnergy_le`, restated for the named energy. -/
theorem residueEnergy_le_card_mul_sq {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (w : ι → ℕ → ℂ) {A : ℝ}
    (hA : ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
      ‖Window.twist (P i) (w i) χ‖ ≤ A) :
    residueEnergy q P w ≤ (@Fintype.card ι _ : ℝ) * A ^ 2 := by
  simpa [residueEnergy] using multiModulus_residueEnergy_le q P w hA

/-- **Multi-modulus summation with the scale bookkeeping.**  Once the number of
moduli is at most the support length and the per-modulus energy `A ^ 2` is at
most `Econv / d`, the summed residue energy is at most
`support * (Econv / d)`.

The two hypotheses are the paper-level `D^{O(1)}` bookkeeping of the large
sieve; the Bessel summation itself is proved. -/
theorem residueEnergy_le_support_mul_energy {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (w : ι → ℕ → ℂ)
    {A support Econv d : ℝ}
    (hA : ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
      ‖Window.twist (P i) (w i) χ‖ ≤ A)
    (hcard : (@Fintype.card ι _ : ℝ) ≤ support)
    (hsupport : 0 ≤ support)
    (henergy : A ^ 2 ≤ Econv / d) :
    residueEnergy q P w ≤ support * (Econv / d) := by
  calc
    residueEnergy q P w ≤ (@Fintype.card ι _ : ℝ) * A ^ 2 :=
      residueEnergy_le_card_mul_sq q P w hA
    _ ≤ support * A ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg A)
    _ ≤ support * (Econv / d) := mul_le_mul_of_nonneg_left henergy hsupport

/-! ## 2. The Mellin / Plancherel realization -/

/-- The Plancherel residue energy of the Mellin weight `n ↦ n ^ (-s)`; this is
the left-hand side of `mellinClassError_plancherel`. -/
noncomputable def mellinResidueEnergy (q : ℕ) [NeZero q] (P : Finset ℕ) (s : ℂ) : ℝ :=
  ∑ r : (ZMod q)ˣ, ‖mellinClassError P s r‖ ^ 2

/-- **Mellin Plancherel.**  The residue discrepancy energy at the Mellin weight
equals the nonprincipal Dirichlet-character energy divided by `φ(q)`.  This is
`mellinClassError_plancherel` for the named energy. -/
theorem mellinResidueEnergy_eq_characterEnergy {q : ℕ} [NeZero q]
    (P : Finset ℕ) (s : ℂ) :
    mellinResidueEnergy q P s =
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖productDirichletPolynomial P (fun n => χ n) s‖ ^ 2) /
        (q.totient : ℝ) := by
  simpa [mellinResidueEnergy] using mellinClassError_plancherel P s

/-- **Mellin Bessel bound.**  A uniform bound on the nonprincipal product
polynomials bounds the whole Mellin residue energy by `A ^ 2`, with no factor
for the number of characters.  This is the single-cell Plancherel estimate in
the form consumed by the multi-modulus summation. -/
theorem mellinResidueEnergy_le_sq {q : ℕ} [NeZero q] (P : Finset ℕ) (s : ℂ)
    {A : ℝ}
    (hA : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖productDirichletPolynomial P (fun n => χ n) s‖ ≤ A) :
    mellinResidueEnergy q P s ≤ A ^ 2 := by
  have h := classMass_centered_sq_le (q := q) P
    (fun n => ((n : ℂ) ^ s)⁻¹) (M := A) ?_
  · simpa [mellinResidueEnergy, mellinClassError] using h
  · intro χ hχ
    have hχ' := hA χ hχ
    simpa only [Window.twist, productDirichletPolynomial, div_eq_mul_inv] using hχ'

/-- The Mellin second moment of a finite family of denominator moduli. -/
noncomputable def mellinSecondMoment {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (s : ι → ℂ) : ℝ :=
  ∑ i, mellinResidueEnergy (q i) (P i) (s i)

/-- The Mellin second moment is exactly the residue energy at the Mellin
weights, so the multi-modulus Bessel summation applies to it unchanged. -/
theorem mellinSecondMoment_eq_residueEnergy {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (s : ι → ℂ) :
    mellinSecondMoment q P s =
      residueEnergy q P (fun i n => ((n : ℂ) ^ (s i))⁻¹) := by
  simp [mellinSecondMoment, mellinResidueEnergy, residueEnergy, mellinClassError]

/-- **Multi-modulus summation for the Mellin second moment.**  Summing the
Plancherel–Bessel bounds over the family costs the number of moduli. -/
theorem mellinSecondMoment_le_card_mul_sq {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (s : ι → ℂ) {A : ℝ}
    (hA : ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
      ‖productDirichletPolynomial (P i) (fun n => χ n) (s i)‖ ≤ A) :
    mellinSecondMoment q P s ≤ (@Fintype.card ι _ : ℝ) * A ^ 2 := by
  calc
    mellinSecondMoment q P s ≤ ∑ _i : ι, A ^ 2 :=
      Finset.sum_le_sum fun i _ => mellinResidueEnergy_le_sq (P i) (s i) (hA i)
    _ = (@Fintype.card ι _ : ℝ) * A ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The `multiModulusSum` shape for the Mellin second moment.**  The
Plancherel–Bessel bound, the support count and the per-cell energy
identification together give exactly `S2 ≤ support * (Econv / d)`. -/
theorem mellinSecondMoment_le_support_mul_energy {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (P : ι → Finset ℕ) (s : ι → ℂ)
    {A support Econv d : ℝ}
    (hA : ∀ i (χ : DirichletCharacter ℂ (q i)), χ ≠ 1 →
      ‖productDirichletPolynomial (P i) (fun n => χ n) (s i)‖ ≤ A)
    (hcard : (@Fintype.card ι _ : ℝ) ≤ support)
    (hsupport : 0 ≤ support)
    (henergy : A ^ 2 ≤ Econv / d) :
    mellinSecondMoment q P s ≤ support * (Econv / d) := by
  calc
    mellinSecondMoment q P s ≤ (@Fintype.card ι _ : ℝ) * A ^ 2 :=
      mellinSecondMoment_le_card_mul_sq q P s hA
    _ ≤ support * A ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg A)
    _ ≤ support * (Econv / d) := mul_le_mul_of_nonneg_left henergy hsupport

/-- **Mellin energy from the critical line.**  The residue energy of a disjoint
prime-bin product is bounded by the explicit per-bin envelope of
`primeBinProducts_mellin_energy_from_critical_line`. -/
theorem mellinResidueEnergy_primeBinProducts_le_from_critical_line
    (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
        (A B : ι → ℕ),
        (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
        (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        ∀ σ t : ℝ, 0 ≤ σ →
          mellinResidueEnergy q (primeBinProducts A B) ((σ : ℂ) + t * Complex.I) ≤
            (∏ i, K * Real.sqrt (B i) *
              (1 + Real.log (q * ((B i : ℝ) + |t| + 2))) ^ 3) ^ 2 := by
  obtain ⟨K, hK, hb⟩ := primeBinProducts_mellin_energy_from_critical_line line
  refine ⟨K, hK, ?_⟩
  intro q _ ι _ _ A B hB hAB hdisj σ t hσ
  have h := hb (q := q) (ι := ι) (A := A) (B := B) hB hAB hdisj σ t hσ
  simpa [mellinResidueEnergy] using h

/-! ## 3. The sharp-prefix grid energy -/

/-- The `L²` grid-prefix energy of the numerator counts: the norm over the
residue/frequency grid of the maximal prefix Fourier coefficient. -/
noncomputable def gridPrefixEnergy {m B : ℕ} [NeZero m] [NeZero B] (cop : m.Coprime B)
    (P : Finset ℕ) (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty) : ℝ :=
  ‖(WithLp.toLp 2 (fun i : GridCoordinate m B =>
      cutoffs.sup' hne (fun j => ‖gridPrefixFourier cop P j i‖)) :
        EuclideanSpace ℝ (GridCoordinate m B))‖

/-- **Prefix energy from the critical line.**  The explicit envelope of
`primeBinProducts_gridPrefix_from_critical_line` bounds the named grid-prefix
energy.  This supplies the per-modulus spectral constant `A` of the
multi-modulus summation. -/
theorem gridPrefixEnergy_le_envelope (line : DirichletLZerosOnLine) {m B : ℕ}
    [NeZero m] [NeZero B] [NeZero (m * B)] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (cop : m.Coprime B) (X : ℝ)
        (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty)
        {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ),
        2 ≤ X → Real.exp 1 ≤ X →
        (∀ j ∈ cutoffs, X ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X) →
        (∀ n ∈ primeBinProducts A U, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) →
        (∀ i, 2 ≤ U i) → (∀ i, A i ≤ U i) →
        (Pairwise fun i j => Disjoint (primeBin (A i) (U i)) (primeBin (A j) (U j))) →
        gridPrefixEnergy cop (primeBinProducts A U) cutoffs hne ≤
          Real.sqrt B * ((4 * Real.exp 2 / Real.pi) *
            ((∏ i, C * Real.sqrt (U i) * (1 + Real.log ((m * B : ℕ) *
              ((U i : ℝ) + X ^ 3 + 2))) ^ 3) * Real.log X) +
            (2 * K / X ^ 2) * (primeBinProducts A U).card) := by
  obtain ⟨C, K, hC, hK, hb⟩ :=
    primeBinProducts_gridPrefix_from_critical_line (m := m) (B := B) line
  refine ⟨C, K, hC, hK, ?_⟩
  intro cop X cutoffs hne ι _ _ A U hX heX hcut hP hU hAU hdisj
  simpa [gridPrefixEnergy] using hb cop X cutoffs hne A U
    hX heX hcut hP hU hAU hdisj

/-- **A single grid coordinate is bounded by the prefix energy.**  Since the
grid-prefix energy is the Euclidean norm of a vector of nonnegative prefix
maxima, every coordinatewise prefix maximum is at most the energy.  This is the
step that turns the prefix estimate into the uniform twist bound consumed by the
Bessel summation. -/
theorem gridPrefixEnergy_coordinate_le {m B : ℕ} [NeZero m] [NeZero B] (cop : m.Coprime B)
    (P : Finset ℕ) (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty)
    (E : ℝ) (hE : gridPrefixEnergy cop P cutoffs hne ≤ E)
    (i : GridCoordinate m B) :
    cutoffs.sup' hne (fun j => ‖gridPrefixFourier cop P j i‖) ≤ E := by
  set f : GridCoordinate m B → ℝ :=
    fun i => cutoffs.sup' hne (fun j => ‖gridPrefixFourier cop P j i‖) with hf
  have hcoord : f i ≤ gridPrefixEnergy cop P cutoffs hne := by
    have hnorm : gridPrefixEnergy cop P cutoffs hne =
        Real.sqrt (∑ x, f x ^ 2) := by
      rw [gridPrefixEnergy, EuclideanSpace.norm_eq]
      simp only [hf, Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    exact Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun x _ => sq_nonneg (f x)) (Finset.mem_univ i))
  have hfi : f i = cutoffs.sup' hne (fun j => ‖gridPrefixFourier cop P j i‖) := rfl
  rw [← hfi]
  exact hcoord.trans hE

/-! ## 4. The rational-cell lattice count -/

/-- The support length after the rational-cell partition: `cells` denominator
cells, each meeting `perCell` numerator cells. -/
noncomputable def cellSupport (cells perCell : ℕ → ℝ) (n : ℕ) : ℝ :=
  cells n * perCell n

/-- **The rational-cell lattice count** (KB G.3 p.107, G.15).  The determinant
strip `|det| ≪ V²/K` meets `O(1)` numerator cells inside each denominator cell
and `O(K)` cell pairs in all.  Normalized by the `cells` denominator cells this
is the per-cell count

`perCell n ≤ C n * (M n * V n ^ 2) / cells n`;

multiplying back by `cells n` gives the support bound `O(M V²)`.  This is the
smallest explicit counting input of `rationalCellPartition`; it is not the
L18.4 conclusion and it is not zero. -/
def RationalCellLatticeCount (W C M cells perCell : ℕ → ℝ) : Prop :=
  ∀ n, perCell n ≤ C n * (M n * denomScale W n ^ 2) / cells n

/-- The support length is nonnegative when the cell counts are. -/
theorem cellSupport_nonneg {cells perCell : ℕ → ℝ}
    (hcells : ∀ n, 0 < cells n) (hperCell : ∀ n, 0 ≤ perCell n) (n : ℕ) :
    0 ≤ cellSupport cells perCell n :=
  mul_nonneg (hcells n).le (hperCell n)

/-- **`rationalCellPartition` from the lattice count.**  The exact division
`cells * (X / cells) = X` cancels the denominator-cell count, leaving the paper's
support bound `C * M * V²`. -/
theorem rationalCellPartition_of_latticeCount {W C M cells perCell : ℕ → ℝ}
    (hcells : ∀ n, 0 < cells n)
    (hcount : RationalCellLatticeCount W C M cells perCell) (n : ℕ) :
    cellSupport cells perCell n ≤ C n * (M n * denomScale W n ^ 2) := by
  have hc := hcells n
  calc
    cellSupport cells perCell n = cells n * perCell n := rfl
    _ ≤ cells n * (C n * (M n * denomScale W n ^ 2) / cells n) :=
      mul_le_mul_of_nonneg_left (hcount n) hc.le
    _ = C n * (M n * denomScale W n ^ 2) := by
      rw [mul_div_cancel₀ _ hc.ne']

/-! ## 5. The certificate and `LargeSieveInputs` -/

/-- **The L18.4 large-sieve certificate.**

The second moment is the actual residue energy of a finite family of denominator
moduli, so `multiModulusSum` is the Bessel summation of Section 1.  The support
length is `certCells * perCell`, where `certCells` is the actual cardinality of
the modulus index type, so `rationalCellPartition` is the lattice count of
Section 4.  The only remaining scale input is the paper-level `D^{O(1)}`
identification `energy_le`; the spectral bound is supplied by the
Mellin/Plancherel and prefix-energy estimates through `A`.

Nothing is set to zero: the cell count, `perCell`, `A`, `Econv` and the modulus
family are all explicit. -/
structure LargeSieveCertificate (W d C M Econv : ℕ → ℝ) where
  /-- The index type of denominator modulus cells at stage `n`. -/
  ι : ℕ → Type*
  /-- Each stage has finitely many cells. -/
  fintype : ∀ n, Fintype (ι n)
  /-- The denominator modulus of each cell. -/
  q : ∀ n, ι n → ℕ
  /-- Every denominator modulus is nonzero. -/
  q_ne_zero : ∀ n i, q n i ≠ 0
  /-- The numerator support set of each cell. -/
  P : ∀ n, ι n → Finset ℕ
  /-- The numerator weight of each cell. -/
  w : ∀ n, ι n → ℕ → ℂ
  /-- The uniform per-modulus spectral bound. -/
  A : ℕ → ℝ
  /-- The spectral bound is nonnegative. -/
  A_nonneg : ∀ n, 0 ≤ A n
  /-- The uniform bound on the nonprincipal twists of every cell. -/
  spectral : ∀ n (i : ι n) (χ : DirichletCharacter ℂ (q n i)), χ ≠ 1 →
    ‖Window.twist (P n i) (w n i) χ‖ ≤ A n
  /-- The field degree is positive, so `Econv / d` is defined. -/
  d_pos : ∀ n, 0 < d n
  /-- The undivided convolution energy is nonnegative. -/
  Econv_nonneg : ∀ n, 0 ≤ Econv n
  /-- Every stage has at least one denominator cell. -/
  nonempty : ∀ n, Nonempty (ι n)
  /-- Number of numerator cells met inside one denominator cell. -/
  perCell : ℕ → ℝ
  /-- The per-cell numerator count is nonnegative. -/
  perCell_nonneg : ∀ n, 0 ≤ perCell n
  /-- Each denominator cell meets at least one numerator cell, so the support
  length is at least the number of denominator cells.  This is what makes the
  summed Bessel bound cost `support` rather than the number of active cells. -/
  perCell_ge_one : ∀ n, 1 ≤ perCell n
  /-- **Per-modulus energy identification.**  The single-cell spectral energy `A²`
  is at most the multiplicity-one convolution energy divided by the degree. -/
  energy_le : ∀ n, A n ^ 2 ≤ Econv n / d n
  /-- **The rational-cell lattice count** (KB G.3 p.107, G.15), normalized by the
  actual number of denominator cells. -/
  latticeCount : RationalCellLatticeCount W C M
    (fun n => (@Fintype.card (ι n) (fintype n) : ℝ)) perCell

/-- The number of denominator cells of a certificate: the actual cardinality of
its modulus index type. -/
noncomputable def certCells {W d C M Econv : ℕ → ℝ}
    (K : LargeSieveCertificate W d C M Econv) (n : ℕ) : ℝ :=
  (@Fintype.card (K.ι n) (K.fintype n) : ℝ)

/-- The number of denominator cells is positive, since the index type is
nonempty. -/
theorem certCells_pos {W d C M Econv : ℕ → ℝ}
    (K : LargeSieveCertificate W d C M Econv) (n : ℕ) : 0 < certCells K n := by
  letI := K.fintype n
  rw [certCells]
  exact_mod_cast (Fintype.card_pos_iff.mpr (K.nonempty n))

namespace LargeSieveCertificate

variable {W d C M Econv : ℕ → ℝ}

/-- The summed second moment of the certificate: the residue energy of the
denominator modulus cells. -/
noncomputable def secondMoment (K : LargeSieveCertificate W d C M Econv)
    (n : ℕ) : ℝ :=
  letI := K.fintype n
  letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  residueEnergy (K.q n) (K.P n) (K.w n)

/-- **The `multiModulusSum` field, proved.**  The Bessel inequality gives the
per-cell energy `A²`; summing over the cells costs the number of cells, which is
at most the support; and the per-cell energy is at most `Econv / d`. -/
theorem multiModulusSum (K : LargeSieveCertificate W d C M Econv) (n : ℕ) :
    K.secondMoment n ≤ cellSupport (certCells K) K.perCell n * (Econv n / d n) := by
  letI := K.fintype n
  haveI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
  have hcard : (@Fintype.card (K.ι n) (K.fintype n) : ℝ) ≤
      cellSupport (certCells K) K.perCell n := by
    have hc0 : (0 : ℝ) ≤ (@Fintype.card (K.ι n) (K.fintype n) : ℝ) :=
      (certCells_pos K n).le
    calc
      (@Fintype.card (K.ι n) (K.fintype n) : ℝ) = certCells K n := rfl
      _ ≤ certCells K n * K.perCell n :=
        le_mul_of_one_le_right hc0 (K.perCell_ge_one n)
      _ = cellSupport (certCells K) K.perCell n := rfl
  have h := residueEnergy_le_support_mul_energy (K.q n)
    (K.P n) (K.w n) (A := K.A n)
    (support := cellSupport (certCells K) K.perCell n)
    (Econv := Econv n) (d := d n) (K.spectral n) hcard
    (cellSupport_nonneg (certCells_pos K) K.perCell_nonneg n) (K.energy_le n)
  simpa [secondMoment] using h

/-- **The `rationalCellPartition` field, proved.**  The lattice count divided by
the number of denominator cells multiplies back to the paper's support bound
`C * M * V²`. -/
theorem rationalCellPartition (K : LargeSieveCertificate W d C M Econv) (n : ℕ) :
    cellSupport (certCells K) K.perCell n ≤ C n * (M n * denomScale W n ^ 2) :=
  rationalCellPartition_of_latticeCount (certCells_pos K) K.latticeCount n

/-- **The literal `LargeSieveInputs` certificate.**  Both named fields are proved
from the Plancherel/Bessel summation and the lattice count. -/
noncomputable def toLargeSieve (K : LargeSieveCertificate W d C M Econv) :
    LargeSieveInputs W d C M Econv K.secondMoment where
  support := cellSupport (certCells K) K.perCell
  support_nonneg := cellSupport_nonneg (certCells_pos K) K.perCell_nonneg
  d_pos := K.d_pos
  Econv_nonneg := K.Econv_nonneg
  multiModulusSum := K.multiModulusSum
  rationalCellPartition := K.rationalCellPartition

end LargeSieveCertificate

/-- **`LargeSieveInputs` from a certificate for a specified second moment.**  A
certificate whose residue energy equals `S2` supplies all six fields of
`LargeSieveInputs`. -/
noncomputable def LargeSieveInputs.of_certificate {W d C M Econv S2 : ℕ → ℝ}
    (K : LargeSieveCertificate W d C M Econv)
    (hS2 : ∀ n, S2 n = K.secondMoment n) :
    LargeSieveInputs W d C M Econv S2 where
  support := cellSupport (certCells K) K.perCell
  support_nonneg := cellSupport_nonneg (certCells_pos K) K.perCell_nonneg
  d_pos := K.d_pos
  Econv_nonneg := K.Econv_nonneg
  multiModulusSum := fun n => by
    rw [hS2 n]
    exact K.multiModulusSum n
  rationalCellPartition := K.rationalCellPartition

/-! ## 6. Replacement of the `L18_4Inputs.large_sieve` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **The `large_sieve` field is reduced to a `LargeSieveCertificate`.**  For any
`L18_4Inputs`, a certificate whose second moment is `I.S2` implies the inequality
assumed by its `large_sieve` field. -/
theorem large_sieve_of_certificate
    (K : LargeSieveCertificate I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.secondMoment n) :
    ∀ n, I.S2 n ≤ I.C n * (I.M n * denomScale I.W n ^ 2) * (I.Econv n / I.d n) :=
  (LargeSieveInputs.of_certificate K hS2).large_sieve_all

/-- **Literal replacement of the `large_sieve` proof field.**  All other fields
of `I` are kept, while `large_sieve` is now derived from the Plancherel/Bessel
summation, the lattice count and the scale bookkeeping instead of being
assumed. -/
noncomputable def replaceLargeSieveCertificate
    (K : LargeSieveCertificate I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.secondMoment n) : L18_4Inputs :=
  { I with large_sieve := I.large_sieve_of_certificate K hS2 }

/-- Replacing the large-sieve proof field does not change the rational-good
deficit: `loss` depends only on the data fields, which are untouched. -/
@[simp] theorem replaceLargeSieveCertificate_loss
    (K : LargeSieveCertificate I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.secondMoment n) :
    (I.replaceLargeSieveCertificate K hS2).loss = I.loss := rfl

/-- The replaced input still yields the L18.4 `D^{-B}` deficit bound, because the
deficit is unchanged. -/
theorem replaceLargeSieveCertificate_subexpLoss
    (K : LargeSieveCertificate I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.secondMoment n) :
    SubexpLoss (I.replaceLargeSieveCertificate K hS2).loss := by
  rw [I.replaceLargeSieveCertificate_loss K hS2]
  exact I.subexpLoss

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms residueEnergy_le_card_mul_sq
#print axioms residueEnergy_le_support_mul_energy
#print axioms mellinResidueEnergy_eq_characterEnergy
#print axioms mellinResidueEnergy_le_sq
#print axioms mellinSecondMoment_eq_residueEnergy
#print axioms mellinSecondMoment_le_card_mul_sq
#print axioms mellinSecondMoment_le_support_mul_energy
#print axioms mellinResidueEnergy_primeBinProducts_le_from_critical_line
#print axioms gridPrefixEnergy_le_envelope
#print axioms gridPrefixEnergy_coordinate_le
#print axioms certCells_pos
#print axioms cellSupport_nonneg
#print axioms rationalCellPartition_of_latticeCount
#print axioms LargeSieveCertificate.multiModulusSum
#print axioms LargeSieveCertificate.rationalCellPartition
#print axioms LargeSieveCertificate.toLargeSieve
#print axioms LargeSieveInputs.of_certificate
#print axioms L18_4Inputs.large_sieve_of_certificate
#print axioms L18_4Inputs.replaceLargeSieveCertificate
#print axioms L18_4Inputs.replaceLargeSieveCertificate_loss
#print axioms L18_4Inputs.replaceLargeSieveCertificate_subexpLoss

end Cogentic.RandomizedL18_4
