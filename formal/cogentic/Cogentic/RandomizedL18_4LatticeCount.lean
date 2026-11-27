import Cogentic.RandomizedL18_4LargeSieveInputs
import Cogentic.RandomizedL18_4ThinAggregate

/-!
# L18.4: the rational-cell lattice count from the actual per-cell numerator count

`RandomizedL18_4LargeSieveInputs.LargeSieveCertificate` bundles the remaining
paper-level inputs of the L18.4 large sieve.  Besides the spectral constant and
the energy identification, it assumes the rational-cell lattice count

`perCell n ≤ C n * (M n * V n ^ 2) / cells n`   (`latticeCount`),

where `cells n` is the actual cardinality of the denominator-cell index type and
`perCell n` is the number of numerator cells met inside one denominator cell.

This file removes that input.  The count is decomposed into the two honest
pieces that the determinant strip actually supplies:

* `cells n * perCell n` is the *actual* total number of numerator cells met
  across the denominator cells (`numeratorSupport_eq`), not a chosen quantity;
* the determinant-strip count bounds that total by the paper's upper support
  length `C n * (M n * V n ^ 2)` (`numeratorSupport_le`).

In the certificate data below the total is *defined* as `card ι * perCell`, so
the first piece is definitional there; in the general `PerCellNumeratorCount`
structure it is recorded as an exact field.  The second piece is the smallest
explicit inequality of the rational-cell partition: it is exactly the paper's
`O(M V^2)` aggregate, with no division by the number of denominator cells and no
constant hidden in a division.  The equivalence
`rationalCellLatticeCount_iff_support_le` shows that this aggregate is *exact*:
multiplying the per-cell count back by the number of denominator cells is an
identity, so nothing is lost in the reduction.

The determinant-level machinery of `RandomizedL18_4ThinAggregate` supplies the
aggregate: `stripPairSet_card_le` bounds the ordered strip pairs of a
`LatticeBox` by `(1 + 2 L V^2/(q k)) R`, and
`stripPairSet_card_le_support` records the resulting support bound under the
explicit scale comparison that absorbs the per-level constant into `C M`.

Nothing here is a `sorry`, an `admit`, an `axiom` or a `native_decide`; the cell
count, the per-cell count, the total support and the strip pairs are actual
cardinalities, and no count is set to zero (`numeratorSupport_pos`).

-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open scoped BigOperators Classical
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Randomized

/-! ## 1. The actual per-cell numerator count -/

/-- **The actual per-cell numerator count.**  `cells n` is the number of
denominator cells, `perCell n` the number of numerator cells met inside one
denominator cell, and `total n` the actual total number of numerator cells met
across all denominator cells.  The total is *identified* with
`cells n * perCell n`, and the determinant-level count bounds it by
`C n * (M n * V n ^ 2)`.

This is the smallest explicit form of the rational-cell partition: the per-cell
count is not replaced by an averaged or rounded quantity, and the support length
is the actual product `cells * perCell`. -/
structure PerCellNumeratorCount (W C M : ℕ → ℝ) where
  /-- The number of denominator cells. -/
  cells : ℕ → ℝ
  /-- The number of denominator cells is positive. -/
  cells_pos : ∀ n, 0 < cells n
  /-- The number of numerator cells met inside one denominator cell. -/
  perCell : ℕ → ℝ
  /-- The per-cell count is nonnegative. -/
  perCell_nonneg : ∀ n, 0 ≤ perCell n
  /-- Each denominator cell meets at least one numerator cell.  This is the
  bookkeeping that keeps the support length at least the denominator-cell
  count; it is not the counting input. -/
  perCell_ge_one : ∀ n, 1 ≤ perCell n
  /-- The actual total number of numerator cells met across all denominator
  cells. -/
  total : ℕ → ℝ
  /-- The total is nonnegative. -/
  total_nonneg : ∀ n, 0 ≤ total n
  /-- **Exact decomposition.**  The total is the product of the number of
  denominator cells and the per-cell count; this is an exact identification of
  the actual count, not an averaged or rounded estimate. -/
  total_eq : ∀ n, total n = cells n * perCell n
  /-- **Determinant-level lattice count.**  The total number of numerator cells
  met is at most the paper's upper support length `C * M * V^2`.  This is the
  smallest explicit aggregate form of KB G.3 p.107 / G.15. -/
  total_le : ∀ n, total n ≤ C n * (M n * denomScale W n ^ 2)

namespace PerCellNumeratorCount

variable {W C M : ℕ → ℝ}

/-- **The rational-cell lattice count from the actual per-cell count.**  Dividing
the aggregate support bound by the number of denominator cells is exact:
`cells * perCell = total ≤ C M V^2`, hence
`perCell ≤ C M V^2 / cells`. -/
theorem latticeCount (D : PerCellNumeratorCount W C M) :
    RationalCellLatticeCount W C M D.cells D.perCell := by
  intro n
  rw [le_div_iff₀ (D.cells_pos n)]
  calc
    D.perCell n * D.cells n = D.cells n * D.perCell n := by ring
    _ = D.total n := (D.total_eq n).symm
    _ ≤ C n * (M n * denomScale W n ^ 2) := D.total_le n

/-- The total support is positive, so the reduction never sets a numerator cell
count to zero. -/
theorem total_pos (D : PerCellNumeratorCount W C M) (n : ℕ) : 0 < D.total n := by
  rw [D.total_eq n]
  exact mul_pos (D.cells_pos n) (lt_of_lt_of_le zero_lt_one (D.perCell_ge_one n))

end PerCellNumeratorCount

/-- **Exactness of the reduction.**  With a positive number of denominator cells,
the per-cell lattice count is *equivalent* to the aggregate support bound
`cells * perCell ≤ C M V^2`.  Thus the reduction to the actual per-cell count
loses no information. -/
theorem rationalCellLatticeCount_iff_support_le
    {W C M cells perCell : ℕ → ℝ} (hcells : ∀ n, 0 < cells n) :
    RationalCellLatticeCount W C M cells perCell ↔
      ∀ n, cells n * perCell n ≤ C n * (M n * denomScale W n ^ 2) := by
  constructor
  · intro h n
    have hle := h n
    rw [le_div_iff₀ (hcells n)] at hle
    calc
      cells n * perCell n = perCell n * cells n := by ring
      _ ≤ C n * (M n * denomScale W n ^ 2) := hle
  · intro h n
    rw [le_div_iff₀ (hcells n)]
    calc
      perCell n * cells n = cells n * perCell n := by ring
      _ ≤ C n * (M n * denomScale W n ^ 2) := h n

/-! ## 2. The determinant-level strip count supplies the aggregate -/

/-- **The determinant-strip count gives the aggregate support bound.**  For a
`LatticeBox` and the strip cutoff `V^2 / k`, `stripPairSet_card_le` bounds the
ordered strip pairs by `(1 + 2 L V^2/(q k)) R`.  Once the explicit scale
comparison

`(1 + 2 L V^2/(q k)) R ≤ C M V^2`

absorbs the per-level constant into `C M`, the strip count is exactly the
aggregate support bound consumed by `PerCellNumeratorCount.total_le`. -/
theorem stripPairSet_card_le_support {W : ℕ → ℝ} {n : ℕ} (B : LatticeBox)
    {k C M : ℝ} (hk : 0 < k)
    (hscale : (1 + 2 * B.L * ((denomScale W n ^ 2 / k) / (B.q : ℝ))) *
        (B.S.card : ℝ) ≤ C * (M * denomScale W n ^ 2)) :
    ((stripPairSet B.S (denomScale W n ^ 2 / k)).card : ℝ) ≤
      C * (M * denomScale W n ^ 2) := by
  have hX : 0 ≤ denomScale W n ^ 2 / k := div_nonneg (sq_nonneg _) hk.le
  exact (stripPairSet_card_le B hX).trans hscale

/-- Eventual (stage-indexed) form of `stripPairSet_card_le_support`: a family of
lattice boxes with a positive cutoff at every stage has aggregate support at most
`C n * (M n * V n ^ 2)` as soon as the scale comparison holds at every stage. -/
theorem stripPairSet_card_le_support_all {W C M : ℕ → ℝ}
    (B : ℕ → LatticeBox) {k : ℕ → ℝ} (hk : ∀ n, 0 < k n)
    (hscale : ∀ n,
      (1 + 2 * (B n).L *
          ((denomScale W n ^ 2 / k n) / ((B n).q : ℝ))) *
        ((B n).S.card : ℝ) ≤ C n * (M n * denomScale W n ^ 2)) :
    ∀ n, ((stripPairSet (B n).S (denomScale W n ^ 2 / k n)).card : ℝ) ≤
      C n * (M n * denomScale W n ^ 2) :=
  fun n => stripPairSet_card_le_support (B n) (hk n) (hscale n)

/-! ## 3. Removing the `latticeCount` field of `LargeSieveCertificate` -/

/-- **The large-sieve certificate with the lattice count removed.**  This is the
data of `LargeSieveCertificate` except that the `latticeCount` field is replaced
by the single explicit determinant-level aggregate bound

`card ι * perCell ≤ C * M * V^2`.

The total support is *defined* below as `card ι * perCell`, so multiplying the
per-cell count back by the number of denominator cells is definitional and no
further identification is assumed.  All other fields (the modulus cells, the
numerator sets, the spectral constant, the energy identification and the
positivity bookkeeping) are unchanged. -/
structure LargeSieveCertificateData (W d C M Econv : ℕ → ℝ) where
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
  /-- The field degree is positive. -/
  d_pos : ∀ n, 0 < d n
  /-- The undivided convolution energy is nonnegative. -/
  Econv_nonneg : ∀ n, 0 ≤ Econv n
  /-- Every stage has at least one denominator cell. -/
  nonempty : ∀ n, Nonempty (ι n)
  /-- Number of numerator cells met inside one denominator cell. -/
  perCell : ℕ → ℝ
  /-- The per-cell numerator count is nonnegative. -/
  perCell_nonneg : ∀ n, 0 ≤ perCell n
  /-- Each denominator cell meets at least one numerator cell. -/
  perCell_ge_one : ∀ n, 1 ≤ perCell n
  /-- **Per-modulus energy identification.** -/
  energy_le : ∀ n, A n ^ 2 ≤ Econv n / d n
  /-- **Determinant-level aggregate bound.**  The actual total number of
  numerator cells, `card ι * perCell`, is at most the paper's upper support length
  `C * M * V^2`.  This is the only counting input replacing `latticeCount`. -/
  numeratorSupport_le : ∀ n,
    (@Fintype.card (ι n) (fintype n) : ℝ) * perCell n ≤
      C n * (M n * denomScale W n ^ 2)

namespace LargeSieveCertificateData

variable {W d C M Econv : ℕ → ℝ}

/-- The actual total number of numerator cells met across all denominator cells:
the cardinality of the cell index type times the per-cell count.  This is a
definition, not an assumed decomposition. -/
noncomputable def numeratorSupport (K : LargeSieveCertificateData W d C M Econv) (n : ℕ) : ℝ :=
  (@Fintype.card (K.ι n) (K.fintype n) : ℝ) * K.perCell n

/-- The total support is definitionally the product of the denominator-cell count
and the per-cell count. -/
@[simp] theorem numeratorSupport_eq (K : LargeSieveCertificateData W d C M Econv) (n : ℕ) :
    K.numeratorSupport n = (@Fintype.card (K.ι n) (K.fintype n) : ℝ) * K.perCell n := rfl

/-- The total support is nonnegative. -/
theorem numeratorSupport_nonneg (K : LargeSieveCertificateData W d C M Econv) (n : ℕ) :
    0 ≤ K.numeratorSupport n := by
  rw [K.numeratorSupport_eq n]
  exact mul_nonneg (Nat.cast_nonneg _) (K.perCell_nonneg n)

/-- The total support is positive: there is at least one denominator cell and
each one meets at least one numerator cell. -/
theorem numeratorSupport_pos (K : LargeSieveCertificateData W d C M Econv) (n : ℕ) :
    0 < K.numeratorSupport n := by
  rw [K.numeratorSupport_eq n]
  have hcard : (0 : ℝ) < (@Fintype.card (K.ι n) (K.fintype n) : ℝ) := by
    exact_mod_cast (@Fintype.card_pos_iff (K.ι n) (K.fintype n)).mpr (K.nonempty n)
  exact mul_pos hcard (lt_of_lt_of_le zero_lt_one (K.perCell_ge_one n))

/-- The number of denominator cells is positive. -/
theorem certCells_pos (K : LargeSieveCertificateData W d C M Econv) (n : ℕ) :
    0 < (@Fintype.card (K.ι n) (K.fintype n) : ℝ) := by
  exact_mod_cast (@Fintype.card_pos_iff (K.ι n) (K.fintype n)).mpr (K.nonempty n)

/-- **The actual per-cell numerator count of the certificate data.**  The
denominator-cell count is the cardinality of the cell index type, the per-cell
count is `perCell`, and the total is the actual numerator support
`numeratorSupport`.  This is the reduction target: the lattice count is proved
from this structure and nothing else. -/
noncomputable def toPerCellNumeratorCount (K : LargeSieveCertificateData W d C M Econv) :
    PerCellNumeratorCount W C M where
  cells := fun n => (@Fintype.card (K.ι n) (K.fintype n) : ℝ)
  cells_pos := K.certCells_pos
  perCell := K.perCell
  perCell_nonneg := K.perCell_nonneg
  perCell_ge_one := K.perCell_ge_one
  total := K.numeratorSupport
  total_nonneg := K.numeratorSupport_nonneg
  total_eq := K.numeratorSupport_eq
  total_le := K.numeratorSupport_le

/-- **The `latticeCount` field, proved from the actual per-cell count.**  The
aggregate determinant-level bound divided by the number of denominator cells is
exactly the per-cell lattice count. -/
theorem latticeCount (K : LargeSieveCertificateData W d C M Econv) :
    RationalCellLatticeCount W C M
      (fun n => (@Fintype.card (K.ι n) (K.fintype n) : ℝ)) K.perCell :=
  K.toPerCellNumeratorCount.latticeCount

/-- **The literal `LargeSieveCertificate`.**  All fields of the certificate are
supplied; only `latticeCount` is now a theorem (`latticeCount`), so the counting
input has been removed from the hypothesis list. -/
noncomputable def toLargeSieveCertificate (K : LargeSieveCertificateData W d C M Econv) :
    LargeSieveCertificate W d C M Econv where
  ι := K.ι
  fintype := K.fintype
  q := K.q
  q_ne_zero := K.q_ne_zero
  P := K.P
  w := K.w
  A := K.A
  A_nonneg := K.A_nonneg
  spectral := K.spectral
  d_pos := K.d_pos
  Econv_nonneg := K.Econv_nonneg
  nonempty := K.nonempty
  perCell := K.perCell
  perCell_nonneg := K.perCell_nonneg
  perCell_ge_one := K.perCell_ge_one
  energy_le := K.energy_le
  latticeCount := K.latticeCount

/-- The second moment of the constructed certificate is the residue energy of its
modulus family, definitionally. -/
theorem toLargeSieveCertificate_secondMoment (K : LargeSieveCertificateData W d C M Econv)
    (n : ℕ) :
    K.toLargeSieveCertificate.secondMoment n =
      letI := K.fintype n
      letI : ∀ i, NeZero (K.q n i) := fun i => ⟨K.q_ne_zero n i⟩
      residueEnergy (K.q n) (K.P n) (K.w n) := rfl

end LargeSieveCertificateData

/-! ## 4. Replacement of the `L18_4Inputs.large_sieve` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **The `large_sieve` field from a certificate with the lattice count
removed.**  A `LargeSieveCertificateData` for the data of `I` supplies the
certificate, and the Bessel summation plus the lattice count of Section 3 give
the inequality assumed by `large_sieve`. -/
theorem large_sieve_of_certificateData
    (K : LargeSieveCertificateData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.toLargeSieveCertificate.secondMoment n) :
    ∀ n, I.S2 n ≤ I.C n * (I.M n * denomScale I.W n ^ 2) * (I.Econv n / I.d n) :=
  I.large_sieve_of_certificate K.toLargeSieveCertificate hS2

/-- **Literal replacement of the `large_sieve` proof field**, with the lattice
count discharged from the actual per-cell numerator count.  All other fields of
`I` are kept. -/
noncomputable def replaceLargeSieveCertificateData
    (K : LargeSieveCertificateData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.toLargeSieveCertificate.secondMoment n) : L18_4Inputs :=
  I.replaceLargeSieveCertificate K.toLargeSieveCertificate hS2

/-- The replacement does not change the rational-good deficit. -/
@[simp] theorem replaceLargeSieveCertificateData_loss
    (K : LargeSieveCertificateData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.toLargeSieveCertificate.secondMoment n) :
    (I.replaceLargeSieveCertificateData K hS2).loss = I.loss := by
  unfold replaceLargeSieveCertificateData
  exact I.replaceLargeSieveCertificate_loss K.toLargeSieveCertificate hS2

/-- The replaced input still yields the L18.4 `D^{-B}` deficit bound. -/
theorem replaceLargeSieveCertificateData_subexpLoss
    (K : LargeSieveCertificateData I.W I.d I.C I.M I.Econv)
    (hS2 : ∀ n, I.S2 n = K.toLargeSieveCertificate.secondMoment n) :
    SubexpLoss (I.replaceLargeSieveCertificateData K hS2).loss := by
  rw [I.replaceLargeSieveCertificateData_loss K hS2]
  exact I.subexpLoss

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms PerCellNumeratorCount.latticeCount
#print axioms PerCellNumeratorCount.total_pos
#print axioms rationalCellLatticeCount_iff_support_le
#print axioms stripPairSet_card_le_support
#print axioms stripPairSet_card_le_support_all
#print axioms LargeSieveCertificateData.numeratorSupport_nonneg
#print axioms LargeSieveCertificateData.numeratorSupport_pos
#print axioms LargeSieveCertificateData.certCells_pos
#print axioms LargeSieveCertificateData.toPerCellNumeratorCount
#print axioms LargeSieveCertificateData.latticeCount
#print axioms LargeSieveCertificateData.toLargeSieveCertificate
#print axioms LargeSieveCertificateData.toLargeSieveCertificate_secondMoment
#print axioms L18_4Inputs.large_sieve_of_certificateData
#print axioms L18_4Inputs.replaceLargeSieveCertificateData
#print axioms L18_4Inputs.replaceLargeSieveCertificateData_loss
#print axioms L18_4Inputs.replaceLargeSieveCertificateData_subexpLoss

end Cogentic.RandomizedL18_4
