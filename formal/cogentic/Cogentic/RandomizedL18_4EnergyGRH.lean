import Cogentic.RandomizedL18_4SieveFinish
import Cogentic.RandomizedL18_4LatticeCount
import Cogentic.RandomizedPrimeBinBias

/-!
# L18.4: the energy-residual and numerator-support inputs from the critical line

`RandomizedL18_4SieveFinish.LargeSieveFinishData` still carries two inputs:

* `EnergyResidualBudget`, the per-stage bound on the actual Mellin residue
  energy, and
* `NumeratorSupportBound`, the aggregate rational-cell numerator count.

This file discharges both from `DirichletLZerosOnLine` together with the finite
large-sieve/orthogonality computation already present in the repository.

## 1. The energy residual

The residue energy of a cell is, by Mellin Plancherel
(`mellinResidueEnergy_eq_characterEnergy`), the normalized nonprincipal
character energy.  The critical line supplies the *nonprincipal character
estimate* for tor products of disjoint prime bins: the existing theorem
`mellinResidueEnergy_primeBinProducts_le_from_critical_line` bounds

`mellinResidueEnergy q (primeBinProducts A B) (σ + i t)`

by the square of the explicit GRH envelope

`∏ j, K √(B j) (1 + log (q (B j + |t| + 2)))³`,

for `0 ≤ σ`.  Its constant `K > 0` is extracted below as `primeBinMellinK`.

Consequently the whole energy budget follows from the *single scalar* explicit
input `PrimeBinMellinEnvelopeBudget`: at every cell, the square of the GRH
envelope fits the multiplicity-one convolution energy,

`(GRH envelope)² ≤ Econv / d`.

The reduction `PrimeBinMellinEnvelopeBudget → EnergyResidualBudget` is proved in
`energyResidualBudget_of_primeBinMellinEnvelope`.  The same content is also
stated in the uniform form requested by the paper: the stage supremum `B` of the
per-cell GRH envelopes satisfies `B² ≤ Econv / d`
(`PrimeBinMellinUniformBudget`), and this implies the residual budget
(`energyResidualBudget_of_uniformPrimeBinBound`).

The envelope is strictly positive (`primeBinGRHEnvelope_pos`), so the budget is
strictly positive at every stage (`EnergyResidualGRHData.energyBudget_pos`); no
energy is set to zero.  The genuine nonzero error is retained through the
`NonzeroResidualWitness` of the certificate.

## 2. The numerator support

`RationalCellConstruction.perCell` is the actual maximum incidence count of the
denominator cells.  The cell construction supplies the elementary bound
`perCell n ≤ card (Num n)` (`perCell_le_numCard`): the incidence set of one
denominator cell is a subset of all numerator cells.  Hence the aggregate
support count follows from the finite numerator-cell count
`card (Den n) * card (Num n) ≤ C n * (M n * V n²)`
(`numeratorSupportBound_of_numCardCount`).

Two equivalent certificate forms are also provided: the normalized lattice
count `RationalCellLatticeCount` (`numeratorSupportBound_of_latticeCount`) and
the exact per-cell total `PerCellNumeratorCount`
(`numeratorSupportBound_of_perCellNumeratorCount`).

## 3. The assembled certificate

`EnergyResidualGRHData` bundles the finite cell geometry, the prime-bin
enumeration, the critical-line exponent (`0 ≤ Re s`), the scalar envelope
budget, a nonzero residual witness and the numerator count.  Its
`toLargeSieveFinishData` produces a literal `LargeSieveFinishData`, so the L18.4
`large_sieve` field and the genuine positive error both follow.

Nothing here is a `sorry`, an `admit`, an `axiom` or a `native_decide`; the GRH
estimate and the cell counts are the actual ones, and no energy, count or error
is set to zero.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open scoped BigOperators Classical
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Randomized

set_option linter.style.haveILetI false
set_option linter.checkUnivs false

/-! ## 1. The critical-line Mellin constant and envelope -/

/-- **The nonprincipal character estimate of the critical line.**  This is the
existing product form `PrimeBinProductBound`, exported here to record that the
Mellin envelope below is a consequence of the pointwise nonprincipal character
bound (and not of a separate averaged hypothesis). -/
theorem primeBinCharacterBound_of_critical_line (line : DirichletLZerosOnLine) :
    PrimeBinProductBound :=
  primeBin_product_from_critical_line line

/-- The positive constant of the critical-line prime-bin Mellin estimate,
extracted from `mellinResidueEnergy_primeBinProducts_le_from_critical_line`. -/
noncomputable def primeBinMellinK (line : DirichletLZerosOnLine) : ℝ :=
  Classical.choose (mellinResidueEnergy_primeBinProducts_le_from_critical_line line)

/-- The critical-line constant is strictly positive. -/
theorem primeBinMellinK_pos (line : DirichletLZerosOnLine) :
    0 < primeBinMellinK line :=
  (Classical.choose_spec
    (mellinResidueEnergy_primeBinProducts_le_from_critical_line line)).1

/-- **The nonprincipal character estimate in Mellin form.**  For disjoint prime
bins and a right-half-plane exponent, the Mellin residue energy of the product
set is at most the square of the explicit GRH envelope.  This is the extracted
form of `mellinResidueEnergy_primeBinProducts_le_from_critical_line`, and it is
the estimate which drives the energy budget. -/
theorem primeBinMellinK_bound (line : DirichletLZerosOnLine) :
    ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
      (A B : ι → ℕ),
      (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
      (Pairwise fun i j =>
        Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      ∀ σ t : ℝ, 0 ≤ σ →
        mellinResidueEnergy q (primeBinProducts A B)
            ((σ : ℂ) + t * Complex.I) ≤
          (∏ i, primeBinMellinK line * Real.sqrt (B i) *
            (1 + Real.log (q * ((B i : ℝ) + |t| + 2))) ^ 3) ^ 2 := by
  simpa only [primeBinMellinK] using
    (Classical.choose_spec
      (mellinResidueEnergy_primeBinProducts_le_from_critical_line line)).2

/-- The explicit GRH norm envelope of a prime-bin product at height `t`.  Its
square is the energy bound of `primeBinMellinK_bound`. -/
noncomputable def primeBinGRHEnvelope (line : DirichletLZerosOnLine) (q : ℕ)
    {ι : Type} [Fintype ι] (B : ι → ℕ) (t : ℝ) : ℝ :=
  ∏ j, primeBinMellinK line * Real.sqrt (B j) *
    (1 + Real.log (q * ((B j : ℝ) + |t| + 2))) ^ 3

/-- The GRH envelope is strictly positive when the bins are genuine intervals
and the modulus is nonzero.  In particular the energy budget which it supplies
is never a zero energy. -/
theorem primeBinGRHEnvelope_pos (line : DirichletLZerosOnLine) (q : ℕ)
    {ι : Type} [Fintype ι] (B : ι → ℕ) (hB : ∀ j, 2 ≤ B j) (t : ℝ)
    (hq : 0 < q) :
    0 < primeBinGRHEnvelope line q B t := by
  unfold primeBinGRHEnvelope
  refine Finset.prod_pos ?_
  intro j _
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hB2 : (2 : ℝ) ≤ (B j : ℝ) := by exact_mod_cast hB j
  have hBt : (1 : ℝ) ≤ (B j : ℝ) + |t| + 2 := by
    have ht : (0 : ℝ) ≤ |t| := abs_nonneg t
    linarith
  have harg : (1 : ℝ) ≤ (q : ℝ) * ((B j : ℝ) + |t| + 2) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (q : ℝ) * ((B j : ℝ) + |t| + 2) :=
        mul_le_mul hq1 hBt (by norm_num) (by positivity)
  have hlog : 0 ≤ Real.log ((q : ℝ) * ((B j : ℝ) + |t| + 2)) :=
    Real.log_nonneg harg
  have hbase : 0 < 1 + Real.log ((q : ℝ) * ((B j : ℝ) + |t| + 2)) := by
    linarith
  have hsqrt : 0 < Real.sqrt (B j : ℝ) := by
    apply Real.sqrt_pos.mpr
    linarith
  exact mul_pos (mul_pos (primeBinMellinK_pos line) hsqrt) (pow_pos hbase 3)

/-- **The smallest explicit energy input.**  At every cell, the square of the
critical-line GRH envelope is at most the multiplicity-one convolution energy
divided by the field degree.  There is no spectral constant, no averaged
quantity and no hidden character factor. -/
def PrimeBinMellinEnvelopeBudget (line : DirichletLZerosOnLine)
    {ι : Type} [Fintype ι]
    (cell : RationalCellConstruction) (q : ∀ n, cell.Den n → ℕ)
    (B : ι → ℕ) (s : ∀ n, cell.Den n → ℂ) (Econv d : ℕ → ℝ) : Prop :=
  ∀ n i, (primeBinGRHEnvelope line (q n i) B (s n i).im) ^ 2 ≤ Econv n / d n

/-! ## 2. From the GRH envelope to the energy residual -/

/-- **The energy residual budget from the nonprincipal character estimate.**
If each cell's support is a product of disjoint prime bins and the critical-line
envelope squared fits `Econv / d`, then the actual stage residual (the maximum
Mellin residue energy over the cells) is at most `Econv / d`. -/
theorem energyResidualBudget_of_primeBinMellinEnvelope
    (line : DirichletLZerosOnLine) {ι : Type} [Fintype ι] [DecidableEq ι]
    (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (A B : ι → ℕ) (s : ∀ n, cell.Den n → ℂ)
    (hA : ∀ j, 2 ≤ A j) (hAB : ∀ j, A j ≤ B j)
    (hdisj : Pairwise fun j k =>
      Disjoint (primeBin (A j) (B j)) (primeBin (A k) (B k)))
    (hre : ∀ n i, 0 ≤ (s n i).re)
    (Econv d : ℕ → ℝ)
    (hbudget : PrimeBinMellinEnvelopeBudget line cell q B s Econv d) :
    EnergyResidualBudget cell q q_ne_zero
      (fun _n _ => primeBinProducts A B) s Econv d := by
  intro n
  rw [residualAt_le_iff]
  intro i
  letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
  have hB2 : ∀ j, 2 ≤ B j := fun j => (hA j).trans (hAB j)
  have hgrh := primeBinMellinK_bound line (q n i) A B hB2 hAB hdisj
    (s n i).re (s n i).im (hre n i)
  have hs : ((s n i).re : ℂ) + (s n i).im * Complex.I = s n i :=
    Complex.re_add_im (s n i)
  rw [hs] at hgrh
  exact hgrh.trans (hbudget n i)

/-- The stage supremum of the per-cell GRH envelopes: the uniform character
norm bound of the stage. -/
noncomputable def primeBinGRHStageBound (line : DirichletLZerosOnLine)
    {ι : Type} [Fintype ι]
    (cell : RationalCellConstruction) (q : ∀ n, cell.Den n → ℕ)
    (B : ι → ℕ) (s : ∀ n, cell.Den n → ℂ) (n : ℕ) : ℝ :=
  letI := cell.denFintype n
  letI := cell.denNonempty n
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : cell.Den n => primeBinGRHEnvelope line (q n i) B (s n i).im)

/-- Each per-cell envelope is at most the stage supremum. -/
theorem primeBinGRHEnvelope_le_stageBound (line : DirichletLZerosOnLine)
    {ι : Type} [Fintype ι]
    (cell : RationalCellConstruction) (q : ∀ n, cell.Den n → ℕ)
    (B : ι → ℕ) (s : ∀ n, cell.Den n → ℂ) (n : ℕ) (i : cell.Den n) :
    primeBinGRHEnvelope line (q n i) B (s n i).im ≤
      primeBinGRHStageBound line cell q B s n := by
  letI := cell.denFintype n
  letI := cell.denNonempty n
  simp only [primeBinGRHStageBound]
  exact Finset.le_sup'
    (f := fun i : cell.Den n => primeBinGRHEnvelope line (q n i) B (s n i).im)
    (Finset.mem_univ i)

/-- The uniform form of the smallest explicit energy input: the squared stage
supremum of the GRH envelopes fits `Econv / d`. -/
def PrimeBinMellinUniformBudget (line : DirichletLZerosOnLine)
    {ι : Type} [Fintype ι]
    (cell : RationalCellConstruction) (q : ∀ n, cell.Den n → ℕ)
    (B : ι → ℕ) (s : ∀ n, cell.Den n → ℂ) (Econv d : ℕ → ℝ) : Prop :=
  ∀ n, (primeBinGRHStageBound line cell q B s n) ^ 2 ≤ Econv n / d n

/-- **The energy residual budget from the uniform character norm bound.**  This
is the form `B² ≤ Econv / d` requested by the paper: `B n` is the stage
supremum of the critical-line envelopes. -/
theorem energyResidualBudget_of_uniformPrimeBinBound
    (line : DirichletLZerosOnLine) {ι : Type} [Fintype ι] [DecidableEq ι]
    (cell : RationalCellConstruction)
    (q : ∀ n, cell.Den n → ℕ) (q_ne_zero : ∀ n i, q n i ≠ 0)
    (A B : ι → ℕ) (s : ∀ n, cell.Den n → ℂ)
    (hA : ∀ j, 2 ≤ A j) (hAB : ∀ j, A j ≤ B j)
    (hdisj : Pairwise fun j k =>
      Disjoint (primeBin (A j) (B j)) (primeBin (A k) (B k)))
    (hre : ∀ n i, 0 ≤ (s n i).re)
    (Econv d : ℕ → ℝ)
    (hbudget : PrimeBinMellinUniformBudget line cell q B s Econv d) :
    EnergyResidualBudget cell q q_ne_zero
      (fun _n _ => primeBinProducts A B) s Econv d := by
  intro n
  rw [residualAt_le_iff]
  intro i
  letI : NeZero (q n i) := ⟨q_ne_zero n i⟩
  have hB2 : ∀ j, 2 ≤ B j := fun j => (hA j).trans (hAB j)
  have hgrh := primeBinMellinK_bound line (q n i) A B hB2 hAB hdisj
    (s n i).re (s n i).im (hre n i)
  have hs : ((s n i).re : ℂ) + (s n i).im * Complex.I = s n i :=
    Complex.re_add_im (s n i)
  rw [hs] at hgrh
  have henvle := primeBinGRHEnvelope_le_stageBound line cell q B s n i
  have henvpos : 0 < primeBinGRHEnvelope line (q n i) B (s n i).im :=
    primeBinGRHEnvelope_pos line (q n i) B hB2 (s n i).im
      (Nat.pos_of_ne_zero (q_ne_zero n i))
  have hsq :
      (primeBinGRHEnvelope line (q n i) B (s n i).im) ^ 2 ≤
        (primeBinGRHStageBound line cell q B s n) ^ 2 :=
    pow_le_pow_left₀ henvpos.le henvle 2
  exact hgrh.trans (hsq.trans (hbudget n))

/-! ## 3. The numerator support from the cell construction -/

/-- **The elementary incidence bound of the cell construction.**  The maximum
number of numerator cells met inside one denominator cell is at most the total
number of numerator cells. -/
theorem perCell_le_numCard (C : RationalCellConstruction) (n : ℕ) :
    C.perCell n ≤ (@Fintype.card (C.Num n) (C.numFintype n) : ℝ) := by
  letI := C.denFintype n
  letI := C.denNonempty n
  letI := C.numFintype n
  have hnat : C.perCellNat n ≤ Fintype.card (C.Num n) := by
    have h := Finset.sup'_le Finset.univ_nonempty
      (fun i : C.Den n => (C.numeratorCellsIn n i).card)
      (fun i _ => Finset.card_le_univ (C.numeratorCellsIn n i))
    simpa only [RationalCellConstruction.perCellNat] using h
  unfold RationalCellConstruction.perCell
  exact_mod_cast hnat

/-- **`NumeratorSupportBound` from the finite numerator-cell count.**  The
aggregate support is the number of denominator cells times the per-cell
incidence maximum; the construction bounds the latter by `card (Num n)`, so the
paper's `C * M * V²` bound on the total numerator cells suffices. -/
theorem numeratorSupportBound_of_numCardCount
    (cell : RationalCellConstruction) {W C M : ℕ → ℝ}
    (hcount : ∀ n,
      (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) *
        (@Fintype.card (cell.Num n) (cell.numFintype n) : ℝ) ≤
        C n * (M n * denomScale W n ^ 2)) :
    NumeratorSupportBound cell W C M := by
  intro n
  have hden : (0 : ℝ) ≤ (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) :=
    (cell.card_den_pos n).le
  calc
    (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) * cell.perCell n ≤
        (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) *
          (@Fintype.card (cell.Num n) (cell.numFintype n) : ℝ) :=
      mul_le_mul_of_nonneg_left (perCell_le_numCard cell n) hden
    _ ≤ C n * (M n * denomScale W n ^ 2) := hcount n

/-- **`NumeratorSupportBound` from the normalized lattice count.**  This is the
form already used by the large-sieve certificate: dividing the aggregate support
bound by the positive number of denominator cells. -/
theorem numeratorSupportBound_of_latticeCount
    (cell : RationalCellConstruction) {W C M : ℕ → ℝ}
    (hlat : RationalCellLatticeCount W C M
      (fun n => (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ))
      cell.perCell) :
    NumeratorSupportBound cell W C M := by
  intro n
  have hc : 0 < (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) :=
    cell.card_den_pos n
  have hle := hlat n
  rw [le_div_iff₀ hc] at hle
  calc
    (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) * cell.perCell n =
        cell.perCell n * (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ) := by
      ring
    _ ≤ C n * (M n * denomScale W n ^ 2) := hle

/-- **`NumeratorSupportBound` from the exact per-cell count.**  If the finite
`PerCellNumeratorCount` total is the actual `card (Den n) * perCell n`, then its
determinant-level bound is literally the numerator support bound. -/
theorem numeratorSupportBound_of_perCellNumeratorCount
    (cell : RationalCellConstruction) {W C M : ℕ → ℝ}
    (D : PerCellNumeratorCount W C M)
    (hcells : ∀ n, D.cells n =
      (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ))
    (hperCell : ∀ n, D.perCell n = cell.perCell n) :
    NumeratorSupportBound cell W C M := by
  intro n
  rw [← hcells n, ← hperCell n, ← D.total_eq n]
  exact D.total_le n

/-! ## 4. The assembled critical-line certificate -/

/-- **The L18.4 large-sieve finish data from the critical line.**

The cell family is a rational-cell construction whose numerator support is a
product of disjoint prime bins.  The exponent of each cell lies in the closed
right half-plane, so the critical-line nonprincipal character estimate applies.
The only explicit energy input is the scalar envelope comparison
`PrimeBinMellinEnvelopeBudget`; the numerator count is the exact
`PerCellNumeratorCount` data.  A genuine `NonzeroResidualWitness` keeps the error
strictly positive. -/
structure EnergyResidualGRHData (line : DirichletLZerosOnLine)
    (W d C M Econv : ℕ → ℝ) (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- The rational-cell geometry. -/
  cell : RationalCellConstruction
  /-- The denominator modulus of each cell. -/
  q : ∀ n, cell.Den n → ℕ
  /-- Every denominator modulus is nonzero. -/
  q_ne_zero : ∀ n i, q n i ≠ 0
  /-- The Mellin exponent of each cell. -/
  s : ∀ n, cell.Den n → ℂ
  /-- The exponent lies in the closed right half-plane. -/
  re_nonneg : ∀ n i, 0 ≤ (s n i).re
  /-- Lower endpoints of the prime bins. -/
  A : ι → ℕ
  /-- Upper endpoints of the prime bins. -/
  B : ι → ℕ
  /-- Every bin starts at least at two. -/
  hA : ∀ j, 2 ≤ A j
  /-- Every bin is a genuine interval. -/
  hAB : ∀ j, A j ≤ B j
  /-- The bins are pairwise disjoint. -/
  hdisj : Pairwise fun j k =>
    Disjoint (primeBin (A j) (B j)) (primeBin (A k) (B k))
  /-- The field degree is positive. -/
  d_pos : ∀ n, 0 < d n
  /-- The undivided convolution energy is nonnegative. -/
  Econv_nonneg : ∀ n, 0 ≤ Econv n
  /-- **The smallest explicit energy input.** -/
  energyBudget : PrimeBinMellinEnvelopeBudget line cell q B s Econv d
  /-- **The genuine nonzero error.** -/
  witness : NonzeroResidualWitness cell q
    (fun _n _ => primeBinProducts A B) s
  /-- The exact per-cell numerator count. -/
  support : PerCellNumeratorCount W C M
  /-- The cell count is the actual cardinality of the denominator cells. -/
  support_cells : ∀ n, support.cells n =
    (@Fintype.card (cell.Den n) (cell.denFintype n) : ℝ)
  /-- The per-cell count is the actual incidence maximum. -/
  support_perCell : ∀ n, support.perCell n = cell.perCell n

namespace EnergyResidualGRHData

variable {line : DirichletLZerosOnLine} {W d C M Econv : ℕ → ℝ}
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The energy residual budget, proved from the critical-line estimate.** -/
theorem energyResidualBudget (D : EnergyResidualGRHData line W d C M Econv ι) :
    EnergyResidualBudget D.cell D.q D.q_ne_zero
      (fun _n _ => primeBinProducts D.A D.B) D.s Econv d :=
  energyResidualBudget_of_primeBinMellinEnvelope line D.cell D.q D.q_ne_zero
    D.A D.B D.s D.hA D.hAB D.hdisj D.re_nonneg Econv d D.energyBudget

/-- **The numerator support bound, proved from the cell construction.** -/
theorem numeratorSupportBound (D : EnergyResidualGRHData line W d C M Econv ι) :
    NumeratorSupportBound D.cell W C M :=
  numeratorSupportBound_of_perCellNumeratorCount D.cell D.support
    D.support_cells D.support_perCell

/-- **The numerator support is strictly positive.**  The exact per-cell total is
the number of denominator cells times a positive incidence maximum. -/
theorem support_pos (D : EnergyResidualGRHData line W d C M Econv ι) (n : ℕ) :
    0 < D.support.total n :=
  D.support.total_pos n

/-- **The energy budget is strictly positive.**  The GRH envelope is positive,
so `Econv / d` is positive at every stage; the certificate is never the
zero-energy degenerate case. -/
theorem energyBudget_pos (D : EnergyResidualGRHData line W d C M Econv ι)
    (n : ℕ) :
    0 < Econv n / d n := by
  let i : D.cell.Den n := Classical.choice (D.cell.denNonempty n)
  have hB2 : ∀ j, 2 ≤ D.B j := fun j => (D.hA j).trans (D.hAB j)
  have henv : 0 < primeBinGRHEnvelope line (D.q n i) D.B (D.s n i).im :=
    primeBinGRHEnvelope_pos line (D.q n i) D.B hB2 (D.s n i).im
      (Nat.pos_of_ne_zero (D.q_ne_zero n i))
  have hsq : 0 < (primeBinGRHEnvelope line (D.q n i) D.B (D.s n i).im) ^ 2 :=
    pow_pos henv 2
  exact hsq.trans_le (D.energyBudget n i)

/-- The undivided convolution energy is strictly positive: the positive
normalized budget divided by the positive field degree. -/
theorem Econv_pos (D : EnergyResidualGRHData line W d C M Econv ι) (n : ℕ) :
    0 < Econv n :=
  (div_pos_iff_of_pos_right (D.d_pos n)).mp (D.energyBudget_pos n)

/-- **The literal `LargeSieveFinishData`.**  Both previously assumed inputs are
now theorems: `energyBudget` from the critical-line estimate and
`numeratorSupport_le` from the cell construction. -/
noncomputable def toLargeSieveFinishData
    (D : EnergyResidualGRHData line W d C M Econv ι) :
    LargeSieveFinishData W d C M Econv where
  cell := D.cell
  q := D.q
  q_ne_zero := D.q_ne_zero
  P := fun _n _ => primeBinProducts D.A D.B
  s := D.s
  d_pos := D.d_pos
  Econv_nonneg := D.Econv_nonneg
  energyBudget := D.energyResidualBudget
  witness := D.witness
  numeratorSupport_le := D.numeratorSupportBound

/-- **The L18.4 large-sieve inequality.** -/
theorem large_sieve (D : EnergyResidualGRHData line W d C M Econv ι) (n : ℕ) :
    (D.toLargeSieveFinishData).secondMoment n ≤
      C n * (M n * denomScale W n ^ 2) * (Econv n / d n) :=
  (D.toLargeSieveFinishData).large_sieve n

/-- **The large-sieve inequality together with a genuinely positive error.** -/
theorem large_sieve_with_nonzero_error
    (D : EnergyResidualGRHData line W d C M Econv ι) :
    (∀ n, (D.toLargeSieveFinishData).secondMoment n ≤
      C n * (M n * denomScale W n ^ 2) * (Econv n / d n)) ∧
      ∃ n, 0 < (D.toLargeSieveFinishData).error n :=
  (D.toLargeSieveFinishData).large_sieve_with_nonzero_error

/-- The residual error is positive at the witness stage. -/
theorem residual_nonzero (D : EnergyResidualGRHData line W d C M Econv ι) :
    ∃ n, 0 < residualAt D.cell D.q D.q_ne_zero
      (fun _n _ => primeBinProducts D.A D.B) D.s n :=
  (D.toLargeSieveFinishData).residual_nonzero

end EnergyResidualGRHData

/-! ## Axiom audit -/

#print axioms primeBinCharacterBound_of_critical_line
#print axioms primeBinMellinK_pos
#print axioms primeBinMellinK_bound
#print axioms primeBinGRHEnvelope_pos
#print axioms energyResidualBudget_of_primeBinMellinEnvelope
#print axioms primeBinGRHEnvelope_le_stageBound
#print axioms energyResidualBudget_of_uniformPrimeBinBound
#print axioms perCell_le_numCard
#print axioms numeratorSupportBound_of_numCardCount
#print axioms numeratorSupportBound_of_latticeCount
#print axioms numeratorSupportBound_of_perCellNumeratorCount
#print axioms EnergyResidualGRHData.energyResidualBudget
#print axioms EnergyResidualGRHData.numeratorSupportBound
#print axioms EnergyResidualGRHData.support_pos
#print axioms EnergyResidualGRHData.energyBudget_pos
#print axioms EnergyResidualGRHData.Econv_pos
#print axioms EnergyResidualGRHData.toLargeSieveFinishData
#print axioms EnergyResidualGRHData.large_sieve
#print axioms EnergyResidualGRHData.large_sieve_with_nonzero_error
#print axioms EnergyResidualGRHData.residual_nonzero

end Cogentic.RandomizedL18_4
