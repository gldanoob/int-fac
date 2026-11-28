import Cogentic.RandomizedL18_4Full

/-!
# L18.4: the cell-count and numerator fields, finished

`RandomizedL18_4CellCount`/`CellData` reduce the denominator cell count to an
integer cell of the shrunken interval plus the critical-line prime-bin supply,
and `RandomizedL18_4Numerator`/`Mass` reduce the numerator count to the actual
root-progression count plus an explicit square-root error.  Those files still
carry the residuals as hypotheses of their reduction bundles.

This file collects the *smallest explicit finite-count inequalities* behind the
two fields, proves the reductions from them, and assembles the corresponding
`L18_4Certificate` sub-fields.

## 1. The cell count

`PrimeBinSupply K0` is the literal prime-count inequality

`(B - A) - K0 (1 + log (3B))² √B ≤ #(primeBin A B) · log B`,

i.e. the prime-bin supply before the elementary `log B ≤ lg` step.  It is the
smallest statement left by `primeBin_supply_from_critical_line`; the only
content of the critical line used by the cell count is this finite inequality.
`cellSupply_of_supply` recovers the `L18_4Certificate.cellSupply` form
`(B - A)/(2 lg) ≤ #bin`, and `cellSupply_of_critical_line` extracts a single
constant `K0` for the whole family.

`CellCountFinish` then carries an actual `CellData W d`, the adapter equality
`Ncell = cellData.Ncell` (so `Ncell` is a prime count, never a chosen zero) and
the pointwise supply-fit inequality `2 d K0 (1 + log 3 + W)² ≤ K`.  Its
`cell_prime_count` is the literal L18.4 field, and `cell_count_pos` shows the
field's right-hand side is strictly positive, so the cell count cannot be zero
by fiat.

## 2. The numerator count

`NumeratorData` carries `MassErrorInputs` (whose `mass_lower` and `error_le`
are proved in `RandomizedL18_4Mass`) together with the identification of `Nnum`
with the actual root-residue count, but *not* the residue-class deviation.
`NumeratorFinish` adds that deviation.  The deviation is exactly the
orthogonality/prime-pattern computation of `PrimePatternProgressionBound`;
`exists_patternDeviation` restates that bound in terms of `progressionError`,
`deviation_at_of_patternProgression` shows that it may be evaluated at *any*
larger error constant, and `NumeratorFinish.ofPatternProgression` therefore
builds a `NumeratorFinish` from `NumeratorData` plus the scalar comparison
`patternK hprog ≤ mass.K`.  The remaining numerical input is the finite
product-saving inequality already isolated in `MassErrorInputs.error_le`.

## 3. The certificate

`L18_4CellFinish` extends `L18_4Ambient` with the two sub-field bundles.
`toInputs` rebuilds a literal `L18_4Inputs`, and `toCertificate` plugs the two
bundles into `L18_4Certificate` once the large-sieve certificate, the `S2`
adapter and the thin-pair data are supplied.  Finally
`ofCanonicalAndNumerator` builds the cell data from the canonical shrunken cell
and the supply constant from the critical line, and
`ofCanonicalAndPatternProgression`/`ofCanonicalAndCriticalLine` also discharge
the numerator deviation, leaving only the explicit pointwise fit, the
`MassErrorInputs`/`NumeratorData` data and the scalar comparison
`patternK hprog ≤ mass.K`.

No `sorry`, `admit`, `axiom` or `native_decide` is used; no count, mass or error
is set to zero.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open scoped BigOperators
open Cogentic.Randomized
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

set_option linter.style.haveILetI false
set_option linter.checkUnivs false

/-! ## 1. The explicit prime-bin supply residuals -/

/-- **The finite prime-bin supply.**  The bin `(A, B]` contains all but a
square-root error of its width, measured in `log B` units.  This is the literal
finite-count inequality (no `lg`, no cell, no asymptotics) that the critical
line supplies. -/
def PrimeBinSupply (K0 : ℝ) : Prop :=
  ∀ A B : ℕ, 2 ≤ A → A ≤ B →
    (B : ℝ) - (A : ℝ) -
        K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
      ((primeBin A B).card : ℝ) * Real.log (B : ℝ)

/-- **The `L18_4Certificate.cellSupply` form.**  This is `PrimeBinSupply` after
the elementary step `log B ≤ lg` and the division by `2 lg`. -/
def PrimeBinCellSupply (K0 : ℝ) : Prop :=
  ∀ {A B : ℕ}, 2 ≤ A → A ≤ B → ∀ {lg : ℝ}, 0 < lg →
    Real.log (B : ℝ) ≤ lg →
    K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        ((B : ℝ) - (A : ℝ)) / 2 →
      ((B : ℝ) - (A : ℝ)) / (2 * lg) ≤ ((primeBin A B).card : ℝ)

/-- **The reduction of the certificate field to the finite supply.**  This is
`cell_card_lower_of_primeBinSupply` with the same hypotheses, written as a
reduction between the two `Prop`s. -/
theorem cellSupply_of_supply {K0 : ℝ} (hK0 : 0 ≤ K0) (h : PrimeBinSupply K0) :
    PrimeBinCellSupply K0 := by
  intro A B hA hAB lg hlg hlog herr
  exact cell_card_lower_of_primeBinSupply hK0 h hA hAB hlg hlog herr

/-- The critical line supplies a single constant satisfying the finite
prime-bin inequality. -/
theorem primeBinSupply_of_critical_line (line : DirichletLZerosOnLine) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ PrimeBinSupply K0 := by
  simpa only [PrimeBinSupply, Cogentic.Randomized.PrimeBinSupplyBound] using
    (Cogentic.Randomized.primeBin_supply_from_critical_line line)

/-- The critical line supplies the `L18_4Certificate.cellSupply` field for a
single constant. -/
theorem cellSupply_of_critical_line (line : DirichletLZerosOnLine) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ PrimeBinCellSupply K0 := by
  obtain ⟨K0, hK0, h⟩ := primeBinSupply_of_critical_line line
  exact ⟨K0, hK0, cellSupply_of_supply hK0 h⟩

/-- The explicit supply-fit condition: the square-root error fits in half a cell
of width `V/(dK)`.  This is the only pointwise real inequality used by the cell
count besides the geometry of `CellData`. -/
def CellSupplyFit (W d : ℕ → ℝ) (K0 : ℝ) : Prop :=
  ∀ n, 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n

/-- **The supply-fit is an eventual consequence of polynomial degree growth.**  If
`d n ≤ exp (c W n)` with `c < 1/4` and `W → ∞`, then the explicit pointwise
inequality `CellSupplyFit W d K0` holds eventually.  This is the existing
`eventually_supply_fit_of_exp_dominated`, restated for the finish bundle's
`CellSupplyFit`. -/
theorem eventually_cellSupplyFit_of_exp_dominated
    {W d : ℕ → ℝ} {K0 c : ℝ} (hK0 : 0 ≤ K0) (hc : c < 1 / 4)
    (hd : ∀ᶠ n : ℕ in atTop, d n ≤ Real.exp (c * W n))
    (hW : Tendsto W atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n :=
  eventually_supply_fit_of_exp_dominated hK0 hc hd hW

/-! ## 2. The cell-count sub-field -/

/-- **The denominator cell count, finished.**  It carries an actual integer cell
`(A, B] ⊂ (0, V]` of width at least `V/(dK)`, the identification of `Ncell` with
the actual prime count of that cell, and the explicit finite supply plus its
pointwise fit. -/
structure CellCountFinish (W d Ncell : ℕ → ℝ) where
  /-- The integer denominator cell. -/
  cellData : CellData W d
  /-- `Ncell` is the actual prime count of the cell. -/
  hNcell : ∀ n, Ncell n = cellData.Ncell n
  /-- The prime-bin supply constant. -/
  cellK0 : ℝ
  /-- The supply constant is nonnegative. -/
  cellK0_nonneg : 0 ≤ cellK0
  /-- The finite prime-bin supply inequality. -/
  supply : PrimeBinSupply cellK0
  /-- The square-root error fits in half the cell width. -/
  supplyFit : CellSupplyFit W d cellK0
  /-- `log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- The field degree is positive. -/
  d_pos : ∀ n, 0 < d n

namespace CellCountFinish

variable {W d Ncell : ℕ → ℝ}

/-- **The literal `cell_prime_count` field**, proved from the finite supply and
the explicit fit. -/
theorem cell_prime_count (C : CellCountFinish W d Ncell) :
    ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ Ncell n := by
  intro n
  rw [C.hNcell n]
  exact cell_prime_count_of_cellData C.cellK0_nonneg
    (cellSupply_of_supply C.cellK0_nonneg C.supply) C.W_nonneg C.d_pos
    C.cellData C.supplyFit n

/-- `Ncell` is manifestly the actual prime count of the cell, never a chosen
number. -/
theorem Ncell_eq_primeBin_card (C : CellCountFinish W d Ncell) (n : ℕ) :
    Ncell n = ((primeBin (C.cellData.A n) (C.cellData.B n)).card : ℝ) := by
  rw [C.hNcell n]
  rfl

/-- **The cell count is strictly positive.**  The field's lower bound is
positive, so the actual prime count cannot be zero. -/
theorem cell_count_pos (C : CellCountFinish W d Ncell) (n : ℕ) :
    0 < Ncell n := by
  have hV : 0 < denomScale W n := denomScale_pos W n
  have hK : 0 < cellMesh W n := cellMesh_pos W n
  have h1W : 0 < 1 + W n := by linarith [C.W_nonneg n]
  have h2d : 0 < 2 * d n := mul_pos (by norm_num) (C.d_pos n)
  have hpos :
      0 < denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) :=
    div_pos hV (mul_pos (mul_pos h2d hK) h1W)
  exact lt_of_lt_of_le hpos (C.cell_prime_count n)

/-- The cell count is nonzero. -/
theorem cell_count_ne_zero (C : CellCountFinish W d Ncell) (n : ℕ) :
    Ncell n ≠ 0 :=
  (C.cell_count_pos n).ne'

end CellCountFinish

/-! ## 3. The numerator error and its orthogonality deviation -/

/-- The explicit prime-pattern progression error is nonnegative. -/
theorem progressionError_nonneg (K : ℝ) (hK : 0 ≤ K) (q : ℕ) (B : ℕ → ℕ)
    (patterns : Finset (Finset ℕ)) :
    0 ≤ progressionError K q B patterns := by
  unfold progressionError
  refine Finset.sum_nonneg ?_
  intro s _
  refine Finset.prod_nonneg ?_
  intro i _
  exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (Real.sqrt_nonneg _)

/-- **The progression error is genuinely nonzero.**  If the constant is positive
and some occupied pattern has every bin of size at least two, the explicit
square-root error has a positive summand. -/
theorem progressionError_pos {K : ℝ} {q : ℕ} {B : ℕ → ℕ}
    {patterns : Finset (Finset ℕ)}
    (hK : 0 < K) (hne : patterns.Nonempty)
    (hB : ∀ s ∈ patterns, ∀ i ∈ s, 2 ≤ B i) :
    0 < progressionError K q B patterns := by
  unfold progressionError
  obtain ⟨s0, hs0⟩ := hne
  refine Finset.sum_pos' ?nonneg ⟨s0, hs0, ?pos⟩
  · intro s _
    refine Finset.prod_nonneg ?_
    intro i _
    exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (Real.sqrt_nonneg _)
  · refine Finset.prod_pos ?_
    intro i hi
    have hBi : 2 ≤ B i := hB s0 hs0 i hi
    have hBpos : (0 : ℝ) < (B i : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hBi)
    have hbase : (0 : ℝ) < 1 + Real.log (3 * (q : ℝ) * (B i : ℝ)) := by
      rcases eq_or_ne q 0 with hq0 | hqne
      · subst hq0
        have hzero : 3 * ((0 : ℕ) : ℝ) * (B i : ℝ) = 0 := by norm_num
        rw [hzero, Real.log_zero]
        norm_num
      · have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
          have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
          exact_mod_cast hqpos
        have hBi1 : (1 : ℝ) ≤ (B i : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hBi)
        have hx : (1 : ℝ) ≤ 3 * (q : ℝ) * (B i : ℝ) := by nlinarith
        have hlog : 0 ≤ Real.log (3 * (q : ℝ) * (B i : ℝ)) :=
          Real.log_nonneg hx
        linarith
    have hsqpos :
        (0 : ℝ) < (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 := by
      positivity
    have hsqrtpos : 0 < Real.sqrt (B i : ℝ) := Real.sqrt_pos.mpr hBpos
    exact mul_pos (mul_pos (by linarith : (0 : ℝ) < 2 * K) hsqpos) hsqrtpos

/-- The explicit progression error is monotone in the error constant. -/
theorem progressionError_mono {K K' : ℝ} (hK : 0 ≤ K) (hKK' : K ≤ K')
    (q : ℕ) (B : ℕ → ℕ) (patterns : Finset (Finset ℕ)) :
    progressionError K q B patterns ≤ progressionError K' q B patterns := by
  unfold progressionError
  refine Finset.sum_le_sum ?_
  intro s _
  refine Finset.prod_le_prod ?nonneg ?step
  · intro i _
    exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (Real.sqrt_nonneg _)
  · intro i _
    have h2 : 2 * K ≤ 2 * K' := by linarith
    have hg :
        0 ≤ (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
          Real.sqrt (B i : ℝ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h := mul_le_mul_of_nonneg_right h2 hg
    calc
      2 * K * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
            Real.sqrt (B i : ℝ)
          = (2 * K) * ((1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
              Real.sqrt (B i : ℝ)) := by ring
      _ ≤ (2 * K') * ((1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
              Real.sqrt (B i : ℝ)) := h
      _ = 2 * K' * (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 *
              Real.sqrt (B i : ℝ) := by ring

/-- **The orthogonality deviation at a chosen constant.**  `PrimePatternProgression`
is restated as a single finite-sum inequality for the concrete
`progressionError`.  This is the residue-class computation behind the numerator
count. -/
theorem exists_patternDeviation (hprog : PrimePatternProgressionBound) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
        (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ)),
        Pairwise (fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        |(((primeBinPatternProducts A B patterns).filter
              (fun m : ℕ => (r : ZMod q) = (m : ZMod q))).card : ℝ) -
            (((primeBinPatternProducts A B patterns).filter
              (fun m : ℕ => m.Coprime q)).card : ℝ) / (q.totient : ℝ)| ≤
          progressionError K q B patterns := by
  obtain ⟨K, hK, hbound⟩ := hprog
  refine ⟨K, hK, ?_⟩
  intro q _ r A B patterns hdisj hA hAB
  simpa only [progressionError] using hbound q r A B patterns hdisj hA hAB

/-- The constant chosen from `PrimePatternProgressionBound`. -/
noncomputable def patternK (hprog : PrimePatternProgressionBound) : ℝ :=
  Classical.choose (exists_patternDeviation hprog)

theorem patternK_nonneg (hprog : PrimePatternProgressionBound) :
    0 ≤ patternK hprog :=
  (Classical.choose_spec (exists_patternDeviation hprog)).1

theorem patternK_deviation (hprog : PrimePatternProgressionBound) :
    ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
      (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ)),
      Pairwise (fun i j =>
        Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
      |(((primeBinPatternProducts A B patterns).filter
            (fun m : ℕ => (r : ZMod q) = (m : ZMod q))).card : ℝ) -
          (((primeBinPatternProducts A B patterns).filter
            (fun m : ℕ => m.Coprime q)).card : ℝ) / (q.totient : ℝ)| ≤
        progressionError (patternK hprog) q B patterns :=
  (Classical.choose_spec (exists_patternDeviation hprog)).2

/-- **The deviation at any larger error constant.**  Since `progressionError` is
monotone in its constant, the orthogonality bound obtained at `patternK hprog`
holds at every `K ≥ patternK hprog`. -/
theorem deviation_at_of_patternProgression
    (hprog : PrimePatternProgressionBound) {K : ℝ} (_hK : 0 ≤ K)
    (hKge : patternK hprog ≤ K)
    (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
    (A B : ℕ → ℕ) (patterns : Finset (Finset ℕ))
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i) :
    |(((primeBinPatternProducts A B patterns).filter
          (fun m : ℕ => (r : ZMod q) = (m : ZMod q))).card : ℝ) -
        (((primeBinPatternProducts A B patterns).filter
          (fun m : ℕ => m.Coprime q)).card : ℝ) / (q.totient : ℝ)| ≤
      progressionError K q B patterns :=
  (patternK_deviation hprog q r A B patterns hdisj hA hAB).trans
    (progressionError_mono (patternK_nonneg hprog) hKge q B patterns)

/-! ## 4. The numerator-count sub-field -/

/-- **The numerator data without the deviation.**  It carries the actual pool,
the mass/error data of `RandomizedL18_4Mass`, and the identification of `Nnum`
with the actual root-residue count.  The only analytic input still missing is
the residue-class deviation, which is supplied either explicitly or from the
prime-pattern progression bound. -/
structure NumeratorData (W ell rho Nnum : ℕ → ℝ) where
  /-- The mass and error data of the actual numerator pool. -/
  mass : MassErrorInputs W ell rho
  /-- The root residue. -/
  r : ∀ n, (ZMod (mass.q n))ˣ
  /-- The pool is coprime to the root modulus. -/
  coprime_all : ∀ n m,
    m ∈ numeratorPool (mass.A n) (mass.B n) (mass.patterns n) →
      m.Coprime (mass.q n)
  /-- `Nnum` is the actual root-residue count. -/
  Nnum_eq_count : ∀ n, Nnum n =
    (progressionCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n)
      (r n) : ℝ)

/-- **The numerator count, finished.**  It is `NumeratorData` together with the
residue-class deviation, which is exactly the orthogonality/prime-pattern
computation. -/
structure NumeratorFinish (W ell rho Nnum : ℕ → ℝ)
    extends NumeratorData W ell rho Nnum where
  /-- The residue-class deviation of the actual count. -/
  deviation : ∀ n,
    |(progressionCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n)
        (r n) : ℝ) -
      (coprimeCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n) : ℝ) /
        (mass.q n).totient| ≤
      progressionError mass.K (mass.q n) (mass.B n) (mass.patterns n)

namespace NumeratorFinish

variable {W ell rho Nnum : ℕ → ℝ}

/-- **The literal `cell_numerator_count` field.** -/
theorem numerator_count (N : NumeratorFinish W ell rho Nnum) :
    ∀ n, denomScale W n * rho n / (2 * ell n) ≤ Nnum n := fun n =>
  (N.mass.toNumeratorCountInputs Nnum N.r N.coprime_all N.Nnum_eq_count
    N.deviation).numerator_count n

/-- The explicit square-root error is at most half the reference count.  This is
the finite product-saving inequality `MassErrorInputs.error_le`, restated at the
numerator bundle. -/
theorem progression_error_le (N : NumeratorFinish W ell rho Nnum) (n : ℕ) :
    progressionError N.mass.K (N.mass.q n) (N.mass.B n) (N.mass.patterns n) ≤
      denomScale W n * rho n / (2 * ell n) :=
  N.mass.error_le n

/-- The explicit error is nonnegative. -/
theorem progression_error_nonneg (N : NumeratorFinish W ell rho Nnum) (n : ℕ) :
    0 ≤ progressionError N.mass.K (N.mass.q n) (N.mass.B n) (N.mass.patterns n) :=
  progressionError_nonneg N.mass.K N.mass.K_nonneg (N.mass.q n) (N.mass.B n)
    (N.mass.patterns n)

/-- The explicit error is genuinely positive whenever the data are nontrivial. -/
theorem progression_error_pos (N : NumeratorFinish W ell rho Nnum) (n : ℕ)
    (hK : 0 < N.mass.K) (hne : (N.mass.patterns n).Nonempty)
    (hB : ∀ s ∈ N.mass.patterns n, ∀ i ∈ s, 2 ≤ N.mass.B n i) :
    0 < progressionError N.mass.K (N.mass.q n) (N.mass.B n) (N.mass.patterns n) :=
  progressionError_pos hK hne hB

/-- Add an explicit deviation to the numerator data. -/
noncomputable def ofDeviation (D : NumeratorData W ell rho Nnum)
    (deviation : ∀ n,
      |(progressionCount (D.mass.A n) (D.mass.B n) (D.mass.patterns n)
          (D.mass.q n) (D.r n) : ℝ) -
        (coprimeCount (D.mass.A n) (D.mass.B n) (D.mass.patterns n)
          (D.mass.q n) : ℝ) /
          (D.mass.q n).totient| ≤
        progressionError D.mass.K (D.mass.q n) (D.mass.B n) (D.mass.patterns n)) :
    NumeratorFinish W ell rho Nnum where
  mass := D.mass
  r := D.r
  coprime_all := D.coprime_all
  Nnum_eq_count := D.Nnum_eq_count
  deviation := deviation

/-- **Discharge the deviation by the orthogonality computation.**  From the
prime-pattern progression bound and the scalar comparison
`patternK hprog ≤ D.mass.K`, the deviation is no longer an assumption. -/
noncomputable def ofPatternProgression (D : NumeratorData W ell rho Nnum)
    (hprog : PrimePatternProgressionBound) (hKge : patternK hprog ≤ D.mass.K) :
    NumeratorFinish W ell rho Nnum :=
  ofDeviation D fun n => by
    haveI : NeZero (D.mass.q n) := ⟨(D.mass.q_pos n).ne'⟩
    exact deviation_at_of_patternProgression hprog D.mass.K_nonneg hKge
      (D.mass.q n) (D.r n) (D.mass.A n) (D.mass.B n) (D.mass.patterns n)
      (D.mass.hdisj n) (D.mass.hA n) (D.mass.hAB n)

end NumeratorFinish

/-! ## 5. The combined finish bundle and the certificate sub-fields -/

/-- **The L18.4 cell-count and numerator sub-fields.**  It extends the ambient
data of `RandomizedL18_4Full.L18_4Ambient` with the two genuine sub-bundles; the
remaining two analytic fields (`large_sieve` and `thin_pair_fraction`) are not
part of it. -/
structure L18_4CellFinish extends L18_4Ambient where
  /-- The denominator-cell count data. -/
  cellData : CellData W d
  /-- `Ncell` is the actual prime count of the cell. -/
  hNcell : ∀ n, Ncell n = cellData.Ncell n
  /-- The prime-bin supply constant. -/
  cellK0 : ℝ
  /-- The supply constant is nonnegative. -/
  cellK0_nonneg : 0 ≤ cellK0
  /-- The finite prime-bin supply inequality. -/
  cellSupply : PrimeBinSupply cellK0
  /-- The square-root error fits in half the cell width. -/
  cellSupplyFit : CellSupplyFit W d cellK0
  /-- The numerator mass/error data. -/
  mass : MassErrorInputs W ell rho
  /-- The root residue. -/
  numR : ∀ n, (ZMod (mass.q n))ˣ
  /-- The numerator pool is coprime to the root modulus. -/
  numCoprime : ∀ n m,
    m ∈ numeratorPool (mass.A n) (mass.B n) (mass.patterns n) →
      m.Coprime (mass.q n)
  /-- `Nnum` is the actual root-residue count. -/
  numEq : ∀ n, Nnum n =
    (progressionCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n)
      (numR n) : ℝ)
  /-- The residue-class deviation of the numerator count. -/
  numDeviation : ∀ n,
    |(progressionCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n)
        (numR n) : ℝ) -
      (coprimeCount (mass.A n) (mass.B n) (mass.patterns n) (mass.q n) : ℝ) /
        (mass.q n).totient| ≤
      progressionError mass.K (mass.q n) (mass.B n) (mass.patterns n)

namespace L18_4CellFinish

/-- The cell-count view of the bundle. -/
noncomputable def cellCount (C : L18_4CellFinish) :
    CellCountFinish C.W C.d C.Ncell where
  cellData := C.cellData
  hNcell := C.hNcell
  cellK0 := C.cellK0
  cellK0_nonneg := C.cellK0_nonneg
  supply := C.cellSupply
  supplyFit := C.cellSupplyFit
  W_nonneg := C.W_nonneg
  d_pos := C.d_pos

/-- The numerator-count view of the bundle. -/
noncomputable def numeratorData (C : L18_4CellFinish) :
    NumeratorData C.W C.ell C.rho C.Nnum where
  mass := C.mass
  r := C.numR
  coprime_all := C.numCoprime
  Nnum_eq_count := C.numEq

/-- The numerator-count view of the bundle, with the deviation attached. -/
noncomputable def numeratorCount (C : L18_4CellFinish) :
    NumeratorFinish C.W C.ell C.rho C.Nnum :=
  NumeratorFinish.ofDeviation C.numeratorData C.numDeviation

/-- **The literal `cell_prime_count` field of L18.4.** -/
theorem cell_prime_count (C : L18_4CellFinish) :
    ∀ n, denomScale C.W n / (2 * C.d n * cellMesh C.W n * (1 + C.W n)) ≤
      C.Ncell n :=
  C.cellCount.cell_prime_count

/-- **The literal `cell_numerator_count` field of L18.4.** -/
theorem cell_numerator_count (C : L18_4CellFinish) :
    ∀ n, denomScale C.W n * C.rho n / (2 * C.ell n) ≤ C.Nnum n :=
  C.numeratorCount.numerator_count

/-- **Both fields at once.** -/
theorem cell_and_numerator_count (C : L18_4CellFinish) :
    (∀ n, denomScale C.W n / (2 * C.d n * cellMesh C.W n * (1 + C.W n)) ≤
      C.Ncell n) ∧
    (∀ n, denomScale C.W n * C.rho n / (2 * C.ell n) ≤ C.Nnum n) :=
  ⟨C.cell_prime_count, C.cell_numerator_count⟩

/-- The cell count is strictly positive, so it is never a zero-count. -/
theorem cell_count_pos (C : L18_4CellFinish) (n : ℕ) : 0 < C.Ncell n :=
  C.cellCount.cell_count_pos n

/-- The numerator square-root error is genuinely nonnegative. -/
theorem numerator_error_nonneg (C : L18_4CellFinish) (n : ℕ) :
    0 ≤ progressionError C.mass.K (C.mass.q n) (C.mass.B n) (C.mass.patterns n) :=
  C.numeratorCount.progression_error_nonneg n

/-- The numerator square-root error is at most half the reference count. -/
theorem numerator_error_le (C : L18_4CellFinish) (n : ℕ) :
    progressionError C.mass.K (C.mass.q n) (C.mass.B n) (C.mass.patterns n) ≤
      denomScale C.W n * C.rho n / (2 * C.ell n) :=
  C.numeratorCount.progression_error_le n

/-- **The two certificate sub-fields, assembled into a literal `L18_4Inputs`.**
The remaining large-sieve and thin-pair fields are passed explicitly. -/
noncomputable def toInputs (C : L18_4CellFinish)
    (large_sieve : ∀ n,
      C.S2 n ≤ C.C n * (C.M n * denomScale C.W n ^ 2) * (C.Econv n / C.d n))
    (thin_pair_fraction : ∀ n, C.thin n ≤ 1 / cellMesh C.W n) :
    L18_4Inputs :=
  C.toL18_4Ambient.toInputs large_sieve C.cell_prime_count
    C.cell_numerator_count thin_pair_fraction

/-- The composed input still has the L18.4 `D^{-B}` deficit. -/
theorem toInputs_subexpLoss (C : L18_4CellFinish)
    (large_sieve : ∀ n,
      C.S2 n ≤ C.C n * (C.M n * denomScale C.W n ^ 2) * (C.Econv n / C.d n))
    (thin_pair_fraction : ∀ n, C.thin n ≤ 1 / cellMesh C.W n) :
    SubexpLoss (C.toInputs large_sieve thin_pair_fraction).loss :=
  (C.toInputs large_sieve thin_pair_fraction).subexpLoss

/-- The composed L18.4 `SubexpLeaf`. -/
noncomputable def toSubexpLeaf (C : L18_4CellFinish)
    (large_sieve : ∀ n,
      C.S2 n ≤ C.C n * (C.M n * denomScale C.W n ^ 2) * (C.Econv n / C.d n))
    (thin_pair_fraction : ∀ n, C.thin n ≤ 1 / cellMesh C.W n) : SubexpLeaf :=
  (C.toInputs large_sieve thin_pair_fraction).toSubexpLeaf

/-- **The corresponding `L18_4Certificate`.**  Given the large-sieve
sub-certificate, its `S2` adapter, and the thin-pair raw data, the finish bundle
supplies every remaining sub-field: `cellData`, `hNcell`, `cellK0`,
`cellSupply`, `cellSupplyFit`, `mass`, `numR`, `numCoprime`, `numEq` and
`numDeviation`. -/
noncomputable def toCertificate (C : L18_4CellFinish)
    (largeSieve : LargeSieveCertificate C.W C.d C.C C.M C.Econv)
    (hS2 : ∀ n, C.S2 n = largeSieve.secondMoment n)
    (thinData : ThinAggregateData C.W C.d C.ell C.rho C.thin C.Ncell C.Nnum) :
    L18_4Certificate where
  toL18_4Ambient := C.toL18_4Ambient
  largeSieve := largeSieve
  hS2 := hS2
  cellData := C.cellData
  hNcell := C.hNcell
  cellK0 := C.cellK0
  cellK0_nonneg := C.cellK0_nonneg
  cellSupply := cellSupply_of_supply C.cellK0_nonneg C.cellSupply
  cellSupplyFit := C.cellSupplyFit
  mass := C.mass
  numR := C.numR
  numCoprime := C.numCoprime
  numEq := C.numEq
  numDeviation := C.numDeviation
  thinData := thinData

/-- The certificate assembled from the finish bundle carries the same L18.4
deficit. -/
theorem toCertificate_subexpLoss (C : L18_4CellFinish)
    (largeSieve : LargeSieveCertificate C.W C.d C.C C.M C.Econv)
    (hS2 : ∀ n, C.S2 n = largeSieve.secondMoment n)
    (thinData : ThinAggregateData C.W C.d C.ell C.rho C.thin C.Ncell C.Nnum) :
    SubexpLoss (C.toCertificate largeSieve hS2 thinData).toInputs.loss :=
  (C.toCertificate largeSieve hS2 thinData).subexpLoss

end L18_4CellFinish

/-! ## 6. The canonical-cell constructor -/

/-- The prime-bin supply constant chosen from the critical line. -/
noncomputable def cellK0OfLine (line : DirichletLZerosOnLine) : ℝ :=
  Classical.choose (primeBinSupply_of_critical_line line)

theorem cellK0OfLine_nonneg (line : DirichletLZerosOnLine) :
    0 ≤ cellK0OfLine line :=
  (Classical.choose_spec (primeBinSupply_of_critical_line line)).1

theorem cellK0OfLine_supply (line : DirichletLZerosOnLine) :
    PrimeBinSupply (cellK0OfLine line) :=
  (Classical.choose_spec (primeBinSupply_of_critical_line line)).2

/-- **The finish bundle from the canonical shrunken cell.**  The cell data are
`canonicalCellData` (an actual integer cell inside `(2V/3, (2V/3)(1 + 1/d)]`),
the supply is the critical-line supply, and the numerator data are the actual
pool/count data.  The only residuals are the explicit pointwise fit
`CellSupplyFit`, the `MassErrorInputs` package and the adapter equality
`Ncell = canonicalCellData.Ncell`. -/
noncomputable def ofCanonicalAndNumerator (A : L18_4Ambient)
    (line : DirichletLZerosOnLine)
    (hV12 : ∀ n, 12 ≤ denomScale A.W n)
    (hK6 : ∀ n, 6 ≤ A.d n * cellMesh A.W n)
    (hNcell : ∀ n, A.Ncell n =
      (canonicalCellData (W := A.W) (d := A.d) A.d_pos hV12 hK6).Ncell n)
    (supplyFit : CellSupplyFit A.W A.d (cellK0OfLine line))
    (N : NumeratorFinish A.W A.ell A.rho A.Nnum) :
    L18_4CellFinish where
  toL18_4Ambient := A
  cellData := canonicalCellData (W := A.W) (d := A.d) A.d_pos hV12 hK6
  hNcell := hNcell
  cellK0 := cellK0OfLine line
  cellK0_nonneg := cellK0OfLine_nonneg line
  cellSupply := cellK0OfLine_supply line
  cellSupplyFit := supplyFit
  mass := N.mass
  numR := N.r
  numCoprime := N.coprime_all
  numEq := N.Nnum_eq_count
  numDeviation := N.deviation

/-- **The fully reduced canonical constructor.**  The numerator deviation is
discharged by the prime-pattern progression bound; the only scalar comparison
left is `patternK hprog ≤ mass.K`. -/
noncomputable def ofCanonicalAndPatternProgression (A : L18_4Ambient)
    (line : DirichletLZerosOnLine)
    (hV12 : ∀ n, 12 ≤ denomScale A.W n)
    (hK6 : ∀ n, 6 ≤ A.d n * cellMesh A.W n)
    (hNcell : ∀ n, A.Ncell n =
      (canonicalCellData (W := A.W) (d := A.d) A.d_pos hV12 hK6).Ncell n)
    (supplyFit : CellSupplyFit A.W A.d (cellK0OfLine line))
    (D : NumeratorData A.W A.ell A.rho A.Nnum)
    (hprog : PrimePatternProgressionBound) (hKge : patternK hprog ≤ D.mass.K) :
    L18_4CellFinish :=
  ofCanonicalAndNumerator A line hV12 hK6 hNcell supplyFit
    (NumeratorFinish.ofPatternProgression D hprog hKge)

/-- **The canonical constructor from the critical line alone.**  The cell supply
is `cellK0OfLine`, the cell is the canonical shrunken cell, and the numerator
deviation is the prime-pattern progression bound supplied by the critical line
(`patternProgression_of_critical_line`).  The remaining explicit inputs are the
pointwise fit, the `MassErrorInputs` data, the adapter equality and the scalar
comparison `patternK (patternProgression_of_critical_line line) ≤ mass.K`. -/
noncomputable def ofCanonicalAndCriticalLine (A : L18_4Ambient)
    (line : DirichletLZerosOnLine)
    (hV12 : ∀ n, 12 ≤ denomScale A.W n)
    (hK6 : ∀ n, 6 ≤ A.d n * cellMesh A.W n)
    (hNcell : ∀ n, A.Ncell n =
      (canonicalCellData (W := A.W) (d := A.d) A.d_pos hV12 hK6).Ncell n)
    (supplyFit : CellSupplyFit A.W A.d (cellK0OfLine line))
    (D : NumeratorData A.W A.ell A.rho A.Nnum)
    (hKge :
      patternK (patternProgression_of_critical_line line) ≤ D.mass.K) :
    L18_4CellFinish :=
  ofCanonicalAndPatternProgression A line hV12 hK6 hNcell supplyFit D
    (patternProgression_of_critical_line line) hKge

/-! ## Axiom audit -/

#print axioms PrimeBinSupply
#print axioms cellSupply_of_supply
#print axioms primeBinSupply_of_critical_line
#print axioms cellSupply_of_critical_line
#print axioms CellCountFinish.cell_prime_count
#print axioms CellCountFinish.Ncell_eq_primeBin_card
#print axioms CellCountFinish.cell_count_pos
#print axioms CellCountFinish.cell_count_ne_zero
#print axioms progressionError_nonneg
#print axioms progressionError_pos
#print axioms progressionError_mono
#print axioms exists_patternDeviation
#print axioms patternK_nonneg
#print axioms patternK_deviation
#print axioms deviation_at_of_patternProgression
#print axioms NumeratorFinish.numerator_count
#print axioms NumeratorFinish.progression_error_le
#print axioms NumeratorFinish.progression_error_nonneg
#print axioms NumeratorFinish.progression_error_pos
#print axioms NumeratorFinish.ofDeviation
#print axioms NumeratorFinish.ofPatternProgression
#print axioms L18_4CellFinish.numeratorData
#print axioms L18_4CellFinish.cell_prime_count
#print axioms L18_4CellFinish.cell_numerator_count
#print axioms L18_4CellFinish.cell_and_numerator_count
#print axioms L18_4CellFinish.cell_count_pos
#print axioms L18_4CellFinish.numerator_error_nonneg
#print axioms L18_4CellFinish.numerator_error_le
#print axioms L18_4CellFinish.toInputs
#print axioms L18_4CellFinish.toInputs_subexpLoss
#print axioms L18_4CellFinish.toSubexpLeaf
#print axioms L18_4CellFinish.toCertificate
#print axioms L18_4CellFinish.toCertificate_subexpLoss
#print axioms cellK0OfLine_nonneg
#print axioms cellK0OfLine_supply
#print axioms ofCanonicalAndNumerator
#print axioms ofCanonicalAndPatternProgression
#print axioms ofCanonicalAndCriticalLine
#print axioms eventually_cellSupplyFit_of_exp_dominated

end Cogentic.RandomizedL18_4
