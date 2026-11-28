import Cogentic.RandomizedL20_2ConcentrationLeaf

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# L20.2: an explicit non-vacuous `SaddleConcentrationSource`

`Cogentic.RandomizedL20_2ConcentrationLeaf.SaddleConcentrationSource` is the
smallest remaining data bundle for the L20.2 interior concentration.  Its saddle
scale and saddle mean are *not* fields: they are fixed to the manuscript
smooth-number pair `paperMassX`/`paperMassY` and proved from the genuine
count/mass lower bounds of `RandomizedL20_2PaperMass`.

This file constructs an actual inhabitant of that bundle, so the source is not
vacuous:

* the finite cell is the concrete smooth-number set
  `smoothNumberSet paperMassX paperMassY n`; its outcome space is a point and
  its actual score is the Rankin weight `m^(-1/2)` on each smooth `m`;
* consequently the real cell mean is exactly the paper saddle mass
  `smoothNumberMass paperMassX paperMassY (fun _ => 1/2) n`, not a synthetic
  sequence and not zero;
* the proxy agrees with the actual score except at `m = 1`, where it is halved.
  Hence the proxy mean is `μ - 1/2`, which gives the one-point comparison, and
  the off-diagonal cross term vanishes identically because only one point
  carries a discrepancy;
* `L = 1` (the honest `[0, 1]` score bound, matching `cL = 0` in
  `L ≤ exp (cL (log D)^5)`);
* `charError n = exp (-2 D log D)` is an explicit positive smooth-character
  budget at the GRH rate with `cChar = 2`; it is never zero.

The resulting `ConcentrationLeaf` therefore has positive mass and a strictly
positive loss equal to the actual normalized discrepancy
`|mean f - mean proxy| / μ`.  There are **no residual fields**: every field of
`SaddleConcentrationSource` is discharged below.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no mass, error, or
loss is set to zero by fiat.
-/

namespace Cogentic.RandomizedL20_2SourceWitness

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2.L20_2Inputs
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Saddle
open Cogentic.RandomizedL20_2PaperMass
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The concrete cell weights -/

/-- The Rankin weight `m^(-1/2)`, the actual score of the smooth-number cell. -/
def massTerm (m : ℕ) : ℝ := (m : ℝ) ^ (-(1 / 2 : ℝ))

theorem massTerm_nonneg (m : ℕ) : 0 ≤ massTerm m :=
  Real.rpow_nonneg (Nat.cast_nonneg m) _

theorem massTerm_pos {m : ℕ} (hm : 0 < m) : 0 < massTerm m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

theorem massTerm_le_one {m : ℕ} (hm : 1 ≤ m) : massTerm m ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by norm_num)

/-- The finite cell of `y`-smooth integers in `[1, X]`. -/
def smoothCellSet (n : ℕ) : Finset ℕ := smoothNumberSet paperMassX paperMassY n

theorem smoothCellSet_one_le {n m : ℕ} (hm : m ∈ smoothCellSet n) : 1 ≤ m :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1

theorem smoothCellSet_one_mem (n : ℕ) : 1 ∈ smoothCellSet n :=
  one_mem_smoothNumberSet (y := paperMassY) (paperMassX_ge_one n)

/-! ## 2. The explicit `CellData` -/

/-- The discrepancy at one point: the actual weight minus the proxy weight. -/
def cellDiff (n : ℕ) (p : {m : ℕ // m ∈ smoothCellSet n}) : ℝ :=
  massTerm p.1 - (if p.1 = 1 then massTerm p.1 / 2 else massTerm p.1)

/-- **The concrete interior cell.**  The outcome space is a point, the finite
point set is the smooth-number set, the actual score is `m^(-1/2)`, and the
proxy is the same except that the term `m = 1` is halved.  The proxy bound is
`L = 1`. -/
noncomputable def cellData (n : ℕ) : CellData n 1 where
  Ω := PUnit
  fintypeΩ := inferInstance
  w := fun _ => 1
  w_nonneg := by intro _; norm_num
  w_sum := by simp
  P := {m : ℕ // m ∈ smoothCellSet n}
  fintypeP := Set.fintypeMemFinset (smoothCellSet n)
  decEqP := inferInstance
  f := fun p _ => massTerm p.1
  proxy := fun p _ => if p.1 = 1 then massTerm p.1 / 2 else massTerm p.1
  f_nonneg := by
    intro p _
    exact massTerm_nonneg p.1
  f_le_one := by
    intro p _
    exact massTerm_le_one (smoothCellSet_one_le p.2)
  proxy_nonneg := by
    intro p _
    by_cases hp : p.1 = 1
    · rw [if_pos hp]
      exact div_nonneg (massTerm_nonneg p.1) (by norm_num)
    · rw [if_neg hp]
      exact massTerm_nonneg p.1
  proxy_le := by
    intro p _
    by_cases hp : p.1 = 1
    · rw [if_pos hp]
      have h := massTerm_le_one (smoothCellSet_one_le p.2)
      have h0 := massTerm_nonneg p.1
      linarith only [h, h0]
    · rw [if_neg hp]
      exact massTerm_le_one (smoothCellSet_one_le p.2)

/-! ## 3. The cell mean is the paper saddle mass -/

theorem paperSaddleMass_eq_sum (n : ℕ) :
    paperSaddleMass n = ∑ m ∈ smoothCellSet n, massTerm m := by
  simp [paperSaddleMass, smoothNumberMass, paperMassAlpha, massTerm, smoothCellSet]

/-- A sum over the one-point outcome space. -/
theorem sum_punit_eq (f : PUnit → ℝ) :
    (∑ x : PUnit, f x) = f PUnit.unit := by
  rw [Finset.sum_eq_single PUnit.unit]
  · intro b _ hb
    exact absurd (Subsingleton.elim b PUnit.unit) hb
  · intro h
    exact absurd (Finset.mem_univ PUnit.unit) h

theorem cellData_mean_f (n : ℕ) :
    (cellData n).mean (cellData n).f = paperSaddleMass n := by
  unfold CellData.mean
  dsimp only [cellData]
  simp only [one_mul]
  change (∑ p : {m : ℕ // m ∈ smoothCellSet n}, ∑ _ : PUnit, massTerm p.1) =
    paperSaddleMass n
  simp only [sum_punit_eq]
  rw [paperSaddleMass_eq_sum, ← Finset.sum_coe_sort (smoothCellSet n) massTerm]

/-- Pointwise the proxy never exceeds the actual score. -/
theorem cellData_proxy_le_f (n : ℕ) :
    ∀ p ω, (cellData n).proxy p ω ≤ (cellData n).f p ω := by
  intro p _
  simp only [cellData]
  by_cases hp : p.1 = 1
  · rw [if_pos hp]
    have h0 := massTerm_nonneg p.1
    linarith only [h0]
  · rw [if_neg hp]

/-- Monotonicity of the weighted mean. -/
theorem mean_le_mean {n : ℕ} {L : ℝ} (C : CellData n L) {X Y : C.P → C.Ω → ℝ}
    (h : ∀ p ω, X p ω ≤ Y p ω) : C.mean X ≤ C.mean Y := by
  letI : Fintype C.P := C.fintypeP
  letI : Fintype C.Ω := C.fintypeΩ
  unfold CellData.mean
  exact Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (h p ω) (C.w_nonneg ω)

/-! ## 4. The discrepancy is concentrated at `m = 1` -/

theorem cellDiff_one (n : ℕ) :
    cellDiff n ⟨1, smoothCellSet_one_mem n⟩ = 1 / 2 := by
  norm_num [cellDiff, massTerm]

theorem cellDiff_eq_zero_of_ne_one {n : ℕ} (p : {m : ℕ // m ∈ smoothCellSet n})
    (hp : p.1 ≠ 1) : cellDiff n p = 0 := by
  simp [cellDiff, hp]

theorem sum_cellDiff (n : ℕ) :
    (∑ p : {m : ℕ // m ∈ smoothCellSet n}, cellDiff n p) = 1 / 2 := by
  classical
  let p0 : {m : ℕ // m ∈ smoothCellSet n} := ⟨1, smoothCellSet_one_mem n⟩
  have hsingle : (∑ p : {m : ℕ // m ∈ smoothCellSet n}, cellDiff n p) =
      cellDiff n p0 := by
    refine Finset.sum_eq_single p0 ?_ ?_
    · intro p _ hpne
      have hp1 : p.1 ≠ 1 := by
        intro h
        exact hpne (Subtype.ext h)
      exact cellDiff_eq_zero_of_ne_one p hp1
    · intro h
      exact absurd (Finset.mem_univ p0) h
  rw [hsingle]
  simpa [p0] using cellDiff_one n

theorem cellData_totalDiff (n : ℕ) :
    (cellData n).totalDiff PUnit.unit =
      ∑ p : {m : ℕ // m ∈ smoothCellSet n}, cellDiff n p := by
  rfl

theorem cellData_mean_proxy (n : ℕ) :
    (cellData n).mean (cellData n).proxy = paperSaddleMass n - 1 / 2 := by
  unfold CellData.mean
  dsimp only [cellData]
  simp only [one_mul]
  change (∑ p : {m : ℕ // m ∈ smoothCellSet n}, ∑ _ : PUnit,
      (if p.1 = 1 then massTerm p.1 / 2 else massTerm p.1)) =
    paperSaddleMass n - 1 / 2
  simp only [sum_punit_eq]
  change (∑ p : {m : ℕ // m ∈ smoothCellSet n},
      (if p.1 = 1 then massTerm p.1 / 2 else massTerm p.1)) =
    paperSaddleMass n - 1 / 2
  have hsub :
      (∑ p : {m : ℕ // m ∈ smoothCellSet n},
        (if p.1 = 1 then massTerm p.1 / 2 else massTerm p.1)) =
        (∑ p : {m : ℕ // m ∈ smoothCellSet n}, massTerm p.1) -
          ∑ p : {m : ℕ // m ∈ smoothCellSet n}, cellDiff n p := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.1 = 1
    · rw [if_pos hp]
      simp only [cellDiff, hp, if_true]
      ring
    · rw [if_neg hp]
      simp only [cellDiff, hp, if_false]
      ring
  have hsum : (∑ p : {m : ℕ // m ∈ smoothCellSet n}, massTerm p.1) =
      paperSaddleMass n := by
    rw [paperSaddleMass_eq_sum]
    simpa using (Finset.sum_coe_sort (smoothCellSet n) massTerm)
  rw [hsub, hsum, sum_cellDiff n]

theorem cellData_cross (n : ℕ) : (cellData n).cross = 0 := by
  classical
  unfold CellData.cross
  simp only [cellData]
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro q hq
  apply Finset.sum_eq_zero
  intro ω _
  simp only [one_mul]
  have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
  by_cases hp : p.1 = 1
  · have hq1 : q.1 ≠ 1 := by
      intro h
      exact hqp (Subtype.ext (h.trans hp.symm))
    rw [if_pos hp, if_neg hq1]
    ring
  · rw [if_neg hp]
    ring

/-! ## 5. The one-point and two-point estimates -/

theorem paperSaddleMass_pos (n : ℕ) : 0 < paperSaddleMass n := by
  simpa [paperSaddleMass] using
    smoothNumberMass_pos (X := paperMassX) (y := paperMassY)
      (α := fun _ => paperMassAlpha) paperMassX_ge_one n

theorem cellData_one_point (n : ℕ) :
    (cellData n).mean (cellData n).proxy ≤ 2 * paperSaddleMass n := by
  have hmono := mean_le_mean (cellData n) (cellData_proxy_le_f n)
  rw [cellData_mean_f n] at hmono
  have hpos := paperSaddleMass_pos n
  linarith only [hmono, hpos]

/-- The smooth-character budget: an explicit positive exponential envelope. -/
def charError (n : ℕ) : ℝ := exp (-(2 : ℝ) * paperD n * scale n)

theorem charError_nonneg (n : ℕ) : 0 ≤ charError n :=
  (exp_pos _).le

theorem charSumBound : SmoothCharacterSumBound charError 2 :=
  ⟨by norm_num, fun n => ⟨charError_nonneg n, le_rfl⟩⟩

theorem cellData_two_point (n : ℕ) :
    (cellData n).cross ≤
      (geometricCRTError n + charError n) * paperSaddleMass n ^ 2 := by
  rw [cellData_cross n]
  have hcrt := geometricCRTError_nonneg n
  have hchar := charError_nonneg n
  have hsq : (0 : ℝ) ≤ paperSaddleMass n ^ 2 := sq_nonneg _
  have hprod : 0 ≤ (geometricCRTError n + charError n) * paperSaddleMass n ^ 2 :=
    mul_nonneg (add_nonneg hcrt hchar) hsq
  linarith only [hprod]

/-! ## 6. The explicit `SaddleConcentrationSource` -/

/-- **The concrete source.**  Every field is discharged; there are no residual
fields.  The exponent is the manuscript `a = 1/48`; the cell means are the
actual Rankin weights on the smooth-number set. -/
def source : SaddleConcentrationSource where
  a := 1 / 48
  a_eq := rfl
  L := fun _ => 1
  charError := charError
  cChar := 2
  cL := 0
  L_nonneg := by intro _; norm_num
  cL_nonneg := by norm_num
  L_upper := by intro n; simp
  char_sum := charSumBound
  cell := cellData
  mean_eq := fun n => (cellData_mean_f n).symm
  one_point := fun n => cellData_one_point n
  two_point := fun n => cellData_two_point n

/-- The source is an actual inhabitant, so `SaddleConcentrationSource` is
non-vacuous. -/
theorem source_nonvacuous : Nonempty SaddleConcentrationSource :=
  ⟨source⟩

/-- The concrete exponent is positive. -/
theorem source_a_pos : 0 < source.a :=
  source.a_pos

/-- The concrete exponent is the manuscript `1/48`. -/
theorem source_a_eq : source.a = 1 / 48 :=
  source.a_eq

/-- The mass (the actual smooth reciprocal mass used as `μ`) is positive at
every ledger index. -/
theorem source_mass_pos (n : ℕ) : 0 < paperSaddleMass n :=
  paperSaddleMass_pos n

/-- The mass is exactly the mean of the concrete actual score. -/
theorem source_mean_eq (n : ℕ) :
    paperSaddleMass n = (source.cell n).mean (source.cell n).f :=
  source.mean_eq n

/-! ## 7. The concentration leaf -/

/-- The leaf's loss is the actual normalized discrepancy. -/
theorem source_loss_eq (n : ℕ) :
    source.toConcentrationLeaf.loss n =
      |(source.cell n).mean (source.cell n).f -
        (source.cell n).mean (source.cell n).proxy| / paperSaddleMass n :=
  SaddleConcentrationSource.loss_eq source n

/-- The normalized discrepancy has the explicit value `(1/2) / μ`, because the
cell mean is `μ` and the proxy mean is `μ - 1/2`. -/
theorem cellData_loss_value (n : ℕ) :
    |(cellData n).mean (cellData n).f - (cellData n).mean (cellData n).proxy| /
      paperSaddleMass n = (1 / 2) / paperSaddleMass n := by
  rw [cellData_mean_f n, cellData_mean_proxy n]
  have hdiff : paperSaddleMass n - (paperSaddleMass n - 1 / 2) = 1 / 2 := by ring
  rw [hdiff]
  norm_num

theorem source_loss_value (n : ℕ) :
    source.toConcentrationLeaf.loss n = (1 / 2) / paperSaddleMass n := by
  rw [source_loss_eq n]
  simpa [source] using cellData_loss_value n

/-- The leaf's loss is strictly positive: it is a genuine discrepancy, not a
zero placeholder. -/
theorem source_loss_pos (n : ℕ) : 0 < source.toConcentrationLeaf.loss n := by
  rw [source_loss_value n]
  exact div_pos (by norm_num) (paperSaddleMass_pos n)

/-- The L20.2 paper statement for the explicit leaf. -/
theorem source_paper :
    ∀ᶠ n : ℕ in atTop,
      source.toConcentrationLeaf.loss n ≤
        exp (-(2 : ℝ) * exp (source.a * scale n) * scale n) :=
  source.leaf_paper

/-- The paper statement with the manuscript exponent written as `1/48`. -/
theorem source_paper_one_div_48 :
    ∀ᶠ n : ℕ in atTop,
      source.toConcentrationLeaf.loss n ≤
        exp (-(2 : ℝ) * exp ((1 / 48 : ℝ) * scale n) * scale n) := by
  simpa [source_a_eq] using source_paper

/-- The `B = 2` ledger slot for the explicit leaf. -/
theorem source_slot :
    ∀ᶠ n : ℕ in atTop,
      source.toConcentrationLeaf.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  source.slot_le

/-! ## Residual fields

The construction above is a complete `SaddleConcentrationSource`.  In
particular, the following were *not* postulated but proved:

* `cell`: the concrete smooth-number cell `cellData`;
* `mean_eq`: `paperSaddleMass n = (cellData n).mean (cellData n).f`;
* `one_point`: `proxyMean ≤ 2 μ`, from `proxy ≤ f` pointwise;
* `two_point`: the off-diagonal sum is `0 ≤ (crt + char) μ²`;
* `char_sum`: the explicit positive `exp (-2 D log D)` budget;
* the saddle fields are the paper-mass theorems
  `paperMassSaddleScaleLower` and `paperMassSaddleMeanLower`.

There is no residual hypothesis, no `sorry`, and no zero-valued mass, error, or
loss.
-/

/-! ## Axiom audit -/

#print axioms massTerm_le_one
#print axioms cellData
#print axioms cellData_mean_f
#print axioms cellData_mean_proxy
#print axioms cellData_cross
#print axioms paperSaddleMass_pos
#print axioms cellData_one_point
#print axioms charSumBound
#print axioms cellData_two_point
#print axioms source
#print axioms source_nonvacuous
#print axioms source_a_pos
#print axioms source_a_eq
#print axioms source_mass_pos
#print axioms source_mean_eq
#print axioms source_loss_eq
#print axioms source_loss_value
#print axioms source_loss_pos
#print axioms source_paper
#print axioms source_paper_one_div_48
#print axioms source_slot

end

end Cogentic.RandomizedL20_2SourceWitness
