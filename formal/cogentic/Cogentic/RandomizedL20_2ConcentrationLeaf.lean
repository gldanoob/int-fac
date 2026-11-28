import Cogentic.RandomizedL20_2PaperMass
import Cogentic.RandomizedL20_2PaperSmooth
import Cogentic.RandomizedL20_2Sub

set_option linter.style.haveILetI false

/-!
# L20.2: the paper-mass `ConcentrationLeaf`

`Cogentic.RandomizedL20_2PaperMass` proves the two saddle-point lower bounds for
the *actual* manuscript smooth-number pair

* `paperMassX n = exp (max 16 (D log D))`, `paperMassY n = paperMassX n^(3/4)`,
* `SaddlePointScaleLower (smoothSaddleScale paperMassX paperMassY) paperMassCount`
  (from the smooth-number count `#smooth ≥ exp ((1/2) D log D)`),
* `SaddlePointMeanLower (smoothNumberMass paperMassX paperMassY (fun _ => 1/2))
  (smoothSaddleScale paperMassX paperMassY) paperMassEta`
  (from the smooth reciprocal-mass lower bound).

This file feeds those genuine saddle bounds into the L20.2 concentration
machinery of `Cogentic.RandomizedL20_2` and produces a `ConcentrationLeaf`:

* `SaddleConcentrationSource` is the smallest remaining data bundle.  It keeps
  only the finite-cell concentration inputs (the actual cell, the one-point
  comparison, the two-point estimate, the GRH smooth-character budget, and the
  proxy bound).  The saddle scale and saddle mean are *not* fields: they are
  fixed to the paper-mass pair and proved from the existing count and mass
  bounds.  The truncated geometric CRT tail is also not a field: it is the
  proved `RandomizedL20_2Sub.geometricCRTError`.
* `SaddleConcentrationSource.toConcentrationLeaf` builds the leaf.  Its `loss`
  is the actual normalized discrepancy
  `|mean f - mean proxy| / smoothNumberMass`, never zero by fiat.
* `SaddleConcentrationSource.paper_bound` is the manuscript statement
  `loss n ≤ exp (-2 exp (a log D) log D)` with `a = 1/48`.
* `PaperExponentSaddleInequality` isolates the explicit scalar saddle
  inequality that the paper exponent consumes, and
  `paperExponentSaddleInequality` proves it outright (it is *not* an axiom).
* `SaddleConcentrationSource.toPaperLeaf` replaces the `l20_2` field of a
  `PaperAnalyticAssumptions` bundle, and `toPaperLeaf_slot` shows that the
  resulting leaf still feeds the C5 ledger through the paper endpoint.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and the loss is never
set to zero.
-/

namespace Cogentic.RandomizedL20_2ConcentrationLeaf

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2.L20_2Inputs
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Saddle
open Cogentic.RandomizedL20_2PaperMass
open Cogentic.RandomizedL20_2PaperSmooth
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The paper-mass saddle pair -/

/-- The saddle scale of the manuscript smooth-number pair,
`Λ n = log #(paperMassY n)-smooth integers up to paperMassX n`. -/
def paperSaddleScale (n : ℕ) : ℝ := smoothSaddleScale paperMassX paperMassY n

/-- The saddle mean of the manuscript smooth-number pair, the actual reciprocal
mass `∑ m^(-1/2)` over the `paperMassY n`-smooth integers. -/
def paperSaddleMass (n : ℕ) : ℝ :=
  smoothNumberMass paperMassX paperMassY (fun _ => paperMassAlpha) n

/-- The paper-mass pair satisfies the saddle-point scale lower bound, inherited
from the smooth-number count. -/
theorem paperSaddleScaleLower :
    SaddlePointScaleLower paperSaddleScale paperMassCount :=
  paperMassSaddleScaleLower

/-- The paper-mass pair satisfies the saddle-point mean lower bound, inherited
from the smooth reciprocal mass. -/
theorem paperSaddleMeanLower :
    SaddlePointMeanLower paperSaddleMass paperSaddleScale paperMassEta :=
  paperMassSaddleMeanLower

/-- The alternative self-smooth paper pair of
`Cogentic.RandomizedL20_2PaperSmooth` also realizes both saddle lower bounds.
This records that the saddle reduction is not tied to one particular paper pair. -/
theorem paperSmooth_saddle_fields :
    SaddlePointScaleLower (smoothSaddleScale paperSmoothX paperSmoothY) (1 / 2) ∧
      SaddlePointMeanLower
        (smoothNumberMass paperSmoothX paperSmoothY (fun _ => (1 / 2 : ℝ)))
        (smoothSaddleScale paperSmoothX paperSmoothY) (1 / 2) :=
  ⟨paperSmoothSaddleScaleLower, paperSmoothSaddleMeanLower⟩

/-! ## 2. The explicit saddle inequality for the paper exponent -/

/-- **The explicit scalar saddle inequality consumed by the paper exponent.**
The concentration rate `exp (-2 A log D)` with `A = exp (a log D)` needs two
comparisons between the polynomial proxy/exponent budget and the saddle scale:

* the diagonal budget
  `log 3 + cL (log D)^5 + log 2 + 4 A log D ≤ η cLam D log D`;
* the off-diagonal budget
  `2 log 2 + 4 A log D ≤ min cCRT cChar · D log D`.

These are the *smallest* explicit saddle comparisons: everything else in the
G.10 proof is finite-cell algebra.  The next theorem proves them from `a < 1`
and the positivity of the saddle constants, so this `Prop` is discharged, not
assumed. -/
def PaperExponentSaddleInequality (a cL η cLam cCRT cChar : ℝ) : Prop :=
  (∀ᶠ n : ℕ in atTop,
    Real.log 3 + cL * (scale n) ^ 5 + Real.log 2 +
      4 * exp (a * scale n) * scale n ≤
      η * cLam * (paperD n * scale n)) ∧
  (∀ᶠ n : ℕ in atTop,
    2 * Real.log 2 + 4 * exp (a * scale n) * scale n ≤
      min cCRT cChar * (paperD n * scale n))

/-- The diagonal saddle budget: the polynomial proxy factor and the interior
level `A = exp (a log D)` are absorbed by the saddle mean.  This is the
`a < 1` scalar comparison behind `eventually_diagonal_budget`. -/
theorem eventually_diagonal_budget_of_lt_one {a cL η cLam : ℝ}
    (ha : a < 1) (hcL : 0 ≤ cL) (hη : 0 < η) (hc : 0 < cLam) :
    ∀ᶠ n : ℕ in atTop,
      Real.log 3 + cL * (scale n) ^ 5 + Real.log 2 +
        4 * exp (a * scale n) * scale n ≤
        η * cLam * (paperD n * scale n) := by
  have hK : 0 < η * cLam := mul_pos hη hc
  have hK4 : 0 < η * cLam / 4 := by positivity
  have hconst : ∀ᶠ n : ℕ in atTop,
      Real.log 3 + Real.log 2 ≤
        (η * cLam / 4) * (paperD n * scale n) :=
    eventually_const_le_exp_mul (c := Real.log 3 + Real.log 2) hK4
  have hpow : ∀ᶠ n : ℕ in atTop,
      cL * (scale n) ^ 5 ≤
        (η * cLam / 4) * (paperD n * scale n) := by
    rcases eq_or_lt_of_le hcL with hcL0 | hcLpos
    · filter_upwards [scale_grows.eventually_ge_atTop 0] with n hs
      rw [← hcL0, zero_mul]
      exact mul_nonneg (by positivity) (mul_nonneg (paperD_pos n).le hs)
    · have hε : 0 < (η * cLam) / (4 * cL) := div_pos hK (by positivity)
      have hsmall := eventually_pow_le_const_mul_exp (k := 4) (c := 1)
        zero_lt_one hε
      filter_upwards [hsmall, scale_grows.eventually_ge_atTop 1] with n hn hs
      have hpow5 : (scale n) ^ 5 = (scale n) ^ 4 * scale n := by ring
      have hmul : (scale n) ^ 4 * scale n ≤
          ((η * cLam) / (4 * cL)) * exp (1 * scale n) * scale n :=
        mul_le_mul_of_nonneg_right (by simpa using hn) (by linarith only [hs])
      have hfac : cL * (((η * cLam) / (4 * cL)) *
          exp (1 * scale n) * scale n) =
          (η * cLam / 4) * (exp (1 * scale n) * scale n) := by
        field_simp [hcLpos.ne']
      have hrew : paperD n * scale n = exp (1 * scale n) * scale n := by
        unfold paperD
        ring_nf
      calc
        cL * (scale n) ^ 5 = cL * ((scale n) ^ 4 * scale n) := by rw [hpow5]
        _ ≤ cL * (((η * cLam) / (4 * cL)) *
              exp (1 * scale n) * scale n) :=
          mul_le_mul_of_nonneg_left hmul hcL
        _ = (η * cLam / 4) * (exp (1 * scale n) * scale n) := hfac
        _ = (η * cLam / 4) * (paperD n * scale n) := by rw [hrew]
  have hA : ∀ᶠ n : ℕ in atTop,
      4 * exp (a * scale n) * scale n ≤
        (η * cLam / 4) * (paperD n * scale n) := by
    have hsmall := eventually_exp_mul_le_exp_mul (a := a) ha
      (c := (η * cLam) / 16) (by positivity)
    filter_upwards [hsmall] with n hn
    calc
      4 * exp (a * scale n) * scale n =
          4 * (exp (a * scale n) * scale n) := by ring
      _ ≤ 4 * (((η * cLam) / 16) * (paperD n * scale n)) :=
        mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = (η * cLam / 4) * (paperD n * scale n) := by ring
  filter_upwards [hconst, hpow, hA, scale_grows.eventually_ge_atTop 0]
    with n hc' hp hA' hs
  have hsum : Real.log 3 + Real.log 2 + cL * (scale n) ^ 5 +
      4 * exp (a * scale n) * scale n ≤
      3 * ((η * cLam / 4) * (paperD n * scale n)) := by
    linarith only [hc', hp, hA']
  have hnonneg : 0 ≤ (η * cLam / 4) * (paperD n * scale n) :=
    mul_nonneg (by positivity) (mul_nonneg (paperD_pos n).le hs)
  nlinarith only [hsum, hnonneg, hK]

/-- The off-diagonal saddle budget: the CRT and smooth-character errors absorb
the interior level `A = exp (a log D)`. -/
theorem eventually_offdiagonal_budget_of_lt_one {a cCRT cChar : ℝ}
    (ha : a < 1) (hcrt : 0 < cCRT) (hchar : 0 < cChar) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.log 2 + 4 * exp (a * scale n) * scale n ≤
        min cCRT cChar * (paperD n * scale n) := by
  have hcpos : 0 < min cCRT cChar := lt_min hcrt hchar
  have hhalf : 0 < min cCRT cChar / 2 := by positivity
  have hconst : ∀ᶠ n : ℕ in atTop,
      2 * Real.log 2 ≤ (min cCRT cChar / 2) * (paperD n * scale n) :=
    eventually_const_le_exp_mul (c := 2 * Real.log 2) hhalf
  have hA : ∀ᶠ n : ℕ in atTop,
      4 * exp (a * scale n) * scale n ≤
        (min cCRT cChar / 2) * (paperD n * scale n) := by
    have hsmall := eventually_exp_mul_le_exp_mul (a := a) ha
      (c := min cCRT cChar / 8) (by positivity)
    filter_upwards [hsmall] with n hn
    calc
      4 * exp (a * scale n) * scale n =
          4 * (exp (a * scale n) * scale n) := by ring
      _ ≤ 4 * (((min cCRT cChar) / 8) * (paperD n * scale n)) :=
        mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = (min cCRT cChar / 2) * (paperD n * scale n) := by ring
  filter_upwards [hconst, hA] with n hc' hA'
  linarith only [hc', hA']

/-- **The explicit saddle inequality is proved.**  It follows from `a < 1`, the
positivity of the saddle constants `η, cLam`, and the positivity of the CRT and
smooth-character decay constants.  No saddle term is assumed. -/
theorem paperExponentSaddleInequality {a cL η cLam cCRT cChar : ℝ}
    (ha : a < 1) (hcL : 0 ≤ cL) (hη : 0 < η) (hc : 0 < cLam)
    (hcrt : 0 < cCRT) (hchar : 0 < cChar) :
    PaperExponentSaddleInequality a cL η cLam cCRT cChar :=
  ⟨eventually_diagonal_budget_of_lt_one ha hcL hη hc,
    eventually_offdiagonal_budget_of_lt_one ha hcrt hchar⟩

/-! ## 3. The smallest concentration source -/

/-- **The L20.2 concentration source.**  The saddle scale and saddle mean are
not fields: they are the paper-mass pair, whose two lower bounds are proved in
`RandomizedL20_2PaperMass`.  What remains is exactly the finite-cell
concentration data that G.10 consumes:

* the actual weighted cell and its proxy score;
* the identification `mean f = smoothNumberMass` of the ideal mean;
* the one-point comparison (G.8);
* the off-diagonal two-point estimate (G.10);
* the GRH smooth-character budget (the truncated geometric CRT tail is the
  proved `RandomizedL20_2Sub.geometricCRTError`);
* the polynomial proxy bound on `L`.

The `a` field is the manuscript exponent (`a = 1/48`). -/
structure SaddleConcentrationSource where
  /-- The interior exponent `a` in `A = D^a`; the paper has `a = 1/48`. -/
  a : ℝ
  /-- The manuscript value `a = 1/48`. -/
  a_eq : a = 1 / 48
  /-- The proxy score bound `L`. -/
  L : ℕ → ℝ
  /-- The smooth-character error budget. -/
  charError : ℕ → ℝ
  /-- The smooth-character decay constant. -/
  cChar : ℝ
  /-- The polynomial exponent constant in `L ≤ exp (cL (log D)^5)`. -/
  cL : ℝ
  /-- `L` is nonnegative. -/
  L_nonneg : ∀ n, 0 ≤ L n
  /-- The polynomial exponent constant is nonnegative. -/
  cL_nonneg : 0 ≤ cL
  /-- The G.10 proxy bound `L ≤ exp (cL (log D)^5)`. -/
  L_upper : ∀ n, L n ≤ exp (cL * (scale n) ^ 5)
  /-- The GRH smooth-character sum. -/
  char_sum : SmoothCharacterSumBound charError cChar
  /-- The finite interior cell at each ledger index. -/
  cell : ∀ n, CellData n (L n)
  /-- The ideal mean is the actual mean of the cell, and equals the paper-mass
  saddle mean. -/
  mean_eq : ∀ n, paperSaddleMass n = (cell n).mean (cell n).f
  /-- G.8 one-point comparison. -/
  one_point : OnePointProxyComparison
    (fun n => (cell n).mean (cell n).proxy) paperSaddleMass
  /-- G.10 off-diagonal two-point estimate, against the proved geometric CRT
  tail and the GRH smooth-character error. -/
  two_point : TwoPointOffDiagonalBound
    (fun n => (cell n).cross) paperSaddleMass geometricCRTError charError

namespace SaddleConcentrationSource

variable (S : SaddleConcentrationSource)

/-- The source's exponent is positive. -/
theorem a_pos : 0 < S.a := by
  rw [S.a_eq]
  norm_num

/-- The source's exponent is less than one. -/
theorem a_lt_one : S.a < 1 := by
  rw [S.a_eq]
  norm_num

/-- The source's explicit saddle inequality, obtained by discharging
`PaperExponentSaddleInequality` from the paper-mass constants. -/
theorem saddle_inequality :
    PaperExponentSaddleInequality S.a S.cL paperMassEta paperMassCount
      2 S.cChar :=
  paperExponentSaddleInequality S.a_lt_one S.cL_nonneg
    (by norm_num [paperMassEta]) (by norm_num [paperMassCount])
    (by norm_num) S.char_sum.1

/-- The source builds the decomposed `L20_2Inputs`; its saddle fields are the
proved paper-mass bounds. -/
def toInputs : L20_2Inputs where
  a := S.a
  a_eq := S.a_eq
  Λ := paperSaddleScale
  μ := paperSaddleMass
  L := S.L
  crtError := geometricCRTError
  charError := S.charError
  cLam := paperMassCount
  η := paperMassEta
  cCRT := 2
  cChar := S.cChar
  cL := S.cL
  saddle_scale := paperSaddleScaleLower
  saddle_mean := paperSaddleMeanLower
  L_nonneg := S.L_nonneg
  cL_nonneg := S.cL_nonneg
  L_upper := S.L_upper
  crt_law := truncatedGeometricCRTLaw
  char_sum := S.char_sum
  cell := S.cell
  μ_eq := S.mean_eq
  one_point := S.one_point
  two_point := S.two_point

/-- **The concentration leaf built from the paper-mass source.**  Its loss is
the genuine normalized mean discrepancy. -/
def toConcentrationLeaf : ConcentrationLeaf :=
  S.toInputs.toConcentrationLeaf

/-- The leaf's loss is the actual normalized discrepancy against the paper-mass
saddle mean, never a zero placeholder. -/
theorem loss_eq (n : ℕ) :
    S.toConcentrationLeaf.loss n =
      |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| /
        paperSaddleMass n :=
  rfl

/-- The loss is nonnegative. -/
theorem loss_nonneg (n : ℕ) : 0 ≤ S.toConcentrationLeaf.loss n :=
  S.toInputs.loss_nonneg n

/-- **The manuscript concentration statement.**  The loss is at most
`exp (-2 exp (a log D) log D)`, i.e. `D^{-2A}` with `A = D^a` and `D = exp (log D)`.
This is derived from the paper-mass saddle bounds together with the finite-cell
G.8/G.10 estimates. -/
theorem paper_bound :
    ∀ᶠ n : ℕ in atTop,
      S.toConcentrationLeaf.loss n ≤
        exp (-(2 : ℝ) * exp (S.a * scale n) * scale n) := by
  filter_upwards [S.toInputs.loss_le_paper] with n hn
  have hA : S.toInputs.A n = exp (S.a * scale n) := rfl
  rwa [hA] at hn

/-- The `paper` field of the constructed leaf, stated with the leaf's own
exponent (which is the manuscript `1/48`). -/
theorem leaf_paper :
    ∀ᶠ n : ℕ in atTop,
      S.toConcentrationLeaf.loss n ≤
        exp (-(2 : ℝ) * exp (S.toConcentrationLeaf.a * scale n) * scale n) :=
  S.toConcentrationLeaf.paper

/-- The paper statement implies the `B = 2` ledger slot. -/
theorem slot_le :
    ∀ᶠ n : ℕ in atTop,
      S.toConcentrationLeaf.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toConcentrationLeaf.slot

/-- The leaf's exponent is exactly the manuscript `a = 1/48`. -/
theorem leaf_a_eq : S.toConcentrationLeaf.a = 1 / 48 :=
  S.a_eq

/-- Replace the L20.2 field of a `PaperAnalyticAssumptions` bundle by the
paper-mass concentration leaf.  Every other leaf and the epoch family are
untouched. -/
def toPaperLeaf
    {E : ∀ n, 3 ≤ n → Cogentic.RandomizedEpochAssembly.HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) : PaperAnalyticAssumptions E C :=
  L20_2Inputs.replacePaperLeaf P S.toInputs

/-- The replaced bundle's interior-concentration slot is precisely the leaf's
`B = 2` loss bound, so the source feeds the C5 ledger. -/
theorem toPaperLeaf_slot
    {E : ∀ n, 3 ≤ n → Cogentic.RandomizedEpochAssembly.HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) :
    ∀ᶠ n : ℕ in atTop,
      (S.toPaperLeaf P).slots .interiorConcentration n ≤
        exp (-(2 : ℝ) * scale n) :=
  L20_2Inputs.replacePaperLeaf_slot P S.toInputs

/-- The same slot through the generic paper endpoint: the replaced bundle's
`interiorConcentration` slot is a `C5Leaf` slot and satisfies the ledger rate. -/
theorem toPaperLeaf_slot_via_endpoint
    {E : ∀ n, 3 ≤ n → Cogentic.RandomizedEpochAssembly.HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) :
    ∀ᶠ n : ℕ in atTop,
      (S.toPaperLeaf P).slots .interiorConcentration n ≤
        exp (-(2 : ℝ) * scale n) :=
  PaperAnalyticAssumptions.slot_le (S.toPaperLeaf P) .interiorConcentration

end SaddleConcentrationSource

/-! ## Axiom audit -/

#print axioms paperSaddleScaleLower
#print axioms paperSaddleMeanLower
#print axioms paperSmooth_saddle_fields
#print axioms eventually_diagonal_budget_of_lt_one
#print axioms eventually_offdiagonal_budget_of_lt_one
#print axioms paperExponentSaddleInequality
#print axioms SaddleConcentrationSource.a_pos
#print axioms SaddleConcentrationSource.a_lt_one
#print axioms SaddleConcentrationSource.saddle_inequality
#print axioms SaddleConcentrationSource.toInputs
#print axioms SaddleConcentrationSource.toConcentrationLeaf
#print axioms SaddleConcentrationSource.loss_eq
#print axioms SaddleConcentrationSource.loss_nonneg
#print axioms SaddleConcentrationSource.paper_bound
#print axioms SaddleConcentrationSource.leaf_paper
#print axioms SaddleConcentrationSource.slot_le
#print axioms SaddleConcentrationSource.leaf_a_eq
#print axioms SaddleConcentrationSource.toPaperLeaf
#print axioms SaddleConcentrationSource.toPaperLeaf_slot
#print axioms SaddleConcentrationSource.toPaperLeaf_slot_via_endpoint

end

end Cogentic.RandomizedL20_2ConcentrationLeaf
