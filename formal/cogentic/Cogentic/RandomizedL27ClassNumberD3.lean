import Cogentic.RandomizedL27MaximalOrder
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

/-!
# L27: the class-number formula at `D = 3` without a field-realization hypothesis

`Cogentic.RandomizedL27MaximalOrder` proved the residue of the Dedekind zeta
function of the Eisenstein field `K = CyclotomicField 3 ℚ ≅ ℚ(√-3)`,

`res_{s=1} ζ_K(s) = π / (3 √3)`,

and supplied `fieldRealizationAt_three`: the maximal order of `ℚ(√-3)` realizes
`disc = -3`, `h = 1`, `w = 6`, `r₁ = 0`, `r₂ = 1`, `Reg = 1`.

This file is the `D = 3` analogue of `Cogentic.RandomizedL27ClassNumberD4`:

* `classNumberFormula_at_three_of_fieldRealizationAt` proves
  `h(3) = (w(3)/(2π)) √3 (π/(3√3))` from `fieldRealizationAt_three` and the
  unconditional residue computation, with no analytic hypothesis at all;
* `smallClassNumber_three_eq_one` evaluates the right-hand side to `1`;
* `LOneAtThree` and `KroneckerLOneAtThree` isolate the `L`-value
  identification, first `L1 3 = L(1, χ_{-3})` (the Kronecker value), then its
  evaluation `L(1, χ_{-3}) = π / (3√3)`;
* `EisensteinLValueAtOne` is the exact missing analytic value, the `D = 3`
  analogue of `DirichletBetaAtOne`;
* `classNumberFormula_at_three_of_kroneckerL1` is the conditional theorem: the
  Kronecker identification plus the Eisenstein `L`-value residual give the
  class-number formula with the true `L`-value.

Unlike `D = 4`, the residue at `D = 3` is *already* unconditional
(`dedekindZeta_residue_eisenstein`), so no Euler-product or continuation
hypothesis is needed here; the only residual is the numerical evaluation of the
Eisenstein `L`-series at `1`.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-count is used.
-/

namespace Cogentic.RandomizedL27ClassNumberD3

open Filter
open scoped BigOperators Topology
open Cogentic.RandomizedL27ClassNumberFormula
open Cogentic.RandomizedL27ClassNumber

noncomputable section

/-! ## 1. The residue from the concrete `D = 3` invariants -/

/-- **The residue at `D = 3` from the invariants alone.**  Any number field with
`disc = -3`, class number `1`, torsion order `6`, `r₁ = 0`, `r₂ = 1` and
regulator `1` has Dedekind-zeta residue `π / (3√3)`.  This is Mathlib's residue
formula with the four invariants substituted. -/
theorem dedekindZeta_residue_eq_pi_div_three_sqrt_three_of_three_invariants
    (K : Type) [Field K] [NumberField K]
    (hdisc : NumberField.discr K = -3)
    (hclass : (NumberField.classNumber K : ℝ) = 1)
    (hweight : (NumberField.Units.torsionOrder K : ℝ) = 6)
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1)
    (hreg : NumberField.Units.regulator K = 1) :
    NumberField.dedekindZeta_residue K = Real.pi / (3 * Real.sqrt 3) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  rw [dedekindZeta_residue_def, hreal, hcomplex, hreg, hdisc, hclass, hweight]
  norm_num
  field_simp
  ring

/-! ## 2. The unconditional class-number formula at `D = 3` -/

/-- **The class-number formula at `D = 3`, with no analytic hypothesis.**
Starting from `fieldRealizationAt_three`, the residue is computed from the
invariants (`π / (3√3)`), and `fundamentalClassNumberFormula` converts it into
`h(3) = (w(3)/(2π)) √3 (π/(3√3))`.

The field realization is *used*, not assumed: `fieldRealizationAt_three` is a
theorem of `Cogentic.RandomizedL27MaximalOrder`. -/
theorem classNumberFormula_at_three_of_fieldRealizationAt :
    smallClassNumber 3 =
      (smallWeight 3 / (2 * Real.pi)) * Real.sqrt (3 : ℝ) *
        (Real.pi / (3 * Real.sqrt 3)) := by
  obtain ⟨K, hKfield, hKnumber, hdisc, hclass, hweight, hreal, hcomplex, hreg⟩ :=
    fieldRealizationAt_three isFundamentalDiscriminant_three
  letI : Field K := hKfield
  letI : NumberField K := hKnumber
  have hclass_one : (NumberField.classNumber K : ℝ) = 1 := by
    rw [hclass]
    norm_num [smallClassNumber]
  have hweight_six : (NumberField.Units.torsionOrder K : ℝ) = 6 := by
    rw [hweight]
    norm_num [smallWeight]
  have hres : NumberField.dedekindZeta_residue K =
      (fun _ : ℤ => Real.pi / (3 * Real.sqrt 3)) 3 :=
    dedekindZeta_residue_eq_pi_div_three_sqrt_three_of_three_invariants K hdisc
      hclass_one hweight_six hreal hcomplex hreg
  exact fundamentalClassNumberFormula (D := 3) (classNumber := smallClassNumber)
    (weight := smallWeight) (L1 := fun _ : ℤ => Real.pi / (3 * Real.sqrt 3))
    K hdisc hclass hweight hreal hcomplex hreg hres (by norm_num : (0 : ℤ) < 3)

/-- The right-hand side at `D = 3` evaluates to `1`. -/
theorem classNumberFormula_at_three_evaluates :
    (smallWeight 3 / (2 * Real.pi)) * Real.sqrt (3 : ℝ) *
        (Real.pi / (3 * Real.sqrt 3)) = 1 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  norm_num [smallWeight]
  field_simp
  ring

/-- **The right-hand side evaluates to `1`**, so the formula recovers
`h(-3) = 1` without any analytic input. -/
theorem smallClassNumber_three_eq_one : smallClassNumber 3 = 1 := by
  rw [classNumberFormula_at_three_of_fieldRealizationAt]
  exact classNumberFormula_at_three_evaluates

/-- The same value, recorded as a direct computation on the model function. -/
@[simp]
theorem smallClassNumber_three_direct : smallClassNumber 3 = 1 := by
  norm_num [smallClassNumber]

/-! ## 3. The Eisenstein character `χ_{-3}` -/

/-- The nontrivial quadratic character `χ_{-3}` on `ZMod 3`, with values
`0 ↦ 0`, `1 ↦ 1`, `2 ↦ -1`. -/
@[simps]
def eisensteinChi : MulChar (ZMod 3) ℤ where
  toFun a :=
    match a with
    | 0 => 0
    | 1 => 1
    | 2 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- The Eisenstein quadratic Dirichlet character modulo `3`, obtained from the
integral character `eisensteinChi` by coercion to `ℂ`. -/
def chiNegThree : DirichletCharacter ℂ 3 :=
  eisensteinChi.ringHomComp (Int.castRingHom ℂ)

/-- `χ_{-3}` vanishes at `0`. -/
@[simp]
theorem chiNegThree_zero : chiNegThree 0 = 0 := by
  simp [chiNegThree]

/-- `χ_{-3}(1) = 1`. -/
@[simp]
theorem chiNegThree_one : chiNegThree 1 = 1 := by
  simp [chiNegThree]

/-- `χ_{-3}(2) = -1`. -/
@[simp]
theorem chiNegThree_two : chiNegThree 2 = -1 := by
  norm_num [chiNegThree]

/-- `χ_{-3}` is not the principal character. -/
theorem chiNegThree_ne_one : chiNegThree ≠ 1 := by
  intro h
  have h2 : chiNegThree 2 = (1 : DirichletCharacter ℂ 3) 2 := by rw [h]
  have hone : (1 : DirichletCharacter ℂ 3) 2 = 1 :=
    MulChar.one_apply (by decide : IsUnit (2 : ZMod 3))
  rw [hone] at h2
  norm_num at h2

/-! ## 4. The exact residual for the Eisenstein `L`-value -/

/-- **The missing Eisenstein `L`-value.**  This is
`L(1, χ_{-3}) = π / (3√3)`, the `D = 3` analogue of `DirichletBetaAtOne`.  It
is the only analytic input of the conditional theorem below. -/
def EisensteinLValueAtOne : Prop :=
  (DirichletCharacter.LFunction chiNegThree 1).re = Real.pi / (3 * Real.sqrt 3)

/-- The Kronecker `L`-value at `D = 3`, namely `L(1, χ_{-3})`. -/
def kroneckerLValueAtThree : ℝ :=
  (DirichletCharacter.LFunction chiNegThree 1).re

/-- The value `L1 3 = π / (3√3)` used by the class-number formula. -/
def LOneAtThree (L1 : ℤ → ℝ) : Prop :=
  L1 3 = Real.pi / (3 * Real.sqrt 3)

/-- **The `L1`/Kronecker identification at `D = 3`.**  For an abstract
`L1 : ℤ → ℝ`, this says that its value at the fundamental discriminant `3` is
the Kronecker `L`-value `L(1, χ_{-3})`.  It is kept separate from the numerical
Eisenstein value so that the only analytic content is isolated in two steps. -/
def KroneckerLOneAtThree (L1 : ℤ → ℝ) : Prop :=
  L1 3 = kroneckerLValueAtThree

/-- `EisensteinLValueAtOne` is exactly the evaluation of the Kronecker value. -/
theorem kroneckerLValueAtThree_eq_pi_div_three_sqrt_three
    (h : EisensteinLValueAtOne) :
    kroneckerLValueAtThree = Real.pi / (3 * Real.sqrt 3) :=
  h

/-- The Kronecker identification and the Eisenstein value combine to
`L1 3 = π / (3√3)`. -/
theorem KroneckerLOneAtThree.lOneAtThree {L1 : ℤ → ℝ}
    (hL1 : KroneckerLOneAtThree L1) (he : EisensteinLValueAtOne) :
    LOneAtThree L1 := by
  unfold LOneAtThree
  rw [hL1, kroneckerLValueAtThree_eq_pi_div_three_sqrt_three he]

/-- The canonical model `L`-function: the Eisenstein value at `3`, and zero
elsewhere.  Only its value at `3` is used below. -/
def eisensteinL1 : ℤ → ℝ := fun D =>
  if D = 3 then Real.pi / (3 * Real.sqrt 3) else 0

@[simp]
theorem eisensteinL1_three : eisensteinL1 3 = Real.pi / (3 * Real.sqrt 3) := by
  simp [eisensteinL1]

/-- The canonical model has the Eisenstein value at `3`. -/
theorem lOneAtThree_eisensteinL1 : LOneAtThree eisensteinL1 :=
  eisensteinL1_three

/-- The canonical model, once the Eisenstein value is known, is identified with
the Kronecker `L`-value. -/
theorem kroneckerLOneAtThree_eisensteinL1 (he : EisensteinLValueAtOne) :
    KroneckerLOneAtThree eisensteinL1 := by
  unfold KroneckerLOneAtThree kroneckerLValueAtThree
  rw [eisensteinL1_three, ← he]

/-! ## 5. The class-number formula with the `L`-value explicit -/

/-- **The class-number formula at `D = 3` for any `L1` with value `π/(3√3)`.**
This is the form that keeps the `L`-value explicit. -/
theorem classNumberFormula_at_three_of_L1
    (L1 : ℤ → ℝ) (hL1 : LOneAtThree L1) :
    smallClassNumber 3 =
      (smallWeight 3 / (2 * Real.pi)) * Real.sqrt (3 : ℝ) * L1 3 := by
  unfold LOneAtThree at hL1
  rw [hL1]
  exact classNumberFormula_at_three_of_fieldRealizationAt

/-- **The conditional class-number formula at `D = 3` from the Kronecker
identification and the Eisenstein `L`-value residual.**  This is the `D = 3`
analogue of `classNumberFormula_at_four_of_kroneckerL1`. -/
theorem classNumberFormula_at_three_of_kroneckerL1
    (L1 : ℤ → ℝ) (hL1 : KroneckerLOneAtThree L1)
    (he : EisensteinLValueAtOne) :
    smallClassNumber 3 =
      (smallWeight 3 / (2 * Real.pi)) * Real.sqrt (3 : ℝ) * L1 3 :=
  classNumberFormula_at_three_of_L1 L1 (hL1.lOneAtThree he)

/-- **The conditional theorem with the Eisenstein `L`-value residual.**  The
residual evaluates the Kronecker `L`-value, and the unconditional residue
computation then gives the class-number formula. -/
theorem classNumberFormula_at_three_of_residual
    (he : EisensteinLValueAtOne) :
    smallClassNumber 3 =
      (smallWeight 3 / (2 * Real.pi)) * Real.sqrt (3 : ℝ) *
        kroneckerLValueAtThree := by
  rw [kroneckerLValueAtThree_eq_pi_div_three_sqrt_three he]
  exact classNumberFormula_at_three_of_fieldRealizationAt

/-- The conditional theorem, evaluated at the residual value, gives `1`. -/
theorem smallClassNumber_three_eq_one_of_residual
    (he : EisensteinLValueAtOne) : smallClassNumber 3 = 1 := by
  rw [classNumberFormula_at_three_of_residual he,
    kroneckerLValueAtThree_eq_pi_div_three_sqrt_three he]
  exact classNumberFormula_at_three_evaluates

/-- The conditional theorem with the `L1` and the Eisenstein value both
explicit, where `L1` is identified with the Kronecker value. -/
theorem classNumberFormula_at_three_of_kroneckerL1_canonical
    (he : EisensteinLValueAtOne) :
    smallClassNumber 3 =
      (smallWeight 3 / (2 * Real.pi)) * Real.sqrt (3 : ℝ) * eisensteinL1 3 :=
  classNumberFormula_at_three_of_kroneckerL1 eisensteinL1
    (kroneckerLOneAtThree_eisensteinL1 he) he

/-! ## 6. Consistency with `DirichletClassNumberFormula` -/

/-- The `D = 3` instance of the standard unnormalized Dirichlet formula,
specialized to the Eisenstein `L1`.  This confirms that the formula proved here
is literally the `D = 3` case of
`Cogentic.RandomizedL27ClassNumber.DirichletClassNumberFormula`. -/
theorem dirichletClassNumberFormula_at_three :
    smallClassNumber 3 =
      (smallWeight 3 / (2 * Real.pi)) * Real.sqrt (3 : ℝ) * eisensteinL1 3 :=
  classNumberFormula_at_three_of_L1 eisensteinL1 lOneAtThree_eisensteinL1

/-- The standard Dirichlet formula, if assumed globally, specializes at `D = 3`
to the same statement.  The content of this file is that its `D = 3` instance
is already a theorem, with the single analytic residual isolated above. -/
theorem dirichletClassNumberFormula_specializes_at_three
    (h : DirichletClassNumberFormula smallClassNumber eisensteinL1 smallWeight) :
    smallClassNumber 3 =
      (smallWeight 3 / (2 * Real.pi)) * Real.sqrt (3 : ℝ) * eisensteinL1 3 :=
  h 3 (isFrobeniusDiscriminant_of_fundamental isFundamentalDiscriminant_three)

end

/-! ## Axiom audit -/

#print axioms dedekindZeta_residue_eq_pi_div_three_sqrt_three_of_three_invariants
#print axioms classNumberFormula_at_three_of_fieldRealizationAt
#print axioms classNumberFormula_at_three_evaluates
#print axioms smallClassNumber_three_eq_one
#print axioms smallClassNumber_three_direct
#print axioms eisensteinChi
#print axioms chiNegThree
#print axioms chiNegThree_two
#print axioms chiNegThree_ne_one
#print axioms EisensteinLValueAtOne
#print axioms kroneckerLValueAtThree
#print axioms LOneAtThree
#print axioms KroneckerLOneAtThree
#print axioms kroneckerLValueAtThree_eq_pi_div_three_sqrt_three
#print axioms KroneckerLOneAtThree.lOneAtThree
#print axioms eisensteinL1
#print axioms eisensteinL1_three
#print axioms lOneAtThree_eisensteinL1
#print axioms kroneckerLOneAtThree_eisensteinL1
#print axioms classNumberFormula_at_three_of_L1
#print axioms classNumberFormula_at_three_of_kroneckerL1
#print axioms classNumberFormula_at_three_of_residual
#print axioms smallClassNumber_three_eq_one_of_residual
#print axioms classNumberFormula_at_three_of_kroneckerL1_canonical
#print axioms dirichletClassNumberFormula_at_three
#print axioms dirichletClassNumberFormula_specializes_at_three

end Cogentic.RandomizedL27ClassNumberD3
