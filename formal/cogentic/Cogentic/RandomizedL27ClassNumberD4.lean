import Cogentic.RandomizedL27GaussianFactor

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

/-!
# L27: the class-number formula at `D = 4` without a field-realization hypothesis

`Cogentic.RandomizedL27GaussianFactor` proved the Dirichlet class-number
formula at `D = 4` from the Gaussian Euler product `GaussianDedekindZetaEulerProduct`
and the beta value `DirichletBetaAtOne`, but the statement was conditional on
those two analytic inputs.  `Cogentic.RandomizedL27MaximalOrder` supplied the
arithmetic invariants of `ℚ(i)` (`disc = -4`, `h = 1`, `w = 4`, `r₁ = 0`,
`r₂ = 1`, `Reg = 1`) together with the unconditional residue computation
`NumberField.dedekindZeta_residue GaussianCyclotomicField = π / 4`.

This file combines the two in the sharpest form:

* `classNumberFormula_at_four_of_fieldRealizationAt` proves
  `h(4) = (w(4)/(2π)) √4 (π/4)` from `fieldRealizationAt_four` and the
  `D = 4` residue, with no analytic hypothesis at all;
* `smallClassNumber_four_eq_one` evaluates the right-hand side to `1`;
* `LOneAtFour` and `KroneckerLOneAtFour` isolate the `L`-value identification:
  first `L1 4 = L(1, χ_{-4})` (the Kronecker value), then its evaluation
  `L(1, χ_{-4}) = π / 4` via `DirichletBetaAtOne`;
* `classNumberFormula_at_four_of_eulerProduct_of_beta` and the residual
  structure `GaussianAnalyticResidual` restate the conditional theorem with
  exactly the Gaussian Euler product, the continuation, and the beta value as
  hypotheses — in particular **no** `FundamentalOrderRealization` hypothesis;
* `GaussianResidueResidual` records that the residue (and hence the
  class-number formula) uses only the Euler product and the beta value; the
  continuation is needed only for the all-`s` factorization.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-count is used.
-/

namespace Cogentic.RandomizedL27ClassNumberD4

open Filter
open scoped BigOperators Topology
open Cogentic.RandomizedL27ClassNumberFormula
open Cogentic.RandomizedL27ClassNumber
open Cogentic.RandomizedL27GaussianFactor

noncomputable section

/-! ## 1. The residue from the concrete `D = 4` invariants -/

/-- **The residue at `D = 4` from the invariants alone.**  Any number field with
`disc = -4`, class number `1`, torsion order `4`, `r₁ = 0`, `r₂ = 1` and
regulator `1` has Dedekind-zeta residue `π / 4`.  This is Mathlib's residue
formula with the four invariants substituted. -/
theorem dedekindZeta_residue_eq_pi_div_four_of_four_invariants
    (K : Type) [Field K] [NumberField K]
    (hdisc : NumberField.discr K = -4)
    (hclass : (NumberField.classNumber K : ℝ) = 1)
    (hweight : (NumberField.Units.torsionOrder K : ℝ) = 4)
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1)
    (hreg : NumberField.Units.regulator K = 1) :
    NumberField.dedekindZeta_residue K = Real.pi / 4 := by
  rw [dedekindZeta_residue_def, hreal, hcomplex, hreg, hdisc, hclass, hweight]
  norm_num
  field_simp
  norm_num

/-! ## 2. The unconditional class-number formula at `D = 4` -/

/-- **The class-number formula at `D = 4`, with no analytic hypothesis.**
Starting from `fieldRealizationAt_four`, the residue is computed from the
invariants (`π / 4`), and `fundamentalClassNumberFormula` converts it into
`h(4) = (w(4)/(2π)) √4 (π/4)`.

The field realization is *used*, not assumed: `fieldRealizationAt_four` is a
theorem of `Cogentic.RandomizedL27MaximalOrder`. -/
theorem classNumberFormula_at_four_of_fieldRealizationAt :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * (Real.pi / 4) := by
  obtain ⟨K, hKfield, hKnumber, hdisc, hclass, hweight, hreal, hcomplex, hreg⟩ :=
    fieldRealizationAt_four isFundamentalDiscriminant_four
  letI : Field K := hKfield
  letI : NumberField K := hKnumber
  have hclass_one : (NumberField.classNumber K : ℝ) = 1 := by
    rw [hclass]
    norm_num [smallClassNumber]
  have hweight_four : (NumberField.Units.torsionOrder K : ℝ) = 4 := by
    rw [hweight]
    norm_num [smallWeight]
  have hres : NumberField.dedekindZeta_residue K =
      (fun _ : ℤ => Real.pi / 4) 4 :=
    dedekindZeta_residue_eq_pi_div_four_of_four_invariants K hdisc hclass_one
      hweight_four hreal hcomplex hreg
  exact fundamentalClassNumberFormula (D := 4) (classNumber := smallClassNumber)
    (weight := smallWeight) (L1 := fun _ : ℤ => Real.pi / 4)
    K hdisc hclass hweight hreal hcomplex hreg hres (by norm_num : (0 : ℤ) < 4)

/-- **The right-hand side evaluates to `1`**, so the formula recovers
`h(-4) = 1` without any analytic input. -/
theorem smallClassNumber_four_eq_one : smallClassNumber 4 = 1 := by
  rw [classNumberFormula_at_four_of_fieldRealizationAt]
  exact classNumberFormula_at_four_evaluates

/-- The same value, recorded as a direct computation on the model function. -/
@[simp]
theorem smallClassNumber_four_direct : smallClassNumber 4 = 1 := by
  norm_num [smallClassNumber]

/-! ## 3. Isolating the Kronecker `L`-value -/

/-- The value `L1 4 = π / 4` used by the class-number formula. -/
def LOneAtFour (L1 : ℤ → ℝ) : Prop :=
  L1 4 = Real.pi / 4

/-- **The Kronecker/Dirichlet `L`-value at `D = 4`**, namely
`L(1, χ_{-4})`.  This is the analytic quantity to which the model function
`L1` must be matched; the beta value `DirichletBetaAtOne` evaluates it. -/
def kroneckerLValueAtFour : ℝ :=
  (DirichletCharacter.LFunction chiNegFour 1).re

/-- **The `L1`/Kronecker identification at `D = 4`.**  For an abstract
`L1 : ℤ → ℝ`, this says that its value at the fundamental discriminant `4` is
the Kronecker `L`-value `L(1, χ_{-4})`.  It is kept separate from the beta value
so that the only analytic content is isolated in two steps. -/
def KroneckerLOneAtFour (L1 : ℤ → ℝ) : Prop :=
  L1 4 = kroneckerLValueAtFour

/-- `DirichletBetaAtOne` is exactly the evaluation of the Kronecker value. -/
theorem kroneckerLValueAtFour_eq_pi_div_four (hbeta : DirichletBetaAtOne) :
    kroneckerLValueAtFour = Real.pi / 4 :=
  hbeta

/-- The Kronecker identification and the beta value combine to `L1 4 = π / 4`. -/
theorem KroneckerLOneAtFour.lOneAtFour {L1 : ℤ → ℝ}
    (hL1 : KroneckerLOneAtFour L1) (hbeta : DirichletBetaAtOne) :
    LOneAtFour L1 := by
  unfold LOneAtFour
  rw [hL1, kroneckerLValueAtFour_eq_pi_div_four hbeta]

/-- The canonical model `L`-function: the Gaussian beta value at `4`, and zero
elsewhere.  Only its value at `4` is used below. -/
def gaussianL1 : ℤ → ℝ := fun D => if D = 4 then Real.pi / 4 else 0

@[simp]
theorem gaussianL1_four : gaussianL1 4 = Real.pi / 4 := by
  simp [gaussianL1]

/-- The canonical model has the beta value at `4`. -/
theorem lOneAtFour_gaussianL1 : LOneAtFour gaussianL1 :=
  gaussianL1_four

/-- The canonical model, once the beta value is known, is identified with the
Kronecker `L`-value. -/
theorem kroneckerLOneAtFour_gaussianL1 (hbeta : DirichletBetaAtOne) :
    KroneckerLOneAtFour gaussianL1 := by
  unfold KroneckerLOneAtFour kroneckerLValueAtFour
  rw [gaussianL1_four, ← hbeta]

/-- **The class-number formula at `D = 4` for any `L1` with value `π / 4`.**
This is the form that keeps the `L`-value explicit. -/
theorem classNumberFormula_at_four_of_L1
    (L1 : ℤ → ℝ) (hL1 : LOneAtFour L1) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * L1 4 := by
  unfold LOneAtFour at hL1
  rw [hL1]
  exact classNumberFormula_at_four_of_fieldRealizationAt

/-- **The class-number formula at `D = 4` from the Kronecker identification and
the beta value.** -/
theorem classNumberFormula_at_four_of_kroneckerL1
    (L1 : ℤ → ℝ) (hL1 : KroneckerLOneAtFour L1)
    (hbeta : DirichletBetaAtOne) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * L1 4 :=
  classNumberFormula_at_four_of_L1 L1 (hL1.lOneAtFour hbeta)

/-! ## 4. The conditional theorem with exactly the Gaussian residuals -/

/-- **The conditional residue theorem.**  The Euler product plus the beta value
give the residue `π / 4`; the meromorphic continuation is not needed for the
residue at `1`. -/
theorem residue_gaussian_eq_pi_div_four_of_eulerProduct_of_beta
    (heuler : GaussianDedekindZetaEulerProduct)
    (hbeta : DirichletBetaAtOne) :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = Real.pi / 4 :=
  residue_gaussian_eq_pi_div_four_of_eulerProduct_of_LValue heuler hbeta

/-- **The conditional class-number formula at `D = 4`.**  The only inputs are
the Gaussian Euler product and the beta value; there is no
`FundamentalOrderRealization` hypothesis. -/
theorem classNumberFormula_at_four_of_eulerProduct_of_beta
    (heuler : GaussianDedekindZetaEulerProduct)
    (hbeta : DirichletBetaAtOne) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * (Real.pi / 4) :=
  classNumberFormula_gaussian_of_eulerProduct_of_LValue heuler hbeta

/-- The conditional theorem with `L1` and the beta value explicit. -/
theorem classNumberFormula_at_four_of_eulerProduct_of_beta_of_L1
    (L1 : ℤ → ℝ) (hL1 : LOneAtFour L1)
    (heuler : GaussianDedekindZetaEulerProduct)
    (hbeta : DirichletBetaAtOne) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * L1 4 := by
  unfold LOneAtFour at hL1
  rw [hL1]
  exact classNumberFormula_at_four_of_eulerProduct_of_beta heuler hbeta

/-- The conditional theorem with the Kronecker identification explicit.  The
Euler product and beta value remain the only analytic inputs. -/
theorem classNumberFormula_at_four_of_eulerProduct_of_kroneckerL1
    (L1 : ℤ → ℝ) (hL1 : KroneckerLOneAtFour L1)
    (heuler : GaussianDedekindZetaEulerProduct)
    (hbeta : DirichletBetaAtOne) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * L1 4 := by
  rw [show L1 4 = Real.pi / 4 from (hL1.lOneAtFour hbeta)]
  exact classNumberFormula_at_four_of_eulerProduct_of_beta heuler hbeta

/-- The conditional theorem evaluates to `1`. -/
theorem smallClassNumber_four_eq_one_of_eulerProduct_of_beta
    (heuler : GaussianDedekindZetaEulerProduct)
    (hbeta : DirichletBetaAtOne) :
    smallClassNumber 4 = 1 := by
  rw [classNumberFormula_at_four_of_eulerProduct_of_beta heuler hbeta]
  exact classNumberFormula_at_four_evaluates

/-- **The bundled analytic residual of the Gaussian route.**  It contains
exactly the three analytic statements isolated by
`Cogentic.RandomizedL27GaussianFactor`:

* `GaussianDedekindZetaEulerProduct` — the Euler product of `ζ_{ℚ(i)}`;
* `DedekindZetaContinuationAtFour` — its meromorphic continuation, needed only
  for the all-`s` factorization;
* `DirichletBetaAtOne` — the value `L(1, χ_{-4}) = π / 4`.

There is no field-realization, class-number, or unit component. -/
structure GaussianAnalyticResidual where
  /-- The Euler product of the Dedekind zeta function of `ℚ(i)`. -/
  eulerProduct : GaussianDedekindZetaEulerProduct
  /-- The continuation extending the half-plane factorization to all `s`. -/
  continuation : DedekindZetaContinuationAtFour
    (fun s => DirichletCharacter.LFunction chiNegFour s)
  /-- The beta value `L(1, χ_{-4}) = π / 4`. -/
  betaAtOne : DirichletBetaAtOne

/-- The Euler product part gives the half-plane factorization. -/
theorem gaussianAnalyticResidual_rightHalfPlane (h : GaussianAnalyticResidual) :
    DedekindZetaFactorizationAtFourRightHalfPlane
      (fun s => DirichletCharacter.LFunction chiNegFour s) :=
  dedekindZetaFactorizationAtFourRightHalfPlane_LFunction_of_eulerProduct
    h.eulerProduct

/-- Adding the continuation gives the full factorization. -/
theorem gaussianAnalyticResidual_factorization (h : GaussianAnalyticResidual) :
    DedekindZetaFactorizationAtFour
      (fun s => DirichletCharacter.LFunction chiNegFour s) :=
  dedekindZetaFactorizationAtFour_LFunction_of_eulerProduct_of_continuation
    h.eulerProduct h.continuation

/-- The residue uses only the Euler product and the beta value. -/
theorem gaussianAnalyticResidual_residue (h : GaussianAnalyticResidual) :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = Real.pi / 4 :=
  residue_gaussian_eq_pi_div_four_of_eulerProduct_of_beta h.eulerProduct
    h.betaAtOne

/-- **The class-number formula at `D = 4` from the analytic residual alone.** -/
theorem classNumberFormula_at_four_of_residual (h : GaussianAnalyticResidual) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * (Real.pi / 4) :=
  classNumberFormula_at_four_of_eulerProduct_of_beta h.eulerProduct h.betaAtOne

/-- The formula from the bundled residual evaluates to `1`. -/
theorem smallClassNumber_four_eq_one_of_residual (h : GaussianAnalyticResidual) :
    smallClassNumber 4 = 1 :=
  smallClassNumber_four_eq_one_of_eulerProduct_of_beta h.eulerProduct h.betaAtOne

/-! ## 5. The exact residual for the residue and for the formula -/

/-- **The exact analytic residual for the residue at `1`.**  Only the Euler
product and the beta value are used; the continuation is genuinely only needed
for the all-`s` factorization stated in `GaussianAnalyticResidual`. -/
def GaussianResidueResidual : Prop :=
  GaussianDedekindZetaEulerProduct ∧ DirichletBetaAtOne

/-- Every full analytic residual restricts to the residue residual. -/
theorem GaussianAnalyticResidual.toResidueResidual (h : GaussianAnalyticResidual) :
    GaussianResidueResidual :=
  ⟨h.eulerProduct, h.betaAtOne⟩

/-- The residue from the exact residual. -/
theorem residue_of_gaussianResidueResidual (h : GaussianResidueResidual) :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = Real.pi / 4 :=
  residue_gaussian_eq_pi_div_four_of_eulerProduct_of_beta h.1 h.2

/-- **The class-number formula at `D = 4` from the exact residue residual.** -/
theorem classNumberFormula_at_four_of_residueResidual (h : GaussianResidueResidual) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * (Real.pi / 4) :=
  classNumberFormula_at_four_of_eulerProduct_of_beta h.1 h.2

/-- The formula from the exact residual evaluates to `1`. -/
theorem smallClassNumber_four_eq_one_of_residueResidual
    (h : GaussianResidueResidual) : smallClassNumber 4 = 1 :=
  smallClassNumber_four_eq_one_of_eulerProduct_of_beta h.1 h.2

/-! ## 6. Consistency with `DirichletClassNumberFormula` -/

/-- The `D = 4` instance of the standard unnormalized Dirichlet formula,
specialized to the Gaussian `L1`.  This confirms that the formula proved here is
literally the `D = 4` case of
`Cogentic.RandomizedL27ClassNumber.DirichletClassNumberFormula`. -/
theorem dirichletClassNumberFormula_at_four :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * gaussianL1 4 :=
  classNumberFormula_at_four_of_L1 gaussianL1 lOneAtFour_gaussianL1

/-- The standard Dirichlet formula, if assumed globally, specializes at `D = 4`
to the same statement.  The content of this file is that its `D = 4` instance
is already a theorem, with the analytic residual isolated above. -/
theorem dirichletClassNumberFormula_specializes_at_four
    (h : DirichletClassNumberFormula smallClassNumber gaussianL1 smallWeight) :
    smallClassNumber 4 =
      (smallWeight 4 / (2 * Real.pi)) * Real.sqrt (4 : ℝ) * gaussianL1 4 :=
  h 4 (isFrobeniusDiscriminant_of_fundamental isFundamentalDiscriminant_four)

end

/-! ## Axiom audit -/

#print axioms dedekindZeta_residue_eq_pi_div_four_of_four_invariants
#print axioms classNumberFormula_at_four_of_fieldRealizationAt
#print axioms smallClassNumber_four_eq_one
#print axioms smallClassNumber_four_direct
#print axioms KroneckerLOneAtFour
#print axioms LOneAtFour
#print axioms kroneckerLValueAtFour
#print axioms kroneckerLValueAtFour_eq_pi_div_four
#print axioms KroneckerLOneAtFour.lOneAtFour
#print axioms gaussianL1
#print axioms gaussianL1_four
#print axioms lOneAtFour_gaussianL1
#print axioms kroneckerLOneAtFour_gaussianL1
#print axioms classNumberFormula_at_four_of_L1
#print axioms classNumberFormula_at_four_of_kroneckerL1
#print axioms residue_gaussian_eq_pi_div_four_of_eulerProduct_of_beta
#print axioms classNumberFormula_at_four_of_eulerProduct_of_beta
#print axioms classNumberFormula_at_four_of_eulerProduct_of_beta_of_L1
#print axioms classNumberFormula_at_four_of_eulerProduct_of_kroneckerL1
#print axioms smallClassNumber_four_eq_one_of_eulerProduct_of_beta
#print axioms gaussianAnalyticResidual_rightHalfPlane
#print axioms gaussianAnalyticResidual_factorization
#print axioms gaussianAnalyticResidual_residue
#print axioms classNumberFormula_at_four_of_residual
#print axioms smallClassNumber_four_eq_one_of_residual
#print axioms GaussianAnalyticResidual.toResidueResidual
#print axioms residue_of_gaussianResidueResidual
#print axioms classNumberFormula_at_four_of_residueResidual
#print axioms smallClassNumber_four_eq_one_of_residueResidual
#print axioms dirichletClassNumberFormula_at_four
#print axioms dirichletClassNumberFormula_specializes_at_four

end Cogentic.RandomizedL27ClassNumberD4
