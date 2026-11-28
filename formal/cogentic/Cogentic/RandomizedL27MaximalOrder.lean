import Cogentic.RandomizedL27ClassNumberFormula
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.LSeries.RiemannZeta

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

/-!
# L27: concrete maximal orders for `D = 4` and `D = 3`

This file tests the maximal-order field realization
`Cogentic.RandomizedL27ClassNumberFormula.FundamentalOrderFieldRealization`
against the two smallest negative fundamental discriminants.

Mathlib has no general construction of `ℚ(√-D)` together with its ring of
integers.  We therefore use the cyclotomic models

* `D = 4`: `K = CyclotomicField 4 ℚ ≅ ℚ(i)`,
* `D = 3`: `K = CyclotomicField 3 ℚ ≅ ℚ(√-3)`.

For these fields Mathlib computes the discriminant
(`IsCyclotomicExtension.Rat.discr_prime_pow`), the number of real and complex
places (`IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`,
`...nrComplexPlaces_eq_totient_div_two`), the torsion order
(`IsCyclotomicExtension.Rat.torsionOrder_eq`) and, for `D = 3`, the class
number (`IsCyclotomicExtension.Rat.three_pid`).  The class number of `ℚ(i)` is
obtained from the Minkowski bound.

The regulator is handled by the general lemma
`regulator_eq_one_of_rank_eq_zero`: the determinant formula for the regulator
has an empty index set in unit rank zero, hence the regulator is `1`.

The general discriminant is reduced to the concrete field
`AdjoinRoot (X^2 + D)`.  Mathlib supplies the field and its `NumberField`
instance, but not the ring of integers, the discriminant, the class number or
the unit torsion of this model.  These are isolated as `QuadraticFieldGap`.

For the analytic input, we compute the residue of `ζ_{ℚ(i)}` directly from
Mathlib's residue formula: it is `π / 4`.  Mathlib does not prove the
factorization `ζ_{ℚ(i)}(s) = ζ(s) L(s, χ_{-4})`; we state it as
`DedekindZetaFactorizationAtFour` and prove that it implies the residue
identification `res = L(1, χ_{-4})`.

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

namespace Cogentic.RandomizedL27ClassNumberFormula

open Filter Real
open scoped BigOperators Topology
open NumberField

noncomputable section

/-! ## 1. The regulator in unit rank zero -/

/-- **The regulator is `1` in unit rank zero.**  The determinant formula
`NumberField.Units.regulator_eq_det` writes the regulator as the determinant of
a matrix indexed by the infinite places different from a fixed place.  When the
unit rank is zero the index type is empty, so the determinant is `1`. -/
theorem regulator_eq_one_of_rank_eq_zero (K : Type*) [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 0) :
    NumberField.Units.regulator K = 1 := by
  classical
  haveI : Nonempty (NumberField.InfinitePlace K) := inferInstance
  obtain ⟨w'⟩ := ‹Nonempty (NumberField.InfinitePlace K)›
  have hcard : Fintype.card (NumberField.InfinitePlace K) = 1 := by
    have hpos : 0 < Fintype.card (NumberField.InfinitePlace K) := Fintype.card_pos
    have hsub : Fintype.card (NumberField.InfinitePlace K) - 1 = 0 := hrank
    omega
  have hcompl : Fintype.card {w : NumberField.InfinitePlace K // w ≠ w'} = 0 := by
    rw [Fintype.card_subtype_compl (fun w => w = w')]
    simp [hcard]
  let e : {w : NumberField.InfinitePlace K // w ≠ w'} ≃ Fin (NumberField.Units.rank K) :=
    (Fintype.equivFin _).trans (finCongr (by rw [hcompl, hrank]))
  rw [NumberField.Units.regulator_eq_det K w' e]
  rw [Matrix.det_eq_one_of_card_eq_zero hcompl]
  norm_num

/-- The regulator is `1` for an imaginary quadratic field (`r₁ = 0`, `r₂ = 1`). -/
theorem regulator_eq_one_of_imaginary_quadratic (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1) :
    NumberField.Units.regulator K = 1 := by
  apply regulator_eq_one_of_rank_eq_zero K
  unfold NumberField.Units.rank
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, hcomplex]

/-! ## 2. `D = 4`: the Gaussian field -/

/-- The cyclotomic model of `ℚ(i)`. -/
abbrev GaussianCyclotomicField : Type := CyclotomicField 4 ℚ

instance : IsCyclotomicExtension {4} ℚ GaussianCyclotomicField :=
  CyclotomicField.isCyclotomicExtension 4 ℚ

instance : NumberField GaussianCyclotomicField := inferInstance

/-- `4` is a fundamental discriminant. -/
theorem isFundamentalDiscriminant_four : IsFundamentalDiscriminant 4 := by
  refine ⟨by norm_num, Or.inr ⟨by norm_num, ?_, Or.inl (by norm_num)⟩⟩
  norm_num

/-- The discriminant of `ℚ(ζ₄)` is `-4`. -/
theorem discr_gaussian : NumberField.discr GaussianCyclotomicField = -4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclotomicExtension {2 ^ 2} ℚ GaussianCyclotomicField := by
    rw [show 2 ^ 2 = 4 by norm_num]
    infer_instance
  rw [IsCyclotomicExtension.Rat.discr_prime_pow 2 2 GaussianCyclotomicField]
  norm_num
  decide

/-- `ℚ(ζ₄)` has no real places. -/
theorem nrRealPlaces_gaussian :
    NumberField.InfinitePlace.nrRealPlaces GaussianCyclotomicField = 0 :=
  IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 4) GaussianCyclotomicField
    (by decide)

/-- `ℚ(ζ₄)` has one complex place. -/
theorem nrComplexPlaces_gaussian :
    NumberField.InfinitePlace.nrComplexPlaces GaussianCyclotomicField = 1 := by
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 4)
    GaussianCyclotomicField]
  decide

/-- The regulator of `ℚ(ζ₄)` is `1`. -/
theorem regulator_gaussian :
    NumberField.Units.regulator GaussianCyclotomicField = 1 :=
  regulator_eq_one_of_imaginary_quadratic GaussianCyclotomicField
    nrRealPlaces_gaussian nrComplexPlaces_gaussian

/-- `ℚ(ζ₄)` has class number `1`. -/
theorem classNumber_gaussian : NumberField.classNumber GaussianCyclotomicField = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_gaussian, nrComplexPlaces_gaussian,
    IsCyclotomicExtension.Rat.finrank (k := 4) (K := GaussianCyclotomicField)]
  · rw [show Nat.totient 4 = 2 by decide]
    norm_num
    nlinarith [Real.pi_gt_three]

/-- `ℚ(ζ₄)` has torsion order `4`. -/
theorem torsionOrder_gaussian :
    NumberField.Units.torsionOrder GaussianCyclotomicField = 4 := by
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 4)
    (K := GaussianCyclotomicField)]
  rw [if_pos (show Even 4 by exact ⟨2, rfl⟩)]

/-- **The residue of `ζ_{ℚ(i)}`.**  This is Mathlib's residue formula with all
invariants of `ℚ(ζ₄)` substituted. -/
theorem dedekindZeta_residue_gaussian :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = Real.pi / 4 := by
  rw [NumberField.dedekindZeta_residue_def, nrRealPlaces_gaussian,
    nrComplexPlaces_gaussian, regulator_gaussian, discr_gaussian,
    classNumber_gaussian, torsionOrder_gaussian]
  norm_num
  field_simp
  norm_num

/-! ## 3. `D = 3`: the Eisenstein field -/

/-- The cyclotomic model of `ℚ(√-3)`. -/
abbrev EisensteinCyclotomicField : Type := CyclotomicField 3 ℚ

instance : IsCyclotomicExtension {3} ℚ EisensteinCyclotomicField :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : NumberField EisensteinCyclotomicField := inferInstance

/-- `3` is a fundamental discriminant. -/
theorem isFundamentalDiscriminant_three : IsFundamentalDiscriminant 3 := by
  refine ⟨by norm_num, Or.inl ⟨by norm_num, ?_⟩⟩
  norm_num

/-- The discriminant of `ℚ(ζ₃)` is `-3`. -/
theorem discr_eisenstein : NumberField.discr EisensteinCyclotomicField = -3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsCyclotomicExtension.Rat.discr_prime 3 EisensteinCyclotomicField]
  norm_num

/-- `ℚ(ζ₃)` has no real places. -/
theorem nrRealPlaces_eisenstein :
    NumberField.InfinitePlace.nrRealPlaces EisensteinCyclotomicField = 0 :=
  IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) EisensteinCyclotomicField
    (by decide)

/-- `ℚ(ζ₃)` has one complex place. -/
theorem nrComplexPlaces_eisenstein :
    NumberField.InfinitePlace.nrComplexPlaces EisensteinCyclotomicField = 1 := by
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 3)
    EisensteinCyclotomicField]
  decide

/-- The regulator of `ℚ(ζ₃)` is `1`. -/
theorem regulator_eisenstein :
    NumberField.Units.regulator EisensteinCyclotomicField = 1 :=
  regulator_eq_one_of_imaginary_quadratic EisensteinCyclotomicField
    nrRealPlaces_eisenstein nrComplexPlaces_eisenstein

/-- `ℚ(ζ₃)` has class number `1`, from Mathlib's `three_pid`. -/
theorem classNumber_eisenstein :
    NumberField.classNumber EisensteinCyclotomicField = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  exact IsCyclotomicExtension.Rat.three_pid EisensteinCyclotomicField

/-- `ℚ(ζ₃)` has torsion order `6`. -/
theorem torsionOrder_eisenstein :
    NumberField.Units.torsionOrder EisensteinCyclotomicField = 6 := by
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 3)
    (K := EisensteinCyclotomicField)]
  rw [if_neg (by decide : ¬ Even 3)]

/-- **The residue of `ζ_{ℚ(√-3)}`.**  This is Mathlib's residue formula with all
invariants of `ℚ(ζ₃)` substituted. -/
theorem dedekindZeta_residue_eisenstein :
    NumberField.dedekindZeta_residue EisensteinCyclotomicField =
      Real.pi / (3 * Real.sqrt 3) := by
  rw [NumberField.dedekindZeta_residue_def, nrRealPlaces_eisenstein,
    nrComplexPlaces_eisenstein, regulator_eisenstein, discr_eisenstein,
    classNumber_eisenstein, torsionOrder_eisenstein]
  norm_num
  field_simp
  norm_num

/-! ## 4. Per-discriminant field realizations -/

/-- The body of `FundamentalOrderFieldRealization` at a single `D`. -/
def FieldRealizationAt (classNumber weight : ℤ → ℝ) (D : ℤ) : Prop :=
  IsFundamentalDiscriminant D →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      NumberField.discr K = -D ∧
      (NumberField.classNumber K : ℝ) = classNumber D ∧
      (NumberField.Units.torsionOrder K : ℝ) = weight D ∧
      NumberField.InfinitePlace.nrRealPlaces K = 0 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 1 ∧
      NumberField.Units.regulator K = 1

/-- The per-discriminant predicate is exactly the body of the global
realization. -/
theorem fundamentalOrderFieldRealization_iff {classNumber weight : ℤ → ℝ} :
    FundamentalOrderFieldRealization classNumber weight ↔
      ∀ D : ℤ, FieldRealizationAt classNumber weight D :=
  Iff.rfl

/-- A model class-number function which is correct at `D = 3` and `D = 4`. -/
def smallClassNumber : ℤ → ℝ := fun D => if D = 3 ∨ D = 4 then 1 else 0

/-- A model unit-weight function which is correct at `D = 3` and `D = 4`. -/
def smallWeight : ℤ → ℝ := fun D => if D = 3 then 6 else if D = 4 then 4 else 0

/-- **`D = 4`: the maximal order of `ℚ(i)` realizes the expected invariants.**
These are `disc = -4`, `h = 1`, `w = 4`, `r₁ = 0`, `r₂ = 1`, `Reg = 1`. -/
theorem fieldRealizationAt_four : FieldRealizationAt smallClassNumber smallWeight 4 := by
  intro _
  refine ⟨GaussianCyclotomicField, inferInstance, inferInstance, discr_gaussian, ?_, ?_,
    nrRealPlaces_gaussian, nrComplexPlaces_gaussian, regulator_gaussian⟩
  · rw [classNumber_gaussian]
    norm_num [smallClassNumber]
  · rw [torsionOrder_gaussian]
    norm_num [smallWeight]

/-- **`D = 3`: the maximal order of `ℚ(√-3)` realizes the expected invariants.**
These are `disc = -3`, `h = 1`, `w = 6`, `r₁ = 0`, `r₂ = 1`, `Reg = 1`. -/
theorem fieldRealizationAt_three : FieldRealizationAt smallClassNumber smallWeight 3 := by
  intro _
  refine ⟨EisensteinCyclotomicField, inferInstance, inferInstance, discr_eisenstein, ?_, ?_,
    nrRealPlaces_eisenstein, nrComplexPlaces_eisenstein, regulator_eisenstein⟩
  · rw [classNumber_eisenstein]
    norm_num [smallClassNumber]
  · rw [torsionOrder_eisenstein]
    norm_num [smallWeight]

/-- **The existential form at `D = 4`.**  This is the exact body of
`FundamentalOrderFieldRealization` at `D = 4`, with the classical values
`h(-4) = 1` and `w(-4) = 4`. -/
theorem exists_gaussian_maximalOrder :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      NumberField.discr K = -4 ∧
      (NumberField.classNumber K : ℝ) = 1 ∧
      (NumberField.Units.torsionOrder K : ℝ) = 4 ∧
      NumberField.InfinitePlace.nrRealPlaces K = 0 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 1 ∧
      NumberField.Units.regulator K = 1 := by
  obtain ⟨K, hK, hN, hdisc, hclass, hweight, hreal, hcomplex, hreg⟩ :=
    fieldRealizationAt_four isFundamentalDiscriminant_four
  letI : Field K := hK
  letI : NumberField K := hN
  exact ⟨K, hK, hN, hdisc, by simpa [smallClassNumber] using hclass,
    by simpa [smallWeight] using hweight, hreal, hcomplex, hreg⟩

/-- **The existential form at `D = 3`.**  This is the exact body of
`FundamentalOrderFieldRealization` at `D = 3`, with the classical values
`h(-3) = 1` and `w(-3) = 6`. -/
theorem exists_eisenstein_maximalOrder :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      NumberField.discr K = -3 ∧
      (NumberField.classNumber K : ℝ) = 1 ∧
      (NumberField.Units.torsionOrder K : ℝ) = 6 ∧
      NumberField.InfinitePlace.nrRealPlaces K = 0 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 1 ∧
      NumberField.Units.regulator K = 1 := by
  obtain ⟨K, hK, hN, hdisc, hclass, hweight, hreal, hcomplex, hreg⟩ :=
    fieldRealizationAt_three isFundamentalDiscriminant_three
  letI : Field K := hK
  letI : NumberField K := hN
  exact ⟨K, hK, hN, hdisc, by simpa [smallClassNumber] using hclass,
    by simpa [smallWeight] using hweight, hreal, hcomplex, hreg⟩

/-! ## 5. The general discriminant: the exact construction gap -/

/-- The concrete quadratic field `AdjoinRoot (X^2 + D)` over `ℚ`.  For `D > 0`
this is `ℚ(√-D)`. -/
abbrev ImaginaryQuadraticField (D : ℤ) : Type :=
  AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))

/-- `X^2 + D` is irreducible over `ℚ` for `D > 0`, so `AdjoinRoot (X^2 + D)`
is a number field. -/
theorem irreducible_quadraticPoly {D : ℤ} (hD : 0 < D) :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (D : ℚ)) := by
  have h : Polynomial.X ^ 2 + Polynomial.C (D : ℚ) =
      Polynomial.X ^ 2 - Polynomial.C (-(D : ℚ)) := by
    rw [Polynomial.C_neg, sub_neg_eq_add]
  rw [h, X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  intro b hb
  have hb' : b ^ 2 = -(D : ℚ) := by simpa using hb
  have hnonneg : 0 ≤ b ^ 2 := sq_nonneg b
  have hDpos : (0 : ℚ) < D := by exact_mod_cast hD
  nlinarith

/-- The concrete field `AdjoinRoot (X^2 + D)` is a number field for every
positive discriminant. -/
theorem numberField_imaginaryQuadraticField {D : ℤ} (hD : 0 < D) :
    letI : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) :=
      ⟨irreducible_quadraticPoly hD⟩
    NumberField (ImaginaryQuadraticField D) := by
  letI : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) :=
    ⟨irreducible_quadraticPoly hD⟩
  infer_instance

/-- **The exact remaining construction gap.**  For every fundamental
discriminant `D`, the concrete field `AdjoinRoot (X^2 + D)` already exists and
is a number field; what is missing is the computation of its arithmetic
invariants: the discriminant `-D`, the class number, the unit torsion, and the
embedding counts.

This is precisely the part of `FundamentalOrderFieldRealization` that Mathlib
does not provide. -/
def QuadraticFieldGap (classNumber weight : ℤ → ℝ) : Prop :=
  ∀ (D : ℤ) (hD : IsFundamentalDiscriminant D),
    letI : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) :=
      ⟨irreducible_quadraticPoly (isFundamentalDiscriminant_pos hD)⟩
    NumberField.discr (ImaginaryQuadraticField D) = -D ∧
      (NumberField.classNumber (ImaginaryQuadraticField D) : ℝ) = classNumber D ∧
      (NumberField.Units.torsionOrder (ImaginaryQuadraticField D) : ℝ) = weight D ∧
      NumberField.InfinitePlace.nrRealPlaces (ImaginaryQuadraticField D) = 0 ∧
      NumberField.InfinitePlace.nrComplexPlaces (ImaginaryQuadraticField D) = 1 ∧
      NumberField.Units.regulator (ImaginaryQuadraticField D) = 1

/-- **From the concrete quadratic-field gap to the maximal-order field
realization.**  This is the precise reduction: once the invariants of
`AdjoinRoot (X^2 + D)` are known, the global realization follows. -/
theorem fundamentalOrderFieldRealization_of_quadraticFieldGap
    {classNumber weight : ℤ → ℝ} (h : QuadraticFieldGap classNumber weight) :
    FundamentalOrderFieldRealization classNumber weight := by
  intro D hD
  haveI : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) :=
    ⟨irreducible_quadraticPoly (isFundamentalDiscriminant_pos hD)⟩
  obtain ⟨hdisc, hclass, hweight, hreal, hcomplex, hreg⟩ := h D hD
  exact ⟨ImaginaryQuadraticField D, inferInstance, inferInstance, hdisc, hclass,
    hweight, hreal, hcomplex, hreg⟩

/-! ## 6. The analytic identification at `D = 4` -/

/-- The exact missing factorization of the Dedekind zeta function of `ℚ(i)`:
`ζ_{ℚ(i)}(s) = ζ(s) L(s, χ_{-4})`, with the `L`-factor left abstract. -/
def DedekindZetaFactorizationAtFour (L : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, NumberField.dedekindZeta GaussianCyclotomicField s = riemannZeta s * L s

/-- **The residue is the value at `1` of the `L`-factor.**  This is the exact
reduction from the factorization to the residue identification: if
`ζ_{ℚ(i)} = ζ · L` and `L` is continuous at `1`, then
`res_{s=1} ζ_{ℚ(i)}(s) = L(1)`. -/
theorem residue_gaussian_eq_L_one_of_factorization
    (L : ℂ → ℂ) (hfac : DedekindZetaFactorizationAtFour L)
    (hL : ContinuousAt L 1) :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = (L 1).re := by
  have hK := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT GaussianCyclotomicField
  have hcoe : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact fun h => (ne_of_gt (show (1 : ℝ) < s from hs)) (Complex.ofReal_injective h)
  have hζ : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hcoe
  have hLt : Tendsto (fun s : ℝ => L (s : ℂ)) (𝓝[>] 1) (𝓝 (L 1)) := by
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
    exact hL.tendsto.comp hc
  have hprod : Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ) * L (s : ℂ))
      (𝓝[>] 1) (𝓝 (1 * L 1)) :=
    hζ.mul hLt
  have hK' : Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * (riemannZeta (s : ℂ) * L (s : ℂ)))
      (𝓝[>] 1) (𝓝 ((NumberField.dedekindZeta_residue GaussianCyclotomicField : ℂ))) := by
    have hfac' : ∀ s : ℂ,
        NumberField.dedekindZeta GaussianCyclotomicField s = riemannZeta s * L s := hfac
    simpa [hfac', Complex.ofReal_sub] using hK
  have huniq : (NumberField.dedekindZeta_residue GaussianCyclotomicField : ℂ) = L 1 :=
    tendsto_nhds_unique hK' (by simpa [mul_assoc] using hprod)
  have hre := congr_arg Complex.re huniq
  simpa using hre

/-- **The residue identification at `D = 4` from the factorization and the
value `L(1) = L1 4`.** -/
theorem residue_gaussian_eq_L1_of_factorization
    (L1 : ℤ → ℝ) (L : ℂ → ℂ) (hfac : DedekindZetaFactorizationAtFour L)
    (hL : ContinuousAt L 1) (hval : (L 1).re = L1 4) :
    NumberField.dedekindZeta_residue GaussianCyclotomicField = L1 4 := by
  rw [residue_gaussian_eq_L_one_of_factorization L hfac hL, hval]

/-- The per-discriminant specialization of the global residue predicate. -/
def DedekindZetaResidueIsQuadraticLAt (L1 : ℤ → ℝ) (D : ℤ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    IsFundamentalDiscriminant D →
    NumberField.discr K = -D →
    NumberField.InfinitePlace.nrRealPlaces K = 0 →
    NumberField.InfinitePlace.nrComplexPlaces K = 1 →
    NumberField.Units.regulator K = 1 →
    NumberField.dedekindZeta_residue K = L1 D

/-- **The global predicate implies its `D = 4` specialization.**  The concrete
residue value `π / 4` is `dedekindZeta_residue_gaussian`. -/
theorem dedekindZetaResidueIsQuadraticLAt_four_of_global
    {L1 : ℤ → ℝ} (h : DedekindZetaResidueIsQuadraticL L1) :
    DedekindZetaResidueIsQuadraticLAt L1 4 := by
  intro K _ _ hD hdisc hreal hcomplex hreg
  exact h 4 K hD hdisc hreal hcomplex hreg

end

/-! ## Axiom audit -/

#print axioms regulator_eq_one_of_rank_eq_zero
#print axioms regulator_eq_one_of_imaginary_quadratic
#print axioms isFundamentalDiscriminant_four
#print axioms discr_gaussian
#print axioms nrRealPlaces_gaussian
#print axioms nrComplexPlaces_gaussian
#print axioms regulator_gaussian
#print axioms classNumber_gaussian
#print axioms torsionOrder_gaussian
#print axioms dedekindZeta_residue_gaussian
#print axioms isFundamentalDiscriminant_three
#print axioms discr_eisenstein
#print axioms nrRealPlaces_eisenstein
#print axioms nrComplexPlaces_eisenstein
#print axioms regulator_eisenstein
#print axioms classNumber_eisenstein
#print axioms torsionOrder_eisenstein
#print axioms dedekindZeta_residue_eisenstein
#print axioms fieldRealizationAt_four
#print axioms fieldRealizationAt_three
#print axioms exists_gaussian_maximalOrder
#print axioms exists_eisenstein_maximalOrder
#print axioms irreducible_quadraticPoly
#print axioms numberField_imaginaryQuadraticField
#print axioms fundamentalOrderFieldRealization_of_quadraticFieldGap
#print axioms residue_gaussian_eq_L_one_of_factorization
#print axioms residue_gaussian_eq_L1_of_factorization
#print axioms dedekindZetaResidueIsQuadraticLAt_four_of_global

end Cogentic.RandomizedL27ClassNumberFormula
