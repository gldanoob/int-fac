import Cogentic.RandomizedL27Siegel
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# L27: the Dirichlet class-number and `L(1, χ)` inputs

`Cogentic.RandomizedL27Siegel` reduced the Siegel leaf to two arithmetic
inequalities:

* `HurwitzClassNumberFormulaLower hurwitz L1 c`, the lower half of the
  imaginary quadratic order class-number formula;
* `DirichletLOneLower L1 l`, a uniform positive lower bound for the quadratic
  `L`-value at `1`.

This file reduces those two inputs once more, in the direction of the standard
Dirichlet class-number formula.

## The class-number side

For an imaginary quadratic order of discriminant `-D`, let `h(D)` be its class
number and `w(D)` its unit weight.  The classical formula is

`h(D) = (w(D)/(2π)) · L(1, χ_D) · √D`.

Dividing by `w(D)` gives the *weighted* class number `h(D)/w(D)`, which is the
quantity that the Hurwitz class number `H(-D)` dominates (the Hurwitz class
number is the sum of the weighted class numbers of the orders of discriminant
`-D`).  Thus the lower half of the formula follows from three explicit facts:

1. `DirichletClassNumberFormula classNumber L1 weight` — the formula as an
   equality, with the unit weight kept visible;
2. `UnitWeightPositive weight` — `w(D) > 0`;
3. `HurwitzDominatesWeightedClassNumber hurwitz classNumber weight` —
   `h(D)/w(D) ≤ H(-D)`.

The reduction is `hurwitzClassNumberFormulaLower_of_dirichletFormula`; the
bundled form is `DirichletClassNumberInput.hurwitzFormulaLower`.  Keeping the
weight visible is essential: the unweighted class number can exceed the Hurwitz
class number at the two small discriminants, so the honest domination is by the
weighted class number.

## The `L`-one side

A uniform positive lower bound `0 < l ≤ L(1, χ_D)` fails exactly when there is a
positive sequence of Frobenius discriminants whose `L`-values tend to zero.  This
is `ExceptionalLOneSequence`.  The equivalence

`(∃ l, DirichletLOneLower L1 l) ↔ NoExceptionalLOneSequence L1`

under pointwise positivity is `dirichletLOneInput_iff_noExceptionalSequence`.
The pointwise positivity itself is *derived* from the class-number formula and
the positivity of the class number (`L1_pos_of_dirichletFormula`), so the only
remaining `L`-input is the qualitative absence of an exceptional sequence.

Combining the two reductions yields the trace leaf with the explicit constant
`classNumberFormulaConstant * l`; see
`exists_hurwitzSiegelLowerTrace_of_classNumberInput` and
`toSiegelInputs_of_classNumberFormula`.

## What Mathlib supplies

Mathlib has the general Dirichlet class-number formula for number fields
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) and the qualitative
nonvanishing of Dirichlet `L`-functions on `re s ≥ 1`
(`DirichletCharacter.LFunction_ne_zero_of_one_le_re`).  It does not contain the
quadratic order class-number formula, a construction of the Kronecker character
`χ_D`, or any uniform positive lower bound for `L(1, χ_D)`.  Consequently the
formula equality and the absence of an exceptional sequence are kept as named
inputs here rather than replaced by a zero count or an unproved lemma.  The
Mathlib anchors are re-exported at the end of §0.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No class number,
curve count, or loss is set to zero.
-/

namespace Cogentic.RandomizedL27ClassNumber

open Filter Real
open scoped BigOperators Topology
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27Siegel
open Cogentic.RandomizedL27TraceClass

noncomputable section

/-! ## 0. Mathlib anchors -/

/-- The general Dirichlet class-number formula, in the form supplied by
Mathlib: the residue of the Dedekind zeta function at `1`. -/
theorem dedekindZeta_classNumberFormula (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ => (s - 1) * NumberField.dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K)) :=
  NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K

/-- The residue in Mathlib's Dirichlet class-number formula is positive. -/
theorem dedekindZeta_residue_pos (K : Type*) [Field K] [NumberField K] :
    0 < NumberField.dedekindZeta_residue K :=
  NumberField.dedekindZeta_residue_pos K

/-- Mathlib's qualitative nonvanishing of a nontrivial Dirichlet `L`-function at
`1`.  This is the largest `L`-one statement available in Mathlib; it gives no
uniform lower bound. -/
theorem dirichletLFunction_one_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    χ.LFunction 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

/-! ## 1. The standard Dirichlet class-number formula -/

/-- **The imaginary-quadratic order class-number formula.**  On Frobenius
discriminants,
`h(D) = (w(D)/(2π)) · L(1, χ_D) · √D`,
where `h` is the order class number and `w` is the unit weight.  The equality is
kept unnormalized so that the unit weight is visible. -/
def DirichletClassNumberFormula (classNumber L1 weight : ℤ → ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D →
    classNumber D = (weight D / (2 * Real.pi)) * Real.sqrt (D : ℝ) * L1 D

/-- The unit weight is positive on Frobenius discriminants. -/
def UnitWeightPositive (weight : ℤ → ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < weight D

/-- The order class number is positive on Frobenius discriminants. -/
def OrderClassNumberPositive (classNumber : ℤ → ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < classNumber D

/-- **The Hurwitz class number dominates the weighted order class number.**
This is the order-theoretic half of the Hurwitz class-number definition: `H(-D)`
is the sum, over the orders of discriminant `-D`, of their weighted class
numbers. -/
def HurwitzDominatesWeightedClassNumber
    (hurwitz classNumber weight : ℤ → ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D →
    classNumber D / weight D ≤ hurwitz D

/-- The weighted class number equals the canonical class-number-formula lower
bound.  This is the class-number formula after dividing by the unit weight. -/
theorem weightedClassNumber_eq_formulaConstant
    {classNumber L1 weight : ℤ → ℝ}
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight) {D : ℤ}
    (hD : IsFrobeniusDiscriminant D) :
    classNumber D / weight D =
      classNumberFormulaConstant * Real.sqrt (D : ℝ) * L1 D := by
  have hwpos : 0 < weight D := hw D hD
  rw [hformula D hD, classNumberFormulaConstant]
  field_simp [hwpos.ne']

/-- **The formula lower bound from the standard Dirichlet formula.**  The
unweighted formula, the positivity of the unit weight, and the domination of the
weighted class number by the Hurwitz class number give
`H(-D) ≥ (1/(2π)) · L(1, χ_D) · √D`. -/
theorem hurwitzClassNumberFormulaLower_of_dirichletFormula
    {hurwitz classNumber L1 weight : ℤ → ℝ}
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight) :
    HurwitzClassNumberFormulaLower hurwitz L1 classNumberFormulaConstant := by
  intro D hD
  calc
    classNumberFormulaConstant * L1 D * Real.sqrt (D : ℝ) =
        classNumberFormulaConstant * Real.sqrt (D : ℝ) * L1 D := by ring
    _ = classNumber D / weight D :=
      (weightedClassNumber_eq_formulaConstant hformula hw hD).symm
    _ ≤ hurwitz D := hdom D hD

/-- **The `L`-value is positive.**  The standard formula, positivity of the
class number, and positivity of the unit weight force `L(1, χ_D) > 0`.  Thus the
sign half of `DirichletLOneLower` is not an extra input. -/
theorem L1_pos_of_dirichletFormula
    {classNumber L1 weight : ℤ → ℝ}
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hclass : OrderClassNumberPositive classNumber) :
    ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D := by
  intro D hD
  have hwpos : 0 < weight D := hw D hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast isFrobeniusDiscriminant_pos hD
  have hsqrt : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hDpos
  have hc : 0 < classNumberFormulaConstant := classNumberFormulaConstant_pos
  have hquot : 0 < classNumber D / weight D :=
    div_pos (hclass D hD) hwpos
  rw [weightedClassNumber_eq_formulaConstant hformula hw hD] at hquot
  have hprod : 0 < (classNumberFormulaConstant * Real.sqrt (D : ℝ)) * L1 D := by
    simpa [mul_assoc] using hquot
  exact pos_of_mul_pos_right hprod (mul_pos hc hsqrt).le

/-! ## 2. The `L`-one input as absence of an exceptional sequence -/

/-- **An exceptional `L`-one sequence.**  A sequence of Frobenius discriminants,
with positive `L`-values, along which `L(1, χ_D)` tends to zero.  This is exactly
the failure mode excluded by a uniform positive lower bound. -/
def ExceptionalLOneSequence (L1 : ℤ → ℝ) : Prop :=
  ∃ D : ℕ → ℤ, (∀ n, IsFrobeniusDiscriminant (D n)) ∧
    (∀ n, 0 < L1 (D n)) ∧
      Tendsto (fun n => L1 (D n)) atTop (𝓝 0)

/-- The qualitative residual `L`-one input: no positive exceptional sequence. -/
def NoExceptionalLOneSequence (L1 : ℤ → ℝ) : Prop :=
  ¬ ExceptionalLOneSequence L1

/-- The uniform positive lower bound, packaged as an existential. -/
def DirichletLOneInput (L1 : ℤ → ℝ) : Prop :=
  ∃ l : ℝ, DirichletLOneLower L1 l

/-- **A uniform lower bound is exactly the absence of a positive sequence
tending to zero.**  Pointwise positivity turns the uniform bound into the
qualitative nonvanishing statement. -/
theorem dirichletLOneInput_iff_noExceptionalSequence
    {L1 : ℤ → ℝ}
    (hpos : ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D) :
    DirichletLOneInput L1 ↔ NoExceptionalLOneSequence L1 := by
  constructor
  · rintro ⟨l, hlt, hbound⟩ ⟨D, hD, _hDpos, htend⟩
    have hev : ∀ᶠ n : ℕ in atTop, L1 (D n) < l :=
      (tendsto_order.1 htend).2 l hlt
    rcases eventually_atTop.1 hev with ⟨N, hN⟩
    linarith [hbound (D N) (hD N), hN N le_rfl]
  · intro hno
    by_contra hnot
    apply hno
    have hex : ∀ n : ℕ,
        ∃ D : ℤ, IsFrobeniusDiscriminant D ∧
          L1 D < 1 / ((n : ℝ) + 1) := by
      intro n
      have hl : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      by_contra h
      apply hnot
      refine ⟨1 / ((n : ℝ) + 1), hl, ?_⟩
      intro D hD
      by_contra hle
      exact h ⟨D, hD, lt_of_not_ge hle⟩
    choose D hD using hex
    refine ⟨D, (fun n => (hD n).1), (fun n => hpos (D n) (hD n).1), ?_⟩
    exact squeeze_zero (fun n => (hpos (D n) (hD n).1).le)
      (fun n => le_of_lt (hD n).2) tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The `L`-one input from the formula and the absence of an exceptional
sequence.**  Pointwise positivity is derived from the class-number formula, so
the only `L`-specific input is `NoExceptionalLOneSequence`. -/
theorem dirichletLOneInput_of_classNumberFormula
    {classNumber L1 weight : ℤ → ℝ}
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hclass : OrderClassNumberPositive classNumber)
    (hno : NoExceptionalLOneSequence L1) :
    DirichletLOneInput L1 :=
  (dirichletLOneInput_iff_noExceptionalSequence
    (L1_pos_of_dirichletFormula hformula hw hclass)).mpr hno

/-- An explicit form of the preceding reduction. -/
theorem exists_dirichletLOneLower_of_classNumberFormula
    {classNumber L1 weight : ℤ → ℝ}
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hclass : OrderClassNumberPositive classNumber)
    (hno : NoExceptionalLOneSequence L1) :
    ∃ l : ℝ, DirichletLOneLower L1 l :=
  dirichletLOneInput_of_classNumberFormula hformula hw hclass hno

/-! ## 3. Reduction to the Siegel trace leaf -/

/-- **The trace leaf from the standard class-number formula and an explicit
`L`-lower bound.**  The formula lower bound is derived from the unnormalized
Dirichlet formula; no additional class-number hypothesis is introduced. -/
theorem hurwitzSiegelLowerTrace_of_classNumberFormula
    {p : ℕ → ℕ} {hurwitz classNumber L1 weight : ℤ → ℝ} {l : ℝ}
    (hp : ∀ n, 0 < p n)
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight)
    (hl : 0 < l)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D) :
    HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) :=
  hurwitzSiegelLowerTrace_of_formula hp hl
    (hurwitzClassNumberFormulaLower_of_dirichletFormula hformula hw hdom) hL

/-- **The trace leaf from the formula plus the qualitative `L`-one input.**
The lower-bound constant `l` is produced from the absence of an exceptional
sequence. -/
theorem exists_hurwitzSiegelLowerTrace_of_classNumberFormula
    {p : ℕ → ℕ} {hurwitz classNumber L1 weight : ℤ → ℝ}
    (hp : ∀ n, 0 < p n)
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hclass : OrderClassNumberPositive classNumber)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight)
    (hno : NoExceptionalLOneSequence L1) :
    ∃ l : ℝ, 0 < l ∧
      HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) := by
  obtain ⟨l, hDL⟩ :=
    exists_dirichletLOneLower_of_classNumberFormula hformula hw hclass hno
  exact ⟨l, hDL.1,
    hurwitzSiegelLowerTrace_of_classNumberFormula hp hformula hw hdom hDL.1 hDL.2⟩

/-! ## 4. The bundled class-number input -/

/-- **The smallest explicit class-number input.**  It consists of the standard
Dirichlet formula, positivity of the unit weight, positivity of the class
number, and the domination of the weighted class number by the Hurwitz class
number.  All four are properties of the arithmetic objects, not of the curve
model. -/
structure DirichletClassNumberInput (hurwitz L1 : ℤ → ℝ) where
  /-- The imaginary quadratic order class number `h(D)`. -/
  classNumber : ℤ → ℝ
  /-- The unit weight `w(D)`. -/
  weight : ℤ → ℝ
  /-- The standard Dirichlet class-number formula. -/
  formula : DirichletClassNumberFormula classNumber L1 weight
  /-- The unit weight is positive. -/
  weight_pos : UnitWeightPositive weight
  /-- The class number is positive. -/
  classNumber_pos : OrderClassNumberPositive classNumber
  /-- The Hurwitz class number dominates the weighted class number. -/
  hurwitz_dominates : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight

namespace DirichletClassNumberInput

/-- The formula lower bound carried by the bundle. -/
theorem hurwitzFormulaLower {hurwitz L1 : ℤ → ℝ}
    (D : DirichletClassNumberInput hurwitz L1) :
    HurwitzClassNumberFormulaLower hurwitz L1 classNumberFormulaConstant :=
  hurwitzClassNumberFormulaLower_of_dirichletFormula
    D.formula D.weight_pos D.hurwitz_dominates

/-- The pointwise positivity of the `L`-value carried by the bundle. -/
theorem L1_pos {hurwitz L1 : ℤ → ℝ}
    (D : DirichletClassNumberInput hurwitz L1) :
    ∀ E : ℤ, IsFrobeniusDiscriminant E → 0 < L1 E :=
  L1_pos_of_dirichletFormula D.formula D.weight_pos D.classNumber_pos

/-- The bundle plus the qualitative `L`-one input gives an explicit uniform
lower bound. -/
theorem exists_l_one_lower {hurwitz L1 : ℤ → ℝ}
    (D : DirichletClassNumberInput hurwitz L1)
    (hno : NoExceptionalLOneSequence L1) :
    ∃ l : ℝ, DirichletLOneLower L1 l :=
  exists_dirichletLOneLower_of_classNumberFormula
    D.formula D.weight_pos D.classNumber_pos hno

/-- The trace leaf from the bundle and an explicit lower bound `l`. -/
theorem siegelLowerTrace {p : ℕ → ℕ} {hurwitz L1 : ℤ → ℝ} {l : ℝ}
    (D : DirichletClassNumberInput hurwitz L1)
    (hp : ∀ n, 0 < p n) (hl : 0 < l)
    (hL : ∀ E : ℤ, IsFrobeniusDiscriminant E → l ≤ L1 E) :
    HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) :=
  hurwitzSiegelLowerTrace_of_classNumberFormula hp
    D.formula D.weight_pos D.hurwitz_dominates hl hL

/-- The trace leaf from the bundle and the qualitative `L`-one input. -/
theorem exists_siegelLowerTrace {p : ℕ → ℕ} {hurwitz L1 : ℤ → ℝ}
    (D : DirichletClassNumberInput hurwitz L1)
    (hp : ∀ n, 0 < p n) (hno : NoExceptionalLOneSequence L1) :
    ∃ l : ℝ, 0 < l ∧
      HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) :=
  exists_hurwitzSiegelLowerTrace_of_classNumberFormula hp
    D.formula D.weight_pos D.classNumber_pos D.hurwitz_dominates hno

end DirichletClassNumberInput

/-! ## 5. Reassembling the L27 bundle -/

/-- **Direct construction of `L27SiegelInputs` from the class-number formula.**
The Siegel field is derived from the standard formula, the weight, the
domination, and the explicit `L`-lower bound; the remaining fields are the same
geometric/Deuring data as in `RandomizedL27Siegel.toSiegelInputs`. -/
def toSiegelInputs_of_classNumberFormula {I : L27_1Inputs}
    (hurwitz L1 : ℤ → ℝ) (classNumber weight : ℤ → ℝ) {l θ : ℝ}
    (l_pos : 0 < l) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ)
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight)
    (l_one_lower : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D)
    (scale : HurwitzDiscriminantScale I.p I.smooth θ)
    (trace : DeuringTraceCountLower I.p I.orderCount hurwitz)
    (strata : JInvariantStratification I.p I.orderCount I.orderTop)
    (hp4 : ∀ n, 4 ≤ I.p n) : L27SiegelInputs I :=
  Cogentic.RandomizedL27Siegel.toSiegelInputs hurwitz L1 l_pos θ_pos kappa_le
    (hurwitzClassNumberFormulaLower_of_dirichletFormula hformula hw hdom)
    l_one_lower scale trace strata hp4

/-- **The trace leaf, together with the Siegel constant, from the bundle and
the qualitative `L`-one input.** -/
theorem exists_trace_of_classNumberInput {I : L27_1Inputs}
    {hurwitz L1 : ℤ → ℝ} (D : DirichletClassNumberInput hurwitz L1)
    (hno : NoExceptionalLOneSequence L1) :
    ∃ l : ℝ, 0 < l ∧
      HurwitzSiegelLowerTrace I.p hurwitz (classNumberFormulaConstant * l) :=
  D.exists_siegelLowerTrace (fun n => I.p_pos n) hno

/-! ## Axiom audit -/

#print axioms dedekindZeta_classNumberFormula
#print axioms dedekindZeta_residue_pos
#print axioms dirichletLFunction_one_ne_zero
#print axioms weightedClassNumber_eq_formulaConstant
#print axioms hurwitzClassNumberFormulaLower_of_dirichletFormula
#print axioms L1_pos_of_dirichletFormula
#print axioms dirichletLOneInput_iff_noExceptionalSequence
#print axioms dirichletLOneInput_of_classNumberFormula
#print axioms exists_dirichletLOneLower_of_classNumberFormula
#print axioms hurwitzSiegelLowerTrace_of_classNumberFormula
#print axioms exists_hurwitzSiegelLowerTrace_of_classNumberFormula
#print axioms DirichletClassNumberInput.hurwitzFormulaLower
#print axioms DirichletClassNumberInput.L1_pos
#print axioms DirichletClassNumberInput.exists_l_one_lower
#print axioms DirichletClassNumberInput.siegelLowerTrace
#print axioms DirichletClassNumberInput.exists_siegelLowerTrace
#print axioms toSiegelInputs_of_classNumberFormula
#print axioms exists_trace_of_classNumberInput

end

end Cogentic.RandomizedL27ClassNumber
