import Cogentic.RandomizedL27ClassNumber
import Cogentic.RandomizedL27LOneSiegel
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Data.Nat.Totient

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

/-!
# L27: discharging the class-number formula for maximal and non-maximal orders

`Cogentic.RandomizedL27ClassNumber` isolated the *unnormalized* Dirichlet
formula

`h(D) = (w(D)/(2π)) · L(1, χ_D) · √D`

as the input `DirichletClassNumberFormula`, together with the unit weight
`w(D)`, the positivity of the order class number, and the domination of the
weighted class number by the Hurwitz class number.  This file tests how much of
that input Mathlib can actually supply, and states exactly what is left.

## 1. The maximal orders

Mathlib proves the residue formula for the Dedekind zeta function of an
arbitrary number field `K`,

`res_{s=1} ζ_K(s) =
  2^{r₁} (2π)^{r₂} Reg(K) h(K) / (w(K) √|disc K|)`,

as `NumberField.dedekindZeta_residue_def`, and proves that `(s-1) ζ_K(s)` tends
to this residue as `s → 1⁺`
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`).  For an imaginary
quadratic field `r₁ = 0`, `r₂ = 1`, `Reg = 1`, and the residue becomes

`res_{s=1} ζ_K(s) = 2π h(K) / (w(K) √|disc K|)`.

We prove this simplification (`classNumber_eq_residue_of_imaginaryQuadratic`),
then isolate the single *analytic* identification that Mathlib does not
contain, namely `res_{s=1} ζ_K(s) = L(1, χ_D)` for the quadratic character of
`K = ℚ(√-D)`, as `DedekindZetaResidueIsQuadraticL`.  The standard invariant
computation of the maximal order (`disc = -D`, `classNumber = h(D)`,
`torsionOrder = w(D)`, `r₁ = 0`, `r₂ = 1`, `Reg = 1`) is
`FundamentalOrderFieldRealization`; the two together are
`FundamentalOrderRealization`.  The reduction
`fundamentalDirichletClassNumberFormula` derives the Dirichlet formula on
fundamental discriminants from that realization.

Mathlib does **not** construct `ℚ(√-D)`, does not identify its Dedekind zeta
with `ζ(s) L(s, χ_D)`, and hence does not prove `res = L(1, χ_D)`.  The latter
is the exact missing lemma; it is the only analytic input in this section.

## 2. The non-maximal orders

For a non-fundamental discriminant `D = D₀ f²` (with `D₀` fundamental and
`f > 1`), the order of discriminant `-D` is non-maximal, and the Dirichlet
formula acquires the conductor factor

`h(D)/w(D) = (√D · L(1, χ_D) / (2π)) · ∏_{p | f} (1 - χ_D(p)/p)`.

The Hurwitz class number is the `w/2`-weighted sum over the orders of
discriminant `-D`:

`H(D) = Σ_{d² | D} h(D/d²)/w_half(D/d²)
     = Σ_{g | f} 2 · h(D₀ g²)/w(D₀ g²)`.

Both facts are stated as the explicit order/conductor inputs
`HurwitzOrderDecomposition` and `NonMaximalOrderConductorFormula`, bundled in
`ClassNumberFormulaInput` together with the standard cover
`OrderConductorCover`, the elementary product bound
`ConductorProductGeometric`, and the character invariance `L1OrderInvariant`.
From them we prove the lower bound

`H(D) ≥ (1/π) √D L(1, χ_D) ≥ (1/(2π)) √D L(1, χ_D)`

by comparing the conductor product with `φ(g)/g` and using
`Σ_{g | f} φ(g) = f` (`Nat.sum_totient`).  This is
`hurwitzClassNumberFormulaLower_of_orderConductor`, and it is the reduction to
`HurwitzClassNumberFormulaLower` with the canonical constant `1/(2π)`.

Thus the class-number formula part of L27 is reduced to:

* the Mathlib residue formula plus the standard invariants of the maximal
  imaginary quadratic order (with `res = L(1, χ_D)` the only analytic gap);
* the order/conductor formula for non-maximal orders;
* the Hurwitz order decomposition.

## 3. Siegel is not assumed

The `L(1, χ_D)` lower bound is **not** derived here.  `SiegelLOneLower` and
`NoExceptionalLOneSequence` remain the separate deep input of
`Cogentic.RandomizedL27LOneSiegel`, and the earlier
`brauerSiegelLower_insufficient_for_constant` shows that the class-number
formula alone (even with the classical logarithmic Brauer–Siegel loss) cannot
produce the constant L27 needs.  The capstone at the end of this file takes the
Siegel input explicitly and re-uses the existing trace-leaf reduction.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No class number,
curve count, or loss is set to zero.
-/

namespace Cogentic.RandomizedL27ClassNumberFormula

open Filter Real
open scoped BigOperators Topology
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27ClassNumber
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27LOneSiegel
open Cogentic.RandomizedL27Siegel

noncomputable section

/-! ## 1. Mathlib's residue formula and the imaginary quadratic simplification -/

/-- Mathlib's residue formula, re-exported with the invariant notation. -/
theorem dedekindZeta_residue_def (K : Type*) [Field K] [NumberField K] :
    NumberField.dedekindZeta_residue K =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * (NumberField.classNumber K : ℝ)) /
        ((NumberField.Units.torsionOrder K : ℝ) *
          Real.sqrt |(NumberField.discr K : ℝ)|) :=
  NumberField.dedekindZeta_residue_def K

/-- Mathlib's residue formula in limit form. -/
theorem tendsto_sub_one_mul_dedekindZeta (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ => (s - 1) * NumberField.dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K)) :=
  NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K

/-- **The residue of an imaginary quadratic field.**  With `r₁ = 0`, `r₂ = 1`
and `Reg = 1`, Mathlib's residue formula reduces to
`res = 2π h / (w √|disc|)`. -/
theorem residue_eq_two_pi_mul_classNumber_div
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1)
    (hreg : NumberField.Units.regulator K = 1) :
    NumberField.dedekindZeta_residue K =
      (2 * Real.pi * (NumberField.classNumber K : ℝ)) /
        ((NumberField.Units.torsionOrder K : ℝ) *
          Real.sqrt |(NumberField.discr K : ℝ)|) := by
  rw [dedekindZeta_residue_def, hreal, hcomplex, hreg]
  norm_num [pow_one]

/-- **The class number from the residue.**  For an imaginary quadratic field,
`h = w √|disc| res / (2π)`. -/
theorem classNumber_eq_residue_of_imaginaryQuadratic
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1)
    (hreg : NumberField.Units.regulator K = 1) :
    (NumberField.classNumber K : ℝ) =
      (NumberField.Units.torsionOrder K : ℝ) *
        Real.sqrt |(NumberField.discr K : ℝ)| *
        NumberField.dedekindZeta_residue K / (2 * Real.pi) := by
  rw [residue_eq_two_pi_mul_classNumber_div K hreal hcomplex hreg]
  have hw : (NumberField.Units.torsionOrder K : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.Units.torsionOrder_pos K).ne'
  have hd : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := by
    refine (Real.sqrt_pos.mpr ?_).ne'
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  field_simp

/-! ## 2. Fundamental discriminants -/

/-- **A positive fundamental discriminant.**  `D > 0` is a fundamental
discriminant when `-D` is the discriminant of an imaginary quadratic field:
either `D ≡ 3 (mod 4)` and `D` is squarefree, or `D = 4m` with `m` squarefree
and `m ≡ 1, 2 (mod 4)`.  The sign convention matches `IsFrobeniusDiscriminant`:
the Hurwitz class number is `H(-D)`. -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  0 < D ∧
    ((D % 4 = 3 ∧ Squarefree D) ∨
      (D % 4 = 0 ∧ Squarefree (D / 4) ∧ (D / 4 % 4 = 1 ∨ D / 4 % 4 = 2)))

/-- A fundamental discriminant is positive. -/
theorem isFundamentalDiscriminant_pos {D : ℤ}
    (h : IsFundamentalDiscriminant D) : 0 < D :=
  h.1

/-- **A fundamental discriminant is a Frobenius discriminant.**  This is the
support bridge: the class-number formula on fundamental discriminants is
available on the same support as the Siegel leaf. -/
theorem isFrobeniusDiscriminant_of_fundamental {D : ℤ}
    (h : IsFundamentalDiscriminant D) : IsFrobeniusDiscriminant D := by
  rcases h with ⟨hDpos, hcases⟩
  rcases hcases with ⟨hmod, _hsq⟩ | ⟨hmod, _hsq, _hmod4⟩
  · -- `D = 4p - 1` with `p = (D + 1) / 4`.
    have hD : D = 4 * ((D + 1) / 4) - 1 := by omega
    have hp : 0 < ((D + 1) / 4).toNat := by omega
    refine ⟨((D + 1) / 4).toNat, hp, 1, ?_, ?_⟩
    · unfold traceDisc
      have hcast : ((((D + 1) / 4).toNat : ℕ) : ℤ) = (D + 1) / 4 := by
        simp [Int.toNat_of_nonneg (by omega : 0 ≤ (D + 1) / 4)]
      rw [hcast]
      omega
    · unfold traceDisc
      have hcast : ((((D + 1) / 4).toNat : ℕ) : ℤ) = (D + 1) / 4 := by
        simp [Int.toNat_of_nonneg (by omega : 0 ≤ (D + 1) / 4)]
      rw [hcast]
      omega
  · -- `D = 4p` with `p = D / 4`.
    have hD : D = 4 * (D / 4) := by omega
    have hp : 0 < (D / 4).toNat := by omega
    refine ⟨(D / 4).toNat, hp, 0, ?_, ?_⟩
    · unfold traceDisc
      have hcast : ((((D / 4).toNat : ℕ) : ℤ)) = D / 4 := by
        simp [Int.toNat_of_nonneg (by omega : 0 ≤ D / 4)]
      rw [hcast]
      omega
    · unfold traceDisc
      have hcast : ((((D / 4).toNat : ℕ) : ℤ)) = D / 4 := by
        simp [Int.toNat_of_nonneg (by omega : 0 ≤ D / 4)]
      rw [hcast]
      omega

/-! ## 3. The maximal-order realization -/

/-- **The maximal-order field realization.**  For every fundamental
discriminant `D`, there is a number field `K` whose ring of integers is the
maximal order of the imaginary quadratic field `ℚ(√-D)`, together with the
standard invariants `disc K = -D`, `h(K) = classNumber D`,
`w(K) = weight D`, `r₁ = 0`, `r₂ = 1`, `Reg = 1`.

Mathlib does not construct `ℚ(√-D)`, so this realization is an explicit
geometric input.  It contains no analysis. -/
def FundamentalOrderFieldRealization
    (classNumber weight : ℤ → ℝ) : Prop :=
  ∀ D : ℤ, IsFundamentalDiscriminant D →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      NumberField.discr K = -D ∧
      (NumberField.classNumber K : ℝ) = classNumber D ∧
      (NumberField.Units.torsionOrder K : ℝ) = weight D ∧
      NumberField.InfinitePlace.nrRealPlaces K = 0 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 1 ∧
      NumberField.Units.regulator K = 1

/-- **The exact missing analytic lemma.**  For the maximal order of
`ℚ(√-D)`, the residue of the Dedekind zeta function at `1` is the quadratic
`L`-value `L(1, χ_D)`.

Mathlib has the residue formula
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) but not the
factorization `ζ_K(s) = ζ(s) L(s, χ_D)` nor the construction of the Kronecker
character `χ_D`.  This is therefore the one analytic identification that is
kept as a named input. -/
def DedekindZetaResidueIsQuadraticL (L1 : ℤ → ℝ) : Prop :=
  ∀ (D : ℤ) (K : Type) [Field K] [NumberField K],
    IsFundamentalDiscriminant D →
    NumberField.discr K = -D →
    NumberField.InfinitePlace.nrRealPlaces K = 0 →
    NumberField.InfinitePlace.nrComplexPlaces K = 1 →
    NumberField.Units.regulator K = 1 →
    NumberField.dedekindZeta_residue K = L1 D

/-- **The standard maximal-order realization.**  It is the field realization
together with the single analytic identification `res = L(1, χ_D)`. -/
def FundamentalOrderRealization
    (classNumber weight L1 : ℤ → ℝ) : Prop :=
  FundamentalOrderFieldRealization classNumber weight ∧
    DedekindZetaResidueIsQuadraticL L1

/-- **The Dirichlet formula at one fundamental discriminant**, derived from
Mathlib's residue formula and the maximal-order realization. -/
theorem fundamentalClassNumberFormula
    (K : Type*) [Field K] [NumberField K]
    {D : ℤ} {classNumber weight L1 : ℤ → ℝ}
    (hdisc : NumberField.discr K = -D)
    (hclass : (NumberField.classNumber K : ℝ) = classNumber D)
    (hweight : (NumberField.Units.torsionOrder K : ℝ) = weight D)
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1)
    (hreg : NumberField.Units.regulator K = 1)
    (hres : NumberField.dedekindZeta_residue K = L1 D)
    (hDpos : 0 < D) :
    classNumber D =
      (weight D / (2 * Real.pi)) * Real.sqrt (D : ℝ) * L1 D := by
  have h := classNumber_eq_residue_of_imaginaryQuadratic K hreal hcomplex hreg
  rw [hclass, hweight, hres, hdisc] at h
  have hsqrt : Real.sqrt |(((-D : ℤ) : ℝ))| = Real.sqrt (D : ℝ) := by
    rw [Int.cast_neg, abs_neg, abs_of_pos (by exact_mod_cast hDpos)]
  rw [hsqrt] at h
  rw [h]
  ring

/-- The same formula in the `√|disc|` normalization, matching
`dedekindZeta_residue` directly. -/
theorem fundamentalClassNumberFormula_abs
    (K : Type*) [Field K] [NumberField K]
    {D : ℤ} {classNumber weight L1 : ℤ → ℝ}
    (hdisc : NumberField.discr K = -D)
    (hclass : (NumberField.classNumber K : ℝ) = classNumber D)
    (hweight : (NumberField.Units.torsionOrder K : ℝ) = weight D)
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1)
    (hreg : NumberField.Units.regulator K = 1)
    (hres : NumberField.dedekindZeta_residue K = L1 D)
    (hDpos : 0 < D) :
    classNumber D =
      (weight D / (2 * Real.pi)) * Real.sqrt |(((-D : ℤ) : ℝ))| * L1 D := by
  rw [fundamentalClassNumberFormula K hdisc hclass hweight hreal hcomplex hreg
    hres hDpos]
  have habs : |(((-D : ℤ) : ℝ))| = (D : ℝ) := by
    rw [Int.cast_neg, abs_neg, abs_of_pos (by exact_mod_cast hDpos)]
  rw [habs]

/-- **The Dirichlet formula at a fundamental discriminant from the residue
identification alone.**  This wrapper shows that the only analytic input is
`DedekindZetaResidueIsQuadraticL`. -/
theorem fundamentalClassNumberFormula_of_quadraticL
    (K : Type) [Field K] [NumberField K]
    {D : ℤ} {classNumber weight L1 : ℤ → ℝ}
    (hD : IsFundamentalDiscriminant D)
    (hdisc : NumberField.discr K = -D)
    (hclass : (NumberField.classNumber K : ℝ) = classNumber D)
    (hweight : (NumberField.Units.torsionOrder K : ℝ) = weight D)
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1)
    (hreg : NumberField.Units.regulator K = 1)
    (hres : DedekindZetaResidueIsQuadraticL L1) :
    classNumber D =
      (weight D / (2 * Real.pi)) * Real.sqrt (D : ℝ) * L1 D :=
  fundamentalClassNumberFormula K hdisc hclass hweight hreal hcomplex hreg
    (hres D K hD hdisc hreal hcomplex hreg) (isFundamentalDiscriminant_pos hD)

/-- **The Dirichlet formula on fundamental discriminants.**  This is the part
of `DirichletClassNumberFormula` that Mathlib's residue theorem reaches: the
maximal orders of imaginary quadratic fields. -/
theorem fundamentalDirichletClassNumberFormula
    {classNumber weight L1 : ℤ → ℝ}
    (hrealize : FundamentalOrderRealization classNumber weight L1) :
    ∀ D : ℤ, IsFundamentalDiscriminant D →
      classNumber D =
        (weight D / (2 * Real.pi)) * Real.sqrt (D : ℝ) * L1 D := by
  intro D hD
  obtain ⟨hfield, hres⟩ := hrealize
  obtain ⟨K, hKfield, hKnumber, hdisc, hclass, hweight, hreal, hcomplex,
    hreg⟩ := hfield D hD
  letI := hKfield
  letI := hKnumber
  exact fundamentalClassNumberFormula_of_quadraticL K hD hdisc hclass hweight
    hreal hcomplex hreg hres

/-! ## 4. The order/conductor input for non-maximal orders -/

/-- **The Hurwitz order decomposition.**  For `D = D₀ f²` with `D₀` fundamental
and `f > 0`, the Hurwitz class number is the sum, over the orders of
discriminant `-D`, of `2 h/w` (equivalently `h/w_half`, where `w_half = w/2`):

`H(D) = Σ_{g | f} 2 · h(D₀ g²)/w(D₀ g²)`.

This is the standard relation
`H(D) = Σ_{d² | D} h(D/d²)/w_half(D/d²)`, with `g = f/d`. -/
def HurwitzOrderDecomposition
    (hurwitz classNumber weight : ℤ → ℝ) : Prop :=
  ∀ (D₀ : ℤ) (f : ℕ), IsFundamentalDiscriminant D₀ → 0 < f →
    hurwitz (D₀ * (f : ℤ) ^ 2) =
      ∑ g ∈ f.divisors,
        2 * (classNumber (D₀ * (g : ℤ) ^ 2) /
          weight (D₀ * (g : ℤ) ^ 2))

/-- **The weighted order class-number formula with the conductor factor.**
For `D = D₀ f²`, the weighted class number of the order of discriminant `-D` is

`h(D)/w(D) = (√D · L(1, χ_D) / (2π)) · ∏_{p | f} (1 - χ_D(p)/p)`.

The product is kept abstract as `conductorProduct D₀ f`; the next input says
that it dominates the trivial Euler product. -/
def WeightedOrderConductorFormula
    (classNumber weight L1 : ℤ → ℝ) (conductorProduct : ℤ → ℕ → ℝ) : Prop :=
  ∀ (D₀ : ℤ) (f : ℕ), IsFundamentalDiscriminant D₀ → 0 < f →
    classNumber (D₀ * (f : ℤ) ^ 2) / weight (D₀ * (f : ℤ) ^ 2) =
      Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) *
          L1 (D₀ * (f : ℤ) ^ 2) / (2 * Real.pi) *
        conductorProduct D₀ f

/-- **The quadratic character does not change when passing to an order.**
`L1(D₀ f²) = L1(D₀)`: the Kronecker character of `-D₀ f²` is the Kronecker
character of the fundamental discriminant `-D₀`. -/
def L1OrderInvariant (L1 : ℤ → ℝ) : Prop :=
  ∀ (D₀ : ℤ) (f : ℕ), IsFundamentalDiscriminant D₀ → 0 < f →
    L1 (D₀ * (f : ℤ) ^ 2) = L1 D₀

/-- **The conductor product dominates the trivial Euler product.**  Each local
factor `1 - χ(p)/p` is at least `1 - 1/p`, so the product is at least
`φ(f)/f`. -/
def ConductorProductGeometric (conductorProduct : ℤ → ℕ → ℝ) : Prop :=
  ∀ (D₀ : ℤ) (f : ℕ), IsFundamentalDiscriminant D₀ → 0 < f →
    (Nat.totient f : ℝ) / (f : ℝ) ≤ conductorProduct D₀ f

/-- The unit weight is positive on the orders of discriminant `-D₀ g²`. -/
def OrderWeightPositive (weight : ℤ → ℝ) : Prop :=
  ∀ (D₀ : ℤ) (g : ℕ), IsFundamentalDiscriminant D₀ → 0 < g →
    0 < weight (D₀ * (g : ℤ) ^ 2)

/-- The order class number is nonnegative on the orders of discriminant
`-D₀ g²`. -/
def OrderClassNumberNonneg (classNumber : ℤ → ℝ) : Prop :=
  ∀ (D₀ : ℤ) (g : ℕ), IsFundamentalDiscriminant D₀ → 0 < g →
    0 ≤ classNumber (D₀ * (g : ℤ) ^ 2)

/-- **Every Frobenius discriminant is `D₀ f²` for a fundamental `D₀`.**  This is
the standard order-conductor decomposition of a quadratic discriminant. -/
def OrderConductorCover : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D →
    ∃ (D₀ : ℤ) (f : ℕ), IsFundamentalDiscriminant D₀ ∧ 0 < f ∧
      D = D₀ * (f : ℤ) ^ 2

/-! ## 5. The reduction to the Hurwitz lower bound -/

/-- `√(D₀ g²) = g √D₀` for positive `D₀`. -/
theorem sqrt_int_mul_sq (A : ℤ) (g : ℕ) (hA : 0 ≤ A) :
    Real.sqrt ((A * (g : ℤ) ^ 2 : ℤ) : ℝ) =
      (g : ℝ) * Real.sqrt (A : ℝ) := by
  have hcast : ((A * (g : ℤ) ^ 2 : ℤ) : ℝ) = (A : ℝ) * (g : ℝ) ^ 2 := by
    push_cast
    ring
  rw [hcast, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- The elementary algebra behind the conductor sum: the factor `2` in the
Hurwitz decomposition and the factor `√(D₀g²) = g√D₀` combine into
`(√D/(π f)) · g · L1(D₀) · P`. -/
theorem two_mul_weighted_eq
    {D₀ : ℤ} {f g : ℕ} {L1 : ℤ → ℝ} {P : ℝ}
    (hD0 : 0 < D₀) (hf : 0 < f) (hg : 0 < g)
    (hL1 : L1 (D₀ * (g : ℤ) ^ 2) = L1 D₀) :
    2 * (Real.sqrt ((D₀ * (g : ℤ) ^ 2 : ℤ) : ℝ) *
          L1 (D₀ * (g : ℤ) ^ 2) / (2 * Real.pi) * P) =
      (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) /
          (Real.pi * (f : ℝ))) * ((g : ℝ) * (L1 D₀ * P)) := by
  rw [hL1, sqrt_int_mul_sq D₀ g hD0.le, sqrt_int_mul_sq D₀ f hD0.le]
  have hfR : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  field_simp

/-- **The `L`-value is nonnegative.**  At `f = 1` the weighted order formula is
the maximal-order formula; positivity of the class number and of the weight,
together with the positivity of the conductor product at `1`, force
`L1 D₀ ≥ 0`. -/
theorem L1_nonneg_of_orderConductor
    {classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    (hformula : WeightedOrderConductorFormula classNumber weight L1 conductorProduct)
    (hprod : ConductorProductGeometric conductorProduct)
    (hweight : OrderWeightPositive weight)
    (hclass : OrderClassNumberNonneg classNumber)
    {D₀ : ℤ} (hD : IsFundamentalDiscriminant D₀) :
    0 ≤ L1 D₀ := by
  have hD0pos : 0 < D₀ := isFundamentalDiscriminant_pos hD
  have hw : 0 < weight D₀ := by
    simpa using hweight D₀ 1 hD one_pos
  have hc : 0 ≤ classNumber D₀ := by
    simpa using hclass D₀ 1 hD one_pos
  have h : classNumber D₀ / weight D₀ =
      Real.sqrt (D₀ : ℝ) * L1 D₀ / (2 * Real.pi) * conductorProduct D₀ 1 := by
    simpa using hformula D₀ 1 hD one_pos
  have hleft : 0 ≤ classNumber D₀ / weight D₀ := div_nonneg hc hw.le
  have hP : 0 < conductorProduct D₀ 1 := by
    have hp := hprod D₀ 1 hD one_pos
    norm_num at hp
    linarith
  have hfac : 0 < Real.sqrt (D₀ : ℝ) / (2 * Real.pi) * conductorProduct D₀ 1 := by
    positivity
  rw [h] at hleft
  have hleft' : 0 ≤ (Real.sqrt (D₀ : ℝ) / (2 * Real.pi) *
      conductorProduct D₀ 1) * L1 D₀ := by
    convert hleft using 1 <;> ring
  exact nonneg_of_mul_nonneg_right hleft' hfac

/-- **The Hurwitz lower bound from the order/conductor input.**  The Hurwitz
decomposition, the weighted order class-number formula, the invariance of the
quadratic character, and the Euler-product lower bound give

`H(D) ≥ (1/π) √D L(1, χ_D) ≥ (1/(2π)) √D L(1, χ_D)`.

The second inequality uses only `L1 D ≥ 0`, which is derived above. -/
theorem hurwitzClassNumberFormulaLower_of_orderConductor
    {hurwitz classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    (hcover : OrderConductorCover)
    (hdecomp : HurwitzOrderDecomposition hurwitz classNumber weight)
    (hformula : WeightedOrderConductorFormula classNumber weight L1 conductorProduct)
    (hL1inv : L1OrderInvariant L1)
    (hprod : ConductorProductGeometric conductorProduct)
    (hweight : OrderWeightPositive weight)
    (hclass : OrderClassNumberNonneg classNumber) :
    HurwitzClassNumberFormulaLower hurwitz L1 (1 / (2 * Real.pi)) := by
  intro D hD
  obtain ⟨D₀, f, hD0fund, hf, rfl⟩ := hcover D hD
  have hD0pos : 0 < D₀ := isFundamentalDiscriminant_pos hD0fund
  have hD0nonneg : (0 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD0pos.le
  have hfRpos : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hL1D0 : 0 ≤ L1 D₀ :=
    L1_nonneg_of_orderConductor hformula hprod hweight hclass hD0fund
  have hL1D : 0 ≤ L1 (D₀ * (f : ℤ) ^ 2) := by
    rw [hL1inv D₀ f hD0fund hf]
    exact hL1D0
  have hH := hdecomp D₀ f hD0fund hf
  rw [hH, ← Finset.mul_sum]
  have hterm (g : ℕ) (hg : g ∈ f.divisors) :
      2 * (classNumber (D₀ * (g : ℤ) ^ 2) /
          weight (D₀ * (g : ℤ) ^ 2)) =
        (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) /
            (Real.pi * (f : ℝ))) *
          ((g : ℝ) * (L1 D₀ * conductorProduct D₀ g)) := by
    have hgpos : 0 < g :=
      Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hg) hf
    have hform := hformula D₀ g hD0fund hgpos
    have hL1g := hL1inv D₀ g hD0fund hgpos
    rw [hform]
    exact two_mul_weighted_eq hD0pos hf hgpos hL1g
  have hsum_ge :
      (∑ g ∈ f.divisors,
          (g : ℝ) * (L1 D₀ * conductorProduct D₀ g)) ≥
        ∑ g ∈ f.divisors, L1 D₀ * (Nat.totient g : ℝ) := by
    apply Finset.sum_le_sum
    intro g hg
    have hgpos : 0 < g :=
      Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hg) hf
    have hgRpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
    have hPge : (Nat.totient g : ℝ) ≤ (g : ℝ) * conductorProduct D₀ g := by
      have hp := hprod D₀ g hD0fund hgpos
      rw [div_le_iff₀ hgRpos] at hp
      calc
        (Nat.totient g : ℝ) ≤ conductorProduct D₀ g * (g : ℝ) := hp
        _ = (g : ℝ) * conductorProduct D₀ g := by ring
    calc
      (g : ℝ) * (L1 D₀ * conductorProduct D₀ g) =
          L1 D₀ * ((g : ℝ) * conductorProduct D₀ g) := by ring
      _ ≥ L1 D₀ * (Nat.totient g : ℝ) :=
        mul_le_mul_of_nonneg_left hPge hL1D0
  have hsumphi : (∑ g ∈ f.divisors, (Nat.totient g : ℝ)) = (f : ℝ) := by
    rw [← Nat.cast_sum, Nat.sum_totient]
  calc
    2 * (∑ g ∈ f.divisors,
        classNumber (D₀ * (g : ℤ) ^ 2) / weight (D₀ * (g : ℤ) ^ 2)) =
        ∑ g ∈ f.divisors,
          2 * (classNumber (D₀ * (g : ℤ) ^ 2) /
            weight (D₀ * (g : ℤ) ^ 2)) := by
      rw [Finset.mul_sum]
    _ = ∑ g ∈ f.divisors,
          (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) /
              (Real.pi * (f : ℝ))) *
            ((g : ℝ) * (L1 D₀ * conductorProduct D₀ g)) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact hterm g hg
    _ = (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) /
          (Real.pi * (f : ℝ))) *
        ∑ g ∈ f.divisors,
          (g : ℝ) * (L1 D₀ * conductorProduct D₀ g) := by
      rw [Finset.mul_sum]
    _ ≥ (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) /
          (Real.pi * (f : ℝ))) *
        ∑ g ∈ f.divisors, L1 D₀ * (Nat.totient g : ℝ) := by
      apply mul_le_mul_of_nonneg_left hsum_ge
      positivity
    _ = (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) /
          (Real.pi * (f : ℝ))) * (L1 D₀ * (f : ℝ)) := by
      rw [← Finset.mul_sum, hsumphi]
    _ = (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) / Real.pi) * L1 D₀ := by
      field_simp
    _ ≥ (1 / (2 * Real.pi)) * L1 (D₀ * (f : ℤ) ^ 2) *
          Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) := by
      rw [hL1inv D₀ f hD0fund hf]
      have hcoef : (1 : ℝ) / (2 * Real.pi) ≤ 1 / Real.pi := by
        rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
        nlinarith [Real.pi_pos]
      have hmul : (1 / (2 * Real.pi)) * L1 D₀ ≤ (1 / Real.pi) * L1 D₀ :=
        mul_le_mul_of_nonneg_right hcoef hL1D0
      have hsq := mul_le_mul_of_nonneg_right hmul
        (Real.sqrt_nonneg ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ))
      calc
        (1 / (2 * Real.pi)) * L1 D₀ *
            Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) =
            ((1 / (2 * Real.pi)) * L1 D₀) *
              Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) := by ring
        _ ≤ ((1 / Real.pi) * L1 D₀) *
              Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) := hsq
        _ = (Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) / Real.pi) * L1 D₀ := by
          ring

/-! ## 6. Splitting off the maximal orders -/

/-- The conductor factor is normalized at `f = 1` (the empty product). -/
def ConductorProductNormalized (conductorProduct : ℤ → ℕ → ℝ) : Prop :=
  ∀ D₀ : ℤ, conductorProduct D₀ 1 = 1

/-- **The order-conductor formula for non-maximal orders only.**  This is the
part that Mathlib does not supply: for `f > 1`, the weighted class number gains
the conductor product `∏_{p | f} (1 - χ(p)/p)`. -/
def NonMaximalOrderConductorFormula
    (classNumber weight L1 : ℤ → ℝ) (conductorProduct : ℤ → ℕ → ℝ) : Prop :=
  ∀ (D₀ : ℤ) (f : ℕ), IsFundamentalDiscriminant D₀ → 1 < f →
    classNumber (D₀ * (f : ℤ) ^ 2) / weight (D₀ * (f : ℤ) ^ 2) =
      Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) *
          L1 (D₀ * (f : ℤ) ^ 2) / (2 * Real.pi) *
        conductorProduct D₀ f

/-- **The full weighted order formula from the maximal-order formula and the
non-maximal conductor formula.**  At `f = 1` the weighted formula is the
Dirichlet formula at the fundamental discriminant; at `f > 1` it is the
order-conductor input. -/
theorem weightedOrderConductorFormula_of_fundamental
    {classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    (hfund : ∀ D : ℤ, IsFundamentalDiscriminant D →
      classNumber D =
        (weight D / (2 * Real.pi)) * Real.sqrt (D : ℝ) * L1 D)
    (hnonmax : NonMaximalOrderConductorFormula classNumber weight L1 conductorProduct)
    (hweight : OrderWeightPositive weight)
    (hprod1 : ConductorProductNormalized conductorProduct) :
    WeightedOrderConductorFormula classNumber weight L1 conductorProduct := by
  intro D₀ f hD0 hf
  rcases eq_or_lt_of_le (Nat.one_le_of_lt hf) with hf1 | hf1
  · -- `f = 1`: the empty conductor product is `1`.
    rw [← hf1]
    have h := hfund D₀ hD0
    have hw : weight D₀ ≠ 0 := by
      simpa using (hweight D₀ 1 hD0 one_pos).ne'
    simp only [Nat.cast_one, one_pow, mul_one, hprod1 D₀]
    rw [h]
    field_simp [hw]
  · -- `f > 1`: the genuine conductor formula.
    exact hnonmax D₀ f hD0 hf1

/-- **The unweighted Dirichlet formula is the wrong statement for non-maximal
orders.**  If the conductor-free formula `DirichletClassNumberFormula` held at
`D = D₀ f²` together with the correct weighted order formula, then the
conductor product would have to be `1`.  This isolates exactly why the
non-fundamental case is not discharged by the residue theorem: the missing
factor is `∏(1 - χ(p)/p)`, not an analytic error term. -/
theorem conductorProduct_eq_one_of_dirichletFormula
    {classNumber weight L1 : ℤ → ℝ} {conductorProduct : ℤ → ℕ → ℝ}
    {D₀ : ℤ} {f : ℕ}
    (hdir : DirichletClassNumberFormula classNumber L1 weight)
    (hform : WeightedOrderConductorFormula classNumber weight L1 conductorProduct)
    (hD0 : IsFundamentalDiscriminant D₀) (hf : 0 < f)
    (hD : IsFrobeniusDiscriminant (D₀ * (f : ℤ) ^ 2))
    (hweight : 0 < weight (D₀ * (f : ℤ) ^ 2))
    (hL1 : 0 < L1 (D₀ * (f : ℤ) ^ 2)) :
    conductorProduct D₀ f = 1 := by
  have hdir' := hdir (D₀ * (f : ℤ) ^ 2) hD
  have hform' := hform D₀ f hD0 hf
  have hw : weight (D₀ * (f : ℤ) ^ 2) ≠ 0 := hweight.ne'
  have hdiv : classNumber (D₀ * (f : ℤ) ^ 2) / weight (D₀ * (f : ℤ) ^ 2) =
      Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) *
        L1 (D₀ * (f : ℤ) ^ 2) / (2 * Real.pi) := by
    rw [hdir']
    field_simp [hw]
  rw [hdiv] at hform'
  have hbase : Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) *
      L1 (D₀ * (f : ℤ) ^ 2) / (2 * Real.pi) ≠ 0 := by
    have hDpos : (0 : ℝ) < ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast isFrobeniusDiscriminant_pos hD
    have hsqrt : 0 < Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) :=
      Real.sqrt_pos.mpr hDpos
    positivity
  have hEq :
      Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) *
          L1 (D₀ * (f : ℤ) ^ 2) / (2 * Real.pi) * conductorProduct D₀ f =
        Real.sqrt ((D₀ * (f : ℤ) ^ 2 : ℤ) : ℝ) *
          L1 (D₀ * (f : ℤ) ^ 2) / (2 * Real.pi) * 1 := by
    rw [mul_one, ← hform']
  exact mul_left_cancel₀ hbase hEq

/-! ## 7. The bundled class-number side -/

/-- **The class-number side of L27, split into its exact residuals.**

* `maximal` is the Mathlib residue computation for the maximal order, with the
  single analytic identification `res = L(1, χ_D)`;
* `nonmaximal` is the order/conductor formula for the non-maximal orders;
* `decomposition` is the Hurwitz order decomposition;
* `conductor_geometric` is `∏(1 - χ(p)/p) ≥ φ(f)/f`;
* `L1_invariant` says the quadratic character is unchanged by the conductor.

No Siegel hypothesis occurs here. -/
structure ClassNumberFormulaInput (hurwitz L1 : ℤ → ℝ) where
  /-- The order class number `h(D)`. -/
  classNumber : ℤ → ℝ
  /-- The full unit weight `w(D)`. -/
  weight : ℤ → ℝ
  /-- The conductor product `∏_{p | f} (1 - χ(p)/p)`. -/
  conductorProduct : ℤ → ℕ → ℝ
  /-- Every Frobenius discriminant is `D₀ f²`. -/
  cover : OrderConductorCover
  /-- The maximal-order realization from Mathlib's residue formula. -/
  maximal : FundamentalOrderRealization classNumber weight L1
  /-- The Hurwitz order decomposition. -/
  decomposition : HurwitzOrderDecomposition hurwitz classNumber weight
  /-- The non-maximal order/conductor formula. -/
  nonmaximal : NonMaximalOrderConductorFormula classNumber weight L1 conductorProduct
  /-- The conductor product dominates the trivial Euler product. -/
  conductor_geometric : ConductorProductGeometric conductorProduct
  /-- The conductor product is `1` at `f = 1`. -/
  conductor_one : ConductorProductNormalized conductorProduct
  /-- The quadratic character is unchanged by the conductor. -/
  L1_invariant : L1OrderInvariant L1
  /-- The unit weight is positive on order discriminants. -/
  weight_pos : OrderWeightPositive weight
  /-- The order class number is nonnegative on order discriminants. -/
  class_nonneg : OrderClassNumberNonneg classNumber

namespace ClassNumberFormulaInput

/-- **The Hurwitz class-number formula lower bound.**  This is the exact
`HurwitzClassNumberFormula` input of `Cogentic.RandomizedL27Siegel`, with the
canonical constant `1/(2π)`. -/
theorem hurwitzFormulaLower {hurwitz L1 : ℤ → ℝ}
    (D : ClassNumberFormulaInput hurwitz L1) :
    HurwitzClassNumberFormula hurwitz L1 := by
  have hfund := fundamentalDirichletClassNumberFormula D.maximal
  have hweighted : WeightedOrderConductorFormula D.classNumber D.weight L1
      D.conductorProduct :=
    weightedOrderConductorFormula_of_fundamental hfund D.nonmaximal
      D.weight_pos D.conductor_one
  have h := hurwitzClassNumberFormulaLower_of_orderConductor D.cover
    D.decomposition hweighted D.L1_invariant D.conductor_geometric
    D.weight_pos D.class_nonneg
  simpa [HurwitzClassNumberFormula, classNumberFormulaConstant] using h

/-- **The Siegel trace leaf from the class-number side plus the separate
Siegel input.**  The class-number part supplies `HurwitzClassNumberFormula`;
the deep analytic input `SiegelLOneLower` supplies the uniform `L`-one lower
bound.  The two are combined by `hurwitzSiegelLowerTrace_of_formula`. -/
theorem exists_siegelLowerTrace {p : ℕ → ℕ} {hurwitz L1 : ℤ → ℝ}
    (D : ClassNumberFormulaInput hurwitz L1)
    (hp : ∀ n, 0 < p n) (hS : SiegelLOneLower L1) :
    ∃ l : ℝ, 0 < l ∧
      HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) := by
  obtain ⟨l, hl, hbound⟩ := hS
  exact ⟨l, hl, hurwitzSiegelLowerTrace_of_formula hp hl D.hurwitzFormulaLower hbound⟩

/-- The explicit-constant form of the preceding theorem. -/
theorem siegelLowerTrace {p : ℕ → ℕ} {hurwitz L1 : ℤ → ℝ}
    (D : ClassNumberFormulaInput hurwitz L1)
    (hp : ∀ n, 0 < p n) {l : ℝ} (hl : 0 < l)
    (hbound : ∀ E : ℤ, IsFrobeniusDiscriminant E → l ≤ L1 E) :
    HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) :=
  hurwitzSiegelLowerTrace_of_formula hp hl D.hurwitzFormulaLower hbound

end ClassNumberFormulaInput

/-! ## 8. Siegel remains a separate input -/

/-- **The class-number formula alone cannot replace Siegel.**  Even the
classical Brauer–Siegel shape (a logarithmic loss) is compatible with the
absence of any constant Hurwitz lower bound, as proved in
`Cogentic.RandomizedL27LOneSiegel.brauerSiegelLower_insufficient_for_constant`.
This theorem records the consequence in the form used here: it is not the case
that every `BrauerSiegelLower` model admits a positive `c` with
`HurwitzSiegelLowerFrob`. -/
theorem classNumberFormula_alone_insufficient_for_siegel :
    ¬ ∀ hurwitz : ℤ → ℝ, BrauerSiegelLower hurwitz 1 →
      ∃ c : ℝ, 0 < c ∧ HurwitzSiegelLowerFrob hurwitz c := by
  intro h
  obtain ⟨hurwitz, hBS, hno⟩ := brauerSiegelLower_insufficient_for_constant
  exact hno (h hurwitz hBS)

/-- The separate Siegel input, in the two equivalent forms used downstream.
This is a re-export; it is not derived from the class-number formula. -/
theorem siegel_lOneLower_iff_noExceptional {L1 : ℤ → ℝ}
    (hpos : ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D) :
    SiegelLOneLower L1 ↔ NoExceptionalLOneSequence L1 :=
  siegelLOneLower_iff_noExceptional hpos

/-! ## Axiom audit -/

#print axioms dedekindZeta_residue_def
#print axioms tendsto_sub_one_mul_dedekindZeta
#print axioms residue_eq_two_pi_mul_classNumber_div
#print axioms classNumber_eq_residue_of_imaginaryQuadratic
#print axioms isFrobeniusDiscriminant_of_fundamental
#print axioms fundamentalClassNumberFormula
#print axioms fundamentalClassNumberFormula_abs
#print axioms fundamentalClassNumberFormula_of_quadraticL
#print axioms fundamentalDirichletClassNumberFormula
#print axioms sqrt_int_mul_sq
#print axioms two_mul_weighted_eq
#print axioms L1_nonneg_of_orderConductor
#print axioms hurwitzClassNumberFormulaLower_of_orderConductor
#print axioms weightedOrderConductorFormula_of_fundamental
#print axioms conductorProduct_eq_one_of_dirichletFormula
#print axioms ClassNumberFormulaInput.hurwitzFormulaLower
#print axioms ClassNumberFormulaInput.exists_siegelLowerTrace
#print axioms ClassNumberFormulaInput.siegelLowerTrace
#print axioms classNumberFormula_alone_insufficient_for_siegel
#print axioms siegel_lOneLower_iff_noExceptional

end

end Cogentic.RandomizedL27ClassNumberFormula
