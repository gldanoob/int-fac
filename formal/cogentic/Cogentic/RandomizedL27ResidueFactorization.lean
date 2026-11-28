import Cogentic.RandomizedL27ClassNumberFormula
import Cogentic.RandomizedL34DedekindGRH
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# L27: the residue of `ζ_K` from the abelian factorization

`Cogentic.RandomizedL27ClassNumberFormula` isolated the analytic identity

`res_{s=1} ζ_K(s) = L(1, χ_D)`

as `DedekindZetaResidueIsQuadraticL`.  `Cogentic.RandomizedL34DedekindGRH`
introduced the abelian factorization hypothesis

`ζ_K(s) = ∏ i, L(s, χ i)`   for `s ≠ 1`

as `DedekindZetaFactorsIntoDirichletOffPole`.

This file closes the gap between the two: **if** the factorization has exactly
one factor equal to the Riemann zeta function and **if** the product of the
remaining factors at `1` is `L1 D`, **then** `res_{s=1} ζ_K = L1 D`.  The proof
is the elementary residue computation

`(s - 1) ζ_K(s) = ((s - 1) ζ(s)) · ∏_{i ≠ i₀} L(s, χ i) ⟶ 1 · ∏_{i ≠ i₀} L(1, χ i)`,

using Mathlib's `riemannZeta_residue_one`, the differentiability of the
nontrivial `L`-functions at `1`, and `LFunction_apply_one_ne_zero` for the
finiteness/nonvanishing of the remaining product.

## Exact residuals

Everything is reduced to the following two inputs, both independent of the
residue computation:

* `AbelianFactorizationHypothesis`: for each field the abelian factorization
  with a distinguished factor equal to `riemannZeta` and all other characters
  nontrivial;
* `QuadraticCharacterProduct L1`: the product of the other factors at `1`
  equals `L1 D`.

Given the first, the second is *equivalent* to
`DedekindZetaResidueIsQuadraticL L1`
(`dedekindZetaResidueIsQuadraticL_iff_factorization`).  Thus the residue
identity is reduced exactly to the product identity, with no analytic content
left.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL27ResidueFactorization

set_option linter.style.haveILetI false

open Filter
open scoped BigOperators Topology

open Cogentic.RandomizedL27ClassNumberFormula
open Cogentic.RandomizedL34DedekindGRH

noncomputable section

/-! ## 1. The product identity and the factorization data -/

/-- **The remaining product identity.**  The product of all `L`-factors other
than the distinguished Riemann-zeta factor, evaluated at `1`, is the quadratic
`L`-value `L1 D`.  This is the exact residual of the residue computation. -/
def QuadraticCharacterProduct
    (L1 : ℤ → ℝ)
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (i₀ : ι) (D : ℤ) : Prop :=
  (∏ i ∈ Finset.univ \ {i₀}, DirichletCharacter.LFunction (χ i) 1) = (L1 D : ℂ)

/-- **The principal character modulo `1` is the Riemann zeta function.**  This
is the concrete form of the distinguished factor: `χ i₀ = 1` at modulus `1`
has `L`-function `riemannZeta`. -/
theorem principal_LFunction_of_eq_one
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hN : N = 1) (hχ : χ = 1) :
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = riemannZeta s := by
  subst hN
  subst hχ
  intro s
  simp

/-- **An abelian factorization with a unique Riemann-zeta factor.**

`ζ_K(s) = ∏ i, L(s, χ i)` away from the pole, one distinguished index `i₀`
whose character is the principal character `1` at modulus `1` (hence its factor
is literally `riemannZeta`), and every other character nontrivial (hence entire
and nonzero at `1`). -/
structure AbelianFactorizationWithRiemannZeta
    (K : Type) [Field K] [NumberField K] where
  /-- The finite index set of the character family. -/
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  /-- The moduli of the characters. -/
  N : ι → ℕ
  [neZero : ∀ i, NeZero (N i)]
  /-- The Dirichlet characters of the abelian factorization. -/
  χ : ∀ i, DirichletCharacter ℂ (N i)
  /-- The distinguished index of the Riemann-zeta factor. -/
  i₀ : ι
  /-- The off-pole factorization `ζ_K = ∏ L(·, χ i)`, in the form of the
  hypothesis `DedekindZetaFactorsIntoDirichletOffPole` of L34. -/
  offPole : DedekindZetaFactorsIntoDirichletOffPole K ι N χ
  /-- The distinguished modulus is `1`. -/
  modulus_principal : N i₀ = 1
  /-- The distinguished character is the principal character. -/
  character_principal : χ i₀ = 1
  /-- Every other character is nontrivial. -/
  nontrivial : ∀ i, i ≠ i₀ → χ i ≠ 1

attribute [instance] AbelianFactorizationWithRiemannZeta.fintype
attribute [instance] AbelianFactorizationWithRiemannZeta.decEq
attribute [instance] AbelianFactorizationWithRiemannZeta.neZero

/-- The distinguished factor of an abelian factorization is the Riemann zeta
function. -/
theorem AbelianFactorizationWithRiemannZeta.principal
    {K : Type} [Field K] [NumberField K]
    (F : AbelianFactorizationWithRiemannZeta K) :
    ∀ s : ℂ, DirichletCharacter.LFunction (F.χ F.i₀) s = riemannZeta s :=
  principal_LFunction_of_eq_one F.modulus_principal F.character_principal

/-- **The abelian factorization hypothesis**, uniformly over all fields and
fundamental discriminants.  This input does not depend on `L1`. -/
def AbelianFactorizationHypothesis : Prop :=
  ∀ (D : ℤ) (K : Type) [Field K] [NumberField K],
    IsFundamentalDiscriminant D →
    NumberField.discr K = -D →
    NumberField.InfinitePlace.nrRealPlaces K = 0 →
    NumberField.InfinitePlace.nrComplexPlaces K = 1 →
    NumberField.Units.regulator K = 1 →
    Nonempty (AbelianFactorizationWithRiemannZeta K)

/-- **The exact residual of `DedekindZetaResidueIsQuadraticL`.**  For each field
and fundamental discriminant we require the factorization together with the
single product identity `QuadraticCharacterProduct L1`. -/
def DedekindZetaResidueFactorization (L1 : ℤ → ℝ) : Prop :=
  ∀ (D : ℤ) (K : Type) [Field K] [NumberField K],
    IsFundamentalDiscriminant D →
    NumberField.discr K = -D →
    NumberField.InfinitePlace.nrRealPlaces K = 0 →
    NumberField.InfinitePlace.nrComplexPlaces K = 1 →
    NumberField.Units.regulator K = 1 →
    ∃ F : AbelianFactorizationWithRiemannZeta K,
      QuadraticCharacterProduct L1 F.ι F.N F.χ F.i₀ D

/-! ## 2. Finiteness and nonvanishing of the remaining product -/

/-- **The product of the nontrivial factors at `1` is nonzero.**  This is the
finiteness part of the residue computation: Mathlib's
`LFunction_apply_one_ne_zero` says every nontrivial factor is nonzero at `1`,
and a finite product of nonzero complex numbers is nonzero. -/
theorem prod_LFunction_one_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)} {i₀ : ι}
    (hχ : ∀ i, i ≠ i₀ → χ i ≠ 1) :
    (∏ i ∈ Finset.univ \ {i₀}, DirichletCharacter.LFunction (χ i) 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi' : i ≠ i₀ := by
    simpa using (Finset.mem_sdiff.mp hi).2
  exact DirichletCharacter.LFunction_apply_one_ne_zero (hχ i hi')

/-- **`L1 D` is nonzero** under the product identity, since the product is
nonzero. -/
theorem L1_ne_zero_of_quadraticCharacterProduct
    {L1 : ℤ → ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)} {i₀ : ι} {D : ℤ}
    (hχ : ∀ i, i ≠ i₀ → χ i ≠ 1)
    (hprod : QuadraticCharacterProduct L1 ι N χ i₀ D) :
    L1 D ≠ 0 := by
  intro hzero
  apply prod_LFunction_one_ne_zero hχ
  rw [hprod, hzero]
  simp

/-! ## 3. The residue computation -/

/-- **The residue from the factorization.**  If `ζ_K = ∏ L(·, χ i)` off the
pole, one factor is `riemannZeta`, and every other character is nontrivial,
then

`res_{s=1} ζ_K = ∏_{i ≠ i₀} L(1, χ i)`.

The proof differentiates the simple pole of `ζ` from the finite product: along
real `s → 1⁺`, `(s - 1) ζ_K(s)` is the product of
`(s - 1) ζ(s) → 1` and the continuous product `∏_{i ≠ i₀} L(s, χ i)`. -/
theorem residue_eq_prod_of_factorization
    (K : Type) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)} {i₀ : ι}
    (hfac : ∀ s : ℂ, s ≠ 1 →
      NumberField.dedekindZeta K s = ∏ i, DirichletCharacter.LFunction (χ i) s)
    (hprincipal : ∀ s : ℂ, DirichletCharacter.LFunction (χ i₀) s = riemannZeta s)
    (hnontrivial : ∀ i, i ≠ i₀ → χ i ≠ 1) :
    (NumberField.dedekindZeta_residue K : ℂ) =
      ∏ i ∈ Finset.univ \ {i₀}, DirichletCharacter.LFunction (χ i) 1 := by
  have hζ : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      NumberField.dedekindZeta K (s : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
    simpa using NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hinj : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast (ne_of_gt hs)
  have hprincipal_res : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      DirichletCharacter.LFunction (χ i₀) (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    have h := riemannZeta_residue_one.comp hinj
    simpa only [Function.comp_def, hprincipal] using h
  have hcont : Tendsto (fun s : ℝ =>
      ∏ i ∈ Finset.univ \ {i₀}, DirichletCharacter.LFunction (χ i) (s : ℂ))
      (𝓝[>] (1 : ℝ))
      (𝓝 (∏ i ∈ Finset.univ \ {i₀}, DirichletCharacter.LFunction (χ i) 1)) := by
    refine tendsto_finsetProd (Finset.univ \ {i₀}) ?_
    intro i hi
    have hi' : i ≠ i₀ := by
      simpa using (Finset.mem_sdiff.mp hi).2
    have hstep : Tendsto
        ((fun z : ℂ => DirichletCharacter.LFunction (χ i) z) ∘
          (fun s : ℝ => (s : ℂ))) (𝓝 (1 : ℝ))
        (𝓝 (DirichletCharacter.LFunction (χ i) 1)) :=
      ((DirichletCharacter.differentiable_LFunction
        (hnontrivial i hi')).continuous.tendsto (1 : ℂ)).comp
        (Complex.continuous_ofReal.tendsto (1 : ℝ))
    simpa only [Function.comp_def] using hstep.mono_left nhdsWithin_le_nhds
  have hprod_lim : Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * (∏ i, DirichletCharacter.LFunction (χ i) (s : ℂ)))
      (𝓝[>] (1 : ℝ))
      (𝓝 (1 * ∏ i ∈ Finset.univ \ {i₀}, DirichletCharacter.LFunction (χ i) 1)) := by
    have hmul := hprincipal_res.mul hcont
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s _hs
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i₀)]
    ring
  have hζ' : Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * (∏ i, DirichletCharacter.LFunction (χ i) (s : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
    refine hζ.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (s : ℂ) ≠ 1 := by
      exact_mod_cast (ne_of_gt hs)
    rw [hfac (s : ℂ) hs1]
  have huniq := tendsto_nhds_unique hζ' hprod_lim
  simpa using huniq

/-- **The residue from bundled factorization data.** -/
theorem residue_eq_L1_of_factorizationData
    {K : Type} [Field K] [NumberField K]
    {L1 : ℤ → ℝ} {D : ℤ}
    (F : AbelianFactorizationWithRiemannZeta K)
    (hprod : QuadraticCharacterProduct L1 F.ι F.N F.χ F.i₀ D) :
    NumberField.dedekindZeta_residue K = L1 D := by
  apply Complex.ofReal_injective
  calc
    (NumberField.dedekindZeta_residue K : ℂ) =
        ∏ i ∈ Finset.univ \ {F.i₀},
          DirichletCharacter.LFunction (F.χ i) 1 :=
      residue_eq_prod_of_factorization K F.offPole F.principal F.nontrivial
    _ = (L1 D : ℂ) := hprod

/-! ## 4. The reduction of `DedekindZetaResidueIsQuadraticL` -/

/-- **The residue identity from the factorization and the product identity.** -/
theorem dedekindZetaResidueIsQuadraticL_of_factorization
    {L1 : ℤ → ℝ} (h : DedekindZetaResidueFactorization L1) :
    DedekindZetaResidueIsQuadraticL L1 := by
  intro D K hKfield hKnumber hD hdisc hreal hcomplex hreg
  letI := hKfield
  letI := hKnumber
  obtain ⟨F, hprod⟩ := h D K hD hdisc hreal hcomplex hreg
  exact residue_eq_L1_of_factorizationData F hprod

/-- **The product identity from the residue identity.**  Conversely, given the
abelian factorization (with unique Riemann-zeta factor) and the residue
identity, the product identity holds for free.  This is the precise sense in
which `DedekindZetaResidueIsQuadraticL` is *equivalent* to the product identity
once the factorization is known. -/
theorem quadraticCharacterProduct_of_residue
    {L1 : ℤ → ℝ} {D : ℤ} {K : Type} [Field K] [NumberField K]
    (F : AbelianFactorizationWithRiemannZeta K)
    (hres : NumberField.dedekindZeta_residue K = L1 D) :
    QuadraticCharacterProduct L1 F.ι F.N F.χ F.i₀ D := by
  have hprod := residue_eq_prod_of_factorization K F.offPole F.principal F.nontrivial
  change (∏ i ∈ Finset.univ \ {F.i₀},
    DirichletCharacter.LFunction (F.χ i) 1) = (L1 D : ℂ)
  rw [← hprod]
  exact_mod_cast hres

/-- **Strict reduction.**  Given the abelian factorization hypothesis with a
unique Riemann-zeta factor, the residue identity for `L1` is equivalent to the
single product identity `QuadraticCharacterProduct L1` for the factors.  No
analytic content remains: all of it is in `AbelianFactorizationHypothesis`. -/
theorem dedekindZetaResidueIsQuadraticL_iff_factorization
    {L1 : ℤ → ℝ} (hfac : AbelianFactorizationHypothesis) :
    DedekindZetaResidueIsQuadraticL L1 ↔ DedekindZetaResidueFactorization L1 := by
  constructor
  · intro hres D K hKfield hKnumber hD hdisc hreal hcomplex hreg
    letI := hKfield
    letI := hKnumber
    obtain ⟨F⟩ := hfac D K hD hdisc hreal hcomplex hreg
    refine ⟨F, ?_⟩
    exact quadraticCharacterProduct_of_residue F
      (hres D K hD hdisc hreal hcomplex hreg)
  · intro hres
    exact dedekindZetaResidueIsQuadraticL_of_factorization hres

/-! ## 5. The maximal-order class-number formula -/

/-- **The Dirichlet formula for maximal orders from the factorization and the
product identity.**  This composes the residue theorem above with
`fundamentalDirichletClassNumberFormula`; the only inputs are the geometric
field realization and the bundled factorization/product data. -/
theorem fundamentalDirichletClassNumberFormula_of_factorization
    {classNumber weight L1 : ℤ → ℝ}
    (hfield : FundamentalOrderFieldRealization classNumber weight)
    (hfac : DedekindZetaResidueFactorization L1) :
    ∀ D : ℤ, IsFundamentalDiscriminant D →
      classNumber D =
        (weight D / (2 * Real.pi)) * Real.sqrt (D : ℝ) * L1 D :=
  fundamentalDirichletClassNumberFormula
    ⟨hfield, dedekindZetaResidueIsQuadraticL_of_factorization hfac⟩

/-- **The same formula at one fundamental discriminant**, with the factorization
data supplied explicitly for the field `K`. -/
theorem fundamentalClassNumberFormula_of_factorizationData
    (K : Type) [Field K] [NumberField K]
    {D : ℤ} {classNumber weight L1 : ℤ → ℝ}
    (hD : IsFundamentalDiscriminant D)
    (hdisc : NumberField.discr K = -D)
    (hclass : (NumberField.classNumber K : ℝ) = classNumber D)
    (hweight : (NumberField.Units.torsionOrder K : ℝ) = weight D)
    (hreal : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1)
    (hreg : NumberField.Units.regulator K = 1)
    (F : AbelianFactorizationWithRiemannZeta K)
    (hprod : QuadraticCharacterProduct L1 F.ι F.N F.χ F.i₀ D) :
    classNumber D =
      (weight D / (2 * Real.pi)) * Real.sqrt (D : ℝ) * L1 D :=
  fundamentalClassNumberFormula K hdisc hclass hweight hreal hcomplex hreg
    (residue_eq_L1_of_factorizationData F hprod)
    (isFundamentalDiscriminant_pos hD)

/-! ## Axiom audit -/

#print axioms residue_eq_prod_of_factorization
#print axioms prod_LFunction_one_ne_zero
#print axioms L1_ne_zero_of_quadraticCharacterProduct
#print axioms residue_eq_L1_of_factorizationData
#print axioms dedekindZetaResidueIsQuadraticL_of_factorization
#print axioms quadraticCharacterProduct_of_residue
#print axioms dedekindZetaResidueIsQuadraticL_iff_factorization
#print axioms fundamentalDirichletClassNumberFormula_of_factorization
#print axioms fundamentalClassNumberFormula_of_factorizationData

end

end Cogentic.RandomizedL27ResidueFactorization
