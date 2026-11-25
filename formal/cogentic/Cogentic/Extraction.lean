import Cogentic.Rank
import Mathlib.Algebra.Module.Prod
import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-! Unit signs and local evaluation in the two-field extractor. -/

namespace Cogentic

open NumberField
open scoped BigOperators NumberField Matrix

/-- Vanishing of the unnormalized Helmert rows forces a constant vector. -/
theorem constant_of_helmert_rows (d : ℕ) (x : ℕ → ℝ)
    (rows : ∀ j, j+1 < d → ∑ i ∈ Finset.range (j+1), x i = (j+1 : ℕ) * x (j+1)) :
    ∀ j < d, x j = x 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    cases j with
    | zero => rfl
    | succ j =>
      have equal : ∑ i ∈ Finset.range (j+1), x i = ∑ _i ∈ Finset.range (j+1), x 0 :=
        Finset.sum_congr rfl fun i hi =>
          ih i (Finset.mem_range.mp hi) ((Finset.mem_range.mp hi).trans hj)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at equal
      exact mul_left_cancel₀ (by positivity : ((j+1 : ℕ) : ℝ) ≠ 0) ((rows j hj).symm.trans equal)

/-- Trivial multiplicative valuations at every finite prime give a unit of the
full ring of integers, by integrality of the element and its inverse. -/
theorem unit_of_finite_valuations {K : Type*} [Field K] [NumberField K]
    (x : K) (hx : x ≠ 0) (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v.valuation K x = 1) :
    ∃ u : (𝓞 K)ˣ, (u : K) = x := by
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x
    (fun v => (h v).le)
  obtain ⟨b, hb⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x⁻¹
    (fun v => by rw [map_inv₀, h v, inv_one])
  have ab : a*b = 1 := RingOfIntegers.coe_injective (by
    rw [map_mul, ha, hb, mul_inv_cancel₀ hx]
    rfl)
  exact ⟨⟨a, b, ab, (mul_comm b a).trans ab⟩, ha⟩

private theorem exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, WithZero.exp (f i)) = WithZero.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp only [Finset.prod_insert ha, Finset.sum_insert ha, WithZero.exp_add, ih]

/-- Local prime-ideal rows yield an actual unit, including the common valuation
offset of a nonmonic field generator. Rows may have arbitrary signed multiplicities. -/
theorem unit_from_incidence {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (g : K) (a : ι → K) (hg : g ≠ 0) (ha : ∀ i, a i ≠ 0) (E : ℕ) (c : ι → ℤ)
    (balance : ∑ i, c i = 0)
    (local_rows : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ∃ (offset target : ℤ) (row : ι → ℤ),
        v.valuation K g = WithZero.exp target ∧
        (∀ i, v.valuation K (a i) = WithZero.exp (offset + row i)) ∧
        ∑ i, c i * row i = -((E : ℤ)*target)) :
    ∃ u : (𝓞 K)ˣ, (u : K) = g^E * ∏ i, (a i)^(c i) := by
  apply unit_of_finite_valuations _ (mul_ne_zero (pow_ne_zero _ hg)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (ha i))))
  intro v
  obtain ⟨o, t, row, ht, hr, hsum⟩ := local_rows v
  have cancel : (E : ℤ)*t + ∑ i, c i*(o + row i) = 0 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, balance, zero_mul,
      zero_add, hsum, add_neg_cancel]
  simp only [map_mul, map_pow, map_prod, map_zpow₀, ht, hr, ← WithZero.exp_zsmul,
    ← WithZero.exp_nsmul, zsmul_eq_mul, nsmul_eq_mul, Int.cast_id, exp_sum, ← WithZero.exp_add, cancel,
    WithZero.exp_zero]

/-- A single real place suffices for a torsion field unit to have sign ±1. -/
theorem signed_of_torsion {K : Type*} [Field K] [NumberField K] (σ : K →+* ℝ) (u : (𝓞 K)ˣ)
    (h : u ∈ NumberField.Units.torsion K) : (u : K) = 1 ∨ (u : K) = -1 := by
  have hφ := (NumberField.Units.mem_torsion K).mp h (InfinitePlace.mk (Complex.ofRealHom.comp σ))
  have h_abs : |σ (u : K)| = 1 := by
    simpa [InfinitePlace.apply, Real.norm_eq_abs] using hφ
  rcases eq_or_eq_neg_of_abs_eq h_abs with hp | hn
  · left; exact σ.injective (by simpa using hp)
  · right; exact σ.injective (by simpa using hn)

/-- The product formula kills the common logarithm. This uses the genuine unit of
the full ring of integers and allows the real embedding in either parity of degree. -/
theorem signed_of_constant_logs {K : Type*} [Field K] [NumberField K]
    (σ : K →+* ℝ) (u : (𝓞 K)ˣ) (t : ℝ) (h : ∀ v : InfinitePlace K, Real.log (v (u : K)) = t) :
    (u : K) = 1 ∨ (u : K) = -1 := by
  classical
  have prod_formula := NumberField.Units.sum_mult_mul_log u
  simp_rw [h] at prod_formula
  rw [← Finset.sum_mul] at prod_formula
  have pos : 0 < ∑ v : InfinitePlace K, (v.mult : ℝ) :=
    Finset.sum_pos (fun v _ => by exact_mod_cast (InfinitePlace.mult_pos (w := v))) Finset.univ_nonempty
  have ht := (mul_eq_zero.mp prod_formula).resolve_left pos.ne'
  apply signed_of_torsion σ u
  apply NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mp
  ext v
  simp [NumberField.Units.dirichletUnitTheorem.logEmbedding_component, h, ht]

/-- A modular polynomial root defines evaluation even after inverting a family
of denominators, provided their values are units modulo N. -/
noncomputable def localRootEval {R : Type*} [CommRing R] {N : ℕ}
    (f : Polynomial R) (φ : R →+* ZMod N) (m : ZMod N) (root : f.eval₂ φ m = 0)
    (S : Submonoid (AdjoinRoot f))
    (units : ∀ s : S, IsUnit (AdjoinRoot.lift φ m root s)) :
    Localization S →+* ZMod N := IsLocalization.lift units

theorem localRootEval_at_mark {R : Type*} [CommRing R] {N : ℕ}
    (f : Polynomial R) (φ : R →+* ZMod N) (m : ZMod N) (root : f.eval₂ φ m = 0)
    (S : Submonoid (AdjoinRoot f))
    (units : ∀ s : S, IsUnit (AdjoinRoot.lift φ m root s)) (a : ℤ) :
    localRootEval f φ m root S units (algebraMap _ (Localization S) (a - AdjoinRoot.root f)) =
      (a : ZMod N) - m := by
  rw [localRootEval, IsLocalization.lift_eq, map_sub, map_intCast, AdjoinRoot.lift_root]

/-- The leading coefficient can be inverted over the integers whenever it is
coprime to the modulus, allowing nonmonic integral input polynomials. -/
noncomputable def evalLeadingCoefficients (c N : ℕ) (hc : c.Coprime N) :
    Localization.Away (c : ℤ) →+* ZMod N :=
  IsLocalization.Away.lift (c : ℤ) (g := Int.castRingHom (ZMod N))
    (by simpa using (ZMod.isUnit_iff_coprime c N).mpr hc)

private theorem intCast_unit_of_coprime {N : ℕ} {z : ℤ} (h : IsCoprime z (N : ℤ)) :
    IsUnit (z : ZMod N) := by
  have coprime := h.map (Int.castRingHom (ZMod N))
  simpa [isCoprime_zero_right] using coprime

/-- Localization at precisely the marks used by the relation. Its complete
denominator submonoid maps to units by the original coprimality tests. -/
theorem eval_mark_denominators {ι R : Type*} [CommRing R] {N : ℕ}
    (f : Polynomial R) (φ : R →+* ZMod N) (m : ℤ) (root : f.eval₂ φ (m : ZMod N) = 0)
    (a : ι → ℤ) (coprime : ∀ i, IsCoprime (a i - m) (N : ℤ)) :
    let S := Submonoid.closure (Set.range (fun i => (a i : AdjoinRoot f) - AdjoinRoot.root f))
    ∀ s : S, IsUnit (AdjoinRoot.lift φ (m : ZMod N) root s) := by
  let e := AdjoinRoot.lift φ (m : ZMod N) root
  have each : Set.range (fun i => (a i : AdjoinRoot f) - AdjoinRoot.root f) ⊆
      (IsUnit.submonoid (ZMod N)).comap e.toMonoidHom := by
    rintro _ ⟨i, rfl⟩
    change IsUnit (e (_ - _))
    simpa only [e, map_sub, map_intCast, AdjoinRoot.lift_root, Int.cast_sub] using
      intCast_unit_of_coprime (coprime i)
  intro S s
  exact (Submonoid.closure_le.mpr each) s.property

/-- The two relations may contain negative multiplicities. In each localized root
ring the marks are units. Agreement of their individual evaluations gives the same
evaluated product, which cancels after squaring both field identities. -/
theorem modular_exponent_of_signed_relations
    {ι R₁ R₂ K₁ K₂ : Type*} [Fintype ι] [CommRing R₁] [CommRing R₂] [Field K₁] [Field K₂]
    {N : ℕ} (inc₁ : R₁ →+* K₁) (inc₂ : R₂ →+* K₂)
    (inj₁ : Function.Injective inc₁) (inj₂ : Function.Injective inc₂)
    (eval₁ : R₁ →+* ZMod N) (eval₂ : R₂ →+* ZMod N) (a₁ : ι → R₁ˣ) (a₂ : ι → R₂ˣ)
    (same : ∀ i, eval₁ (a₁ i : R₁) = eval₂ (a₂ i : R₂))
    (ℓ E : ℕ) (c : ι → ℤ)
    (sign₁ : (inc₁ (ℓ^E * ((∏ i, (a₁ i)^(c i) : R₁ˣ) : R₁)))^2 = 1)
    (sign₂ : (inc₂ ((∏ i, (a₂ i)^(c i) : R₂ˣ) : R₂))^2 = 1) :
    (ℓ : ZMod N)^(2*E) = 1 := by
  let P₁ : R₁ˣ := ∏ i, (a₁ i)^(c i)
  let P₂ : R₂ˣ := ∏ i, (a₂ i)^(c i)
  have same_units (i) : Units.map eval₁.toMonoidHom (a₁ i) = Units.map eval₂.toMonoidHom (a₂ i) :=
    Units.ext (same i)
  have same_product : Units.map eval₁.toMonoidHom P₁ = Units.map eval₂.toMonoidHom P₂ := by
    simp only [P₁, P₂, map_prod, map_zpow, same_units]
  have common : eval₁ (P₁ : R₁) = eval₂ (P₂ : R₂) := congrArg Units.val same_product
  have s₁ : (ℓ^E * (P₁ : R₁))^2 = 1 := inj₁ (by rw [map_pow, map_one]; exact sign₁)
  have s₂ : (P₂ : R₂)^2 = 1 := inj₂ (by rw [map_pow, map_one]; exact sign₂)
  have h₁ := congrArg eval₁ s₁
  have h₂ := congrArg eval₂ s₂
  simp only [map_pow, map_one] at h₂
  simp only [map_pow, map_mul, map_natCast, map_one, mul_pow, common, h₂, mul_one] at h₁
  simpa only [Nat.mul_comm 2 E, pow_mul] using h₁

/-- In any integer lattice basis, the adjugate supplies integer correction
coefficients whose combination kills the determinant multiple of the target. -/
theorem adjugate_lattice_relation {ι L : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup L] [Module ℤ L] (b : Module.Basis ι ℤ L) (v : ι → L) (t : L) :
    ∃ c : ι → ℤ, (b.toMatrix v).det • t + ∑ i, c i • v i = 0 := by
  let A := b.toMatrix v
  let p : ι → ℤ := b.equivFun t
  let r : ι → ℤ := A.adjugate *ᵥ p
  refine ⟨fun i => -r i, ?_⟩
  have adj : A *ᵥ r = A.det • p := by
    change A *ᵥ (A.adjugate *ᵥ p) = A.det • p
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  apply b.equivFun.injective
  ext j
  have e := congrFun adj j
  simpa [A, p, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply,
    Module.Basis.equivFun_apply, mul_comm, sub_eq_add_neg] using sub_eq_zero.mpr e.symm

private theorem abs_adjugate_lattice_relation {ι L : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup L] [Module ℤ L] (b : Module.Basis ι ℤ L) (v : ι → L) (t : L) :
    ∃ c : ι → ℤ, |(b.toMatrix v).det| • t + ∑ i, c i • v i = 0 := by
  obtain ⟨c, hc⟩ := adjugate_lattice_relation b v t
  rcases le_or_gt 0 (b.toMatrix v).det with pos | neg
  · exact ⟨c, by rwa [abs_of_nonneg pos]⟩
  · refine ⟨fun i => -c i, ?_⟩
    rw [abs_of_neg neg]
    simp only [neg_zsmul, Finset.sum_neg_distrib, ← neg_add, neg_eq_zero]
    exact hc

abbrev UnitClass (K : Type*) [Field K] [NumberField K] :=
  Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)

/-- The canonical integer action on the paired additive unit classes. -/
instance pairedUnitClassModule {K₁ K₂ : Type*} [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂] :
    Module ℤ (UnitClass K₁ × UnitClass K₂) := AddCommGroup.toIntModule (UnitClass K₁ × UnitClass K₂)

set_option backward.isDefEq.respectTransparency.types false in
/-- The paired integral basis supplied by Dirichlet's unit theorem. The row
indices have the sum of the two true field unit ranks. -/
noncomputable def pairedUnitBasis (K₁ K₂ : Type*) [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] : Module.Basis (Fin (NumberField.Units.rank K₁) ⊕
    Fin (NumberField.Units.rank K₂)) ℤ (UnitClass K₁ × UnitClass K₂) :=
  @Module.Basis.prod _ _ _ _ _ _ _ (AddCommGroup.toIntModule (UnitClass K₁))
    _ (AddCommGroup.toIntModule (UnitClass K₂)) (NumberField.Units.basisModTorsion K₁)
    (NumberField.Units.basisModTorsion K₂)

def unitClass {K : Type*} [Field K] [NumberField K] (u : (𝓞 K)ˣ) : UnitClass K :=
  Additive.ofMul (QuotientGroup.mk u)

private theorem torsion_of_class_relation {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (u : (𝓞 K)ˣ) (v : ι → (𝓞 K)ˣ) (d : ℤ) (c : ι → ℤ)
    (h : d • unitClass u + ∑ i, c i • unitClass (v i) = 0) :
    u^d * ∏ i, (v i)^(c i) ∈ NumberField.Units.torsion K := by
  apply (QuotientGroup.eq_one_iff _).mp
  have h' := congrArg Additive.toMul h
  simpa [unitClass, toMul_sum, QuotientGroup.mk_prod] using h'

/-- An integer multiple of the target is cancelled by shared integer coefficients
in the chosen free abelian lattice. -/
def latticeRelation {L ι : Type*} [AddCommGroup L] [Module ℤ L] [Fintype ι]
    (d : ℤ) (target : L) (c : ι → ℤ) (v : ι → L) : Prop :=
  d • target + ∑ i, c i • v i = 0

private theorem signs_of_paired_class_relation {K₁ K₂ ι : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype ι] (σ₁ : K₁ →+* ℝ) (σ₂ : K₂ →+* ℝ)
    (u₁ : (𝓞 K₁)ˣ) (u₂ : (𝓞 K₂)ˣ) (v₁ : ι → (𝓞 K₁)ˣ) (v₂ : ι → (𝓞 K₂)ˣ)
    (d : ℕ) (c : ι → ℤ)
    (hc : latticeRelation (d : ℤ) (unitClass u₁, unitClass u₂) c
      (fun i => (unitClass (v₁ i), unitClass (v₂ i)))) :
      (((u₁^d * ∏ i, (v₁ i)^(c i) : (𝓞 K₁)ˣ) : K₁) = 1 ∨
        ((u₁^d * ∏ i, (v₁ i)^(c i) : (𝓞 K₁)ˣ) : K₁) = -1) ∧
      (((u₂^d * ∏ i, (v₂ i)^(c i) : (𝓞 K₂)ˣ) : K₂) = 1 ∨
        ((u₂^d * ∏ i, (v₂ i)^(c i) : (𝓞 K₂)ˣ) : K₂) = -1) := by
  unfold latticeRelation at hc
  simp only [← zpow_natCast]
  refine ⟨signed_of_torsion σ₁ _ (torsion_of_class_relation _ _ _ _ ?_),
    signed_of_torsion σ₂ _ (torsion_of_class_relation _ _ _ _ ?_)⟩
  · simpa only [map_add, map_sum, map_zsmul, map_zero, AddMonoidHom.coe_fst] using
      congrArg (AddMonoidHom.fst (UnitClass K₁) (UnitClass K₂)) hc
  · simpa only [map_add, map_sum, map_zsmul, map_zero, AddMonoidHom.coe_snd] using
      congrArg (AddMonoidHom.snd (UnitClass K₁) (UnitClass K₂)) hc

/-- For a full-rank family of paired field-unit classes, the same integer
coefficients cancel both class coordinates. Real embeddings turn the two
remaining torsion units into signs in the actual number fields. -/
theorem two_field_unit_cancellation {K₁ K₂ ι : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype ι] [DecidableEq ι]
    (σ₁ : K₁ →+* ℝ) (σ₂ : K₂ →+* ℝ) (basis : Module.Basis ι ℤ (UnitClass K₁ × UnitClass K₂))
    (u₁ : (𝓞 K₁)ˣ) (u₂ : (𝓞 K₂)ˣ) (v₁ : ι → (𝓞 K₁)ˣ) (v₂ : ι → (𝓞 K₂)ˣ)
    (d : ℕ) (hd : (d : ℤ) = |(basis.toMatrix fun i => (unitClass (v₁ i), unitClass (v₂ i))).det|) :
    ∃ c : ι → ℤ,
      (((u₁^d * ∏ i, (v₁ i)^(c i) : (𝓞 K₁)ˣ) : K₁) = 1 ∨
        ((u₁^d * ∏ i, (v₁ i)^(c i) : (𝓞 K₁)ˣ) : K₁) = -1) ∧
      (((u₂^d * ∏ i, (v₂ i)^(c i) : (𝓞 K₂)ˣ) : K₂) = 1 ∨
        ((u₂^d * ∏ i, (v₂ i)^(c i) : (𝓞 K₂)ˣ) : K₂) = -1) := by
  obtain ⟨c, hc⟩ := abs_adjugate_lattice_relation basis (fun i => (unitClass (v₁ i), unitClass (v₂ i)))
    (unitClass u₁, unitClass u₂)
  rw [← hd] at hc
  exact ⟨c, signs_of_paired_class_relation σ₁ σ₂ u₁ u₂ v₁ v₂ d c hc⟩

private theorem field_product_of_units {R K ι : Type*} [CommRing R] [Field K] [Fintype ι]
    (inc : R →+* K) (a : ι → Rˣ) (c : ι → ℤ) :
    inc ((∏ i, (a i)^(c i) : Rˣ) : R) = ∏ i, (inc (a i : R))^(c i) := by
  let F : Rˣ →* K := inc.toMonoidHom.comp (Units.coeHom R)
  change F (∏ i, (a i)^(c i)) = ∏ i, (F (a i))^(c i)
  rw [map_prod]
  simp only [map_zpow]

private theorem integer_units_product_coe {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (a : ι → (𝓞 K)ˣ) (c : ι → ℤ) :
    ((∏ i, (a i)^(c i) : (𝓞 K)ˣ) : K) = ∏ i, (a i : K)^(c i) :=
  field_product_of_units (algebraMap (𝓞 K) K) a c

private theorem signSq {K : Type*} [Field K] {x : K} (h : x = 1 ∨ x = -1) : x^2 = 1 := by
  rcases h with rfl | rfl <;> norm_num

/-- Any common positive denominator that clears the paired class relation
gives the same modular exponent test, including the reconstructed least denominator. -/
theorem order_from_unit_class_relation {K₁ K₂ R₁ R₂ ι : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [CommRing R₁] [CommRing R₂] [Fintype ι]
    (σ₁ : K₁ →+* ℝ) (σ₂ : K₂ →+* ℝ)
    (inc₁ : R₁ →+* K₁) (inc₂ : R₂ →+* K₂) (inj₁ : Function.Injective inc₁)
    (inj₂ : Function.Injective inc₂) {N : ℕ} (eval₁ : R₁ →+* ZMod N) (eval₂ : R₂ →+* ZMod N)
    (ℓ e : ℕ) (he : 0 < e) (t₁ : R₁ˣ) (t₂ : R₂ˣ) (a₁ : ι → R₁ˣ) (a₂ : ι → R₂ˣ)
    (target_eval : eval₁ (t₁ : R₁) = eval₂ (t₂ : R₂))
    (neutral_eval : ∀ i, eval₁ (a₁ i : R₁) = eval₂ (a₂ i : R₂))
    (u₁ : (𝓞 K₁)ˣ) (u₂ : (𝓞 K₂)ˣ) (v₁ : ι → (𝓞 K₁)ˣ) (v₂ : ι → (𝓞 K₂)ˣ)
    (ut₁ : (u₁ : K₁) = ℓ^e * inc₁ (t₁ : R₁)) (ut₂ : (u₂ : K₂) = inc₂ (t₂ : R₂))
    (vr₁ : ∀ i, (v₁ i : K₁) = inc₁ (a₁ i : R₁)) (vr₂ : ∀ i, (v₂ i : K₂) = inc₂ (a₂ i : R₂))
    (d : ℕ) (c : ι → ℤ)
    (hc : latticeRelation (d : ℤ) (unitClass u₁, unitClass u₂) c
      (fun i => (unitClass (v₁ i), unitClass (v₂ i))))
    (hdPos : 0 < d) :
    0 < 2*(e*d) ∧ (ℓ : ZMod N)^(2*(e*d)) = 1 := by
  obtain ⟨h₁, h₂⟩ := signs_of_paired_class_relation σ₁ σ₂ u₁ u₂ v₁ v₂ d c hc
  let p₁ := ∏ i, (a₁ i)^(c i)
  let p₂ := ∏ i, (a₂ i)^(c i)
  have cmp (i) : Units.map eval₁.toMonoidHom (a₁ i) = Units.map eval₂.toMonoidHom (a₂ i) :=
    Units.ext (neutral_eval i)
  have pc : eval₁ (p₁ : R₁) = eval₂ (p₂ : R₂) := by
    have h : Units.map eval₁.toMonoidHom p₁ = Units.map eval₂.toMonoidHom p₂ := by
      simp only [p₁, p₂, map_prod, map_zpow, cmp]
    exact congrArg Units.val h
  have s₁ : (ℓ^(e*d) * (t₁ : R₁)^d * (p₁ : R₁))^2 = 1 := by
    apply inj₁
    simpa only [map_pow, map_mul, map_one, map_natCast, p₁, field_product_of_units,
      NumberField.Units.coe_mul, NumberField.Units.coe_pow, integer_units_product_coe,
      ut₁, vr₁, mul_pow, pow_mul] using signSq h₁
  have s₂ : ((t₂ : R₂)^d * (p₂ : R₂))^2 = 1 := by
    apply inj₂
    simpa only [map_pow, map_mul, map_one, p₂, field_product_of_units,
      NumberField.Units.coe_mul, NumberField.Units.coe_pow, integer_units_product_coe,
      ut₂, vr₂] using signSq h₂
  have v := congrArg eval₂ s₂
  simp only [map_pow, map_one, map_mul, mul_pow] at v
  have h := congrArg eval₁ s₁
  simp only [map_pow, map_one, map_mul, map_natCast, mul_pow, target_eval, pc, mul_assoc, v,
    mul_one] at h
  exact ⟨by positivity, by simpa only [Nat.mul_comm 2 (e*d), pow_mul] using h⟩

/-- Once valuation relations have supplied the displayed genuine units, a
nonzero unit-class minor yields a verified positive even exponent modulo N.
No computation of the fundamental units is asserted. -/
theorem order_from_unit_minor {K₁ K₂ R₁ R₂ ι : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [CommRing R₁] [CommRing R₂] [Fintype ι] [DecidableEq ι]
    (σ₁ : K₁ →+* ℝ) (σ₂ : K₂ →+* ℝ) (basis : Module.Basis ι ℤ (UnitClass K₁ × UnitClass K₂))
    (inc₁ : R₁ →+* K₁) (inc₂ : R₂ →+* K₂) (inj₁ : Function.Injective inc₁)
    (inj₂ : Function.Injective inc₂) {N : ℕ} (eval₁ : R₁ →+* ZMod N) (eval₂ : R₂ →+* ZMod N)
    (ℓ e : ℕ) (he : 0 < e) (t₁ : R₁ˣ) (t₂ : R₂ˣ) (a₁ : ι → R₁ˣ) (a₂ : ι → R₂ˣ)
    (target_eval : eval₁ (t₁ : R₁) = eval₂ (t₂ : R₂))
    (neutral_eval : ∀ i, eval₁ (a₁ i : R₁) = eval₂ (a₂ i : R₂))
    (u₁ : (𝓞 K₁)ˣ) (u₂ : (𝓞 K₂)ˣ) (v₁ : ι → (𝓞 K₁)ˣ) (v₂ : ι → (𝓞 K₂)ˣ)
    (ut₁ : (u₁ : K₁) = ℓ^e * inc₁ (t₁ : R₁)) (ut₂ : (u₂ : K₂) = inc₂ (t₂ : R₂))
    (vr₁ : ∀ i, (v₁ i : K₁) = inc₁ (a₁ i : R₁)) (vr₂ : ∀ i, (v₂ i : K₂) = inc₂ (a₂ i : R₂))
    (d : ℕ) (hd : (d : ℤ) = |(basis.toMatrix fun i => (unitClass (v₁ i), unitClass (v₂ i))).det|)
    (hdPos : 0 < d) :
    0 < 2*(e*d) ∧ (ℓ : ZMod N)^(2*(e*d)) = 1 := by
  obtain ⟨c, hc⟩ := abs_adjugate_lattice_relation basis
    (fun i => (unitClass (v₁ i), unitClass (v₂ i))) (unitClass u₁, unitClass u₂)
  rw [← hd] at hc
  exact order_from_unit_class_relation σ₁ σ₂ inc₁ inc₂ inj₁ inj₂ eval₁ eval₂ ℓ e he t₁ t₂
    a₁ a₂ target_eval neutral_eval u₁ u₂ v₁ v₂ ut₁ ut₂ vr₁ vr₂ d c hc hdPos

/-- Spanning over a field by observed lattice vectors forces an actual nonzero integer
minor from the same candidate family, even when its initial indexing type is infinite. -/
theorem integer_minor_of_field_span {F ι τ L : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    [AddCommGroup L] [Module ℤ L] (b : Module.Basis ι ℤ L) (v : τ → L)
    (obs : L →ₗ[ℤ] (ι → F)) (hs : Submodule.span F (Set.range fun j => obs (v j)) = ⊤) :
    ∃ pick : ι → τ, (b.toMatrix (fun j => v (pick j))).det ≠ 0 := by
  classical
  let canonical := Pi.basisFun F ι
  let axes := Module.Basis.ofSpan hs.ge
  let e := axes.indexEquiv canonical
  let realBasis := axes.reindex e
  have contained (i : ι) : ∃ j, obs (v j) = realBasis i :=
    Module.Basis.ofSpan_subset hs.ge ⟨e.symm i, by simp [realBasis, axes]⟩
  choose pick hpick using contained
  let A := b.toMatrix fun j => v (pick j)
  let B : Matrix ι ι F := fun i j => obs (b j) i
  have factor : canonical.toMatrix realBasis = B * A.map (Int.castRingHom F) := by
    ext i j
    change realBasis j i = ∑ k, obs (b k) i * ((b.repr (v (pick j)) k : ℤ) : F)
    rw [← hpick]
    have h := congrArg obs (b.sum_repr (v (pick j)))
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, mul_comm]
      using (congrFun h i).symm
  have unitDet := (canonical.is_basis_iff_det (v := (realBasis : ι → (ι → F)))).mp
    ⟨realBasis.linearIndependent, realBasis.span_eq⟩
  have nz : (canonical.toMatrix realBasis).det ≠ 0 := unitDet.ne_zero
  refine ⟨pick, fun bad => nz ?_⟩
  change A.det = 0 at bad
  rw [factor, Matrix.det_mul]
  change B.det * ((Int.castRingHom F).mapMatrix A).det = 0
  rw [← RingHom.map_det, bad, map_zero, mul_zero]

/-- Real spanning by observed lattice vectors forces an actual nonzero integer
minor from the same candidate family, even when its initial indexing type is infinite. -/
theorem integer_minor_of_real_span {ι τ L : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup L] [Module ℤ L] (b : Module.Basis ι ℤ L) (v : τ → L)
    (obs : L →ₗ[ℤ] (ι → ℝ)) (hs : Submodule.span ℝ (Set.range fun j => obs (v j)) = ⊤) :
    ∃ pick : ι → τ, (b.toMatrix (fun j => v (pick j))).det ≠ 0 := integer_minor_of_field_span b v obs hs

/-- Each logarithmic real embedding descends to the unit class modulo torsion,
since changing an integral unit by a torsion unit only changes its real sign. -/
noncomputable def classLogAt {K : Type*} [Field K] [NumberField K] (σ : K →+* ℝ) :
    UnitClass K →+ ℝ := by
  let f : (𝓞 K)ˣ →* Multiplicative ℝ := {
    toFun := fun u => Multiplicative.ofAdd (Real.log |σ (u : K)|)
    map_one' := by change Multiplicative.ofAdd (Real.log |σ (1 : K)|) = 1; simp
    map_mul' := by
      intro u v
      change Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
      have nz (z : (𝓞 K)ˣ) : |σ (z : K)| ≠ 0 :=
        abs_ne_zero.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero z))
      rw [NumberField.Units.coe_mul, map_mul, abs_mul, Real.log_mul (nz u) (nz v)]
      rfl }
  let q := QuotientGroup.lift (NumberField.Units.torsion K) f (by
    intro u hu
    change Multiplicative.ofAdd (Real.log |σ (u : K)|) = 1
    rcases signed_of_torsion σ u hu with h | h <;> simp [h])
  exact q.toAdditiveLeft

@[simp] theorem classLogAt_unitClass {K : Type*} [Field K] [NumberField K]
    (σ : K →+* ℝ) (u : (𝓞 K)ˣ) : classLogAt σ (unitClass u) = Real.log |σ (u : K)| := rfl

/-- All actual logarithmic embedding rows of both fields followed by any real
coordinate projection, including the two Helmert blocks used by the extractor. -/
noncomputable def observeUnitPair {K₁ K₂ ι₁ ι₂ ν : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype ι₁] [Fintype ι₂]
    (σ₁ : ι₁ → K₁ →+* ℝ) (σ₂ : ι₂ → K₂ →+* ℝ) (H : Matrix ν (ι₁ ⊕ ι₂) ℝ) :
    UnitClass K₁ × UnitClass K₂ →ₗ[ℤ] (ν → ℝ) := by
  let raw : UnitClass K₁ × UnitClass K₂ →+ (ι₁ ⊕ ι₂ → ℝ) := {
    toFun := fun u => Sum.elim (fun i => classLogAt (σ₁ i) u.1) (fun j => classLogAt (σ₂ j) u.2)
    map_zero' := by funext i; cases i <;> simp
    map_add' := by intro a b; funext i; cases i <;> simp }
  let G := H.mulVecLin.toAddMonoidHom.comp raw
  exact { toFun := G, map_add' := map_add G, map_smul' := fun z a => map_zsmul G z a }

@[simp] theorem observeUnitPair_apply {K₁ K₂ ι₁ ι₂ ν : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype ι₁] [Fintype ι₂]
    (σ₁ : ι₁ → K₁ →+* ℝ) (σ₂ : ι₂ → K₂ →+* ℝ) (H : Matrix ν (ι₁ ⊕ ι₂) ℝ)
    (a : (𝓞 K₁)ˣ) (b : (𝓞 K₂)ˣ) :
    observeUnitPair σ₁ σ₂ H (unitClass a, unitClass b) =
      H *ᵥ Sum.elim (fun i => Real.log |σ₁ i (a : K₁)|) (fun j => Real.log |σ₂ j (b : K₂)|) := rfl

/-- Normalizing every mark by A shifts its logarithm by the same constant.
The intercept equation removes that shift, even for negative exponents. -/
theorem normalized_log_relation {K κ : Type*} [Field K] [Fintype κ]
    (σ : K →+* ℝ) (a : κ → K) (nz : ∀ j, a j ≠ 0) (A : ℝ) (hA : 0 < A)
    (z : κ → ℤ) (sz : ∑ j, z j = 0) :
    ∑ j, Real.log (|σ (a j)| / A) * (z j : ℝ) = Real.log |σ (∏ j, (a j)^(z j))| := by
  have hn (j) : |σ (a j)| ≠ 0 := abs_ne_zero.mpr ((map_ne_zero σ).mpr (nz j))
  have cast_sum : ∑ j, (z j : ℝ) = 0 := by exact_mod_cast sz
  simp only [map_prod, map_zpow₀, Finset.abs_prod, abs_zpow, Real.log_prod
    (fun j _ => zpow_ne_zero _ (hn j)), Real.log_zpow, Real.log_div (hn _) hA.ne',
    sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, cast_sum, mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual normalized logarithmic rows of field elements on a common set of marks,
prior to application of the real projection matrix. -/
noncomputable def markLogs {K₁ K₂ α β κ : Type*} [Field K₁] [Field K₂]
    (σ₁ : α → K₁ →+* ℝ) (σ₂ : β → K₂ →+* ℝ) (a₁ : κ → K₁) (a₂ : κ → K₂) (A : ℝ) :
    Matrix (α ⊕ β) κ ℝ :=
  fun k j => Sum.elim (fun i => Real.log (|σ₁ i (a₁ j)| / A))
    (fun i => Real.log (|σ₂ i (a₂ j)| / A)) k

/-- The actual products of the marks in the two fields have precisely the
normalized projected unit-log coordinates on every balanced integer relation. -/
theorem observed_unit_relations {K₁ K₂ α β κ ν : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype α] [Fintype β] [Fintype κ]
    (σ₁ : α → K₁ →+* ℝ) (σ₂ : β → K₂ →+* ℝ) (a₁ : κ → K₁) (a₂ : κ → K₂)
    (ha₁ : ∀ j, a₁ j ≠ 0) (ha₂ : ∀ j, a₂ j ≠ 0) (A : ℝ) (hA : 0 < A)
    (H : Matrix ν (α ⊕ β) ℝ) (z : κ → ℤ) (sz : ∑ j, z j = 0)
    (u₁ : (𝓞 K₁)ˣ) (u₂ : (𝓞 K₂)ˣ) (hu₁ : (u₁ : K₁) = ∏ j, (a₁ j)^(z j))
    (hu₂ : (u₂ : K₂) = ∏ j, (a₂ j)^(z j)) :
    observeUnitPair σ₁ σ₂ H (unitClass u₁, unitClass u₂) =
      (H * markLogs σ₁ σ₂ a₁ a₂ A) *ᵥ (fun j => (z j : ℝ)) := by
  rw [observeUnitPair_apply, ← Matrix.mulVec_mulVec, hu₁, hu₂]
  congr 1
  funext k
  rcases k with i | i
  · exact (normalized_log_relation (σ₁ i) a₁ ha₁ A hA z sz).symm
  · exact (normalized_log_relation (σ₂ i) a₂ ha₂ A hA z sz).symm

/-- The actual positive joint Gram yields integer valuation relations whose
paired units have a nonzero determinant in the integral unit-class lattice.
The finite-place input is precisely integrality of the two neutral mark products. -/
theorem unit_minor_from_positive_gram {K₁ K₂ α β κ ι ν : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]
    [Fintype ν] [DecidableEq ν] (σ₁ : α → K₁ →+* ℝ) (σ₂ : β → K₂ →+* ℝ)
    (a₁ : κ → K₁) (a₂ : κ → K₂) (ha₁ : ∀ j, a₁ j ≠ 0) (ha₂ : ∀ j, a₂ j ≠ 0)
    (A : ℝ) (hA : 0 < A) (H : Matrix ν (α ⊕ β) ℝ) (V : Matrix ι κ ℤ)
    (top : ι) (intercept : ∀ j, V top j = 1) (scale : ι → ℝ) (hs : ∀ i, scale i ≠ 0)
    (W : Matrix κ κ ℝ) (basis : Module.Basis ν ℤ (UnitClass K₁ × UnitClass K₂))
    (cert : let M := jointRows V scale (H * markLogs σ₁ σ₂ a₁ a₂ A); (M * W * M.transpose).PosDef)
    (units : ∀ z : κ → ℤ, (∀ i, ∑ j, V i j * z j = 0) →
      ∃ (u₁ : (𝓞 K₁)ˣ) (u₂ : (𝓞 K₂)ˣ), (u₁ : K₁) = ∏ j, (a₁ j)^(z j) ∧
        (u₂ : K₂) = ∏ j, (a₂ j)^(z j)) :
    ∃ (z : ν → κ → ℤ) (u₁ : ν → (𝓞 K₁)ˣ) (u₂ : ν → (𝓞 K₂)ˣ),
      (∀ k i, ∑ j, V i j * z k j = 0) ∧
      (∀ k, (u₁ k : K₁) = ∏ j, (a₁ j)^(z k j)) ∧
      (∀ k, (u₂ k : K₂) = ∏ j, (a₂ j)^(z k j)) ∧
      (basis.toMatrix (fun k => (unitClass (u₁ k), unitClass (u₂ k)))).det ≠ 0 := by
  classical
  let Z := {z : κ → ℤ // ∀ i, ∑ j, V i j * z j = 0}
  let U := H * markLogs σ₁ σ₂ a₁ a₂ A
  let obs := observeUnitPair σ₁ σ₂ H
  have have_units (z : Z) := units z.val z.property
  choose p q hp hq using have_units
  have observed (z : Z) : obs (unitClass (p z), unitClass (q z)) =
      U *ᵥ (fun j => (z.val j : ℝ)) := by
    have zero_sum : ∑ j, z.val j = 0 := by simpa [intercept] using z.property top
    exact observed_unit_relations σ₁ σ₂ a₁ a₂ ha₁ ha₂ A hA H z.val zero_sum _ _ (hp z) (hq z)
  have seteq : Set.range (fun z : Z => obs (unitClass (p z), unitClass (q z))) =
      {y : ν → ℝ | ∃ z : κ → ℤ, (∀ i, ∑ j, V i j * z j = 0) ∧ y = U *ᵥ (fun j => (z j : ℝ))} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, observed z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z,hz⟩, observed ⟨z,hz⟩⟩
  have span := (positive_gram_descent V scale hs U W cert).2
  rw [← seteq] at span
  obtain ⟨pick, det⟩ := integer_minor_of_real_span basis
    (fun z : Z => (unitClass (p z), unitClass (q z))) obs span
  exact ⟨fun k => (pick k).val, fun k => p (pick k), fun k => q (pick k),
    fun k => (pick k).property, fun k => hp (pick k), fun k => hq (pick k), det⟩

end Cogentic
