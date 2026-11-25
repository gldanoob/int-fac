import Cogentic.ConstructionBrackets
import Cogentic.UnitGap
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace Cogentic.Construction

open Polynomial NumberField NumberField.InfinitePlace

/-- A rational polynomial with its real roots listed without repetitions gives
    the ordered *actual* infinite places of the root-adjunction number field. -/
theorem ordered_from_roots {f : Polynomial ℚ} [irr : Fact (Irreducible f)]
    {d : ℕ} (degree : f.natDegree = d) (ρ : Fin d → ℝ) (unique : Function.Injective ρ)
    (roots : ∀ i, f.eval₂ (Rat.castHom ℝ) (ρ i) = 0) :
    ∃ real : IsTotallyReal (AdjoinRoot f), letI := real
      ∃ places : Fin d ≃ InfinitePlace (AdjoinRoot f),
        (∀ i, orderedRealEmbeddings places i (AdjoinRoot.root f) = ρ i) ∧
        (∀ x : ℝ, f.eval₂ (Rat.castHom ℝ) x = 0 → ∃ i, ρ i = x) := by
  classical
  let K := AdjoinRoot f
  let realEmb (i : Fin d) : K →+* ℝ := AdjoinRoot.lift (Rat.castHom ℝ) (ρ i) (roots i)
  let compEmb (i : Fin d) : K →+* ℂ := Complex.ofRealHom.comp (realEmb i)
  have onroot (i : Fin d) : realEmb i (AdjoinRoot.root f) = ρ i := AdjoinRoot.lift_root ..
  have coe_root (i : Fin d) : compEmb i (AdjoinRoot.root f) = (ρ i:ℂ) := by simp [compEmb,onroot]
  have real (i : Fin d) : ComplexEmbedding.IsReal (compEmb i) := by
    rw [ComplexEmbedding.isReal_iff]
    apply RingHom.ext
    intro x
    change starRingEnd ℂ ((realEmb i x:ℝ):ℂ) = ((realEmb i x:ℝ):ℂ)
    simp
  have inject : Function.Injective compEmb := by
    intro i j eq
    apply unique
    have h := RingHom.congr_fun eq (AdjoinRoot.root f)
    simpa [coe_root] using h
  have count : Module.finrank ℚ K = d := (AdjoinRoot.powerBasis irr.out.ne_zero).finrank.trans degree
  have all := ((Fintype.bijective_iff_injective_and_card compEmb).mpr ⟨inject,by
    rw [Fintype.card_fin,NumberField.Embeddings.card,count]⟩).2
  have total : IsTotallyReal K := ⟨fun w => by
    obtain ⟨i,eq⟩ := all w.embedding
    exact InfinitePlace.isReal_iff.mpr (eq ▸ real i)⟩
  let places := fun i => InfinitePlace.mk (compEmb i)
  have places_inj : Function.Injective places := by
    intro i j eq
    have h := InfinitePlace.mk_eq_iff.mp eq
    rw [ComplexEmbedding.isReal_iff.mp (real i),or_self] at h
    exact inject h
  have places_surj : Function.Surjective places := by
    intro w
    obtain ⟨i,eq⟩ := all w.embedding
    exact ⟨i,(congrArg InfinitePlace.mk eq).trans (InfinitePlace.mk_embedding w)⟩
  let e := Equiv.ofBijective places ⟨places_inj,places_surj⟩
  let := total
  refine ⟨total,e,?_,?_⟩
  · intro i
    apply Complex.ofReal_injective
    rw [orderedRealEmbeddings,InfinitePlace.embedding_of_isReal_apply]
    change (InfinitePlace.mk (compEmb i)).embedding (AdjoinRoot.root f) = _
    rw [InfinitePlace.embedding_mk_eq_of_isReal (real i),coe_root]
  · intro x hx
    let r : K →+* ℝ := AdjoinRoot.lift (Rat.castHom ℝ) x hx
    obtain ⟨i,eq⟩ := all (Complex.ofRealHom.comp r)
    have atroot := RingHom.congr_fun eq (AdjoinRoot.root f)
    rw [coe_root] at atroot
    exact ⟨i,Complex.ofReal_injective (atroot.trans (congrArg Complex.ofReal (AdjoinRoot.lift_root ..)))⟩

noncomputable def fieldPolynomial (s : Marking.Input) (side : Bool) :=
  (Marking.polynomial (s.coeffs side)).map (Int.castRingHom ℚ)

private theorem rational_eval {R : Type*} [Field R] [CharZero R] (cs : List ℤ) (x : R) :
    ((Marking.polynomial cs).map (Int.castRingHom ℚ)).eval₂ (Rat.castHom R) x = (Marking.horner x cs).1 := by
  induction cs with
  | nil => simp [Marking.polynomial,Marking.horner]
  | cons c cs ih =>
    simp only [Marking.polynomial,Marking.horner,Polynomial.map_add,Polynomial.map_mul,map_C,map_X,
      eval₂_add,eval₂_C,eval₂_mul,eval₂_X,ih]
    simp

/-- Each ordered real embedding sends the adjoined generator to A times the
    unique real root in its indexed normalized bisection bracket. -/
theorem constructed_field_places {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 10004 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    ∀ side : Bool, ∃ irr : Irreducible (fieldPolynomial s side), letI : Fact (Irreducible (fieldPolynomial s side)) := ⟨irr⟩
      ∃ real : IsTotallyReal (AdjoinRoot (fieldPolynomial s side)), letI := real
        ∃ places : Fin s.degree ≃ InfinitePlace (AdjoinRoot (fieldPolynomial s side)),
          let θ := AdjoinRoot.root (fieldPolynomial s side)
          (Marking.polynomial (s.coeffs side)).eval₂ (Int.castRingHom (AdjoinRoot (fieldPolynomial s side))) θ = 0 ∧
          ∀ i, orderedRealEmbeddings places i θ/s.A ∈
              Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
            ∀ x ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ),
            RootLogs.normalized s.A (s.coeffs side) x = 0 ↔ x = orderedRealEmbeddings places i θ/s.A := by
  let data := construct n ell u₀ u₁ v₀ v₁
  let s := TryPair.fixedInput n ell data
  dsimp only
  intro side
  have given := constructed_rational_fields (by omega : 3 ≤ Fixed.d (n.log2+1)) target u₀ u₁ v₀ v₁
  have fInfo : (fieldPolynomial s side).natDegree = s.degree ∧ Irreducible (fieldPolynomial s side) := by
    have deg (p : Polynomial ℤ) : (p.map (Int.castRingHom ℚ)).natDegree = p.natDegree :=
      natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)) _
    cases side
    · exact ⟨(deg _).trans given.1.1,given.1.2⟩
    · exact ⟨(deg _).trans given.2.1,given.2.2⟩
  refine ⟨fInfo.2,?_⟩
  let : Fact (Irreducible (fieldPolynomial s side)) := ⟨fInfo.2⟩
  let f := fieldPolynomial s side
  let K := AdjoinRoot f
  let θ := AdjoinRoot.root f
  let inside := fun (i : Fin s.degree) (x : ℝ) =>
    x ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ)
  have select (i : Fin s.degree) : ∃ x, inside i x ∧ RootLogs.normalized s.A (s.coeffs side) x = 0 := by
    obtain ⟨_,_,x,hx,root,_⟩ := constructed_isolate hn big target box side i 0
    exact ⟨x,hx,root⟩
  choose x insideX zero using select
  have ordered (i j : Fin s.degree) (ij : i < j) {a b : ℝ} (ha : inside i a) (hb : inside j b) : a < b := by
    have sep := brackets_ordered hn big ell data side i j ij
    exact ha.2.trans_lt ((show ((RootLogs.bracket s side i).right:ℝ) < (RootLogs.bracket s side j).left by exact_mod_cast sep).trans_le hb.1)
  have inject : Function.Injective x := (show StrictMono x from fun i j ij => ordered i j ij (insideX i) (insideX j)).injective
  have aposN : 0 < s.A := Nat.pow_pos (by decide)
  have apos : (0:ℝ) < s.A := by exact_mod_cast aposN
  let ρ := fun i => (s.A:ℝ)*x i
  have roots (i) : f.eval₂ (Rat.castHom ℝ) (ρ i) = 0 := (rational_eval ..).trans (zero i)
  have inj : Function.Injective ρ := fun _ _ h => inject (mul_left_cancel₀ apos.ne' h)
  obtain ⟨total,places,images,all⟩ := ordered_from_roots fInfo.1 ρ inj roots
  let := total
  refine ⟨total,places,?_,?_⟩
  · have compose (p : Polynomial ℤ) (φ : ℚ →+* K) (x : K) :
        (p.map (Int.castRingHom ℚ)).eval₂ φ x = p.eval₂ (Int.castRingHom K) x := by
      rw [Polynomial.eval₂_map,show φ.comp (Int.castRingHom ℚ) = Int.castRingHom K from Subsingleton.elim _ _]
    exact (compose _ (AdjoinRoot.of f) θ).symm.trans (AdjoinRoot.eval₂_root f)
  · intro i
    have identity : orderedRealEmbeddings places i θ/s.A = x i := by rw [images]; dsimp [ρ]; field_simp
    rw [identity]
    refine ⟨insideX i,?_⟩
    intro t ht
    refine ⟨fun eq => ?_,fun eq => eq ▸ zero i⟩
    obtain ⟨j,hj⟩ := all (s.A*t) ((rational_eval ..).trans eq)
    have values : x j = t := mul_left_cancel₀ apos.ne' hj
    have same : j = i := by
      rcases lt_trichotomy j i with lt | eq | gt
      · exact False.elim ((ordered j i lt (insideX j) ht).ne values)
      · exact eq
      · exact False.elim ((ordered i j gt ht (insideX j)).ne values.symm)
    exact values.symm.trans (congrArg x same)

end Cogentic.Construction

#print axioms Cogentic.Construction.constructed_field_places
