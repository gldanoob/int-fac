import Cogentic.ConstructedFields
import Cogentic.EliminationUnits

namespace Cogentic.Construction

open Polynomial NumberField

/-- The integer subring at a chosen algebraic root with precisely the affine
    marks inverted. The two maps agree on each selected rational mark. -/
structure MarkRing {ι : Type} (K : Type) [Field K] (N : ℕ) (θ : K) (m : ℤ) (a : ι → ℤ) where
  carrier : Type
  [commRing : CommRing carrier]
  inc : carrier →+* K
  injective : Function.Injective inc
  reduce : carrier →+* ZMod N
  mark : ι → carrierˣ
  mark_field : ∀ i, inc (mark i : carrier) = (a i : K)-θ
  mark_mod : ∀ i, reduce (mark i : carrier) = (a i : ZMod N)-m

attribute [instance] MarkRing.commRing

private theorem field_eval (f p : Polynomial ℤ) :
    p.eval₂ (Int.castRingHom (AdjoinRoot (f.map (Int.castRingHom ℚ)))) (AdjoinRoot.root (f.map (Int.castRingHom ℚ))) =
      AdjoinRoot.mk (f.map (Int.castRingHom ℚ)) (p.map (Int.castRingHom ℚ)) := by
  let fq := f.map (Int.castRingHom ℚ)
  rw [←AdjoinRoot.aeval_eq,aeval_def,Polynomial.eval₂_map]
  congr 1

private theorem content_root {S : Type*} [CommRing S] (f : Polynomial ℤ) (x : S)
    (unit : IsUnit (f.content : S)) (root : f.eval₂ (Int.castRingHom S) x = 0) :
    f.primPart.eval₂ (Int.castRingHom S) x = 0 := by
  have eq := congrArg (fun p : Polynomial ℤ => p.eval₂ (Int.castRingHom S) x) f.eq_C_content_mul_primPart
  change f.eval₂ _ x = (C f.content*f.primPart).eval₂ _ x at eq
  rw [eval₂_mul,eval₂_C,root] at eq
  exact unit.mul_left_cancel (by simpa using eq.symm : (f.content:S)*f.primPart.eval₂ (Int.castRingHom S) x = (f.content:S)*0)

/-- Primitive-part Gauss divisibility proves injectivity into the rational
    number field, while a unit leading coefficient retains the same root
    modulo the composite modulus after removing polynomial content. -/
noncomputable def specialize {ι : Type} (f : Polynomial ℤ) [irr : Fact (Irreducible (f.map (Int.castRingHom ℚ)))]
    {N : ℕ} (m : ℤ) (a : ι → ℤ) (leading : IsUnit (f.leadingCoeff : ZMod N))
    (root : f.eval₂ (Int.castRingHom (ZMod N)) (m:ZMod N) = 0)
    (unitMark : ∀ i, IsUnit ((a i : ZMod N)-(m:ZMod N)))
    (nonzero : ∀ i, (a i : AdjoinRoot (f.map (Int.castRingHom ℚ))) -
      AdjoinRoot.root (f.map (Int.castRingHom ℚ)) ≠ 0) :
    MarkRing (AdjoinRoot (f.map (Int.castRingHom ℚ))) N (AdjoinRoot.root (f.map (Int.castRingHom ℚ))) m a := by
  classical
  let fq := f.map (Int.castRingHom ℚ)
  let K := AdjoinRoot fq
  let θ := AdjoinRoot.root fq
  have rootK : f.eval₂ (Int.castRingHom K) θ = 0 := (field_eval ..).trans (AdjoinRoot.mk_eq_zero.mpr dvd_rfl)
  have fnz : f ≠ 0 := fun eq => irr.out.ne_zero (by simp [eq])
  have cnz : f.content ≠ 0 := (content_eq_zero_iff).not.mpr fnz
  have cK : IsUnit (f.content : K) := (show (f.content:K) ≠ 0 by exact_mod_cast cnz).isUnit
  have cN : IsUnit (f.content : ZMod N) := isUnit_of_dvd_unit
    ((map_dvd (Int.castRingHom (ZMod N)) (content_dvd_coeff (p := f) f.natDegree))) leading
  let B := AdjoinRoot f.primPart
  let inc := AdjoinRoot.lift (Int.castRingHom K) θ (content_root f θ cK rootK)
  let mod := AdjoinRoot.lift (Int.castRingHom (ZMod N)) (m:ZMod N) (content_root f _ cN root)
  have inject : Function.Injective inc := by
    apply (injective_iff_map_eq_zero inc).mpr
    intro y hy
    obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective y
    apply AdjoinRoot.mk_eq_zero.mpr
    apply (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ f.isPrimitive_primPart).mpr
    obtain ⟨h,eq⟩ : fq ∣ g.map (Int.castRingHom ℚ) :=
      AdjoinRoot.mk_eq_zero.mp ((field_eval f g).symm.trans ((AdjoinRoot.lift_mk ..).symm.trans hy))
    exact ((map_dvd (Polynomial.mapRingHom (Int.castRingHom ℚ)) f.primPart_dvd)).trans ⟨h,eq⟩
  let value := fun i => (a i:B)-AdjoinRoot.root f.primPart
  let S := Submonoid.closure (Set.range value)
  have imagesF (i) : inc (value i) = (a i:K)-θ := by simp [inc,value,AdjoinRoot.lift_root]
  have imagesN (i) : mod (value i) = (a i:ZMod N)-m := by simp [mod,value,AdjoinRoot.lift_root]
  have units {T : Type} [CommRing T] (φ : B →+* T) (h : ∀ i, IsUnit (φ (value i))) :
      ∀ s : S, IsUnit (φ s) := by
    have subset : Set.range value ⊆ (IsUnit.submonoid T).comap φ.toMonoidHom := by
      rintro _ ⟨i,rfl⟩; exact h i
    exact fun s => (Submonoid.closure_le.mpr subset) s.property
  have uf := units inc (fun i => (imagesF i ▸ (nonzero i).isUnit))
  have un := units mod (fun i => (imagesN i ▸ unitMark i))
  let R := Localization S
  let toK : R →+* K := IsLocalization.lift uf
  let toMod : R →+* ZMod N := IsLocalization.lift un
  have injectR : Function.Injective toK := by
    apply (IsLocalization.lift_injective_iff (S := R) uf).mpr
    intro x y
    constructor
    · intro eq
      simpa [toK,IsLocalization.lift_eq] using congrArg toK eq
    · exact fun h => congrArg (algebraMap B R) (inject h)
  let inS (i : ι) : S := ⟨value i,Submonoid.subset_closure ⟨i,rfl⟩⟩
  let u (i : ι) := (IsLocalization.map_units R (inS i)).unit
  refine ⟨R,toK,injectR,toMod,u,fun i => ?_,fun i => ?_⟩
  · change toK (algebraMap B R (value i)) = _
    exact (IsLocalization.lift_eq ..).trans (imagesF i)
  · change toMod (algebraMap B R (value i)) = _
    exact (IsLocalization.lift_eq ..).trans (imagesN i)

private theorem leading_from_guard {s : Marking.Input} {cs : List ℤ} (ok : s.polynomialGuard cs)
    (pos : 1 ≤ s.leading) : (Marking.polynomial cs).leadingCoeff = (s.leading:ℤ) := by
  have last : cs[s.degree]? = some (s.leading:ℤ) := by
    simpa [List.getLast?_eq_getElem?,ok.1] using ok.2.1
  have coefficient : (Marking.polynomial cs).coeff s.degree = (s.leading:ℤ) := by
    simpa [List.getD_eq_getElem?_getD,last] using coefficient_rep (R := ℤ) cs s.degree
  have upper : (Marking.polynomial cs).natDegree ≤ s.degree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by have := ok.1; omega : cs.length ≤ j)] using
      coefficient_rep (R := ℤ) cs j
  rw [leadingCoeff,natDegree_eq_of_le_of_coeff_ne_zero upper (coefficient ▸ (by exact_mod_cast (by omega : s.leading ≠ 0)))]
  exact coefficient

/-- The executable marking output instantiates the two required evaluation
    rings. All denominators come directly from the retained marks. -/
noncomputable def markedRing {s : Marking.Input} {rel : Marking.Relations}
    (marked : Marking.stageOne s = some rel) (side : Bool) [Fact (Irreducible (fieldPolynomial s side))] :
    MarkRing (AdjoinRoot (fieldPolynomial s side)) s.n (AdjoinRoot.root (fieldPolynomial s side))
      (s.m:ℤ) (fun j : Fin rel.marks.length => (rel.marks.get j:ℤ)) := by
  let f := Marking.polynomial (s.coeffs side)
  let : Fact (Irreducible (f.map (Int.castRingHom ℚ))) := ⟨(inferInstance : Fact (Irreducible (fieldPolynomial s side))).out⟩
  let K := AdjoinRoot (fieldPolynomial s side)
  let θ := AdjoinRoot.root (fieldPolynomial s side)
  have rows := stageOne_affine_rows marked side
  have rootMod := (Marking.rows_and_guards marked).1
  obtain ⟨_,_,_,lead,_,_,_,_,_,cop,_,_,_,_,first,second⟩ := rootMod
  have guard : s.polynomialGuard (s.coeffs side) := by cases side; exact first; exact second
  have leading : IsUnit (f.leadingCoeff : ZMod s.n) := by
    rw [show f.leadingCoeff = (s.leading:ℤ) from leading_from_guard guard lead,Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime ..).mpr cop
  have common : f.eval₂ (Int.castRingHom (ZMod s.n)) (s.m:ZMod s.n) = 0 := by
    have root := guard.2.2.2
    simpa only [Marking.horner_correct] using root
  have unitZ {N : ℕ} (z : ℤ) (cp : z.natAbs.Coprime N) : IsUnit (z : ZMod N) := by
    have unit := (ZMod.isUnit_iff_coprime ..).mpr cp
    cases z with
    | ofNat n => simpa using unit
    | negSucc n => simpa using unit.neg
  have markUnit (i : Fin rel.marks.length) :
      IsUnit (((rel.marks.get i:ℤ):ZMod s.n)-((s.m:ℤ):ZMod s.n)) := by
    have eligible := ((Marking.retained_iff marked _).mp (List.get_mem rel.marks i)).1
    simp only [Marking.Input.eligibleMarks,Finset.mem_sort,Finset.mem_filter] at eligible
    simpa only [Int.cast_sub] using unitZ ((rel.marks.get i:ℤ)-s.m) eligible.2.2.2
  have rootField : f.eval₂ (Int.castRingHom K) θ = 0 := (field_eval f f).trans (AdjoinRoot.mk_eq_zero.mpr dvd_rfl)
  exact specialize f s.m _ leading (by simpa using common) markUnit (rows.nonzero_marks θ rootField)

namespace MarkRing

variable {ι κ K₁ K₂ : Type} [Fintype ι] [Fintype κ] [Field K₁] [Field K₂]
  {N : ℕ} {m : ℤ} {a : ι → ℤ} {θ₁ : K₁} {θ₂ : K₂}

private noncomputable def powerWord (D : MarkRing K₁ N θ₁ m a) (v : ι → ℤ) : D.carrierˣ :=
  ∏ j, (D.mark j)^(v j)

private theorem powerWord_field (D : MarkRing K₁ N θ₁ m a) (v : ι → ℤ) :
    D.inc ((powerWord D v : D.carrierˣ) : D.carrier) = ∏ j, ((a j : K₁)-θ₁)^(v j) := by
  let F := D.inc.toMonoidHom.comp (Units.coeHom D.carrier)
  change F (∏ j, (D.mark j)^(v j)) = _
  rw [map_prod]
  simp only [map_zpow]
  exact Finset.prod_congr rfl (fun j _ => congrArg (· ^ v j) (D.mark_field j))

private theorem powerWord_agrees (D : MarkRing K₁ N θ₁ m a) (E : MarkRing K₂ N θ₂ m a) (v : ι → ℤ) :
    D.reduce (powerWord D v : D.carrier) = E.reduce (powerWord E v : E.carrier) := by
  have atMark (j) : Units.map D.reduce.toMonoidHom (D.mark j) = Units.map E.reduce.toMonoidHom (E.mark j) :=
    Units.ext ((D.mark_mod j).trans (E.mark_mod j).symm)
  exact congrArg Units.val (show Units.map D.reduce.toMonoidHom (powerWord D v) =
      Units.map E.reduce.toMonoidHom (powerWord E v) by simp only [powerWord,map_prod,map_zpow,atMark])

/-- The genuine class relation descends through the two computed mark rings
    and yields the source's even modular exponent. -/
theorem order_from_affine_classes [NumberField K₁] [NumberField K₂] (D : MarkRing K₁ N θ₁ m a) (E : MarkRing K₂ N θ₂ m a)
    (σ₁ : K₁ →+* ℝ) (σ₂ : K₂ →+* ℝ) (ℓ e : ℕ) (he : 0 < e)
    (t : ι → ℤ) (w : κ → ι → ℤ) (u₁ : (𝓞 K₁)ˣ) (u₂ : (𝓞 K₂)ˣ)
    (v₁ : κ → (𝓞 K₁)ˣ) (v₂ : κ → (𝓞 K₂)ˣ)
    (hu₁ : (u₁:K₁) = ℓ^e * ∏ j, ((a j:K₁)-θ₁)^(t j))
    (hu₂ : (u₂:K₂) = ∏ j, ((a j:K₂)-θ₂)^(t j))
    (hv₁ : ∀ i, (v₁ i:K₁) = ∏ j, ((a j:K₁)-θ₁)^(w i j))
    (hv₂ : ∀ i, (v₂ i:K₂) = ∏ j, ((a j:K₂)-θ₂)^(w i j))
    (d : ℕ) (c : κ → ℤ) (hc : latticeRelation (d:ℤ) (unitClass u₁,unitClass u₂) c
      (fun i => (unitClass (v₁ i),unitClass (v₂ i)))) (hd : 0 < d) :
    0 < 2*(e*d) ∧ (ℓ:ZMod N)^(2*(e*d)) = 1 := by
  apply order_from_unit_class_relation σ₁ σ₂ D.inc E.inc D.injective E.injective D.reduce E.reduce
    ℓ e he (D.powerWord t) (E.powerWord t) (fun i => D.powerWord (w i)) (fun i => E.powerWord (w i))
    (powerWord_agrees D E t) (fun i => powerWord_agrees D E (w i)) u₁ u₂ v₁ v₂
  · rwa [powerWord_field]
  · rwa [powerWord_field]
  · intro i; rw [powerWord_field]; exact hv₁ i
  · intro i; rw [powerWord_field]; exact hv₂ i
  · exact hc
  · exact hd

end MarkRing

end Cogentic.Construction

#print axioms Cogentic.Construction.markedRing
#print axioms Cogentic.Construction.MarkRing.order_from_affine_classes
