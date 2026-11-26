import Cogentic.SurvivingGram

namespace Cogentic
open Marking
open scoped Matrix BigOperators

/-- On columns missing every target, the two finite norm equations use only ordinary rows.
A positive ordinary Gram there extends across one surviving witness for each target. -/
theorem positiveMarkCore_of_target_witnesses {N ell a b c d : ℕ} (hn : 2 ≤ N)
    (big : 10004 ≤ Fixed.d (N.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1))) :
    let s := TryPair.fixedInput N ell (Construction.construct N ell a b c d)
    ∀ {rel}, stageOne s = some rel → ∀ x : Bool → Fin s.degree → ℝ,
    (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
      RootLogs.normalized s.A (s.coeffs side) (x side i)=0) →
    ∀ {κ₁ κ₂ τ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype τ] [DecidableEq τ]
      (rows : ((κ₁ ⊕ κ₂) ⊕ τ) ↪ Fin rel.rows.length)
      (J : Finset (Fin rel.marks.length)) (pick : τ → Fin rel.marks.length)
      (scale : κ₁ ⊕ κ₂ → ℝ), (∀ i, scale i≠0) →
      (∀ i, (rel.rows.get (rows (.inl i))).second=i.elim (fun _ => false) (fun _ => true)) →
      (∀ i, i ∉ Set.range rows → rel.rhs i.succ=0) →
      (∀ i, i ∉ Set.range rows → ∀ j ∈ J, rel.matrix i.succ j=0) →
      (∀ i, i ∉ Set.range rows → ∀ r, rel.matrix i.succ (pick r)=0) →
      (∀ r, ∀ j∈J, rel.matrix (rows (.inr r)).succ j=0) →
      (∀ r t, rel.matrix (rows (.inr r)).succ (pick t)=if r=t then 1 else 0) →
    let z := fun i (j : J) => scale i*(rel.matrix (rows (.inl i)).succ j.val:ℝ)
    let w := fun i => Real.log (rel.rows.get (rows (.inl i))).q/scale i
    let L := (rawMarkMatrix s rel x).submatrix id (Subtype.val : J → Fin rel.marks.length)
    ∀ weight : J → ℝ,
    (∀ (v₀ : ℝ) (f₁ : κ₁ → ℝ) (f₂ : κ₂ → ℝ) (raw : Fin s.degree ⊕ Fin s.degree → ℝ),
      (fun i => w (.inl i)) ⬝ᵥ f₁=0 → (fun i => w (.inr i)) ⬝ᵥ f₂=0 →
      ¬(v₀=0 ∧ f₁=0 ∧ f₂=0 ∧ raw=0) →
      0 < ∑ j, weight j*(v₀+f₁ ⬝ᵥ (fun i => z (.inl i) j)+f₂ ⬝ᵥ (fun i => z (.inr i) j)+
        raw ⬝ᵥ (fun i => L i j))^2) → PositiveMarkCore s rel x := by
  classical
  intro s rel marked x roots κ₁ κ₂ τ _ _ _ _ rows J pick scale nz color rhs outside extra miss hits z w L weight model
  let ordinary : κ₁ ⊕ κ₂ ↪ Fin rel.rows.length :=
    ⟨fun i=>rows (.inl i),fun _ _ h=>Sum.inl.inj (rows.injective h)⟩
  have off (i) (hi : i∉Set.range ordinary) (j) (hj : j∈J) : rel.matrix i.succ j=0 := by
    by_cases h : i∈Set.range rows
    · obtain ⟨k,rfl⟩ := h
      cases k with
      | inl o => exact False.elim (hi ⟨o,rfl⟩)
      | inr t => exact miss t j hj
    · exact outside i h j hj
  obtain ⟨left,right⟩ := surviving_norm_coordinates hn big target marked x roots ordinary J scale nz color off
  let U := twoFieldRows (concreteRowCode s.degree) (fun i => z (.inl i)) (fun i => z (.inr i)) L
  have gram : (U * Matrix.diagonal weight * U.transpose).PosDef :=
    twoFieldGram_of_perpendicular (by change 0<Fixed.d (N.log2+1);omega) (concreteRowCode s.degree)
      _ _ L weight (fun i => w (.inl i)) (fun i => w (.inr i)) _ _ left right model
  let K := J ∪ Finset.univ.image pick
  let p := withIntercept rows
  have pn : p none=0 := rfl
  have ps (k) : p (some k)=(rows k).succ := rfl
  let scales : Option ((κ₁ ⊕ κ₂) ⊕ τ) → ℝ := fun o=>o.elim 1 (Sum.elim scale (fun _=>1))
  have sc (i) : scales i≠0 := by rcases i with _|(_|_) <;> first | exact one_ne_zero | exact nz _
  have missing i (hi : i.succ∉Set.range p) : i∉Set.range rows := by
    rintro ⟨o,rfl⟩
    exact hi ⟨some o,rfl⟩
  apply positiveMarkCore_of_numbered_rows p K scales sc (Matrix.diagonal (fun _=>1))
    (fun i=>Fin.cases (fun hi=>False.elim (hi ⟨none,rfl⟩)) (fun i hi=>rhs i (missing i hi)) i)
  · intro i
    refine Fin.cases (fun hi=>False.elim (hi ⟨none,rfl⟩)) ?_ i
    intro i hi j hj
    rcases Finset.mem_union.mp hj with hj|hj
    · exact outside i (missing i hi) j hj
    · obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hj
      exact extra i (missing i hi) t
  let V := jointRows (rel.matrix.submatrix p (Subtype.val : K→_)) scales
    ((bracketMarkMatrix s rel x).submatrix id (Subtype.val : K→_))
  apply diagonal_gram_positive V
  intro v ne
  have hasColumn : ∃ j : K, (V.transpose *ᵥ v) j ≠ 0 := by
    by_contra! zero
    let u : Option (κ₁ ⊕ κ₂) ⊕ Fin (2*s.degree-2) → ℝ :=
      Sum.elim (fun o=>v (.inl (o.map Sum.inl))) (fun i=>v (.inr i))
    have old (j : J) : (U.transpose *ᵥ u) j=0 := by
      let j' : K := ⟨j.val,Finset.mem_union_left _ j.prop⟩
      have h := zero j'
      have br (i) : (pairedHelmertMatrix (concreteRowCode s.degree)*L) i j=bracketMarkMatrix s rel x i j.val := by
        rw [bracketMarkMatrix_eq_raw]
        rfl
      have base : rel.matrix 0 j.val=1 := rfl
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_sum_type,
        Fintype.sum_option, V, jointRows, Matrix.submatrix_apply, id_eq, pn, ps,
        scales,Option.elim,Sum.elim_inl,Sum.elim_inr,j',base,
        Int.cast_one,one_mul,miss _ _ j.prop,Int.cast_zero,zero_mul,Finset.sum_const_zero,add_zero] at h
      simpa only [U,twoFieldRows,Matrix.mulVec,dotProduct,Matrix.transpose_apply,Fintype.sum_sum_type,
        Fintype.sum_option,u,Sum.elim_inl,Sum.elim_inr,Option.map_none,Option.map_some,br,one_mul,z] using h
    have dead : u=0 := by
      by_contra un
      have pos := (Matrix.posDef_iff_dotProduct_mulVec.mp gram).2 un
      rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,show U.transpose *ᵥ u=0 from funext old] at pos
      simp at pos
    have vo (i : κ₁ ⊕ κ₂) : v (.inl (some (.inl i)))=0 := congrFun dead (.inl (some i))
    have vi : v (.inl none)=0 := congrFun dead (.inl none)
    have va (i) : v (.inr i)=0 := congrFun dead (.inr i)
    have vt (r : τ) : v (.inl (some (.inr r)))=0 := by
      let j : K := ⟨pick r,Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
      have h := zero j
      simpa [V,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fintype.sum_option,jointRows,
        pn,ps,scales,vo,vi,va,j,hits,ite_mul] using h
    apply ne
    funext i
    rcases i with (_|i)
    · rename_i i
      rcases i with _|(_|_)
      · exact vi
      · exact vo _
      · exact vt _
    · exact va _
  obtain ⟨j,hj⟩ := hasColumn
  simpa only [one_mul] using Finset.sum_pos' (s:=Finset.univ)
    (fun (k : K) _=>sq_nonneg ((V.transpose *ᵥ v) k)) ⟨j,Finset.mem_univ _,sq_pos_of_ne_zero hj⟩

end Cogentic

#print axioms Cogentic.positiveMarkCore_of_target_witnesses
