import Cogentic.TargetRankExtension

namespace Cogentic
open Marking Finset Real
open scoped Matrix BigOperators

/-- Numerical positivity on the retained ordinary rows and target-free marks,
plus one retained mark per target residue, gives the executable certificate.
All row and mark indices in the hypotheses are their physical values. -/
theorem positiveMarkCore_of_retained_sets {N ell a b c d : ℕ} (hn : 2≤N)
    (big : 10004≤Fixed.d (N.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (N.log2+1))) :
    let s := TryPair.fixedInput N ell (Construction.construct N ell a b c d)
    ∀ {rel}, stageOne s=some rel → ∀ x : Bool → Fin s.degree → ℝ,
    (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
      RootLogs.normalized s.A (s.coeffs side) (x side i)=0) →
    ∀ (A : Finset Row) (Y : Finset ℕ), A⊆rel.rows.toFinset → (∀ i∈A,i.q≠ell) → Y⊆rel.marks.toFinset →
    (∀ r∈rel.rows, r.q=ell → ∀ y∈Y, y%ell≠r.r) →
    let avoids := fun (y : ℕ)=>∀ i∈rel.rows, i.q≠ell → i∉A → y%i.q≠i.r
    (∀ y∈Y, avoids y) → (∀ i∈rel.rows, i.q=ell → ∃ y∈rel.marks,y%ell=i.r ∧ avoids y) →
    ∀ (scale : A→ℝ) (weight : ℕ→ℝ), (∀ i,scale i≠0) →
    let z := fun (i : A) (y : ℕ)=>if y%i.val.q=i.val.r then scale i else 0
    let logs := fun (y : ℕ) (k : Fin s.degree ⊕ Fin s.degree)=>
      k.elim (fun i=>log |(y:ℝ)/s.A-x false i|) (fun i=>log |(y:ℝ)/s.A-x true i|)
    (∀ (v₀ : ℝ) (f : A→ℝ) (g : Fin s.degree ⊕ Fin s.degree→ℝ),
      (∀ side : Bool, (∑ i : A,if i.val.second=side then log i.val.q/scale i*f i else 0)=0) →
      ¬(v₀=0 ∧ f=0 ∧ g=0) →
      0 < ∑ y∈Y,weight y*(v₀+(∑ i : A, f i*z i y)+g ⬝ᵥ logs y)^2) → PositiveMarkCore s rel x := by
  classical
  intro s rel stage x roots A Y listed away retained targetMiss avoids noBad witness scale weight nz z logs model
  let P := fun i : A=>i.val.second=false
  let L := {i : A // P i}; let R := {i : A // ¬P i}
  let e : L ⊕ R ≃ A := Equiv.sumCompl P
  have sides (o : L ⊕ R) : (e o).val.second=o.elim (fun _=>false) (fun _=>true) := by
    cases o with
    | inl i => exact i.prop
    | inr i => exact Bool.eq_true_of_not_eq_false i.prop
  let T := {i : Fin rel.rows.length // (rel.rows.get i).q=ell}
  have ord (i : A) : ∃ j, rel.rows.get j=i.val := List.mem_iff_get.mp (List.mem_toFinset.mp (listed i.prop))
  choose idx rowAt using ord
  have ii : Function.Injective idx := fun i j h=>Subtype.ext ((rowAt i).symm.trans ((congrArg rel.rows.get h).trans (rowAt j)))
  let fn := Sum.elim (idx ∘ e) (Subtype.val : T→_)
  have disj (k : L ⊕ R) (t : T) : idx (e k)≠t.val := by
    intro eq
    exact away _ (e k).prop ((congrArg Row.q ((rowAt (e k)).symm.trans (congrArg rel.rows.get eq))).trans t.prop)
  let rows : ((L ⊕ R) ⊕ T) ↪ Fin rel.rows.length :=
    ⟨fn,by
      rintro (o|t) (o'|t') h
      · exact congrArg Sum.inl (e.injective (ii h))
      · exact False.elim (disj o t' h)
      · exact False.elim (disj o' t h.symm)
      · exact congrArg Sum.inr (Subtype.ext h)⟩
  have rowO o : rel.rows.get (rows (.inl o))=(e o).val := rowAt _
  have notIn i (hi : i∉Set.range rows) : (rel.rows.get i).q≠ell ∧ rel.rows.get i∉A := by
    have nd : rel.rows.Nodup := (rows_and_guards stage).2.2.2.1 ▸ (List.nodup_dedup _).filter _
    refine ⟨fun eq=>hi ⟨.inr ⟨i,eq⟩,rfl⟩,fun mem=>?_⟩
    let a : A := ⟨rel.rows.get i,mem⟩
    obtain ⟨k,hk⟩ := e.surjective a
    exact hi ⟨.inl k,nd.injective_get (by rw [rowO,hk])⟩
  have targets (t : T) : (rel.rows.get t.val).second=false := by
    have clean : rel.rows.get t.val∈s.clean := (rows_and_guards stage).2.2.2.1 ▸ rel.rows.get_mem _
    exact (Construction.target_rows_clean (by omega) target a b c d _ (mem_clean.mp clean).1 t.prop).1
  have rowEq (u v : Row) (hs : u.second=v.second) (hq : u.q=v.q) (hr : u.r=v.r) : u=v := by
    cases u; cases v; simp_all
  have rid {r t : T} : (rel.rows.get r.val).r=(rel.rows.get t.val).r ↔ r=t := by
    refine ⟨fun hr=>?_,fun h=>congrArg (fun k : T=>(rel.rows.get k.val).r) h⟩
    have eq := rowEq _ _ ((targets r).trans (targets t).symm) (r.prop.trans t.prop.symm) hr
    have nd : rel.rows.Nodup := (rows_and_guards stage).2.2.2.1 ▸ (List.nodup_dedup _).filter _
    exact Subtype.ext (nd.injective_get eq)
  choose yPick yp yr ya using fun t : T=>witness (rel.rows.get t.val) (rel.rows.get_mem _) t.prop
  choose pick hp using fun t : T=>List.mem_iff_get.mp (yp t)
  choose markIndex markAt using fun y : Y=>List.mem_iff_get.mp (List.mem_toFinset.mp (retained y.prop))
  let J := univ.image markIndex
  let j : Y ≃ J := Equiv.ofBijective (fun y=>⟨markIndex y,mem_image.mpr ⟨y,mem_univ _,rfl⟩⟩)
    ⟨fun a b eq=>Subtype.ext ((markAt a).symm.trans ((congrArg rel.marks.get (congrArg Subtype.val eq)).trans (markAt b))),
     fun b=>by obtain ⟨y,_,ey⟩ := mem_image.mp b.prop; exact ⟨y,Subtype.ext ey⟩⟩
  have inside k (hk : k∈J) : rel.marks.get k∈Y := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hk; rw [markAt]; exact y.prop
  have whichTarget : rel.target=ell := (rows_and_guards stage).2.2.1
  refine positiveMarkCore_of_target_witnesses hn big target stage x roots rows J pick (scale ∘ e)
    (fun _=>nz _) (fun i=>(congrArg Row.second (rowO i)).trans (sides i)) ?_ ?_ ?_ ?_ ?_ (fun k=>weight (rel.marks.get k.val)) ?_
  · intro i hi
    simp only [Relations.rhs,Fin.cases_succ,whichTarget,Bool.and_eq_true,beq_iff_eq]
    exact if_neg (fun h=>(notIn i hi).1 h.2)
  · intro i hi k hk
    have h := noBad _ (inside k hk) _ (rel.rows.get_mem i) (notIn i hi).1 (notIn i hi).2
    exact if_neg h
  · intro i hi t
    have h := ya t _ (rel.rows.get_mem i) (notIn i hi).1 (notIn i hi).2
    change (if rel.marks.get (pick t)%(rel.rows.get i).q=(rel.rows.get i).r then (1:ℤ) else 0)=0
    rw [hp,if_neg h]
  · intro t k hk
    have h := targetMiss _ (rel.rows.get_mem t.val) t.prop _ (inside k hk)
    change (if _%(rel.rows.get t.val).q=(rel.rows.get t.val).r then (1:ℤ) else 0)=0
    rw [t.prop,if_neg h]
  · intro r t
    change (if rel.marks.get (pick t)%(rel.rows.get r.val).q=(rel.rows.get r.val).r then (1:ℤ) else 0)=_
    rw [hp,r.prop,yr]
    by_cases eq : r=t
    · subst r; simp
    · rw [if_neg eq,if_neg (fun h=>eq (rid.mp h.symm))]
  intro v₀ f₁ f₂ g perp₁ perp₂ ne
  let f := fun i : A=>Sum.elim f₁ f₂ (e.symm i)
  have ff (k) : f (e k)=Sum.elim f₁ f₂ k := by simp only [f,e.symm_apply_apply]
  have perp (side : Bool) : (∑ i : A,if i.val.second=side then log i.val.q/scale i*f i else 0)=0 := by
    rw [←e.sum_comp,Fintype.sum_sum_type]
    cases side
    · simpa only [sides,Sum.elim_inl,Sum.elim_inr,Bool.true_eq_false,if_false,if_true,ff,sum_const_zero,add_zero,
        dotProduct,Function.comp_apply,rowO] using perp₁
    · simpa only [sides,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,if_false,if_true,ff,sum_const_zero,zero_add,
        dotProduct,Function.comp_apply,rowO] using perp₂
  have nonzero : ¬(v₀=0 ∧ f=0 ∧ g=0) := by
    rintro ⟨v0,f0,g0⟩
    refine ne ⟨v0,funext (fun i=>?_),funext (fun i=>?_),g0⟩
    · exact (ff (.inl i)).symm.trans (congrFun f0 _)
    · exact (ff (.inr i)).symm.trans (congrFun f0 _)
  have h := model v₀ f g perp nonzero
  rw [←j.sum_comp]
  rw [←sum_coe_sort Y] at h
  apply lt_of_lt_of_eq h
  apply sum_congr rfl
  intro y _
  have pos : rel.marks.get (j y).val=y.val := markAt _
  have ordEntry (i) :
      scale (e i)*(rel.matrix (rows (.inl i)).succ (j y).val:ℝ)=z (e i) y.val := by
    simp only [Relations.matrix,Fin.cases_succ,rowO,pos,z]
    split <;> simp
  simp only [pos,←e.sum_comp (fun i=>f i*z i y.val),Fintype.sum_sum_type,ff,Sum.elim_inl,Sum.elim_inr,
    Matrix.submatrix_apply,id_eq,rawMarkMatrix,logs,dotProduct,Function.comp_apply,ordEntry,add_assoc]
  rfl

end Cogentic

#print axioms Cogentic.positiveMarkCore_of_retained_sets
