import Cogentic.GramCandidate
import Cogentic.CompanionReduction
import Cogentic.CoefficientTail
import Cogentic.Rank

namespace Cogentic
open Matrix Marking TwoThirdsSearch
open scoped Matrix BigOperators

/-- Membership in the column space tested by *all* row dependencies. -/
private theorem column_image {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (b : ι → ℝ)
    (vanish : ∀ a : ι → ℝ, (∀ j, ∑ i, a i*M i j=0) → ∑ i,a i*b i=0) :
    ∃ x, M *ᵥ x = b := by
  classical
  by_contra missing
  have out : b∉LinearMap.range M.mulVecLin := missing
  obtain ⟨f,notZero,kernel⟩ := Submodule.exists_le_ker_of_notMem out
  let a : ι → ℝ := fun i=>f (Pi.single i 1)
  have eval (y : ι → ℝ) : f y=∑ i, a i*y i := by
    have expand : y=∑ i, y i • Pi.single i (1:ℝ) := by
      ext i
      simp [Finset.sum_apply,Pi.single_apply,Pi.smul_apply,mul_ite]
    conv_lhs => rw [expand]
    simp [a,map_sum,mul_comm]
  have cols (j) : ∑ i, a i*M i j=0 := by
    rw [←eval]
    apply kernel
    exact ⟨Pi.single j 1, by ext i; simp [mulVec,dotProduct,Pi.single_apply,mul_ite]⟩
  exact notZero ((eval b).trans (vanish a cols))

/-- Ordinary incidence rows may satisfy arbitrary dependencies. Extraction only
requires that a joint dependency has zero target pairing and zero log component. -/
theorem annihilator_descent {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℤ) (b : ι → ℤ) (U : Matrix ν κ ℝ)
    (compatible : ∀ (f : ι → ℝ) (g : ν → ℝ),
      (∀ j, (∑ i, f i*(A i j:ℝ))+(∑ k, g k*U k j)=0) → (∑ i, f i*(b i:ℝ))=0 ∧ g=0) :
    (∃ t : κ → ℚ, ∀ i, ∑ j,(A i j:ℚ)*t j=(b i:ℚ)) ∧
      Submodule.span ℝ {y : ν → ℝ | ∃ z : κ → ℤ, (∀ i, ∑ j,A i j*z j=0) ∧ y=U *ᵥ (fun j=>(z j:ℝ))}=⊤ := by
  classical
  let M : Matrix (ι ⊕ ν) κ ℝ := jointRows A (fun _=>1) U
  have lift (c : ℝ) (v : ν → ℝ) : ∃ x, M *ᵥ x = Sum.elim (fun i => c*(b i:ℝ)) v := by
    apply column_image
    intro a left
    obtain ⟨target,logs⟩ := compatible (fun i=>a (.inl i)) (fun k=>a (.inr k))
      (fun j => by simpa [M,jointRows,Fintype.sum_sum_type] using left j)
    have gzero (k : ν) : a (.inr k)=0 := congrFun logs k
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,gzero,zero_mul,Finset.sum_const_zero,add_zero]
    simpa only [Finset.mul_sum,mul_left_comm,mul_zero] using congrArg (c*·) target
  constructor
  · obtain ⟨x,hx⟩ := lift 1 0
    apply rational_incidence_solution A b x
    intro i
    simpa [M,jointRows,mulVec,dotProduct] using congrFun hx (.inl i)
  · let S := Submodule.span ℝ {y : ν → ℝ | ∃ z : κ → ℤ, (∀ i, ∑ j,A i j*z j=0) ∧ y=U *ᵥ (fun j=>(z j:ℝ))}
    apply top_unique
    intro y _
    obtain ⟨x,hx⟩ := lift 0 y
    have neutral (i : ι) : ∑ j, (A i j:ℝ)*x j=0 := by
      simpa [M,jointRows,mulVec,dotProduct] using congrFun hx (.inl i)
    have image : U *ᵥ x = y := funext fun k=>congrFun hx (.inr k)
    have exactKernel := real_kernel_spanned_by_integer A x neutral
    have span_le : Submodule.span ℝ {v : κ → ℝ | ∃ z : κ → ℤ,
        (∀ i, ∑ j,A i j*z j=0) ∧ v=fun j=>(z j:ℝ)} ≤ S.comap U.mulVecLin := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z,hz,rfl⟩
      exact Submodule.subset_span ⟨z,hz,rfl⟩
    rw [←image]
    exact span_le exactKernel

/-- A dependency that fails the test also obstructs at least one of the two
span conditions used by extraction. -/
theorem annihilator_criterion {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℤ) (b : ι → ℤ) (U : Matrix ν κ ℝ) :
    (∀ (f : ι → ℝ) (g : ν → ℝ),
      (∀ j, (∑ i, f i*(A i j:ℝ))+(∑ k, g k*U k j)=0) → (∑ i, f i*(b i:ℝ))=0 ∧ g=0) ↔
    (∃ t : κ → ℚ, ∀ i, ∑ j,(A i j:ℚ)*t j=(b i:ℚ)) ∧
      Submodule.span ℝ {y : ν → ℝ | ∃ z : κ → ℤ, (∀ i, ∑ j,A i j*z j=0) ∧ y=U *ᵥ (fun j=>(z j:ℝ))}=⊤ := by
  classical
  refine ⟨annihilator_descent A b U,?_⟩
  rintro ⟨⟨t,ht⟩,span⟩ f g dep
  have paired (v : κ → ℝ) :
      (∑ i, f i*(∑ j,(A i j:ℝ)*v j)) + (∑ k, g k*(U *ᵥ v) k)=0 := by
    simp only [mulVec,dotProduct,Finset.mul_sum,←mul_assoc]
    rw [Finset.sum_comm (f := fun i j=>f i*(A i j:ℝ)*v j),
      Finset.sum_comm (f := fun k j=>g k*U k j*v j),←Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    simpa [Finset.sum_mul,add_mul] using congrArg (·*v j) (dep j)
  have orthogonal (y : ν → ℝ) : ∑ k, g k*y k=0 := by
    have mem : y∈Submodule.span ℝ {q : ν → ℝ | ∃ z : κ → ℤ, (∀ i, ∑ j,A i j*z j=0) ∧
        q=U *ᵥ (fun j=>(z j:ℝ))} := span ▸ Submodule.mem_top
    induction mem using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z,hz,rfl⟩ := hy
      have zero (i) : ∑ j,(A i j:ℝ)*(z j:ℝ)=0 := by exact_mod_cast hz i
      simpa [zero] using paired (fun j=>(z j:ℝ))
    | zero => simp
    | add u v _ _ hu hv => simp [mul_add,Finset.sum_add_distrib,hu,hv]
    | smul a v _ hv =>
      simpa [Pi.smul_apply,smul_eq_mul,mul_left_comm,←Finset.mul_sum] using congrArg (a*·) hv
  have gone : g=0 := by
    ext k
    simpa [Pi.single_apply,mul_ite] using orthogonal (Pi.single k 1)
  refine ⟨?_,gone⟩
  have actual (i) : ∑ j,(A i j:ℝ)*(t j:ℝ)=(b i:ℝ) := by exact_mod_cast ht i
  simpa [gone,actual] using paired (fun j=>(t j:ℝ))

/-- The exact row-dependency test on the relation object returned by stage one. -/
def CompatibleRelations (s : Marking.Input) (rel : Relations)
    (x : Bool → Fin s.degree → ℝ) : Prop :=
  ∀ (f : Fin (rel.rows.length+1) → ℝ) (g : Fin (2*s.degree-2) → ℝ),
    (∀ j, (∑ i, f i*(rel.matrix i j:ℝ))+(∑ k, g k*bracketMarkMatrix s rel x k j)=0) →
    (∑ i, f i*(rel.rhs i:ℝ))=0 ∧ g=0

/-- A sufficient condition on the actual computed rows, including dependent
ordinary rows, for a search tuple to return a verified divisor or exponent. -/
theorem candidate_of_annihilator {n ell u v w z : ℕ} (hn : 2≤n)
    (big : 130000≤Fixed.d (n.log2+1)) (composite : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (box : let b:=n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
        w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
    (∀ rel, stageOne s=some rel → ∃ x : Bool → Fin s.degree → ℝ,
      (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
        RootLogs.normalized s.A (s.coeffs side) (x side i)=0) ∧
      CompatibleRelations s rel x) →
    verify n ell (Concrete.candidate n ell u v w z)≠none := by
  intro s h
  apply candidate_of_concrete_spans hn big composite target sieved box
  intro rel marked
  obtain ⟨x,roots,compat⟩ := h rel marked
  obtain ⟨aff,span⟩ := annihilator_descent rel.matrix (-rel.rhs) (bracketMarkMatrix s rel x) (by
    intro f g dep
    obtain ⟨target,logs⟩ := compat f g dep
    exact ⟨by simpa [Finset.sum_neg_distrib] using congrArg Neg.neg target,logs⟩)
  exact ⟨by simpa using aff,x,roots,span⟩

/-- Convert the positive coefficient pairs produced by the local supply theorem
directly to the per-target witness consumed by complete factorization. -/
theorem boxHit_of_annihilator {n ell : ℕ} {u v : ℤ×ℤ} {rel : Relations} (hn : 2≤n)
    (big : 130000≤Fixed.d (n.log2+1)) (composite : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (bu : Construction.inCoefficientBox n u) (bv : Construction.inCoefficientBox n v) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat)
    stageOne s=some rel → ∀ x : Bool → Fin s.degree → ℝ,
    (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
      RootLogs.normalized s.A (s.coeffs side) (x side i)=0) →
    CompatibleRelations s rel x → Companion.BoxHit n ell := by
  intro s marked x roots compat
  obtain ⟨a,c⟩ := bu.nat_ranges
  obtain ⟨e,f⟩ := bv.nat_ranges
  refine ⟨_,_,_,_,a,c,e,f,candidate_of_annihilator hn big composite target sieved
    ⟨a.2,c.2,e.2,f.2⟩ ?_⟩
  intro rel' same
  change stageOne s=some rel' at same
  cases Option.some.inj (marked.symm.trans same)
  exact ⟨x,roots,compat⟩

end Cogentic

#print axioms Cogentic.candidate_of_annihilator
