import Cogentic.RetainedTargetCore
import Cogentic.ModelRank
import Cogentic.CoefficientBox
import Cogentic.RankCoverage

namespace Cogentic.Construction
open Marking Finset Real
open scoped Matrix
noncomputable section

/-- Intercept, ordered true root logarithms and ordinary incidence at one retained mark. -/
def retainedMissColumn (s : Input) (A : Finset Row) (scale : A→ℝ)
    (x : Bool→Fin s.degree→ℝ) (a : ℕ) : Option (Fin (2*s.degree)) ⊕ A → ℝ
  | .inl none => 1
  | .inl (some j) => log |(a:ℝ)/s.A-x (gridPlace j).1 (gridPlace j).2|
  | .inr i => if a%i.val.q=i.val.r then scale i else 0

theorem retainedMissColumn_score (s : Input) (A : Finset Row) (scale : A→ℝ)
    (x : Bool→Fin s.degree→ℝ) (a : ℕ) (t : Option (Fin (2*s.degree)) ⊕ A → ℝ) :
    (∑ i,retainedMissColumn s A scale x a i*t i) =
      (t (.inl none)+∑ i : A,t (.inr i)*(if a%i.val.q=i.val.r then scale i else 0))+
      ∑ j,t (.inl (some j))*log |(a:ℝ)/s.A-x (gridPlace j).1 (gridPlace j).2| := by
  rw [Fintype.sum_sum_type,Fintype.sum_option]
  simp only [retainedMissColumn,one_mul]
  simp_rw [mul_comm (ite _ _ _) _,mul_comm (log _) _]
  ring

/-- Ordinary executable rows left after the prescribed row indices are peeled. -/
def remainingOrdinaryRows {ι : Type*} (rel : Relations) (ell : ℕ) (row : ι→Row) (D : Finset ι) :=
  (rel.rows.toFinset.filter (fun r=>r.q≠ell)) \ D.image row

theorem remainingOrdinaryRows_spec {ι : Type*} (rel : Relations) (ell : ℕ) (row : ι→Row) (D : Finset ι)
    (canonical : ∀ i∈D,(row i).r<(row i).q) :
    let A := remainingOrdinaryRows rel ell row D
    A⊆rel.rows.toFinset ∧ (∀ r∈A,r.q≠ell) ∧
      ∀ a : ℕ, (∀ i∈D,¬a ≡ (row i).r [MOD (row i).q]) →
        ∀ r∈rel.rows,r.q≠ell → r∉A → a%r.q≠r.r := by
  classical
  intro A
  refine ⟨fun _ h=>(mem_filter.mp (mem_sdiff.mp h).1).1,
    fun _ h=>(mem_filter.mp (mem_sdiff.mp h).1).2,?_⟩
  intro a untouched r listed ordinary removed
  have hr : r∈D.image row := by
    by_contra no
    exact removed (mem_sdiff.mpr ⟨mem_filter.mpr ⟨List.mem_toFinset.mpr listed,ordinary⟩,no⟩)
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt (canonical i hi)] using untouched i hi

/-- Assemble a boxed rank witness from the miss-column energy and a retained
representative for each target row. The bracket roots come from this same tuple. -/
theorem boxHasRank_of_retained_energy {n ell : ℕ} (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    {u v : ℤ×ℤ} (bu : inCoefficientBox n u) (bv : inCoefficientBox n v) :
    let s := TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat)
    ∀ {rel}, stageOne s=some rel → ∀ (A : Finset Row) (Y : Finset ℕ),
    A⊆rel.rows.toFinset → (∀ i∈A,i.q≠ell) → Y⊆rel.marks.toFinset →
    (∀ r∈rel.rows,r.q=ell → ∀ a∈Y,a%ell≠r.r) →
    let avoids := fun a=>∀ i∈rel.rows,i.q≠ell → i∉A → a%i.q≠i.r
    (∀ a∈Y,avoids a) → (∀ r∈rel.rows,r.q=ell → ∃ a∈rel.marks,a%ell=r.r ∧ avoids a) →
    ∀ (scale : A→ℝ) (weight : ℕ→ℝ), (∀ i,scale i≠0) →
    (∀ x : Bool→Fin s.degree→ℝ,
      (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
        RootLogs.normalized s.A (s.coeffs side) (x side i)=0) →
      ∀ t : Option (Fin (2*s.degree)) ⊕ A → ℝ, t≠0 →
      (∀ side : Bool,(∑ i : A,if i.val.second=side then log i.val.q/scale i*t (.inr i) else 0)=0) →
      0 < ∑ a∈Y,weight a*(∑ i,retainedMissColumn s A scale x a i*t i)^2) →
    Concrete.BoxHasRank n ell := by
  classical
  intro s rel marked A Y listed ordinary retained miss avoids clean picks scale weight nz energy
  obtain ⟨u₁,u₂⟩ := bu.nat_ranges
  obtain ⟨v₁,v₂⟩ := bv.nat_ranges
  obtain ⟨_,x,_,xr,_,_⟩ := constructed_mark_logs hn big target ⟨u₁.2,u₂.2,v₁.2,v₂.2⟩ marked
  have roots (side) (i) := And.intro (xr side i).2.1 (xr side i).2.2.1
  refine ⟨_,_,_,_,u₁,u₂,v₁,v₂,rel,marked,x,roots,?_⟩
  apply positiveMarkCore_of_retained_sets hn big target marked x roots A Y listed ordinary retained miss clean picks scale weight nz
  intro v₀ f g perp ne
  let e := interleavePlaces s.degree
  let t : Option (Fin (2*s.degree)) ⊕ A → ℝ := Sum.elim (fun i=>i.elim v₀ (fun j=>g (e.symm j))) f
  have nonzero : t≠0 := by
    intro zero
    apply ne
    refine ⟨congrFun zero (.inl none),funext (fun i=>congrFun zero (.inr i)),?_⟩
    funext i
    simpa only [t,Sum.elim_inl,Option.elim_some,e.symm_apply_apply,Pi.zero_apply] using congrFun zero (.inl (some (e i)))
  have pos := energy x roots t nonzero perp
  apply lt_of_lt_of_eq pos
  apply sum_congr rfl
  intro a _
  congr 2
  let l := fun (k : Fin s.degree ⊕ Fin s.degree)=>k.elim
    (fun i=>log |(a:ℝ)/s.A-x false i|) (fun i=>log |(a:ℝ)/s.A-x true i|)
  have logAt (k) : log |(a:ℝ)/s.A-x (gridPlace (e k)).1 (gridPlace (e k)).2|=l k := by
    cases k <;> simp [e,l,gridPlace]
  rw [retainedMissColumn_score]
  simp only [t,Sum.elim_inl,Sum.elim_inr,Option.elim_none,Option.elim_some]
  congr 1
  rw [←e.sum_comp]
  simp only [logAt,e.symm_apply_apply,dotProduct]
  rfl

end
end Cogentic.Construction

#print axioms Cogentic.Construction.boxHasRank_of_retained_energy
