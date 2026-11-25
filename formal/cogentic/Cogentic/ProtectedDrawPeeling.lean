import Cogentic.ProtectedRank
import Cogentic.RetainedDenominatorPeeling

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- The returned relation matrix on this specified tuple has independent
true log, intercept and target rows, including the bracket projection. -/
def protectedDrawRank (n ell : ℕ) (u v : ℤ×ℤ) : Prop :=
  let s := TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat)
  let S := (wanted s.degree ell (Fixed.rootBase n)).toFinset
  ∃ rel, Marking.stageOne s=some rel ∧ (∀ r, Marking.Row.mk false ell r ∈ rel.rows ↔ r∈S) ∧
    ∃ x : Bool → Fin s.degree → ℝ,
      (∀ side j, x side j ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ) ∧
        RootLogs.normalized s.A (s.coeffs side) (x side j)=0) ∧
      IndependentWithTargets rel S ell (fun j i=>log |(rel.marks.get i:ℝ)/s.A-x (gridPlace j).1 (gridPlace j).2|) ∧
      IndependentWithTargets rel S ell (bracketMarkMatrix s rel x)

/-- The protected rank on boxed draws is certified by a nonnegative test
of arbitrarily small expectation under the actual unrestricted law. -/
theorem protected_rank_test (line : DirichletLZerosOnLine) (k : ℕ) (hk : 0<k) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∃ (test : Ω→ℝ) (μ : ℝ), (∀ t,0≤test t) ∧ HasSum (fun t=>twoFieldWeight O O t*test t) μ ∧ μ≤1/(k:ℝ) ∧
      ∀ t : Ω, inCoefficientBox n t.1.val → inCoefficientBox n t.2.val → test t<1 → protectedDrawRank n ell t.1.val t.2.val := by
  classical
  obtain ⟨n₀,test⟩ := target_class_count_test line k hk
  obtain ⟨b₀,grows⟩ := Fixed.degree_grows 130000
  refine ⟨max n₀ (max 2 (2^b₀)),?_⟩
  intro n large ell target comp absent O Ω
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  let b := n.log2+1; let d := Fixed.d b; let m := Fixed.rootBase n
  have deg := grows b (((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _))
  let C := Option (Bool×Fin d); let I := C ⊕ Fin d; let roots := wanted d ell m
  have spec := wanted_spec (target_gt_degree target) m
  have len : roots.length=d := spec.1
  let row (i : Fin d) := roots.get ⟨i.val,len.symm ▸ i.isLt⟩
  let c : I→C := Sum.elim id (fun _=>none)
  let r : I→ℕ := Sum.elim (fun _=>m) row
  have bound : Fintype.card I≤4*Fixed.d b+4 := by simp [I,C,d];omega
  obtain ⟨f,μ,fn,ex,rate,pass⟩ := test n old ell target comp absent I bound c r
  refine ⟨f,μ,fn,ex,rate,?_⟩
  intro t bu bv small
  obtain ⟨rel,stage,counts⟩ := pass t bu bv small
  have hits (i : I) : ∃ a∈constructorCellMarks n ell (c i), a ≡ r i [MOD ell] ∧ a∈rel.marks := by
    let Y := (constructorCellMarks n ell (c i)).filter (fun a=>a ≡ r i [MOD ell] ∧ a∈rel.marks)
    have yp : Y.Nonempty := by
      by_contra! he
      have count := counts i
      change 4*(cellMarkCount b:ℝ) ≤ _*Y.card at count
      rw [he,card_empty,Nat.cast_zero,mul_zero] at count
      have mp : (0:ℝ)<cellMarkCount b := by dsimp [cellMarkCount];positivity
      linarith
    obtain ⟨a,ha⟩ := yp
    exact ⟨a,mem_filter.mp ha⟩
  refine ⟨rel,stage,fun r=>by simpa using computed_target_row_iff (show 3≤Fixed.d b by omega) target stage r,?_⟩
  apply protected_rank_of_cell_hits hn deg target _ _ rel bu bv stage
  · intro i
    obtain ⟨a,am,ar,arr⟩ := hits (.inl i)
    exact ⟨a,am,arr,ar⟩
  · intro z hz
    obtain ⟨i,eq⟩ := List.mem_iff_get.mp hz
    let j : Fin d := ⟨i.val,len ▸ i.isLt⟩
    obtain ⟨a,am,ar,arr⟩ := hits (.inr j)
    have eq' : row j=z := eq
    change a%ell=row j%ell at ar
    exact ⟨a,am,arr,ar.trans (by rw [eq',Nat.mod_eq_of_lt ((spec.2.2 z hz).1)])⟩

/-- The first-stage protected rank, denominator, ordinary-row rejection
energy, and any additional tests all hold on one actual draw. A freely
chosen inverse integer controls the extra budget for the protected rank. -/
theorem protected_rank_denominator_peeling (line : DirichletLZerosOnLine) (k : ℕ) (hk : 0<k) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let e := exp (-(Fixed.z b:ℝ)^2)
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c, 0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ mass scale : Marking.Row→ℝ, (∀ i,i.q.Prime → mass i*scale i^2=1) →
    ∀ (cost : Ω→ℝ) (budget : ℝ), (∀ t,0≤cost t) →
    HasSum (fun t=>twoFieldWeight O O t*cost t) budget →
    budget+1/(k:ℝ)+256/(Fixed.d b:ℝ)+5*e+1/(Fixed.B b:ℝ)<1 →
    ∃ t : Ω, let x := t.1.val; let y := t.2.val
      let input := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
      let rows := input.rows.toFinset.filter (fun i=>i.q≠ell)
      let X := univ.biUnion (constructorCellMarks n ell)
      let Y := X.filter (fun a=>rejectedSmoothMark O O a x y)
      let wt := fun a=>constructorMixturePrior n ell mix a/smoothMarkProbability O O a
      let z := fun (i : Marking.Row) (a : ℕ)=>if a%i.q=i.r then scale i else 0
      let bad := rows.filter (fun i=>e ≤ ∑ a∈Y,wt a*(z i a)^2)
      retainedDenominatorGood n ell mix x y ∧ protectedDrawRank n ell x y ∧ cost t<1 ∧
      (∑ a∈Y,wt a)<e^3 ∧ (∑ i∈bad,mass i)≤b*e^2 ∧
      ∀ v : Marking.Row→ℝ, (∑ a∈Y,wt a*(∑ i∈rows\bad,z i a*v i)^2)≤
        (b:ℝ)*e*(∑ i∈rows\bad,(v i)^2) := by
  obtain ⟨n₁,rankTest⟩ := protected_rank_test line k hk
  obtain ⟨n₂,peeling⟩ := retained_denominator_rejection_peeling line
  refine ⟨max n₁ n₂,?_⟩
  intro n large ell target comp absent b e O Ω mix pos norm mass scale unit cost budget cn ec fit
  obtain ⟨nr,np⟩ := max_le_iff.mp large
  obtain ⟨f,μ,fn,ef,rate,passes⟩ := rankTest n nr ell target comp absent
  have both : HasSum (fun t:Ω=>twoFieldWeight O O t*(cost t+f t)) (budget+μ) :=
    (ec.add ef).congr_fun (fun t=>mul_add ..)
  have small : budget+μ+256/(Fixed.d b:ℝ)+5*e+1/(Fixed.B b:ℝ)<1 := by linarith only [fit,rate]
  obtain ⟨t,good,tests,loss,bad,energy⟩ := peeling n np ell target comp absent mix pos norm mass scale unit
    (fun t=>cost t+f t) _ (fun t=>add_nonneg (cn t) (fn t)) both small
  exact ⟨t,good,passes t good.1 good.2.1 ((le_add_of_nonneg_left (cn t)).trans_lt tests),
    (le_add_of_nonneg_right (fn t)).trans_lt tests,loss,bad,energy⟩

end
end Cogentic.Construction

#print axioms Cogentic.Construction.protected_rank_denominator_peeling
