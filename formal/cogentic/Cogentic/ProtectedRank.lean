import Cogentic.RetainedArchRank
import Cogentic.TargetClassSupply

namespace Cogentic.Construction
open Finset Real Polynomial Matrix
open scoped Matrix

/-- The protected colors index exactly the target rows present in the computed matrix. -/
theorem computed_target_row_iff {n ell u v w z : ℕ}
    (hd : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) :
    let s := TryPair.fixedInput n ell (construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel → ∀ r,
      (Marking.Row.mk false ell r) ∈ rel.rows ↔ r ∈ wanted s.degree ell (Fixed.rootBase n) := by
  intro s rel marked r
  have : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
  let f := (Marking.polynomial s.first).map (Int.castRingHom (ZMod ell))
  let rs := wanted (Fixed.d (n.log2+1)) ell (Fixed.rootBase n)
  have poly := (target_polynomials (show 2≤Fixed.d (n.log2+1) by omega) target u v w z).1
  have allRoots : f.roots = ((rs.map (fun a : ℕ=>(a:ZMod ell)) : List (ZMod ell)) : Multiset (ZMod ell)) := by
    change ((Marking.polynomial (construct n ell u v w z).first).map _).roots = _
    rw [poly,roots_C_mul _ (leading_unit_at_target hd target)]
    simpa [rs,List.map_map,Function.comp_def] using roots_multiset_prod_X_sub_C
      ((rs.map (fun a : ℕ=>(a:ZMod ell)) : List (ZMod ell)) : Multiset (ZMod ell))
  have listSpec := wanted_spec (target_gt_degree target) (Fixed.rootBase n)
  have fne : f≠0 := by
    intro zero
    have eq := congrArg Multiset.card allRoots
    rw [zero,roots_zero] at eq
    simp [rs,listSpec.1] at eq
    omega
  have base := (Marking.rows_and_guards marked).2.1
  have rows := (Marking.rows_and_guards marked).2.2.2.1
  rw [rows]
  constructor
  · intro hr
    obtain ⟨_,small,root⟩ := Marking.mem_rows.mp (Marking.mem_clean.mp hr).1
    have root' : f.IsRoot (r:ZMod ell) := (Polynomial.eval_map ..).trans root
    have hmem := (mem_roots fne).mpr root'
    rw [allRoots] at hmem
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp hmem
    have aSmall := (listSpec.2.2 a ha).1
    have same := congrArg ZMod.val eq
    have rSmall : r<ell := small
    rw [ZMod.val_natCast_of_lt aSmall,ZMod.val_natCast_of_lt rSmall] at same
    exact same ▸ ha
  · intro hr
    have hmem : (r:ZMod ell) ∈ f.roots := by
      rw [allRoots]
      exact List.mem_map.mpr ⟨r,hr,rfl⟩
    have root := (mem_roots fne).mp hmem
    have member : Marking.Row.mk false ell r ∈ s.rows :=
      Marking.mem_rows.mpr ⟨base,(listSpec.2.2 r hr).1, (Polynomial.eval_map ..).symm.trans root⟩
    exact (target_rows_clean hd target u v w z _ member rfl).2

/-- A combination of the target indicator rows evaluates one coefficient at the
observed residue, with zero outside the set of target residues. -/
def targetScore (S : Finset ℕ) (f : S → ℝ) (r : ℕ) : ℝ :=
  if h : r∈S then f ⟨r,h⟩ else 0

/-- Adding the intercept and the target indicators to these rows gives
independent row functions on the retained marks. -/
def IndependentWithTargets {ι : Type*} [Fintype ι] (rel : Marking.Relations)
    (S : Finset ℕ) (ell : ℕ) (rows : Matrix ι (Fin rel.marks.length) ℝ) : Prop :=
  ∀ (t : ℝ) (f : S → ℝ) (y : ι → ℝ), (∀ i, (t+∑ j,rows j i*y j)+
    targetScore S f (rel.marks.get i%ell)=0) → t=0 ∧ f=0 ∧ y=0

private theorem project_independent {s : Marking.Input} (dp : 0<s.degree)
    (rel : Marking.Relations) (S : Finset ℕ) (ell : ℕ) (x : Bool → Fin s.degree → ℝ)
    (indep : IndependentWithTargets rel S ell (fun j i=>log |(rel.marks.get i:ℝ)/s.A-
      x (gridPlace j).1 (gridPlace j).2|)) :
    IndependentWithTargets rel S ell (bracketMarkMatrix s rel x) := by
  intro t f y dep
  let e := interleavePlaces s.degree
  let H := pairedHelmertMatrix (concreteRowCode s.degree)
  let L := rawMarkMatrix s rel x
  let v := H.transpose *ᵥ y
  have cols (j : Fin rel.marks.length) : ∑ k, log |(rel.marks.get j:ℝ)/s.A-
      x (gridPlace k).1 (gridPlace k).2| * v (e.symm k) =
      ∑ i,bracketMarkMatrix s rel x i j*y i := by
    rw [bracketMarkMatrix_eq_raw]
    change _ = ∑ i,(H*L) i j*y i
    rw [←e.sum_comp]
    have row (k : Fin s.degree ⊕ Fin s.degree) :
        log |(rel.marks.get j:ℝ)/s.A-x (gridPlace (e k)).1 (gridPlace (e k)).2| = L k j := by
      cases k <;> simp [gridPlace,e,L,rawMarkMatrix]
    simp_rw [row,Equiv.symm_apply_apply]
    change (∑ k,L k j*((H.transpose *ᵥ y) k))=_
    simp only [mulVec,dotProduct,Matrix.transpose_apply,Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  obtain ⟨tz,fz,vz⟩ := indep t f (fun k=>v (e.symm k)) (fun j=>by simpa only [cols] using dep j)
  have v0 (k) : v k=0 := by simpa using congrFun vz (e k)
  have yz := paired_helmert_transpose_constant dp (concreteRowCode s.degree) y 0 0
    (funext fun k => by cases k <;> exact v0 _)
  exact ⟨tz,fz,yz.1⟩

/-- On any boxed, successful tuple, an off-target mark in each constructor
cell and a baseline mark of each target color suffice for both forms of
independence. The tuple can therefore carry further simultaneous tests. -/
theorem protected_rank_of_cell_hits {n ell : ℕ} (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (u v : ℤ×ℤ) (rel : Marking.Relations)
    (bu : inCoefficientBox n u) (bv : inCoefficientBox n v) :
    let b := n.log2+1; let s := TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat)
    let S := (wanted s.degree ell (Fixed.rootBase n)).toFinset
    Marking.stageOne s=some rel →
    (∀ c : Option (Bool×Fin (Fixed.d b)), ∃ a∈constructorCellMarks n ell c, a∈rel.marks ∧ a%ell=Fixed.rootBase n%ell) →
    (∀ r∈wanted (Fixed.d b) ell (Fixed.rootBase n), ∃ a∈constructorCellMarks n ell none, a∈rel.marks ∧ a%ell=r) →
      ∃ x : Bool → Fin s.degree → ℝ,
        (∀ side j, x side j ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ) ∧
          RootLogs.normalized s.A (s.coeffs side) (x side j)=0) ∧
        IndependentWithTargets rel S ell (fun j i=>log |(rel.marks.get i:ℝ)/s.A-
          x (gridPlace j).1 (gridPlace j).2|) ∧
        IndependentWithTargets rel S ell (bracketMarkMatrix s rel x) := by
  classical
  intro b s S stage quiet hit
  change 130000≤Fixed.d b at big
  have box (k : ℤ×ℤ) (inside : inCoefficientBox n k) :
      k.1.toNat≤2*b^2*Fixed.U b*Fixed.A b ∧ k.2.toNat≤2*b^2*Fixed.U b := by
    obtain ⟨_,l,_,r⟩ := inside
    exact ⟨Int.toNat_le.mpr (by exact_mod_cast l),Int.toNat_le.mpr (by exact_mod_cast r)⟩
  obtain ⟨_,x,_,roots,_,_⟩ := constructed_mark_logs hn (show 10004≤Fixed.d b by omega) target
    ⟨(box u bu).1,(box u bu).2,(box v bv).1,(box v bv).2⟩ stage
  refine ⟨x,fun side j=>⟨(roots side j).2.1,(roots side j).2.2.1⟩,?_⟩
  suffices h : IndependentWithTargets rel _ ell (fun j i=>log |(rel.marks.get i:ℝ)/s.A-
      x (gridPlace j).1 (gridPlace j).2|) from
    ⟨h,project_independent (show 0<s.degree by change 0<Fixed.d b; omega) rel _ ell x h⟩
  intro t f y zero
  obtain ⟨idx,res,estimate⟩ := retained_arch_energy hn big stage (fun a=>a%ell=Fixed.rootBase n%ell) quiet
  have off : Fixed.rootBase n%ell ∉ S := fun h =>
    ((wanted_spec (target_gt_degree target) (Fixed.rootBase n)).2.2 _ (List.mem_toFinset.mp h)).2 rfl
  have onGrid (c) : t+∑ j, log |(rel.marks.get (idx c):ℝ)/s.A-
      x (gridPlace j).1 (gridPlace j).2| * y j = 0 := by
    have hz := zero (idx c)
    change (t+∑ j, log |(rel.marks.get (idx c):ℝ)/s.A-x (gridPlace j).1 (gridPlace j).2| * y j)+
      targetScore S f (rel.marks.get (idx c)%ell) = 0 at hz
    rwa [res c,targetScore,dif_neg off,add_zero] at hz
  have lower := estimate x (fun side j=>(roots side j).2.1) t y
  change t^2+∑ j, (y j)^2 ≤ 12*∑ c, (t+∑ j, log |(rel.marks.get (idx c):ℝ)/s.A-
      x (gridPlace j).1 (gridPlace j).2| * y j)^2 at lower
  simp only [onGrid,zero_pow (by decide : 2≠0),sum_const_zero,mul_zero] at lower
  have norms := sum_nonneg (s:=univ) (fun j _=>sq_nonneg (y j))
  have t0 : t=0 := by nlinarith only [lower,norms,sq_nonneg t]
  have sy : ∑ j,(y j)^2=0 := le_antisymm (by simpa [t0] using lower) norms
  have y0 : y=0 := dotProduct_self_eq_zero.mp (by simpa only [dotProduct,←sq] using sy)
  refine ⟨t0,?_,y0⟩
  funext r
  obtain ⟨a,_,ret,mod⟩ := hit r.val (List.mem_toFinset.mp r.prop)
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ret
  have zi := zero i
  simp only [y0,t0,Pi.zero_apply,mul_zero,sum_const_zero,add_zero,zero_add] at zi
  change targetScore S f (rel.marks.get i%ell)=0 at zi
  rw [hi,mod,targetScore,dif_pos r.prop] at zi
  exact zi

/-- For each sufficiently large surviving input and each target, one positive
search tuple has independent intercept, target indicators and all true log rows. -/
theorem exists_protected_rank (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∃ (u v : ℤ×ℤ) (rel : Marking.Relations), inCoefficientBox n u ∧ inCoefficientBox n v ∧
      let s := TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat)
      let S := (wanted s.degree ell (Fixed.rootBase n)).toFinset
      Marking.stageOne s=some rel ∧ (∀ r, Marking.Row.mk false ell r ∈ rel.rows ↔ r∈S) ∧
      6997*Fixed.h (n.log2+1)+2 ≤ (ordinaryMarkMatrix rel ((constructorCellMarks n ell none).filter
        (fun a=>a%ell=Fixed.rootBase n%ell ∧ a∈rel.marks))).rank ∧
      ∃ x : Bool → Fin s.degree → ℝ,
        (∀ side j, x side j ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ) ∧
          RootLogs.normalized s.A (s.coeffs side) (x side j)=0) ∧
        IndependentWithTargets rel S ell (fun j i=>log |(rel.marks.get i:ℝ)/s.A-
          x (gridPlace j).1 (gridPlace j).2|) ∧
        IndependentWithTargets rel S ell (bracketMarkMatrix s rel x) := by
  classical
  obtain ⟨n₁,supply⟩ := protected_target_cells_rank line
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows 130000
  refine ⟨max n₁ (max 2 (2^b₀)),?_⟩
  intro n large ell target composite sieved
  obtain ⟨nlarge,other⟩ := max_le_iff.mp large
  obtain ⟨hn,pow⟩ := max_le_iff.mp other
  let b := n.log2+1
  have bit := (Nat.le_log2 (show n≠0 by omega)).mpr pow
  have big : 130000 ≤ Fixed.d b := grow _ (by dsimp [b]; omega)
  obtain ⟨u,v,rel,bu,bv,stage,quiet,hit,_,_,ordinary⟩ := supply n nlarge ell target composite sieved
  refine ⟨u,v,rel,bu,bv,stage,?_,ordinary,?_⟩
  · intro r
    simpa using computed_target_row_iff (show 3≤Fixed.d b by omega) target stage r
  exact protected_rank_of_cell_hits hn big target u v rel bu bv stage quiet hit

end Cogentic.Construction

#print axioms Cogentic.Construction.exists_protected_rank
