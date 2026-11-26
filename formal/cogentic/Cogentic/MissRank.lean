import Cogentic.MissDrawParameters
import Cogentic.MissDrawPeeling
import Cogentic.MissGramDraw
import Cogentic.MissEntryBounds
import Cogentic.MissGridExtraction
import Cogentic.MissRankSupport

namespace Cogentic.Construction
open Finset Real Marking Window
noncomputable section
open scoped Classical

/-- One coefficient draw supplies the ordinary Gram on retained target misses
and a surviving mark for each target row of the executable matrix. -/
theorem eventual_box_has_rank (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    Concrete.BoxHasRank n ell := by
  obtain ⟨b₁,saddles⟩ := miss_draw_saddles line
  obtain ⟨n₂,draw⟩ := simultaneous_miss_gram_draw line
  obtain ⟨n₃,prior⟩ := pooled_mesh_prior line
  obtain ⟨n₅,b₅,entries⟩ := miss_entry_bounds line
  obtain ⟨b₆,degree⟩ := Fixed.degree_grows 130000
  obtain ⟨b₇,extract⟩ := boxHasRank_of_miss_entries
  obtain ⟨b₈,precision⟩ := miss_rank_precision
  obtain ⟨n₉,peel⟩ := miss_draw_peeling line
  let limit := max (max (max (max n₂ n₃) n₅) n₉) (max b₁ (max b₅ (max b₆ (max b₇ b₈))))
  refine ⟨limit,?_⟩
  intro n ell b big hn comp target sieve
  have bounds := show limit≤b from big
  simp only [limit,max_le_iff] at bounds
  obtain ⟨⟨⟨⟨l₂,l₃⟩,l₅⟩,l₉⟩,l₁,l₅',l₆,l₇,l₈⟩ := bounds
  have bn : b≤n :=
    (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=n.log2))).trans (Nat.log2_self_le (by omega))
  let β := branchMeshSaddle n ell (firstCellMark b none) false false
  let α (j : GridPosition b) := branchMeshSaddle n ell (firstCellMark b (j.1.map gridPlace)+j.2.val) false
  let u := saddleMean (primeBand b) β / log (Fixed.B b)
  obtain ⟨βband,βrange,up,ub,sd,αspec⟩ := saddles l₁ hn target
  have βband' : β∈Set.Icc (0:ℝ) 1 := ⟨(by norm_num : (0:ℝ)≤199/200).trans βband.1,βband.2⟩
  let mass (i : Row) := (i.q:ℝ)^(-β)
  let scale (i : Row) := (sqrt (mass i))⁻¹
  obtain ⟨_,_,mixpos,mixsum,_⟩ := prior n (l₃.trans bn) ell target comp sieve
  obtain ⟨x,y,good,_,rejected,massBase,pairCost,crossCost,logCost,rel,stage,picks⟩ :=
    draw n (l₂.trans bn) ell target comp sieve β u βband' up ub sd (meshMix n ell)
      mixpos mixsum mass scale (saddle_row_reciprocal β)
  have hd : 3≤Fixed.d b := (by decide : 3≤130000).trans (degree b l₆)
  let S := smoothMesh n ell x y
  let X := S.filter (fun a=>hitsTarget n ell a false=false)
  let weight := fun a=>meshWeight n ell a/(∑ k∈S,meshWeight n ell k)
  let A₀ := rel.rows.toFinset.filter (fun r=>r.q≠ell)
  have sub₀ : A₀⊆rel.rows.toFinset := filter_subset _ _
  have ordinary₀ : ∀ i∈A₀,i.q≠ell := fun i hi=>(mem_filter.mp hi).2
  have massBound := surviving_ordinary_mass hn hd comp target sieve x y good.1 good.2.1 β u ub massBase
  obtain ⟨band₀,_⟩ := massBound A₀ (clean_subset_listed stage sub₀) ordinary₀
  have allEntries (A : Finset Row) (sub : A⊆rel.rows.toFinset) (away : ∀ i∈A,i.q≠ell) :=
    entries (l₅.trans bn) l₅' hn hd target comp sieve x y good.1 good.2.1 good stage A sub away β pairCost crossCost logCost
  obtain ⟨diag₀,_,off₀⟩ := allEntries A₀ sub₀ ordinary₀
  let e := exp (-(Fixed.z b:ℝ)^2)
  let δ := exp (-(1/4)*(Fixed.z b:ℝ)^2)
  obtain ⟨precOff,precDiag,precProt,precFit⟩ := precision b l₈
  -- Peeling uses the same errors and smooth weights as the Gram transfer.
  obtain ⟨D,cap,diagOrd,wn,weightBound,lost⟩ := peel n (l₉.trans bn) ell target comp sieve x y good
    stage A₀ sub₀ (fun i hi=>⟨band₀ i hi,ordinary₀ i hi⟩) α β βband'.1
    (fun j k=>(αspec j k).1.1) βrange (fun j k=>(αspec j k).2) rejected diag₀ off₀
  let A := A₀ \ D.image Subtype.val
  let Y := X.filter (fun a=>a∈rel.marks ∧ ∀ i∈D,a%i.val.q≠i.val.r)
  have subA₀ : A⊆A₀ := sdiff_subset
  have listed : A⊆rel.rows.toFinset := subA₀.trans sub₀
  have ordinary : ∀ i∈A,i.q≠ell := fun i hi=>ordinary₀ i (subA₀ hi)
  obtain ⟨band,total⟩ := massBound A (clean_subset_listed stage listed) ordinary
  have sub : Y⊆X := filter_subset _ _
  have retained : Y⊆rel.marks.toFinset := fun a ha=>List.mem_toFinset.mpr (mem_filter.mp ha).2.1
  have miss (r : Row) (hr : r∈rel.rows) (rq : r.q=ell) (a : ℕ) (ha : a∈Y) : a%ell≠r.r := by
    intro hit
    have no := (mem_filter.mp (sub ha)).2
    have yes := (target_part_residues hd target a).1.mpr (hit.symm ▸ listed_target_mem_wanted hd target x y stage r hr rq)
    rw [no] at yes
    contradiction
  have avoids (a : ℕ) (h : ∀ i∈D,a%i.val.q≠i.val.r) (r : Row) (hr : r∈rel.rows)
      (rq : r.q≠ell) (no : r∉A) : a%r.q≠r.r := by
    have mem : r∈A₀ := mem_filter.mpr ⟨List.mem_toFinset.mpr hr,rq⟩
    have removed : r∈D.image Subtype.val := by
      by_contra nr
      exact no (mem_sdiff.mpr ⟨mem,nr⟩)
    obtain ⟨i,hi,rfl⟩ := mem_image.mp removed
    exact h i hi
  have picked (r : Row) (hr : r∈rel.rows) (rq : r.q=ell) :
      ∃ a∈rel.marks,a%ell=r.r ∧ ∀ i∈rel.rows,i.q≠ell → i∉A → a%i.q≠i.r := by
    obtain ⟨a,ha,hit,off⟩ := peeled_target_witnesses hn hd comp target sieve x y good.1 good.2.1 β e
      stage D cap picks r hr rq
    exact ⟨a,ha,hit,avoids a off⟩
  obtain ⟨_,diagProt,off⟩ := allEntries A listed ordinary
  refine extract l₇ hn target x y good.1 good.2.1 stage A X Y listed
    (fun i hi=>⟨band i hi,ordinary i hi⟩) sub retained miss
    (fun a ha=>avoids a (mem_filter.mp ha).2.2) picked α β
    ((by norm_num : (1/2:ℝ)≤199/200).trans βband.1) (fun j k=>(αspec j k).1.1)
    βrange (fun j k=>(αspec j k).2) total weight δ (fun a _=>wn a) weightBound
    (exp_pos _).le precFit ?_ (off.trans precOff) lost
  -- The protected diagonal is a single term of its full block cost.
  intro i
  cases i with
  | inl j =>
    exact (protected_diagonal_from_cost _ (exp_pos _).le diagProt j).trans precProt
  | inr j =>
    let i : A₀ := ⟨j.val,subA₀ j.prop⟩
    have hi : i∉D := fun h=>(mem_sdiff.mp j.prop).2 (mem_image_of_mem Subtype.val h)
    simpa only [missGridGram,missMomentEntry,ordinaryRawEntry,if_pos rfl,retainedMissColumn] using
      (diagOrd i hi).le.trans precDiag

end
end Cogentic.Construction

#print axioms Cogentic.Construction.eventual_box_has_rank
