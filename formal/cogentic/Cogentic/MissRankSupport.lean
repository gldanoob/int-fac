import Cogentic.OrdinaryMass
import Cogentic.RankErrorBudget
import Cogentic.RetainedBoxRank

namespace Cogentic.Construction
open Finset Real Marking
noncomputable section
open scoped Classical

theorem clean_subset_listed {s : Input} {rel : Relations} (stage : stageOne s=some rel)
    {A : Finset Row} (sub : A⊆rel.rows.toFinset) : A⊆s.rows.toFinset :=
  fun _ hr => List.mem_toFinset.mpr (mem_clean.mp
    ((rows_and_guards stage).2.2.2.1 ▸ List.mem_toFinset.mp (sub hr))).1

theorem listed_target_mem_wanted {n ell : ℕ} (hd : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (x y : ℤ×ℤ) :
    let s := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
    ∀ {rel}, stageOne s=some rel → ∀ r∈rel.rows,r.q=ell →
    r.r∈wanted (Fixed.d (n.log2+1)) ell (Fixed.rootBase n) := by
  intro s rel stage r listed eq
  have inp : r∈s.rows := List.mem_toFinset.mp (clean_subset_listed stage
    (subset_refl rel.rows.toFinset) (List.mem_toFinset.mpr listed))
  have side := (target_rows_clean hd target _ _ _ _ r inp eq).1
  have hr : Row.mk false ell r.r=r := by cases r; cases eq; cases side; rfl
  have iff := computed_target_row_iff hd target stage r.r
  exact iff.mp (hr.symm ▸ listed)

theorem peeled_target_witnesses {n ell : ℕ} (hn : 2≤n) (hd : 3≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieve : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (x y : ℤ×ℤ) (bx : inCoefficientBox n x) (by' : inCoefficientBox n y) (β cap : ℝ) :
    let s := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
    ∀ {rel}, stageOne s=some rel →
    let A₀ := rel.rows.toFinset.filter (fun r=>r.q≠ell)
    ∀ D : Finset A₀, (∑ i∈D,(i.val.q:ℝ)^(-β))≤cap →
    (∀ E⊆admittedOrdinaryRows n ell x y, (∑ i∈E,(bandRowPrime i:ℝ)^(-β))≤cap →
      ∀ r∈wanted (Fixed.d (n.log2+1)) ell (Fixed.rootBase n), ∃ a∈rel.marks, a ≡ r [MOD ell] ∧
        ∀ i∈E, ¬a ≡ i.2.2.val [MOD bandRowPrime i]) →
    ∀ r∈rel.rows,r.q=ell → ∃ a∈rel.marks,a%ell=r.r ∧ ∀ i∈D,a%i.val.q≠i.val.r := by
  intro s rel stage A₀ D capD picks r rm rq
  let row (i : BandRow (n.log2+1)) := Row.mk i.1 (bandRowPrime i) i.2.2.val
  let S := admittedOrdinaryRows n ell x y
  have listed : A₀⊆rel.rows.toFinset := filter_subset _ _
  have imageEq : S.image row=s.rows.toFinset.filter (fun r=>r.q≠ell) :=
    admitted_ordinary_rows_eq hn hd comp target sieve x y bx by'
  have exists_row (i : A₀) : ∃ j∈S,row j=i.val := by
    apply mem_image.mp
    rw [imageEq]
    exact mem_filter.mpr ⟨clean_subset_listed stage listed i.prop,(mem_filter.mp i.prop).2⟩
  let f (i : A₀) := Classical.choose (exists_row i)
  have hf (i : A₀) := Classical.choose_spec (exists_row i)
  let E := D.image f
  have cover : E⊆S := fun j hj=>by obtain ⟨i,_,rfl⟩ := mem_image.mp hj; exact (hf i).1
  have bound : (∑ i∈E,(bandRowPrime i:ℝ)^(-β))≤cap := by
    apply (sum_image_le_of_nonneg (s:=D) (g:=f) (f:=fun i=>(bandRowPrime i:ℝ)^(-β))
      (fun i _=>rpow_nonneg (Nat.cast_nonneg _) _)).trans
    have labels (i : A₀) : bandRowPrime (f i)=i.val.q := congrArg Row.q (hf i).2
    simp_rw [labels]
    exact capD
  have wanted := listed_target_mem_wanted hd target x y stage r rm rq
  obtain ⟨a,am,eq,off⟩ := picks E cover bound r.r wanted
  have canon := ((wanted_spec (target_gt_degree target) (Fixed.rootBase n)).2.2 r.r wanted).1
  refine ⟨a,am,by simpa only [Nat.ModEq,Nat.mod_eq_of_lt canon] using eq,?_⟩
  intro i hi hit
  have small : (row (f i)).r < (row (f i)).q := (f i).2.2.isLt
  rw [(hf i).2] at small
  have neq := off (f i) (mem_image_of_mem f hi)
  apply neq
  change a ≡ (row (f i)).r [MOD (row (f i)).q]
  rw [(hf i).2]
  exact hit.trans (Nat.mod_eq_of_lt small).symm

theorem protected_diagonal_from_cost {I : Type*} [Fintype I] (E : I→I→ℝ) {e : ℝ}
    (en : 0≤e) (h : (∑ i,∑ j,(E i j)^2)≤256*e^6) (i : I) : |E i i|≤32*e^3 := by
  have nn (j : I) : 0≤∑ k,(E j k)^2 := sum_nonneg fun _ _=>sq_nonneg _
  have one := (single_le_sum (s:=univ) (f:=fun j=>(E i j)^2)
    (fun _ _=>sq_nonneg _) (mem_univ i)).trans
      ((single_le_sum (s:=univ) (f:=fun j=>∑ k,(E j k)^2) (fun j _=>nn j) (mem_univ i)).trans h)
  have stronger : (E i i)^2≤(32*e^3)^2 := one.trans (by nlinarith only [sq_nonneg (e^3)])
  exact le_of_sq_le_sq (by simpa only [sq_abs] using stronger) (by positivity)

theorem miss_rank_precision :
    ∃ b₀ : ℕ, ∀ b≥b₀,
      let e := exp (-(Fixed.z b:ℝ)^2)
      let δ := exp (-(1/4)*(Fixed.z b:ℝ)^2)
      let d := (Fixed.d b:ℝ)
      δ^2 ≥ 1024*e^6 ∧ δ ≥ e^2 ∧ δ ≥ 32*e^3 ∧
      4*(2*(768*(10000*d)*(2*d+1)))*δ≤1 := by
  obtain ⟨b₁,budget⟩ := rank_polynomial_savings 184320000 2 (show (0:ℝ)<1/4 by norm_num)
  obtain ⟨b₂,prec⟩ := rank_polynomial_savings 1024 0 (show (1/2:ℝ)<6 by norm_num)
  obtain ⟨b₃,prot⟩ := rank_polynomial_savings 32 0 (show (1/4:ℝ)<3 by norm_num)
  refine ⟨max 1 (max b₁ (max b₂ b₃)),?_⟩
  intro b big e δ d
  obtain ⟨bp,more⟩ := max_le_iff.mp big
  obtain ⟨h₁,h₂₃⟩ := max_le_iff.mp more
  obtain ⟨h₂,h₃⟩ := max_le_iff.mp h₂₃
  have ex (k : ℕ) : e^k=exp (-(k:ℝ)*(Fixed.z b:ℝ)^2) := by
    dsimp only [e]
    rw [←exp_nat_mul]; congr 1; ring
  have δsq : δ^2=exp (-(1/2)*(Fixed.z b:ℝ)^2) := by
    dsimp only [δ]
    rw [←exp_nat_mul]; congr 1; push_cast; ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [ex,δsq]; simpa using prec b h₂
  · rw [ex]
    dsimp only [δ]
    exact exp_le_exp.mpr (by push_cast; nlinarith only [sq_nonneg (Fixed.z b:ℝ)])
  · rw [ex]
    dsimp only [δ]
    simpa using prot b h₃
  · have dl : d≤(b:ℝ) := by dsimp only [d];exact_mod_cast Fixed.degree_le_bits b
    have dn : 0≤d := Nat.cast_nonneg _
    have bl : (1:ℝ)≤b := by exact_mod_cast bp
    have base : 4*(2*(768*(10000*d)*(2*d+1))) ≤ 184320000*(b:ℝ)^2 := by
      have h := mul_le_mul dl (show 2*d+1≤3*(b:ℝ) by linarith) (by positivity) (by positivity)
      nlinarith only [h]
    exact (mul_le_mul_of_nonneg_right base (exp_pos _).le).trans (by simpa [δ] using budget b h₁)

end
end Cogentic.Construction
