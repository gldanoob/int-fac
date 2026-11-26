import Cogentic.GramPeeling
import Cogentic.Marking

namespace Cogentic.Construction
open Finset Real
noncomputable section
open scoped Classical

/-- Remove all columns meeting peeled rows. An upper bound for the original
smooth pair entries suffices to limit each surviving row's lost diagonal.
Protected rows stay outside the discarded set. -/
theorem peeled_row_hit_loss {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι→Marking.Row) (X : Finset ℕ) (w : ℕ→ℝ) (wn : ∀ a∈X,0≤w a)
    (initial targetRows : Finset ι) (mass : ι→ℝ) (E : ι→ι→ℝ) (cap δ C : ℝ)
    (cp : 0<cap) (dp : 0<δ) (cn : 0≤C) (mp : ∀ i,0 < mass i)
    (clean : Disjoint initial targetRows) (init : ∑ i∈initial,mass i≤cap/2)
    (small : 8*(∑ i,∑ j,(E i j)^2)≤δ^2)
    (targets : ∀ i∈targetRows,4*cap*(∑ j,(E i j)^2)<δ^2*mass i)
    (overlaps : ∀ i∉initial,∀ j, i≠j →
      (∑ a∈X with a%(row i).q=(row i).r ∧ a%(row j).q=(row j).r,w a) ≤
        C*mass i*mass j+sqrt (mass i)*(sqrt (mass j)*|E i j|)) :
    ∃ D : Finset ι, initial⊆D ∧ Disjoint D targetRows ∧ (∑ j∈D,mass j)≤cap ∧ ∀ i∉D,
      (∑ a∈X with a%(row i).q=(row i).r ∧ ∃ j∈D,a%(row j).q=(row j).r, w a) ≤
        (C*cap+δ/2)*mass i := by
  classical
  obtain ⟨D,start,safe,limit,stable⟩ := stable_gram_deletion initial targetRows mass E cap δ cp dp mp clean init small targets
  refine ⟨D,start,safe,limit,?_⟩
  intro i keep
  let hit := fun (i : ι) (a : ℕ)=> a%(row i).q=(row i).r
  have unionBound : (∑ a∈X with hit i a ∧ ∃ j∈D, hit j a,w a) ≤
      ∑ j∈D,∑ a∈X with hit i a ∧ hit j a,w a := by
    simp only [sum_filter];rw [sum_comm]
    apply sum_le_sum
    intro a ha
    have nonn (j : ι) : 0≤(if hit i a ∧ hit j a then w a else 0) := by split <;> first | exact wn a ha | rfl
    split
    · next yes =>
      obtain ⟨ia,j,jm,hj⟩ := yes
      exact (if_pos ⟨ia,hj⟩).symm.le.trans (single_le_sum (fun j _=>nonn j) jm)
    · exact sum_nonneg (fun j _=>nonn j)
  have both := sum_le_sum (s:=D) (fun j jm=>overlaps i (fun inside=>keep (start inside)) j (by rintro rfl;exact keep jm))
  rw [sum_add_distrib,←mul_sum,←mul_sum] at both
  apply unionBound.trans (both.trans ?_)
  have ab := mul_le_mul_of_nonneg_left limit (mul_nonneg cn (mp i).le)
  have inter := mul_le_mul_of_nonneg_left (stable i keep) (sqrt_nonneg (mass i))
  have sq := Real.sq_sqrt (mp i).le
  have inter' : sqrt (mass i)*(∑ j∈D,sqrt (mass j)*|E i j|)≤δ/2*mass i := by
    calc _ = (sqrt (mass i)*(2*∑ j∈D,sqrt (mass j)*|E i j|))/2 := by ring
         _ ≤ (sqrt (mass i)*(δ*sqrt (mass i)))/2 := div_le_div_of_nonneg_right inter (by norm_num)
         _ = δ/2*(sqrt (mass i))^2 := by ring
         _ = _ := by rw [sq]
  exact (add_le_add ab inter').trans_eq (by ring)


/-- On the same smooth marks, remove the rows with inaccurate diagonals and
those whose interactions with deleted rows are too large. The weighted
diagonal error controls the total column mass lost even on the deleted rows. -/
theorem ordinary_miss_peeling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : ι→Marking.Row) (X : Finset ℕ) (w : ℕ→ℝ) (wn : ∀ a∈X,0≤w a)
    (initial : Finset ι) (μ d : ι→ℝ) (E : ι→ι→ℝ) (cap τ δ C : ℝ)
    (cp : 0<cap) (tp : 0<τ) (dp : 0<δ) (cn : 0≤C) (mp : ∀ i,0<μ i)
    (init : (∑ i∈initial,μ i)≤cap/4)
    (diag : (∑ i,μ i*(d i)^2)≤τ^2*(cap/4))
    (off : 8*(∑ i,∑ j,(E i j)^2)≤δ^2)
    (single : ∀ i,(∑ a∈X with a%(row i).q=(row i).r,w a) ≤ μ i*(C+|d i|))
    (pair : ∀ i∉initial,∀ j,i≠j →
      (∑ a∈X with a%(row i).q=(row i).r ∧ a%(row j).q=(row j).r,w a) ≤
        C*μ i*μ j+sqrt (μ i)*(sqrt (μ j)*|E i j|)) :
    ∃ D : Finset ι, initial⊆D ∧ (∑ i∈D,μ i)≤cap ∧
      (∑ a∈X with ∃ i∈D,a%(row i).q=(row i).r,w a) ≤ (C+τ)*cap ∧
      ∀ i∉D, |d i|<τ ∧
        (∑ a∈X with a%(row i).q=(row i).r ∧ ∃ j∈D,a%(row j).q=(row j).r,w a) ≤
          (C*cap+δ/2)*μ i := by
  classical
  let B := univ.filter (fun i=>τ≤|d i|)
  have part (S : Finset ι) : (∑ i∈S, μ i*(d i)^2)≤τ^2*(cap/4) :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun i _ _=>mul_nonneg (mp i).le (sq_nonneg _))).trans diag
  have bad : (∑ i∈B,μ i)≤cap/4 := by
    apply le_of_mul_le_mul_right (a:=τ^2) _ (sq_pos_of_pos tp)
    rw [sum_mul,mul_comm (cap/4)]
    apply (sum_le_sum (s:=B) (fun i hi=>mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ tp.le (mem_filter.mp hi).2 2).trans_eq (sq_abs _)) (mp i).le)).trans
    exact part B
  have initialBound : (∑ i∈initial∪B, μ i)≤cap/2 := by
    have eq := sum_union_inter (s₁:=initial) (s₂:=B) (f:=μ)
    have nn := sum_nonneg (s:=initial∩B) (fun i _=>(mp i).le)
    linarith
  obtain ⟨D,sub,_,size,loss⟩ := peeled_row_hit_loss row X w wn (initial∪B) ∅ μ E cap δ C cp dp cn mp
    (by simp) initialBound off (by simp) (fun i hi=>pair i (fun h=>hi (mem_union_left _ h)))
  have cs := sum_mul_sq_le_sq_mul_sq D (fun i=>sqrt (μ i)) (fun i=>sqrt (μ i)*|d i|)
  simp only [←mul_assoc,←sq,Real.sq_sqrt (mp _).le,mul_pow,sq_abs] at cs
  have l1 : (∑ i∈D,μ i*|d i|)≤τ*cap := by
    have bound := mul_le_mul size (part D)
      (sum_nonneg (fun i _=>mul_nonneg (mp i).le (sq_nonneg _))) cp.le
    apply le_of_sq_le_sq _ (mul_nonneg tp.le cp.le)
    exact (cs.trans bound).trans (by nlinarith only [sq_nonneg (τ*cap)])
  refine ⟨D,Subset.trans subset_union_left sub,size,?_,?_⟩
  · calc
      _ ≤ ∑ i∈D, ∑ a∈X with a%(row i).q=(row i).r,w a := by
        simp only [sum_filter]
        rw [sum_comm]
        apply sum_le_sum
        intro a ha
        have nn (i : ι) : 0≤(if a%(row i).q=(row i).r then w a else 0) := by split <;> first | exact wn a ha | rfl
        split
        · next h =>
          obtain ⟨i,hi,hit⟩ := h
          exact (if_pos hit).symm.le.trans (single_le_sum (fun i _=>nn i) hi)
        · exact sum_nonneg (fun i _=>nn i)
      _ ≤ ∑ i∈D,μ i*(C+|d i|) := sum_le_sum (fun i _=>single i)
      _ ≤ _ := by
        simp only [mul_add,sum_add_distrib,←sum_mul]
        linarith only [mul_le_mul_of_nonneg_right size cn,l1]
  · intro i hi
    exact ⟨lt_of_not_ge (fun h=>hi (sub (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩)))),loss i hi⟩

end
end Cogentic.Construction

#print axioms Cogentic.Construction.peeled_row_hit_loss
#print axioms Cogentic.Construction.ordinary_miss_peeling
