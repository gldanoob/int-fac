import Cogentic.BranchInsertionProfiles
import Cogentic.RawGramTransfer

namespace Cogentic.Construction
open Finset Real Window
noncomputable section

/-- Use the target-miss saddle at the first reference-cell point to normalize
every ordinary row. The field-specific centers still vary across the mesh. -/
theorem miss_draw_saddles (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    let β := branchMeshSaddle n ell (firstCellMark b none) false false
    let α := fun (j : GridPosition b) => branchMeshSaddle n ell
      (firstCellMark b (j.1.map gridPlace)+j.2.val) false
    let H := log (Fixed.B b)
    let u := saddleMean (primeBand b) β / H
    β∈Set.Icc (199/200:ℝ) 1 ∧ InMarkSaddleRange n (saddleMean (primeBand b) β) ∧
      0<u ∧ u≤110*(Fixed.d b:ℝ) ∧ saddleMean (primeBand b) β=H*u ∧
      ∀ j side, α j side∈Set.Icc (199/200:ℝ) 1 ∧
        InMarkSaddleRange n (saddleMean (primeBand b) (α j side)) := by
  obtain ⟨b₀,mesh⟩ := canonical_mesh_saddle_range line
  refine ⟨b₀,?_⟩
  intro n ell b big hn target β α H u
  have mp : 0<cellMarkCount b := Nat.pow_pos (by decide : 0<2)
  have anchor : β∈Set.Icc (199/200:ℝ) 1 ∧ InMarkSaddleRange n (saddleMean (primeBand b) β) := by
    simpa only [β,Nat.add_zero] using mesh big hn target none false false 0 mp
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos n.log2)
  have hp : 0<H := log_pos (by exact_mod_cast (Nat.one_lt_pow (Nat.mul_ne_zero (by decide)
    (Nat.mul_ne_zero dp.ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b))
  have dx : (0:ℝ)<Fixed.d b := Nat.cast_pos.mpr dp
  have positive := (mul_pos hp (by positivity : (0:ℝ)<90*Fixed.d b)).trans_le anchor.2.1
  refine ⟨anchor.1,anchor.2,div_pos positive hp,(div_le_iff₀ hp).mpr ?_,?_,?_⟩
  · exact anchor.2.2.1.trans_eq (mul_comm ..)
  · dsimp only [u]; field_simp
  · intro j side
    exact mesh big hn target (j.1.map gridPlace) false side j.2.val j.2.isLt

theorem saddle_row_reciprocal (β : ℝ) (i : Marking.Row) (prime : i.q.Prime) :
    (i.q:ℝ)^(-β) * (Real.sqrt ((i.q:ℝ)^(-β)))⁻¹ ^ 2 = 1 := by
  have pos := Real.rpow_pos_of_pos (Nat.cast_pos.mpr prime.pos : (0 : ℝ) < (i.q : ℝ)) (-β)
  rw [inv_pow, Real.sq_sqrt pos.le, mul_inv_cancel₀ pos.ne']

end
end Cogentic.Construction

#print axioms Cogentic.Construction.miss_draw_saddles
