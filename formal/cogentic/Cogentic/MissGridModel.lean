import Cogentic.RawGridModel
import Cogentic.RawGramTransfer

namespace Cogentic.Construction
open Finset Real Window
noncomputable section

/-- The miss-only ordinary/log/intercept model uses the actual saddle at every raw
mesh position. The only row constraints are a total admitted mass bound and the
two field norm equations. Any subset of admitted rows can be used. -/
theorem miss_grid_model_coercivity :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → ell∈dyadicTargets (Fixed.beta b) → ∀ a c e f : ℕ,
    let input := TryPair.fixedInput n ell (construct n ell a c e f)
    ∀ A : Finset Marking.Row, A⊆input.rows.toFinset → (∀ i∈A,i.q∈primeBand b) →
    ∀ (α : GridPosition b→Bool→ℝ) (β : ℝ), 1/2≤β → (∀ j side, 199/200≤α j side) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    (∀ j side, InMarkSaddleRange n (saddleMean (primeBand b) (α j side))) →
    let d := (Fixed.d b:ℝ); let miss := 1-d/(ell:ℝ)
    let p := fun i : A=>i.val.q; let side := fun i : A=>i.val.second
    let μ := fun i : A=>(p i:ℝ)^(-β); let w := fun i=>sqrt (μ i)
    let I := fun j k (q : ℕ)=>fullBandInsertion b q (α j k)/((q:ℝ)*(q:ℝ)^(-β))
    let m := fun j i=>w i*I j (side i) (p i)
    let R := fun j=>ordinaryRawEntry p side w (I j)
    (∑ i,μ i)≤15000*d → ∀ v : (Option (Fin (2*Fixed.d b))) ⊕ ↥A → ℝ,
    (∀ k : Bool, (∑ i : A,if side i=k then w i*log (p i)*v (.inr i) else 0)=0) →
    (∑ i,(v i)^2) ≤ 2*(768*(10000*d)*(2*d+1))*(∑ i,∑ j,v i*missGridGram miss m R i j*v j) := by
  classical
  obtain ⟨b₁,model⟩ := raw_grid_model_margin
  obtain ⟨b₂,grow⟩ := Fixed.degree_grows 130000
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b big target a c e f input A sub band α β ba aa mb ma d miss p side μ w I m R mass v perp
  obtain ⟨one,two⟩ := max_le_iff.mp big
  have hd := grow b two
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos n.log2)
  have dh : Fixed.d b≤Fixed.h b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have expbd : 2*Fixed.d b≤Fixed.beta b-1 := by change 2*Fixed.d b≤1000*Fixed.h b-1;omega
  have lower : 2*Fixed.d b≤ ell := (Nat.lt_two_pow_self.le.trans ((Nat.pow_le_pow_right (by decide) expbd).trans (mem_dyadicTargets.mp target).2.1.le))
  have ellp : (0:ℝ)<ell := by exact_mod_cast (mem_dyadicTargets.mp target).1.pos
  have hmiss : 1/2≤ miss := by
    have bd : 2*d≤ ell := by dsimp only [d]; exact_mod_cast lower
    have half : d/(ell:ℝ)≤1/2 := (div_le_iff₀ ellp).mpr (by linarith only [bd])
    dsimp only [miss];linarith only [half]
  apply miss_grid_gram_energy hd miss hmiss m R v
  intro z
  let g := ∑ i,gridLogColumn z i*v (.inl i)
  let s := ∑ i,m z i*v (.inr i)
  let V := (∑ i,∑ j,v (.inr i)*R z i j*v (.inr j))-s^2
  let F := ∑ i : A,(v (.inr i))^2
  let x := (sqrt (ell:ℝ))⁻¹
  let τ := d*x^2
  have h := model one target a c e f A sub band (fun _=>α z) β ba (fun _=>aa z) mb (fun _=>ma z) mass g
    (fun i=>v (.inr i)) (fun _=>0) (fun k=>by simpa using perp k)
  change ((1-τ)*s+τ*s+x*(∑ _ : Fin (Fixed.d b),(0:ℝ)))^2≤120000*d*(F+∑ _ : Fin (Fixed.d b),(0:ℝ)^2) ∧
    (g+((1-τ)*s+τ*s+x*(∑ _ : Fin (Fixed.d b),(0:ℝ))))^2+13/16*(F+∑ _ : Fin (Fixed.d b),(0:ℝ)^2)≤
      (1-τ)*((g+s)^2+V)+τ*V+∑ _ : Fin (Fixed.d b),(x*(g+s)+(0:ℝ))^2 at h
  simp only [sum_const_zero,mul_zero,add_zero,sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  change s^2≤120000*d*F ∧ (g+s)^2+13/16*F≤(g+s)^2+V
  dsimp only [τ] at h
  change _ ∧ _≤_+(d:ℝ)*(x*(g+s))^2 at h
  constructor <;> nlinarith only [h.1,h.2]

end
end Cogentic.Construction
#print axioms Cogentic.Construction.miss_grid_model_coercivity
