import Cogentic.MissGridModel
import Cogentic.RetainedBoxRank

namespace Cogentic.Construction
open Finset Real Marking Window
noncomputable section

/-- Transfer the target-miss reference to one boxed draw. `X` consists of
smooth target misses and `Y` of retained misses avoiding the deleted rows.
The weight is normalized by the smooth mass over all target branches. -/
theorem boxHasRank_of_miss_entries :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ (u y : ℤ×ℤ), inCoefficientBox n u → inCoefficientBox n y →
    let input := TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat y.1.toNat y.2.toNat)
    ∀ {rel}, stageOne input=some rel → ∀ (A : Finset Row) (X Y : Finset ℕ), A⊆rel.rows.toFinset →
    (∀ i∈A,i.q∈primeBand b ∧ i.q≠ell) → Y⊆X → Y⊆rel.marks.toFinset →
    (∀ r∈rel.rows,r.q=ell → ∀ a∈Y,a%ell≠r.r) →
    let avoids := fun a=>∀ i∈rel.rows,i.q≠ell → i∉A → a%i.q≠i.r
    (∀ a∈Y,avoids a) → (∀ r∈rel.rows,r.q=ell → ∃ a∈rel.marks,a%ell=r.r ∧ avoids a) →
    ∀ (α : GridPosition b→Bool→ℝ) (β : ℝ), 1/2≤β → (∀ j k,199/200≤α j k) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) → (∀ j k,InMarkSaddleRange n (saddleMean (primeBand b) (α j k))) →
    let d := (Fixed.d b:ℝ); let τ := 1-d/ell
    let p := fun i : A=>i.val.q; let side := fun i : A=>i.val.second
    let μ := fun i : A=>(p i:ℝ)^(-β); let w := fun i=>sqrt (μ i); let scale := fun i=>(w i)⁻¹
    let I := fun j k (q : ℕ)=>fullBandInsertion b q (α j k)/((q:ℝ)*(q:ℝ)^(-β))
    let m := fun j i=>w i*I j (side i) (p i); let R := fun j=>ordinaryRawEntry p side w (I j)
    let Z := retainedMissColumn input A scale (fun k i=>(center input.degree k i.val:ℝ))
    (∑ i,μ i)≤15000*d → ∀ (weight : ℕ→ℝ) (δ : ℝ), (∀ a∈Y,0≤weight a) → (∑ a∈Y,weight a)≤1 →
    let C := 2*(768*(10000*d)*(2*d+1))
    let err := fun i j=>missGridGram τ m R i j-∑ a∈X,weight a*Z a i*Z a j
    0≤δ → 4*C*δ≤1 → (∀ i,|err i i|≤δ) →
    (∑ i,∑ j,(if i=j then 0 else err i j)^2)≤δ^2 →
    (∀ (v : Option (Fin (2*input.degree)) ⊕ A → ℝ), (∑ a∈X\Y,weight a*(∑ i,Z a i*v i)^2)≤δ*(∑ i,(v i)^2)) →
    Concrete.BoxHasRank n ell := by
  classical
  obtain ⟨b₁,model⟩ := miss_grid_model_coercivity
  obtain ⟨b₂,grow⟩ := Fixed.degree_grows 130000
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b big hn target u y bu byy input rel stage A X Y listed band sub retained miss avoids good picks α β ba aa mb ma d τ p side μ w scale I m R Z mass weight δ nn total C err dn fit diag frob lost
  obtain ⟨one,two⟩ := max_le_iff.mp big
  have hd := grow b two
  have hd' : 10004≤Fixed.d b := by omega
  have wp (i : A) : 0<w i := sqrt_pos.mpr (rpow_pos_of_pos (Nat.cast_pos.mpr (mem_primeBand.mp (band i i.prop).1).1.pos) _)
  have rows : A⊆input.rows.toFinset := by
    intro i hi
    have clean : i∈input.clean := (rows_and_guards stage).2.2.2.1 ▸ List.mem_toFinset.mp (listed hi)
    exact List.mem_toFinset.mpr (mem_clean.mp clean).1
  apply boxHasRank_of_retained_energy hn hd' target bu byy stage A Y listed (fun i hi=>(band i hi).2) retained miss good picks scale weight (fun i=>inv_ne_zero (wp i).ne')
  intro x roots v vn perp
  have perp' (k : Bool) : (∑ i,if side i=k then w i*log (p i)*v (.inr i) else 0)=0 := by
    simpa only [side,p,scale,div_inv_eq_mul,mul_comm (log _)] using perp k
  have ref := model one target _ _ _ _ A rows (fun i hi=>(band i hi).1) α β ba aa mb ma mass v perp'
  let E := ∑ i,(v i)^2
  obtain ⟨k,nz⟩ := Function.ne_iff.mp vn
  have ep : 0<E := sum_pos' (fun _ _=>sq_nonneg _) ⟨k,mem_univ _,sq_pos_of_ne_zero nz⟩
  have cp : 0<C := by
    have : 0<d := Nat.cast_pos.mpr (Fixed.degree_pos (Nat.succ_pos _))
    dsimp only [C];positivity
  have near := gram_survives_deletion (missGridGram τ m R) Z weight X Y sub v C δ cp dn fit ref diag frob (lost v)
  let g := fun j=>v (.inl (some j))
  let shift := fun a=>v (.inl none)+∑ i : A,v (.inr i)*(if a%i.val.q=i.val.r then scale i else 0)
  have size : (∑ j,(g j)^2)≤E := by
    dsimp only [E];rw [Fintype.sum_sum_type,Fintype.sum_option]
    dsimp only [g];linarith only [sq_nonneg (v (.inl none)),sum_nonneg (s:=univ) (fun (i:A) _=>sq_nonneg (v (.inr i)))]
  have scores (a : ℕ) (z : Bool→Fin input.degree→ℝ) :
      (∑ i,retainedMissColumn input A scale z a i*v i)=shift a+∑ j,g j*log |(a:ℝ)/input.A-z (gridPlace j).1 (gridPlace j).2| := by
    exact retainedMissColumn_score input A scale z a v
  have nominal (a : ℕ) : (∑ i,Z a i*v i)=shift a+∑ j,g j*log |(a:ℝ)/input.A-nominalCenter input.degree j| := by
    simp only [Z,scores,gridPlace_center]
  change 0 < ∑ a∈Y,weight a*(∑ i,retainedMissColumn input A scale x a i*v i)^2
  simp_rw [scores]
  apply retained_true_score_positive hn hd' stage Y retained x (fun k i=>(roots k i).1) weight shift g nn total E ep size
  change E≤8*(768*(10000*d)*(2*d+1))*(∑ a∈Y,weight a*(shift a+∑ j,g j*log |(a:ℝ)/input.A-nominalCenter input.degree j|)^2)
  change E ≤ 4*C*(∑ a∈Y,weight a*(∑ i : Option (Fin (2*input.degree)) ⊕ A,Z a i*v i)^2) at near
  simp_rw [nominal] at near
  simpa only [show 4*C=8*(768*(10000*d)*(2*d+1)) by dsimp only [C];ring] using near

end
end Cogentic.Construction
#print axioms Cogentic.Construction.boxHasRank_of_miss_entries
