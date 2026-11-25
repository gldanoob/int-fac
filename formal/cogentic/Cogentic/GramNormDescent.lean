import Cogentic.NormRemoval
import Cogentic.GramPositivity

/-! Strict positivity for the two-field Gram in its original coordinates. -/

open scoped Matrix BigOperators
namespace Cogentic

/-- Joint column array in block notation. The finite blocks are already in
the chosen row scales. The archimedean block uses the actual Helmert matrix. -/
noncomputable def twoFieldRows {d : ℕ} {ι κ₁ κ₂ μ : Type*}
    (code : ι ≃ Fin (d-1) ⊕ Fin (d-1)) (z₁ : κ₁ → μ → ℝ) (z₂ : κ₂ → μ → ℝ)
    (L : Matrix (Fin d ⊕ Fin d) μ ℝ) :
    Matrix (Option (κ₁ ⊕ κ₂) ⊕ ι) μ ℝ :=
  fun i j => match i with
    | .inl none => 1
    | .inl (some (.inl k)) => z₁ k j
    | .inl (some (.inr k)) => z₂ k j
    | .inr k => (pairedHelmertMatrix code * L) k j

/-- Positivity on the subspace perpendicular to both norm directions suffices
for the positive definite Gram in the original intercept, finite and ordered
Helmert coordinates. The proof uses the exact norm identity on every mark. -/
theorem twoFieldGram_of_perpendicular {d : ℕ} (dp : 0<d) {ι κ₁ κ₂ μ : Type*}
    [Fintype ι] [Fintype κ₁] [Fintype κ₂] [Fintype μ] [DecidableEq μ]
    (code : ι ≃ Fin (d-1) ⊕ Fin (d-1)) (z₁ : κ₁ → μ → ℝ) (z₂ : κ₂ → μ → ℝ)
    (L : Matrix (Fin d ⊕ Fin d) μ ℝ) (weight : μ → ℝ)
    (w₁ : κ₁ → ℝ) (w₂ : κ₂ → ℝ) (C₁ C₂ : ℝ)
    (norm₁ : ∀ j, w₁ ⬝ᵥ (fun i => z₁ i j)=C₁+∑ k, L (Sum.inl k) j)
    (norm₂ : ∀ j, w₂ ⬝ᵥ (fun i => z₂ i j)=C₂+∑ k, L (Sum.inr k) j)
    (model : ∀ (v₀ : ℝ) (f₁ : κ₁ → ℝ) (f₂ : κ₂ → ℝ) (raw : Fin d ⊕ Fin d → ℝ),
      w₁ ⬝ᵥ f₁=0 → w₂ ⬝ᵥ f₂=0 → ¬(v₀=0 ∧ f₁=0 ∧ f₂=0 ∧ raw=0) →
      0 < ∑ j, weight j*(v₀+f₁ ⬝ᵥ (fun i => z₁ i j)+f₂ ⬝ᵥ (fun i => z₂ i j)+raw ⬝ᵥ (fun i => L i j))^2) :
    let V := twoFieldRows code z₁ z₂ L
    (V * Matrix.diagonal weight * V.transpose).PosDef := by
  classical
  intro V
  apply diagonal_gram_positive
  intro v ne
  let v₀ := v (Sum.inl none)
  let f₁ := fun i => v (Sum.inl (some (Sum.inl i)))
  let f₂ := fun i => v (Sum.inl (some (Sum.inr i)))
  let g := fun i => v (Sum.inr i)
  let H := pairedHelmertMatrix code
  let raw := H.transpose *ᵥ g
  let t₁ := normShift w₁ f₁
  let t₂ := normShift w₂ f₂
  let u := Sum.elim (fun i : Fin d => raw (Sum.inl i)-t₁) (fun i : Fin d => raw (Sum.inr i)-t₂)
  have survive : ¬(v₀-t₁*C₁-t₂*C₂=0 ∧ f₁+t₁ • w₁=0 ∧ f₂+t₂ • w₂=0 ∧ u=0) := by
    rintro ⟨iv,left,right,uv⟩
    have constant : raw=Sum.elim (fun _ => t₁) (fun _ => t₂) := by
      funext k
      cases k with
      | inl i => exact sub_eq_zero.mp (congrFun uv (Sum.inl i))
      | inr i => exact sub_eq_zero.mp (congrFun uv (Sum.inr i))
    obtain ⟨i0,f10,f20,g0⟩ := normRemoval_injective dp code v₀ g C₁ C₂ w₁ f₁ w₂ f₂ iv left right constant
    apply ne
    funext k
    rcases k with (_|i)
    · rename_i k
      rcases k with _|(_|_)
      · exact i0
      · exact congrFun f10 _
      · exact congrFun f20 _
    · exact congrFun g0 i
  have positive := model (v₀-t₁*C₁-t₂*C₂) (f₁+t₁ • w₁) (f₂+t₂ • w₂) u
    (normShift_perpendicular w₁ f₁) (normShift_perpendicular w₂ f₂) survive
  have entry (j) : (V.transpose *ᵥ v) j = v₀+f₁ ⬝ᵥ (fun i => z₁ i j)+f₂ ⬝ᵥ (fun i => z₂ i j) +
      raw ⬝ᵥ (fun i => L i j) := by
    have arch : raw ⬝ᵥ (fun i => L i j) = g ⬝ᵥ (H *ᵥ fun i => L i j) := by
      rw [Matrix.dotProduct_mulVec,show raw=g ᵥ* H from Matrix.mulVec_transpose H g]
    rw [arch]
    change (∑ k, twoFieldRows code z₁ z₂ L k j*v k) = _
    simp only [Fintype.sum_sum_type,Fintype.sum_option,twoFieldRows,one_mul]
    simp only [v₀,f₁,f₂,g,H,dotProduct,Matrix.mulVec,Matrix.mul_apply,mul_comm]
    ring
  have score (j) : (V.transpose *ᵥ v) j =
      (v₀-t₁*C₁-t₂*C₂)+(f₁+t₁ • w₁) ⬝ᵥ (fun i => z₁ i j)+(f₂+t₂ • w₂) ⬝ᵥ (fun i => z₂ i j)+u ⬝ᵥ (fun i => L i j) := by
    have left := normShift_score w₁ f₁ (fun i => z₁ i j) (fun i => raw (Sum.inl i)) (fun i => L (Sum.inl i) j) C₁ (norm₁ j)
    have right := normShift_score w₂ f₂ (fun i => z₂ i j) (fun i => raw (Sum.inr i)) (fun i => L (Sum.inr i) j) C₂ (norm₂ j)
    change (-t₁*C₁)+_+_= _ at left
    change (-t₂*C₂)+_+_= _ at right
    rw [entry]
    have split (a : Fin d ⊕ Fin d → ℝ) : a ⬝ᵥ (fun i => L i j) =
        (fun i => a (Sum.inl i)) ⬝ᵥ (fun i => L (Sum.inl i) j) +
        (fun i => a (Sum.inr i)) ⬝ᵥ (fun i => L (Sum.inr i) j) := Fintype.sum_sum_type _
    rw [split raw,split u]
    dsimp only [u,Sum.elim_inl,Sum.elim_inr]
    linarith
  simpa only [score] using positive

end Cogentic

#print axioms Cogentic.twoFieldGram_of_perpendicular
