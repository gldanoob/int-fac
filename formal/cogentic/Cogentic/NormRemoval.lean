import Cogentic.SelectedMinor
import Cogentic.NormCoordinates

/-! The two exact norm directions can be removed while preserving every
actual column score and injectivity of the coefficient change. -/

namespace Cogentic
open scoped Matrix BigOperators

private theorem helmert_prescribe (target : ℕ → ℝ) (d : ℕ) :
    ∃ f : ℕ → ℝ, ∀ j, 0 < j → j < d → helmertCoordinate f j = target j := by
  induction d with
  | zero => exact ⟨0,fun _ _ hj => False.elim (Nat.not_lt_zero _ hj)⟩
  | succ k ih =>
    obtain ⟨f,hf⟩ := ih
    let s := Real.sqrt ((k:ℝ)*(k+1))
    let t := ((∑ j ∈ Finset.range k, f j)-s*target k)/(k:ℝ)
    let g := Function.update f k t
    have before (j) (h : j≤k) : ∑ i ∈ Finset.range j, g i = ∑ i ∈ Finset.range j, f i := by
      exact Finset.sum_congr rfl (fun i hi => Function.update_of_ne (by have := Finset.mem_range.mp hi; omega) _ _)
    refine ⟨g,fun j jp hj => ?_⟩
    by_cases eq : j=k
    · subst j
      have kr : 0 < (k:ℝ) := by exact_mod_cast jp
      have sr : s≠0 := by dsimp [s]; positivity
      rw [helmertCoordinate,before k le_rfl,show g k=t from Function.update_self ..]
      change ((∑ i ∈ Finset.range k, f i)-k*t)/s=target k
      dsimp [t]
      field_simp
      ring
    · rw [← hf j jp (by omega),helmertCoordinate,helmertCoordinate,before j (by omega),
        show g j = f j from Function.update_of_ne eq _ _]

/-- The actual Helmert rows in either block admit any prescribed set of
coordinates. Their transpose consequently loses no search coefficient. -/
theorem paired_helmert_surjective {d : ℕ} {ι : Type*}
    (code : ι ≃ Fin (d-1) ⊕ Fin (d-1)) : Function.Surjective (pairedHelmertMatrix code).mulVec := by
  intro y
  let desired := fun (side : Bool) (k : ℕ) => if h : k-1<d-1 then
    y (code.symm (if side then Sum.inr ⟨k-1,h⟩ else Sum.inl ⟨k-1,h⟩)) else 0
  obtain ⟨f,hf⟩ := helmert_prescribe (desired false) d
  obtain ⟨g,hg⟩ := helmert_prescribe (desired true) d
  let raw := Sum.elim (fun i : Fin d => f i.val) (fun i : Fin d => g i.val)
  refine ⟨raw,?_⟩
  have trunc (T : ℕ → ℝ) (k : Fin (d-1)) :
      helmertCoordinate (fun j => if j<d then T j else 0) (k.val+1) = helmertCoordinate T (k.val+1) := by
    have lt : k.val+1<d := by omega
    have sumEq := Finset.sum_congr (s₁:=Finset.range (k.val+1)) rfl (fun i hi =>
      if_pos (lt_trans (Finset.mem_range.mp hi) lt) : ∀ i ∈ Finset.range (k.val+1), (if i<d then T i else 0)=T i)
    simp only [helmertCoordinate,sumEq,if_pos lt]
  funext i
  rw [pairedHelmertMatrix_apply]
  cases eq : code i with
  | inl k =>
    have lt : k.val+1<d := by omega
    have yay : code.symm (.inl k)=i := code.symm_apply_eq.mpr eq.symm
    change helmertCoordinate (fun j => if j<d then f j else 0) (k.val+1)=y i
    rw [trunc, hf _ (by omega) lt]
    simp [desired,k.isLt,yay]
  | inr k =>
    have lt : k.val+1<d := by omega
    have yay : code.symm (.inr k)=i := code.symm_apply_eq.mpr eq.symm
    change helmertCoordinate (fun j => if j<d then g j else 0) (k.val+1)=y i
    rw [trunc, hg _ (by omega) lt]
    simp [desired,k.isLt,yay]

/-- Inner-product projection away from the exact norm vector, including
the case in which this field has no surviving finite rows. -/
noncomputable def normShift {ι : Type*} [Fintype ι] (w v : ι → ℝ) := -(w ⬝ᵥ v)/(w ⬝ᵥ w)

theorem normShift_perpendicular {ι : Type*} [Fintype ι] (w v : ι → ℝ) :
    w ⬝ᵥ (v+normShift w v • w)=0 := by
  by_cases h : w ⬝ᵥ w=0
  · have z : w=0 := (dotProduct_self_eq_zero.mp h)
    simp [z]
  · rw [dotProduct_add,dotProduct_smul,normShift,smul_eq_mul]
    field_simp
    ring

/-- A single field's shift removes its norm coordinate exactly on every
mark having the genuine polynomial norm identity. -/
theorem normShift_score {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w v z : ι → ℝ) (y L : κ → ℝ) (C : ℝ) (identity : w ⬝ᵥ z = C + ∑ j, L j) :
    let t := normShift w v
    (-t*C)+(v+t • w) ⬝ᵥ z + (fun j => y j-t) ⬝ᵥ L = v ⬝ᵥ z + y ⬝ᵥ L := by
  intro t
  rw [add_dotProduct,smul_dotProduct,smul_eq_mul,identity]
  have eq : (fun j => y j-t) ⬝ᵥ L=y ⬝ᵥ L-t*∑ j, L j := by
    simp [dotProduct,sub_mul,Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [eq]
  ring

/-- A constant lift of a pair of Helmert coefficient blocks must vanish.
This is the injectivity required after the two norm directions are shifted. -/
theorem paired_helmert_transpose_constant {d : ℕ} (dp : 0<d) {ι : Type*} [Fintype ι]
    (code : ι ≃ Fin (d-1) ⊕ Fin (d-1)) (v : ι → ℝ) (c₁ c₂ : ℝ)
    (eq : (pairedHelmertMatrix code).transpose *ᵥ v = Sum.elim (fun _ => c₁) (fun _ => c₂)) :
    v=0 ∧ c₁=0 ∧ c₂=0 := by
  let H := pairedHelmertMatrix code
  let raw := H.transpose *ᵥ v
  have transposePair (x : Fin d ⊕ Fin d → ℝ) : raw ⬝ᵥ x = v ⬝ᵥ (H *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec,show raw = v ᵥ* H from Matrix.mulVec_transpose H v]
  have kernel : H *ᵥ raw=0 := by
    change H *ᵥ ((pairedHelmertMatrix code).transpose *ᵥ v)=0
    rw [eq]; exact pairedHelmertMatrix_constant code c₁ c₂
  have zr : raw=0 := dotProduct_self_eq_zero.mp (by rw [transposePair,kernel,dotProduct_zero])
  obtain ⟨x,hx⟩ := paired_helmert_surjective code v
  have v0 : v=0 := dotProduct_self_eq_zero.mp (calc
    v ⬝ᵥ v = v ⬝ᵥ (H *ᵥ x) := congrArg (fun y => v ⬝ᵥ y) hx.symm
    _ = raw ⬝ᵥ x := (transposePair x).symm
    _ = 0 := by rw [zr,zero_dotProduct])
  have ceq : Sum.elim (fun _ : Fin d => c₁) (fun _ : Fin d => c₂) = 0 := eq.symm.trans zr
  exact ⟨v0,congrFun ceq (.inl ⟨0,dp⟩),congrFun ceq (.inr ⟨0,dp⟩)⟩

/-- A zero shifted coefficient vector has zero intercept, finite
coordinates and Helmert coefficients already before norm removal. -/
theorem normRemoval_injective {d : ℕ} (dp : 0<d) {ι κ₁ κ₂ : Type*} [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    (code : ι ≃ Fin (d-1) ⊕ Fin (d-1)) (v₀ : ℝ) (v : ι → ℝ)
    (C₁ C₂ : ℝ) (w₁ z₁ : κ₁ → ℝ) (w₂ z₂ : κ₂ → ℝ) :
    let t₁ := normShift w₁ z₁
    let t₂ := normShift w₂ z₂
    (v₀-t₁*C₁-t₂*C₂=0) → (z₁+t₁ • w₁=0) → (z₂+t₂ • w₂=0) →
    ((pairedHelmertMatrix code).transpose *ᵥ v = Sum.elim (fun _ => t₁) (fun _ => t₂)) →
    v₀=0 ∧ z₁=0 ∧ z₂=0 ∧ v=0 := by
  intro t₁ t₂ intercept left right arch
  obtain ⟨v0,zl,zr⟩ := paired_helmert_transpose_constant dp code v t₁ t₂ arch
  simpa [zl,zr] using And.intro intercept (And.intro left (And.intro right v0))

end Cogentic

#print axioms Cogentic.normRemoval_injective
