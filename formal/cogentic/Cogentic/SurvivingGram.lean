import Cogentic.PeeledCandidate
import Cogentic.GramNormDescent

/-! Positive joint Gram for the actual surviving, rescaled executable rows. -/

open scoped Matrix BigOperators
namespace Cogentic
open Marking

/-- Unprojected real logarithmic coordinates for the ordered bracket roots. -/
noncomputable def rawMarkMatrix (s : Input) (rel : Relations) (x : Bool → Fin s.degree → ℝ) :
    Matrix (Fin s.degree ⊕ Fin s.degree) (Fin rel.marks.length) ℝ :=
  fun k j => k.elim (fun i => Real.log |(rel.marks.get j:ℝ)/s.A-x false i|)
    (fun i => Real.log |(rel.marks.get j:ℝ)/s.A-x true i|)

theorem bracketMarkMatrix_eq_raw (s : Input) (rel : Relations) (x : Bool → Fin s.degree → ℝ) :
    bracketMarkMatrix s rel x = pairedHelmertMatrix (concreteRowCode s.degree) * rawMarkMatrix s rel x := by
  ext i j
  change _ = (pairedHelmertMatrix (concreteRowCode s.degree) *ᵥ (fun k => rawMarkMatrix s rel x k j)) i
  rw [pairedHelmertMatrix_apply]
  exact (concreteRowCode_elim s.degree (fun side => helmertCoordinate
    (Construction.markLogAt x (rel.marks.get j) s.A side)) i).symm

/-- An arbitrary numbering of surviving rows and their scales can be used for
the positive Gram certificate, including a numbering grouped by field. -/
theorem positiveMarkCore_of_numbered_rows {s : Input} {rel : Relations} {x : Bool → Fin s.degree → ℝ}
    {β : Type*} [Fintype β] (p : β ↪ Fin (rel.rows.length+1)) (J : Finset (Fin rel.marks.length))
    (scale : β → ℝ) (nz : ∀ i, scale i ≠ 0) (W : Matrix J J ℝ)
    (missTarget : ∀ i, i ∉ Set.range p → rel.rhs i=0)
    (missMark : ∀ i, i ∉ Set.range p → ∀ j ∈ J, rel.matrix i j=0) :
    let V : Matrix (β ⊕ Fin (2*s.degree-2)) J ℝ := jointRows
      (rel.matrix.submatrix p Subtype.val) scale ((bracketMarkMatrix s rel x).submatrix id Subtype.val)
    (V * W * V.transpose).PosDef → PositiveMarkCore s rel x := by
  classical
  intro V gram
  let I := Finset.univ.image p
  let e : β ≃ I := Equiv.ofBijective (fun k => ⟨p k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun i j h => p.injective (congrArg Subtype.val h),fun j => by
      obtain ⟨k,_,eq⟩ := Finset.mem_image.mp j.prop
      exact ⟨k,Subtype.ext eq⟩⟩
  have back (i : I) : p (e.symm i)=i.val := congrArg Subtype.val (e.apply_symm_apply i)
  have outside (i) (h : i∉I) : i ∉ Set.range p := by rintro ⟨k,rfl⟩; exact h (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
  refine ⟨I,J,scale ∘ e.symm,W,fun i => nz _,fun i h => missTarget i (outside i h),
    fun i h => missMark i (outside i h),?_⟩
  let E := e.symm.sumCongr (Equiv.refl (Fin (2*s.degree-2)))
  let V' : Matrix (I ⊕ Fin (2*s.degree-2)) J ℝ := jointRows
    (rel.matrix.submatrix Subtype.val Subtype.val) (scale ∘ e.symm)
    ((bracketMarkMatrix s rel x).submatrix id Subtype.val)
  have rows : V'=V.submatrix E (Equiv.refl J) := by
    ext i j
    cases i with
    | inl i => simp [V',V,jointRows,E,back]
    | inr i => rfl
  have product : V'*W*V'.transpose = (V*W*V.transpose).submatrix E E := by
    rw [rows]
    calc
      _ = (V.submatrix E (Equiv.refl J) * W.submatrix (Equiv.refl J) (Equiv.refl J)) *
        V.transpose.submatrix (Equiv.refl J) E := rfl
      _ = _ := by rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  change (V'*W*V'.transpose).PosDef
  rw [product]
  exact gram.submatrix E.injective

/-- Number the intercept first, then the selected executable rows. -/
def withIntercept {n : ℕ} {β : Type*} (f : β ↪ Fin n) : Option β ↪ Fin (n+1) where
  toFun
    | none => 0
    | some k => (f k).succ
  inj' := by
    rintro (_|i) (_|j) h
    · rfl
    · exact False.elim ((Fin.succ_ne_zero _) h.symm)
    · exact False.elim ((Fin.succ_ne_zero _) h)
    · exact congrArg some (f.injective (Fin.succ_inj.mp h))

/-- Numbering the surviving executable rows by their two fields and keeping
their actual rescalings identifies their block Gram with PositiveMarkCore. -/
theorem positiveMarkCore_of_two_field_gram {s : Input} {rel : Relations} {x : Bool → Fin s.degree → ℝ}
    {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] (rows : κ₁ ⊕ κ₂ ↪ Fin rel.rows.length)
    (J : Finset (Fin rel.marks.length)) (scale : κ₁ ⊕ κ₂ → ℝ) (nz : ∀ i, scale i ≠ 0)
    (weights : J → ℝ) (missTarget : ∀ i, i ∉ Set.range rows → rel.rhs i.succ=0)
    (missMark : ∀ i, i ∉ Set.range rows → ∀ j ∈ J, rel.matrix i.succ j=0) :
    let z := fun i (j : J) => scale i*(rel.matrix (rows i).succ j.val:ℝ)
    let L := (rawMarkMatrix s rel x).submatrix id (Subtype.val : J → Fin rel.marks.length)
    let V := twoFieldRows (concreteRowCode s.degree) (fun i => z (.inl i)) (fun i => z (.inr i)) L
    (V * Matrix.diagonal weights * V.transpose).PosDef → PositiveMarkCore s rel x := by
  classical
  intro z L V gram
  let p := withIntercept rows
  let scale' := fun i : Option (κ₁ ⊕ κ₂) => i.elim 1 scale
  have missing (i) (h : i.succ ∉ Set.range p) : i ∉ Set.range rows := by
    rintro ⟨k,rfl⟩
    exact h ⟨some k,rfl⟩
  apply positiveMarkCore_of_numbered_rows p J scale' (fun i => by cases i with
    | none => exact one_ne_zero
    | some i => exact nz i)
    (Matrix.diagonal weights) (fun i => Fin.cases (fun h => False.elim (h ⟨none,rfl⟩)) (fun k h => missTarget k (missing k h)) i)
    (fun i => Fin.cases (fun h => False.elim (h ⟨none,rfl⟩)) (fun k h => missMark k (missing k h)) i)
  let A := rel.matrix.submatrix p (Subtype.val : J → Fin rel.marks.length)
  let U := (bracketMarkMatrix s rel x).submatrix id (Subtype.val : J → Fin rel.marks.length)
  have eq : jointRows A scale' U=V := by
    ext i j
    rcases i with ⟨_⟩|i
    · rename_i i
      rcases i with _|(_|_)
      · change (1:ℝ)*(1:ℤ)=1
        norm_num
      · rfl
      · rfl
    · change bracketMarkMatrix s rel x i j.val = _
      rw [bracketMarkMatrix_eq_raw]
      rfl
  rwa [show jointRows (rel.matrix.submatrix p Subtype.val) scale' ((bracketMarkMatrix s rel x).submatrix id Subtype.val)=
    jointRows A scale' U by rfl,eq]

private theorem sum_covered_rows {κ η : Type*} [Fintype κ] [Fintype η]
    (rows : κ ↪ η) (f : η → ℝ) (off : ∀ k, k ∉ Set.range rows → f k=0) :
    ∑ i, f i = ∑ j, f (rows j) := by
  classical
  let S := Finset.univ.image rows
  have sub := Finset.sum_subset (f:=f) (Finset.subset_univ S) (fun i _ h => off i (by
    rintro ⟨j,rfl⟩; exact h (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))
  exact sub.symm.trans (Finset.sum_image rows.injective.injOn)

/-- The finite/real norm identity persists on the actual rescaled rows
after marks hitting every omitted row are zeroed. -/
theorem surviving_norm_coordinates {N ell a b c d : ℕ} (hn : 2 ≤ N)
    (big : 10004 ≤ Fixed.d (N.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1))) :
    let pair := Construction.construct N ell a b c d
    let s := TryPair.fixedInput N ell pair
    ∀ {rel}, stageOne s = some rel → ∀ x : Bool → Fin s.degree → ℝ,
    (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
      RootLogs.normalized s.A (s.coeffs side) (x side i)=0) →
    ∀ {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] (rows : κ₁ ⊕ κ₂ ↪ Fin rel.rows.length)
      (J : Finset (Fin rel.marks.length)) (scale : κ₁ ⊕ κ₂ → ℝ), (∀ i, scale i≠0) →
      (∀ i, (rel.rows.get (rows i)).second=i.elim (fun _ => false) (fun _ => true)) →
      (∀ i, i ∉ Set.range rows → ∀ j ∈ J, rel.matrix i.succ j=0) →
    let z := fun i (j : J) => scale i*(rel.matrix (rows i).succ j.val:ℝ)
    let w := fun i => Real.log (rel.rows.get (rows i)).q/scale i
    let C := fun side => Real.log |((polynomial (s.coeffs side)).leadingCoeff:ℝ)|+(s.degree:ℝ)*Real.log s.A
    let L := (rawMarkMatrix s rel x).submatrix id (Subtype.val : J → Fin rel.marks.length)
    (∀ j : J, (fun i => w (.inl i)) ⬝ᵥ (fun i => z (.inl i) j)=C false+∑ i, L (Sum.inl i) j) ∧
    (∀ j : J, (fun i => w (.inr i)) ⬝ᵥ (fun i => z (.inr i) j)=C true+∑ i, L (Sum.inr i) j) := by
  classical
  intro pair s rel marked x roots κ₁ κ₂ _ _ rows J scale nz color miss z w C L
  have entry (i) (j : J) : w i*z i j=Real.log (rel.rows.get (rows i)).q*(rel.matrix (rows i).succ j.val:ℝ) := by
    dsimp [w,z]; field_simp [nz i]
  have actual (j : J) (side : Bool) := retained_norm_coordinates hn big target marked side (x side) (roots side) j.val
  have covered (j : J) (side : Bool) := sum_covered_rows rows
    (fun i => (if (rel.rows.get i).second=side then Real.log (rel.rows.get i).q else 0)*(rel.matrix i.succ j.val:ℝ))
    (by intro i hi; rw [miss i hi j.val j.prop]; simp)
  constructor
  · intro j
    have h := actual j false
    rw [covered j false,Fintype.sum_sum_type] at h
    simp only [color,Sum.elim_inl,Sum.elim_inr,if_true,Bool.true_eq_false,if_false,zero_mul,Finset.sum_const_zero,add_zero] at h
    simp only [dotProduct,entry]
    exact h
  · intro j
    have h := actual j true
    rw [covered j true,Fintype.sum_sum_type] at h
    simp only [color,Sum.elim_inl,Sum.elim_inr,if_true,Bool.false_eq_true,if_false,zero_mul,Finset.sum_const_zero,zero_add] at h
    simp only [dotProduct,entry]
    exact h

/-- Model comparison on the two perpendicular subspaces of the surviving
actual rows suffices for the precise rank certificate used by extraction.
The finite scalings, dropped row support, norm identities and both true log
blocks are transported to the executable ordering here. -/
theorem positiveMarkCore_of_perpendicular {N ell a b c d : ℕ} (hn : 2 ≤ N)
    (big : 10004 ≤ Fixed.d (N.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1))) :
    let pair := Construction.construct N ell a b c d
    let s := TryPair.fixedInput N ell pair
    ∀ {rel}, stageOne s = some rel → ∀ x : Bool → Fin s.degree → ℝ,
    (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
      RootLogs.normalized s.A (s.coeffs side) (x side i)=0) →
    ∀ {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] (rows : κ₁ ⊕ κ₂ ↪ Fin rel.rows.length)
      (J : Finset (Fin rel.marks.length)) (scale : κ₁ ⊕ κ₂ → ℝ), (∀ i, scale i≠0) →
      (∀ i, (rel.rows.get (rows i)).second=i.elim (fun _ => false) (fun _ => true)) →
      (∀ i, i ∉ Set.range rows → rel.rhs i.succ=0) →
      (∀ i, i ∉ Set.range rows → ∀ j ∈ J, rel.matrix i.succ j=0) →
    let z := fun i (j : J) => scale i*(rel.matrix (rows i).succ j.val:ℝ)
    let w := fun i => Real.log (rel.rows.get (rows i)).q/scale i
    let L := (rawMarkMatrix s rel x).submatrix id (Subtype.val : J → Fin rel.marks.length)
    ∀ weight : J → ℝ,
    (∀ (v₀ : ℝ) (f₁ : κ₁ → ℝ) (f₂ : κ₂ → ℝ) (raw : Fin s.degree ⊕ Fin s.degree → ℝ),
      (fun i => w (.inl i)) ⬝ᵥ f₁=0 → (fun i => w (.inr i)) ⬝ᵥ f₂=0 →
      ¬(v₀=0 ∧ f₁=0 ∧ f₂=0 ∧ raw=0) →
      0 < ∑ j, weight j*(v₀+f₁ ⬝ᵥ (fun i => z (.inl i) j)+f₂ ⬝ᵥ (fun i => z (.inr i) j)+
        raw ⬝ᵥ (fun i => L i j))^2) → PositiveMarkCore s rel x := by
  classical
  intro pair s rel marked x root κ₁ κ₂ _ _ rows J scale nz color noTarget noMarks z w L weight model
  obtain ⟨left,right⟩ := surviving_norm_coordinates hn big target marked x root rows J scale nz color noMarks
  apply positiveMarkCore_of_two_field_gram rows J scale nz weight noTarget noMarks
  have dp : 0<s.degree := by change 0<Fixed.d (N.log2+1); omega
  exact twoFieldGram_of_perpendicular dp (concreteRowCode s.degree) (fun i => z (.inl i)) (fun i => z (.inr i))
    L weight (fun i => w (.inl i)) (fun i => w (.inr i)) _ _ left right model

end Cogentic

#print axioms Cogentic.positiveMarkCore_of_perpendicular
