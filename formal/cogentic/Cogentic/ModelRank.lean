import Cogentic.SurvivingGram

/-! Fixed-grid scalar moment criteria imply positivity and actual extraction. -/

open scoped Matrix BigOperators
namespace Cogentic
open Marking

/-- Interleave the left and right normalized target roots in spatial order. -/
noncomputable def interleavePlaces (d : ℕ) : Fin d ⊕ Fin d ≃ Fin (2*d) :=
  let f : Fin d ⊕ Fin d → Fin (2*d) := Sum.elim
    (fun i => ⟨2*i.val,by omega⟩) (fun i => ⟨2*i.val+1,by omega⟩)
  Equiv.ofBijective f ⟨by
    rintro (i|i) (j|j) eq <;> have h := congrArg Fin.val eq <;> dsimp [f] at h <;>
      first | exact congrArg Sum.inl (Fin.ext (by omega))
            | exact congrArg Sum.inr (Fin.ext (by omega))
            | omega,
    fun k => by
      have lt : k.val/2<d := by omega
      by_cases even : k.val%2=0
      · exact ⟨.inl ⟨_,lt⟩,Fin.ext (by change 2*(k.val/2)=k.val; omega)⟩
      · exact ⟨.inr ⟨_,lt⟩,Fin.ext (by change 2*(k.val/2)+1=k.val; omega)⟩⟩

theorem interleaved_centers {d : ℕ} (k : Fin d) :
    nominalCenter d (interleavePlaces d (.inl k)) = (Construction.center d false k.val:ℝ) ∧
    nominalCenter d (interleavePlaces d (.inr k)) = (Construction.center d true k.val:ℝ) := by
  have left : (interleavePlaces d (.inl k)).val=2*k.val := rfl
  have right : (interleavePlaces d (.inr k)).val=2*k.val+1 := rfl
  constructor <;> simp [nominalCenter,left,right,Construction.center]
  ring

/-- The empirical matrix comparison required from the one- and two-mark
moment calculation, with the finite-only covariance error distinguished
from the full-coordinate error. -/
def CenteredMomentBounds {α : Type*} [Fintype α] (p g : α → ℝ)
    (u cells F arch actual : ℝ) : Prop :=
  ∃ (m : α → ℝ) (diag projection remainder ε : ℝ),
    (∑ a, p a*(m a)^2 ≤ 12*u*F) ∧ 15*F ≤ 16*diag ∧ 16*projection ≤ F ∧ 16*remainder ≤ F ∧
    (∑ a, p a*(g a+m a)^2)+diag-projection-remainder ≤ actual+ε ∧ 768*u*cells*ε ≤ F+arch

private theorem sqsum_zero {ι : Type*} [Fintype ι] (x : ι → ℝ) (eq : ∑ j, (x j)^2=0) : x=0 :=
  dotProduct_self_eq_zero.mp (by simpa only [dotProduct,←sq] using eq)

private theorem score_size_pos {ι κ₁ κ₂ : Type*} [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    (v : ℝ) (f₁ : κ₁ → ℝ) (f₂ : κ₂ → ℝ) (a : ι → ℝ) (ne : ¬(v=0 ∧ f₁=0 ∧ f₂=0 ∧ a=0)) :
    0 < ((∑ i, (f₁ i)^2)+(∑ i, (f₂ i)^2))+(v^2+∑ i, (a i)^2) := by
  have p₁ : 0≤∑ i, (f₁ i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have p₂ : 0≤∑ i, (f₂ i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have pa : 0≤∑ i, (a i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_contra! h
  exact ne ⟨by nlinarith [sq_nonneg v],sqsum_zero _ (by nlinarith [sq_nonneg v]),
    sqsum_zero _ (by nlinarith [sq_nonneg v]),sqsum_zero _ (by nlinarith [sq_nonneg v])⟩

/-- The scalar empirical comparisons on the surviving rows, plus the
specified baseline/root intervals and deleted row support, are sufficient
for the executable's positive mark core. -/
theorem positiveMarkCore_of_centered_moments {N ell a b c d : ℕ} (hn : 2 ≤ N)
    (big : 130000 ≤ Fixed.d (N.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1))) :
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
    let width := (Fixed.invWidth (N.log2+1):ℝ)⁻¹
    let cells := (2*s.degree+1:ℝ)
    ∀ {β : Option (Fin (2*s.degree)) → Type*} [∀ k, Fintype (β k)]
      (point mass : (k : Option (Fin (2*s.degree))) → β k → ℝ),
      (∀ a, 3/4 ≤ point none a ∧ point none a ≤ 1) →
      (∀ i a, nominalCenter s.degree i+width ≤ point (some i) a ∧ point (some i) a ≤ nominalCenter s.degree i+2*width) →
      (∀ k a, 0 ≤ mass k a) → (∀ k, ∑ a, mass k a = 1) →
    let p := fun a : (k : Option (Fin (2*s.degree))) × β k => mass a.1 a.2/cells
    ∀ (weight : J → ℝ) (u : ℝ), 1 ≤ u →
    (∀ (v₀ : ℝ) (f₁ : κ₁ → ℝ) (f₂ : κ₂ → ℝ) (raw : Fin s.degree ⊕ Fin s.degree → ℝ),
      (fun i => w (.inl i)) ⬝ᵥ f₁=0 → (fun i => w (.inr i)) ⬝ᵥ f₂=0 →
      let va := raw ∘ (interleavePlaces s.degree).symm
      let g := fun a : (k : Option (Fin (2*s.degree))) × β k =>
        v₀+∑ j, Real.log |point a.1 a.2-nominalCenter s.degree j| * va j
      let F := (∑ i, (f₁ i)^2)+∑ i, (f₂ i)^2
      let arch := v₀^2+∑ i, (va i)^2
      let actual := ∑ j, weight j*(v₀+f₁ ⬝ᵥ (fun i => z (.inl i) j)+f₂ ⬝ᵥ (fun i => z (.inr i) j)+
        raw ⬝ᵥ (fun i => L i j))^2
      CenteredMomentBounds p g u cells F arch actual) → PositiveMarkCore s rel x := by
  classical
  intro pair s rel marked x roots κ₁ κ₂ _ _ rows J scale nz color noTarget noMarks z w L width cells β βfinite point mass
    base loc nonneg norm p weight u up moment
  apply positiveMarkCore_of_perpendicular hn (by omega) target marked x roots rows J scale nz color noTarget noMarks weight
  intro v₀ f₁ f₂ raw left right ne
  let va := raw ∘ (interleavePlaces s.degree).symm
  let F := (∑ i, (f₁ i)^2)+∑ i, (f₂ i)^2
  let arch := v₀^2+∑ i, (va i)^2
  let actual := ∑ j, weight j*(v₀+f₁ ⬝ᵥ (fun i => z (.inl i) j)+f₂ ⬝ᵥ (fun i => z (.inr i) j)+
    raw ⬝ᵥ (fun i => L i j))^2
  obtain ⟨m,diag,proj,remn,ε,mean,hdiag,hproj,hrem,obs,err⟩ := moment v₀ f₁ f₂ raw left right
  have fp : 0≤F := by dsimp [F]; positivity
  have margin := @fixed_centered_model_margin (N.log2+1) big β βfinite point mass base loc nonneg norm v₀ va m u F diag proj remn actual ε
    up fp mean hdiag hproj hrem obs err
  have survive : ¬(v₀=0 ∧ f₁=0 ∧ f₂=0 ∧ va=0) := by
    rintro ⟨h,l,r,zero⟩
    apply ne
    refine ⟨h,l,r,?_⟩
    funext j
    have eq := congrFun zero (interleavePlaces s.degree j)
    simpa only [va,Function.comp_apply,Equiv.symm_apply_apply,Pi.zero_apply] using eq
  have pos : 0 < F+arch := score_size_pos v₀ f₁ f₂ va survive
  have factor : 0 < 768*u*cells := by dsimp [cells]; positivity
  change F+arch ≤ 768*u*cells*actual at margin
  exact pos_of_mul_pos_right (pos.trans_le margin) factor.le

namespace Construction

/-- The field and index of a root in the spatially interleaved grid. -/
noncomputable def gridPlace {d : ℕ} (j : Fin (2*d)) : Bool × Fin d :=
  ((interleavePlaces d).symm j).elim (fun i => (false,i)) (fun i => (true,i))

theorem gridPlace_center {d : ℕ} (j : Fin (2*d)) :
    nominalCenter d j = (center d (gridPlace j).1 (gridPlace j).2.val:ℝ) := by
  obtain ⟨i,rfl⟩ := (interleavePlaces d).surjective j
  cases i with
  | inl k => simpa [gridPlace] using (interleaved_centers k).1
  | inr k => simpa [gridPlace] using (interleaved_centers k).2

end Construction

end Cogentic

#print axioms Cogentic.positiveMarkCore_of_centered_moments
