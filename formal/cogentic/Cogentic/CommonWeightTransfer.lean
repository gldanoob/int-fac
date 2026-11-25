import Cogentic.CenteredResidueContrast

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- Transfer a pointwise relative error to the actual squared smooth score.
The comparison weight may vary by mark and the original score may have either sign. -/
private theorem second_le_relative {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (X : Finset ℕ) (delta v : ℕ→ℝ)
    (e : ℝ) (bd : ∀ a∈X, |delta a|≤e*v a) :
    let E := smoothMarkEvent R false
    let F := smoothMarkEvent T true
    twoFieldSecond R T X delta E F ≤ e^2 * twoFieldSecond R T X v E F := by
  intro E F
  have point (u w : ℤ×ℤ) : |twoFieldScore X delta E F u w|≤e*twoFieldScore X v E F u w := by
    unfold twoFieldScore
    rw [mul_sum]
    apply (abs_sum_le_sum_abs ..).trans
    refine sum_le_sum fun a ha=>?_
    by_cases both : E a u ∧ F a w <;> simp [both,bd a ha]
  have h₁ := twoField_score_second R T target X delta E F
  have h₂ := (twoField_score_second R T target X v E F).mul_left (e^2)
  apply hasSum_le _ h₁ h₂
  intro k
  rw [←mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (R.pointMass_nonneg _ _) (T.pointMass_nonneg _ _))
  have h := pow_le_pow_left₀ (abs_nonneg _) (point k.1.val k.2.val) 2
  simpa only [sq_abs,mul_pow] using h

/-- The common unconditional smooth weight can be compared to the explicit
two-field saddle insertion under each conditional law on the very same marks.
The resulting second-moment loss is quadratic in the uniform relative error. -/
theorem common_weight_second_transfer (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (X : Finset ℕ), (∀ a∈X, a∈(construct n ell 0 0 0 0).marks) →
    ∃ α β : ℕ→ℝ, (∀ a∈X, Window.saddleMean (primeBand b) (α a)=
      log ((exactMean n ell a false:ℝ)/targetPart n ell a false) ∧
      Window.saddleMean (primeBand b) (β a)=log ((exactMean n ell a true:ℝ)/targetPart n ell a true) ∧
      α a∈Set.Icc (199/200:ℝ) 1 ∧ β a∈Set.Icc (199/200:ℝ) 1) ∧
    ∀ (R T : PrescribedRows n ell) (f : ℕ→ℝ),
    let O := PrescribedRows.unrestricted n ell
    let J := fun a=>fullBandInsertion b (R.hitProduct a) (α a)*fullBandInsertion b (T.hitProduct a) (β a)
    let p := smoothMarkProbability R T
    let raw := fun a=>f a/smoothMarkProbability O O a
    let approx := fun a=>f a*(J a/p a)
    let E := smoothMarkEvent R false
    let F := smoothMarkEvent T true
    twoFieldSecond R T X (fun a=>raw a-approx a) E F ≤
      (C*exp (-K*(Fixed.z b:ℝ)^2))^2*twoFieldSecond R T X (fun a=>|f a| *(J a/p a)) E F := by
  classical
  obtain ⟨C,cp,b₁,model⟩ := hit_smooth_marginal_ratio line K hk
  obtain ⟨b₂,floor⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨C,cp,max b₁ b₂,?_⟩
  intro n ell b large hn composite target sieve X marks
  let O := PrescribedRows.unrestricted n ell
  let e := C*exp (-K*(Fixed.z b:ℝ)^2)
  have le₁ := (max_le_iff.mp large).1
  have le₂ := (max_le_iff.mp large).2
  have data (a : ℕ) : ∃ α β : ℝ, a∈X → α∈Set.Icc (199/200:ℝ) 1 ∧ β∈Set.Icc (199/200:ℝ) 1 ∧
      Window.saddleMean (primeBand b) α=log ((exactMean n ell a false:ℝ)/targetPart n ell a false) ∧
      Window.saddleMean (primeBand b) β=log ((exactMean n ell a true:ℝ)/targetPart n ell a true) ∧
      0<smoothMarkProbability O O a ∧ ∀ R T : PrescribedRows n ell,
      let J := fullBandInsertion b (R.hitProduct a) α*fullBandInsertion b (T.hitProduct a) β
      0<J ∧ |(smoothMarkProbability R T a/smoothMarkProbability O O a)/J-1|≤e := by
    by_cases ha : a∈X
    · obtain ⟨α,β,h⟩ := model le₁ hn composite target sieve (marks a ha)
      exact ⟨α,β,fun _=>h⟩
    · exact ⟨0,0,fun h=>False.elim (ha h)⟩
  choose α β law using data
  refine ⟨α,β,fun a ha=>?_,?_⟩
  · obtain ⟨aa,bb,ma,mb,_⟩ := law a ha
    exact ⟨ma,mb,aa,bb⟩
  intro R T f _ J p raw approx E F
  have prob (a) (ha : a∈X) : 0<p a := by
    have each (U : PrescribedRows n ell) (side : Bool) : 0<prescribedProbability U side (smoothMarkEvent U side a) := by
      have lo := floor U le₂ hn composite target sieve (marks a ha) side
      exact ((show 0<8/(Fixed.B b:ℝ) by dsimp [Fixed.B]; positivity).trans_le lo).trans_eq
        (probability_congr U side _ (smoothMarkEvent U side a) rfl)
    exact mul_pos (each R false) (each T true)
  have ratios (a) (ha : a∈X) := (law a ha).2.2.2.2
  apply second_le_relative R T target X _ _ e
  · intro a ha
    obtain ⟨po,rel⟩ := ratios a ha
    obtain ⟨jp,err⟩ := rel R T
    change 0<J a at jp
    let t := (p a/smoothMarkProbability O O a)/J a-1
    have id : raw a-approx a=f a*(J a/p a)*t := by
      change f a/smoothMarkProbability O O a-f a*(J a/p a)=
        f a*(J a/p a)*((p a/smoothMarkProbability O O a)/J a-1)
      field_simp [jp.ne',po.ne',(prob a ha).ne']
    rw [id,abs_mul,abs_mul,abs_of_pos (div_pos jp (prob a ha)),mul_comm e]
    exact mul_le_mul_of_nonneg_left err (mul_nonneg (abs_nonneg _) (div_pos jp (prob a ha)).le)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.common_weight_second_transfer
