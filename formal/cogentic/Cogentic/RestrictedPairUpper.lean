import Cogentic.NearSmoothUpper
import Cogentic.DifferencePrimes
import Cogentic.TwoFieldMoments

namespace Cogentic.Construction
open Finset Real Cogentic.Window
noncomputable section

/-- For any restriction on the first signed quotient, its actual restricted smooth
probability bounds the joint mass with a second smooth mark. The error is the
tail of the first projection, uniformly in the restriction and mark separation. -/
theorem PrescribedRows.restricted_joint_smooth_upper (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a≤Fixed.A b → a'∈(construct n ell 0 0 0 0).marks → a'≠a →
    ∀ (side : Bool) (F : ℤ→Prop) [DecidablePred F],
    let E := fun a (k : ℤ×ℤ) => supportedValue (sieveBand n ell (R.prefactor a side)) (R.intercept a side k.1 k.2)
    let A := fun (k : ℤ×ℤ) => E a k ∧ F (R.intercept a side k.1 k.2)
    prescribedProbability R side (fun k=>A k ∧ E a' k) ≤
      exp (10*(Fixed.h b:ℝ)) * (prescribedProbability R side A * prescribedProbability R side (E a')) +
        (1+90*exp (-(Fixed.U b:ℝ)))*(8*exp (-π*((b:ℝ)^3)^2/2)) := by
  classical
  obtain ⟨b₀,conditional⟩ := PrescribedRows.conditional_smooth_relative line
  refine ⟨b₀,?_⟩
  intro n ell a a' R b large hn comp target absent cap second diff side F inst E A
  let M := prodPrimes (R.miss a)
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let Z := ∑' k : C, coefficientWeight n k.val
  let r₀ := exp (10*(Fixed.h b:ℝ))
  let P := prescribedProbability R side (E a'); let P₁ := prescribedProbability R side A
  let rate := r₀*P
  let bulk (k : ℤ×ℤ) := |((k.1+(a:ℤ)*k.2:ℤ):ℝ)-lineCenter n a|≤(b:ℝ)^3*projectionScale n a
  let all (k : ℤ×ℤ) := A k ∧ E a' k
  let both (k : ℤ×ℤ) := bulk k ∧ all k
  obtain ⟨c,r,e,coords,ws,zp,_,events⟩ := R.coefficient_law target side cap
  let x := fun i : ℤ => c+(R.hitProduct a:ℤ)*i
  let y := fun i j : ℤ => r i+(M:ℤ)*j
  let key (i j : ℤ) := (x i-(a:ℤ)*y i j,y i j)
  let W (k : ℤ×ℤ) := coefficientWeight n (key k.1 k.2)
  let V (F : ℤ×ℤ→Prop) [DecidablePred F] (k : ℤ×ℤ) := if F (key k.1 k.2) then W k else 0
  have wp (k : ℤ×ℤ) : 0<W k := mul_pos (exp_pos _) (exp_pos _)
  have summ : Summable W := ws.congr (fun _ => (coefficient_weight_projection ..).symm)
  have vs (F : ℤ×ℤ→Prop) [DecidablePred F] : Summable (V F) := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact (wp k).le | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact (wp k).le | rfl) summ
  have prob (F : ℤ×ℤ→Prop) [DecidablePred F] : prescribedProbability R side F=(∑' k,V F k)/Z := by
    have h := events F
    change prescribedProbability R side F = _ at h
    rw [h]; congr 1; apply tsum_congr; intro k; dsimp only [V,W]
    split <;> first | exact (coefficient_weight_projection ..).symm | rfl
  have obs (i j : ℤ) : (key i j).1+(a:ℤ)*(key i j).2=x i := sub_add_cancel ..
  have pp : 0≤P := by
    apply div_nonneg
    · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
    · exact tsum_nonneg (fun k => mul_nonneg (exp_pos _).le (exp_pos _).le)
  have rp : 0≤rate := mul_nonneg (exp_pos _).le pp
  have fiber (i : ℤ) : (∑' j : ℤ, V both (i,j)) ≤ rate*(∑' j : ℤ, V A (i,j)) := by
    let seed := (x i-(a:ℤ)*r i, r i)
    have compatible := (e (i,0)).property
    rw [coords] at compatible
    simp only [mul_zero,add_zero] at compatible
    have atX : seed.1+(a:ℤ)*seed.2=x i := sub_add_cancel ..
    have same (j : ℤ) : A (key i j)↔A seed := by simp only [A,E,PrescribedRows.intercept,obs,atX]
    by_cases h : bulk seed ∧ A seed
    · have central := h.1
      dsimp only [bulk] at central
      have est := conditional R large hn comp target absent cap second diff side seed.1 seed.2 compatible central
      dsimp only at est
      rw [atX] at est
      change (∑' j : ℤ, V (E a') (i,j))/(∑' j : ℤ, W (i,j))≤rate at est
      have ge (j : ℤ) : V A (i,j)=W (i,j) := if_pos ((same j).mpr h.2)
      have le (j : ℤ) : V both (i,j) ≤ V (E a') (i,j) := by
        by_cases h' : both (key i j)
        · simp only [V,if_pos h',if_pos h'.2.2,le_refl]
        · simp only [V,if_neg h']; split <;> first | rfl | exact (wp _).le
      rw [tsum_congr ge]
      have pos : 0<∑' j : ℤ,W (i,j) := (wp (i,0)).trans_le ((summ.prod_factor i).le_tsum 0 (fun j _ => (wp _).le))
      exact ((vs both).prod_factor i|>.tsum_le_tsum le ((vs (E a')).prod_factor i)).trans ((div_le_iff₀ pos).mp est)
    · have no (j : ℤ) : ¬both (key i j) := by
        intro hit
        apply h
        exact ⟨by simpa only [bulk,atX,obs] using hit.1,(same j).mp hit.2.1⟩
      simp_rw [show ∀ j : ℤ,V both (i,j)=0 from fun j => if_neg (no j),tsum_zero]
      exact mul_nonneg rp (tsum_nonneg (fun j => by dsimp only [V]; split <;> first | rfl | exact (wp _).le))
  have bulkBound : prescribedProbability R side both≤rate*P₁ := by
    change prescribedProbability R side both≤rate*prescribedProbability R side A
    rw [prob both,prob A,←mul_div_assoc,div_le_div_iff_of_pos_right zp,
      (vs both).tsum_prod,(vs A).tsum_prod,←tsum_mul_left]
    exact (vs both).prod.tsum_le_tsum fiber ((vs A).prod.mul_left _)
  have outside := R.observation_cut_error target cap side ((b:ℝ)^3) (by positivity) all both
    (fun k inside => by have yes : bulk k := inside.le; simp [both,yes])
  change prescribedProbability R side all ≤ r₀*(P₁*P)+_
  change prescribedProbability R side both ≤ r₀*P*P₁ at bulkBound
  linarith only [bulkBound,(abs_le.mp outside).2]


/-- Probability removed from a large-prime deletion, under the actual compatible coefficient law. -/
theorem PrescribedRows.deleted_probability {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) (A B : ℤ×ℤ→Prop)
    [DecidablePred A] [DecidablePred B] (sub : ∀ k, B k → A k) :
    prescribedProbability R side (fun k=>A k ∧ ¬B k) =
      prescribedProbability R side A - prescribedProbability R side B := by
  have ha := R.point_event side target A
  have hb := R.point_event side target B
  have hd := R.point_event side target (fun k=>A k ∧ ¬B k)
  apply eq_sub_of_add_eq
  rw [←(hd.add hb).tsum_eq,←ha.tsum_eq]
  apply tsum_congr
  intro x
  by_cases inside : B x.val
  · simp [inside,sub _ inside]
  · by_cases h : A x.val <;> simp [inside,h]

/-- The joint mass lost by deleting primes of the mark difference at the first
smooth quotient, relative to the two actual marginals plus a Gaussian tail.
At most 20 band primes can divide the difference at this schedule. -/
theorem PrescribedRows.difference_joint_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → a'∈(construct n ell 0 0 0 0).marks → a'≠a → ∀ side : Bool,
    let J := sieveBand n ell (R.prefactor a side)
    let E := fun i (k : ℤ×ℤ) => supportedValue (sieveBand n ell (R.prefactor i side)) (R.intercept i side k.1 k.2)
    let K := J \ bandDifferencePrimes b a a'
    let clean := fun (k : ℤ×ℤ) => supportedValue K (R.intercept a side k.1 k.2)
    prescribedProbability R side (fun k=>(E a k ∧ ¬clean k) ∧ E a' k) ≤
      (exp (10*(Fixed.h b:ℝ))*(720*(Fixed.B b:ℝ)^(-199/400:ℝ)+360*exp (-(Fixed.U b:ℝ)))) *
        (prescribedProbability R side (E a) * prescribedProbability R side (E a')) +
      (1+90*exp (-(Fixed.U b:ℝ)))*(8*exp (-π*((b:ℝ)^3)^2/2)) := by
  classical
  obtain ⟨b₁,res⟩ := PrescribedRows.restricted_joint_smooth_upper line
  obtain ⟨b₂,loss⟩ := PrescribedRows.difference_exclusion_loss line
  refine ⟨max b₁ b₂,?_⟩
  intro n ell a a' R b large hn comp target absent first second diff side J E K clean
  have cap := ((constructed_marks_iff ..).mp first).2.1
  have cap' := ((constructed_marks_iff ..).mp second).2.1
  have upper := res R (max_le_iff.mp large).1 hn comp target absent cap second diff side (fun v=>¬supportedValue K v)
  have bad := loss R (max_le_iff.mp large).2 hn comp target absent first cap' diff.symm side
  change prescribedProbability R side (E a)-prescribedProbability R side clean ≤
    (720*(Fixed.B b:ℝ)^(-199/400:ℝ)+360*exp (-(Fixed.U b:ℝ)))*prescribedProbability R side (E a) at bad
  have sub (k : ℤ×ℤ) (h : clean k) : E a k := by
    obtain ⟨x,hx,eq⟩ := mem_image.mp h
    obtain ⟨ps,hp,eqp⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨x,mem_image.mpr ⟨ps,mem_powerset.mpr ((mem_powerset.mp hp).trans sdiff_subset),eqp⟩,eq⟩
  have pp : 0≤prescribedProbability R side (E a') := by
    apply div_nonneg
    · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
    · exact tsum_nonneg (fun k => mul_nonneg (exp_pos _).le (exp_pos _).le)
  rw [←R.deleted_probability target side (E a) clean sub] at bad
  apply upper.trans
  apply add_le_add_left
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right bad pp) (exp_pos _).le).trans_eq (by ring)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.difference_joint_loss
