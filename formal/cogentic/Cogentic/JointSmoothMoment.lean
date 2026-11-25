import Cogentic.PolynomialProbability

namespace Cogentic.Construction
open Real Cogentic.Window

/-- The probability of smoothness at two distinct marks on one prescribed
coefficient lattice is a one-dimensional Gaussian sum of the second scalar
mass over the first smooth observations. The same CRT representatives work
for every restriction of the first observation. -/
theorem PrescribedRows.joint_smooth_probability {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (big : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a≤Fixed.A (n.log2+1)) (am : a'<Fixed.rootBase n) (different : a'≠a) (side : Bool) :
    let J := sieveBand n ell (R.prefactor a side)
    let J' := sieveBand n ell (R.prefactor a' side)
    let pre : ℝ := R.prefactor a' side
    let H := R.hitProduct a
    let S := projectionScale n a
    ∃ (c : ℤ) (r : ℤ→ℤ), let x := fun i : ℤ => c+(H:ℤ)*i
      (∀ i, R.compatible side (x i-a*r i) (r i)) ∧
      ∀ (F : ℤ→Prop) [DecidablePred F],
      let m := fun i : ℤ => (scalarMass J' (R.intercept a' side (x i-a*r i) (r i))
        (R.secondStep a a' side) (conditionalMean n ell a a' side (x i)/pre)
        (twoWidth n ell a a'/pre)).re
      let model := (H:ℝ)/S * ∑' i : ℤ, if F (x i) ∧ supportedValue J (R.intercept a side (x i) 0)
        then coeffGaussian (x i) (lineCenter n a) S*m i else 0
      let actual := prescribedProbability R side (fun k =>
        (F (k.1+(a:ℤ)*k.2) ∧ supportedValue J (R.intercept a side k.1 k.2)) ∧
        supportedValue J' (R.intercept a' side k.1 k.2))
      0 ≤ model ∧ |actual-model| ≤ 18*exp (-(Fixed.U (n.log2+1):ℝ))*model := by
  classical
  intro J J' pre H S
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let Z := ∑' k : C, coefficientWeight n k.val
  let M := prodPrimes (R.miss a)
  let T := conditionalScale n a
  obtain ⟨c,r,e,coords,ws,zp,normal,events⟩ := R.coefficient_law target side cap
  let x := fun i : ℤ => c+(H:ℤ)*i
  let y := fun i j : ℤ => r i+(M:ℤ)*j
  let key := fun i j : ℤ => (x i-(a:ℤ)*y i j,y i j)
  let seed := fun i : ℤ => (x i-(a:ℤ)*r i,r i)
  let W₁ := fun i : ℤ => coeffGaussian (x i) (lineCenter n a) S
  let W₂ := fun i j : ℤ => coeffGaussian (y i j) (projectedConditionalCenter n a (x i)) T
  let W := fun k : ℤ×ℤ => W₁ k.1*W₂ k.1 k.2
  let h := fun i : ℤ => R.intercept a' side (seed i).1 (seed i).2
  let s := R.secondStep a a' side
  let m := fun i : ℤ => (scalarMass J' (h i) s (conditionalMean n ell a a' side (x i)/pre)
    (twoWidth n ell a a'/pre)).re
  have ok (i : ℤ) : R.compatible side (seed i).1 (seed i).2 := by
    have h := (e (i,0)).property
    rw [coords] at h
    simpa only [Int.mul_zero,Int.add_zero] using h
  have hPos : 0<(H:ℝ) := by
    exact_mod_cast (R.subprod_bounds (s:=R.hit a) (Finset.filter_subset ..)).1
  have mPos : 0<(M:ℝ) := by
    exact_mod_cast (R.subprod_bounds (s:=R.miss a) Finset.sdiff_subset).1
  have sPos : 0<S := by dsimp [S,projectionScale,Fixed.A,Fixed.U]; positivity
  have tPos : 0<T := by
    dsimp only [T,conditionalScale]
    exact div_pos (by dsimp [Fixed.U,Fixed.A]; positivity) sPos
  have obs (i j : ℤ) : (key i j).1+(a:ℤ)*(key i j).2=x i := sub_add_cancel ..
  have second (i j : ℤ) : R.intercept a' side (key i j).1 (key i j).2=h i+s*j := by
    have step := R.second_quotient target a a' side (seed i).1 (seed i).2 (ok i) j
    change markSign n a' side*affineValue n ell a' side
      (x i-(a:ℤ)*y i j+(a':ℤ)*y i j)/(R.prefactor a' side:ℤ)=_
    rw [show x i-(a:ℤ)*y i j+(a':ℤ)*y i j =
        (seed i).1+(a':ℤ)*(seed i).2+((a':ℤ)-a)*prodPrimes (R.miss a)*j by
      dsimp only [seed,y,M]; ring]
    exact step
  have moment (i : ℤ) : m i = (M:ℝ)/T*(∑' j : ℤ, if supportedValue J' (h i+s*j) then W₂ i j else 0) := by
    have exactMass := congrArg Complex.re (R.second_event_weight big target am different side
      (seed i).1 (seed i).2 (ok i))
    simpa only [seed,sub_add_cancel,Complex.ofReal_re,W₂,y,Int.cast_add,Int.cast_mul,Int.cast_natCast] using exactMass
  refine ⟨c,r,ok,?_⟩
  intro F inst
  let good := fun i : ℤ => F (x i) ∧ supportedValue J (R.intercept a side (x i) 0)
  let E := fun k : ℤ×ℤ => (F (k.1+(a:ℤ)*k.2) ∧ supportedValue J (R.intercept a side k.1 k.2)) ∧
    supportedValue J' (R.intercept a' side k.1 k.2)
  let V := fun k : ℤ×ℤ => if E (key k.1 k.2) then W k else 0
  let N := ∑' i : ℤ, if good i then W₁ i*m i else 0
  have wn (k : ℤ×ℤ) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  have vs : Summable V := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact wn k | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact wn k | rfl) (show Summable W from ws)
  have fiber (i : ℤ) : (∑' j : ℤ,V (i,j)) = (T/M)*(if good i then W₁ i*m i else 0) := by
    have intercept (j : ℤ) : R.intercept a side (key i j).1 (key i j).2=R.intercept a side (x i) 0 := by
      simp only [intercept,obs,Int.mul_zero,Int.add_zero]
    have spec (j : ℤ) : E (key i j) ↔ good i ∧ supportedValue J' (h i+s*j) := by
      simp only [E,good,obs,intercept j,second i j]
    simp only [V,spec,W]
    by_cases g : good i
    · simp only [g,true_and,if_true,←mul_ite_zero,tsum_mul_left,moment i]
      field_simp
    · simp only [g,false_and,if_false,tsum_zero,mul_zero]
  have central : (∑' k,V k) = (T/M)*N := by
    rw [vs.tsum_prod]
    exact (tsum_congr fiber).trans (tsum_mul_left ..)
  have actual := events E
  change prescribedProbability R side E=(∑' k,V k)/Z at actual
  rw [central] at actual
  let model := (H:ℝ)/S*N
  have valid : 0 ≤ model := by
    have positiveN : 0≤N := tsum_nonneg (fun i => by
      split
      · rw [moment]; exact mul_nonneg (exp_pos _).le (mul_nonneg (div_nonneg mPos.le tPos.le)
          (tsum_nonneg (fun j => by split <;> first | exact (exp_pos _).le | rfl)))
      · rfl)
    exact mul_nonneg (div_nonneg hPos.le sPos.le) positiveN
  have ratio : prescribedProbability R side E=((S/H)*(T/M)/Z)*model := by
    rw [actual]
    dsimp only [model]; field_simp
  change 0 ≤ model ∧ |prescribedProbability R side E-model| ≤ _*model
  refine ⟨valid,?_⟩
  rw [ratio,←sub_one_mul,abs_mul,abs_of_nonneg valid]
  exact mul_le_mul_of_nonneg_right normal valid

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.joint_smooth_probability
