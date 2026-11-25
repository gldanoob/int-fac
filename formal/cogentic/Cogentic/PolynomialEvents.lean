import Cogentic.PolynomialLaw
import Cogentic.PolynomialRelative

namespace Cogentic.Construction
open Real Cogentic.Window
noncomputable section

def signedBase (n ell a : ℕ) (side : Bool) : ℤ :=
  markSign n a side * eval (a:ℤ) (basePolynomial n ell side)

def signedSlope (n ell a : ℕ) (side : Bool) : ℤ :=
  markSign n a side * (primorial (Fixed.d (n.log2+1)):ℤ)*ell*((a:ℤ)-Fixed.rootBase n)

theorem signed_value (n ell a : ℕ) (side : Bool) (x : ℤ) :
    markSign n a side*affineValue n ell a side x=signedBase n ell a side+signedSlope n ell a side*x := by
  simp only [affineValue,signedBase,signedSlope]; ring

theorem signed_center {n ell a : ℕ} (big : 3≤Fixed.d (n.log2+1)) (side : Bool) :
    (exactMean n ell a side:ℝ)=(signedBase n ell a side:ℝ)+(signedSlope n ell a side:ℝ)*lineCenter n a := by
  have eq := congrArg (Int.cast (R := ℝ)) (signed_value n ell a side (lineCenter n a))
  rw [mean_is_affine big]
  push_cast at eq
  exact eq

theorem abs_slope (n ell a : ℕ) (side : Bool) :
    |(signedSlope n ell a side:ℝ)|=(primorial (Fixed.d (n.log2+1)):ℝ)*ell*|(a:ℝ)-Fixed.rootBase n| := by
  simp only [signedSlope,Int.cast_mul,Int.cast_sub,Int.cast_natCast,abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (primorial _)),abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ell)]
  have h : |(markSign n a side:ℝ)|=1 := by unfold markSign; split <;> norm_num
  rw [h,one_mul]

theorem PrescribedRows.signed_intercept {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) (side : Bool)
    (u v : ℤ) (ok : R.compatible side u v) :
    (R.intercept a side u v:ℝ) =
      ((signedBase n ell a side:ℝ)+(signedSlope n ell a side:ℝ)*(u+(a:ℝ)*v))/(R.prefactor a side:ℝ) := by
  have hd := dvd_mul_of_dvd_right (R.pre_dvd target a side u v ok) (markSign n a side)
  have h := congrArg (Int.cast (R := ℝ)) (Int.ediv_mul_cancel hd)
  change ((R.intercept a side u v*(R.prefactor a side:ℤ):ℤ):ℝ)=_ at h
  rw [signed_value] at h
  push_cast at h
  exact (eq_div_iff (by exact_mod_cast (R.pre_bounds target a side).1.ne')).mpr h

abbrev supportedValue (J : Finset ℕ) (z : ℤ) : Prop :=
  z∈(squarefreeSupport J).image (fun k : ℕ => (k:ℤ))

/-- Change a normalized Gaussian event from a coefficient coordinate to
    its signed integer evaluation; the affine offset and the full modulus
    scale cancel exactly, for either orientation. -/
theorem scalar_event_weight (J : Finset ℕ) (c s z : ℤ) (F K M μ σ Y S : ℝ)
    (kn : K≠0) (mp : 0<M) (start : (c:ℝ)=F+K*z) (step : (s:ℝ)=K*M)
    (center : Y=F+K*μ) (width : S=|K| *σ) :
    scalarMass J c s Y S =
      (M/σ*(∑' j : ℤ, if supportedValue J (c+s*j) then coeffGaussian ((z:ℝ)+M*j) μ σ else 0):ℝ) := by
  classical
  have size : (s.natAbs:ℝ)=|K| *M := by rw [Nat.cast_natAbs,Int.cast_abs,step,abs_mul,abs_of_pos mp]
  have normal : (s.natAbs:ℝ)/S=M/σ := by rw [width,size,mul_div_mul_left _ _ (abs_ne_zero.mpr kn)]
  have weight (j : ℤ) : coeffGaussian (↑(c+s*j:ℤ)) Y S=coeffGaussian ((z:ℝ)+M*j) μ σ := by
    rw [Int.cast_add,Int.cast_mul,start,step,center,width,show F+K*z+K*M*j=F+K*((z:ℝ)+M*j) by ring]
    exact conditional_second_weight kn ..
  unfold scalarMass
  rw [normal]
  congr 2
  exact tsum_congr (fun j => by simp only [supportedValue,weight j])

/-- The normalized first-coordinate event for an actual compatible seed
    is exactly the scalar character sum estimated by the relative theorem. -/
theorem PrescribedRows.first_event_weight {n ell a : ℕ} (R : PrescribedRows n ell) (big : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (am : a<Fixed.rootBase n) (side : Bool)
    (u v : ℤ) (ok : R.compatible side u v) :
    let J := sieveBand n ell (R.prefactor a side); let pre : ℝ := R.prefactor a side
    let c := R.intercept a side u v; let s := firstStep n ell a side; let x := u+a*v
    let H : ℝ := R.hitProduct a; let σ := projectionScale n a
    scalarMass J c s (exactMean n ell a side/pre) (oneWidth n ell a/pre) =
      (H/σ*(∑' j : ℤ, if supportedValue J (c+s*j) then coeffGaussian ((x:ℝ)+H*j) (lineCenter n a) σ else 0):ℝ) := by
  let pre : ℝ := R.prefactor a side; let H : ℝ := R.hitProduct a
  let F : ℝ := signedBase n ell a side; let D : ℝ := signedSlope n ell a side
  have pp : 0<pre := by dsimp only [pre]; exact_mod_cast (R.pre_bounds target a side).1
  have hp : 0<H := by dsimp only [H,PrescribedRows.hitProduct,PrescribedRows.hit]; exact_mod_cast (R.subprod_bounds (Finset.filter_subset (fun q => (R.residue q:ZMod q)=a) R.primes)).1
  have ep := (mem_dyadicTargets.mp target).1.pos
  have dn : D ≠ 0 := by
    apply abs_ne_zero.mp
    rw [show |D|=_ from abs_slope n ell a side]
    have p := primorial_pos (Fixed.d (n.log2+1))
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast p.ne') (by exact_mod_cast ep.ne')) (abs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast am.ne)))
  have size : ((firstStep n ell a side:ℤ):ℝ)*pre=D*H := by
    have hs := congrArg (fun z : ℤ => ((z*(R.hitProduct a:ℤ):ℤ):ℝ)) (scaled_first n ell a side)
    dsimp [pre,H,D,signedSlope,PrescribedRows.prefactor] at *
    push_cast at hs ⊢
    linear_combination hs
  apply scalar_event_weight _ _ _ (u+(a:ℤ)*v) (F/pre) (D/pre) H _ _ _ _ (div_ne_zero dn pp.ne') hp
  · rw [R.signed_intercept target a side u v ok]; push_cast; ring
  · field_simp [pp.ne']; linarith only [size]
  · rw [signed_center big]; dsimp [F,D]; ring
  · rw [abs_div,abs_of_pos pp,show |D|=_ from abs_slope n ell a side]
    unfold oneWidth; ring

private theorem regression_identity (A U a b x c₀ c₁ F D : ℝ) (vp : 0<(U*A)^2+a^2*U^2) :
    F+D*(c₀+b*c₁)+D*(((U*A)^2+a*b*U^2)/((U*A)^2+a^2*U^2))*(x-(c₀+a*c₁)) =
      F+D*(x+(b-a)*(c₁+a*U^2/((U*A)^2+a^2*U^2)*(x-(c₀+a*c₁)))) := by
  generalize hv : (U*A)^2+a^2*U^2=v at vp ⊢
  field_simp [vp.ne']
  rw [←hv]
  ring

/-- Evaluation of the second polynomial along the conditional Gaussian
    has the signed displacement used in the analytic window. -/
theorem signed_conditional_center {n ell a a' : ℕ} (big : 3≤Fixed.d (n.log2+1)) (side : Bool) (x : ℤ) :
    conditionalMean n ell a a' side x=(signedBase n ell a' side:ℝ)+(signedSlope n ell a' side:ℝ)*
      ((x:ℝ)+((a':ℝ)-a)*projectedConditionalCenter n a x) := by
  let b := n.log2+1; let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b
  have vp : 0<(U*A)^2+(a:ℝ)^2*U^2 := by
    have up : 0<U := by dsimp [U,Fixed.U]; positivity
    have ap : 0<A := by dsimp [A,Fixed.A]; positivity
    positivity
  have orient : (orientation n a' side:ℝ)=(markSign n a' side:ℝ) := by rw [←markSign_eq]; norm_cast
  have h := regression_identity A U a a' x ((b:ℝ)^2*U*A) ((b:ℝ)^2*U)
    (signedBase n ell a' side) (signedSlope n ell a' side) vp
  have ctr (j : ℕ) : (lineCenter n j:ℝ)=(b:ℝ)^2*U*A+j*((b:ℝ)^2*U) := by simp [lineCenter,b,U,A]
  rw [conditionalMean,signed_center big,projectedConditionalCenter,proj_sq,orient,ctr,ctr]
  simpa only [signedSlope,Int.cast_mul,Int.cast_sub,Int.cast_natCast,U,A,b] using h

/-- After fixing the observed first coordinate, each remaining
    coefficient-class Gaussian weight is exactly the normalized second
    scalar character sum, with its actual shifted mean. -/
theorem PrescribedRows.second_event_weight {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (big : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (am : a'<Fixed.rootBase n) (different : a'≠a) (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    let J := sieveBand n ell (R.prefactor a' side); let pre : ℝ := R.prefactor a' side
    let c := R.intercept a' side u v; let s := R.secondStep a a' side; let x := u+a*v
    let M : ℝ := prodPrimes (R.miss a); let t := conditionalScale n a
    scalarMass J c s (conditionalMean n ell a a' side x/pre) (twoWidth n ell a a'/pre) =
      (M/t*(∑' j : ℤ, if supportedValue J (c+s*j) then coeffGaussian ((v:ℝ)+M*j)
        (projectedConditionalCenter n a x) t else 0):ℝ) := by
  let pre : ℝ := R.prefactor a' side; let M : ℝ := prodPrimes (R.miss a)
  let F : ℝ := signedBase n ell a' side; let D : ℝ := signedSlope n ell a' side
  let δ : ℝ := (a':ℝ)-a; let x : ℤ := u+a*v
  have pp : 0<pre := by dsimp only [pre]; exact_mod_cast (R.pre_bounds target a' side).1
  have mp : 0<M := by dsimp only [M]; exact_mod_cast (R.subprod_bounds (s := R.miss a) Finset.sdiff_subset).1
  have ep := (mem_dyadicTargets.mp target).1.pos
  have dn : D ≠ 0 := by
    apply abs_ne_zero.mp
    rw [show |D|=_ from abs_slope n ell a' side]
    have p := primorial_pos (Fixed.d (n.log2+1))
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast p.ne') (by exact_mod_cast ep.ne')) (abs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast am.ne)))
  have δn : δ≠0 := sub_ne_zero.mpr (by exact_mod_cast different)
  have size : ((R.secondStep a a' side:ℤ):ℝ)*pre=D*δ*M := by
    have h := congrArg (Int.cast (R := ℝ)) (R.scaled_second a a' side)
    push_cast at h
    simpa only [pre,D,δ,M,signedSlope,Int.cast_mul,Int.cast_sub,Int.cast_natCast] using h
  apply scalar_event_weight _ _ _ v ((F+D*(x:ℝ))/pre) (D*δ/pre) M _ _ _ _ (div_ne_zero (mul_ne_zero dn δn) pp.ne') mp
  · rw [R.signed_intercept target a' side u v ok]; dsimp [x,δ,F,D]; push_cast; ring
  · field_simp [pp.ne']; linarith only [size]
  · rw [signed_conditional_center big]; dsimp only [δ,F,D,x]; ring
  · rw [abs_div,abs_mul,abs_of_pos pp,show |D|=_ from abs_slope n ell a' side]
    unfold twoWidth conditionalScale; dsimp only [δ]; ring

end
end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.first_event_weight

#print axioms Cogentic.Construction.PrescribedRows.second_event_weight
