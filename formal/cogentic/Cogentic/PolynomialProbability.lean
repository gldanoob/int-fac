import Cogentic.PolynomialEvents

namespace Cogentic.Construction
open Real Cogentic.Window
noncomputable section

/-- The actual conditioned discrete coefficient measure. -/
def prescribedProbability {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) (E : ℤ×ℤ→Prop)
    [DecidablePred E] : ℝ :=
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  (∑' k : C, if E k.val then coefficientWeight n k.val else 0)/(∑' k : C, coefficientWeight n k.val)

theorem PrescribedRows.probability_scales {n ell a : ℕ} (R : PrescribedRows n ell)
    (cap : a≤Fixed.A (n.log2+1)) :
    let H : ℝ := R.hitProduct a; let M : ℝ := prodPrimes (R.miss a)
    let τ := projectionScale n a/H; let υ := conditionalScale n a/M
    let e₁ := 6*exp (-π*τ^2); let e₂ := 12*exp (-π*υ^2)
    2≤τ ∧ 2≤υ ∧ e₂+e₁*(1+e₂) ≤ 90*exp (-(Fixed.U (n.log2+1):ℝ)) ∧
      6*exp (-π*υ^2) ≤ 6*exp (-(Fixed.U (n.log2+1):ℝ)) := by
  let H := R.hitProduct a; let M := prodPrimes (R.miss a)
  have hp := R.subprod_bounds (Finset.filter_subset (fun q => (R.residue q:ZMod q)=a) R.primes)
  have mp := R.subprod_bounds (s := R.miss a) Finset.sdiff_subset
  have ⟨first,second,e⟩ := conditional_schedule cap (H := H) (M := M) hp.1 mp.1 hp.2 mp.2
  let X := exp (-π*(projectionScale n a/H)^2); let Y := exp (-π*(conditionalScale n a/M)^2)
  let Z := exp (-(Fixed.U (n.log2+1):ℝ))
  change 6*max (3*X) (3*Y) ≤ 18*Z at e
  have xz : X≤Z := by linarith [le_max_left (3*X) (3*Y)]
  have yz : Y≤Z := by linarith [le_max_right (3*X) (3*Y)]
  have yn : 0≤Y := (exp_pos _).le
  have zp : Z≤1 := Real.exp_le_one_iff.mpr (by simp)
  have xy : X*Y≤Z := (mul_le_mul_of_nonneg_right xz yn).trans (by nlinarith [mul_nonneg (show 0≤Z by exact (exp_pos _).le) (sub_nonneg.mpr (yz.trans zp))])
  refine ⟨first,second,?_,?_⟩
  · change 12*Y+6*X*(1+12*Y)≤90*Z; linarith only [xz,yz,xy]
  · change 6*Y≤6*Z; linarith only [yz]

/-- Given the first coordinate, the original two-coordinate measure of
    the signed squarefree event has the analytic scalar mass as its model.
    This includes the actual conditional residue shift and both normalizers. -/
theorem PrescribedRows.second_probability {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (big : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a≤Fixed.A (n.log2+1)) (am : a'<Fixed.rootBase n) (different : a'≠a)
    (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    let J := sieveBand n ell (R.prefactor a' side); let pre : ℝ := R.prefactor a' side
    let c := R.intercept a' side u v; let s := R.secondStep a a' side; let x := u+(a:ℤ)*v
    let M := prodPrimes (R.miss a); let y := fun j : ℤ => v+(M:ℤ)*j
    let key := fun j : ℤ => (x-a*y j,y j)
    let G := fun j : ℤ => coefficientWeight n (key j)
    let E := fun j : ℤ => supportedValue J (R.intercept a' side (key j).1 (key j).2)
    let Z := ∑' j, G j
    let m := (scalarMass J c s (conditionalMean n ell a a' side x/pre) (twoWidth n ell a a'/pre)).re
    0<Z ∧ |(∑' j, if E j then G j else 0)/Z-m| ≤ 6*exp (-(Fixed.U (n.log2+1):ℝ))*m := by
  let J := sieveBand n ell (R.prefactor a' side); let M := prodPrimes (R.miss a)
  let c := R.intercept a' side u v; let s := R.secondStep a a' side; let x := u+(a:ℤ)*v
  let t := conditionalScale n a; let μ := projectedConditionalCenter n a x
  let y := fun j : ℤ => v+(M:ℤ)*j
  let E := fun j : ℤ => supportedValue J (c+s*j)
  let W := fun j : ℤ => coeffGaussian ((v:ℝ)+(M:ℝ)*j) μ t
  let P := coeffGaussian x (lineCenter n a) (projectionScale n a)
  have mp := (R.subprod_bounds (s := R.miss a) Finset.sdiff_subset).1
  have bounds := R.probability_scales cap
  have mass := R.second_event_weight big target am different side u v ok
  have prob := conditional_progression_probability v M μ t (by dsimp [M]; exact_mod_cast mp) bounds.2.1 E
  have ev (j : ℤ) : R.intercept a' side (x-a*y j) (y j)=c+s*j := by
    have h := R.second_quotient target a a' side u v ok j
    change markSign n a' side*affineValue n ell a' side (x-a*y j+(a':ℤ)*y j)/(R.prefactor a' side:ℤ)=_
    rw [show x-a*y j+(a':ℤ)*y j = u+a'*v+((a':ℤ)-a)*prodPrimes (R.miss a)*j by dsimp [x,y,M];ring]
    exact h
  have gz (j : ℤ) : coefficientWeight n (x-a*y j,y j)=P*W j := by
    rw [coefficient_weight_projection]
    simp only [P,W,μ,t,y,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  have z : 0<∑' j,W j := prob.1
  have pn : 0<P := exp_pos _
  have mn : 0≤(M:ℝ)/t*(∑' j, if E j then W j else 0) := by
    have tp : 0<t := by have := bounds.2.1; change 2≤t/(M:ℝ) at this; exact (div_pos_iff_of_pos_right (show 0<(M:ℝ) by dsimp [M]; exact_mod_cast mp)).mp (by linarith)
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) tp.le) (tsum_nonneg (fun j => by split <;> first | exact (exp_pos _).le | rfl))
  let m := (scalarMass J c s (conditionalMean n ell a a' side x/(R.prefactor a' side:ℝ)) (twoWidth n ell a a'/(R.prefactor a' side:ℝ))).re
  dsimp only
  change 0<(∑' j : ℤ, coefficientWeight n (x-a*y j,y j)) ∧
    |(∑' j : ℤ, if supportedValue J (R.intercept a' side (x-a*y j) (y j)) then coefficientWeight n (x-a*y j,y j) else 0)/
      (∑' j : ℤ, coefficientWeight n (x-a*y j,y j))-m| ≤ 6*exp (-(Fixed.U (n.log2+1):ℝ))*m
  simp_rw [gz,ev]
  dsimp only [m]
  rw [mass,Complex.ofReal_re,tsum_mul_left]
  refine ⟨mul_pos pn z,?_⟩
  simp_rw [←mul_ite_zero,tsum_mul_left]
  rw [mul_div_mul_left _ _ pn.ne']
  exact prob.2.trans (mul_le_mul_of_nonneg_right bounds.2.2.2 mn)

/-- The actual Gaussian probability of the first prescribed finite event
    is given by the scalar window, uniformly over all roots and both signs. -/
theorem PrescribedRows.first_finite_probability {n ell a : ℕ} (R : PrescribedRows n ell)
    (big : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a≤Fixed.A (n.log2+1)) (am : a<Fixed.rootBase n) (side : Bool) :
    let pre : ℝ := R.prefactor a side
    ∃ u v : ℤ, R.compatible side u v ∧ ∀ A : Finset ℕ,
      let E := fun k : ℤ×ℤ => finiteValue A (R.intercept a side k.1 k.2)
      let c := R.intercept a side u v; let s := firstStep n ell a side
      let m := (finiteScalarMass A c s (exactMean n ell a side/pre) (oneWidth n ell a/pre)).re
      |prescribedProbability R side E-m| ≤ 90*exp (-(Fixed.U (n.log2+1):ℝ))*m := by
  classical
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let pre : ℝ := R.prefactor a side
  let H := R.hitProduct a; let M := prodPrimes (R.miss a)
  let S := projectionScale n a; let T := conditionalScale n a; let μ := (lineCenter n a:ℝ)
  obtain ⟨c,r,e,coords,ws,zp,_,events⟩ := R.coefficient_law target side cap
  let x := fun i : ℤ => c+(H:ℤ)*i
  let y := fun i j : ℤ => r i+(M:ℤ)*j
  let k₀ := (e (0,0)).val
  let F := R.intercept a side k₀.1 k₀.2; let s := firstStep n ell a side
  let W := fun k : ℤ×ℤ => coeffGaussian (x k.1) μ S*coeffGaussian (y k.1 k.2)
    (projectedConditionalCenter n a (x k.1)) T
  have pos (k : ℤ×ℤ) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  have Wsum : Summable W := ws
  have cc (k : ℤ×ℤ) : (e k).val=(x k.1-a*y k.1 k.2,y k.1 k.2) := coords _ _
  have orig : k₀.1+a*k₀.2=c := by dsimp [k₀]; rw [cc]; simp [x]
  have ok : R.compatible side k₀.1 k₀.2 := (e (0,0)).property
  refine ⟨k₀.1,k₀.2,ok,?_⟩
  intro A
  let E := fun k : ℤ×ℤ => finiteValue A (R.intercept a side k.1 k.2)
  let good := fun i : ℤ => finiteValue A (F+s*i)
  have wb (k : ℤ×ℤ) : coefficientWeight n (e k).val=W k := by rw [cc]; exact coefficient_weight_projection ..
  have Z := (e.tsum_eq (fun k : C => coefficientWeight n k.val)).symm.trans (tsum_congr wb)
  have eq (i j : ℤ) : R.intercept a side (x i-a*y i j) (y i j)=F+s*i := by
    have h := R.first_quotient target a side k₀.1 k₀.2 ok i
    rw [orig] at h
    change markSign n a side*affineValue n ell a side (x i-a*y i j+a*y i j)/(R.prefactor a side:ℤ)=_
    rw [sub_add_cancel]
    exact h
  have numerator := events E
  change prescribedProbability R side E = (∑' k : ℤ×ℤ, if E (x k.1-a*y k.1 k.2,y k.1 k.2)
    then W k else 0)/(∑' k : C, coefficientWeight n k.val) at numerator
  have unpack : prescribedProbability R side E = (∑' i : ℤ, if good i then ∑' j : ℤ, W (i,j) else 0)/
      (∑' i : ℤ, ∑' j : ℤ,W (i,j)) := by
    rw [numerator,Z,Wsum.tsum_prod]
    congr 1
    let V := fun k : ℤ×ℤ => if good k.1 then W k else 0
    have vs : Summable V := Summable.of_nonneg_of_le (fun k => by dsimp only [V]; split <;> first | exact pos k | rfl)
      (fun k => by dsimp only [V]; split <;> first | exact pos k | rfl) Wsum
    calc _=(∑' k, V k) := tsum_congr (fun k => by simp only [V,E,good,eq])
         _= _ := by rw [vs.tsum_prod]; apply tsum_congr; intro i; by_cases g : good i <;> simp [V,g]
  have sm := R.first_finite_event_weight A big target am side k₀.1 k₀.2 ok
  rw [orig] at sm
  let m := (finiteScalarMass A F s (exactMean n ell a side/pre) (oneWidth n ell a/pre)).re
  have mEq : m=(H:ℝ)/S*(∑' i : ℤ,if good i then coeffGaussian ((c:ℝ)+(H:ℝ)*i) μ S else 0) := by
    exact congrArg Complex.re sm
  have bounds := R.probability_scales cap
  have hp : 0<(H:ℝ) := by dsimp only [H,hitProduct,hit]; exact_mod_cast (R.subprod_bounds (Finset.filter_subset (fun q => (R.residue q:ZMod q)=a) R.primes)).1
  have mp : 0<(M:ℝ) := by dsimp only [M]; exact_mod_cast (R.subprod_bounds (s := R.miss a) Finset.sdiff_subset).1
  have marg := gaussian_first_marginal c H S M T μ (fun i => (r i:ℝ)) (fun i => projectedConditionalCenter n a (x i))
    hp mp bounds.1 bounds.2.1 good
  have sp : 0<S := by dsimp [S,projectionScale,Fixed.A,Fixed.U]; positivity
  have mn : 0 ≤ m := by rw [mEq]; exact mul_nonneg (div_nonneg hp.le sp.le) (tsum_nonneg (fun i => by split <;> first | exact (exp_pos _).le | rfl))
  change |prescribedProbability R side E-m|≤90*exp (-(Fixed.U (n.log2+1):ℝ))*m
  rw [unpack]
  apply le_trans _ (mul_le_mul_of_nonneg_right bounds.2.2.1 mn)
  rw [mEq]
  simpa only [W,x,y,Int.cast_add,Int.cast_mul,Int.cast_natCast] using marg

theorem PrescribedRows.first_band_probability {n ell a : ℕ} (R : PrescribedRows n ell)
    (big : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a≤Fixed.A (n.log2+1)) (am : a<Fixed.rootBase n) (side : Bool) :
    let pre : ℝ := R.prefactor a side
    ∃ u v : ℤ, R.compatible side u v ∧ ∀ J : Finset ℕ,
      let E := fun k : ℤ×ℤ => supportedValue J (R.intercept a side k.1 k.2)
      let c := R.intercept a side u v; let s := firstStep n ell a side
      let m := (scalarMass J c s (exactMean n ell a side/pre) (oneWidth n ell a/pre)).re
      |prescribedProbability R side E-m| ≤ 90*exp (-(Fixed.U (n.log2+1):ℝ))*m := by
  obtain ⟨u,v,ok,estimate⟩ := R.first_finite_probability big target cap am side
  exact ⟨u,v,ok,fun J => estimate (squarefreeSupport J)⟩

theorem PrescribedRows.first_probability {n ell a : ℕ} (R : PrescribedRows n ell)
    (big : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a≤Fixed.A (n.log2+1)) (am : a<Fixed.rootBase n) (side : Bool) :
    let J := sieveBand n ell (R.prefactor a side); let pre : ℝ := R.prefactor a side
    let E := fun k : ℤ×ℤ => supportedValue J (R.intercept a side k.1 k.2)
    ∃ u v : ℤ, R.compatible side u v ∧
      let c := R.intercept a side u v; let s := firstStep n ell a side
      let m := (scalarMass J c s (exactMean n ell a side/pre) (oneWidth n ell a/pre)).re
      |prescribedProbability R side E-m| ≤ 90*exp (-(Fixed.U (n.log2+1):ℝ))*m := by
  obtain ⟨u,v,ok,estimate⟩ := R.first_band_probability big target cap am side
  exact ⟨u,v,ok,estimate _⟩

end
end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.second_probability

#print axioms Cogentic.Construction.PrescribedRows.first_probability
