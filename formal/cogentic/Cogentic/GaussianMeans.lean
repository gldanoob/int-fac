import Cogentic.WindowScales
import Cogentic.SaddleConstructionScale

namespace Cogentic.Construction

/-- The common base for all fixed dyadic parameters. -/
def dyadicUnit (b : ℕ) : ℕ := 2^Fixed.h b

theorem dyadic_data {b : ℕ} (bp : 0 < b) :
    let x := dyadicUnit b; let d := Fixed.d b
    2 ≤ x ∧ b ≤ x ∧ Fixed.K₁ b = x^100 ∧ Fixed.B b = x^1000 ∧
      Fixed.A b = x^10000 ∧ Fixed.U b = x^(100000*d) ∧ 2^(8*Fixed.v b) = x^(8*d) := by
  let h := Fixed.h b
  let d := Fixed.d b
  have dp := Fixed.degree_pos bp
  have zp : 0 < Fixed.z b := Nat.succ_pos _
  have hp : 0 < h := Nat.mul_pos dp zp
  have zh : Fixed.z b ≤ h := Nat.le_mul_of_pos_left _ dp
  refine ⟨Nat.pow_le_pow_right (n := 2) (i := 1) (by decide) hp, Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) zh),?_⟩
  simp only [Fixed.K₁,Fixed.B,Fixed.beta,Fixed.A,Fixed.U,Fixed.v,dyadicUnit,←Nat.pow_mul]
  constructor <;> first | exact congrArg (2^·) (by ring) | skip
  constructor <;> first | exact congrArg (2^·) (by ring) | skip
  constructor <;> first | exact congrArg (2^·) (by ring) | skip
  constructor <;> exact congrArg (2^·) (by ring)

def meanPolynomial (n ell : ℕ) (side : Bool) : List ℤ :=
  let b := n.log2+1; let d := Fixed.d b; let A := Fixed.A b
  let P := primorial d; let m := Fixed.rootBase n; let c := leadingCoefficient n
  perturb (P*ell) m (b^2*Fixed.U b*A) (b^2*Fixed.U b)
    (corrected n m (P*ell) c (preliminary d A m P ell c side))

def idealAt (n a : ℕ) (side : Bool) : ℚ :=
  let b := n.log2+1
  idealValue (Fixed.d b) side ((a:ℚ)/Fixed.A b)

def orientation (n a : ℕ) (side : Bool) : ℚ := if idealAt n a side < 0 then -1 else 1

/-- Mean obtained by evaluating the constructed polynomial at the center
    of its coefficient distribution with the sign of the ideal value. -/
def exactMean (n ell a : ℕ) (side : Bool) : ℚ :=
  let b := n.log2+1
  orientation n a side * RootLogs.normalized (Fixed.A b) (meanPolynomial n ell side) ((a:ℚ)/Fixed.A b)

theorem mean_polynomial_is_constructed (n ell : ℕ) :
    let b := n.log2+1; let a := b^2*Fixed.U b*Fixed.A b; let z := b^2*Fixed.U b
    let p := construct n ell a z a z
    p.first = meanPolynomial n ell false ∧ p.second = meanPolynomial n ell true := ⟨rfl,rfl⟩

/-- Shape of the two-dimensional coefficient Gaussian projected along (1,a). -/
noncomputable def projectionScale (n a : ℕ) : ℝ :=
  let b := n.log2+1; let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b
  Real.sqrt ((U*A)^2+((a:ℝ)*U)^2)

noncomputable def oneWidth (n ell a : ℕ) : ℝ :=
  let b := n.log2+1
  (primorial (Fixed.d b):ℝ)*ell*|(a:ℝ)-Fixed.rootBase n| * projectionScale n a

noncomputable def twoWidth (n ell a a' : ℕ) : ℝ :=
  let b := n.log2+1; let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b
  (primorial (Fixed.d b):ℝ)*ell*|(a':ℝ)-Fixed.rootBase n| * |(a':ℝ)-a| * (U*A*U/projectionScale n a)

def lineCenter (n a : ℕ) : ℕ :=
  let b := n.log2+1
  b^2*Fixed.U b*Fixed.A b+a*(b^2*Fixed.U b)

/-- Conditional mean of the second projection after observing the first. -/
noncomputable def conditionalMean (n ell a a' : ℕ) (side : Bool) (observed : ℝ) : ℝ :=
  let b := n.log2+1; let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b
  exactMean n ell a' side + (orientation n a' side:ℝ)*(primorial (Fixed.d b):ℝ)*ell*((a':ℝ)-Fixed.rootBase n)*
    (((U*A)^2+(a:ℝ)*a'*U^2)/(projectionScale n a)^2)*(observed-lineCenter n a)

theorem exact_center_error {n ell a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (cap : a ≤ Fixed.A (n.log2+1)) (side : Bool) :
    abs ((exactMean n ell a side:ℝ)-(amplitude n:ℝ)*|(idealAt n a side:ℝ)|) ≤
      amplitude n/(Fixed.K₁ (n.log2+1):ℝ) := by
  let b := n.log2+1; let A := Fixed.A b
  have ap : 0<A := Nat.pow_pos (by decide)
  have raw := normalized_error hn big target side (a := b^2*Fixed.U b*A) (z := b^2*Fixed.U b)
    ⟨by change _ ≤ 2*b^2*Fixed.U b*A; rw [Nat.mul_assoc 2, Nat.mul_assoc 2]; omega,
      by change _ ≤ 2*b^2*Fixed.U b; rw [Nat.mul_assoc 2]; omega⟩ ((a:ℚ)/A)
    (by rw [abs_of_nonneg (by positivity)]; exact (div_le_one (by exact_mod_cast ap)).mpr (by exact_mod_cast cap))
  have amp : (amplitude n:ℚ) = leadingCoefficient n*(A:ℚ)^Fixed.d b := by simp [amplitude,b,A]
  dsimp only at raw
  rw [←amp] at raw
  change |RootLogs.normalized A (meanPolynomial n ell side) ((a:ℚ)/A)-(amplitude n:ℚ)*idealAt n a side| ≤ _ at raw
  have signed : abs (exactMean n ell a side-(amplitude n:ℚ)*|idealAt n a side|) ≤ amplitude n/(Fixed.K₁ b:ℚ) := by
    by_cases neg : idealAt n a side < 0
    · rw [exactMean,orientation,if_pos neg,neg_one_mul,abs_of_neg neg,mul_neg,sub_neg_eq_add,
        show -(RootLogs.normalized A (meanPolynomial n ell side) ((a:ℚ)/A))+(amplitude n:ℚ)*idealAt n a side =
          -(RootLogs.normalized A (meanPolynomial n ell side) ((a:ℚ)/A)-(amplitude n:ℚ)*idealAt n a side) by ring,abs_neg]
      exact raw
    · simpa [exactMean,orientation,neg,abs_of_nonneg (le_of_not_gt neg),b,A] using raw
  have cast := (Rat.cast_le (K := ℝ)).mpr signed
  push_cast at cast
  exact cast

private theorem projected_scale_bounds {n a : ℕ} (cap : a ≤ Fixed.A (n.log2+1)) :
    let b := n.log2+1; let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b
    U*A ≤ projectionScale n a ∧ projectionScale n a ≤ 2*(U*A) := by
  intro b U A
  have Up : 0 ≤ U := by dsimp [U]; positivity
  have Ap : 0 ≤ A := by dsimp [A]; positivity
  have ap : 0 ≤ (a:ℝ) := Nat.cast_nonneg _
  have au : (a:ℝ)*U ≤ U*A := (mul_le_mul_of_nonneg_right (by change (a:ℝ) ≤ (Fixed.A b:ℝ); exact_mod_cast cap : (a:ℝ) ≤ A) Up).trans_eq (mul_comm ..)
  have sq := pow_le_pow_left₀ (mul_nonneg ap Up) au 2
  have pos := Real.sqrt_nonneg ((U*A)^2+((a:ℝ)*U)^2)
  have eq := Real.sq_sqrt (show 0 ≤ (U*A)^2+((a:ℝ)*U)^2 by positivity)
  change U*A ≤ Real.sqrt _ ∧ Real.sqrt _ ≤ 2*(U*A)
  constructor <;> nlinarith [mul_nonneg Up Ap,sq_nonneg ((a:ℝ)*U),sq_nonneg (U*A)]

private theorem reference_bounds {n : ℕ} (hn : 2 ≤ n) :
    let b := n.log2+1; let d := Fixed.d b; let x := dyadicUnit b
    x^(100000*d) ≤ referenceWidth n ∧ referenceWidth n ≤ x^(100008*d+11002) := by
  let b := n.log2+1
  let d := Fixed.d b
  let x := dyadicUnit b
  let P := primorial d
  have ⟨xp,_,_,B,A,U,m⟩ := dyadic_data (b := b) (Nat.succ_pos _)
  have zp : 0 < Fixed.z b := Nat.succ_pos _
  have dp := Fixed.degree_pos (b := b) (Nat.succ_pos _)
  have dh : d ≤ Fixed.h b := Nat.le_mul_of_pos_right _ zp
  have pp : 0<P := primorial_pos _
  have mp : 0<Fixed.rootBase n := by simp [Fixed.rootBase]
  have Bp : 0<Fixed.B b := Nat.pow_pos (by decide)
  have Ap : 0<Fixed.A b := Nat.pow_pos (by decide)
  have ppow : P ≤ x^2 := by
    apply (primorial_le_four_pow _).trans
    change (2^2)^d ≤ (2^Fixed.h b)^2
    rw [←Nat.pow_mul,←Nat.pow_mul,Nat.mul_comm (Fixed.h b) 2]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ dh)
  have mpow := (rootBase_bound hn).trans_eq m
  constructor
  · rw [←U]
    exact (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos pp Bp) mp)).trans (Nat.le_mul_of_pos_right _ Ap)
  · have h := Nat.mul_le_mul_right (Fixed.A b) (Nat.mul_le_mul_right (Fixed.U b)
        (Nat.mul_le_mul (Nat.mul_le_mul_right (Fixed.B b) ppow) mpow))
    change P*Fixed.B b*Fixed.rootBase n*Fixed.U b*Fixed.A b ≤ _
    apply h.trans_eq
    rw [A,B,U,←Nat.pow_add,←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]
    congr 1; ring

private theorem width_factors {n ell a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (cap : a ≤ Fixed.A (n.log2+1)) :
    let b := n.log2+1; let P : ℝ := primorial (Fixed.d b); let m : ℝ := Fixed.rootBase n
    let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b; let B : ℝ := Fixed.B b
    P*B*m/4 ≤ P*ell*|(a:ℝ)-m| ∧ P*ell*|(a:ℝ)-m| ≤ P*B*m ∧
      U*A ≤ projectionScale n a ∧ projectionScale n a ≤ 2*(U*A) := by
  intro b P m U A B
  let d := Fixed.d b
  have dp : 0<d := by change 10004 ≤ d at big; omega
  have ap : 0 < Fixed.A b := Nat.pow_pos (by decide)
  have hp : 0 < Fixed.h b := Nat.mul_pos dp (Nat.succ_pos _)
  have bet : 0<Fixed.beta b := by change 0<1000*Fixed.h b; omega
  have bp : 0 < B := by change 0 < (Fixed.B b:ℝ); exact_mod_cast Nat.pow_pos (by decide : 0 < 2) (n := Fixed.beta b)
  have ep : 0 ≤ (ell:ℝ) := Nat.cast_nonneg _
  have pp : 0 ≤ P := by dsimp [P]; positivity
  have mr := (Fixed.stage_guards hn big).markRange
  have halfa : 2*a ≤ Fixed.rootBase n := by
    apply (Nat.mul_le_mul_left 2 cap).trans
    exact (Nat.mul_le_mul_right (Fixed.A b) (by omega : 2 ≤ 4*d)).trans mr
  have halfR : 2*(a:ℝ) ≤ m := by change 2*(a:ℝ) ≤ (Fixed.rootBase n:ℝ); exact_mod_cast halfa
  have delta : |(a:ℝ)-m| = m-a := abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) a]) |>.trans (by ring)
  have gapL : m/2 ≤ m-a := by linarith
  have gapU : m-a ≤ m := by linarith [Nat.cast_nonneg (α := ℝ) a]
  have lower := (mem_dyadicTargets.mp target).2.1
  have upper := (mem_dyadicTargets.mp target).2.2
  change 2^(Fixed.beta b-1)<ell at lower
  have B2 : Fixed.B b = 2^(Fixed.beta b-1)*2 := by
    change 2^Fixed.beta b = _
    conv_lhs => rw [show Fixed.beta b = (Fixed.beta b-1)+1 by omega,pow_succ]
  have LE : B/2 ≤ ell := by
    have nat : Fixed.B b ≤ 2*ell := B2 ▸ (by omega)
    have real : B ≤ 2*(ell:ℝ) := by dsimp [B]; exact_mod_cast nat
    linarith
  have UE : (ell:ℝ) ≤ B := by dsimp [B]; exact_mod_cast upper
  rw [delta]
  have mpos : 0 ≤ m := by dsimp [m]; positivity
  have lo := mul_le_mul (mul_le_mul_of_nonneg_left LE pp) gapL (by linarith : 0 ≤ m/2) (mul_nonneg pp ep)
  have hi := mul_le_mul (mul_le_mul_of_nonneg_left UE pp) gapU (by linarith) (mul_nonneg pp bp.le)
  exact ⟨by linarith,hi,projected_scale_bounds cap⟩

private theorem one_width_bounds {n ell a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (cap : a ≤ Fixed.A (n.log2+1)) :
    (referenceWidth n:ℝ)/4 ≤ oneWidth n ell a ∧ oneWidth n ell a ≤ 2*referenceWidth n := by
  obtain ⟨lo,hi,low,high⟩ := width_factors hn big target cap
  have small := mul_le_mul lo low (show (0:ℝ) ≤ Fixed.U (n.log2+1)* (Fixed.A (n.log2+1):ℝ) by positivity) (by positivity)
  have large := mul_le_mul hi high (Real.sqrt_nonneg _) (by positivity)
  dsimp [oneWidth,referenceWidth]
  push_cast
  constructor <;> linarith

private theorem two_width_bounds {n ell a a' : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a ≤ Fixed.A (n.log2+1)) (cap' : a' ≤ Fixed.A (n.log2+1))
    (clean : (Fixed.A (n.log2+1):ℝ) ≤ |(a':ℝ)-a| * (dyadicUnit (n.log2+1):ℝ)^50) :
    let x : ℝ := dyadicUnit (n.log2+1)
    (referenceWidth n:ℝ)/(8*x^50) ≤ twoWidth n ell a a' ∧ twoWidth n ell a a' ≤ 2*referenceWidth n := by
  let b := n.log2+1
  let U : ℝ := Fixed.U b
  let A : ℝ := Fixed.A b
  let P : ℝ := primorial (Fixed.d b)
  let B : ℝ := Fixed.B b
  let m : ℝ := Fixed.rootBase n
  let x : ℝ := dyadicUnit b
  let e := |(a':ℝ)-a|
  let V := P*ell*|(a':ℝ)-m|
  let S := projectionScale n a
  have ⟨vLo,vHi,_,_⟩ := width_factors hn big target cap'
  change P*B*m/4 ≤ V at vLo
  change V ≤ P*B*m at vHi
  have ⟨sLo,sHi⟩ := projected_scale_bounds cap
  change U*A ≤ S at sLo
  change S ≤ 2*(U*A) at sHi
  have up : 0 < U := by dsimp [U,Fixed.U]; positivity
  have ap : 0 < A := by dsimp [A,Fixed.A]; positivity
  have xp : 0 < x := by dsimp [x,dyadicUnit]; positivity
  have vp : 0 ≤ V := by dsimp [V,P]; positivity
  have ep : 0 ≤ e := abs_nonneg _
  have sp := (mul_pos up ap).trans_le sLo
  have elo : A ≤ e*x^50 := clean
  have ehi : e ≤ A := by
    have a1 : (a:ℝ) ≤ A := by dsimp [A]; exact_mod_cast cap
    have a2 : (a':ℝ) ≤ A := by dsimp [A]; exact_mod_cast cap'
    exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) a'],by linarith [Nat.cast_nonneg (α := ℝ) a]⟩
  have ulo : U/2 ≤ U*A*U/S :=
    (le_div_iff₀ sp).mpr (by linarith [mul_le_mul_of_nonneg_right sHi up.le])
  have uhi : U*A*U/S ≤ U :=
    (div_le_iff₀ sp).mpr (by linarith [mul_le_mul_of_nonneg_right sLo up.le])
  have size : (referenceWidth n:ℝ) = P*B*m*U*A := by simp [referenceWidth,b,P,B,m,U,A]
  change (referenceWidth n:ℝ)/(8*x^50) ≤ V*e*(U*A*U/S) ∧ V*e*(U*A*U/S) ≤ 2*referenceWidth n
  rw [size]
  have nonneg : 0 ≤ P*B*m := by dsimp [P,B,m]; positivity
  have low := mul_le_mul (mul_le_mul vLo elo ap.le vp) ulo (by linarith) (mul_nonneg vp (mul_nonneg ep (pow_nonneg xp.le _)))
  have high := mul_le_mul (mul_le_mul vHi ehi ep nonneg) uhi (by positivity) (mul_nonneg nonneg ap.le)
  refine ⟨(div_le_iff₀ (by positivity)).mpr (by linarith),?_⟩
  linarith [mul_nonneg (mul_nonneg nonneg up.le) ap.le]

theorem conditional_center_error {n ell a a' : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a ≤ Fixed.A (n.log2+1)) (cap' : a' ≤ Fixed.A (n.log2+1)) (side : Bool) (observed : ℝ)
    (central : |observed-lineCenter n a| ≤ ((n.log2+1:ℕ):ℝ)^3*projectionScale n a) :
    |conditionalMean n ell a a' side observed - (exactMean n ell a' side:ℝ)| ≤
      4*((n.log2+1:ℕ):ℝ)^3*referenceWidth n := by
  let b := n.log2+1
  let U : ℝ := Fixed.U b
  let A : ℝ := Fixed.A b
  let P : ℝ := primorial (Fixed.d b)
  let B : ℝ := Fixed.B b
  let m : ℝ := Fixed.rootBase n
  let V := P*ell*|(a':ℝ)-m|
  let N := (U*A)^2+(a:ℝ)*a'*U^2
  let S := projectionScale n a
  have ⟨_,vHi,_,_⟩ := width_factors hn big target cap'
  change V ≤ P*B*m at vHi
  have ⟨sLo,sHi⟩ := projected_scale_bounds cap
  change U*A ≤ S at sLo
  change S ≤ 2*(U*A) at sHi
  have up : 0 < U := by dsimp [U,Fixed.U]; positivity
  have ap : 0 < A := by dsimp [A,Fixed.A]; positivity
  have sp := (mul_pos up ap).trans_le sLo
  have ap1 : (a:ℝ) ≤ A := by dsimp [A]; exact_mod_cast cap
  have ap2 : (a':ℝ) ≤ A := by dsimp [A]; exact_mod_cast cap'
  have aa := mul_le_mul ap1 ap2 (Nat.cast_nonneg (α := ℝ) _) ap.le
  have nLim : N ≤ 2*S^2 := by
    dsimp only [N]
    nlinarith [mul_le_mul_of_nonneg_right aa (sq_nonneg U),pow_le_pow_left₀ (mul_nonneg up.le ap.le) sLo 2]
  have ratio : |N/S^2| ≤ 2 := by
    rw [abs_of_nonneg (by dsimp [N]; positivity)]
    exact (div_le_iff₀ (by positivity)).mpr nLim
  have sign : |(orientation n a' side:ℝ)| = 1 := by unfold orientation; split <;> norm_num
  have vabs : |(orientation n a' side:ℝ)*P*ell*((a':ℝ)-m)| = V := by
    simp [abs_mul,sign,abs_of_nonneg (show 0 ≤ P by dsimp [P]; positivity),V]
  have size : (referenceWidth n:ℝ) = P*B*m*U*A := by simp [referenceWidth,b,P,B,m,U,A]
  have cp : 0 ≤ ((b:ℝ)^3) := by positivity
  have pb : 0 ≤ P*B*m := by dsimp [P,B,m]; positivity
  have step := mul_le_mul_of_nonneg_left sHi cp
  have delta := central.trans step
  change |((exactMean n ell a' side:ℝ)+(orientation n a' side:ℝ)*P*ell*((a':ℝ)-m)*(N/S^2)*(observed-lineCenter n a))-
      (exactMean n ell a' side:ℝ)| ≤ 4*(b:ℝ)^3*referenceWidth n
  rw [add_sub_cancel_left,abs_mul,abs_mul,vabs,size]
  have h := mul_le_mul (mul_le_mul vHi ratio (abs_nonneg _) pb) delta (abs_nonneg _)
    (mul_nonneg pb (by norm_num))
  linarith

theorem centered_envelope {n ell a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (cap : a ≤ Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (side : Bool) (Y : ℝ) (shift : |Y-(exactMean n ell a side:ℝ)| ≤ 4*((n.log2+1:ℕ):ℝ)^3*referenceWidth n) :
    let b := n.log2+1; let x : ℝ := dyadicUnit b
    (amplitude n:ℝ)/(2*x^4) ≤ Y ∧ Y ≤ 2*amplitude n := by
  let b := n.log2+1
  let x : ℝ := dyadicUnit b
  let W : ℝ := referenceWidth n
  let X : ℝ := amplitude n
  have ⟨xx,bx,k,_,_,_,_⟩ := dyadic_data (b := b) (Nat.succ_pos _)
  have two : (2:ℝ) ≤ x := by dsimp [x]; exact_mod_cast xx
  have b1 : (1:ℝ) ≤ b := by exact_mod_cast Nat.succ_pos n.log2
  have bp : 0 < (b:ℝ) := by positivity
  have bxR : (b:ℝ) ≤ x := by dsimp [x]; exact_mod_cast bx
  have xp : 0 < x := by linarith
  have Wp : 0 ≤ W := by dsimp [W]; positivity
  have Xp : 0 ≤ X := by dsimp [X]; positivity
  have kR : (Fixed.K₁ b:ℝ) = x^100 := by dsimp [x]; exact_mod_cast k
  have lower : 6*x^100*(b:ℝ)^2*W ≤ X := by
    rw [←kR]; dsimp only [X,W]; exact_mod_cast (amplitude_compare hn big).1
  have ex := exact_center_error hn big target cap side
  change abs ((exactMean n ell a side:ℝ)-X*|(idealAt n a side:ℝ)|) ≤ X/(Fixed.K₁ b:ℝ) at ex
  rw [kR] at ex
  have g := grid_ideal_value hn big cap grid side
  have idealL : (x^4)⁻¹ ≤ |(idealAt n a side:ℝ)| := by
    have eq : (1/2:ℚ)^(4*Fixed.h b) = ((dyadicUnit b:ℚ)^4)⁻¹ := by
      simp only [dyadicUnit,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_pow,←pow_mul,Nat.mul_comm 4]
    have bound := g.1
    rw [eq] at bound
    have cast := (Rat.cast_le (K := ℝ)).mpr bound
    push_cast at cast
    exact cast
  have idealH : |(idealAt n a side:ℝ)| ≤ 1 := by exact_mod_cast (Rat.cast_le (K := ℝ)).mpr g.2
  have errSmall : X/x^100 ≤ X/(4*x^4) := by
    apply div_le_div_of_nonneg_left Xp (by positivity)
    calc 4*x^4 ≤ x^2*x^4 := mul_le_mul_of_nonneg_right (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two 2]) (by positivity)
         _ = x^6 := by ring
         _ ≤ x^100 := pow_le_pow_right₀ (by linarith) (by decide)
  have shiftSmall : 4*(b:ℝ)^3*W ≤ X/(4*x^4) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have c : 16 ≤ x^4 := by
      have c4 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two 4
      norm_num at c4; exact c4
    have u : 16*(b:ℝ)*x^4 ≤ 6*x^100 := by
      calc 16*(b:ℝ)*x^4 ≤ x^4*x*x^4 := mul_le_mul_of_nonneg_right (mul_le_mul c bxR bp.le (by positivity)) (by positivity)
           _ = x^9 := by ring
           _ ≤ x^100 := pow_le_pow_right₀ (by linarith) (by decide)
           _ ≤ _ := by linarith [pow_nonneg xp.le 100]
    have q := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right u (sq_nonneg (b:ℝ))) Wp
    linarith
  have small := abs_le.mp (ex.trans errSmall)
  have sh := abs_le.mp (shift.trans shiftSmall)
  have gl := mul_le_mul_of_nonneg_left idealL Xp
  have gu := mul_le_mul_of_nonneg_left idealH Xp
  have eq1 : X*(x^4)⁻¹ = X/x^4 := by ring
  rw [eq1] at gl
  have eq2 : X/(4*x^4) = (X/x^4)/4 := by ring
  rw [eq2] at small sh
  have eq3 : X/(2*x^4) = (X/x^4)/2 := by ring
  have Xdiv : X/x^4 ≤ X := div_le_self Xp (one_le_pow₀ (by linarith))
  change X/(2*x^4) ≤ Y ∧ Y ≤ 2*X
  rw [eq3]
  constructor <;> linarith

/-- The numerical window parameters consumed by the saddle and contour bounds. -/
def InWindow (b : ℕ) (Y S : ℝ) : Prop :=
  0 < S ∧ 1 ≤ Y ∧
  90*(Fixed.d b:ℝ) ≤ Real.log Y/Real.log (Fixed.B b) ∧
  Real.log Y/Real.log (Fixed.B b) ≤ 110*(Fixed.d b:ℝ) ∧
  (Fixed.B b:ℝ)^(17/200:ℝ) ≤ Y/S ∧ Y/S ≤ (Fixed.B b:ℝ)^(17/100:ℝ) ∧
  Y/S ≤ Y^(1/2000:ℝ)

private theorem upper_exponent (d : ℕ) (big : 10004 ≤ d) : 7+100+2+(100008*d+11002) ≤ 110000*d := by
  calc _ = 100008*d+11111 := by ring
       _ ≤ 100008*d+9992*d := Nat.add_le_add_left ((by decide : 11111 ≤ 9992*2).trans (Nat.mul_le_mul_left _ (by omega : 2≤d))) _
       _ = _ := by ring

private theorem divided_window {n : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (Y S D : ℝ) (divisor : 1 ≤ D ∧ D ≤ (Fixed.A (n.log2+1):ℝ)*(Fixed.B (n.log2+1):ℝ)^40)
    (mean : let x : ℝ := dyadicUnit (n.log2+1); (amplitude n:ℝ)/(2*x^4) ≤ Y ∧ Y ≤ 2*amplitude n)
    (scale : let x : ℝ := dyadicUnit (n.log2+1); (referenceWidth n:ℝ)/(8*x^50) ≤ S ∧ S ≤ 2*referenceWidth n) :
    InWindow (n.log2+1) (Y/D) (S/D) := by
  let b := n.log2+1; let d := Fixed.d b; let x : ℝ := dyadicUnit b
  let W : ℝ := referenceWidth n; let X : ℝ := amplitude n
  have ⟨xx,bx,k,B,A,_,_⟩ := dyadic_data (b := b) (Nat.succ_pos _)
  have dg : 10004 ≤ d := big
  have dp : 0 < d := by omega
  have hp : 0 < Fixed.h b := Nat.mul_pos dp (Nat.succ_pos _)
  have two : (2:ℝ) ≤ x := by dsimp [x]; exact_mod_cast xx
  have bxR : (b:ℝ) ≤ x := by dsimp [x]; exact_mod_cast bx
  have one : (1:ℝ) ≤ b := by exact_mod_cast Nat.succ_pos n.log2
  have b2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) one 2
  have B2 := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) b) bxR 2
  have xp : 0 < x := by linarith
  have xone : 1 ≤ x := by linarith
  have kR : (Fixed.K₁ b:ℝ) = x^100 := by dsimp [x]; exact_mod_cast k
  have BR : (Fixed.B b:ℝ) = x^1000 := by dsimp [x]; exact_mod_cast B
  have AR : (Fixed.A b:ℝ) = x^10000 := by dsimp [x]; exact_mod_cast A
  have wl : x^(100000*d) ≤ W := by dsimp [x,W]; exact_mod_cast (reference_bounds hn).1
  have wh : W ≤ x^(100008*d+11002) := by dsimp [x,W]; exact_mod_cast (reference_bounds hn).2
  have wp := (pow_pos xp (100000*d)).trans_le wl
  have xl : 6*x^100*(b:ℝ)^2*W ≤ X := by
    rw [←kR]; dsimp only [W,X]; exact_mod_cast (amplitude_compare hn big).1
  have xh : X ≤ 54*x^100*(b:ℝ)^2*W := by
    rw [←kR]; dsimp only [W,X]; exact_mod_cast (amplitude_compare hn big).2
  have xw : W ≤ X := by
    have oneX := one_le_pow₀ xone (n := 100)
    have aa : 1 ≤ x^100*(b:ℝ)^2 := one_le_mul_of_one_le_of_one_le oneX (by linarith)
    exact (le_mul_of_one_le_left wp.le (by linarith : 1 ≤ 6*x^100*(b:ℝ)^2)).trans xl
  have Dp : 0 < D := by linarith [divisor.1]
  have Dlow := divisor.1
  have Dhi := divisor.2
  rw [AR,BR,←pow_mul,←pow_add] at Dhi
  change D ≤ x^50000 at Dhi
  change X/(2*x^4) ≤ Y ∧ Y ≤ 2*X at mean
  change W/(8*x^50) ≤ S ∧ S ≤ 2*W at scale
  have sp := (div_pos wp (by positivity : 0<8*x^50)).trans_le scale.1
  have yp := (div_pos (wp.trans_le xw) (by positivity : 0<2*x^4)).trans_le mean.1
  have lower : x^(90000*d) ≤ Y/D := by
    apply (le_div_iff₀ Dp).mpr
    apply le_trans ?_ mean.1
    apply (le_div_iff₀ (by positivity)).mpr
    calc x^(90000*d)*D*(2*x^4) ≤ x^(90000*d)*x^50000*(x*x^4) :=
           mul_le_mul (mul_le_mul_of_nonneg_left Dhi (pow_nonneg xp.le _))
             (mul_le_mul_of_nonneg_right two (pow_nonneg xp.le _)) (by positivity) (by positivity)
         _ = x^(90000*d+50000+5) := by rw [pow_add,pow_add]; ring
         _ ≤ x^(100000*d) := pow_le_pow_right₀ xone (by omega)
         _ ≤ X := wl.trans xw
  have upper : Y/D ≤ x^(110000*d) := by
    apply (div_le_self yp.le Dlow).trans (mean.2.trans ?_)
    have c : (108:ℝ) ≤ x^7 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two 7; norm_num at this; linarith
    calc 2*X ≤ 108*x^100*(b:ℝ)^2*W := by linarith
         _ ≤ x^7*x^100*x^2*x^(100008*d+11002) :=
           mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right c (pow_nonneg xp.le _)) B2
             (sq_nonneg _) (by positivity)) wh wp.le (by positivity)
         _ = x^(7+100+2+(100008*d+11002)) := by rw [←pow_add,←pow_add,←pow_add]
         _ ≤ x^(110000*d) := pow_le_pow_right₀ xone (upper_exponent d dg)
  have same : (Y/D)/(S/D) = Y/S := by field_simp
  have wlo : x^85 ≤ (Y/D)/(S/D) := by
    rw [same]
    apply (le_div_iff₀ sp).mpr
    apply (mul_le_mul_of_nonneg_left scale.2 (pow_nonneg xp.le 85)).trans (le_trans ?_ mean.1)
    apply (le_div_iff₀ (by positivity)).mpr
    have p : x^(85+4) ≤ x^100 := pow_le_pow_right₀ xone (by decide)
    have q := le_mul_of_one_le_right (pow_nonneg xp.le 100) (show (1:ℝ) ≤ (b:ℝ)^2 by linarith)
    rw [pow_add] at p
    have h := mul_le_mul_of_nonneg_right (show 4*(x^85*x^4) ≤ 6*x^100*(b:ℝ)^2 by linarith [pow_nonneg xp.le 100]) wp.le
    linarith
  have whi : (Y/D)/(S/D) ≤ x^170 := by
    rw [same]
    apply (div_le_iff₀ sp).mpr
    apply mean.2.trans (le_trans ?_ (mul_le_mul_of_nonneg_left scale.1 (pow_nonneg xp.le 170)))
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (by positivity)).mpr
    have c : (864:ℝ) ≤ x^10 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two 10; norm_num at this; linarith
    have v : 864*x^100*(b:ℝ)^2*x^50 ≤ x^170 := by
      calc _ ≤ x^10*x^100*x^2*x^50 := mul_le_mul_of_nonneg_right
             (mul_le_mul (mul_le_mul_of_nonneg_right c (pow_nonneg xp.le _)) B2 (by positivity) (by positivity)) (pow_nonneg xp.le _)
           _ = x^(10+100+2+50) := by rw [←pow_add,←pow_add,←pow_add]
           _ ≤ x^170 := pow_le_pow_right₀ xone (by decide)
    have p := mul_le_mul_of_nonneg_right xh (pow_nonneg xp.le 50)
    linarith [mul_le_mul_of_nonneg_right v wp.le]
  have eq : x = (2:ℝ)^Fixed.h b := by simp [x,dyadicUnit]
  rw [eq] at lower upper wlo whi
  obtain ⟨spos,yone,ul,uh,rl,rh,small⟩ := Window.fixed_construction_window hp (Y/D) (S/D) lower upper wlo whi
  exact ⟨spos,yone,ul,uh,rl,rh,small (by omega)⟩

/-- The actual mean at the center of the coefficient box and the exact
    one-mark projected width satisfy the window bounds after every permitted
    divisor up to A·B^40. -/
theorem one_point_window {n ell a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (cap : a ≤ Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (side : Bool) (D : ℝ) (divisor : 1 ≤ D ∧ D ≤ (Fixed.A (n.log2+1):ℝ)*(Fixed.B (n.log2+1):ℝ)^40) :
    InWindow (n.log2+1) ((exactMean n ell a side:ℝ)/D) (oneWidth n ell a/D) := by
  let b := n.log2+1; let x : ℝ := dyadicUnit b
  have xp : 1 ≤ x := by dsimp [x,dyadicUnit]; exact_mod_cast Nat.one_le_two_pow
  have c := centered_envelope hn big target cap grid side (exactMean n ell a side) (by simp; positivity)
  have w := one_width_bounds hn big target cap
  apply divided_window hn big _ _ _ divisor c ⟨?_,w.2⟩
  apply le_trans ?_ w.1
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) _) (by norm_num)
    (by linarith [one_le_pow₀ xp (n := 50)] : (4:ℝ) ≤ 8*x^50)

/-- A separated pair, with the first projection in its central range, has
    an admissible exact conditional mean and second projected width. The
    statement includes rescaling by auxiliary prime and gcd divisors. -/
theorem two_point_window {n ell a a' : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a ≤ Fixed.A (n.log2+1)) (cap' : a' ≤ Fixed.A (n.log2+1))
    (grid' : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a')
    (clean : (Fixed.A (n.log2+1):ℝ) ≤ |(a':ℝ)-a| * (dyadicUnit (n.log2+1):ℝ)^50)
    (side : Bool) (observed D : ℝ) (central : |observed-lineCenter n a| ≤ ((n.log2+1:ℕ):ℝ)^3*projectionScale n a)
    (divisor : 1 ≤ D ∧ D ≤ (Fixed.A (n.log2+1):ℝ)*(Fixed.B (n.log2+1):ℝ)^40) :
    InWindow (n.log2+1) (conditionalMean n ell a a' side observed/D) (twoWidth n ell a a'/D) := by
  exact divided_window hn big _ _ _ divisor (centered_envelope hn big target cap' grid' side _
    (conditional_center_error hn big target cap cap' side observed central)) (two_width_bounds hn big target cap cap' clean)

end Cogentic.Construction

#print axioms Cogentic.Construction.one_point_window
#print axioms Cogentic.Construction.two_point_window
