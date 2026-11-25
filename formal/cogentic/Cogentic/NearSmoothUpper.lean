import Cogentic.JointSmoothBulk
import Cogentic.ClassBalance
import Cogentic.SmoothBox

namespace Cogentic.Window
open Finset Real
noncomputable section

private theorem prefix_between (J : Finset ℕ) (B L : ℝ) (bl : 1≤B) (ll : 1≤L)
    (cap : ∀ p∈J, (p:ℝ)≤B) (high : L≤(∏ p∈J,p:ℕ)) :
    ∃ T⊆J, L≤(∏ p∈T,p:ℕ) ∧ ((∏ p∈T,p:ℕ):ℝ)≤B*L := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨∅,Subset.rfl,high,?_⟩
    simpa using one_le_mul_of_one_le_of_one_le bl ll
  | @insert p J fresh ih =>
    by_cases h : L≤(∏ q∈J,q:ℕ)
    · obtain ⟨T,sub,lo,hi⟩ := ih (fun q h => cap q (mem_insert_of_mem h)) h
      exact ⟨T,sub.trans (subset_insert ..),lo,hi⟩
    · refine ⟨insert p J,Subset.rfl,high,?_⟩
      rw [prod_insert fresh,Nat.cast_mul]
      exact mul_le_mul (cap p (mem_insert_self ..)) (le_of_not_ge h) (Nat.cast_nonneg _) (zero_le_one.trans bl)

private theorem smooth_divisor_between {J : Finset ℕ} {n : ℕ} {B L : ℝ} (bl : 1≤B) (ll : 1≤L)
    (cap : ∀ p∈J, (p:ℝ)≤B) (hn : n∈squarefreeSupport J) (large : L≤n) :
    ∃ t∈squarefreeSupport J, t∣n ∧ L≤t ∧ (t:ℝ)≤B*L := by
  obtain ⟨D,hd,rfl⟩ := mem_image.mp hn
  obtain ⟨T,sub,lo,hi⟩ := prefix_between D B L bl ll (fun p hp => cap p (mem_powerset.mp hd hp)) large
  exact ⟨_,mem_image.mpr ⟨T,mem_powerset.mpr (sub.trans (mem_powerset.mp hd)),rfl⟩,
    Finset.prod_dvd_prod_of_subset _ _ _ sub,lo,hi⟩

private theorem support_euler (J : Finset ℕ) (prime : ∀ p∈J, p.Prime) (α : ℝ) :
    ∑ m∈squarefreeSupport J, (m:ℝ)^(-α) = eulerMass J α := by
  classical
  let f := fun s : Finset ℕ => ∏ p∈s,p
  have inj : Set.InjOn f J.powerset := by
    intro s hs t ht eq
    have a := Nat.primeFactors_prod (fun p hp => prime p (mem_powerset.mp hs hp))
    have b := Nat.primeFactors_prod (fun p hp => prime p (mem_powerset.mp ht hp))
    exact a.symm.trans ((congrArg Nat.primeFactors eq).trans b)
  rw [squarefreeSupport,sum_image inj,eulerMass,prod_one_add]
  apply sum_congr rfl
  intro s hs
  rw [Nat.cast_prod,Real.finsetProd_rpow]
  exact fun _ _ => Nat.cast_nonneg _

private theorem finite_progression_tail (A : Finset ℕ) (q r : ℕ) (Y S T : ℝ) (qp : 0<q)
    (wide : 2≤S/q) (tp : 0≤T) (cl : ∀ n∈A, n≡r [MOD q])
    (away : ∀ n∈A, T*S ≤ |(n:ℝ)-Y|) :
    (q:ℝ)*(∑ n∈A, gaussian Y S n) ≤ 8*exp (-π*T^2/2) := by
  classical
  have qr : (0:ℝ)<q := by exact_mod_cast qp
  have sp : 0<S := by have := (le_div_iff₀ qr).mp wide; linarith
  let j := fun n : ℕ => ((n:ℤ)-(r:ℤ))/(q:ℤ)
  have key (n) (h : n∈A) : (r:ℤ)+(q:ℤ)*j n=n := by
    dsimp only [j]; rw [mul_comm,Int.ediv_mul_cancel ((Nat.modEq_iff_dvd.mp (cl n h).symm))]; ring
  have realKey (n) (h : n∈A) : (r:ℝ)+(q:ℝ)*j n=n := by exact_mod_cast key n h
  let G := fun i : ℤ => coeffGaussian ((r:ℝ)+(q:ℝ)*i) Y S
  let cut := fun i : ℤ => if T*S≤|(r:ℝ)+(q:ℝ)*i-Y| then G i else 0
  have gs : Summable G := by
    have nz := (conditional_progression_probability r q Y S qr wide (fun _ => True)).1.ne'
    by_contra h
    exact nz (tsum_eq_zero_of_not_summable h)
  have cn (i) : 0≤cut i := by dsimp [cut,G]; split <;> first | exact (exp_pos _).le | rfl
  have cs := Summable.of_nonneg_of_le cn (fun i => show cut i≤G i by dsimp [cut]; split <;> first | rfl | exact (exp_pos _).le) gs
  have inj : Set.InjOn j A := by
    intro n hn m hm eq
    exact_mod_cast ((key n hn).symm.trans ((congrArg (fun z : ℤ => (r:ℤ)+q*z) eq).trans (key m hm)))
  have eq : (∑ n∈A, gaussian Y S n)=(∑ i∈A.image j, cut i)/S := by
    rw [sum_image inj,sum_div]
    apply sum_congr rfl
    intro n h
    simp only [cut,G,realKey n h,if_pos (away n h)]
    rfl
  rw [eq,show (q:ℝ)*((∑ i∈A.image j, cut i)/S)=(q/S)*(∑ i∈A.image j, cut i) by ring]
  apply (mul_le_mul_of_nonneg_left (cs.sum_le_tsum _ (fun i _ => cn i)) (div_nonneg qr.le sp.le)).trans
  exact Cogentic.Construction.first_gaussian_tail r q Y S T qr (by linarith) tp

/-- A greedy divisor of a smooth value controls the mass in any reduced
class. This upper bound only needs the width divided by the stride, so it
remains available arbitrarily close to the first observed mark. -/
theorem greedy_class_gaussian {q : ℕ} (qp : 0<q) (J : Finset ℕ)
    (prime : ∀ p∈J, p.Prime) (clean : ∀ p∈J, ¬p∣q) (r : (ZMod q)ˣ)
    (B Y S α : ℝ) (bl : 1≤B) (cap : ∀ p∈J, (p:ℝ)≤B)
    (wide : 2*q*B≤S) (high : 2*S≤Y) (ha : α≤1) :
    (q:ℝ)*classWeight J Y S r ≤
      8*(S/(2*q*B))^(α-1)*eulerMass J α + 8*exp (-π*(Y/(2*S))^2/2) := by
  classical
  let : NeZero q := ⟨qp.ne'⟩
  let L := S/(2*q*B)
  let T := Y/(2*S)
  let F := squarefreeSupport J
  let C := F.filter (fun n : ℕ => (r:ZMod q)=n)
  let H := F.filter (fun t : ℕ => L≤(t:ℝ) ∧ (t:ℝ)≤B*L)
  let A := C.filter (fun n : ℕ => L≤(n:ℝ))
  let Z := C.filter (fun n : ℕ => ¬L≤(n:ℝ))
  let w := fun n : ℕ => gaussian Y S n
  have qr : (0:ℝ)<q := by exact_mod_cast qp
  have q1 : (1:ℝ)≤q := by exact_mod_cast qp
  have bp : 0<B := zero_lt_one.trans_le bl
  have sp : 0<S := (by positivity : 0<2*(q:ℝ)*B).trans_le wide
  have lp : 1≤L := (one_le_div (by positivity)).mpr wide
  have ls : L≤S := div_le_self sp.le (by nlinarith only [mul_le_mul q1 bl (by norm_num) qr.le] : (1:ℝ)≤2*q*B)
  have low (n : ℕ) (hn : n∈C) : n≡(r:ZMod q).val [MOD q] :=
    (ZMod.natCast_eq_natCast_iff ..).mp ((mem_filter.mp hn).2.symm.trans (ZMod.natCast_zmod_val _).symm)
  have positive (n : ℕ) : 0≤w n := div_nonneg (exp_pos _).le sp.le
  have wideQ : 2≤S/q := (le_div_iff₀ qr).mpr ((le_mul_of_one_le_right (by positivity) bl).trans wide)
  have lower := finite_progression_tail Z q (r:ZMod q).val Y S T qp wideQ
    (div_nonneg (by linarith) (by positivity)) (fun n hn => low n (mem_filter.mp hn).1) (fun n hn => by
      have small := (le_of_not_ge (mem_filter.mp hn).2).trans ls
      have neg : (n:ℝ)-Y≤0 := by linarith
      rw [abs_of_nonpos neg,show T*S=Y/2 by dsimp [T]; field_simp]; linarith)
  have cover (n : ℕ) (hn : n∈A) : w n ≤ ∑ t∈H, if t∣n then w n else 0 := by
    obtain ⟨hm,lg⟩ := mem_filter.mp hn
    obtain ⟨t,tm,dvd,lo,hi⟩ := smooth_divisor_between bl lp cap (mem_filter.mp hm).1 lg
    simpa only [if_pos dvd] using (single_le_sum (f:=fun t => if t∣n then w n else 0) (s:=H)
      (fun t _ => by split <;> first | exact positive n | rfl) (mem_filter.mpr ⟨tm,lo,hi⟩))
  have each (t : ℕ) (ht : t∈H) : (q:ℝ)*(∑ n∈A, if t∣n then w n else 0) ≤ 8*L^(α-1)*(t:ℝ)^(-α) := by
    obtain ⟨hF,lo,hi⟩ := mem_filter.mp ht
    have tp : 0<t := Nat.pos_of_ne_zero ((mem_squarefreeSupport J prime t).mp hF).1.ne_zero
    have tr : (0:ℝ)<t := by exact_mod_cast tp
    have cop : q.Coprime t := by
      obtain ⟨P,ph,rfl⟩ := mem_image.mp hF
      exact Nat.coprime_prod_right_iff.mpr (fun p hp => ((prime p (mem_powerset.mp ph hp)).coprime_iff_not_dvd.mpr
        (clean p (mem_powerset.mp ph hp))).symm)
    let c := Nat.chineseRemainder cop (r:ZMod q).val 0
    let D := A.filter (t∣·)
    have cl (n : ℕ) (hn : n∈D) : n≡c.val [MOD q*t] := by
      obtain ⟨atA,divides⟩ := mem_filter.mp hn
      exact (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
        ⟨(low n (mem_filter.mp atA).1).trans c.property.1.symm,(Nat.modEq_zero_iff_dvd.mpr divides).trans c.property.2.symm⟩
    have wid : 2≤S/((q*t:ℕ):ℝ) := by
      rw [Nat.cast_mul,le_div_iff₀ (mul_pos qr tr)]
      have ub : B*L=S/(2*q) := by dsimp only [L]; field_simp
      rw [ub,le_div_iff₀ (by positivity)] at hi
      linarith only [hi]
    have est := finite_progression_tail D (q*t) c.val Y S 0 (Nat.mul_pos qp tp) wid le_rfl cl
      (fun n _ => by rw [zero_mul]; exact abs_nonneg _)
    simp only [Nat.cast_mul,zero_pow (by decide : 2≠0),mul_zero,zero_div,exp_zero,mul_one] at est
    rw [←sum_filter]
    apply (show (q:ℝ)*(∑ n∈D,w n) ≤ 8/t from (le_div_iff₀ tr).mpr (by linarith only [est])).trans
    have expo := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le lp) lo (sub_nonpos.mpr ha)
    have eq : (t:ℝ)^(α-1)*(t:ℝ)^(-α)=(t:ℝ)⁻¹ := by
      rw [←Real.rpow_add tr,show α-1+ -α = -1 by ring,Real.rpow_neg_one]
    calc
      8/t = 8*((t:ℝ)^(α-1)*(t:ℝ)^(-α)) := by rw [eq,div_eq_mul_inv]
      _ ≤ _ := by rw [←mul_assoc]; gcongr
  have sums := sum_le_sum cover
  rw [sum_comm] at sums
  have main := mul_le_mul_of_nonneg_left sums qr.le
  conv_rhs at main => rw [mul_sum]
  have power := (sum_le_sum each)
  rw [←mul_sum (a:=8*L^(α-1))] at power
  have ker : (∑ t∈H, (t:ℝ)^(-α)) ≤ eulerMass J α := by
    rw [←support_euler J prime α]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun t _ _ => Real.rpow_nonneg (Nat.cast_nonneg t) _)
  have all := main.trans (power.trans (mul_le_mul_of_nonneg_left ker (by positivity : 0≤8*L^(α-1))))
  have split : classWeight J Y S r = (∑ n∈A,w n)+(∑ n∈Z,w n) := by
    change (∑ n∈F, if (r:ZMod q)=n then w n else 0)=_
    rw [←sum_filter]
    exact (sum_filter_add_sum_filter_not C (fun n => L≤(n:ℝ)) w).symm
  rw [split,mul_add]
  exact add_le_add all lower

end
end Cogentic.Window

namespace Cogentic.Construction
open Finset Real Cogentic.Window
noncomputable section

/-- Reducing a nonunit class divides the Gaussian width and the stride by
the same gcd. In particular the bound on the whole signed scalar measure
carries no multiplicative gcd loss. -/
theorem greedy_scalar_upper (J : Finset ℕ) (prime : ∀ p∈J, p.Prime)
    (B Y S α : ℝ) (bl : 1≤B) (cap : ∀ p∈J, (p:ℝ)≤B)
    (c s : ℤ) (sn : s≠0) (wide : 2*s.natAbs*B≤S) (high : 2*S≤Y) (ha : α≤1) :
    let K := J.filter (fun p => ¬p∣s.natAbs)
    (scalarMass J c s Y S).re ≤ 8*(S/(2*s.natAbs*B))^(α-1)*eulerMass K α +
      8*exp (-π*(Y/(2*S))^2/2) := by
  intro K
  let g := commonDivisor c s
  let q := s.natAbs/g
  have spn := Int.natAbs_pos.mpr sn
  have sd : g∣s.natAbs := (gcd_dvd_intercept c s sn).2
  have gp : 0<g := Nat.gcd_pos_of_pos_right _ spn
  have gr : (0:ℝ)<g := by exact_mod_cast gp
  have qp : 0<q := Nat.div_pos (Nat.le_of_dvd spn sd) gp
  have fact : (q:ℝ)*g=s.natAbs := by exact_mod_cast Nat.div_mul_cancel sd
  have bp : 0<B := zero_lt_one.trans_le bl
  have str : (0:ℝ)<s.natAbs := by exact_mod_cast spn
  have sp : 0<S := (by positivity : (0:ℝ)<2*s.natAbs*B).trans_le wide
  have QP := scalar_reduced_exact prime c s sn Y S sp
  let r := ZMod.unitOfCoprime (scalarResidue c s/g)
    (TwoThirdsWindow.reduced_class_coprime (scalarResidue c s) s.natAbs spn)
  change scalarMass J c s Y S=if g∈squarefreeSupport J then
    (q:ℂ)*classMass (squarefreeSupport K) (fun t => (gaussian (Y/g) (S/g) t:ℂ)) r else 0 at QP
  rw [QP]
  split
  · have qwide : 2*(q:ℝ)*B≤S/g := (le_div_iff₀ gr).mpr (by
      rw [←fact] at wide; linarith only [wide])
    have qsmall := div_le_div_of_nonneg_right high gr.le
    have ub := greedy_class_gaussian qp K (fun p h => prime p (mem_filter.mp h).1)
      (fun p h dv => (mem_filter.mp h).2 (dv.trans (Nat.div_dvd_of_dvd sd))) r B
      (Y/g) (S/g) α bl (fun p h => cap p (mem_filter.mp h).1) qwide (by simpa only [mul_div_assoc] using qsmall) ha
    rw [←coe_classWeight]
    simp only [Complex.mul_re,Complex.natCast_re,Complex.ofReal_re,Complex.natCast_im,zero_mul,sub_zero]
    have ratio : (S/g)/(2*(q:ℝ)*B)=S/(2*s.natAbs*B) := by
      rw [←fact]; field_simp
    have shift : (Y/g)/(2*(S/g))=Y/(2*S) := by field_simp
    rwa [ratio,shift] at ub
  · simp only [Complex.zero_re]
    exact add_nonneg (mul_nonneg (by positivity) (eulerMass_pos _ _).le) (by positivity)

private theorem rough_slope_width {n a : ℕ} (cap : a≤Fixed.A (n.log2+1)) :
    let b := n.log2+1; let U : ℝ := Fixed.U b
    U/2≤conditionalScale n a ∧ conditionalScale n a≤U := by
  intro b U
  let A : ℝ := Fixed.A b
  have up : 0<U := by dsimp [U,Fixed.U]; positivity
  have ap : 0<A := by dsimp [A,Fixed.A]; positivity
  have pr := projected_scale_bounds cap
  change U*A≤projectionScale n a ∧ projectionScale n a≤2*(U*A) at pr
  have sp := (mul_pos up ap).trans_le pr.1
  change U/2 ≤ U*A*U/projectionScale n a ∧ U*A*U/projectionScale n a≤U
  constructor
  · apply (le_div_iff₀ sp).mpr; linarith only [mul_le_mul_of_nonneg_right pr.2 up.le]
  · apply (div_le_iff₀ sp).mpr; linarith only [mul_le_mul_of_nonneg_right pr.1 up.le]

private theorem rough_width_cap {n ell a a' : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (cap : a≤Fixed.A (n.log2+1))
    (cap' : a'≤Fixed.A (n.log2+1)) :
    twoWidth n ell a a'≤referenceWidth n := by
  let b := n.log2+1; let A := Fixed.A b; let m := Fixed.rootBase n
  have am : (a':ℝ)≤ m := by exact_mod_cast (mark_range hn big cap').le
  have p := (rough_slope_width cap).2
  have pos : 0≤conditionalScale n a := (by positivity : (0:ℝ)≤(Fixed.U b:ℝ)/2).trans (rough_slope_width cap).1
  have abs1 : |(a':ℝ)-m|≤ m := by rw [abs_of_nonpos (sub_nonpos.mpr am)]; linarith [Nat.cast_nonneg (α:=ℝ) a']
  have abs2 : |(a':ℝ)-a|≤A := by
    exact abs_le.mpr ⟨by linarith [show (a:ℝ)≤A by exact_mod_cast cap,Nat.cast_nonneg (α:=ℝ) a'],
      by linarith [show (a':ℝ)≤A by exact_mod_cast cap',Nat.cast_nonneg (α:=ℝ) a]⟩
  have le : (ell:ℝ)≤Fixed.B b := by exact_mod_cast (mem_dyadicTargets.mp target).2.2
  change (primorial (Fixed.d b):ℝ)*ell * |(a':ℝ)-m| * |(a':ℝ)-a| * conditionalScale n a≤_
  dsimp only [referenceWidth]
  push_cast
  calc _ ≤ (primorial (Fixed.d b):ℝ)*Fixed.B b*m*A*Fixed.U b := by gcongr
       _ = _ := by dsimp [b,A,m]; ring

/-- The width-to-stride ratio, even at adjacent distinct marks, equals
the free coefficient width divided by its imposed slope modulus. -/
theorem PrescribedRows.rough_second_width {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (side : Bool) :
    let pre := R.prefactor a' side; let m := prodPrimes (R.miss a)
    twoWidth n ell a a' *m=(R.secondStep a a' side).natAbs*(pre:ℝ)*conditionalScale n a := by
  intro pre m
  have h := congrArg Int.natAbs (R.scaled_second a a' side)
  have sign : (markSign n a' side).natAbs=1 := by unfold markSign; split <;> decide
  simp only [Int.natAbs_mul,Int.natAbs_natCast,sign,one_mul] at h
  have cast := congrArg (Nat.cast (R:=ℝ)) h
  push_cast at cast
  change _ = (R.secondStep a a' side).natAbs*(R.prefactor a' side:ℝ)*conditionalScale n a
  rw [cast]
  dsimp only [twoWidth,conditionalScale,m]
  simp only [Int.cast_sub,Int.cast_natCast,Nat.cast_natAbs,Int.cast_abs]
  ring

/-- Uniform upper bound for the actual second-observation event for every
distinct pair on the grid, including separation one. -/
theorem PrescribedRows.conditional_smooth_upper {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (cap : a≤Fixed.A (n.log2+1))
    (mark : a'∈(construct n ell 0 0 0 0).marks) (diff : a'≠a)
    (side : Bool) (u v : ℤ) (ok : R.compatible side u v) (α : ℝ) (ha : α≤1) :
    let b := n.log2+1; let B : ℝ := Fixed.B b; let U : ℝ := Fixed.U b
    let x := u+a*v; let m := prodPrimes (R.miss a)
    let y := fun j : ℤ => v+(m:ℤ)*j; let key := fun j : ℤ => (x-a*y j,y j)
    let J := sieveBand n ell (R.prefactor a' side); let s := R.secondStep a a' side
    let E := fun j : ℤ => supportedValue J (R.intercept a' side (key j).1 (key j).2)
    let G := fun j : ℤ => coefficientWeight n (key j)
    |(x:ℝ)-lineCenter n a|≤(b:ℝ)^3*projectionScale n a →
    (∑' j, if E j then G j else 0)/(∑' j, G j) ≤
      (1+6*exp (-U))*(8*(U/(4*B^3))^(α-1)*eulerMass (J.filter (fun p => ¬p∣s.natAbs)) α +
        8*exp (-π*((b:ℝ)^3)^2/2)) := by
  intro b B U x m y key J s E G bulk
  obtain ⟨_,cap',grid',_⟩ := (constructed_marks_iff ..).mp mark
  let pre : ℝ := R.prefactor a' side
  let Y := conditionalMean n ell a a' side x; let S := twoWidth n ell a a'
  let N : ℝ := s.natAbs
  have am := mark_range hn big cap'
  have sn := (R.secondStep_size am (mem_dyadicTargets.mp target).1.pos diff side).2
  have np : 0<N := by dsimp only [N,s]; exact_mod_cast Int.natAbs_pos.mpr sn
  have pp : 0<pre := by dsimp only [pre]; exact_mod_cast (R.pre_bounds target a' side).1
  have bp : 1≤B := by dsimp only [B]; exact_mod_cast Nat.one_le_two_pow
  have Bp : 0<B := zero_lt_one.trans_le bp
  have up : 0<U := by dsimp [U,Fixed.U]; positivity
  have mb := R.subprod_bounds (s:=R.miss a) sdiff_subset
  have mp : (0:ℝ)< m := by exact_mod_cast mb.1
  have mc : (m:ℝ)≤B^2 := by dsimp only [B]; exact_mod_cast mb.2
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos _)
  have hp : 0<Fixed.h b := Nat.mul_pos dp (Nat.succ_pos _)
  have hv : Fixed.h b≤Fixed.v b := Nat.le_mul_of_pos_left _ dp
  have up4 : 4*B^3≤U := by
    dsimp only [B,U]; exact_mod_cast (show 4*(Fixed.B b)^3≤Fixed.U b by
      change 2^2*(2^(1000*Fixed.h b))^3 ≤ 2^(100000*Fixed.v b)
      rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega))
  have rat := R.rough_second_width (a:=a) (a':=a') side
  change S*m=N*pre*conditionalScale n a at rat
  have ratio : (S/pre)/(2*N*B)=conditionalScale n a/(2*(m:ℝ)*B) := by
    field_simp; linarith only [rat]
  have slope := (rough_slope_width cap).1
  have condpos : 0≤conditionalScale n a := (by positivity : 0≤U/2).trans slope
  have bot : U/(4*B^3) ≤ (S/pre)/(2*N*B) := by
    rw [ratio]
    calc _ = (U/2)/(2*B^2*B) := by ring
         _ ≤ _ := by gcongr
  have wide : 2*N*B≤S/pre := (one_le_div (by positivity)).mp
    (((one_le_div (by positivity)).mpr up4).trans bot)
  have sp0 := (lt_of_lt_of_le (by positivity : 0<2*N*B) wide)
  have sp : 0<S := (div_pos_iff.mp sp0).resolve_right (by simp [pp.not_gt]) |>.1
  have sc := rough_width_cap hn big target cap cap'
  have center := centered_envelope hn big target cap' grid' side Y
    (conditional_center_error hn big target cap cap' side x bulk)
  let X : ℝ := dyadicUnit b
  have ⟨x2,bx,k,_,_,_,_⟩ := dyadic_data (b:=b) (Nat.succ_pos _)
  have X1 : 1≤X := by dsimp [X]; exact_mod_cast (le_trans (by decide : 1≤2) x2)
  have bX : (b:ℝ)≤X := by dsimp only [X]; exact_mod_cast bx
  have amp : 6*X^100*(b:ℝ)^2*referenceWidth n ≤ amplitude n := by
    dsimp only [X]; exact_mod_cast (k ▸ (amplitude_compare hn big).1)
  have lower : 2*(b:ℝ)^3*S≤Y := by
    apply le_trans _ center.1
    apply (le_div_iff₀ (by positivity)).mpr
    have p5 := pow_le_pow_right₀ X1 (by decide : 5≤100)
    have b3 := mul_le_mul_of_nonneg_right bX (sq_nonneg (b:ℝ))
    have w0 := Nat.cast_nonneg (α:=ℝ) (referenceWidth n)
    have b4 : 4*(b:ℝ)*X^4 ≤ 6*X^100 := by
      have one := mul_le_mul_of_nonneg_right bX (pow_nonneg (zero_le_one.trans X1) 4)
      rw [pow_succ'] at p5
      nlinarith only [one,p5,pow_nonneg (zero_le_one.trans X1) 100]
    have e := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right b4 (sq_nonneg (b:ℝ))) w0
    have cmp := mul_le_mul_of_nonneg_right sc (by positivity : 0≤4*(b:ℝ)^3*X^4)
    change _*(2*X^4)≤_
    linarith only [amp,e,cmp]
  have oneB : (1:ℝ)≤b := by exact_mod_cast (Nat.succ_pos n.log2)
  have ls := mul_le_mul_of_nonneg_right (one_le_pow₀ oneB (n:=3)) sp.le
  have high : 2*(S/pre)≤Y/pre := by
    rw [←mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith only [ls,lower]) pp.le
  let c := R.intercept a' side u v
  have raw := greedy_scalar_upper J (fun p h => (mem_primeBand.mp (mem_filter.mp h).1).1)
    B (Y/pre) (S/pre) α bp (fun p h => by dsimp only [B]; exact_mod_cast (mem_primeBand.mp (mem_filter.mp h).1).2.1)
    c s sn wide high ha
  have rate := Real.rpow_le_rpow_of_nonpos (div_pos up (by positivity)) bot (sub_nonpos.mpr ha)
  have tol : (b:ℝ)^3 ≤ (Y/pre)/(2*(S/pre)) := by
    rw [show (Y/pre)/(2*(S/pre))=Y/(2*S) by field_simp,le_div_iff₀ (by positivity)]
    linarith only [lower]
  have decay : exp (-π*((Y/pre)/(2*(S/pre)))^2/2) ≤ exp (-π*((b:ℝ)^3)^2/2) := by
    apply exp_le_exp.mpr
    linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) tol 2) pi_pos.le]
  have prob := (R.second_probability (by omega : 3≤Fixed.d (n.log2+1)) target cap am diff side u v ok).2
  let z := (scalarMass J c s (Y/pre) (S/pre)).re
  change |(∑' j, if E j then G j else 0)/(∑' j, G j)-z| ≤ 6*exp (-U)*z at prob
  refine le_trans (show _≤(1+6*exp (-U))*z by linarith only [(abs_le.mp prob).2]) ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact raw.trans (add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left rate (by norm_num : (0:ℝ)≤8)) (eulerMass_pos _ _).le)
    (mul_le_mul_of_nonneg_left decay (by norm_num)))


private theorem center_over_free_width {n ell a : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (cap : a≤Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (side : Bool) {pre : ℕ} (pp : 0<pre) :
    let b := n.log2+1; let B := Fixed.B b; let U := Fixed.U b
    (exactMean n ell a side:ℝ)/pre / ((U:ℝ)/(4*(B:ℝ)^3)) ≤ (B:ℝ)^(Fixed.d b) := by
  intro b B U
  let X := dyadicUnit b; let d := Fixed.d b
  have ⟨xx,bX,k,beq,aeq,_,meq⟩ := dyadic_data (b:=b) (Nat.succ_pos _)
  have xp : 0<X := (by decide : 0<2).trans_le xx
  have ppow : primorial d ≤ X^2 := by
    refine (primorial_le_four_pow d).trans ?_
    change (2^2)^d ≤ (2^Fixed.h b)^2
    rw [←pow_mul,←pow_mul,Nat.mul_comm (Fixed.h b) 2]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  have mpow := (rootBase_bound hn).trans_eq meq
  have scale : 4*B^3*(2*amplitude n) ≤ U*B^d := calc
    _ ≤ 4*B^3*(2*(54*Fixed.K₁ b*b^2*referenceWidth n)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 (amplitude_compare hn big).2)
    _ = U*(432*Fixed.K₁ b*b^2*(primorial d)*Fixed.rootBase n*B^4*Fixed.A b) := by
      dsimp only [referenceWidth,b,U,B,d]; ring
    _ ≤ U*((X^9)*X^100*X^2*X^2*X^(8*d)*(X^1000)^4*X^10000) := by
      have h432 : 432≤X^9 := (by decide : 432≤2^9).trans (Nat.pow_le_pow_left xx 9)
      rw [k,aeq,show B=X^1000 from beq]
      gcongr
    _ ≤ U*B^d := by
      rw [show B=X^1000 from beq,←pow_mul,←pow_mul]
      simp only [←pow_add]
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right xp (by change 10004≤d at big; omega)
  have avg := centered_envelope hn big target cap grid side (exactMean n ell a side) (by simp; positivity)
  have y0 : (0:ℝ)≤exactMean n ell a side := (by positivity : (0:ℝ)≤(amplitude n:ℝ)/(2*(dyadicUnit b:ℝ)^4)).trans avg.1
  have up : (0:ℝ)<U := by dsimp [U,Fixed.U]; positivity
  have bp : (0:ℝ)<B := by dsimp [B,Fixed.B]; positivity
  have part := (div_le_self y0 (show (1:ℝ)≤pre by exact_mod_cast pp)).trans avg.2
  rw [div_div_eq_mul_div,div_le_iff₀ up]
  have sc : 4*(B:ℝ)^3*(2*amplitude n) ≤ U*(B:ℝ)^d := by exact_mod_cast scale
  linarith only [mul_le_mul_of_nonneg_right part (show 0≤4*(B:ℝ)^3 by positivity),sc]

private theorem tilt_loss {L Y B α z : ℝ} {d h : ℕ} (lp : 0<L) (yp : 0<Y)
    (ha : α≤1) (cap : Y/L ≤ B^d) (tilt : (1-α)*log B≤4*z) (scale : (d:ℝ)*z=h) :
    L^(α-1)≤exp (4*(h:ℝ))*Y^(α-1) := by
  have lg := log_le_log (div_pos yp lp) cap
  rw [log_div yp.ne' lp.ne',log_pow] at lg
  rw [rpow_def_of_pos lp,rpow_def_of_pos yp,←exp_add,exp_le_exp]
  linarith only [mul_le_mul_of_nonneg_right lg (sub_nonneg.mpr ha),
    mul_le_mul_of_nonneg_left tilt (Nat.cast_nonneg (α:=ℝ) d),scale]

/-- An explicit relative upper for the actual conditional smoothness
probability uses the one-mark probability at the same second mark. It
requires no restriction on the distance or on the gcd common to the two
affine observations. -/
theorem PrescribedRows.conditional_smooth_relative (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a≤Fixed.A b → a'∈(construct n ell 0 0 0 0).marks → a'≠a →
    ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let x := u+a*v; let m := prodPrimes (R.miss a)
    let y := fun j : ℤ => v+(m:ℤ)*j; let key := fun j : ℤ => (x-a*y j,y j)
    let J := sieveBand n ell (R.prefactor a' side)
    let E := fun k : ℤ×ℤ => supportedValue J (R.intercept a' side k.1 k.2)
    let G := fun j : ℤ => coefficientWeight n (key j)
    |(x:ℝ)-lineCenter n a|≤(b:ℝ)^3*projectionScale n a →
    (∑' j, if E (key j) then G j else 0)/(∑' j, G j) ≤
      exp (10*(Fixed.h b:ℝ))*prescribedProbability R side E := by
  obtain ⟨b₁,floor⟩ := PrescribedRows.smooth_probability_saddle_floor line
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro n ell a a' R b hb hn comp target absent cap mark diff side u v ok x m y key J E G bulk
  obtain ⟨one,two⟩ := max_le_iff.mp hb
  obtain ⟨baseline,α,ha,yp,lam,model⟩ := floor R one hn comp target absent mark side
  let P := prescribedProbability R side E
  let B : ℝ := Fixed.B b; let U : ℝ := Fixed.U b; let h : ℝ := Fixed.h b
  let c := firstStep n ell a' side; let s := R.secondStep a a' side
  let J₁ := J.filter (fun p => ¬p∣c.natAbs); let J₂ := J.filter (fun p => ¬p∣s.natAbs)
  let Y := (exactMean n ell a' side:ℝ)/(R.prefactor a' side:ℝ); let L := U/(4*B^3)
  have big := degree b two
  obtain ⟨_,cap',grid',_⟩ := (constructed_marks_iff ..).mp mark
  have capY := center_over_free_width hn big target cap' grid' side (R.pre_bounds target a' side).1
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have lu : 0<L := by dsimp [L,U,Fixed.U]; positivity
  have t := tilt_loss (L:=L) (Y:=Y) (B:=B) (d:=Fixed.d b) (h:=Fixed.h b) lu yp ha.2 capY lam
    (by simp only [Fixed.h,Nat.cast_mul,b])
  have sub : J₂⊆J₁ := by
    have hcs : c.natAbs∣s.natAbs := Int.natAbs_dvd_natAbs.mpr (dvd_mul_of_dvd_left (dvd_mul_right ..) _)
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,fun dvd => (mem_filter.mp hp).2 (dvd.trans hcs)⟩
  have eu : eulerMass J₂ α ≤ eulerMass J₁ α := prod_le_prod_of_subset_of_one_le sub
    (fun i _ => by change 0≤1+(i:ℝ)^(-α); positivity)
    (fun i _ _ => by change 1≤1+(i:ℝ)^(-α); linarith [rpow_nonneg (Nat.cast_nonneg i) (-α)])
  change exp (-4*h)*(Y^(α-1)*eulerMass J₁ α) ≤ 8*π*P at model
  have inv : Y^(α-1)*eulerMass J₁ α ≤ exp (4*h)*(8*π*P) := by
    have z := mul_le_mul_of_nonneg_left model (exp_pos (4*h)).le
    rwa [←mul_assoc,←exp_add,show 4*h+ -4*h=0 by ring,exp_zero,one_mul] at z
  have raw := R.conditional_smooth_upper hn big target cap mark diff side u v ok α ha.2 bulk
  apply raw.trans
  change (1+6*exp (-U))*(8*L^(α-1)*eulerMass J₂ α+8*exp (-π*((b:ℝ)^3)^2/2)) ≤ exp (10*h)*P
  have er := mul_le_mul t eu (eulerMass_pos _ _).le (by positivity)
  have main : 8*L^(α-1)*eulerMass J₂ α ≤ 64*π*exp (8*h)*P := by
    have bound := mul_le_mul_of_nonneg_left inv (exp_pos (4*h)).le
    conv_rhs at bound => rw [←mul_assoc,←exp_add,show 4*h+4*h=8*h by ring]
    change L^(α-1)*eulerMass J₂ α ≤ exp (4*h)*Y^(α-1)*eulerMass J₁ α at er
    linarith only [er,bound]
  change 8/B≤P at baseline
  have pp : 0<P := (div_pos (by norm_num) bp).trans_le baseline
  have db := Fixed.degree_le_bits b
  have dh : Fixed.d b≤Fixed.h b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hr : (10004:ℝ)≤h := by dsimp only [h]; exact_mod_cast big.trans dh
  have br : (10004:ℝ)≤b := by exact_mod_cast big.trans db
  have tau : 8*exp (-π*((b:ℝ)^3)^2/2) ≤ P := by
    apply le_trans _ baseline
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [←exp_log bp,←exp_neg,exp_le_exp]
    have hbnd : log B ≤ 1000*b := by
      have hle := (Nat.mul_le_mul_right (Fixed.z b) (Nat.le_self_pow (by decide : 3≠0) (Fixed.d b))).trans (Fixed.degree_floor b).1
      have lg : log 2≤1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
      have eq : log B = 1000*h*log 2 := by simp only [B,h,Fixed.B,Fixed.beta,Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul]
      rw [eq]; nlinarith only [mul_le_mul_of_nonneg_left lg (show 0≤h by linarith),show h≤b by dsimp only [h]; exact_mod_cast hle]
    have br1 : 1≤(b:ℝ) := by linarith
    have pw := le_self_pow₀ br1 (by decide : (3:ℕ)≠0)
    have sq := pow_le_pow_left₀ (by positivity) pw 2
    have lin := mul_le_mul_of_nonneg_right br (Nat.cast_nonneg (α:=ℝ) b)
    nlinarith only [mul_le_mul_of_nonneg_right pi_gt_three.le (sq_nonneg ((b:ℝ)^3)),hbnd,sq,lin]
  have smallN : 1+6*exp (-U) ≤ 7 := by linarith only [exp_le_one_iff.mpr (neg_nonpos.mpr (show 0≤U by dsimp [U]; positivity))]
  have e8 : 1≤exp (8*h) := one_le_exp (by linarith)
  have const : 7*(64*π+1) ≤ exp (2*h) := by linarith only [add_one_le_exp (2*h),pi_lt_four,hr]
  have mx := mul_le_mul_of_nonneg_left (add_le_add main tau) (by norm_num : (0:ℝ)≤7)
  have e := mul_le_mul_of_nonneg_right const (mul_nonneg (exp_pos (8*h)).le pp.le)
  conv_rhs at e => rw [←mul_assoc,←exp_add,show 2*h+8*h=10*h by ring]
  have ep : 0<eulerMass J₂ α := eulerMass_pos _ _
  apply (mul_le_mul_of_nonneg_right smallN (by positivity : 0≤8*L^(α-1)*eulerMass J₂ α+8*exp (-π*((b:ℝ)^3)^2/2))).trans
  linarith only [mx,e,mul_le_mul_of_nonneg_right e8 pp.le]


/-- For every distinct pair the complete one-field joint probability is at
most X^16 times the product of the two actual marginal probabilities, including
on the diagonal neighborhood where the nominal-center expansion is unavailable. -/
theorem PrescribedRows.joint_smooth_upper (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → a'∈(construct n ell 0 0 0 0).marks → a'≠a →
    ∀ side : Bool,
    let E := fun a (k : ℤ×ℤ) => supportedValue (sieveBand n ell (R.prefactor a side)) (R.intercept a side k.1 k.2)
    prescribedProbability R side (fun k => E a k ∧ E a' k) ≤
      (dyadicUnit b:ℝ)^16 * (prescribedProbability R side (E a)*prescribedProbability R side (E a')) := by
  classical
  obtain ⟨b₁,conditional⟩ := PrescribedRows.conditional_smooth_relative line
  obtain ⟨b₂,margin⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨max b₁ (max b₂ 10004),?_⟩
  intro n ell a a' R b hb hn comp target absent first second diff side E
  obtain ⟨one,rest⟩ := max_le_iff.mp hb
  obtain ⟨two,big⟩ := max_le_iff.mp rest
  have cap := ((constructed_marks_iff ..).mp first).2.1
  let M := prodPrimes (R.miss a)
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let Z := ∑' k : C, coefficientWeight n k.val
  let r₀ := exp (10*(Fixed.h b:ℝ))
  let P := prescribedProbability R side (E a'); let P₁ := prescribedProbability R side (E a)
  let rate := r₀*P
  let bulk (k : ℤ×ℤ) := |((k.1+(a:ℤ)*k.2:ℤ):ℝ)-lineCenter n a|≤(b:ℝ)^3*projectionScale n a
  let all (k : ℤ×ℤ) := E a k ∧ E a' k
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
  let B : ℝ := Fixed.B b
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have f1 : 8/B≤P₁ := margin R two hn comp target absent first side
  have f2 : 8/B≤P := margin R two hn comp target absent second side
  have pp := (div_pos (by norm_num : (0:ℝ)<8) bp).trans_le f2
  have rp : 0≤rate := mul_nonneg (exp_pos _).le pp.le
  have fiber (i : ℤ) : (∑' j : ℤ, V both (i,j)) ≤ rate*(∑' j : ℤ, V (E a) (i,j)) := by
    let seed := (x i-(a:ℤ)*r i, r i)
    have compatible := (e (i,0)).property
    rw [coords] at compatible
    simp only [mul_zero,add_zero] at compatible
    have atX : seed.1+(a:ℤ)*seed.2=x i := sub_add_cancel ..
    have same (j : ℤ) : E a (key i j)↔E a seed := by simp only [E,PrescribedRows.intercept,obs,atX]
    by_cases h : bulk seed ∧ E a seed
    · have central := h.1
      dsimp only [bulk] at central
      have est := conditional R one hn comp target absent cap second diff side seed.1 seed.2 compatible central
      dsimp only at est
      rw [atX] at est
      change (∑' j : ℤ, V (E a') (i,j))/(∑' j : ℤ, W (i,j))≤rate at est
      have ge (j : ℤ) : V (E a) (i,j)=W (i,j) := if_pos ((same j).mpr h.2)
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
    change prescribedProbability R side both≤rate*prescribedProbability R side (E a)
    rw [prob both,prob (E a),←mul_div_assoc,div_le_div_iff_of_pos_right zp,
      (vs both).tsum_prod,(vs (E a)).tsum_prod,←tsum_mul_left]
    exact (vs both).prod.tsum_le_tsum fiber ((vs (E a)).prod.mul_left _)
  have outside := R.observation_cut_error target cap side ((b:ℝ)^3) (by positivity) all both
    (fun k inside => by have yes : bulk k := inside.le; simp [both,yes])
  let H := (Fixed.h b:ℝ)
  have br : (10004:ℝ)≤b := by exact_mod_cast big
  have hp : 1≤H := by dsimp [H]; exact_mod_cast Nat.mul_pos (Fixed.degree_pos (by dsimp [b]; omega)) (Nat.succ_pos b.log2)
  have loss : (1+90*exp (-(Fixed.U b:ℝ)))*(8*exp (-π*((b:ℝ)^3)^2/2)) ≤ P₁*P := by
    apply le_trans _ (mul_le_mul f1 f2 (div_nonneg (by norm_num) bp.le) ((div_pos (by norm_num) bp).trans_le f1).le)
    have normS : 1+90*exp (-(Fixed.U b:ℝ)) ≤ 91 := by linarith only [exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg (α:=ℝ) (Fixed.U b)))]
    apply (mul_le_mul_of_nonneg_right normS (by positivity)).trans
    have z : log B≤1000*(b:ℝ) := by
      have hl := (Nat.mul_le_mul_right (Fixed.z b) (Nat.le_self_pow (by decide : 3≠0) (Fixed.d b))).trans (Fixed.degree_floor b).1
      have eq : log B=1000*H*log 2 := by simp only [B,H,Fixed.B,Fixed.beta,Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul]
      have lg : log 2≤1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
      rw [eq]; nlinarith only [mul_le_mul_of_nonneg_left lg (zero_le_one.trans hp),show H≤b by dsimp only [H]; exact_mod_cast hl]
    have r1 : (1:ℝ)≤b := by linarith
    have sq := pow_le_pow_left₀ (by positivity) (le_self_pow₀ r1 (by decide : (3:ℕ)≠0)) 2
    have lin := mul_le_mul_of_nonneg_right br (Nat.cast_nonneg (α:=ℝ) b)
    have rateE : 1000 + -π*((b:ℝ)^3)^2/2 ≤ -(2*log B) := by
      nlinarith only [sq,lin,z,br,mul_le_mul_of_nonneg_right pi_gt_three.le (sq_nonneg ((b:ℝ)^3))]
    have ex := exp_le_exp.mpr rateE
    rw [exp_add,exp_neg,show 2*log B=(2:ℕ)*log B by norm_num,exp_nat_mul,exp_log bp] at ex
    have en := mul_le_mul_of_nonneg_right (add_one_le_exp 1000) (exp_pos (-π*((b:ℝ)^3)^2/2)).le
    have db : 8/B*(8/B)=64*(B^2)⁻¹ := by ring
    rw [db]; nlinarith only [ex,en,inv_nonneg.mpr (sq_nonneg B), (exp_pos (-π*((b:ℝ)^3)^2/2)).le]
  have power : r₀+1≤(dyadicUnit b:ℝ)^16 := by
    have two : 2≤exp H := by linarith only [add_one_le_exp H,hp]
    have e1 : 1≤r₀ := one_le_exp (by change 0≤10*H; linarith)
    have rhs : (dyadicUnit b:ℝ)^16=exp (16*H*log 2) := by
      simp only [dyadicUnit,Nat.cast_pow,Nat.cast_ofNat]
      rw [←exp_log (by norm_num : (0:ℝ)<2),←exp_nat_mul,←exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
      dsimp only [H]; congr 1; push_cast; ring
    rw [rhs]
    have mag : 11*H≤16*H*log 2 := by
      have := mul_le_mul_of_nonneg_left (show (11/16:ℝ)≤log 2 by linarith [log_two_gt_d9]) (zero_le_one.trans hp)
      linarith
    have bigR := (exp_le_exp.mpr mag)
    rw [show 11*H=H+10*H by ring,exp_add] at bigR
    linarith only [e1,bigR,mul_le_mul_of_nonneg_right two (exp_pos (10*H)).le,
      show r₀=exp (10*H) by rfl]
  change prescribedProbability R side all≤_* (P₁*P)
  have ub := (abs_le.mp outside).2.trans loss
  exact le_trans (show prescribedProbability R side all ≤ (r₀+1)*(P₁*P) by
    change prescribedProbability R side both≤r₀*P*P₁ at bulkBound
    linarith only [bulkBound,ub]) (mul_le_mul_of_nonneg_right power (mul_nonneg ((div_pos (by norm_num) bp).trans_le f1).le pp.le))


end
end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.joint_smooth_upper
