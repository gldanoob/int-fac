import Cogentic.BadRowSlopes
import Cogentic.PolynomialLaw
import Cogentic.PolynomialRetained

namespace Cogentic.Construction
open Real Finset Cogentic.Window

private theorem slope_normalizer (c μ M S : ℝ) (mp : 0<M) (wide : 2≤S/M) :
    let f := fun j : ℤ => coeffGaussian (c+M*j) μ S
    Summable f ∧ (S/M)/2 ≤ ∑' j, f j ∧ (∑' j, f j) ≤ 2*(S/M) := by
  intro f
  let t := S/M
  have tp : 0<t := by change 2≤t at wide; linarith
  have norm : |(∑' j, f j)/t-1| ≤ 3*exp (-π*t^2) := by
    dsimp only [f,t]
    simp_rw [coeffGaussian_progression _ _ _ _ _ mp]
    exact shifted_gaussian_normalizer _ _ (by linarith)
  have e : 3*exp (-π*t^2) ≤ 1/2 := by
    rw [neg_mul,exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
    have sq : 4≤t^2 := by change 2≤t at wide; nlinarith only [sq_nonneg (t-2),wide]
    nlinarith only [add_one_le_exp (π*t^2),mul_le_mul_of_nonneg_left sq pi_pos.le,pi_gt_three]
  have err := abs_le.mp (norm.trans e)
  have low := (le_div_iff₀ tp).mp (show 1/2 ≤ (∑' j,f j)/t by linarith only [err.1])
  have high := (div_le_iff₀ tp).mp (show (∑' j,f j)/t ≤ 2 by linarith only [err.2])
  refine ⟨?_,by linarith only [low],high⟩
  by_contra no
  rw [tsum_eq_zero_of_not_summable no] at low
  linarith

private theorem one_residue_weight (p : ℕ) (hp : 0<p) (r : ZMod p) (c M μ S : ℝ)
    (mp : 0<M) (wide : 2≤S/(M*p)) :
    (∑' j : ℤ, if (j:ZMod p)=r then coeffGaussian (c+M*j) μ S else 0) ≤ 2*(S/(M*p)) := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  let f := fun j : ℤ => if (j:ZMod p)=r then coeffGaussian (c+M*j) μ S else 0
  let k := fun j : ℤ => (r.val:ℤ)+p*j
  have matchR : ((r.val:ℤ):ZMod p)=r := by simp
  have inj : Function.Injective k := fun i j eq =>
    mul_left_cancel₀ (by exact_mod_cast hp.ne' : (p:ℤ)≠0) (add_left_cancel eq : (p:ℤ)*i=p*j)
  have support : Function.support f ⊆ Set.range k := by
    intro i fi
    have h : (i:ZMod p)=r := by by_contra no; exact fi (if_neg no)
    obtain ⟨j,eq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub r.val i p).mp (matchR.trans h.symm)
    exact ⟨j,by dsimp [k]; linarith only [eq]⟩
  have eval (j : ℤ) : f (k j) = coeffGaussian ((c+M*r.val)+(M*p)*j) μ S := by
    have key : (k j:ZMod p)=r := by simp [k]
    simp only [f,if_pos key,k,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    congr 1; ring
  rw [←(inj.tsum_eq support),tsum_congr eval]
  exact (slope_normalizer (c+M*r.val) μ (M*p) S (mul_pos mp (by exact_mod_cast hp)) wide).2.2

/-- On a fixed first-coordinate Gaussian fiber, avoiding one residue per
prime loses at most four times the sum of their reciprocal moduli. -/
theorem gaussian_forbidden_slopes (P : Finset ℕ) (r : ∀ p : ℕ, ZMod p)
    (E : ℤ→Prop) [DecidablePred E] (c M μ S : ℝ) (mp : 0<M) (baseWide : 2≤S/M)
    (wide : ∀ p∈P, 0<p ∧ 2≤S/(M*p)) (bad : ∀ j, E j → ∃ p∈P, (j:ZMod p)=r p) :
    let W := fun j : ℤ => coeffGaussian (c+M*j) μ S
    0 < ∑' j, W j ∧ (∑' j, if E j then W j else 0)/(∑' j, W j) ≤ 4*∑ p∈P, (p:ℝ)⁻¹ := by
  classical
  intro W
  let Z := ∑' j, W j
  let τ := S/M
  let A := fun (p : ℕ) (j : ℤ) => if (j:ZMod p)=r p then W j else 0
  obtain ⟨ws,low,_⟩ := slope_normalizer c μ M S mp baseWide
  have zp : 0<Z := (by change 2≤τ at baseWide; linarith : 0<τ/2).trans_le low
  have wn (j) : 0≤W j := (exp_pos _).le
  have bounds (p j) : 0≤A p j ∧ A p j≤W j := by dsimp only [A]; split <;> simp [wn]
  have ss (p) := Summable.of_nonneg_of_le (fun j => (bounds p j).1) (fun j => (bounds p j).2) ws
  have en (j : ℤ) : 0 ≤ (if E j then W j else 0) := by split <;> first | exact wn _ | rfl
  have es := Summable.of_nonneg_of_le en (fun j => show (if E j then W j else 0) ≤ W j by split <;> first | rfl | exact wn _) ws
  have cover (j : ℤ) : (if E j then W j else 0) ≤ ∑ p∈P, A p j := by
    split
    next h =>
      obtain ⟨p,pm,bp⟩ := bad j h
      exact (by simpa only [A,if_pos bp] using single_le_sum (s:=P) (f:=fun i => A i j) (fun i _ => (bounds i j).1) pm)
    next => exact sum_nonneg (fun p _ => (bounds p j).1)
  have ub := es.tsum_le_tsum cover (summable_sum (s:=P) (fun p _ => ss p))
  rw [Summable.tsum_finsetSum (fun p _ => ss p)] at ub
  have each (p) (pm : p∈P) : (∑' j, A p j) ≤ 4*(p:ℝ)⁻¹*Z := by
    apply (one_residue_weight p (wide p pm).1 (r p) c M μ S mp (wide p pm).2).trans
    have eq : 2*(S/(M*p)) = (4*(p:ℝ)⁻¹)*(τ/2) := by dsimp only [τ]; ring
    rw [eq]
    exact mul_le_mul_of_nonneg_left low (by positivity)
  refine ⟨zp,(div_le_iff₀ zp).mpr (ub.trans ((sum_le_sum each).trans_eq ?_))⟩
  rw [←sum_mul,←mul_sum]

private theorem slope_width {n a M p : ℕ} (cap : a≤Fixed.A (n.log2+1))
    (mp : 0<M) (mc : M≤(Fixed.B (n.log2+1))^2) (pp : 0<p) (pc : p≤Fixed.B (n.log2+1)) :
    2 ≤ conditionalScale n a / ((M:ℝ)*p) := by
  let b := n.log2+1
  let B := Fixed.B b; let U := Fixed.U b; let A := Fixed.A b
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos _)
  have h1 : 0<Fixed.h b := Nat.mul_pos dp (Nat.succ_pos _)
  have hv : Fixed.h b ≤ Fixed.v b := Nat.le_mul_of_pos_left _ dp
  have ub : 4*B^3 ≤ U := by
    change 2^2*(2^(1000*Fixed.h b))^3 ≤ 2^(100000*Fixed.v b)
    rw [←Nat.pow_mul,←Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have prod : 4*(M*p) ≤ U := (Nat.mul_le_mul_left 4
    ((Nat.mul_le_mul mc pc).trans_eq (by change B^2*B=B^3; ring))).trans ub
  have AU := projected_scale_bounds cap
  have ua : 0<(U:ℝ)*A := by dsimp only [U,A,Fixed.A,Fixed.U]; positivity
  have lo : (U:ℝ)/2 ≤ conditionalScale n a := by
    change (U:ℝ)/2 ≤ (U:ℝ)*A*U/projectionScale n a
    apply (le_div_iff₀ (ua.trans_le AU.1)).mpr
    linarith only [mul_le_mul_of_nonneg_right AU.2 (Nat.cast_nonneg (α:=ℝ) U)]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<M*p)).mpr
  have le : 4*((M:ℝ)*p) ≤ U := by exact_mod_cast prod
  linarith

/-- A prescribed set of primes divides the derivative at a nonnegative
constructor point on the fixed-value fiber. -/
def singularAtSlope (n ell a M : ℕ) (side : Bool) (x t : ℤ) (P : Finset ℕ) (j : ℤ) : Prop :=
  let v := t+(M:ℤ)*j
  let u := x-a*v
  0≤u ∧ 0≤v ∧ ∃ p∈P,
    let s := TryPair.fixedInput n ell (construct n ell u.toNat v.toNat u.toNat v.toNat)
    p ∣ (Marking.horner (a:ℤ) (s.coeffs side)).2.natAbs

open scoped Classical in
/-- Under the actual conditional coefficient distribution, ordinary
dividing primes away from the slope progression modulus cause a derivative
failure in the nonnegative search coordinates with probability ≤ 4 Σ 1/p. -/
theorem constructed_singular_slope_mass {n ell a M : ℕ} (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) (x t : ℤ)
    (mp : 0<M) (mc : M≤(Fixed.B (n.log2+1))^2) (P : Finset ℕ)
    (primes : ∀ p∈P, p.Prime ∧ p≠ell ∧ ¬p∣M ∧ p≤Fixed.B (n.log2+1) ∧ p∣(affineValue n ell a side x).natAbs) :
    let v := fun j : ℤ => t+(M:ℤ)*j
    let u := fun j : ℤ => x-a*v j
    let W := fun j : ℤ => coefficientWeight n (u j,v j)
    let bad := singularAtSlope n ell a M side x t P
    let Z := ∑' j, W j
    0<Z ∧ (∑' j, if bad j then W j else 0)/Z ≤ 4*∑ p∈P,(p:ℝ)⁻¹ := by
  classical
  intro v u W bad Z
  have cap := ((constructed_marks_iff ..).mp mark).2.1
  let S := conditionalScale n a; let μ := projectedConditionalCenter n a x
  let G := fun j : ℤ => coeffGaussian ((t:ℝ)+(M:ℝ)*j) μ S
  let H := coeffGaussian x (lineCenter n a) (projectionScale n a)
  have hp : 0<H := exp_pos _
  have w (j : ℤ) : W j = H * G j := by
    rw [show W j = coefficientWeight n (x-a*v j,v j) from rfl,coefficient_weight_projection]
    simp only [H,G,v,Int.cast_add,Int.cast_mul,Int.cast_natCast,μ,S]
  have ob (p : ℕ) (h : p∈P) := one_singular_slope hn big comp target absent mark side x (primes p h).1 (primes p h).2.1 (primes p h).2.2.2.2
  choose! r hr using ob
  let res := fun p : ℕ => if h : p∈P then (r p - (t:ZMod p))*(ZMod.unitOfCoprime M
    (((primes p h).1.coprime_iff_not_dvd.mpr (primes p h).2.2.1).symm))⁻¹ else 0
  have hit (j : ℤ) (b : bad j) : ∃ p∈P, (j:ZMod p)=res p := by
    obtain ⟨gu,gv,p,hm,zero⟩ := b
    change 0≤u j at gu
    change 0≤v j at gv
    have fixed : ((u j).toNat:ℤ) + a*(v j).toNat = x := by rw [Int.toNat_of_nonneg gu,Int.toNat_of_nonneg gv]; dsimp only [u]; ring
    have cast := (hr p hm (u j).toNat (v j).toNat fixed).mp zero
    have veq : (((v j).toNat:ℕ):ZMod p) = (v j:ZMod p) := by rw [←Int.cast_natCast,Int.toNat_of_nonneg gv]
    rw [veq] at cast
    change (↑(t+(M:ℤ)*j):ZMod p)=r p at cast
    push_cast at cast
    let unit := ZMod.unitOfCoprime M (((primes p hm).1.coprime_iff_not_dvd.mpr (primes p hm).2.2.1).symm)
    refine ⟨p,hm,?_⟩
    simp only [res,dif_pos hm]
    change (j:ZMod p)=(r p-(t:ZMod p))*↑unit⁻¹
    apply (Units.eq_mul_inv_iff_mul_eq unit).mpr
    change (j:ZMod p)*(M:ZMod p)=r p-t
    linear_combination cast
  have bp : 1≤Fixed.B (n.log2+1) := Nat.one_le_two_pow
  have base := slope_width cap mp mc (p:=1) (by decide) bp
  simp only [Nat.cast_one,mul_one] at base
  have est := gaussian_forbidden_slopes P res bad t M μ S (by exact_mod_cast mp) base
    (fun p h => ⟨(primes p h).1.pos,slope_width cap mp mc (primes p h).1.pos (primes p h).2.2.2.1⟩) hit
  change 0 < ∑' j, G j ∧ (∑' j, if bad j then G j else 0)/(∑' j,G j) ≤ _ at est
  change 0 < ∑' j,W j ∧ (∑' j, if bad j then W j else 0)/(∑' j,W j) ≤ _
  simp_rw [w,←mul_ite_zero,tsum_mul_left]
  rw [mul_div_mul_left _ _ hp.ne']
  exact ⟨mul_pos hp est.1,est.2⟩

open scoped Classical in
/-- If the fixed value occurs at a smooth boxed point, ordinary factors
away from the slope modulus discard at most b / 2^(500h) of its fiber. -/
theorem boxed_singular_slope_mass {n ell a M i k : ℕ} (hn : 2≤n)
    (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) (t : ℤ)
    (mp : 0<M) (mc : M≤(Fixed.B (n.log2+1))^2)
    (box : let b := n.log2+1; i≤2*b^2*Fixed.U b*Fixed.A b ∧ k≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell i k i k)
    let m := Marking.value (s.coeffs side) a
    let x := (i:ℤ)+a*k
    let v := fun j : ℤ => t+(M:ℤ)*j
    let W := fun j : ℤ => coefficientWeight n (x-a*v j,v j)
    let P := m.primeFactors.filter (fun p => p≠ell ∧ ¬p∣M)
    let bad := singularAtSlope n ell a M side x t P
    Marking.SquarefreeSmooth s.base m →
      (∑' j, if bad j then W j else 0)/(∑' j, W j) ≤ ((n.log2+1:ℕ):ℝ)/2^(500*Fixed.h (n.log2+1)) := by
  classical
  intro s m x v W P bad smooth
  let b := n.log2+1
  let h := Fixed.h b
  let L := 2^(500*h)
  have lp : 0<L := Nat.pow_pos (by decide)
  obtain ⟨amin,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have small : 10004≤Fixed.d b := le_trans (by decide) big
  have val := congrArg Int.natAbs (signed_box_value hn small target cap grid box side)
  have sign : (markSign n a side).natAbs=1 := by unfold markSign; split <;> decide
  simp only [Int.natAbs_mul,sign,one_mul,Int.natAbs_natCast] at val
  change (affineValue n ell a side x).natAbs=m at val
  have base (p : ℕ) (pm : p∈P) := (constructed_factorBase_iff n ell i k i k p).mp
    (Marking.mem_base.mp (smooth.2.2 p (Nat.prime_of_mem_primeFactors (mem_filter.mp pm).1)
      (Nat.dvd_of_mem_primeFactors (mem_filter.mp pm).1))).1
  have bound := (constructed_singular_slope_mass hn small comp target absent mark side x t mp mc P
    (fun p pm => ⟨(base p pm).1,(mem_filter.mp pm).2.1,(mem_filter.mp pm).2.2,(base p pm).2.1,
      val ▸ Nat.dvd_of_mem_primeFactors (mem_filter.mp pm).1⟩)).2
  apply bound.trans
  have each (p : ℕ) (pm : p∈P) : (p:ℝ)⁻¹ ≤ (L:ℝ)⁻¹ := by
    apply inv_anti₀ (by exact_mod_cast lp)
    apply Nat.cast_le.mpr
    by_contra! below
    have BB : Fixed.B b=L^2 := by
      change 2^(1000*h)=(2^(500*h))^2
      rw [←pow_mul]; congr 1; ring
    exact (base p pm).2.2.1.not_ge (BB ▸ Nat.pow_le_pow_left below.le 2)
  have card := mark_sparsity hn big comp target absent amin cap
    (show _ ∧ _ ∧ _ ∧ _ from ⟨box.1,box.2,box⟩) side smooth
  change 4*m.primeFactors.card≤b at card
  have size := (Nat.mul_le_mul_left 4 (card_le_card (filter_subset (fun p => p≠ell ∧ ¬p∣M) m.primeFactors))).trans card
  have cast : 4*(P.card:ℝ) ≤ b := by exact_mod_cast size
  have sum := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at sum
  refine (mul_le_mul_of_nonneg_left sum (by norm_num : (0:ℝ)≤4)).trans ?_
  rw [←mul_assoc,←div_eq_mul_inv]
  exact (div_le_div_of_nonneg_right cast (Nat.cast_nonneg (α:=ℝ) L)).trans_eq
    (by dsimp only [L,h,b]; push_cast; rfl)

theorem slope_loss_le_sixteenth {b : ℕ} (pos : 0<b) :
    (b:ℝ)/2^(500*Fixed.h b) ≤ 1/16 := by
  have dp := Fixed.degree_pos pos
  have zh : Fixed.z b ≤ Fixed.h b := Nat.le_mul_of_pos_left _ dp
  have hp : 0<Fixed.h b := Nat.mul_pos dp (Nat.succ_pos _)
  have bw : 16*b ≤ 2^(500*Fixed.h b) := calc
    16*b ≤ 2^4*2^(Fixed.z b) := Nat.mul_le_mul_left _ Nat.lt_log2_self.le
    _ ≤ _ := by rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ)<16)).mpr
  rw [one_mul,mul_comm]
  exact_mod_cast bw

end Cogentic.Construction
