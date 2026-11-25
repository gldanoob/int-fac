import Cogentic.PolynomialLaw
namespace Cogentic.Construction
open Real Cogentic.Window

theorem PrescribedRows.weight_normalizer {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) :
    let b := n.log2+1
    let W := (Fixed.U b:ℝ)*Fixed.A b*Fixed.U b
    let Q := prodPrimes R.primes
    let Z := ∑' k : {v : ℤ×ℤ // R.compatible side v.1 v.2}, coefficientWeight n k.val
    0<Z ∧ |W/(Q*Z)-1| ≤ 18*exp (-(Fixed.U b:ℝ)) := by
  intro b W Q Z
  obtain ⟨_,_,_,_,_,zp,normal,_⟩ := R.coefficient_law target side (Nat.zero_le (Fixed.A b))
  let H := R.hitProduct 0
  let M := prodPrimes (R.miss 0)
  let p := projectionScale n 0
  change |((p/H)*(conditionalScale n 0/M))/Z-1| ≤ _ at normal
  have pp : 0<p := by
    change 0 < sqrt (((Fixed.U b:ℝ)*Fixed.A b)^2+(((0:ℕ):ℝ)*(Fixed.U b:ℝ))^2)
    simp only [Nat.cast_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero]
    have u : 0 < Fixed.U b := Nat.pow_pos (by decide)
    have a : 0 < Fixed.A b := Nat.pow_pos (by decide)
    positivity
  have hm : H*M=Q := by
    rw [Nat.mul_comm]
    exact Finset.prod_sdiff (f := id) (show R.hit 0 ⊆ R.primes from Finset.filter_subset ..)
  have mod : (H:ℝ)*M=Q := by exact_mod_cast hm
  have eq : ((p/H)*(conditionalScale n 0/M))/Z = W/(Q*Z) := by
    change ((p/H)*(W/p/M))/Z=_
    rw [←mod]
    field_simp
  exact ⟨zp,eq ▸ normal⟩

/-- Prescribing up to two actual polynomial roots has probability
(1 + O(exp(-U))) divided by the product of their distinct primes. -/
theorem PrescribedRows.admission_probability {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) :
    let b := n.log2+1
    let total := ∑' k : ℤ×ℤ, coefficientWeight n k
    let accepted := ∑' k : {v : ℤ×ℤ // R.compatible side v.1 v.2}, coefficientWeight n k.val
    0<total ∧ 0<accepted ∧
      |(prodPrimes R.primes:ℝ)*(accepted/total)-1| ≤ 72*exp (-(Fixed.U b:ℝ)) := by
  classical
  intro b total accepted
  let S : PrescribedRows n ell := ⟨∅,fun _ => 0,by simp,by simp,by simp,by simp⟩
  have all (k : ℤ×ℤ) : S.compatible side k.1 k.2 := by simp [S,compatible]
  let iso : {k : ℤ×ℤ // S.compatible side k.1 k.2} ≃ ℤ×ℤ :=
    ⟨Subtype.val,fun k => ⟨k,all k⟩,fun _ => rfl,fun _ => rfl⟩
  have full : (∑' k : {k : ℤ×ℤ // S.compatible side k.1 k.2}, coefficientWeight n k.val) = total :=
    iso.tsum_eq (coefficientWeight n)
  have ⟨tp,un⟩ := S.weight_normalizer target side
  rw [full] at tp un
  have unit : prodPrimes S.primes=1 := by simp [S,prodPrimes]
  rw [unit,Nat.cast_one,one_mul] at un
  obtain ⟨ap,cn⟩ := R.weight_normalizer target side
  let W := (Fixed.U b:ℝ)*Fixed.A b*Fixed.U b
  let Q : ℝ := prodPrimes R.primes
  let e := exp (-(Fixed.U b:ℝ))
  let x := W/(Q*accepted)
  let y := W/total
  change |x-1| ≤ 18*e at cn
  change |y-1| ≤ 18*e at un
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos _)
  have vp : 0<Fixed.v b := Nat.mul_pos dp (Nat.mul_pos dp (Nat.succ_pos _))
  have up : 6 ≤ (Fixed.U b:ℝ) := by
    exact_mod_cast (by decide : 6 ≤ 2^3).trans
      (Nat.pow_le_pow_right (by decide : 0<2) (by change 3≤100000*Fixed.v b; omega))
  have big : 36 ≤ exp (Fixed.U b:ℝ) := by
    have six := pow_div_factorial_le_exp 6 (by norm_num) 3
    norm_num at six
    exact six.trans (exp_le_exp.mpr up)
  have little : 18*e ≤ 1/2 := by
    dsimp only [e]; rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]; linarith only [big]
  have half : 1/2 ≤ x := by linarith only [(abs_le.mp (cn.trans little)).1]
  have xpos : 0<x := by linarith
  have diff : |y-x| ≤ 36*e := by
    have h := abs_sub (y-1) (x-1)
    rw [sub_sub_sub_cancel_right] at h
    linarith only [h,cn,un]
  have rat : |y/x-1| ≤ 72*e := by
    rw [←div_self xpos.ne' (a:=x),←sub_div,abs_div,abs_of_pos xpos,div_le_iff₀ xpos]
    linarith only [diff,mul_le_mul_of_nonneg_right half (show 0≤72*e by dsimp [e]; positivity)]
  have qp : 0<Q := by dsimp only [Q]; exact_mod_cast (R.subprod_bounds (s:=R.primes) Finset.Subset.rfl).1
  have wp : 0<W := by
    have u : 0<Fixed.U b := Nat.pow_pos (by decide)
    have a : 0<Fixed.A b := Nat.pow_pos (by decide)
    dsimp [W]; positivity
  have eq : y/x=Q*(accepted/total) := by dsimp only [y,x]; field_simp
  exact ⟨tp,ap,eq ▸ rat⟩

end Cogentic.Construction
