import Cogentic.FixedErrorBudget
import Cogentic.ProgressionCorrection
import Cogentic.ScalarSteps

namespace Cogentic.Construction
open Real Finset Cogentic.Window
noncomputable section

/-- Adding prime divisors to a conductor can only increase its coprime
class correction. -/
theorem coprime_factor_ratio_one_le {q q' : ℕ} (qpos : 0 < q) (qp : 0 < q') (div : q∣q') :
    1 ≤ coprimeFactor q'/coprimeFactor q := by
  obtain ⟨k,eq⟩ := div
  have kp : 0 < k := by rw [eq] at qp; exact Nat.pos_of_mul_pos_left qp
  rw [eq,coprime_factor_quotient _ _ qpos kp]
  apply Finset.one_le_prod
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
  have top : 1 < (p:ℝ) := by exact_mod_cast prime.one_lt
  exact (one_le_div (sub_pos.mpr top)).mpr (by linarith only [top])

theorem PrescribedRows.second_correction_one_le {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (am : a' < Fixed.rootBase n) (ep : 0 < ell) (different : a'≠a) (side : Bool) :
    1 ≤ coprimeFactor (R.secondStep a a' side).natAbs/coprimeFactor (firstStep n ell a' side).natAbs := by
  apply coprime_factor_ratio_one_le (Int.natAbs_pos.mpr (firstStep_size am ep side).2)
    (Int.natAbs_pos.mpr (R.secondStep_size am ep different side).2)
  unfold PrescribedRows.secondStep
  rw [Int.natAbs_mul,Int.natAbs_mul]
  exact dvd_mul_of_dvd_left (dvd_mul_right ..) _

/-- All losses in the integrated separated-pair estimate, including
exceptional first observations amplified by the all-pairs upper bound,
decay at an arbitrary prescribed logarithmic-square rate on the schedule. -/
theorem integrated_difference_savings (K : ℝ) (hk : 1 ≤ K) :
    ∃ b₀ : ℕ, ∀ b≥b₀, ∀ (P₁ P₂ correction C₀ : ℝ),
    let B : ℝ := Fixed.B b
    let e := exp (-K*(Fixed.z b:ℝ)^2)
    let rate := correction*P₂
    let η := 720*B^(-199/400:ℝ)+360*exp (-(Fixed.U b:ℝ))
    let τ := (1+90*exp (-(Fixed.U b:ℝ)))*(8*exp (-π*((b:ℝ)^3)^2/2))
    8/B ≤ P₁ → 8/B ≤ P₂ → 1 ≤ correction →
    (C₀*e+η)*rate*P₁+exp (10*(Fixed.h b:ℝ))*η*(P₁*P₂)+(2+rate)*τ ≤
      (C₀+4344)*e*(rate*P₁) := by
  obtain ⟨n,save⟩ := fixed_band_power_savings K hk
  refine ⟨max n 3000,?_⟩
  intro b huge P₁ P₂ correction C₀ B e rate η τ p₁ p₂ c
  obtain ⟨one,large⟩ := max_le_iff.mp huge
  have br : 3000 ≤ (b:ℝ) := by exact_mod_cast large
  have bn : 0 < b := by omega
  have Bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have Bo : 1 ≤ B := by dsimp only [B]; exact_mod_cast (show 1≤Fixed.B b from Nat.one_le_two_pow)
  have epos : 0 ≤ e := (exp_pos _).le
  have cp : 0 ≤ correction := zero_le_one.trans c
  have xp : 0 ≤ P₁ := (by positivity : 0 ≤ 8/B).trans p₁
  have yp : 0 ≤ P₂ := (by positivity : 0 ≤ 8/B).trans p₂
  have ratePos : 0 ≤ rate := mul_nonneg cp yp
  have saveB : B^(-17/200:ℝ) ≤ e := save b one
  let H := log B
  let h : ℝ := Fixed.h b
  have logB : H=1000*h*log 2 := by
    dsimp only [H,h,B,Fixed.B,Fixed.beta]
    simp only [Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul]
  have low : 500*h ≤ H := by
    rw [logB]
    have bound := mul_le_mul_of_nonneg_left (show (1/2:ℝ)≤log 2 by linarith [log_two_gt_d9]) (show 0≤1000*h by dsimp [h]; positivity)
    linarith only [bound]
  have h0 : 0 ≤ H := log_nonneg Bo
  have dpos := Fixed.degree_pos bn
  obtain ⟨_,_,_,bb,_,uu,_⟩ := dyadic_data bn
  have BU : Fixed.B b ≤ Fixed.U b := by
    rw [bb,uu]
    apply Nat.pow_le_pow_right (Nat.pow_pos (by decide))
    omega
  have ularge : B ≤ (Fixed.U b:ℝ) := by dsimp [B]; exact_mod_cast BU
  have uf : exp (-(Fixed.U b:ℝ)) ≤ B^(-199/400:ℝ) := by
    rw [rpow_def_of_pos Bp,exp_le_exp]
    have hl : H≤B := log_le_self Bp.le
    change -(Fixed.U b:ℝ)≤H*(-199/400)
    linarith only [h0,hl,ularge]
  have etaBound : η ≤ 1080*B^(-199/400:ℝ) := by
    dsimp only [η]
    linarith only [uf]
  have tilted : exp (10*h)*B^(-199/400:ℝ) ≤ B^(-17/200:ℝ) := by
    rw [rpow_def_of_pos Bp,rpow_def_of_pos Bp,←exp_add,exp_le_exp]
    change 10*h+H*(-199/400) ≤ H*(-17/200)
    linarith only [low,h0]
  have amp : exp (10*h)*η ≤ 1080*e := by
    have a := mul_le_mul_of_nonneg_left etaBound (exp_pos (10*h)).le
    linarith only [a,mul_le_mul_of_nonneg_left (tilted.trans saveB) (by norm_num : (0:ℝ)≤1080)]
  have etaSmall : η ≤ 1080*e := etaBound.trans (mul_le_mul_of_nonneg_left
    ((rpow_le_rpow_of_exponent_le Bo (by norm_num : (-199/400:ℝ)≤ -17/200)).trans saveB) (by norm_num))
  have zcap : Fixed.z b ≤ b := (Nat.log2_lt bn.ne').mpr (Nat.lt_two_pow_self (n:=b))
  have hcap : h ≤ (b:ℝ)^2 := by
    dsimp only [h,Fixed.h]
    rw [pow_two]
    exact_mod_cast Nat.mul_le_mul (Fixed.degree_le_bits b) zcap
  have Hcap : H ≤ 1000*(b:ℝ)^2 := by
    rw [logB]
    have l := mul_le_mul_of_nonneg_left (show log (2:ℝ) ≤ 1 by linarith [log_two_lt_d9])
      (show 0≤1000*h by dsimp [h]; positivity)
    linarith only [l,hcap]
  have b1 : 1 ≤ (b:ℝ) := by linarith only [br]
  have b4 : 3000 ≤ (b:ℝ)^4 := br.trans (le_self_pow₀ b1 (by decide))
  have power : 3000*(b:ℝ)^2 ≤ ((b:ℝ)^3)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right b4 (sq_nonneg (b:ℝ))]
  have logTail : -π*((b:ℝ)^3)^2/2 ≤ -(3*H) := by
    linarith only [power,Hcap,mul_le_mul_of_nonneg_right pi_gt_three.le (sq_nonneg ((b:ℝ)^3)),
      sq_nonneg ((b:ℝ)^3)]
  have lowPow := (rpow_le_rpow_of_exponent_le Bo (by norm_num : (-1:ℝ) ≤ -17/200)).trans saveB
  rw [rpow_neg_one] at lowPow
  have tail : exp (-π*((b:ℝ)^3)^2/2) ≤ e/B^2 := by
    apply (exp_le_exp.mpr logTail).trans
    rw [exp_neg,show 3*H=(3:ℕ)*log B by norm_num [H],exp_nat_mul,exp_log Bp]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos Bp)).mpr lowPow |>.trans_eq' ?_
    field_simp
  have tcap : τ ≤ 728*(e/B^2) := by
    apply (mul_le_mul (show 1+90*exp (-(Fixed.U b:ℝ)) ≤ 91 by
      linarith only [exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg (α:=ℝ) (Fixed.U b)))])
      (mul_le_mul_of_nonneg_left tail (by norm_num : (0:ℝ)≤8)) (by positivity) (by norm_num)).trans_eq
    ring
  have xlow : B⁻¹ ≤ P₁ := (show B⁻¹≤8/B by rw [←one_div]; gcongr; norm_num).trans p₁
  have ylow : B⁻¹ ≤ P₂ := (show B⁻¹≤8/B by rw [←one_div]; gcongr; norm_num).trans p₂
  have normalized : (B^2)⁻¹ ≤ P₁*P₂ := by
    rw [pow_two,mul_inv_rev]
    exact mul_le_mul xlow ylow (inv_nonneg.mpr Bp.le) xp
  have baseSmall : (B^2)⁻¹ ≤ P₁ := by
    exact (inv_anti₀ Bp (le_self_pow₀ Bo (by decide))).trans xlow
  have q : P₁*P₂ ≤ rate*P₁ := by
    have p := mul_le_mul_of_nonneg_right c (mul_nonneg xp yp)
    dsimp only [rate]; linarith only [p]
  have cT : τ ≤ 728*e*(rate*P₁) := by
    have m := mul_le_mul_of_nonneg_left (normalized.trans q) (show 0≤728*e by positivity)
    apply tcap.trans; simpa only [div_eq_mul_inv,mul_assoc] using m
  have oT : τ ≤ 728*e*P₁ := by
    apply tcap.trans
    simpa only [div_eq_mul_inv,mul_assoc] using mul_le_mul_of_nonneg_left baseSmall (show 0≤728*e by positivity)
  have rt := mul_le_mul_of_nonneg_left oT ratePos
  have am := mul_le_mul_of_nonneg_right amp (mul_nonneg xp yp)
  have swap := mul_le_mul_of_nonneg_left q (show 0≤1080*e by positivity)
  have ae := mul_le_mul_of_nonneg_right etaSmall (mul_nonneg ratePos xp)
  change (C₀*e+η)*rate*P₁+exp (10*h)*η*(P₁*P₂)+(2+rate)*τ ≤ _
  linarith only [ae,am,swap,cT,rt]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.integrated_difference_savings
#print axioms Cogentic.Construction.PrescribedRows.second_correction_one_le
