import Cogentic.GaussianJoint

open Real

namespace Cogentic.Window

noncomputable section

/-- Under the source's coefficient widths and U ≥ 4B⁴, both scalar
    progressions in the conditioned two-point law have exponentially
    small Gaussian normalization errors. -/
theorem two_point_schedule_widths (a A U B Q M : ℝ) (hA : 1 ≤ A) (ha : |a| ≤ A)
    (hB : 1 ≤ B) (hU : 4*B^4 ≤ U) (hQ : 0 < Q) (hM : 0 < M)
    (qmax : Q ≤ B^2) (mmax : M ≤ B^2) :
    let S := Real.sqrt ((U*A)^2+a^2*U^2)
    let t := U*A*U/S
    let τ := S/Q
    let υ := t/M
    2 ≤ τ ∧ 2 ≤ υ ∧
      6*max (3*Real.exp (-π*τ^2)) (3*Real.exp (-π*υ^2)) ≤ 18*Real.exp (-U) := by
  let S := Real.sqrt ((U*A)^2+a^2*U^2)
  let t := U*A*U/S
  have bp : 0 < B := by linarith
  have up : 0 < U := (show 0 < 4*B^4 by positivity).trans_le hU
  have ap : 0 < A := by linarith
  have sp : 0 < S := by dsimp [S]; positivity
  have sq : S^2=(U*A)^2+a^2*U^2 := Real.sq_sqrt (by positivity)
  have aa := pow_le_pow_left₀ (abs_nonneg a) ha 2
  rw [sq_abs] at aa
  have lo : U*A ≤ S := by nlinarith [mul_self_nonneg a,mul_nonneg (sq_nonneg a) (sq_nonneg U)]
  have hi : S ≤ 2*(U*A) := by
    nlinarith [mul_le_mul_of_nonneg_right aa (sq_nonneg U),mul_pos up ap,sq_nonneg (U*A)]
  have tl : U/2 ≤ t := by
    dsimp only [t]
    rw [le_div_iff₀ sp]
    nlinarith only [mul_le_mul_of_nonneg_left hi up.le]
  have mag : 2 ≤ U/(2*B^2) := by
    rw [le_div_iff₀ (by positivity)]
    have b2 : 1 ≤ B^2 := one_le_pow₀ hB
    nlinarith [mul_nonneg (sq_nonneg B) (show 0 ≤ B^2-1 by linarith)]
  have root : U ≤ (U/(2*B^2))^2 := by
    rw [div_pow,le_div_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hU up.le]
  have boost (X J : ℝ) (hJ : 0 < J) (jmax : J ≤ B^2) (loX : U/2 ≤ X) :
      2 ≤ X/J ∧ U ≤ π*(X/J)^2 := by
    have comp : U/(2*B^2) ≤ X/J := by
      rw [div_le_div_iff₀ (by positivity) hJ]
      nlinarith [mul_le_mul_of_nonneg_left jmax up.le,
        mul_le_mul_of_nonneg_right loX (sq_nonneg B)]
    have ss := pow_le_pow_left₀ (show 0 ≤ U/(2*B^2) by positivity) comp 2
    have πone : (1:ℝ) ≤ π := by linarith [Real.pi_gt_three]
    have πscale := mul_le_mul_of_nonneg_right πone (sq_nonneg (X/J))
    rw [one_mul] at πscale
    exact ⟨mag.trans comp,(root.trans ss).trans πscale⟩
  have first := boost S Q hQ qmax (by nlinarith [lo,mul_le_mul_of_nonneg_left hA up.le])
  have second := boost t M hM mmax tl
  refine ⟨first.1,second.1,?_⟩
  have one : Real.exp (-π*(S/Q)^2) ≤ Real.exp (-U) := Real.exp_le_exp.mpr (by linarith [first.2])
  have two : Real.exp (-π*(t/M)^2) ≤ Real.exp (-U) := Real.exp_le_exp.mpr (by linarith [second.2])
  change 6*max (3*Real.exp (-π*(S/Q)^2)) (3*Real.exp (-π*(t/M)^2)) ≤ _
  have h := max_le (mul_le_mul_of_nonneg_left one (by norm_num : (0:ℝ) ≤ 3))
    (mul_le_mul_of_nonneg_left two (by norm_num : (0:ℝ) ≤ 3))
  linarith

/-- Movement of the second conditional scalar mean as the first scalar
    coordinate moves. The regression coefficient is uniformly at most two
    on [0,A] for the source's widths. -/
theorem conditional_evaluation_center (a b A x c₀ c₁ U : ℝ) (hA : 0 < A) (hU : 0 < U)
    (ha : 0 ≤ a) (ha' : a ≤ A) (hb : 0 ≤ b) (hb' : b ≤ A) :
    let v := (U*A)^2+a^2*U^2
    let μ := c₀+a*c₁
    let m := c₁+a*U^2/v*(x-μ)
    |x+(b-a)*m-(c₀+b*c₁)| ≤ 2*|x-μ| := by
  let v := (U*A)^2+a^2*U^2
  let μ := c₀+a*c₁
  let k := ((U*A)^2+a*b*U^2)/v
  have vp : 0 < v := by dsimp [v]; positivity
  have kp : 0 ≤ k := by dsimp only [k]; positivity
  have k2 : k ≤ 2 := by
    dsimp only [k]
    rw [div_le_iff₀ vp]
    dsimp only [v]
    have ab := mul_le_mul ha' hb' hb hA.le
    nlinarith [mul_le_mul_of_nonneg_right ab (sq_nonneg U),mul_nonneg (sq_nonneg a) (sq_nonneg U)]
  change |x+(b-a)*(c₁+a*U^2/v*(x-μ))-(c₀+b*c₁)| ≤ 2*|x-μ|
  rw [show x+(b-a)*(c₁+a*U^2/v*(x-μ))-(c₀+b*c₁) = k*(x-μ) by
    dsimp only [k,μ]; field_simp; dsimp only [v]; ring,abs_mul,abs_of_nonneg kp]
  exact mul_le_mul_of_nonneg_right k2 (abs_nonneg _)

end

end Cogentic.Window
