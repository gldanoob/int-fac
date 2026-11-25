import Cogentic.SearchScale

namespace Cogentic.CompanionSplitCost

open Real

/-- The scale in the exponent defining `L_N[2/3,C]`, with natural logarithms. -/
noncomputable def scale (n : ℕ) : ℝ :=
  (log n) ^ (2 / 3 : ℝ) * (log (log n)) ^ (1 / 3 : ℝ)

private theorem log_large {n : ℕ} (hn : 64 ≤ n) : 3 ≤ log n := by
  have h : (64 : ℝ) ≤ n := by exact_mod_cast hn
  apply (le_log_iff_exp_le (by linarith : (0 : ℝ) < n)).mpr
  have cube := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 3
  rw [show exp 3 = (exp 1)^3 by rw [← exp_nat_mul]; norm_num]
  linarith

/-- Absorb the complete right hand side of Cogentic Theorem 1.2(a), including
its prefactor and shifted iterated logarithm, into the two-thirds bound. -/
theorem splitter_cost {n M : ℕ} (hn : 64 ≤ n) (hM : 1 ≤ M) {C₁ A D : ℝ}
    (hc : 0 ≤ C₁) (ha : 0 ≤ A) (size : log M ≤ exp (D * scale n)) :
    C₁ * exp (A * sqrt (log n) * log (log ((n : ℝ) + 16))) * log M * (log n)^2 ≤
      exp ((C₁ + 12*A + D + 12) * scale n) := by
  let L := log n
  let z := log L
  have hL : 3 ≤ L := log_large hn
  have lp : 0 < L := by linarith
  have hz : 1 ≤ z := (le_log_iff_exp_le lp).mpr (by linarith [exp_one_lt_d9])
  have hpow : L ^ (2/3:ℝ) ≤ scale n := by
    exact le_mul_of_one_le_right (rpow_nonneg lp.le _) (one_le_rpow hz (by norm_num))
  have hs : 1 ≤ scale n := (one_le_rpow (by linarith : 1 ≤ L) (by norm_num)).trans hpow
  have zbound : z ≤ 6 * L ^ (1/6 : ℝ) := by
    have := log_le_rpow_div lp.le (by norm_num : (0:ℝ) < 1/6)
    dsimp [z]; linarith
  have n64 : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have npos : (0 : ℝ) < n := by linarith
  have logTwo : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have shifted : log (log ((n : ℝ)+16)) ≤ 2*z := by
    have inner := log_le_log (by linarith : (0:ℝ)<n+16)
      (by linarith : (n:ℝ)+16 ≤ 2*n)
    rw [log_mul (by norm_num) npos.ne'] at inner
    have mid : log ((n:ℝ)+16) ≤ 2*L := by change log 2 + L ≥ _ at inner; linarith
    have outer := log_le_log (log_pos (by linarith : (1:ℝ)<n+16)) mid
    rw [log_mul (by norm_num) lp.ne'] at outer
    change _ ≤ log 2 + z at outer
    linarith
  have split : sqrt L * log (log ((n:ℝ)+16)) ≤ 12*scale n := by
    calc
      _ ≤ sqrt L * (2*(6*L^(1/6:ℝ))) := by gcongr; linarith
      _ = 12 * L^(2/3:ℝ) := by
        rw [sqrt_eq_rpow,show (2/3:ℝ) = 1/2+1/6 by norm_num,rpow_add lp]; ring
      _ ≤ _ := by gcongr
  have poly : z ≤ 6*scale n := zbound.trans (by
    gcongr; exact (rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L)
      (by norm_num : (1/6:ℝ) ≤ 2/3)).trans hpow)
  have const : C₁ ≤ exp (C₁*scale n) :=
    (by linarith [add_one_le_exp C₁] : C₁ ≤ exp C₁).trans (exp_le_exp.mpr
      (le_mul_of_one_le_right hc hs))
  have sqbound : L^2 ≤ exp (12*scale n) := by
    rw [show L^2 = exp (2*z) by rw [show (2:ℝ)*z = (2:ℕ)*z by norm_num,
      exp_nat_mul,exp_log lp]]
    exact exp_le_exp.mpr (by linarith)
  have logMpos := log_nonneg (by exact_mod_cast hM : (1:ℝ) ≤ M)
  have expbound : exp (A * sqrt L * log (log ((n:ℝ)+16))) ≤ exp (12*A*scale n) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left split ha]
  change C₁ * exp (A * sqrt L * _) * log M * L^2 ≤ _
  calc
    _ ≤ exp (C₁*scale n) * exp (12*A*scale n) * exp (D*scale n) * exp (12*scale n) := by
      apply mul_le_mul _ sqbound (sq_nonneg L) (by positivity)
      apply mul_le_mul _ size logMpos (by positivity)
      exact mul_le_mul const expbound (exp_pos _).le (exp_pos _).le
    _ = _ := by rw [← exp_add,← exp_add,← exp_add]; congr 1; ring

/-- Convert the integer loop budget to the natural-logarithm two-thirds scale. -/
theorem binary_scale_le {n : ℕ} (hn : 64 ≤ n) :
    (TwoThirdsCost.scale (n.log2+1) : ℝ) ≤ 65 * scale n := by
  let b := n.log2+1
  have bp : 0 < b := Nat.succ_pos _
  have rounded : TwoThirdsCost.scale b ≤ 13*Fixed.v b := by
    apply (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp
    calc
      _ ≤ 32*(b^2 * Fixed.z b) := (TwoThirdsCost.scale_cubed b bp.ne').2
      _ ≤ 32*(64*(Fixed.v b)^3) := Nat.mul_le_mul_left _ (Fixed.scale_bounds bp).2
      _ ≤ _ := by rw [Nat.mul_pow]; omega
  have vr := Concrete.two_thirds_scale (log_large hn)
  change (Fixed.v b:ℝ) ≤ 5*(log n)^(2/3:ℝ)*(log (log n))^(1/3:ℝ) at vr
  have sr : (TwoThirdsCost.scale b:ℝ) ≤ 13*(Fixed.v b:ℝ) := by exact_mod_cast rounded
  dsimp [scale]
  linarith

/-- The actual double-exponential cap proved for the saturated search output
implies the logarithmic exponent-size hypothesis of the companion splitter. -/
theorem log_of_saturated_bound {n M : ℕ} (hn : 64 ≤ n) (hM : 0 < M)
    (bound : M ≤ 2^(2^(2017*TwoThirdsCost.scale (n.log2+1)))) :
    log M ≤ exp (131105 * scale n) := by
  let b := n.log2+1
  have sr := binary_scale_le hn
  let k := 2017*TwoThirdsCost.scale b
  have kb : (k:ℝ) ≤ 131105 * scale n := by
    dsimp [k,b]; push_cast; linarith
  have logTwo : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog := log_le_log (by exact_mod_cast hM : (0:ℝ)<M)
    (by exact_mod_cast bound : (M:ℝ) ≤ (2:ℝ)^((2:ℕ)^k))
  rw [log_pow] at hlog
  push_cast at hlog
  calc
    log M ≤ (2:ℝ)^k * log 2 := hlog
    _ ≤ (2:ℝ)^k := (mul_le_mul_of_nonneg_left logTwo (by positivity)).trans_eq (mul_one _)
    _ = exp ((k:ℝ)*log 2) := by rw [exp_nat_mul, exp_log (by norm_num : (0:ℝ)<2)]
    _ ≤ _ := exp_le_exp.mpr (((mul_le_mul_of_nonneg_left logTwo (Nat.cast_nonneg k)).trans_eq
      (mul_one _)).trans kb)

/-- Apply the paper's cost expression directly to the cap in
`Cogentic.TryPair.saturated_size`. -/
theorem splitter_cost_of_saturated_bound {n M : ℕ} (hn : 64 ≤ n) (hM : 0 < M)
    (bound : M ≤ 2^(2^(2017*TwoThirdsCost.scale (n.log2+1)))) {C₁ A : ℝ}
    (hc : 0 ≤ C₁) (ha : 0 ≤ A) :
    C₁ * exp (A * sqrt (log n) * log (log ((n : ℝ) + 16))) * log M * (log n)^2 ≤
      exp ((C₁ + 12*A + 131117) * scale n) := by
  simpa only [show ∀ x : ℝ, x + 131105 + 12 = x + 131117 by intro x; ring] using
    splitter_cost hn hM hc ha (log_of_saturated_bound hn hM bound)

end Cogentic.CompanionSplitCost

#print axioms Cogentic.CompanionSplitCost.splitter_cost_of_saturated_bound
