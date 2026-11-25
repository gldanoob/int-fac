import Cogentic.FixedWings
import Cogentic.GaussianErrorBudget

namespace Cogentic.Window
open Real

theorem log_scale_le {b : ℕ} (hb : 0 < b) (hd : 16 ≤ Fixed.d b) :
    (Fixed.z b:ℝ) ≤ 16*log (Fixed.d b) := by
  have raw := binary_log_degree b hb hd
  have logs := log_le_log (by positivity : (0:ℝ)<2^(Fixed.z b))
    (by exact_mod_cast raw : (2:ℝ)^(Fixed.z b) ≤ (Fixed.d b:ℝ)^8)
  rw [log_pow,log_pow] at logs
  have half : (1/2:ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  norm_num at logs
  linarith [mul_le_mul_of_nonneg_left half (Nat.cast_nonneg (α:=ℝ) (Fixed.z b))]

/-- The fixed schedule absorbs any fixed multiple of the squared
logarithm in the exponent of a negative power of B. -/
theorem fixed_band_power_savings (K : ℝ) (hK : 1 ≤ K) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀,
      (Fixed.B b:ℝ)^(-17/200:ℝ) ≤ exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨k,hk⟩ := exists_nat_ge ((32*K)^2)
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows (max 16 k)
  refine ⟨max 1 b₀,fun b big => ?_⟩
  have hb : 0 < b := (le_max_left ..).trans big
  have degree := grow b ((le_max_right ..).trans big)
  let d : ℝ := Fixed.d b
  let z : ℝ := Fixed.z b
  have d16 : 16 ≤ Fixed.d b := (le_max_left ..).trans degree
  have dp : 0 < d := by dsimp [d]; exact_mod_cast (show 0 < Fixed.d b by omega)
  have zp : 0 ≤ z := Nat.cast_nonneg _
  have zlog : z ≤ 16*log d := log_scale_le hb d16
  have root : 32*K ≤ sqrt d := (le_sqrt (by linarith) dp.le).mpr
    (hk.trans (by dsimp [d]; exact_mod_cast (show k ≤ Fixed.d b from (le_max_right ..).trans degree)))
  have sqroot := sq_sqrt dp.le
  have logd : log d ≤ 2*sqrt d := by
    have t := log_le_sub_one_of_pos (sqrt_pos.mpr dp)
    rw [log_sqrt dp.le] at t; linarith
  have Kz : K*z ≤ d := by
    have p := mul_le_mul_of_nonneg_left (zlog.trans (by linarith : 16*log d ≤ 32*sqrt d)) (by linarith : 0≤K)
    nlinarith [mul_le_mul_of_nonneg_right root (sqrt_nonneg d)]
  have lnB : log (Fixed.B b) = 1000*d*z*log 2 := by
    unfold Fixed.B Fixed.beta Fixed.h
    rw [Nat.cast_pow,Nat.cast_ofNat,log_pow]
    push_cast
    dsimp [d,z]; ring
  have bp : (0:ℝ) < Fixed.B b := by unfold Fixed.B; positivity
  rw [rpow_def_of_pos bp,lnB,exp_le_exp]
  change 1000*d*z*log 2*(-17/200) ≤ -K*z^2
  have save := mul_le_mul_of_nonneg_right Kz zp
  have two : 1/2 ≤ log 2 := by linarith [log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_left two (mul_nonneg dp.le zp)]

/-- The moderate-frequency estimate applies to every center with u≥d in
the executable search, with the same threshold over the allowed centers. -/
theorem fixed_middle_savings (K : ℝ) (hK : 1 ≤ K) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ u : ℝ, (Fixed.d b:ℝ) ≤ u →
      exp ((1/4-u/(1152*(log (8*u+1))^3))/4) ≤ exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨u₀,bound⟩ := middle_log_square_decay (256*K) (by linarith)
  obtain ⟨k,hk⟩ := exists_nat_ge u₀
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows (max 16 k)
  refine ⟨max 1 b₀,fun b big u fit => ?_⟩
  have deg := grow b ((le_max_right ..).trans big)
  have hd : 16 ≤ Fixed.d b := (le_max_left ..).trans deg
  have du : 0 < (Fixed.d b:ℝ) := by exact_mod_cast (show 0 < Fixed.d b by omega)
  have cutoff : u₀ ≤ u := hk.trans ((show (k:ℝ) ≤ Fixed.d b by exact_mod_cast (show k ≤ Fixed.d b from (le_max_right ..).trans deg)).trans fit)
  refine (bound u cutoff).trans (exp_le_exp.mpr ?_)
  have zlog := log_scale_le (show 0 < b from (le_max_left ..).trans big) hd
  have zfit : (Fixed.z b:ℝ) ≤ 16*log u := zlog.trans (by linarith [log_le_log du fit])
  have sq := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (Fixed.z b)) zfit 2
  linarith [mul_le_mul_of_nonneg_left sq (by linarith : 0≤K)]

end Cogentic.Window
