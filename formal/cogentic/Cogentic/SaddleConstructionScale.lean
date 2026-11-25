import Cogentic.FixedSchedule

open Real

namespace Cogentic.Window

/-- The finite power envelopes used by construction give the real center
    and relative-width ranges used in the Mellin estimates. -/
theorem construction_power_window (x Y S : ℝ) (d : ℕ) (hx : 1 < x)
    (lower : x^(90000*d) ≤ Y) (upper : Y ≤ x^(110000*d))
    (wlo : x^85 ≤ Y/S) (whi : Y/S ≤ x^170) :
    let B := x^1000
    0 < S ∧ 1 ≤ Y ∧
    90*(d:ℝ) ≤ Real.log Y/Real.log B ∧ Real.log Y/Real.log B ≤ 110*(d:ℝ) ∧
    B^(17/200:ℝ) ≤ Y/S ∧ Y/S ≤ B^(17/100:ℝ) ∧
    (4 ≤ d → Y/S ≤ Y^(1/2000:ℝ)) := by
  let B := x^1000
  have xp : 0 < x := by linarith
  have yp : 0 < Y := (pow_pos xp _).trans_le lower
  have y1 : 1 ≤ Y := (one_le_pow₀ hx.le).trans lower
  have rp : 0 < Y/S := (pow_pos xp _).trans_le wlo
  have sp : 0 < S := (div_pos_iff_of_pos_left yp).mp rp
  have lh : 0 < Real.log x := Real.log_pos hx
  have H : Real.log B = 1000*Real.log x := by dsimp [B]; rw [Real.log_pow]; norm_num
  have hp : 0 < Real.log B := by rw [H]; positivity
  have al := Real.log_le_log (pow_pos xp _) lower
  have ah := Real.log_le_log yp upper
  rw [Real.log_pow] at al ah
  push_cast at al ah
  have width (k : ℕ) (r : ℝ) (hr : 1000*r=k) : B^r=x^k := by
    dsimp [B]
    rw [← Real.rpow_natCast x 1000,← Real.rpow_mul xp.le,show (↑(1000:ℕ):ℝ)*r = k by simpa using hr,Real.rpow_natCast]
  have wl : B^(17/200:ℝ) = x^85 := width 85 _ (by norm_num)
  have wu : B^(17/100:ℝ) = x^170 := width 170 _ (by norm_num)
  refine ⟨sp,y1,?_,?_,wl.trans_le wlo,whi.trans_eq wu.symm,?_⟩
  · rw [le_div_iff₀ hp,H]
    nlinarith only [al]
  · rw [div_le_iff₀ hp,H]
    nlinarith only [ah]
  · intro hd
    refine whi.trans ?_
    rw [Real.rpow_def_of_pos yp]
    apply (Real.log_le_iff_le_exp (pow_pos xp _)).mp
    rw [Real.log_pow]
    have dr : (4:ℝ) ≤ d := by exact_mod_cast hd
    norm_num
    nlinarith only [al,mul_le_mul_of_nonneg_right dr lh.le,lh.le]

/-- Identify the base of the dyadic construction with the actual
    smoothness bound consumed by the analytic pipeline. -/
theorem fixed_base_power (b : ℕ) : ((2:ℝ)^(Fixed.h b))^1000 = (Fixed.B b:ℝ) := by
  dsimp [Fixed.B,Fixed.beta]
  push_cast
  rw [← pow_mul,Nat.mul_comm]

theorem fixed_construction_window {b : ℕ} (h : 0 < Fixed.h b) (Y S : ℝ)
    (lower : ((2:ℝ)^(Fixed.h b))^(90000*Fixed.d b) ≤ Y)
    (upper : Y ≤ ((2:ℝ)^(Fixed.h b))^(110000*Fixed.d b))
    (wlo : ((2:ℝ)^(Fixed.h b))^85 ≤ Y/S) (whi : Y/S ≤ ((2:ℝ)^(Fixed.h b))^170) :
    0 < S ∧ 1 ≤ Y ∧
    90*(Fixed.d b:ℝ) ≤ Real.log Y/Real.log (Fixed.B b) ∧
    Real.log Y/Real.log (Fixed.B b) ≤ 110*(Fixed.d b:ℝ) ∧
    (Fixed.B b:ℝ)^(17/200:ℝ) ≤ Y/S ∧ Y/S ≤ (Fixed.B b:ℝ)^(17/100:ℝ) ∧
    (4 ≤ Fixed.d b → Y/S ≤ Y^(1/2000:ℝ)) := by
  have result := construction_power_window _ _ _ _ (one_lt_pow₀ (by norm_num : 1 < (2:ℝ)) h.ne')
    lower upper wlo whi
  dsimp only at result
  rwa [fixed_base_power] at result

end Cogentic.Window
