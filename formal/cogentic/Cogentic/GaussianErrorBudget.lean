import Cogentic.PrincipalMass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Cogentic.Window
open Real

/-- In the full window estimate the Mellin truncation is exponentially
small relative to the saddle prefactor throughout the allowed width range.
The bound is uniform in the tilt, the center and the omitted primes. -/
theorem fixed_gaussian_tail (B Y S α : ℝ) (J : Finset ℕ) (hB : 1 ≤ B) (hY : 0 < Y)
    (hS : 0 < S) (width : Y/S ≤ B^(17/100:ℝ)) (large : 100 ≤ B^(1/100:ℝ)) :
    let E := eulerMass J α
    let T := B^(1/5:ℝ)
    E*((Y^α/S*4*exp (π/4+1))*(2*(4*(Y/S)))*exp (-T/(4*(Y/S)))) ≤
      Y^(α-1)*E*exp (-(B^(1/50:ℝ))) := by
  let x := B^(1/100:ℝ)
  let R := Y/S
  have xp : 0 < x := by dsimp [x]; positivity
  have rp : 0 < R := div_pos hY hS
  have x100 : 100 ≤ x := large
  have power (k : ℕ) : x^k = B^((k:ℝ)/100) := by
    dsimp [x]; rw [←rpow_natCast _ k,←rpow_mul (by linarith)]; congr 1; ring
  have rbound : R ≤ x^17 := by rw [power]; exact width
  have u : B^(1/5:ℝ) = x^20 := by rw [power]; norm_num
  have v : B^(1/50:ℝ) = x^2 := by rw [power]; norm_num
  have freq : x^3/4 ≤ x^20/(4*R) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc x^3/4*(4*R) = x^3*R := by ring
         _ ≤ x^3*x^17 := mul_le_mul_of_nonneg_left rbound (by positivity)
         _ = _ := by ring
  have logcap : log 32+(π/4+1)+34*log x+x^2 ≤ x^3/4 := by
    have large2 := mul_nonneg (sub_nonneg.mpr x100) xp.le
    have large3 := mul_nonneg (sub_nonneg.mpr x100) (sq_nonneg x)
    nlinarith [pi_lt_four,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<32),log_le_sub_one_of_pos xp]
  have cut : 32*exp (π/4+1)*R^2*exp (-(x^20)/(4*R)) ≤ exp (-(x^2)) := by
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ rp.le rbound 2) (by positivity : 0 ≤ 32*exp (π/4+1))) (exp_pos _).le)
    rw [←pow_mul]
    have e : (32:ℝ)*exp (π/4+1)*x^(17*2)*exp (-(x^20)/(4*R)) =
        exp (log 32+(π/4+1)+34*log x-x^20/(4*R)) := by
      rw [sub_eq_add_neg,exp_add _ (-(x^20/(4*R))),exp_add _ (34*log x),
        exp_add (log 32) (π/4+1),exp_log (by norm_num : (0:ℝ)<32),
        show exp (34*log x) = (exp (log x))^34 from exp_nat_mul _ 34,exp_log xp]
      simp [neg_div]
    rw [e,exp_le_exp]
    linarith
  have tilt : Y^α = Y^(α-1)*Y := by rw [←rpow_add_one hY.ne']; ring_nf
  dsimp only
  rw [u,v]
  calc
    _ = (Y^(α-1)*eulerMass J α)*(32*exp (π/4+1)*R^2*exp (-(x^20)/(4*R))) := by
      rw [tilt]; dsimp [R]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left cut (mul_nonneg (rpow_nonneg hY.le _) (eulerMass_pos _ _).le)

/-- The replacement of the linear Gaussian by its central Mellin value
costs at most a fixed negative power of B on the clean width schedule. -/
theorem fixed_gaussian_central_error (B R : ℝ) (hB : 0 < B) (hH : 1 ≤ log B)
    (width : B^(17/200:ℝ) ≤ R) :
    48/(π*R*log B) ≤ 48/π*B^(-17/200:ℝ) := by
  have p : 0 < B^(17/200:ℝ) := rpow_pos_of_pos hB _
  have rp := p.trans_le width
  rw [show (-17/200:ℝ) = -(17/200) by ring,rpow_neg hB.le,←div_eq_mul_inv,div_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  calc π*B^(17/200:ℝ) ≤ π*R := mul_le_mul_of_nonneg_left width pi_pos.le
       _ ≤ _ := le_mul_of_one_le_right (by positivity) hH

/-- The actual saddle's moderate-frequency loss beats every prescribed
Gaussian in log u, uniformly above one threshold for the saddle scale u. -/
theorem middle_log_square_decay (C : ℝ) (hC : 1 ≤ C) :
    ∃ u₀ : ℝ, ∀ u ≥ u₀,
      exp ((1/4-u/(1152*(log (8*u+1))^3))/4) ≤ exp (-C*(log u)^2) := by
  let K := 100000*C
  have pos : 0 < K := by dsimp [K]; linarith
  have small := (isLittleO_log_rpow_rpow_atTop 5 (by norm_num : (0:ℝ)<1)).bound (inv_pos.mpr pos)
  obtain ⟨t,major⟩ := Filter.eventually_atTop.mp small
  refine ⟨max t 10,fun u large => ?_⟩
  have u10 : 10 ≤ u := (le_max_right ..).trans large
  have up : 0 < u := by linarith
  have log1 : 1 ≤ log u := (le_log_iff_exp_le up).mpr (by linarith [exp_one_lt_d9])
  have logbig := log_le_log (by positivity : 0 < 8*u+1)
    (show 8*u+1 ≤ u^2 by nlinarith [mul_nonneg (sub_nonneg.mpr u10) (by linarith : 0 ≤ u-1)])
  rw [log_pow] at logbig
  norm_num at logbig
  have p : 0 < log (8*u+1) := log_pos (by linarith)
  have poly := major u ((le_max_left ..).trans large)
  simp only [Real.rpow_one,Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg up.le,
    abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ log u) 5)] at poly
  have scale : K*(log u)^5 ≤ u := by
    simpa only [← mul_assoc,mul_inv_cancel₀ pos.ne',one_mul] using
      mul_le_mul_of_nonneg_left poly pos.le
  have denom : 1152*(log (8*u+1))^3 ≤ 9216*(log u)^3 := by
    calc _ ≤ 1152*((2:ℝ)*log u)^3 := by gcongr
         _ = _ := by ring
  have need : 5*C*(log u)^2 ≤ u/(1152*(log (8*u+1))^3) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc _ ≤ (5*C*(log u)^2)*(9216*(log u)^3) :=
               mul_le_mul_of_nonneg_left denom (by positivity)
         _ ≤ K*(log u)^5 := by dsimp [K]; nlinarith [mul_nonneg (by linarith : 0≤C) (pow_nonneg (by linarith : 0≤log u) 5)]
         _ ≤ u := scale
  apply exp_le_exp.mpr
  have enough := mul_le_mul hC (one_le_pow₀ (n := 2) log1) (by norm_num) (by linarith)
  linarith

/-- The absolute nonprincipal-character discrepancy is uniformly small
relative to the principal Euler prefactor at a sufficiently shallow tilt. -/
theorem character_error_at_saddle (Y α : ℝ) (J : Finset ℕ) (hY : 1 ≤ Y) (shallow : 999/1000 ≤ α) :
    Y^(-3/1000:ℝ) ≤ (Y^(α-1)*eulerMass J α)*Y^(-1/500:ℝ) := by
  have one : 1 ≤ eulerMass J α := Finset.one_le_prod (fun p _ => by
    change 1 ≤ 1+(p:ℝ)^(-α); linarith [rpow_nonneg (Nat.cast_nonneg p) (-α)])
  have yp : 0 < Y := zero_lt_one.trans_le hY
  calc
    _ ≤ Y^(α-1+(-1/500:ℝ)) := rpow_le_rpow_of_exponent_le hY (by linarith)
    _ = Y^(α-1)*Y^(-1/500:ℝ) := rpow_add yp ..
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (rpow_nonneg yp.le _) one) (rpow_nonneg yp.le _)

end Cogentic.Window
