import Cogentic.WindowSaddle

open Real MeasureTheory Set

namespace Cogentic.Window

/-- Uniform central mass bound at any logarithmic displacement, with the
    actual variance of the retained factors. -/
theorem omitted_mass_uniform {ι : Type*} [DecidableEq ι] (J D : Finset ι)
    (r ell : ι → ℝ) (H a : ℝ) (hH : 0 < H)
    (hr : ∀ p∈J, 0 ≤ r p) (hr' : ∀ p∈J, r p ≤ 1) (hband : ∀ p∈J, |ell p| ≤ H)
    (hV : 0 < saddleVariance (J\D) r ell) :
    |omittedMass J D r ell H a| ≤ sqrt (3*π/saddleVariance (J\D) r ell) := by
  let V := saddleVariance (J\D) r ell
  have vp : 0 < V := hV
  let g := fun t : ℝ => exp (-(V/3)*t^2)
  have gi : Integrable g := integrable_exp_neg_mul_sq (by positivity)
  have lr : -(1/H) ≤ 1/H := by have := one_div_pos.mpr hH; linarith
  have retained (t : ℝ) : ‖omittedCharacteristic J D r ell t‖ =
      ‖saddleCharacteristic (J\D) r ell t‖ := by
    rw [omittedCharacteristic,saddleCharacteristic,norm_prod,norm_prod,Finset.sdiff_eq_filter,
      Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : p∈D
    · simp only [hp,if_pos,not_true_eq_false,if_false]
      change ‖Complex.exp (Complex.I*↑(-r p*(t*ell p)))‖=1
      simp [Complex.norm_exp]
    · simp [hp]
  let f := fun t : ℝ => (Complex.exp (Complex.I*↑(a*t))*omittedCharacteristic J D r ell t).re
  have bound (t : ℝ) (mem : t∈Ioc (-(1/H)) (1/H)) : ‖f t‖ ≤ g t := by
    have ph (p) (hp : p∈J\D) : |t*ell p| ≤ 1 := by
      rw [abs_mul]
      have tm : |t| ≤ 1/H := abs_le.mpr ⟨mem.1.le,mem.2⟩
      calc _ ≤ (1/H)*H := mul_le_mul tm (hband p (Finset.mem_sdiff.mp hp).1) (abs_nonneg _) (by positivity)
           _ = 1 := by field_simp
    simp only [f,Real.norm_eq_abs]
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul,Complex.norm_exp]
    simp only [Complex.I_mul_re,Complex.ofReal_im,neg_zero,exp_zero,one_mul,retained]
    exact (saddle_characteristic_decay _ r ell t
      (fun p hp => hr p (Finset.mem_sdiff.mp hp).1)
      (fun p hp => hr' p (Finset.mem_sdiff.mp hp).1) ph).trans_eq (by dsimp [g,V]; ring_nf)
  change |∫ t in -(1/H)..1/H, f t| ≤ sqrt (3*π/V)
  rw [←Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_of_norm_le lr (Filter.Eventually.of_forall bound)
    gi.intervalIntegrable).trans
  rw [intervalIntegral.integral_of_le lr]
  calc _ ≤ ∫ t : ℝ, g t := setIntegral_le_integral gi (Filter.Eventually.of_forall (fun _ => (exp_pos _).le))
       _ = _ := by dsimp [g]; rw [integral_gaussian]; congr 1; ring

/-- Deletion loses at most H² times the sum of deleted Bernoulli
    parameters from the central variance. -/
theorem retained_saddle_variance {ι : Type*} [DecidableEq ι] (J D : Finset ι)
    (r ell : ι → ℝ) (H : ℝ) (hr : ∀ p∈J, 0 ≤ r p)
    (band : ∀ p∈J, |ell p| ≤ H) :
    saddleVariance J r ell ≤ saddleVariance (J\D) r ell+
      (∑ p ∈ J, if p ∈ D then r p else 0)*H^2 := by
  rw [saddleVariance,saddleVariance,Finset.sdiff_eq_filter,Finset.sum_filter,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  by_cases d : p∈D
  · simp only [d,not_true_eq_false,if_false,if_pos,zero_add]
    have b := pow_le_pow_left₀ (abs_nonneg _) (band p hp) 2
    rw [sq_abs] at b
    exact mul_le_mul (by nlinarith [sq_nonneg (r p)]) b (sq_nonneg _) (hr p hp)
  · simp [d]

/-- Uniform all-shifts central estimate in saddle units, including
    logarithmic divisibility shifts exceeding two band lengths. -/
theorem omitted_prime_mass_uniform (J D : Finset ℕ) (α H u a : ℝ)
    (ha : 0 ≤ α) (hH : 0 < H) (up : 0 < u) (hJ : ∀ p∈J, 1 ≤ p)
    (band : ∀ p∈J, H/2 ≤ log p ∧ log p ≤ H) (mean : saddleMean J α=H*u)
    (small : (∑ p∈J, if p∈D then primeProbability α p else 0) ≤ u/8) :
    |omittedMass J D (primeProbability α) (fun p=>log p) H a| ≤
      sqrt (24*π)/(H*sqrt u) := by
  let r := primeProbability α
  let ell := fun p : ℕ => log p
  let V := saddleVariance (J\D) r ell
  have hband (p) (hp : p∈J) : |ell p| ≤ H := by
    rw [abs_of_nonneg (show 0≤ell p from log_nonneg (by exact_mod_cast hJ p hp))]
    exact (band p hp).2
  have v0 := (prime_saddle_variance_bounds J α H ha hH.le hJ band).1
  rw [mean] at v0
  have r0 (p : ℕ) : 0 ≤ r p := by dsimp [r,primeProbability]; positivity
  have r1 (p : ℕ) : r p ≤ 1 := by
    dsimp [r,primeProbability]
    rw [div_le_one (by positivity)]
    linarith
  have left := retained_saddle_variance J D r ell H (fun p _ => r0 p) hband
  have sg := mul_le_mul_of_nonneg_right small (sq_nonneg H)
  change saddleVariance J r ell ≤ V + _ at left
  change H*(H*u)/4 ≤ saddleVariance J r ell at v0
  change (∑ p∈J, if p∈D then r p else 0)*H^2 ≤ _ at sg
  have lower : H^2*u/8 ≤ V := by linarith only [v0,left,sg]
  have vp : 0 < V := (by positivity : 0 < H^2*u/8).trans_le lower
  apply (omitted_mass_uniform J D r ell H a hH (fun p _ => r0 p) (fun p _ => r1 p) hband vp).trans
  change sqrt (3*π/V) ≤ sqrt (24*π)/(H*sqrt u)
  apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
  rw [sq_sqrt (by positivity),div_pow,mul_pow,sq_sqrt up.le,sq_sqrt (by positivity)]
  apply (div_le_div_iff₀ vp (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left lower pi_pos.le]

end Cogentic.Window
