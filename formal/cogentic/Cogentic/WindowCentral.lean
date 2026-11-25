import Cogentic.Window
import Cogentic.WindowSaddle

open Complex MeasureTheory
open scoped BigOperators

namespace Cogentic.Window

noncomputable section

/-- Real normalization of the tilted retained Euler product. -/
def eulerMass (J : Finset ℕ) (α : ℝ) : ℝ := ∏ p ∈ J, (1+(p : ℝ)^(-α))

theorem eulerMass_pos (J : Finset ℕ) (α : ℝ) : 0 < eulerMass J α :=
  Finset.prod_pos (fun _ _ => by positivity)

private theorem eulerMass_coe (J : Finset ℕ) (α : ℝ) :
    (eulerMass J α : ℂ) = ∏ p ∈ J, (1+(((p:ℝ)^(-α):ℝ):ℂ)) := by
  simp [eulerMass]

theorem principalEuler_critical_norm (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p)
    (α t : ℝ) : ‖principalEuler J (α-t*Complex.I)‖ ≤ eulerMass J α := by
  rw [principalEuler,norm_prod,eulerMass]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro p hp
  apply (norm_add_le ..).trans
  have pos : (0:ℝ) < p := by exact_mod_cast hJ p hp
  rw [norm_one,← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos pos]
  simp

private theorem central_point_factor (J D : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p)
    (α t Y : ℝ) (hY : 0 < Y) :
    principalEuler (J\D) (α-t*Complex.I) * (Y:ℂ)^(α-t*Complex.I-1) =
      ((Y^(α-1)*eulerMass (J\D) α : ℝ):ℂ) *
        (Complex.exp (Complex.I*((saddleMean J α-Real.log Y)*t : ℝ)) *
          omittedCharacteristic J D (primeProbability α) (fun p => Real.log p) t) := by
  have normnz : (eulerMass (J\D) α : ℂ) ≠ 0 := ofReal_ne_zero.mpr (eulerMass_pos _ _).ne'
  have power : (Y:ℂ)^(α-t*Complex.I-1) =
      ((Y^(α-1):ℝ):ℂ)*Complex.exp (-Complex.I*(t*Real.log Y)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne'),
      ← Complex.ofReal_log hY.le,Real.rpow_def_of_pos hY,Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  have phases : Complex.exp (Complex.I*((saddleMean J α-Real.log Y)*t : ℝ)) *
      Complex.exp (-Complex.I*(t*saddleMean J α)) = Complex.exp (-Complex.I*(t*Real.log Y)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [omitted_characteristic_euler J D hJ,← eulerMass_coe,power,Complex.ofReal_mul]
  rw [← phases]
  field_simp

/-- The real central principal Mellin integral is the tilted omitted-prime
    saddle mass, up to the explicit linear-Gaussian error. This holds for
    any center, using its displacement from the chosen common saddle. -/
theorem principal_central_mellin (J D : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p)
    (α H Y S : ℝ) (ha : 1/2 ≤ α) (ha' : α ≤ 1) (hH : 1 ≤ H)
    (hY : 0 < Y) (hS : 0 < S) (hR : 1 ≤ Y/S) :
    let s := fun t : ℝ => (α : ℂ)-t*Complex.I
    let W := fun x : ℝ => (gaussian Y S x : ℂ)
    let F := Y^(α-1)*eulerMass (J\D) α
    let a := saddleMean J α-Real.log Y
    |(∫ t : ℝ in -(1/H)..1/H, (principalEuler (J\D) (s t)*mellin W (s t)).re) -
      F*omittedMass J D (primeProbability α) (fun p => Real.log p) H a| ≤
      F*(48/(Real.pi*(Y/S)*H)) := by
  let line (t : ℝ) : ℂ := (α : ℂ)-t*Complex.I
  let W := fun x : ℝ => (gaussian Y S x : ℂ)
  let E := eulerMass (J\D) α
  let F := Y^(α-1)*E
  let a := saddleMean J α-Real.log Y
  let f (t : ℝ) := (principalEuler (J\D) (line t)*mellin W (line t)).re
  let g (t : ℝ) := (Complex.exp (Complex.I*(a*t : ℝ))*
      omittedCharacteristic J D (primeProbability α) (fun p => Real.log p) t).re
  have posH : 0 < H := zero_lt_one.trans_le hH
  have lr : -(1/H) ≤ 1/H := by linarith [one_div_pos.mpr posH]
  have lre (t : ℝ) : (line t).re = α := by simp [line]
  have mc : Continuous (fun t => mellin W (line t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (gaussian_mellin_differentiable Y S (line t) hS (by rw [lre]; linarith)).continuousAt.comp
      (by unfold line; fun_prop)
  have pe : Continuous (fun t => principalEuler (J\D) (line t)) := by
    unfold principalEuler
    apply continuous_finsetProd
    intro p hp
    have pos := hJ p (Finset.mem_sdiff.mp hp).1
    apply continuous_const.add
    exact (by unfold line; fun_prop : Continuous (fun t => -line t)).const_cpow
      (Or.inl (by exact_mod_cast pos.ne' : (p:ℂ) ≠ 0))
  have fc : Continuous f := Complex.continuous_re.comp (pe.mul mc)
  have point (t : ℝ) : (principalEuler (J\D) (line t)*(Y:ℂ)^(line t-1)).re = F*g t := by
    rw [central_point_factor J D hJ α t Y hY,Complex.re_ofReal_mul]
  have gc : Continuous (fun t => F*g t) := by
    simp_rw [← point]
    apply Complex.continuous_re.comp
    apply pe.mul
    exact (by unfold line; fun_prop : Continuous (fun t => line t-1)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  have bound (t : ℝ) (ht : t ∈ Set.uIoc (-(1/H)) (1/H)) :
      ‖f t-F*g t‖ ≤ E*(Y^(α-1)*(24/(Real.pi*(Y/S)))) := by
    rw [Set.uIoc_of_le lr] at ht
    have tw : |t| ≤ 1/H := abs_le.mpr ⟨ht.1.le,ht.2⟩
    have th : |t| ≤ 1 := tw.trans ((div_le_one posH).mpr hH)
    have hn : ‖line t-1‖ ≤ 2 := by
      rw [show line t-1=((α-1:ℝ):ℂ)-t*Complex.I by dsimp [line]; push_cast; ring]
      apply (norm_sub_le ..).trans
      simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one]
      rw [abs_of_nonpos (by linarith : α-1 ≤ 0)]; linarith
    have delta := gaussian_mellin_central Y S (line t) hY hS hR (by rwa [lre]) (by rwa [lre]) hn
    rw [lre] at delta
    dsimp only [f]
    rw [← point,Real.norm_eq_abs,← Complex.sub_re]
    apply (Complex.abs_re_le_norm _).trans
    rw [← mul_sub,norm_mul]
    exact mul_le_mul (principalEuler_critical_norm (J\D) (fun p h => hJ p (Finset.mem_sdiff.mp h).1) α t)
      delta (norm_nonneg _) (eulerMass_pos _ _).le
  change |(∫ t : ℝ in -(1/H)..1/H, f t)-F*(∫ t : ℝ in -(1/H)..1/H, g t)| ≤ _
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub
    (fc.intervalIntegrable ..) (gc.intervalIntegrable ..),← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const bound).trans_eq
  rw [abs_of_nonneg (by linarith [one_div_pos.mpr posH] : 0 ≤ 1/H- -(1/H))]
  change _ = F*(48/(Real.pi*(Y/S)*H))
  dsimp [F]; ring

end

end Cogentic.Window
