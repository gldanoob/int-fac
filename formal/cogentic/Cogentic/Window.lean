import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

open scoped BigOperators

namespace Cogentic.Window

noncomputable section

variable {q : ℕ}

/-- Cogentic's Gaussian in the original linear coordinate. -/
def gaussian (Y S x : ℝ) : ℝ := Real.exp (-Real.pi*((x-Y)/S)^2)/S

/-- Changing variables by a common divisor carries both the window and its
    arithmetic progression normalization. -/
theorem gaussian_rescale (q g Y S x : ℝ) (hg : g ≠ 0) (hS : S ≠ 0) :
    (q/g)*gaussian (Y/g) (S/g) (x/g) = q*gaussian Y S x := by
  have scale : (x/g - Y/g)/(S/g) = (x-Y)/S := by field_simp
  dsimp [gaussian]
  rw [scale]
  field_simp

/-- Shifting the contour for the linear Gaussian through an imaginary
    logarithmic displacement keeps uniformly positive quadratic decay. -/
theorem gaussian_strip_quadratic (x y : ℝ) (hy : |y| ≤ 1/4) :
    (Real.exp x - 1)^2/2 - 4*y^2 ≤
      ((Complex.exp ((x : ℂ)+y*Complex.I)-1)^2).re := by
  let u := Real.exp x
  have hu := Real.exp_pos x
  have trig := Real.cos_sq_add_sin_sq y
  have diff : ((Complex.exp ((x : ℂ)+y*Complex.I)-1)^2).re =
      (u-1)^2 + 2*u*(1-Real.cos y) - 2*u^2*(Real.sin y)^2 := by
    simp only [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero, Complex.exp_re, Complex.exp_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_I_im, Complex.I_re,
      mul_zero, zero_mul, add_zero, zero_add]
    dsimp [u]
    nlinarith [congrArg (fun v : ℝ => (Real.exp x)^2*v) trig]
  have hu2 : u^2 ≤ 2*(u-1)^2+2 := by nlinarith [sq_nonneg (u-2)]
  have small : 4*y^2 ≤ 1/2 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg y) hy 2
    rw [sq_abs] at hsq
    nlinarith
  rw [diff]
  change (u-1)^2/2 - 4*y^2 ≤ _
  nlinarith [mul_nonneg (show 0 ≤ 2*u by positivity [u]) (sub_nonneg.mpr (Real.cos_le_one y)),
    mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := y)) (sq_nonneg u),
    mul_le_mul_of_nonneg_right hu2 (sq_nonneg y),
    mul_le_mul_of_nonneg_right small (sq_nonneg (u-1))]

/-- The Mellin integrand after scaling the linear Gaussian to center one and
    substituting the logarithmic coordinate. -/
def gaussianLogIntegrand (R : ℝ) (s z : ℂ) : ℂ :=
  Complex.exp (-((Real.pi * R^2 : ℝ) : ℂ)*(Complex.exp z-1)^2 + s*z)

theorem gaussian_strip_bound (R : ℝ) (s : ℂ) (x y : ℝ) (hR : 1 ≤ R)
    (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) (hy : |y| ≤ 1/(4*R)) :
    ‖gaussianLogIntegrand R s (x+y*Complex.I)‖ ≤
      Real.exp (Real.pi/4+1 - s.im*y) * Real.exp (-|x|/2) := by
  have pos : 0 < R := zero_lt_one.trans_le hR
  have hsmall : |y| ≤ 1/4 := hy.trans (by gcongr; linarith)
  have geom := gaussian_strip_quadratic x y hsmall
  have sqy : (R*y)^2 ≤ (1/4 : ℝ)^2 := by
    rw [← sq_abs (R*y), abs_mul, abs_of_pos pos]
    apply pow_le_pow_left₀ (mul_nonneg pos.le (abs_nonneg _))
    have := (le_div_iff₀ (show 0 < 4*R by positivity)).mp hy
    linarith
  have piR : 2 ≤ Real.pi*R^2 := by
    nlinarith [Real.two_le_pi, mul_nonneg Real.pi_pos.le (show 0 ≤ R^2-1 by nlinarith)]
  have core : -(Real.pi*R^2)*((Real.exp x-1)^2/2) + s.re*x ≤ 1 - |x|/2 := by
    rcases le_or_gt x 0 with hx | hx
    · rw [abs_of_nonpos hx]
      nlinarith [mul_nonneg (show 0 ≤ Real.pi*R^2 by positivity) (sq_nonneg (Real.exp x-1)),
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs) hx]
    · rw [abs_of_pos hx]
      have hex : x ≤ Real.exp x-1 := by linarith [Real.add_one_le_exp x]
      have hx2 := pow_le_pow_left₀ hx.le hex 2
      nlinarith [mul_nonneg (sub_nonneg.mpr piR) (sq_nonneg (Real.exp x-1)),
        mul_nonneg (sub_nonneg.mpr hs') hx.le, sq_nonneg (x-3/4), hx2]
  rw [gaussianLogIntegrand, Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  simp only [Complex.add_re, neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.mul_re s, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add]
  nlinarith [mul_le_mul_of_nonneg_left geom (show 0 ≤ Real.pi*R^2 by positivity),
    mul_le_mul_of_nonneg_left sqy Real.pi_pos.le]

private theorem gaussian_envelope_integral : ∫ x : ℝ, Real.exp (-|x|/2) = 4 := by
  simp_rw [show ∀ x : ℝ, -|x|/2 = (-1/2 : ℝ)*|x| by intro x; ring]
  rw [integral_comp_abs (f := fun x => Real.exp ((-1/2 : ℝ)*x)),
    integral_exp_mul_Ioi (by norm_num) 0]
  norm_num

private theorem integrable_gaussian_envelope : MeasureTheory.Integrable
    (fun x : ℝ => Real.exp (-|x|/2)) :=
  .of_integral_ne_zero (by rw [gaussian_envelope_integral]; norm_num)

open Filter MeasureTheory Complex in
open scoped Topology in
private theorem gaussian_horizontal_shift (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (y C : ℝ) (h : ∀ x u : ℝ, u ∈ Set.uIcc 0 y →
      ‖F (x+u*I)‖ ≤ C*Real.exp (-|x|/2)) :
    (∫ x : ℝ, F x) = ∫ x : ℝ, F (x+y*I) := by
  let H (u T : ℝ) := ∫ x : ℝ in -T..T, F (x+u*I)
  let V (x : ℝ) := ∫ u : ℝ in 0..y, F (x+u*I)
  have int (u : ℝ) (hu : u ∈ Set.uIcc 0 y) : Integrable (fun x : ℝ => F (x+u*I)) := by
    apply (integrable_gaussian_envelope.const_mul C).mono'
    · exact (hF.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall (fun x => h x u hu)
  have edge (x : ℝ) : ‖V x‖ ≤ C*Real.exp (-|x|/2)*|y| := by
    simpa only [sub_zero, V] using intervalIntegral.norm_integral_le_of_norm_le_const
      (fun u hu => h x u (Set.uIoc_subset_uIcc hu))
  have decay : Tendsto (fun T : ℝ => C*Real.exp (-T/2)*|y|) atTop (𝓝 0) := by
    have e := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2)))
    simpa [Function.comp_def, neg_div] using (e.const_mul C).mul_const |y|
  have ev (sgn : ℝ → ℝ) (hsign : ∀ T : ℝ, 0 ≤ T → |sgn T| = T) :
      Tendsto (fun T => V (sgn T)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _)) _ decay
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    simpa only [hsign T hT] using edge (sgn T)
  have plus := ev id (fun T hT => abs_of_nonneg hT)
  have minus := ev (fun T => -T) (fun T hT => by rw [abs_neg, abs_of_nonneg hT])
  have boundary (T : ℝ) : H 0 T - H y T + I*V T - I*V (-T) = 0 := by
    have rect := integral_boundary_rect_eq_zero_of_differentiableOn F (-(T : ℂ))
      (T+y*I) hF.differentiableOn
    simpa only [H, V, neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero,
      neg_re, ofReal_re, add_re, mul_re, I_re, mul_zero, I_im, sub_zero, add_im,
      mul_im, mul_one, zero_add, smul_eq_mul, ofReal_neg] using rect
  have limit := ((intervalIntegral_tendsto_integral (int 0 Set.left_mem_uIcc)
    tendsto_neg_atTop_atBot tendsto_id).sub
    (intervalIntegral_tendsto_integral (int y Set.right_mem_uIcc)
      tendsto_neg_atTop_atBot tendsto_id) |>.add (plus.const_mul I)).sub (minus.const_mul I)
  change Tendsto (fun T => H 0 T - H y T + I*V T - I*V (-T)) atTop _ at limit
  simp only [boundary, zero_mul, mul_zero, add_zero, sub_zero, ofReal_zero] at limit
  exact sub_eq_zero.mp (tendsto_nhds_unique limit tendsto_const_nhds)

/-- Exponential high-frequency decay for the exact normalized linear Gaussian.
    The shift is allowed to depend on the sign of the frequency. -/
theorem gaussian_log_frequency_bound (R : ℝ) (s : ℂ) (hR : 1 ≤ R)
    (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) :
    ‖∫ x : ℝ, gaussianLogIntegrand R s x‖ ≤
      4*Real.exp (Real.pi/4+1 - |s.im|/(4*R)) := by
  let d := 1/(4*R)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let y := if 0 ≤ s.im then d else -d
  have hdy : |y| = d := by dsimp only [y]; split_ifs <;> simp [hd]
  have freq : s.im*y = |s.im|/(4*R) := by
    dsimp [y,d]
    split_ifs with h <;> simp [abs_of_nonneg, abs_of_neg, h, lt_of_not_ge, div_eq_mul_inv]
  have uniformBound (x u : ℝ) (hu : u ∈ Set.uIcc 0 y) :
      ‖gaussianLogIntegrand R s (x+u*Complex.I)‖ ≤
        Real.exp (Real.pi/4+1+|s.im| * d)*Real.exp (-|x|/2) := by
    have absu : |u| ≤ d := by simpa [hdy] using Set.abs_sub_left_of_mem_uIcc hu
    apply (gaussian_strip_bound R s x u hR hs hs' absu).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    have m := mul_le_mul_of_nonneg_left absu (abs_nonneg s.im)
    rw [← abs_mul] at m
    linarith [neg_abs_le (s.im*u)]
  rw [gaussian_horizontal_shift (gaussianLogIntegrand R s) (by unfold gaussianLogIntegrand; fun_prop)
    y _ uniformBound]
  have b := MeasureTheory.norm_integral_le_of_norm_le
    (integrable_gaussian_envelope.const_mul (Real.exp (Real.pi/4+1 - s.im*y)))
    (Filter.Eventually.of_forall (fun x => gaussian_strip_bound R s x y hR hs hs'
      (le_of_eq hdy)))
  change _ ≤ ∫ x : ℝ, Real.exp (Real.pi/4+1 - s.im*y)*Real.exp (-|x|/2) at b
  rw [MeasureTheory.integral_const_mul, gaussian_envelope_integral, freq] at b
  simpa only [mul_comm] using b

private def normalizedGaussian (R x : ℝ) : ℂ :=
  Complex.exp (-((Real.pi*R^2 : ℝ) : ℂ)*((x : ℂ)-1)^2)

private theorem gaussian_log_change (R : ℝ) (s : ℂ) (x : ℝ) :
    Real.exp x • (((Real.exp x : ℝ) : ℂ)^(s-1) • normalizedGaussian R (Real.exp x)) =
      gaussianLogIntegrand R s x := by
  rw [Complex.real_smul, smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [gaussianLogIntegrand, normalizedGaussian, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

private theorem normalized_gaussian_mellin (R : ℝ) (s : ℂ) :
    mellin (normalizedGaussian R) s = ∫ x : ℝ, gaussianLogIntegrand R s x := by
  rw [mellin, ← Real.range_exp, ← Set.image_univ,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  simp only [abs_of_pos (Real.exp_pos _), gaussian_log_change, MeasureTheory.setIntegral_univ]

private theorem normalized_gaussian_convergent (R : ℝ) (s : ℂ) (hR : 1 ≤ R)
    (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) : MellinConvergent (normalizedGaussian R) s := by
  rw [MellinConvergent, ← Real.range_exp, ← Set.image_univ,
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  simp only [abs_of_pos (Real.exp_pos _), gaussian_log_change, MeasureTheory.integrableOn_univ]
  apply (integrable_gaussian_envelope.const_mul (Real.exp (Real.pi/4+1))).mono'
  · unfold gaussianLogIntegrand
    fun_prop
  · apply Filter.Eventually.of_forall
    intro x
    have : 0 ≤ 1/(4*R) := by positivity
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, mul_zero, sub_zero] using
      gaussian_strip_bound R s x 0 hR hs hs' (by rwa [abs_zero])

private theorem gaussian_scale_function (Y S : ℝ) (hY : 0 < Y) (hS : 0 < S) :
    (fun x : ℝ => (gaussian Y S x : ℂ)) =
      fun x => normalizedGaussian (Y/S) (Y⁻¹*x)/(S : ℂ) := by
  funext x
  simp only [gaussian, normalizedGaussian, Complex.ofReal_div, Complex.ofReal_exp,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_inv]
  congr 2
  field_simp [Complex.ofReal_ne_zero.mpr hY.ne', Complex.ofReal_ne_zero.mpr hS.ne']

/-- A uniform bound for the Mellin transform of the actual linear Gaussian,
    exponentially decreasing for frequencies above the relative inverse width. -/
theorem gaussian_mellin_bound (Y S : ℝ) (s : ℂ) (hY : 0 < Y) (hS : 0 < S)
    (hR : 1 ≤ Y/S) (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) :
    ‖mellin (fun x : ℝ => (gaussian Y S x : ℂ)) s‖ ≤
      Y^s.re/S * (4*Real.exp (Real.pi/4+1 - |s.im|/(4*(Y/S)))) := by
  rw [gaussian_scale_function Y S hY hS, mellin_div_const,
    mellin_comp_mul_left _ _ (inv_pos.mpr hY), smul_eq_mul, norm_div, norm_mul,
    normalized_gaussian_mellin, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hY),
    Complex.neg_re, Real.inv_rpow hY.le, Real.rpow_neg hY.le, inv_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  calc
    _ ≤ Y^s.re * (4*Real.exp (Real.pi/4+1 - |s.im|/(4*(Y/S)))) / S := by
      gcongr
      exact gaussian_log_frequency_bound (Y/S) s hR hs hs'
    _ = _ := by ring

theorem gaussian_mellin_convergent (Y S : ℝ) (s : ℂ) (hY : 0 < Y) (hS : 0 < S)
    (hR : 1 ≤ Y/S) (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) :
    MellinConvergent (fun x : ℝ => (gaussian Y S x : ℂ)) s := by
  rw [gaussian_scale_function Y S hY hS]
  apply MellinConvergent.div_const
  exact (MellinConvergent.comp_mul_left (inv_pos.mpr hY)).mpr
    (normalized_gaussian_convergent (Y/S) s hR hs hs')

private theorem frequency_envelope_integral (D : ℝ) (hD : 0 < D) :
    (∫ t : ℝ, Real.exp (-|t|/D)) = 2*D := by
  simp_rw [show ∀ t : ℝ, -|t|/D = (-D⁻¹)*|t| by intro; ring]
  rw [integral_comp_abs (f := fun t => Real.exp ((-D⁻¹)*t)),
    integral_exp_mul_Ioi (neg_lt_zero.mpr (inv_pos.mpr hD)) 0]
  simp

private theorem gaussian_localized_majorant (R : ℝ) (s : ℂ) (x : ℝ)
    (hR : 1 ≤ R) (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) :
    ‖gaussianLogIntegrand R s x‖ ≤ Real.exp 1*Real.exp (-R*|x|/4) +
      Real.exp (-R/4)*Real.exp (-|x|/2) := by
  rw [gaussianLogIntegrand, Complex.norm_exp]
  simp only [Complex.add_re, neg_mul, Complex.neg_re, Complex.re_ofReal_mul, Complex.mul_re s,
    ← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have positive : 0 < R := zero_lt_one.trans_le hR
  have sq_scale (v : ℝ) : R^2*v^2 ≤ Real.pi*R^2*v^2 := by
    nlinarith [mul_nonneg (show 0 ≤ Real.pi-1 by linarith [Real.two_le_pi]) (mul_nonneg (sq_nonneg R) (sq_nonneg v))]
  by_cases hx : x ≤ -1
  · apply (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans'
    rw [← Real.exp_add, Real.exp_le_exp, abs_of_nonpos (by linarith : x ≤ 0)]
    have ex : Real.exp x ≤ 1/2 := by
      rw [← neg_neg x, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      norm_num; linarith [Real.add_one_le_exp (-x)]
    have sqex : 1/4 ≤ (Real.exp x-1)^2 := by
      nlinarith [sq_nonneg (Real.exp x-1/2)]
    nlinarith [sq_scale (Real.exp x-1),
      mul_le_mul_of_nonneg_left sqex (sq_nonneg R),
      mul_nonneg (sub_nonneg.mpr hR) positive.le,
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs) (by linarith : x ≤ 0)]
  · apply (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans'
    rw [← Real.exp_add, Real.exp_le_exp]
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0]
      have ex : x ≤ Real.exp x-1 := by linarith [Real.add_one_le_exp x]
      have sqex := pow_le_pow_left₀ hx0 ex 2
      nlinarith [sq_scale (Real.exp x-1), mul_le_mul_of_nonneg_left sqex (sq_nonneg R),
        mul_nonneg (sub_nonneg.mpr hs') hx0, mul_nonneg (sub_nonneg.mpr hR) hx0,
        sq_nonneg (R*x-5/8)]
    · rw [abs_of_nonpos (le_of_not_ge hx0)]
      have b : (1-x)*Real.exp x ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
        linarith
      have ex : Real.exp x ≤ 1+x/2 := by
        by_contra! h
        have strict := mul_lt_mul_of_pos_left h (show 0 < 1-x by linarith)
        nlinarith [mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ 1+x by linarith)]
      have sqex := pow_le_pow_left₀ (show 0 ≤ -x/2 by linarith)
        (show -x/2 ≤ 1-Real.exp x by linarith) 2
      nlinarith [sq_scale (Real.exp x-1),
        mul_le_mul_of_nonneg_left sqex (sq_nonneg R),
        mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ s.re by linarith) (le_of_not_ge hx0),
        sq_nonneg (R*x/2+1/4)]

private theorem gaussian_log_uniform (R : ℝ) (s : ℂ) (hR : 1 ≤ R)
    (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) :
    ‖∫ x : ℝ, gaussianLogIntegrand R s x‖ ≤ (8*Real.exp 1+16)/R := by
  have pos : 0 < R := zero_lt_one.trans_le hR
  let D := 4/R
  have hD : 0 < D := by dsimp [D]; positivity
  have sub (x : ℝ) : -R*|x|/4 = -|x|/D := by dsimp [D]; field_simp
  have gauss : MeasureTheory.Integrable (fun x : ℝ => Real.exp (-|x|/D)) :=
    .of_integral_ne_zero (by rw [frequency_envelope_integral D hD]; positivity)
  have i1 := gauss.const_mul (Real.exp 1)
  have i2 := integrable_gaussian_envelope.const_mul (Real.exp (-R/4))
  have b := MeasureTheory.norm_integral_le_of_norm_le (i1.add i2)
    (Filter.Eventually.of_forall (fun x => by
      simpa only [sub, Pi.add_apply] using gaussian_localized_majorant R s x hR hs hs'))
  change _ ≤ ∫ x : ℝ, Real.exp 1*Real.exp (-|x|/D)+Real.exp (-R/4)*Real.exp (-|x|/2) at b
  rw [MeasureTheory.integral_add i1 i2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, frequency_envelope_integral D hD, gaussian_envelope_integral] at b
  have tail : Real.exp (-R/4) ≤ 4/R := by
    rw [neg_div, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    simp only [inv_div]
    linarith [Real.add_one_le_exp (R/4)]
  dsimp [D] at b
  calc
    _ ≤ Real.exp 1*(2*(4/R))+(4/R)*4 := b.trans (by linarith)
    _ = _ := by ring

/-- A uniform estimate with the natural Mellin scaling, including on the
    first horizontal edge of the principal contour. -/
theorem gaussian_mellin_uniform (Y S : ℝ) (s : ℂ) (hY : 0 < Y) (hS : 0 < S)
    (hR : 1 ≤ Y/S) (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) :
    ‖mellin (fun x : ℝ => (gaussian Y S x : ℂ)) s‖ ≤ (8*Real.exp 1+16)*Y^(s.re-1) := by
  rw [gaussian_scale_function Y S hY hS, mellin_div_const,
    mellin_comp_mul_left _ _ (inv_pos.mpr hY), smul_eq_mul, norm_div, norm_mul,
    normalized_gaussian_mellin, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hY),
    Complex.neg_re, Real.inv_rpow hY.le, Real.rpow_neg hY.le, inv_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS, Real.rpow_sub hY, Real.rpow_one]
  calc
    _ ≤ Y^s.re*((8*Real.exp 1+16)/(Y/S))/S := by
      gcongr
      exact gaussian_log_uniform (Y/S) s hR hs hs'
    _ = _ := by field_simp

private theorem frequency_envelope_tail (D T : ℝ) (hD : 0 < D) (hT : 0 ≤ T) :
    (∫ t in {t : ℝ | T < |t|}, Real.exp (-|t|/D)) = 2*D*Real.exp (-T/D) := by
  let tail := {t : ℝ | T < |t|}
  have m : MeasurableSet tail := measurableSet_lt measurable_const continuous_abs.measurable
  have eqind : tail.indicator (fun t : ℝ => Real.exp (-|t|/D)) =
      fun t : ℝ => (Set.Ioi T).indicator (fun v => Real.exp ((-D⁻¹)*v)) |t| := by
    ext t
    by_cases h : T < |t|
    · rw [Set.indicator_of_mem (show t ∈ tail from h),
        Set.indicator_of_mem (show |t| ∈ Set.Ioi T from h)]
      congr 1
      ring
    · rw [Set.indicator_of_notMem (show t ∉ tail from h),
        Set.indicator_of_notMem (show |t| ∉ Set.Ioi T from h)]
  rw [← MeasureTheory.integral_indicator m, eqind, integral_comp_abs,
    MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
    max_eq_right hT, integral_exp_mul_Ioi (neg_lt_zero.mpr (inv_pos.mpr hD))]
  rw [show (-D⁻¹)*T = -T/D by ring]
  simp only [div_eq_mul_inv, inv_neg, inv_inv, neg_mul_neg]
  ring

private theorem gaussian_line_bound (Y S σ t : ℝ) (hY : 0 < Y) (hS : 0 < S)
    (hR : 1 ≤ Y/S) (hs : 1/2 ≤ σ) (hs' : σ ≤ 1) :
    ‖mellin (fun x : ℝ => (gaussian Y S x : ℂ)) (σ+t*Complex.I)‖ ≤
      (Y^σ/S*4*Real.exp (Real.pi/4+1))*Real.exp (-|t|/(4*(Y/S))) := by
  have re : ((σ : ℂ)+t*Complex.I).re = σ := by simp
  have im : ((σ : ℂ)+t*Complex.I).im = t := by simp
  have b := gaussian_mellin_bound Y S (σ+t*Complex.I) hY hS hR (by rwa [re]) (by rwa [re])
  rw [re, im, sub_eq_add_neg, Real.exp_add, ← neg_div] at b
  linarith only [b]

theorem gaussian_vertical_integrable (Y S σ : ℝ) (hY : 0 < Y) (hS : 0 < S)
    (hR : 1 ≤ Y/S) (hs : 1/2 ≤ σ) (hs' : σ ≤ 1) :
    Complex.VerticalIntegrable (mellin (fun x : ℝ => (gaussian Y S x : ℂ))) σ := by
  have env : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-|t|/(4*(Y/S)))) :=
    .of_integral_ne_zero (by rw [frequency_envelope_integral _ (by positivity)]; positivity)
  apply (env.const_mul (Y^σ/S*4*Real.exp (Real.pi/4+1))).mono'
  · rw [gaussian_scale_function Y S hY hS]
    simp_rw [mellin_div_const, mellin_comp_mul_left _ _ (inv_pos.mpr hY), smul_eq_mul,
      normalized_gaussian_mellin]
    have hcont : Continuous (fun p : ℝ × ℝ =>
        gaussianLogIntegrand (Y/S) (σ+p.1*Complex.I) p.2) := by
      unfold gaussianLogIntegrand
      fun_prop
    have hcpow : Continuous (fun t : ℝ => ((Y⁻¹ : ℝ) : ℂ)^(-((σ : ℂ)+t*Complex.I))) :=
      (by fun_prop : Continuous (fun t : ℝ => -((σ : ℂ)+t*Complex.I))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (inv_pos.mpr hY).ne'))
    simp only [div_eq_mul_inv]
    exact (hcpow.aestronglyMeasurable.mul
      hcont.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable).mul_const _
  · exact Filter.Eventually.of_forall (fun t => gaussian_line_bound Y S σ t hY hS hR hs hs')

/-- Explicit whole-line and tail integrals for the Gaussian Mellin inversion. -/
theorem gaussian_mellin_integral_bounds (Y S σ T : ℝ) (hY : 0 < Y) (hS : 0 < S)
    (hR : 1 ≤ Y/S) (hs : 1/2 ≤ σ) (hs' : σ ≤ 1) (hT : 0 ≤ T) :
    let M := fun t : ℝ => ‖mellin (fun x : ℝ => (gaussian Y S x : ℂ)) (σ+t*Complex.I)‖
    let D := 4*(Y/S)
    let C := (Y^σ/S*4*Real.exp (Real.pi/4+1))*(2*D)
    (∫ t, M t) ≤ C ∧ (∫ t in {t : ℝ | T < |t|}, M t) ≤ C*Real.exp (-T/D) := by
  dsimp only
  have hD : 0 < 4*(Y/S) := by positivity
  have env : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-|t|/(4*(Y/S)))) :=
    .of_integral_ne_zero (by rw [frequency_envelope_integral _ hD]; positivity)
  have int := (gaussian_vertical_integrable Y S σ hY hS hR hs hs').norm
  have dom := env.const_mul (Y^σ/S*4*Real.exp (Real.pi/4+1))
  have b := fun t => gaussian_line_bound Y S σ t hY hS hR hs hs'
  constructor
  · exact (MeasureTheory.integral_mono int dom b).trans_eq (by
      rw [MeasureTheory.integral_const_mul, frequency_envelope_integral _ hD])
  · exact (MeasureTheory.integral_mono int.integrableOn dom.integrableOn b).trans_eq (by
      rw [MeasureTheory.integral_const_mul, frequency_envelope_tail _ T hD hT]; ring)

/-- All distinct products of subsets of the prime band, including the empty product. -/
def squarefreeSupport (J : Finset ℕ) : Finset ℕ :=
  J.powerset.image (fun S => ∏ p ∈ S, p)

theorem mem_squarefreeSupport (J : Finset ℕ) (hJ : ∀ p ∈ J, Nat.Prime p) (n : ℕ) :
    n ∈ squarefreeSupport J ↔ Squarefree n ∧ n.primeFactors ⊆ J := by
  classical
  constructor
  · rintro hn
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hn
    have subset := Finset.mem_powerset.mp hS
    have primes (p : ℕ) (hp : p ∈ S) := hJ p (subset hp)
    refine ⟨Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp t ht hpt => ?_)
      (fun p hp => (primes p hp).squarefree), ?_⟩
    · exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (primes p hp) (primes t ht)).mpr hpt)
    · rwa [Nat.primeFactors_prod primes]
  · rintro ⟨hn, sub⟩
    exact Finset.mem_image.mpr ⟨n.primeFactors, Finset.mem_powerset.mpr sub,
      Nat.prod_primeFactors_of_squarefree hn⟩

/-- The support can be the finite set of squarefree products from the allowed prime band. -/
def twist (support : Finset ℕ) (weight : ℕ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ support, χ n * weight n

def classMass (support : Finset ℕ) (weight : ℕ → ℂ) (r : (ZMod q)ˣ) : ℂ :=
  ∑ n ∈ support, if (r : ZMod q) = n then weight n else 0

/-- Each integer in the finite Dirichlet series corresponds to exactly one Euler-product term. -/
theorem squarefree_euler_expansion (J : Finset ℕ) (hJ : ∀ p ∈ J, Nat.Prime p)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    twist (squarefreeSupport J) (fun n => (n : ℂ)^(-s)) χ =
      ∏ p ∈ J, (1+(p : ℂ)^(-s)*χ p) := by
  classical
  have unique : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (J.powerset : Set (Finset ℕ)) := by
    intro S hS T hT eq
    have left := Nat.primeFactors_prod (fun p hp => hJ p (Finset.mem_powerset.mp hS hp))
    have right := Nat.primeFactors_prod (fun p hp => hJ p (Finset.mem_powerset.mp hT hp))
    exact left.symm.trans ((congrArg Nat.primeFactors eq).trans right)
  rw [twist, squarefreeSupport, Finset.sum_image unique, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S mem
  clear mem
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul, Nat.cast_mul,
      map_mul, Complex.natCast_mul_natCast_cpow, ← ih]
    ring

/-- Mellin inversion for the finite squarefree Euler product. All integrability
    of the finite twisted sum is deduced from integrability of the window's
    Mellin transform on the chosen line. -/
theorem squarefree_mellin (J : Finset ℕ) (hJ : ∀ p ∈ J, Nat.Prime p)
    (χ : DirichletCharacter ℂ q) (σ : ℝ) (f : ℝ → ℂ)
    (hf : MellinConvergent f σ) (hM : Complex.VerticalIntegrable (mellin f) σ)
    (hc : Continuous f) :
    twist (squarefreeSupport J) (fun n => f n) χ =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (∏ p ∈ J, (1+(p : ℂ)^(-((σ : ℂ)+t*Complex.I))*χ p)) * mellin f (σ+t*Complex.I) := by
  classical
  let S := squarefreeSupport J
  let line (t : ℝ) : ℂ := σ + t*Complex.I
  let c : ℂ := ((1 / (2*Real.pi) : ℝ) : ℂ)
  have spos (n : ℕ) (hn : n ∈ S) : 0 < n :=
    Nat.pos_of_ne_zero ((mem_squarefreeSupport J hJ n).mp hn).1.ne_zero
  have int (n : ℕ) (hn : n ∈ S) :
      MeasureTheory.Integrable (fun t => χ n * ((n : ℂ)^(-line t)*mellin f (line t))) := by
    apply MeasureTheory.Integrable.const_mul
    have pos : (0 : ℝ) < n := by exact_mod_cast spos n hn
    have nz : (n : ℂ) ≠ 0 := by exact_mod_cast (spos n hn).ne'
    have hcont : Continuous (fun t : ℝ => (n : ℂ)^(-line t)) :=
      (by dsimp [line]; fun_prop : Continuous (fun t : ℝ => -line t)).const_cpow (Or.inl nz)
    apply hM.bdd_mul hcont.aestronglyMeasurable (c := (n : ℝ)^(-σ))
    apply Filter.Eventually.of_forall
    intro t
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos pos]
    simp [line]
  have oneTerm (n : ℕ) (hn : n ∈ S) :
      χ n*f n = c * ∫ t : ℝ, χ n * ((n : ℂ)^(-line t)*mellin f (line t)) := by
    rw [MeasureTheory.integral_const_mul, ← mellinInv_mellin_eq σ f
      (by exact_mod_cast spos n hn : (0 : ℝ) < n) hf hM hc.continuousAt]
    simp only [mellinInv, Complex.real_smul, smul_eq_mul, Complex.ofReal_natCast, line, c]
    ring
  change ∑ n ∈ S, χ n * f n = c * ∫ t : ℝ,
    (∏ p ∈ J, (1+(p : ℂ)^(-line t)*χ p)) * mellin f (line t)
  calc
    _ = ∑ n ∈ S, c * ∫ t : ℝ, χ n * ((n : ℂ)^(-line t)*mellin f (line t)) :=
      Finset.sum_congr rfl oneTerm
    _ = c * ∫ t : ℝ, ∑ n ∈ S, χ n * ((n : ℂ)^(-line t)*mellin f (line t)) := by
      rw [← Finset.mul_sum, MeasureTheory.integral_finsetSum S int]
    _ = _ := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [← squarefree_euler_expansion J hJ χ (line t)]
      simp only [twist, Finset.sum_mul, mul_assoc, S]

/-- The finite-frequency Euler bound and the Mellin tail give a bound for
    the original weighted character sum. The tail uses the untwisted absolute
    Euler product on the integration line. -/
theorem squarefree_window_bound (J : Finset ℕ) (hJ : ∀ p ∈ J, Nat.Prime p)
    (χ : DirichletCharacter ℂ q) (σ T A : ℝ) (hA : 0 ≤ A) (f : ℝ → ℂ)
    (hf : MellinConvergent f σ) (hM : Complex.VerticalIntegrable (mellin f) σ)
    (hc : Continuous f)
    (hEuler : ∀ t : ℝ, |t| ≤ T →
      ‖∏ p ∈ J, (1+(p : ℂ)^(-((σ : ℂ)+t*Complex.I))*χ p)‖ ≤ A) :
    let M := fun t : ℝ => ‖mellin f (σ+t*Complex.I)‖
    let E := ∏ p ∈ J, (1+(p : ℝ)^(-σ))
    ‖twist (squarefreeSupport J) (fun n => f n) χ‖ ≤ (1/(2*Real.pi)) *
      (A * (∫ t, M t) + E * ∫ t in {t : ℝ | T < |t|}, M t) := by
  let line (t : ℝ) : ℂ := σ+t*Complex.I
  let F (t : ℝ) := ∏ p ∈ J, (1+(p : ℂ)^(-line t)*χ p)
  let M (t : ℝ) := ‖mellin f (line t)‖
  let E := ∏ p ∈ J, (1+(p : ℝ)^(-σ))
  let tail := {t : ℝ | T < |t|}
  have measurable : MeasurableSet tail := measurableSet_lt measurable_const continuous_abs.measurable
  have hInt : MeasureTheory.Integrable M := hM.norm
  have fullBound (t : ℝ) : ‖F t‖ ≤ E := by
    dsimp only [F, E]
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro p hp
    have pos : (0 : ℝ) < p := by exact_mod_cast (hJ p hp).pos
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ)^(-line t)*χ p‖ := norm_add_le ..
      _ ≤ _ := by
        rw [norm_one, norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos pos]
        simp only [line, Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
          Complex.ofReal_im, neg_zero, add_zero]
        exact add_le_add le_rfl (by
          simpa using mul_le_mul_of_nonneg_left (χ.norm_le_one (p : ZMod q)) (Real.rpow_nonneg pos.le (-σ)))
  have bound (t : ℝ) : ‖F t * mellin f (line t)‖ ≤ A*M t + E*tail.indicator M t := by
    rw [norm_mul]
    by_cases h : T < |t|
    · rw [Set.indicator_of_mem (show t ∈ tail from h)]
      exact (mul_le_mul_of_nonneg_right (fullBound t) (norm_nonneg _)).trans
        (le_add_of_nonneg_left (mul_nonneg hA (norm_nonneg _)))
    · rw [Set.indicator_of_notMem (show t ∉ tail from h), mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (hEuler t (le_of_not_gt h)) (norm_nonneg _)
  have i1 := hInt.const_mul A
  have i2 := (hInt.indicator measurable).const_mul E
  have integralBound := MeasureTheory.norm_integral_le_of_norm_le (i1.add i2)
    (Filter.Eventually.of_forall bound)
  simp only [Pi.add_apply] at integralBound
  rw [MeasureTheory.integral_add i1 i2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator measurable] at integralBound
  rw [squarefree_mellin J hJ χ σ f hf hM hc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ 1/(2*Real.pi) by positivity)]
  exact mul_le_mul_of_nonneg_left integralBound (by positivity)

variable [NeZero q]

/-- Exact character expansion for every reduced residue, including imprimitive characters. -/
theorem orthogonality (support : Finset ℕ) (weight : ℕ → ℂ) (r : (ZMod q)ˣ) :
    (q.totient : ℂ) * classMass support weight r =
      ∑ χ : DirichletCharacter ℂ q, χ (r : ZMod q)⁻¹ * twist support weight χ := by
  classical
  simp only [classMass, twist, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit]
  split_ifs <;> simp

/-- Summing the individual character errors and normalizing by the progression
    step costs at most `q * ε`, uniformly in the reduced residue. -/
theorem uniform_progression_bound (support : Finset ℕ) (weight : ℕ → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hχ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖twist support weight χ‖ ≤ ε)
    (r : (ZMod q)ˣ) :
    ‖(q : ℂ) * classMass support weight r -
      ((q : ℂ) / q.totient) * twist support weight (1 : DirichletCharacter ℂ q)‖ ≤ q * ε := by
  classical
  let error (χ : DirichletCharacter ℂ q) :=
    χ (r : ZMod q)⁻¹ * twist support weight χ -
      (if χ = 1 then twist support weight (1 : DirichletCharacter ℂ q) else 0)
  have herr (χ : DirichletCharacter ℂ q) : ‖error χ‖ ≤ ε := by
    by_cases h : χ = 1
    · subst χ
      simpa [error, ZMod.inv_coe_unit, MulChar.one_apply_coe] using hε
    · simp only [error, if_neg h, sub_zero, norm_mul]
      exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans
        (by simpa using hχ χ h)
  have hexact : (q.totient : ℂ) * classMass support weight r -
      twist support weight (1 : DirichletCharacter ℂ q) = ∑ χ, error χ := by
    rw [orthogonality]
    simp [error, Finset.sum_sub_distrib]
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have bound : ‖(q.totient : ℂ) * classMass support weight r -
      twist support weight (1 : DirichletCharacter ℂ q)‖ ≤ (q.totient : ℝ)*ε := by
    rw [hexact]
    calc
      _ ≤ ∑ χ, ‖error χ‖ := norm_sum_le ..
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, ε := Finset.sum_le_sum (fun χ _ => herr χ)
      _ = _ := by simp [hcard]
  have hp : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
  have hpC : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpR : (0 : ℝ) < q.totient := by exact_mod_cast hp
  have scale : (q : ℂ) * classMass support weight r -
      ((q : ℂ) / q.totient) * twist support weight (1 : DirichletCharacter ℂ q) =
      ((q : ℂ) / q.totient) * ((q.totient : ℂ) * classMass support weight r -
        twist support weight (1 : DirichletCharacter ℂ q)) := by
    rw [mul_sub, ← mul_assoc, div_mul_cancel₀ _ hpC]
  rw [scale, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  calc
    _ ≤ ((q : ℝ)/q.totient) * ((q.totient : ℝ)*ε) :=
      mul_le_mul_of_nonneg_left bound (div_nonneg (Nat.cast_nonneg _) hpR.le)
    _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hpR.ne']

end

end Cogentic.Window
