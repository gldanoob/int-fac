import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Complex MeasureTheory
open scoped BigOperators

namespace Cogentic.Window

noncomputable section

private def phase (z : ℝ) : ℂ := Complex.exp (Complex.I * z)

private theorem norm_phase (z : ℝ) : ‖phase z‖ = 1 := by
  simp [phase, Complex.norm_exp]

private theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp [phase, mul_add, Complex.exp_add]

/-- One normalized, centered prime Euler factor with Bernoulli parameter r. -/
def centeredFactor (r z : ℝ) : ℂ :=
  ((1-r : ℝ) : ℂ)*phase (-r*z) + (r : ℂ)*phase ((1-r)*z)

private theorem norm_centeredFactor_le_one (r z : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1) :
    ‖centeredFactor r z‖ ≤ 1 := by
  apply (norm_add_le ..).trans
  simp only [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, abs_of_nonneg (sub_nonneg.mpr hr')]
  linarith

private theorem centeredFactor_eq (r z : ℝ) :
    centeredFactor r z = phase (-r*z) * (((1-r : ℝ) : ℂ)+(r : ℂ)*phase z) := by
  rw [centeredFactor, show (1-r)*z = -r*z+z by ring, phase_add]
  ring

/-- An exact variance term controls the modulus of a prime factor at every frequency. -/
theorem centeredFactor_decay (r z : ℝ) :
    ‖centeredFactor r z‖ ≤ Real.exp (-r*(1-r)*(1-Real.cos z)) := by
  rw [centeredFactor_eq, norm_mul, norm_phase, one_mul]
  have identity : ‖((1-r : ℝ) : ℂ)+(r : ℂ)*phase z‖^2 =
      1-2*r*(1-r)*(1-Real.cos z) := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_im,
      zero_add, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      phase, Complex.exp_re, Complex.exp_im, Complex.I_mul_re, Complex.I_mul_im,
      neg_zero, Real.exp_zero, one_mul]
    nlinarith [congrArg (fun v : ℝ => r^2*v) (Real.cos_sq_add_sin_sq z)]
  have expbound := Real.add_one_le_exp (-2*r*(1-r)*(1-Real.cos z))
  have sqexp : (Real.exp (-r*(1-r)*(1-Real.cos z)))^2 =
      Real.exp (-2*r*(1-r)*(1-Real.cos z)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  nlinarith [sqexp, Real.exp_pos (-r*(1-r)*(1-Real.cos z))]

private theorem one_sub_cos_lower (z : ℝ) (hz : |z| ≤ 1) : z^2/3 ≤ 1-Real.cos z := by
  let u := |z|/2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu' : u ≤ 1 := by dsimp [u]; linarith
  have ucube : u^3 ≤ u := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hu'), mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu')]
  have sinlow : (5/6)*u ≤ Real.sin u := by linarith [Real.sin_ge_sub_cube hu]
  have sqb := pow_le_pow_left₀ (show 0 ≤ (5/6)*u by positivity) sinlow 2
  have trig : Real.cos z = 1-2*(Real.sin u)^2 := by
    rw [← Real.cos_abs, ← Real.cos_two_mul_eq_one_sub, show 2*u = |z| by dsimp [u]; ring]
  rw [trig]
  have abs2 := sq_abs z
  dsimp [u] at sqb
  nlinarith [sq_nonneg z]

/-- Variance of the tilted prime logarithms. -/
def saddleVariance {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) : ℝ :=
  ∑ p ∈ J, r p*(1-r p)*(ell p)^2

/-- Normalized principal Euler product after canceling its linear phase. -/
def saddleCharacteristic {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (t : ℝ) : ℂ :=
  ∏ p ∈ J, centeredFactor (r p) (t*ell p)

/-- Gaussian majorant for the complete prime product on the central saddle arc. -/
theorem saddle_characteristic_decay {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (t : ℝ) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1)
    (hphase : ∀ p ∈ J, |t*ell p| ≤ 1) :
    ‖saddleCharacteristic J r ell t‖ ≤ Real.exp (-saddleVariance J r ell*t^2/3) := by
  rw [saddleCharacteristic, norm_prod]
  calc
    _ ≤ ∏ p ∈ J, Real.exp (-(r p*(1-r p)*(ell p)^2)*t^2/3) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro p hp
      apply (centeredFactor_decay _ _).trans
      apply Real.exp_le_exp.mpr
      have pos := mul_nonneg (hr p hp) (sub_nonneg.mpr (hr' p hp))
      nlinarith [mul_le_mul_of_nonneg_left (one_sub_cos_lower _ (hphase p hp)) pos]
    _ = _ := by
      rw [← Real.exp_sum, saddleVariance]
      congr 1
      simp only [neg_mul, neg_div, Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul]

private theorem phase_remainder (z : ℝ) :
    ‖phase z-1-Complex.I*z‖ ≤ z^2/2 := by
  let a : ℂ := Complex.I*z
  let f (x : ℝ) := Complex.exp (a*x)-1-a*x
  let g (x : ℝ) := a*(Complex.exp (a*x)-1)
  have der (x : ℝ) : HasDerivAt f (g x) x := by
    have d := (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul a
    convert! ((d.cexp.sub_const 1).sub d) using 1; simp [g]; ring
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun x _ => der x)
    ((by dsimp [g]; fun_prop : Continuous g).intervalIntegrable ..)
  have bound (x : ℝ) (hx : x ∈ Set.Icc 0 1) : ‖g x‖ ≤ z^2*x := by
    have b := @Real.norm_exp_I_mul_ofReal_sub_one_le (z*x)
    simp only [Complex.ofReal_mul, ← mul_assoc, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1] at b
    dsimp only [g]
    rw [norm_mul, show ‖a‖ = |z| by simp [a, Real.norm_eq_abs]]
    exact (mul_le_mul_of_nonneg_left b (abs_nonneg _)).trans_eq (by rw [← mul_assoc, ← sq, sq_abs])
  calc
    _ = ‖∫ x : ℝ in 0..1, g x‖ := by rw [integral]; simp [phase,a,f]
    _ ≤ ∫ x : ℝ in 0..1, ‖g x‖ := intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x : ℝ in 0..1, z^2*x := intervalIntegral.integral_mono_on (by norm_num)
      ((by dsimp [g]; fun_prop : Continuous (fun x => ‖g x‖)).intervalIntegrable ..)
      ((by fun_prop : Continuous (fun x : ℝ => z^2*x)).intervalIntegrable ..) bound
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; ring

private theorem centeredFactor_error (r z : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1) :
    ‖centeredFactor r z-1‖ ≤ r*(1-r)*z^2/2 := by
  let err (x : ℝ) := phase x - 1 - Complex.I*x
  have eqn : centeredFactor r z-1 =
      ((1-r : ℝ) : ℂ)*err (-r*z)+(r : ℂ)*err ((1-r)*z) := by
    dsimp [centeredFactor, err]
    push_cast
    ring
  rw [eqn]
  apply (norm_add_le ..).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, abs_of_nonneg (sub_nonneg.mpr hr')]
  have h1 := mul_le_mul_of_nonneg_left (phase_remainder (-r*z)) (sub_nonneg.mpr hr')
  have h2 := mul_le_mul_of_nonneg_left (phase_remainder ((1-r)*z)) hr
  dsimp [err]
  linarith only [h1,h2]

/-- A second-order estimate for the centered Euler product on every frequency. -/
theorem saddle_characteristic_quadratic_error {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (t : ℝ) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1) :
    ‖saddleCharacteristic J r ell t-1‖ ≤ saddleVariance J r ell*t^2/2 := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [saddleCharacteristic,saddleVariance]
  | insert p J hp ih =>
    have h₁ := hr p (Finset.mem_insert_self ..)
    have h₂ := hr' p (Finset.mem_insert_self ..)
    have hx := norm_centeredFactor_le_one (r p) (t*ell p) h₁ h₂
    have diff := centeredFactor_error (r p) (t*ell p) h₁ h₂
    have tail := ih (fun p h => hr p (Finset.mem_insert_of_mem h))
      (fun p h => hr' p (Finset.mem_insert_of_mem h))
    rw [saddleCharacteristic, Finset.prod_insert hp, saddleVariance, Finset.sum_insert hp]
    change ‖centeredFactor (r p) (t*ell p)*saddleCharacteristic J r ell t-1‖ ≤ _
    rw [show ∀ x y : ℂ, x*y-1 = x*(y-1)+(x-1) by intro x y; ring]
    apply (norm_add_le ..).trans
    rw [norm_mul]
    have scaled := mul_le_mul_of_nonneg_right hx (norm_nonneg (saddleCharacteristic J r ell t-1))
    dsimp [saddleVariance] at tail
    linarith only [scaled, tail, diff]

/-- Lower bound for the real part of the principal saddle integrand. -/
theorem saddle_characteristic_real_lower {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (t : ℝ) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1) :
    1-saddleVariance J r ell*t^2/2 ≤ (saddleCharacteristic J r ell t).re := by
  have e := saddle_characteristic_quadratic_error J r ell t hr hr'
  have re := Complex.re_le_norm (1-saddleCharacteristic J r ell t)
  rw [norm_sub_rev, Complex.sub_re, Complex.one_re] at re
  linarith

private theorem normalized_half_mass (g : ℝ → ℝ) (hg : Continuous g) (b : ℝ) (hb : 3/2 ≤ b)
    (hcentral : ∀ x : ℝ, 1-x^2/2 ≤ g x)
    (htail : ∀ x : ℝ, x ∈ Set.Icc (3/2) b → -Real.exp (-x^2/3) ≤ g x) :
    1/4 ≤ ∫ x : ℝ in 0..b, g x := by
  let a : ℝ := 3/2
  have hint (u v : ℝ) : IntervalIntegrable g volume u v := hg.intervalIntegrable u v
  have central := intervalIntegral.integral_mono_on (show 0 ≤ a by norm_num [a])
    ((by fun_prop : Continuous (fun x : ℝ => 1-x^2/2)).intervalIntegrable ..)
    (hint 0 a) (fun x _ => hcentral x)
  have centralExact : (∫ x : ℝ in 0..a, 1-x^2/2) = 15/16 := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const,
      intervalIntegral.integral_div, integral_pow]
    · norm_num [a]
    all_goals apply Continuous.intervalIntegrable; fun_prop
  rw [centralExact] at central
  have tail := intervalIntegral.integral_mono_on hb
    ((by fun_prop : Continuous (fun x : ℝ => -Real.exp (3/4-x))).intervalIntegrable ..)
    (hint a b) (fun x hx => (neg_le_neg (Real.exp_le_exp.mpr
      (show -x^2/3 ≤ 3/4-x by nlinarith [sq_nonneg (x-3/2)]))).trans (htail x hx))
  have tailExact : (∫ x : ℝ in a..b, -Real.exp (3/4-x)) =
      Real.exp (3/4-b)-Real.exp (-3/4) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => Real.exp (3/4-x))]
    · norm_num [a]
    · intro x _
      convert! ((hasDerivAt_id x).const_sub (3/4)).exp using 1; simp
    · apply Continuous.intervalIntegrable; fun_prop
  have ea : Real.exp (-3/4) ≤ 4/7 := by
    rw [show (-3/4 : ℝ) = -(3/4) by ring, Real.exp_neg, inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith [Real.add_one_le_exp (3/4)]
  rw [tailExact] at tail
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)]
  linarith [Real.exp_pos (3/4-b)]

/-- Explicit lower bound for the entire central saddle mass, including the
    part of the symmetric arc where its real part can be negative. Frequencies
    are expressed in units of inverse standard deviation. -/
theorem saddle_mass_lower {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (W b : ℝ) (hW : 0 < W) (hV : saddleVariance J r ell = W^2)
    (hb : 3/2 ≤ b) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1)
    (hband : ∀ p ∈ J, b*|ell p| ≤ W) :
    1/2 ≤ ∫ x : ℝ in -b..b, (saddleCharacteristic J r ell (x/W)).re := by
  let g (x : ℝ) := (saddleCharacteristic J r ell (x/W)).re
  have cont : Continuous g := by unfold g saddleCharacteristic centeredFactor phase; fun_prop
  have variance (x : ℝ) : saddleVariance J r ell*(x/W)^2 = x^2 := by
    rw [hV]; field_simp
  have center (x : ℝ) : 1-x^2/2 ≤ g x := by
    simpa only [g, variance] using saddle_characteristic_real_lower J r ell (x/W) hr hr'
  have major (x : ℝ) (hx : |x| ≤ b) : -Real.exp (-x^2/3) ≤ g x := by
    have phases (p : ι) (hp : p ∈ J) : |x/W*ell p| ≤ 1 := by
      rw [abs_mul, abs_div, abs_of_pos hW, div_mul_eq_mul_div, div_le_one hW]
      exact (mul_le_mul_of_nonneg_right hx (abs_nonneg _)).trans (hband p hp)
    have c := saddle_characteristic_decay J r ell (x/W) hr hr' phases
    rw [neg_mul, variance] at c
    have negRe := Complex.re_le_norm (-(saddleCharacteristic J r ell (x/W)))
    rw [Complex.neg_re, norm_neg] at negRe
    dsimp only [g]; linarith
  have pos := normalized_half_mass g cont b hb center (fun x hx => major x (by
    rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x)]; exact hx.2))
  have neg := normalized_half_mass (fun x => g (-x)) (cont.comp continuous_neg) b hb
    (fun x => by simpa only [neg_sq] using center (-x))
    (fun x hx => by
      have hnx : |(-x)| ≤ b := by
        rw [abs_neg, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x)]; exact hx.2
      simpa only [neg_sq] using major (-x) hnx)
  rw [intervalIntegral.integral_comp_neg, neg_zero] at neg
  change 1/2 ≤ ∫ x : ℝ in -b..b, g x
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cont.intervalIntegrable (-b) 0) (cont.intervalIntegrable 0 b)]
  linarith

/-- Tilted probability of choosing a prime in the squarefree Euler product. -/
def primeProbability (α : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ)^(-α)/(1+(p : ℝ)^(-α))

def principalEuler (J : Finset ℕ) (s : ℂ) : ℂ := ∏ p ∈ J, (1+(p : ℂ)^(-s))

def saddleMean (J : Finset ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ J, primeProbability α p * Real.log p

private theorem prime_factor_phase (p : ℕ) (hp : 0 < p) (α t : ℝ) :
    (p : ℂ)^(-((α : ℂ)-t*Complex.I)) =
      (((p : ℝ)^(-α) : ℝ) : ℂ)*phase (t*Real.log p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpR.ne'),
    ← Complex.ofReal_log hpR.le, Real.rpow_def_of_pos hpR, Complex.ofReal_exp,
    phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem prime_centered_factor (p : ℕ) (hp : 0 < p) (α t : ℝ) :
      centeredFactor (primeProbability α p) (t*Real.log p) =
        phase (-primeProbability α p*(t*Real.log p)) *
        ((1+(p : ℂ)^(-((α : ℂ)-t*Complex.I))) / (1+(((p:ℝ)^(-α) : ℝ) : ℂ))) := by
    rw [centeredFactor_eq, prime_factor_phase p hp]
    congr 1
    have pos : 0 < 1+(p : ℝ)^(-α) := by positivity
    have nz : (1+(((p:ℝ)^(-α) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast pos.ne'
    simp only [primeProbability, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_add]
    field_simp
    ring

private theorem prime_center_phase (J : Finset ℕ) (α t : ℝ) : (∏ p ∈ J, phase (-primeProbability α p*(t*Real.log p))) =
      Complex.exp (-Complex.I*(t*saddleMean J α)) := by
    simp only [phase, ← Complex.exp_sum]
    congr 1
    simp only [saddleMean, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_neg,
      Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)

/-- The characteristic function used in the saddle bounds is exactly the
    principal squarefree Euler product at the specified complex frequency. -/
theorem saddle_characteristic_euler (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) (α t : ℝ) :
    saddleCharacteristic J (primeProbability α) (fun p => Real.log p) t =
      Complex.exp (-Complex.I*(t*saddleMean J α)) *
        principalEuler J (α-t*Complex.I) / (∏ p ∈ J, (1+(((p:ℝ)^(-α) : ℝ) : ℂ))) := by
  rw [saddleCharacteristic, Finset.prod_congr rfl (fun p hp => prime_centered_factor p (hJ p hp) α t), Finset.prod_mul_distrib,
    Finset.prod_div_distrib, prime_center_phase, principalEuler]
  ring

/-- Explicit lower bound for the actual central prime Euler integral on a
    squarefree band, at its exact logarithmic mean. -/
theorem principal_euler_saddle_mass (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) (α W b : ℝ)
    (hW : 0 < W) (hV : saddleVariance J (primeProbability α) (fun p => Real.log p) = W^2)
    (hb : 3/2 ≤ b) (hband : ∀ p ∈ J, b*|Real.log p| ≤ W) :
    1/2 ≤ ∫ x : ℝ in -b..b,
      (Complex.exp (-Complex.I*((x/W)*saddleMean J α)) *
        principalEuler J (α-(x/W)*Complex.I) / (∏ p ∈ J, (1+(((p:ℝ)^(-α) : ℝ) : ℂ)))).re := by
  have eqn (x : ℝ) := saddle_characteristic_euler J hJ α (x/W)
  simp only [Complex.ofReal_div] at eqn
  conv_rhs => arg 1; intro x; rw [← eqn x]
  apply saddle_mass_lower J _ _ W b hW hV hb _ _ hband
  · intro p hp; unfold primeProbability; positivity
  · intro p hp
    unfold primeProbability
    exact (div_le_one (by positivity)).mpr (by linarith)

private theorem primeProbability_mem (α : ℝ) (p : ℕ) :
    0 ≤ primeProbability α p ∧ primeProbability α p ≤ 1 := by
  unfold primeProbability
  constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr (by linarith)

/-- Differentiating the exact Bernoulli inclusion probability of a prime. -/
theorem primeProbability_derivative (α : ℝ) (p : ℕ) (hp : 0 < p) :
    HasDerivAt (fun a => primeProbability a p)
      (-(Real.log p)*primeProbability α p*(1-primeProbability α p)) α := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have d := (hasDerivAt_neg α).const_rpow hpR
  have pos : 0 < 1+(p : ℝ)^(-α) := by positivity
  convert! d.div (d.const_add 1) pos.ne' using 1
  unfold primeProbability
  field_simp
  ring

/-- The saddle mean decreases at exactly the finite-product variance. -/
theorem saddleMean_derivative (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) (α : ℝ) :
    HasDerivAt (saddleMean J)
      (-saddleVariance J (primeProbability α) (fun p => Real.log p)) α := by
  unfold saddleMean saddleVariance
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro p hp
  convert! (primeProbability_derivative α p (hJ p hp)).mul_const (Real.log p) using 1
  ring

/-- On a dyadic logarithmic band, the saddle equation by itself controls
    the variance in terms of the logarithmic center; no prime asymptotic is required. -/
theorem prime_saddle_variance_bounds (J : Finset ℕ) (α H : ℝ) (ha : 0 ≤ α) (hH : 0 ≤ H)
    (hJ : ∀ p ∈ J, 1 ≤ p) (hband : ∀ p ∈ J, H/2 ≤ Real.log p ∧ Real.log p ≤ H) :
    H*saddleMean J α/4 ≤ saddleVariance J (primeProbability α) (fun p => Real.log p) ∧
      saddleVariance J (primeProbability α) (fun p => Real.log p) ≤ H*saddleMean J α := by
  have one (p : ℕ) (hp : p ∈ J) : primeProbability α p ≤ 1/2 := by
    have pge : (1:ℝ) ≤ p := by exact_mod_cast hJ p hp
    have w := Real.rpow_le_one_of_one_le_of_nonpos pge (neg_nonpos.mpr ha)
    unfold primeProbability
    rw [div_le_iff₀ (by positivity)]
    linarith
  have term (p : ℕ) (hp : p ∈ J) :
      H*(primeProbability α p*Real.log p)/4 ≤
        primeProbability α p*(1-primeProbability α p)*(Real.log p)^2 ∧
      primeProbability α p*(1-primeProbability α p)*(Real.log p)^2 ≤
        H*(primeProbability α p*Real.log p) := by
    let r := primeProbability α p
    have hr : 0 ≤ r := (primeProbability_mem α p).1
    have hr' : r ≤ 1/2 := one p hp
    have lo := (hband p hp).1
    have hi := (hband p hp).2
    have pn : 0 ≤ Real.log p := by linarith
    have scale : 0 ≤ r*Real.log p := mul_nonneg hr pn
    have lb : H/4 ≤ (1-r)*Real.log p := by
      nlinarith [mul_nonneg (show 0 ≤ 1/2-r by linarith) pn]
    have ub : (1-r)*Real.log p ≤ H := by nlinarith [mul_nonneg hr pn]
    change H*(r*Real.log p)/4 ≤ _ ∧ _ ≤ H*(r*Real.log p)
    constructor
    · exact (show H*(r*Real.log p)/4 = H/4*(r*Real.log p) by ring).le.trans
        ((mul_le_mul_of_nonneg_right lb scale).trans_eq (by dsimp [r]; ring))
    · exact (show _ = ((1-r)*Real.log p)*(r*Real.log p) by dsimp [r]; ring).le.trans
        (mul_le_mul_of_nonneg_right ub scale)
  unfold saddleMean saddleVariance
  simp only [Finset.mul_sum, Finset.sum_div]
  exact ⟨Finset.sum_le_sum (fun p hp => (term p hp).1), Finset.sum_le_sum (fun p hp => (term p hp).2)⟩

/-- Third and fourth cumulants of the tilted prime logarithms. -/
def saddleThird (J : Finset ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ J, let r := primeProbability α p
    r*(1-r)*(1-2*r)*(Real.log p)^3

def saddleFourth (J : Finset ℕ) (α : ℝ) : ℝ :=
  ∑ p ∈ J, let r := primeProbability α p
    r*(1-r)*(1-6*r*(1-r))*(Real.log p)^4

theorem saddleVariance_derivative (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) (α : ℝ) :
    HasDerivAt (fun a => saddleVariance J (primeProbability a) (fun p => Real.log p))
      (-saddleThird J α) α := by
  unfold saddleVariance saddleThird
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro p hp
  have d := primeProbability_derivative α p (hJ p hp)
  convert! (d.mul (d.const_sub 1)).mul_const ((Real.log p)^2) using 1
  ring

theorem saddleThird_derivative (J : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) (α : ℝ) :
    HasDerivAt (saddleThird J) (-saddleFourth J α) α := by
  unfold saddleThird saddleFourth
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro p hp
  have d := primeProbability_derivative α p (hJ p hp)
  convert! ((d.mul (d.const_sub 1)).mul ((d.const_mul 2).const_sub 1)).mul_const
    ((Real.log p)^3) using 1
  simp only [Pi.mul_apply]
  ring

/-- Uniform finite-band bounds for the two cumulants in the Edgeworth term. -/
theorem saddle_cumulants_bound (J : Finset ℕ) (α H : ℝ)
    (hband : ∀ p ∈ J, |Real.log p| ≤ H) :
    let V := saddleVariance J (primeProbability α) (fun p => Real.log p)
    |saddleThird J α| ≤ V*H ∧ |saddleFourth J α| ≤ V*H^2 := by
  dsimp only
  unfold saddleThird saddleFourth saddleVariance
  rw [Finset.sum_mul, Finset.sum_mul]
  constructor
  all_goals
    apply (Finset.abs_sum_le_sum_abs ..).trans
    apply Finset.sum_le_sum
    intro p hp
    let r := primeProbability α p
    let l := Real.log p
    have hr : 0 ≤ r := (primeProbability_mem α p).1
    have hr' : r ≤ 1 := (primeProbability_mem α p).2
    have v : 0 ≤ r*(1-r) := mul_nonneg hr (sub_nonneg.mpr hr')
    have w : 0 ≤ r*(1-r)*l^2 := mul_nonneg v (sq_nonneg l)
    have lh : |l| ≤ H := hband p hp
  · have shape : |1-2*r| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    change |r*(1-r)*(1-2*r)*l^3| ≤ r*(1-r)*l^2*H
    rw [show r*(1-r)*(1-2*r)*l^3 = (r*(1-r)*l^2)*((1-2*r)*l) by ring,
      abs_mul, abs_of_nonneg w, abs_mul]
    gcongr
    exact (mul_le_mul_of_nonneg_right shape (abs_nonneg l)).trans (by simpa using lh)
  · have shape : |1-6*r*(1-r)| ≤ 1 := abs_le.mpr
      ⟨by nlinarith [sq_nonneg (r-1/2)], by linarith⟩
    change |r*(1-r)*(1-6*r*(1-r))*l^4| ≤ r*(1-r)*l^2*H^2
    rw [show r*(1-r)*(1-6*r*(1-r))*l^4 = (r*(1-r)*l^2)*((1-6*r*(1-r))*l^2) by ring,
      abs_mul, abs_of_nonneg w, abs_mul, abs_of_nonneg (sq_nonneg l)]
    apply mul_le_mul_of_nonneg_left _ w
    apply (mul_le_mul_of_nonneg_right shape (sq_nonneg l)).trans
    simpa using pow_le_pow_left₀ (abs_nonneg l) lh 2

/-- Absolute bound for the first relative Edgeworth coefficient with its
    exact fourth-cumulant and squared-third-cumulant constants. -/
theorem saddle_edgeworth_coefficient (J : Finset ℕ) (α H : ℝ)
    (hband : ∀ p ∈ J, |Real.log p| ≤ H)
    (hV : 0 < saddleVariance J (primeProbability α) (fun p => Real.log p)) :
    let V := saddleVariance J (primeProbability α) (fun p => Real.log p)
    |saddleFourth J α/(8*V^2) - 5*(saddleThird J α)^2/(24*V^3)| ≤ H^2/(3*V) := by
  let V := saddleVariance J (primeProbability α) (fun p => Real.log p)
  change |saddleFourth J α/(8*V^2) - 5*(saddleThird J α)^2/(24*V^3)| ≤ H^2/(3*V)
  have hV' : 0 < V := hV
  obtain ⟨third, fourth⟩ := saddle_cumulants_bound J α H hband
  change |saddleThird J α| ≤ V*H at third
  change |saddleFourth J α| ≤ V*H^2 at fourth
  have thirdSq := pow_le_pow_left₀ (abs_nonneg _) third 2
  rw [sq_abs] at thirdSq
  apply (abs_sub _ _).trans
  rw [abs_div, abs_of_pos (show 0 < 8*V^2 by positivity),
    abs_of_nonneg (show 0 ≤ 5*(saddleThird J α)^2/(24*V^3) by positivity)]
  calc
    _ ≤ (V*H^2)/(8*V^2)+5*(V*H)^2/(24*V^3) := by gcongr
    _ = _ := by field_simp; ring

private theorem small_sine_defect (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    x^3/9 ≤ x-Real.sin x := by
  have b := intervalIntegral.integral_mono_on (μ := volume) hx
    ((by fun_prop : Continuous (fun y : ℝ => y^2/3)).intervalIntegrable ..)
    ((by fun_prop : Continuous (fun y : ℝ => 1-Real.cos y)).intervalIntegrable ..)
    (fun y hy => one_sub_cos_lower y (by rw [abs_of_nonneg hy.1]; exact hy.2.trans hx'))
  rw [intervalIntegral.integral_div, integral_pow, intervalIntegral.integral_sub,
      intervalIntegral.integral_const, integral_cos] at b
  · norm_num at b; linarith
  all_goals apply Continuous.intervalIntegrable; fun_prop

private theorem sine_defect (h u : ℝ) (hh : 0 < h) (hh' : h ≤ 1) (hu : h/2 ≤ u) :
    u*h^2/36 ≤ u-|Real.sin u| := by
  have up : 0 < u := by linarith
  have hs : h^2 ≤ 1 := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh')]
  by_cases small : u ≤ 1
  · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi up.le (by linarith [Real.two_le_pi]))]
    have sq := pow_le_pow_left₀ (show 0 ≤ h/2 by positivity) hu 2
    nlinarith [mul_le_mul_of_nonneg_left sq up.le, small_sine_defect u up.le small]
  · by_cases mid : u ≤ 2
    · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi up.le (mid.trans Real.two_le_pi))]
      have lip := Real.abs_sin_sub_sin_le u 1
      rw [abs_of_nonneg (by linarith : 0 ≤ u-1)] at lip
      nlinarith [mul_le_mul_of_nonneg_left hs up.le, le_abs_self (Real.sin u-Real.sin 1),
        small_sine_defect 1 zero_le_one le_rfl]
    · nlinarith [Real.abs_sin_le_one u, mul_le_mul_of_nonneg_left hs up.le]

/-- Uniform nonresonance on a log-band of length h, with no dependence
    on the initial phase. This includes intervals centered on a multiple of 2π. -/
theorem cosine_band_gap (a h ω : ℝ) (hh : 0 < h) (hh' : h ≤ 1) (hω : 1 ≤ ω) :
    h^3/36 ≤ ∫ v : ℝ in a..a+h, 1-Real.cos (ω*v) := by
  have wp : 0 < ω := zero_lt_one.trans_le hω
  let u := ω*h/2
  have ugap := sine_defect h u hh hh' (by dsimp [u]; nlinarith [mul_nonneg (sub_nonneg.mpr hω) hh.le])
  have osc : (∫ v : ℝ in a..a+h, Real.cos (ω*v)) =
      (Real.sin (ω*(a+h))-Real.sin (ω*a))/ω := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun v => Real.sin (ω*v)/ω)]
    · ring
    · intro x _
      convert! (((hasDerivAt_id x).const_mul ω).sin.div_const ω) using 1
      field_simp
      rfl
    · apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const, osc]
  · simp only [smul_eq_mul, mul_one, add_sub_cancel_left]
    rw [Real.sin_sub_sin, show (ω*(a+h)-ω*a)/2 = u by dsimp [u]; ring]
    let θ := (ω*(a+h)+ω*a)/2
    have upper : Real.sin u*Real.cos θ ≤ |Real.sin u| := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg (Real.sin u))
    have num : h^3/36*ω ≤ h*ω-2*Real.sin u*Real.cos θ := by
      dsimp [u] at ugap
      change _ ≤ h*ω-2*Real.sin (ω*h/2)*Real.cos θ
      dsimp [u] at upper
      linarith only [ugap,upper]
    change h^3/36 ≤ h-2*Real.sin u*Real.cos θ/ω
    rw [show h-2*Real.sin u*Real.cos θ/ω = (h*ω-2*Real.sin u*Real.cos θ)/ω by field_simp]
    exact (le_div_iff₀ wp).mpr num
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- Lower bound for the actual continuous prime main term on the upper
    saddle band, uniformly over all positive and negative frequencies. -/
theorem saddle_weighted_cosine_gap (lam ω : ℝ) (hlam : 2 ≤ lam) (hω : 1 ≤ |ω|) :
    Real.exp (lam-1)/(36*lam^3) ≤
      ∫ v : ℝ in (1-1/lam)..1, Real.exp (lam*v)/v*(1-Real.cos (ω*v)) := by
  let h := 1/lam
  let a := 1-h
  have lp : 0 < lam := by linarith
  have hp : 0 < h := by dsimp [h]; positivity
  have hhalf : h ≤ 1/2 := by dsimp [h]; exact one_div_le_one_div_of_le zero_lt_two hlam
  have hid : a+h = 1 := by dsimp [a]; ring
  have ah : a ≤ 1 := by dsimp [a]; linarith
  have cosabs (v : ℝ) : Real.cos (|ω| * v) = Real.cos (ω*v) := by
    rcases le_or_gt 0 ω with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_neg hz, neg_mul, Real.cos_neg]
  have gap := cosine_band_gap a h |ω| hp (by linarith) hω
  simp_rw [cosabs] at gap
  rw [hid] at gap
  have cont : ContinuousOn (fun v : ℝ => Real.exp (lam*v)/v*(1-Real.cos (ω*v))) (Set.uIcc a 1) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.div (by fun_prop) continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le ah] at hx
      have : 0 < x := by dsimp [a] at hx; linarith [hx.1]
      exact this.ne'
    · fun_prop
  have lower (v : ℝ) (hv : v ∈ Set.Icc a 1) :
      Real.exp (lam-1)*(1-Real.cos (ω*v)) ≤ Real.exp (lam*v)/v*(1-Real.cos (ω*v)) := by
    have vp : 0 < v := by dsimp [a] at hv; linarith [hv.1]
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr (Real.cos_le_one _))
    rw [le_div_iff₀ vp]
    have e : lam-1 ≤ lam*v := by
      have m := mul_le_mul_of_nonneg_left hv.1 lp.le
      dsimp [a, h] at m
      rwa [mul_sub, mul_one, mul_one_div_cancel lp.ne'] at m
    exact (mul_le_mul_of_nonneg_left hv.2 (Real.exp_pos _).le).trans
      (by simpa only [mul_one] using Real.exp_le_exp.mpr e)
  have bound := intervalIntegral.integral_mono_on (μ := volume) ah
    ((by fun_prop : Continuous (fun v : ℝ => Real.exp (lam-1)*(1-Real.cos (ω*v)))).intervalIntegrable ..)
    cont.intervalIntegrable lower
  rw [intervalIntegral.integral_const_mul] at bound
  calc
    _ = Real.exp (lam-1)*(h^3/36) := by dsimp [h]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left gap (Real.exp_pos _).le).trans bound

private def gaussianMoment (b : ℝ) (k : ℕ) : ℝ :=
  ∫ x : ℝ, x^(2*k)*Real.exp (-b*x^2)

private theorem gaussianMoment_gamma (b : ℝ) (hb : 0 < b) (k : ℕ) :
    gaussianMoment b k = b^(-((2*(k:ℝ)+1)/2))*Real.Gamma ((2*(k:ℝ)+1)/2) := by
  have g := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := (2:ℝ)) (q := ((2*k:ℕ):ℝ))
    (by norm_num) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)) hb
  simp only [Real.rpow_natCast, Real.rpow_two] at g
  simp only [Nat.cast_mul, Nat.cast_ofNat] at g
  calc
    _ = ∫ x : ℝ, |x|^(2*k)*Real.exp (-b*|x|^2) := by simp [gaussianMoment, pow_abs_two_mul]
    _ = 2*∫ x in Set.Ioi (0:ℝ), x^(2*k)*Real.exp (-b*x^2) :=
      integral_comp_abs (f := fun x => x^(2*k)*Real.exp (-b*x^2))
    _ = _ := by rw [g, neg_div]; ring

private theorem gaussianMoment_succ (V : ℝ) (hV : 0 < V) (k : ℕ) :
    gaussianMoment (V/2) (k+1) = (2*(k:ℝ)+1)/V * gaussianMoment (V/2) k := by
  have hpos : 0 < V/2 := by positivity
  let a := (2*(k:ℝ)+1)/2
  have ha : 0 < a := by dsimp [a]; positivity
  rw [gaussianMoment_gamma (V/2) hpos, gaussianMoment_gamma (V/2) hpos]
  push_cast
  rw [show (2*((k:ℝ)+1)+1)/2 = a+1 by dsimp [a]; ring,
    Real.Gamma_add_one ha.ne', neg_add', Real.rpow_sub hpos, Real.rpow_one]
  dsimp [a]
  field_simp

/-- Integrating the fourth- and sixth-degree saddle corrections produces
    exactly the first relative Edgeworth term. -/
theorem saddle_edgeworth_integral (V K₃ K₄ : ℝ) (hV : 0 < V) :
    (∫ x : ℝ, Real.exp (-(V/2)*x^2)*(1+K₄*x^4/24-K₃^2*x^6/72)) =
      Real.sqrt (2*Real.pi/V)*(1+K₄/(8*V^2)-5*K₃^2/(24*V^3)) := by
  let G (x : ℝ) := Real.exp (-(V/2)*x^2)
  have integ (k : ℕ) : Integrable (fun x : ℝ => x^k*G x) := by
    simpa [G] using integrable_rpow_mul_exp_neg_mul_sq (b := V/2) (s := (k:ℝ))
      (by positivity) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  have i0 : Integrable G := by simpa only [pow_zero, one_mul] using integ 0
  have i4 := (integ 4).const_mul (K₄/24)
  have i6 := (integ 6).const_mul (K₃^2/72)
  have m0 : gaussianMoment (V/2) 0 = Real.sqrt (2*Real.pi/V) := by
    simp only [gaussianMoment, Nat.mul_zero, pow_zero, one_mul, integral_gaussian]
    congr 1
    ring
  have m1 := gaussianMoment_succ V hV 0
  have m2 := gaussianMoment_succ V hV 1
  have m3 := gaussianMoment_succ V hV 2
  norm_num at m1 m2 m3
  rw [m0] at m1
  rw [m1] at m2
  rw [m2] at m3
  calc
    _ = ∫ x : ℝ, G x+(K₄/24)*(x^4*G x)-(K₃^2/72)*(x^6*G x) := by
      congr 1
      funext x
      dsimp [G]
      ring
    _ = gaussianMoment (V/2) 0 + K₄/24*gaussianMoment (V/2) 2 -
        K₃^2/72*gaussianMoment (V/2) 3 := by
      have i04 : Integrable (fun x : ℝ => G x+K₄/24*(x^4*G x)) := i0.add i4
      rw [integral_sub i04 i6, integral_add i0 i4, integral_const_mul, integral_const_mul]
      simp [gaussianMoment,G]
    _ = _ := by rw [m0,m2,m3]; field_simp; ring

/-- Logarithm of the centered compound Poisson approximation to the tilted
    Euler product. Its Taylor coefficients are the raw prime logarithm moments. -/
def poissonExponent {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ J, (r p : ℂ)*(phase (t*ell p)-1-Complex.I*(t*ell p : ℝ))

private def poissonFactor (r z : ℝ) : ℂ :=
  Complex.exp ((r : ℂ)*(phase z-1-Complex.I*z))

private theorem poissonFactor_eq (r z : ℝ) :
    poissonFactor r z = phase (-r*z)*Complex.exp ((r : ℂ)*(phase z-1)) := by
  change Complex.exp _ = Complex.exp (Complex.I*(-r*z : ℝ))*Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_poissonFactor (r z : ℝ) (hr : 0 ≤ r) : ‖poissonFactor r z‖ ≤ 1 := by
  rw [poissonFactor_eq, norm_mul, norm_phase, one_mul, Complex.norm_exp,
    Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos hr
    (sub_nonpos.mpr ((Complex.re_le_norm _).trans_eq (norm_phase z)))

private theorem poisson_factor_error (r z : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/2) :
    ‖centeredFactor r z-poissonFactor r z‖ ≤ 4*r^2 := by
  let w := (r : ℂ)*(phase z-1)
  have small : ‖w‖ ≤ 2*r := by
    dsimp only [w]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, mul_comm (2:ℝ)]
    apply mul_le_mul_of_nonneg_left _ hr
    exact (norm_sub_le ..).trans_eq (by rw [norm_phase, norm_one]; norm_num)
  have b := Complex.norm_exp_sub_one_sub_id_le (small.trans (show 2*r ≤ 1 by linarith))
  rw [centeredFactor_eq, poissonFactor_eq, ← mul_sub, norm_mul, norm_phase, one_mul]
  have eqn : ((1-r : ℝ) : ℂ)+(r : ℂ)*phase z = 1+w := by dsimp [w]; push_cast; ring
  rw [eqn, norm_sub_rev]
  change ‖Complex.exp w-(1+w)‖ ≤ _
  rw [show Complex.exp w-(1+w) = Complex.exp w-1-w by ring]
  exact b.trans ((pow_le_pow_left₀ (norm_nonneg _) small 2).trans_eq (by ring))

/-- Uniform Poisson approximation for the complete centered Euler product.
    The explicit squared-probability cost is negligible on the prime band. -/
theorem saddle_poisson_approximation {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (t : ℝ)
    (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2) :
    ‖saddleCharacteristic J r ell t - Complex.exp (poissonExponent J r ell t)‖ ≤
      4*∑ p ∈ J, (r p)^2 := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [saddleCharacteristic,poissonExponent]
  | insert p J hp ih =>
    have hrp := hr p (Finset.mem_insert_self ..)
    have hhalf := hr' p (Finset.mem_insert_self ..)
    have tail := ih (fun p h => hr p (Finset.mem_insert_of_mem h))
      (fun p h => hr' p (Finset.mem_insert_of_mem h))
    let A := centeredFactor (r p) (t*ell p)
    let B := poissonFactor (r p) (t*ell p)
    let X := saddleCharacteristic J r ell t
    let Y := Complex.exp (poissonExponent J r ell t)
    have A1 : ‖A‖ ≤ 1 := norm_centeredFactor_le_one _ _ hrp (by linarith)
    have Y1 : ‖Y‖ ≤ 1 := by
      rw [show Y = ∏ q ∈ J, poissonFactor (r q) (t*ell q) by simp [Y,poissonFactor,poissonExponent,Complex.exp_sum]]
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun q hq => norm_poissonFactor _ _ (hr q (Finset.mem_insert_of_mem hq)))
    have ab : ‖A-B‖ ≤ 4*(r p)^2 := poisson_factor_error _ _ hrp hhalf
    rw [saddleCharacteristic, Finset.prod_insert hp, poissonExponent, Finset.sum_insert hp,
      Complex.exp_add, Finset.sum_insert hp]
    change ‖A*X-B*Y‖ ≤ _
    rw [show A*X-B*Y=A*(X-Y)+(A-B)*Y by ring]
    apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul]
    have left := mul_le_mul_of_nonneg_right A1 (norm_nonneg (X-Y))
    have right := mul_le_mul_of_nonneg_left Y1 (norm_nonneg (A-B))
    change ‖X-Y‖ ≤ _ at tail
    linarith

private def phasePolynomial (z : ℝ) : ℂ :=
  -(z : ℂ)^2/2 - Complex.I*(z : ℂ)^3/6 + (z : ℂ)^4/24 + Complex.I*(z : ℂ)^5/120

private theorem phase_fifth_order (z : ℝ) (hz : |z| ≤ 1) :
    ‖phase z-1-Complex.I*z-phasePolynomial z‖ ≤ |z|^6 * Real.exp 1 := by
  have rem := Complex.norm_exp_sub_sum_le_norm_mul_exp (Complex.I*z) 6
  have pol : (∑ m ∈ Finset.range 6, (Complex.I*z)^m / (m.factorial : ℂ)) =
      1+Complex.I*z+phasePolynomial z := by
    unfold phasePolynomial
    norm_num [Finset.sum_range_succ, mul_pow, Complex.I_pow_three, Complex.I_pow_four,
      show Complex.I^5 = Complex.I by rw [pow_succ,Complex.I_pow_four,one_mul]]
    ring
  rw [pol, show ‖Complex.I*z‖ = |z| by simp [Real.norm_eq_abs]] at rem
  rw [show phase z-1-Complex.I*z-phasePolynomial z = phase z-(1+Complex.I*z+phasePolynomial z) by ring]
  exact rem.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz) (by positivity))

/-- The raw logarithm moments of the compound Poisson prime model. -/
def poissonMoment {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ J, r p*(ell p)^k

/-- Explicit sixth-order Taylor remainder for the logarithm of the Poisson
    model, on the entire central arc of the prime Euler product. -/
theorem poisson_exponent_expansion {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (t H : ℝ)
    (hr : ∀ p ∈ J, 0 ≤ r p) (hband : ∀ p ∈ J, |ell p| ≤ H)
    (hphase : ∀ p ∈ J, |t*ell p| ≤ 1) :
    let M := poissonMoment J r ell
    let P : ℂ := -((M 2 : ℝ):ℂ)*(t:ℂ)^2/2
      -Complex.I*(M 3 : ℝ)*(t:ℂ)^3/6 + (M 4 : ℝ)*(t:ℂ)^4/24
      + Complex.I*(M 5 : ℝ)*(t:ℂ)^5/120
    ‖poissonExponent J r ell t - P‖ ≤ Real.exp 1*M 2*H^4*|t|^6 := by
  classical
  dsimp only
  let P := ∑ p ∈ J, (r p : ℂ)*phasePolynomial (t*ell p)
  have parts : P = -((poissonMoment J r ell 2 : ℝ):ℂ)*(t:ℂ)^2/2
      -Complex.I*(poissonMoment J r ell 3 : ℝ)*(t:ℂ)^3/6
      + (poissonMoment J r ell 4 : ℝ)*(t:ℂ)^4/24
      + Complex.I*(poissonMoment J r ell 5 : ℝ)*(t:ℂ)^5/120 := by
    simp only [P, poissonMoment, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      neg_mul, ← Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    simp only [phasePolynomial, Complex.ofReal_mul]
    ring
  rw [← parts, poissonExponent]
  change ‖(∑ p ∈ J, _) - ∑ p ∈ J, (r p : ℂ)*phasePolynomial (t*ell p)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  simp only [poissonMoment, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr p hp)]
  have b := mul_le_mul_of_nonneg_left (phase_fifth_order _ (hphase p hp)) (hr p hp)
  apply b.trans
  rw [abs_mul, mul_pow]
  have pw := pow_le_pow_left₀ (abs_nonneg _) (hband p hp) 4
  have extra := mul_le_mul_of_nonneg_left pw (sq_nonneg (ell p))
  have weight : 0 ≤ Real.exp 1*r p*|t|^6 := by positivity [hr p hp]
  have bound := mul_le_mul_of_nonneg_left extra weight
  rw [show |ell p|^4 = (ell p)^4 by exact (by decide : Even 4).pow_abs _] at bound
  rw [show |ell p|^6 = (ell p)^6 by exact (by decide : Even 6).pow_abs _]
  linarith only [bound]

private theorem exp_difference (z w : ℂ) (A : ℝ) (hz : z.re ≤ A) (hw : w.re ≤ A) :
    ‖Complex.exp z-Complex.exp w‖ ≤ Real.exp A*‖z-w‖ := by
  let f (x : ℝ) := Complex.exp (w+(z-w)*x)
  let g (x : ℝ) := f x*(z-w)
  have der (x : ℝ) : HasDerivAt f (g x) x := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (z-w)).const_add w
    convert! h.cexp using 1; simp [f,g]
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun x _ => der x)
    ((by dsimp [f,g]; fun_prop : Continuous g).intervalIntegrable ..)
  calc
    _ = ‖∫ x : ℝ in 0..1, g x‖ := by rw [integral]; simp [f]
    _ ≤ _ := by
      apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp A*‖z-w‖) ?_).trans_eq
      · norm_num
      · intro x hx
        rw [Set.uIoc_of_le zero_le_one] at hx
        dsimp only [g,f]
        rw [norm_mul,Complex.norm_exp]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        simp only [Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.ofReal_im,
          Complex.ofReal_re,mul_zero,sub_zero]
        nlinarith [mul_nonneg (sub_nonneg.mpr hz) hx.1.le,
          mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hx.2)]

private theorem cos_quad_error (x : ℝ) : |Real.cos x-1| ≤ x^2/2 := by
  have re := Complex.abs_re_le_norm (phase x-1-Complex.I*x)
  have b := re.trans (phase_remainder x)
  simpa [phase,Complex.sub_re,Complex.exp_re] using b

private theorem cos_fourth_error (x : ℝ) : |Real.cos x-1+x^2/2| ≤ (Real.exp 1+3)*x^4 := by
  by_cases small : |x| ≤ 1
  · have rem := Complex.norm_exp_sub_sum_le_norm_mul_exp (Complex.I*x) 4
    have pol : (∑ m ∈ Finset.range 4, (Complex.I*x)^m / (m.factorial : ℂ)) =
        1+Complex.I*x-(x : ℂ)^2/2-Complex.I*(x:ℂ)^3/6 := by
      norm_num [Finset.sum_range_succ,mul_pow,Complex.I_pow_three]; ring
    rw [pol, show ‖Complex.I*x‖ = |x| by simp [Real.norm_eq_abs]] at rem
    have re := Complex.abs_re_le_norm
      (phase x-(1+Complex.I*x-(x : ℂ)^2/2-Complex.I*(x:ℂ)^3/6))
    have rid : (phase x-(1+Complex.I*x-(x : ℂ)^2/2-Complex.I*(x:ℂ)^3/6)).re =
        Real.cos x-1+x^2/2 := by
      norm_num [phase,Complex.sub_re,Complex.add_re,Complex.exp_re,Complex.div_re,
        ← Complex.ofReal_pow]
      ring
    rw [rid] at re
    apply (re.trans rem).trans
    rw [show |x|^4 = x^4 by exact (by decide : Even 4).pow_abs _]
    nlinarith [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr small) (show 0 ≤ x^4 by positivity),
      show 0 ≤ x^4 by positivity]
  · have h1 : 1 ≤ x^2 := by
      simpa only [one_pow,sq_abs] using pow_le_pow_left₀ zero_le_one (le_of_not_ge small) 2
    have h2 : x^2 ≤ x^4 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h1)]
    apply (abs_add_le ..).trans
    rw [abs_of_nonneg (by positivity : 0 ≤ x^2/2)]
    nlinarith [cos_quad_error x, mul_nonneg (Real.exp_pos 1).le (show 0 ≤ x^4 by positivity)]

private theorem exp_quadratic_error (c : ℝ) (hc : 0 ≤ c) :
    |Real.exp c-1-c| ≤ c^2 * Real.exp c := by
  have b := Complex.norm_exp_sub_sum_le_norm_mul_exp (c : ℂ) 2
  norm_num [Finset.sum_range_succ, Real.norm_eq_abs, abs_of_nonneg hc] at b
  rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at b
  simpa [sub_add_eq_sub_sub] using b

private theorem exponential_polynomial_error (a b c d : ℝ) (hc : 0 ≤ c) :
    |Real.exp (a+c)*Real.cos (b+d) - Real.exp a*(1+c-b^2/2)| ≤
      Real.exp (a+c)*c^2 + Real.exp a*
        (c*(b+d)^2/2+(Real.exp 1+3)*(b+d)^4+|b*d|+d^2/2) := by
  let k := Real.cos (b+d)
  let u := (Real.exp c-1-c)*k
  let v := c*(k-1)
  let w := k-1+(b+d)^2/2
  have hu : |u| ≤ c^2*Real.exp c := by
    dsimp only [u]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (by simpa using exp_quadratic_error c hc)
  have hv : |v| ≤ c*(b+d)^2/2 := by
    dsimp only [v]
    rw [abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left (cos_quad_error _) hc).trans_eq (by ring)
  have hw : |w| ≤ (Real.exp 1+3)*(b+d)^4 := cos_fourth_error _
  have sum : |u+v+w-b*d-d^2/2| ≤
      c^2*Real.exp c+c*(b+d)^2/2+(Real.exp 1+3)*(b+d)^4+|b*d|+d^2/2 := by
    calc
      _ ≤ (|u|+|v|+|w|+|b*d|)+|d^2/2| := by
        apply (abs_sub ..).trans
        gcongr
        apply (abs_sub ..).trans
        gcongr
        apply (abs_add_le ..).trans
        gcongr
        exact abs_add_le ..
      _ ≤ _ := by rw [abs_of_nonneg (by positivity : 0 ≤ d^2/2)]; linarith
  rw [Real.exp_add]
  rw [show Real.exp a*Real.exp c*Real.cos (b+d)-Real.exp a*(1+c-b^2/2) =
    Real.exp a*(u+v+w-b*d-d^2/2) by dsimp [u,v,w,k]; ring]
  rw [abs_mul, abs_of_pos (Real.exp_pos a)]
  exact (mul_le_mul_of_nonneg_left sum (Real.exp_pos _).le).trans_eq (by ring)

/-- Error in the real exponential after the first Edgeworth correction. It
    includes both the complex Taylor error and the effect of the odd terms. -/
theorem real_edgeworth_error (z : ℂ) (A a b c d E : ℝ) (hc : 0 ≤ c)
    (hz : z.re ≤ A) (ha : a+c ≤ A)
    (hE : ‖z-((a+c : ℝ)+(b+d : ℝ)*Complex.I)‖ ≤ E) :
    |(Complex.exp z).re - Real.exp a*(1+c-b^2/2)| ≤
      Real.exp A*(E+c^2+c*(b+d)^2/2+(Real.exp 1+3)*(b+d)^4+|b*d|+d^2/2) := by
  let p : ℂ := (a+c : ℝ)+(b+d : ℝ)*Complex.I
  have pr : p.re = a+c := by simp [p]
  have pi : p.im = b+d := by simp [p]
  have pe : (Complex.exp p).re = Real.exp (a+c)*Real.cos (b+d) := by rw [Complex.exp_re, pr, pi]
  have first : |(Complex.exp z).re-(Complex.exp p).re| ≤ Real.exp A*E := by
    apply (Complex.abs_re_le_norm (Complex.exp z-Complex.exp p)).trans
    exact (exp_difference z p A hz (pr.le.trans ha)).trans
      (mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le)
  have second := exponential_polynomial_error a b c d hc
  have h1 := Real.exp_le_exp.mpr ha
  have h2 := Real.exp_le_exp.mpr (show a ≤ A by linarith)
  have qpos : 0 ≤ c*(b+d)^2/2+(Real.exp 1+3)*(b+d)^4+|b*d|+d^2/2 := by positivity
  have split := abs_sub_le (Complex.exp z).re (Complex.exp p).re (Real.exp a*(1+c-b^2/2))
  rw [pe] at first split
  linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg c), mul_le_mul_of_nonneg_right h2 qpos]

private theorem edgeworth_polynomial_bound (u y b c d : ℝ) (hu : 0 ≤ u)
    (hy : 0 ≤ y) (hy' : y ≤ 1) (hb : |b| ≤ u*y) (hc : 0 ≤ c) (hc' : c ≤ u*y^2)
    (hd : |d| ≤ u*y^3) :
    Real.exp 1*u*y^4+c^2+c*(b+d)^2/2+(Real.exp 1+3)*(b+d)^4+|b*d|+d^2/2 ≤
      y^4*(Real.exp 1*u+3*u^2+2*u^3+16*(Real.exp 1+3)*u^4) := by
  have y2 : y^2 ≤ 1 := by nlinarith [mul_nonneg hy (sub_nonneg.mpr hy')]
  have y3 : y^3 ≤ y := by nlinarith [mul_le_mul_of_nonneg_left y2 hy]
  have sum : |b+d| ≤ 2*u*y := (abs_add_le ..).trans
    (by linarith [mul_le_mul_of_nonneg_left y3 hu])
  have sqsum := pow_le_pow_left₀ (abs_nonneg _) sum 2
  have fourth := pow_le_pow_left₀ (abs_nonneg _) sum 4
  rw [sq_abs] at sqsum
  rw [show |b+d|^4=(b+d)^4 by exact (by decide : Even 4).pow_abs _] at fourth
  have csq := pow_le_pow_left₀ hc hc' 2
  have cs := mul_le_mul hc' sqsum (sq_nonneg _) (by positivity)
  have scale := mul_le_mul_of_nonneg_left fourth (show 0 ≤ Real.exp 1+3 by positivity)
  have bd := mul_le_mul hb hd (abs_nonneg _) (mul_nonneg hu hy)
  rw [← abs_mul] at bd
  have dsq := pow_le_pow_left₀ (abs_nonneg d) hd 2
  rw [sq_abs] at dsq
  nlinarith [mul_le_mul_of_nonneg_right y2 (show 0 ≤ u^2*y^4 by positivity)]

private theorem poisson_moment_bound {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (k : ℕ) (H : ℝ) (hr : ∀ p ∈ J, 0 ≤ r p) (hband : ∀ p ∈ J, |ell p| ≤ H) :
    |poissonMoment J r ell (2+k)| ≤ poissonMoment J r ell 2 * H^k := by
  unfold poissonMoment
  rw [Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [pow_add, ← mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg (hr p hp) (sq_nonneg _)), abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hband p hp) k)
    (mul_nonneg (hr p hp) (sq_nonneg _))

private theorem poisson_exponent_real {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (t : ℝ)
    (hr : ∀ p ∈ J, 0 ≤ r p) (hphase : ∀ p ∈ J, |t*ell p| ≤ 1) :
    (poissonExponent J r ell t).re ≤ -(poissonMoment J r ell 2*t^2)/3 := by
  unfold poissonExponent poissonMoment
  simp only [Complex.re_sum, Complex.re_ofReal_mul,Complex.sub_re,Complex.I_mul_re,
    Complex.ofReal_im, neg_zero, sub_zero, Complex.one_re, phase, Complex.exp_re,
    Complex.I_mul_im, Complex.ofReal_re, Real.exp_zero, one_mul,Finset.sum_mul,
    ← Finset.sum_neg_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  nlinarith [mul_le_mul_of_nonneg_left (one_sub_cos_lower _ (hphase p hp)) (hr p hp)]

private theorem central_poisson_parameters {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (t H : ℝ) (hH : 0 ≤ H) (hr : ∀ p ∈ J, 0 ≤ r p)
    (hband : ∀ p ∈ J, |ell p| ≤ H) (hsmall : H*|t| ≤ 1) :
    let M := poissonMoment J r ell
    let u := M 2*t^2
    let y := H*|t|
    let b := -(M 3)*t^3/6
    let c := M 4*t^4/24
    let d := M 5*t^5/120
    let z := poissonExponent J r ell t
    0 ≤ u ∧ 0 ≤ y ∧ |b| ≤ u*y ∧ 0 ≤ c ∧ c ≤ u*y^2 ∧ |d| ≤ u*y^3 ∧
      -u/2+c ≤ -u/3 ∧ z.re ≤ -u/3 ∧
      ‖z-((-u/2+c : ℝ)+(b+d : ℝ)*Complex.I)‖ ≤ Real.exp 1*u*y^4 := by
  let M := poissonMoment J r ell
  let u := M 2*t^2
  let y := H*|t|
  let b := -(M 3)*t^3/6
  let c := M 4*t^4/24
  let d := M 5*t^5/120
  let z := poissonExponent J r ell t
  have mpos (j : ℕ) : 0 ≤ M (2*j) := Finset.sum_nonneg
    (fun p hp => mul_nonneg (hr p hp) ((by exact even_two_mul j : Even (2*j)).pow_nonneg _))
  have m2 : 0 ≤ M 2 := mpos 1
  have m4 : 0 ≤ M 4 := mpos 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have phasele (p : ι) (hp : p ∈ J) : |t*ell p| ≤ 1 := by
    rw [abs_mul,mul_comm]
    exact (mul_le_mul_of_nonneg_right (hband p hp) (abs_nonneg _)).trans hsmall
  have b3 : |M 3| ≤ M 2*H := by simpa using poisson_moment_bound J r ell 1 H hr hband
  have b4 : M 4 ≤ M 2*H^2 := (le_abs_self _).trans (poisson_moment_bound J r ell 2 H hr hband)
  have b5 : |M 5| ≤ M 2*H^3 := poisson_moment_bound J r ell 3 H hr hband
  have hb : |b| ≤ u*y := by
    dsimp [b,u,y]
    rw [abs_div,abs_mul,abs_neg,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<6)]
    have bound := mul_le_mul_of_nonneg_right b3 (show 0 ≤ |t|^3 by positivity)
    have ts : |t|^3 = t^2*|t| := by rw [pow_succ,sq_abs]
    rw [ts] at bound ⊢
    nlinarith [mul_nonneg (mul_nonneg m2 hH) (mul_nonneg (sq_nonneg t) (abs_nonneg t))]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcstrong : c ≤ u*y^2/24 := by
    dsimp [c,u,y]
    rw [mul_pow, sq_abs]
    nlinarith [mul_le_mul_of_nonneg_right b4 (show 0 ≤ t^4 by positivity)]
  have hc' : c ≤ u*y^2 := by linarith [mul_nonneg hu (sq_nonneg y)]
  have hd : |d| ≤ u*y^3 := by
    dsimp [d,u,y]
    rw [abs_div,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<120),mul_pow]
    have bound := mul_le_mul_of_nonneg_right b5 (show 0 ≤ |t|^5 by positivity)
    have ts : |t|^5 = t^2*|t|^3 := by rw [show (5:ℕ)=2+3 by decide,pow_add,sq_abs]
    rw [ts] at bound ⊢
    nlinarith [mul_nonneg (mul_nonneg m2 (show 0 ≤ H^3 by positivity)) (mul_nonneg (sq_nonneg t) (show 0 ≤ |t|^3 by positivity))]
  have la : -u/2+c ≤ -u/3 := by
    have y2 := pow_le_pow_left₀ hy hsmall 2
    simp only [one_pow] at y2
    nlinarith [mul_le_mul_of_nonneg_left y2 hu]
  have expo := poisson_exponent_expansion J r ell t H hr hband phasele
  have E : ‖z-((-u/2+c : ℝ)+(b+d : ℝ)*Complex.I)‖ ≤ Real.exp 1*u*y^4 := by
    convert! expo using 1
    · dsimp [b,c,d,u,z,M]
      push_cast
      congr 2
      ring
    · dsimp [u,y,M]
      have ts : |t|^6 = t^2*|t|^4 := by rw [show (6:ℕ)=2+4 by decide,pow_add,sq_abs]
      rw [ts]; ring
  exact ⟨hu,hy,hb,hc,hc',hd,la,poisson_exponent_real J r ell t hr phasele,E⟩

/-- Pointwise first Edgeworth expansion of the actual centered prime product.
    Setting u=Vt² and y=H|t| keeps the remainder integrable with relative
    size H⁴/V². The separate squared-probability term is the finite-band
    Bernoulli-to-Poisson replacement error. -/
theorem saddle_edgeworth_pointwise {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (t H : ℝ) (hH : 0 ≤ H) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2)
    (hband : ∀ p ∈ J, |ell p| ≤ H) (hsmall : H*|t| ≤ 1) :
    let M := poissonMoment J r ell
    let u := M 2 * t^2
    let y := H*|t|
    |(saddleCharacteristic J r ell t).re - Real.exp (-u/2)*
      (1+(M 4*t^4/24)-(M 3)^2*t^6/72)| ≤
      4*(∑ p ∈ J, (r p)^2) + Real.exp (-u/3)*
      (y^4*(Real.exp 1*u+3*u^2+2*u^3+16*(Real.exp 1+3)*u^4)) := by
  let M := poissonMoment J r ell
  let u := M 2*t^2
  let y := H*|t|
  let b := -(M 3)*t^3/6
  let c := M 4*t^4/24
  let d := M 5*t^5/120
  let z := poissonExponent J r ell t
  obtain ⟨hu,hy,hb,hc,hc',hd,la,hz,E⟩ := central_poisson_parameters J r ell t H hH hr hband hsmall
  have point := real_edgeworth_error z (-u/3) (-u/2) b c d (Real.exp 1*u*y^4)
    hc hz la E
  have polynomial := edgeworth_polynomial_bound u y b c d hu hy hsmall hb hc hc' hd
  have approx := saddle_poisson_approximation J r ell t hr hr'
  have realError := (Complex.abs_re_le_norm (saddleCharacteristic J r ell t - Complex.exp z)).trans approx
  rw [Complex.sub_re] at realError
  have reduce : b^2/2 = (M 3)^2*t^6/72 := by dsimp [b]; ring
  rw [reduce] at point
  exact (abs_sub_le _ (Complex.exp z).re _).trans
    (add_le_add realError (point.trans (mul_le_mul_of_nonneg_left polynomial (Real.exp_pos _).le)))

private def momentConstant : ℕ → ℝ
  | 0 => 1
  | k+1 => 3*(2*(k:ℝ)+1)/2 * momentConstant k

private theorem gaussianMoment_scaled (V : ℝ) (hV : 0 < V) (k : ℕ) :
    gaussianMoment (V/3) k = momentConstant k/V^k*Real.sqrt (3*Real.pi/V) := by
  induction k with
  | zero =>
    simp only [gaussianMoment, Nat.mul_zero, pow_zero, one_mul, integral_gaussian,
      momentConstant,div_one]
    congr 1; ring
  | succ k ih =>
    have m := gaussianMoment_succ (2*V/3) (by positivity) k
    rw [show 2*V/3/2=V/3 by ring, ih] at m
    rw [m,momentConstant,pow_succ]
    field_simp

private def envelopeTerm (V H : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(V*t^2)/3)*(H*|t|)^4*(V*t^2)^k

private theorem envelopeTerm_eq (V H : ℝ) (k : ℕ) (t : ℝ) :
    envelopeTerm V H k t = (H^4*V^k)*(t^(2*(k+2))*Real.exp (-(V/3)*t^2)) := by
  simp only [envelopeTerm,mul_pow,show |t|^4=t^4 by exact (by decide : Even 4).pow_abs _,
    ← pow_mul, Nat.mul_add, pow_add]
  rw [show -(V*t^2)/3 = -(V/3)*t^2 by ring]
  ring

private theorem envelopeTerm_integrable (V H : ℝ) (hV : 0 < V) (k : ℕ) :
    Integrable (envelopeTerm V H k) := by
  simp_rw [show envelopeTerm V H k = fun t => (H^4*V^k)*(t^(2*(k+2))*Real.exp (-(V/3)*t^2)) by
    funext t; exact envelopeTerm_eq V H k t]
  apply Integrable.const_mul
  convert! integrable_rpow_mul_exp_neg_mul_sq (b := V/3) (s := ((2*(k+2):ℕ):ℝ))
    (by positivity) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)) using 1
  simp only [Real.rpow_natCast]

private theorem envelopeTerm_integral (V H : ℝ) (hV : 0 < V) (k : ℕ) :
    (∫ t : ℝ, envelopeTerm V H k t) = momentConstant (k+2)*
        (H^4/V^2*Real.sqrt (3*Real.pi/V)) := by
  simp_rw [envelopeTerm_eq]
  rw [integral_const_mul]
  change _*gaussianMoment (V/3) (k+2) = _
  rw [gaussianMoment_scaled V hV, pow_add]
  field_simp

private def envelopeCoefficient : ℕ → ℝ
  | 0 => 1
  | 1 => Real.exp 1+1
  | 2 => 4
  | 3 => 2
  | _ => 16*(Real.exp 1+3)

private def saddleEnvelope (V H t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 5, envelopeCoefficient k*envelopeTerm V H k t

/-- Absolute constant in the integrated first Edgeworth remainder. -/
def saddleEdgeworthConstant : ℝ :=
  ∑ k ∈ Finset.range 5, envelopeCoefficient k*momentConstant (k+2)

private theorem saddleEnvelope_eq (V H t : ℝ) :
    let u := V*t^2
    let y := H*|t|
    saddleEnvelope V H t = Real.exp (-u/3)*(y^4*
      (1+(Real.exp 1+1)*u+4*u^2+2*u^3+16*(Real.exp 1+3)*u^4)) := by
  simp only [saddleEnvelope,envelopeTerm,Finset.sum_range_succ,Finset.sum_range_zero,
    envelopeCoefficient]
  ring

private theorem saddleEnvelope_integrable (V H : ℝ) (hV : 0 < V) :
    Integrable (saddleEnvelope V H) := by
  apply integrable_finsetSum
  exact fun k _ => (envelopeTerm_integrable V H hV k).const_mul _

private theorem saddleEnvelope_integral (V H : ℝ) (hV : 0 < V) :
    (∫ t : ℝ, saddleEnvelope V H t) =
      saddleEdgeworthConstant*(H^4/V^2*Real.sqrt (3*Real.pi/V)) := by
  unfold saddleEnvelope
  rw [integral_finsetSum _ (fun k _ => (envelopeTerm_integrable V H hV k).const_mul _)]
  simp_rw [integral_const_mul,envelopeTerm_integral V H hV, ← mul_assoc]
  rw [← Finset.sum_mul,saddleEdgeworthConstant]
  rw [← Finset.sum_mul]

private def edgeworthModel (V K₃ K₄ t : ℝ) : ℝ :=
  Real.exp (-(V/2)*t^2)*(1+K₄*t^4/24-K₃^2*t^6/72)

private theorem edgeworthModel_integrable (V K₃ K₄ : ℝ) (hV : 0 < V) :
    Integrable (edgeworthModel V K₃ K₄) := by
  let G (x : ℝ) := Real.exp (-(V/2)*x^2)
  have ig (k : ℕ) : Integrable (fun x : ℝ => x^k*G x) := by
    simpa [G] using integrable_rpow_mul_exp_neg_mul_sq (b := V/2) (s := (k:ℝ))
      (by positivity) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  have i0 : Integrable G := by simpa using ig 0
  have e : edgeworthModel V K₃ K₄ = fun x =>
      (G x+(K₄/24)*(x^4*G x))-(K₃^2/72)*(x^6*G x) := by
    funext x; unfold edgeworthModel G; ring
  rw [e]
  exact (i0.add ((ig 4).const_mul _)).sub ((ig 6).const_mul _)

private theorem edgeworthModel_tail (V H K₃ K₄ t : ℝ) (hV : 0 ≤ V) (_hH : 0 ≤ H)
    (h₃ : |K₃| ≤ V*H) (h₄ : |K₄| ≤ V*H^2) (hout : 1 ≤ H*|t|) :
    |edgeworthModel V K₃ K₄ t| ≤ saddleEnvelope V H t := by
  let u := V*t^2
  let y := H*|t|
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have yy : 1 ≤ y := hout
  have y2 := pow_le_pow_left₀ zero_le_one yy 2
  have y4 := pow_le_pow_left₀ zero_le_one yy 4
  simp only [one_pow] at y2 y4
  have y24 : y^2 ≤ y^4 := by nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr y2)]
  have q4 : |K₄*t^4/24| ≤ u*y^2 := by
    dsimp [u,y]
    rw [abs_div,abs_mul,abs_of_nonneg (show 0 ≤ t^4 by positivity),
      abs_of_pos (by norm_num : (0:ℝ)<24),mul_pow,sq_abs]
    nlinarith [mul_le_mul_of_nonneg_right h₄ (show 0 ≤ t^4 by positivity),
      mul_nonneg (mul_nonneg hV (sq_nonneg H)) (show 0 ≤ t^4 by positivity)]
  have q3 : K₃^2*t^6/72 ≤ u^2*y^2 := by
    have sq := pow_le_pow_left₀ (abs_nonneg K₃) h₃ 2
    rw [sq_abs] at sq
    dsimp [u,y]
    rw [mul_pow,mul_pow,sq_abs]
    nlinarith [mul_le_mul_of_nonneg_right sq (show 0 ≤ t^6 by positivity),
      mul_nonneg (sq_nonneg (V*H)) (show 0 ≤ t^6 by positivity)]
  have polynomial : |1+K₄*t^4/24-K₃^2*t^6/72| ≤ y^4*(1+u+u^2) := by
    apply (abs_sub ..).trans
    rw [abs_of_nonneg (show 0 ≤ K₃^2*t^6/72 by positivity)]
    have s := abs_add_le (1:ℝ) (K₄*t^4/24)
    rw [abs_one] at s
    nlinarith [mul_le_mul_of_nonneg_left y24 hu, mul_le_mul_of_nonneg_left y24 (sq_nonneg u)]
  rw [edgeworthModel,abs_mul,abs_of_pos (Real.exp_pos _),saddleEnvelope_eq]
  change _ ≤ Real.exp (-u/3)*(y^4*(1+(Real.exp 1+1)*u+4*u^2+2*u^3+16*(Real.exp 1+3)*u^4))
  have ex : Real.exp (-(V/2)*t^2) ≤ Real.exp (-u/3) := Real.exp_le_exp.mpr
    (by dsimp [u] at *; linarith only [hu])
  apply (mul_le_mul ex polynomial (abs_nonneg _) (Real.exp_pos _).le).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_nonneg (Real.exp_pos 1).le hu, sq_nonneg u,
    show 0 ≤ u^3 by positivity, show 0 ≤ (Real.exp 1+3)*u^4 by positivity]

/-- First Edgeworth expansion for the actual central Euler integral. The
    variance and cumulants in the main term are the Poisson prime moments.
    The explicit squared-probability term accounts for the distinction
    between Bernoulli and Poisson primes on the original squarefree support. -/
theorem saddle_integral_edgeworth {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (H : ℝ)
    (hH : 0 < H) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2)
    (hband : ∀ p ∈ J, |ell p| ≤ H) (hV : 0 < poissonMoment J r ell 2) :
    let M := poissonMoment J r ell
    let V := M 2
    |(∫ t : ℝ in -(1/H)..1/H, (saddleCharacteristic J r ell t).re) -
      Real.sqrt (2*Real.pi/V)*(1+M 4/(8*V^2)-5*(M 3)^2/(24*V^3))| ≤
      (8/H)*(∑ p ∈ J, (r p)^2) + saddleEdgeworthConstant*(H^4/V^2*Real.sqrt (3*Real.pi/V)) := by
  let M := poissonMoment J r ell
  let V := M 2
  let I := Set.Ioc (-(1/H)) (1/H)
  let f (t : ℝ) := (saddleCharacteristic J r ell t).re
  let G := edgeworthModel V (M 3) (M 4)
  let A := 4*(∑ p ∈ J, (r p)^2)
  have vpos : 0 < V := hV
  have ip : 0 < 1/H := by positivity
  have lr : -(1/H) ≤ 1/H := by linarith
  have measurable : MeasurableSet I := measurableSet_Ioc
  have fcont : Continuous f := by unfold f saddleCharacteristic centeredFactor phase; fun_prop
  have iF : Integrable (I.indicator f) := (integrable_indicator_iff measurable).mpr fcont.integrableOn_Ioc
  have iG : Integrable G := edgeworthModel_integrable _ _ _ vpos
  have iA : Integrable (I.indicator (fun _ => A)) :=
    (integrable_indicator_iff measurable).mpr continuous_const.integrableOn_Ioc
  have env := saddleEnvelope_integrable V H vpos
  have bound (t : ℝ) : ‖I.indicator f t-G t‖ ≤ I.indicator (fun _ => A) t+saddleEnvelope V H t := by
    rw [Real.norm_eq_abs]
    by_cases h : t ∈ I
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      have hsmall : H*|t| ≤ 1 := by
        rw [mul_comm, ← le_div_iff₀ hH, abs_le]
        exact ⟨h.1.le,h.2⟩
      have p := saddle_edgeworth_pointwise J r ell t H hH.le hr hr' hband hsmall
      let u := V*t^2
      let y := H*|t|
      have hu : 0 ≤ u := by dsimp [u]; positivity
      have inside : |f t-G t| ≤ A+Real.exp (-u/3)*(y^4*
          (Real.exp 1*u+3*u^2+2*u^3+16*(Real.exp 1+3)*u^4)) := by
        simpa only [f,G,edgeworthModel,show -(V/2)*t^2 = -u/2 by dsimp [u]; ring] using p
      apply inside.trans
      rw [saddleEnvelope_eq]
      change _ ≤ A+Real.exp (-u/3)*(y^4*_)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change Real.exp 1*u+3*u^2+2*u^3+16*(Real.exp 1+3)*u^4 ≤
        1+(Real.exp 1+1)*u+4*u^2+2*u^3+16*(Real.exp 1+3)*u^4
      nlinarith [sq_nonneg u]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_sub, abs_neg, zero_add]
      have hout : 1 ≤ H*|t| := by
        rw [mul_comm, ← div_le_iff₀ hH]
        by_contra! ha
        exact h (show t ∈ I from ⟨(abs_lt.mp ha).1,(abs_lt.mp ha).2.le⟩)
      apply edgeworthModel_tail V H _ _ t vpos.le hH.le _ _ hout
      · simpa only [pow_one] using poisson_moment_bound J r ell 1 H hr hband
      · exact poisson_moment_bound J r ell 2 H hr hband
  have total := norm_integral_le_of_norm_le (iA.add env) (Filter.Eventually.of_forall bound)
  change ‖∫ t, I.indicator f t-G t‖ ≤ ∫ t, I.indicator (fun _ => A) t+saddleEnvelope V H t at total
  rw [integral_sub iF iG, integral_add iA env, integral_indicator measurable,
    integral_indicator measurable, ← intervalIntegral.integral_of_le lr, ← intervalIntegral.integral_of_le lr,
    intervalIntegral.integral_const,saddleEnvelope_integral V H vpos,Real.norm_eq_abs] at total
  change _ ≤ _ + _ at total
  have main : (∫ t : ℝ, G t) = _ := saddle_edgeworth_integral V (M 3) (M 4) vpos
  rw [main] at total
  apply total.trans_eq
  simp only [smul_eq_mul,A]
  ring

private def shiftScale : ℝ := 1000*(Real.exp 1+3)

private def shiftedModel (V K₃ K₄ a t : ℝ) : ℝ :=
  Real.exp (-(V/2)*t^2) *
    (1+K₄*t^4/24-K₃^2*t^6/72+K₃*a*t^4/6-a^2*t^2/2)

/-- Shifting the target logarithm by up to two prime logarithms gives the
    same integrated order of error. This pointwise estimate includes the
    mixed term between the skewness and the frequency displacement. -/
private theorem shifted_saddle_pointwise {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (a t H : ℝ) (hH : 0 ≤ H) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2)
    (hband : ∀ p ∈ J, |ell p| ≤ H) (hsmall : H*|t| ≤ 1) (ha : |a| ≤ 2*H) :
    let M := poissonMoment J r ell
    |(phase (a*t)*saddleCharacteristic J r ell t).re - shiftedModel (M 2) (M 3) (M 4) a t| ≤
      4*(∑ p ∈ J, (r p)^2) + shiftScale*saddleEnvelope (M 2) H t := by
  let M := poissonMoment J r ell
  let u := M 2*t^2
  let y := H*|t|
  let b := -(M 3)*t^3/6
  let c := M 4*t^4/24
  let d := M 5*t^5/120
  let z := poissonExponent J r ell t
  obtain ⟨hu,hy,hb,hc,hc',hd,la,hz,E⟩ := central_poisson_parameters J r ell t H hH hr hband hsmall
  change 0 ≤ u at hu
  change 0 ≤ y at hy
  change |b| ≤ u*y at hb
  change 0 ≤ c at hc
  change c ≤ u*y^2 at hc'
  change |d| ≤ u*y^3 at hd
  let U := u+2
  have hU : 0 ≤ U := by dsimp [U]; linarith
  have hb' : |b+a*t| ≤ U*y := by
    apply (abs_add_le ..).trans
    rw [abs_mul]
    have s := mul_le_mul_of_nonneg_right ha (abs_nonneg t)
    change |b|+|a| * |t| ≤ (u+2)*y
    dsimp [y] at hb ⊢; linarith only [hb,s]
  have hcu : c ≤ U*y^2 := hc'.trans (by dsimp [U]; nlinarith [sq_nonneg y])
  have hdu : |d| ≤ U*y^3 := hd.trans (by dsimp [U]; nlinarith [show 0 ≤ y^3 by positivity])
  let z' := z + Complex.I*(a*t : ℝ)
  have zr : z'.re ≤ -u/3 := by simpa [z',z] using hz
  have rem : ‖z'-((-u/2+c : ℝ)+(b+a*t+d : ℝ)*Complex.I)‖ ≤ Real.exp 1*U*y^4 := by
    have id : z'-((-u/2+c : ℝ)+(b+a*t+d : ℝ)*Complex.I) =
        z-((-u/2+c : ℝ)+(b+d : ℝ)*Complex.I) := by dsimp [z']; push_cast; ring
    rw [id]
    apply E.trans
    change Real.exp 1*u*y^4 ≤ Real.exp 1*(u+2)*y^4
    gcongr; linarith
  have point := real_edgeworth_error z' (-u/3) (-u/2) (b+a*t) c d (Real.exp 1*U*y^4)
    hc zr la rem
  have poly := edgeworth_polynomial_bound U y (b+a*t) c d hU hy hsmall hb' hc hcu hdu
  have big : Real.exp (-u/3)*(y^4*(Real.exp 1*U+3*U^2+2*U^3+16*(Real.exp 1+3)*U^4))
      ≤ shiftScale*saddleEnvelope (M 2) H t := by
    rw [saddleEnvelope_eq]
    change _ ≤ shiftScale*(Real.exp (-u/3)*(y^4*(1+(Real.exp 1+1)*u+4*u^2+2*u^3+16*(Real.exp 1+3)*u^4)))
    rw [show shiftScale*(Real.exp (-u/3)*(y^4*(1+(Real.exp 1+1)*u+4*u^2+2*u^3+16*(Real.exp 1+3)*u^4))) =
      Real.exp (-u/3)*(y^4*(shiftScale*(1+(Real.exp 1+1)*u+4*u^2+2*u^3+16*(Real.exp 1+3)*u^4))) by ring]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sub_nonneg.mp
    dsimp [U,shiftScale]
    ring_nf
    positivity
  have approx := saddle_poisson_approximation J r ell t hr hr'
  have err : |(phase (a*t)*saddleCharacteristic J r ell t).re-(Complex.exp z').re| ≤
      4*(∑ p ∈ J, (r p)^2) := by
    have expz : Complex.exp z' = phase (a*t)*Complex.exp z := by
      rw [show z'=Complex.I*(a*t : ℝ)+z by dsimp [z']; ring, Complex.exp_add]
      rfl
    rw [expz,← Complex.sub_re]
    apply (Complex.abs_re_le_norm _).trans
    rw [← mul_sub,norm_mul,norm_phase,one_mul]
    exact approx
  have model : Real.exp (-u/2)*(1+c-(b+a*t)^2/2) = shiftedModel (M 2) (M 3) (M 4) a t := by
    dsimp [u,b,c,shiftedModel]
    rw [show -(M 2*t^2)/2=-(M 2/2)*t^2 by ring]
    ring
  rw [model] at point
  exact (abs_sub_le _ (Complex.exp z').re _).trans
    (add_le_add err (point.trans ((mul_le_mul_of_nonneg_left poly (Real.exp_pos _).le).trans big)))

private theorem shiftedModel_split (V K₃ K₄ a t : ℝ) :
    shiftedModel V K₃ K₄ a t = edgeworthModel V K₃ K₄ t +
      (K₃*a/6)*(t^4*Real.exp (-(V/2)*t^2)) - (a^2/2)*(t^2*Real.exp (-(V/2)*t^2)) := by
  dsimp [shiftedModel,edgeworthModel]; ring

private theorem shiftedModel_integral (V K₃ K₄ a : ℝ) (hV : 0 < V) :
    Integrable (shiftedModel V K₃ K₄ a) ∧ (∫ t : ℝ, shiftedModel V K₃ K₄ a t) =
      Real.sqrt (2*Real.pi/V)*(1+K₄/(8*V^2)-5*K₃^2/(24*V^3)+K₃*a/(2*V^2)-a^2/(2*V)) := by
  let G (t : ℝ) := Real.exp (-(V/2)*t^2)
  have ig (k : ℕ) : Integrable (fun x : ℝ => x^k*G x) := by
    simpa [G] using integrable_rpow_mul_exp_neg_mul_sq (b := V/2) (s := (k:ℝ))
      (by positivity) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  have base := edgeworthModel_integrable V K₃ K₄ hV
  have i4 := (ig 4).const_mul (K₃*a/6)
  have i2 := (ig 2).const_mul (a^2/2)
  have e : shiftedModel V K₃ K₄ a = fun t =>
      edgeworthModel V K₃ K₄ t + (K₃*a/6)*(t^4*G t) - (a^2/2)*(t^2*G t) :=
    funext (shiftedModel_split V K₃ K₄ a)
  rw [e]
  refine ⟨(base.add i4).sub i2, ?_⟩
  have ib : Integrable (fun t => edgeworthModel V K₃ K₄ t+(K₃*a/6)*(t^4*G t)) := base.add i4
  rw [integral_sub ib i2,integral_add base i4,integral_const_mul,integral_const_mul]
  have m0 : gaussianMoment (V/2) 0 = Real.sqrt (2*Real.pi/V) := by
    simp only [gaussianMoment,Nat.mul_zero,pow_zero,one_mul,integral_gaussian]; congr 1; ring
  have m1 := gaussianMoment_succ V hV 0
  have m2 := gaussianMoment_succ V hV 1
  norm_num at m1 m2
  rw [m0] at m1
  rw [m1] at m2
  change (∫ t : ℝ, edgeworthModel V K₃ K₄ t)+_*gaussianMoment (V/2) 2-_*gaussianMoment (V/2) 1 = _
  rw [m1,m2,show (∫ t : ℝ, edgeworthModel V K₃ K₄ t) = _ from saddle_edgeworth_integral V K₃ K₄ hV]
  field_simp
  ring

private theorem shiftedModel_tail (V H K₃ K₄ a t : ℝ) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (h₃ : |K₃| ≤ V*H) (h₄ : |K₄| ≤ V*H^2) (ha : |a| ≤ 2*H) (hout : 1 ≤ H*|t|) :
    |shiftedModel V K₃ K₄ a t| ≤ shiftScale*saddleEnvelope V H t := by
  let u := V*t^2
  let y := H*|t|
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have yy : 1 ≤ y := hout
  have y2 := pow_le_pow_left₀ zero_le_one yy 2
  simp only [one_pow] at y2
  have y24 : y^2 ≤ y^4 := by nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr y2)]
  have lin : |K₃*a*t^4/6| ≤ u*y^4 := by
    have prod := mul_le_mul h₃ ha (abs_nonneg _) (mul_nonneg hV hH)
    rw [abs_div,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<6),
      abs_of_nonneg (show 0 ≤ t^4 by positivity)]
    apply (show |K₃| * |a| * t^4/6 ≤ u*y^2 by
      dsimp [u,y]; rw [mul_pow,sq_abs]
      nlinarith [mul_le_mul_of_nonneg_right prod (show 0 ≤ t^4 by positivity),
        mul_nonneg (mul_nonneg hV (sq_nonneg H)) (show 0 ≤ t^4 by positivity)]).trans
    exact mul_le_mul_of_nonneg_left y24 hu
  have quad : a^2*t^2/2 ≤ 2*y^4 := by
    have sq := pow_le_pow_left₀ (abs_nonneg _) ha 2
    rw [sq_abs] at sq
    have w : a^2*t^2/2 ≤ 2*y^2 := by
      dsimp [y]; rw [mul_pow,sq_abs]; nlinarith [mul_le_mul_of_nonneg_right sq (sq_nonneg t)]
    linarith
  have model : shiftedModel V K₃ K₄ a t =
      edgeworthModel V K₃ K₄ t+Real.exp (-u/2)*(K₃*a*t^4/6-a^2*t^2/2) := by
    dsimp [shiftedModel,edgeworthModel,u]
    rw [show -(V*t^2)/2=-(V/2)*t^2 by ring]; ring
  rw [model]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  have b : |K₃*a*t^4/6-a^2*t^2/2| ≤ y^4*(u+2) := by
    apply (abs_sub ..).trans
    rw [abs_of_nonneg (show 0 ≤ a^2*t^2/2 by positivity)]
    linarith only [lin,quad]
  have ex : Real.exp (-u/2) ≤ Real.exp (-u/3) := Real.exp_le_exp.mpr (by linarith)
  apply (add_le_add (edgeworthModel_tail V H _ _ t hV hH h₃ h₄ hout)
    (mul_le_mul ex b (abs_nonneg _) (Real.exp_pos _).le)).trans
  rw [saddleEnvelope_eq]
  let P := 1+(Real.exp 1+1)*u+4*u^2+2*u^3+16*(Real.exp 1+3)*u^4
  change Real.exp (-u/3)*(y^4*P)+Real.exp (-u/3)*(y^4*(u+2)) ≤ shiftScale*(Real.exp (-u/3)*(y^4*P))
  rw [show Real.exp (-u/3)*(y^4*P)+Real.exp (-u/3)*(y^4*(u+2)) = (Real.exp (-u/3)*y^4)*(P+(u+2)) by ring,
    show shiftScale*(Real.exp (-u/3)*(y^4*P))=(Real.exp (-u/3)*y^4)*(shiftScale*P) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sub_nonneg.mp
  dsimp [P,shiftScale]
  ring_nf
  positivity

/-- The central integral after changing the logarithmic center by a. -/
def shiftedMass {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (H a : ℝ) : ℝ :=
  ∫ t : ℝ in -(1/H)..1/H, (phase (a*t)*saddleCharacteristic J r ell t).re

/-- At a common saddle, all centers displaced by at most two maximal prime
    logarithms have a uniform expansion. The stated Gaussian coefficient
    is quadratic in the displacement, including the skewness correction. -/
theorem shifted_saddle_integral {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (a H : ℝ)
    (hH : 0 < H) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2)
    (hband : ∀ p ∈ J, |ell p| ≤ H) (hV : 0 < poissonMoment J r ell 2) (ha : |a| ≤ 2*H) :
    let M := poissonMoment J r ell
    let V := M 2
    |shiftedMass J r ell H a - Real.sqrt (2*Real.pi/V)*
      (1+M 4/(8*V^2)-5*(M 3)^2/(24*V^3)+(M 3)*a/(2*V^2)-a^2/(2*V))| ≤
      (8/H)*(∑ p ∈ J, (r p)^2) + (1000*(Real.exp 1+3)*saddleEdgeworthConstant)*
      (H^4/V^2*Real.sqrt (3*Real.pi/V)) := by
  let M := poissonMoment J r ell
  let V := M 2
  let I := Set.Ioc (-(1/H)) (1/H)
  let f (t : ℝ) := (phase (a*t)*saddleCharacteristic J r ell t).re
  let G := shiftedModel V (M 3) (M 4) a
  let A := 4*(∑ p ∈ J, (r p)^2)
  have vpos : 0 < V := hV
  have ip : 0 < 1/H := by positivity
  have lr : -(1/H) ≤ 1/H := by linarith
  have measurable : MeasurableSet I := measurableSet_Ioc
  have fcont : Continuous f := by unfold f saddleCharacteristic centeredFactor phase; fun_prop
  have iF : Integrable (I.indicator f) := (integrable_indicator_iff measurable).mpr fcont.integrableOn_Ioc
  obtain ⟨iG,main⟩ := shiftedModel_integral V (M 3) (M 4) a vpos
  have iA : Integrable (I.indicator (fun _ => A)) :=
    (integrable_indicator_iff measurable).mpr continuous_const.integrableOn_Ioc
  have env := (saddleEnvelope_integrable V H vpos).const_mul shiftScale
  have bound (t : ℝ) : ‖I.indicator f t-G t‖ ≤ I.indicator (fun _ => A) t+shiftScale*saddleEnvelope V H t := by
    rw [Real.norm_eq_abs]
    by_cases h : t ∈ I
    · rw [Set.indicator_of_mem h,Set.indicator_of_mem h]
      apply shifted_saddle_pointwise J r ell a t H hH.le hr hr' hband _ ha
      rw [mul_comm, ← le_div_iff₀ hH, abs_le]
      exact ⟨h.1.le,h.2⟩
    · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,zero_sub,abs_neg,zero_add]
      have hout : 1 ≤ H*|t| := by
        rw [mul_comm, ← div_le_iff₀ hH]
        by_contra! hl
        exact h (show t ∈ I from ⟨(abs_lt.mp hl).1,(abs_lt.mp hl).2.le⟩)
      apply shiftedModel_tail V H _ _ a t vpos.le hH.le _ _ ha hout
      · simpa only [pow_one] using poisson_moment_bound J r ell 1 H hr hband
      · exact poisson_moment_bound J r ell 2 H hr hband
  have total := norm_integral_le_of_norm_le (iA.add env) (Filter.Eventually.of_forall bound)
  change ‖∫ t, I.indicator f t-G t‖ ≤ ∫ t, I.indicator (fun _ => A) t+shiftScale*saddleEnvelope V H t at total
  change Integrable G at iG
  change (∫ t, G t) = _ at main
  rw [integral_sub iF iG, integral_add iA env, integral_indicator measurable,
    integral_indicator measurable, ← intervalIntegral.integral_of_le lr, ← intervalIntegral.integral_of_le lr,
    intervalIntegral.integral_const,integral_const_mul,saddleEnvelope_integral V H vpos,Real.norm_eq_abs,main] at total
  apply total.trans_eq
  simp only [smul_eq_mul,A,shiftScale]
  ring

/-- Removing an Euler factor retains its share of the common centering phase. -/
def omittedCharacteristic {ι : Type*} [DecidableEq ι] (J D : Finset ι) (r ell : ι → ℝ) (t : ℝ) : ℂ :=
  ∏ p ∈ J, if p ∈ D then phase (-r p*(t*ell p)) else centeredFactor (r p) (t*ell p)

def omittedMass {ι : Type*} [DecidableEq ι] (J D : Finset ι) (r ell : ι → ℝ) (H a : ℝ) : ℝ :=
  ∫ t : ℝ in -(1/H)..1/H, (phase (a*t)*omittedCharacteristic J D r ell t).re

/-- Exact omitted squarefree Euler product with the shared logarithmic center. -/
theorem omitted_characteristic_euler (J D : Finset ℕ) (hJ : ∀ p ∈ J, 0 < p) (α t : ℝ) :
    omittedCharacteristic J D (primeProbability α) (fun p => Real.log p) t =
      Complex.exp (-Complex.I*(t*saddleMean J α)) *
        principalEuler (J\D) (α-t*Complex.I) / (∏ p ∈ J\D, (1+(((p:ℝ)^(-α) : ℝ) : ℂ))) := by
  let Q (p : ℕ) := (1+(p : ℂ)^(-((α : ℂ)-t*Complex.I)))/(1+(((p:ℝ)^(-α) : ℝ) : ℂ))
  have oneFactor (p : ℕ) (hp : p ∈ J) :
      (if p ∈ D then phase (-primeProbability α p*(t*Real.log p))
        else centeredFactor (primeProbability α p) (t*Real.log p)) =
      phase (-primeProbability α p*(t*Real.log p))*(if p ∈ D then 1 else Q p) := by
    split_ifs <;> simp only [mul_one,prime_centered_factor p (hJ p hp) α t,Q]
  have retained : (∏ p ∈ J, if p ∈ D then 1 else Q p) = ∏ p ∈ J\D, Q p := by
    rw [Finset.sdiff_eq_filter,Finset.prod_filter]; simp
  rw [omittedCharacteristic,Finset.prod_congr rfl oneFactor,Finset.prod_mul_distrib,
    retained,prime_center_phase]
  simp only [Q,Finset.prod_div_distrib,principalEuler]
  ring

private theorem omitted_product_error {ι : Type*} [DecidableEq ι]
    (J D : Finset ι) (r ell : ι → ℝ) (t : ℝ) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1) :
    ‖omittedCharacteristic J D r ell t-saddleCharacteristic J r ell t‖ ≤
      2*(∑ p ∈ J, if p ∈ D then r p else 0) := by
  induction J using Finset.induction_on with
  | empty => simp [omittedCharacteristic,saddleCharacteristic]
  | insert p J hp ih =>
    have h0 := hr p (Finset.mem_insert_self ..)
    have h1 := hr' p (Finset.mem_insert_self ..)
    let θ := t*ell p
    let A := if p ∈ D then phase (-r p*θ) else centeredFactor (r p) θ
    let B := centeredFactor (r p) θ
    let X := omittedCharacteristic J D r ell t
    let Y := saddleCharacteristic J r ell t
    have A1 : ‖A‖ ≤ 1 := by
      dsimp only [A]; split_ifs
      · exact (norm_phase _).le
      · exact norm_centeredFactor_le_one _ _ h0 h1
    have Y1 : ‖Y‖ ≤ 1 := by
      dsimp only [Y,saddleCharacteristic]
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun q hq => norm_centeredFactor_le_one _ _
        (hr q (Finset.mem_insert_of_mem hq)) (hr' q (Finset.mem_insert_of_mem hq)))
    have ab : ‖A-B‖ ≤ 2*(if p ∈ D then r p else 0) := by
      dsimp only [A,B]; split_ifs
      · rw [centeredFactor_eq,show phase (-r p*θ)-phase (-r p*θ)*(((1-r p : ℝ):ℂ)+(r p:ℂ)*phase θ) =
          phase (-r p*θ)*((r p:ℂ)*(1-phase θ)) by push_cast; ring,
          norm_mul,norm_phase,one_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]
        have x := norm_sub_le (1 : ℂ) (phase θ)
        rw [norm_one,norm_phase] at x
        linarith [mul_le_mul_of_nonneg_left x h0]
      · simp
    have tail := ih (fun q h => hr q (Finset.mem_insert_of_mem h)) (fun q h => hr' q (Finset.mem_insert_of_mem h))
    rw [omittedCharacteristic,Finset.prod_insert hp,saddleCharacteristic,Finset.prod_insert hp,Finset.sum_insert hp]
    change ‖A*X-B*Y‖ ≤ _
    rw [show A*X-B*Y=A*(X-Y)+(A-B)*Y by ring]
    apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul]
    have left := mul_le_mul_of_nonneg_right A1 (norm_nonneg (X-Y))
    have right := mul_le_mul_of_nonneg_left Y1 (norm_nonneg (A-B))
    change ‖X-Y‖ ≤ _ at tail
    linarith

/-- A different omitted set at each logarithmic shift has an explicit
    uniform cost in the corresponding common-saddle integral. -/
theorem omitted_mass_error {ι : Type*} [DecidableEq ι] (J D : Finset ι) (r ell : ι → ℝ)
    (H a : ℝ) (hH : 0 < H) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1) :
    |omittedMass J D r ell H a-shiftedMass J r ell H a| ≤
      (4/H)*(∑ p ∈ J, if p ∈ D then r p else 0) := by
  let f (t : ℝ) := (phase (a*t)*omittedCharacteristic J D r ell t).re
  let g (t : ℝ) := (phase (a*t)*saddleCharacteristic J r ell t).re
  have fcont : Continuous f := by
    have prod : Continuous (omittedCharacteristic J D r ell) := by
      unfold omittedCharacteristic
      apply continuous_finsetProd
      intro p _
      by_cases h : p ∈ D <;> simp [h,centeredFactor,phase] <;> fun_prop
    exact Complex.continuous_re.comp ((by unfold phase; fun_prop :
      Continuous (fun t : ℝ => phase (a*t))).mul prod)
  have gcont : Continuous g := by unfold g saddleCharacteristic centeredFactor phase; fun_prop
  have bound (t : ℝ) : ‖f t-g t‖ ≤ 2*(∑ p ∈ J, if p ∈ D then r p else 0) := by
    dsimp only [f,g]
    rw [Real.norm_eq_abs, ← Complex.sub_re]
    apply (Complex.abs_re_le_norm _).trans
    rw [← mul_sub,norm_mul,norm_phase,one_mul]
    exact omitted_product_error J D r ell t hr hr'
  change |(∫ t : ℝ in -(1/H)..1/H, f t) - (∫ t : ℝ in -(1/H)..1/H, g t)| ≤ _
  rw [← intervalIntegral.integral_sub (fcont.intervalIntegrable ..) (gcont.intervalIntegrable ..),← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => bound t)).trans_eq
  rw [abs_of_nonneg (by linarith [one_div_pos.mpr hH] : 0 ≤ 1/H- -(1/H))]
  ring

private def centerPolynomial (V K₃ K₄ a : ℝ) : ℝ :=
  1+K₄/(8*V^2)-5*K₃^2/(24*V^3)+K₃*a/(2*V^2)-a^2/(2*V)

private theorem centerPolynomial_near_one (V H K₃ K₄ a : ℝ) (hV : 0 < V) (hH : 0 ≤ H)
    (h₃ : |K₃| ≤ V*H) (h₄ : |K₄| ≤ V*H^2) (ha : |a| ≤ 2*H) :
    |centerPolynomial V K₃ K₄ a-1| ≤ 4*H^2/V := by
  have b4 := mul_le_mul_of_nonneg_right h₄ hV.le
  have s3 := pow_le_pow_left₀ (abs_nonneg _) h₃ 2
  rw [sq_abs] at s3
  have b3 := mul_le_mul h₃ ha (abs_nonneg _) (mul_nonneg hV.le hH)
  rw [← abs_mul] at b3
  have b3' := mul_le_mul_of_nonneg_right b3 hV.le
  have sa := pow_le_pow_left₀ (abs_nonneg _) ha 2
  rw [sq_abs] at sa
  have sa' := mul_le_mul_of_nonneg_right sa (sq_nonneg V)
  have p4 := mul_le_mul_of_nonneg_right (le_abs_self K₄) hV.le
  have n4 := mul_le_mul_of_nonneg_right (neg_le_abs K₄) hV.le
  have p3 := mul_le_mul_of_nonneg_right (le_abs_self (K₃*a)) hV.le
  have n3 := mul_le_mul_of_nonneg_right (neg_le_abs (K₃*a)) hV.le
  unfold centerPolynomial
  rw [abs_le]
  constructor <;> field_simp <;> nlinarith [sq_nonneg K₃, mul_nonneg (sq_nonneg a) (sq_nonneg V),
    mul_nonneg (sq_nonneg V) (sq_nonneg H)]

/-- Uniform absolute error after scaling the omitted central integrals by
    the leading Gaussian mass. D bounds the sum of deleted probabilities. -/
def insertionError {ι : Type*} (J : Finset ι) (r ell : ι → ℝ) (H D : ℝ) : ℝ :=
  let V := poissonMoment J r ell 2
  ((4/H)*D+(8/H)*(∑ p ∈ J, (r p)^2)+(1000*(Real.exp 1+3)*saddleEdgeworthConstant)*
    (H^4/V^2*Real.sqrt (3*Real.pi/V)))/Real.sqrt (2*Real.pi/V)

private theorem normalized_omitted_expansion {ι : Type*} [DecidableEq ι]
    (J D : Finset ι) (r ell : ι → ℝ) (H a d : ℝ)
    (hH : 0 < H) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2)
    (hband : ∀ p ∈ J, |ell p| ≤ H) (hV : 0 < poissonMoment J r ell 2) (ha : |a| ≤ 2*H)
    (hD : (∑ p ∈ J, if p ∈ D then r p else 0) ≤ d) :
    let M := poissonMoment J r ell
    let V := M 2
    |omittedMass J D r ell H a/Real.sqrt (2*Real.pi/V)-centerPolynomial V (M 3) (M 4) a| ≤
      insertionError J r ell H d := by
  let M := poissonMoment J r ell
  let V := M 2
  let scale := Real.sqrt (2*Real.pi/V)
  let P := centerPolynomial V (M 3) (M 4) a
  have sp : 0 < scale := Real.sqrt_pos.mpr (div_pos (by positivity) hV)
  have m := shifted_saddle_integral J r ell a H hH hr hr' hband hV ha
  have diff := omitted_mass_error J D r ell H a hH hr (fun p hp => (hr' p hp).trans (by norm_num))
  change |omittedMass J D r ell H a/scale-P| ≤ _
  rw [show omittedMass J D r ell H a/scale-P=(omittedMass J D r ell H a-scale*P)/scale by field_simp, abs_div,abs_of_pos sp]
  unfold insertionError
  apply div_le_div_of_nonneg_right _ sp.le
  apply (abs_sub_le _ (shiftedMass J r ell H a) _).trans
  change |shiftedMass J r ell H a-scale*P| ≤ _ at m
  have deleted := diff.trans (mul_le_mul_of_nonneg_left hD (by positivity))
  linarith only [m,deleted]

private theorem normalized_omitted_near_one {ι : Type*} [DecidableEq ι]
    (J D : Finset ι) (r ell : ι → ℝ) (H a d : ℝ)
    (hH : 0 < H) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2)
    (hband : ∀ p ∈ J, |ell p| ≤ H) (hV : 0 < poissonMoment J r ell 2) (ha : |a| ≤ 2*H)
    (hD : (∑ p ∈ J, if p ∈ D then r p else 0) ≤ d) :
    let V := poissonMoment J r ell 2
    |omittedMass J D r ell H a/Real.sqrt (2*Real.pi/V)-1| ≤ 4*(H^2/V)+insertionError J r ell H d := by
  let M := poissonMoment J r ell
  let V := M 2
  have m3 : |M 3| ≤ V*H := by simpa using poisson_moment_bound J r ell 1 H hr hband
  have m4 : |M 4| ≤ V*H^2 := poisson_moment_bound J r ell 2 H hr hband
  have near := centerPolynomial_near_one V H (M 3) (M 4) a hV hH.le m3 m4 ha
  have appr := normalized_omitted_expansion J D r ell H a d hH hr hr' hband hV ha hD
  apply (abs_sub_le _ (centerPolynomial V (M 3) (M 4) a) _).trans
  exact (add_le_add appr near).trans_eq (by ring)

/-- The positive base mass and the accompanying one-point insertion ratio. -/
theorem saddle_single_ratio {ι : Type*} [DecidableEq ι] (J D₀ D₁ : Finset ι)
    (r ell : ι → ℝ) (H a d : ℝ) (hH : 0 < H) (hr : ∀ p ∈ J, 0 ≤ r p)
    (hr' : ∀ p ∈ J, r p ≤ 1/2) (hband : ∀ p ∈ J, |ell p| ≤ H)
    (hV : 0 < poissonMoment J r ell 2) (ha : |a| ≤ 2*H)
    (h₀ : (∑ p ∈ J, if p ∈ D₀ then r p else 0) ≤ d)
    (h₁ : (∑ p ∈ J, if p ∈ D₁ then r p else 0) ≤ d)
    (hsmall : 4*(H^2/poissonMoment J r ell 2)+insertionError J r ell H d ≤ 1/2) :
    let V := poissonMoment J r ell 2
    let η := 4*(H^2/V)+insertionError J r ell H d
    let ratio := omittedMass J D₁ r ell H a/omittedMass J D₀ r ell H 0
    0 < omittedMass J D₀ r ell H 0 ∧ |ratio-1| ≤ 4*η ∧ |ratio| ≤ 3 := by
  let scale := Real.sqrt (2*Real.pi/poissonMoment J r ell 2)
  let A := omittedMass J D₁ r ell H a/scale
  let B := omittedMass J D₀ r ell H 0/scale
  let η := 4*(H^2/poissonMoment J r ell 2)+insertionError J r ell H d
  have sp : 0 < scale := Real.sqrt_pos.mpr (div_pos (by positivity) hV)
  have b0 : |B-1| ≤ η := normalized_omitted_near_one J D₀ r ell H 0 d hH hr hr' hband hV
    (by rw [abs_zero]; positivity) h₀
  have b1 : |A-1| ≤ η := normalized_omitted_near_one J D₁ r ell H a d hH hr hr' hband hV ha h₁
  change η ≤ 1/2 at hsmall
  have half : 1/2 ≤ B := by linarith [(abs_le.mp b0).1]
  have bp : 0 < B := by linarith
  have ep : 0 ≤ η := (abs_nonneg _).trans b0
  have id : A/B = omittedMass J D₁ r ell H a/omittedMass J D₀ r ell H 0 :=
    div_div_div_cancel_right₀ sp.ne' _ _
  dsimp only
  rw [← id]
  refine ⟨(div_pos_iff_of_pos_right sp).mp bp, ?_, ?_⟩
  · rw [show A/B-1=(A-B)/B by field_simp,abs_div,abs_of_pos bp,div_le_iff₀ bp]
    have b := abs_sub_le A 1 B
    rw [abs_sub_comm 1 B] at b
    change _ ≤ 4*η*B
    nlinarith [mul_le_mul_of_nonneg_left half ep]
  · rw [abs_div,abs_of_pos bp,div_le_iff₀ bp]
    have al := abs_le.mp b1
    exact abs_le.mpr ⟨by linarith [al.1], by linarith [al.2]⟩

private theorem quadratic_ratio_error (x₀ x₁ x₂ x₁₂ c ε η δ : ℝ)
    (h₀ : |x₀-1| ≤ η) (h₁ : |x₁-1| ≤ η) (h₂ : |x₂-1| ≤ η) (h₁₂ : |x₁₂-1| ≤ η)
    (hsmall : η ≤ 1/2) (hc : |c| ≤ δ) (hl : |x₁₂-x₁-x₂+x₀+c| ≤ 4*ε) :
    |x₁₂/x₀ - (x₁/x₀)*(x₂/x₀)*(1-c)| ≤ 4*(4*ε+2*η^2+δ*(2*η+η^2)) := by
  have hn : 0 ≤ η := (abs_nonneg _).trans h₀
  have half : 1/2 ≤ x₀ := by linarith [(abs_le.mp h₀).1]
  have pos : 0 < x₀ := by linarith
  have cross (x y : ℝ) (hx : |x-1| ≤ η) (hy : |y-1| ≤ η) :
      |(x-1)*(y-1)| ≤ η^2 := by rw [abs_mul,sq]; exact mul_le_mul hx hy (abs_nonneg _) hn
  have mixed := cross x₁₂ x₀ h₁₂ h₀
  have single := cross x₁ x₂ h₁ h₂
  have prod : |x₁*x₂-1| ≤ 2*η+η^2 := by
    rw [show x₁*x₂-1=(x₁-1)+(x₂-1)+(x₁-1)*(x₂-1) by ring]
    exact (abs_add_le ..).trans (by linarith [abs_add_le (x₁-1) (x₂-1)])
  have term := mul_le_mul hc prod (abs_nonneg _) ((abs_nonneg _).trans hc)
  rw [← abs_mul] at term
  let L := x₁₂-x₁-x₂+x₀+c
  let B := 4*ε+2*η^2+δ*(2*η+η^2)
  have num : |x₁₂*x₀-x₁*x₂*(1-c)| ≤ B := by
    rw [show x₁₂*x₀-x₁*x₂*(1-c) =
      ((L+(x₁₂-1)*(x₀-1))-(x₁-1)*(x₂-1))+c*(x₁*x₂-1) by dsimp [L]; ring]
    apply (abs_add_le ..).trans
    have first := abs_add_le L ((x₁₂-1)*(x₀-1))
    have second := abs_sub (L+(x₁₂-1)*(x₀-1)) ((x₁-1)*(x₂-1))
    change |L| ≤ 4*ε at hl
    dsimp [B]; linarith only [first,second,hl,mixed,single,term]
  have denom : 1 ≤ 4*x₀^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ x₀-1/2) (by linarith : 0 ≤ x₀+1/2)]
  have nonneg : 0 ≤ B := (abs_nonneg _).trans num
  rw [show x₁₂/x₀-(x₁/x₀)*(x₂/x₀)*(1-c)=(x₁₂*x₀-x₁*x₂*(1-c))/x₀^2 by field_simp,
    abs_div,abs_of_nonneg (sq_nonneg x₀), div_le_iff₀ (sq_pos_of_pos pos)]
  change _ ≤ 4*B*x₀^2
  nlinarith only [num,mul_le_mul_of_nonneg_left denom nonneg]

/-- Pair insertion covariance of the actual finite squarefree Euler saddle
    masses, allowing separate deletions at each center. The curvature is
    the negative product of the two logarithmic displacements divided by
    the prime variance. The finite error is second order whenever the
    normalized Edgeworth and deletion errors are second order. -/
theorem saddle_pair_covariance {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (D : ℝ → Finset ι) (r ell : ι → ℝ) (H h k d : ℝ)
    (hH : 0 < H) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2)
    (hband : ∀ p ∈ J, |ell p| ≤ H) (hV : 0 < poissonMoment J r ell 2) (hh : |h| ≤ H) (hk : |k| ≤ H)
    (hD : ∀ a : ℝ, |a| ≤ 2*H → (∑ p ∈ J, if p ∈ D a then r p else 0) ≤ d)
    (hsmall : 4*(H^2/poissonMoment J r ell 2)+insertionError J r ell H d ≤ 1/2) :
    let form := fun a : ℝ => omittedMass J (D a) r ell H a
    let V := poissonMoment J r ell 2
    let δ := H^2/V
    let ε := insertionError J r ell H d
    let η := 4*δ+ε
    |form (h+k)/form 0-(form h/form 0)*(form k/form 0)*(1-h*k/V)| ≤
      4*(4*ε+2*η^2+δ*(2*η+η^2)) := by
  let M := poissonMoment J r ell
  let V := M 2
  let scale := Real.sqrt (2*Real.pi/V)
  let form := fun a : ℝ => omittedMass J (D a) r ell H a
  let F := fun a : ℝ => form a/scale
  let P := centerPolynomial V (M 3) (M 4)
  let δ := H^2/V
  let ε := insertionError J r ell H d
  let η := 4*δ+ε
  have vpos : 0 < V := hV
  have sp : 0 < scale := Real.sqrt_pos.mpr (div_pos (by positivity) hV)
  have appr (a : ℝ) (ha : |a| ≤ 2*H) : |F a-P a| ≤ ε :=
    normalized_omitted_expansion J (D a) r ell H a d hH hr hr' hband hV ha (hD a ha)
  have close (a : ℝ) (ha : |a| ≤ 2*H) : |F a-1| ≤ η := by
    exact normalized_omitted_near_one J (D a) r ell H a d hH hr hr' hband hV ha (hD a ha)
  have z : |(0 : ℝ)| ≤ 2*H := by rw [abs_zero]; positivity
  have h1 : |h| ≤ 2*H := by linarith
  have h2 : |k| ≤ 2*H := by linarith
  have h12 : |h+k| ≤ 2*H := (abs_add_le h k).trans (by linarith)
  have curvature : |h*k/V| ≤ δ := by
    rw [abs_div,abs_mul,abs_of_pos vpos]
    exact div_le_div_of_nonneg_right ((mul_le_mul hh hk (abs_nonneg k) hH.le).trans_eq (by ring)) vpos.le
  have linear :
      |F (h+k)-F h-F k+F 0+h*k/V| ≤ 4*ε := by
    have id : F (h+k)-F h-F k+F 0+h*k/V =
        ((F (h+k)-P (h+k))-(F h-P h))-(F k-P k)+(F 0-P 0) := by
      dsimp [P,centerPolynomial]; ring
    rw [id]
    have a1 := abs_sub (F (h+k)-P (h+k)) (F h-P h)
    have a2 := abs_sub ((F (h+k)-P (h+k))-(F h-P h)) (F k-P k)
    apply (abs_add_le ..).trans
    linarith only [a1,a2,appr (h+k) h12,appr h h1,appr k h2,appr 0 z]
  have result := quadratic_ratio_error (F 0) (F h) (F k) (F (h+k)) (h*k/V) ε η δ
    (close 0 z) (close h h1) (close k h2) (close (h+k) h12) hsmall curvature linear
  simpa only [F,div_div_div_cancel_right₀ sp.ne'] using result

private theorem bernoulli_curvature_error {ι : Type*} (J : Finset ι) (r ell : ι → ℝ)
    (H h k m : ℝ) (hH : 0 ≤ H) (hm : 0 ≤ m) (hr : ∀ p ∈ J, 0 ≤ r p)
    (hr' : ∀ p ∈ J, r p ≤ 1/2) (hmax : ∀ p ∈ J, r p ≤ m)
    (hV : 0 < poissonMoment J r ell 2) (hh : |h| ≤ H) (hk : |k| ≤ H) :
    let V := poissonMoment J r ell 2
    let W := saddleVariance J r ell
    |h*k/W-h*k/V| ≤ 2*m*(H^2/V) := by
  let V := poissonMoment J r ell 2
  let W := saddleVariance J r ell
  have vp : 0 < V := hV
  have low : V/2 ≤ W := by
    unfold V W poissonMoment saddleVariance
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    nlinarith [mul_nonneg (mul_nonneg (hr p hp) (sq_nonneg (ell p)))
      (sub_nonneg.mpr (hr' p hp))]
  have diff : V-W = ∑ p ∈ J, (r p)^2*(ell p)^2 := by
    unfold V W poissonMoment saddleVariance
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have pos : 0 ≤ V-W := by rw [diff]; exact Finset.sum_nonneg (fun _ _ => by positivity)
  have upper : V-W ≤ m*V := by
    rw [diff]
    unfold V poissonMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    nlinarith [mul_le_mul_of_nonneg_right (hmax p hp) (mul_nonneg (hr p hp) (sq_nonneg (ell p)))]
  have wp : 0 < W := by linarith
  change |h*k/W-h*k/V| ≤ 2*m*(H^2/V)
  rw [show h*k/W-h*k/V=h*k*(V-W)/(W*V) by field_simp,abs_div,abs_mul,abs_of_nonneg pos,
    abs_of_pos (mul_pos wp vp),div_le_iff₀ (mul_pos wp vp)]
  have hk2 : |h*k| ≤ H^2 := by rw [abs_mul,sq]; exact mul_le_mul hh hk (abs_nonneg k) hH
  apply (mul_le_mul hk2 upper pos (sq_nonneg H)).trans
  rw [show 2*m*(H^2/V)*(W*V) = 2*m*H^2*W by field_simp]
  nlinarith [mul_le_mul_of_nonneg_left low (mul_nonneg hm (sq_nonneg H))]

/-- The pair-insertion ratio with the exact Bernoulli variance, equal to the
    second derivative of the logarithm of the squarefree Euler product. -/
theorem saddle_pair_covariance_bernoulli {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (D : ℝ → Finset ι) (r ell : ι → ℝ) (H h k d m : ℝ)
    (hH : 0 < H) (hm : 0 ≤ m) (hr : ∀ p ∈ J, 0 ≤ r p) (hr' : ∀ p ∈ J, r p ≤ 1/2)
    (hmax : ∀ p ∈ J, r p ≤ m) (hband : ∀ p ∈ J, |ell p| ≤ H)
    (hV : 0 < poissonMoment J r ell 2) (hh : |h| ≤ H) (hk : |k| ≤ H)
    (hD : ∀ a : ℝ, |a| ≤ 2*H → (∑ p ∈ J, if p ∈ D a then r p else 0) ≤ d)
    (hsmall : 4*(H^2/poissonMoment J r ell 2)+insertionError J r ell H d ≤ 1/2) :
    let form := fun a : ℝ => omittedMass J (D a) r ell H a
    let V := poissonMoment J r ell 2
    let δ := H^2/V
    let ε := insertionError J r ell H d
    let η := 4*δ+ε
    |form (h+k)/form 0-(form h/form 0)*(form k/form 0)*(1-h*k/(saddleVariance J r ell))| ≤
      4*(4*ε+2*η^2+δ*(2*η+η^2)) + 18*m*δ := by
  let form := fun a => omittedMass J (D a) r ell H a
  let ratio := (form h/form 0)*(form k/form 0)
  let V := poissonMoment J r ell 2
  let W := saddleVariance J r ell
  let δ := H^2/V
  have h0 : |(0:ℝ)| ≤ 2*H := by rw [abs_zero]; positivity
  have h1 : |h| ≤ 2*H := by linarith
  have h2 : |k| ≤ 2*H := by linarith
  have p1 := (saddle_single_ratio J (D 0) (D h) r ell H h d hH hr hr' hband hV h1
    (hD 0 h0) (hD h h1) hsmall).2.2
  have p2 := (saddle_single_ratio J (D 0) (D k) r ell H k d hH hr hr' hband hV h2
    (hD 0 h0) (hD k h2) hsmall).2.2
  have pr : |ratio| ≤ 9 := by
    dsimp only [ratio]
    rw [abs_mul]
    exact (mul_le_mul p1 p2 (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have base := saddle_pair_covariance J D r ell H h k d hH hr hr' hband hV hh hk hD hsmall
  have diff := bernoulli_curvature_error J r ell H h k m hH.le hm hr hr' hmax hV hh hk
  have last : |ratio*(1-h*k/V)-ratio*(1-h*k/W)| ≤ 18*m*δ := by
    rw [show ratio*(1-h*k/V)-ratio*(1-h*k/W)=ratio*(h*k/W-h*k/V) by ring,abs_mul]
    exact (mul_le_mul pr diff (abs_nonneg _) (by norm_num)).trans_eq (by dsimp [δ,V]; ring)
  exact (abs_sub_le _ (ratio*(1-h*k/V)) _).trans (add_le_add base last)

end

end Cogentic.Window
