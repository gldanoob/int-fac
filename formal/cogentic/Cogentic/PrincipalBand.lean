import Cogentic.DyadicTargets
import Cogentic.WindowPrime
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Cogentic.Window
open Set Real Filter MeasureTheory

/-- The classical principal prime-count estimate on any subinterval ending at B.
    The same absolute constant serves all real endpoints at least two. -/
theorem principal_theta_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B x : ℝ, 2 ≤ x → x ≤ B →
      |Chebyshev.theta x-x| ≤ c*(1+Real.log (3*B))^2*√x := by
  obtain ⟨c,hc,bound⟩ := uniform_psi_from_critical_line line
  refine ⟨c+2,by linarith,fun B x hx hB => ?_⟩
  have p := bound 1 (1 : DirichletCharacter ℂ 1) x hx
  rw [Cogentic.principal_psi, Complex.norm_real, Real.norm_eq_abs] at p
  simp only [Nat.cast_one, mul_one] at p
  let D := 1+Real.log (3*B)
  have dp : 1 ≤ D := by dsimp [D]; linarith [Real.log_nonneg (show 1 ≤ 3*B by linarith)]
  have ds : D ≤ D^2 := by nlinarith [mul_nonneg (show 0 ≤ D by linarith) (sub_nonneg.mpr dp)]
  have l : 1+Real.log (3*x) ≤ D := by
    dsimp [D]; gcongr
  have lpos : 0 ≤ 1+Real.log (3*x) := by linarith [Real.log_nonneg (show 1 ≤ 3*x by linarith)]
  have lx : Real.log x ≤ D^2 := by
    refine le_trans ?_ ds
    dsimp [D]
    linarith [Real.log_le_log (show 0 < x by linarith) (show x ≤ 3*B by linarith)]
  have main := p.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lpos l 2) (by positivity))
  have primePowers := Chebyshev.psi_sub_theta_le (show 1 ≤ x by linarith)
  have adjust := mul_le_mul_of_nonneg_left lx (show 0 ≤ 2*√x by positivity)
  have nonneg := Chebyshev.theta_le_psi x
  rw [abs_le] at main ⊢
  change -((c+2)*D^2*√x) ≤ _ ∧ _ ≤ (c+2)*D^2*√x
  constructor <;> linarith

private noncomputable def primeLogWeight (n : ℕ) : ℂ :=
  if n.Prime then (Real.log n : ℂ) else 0

private theorem theta_prefix (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n = (Chebyshev.theta x : ℂ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Complex.ofReal_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

/-- Error identity for a smooth test function before taking absolute values. -/
private theorem abel_theta {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (f f' : ℝ → ℂ)
    (df : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (dc : ContinuousOn f' (Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n*primeLogWeight n) - (∫ x in a..b, f x) =
      f b*((Chebyshev.theta b:ℂ)-b) - f a*((Chebyshev.theta a:ℂ)-a) -
      ∫ x in a..b, f' x*((Chebyshev.theta x:ℂ)-x) := by
  have di : IntegrableOn (deriv f) (Icc a b) := dc.integrableOn_Icc.congr_fun
    (fun x hx => (df x hx).deriv.symm) measurableSet_Icc
  have disc := sum_mul_eq_sub_sub_integral_mul primeLogWeight ha hab
    (fun x hx => (df x hx).differentiableAt) di
  simp only [theta_prefix] at disc
  rw [disc, ← intervalIntegral.integral_of_le hab]
  have df' : (∫ x in a..b, deriv f x*(Chebyshev.theta x:ℂ)) =
      ∫ x in a..b, f' x*(Chebyshev.theta x:ℂ) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]; intro x hx; dsimp only; rw [(df x hx).deriv]
  rw [df']
  have fc : ContinuousOn f (uIcc a b) := by
    rw [uIcc_of_le hab]; exact fun x hx => (df x hx).continuousAt.continuousWithinAt
  have dc' : ContinuousOn f' (uIcc a b) := (uIcc_of_le hab).symm ▸ dc
  have parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (v := fun x : ℝ => (x:ℂ)) fc (by fun_prop)
    (fun x hx => df x (by simpa [min_eq_left hab, max_eq_right hab] using mem_Icc_of_Ioo hx))
    (fun x _ => Complex.ofRealCLM.hasDerivAt) dc'.intervalIntegrable intervalIntegrable_const
  have parts' : (∫ x in a..b, f x) = f b*(b:ℂ) - f a*(a:ℂ) - ∫ x in a..b, f' x*(x:ℂ) := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using parts
  rw [parts']
  have iθ : IntervalIntegrable (fun x : ℝ => f' x*(Chebyshev.theta x:ℂ)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have h := integrableOn_mul_sum_Icc (m := 0) primeLogWeight (show 0 ≤ a from ha) dc.integrableOn_Icc
    simpa only [theta_prefix] using h.mono_set Ioc_subset_Icc_self
  have ix : IntervalIntegrable (fun x : ℝ => f' x*(x:ℂ)) volume a b :=
    (dc'.mul (by fun_prop)).intervalIntegrable
  simp only [mul_sub, intervalIntegral.integral_sub iθ ix]
  ring

/-- Abel's error bound for a test kernel of size x^(-σ) and derivative of size
    W x^(-σ-1), with the square-root prime-count constant uniform on the band. -/
private theorem band_error {a b K σ W : ℝ} (ha : 0 < a) (hab : a ≤ b) (hσ : 1/2 < σ)
    (hK : 0 ≤ K) (hW : 0 ≤ W) (f f' : ℝ → ℂ)
    (df : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (dc : ContinuousOn f' (Icc a b))
    (fBound : ∀ x ∈ Icc a b, ‖f x‖ ≤ x^(-σ))
    (dfBound : ∀ x ∈ Icc a b, ‖f' x‖ ≤ W*x^(-σ-1))
    (theta : ∀ x ∈ Icc a b, |Chebyshev.theta x-x| ≤ K*√x) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n*primeLogWeight n) - (∫ x in a..b, f x)‖ ≤
      K*a^(1/2-σ)*(2+W/(σ-1/2)) := by
  let err (x : ℝ) := (Chebyshev.theta x:ℂ)-(x:ℂ)
  have bound (x : ℝ) (hx : x ∈ Icc a b) : ‖err x‖ ≤ K*x^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    simpa only [err, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using theta x hx
  let e := 1/2-σ
  have he : e < 0 := by dsimp [e]; linarith
  have endval (x : ℝ) (hx : x ∈ Icc a b) : ‖f x*err x‖ ≤ K*a^e := by
    have pos := ha.trans_le hx.1
    rw [norm_mul]
    calc
      _ ≤ x^(-σ)*(K*x^(1/2:ℝ)) := mul_le_mul (fBound x hx) (bound x hx) (norm_nonneg _) (by positivity)
      _ = K*x^e := by rw [mul_left_comm, ← Real.rpow_add pos]; dsimp [e]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hx.1 he.le) hK
  have integrand (x : ℝ) (hx : x ∈ Ioc a b) : ‖f' x*err x‖ ≤ (W*K)*x^(e-1) := by
    have hc := mem_Icc_of_Ioc hx
    have pos := ha.trans hx.1
    rw [norm_mul]
    calc
      _ ≤ (W*x^(-σ-1))*(K*x^(1/2:ℝ)) := mul_le_mul (dfBound x hc) (bound x hc) (norm_nonneg _) (by positivity)
      _ = _ := by rw [mul_mul_mul_comm, ← Real.rpow_add pos]; congr 2; dsimp [e]; ring
  have hzero : (0:ℝ) ∉ uIcc a b := by rw [uIcc_of_le hab]; exact fun h => ha.not_ge h.1
  have integ : ‖∫ x in a..b, f' x*err x‖ ≤ (W*K)*(a^e/(-e)) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hab
      (Eventually.of_forall integrand)
      ((intervalIntegral.intervalIntegrable_rpow (μ := volume) (r := e-1) (Or.inr hzero)).const_mul (W*K))
    refine h.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith,hzero⟩), sub_add_cancel]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hW hK)
    rw [div_neg, ← neg_div, div_le_div_right_of_neg he]
    linarith [Real.rpow_nonneg (ha.le.trans hab) e]
  rw [abel_theta ha.le hab f f' df dc]
  calc
    _ ≤ (‖f b*err b‖ + ‖f a*err a‖) + ‖∫ x in a..b, f' x*err x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (K*a^e + K*a^e) + (W*K)*(a^e/(-e)) :=
      add_le_add (add_le_add (endval b ⟨hab,le_rfl⟩) (endval a ⟨le_rfl,hab⟩)) integ
    _ = _ := by rw [show -e = σ-1/2 by dsimp [e]; ring]; dsimp [e]; ring

/-- Continuous prime integral on the actual band, with a square-root error
    scaled by the frequency. No zero-density or prime-count input is assumed here. -/
theorem principal_prime_integral (line : DirichletLZerosOnLine) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (a b : ℝ) (s : ℂ), 4 ≤ a → a ≤ b → 1/2 < s.re →
      ‖(∑ n ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (n:ℂ)^(-s)) -
         (∫ x in a..b, (x:ℂ)^(-s)/((Real.log x:ℝ):ℂ))‖ ≤
        (c*(1+Real.log (3*b))^2)*a^(1/2-s.re)*(2+(‖s‖+1)/(s.re-1/2)) := by
  obtain ⟨c,hc,theta⟩ := principal_theta_from_critical_line line
  refine ⟨c,hc,fun a b s ha hab hs => ?_⟩
  let F := fun x : ℝ => (x:ℂ)^(-s)
  let G := fun x : ℝ => (((Real.log x)⁻¹:ℝ):ℂ)
  let dF := fun x : ℝ => -s*(x:ℂ)^(-s-1)
  let dG := fun x : ℝ => ((-x⁻¹/(Real.log x)^2:ℝ):ℂ)
  have xpos (x : ℝ) (h : x ∈ Icc a b) : 0 < x := by linarith [h.1]
  have lp (x : ℝ) (h : x ∈ Icc a b) : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le (xpos x h)).mpr
    linarith [Real.exp_one_lt_d9, h.1]
  have sn : -s ≠ 0 := by
    intro h
    have eq := neg_eq_zero.mp h
    norm_num [eq] at hs
  have sn' : -s-1 ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have df (x : ℝ) (h : x ∈ Icc a b) : HasDerivAt F (dF x) x :=
    hasDerivAt_ofReal_cpow_const (xpos x h).ne' sn
  have dg (x : ℝ) (h : x ∈ Icc a b) : HasDerivAt G (dG x) x := by
    exact ((Real.hasDerivAt_log (xpos x h).ne').inv (by linarith [lp x h])).ofReal_comp
  have dcont : ContinuousOn (fun x => dF x*G x + F x*dG x) (Icc a b) := by
    intro x hx
    have h1 := (df x hx).continuousAt
    have h2 := (dg x hx).continuousAt
    have h3 : ContinuousAt dF x := continuousAt_const.mul
      (hasDerivAt_ofReal_cpow_const (xpos x hx).ne' sn').continuousAt
    have h4 : ContinuousAt dG x := by
      have h0 := (xpos x hx).ne'
      have L : Real.log x ≠ 0 := by linarith [lp x hx]
      dsimp [dG]; fun_prop (disch := positivity)
    exact ((h3.mul h2).add (h1.mul h4)).continuousWithinAt
  have gbound (x : ℝ) (hx : x ∈ Icc a b) : ‖G x‖ ≤ 1 := by
    simp only [G, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by linarith [lp x hx] : 0 ≤ Real.log x)]
    exact (inv_le_one₀ (by linarith [lp x hx])).mpr (lp x hx)
  have dgbound (x : ℝ) (hx : x ∈ Icc a b) : ‖dG x‖ ≤ x⁻¹ := by
    have L := lp x hx
    have pos := xpos x hx
    simp only [dG, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_inv,
      abs_of_pos pos, abs_of_nonneg (sq_nonneg (Real.log x))]
    apply div_le_self (by positivity)
    nlinarith [sq_nonneg (Real.log x-1)]
  have fnorm (x : ℝ) (hx : x ∈ Icc a b) : ‖F x‖ = x^(-s.re) := by
    simp only [F,Complex.norm_cpow_eq_rpow_re_of_pos (xpos x hx), Complex.neg_re]
  have bound := band_error (a := a) (b := b) (by linarith) hab hs
    (show 0 ≤ c*(1+Real.log (3*b))^2 by positivity) (show 0 ≤ ‖s‖+1 by positivity)
    (fun x => F x*G x) (fun x => dF x*G x+F x*dG x)
    (fun x hx => (df x hx).mul (dg x hx)) dcont (by
      intro x hx
      rw [norm_mul, fnorm x hx]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (gbound x hx) (Real.rpow_nonneg (xpos x hx).le (-s.re)))
    (by
      intro x hx
      have pos := xpos x hx
      have h := norm_add_le (dF x*G x) (F x*dG x)
      rw [norm_mul (dF x) (G x), norm_mul (F x) (dG x), fnorm x hx] at h
      have dfn : ‖dF x‖ = ‖s‖*x^(-s.re-1) := by
        simp only [dF, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos pos,
          Complex.sub_re, Complex.neg_re, Complex.one_re]
      rw [dfn] at h
      apply h.trans
      calc
        _ ≤ (‖s‖*x^(-s.re-1))*1 + x^(-s.re)*x⁻¹ := add_le_add
          (mul_le_mul_of_nonneg_left (gbound x hx) (by positivity))
          (mul_le_mul_of_nonneg_left (dgbound x hx) (by positivity))
        _ = _ := by rw [← Real.rpow_neg_one, ← Real.rpow_add pos]; ring_nf)
    (fun x hx => theta b x (by linarith [hx.1]) hx.2)
  have bandSame : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, F n*G n*primeLogWeight n) =
      ∑ n ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (n:ℂ)^(-s) := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · have nz : ((Real.log n:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      simp only [F,G,primeLogWeight,hp,if_true, Complex.ofReal_inv, Complex.ofReal_natCast,
        mul_assoc, inv_mul_cancel₀ nz, mul_one]
    · simp [primeLogWeight,hp]
  rw [bandSame] at bound
  simpa only [F,G,Complex.ofReal_inv, div_eq_mul_inv] using bound

/-- Change of variables x = exp v in the prime integral. -/
theorem principal_integral_log_band (a b : ℝ) (s : ℂ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in Real.exp a..Real.exp b, (x:ℂ)^(-s)/((Real.log x:ℝ):ℂ)) =
      ∫ v in a..b, Complex.exp ((1-s)*v)/(v:ℂ) := by
  let g (x : ℝ) := (x:ℂ)^(-s)/((Real.log x:ℝ):ℂ)
  have cont : ContinuousOn g (Real.exp '' uIcc a b) := by
    rintro _ ⟨v,hv,rfl⟩
    rw [uIcc_of_le hab] at hv
    have pos := ha.trans_le hv.1
    have nz : ((Real.log (Real.exp v):ℝ):ℂ) ≠ 0 := by simp [pos.ne']
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div (f := fun x : ℝ => (x:ℂ)^(-s)) (g := fun x : ℝ => ((Real.log x:ℝ):ℂ)) _ _ nz
    · by_cases h : -s = 0
      · simp [h, continuousAt_const]
      · exact (hasDerivAt_ofReal_cpow_const (Real.exp_pos v).ne' h).continuousAt
    · exact Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log (Real.exp_pos _).ne')
  have sub := intervalIntegral.integral_deriv_smul_comp' (fun x _ => Real.hasDerivAt_exp x)
    Real.continuous_exp.continuousOn cont
  change (∫ x in Real.exp a..Real.exp b, g x) = _
  rw [← sub]
  apply intervalIntegral.integral_congr
  intro v _
  simp only [Function.comp_apply, g, Real.log_exp, Complex.real_smul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, Complex.ofReal_exp,
    ← mul_div_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- One absolute constant controls the principal prime integral throughout
    the fixed frequency rectangle. Both endpoints are real before flooring. -/
theorem fixed_principal_prime_band (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (s : ℂ), 16 ≤ B →
      199/200 ≤ s.re → s.re ≤ 1 → |s.im| ≤ B^(1/5 : ℝ) →
      ‖(∑ n ∈ (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime, (n:ℂ)^(-s)) -
         (∫ x in Real.log B/2..Real.log B, Complex.exp ((1-s)*x)/(x:ℂ))‖ ≤
        C*(1+Real.log (3*B))^2*B^(-19/400 : ℝ) := by
  obtain ⟨c,hc,main⟩ := principal_prime_integral line
  refine ⟨10*c,by positivity,fun B s hB hlo hhi ht => ?_⟩
  have one : 1 ≤ B := by linarith
  have pos : 0 < B := by linarith
  have lpos := Real.log_pos (show 1 < B by linarith)
  have sq := Real.sq_sqrt pos.le
  have spos := Real.sqrt_nonneg B
  have lo : 4 ≤ Real.sqrt B := by nlinarith
  have hab : Real.sqrt B ≤ B := by nlinarith
  have sden : 0 < s.re-1/2 := by linarith
  have k0 : 0 ≤ c*(1+Real.log (3*B))^2 := by positivity
  have hpow := Real.one_le_rpow one (show (0 : ℝ) ≤ 1/5 by norm_num)
  have hs := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg (show 0 ≤ s.re by linarith)] at hs
  have height : 2+(‖s‖+1)/(s.re-1/2) ≤ 10*B^(1/5 : ℝ) := by
    have aux : (‖s‖+1)/(s.re-1/2) ≤ 8*B^(1/5 : ℝ) := by
      apply (div_le_iff₀ sden).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (Real.rpow_nonneg pos.le (1/5:ℝ))]
    linarith
  have power : (Real.sqrt B)^(1/2-s.re) ≤ B^(-99/400 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul pos.le]
    apply Real.rpow_le_rpow_of_exponent_le one
    linarith
  have changevar := principal_integral_log_band (Real.log B/2) (Real.log B) s (by linarith) (by linarith)
  rw [Real.exp_log pos, show Real.exp (Real.log B/2) = Real.sqrt B by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos pos]; congr 1; ring] at changevar
  rw [← changevar]
  refine (main _ _ _ lo hab (by linarith)).trans ?_
  calc
    _ ≤ (c*(1+Real.log (3*B))^2*B^(-99/400:ℝ))*(10*B^(1/5:ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left power k0) height (by positivity) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add pos, show (-99/400+1/5:ℝ) = -19/400 by norm_num]
      ring

end Cogentic.Window
