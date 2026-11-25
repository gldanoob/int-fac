import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped Interval

namespace Cogentic.Window

noncomputable section

/-- The oscillatory prime main term in logarithmic coordinates on a dyadic
    log-band. The factor `|z.im|` is the Mellin frequency. -/
theorem prime_integral_decay (z : ℂ) (a : ℝ) (ha : 0 < a) (hz : 0 ≤ z.re) :
    |z.im| * ‖∫ x in a..2*a, Complex.exp (z*x)/(x : ℂ)‖ ≤
      3 * Real.exp (z.re*(2*a)) / a := by
  let F (x : ℝ) : ℂ := Complex.exp (z*x)/(x : ℂ)
  let G (x : ℝ) : ℂ := Complex.exp (z*x)/(x : ℂ)^2
  let M := Real.exp (z.re*(2*a))
  have hab : a ≤ 2*a := by linarith
  have pos (x : ℝ) (hx : x ∈ [[a, 2*a]]) : 0 < x := by
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have nonzero (x : ℝ) (hx : x ∈ [[a, 2*a]]) : (x : ℂ) ≠ 0 := by
    exact_mod_cast (pos x hx).ne'
  have cF : ContinuousOn F [[a, 2*a]] :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn.div
      Complex.continuous_ofReal.continuousOn nonzero
  have cG : ContinuousOn G [[a, 2*a]] :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn.div
      (Complex.continuous_ofReal.pow 2).continuousOn (fun x hx => pow_ne_zero _ (nonzero x hx))
  have derivative (x : ℝ) (hx : x ∈ [[a, 2*a]]) : HasDerivAt F (z*F x - G x) x := by
    have h := ((((hasDerivAt_id (x : ℂ)).const_mul z).cexp).fun_div
      (hasDerivAt_id (x : ℂ)) (nonzero x hx)).comp_ofReal
    apply h.congr_deriv
    simp only [F, G, id_eq, mul_one]
    field_simp [nonzero x hx]
  have intF := cF.intervalIntegrable (μ := volume)
  have intG := cG.intervalIntegrable (μ := volume)
  have identity : z*(∫ x in a..2*a, F x) =
      (F (2*a) - F a) + ∫ x in a..2*a, G x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative ((intF.const_mul z).sub intG)
    rw [intervalIntegral.integral_sub (intF.const_mul z) intG, intervalIntegral.integral_const_mul] at h
    exact sub_eq_iff_eq_add.mp h
  have expBound (x : ℝ) (hx : x ≤ 2*a) : ‖Complex.exp (z*x)‖ ≤ M := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using mul_le_mul_of_nonneg_left hx hz
  have mpos : 0 ≤ M := (Real.exp_pos _).le
  have boundF (x : ℝ) (lo : a ≤ x) (hi : x ≤ 2*a) : ‖F x‖ ≤ M/a := by
    simp only [F, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans_le lo)]
    exact div_le_div₀ mpos (expBound _ hi) ha lo
  have boundG : ‖∫ x in a..2*a, G x‖ ≤ M/a := by
    have bound (x : ℝ) (hx : x ∈ Ι a (2*a)) : ‖G x‖ ≤ M/a^2 := by
      rw [uIoc_of_le hab] at hx
      simp only [G, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans hx.1)]
      exact div_le_div₀ mpos (expBound _ hx.2) (sq_pos_of_pos ha) (by gcongr; exact hx.1.le)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const bound
    rw [abs_of_nonneg (sub_nonneg.mpr hab), show 2*a - a = a by ring] at h
    convert h using 1
    field_simp
  change |z.im| * ‖∫ x in a..2*a, F x‖ ≤ 3*M/a
  calc
    _ ≤ ‖z * ∫ x in a..2*a, F x‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _)
    _ = _ := congrArg norm identity
    _ ≤ ‖F (2*a) - F a‖ + ‖∫ x in a..2*a, G x‖ := norm_add_le ..
    _ ≤ (M/a + M/a) + M/a := add_le_add
      ((norm_sub_le ..).trans (add_le_add (boundF _ hab le_rfl) (boundF _ le_rfl hab))) boundG
    _ = _ := by ring

/-- The ordinary prime-counting character sum. -/
def primeCount {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, if n.Prime then χ n else 0

/-- Abel summation on the actual prime band. The input is the ordinary
    square-root character estimate, with its logarithms absorbed into `K`.
    The output retains the frequency loss `‖s‖` and the lower-endpoint saving. -/
theorem prime_band_from_count {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a b K : ℝ) (s : ℂ) (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K) (hs : 1/2 < s.re)
    (hcount : ∀ x ∈ Icc a b, ‖primeCount χ x‖ ≤ K*x^(1/2 : ℝ)) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, if n.Prime then (n : ℂ)^(-s)*χ n else 0‖ ≤
      K * a^(1/2 - s.re) * (2 + ‖s‖ / (s.re - 1/2)) := by
  let f (x : ℝ) := (x : ℂ)^(-s)
  let e := (1/2 : ℝ) - s.re
  let P := primeCount χ
  have he : e < 0 := by dsimp [e]; linarith
  have hzero : (0 : ℝ) ∉ [[a,b]] := by rw [uIcc_of_le hab]; exact fun h => ha.not_ge h.1
  have sd : -s ≠ 0 := by
    intro h
    have eq : s = 0 := neg_eq_zero.mp h
    simp [eq] at hs
    linarith
  have sd' : -s - 1 ≠ 0 := by
    intro h
    have eq := congrArg Complex.re h
    simp at eq
    linarith
  have derivative (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt f (-s*(x : ℂ)^(-s-1)) x :=
    hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne' sd
  have cont : ContinuousOn (fun x : ℝ => -s*(x : ℂ)^(-s-1)) (Icc a b) := by
    intro x hx
    exact (continuousAt_const.mul
      (hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne' sd').continuousAt).continuousWithinAt
  have hint : IntegrableOn (deriv f) (Icc a b) := by
    apply (cont.integrableOn_Icc).congr_fun _ measurableSet_Icc
    intro x hx
    exact (derivative x hx).deriv.symm
  have parts := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => if n.Prime then χ n else 0) ha.le hab
    (fun x hx => (derivative x hx).differentiableAt) hint
  change ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * (if n.Prime then χ n else 0) =
    f b * P b - f a * P a - ∫ x in Ioc a b, deriv f x * P x at parts
  have endpoint (x : ℝ) (hx : x ∈ Icc a b) : ‖f x * P x‖ ≤ K*a^e := by
    have pos := ha.trans_le hx.1
    rw [norm_mul, show ‖f x‖ = x^(-s.re) by simp [f, Complex.norm_cpow_eq_rpow_re_of_pos pos] ]
    calc
      _ ≤ x^(-s.re) * (K*x^(1/2 : ℝ)) := mul_le_mul_of_nonneg_left (hcount _ hx) (Real.rpow_nonneg pos.le _)
      _ = K * x^e := by rw [mul_left_comm, ← Real.rpow_add pos]; dsimp [e]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hx.1 he.le) hK
  have integrand (x : ℝ) (hx : x ∈ Ioc a b) :
      ‖deriv f x * P x‖ ≤ (‖s‖*K) * x^(e-1) := by
    have pos := ha.trans hx.1
    have mem := mem_Icc_of_Ioc hx
    rw [(derivative x mem).deriv, norm_mul, norm_mul, norm_neg,
      Complex.norm_cpow_eq_rpow_re_of_pos pos, Complex.sub_re, Complex.neg_re, Complex.one_re]
    calc
      _ ≤ (‖s‖*x^(-s.re-1)) * (K*x^(1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hcount _ mem) (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg pos.le _))
      _ = _ := by
        rw [mul_mul_mul_comm, ← Real.rpow_add pos]
        congr 2
        dsimp [e]
        ring
  have integralBound : ‖∫ x in Ioc a b, deriv f x * P x‖ ≤
      (‖s‖*K) * (a^e / (-e)) := by
    rw [← intervalIntegral.integral_of_le hab]
    have cmp := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall integrand)
      ((intervalIntegral.intervalIntegrable_rpow (μ := volume) (r := e-1) (Or.inr hzero)).const_mul
        (‖s‖*K))
    refine cmp.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, hzero⟩), sub_add_cancel]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hK)
    rw [div_neg, ← neg_div, div_le_div_right_of_neg he]
    linarith [Real.rpow_nonneg (ha.le.trans hab) e]
  have scaledSum : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
      if n.Prime then (n : ℂ)^(-s)*χ n else 0) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * (if n.Prime then χ n else 0) := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : n.Prime <;> simp [h, f]
  rw [scaledSum, parts]
  calc
    _ ≤ (‖f b * P b‖ + ‖f a * P a‖) + ‖∫ x in Ioc a b, deriv f x * P x‖ :=
      (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) le_rfl)
    _ ≤ (K*a^e + K*a^e) + (‖s‖*K)*(a^e / (-e)) :=
      add_le_add (add_le_add (endpoint _ ⟨hab,le_rfl⟩) (endpoint _ ⟨le_rfl,hab⟩)) integralBound
    _ = _ := by rw [show -e = s.re - 1/2 by dsimp [e]; ring]; dsimp [e]; ring

/-- The fixed schedule's full frequency rectangle. The saving is
    `1/5 + (1/2 - 199/200)/2 = -19/400`. -/
theorem fixed_frequency_prime_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (B K : ℝ) (s : ℂ) (hB : 1 ≤ B) (hK : 0 ≤ K)
    (hlo : 199/200 ≤ s.re) (hhi : s.re ≤ 1) (ht : |s.im| ≤ B^(1/5 : ℝ))
    (hcount : ∀ x ∈ Icc (Real.sqrt B) B, ‖primeCount χ x‖ ≤ K*x^(1/2 : ℝ)) :
    ‖∑ n ∈ Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊, if n.Prime then (n : ℂ)^(-s)*χ n else 0‖ ≤
      8*K*B^(-19/400 : ℝ) := by
  have pos : 0 < B := zero_lt_one.trans_le hB
  have hpow := Real.one_le_rpow hB (show (0 : ℝ) ≤ 1/5 by norm_num)
  have hden : 0 < s.re-1/2 := by linarith
  have hab : Real.sqrt B ≤ B := by
    calc
      _ = B^(1/2 : ℝ) := Real.sqrt_eq_rpow B
      _ ≤ B^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
      _ = _ := Real.rpow_one B
  have hs := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg (show 0 ≤ s.re by linarith)] at hs
  have height : 2 + ‖s‖/(s.re-1/2) ≤ 8*B^(1/5 : ℝ) := by
    have quotient : ‖s‖/(s.re-1/2) ≤ 6*B^(1/5 : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (Real.rpow_nonneg pos.le (1/5 : ℝ))]
    linarith
  have power : (Real.sqrt B)^(1/2-s.re) ≤ B^(-99/400 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul pos.le]
    apply Real.rpow_le_rpow_of_exponent_le hB
    linarith
  refine (prime_band_from_count χ _ B K s (Real.sqrt_pos.mpr pos) hab hK (by linarith) hcount).trans ?_
  calc
    _ ≤ (K*B^(-99/400 : ℝ))*(8*B^(1/5 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left power hK) height
        (by positivity) (mul_nonneg hK (Real.rpow_nonneg pos.le _))
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add pos]
      rw [show (-99/400 + 1/5 : ℝ) = -19/400 by norm_num, mul_comm K]

private theorem one_add_norm_bound (w : ℂ) :
    ‖1+w‖ ≤ Real.exp (w.re + ‖w‖^2/2) := by
  have hs : ‖1+w‖^2 = 1 + (2*w.re + ‖w‖^2) := by
    simp [Complex.sq_norm, Complex.normSq_add]
    ring
  have h := Real.add_one_le_exp (2*w.re + ‖w‖^2)
  have hex : Real.exp (2*w.re + ‖w‖^2) = Real.exp (w.re + ‖w‖^2/2)^2 := by
    rw [pow_two (Real.exp _), ← Real.exp_add]
    congr 1
    ring
  rw [hex] at h
  nlinarith [norm_nonneg (1+w), Real.exp_pos (w.re + ‖w‖^2/2)]

/-- The quadratic error in the absolute Euler-product bound is an absolute
    constant on the fixed contour, independently of the prime band or modulus. -/
theorem squarefree_product_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (J : Finset ℕ) (hJ : ∀ p ∈ J, 1 ≤ p) (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖∏ p ∈ J, (1 + (p : ℂ)^(-s)*χ p)‖ ≤ Real.exp
      (‖∑ p ∈ J, (p : ℂ)^(-s)*χ p‖ + (∑' n : ℕ, (n : ℝ)^(-3/2 : ℝ))/2) := by
  let w (p : ℕ) : ℂ := (p : ℂ)^(-s)*χ p
  have quad (p : ℕ) (hp : p ∈ J) : ‖w p‖^2 ≤ (p : ℝ)^(-3/2 : ℝ) := by
    have pone : (1 : ℝ) ≤ p := by exact_mod_cast hJ p hp
    have pos : (0 : ℝ) < p := zero_lt_one.trans_le pone
    have h1 : ‖w p‖ ≤ (p : ℝ)^(-s.re) := by
      rw [show ‖w p‖ = ‖(p : ℂ)^(-s)‖*‖χ p‖ by exact norm_mul ..,
        ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos pos, Complex.neg_re]
      exact (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (Real.rpow_nonneg pos.le _)).trans_eq (mul_one _)
    calc
      _ ≤ ((p : ℝ)^(-s.re))^2 := pow_le_pow_left₀ (norm_nonneg _) h1 _
      _ = (p : ℝ)^((-s.re)*2) := by rw [Real.rpow_mul pos.le, Real.rpow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le pone (by linarith)
  have tail := Real.summable_nat_rpow.mpr (show (-3/2 : ℝ) < -1 by norm_num)
  have quadSum : ∑ p ∈ J, ‖w p‖^2 ≤ ∑' n : ℕ, (n : ℝ)^(-3/2 : ℝ) :=
    (Finset.sum_le_sum quad).trans
      (tail.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  change ‖∏ p ∈ J, (1 + w p)‖ ≤ _
  rw [norm_prod]
  calc
    _ ≤ ∏ p ∈ J, Real.exp ((w p).re + ‖w p‖^2/2) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => one_add_norm_bound (w p))
    _ = _ := (Real.exp_sum _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Complex.re_sum]
      exact add_le_add (Complex.re_le_norm _) (by linarith)

/-- Nonprincipal Euler-product bound on the entire fixed rectangle when the
    ordinary prime-counting character satisfies a square-root estimate. -/
theorem fixed_frequency_euler_product {q : ℕ} (χ : DirichletCharacter ℂ q)
    (B K : ℝ) (s : ℂ) (hB : 1 ≤ B) (hK : 0 ≤ K)
    (hlo : 199/200 ≤ s.re) (hhi : s.re ≤ 1) (ht : |s.im| ≤ B^(1/5 : ℝ))
    (hcount : ∀ x ∈ Icc (Real.sqrt B) B, ‖primeCount χ x‖ ≤ K*x^(1/2 : ℝ)) :
    let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    ‖∏ p ∈ J, (1 + (p : ℂ)^(-s)*χ p)‖ ≤
      Real.exp (8*K*B^(-19/400 : ℝ) + (∑' n : ℕ, (n : ℝ)^(-3/2 : ℝ))/2) := by
  dsimp only
  refine (squarefree_product_bound χ _ (fun p hp => (Finset.mem_filter.mp hp).2.one_le)
    s (by linarith)).trans (Real.exp_le_exp.mpr (add_le_add ?_ le_rfl))
  rw [Finset.sum_filter]
  exact fixed_frequency_prime_sum χ B K s hB hK hlo hhi ht hcount

/-- Character factors at omitted primes, including primes of the progression
    modulus, cost at most the stated term per removed member of the band. -/
theorem fixed_frequency_euler_product_omitting {q : ℕ} (χ : DirichletCharacter ℂ q)
    (B K : ℝ) (s : ℂ) (D : Finset ℕ) (hB : 1 ≤ B) (hK : 0 ≤ K)
    (hlo : 199/200 ≤ s.re) (hhi : s.re ≤ 1) (ht : |s.im| ≤ B^(1/5 : ℝ))
    (hcount : ∀ x ∈ Icc (Real.sqrt B) B, ‖primeCount χ x‖ ≤ K*x^(1/2 : ℝ))
    (hD : D ⊆ (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime) :
    let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    ‖∏ p ∈ J \ D, (1 + (p : ℂ)^(-s)*χ p)‖ ≤
      Real.exp (8*K*B^(-19/400 : ℝ) + D.card*B^(-199/400 : ℝ) +
        (∑' n : ℕ, (n : ℝ)^(-3/2 : ℝ))/2) := by
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  let w (p : ℕ) := (p : ℂ)^(-s)*χ p
  have pos : 0 < B := zero_lt_one.trans_le hB
  have sqrtPos := Real.sqrt_pos.mpr pos
  have deleted (p : ℕ) (hp : p ∈ D) : ‖w p‖ ≤ B^(-199/400 : ℝ) := by
    have lower : Real.sqrt B < p :=
      Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hD hp)).1).1
    have ppos := sqrtPos.trans lower
    rw [show ‖w p‖ = ‖(p : ℂ)^(-s)‖ * ‖χ p‖ by exact norm_mul ..,
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos ppos, Complex.neg_re]
    calc
      _ ≤ (p : ℝ)^(-s.re) := by
        simpa using mul_le_mul_of_nonneg_left (χ.norm_le_one (p : ZMod q)) (Real.rpow_nonneg ppos.le (-s.re))
      _ ≤ (Real.sqrt B)^(-s.re) := Real.rpow_le_rpow_of_nonpos sqrtPos lower.le (by linarith)
      _ ≤ _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul pos.le]
        apply Real.rpow_le_rpow_of_exponent_le hB
        linarith
  have small : ‖∑ p ∈ D, w p‖ ≤ D.card*B^(-199/400 : ℝ) := by
    calc
      _ ≤ ∑ p ∈ D, ‖w p‖ := norm_sum_le ..
      _ ≤ ∑ _p ∈ D, B^(-199/400 : ℝ) := Finset.sum_le_sum deleted
      _ = _ := by simp
  have full : ‖∑ p ∈ J, w p‖ ≤ 8*K*B^(-19/400 : ℝ) := by
    dsimp [J]
    rw [Finset.sum_filter]
    exact fixed_frequency_prime_sum χ B K s hB hK hlo hhi ht hcount
  have sub : ‖∑ p ∈ J \ D, w p‖ ≤ 8*K*B^(-19/400 : ℝ) + D.card*B^(-199/400 : ℝ) := by
    rw [Finset.sum_sdiff_eq_sub hD]
    exact (norm_sub_le ..).trans (add_le_add full small)
  exact (squarefree_product_bound χ _ (fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.one_le) s (by linarith)).trans
    (Real.exp_le_exp.mpr (add_le_add sub le_rfl))

end

end Cogentic.Window
