import Cogentic.RandomizedHasseIncidence
import Cogentic.RandomizedPrimeBinSupply
import Cogentic.RandomizedSplitWork
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Real Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology ArithmeticFunction.Omega FourierTransform

namespace Cogentic.RandomizedEllipticAndGaussian

noncomputable section

/-!
# Discrete Gaussian Progression, 2D Mahalanobis Tiles, Hasse Exceptional Primes, and Recursive Elliptic Recognition

This file formalizes:
1. Elementary unimodal Riemann tile bounds for 1D discrete Gaussian progressions (valid for all
   widths `σ > 0`, steps `m > 0`, and translates `r ∈ ℝ`), together with exact residue-class
   probability bounds (both exponentially sharp via Poisson summation and the clean interval
   `[(1 - q/σ)/q, (1 + q/σ)/q]`) and single-root progression conditioning.
2. 2D rectangular Mahalanobis tile comparison for correlated bivariate Gaussians on arbitrary
   translated rectangular lattices, yielding both the exact full-lattice normalizer bounds
   `1 - π δ - π δ^2 ≤ h₁ h₂ Z_lat / Z ≤ 1 + π δ + π δ^2` and the `O(r₀^2)` discarded
   inner-ellipse mass bound (including the `V^(-a)` specialization `O(V^(-2a))`).
3. Dyadic Hasse-interval exceptional-prime deletion bounds combining
   `Cogentic.RandomizedHasseIncidence.rich_hasse_centres_mul_le`, prime-factor deletion of `N`,
   band-weighted deletion charges, and `Cogentic.Randomized.primeBin_supply_from_critical_line`.
4. Soundness and strong-induction failure-probability bounds for a two-stage recursive partial
   factorizer (small-factor prepass up to `B` followed by recursive elliptic splitting on
   non-exceptional primes), achieving complete verified prime factorization with failure
   probability at most `δ_small + m.log2 * δ_split`.
-/

/-! ## Part 1: 1D Unimodal Riemann Tile Comparison & Residue-Class Probability Bounds -/

section DiscreteGaussian1D

/-- The unnormalized 1D Gaussian weight (matching `Cogentic.Window.coeffGaussian`). -/
def coeffGaussian (x μ σ : ℝ) : ℝ := Real.exp (-π * ((x - μ) / σ) ^ 2)

private lemma coeffGaussian_progression (c M j μ t : ℝ) (hM : 0 < M) :
    coeffGaussian (c + M * j) μ t = coeffGaussian j ((μ - c) / M) (t / M) := by
  unfold coeffGaussian
  congr 3
  field_simp
  ring

private lemma shifted_gaussian_poisson (θ τ : ℝ) (hτ : 0 < τ) :
    ((∑' j : ℤ, coeffGaussian j θ τ : ℝ) : ℂ) =
      (τ : ℂ) * ∑' n : ℤ, (Real.exp (-π * τ ^ 2 * (n : ℝ) ^ 2) : ℂ) *
        fourier n ((-θ : ℝ) : UnitAddCircle) := by
  let a : ℝ := (τ⁻¹) ^ 2
  let f : ℝ → ℂ := fun x => Complex.exp (-(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have h1 : 0 < ((π : ℂ) * a).re := by simpa using mul_pos Real.pi_pos ha
  have h2 : 0 < ((π : ℂ) / a).re := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    positivity
  have hscale : 1 / (a : ℂ) ^ (1 / 2 : ℂ) = τ := by
    have hs : a ^ (1 / 2 : ℝ) = τ⁻¹ := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (inv_nonneg.mpr hτ.le)]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow ha.le, hs]
    simp
  have hF : 𝓕 f = fun x : ℝ => (τ : ℂ) * Complex.exp (-(π : ℂ) / (a : ℂ) * (x : ℂ) ^ 2) := by
    simpa only [f, hscale] using (fourier_gaussian_pi (show 0 < (a : ℂ).re by exact ha))
  have hdec : f =O[cocompact ℝ] (|·| ^ (-2 : ℝ)) := by
    simpa only [f, neg_mul] using (isLittleO_exp_neg_mul_sq_cocompact h1 (-2)).isBigO
  have hdecF : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-2 : ℝ)) := by
    rw [hF]
    simpa only [neg_div] using
      ((isLittleO_exp_neg_mul_sq_cocompact h2 (-2)).isBigO.const_mul_left (τ : ℂ))
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay (f := f)
    (by dsimp [f]; fun_prop) one_lt_two hdec hdecF (-θ)
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  convert hp using 1
  · apply tsum_congr; intro n
    simp only [coeffGaussian, Complex.ofReal_exp, f]
    congr 1; push_cast; dsimp [a]; push_cast; ring
  · rw [hF]
    apply tsum_congr; intro n
    rw [← mul_assoc]
    congr 2
    rw [Complex.ofReal_exp]
    congr 1; dsimp [a]; push_cast; ring_nf; simp; ring

private lemma bilateral_fourier_tail (f : ℤ → ℂ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hz : f 0 = 1)
    (h : ∀ n : ℕ, ‖f ((n : ℤ) + 1)‖ ≤ ρ ^ (n + 1) ∧ ‖f (-((n : ℤ) + 1))‖ ≤ ρ ^ (n + 1)) :
    ‖(∑' n : ℤ, f n) - 1‖ ≤ 2 * ρ / (1 - ρ) := by
  have geo : HasSum (fun n : ℕ => ρ ^ (n + 1)) (ρ / (1 - ρ)) := by
    simpa only [pow_succ', div_eq_mul_inv, one_div] using
      (hasSum_geometric_of_lt_one hρ hρ').mul_left ρ
  have hp : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    Summable.of_norm_bounded geo.summable (fun n => (h n).1)
  have hn : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    Summable.of_norm_bounded geo.summable (fun n => (h n).2)
  have hp0 : Summable (fun n : ℕ => f (n : ℤ)) := (summable_nat_add_iff 1).mp hp
  rw [tsum_of_nat_of_neg_add_one hp0 hn, hp0.tsum_eq_zero_add]
  simp only [Nat.cast_zero, hz, Nat.cast_add, Nat.cast_one]
  rw [show 1 + (∑' n : ℕ, f ((n : ℤ) + 1)) + (∑' n : ℕ, f (-((n : ℤ) + 1))) - 1 =
    (∑' n : ℕ, f ((n : ℤ) + 1)) + (∑' n : ℕ, f (-((n : ℤ) + 1))) by ring]
  exact (norm_add_le ..).trans ((add_le_add
    (tsum_of_norm_bounded geo (fun n => (h n).1))
    (tsum_of_norm_bounded geo (fun n => (h n).2))).trans_eq (by ring))

/-- Poisson-summation relative error bound for a shifted 1D discrete Gaussian normalizer
(matching `Cogentic.Window.shifted_gaussian_normalizer`). -/
theorem shifted_gaussian_normalizer (θ τ : ℝ) (hτ : 1 ≤ τ) :
    |(∑' j : ℤ, coeffGaussian j θ τ) / τ - 1| ≤ 3 * Real.exp (-π * τ ^ 2) := by
  have ht : 0 < τ := by linarith
  let ρ := Real.exp (-π * τ ^ 2)
  have hpos : 0 < ρ := Real.exp_pos _
  have hr : ρ ≤ 1 / 3 := by
    have he : 3 ≤ Real.exp (π * τ ^ 2) := by
      nlinarith [Real.add_one_le_exp (π * τ ^ 2), Real.pi_gt_three,
        mul_nonneg Real.pi_pos.le (show 0 ≤ τ ^ 2 - 1 by nlinarith)]
    dsimp [ρ]; rw [neg_mul, Real.exp_neg]
    exact (inv_anti₀ (by norm_num : 0 < (3 : ℝ)) he).trans_eq (by ring)
  let f : ℤ → ℂ := fun n => (Real.exp (-π * τ ^ 2 * (n : ℝ) ^ 2) : ℂ) *
    fourier n ((-θ : ℝ) : UnitAddCircle)
  have fnorm (n : ℤ) : ‖f n‖ = Real.exp (-π * τ ^ 2 * (n : ℝ) ^ 2) := by
    change ‖(Real.exp (-π * τ ^ 2 * (n : ℝ) ^ 2) : ℂ) * fourier n ((-θ : ℝ) : UnitAddCircle)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      show ‖fourier n ((-θ : ℝ) : UnitAddCircle)‖ = 1 from Circle.norm_coe _, mul_one]
  have coeff (n : ℕ) :
      ‖f ((n : ℤ) + 1)‖ ≤ ρ ^ (n + 1) ∧ ‖f (-((n : ℤ) + 1))‖ ≤ ρ ^ (n + 1) := by
    rw [fnorm, fnorm]; dsimp [ρ]; rw [← Real.exp_nat_mul]; push_cast
    constructor <;> apply Real.exp_le_exp.mpr <;>
      nlinarith [mul_nonneg (show 0 ≤ π * τ ^ 2 by positivity) (show 0 ≤ (n : ℝ) ^ 2 + n by positivity)]
  have tail := bilateral_fourier_tail f ρ hpos.le (by linarith) (by simp [f]) coeff
  have id := shifted_gaussian_poisson θ τ ht
  change _ = (τ : ℂ) * ∑' n : ℤ, f n at id
  have id' : (∑' n : ℤ, f n) = ((∑' j : ℤ, coeffGaussian j θ τ : ℝ) : ℂ) / τ := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr ht.ne'), id, mul_comm]
  rw [id', ← Complex.ofReal_div, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at tail
  exact tail.trans ((div_le_iff₀ (by linarith : 0 < 1 - ρ)).mpr
    (by nlinarith [mul_nonneg hpos.le (show 0 ≤ 1 / 3 - ρ by linarith)]))

private lemma conditional_progression_probability (c M μ t : ℝ) (hM : 0 < M) (hτ : 2 ≤ t / M)
    (E : ℤ → Prop) [DecidablePred E] :
    let w := fun j : ℤ => coeffGaussian (c + M * j) μ t
    let z := ∑' j : ℤ, w j
    let n := ∑' j : ℤ, if E j then w j else 0
    0 < z ∧ |n / z - M / t * n| ≤ 6 * Real.exp (-π * (t / M) ^ 2) * (M / t * n) := by
  dsimp only
  let Z := ∑' j : ℤ, coeffGaussian (c + M * j) μ t
  let N := ∑' j : ℤ, if E j then coeffGaussian (c + M * j) μ t else 0
  let τ := t / M
  let e := 3 * Real.exp (-π * τ ^ 2)
  have ht : 0 < τ := by dsimp [τ]; linarith
  have Zerr : |Z / τ - 1| ≤ e := by
    dsimp [Z, τ, e]
    simp_rw [coeffGaussian_progression _ _ _ _ _ hM]
    exact shifted_gaussian_normalizer _ _ (by linarith)
  have he : e ≤ 1 / 2 := by
    have hx : 6 ≤ Real.exp (π * τ ^ 2) := by
      nlinarith [Real.add_one_le_exp (π * τ ^ 2), Real.pi_gt_three,
        mul_nonneg Real.pi_pos.le (show 0 ≤ τ ^ 2 - 4 by nlinarith)]
    dsimp [e]; rw [neg_mul, Real.exp_neg]
    have hi := inv_anti₀ (by norm_num : 0 < (6 : ℝ)) hx
    linarith
  have zp : 0 < Z := by
    have := (abs_le.mp Zerr).1
    exact (div_pos_iff_of_pos_right ht).mp (by linarith)
  have Zlow : τ ≤ 2 * Z := by
    have := (le_div_iff₀ ht).mp (by linarith [(abs_le.mp Zerr).1] : 1 / 2 ≤ Z / τ)
    linarith
  have zabs : |Z - τ| ≤ τ * e := by
    have eq : Z / τ - 1 = (Z - τ) / τ := by field_simp
    rw [eq, abs_div, abs_of_pos ht] at Zerr
    exact ((div_le_iff₀ ht).mp Zerr).trans_eq (by ring)
  have npos : 0 ≤ N := by
    apply tsum_nonneg; intro j; split <;> [exact (Real.exp_pos _).le; rfl]
  change 0 < Z ∧ |N / Z - M / t * N| ≤ 6 * Real.exp (-π * τ ^ 2) * (M / t * N)
  rw [show 6 * Real.exp (-π * τ ^ 2) = 2 * e by dsimp [e]; ring]
  have tpos : 0 < t := (div_pos_iff_of_pos_right hM).mp ht
  have minv : M / t = 1 / τ := by dsimp [τ]; field_simp
  rw [minv]
  refine ⟨zp, ?_⟩
  have eq : N / Z - 1 / τ * N = (N / τ) * ((τ - Z) / Z) := by field_simp
  rw [eq, abs_mul, abs_of_nonneg (div_nonneg npos ht.le), abs_div, abs_of_pos zp, abs_sub_comm τ Z]
  have err : |Z - τ| / Z ≤ 2 * e := by
    rw [div_le_iff₀ zp]
    exact zabs.trans ((mul_le_mul_of_nonneg_right Zlow (by dsimp [e]; positivity)).trans_eq (by ring))
  exact (mul_le_mul_of_nonneg_left err (div_nonneg npos ht.le)).trans_eq (by ring)

private lemma gaussian_integral_eq (σ : ℝ) (hσ : 0 < σ) :
    (∫ x : ℝ, coeffGaussian x 0 σ) = σ := by
  have hrew : (fun x : ℝ => coeffGaussian x 0 σ) = fun x : ℝ => Real.exp (-(π / σ ^ 2) * x ^ 2) := by
    ext x
    unfold coeffGaussian
    congr 1
    ring
  rw [hrew, integral_gaussian (π / σ ^ 2)]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  rw [show π / (π / σ ^ 2) = σ ^ 2 by field_simp [hpi, hσ.ne'], Real.sqrt_sq hσ.le]

private lemma integrable_coeffGaussian_zero (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : ℝ => coeffGaussian x 0 σ) volume := by
  have hrew : (fun x : ℝ => coeffGaussian x 0 σ) = fun x : ℝ => Real.exp (-(π / σ ^ 2) * x ^ 2) := by
    ext x
    unfold coeffGaussian
    congr 1
    ring
  rw [hrew]
  exact integrable_exp_neg_mul_sq (by positivity)

private lemma coeffGaussian_zero_le_one (x σ : ℝ) : coeffGaussian x 0 σ ≤ 1 := by
  unfold coeffGaussian
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg ((x - 0) / σ)])

private lemma coeffGaussian_zero_pos (x σ : ℝ) : 0 < coeffGaussian x 0 σ :=
  Real.exp_pos _

private lemma coeffGaussian_zero_antitone_abs {x y σ : ℝ} (h : |x| ≤ |y|) :
    coeffGaussian y 0 σ ≤ coeffGaussian x 0 σ := by
  unfold coeffGaussian
  apply Real.exp_le_exp.mpr
  have hsq : x ^ 2 ≤ y ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg x) (abs_nonneg y)).mpr h
    simpa [sq_abs] using this
  have hdiv : ((x - 0) / σ) ^ 2 ≤ ((y - 0) / σ) ^ 2 := by
    simp only [sub_zero, div_pow]
    exact div_le_div_of_nonneg_right hsq (sq_nonneg σ)
  nlinarith [Real.pi_pos]

private lemma continuous_coeffGaussian_zero (σ : ℝ) :
    Continuous (fun x : ℝ => coeffGaussian x 0 σ) := by
  unfold coeffGaussian
  fun_prop

private lemma unimodal_gaussian_zero_shifted (r σ m : ℝ) (hσ : 0 < σ) (hm : 0 < m)
    (hr0 : 0 ≤ r) (hrm : r < m) :
    Summable (fun k : ℤ => coeffGaussian (r + k * m) 0 σ) ∧
      σ / m - 1 ≤ (∑' k : ℤ, coeffGaussian (r + k * m) 0 σ) ∧
      (∑' k : ℤ, coeffGaussian (r + k * m) 0 σ) ≤ σ / m + 1 := by
  let g : ℝ → ℝ := fun x => coeffGaussian x 0 σ
  let xpos : ℕ → ℝ := fun n => r + (n : ℝ) * m
  let xneg : ℕ → ℝ := fun n => r - ((n : ℝ) + 1) * m
  have hg_cont : Continuous g := continuous_coeffGaussian_zero σ
  have hg_int : Integrable g volume := integrable_coeffGaussian_zero σ hσ
  have hg_pos (x : ℝ) : 0 ≤ g x := (coeffGaussian_zero_pos x σ).le
  have hg_le1 (x : ℝ) : g x ≤ 1 := coeffGaussian_zero_le_one x σ
  have hg_ii (a b : ℝ) : IntervalIntegrable g volume a b := hg_cont.intervalIntegrable a b
  -- Step bounds on positive intervals [xpos n, xpos (n+1)]
  have hpos_step_lo (n : ℕ) : (∫ t in xpos n..xpos (n + 1), g t) ≤ m * g (xpos n) := by
    have hle : xpos n ≤ xpos (n + 1) := by dsimp [xpos]; push_cast; linarith
    have hbd : ∀ t ∈ Set.Icc (xpos n) (xpos (n + 1)), g t ≤ g (xpos n) := by
      intro t ht
      apply coeffGaussian_zero_antitone_abs
      have h0 : 0 ≤ xpos n := by dsimp [xpos]; positivity
      rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans ht.1)]
      exact ht.1
    calc
      (∫ t in xpos n..xpos (n + 1), g t)
          ≤ ∫ _t in xpos n..xpos (n + 1), g (xpos n) :=
        intervalIntegral.integral_mono_on hle (hg_ii _ _) intervalIntegrable_const hbd
      _ = m * g (xpos n) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        congr 1; dsimp [xpos]; push_cast; ring
  have hpos_step_hi (n : ℕ) : m * g (xpos (n + 1)) ≤ ∫ t in xpos n..xpos (n + 1), g t := by
    have hle : xpos n ≤ xpos (n + 1) := by dsimp [xpos]; push_cast; linarith
    have hbd : ∀ t ∈ Set.Icc (xpos n) (xpos (n + 1)), g (xpos (n + 1)) ≤ g t := by
      intro t ht
      apply coeffGaussian_zero_antitone_abs
      have h0 : 0 ≤ xpos n := by dsimp [xpos]; positivity
      rw [abs_of_nonneg (h0.trans ht.1), abs_of_nonneg (h0.trans hle)]
      exact ht.2
    calc
      m * g (xpos (n + 1)) = ∫ _t in xpos n..xpos (n + 1), g (xpos (n + 1)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        congr 1; dsimp [xpos]; push_cast; ring
      _ ≤ ∫ t in xpos n..xpos (n + 1), g t :=
        intervalIntegral.integral_mono_on hle intervalIntegrable_const (hg_ii _ _) hbd
  -- Step bounds on negative intervals [xneg (n+1), xneg n]
  have hneg_nonpos (n : ℕ) : xneg n ≤ 0 := by
    dsimp [xneg]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith
  have hneg_step_lo (n : ℕ) : (∫ t in xneg (n + 1)..xneg n, g t) ≤ m * g (xneg n) := by
    have hle : xneg (n + 1) ≤ xneg n := by dsimp [xneg]; push_cast; linarith
    have hbd : ∀ t ∈ Set.Icc (xneg (n + 1)) (xneg n), g t ≤ g (xneg n) := by
      intro t ht
      apply coeffGaussian_zero_antitone_abs
      have h0 := hneg_nonpos n
      rw [abs_of_nonpos h0, abs_of_nonpos (ht.2.trans h0)]
      linarith [ht.2]
    calc
      (∫ t in xneg (n + 1)..xneg n, g t)
          ≤ ∫ _t in xneg (n + 1)..xneg n, g (xneg n) :=
        intervalIntegral.integral_mono_on hle (hg_ii _ _) intervalIntegrable_const hbd
      _ = m * g (xneg n) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        congr 1; dsimp [xneg]; push_cast; ring
  have hneg_step_hi (n : ℕ) : m * g (xneg (n + 1)) ≤ ∫ t in xneg (n + 1)..xneg n, g t := by
    have hle : xneg (n + 1) ≤ xneg n := by dsimp [xneg]; push_cast; linarith
    have hbd : ∀ t ∈ Set.Icc (xneg (n + 1)) (xneg n), g (xneg (n + 1)) ≤ g t := by
      intro t ht
      apply coeffGaussian_zero_antitone_abs
      have h0 := hneg_nonpos n
      rw [abs_of_nonpos (ht.2.trans h0), abs_of_nonpos (hle.trans h0)]
      linarith [ht.1]
    calc
      m * g (xneg (n + 1)) = ∫ _t in xneg (n + 1)..xneg n, g (xneg (n + 1)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        congr 1; dsimp [xneg]; push_cast; ring
      _ ≤ ∫ t in xneg (n + 1)..xneg n, g t :=
        intervalIntegral.integral_mono_on hle intervalIntegrable_const (hg_ii _ _) hbd
  -- Center interval [xneg 0, xpos 0] = [r - m, r] containing 0
  have hcenter_lo : (∫ t in xneg 0..xpos 0, g t) ≤ m := by
    have hle : xneg 0 ≤ xpos 0 := by dsimp [xneg, xpos]; linarith
    calc
      (∫ t in xneg 0..xpos 0, g t)
          ≤ ∫ _t in xneg 0..xpos 0, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hle (hg_ii _ _) intervalIntegrable_const (fun t _ => hg_le1 t)
      _ = m := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        dsimp [xneg, xpos]; ring
  have hcenter_hi : m * (g (xneg 0) + g (xpos 0)) ≤ (∫ t in xneg 0..xpos 0, g t) + m := by
    have hle1 : xneg 0 ≤ 0 := hneg_nonpos 0
    have hle2 : 0 ≤ xpos 0 := by dsimp [xpos]; linarith
    have hleft : (m - r) * g (xneg 0) ≤ ∫ t in xneg 0..0, g t := by
      calc
        (m - r) * g (xneg 0) = ∫ _t in xneg 0..0, g (xneg 0) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          congr 1; dsimp [xneg]; ring
        _ ≤ ∫ t in xneg 0..0, g t :=
          intervalIntegral.integral_mono_on hle1 intervalIntegrable_const (hg_ii _ _) (fun t ht => by
            apply coeffGaussian_zero_antitone_abs
            rw [abs_of_nonpos ht.2, abs_of_nonpos hle1]
            linarith [ht.1])
    have hright : r * g (xpos 0) ≤ ∫ t in 0..xpos 0, g t := by
      calc
        r * g (xpos 0) = ∫ _t in 0..xpos 0, g (xpos 0) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          congr 1; dsimp [xpos]; ring
        _ ≤ ∫ t in 0..xpos 0, g t :=
          intervalIntegral.integral_mono_on hle2 intervalIntegrable_const (hg_ii _ _) (fun t ht => by
            apply coeffGaussian_zero_antitone_abs
            rw [abs_of_nonneg ht.1, abs_of_nonneg hle2]
            exact ht.2)
    have hsplit : (∫ t in xneg 0..0, g t) + (∫ t in 0..xpos 0, g t) =
        ∫ t in xneg 0..xpos 0, g t :=
      intervalIntegral.integral_add_adjacent_intervals (hg_ii _ _) (hg_ii _ _)
    have h1 : r * g (xneg 0) ≤ r := by nlinarith [hg_le1 (xneg 0)]
    have h2 : (m - r) * g (xpos 0) ≤ m - r := by nlinarith [hg_le1 (xpos 0)]
    linarith
  -- Telescoping identities
  have htel_pos (N : ℕ) :
      (∑ n ∈ Finset.range N, ∫ t in xpos n..xpos (n + 1), g t) = ∫ t in xpos 0..xpos N, g t := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals (hg_ii _ _) (hg_ii _ _)
  have htel_neg (N : ℕ) :
      (∑ n ∈ Finset.range N, ∫ t in xneg (n + 1)..xneg n, g t) = ∫ t in xneg N..xneg 0, g t := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals (hg_ii _ _) (hg_ii _ _)
  -- Integral over any finite interval is bounded by full integral σ
  have hint_le_sigma (a b : ℝ) (hab : a ≤ b) : (∫ t in a..b, g t) ≤ σ := by
    rw [intervalIntegral.integral_of_le hab, ← gaussian_integral_eq σ hσ]
    exact setIntegral_le_integral hg_int (Eventually.of_forall hg_pos)
  -- Partial sum upper bound for all N
  have hpartial_hi (N : ℕ) :
      (∑ n ∈ Finset.range (N + 1), g (xpos n)) + (∑ n ∈ Finset.range (N + 1), g (xneg n)) ≤
        σ / m + 1 := by
    have h1 : m * (∑ n ∈ Finset.range N, g (xpos (n + 1))) ≤ ∫ t in xpos 0..xpos N, g t := by
      rw [Finset.mul_sum, ← htel_pos N]
      exact Finset.sum_le_sum fun n _ => hpos_step_hi n
    have h2 : m * (∑ n ∈ Finset.range N, g (xneg (n + 1))) ≤ ∫ t in xneg N..xneg 0, g t := by
      rw [Finset.mul_sum, ← htel_neg N]
      exact Finset.sum_le_sum fun n _ => hneg_step_hi n
    have hcomb : (∫ t in xneg N..xneg 0, g t) + (∫ t in xneg 0..xpos 0, g t) +
        (∫ t in xpos 0..xpos N, g t) = ∫ t in xneg N..xpos N, g t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hg_ii _ _) (hg_ii _ _),
        intervalIntegral.integral_add_adjacent_intervals (hg_ii _ _) (hg_ii _ _)]
    have hle_N : xneg N ≤ xpos N := by
      have := hneg_nonpos N
      have : 0 ≤ xpos N := by dsimp [xpos]; positivity
      linarith
    have htot := hint_le_sigma (xneg N) (xpos N) hle_N
    have hmul : m * ((∑ n ∈ Finset.range (N + 1), g (xpos n)) +
        (∑ n ∈ Finset.range (N + 1), g (xneg n))) ≤ σ + m := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      linarith
    have hdiv := (le_div_iff₀ hm).mpr (by linarith : ((∑ n ∈ Finset.range (N + 1), g (xpos n)) +
      (∑ n ∈ Finset.range (N + 1), g (xneg n))) * m ≤ σ + m)
    have hsimp : (σ + m) / m = σ / m + 1 := by field_simp [hm.ne']
    linarith
  -- Deduce Summable and upper bound on tsum over ℤ
  have hf_eq_pos (n : ℕ) : coeffGaussian (r + (n : ℤ) * m) 0 σ = g (xpos n) := by
    simp [g, xpos]
  have hf_eq_neg (n : ℕ) : coeffGaussian (r + (-(n : ℤ) - 1) * m) 0 σ = g (xneg n) := by
    simp only [g, xneg, Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]
    congr 1; ring
  have hsum_pos : Summable (fun n : ℕ => g (xpos n)) := by
    refine summable_of_sum_range_le (fun n => hg_pos _) (c := σ / m + 1) fun N => ?_
    have h1 := hpartial_hi N
    have h2 : 0 ≤ ∑ n ∈ Finset.range (N + 1), g (xneg n) := Finset.sum_nonneg fun _ _ => hg_pos _
    have h3 : (∑ n ∈ Finset.range N, g (xpos n)) ≤ ∑ n ∈ Finset.range (N + 1), g (xpos n) := by
      rw [Finset.sum_range_succ]; linarith [hg_pos (xpos N)]
    linarith
  have hsum_neg : Summable (fun n : ℕ => g (xneg n)) := by
    refine summable_of_sum_range_le (fun n => hg_pos _) (c := σ / m + 1) fun N => ?_
    have h1 := hpartial_hi N
    have h2 : 0 ≤ ∑ n ∈ Finset.range (N + 1), g (xpos n) := Finset.sum_nonneg fun _ _ => hg_pos _
    have h3 : (∑ n ∈ Finset.range N, g (xneg n)) ≤ ∑ n ∈ Finset.range (N + 1), g (xneg n) := by
      rw [Finset.sum_range_succ]; linarith [hg_pos (xneg N)]
    linarith
  let f : ℤ → ℝ := fun k => coeffGaussian (r + k * m) 0 σ
  have hsum_pos' : Summable (fun n : ℕ => f (n : ℤ)) := by
    simpa only [f, hf_eq_pos] using hsum_pos
  have hsum_neg' : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    have hrew : (fun n : ℕ => f (-((n : ℤ) + 1))) = fun n : ℕ => g (xneg n) := by
      ext n
      simpa only [neg_add, ← sub_eq_add_neg] using hf_eq_neg n
    rw [hrew]; exact hsum_neg
  have hsum_int : Summable f :=
    summable_int_of_summable_nat hsum_pos' (by
      have := hsum_neg'
      simpa [Int.negSucc_eq] using (summable_nat_add_iff 1).mpr (by
        have hrew : (fun n : ℕ => f (-(↑(n + 1) : ℤ))) = fun n : ℕ => f (-((n : ℤ) + 1)) := by
          ext n; push_cast; rfl
        rw [hrew]; exact hsum_neg'))
  have htsum_split : (∑' k : ℤ, f k) = (∑' n : ℕ, g (xpos n)) + (∑' n : ℕ, g (xneg n)) := by
    rw [tsum_of_nat_of_neg_add_one hsum_pos' hsum_neg']
    congr 1
    · exact tsum_congr fun n => hf_eq_pos n
    · exact tsum_congr fun n => by
        simpa only [neg_add, ← sub_eq_add_neg] using hf_eq_neg n
  have hupper : (∑' k : ℤ, f k) ≤ σ / m + 1 := by
    rw [htsum_split]
    have htend : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), g (xpos n)) +
        (∑ n ∈ Finset.range (N + 1), g (xneg n))) atTop
        (𝓝 ((∑' n : ℕ, g (xpos n)) + (∑' n : ℕ, g (xneg n)))) := by
      have hp := (hsum_pos.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
      have hn := (hsum_neg.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
      exact hp.add hn
    exact le_of_tendsto htend (Eventually.of_forall hpartial_hi)
  -- Lower bound on tsum via intervalIntegral_tendsto_integral
  have hlower_N (N : ℕ) : (∫ t in xneg N..xpos N, g t) ≤ m * (∑' k : ℤ, f k) + m := by
    have h1 : (∫ t in xpos 0..xpos N, g t) ≤ m * (∑ n ∈ Finset.range N, g (xpos n)) := by
      rw [Finset.mul_sum, ← htel_pos N]
      exact Finset.sum_le_sum fun n _ => hpos_step_lo n
    have h2 : (∫ t in xneg N..xneg 0, g t) ≤ m * (∑ n ∈ Finset.range N, g (xneg n)) := by
      rw [Finset.mul_sum, ← htel_neg N]
      exact Finset.sum_le_sum fun n _ => hneg_step_lo n
    have hcomb : (∫ t in xneg N..xneg 0, g t) + (∫ t in xneg 0..xpos 0, g t) +
        (∫ t in xpos 0..xpos N, g t) = ∫ t in xneg N..xpos N, g t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hg_ii _ _) (hg_ii _ _),
        intervalIntegral.integral_add_adjacent_intervals (hg_ii _ _) (hg_ii _ _)]
    have hp_le : (∑ n ∈ Finset.range N, g (xpos n)) ≤ ∑' n : ℕ, g (xpos n) :=
      hsum_pos.sum_le_tsum (Finset.range N) (fun n _ => hg_pos _)
    have hn_le : (∑ n ∈ Finset.range N, g (xneg n)) ≤ ∑' n : ℕ, g (xneg n) :=
      hsum_neg.sum_le_tsum (Finset.range N) (fun n _ => hg_pos _)
    rw [htsum_split]
    nlinarith
  have hxpos_top : Tendsto xpos atTop atTop := by
    dsimp [xpos]
    exact tendsto_atTop_add_const_left atTop r
      (Tendsto.atTop_mul_const hm tendsto_natCast_atTop_atTop)
  have hxneg_bot : Tendsto xneg atTop atBot := by
    dsimp [xneg]
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * m) atTop atTop :=
      Tendsto.atTop_mul_const hm (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    exact tendsto_const_nhds_sub_atTop r h1
  have htend_int : Tendsto (fun N : ℕ => ∫ t in xneg N..xpos N, g t) atTop (𝓝 σ) := by
    rw [← gaussian_integral_eq σ hσ]
    exact intervalIntegral_tendsto_integral hg_int hxneg_bot hxpos_top
  have hsigma_le : σ ≤ m * (∑' k : ℤ, f k) + m :=
    le_of_tendsto htend_int (Eventually.of_forall hlower_N)
  have hlower : σ / m - 1 ≤ ∑' k : ℤ, f k := by
    rw [sub_le_iff_le_add, div_le_iff₀ hm]
    linarith
  exact ⟨hsum_int, hlower, hupper⟩

/-- **Unimodal Riemann tile comparison for 1D discrete Gaussian progressions.**
For EVERY width `σ > 0`, step `m > 0`, center `μ ∈ ℝ`, and shift `r ∈ ℝ`, the discrete
Gaussian sum along the arithmetic progression `r + k * m` is summable and lies within `± 1`
of its continuous integral density `σ / m`. -/
theorem unimodal_gaussian_progression_bounds (r μ σ m : ℝ) (hσ : 0 < σ) (hm : 0 < m) :
    Summable (fun k : ℤ => coeffGaussian (r + k * m) μ σ) ∧
      σ / m - 1 ≤ (∑' k : ℤ, coeffGaussian (r + k * m) μ σ) ∧
      (∑' k : ℤ, coeffGaussian (r + k * m) μ σ) ≤ σ / m + 1 := by
  let k₀ : ℤ := ⌊(r - μ) / m⌋
  let r' : ℝ := (r - μ) - (k₀ : ℝ) * m
  have hr0 : 0 ≤ r' := by
    dsimp [r', k₀]
    have h := (Int.floor_le ((r - μ) / m))
    have := (le_div_iff₀ hm).mp h
    linarith
  have hrm : r' < m := by
    dsimp [r', k₀]
    have h := Int.lt_floor_add_one ((r - μ) / m)
    have := (div_lt_iff₀ hm).mp h
    linarith
  have hbase := unimodal_gaussian_zero_shifted r' σ m hσ hm hr0 hrm
  let e : ℤ ≃ ℤ := Equiv.addRight (-k₀)
  have hcomp : (fun k : ℤ => coeffGaussian (r + k * m) μ σ) ∘ (Equiv.addRight k₀) =
      fun k : ℤ => coeffGaussian (r' + k * m) 0 σ := by
    ext k
    simp only [Function.comp_apply, Equiv.coe_addRight, coeffGaussian, sub_zero, r']
    congr 2
    push_cast
    ring
  have hsum : Summable (fun k : ℤ => coeffGaussian (r + k * m) μ σ) := by
    rw [← (Equiv.addRight k₀).summable_iff, hcomp]
    exact hbase.1
  have htsum : (∑' k : ℤ, coeffGaussian (r + k * m) μ σ) =
      ∑' k : ℤ, coeffGaussian (r' + k * m) 0 σ := by
    rw [← (Equiv.addRight k₀).tsum_eq, ← hcomp]
    rfl
  rw [htsum]
  exact ⟨hsum, hbase.2.1, hbase.2.2⟩

/-- Residue-class indicator sum equals the translated progression sum. -/
theorem residue_class_tsum_eq (a : ℤ) (q : ℕ) (hq : 0 < q) (μ σ : ℝ) :
    (∑' n : ℤ, if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0) =
      ∑' k : ℤ, coeffGaussian ((a : ℝ) + (k : ℝ) * (q : ℝ)) μ σ := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  let f : ℤ → ℤ := fun k => a + k * (q : ℤ)
  have hf_inj : Function.Injective f := by
    intro k₁ k₂ h
    dsimp [f] at h
    exact mul_right_cancel₀ hqZ (add_left_cancel h)
  have hrange : ∀ n : ℤ, (n : ZMod q) = (a : ZMod q) ↔ n ∈ Set.range f := by
    intro n
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      dsimp [f]; linarith
    · rintro ⟨k, rfl⟩
      refine ⟨-k, ?_⟩
      dsimp [f]; ring
  have hrew : (fun n : ℤ => if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0) =
      Set.indicator (Set.range f) (fun n : ℤ => coeffGaussian n μ σ) := by
    ext n
    simp [Set.indicator_apply, hrange]
  rw [hrew, tsum_indicator_range hf_inj]
  apply tsum_congr
  intro k
  simp [f]

/-- Elementary exponential bound: `9 * exp(-π * τ^2) ≤ 1 / τ` for all `τ ≥ 1`. -/
private lemma nine_mul_exp_neg_pi_sq_le_inv {τ : ℝ} (hτ : 1 ≤ τ) :
    9 * Real.exp (-π * τ ^ 2) ≤ 1 / τ := by
  have hτpos : 0 < τ := by linarith
  have hx : 0 ≤ π * τ ^ 2 := by positivity
  have hsum := Real.sum_le_exp_of_nonneg hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one,
    Nat.cast_one, div_one, zero_add] at hsum
  have hpi : 3 < π := Real.pi_gt_three
  have hτ2 : τ ≤ τ ^ 2 := by nlinarith
  have hτ4 : τ ≤ τ ^ 4 := by nlinarith
  have hτ6 : τ ≤ τ ^ 6 := by nlinarith
  have h1 : 9 * τ ≤ Real.exp (π * τ ^ 2) := by
    have hpow2 : 9 * τ ^ 4 ≤ (π * τ ^ 2) ^ 2 := by nlinarith [sq_nonneg τ]
    have hpow3 : 27 * τ ^ 6 ≤ (π * τ ^ 2) ^ 3 := by
      have : (3 * τ ^ 2) ^ 3 ≤ (π * τ ^ 2) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg τ]) 3
      linarith
    norm_num at hsum
    nlinarith
  rw [neg_mul, Real.exp_neg, one_div]
  have hinv := inv_anti₀ (by positivity : 0 < 9 * τ) h1
  have : 9 * (Real.exp (π * τ ^ 2))⁻¹ ≤ 9 * (9 * τ)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by norm_num)
  calc
    9 * (Real.exp (π * τ ^ 2))⁻¹ ≤ 9 * (9 * τ)⁻¹ := this
    _ = τ⁻¹ := by field_simp [hτpos.ne']

/-- **Exponentially sharp 1D discrete Gaussian residue-class probability bound**
(reusing `Cogentic.Window.shifted_gaussian_normalizer`). For any modulus `q ≥ 1` and width
`σ ≥ q`, every residue class `a mod q` has probability within `9 * exp(-π (σ/q)^2) / q` of `1/q`. -/
theorem gaussian_residue_class_prob_sharp (a : ℤ) (q : ℕ) (hq : 0 < q) (μ σ : ℝ)
    (hσq : (q : ℝ) ≤ σ) :
    let Z := ∑' n : ℤ, coeffGaussian n μ σ
    let Z_a := ∑' n : ℤ, if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0
    0 < Z ∧ |Z_a / Z - 1 / (q : ℝ)| ≤ 9 * Real.exp (-π * (σ / q) ^ 2) / (q : ℝ) := by
  dsimp only
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hτ : 1 ≤ σ / (q : ℝ) := (one_le_div hqR).mpr hσq
  have hσ1 : 1 ≤ σ := hq1.trans hσq
  have hσpos : 0 < σ := by linarith
  have hτpos : 0 < σ / (q : ℝ) := by linarith
  let ε : ℝ := 3 * Real.exp (-π * (σ / (q : ℝ)) ^ 2)
  have hε_nonneg : 0 ≤ ε := by positivity
  have hε_small : ε ≤ 1 / 3 := by
    have hexp : 9 ≤ Real.exp (π * (σ / (q : ℝ)) ^ 2) := by
      have := nine_mul_exp_neg_pi_sq_le_inv hτ
      have h1 : 1 / (σ / (q : ℝ)) ≤ 1 := (div_le_one hτpos).mpr hτ
      rw [neg_mul, Real.exp_neg] at this
      have h2 : 9 * (Real.exp (π * (σ / (q : ℝ)) ^ 2))⁻¹ ≤ 1 := this.trans h1
      have hpos := Real.exp_pos (π * (σ / (q : ℝ)) ^ 2)
      have := (mul_le_iff_le_one_right hpos).mp (by
        calc
          9 * (Real.exp (π * (σ / (q : ℝ)) ^ 2))⁻¹ * Real.exp (π * (σ / (q : ℝ)) ^ 2)
              ≤ 1 * Real.exp (π * (σ / (q : ℝ)) ^ 2) := mul_le_mul_of_nonneg_right h2 hpos.le
          _ = Real.exp (π * (σ / (q : ℝ)) ^ 2) := one_mul _)
      -- simpler: directly use h2
      have h3 : 9 = 9 * (Real.exp (π * (σ / (q : ℝ)) ^ 2))⁻¹ * Real.exp (π * (σ / (q : ℝ)) ^ 2) := by
        field_simp [hpos.ne']
      nlinarith [mul_le_mul_of_nonneg_right h2 hpos.le]
    dsimp [ε]
    rw [neg_mul, Real.exp_neg]
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 9) hexp
    linarith
  -- Full normalizer Z bound
  have hZ_norm : |(∑' n : ℤ, coeffGaussian n μ σ) / σ - 1| ≤ ε := by
    have h1 := shifted_gaussian_normalizer μ σ hσ1
    have hmono : Real.exp (-π * σ ^ 2) ≤ Real.exp (-π * (σ / (q : ℝ)) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hle : σ / (q : ℝ) ≤ σ := div_le_self hσpos.le hq1
      have hsq : (σ / (q : ℝ)) ^ 2 ≤ σ ^ 2 :=
        pow_le_pow_left₀ hτpos.le hle 2
      nlinarith [Real.pi_pos]
    exact h1.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  -- Residue-class normalizer Z_a bound
  have hZa_eq : (∑' n : ℤ, if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0) =
      ∑' k : ℤ, coeffGaussian k ((μ - (a : ℝ)) / (q : ℝ)) (σ / (q : ℝ)) := by
    rw [residue_class_tsum_eq a q hq μ σ]
    apply tsum_congr
    intro k
    have h := coeffGaussian_progression (a : ℝ) (q : ℝ) (k : ℝ) μ σ hqR
    simpa [mul_comm] using h
  have hZa_norm : |(∑' n : ℤ, if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0) /
      (σ / (q : ℝ)) - 1| ≤ ε := by
    rw [hZa_eq]
    exact shifted_gaussian_normalizer ((μ - (a : ℝ)) / (q : ℝ)) (σ / (q : ℝ)) hτ
  let Z := ∑' n : ℤ, coeffGaussian n μ σ
  let Z_a := ∑' n : ℤ, if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0
  have hZ_lo : (1 - ε) * σ ≤ Z := (le_div_iff₀ hσpos).mp (by linarith [(abs_le.mp hZ_norm).1])
  have hZ_hi : Z ≤ (1 + ε) * σ := (div_le_iff₀ hσpos).mp (by linarith [(abs_le.mp hZ_norm).2])
  have hZa_lo : (1 - ε) * (σ / (q : ℝ)) ≤ Z_a :=
    (le_div_iff₀ hτpos).mp (by linarith [(abs_le.mp hZa_norm).1])
  have hZa_hi : Z_a ≤ (1 + ε) * (σ / (q : ℝ)) :=
    (div_le_iff₀ hτpos).mp (by linarith [(abs_le.mp hZa_norm).2])
  have hZ_pos : 0 < Z := (mul_pos (by linarith : 0 < 1 - ε) hσpos).trans_le hZ_lo
  refine ⟨hZ_pos, ?_⟩
  have hdiff : |Z_a * (q : ℝ) - Z| ≤ 2 * ε * σ := by
    rw [abs_le]
    have hZa_q_lo : (1 - ε) * σ ≤ Z_a * (q : ℝ) := by
      have := mul_le_mul_of_nonneg_right hZa_lo hqR.le
      rwa [mul_assoc, div_mul_cancel₀ _ hqR.ne'] at this
    have hZa_q_hi : Z_a * (q : ℝ) ≤ (1 + ε) * σ := by
      have := mul_le_mul_of_nonneg_right hZa_hi hqR.le
      rwa [mul_assoc, div_mul_cancel₀ _ hqR.ne'] at this
    constructor <;> linarith
  have hZ_23 : (2 / 3) * σ ≤ Z := by nlinarith
  have heq : Z_a / Z - 1 / (q : ℝ) = (Z_a * (q : ℝ) - Z) / (Z * (q : ℝ)) := by
    field_simp [hZ_pos.ne', hqR.ne']
  rw [heq, abs_div, abs_of_pos (mul_pos hZ_pos hqR), div_le_iff₀ (mul_pos hZ_pos hqR)]
  calc
    |Z_a * (q : ℝ) - Z| ≤ 2 * ε * σ := hdiff
    _ = 3 * ε * ((2 / 3) * σ) := by ring
    _ ≤ 3 * ε * Z := mul_le_mul_of_nonneg_left hZ_23 (by positivity)
    _ = 9 * Real.exp (-π * (σ / (q : ℝ)) ^ 2) / (q : ℝ) * (Z * (q : ℝ)) := by
      dsimp [ε]; field_simp [hqR.ne']; ring

/-- **Exact residue-class probability interval** `[(1 - q/σ)/q, (1 + q/σ)/q]`:
for any modulus `q ≥ 1` and width `σ ≥ q`, every residue class `a mod q` of a 1D discrete
Gaussian of width `σ` has probability in `[(1 - q / σ) / q, (1 + q / σ) / q]`. -/
theorem gaussian_residue_class_prob_interval (a : ℤ) (q : ℕ) (hq : 0 < q) (μ σ : ℝ)
    (hσq : (q : ℝ) ≤ σ) :
    let Z := ∑' n : ℤ, coeffGaussian n μ σ
    let Z_a := ∑' n : ℤ, if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0
    (1 - (q : ℝ) / σ) / (q : ℝ) ≤ Z_a / Z ∧ Z_a / Z ≤ (1 + (q : ℝ) / σ) / (q : ℝ) := by
  dsimp only
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hτ : 1 ≤ σ / (q : ℝ) := (one_le_div hqR).mpr hσq
  have hsharp := (gaussian_residue_class_prob_sharp a q hq μ σ hσq).2
  have hexp : 9 * Real.exp (-π * (σ / (q : ℝ)) ^ 2) ≤ (q : ℝ) / σ := by
    have h := nine_mul_exp_neg_pi_sq_le_inv hτ
    rwa [one_div_div] at h
  have hbd : |((∑' n : ℤ, if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0) /
      (∑' n : ℤ, coeffGaussian n μ σ)) - 1 / (q : ℝ)| ≤ ((q : ℝ) / σ) / (q : ℝ) :=
    hsharp.trans (div_le_div_of_nonneg_right hexp hqR.le)
  have ⟨hlo, hhi⟩ := abs_le.mp hbd
  constructor
  · rw [sub_div]; linarith
  · rw [add_div]; linarith

/-- **Elementary unimodal residue-class probability bound** (no Fourier/Poisson input):
directly from the unimodal Riemann tile bounds, for any `q ≥ 1` and `σ > 1`, every residue
class `a mod q` has probability in `[(σ/q - 1)/(σ + 1), (σ/q + 1)/(σ - 1)]`. -/
theorem gaussian_residue_class_prob_unimodal (a : ℤ) (q : ℕ) (hq : 0 < q) (μ σ : ℝ)
    (hσ1 : 1 < σ) :
    let Z := ∑' n : ℤ, coeffGaussian n μ σ
    let Z_a := ∑' n : ℤ, if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0
    (σ / (q : ℝ) - 1) / (σ + 1) ≤ Z_a / Z ∧ Z_a / Z ≤ (σ / (q : ℝ) + 1) / (σ - 1) := by
  dsimp only
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hσpos : 0 < σ := by linarith
  have hZ := unimodal_gaussian_progression_bounds 0 μ σ 1 hσpos zero_lt_one
  have hZ_eq : (∑' k : ℤ, coeffGaussian (0 + (k : ℝ) * 1) μ σ) =
      ∑' n : ℤ, coeffGaussian n μ σ := by
    apply tsum_congr; intro k; simp
  rw [hZ_eq, div_one] at hZ
  have hZa := unimodal_gaussian_progression_bounds (a : ℝ) μ σ (q : ℝ) hσpos hqR
  rw [← residue_class_tsum_eq a q hq μ σ] at hZa
  have hZ_pos : 0 < ∑' n : ℤ, coeffGaussian n μ σ := by linarith [hZ.2.1]
  have hZa_nonneg : 0 ≤ ∑' n : ℤ,
      if (n : ZMod q) = (a : ZMod q) then coeffGaussian n μ σ else 0 := by
    apply tsum_nonneg; intro n; split_ifs
    · exact (Real.exp_pos _).le
    · rfl
  constructor
  · rw [div_le_div_iff₀ (by linarith : 0 < σ + 1) hZ_pos]
    by_cases hsign : 0 ≤ σ / (q : ℝ) - 1
    · exact mul_le_mul hZa.2.1 hZ.2.2 hZ_pos.le hZa_nonneg
    · have hneg : σ / (q : ℝ) - 1 ≤ 0 := le_of_not_ge hsign
      exact (mul_nonpos_of_nonpos_of_nonneg hneg hZ_pos.le).trans
        (mul_nonneg hZa_nonneg (by linarith : 0 ≤ σ + 1))
  · rw [div_le_div_iff₀ hZ_pos (by linarith : 0 < σ - 1)]
    exact mul_le_mul hZa.2.2 hZ.2.1 (by linarith : 0 ≤ σ - 1) (by positivity)

/-- **Single-root progression conditioning bound** combining `Cogentic.Window.conditional_progression_probability`
with the unimodal upper bound on any progression event: for a step `M > 0` and width `t ≥ 2 * M`,
the normalized conditional probability of any predicate `E` along `c + M * j` agrees with the
ideal density `(M / t) * ∑_{E} w_j` up to relative error `6 * exp(-π (t/M)^2)`. -/
theorem single_root_progression_conditioning (c M μ t : ℝ) (hM : 0 < M) (hτ : 2 ≤ t / M)
    (E : ℤ → Prop) [DecidablePred E] :
    let w := fun j : ℤ => coeffGaussian (c + M * j) μ t
    let Z := ∑' j : ℤ, w j
    let N := ∑' j : ℤ, if E j then w j else 0
    0 < Z ∧ |N / Z - (M / t) * N| ≤ 6 * Real.exp (-π * (t / M) ^ 2) * ((M / t) * N) ∧
      (M / t) * N ≤ 1 + M / t := by
  dsimp only
  have hcond := conditional_progression_probability c M μ t hM hτ E
  have htpos : 0 < t := by
    have : 0 < t / M := by linarith
    exact (div_pos_iff_of_pos_right hM).mp this
  have huni := unimodal_gaussian_progression_bounds c μ t M htpos hM
  have hw_eq : (fun j : ℤ => coeffGaussian (c + M * (j : ℝ)) μ t) =
      fun j : ℤ => coeffGaussian (c + (j : ℝ) * M) μ t := by
    ext j; ring_nf
  have hN_le : (∑' j : ℤ, if E j then coeffGaussian (c + M * j) μ t else 0) ≤
      ∑' j : ℤ, coeffGaussian (c + (j : ℝ) * M) μ t := by
    have hsub : Summable (fun j : ℤ => if E j then coeffGaussian (c + M * j) μ t else 0) :=
      Summable.of_nonneg_of_le
        (fun j => by split_ifs <;> [exact (Real.exp_pos _).le; rfl])
        (fun j => by
          rw [show c + M * (j : ℝ) = c + (j : ℝ) * M by ring]
          split_ifs <;> [exact le_rfl; exact (Real.exp_pos _).le])
        huni.1
    exact hsub.tsum_le_tsum (fun j => by
      rw [show c + M * (j : ℝ) = c + (j : ℝ) * M by ring]
      split_ifs <;> [exact le_rfl; exact (Real.exp_pos _).le]) huni.1
  have hbound : (M / t) * (∑' j : ℤ, if E j then coeffGaussian (c + M * j) μ t else 0) ≤
      1 + M / t := by
    have hmul := mul_le_mul_of_nonneg_left (hN_le.trans huni.2.2) (div_nonneg hM.le htpos.le)
    calc
      _ ≤ (M / t) * (t / M + 1) := hmul
      _ = 1 + M / t := by field_simp [hM.ne', htpos.ne']
  exact ⟨hcond.1, hcond.2, hbound⟩

end DiscreteGaussian1D

/-! ## Part 2: 2D Rectangular Mahalanobis Tile Comparison & Discarded Inner-Ellipse Mass Bounds -/

section Mahalanobis2D

/-- Explicit Cholesky/Mahalanobis coordinate map for marginal scales `T₁, T₂ > 0`,
center `(c₁, c₂)`, and correlation `ρ ∈ (-1, 1)` with `κ = √(1 - ρ^2)`.
It satisfies `‖mahalanobisCoord x‖₂^2 = (u₁^2 - 2 ρ u₁ u₂ + u₂^2) / κ^2`. -/
def mahalanobisCoord (T₁ T₂ c₁ c₂ ρ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  let κ := Real.sqrt (1 - ρ ^ 2)
  let u₁ := (x.1 - c₁) / T₁
  let u₂ := (x.2 - c₂) / T₂
  (u₁, (u₂ - ρ * u₁) / κ)

/-- Euclidean norm on `ℝ × ℝ`. -/
def euclidNorm2 (y : ℝ × ℝ) : ℝ := Real.sqrt (y.1 ^ 2 + y.2 ^ 2)

/-- Squared Mahalanobis radius equals the exact inverse-covariance quadratic form `uᵀ C⁻¹ u`. -/
theorem mahalanobis_norm_sq (T₁ T₂ c₁ c₂ ρ : ℝ) (hρ : |ρ| < 1) (x : ℝ × ℝ) :
    (euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x)) ^ 2 =
      (((x.1 - c₁) / T₁) ^ 2 - 2 * ρ * ((x.1 - c₁) / T₁) * ((x.2 - c₂) / T₂) +
        ((x.2 - c₂) / T₂) ^ 2) / (1 - ρ ^ 2) := by
  have h1ρ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      have h := (sq_lt_sq₀ (abs_nonneg ρ) zero_le_one).mpr (by simpa using hρ)
      simpa [sq_abs] using h
    linarith
  unfold euclidNorm2 mahalanobisCoord
  dsimp only
  rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt h1ρ.le]
  field_simp [h1ρ.ne']
  ring

/-- 2D correlated Gaussian weight `g(x) = exp(-π ‖y(x)‖₂^2)`. -/
def gaussian2D (T₁ T₂ c₁ c₂ ρ : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.exp (-π * (euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x)) ^ 2)

/-- Mahalanobis tile half-diameter `δ = (1 / (2 κ)) (h₁ / T₁ + h₂ / T₂)`. -/
def mahalanobisMesh (T₁ T₂ ρ h₁ h₂ : ℝ) : ℝ :=
  (h₁ / T₁ + h₂ / T₂) / (2 * Real.sqrt (1 - ρ ^ 2))

private lemma euclidNorm2_nonneg (y : ℝ × ℝ) : 0 ≤ euclidNorm2 y := Real.sqrt_nonneg _

private lemma euclidNorm2_triangle (y z : ℝ × ℝ) :
    euclidNorm2 (y.1 + z.1, y.2 + z.2) ≤ euclidNorm2 y + euclidNorm2 z := by
  unfold euclidNorm2
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  apply Real.sqrt_le_sqrt
  have hcs : (y.1 * z.1 + y.2 * z.2) ^ 2 ≤ (y.1 ^ 2 + y.2 ^ 2) * (z.1 ^ 2 + z.2 ^ 2) := by
    nlinarith [sq_nonneg (y.1 * z.2 - y.2 * z.1)]
  have hprod : y.1 * z.1 + y.2 * z.2 ≤ Real.sqrt (y.1 ^ 2 + y.2 ^ 2) * Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact le_trans (le_abs_self _) (by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hcs)
  have h1 := Real.sq_sqrt (show 0 ≤ y.1 ^ 2 + y.2 ^ 2 by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ z.1 ^ 2 + z.2 ^ 2 by positivity)
  nlinarith

private lemma euclidNorm2_sub_abs_le (y z : ℝ × ℝ) :
    |euclidNorm2 y - euclidNorm2 z| ≤ euclidNorm2 (y.1 - z.1, y.2 - z.2) := by
  rw [abs_le]
  constructor
  · have h := euclidNorm2_triangle y (z.1 - y.1, z.2 - y.2)
    have heq : (y.1 + (z.1 - y.1), y.2 + (z.2 - y.2)) = z := by ext <;> simp
    have hsym : euclidNorm2 (z.1 - y.1, z.2 - y.2) = euclidNorm2 (y.1 - z.1, y.2 - z.2) := by
      unfold euclidNorm2; congr 1; ring
    rw [heq, hsym] at h; linarith
  · have h := euclidNorm2_triangle z (y.1 - z.1, y.2 - z.2)
    have heq : (z.1 + (y.1 - z.1), z.2 + (y.2 - z.2)) = y := by ext <;> simp
    rw [heq] at h; linarith

/-- Every point in a raw centered rectangle of side lengths `(h₁, h₂)` lies within
Mahalanobis distance `δ = (1/(2κ)) (h₁/T₁ + h₂/T₂)` of the tile center. -/
theorem mahalanobis_tile_radius_lip (T₁ T₂ c₁ c₂ ρ h₁ h₂ : ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hρ : |ρ| < 1) {x x₀ : ℝ × ℝ}
    (hx₁ : |x.1 - x₀.1| ≤ h₁ / 2) (hx₂ : |x.2 - x₀.2| ≤ h₂ / 2) :
    |euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x) -
      euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x₀)| ≤ mahalanobisMesh T₁ T₂ ρ h₁ h₂ := by
  have h1ρ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      have h := (sq_lt_sq₀ (abs_nonneg ρ) zero_le_one).mpr (by simpa using hρ)
      simpa [sq_abs] using h
    linarith
  let κ := Real.sqrt (1 - ρ ^ 2)
  have hκ : 0 < κ := Real.sqrt_pos.mpr h1ρ
  let du₁ := (x.1 - x₀.1) / T₁
  let du₂ := (x.2 - x₀.2) / T₂
  have hdiff : (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x).1 - (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x₀).1 = du₁ ∧
      (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x).2 - (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x₀).2 =
        (du₂ - ρ * du₁) / κ := by
    unfold mahalanobisCoord
    dsimp only [du₁, du₂, κ]
    constructor <;> ring
  have htri := euclidNorm2_sub_abs_le (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x)
    (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x₀)
  rw [hdiff.1, hdiff.2] at htri
  have hsplit : (du₁, (du₂ - ρ * du₁) / κ) = (du₁, -ρ * du₁ / κ) + (0, du₂ / κ) := by
    ext <;> simp; ring
  have hnorm_sum : euclidNorm2 (du₁, (du₂ - ρ * du₁) / κ) ≤
      euclidNorm2 (du₁, -ρ * du₁ / κ) + euclidNorm2 (0, du₂ / κ) := by
    have := euclidNorm2_triangle (du₁, -ρ * du₁ / κ) (0, du₂ / κ)
    convert this using 2
    ext <;> simp; ring
  have hnorm1 : euclidNorm2 (du₁, -ρ * du₁ / κ) = |du₁| / κ := by
    unfold euclidNorm2
    have hsq : du₁ ^ 2 + (-ρ * du₁ / κ) ^ 2 = (du₁ / κ) ^ 2 := by
      have hκsq : κ ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt h1ρ.le
      rw [div_pow, div_pow, hκsq]
      field_simp [h1ρ.ne']
      ring
    rw [hsq, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hκ]
  have hnorm2 : euclidNorm2 (0, du₂ / κ) = |du₂| / κ := by
    unfold euclidNorm2
    rw [zero_pow (by norm_num), zero_add, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hκ]
  have hdu₁ : |du₁| ≤ (h₁ / 2) / T₁ := by
    dsimp [du₁]; rw [abs_div, abs_of_pos hT₁]; exact div_le_div_of_nonneg_right hx₁ hT₁.le
  have hdu₂ : |du₂| ≤ (h₂ / 2) / T₂ := by
    dsimp [du₂]; rw [abs_div, abs_of_pos hT₂]; exact div_le_div_of_nonneg_right hx₂ hT₂.le
  calc
    |euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x) -
        euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x₀)|
        ≤ |du₁| / κ + |du₂| / κ := htri.trans (hnorm_sum.trans (by rw [hnorm1, hnorm2]))
    _ ≤ ((h₁ / 2) / T₁) / κ + ((h₂ / 2) / T₂) / κ :=
      add_le_add (div_le_div_of_nonneg_right hdu₁ hκ.le) (div_le_div_of_nonneg_right hdu₂ hκ.le)
    _ = mahalanobisMesh T₁ T₂ ρ h₁ h₂ := by
      unfold mahalanobisMesh; dsimp only [κ]; ring

/-- Change of variables in `lintegral` for `mahalanobisCoord`: Jacobian is `T₁ * T₂ * κ`. -/
private lemma lintegral_comp_mahalanobisCoord (T₁ T₂ c₁ c₂ ρ : ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hρ : |ρ| < 1)
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : ℝ × ℝ, F (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x)) =
      ENNReal.ofReal (T₁ * T₂ * Real.sqrt (1 - ρ ^ 2)) * ∫⁻ y : ℝ × ℝ, F y := by
  have h1ρ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      have h := (sq_lt_sq₀ (abs_nonneg ρ) zero_le_one).mpr (by simpa using hρ)
      simpa [sq_abs] using h
    linarith
  let κ := Real.sqrt (1 - ρ ^ 2)
  have hκ : 0 < κ := Real.sqrt_pos.mpr h1ρ
  have hmeas_φ : Measurable (mahalanobisCoord T₁ T₂ c₁ c₂ ρ) := by
    unfold mahalanobisCoord
    fun_prop
  have hprod_lhs : (∫⁻ x : ℝ × ℝ, F (mahalanobisCoord T₁ T₂ c₁ c₂ ρ x)) =
      ∫⁻ x₁ : ℝ, ∫⁻ x₂ : ℝ, F (mahalanobisCoord T₁ T₂ c₁ c₂ ρ (x₁, x₂)) :=
    lintegral_prod _ (hF.comp hmeas_φ).aemeasurable
  have hprod_rhs : (∫⁻ y : ℝ × ℝ, F y) = ∫⁻ y₁ : ℝ, ∫⁻ y₂ : ℝ, F (y₁, y₂) :=
    lintegral_prod _ hF.aemeasurable
  rw [hprod_lhs, hprod_rhs]
  -- Evaluate inner integral over x₂ for each fixed x₁
  have hinner (x₁ : ℝ) :
      (∫⁻ x₂ : ℝ, F (mahalanobisCoord T₁ T₂ c₁ c₂ ρ (x₁, x₂))) =
        ENNReal.ofReal (T₂ * κ) * ∫⁻ y₂ : ℝ, F ((x₁ - c₁) / T₁, y₂) := by
    let u₁ := (x₁ - c₁) / T₁
    let a := (T₂ * κ)⁻¹
    let b := -(c₂ / T₂ + ρ * u₁) / κ
    have ha : a ≠ 0 := inv_ne_zero (mul_pos hT₂ hκ).ne'
    have hrew : (fun x₂ : ℝ => F (mahalanobisCoord T₁ T₂ c₁ c₂ ρ (x₁, x₂))) =
        fun x₂ : ℝ => F (u₁, a * x₂ + b) := by
      ext x₂
      unfold mahalanobisCoord
      dsimp only [u₁, a, b, κ]
      congr 2
      field_simp [hT₂.ne', hκ.ne']
      ring
    rw [hrew]
    have hmul := lintegral_mul_left_eq_self (fun y => F (u₁, y + b)) a
    -- Use MeasureTheory.Measure.lintegral_comp_mul_left_add
    have hstep1 : (∫⁻ x₂ : ℝ, F (u₁, a * x₂ + b)) =
        ENNReal.ofReal |a⁻¹| * ∫⁻ y₂ : ℝ, F (u₁, y₂ + b) := by
      have := lintegral_mul_left_eq_self (f := fun y => F (u₁, y + b)) (a := a)
      -- lintegral_mul_left_eq_self : ∫⁻ x, f (a * x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x, f x
      -- Wait: let's check direction using Measure.map_mul_left_eq_self or direct calc
      simpa using this
    rw [hstep1, lintegral_add_right_eq_self (fun y₂ => F (u₁, y₂)) b]
    congr 1
    rw [inv_inv, abs_of_pos (mul_pos hT₂ hκ)]
  simp_rw [hinner]
  rw [lintegral_const_mul _ (by
    have hmeas1 : Measurable (fun x₁ : ℝ => ∫⁻ y₂ : ℝ, F ((x₁ - c₁) / T₁, y₂)) := by
      have hm : Measurable (fun p : ℝ × ℝ => F ((p.1 - c₁) / T₁, p.2)) :=
        hF.comp (by fun_prop)
      exact hm.lintegral_prod_right'
    exact hmeas1)]
  -- Evaluate outer integral over x₁
  have houter : (∫⁻ x₁ : ℝ, ∫⁻ y₂ : ℝ, F ((x₁ - c₁) / T₁, y₂)) =
      ENNReal.ofReal T₁ * ∫⁻ y₁ : ℝ, ∫⁻ y₂ : ℝ, F (y₁, y₂) := by
    let G : ℝ → ℝ≥0∞ := fun y₁ => ∫⁻ y₂ : ℝ, F (y₁, y₂)
    have hrew : (fun x₁ : ℝ => G ((x₁ - c₁) / T₁)) = fun x₁ : ℝ => G (T₁⁻¹ * x₁ + (-c₁ / T₁)) := by
      ext x₁; congr 1; ring
    change (∫⁻ x₁ : ℝ, G ((x₁ - c₁) / T₁)) = ENNReal.ofReal T₁ * ∫⁻ y₁ : ℝ, G y₁
    rw [hrew, lintegral_mul_left_eq_self (f := fun y => G (y + (-c₁ / T₁))) (a := T₁⁻¹),
      lintegral_add_right_eq_self G (-c₁ / T₁), inv_inv, abs_of_pos hT₁]
  rw [houter, ← mul_assoc, ← ENNReal.ofReal_mul (mul_pos hT₂ hκ).le]
  congr 2
  ring

/-- Polar coordinate radial integration in `lintegral`: for any measurable `F : ℝ → ℝ≥0∞`,
`∫⁻ y : ℝ × ℝ, F ‖y‖₂ = 2π * ∫⁻ r in Ioi 0, r * F r`. -/
private lemma lintegral_radial_2D (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y : ℝ × ℝ, F (euclidNorm2 y)) =
      ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r := by
  rw [← Real.lintegral_comp_polarCoord_symm]
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  rw [htarget, Measure.restrict_prod_eq_prod_restrict]
  have hmeas_int : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • F (euclidNorm2 (polarCoord.symm p))) := by
    have h1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1) := by fun_prop
    have h2 : Measurable (fun p : ℝ × ℝ => euclidNorm2 (polarCoord.symm p)) := by
      unfold euclidNorm2 polarCoord
      simp only [PartialHomeomorph.coe_symm_mk]
      fun_prop
    exact h1.mul (hF.comp h2)
  rw [lintegral_prod _ hmeas_int.aemeasurable]
  have hcongr : ∀ r ∈ Ioi (0 : ℝ),
      (∫⁻ θ : ℝ in Ioo (-π) π, ENNReal.ofReal r • F (euclidNorm2 (polarCoord.symm (r, θ)))) =
        ENNReal.ofReal (2 * π) * (ENNReal.ofReal r * F r) := by
    intro r hr
    have hnorm (θ : ℝ) : euclidNorm2 (polarCoord.symm (r, θ)) = r := by
      unfold euclidNorm2
      change Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r
      have hsq : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
        calc
          (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2
              = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
          _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
      rw [hsq, Real.sqrt_sq (le_of_lt hr)]
    simp_rw [hnorm, smul_eq_mul]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    rw [show π - -π = 2 * π by ring, mul_comm]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
  rw [lintegral_const_mul _ (by fun_prop)]

/-- Exact 1D improper integral `∫_{Ioi a} t * exp(-π t^2) dt = exp(-π a^2) / (2π)`. -/
private lemma integral_Ioi_mul_exp_neg_pi_sq (a : ℝ) :
    (∫ t in Ioi a, t * Real.exp (-π * t ^ 2)) = Real.exp (-π * a ^ 2) / (2 * π) := by
  let F : ℝ → ℝ := fun t => -Real.exp (-π * t ^ 2) / (2 * π)
  have hderiv : ∀ t ∈ Ici a, HasDerivAt F (t * Real.exp (-π * t ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => -π * x ^ 2) (-2 * π * t) t := by
      have := (hasDerivAt_pow 2 t).const_mul (-π)
      convert this using 1; ring
    have h2 : HasDerivAt (fun x : ℝ => -Real.exp (-π * x ^ 2) / (2 * π))
        (-(Real.exp (-π * t ^ 2) * (-2 * π * t)) / (2 * π)) t :=
      ((h1.exp).neg).div_const (2 * π)
    convert h2 using 1
    field_simp [Real.pi_pos.ne']
    ring
  have hnonneg : ∀ t ∈ Ioi a, 0 ≤ t * Real.exp (-π * t ^ 2) → True := fun _ _ _ => trivial
  have htend : Tendsto F atTop (𝓝 0) := by
    dsimp [F]
    have hsq : Tendsto (fun t : ℝ => π * t ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop Real.pi_pos (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(π * t ^ 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsq)
    have hrew : (fun t : ℝ => -Real.exp (-π * t ^ 2) / (2 * π)) =
        fun t : ℝ => -Real.exp (-(π * t ^ 2)) / (2 * π) := by
      ext t; rw [neg_mul]
    rw [hrew]
    simpa using (hexp.neg).div_const (2 * π)
  have hint : IntegrableOn (fun t : ℝ => t * Real.exp (-π * t ^ 2)) (Ioi a) volume := by
    have hdom : IntegrableOn (fun t : ℝ => Real.exp (-(π / 2) * t ^ 2)) (Ioi a) volume :=
      (integrable_exp_neg_mul_sq (by positivity)).integrableOn
    have hdom2 : IntegrableOn (fun t : ℝ => Real.exp (-(π / 2) * t ^ 2) * 1) (Ioi a) volume := by
      simpa using hdom
    refine Integrable.mono' (hdom.const_mul (1 + |a| + 1)) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp_split : Real.exp (-π * t ^ 2) =
        Real.exp (-(π / 2) * t ^ 2) * Real.exp (-(π / 2) * t ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hbound : |t| * Real.exp (-(π / 2) * t ^ 2) ≤ 1 := by
      have h1 : (π / 2) * t ^ 2 + 1 ≤ Real.exp ((π / 2) * t ^ 2) := by
        linarith [Real.add_one_le_exp ((π / 2) * t ^ 2)]
      have h2 : |t| ≤ (π / 2) * t ^ 2 + 1 := by
        have hpi : 3 < π := Real.pi_gt_three
        nlinarith [sq_nonneg (|t| - 1), sq_abs t]
      rw [neg_mul, Real.exp_neg]
      have hpos : 0 < Real.exp ((π / 2) * t ^ 2) := Real.exp_pos _
      calc
        |t| * (Real.exp ((π / 2) * t ^ 2))⁻¹ ≤ Real.exp ((π / 2) * t ^ 2) * (Real.exp ((π / 2) * t ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (h2.trans h1) (inv_nonneg.mpr hpos.le)
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    calc
      |t| * Real.exp (-π * t ^ 2)
          = (|t| * Real.exp (-(π / 2) * t ^ 2)) * Real.exp (-(π / 2) * t ^ 2) := by
        rw [hexp_split]; ring
      _ ≤ 1 * Real.exp (-(π / 2) * t ^ 2) :=
        mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
      _ ≤ (1 + |a| + 1) * Real.exp (-(π / 2) * t ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg a]) (Real.exp_pos _).le
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  dsimp [F] at hval
  linarith

/-- Exact radial upper integral `2π ∫_{0}^∞ r exp(-π (max (r - δ) 0)^2) dr = 1 + π δ + π δ^2`. -/
private lemma lintegral_radial_upper (δ : ℝ) (hδ : 0 ≤ δ) :
    (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Real.exp (-π * (max (euclidNorm2 y - δ) 0) ^ 2))) =
      ENNReal.ofReal (1 + π * δ + π * δ ^ 2) := by
  have hmeas : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-π * (max (r - δ) 0) ^ 2))) := by
    fun_prop
  rw [lintegral_radial_2D _ hmeas]
  let g : ℝ → ℝ := fun r => r * Real.exp (-π * (max (r - δ) 0) ^ 2)
  have hrew : ∀ r ∈ Ioi (0 : ℝ),
      ENNReal.ofReal r * ENNReal.ofReal (Real.exp (-π * (max (r - δ) 0) ^ 2)) =
        ENNReal.ofReal (g r) := by
    intro r hr
    rw [← ENNReal.ofReal_mul (le_of_lt hr)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hrew]
  -- Split Ioi 0 = Ioc 0 δ ∪ Ioi δ
  have hunion : Ioi (0 : ℝ) = Ioc 0 δ ∪ Ioi δ := (Ioc_union_Ioi_eq_Ioi hδ).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) δ) (Ioi δ) := Ioc_disjoint_Ioi_same
  rw [hunion, lintegral_union measurableSet_Ioi hdisj]
  -- Part 1: on Ioc 0 δ, g r = r
  have hpart1 : (∫⁻ r in Ioc (0 : ℝ) δ, ENNReal.ofReal (g r)) = ENNReal.ofReal (δ ^ 2 / 2) := by
    have hcongr1 : ∀ r ∈ Ioc (0 : ℝ) δ, ENNReal.ofReal (g r) = ENNReal.ofReal r := by
      intro r hr
      dsimp [g]
      rw [max_eq_right (sub_nonpos.mpr hr.2), zero_pow (by norm_num), mul_zero, Real.exp_zero, mul_one]
    rw [setLIntegral_congr_fun measurableSet_Ioc hcongr1]
    rw [← ofReal_integral_eq_lintegral_ofReal (continuousOn_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Eventually.of_forall (fun r => by exact id) |> fun _ => by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr; exact hr.1.le)]
    rw [← intervalIntegral.integral_of_le hδ, integral_id]
    congr 1; ring
  -- Part 2: on Ioi δ, substitute t = r - δ
  have hpart2 : (∫⁻ r in Ioi δ, ENNReal.ofReal (g r)) =
      ENNReal.ofReal (1 / (2 * π) + δ / 2) := by
    have hcongr2 : ∀ r ∈ Ioi δ,
        ENNReal.ofReal (g r) = ENNReal.ofReal (r * Real.exp (-π * (r - δ) ^ 2)) := by
      intro r hr
      dsimp [g]
      rw [max_eq_left (sub_nonneg.mpr hr.le)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr2]
    have hshift : (∫⁻ r in Ioi δ, ENNReal.ofReal (r * Real.exp (-π * (r - δ) ^ 2))) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((t + δ) * Real.exp (-π * t ^ 2)) := by
      have h := lintegral_add_right_eq_self (fun t => (Ioi (0 : ℝ)).indicator
        (fun s => ENNReal.ofReal ((s + δ) * Real.exp (-π * s ^ 2))) t) (-δ)
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
      rw [← h]
      apply lintegral_congr
      intro r
      by_cases hr : δ < r
      · have hr' : 0 < r + -δ := by linarith
        simp [Set.indicator_apply, hr, hr', show r + -δ + δ = r by ring,
          show r + -δ = r - δ by ring]
      · have hr' : ¬ (0 < r + -δ) := by linarith
        simp [Set.indicator_apply, hr, hr']
    rw [hshift]
    have hadd : ∀ t ∈ Ioi (0 : ℝ),
        ENNReal.ofReal ((t + δ) * Real.exp (-π * t ^ 2)) =
          ENNReal.ofReal (t * Real.exp (-π * t ^ 2)) +
          ENNReal.ofReal (δ * Real.exp (-π * t ^ 2)) := by
      intro t ht
      rw [add_mul, ENNReal.ofReal_add (mul_nonneg ht.le (Real.exp_pos _).le)
        (mul_nonneg hδ (Real.exp_pos _).le)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hadd,
      lintegral_add_left (by fun_prop)]
    -- First sub-integral: ∫_{Ioi 0} t exp(-π t^2) = 1 / (2π)
    have hsub1 : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * Real.exp (-π * t ^ 2))) =
        ENNReal.ofReal (1 / (2 * π)) := by
      have hint1 : IntegrableOn (fun t : ℝ => t * Real.exp (-π * t ^ 2)) (Ioi 0) volume := by
        have hdom : IntegrableOn (fun t : ℝ => Real.exp (-(π / 2) * t ^ 2)) (Ioi 0) volume :=
          (integrable_exp_neg_mul_sq (by positivity)).integrableOn
        refine Integrable.mono' hdom (by fun_prop) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
        have hexp_split : Real.exp (-π * t ^ 2) =
            Real.exp (-(π / 2) * t ^ 2) * Real.exp (-(π / 2) * t ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
        have hbound : t * Real.exp (-(π / 2) * t ^ 2) ≤ 1 := by
          have h1 : (π / 2) * t ^ 2 + 1 ≤ Real.exp ((π / 2) * t ^ 2) := by
            linarith [Real.add_one_le_exp ((π / 2) * t ^ 2)]
          have h2 : t ≤ (π / 2) * t ^ 2 + 1 := by
            nlinarith [Real.pi_gt_three, sq_nonneg (t - 1)]
          rw [neg_mul, Real.exp_neg]
          have hpos := Real.exp_pos ((π / 2) * t ^ 2)
          calc
            t * (Real.exp ((π / 2) * t ^ 2))⁻¹ ≤ Real.exp ((π / 2) * t ^ 2) * (Real.exp ((π / 2) * t ^ 2))⁻¹ :=
              mul_le_mul_of_nonneg_right (h2.trans h1) (inv_nonneg.mpr hpos.le)
            _ = 1 := mul_inv_cancel₀ hpos.ne'
        calc
          t * Real.exp (-π * t ^ 2)
              = (t * Real.exp (-(π / 2) * t ^ 2)) * Real.exp (-(π / 2) * t ^ 2) := by
            rw [hexp_split]; ring
          _ ≤ 1 * Real.exp (-(π / 2) * t ^ 2) :=
            mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
          _ = Real.exp (-(π / 2) * t ^ 2) := one_mul _
      rw [← ofReal_integral_eq_lintegral_ofReal hint1 (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg ht.le (Real.exp_pos _).le)]
      rw [integral_Ioi_mul_exp_neg_pi_sq 0]
      simp
    -- Second sub-integral: ∫_{Ioi 0} δ exp(-π t^2) = δ / 2
    have hsub2 : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (δ * Real.exp (-π * t ^ 2))) =
        ENNReal.ofReal (δ / 2) := by
      have hint2 : IntegrableOn (fun t : ℝ => δ * Real.exp (-π * t ^ 2)) (Ioi 0) volume :=
        ((integrable_exp_neg_mul_sq Real.pi_pos).const_mul δ).integrableOn
      rw [← ofReal_integral_eq_lintegral_ofReal hint2 (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
        exact mul_nonneg hδ (Real.exp_pos _).le)]
      rw [integral_const_mul, integral_gaussian_Ioi π, div_self Real.pi_pos.ne', Real.sqrt_one]
      congr 1; ring
    rw [hsub1, hsub2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hpart1, hpart2, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp [Real.pi_pos.ne']
  ring

/-- Radial lower integral bound `1 - π δ - π δ^2 ≤ 2π ∫_{0}^∞ r exp(-π (r + δ)^2) dr`. -/
private lemma lintegral_radial_lower (δ : ℝ) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (1 - π * δ - π * δ ^ 2) ≤
      ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Real.exp (-π * (euclidNorm2 y + δ) ^ 2)) := by
  have hmeas : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-π * (r + δ) ^ 2))) := by
    fun_prop
  rw [lintegral_radial_2D _ hmeas]
  have hrew : ∀ r ∈ Ioi (0 : ℝ),
      ENNReal.ofReal r * ENNReal.ofReal (Real.exp (-π * (r + δ) ^ 2)) =
        ENNReal.ofReal (r * Real.exp (-π * (r + δ) ^ 2)) := by
    intro r hr
    rw [← ENNReal.ofReal_mul (le_of_lt hr)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hrew]
  -- Shift t = r + δ
  have hshift : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * Real.exp (-π * (r + δ) ^ 2))) =
      ∫⁻ t in Ioi δ, ENNReal.ofReal ((t - δ) * Real.exp (-π * t ^ 2)) := by
    have h := lintegral_add_right_eq_self (fun t => (Ioi δ).indicator
      (fun s => ENNReal.ofReal ((s - δ) * Real.exp (-π * s ^ 2))) t) δ
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
    rw [← h]
    apply lintegral_congr
    intro r
    by_cases hr : 0 < r
    · have hr' : δ < r + δ := by linarith
      simp [Set.indicator_apply, hr, hr']
    · have hr' : ¬ (δ < r + δ) := by linarith
      simp [Set.indicator_apply, hr, hr']
  rw [hshift]
  have hint_t : IntegrableOn (fun t : ℝ => t * Real.exp (-π * t ^ 2)) (Ioi δ) volume := by
    have hdom : IntegrableOn (fun t : ℝ => Real.exp (-(π / 2) * t ^ 2)) (Ioi δ) volume :=
      (integrable_exp_neg_mul_sq (by positivity)).integrableOn
    refine Integrable.mono' hdom (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hδ.trans_lt ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht0, abs_of_pos (Real.exp_pos _)]
    have hexp_split : Real.exp (-π * t ^ 2) =
        Real.exp (-(π / 2) * t ^ 2) * Real.exp (-(π / 2) * t ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hbound : t * Real.exp (-(π / 2) * t ^ 2) ≤ 1 := by
      have h1 : (π / 2) * t ^ 2 + 1 ≤ Real.exp ((π / 2) * t ^ 2) := by
        linarith [Real.add_one_le_exp ((π / 2) * t ^ 2)]
      have h2 : t ≤ (π / 2) * t ^ 2 + 1 := by nlinarith [Real.pi_gt_three, sq_nonneg (t - 1)]
      rw [neg_mul, Real.exp_neg]
      have hpos := Real.exp_pos ((π / 2) * t ^ 2)
      calc
        t * (Real.exp ((π / 2) * t ^ 2))⁻¹ ≤ Real.exp ((π / 2) * t ^ 2) * (Real.exp ((π / 2) * t ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (h2.trans h1) (inv_nonneg.mpr hpos.le)
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    calc
      t * Real.exp (-π * t ^ 2)
          = (t * Real.exp (-(π / 2) * t ^ 2)) * Real.exp (-(π / 2) * t ^ 2) := by
        rw [hexp_split]; ring
      _ ≤ 1 * Real.exp (-(π / 2) * t ^ 2) :=
        mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
      _ = Real.exp (-(π / 2) * t ^ 2) := one_mul _
  have hint_c : IntegrableOn (fun t : ℝ => δ * Real.exp (-π * t ^ 2)) (Ioi δ) volume :=
    ((integrable_exp_neg_mul_sq Real.pi_pos).const_mul δ).integrableOn
  have hint_sub : IntegrableOn (fun t : ℝ => (t - δ) * Real.exp (-π * t ^ 2)) (Ioi δ) volume := by
    simpa [sub_mul] using hint_t.sub hint_c
  rw [← ofReal_integral_eq_lintegral_ofReal hint_sub (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (sub_nonneg.mpr ht.le) (Real.exp_pos _).le)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hval : (∫ t in Ioi δ, (t - δ) * Real.exp (-π * t ^ 2)) =
      (∫ t in Ioi δ, t * Real.exp (-π * t ^ 2)) - (∫ t in Ioi δ, δ * Real.exp (-π * t ^ 2)) := by
    simp_rw [sub_mul]
    exact integral_sub hint_t hint_c
  rw [hval, integral_Ioi_mul_exp_neg_pi_sq δ, integral_const_mul]
  have htail : (∫ t in Ioi δ, Real.exp (-π * t ^ 2)) ≤ 1 / 2 := by
    calc
      (∫ t in Ioi δ, Real.exp (-π * t ^ 2))
          ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-π * t ^ 2) :=
        setIntegral_mono_set (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn
          (Eventually.of_forall fun _ => (Real.exp_pos _).le)
          (Eventually.of_forall (Ioi_subset_Ioi hδ))
      _ = 1 / 2 := by
        rw [integral_gaussian_Ioi π, div_self Real.pi_pos.ne', Real.sqrt_one]
  have hexp_lo : 1 - π * δ ^ 2 ≤ Real.exp (-π * δ ^ 2) := by
    have := Real.add_one_le_exp (-π * δ ^ 2)
    linarith
  have hmul_tail : δ * (∫ t in Ioi δ, Real.exp (-π * t ^ 2)) ≤ δ / 2 := by
    nlinarith
  have h1 : (1 - π * δ ^ 2) / (2 * π) - δ / 2 ≤
      Real.exp (-π * δ ^ 2) / (2 * π) - δ * ∫ t in Ioi δ, Real.exp (-π * t ^ 2) := by
    have := div_le_div_of_nonneg_right hexp_lo (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π)
  calc
    1 - π * δ - π * δ ^ 2 = 2 * π * ((1 - π * δ ^ 2) / (2 * π) - δ / 2) := by
      field_simp [Real.pi_pos.ne']; ring
    _ ≤ _ := h2

/-- Raw rectangular tiles centered at a translated 2D lattice partition `ℝ × ℝ` pairwise disjointly. -/
private def latticeTile (x₀ : ℝ × ℝ) (h₁ h₂ : ℝ) (k : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Ico (x₀.1 + (k.1 : ℝ) * h₁ - h₁ / 2) (x₀.1 + (k.1 : ℝ) * h₁ + h₁ / 2) ×ˢ
    Ico (x₀.2 + (k.2 : ℝ) * h₂ - h₂ / 2) (x₀.2 + (k.2 : ℝ) * h₂ + h₂ / 2)

private lemma latticeTile_measurable (x₀ : ℝ × ℝ) (h₁ h₂ : ℝ) (k : ℤ × ℤ) :
    MeasurableSet (latticeTile x₀ h₁ h₂ k) :=
  measurableSet_Ico.prod measurableSet_Ico

private lemma latticeTile_volume (x₀ : ℝ × ℝ) {h₁ h₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (k : ℤ × ℤ) :
    volume (latticeTile x₀ h₁ h₂ k) = ENNReal.ofReal (h₁ * h₂) := by
  unfold latticeTile
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico,
    ← ENNReal.ofReal_mul (by linarith)]
  congr 1; ring

private lemma latticeTile_iUnion_eq_univ (x₀ : ℝ × ℝ) {h₁ h₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    (⋃ k : ℤ × ℤ, latticeTile x₀ h₁ h₂ k) = Set.univ := by
  ext ⟨x₁, x₂⟩
  simp only [mem_iUnion, mem_univ, iff_true]
  refine ⟨(⌊(x₁ - x₀.1) / h₁ + 1 / 2⌋, ⌊(x₂ - x₀.2) / h₂ + 1 / 2⌋), ?_, ?_⟩
  · have hlo := Int.floor_le ((x₁ - x₀.1) / h₁ + 1 / 2)
    have hhi := Int.lt_floor_add_one ((x₁ - x₀.1) / h₁ + 1 / 2)
    have h1 := mul_le_mul_of_nonneg_right hlo hh₁.le
    have h2 := mul_lt_mul_of_pos_right hhi hh₁
    have heq : ((x₁ - x₀.1) / h₁ + 1 / 2) * h₁ = x₁ - x₀.1 + h₁ / 2 := by
      field_simp [hh₁.ne']; ring
    rw [heq] at h1 h2
    exact ⟨by linarith, by linarith⟩
  · have hlo := Int.floor_le ((x₂ - x₀.2) / h₂ + 1 / 2)
    have hhi := Int.lt_floor_add_one ((x₂ - x₀.2) / h₂ + 1 / 2)
    have h1 := mul_le_mul_of_nonneg_right hlo hh₂.le
    have h2 := mul_lt_mul_of_pos_right hhi hh₂
    have heq : ((x₂ - x₀.2) / h₂ + 1 / 2) * h₂ = x₂ - x₀.2 + h₂ / 2 := by
      field_simp [hh₂.ne']; ring
    rw [heq] at h1 h2
    exact ⟨by linarith, by linarith⟩

private lemma latticeTile_pairwiseDisjoint (x₀ : ℝ × ℝ) {h₁ h₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    Pairwise (Disjoint on latticeTile x₀ h₁ h₂) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  intro ⟨x₁, x₂⟩ hk hl
  apply hkl
  have huniq : ∀ (a b c : ℝ) (hc : 0 < c) (i j : ℤ),
      a + (i : ℝ) * c - c / 2 ≤ b → b < a + (i : ℝ) * c + c / 2 →
      a + (j : ℝ) * c - c / 2 ≤ b → b < a + (j : ℝ) * c + c / 2 → i = j := by
    intro a b c hc i j hi1 hi2 hj1 hj2
    have h1 : ((i : ℝ) - (j : ℝ)) * c < c := by linarith
    have h2 : ((j : ℝ) - (i : ℝ)) * c < c := by linarith
    have h1' : (i : ℝ) - (j : ℝ) < 1 := by nlinarith
    have h2' : (j : ℝ) - (i : ℝ) < 1 := by nlinarith
    have hi : i < j + 1 := by exact_mod_cast (show (i : ℝ) < (j : ℝ) + 1 by linarith)
    have hj : j < i + 1 := by exact_mod_cast (show (j : ℝ) < (i : ℝ) + 1 by linarith)
    omega
  ext
  · exact huniq x₀.1 x₁ h₁ hh₁ k.1 l.1 hk.1.1 hk.1.2 hl.1.1 hl.1.2
  · exact huniq x₀.2 x₂ h₂ hh₂ k.2 l.2 hk.2.1 hk.2.2 hl.2.1 hl.2.2

/-- **2D rectangular Mahalanobis tile comparison** (from `keybreak-gaussian-variation.md`):
for any marginal scales `T₁, T₂ > 0`, center `(c₁, c₂)`, correlation `|ρ| < 1`, lattice spacings
`h₁, h₂ > 0`, and translate `x₀ ∈ ℝ × ℝ`, the full lattice Gaussian mass `Z_lat` satisfies
`1 - π δ - π δ^2 ≤ h₁ h₂ Z_lat / Z ≤ 1 + π δ + π δ^2`, where `Z = T₁ T₂ √(1 - ρ^2)` and
`δ = (1/(2κ)) (h₁/T₁ + h₂/T₂)`. -/
theorem mahalanobis_2d_lattice_mass_bounds (T₁ T₂ c₁ c₂ ρ h₁ h₂ : ℝ) (x₀ : ℝ × ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hρ : |ρ| < 1) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    let Z := T₁ * T₂ * Real.sqrt (1 - ρ ^ 2)
    let δ := mahalanobisMesh T₁ T₂ ρ h₁ h₂
    let lat : ℤ × ℤ → ℝ × ℝ := fun k => (x₀.1 + (k.1 : ℝ) * h₁, x₀.2 + (k.2 : ℝ) * h₂)
    let g := fun k : ℤ × ℤ => gaussian2D T₁ T₂ c₁ c₂ ρ (lat k)
    Summable g ∧
      1 - π * δ - π * δ ^ 2 ≤ (h₁ * h₂ * (∑' k : ℤ × ℤ, g k)) / Z ∧
      (h₁ * h₂ * (∑' k : ℤ × ℤ, g k)) / Z ≤ 1 + π * δ + π * δ ^ 2 := by
  dsimp only
  have h1ρ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      have h := (sq_lt_sq₀ (abs_nonneg ρ) zero_le_one).mpr (by simpa using hρ)
      simpa [sq_abs] using h
    linarith
  let κ := Real.sqrt (1 - ρ ^ 2)
  have hκ : 0 < κ := Real.sqrt_pos.mpr h1ρ
  let Z := T₁ * T₂ * κ
  have hZ : 0 < Z := by positivity
  let δ := mahalanobisMesh T₁ T₂ ρ h₁ h₂
  have hδ : 0 ≤ δ := by unfold δ mahalanobisMesh; positivity
  let lat : ℤ × ℤ → ℝ × ℝ := fun k => (x₀.1 + (k.1 : ℝ) * h₁, x₀.2 + (k.2 : ℝ) * h₂)
  let g := fun k : ℤ × ℤ => gaussian2D T₁ T₂ c₁ c₂ ρ (lat k)
  let φ := mahalanobisCoord T₁ T₂ c₁ c₂ ρ
  let f_lo : ℝ × ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-π * (euclidNorm2 y + δ) ^ 2))
  let f_hi : ℝ × ℝ → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (Real.exp (-π * (max (euclidNorm2 y - δ) 0) ^ 2))
  have hf_lo_meas : Measurable f_lo := by unfold f_lo euclidNorm2; fun_prop
  have hf_hi_meas : Measurable f_hi := by unfold f_hi euclidNorm2; fun_prop
  -- Pointwise comparison on each tile
  have htile_cmp (k : ℤ × ℤ) (x : ℝ × ℝ) (hx : x ∈ latticeTile x₀ h₁ h₂ k) :
      f_lo (φ x) ≤ ENNReal.ofReal (g k) ∧ ENNReal.ofReal (g k) ≤ f_hi (φ x) := by
    have hx₁ : |x.1 - (lat k).1| ≤ h₁ / 2 := by
      rw [abs_le]; dsimp [lat]
      exact ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
    have hx₂ : |x.2 - (lat k).2| ≤ h₂ / 2 := by
      rw [abs_le]; dsimp [lat]
      exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
    have hlip := mahalanobis_tile_radius_lip T₁ T₂ c₁ c₂ ρ h₁ h₂ hT₁ hT₂ hρ hx₁ hx₂
    have ⟨hlo, hhi⟩ := abs_le.mp hlip
    constructor
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hrad : euclidNorm2 (φ (lat k)) ≤ euclidNorm2 (φ x) + δ := by linarith
      have hsq : (euclidNorm2 (φ (lat k))) ^ 2 ≤ (euclidNorm2 (φ x) + δ) ^ 2 :=
        pow_le_pow_left₀ (euclidNorm2_nonneg _) hrad 2
      nlinarith [Real.pi_pos]
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hrad : max (euclidNorm2 (φ x) - δ) 0 ≤ euclidNorm2 (φ (lat k)) :=
        max_le (by linarith) (euclidNorm2_nonneg _)
      have hsq : (max (euclidNorm2 (φ x) - δ) 0) ^ 2 ≤ (euclidNorm2 (φ (lat k))) ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) hrad 2
      nlinarith [Real.pi_pos]
  -- Integrate over each tile and sum over k ∈ ℤ × ℤ
  have hlo_tile (k : ℤ × ℤ) :
      (∫⁻ x in latticeTile x₀ h₁ h₂ k, f_lo (φ x)) ≤
        ENNReal.ofReal (h₁ * h₂) * ENNReal.ofReal (g k) := by
    calc
      (∫⁻ x in latticeTile x₀ h₁ h₂ k, f_lo (φ x))
          ≤ ∫⁻ _x in latticeTile x₀ h₁ h₂ k, ENNReal.ofReal (g k) :=
        setLIntegral_mono' (latticeTile_measurable x₀ h₁ h₂ k) fun x hx => (htile_cmp k x hx).1
      _ = ENNReal.ofReal (h₁ * h₂) * ENNReal.ofReal (g k) := by
        rw [setLIntegral_const, latticeTile_volume x₀ hh₁ hh₂ k, mul_comm]
  have hhi_tile (k : ℤ × ℤ) :
      ENNReal.ofReal (h₁ * h₂) * ENNReal.ofReal (g k) ≤
        ∫⁻ x in latticeTile x₀ h₁ h₂ k, f_hi (φ x) := by
    calc
      ENNReal.ofReal (h₁ * h₂) * ENNReal.ofReal (g k)
          = ∫⁻ _x in latticeTile x₀ h₁ h₂ k, ENNReal.ofReal (g k) := by
        rw [setLIntegral_const, latticeTile_volume x₀ hh₁ hh₂ k, mul_comm]
      _ ≤ ∫⁻ x in latticeTile x₀ h₁ h₂ k, f_hi (φ x) :=
        setLIntegral_mono' (latticeTile_measurable x₀ h₁ h₂ k) fun x hx => (htile_cmp k x hx).2
  have hsum_lo : (∫⁻ x : ℝ × ℝ, f_lo (φ x)) ≤
      ENNReal.ofReal (h₁ * h₂) * ∑' k : ℤ × ℤ, ENNReal.ofReal (g k) := by
    rw [← setLIntegral_univ, ← latticeTile_iUnion_eq_univ x₀ hh₁ hh₂,
      lintegral_iUnion (latticeTile_measurable x₀ h₁ h₂)
        (latticeTile_pairwiseDisjoint x₀ hh₁ hh₂), ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hlo_tile
  have hsum_hi : ENNReal.ofReal (h₁ * h₂) * (∑' k : ℤ × ℤ, ENNReal.ofReal (g k)) ≤
      ∫⁻ x : ℝ × ℝ, f_hi (φ x) := by
    rw [← setLIntegral_univ, ← latticeTile_iUnion_eq_univ x₀ hh₁ hh₂,
      lintegral_iUnion (latticeTile_measurable x₀ h₁ h₂)
        (latticeTile_pairwiseDisjoint x₀ hh₁ hh₂), ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hhi_tile
  -- Apply Jacobian change of variables and radial integrals
  rw [lintegral_comp_mahalanobisCoord T₁ T₂ c₁ c₂ ρ hT₁ hT₂ hρ f_lo hf_lo_meas] at hsum_lo
  rw [lintegral_comp_mahalanobisCoord T₁ T₂ c₁ c₂ ρ hT₁ hT₂ hρ f_hi hf_hi_meas,
    lintegral_radial_upper δ hδ] at hsum_hi
  have hlo_bound : ENNReal.ofReal Z * ENNReal.ofReal (1 - π * δ - π * δ ^ 2) ≤
      ENNReal.ofReal (h₁ * h₂) * ∑' k : ℤ × ℤ, ENNReal.ofReal (g k) :=
    (mul_le_mul_left' (lintegral_radial_lower δ hδ) _).trans hsum_lo
  -- Deduce finiteness and Summable g
  have hfinite : (∑' k : ℤ × ℤ, ENNReal.ofReal (g k)) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (mul_pos hh₁ hh₂)).ne'] at hsum_hi
    have hlt : ENNReal.ofReal Z * ENNReal.ofReal (1 + π * δ + π * δ ^ 2) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    exact (not_le_of_gt hlt) hsum_hi
  have hg_nonneg (k : ℤ × ℤ) : 0 ≤ g k := (Real.exp_pos _).le
  have hsumm : Summable g := by
    have h := ENNReal.summable_toReal hfinite
    simpa only [ENNReal.toReal_ofReal (hg_nonneg _)] using h
  have htsum_eq : (∑' k : ℤ × ℤ, ENNReal.ofReal (g k)) = ENNReal.ofReal (∑' k : ℤ × ℤ, g k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hg_nonneg hsumm]
  rw [htsum_eq, ← ENNReal.ofReal_mul (mul_pos hh₁ hh₂).le, ← ENNReal.ofReal_mul hZ.le] at hsum_hi
  rw [htsum_eq, ← ENNReal.ofReal_mul (mul_pos hh₁ hh₂).le] at hlo_bound
  have hupper_real : h₁ * h₂ * (∑' k : ℤ × ℤ, g k) ≤ Z * (1 + π * δ + π * δ ^ 2) := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum_hi
  have hlower_real : Z * (1 - π * δ - π * δ ^ 2) ≤ h₁ * h₂ * (∑' k : ℤ × ℤ, g k) := by
    by_cases hpos : 0 ≤ 1 - π * δ - π * δ ^ 2
    · rw [← ENNReal.ofReal_mul hZ.le] at hlo_bound
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (mul_pos hh₁ hh₂).le (tsum_nonneg hg_nonneg))).mp hlo_bound
    · have hneg : 1 - π * δ - π * δ ^ 2 ≤ 0 := le_of_not_ge hpos
      exact (mul_nonpos_of_nonneg_of_nonpos hZ.le hneg).trans
        (mul_nonneg (mul_pos hh₁ hh₂).le (tsum_nonneg hg_nonneg))
  refine ⟨hsumm, ?_, ?_⟩
  · rw [le_div_iff₀ hZ, mul_comm]; exact hlower_real
  · rw [div_le_iff₀ hZ, mul_comm]; exact hupper_real

/-- In particular, whenever the Mahalanobis mesh satisfies `δ ≤ 1 / 10`, the full 2D lattice
mass satisfies `Z_lat ≥ Z / (2 * h₁ * h₂)` (matching `keybreak-gaussian-variation.md`). -/
theorem mahalanobis_2d_lattice_mass_half (T₁ T₂ c₁ c₂ ρ h₁ h₂ : ℝ) (x₀ : ℝ × ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hρ : |ρ| < 1) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (hδ : mahalanobisMesh T₁ T₂ ρ h₁ h₂ ≤ 1 / 10) :
    let Z := T₁ * T₂ * Real.sqrt (1 - ρ ^ 2)
    let lat : ℤ × ℤ → ℝ × ℝ := fun k => (x₀.1 + (k.1 : ℝ) * h₁, x₀.2 + (k.2 : ℝ) * h₂)
    Z / (2 * h₁ * h₂) ≤ ∑' k : ℤ × ℤ, gaussian2D T₁ T₂ c₁ c₂ ρ (lat k) := by
  dsimp only
  have h1ρ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      have h := (sq_lt_sq₀ (abs_nonneg ρ) zero_le_one).mpr (by simpa using hρ)
      simpa [sq_abs] using h
    linarith
  have hZ : 0 < T₁ * T₂ * Real.sqrt (1 - ρ ^ 2) := by positivity
  have hmain := (mahalanobis_2d_lattice_mass_bounds T₁ T₂ c₁ c₂ ρ h₁ h₂ x₀ hT₁ hT₂ hρ hh₁ hh₂).2.1
  have hδ0 : 0 ≤ mahalanobisMesh T₁ T₂ ρ h₁ h₂ := by unfold mahalanobisMesh; positivity
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hhalf : (1 / 2 : ℝ) ≤ 1 - π * mahalanobisMesh T₁ T₂ ρ h₁ h₂ -
      π * (mahalanobisMesh T₁ T₂ ρ h₁ h₂) ^ 2 := by
    nlinarith [sq_nonneg (mahalanobisMesh T₁ T₂ ρ h₁ h₂)]
  have hge := hhalf.trans hmain
  rw [le_div_iff₀ hZ] at hge
  rw [div_le_iff₀ (by positivity : 0 < 2 * h₁ * h₂)]
  nlinarith

/-- **Continuous discarded inner-ellipse mass bound** `O(r₀^2)`:
in Mahalanobis coordinates, the Gaussian mass inside the disk `‖y‖₂ < r₀` is at most `π * r₀^2`. -/
theorem continuous_inner_ellipse_mass_le (r₀ : ℝ) (hr₀ : 0 ≤ r₀) :
    (∫⁻ y : ℝ × ℝ, if euclidNorm2 y < r₀ then
        ENNReal.ofReal (Real.exp (-π * (euclidNorm2 y) ^ 2)) else 0) ≤
      ENNReal.ofReal (π * r₀ ^ 2) := by
  have hle : ∀ y : ℝ × ℝ,
      (if euclidNorm2 y < r₀ then ENNReal.ofReal (Real.exp (-π * (euclidNorm2 y) ^ 2)) else 0) ≤
        if euclidNorm2 y < r₀ then 1 else 0 := by
    intro y
    split_ifs
    · exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg (euclidNorm2 y)]))
    · exact le_rfl
  refine (lintegral_mono hle).trans ?_
  let F : ℝ → ℝ≥0∞ := fun r => if r < r₀ then 1 else 0
  have hF : Measurable F := Measurable.ite measurableSet_Iio measurable_const measurable_const
  change (∫⁻ y : ℝ × ℝ, F (euclidNorm2 y)) ≤ ENNReal.ofReal (π * r₀ ^ 2)
  rw [lintegral_radial_2D F hF]
  have hsub : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r) =
      ∫⁻ r in Ioo (0 : ℝ) r₀, ENNReal.ofReal r := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro r
    dsimp [F]
    by_cases h1 : 0 < r <;> by_cases h2 : r < r₀ <;>
      simp [Set.indicator_apply, h1, h2]
  rw [hsub, ← ofReal_integral_eq_lintegral_ofReal
    (continuousOn_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr; exact hr.1.le)]
  rw [MeasureTheory.integral_Ioo_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr₀,
    integral_id, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  ring_nf; exact le_rfl

/-- **Discrete 2D lattice discarded inner-ellipse mass bound** `O((r₀ + δ)^2)`:
for any Mahalanobis mesh `δ ≤ 1 / 10` and inner cutoff `r₀ ≥ 0`, the discrete Gaussian mass
on lattice points with Mahalanobis radius `< r₀` divided by the full lattice mass `Z_lat` is
at most `2 * π * (r₀ + δ)^2`. -/
theorem mahalanobis_2d_inner_ellipse_mass_le (T₁ T₂ c₁ c₂ ρ h₁ h₂ : ℝ) (x₀ : ℝ × ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hρ : |ρ| < 1) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (hδ : mahalanobisMesh T₁ T₂ ρ h₁ h₂ ≤ 1 / 10) (r₀ : ℝ) (hr₀ : 0 ≤ r₀) :
    let δ := mahalanobisMesh T₁ T₂ ρ h₁ h₂
    let lat : ℤ × ℤ → ℝ × ℝ := fun k => (x₀.1 + (k.1 : ℝ) * h₁, x₀.2 + (k.2 : ℝ) * h₂)
    let rad := fun k : ℤ × ℤ => euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ (lat k))
    let g := fun k : ℤ × ℤ => gaussian2D T₁ T₂ c₁ c₂ ρ (lat k)
    (∑' k : ℤ × ℤ, if rad k < r₀ then g k else 0) / (∑' k : ℤ × ℤ, g k) ≤
      2 * π * (r₀ + δ) ^ 2 := by
  dsimp only
  have h1ρ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      have h := (sq_lt_sq₀ (abs_nonneg ρ) zero_le_one).mpr (by simpa using hρ)
      simpa [sq_abs] using h
    linarith
  let κ := Real.sqrt (1 - ρ ^ 2)
  have hκ : 0 < κ := Real.sqrt_pos.mpr h1ρ
  let Z := T₁ * T₂ * κ
  have hZ : 0 < Z := by positivity
  let δ := mahalanobisMesh T₁ T₂ ρ h₁ h₂
  have hδ0 : 0 ≤ δ := by unfold δ mahalanobisMesh; positivity
  let lat : ℤ × ℤ → ℝ × ℝ := fun k => (x₀.1 + (k.1 : ℝ) * h₁, x₀.2 + (k.2 : ℝ) * h₂)
  let φ := mahalanobisCoord T₁ T₂ c₁ c₂ ρ
  let rad := fun k : ℤ × ℤ => euclidNorm2 (φ (lat k))
  let g := fun k : ℤ × ℤ => gaussian2D T₁ T₂ c₁ c₂ ρ (lat k)
  let indBall : ℝ × ℝ → ℝ≥0∞ := fun y => if euclidNorm2 y < r₀ + δ then 1 else 0
  have hind_meas : Measurable indBall := by
    unfold indBall euclidNorm2
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const measurable_const
  -- Tile-by-tile comparison for the inner ellipse
  have htile (k : ℤ × ℤ) :
      ENNReal.ofReal (h₁ * h₂) * ENNReal.ofReal (if rad k < r₀ then g k else 0) ≤
        ∫⁻ x in latticeTile x₀ h₁ h₂ k, indBall (φ x) := by
    by_cases hk : rad k < r₀
    · rw [if_pos hk]
      have hg1 : ENNReal.ofReal (g k) ≤ 1 :=
        ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg (rad k)]))
      calc
        ENNReal.ofReal (h₁ * h₂) * ENNReal.ofReal (g k)
            ≤ ENNReal.ofReal (h₁ * h₂) * 1 := mul_le_mul_left' hg1 _
        _ = ∫⁻ _x in latticeTile x₀ h₁ h₂ k, (1 : ℝ≥0∞) := by
          rw [setLIntegral_const, latticeTile_volume x₀ hh₁ hh₂ k, mul_one]
        _ ≤ ∫⁻ x in latticeTile x₀ h₁ h₂ k, indBall (φ x) := by
          apply setLIntegral_mono' (latticeTile_measurable x₀ h₁ h₂ k)
          intro x hx
          have hx₁ : |x.1 - (lat k).1| ≤ h₁ / 2 := by
            rw [abs_le]; dsimp [lat]
            exact ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
          have hx₂ : |x.2 - (lat k).2| ≤ h₂ / 2 := by
            rw [abs_le]; dsimp [lat]
            exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
          have hlip := (abs_le.mp (mahalanobis_tile_radius_lip T₁ T₂ c₁ c₂ ρ h₁ h₂ hT₁ hT₂ hρ hx₁ hx₂)).2
          have hlt : euclidNorm2 (φ x) < r₀ + δ := by dsimp [rad, δ] at hk ⊢; linarith
          simp [indBall, hlt]
    · rw [if_neg hk, ENNReal.ofReal_zero, mul_zero]
      exact zero_le _
  have hsum_ball :
      ENNReal.ofReal (h₁ * h₂) * (∑' k : ℤ × ℤ, ENNReal.ofReal (if rad k < r₀ then g k else 0)) ≤
        ∫⁻ x : ℝ × ℝ, indBall (φ x) := by
    rw [← setLIntegral_univ, ← latticeTile_iUnion_eq_univ x₀ hh₁ hh₂,
      lintegral_iUnion (latticeTile_measurable x₀ h₁ h₂)
        (latticeTile_pairwiseDisjoint x₀ hh₁ hh₂), ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum htile
  rw [lintegral_comp_mahalanobisCoord T₁ T₂ c₁ c₂ ρ hT₁ hT₂ hρ indBall hind_meas] at hsum_ball
  -- Evaluate the disk area ∫⁻ y, indBall y = π * (r₀ + δ)^2
  have hdisk : (∫⁻ y : ℝ × ℝ, indBall y) = ENNReal.ofReal (π * (r₀ + δ) ^ 2) := by
    let F : ℝ → ℝ≥0∞ := fun r => if r < r₀ + δ then 1 else 0
    have hF : Measurable F := Measurable.ite measurableSet_Iio measurable_const measurable_const
    change (∫⁻ y : ℝ × ℝ, F (euclidNorm2 y)) = ENNReal.ofReal (π * (r₀ + δ) ^ 2)
    rw [lintegral_radial_2D F hF]
    have hsub : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r) =
        ∫⁻ r in Ioo (0 : ℝ) (r₀ + δ), ENNReal.ofReal r := by
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr; intro r
      dsimp [F]
      by_cases h1 : 0 < r <;> by_cases h2 : r < r₀ + δ <;> simp [Set.indicator_apply, h1, h2]
    rw [hsub, ← ofReal_integral_eq_lintegral_ofReal
      (continuousOn_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr; exact hr.1.le)]
    rw [MeasureTheory.integral_Ioo_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      integral_id, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  rw [hdisk, ← ENNReal.ofReal_mul hZ.le] at hsum_ball
  have hmain := mahalanobis_2d_lattice_mass_bounds T₁ T₂ c₁ c₂ ρ h₁ h₂ x₀ hT₁ hT₂ hρ hh₁ hh₂
  have hsumm_g : Summable g := hmain.1
  have hsumm_inner : Summable (fun k : ℤ × ℤ => if rad k < r₀ then g k else 0) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs <;> [exact (Real.exp_pos _).le; rfl])
      (fun k => by split_ifs <;> [exact le_rfl; exact (Real.exp_pos _).le])
      hsumm_g
  have hnonneg_inner (k : ℤ × ℤ) : 0 ≤ if rad k < r₀ then g k else 0 := by
    split_ifs <;> [exact (Real.exp_pos _).le; rfl]
  rw [ENNReal.ofReal_tsum_of_nonneg hnonneg_inner hsumm_inner,
    ← ENNReal.ofReal_mul (mul_pos hh₁ hh₂).le] at hsum_ball
  have hnum_le : h₁ * h₂ * (∑' k : ℤ × ℤ, if rad k < r₀ then g k else 0) ≤
      Z * (π * (r₀ + δ) ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum_ball
  have hden_ge := mahalanobis_2d_lattice_mass_half T₁ T₂ c₁ c₂ ρ h₁ h₂ x₀ hT₁ hT₂ hρ hh₁ hh₂ hδ
  have hden_pos : 0 < ∑' k : ℤ × ℤ, g k :=
    (div_pos hZ (by positivity : 0 < 2 * h₁ * h₂)).trans_le hden_ge
  rw [div_le_iff₀ hden_pos]
  have hZ_le : Z ≤ 2 * (h₁ * h₂ * (∑' k : ℤ × ℤ, g k)) := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * h₁ * h₂)).mp hden_ge
    linarith
  have h1 : h₁ * h₂ * (∑' k : ℤ × ℤ, if rad k < r₀ then g k else 0) ≤
      h₁ * h₂ * (2 * π * (r₀ + δ) ^ 2 * (∑' k : ℤ × ℤ, g k)) := by
    have hmul := mul_le_mul_of_nonneg_right hZ_le (by positivity : 0 ≤ π * (r₀ + δ) ^ 2)
    linarith
  exact le_of_mul_le_mul_left h1 (mul_pos hh₁ hh₂)

/-- Specialization to Mahalanobis radius cutoff `r₀ = V ^ (-a)` with mesh `δ ≤ V ^ (-a)`:
discarding Mahalanobis radii `< V ^ (-a)` loses mass at most `8 * π * V ^ (-2 * a)`. -/
theorem mahalanobis_2d_discarded_radius_rpow_le (T₁ T₂ c₁ c₂ ρ h₁ h₂ V a : ℝ) (x₀ : ℝ × ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hρ : |ρ| < 1) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (hV : 0 < V)
    (hδ10 : mahalanobisMesh T₁ T₂ ρ h₁ h₂ ≤ 1 / 10)
    (hδr : mahalanobisMesh T₁ T₂ ρ h₁ h₂ ≤ V ^ (-a)) :
    let lat : ℤ × ℤ → ℝ × ℝ := fun k => (x₀.1 + (k.1 : ℝ) * h₁, x₀.2 + (k.2 : ℝ) * h₂)
    let rad := fun k : ℤ × ℤ => euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ (lat k))
    let g := fun k : ℤ × ℤ => gaussian2D T₁ T₂ c₁ c₂ ρ (lat k)
    (∑' k : ℤ × ℤ, if rad k < V ^ (-a) then g k else 0) / (∑' k : ℤ × ℤ, g k) ≤
      8 * π * V ^ (-2 * a) := by
  dsimp only
  have hr₀ : 0 ≤ V ^ (-a) := (Real.rpow_pos_of_pos hV (-a)).le
  have hbase := mahalanobis_2d_inner_ellipse_mass_le T₁ T₂ c₁ c₂ ρ h₁ h₂ x₀
    hT₁ hT₂ hρ hh₁ hh₂ hδ10 (V ^ (-a)) hr₀
  refine hbase.trans ?_
  have hsum : V ^ (-a) + mahalanobisMesh T₁ T₂ ρ h₁ h₂ ≤ 2 * V ^ (-a) := by linarith
  have hsq : (V ^ (-a) + mahalanobisMesh T₁ T₂ ρ h₁ h₂) ^ 2 ≤ (2 * V ^ (-a)) ^ 2 :=
    pow_le_pow_left₀ (by unfold mahalanobisMesh; positivity) hsum 2
  have hrpow : (V ^ (-a)) ^ 2 = V ^ (-2 * a) := by
    rw [← Real.rpow_natCast (V ^ (-a)) 2, ← Real.rpow_mul hV.le]
    congr 1; norm_num; ring
  calc
    2 * π * (V ^ (-a) + mahalanobisMesh T₁ T₂ ρ h₁ h₂) ^ 2
        ≤ 2 * π * (2 * V ^ (-a)) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 8 * π * V ^ (-2 * a) := by rw [mul_pow, hrpow]; ring

end Mahalanobis2D

/-! ## Part 3: Hasse-Interval Exceptional-Prime Deletion Bounds -/

section HasseExceptionalDeletion

open Cogentic.RandomizedHasseIncidence Cogentic.Randomized

/-- The number of distinct prime factors of any natural number `N` is at most `N.log2`. -/
theorem primeFactors_card_le_log2 (N : ℕ) : N.primeFactors.card ≤ N.log2 := by
  by_cases hN : N = 0
  · simp [hN]
  have h1 : N.primeFactors.card ≤ Ω N := by
    rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_primeFactorsList]
    exact List.toFinset_card_le _
  exact h1.trans (RandomizedSplitWork.cardFactors_le_log2 N)

/-- Applying `RandomizedHasseIncidence.rich_hasse_centres_mul_le` to primes in the dyad
`(P, 2P]` bounds the number of primes with at least `k` Hasse-interval witnesses in `W`. -/
theorem dyadic_rich_hasse_primes_mul_le (W : Finset ℤ) (P k : ℕ) :
    ((primeBin P (2 * P)).filter fun p =>
        k ≤ (W.filter fun w => (w - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ)).card).card * k ≤
      (2 * Nat.sqrt (8 * P) + 1) * W.card := by
  let D := primeBin P (2 * P)
  let C : Finset ℤ := D.image (fun p : ℕ => (p : ℤ) + 1)
  have hC : ∀ c ∈ C, c ≤ 2 * (P : ℤ) + 1 := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    have hp2P : p ≤ 2 * P := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    omega
  have hinj : Function.Injective (fun p : ℕ => (p : ℤ) + 1) := by
    intro a b h; omega
  have hcard :
      (D.filter fun p => k ≤ (W.filter fun w => (w - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ)).card).card =
      (C.filter fun c => k ≤ (W.filter fun w => (w - c) ^ 2 ≤ 4 * (c - 1)).card).card := by
    rw [← Finset.card_image_of_injective _ hinj]
    congr 1
    ext c
    simp only [C, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨p, ⟨hpD, hpk⟩, rfl⟩
      exact ⟨⟨p, hpD, rfl⟩, by simpa using hpk⟩
    · rintro ⟨⟨p, hpD, rfl⟩, hck⟩
      exact ⟨p, ⟨hpD, by simpa using hck⟩, rfl⟩
  rw [hcard]
  exact rich_hasse_centres_mul_le C W P k hC

/-- **Dyadic exceptional-prime fraction bound after deleting prime factors of `N`**:
if at most `M` primes in the dyad `(P, 2P]` fail the smooth-order threshold and the dyad
contains at least `c * P / log P` primes (`> 0`), then after also deleting all prime factors
of `N` (at most `N.log2` primes), the exceptional fraction is at most
`(M + N.log2) / (c * P / log P)`. -/
theorem dyadic_exceptional_fraction_le {P N M : ℕ} {c : ℝ}
    (hN : N ≠ 0)
    (E : Finset ℕ) (hEM : E.card ≤ M)
    (hsupply_pos : 0 < c * (P : ℝ) / Real.log P)
    (hsupply : c * (P : ℝ) / Real.log P ≤ ((primeBin P (2 * P)).card : ℝ)) :
    let D := primeBin P (2 * P)
    let E_total := (E ∩ D) ∪ (D.filter fun p => p ∣ N)
    (E_total.card : ℝ) / (D.card : ℝ) ≤
      ((M : ℝ) + (N.log2 : ℝ)) / (c * (P : ℝ) / Real.log P) := by
  dsimp only
  let D := primeBin P (2 * P)
  let E_N := D.filter fun p => p ∣ N
  have hEN_sub : E_N ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨hpD, hdvd⟩ := Finset.mem_filter.mp hp
    have hpPrime : p.Prime := (Finset.mem_filter.mp hpD).2
    exact Nat.mem_primeFactors.mpr ⟨hpPrime, hdvd, hN⟩
  have hEN_card : E_N.card ≤ N.log2 :=
    (Finset.card_le_card hEN_sub).trans (primeFactors_card_le_log2 N)
  have htot_card : ((E ∩ D) ∪ E_N).card ≤ M + N.log2 := calc
    ((E ∩ D) ∪ E_N).card ≤ (E ∩ D).card + E_N.card := Finset.card_union_le _ _
    _ ≤ E.card + E_N.card := Nat.add_le_add_right (Finset.card_le_card Finset.inter_subset_left) _
    _ ≤ M + N.log2 := Nat.add_le_add hEM hEN_card
  have hD_pos : (0 : ℝ) < (D.card : ℝ) := hsupply_pos.trans_le hsupply
  have hnum_le : (((E ∩ D) ∪ E_N).card : ℝ) ≤ (M : ℝ) + (N.log2 : ℝ) := by
    exact_mod_cast htot_card
  calc
    (((E ∩ D) ∪ E_N).card : ℝ) / (D.card : ℝ)
        ≤ ((M : ℝ) + (N.log2 : ℝ)) / (D.card : ℝ) :=
      div_le_div_of_nonneg_right hnum_le hD_pos.le
    _ ≤ ((M : ℝ) + (N.log2 : ℝ)) / (c * (P : ℝ) / Real.log P) :=
      div_le_div_of_nonneg_left (by positivity) hsupply_pos hsupply

/-- Direct combination of `rich_hasse_centres_mul_le` with prime-factor deletion of `N` on a
dyad `(P, 2P]`. -/
theorem dyadic_hasse_exceptional_fraction_le {P N k : ℕ} {c : ℝ}
    (hN : N ≠ 0) (hk : 0 < k) (W : Finset ℤ)
    (hsupply_pos : 0 < c * (P : ℝ) / Real.log P)
    (hsupply : c * (P : ℝ) / Real.log P ≤ ((primeBin P (2 * P)).card : ℝ)) :
    let D := primeBin P (2 * P)
    let E_hasse := D.filter fun p =>
      k ≤ (W.filter fun w => (w - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ)).card
    let E_total := E_hasse ∪ (D.filter fun p => p ∣ N)
    (E_total.card : ℝ) / (D.card : ℝ) ≤
      ((((2 * Nat.sqrt (8 * P) + 1) * W.card : ℕ) : ℝ) / (k : ℝ) + (N.log2 : ℝ)) /
        (c * (P : ℝ) / Real.log P) := by
  dsimp only
  let D := primeBin P (2 * P)
  let E_hasse := D.filter fun p =>
    k ≤ (W.filter fun w => (w - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ)).card
  let E_N := D.filter fun p => p ∣ N
  have hhasse : (E_hasse.card : ℝ) ≤ (((2 * Nat.sqrt (8 * P) + 1) * W.card : ℕ) : ℝ) / (k : ℝ) := by
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [le_div_iff₀ hkR]
    exact_mod_cast dyadic_rich_hasse_primes_mul_le W P k
  have hEN_card : E_N.card ≤ N.log2 := by
    refine (Finset.card_le_card fun p hp => ?_).trans (primeFactors_card_le_log2 N)
    obtain ⟨hpD, hdvd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp hpD).2, hdvd, hN⟩
  have htot : ((E_hasse ∪ E_N).card : ℝ) ≤
      (((2 * Nat.sqrt (8 * P) + 1) * W.card : ℕ) : ℝ) / (k : ℝ) + (N.log2 : ℝ) := by
    have hcard : ((E_hasse ∪ E_N).card : ℝ) ≤ (E_hasse.card : ℝ) + (E_N.card : ℝ) := by
      exact_mod_cast Finset.card_union_le E_hasse E_N
    have hEN_R : (E_N.card : ℝ) ≤ (N.log2 : ℝ) := by exact_mod_cast hEN_card
    linarith
  have hD_pos : (0 : ℝ) < (D.card : ℝ) := hsupply_pos.trans_le hsupply
  calc
    ((E_hasse ∪ E_N).card : ℝ) / (D.card : ℝ)
        ≤ ((((2 * Nat.sqrt (8 * P) + 1) * W.card : ℕ) : ℝ) / (k : ℝ) + (N.log2 : ℝ)) /
            (D.card : ℝ) :=
      div_le_div_of_nonneg_right htot hD_pos.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hsupply_pos hsupply

/-- Under `DirichletLZerosOnLine`, every sufficiently large dyad `(P, 2P]` contains at least
`(1 / 4) * P / log P` primes (derived directly from `primeBin_supply_from_critical_line`). -/
theorem dyadic_prime_supply_eventually (line : DirichletLZerosOnLine) :
    ∃ P₀ : ℕ, 2 ≤ P₀ ∧ ∀ P ≥ P₀,
      (1 / 4 : ℝ) * (P : ℝ) / Real.log P ≤ ((primeBin P (2 * P)).card : ℝ) := by
  obtain ⟨K, hK, hbin⟩ := primeBin_supply_from_critical_line line
  have hlog_littleO : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ (1 / 8 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hsmall_real : ∀ᶠ x : ℝ in atTop,
      K * (1 + Real.log (6 * x)) ^ 2 * Real.sqrt (2 * x) ≤ x / 2 := by
    let C : ℝ := K * 4 * (6 ^ (1 / 4 : ℝ)) * Real.sqrt 2
    have hC : 0 ≤ C := by positivity
    have htend : Tendsto (fun x : ℝ => C * x ^ (-1 / 4 : ℝ)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun x : ℝ => x ^ (-1 / 4 : ℝ)) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
      simpa using h0.const_mul C
    have hlt : ∀ᶠ x : ℝ in atTop, C * x ^ (-1 / 4 : ℝ) < 1 / 2 :=
      htend.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [eventually_gt_atTop (1 : ℝ), hlt,
      (hlog_littleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 6))] with x hx hCx hlog6
    have hx0 : 0 < x := by linarith
    have h6x1 : 1 ≤ 6 * x := by linarith
    have hlog_nonneg : 0 ≤ Real.log (6 * x) := Real.log_nonneg h6x1
    have h6x_rpow : 1 ≤ (6 * x) ^ (1 / 8 : ℝ) := Real.one_le_rpow h6x1 (by norm_num)
    have hlog_bd : Real.log (6 * x) ≤ (1 / 2) * (6 * x) ^ (1 / 8 : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg,
        abs_of_pos (Real.rpow_pos_of_pos (by positivity : 0 < 6 * x) _)] using hlog6
    have h1plus : 1 + Real.log (6 * x) ≤ 2 * (6 * x) ^ (1 / 8 : ℝ) := by linarith
    have hsq : (1 + Real.log (6 * x)) ^ 2 ≤ 4 * (6 ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by
      calc
        (1 + Real.log (6 * x)) ^ 2 ≤ (2 * (6 * x) ^ (1 / 8 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h1plus 2
        _ = 4 * ((6 * x) ^ (1 / 8 : ℝ)) ^ 2 := by ring
        _ = 4 * (6 * x) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_natCast ((6 * x) ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul (by positivity)]
          congr 2; norm_num
        _ = 4 * (6 ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hx0.le]
    have hsqrt : Real.sqrt (2 * x) = Real.sqrt 2 * x ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow]
    have hxpow : x ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (-1 / 4 : ℝ) * x := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']
      congr 1; norm_num
    have hbound : K * (1 + Real.log (6 * x)) ^ 2 * Real.sqrt (2 * x) ≤
        (C * x ^ (-1 / 4 : ℝ)) * x := by
      calc
        K * (1 + Real.log (6 * x)) ^ 2 * Real.sqrt (2 * x)
            ≤ K * (4 * (6 ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ))) * (Real.sqrt 2 * x ^ (1 / 2 : ℝ)) := by
          rw [hsqrt]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq hK) (by positivity)
        _ = C * (x ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ)) := by dsimp [C]; ring
        _ = (C * x ^ (-1 / 4 : ℝ)) * x := by rw [hxpow]; ring
    exact hbound.trans (by nlinarith)
  rw [Filter.eventually_atTop] at hsmall_real
  obtain ⟨X, hX⟩ := hsmall_real
  refine ⟨max 2 (Nat.ceil X), le_max_left _ _, fun P hP => ?_⟩
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hP
  have hPX : X ≤ (P : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast (le_max_right 2 _).trans hP)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hlogP_pos : 0 < Real.log P := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hlog2P_le : Real.log ((2 * P : ℕ) : ℝ) ≤ 2 * Real.log P := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hPpos.ne']
    have hlog2 : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) (by exact_mod_cast hP2)
    linarith
  have hsupply := hbin P (2 * P) hP2 (by omega)
  have herr := hX (P : ℝ) hPX
  have hrew : (3 : ℝ) * ((2 * P : ℕ) : ℝ) = 6 * (P : ℝ) := by push_cast; ring
  have hrew2 : ((2 * P : ℕ) : ℝ) = 2 * (P : ℝ) := by push_cast; ring
  rw [hrew, hrew2] at hsupply
  have hhalf : (P : ℝ) / 2 ≤ ((primeBin P (2 * P)).card : ℝ) * Real.log ((2 * P : ℕ) : ℝ) := by
    rw [hrew2]
    linarith
  have hcard_mul : (P : ℝ) / 2 ≤ ((primeBin P (2 * P)).card : ℝ) * (2 * Real.log P) :=
    hhalf.trans (mul_le_mul_of_nonneg_left hlog2P_le (Nat.cast_nonneg _))
  rw [div_le_iff₀ hlogP_pos]
  linarith

/-- End-to-end dyadic exceptional-prime fraction bound under `DirichletLZerosOnLine`,
combining `primeBin_supply_from_critical_line`, `rich_hasse_centres_mul_le`, and deletion of
all prime factors of `N`. -/
theorem dyadic_exceptional_fraction_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ P₀ : ℕ, 2 ≤ P₀ ∧ ∀ P ≥ P₀, ∀ (N M : ℕ) (_hN : N ≠ 0) (E : Finset ℕ),
      E.card ≤ M →
      let D := primeBin P (2 * P)
      let E_total := (E ∩ D) ∪ (D.filter fun p => p ∣ N)
      (E_total.card : ℝ) / (D.card : ℝ) ≤
        ((M : ℝ) + (N.log2 : ℝ)) / ((1 / 4 : ℝ) * (P : ℝ) / Real.log P) := by
  obtain ⟨P₀, hP₀2, hsupply⟩ := dyadic_prime_supply_eventually line
  refine ⟨P₀, hP₀2, fun P hP N M hN E hEM => ?_⟩
  have hP2 : 2 ≤ P := hP₀2.trans hP
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  exact dyadic_exceptional_fraction_le hN E hEM (by positivity) (hsupply P hP)

/-- **Band-weighted exceptional deletion charge** (from `keybreak-public-elliptic-recognition.md`):
if a nonnegative profile `B` varies by at most a factor `C` across a prime dyad `D`, and the
exceptional subset `E ⊆ D` has fraction `E.card / D.card ≤ η`, then the total deleted weight
satisfies `∑ p ∈ E, B p ≤ C * η * ∑ p ∈ D, B p`. -/
theorem exceptional_band_weight_sum_le {D E : Finset ℕ} (hED : E ⊆ D) (hD : D.Nonempty)
    (B : ℕ → ℝ) (C η : ℝ)
    (hB : ∀ p ∈ D, 0 ≤ B p)
    (hvar : ∀ p ∈ D, ∀ q ∈ D, B p ≤ C * B q)
    (hfrac : (E.card : ℝ) / (D.card : ℝ) ≤ η) :
    (∑ p ∈ E, B p) ≤ C * η * (∑ q ∈ D, B q) := by
  have hDpos : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  have hC_nonneg : 0 ≤ C * (∑ q ∈ D, B q) := by
    have h0 : 0 ≤ ∑ p ∈ E, B p := Finset.sum_nonneg fun p hp => hB p (hED hp)
    by_cases hE0 : E.Nonempty
    · obtain ⟨p, hp⟩ := hE0
      have h1 := Finset.sum_le_sum fun q hq => hvar p (hED hp) q hq
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
      exact (mul_nonneg hDpos.le (hB p (hED hp))).trans h1
    · have hsum_pos : 0 ≤ ∑ q ∈ D, B q := Finset.sum_nonneg hB
      by_cases hB0 : (∑ q ∈ D, B q) = 0
      · simp [hB0]
      · obtain ⟨q, hq⟩ := hD
        have h1 := Finset.sum_le_sum fun r hr => hvar r hr q hq
        -- Even simpler: if E = ∅, the main goal is 0 ≤ C * η * ∑ B; handle directly below!
        have hpos_ex : ∃ q₀ ∈ D, 0 < B q₀ := by
          by_contra hall
          push_neg at hall
          apply hB0
          exact Finset.sum_eq_zero fun r hr => le_antisymm (hall r hr) (hB r hr)
        obtain ⟨q₀, hq₀, hBq₀⟩ := hpos_ex
        have hC0 : 0 ≤ C := by
          have := hvar q₀ hq₀ q₀ hq₀
          nlinarith
        exact mul_nonneg hC0 hsum_pos
  have hdouble : (D.card : ℝ) * (∑ p ∈ E, B p) ≤ (E.card : ℝ) * (C * (∑ q ∈ D, B q)) := by
    calc
      (D.card : ℝ) * (∑ p ∈ E, B p) = ∑ _q ∈ D, ∑ p ∈ E, B p := by simp [nsmul_eq_mul]
      _ ≤ ∑ q ∈ D, ∑ _p ∈ E, (C * B q) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun p hp => hvar p (hED hp) q hq
      _ = ∑ q ∈ D, (E.card : ℝ) * (C * B q) := by
        apply Finset.sum_congr rfl; intro q _; simp [nsmul_eq_mul]
      _ = (E.card : ℝ) * (C * (∑ q ∈ D, B q)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hdiv : (∑ p ∈ E, B p) ≤ ((E.card : ℝ) / (D.card : ℝ)) * (C * (∑ q ∈ D, B q)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hDpos, mul_comm]
    exact hdouble
  calc
    (∑ p ∈ E, B p) ≤ ((E.card : ℝ) / (D.card : ℝ)) * (C * (∑ q ∈ D, B q)) := hdiv
    _ ≤ η * (C * (∑ q ∈ D, B q)) := mul_le_mul_of_nonneg_right hfrac hC_nonneg
    _ = C * η * (∑ q ∈ D, B q) := by ring

end HasseExceptionalDeletion

/-! ## Part 4: Recursive Partial-Factorization & Elliptic Recognition Success Bounds -/

section RecursiveRecognition

/-- A certified proper multiplicative split of `n`. -/
abbrev ProperSplit (n : ℕ) := {p : ℕ × ℕ // 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 * p.2 = n}

private lemma ProperSplit.fst_lt {n : ℕ} (p : ProperSplit n) : p.val.1 < n := by
  obtain ⟨ha, hb, hab⟩ := p.property
  exact hab ▸ lt_mul_of_one_lt_right (by omega : 0 < p.val.1) (by omega)

private lemma ProperSplit.snd_lt {n : ℕ} (p : ProperSplit n) : p.val.2 < n := by
  obtain ⟨ha, hb, hab⟩ := p.property
  exact hab ▸ lt_mul_of_one_lt_left (by omega : 0 < p.val.2) (by omega)

/-- **Recursive elliptic factorizer**: given a fallible splitting kernel `ellipticSplit` on
composite integers `n ≥ 2` returning either `none` (local rejection) or a verified proper split
`some p`, recursively splits both factors until every leaf is prime (or `n = 1` returns `[]`). -/
noncomputable def recursiveEllipticFactor
    (ellipticSplit : ∀ n, 2 ≤ n → ¬ n.Prime → PMF (Option (ProperSplit n)))
    (n : ℕ) : PMF (Option (List ℕ)) :=
  if h1 : n = 1 then
    PMF.pure (some [])
  else if h2 : 2 ≤ n then
    if hp : n.Prime then
      PMF.pure (some [n])
    else
      (ellipticSplit n h2 hp).bind fun
        | none => PMF.pure none
        | some p =>
          (recursiveEllipticFactor ellipticSplit p.val.1).bind fun
            | none => PMF.pure none
            | some left =>
              (recursiveEllipticFactor ellipticSplit p.val.2).map fun
                | none => none
                | some right => some (left ++ right)
  else
    PMF.pure none
termination_by n
decreasing_by
  all_goals first | exact p.fst_lt | exact p.snd_lt

/-- **Soundness of recursive elliptic factorization**: any returned factor list is a complete
verified prime factorization of `n` (product equals `n`, every entry is prime, and it is a
permutation of `n.primeFactorsList`). -/
theorem recursiveEllipticFactor_sound
    (ellipticSplit : ∀ n, 2 ≤ n → ¬ n.Prime → PMF (Option (ProperSplit n))) :
    ∀ (n : ℕ) (l : List ℕ),
      some l ∈ (recursiveEllipticFactor ellipticSplit n).support →
      l.prod = n ∧ (∀ p ∈ l, p.Prime) ∧ l.Perm n.primeFactorsList := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl
    rw [recursiveEllipticFactor] at hl
    by_cases h1 : n = 1
    · rw [dif_pos h1] at hl
      simp only [PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq] at hl
      subst hl; subst h1
      simp
    · rw [dif_neg h1] at hl
      by_cases h2 : 2 ≤ n
      · rw [dif_pos h2] at hl
        by_cases hp : n.Prime
        · rw [dif_pos hp] at hl
          simp only [PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq] at hl
          subst hl
          refine ⟨by simp, by simpa using hp, ?_⟩
          exact Nat.primeFactorsList_unique (by simp) (by simpa using hp)
        · rw [dif_neg hp] at hl
          rw [PMF.mem_support_bind_iff] at hl
          obtain ⟨o, _, ho⟩ := hl
          cases o with
          | none =>
            simp only [PMF.support_pure, Set.mem_singleton_iff, reduceCtorEq] at ho
          | some p =>
            rw [PMF.mem_support_bind_iff] at ho
            obtain ⟨ol, hol_supp, hol⟩ := ho
            cases ol with
            | none =>
              simp only [PMF.support_pure, Set.mem_singleton_iff, reduceCtorEq] at hol
            | some left =>
              rw [PMF.mem_support_map_iff] at hol
              obtain ⟨or_, hor_supp, hor_eq⟩ := hol
              cases or_ with
              | none => simp at hor_eq
              | some right =>
                simp only [Option.some.injEq] at hor_eq
                subst hor_eq
                have hleft := ih p.val.1 p.fst_lt left hol_supp
                have hright := ih p.val.2 p.snd_lt right hor_supp
                have hprod : (left ++ right).prod = n := by
                  rw [List.prod_append, hleft.1, hright.1, p.property.2.2]
                have hprime : ∀ q ∈ left ++ right, q.Prime := by
                  intro q hq
                  rcases List.mem_append.mp hq with hq | hq
                  · exact hleft.2.1 q hq
                  · exact hright.2.1 q hq
                exact ⟨hprod, hprime, Nat.primeFactorsList_unique hprod hprime⟩
      · rw [dif_neg h2] at hl
        simp only [PMF.support_pure, Set.mem_singleton_iff, reduceCtorEq] at hl

/-- Helper: in any `PMF (Option α)`, the sum of probabilities of all `some x` outcomes is `≤ 1`. -/
private lemma pmf_tsum_some_le_one {α : Type*} (p : PMF (Option α)) :
    (∑' x : α, p (some x)) ≤ 1 := by
  have h1 : (∑' x : α, p (some x)) ≤ ∑' o : Option α, p o := by
    rw [tsum_option (f := fun o => p o) ENNReal.summable]
    exact le_add_self
  exact h1.trans_eq p.tsum_coe

/-- Helper: failure probability of chaining two `PMF (Option (List ℕ))` computations is at most
the sum of their individual failure probabilities. -/
private lemma pmf_option_append_fail_le (p q : PMF (Option (List ℕ))) :
    (p.bind fun
      | none => PMF.pure none
      | some left => q.map fun
        | none => none
        | some right => some (left ++ right)) none ≤ p none + q none := by
  rw [PMF.bind_apply, tsum_option ENNReal.summable]
  simp only [PMF.pure_apply_self, mul_one]
  refine add_le_add_left ?_ (p none)
  have hmap (left : List ℕ) :
      (q.map fun
        | none => (none : Option (List ℕ))
        | some right => some (left ++ right)) none = q none := by
    rw [PMF.map_apply, tsum_option ENNReal.summable]
    simp
  simp_rw [hmap]
  rw [ENNReal.tsum_mul_right]
  calc
    (∑' left : List ℕ, p (some left)) * q none ≤ 1 * q none :=
      mul_le_mul_right' (pmf_tsum_some_le_one p) _
    _ = q none := one_mul _

/-- **Strong-induction failure probability bound for recursive elliptic splitting** (in terms of
`Ω n - 1`, the exact number of splits needed):
if every prime factor of `n ≥ 1` belongs to `Eligible` and every composite `k ≥ 2` with all
prime factors in `Eligible` fails to split with probability at most `δ_split`, then
`recursiveEllipticFactor` fails with probability at most `(Ω n - 1) * δ_split`. -/
theorem recursiveEllipticFactor_fail_le_cardFactors
    (ellipticSplit : ∀ n, 2 ≤ n → ¬ n.Prime → PMF (Option (ProperSplit n)))
    (Eligible : Set ℕ) (δ_split : ℝ) (hδ : 0 ≤ δ_split)
    (hsplit : ∀ k (hk : 2 ≤ k) (hcomp : ¬ k.Prime),
      (∀ p ∈ k.primeFactors, p ∈ Eligible) →
      (ellipticSplit k hk hcomp none).toReal ≤ δ_split) :
    ∀ n : ℕ, 1 ≤ n → (∀ p ∈ n.primeFactors, p ∈ Eligible) →
      (recursiveEllipticFactor ellipticSplit n none).toReal ≤
        ((Ω n - 1 : ℕ) : ℝ) * δ_split := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn helig
    -- Work in ENNReal using ENNReal.ofReal δ_split, then convert to Real at the end!
    have hsplitE : ∀ k (hk : 2 ≤ k) (hcomp : ¬ k.Prime),
        (∀ p ∈ k.primeFactors, p ∈ Eligible) →
        ellipticSplit k hk hcomp none ≤ ENNReal.ofReal δ_split := by
      intro k hk hcomp hkE
      rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (hsplit k hk hcomp hkE)
    suffices hE : recursiveEllipticFactor ellipticSplit n none ≤
        ENNReal.ofReal (((Ω n - 1 : ℕ) : ℝ) * δ_split) by
      have hre := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
      rwa [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hδ)] at hre
    rw [recursiveEllipticFactor]
    by_cases h1 : n = 1
    · rw [dif_pos h1]
      simp
    · have h2 : 2 ≤ n := by omega
      rw [dif_neg h1, dif_pos h2]
      by_cases hp : n.Prime
      · rw [dif_pos hp]
        simp
      · rw [dif_neg hp]
        rw [PMF.bind_apply, tsum_option ENNReal.summable]
        simp only [PMF.pure_apply_self, mul_one]
        have hchild (p : ProperSplit n) :
            ((recursiveEllipticFactor ellipticSplit p.val.1).bind fun
              | none => PMF.pure none
              | some left => (recursiveEllipticFactor ellipticSplit p.val.2).map fun
                | none => none
                | some right => some (left ++ right)) none ≤
              ENNReal.ofReal (((Ω n - 2 : ℕ) : ℝ) * δ_split) := by
          obtain ⟨ha, hb, hab⟩ := p.property
          have helig1 : ∀ q ∈ p.val.1.primeFactors, q ∈ Eligible := by
            intro q hq
            apply helig q
            rw [Nat.mem_primeFactors] at hq ⊢
            exact ⟨hq.1, hq.2.1.trans ⟨p.val.2, hab.symm⟩, by omega⟩
          have helig2 : ∀ q ∈ p.val.2.primeFactors, q ∈ Eligible := by
            intro q hq
            apply helig q
            rw [Nat.mem_primeFactors] at hq ⊢
            exact ⟨hq.1, hq.2.1.trans ⟨p.val.1, by rw [mul_comm, hab]⟩, by omega⟩
          have ih1 : recursiveEllipticFactor ellipticSplit p.val.1 none ≤
              ENNReal.ofReal (((Ω p.val.1 - 1 : ℕ) : ℝ) * δ_split) := by
            rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
            exact ENNReal.ofReal_le_ofReal (ih p.val.1 p.fst_lt (by omega) helig1)
          have ih2 : recursiveEllipticFactor ellipticSplit p.val.2 none ≤
              ENNReal.ofReal (((Ω p.val.2 - 1 : ℕ) : ℝ) * δ_split) := by
            rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
            exact ENNReal.ofReal_le_ofReal (ih p.val.2 p.snd_lt (by omega) helig2)
          have hΩ1 : 1 ≤ Ω p.val.1 :=
            ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
          have hΩ2 : 1 ≤ Ω p.val.2 :=
            ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
          have hΩn : Ω n = Ω p.val.1 + Ω p.val.2 :=
            hab ▸ ArithmeticFunction.cardFactors_mul (by omega) (by omega)
          have hsub_eq : (Ω p.val.1 - 1) + (Ω p.val.2 - 1) = Ω n - 2 := by omega
          calc
            _ ≤ recursiveEllipticFactor ellipticSplit p.val.1 none +
                recursiveEllipticFactor ellipticSplit p.val.2 none :=
              pmf_option_append_fail_le _ _
            _ ≤ ENNReal.ofReal (((Ω p.val.1 - 1 : ℕ) : ℝ) * δ_split) +
                ENNReal.ofReal (((Ω p.val.2 - 1 : ℕ) : ℝ) * δ_split) :=
              add_le_add ih1 ih2
            _ = ENNReal.ofReal (((Ω n - 2 : ℕ) : ℝ) * δ_split) := by
              rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hδ)
                (mul_nonneg (Nat.cast_nonneg _) hδ)]
              congr 1
              rw [← add_mul, ← Nat.cast_add, hsub_eq]
        have hsum_child :
            (∑' p : ProperSplit n, ellipticSplit n h2 hp (some p) *
              ((recursiveEllipticFactor ellipticSplit p.val.1).bind fun
                | none => PMF.pure none
                | some left => (recursiveEllipticFactor ellipticSplit p.val.2).map fun
                  | none => none
                  | some right => some (left ++ right)) none) ≤
              ENNReal.ofReal (((Ω n - 2 : ℕ) : ℝ) * δ_split) := by
          calc
            _ ≤ ∑' p : ProperSplit n, ellipticSplit n h2 hp (some p) *
                ENNReal.ofReal (((Ω n - 2 : ℕ) : ℝ) * δ_split) :=
              ENNReal.tsum_le_tsum fun p => mul_le_mul_left' (hchild p) _
            _ = (∑' p : ProperSplit n, ellipticSplit n h2 hp (some p)) *
                ENNReal.ofReal (((Ω n - 2 : ℕ) : ℝ) * δ_split) := ENNReal.tsum_mul_right
            _ ≤ 1 * ENNReal.ofReal (((Ω n - 2 : ℕ) : ℝ) * δ_split) :=
              mul_le_mul_right' (pmf_tsum_some_le_one _) _
            _ = ENNReal.ofReal (((Ω n - 2 : ℕ) : ℝ) * δ_split) := one_mul _
        have hΩ_ge2 : 2 ≤ Ω n := by
          by_contra hlt
          push_neg at hlt
          have hpos : 1 ≤ Ω n := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
          have heq1 : Ω n = 1 := by omega
          exact hp (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp heq1)
        have hstep_eq : 1 + (Ω n - 2) = Ω n - 1 := by omega
        calc
          ellipticSplit n h2 hp none +
              (∑' p : ProperSplit n, ellipticSplit n h2 hp (some p) *
                ((recursiveEllipticFactor ellipticSplit p.val.1).bind fun
                  | none => PMF.pure none
                  | some left => (recursiveEllipticFactor ellipticSplit p.val.2).map fun
                    | none => none
                    | some right => some (left ++ right)) none)
              ≤ ENNReal.ofReal δ_split + ENNReal.ofReal (((Ω n - 2 : ℕ) : ℝ) * δ_split) :=
            add_le_add (hsplitE n h2 hp helig) hsum_child
          _ = ENNReal.ofReal (((Ω n - 1 : ℕ) : ℝ) * δ_split) := by
            rw [← ENNReal.ofReal_add hδ (mul_nonneg (Nat.cast_nonneg _) hδ)]
            congr 1
            have : (1 : ℝ) + ((Ω n - 2 : ℕ) : ℝ) = ((Ω n - 1 : ℕ) : ℝ) := by exact_mod_cast hstep_eq
            linarith

/-- Corollary bounding recursive elliptic splitting failure by `n.log2 * δ_split`. -/
theorem recursiveEllipticFactor_fail_le_log2
    (ellipticSplit : ∀ n, 2 ≤ n → ¬ n.Prime → PMF (Option (ProperSplit n)))
    (Eligible : Set ℕ) (δ_split : ℝ) (hδ : 0 ≤ δ_split)
    (hsplit : ∀ k (hk : 2 ≤ k) (hcomp : ¬ k.Prime),
      (∀ p ∈ k.primeFactors, p ∈ Eligible) →
      (ellipticSplit k hk hcomp none).toReal ≤ δ_split)
    {n : ℕ} (hn : 1 ≤ n) (helig : ∀ p ∈ n.primeFactors, p ∈ Eligible) :
    (recursiveEllipticFactor ellipticSplit n none).toReal ≤ (n.log2 : ℝ) * δ_split := by
  have h1 := recursiveEllipticFactor_fail_le_cardFactors ellipticSplit Eligible δ_split hδ hsplit n hn helig
  have h2 : (Ω n - 1 : ℕ) ≤ n.log2 := (Nat.sub_le _ _).trans (RandomizedSplitWork.cardFactors_le_log2 n)
  exact h1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hδ)

/-- **Two-stage partial + recursive elliptic recognizer** (from `keybreak-public-elliptic-recognition.md`):
first run the small-factor prepass (cutoff `B`) returning either `none` or `(smalls, cofactor)`,
then recursively split `cofactor` via `recursiveEllipticFactor` and concatenate the prime lists. -/
noncomputable def twoStageRecognizer
    (smallFactor : PMF (Option (List ℕ × ℕ)))
    (ellipticSplit : ∀ n, 2 ≤ n → ¬ n.Prime → PMF (Option (ProperSplit n))) :
    PMF (Option (List ℕ)) :=
  smallFactor.bind fun
    | none => PMF.pure none
    | some (smalls, cofactor) =>
      (recursiveEllipticFactor ellipticSplit cofactor).map fun
        | none => none
        | some larges => some (smalls ++ larges)

/-- **Soundness of the two-stage recognizer**: every accepted list is a complete verified prime
factorization of `m` (product equals `m`, every entry is prime, and it is a permutation of
`m.primeFactorsList`). -/
theorem twoStageRecognizer_sound
    {m B : ℕ}
    (smallFactor : PMF (Option (List ℕ × ℕ)))
    (hsmall_sound : ∀ smalls cofactor,
      some (smalls, cofactor) ∈ smallFactor.support →
      smalls.prod * cofactor = m ∧ (∀ p ∈ smalls, p.Prime ∧ p ≤ B) ∧
        (∀ p ∈ cofactor.primeFactors, B < p))
    (ellipticSplit : ∀ n, 2 ≤ n → ¬ n.Prime → PMF (Option (ProperSplit n)))
    {l : List ℕ} (hl : some l ∈ (twoStageRecognizer smallFactor ellipticSplit).support) :
    l.prod = m ∧ (∀ p ∈ l, p.Prime) ∧ l.Perm m.primeFactorsList := by
  rw [twoStageRecognizer, PMF.mem_support_bind_iff] at hl
  obtain ⟨o, ho_supp, ho⟩ := hl
  cases o with
  | none =>
    simp only [PMF.support_pure, Set.mem_singleton_iff, reduceCtorEq] at ho
  | some sc =>
    rcases sc with ⟨smalls, cofactor⟩
    rw [PMF.mem_support_map_iff] at ho
    obtain ⟨ol, hol_supp, hol_eq⟩ := ho
    cases ol with
    | none => simp at hol_eq
    | some larges =>
      simp only [Option.some.injEq] at hol_eq
      subst hol_eq
      obtain ⟨hprod_sc, hsmall_p, _⟩ := hsmall_sound smalls cofactor ho_supp
      obtain ⟨hprod_l, hlarge_p, _⟩ := recursiveEllipticFactor_sound ellipticSplit cofactor larges hol_supp
      have hprod : (smalls ++ larges).prod = m := by
        rw [List.prod_append, hprod_l, hprod_sc]
      have hprime : ∀ p ∈ smalls ++ larges, p.Prime := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact (hsmall_p p hp).1
        · exact hlarge_p p hp
      exact ⟨hprod, hprime, Nat.primeFactorsList_unique hprod hprime⟩

/-- **Recursive partial-factorization failure bound** `δ_small + m.log2 * δ_split`:
given a candidate integer `m ≥ 1` whose prime factors above `B` all belong to `Eligible`,
a small-factor prepass finding all prime factors `≤ B` with failure probability `≤ δ_small`,
and an elliptic splitter failing with probability `≤ δ_split` on composites supported on
`Eligible`, the two-stage recursive recognizer fails with probability at most
`δ_small + m.log2 * δ_split`. -/
theorem twoStageRecognizer_fail_le
    {m B : ℕ} (hm : 1 ≤ m) (Eligible : Set ℕ)
    (hm_elig : ∀ p ∈ m.primeFactors, B < p → p ∈ Eligible)
    (smallFactor : PMF (Option (List ℕ × ℕ)))
    (hsmall_sound : ∀ smalls cofactor,
      some (smalls, cofactor) ∈ smallFactor.support →
      smalls.prod * cofactor = m ∧ (∀ p ∈ smalls, p.Prime ∧ p ≤ B) ∧
        (∀ p ∈ cofactor.primeFactors, B < p))
    (ellipticSplit : ∀ n, 2 ≤ n → ¬ n.Prime → PMF (Option (ProperSplit n)))
    (δ_small δ_split : ℝ) (hδ_small : 0 ≤ δ_small) (hδ_split : 0 ≤ δ_split)
    (hsmall_fail : (smallFactor none).toReal ≤ δ_small)
    (hsplit_fail : ∀ k (hk : 2 ≤ k) (hcomp : ¬ k.Prime),
      (∀ p ∈ k.primeFactors, p ∈ Eligible) →
      (ellipticSplit k hk hcomp none).toReal ≤ δ_split) :
    (twoStageRecognizer smallFactor ellipticSplit none).toReal ≤
      δ_small + (m.log2 : ℝ) * δ_split := by
  suffices hE : twoStageRecognizer smallFactor ellipticSplit none ≤
      ENNReal.ofReal (δ_small + (m.log2 : ℝ) * δ_split) by
    have hre := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
    rwa [ENNReal.toReal_ofReal (add_nonneg hδ_small (mul_nonneg (Nat.cast_nonneg _) hδ_split))] at hre
  rw [twoStageRecognizer, PMF.bind_apply, tsum_option ENNReal.summable]
  simp only [PMF.pure_apply_self, mul_one]
  have hsmallE : smallFactor none ≤ ENNReal.ofReal δ_small := by
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hsmall_fail
  have hterm (sc : List ℕ × ℕ) :
      smallFactor (some sc) *
        ((recursiveEllipticFactor ellipticSplit sc.2).map fun
          | none => (none : Option (List ℕ))
          | some larges => some (sc.1 ++ larges)) none ≤
      smallFactor (some sc) * ENNReal.ofReal ((m.log2 : ℝ) * δ_split) := by
    by_cases h0 : smallFactor (some sc) = 0
    · simp [h0]
    · have hsupp : some sc ∈ smallFactor.support := (PMF.mem_support_iff _ _).mpr h0
      obtain ⟨hprod_sc, _, hcof_gt⟩ := hsmall_sound sc.1 sc.2 hsupp
      have hcof_pos : 1 ≤ sc.2 := by
        by_contra hlt
        have hzero : sc.2 = 0 := by omega
        rw [hzero, mul_zero] at hprod_sc
        omega
      have hcof_le : sc.2 ≤ m := by
        have h1 : 1 ≤ sc.1.prod := by
          by_contra hlt
          have hzero : sc.1.prod = 0 := by omega
          rw [hzero, zero_mul] at hprod_sc
          omega
        calc sc.2 = 1 * sc.2 := (one_mul _).symm
          _ ≤ sc.1.prod * sc.2 := Nat.mul_le_mul_right _ h1
          _ = m := hprod_sc
      have hcof_elig : ∀ p ∈ sc.2.primeFactors, p ∈ Eligible := by
        intro p hp
        have hp_gt : B < p := hcof_gt p hp
        have hp_m : p ∈ m.primeFactors := by
          rw [Nat.mem_primeFactors] at hp ⊢
          exact ⟨hp.1, hp.2.1.trans ⟨sc.1.prod, by rw [mul_comm, hprod_sc]⟩, by omega⟩
        exact hm_elig p hp_m hp_gt
      have hmap :
          ((recursiveEllipticFactor ellipticSplit sc.2).map fun
            | none => (none : Option (List ℕ))
            | some larges => some (sc.1 ++ larges)) none =
          recursiveEllipticFactor ellipticSplit sc.2 none := by
        rw [PMF.map_apply, tsum_option ENNReal.summable]
        simp
      rw [hmap]
      apply mul_le_mul_left'
      rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
      apply ENNReal.ofReal_le_ofReal
      have hfail := recursiveEllipticFactor_fail_le_log2 ellipticSplit Eligible δ_split hδ_split
        hsplit_fail hcof_pos hcof_elig
      have hlog_le : sc.2.log2 ≤ m.log2 := Nat.log2_le_log2 hcof_le
      exact hfail.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlog_le) hδ_split)
  have hsum : (∑' sc : List ℕ × ℕ, smallFactor (some sc) *
        ((recursiveEllipticFactor ellipticSplit sc.2).map fun
          | none => (none : Option (List ℕ))
          | some larges => some (sc.1 ++ larges)) none) ≤
      ENNReal.ofReal ((m.log2 : ℝ) * δ_split) := by
    calc
      _ ≤ ∑' sc : List ℕ × ℕ, smallFactor (some sc) * ENNReal.ofReal ((m.log2 : ℝ) * δ_split) :=
        ENNReal.tsum_le_tsum hterm
      _ = (∑' sc : List ℕ × ℕ, smallFactor (some sc)) * ENNReal.ofReal ((m.log2 : ℝ) * δ_split) :=
        ENNReal.tsum_mul_right
      _ ≤ 1 * ENNReal.ofReal ((m.log2 : ℝ) * δ_split) :=
        mul_le_mul_right' (pmf_tsum_some_le_one _) _
      _ = ENNReal.ofReal ((m.log2 : ℝ) * δ_split) := one_mul _
  calc
    smallFactor none + (∑' sc : List ℕ × ℕ, smallFactor (some sc) *
          ((recursiveEllipticFactor ellipticSplit sc.2).map fun
            | none => (none : Option (List ℕ))
            | some larges => some (sc.1 ++ larges)) none)
        ≤ ENNReal.ofReal δ_small + ENNReal.ofReal ((m.log2 : ℝ) * δ_split) :=
      add_le_add hsmallE hsum
    _ = ENNReal.ofReal (δ_small + (m.log2 : ℝ) * δ_split) :=
      (ENNReal.ofReal_add hδ_small (mul_nonneg (Nat.cast_nonneg _) hδ_split)).symm

/-- **Recursive partial-factorization success probability lower bound**:
the probability that `twoStageRecognizer` outputs `some l` (which by `twoStageRecognizer_sound`
is guaranteed to be a complete verified prime factorization of `m`) is at least
`1 - (δ_small + m.log2 * δ_split)`. -/
theorem twoStageRecognizer_success_ge
    {m B : ℕ} (hm : 1 ≤ m) (Eligible : Set ℕ)
    (hm_elig : ∀ p ∈ m.primeFactors, B < p → p ∈ Eligible)
    (smallFactor : PMF (Option (List ℕ × ℕ)))
    (hsmall_sound : ∀ smalls cofactor,
      some (smalls, cofactor) ∈ smallFactor.support →
      smalls.prod * cofactor = m ∧ (∀ p ∈ smalls, p.Prime ∧ p ≤ B) ∧
        (∀ p ∈ cofactor.primeFactors, B < p))
    (ellipticSplit : ∀ n, 2 ≤ n → ¬ n.Prime → PMF (Option (ProperSplit n)))
    (δ_small δ_split : ℝ) (hδ_small : 0 ≤ δ_small) (hδ_split : 0 ≤ δ_split)
    (hsmall_fail : (smallFactor none).toReal ≤ δ_small)
    (hsplit_fail : ∀ k (hk : 2 ≤ k) (hcomp : ¬ k.Prime),
      (∀ p ∈ k.primeFactors, p ∈ Eligible) →
      (ellipticSplit k hk hcomp none).toReal ≤ δ_split) :
    1 - (δ_small + (m.log2 : ℝ) * δ_split) ≤
      ((twoStageRecognizer smallFactor ellipticSplit).toOuterMeasure {o | o.isSome}).toReal := by
  let P := twoStageRecognizer smallFactor ellipticSplit
  have hfail := twoStageRecognizer_fail_le hm Eligible hm_elig smallFactor hsmall_sound
    ellipticSplit δ_small δ_split hδ_small hδ_split hsmall_fail hsplit_fail
  have hpart : P none + P.toOuterMeasure {o | o.isSome} = 1 := by
    rw [PMF.toOuterMeasure_apply, ← P.tsum_coe, tsum_option ENNReal.summable,
      tsum_option ENNReal.summable]
    simp [Set.indicator_apply]
  have hfin1 : P none ≠ ⊤ := P.apply_ne_top none
  have hfin2 : P.toOuterMeasure {o | o.isSome} ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hpart
    exact ENNReal.top_ne_one hpart
  have hreal : (P none).toReal + (P.toOuterMeasure {o | o.isSome}).toReal = 1 := by
    rw [← ENNReal.toReal_add hfin1 hfin2, hpart, ENNReal.toReal_one]
  linarith

end RecursiveRecognition

end

#print axioms unimodal_gaussian_progression_bounds
#print axioms gaussian_residue_class_prob_sharp
#print axioms gaussian_residue_class_prob_interval
#print axioms gaussian_residue_class_prob_unimodal
#print axioms single_root_progression_conditioning
#print axioms mahalanobis_norm_sq
#print axioms mahalanobis_tile_radius_lip
#print axioms mahalanobis_2d_lattice_mass_bounds
#print axioms mahalanobis_2d_lattice_mass_half
#print axioms continuous_inner_ellipse_mass_le
#print axioms mahalanobis_2d_inner_ellipse_mass_le
#print axioms mahalanobis_2d_discarded_radius_rpow_le
#print axioms primeFactors_card_le_log2
#print axioms dyadic_rich_hasse_primes_mul_le
#print axioms dyadic_exceptional_fraction_le
#print axioms dyadic_hasse_exceptional_fraction_le
#print axioms dyadic_prime_supply_eventually
#print axioms dyadic_exceptional_fraction_from_critical_line
#print axioms exceptional_band_weight_sum_le
#print axioms recursiveEllipticFactor_sound
#print axioms recursiveEllipticFactor_fail_le_cardFactors
#print axioms recursiveEllipticFactor_fail_le_log2
#print axioms twoStageRecognizer_sound
#print axioms twoStageRecognizer_fail_le
#print axioms twoStageRecognizer_success_ge

end Cogentic.RandomizedEllipticAndGaussian

