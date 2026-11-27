import Mathlib
import Cogentic.RandomizedPrimeBinLogTwist
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronKernel

/-! Transfer from a finite Dirichlet polynomial to a sharp prefix of its integer support. -/

open Complex MeasureTheory
open scoped BigOperators

namespace Cogentic

/-- The finite Dirichlet polynomial with coefficients on the integer support `P`. -/
noncomputable def productDirichletPolynomial (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ P, a n / (n : ℂ) ^ s

def perronLine (c t : ℝ) : ℂ := (c : ℂ) + t * I

/-- The truncated vertical integral for a finite Dirichlet polynomial. -/
noncomputable def productPerronIntegral (P : Finset ℕ) (a : ℕ → ℂ) (x c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
    productDirichletPolynomial P a (perronLine c t) * (x : ℂ) ^ perronLine c t /
      perronLine c t)

private noncomputable def perronKernel (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ perronLine c t / perronLine c t)

private theorem perronLine_continuous (c : ℝ) : Continuous (perronLine c) := by
  unfold perronLine
  fun_prop

private theorem perronLine_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : perronLine c t ≠ 0 :=
  GlobalTheory.PerronKernel.ne_zero_of_re hc.ne'

private theorem kernel_continuous {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Continuous (fun t => (y : ℂ) ^ perronLine c t / perronLine c t) :=
  ((perronLine_continuous c).const_cpow (Or.inl (by exact_mod_cast hy.ne'))).div
    (perronLine_continuous c) (perronLine_ne_zero hc)

/-- Interchanging a finite support with the truncated vertical integral. -/
private theorem productPerronIntegral_eq_sum (P : Finset ℕ) (a : ℕ → ℂ)
    {x c T : ℝ} (hx : 0 < x) (hc : 0 < c) (hP : ∀ n ∈ P, 0 < n) :
    productPerronIntegral P a x c T = ∑ n ∈ P, a n * perronKernel (x / n) c T := by
  classical
  unfold productPerronIntegral perronKernel
  have heq (t : ℝ) :
      productDirichletPolynomial P a (perronLine c t) * (x : ℂ) ^ perronLine c t /
        perronLine c t =
      ∑ n ∈ P, a n * (((x / (n : ℝ) : ℝ) : ℂ) ^ perronLine c t / perronLine c t) := by
    unfold productDirichletPolynomial
    rw [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hP n hn
    have harg : ((n : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hn0.le]
      exact Real.pi_ne_zero.symm
    rw [div_eq_mul_inv x, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.2 hn0.le),
      Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.ofReal_natCast]
    ring
  have hi := intervalIntegral.integral_congr (a := -T) (b := T) (μ := volume)
    (fun t _ => heq t)
  rw [hi, intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_const_mul]
    ring
  · intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hP n hn
    exact ((kernel_continuous (div_pos hx hn0) hc).const_mul (a n)).intervalIntegrable _ _

private theorem log_ratio_lower {X x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxX : x ≤ 2 * X) (hyX : y ≤ 2 * X) (hgap : 1 / 2 ≤ |x - y|) :
    1 ≤ 4 * X * |Real.log (x / y)| := by
  by_cases hxy : x ≤ y
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hx hy)
    have hlogneg : Real.log (x / y) ≤ 0 := by
      have : x / y ≤ 1 := (div_le_one hy).2 hxy
      linarith
    rw [abs_of_nonpos hlogneg]
    rw [abs_of_nonpos (sub_nonpos.2 hxy)] at hgap
    have hlin : 1 / 2 ≤ y * (-Real.log (x / y)) := by
      have hm := mul_le_mul_of_nonneg_left hlog hy.le
      have hc : y * (x / y) = x := by field_simp
      rw [mul_sub, hc, mul_one] at hm
      linarith
    have := mul_le_mul_of_nonneg_right hyX (neg_nonneg.2 hlogneg)
    linarith
  · have hyx : y ≤ x := (lt_of_not_ge hxy).le
    have hlog := Real.log_le_sub_one_of_pos (div_pos hy hx)
    have hlogeq : Real.log (y / x) = -Real.log (x / y) := by
      rw [Real.log_div hy.ne' hx.ne', Real.log_div hx.ne' hy.ne']
      ring
    have hlogpos : 0 ≤ Real.log (x / y) := by
      have : y / x ≤ 1 := (div_le_one hx).2 hyx
      rw [hlogeq] at hlog
      linarith
    rw [abs_of_nonneg hlogpos]
    rw [abs_of_nonneg (sub_nonneg.2 hyx)] at hgap
    have hlin : 1 / 2 ≤ x * Real.log (x / y) := by
      have hm := mul_le_mul_of_nonneg_left hlog hx.le
      have hc : x * (y / x) = y := by field_simp
      rw [mul_sub, hc, mul_one, hlogeq, mul_neg] at hm
      linarith
    have := mul_le_mul_of_nonneg_right hxX hlogpos
    linarith

/-- The half-integer cutoff has a uniform inverse-square truncation error at height
`X³` and abscissa `1 / log X` for integer support in `[X, 2X]`. -/
theorem product_perron_prefix_error :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℝ) (P : Finset ℕ) (a : ℕ → ℂ) (m : ℕ),
      2 ≤ X → X ≤ (m : ℝ) + 1 / 2 → (m : ℝ) + 1 / 2 ≤ 2 * X →
      (∀ n ∈ P, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) →
      ‖productPerronIntegral P a ((m : ℝ) + 1 / 2) (1 / Real.log X) (X ^ 3)
          - ∑ n ∈ P.filter (· ≤ m), a n‖ ≤
        (K / X ^ 2) * ∑ n ∈ P, ‖a n‖ := by
  obtain ⟨C, hC, hK⟩ := GlobalTheory.PerronKernel.truncated_perron_kernel
  refine ⟨4 * C * Real.exp 1, by positivity, ?_⟩
  intro X P a m hX hXm hmX hP
  let x : ℝ := (m : ℝ) + 1 / 2
  let c : ℝ := 1 / Real.log X
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hx : 0 < x := hX0.trans_le hXm
  have hc : 0 < c := one_div_pos.2 (Real.log_pos hX1)
  have hT : 1 ≤ X ^ 3 := one_le_pow₀ hX1.le
  have hsupport (n : ℕ) (hn : n ∈ P) : 0 < n := by
    have : (0 : ℝ) < n := hX0.trans_le (hP n hn).1
    exact_mod_cast this
  change ‖productPerronIntegral P a x c (X ^ 3)
          - ∑ n ∈ P.filter (· ≤ m), a n‖ ≤ _
  rw [productPerronIntegral_eq_sum P a hx hc hsupport, Finset.sum_filter, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hsupport n hn
  have hy : 0 < x / n := div_pos hx hn0
  have hside : (1 : ℝ) < x / n ↔ n ≤ m := by
    rw [lt_div_iff₀ hn0, one_mul]
    constructor
    · intro h
      by_contra! hnm
      have hs : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hnm
      dsimp [x] at h
      linarith
    · intro h
      have hs : (n : ℝ) ≤ m := by exact_mod_cast h
      dsimp [x]
      linarith
  have hgap : 1 / 2 ≤ |x - n| := by
    by_cases h : n ≤ m
    · have hs : (n : ℝ) ≤ m := by exact_mod_cast h
      exact (show 1 / 2 ≤ x - n by dsimp [x]; linarith).trans (le_abs_self _)
    · have hs : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge h)
      exact (show 1 / 2 ≤ -(x - n) by dsimp [x]; linarith).trans (neg_le_abs _)
  have hlog := log_ratio_lower hx hn0 hmX (hP n hn).2 hgap
  have hy1 : x / n ≠ 1 := by
    intro he
    rw [he, Real.log_one, abs_zero, mul_zero] at hlog
    linarith
  have hloglower : X ^ 2 / 4 ≤ X ^ 3 * |Real.log (x / n)| := by
    have hm := mul_le_mul_of_nonneg_left hlog (sq_nonneg X)
    nlinarith only [hm]
  have hmin : min 1 (1 / (X ^ 3 * |Real.log (x / n)|)) ≤ 4 / X ^ 2 := by
    refine (min_le_right _ _).trans ?_
    have he : 0 < X ^ 2 / 4 := by positivity
    calc
      _ ≤ 1 / (X ^ 2 / 4) := one_div_le_one_div_of_le he hloglower
      _ = _ := by ring
  have hpow : (x / n) ^ c ≤ Real.exp 1 := by
    have ht : x / n ≤ 2 :=
      (div_le_iff₀ hn0).2 (hmX.trans (mul_le_mul_of_nonneg_left (hP n hn).1 (by norm_num)))
    have hle : x / n ≤ X := ht.trans hX
    calc
      _ ≤ X ^ c := Real.rpow_le_rpow hy.le hle hc.le
      _ = _ := by
        rw [Real.rpow_def_of_pos hX0]
        congr 1
        dsimp [c]
        exact mul_one_div_cancel (Real.log_pos hX1).ne'
  have hkernel := hK (x / n) c (X ^ 3) hy hy1 hc hT
  change ‖perronKernel (x / n) c (X ^ 3) - (if 1 < x / n then 1 else 0)‖ ≤ _ at hkernel
  simp only [hside] at hkernel
  have he : (if n ≤ m then a n else 0) = a n * (if n ≤ m then 1 else 0) := by
    split_ifs <;> simp
  rw [he, ← mul_sub, norm_mul]
  calc
    _ ≤ ‖a n‖ * (C * (x / n) ^ c * min 1 (1 / (X ^ 3 * |Real.log (x / n)|))) :=
      mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
    _ ≤ ‖a n‖ * (C * Real.exp 1 * (4 / X ^ 2)) := by gcongr
    _ = _ := by ring

#print axioms product_perron_prefix_error

/-- The vertical denominator contributes a logarithm as the contour gets taller. -/
theorem product_perron_vertical_l1 {c T : ℝ} (hc : 0 < c) (hT : c ≤ T) :
    (∫ t in (-T)..T, ‖(perronLine c t)⁻¹‖) ≤ 2 * (1 + Real.log (T / c)) := by
  let f : ℝ → ℝ := fun t => ‖(perronLine c t)⁻¹‖
  have hcont : Continuous f :=
    ((perronLine_continuous c).inv₀ (perronLine_ne_zero hc)).norm
  have heven (t : ℝ) : f (-t) = f t := by
    simp [f, norm_inv, Complex.norm_def, Complex.normSq_apply, perronLine]
  have hneg : (∫ t in (-T)..0, f t) = ∫ t in (0 : ℝ)..T, f t := by
    have heq : (∫ t in (0 : ℝ)..T, f (-t)) = ∫ t in (0 : ℝ)..T, f t :=
      intervalIntegral.integral_congr (fun t _ => heven t)
    rw [intervalIntegral.integral_comp_neg, neg_zero] at heq
    exact heq
  have hhead : (∫ t in (0 : ℝ)..c, f t) ≤ 1 := by
    have hle := intervalIntegral.integral_mono_on (μ := volume) hc.le (hcont.intervalIntegrable _ _)
      (intervalIntegrable_const (c := c⁻¹)) (fun t _ => by
        have hnorm : c ≤ ‖perronLine c t‖ := by
          simpa [perronLine] using Complex.re_le_norm (perronLine c t)
        exact (norm_inv _).trans_le (inv_anti₀ hc hnorm))
    simpa [intervalIntegral.integral_const, hc.ne'] using hle
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume c T := by
    refine ContinuousOn.intervalIntegrable ?_
    apply continuousOn_id.inv₀
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact (hc.trans_le ht.1).ne'
  have htail : (∫ t in c..T, f t) ≤ Real.log (T / c) := by
    rw [← integral_inv_of_pos hc (hc.trans_le hT)]
    apply intervalIntegral.integral_mono_on hT (hcont.intervalIntegrable _ _) hinv
    intro t ht
    have hpos := hc.trans_le ht.1
    have hnorm : t ≤ ‖perronLine c t‖ := by
      simpa [perronLine, abs_of_pos hpos] using Complex.abs_im_le_norm (perronLine c t)
    exact (norm_inv _).trans_le (inv_anti₀ hpos hnorm)
  change (∫ t in (-T)..T, f t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hneg,
    ← intervalIntegral.integral_add_adjacent_intervals (b := c)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  linarith

/-- A uniform estimate on the full Dirichlet polynomial along the truncated line
controls its Perron integral with the explicit logarithmic loss. -/
theorem product_perron_integral_norm_le (P : Finset ℕ) (a : ℕ → ℂ) {x c T M : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : c ≤ T) (hM : 0 ≤ M) (hP : ∀ n ∈ P, 0 < n)
    (hpoly : ∀ t ∈ Set.Icc (-T) T, ‖productDirichletPolynomial P a (perronLine c t)‖ ≤ M) :
    ‖productPerronIntegral P a x c T‖ ≤ (M * x ^ c / Real.pi) * (1 + Real.log (T / c)) := by
  have hab : -T ≤ T := by linarith
  have hcont : Continuous (fun t => productDirichletPolynomial P a (perronLine c t)) := by
    unfold productDirichletPolynomial
    refine continuous_finsetSum _ ?_
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hP n hn).ne'
    apply continuous_const.div ((perronLine_continuous c).const_cpow (Or.inl hn0))
    intro t
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)
  let f : ℝ → ℂ :=
    fun t => productDirichletPolynomial P a (perronLine c t) * (x : ℂ) ^ perronLine c t /
      perronLine c t
  have hf : Continuous f := by
    change Continuous (fun t => _ * _ / _)
    have hcx := (perronLine_continuous c).const_cpow (b := (x : ℂ))
      (Or.inl (by exact_mod_cast hx.ne'))
    exact (hcont.mul hcx).div (perronLine_continuous c) (perronLine_ne_zero hc)
  let g : ℝ → ℝ := fun t => (M * x ^ c) * ‖(perronLine c t)⁻¹‖
  have hg : Continuous g := continuous_const.mul
    ((perronLine_continuous c).inv₀ (perronLine_ne_zero hc)).norm
  have hpt : ∀ t ∈ Set.Icc (-T) T, ‖f t‖ ≤ g t := by
    intro t ht
    have hs : (perronLine c t).re = c := by simp [perronLine]
    dsimp only [f, g]
    rw [div_eq_mul_inv, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (hpoly t ht) (Real.rpow_nonneg hx.le _)
  have hbound : ‖∫ t in (-T)..T, f t‖ ≤ (M * x ^ c) * (2 * (1 + Real.log (T / c))) := by
    calc
      _ ≤ ∫ t in (-T)..T, ‖f t‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in (-T)..T, g t := intervalIntegral.integral_mono_on hab
        (hf.norm.intervalIntegrable _ _) (hg.intervalIntegrable _ _) hpt
      _ = (M * x ^ c) * ∫ t in (-T)..T, ‖(perronLine c t)⁻¹‖ :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (product_perron_vertical_l1 hc hT) (by positivity)
  unfold productPerronIntegral
  change ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, f t)‖ ≤ _
  have hfactor : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_mul, hfactor]
  calc
    _ ≤ 1 / (2 * Real.pi) * ((M * x ^ c) * (2 * (1 + Real.log (T / c)))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

#print axioms product_perron_integral_norm_le

/-- A line bound transfers to the sharp prefix, with an explicit logarithmic loss
and an inverse-square error times the coefficient mass. -/
theorem product_perron_prefix_norm_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℝ) (P : Finset ℕ) (a : ℕ → ℂ) (m : ℕ) (M : ℝ),
      2 ≤ X → Real.exp 1 ≤ X →
      X ≤ (m : ℝ) + 1 / 2 → (m : ℝ) + 1 / 2 ≤ 2 * X →
      (∀ n ∈ P, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) → 0 ≤ M →
      (∀ t ∈ Set.Icc (-(X ^ 3)) (X ^ 3),
        ‖productDirichletPolynomial P a (perronLine (1 / Real.log X) t)‖ ≤ M) →
      ‖∑ n ∈ P.filter (· ≤ m), a n‖ ≤
        (4 * Real.exp 2 / Real.pi) * (M * Real.log X) +
          (K / X ^ 2) * ∑ n ∈ P, ‖a n‖ := by
  obtain ⟨K, hK, herr⟩ := product_perron_prefix_error
  refine ⟨K, hK, ?_⟩
  intro X P a m M hX heX hXm hmX hP hM hpoly
  let c := 1 / Real.log X
  let x : ℝ := (m : ℝ) + 1 / 2
  have hX0 : 0 < X := by linarith
  have hx : 0 < x := hX0.trans_le hXm
  have hlog : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 heX
  have hlog0 : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hc : 0 < c := one_div_pos.2 hlog0
  have hT : c ≤ X ^ 3 := calc
    c ≤ 1 := (div_le_one hlog0).2 hlog
    _ ≤ _ := one_le_pow₀ (by linarith)
  have hsupport (n : ℕ) (hn : n ∈ P) : 0 < n := by
    have : (0 : ℝ) < n := hX0.trans_le (hP n hn).1
    exact_mod_cast this
  have hpow : x ^ c ≤ Real.exp 2 := by
    have hx2 : x ≤ X ^ 2 := hmX.trans (by nlinarith [mul_nonneg hX0.le (sub_nonneg.2 hX)])
    have hlogx := (Real.log_le_log_iff hx (sq_pos_of_pos hX0)).2 hx2
    rw [Real.log_pow, Nat.cast_ofNat] at hlogx
    rw [Real.rpow_def_of_pos hx, Real.exp_le_exp]
    change Real.log x * (1 / Real.log X) ≤ 2
    rw [mul_one_div, div_le_iff₀ hlog0]
    exact hlogx
  have hheight : 1 + Real.log (X ^ 3 / c) ≤ 4 * Real.log X := by
    have heq : X ^ 3 / c = X ^ 3 * Real.log X := by
      simp [c, div_eq_mul_inv]
    rw [heq, Real.log_mul (pow_ne_zero _ hX0.ne') hlog0.ne', Real.log_pow]
    norm_num
    linarith [Real.log_le_sub_one_of_pos hlog0]
  have hfactor := product_perron_integral_norm_le P a hx hc hT hM hsupport hpoly
  have hband : ‖productPerronIntegral P a x c (X ^ 3)‖ ≤
      (4 * Real.exp 2 / Real.pi) * (M * Real.log X) := by
    refine hfactor.trans ?_
    calc
      _ ≤ (M * Real.exp 2 / Real.pi) * (4 * Real.log X) := by
        have h0 : 0 ≤ 1 + Real.log (X ^ 3 / c) := by
          have hq : 1 ≤ X ^ 3 / c := (le_div_iff₀ hc).2 (by simpa using hT)
          linarith [Real.log_nonneg hq]
        gcongr
      _ = _ := by ring
  let z := productPerronIntegral P a x c (X ^ 3)
  let w := ∑ n ∈ P.filter (· ≤ m), a n
  have hw : w = z + -(z - w) := by abel
  change ‖w‖ ≤ _
  calc
    ‖w‖ = ‖z + -(z - w)‖ := congrArg norm hw
    _ ≤ ‖z‖ + ‖z - w‖ := by simpa only [norm_neg] using norm_add_le z (-(z - w))
    _ ≤ _ := add_le_add hband (herr X P a m hX hXm hmX hP)

#print axioms product_perron_prefix_norm_le

namespace Randomized

/-- Disjoint prime bins give a multiplicative Dirichlet polynomial at every complex argument. -/
theorem primeBinProducts_dirichletPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ) (s : ℂ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) :
    productDirichletPolynomial (primeBinProducts A B) (fun n ↦ χ n) s =
      ∏ i, ∑ p ∈ primeBin (A i) (B i), χ p / (p : ℂ) ^ s := by
  let f : ℕ →* ℂ :=
    { toFun := fun n ↦ χ n / (n : ℂ) ^ s
      map_one' := by simp
      map_mul' := by
        intro m n
        simp only [Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow, mul_div_mul_comm] }
  unfold productDirichletPolynomial
  rw [primeBinProducts, Finset.sum_image (primeBin_product_injOn A B hdisj)]
  change ∑ p ∈ Fintype.piFinset (fun i ↦ primeBin (A i) (B i)), f (∏ i, p i) =
    ∏ i, ∑ p ∈ primeBin (A i) (B i), f p
  simp_rw [map_prod]
  exact (Finset.prod_univ_sum _ (fun _ p ↦ f p)).symm

/-- Uniform bin bounds on the contour transfer to a sharp prefix of the distinct product set. -/
theorem primeBinProducts_prefix_norm_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℝ) (m : ℕ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ) (H : ι → ℝ),
      2 ≤ X → Real.exp 1 ≤ X →
      X ≤ (m : ℝ) + 1 / 2 → (m : ℝ) + 1 / 2 ≤ 2 * X →
      (∀ n ∈ primeBinProducts A B, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) →
      (Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      (∀ i, 0 ≤ H i) →
      (∀ i t, t ∈ Set.Icc (-(X ^ 3)) (X ^ 3) →
        ‖∑ p ∈ primeBin (A i) (B i), χ p / (p : ℂ) ^ perronLine (1 / Real.log X) t‖ ≤ H i) →
      ‖∑ n ∈ (primeBinProducts A B).filter (· ≤ m), χ n‖ ≤
        (4 * Real.exp 2 / Real.pi) * ((∏ i, H i) * Real.log X) +
          (K / X ^ 2) * (primeBinProducts A B).card := by
  obtain ⟨K, hK, bound⟩ := product_perron_prefix_norm_le
  refine ⟨K, hK, ?_⟩
  intro X m q _ χ ι _ _ A B H hX heX hXm hmX hP hdisj hH hbins
  have hM : 0 ≤ ∏ i, H i := Finset.prod_nonneg (fun i _ ↦ hH i)
  have hline (t : ℝ) (ht : t ∈ Set.Icc (-(X ^ 3)) (X ^ 3)) :
      ‖productDirichletPolynomial (primeBinProducts A B) (fun n ↦ χ n)
          (perronLine (1 / Real.log X) t)‖ ≤ ∏ i, H i := by
    rw [primeBinProducts_dirichletPolynomial χ A B _ hdisj, norm_prod]
    exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hbins i t ht)
  refine (bound X (primeBinProducts A B) (fun n ↦ χ n) m _ hX heX hXm hmX hP hM hline).trans ?_
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ _n ∈ primeBinProducts A B, (1 : ℝ) := Finset.sum_le_sum fun n _ ↦ χ.norm_le_one n
    _ = _ := by simp

#print axioms primeBinProducts_prefix_norm_le

/-- Square-root bounds for sharp prefixes of a disjoint prime-product set,
with truncation measured against the full cardinality. -/
def PrimeBinProductPrefixBound : Prop :=
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (X : ℝ) (m : ℕ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
      2 ≤ X → Real.exp 1 ≤ X →
      X ≤ (m : ℝ) + 1 / 2 → (m : ℝ) + 1 / 2 ≤ 2 * X →
      (∀ n ∈ primeBinProducts A B, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) →
      (Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
      ‖∑ n ∈ (primeBinProducts A B).filter (· ≤ m), χ n‖ ≤
        (4 * Real.exp 2 / Real.pi) *
          ((∏ i, C * Real.sqrt (B i) *
            (1 + Real.log (q * ((B i : ℝ) + X ^ 3 + 2))) ^ 3) * Real.log X) +
          (K / X ^ 2) * (primeBinProducts A B).card

/-- The log-twisted prime theorem supplies the needed line bounds uniformly
through height `X³`. -/
theorem primeBin_product_prefix_from_critical_line (line : DirichletLZerosOnLine) :
    PrimeBinProductPrefixBound := by
  obtain ⟨C, hC, hbin⟩ := primeBin_mellin_from_critical_line line
  obtain ⟨K, hK, hprefix⟩ := primeBinProducts_prefix_norm_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro X m q _ χ hχ ι _ _ A B hX heX hXm hmX hP hdisj hB hAB
  let H (i : ι) : ℝ := C * Real.sqrt (B i) *
    (1 + Real.log (q * ((B i : ℝ) + X ^ 3 + 2))) ^ 3
  refine hprefix X m q χ A B H hX heX hXm hmX hP hdisj ?_ ?_
  all_goals
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
    have hq₀ : (0 : ℝ) ≤ q := by positivity
    have hlogArg (i : ι) (u : ℝ) (hu : 0 ≤ u) : 1 ≤ (q : ℝ) * ((B i : ℝ) + u + 2) := by
      apply one_le_mul_of_one_le_of_one_le hq
      have : (0 : ℝ) ≤ B i := by positivity
      linarith
  · intro i
    dsimp only [H]
    have hlog := Real.log_nonneg (hlogArg i (X ^ 3) (by positivity))
    positivity
  · intro i t ht
    have hTabs : |t| ≤ X ^ 3 := abs_le.mpr ht
    have hX1 : 1 < X := by linarith
    have ht₀ : 0 ≤ 1 + Real.log (q * ((B i : ℝ) + |t| + 2)) := by
      linarith [Real.log_nonneg (hlogArg i |t| (abs_nonneg t))]
    have htlog : Real.log (q * ((B i : ℝ) + |t| + 2)) ≤
        Real.log (q * ((B i : ℝ) + X ^ 3 + 2)) := by
      apply Real.log_le_log (zero_lt_one.trans_le (hlogArg i |t| (abs_nonneg t)))
      exact mul_le_mul_of_nonneg_left (by linarith) hq₀
    have hline := hbin q χ hχ (A i) (B i) (1 / Real.log X) t (hB i) (hAB i)
      (one_div_nonneg.mpr (Real.log_nonneg hX1.le))
    refine hline.trans ?_
    dsimp only [H]
    gcongr

#print axioms primeBin_product_prefix_from_critical_line

end Randomized

end Cogentic
