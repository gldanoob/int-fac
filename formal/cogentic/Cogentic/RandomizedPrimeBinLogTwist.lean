import Cogentic.RandomizedPrimeBinBias
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronOfLeTwoVonMangoldt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip

namespace Cogentic.Randomized

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Set
open scoped Interval

private theorem zero_re_le_half (line : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {z : ℂ} (hz : LFunction χ z = 0) :
    z.re ≤ 1 / 2 := by
  by_contra! h
  by_cases hh : 1 ≤ z.re
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hh hz
  · exact (ne_of_gt h) (line q χ z (by linarith) (lt_of_not_ge hh) hz)

private theorem logDeriv_bound_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (s : ℂ) (d : ℝ), 0 < d → 1/2 + d ≤ s.re → s.re ≤ 2 →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
        K * Real.log (q * (|s.im| + 2)) * (1 + 1/d) := by
  obtain ⟨K, hK, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨K, hK, fun q _ χ hχ s d hd hlow hhi => ?_⟩
  have hne : LFunction χ s ≠ 0 := fun hz => by
    linarith [zero_re_le_half line hχ hz]
  obtain ⟨hfin, hcount, herr⟩ := H q χ hχ s (by linarith) hhi hne
  let Z := hfin.toFinset
  let a (w : ℂ) := analyticOrderNatAt (LFunction χ) w
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount herr
  change (∑ w ∈ Z, (a w : ℝ)) ≤ _ at hcount
  change ‖deriv (LFunction χ) s / LFunction χ s - ∑ w ∈ Z, (a w : ℂ) / (s - w)‖ ≤ _ at herr
  have bound : ‖∑ w ∈ Z, (a w : ℂ) / (s - w)‖ ≤ K * Real.log (q * (|s.im| + 2)) / d := by
    refine (norm_sum_le _ _).trans ?_
    apply le_trans _ (div_le_div_of_nonneg_right hcount hd.le)
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro w hw
    have hw' := (hfin.mem_toFinset.mp hw).2
    rw [norm_div]
    simp only [Complex.norm_natCast]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd
    exact (by simp only [sub_re]; linarith [zero_re_le_half line hχ hw'] :
      d ≤ (s - w).re).trans (Complex.re_le_norm _)
  calc
    _ = ‖(deriv (LFunction χ) s / LFunction χ s - ∑ w ∈ Z, (a w : ℂ) / (s - w)) +
        ∑ w ∈ Z, (a w : ℂ) / (s - w)‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le ..
    _ ≤ _ := add_le_add herr bound
    _ = _ := by ring

private noncomputable def mellinPoint (σ v : ℝ) : ℂ := σ + v * I

@[simp] private theorem mellinPoint_re (σ v : ℝ) : (mellinPoint σ v).re = σ := by
  simp [mellinPoint]

@[simp] private theorem mellinPoint_im (σ v : ℝ) : (mellinPoint σ v).im = v := by
  simp [mellinPoint]

private theorem vertical_inverse_integral {T : ℝ} (hT : 0 ≤ T) :
    ∫ v in -T..T, (1 + |v|)⁻¹ = 2 * Real.log (1 + T) := by
  have cont : Continuous fun v : ℝ => (1 + |v|)⁻¹ :=
    (continuous_const.add continuous_abs).inv₀ (fun v => by dsimp; positivity)
  have half : (∫ v in (0 : ℝ)..T, (1 + |v|)⁻¹) = Real.log (1 + T) := by
    calc
      _ = ∫ v in (0 : ℝ)..T, (1 + v)⁻¹ := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hT]
        intro v hv
        simp only [abs_of_nonneg hv.1]
      _ = _ := by
        have h (v : ℝ) (hv : v ∈ [[(0 : ℝ), T]]) :
            HasDerivAt (fun v => Real.log (1 + v)) (1 + v)⁻¹ v := by
          rw [uIcc_of_le hT] at hv
          simpa using (((hasDerivAt_id' v).const_add 1).log
            (show (1 + v : ℝ) ≠ 0 by linarith [hv.1]))
        have integrable : IntervalIntegrable (fun v : ℝ => (1 + v)⁻¹) volume 0 T := by
          apply ContinuousOn.intervalIntegrable
          apply (continuous_const.add continuous_id).continuousOn.inv₀
          rw [uIcc_of_le hT]
          intro v hv
          change (1 + v : ℝ) ≠ 0
          linarith [hv.1]
        simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt h integrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (cont.intervalIntegrable _ _)
    (cont.intervalIntegrable _ _) (b := 0), half]
  have h := intervalIntegral.integral_comp_neg (f := fun v : ℝ => (1 + |v|)⁻¹) (a := 0) (b := T)
  simp only [abs_neg, neg_zero] at h
  rw [← h, half]
  ring

private theorem norm_vertical_integral {F : ℂ → ℂ} {a T M : ℝ} (ha : 1/2 ≤ a)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hF : ∀ v ∈ Icc (-T) T,
      ‖F (mellinPoint a v)‖ ≤ M / ‖mellinPoint a v‖) :
    ‖∫ v in -T..T, F (mellinPoint a v)‖ ≤ 8 * M * Real.log (1 + T) := by
  have cont : Continuous fun v : ℝ => (1 + |v|)⁻¹ :=
    (continuous_const.add continuous_abs).inv₀ (fun v => by dsimp; positivity)
  have hle : -T ≤ T := by linarith
  apply (intervalIntegral.norm_integral_le_of_norm_le hle
    (g := fun v => (4 * M) * (1 + |v|)⁻¹) ?_ ((cont.const_mul _).intervalIntegrable _ _)).trans_eq
  swap
  · apply Filter.Eventually.of_forall
    intro v hv
    have h := Complex.re_le_norm (mellinPoint a v)
    have hi := Complex.abs_im_le_norm (mellinPoint a v)
    rw [mellinPoint_re] at h
    rw [mellinPoint_im] at hi
    have hp : 0 < ‖mellinPoint a v‖ := by linarith
    apply (hF v ⟨hv.1.le, hv.2⟩).trans
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ hp (by positivity)).2
    nlinarith [mul_nonneg hM (show 0 ≤ 4 * ‖mellinPoint a v‖ - (1 + |v|) by linarith)]
  · rw [intervalIntegral.integral_const_mul, vertical_inverse_integral hT]
    ring


private noncomputable def mangoldtLogTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (n : ℕ) : ℂ := χ n * (vonMangoldt n : ℂ) * (n : ℂ)^(-(t : ℂ) * I)

private theorem norm_logTwist (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖(n : ℂ)^(-(t : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

private theorem mangoldtLogTwist_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ‖mangoldtLogTwist χ t n‖ ≤ vonMangoldt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mangoldtLogTwist]
  · rw [mangoldtLogTwist, norm_mul, norm_mul, norm_logTwist t hn, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)

private theorem LSeries_mangoldtLogTwist {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (mangoldtLogTwist χ t) s =
      -deriv (LFunction χ) (s + t * I) / LFunction χ (s + t * I) := by
  have hr : 1 < (s + t * I).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hr, deriv_LFunction_eq_deriv_LSeries χ hr,
    ← LSeries_twist_vonMangoldt_eq χ hr]
  unfold LSeries
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  simp only [LSeries.term, hn.ne', if_false, mangoldtLogTwist, Pi.mul_apply]
  have nz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Complex.cpow_add _ _ nz, neg_mul, Complex.cpow_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem contour_logDeriv_bound (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (u t : ℝ), 1 ≤ Real.log u → 0 < u →
      let c := 1 + 1 / Real.log u
      ‖∫ v in -u..u, LSeries (mangoldtLogTwist χ t) (mellinPoint c v) *
        (u : ℂ)^(mellinPoint c v) / mellinPoint c v‖ ≤
          K * (Real.sqrt u) * (1 + Real.log (q * (u + |t| + 2)))^3 := by
  obtain ⟨K, hK, H⟩ := logDeriv_bound_from_critical_line line
  refine ⟨(24 * Real.exp (1/2) + 6 * Real.exp 1) * K, by positivity, ?_⟩
  intro q _ χ hχ u t hlu hu
  let L := Real.log u
  let c := 1 + 1 / L
  -- Shift only the log derivative so Perron keeps the denominator on its original contour.
  let d := 1 / (2 * L)
  let a := 1/2 + d
  let D := 1 + Real.log (q * (u + |t| + 2))
  let M := 3 * K * D^2
  let F (z : ℂ) := (-deriv (LFunction χ) (z + t * I) / LFunction χ (z + t * I)) *
    (u : ℂ)^z / z
  have hL : 0 < L := by dsimp [L]; linarith
  have hc : 1 < c := lt_add_of_pos_right _ (one_div_pos.mpr hL)
  have hd : 0 < d := by positivity
  have hdc : d ≤ 1/2 := by dsimp [d]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hca : c - a ≤ 1 := by
    have heq : 1 / L = 2 * d := by dsimp [d]; field_simp
    dsimp [c, a]
    rw [heq]
    linarith
  have hac : a ≤ c := by
    have ha : a ≤ 1 := by dsimp [a]; linarith
    exact ha.trans hc.le
  have hc2 : c ≤ 2 := by
    dsimp [c]
    linarith [(div_le_iff₀ hL).mpr (show (1 : ℝ) ≤ 1 * L by simpa [L] using hlu)]
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hlog : Real.log (q * (u + |t| + 2)) ≥ L := by
    apply Real.log_le_log hu
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) hu.le,
      mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hDL : L ≤ D := by dsimp [D]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (z : ℂ) (hzr : z.re ∈ Icc a c) (hzi : z.im ∈ Icc (-u) u) :
      ‖-deriv (LFunction χ) (z + t * I) / LFunction χ (z + t * I)‖ ≤ M := by
    rw [neg_div, norm_neg]
    have h := H q χ hχ (z + t * I) d hd (by simpa [a] using hzr.1)
      (by simpa using hzr.2.trans hc2)
    have ht : |(z + t * I).im| ≤ u + |t| := by
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      exact (abs_add_le ..).trans (add_le_add_left (abs_le.mpr hzi) _)
    have htlog : Real.log (q * (|(z + t * I).im| + 2)) ≤ D := by
      have := Real.log_le_log (show 0 < (q : ℝ) * (|(z + t * I).im| + 2) by positivity)
        (mul_le_mul_of_nonneg_left (add_le_add_left ht 2) (Nat.cast_nonneg q))
      exact this.trans (le_add_of_nonneg_left zero_le_one)
    have heq : 1 / d = 2 * L := by dsimp [d]; field_simp
    rw [heq] at h
    refine h.trans ?_
    dsimp [M]
    calc
      _ ≤ (K * D) * (3 * D) := mul_le_mul (mul_le_mul_of_nonneg_left htlog hK.le)
        (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hF (z : ℂ) (hzr : z.re ∈ Icc a c) (hzi : z.im ∈ Icc (-u) u) :
      ‖F z‖ ≤ M * Real.exp (L * z.re) / ‖z‖ := by
    dsimp only [F]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Real.rpow_def_of_pos hu]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hb z hzr hzi)
      (Real.exp_pos _).le) (norm_nonneg _)
  have hdiff : DifferentiableOn ℂ F
      ([[ (mellinPoint a (-u)).re, (mellinPoint c u).re ]] ×ℂ
       [[ (mellinPoint a (-u)).im, (mellinPoint c u).im ]]) := by
    simp only [mellinPoint_re, mellinPoint_im, uIcc_of_le hac, uIcc_of_le (show -u ≤ u by linarith)]
    intro z hz
    have hz₁ : 1/2 < z.re := by have h := hz.1.1; dsimp [a] at h; linarith
    have hn : LFunction χ (z + t * I) ≠ 0 := fun hz => by
      have h := zero_re_le_half line hχ hz
      simp at h
      linarith
    have hz₀ : z ≠ 0 := fun h => by rw [h, zero_re] at hz₁; linarith
    have hdiffL : Differentiable ℂ (LFunction χ) :=
      fun w => differentiableAt_LFunction χ w (Or.inr hχ)
    have hshift : Differentiable ℂ (fun z : ℂ => z + t * I) := differentiable_id.add_const _
    have hx : DifferentiableAt ℂ (fun z : ℂ => (u : ℂ)^z) z := by
      simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
      fun_prop
    exact (((((hdiffL.deriv.comp hshift).differentiableAt.neg).div
      ((hdiffL.comp hshift).differentiableAt) hn).mul hx).div
        differentiableAt_id hz₀).differentiableWithinAt
  have rect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    (mellinPoint a (-u)) (mellinPoint c u) hdiff
  simp only [mellinPoint_re, mellinPoint_im, smul_eq_mul] at rect
  have V := norm_vertical_integral (F := F) (a := a) (T := u)
    (M := M * Real.exp (L * a)) (by dsimp [a]; linarith) hu.le (by positivity)
    (fun v hv => by simpa using hF (mellinPoint a v) (by simpa only [mellinPoint_re] using (show a ∈ Icc a c from ⟨le_rfl, hac⟩)) (by simpa))
  have horizontal (v : ℝ) (hv : |v| = u) :
      ‖∫ σ in a..c, F (mellinPoint σ v)‖ ≤ M * Real.exp 1 := by
    have hv' : v ∈ Icc (-u) u := abs_le.mp hv.le
    have estimate (σ : ℝ) (hσ : σ ∈ Ι a c) :
        ‖F (mellinPoint σ v)‖ ≤ M * Real.exp 1 := by
      rw [uIoc_of_le hac] at hσ
      have h := hF (mellinPoint σ v) (by simpa using ⟨hσ.1.le, hσ.2⟩) (by simpa)
      rw [mellinPoint_re] at h
      have hnorm : u ≤ ‖mellinPoint σ v‖ := by
        simpa [hv] using Complex.abs_im_le_norm (mellinPoint σ v)
      have hcL : L * c = L + 1 := by dsimp [c]; field_simp
      have hexp : Real.exp (L * σ) ≤ u * Real.exp 1 := by
        rw [← Real.exp_log hu, ← Real.exp_add]
        exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hσ.2 hL.le).trans_eq hcL)
      refine h.trans ((div_le_iff₀ (hu.trans_le hnorm)).mpr ?_)
      calc
        _ ≤ M * (u * Real.exp 1) := mul_le_mul_of_nonneg_left hexp hM
        _ ≤ _ := by
          calc
            M * (u * Real.exp 1) = (M * Real.exp 1) * u := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const estimate).trans ?_
    rw [abs_of_nonneg (sub_nonneg.mpr hac)]
    exact mul_le_of_le_one_right (by positivity) hca
  have hV := GlobalTheory.PerronKernel.norm_le_three
    (x := ∫ v in -u..u, F (mellinPoint c v))
    (p := ∫ σ in a..c, F (mellinPoint σ u))
    (q := ∫ σ in a..c, F (mellinPoint σ (-u)))
    (r := ∫ v in -u..u, F (mellinPoint a v))
    (Or.inl (by simp only [mellinPoint]; linear_combination rect))
  have hright : (∫ v in -u..u, LSeries (mangoldtLogTwist χ t) (mellinPoint c v) *
      (u : ℂ)^(mellinPoint c v) / mellinPoint c v) = ∫ v in -u..u, F (mellinPoint c v) := by
    apply intervalIntegral.integral_congr
    intro v _
    dsimp [F]
    rw [LSeries_mangoldtLogTwist χ t (s := mellinPoint c v) (by simpa only [mellinPoint_re] using hc)]
  have hexp : Real.exp (L * a) = Real.sqrt u * Real.exp (1/2) := by
    have h : L * a = L * (1/2) + 1/2 := by dsimp [a, d]; field_simp <;> ring
    rw [h, Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu]
  have hlog' : Real.log (1 + u) ≤ D := by
    have := Real.log_le_log (show 0 < 1 + u by positivity)
      (show 1 + u ≤ (q : ℝ) * (u + |t| + 2) by
        nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) hu.le,
          mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)])
    dsimp [D]
    linarith
  have hu1 : 1 ≤ u := Real.one_le_exp_iff.mpr hL.le |>.trans_eq (Real.exp_log hu)
  change ‖∫ v in -u..u, LSeries (mangoldtLogTwist χ t) (mellinPoint c v) *
    (u : ℂ)^(mellinPoint c v) / mellinPoint c v‖ ≤ (24 * Real.exp (1/2) + 6 * Real.exp 1) *
      K * Real.sqrt u * D^3
  rw [hright]
  calc
    _ ≤ _ := hV
    _ ≤ M * Real.exp 1 + M * Real.exp 1 + 8 * (M * Real.exp (L * a)) * Real.log (1 + u) :=
      add_le_add (add_le_add (horizontal _ (abs_of_nonneg hu.le))
        (horizontal _ (by simp [abs_of_nonneg hu.le]))) V
    _ ≤ 2 * (M * Real.exp 1) * (Real.sqrt u * D) + 8 * (M * Real.exp (L * a)) * D := by
      apply add_le_add
      · rw [← two_mul]
        exact le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hu1) hD)
      · exact mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = _ := by rw [hexp]; dsimp [M]; ring


private theorem mangoldtLogTwist_prefix (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (u t : ℝ), 2 ≤ u →
        ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, mangoldtLogTwist χ t n‖ ≤
          K * Real.sqrt u * (1 + Real.log (q * (u + |t| + 2)))^3 := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.PerronCoeff.truncated_perron_of_le_two_vonMangoldt
  obtain ⟨K, hK, Kbound⟩ := contour_logDeriv_bound line
  refine ⟨Real.exp 1 + 2 * C + ‖(1 / (2 * Real.pi) : ℂ)‖ * K, by positivity, ?_⟩
  intro q _ χ hχ u t hu
  let D := 1 + Real.log (q * (u + |t| + 2))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hu₀ : 0 < u := by linarith
  have hsqrt : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr (by linarith)
  have hlog : Real.log u ≤ Real.log (q * (u + |t| + 2)) := by
    apply Real.log_le_log hu₀
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) hu₀.le,
      mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Real.log_nonneg (show 1 ≤ u by linarith)]
  have hmain : 1 ≤ Real.sqrt u * D^3 := one_le_mul_of_one_le_of_one_le hsqrt (one_le_pow₀ hD)
  by_cases hl : 1 ≤ Real.log u
  · let c := 1 + 1 / Real.log u
    let J : ℂ := ∫ v in -u..u, LSeries (mangoldtLogTwist χ t) (mellinPoint c v) *
      (u : ℂ)^(mellinPoint c v) / mellinPoint c v
    let P := ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, mangoldtLogTwist χ t n
    have E := H (mangoldtLogTwist χ t) u u (fun n =>
      (mangoldtLogTwist_bound χ t n).trans (by linarith [vonMangoldt_nonneg (n := n)])) hu le_rfl
    change ‖P - (1 / (2 * Real.pi) : ℂ) * J‖ ≤ _ at E
    rw [mul_div_cancel_left₀ _ hu₀.ne'] at E
    have hlogD : Real.log u ≤ D := by dsimp [D]; linarith
    have hsquares : Real.log u ^ 2 + Real.log u ≤ 2 * D^3 := by
      have hp := pow_le_pow_left₀ (show 0 ≤ Real.log u by linarith) hlogD 2
      have hd2 : D ≤ D^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ D) (sub_nonneg.mpr hD)]
      have hd3 : D^2 ≤ D^3 := by nlinarith only [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hD)]
      linarith
    have E' := E.trans (mul_le_mul_of_nonneg_left hsquares hC.le)
    have JB := Kbound q χ hχ u t hl hu₀
    change ‖J‖ ≤ K * Real.sqrt u * D^3 at JB
    change ‖P‖ ≤ _
    calc
      _ = ‖(P - (1 / (2 * Real.pi) : ℂ) * J) + (1 / (2 * Real.pi) : ℂ) * J‖ := by
        rw [sub_add_cancel]
      _ ≤ _ := norm_add_le ..
      _ ≤ C * (2 * D^3) + ‖(1 / (2 * Real.pi) : ℂ)‖ * (K * Real.sqrt u * D^3) := by
        rw [norm_mul]
        exact add_le_add E' (mul_le_mul_of_nonneg_left JB (norm_nonneg _))
      _ ≤ _ := by
        have hle := le_mul_of_one_le_left (show 0 ≤ C * (2 * D^3) by positivity) hsqrt
        dsimp only [D] at *
        nlinarith only [hle, mul_nonneg (Real.exp_pos 1).le (show 0 ≤ Real.sqrt u *
          (1 + Real.log (q * (u + |t| + 2)))^3 by positivity)]
  · have hsmall : u ≤ Real.exp 1 := by
      rw [← Real.exp_log hu₀]
      exact Real.exp_le_exp.mpr (le_of_not_ge hl)
    have term (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊u⌋₊) : ‖mangoldtLogTwist χ t n‖ ≤ 1 := by
      obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
      have hn₀ : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn₁)
      have hx : (n : ℝ) ≤ u := (Nat.cast_le.mpr hn₂).trans (Nat.floor_le hu₀.le)
      exact (mangoldtLogTwist_bound χ t n).trans
        ((vonMangoldt_le_log (n := n)).trans ((Real.log_le_log hn₀ hx).trans (le_of_not_ge hl)))
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ‖mangoldtLogTwist χ t n‖ := norm_sum_le ..
      _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℝ) := Finset.sum_le_sum term
      _ = (⌊u⌋₊ : ℝ) := by simp
      _ ≤ u := Nat.floor_le hu₀.le
      _ ≤ Real.exp 1 := hsmall
      _ ≤ _ := by
        have hpos : Real.exp 1 ≤ Real.exp 1 + 2 * C + ‖(1 / (2 * Real.pi) : ℂ)‖ * K := by
          linarith [mul_nonneg (norm_nonneg (1 / (2 * Real.pi) : ℂ)) hK.le]
        have hg := le_mul_of_one_le_right (Real.exp_pos 1).le hmain
        exact hg.trans (by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hpos (by positivity))

private noncomputable def primeLogTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (n : ℕ) : ℂ := if n.Prime then (Real.log n : ℂ) * (χ n * (n : ℂ)^(-(t : ℂ) * I)) else 0

private theorem primeLogTwist_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, mangoldtLogTwist χ t n) -
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, primeLogTwist χ t n)‖ ≤ 2 * Real.sqrt u * Real.log u := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (le_trans ?_ (Chebyshev.psi_sub_theta_le hu))
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
  have heq : Finset.Icc 1 ⌊u⌋₊ = Finset.Ioc 0 ⌊u⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← heq]
  apply Finset.sum_le_sum
  intro n _
  by_cases hn : n.Prime
  · simp [primeLogTwist, mangoldtLogTwist, hn, vonMangoldt_apply_prime hn, mul_comm, mul_left_comm]
  · simp only [primeLogTwist, hn, if_false, sub_zero, not_false_eq_true]
    exact mangoldtLogTwist_bound χ t n


private theorem primeLogTwist_prefix (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (B n : ℕ) (t : ℝ), 2 ≤ B → n ≤ B →
        ‖∑ i ∈ Finset.range (n+1), primeLogTwist χ t i‖ ≤
          K * Real.sqrt B * (1 + Real.log (q * ((B : ℝ) + |t| + 2)))^3 := by
  obtain ⟨K, hK, H⟩ := mangoldtLogTwist_prefix line
  refine ⟨K + 2, by positivity, ?_⟩
  intro q _ χ hχ B n t hB hnB
  let D := 1 + Real.log (q * ((B : ℝ) + |t| + 2))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hD : 1 ≤ D := by
    dsimp [D]
    have h := Real.log_nonneg (show 1 ≤ (q : ℝ) * ((B : ℝ) + |t| + 2) by
      nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t),
        mul_nonneg (sub_nonneg.mpr hq) (show (0 : ℝ) ≤ B by positivity)])
    linarith
  change _ ≤ (K + 2) * Real.sqrt B * D^3
  by_cases hn : 2 ≤ n
  · have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hr : (n : ℝ) ≤ B := by exact_mod_cast hnB
    have hep : Real.sqrt n ≤ Real.sqrt B := Real.sqrt_le_sqrt hr
    have Dn : 1 ≤ 1 + Real.log (q * ((n : ℝ) + |t| + 2)) := by
      have := Real.log_nonneg (show 1 ≤ (q : ℝ) * ((n : ℝ) + |t| + 2) by
        nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t),
          mul_nonneg (sub_nonneg.mpr hq) (show (0 : ℝ) ≤ n by positivity)])
      linarith
    have hdcomp : 1 + Real.log (q * ((n : ℝ) + |t| + 2)) ≤ D := by
      apply add_le_add_right
      apply Real.log_le_log (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg q)
    have E := (H q χ hχ n t hnr).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hep hK.le)
        (pow_le_pow_left₀ (by linarith) hdcomp 3) (by positivity) (by positivity))
    have hlog : Real.log n ≤ D^3 := by
      have h := Real.log_le_log (show (0 : ℝ) < n by linarith)
        (show (n : ℝ) ≤ q * ((n : ℝ) + |t| + 2) by
          nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t),
            mul_nonneg (sub_nonneg.mpr hq) (show (0 : ℝ) ≤ n by positivity)])
      have hpow : D ≤ D^3 := by
        calc
          D = D^1 := by rw [pow_one]
          _ ≤ _ := pow_le_pow_right₀ hD (by norm_num)
      exact (show Real.log n ≤ D by linarith).trans hpow
    have Ep := (primeLogTwist_tail χ t (show 1 ≤ (n : ℝ) by linarith)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hep (by norm_num)) hlog
        (Real.log_nonneg (by linarith)) (by positivity))
    rw [Nat.floor_natCast] at E Ep
    rw [Nat.range_succ_eq_Icc_zero, Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons]
    have heq : Finset.Ioc 0 n = Finset.Icc 1 n := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [heq]
    simp only [primeLogTwist, Nat.not_prime_zero, if_false, zero_add]
    change ‖∑ i ∈ Finset.Icc 1 n, primeLogTwist χ t i‖ ≤ _
    let P := ∑ i ∈ Finset.Icc 1 n, mangoldtLogTwist χ t i
    let Q := ∑ i ∈ Finset.Icc 1 n, primeLogTwist χ t i
    change ‖Q‖ ≤ _
    calc
      _ = ‖P - (P - Q)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le ..
      _ ≤ K * Real.sqrt B * D^3 + 2 * Real.sqrt B * D^3 := add_le_add E Ep
      _ = _ := by ring
  · interval_cases n <;> simp [primeLogTwist, Finset.sum_range_succ] <;> positivity

private theorem primeLogTwist_remove_log {q B : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 0 ≤ σ) {M : ℝ} (hM : 0 ≤ M)
    (H : ∀ n ≤ B, ‖∑ i ∈ Finset.range (n+1), primeLogTwist χ t i‖ ≤ M) :
    ‖∑ p ∈ (Finset.range (B+1)).filter Nat.Prime, χ p / (p : ℂ)^((σ : ℂ) + t * I)‖ ≤
      (Real.log 2)⁻¹ * M := by
  let w (n : ℕ) : ℝ := (max 2 (n : ℝ))^(-σ) * (Real.log (max 2 (n : ℝ)))⁻¹
  have hw (j : ℕ) : 0 < Real.log (max 2 (j : ℝ)) :=
    Real.log_pos (by linarith [le_max_left (2:ℝ) j])
  have hpos (n : ℕ) : 0 ≤ w n := by
    dsimp only [w]
    exact mul_nonneg (Real.rpow_nonneg ((Nat.cast_nonneg n).trans (le_max_right ..)) _)
      (inv_nonneg.mpr (hw n).le)
  have hdec : Antitone w := by
    intro a b hab
    have hmax : max 2 (a : ℝ) ≤ max 2 (b : ℝ) :=
      max_le_max_left _ (by exact_mod_cast hab)
    have ha : 0 < max 2 (a : ℝ) := zero_lt_two.trans_le (le_max_left ..)
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos ha hmax (neg_nonpos.mpr hσ))
      (inv_anti₀ (hw a) (Real.log_le_log ha hmax)) (inv_nonneg.mpr (hw b).le)
      (Real.rpow_nonneg ha.le _)
  have hterm (n : ℕ) : w n • primeLogTwist χ t n =
      if n.Prime then χ n / (n : ℂ)^((σ : ℂ) + t * I) else 0 := by
    by_cases hp : n.Prime
    · have hn : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
      have hlog : ((Real.log n : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.log_pos (by linarith : (1 : ℝ) < n)).ne'
      have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      simp only [Complex.real_smul, w, max_eq_right hn, primeLogTwist, hp, if_true,
        Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n),
        Complex.ofReal_natCast, Complex.ofReal_neg, neg_mul, Complex.cpow_add _ _ hn₀,
        Complex.cpow_neg, div_eq_mul_inv, mul_inv_rev]
      rw [mul_assoc (((n : ℂ)^(σ : ℂ))⁻¹), ← mul_assoc (((Real.log n : ℝ) : ℂ)⁻¹),
        inv_mul_cancel₀ hlog, one_mul]
      ring
    · simp [primeLogTwist, hp]
  rw [Finset.sum_filter, ← (funext hterm), Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel]
  have hnorm (n : ℕ) (hn : n ∈ Finset.range B) :
      ‖(w (n+1) - w n) • (∑ i ∈ Finset.range (n+1), primeLogTwist χ t i)‖ ≤
        (w n - w (n+1)) * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hdec (Nat.le_succ n))), neg_sub]
    exact mul_le_mul_of_nonneg_left (H n (Finset.mem_range.mp hn).le)
      (sub_nonneg.mpr (hdec (Nat.le_succ n)))
  calc
    _ ≤ _ := norm_sub_le ..
    _ ≤ w B * M + (∑ n ∈ Finset.range B, (w n - w (n+1)) * M) := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hpos B)]
        exact mul_le_mul_of_nonneg_left (H B le_rfl) (hpos B)
      · exact (norm_sum_le ..).trans (Finset.sum_le_sum hnorm)
    _ = w 0 * M := by rw [← Finset.sum_mul, Finset.sum_range_sub']; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hM
      have hpow := Real.rpow_le_one_of_one_le_of_nonpos (show (1 : ℝ) ≤ 2 by norm_num)
        (neg_nonpos.mpr hσ)
      have hl : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_nonneg (by norm_num))
      simpa [w] using mul_le_of_le_one_left hl hpow

/-- Under Dirichlet GRH, the square-root estimate for a sharp prime bin has only
cubic logarithmic dependence on the archimedean height and the modulus. -/
theorem primeBin_mellin_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (A B : ℕ) (σ t : ℝ), 2 ≤ B → A ≤ B → 0 ≤ σ →
        ‖∑ p ∈ primeBin A B, χ p / (p : ℂ)^((σ : ℂ) + t * I)‖ ≤
          K * Real.sqrt B * (1 + Real.log (q * ((B : ℝ) + |t| + 2)))^3 := by
  obtain ⟨K, hK, H⟩ := primeLogTwist_prefix line
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * (Real.log 2)⁻¹ * K, by positivity, ?_⟩
  intro q _ χ hχ A B σ t hB hAB hσ
  let D := 1 + Real.log (q * ((B : ℝ) + |t| + 2))
  let M := K * Real.sqrt B * D^3
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hD : 0 ≤ D := by
    dsimp [D]
    have h := Real.log_nonneg (show 1 ≤ (q : ℝ) * ((B : ℝ) + |t| + 2) by
      nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t),
        mul_nonneg (sub_nonneg.mpr hq) (show (0 : ℝ) ≤ B by positivity)])
    linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA := primeLogTwist_remove_log (B := A) χ σ t hσ hM (fun n hn => H q χ hχ B n t hB (hn.trans hAB))
  have hB' := primeLogTwist_remove_log (B := B) χ σ t hσ hM (fun n hn => H q χ hχ B n t hB hn)
  have hsub : (Finset.range (A+1)).filter Nat.Prime ⊆ (Finset.range (B+1)).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.range_mono (Nat.succ_le_succ hAB))
  have hdiff : primeBin A B = (Finset.range (B+1)).filter Nat.Prime \
      (Finset.range (A+1)).filter Nat.Prime := by
    ext p
    by_cases hp : p.Prime <;> simp [primeBin, hp] <;> omega
  rw [hdiff, Finset.sum_sdiff_eq_sub hsub]
  calc
    _ ≤ _ := norm_sub_le ..
    _ ≤ (Real.log 2)⁻¹ * M + (Real.log 2)⁻¹ * M := add_le_add hB' hA
    _ = _ := by dsimp [M, D]; ring

/-- Sharp prime-bin estimate with the purely oscillatory logarithmic weight. -/
theorem primeBin_logTwist_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (A B : ℕ) (t : ℝ), 2 ≤ B → A ≤ B →
        ‖∑ p ∈ primeBin A B, χ p * (p : ℂ)^(-(t : ℂ) * I)‖ ≤
          K * Real.sqrt B * (1 + Real.log (q * ((B : ℝ) + |t| + 2)))^3 := by
  obtain ⟨K, hK, H⟩ := primeBin_mellin_from_critical_line line
  refine ⟨K, hK, fun q _ χ hχ A B t hB hAB => ?_⟩
  simpa only [Complex.ofReal_zero, zero_add, neg_mul, Complex.cpow_neg, div_eq_mul_inv]
    using H q χ hχ A B 0 t hB hAB le_rfl

open Lean Elab Command in
run_cmd
  for ax in ← collectAxioms ``primeBin_logTwist_from_critical_line do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "The prime-bin twist theorem depends on unexpected axiom {ax}"

#print axioms primeBin_mellin_from_critical_line
#print axioms primeBin_logTwist_from_critical_line

end Cogentic.Randomized
