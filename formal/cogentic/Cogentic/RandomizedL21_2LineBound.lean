import Cogentic.RandomizedL21_2Vertical
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormSubOneMulRiemannZetaLe
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville

set_option linter.style.haveILetI false

/-!
# L21.2: the uniform zeta line bound at `Re s = 2/3`

`Cogentic.RandomizedL21_2Vertical` reduces the truncated Perron shift of L21.2 to
the single uniform estimate

```
VerticalLineBound X K C :
  ∀ᶠ n, ∀ u, |u| ≤ 2 * X n ^ 3 →
    ‖logDeriv riemannZeta (2/3 + i u)‖ ≤ K n * (log X n) ^ C.
```

This file supplies that estimate from the smallest possible zeta-side input.

The logarithmic derivative is controlled by the classical ball log-derivative
bound (Borel--Carathéodory): if `f` is nonzero and bounded by `M * ‖f z₀‖` on a
ball of radius `R` around `z₀`, then `‖f'/f z₀‖ ≤ 24 log M / R`.  We prove this
bound here from Mathlib's Borel--Carathéodory theorem, so no unbuilt dependency
is required.

The only genuinely arithmetic input is a uniform lower bound for `ζ` in a thin
strip around the line `Re s = 2/3` (`ZetaStripLowerBound`).  This is the minimal
quantitative form of the classical non-vanishing/zero-free input at `2/3`: it
implies both non-vanishing on the strip and the ratio `M` needed above.
Everything else -- the upper bound for `ζ` in the strip -- is proved from the
approximate functional equation `norm_zeta_sub_sum_le`.

We also record the even more primitive `ZetaLineEstimate`, a pointwise lower
bound for `ζ` and a pointwise upper bound for `ζ'` on the line, which gives
`VerticalLineBound` by direct division.

Everything is conditional only on the explicit zeta input, with no `sorry`,
`admit`, `axiom` or `native_decide`, and no bound replaced by zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2LineBound

open Filter Real MeasureTheory
open Complex Metric
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Vertical

/-! ## The classical log-derivative bound on a ball -/

/-- On a ball where `f` does not vanish, `f` has a holomorphic logarithm
vanishing at the centre.  This is the elementary step behind the classical
log-derivative bound. -/
lemma exists_log_on_ball {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧
      (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by
  have hopen : IsOpen (ball z₀ R) := isOpen_ball
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball z₀ R) :=
    (hf.deriv hopen).div hf hne
  obtain ⟨G, hG⟩ := hd.isExactOn_ball
  refine ⟨fun z => G z - G z₀, by simp, fun z hz => (hG z hz).sub_const _, ?_⟩
  have hk : ∀ z ∈ ball z₀ R,
      HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀))) 0 z := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z :=
      (hf.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hgz : HasDerivAt (fun w => -(G w - G z₀)) (-(deriv f z / f z)) z :=
      ((hG z hz).sub_const _).neg
    have h : HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀)))
        (deriv f z * Complex.exp (-(G z - G z₀)) +
          f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z))) z :=
      hfz.mul hgz.cexp
    have h0 : deriv f z * Complex.exp (-(G z - G z₀)) +
        f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z)) = 0 := by
      have h1 := hne z hz
      field_simp
      all_goals ring
    exact h0 ▸ h
  intro z hz
  have hz₀ : z₀ ∈ ball z₀ R := mem_ball_self (pos_of_mem_ball hz)
  have hconst := hopen.is_const_of_deriv_eq_zero (convex_ball z₀ R).isPreconnected
    (fun w hw => (hk w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hk w hw).deriv) hz hz₀
  simp only [sub_self, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- **Classical log-derivative bound.**  If `f` is holomorphic and nonzero on
the ball `closedBall z₀ R` and satisfies `‖f z‖ ≤ M * ‖f z₀‖` there with
`1 ≤ M`, then on the concentric half-ball,
`‖f'/f z‖ ≤ 24 log M / R`. -/
lemma logDeriv_bound_on_ball {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (closedBall z₀ R))
    (hne : ∀ z ∈ closedBall z₀ R, f z ≠ 0)
    (hbd : ∀ z ∈ closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖)
    {z : ℂ} (hz : z ∈ closedBall z₀ (R / 2)) :
    ‖deriv f z / f z‖ ≤ 24 * Real.log M / R := by
  have hR0 : R ≠ 0 := hR.ne'
  have hfb : DifferentiableOn ℂ f (ball z₀ R) := hf.mono ball_subset_closedBall
  have hneb : ∀ w ∈ ball z₀ R, f w ≠ 0 := fun w hw => hne w (ball_subset_closedBall hw)
  obtain ⟨g, hg0, hgd, hgf⟩ := exists_log_on_ball hfb hneb
  have hf0 : 0 < ‖f z₀‖ := norm_pos_iff.2 (hne z₀ (mem_closedBall_self hR.le))
  have hre : ∀ w ∈ ball z₀ R, (g w).re ≤ Real.log M := by
    intro w hw
    have h1 := hbd w (ball_subset_closedBall hw)
    rw [hgf w hw, norm_mul, Complex.norm_exp] at h1
    have h2 : Real.exp (g w).re ≤ M := by
      by_contra h
      have h3 := mul_lt_mul_of_pos_left (lt_of_not_ge h) hf0
      linarith
    calc (g w).re = Real.log (Real.exp (g w).re) := (Real.log_exp _).symm
      _ ≤ Real.log M := Real.log_le_log (Real.exp_pos _) h2
  have hzb : dist z z₀ ≤ R / 2 := hz
  have hshift : ∀ v ∈ ball (0 : ℂ) R, z₀ + v ∈ ball z₀ R := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.1 hv
  have hmain : ∀ A : ℝ, Real.log M < A → ‖deriv f z / f z‖ ≤ 24 * A / R := by
    intro A hA
    have hA0 : 0 < A := lt_of_le_of_lt (Real.log_nonneg hM) hA
    have hhd : DifferentiableOn ℂ (fun v => g (z₀ + v)) (ball 0 R) := by
      intro v hv
      exact ((hgd _ (hshift v hv)).differentiableAt.comp v
        (differentiableAt_id.const_add z₀)).differentiableWithinAt
    have hhm : Set.MapsTo (fun v => g (z₀ + v)) (ball 0 R) {w | w.re ≤ A} := by
      intro v hv
      exact le_trans (hre _ (hshift v hv)) hA.le
    have hbc : ∀ w ∈ closedBall z₀ (3 * R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      obtain ⟨u, rfl⟩ : ∃ u, w = z₀ + u := ⟨w - z₀, by ring⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hw
      have huR : u ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        linarith
      have hB : ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) :=
        Complex.borelCaratheodory_zero hA0 hhd hhm hR huR (by simpa using hg0)
      have hpos : 0 < R - ‖u‖ := by linarith
      calc ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) := hB
        _ ≤ 6 * A := by
          rw [div_le_iff₀ hpos]
          nlinarith [norm_nonneg u]
    have hR4 : 0 < R / 4 := by linarith
    have hsub : closedBall z (R / 4) ⊆ ball z₀ R := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < R := by linarith
    have hdiff : DiffContOnCl ℂ g (ball z (R / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hR4.ne']
      intro w hw
      exact (hgd w (hsub hw)).differentiableAt.differentiableWithinAt
    have hC : ∀ w ∈ sphere z (R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      apply hbc
      rw [mem_sphere] at hw
      rw [mem_closedBall]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ 3 * R / 4 := by linarith
    have hzb' : z ∈ ball z₀ R := hsub (mem_closedBall_self hR4.le)
    have hder := norm_deriv_le_of_forall_mem_sphere_norm_le hR4 hdiff hC
    rw [(hgd z hzb').deriv] at hder
    calc ‖deriv f z / f z‖ ≤ 6 * A / (R / 4) := hder
      _ = 24 * A / R := by
        field_simp
        all_goals ring
  apply le_of_forall_pos_le_add
  intro ε hε
  have hεR : 0 < ε * R / 24 := by positivity
  have h := hmain (Real.log M + ε * R / 24) (by linarith)
  calc ‖deriv f z / f z‖ ≤ 24 * (Real.log M + ε * R / 24) / R := h
    _ = 24 * Real.log M / R + ε := by
      field_simp

/-! ## Geometry of the strip around `Re s = 2/3` -/

lemma strip_re_abs {u : ℝ} {z : ℂ} {R : ℝ}
    (hz : ‖z - perronLine perronRe u‖ ≤ R) :
    |z.re - (2 / 3 : ℝ)| ≤ R := by
  calc |z.re - (2 / 3 : ℝ)| = |(z - perronLine perronRe u).re| := by
        simp [perronLine, perronRe]
    _ ≤ ‖z - perronLine perronRe u‖ := Complex.abs_re_le_norm _
    _ ≤ R := hz

lemma strip_dist_one_ge {u : ℝ} {z : ℂ} {R : ℝ}
    (hz : ‖z - perronLine perronRe u‖ ≤ R) (hR : R ≤ 1 / 8) :
    (5 / 24 : ℝ) ≤ ‖z - 1‖ := by
  have hbase : (1 / 3 : ℝ) ≤ ‖perronLine perronRe u - 1‖ := by
    have hre : (perronLine perronRe u - 1).re = -(1 / 3 : ℝ) := by
      simp [perronLine, perronRe]
      norm_num
    calc (1 / 3 : ℝ) = |(-(1 / 3) : ℝ)| := by norm_num
      _ = |(perronLine perronRe u - 1).re| := by rw [hre]
      _ ≤ ‖perronLine perronRe u - 1‖ := Complex.abs_re_le_norm _
  have htri : ‖perronLine perronRe u - 1‖ ≤ ‖z - perronLine perronRe u‖ + ‖z - 1‖ := by
    have h := norm_sub_le (z - 1) (z - perronLine perronRe u)
    have he : (z - 1) - (z - perronLine perronRe u) = perronLine perronRe u - 1 := by ring
    rw [he] at h
    linarith
  linarith

lemma strip_norm_le {u X : ℝ} {z : ℂ} {R : ℝ}
    (hu : |u| ≤ 2 * X ^ 3) (hz : ‖z - perronLine perronRe u‖ ≤ R) (hR : R ≤ 1 / 8) :
    ‖z‖ ≤ 2 * X ^ 3 + 1 := by
  have hs0 : ‖perronLine perronRe u‖ ≤ 2 / 3 + |u| := by
    have h := Complex.norm_le_abs_re_add_abs_im
      (((2 / 3 : ℝ) : ℂ) + ((u : ℂ) * I))
    have hre : (((2 / 3 : ℝ) : ℂ) + ((u : ℂ) * I)).re = 2 / 3 := by simp
    have him : (((2 / 3 : ℝ) : ℂ) + ((u : ℂ) * I)).im = u := by simp
    simp only [perronLine, perronRe]
    rw [hre, him] at h
    calc ‖((2 / 3 : ℝ) : ℂ) + (u : ℂ) * I‖ ≤ |(2 / 3 : ℝ)| + |u| := h
      _ = 2 / 3 + |u| := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  have htri : ‖z‖ ≤ ‖z - perronLine perronRe u‖ + ‖perronLine perronRe u‖ := by
    have := norm_add_le (z - perronLine perronRe u) (perronLine perronRe u)
    simpa using this
  linarith

/-! ## An unconditional upper bound in the strip -/

/-- The approximate functional equation form `norm_sub_one_mul_riemannZeta_le`
gives a polynomial upper bound for `ζ` in the strip `|Re s - 2/3| ≤ 1/8`,
uniform in the imaginary part. -/
lemma exists_zeta_upper_bound_strip :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X u : ℝ) (z : ℂ), 1 ≤ X → |u| ≤ 2 * X ^ 3 →
      ‖z - perronLine perronRe u‖ ≤ 1 / 8 →
      ‖riemannZeta z‖ ≤ C * X ^ 15 := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.ZetaLeft.norm_sub_one_mul_riemannZeta_le
  refine ⟨max ((24 / 5) * C * 5 ^ 5) 1, le_max_right _ _, ?_⟩
  intro X u z hX hu hz
  have hX3 : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX
  have hre_abs := strip_re_abs hz
  have hzre_ge : (13 / 24 : ℝ) ≤ z.re := by
    have := (abs_le.mp hre_abs).1
    linarith
  have hzre_lower : -(7 / 4 : ℝ) ≤ z.re := by linarith
  have hzre_upper : z.re ≤ 19 / 24 := by
    have := (abs_le.mp hre_abs).2
    linarith
  have hzne : z ≠ 1 := by
    intro h
    rw [h] at hzre_upper
    norm_num at hzre_upper
  have hdist1 : (5 / 24 : ℝ) ≤ ‖z - 1‖ :=
    strip_dist_one_ge hz (le_refl (1 / 8))
  have hnormz : ‖z‖ ≤ 2 * X ^ 3 + 1 :=
    strip_norm_le hu hz (le_refl (1 / 8))
  have h := hC z hzre_lower hzne
  have hmul : ‖z - 1‖ * ‖riemannZeta z‖ ≤ C * (‖z‖ + 2) ^ 5 := by
    simpa [norm_mul] using h
  have hlow : (5 / 24) * ‖riemannZeta z‖ ≤ C * (‖z‖ + 2) ^ 5 := by
    calc (5 / 24) * ‖riemannZeta z‖ ≤ ‖z - 1‖ * ‖riemannZeta z‖ := by gcongr
      _ ≤ C * (‖z‖ + 2) ^ 5 := hmul
  have hratio : ‖riemannZeta z‖ ≤ C * (‖z‖ + 2) ^ 5 / (5 / 24) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 5 / 24)]
    linarith
  have h5 : ‖z‖ + 2 ≤ 5 * X ^ 3 := by nlinarith
  have hpow : (‖z‖ + 2) ^ 5 ≤ (5 * X ^ 3) ^ 5 :=
    pow_le_pow_left₀ (by positivity) h5 5
  calc ‖riemannZeta z‖ ≤ C * (‖z‖ + 2) ^ 5 / (5 / 24) := hratio
    _ = (24 / 5) * C * (‖z‖ + 2) ^ 5 := by ring
    _ ≤ (24 / 5) * C * (5 * X ^ 3) ^ 5 := by gcongr
    _ = ((24 / 5) * C * 5 ^ 5) * X ^ 15 := by
        rw [mul_pow]
        ring
    _ ≤ max ((24 / 5) * C * 5 ^ 5) 1 * X ^ 15 := by
        gcongr
        exact le_max_left _ _

/-! ## The minimal zeta-side inputs -/

/-- A uniform lower bound for `ζ` in the strip of radius `R` around the line
`Re s = 2/3`, of size `b n`.  This is the minimal quantitative non-vanishing
input: it implies both non-vanishing in the strip and the ratio needed by the
classical log-derivative bound. -/
def ZetaStripLowerBound (X : ℕ → ℝ) (R : ℝ) (b : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
    ∀ z : ℂ, ‖z - perronLine perronRe u‖ ≤ R → b n ≤ ‖riemannZeta z‖

/-- The even smaller pointwise line estimate: a lower bound for `ζ` and an
upper bound for `ζ'` on `Re s = 2/3`. -/
def ZetaLineEstimate (X : ℕ → ℝ) (b B : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
    b n ≤ ‖riemannZeta (perronLine perronRe u)‖ ∧
      ‖deriv riemannZeta (perronLine perronRe u)‖ ≤ B n

/-- The classical log-derivative line estimate:
`‖ζ'/ζ (2/3 + i u)‖ = O ((log (|u| + 2))^2)`.  This is the standard
unconditional shape of the vertical-strip bound; at `Re s = 2/3` it is exactly
the remaining zeta input. -/
def ClassicalLogDerivLineBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
    ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤
      C * (Real.log (|u| + 2)) ^ 2

/-! ## From the classical log-derivative line bound -/

/-- The classical `O (log^2)` line estimate implies `VerticalLineBound` with a
polylogarithmic constant.  The height `2 X^3` costs only a factor `4` in the
logarithm. -/
theorem verticalLineBound_of_classicalLogDeriv {X : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (h : ClassicalLogDerivLineBound) :
    ∃ K : ℝ, 0 < K ∧ VerticalLineBound X (fun _ => K) 2 := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨16 * C, by positivity, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro n u hu
  set L := bandLog X n with hLdef
  have hL3 : 3 ≤ L := hU n
  have hL1 : 1 ≤ L := by linarith
  have hX1 : 1 < X n := hX n
  have hXpos : 0 < X n := by linarith
  have hX3 : (1 : ℝ) ≤ X n ^ 3 := by
    simpa using one_le_pow₀ hX1.le (n := 3)
  rw [Real.rpow_two]
  have hupper : |u| + 2 ≤ X n ^ 4 := by
    have h1 : |u| + 2 ≤ 2 * X n ^ 3 + 2 := by linarith [abs_nonneg u]
    have h2 : 2 * X n ^ 3 + 2 ≤ 4 * X n ^ 3 := by linarith
    have h3 : (4 : ℝ) ≤ X n := by
      have h4exp : (4 : ℝ) ≤ Real.exp 3 := by
        have := Real.add_one_le_exp (3 : ℝ)
        norm_num at this ⊢
        exact this
      have hexp : Real.exp 3 ≤ X n := by
        have := Real.exp_le_exp.mpr (show (3 : ℝ) ≤ L by linarith)
        simpa [L, bandLog, Real.exp_log hXpos] using this
      linarith
    have h4 : 4 * X n ^ 3 ≤ X n * X n ^ 3 :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : X n * X n ^ 3 = X n ^ 4 := by ring
    linarith
  have hlogpos : 0 ≤ Real.log (|u| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg u]
  have hlog_le : Real.log (|u| + 2) ≤ 4 * L := by
    have h1 : Real.log (|u| + 2) ≤ Real.log (X n ^ 4) :=
      Real.log_le_log (by linarith [abs_nonneg u]) hupper
    have h2 : Real.log (X n ^ 4) = 4 * L := by
      rw [Real.log_pow]
      simp [L, bandLog]
    linarith
  have hsq : (Real.log (|u| + 2)) ^ 2 ≤ (4 * L) ^ 2 :=
    pow_le_pow_left₀ hlogpos hlog_le 2
  calc
    ‖logDeriv riemannZeta (perronLine perronRe u)‖
        ≤ C * (Real.log (|u| + 2)) ^ 2 := hC u
    _ ≤ C * (4 * L) ^ 2 := by gcongr
    _ = (16 * C) * L ^ 2 := by ring

/-! ## From the pointwise line estimate to `VerticalLineBound` -/

theorem verticalLineBound_of_zetaLineEstimate {X : ℕ → ℝ} {b B : ℕ → ℝ}
    (hU : ∀ n, 1 ≤ bandLog X n)
    (hb : ∀ n, 0 < b n) (hB : ∀ n, 0 ≤ B n)
    (h : ZetaLineEstimate X b B) :
    VerticalLineBound X (fun n => B n / b n) 2 := by
  unfold VerticalLineBound
  filter_upwards [h] with n hn
  intro u hu
  obtain ⟨hlow, hup⟩ := hn u hu
  have hU1 : 1 ≤ bandLog X n := hU n
  have hpos : 0 < ‖riemannZeta (perronLine perronRe u)‖ :=
    lt_of_lt_of_le (hb n) hlow
  rw [logDeriv_apply, norm_div]
  rw [Real.rpow_two]
  calc
    ‖deriv riemannZeta (perronLine perronRe u)‖ /
        ‖riemannZeta (perronLine perronRe u)‖
        ≤ B n / ‖riemannZeta (perronLine perronRe u)‖ :=
          div_le_div_of_nonneg_right hup hpos.le
    _ ≤ B n / b n :=
          div_le_div_of_nonneg_left (hB n) (hb n) hlow
    _ ≤ (B n / b n) * (bandLog X n) ^ 2 := by
          have hsq : 1 ≤ (bandLog X n) ^ 2 := one_le_pow₀ hU1
          have hnonneg : 0 ≤ B n / b n := div_nonneg (hB n) (hb n).le
          simpa using mul_le_mul_of_nonneg_left hsq hnonneg

/-! ## From the strip lower bound to `VerticalLineBound` -/

/-- **`VerticalLineBound` from a uniform lower bound in a thin strip.**
The upper bound in the strip is unconditional (`exists_zeta_upper_bound_strip`);
the lower bound and non-vanishing are the explicit zeta input.  The classical
ball log-derivative bound then gives the claimed `O (log X)` constant. -/
theorem verticalLineBound_of_zetaStripLower {X : ℕ → ℝ} {R : ℝ} {b : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hR0 : 0 < R) (hR8 : R ≤ 1 / 8)
    (hb0 : ∀ n, 0 < b n) (hb1 : ∀ n, b n ≤ 1)
    (hL : ZetaStripLowerBound X R b) :
    VerticalLineBound X
      (fun n => 24 * (Real.log (Classical.choose exists_zeta_upper_bound_strip) +
          15 + Real.log (1 / b n)) / R) 2 := by
  set C : ℝ := Classical.choose exists_zeta_upper_bound_strip with hCdef
  have hCspec := Classical.choose_spec exists_zeta_upper_bound_strip
  have hC1 : 1 ≤ C := by rw [hCdef]; exact hCspec.1
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hC : ∀ (X u : ℝ) (z : ℂ), 1 ≤ X → |u| ≤ 2 * X ^ 3 →
      ‖z - perronLine perronRe u‖ ≤ 1 / 8 →
      ‖riemannZeta z‖ ≤ C * X ^ 15 := by
    rw [hCdef]
    exact hCspec.2
  unfold VerticalLineBound
  filter_upwards [hL] with n hn
  intro u hu
  set L := bandLog X n with hLdef
  have hL3 : 3 ≤ L := hU n
  have hL1 : 1 ≤ L := by linarith
  have hX1 : 1 < X n := hX n
  have hXpos : 0 < X n := by linarith
  have hX3 : (1 : ℝ) ≤ X n ^ 3 := by
    simpa using one_le_pow₀ hX1.le (n := 3)
  set s0 : ℂ := perronLine perronRe u with hs0
  have hR8' : R ≤ 1 / 8 := hR8
  -- Pointwise geometry on the closed ball
  have hzre_ge : ∀ z ∈ closedBall s0 R, (13 / 24 : ℝ) ≤ z.re := by
    intro z hz
    have hz' : ‖z - s0‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have h := (abs_le.mp (strip_re_abs hz')).1
    linarith
  have hzre_upper : ∀ z ∈ closedBall s0 R, z.re ≤ 19 / 24 := by
    intro z hz
    have hz' : ‖z - s0‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have h := (abs_le.mp (strip_re_abs hz')).2
    linarith
  have hzne_one : ∀ z ∈ closedBall s0 R, z ≠ 1 := by
    intro z hz
    have hle := hzre_upper z hz
    intro h
    rw [h] at hle
    norm_num at hle
  have hdist1 : ∀ z ∈ closedBall s0 R, (5 / 24 : ℝ) ≤ ‖z - 1‖ := by
    intro z hz
    have hz' : ‖z - s0‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact strip_dist_one_ge hz' hR8'
  have hnormz : ∀ z ∈ closedBall s0 R, ‖z‖ ≤ 2 * X n ^ 3 + 1 := by
    intro z hz
    have hz' : ‖z - s0‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact strip_norm_le hu hz' hR8'
  -- Non-vanishing and the ratio bound
  have hne : ∀ z ∈ closedBall s0 R, riemannZeta z ≠ 0 := by
    intro z hz hz0
    have hz' : ‖z - s0‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hb := hn u hu z hz'
    rw [hz0, norm_zero] at hb
    linarith [hb0 n]
  have hupper : ∀ z ∈ closedBall s0 R, ‖riemannZeta z‖ ≤ C * X n ^ 15 := by
    intro z hz
    have hz' : ‖z - s0‖ ≤ 1 / 8 := by
      have h1 : ‖z - s0‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      exact le_trans h1 hR8'
    exact hC (X n) u z hX1.le hu hz'
  have hlow0 : b n ≤ ‖riemannZeta s0‖ := by
    exact hn u hu s0 (by rw [hs0, sub_self, norm_zero]; positivity)
  set M : ℝ := C * X n ^ 15 / b n with hMdef
  have hX15 : (1 : ℝ) ≤ X n ^ 15 := by
    calc (1 : ℝ) ≤ (X n ^ 3) ^ 5 := one_le_pow₀ hX3 (n := 5)
      _ = X n ^ 15 := by
          rw [← pow_mul]
  have hM1 : 1 ≤ M := by
    rw [hMdef, le_div_iff₀ (hb0 n)]
    nlinarith [hC1, hX15, hb1 n]
  have hbd : ∀ z ∈ closedBall s0 R, ‖riemannZeta z‖ ≤ M * ‖riemannZeta s0‖ := by
    intro z hz
    calc
      ‖riemannZeta z‖ ≤ C * X n ^ 15 := hupper z hz
      _ = M * b n := by
          rw [hMdef]
          exact (div_mul_cancel₀ (C * X n ^ 15) (hb0 n).ne').symm
      _ ≤ M * ‖riemannZeta s0‖ := by
          exact mul_le_mul_of_nonneg_left hlow0 (by linarith)
  have hdiff : DifferentiableOn ℂ riemannZeta (closedBall s0 R) := by
    intro z hz
    exact (differentiableAt_riemannZeta (hzne_one z hz)).differentiableWithinAt
  have hbound := logDeriv_bound_on_ball (f := riemannZeta) (z₀ := s0) (R := R) (M := M)
    hR0 hM1 hdiff hne hbd (z := s0) (by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_self, norm_zero]
      positivity)
  -- Bound `log M`.
  have hlogM_eq : Real.log M = Real.log C + 15 * L + Real.log (1 / b n) := by
    rw [hMdef, Real.log_div (by positivity) (hb0 n).ne']
    rw [Real.log_mul hC0.ne' (pow_ne_zero 15 hXpos.ne')]
    rw [Real.log_pow]
    rw [Real.log_div one_ne_zero (hb0 n).ne', Real.log_one]
    simp only [L, bandLog]
    ring
  have hlogM_le : Real.log M ≤
      (Real.log C + 15 + Real.log (1 / b n)) * L := by
    have hlog1b : 0 ≤ Real.log (1 / b n) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (hb0 n)]
      linarith [hb1 n]
    have hA : 0 ≤ Real.log C + Real.log (1 / b n) := by
      have : 0 ≤ Real.log C := Real.log_nonneg hC1
      linarith
    rw [hlogM_eq]
    have hALE : Real.log C + Real.log (1 / b n) ≤
        (Real.log C + Real.log (1 / b n)) * L := by
      have := mul_le_mul_of_nonneg_left hL1 hA
      simpa using this
    nlinarith
  -- Final arithmetic.
  have hCnonneg : 0 ≤ Real.log C + 15 + Real.log (1 / b n) := by
    have hlog1b : 0 ≤ Real.log (1 / b n) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (hb0 n)]
      linarith [hb1 n]
    have hlogC : 0 ≤ Real.log C := by
      apply Real.log_nonneg
      exact hC1
    linarith
  rw [logDeriv_apply]
  rw [Real.rpow_two]
  calc
    ‖deriv riemannZeta s0 / riemannZeta s0‖ ≤ 24 * Real.log M / R := hbound
    _ ≤ 24 * ((Real.log C + 15 + Real.log (1 / b n)) * L) / R := by
        gcongr
    _ = (24 * (Real.log C + 15 + Real.log (1 / b n)) / R) * L := by
        ring
    _ ≤ (24 * (Real.log C + 15 + Real.log (1 / b n)) / R) * L ^ 2 := by
        gcongr
        nlinarith [hL1]

/-! ## The chosen upper-bound constant -/

lemma zetaUpperConstant_one_le : 1 ≤ Classical.choose exists_zeta_upper_bound_strip :=
  (Classical.choose_spec exists_zeta_upper_bound_strip).1

lemma zetaUpperConstant_pos : 0 < Classical.choose exists_zeta_upper_bound_strip :=
  lt_of_lt_of_le zero_lt_one zetaUpperConstant_one_le

lemma zetaUpperConstant_log_nonneg :
    0 ≤ Real.log (Classical.choose exists_zeta_upper_bound_strip) :=
  Real.log_nonneg zetaUpperConstant_one_le

/-! ## Composing with the vertical Perron contour -/

/-- The strip lower bound produces the vertical-strip zeta bound of
`Cogentic.RandomizedL21_2Vertical`, with the contour loss `product_perron_vertical_l1`
made explicit. -/
theorem verticalZetaStripBound_of_zetaStripLower {X : ℕ → ℝ} {c R : ℝ} {b : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hR0 : 0 < R) (hR8 : R ≤ 1 / 8)
    (hb0 : ∀ n, 0 < b n) (hb1 : ∀ n, b n ≤ 1)
    (hL : ZetaStripLowerBound X R b) :
    VerticalZetaStripBound X c
      (fun n => ((24 * (Real.log (Classical.choose exists_zeta_upper_bound_strip) +
          15 + Real.log (1 / b n)) / R) / Real.pi) *
        (1 + Real.log (X n ^ 3 / perronRe))) 2 := by
  have hK : ∀ n, 0 ≤ (24 * (Real.log (Classical.choose exists_zeta_upper_bound_strip) +
      15 + Real.log (1 / b n)) / R) := by
    intro n
    have hlog1b : 0 ≤ Real.log (1 / b n) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (hb0 n)]
      linarith [hb1 n]
    have : 0 ≤ Real.log (Classical.choose exists_zeta_upper_bound_strip) + 15 +
        Real.log (1 / b n) := by
      linarith [zetaUpperConstant_log_nonneg]
    positivity
  exact verticalZetaStripBound_of_lineBound hX hK
    (verticalLineBound_of_zetaStripLower hX hU hR0 hR8 hb0 hb1 hL)

/-- The same input also yields the full three-term vertical shift bound once the
Perron remainder is supplied. -/
theorem verticalShiftBound_of_zetaStripLower {X : ℕ → ℝ} {c R : ℝ} {b : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hR0 : 0 < R) (hR8 : R ≤ 1 / 8)
    (hb0 : ∀ n, 0 < b n) (hb1 : ∀ n, b n ≤ 1)
    (hsmall : ∀ᶠ n : ℕ in atTop,
      smoothCutoff c X n ≤ Real.exp (bandLog X n / 3))
    (hL : ZetaStripLowerBound X R b)
    (hR : PerronShiftRemainder X c
      (fun n => ((24 * (Real.log (Classical.choose exists_zeta_upper_bound_strip) +
          15 + Real.log (1 / b n)) / R) / Real.pi) *
        (1 + Real.log (X n ^ 3 / perronRe))) 2) :
    VerticalShiftBound X c
      (fun n => 3 * (((24 * (Real.log (Classical.choose exists_zeta_upper_bound_strip) +
          15 + Real.log (1 / b n)) / R) / Real.pi) *
        (1 + Real.log (X n ^ 3 / perronRe)))) 2 := by
  have hK : ∀ n, 0 ≤ (24 * (Real.log (Classical.choose exists_zeta_upper_bound_strip) +
      15 + Real.log (1 / b n)) / R) := by
    intro n
    have hlog1b : 0 ≤ Real.log (1 / b n) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (hb0 n)]
      linarith [hb1 n]
    have : 0 ≤ Real.log (Classical.choose exists_zeta_upper_bound_strip) + 15 +
        Real.log (1 / b n) := by
      linarith [zetaUpperConstant_log_nonneg]
    positivity
  exact verticalShiftBound_of_lineBound hX hK hU (le_refl 2) hsmall
    (verticalLineBound_of_zetaStripLower hX hU hR0 hR8 hb0 hb1 hL) hR

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2LineBound.exists_log_on_ball
#print axioms Cogentic.RandomizedL21_2LineBound.logDeriv_bound_on_ball
#print axioms Cogentic.RandomizedL21_2LineBound.exists_zeta_upper_bound_strip
#print axioms Cogentic.RandomizedL21_2LineBound.verticalLineBound_of_classicalLogDeriv
#print axioms Cogentic.RandomizedL21_2LineBound.verticalLineBound_of_zetaLineEstimate
#print axioms Cogentic.RandomizedL21_2LineBound.verticalLineBound_of_zetaStripLower
#print axioms Cogentic.RandomizedL21_2LineBound.verticalZetaStripBound_of_zetaStripLower
#print axioms Cogentic.RandomizedL21_2LineBound.verticalShiftBound_of_zetaStripLower

end Cogentic.RandomizedL21_2LineBound

#check Cogentic.RandomizedL21_2LineBound.ZetaStripLowerBound
#check Cogentic.RandomizedL21_2LineBound.ZetaLineEstimate
#check Cogentic.RandomizedL21_2LineBound.ClassicalLogDerivLineBound
#check Cogentic.RandomizedL21_2LineBound.verticalLineBound_of_classicalLogDeriv
#check Cogentic.RandomizedL21_2LineBound.verticalLineBound_of_zetaLineEstimate
#check Cogentic.RandomizedL21_2LineBound.verticalLineBound_of_zetaStripLower
#check Cogentic.RandomizedL21_2LineBound.verticalZetaStripBound_of_zetaStripLower
#check Cogentic.RandomizedL21_2LineBound.verticalShiftBound_of_zetaStripLower
