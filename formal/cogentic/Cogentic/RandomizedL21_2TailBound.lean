import Cogentic.RandomizedL21_2StripBound

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-!
# L21.2: the elementary vertical-tail bound

`Cogentic.RandomizedL21_2Remainder.VerticalTailBound` is the cost of moving the
vertical Perron contour from height `T = X^3` to `T = X^3 + 1`:

```
‖verticalZetaSum v t (X^3 + 1) - verticalZetaSum v t (X^3)‖
  ≤ shiftHorizontal (Ktail n) (bandLog X n) C (X n) v.
```

Writing `T = X^3`, the two contour integrals differ only on the two unit-length
end pieces `[T, T+1]` and `[-T-1, -T]`.  On each of them `|τ| ≥ T`, so the
denominator `perronLine (2/3) τ` costs `1/T`, while the log-derivative factor is
uniformly bounded on the segment `Re s = 2/3`, `|Im s| ≤ 3 T`.  Hence the
difference is at most

```
(2 / (2π)) * M * v^(2/3) / T = (M / π) * v^(2/3) / T,
```

and since `v^(2/3) ≤ v` for `v ≥ 1` this is `O (v / (π T))`, exactly one copy of
`shiftHorizontal` with `Ktail = M / π`.

The strip input is the same unconditional bound on `ζ'/ζ` that the rest of
L21.2 uses: on `Re s = 2/3` it is proved from the Riemann hypothesis and the
zero-counting estimate `GlobalTheory.ZetaWide.main`.  At heights `|Im s| < 1`
the existing pole-free bound `StripZetaBoundOffPole` does not apply, but the
same zero-counting argument does: the pole term `1/(s-1)` is bounded by `3`
because `Re s = 2/3`, so the constant only grows from `1` to `3`.  This is
`norm_logDeriv_le_of_perronRe` below.

The main results are:

* `verticalZetaSum_tail_identity`: the exact integral difference identity;
* `norm_verticalTail_le`: the elementary `L¹` tail estimate;
* `LineBoundAtPerronRe`: the smallest explicit zeta estimate needed;
* `verticalTailBound_of_lineBound`: `LineBoundAtPerronRe` implies
  `VerticalTailBound`;
* `verticalTailBound_of_RH`: the unconditional `VerticalTailBound` under the
  Riemann hypothesis, with the explicit constant `tailK / π` and exponent `1`;
* `verticalTailBound_of_stripOffPole`: the same from the existing
  `StripZetaBoundOffPole` plus the near-axis estimate;
* `perronShiftRemainder_of_RH_stripTail`: the L21.2 `PerronShiftRemainder`
  with the vertical tail discharged.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and the bound is
strictly positive.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2TailBound

open Filter Real MeasureTheory Complex
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2StripBound

/-! ## The strip constant at `Re s = 2/3` -/

/-- The explicit constant of the uniform bound on `ζ'/ζ` along the line
`Re s = 2/3`, valid at all heights (including `|Im s| < 1`).  It is the
zero-counting constant `28 * wideC` plus `3` for the pole term `1/(s-1)`. -/
noncomputable def tailK : ℝ := 28 * wideC + 3

lemma tailK_pos : 0 < tailK := by
  unfold tailK
  have hw := wideC_pos
  positivity

lemma tailK_nonneg : 0 ≤ tailK := tailK_pos.le

/-- `ζ'/ζ` is differentiable at every point away from the pole and the zeros. -/
theorem differentiableAt_logDeriv_riemannZeta {s : ℂ} (hne : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (logDeriv riemannZeta) s := by
  have hAn : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hne)
  have hder : DifferentiableAt ℂ (deriv riemannZeta) s := hAn.deriv.differentiableAt
  have hζ : DifferentiableAt ℂ riemannZeta s := hAn.differentiableAt
  simpa [logDeriv] using hder.div hζ hz

/-- **`ζ'/ζ` at `Re s = 2/3`, at every height.**  Compared with
`norm_logDeriv_le_of_leftStrip`, the hypothesis `1 ≤ |Im s|` is dropped: the
pole term is at most `3` because the real part is `2/3`, and the zero terms are
still at distance at least `1/6` from the line. -/
theorem norm_logDeriv_le_of_perronRe {s : ℂ} (hRH : RiemannZetaZerosOnLine)
    (hre : s.re = perronRe) :
    ‖logDeriv riemannZeta s‖ ≤ 7 * wideC * Real.log (|s.im| + 2) + 3 := by
  have hre1 : perronRe ≤ s.re := le_of_eq hre.symm
  have hre2 : s.re ≤ 2 := by
    rw [hre]; norm_num [perronRe]
  have hre_low : -1 ≤ s.re := by
    rw [hre]; norm_num [perronRe]
  have hsne : s ≠ 1 := by
    intro h
    have hre' : s.re = 1 := by rw [h]; simp
    rw [hre] at hre'
    norm_num [perronRe] at hre'
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_RH_ge hRH hre1 hsne
  obtain ⟨hfin, hcount, herr⟩ := wideC_spec s hre_low hre2 hsne hz
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount herr
  set Z : Finset ℂ := hfin.toFinset with hZ
  have hcount' : (∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℝ)) ≤
      wideC * Real.log (|s.im| + 2) := by
    simpa [Z] using hcount
  have herr' : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
      ∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤
      wideC * Real.log (|s.im| + 2) := by
    simpa [Z] using herr
  have hsum_le : ‖∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤
      6 * (∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℝ)) := by
    calc
      ‖∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖
          ≤ ∑ w ∈ Z, ‖(analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℝ) * 6 := by
            apply Finset.sum_le_sum
            intro w hw
            have hwset : w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧
                riemannZeta w = 0} := by simpa [Z] using hw
            have hwre : w.re = 1 / 2 := zero_re_eq_half_of_mem_wide (hRH := hRH) hwset
            have hdist : (1 / 6 : ℝ) ≤ ‖s - w‖ := by
              have hsix : (1 / 6 : ℝ) ≤ s.re - 1 / 2 := by
                have hre' : (2 / 3 : ℝ) ≤ s.re := by simpa [perronRe] using hre1
                linarith
              calc
                (1 / 6 : ℝ) ≤ s.re - 1 / 2 := hsix
                _ = (s - w).re := by simp [hwre]
                _ ≤ ‖s - w‖ := Complex.re_le_norm _
            have hpos : 0 < ‖s - w‖ := lt_of_lt_of_le (by norm_num) hdist
            have hnorm : ‖(analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ =
                (analyticOrderNatAt riemannZeta w : ℝ) / ‖s - w‖ := by
              rw [norm_div, Complex.norm_natCast]
            rw [hnorm]
            have hnonneg : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta w : ℝ) :=
              Nat.cast_nonneg _
            calc
              (analyticOrderNatAt riemannZeta w : ℝ) / ‖s - w‖
                  ≤ (analyticOrderNatAt riemannZeta w : ℝ) / (1 / 6) :=
                    div_le_div_of_nonneg_left hnonneg (by norm_num) hdist
              _ = (analyticOrderNatAt riemannZeta w : ℝ) * 6 := by ring_nf
      _ = 6 * (∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℝ)) := by
            rw [Finset.mul_sum]
            ring_nf
  have hsinv : ‖(1 : ℂ) / (s - 1)‖ ≤ 3 := by
    have hs : s.re = 2 / 3 := by simpa [perronRe] using hre
    have hre_sub : (s - 1).re = -(1 / 3) := by
      simp [hs]
      norm_num
    have hdist : (1 / 3 : ℝ) ≤ ‖s - 1‖ := by
      calc
        (1 / 3 : ℝ) = |(s - 1).re| := by rw [hre_sub]; norm_num
        _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    have hpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
    rw [norm_div, norm_one, div_le_iff₀ hpos]
    linarith
  have hdecomp : logDeriv riemannZeta s =
      (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
        ∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)) -
      ((1 : ℂ) / (s - 1) -
        ∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)) := by
    change deriv riemannZeta s / riemannZeta s = _
    ring_nf
  rw [hdecomp]
  calc
    ‖(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
        ∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)) -
      ((1 : ℂ) / (s - 1) -
        ∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w))‖
        ≤ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
            ∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ +
          ‖(1 : ℂ) / (s - 1) -
            ∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ :=
          norm_sub_le _ _
    _ ≤ wideC * Real.log (|s.im| + 2) +
          (‖(1 : ℂ) / (s - 1)‖ +
            ‖∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖) := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ wideC * Real.log (|s.im| + 2) + (3 +
          6 * (∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℝ))) := by
          apply add_le_add le_rfl
          exact add_le_add hsinv hsum_le
    _ ≤ wideC * Real.log (|s.im| + 2) + (3 +
          6 * (wideC * Real.log (|s.im| + 2))) := by
          have h6 := mul_le_mul_of_nonneg_left hcount' (by norm_num : (0 : ℝ) ≤ 6)
          linarith
    _ = 7 * wideC * Real.log (|s.im| + 2) + 3 := by ring_nf

/-- The uniform `O (log X)` bound for `ζ'/ζ` on `Re s = 2/3`, `|Im s| ≤ 3 X^3`,
without any lower bound on the height. -/
theorem norm_logDeriv_perronLine_le {X : ℕ → ℝ} {n : ℕ} {u : ℝ}
    (hX : 1 < X n) (hU : 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine) (hu : |u| ≤ 3 * X n ^ 3) :
    ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤ tailK * bandLog X n := by
  have hbase := norm_logDeriv_le_of_perronRe (s := perronLine perronRe u) hRH
    (by simp [perronLine])
  have hbase' : ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤
      7 * wideC * Real.log (|u| + 2) + 3 := by
    simpa [perronLine] using hbase
  have hlog_le := log_abs_add_two_le_four_bandLog hX hU hu
  have hL1 : 1 ≤ bandLog X n := by linarith
  have hw7 : (0 : ℝ) ≤ 7 * wideC := mul_nonneg (by norm_num) wideC_pos.le
  have hmul : 7 * wideC * Real.log (|u| + 2) ≤
      7 * wideC * (4 * bandLog X n) :=
    mul_le_mul_of_nonneg_left hlog_le hw7
  have hmul' : 7 * wideC * Real.log (|u| + 2) ≤ 28 * wideC * bandLog X n := by
    calc
      7 * wideC * Real.log (|u| + 2)
          ≤ 7 * wideC * (4 * bandLog X n) := hmul
      _ = 28 * wideC * bandLog X n := by ring
  have h3 : 3 ≤ 3 * bandLog X n := by linarith
  have hb : 7 * wideC * Real.log (|u| + 2) + 3 ≤ tailK * bandLog X n := by
    unfold tailK
    linarith
  exact hbase'.trans hb

/-- The eventual form of `norm_logDeriv_perronLine_le`. -/
theorem stripZetaBoundPerronRe_of_RH {X : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 3 * X n ^ 3 →
      ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤ tailK * bandLog X n :=
  Filter.Eventually.of_forall fun n u hu =>
    norm_logDeriv_perronLine_le (n := n) (u := u) (hX n) (hU n) hRH hu

/-! ## The exact tail identity -/

/-- Continuity of the vertical-strip integrand on the whole line
`Re s = 2/3` under the Riemann hypothesis. -/
theorem continuous_stripIntegrand {v : ℝ} (hv : 0 < v) (t : ℝ)
    (hRH : RiemannZetaZerosOnLine) :
    Continuous (stripIntegrand v t) := by
  have hg : Continuous fun τ : ℝ =>
      logDeriv riemannZeta (perronLine perronRe (τ + t)) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hsne : perronLine perronRe (τ + t) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp [perronLine, perronRe] at hre
      norm_num at hre
    have hz : riemannZeta (perronLine perronRe (τ + t)) ≠ 0 :=
      riemannZeta_ne_zero_of_RH_ge hRH (by simp [perronLine]) hsne
    have hdiff := differentiableAt_logDeriv_riemannZeta hsne hz
    have hline : Continuous fun x : ℝ => perronLine perronRe (x + t) := by
      unfold perronLine
      fun_prop
    have hcomp : ContinuousAt
        (fun x : ℝ => logDeriv riemannZeta (perronLine perronRe (x + t))) τ :=
      hdiff.continuousAt.comp_of_eq
        (f := fun x : ℝ => perronLine perronRe (x + t))
        (y := perronLine perronRe (τ + t)) hline.continuousAt rfl
    exact hcomp
  have hcp : Continuous fun τ : ℝ => (v : ℂ) ^ perronLine perronRe τ := by
    have hdiff : Differentiable ℂ fun z : ℂ => (v : ℂ) ^ z :=
      fun z => (GlobalTheory.ExplicitRect.analyticAt_cpow hv z).differentiableAt
    exact hdiff.continuous.comp (by unfold perronLine; fun_prop)
  have hden : ∀ τ : ℝ, perronLine perronRe τ ≠ 0 := fun τ =>
    GlobalTheory.PerronKernel.ne_zero_of_re (by norm_num [perronRe])
  have hdencont : Continuous fun τ : ℝ => perronLine perronRe τ := by
    unfold perronLine
    fun_prop
  unfold stripIntegrand
  exact hg.neg.mul (hcp.div hdencont hden)

/-- **The exact integral difference identity.**  Raising the truncation height
from `T` to `T + 1` changes `verticalZetaSum` only by the two unit-length end
pieces `[-T-1, -T]` and `[T, T+1]`. -/
theorem verticalZetaSum_tail_identity {v t T : ℝ}
    (hcont : Continuous (stripIntegrand v t)) :
    verticalZetaSum v t (T + 1) - verticalZetaSum v t T =
      (1 / (2 * Real.pi) : ℂ) *
        ((∫ τ in (-(T + 1))..(-T), stripIntegrand v t τ) +
          (∫ τ in T..(T + 1), stripIntegrand v t τ)) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (stripIntegrand v t) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have h1 : (∫ τ in (-(T + 1))..(T + 1), stripIntegrand v t τ) =
      (∫ τ in (-(T + 1))..(-T), stripIntegrand v t τ) +
        ∫ τ in (-T)..(T + 1), stripIntegrand v t τ :=
    (intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)).symm
  have h2 : (∫ τ in (-T)..(T + 1), stripIntegrand v t τ) =
      (∫ τ in (-T)..T, stripIntegrand v t τ) +
        ∫ τ in T..(T + 1), stripIntegrand v t τ :=
    (intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)).symm
  unfold verticalZetaSum
  rw [h1, h2]
  ring

/-! ## The elementary tail estimate -/

/-- **The vertical tail is `O (M v^{2/3} / T)`.**  A uniform bound `M` for
`ζ'/ζ` on `Re s = 2/3`, `|Im s| ≤ 3 T`, bounds the change of the truncated
vertical integral between heights `T` and `T + 1` by
`M v^{2/3} / (π T)`. -/
theorem norm_verticalTail_le {v t T M : ℝ}
    (hv : 0 < v) (hT : 0 < T) (hT1 : 1 ≤ T) (hM : 0 ≤ M) (ht : |t| ≤ T)
    (hcont : Continuous (stripIntegrand v t))
    (hbound : ∀ u : ℝ, |u| ≤ 3 * T →
      ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤ M) :
    ‖verticalZetaSum v t (T + 1) - verticalZetaSum v t T‖ ≤
      M * v ^ perronRe / (Real.pi * T) := by
  have hpoint : ∀ τ : ℝ, T ≤ |τ| → |τ + t| ≤ 3 * T →
      ‖stripIntegrand v t τ‖ ≤ M * v ^ perronRe / T := by
    intro τ hτ hτt
    have hz := hbound (τ + t) hτt
    have hnormτ : T ≤ ‖perronLine perronRe τ‖ := by
      have him : (perronLine perronRe τ).im = τ := by simp [perronLine]
      calc
        T ≤ |τ| := hτ
        _ = |(perronLine perronRe τ).im| := by rw [him]
        _ ≤ ‖perronLine perronRe τ‖ := Complex.abs_im_le_norm _
    have hinv : ‖(perronLine perronRe τ)⁻¹‖ ≤ 1 / T := by
      rw [norm_inv]
      calc
        ‖perronLine perronRe τ‖⁻¹ ≤ T⁻¹ := inv_anti₀ hT hnormτ
        _ = 1 / T := by rw [one_div]
    calc
      ‖stripIntegrand v t τ‖
          = ‖logDeriv riemannZeta (perronLine perronRe (τ + t))‖ *
              (v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖) := by
            unfold stripIntegrand
            rw [norm_mul, norm_neg, norm_div, norm_inv,
              Complex.norm_cpow_eq_rpow_re_of_pos hv, div_eq_mul_inv]
            simp [perronLine]
      _ ≤ M * (v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖) :=
            mul_le_mul_of_nonneg_right hz
              (mul_nonneg (Real.rpow_nonneg hv.le _) (norm_nonneg _))
      _ ≤ M * (v ^ perronRe * (1 / T)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hv.le _)) hM
      _ = M * v ^ perronRe / T := by ring
  have hIntpos : ‖∫ τ in T..(T + 1), stripIntegrand v t τ‖ ≤
      M * v ^ perronRe / T := by
    have hb : ∀ τ ∈ Set.uIoc T (T + 1), ‖stripIntegrand v t τ‖ ≤
        M * v ^ perronRe / T := by
      intro τ hτ
      rw [Set.uIoc_of_le (by linarith : T ≤ T + 1)] at hτ
      have ht' := abs_le.mp ht
      refine hpoint τ ?_ ?_
      · rw [abs_of_nonneg (le_trans hT.le hτ.1.le)]
        exact hτ.1.le
      · rw [abs_le]
        constructor <;> nlinarith [hτ.1, hτ.2, ht'.1, ht'.2, hT1]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [show (T + 1) - T = (1 : ℝ) by ring, abs_one, mul_one] at h
    exact h
  have hIntneg : ‖∫ τ in (-(T + 1))..(-T), stripIntegrand v t τ‖ ≤
      M * v ^ perronRe / T := by
    have hb : ∀ τ ∈ Set.uIoc (-(T + 1)) (-T), ‖stripIntegrand v t τ‖ ≤
        M * v ^ perronRe / T := by
      intro τ hτ
      rw [Set.uIoc_of_le (by linarith : -(T + 1) ≤ -T)] at hτ
      have ht' := abs_le.mp ht
      refine hpoint τ ?_ ?_
      · rw [abs_of_nonpos (by linarith [hτ.2] : τ ≤ 0)]
        linarith [hτ.2]
      · rw [abs_le]
        constructor <;> nlinarith [hτ.1, hτ.2, ht'.1, ht'.2, hT1]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [show (-T) - (-(T + 1)) = (1 : ℝ) by ring, abs_one, mul_one] at h
    exact h
  have hnormfac : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [verticalZetaSum_tail_identity hcont, norm_mul, hnormfac]
  calc
    (1 / (2 * Real.pi)) *
        ‖(∫ τ in (-(T + 1))..(-T), stripIntegrand v t τ) +
          (∫ τ in T..(T + 1), stripIntegrand v t τ)‖
        ≤ (1 / (2 * Real.pi)) *
            (‖∫ τ in (-(T + 1))..(-T), stripIntegrand v t τ‖ +
              ‖∫ τ in T..(T + 1), stripIntegrand v t τ‖) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact norm_add_le _ _
    _ ≤ (1 / (2 * Real.pi)) *
          (M * v ^ perronRe / T + M * v ^ perronRe / T) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact add_le_add hIntneg hIntpos
    _ = M * v ^ perronRe / (Real.pi * T) := by
          field_simp
          ring

/-! ## The minimal zeta input and the tail bound -/

/-- **The smallest explicit zeta estimate for the vertical tail.**  A uniform
`O (U^C)` bound for `ζ'/ζ` on `Re s = 2/3`, `|Im s| ≤ 3 X^3`, with no lower
bound on the height. -/
def LineBoundAtPerronRe (X : ℕ → ℝ) (K : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 3 * X n ^ 3 →
    ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤ K n * (bandLog X n) ^ C

/-- **`LineBoundAtPerronRe` implies `VerticalTailBound`.**  The vertical tail is
bounded by `(K n / π) * v^(2/3) * U^C / X^3`, and `v^(2/3) ≤ v`. -/
theorem verticalTailBound_of_lineBound {X : ℕ → ℝ} {K : ℕ → ℝ} {C : ℝ}
    (hRH : RiemannZetaZerosOnLine)
    (hX : ∀ n, 1 < X n)
    (hK : ∀ᶠ n : ℕ in atTop, 0 ≤ K n)
    (hL : LineBoundAtPerronRe X K C) :
    VerticalTailBound X (fun n => K n / Real.pi) C := by
  filter_upwards [hK, hL] with n hk hn
  intro v t hv ht
  have hv0 : 0 < v := by linarith
  have hXpos : 0 < X n := lt_trans zero_lt_one (hX n)
  have hTpos : 0 < X n ^ 3 := pow_pos hXpos 3
  have hT1 : (1 : ℝ) ≤ X n ^ 3 := by
    have hgt : (1 : ℝ) < X n ^ 3 := one_lt_pow₀ (hX n) (by norm_num : (3 : ℕ) ≠ 0)
    linarith
  have hU0 : 0 ≤ bandLog X n := (Real.log_pos (hX n)).le
  have hUc : 0 ≤ (bandLog X n) ^ C := Real.rpow_nonneg hU0 C
  have hcont : Continuous (stripIntegrand v t) := continuous_stripIntegrand hv0 t hRH
  have htail := norm_verticalTail_le (v := v) (t := t) (T := X n ^ 3)
    (M := K n * (bandLog X n) ^ C) hv0 hTpos hT1
    (mul_nonneg hk hUc) ht hcont (fun u hu => hn u hu)
  refine htail.trans ?_
  unfold shiftHorizontal
  have hv23 : v ^ perronRe ≤ v := by
    rw [perronRe]
    exact Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hstep : v ^ perronRe * (bandLog X n) ^ C / X n ^ 3 ≤
      v * (bandLog X n) ^ C / X n ^ 3 := by
    apply div_le_div_of_nonneg_right ?_ (pow_nonneg hXpos.le 3)
    exact mul_le_mul_of_nonneg_right hv23 hUc
  calc
    K n * (bandLog X n) ^ C * v ^ perronRe / (Real.pi * X n ^ 3)
        = (K n / Real.pi) * (v ^ perronRe * (bandLog X n) ^ C / X n ^ 3) := by
          field_simp
    _ ≤ (K n / Real.pi) * (v * (bandLog X n) ^ C / X n ^ 3) :=
          mul_le_mul_of_nonneg_left hstep (div_nonneg hk Real.pi_pos.le)

/-- **The unconditional vertical tail bound.**  Under the Riemann hypothesis,
`VerticalTailBound` holds with the explicit constant `tailK / π` and exponent
`1`, where `tailK = 28 * wideC + 3` comes from the zero-counting estimate for
`ζ'/ζ` at `Re s = 2/3`. -/
theorem verticalTailBound_of_RH {X : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine) :
    VerticalTailBound X (fun _ => tailK / Real.pi) 1 := by
  refine verticalTailBound_of_lineBound hRH hX
    (Filter.Eventually.of_forall fun _ => tailK_nonneg) ?_
  filter_upwards [stripZetaBoundPerronRe_of_RH hX hU hRH] with n hn
  intro u hu
  rw [Real.rpow_one]
  exact hn u hu

/-! ## The same tail bound from the existing pole-free strip bound -/

/-- The pole-free strip bound plus the near-axis estimate give
`LineBoundAtPerronRe`.  This explicitly uses the existing
`StripZetaBoundOffPole` for heights `|Im s| ≥ 1`, and
`norm_logDeriv_perronLine_le` for `|Im s| ≤ 1`. -/
theorem lineBoundAtPerronRe_of_stripOffPole {X : ℕ → ℝ} {Kstrip : ℕ → ℝ}
    {Cstrip : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine)
    (hstrip : StripZetaBoundOffPole X Kstrip Cstrip)
    (hKstrip : ∀ᶠ n : ℕ in atTop, 0 ≤ Kstrip n)
    (hC : 1 ≤ Cstrip) :
    LineBoundAtPerronRe X (fun n => Kstrip n + tailK) Cstrip := by
  filter_upwards [hstrip, hKstrip] with n hs hk
  intro u hu
  have hL1 : 1 ≤ bandLog X n := by linarith [hU n]
  have hL0 : 0 ≤ bandLog X n := by linarith
  have hpow : bandLog X n ≤ (bandLog X n) ^ Cstrip := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 hC
    simpa using this
  have hnear : ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤
      tailK * bandLog X n :=
    norm_logDeriv_perronLine_le (hX n) (hU n) hRH hu
  have hUc : 0 ≤ (bandLog X n) ^ Cstrip := Real.rpow_nonneg hL0 Cstrip
  by_cases hcase : 1 ≤ |u|
  · have hb := hs (perronLine perronRe u) (by simp [perronLine])
      (by simp [perronLine]; norm_num [perronRe])
      (by simpa [perronLine] using hcase)
      (by simpa [perronLine] using hu)
    calc
      ‖logDeriv riemannZeta (perronLine perronRe u)‖
          ≤ Kstrip n * (bandLog X n) ^ Cstrip := hb
      _ ≤ (Kstrip n + tailK) * (bandLog X n) ^ Cstrip := by
            have := mul_le_mul_of_nonneg_right (show Kstrip n ≤ Kstrip n + tailK by
              linarith [tailK_pos]) hUc
            linarith
  · calc
      ‖logDeriv riemannZeta (perronLine perronRe u)‖
          ≤ tailK * bandLog X n := hnear
      _ ≤ tailK * (bandLog X n) ^ Cstrip :=
            mul_le_mul_of_nonneg_left hpow tailK_nonneg
      _ ≤ (Kstrip n + tailK) * (bandLog X n) ^ Cstrip := by
            have := mul_le_mul_of_nonneg_right (show tailK ≤ Kstrip n + tailK by
              linarith [hk]) hUc
            linarith

/-- **`VerticalTailBound` from `StripZetaBoundOffPole` and the Riemann
hypothesis.**  The final constant is `(Kstrip n + tailK) / π`. -/
theorem verticalTailBound_of_stripOffPole {X : ℕ → ℝ} {Kstrip : ℕ → ℝ}
    {Cstrip : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine)
    (hstrip : StripZetaBoundOffPole X Kstrip Cstrip)
    (hKstrip : ∀ᶠ n : ℕ in atTop, 0 ≤ Kstrip n)
    (hC : 1 ≤ Cstrip) :
    VerticalTailBound X (fun n => (Kstrip n + tailK) / Real.pi) Cstrip :=
  verticalTailBound_of_lineBound hRH hX
    (hKstrip.mono fun _ hn => add_nonneg hn tailK_nonneg)
    (lineBoundAtPerronRe_of_stripOffPole hX hU hRH hstrip hKstrip hC)

/-- **The `StripZetaBoundOffPole` route, with the strip bound itself proved.**
The resulting constant is `(stripK + tailK) / π`, where `stripK` is the explicit
constant of `stripZetaBoundOffPole_of_RH`. -/
theorem verticalTailBound_of_RH_strip {X : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine) :
    VerticalTailBound X (fun _ => (stripK + tailK) / Real.pi) 1 :=
  verticalTailBound_of_stripOffPole hX hU hRH
    (stripZetaBoundOffPole_of_RH hX hU hRH)
    (Filter.Eventually.of_forall fun _ => stripK_nonneg) le_rfl

/-! ## The L21.2 remainder with the tail discharged -/

/-- **`PerronShiftRemainder` with the vertical tail discharged.**  This is
`perronShiftRemainder_of_RH_stripBound` with `Ktail = tailK / π` supplied by
`verticalTailBound_of_RH`. -/
theorem perronShiftRemainder_of_RH_stripTail {X : ℕ → ℝ} {c : ℝ}
    {Kper Kref : ℕ → ℝ}
    (hRH : RiemannZetaZerosOnLine)
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRef : ReferencePerronBound X c Kref 1)
    (hKref : ∀ᶠ n : ℕ in atTop, 0 ≤ Kref n)
    (hK : ∀ᶠ n : ℕ in atTop,
      Kref n + (3 * Real.exp 1 / Real.pi) * stripK + tailK / Real.pi ≤ Kper n) :
    PerronShiftRemainder X c Kper 1 :=
  perronShiftRemainder_of_RH_stripBound hRH hX hU hRef
    (verticalTailBound_of_RH hX hU hRH) hKref
    (Filter.Eventually.of_forall fun _ =>
      div_nonneg tailK_nonneg Real.pi_pos.le) hK

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2TailBound.norm_logDeriv_le_of_perronRe
#print axioms Cogentic.RandomizedL21_2TailBound.norm_logDeriv_perronLine_le
#print axioms Cogentic.RandomizedL21_2TailBound.stripZetaBoundPerronRe_of_RH
#print axioms Cogentic.RandomizedL21_2TailBound.continuous_stripIntegrand
#print axioms Cogentic.RandomizedL21_2TailBound.verticalZetaSum_tail_identity
#print axioms Cogentic.RandomizedL21_2TailBound.norm_verticalTail_le
#print axioms Cogentic.RandomizedL21_2TailBound.verticalTailBound_of_lineBound
#print axioms Cogentic.RandomizedL21_2TailBound.verticalTailBound_of_RH
#print axioms Cogentic.RandomizedL21_2TailBound.lineBoundAtPerronRe_of_stripOffPole
#print axioms Cogentic.RandomizedL21_2TailBound.verticalTailBound_of_stripOffPole
#print axioms Cogentic.RandomizedL21_2TailBound.verticalTailBound_of_RH_strip
#print axioms Cogentic.RandomizedL21_2TailBound.perronShiftRemainder_of_RH_stripTail

end Cogentic.RandomizedL21_2TailBound
