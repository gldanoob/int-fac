import Cogentic.RandomizedL21_2Remainder
import Cogentic.RandomizedL21_2LineBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsMore

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-!
# L21.2: the uniform strip bound for `ζ'/ζ`

`Cogentic.RandomizedL21_2Remainder.StripZetaBound` asks for a uniform bound for
`ζ'/ζ` on the *closed* strip `2/3 ≤ Re s ≤ 3`, at heights `|Im s| ≤ 3 X³`.
That statement cannot hold as written: it contains the pole of `ζ` at `s = 1`.
Indeed `ζ(s) ~ 1/(s-1)` near `1`, so `ζ'/ζ(s) ~ -1/(s-1)`, which is unbounded
on every punctured neighbourhood of `1`.  The Perron contour only ever evaluates
`ζ'/ζ` at heights `|Im s| ≥ 1` (the contour is at height `T = X³ + 1` and the
twist has `|t| ≤ X³`), so the pole is never approached.

This file therefore isolates the true, pole-free form

```
StripZetaBoundOffPole X K C :
  ∀ᶠ n, ∀ s, 2/3 ≤ Re s → Re s ≤ 3 → 1 ≤ |Im s| → |Im s| ≤ 3 X n³ →
    ‖ζ'/ζ s‖ ≤ K n * (log X n)^C,
```

and proves it from the Riemann hypothesis plus the *unconditional* polynomial
upper bound for `ζ` in the strip.  The proof is the classical zero-counting /
log-derivative estimate of `GlobalTheory.ZetaWide.main`: on the disc of radius
`7/2` about `2 + i Im s`, the zeros of `ζ` are the critical-line zeros
(`Re w = 1/2`), so each term `1/(s-w)` is at most `6`, and their total number is
`O (log (|Im s| + 2))`.  The pole term `1/(s-1)` is at most `1` because
`|Im s| ≥ 1`.

The explicit constant is

```
28 * C_wide + 1 + (B_Λ + 1),
```

with `C_wide` the absolute constant of `GlobalTheory.ZetaWide.main` and
`B_Λ = ∑ ‖Λ(n)/n²‖` the absolutely convergent von Mangoldt series at `2`.  The
right-hand side is bounded by the same constant times `log X`, and the whole
argument is independent of `ZetaStripInput`: it only needs the Riemann
hypothesis (which is already an input of `perronShiftRemainder_of_RH_strip`).

We then replay `contourRemainderBound_of_strip` and
`perronShiftRemainder_of_RH_strip` with the pole-free hypothesis, obtaining the
same `ContourRemainderBound` and `PerronShiftRemainder` conclusions:

* `stripZetaBoundOffPole_of_RH` — the pole-free strip bound with the explicit
  constant `stripK` and exponent `1`;
* `contourRemainderBound_of_stripOffPole` — the same horizontal estimate as
  `contourRemainderBound_of_strip`;
* `perronShiftRemainder_of_RH_stripOffPole` — the exact analogue of
  `perronShiftRemainder_of_RH_strip`;
* `perronShiftRemainder_of_RH_stripBound` — the fully composed version, with no
  strip hypothesis left;
* `stripZetaBound_of_RH_and_nearPole` — the literal `StripZetaBound` from the
  pole-free bound plus the explicit near-pole residual.

The literal `StripZetaBound` is recovered from the pole-free bound plus an explicit
near-pole hypothesis; the missing near-pole hypothesis is exactly the pole
itself, and is never used by the contour.  In particular
`perronShiftRemainder_of_RH_strip` cannot be applied with the literal
`StripZetaBound` derived here (no such derivation exists), but
`perronShiftRemainder_of_RH_stripOffPole` produces exactly the same conclusion
from the part of the strip that the contour visits.

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2StripBound

open Filter Real MeasureTheory Complex
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL21_2Remainder

/-! ## The pole-free strip bound -/

/-- The true strip bound for `ζ'/ζ`: uniform on `2/3 ≤ Re s ≤ 3`,
`1 ≤ |Im s| ≤ 3 X³`.  The lower height bound `1 ≤ |Im s|` keeps the evaluation
away from the pole at `s = 1`; the Perron contour always satisfies it. -/
def StripZetaBoundOffPole (X : ℕ → ℝ) (K : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, perronRe ≤ s.re → s.re ≤ 3 →
    1 ≤ |s.im| → |s.im| ≤ 3 * X n ^ 3 →
      ‖logDeriv riemannZeta s‖ ≤ K n * (bandLog X n) ^ C

/-- The literal `StripZetaBound` implies the pole-free form (the extra hypothesis
`1 ≤ |Im s|` is simply discarded).  This records that the only difference
between the two statements is the punctured neighbourhood of the pole. -/
theorem stripZetaBoundOffPole_of_stripZetaBound {X : ℕ → ℝ} {K : ℕ → ℝ} {C : ℝ}
    (h : StripZetaBound X K C) : StripZetaBoundOffPole X K C := by
  filter_upwards [h] with n hn
  intro s h1 h2 _ h3
  exact hn s h1 h2 h3

/-- The near-pole part of the literal `StripZetaBound`: heights `|Im s| ≤ 1`.
This is the only piece that the pole-free estimate does not cover. -/
def StripZetaBoundNearPole (X : ℕ → ℝ) (K : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, perronRe ≤ s.re → s.re ≤ 3 →
    |s.im| ≤ 1 → ‖logDeriv riemannZeta s‖ ≤ K n * (bandLog X n) ^ C

/-- The literal `StripZetaBound` is exactly the pole-free bound together with
the near-pole bound.  `StripZetaBoundNearPole` is the only part that cannot be
proved, because it contains the pole `s = 1`; the contour never uses it. -/
theorem stripZetaBound_of_offPole_and_nearPole {X : ℕ → ℝ} {K : ℕ → ℝ} {C : ℝ}
    (hoff : StripZetaBoundOffPole X K C) (hnear : StripZetaBoundNearPole X K C) :
    StripZetaBound X K C := by
  filter_upwards [hoff, hnear] with n hoffn hnearn
  intro s h1 h2 h3
  by_cases hge : 1 ≤ |s.im|
  · exact hoffn s h1 h2 hge h3
  · exact hnearn s h1 h2 (le_of_lt (lt_of_not_ge hge))

/-! ## The Riemann-zeta logarithmic derivative away from the pole -/

/-- The absolute constant of the zero-counting / log-derivative estimate. -/
noncomputable def wideC : ℝ := Classical.choose GlobalTheory.ZetaWide.main

lemma wideC_pos : 0 < wideC := by
  unfold wideC
  exact (Classical.choose_spec GlobalTheory.ZetaWide.main).1

lemma wideC_spec :
    ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0},
        (analyticOrderNatAt riemannZeta w : ℝ)) ≤
        wideC * Real.log (|s.im| + 2) ∧
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
        ∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0},
          (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤
        wideC * Real.log (|s.im| + 2) := by
  unfold wideC
  exact (Classical.choose_spec GlobalTheory.ZetaWide.main).2

/-- Under the Riemann hypothesis, `ζ` has no zeros in `Re s ≥ 2/3` except the
pole at `1`. -/
theorem riemannZeta_ne_zero_of_RH_ge {s : ℂ} (hRH : RiemannZetaZerosOnLine)
    (hre : perronRe ≤ s.re) (hne : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hnot_triv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre' : s.re = -2 * ((n : ℝ) + 1) := by
      have := congrArg Complex.re hn
      simpa using this
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hper : (0 : ℝ) < perronRe := by norm_num [perronRe]
    nlinarith
  have hhalf := hRH s hz hnot_triv hne
  have hper2 : (2 / 3 : ℝ) ≤ s.re := by simpa [perronRe] using hre
  linarith

/-- A zero in the zero-counting disc of `GlobalTheory.ZetaWide.main` has real
part `1/2` under the Riemann hypothesis. -/
theorem zero_re_eq_half_of_mem_wide {hRH : RiemannZetaZerosOnLine} {s w : ℂ}
    (hw : w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧
      riemannZeta w = 0}) : w.re = 1 / 2 := by
  obtain ⟨hball, hw1, hwz⟩ := hw
  have hnot_triv : ¬ ∃ n : ℕ, w = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre' : w.re = -2 * ((n : ℝ) + 1) := by
      have := congrArg Complex.re hn
      simpa using this
    have hre_ball : -(3 / 2 : ℝ) ≤ w.re := by
      have h := Complex.abs_re_le_norm (w - (2 + s.im * I))
      have : |w.re - 2| ≤ 7 / 2 := by
        calc |w.re - 2| = |(w - (2 + s.im * I)).re| := by simp
          _ ≤ ‖w - (2 + s.im * I)‖ := Complex.abs_re_le_norm _
          _ ≤ 7 / 2 := hball
      have := (abs_le.mp this).1
      linarith
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith
  exact hRH w hwz hnot_triv hw1

/-- **`ζ'/ζ` on the left part of the strip, away from the pole.**  For
`2/3 ≤ Re s ≤ 2` and `1 ≤ |Im s|`, the zero-counting estimate gives

```
‖ζ'/ζ s‖ ≤ 7 * C_wide * log (|Im s| + 2) + 1.
```

The factor `7` is `1` (the pole term) plus `6` (each zero term, since the
distance from `Re s ≥ 2/3` to a zero at `Re w = 1/2` is at least `1/6`). -/
theorem norm_logDeriv_le_of_leftStrip {s : ℂ} (hRH : RiemannZetaZerosOnLine)
    (hre1 : perronRe ≤ s.re) (hre2 : s.re ≤ 2) (him : 1 ≤ |s.im|) :
    ‖logDeriv riemannZeta s‖ ≤ 7 * wideC * Real.log (|s.im| + 2) + 1 := by
  have hre_low : -1 ≤ s.re := by
    have hper : (-1 : ℝ) ≤ perronRe := by norm_num [perronRe]
    linarith
  have hsne : s ≠ 1 := by
    intro h
    have him0 : s.im = 0 := by rw [h]; simp
    rw [him0, abs_zero] at him
    norm_num at him
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
  have hsinv : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    have hdist : (1 : ℝ) ≤ ‖s - 1‖ := by
      calc
        (1 : ℝ) ≤ |s.im| := him
        _ = |(s - 1).im| := by simp
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have hpos : 0 < ‖s - 1‖ := lt_of_lt_of_le zero_lt_one hdist
    rw [norm_div, norm_one]
    rw [div_le_one hpos]
    exact hdist
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
    _ ≤ wideC * Real.log (|s.im| + 2) + (1 +
          6 * (∑ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℝ))) := by
          gcongr
    _ ≤ wideC * Real.log (|s.im| + 2) + (1 +
          6 * (wideC * Real.log (|s.im| + 2))) := by
          gcongr
    _ = 7 * wideC * Real.log (|s.im| + 2) + 1 := by ring_nf

/-! ## The von Mangoldt series constant at `2` -/

/-- The absolutely convergent von Mangoldt series at `2`,
`B_Λ = ∑ ‖Λ(n)/n²‖`.  It bounds `ζ'/ζ` on `Re s ≥ 2`. -/
noncomputable def mangoldtL2 : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (2 : ℂ) n‖

lemma mangoldtL2_nonneg : 0 ≤ mangoldtL2 :=
  tsum_nonneg fun _ => norm_nonneg _

/-- **`ζ'/ζ` on the right part of the strip.**  For `Re s ≥ 2` the Dirichlet
series of the von Mangoldt function converges absolutely, and
`ζ'/ζ s = -∑ Λ(n)/n^s`, so the logarithmic derivative is bounded by its value
at `2`. -/
theorem norm_logDeriv_le_mangoldtL2 {s : ℂ} (hs : 2 ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ mangoldtL2 := by
  have hs1 : 1 < s.re := by linarith
  have hs2 : 1 < ((2 : ℂ).re) := by norm_num
  have hsum_s := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs1
  have hsum_2 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ)) hs2
  have hId := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := s) hs1
  have hlog : logDeriv riemannZeta s =
      - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    rw [hId]
    change deriv riemannZeta s / riemannZeta s = _
    ring_nf
  rw [hlog, norm_neg]
  have hnorm : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤
      ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
    norm_tsum_le_tsum_norm hsum_s.norm
  have hmono : ∀ n : ℕ,
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (2 : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · rfl
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hn1 hs
      exact div_le_div_of_nonneg_left (norm_nonneg _)
        (Real.rpow_pos_of_pos (by linarith) 2) hpow
  calc
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖
        ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
          hnorm
    _ ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (2 : ℂ) n‖ := by
          exact hsum_s.norm.tsum_le_tsum hmono hsum_2.norm
    _ = mangoldtL2 := rfl

/-! ## The explicit strip constant -/

/-- The explicit constant of the pole-free strip bound,
`28 * C_wide + 1 + B_Λ + 1`. -/
noncomputable def stripK : ℝ := 28 * wideC + 1 + (mangoldtL2 + 1)

lemma stripK_pos : 0 < stripK := by
  unfold stripK
  have hw := wideC_pos
  have hm := mangoldtL2_nonneg
  positivity

lemma stripK_nonneg : 0 ≤ stripK := stripK_pos.le

/-- The elementary comparison `log (|u| + 2) ≤ 4 log X` for `|u| ≤ 3 X³` and
`log X ≥ 3`. -/
theorem log_abs_add_two_le_four_bandLog {X : ℕ → ℝ} {n : ℕ} {u : ℝ}
    (hX : 1 < X n) (hU : 3 ≤ bandLog X n) (hu : |u| ≤ 3 * X n ^ 3) :
    Real.log (|u| + 2) ≤ 4 * bandLog X n := by
  have hXpos : 0 < X n := lt_trans zero_lt_one hX
  have hX4 : (4 : ℝ) ≤ X n := by
    have h4exp : (4 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ)
      norm_num at this ⊢
      exact this
    have hexp : Real.exp 3 ≤ X n := by
      have := Real.exp_le_exp.mpr (show (3 : ℝ) ≤ bandLog X n by linarith)
      simpa [bandLog, Real.exp_log hXpos] using this
    linarith
  have harg : |u| + 2 ≤ 4 * X n ^ 3 := by
    have h1 : |u| + 2 ≤ 3 * X n ^ 3 + 2 := by linarith [abs_nonneg u]
    have h2 : (2 : ℝ) ≤ X n ^ 3 := by
      have h4pow : (4 : ℝ) ^ 3 ≤ X n ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hX4 3
      norm_num at h4pow
      linarith
    nlinarith
  have hle : Real.log (|u| + 2) ≤ Real.log (4 * X n ^ 3) :=
    Real.log_le_log (by linarith [abs_nonneg u]) harg
  have heq : Real.log (4 * X n ^ 3) = Real.log 4 + 3 * bandLog X n := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 hXpos.ne'), Real.log_pow]
    simp [bandLog]
  have hlog4 : Real.log 4 ≤ bandLog X n := by
    exact Real.log_le_log (by norm_num) hX4
  linarith

/-- **The pole-free strip bound from the Riemann hypothesis and the
unconditional upper bound for `ζ`.**  The constant is `stripK` and the exponent
is `1`; both branches (`Re s ≤ 2` and `Re s ≥ 2`) are bounded by `stripK log X`. -/
theorem stripZetaBoundOffPole_of_RH {X : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine) :
    StripZetaBoundOffPole X (fun _ => stripK) 1 := by
  refine Filter.Eventually.of_forall ?_
  intro n s hre1 hre2 him1 him2
  set L := bandLog X n with hLdef
  have hL3 : 3 ≤ L := hU n
  have hL1 : 1 ≤ L := by linarith
  have hlog_le : Real.log (|s.im| + 2) ≤ 4 * L :=
    log_abs_add_two_le_four_bandLog (hX n) hL3 him2
  have hlog_nonneg : 0 ≤ Real.log (|s.im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg s.im])
  rw [Real.rpow_one]
  by_cases hcase : s.re ≤ 2
  · have hleft' : ‖logDeriv riemannZeta s‖ ≤
        7 * wideC * Real.log (|s.im| + 2) + 1 :=
      norm_logDeriv_le_of_leftStrip hRH hre1 hcase him1
    have hb : 7 * wideC * Real.log (|s.im| + 2) + 1 ≤ (28 * wideC + 1) * L := by
      have hw := wideC_pos
      nlinarith [hlog_le, hL1]
    calc
      ‖logDeriv riemannZeta s‖ ≤ 7 * wideC * Real.log (|s.im| + 2) + 1 := hleft'
      _ ≤ (28 * wideC + 1) * L := hb
      _ ≤ stripK * L := by
            have hmono : 28 * wideC + 1 ≤ stripK := by
              unfold stripK
              have hm := mangoldtL2_nonneg
              linarith
            exact mul_le_mul_of_nonneg_right hmono (by linarith)
  · have hright : ‖logDeriv riemannZeta s‖ ≤ mangoldtL2 :=
      norm_logDeriv_le_mangoldtL2 (le_of_lt (lt_of_not_ge hcase))
    calc
      ‖logDeriv riemannZeta s‖ ≤ mangoldtL2 := hright
      _ ≤ stripK * L := by
            have hm : mangoldtL2 ≤ stripK := by
              unfold stripK
              have hw : 0 ≤ 28 * wideC := mul_nonneg (by norm_num) wideC_pos.le
              linarith
            calc
              mangoldtL2 ≤ stripK := hm
              _ = stripK * 1 := by ring_nf
              _ ≤ stripK * L := by
                    exact mul_le_mul_of_nonneg_left hL1 stripK_nonneg

/-- **The contour remainder from the pole-free strip bound.**  This is exactly
`contourRemainderBound_of_strip`, with the strip hypothesis weakened to the
heights `|Im s| ≥ 1` that the contour actually visits. -/
theorem contourRemainderBound_of_stripOffPole {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ}
    {C : ℝ} {Kstrip : ℕ → ℝ}
    (hRH : RiemannZetaZerosOnLine) (hstrip : StripZetaBoundOffPole X Kstrip C)
    (hX : ∀ n, 1 < X n) (hKstrip : ∀ n, 0 ≤ Kstrip n)
    (hK : ∀ᶠ n : ℕ in atTop,
      (3 * Real.exp 1 / Real.pi) * Kstrip n ≤ K n) :
    ContourRemainderBound X c K C := by
  filter_upwards [hstrip, hK] with n hb hk
  intro v t hv hvB ht
  let T : ℝ := X n ^ 3 + 1
  have hX3pos : (0 : ℝ) < X n ^ 3 := pow_pos (lt_trans zero_lt_one (hX n)) 3
  have hX3gt : (1 : ℝ) < X n ^ 3 := one_lt_pow₀ (hX n) (by norm_num)
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : |t| < T := by
    have := abs_le.mp ht
    dsimp [T]
    linarith
  have hid := zetaShiftContourIdentity (v := v) (t := t) (T := T)
    (by linarith : 1 < v) hT htT (stripNoZeros_of_RH hRH)
  rw [hid]
  have hbound : ∀ σ ∈ Set.Icc perronRe (refRe v),
      ‖logDeriv riemannZeta ((σ : ℂ) + (T + t) * I)‖ ≤
          Kstrip n * (bandLog X n) ^ C ∧
      ‖logDeriv riemannZeta ((σ : ℂ) + (-T + t) * I)‖ ≤
          Kstrip n * (bandLog X n) ^ C := by
    intro σ hσ
    have hσre1 : perronRe ≤ σ := hσ.1
    have hσre2 : σ ≤ 3 := by
      exact hσ.2.trans (refRe_le_three hv)
    have ht' := abs_le.mp ht
    have him1top : |((σ : ℂ) + (T + t) * I).im| ≤ 3 * X n ^ 3 := by
      have him : ((σ : ℂ) + (T + t) * I).im = T + t := by simp
      rw [him]
      dsimp [T] at *
      rw [abs_le]
      constructor <;> nlinarith [hX3gt, ht'.1, ht'.2]
    have him1bot : |((σ : ℂ) + (-T + t) * I).im| ≤ 3 * X n ^ 3 := by
      have him : ((σ : ℂ) + (-T + t) * I).im = -T + t := by simp
      rw [him]
      dsimp [T] at *
      rw [abs_le]
      constructor <;> nlinarith [hX3gt, ht'.1, ht'.2]
    have hlowtop : 1 ≤ |((σ : ℂ) + (T + t) * I).im| := by
      have him : ((σ : ℂ) + (T + t) * I).im = T + t := by simp
      rw [him, abs_of_nonneg (by dsimp [T]; linarith [ht'.1])]
      dsimp [T]; linarith [ht'.1]
    have hlowbot : 1 ≤ |((σ : ℂ) + (-T + t) * I).im| := by
      have him : ((σ : ℂ) + (-T + t) * I).im = -T + t := by simp
      rw [him, abs_of_nonpos (by dsimp [T]; linarith [ht'.2])]
      dsimp [T]; linarith [ht'.2]
    exact ⟨hb ((σ : ℂ) + (T + t) * I) (by simpa using hσre1)
        (by simpa using hσre2) hlowtop him1top,
      hb ((σ : ℂ) + (-T + t) * I) (by simpa using hσre1)
        (by simpa using hσre2) hlowbot him1bot⟩
  have hh := norm_horizRemainder_le (v := v) (t := t) (T := T)
    (K := Kstrip n) (U := bandLog X n) (C := C) hv hT
    (hKstrip n) (Real.log_pos (hX n)).le hbound
  refine hh.trans ?_
  have hden : X n ^ 3 ≤ T := by dsimp [T]; linarith
  have hnum_nonneg : 0 ≤ v * (bandLog X n) ^ C :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (Real.log_pos (hX n)).le C)
  have hdiv : v * (bandLog X n) ^ C / T ≤
      v * (bandLog X n) ^ C / X n ^ 3 :=
    div_le_div_of_nonneg_left hnum_nonneg hX3pos hden
  unfold shiftHorizontal
  calc
    (3 * Real.exp 1 / Real.pi) * (Kstrip n * (v * (bandLog X n) ^ C / T))
        ≤ (3 * Real.exp 1 / Real.pi) *
            (Kstrip n * (v * (bandLog X n) ^ C / X n ^ 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hdiv (hKstrip n)) (by positivity)
    _ = ((3 * Real.exp 1 / Real.pi) * Kstrip n) *
          (v * (bandLog X n) ^ C / X n ^ 3) := by ring
    _ ≤ K n * (v * (bandLog X n) ^ C / X n ^ 3) :=
          mul_le_mul_of_nonneg_right hk
            (div_nonneg
              (mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_pos (hX n)).le C))
              (pow_nonneg (le_of_lt (lt_trans zero_lt_one (hX n))) 3))

/-- **`PerronShiftRemainder` from the Riemann hypothesis, the pole-free strip
bound, and the two explicit Perron inputs.**  Identical to
`perronShiftRemainder_of_RH_strip`, but the strip hypothesis only concerns the
heights actually used by the contour. -/
theorem perronShiftRemainder_of_RH_stripOffPole {X : ℕ → ℝ} {c : ℝ} {Kper : ℕ → ℝ}
    {Cper : ℝ} {Kstrip Kref Ktail : ℕ → ℝ}
    (hRH : RiemannZetaZerosOnLine)
    (hstrip : StripZetaBoundOffPole X Kstrip Cper)
    (hX : ∀ n, 1 < X n) (hKstrip : ∀ n, 0 ≤ Kstrip n)
    (hRef : ReferencePerronBound X c Kref Cper)
    (hTail : VerticalTailBound X Ktail Cper)
    (hKref : ∀ᶠ n : ℕ in atTop, 0 ≤ Kref n)
    (hKtail : ∀ᶠ n : ℕ in atTop, 0 ≤ Ktail n)
    (hK : ∀ᶠ n : ℕ in atTop,
      Kref n + (3 * Real.exp 1 / Real.pi) * Kstrip n + Ktail n ≤ Kper n) :
    PerronShiftRemainder X c Kper Cper := by
  refine perronShiftRemainder_of_bounds (X := X) (c := c) (Kper := Kper)
    (Cper := Cper) (Kref := Kref)
    (Kcont := fun n => (3 * Real.exp 1 / Real.pi) * Kstrip n) (Ktail := Ktail)
    hX hRef ?_ hTail hKref ?_ hKtail ?_
  · exact contourRemainderBound_of_stripOffPole hRH hstrip hX hKstrip
      (Filter.Eventually.of_forall fun _ => le_refl _)
  · exact Filter.Eventually.of_forall fun n =>
      mul_nonneg (by positivity) (hKstrip n)
  · exact hK

/-- **The fully composed bound.**  With `X` growing, `log X ≥ 3`, and the
Riemann hypothesis, the explicit constant `stripK` and exponent `1` feed
`perronShiftRemainder_of_RH_stripOffPole` with no strip hypothesis left. -/
theorem perronShiftRemainder_of_RH_stripBound {X : ℕ → ℝ} {c : ℝ}
    {Kper Kref Ktail : ℕ → ℝ}
    (hRH : RiemannZetaZerosOnLine)
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRef : ReferencePerronBound X c Kref 1)
    (hTail : VerticalTailBound X Ktail 1)
    (hKref : ∀ᶠ n : ℕ in atTop, 0 ≤ Kref n)
    (hKtail : ∀ᶠ n : ℕ in atTop, 0 ≤ Ktail n)
    (hK : ∀ᶠ n : ℕ in atTop,
      Kref n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n ≤ Kper n) :
    PerronShiftRemainder X c Kper 1 :=
  perronShiftRemainder_of_RH_stripOffPole hRH
    (stripZetaBoundOffPole_of_RH hX hU hRH) hX (fun _ => stripK_nonneg)
    hRef hTail hKref hKtail hK

/-- **The literal `StripZetaBound` from the Riemann hypothesis plus the
near-pole residual.**  This is the exact reduction to the statement of
`Cogentic.RandomizedL21_2Remainder.StripZetaBound`: everything except the
punctured neighbourhood of the pole `s = 1` is proved, and the near-pole part is
the explicit residual `StripZetaBoundNearPole`.  That residual is not derivable
(it contains the pole), but it is never used by the Perron contour. -/
theorem stripZetaBound_of_RH_and_nearPole {X : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine)
    (hnear : StripZetaBoundNearPole X (fun _ => stripK) 1) :
    StripZetaBound X (fun _ => stripK) 1 :=
  stripZetaBound_of_offPole_and_nearPole (stripZetaBoundOffPole_of_RH hX hU hRH) hnear

/-- **Composition through the original `perronShiftRemainder_of_RH_strip`.**
Once the near-pole residual `StripZetaBoundNearPole` is supplied, the literal
`StripZetaBound` is available and the original theorem applies verbatim.  The
pole-free theorem `perronShiftRemainder_of_RH_stripBound` is the same conclusion
without this residual. -/
theorem perronShiftRemainder_of_RH_strip_viaNearPole {X : ℕ → ℝ} {c : ℝ}
    {Kper Kref Ktail : ℕ → ℝ}
    (hRH : RiemannZetaZerosOnLine)
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hnear : StripZetaBoundNearPole X (fun _ => stripK) 1)
    (hRef : ReferencePerronBound X c Kref 1)
    (hTail : VerticalTailBound X Ktail 1)
    (hKref : ∀ᶠ n : ℕ in atTop, 0 ≤ Kref n)
    (hKtail : ∀ᶠ n : ℕ in atTop, 0 ≤ Ktail n)
    (hK : ∀ᶠ n : ℕ in atTop,
      Kref n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n ≤ Kper n) :
    PerronShiftRemainder X c Kper 1 :=
  perronShiftRemainder_of_RH_strip hRH
    (stripZetaBound_of_RH_and_nearPole hX hU hRH hnear)
    hX (fun _ => stripK_nonneg) hRef hTail hKref hKtail hK

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2StripBound.riemannZeta_ne_zero_of_RH_ge
#print axioms Cogentic.RandomizedL21_2StripBound.norm_logDeriv_le_of_leftStrip
#print axioms Cogentic.RandomizedL21_2StripBound.norm_logDeriv_le_mangoldtL2
#print axioms Cogentic.RandomizedL21_2StripBound.stripZetaBoundOffPole_of_RH
#print axioms Cogentic.RandomizedL21_2StripBound.contourRemainderBound_of_stripOffPole
#print axioms Cogentic.RandomizedL21_2StripBound.perronShiftRemainder_of_RH_stripOffPole
#print axioms Cogentic.RandomizedL21_2StripBound.perronShiftRemainder_of_RH_stripBound
#print axioms Cogentic.RandomizedL21_2StripBound.perronShiftRemainder_of_RH_strip_viaNearPole

end Cogentic.RandomizedL21_2StripBound
