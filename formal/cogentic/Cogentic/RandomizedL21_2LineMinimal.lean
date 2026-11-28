import Cogentic.RandomizedL21_2LineBound
import Cogentic.RandomizedPaperEndpointWave17

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-!
# L21.2: the minimal zeta-line input

`Cogentic.RandomizedL21_2LineBound` reduces the L21.2 Perron shift to a
uniform bound for `ζ'/ζ` on the segment `Re s = 2/3`, `|Im s| ≤ 2 X³`
(`VerticalLineBound`).  It also names two sufficient zeta-side inputs:

* `ZetaLineEstimate X b B`, the two-sided pointwise estimate
  `b n ≤ ‖ζ(2/3+iu)‖` and `‖ζ'(2/3+iu)‖ ≤ B n` on the segment;
* `ClassicalLogDerivLineBoundOn X`, the range-local classical
  `O (log²)` bound for `ζ'/ζ`.

This file records the smallest forms of those inputs and proves the exact
translation between them.

The genuinely arithmetic content of the line estimate is the non-vanishing of
`ζ` on `Re s = 2/3` in the height range.  We prove that this qualitative
statement is *exactly* equivalent to the existence of a positive lower bound
`b n ≤ ‖ζ(2/3+iu)‖`: one direction is immediate, the other is compactness of
the segment together with continuity of `ζ`.  Thus the quantitative lower
bound carries no extra content beyond zero-freeness.  The qualitative
statement is `ZetaLineZeroFree`; it is not known unconditionally, because the
classical zero-free region only gives `Re s > 1 - c / log |Im s|` and never
reaches `2/3`.  Under the Riemann hypothesis it is discharged
(`zetaLineZeroFree_of_RH`).

We then prove:

* `zetaLineEstimate_iff_twoSided`: `ZetaLineEstimate` is exactly the pair
  (lower bound, upper bound for `ζ'`);
* `classicalLogDerivLineBoundOn_iff_range`: `ClassicalLogDerivLineBoundOn` is
  exactly its range-local `O (log²)` form;
* `classicalLogDerivLineBoundOn_iff_ratio`: on a zero-free line, the classical
  bound is exactly the relative estimate
  `‖ζ'‖ ≤ C (log (|u|+2))² ‖ζ‖`;
* `zetaLineEstimate_of_ratio`: the relative estimate plus a lower bound gives
  `ZetaLineEstimate` at the explicit constant `zetaLineDerivConstant`, using
  the unconditional polynomial upper bound for `ζ`;
* positivity and monotonicity of `zetaLineDerivConstant`, `B / b`, and the line
  bound itself;
* `verticalLineBound_of_zetaLineEstimate_exponent` and
  `verticalLineBound_of_classicalLogDerivOn_exponent`: the two reductions to
  `VerticalLineBound` at the exponent `C - 1` used by the paper record;
* `wave17LineBound_of_zetaLineEstimate` and
  `wave17WithZetaLineEstimate`: the reduction into the Wave-17
  `lineBound` field, leaving every other field unchanged.

Everything is conditional only on the explicit zeta input.  There is no
`sorry`, `admit`, `axiom` or `native_decide`, and no bound is replaced by zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2LineMinimal

open Filter Real MeasureTheory Complex Metric
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2StripBound

/-! ## The minimal line predicates -/

/-- The upper bound for `ζ'` on the segment `Re s = 2/3`, `|Im s| ≤ 2 X³`.
Together with `ZetaLineLower` this is exactly `ZetaLineEstimate`. -/
def ZetaLineDerivUpper (X : ℕ → ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
    ‖deriv riemannZeta (perronLine perronRe u)‖ ≤ B n

/-- The qualitative form of the lower bound: `ζ` does not vanish on the segment
`Re s = 2/3`, `|Im s| ≤ 2 X³`.  This is the single genuinely open analytic
input of the line reduction: no unconditional zero-free region for `ζ` reaches
`Re s = 2/3`. -/
def ZetaLineZeroFree (X : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
    riemannZeta (perronLine perronRe u) ≠ 0

/-- The two-sided pointwise line estimate, split into its two halves. -/
def ZetaLineTwoSided (X : ℕ → ℝ) (b B : ℕ → ℝ) : Prop :=
  ZetaLineLower X b ∧ ZetaLineDerivUpper X B

/-- The relative classical line estimate: `ζ` does not vanish on the segment
and `‖ζ'‖ ≤ C (log (|u|+2))² ‖ζ‖`.  On a zero-free line this is exactly
`ClassicalLogDerivLineBoundOn`. -/
def ClassicalLineRatioBound (X : ℕ → ℝ) (C : ℝ) : Prop :=
  0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
    riemannZeta (perronLine perronRe u) ≠ 0 ∧
      ‖deriv riemannZeta (perronLine perronRe u)‖ ≤
        C * (Real.log (|u| + 2)) ^ 2 *
          ‖riemannZeta (perronLine perronRe u)‖

/-! ## Exact translations -/

/-- `ZetaLineEstimate` is exactly the conjunction of the lower bound and the
upper bound for `ζ'`. -/
theorem zetaLineEstimate_iff_twoSided {X : ℕ → ℝ} {b B : ℕ → ℝ} :
    ZetaLineEstimate X b B ↔ ZetaLineTwoSided X b B := by
  unfold ZetaLineEstimate ZetaLineTwoSided ZetaLineLower ZetaLineDerivUpper
  constructor
  · intro h
    exact ⟨h.mono fun n hn u hu => (hn u hu).1,
      h.mono fun n hn u hu => (hn u hu).2⟩
  · rintro ⟨hlo, hhi⟩
    filter_upwards [hlo, hhi] with n hnlo hnhi
    intro u hu
    exact ⟨hnlo u hu, hnhi u hu⟩

/-- `ClassicalLogDerivLineBoundOn` is exactly its range-local `O (log²)`
form. -/
theorem classicalLogDerivLineBoundOn_iff_range {X : ℕ → ℝ} :
    ClassicalLogDerivLineBoundOn X ↔
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
        ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤
          C * (Real.log (|u| + 2)) ^ 2 :=
  Iff.rfl

/-- On a zero-free line, the classical `O (log²)` bound is exactly the
relative estimate `‖ζ'‖ ≤ C (log (|u|+2))² ‖ζ‖`.  The zero-free hypothesis is
needed only to divide by `‖ζ‖`; without it the Lean division by zero would
make the two statements differ at the zeros. -/
theorem classicalLogDerivLineBoundOn_iff_ratio {X : ℕ → ℝ}
    (hz : ZetaLineZeroFree X) :
    ClassicalLogDerivLineBoundOn X ↔ ∃ C : ℝ, ClassicalLineRatioBound X C := by
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hC, hz] with n hn hzn
    intro u hu
    have hne : riemannZeta (perronLine perronRe u) ≠ 0 := hzn u hu
    refine ⟨hne, ?_⟩
    have hb := hn u hu
    rw [logDeriv_apply, norm_div] at hb
    have hpos : 0 < ‖riemannZeta (perronLine perronRe u)‖ :=
      norm_pos_iff.mpr hne
    exact (div_le_iff₀ hpos).mp hb
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hC] with n hn
    intro u hu
    obtain ⟨hne, hder⟩ := hn u hu
    rw [logDeriv_apply, norm_div]
    have hpos : 0 < ‖riemannZeta (perronLine perronRe u)‖ :=
      norm_pos_iff.mpr hne
    exact (div_le_iff₀ hpos).mpr hder

/-! ## The lower bound is exactly zero-freeness -/

/-- The line `u ↦ ζ(2/3 + iu)` is continuous. -/
lemma continuous_riemannZeta_perronLine :
    Continuous fun u : ℝ => riemannZeta (perronLine perronRe u) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hne : perronLine perronRe u ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [perronLine, perronRe] at hre
    norm_num at hre
  have hline : Continuous fun v : ℝ => perronLine perronRe v := by
    unfold perronLine
    fun_prop
  exact (differentiableAt_riemannZeta hne).continuousAt.comp hline.continuousAt

/-- A nonzero continuous function on the compact segment
`|u| ≤ 2 X³` has a positive lower bound.  If the segment is empty (when
`X n < 0`) any positive number works. -/
lemma exists_pos_lower_on_line {X : ℕ → ℝ} {n : ℕ}
    (hn : ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
      riemannZeta (perronLine perronRe u) ≠ 0) :
    ∃ b : ℝ, 0 < b ∧ ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
      b ≤ ‖riemannZeta (perronLine perronRe u)‖ := by
  by_cases hr : 0 ≤ 2 * X n ^ 3
  · have hKne : (Set.Icc (-(2 * X n ^ 3)) (2 * X n ^ 3)).Nonempty :=
      ⟨0, by constructor <;> linarith⟩
    obtain ⟨u0, hu0, hmin⟩ := isCompact_Icc.exists_isMinOn hKne
      (continuous_riemannZeta_perronLine.norm.continuousOn)
    have hu0' : |u0| ≤ 2 * X n ^ 3 := by
      simpa [Set.mem_Icc, abs_le] using hu0
    have hpos : 0 < ‖riemannZeta (perronLine perronRe u0)‖ :=
      norm_pos_iff.mpr (hn u0 hu0')
    refine ⟨_, hpos, ?_⟩
    intro u hu
    exact hmin (by simpa [Set.mem_Icc, abs_le] using hu)
  · have hr' : 2 * X n ^ 3 < 0 := lt_of_not_ge hr
    refine ⟨1, one_pos, ?_⟩
    intro u hu
    have hnn : 0 ≤ |u| := abs_nonneg u
    linarith

/-- **The quantitative lower bound is exactly zero-freeness.**  A positive
lower bound `b n ≤ ‖ζ(2/3+iu)‖` exists if and only if `ζ` is nonzero on the
segment.  This is the precise sense in which `ZetaLineZeroFree` is the whole
open input: no quantitative information is lost or hidden. -/
theorem zetaLineZeroFree_iff_exists_positive_lower (X : ℕ → ℝ) :
    ZetaLineZeroFree X ↔
      ∃ b : ℕ → ℝ, (∀ n, 0 < b n) ∧ ZetaLineLower X b := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
    have key : ∀ n : ℕ, N ≤ n →
        ∃ b : ℝ, 0 < b ∧ ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
          b ≤ ‖riemannZeta (perronLine perronRe u)‖ :=
      fun n hn => exists_pos_lower_on_line (hN n hn)
    refine ⟨fun n => if hn : N ≤ n then Classical.choose (key n hn) else 1, ?_, ?_⟩
    · intro n
      by_cases hn : N ≤ n
      · simp only [dif_pos hn]
        exact (Classical.choose_spec (key n hn)).1
      · simp only [dif_neg hn]
        norm_num
    · unfold ZetaLineLower
      rw [Filter.eventually_atTop]
      refine ⟨N, ?_⟩
      intro n hn
      simp only [dif_pos hn]
      exact (Classical.choose_spec (key n hn)).2
  · rintro ⟨b, hb, hlow⟩
    filter_upwards [hlow] with n hn
    intro u hu hzero
    have hb_le := hn u hu
    rw [hzero, norm_zero] at hb_le
    exact (not_lt_of_ge hb_le) (hb n)

/-- Under the Riemann hypothesis the open line input is discharged: a zero on
`Re s = 2/3` would be a zero with real part `1/2`. -/
theorem zetaLineZeroFree_of_RH {X : ℕ → ℝ} (hRH : RiemannZetaZerosOnLine) :
    ZetaLineZeroFree X := by
  refine Filter.Eventually.of_forall ?_
  intro n u hu
  refine riemannZeta_ne_zero_of_RH_ge hRH (s := perronLine perronRe u) ?_ ?_
  · simp [perronLine]
  · intro h
    have hre := congrArg Complex.re h
    simp [perronLine, perronRe] at hre
    norm_num at hre

/-- The precise failure mode of the open input: if `ZetaLineZeroFree X` fails,
then for infinitely many `n` there is an actual zero of `ζ` on
`Re s = 2/3` inside the segment `|Im s| ≤ 2 X n³`.  This is the statement that
is not excluded unconditionally. -/
theorem not_zetaLineZeroFree_iff_frequently_zero (X : ℕ → ℝ) :
    ¬ ZetaLineZeroFree X ↔
      ∃ᶠ n : ℕ in atTop, ∃ u : ℝ,
        |u| ≤ 2 * X n ^ 3 ∧ riemannZeta (perronLine perronRe u) = 0 := by
  unfold ZetaLineZeroFree
  rw [Filter.not_eventually]
  apply Filter.frequently_congr
  exact Filter.Eventually.of_forall fun n => by
    constructor
    · intro h
      push Not at h
      exact h
    · rintro ⟨u, hu, hz⟩ hc
      exact hc u hu hz

/-! ## The explicit derivative constant -/

/-- The uniform upper bound for `ζ'` obtained from the relative classical
bound and the unconditional polynomial upper bound for `ζ` in the strip. -/
noncomputable def zetaLineDerivConstant (X : ℕ → ℝ) (C : ℝ) (n : ℕ) : ℝ :=
  C * (4 * bandLog X n) ^ 2 *
    (Classical.choose exists_zeta_upper_bound_strip * X n ^ 15)

/-- The explicit derivative constant is strictly positive whenever `C > 0`. -/
theorem zetaLineDerivConstant_pos {X : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (n : ℕ) :
    0 < zetaLineDerivConstant X C n := by
  unfold zetaLineDerivConstant
  have hL0 : 0 < bandLog X n := by linarith [hU n]
  have h4L : 0 < 4 * bandLog X n := by linarith
  have hsq : 0 < (4 * bandLog X n) ^ 2 := pow_pos h4L 2
  have hX0 : 0 < X n := lt_trans zero_lt_one (hX n)
  have hX15 : 0 < X n ^ 15 := pow_pos hX0 15
  exact mul_pos (mul_pos hC hsq) (mul_pos zetaUpperConstant_pos hX15)

/-- `zetaLineDerivConstant` is monotone in the relative constant `C`. -/
theorem zetaLineDerivConstant_mono {X : ℕ → ℝ} {C C' : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hCC' : C ≤ C') (n : ℕ) :
    zetaLineDerivConstant X C n ≤ zetaLineDerivConstant X C' n := by
  unfold zetaLineDerivConstant
  have hL0 : 0 ≤ 4 * bandLog X n := by linarith [hU n]
  have hsq : 0 ≤ (4 * bandLog X n) ^ 2 := sq_nonneg _
  have hCup : 0 ≤ Classical.choose exists_zeta_upper_bound_strip :=
    zetaUpperConstant_pos.le
  have hX15 : 0 ≤ X n ^ 15 := pow_nonneg (le_of_lt (lt_trans zero_lt_one (hX n))) 15
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC' hsq) (mul_nonneg hCup hX15)

/-- The upper bound for `ζ'` from the relative classical estimate: use the
unconditional strip bound for `ζ` and `log (|u|+2) ≤ 4 log X`. -/
theorem zetaLineDerivUpper_of_ratio {X : ℕ → ℝ} {C : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (h : ClassicalLineRatioBound X C) :
    ZetaLineDerivUpper X (zetaLineDerivConstant X C) := by
  have hC0 : 0 < C := h.1
  have hspec := Classical.choose_spec exists_zeta_upper_bound_strip
  filter_upwards [h.2] with n hn
  intro u hu
  obtain ⟨_hne, hder⟩ := hn u hu
  have hX1 : 1 ≤ X n := (hX n).le
  have hX3 : 0 ≤ X n ^ 3 := pow_nonneg (le_of_lt (lt_trans zero_lt_one (hX n))) 3
  have hu3 : |u| ≤ 3 * X n ^ 3 := by
    have h23 : 2 * X n ^ 3 ≤ 3 * X n ^ 3 := by nlinarith
    linarith
  have hzupper : ‖riemannZeta (perronLine perronRe u)‖ ≤
      Classical.choose exists_zeta_upper_bound_strip * X n ^ 15 := by
    exact hspec.2 (X n) u (perronLine perronRe u) hX1 hu (by
      rw [sub_self, norm_zero]
      norm_num)
  have hlog : Real.log (|u| + 2) ≤ 4 * bandLog X n :=
    log_abs_add_two_le_four_bandLog (hX n) (hU n) hu3
  have hlog0 : 0 ≤ Real.log (|u| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg u]
  have hlog2 : (Real.log (|u| + 2)) ^ 2 ≤ (4 * bandLog X n) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  have hfirst : C * (Real.log (|u| + 2)) ^ 2 ≤ C * (4 * bandLog X n) ^ 2 :=
    mul_le_mul_of_nonneg_left hlog2 hC0.le
  calc
    ‖deriv riemannZeta (perronLine perronRe u)‖
        ≤ C * (Real.log (|u| + 2)) ^ 2 *
            ‖riemannZeta (perronLine perronRe u)‖ := hder
    _ = (C * (Real.log (|u| + 2)) ^ 2) *
          ‖riemannZeta (perronLine perronRe u)‖ := rfl
    _ ≤ (C * (4 * bandLog X n) ^ 2) *
          ‖riemannZeta (perronLine perronRe u)‖ :=
        mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
    _ ≤ (C * (4 * bandLog X n) ^ 2) *
          (Classical.choose exists_zeta_upper_bound_strip * X n ^ 15) :=
        mul_le_mul_of_nonneg_left hzupper
          (mul_nonneg hC0.le (sq_nonneg _))
    _ = zetaLineDerivConstant X C n := by
        unfold zetaLineDerivConstant
        ring

/-- From a positive lower bound and the relative classical estimate, the full
two-sided line estimate follows at the explicit derivative constant. -/
theorem zetaLineEstimate_of_ratio {X : ℕ → ℝ} {b : ℕ → ℝ} {C : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hlow : ZetaLineLower X b) (h : ClassicalLineRatioBound X C) :
    ZetaLineEstimate X b (zetaLineDerivConstant X C) :=
  zetaLineEstimate_iff_twoSided.mpr
    ⟨hlow, zetaLineDerivUpper_of_ratio hX hU h⟩

/-- The exact bridge from the range-local classical bound to the two-sided
estimate, given the zero-free line and a lower bound. -/
theorem exists_zetaLineEstimate_of_classicalLogDeriv {X : ℕ → ℝ} {b : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hz : ZetaLineZeroFree X) (hlow : ZetaLineLower X b)
    (h : ClassicalLogDerivLineBoundOn X) :
    ∃ C : ℝ, ClassicalLineRatioBound X C ∧
      ZetaLineEstimate X b (zetaLineDerivConstant X C) := by
  obtain ⟨C, hC⟩ := (classicalLogDerivLineBoundOn_iff_ratio hz).mp h
  exact ⟨C, hC, zetaLineEstimate_of_ratio hX hU hlow hC⟩

/-- **Capstone: under RH the classical range-local bound supplies the whole
two-sided line estimate.**  Zero-freeness produces a positive lower bound `b`
by compactness, and the explicit `zetaLineDerivConstant` produces `B`. -/
theorem exists_zetaLineEstimate_of_RH {X : ℕ → ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine) (h : ClassicalLogDerivLineBoundOn X) :
    ∃ b B : ℕ → ℝ, (∀ n, 0 < b n) ∧ ZetaLineEstimate X b B := by
  have hz : ZetaLineZeroFree X := zetaLineZeroFree_of_RH hRH
  obtain ⟨b, hb, hlow⟩ := (zetaLineZeroFree_iff_exists_positive_lower X).mp hz
  obtain ⟨C, _hC, hEst⟩ :=
    exists_zetaLineEstimate_of_classicalLogDeriv hX hU hz hlow h
  exact ⟨b, zetaLineDerivConstant X C, hb, hEst⟩

/-! ## Positivity and monotonicity of the constants -/

/-- Monotonicity of the lower bound in the sequence `b`. -/
theorem zetaLineLower_mono {X : ℕ → ℝ} {b b' : ℕ → ℝ}
    (hle : ∀ᶠ n : ℕ in atTop, b' n ≤ b n) (h : ZetaLineLower X b) :
    ZetaLineLower X b' := by
  filter_upwards [h, hle] with n hn hnn
  intro u hu
  exact hnn.trans (hn u hu)

/-- Monotonicity of the derivative upper bound in the sequence `B`. -/
theorem zetaLineDerivUpper_mono {X : ℕ → ℝ} {B B' : ℕ → ℝ}
    (hle : ∀ᶠ n : ℕ in atTop, B n ≤ B' n) (h : ZetaLineDerivUpper X B) :
    ZetaLineDerivUpper X B' := by
  filter_upwards [h, hle] with n hn hnn
  intro u hu
  exact (hn u hu).trans hnn

/-- Monotonicity of the two-sided estimate: lowering `b` and raising `B`
preserves the estimate. -/
theorem zetaLineTwoSided_mono {X : ℕ → ℝ} {b b' B B' : ℕ → ℝ}
    (hb : ∀ᶠ n : ℕ in atTop, b' n ≤ b n)
    (hB : ∀ᶠ n : ℕ in atTop, B n ≤ B' n)
    (h : ZetaLineTwoSided X b B) :
    ZetaLineTwoSided X b' B' :=
  ⟨zetaLineLower_mono hb h.1, zetaLineDerivUpper_mono hB h.2⟩

/-- Monotonicity of `ZetaLineEstimate`. -/
theorem zetaLineEstimate_mono {X : ℕ → ℝ} {b b' B B' : ℕ → ℝ}
    (hb : ∀ᶠ n : ℕ in atTop, b' n ≤ b n)
    (hB : ∀ᶠ n : ℕ in atTop, B n ≤ B' n)
    (h : ZetaLineEstimate X b B) :
    ZetaLineEstimate X b' B' :=
  zetaLineEstimate_iff_twoSided.mpr
    (zetaLineTwoSided_mono hb hB (zetaLineEstimate_iff_twoSided.mp h))

/-- Monotonicity of the relative classical bound in its constant. -/
theorem classicalLineRatioBound_mono {X : ℕ → ℝ} {C C' : ℝ}
    (hCC' : C ≤ C') (hC' : 0 < C') (h : ClassicalLineRatioBound X C) :
    ClassicalLineRatioBound X C' := by
  refine ⟨hC', ?_⟩
  filter_upwards [h.2] with n hn
  intro u hu
  obtain ⟨hne, hder⟩ := hn u hu
  refine ⟨hne, ?_⟩
  have hlog : 0 ≤ (Real.log (|u| + 2)) ^ 2 := sq_nonneg _
  have hnorm : 0 ≤ ‖riemannZeta (perronLine perronRe u)‖ := norm_nonneg _
  calc
    ‖deriv riemannZeta (perronLine perronRe u)‖
        ≤ C * (Real.log (|u| + 2)) ^ 2 *
            ‖riemannZeta (perronLine perronRe u)‖ := hder
    _ = C * ((Real.log (|u| + 2)) ^ 2 *
          ‖riemannZeta (perronLine perronRe u)‖) := by ring
    _ ≤ C' * ((Real.log (|u| + 2)) ^ 2 *
          ‖riemannZeta (perronLine perronRe u)‖) :=
        mul_le_mul_of_nonneg_right hCC' (mul_nonneg hlog hnorm)
    _ = C' * (Real.log (|u| + 2)) ^ 2 *
          ‖riemannZeta (perronLine perronRe u)‖ := by ring

/-- The quotient `B / b` is positive when both sequences are positive. -/
theorem derivRatio_pos {b B : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    (hB : ∀ n, 0 < B n) (n : ℕ) : 0 < B n / b n :=
  div_pos (hB n) (hb n)

/-- The quotient `B / b` is monotone when `B` grows and the lower bound `b`
shrinks.  This is the monotonicity of the line constant `B / b` produced by
`verticalLineBound_of_zetaLineEstimate`. -/
theorem derivRatio_mono {b b' B B' : ℝ} (hb : 0 < b) (hb' : 0 < b')
    (hbb : b' ≤ b) (hB0 : 0 ≤ B) (hB : B ≤ B') :
    B / b ≤ B' / b' := by
  have h1 : B / b ≤ B' / b := div_le_div_of_nonneg_right hB hb.le
  have h2 : B' / b ≤ B' / b' :=
    div_le_div_of_nonneg_left (le_trans hB0 hB) hb' hbb
  exact h1.trans h2

/-! ## Reductions to `VerticalLineBound` -/

/-- **The two-sided line estimate gives `VerticalLineBound` at exponent
`C - 1`.**  The exponent `2` of `verticalLineBound_of_zetaLineEstimate` is
raised to the paper's `C - 1` using `log X ≥ 3`. -/
theorem verticalLineBound_of_zetaLineEstimate_exponent
    {X : ℕ → ℝ} {b B : ℕ → ℝ} {C : ℝ}
    (_hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hC : 3 ≤ C)
    (hb : ∀ n, 0 < b n) (hB : ∀ n, 0 ≤ B n)
    (h : ZetaLineEstimate X b B) :
    VerticalLineBound X (fun n => B n / b n) (C - 1) := by
  have hU1 : ∀ n, 1 ≤ bandLog X n := fun n => by linarith [hU n]
  have hbase : VerticalLineBound X (fun n => B n / b n) 2 :=
    verticalLineBound_of_zetaLineEstimate hU1 hb hB h
  unfold VerticalLineBound at hbase ⊢
  filter_upwards [hbase] with n hn
  intro u hu
  have hexp : (bandLog X n) ^ (2 : ℝ) ≤ (bandLog X n) ^ (C - 1) :=
    Real.rpow_le_rpow_of_exponent_le (hU1 n) (by linarith)
  calc
    ‖logDeriv riemannZeta (perronLine perronRe u)‖
        ≤ (B n / b n) * (bandLog X n) ^ (2 : ℝ) := hn u hu
    _ ≤ (B n / b n) * (bandLog X n) ^ (C - 1) :=
        mul_le_mul_of_nonneg_left hexp (div_nonneg (hB n) (hb n).le)

/-- **The range-local classical `O (log²)` bound gives `VerticalLineBound` at
the paper's exponent `C - 1`.**  The constant produced by
`verticalLineBound_of_classicalLogDerivOn` is positive. -/
theorem verticalLineBound_of_classicalLogDerivOn_exponent
    {X : ℕ → ℝ} {C : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hC : 3 ≤ C)
    (h : ClassicalLogDerivLineBoundOn X) :
    ∃ K : ℝ, 0 < K ∧ VerticalLineBound X (fun _ => K) (C - 1) := by
  obtain ⟨K, hK0, hK⟩ := verticalLineBound_of_classicalLogDerivOn hX hU h
  refine ⟨K, hK0, ?_⟩
  unfold VerticalLineBound at hK ⊢
  filter_upwards [hK] with n hn
  intro u hu
  have hL1 : 1 ≤ bandLog X n := by linarith [hU n]
  have hexp : (bandLog X n) ^ (2 : ℝ) ≤ (bandLog X n) ^ (C - 1) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  calc
    ‖logDeriv riemannZeta (perronLine perronRe u)‖
        ≤ K * (bandLog X n) ^ (2 : ℝ) := hn u hu
    _ ≤ K * (bandLog X n) ^ (C - 1) :=
        mul_le_mul_of_nonneg_left hexp hK0.le

/-! ## The Wave-17 `lineBound` field -/

/-- **The `lineBound` field of `Wave17L21_2Inputs` from the two-sided line
estimate.**  The only remaining side condition is that the quotient `B / b`
dominates the raw wave-17 constant.  All other fields of the record are
untouched. -/
theorem wave17LineBound_of_zetaLineEstimate
    (D : Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs)
    {b B : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hB : ∀ n, 0 ≤ B n)
    (h : ZetaLineEstimate D.profile.X b B)
    (hK : ∀ᶠ n : ℕ in atTop, B n / b n ≤ D.KlineRaw) :
    VerticalLineBound D.profile.X (fun _ => D.KlineRaw) (D.Cper - 1) := by
  have hVB := verticalLineBound_of_zetaLineEstimate_exponent
    (X := D.profile.X) (b := b) (B := B) (C := D.Cper)
    D.X_gt_one D.U_ge_three D.Cper_ge_three hb hB h
  exact Cogentic.RandomizedPaperEndpointWave17.verticalLineBound_mono
    D.X_gt_one hVB hK

/-- The constant-sequence form of `wave17LineBound_of_zetaLineEstimate`. -/
theorem wave17LineBound_of_constant_zetaLineEstimate
    (D : Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs)
    {b B : ℝ} (hb : 0 < b) (hB : 0 ≤ B)
    (h : ZetaLineEstimate D.profile.X (fun _ => b) (fun _ => B))
    (hK : B / b ≤ D.KlineRaw) :
    VerticalLineBound D.profile.X (fun _ => D.KlineRaw) (D.Cper - 1) :=
  wave17LineBound_of_zetaLineEstimate D (fun _ => hb) (fun _ => hB) h
    (Filter.Eventually.of_forall fun _ => hK)

/-- The range-local classical bound gives the wave-17 `lineBound` field at a
derived positive constant.  If that constant is below `KlineRaw`, monotonicity
of `VerticalLineBound` (or `verticalLineBound_mono`) passes to the literal
field. -/
theorem wave17LineBound_of_classicalLogDerivOn
    (D : Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs)
    (h : ClassicalLogDerivLineBoundOn D.profile.X) :
    ∃ K : ℝ, 0 < K ∧
      VerticalLineBound D.profile.X (fun _ => K) (D.Cper - 1) :=
  verticalLineBound_of_classicalLogDerivOn_exponent
    D.X_gt_one D.U_ge_three D.Cper_ge_three h

/-- Replace only the `lineBound` field of a wave-17 record by the bound
produced from the two-sided line estimate. -/
noncomputable def wave17WithZetaLineEstimate
    (D : Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs)
    (b B : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hB : ∀ n, 0 ≤ B n)
    (h : ZetaLineEstimate D.profile.X b B)
    (hK : ∀ᶠ n : ℕ in atTop, B n / b n ≤ D.KlineRaw) :
    Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs :=
  { D with
    lineBound := wave17LineBound_of_zetaLineEstimate D hb hB h hK }

/-- The `lineBound` field of the replaced record is exactly the minimal
reduction. -/
theorem wave17WithZetaLineEstimate_lineBound
    (D : Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs)
    {b B : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hB : ∀ n, 0 ≤ B n)
    (h : ZetaLineEstimate D.profile.X b B)
    (hK : ∀ᶠ n : ℕ in atTop, B n / b n ≤ D.KlineRaw) :
    (wave17WithZetaLineEstimate D b B hb hB h hK).lineBound =
      wave17LineBound_of_zetaLineEstimate D hb hB h hK :=
  rfl

/-- Replacing the `lineBound` field changes no other data. -/
theorem wave17WithZetaLineEstimate_data
    (D : Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs)
    {b B : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hB : ∀ n, 0 ≤ B n)
    (h : ZetaLineEstimate D.profile.X b B)
    (hK : ∀ᶠ n : ℕ in atTop, B n / b n ≤ D.KlineRaw) :
    (wave17WithZetaLineEstimate D b B hb hB h hK).profile = D.profile ∧
      (wave17WithZetaLineEstimate D b B hb hB h hK).c = D.c ∧
      (wave17WithZetaLineEstimate D b B hb hB h hK).Cper = D.Cper ∧
      (wave17WithZetaLineEstimate D b B hb hB h hK).KlineRaw = D.KlineRaw :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The derived wave-17 constant is unchanged by the replacement. -/
theorem wave17WithZetaLineEstimate_Kline
    (D : Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs)
    {b B : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hB : ∀ n, 0 ≤ B n)
    (h : ZetaLineEstimate D.profile.X b B)
    (hK : ∀ᶠ n : ℕ in atTop, B n / b n ≤ D.KlineRaw) :
    (wave17WithZetaLineEstimate D b B hb hB h hK).Kline = D.Kline :=
  rfl

/-- The derived constant of the replaced record also supplies the `lineBound`
at the record's own `Kline`, by `lineBound_derived`. -/
theorem wave17WithZetaLineEstimate_lineBound_derived
    (D : Cogentic.RandomizedPaperEndpointWave17.Wave17L21_2Inputs)
    {b B : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hB : ∀ n, 0 ≤ B n)
    (h : ZetaLineEstimate D.profile.X b B)
    (hK : ∀ᶠ n : ℕ in atTop, B n / b n ≤ D.KlineRaw) :
    VerticalLineBound D.profile.X
      (fun _ => (wave17WithZetaLineEstimate D b B hb hB h hK).Kline)
      (D.Cper - 1) :=
  (wave17WithZetaLineEstimate D b B hb hB h hK).lineBound_derived

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2LineMinimal.zetaLineEstimate_iff_twoSided
#print axioms Cogentic.RandomizedL21_2LineMinimal.classicalLogDerivLineBoundOn_iff_range
#print axioms Cogentic.RandomizedL21_2LineMinimal.classicalLogDerivLineBoundOn_iff_ratio
#print axioms Cogentic.RandomizedL21_2LineMinimal.zetaLineZeroFree_iff_exists_positive_lower
#print axioms Cogentic.RandomizedL21_2LineMinimal.zetaLineZeroFree_of_RH
#print axioms Cogentic.RandomizedL21_2LineMinimal.not_zetaLineZeroFree_iff_frequently_zero
#print axioms Cogentic.RandomizedL21_2LineMinimal.zetaLineDerivUpper_of_ratio
#print axioms Cogentic.RandomizedL21_2LineMinimal.zetaLineEstimate_of_ratio
#print axioms Cogentic.RandomizedL21_2LineMinimal.exists_zetaLineEstimate_of_classicalLogDeriv
#print axioms Cogentic.RandomizedL21_2LineMinimal.exists_zetaLineEstimate_of_RH
#print axioms Cogentic.RandomizedL21_2LineMinimal.zetaLineEstimate_mono
#print axioms Cogentic.RandomizedL21_2LineMinimal.derivRatio_mono
#print axioms Cogentic.RandomizedL21_2LineMinimal.verticalLineBound_of_zetaLineEstimate_exponent
#print axioms Cogentic.RandomizedL21_2LineMinimal.verticalLineBound_of_classicalLogDerivOn_exponent
#print axioms Cogentic.RandomizedL21_2LineMinimal.wave17LineBound_of_zetaLineEstimate
#print axioms Cogentic.RandomizedL21_2LineMinimal.wave17LineBound_of_constant_zetaLineEstimate
#print axioms Cogentic.RandomizedL21_2LineMinimal.wave17WithZetaLineEstimate
#print axioms Cogentic.RandomizedL21_2LineMinimal.wave17WithZetaLineEstimate_lineBound_derived

end Cogentic.RandomizedL21_2LineMinimal

#check Cogentic.RandomizedL21_2LineMinimal.ZetaLineDerivUpper
#check Cogentic.RandomizedL21_2LineMinimal.ZetaLineZeroFree
#check Cogentic.RandomizedL21_2LineMinimal.ZetaLineTwoSided
#check Cogentic.RandomizedL21_2LineMinimal.ClassicalLineRatioBound
#check Cogentic.RandomizedL21_2LineMinimal.zetaLineZeroFree_iff_exists_positive_lower
#check Cogentic.RandomizedL21_2LineMinimal.not_zetaLineZeroFree_iff_frequently_zero
#check Cogentic.RandomizedL21_2LineMinimal.exists_zetaLineEstimate_of_RH
#check Cogentic.RandomizedL21_2LineMinimal.verticalLineBound_of_zetaLineEstimate_exponent
#check Cogentic.RandomizedL21_2LineMinimal.verticalLineBound_of_classicalLogDerivOn_exponent
#check Cogentic.RandomizedL21_2LineMinimal.wave17LineBound_of_zetaLineEstimate
#check Cogentic.RandomizedL21_2LineMinimal.wave17WithZetaLineEstimate
