import Cogentic.RandomizedL30Relative

/-!
# L30: the paper-regime short-interval density

`Cogentic/RandomizedL30Relative.lean` isolates the single counting statement

`YounisOddIntervalDensity a p t err :  ∀ n, a * |centralOrderInterval p n| ≤ centralOddSmoothCount p t err n`

and reduces the relative short-interval density to it using only the
unconditional parity bound on the global odd smooth count.  Its concrete
witness uses the very large cutoff `Y = p³`, for which *every* integer below
`p²` is smooth.

This file does the paper-regime bookkeeping.  The paper's parameters are

* `t_p = √(log p · log log p)`, the scale of
  `YounisShortIntervalEstimate`;
* `Y_n = exp ((1 + ε_n) t_{p_n})`, the cutoff `smoothCutoff` with `t = t_p`.

The placeholders are `paperT` and `paperSmoothCutoff`; `PaperRegime p t err`
records `t = paperT p` and `0 ≤ ε`.

Three reductions are proved.

## 1. The smallest explicit fixed-density count

The interval `(p² - p^{3/2}/2, p²]` contains at most `p^{3/2}` integers
(`centralOrderInterval_card_le_three_halves`).  Hence the fixed-density
statement is equivalent, up to the forced factor `4`, to the explicit count

`YounisOddShortIntervalCount c p t err :  ∀ n, c * p_n^{3/2} ≤ centralOddSmoothCount p t err n`.

Both directions are proved:
`intervalDensity_of_shortIntervalCount` and
`shortIntervalCount_of_intervalDensity` (the latter loses exactly the factor
`4` supplied by `centralOrderInterval_card_ge_quarter`).  Specialising to
`t = paperT p` gives the paper-regime versions.

## 2. The Younis-normalised paper count

At the paper cutoff the fixed-density statement is the wrong scale: the global
density `Ψ_odd(p², Y)/p²` is of order `exp (-(1+ε)t_p) → 0`, so a positive
proportion of `p^{3/2}` smooth orders in the interval is far stronger than the
paper's theorem and does not follow from it.  The faithful paper-scale statement
therefore carries the density factor:

`YounisOddPaperShortCount c p t err :  ∀ n, c * p_n^{3/2} * exp (-(1+ε_n)t_n) ≤ centralOddSmoothCount p t err n`.

This is the paper's `p^{3/2} exp (-(1+ε)t_p)` count.  The relative short-interval
density follows from it together with an *upper* bound on the global odd density
of the same shape (`GlobalOddUpperDensity C`), with `A * C ≤ c`
(`paperRelative_of_globalUpper`).  The parity bound
`globalOddSmoothCount ≤ p²/4 + 1/2` gives such an upper bound with `C = 3/8`
whenever `(1+ε)t ≤ 0` (`globalOddUpperDensity_of_parity`), and hence the
paper-regime relative density from the paper count in that corner
(`paperRelative_of_parity`).  Composing with the global odd lower bound
reproduces `YounisOddCentralCount` (`paperCentralCount_of_globalUpper`).

## 3. The witness construction at a general cutoff

The witness set `{p_n² - (4j+2) : j < 8^{n+3}}` only uses that every element is
at most `p_n²`, so it is smooth for *any* cutoff dominating `p_n³`.  We prove
the monotonicity of `centralSmoothOrders` in the cutoff and transfer the
witness density to every pair `(t, err)` with
`exp ((1+ε_n)t_n) ≥ p_n³` (`witnessIntervalDensity_of_cutoff`,
`paperWitnessIntervalDensity`).  This is the large-cutoff corner of the
`Y = exp ((1+ε)t)` family.

For orientation we also record that the actual paper scale is on the other
side: for `p ≥ e`, `t_p ≤ 3 log p`, so `exp (t_p) ≤ p³`
(`paperT_le_three_log`, `paperSmoothCutoff_zero_le_cube`).  The witness
construction therefore cannot certify the paper cutoff, and the paper-scale
density is exactly the count input isolated in §1-§2.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count or error
is set to zero.
-/

namespace Cogentic.RandomizedL30Interval

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Relative

noncomputable section

/-! ## The paper's scale and cutoff -/

/-- The paper's `t_p = √(log p · log log p)`. -/
def paperT (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (p n) * Real.log (Real.log (p n)))

/-- The paper's cutoff `Y_n = exp ((1 + ε_n) t_{p_n})`. -/
def paperSmoothCutoff (p err : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp ((1 + err n) * paperT p n)

/-- `paperSmoothCutoff` is `smoothCutoff` at the paper scale. -/
theorem paperSmoothCutoff_eq_smoothCutoff (p err : ℕ → ℝ) :
    paperSmoothCutoff p err = smoothCutoff (paperT p) err := rfl

/-- **The paper regime.**  The scale is `t_p`, the relative error is
nonnegative, and the cutoff is consequently `exp ((1+ε)t_p)`. -/
def PaperRegime (p t err : ℕ → ℝ) : Prop :=
  t = paperT p ∧ ∀ n, 0 ≤ err n

theorem PaperRegime.t_eq {p t err : ℕ → ℝ} (h : PaperRegime p t err) :
    t = paperT p := h.1

theorem PaperRegime.err_nonneg {p t err : ℕ → ℝ} (h : PaperRegime p t err) :
    ∀ n, 0 ≤ err n := h.2

/-- The paper regime holds for the paper scale itself. -/
theorem paperRegime_self {p err : ℕ → ℝ} (herr : ∀ n, 0 ≤ err n) :
    PaperRegime p (paperT p) err :=
  ⟨rfl, herr⟩

/-- In the paper regime the cutoff is literally `paperSmoothCutoff`. -/
theorem PaperRegime.smoothCutoff_eq {p t err : ℕ → ℝ}
    (h : PaperRegime p t err) :
    smoothCutoff t err = paperSmoothCutoff p err := by
  rw [h.t_eq]
  rfl

/-- Transfer an interval-density statement from `t_p` to any paper-regime scale. -/
theorem intervalDensity_of_paperRegime {a : ℝ} {p t err : ℕ → ℝ}
    (h : PaperRegime p t err)
    (hd : YounisOddIntervalDensity a p (paperT p) err) :
    YounisOddIntervalDensity a p t err := by
  rw [h.t_eq]
  exact hd

/-- Transfer a relative-density statement from `t_p` to any paper-regime scale. -/
theorem relativeShortInterval_of_paperRegime {A : ℝ} {p t err : ℕ → ℝ}
    (h : PaperRegime p t err)
    (hd : YounisOddRelativeShortInterval A p (paperT p) err) :
    YounisOddRelativeShortInterval A p t err := by
  rw [h.t_eq]
  exact hd

/-! ## Interval cardinality at the paper scale -/

/-- The central interval `(p² - p^{3/2}/2, p²]` contains at most
`p^{3/2}/2 + 1` integers.  The rounding of both endpoints costs at most one. -/
theorem centralOrderInterval_card_le_half_add_one {p : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) :
    ((centralOrderInterval p n).card : ℝ) ≤ p n ^ ((3 : ℝ) / 2) / 2 + 1 := by
  let L : ℝ := p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2
  let a : ℕ := ⌈L⌉₊
  let b : ℕ := ⌊p n ^ 2⌋₊
  have hL1 : (1 : ℝ) ≤ L := one_le_central_lower hp
  have hp_pos : (0 : ℝ) < p n := by linarith
  by_cases hab : a ≤ b + 1
  · have hc : (centralOrderInterval p n).card = b + 1 - a := by
      dsimp only [centralOrderInterval, a, b]
      rw [Nat.card_Icc]
    have hcard : ((centralOrderInterval p n).card : ℝ) =
        (b : ℝ) + 1 - (a : ℝ) := by
      rw [hc, Nat.cast_sub hab]
      push_cast
      ring
    have ha_ge : L ≤ (a : ℝ) := Nat.le_ceil L
    have hb_le : (b : ℝ) ≤ p n ^ 2 := by
      dsimp only [b]
      exact Nat.floor_le (by positivity)
    rw [hcard]
    dsimp only [L] at ha_ge
    linarith
  · have hempty : centralOrderInterval p n = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      obtain ⟨m, hm⟩ := hne
      have hhab : b + 1 < a := by omega
      rw [centralOrderInterval, Finset.mem_Icc] at hm
      have hma : a ≤ m := hm.1
      have hmb : m ≤ b := hm.2
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hpow : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hp_pos.le _
    linarith

/-- The central interval contains at most `p^{3/2}` integers for `p ≥ 2`. -/
theorem centralOrderInterval_card_le_three_halves {p : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) :
    ((centralOrderInterval p n).card : ℝ) ≤ p n ^ ((3 : ℝ) / 2) := by
  have hhalf := centralOrderInterval_card_le_half_add_one hp
  have hone : (1 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) / 2 := by
    have hmono : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hbase : (2 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) := hmono
        _ ≤ p n ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow (by norm_num) hp (by norm_num)
    linarith
  linarith

/-! ## The smallest explicit fixed-density count -/

/-- **The smallest explicit short-interval count.**  The central interval
contains at least `c p^{3/2}` odd smooth orders.  Compared with
`YounisOddIntervalDensity` this replaces the interval cardinality by the
explicit scale `p^{3/2}`, which is the form in which the paper states the
Younis count. -/
def YounisOddShortIntervalCount (c : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, c * p n ^ ((3 : ℝ) / 2) ≤ centralOddSmoothCount p t err n

/-- **From the explicit count to the interval density.**  Since the interval
has at most `p^{3/2}` integers, `c p^{3/2}` odd smooth orders give density
`c` on the whole interval. -/
theorem intervalDensity_of_shortIntervalCount {a : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddShortIntervalCount a p t err) :
    YounisOddIntervalDensity a p t err := by
  intro n
  have hK := centralOrderInterval_card_le_three_halves (hp n)
  have hKnon : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  by_cases ha : 0 ≤ a
  · exact (mul_le_mul_of_nonneg_left hK ha).trans (h n)
  · have ha' : a < 0 := lt_of_not_ge ha
    have hleft : a * ((centralOrderInterval p n).card : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha'.le hKnon
    have hright : (0 : ℝ) ≤ centralOddSmoothCount p t err n := by
      unfold centralOddSmoothCount
      positivity
    exact hleft.trans hright

/-- **From the interval density to the explicit count.**  The interval has at
least `p^{3/2}/4` integers, so density `a` gives the explicit count with the
forced constant `a/4`. -/
theorem shortIntervalCount_of_intervalDensity {a : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddIntervalDensity a p t err) :
    YounisOddShortIntervalCount (a / 4) p t err := by
  intro n
  have hlow := centralOrderInterval_card_ge_quarter (hp n)
  have hcount_non : (0 : ℝ) ≤ centralOddSmoothCount p t err n := by
    unfold centralOddSmoothCount
    positivity
  by_cases ha : 0 ≤ a
  · have hmul : (a / 4) * p n ^ ((3 : ℝ) / 2) ≤
        a * ((centralOrderInterval p n).card : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlow ha
      calc (a / 4) * p n ^ ((3 : ℝ) / 2)
          = a * (p n ^ ((3 : ℝ) / 2) / 4) := by ring
        _ ≤ a * ((centralOrderInterval p n).card : ℝ) := this
    exact hmul.trans (h n)
  · have ha' : a < 0 := lt_of_not_ge ha
    have hpow_non : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by linarith [hp n]) _
    have hleft : (a / 4) * p n ^ ((3 : ℝ) / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hpow_non
    exact hleft.trans hcount_non

/-- **Paper-scale reduction.**  At `t = t_p`, the fixed-density interval count
follows from the explicit `p^{3/2}` count. -/
theorem paperIntervalDensity_of_shortIntervalCount {a : ℝ} {p err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddShortIntervalCount a p (paperT p) err) :
    YounisOddIntervalDensity a p (paperT p) err :=
  intervalDensity_of_shortIntervalCount hp h

/-- **Paper-scale converse.**  Density at `t = t_p` gives the explicit count
with constant `a/4`. -/
theorem paperShortIntervalCount_of_intervalDensity {a : ℝ} {p err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddIntervalDensity a p (paperT p) err) :
    YounisOddShortIntervalCount (a / 4) p (paperT p) err :=
  shortIntervalCount_of_intervalDensity hp h

/-- **Paper-scale relative density from the explicit fixed-density count.**
This is the composition with the relative-density reduction of
`RandomizedL30Relative`, and it is where the global parity bound enters: the
bound `globalOddSmoothCount ≤ p²/4 + 1/2` is exactly what lets the factor
`3/8` appear. -/
theorem paperRelative_of_shortIntervalCount {A a : ℝ} {p err : ℕ → ℝ}
    (hA : 0 ≤ A) (hp : ∀ n, 2 ≤ p n) (ha : 3 * A / 8 ≤ a)
    (h : YounisOddShortIntervalCount a p (paperT p) err) :
    YounisOddRelativeShortInterval A p (paperT p) err :=
  younisOddRelative_of_intervalDensity hA hp ha
    (paperIntervalDensity_of_shortIntervalCount hp h)

/-! ## The Younis-normalised paper count -/

/-- **The paper count on the interval length.**  The central interval contains
at least `c |interval| exp (-(1+ε)t)` odd smooth orders.  This is the local
Younis density at the paper scale, keeping the global density factor explicit
rather than replacing it by a constant. -/
def YounisOddPaperIntervalCount (c : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, c * ((centralOrderInterval p n).card : ℝ) *
      Real.exp (-(1 + err n) * t n) ≤ centralOddSmoothCount p t err n

/-- **The paper count on the `p^{3/2}` scale.**  The paper's displayed form
`c p^{3/2} exp (-(1+ε)t_p)` of the short-interval count. -/
def YounisOddPaperShortCount (c : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, c * p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) ≤
    centralOddSmoothCount p t err n

/-- **An upper bound on the global odd density.**  The global odd smooth
density is at most `C exp (-(1+ε)t)`.  This is the companion of the local
Younis count: the relative statement compares the local count with the global
density, so an upper bound of the same exponential shape is needed to pass from
the paper count to the relative statement. -/
def GlobalOddUpperDensity (C : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, globalOddSmoothCount p t err n / p n ^ 2 ≤
    C * Real.exp (-(1 + err n) * t n)

/-- The `p^{3/2}` form of the paper count implies the interval-length form,
because the interval has at most `p^{3/2}` integers. -/
theorem paperIntervalCount_of_paperShortCount {c : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddPaperShortCount c p t err) :
    YounisOddPaperIntervalCount c p t err := by
  intro n
  have hK := centralOrderInterval_card_le_three_halves (hp n)
  have he : (0 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := (Real.exp_pos _).le
  have hI : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  by_cases hc : 0 ≤ c
  · have hmul : c * ((centralOrderInterval p n).card : ℝ) ≤
        c * p n ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hK hc
    exact (mul_le_mul_of_nonneg_right hmul he).trans (h n)
  · have hc' : c < 0 := lt_of_not_ge hc
    have hleft : c * ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(1 + err n) * t n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc'.le hI) he
    have hright : (0 : ℝ) ≤ centralOddSmoothCount p t err n := by
      unfold centralOddSmoothCount
      positivity
    exact hleft.trans hright

/-- The interval-length form of the paper count gives the `p^{3/2}` form with
the forced constant `c/4`, using `|interval| ≥ p^{3/2}/4`. -/
theorem paperShortCount_of_paperIntervalCount {c : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (h : YounisOddPaperIntervalCount c p t err) :
    YounisOddPaperShortCount (c / 4) p t err := by
  intro n
  have hlow := centralOrderInterval_card_ge_quarter (hp n)
  have he : (0 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := (Real.exp_pos _).le
  have hcount_non : (0 : ℝ) ≤ centralOddSmoothCount p t err n := by
    unfold centralOddSmoothCount
    positivity
  by_cases hc : 0 ≤ c
  · have hmul : (c / 4) * p n ^ ((3 : ℝ) / 2) ≤
        c * ((centralOrderInterval p n).card : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlow hc
      calc (c / 4) * p n ^ ((3 : ℝ) / 2)
          = c * (p n ^ ((3 : ℝ) / 2) / 4) := by ring
        _ ≤ c * ((centralOrderInterval p n).card : ℝ) := this
    exact (mul_le_mul_of_nonneg_right hmul he).trans (h n)
  · have hc' : c < 0 := lt_of_not_ge hc
    have hpow_non : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by linarith [hp n]) _
    have hleft : (c / 4) * p n ^ ((3 : ℝ) / 2) *
        Real.exp (-(1 + err n) * t n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpow_non) he
    exact hleft.trans hcount_non

/-- **The paper count implies the relative short-interval density.**  If the
local paper count holds with constant `c` and the global odd density is at most
`C exp (-(1+ε)t)`, then the relative density holds with any `A` satisfying
`A C ≤ c`.  No interval-cardinality loss appears: the factor `|interval|` is
already present on both sides. -/
theorem paperRelative_of_globalUpper {A c C : ℝ} {p t err : ℕ → ℝ}
    (hA : 0 ≤ A) (hAC : A * C ≤ c)
    (hcount : YounisOddPaperIntervalCount c p t err)
    (hupper : GlobalOddUpperDensity C p t err) :
    YounisOddRelativeShortInterval A p t err := by
  intro n
  have hI : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  have he : (0 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := (Real.exp_pos _).le
  have hstep1 : A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p t err n / p n ^ 2) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (C * Real.exp (-(1 + err n) * t n)) :=
    mul_le_mul_of_nonneg_left (hupper n) (mul_nonneg hA hI)
  have hstep2 : A * ((centralOrderInterval p n).card : ℝ) *
        (C * Real.exp (-(1 + err n) * t n)) ≤
      c * ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(1 + err n) * t n) := by
    have hmul := mul_le_mul_of_nonneg_right hAC
      (by positivity : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(1 + err n) * t n))
    calc A * ((centralOrderInterval p n).card : ℝ) *
          (C * Real.exp (-(1 + err n) * t n))
        = (A * C) * (((centralOrderInterval p n).card : ℝ) *
            Real.exp (-(1 + err n) * t n)) := by ring
      _ ≤ c * (((centralOrderInterval p n).card : ℝ) *
            Real.exp (-(1 + err n) * t n)) := hmul
      _ = c * ((centralOrderInterval p n).card : ℝ) *
            Real.exp (-(1 + err n) * t n) := by ring
  exact hstep1.trans (hstep2.trans (hcount n))

/-- **The parity bound as a global upper density.**  If `(1+ε)t ≤ 0`, then
`exp (-(1+ε)t) ≥ 1`, and the parity bound
`globalOddSmoothCount ≤ p²/4 + 1/2 ≤ 3 p²/8` gives
`GlobalOddUpperDensity (3/8)`. -/
theorem globalOddUpperDensity_of_parity {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (ht : ∀ n, (1 + err n) * t n ≤ 0) :
    GlobalOddUpperDensity (3 / 8) p t err := by
  intro n
  have hG := globalOddSmoothCount_le_quarter_sq
    (p := p) (t := t) (err := err) (hp n)
  have hp2 : (0 : ℝ) < p n ^ 2 := by
    have hpos : (0 : ℝ) < p n := by linarith [hp n]
    positivity
  have hp4 : (4 : ℝ) ≤ p n ^ 2 := by
    have h2 : (2 : ℝ) ≤ p n := hp n
    nlinarith [sq_nonneg (p n - 2), h2]
  have hunit : (1 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := by
    have h : Real.exp 0 ≤ Real.exp (-(1 + err n) * t n) :=
      Real.exp_le_exp.mpr (by nlinarith [ht n])
    simpa using h
  have hquarter : globalOddSmoothCount p t err n ≤ (3 / 8) * p n ^ 2 := by
    nlinarith only [hG, hp4]
  rw [div_le_iff₀ hp2]
  calc globalOddSmoothCount p t err n ≤ (3 / 8) * p n ^ 2 := hquarter
    _ ≤ (3 / 8) * p n ^ 2 * Real.exp (-(1 + err n) * t n) := by
        have hmul := mul_le_mul_of_nonneg_left hunit
          (by positivity : (0 : ℝ) ≤ (3 / 8) * p n ^ 2)
        calc (3 / 8) * p n ^ 2 = (3 / 8) * p n ^ 2 * 1 := by ring
          _ ≤ (3 / 8) * p n ^ 2 * Real.exp (-(1 + err n) * t n) := hmul
    _ = (3 / 8) * Real.exp (-(1 + err n) * t n) * p n ^ 2 := by ring

/-- **The paper count plus the parity bound gives relative density.**  This is
the explicit use of the global parity bound requested by the paper-regime
reduction: it supplies `GlobalOddUpperDensity (3/8)`. -/
theorem paperRelative_of_parity {A c : ℝ} {p t err : ℕ → ℝ}
    (hA : 0 ≤ A) (hp : ∀ n, 2 ≤ p n) (ht : ∀ n, (1 + err n) * t n ≤ 0)
    (hAC : A * (3 / 8) ≤ c)
    (hcount : YounisOddPaperIntervalCount c p t err) :
    YounisOddRelativeShortInterval A p t err :=
  paperRelative_of_globalUpper hA hAC hcount
    (globalOddUpperDensity_of_parity hp ht)

/-- **The paper-scale short-interval count gives the relative density**, with
the global upper bound and the constant relation made explicit.  This is the
faithful paper-regime implication: the local count at the paper cutoff plus the
global density upper bound. -/
theorem paperRelative_of_paperShortCount {A c C : ℝ} {p err : ℕ → ℝ}
    (hA : 0 ≤ A) (hp : ∀ n, 2 ≤ p n) (hAC : A * C ≤ c)
    (hcount : YounisOddPaperShortCount c p (paperT p) err)
    (hupper : GlobalOddUpperDensity C p (paperT p) err) :
    YounisOddRelativeShortInterval A p (paperT p) err :=
  paperRelative_of_globalUpper hA hAC
    (paperIntervalCount_of_paperShortCount hp hcount) hupper

/-- **Full paper-scale reduction to the odd central count.**  From the paper's
explicit short-interval count, the global upper density, and the global odd
lower bound with `A B ≥ 4`, the Younis odd central count follows at `t = t_p`. -/
theorem paperCentralCount_of_globalUpper {A B c C : ℝ} {p err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hAC : A * C ≤ c)
    (hcount : YounisOddPaperIntervalCount c p (paperT p) err)
    (hupper : GlobalOddUpperDensity C p (paperT p) err)
    (hglob : YounisOddGlobalLower B p (paperT p) err) :
    YounisOddCentralCount p (paperT p) err :=
  younisOddCentralCount_of_density hp hA hB hAB
    (paperRelative_of_globalUpper hA.le hAC hcount hupper) hglob

/-! ## The witness construction at a general cutoff -/

/-- The smooth orders are monotone in the cutoff. -/
theorem centralSmoothOrders_mono_cutoff {p t err t' err' : ℕ → ℝ} {n : ℕ}
    (h : smoothCutoff t err n ≤ smoothCutoff t' err' n) :
    centralSmoothOrders p t err n ⊆ centralSmoothOrders p t' err' n := by
  intro m hm
  rw [centralSmoothOrders, Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, fun q hq => (hm.2 q hq).trans h⟩

/-- The odd smooth orders are monotone in the cutoff. -/
theorem centralOddSmoothOrders_mono_cutoff {p t err t' err' : ℕ → ℝ} {n : ℕ}
    (h : smoothCutoff t err n ≤ smoothCutoff t' err' n) :
    centralOddSmoothOrders p t err n ⊆ centralOddSmoothOrders p t' err' n := by
  intro m hm
  rw [centralOddSmoothOrders, Finset.mem_filter] at hm ⊢
  exact ⟨centralSmoothOrders_mono_cutoff h hm.1, hm.2⟩

/-- The witness cutoff is `p³`. -/
theorem smoothCutoff_witnessT (n : ℕ) :
    smoothCutoff witnessT witnessErr n = witnessP n ^ 3 := by
  unfold smoothCutoff witnessT witnessErr
  rw [show (1 + (0 : ℝ)) * (3 * Real.log (witnessP n)) =
      ((3 : ℕ) : ℝ) * Real.log (witnessP n) by norm_num]
  rw [Real.exp_nat_mul, Real.exp_log (witnessP_pos n)]

/-- The witness level is a lower bound on the central odd smooth count for
every cutoff dominating `p³`. -/
theorem witnessLevel_le_centralOddSmoothCount_of_cutoff {t err : ℕ → ℝ}
    (hdom : ∀ n, smoothCutoff witnessT witnessErr n ≤ smoothCutoff t err n)
    (n : ℕ) :
    (witnessLevel n : ℝ) ≤ centralOddSmoothCount witnessP t err n := by
  have hsub : witnessLocalSet n ⊆ centralOddSmoothOrders witnessP t err n :=
    (witnessLocalSet_subset n).trans (centralOddSmoothOrders_mono_cutoff (hdom n))
  have hcard := Finset.card_le_card hsub
  rw [witnessLocalSet_card] at hcard
  unfold centralOddSmoothCount
  exact_mod_cast hcard

/-- **The witness density at any cutoff dominating `p³`.**  The explicit local
set needs only `Y ≥ p³`; the interval-cardinality estimate is the same as in
`witness_intervalDensity`. -/
theorem witnessIntervalDensity_of_cutoff {t err : ℕ → ℝ}
    (hdom : ∀ n, smoothCutoff witnessT witnessErr n ≤ smoothCutoff t err n) :
    YounisOddIntervalDensity witnessDensity witnessP t err := by
  intro n
  have hC := witnessLevel_le_centralOddSmoothCount_of_cutoff hdom n
  have hK := witness_centralOrderInterval_card_le n
  have hlevel_one : (1 : ℝ) ≤ (witnessLevel n : ℝ) := by
    have hpos : 0 < witnessLevel n := by
      unfold witnessLevel
      positivity
    have h1 : 1 ≤ witnessLevel n := by omega
    exact_mod_cast h1
  have hK' : witnessDensity * ((centralOrderInterval witnessP n).card : ℝ) ≤
      witnessDensity * (4 * (witnessLevel n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hK (by norm_num [witnessDensity])
  have hlevel : witnessDensity * (4 * (witnessLevel n : ℝ) + 1) ≤
      (witnessLevel n : ℝ) := by
    unfold witnessDensity
    nlinarith [hlevel_one]
  exact hK'.trans (hlevel.trans hC)

/-- **The witness construction in the paper cutoff shape.**  When the
exponent `(1+ε)t` dominates `3 log p` (so that `Y = exp ((1+ε)t) ≥ p³`), the
witness gives interval density `1/5`.  This is the large-cutoff corner of the
paper's `Y = exp ((1+ε)t_p)` family. -/
theorem paperWitnessIntervalDensity {t err : ℕ → ℝ}
    (hdom : ∀ n, 3 * Real.log (witnessP n) ≤ (1 + err n) * t n) :
    YounisOddIntervalDensity witnessDensity witnessP t err := by
  apply witnessIntervalDensity_of_cutoff
  intro n
  have hcube : witnessP n ^ 3 = Real.exp (3 * Real.log (witnessP n)) := by
    rw [show (3 : ℝ) * Real.log (witnessP n) =
        ((3 : ℕ) : ℝ) * Real.log (witnessP n) by norm_num]
    rw [Real.exp_nat_mul, Real.exp_log (witnessP_pos n)]
  rw [smoothCutoff_witnessT, hcube]
  unfold smoothCutoff
  exact Real.exp_le_exp.mpr (hdom n)

/-- The general cutoff-dominance theorem recovers the concrete witness of
`RandomizedL30Relative`. -/
theorem witness_intervalDensity_recovered :
    YounisOddIntervalDensity witnessDensity witnessP witnessT witnessErr :=
  witnessIntervalDensity_of_cutoff (fun _ => le_rfl)

/-- **The paper-normalised count is nonvacuous.**  For the witness scale the
fixed-density bound gives the paper's `|interval| exp (-(1+ε)t)` count with
constant `1/5`, because `exp (-(1+ε)t) ≤ 1` there. -/
theorem witness_paperIntervalCount :
    YounisOddPaperIntervalCount witnessDensity witnessP witnessT witnessErr := by
  intro n
  have hdens := witness_intervalDensity n
  have hp1 : (1 : ℝ) ≤ witnessP n := by linarith [witnessP_ge_two n]
  have hlog : 0 ≤ Real.log (witnessP n) := Real.log_nonneg hp1
  have he : Real.exp (-(1 + witnessErr n) * witnessT n) ≤ 1 := by
    have h : Real.exp (-(1 + witnessErr n) * witnessT n) ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      unfold witnessErr witnessT
      nlinarith
    simpa using h
  have hI : (0 : ℝ) ≤ ((centralOrderInterval witnessP n).card : ℝ) := by positivity
  have hnon : (0 : ℝ) ≤ witnessDensity *
      ((centralOrderInterval witnessP n).card : ℝ) :=
    mul_nonneg (by norm_num [witnessDensity]) hI
  calc witnessDensity * ((centralOrderInterval witnessP n).card : ℝ) *
        Real.exp (-(1 + witnessErr n) * witnessT n)
      ≤ witnessDensity * ((centralOrderInterval witnessP n).card : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left he hnon
    _ = witnessDensity * ((centralOrderInterval witnessP n).card : ℝ) := by ring
    _ ≤ centralOddSmoothCount witnessP witnessT witnessErr n := hdens

/-! ## The paper scale lies below the witness cutoff -/

/-- For `p ≥ e`, the paper scale is at most `3 log p`. -/
theorem paperT_le_three_log {p : ℕ → ℝ} {n : ℕ} (hp : Real.exp 1 ≤ p n) :
    paperT p n ≤ 3 * Real.log (p n) := by
  have hp_pos : (0 : ℝ) < p n := lt_of_lt_of_le (Real.exp_pos 1) hp
  set L : ℝ := Real.log (p n) with hL
  have hL1 : (1 : ℝ) ≤ L := by
    have h := Real.log_le_log (Real.exp_pos 1) hp
    rw [Real.log_exp] at h
    exact h
  have hlogL_le : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L)
    linarith
  have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hprod : L * Real.log L ≤ L * L :=
    mul_le_mul_of_nonneg_left hlogL_le (by linarith)
  have hsqrt : Real.sqrt (L * Real.log L) ≤ Real.sqrt (L * L) :=
    Real.sqrt_le_sqrt hprod
  have hsqrtLL : Real.sqrt (L * L) = L := by
    have hLnon : 0 ≤ L := by linarith
    calc Real.sqrt (L * L) = Real.sqrt (L ^ 2) := by
          rw [show L * L = L ^ 2 by ring]
      _ = |L| := Real.sqrt_sq_eq_abs L
      _ = L := abs_of_nonneg hLnon
  have hmain : Real.sqrt (L * Real.log L) ≤ L := hsqrt.trans hsqrtLL.le
  rw [show paperT p n = Real.sqrt (L * Real.log L) from rfl]
  calc Real.sqrt (L * Real.log L) ≤ L := hmain
    _ = Real.log (p n) := hL
    _ ≤ 3 * Real.log (p n) := by linarith

/-- At zero relative error the paper cutoff is at most `p³`.  In particular, at
the witness scale `p = witnessP` it is at most the witness cutoff, so the
witness set, which requires a cutoff at least `p³`, cannot be used at the paper
scale; the remaining content is exactly the short-interval count of §1-§2. -/
theorem paperSmoothCutoff_zero_le_cube {p : ℕ → ℝ} {n : ℕ}
    (hp : Real.exp 1 ≤ p n) :
    paperSmoothCutoff p (fun _ => 0) n ≤ p n ^ 3 := by
  have hp_pos : (0 : ℝ) < p n := lt_of_lt_of_le (Real.exp_pos 1) hp
  unfold paperSmoothCutoff
  rw [show (1 + (0 : ℝ)) * paperT p n = paperT p n by ring]
  have h1 : paperT p n ≤ 3 * Real.log (p n) := paperT_le_three_log hp
  calc Real.exp (paperT p n) ≤ Real.exp (3 * Real.log (p n)) :=
        Real.exp_le_exp.mpr h1
    _ = p n ^ 3 := by
        rw [show (3 : ℝ) * Real.log (p n) =
            ((3 : ℕ) : ℝ) * Real.log (p n) by norm_num]
        rw [Real.exp_nat_mul, Real.exp_log hp_pos]

/-! ## Axiom audit -/

#print axioms centralOrderInterval_card_le_half_add_one
#print axioms centralOrderInterval_card_le_three_halves
#print axioms intervalDensity_of_shortIntervalCount
#print axioms shortIntervalCount_of_intervalDensity
#print axioms paperIntervalDensity_of_shortIntervalCount
#print axioms paperShortIntervalCount_of_intervalDensity
#print axioms paperRelative_of_shortIntervalCount
#print axioms paperIntervalCount_of_paperShortCount
#print axioms paperShortCount_of_paperIntervalCount
#print axioms paperRelative_of_globalUpper
#print axioms globalOddUpperDensity_of_parity
#print axioms paperRelative_of_parity
#print axioms paperRelative_of_paperShortCount
#print axioms paperCentralCount_of_globalUpper
#print axioms centralSmoothOrders_mono_cutoff
#print axioms centralOddSmoothOrders_mono_cutoff
#print axioms smoothCutoff_witnessT
#print axioms witnessLevel_le_centralOddSmoothCount_of_cutoff
#print axioms witnessIntervalDensity_of_cutoff
#print axioms paperWitnessIntervalDensity
#print axioms witness_intervalDensity_recovered
#print axioms witness_paperIntervalCount
#print axioms paperT_le_three_log
#print axioms paperSmoothCutoff_zero_le_cube

end

end Cogentic.RandomizedL30Interval
