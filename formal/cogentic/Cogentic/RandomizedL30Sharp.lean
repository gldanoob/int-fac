import Cogentic.RandomizedL30SmoothDensity

set_option maxHeartbeats 4000000

/-!
# L30: the sharp-exponent density predicates and their relative-density chain

This file isolates the *sound* normalization of the paper-scale smooth density
used by the L30 endpoint.  The paper-scale upper estimate of
`Cogentic/RandomizedL30UpperDensity`,

`PaperScaleSmoothUpper C p ε`,
asks for the factor `exp (-(1+ε) t_p)`, which is strictly smaller than the true
Dickman factor `exp (-(u log u))`; it is therefore false for every `C`
(`Cogentic/RandomizedL30Normalization.paperScaleSmoothUpper_false`).  The
present file is the low-level, endpoint-independent half of the repair: it
defines the corrected predicates

* `PaperScaleSmoothUpperSharp C p ε`,
* `GlobalOddUpperDensitySharp C p ε`,
* `GlobalOddUpperDensityEps C p ε`,
* `YounisOddPaperSharpCount c p ε`,
* `YounisOddPaperSharpIntervalCount c p ε`,

all with the true factor `exp (-(u log u))`, and proves

* `globalOddUpperDensitySharp_of_paperScaleSharp`,
* `paperSharpIntervalCount_of_paperSharpCount`,
* `paperRelative_of_sharpUpper`.

The latter is the replacement for `paperRelative_of_globalUpper`: with the
*same* sharp exponent on the local lower bound and on the global upper bound,
the relative density follows with any constants `A C ≤ c`.  Keeping this module
below the endpoint waves lets `RandomizedPaperEndpointWave13` and its
successors consume the sharp chain without a circular import.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or error
is set to zero.
-/

namespace Cogentic.RandomizedL30Sharp

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity

noncomputable section

/-- The sharp paper-scale smooth upper estimate.  The exponential factor is the
true Dickman exponent `u log u`, not the too-small `(1+ε)t_p`. -/
def PaperScaleSmoothUpperSharp (C : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
      C * p n ^ 2 *
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n)))

/-- The corrected global odd upper density, with the sharp exponent `u log u`. -/
def GlobalOddUpperDensitySharp (C : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 ≤
      C * Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n)))

/-- The safe over-estimate correction at `(1-ε)t_p`.  Since
`1-ε < 1/(1+ε)`, this factor is larger than the true density factor, so it is
a valid (if lossy) upper bound. -/
def GlobalOddUpperDensityEps (C : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 ≤
      C * Real.exp (-(1 - ε) * paperT p n)

/-- The sharp local paper count on the `p^{3/2}` scale, using the true exponent
`u log u` instead of `(1+ε)t_p`. -/
def YounisOddPaperSharpCount (c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * p n ^ ((3 : ℝ) / 2) *
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n

/-- The sharp local paper count in interval-length form. -/
def YounisOddPaperSharpIntervalCount (c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n

/-- The eventual relative short-interval density at the sharp exponent.  This is
the conclusion of `paperRelative_of_sharpUpper`; it is definitionally the usual
relative count with the sharp global density inserted. -/
def EventuallyYounisOddSharpRelativeShortInterval
    (A : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n

/-- The sharp smooth upper estimate implies the sharp global odd upper
density by the parity inclusion. -/
theorem globalOddUpperDensitySharp_of_paperScaleSharp
    {C : ℝ} {p : ℕ → ℝ} (hg : PaperDensityGrowth p) {ε : ℝ}
    (h : PaperScaleSmoothUpperSharp C p ε) :
    GlobalOddUpperDensitySharp C p ε := by
  filter_upwards [h, hg.eventually_sixteen] with n hn hp
  have hp2 : 0 < p n ^ 2 := by
    have : 0 < p n := by linarith
    positivity
  have hsub : globalOddSmoothOrders p (paperT p) (paperError ε) n ⊆
      globalSmoothOrders p (paperT p) (paperError ε) n := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hcard : globalOddSmoothCount p (paperT p) (paperError ε) n ≤
      ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
    unfold globalOddSmoothCount
    exact_mod_cast Finset.card_le_card hsub
  rw [div_le_iff₀ hp2]
  calc
    globalOddSmoothCount p (paperT p) (paperError ε) n
        ≤ ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := hcard
    _ ≤ C * p n ^ 2 *
          Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) := hn
    _ = C * Real.exp (-(paperDensityU p ε n *
          Real.log (paperDensityU p ε n))) * p n ^ 2 := by ring

/-- The sharp `p^{3/2}` local count gives the sharp interval-length count,
because the central interval contains at most `p^{3/2}` integers. -/
theorem paperSharpIntervalCount_of_paperSharpCount {c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ n, 2 ≤ p n) (h : YounisOddPaperSharpCount c p ε) :
    YounisOddPaperSharpIntervalCount c p ε := by
  filter_upwards [h] with n hn
  have hK := centralOrderInterval_card_le_three_halves (p := p) (n := n) (hp n)
  have he : (0 : ℝ) ≤
      Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) :=
    (Real.exp_pos _).le
  have hI : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  by_cases hc : 0 ≤ c
  · have hmul : c * ((centralOrderInterval p n).card : ℝ) ≤
        c * p n ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hK hc
    exact (mul_le_mul_of_nonneg_right hmul he).trans hn
  · have hc' : c < 0 := lt_of_not_ge hc
    have hleft : c * ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc'.le hI) he
    have hright : (0 : ℝ) ≤ centralOddSmoothCount p (paperT p) (paperError ε) n := by
      unfold centralOddSmoothCount
      positivity
    exact hleft.trans hright

/-- **The corrected relative-density chain.**  With the *same* sharp exponent
`u log u` on the local lower bound and on the global upper bound, the relative
density follows with any constants `A C ≤ c`.  This is the replacement for
`paperRelative_of_globalUpper`, which cannot be used with `(1+ε)t_p` on the
upper side. -/
theorem paperRelative_of_sharpUpper {A c C : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hA : 0 ≤ A) (hAC : A * C ≤ c)
    (hcount : YounisOddPaperSharpIntervalCount c p ε)
    (hupper : GlobalOddUpperDensitySharp C p ε) :
    EventuallyYounisOddSharpRelativeShortInterval A p ε := by
  filter_upwards [hcount, hupper] with n hc hu
  have hI : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  have he : (0 : ℝ) ≤
      Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) :=
    (Real.exp_pos _).le
  have hstep1 : A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (C * Real.exp (-(paperDensityU p ε n *
          Real.log (paperDensityU p ε n)))) :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  have hstep2 : A * ((centralOrderInterval p n).card : ℝ) *
        (C * Real.exp (-(paperDensityU p ε n *
          Real.log (paperDensityU p ε n)))) ≤
      c * ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) := by
    have hmul := mul_le_mul_of_nonneg_right hAC
      (by positivity : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))))
    calc
      A * ((centralOrderInterval p n).card : ℝ) *
          (C * Real.exp (-(paperDensityU p ε n *
            Real.log (paperDensityU p ε n))))
          = (A * C) * (((centralOrderInterval p n).card : ℝ) *
              Real.exp (-(paperDensityU p ε n *
                Real.log (paperDensityU p ε n)))) := by ring
      _ ≤ c * (((centralOrderInterval p n).card : ℝ) *
              Real.exp (-(paperDensityU p ε n *
                Real.log (paperDensityU p ε n)))) := hmul
      _ = c * ((centralOrderInterval p n).card : ℝ) *
              Real.exp (-(paperDensityU p ε n *
                Real.log (paperDensityU p ε n))) := by ring
  exact hstep1.trans (hstep2.trans hc)

/-! ## Axiom audit -/

#print axioms globalOddUpperDensitySharp_of_paperScaleSharp
#print axioms paperSharpIntervalCount_of_paperSharpCount
#print axioms paperRelative_of_sharpUpper

end

end Cogentic.RandomizedL30Sharp
