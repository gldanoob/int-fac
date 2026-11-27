import Cogentic.RandomizedL27Scale

/-!
# L27 central window: the paper's smooth-order set

`Cogentic.RandomizedL27Scale` isolates the geometric leaf

`CentralTraceWindow p smooth θ : ∀ n j, smooth n j = true →
  (hasseTrace (p n) j)² ≤ (4 - θ) p n`

and proves it equivalent to `HurwitzDiscriminantScale`.  The `smooth` argument
there is the arbitrary boolean field of `L27_1Inputs`; the countermodel
`hasseBound_not_imply_hurwitzDiscriminantScale` shows that no Hasse-type input
forces the window on an unrestricted smooth set.

The modelling point of this file is that the paper's counted smooth-order set
is *not* the unrestricted field: `ψ₀` counts the stage-one smooth orders whose
Frobenius trace lies in the central interval

`|j - (p + 1)| ≤ sqrt ((4 - θ) p)`.

We therefore name that set (`PaperSmoothOrder` / `paperSmooth`) and prove:

* the central interval is exactly the squared trace window
  (`paperOrderWindow_iff_centralWindow`);
* the paper's set satisfies `CentralTraceWindow`
  (`centralTraceWindow_paperSmooth`), hence `HurwitzDiscriminantScale`
  (`hurwitzDiscriminantScale_paperSmooth`);
* passage between the paper's interval definition and the squared form used by
  `CentralTraceWindow` is a definitional equality after unfolding
  (`paperSmooth_eq_windowSmooth`, `paperSmooth_eq_true_iff_centralWindow`);
* `CentralTraceWindow` is exactly the assertion that the smooth set is its own
  central-window restriction (`centralTraceWindow_iff_windowSmooth_eq`,
  `centralTraceWindow_iff_exists_paperSmooth`).

The stronger paper-side variant `t² ≤ (1 - θ)p` is already reduced to the
central window in `RandomizedL27Scale.centralTraceWindow_of_centralTraceFraction`;
this file models the exact central-window set `(4 - θ)p` that the L27 bundle
consumes.

The window is not collapsed: at the centre `j = p + 1` the trace is zero, and
for `θ = 1`, `p ≥ 4` the two distinct orders `p` and `p + 2` both lie in the
window (`center_mem_centralWindow`, `centralWindow_two_orders_at_one`).  No
order count, class number, or loss is set to zero in this identification.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL27Window

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27Scale
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The paper's central order interval and smooth-order set -/

/-- The central order interval of the paper.  An order `j` is counted when its
Frobenius trace `t = p + 1 - j` lies within the central half-width
`sqrt ((4 - θ) p)`.  This is the interval form of `InCentralWindow`; the square
of the trace inequality is derived in `paperOrderWindow_iff_centralWindow`. -/
def PaperOrderWindow (p : ℕ → ℕ) (θ : ℝ) (n j : ℕ) : Prop :=
  |(j : ℝ) - ((p n : ℝ) + 1)| ≤ Real.sqrt ((4 - θ) * (p n : ℝ))

/-- The paper's smooth-order set: stage-one smooth orders (the ambient boolean
`smooth` of `L27_1Inputs`) that lie in the central order interval.  This is the
set counted by `ψ₀` in the L27 reduction. -/
def PaperSmoothOrder (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool) (θ : ℝ)
    (n j : ℕ) : Prop :=
  smooth n j = true ∧ PaperOrderWindow p θ n j

/-- Boolean form of the paper's smooth-order set. -/
def paperSmooth (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool) (θ : ℝ) :
    ℕ → ℕ → Bool := by
  classical
  exact fun n j => smooth n j && decide (PaperOrderWindow p θ n j)

/-- The squared-trace restriction of an arbitrary smooth predicate.  This is
the boolean set appearing in `CentralTraceWindow`. -/
def windowSmooth (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool) (θ : ℝ) :
    ℕ → ℕ → Bool := by
  classical
  exact fun n j => smooth n j && decide (InCentralWindow p θ n j)

/-- Unfolding the paper's boolean smooth set. -/
theorem paperSmooth_eq_true_iff {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    {n j : ℕ} :
    paperSmooth p smooth θ n j = true ↔
      smooth n j = true ∧ PaperOrderWindow p θ n j := by
  simp [paperSmooth, Bool.and_eq_true, decide_eq_true_eq]

/-- Unfolding the squared-trace restriction. -/
theorem windowSmooth_eq_true_iff {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    {n j : ℕ} :
    windowSmooth p smooth θ n j = true ↔
      smooth n j = true ∧ InCentralWindow p θ n j := by
  simp [windowSmooth, Bool.and_eq_true, decide_eq_true_eq]

/-- The paper's smooth set is a subset of the ambient smooth set; the window
restriction only discards orders, it never adds any. -/
theorem paperSmooth_subset {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    {n j : ℕ} (h : paperSmooth p smooth θ n j = true) :
    smooth n j = true :=
  (paperSmooth_eq_true_iff.mp h).1

/-- The window-restricted set is a subset of the ambient smooth set. -/
theorem windowSmooth_subset {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    {n j : ℕ} (h : windowSmooth p smooth θ n j = true) :
    smooth n j = true :=
  (windowSmooth_eq_true_iff.mp h).1

/-! ## 2. The central interval is the squared trace window -/

/-- Cast form of the Frobenius trace. -/
theorem hasseTrace_cast (p j : ℕ) :
    (hasseTrace p j : ℝ) = (p : ℝ) + 1 - (j : ℝ) := by
  unfold hasseTrace
  push_cast
  ring

/-- **The paper's interval is exactly the squared central-trace condition.**
For `θ ≤ 4` the real interval `|j - (p + 1)| ≤ sqrt ((4 - θ) p)` and the
squared inequality `(p + 1 - j)² ≤ (4 - θ) p` are equivalent.  This is the
only algebraic content of the identification. -/
theorem paperOrderWindow_iff_centralWindow {p : ℕ → ℕ} {θ : ℝ} {n j : ℕ}
    (hθ : θ ≤ 4) :
    PaperOrderWindow p θ n j ↔ InCentralWindow p θ n j := by
  unfold PaperOrderWindow InCentralWindow
  have hp : (0 : ℝ) ≤ (p n : ℝ) := by positivity
  have hw : (0 : ℝ) ≤ (4 - θ) * (p n : ℝ) :=
    mul_nonneg (by linarith) hp
  have ht : (hasseTrace (p n) j : ℝ) = (p n : ℝ) + 1 - (j : ℝ) :=
    hasseTrace_cast (p n) j
  constructor
  · intro h
    have h_abs : |(hasseTrace (p n) j : ℝ)| ≤
        Real.sqrt ((4 - θ) * (p n : ℝ)) := by
      rw [ht]
      simpa [abs_sub_comm] using h
    have hsq : ((hasseTrace (p n) j : ℝ)) ^ 2 ≤
        (Real.sqrt ((4 - θ) * (p n : ℝ))) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using h_abs
    calc
      ((hasseTrace (p n) j : ℝ)) ^ 2
          ≤ (Real.sqrt ((4 - θ) * (p n : ℝ))) ^ 2 := hsq
      _ = (4 - θ) * (p n : ℝ) := Real.sq_sqrt hw
  · intro h
    have hsq : ((hasseTrace (p n) j : ℝ)) ^ 2 ≤
        (Real.sqrt ((4 - θ) * (p n : ℝ))) ^ 2 := by
      rw [Real.sq_sqrt hw]
      exact h
    have h_abs : |(hasseTrace (p n) j : ℝ)| ≤
        Real.sqrt ((4 - θ) * (p n : ℝ)) :=
      abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _)
    rw [ht] at h_abs
    rw [abs_sub_comm]
    exact h_abs

/-- **The smallest explicit definitional equality, Prop form.**  After
unfolding, the paper's smooth-order predicate is exactly the ambient smooth set
filtered by the central trace condition. -/
theorem paperSmoothOrder_iff_smooth_and_central {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} (hθ : θ ≤ 4) {n j : ℕ} :
    PaperSmoothOrder p smooth θ n j ↔
      smooth n j = true ∧ InCentralWindow p θ n j := by
  unfold PaperSmoothOrder
  rw [paperOrderWindow_iff_centralWindow hθ]

/-- **The smallest explicit definitional equality, boolean form.**  The
paper's boolean smooth set is exactly the ambient smooth set filtered by the
central trace condition.  This is the modelling identification: the paper's
`ψ₀` set is defined by the central window, not by the unrestricted `smooth`
field. -/
theorem paperSmooth_eq_true_iff_centralWindow {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} (hθ : θ ≤ 4) {n j : ℕ} :
    paperSmooth p smooth θ n j = true ↔
      smooth n j = true ∧ InCentralWindow p θ n j := by
  rw [paperSmooth_eq_true_iff, paperOrderWindow_iff_centralWindow hθ]

/-- **The interval and squared-trace boolean sets agree.**  The paper's smooth
set defined by the order interval is the same boolean predicate as the
central-window restriction used by `CentralTraceWindow`. -/
theorem paperSmooth_eq_windowSmooth {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool}
    {θ : ℝ} (hθ : θ ≤ 4) :
    paperSmooth p smooth θ = windowSmooth p smooth θ := by
  funext n j
  cases hs : smooth n j
  · simp [paperSmooth, windowSmooth, hs]
  · by_cases hw : PaperOrderWindow p θ n j
    · have hw' : InCentralWindow p θ n j :=
        (paperOrderWindow_iff_centralWindow hθ).mp hw
      simp [paperSmooth, windowSmooth, hs, hw, hw']
    · have hw' : ¬ InCentralWindow p θ n j :=
        fun h => hw ((paperOrderWindow_iff_centralWindow hθ).mpr h)
      simp [paperSmooth, windowSmooth, hs, hw, hw']

/-! ## 3. The paper's smooth set satisfies the central window -/

/-- **`CentralTraceWindow` for the paper's smooth-order set.**  This is the
modelling identification: once the counted set is defined by the central order
interval, the trace inequality is immediate from the interval bound. -/
theorem centralTraceWindow_paperSmooth {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool}
    {θ : ℝ} (hθ : θ ≤ 4) :
    CentralTraceWindow p (paperSmooth p smooth θ) θ := by
  intro n j hs
  have h := (paperSmooth_eq_true_iff.mp hs).2
  exact (paperOrderWindow_iff_centralWindow hθ).mp h

/-- The squared-trace restriction satisfies the central window by
construction. -/
theorem centralTraceWindow_windowSmooth (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool)
    (θ : ℝ) :
    CentralTraceWindow p (windowSmooth p smooth θ) θ := by
  intro n j hs
  exact (windowSmooth_eq_true_iff.mp hs).2

/-- Direct form for the smooth field of an `L27_1Inputs`. -/
theorem centralTraceWindow_paperSmooth_of_inputs (I : L27_1Inputs) {θ : ℝ}
    (hθ : θ ≤ 4) :
    CentralTraceWindow I.p (paperSmooth I.p I.smooth θ) θ :=
  centralTraceWindow_paperSmooth hθ

/-- If a smooth set is the paper's interval-restricted set, it satisfies the
central window.  This is the constructor form of the identification. -/
theorem centralTraceWindow_of_eq_paperSmooth {p : ℕ → ℕ}
    {smooth ambient : ℕ → ℕ → Bool} {θ : ℝ} (hθ : θ ≤ 4)
    (h : smooth = paperSmooth p ambient θ) :
    CentralTraceWindow p smooth θ := by
  rw [h]
  exact centralTraceWindow_paperSmooth hθ

/-- The paper's smooth set gives the discriminant scale of
`RandomizedL27Hurwitz`. -/
theorem hurwitzDiscriminantScale_paperSmooth {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} (hθ : θ ≤ 4) :
    HurwitzDiscriminantScale p (paperSmooth p smooth θ) θ :=
  hurwitzDiscriminantScale_of_centralTraceWindow
    (centralTraceWindow_paperSmooth hθ)

/-- At `θ = 1` the paper's smooth set satisfies the existing `CentralTrace`
(`t² ≤ 3p`). -/
theorem centralTrace_paperSmooth_one {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool} :
    CentralTrace p (paperSmooth p smooth 1) :=
  centralTrace_of_centralTraceWindow_one
    (centralTraceWindow_paperSmooth (θ := 1) (by norm_num))

/-- At `θ = 1` the paper's smooth set gives the discriminant scale with
`θ = 1`, i.e. `p ≤ D(p, j)` on the counted orders. -/
theorem hurwitzDiscriminantScale_paperSmooth_one {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} :
    HurwitzDiscriminantScale p (paperSmooth p smooth 1) 1 :=
  hurwitzDiscriminantScale_one_of_centralTrace (centralTrace_paperSmooth_one)

/-! ## 4. `CentralTraceWindow` as a definitional equality -/

/-- **The exact content of `CentralTraceWindow`.**  The hypothesis holds for a
smooth set exactly when restricting it to the central window changes nothing.
This is the lossless form of the modelling identification. -/
theorem centralTraceWindow_iff_windowSmooth_eq {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} :
    CentralTraceWindow p smooth θ ↔ windowSmooth p smooth θ = smooth := by
  constructor
  · intro h
    funext n j
    cases hs : smooth n j
    · simp [windowSmooth, hs]
    · have hw : InCentralWindow p θ n j := h n j hs
      simp [windowSmooth, hs, hw]
  · intro h n j hs
    have h' : windowSmooth p smooth θ n j = true := by
      simpa [hs] using congrFun (congrFun h n) j
    exact (windowSmooth_eq_true_iff.mp h').2

/-- **Characterization of the paper's model.**  A smooth set satisfies the
central window exactly when it is the central-window restriction of some
ambient smooth set.  Taking the ambient set to be the set itself is the
forward direction; the backward direction is closure under restriction. -/
theorem centralTraceWindow_iff_exists_windowSmooth {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} :
    CentralTraceWindow p smooth θ ↔
      ∃ ambient : ℕ → ℕ → Bool, smooth = windowSmooth p ambient θ := by
  constructor
  · intro h
    exact ⟨smooth, (centralTraceWindow_iff_windowSmooth_eq.mp h).symm⟩
  · rintro ⟨ambient, rfl⟩
    exact centralTraceWindow_windowSmooth p ambient θ

/-- The same characterization stated with the paper's interval definition of
the smooth set. -/
theorem centralTraceWindow_iff_exists_paperSmooth {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} (hθ : θ ≤ 4) :
    CentralTraceWindow p smooth θ ↔
      ∃ ambient : ℕ → ℕ → Bool, smooth = paperSmooth p ambient θ := by
  constructor
  · intro h
    refine ⟨smooth, ?_⟩
    rw [paperSmooth_eq_windowSmooth hθ]
    exact (centralTraceWindow_iff_windowSmooth_eq.mp h).symm
  · rintro ⟨ambient, rfl⟩
    exact centralTraceWindow_paperSmooth hθ

/-- The paper's smooth set equals the unrestricted smooth set exactly when the
unrestricted set already satisfies the central window. -/
theorem paperSmooth_eq_smooth_iff {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} (hθ : θ ≤ 4) :
    paperSmooth p smooth θ = smooth ↔ CentralTraceWindow p smooth θ := by
  rw [paperSmooth_eq_windowSmooth hθ]
  exact (centralTraceWindow_iff_windowSmooth_eq).symm

/-! ## 5. Nondegeneracy: the window is not a point -/

/-- The centre order `j = p + 1` has trace `0`, so it is always in the paper's
interval. -/
theorem center_mem_paperOrderWindow (p : ℕ → ℕ) (θ : ℝ) (n : ℕ) :
    PaperOrderWindow p θ n (p n + 1) := by
  unfold PaperOrderWindow
  have hzero : (((p n + 1 : ℕ) : ℝ) - ((p n : ℝ) + 1)) = 0 := by
    push_cast
    ring
  rw [hzero, abs_zero]
  exact Real.sqrt_nonneg _

/-- The centre order is in the squared central window whenever `θ ≤ 4`. -/
theorem center_mem_centralWindow {p : ℕ → ℕ} {θ : ℝ} {n : ℕ}
    (hθ : θ ≤ 4) (hp : 0 < p n) :
    InCentralWindow p θ n (p n + 1) := by
  unfold InCentralWindow
  have ht : (hasseTrace (p n) (p n + 1) : ℝ) = 0 := by
    rw [hasseTrace_cast]
    push_cast
    ring
  rw [ht]
  have hw : (0 : ℝ) ≤ (4 - θ) * (p n : ℝ) :=
    mul_nonneg (by linarith) (by positivity)
  simpa using hw

/-- If the ambient smooth set contains the centre order, so does the paper's
smooth set. -/
theorem paperSmooth_center {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    {n : ℕ} (hs : smooth n (p n + 1) = true) :
    paperSmooth p smooth θ n (p n + 1) = true := by
  rw [paperSmooth_eq_true_iff]
  exact ⟨hs, center_mem_paperOrderWindow p θ n⟩

/-- For `θ = 1` and `p ≥ 4`, the two distinct orders `p` and `p + 2` lie in the
paper's interval: their traces are `1` and `-1`, and `1 ≤ 3p`.  Thus the
central window has positive width and is not a zero-width point window. -/
theorem paperOrderWindow_two_orders_at_one {p : ℕ → ℕ} {n : ℕ}
    (hp : 4 ≤ p n) :
    PaperOrderWindow p 1 n (p n) ∧ PaperOrderWindow p 1 n (p n + 2) := by
  have hpR : (4 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast hp
  have h3 : (1 : ℝ) ≤ 3 * (p n : ℝ) := by nlinarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (3 * (p n : ℝ)) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (3 * (p n : ℝ)) := Real.sqrt_le_sqrt h3
  have h41 : (4 : ℝ) - 1 = 3 := by norm_num
  constructor
  · unfold PaperOrderWindow
    rw [h41]
    have h1 : ((p n : ℝ) - ((p n : ℝ) + 1)) = -1 := by ring
    rw [h1, abs_neg, abs_one]
    simpa using hsqrt
  · unfold PaperOrderWindow
    rw [h41]
    have h1 : (((p n + 2 : ℕ) : ℝ) - ((p n : ℝ) + 1)) = 1 := by
      push_cast
      ring
    rw [h1, abs_one]
    simpa using hsqrt

/-- The squared central window at `θ = 1` contains two distinct orders when
`p ≥ 4`; this is the explicit non-zero-window check. -/
theorem centralWindow_two_orders_at_one {p : ℕ → ℕ} {n : ℕ}
    (hp : 4 ≤ p n) :
    ∃ j₁ j₂ : ℕ, j₁ ≠ j₂ ∧
      InCentralWindow p 1 n j₁ ∧ InCentralWindow p 1 n j₂ := by
  obtain ⟨h1, h2⟩ := paperOrderWindow_two_orders_at_one hp
  have hθ : (1 : ℝ) ≤ 4 := by norm_num
  refine ⟨p n, p n + 2, by omega, ?_, ?_⟩
  · exact (paperOrderWindow_iff_centralWindow hθ).mp h1
  · exact (paperOrderWindow_iff_centralWindow hθ).mp h2

/-! ## Axiom audit -/

#print axioms paperSmooth_eq_true_iff
#print axioms windowSmooth_eq_true_iff
#print axioms paperSmooth_subset
#print axioms windowSmooth_subset
#print axioms hasseTrace_cast
#print axioms paperOrderWindow_iff_centralWindow
#print axioms paperSmoothOrder_iff_smooth_and_central
#print axioms paperSmooth_eq_true_iff_centralWindow
#print axioms paperSmooth_eq_windowSmooth
#print axioms centralTraceWindow_paperSmooth
#print axioms centralTraceWindow_paperSmooth_of_inputs
#print axioms centralTraceWindow_of_eq_paperSmooth
#print axioms centralTraceWindow_windowSmooth
#print axioms hurwitzDiscriminantScale_paperSmooth
#print axioms centralTrace_paperSmooth_one
#print axioms hurwitzDiscriminantScale_paperSmooth_one
#print axioms centralTraceWindow_iff_windowSmooth_eq
#print axioms centralTraceWindow_iff_exists_windowSmooth
#print axioms centralTraceWindow_iff_exists_paperSmooth
#print axioms paperSmooth_eq_smooth_iff
#print axioms center_mem_paperOrderWindow
#print axioms center_mem_centralWindow
#print axioms paperSmooth_center
#print axioms paperOrderWindow_two_orders_at_one
#print axioms centralWindow_two_orders_at_one

end

end Cogentic.RandomizedL27Window
