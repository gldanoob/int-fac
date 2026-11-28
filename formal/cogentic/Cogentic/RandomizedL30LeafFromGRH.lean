import Cogentic.RandomizedL30SmoothDensity
import Cogentic.RandomizedPaperEndpointWave14

set_option maxHeartbeats 4000000

/-!
# L30: the eventual leaf built from the GRH density theorem

`Cogentic/RandomizedL30SmoothDensity.lean` proves, under
`DirichletLZerosOnLine` and the elementary growth hypothesis
`PaperDensityGrowth p`, the *eventual* paper-scale statements

* `eventually_paperDensity_binCount`, a lower bound on the explicit
  `centeredBinProducts` count, and
* `eventually_younisOddGlobalLower_paper`, the global odd smooth lower bound
  with constant `1/8`.

The paper-scale statements are asymptotic, so every field of the leaf built
here is stated with `∀ᶠ n in atTop`.  The file records precisely:

1. what the prime-bin count really gives: a *global* odd short count
   (`eventually_paperGlobalShortCount_of_binCount`);
2. why it does **not** give the central short count `YounisOddPaperShortCount`
   through the available containment reduction at the paper schedule: the
   doubled bin strip of `eventually_paperDensity_binCount` starts below the
   central interval
   `(p² - p^{3/2}/2, p²]`.  The obstruction is formalised as
   `paperSchedule_centralPlacement_false`; consequently the central count is
   kept as an explicit field and the exact reduction
   `eventually_paperShortCount_of_binCount_and_centralPlacement` isolates the
   missing (in fact false) placement premise;
3. the global upper density as the smallest explicit eventual upper-density
   proposition `EventuallyGlobalOddUpperDensity`, with the parity special case
   `EventuallyGlobalOddUpperDensity (3/8)` proved only under
   `(1+ε)t ≤ 0` (the parity hypotheses are inconsistent with the paper
   regime, so this is not the paper-scale upper bound);
4. the eventual leaf record `EventuallyL30Counts` / `EventuallyL30Inputs`,
   whose ledger loss is the actual H.3 failure probability, and the minimal
   adapters to the Wave-13/Wave-14 L30 leaves.  The adapters realise eventual
   statements as pointwise ones by shifting the index: if `P` holds eventually
   then `fun n => P (n + N)` holds everywhere.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss or
error is set to zero.
-/

namespace Cogentic.RandomizedL30LeafFromGRH

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Relative
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.Randomized
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperEndpointWave14

noncomputable section

/-! ## 1. Eventual forms of the L30 counting predicates -/

/-- The eventual paper-scale central short count. -/
def EventuallyYounisOddPaperShortCount (c : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) ≤
      centralOddSmoothCount p t err n

/-- The eventual paper-scale short count for the **global** odd smooth count.
This is the honest global analogue of `EventuallyYounisOddPaperShortCount`; the
prime-bin strip of `eventually_paperDensity_binCount` lives in the global range,
not in the central interval. -/
def EventuallyYounisOddPaperGlobalShortCount (c : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) ≤
      globalOddSmoothCount p t err n

/-- The eventual paper-scale interval-length form of the short count. -/
def EventuallyYounisOddPaperIntervalCount (c : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * ((centralOrderInterval p n).card : ℝ) *
      Real.exp (-(1 + err n) * t n) ≤ centralOddSmoothCount p t err n

/-- The eventual relative short-interval density. -/
def EventuallyYounisOddRelativeShortInterval (A : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop,
    A * ((centralOrderInterval p n).card : ℝ) *
      (globalOddSmoothCount p t err n / p n ^ 2) ≤
        centralOddSmoothCount p t err n

/-- The eventual odd central count. -/
def EventuallyYounisOddCentralCount (p t err : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop,
    p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) ≤
      centralOddSmoothCount p t err n

/-- **The smallest explicit eventual upper-density proposition.**  The global
odd smooth density is at most `C exp (-(1+ε)t)` along a tail.  This is exactly
the upper companion consumed by `paperRelative_of_globalUpper`; it is stated
separately so that the leaf reports it as a field rather than hiding it. -/
def EventuallyGlobalOddUpperDensity (C : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop,
    globalOddSmoothCount p t err n / p n ^ 2 ≤
      C * Real.exp (-(1 + err n) * t n)

/-- The eventual form of the explicit binomial lower bound. -/
def EventuallyGlobalOddBinomialCount (B : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop,
    2 ≤ smoothCutoff t err n ∧
      ∃ (P : Finset ℕ) (k : ℕ),
        (∀ q ∈ P, q.Prime ∧ q ≠ 2 ∧ (q : ℝ) ≤ smoothCutoff t err n) ∧
        2 * (smoothCutoff t err n) ^ k ≤ p n ^ 2 ∧
        B * p n ^ 2 * Real.exp (-(1 + err n) * t n) ≤
          ((P.card.choose k : ℕ) : ℝ)

/-! ## 2. Eventual monotonicity and reductions -/

/-- Monotonicity of the eventual global lower bound in its constant. -/
theorem eventuallyYounisOddGlobalLower_mono {B B' : ℝ} {p t err : ℕ → ℝ}
    (hBB : B' ≤ B) (h : EventuallyYounisOddGlobalLower B p t err) :
    EventuallyYounisOddGlobalLower B' p t err := by
  filter_upwards [h] with n hn
  have hscale : (0 : ℝ) ≤ p n ^ 2 * Real.exp (-(1 + err n) * t n) := by
    positivity
  calc
    B' * p n ^ 2 * Real.exp (-(1 + err n) * t n)
        = B' * (p n ^ 2 * Real.exp (-(1 + err n) * t n)) := by ring
    _ ≤ B * (p n ^ 2 * Real.exp (-(1 + err n) * t n)) :=
        mul_le_mul_of_nonneg_right hBB hscale
    _ = B * p n ^ 2 * Real.exp (-(1 + err n) * t n) := by ring
    _ ≤ globalOddSmoothCount p t err n := hn

/-- **The global lower at the paper scale**, re-exported from the GRH density
module.  This is unconditional under `DirichletLZerosOnLine` and
`PaperDensityGrowth`. -/
theorem eventually_younisOddGlobalLower_paper_eighth
    (line : DirichletLZerosOnLine) (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    EventuallyYounisOddGlobalLower (1 / 8) p (paperT p) (paperError ε) :=
  eventually_younisOddGlobalLower_paper line p h hε

/-- Any constant `B ≤ 1/8` inherits the paper-scale global lower bound. -/
theorem eventually_younisOddGlobalLower_paper_of_le
    (line : DirichletLZerosOnLine) (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε B : ℝ} (hε : 0 < ε) (hB : B ≤ 1 / 8) :
    EventuallyYounisOddGlobalLower B p (paperT p) (paperError ε) :=
  eventuallyYounisOddGlobalLower_mono hB
    (eventually_younisOddGlobalLower_paper_eighth line p h hε)

/-- Eventual form of the paper short-count to interval-count reduction. -/
theorem eventually_paperIntervalCount_of_eventuallyPaperShortCount
    {c : ℝ} {p t err : ℕ → ℝ} (hp : ∀ᶠ n in atTop, 2 ≤ p n)
    (h : EventuallyYounisOddPaperShortCount c p t err) :
    EventuallyYounisOddPaperIntervalCount c p t err := by
  filter_upwards [h, hp] with n hn hpn
  have hK := centralOrderInterval_card_le_three_halves (p := p) (n := n) hpn
  have he : (0 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := (Real.exp_pos _).le
  have hI : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  by_cases hc : 0 ≤ c
  · have hmul : c * ((centralOrderInterval p n).card : ℝ) ≤
        c * p n ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hK hc
    exact (mul_le_mul_of_nonneg_right hmul he).trans hn
  · have hc' : c < 0 := lt_of_not_ge hc
    have hleft : c * ((centralOrderInterval p n).card : ℝ) *
        Real.exp (-(1 + err n) * t n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc'.le hI) he
    have hright : (0 : ℝ) ≤ centralOddSmoothCount p t err n := by
      unfold centralOddSmoothCount
      positivity
    exact hleft.trans hright

/-- Eventual form of `paperRelative_of_globalUpper`. -/
theorem eventually_paperRelative_of_eventuallyUpper
    {A c C : ℝ} {p t err : ℕ → ℝ}
    (hA : 0 ≤ A) (hAC : A * C ≤ c)
    (hcount : EventuallyYounisOddPaperIntervalCount c p t err)
    (hupper : EventuallyGlobalOddUpperDensity C p t err) :
    EventuallyYounisOddRelativeShortInterval A p t err := by
  filter_upwards [hcount, hupper] with n hcn hun
  have hI : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  have he : (0 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := (Real.exp_pos _).le
  have hstep1 : A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p t err n / p n ^ 2) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (C * Real.exp (-(1 + err n) * t n)) :=
    mul_le_mul_of_nonneg_left hun (mul_nonneg hA hI)
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
  exact hstep1.trans (hstep2.trans hcn)

/-- Eventual form of the full paper reduction to the odd central count. -/
theorem eventually_centralCount_of_eventuallyUpper_and_lower
    {A B c C : ℝ} {p err : ℕ → ℝ}
    (hp : ∀ᶠ n in atTop, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hAC : A * C ≤ c)
    (hcount : EventuallyYounisOddPaperIntervalCount c p (paperT p) err)
    (hupper : EventuallyGlobalOddUpperDensity C p (paperT p) err)
    (hglob : EventuallyYounisOddGlobalLower B p (paperT p) err) :
    EventuallyYounisOddCentralCount p (paperT p) err := by
  have hrel := eventually_paperRelative_of_eventuallyUpper hA.le hAC hcount hupper
  filter_upwards [hrel, hglob, hp] with n hreln hglobn hpn
  have hp_pos : (0 : ℝ) < p n := by linarith
  have hp2 : (0 : ℝ) < p n ^ 2 := by positivity
  have hcard := centralOrderInterval_card_ge_quarter hpn
  have hdiv : B * exp (-(1 + err n) * paperT p n) ≤
      globalOddSmoothCount p (paperT p) err n / p n ^ 2 := by
    rw [le_div_iff₀ hp2]
    nlinarith [hglobn]
  have hcoef : (0 : ℝ) ≤ A * B * exp (-(1 + err n) * paperT p n) := by positivity
  have hcardmul := mul_le_mul_of_nonneg_left hcard hcoef
  have hABone : (1 : ℝ) ≤ A * B / 4 := by nlinarith
  have hbase : (0 : ℝ) ≤
      p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * paperT p n) := by positivity
  have hbasescale : p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * paperT p n) ≤
      (A * B / 4) *
        (p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * paperT p n)) := by
    calc
      p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * paperT p n)
          = (1 : ℝ) * (p n ^ ((3 : ℝ) / 2) *
              exp (-(1 + err n) * paperT p n)) := by ring
      _ ≤ (A * B / 4) * (p n ^ ((3 : ℝ) / 2) *
              exp (-(1 + err n) * paperT p n)) :=
            mul_le_mul_of_nonneg_right hABone hbase
  have hstep1 : (A * B / 4) * (p n ^ ((3 : ℝ) / 2) *
        exp (-(1 + err n) * paperT p n)) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (B * exp (-(1 + err n) * paperT p n)) := by
    calc
      (A * B / 4) * (p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * paperT p n))
          = (A * B * exp (-(1 + err n) * paperT p n)) *
              (p n ^ ((3 : ℝ) / 2) / 4) := by ring
      _ ≤ (A * B * exp (-(1 + err n) * paperT p n)) *
            ((centralOrderInterval p n).card : ℝ) := hcardmul
      _ = A * ((centralOrderInterval p n).card : ℝ) *
            (B * exp (-(1 + err n) * paperT p n)) := by ring
  have hstep2 : A * ((centralOrderInterval p n).card : ℝ) *
        (B * exp (-(1 + err n) * paperT p n)) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p (paperT p) err n / p n ^ 2) :=
    mul_le_mul_of_nonneg_left hdiv (by positivity)
  exact hbasescale.trans (hstep1.trans (hstep2.trans hreln))

/-! ## 3. The parity upper density is not a paper-scale statement -/

/-- The eventual parity upper density: if `(1+ε)t ≤ 0` eventually, the
unconditional parity bound gives `GlobalOddUpperDensity (3/8)`.  This is the
only unconditional upper density available; it does not apply at the paper
scale, where `(1+ε)t > 0`. -/
theorem eventually_globalOddUpperDensity_of_parity
    {p t err : ℕ → ℝ} (hp : ∀ n, 2 ≤ p n)
    (ht : ∀ᶠ n in atTop, (1 + err n) * t n ≤ 0) :
    EventuallyGlobalOddUpperDensity (3 / 8) p t err := by
  filter_upwards [ht] with n hn
  have hG := globalOddSmoothCount_le_quarter_sq (p := p) (t := t) (err := err) (hp n)
  have hp2 : (0 : ℝ) < p n ^ 2 := by
    have hpos : (0 : ℝ) < p n := by linarith [hp n]
    positivity
  have hp4 : (4 : ℝ) ≤ p n ^ 2 := by
    have h2 : (2 : ℝ) ≤ p n := hp n
    nlinarith [sq_nonneg (p n - 2), h2]
  have hunit : (1 : ℝ) ≤ Real.exp (-(1 + err n) * t n) := by
    have h : Real.exp 0 ≤ Real.exp (-(1 + err n) * t n) :=
      Real.exp_le_exp.mpr (by nlinarith [hn])
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

/-- The paper regime has `(1+ε)t > 0` eventually, so the parity hypothesis
`(1+ε)t ≤ 0` is not available there. -/
theorem eventually_paper_one_add_err_mul_pos
    (p : ℕ → ℝ) (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 0 < (1 + paperError ε n) * paperT p n := by
  filter_upwards [eventually_paperT_pos_of_growth h] with n ht
  have hα : 0 < 1 + paperError ε n := by
    dsimp [paperError]
    linarith
  exact mul_pos hα ht

/-- Consequently the parity upper density is *not* an eventual paper-scale
upper density. -/
theorem not_eventually_paper_one_add_err_mul_nonpos
    (p : ℕ → ℝ) (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ¬ (∀ᶠ n in atTop, (1 + paperError ε n) * paperT p n ≤ 0) := by
  intro hnonpos
  have hpos := eventually_paper_one_add_err_mul_pos p h hε
  have hboth : ∀ᶠ n in atTop,
      0 < (1 + paperError ε n) * paperT p n ∧
        (1 + paperError ε n) * paperT p n ≤ 0 := hpos.and hnonpos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hboth
  exact (not_le_of_gt (hN N le_rfl).1) (hN N le_rfl).2

/-! ## 4. What the prime-bin count gives, and what it does not give -/

/-- **The paper-scale short count for the global odd smooth count.**  This is
the honest consequence of `eventually_paperDensity_binCount`: the bin products
are global odd-half smooth orders, so the global count is at least
`(1/8) p^{3/2} exp (-(1+ε)t)`.  The doubled strip is not contained in the
central interval; see `paperSchedule_centralPlacement_false` below. -/
theorem eventually_paperGlobalShortCount_of_binCount
    (line : DirichletLZerosOnLine) (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    EventuallyYounisOddPaperGlobalShortCount (1 / 8) p (paperT p) (paperError ε) := by
  have hg := eventually_globalOddSmoothCount_paperLower line p h hε
  filter_upwards [hg, h.eventually_sixteen] with n hn hp
  have hp1 : (1 : ℝ) ≤ p n := by linarith
  have h32r : p n ^ ((3 : ℝ) / 2) ≤ p n ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1
      (show ((3 : ℝ) / 2) ≤ 2 by norm_num)
  have h32 : p n ^ ((3 : ℝ) / 2) ≤ p n ^ 2 := by
    simpa using h32r
  have hcoef : (0 : ℝ) ≤
      (1 / 8) * Real.exp (-(1 + ε) * paperT p n) := by positivity
  have hmul : (1 / 8) * Real.exp (-(1 + ε) * paperT p n) *
        p n ^ ((3 : ℝ) / 2) ≤
      (1 / 8) * Real.exp (-(1 + ε) * paperT p n) * p n ^ 2 :=
    mul_le_mul_of_nonneg_left h32 hcoef
  calc
    (1 / 8) * p n ^ ((3 : ℝ) / 2) *
        Real.exp (-(1 + ε) * paperT p n)
        = (1 / 8) * Real.exp (-(1 + ε) * paperT p n) *
            p n ^ ((3 : ℝ) / 2) := by ring
    _ ≤ (1 / 8) * Real.exp (-(1 + ε) * paperT p n) * p n ^ 2 := hmul
    _ = (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) := by ring
    _ ≤ globalOddSmoothCount p (paperT p) (paperError ε) n := hn

/-- **The exact central-placement obstruction.**  At the paper schedule the
bin products satisfy `P^m = p²/4`, so the doubled strip starts at `p²/2`,
whereas the central interval starts at `p² - p^{3/2}/2`.  For `p > 1` the
latter is strictly larger, hence the doubled strip can never be contained in
the central interval.  This is why `eventually_paperDensity_binCount` cannot
imply `YounisOddPaperShortCount` through
`centralOddSmoothCount_lower_of_binCount`, and it is the precise missing
premise kept in `EventuallyL30Counts.short_interval`. -/
theorem paperSchedule_centralPlacement_false {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 1 < p n) (hm : 0 < paperDensityM p ε n) :
    ¬ (p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 <
        2 * paperDensityP p ε n ^ paperDensityM p ε n) := by
  intro h
  have hp0 : 0 < p n := zero_lt_one.trans hp
  rw [paperDensityP_pow hp0 hm] at h
  have h2 : 2 * (p n ^ 2 / 4) = p n ^ 2 / 2 := by ring
  rw [h2] at h
  have hle : p n ^ ((3 : ℝ) / 2) ≤ p n ^ 2 := by
    have hr := Real.rpow_le_rpow_of_exponent_le hp.le
      (show ((3 : ℝ) / 2) ≤ 2 by norm_num)
    simpa using hr
  nlinarith

/-- The paper schedule never satisfies the central placement. -/
theorem not_eventually_paperSchedule_centralPlacement
    (p : ℕ → ℝ) (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ¬ (∀ᶠ n in atTop,
        p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 <
          2 * paperDensityP p ε n ^ paperDensityM p ε n) := by
  intro hplace
  have hu := tendsto_paperDensityU_of_growth h hε
  have hm : ∀ᶠ n in atTop, 0 < paperDensityM p ε n := by
    filter_upwards [eventually_paperDensityU_gt_one_of_tendsto hu] with n hu1
    exact paperDensityM_pos hu1
  have hcomb : ∀ᶠ n in atTop,
      (p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 <
          2 * paperDensityP p ε n ^ paperDensityM p ε n) ∧
        0 < paperDensityM p ε n ∧ 1 < p n :=
    hplace.and (hm.and (h.eventually_sixteen.mono (fun n hn => by linarith)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hcomb
  exact paperSchedule_centralPlacement_false (hN N le_rfl).2.2
    (hN N le_rfl).2.1 (hN N le_rfl).1

/-! ### Eventual schedule facts used by the central reduction -/

/-- `P` is eventually nonnegative at the paper schedule. -/
theorem eventually_paperDensityP_nonneg (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (_hε : 0 < ε) :
    ∀ᶠ n in atTop, 0 ≤ paperDensityP p ε n := by
  filter_upwards [h.eventually_sixteen] with n hp
  exact (paperDensityP_pos (by linarith : 0 < p n)).le

/-- `m` is eventually positive at the paper schedule. -/
theorem eventually_paperDensityM_pos (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 0 < paperDensityM p ε n := by
  have hu := tendsto_paperDensityU_of_growth h hε
  filter_upwards [eventually_paperDensityU_gt_one_of_tendsto hu] with n hu1
  exact paperDensityM_pos hu1

/-- The doubled upper strip is eventually at most `p²`. -/
theorem eventually_paperCentralStrip_upper (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      2 * (paperDensityP p ε n ^ paperDensityM p ε n *
          Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n)) ≤
        p n ^ 2 := by
  have hu := tendsto_paperDensityU_of_growth h hε
  filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
    eventually_paperDensityU_gt_one_of_tendsto hu] with n hp ht hu1
  have hmpos := paperDensityM_pos hu1
  have hJpos := paperDensityJ_pos hmpos
  have hlogu := Real.log_pos hu1
  have hmδ := paperDensityDelta_mul_m_le_log2 hε ht hJpos hlogu
  have hstrip := paperDensity_strip_upper (by linarith : 0 < p n) hmpos hmδ
  nlinarith

/-- The lower bin endpoint is eventually at least `3`. -/
theorem eventually_paperBin_lower (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (3 : ℝ) ≤ paperDensityP p ε n *
        Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) := by
  have hu := tendsto_paperDensityU_of_growth h hε
  have ht := tendsto_paperT_of_growth h
  have hlarge : ∀ᶠ n in atTop,
      Real.log 3 + Real.log 4 ≤
        (1 / 2) * ((1 + ε) * paperT p n) *
          (1 - 1 / Real.log (paperDensityU p ε n)) := by
    filter_upwards [ht.eventually_ge_atTop (4 * (Real.log 3 + Real.log 4)),
      hu.eventually_ge_atTop (Real.exp 2)] with n htbig hubig
    have hlogu2 : 2 ≤ Real.log (paperDensityU p ε n) := by
      have hlog := Real.log_le_log (Real.exp_pos 2) hubig
      rwa [Real.log_exp] at hlog
    have hinv : 1 / Real.log (paperDensityU p ε n) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogu2
    have hα1 : 1 ≤ 1 + ε := by linarith [hε.le]
    have htpos : 0 < paperT p n := by
      have hpos : 0 < 4 * (Real.log 3 + Real.log 4) := by positivity
      linarith
    have hαt : 4 * (Real.log 3 + Real.log 4) ≤ (1 + ε) * paperT p n := by
      have htle : paperT p n ≤ (1 + ε) * paperT p n := by
        nlinarith [hε.le, htpos.le]
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / Real.log (paperDensityU p ε n) := by
      linarith
    have hnonneg : 0 ≤ (1 / 2) * ((1 + ε) * paperT p n) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hhalf hnonneg, hαt]
  filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
    eventually_paperDensityU_gt_one_of_tendsto hu,
    eventually_paperDensityM_le_two_u_of_growth h hε,
    hu.eventually_ge_atTop (Real.exp 2), hlarge] with n hp ht hu1 hm2 hubig hlarge_n
  have hmpos := paperDensityM_pos hu1
  have hJpos := paperDensityJ_pos hmpos
  have hlogu2 : 2 ≤ Real.log (paperDensityU p ε n) := by
    have hlog := Real.log_le_log (Real.exp_pos 2) hubig
    rwa [Real.log_exp] at hlog
  exact paperDensity_bin_lower (by linarith : 0 < p n) (by linarith : 1 < p n)
    hmpos hm2 hlogu2 ht hε hJpos hlarge_n

/-- The upper bin endpoint is eventually at most the paper cutoff. -/
theorem eventually_paperBin_upper (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      paperDensityP p ε n *
        Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) ≤
          paperDensityY p ε n := by
  have hu := tendsto_paperDensityU_of_growth h hε
  filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
    eventually_paperDensityU_gt_one_of_tendsto hu,
    hu.eventually_ge_atTop (Real.exp 1)] with n hp ht hu1 hubig
  have hlogu1 : 1 ≤ Real.log (paperDensityU p ε n) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hubig
    rwa [Real.log_exp] at hlog
  have hmpos := paperDensityM_pos hu1
  have hJpos := paperDensityJ_pos hmpos
  exact paperDensity_bin_upper (by linarith : 1 < p n) hmpos
    (paperDensityU_mul_le_M p ε n) hlogu1 ht hε hJpos

/-- The paper cutoff is eventually at least `2`. -/
theorem eventually_paperSmoothCutoff_ge_two (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 2 ≤ smoothCutoff (paperT p) (paperError ε) n := by
  filter_upwards [eventually_paperT_pos_of_growth h,
    (tendsto_paperT_of_growth h).eventually_ge_atTop 1] with n ht ht1
  dsimp [smoothCutoff, paperError]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hαt : (1 : ℝ) ≤ (1 + ε) * paperT p n := by nlinarith [hε.le, ht1]
  nlinarith [Real.log_two_lt_d9]

/-! ### The conditional central short count -/

/-- **The prime-bin count plus the central placement gives the central short
count.**  Every hypothesis except `hplace` is the eventual paper schedule
proved above; `hplace` is exactly the missing lower placement of the doubled
strip (the upper placement, the odd floors and the smoothness of the bins are
proved above).  Since `not_eventually_paperSchedule_centralPlacement` shows
that `hplace` is *false* for the paper schedule, this theorem isolates the
precise gap in this route. -/
theorem eventually_paperShortCount_of_binCount_and_centralPlacement
    (line : DirichletLZerosOnLine) (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε)
    (hplace : ∀ᶠ n in atTop,
      p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 <
        2 * paperDensityP p ε n ^ paperDensityM p ε n) :
    EventuallyYounisOddPaperShortCount (1 / 8) p (paperT p) (paperError ε) := by
  have hbin := eventually_paperDensity_binCount line p h hε
  have hP := eventually_paperDensityP_nonneg p h hε
  have hk := eventually_paperDensityM_pos p h hε
  have hhi := eventually_paperCentralStrip_upper p h hε
  have hlo := eventually_paperBin_lower p h hε
  have hup := eventually_paperBin_upper p h hε
  have hy2 := eventually_paperSmoothCutoff_ge_two p h hε
  have htpos := eventually_paperT_pos_of_growth h
  have hu1 := eventually_paperDensityU_gt_one_of_tendsto
    (tendsto_paperDensityU_of_growth h hε)
  have hsixteen := h.eventually_sixteen
  filter_upwards [hbin, hplace, hP, hk, hhi, hlo, hup, hy2, htpos, hu1, hsixteen]
    with n hbn hpl hPn hkn hhin hlon hupn hy2n htn hu1n h16n
  obtain ⟨a, ha, hcount⟩ := hbn
  have hJpos : 0 < paperDensityJ p ε n := paperDensityJ_pos hkn
  have hlogu : 0 < Real.log (paperDensityU p ε n) := Real.log_pos hu1n
  have hδnonneg : 0 ≤ paperDensityDelta p ε n :=
    (paperDensityDelta_pos hε htn hJpos hlogu).le
  have hmposR : (0 : ℝ) < (paperDensityM p ε n : ℝ) := by exact_mod_cast hkn
  -- Odd floors.
  have hodd : ∀ j < paperDensityJ p ε n,
      3 ≤ centeredBinFloor (paperDensityP p ε n)
        (paperDensityDelta p ε n) a (paperDensityM p ε n) j := by
    intro j hj
    have ha_le : (a : ℝ) / (paperDensityM p ε n : ℝ) ≤
        (paperDensityJ p ε n : ℝ) := by
      have ha1 : a ≤ paperDensityM p ε n * (paperDensityJ p ε n - 1) :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have ha2 : a ≤ paperDensityJ p ε n * paperDensityM p ε n := by
        rw [Nat.mul_comm]
        exact ha1.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      rw [div_le_iff₀ hmposR]
      exact_mod_cast ha2
    have hle_endpoint : paperDensityP p ε n *
        Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) ≤
          centeredBinEndpoint (paperDensityP p ε n)
            (paperDensityDelta p ε n) a (paperDensityM p ε n) j := by
      unfold centeredBinEndpoint
      apply mul_le_mul_of_nonneg_left _ hPn
      apply Real.exp_le_exp.mpr
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith [hj0, ha_le, hδnonneg]
    exact Nat.le_floor (hlon.trans hle_endpoint)
  -- Upper floors below the cutoff.
  have hfloor : ∀ j < paperDensityJ p ε n,
      (centeredBinFloor (paperDensityP p ε n) (paperDensityDelta p ε n) a
        (paperDensityM p ε n) (j + 1) : ℝ) ≤
      smoothCutoff (paperT p) (paperError ε) n := by
    intro j hj
    have hj1 : ((j + 1 : ℕ) : ℝ) ≤ (paperDensityJ p ε n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hj)
    have hle_endpoint : centeredBinEndpoint (paperDensityP p ε n)
        (paperDensityDelta p ε n) a (paperDensityM p ε n) (j + 1) ≤
          paperDensityP p ε n *
            Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) := by
      unfold centeredBinEndpoint
      apply mul_le_mul_of_nonneg_left _ hPn
      apply Real.exp_le_exp.mpr
      have ha_nonneg : 0 ≤ (a : ℝ) / (paperDensityM p ε n : ℝ) := by positivity
      nlinarith [hj1, ha_nonneg, hδnonneg]
    have hfloor_le : ((centeredBinFloor (paperDensityP p ε n)
        (paperDensityDelta p ε n) a (paperDensityM p ε n) (j + 1) : ℕ) : ℝ) ≤
          centeredBinEndpoint (paperDensityP p ε n)
            (paperDensityDelta p ε n) a (paperDensityM p ε n) (j + 1) :=
      Nat.floor_le (mul_nonneg hPn (Real.exp_pos _).le)
    have hcut : smoothCutoff (paperT p) (paperError ε) n = paperDensityY p ε n :=
      (paperDensityY_eq_smoothCutoff p ε).symm ▸ rfl
    rw [hcut]
    exact hfloor_le.trans (hle_endpoint.trans hupn)
  -- Scale the `p²` count down to `p^{3/2}`.
  have hp1 : (1 : ℝ) ≤ p n := by linarith
  have h32r : p n ^ ((3 : ℝ) / 2) ≤ p n ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1
      (show ((3 : ℝ) / 2) ≤ 2 by norm_num)
  have h32 : p n ^ ((3 : ℝ) / 2) ≤ p n ^ 2 := by
    simpa using h32r
  have hexp : (0 : ℝ) ≤ Real.exp (-(1 + ε) * paperT p n) := (Real.exp_pos _).le
  have hcount' : (1 / 8) * p n ^ ((3 : ℝ) / 2) *
        Real.exp (-(1 + ε) * paperT p n) ≤
      ((centeredBinProducts (paperDensityP p ε n)
        (paperDensityDelta p ε n) (paperDensityJ p ε n)
        (paperDensityM p ε n) a).card : ℝ) := by
    have hmul : (1 / 8) * Real.exp (-(1 + ε) * paperT p n) *
          p n ^ ((3 : ℝ) / 2) ≤
        (1 / 8) * Real.exp (-(1 + ε) * paperT p n) * p n ^ 2 :=
      mul_le_mul_of_nonneg_left h32
        (by positivity : (0 : ℝ) ≤
          (1 / 8) * Real.exp (-(1 + ε) * paperT p n))
    calc
      (1 / 8) * p n ^ ((3 : ℝ) / 2) *
          Real.exp (-(1 + ε) * paperT p n)
          = (1 / 8) * Real.exp (-(1 + ε) * paperT p n) *
              p n ^ ((3 : ℝ) / 2) := by ring
      _ ≤ (1 / 8) * Real.exp (-(1 + ε) * paperT p n) * p n ^ 2 := hmul
      _ = (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) := by ring
      _ ≤ ((centeredBinProducts (paperDensityP p ε n)
        (paperDensityDelta p ε n) (paperDensityJ p ε n)
        (paperDensityM p ε n) a).card : ℝ) := hcount
  exact centralOddSmoothCount_lower_of_binCount hPn hkn hodd hpl hhin hfloor hy2n hcount'

/-- Transport an eventual predicate to a pointwise predicate by shifting the
index.  This is the minimal adapter used to feed the pointwise Wave-13/Wave-14
records from eventual statements. -/
theorem exists_shift_atTop {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) :
    ∃ N, ∀ n, P (n + N) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  exact ⟨N, fun n => hN (n + N) (Nat.le_add_left N n)⟩

/-- The shift extracted from an eventual predicate. -/
noncomputable def eventuallyShift {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) : ℕ :=
  Classical.choose (exists_shift_atTop h)

/-- The defining property of `eventuallyShift`. -/
theorem eventuallyShift_spec {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) (n : ℕ) :
    P (n + eventuallyShift h) :=
  Classical.choose_spec (exists_shift_atTop h) n

/-! ## 5. The eventual L30 leaf record -/

/-- **The eventual L30 counting leaf.**  Every counting field is a tail
statement.  The global lower bound is the one supplied by the GRH density
theorem; the central short count and the global upper density are explicit
fields.  There is no LPP field: the canonical LPP fibre family and the
logarithmic normalization are unconditional and are inserted by the adapters
below. -/
structure EventuallyL30Counts where
  /-- The prime whose genus-two order is counted. -/
  p : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The prime is eventually at least two. -/
  p_ge_two : ∀ᶠ n in atTop, 2 ≤ p n
  /-- The relative error is eventually at least `-1`. -/
  err_ge_neg_one : ∀ᶠ n in atTop, -1 ≤ err n
  /-- The relative short-interval density constant. -/
  A : ℝ
  /-- The global smooth lower-bound constant. -/
  B : ℝ
  /-- The paper short-count constant. -/
  c : ℝ
  /-- The global odd upper-density constant. -/
  C : ℝ
  /-- `A > 0`. -/
  A_pos : 0 < A
  /-- `B > 0`. -/
  B_pos : 0 < B
  /-- The arithmetic relation `A B ≥ 4`. -/
  AB_ge_four : 4 ≤ A * B
  /-- The paper count dominates the relative density constant. -/
  AC_le : A * C ≤ c
  /-- **The paper-scale central short count**, eventual. -/
  short_interval : EventuallyYounisOddPaperShortCount c p (paperT p) err
  /-- **The global odd smooth upper density**, eventual. -/
  global_upper : EventuallyGlobalOddUpperDensity C p (paperT p) err
  /-- **The global odd smooth lower bound**, eventual.  This is unconditional
  under `DirichletLZerosOnLine` and `PaperDensityGrowth`. -/
  global_lower : EventuallyYounisOddGlobalLower B p (paperT p) err

namespace EventuallyL30Counts

variable (S : EventuallyL30Counts)

/-- The consistency `B ≤ C` forced by the two eventual density bounds. -/
theorem B_le_C : S.B ≤ S.C := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (S.p_ge_two.and (S.global_lower.and S.global_upper))
  have hpN : 2 ≤ S.p N := (hN N le_rfl).1
  have hl : S.B * S.p N ^ 2 *
      Real.exp (-(1 + S.err N) * paperT S.p N) ≤
        globalOddSmoothCount S.p (paperT S.p) S.err N := (hN N le_rfl).2.1
  have hu : globalOddSmoothCount S.p (paperT S.p) S.err N / S.p N ^ 2 ≤
      S.C * Real.exp (-(1 + S.err N) * paperT S.p N) := (hN N le_rfl).2.2
  have hp0 : 0 < S.p N := by linarith
  have hp2 : 0 < S.p N ^ 2 := by positivity
  have hX : 0 < S.p N ^ 2 *
      Real.exp (-(1 + S.err N) * paperT S.p N) := by positivity
  have hl' : S.B * (S.p N ^ 2 *
      Real.exp (-(1 + S.err N) * paperT S.p N)) ≤
        globalOddSmoothCount S.p (paperT S.p) S.err N := by
    simpa only [mul_assoc] using hl
  have hu' : globalOddSmoothCount S.p (paperT S.p) S.err N ≤
      S.C * (S.p N ^ 2 *
        Real.exp (-(1 + S.err N) * paperT S.p N)) := by
    have h := (div_le_iff₀ hp2).mp hu
    calc globalOddSmoothCount S.p (paperT S.p) S.err N
        ≤ S.C * Real.exp (-(1 + S.err N) * paperT S.p N) * S.p N ^ 2 := h
      _ = S.C * (S.p N ^ 2 *
            Real.exp (-(1 + S.err N) * paperT S.p N)) := by ring
  exact le_of_mul_le_mul_right (hl'.trans hu') hX

/-- **The arithmetic obstruction of the parity upper bound.**  A leaf whose
global lower constant is `1/8`, whose short count constant is at most `1/8`,
and whose upper density is the parity bound `3/8` cannot exist: `B ≤ C`,
`A B ≥ 4` and `A C ≤ c` force `A ≥ 32` and `A ≤ 1`.  Thus the parity upper
density is not a substitute for the paper-scale upper density. -/
theorem not_parity_eighth (hB : S.B = 1 / 8) (_hC : S.C ≤ 3 / 8)
    (hc : S.c ≤ 1 / 8) : False := by
  have hBC := S.B_le_C
  have hA32 : 32 ≤ S.A := by
    have h := S.AB_ge_four
    rw [hB] at h
    nlinarith
  have hCge : (1 : ℝ) / 8 ≤ S.C := by
    rw [← hB]
    exact hBC
  have hACle : S.A * S.C ≤ 1 / 8 := le_trans S.AC_le hc
  have hA8 : S.A * (1 / 8) ≤ S.A * S.C :=
    mul_le_mul_of_nonneg_left hCge S.A_pos.le
  have hAle : S.A ≤ 1 := by nlinarith
  linarith

/-- The paper-scale central short count carried by the leaf. -/
theorem paperShortCount :
    EventuallyYounisOddPaperShortCount S.c S.p (paperT S.p) S.err :=
  S.short_interval

/-- The global odd upper density carried by the leaf. -/
theorem globalUpper :
    EventuallyGlobalOddUpperDensity S.C S.p (paperT S.p) S.err :=
  S.global_upper

/-- The global lower bound carried by the leaf. -/
theorem globalLower :
    EventuallyYounisOddGlobalLower S.B S.p (paperT S.p) S.err :=
  S.global_lower

/-- The eventual relative short-interval density from the leaf's short count
and upper density. -/
theorem younisRelative :
    EventuallyYounisOddRelativeShortInterval S.A S.p (paperT S.p) S.err :=
  eventually_paperRelative_of_eventuallyUpper S.A_pos.le S.AC_le
    (eventually_paperIntervalCount_of_eventuallyPaperShortCount S.p_ge_two
      S.short_interval)
    S.global_upper

/-- The eventual odd central count from the leaf's three counting fields. -/
theorem younisCentralCount :
    EventuallyYounisOddCentralCount S.p (paperT S.p) S.err :=
  eventually_centralCount_of_eventuallyUpper_and_lower S.p_ge_two S.A_pos S.B_pos
    S.AB_ge_four S.AC_le
    (eventually_paperIntervalCount_of_eventuallyPaperShortCount S.p_ge_two
      S.short_interval)
    S.global_upper S.global_lower

/-- **The Wave-13 L30 counts from the eventual leaf.**  The eventual fields are
made pointwise by shifting `p` and `err` by the common threshold.  The LPP
fields are filled unconditionally with the canonical multiples family and the
logarithmic loss. -/
noncomputable def toWave13L30Counts : Wave13L30Counts := by
  classical
  let h := S.p_ge_two.and (S.err_ge_neg_one.and
    (S.short_interval.and (S.global_upper.and S.global_lower)))
  let N := eventuallyShift h
  let P : ℕ → ℝ := fun n => S.p (n + N)
  let E : ℕ → ℝ := fun n => S.err (n + N)
  have hspec : ∀ n,
      (2 ≤ S.p (n + N)) ∧ (-1 ≤ S.err (n + N)) ∧
        (S.c * S.p (n + N) ^ ((3 : ℝ) / 2) *
            Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N)) ≤
          centralOddSmoothCount S.p (paperT S.p) S.err (n + N)) ∧
        (globalOddSmoothCount S.p (paperT S.p) S.err (n + N) /
            S.p (n + N) ^ 2 ≤
          S.C * Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N))) ∧
        (S.B * S.p (n + N) ^ 2 *
            Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N)) ≤
          globalOddSmoothCount S.p (paperT S.p) S.err (n + N)) := by
    intro n
    have h' := eventuallyShift_spec h n
    simpa only [h] using h'
  refine
    { p := P
      err := E
      p_ge_two := fun n => (hspec n).1
      fibreModels := fun n m => lppModelMultiples P n m
      Q := lppLogLoss P
      A := S.A
      B := S.B
      c := S.c
      C := S.C
      A_pos := S.A_pos
      B_pos := S.B_pos
      AB_ge_four := S.AB_ge_four
      AC_le := S.AC_le
      short_interval := ?_
      global_upper := ?_
      global_lower := ?_
      lpp_normalization := ?_
      lpp_raw := ?_ }
  · intro n
    have hs := (hspec n).2.2.1
    change S.c * S.p (n + N) ^ ((3 : ℝ) / 2) *
        Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N)) ≤
      centralOddSmoothCount S.p (paperT S.p) S.err (n + N)
    exact hs
  · intro n
    have hu := (hspec n).2.2.2.1
    change globalOddSmoothCount S.p (paperT S.p) S.err (n + N) /
        S.p (n + N) ^ 2 ≤
      S.C * Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N))
    exact hu
  · intro n
    have hl := (hspec n).2.2.2.2
    change S.B * S.p (n + N) ^ 2 *
        Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N)) ≤
      globalOddSmoothCount S.p (paperT S.p) S.err (n + N)
    exact hl
  · exact lpp_normalization_logLoss (p := P) (t := paperT P) (err := E)
      (fun n => (hspec n).1) (fun n => Real.sqrt_nonneg _)
      (fun n => (hspec n).2.1)
  · exact lppRawLogModelCount_of_superset (p := P) (t := paperT P) (err := E)
      (fibreModels := fun n m => lppModelMultiples P n m)
      (fun n => (hspec n).1) (fun n m hm => subset_rfl)

/-- **The Wave-14 L30 counts from the eventual leaf**, given the eventual
explicit binomial lower bound.  The latter is the only field not supplied by the
GRH density theorem; in the Wave-14 record it replaces `global_lower`. -/
noncomputable def toWave14L30Counts
    (hbin : EventuallyGlobalOddBinomialCount S.B S.p (paperT S.p) S.err) :
    Wave14L30Counts := by
  classical
  let h := S.p_ge_two.and (S.err_ge_neg_one.and
    (S.short_interval.and (S.global_upper.and (S.global_lower.and hbin))))
  let N := eventuallyShift h
  let P : ℕ → ℝ := fun n => S.p (n + N)
  let E : ℕ → ℝ := fun n => S.err (n + N)
  have hspec : ∀ n,
      (2 ≤ S.p (n + N)) ∧ (-1 ≤ S.err (n + N)) ∧
        (S.c * S.p (n + N) ^ ((3 : ℝ) / 2) *
            Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N)) ≤
          centralOddSmoothCount S.p (paperT S.p) S.err (n + N)) ∧
        (globalOddSmoothCount S.p (paperT S.p) S.err (n + N) /
            S.p (n + N) ^ 2 ≤
          S.C * Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N))) ∧
        (S.B * S.p (n + N) ^ 2 *
            Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N)) ≤
          globalOddSmoothCount S.p (paperT S.p) S.err (n + N)) ∧
        (2 ≤ smoothCutoff (paperT S.p) S.err (n + N) ∧
          ∃ (Pset : Finset ℕ) (k : ℕ),
            (∀ q ∈ Pset, q.Prime ∧ q ≠ 2 ∧
              (q : ℝ) ≤ smoothCutoff (paperT S.p) S.err (n + N)) ∧
            2 * (smoothCutoff (paperT S.p) S.err (n + N)) ^ k ≤
              S.p (n + N) ^ 2 ∧
            S.B * S.p (n + N) ^ 2 *
              Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N)) ≤
                ((Pset.card.choose k : ℕ) : ℝ)) := by
    intro n
    have h' := eventuallyShift_spec h n
    simpa only [h] using h'
  refine
    { p := P
      err := E
      p_ge_two := fun n => (hspec n).1
      err_ge_neg_one := fun n => (hspec n).2.1
      fibreModels := fun n m => lppModelMultiples P n m
      A := S.A
      B := S.B
      c := S.c
      C := S.C
      A_pos := S.A_pos
      B_pos := S.B_pos
      AB_ge_four := S.AB_ge_four
      AC_le := S.AC_le
      short_interval := ?_
      global_upper := ?_
      global_binomial := ?_
      lpp_superset := fun n m hm => subset_rfl }
  · intro n
    have hs := (hspec n).2.2.1
    change S.c * S.p (n + N) ^ ((3 : ℝ) / 2) *
        Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N)) ≤
      centralOddSmoothCount S.p (paperT S.p) S.err (n + N)
    exact hs
  · intro n
    have hu := (hspec n).2.2.2.1
    change globalOddSmoothCount S.p (paperT S.p) S.err (n + N) /
        S.p (n + N) ^ 2 ≤
      S.C * Real.exp (-(1 + S.err (n + N)) * paperT S.p (n + N))
    exact hu
  · intro n
    exact (hspec n).2.2.2.2.2

/-- The reverse adapter: a pointwise Wave-13 counts record together with the
eventual relative-error bound gives an eventual leaf.  This shows the eventual
record is inhabited whenever the Wave-13 record is (for example, by the
constant-scale witness of `RandomizedL30CountsNonvacuous`). -/
noncomputable def ofWave13L30Counts (S : Wave13L30Counts)
    (herr : ∀ᶠ n in atTop, -1 ≤ S.err n) : EventuallyL30Counts where
  p := S.p
  err := S.err
  p_ge_two := Filter.Eventually.of_forall S.p_ge_two
  err_ge_neg_one := herr
  A := S.A
  B := S.B
  c := S.c
  C := S.C
  A_pos := S.A_pos
  B_pos := S.B_pos
  AB_ge_four := S.AB_ge_four
  AC_le := S.AC_le
  short_interval := Filter.Eventually.of_forall S.short_interval
  global_upper := Filter.Eventually.of_forall S.global_upper
  global_lower := Filter.Eventually.of_forall S.global_lower

/-- The reverse adapter from a pointwise Wave-14 counts record.  The global
lower bound is obtained from the explicit binomial count. -/
noncomputable def ofWave14L30Counts (S : Wave14L30Counts) : EventuallyL30Counts where
  p := S.p
  err := S.err
  p_ge_two := Filter.Eventually.of_forall S.p_ge_two
  err_ge_neg_one := Filter.Eventually.of_forall S.err_ge_neg_one
  A := S.A
  B := S.B
  c := S.c
  C := S.C
  A_pos := S.A_pos
  B_pos := S.B_pos
  AB_ge_four := S.AB_ge_four
  AC_le := S.AC_le
  short_interval := Filter.Eventually.of_forall S.short_interval
  global_upper := Filter.Eventually.of_forall S.global_upper
  global_lower := Filter.Eventually.of_forall
    (younisOddGlobalLower_of_binomialCount S.global_binomial)

end EventuallyL30Counts

/-- **The eventual L30 inputs.**  The loss is the actual H.3 failure probability
`failure.failure`, not a count or a zero. -/
structure EventuallyL30Inputs where
  /-- The eventual counting data. -/
  counts : EventuallyL30Counts
  /-- The Cantor/H.5 cost and correctness data. -/
  cantor : CantorCostInputs
  /-- The H.3 failure data, including the useful-prime split bound. -/
  failure : FailureData

namespace EventuallyL30Inputs

variable (I : EventuallyL30Inputs)

/-- The ledger leaf: the actual failure probability. -/
noncomputable def toSubexpLeaf : Cogentic.RandomizedPaperLeafStatements.SubexpLeaf :=
  I.failure.toSubexpLeaf

/-- **The leaf loss is the actual failure probability.** -/
theorem loss_eq (n : ℕ) : I.toSubexpLeaf.loss n = I.failure.failure n := rfl

/-- The leaf loss is nonnegative. -/
theorem loss_nonneg (n : ℕ) : 0 ≤ I.toSubexpLeaf.loss n :=
  FailureData.loss_nonneg I.failure n

/-- The Wave-13 L30 leaf from the eventual record. -/
noncomputable def toWave13L30Inputs : Wave13L30Inputs where
  counts := I.counts.toWave13L30Counts
  cantor := I.cantor
  failure := I.failure

/-- The Wave-13 ledger loss is the actual failure probability. -/
theorem toWave13L30Inputs_loss_eq (n : ℕ) :
    I.toWave13L30Inputs.toSubexpLeaf.loss n = I.failure.failure n := rfl

/-- The Wave-14 L30 leaf from the eventual record, given the eventual explicit
binomial lower bound. -/
noncomputable def toWave14L30Inputs
    (hbin : EventuallyGlobalOddBinomialCount I.counts.B I.counts.p
      (paperT I.counts.p) I.counts.err) : Wave14L30Inputs where
  counts := I.counts.toWave14L30Counts hbin
  cantor := I.cantor
  failure := I.failure

/-- The Wave-14 ledger loss is the actual failure probability. -/
theorem toWave14L30Inputs_loss_eq
    (hbin : EventuallyGlobalOddBinomialCount I.counts.B I.counts.p
      (paperT I.counts.p) I.counts.err) (n : ℕ) :
    (I.toWave14L30Inputs hbin).toSubexpLeaf.loss n = I.failure.failure n := rfl

/-- The reverse adapter: a pointwise Wave-14 input record gives an eventual
input record with the same failure data.  Combined with the non-vacuity witness
of `RandomizedL30CountsNonvacuous`, this shows the eventual input record is
inhabited. -/
noncomputable def ofWave14L30Inputs (I : Wave14L30Inputs) : EventuallyL30Inputs where
  counts := EventuallyL30Counts.ofWave14L30Counts I.counts
  cantor := I.cantor
  failure := I.failure

/-- The reverse adapter preserves the actual failure probability. -/
theorem ofWave14L30Inputs_loss_eq (I : Wave14L30Inputs) (n : ℕ) :
    (ofWave14L30Inputs I).toSubexpLeaf.loss n = I.failure.failure n := rfl

end EventuallyL30Inputs

/-! ## 6. The GRH constructor -/

namespace EventuallyL30Counts

/-- **The leaf with every unconditional field discharged.**  The central short
count and the global upper density remain explicit premises; the global lower
bound is the `.1/8` theorem of `RandomizedL30SmoothDensity`.  The constant `A`
must satisfy `A ≥ 32` because `B = 1/8` and `A B ≥ 4`. -/
noncomputable def ofPaperGRH
    (line : DirichletLZerosOnLine) (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε)
    (A : ℝ) (hA : 0 < A) (hA32 : 32 ≤ A)
    (c C : ℝ) (hAC : A * C ≤ c)
    (hshort : EventuallyYounisOddPaperShortCount c p (paperT p) (paperError ε))
    (hupper : EventuallyGlobalOddUpperDensity C p (paperT p) (paperError ε)) :
    EventuallyL30Counts where
  p := p
  err := paperError ε
  p_ge_two := h.eventually_sixteen.mono (fun n hn => by linarith)
  err_ge_neg_one := Filter.Eventually.of_forall fun _ => by
    dsimp [paperError]
    linarith
  A := A
  B := 1 / 8
  c := c
  C := C
  A_pos := hA
  B_pos := by norm_num
  AB_ge_four := by nlinarith
  AC_le := hAC
  short_interval := hshort
  global_upper := hupper
  global_lower := eventually_younisOddGlobalLower_paper line p h hε

/-- The same constructor with an arbitrary global lower constant `B ≤ 1/8`. -/
noncomputable def ofPaperGRHWithB
    (line : DirichletLZerosOnLine) (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) (hBle : B ≤ 1 / 8)
    (A : ℝ) (hA : 0 < A) (hAB : 4 ≤ A * B)
    (c C : ℝ) (hAC : A * C ≤ c)
    (hshort : EventuallyYounisOddPaperShortCount c p (paperT p) (paperError ε))
    (hupper : EventuallyGlobalOddUpperDensity C p (paperT p) (paperError ε)) :
    EventuallyL30Counts where
  p := p
  err := paperError ε
  p_ge_two := h.eventually_sixteen.mono (fun n hn => by linarith)
  err_ge_neg_one := Filter.Eventually.of_forall fun _ => by
    dsimp [paperError]
    linarith
  A := A
  B := B
  c := c
  C := C
  A_pos := hA
  B_pos := hB
  AB_ge_four := hAB
  AC_le := hAC
  short_interval := hshort
  global_upper := hupper
  global_lower := eventually_younisOddGlobalLower_paper_of_le line p h hε hBle

end EventuallyL30Counts

/-! ## Axiom audit -/

#print axioms eventually_younisOddGlobalLower_paper_eighth
#print axioms eventually_younisOddGlobalLower_paper_of_le
#print axioms EventuallyYounisOddPaperGlobalShortCount
#print axioms eventually_paperGlobalShortCount_of_binCount
#print axioms paperSchedule_centralPlacement_false
#print axioms not_eventually_paperSchedule_centralPlacement
#print axioms eventually_paperShortCount_of_binCount_and_centralPlacement
#print axioms eventually_globalOddUpperDensity_of_parity
#print axioms not_eventually_paper_one_add_err_mul_nonpos
#print axioms eventually_paperRelative_of_eventuallyUpper
#print axioms eventually_centralCount_of_eventuallyUpper_and_lower
#print axioms EventuallyL30Counts.B_le_C
#print axioms EventuallyL30Counts.not_parity_eighth
#print axioms EventuallyL30Counts.paperShortCount
#print axioms EventuallyL30Counts.globalUpper
#print axioms EventuallyL30Counts.globalLower
#print axioms EventuallyL30Counts.younisRelative
#print axioms EventuallyL30Counts.younisCentralCount
#print axioms EventuallyL30Counts.toWave13L30Counts
#print axioms EventuallyL30Counts.toWave14L30Counts
#print axioms EventuallyL30Inputs.toSubexpLeaf
#print axioms EventuallyL30Inputs.loss_eq
#print axioms EventuallyL30Inputs.toWave13L30Inputs
#print axioms EventuallyL30Inputs.toWave13L30Inputs_loss_eq
#print axioms EventuallyL30Inputs.toWave14L30Inputs
#print axioms EventuallyL30Inputs.toWave14L30Inputs_loss_eq
#print axioms EventuallyL30Counts.ofPaperGRH
#print axioms EventuallyL30Counts.ofPaperGRHWithB
#print axioms EventuallyL30Counts.ofWave13L30Counts
#print axioms EventuallyL30Counts.ofWave14L30Counts
#print axioms EventuallyL30Inputs.ofWave14L30Inputs
#print axioms EventuallyL30Inputs.ofWave14L30Inputs_loss_eq

end

end Cogentic.RandomizedL30LeafFromGRH
