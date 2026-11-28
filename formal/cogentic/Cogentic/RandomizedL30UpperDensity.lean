import Cogentic.RandomizedL30LeafFromGRH
import Cogentic.RandomizedSmoothDensity

set_option maxHeartbeats 4000000

/-!
# L30: the paper-scale global odd upper density

`Cogentic/RandomizedL30LeafFromGRH.lean` isolates the paper-scale upper-density
field

`EventuallyGlobalOddUpperDensity C p (paperT p) (paperError ε)`,
i.e.

`globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 ≤
  C * exp (-(1 + ε) * paperT p n)` eventually.

The only *unconditional* upper density in the development is the parity bound
`3/8`, which is available only when `(1 + ε) t ≤ 0`; that corner is empty in the
paper regime (`not_eventually_paper_one_add_err_mul_nonpos`).  This file records
what the smooth-number upper estimate actually supplies at the paper scale.

## What is proved

1. `PaperScaleSmoothUpper C p ε` is the *smallest explicit* paper-scale
   smooth-number upper estimate: the full `Y`-smooth count below `p²` is at most
   `C p² exp (-(1+ε)t_p)`.  The odd count is a subset of this set
   (`globalOddSmoothOrders_subset_global` from `RandomizedL30Younis`), so the
   requested global odd upper density follows with the same constant
   (`eventuallyGlobalOddUpperDensity_of_paperScaleSmoothUpper`).

2. `RankinPaperUpper C p ε` is a concrete analytic sufficient form of
   `PaperScaleSmoothUpper`: it asserts that at the paper scale the explicit
   Rankin bound of `Cogentic.Randomized.smoothCount_rankin_upper` is already at
   most `C p² exp (-(1+ε)t_p)`.  The reduction
   `paperScaleSmoothUpper_of_rankin` is a direct application of the Rankin
   theorem; it is the exact place where the smooth-number upper estimate of
   `Cogentic/RandomizedSmoothDensity.lean` enters.

3. `EventuallySmoothUpperDickman C δ p ε` is the genuine Dickman-shaped
   estimate

   `Ψ(p², exp ((1+ε)t_p)) ≤ C p² exp (-(1-δ) u log u)`,
   `u = log (p²) / log (exp ((1+ε)t_p))`.

   From it we prove the honest upper bound for the *same* odd count at the
   original cutoff:
   `globalOddSmoothCount / p² ≤ C exp (-(1-δ) t_p / (2(1+ε)))`
   (`eventuallyGlobalOddCount_div_sq_le_dickman`).  The factor `2` comes from
   the unconditional asymptotic comparison
   `eventually_paperT_le_two_mul_paperDensityU_log`.  The count is *not*
   redefined with a different `err`: changing `err` would also change the
   smoothness cutoff inside `globalOddSmoothCount`.

4. The exponent obstruction is formalised:
   `(1-δ) u log u` is eventually *strictly smaller* than `(1+ε) t_p`
   (`dickman_exponent_lt_paperExponent`).  Consequently the Dickman factor
   `exp (-(1-δ) u log u)` is eventually *larger* than
   `exp (-(1+ε)t_p)` (`dickman_factor_gt_paperFactor`).  Therefore the true
   Dickman upper estimate cannot imply the paper-scale upper density with the
   positive error `paperError ε`; the latter is stronger than the actual
   smooth-number density at this cutoff.  The missing paper-scale estimate is
   isolated as `PaperScaleSmoothUpper`, and no false reduction from the genuine
   Dickman bound is asserted.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or
constant is set to zero.  The constants `C` in the reductions are explicit and
positive as required.
-/

namespace Cogentic.RandomizedL30UpperDensity

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Relative
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.Randomized

noncomputable section

/-! ## 1. The smallest explicit paper-scale smooth upper estimate -/

/-- **The smallest explicit paper-scale smooth-number upper estimate.**  Every
`exp ((1+ε)t_p)`-smooth integer up to `p²` is counted, and the whole count is at
most `C p² exp (-(1+ε)t_p)`.  This is exactly the upper-density companion used
by the leaf, before restricting to odd-half orders.  It is stated for the full
smooth set so that the odd parity reduction is elementary. -/
def PaperScaleSmoothUpper (C : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
      C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n)

/-- **The global odd upper density from the paper-scale smooth upper bound.**
The odd-half smooth orders are a subset of all smooth orders, so the odd count
inherits the same constant `C`.  This is the parity decomposition used for the
upper side: only the inclusion `globalOddSmoothOrders ⊆ globalSmoothOrders` is
needed, in contrast with the lower side where odd-half orders are constructed
explicitly. -/
theorem eventuallyGlobalOddUpperDensity_of_paperScaleSmoothUpper
    {C : ℝ} (_hC : 0 < C) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (_hε : 0 < ε) (hupper : PaperScaleSmoothUpper C p ε) :
    EventuallyGlobalOddUpperDensity C p (paperT p) (paperError ε) := by
  filter_upwards [hupper, h.eventually_sixteen] with n hn hp
  have hp0 : (0 : ℝ) < p n := by linarith
  have hp2 : (0 : ℝ) < p n ^ 2 := by positivity
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
    _ ≤ C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) := hn
    _ = C * Real.exp (-(1 + ε) * paperT p n) * p n ^ 2 := by ring

/-! ## 2. The reduction from the explicit Rankin upper bound -/

/-- **The paper-scale Rankin upper bound.**  This is the concrete smooth-number
upper estimate of `Cogentic.Randomized.smoothCount_rankin_upper` evaluated at
`x = p²` and `y = exp ((1+ε)t_p)`, and already bounded by the paper-scale
target with constant `C`.  The exponent `α ∈ (0,1)` is existentially quantified
at every scale, so no saddle-point parameter is baked into the statement. -/
def RankinPaperUpper (C : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    (p n ^ 2) ^ α *
      (∏ q ∈ (Finset.Icc 2 ⌊smoothCutoff (paperT p) (paperError ε) n⌋₊).filter
          Nat.Prime, (1 - (q : ℝ) ^ (-α))⁻¹) ≤
      C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n)

/-- **The Rankin bound gives the paper-scale smooth upper estimate.**  This is
the direct application of `smoothCount_rankin_upper`; the only eventual inputs
are `p ≥ 16` (from `PaperDensityGrowth`) and the cutoff being at least `2`. -/
theorem paperScaleSmoothUpper_of_rankin
    {C : ℝ} (_hC : 0 < C) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (hR : RankinPaperUpper C p ε) :
    PaperScaleSmoothUpper C p ε := by
  filter_upwards [hR, h.eventually_sixteen,
    eventually_paperSmoothCutoff_ge_two p h hε] with n hn hp hy
  obtain ⟨α, hα0, hα1, hbound⟩ := hn
  have hp1 : (1 : ℝ) ≤ p n ^ 2 := by
    have h16 : (16 : ℝ) ≤ p n := hp
    nlinarith [sq_nonneg (p n - 4), h16]
  have hcard := smoothCount_rankin_upper
    (x := p n ^ 2) (y := smoothCutoff (paperT p) (paperError ε) n)
    hp1 hy hα0 hα1
  have hfilter : (Finset.Icc 1 ⌊p n ^ 2⌋₊).filter
        (IsSmoothUpTo (smoothCutoff (paperT p) (paperError ε) n)) =
      (Finset.Icc 1 ⌊p n ^ 2⌋₊).filter
        (fun m : ℕ => ∀ q ∈ m.primeFactors,
          (q : ℝ) ≤ smoothCutoff (paperT p) (paperError ε) n) := by
    apply Finset.filter_congr
    intro m _
    rfl
  have hcard' : ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
      (p n ^ 2) ^ α *
        (∏ q ∈ (Finset.Icc 2
            ⌊smoothCutoff (paperT p) (paperError ε) n⌋₊).filter Nat.Prime,
          (1 - (q : ℝ) ^ (-α))⁻¹) := by
    rw [globalSmoothOrders, hfilter]
    exact hcard
  exact hcard'.trans hbound

/-- **The paper-scale global odd upper density from the Rankin upper bound.**
Composing `paperScaleSmoothUpper_of_rankin` with the parity inclusion gives the
requested upper-density statement, for any explicit positive `C` for which the
Rankin bound holds at the paper scale. -/
theorem eventuallyGlobalOddUpperDensity_of_rankinPaperUpper
    {C : ℝ} (hC : 0 < C) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (hR : RankinPaperUpper C p ε) :
    EventuallyGlobalOddUpperDensity C p (paperT p) (paperError ε) :=
  eventuallyGlobalOddUpperDensity_of_paperScaleSmoothUpper hC h hε
    (paperScaleSmoothUpper_of_rankin hC h hε hR)

/-! ## 3. The genuine Dickman-shaped estimate -/

/-- **The genuine Dickman-shaped smooth upper estimate at the paper scale.**
The full smooth count below `p²` with cutoff `exp ((1+ε)t_p)` is at most
`C p² exp (-(1-δ) u log u)`, where
`u = log (p²) / log (exp ((1+ε)t_p))`.  This is the paper-scale form of the
classical Dickman upper bound `ρ(u) ≤ exp (-(1-δ) u log u)` (equivalently the
explicit de Bruijn/Rankin upper bound), with the usual constant `C` and a fixed
`δ > 0`. -/
def EventuallySmoothUpperDickman (C δ : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
      C * p n ^ 2 *
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n)))

/-- The odd-half companion of `EventuallySmoothUpperDickman`. -/
def EventuallyGlobalOddDickmanUpper (C δ : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    globalOddSmoothCount p (paperT p) (paperError ε) n ≤
      C * p n ^ 2 *
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n)))

/-- **The odd parity decomposition for the Dickman upper bound.**  Filtering to
odd-half orders can only decrease the count, so the odd Dickman upper bound
holds with the same constants. -/
theorem eventuallyGlobalOddDickmanUpper_of_smooth
    {C δ : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hd : EventuallySmoothUpperDickman C δ p ε) :
    EventuallyGlobalOddDickmanUpper C δ p ε := by
  filter_upwards [hd] with n hn
  have hsub : globalOddSmoothOrders p (paperT p) (paperError ε) n ⊆
      globalSmoothOrders p (paperT p) (paperError ε) n := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hcard : globalOddSmoothCount p (paperT p) (paperError ε) n ≤
      ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
    unfold globalOddSmoothCount
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hn

/-- **The honest paper-scale upper bound supplied by the Dickman estimate.**
Using `t_p ≤ 2 (1+ε) u log u`, the Dickman factor is at most
`exp (-(1-δ) t_p / (2(1+ε)))`.  The *same* odd count, at the original cutoff
`exp ((1+ε)t_p)`, therefore obeys

`globalOddSmoothCount / p² ≤ C exp (-(1-δ) t_p / (2(1+ε)))`.

This is the strongest upper hold that the genuine Dickman bound gives for the
paper count.  Its exponent is strictly larger than the leaf's `(1+ε)t_p`; it is
not the leaf's positive-error field, see §4. -/
theorem eventuallyGlobalOddCount_div_sq_le_dickman
    {C δ : ℝ} (_hC : 0 < C) (hδ1 : δ ≤ 1)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    (hd : EventuallySmoothUpperDickman C δ p ε) :
    ∀ᶠ n in atTop,
      globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 ≤
        C * Real.exp (-((1 - δ) * paperT p n / (2 * (1 + ε)))) := by
  have hodd := eventuallyGlobalOddDickmanUpper_of_smooth hd
  have hcompare := eventually_paperT_le_two_mul_paperDensityU_log h hε
  filter_upwards [hodd, hcompare, h.eventually_sixteen] with n hn hle hp
  have hp0 : (0 : ℝ) < p n := by linarith
  have hp2 : (0 : ℝ) < p n ^ 2 := by positivity
  have hden : (0 : ℝ) < 2 * (1 + ε) := by positivity
  have hcoef : (0 : ℝ) ≤ 1 - δ := by linarith
  have hrate : (1 - δ) * paperT p n / (2 * (1 + ε)) ≤
      (1 - δ) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hle hcoef]
  have hfactor : Real.exp (-(1 - δ) * (paperDensityU p ε n *
        Real.log (paperDensityU p ε n))) ≤
      Real.exp (-((1 - δ) * paperT p n / (2 * (1 + ε)))) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [div_le_iff₀ hp2]
  have hstep : globalOddSmoothCount p (paperT p) (paperError ε) n ≤
      C * p n ^ 2 *
        Real.exp (-((1 - δ) * paperT p n / (2 * (1 + ε)))) :=
    hn.trans (mul_le_mul_of_nonneg_left hfactor (by positivity))
  calc
    globalOddSmoothCount p (paperT p) (paperError ε) n
        ≤ C * p n ^ 2 *
            Real.exp (-((1 - δ) * paperT p n / (2 * (1 + ε)))) := hstep
    _ = C * Real.exp (-((1 - δ) * paperT p n / (2 * (1 + ε)))) * p n ^ 2 := by
      ring

/-- **The exact exponent-dominance premise.**  The Dickman bound gives the
paper-scale smooth upper estimate precisely when the Dickman exponent dominates
the paper exponent, i.e. `(1+ε)t_p ≤ (1-δ) u log u` eventually.  This is the
smallest explicit bridge between the genuine smooth-number estimate and the
leaf's positive-error upper density. -/
def DickmanDominatesPaperExponent (p : ℕ → ℝ) (ε δ : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    (1 + ε) * paperT p n ≤
      (1 - δ) * (paperDensityU p ε n * Real.log (paperDensityU p ε n))

/-- **The Dickman bound plus exponent dominance gives the paper-scale smooth
upper estimate.**  This is the exact reduction: only the exponent comparison is
used beyond `EventuallySmoothUpperDickman`. -/
theorem paperScaleSmoothUpper_of_dickman_of_exponent
    {C δ : ℝ} (hC : 0 < C) {p : ℕ → ℝ} {ε : ℝ}
    (hd : EventuallySmoothUpperDickman C δ p ε)
    (hexp : DickmanDominatesPaperExponent p ε δ) :
    PaperScaleSmoothUpper C p ε := by
  filter_upwards [hd, hexp] with n hn hexpn
  have hfactor : Real.exp (-(1 - δ) * (paperDensityU p ε n *
        Real.log (paperDensityU p ε n))) ≤
      Real.exp (-(1 + ε) * paperT p n) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact hn.trans (mul_le_mul_of_nonneg_left hfactor (by positivity))

/-- **The requested paper-scale global odd upper density from the Dickman
estimate and the exponent bridge.**  This is the exact composition of
`paperScaleSmoothUpper_of_dickman_of_exponent` with the odd parity reduction.
The hypothesis `DickmanDominatesPaperExponent` is not redundant: §4 proves it
fails in the paper regime, so this theorem cannot be made unconditional from
the true Dickman bound alone. -/
theorem eventuallyGlobalOddUpperDensity_of_dickman_of_exponent
    {C δ : ℝ} (hC : 0 < C) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε)
    (hd : EventuallySmoothUpperDickman C δ p ε)
    (hexp : DickmanDominatesPaperExponent p ε δ) :
    EventuallyGlobalOddUpperDensity C p (paperT p) (paperError ε) :=
  eventuallyGlobalOddUpperDensity_of_paperScaleSmoothUpper hC h hε
    (paperScaleSmoothUpper_of_dickman_of_exponent hC hd hexp)

/-! ## 4. The exponent obstruction -/

/-- **The Dickman exponent is strictly below the paper exponent.**  At the paper
schedule `(1+ε) u log u ≤ t_p`, hence
`(1-δ) u log u ≤ (1-δ) t_p/(1+ε) < (1+ε) t_p` for `δ > 0`.  Thus the genuine
Dickman upper bound has a *larger* exponential factor than the leaf's
positive-error upper density. -/
theorem dickman_exponent_lt_paperExponent
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ n in atTop,
      (1 - δ) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) <
        (1 + ε) * paperT p n := by
  have hupper := eventually_paperDensityU_mul_log_le_paperT h hε
  have htpos := eventually_paperT_pos_of_growth h
  filter_upwards [hupper, htpos] with n hle ht
  have hεpos : (0 : ℝ) < 1 + ε := by linarith
  have hcoef : (0 : ℝ) ≤ 1 - δ := by linarith
  have hle' : (1 - δ) * (paperDensityU p ε n *
        Real.log (paperDensityU p ε n)) ≤
      (1 - δ) * paperT p n / (1 + ε) := by
    rw [le_div_iff₀ hεpos]
    nlinarith [mul_le_mul_of_nonneg_left hle hcoef]
  have hratio : (1 - δ) / (1 + ε) < 1 + ε := by
    rw [div_lt_iff₀ hεpos]
    nlinarith [sq_nonneg (1 + ε), hδ]
  have hstrict : (1 - δ) * paperT p n / (1 + ε) <
      (1 + ε) * paperT p n := by
    rw [div_lt_iff₀ hεpos]
    have h2 := mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_right hratio ht) hεpos
    calc
      (1 - δ) * paperT p n
          = (1 + ε) * (((1 - δ) / (1 + ε)) * paperT p n) := by
            field_simp
      _ < (1 + ε) * ((1 + ε) * paperT p n) := h2
      _ = (1 + ε) * paperT p n * (1 + ε) := by ring
  exact hle'.trans_lt hstrict

/-- **The Dickman factor dominates the paper factor.**  This is the exponential
form of `dickman_exponent_lt_paperExponent`: the factor supplied by the true
Dickman upper bound is eventually larger than the factor required by the
leaf's positive-error upper density.  Hence the latter cannot be derived from
the former by monotonicity of `exp`. -/
theorem dickman_factor_gt_paperFactor
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ n in atTop,
      Real.exp (-(1 + ε) * paperT p n) <
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n))) := by
  filter_upwards [dickman_exponent_lt_paperExponent h hε hδ hδ1] with n hn
  exact Real.exp_lt_exp.mpr (by linarith)

/-- **The exponent-dominance premise is false in the paper regime.**  For every
fixed `0 < δ ≤ 1` and `ε > 0`, the Dickman exponent is eventually strictly below
`(1+ε)t_p` (`dickman_exponent_lt_paperExponent`), so the bridge
`DickmanDominatesPaperExponent` fails.  This is the formal reason why the true
Dickman estimate does not discharge the leaf's positive-error upper density. -/
theorem not_dickmanDominatesPaperExponent
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ¬ DickmanDominatesPaperExponent p ε δ := by
  intro hdom
  have hlt := dickman_exponent_lt_paperExponent h hε hδ hδ1
  have hboth : ∀ᶠ n in atTop,
      (1 + ε) * paperT p n ≤
        (1 - δ) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) ∧
      (1 - δ) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) <
        (1 + ε) * paperT p n := hdom.and hlt
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hboth
  exact (not_lt_of_ge (hN N le_rfl).1) (hN N le_rfl).2

/-- **The positive-error paper upper density is not a consequence of the
Dickman bound via exponent comparison.**  If the smooth density were exactly
the Dickman factor at a tail, then the paper-scale upper density with a positive
error would force the exponential factor `exp (-(1+ε)t_p)` to dominate the
Dickman factor, contradicting `dickman_factor_gt_paperFactor`.  This records
the precise mismatch; the missing estimate is therefore the separate explicit
`PaperScaleSmoothUpper`. -/
theorem paperUpper_not_forced_by_dickman
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdensity : ∀ᶠ n in atTop,
      globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 =
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n)))) :
    ¬ ∀ᶠ n in atTop,
      globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 ≤
        Real.exp (-(1 + ε) * paperT p n) := by
  intro hupper
  have hgt := dickman_factor_gt_paperFactor h hε hδ hδ1
  have hboth : ∀ᶠ n in atTop,
      Real.exp (-(1 + ε) * paperT p n) <
        Real.exp (-(1 - δ) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n))) ∧
      globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 ≤
        Real.exp (-(1 + ε) * paperT p n) := hgt.and hupper
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hboth.and hdensity)
  have hlt := (hN N le_rfl).1.1
  have hle := (hN N le_rfl).1.2
  have heq := (hN N le_rfl).2
  rw [heq] at hle
  exact (not_le_of_gt hlt) hle

/-! ## Axiom audit -/

#print axioms eventuallyGlobalOddUpperDensity_of_paperScaleSmoothUpper
#print axioms paperScaleSmoothUpper_of_rankin
#print axioms eventuallyGlobalOddUpperDensity_of_rankinPaperUpper
#print axioms eventuallyGlobalOddDickmanUpper_of_smooth
#print axioms eventuallyGlobalOddCount_div_sq_le_dickman
#print axioms paperScaleSmoothUpper_of_dickman_of_exponent
#print axioms eventuallyGlobalOddUpperDensity_of_dickman_of_exponent
#print axioms not_dickmanDominatesPaperExponent
#print axioms dickman_exponent_lt_paperExponent
#print axioms dickman_factor_gt_paperFactor
#print axioms paperUpper_not_forced_by_dickman

end

end Cogentic.RandomizedL30UpperDensity
