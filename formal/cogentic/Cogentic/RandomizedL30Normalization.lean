import Cogentic.RandomizedL30UpperDensity
import Cogentic.RandomizedL30Sharp
import Cogentic.RandomizedL30SharpWitness
import Cogentic.RandomizedPaperEndpointWave18

set_option maxHeartbeats 4000000

/-!
# L30: the correct exponent normalization of the paper-scale density

`Cogentic/RandomizedL30UpperDensity.lean` isolates the paper-scale upper
density

`PaperScaleSmoothUpper C p ε`,
i.e. `Ψ(p², exp ((1+ε)t_p)) ≤ C p² exp (-(1+ε)t_p)`, and observes that the
genuine Dickman bound does not imply it.  This file settles the exponent
question exactly.

## The exponent computation

At the paper scale

`t_p = sqrt (log p · log log p)`,   `Y = exp ((1+ε)t_p)`,   `x = p²`,

the Dickman parameter is

`u = log x / log Y = 2 log p / ((1+ε)t_p)`.

The exact identity `paperDensityU_mul_log_eq` of
`Cogentic/RandomizedL30SmoothDensity.lean` gives

`(1+ε) (u log u) = t_p - (log p / t_p) (log log log p + 2 log (1+ε) - 2 log 2)`,

and `log p / t_p² = 1 / log log p`.  Hence `u log u = t_p/(1+ε) (1 - o(1))`:
the true density exponent is `t_p/(1+ε)`, **not** `t_p`.  We formalize the
two-sided comparison as

* `eventually_paperDensityU_mul_log_ge_one_div_sub`:
  `(1/(1+ε) - δ) t_p ≤ u log u` for every `δ > 0`,
* `eventually_paperDensityU_mul_log_le_one_div`:
  `u log u ≤ t_p/(1+ε)`.

In particular `u log u < (1+ε)t_p` (`eventually_u_log_lt_paperExponent`), so

`exp (-(1+ε)t_p) < exp (-(u log u))`    (`eventually_paperFactor_lt_trueFactor`):

the factor required by `PaperScaleSmoothUpper` is *strictly smaller* than the
true smooth-number density factor.  This is the exponent obstruction.

## The falsity theorem

The paper's own global lower bound, at a *smaller* error `ε/2` and therefore a
*smaller* cutoff, is

`(1/8) p² exp (-(1+ε/2)t_p) ≤ Ψ_odd(p², exp ((1+ε/2)t_p))`.

Monotonicity of the smooth set in the cutoff lifts this to the cutoff
`exp ((1+ε)t_p)`, and

`exp (-(1+ε/2)t_p) / exp (-(1+ε)t_p) = exp ((ε/2)t_p) → ∞`.

Therefore for every constant `C`

`C p² exp (-(1+ε)t_p) < Ψ_odd`    eventually

(`eventually_globalOddCount_gt_any_upper`), which refutes both
`EventuallyGlobalOddUpperDensity C p (paperT p) (paperError ε)` and
`PaperScaleSmoothUpper C p ε` for every `C`
(`eventuallyGlobalOddUpperDensity_false`, `paperScaleSmoothUpper_false`).
The falsity is unconditional under `DirichletLZerosOnLine`, the same hypothesis
used to prove the global lower bound.  Consequently the old field
`l30PaperScaleUpper : PaperScaleSmoothUpper l30C l30p l30ε` of
`PaperResidualInputs` (in `Cogentic/RandomizedPaperEndpointWave18.lean`) is
uninhabited: that record carries `line : DirichletLZerosOnLine`,
`l30Growth : PaperDensityGrowth l30p` and `l30ε_pos : 0 < l30ε`, so
`paperScaleSmoothUpper_false` applies to `l30C` for every `l30C`.

## The corrected normalization

The repaired Wave-18 record no longer carries that field.  Its L30 upper field
is `l30SharpUpper : GlobalOddUpperDensitySharp l30C l30p l30ε`, and its local
count field is `l30SharpCentral : YounisOddPaperSharpIntervalCount l30c l30p
l30ε`; the explicit constant-scale witness of
`Cogentic/RandomizedL30SharpWitness` shows that both sharp predicates are
satisfied by genuine positive counts (`sharpUpper_not_refuted`,
`sharpLocal_not_refuted`, `nonempty_wave14L30Counts_sharp`).

The sharp density exponent is `u log u`, equivalently `t_p/(1+ε)`.
`Cogentic/RandomizedL30Sharp` defines the corrected predicates

* `PaperScaleSmoothUpperSharp C p ε`,
* `GlobalOddUpperDensitySharp C p ε`,
* `YounisOddPaperSharpCount c p ε` and its interval form,

all carrying the factor `exp (-(u log u))`, and proves the corrected
relative-density chain:

* `paperRelative_of_sharpUpper`,
* `eventuallyYounisOddCentralCount_of_relative`,
* `paperCentralCount_of_sharpUpper`.

The paper's displayed local count at `exp (-(1+ε)t_p)` is recovered as the
weaker corollary `eventuallyPaperShortCount_of_sharp`, because
`(1+ε)t_p > u log u`.  Thus the *same* `ε` is harmless on the local (lower
bound) side but fatal on the global (upper bound) side.  Finally the safe
over-estimate `(1-ε)t_p` is shown to be valid:
`exp (-(1-ε)t_p) ≥ exp (-(u log u))`
(`eventually_trueFactor_le_epsFactor`), and
`globalOddUpperDensityEps_of_sharp`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or error
is set to zero.
-/

namespace Cogentic.RandomizedL30Normalization

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Relative
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30UpperDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30SharpWitness
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.Randomized
open Cogentic.RandomizedPaperEndpointWave18

noncomputable section

/-! ## 1. The exact exponent comparison -/

/-- Rewrite `t - (log p / t) B` using `t² = log p · log log p`. -/
theorem paperT_sub_div_mul {p : ℕ → ℝ} {n : ℕ} (hp : 16 ≤ p n) (B : ℝ) :
    paperT p n - (Real.log (p n) / paperT p n) * B =
      paperT p n * (1 - B / Real.log (Real.log (p n))) := by
  have hp1 : (1 : ℝ) < p n := by linarith
  have hL : 0 < Real.log (p n) := Real.log_pos hp1
  have hM : 0 < Real.log (Real.log (p n)) := Real.log_pos (one_lt_log_of_sixteen hp)
  have ht : 0 < paperT p n := Real.sqrt_pos_of_pos (mul_pos hL hM)
  have ht2 : paperT p n ^ 2 = Real.log (p n) * Real.log (Real.log (p n)) := by
    unfold paperT
    exact Real.sq_sqrt (mul_nonneg hL.le hM.le)
  have hLt : Real.log (p n) / paperT p n ^ 2 = 1 / Real.log (Real.log (p n)) := by
    rw [ht2]
    field_simp
  calc
    paperT p n - (Real.log (p n) / paperT p n) * B
        = paperT p n - (Real.log (p n) / paperT p n ^ 2) * paperT p n * B := by
            field_simp [ht.ne']
    _ = paperT p n - (1 / Real.log (Real.log (p n))) * paperT p n * B := by
            rw [hLt]
    _ = paperT p n * (1 - B / Real.log (Real.log (p n))) := by
            field_simp [hM.ne']

/-- The normalised error term of the exact identity tends to zero. -/
theorem tendsto_K_div_loglog {p : ℕ → ℝ} (h : PaperDensityGrowth p) (c : ℝ) :
    Tendsto (fun n => (Real.log (Real.log (Real.log (p n))) + c) /
      Real.log (Real.log (p n))) atTop (nhds 0) := by
  have hM : Tendsto (fun n => Real.log (Real.log (p n))) atTop atTop :=
    Real.tendsto_log_atTop.comp h.tendsto_log
  have hratio : Tendsto (fun n => Real.log (Real.log (Real.log (p n))) /
      Real.log (Real.log (p n))) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hM
  have hconst : Tendsto (fun n => c / Real.log (Real.log (p n))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hM
  have hsum := hratio.add hconst
  simpa [add_div] using hsum

/-- Eventual explicit form of `K / log log p ≤ η`. -/
theorem eventually_K_div_loglog_le {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    (c η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, (Real.log (Real.log (Real.log (p n))) + c) /
      Real.log (Real.log (p n)) ≤ η :=
  ((tendsto_order.mp (tendsto_K_div_loglog h c)).2 η hη).mono
    (fun _ hn => le_of_lt hn)

/-- Explicit algebraic form of the exact identity: divide
`(1+ε) u log u = t - (log p / t) K` by `1+ε` and use
`log p / t² = 1 / log log p`. -/
theorem paperDensityU_mul_log_eq_paperT_mul {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 16 ≤ p n) (hε : 0 < ε) :
    paperDensityU p ε n * Real.log (paperDensityU p ε n) =
      paperT p n *
        (1 - (Real.log (Real.log (Real.log (p n))) +
            (2 * Real.log (1 + ε) - 2 * Real.log 2)) /
          Real.log (Real.log (p n))) / (1 + ε) := by
  have hα : (1 + ε) ≠ 0 := by positivity
  have hid := paperDensityU_mul_log_eq (p := p) (ε := ε) hp hε
  have hsub := paperT_sub_div_mul (p := p) hp
    (Real.log (Real.log (Real.log (p n))) +
      (2 * Real.log (1 + ε) - 2 * Real.log 2))
  have hkey : (1 + ε) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) =
      paperT p n *
        (1 - (Real.log (Real.log (Real.log (p n))) +
            (2 * Real.log (1 + ε) - 2 * Real.log 2)) /
          Real.log (Real.log (p n))) := by
    have h := hid
    rw [show (Real.log (Real.log (Real.log (p n))) +
        2 * Real.log (1 + ε) - 2 * Real.log 2) =
        (Real.log (Real.log (Real.log (p n))) +
          (2 * Real.log (1 + ε) - 2 * Real.log 2)) from by ring] at h
    rw [h]
    exact hsub
  rw [eq_div_iff hα]
  calc
    paperDensityU p ε n * Real.log (paperDensityU p ε n) * (1 + ε)
        = (1 + ε) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by ring
    _ = paperT p n *
          (1 - (Real.log (Real.log (Real.log (p n))) +
              (2 * Real.log (1 + ε) - 2 * Real.log 2)) /
            Real.log (Real.log (p n))) := hkey

/-- **Lower half of the exact comparison.**  For every `δ > 0`,
`(1/(1+ε) - δ) t_p ≤ u log u` eventually. -/
theorem eventually_paperDensityU_mul_log_ge_one_div_sub {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, (1 / (1 + ε) - δ) * paperT p n ≤
      paperDensityU p ε n * Real.log (paperDensityU p ε n) := by
  have hη : 0 < (1 + ε) * δ := by positivity
  have hK := eventually_K_div_loglog_le h
    (2 * Real.log (1 + ε) - 2 * Real.log 2) ((1 + ε) * δ) hη
  filter_upwards [h.eventually_sixteen, hK] with n hp hKn
  have hp1 : (1 : ℝ) < p n := by linarith
  have hL : 0 < Real.log (p n) := Real.log_pos hp1
  have hMpos : 0 < Real.log (Real.log (p n)) :=
    Real.log_pos (one_lt_log_of_sixteen hp)
  have ht : 0 < paperT p n := by
    unfold paperT
    exact Real.sqrt_pos_of_pos (mul_pos hL hMpos)
  have hα : 0 < 1 + ε := by positivity
  have hkey := paperDensityU_mul_log_eq_paperT_mul (p := p) (ε := ε) hp hε
  have hBM : (Real.log (Real.log (Real.log (p n))) +
        (2 * Real.log (1 + ε) - 2 * Real.log 2)) / Real.log (Real.log (p n)) ≤
      (1 + ε) * δ := hKn
  have hle1 : paperT p n * (1 - (1 + ε) * δ) ≤
      paperT p n * (1 - (Real.log (Real.log (Real.log (p n))) +
        (2 * Real.log (1 + ε) - 2 * Real.log 2)) / Real.log (Real.log (p n))) :=
    mul_le_mul_of_nonneg_left (by linarith) ht.le
  have hfac : (1 + ε) * (1 / (1 + ε) - δ) = 1 - (1 + ε) * δ := by
    field_simp
  have htarget : (1 / (1 + ε) - δ) * paperT p n * (1 + ε) ≤
      paperT p n * (1 - (Real.log (Real.log (Real.log (p n))) +
        (2 * Real.log (1 + ε) - 2 * Real.log 2)) / Real.log (Real.log (p n))) := by
    calc
      (1 / (1 + ε) - δ) * paperT p n * (1 + ε)
          = paperT p n * ((1 + ε) * (1 / (1 + ε) - δ)) := by ring
      _ = paperT p n * (1 - (1 + ε) * δ) := by rw [hfac]
      _ ≤ paperT p n * (1 - (Real.log (Real.log (Real.log (p n))) +
            (2 * Real.log (1 + ε) - 2 * Real.log 2)) /
          Real.log (Real.log (p n))) := hle1
  rw [hkey]
  rw [le_div_iff₀ hα]
  exact htarget

/-- **Upper half of the exact comparison.**  `u log u ≤ t_p/(1+ε)`. -/
theorem eventually_paperDensityU_mul_log_le_one_div {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, paperDensityU p ε n * Real.log (paperDensityU p ε n) ≤
      (1 / (1 + ε)) * paperT p n := by
  have hle := eventually_paperDensityU_mul_log_le_paperT h hε
  have hα : 0 < 1 + ε := by positivity
  filter_upwards [hle] with n hn
  have hu : paperDensityU p ε n * Real.log (paperDensityU p ε n) ≤
      paperT p n / (1 + ε) := by
    rw [le_div_iff₀ hα]
    nlinarith [hn]
  calc
    paperDensityU p ε n * Real.log (paperDensityU p ε n) ≤
        paperT p n / (1 + ε) := hu
    _ = (1 / (1 + ε)) * paperT p n := by ring

/-- `u log u` is eventually strictly below `(1+ε)t_p`. -/
theorem eventually_u_log_lt_paperExponent {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      paperDensityU p ε n * Real.log (paperDensityU p ε n) <
        (1 + ε) * paperT p n := by
  have hle := eventually_paperDensityU_mul_log_le_one_div h hε
  have htpos := eventually_paperT_pos_of_growth h
  have hα : 0 < 1 + ε := by positivity
  filter_upwards [hle, htpos] with n hn ht
  have hlt : (1 / (1 + ε)) * paperT p n < (1 + ε) * paperT p n := by
    have hcoef : 1 / (1 + ε) < 1 + ε := by
      rw [div_lt_iff₀ hα]
      nlinarith [hε, mul_pos hε hε]
    exact mul_lt_mul_of_pos_right hcoef ht
  exact hn.trans_lt hlt

/-- `(1-ε) t_p ≤ u log u` eventually; the safe over-estimate exponent. -/
theorem eventually_one_sub_eps_mul_paperT_le_u_log {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (1 - ε) * paperT p n ≤
      paperDensityU p ε n * Real.log (paperDensityU p ε n) := by
  have hδ : 0 < ε ^ 2 / (1 + ε) := by positivity
  have hmain := eventually_paperDensityU_mul_log_ge_one_div_sub h hε hδ
  have hcoef : 1 / (1 + ε) - ε ^ 2 / (1 + ε) = 1 - ε := by
    field_simp
    ring
  filter_upwards [hmain] with n hn
  rwa [hcoef] at hn

/-- **The claimed factor is strictly smaller than the true one.** -/
theorem eventually_paperFactor_lt_trueFactor {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      Real.exp (-(1 + ε) * paperT p n) <
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) := by
  filter_upwards [eventually_u_log_lt_paperExponent h hε] with n hn
  exact Real.exp_lt_exp.mpr (by linarith)

/-- **The `(1-ε)` factor is at least the true one.** -/
theorem eventually_trueFactor_le_epsFactor {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) ≤
        Real.exp (-(1 - ε) * paperT p n) := by
  filter_upwards [eventually_one_sub_eps_mul_paperT_le_u_log h hε] with n hn
  exact Real.exp_le_exp.mpr (by linarith)

/-! ## 2. Monotonicity of the global odd smooth count in the cutoff -/

theorem globalSmoothOrders_mono_cutoff {p t err t' err' : ℕ → ℝ} {n : ℕ}
    (h : smoothCutoff t err n ≤ smoothCutoff t' err' n) :
    globalSmoothOrders p t err n ⊆ globalSmoothOrders p t' err' n := by
  intro m hm
  rw [globalSmoothOrders, Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, fun q hq => (hm.2 q hq).trans h⟩

theorem globalOddSmoothOrders_mono_cutoff {p t err t' err' : ℕ → ℝ} {n : ℕ}
    (h : smoothCutoff t err n ≤ smoothCutoff t' err' n) :
    globalOddSmoothOrders p t err n ⊆ globalOddSmoothOrders p t' err' n := by
  intro m hm
  rw [globalOddSmoothOrders, Finset.mem_filter] at hm ⊢
  exact ⟨globalSmoothOrders_mono_cutoff h hm.1, hm.2⟩

theorem globalOddSmoothCount_mono_cutoff {p t err t' err' : ℕ → ℝ} {n : ℕ}
    (h : smoothCutoff t err n ≤ smoothCutoff t' err' n) :
    globalOddSmoothCount p t err n ≤ globalOddSmoothCount p t' err' n := by
  unfold globalOddSmoothCount
  exact_mod_cast Finset.card_le_card (globalOddSmoothOrders_mono_cutoff h)

/-! ## 3. Falsity of the positive-error upper density -/

/-- **The global odd count eventually beats every upper bound of the form
`C p² exp (-(1+ε)t_p)`.**  This is the quantitative falsity statement. -/
theorem eventually_globalOddCount_gt_any_upper
    (line : DirichletLZerosOnLine) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ n in atTop,
      C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) <
        globalOddSmoothCount p (paperT p) (paperError ε) n := by
  have hε2 : 0 < ε / 2 := by positivity
  have hlow := eventually_globalOddSmoothCount_paperLower line p h hε2
  have htpos := eventually_paperT_pos_of_growth h
  have htend := tendsto_paperT_of_growth h
  have hexp : Tendsto (fun n => Real.exp ((ε / 2) * paperT p n)) atTop atTop := by
    have harg : Tendsto (fun n => (ε / 2) * paperT p n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < ε / 2) htend
    exact Real.tendsto_exp_atTop.comp harg
  have hbig : ∀ᶠ n in atTop,
      C < (1 / 8) * Real.exp ((ε / 2) * paperT p n) := by
    have hgt := hexp.eventually_gt_atTop (8 * C)
    filter_upwards [hgt] with n hn
    nlinarith
  filter_upwards [hlow, hbig, htpos, h.eventually_sixteen] with n hlow_n hbig_n htpos_n hp16
  have hp0 : 0 < p n := by linarith
  have hp2pos : 0 < p n ^ 2 := by positivity
  have hcut : smoothCutoff (paperT p) (paperError (ε / 2)) n ≤
      smoothCutoff (paperT p) (paperError ε) n := by
    unfold smoothCutoff paperError
    apply Real.exp_le_exp.mpr
    nlinarith [htpos_n, hε.le]
  have hmono : globalOddSmoothCount p (paperT p) (paperError (ε / 2)) n ≤
      globalOddSmoothCount p (paperT p) (paperError ε) n :=
    globalOddSmoothCount_mono_cutoff hcut
  have hlt : C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) <
      (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε / 2) * paperT p n) := by
    have h1 : C * Real.exp (-(1 + ε) * paperT p n) <
        (1 / 8) * Real.exp (-(1 + ε / 2) * paperT p n) := by
      have hpos : 0 < Real.exp (-(1 + ε) * paperT p n) := Real.exp_pos _
      have hmul := mul_lt_mul_of_pos_right hbig_n hpos
      calc
        C * Real.exp (-(1 + ε) * paperT p n)
            < ((1 / 8) * Real.exp ((ε / 2) * paperT p n)) *
                Real.exp (-(1 + ε) * paperT p n) := hmul
        _ = (1 / 8) * (Real.exp ((ε / 2) * paperT p n) *
              Real.exp (-(1 + ε) * paperT p n)) := by ring
        _ = (1 / 8) * Real.exp ((ε / 2) * paperT p n +
              (-(1 + ε) * paperT p n)) := by rw [Real.exp_add]
        _ = (1 / 8) * Real.exp (-(1 + ε / 2) * paperT p n) := by
              congr 1
              ring_nf
    calc
      C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n)
          = p n ^ 2 * (C * Real.exp (-(1 + ε) * paperT p n)) := by ring
      _ < p n ^ 2 * ((1 / 8) * Real.exp (-(1 + ε / 2) * paperT p n)) :=
            mul_lt_mul_of_pos_left h1 hp2pos
      _ = (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε / 2) * paperT p n) := by ring
  calc
    C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n)
        < (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε / 2) * paperT p n) := hlt
    _ ≤ globalOddSmoothCount p (paperT p) (paperError (ε / 2)) n := hlow_n
    _ ≤ globalOddSmoothCount p (paperT p) (paperError ε) n := hmono

/-- **The paper-scale odd upper density is false** for every constant `C`. -/
theorem eventuallyGlobalOddUpperDensity_false
    (line : DirichletLZerosOnLine) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ¬ EventuallyGlobalOddUpperDensity C p (paperT p) (paperError ε) := by
  intro hupper
  have hgt := eventually_globalOddCount_gt_any_upper line h hε C
  have hle : ∀ᶠ n in atTop,
      globalOddSmoothCount p (paperT p) (paperError ε) n ≤
        C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) := by
    filter_upwards [hupper, h.eventually_sixteen] with n hn hp
    have hp2 : 0 < p n ^ 2 := by
      have : 0 < p n := by linarith
      positivity
    have hmul := mul_le_mul_of_nonneg_right hn hp2.le
    rw [div_mul_cancel₀ _ hp2.ne'] at hmul
    calc
      globalOddSmoothCount p (paperT p) (paperError ε) n
          ≤ C * Real.exp (-(1 + ε) * paperT p n) * p n ^ 2 := hmul
      _ = C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) := by ring
  have hboth : ∀ᶠ n in atTop,
      C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) <
          globalOddSmoothCount p (paperT p) (paperError ε) n ∧
        globalOddSmoothCount p (paperT p) (paperError ε) n ≤
          C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) := hgt.and hle
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hboth
  exact (not_lt_of_ge (hN N le_rfl).2) (hN N le_rfl).1

/-- **The pointwise `GlobalOddUpperDensity` of `RandomizedL30Interval` is also
false** at the paper schedule: it implies the eventual form. -/
theorem globalOddUpperDensity_false
    (line : DirichletLZerosOnLine) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ¬ GlobalOddUpperDensity C p (paperT p) (paperError ε) := by
  intro hpoint
  exact eventuallyGlobalOddUpperDensity_false line h hε C
    (Filter.Eventually.of_forall hpoint)

/-- **`PaperScaleSmoothUpper` is false** for every constant `C`. -/
theorem paperScaleSmoothUpper_false
    (line : DirichletLZerosOnLine) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ¬ PaperScaleSmoothUpper C p ε := by
  intro hpsu
  have hgt := eventually_globalOddCount_gt_any_upper line h hε C
  have hle : ∀ᶠ n in atTop,
      globalOddSmoothCount p (paperT p) (paperError ε) n ≤
        C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) := by
    filter_upwards [hpsu] with n hn
    have hsub : globalOddSmoothOrders p (paperT p) (paperError ε) n ⊆
        globalSmoothOrders p (paperT p) (paperError ε) n := by
      intro m hm
      exact (Finset.mem_filter.mp hm).1
    have hcard : globalOddSmoothCount p (paperT p) (paperError ε) n ≤
        ((globalSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
      unfold globalOddSmoothCount
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans hn
  have hboth : ∀ᶠ n in atTop,
      C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) <
          globalOddSmoothCount p (paperT p) (paperError ε) n ∧
        globalOddSmoothCount p (paperT p) (paperError ε) n ≤
          C * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) := hgt.and hle
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hboth
  exact (not_lt_of_ge (hN N le_rfl).2) (hN N le_rfl).1

/-- Eventual version of the final central-count assembly. -/
theorem eventuallyYounisOddCentralCount_of_relative
    {A B : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hrel : EventuallyYounisOddRelativeShortInterval A p t err)
    (hglob : EventuallyYounisOddGlobalLower B p t err) :
    EventuallyYounisOddCentralCount p t err := by
  filter_upwards [hrel, hglob] with n hrel_n hglob_n
  have hp_pos : (0 : ℝ) < p n := by linarith [hp n]
  have hp2 : (0 : ℝ) < p n ^ 2 := by positivity
  have hcard := centralOrderInterval_card_ge_quarter (hp n)
  have hdiv : B * Real.exp (-(1 + err n) * t n) ≤
      globalOddSmoothCount p t err n / p n ^ 2 := by
    rw [le_div_iff₀ hp2]
    have h := hglob_n
    nlinarith
  have hcoef : (0 : ℝ) ≤ A * B * Real.exp (-(1 + err n) * t n) := by positivity
  have hcardmul := mul_le_mul_of_nonneg_left hcard hcoef
  have hABone : (1 : ℝ) ≤ A * B / 4 := by nlinarith
  have hbase : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) := by
    positivity
  have hbasescale : p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n) ≤
      (A * B / 4) * (p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n)) := by
    calc
      p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n)
          = (1 : ℝ) * (p n ^ ((3 : ℝ) / 2) *
              Real.exp (-(1 + err n) * t n)) := by ring
      _ ≤ (A * B / 4) * (p n ^ ((3 : ℝ) / 2) *
              Real.exp (-(1 + err n) * t n)) :=
            mul_le_mul_of_nonneg_right hABone hbase
  have hstep1 : (A * B / 4) * (p n ^ ((3 : ℝ) / 2) *
        Real.exp (-(1 + err n) * t n)) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (B * Real.exp (-(1 + err n) * t n)) := by
    calc
      (A * B / 4) * (p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + err n) * t n))
          = (A * B * Real.exp (-(1 + err n) * t n)) *
              (p n ^ ((3 : ℝ) / 2) / 4) := by ring
      _ ≤ (A * B * Real.exp (-(1 + err n) * t n)) *
            ((centralOrderInterval p n).card : ℝ) := hcardmul
      _ = A * ((centralOrderInterval p n).card : ℝ) *
            (B * Real.exp (-(1 + err n) * t n)) := by ring
  have hstep2 : A * ((centralOrderInterval p n).card : ℝ) *
        (B * Real.exp (-(1 + err n) * t n)) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p t err n / p n ^ 2) :=
    mul_le_mul_of_nonneg_left hdiv (by positivity)
  exact hbasescale.trans (hstep1.trans (hstep2.trans hrel_n))

/-- **The corrected central-count chain.**  Sharp local count + sharp global
upper density + a global lower bound at `exp (-(1+ε)t_p)` give the paper's odd
central count.  The global lower bound is still the paper's own, at the
displayed exponent. -/
theorem paperCentralCount_of_sharpUpper {A B c C : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hAC : A * C ≤ c)
    (hcount : YounisOddPaperSharpIntervalCount c p ε)
    (hupper : GlobalOddUpperDensitySharp C p ε)
    (hglob : EventuallyYounisOddGlobalLower B p (paperT p) (paperError ε)) :
    EventuallyYounisOddCentralCount p (paperT p) (paperError ε) :=
  have hrel : EventuallyYounisOddRelativeShortInterval A p (paperT p) (paperError ε) :=
    paperRelative_of_sharpUpper hA.le hAC hcount hupper
  eventuallyYounisOddCentralCount_of_relative hp hA hB hAB hrel hglob

/-- The concrete corrected chain, using the GRH-conditional paper global lower
bound with the explicit constant `1/8`. -/
theorem paperCentralCount_of_sharpUpper_grh
    (line : DirichletLZerosOnLine) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) {A c C : ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hAB : 4 ≤ A * (1 / 8))
    (hAC : A * C ≤ c)
    (hcount : YounisOddPaperSharpIntervalCount c p ε)
    (hupper : GlobalOddUpperDensitySharp C p ε) :
    EventuallyYounisOddCentralCount p (paperT p) (paperError ε) :=
  paperCentralCount_of_sharpUpper hp hA (by norm_num) hAB hAC hcount hupper
    (eventually_younisOddGlobalLower_paper_eighth line p h hε)

/-- **The paper's displayed local count is a corollary of the sharp count.**
Because `u log u < (1+ε)t_p`, the factor `exp (-(1+ε)t_p)` is smaller than the
true one, so the same `ε` is harmless on the lower-bound side. -/
theorem eventuallyPaperShortCount_of_sharp {c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε)
    (hcount : YounisOddPaperSharpCount c p ε) :
    EventuallyYounisOddPaperShortCount c p (paperT p) (paperError ε) := by
  have hcmp := eventually_u_log_lt_paperExponent h hε
  filter_upwards [hcount, hcmp, h.eventually_sixteen] with n hn hlt hp16
  have hp_non : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) :=
    Real.rpow_nonneg (by linarith) _
  have he : (0 : ℝ) ≤ Real.exp (-(1 + ε) * paperT p n) := (Real.exp_pos _).le
  by_cases hc : 0 ≤ c
  · have hexp : Real.exp (-(1 + ε) * paperT p n) ≤
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hmul : c * p n ^ ((3 : ℝ) / 2) *
          Real.exp (-(1 + ε) * paperT p n) ≤
        c * p n ^ ((3 : ℝ) / 2) *
          Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) := by
      have hbase : p n ^ ((3 : ℝ) / 2) *
            Real.exp (-(1 + ε) * paperT p n) ≤
          p n ^ ((3 : ℝ) / 2) *
            Real.exp (-(paperDensityU p ε n *
              Real.log (paperDensityU p ε n))) :=
        mul_le_mul_of_nonneg_left hexp hp_non
      calc
        c * p n ^ ((3 : ℝ) / 2) * Real.exp (-(1 + ε) * paperT p n)
            = c * (p n ^ ((3 : ℝ) / 2) *
                Real.exp (-(1 + ε) * paperT p n)) := by ring
        _ ≤ c * (p n ^ ((3 : ℝ) / 2) *
                Real.exp (-(paperDensityU p ε n *
                  Real.log (paperDensityU p ε n)))) :=
              mul_le_mul_of_nonneg_left hbase hc
        _ = c * p n ^ ((3 : ℝ) / 2) *
                Real.exp (-(paperDensityU p ε n *
                  Real.log (paperDensityU p ε n))) := by ring
    exact hmul.trans hn
  · have hc' : c < 0 := lt_of_not_ge hc
    have hleft : c * p n ^ ((3 : ℝ) / 2) *
        Real.exp (-(1 + ε) * paperT p n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc'.le hp_non) he
    have hright : (0 : ℝ) ≤ centralOddSmoothCount p (paperT p) (paperError ε) n := by
      unfold centralOddSmoothCount
      positivity
    exact hleft.trans hright

/-- **The safe `(1-ε)` correction is a weakening of the sharp density.** -/
theorem globalOddUpperDensityEps_of_sharp {C : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε)
    (hupper : GlobalOddUpperDensitySharp C p ε) :
    GlobalOddUpperDensityEps C p ε := by
  have hcmp := eventually_one_sub_eps_mul_paperT_le_u_log h hε
  filter_upwards [hupper, hcmp] with n hn hle
  by_cases hC : 0 ≤ C
  · have hexp : Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) ≤
        Real.exp (-(1 - ε) * paperT p n) := Real.exp_le_exp.mpr (by linarith)
    exact hn.trans (mul_le_mul_of_nonneg_left hexp hC)
  · have hC' : C < 0 := lt_of_not_ge hC
    exfalso
    have hnn : (0 : ℝ) ≤
        globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 :=
      div_nonneg (by unfold globalOddSmoothCount; positivity) (by positivity)
    have hEpos : (0 : ℝ) <
        Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) :=
      Real.exp_pos _
    nlinarith [hn, hC', hEpos, hnn]

/-- **The `(1-ε)` upper bound alone cannot repair the relative-density chain**
when the local count is still the paper's `exp (-(1+ε)t_p)`.  The two
exponentials have a fixed positive gap `2ε`, so the ratio of the global upper
factor to the local lower factor tends to infinity; no positive constants
`A, C` can satisfy the required inequality eventually.  The corrected chain
therefore has to put the *same sharp exponent* `u log u` on both sides. -/
theorem not_relative_of_epsUpper_and_paperLocal {A C c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε)
    (hAC : 0 < A * C) (_hc : 0 < c) :
    ¬ ∀ᶠ n in atTop,
      A * ((centralOrderInterval p n).card : ℝ) *
          (C * Real.exp (-(1 - ε) * paperT p n)) ≤
        c * ((centralOrderInterval p n).card : ℝ) *
          Real.exp (-(1 + ε) * paperT p n) := by
  intro hrel
  have htpos := eventually_paperT_pos_of_growth h
  have htend := tendsto_paperT_of_growth h
  have hexp : Tendsto (fun n => Real.exp (2 * ε * paperT p n)) atTop atTop := by
    have harg : Tendsto (fun n => 2 * ε * paperT p n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * ε) htend
    exact Real.tendsto_exp_atTop.comp harg
  have hbig : ∀ᶠ n in atTop, c < A * C * Real.exp (2 * ε * paperT p n) := by
    have hgt := hexp.eventually_gt_atTop (c / (A * C))
    filter_upwards [hgt] with n hn
    have hrew : c = (A * C) * (c / (A * C)) := by
      rw [mul_comm, div_mul_cancel₀ c hAC.ne']
    rw [hrew]
    exact mul_lt_mul_of_pos_left hn hAC
  have hsmall : ∀ᶠ n in atTop,
      A * C * Real.exp (2 * ε * paperT p n) ≤ c := by
    filter_upwards [hrel, h.eventually_sixteen, htpos] with n hn hp16 ht
    have hp2 : (2 : ℝ) ≤ p n := by linarith
    have hIpos : (0 : ℝ) < ((centralOrderInterval p n).card : ℝ) := by
      have hq := centralOrderInterval_card_ge_quarter (p := p) (n := n) hp2
      have hp32 : (0 : ℝ) < p n ^ ((3 : ℝ) / 2) :=
        Real.rpow_pos_of_pos (by linarith) _
      nlinarith
    have hcancel : A * (C * Real.exp (-(1 - ε) * paperT p n)) ≤
        c * Real.exp (-(1 + ε) * paperT p n) := by
      have hh : (A * (C * Real.exp (-(1 - ε) * paperT p n))) *
            ((centralOrderInterval p n).card : ℝ) ≤
          (c * Real.exp (-(1 + ε) * paperT p n)) *
            ((centralOrderInterval p n).card : ℝ) := by
        calc
          (A * (C * Real.exp (-(1 - ε) * paperT p n))) *
              ((centralOrderInterval p n).card : ℝ)
              = A * ((centralOrderInterval p n).card : ℝ) *
                  (C * Real.exp (-(1 - ε) * paperT p n)) := by ring
          _ ≤ c * ((centralOrderInterval p n).card : ℝ) *
                  Real.exp (-(1 + ε) * paperT p n) := hn
          _ = (c * Real.exp (-(1 + ε) * paperT p n)) *
                  ((centralOrderInterval p n).card : ℝ) := by ring
      exact (mul_le_mul_iff_of_pos_right hIpos).mp hh
    have hEpos : (0 : ℝ) < Real.exp (-(1 + ε) * paperT p n) := Real.exp_pos _
    have hratio : A * (C * Real.exp (-(1 - ε) * paperT p n)) /
          Real.exp (-(1 + ε) * paperT p n) ≤ c :=
      (div_le_iff₀ hEpos).mpr hcancel
    have heq : Real.exp (-(1 - ε) * paperT p n) /
          Real.exp (-(1 + ε) * paperT p n) = Real.exp (2 * ε * paperT p n) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    calc
      A * C * Real.exp (2 * ε * paperT p n)
          = A * (C * (Real.exp (-(1 - ε) * paperT p n) /
              Real.exp (-(1 + ε) * paperT p n))) := by
            rw [heq]
            ring
      _ = A * (C * Real.exp (-(1 - ε) * paperT p n)) /
              Real.exp (-(1 + ε) * paperT p n) := by ring
      _ ≤ c := hratio
  have hboth : ∀ᶠ n in atTop,
      c < A * C * Real.exp (2 * ε * paperT p n) ∧
        A * C * Real.exp (2 * ε * paperT p n) ≤ c := hbig.and hsmall
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hboth
  exact (not_lt_of_ge (hN N le_rfl).2) (hN N le_rfl).1

/-- **The repaired residual record carries the sharp upper field.**  The
Wave-18 record no longer contains `PaperScaleSmoothUpper l30C l30p l30ε` (which
is false for every `l30C`); its upper field is `GlobalOddUpperDensitySharp`,
with the true exponent `u log u`. -/
theorem paperResidualInputs_sharpUpper (D : ℝ) (R : PaperResidualInputs D) :
    GlobalOddUpperDensitySharp R.l30C R.l30p R.l30ε :=
  R.l30SharpUpper

/-- **The repaired sharp upper field is not refuted.**  There is an explicit
constant-scale prime sequence and positive error for which the sharp upper
density holds. -/
theorem sharpUpper_not_refuted :
    ∃ (C : ℝ) (p : ℕ → ℝ) (ε : ℝ), GlobalOddUpperDensitySharp C p ε :=
  ⟨1 / 4, wP, wEps, witness_sharpUpper⟩

/-- **The repaired sharp local count is not refuted.** -/
theorem sharpLocal_not_refuted :
    ∃ (c : ℝ) (p : ℕ → ℝ) (ε : ℝ), YounisOddPaperSharpIntervalCount c p ε :=
  ⟨1 / 16, wP, wEps, witness_sharpLocal⟩

/-- **The repaired `Wave14L30Counts` is inhabited.** -/
theorem nonempty_wave14L30Counts_sharp :
    Nonempty (Cogentic.RandomizedPaperEndpointWave14.Wave14L30Counts) :=
  Cogentic.RandomizedL30SharpWitness.nonempty_wave14L30Counts

/-! ## Axiom audit -/

#print axioms tendsto_K_div_loglog
#print axioms eventually_paperDensityU_mul_log_ge_one_div_sub
#print axioms eventually_paperDensityU_mul_log_le_one_div
#print axioms eventually_u_log_lt_paperExponent
#print axioms eventually_one_sub_eps_mul_paperT_le_u_log
#print axioms eventually_paperFactor_lt_trueFactor
#print axioms eventually_trueFactor_le_epsFactor
#print axioms globalOddSmoothCount_mono_cutoff
#print axioms eventually_globalOddCount_gt_any_upper
#print axioms eventuallyGlobalOddUpperDensity_false
#print axioms globalOddUpperDensity_false
#print axioms paperScaleSmoothUpper_false
#print axioms globalOddUpperDensitySharp_of_paperScaleSharp
#print axioms paperSharpIntervalCount_of_paperSharpCount
#print axioms paperRelative_of_sharpUpper
#print axioms eventuallyYounisOddCentralCount_of_relative
#print axioms paperCentralCount_of_sharpUpper
#print axioms paperCentralCount_of_sharpUpper_grh
#print axioms eventuallyPaperShortCount_of_sharp
#print axioms globalOddUpperDensityEps_of_sharp
#print axioms not_relative_of_epsUpper_and_paperLocal
#print axioms paperResidualInputs_sharpUpper
#print axioms sharpUpper_not_refuted
#print axioms sharpLocal_not_refuted
#print axioms nonempty_wave14L30Counts_sharp

end

end Cogentic.RandomizedL30Normalization
