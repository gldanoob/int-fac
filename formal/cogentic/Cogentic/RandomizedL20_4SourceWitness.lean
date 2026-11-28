import Cogentic.RandomizedL20_4LeafAssembly
import Cogentic.RandomizedL20_4TopComparison
import Cogentic.RandomizedL20_4BaseSource
import Cogentic.RandomizedL20_4RationalSource
import Cogentic.RandomizedL20_4EtaSource
import Cogentic.RandomizedL20_4PairAlt
import Cogentic.RandomizedL20_4Conditioned

/-!
# L20.4: explicit finite witnesses for the sourced leaf

This file constructs concrete, non-degenerate inhabitants of the L20.4 leaf
data.

## What is built

* A two-point probability space `Bool` with the fair coin law `coinPMF`.
  On it we build a genuine `TwoPointAltReducedData` whose conditioning event is
  the disjunction `g ∨ R_{q,s}`.  The rational-good event `g` is full, the child
  root `R_{q,s}` is the half-mass event `{true}`, the height `Z` is `0` on
  `false` and `1/2` on `true`, the mean constants are `a = 1/8`, `a₀ = 1/4`,
  and the pool size is `⌈D³⌉ + 1`.  The pool miss mass is strictly positive at
  every scale (`(1/2)^K`).
* A concrete `DyadData` on `ℕ`: a nonempty dyad of size `⌈exp (scale²)⌉ + 1`
  with a single bad point of mass `2`.  Its Markov-trimmed fraction is
  `1/|dyad| > 0`, and its average is `D^{-B}` for every `B`.
* A concrete `TopG12AdditiveData` with `L = 0`, `step = 1`, and the four
  interior/exception masses equal to `exp (-(scale)²)`.  The additive G.12
  comparison is immediate because `t ≤ √t` for `0 ≤ t ≤ 1`.
* Hence a full `L20_4LeafInputs Bool ℕ`, with `SubexpLoss` and a strictly
  positive assembled loss at every scale.

## The exact residual field of the sourced version

`SourcedTopData` is `TopG12AdditiveData` plus one field

`exceptions : PaperExceptionSources interior L eta`.

`PaperExceptionSources` consists of three `L20_2Inputs` (base, rational,
incoming) together with one `L21_2Inputs` (elliptic), plus the definitional
source identifications.  The L20.2 part is constructed explicitly below
(`witnessL20_2`): a one-point cell with `Fin μ` interior points, score `1`,
proxy `1 - ε`, where `ε = min (√ρ) (1/2)` and `ρ = 2 exp (-2 D log D)`.  This
gives a strictly positive base discrepancy and the genuine CRT + character
budget.

The only field not constructed in the tree is an `L21_2Inputs`.  Consequently
we give

* `sourcedTopDataOfElliptic (E : L21_2Inputs) : SourcedTopData`, and
* `sourcedLeafOfElliptic (E : L21_2Inputs) : L20_4SourcedLeafInputs Bool ℕ`,

both with every other field explicit.  Thus `L20_4SourcedLeafInputs` is
inhabited as soon as one `L21_2Inputs` is supplied, and the only residual
field is `SourcedTopData.exceptions` (specifically its `elliptic` component).

## Structural checks requested

* `event_pos : ∀ n, 0 < pmfProb …` is *not* contradictory: it holds at `n = 0`
  because the witness disjunction is the full event and `pmfProb univ = 1`.
* At `n = 0` we have `scale 0 = 0`, so every `exp (c * scale 0)` is `1`.  The
  constant-vs-growing pool inequality therefore reads `1 ≤ poolSize 0`, which
  the explicit `⌈D³⌉ + 1` satisfies.  Likewise all `∀ n` positivity fields are
  verified at `n = 0` below.
* No field of `L20_4LeafInputs` is contradicted; the only missing sourced field
  is the elliptic `L21_2Inputs` described above.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No loss or count is
set to zero.
-/

namespace Cogentic.RandomizedL20_4SourceWitness

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4TwoPoint
open Cogentic.RandomizedL20_4ChildLower
open Cogentic.RandomizedL20_4PairAlt
open Cogentic.RandomizedL20_4Top
open Cogentic.RandomizedL20_4Additive
open Cogentic.RandomizedL20_4Interior
open Cogentic.RandomizedL20_4InteriorBase
open Cogentic.RandomizedL20_4EtaSource
open Cogentic.RandomizedL20_4LeafAssembly

noncomputable section

/-! ## 1. The fair coin and finite-law computations -/

/-- The fair coin on `Bool`, with mass `1/2` on each point. -/
def coinPMF : PMF Bool :=
  PMF.uniformOfFintype Bool

@[simp]
theorem pmfWeight_coin (b : Bool) : pmfWeight coinPMF b = 1 / 2 := by
  simp [pmfWeight, coinPMF]

/-- The probability of the full event is one. -/
theorem pmfProb_true (μ : PMF Bool) : pmfProb μ (fun _ => True) = 1 := by
  rw [pmfProb_eq_sum_filter, Finset.sum_filter, Fintype.sum_bool]
  simpa [Fintype.sum_bool] using pmfWeight_sum_eq_one μ

/-- The probability of the empty event is zero. -/
theorem pmfProb_false (μ : PMF Bool) : pmfProb μ (fun _ => False) = 0 := by
  rw [pmfProb_eq_sum_filter, Finset.sum_filter, Fintype.sum_bool]
  simp

/-- The coin height `b ↦ if b then 1/2 else 0` has mean `1/4`. -/
theorem pmfExpect_coin_height :
    pmfExpect coinPMF (fun b : Bool => if b then (1 / 2 : ℝ) else 0) = 1 / 4 := by
  rw [pmfExpect, Fintype.sum_bool]
  simp [pmfWeight_coin]
  norm_num

/-- The probability that the coin is `true` is `1/2`. -/
theorem pmfProb_coin_true : pmfProb coinPMF (fun b : Bool => b) = 1 / 2 := by
  rw [pmfProb_eq_sum_filter, Finset.sum_filter, Fintype.sum_bool]
  simp [pmfWeight_coin]

/-- The probability that the coin height reaches `1/16` is `1/2`. -/
theorem pmfProb_coin_height_ge :
    pmfProb coinPMF
      (fun b : Bool => (1 / 16 : ℝ) ≤ if b then (1 / 2 : ℝ) else 0) = 1 / 2 := by
  rw [pmfProb_eq_sum_filter, Finset.sum_filter, Fintype.sum_bool]
  simp [pmfWeight_coin]
  norm_num

/-! ## 2. The concrete disjunction-event pair data -/

/-- The concrete height: zero on `false`, one half on `true`. -/
def witnessHeight (_n : ℕ) (b : Bool) : ℝ := if b then 1 / 2 else 0

/-- The rational-good event is full while the prescribed child root is the
half-mass event `{true}`.  Their disjunction is therefore the full event, which
is exactly the `g ∨ R_{q,s}` event of `TwoPointAltReducedData`; the child-root
mass lower bound is consequently the honest `1/2 ≥ D^{-1}`. -/
def witnessPair : TwoPointAltReducedData Bool where
  μ := fun _ => coinPMF
  good := fun _ _ => True
  childRoot := fun _ b => b = true
  Z := witnessHeight
  a := 1 / 8
  a_pos := by norm_num
  a₀ := 1 / 4
  a₀_pos := by norm_num
  a_le := by norm_num
  cM := 0
  cM_nonneg := le_rfl
  cV := 0
  cV_nonneg := le_rfl
  cB := 1
  cV_lt_cB := by norm_num
  cR := 1
  cR_nonneg := by norm_num
  cG := 1
  cB_le_cG := le_rfl
  mean_upper := by
    refine Eventually.of_forall fun n => ?_
    change pmfExpect coinPMF (fun b : Bool => if b then (1 / 2 : ℝ) else 0) ≤
      Real.exp (0 * scale n)
    rw [pmfExpect_coin_height]
    rw [show (0 : ℝ) * scale n = 0 by ring, Real.exp_zero]
    norm_num
  height_upper := by
    refine Eventually.of_forall fun n b => ?_
    rw [show (0 : ℝ) * scale n = 0 by ring, Real.exp_zero]
    cases b <;> norm_num [witnessHeight]
  Z_nonneg := by
    intro n b
    cases b <;> simp [witnessHeight]
  child_root_mass_lower := by
    unfold ChildRootMassLower EventMassLower
    filter_upwards [scale_grows.eventually_ge_atTop (Real.log 2)] with n hn
    rw [show -(1 : ℝ) * scale n = -scale n by ring, pmfProb_coin_true]
    calc Real.exp (-scale n) ≤ Real.exp (-(Real.log 2)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]
          norm_num
  good_complement := by
    refine Eventually.of_forall fun n => ?_
    have hfun : (fun b : Bool => ¬ (fun _ _ => True) n b) = fun _ => False := by
      funext b
      simp
    rw [hfun, pmfProb_false]
    positivity
  mean_lower := by
    refine Eventually.of_forall fun n => ?_
    change (1 / 4 : ℝ) ≤
      pmfExpect coinPMF (fun b : Bool => if b then (1 / 2 : ℝ) else 0)
    rw [pmfExpect_coin_height]
  cDyad := 0
  cDyad_nonneg := le_rfl
  dyadCard := fun _ => 1
  dyadCard_le := by
    refine Eventually.of_forall fun n => ?_
    simp
  poolSize := fun n => Nat.ceil (Real.exp (3 * scale n)) + 1
  poolSize_ge := by
    refine Eventually.of_forall fun n => ?_
    have h1 : Real.exp (3 * scale n) ≤ (Nat.ceil (Real.exp (3 * scale n)) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (3 * scale n)) : ℝ) ≤
        ((Nat.ceil (Real.exp (3 * scale n)) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hcoef : (0 + 0 + 1 + 0 + 2 : ℝ) = 3 := by norm_num
    rw [hcoef]
    exact h1.trans h2
  event_pos := by
    intro n
    have hval : pmfProb coinPMF
        (pairEventAlt (fun _ _ => True) (fun _ b => b = true) n) = 1 := by
      rw [show pairEventAlt (fun _ _ => True) (fun _ b => b = true) n = fun _ => True by
        funext b
        simp [pairEventAlt], pmfProb_true]
    rw [hval]
    norm_num

/-! ## 3. The positive pool loss of the pair witness -/

/-- The per-draw hit probability of the witness is exactly `1/2`. -/
theorem hitProb_coin (n : ℕ) :
    hitProb (fun _ : ℕ => coinPMF) (fun _ _ => True) witnessHeight (1 / 8) n = 1 / 2 := by
  unfold hitProb
  have hfun : (fun b : Bool =>
      (fun _ _ => True) n b ∧ (1 / 8 : ℝ) / 2 ≤ witnessHeight n b) =
      fun b : Bool => (1 / 16 : ℝ) ≤ if b then (1 / 2 : ℝ) else 0 := by
    funext b
    cases b <;> norm_num [witnessHeight]
  rw [hfun]
  have hden : pmfProb coinPMF (fun _ : Bool => True) = 1 := pmfProb_true _
  rw [hden, pmfProb_coin_height_ge]
  norm_num

/-- The corrected pair loss is a strictly positive power of `1/2` at every
scale. -/
theorem witnessPair_loss_pos (n : ℕ) : 0 < witnessPair.toPairData.loss n := by
  rw [pairLoss_eq_poolLoss witnessPair n]
  unfold poolLoss
  have hμ : witnessPair.μ = fun _ : ℕ => coinPMF := rfl
  have hZ : witnessPair.Z = witnessHeight := rfl
  have ha : witnessPair.a = 1 / 8 := rfl
  have hcard : witnessPair.dyadCard = fun _ => 1 := rfl
  have hgood : witnessPair.good = fun (_ : ℕ) (_ : Bool) => True := rfl
  have hroot : witnessPair.childRoot = fun (_ : ℕ) (b : Bool) => b = true := rfl
  rw [hμ, hZ, ha, hcard, hgood, hroot]
  have hfun : (fun m : ℕ => pairEventAlt (fun (_ : ℕ) (_ : Bool) => True)
      (fun (_ : ℕ) (b : Bool) => b = true) m) = fun (_ : ℕ) (_ : Bool) => True := by
    funext m b
    simp [pairEventAlt]
  rw [hfun, hitProb_coin n]
  have hhalf : (0 : ℝ) < 1 - 1 / 2 := by norm_num
  simpa using pow_pos hhalf (witnessPair.poolSize n)

/-! ## 4. The concrete dyad data -/

/-- The size of the witness dyad at scale `n`. -/
def witnessDyadCard (n : ℕ) : ℕ := Nat.ceil (Real.exp ((scale n) ^ 2)) + 1

/-- The witness dyad: the first `witnessDyadCard n` integers. -/
def witnessDyadSet (n : ℕ) : Finset ℕ := Finset.range (witnessDyadCard n)

/-- The single bad point carries the explicitly positive mass
`exp (scale) + exp (-scale) + 2`.  This is positive at every scale and strictly
exceeds the trimming threshold `exp (-scale)`. -/
def witnessDyadErr (n : ℕ) (p : ℕ) : ℝ :=
  if p = 0 then Real.exp (scale n) + Real.exp (-(scale n)) + 2 else 0

/-- The dyad average. -/
def witnessDyadAvg (n : ℕ) : ℝ :=
  (Real.exp (scale n) + Real.exp (-(scale n)) + 2) / (witnessDyadCard n : ℝ)

theorem witnessDyadCard_pos (n : ℕ) : 0 < witnessDyadCard n := by
  unfold witnessDyadCard
  omega

theorem witnessDyadErr_nonneg (n p : ℕ) : 0 ≤ witnessDyadErr n p := by
  unfold witnessDyadErr
  split_ifs
  · have h1 := Real.exp_pos (scale n)
    have h2 := Real.exp_pos (-(scale n))
    linarith
  · norm_num

theorem sum_witnessDyadErr (n : ℕ) :
    (∑ p ∈ witnessDyadSet n, witnessDyadErr n p) =
      Real.exp (scale n) + Real.exp (-(scale n)) + 2 := by
  have hm : 0 < witnessDyadCard n := witnessDyadCard_pos n
  have hmem : 0 ∈ witnessDyadSet n := by
    simp [witnessDyadSet, hm]
  refine Finset.sum_eq_single 0 ?_ ?_
  · intro p _ hp
    simp [witnessDyadErr, hp]
  · intro h
    exact absurd hmem h

theorem witnessDyadAvg_def (n : ℕ) :
    witnessDyadAvg n =
      (∑ p ∈ witnessDyadSet n, witnessDyadErr n p) /
        ((witnessDyadSet n).card : ℝ) := by
  rw [sum_witnessDyadErr]
  simp [witnessDyadAvg, witnessDyadSet]

/-- The dyad average is `D^{-B}` for every `B`. -/
theorem witnessDyadAvg_subexp : SubexpLoss witnessDyadAvg := by
  intro B hB
  filter_upwards [scale_grows.eventually_ge_atTop (max (B + 2) 2)] with n hn
  have hB1 : B + 2 ≤ scale n := (le_max_left _ _).trans hn
  have h2 : 2 ≤ scale n := (le_max_right _ _).trans hn
  have hs0 : 0 ≤ scale n := by linarith
  have hmpos : (0 : ℝ) < (witnessDyadCard n : ℝ) := by
    exact_mod_cast witnessDyadCard_pos n
  have hmge : Real.exp ((scale n) ^ 2) ≤ (witnessDyadCard n : ℝ) := by
    have h := Nat.le_ceil (Real.exp ((scale n) ^ 2))
    unfold witnessDyadCard
    push_cast
    linarith
  have hexpneg : Real.exp (-(scale n)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexppos : 1 ≤ Real.exp (scale n) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hs0
  have hnum : Real.exp (scale n) + Real.exp (-(scale n)) + 2 ≤
      4 * Real.exp (scale n) := by
    nlinarith [hexpneg, hexppos]
  have hstep : witnessDyadAvg n ≤
      4 * Real.exp (scale n) / Real.exp ((scale n) ^ 2) := by
    unfold witnessDyadAvg
    calc
      (Real.exp (scale n) + Real.exp (-(scale n)) + 2) / (witnessDyadCard n : ℝ) ≤
          (4 * Real.exp (scale n)) / (witnessDyadCard n : ℝ) := by
            exact div_le_div_of_nonneg_right hnum (le_of_lt hmpos)
      _ ≤ 4 * Real.exp (scale n) / Real.exp ((scale n) ^ 2) := by
            exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hmge
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have hpow : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [hpow, Real.log_pow]
    push_cast
    nlinarith
  have hcomb : 4 * Real.exp (scale n) / Real.exp ((scale n) ^ 2) =
      Real.exp (Real.log 4 + (scale n - (scale n) ^ 2)) := by
    calc
      4 * Real.exp (scale n) / Real.exp ((scale n) ^ 2) =
          Real.exp (Real.log 4) * Real.exp (scale n) / Real.exp ((scale n) ^ 2) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ = Real.exp (Real.log 4 + scale n) / Real.exp ((scale n) ^ 2) := by
            rw [← Real.exp_add]
      _ = Real.exp ((Real.log 4 + scale n) - (scale n) ^ 2) := by
            rw [← Real.exp_sub]
      _ = Real.exp (Real.log 4 + (scale n - (scale n) ^ 2)) := by
            congr 1
            ring
  have hquad : Real.log 4 ≤ (scale n) ^ 2 - (B + 1) * scale n := by
    have hfac : (B + 1) * scale n + scale n ≤ (scale n) ^ 2 := by
      have : (B + 1) ≤ scale n - 1 := by linarith
      nlinarith [hs0, this]
    have hslog : Real.log 4 ≤ scale n := by linarith
    linarith
  calc
    witnessDyadAvg n ≤ 4 * Real.exp (scale n) / Real.exp ((scale n) ^ 2) := hstep
    _ = Real.exp (Real.log 4 + (scale n - (scale n) ^ 2)) := hcomb
    _ ≤ Real.exp (-B * scale n) := by
        apply Real.exp_le_exp.mpr
        linarith

/-- The witness dyad data. -/
def witnessDyad : DyadData ℕ where
  dyad := witnessDyadSet
  err := witnessDyadErr
  err_nonneg := witnessDyadErr_nonneg
  avg := witnessDyadAvg
  avg_def := witnessDyadAvg_def
  avg_subexp := witnessDyadAvg_subexp

/-- The single bad point makes the Markov-trimmed fraction strictly positive. -/
theorem witnessDyad_loss_pos (n : ℕ) : 0 < witnessDyad.loss n := by
  have hm : 0 < witnessDyadCard n := witnessDyadCard_pos n
  have hmem : 0 ∈ witnessDyad.bad n := by
    unfold DyadData.bad badSet badDyadPrimes witnessDyad
    simp only [Finset.mem_filter]
    refine ⟨by simp [witnessDyadSet, hm], ?_⟩
    left
    have hexp : 0 < Real.exp (scale n) := Real.exp_pos _
    simp only [witnessDyadErr, if_true]
    have harg : -(1 : ℝ) * scale n = -scale n := by ring
    rw [harg]
    nlinarith
  unfold DyadData.loss dyadLoss
  have hden : ((witnessDyad.dyad n).card : ℝ) = (witnessDyadCard n : ℝ) := by
    simp [witnessDyad, witnessDyadSet]
  rw [hden]
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr ⟨0, hmem⟩)
    (by exact_mod_cast hm)

/-! ## 5. The concrete top data -/

/-- The positive top/interior mass `exp (-(scale)²)`. -/
def witnessTopMass (n : ℕ) : ℝ := Real.exp (-((scale n) ^ 2))

theorem witnessTopMass_pos (n : ℕ) : 0 < witnessTopMass n :=
  Real.exp_pos _

theorem witnessTopMass_nonneg (n : ℕ) : 0 ≤ witnessTopMass n :=
  (witnessTopMass_pos n).le

theorem witnessTopMass_le_one (n : ℕ) : witnessTopMass n ≤ 1 := by
  rw [witnessTopMass]
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg (scale n)]

theorem witnessTopMass_subexp : SubexpLoss witnessTopMass := by
  intro B hB
  filter_upwards [scale_grows.eventually_ge_atTop (max B 0)] with n hn
  have hBle : B ≤ scale n := (le_max_left _ _).trans hn
  have hs0 : 0 ≤ scale n := (le_max_right _ _).trans hn
  rw [witnessTopMass]
  apply Real.exp_le_exp.mpr
  have hmul : B * scale n ≤ (scale n) ^ 2 := by
    nlinarith [hBle, hs0]
  nlinarith

/-- For `0 ≤ t ≤ 1`, `t ≤ √t`. -/
theorem self_le_sqrt_of_mem (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ≤ Real.sqrt t := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [h0, h1]

/-- The concrete additive top data: depth zero, unit step, and the four
interior/exception masses equal to `exp (-(scale)²)`. -/
def witnessTop : TopG12AdditiveData where
  L := 0
  interior := fun n _ => witnessTopMass n
  step := fun _ => 1
  eta := witnessTopMass
  epsRat := witnessTopMass
  epsIn := witnessTopMass
  top := witnessTopMass
  Ctop := fun _ => 1
  cTop := 0
  cInt := 0
  interior_nonneg := by
    intro n i
    exact witnessTopMass_nonneg n
  eta_nonneg := witnessTopMass_nonneg
  epsRat_nonneg := witnessTopMass_nonneg
  epsIn_nonneg := witnessTopMass_nonneg
  top_nonneg := witnessTopMass_nonneg
  Ctop_nonneg := by intro n; norm_num
  cTop_nonneg := le_rfl
  recurrence := by
    refine Eventually.of_forall fun n i hi => ?_
    omega
  step_ge_one := by
    refine Eventually.of_forall fun n => ?_
    norm_num
  alpha_nonneg := by
    refine Eventually.of_forall fun n => ?_
    exact add_nonneg (witnessTopMass_nonneg n) (witnessTopMass_nonneg n)
  depth_bound := by
    refine Eventually.of_forall fun n => ?_
    simp
  additive_comparison := by
    refine Eventually.of_forall fun n => ?_
    have ht0 : 0 ≤ witnessTopMass n := witnessTopMass_nonneg n
    have ht1 : witnessTopMass n ≤ 1 := witnessTopMass_le_one n
    have hle : witnessTopMass n ≤ Real.sqrt (witnessTopMass n) :=
      self_le_sqrt_of_mem _ ht0 ht1
    have hsq : 0 ≤ Real.sqrt (witnessTopMass n) := Real.sqrt_nonneg _
    simp only [Nat.cast_zero, pow_zero, one_mul, zero_mul, add_zero]
    nlinarith [hle, hsq]
  Ctop_le := by
    refine Eventually.of_forall fun n => ?_
    simp
  base_subexp := by
    change SubexpLoss witnessTopMass
    exact witnessTopMass_subexp
  eta_subexp := witnessTopMass_subexp
  epsRat_subexp := witnessTopMass_subexp
  epsIn_subexp := witnessTopMass_subexp

/-! ## 6. The fully concrete leaf -/

/-- The assembled L20.4 leaf with every field concrete. -/
def concreteLeaf : L20_4LeafInputs Bool ℕ where
  pair := witnessPair
  top := witnessTop
  dyad := witnessDyad

/-- Every summand of the assembled loss is strictly positive. -/
theorem concreteLeaf_loss_pos (n : ℕ) : 0 < concreteLeaf.loss n := by
  unfold L20_4LeafInputs.loss
  exact add_pos (add_pos (witnessPair_loss_pos n) (witnessDyad_loss_pos n))
    (witnessTopMass_pos n)

/-- The concrete assembled loss is nonzero at every scale. -/
theorem concreteLeaf_loss_ne_zero (n : ℕ) : concreteLeaf.loss n ≠ 0 :=
  ne_of_gt (concreteLeaf_loss_pos n)

/-- The concrete leaf satisfies the L20.4 manuscript subexponential bound. -/
theorem concreteLeaf_subexpLoss : SubexpLoss concreteLeaf.loss :=
  concreteLeaf.subexpLoss

/-- The `B = 2` ledger slot for the concrete leaf. -/
theorem concreteLeaf_slot :
    ∀ᶠ n : ℕ in atTop, concreteLeaf.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  concreteLeaf.slot_le

/-! ## 7. A concrete L20.2 interior input

The L20.2 input is built from a one-point outcome space.  There are
`μ = ⌈exp (D log D)⌉ + 1` interior points, the actual score is `1`, and the
proxy score is `1 - ε` with `ε = min (√ρ) (1/2)` and `ρ = 2 exp (-2 D log D)`.
Hence the base discrepancy is the strictly positive `ε`, while the off-diagonal
cross term is `μ (μ - 1) ε² ≤ ρ μ²`, exactly the L20.2 budget. -/

/-- The L20.2 CRT budget `exp (-2 D log D)`. -/
def witnessCrt (n : ℕ) : ℝ := Real.exp (-(2 : ℝ) * paperD n * scale n)

/-- The total exception budget `ρ = crt + char`, with both summands equal to the
CRT budget. -/
def witnessRho (n : ℕ) : ℝ := witnessCrt n + witnessCrt n

/-- The positive discrepancy `ε = min (√ρ) (1/2)`. -/
def witnessEps (n : ℕ) : ℝ := min (Real.sqrt (witnessRho n)) (1 / 2)

/-- The number of interior points `μ = ⌈exp (D log D)⌉ + 1`. -/
def witnessMu (n : ℕ) : ℕ := Nat.ceil (Real.exp (paperD n * scale n)) + 1

theorem witnessCrt_pos (n : ℕ) : 0 < witnessCrt n := Real.exp_pos _

theorem witnessRho_pos (n : ℕ) : 0 < witnessRho n := by
  unfold witnessRho
  have h := witnessCrt_pos n
  linarith

theorem witnessRho_nonneg (n : ℕ) : 0 ≤ witnessRho n := (witnessRho_pos n).le

theorem witnessEps_nonneg (n : ℕ) : 0 ≤ witnessEps n := by
  unfold witnessEps
  exact le_min (Real.sqrt_nonneg _) (by norm_num)

theorem witnessEps_le_half (n : ℕ) : witnessEps n ≤ 1 / 2 := by
  unfold witnessEps
  exact min_le_right _ _

theorem witnessEps_pos (n : ℕ) : 0 < witnessEps n := by
  unfold witnessEps
  exact lt_min (Real.sqrt_pos.2 (witnessRho_pos n)) (by norm_num)

theorem witnessEps_sq_le (n : ℕ) : (witnessEps n) ^ 2 ≤ witnessRho n := by
  unfold witnessEps
  by_cases h : Real.sqrt (witnessRho n) ≤ 1 / 2
  · rw [min_eq_left h, Real.sq_sqrt (witnessRho_nonneg n)]
  · have h2 : (1 / 2 : ℝ) ≤ Real.sqrt (witnessRho n) := le_of_not_ge h
    have hs : (0 : ℝ) ≤ Real.sqrt (witnessRho n) := Real.sqrt_nonneg _
    have hsq : (Real.sqrt (witnessRho n)) ^ 2 = witnessRho n :=
      Real.sq_sqrt (witnessRho_nonneg n)
    rw [min_eq_right h2]
    nlinarith [h2, hs, hsq]

theorem witnessMu_pos (n : ℕ) : 0 < witnessMu n := by
  unfold witnessMu
  omega

/-- The concrete L20.2 cell. -/
@[reducible] def witnessCell (n : ℕ) : CellData n 1 where
  Ω := PUnit
  fintypeΩ := inferInstance
  w := fun _ => 1
  w_nonneg := by intro _; norm_num
  w_sum := by simp
  P := Fin (witnessMu n)
  fintypeP := inferInstance
  decEqP := inferInstance
  f := fun _ _ => 1
  proxy := fun _ _ => 1 - witnessEps n
  f_nonneg := by intro _ _; norm_num
  f_le_one := by intro _ _; norm_num
  proxy_nonneg := by
    intro _ _
    have h := witnessEps_le_half n
    linarith
  proxy_le := by
    intro _ _
    have h := witnessEps_nonneg n
    linarith

theorem witnessCell_mean_f (n : ℕ) :
    (witnessCell n).mean (witnessCell n).f = (witnessMu n : ℝ) := by
  simp [CellData.mean, witnessCell]

theorem witnessCell_mean_proxy (n : ℕ) :
    (witnessCell n).mean (witnessCell n).proxy =
      (witnessMu n : ℝ) * (1 - witnessEps n) := by
  simp [CellData.mean, witnessCell]
  ring

theorem witnessCell_one_point (n : ℕ) :
    (witnessCell n).mean (witnessCell n).proxy ≤ 2 * (witnessMu n : ℝ) := by
  rw [witnessCell_mean_proxy]
  have hm : (0 : ℝ) ≤ (witnessMu n : ℝ) := Nat.cast_nonneg _
  have he : 0 ≤ witnessEps n := witnessEps_nonneg n
  nlinarith

theorem witnessCell_cross_eq (n : ℕ) :
    (witnessCell n).cross =
      ∑ p : Fin (witnessMu n),
        ∑ _q ∈ Finset.univ.erase p, (witnessEps n) ^ 2 := by
  simp [CellData.cross, witnessCell]
  ring_nf
  simp

theorem witnessCell_cross_le (n : ℕ) :
    (witnessCell n).cross ≤ witnessRho n * (witnessMu n : ℝ) ^ 2 := by
  rw [witnessCell_cross_eq]
  have heps : (witnessEps n) ^ 2 ≤ witnessRho n := witnessEps_sq_le n
  have hm : (0 : ℝ) ≤ (witnessMu n : ℝ) := Nat.cast_nonneg _
  calc
    (∑ p : Fin (witnessMu n),
        ∑ _q ∈ Finset.univ.erase p, (witnessEps n) ^ 2)
        ≤ ∑ _p : Fin (witnessMu n),
            ∑ _q : Fin (witnessMu n), (witnessEps n) ^ 2 := by
          apply Finset.sum_le_sum
          intro p _
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun q _ _ => sq_nonneg _)
    _ = (witnessMu n : ℝ) * ((witnessMu n : ℝ) * (witnessEps n) ^ 2) := by
          simp [Finset.sum_const]
    _ = (witnessEps n) ^ 2 * (witnessMu n : ℝ) ^ 2 := by ring
    _ ≤ witnessRho n * (witnessMu n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right heps (sq_nonneg _)

theorem witnessCell_two_point (n : ℕ) :
    (witnessCell n).cross ≤ (witnessCrt n + witnessCrt n) * (witnessMu n : ℝ) ^ 2 := by
  have h := witnessCell_cross_le n
  have hrho : witnessRho n = witnessCrt n + witnessCrt n := rfl
  rwa [hrho] at h

/-- The concrete L20.2 interior input. -/
def witnessL20_2 : L20_2Inputs where
  a := 1 / 48
  a_eq := rfl
  Λ := fun n => paperD n * scale n
  μ := fun n => (witnessMu n : ℝ)
  L := fun _ => 1
  crtError := witnessCrt
  charError := witnessCrt
  cLam := 1
  η := 1
  cCRT := 2
  cChar := 2
  cL := 0
  saddle_scale := by
    refine ⟨by norm_num, fun n => ?_⟩
    simp
  saddle_mean := by
    refine ⟨by norm_num, fun n => ?_⟩
    have h := Nat.le_ceil (Real.exp (paperD n * scale n))
    have h' : (Nat.ceil (Real.exp (paperD n * scale n)) : ℝ) ≤
        (witnessMu n : ℝ) := by
      unfold witnessMu
      push_cast
      linarith
    have hexp : Real.exp (1 * (paperD n * scale n)) =
        Real.exp (paperD n * scale n) := by
      congr 1
      ring
    rw [hexp]
    exact h.trans h'
  L_nonneg := by intro n; norm_num
  cL_nonneg := by norm_num
  L_upper := by intro n; simp
  crt_law := ⟨by norm_num, fun n => ⟨(witnessCrt_pos n).le, le_rfl⟩⟩
  char_sum := ⟨by norm_num, fun n => ⟨(witnessCrt_pos n).le, le_rfl⟩⟩
  cell := witnessCell
  μ_eq := fun n => (witnessCell_mean_f n).symm
  one_point := fun n => witnessCell_one_point n
  two_point := fun n => witnessCell_two_point n

theorem witnessL20_2_loss_eq (n : ℕ) :
    witnessL20_2.loss n = witnessEps n := by
  unfold L20_2Inputs.loss
  change |(witnessCell n).mean (witnessCell n).f -
      (witnessCell n).mean (witnessCell n).proxy| / (witnessMu n : ℝ) = witnessEps n
  rw [witnessCell_mean_f, witnessCell_mean_proxy]
  have hm : (0 : ℝ) < (witnessMu n : ℝ) := by
    exact_mod_cast witnessMu_pos n
  have he : 0 ≤ witnessEps n := witnessEps_nonneg n
  have hdiff : (witnessMu n : ℝ) - (witnessMu n : ℝ) * (1 - witnessEps n) =
      (witnessMu n : ℝ) * witnessEps n := by ring
  rw [hdiff, abs_of_nonneg (mul_nonneg hm.le he)]
  field_simp [hm.ne']

theorem witnessL20_2_loss_pos (n : ℕ) : 0 < witnessL20_2.loss n := by
  rw [witnessL20_2_loss_eq]
  exact witnessEps_pos n

theorem witnessL20_2_subexp : SubexpLoss witnessL20_2.loss :=
  loss_subexp_of_L20_2 witnessL20_2

/-! ### The concrete exception sources -/

/-- The base source: the G.11 base mass is the concrete normalized L20.2
discrepancy, which is the positive `ε` above. -/
theorem witness_base_source :
    BaseConcentrationSource (concentrationBase witnessL20_2) 0 witnessL20_2 :=
  baseConcentrationSource_concrete witnessL20_2 0

/-- The rational source: `ε_rat` is the literal CRT plus smooth-character
budget `ρ = crtError + charError`. -/
theorem witness_rational_source :
    RationalExceptionSource (paperEpsRat witnessL20_2) witnessL20_2 :=
  rationalExceptionSource_paper witnessL20_2

/-- The incoming source: `ε_in` is the same CRT plus smooth-character
budget. -/
theorem witness_incoming_source :
    IncomingExceptionSource (paperEpsIn witnessL20_2) witnessL20_2 :=
  incomingExceptionSource_paper witnessL20_2

/-- The elliptic source: the deletion fraction is the L21.2 loss. -/
theorem witness_eta_source (E : Cogentic.RandomizedL21_2.L21_2Inputs) :
    EllipticFromL21_2 (fun n => E.loss n) E :=
  fun _ => rfl

/-- The full paper exception-source bundle, with only the elliptic input free. -/
def witness_exception_sources (E : Cogentic.RandomizedL21_2.L21_2Inputs) :
    PaperExceptionSources (concentrationBase witnessL20_2) 0 (fun n => E.loss n) :=
  paperExceptionSources witnessL20_2 witnessL20_2 witnessL20_2 E 0

/-! ## 8. The sourced top data from one elliptic input

All fields except the `L21_2Inputs` are explicit.  The base, rational and
incoming L20.2 inputs are the concrete `witnessL20_2`; the elliptic fraction is
`E.loss`; the top mass is `√(base loss)/2`, which is positive and satisfies the
additive comparison trivially. -/

/-- The top bad-child mass built from the concrete L20.2 base loss. -/
def sourcedTopMass (n : ℕ) : ℝ := Real.sqrt (witnessL20_2.loss n) / 2

theorem sourcedTopMass_pos (n : ℕ) : 0 < sourcedTopMass n := by
  unfold sourcedTopMass
  have h := Real.sqrt_pos.2 (witnessL20_2_loss_pos n)
  linarith

theorem sourcedTopMass_nonneg (n : ℕ) : 0 ≤ sourcedTopMass n :=
  (sourcedTopMass_pos n).le

/-- The sourced top data, with the sole free input an `L21_2Inputs`. -/
def sourcedTopOfElliptic (E : Cogentic.RandomizedL21_2.L21_2Inputs) : SourcedTopData where
  L := 0
  interior := concentrationBase witnessL20_2
  step := fun _ => 1
  eta := fun n => E.loss n
  exceptions := paperExceptionSources witnessL20_2 witnessL20_2 witnessL20_2 E 0
  top := sourcedTopMass
  Ctop := fun _ => 1
  cTop := 0
  cInt := 0
  interior_nonneg := by
    intro n i
    exact witnessL20_2.loss_nonneg n
  eta_nonneg := by
    intro n
    exact E.loss_nonneg n
  top_nonneg := sourcedTopMass_nonneg
  Ctop_nonneg := by intro n; norm_num
  cTop_nonneg := le_rfl
  recurrence := by
    refine Eventually.of_forall fun n i hi => ?_
    omega
  step_ge_one := by
    refine Eventually.of_forall fun n => ?_
    norm_num
  alpha_nonneg := by
    refine Eventually.of_forall fun n => ?_
    exact add_nonneg (E.loss_nonneg n) (paperEpsRat_nonneg witnessL20_2 n)
  depth_bound := by
    refine Eventually.of_forall fun n => ?_
    simp
  additive_comparison := by
    refine Eventually.of_forall fun n => ?_
    simp only [sourcedTopMass, concentrationBase, paperExceptionSources,
      Nat.cast_zero, pow_zero, one_mul, zero_mul, add_zero]
    have hs : 0 ≤ Real.sqrt (witnessL20_2.loss n) := Real.sqrt_nonneg _
    have hsin : 0 ≤ Real.sqrt (paperEpsIn witnessL20_2 n) := Real.sqrt_nonneg _
    have heta : 0 ≤ E.loss n := E.loss_nonneg n
    change Real.sqrt (witnessL20_2.loss n) / 2 ≤
      Real.sqrt (witnessL20_2.loss n) + Real.sqrt (paperEpsIn witnessL20_2 n) +
        E.loss n
    linarith
  Ctop_le := by
    refine Eventually.of_forall fun n => ?_
    simp

/-- The full sourced leaf, with every field explicit once an `L21_2Inputs` is
supplied. -/
def sourcedLeafOfElliptic (E : Cogentic.RandomizedL21_2.L21_2Inputs) :
    L20_4SourcedLeafInputs Bool ℕ where
  pair := witnessPair
  top := sourcedTopOfElliptic E
  dyad := witnessDyad

theorem sourcedLeafOfElliptic_loss_pos
    (E : Cogentic.RandomizedL21_2.L21_2Inputs) (n : ℕ) :
    0 < (sourcedLeafOfElliptic E).loss n := by
  unfold L20_4SourcedLeafInputs.loss
  exact add_pos (add_pos (witnessPair_loss_pos n) (witnessDyad_loss_pos n))
    (sourcedTopMass_pos n)

theorem sourcedLeafOfElliptic_subexpLoss
    (E : Cogentic.RandomizedL21_2.L21_2Inputs) :
    SubexpLoss (sourcedLeafOfElliptic E).loss :=
  (sourcedLeafOfElliptic E).subexpLoss

/-- **The exact weakening.**  The sourced leaf is inhabited as soon as one
`L21_2Inputs` is supplied; the only residual field of
`SourcedTopData.exceptions` is its `elliptic` component. -/
theorem nonempty_sourcedLeafInputs_of_L21_2
    (E : Cogentic.RandomizedL21_2.L21_2Inputs) :
    Nonempty (L20_4SourcedLeafInputs Bool ℕ) :=
  ⟨sourcedLeafOfElliptic E⟩

/-- The fully concrete leaf is a `L20_4SourcedLeafInputs` with the sourced top
data weakened to its `TopG12AdditiveData` image. -/
theorem concreteLeaf_toLeafInputs :
    Nonempty (L20_4LeafInputs Bool ℕ) :=
  ⟨concreteLeaf⟩

/-- **Residual-field list.**  Everything in `L20_4SourcedLeafInputs` is
constructed below except the elliptic `L21_2Inputs` appearing in
`PaperExceptionSources`. -/
def residualFields : List String :=
  [ "PaperExceptionSources.elliptic : RandomizedL21_2.L21_2Inputs" ]

theorem residualFields_nonempty : residualFields ≠ [] := by
  simp [residualFields]

/-- **Structural checks at `n = 0`.**  The scale vanishes there, so the
constant-vs-growing pool inequality becomes `1 ≤ poolSize 0`. -/
theorem scale_zero : scale 0 = 0 := by
  simp [scale]

theorem event_pos_zero :
    0 < pmfProb coinPMF
      (pairEventAlt (fun _ _ => True) (fun _ b => b = true) 0) :=
  witnessPair.event_pos 0

theorem witnessEps_pos_zero : 0 < witnessEps 0 := witnessEps_pos 0

theorem witnessMu_pos_zero : 0 < witnessMu 0 := witnessMu_pos 0

theorem witnessDyadCard_pos_zero : 0 < witnessDyadCard 0 := witnessDyadCard_pos 0

theorem witnessTopMass_nonneg_zero : 0 ≤ witnessTopMass 0 := witnessTopMass_nonneg 0

theorem witnessPair_poolSize_zero : witnessPair.poolSize 0 = 2 := by
  simp [witnessPair, scale_zero, Nat.ceil_one]

theorem poolSize_ge_zero :
    Real.exp ((0 + 0 + 0 + 0 + 2 : ℝ) * scale 0) ≤
      (witnessPair.poolSize 0 : ℝ) := by
  rw [scale_zero, witnessPair_poolSize_zero]
  norm_num

/-- The exact weakening map: forgetting the sourced exceptions of
`SourcedTopData` produces the plain `L20_4LeafInputs`. -/
def sourcedToLeaf (S : L20_4SourcedLeafInputs Bool ℕ) : L20_4LeafInputs Bool ℕ :=
  S.toLeafInputs

/-! ## Axiom audit -/

#print axioms witnessPair
#print axioms witnessPair_loss_pos
#print axioms witnessDyad
#print axioms witnessDyad_loss_pos
#print axioms witnessL20_2
#print axioms witnessL20_2_loss_pos
#print axioms witnessL20_2_subexp
#print axioms witness_base_source
#print axioms witness_rational_source
#print axioms witness_incoming_source
#print axioms witness_eta_source
#print axioms witness_exception_sources
#print axioms witnessTop
#print axioms concreteLeaf
#print axioms concreteLeaf_loss_pos
#print axioms concreteLeaf_subexpLoss
#print axioms concreteLeaf_slot
#print axioms sourcedTopOfElliptic
#print axioms sourcedLeafOfElliptic
#print axioms sourcedLeafOfElliptic_loss_pos
#print axioms sourcedLeafOfElliptic_subexpLoss
#print axioms nonempty_sourcedLeafInputs_of_L21_2
#print axioms poolSize_ge_zero

#check sourcedToLeaf
#check witnessPair
#check witnessDyad
#check witnessL20_2
#check witnessTop
#check concreteLeaf
#check sourcedTopOfElliptic
#check sourcedLeafOfElliptic
#check witness_exception_sources
#check nonempty_sourcedLeafInputs_of_L21_2

end

end Cogentic.RandomizedL20_4SourceWitness
