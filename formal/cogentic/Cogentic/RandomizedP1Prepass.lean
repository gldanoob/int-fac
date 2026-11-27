import Cogentic.RandomizedP1Analytic

/-!
# P1 prepass: the honest subexponential cost interface and the trial-division gap

`Cogentic/RandomizedP1.lean` reduces the manuscript's P1 prepass to a success
statement and an `exp (o (H))` cost statement.  This file isolates the cost side
in the smallest explicit form that the endpoint can consume:

```text
cost n ≤ exp (ε_n * scale n),      ε_n → 0.
```

The point is that this is *strictly stronger* than the existing `P1Leaf` cost
field: `P1Leaf.cost_sublinear` only says that a chosen exponent is eventually
below every fixed multiple of `scale`, while the sequence `ε_n` here is a single
rate that tends to zero.  The two formulations are equivalent for monotone
envelopes, but the sequence form is the honest statement of `exp (o (H))` and is
the form in which the trial-division gap is visible.

## Main results

* `SubexpPrepassInput` — miss probability with `PrepassSuccess`, an explicit
  prepass cost, and a `SubexpCostRate cost`, i.e. a nonnegative sequence
  `ε_n → 0` with `cost n ≤ exp (ε_n * scale n)` eventually.  No loss is set to
  zero and no cost is set to zero.
* `SubexpPrepassInput.toP1Leaf` — the bundle gives the paper's `P1Leaf`, and
  `SubexpPrepassInput.discharges_P1Leaf_slot` is exactly the C5 loss slot
  `loss ≤ exp (-2 * scale n)` that `PaperAnalyticAssumptions.slot_le` consumes
  for `C5Leaf.prepass`.
* `genusTwoSubexpPrepassInput` and `ecmSubexpPrepassInput` — the genuine
  subexponential prepasses (KB Proposition H.3 and LP Theorem 7.1) supply the
  input, using only their already-formalized `exp (o (H))` cost envelopes.
* `eventually_exp_eps_scale_lt_roughThreshold` — the super-scale separation:
  every budget `exp (ε_n * scale n)` with `ε_n → 0` is eventually *below* the
  paper cutoff `roughThreshold n = exp ((log n)^{2/3})`.
* `trialDivisionCost` and `trialDivision_not_subexpRate` — the concrete counted
  trial-division cost at `roughThreshold` is `≥ roughThreshold`, so it beats
  every such budget eventually and cannot carry a `SubexpCostRate`.  Hence no
  `SubexpPrepassInput` can have trial-division cost, which is the explicit
  numerical form of the audit's `P1` gap.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedP1Prepass

open Filter Real
open Cogentic.RandomizedP1
open Cogentic.RandomizedP1Sub
open Cogentic.RandomizedP1Analytic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSmallPrimePrepass
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub

noncomputable section

/-! ## 1. The explicit subexponential cost rate -/

/-- **The cost-rate interface.**  A nonnegative sequence `ε_n → 0` such that
`cost n ≤ exp (ε_n * scale n)` eventually.  This is the explicit
`exp (o (H))` statement, with the little-o rate named rather than hidden inside
a fixed-slack quantifier. -/
structure SubexpCostRate (cost : ℕ → ℝ) where
  /-- The rate `ε_n` in the budget `exp (ε_n * scale n)`. -/
  eps : ℕ → ℝ
  /-- The rate is nonnegative. -/
  eps_nonneg : ∀ n, 0 ≤ eps n
  /-- The rate tends to zero. -/
  eps_tendsto : Tendsto eps atTop (𝓝 0)
  /-- The cost is eventually within the budget. -/
  cost_le_exp : ∀ᶠ n : ℕ in atTop, cost n ≤ Real.exp (eps n * scale n)

/-- A helper: a sequence tending to zero is eventually below any positive
constant. -/
theorem eventually_lt_of_tendsto_zero {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, f n < c :=
  (tendsto_order.mp hf).2 c hc

/-- **The super-scale separation.**  Every subexponential budget
`exp (ε_n * scale n)` with `ε_n → 0` is eventually strictly below the paper's
rough cutoff `exp ((log n)^{2/3})`.  This is the quantitative form of
`scale = o ((log n)^{2/3})` and is the reason trial division at that cutoff
cannot be a subexponential prepass. -/
theorem eventually_exp_eps_scale_lt_roughThreshold
    {eps : ℕ → ℝ} (heps : Tendsto eps atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (eps n * scale n) < roughThreshold n := by
  have heps_half : ∀ᶠ n : ℕ in atTop, eps n < (1 / 2 : ℝ) :=
    eventually_lt_of_tendsto_zero heps (by norm_num)
  have hlogB : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ logB n :=
    logB_grows.eventually_ge_atTop 1
  filter_upwards [heps_half, eventually_scale_le_half_logB, hlogB,
    scale_grows.eventually_ge_atTop 0] with n hepsn hsc hb hs0
  have h1 : eps n * scale n ≤ (1 / 2 : ℝ) * scale n :=
    mul_le_mul_of_nonneg_right hepsn.le hs0
  have h2 : (1 / 2 : ℝ) * scale n ≤ (1 / 4 : ℝ) * logB n := by
    calc
      (1 / 2 : ℝ) * scale n ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) * logB n) :=
        mul_le_mul_of_nonneg_left hsc (by norm_num)
      _ = (1 / 4 : ℝ) * logB n := by ring
  have hlogB_pos : 0 < logB n := zero_lt_one.trans_le hb
  have h3 : (1 / 4 : ℝ) * logB n < logB n := by nlinarith only [hlogB_pos]
  have hlt : eps n * scale n < logB n :=
    lt_of_le_of_lt (le_trans h1 h2) h3
  unfold roughThreshold
  exact Real.exp_lt_exp.mpr hlt

/-! ## 2. The smallest explicit prepass input -/

/-- **The smallest explicit P1 prepass input.**  It carries exactly the two
paper-level statements the endpoint needs: the miss probability with the
manuscript success rate `PrepassSuccess`, and a cost with an explicit
subexponential rate.  There is no cutoff, work envelope, or polynomial overhead
field, because none of those is consumed by `P1Leaf`. -/
structure SubexpPrepassInput where
  /-- The prepass miss probability. -/
  miss : ℕ → ℝ
  /-- A failure probability is nonnegative. -/
  miss_nonneg : ∀ n, 0 ≤ miss n
  /-- **Success input** (KB Proposition H.3 / LP Theorem 7.1): for every
  `δ > 0`, the miss probability is eventually at most `exp (-δ H)`. -/
  success : PrepassSuccess miss
  /-- The prepass cost. -/
  cost : ℕ → ℝ
  /-- The cost is nonnegative. -/
  cost_nonneg : ∀ n, 0 ≤ cost n
  /-- **Cost input**: the cost is subexponential at an explicit rate. -/
  cost_subexp : SubexpCostRate cost

namespace SubexpPrepassInput

variable (I : SubexpPrepassInput)

/-- The success statement in the manuscript's `SubexpLoss` shape. -/
theorem subexpLoss : SubexpLoss I.miss := I.success

/-- The explicit `exp (o (H))` cost exponent selected from the input.  It is
`max 0 (ε_n * scale n)`, so it is nonnegative and still little-o of `scale`. -/
def costExponent : ℕ → ℝ := fun n => max 0 (I.cost_subexp.eps n * scale n)

/-- The selected exponent is nonnegative. -/
theorem costExponent_nonneg (n : ℕ) : 0 ≤ I.costExponent n :=
  le_max_left 0 _

/-- The selected exponent is eventually below every fixed multiple of `scale`. -/
theorem costExponent_sublinear :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      I.costExponent n ≤ δ * scale n := by
  intro δ hδ
  have heps : ∀ᶠ n : ℕ in atTop, I.cost_subexp.eps n ≤ δ :=
    (eventually_lt_of_tendsto_zero I.cost_subexp.eps_tendsto hδ).mono
      fun n hn => hn.le
  filter_upwards [heps, scale_grows.eventually_ge_atTop 0] with n he hs
  have hds : 0 ≤ δ * scale n := mul_nonneg hδ.le hs
  exact max_le hds (mul_le_mul_of_nonneg_right he hs)

/-- **The charged cost genuinely fits in `exp (costExponent)`.**  The selected
exponent is not a zero-cost placeholder: it dominates the input rate. -/
theorem cost_le_exp_costExponent :
    ∀ᶠ n : ℕ in atTop, I.cost n ≤ Real.exp (I.costExponent n) := by
  filter_upwards [I.cost_subexp.cost_le_exp] with n hle
  exact hle.trans (Real.exp_le_exp.mpr (le_max_right _ _))

/-- **The `P1Leaf` reduction.**  The loss is the input miss probability and the
cost exponent is the explicit rate `max 0 (ε_n * scale n)`; neither is replaced
by zero. -/
def toP1Leaf : P1Leaf where
  loss := I.miss
  loss_nonneg := I.miss_nonneg
  paper := I.subexpLoss
  costExponent := I.costExponent
  costExponent_nonneg := I.costExponent_nonneg
  cost_sublinear := I.costExponent_sublinear

/-- The `P1Leaf` loss is exactly the input miss probability. -/
theorem toP1Leaf_loss (n : ℕ) : I.toP1Leaf.loss n = I.miss n := rfl

/-- **The endpoint loss slot.**  The bundle discharges the `P1Leaf.slot` that
`PaperAnalyticAssumptions.slot_le` consumes for `C5Leaf.prepass`:
`loss ≤ exp (-2 * scale n)`. -/
theorem discharges_P1Leaf_slot :
    ∀ᶠ n : ℕ in atTop,
      I.toP1Leaf.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  I.toP1Leaf.slot

/-- The same statement stated directly on the input miss probability. -/
theorem slot :
    ∀ᶠ n : ℕ in atTop,
      I.miss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  I.success 2 (by norm_num)

end SubexpPrepassInput

/-! ## 3. Genuine subexponential prepasses: genus-two and ECM -/

/-- A local logarithm lemma: if `0 ≤ a ≤ exp b` and `0 ≤ b`, then
`log a ≤ b`.  The zero case uses `Real.log 0 = 0`. -/
theorem log_le_of_le_exp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ Real.exp b) : Real.log a ≤ b := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0, Real.log_zero]
    exact hb
  · exact (Real.log_le_iff_le_exp hapos).mpr h

/-- The canonical rate extracted from an `exp (o (H))` cost envelope:
`ε_n = max 0 (log (cost n) / scale n)`. -/
def subexpEps (cost : ℕ → ℝ) : ℕ → ℝ :=
  fun n => max 0 (Real.log (cost n) / scale n)

/-- The extracted rate is nonnegative. -/
theorem subexpEps_nonneg (cost : ℕ → ℝ) (n : ℕ) : 0 ≤ subexpEps cost n :=
  le_max_left 0 _

/-- **A cost envelope produces an explicit rate.**  If `cost` is nonnegative
and eventually at most `exp (δ H)` for every `δ > 0`, then
`ε_n = max 0 (log (cost n) / scale n)` tends to zero. -/
theorem subexpEps_tendsto {cost : ℕ → ℝ} (h : SubexpCostEnvelope cost) :
    Tendsto (subexpEps cost) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards with n
    exact lt_of_lt_of_le hb (subexpEps_nonneg cost n)
  · intro c hc
    have hc2 : 0 < c / 2 := by positivity
    filter_upwards [h.2 (c / 2) hc2, scale_grows.eventually_gt_atTop 0]
      with n hcost hs
    have hlog : Real.log (cost n) ≤ (c / 2) * scale n :=
      log_le_of_le_exp (h.1 n) (mul_nonneg hc2.le hs.le) hcost
    have hdiv : Real.log (cost n) / scale n ≤ c / 2 := by
      rw [div_le_iff₀ hs]
      exact hlog
    exact max_lt hc (by linarith)

/-- **The extracted rate bounds the cost.**  For a nonnegative cost envelope,
`cost n ≤ exp (ε_n * scale n)` eventually. -/
theorem subexpEps_bound {cost : ℕ → ℝ} (h : SubexpCostEnvelope cost) :
    ∀ᶠ n : ℕ in atTop,
      cost n ≤ Real.exp (subexpEps cost n * scale n) := by
  filter_upwards [scale_grows.eventually_gt_atTop 0] with n hs
  by_cases hzero : cost n = 0
  · rw [hzero]
    exact (Real.exp_pos _).le
  · have hpos : 0 < cost n := lt_of_le_of_ne (h.1 n) (Ne.symm hzero)
    have hle : Real.log (cost n) ≤ subexpEps cost n * scale n := by
      have hdiv : Real.log (cost n) / scale n ≤ subexpEps cost n :=
        le_max_right _ _
      have hmul := mul_le_mul_of_nonneg_right hdiv hs.le
      rwa [div_mul_cancel₀ _ hs.ne'] at hmul
    calc
      cost n = Real.exp (Real.log (cost n)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (subexpEps cost n * scale n) := Real.exp_le_exp.mpr hle

/-- **Every `exp (o (H))` cost envelope carries a `SubexpCostRate`.** -/
def subexpCostRateOfEnvelope {cost : ℕ → ℝ}
    (h : SubexpCostEnvelope cost) : SubexpCostRate cost where
  eps := subexpEps cost
  eps_nonneg := subexpEps_nonneg cost
  eps_tendsto := subexpEps_tendsto h
  cost_le_exp := subexpEps_bound h

/-- **The genus-two prepass gives a `SubexpPrepassInput`.**  Success is the
already-formalized H.3 failure bound (`l30PrepassSuccess`) and the cost is the
H.5 total cost with its `exp (o (H))` envelope.  The loss is the genuine
positive `L30Inputs.loss`, not zero. -/
def genusTwoSubexpPrepassInput (I : L30Inputs) : SubexpPrepassInput where
  miss := I.loss
  miss_nonneg := I.loss_nonneg
  success := l30PrepassSuccess I
  cost := I.totalCost
  cost_nonneg := I.totalCost_nonneg
  cost_subexp := subexpCostRateOfEnvelope (genusTwoCostEnvelope I)

/-- The genus-two input uses the actual H.5 total cost. -/
theorem genusTwoSubexpPrepassInput_cost (I : L30Inputs) :
    (genusTwoSubexpPrepassInput I).cost = I.totalCost := rfl

/-- The genus-two input discharges the endpoint's prepass loss slot. -/
theorem genusTwoPrepass_discharges_slot (I : L30Inputs) :
    ∀ᶠ n : ℕ in atTop,
      (genusTwoSubexpPrepassInput I).toP1Leaf.loss n ≤
        Real.exp (-(2 : ℝ) * scale n) :=
  (genusTwoSubexpPrepassInput I).discharges_P1Leaf_slot

/-- **The ECM prepass gives a `SubexpPrepassInput`** once its success statement
and its cost envelope are supplied.  This is the same interface as
`ecmAnalyticInputs`, with the polynomial work factor dropped because `P1Leaf`
does not consume it. -/
def ecmSubexpPrepassInput (I : L27_1Inputs)
    (hsuccess : PrepassSuccess I.loss) (cost : ℕ → ℝ)
    (hcost : SubexpCostEnvelope cost) : SubexpPrepassInput where
  miss := I.loss
  miss_nonneg := loss_nonneg_of I
  success := hsuccess
  cost := cost
  cost_nonneg := hcost.1
  cost_subexp := subexpCostRateOfEnvelope hcost

/-- The ECM input discharges the endpoint's prepass loss slot. -/
theorem ecmPrepass_discharges_slot (I : L27_1Inputs)
    (hsuccess : PrepassSuccess I.loss) (cost : ℕ → ℝ)
    (hcost : SubexpCostEnvelope cost) :
    ∀ᶠ n : ℕ in atTop,
      (ecmSubexpPrepassInput I hsuccess cost hcost).toP1Leaf.loss n ≤
        Real.exp (-(2 : ℝ) * scale n) :=
  (ecmSubexpPrepassInput I hsuccess cost hcost).discharges_P1Leaf_slot

/-! ## 4. The concrete trial-division cost is not subexponential -/

/-- The counted trial-division cost at the paper cutoff: the exponential of
`trialDivisionExponent`, i.e. `exp (log (54 · roughThreshold · n.size²))`. -/
def trialDivisionCost (n : ℕ) : ℝ :=
  Real.exp (trialDivisionExponent n)

/-- The trial-division cost is exactly the proved work envelope
`54 · roughThreshold n · n.size²` at every positive input. -/
theorem trialDivisionCost_eq_envelope (n : ℕ) (hn : 0 < n) :
    trialDivisionCost n = 54 * roughThreshold n * (n.size : ℝ) ^ 2 := by
  unfold trialDivisionCost
  have hpos : 0 < 54 * roughThreshold n * (n.size : ℝ) ^ 2 := by
    have hT : 0 < roughThreshold n := Real.exp_pos _
    have hs : 0 < (n.size : ℝ) := by
      exact_mod_cast Nat.size_pos.mpr hn
    positivity
  rw [trialDivisionExponent, Real.exp_log hpos]

/-- `roughThreshold` is a lower bound for the counted trial-division cost. -/
theorem eventually_roughThreshold_le_trialDivisionCost :
    ∀ᶠ n : ℕ in atTop, roughThreshold n ≤ trialDivisionCost n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hlog := logB_le_trialDivisionExponent n (by omega : 0 < n)
  unfold trialDivisionCost roughThreshold
  exact Real.exp_le_exp.mpr hlog

/-- **The explicit gap.**  Every subexponential budget `exp (ε_n * scale n)`
with `ε_n → 0` is eventually strictly smaller than the counted trial-division
cost at `roughThreshold`.  This is the inequality that rules out trial division
as a P1 prepass. -/
theorem eventually_exp_eps_scale_lt_trialDivisionCost
    {eps : ℕ → ℝ} (heps : Tendsto eps atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (eps n * scale n) < trialDivisionCost n := by
  filter_upwards [eventually_exp_eps_scale_lt_roughThreshold heps,
    eventually_roughThreshold_le_trialDivisionCost] with n hlt hle
  exact lt_of_lt_of_le hlt hle

/-- **Trial division has no subexponential rate.**  The proved cost envelope at
`roughThreshold` cannot satisfy the required bound at any rate tending to zero. -/
theorem trialDivision_not_subexpRate
    (R : SubexpCostRate trialDivisionCost) : False := by
  have hlt := eventually_exp_eps_scale_lt_trialDivisionCost R.eps_tendsto
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hlt, R.cost_le_exp] with n hlt hle
    exact not_lt_of_ge hle hlt
  obtain ⟨n, hn⟩ := hcontra.exists
  exact hn

/-- There is no subexponential cost rate for the counted trial-division cost. -/
theorem trialDivision_no_subexpRate :
    ¬ Nonempty (SubexpCostRate trialDivisionCost) := by
  rintro ⟨R⟩
  exact trialDivision_not_subexpRate R

/-- **No `SubexpPrepassInput` can use the trial-division cost.** -/
theorem trialDivision_not_subexpPrepass (I : SubexpPrepassInput)
    (hcost : I.cost = trialDivisionCost) : False := by
  have h := I.cost_subexp
  rw [hcost] at h
  exact trialDivision_not_subexpRate h

/-- The non-existential form of the trial-division gap. -/
theorem trialDivision_no_subexpPrepass :
    ¬ ∃ I : SubexpPrepassInput, I.cost = trialDivisionCost := by
  rintro ⟨I, hI⟩
  exact trialDivision_not_subexpPrepass I hI

/-- **The trial-division gap, bundled.**  At the paper cutoff the counted trial
division costs at least `roughThreshold`, every `exp (ε_n * scale n)` budget with
`ε_n → 0` is eventually below `roughThreshold`, and consequently no
`SubexpCostRate` (and hence no `SubexpPrepassInput`) can charge that cost. -/
theorem trialDivision_subexpGap :
    (∀ᶠ n : ℕ in atTop, roughThreshold n ≤ trialDivisionCost n) ∧
      (∀ eps : ℕ → ℝ, Tendsto eps atTop (𝓝 0) → ∀ᶠ n : ℕ in atTop,
        Real.exp (eps n * scale n) < trialDivisionCost n) ∧
      ¬ Nonempty (SubexpCostRate trialDivisionCost) :=
  ⟨eventually_roughThreshold_le_trialDivisionCost,
    fun _ heps => eventually_exp_eps_scale_lt_trialDivisionCost heps,
    trialDivision_no_subexpRate⟩

/-! ## Axiom audit -/

#print axioms eventually_lt_of_tendsto_zero
#print axioms eventually_exp_eps_scale_lt_roughThreshold
#print axioms SubexpPrepassInput.subexpLoss
#print axioms SubexpPrepassInput.costExponent_nonneg
#print axioms SubexpPrepassInput.costExponent_sublinear
#print axioms SubexpPrepassInput.cost_le_exp_costExponent
#print axioms SubexpPrepassInput.toP1Leaf
#print axioms SubexpPrepassInput.toP1Leaf_loss
#print axioms SubexpPrepassInput.discharges_P1Leaf_slot
#print axioms SubexpPrepassInput.slot
#print axioms log_le_of_le_exp
#print axioms subexpEps_nonneg
#print axioms subexpEps_tendsto
#print axioms subexpEps_bound
#print axioms subexpCostRateOfEnvelope
#print axioms genusTwoSubexpPrepassInput
#print axioms genusTwoSubexpPrepassInput_cost
#print axioms genusTwoPrepass_discharges_slot
#print axioms ecmSubexpPrepassInput
#print axioms ecmPrepass_discharges_slot
#print axioms trialDivisionCost_eq_envelope
#print axioms eventually_roughThreshold_le_trialDivisionCost
#print axioms eventually_exp_eps_scale_lt_trialDivisionCost
#print axioms trialDivision_not_subexpRate
#print axioms trialDivision_no_subexpRate
#print axioms trialDivision_not_subexpPrepass
#print axioms trialDivision_no_subexpPrepass
#print axioms trialDivision_subexpGap

end

end Cogentic.RandomizedP1Prepass
