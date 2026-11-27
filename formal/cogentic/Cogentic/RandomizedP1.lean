import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedSmallPrimePrepass

/-!
# P1: the `exp (o(H))` prepass below `exp ((log n)^{2/3})`

Blueprint §0.2 and §2 ("Prepass") isolate one remaining analytic input for the
randomized factoring endpoint: a partial factorer that, on hard inputs with a
prime factor below

`roughThreshold n = exp ((log n)^{2/3})`,

misses with probability at most `exp (-δ H)` for every `δ > 0`, and costs
`exp (o(H))`.  Here `H = scale n = (log n)^{1/3} (log log n)^{2/3}`.  The C5
ledger consumes only the `δ = 2` instance of the success statement; the cost is
charged to C4, and is recorded in `P1Leaf.costExponent` for audit.

This file separates the two P1 inputs:

* `P1Inputs.success` is the manuscript's success statement, exactly in the
  `SubexpLoss` shape;
* `P1Inputs.costExponent` is the cost exponent, with the explicit little-o input
  `costExponent =o scale`.  The little-o statement is converted below into the
  eventual inequality `costExponent n ≤ δ * scale n` used by `P1Leaf`.
  Polynomial overhead is kept as an explicit degree `overhead`, and
  `P1Inputs.work_le_exp_add` shows that it is absorbed into any positive
  exponent slack.

The file then proves the `P1Leaf` reduction (`P1Inputs.toP1Leaf` and
`P1Inputs.slot`).

## The trial-division gap

The counted trial-division prepass in `RandomizedSmallPrimePrepass` does *not*
discharge P1.  It splits every input with a prime factor below its cutoff
(`trialPrepass_splits_of_hasSmallPrimeFactor`), but its proved work bound is

`54 * B * n.size^2`.

At the required cutoff `B ≥ roughThreshold n` this is
`exp ((log n)^{2/3} + O (log log n))`, whose logarithm is not `o (scale n)`.
`trialDivisionExponent_not_sublinear` proves that the logarithm of this envelope
eventually exceeds every fixed multiple of `scale n`, and
`not_trialPrepass_affordable_at_roughThreshold` proves that the cost hypothesis
`B n ≤ exp (ε * scale n)` of `trialPrepass_mean_work_le_exp` fails at every
cutoff reaching `roughThreshold`.  Thus the split between "success is available"
and "the trial-division cost is too large" is explicit in `TrialDivisionGap`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  In particular the P1
failure probability and cost exponent are supplied by the inputs and are not set
to zero.
-/

namespace Cogentic.RandomizedP1

open Filter Real
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSmallPrimePrepass

/-! ## Elementary asymptotics of the rough threshold -/

private theorem log_nat_grows : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `(log log n)^2 = o (log n)`, obtained from
`log x = o (x^s)` at `s = 1` and `x = log n`. -/
theorem logLog_rpow_two_isLittleO_log :
    Asymptotics.IsLittleO atTop
      (fun n : ℕ => Real.log (Real.log n) ^ (2 : ℝ))
      (fun n : ℕ => Real.log n) := by
  have h :=
    (isLittleO_log_rpow_rpow_atTop (r := (2 : ℝ)) (s := 1) (by norm_num)).comp_tendsto
      log_nat_grows
  simpa [Function.comp_def, Real.rpow_one] using h

/-- `scale n = (log n)^{1/3} (log log n)^{2/3}` is little-o of
`logB n = (log n)^{2/3}`.  This is the quantitative form of
`(log n)^{2/3} = ω (scale n)`, i.e. the paper cutoff lies far above
`exp (O (scale n))`. -/
theorem scale_isLittleO_logB :
    Asymptotics.IsLittleO atTop scale logB := by
  have hpow :=
    (logLog_rpow_two_isLittleO_log.rpow (r := (1 / 3 : ℝ)) (by norm_num)
      (Eventually.of_forall fun n => Real.log_natCast_nonneg n))
  have hmul :=
    hpow.mul_isBigO
      (Asymptotics.isBigO_refl (fun n : ℕ => (Real.log n) ^ (1 / 3 : ℝ)) atTop)
  refine hmul.congr' ?_ ?_
  · filter_upwards [log_nat_grows.eventually_ge_atTop 1] with n hn
    have hM : 0 ≤ Real.log (Real.log n) :=
      Real.log_nonneg (by linarith : (1 : ℝ) ≤ Real.log n)
    rw [← Real.rpow_mul hM,
      show (2 : ℝ) * (1 / 3 : ℝ) = (2 / 3 : ℝ) by norm_num]
    unfold scale
    ring
  · filter_upwards [log_nat_grows.eventually_ge_atTop 1] with n hn
    have hL : 0 < Real.log n := zero_lt_one.trans_le hn
    unfold logB
    rw [← Real.rpow_add hL]
    norm_num

/-- Eventually `scale n ≤ (1/2) logB n`. -/
theorem eventually_scale_le_half_logB :
    ∀ᶠ n : ℕ in atTop, scale n ≤ (1 / 2 : ℝ) * logB n := by
  have h := scale_isLittleO_logB.def (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [h, scale_grows.eventually_ge_atTop 0,
    logB_grows.eventually_ge_atTop 0] with n hn hs hb
  rw [Real.norm_of_nonneg hs, Real.norm_of_nonneg hb] at hn
  exact hn

/-- Eventually `scale n < logB n - log 2`. -/
theorem eventually_scale_lt_logB_sub_log_two :
    ∀ᶠ n : ℕ in atTop, scale n < logB n - Real.log 2 := by
  filter_upwards [eventually_scale_le_half_logB,
    logB_grows.eventually_ge_atTop (Real.log 4 + 1)] with n hhalf hbig
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hbig' : 2 * Real.log 2 + 1 ≤ logB n := by
    calc
      2 * Real.log 2 + 1 = Real.log 4 + 1 := by rw [h4]
      _ ≤ logB n := hbig
  have hmid : (1 / 2 : ℝ) * logB n < logB n - Real.log 2 := by
    nlinarith only [hbig']
  exact lt_of_le_of_lt hhalf hmid

/-- For every fixed `ε > 0`, the paper cutoff exceeds the trial-division budget
`exp (ε * scale n)` eventually. -/
theorem eventually_exp_scale_lt_roughThreshold (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (ε * scale n) < roughThreshold n := by
  have hδ : 0 < 1 / (2 * ε) := by positivity
  have hsmall := scale_isLittleO_logB.def hδ
  filter_upwards [hsmall, scale_grows.eventually_ge_atTop 0,
    logB_grows.eventually_ge_atTop 1] with n hn hs hb
  rw [Real.norm_of_nonneg hs, Real.norm_of_nonneg (zero_le_one.trans hb)] at hn
  have hhalf : ε * scale n ≤ (1 / 2 : ℝ) * logB n := by
    calc
      ε * scale n ≤ ε * ((1 / (2 * ε)) * logB n) :=
        mul_le_mul_of_nonneg_left hn hε.le
      _ = (1 / 2 : ℝ) * logB n := by
        field_simp [hε.ne']
        try ring
  have hlt : ε * scale n < logB n := by nlinarith only [hhalf, hb]
  unfold roughThreshold
  exact Real.exp_lt_exp.mpr hlt

/-! ## The P1 inputs -/

/-- Explicit success and cost inputs for the P1 prepass.

`P1Leaf` records a miss probability `loss`, a cost exponent, and the two
manuscript statements.  The fields below are the same two statements, with the
cost side additionally decomposed into a charged work bound, a polynomial
overhead, and the little-o statement `costExponent =o scale`.  The cutoff field
records that the prepass operates up to the paper's `roughThreshold`; it is not
used by `P1Leaf` (which is a statement about the miss probability), but it keeps
the threshold side of P1 explicit. -/
structure P1Inputs where
  /-- The prepass cutoff `B n`. -/
  cutoff : ℕ → ℝ
  /-- The cutoff covers the paper's `exp ((log n)^{2/3})` threshold. -/
  cutoff_ge_rough : ∀ᶠ n : ℕ in atTop, roughThreshold n ≤ cutoff n
  /-- The miss probability of the prepass.  This is the P1 loss. -/
  miss : ℕ → ℝ
  /-- A failure probability is nonnegative. -/
  miss_nonneg : ∀ n, 0 ≤ miss n
  /-- A failure probability is at most one. -/
  miss_le_one : ∀ n, miss n ≤ 1
  /-- **Success input** (KB Prop. H.3 p.129 and blueprint P1): for every
  `δ > 0`, the miss probability is eventually at most `exp (-δ H)`. -/
  success : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    miss n ≤ exp (-(δ) * scale n)
  /-- The exponential part of the prepass cost. -/
  costExponent : ℕ → ℝ
  /-- The cost exponent is nonnegative. -/
  costExponent_nonneg : ∀ n, 0 ≤ costExponent n
  /-- **Cost input**: `costExponent = o (H)`.  This is the manuscript's
  `exp (o(H))` cost statement, in its explicit little-o form. -/
  costExponent_littleO : Asymptotics.IsLittleO atTop costExponent scale
  /-- The charged expected work of the prepass. -/
  work : ℕ → ℝ
  /-- Work is nonnegative. -/
  work_nonneg : ∀ n, 0 ≤ work n
  /-- Polynomial overhead degree of the prepass. -/
  overhead : ℕ
  /-- **Cost input**: the work is at most a polynomial in the bit length times
  `exp (costExponent n)`.  The little-o part is separated from the polynomial
  factor, as in `P1Leaf`'s "up to polynomial factors". -/
  work_le : ∀ n, work n ≤ ((n.log2 : ℝ) + 1) ^ overhead * exp (costExponent n)

namespace P1Inputs

variable (I : P1Inputs)

/-- The little-o cost input implies the eventual `δ`-slack inequality consumed
by `P1Leaf.cost_sublinear`. -/
theorem costExponent_sublinear :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      I.costExponent n ≤ δ * scale n := by
  intro δ hδ
  have h := I.costExponent_littleO.def hδ
  filter_upwards [h, scale_grows.eventually_ge_atTop 0] with n hn hs
  rw [Real.norm_of_nonneg (I.costExponent_nonneg n), Real.norm_of_nonneg hs] at hn
  exact hn

/-- The success input is exactly the manuscript's `SubexpLoss` shape. -/
theorem subexpLoss : SubexpLoss I.miss := I.success

/-- The `δ = 2` instance is the C5 prepass slot. -/
theorem slot :
    ∀ᶠ n : ℕ in atTop, I.miss n ≤ exp (-(2 : ℝ) * scale n) :=
  I.success 2 (by norm_num)

/-- **The P1Leaf reduction.**  The explicit success and cost inputs give the
paper's P1 leaf.  The loss is the input `I.miss` and the cost exponent is the
input `I.costExponent`; neither is replaced by a constant zero. -/
def toP1Leaf : P1Leaf where
  loss := I.miss
  loss_nonneg := I.miss_nonneg
  paper := I.subexpLoss
  costExponent := I.costExponent
  costExponent_nonneg := I.costExponent_nonneg
  cost_sublinear := I.costExponent_sublinear

/-- The polynomial overhead is absorbed into an arbitrary positive exponent
slack. -/
theorem work_le_exp_add {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      I.work n ≤ exp (I.costExponent n + δ * scale n) := by
  filter_upwards [eventually_bitPoly_le_exp (A := (1 : ℝ)) hδ I.overhead]
    with n hpoly
  have hpoly' : ((n.log2 : ℝ) + 1) ^ I.overhead ≤ exp (δ * scale n) := by
    simpa using hpoly
  calc
    I.work n ≤ ((n.log2 : ℝ) + 1) ^ I.overhead * exp (I.costExponent n) :=
      I.work_le n
    _ ≤ exp (δ * scale n) * exp (I.costExponent n) :=
      mul_le_mul_of_nonneg_right hpoly' (Real.exp_pos _).le
    _ = exp (I.costExponent n + δ * scale n) := by
      rw [← Real.exp_add]
      ring_nf

/-- The charged work, including the polynomial overhead and the additive `+1`
of the epoch cost convention, fits in `exp (ε * scale n)` for every `ε > 0`.
This is the P1 input needed by `combined_epoch_asymptotic_logB`'s `hPreWork`. -/
theorem work_add_one_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      I.work n + 1 ≤ exp (ε * scale n) := by
  have hε4 : 0 < ε / 4 := by positivity
  have hε2 : 0 < ε / 2 := by positivity
  have hhalf : ∀ᶠ n : ℕ in atTop,
      I.work n ≤ exp ((ε / 2) * scale n) := by
    filter_upwards [I.work_le_exp_add hε4,
      I.costExponent_sublinear (ε / 4) hε4] with n hw hc
    calc
      I.work n ≤ exp (I.costExponent n + (ε / 4) * scale n) := hw
      _ ≤ exp ((ε / 4) * scale n + (ε / 4) * scale n) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = exp ((ε / 2) * scale n) := by ring_nf
  have htwo : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ≤ exp ((ε / 2) * scale n) := by
    filter_upwards [scale_grows.eventually_ge_atTop (Real.log 2 / (ε / 2))]
      with n hn
    have hlog2 : Real.log 2 ≤ (ε / 2) * scale n := by
      have := (div_le_iff₀ hε2).mp hn
      linarith
    calc
      (2 : ℝ) = exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ exp ((ε / 2) * scale n) := Real.exp_le_exp.mpr hlog2
  filter_upwards [hhalf, htwo] with n hw h2
  have hexp_pos : 0 < exp ((ε / 2) * scale n) := Real.exp_pos _
  calc
    I.work n + 1 ≤ exp ((ε / 2) * scale n) + 1 := by linarith
    _ ≤ exp ((ε / 2) * scale n) + exp ((ε / 2) * scale n) := by linarith
    _ = 2 * exp ((ε / 2) * scale n) := by ring
    _ ≤ exp ((ε / 2) * scale n) * exp ((ε / 2) * scale n) :=
      mul_le_mul_of_nonneg_right h2 hexp_pos.le
    _ = exp (ε * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring

end P1Inputs

/-! ## The explicit trial-division cost gap -/

/-- The logarithm of the proved trial-division work envelope at the paper
cutoff: `log (54 * roughThreshold n * n.size^2)`. -/
noncomputable def trialDivisionExponent (n : ℕ) : ℝ :=
  Real.log (54 * roughThreshold n * (n.size : ℝ) ^ 2)

/-- At any cutoff `B` reaching `roughThreshold`, the proved trial-division work
envelope `54 * B * n.size^2` exceeds the `exp (ε * scale n)` budget.  This is a
statement about the envelope supplied by `trialPrepass_work_le`, not about the
actual (unbounded-below) runtime. -/
theorem trialPrepass_cutoff_cost_gap
    (B : ℕ → ℕ)
    (hB : ∀ᶠ n : ℕ in atTop, roughThreshold n ≤ (B n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (ε * scale n) < 54 * (B n : ℝ) * (n.size : ℝ) ^ 2 := by
  filter_upwards [eventually_exp_scale_lt_roughThreshold ε hε, hB,
    eventually_ge_atTop (1 : ℕ)] with n hlt hBge hn
  have hsize : (1 : ℝ) ≤ (n.size : ℝ) := by
    exact_mod_cast Nat.size_pos.mpr (by omega : 0 < n)
  have hsize2 : (1 : ℝ) ≤ (n.size : ℝ) ^ 2 := by
    exact one_le_pow₀ hsize
  have hmono : roughThreshold n ≤ 54 * roughThreshold n * (n.size : ℝ) ^ 2 := by
    have h54 : (1 : ℝ) ≤ 54 * (n.size : ℝ) ^ 2 := by nlinarith only [hsize2]
    calc
      roughThreshold n = roughThreshold n * 1 := (mul_one _).symm
      _ ≤ roughThreshold n * (54 * (n.size : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h54 (Real.exp_pos _).le
      _ = 54 * roughThreshold n * (n.size : ℝ) ^ 2 := by ring
  have hle : roughThreshold n ≤ 54 * (B n : ℝ) * (n.size : ℝ) ^ 2 := by
    calc
      roughThreshold n ≤ 54 * roughThreshold n * (n.size : ℝ) ^ 2 := hmono
      _ ≤ 54 * (B n : ℝ) * (n.size : ℝ) ^ 2 := by
        have h54B : 54 * roughThreshold n ≤ 54 * (B n : ℝ) :=
          mul_le_mul_of_nonneg_left hBge (by norm_num)
        exact mul_le_mul_of_nonneg_right h54B (sq_nonneg _)
  exact lt_of_lt_of_le hlt hle

/-- No cutoff reaching `roughThreshold` can satisfy the affordable-cutoff
hypothesis `B n ≤ exp (ε * scale n)` of `trialPrepass_mean_work_le_exp`. -/
theorem not_trialPrepass_affordable_at_roughThreshold
    (B : ℕ → ℕ)
    (hB : ∀ᶠ n : ℕ in atTop, roughThreshold n ≤ (B n : ℝ)) :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (B n : ℝ) ≤ Real.exp (ε * scale n)) := by
  intro h
  have h1 := h 1 (by norm_num)
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [h1, eventually_exp_scale_lt_roughThreshold 1 (by norm_num), hB]
      with n hle hlt hge
    linarith
  obtain ⟨n, hn⟩ := hcontra.exists
  exact hn

/-- The trial-division prepass succeeds (with probability one) on every hard
input that has a prime factor below its cutoff.  This is the success half of the
gap: trial division is fine on the success side. -/
theorem trialPrepass_paper_success (B : ℕ → ℕ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      HardInput n → HasSmallPrimeFactor (B n : ℝ) n →
        (trialPrepass (B n) n).1 ≠ none := by
  intro δ hδ
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn hhard hsmall
  exact trialPrepass_splits_of_hasSmallPrimeFactor hn hhard.2.1 hsmall

/-- Eventually `logB n - log 2 ≤ log (54 * roughThreshold n * n.size^2)`. -/
theorem eventually_logB_sub_log_two_le_trialDivisionExponent :
    ∀ᶠ n : ℕ in atTop,
      logB n - Real.log 2 ≤ trialDivisionExponent n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hsize : (1 : ℝ) ≤ (n.size : ℝ) := by
    exact_mod_cast Nat.size_pos.mpr (by omega : 0 < n)
  have hsize2 : (1 : ℝ) ≤ (n.size : ℝ) ^ 2 := by
    exact one_le_pow₀ hsize
  have hmono : roughThreshold n ≤ 54 * roughThreshold n * (n.size : ℝ) ^ 2 := by
    have h54 : (1 : ℝ) ≤ 54 * (n.size : ℝ) ^ 2 := by nlinarith only [hsize2]
    calc
      roughThreshold n = roughThreshold n * 1 := (mul_one _).symm
      _ ≤ roughThreshold n * (54 * (n.size : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h54 (Real.exp_pos _).le
      _ = 54 * roughThreshold n * (n.size : ℝ) ^ 2 := by ring
  have hlog : Real.log (roughThreshold n) ≤
      Real.log (54 * roughThreshold n * (n.size : ℝ) ^ 2) :=
    Real.log_le_log (Real.exp_pos _) hmono
  have hlogr : Real.log (roughThreshold n) = logB n := by
    unfold roughThreshold
    exact Real.log_exp _
  rw [hlogr] at hlog
  have hlog2_nonneg : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  unfold trialDivisionExponent
  linarith only [hlog, hlog2_nonneg]

/-- The trial-division cost exponent is **not** `o (H)`; in fact eventually it
exceeds every fixed positive multiple of `scale n`. -/
theorem trialDivisionExponent_not_sublinear :
    ¬ (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        trialDivisionExponent n ≤ δ * scale n) := by
  intro h
  have h1 := h 1 (by norm_num)
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [h1, eventually_logB_sub_log_two_le_trialDivisionExponent,
      eventually_scale_lt_logB_sub_log_two] with n hle hlog hlt
    have hle' : trialDivisionExponent n ≤ scale n := by simpa using hle
    linarith only [hle', hlog, hlt]
  obtain ⟨n, hn⟩ := hcontra.exists
  exact hn

/-- **The explicit trial-division gap.**  The counted trial-division prepass
has the right splitting behaviour, but its proved work envelope at the paper
cutoff is not `exp (o(H))`: the affordable-cutoff hypothesis fails, and the
logarithm of the envelope is not little-o of `scale`. -/
def TrialDivisionGap : Prop :=
  (∀ B : ℕ → ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      HardInput n → HasSmallPrimeFactor (B n : ℝ) n →
        (trialPrepass (B n) n).1 ≠ none) ∧
    (∀ B : ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, roughThreshold n ≤ (B n : ℝ)) →
        ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          (B n : ℝ) ≤ Real.exp (ε * scale n))) ∧
    (¬ (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        trialDivisionExponent n ≤ δ * scale n))

/-- The trial-division gap is a theorem, not an assumption. -/
theorem trialDivisionGap : TrialDivisionGap :=
  ⟨trialPrepass_paper_success, not_trialPrepass_affordable_at_roughThreshold,
    trialDivisionExponent_not_sublinear⟩

/-! ## Axiom audit -/

#print axioms logLog_rpow_two_isLittleO_log
#print axioms scale_isLittleO_logB
#print axioms eventually_scale_le_half_logB
#print axioms eventually_scale_lt_logB_sub_log_two
#print axioms eventually_exp_scale_lt_roughThreshold
#print axioms P1Inputs.costExponent_sublinear
#print axioms P1Inputs.subexpLoss
#print axioms P1Inputs.slot
#print axioms P1Inputs.toP1Leaf
#print axioms P1Inputs.work_le_exp_add
#print axioms P1Inputs.work_add_one_le_exp
#print axioms trialPrepass_cutoff_cost_gap
#print axioms not_trialPrepass_affordable_at_roughThreshold
#print axioms trialPrepass_paper_success
#print axioms trialDivisionExponent_not_sublinear
#print axioms trialDivisionGap

end Cogentic.RandomizedP1
