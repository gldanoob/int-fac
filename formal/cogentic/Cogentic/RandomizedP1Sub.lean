import Cogentic.RandomizedP1

/-!
# P1 sub-lemmas: trial division, the threshold gap, and success-to-cost

`Cogentic/RandomizedP1.lean` reduces the manuscript's P1 prepass to two explicit
inputs: a success statement (`P1Inputs.success`) and an `exp (o (H))` cost
statement (`P1Inputs.costExponent_littleO`).  This file is the elementary layer
below that reduction.  The two paper-level estimates are kept as explicit
`Prop`s:

* `PrepassSuccess` — the genus-two (KB Proposition H.3) or ECM (LP Theorem 7.1)
  prepass succeeds with probability `≥ exp (-δ H)` for every `δ > 0`;
* `PrepassCostSubexp` — the prepass cost exponent is `o (H)`, i.e. the cost is
  `exp (o (H))`.

Neither proposition is proved, weakened, or replaced by a zero cost.  Everything
else is elementary and is proved here:

1. **Trial-division splitting and cost arithmetic.**
   `trialPrepass_splits` is the deterministic splitting half: every hard input
   with a prime factor below the cutoff is split.  `trialPrepass_work_envelope`
   records the proved work bound `54 B n.size²`; `trialPrepass_work_le_exp`
   turns it into `work + 1 ≤ exp (ε H)` whenever the cutoff is affordable
   (`B ≤ exp (ε H / 2)`), and `trialDivisionExponent_eq` expands the logarithm of
   the envelope as `log 54 + logB n + 2 log n.size`.
2. **Threshold separation.**
   `threshold_separation` records `scale = o (logB)`, the eventual inequality
   `scale < logB - log 2`, and `exp (ε H) < roughThreshold`.  The corresponding
   negative statement for trial division is `trialDivision_threshold_gap`: at
   every cutoff reaching `roughThreshold`, the envelope `54 B n.size²` exceeds
   `exp (ε H)`, so the deterministic trial-division prepass is not affordable
   (`trialDivision_cost_not_subexp`).
3. **Success-to-cost conversion.**
   A single attempt has success mass `1 - miss`; the success input gives
   `(1 - miss)⁻¹ ≤ 2` eventually, so the expected number of independent retries
   is at most `2`.  Consequently the expected repeated work
   `work / (1 - miss)` is at most `2 · work`, and with the subexponential cost
   input it is still `≤ exp (ε H)` for every `ε > 0`
   (`P1SubInputs.repeated_work_add_one_le_exp`).  Thus the success probability
   only changes the cost by a constant, which is absorbed by the `exp (o (H))`
   slack; this is the success-to-cost conversion used by the P1 ledger.

The bundled `P1SubInputs` replaces the two fields of `P1Inputs` by the two
explicit `Prop`s and re-proves the `P1Leaf` reduction, the `δ = 2` slot, the
sublinear cost consequence, and the work bounds.

No `sorry`, `admit`, `axiom`, or `native_decide`.  In particular the
`exp (o (H))` cost is a hypothesis, not a zero-cost artefact.
-/

namespace Cogentic.RandomizedP1Sub

open Filter Real
open Cogentic.RandomizedP1
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSmallPrimePrepass
open Cogentic.RandomizedEpochAnalyticInputs

noncomputable section

/-! ## 1. Trial-division splitting and cost arithmetic -/

/-- **Splitting half of the counted trial-division prepass.**  On every hard
input that has a prime factor at most the cutoff `B n`, the concrete counted
trial-division prepass finds a proper divisor.  The statement is deterministic
and uses no paper-level input. -/
theorem trialPrepass_splits (B : ℕ → ℕ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      HardInput n → HasSmallPrimeFactor (B n : ℝ) n →
        (trialPrepass (B n) n).1 ≠ none :=
  trialPrepass_paper_success B

/-- **The counted trial-division work envelope.**  The proved bit-cost bound is
`54 · B · n.size²`. -/
theorem trialPrepass_work_envelope (B n : ℕ) :
    (trialPrepass B n).2 ≤ 54 * B * n.size ^ 2 :=
  trialPrepass_work_le B n

/-- The logarithm of the trial-division envelope, split into its elementary
pieces: `log 54 + logB n + 2 log n.size`.  This is the arithmetic behind the
`exp ((log n)^{2/3} + O (log log n))` cost of trial division. -/
theorem trialDivisionExponent_eq (n : ℕ) (hn : 0 < n) :
    trialDivisionExponent n =
      Real.log 54 + logB n + 2 * Real.log (n.size : ℝ) := by
  unfold trialDivisionExponent
  have h54 : (54 : ℝ) ≠ 0 := by norm_num
  have hT : roughThreshold n ≠ 0 := (Real.exp_pos _).ne'
  have hs : (n.size : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.size_pos.mpr hn).ne'
  rw [Real.log_mul (mul_ne_zero h54 hT) (pow_ne_zero 2 hs),
    Real.log_mul h54 hT, Real.log_pow]
  rw [show Real.log (roughThreshold n) = logB n from Real.log_exp _]
  push_cast
  ring

/-- The trial-division cost exponent is at least `logB`: the `54` factor and
the `n.size²` factor only add nonnegative terms. -/
theorem logB_le_trialDivisionExponent (n : ℕ) (hn : 0 < n) :
    logB n ≤ trialDivisionExponent n := by
  rw [trialDivisionExponent_eq n hn]
  have hlog54 : 0 ≤ Real.log 54 := Real.log_nonneg (by norm_num)
  have hsize : (1 : ℝ) ≤ (n.size : ℝ) := by
    exact_mod_cast Nat.size_pos.mpr hn
  have hlogsize : 0 ≤ 2 * Real.log (n.size : ℝ) := by
    have := Real.log_nonneg hsize
    positivity
  linarith

/-- The trial-division cost exponent is nonnegative for every input. -/
theorem trialDivisionExponent_nonneg (n : ℕ) : 0 ≤ trialDivisionExponent n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [trialDivisionExponent, roughThreshold, logB]
  · unfold trialDivisionExponent
    have hlogB : 0 ≤ logB n := by
      unfold logB
      exact rpow_nonneg (Real.log_natCast_nonneg n) _
    have hT : (1 : ℝ) ≤ roughThreshold n := by
      unfold roughThreshold
      exact Real.one_le_exp hlogB
    have hsize : (1 : ℝ) ≤ (n.size : ℝ) := by
      exact_mod_cast Nat.size_pos.mpr hn
    have hsize2 : (1 : ℝ) ≤ (n.size : ℝ) ^ 2 := one_le_pow₀ hsize
    have harg : (1 : ℝ) ≤ 54 * roughThreshold n * (n.size : ℝ) ^ 2 := by
      calc
        (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ 54 * roughThreshold n * (n.size : ℝ) ^ 2 := by
          gcongr
          norm_num
    exact Real.log_nonneg harg

/-- The affordable-cutoff cost arithmetic for trial division: if the cutoff is
at most `exp (ε H / 2)`, the proved work envelope plus the constant `1` fits in
`exp (ε H)`.  This is the real-variable form of
`trialPrepass_mean_work_le_exp`, without the `PMF` wrapper. -/
theorem trialPrepass_work_le_exp {B : ℕ → ℕ} {ε : ℝ} (hε : 0 < ε)
    (hB : ∀ᶠ n : ℕ in atTop, (B n : ℝ) ≤ Real.exp ((ε / 2) * scale n)) :
    ∀ᶠ n : ℕ in atTop,
      ((trialPrepass (B n) n).2 : ℝ) + 1 ≤ Real.exp (ε * scale n) := by
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [hB, eventually_bitPoly_le_exp (A := 56) hε2 2,
    scale_grows.eventually_ge_atTop 0] with n hBn hpoly hs0
  set E : ℝ := Real.exp ((ε / 2) * scale n) with hE
  set P : ℝ := ((n.log2 : ℝ) + 1) ^ 2 with hP
  have hEpos : 0 < E := Real.exp_pos _
  have hPnonneg : 0 ≤ P := sq_nonneg _
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg hε2.le hs0)
  have hP1 : 1 ≤ P := by
    have hbits : (1 : ℝ) ≤ (n.log2 : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) n.log2]
    exact one_le_pow₀ hbits
  have hwork := trialPrepass_work_le (B n) n
  have hsize : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  have hcast : ((trialPrepass (B n) n).2 : ℝ) ≤
      54 * (B n : ℝ) * (n.size : ℝ) ^ 2 := by
    exact_mod_cast hwork
  have hsR : (n.size : ℝ) ≤ (n.log2 : ℝ) + 1 := by exact_mod_cast hsize
  have hcostP : ((trialPrepass (B n) n).2 : ℝ) ≤ 54 * (B n : ℝ) * P := by
    calc
      ((trialPrepass (B n) n).2 : ℝ)
          ≤ 54 * (B n : ℝ) * (n.size : ℝ) ^ 2 := hcast
      _ ≤ 54 * (B n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 := by gcongr
      _ = 54 * (B n : ℝ) * P := by rw [hP]
  have hBP : 54 * (B n : ℝ) * P ≤ 54 * E * P := by
    have hmul := mul_le_mul_of_nonneg_right hBn
      (show (0 : ℝ) ≤ 54 * P by positivity)
    calc
      54 * (B n : ℝ) * P = (B n : ℝ) * (54 * P) := by ring
      _ ≤ E * (54 * P) := hmul
      _ = 54 * E * P := by ring
  have hone : (1 : ℝ) ≤ E * P := one_le_mul_of_one_le_of_one_le hE1 hP1
  have hpoly' : 56 * P ≤ E := by simpa [hP] using hpoly
  calc
    ((trialPrepass (B n) n).2 : ℝ) + 1
        ≤ 54 * E * P + 1 := by linarith
    _ ≤ 54 * E * P + E * P := by linarith
    _ = 55 * (E * P) := by ring
    _ ≤ 56 * (E * P) := by
      have hEP : 0 ≤ E * P := mul_nonneg hEpos.le hPnonneg
      nlinarith
    _ = E * (56 * P) := by ring
    _ ≤ E * E := mul_le_mul_of_nonneg_left hpoly' hEpos.le
    _ = Real.exp (ε * scale n) := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring

/-! ## 2. Threshold separation -/

/-- **The P1 threshold separation.**  The ledger scale is little-o of
`logB = (log n)^{2/3}`, the scale is eventually below `logB - log 2`, and every
budget `exp (ε H)` is eventually below the paper cutoff `roughThreshold`. -/
theorem threshold_separation :
    Asymptotics.IsLittleO atTop scale logB ∧
      (∀ᶠ n : ℕ in atTop, scale n < logB n - Real.log 2) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        Real.exp (ε * scale n) < roughThreshold n) :=
  ⟨scale_isLittleO_logB, eventually_scale_lt_logB_sub_log_two,
    eventually_exp_scale_lt_roughThreshold⟩

/-- **The trial-division threshold gap.**  At every cutoff reaching
`roughThreshold`, the proved trial-division envelope `54 B n.size²` exceeds the
`exp (ε H)` budget.  This is the separation that rules out the deterministic
trial-division prepass as the `exp (o (H))` P1 implementation. -/
theorem trialDivision_threshold_gap (B : ℕ → ℕ)
    (hB : ∀ᶠ n : ℕ in atTop, roughThreshold n ≤ (B n : ℝ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (ε * scale n) < 54 * (B n : ℝ) * (n.size : ℝ) ^ 2 :=
  trialPrepass_cutoff_cost_gap B hB hε

/-! ## 3. The paper-level inputs as explicit `Prop`s -/

/-- **Prepass success input.**  A genus-two (KB Proposition H.3) or ECM
(LP Theorem 7.1) prepass misses with probability at most `exp (-δ H)` for every
`δ > 0`.  This is the manuscript's success statement and is not proved here. -/
def PrepassSuccess (miss : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    miss n ≤ Real.exp (-(δ) * scale n)

/-- The genus-two instance of the success input (KB Proposition H.3). -/
abbrev GenusTwoPrepassSuccess (miss : ℕ → ℝ) : Prop := PrepassSuccess miss

/-- The ECM instance of the success input (LP Theorem 7.1).  Its success shape
is the same as the genus-two one; only the cost analysis differs. -/
abbrev ECMPrepassSuccess (miss : ℕ → ℝ) : Prop := PrepassSuccess miss

/-- **Prepass cost input.**  The cost exponent is `o (H)`, i.e. the prepass costs
`exp (o (H))` up to the polynomial overhead carried by `P1Inputs.work_le`.
This is the manuscript's cost statement and is not proved here. -/
def PrepassCostSubexp (costExponent : ℕ → ℝ) : Prop :=
  Asymptotics.IsLittleO atTop costExponent scale

/-- An `IsLittleO` cost input gives the eventual `δ`-slack inequality used by
`P1Leaf`, provided the cost exponent is nonnegative. -/
theorem littleO_to_sublinear {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : Asymptotics.IsLittleO atTop f scale) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, f n ≤ δ * scale n := by
  intro δ hδ
  have hdef := h.def hδ
  filter_upwards [hdef, scale_grows.eventually_ge_atTop 0] with n hn hs
  rw [Real.norm_of_nonneg (hf n), Real.norm_of_nonneg hs] at hn
  exact hn

/-- The trial-division cost exponent fails the `exp (o (H))` cost input.  This
is the cost half of `TrialDivisionGap`, phrased against `PrepassCostSubexp`. -/
theorem trialDivision_cost_not_subexp :
    ¬ PrepassCostSubexp trialDivisionExponent := by
  intro h
  exact trialDivisionExponent_not_sublinear
    (littleO_to_sublinear trialDivisionExponent_nonneg h)

/-! ## 4. Success-to-cost conversion -/

/-- The success mass of one independent prepass attempt. -/
def successMass (miss : ℕ → ℝ) (n : ℕ) : ℝ := 1 - miss n

/-- The `δ`-success input makes the single-attempt success mass at least
`1/2` eventually. -/
theorem successMass_ge_half {miss : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ᶠ n : ℕ in atTop, miss n ≤ Real.exp (-(δ) * scale n)) :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ successMass miss n := by
  filter_upwards [h, scale_grows.eventually_ge_atTop (Real.log 2 / δ)] with n hmiss hs
  have hlog2 : Real.log 2 ≤ δ * scale n := by
    have h' : Real.log 2 ≤ scale n * δ := (div_le_iff₀ hδ).mp hs
    linarith
  have hexp : Real.exp (-(δ) * scale n) ≤ (1 / 2 : ℝ) := by
    have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [hhalf]
    exact Real.exp_le_exp.mpr (by linarith)
  unfold successMass
  linarith [hmiss.trans hexp]

/-- The inverse success mass is at most `2` eventually. -/
theorem inv_successMass_le_two {miss : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ᶠ n : ℕ in atTop, miss n ≤ Real.exp (-(δ) * scale n)) :
    ∀ᶠ n : ℕ in atTop, (successMass miss n)⁻¹ ≤ 2 := by
  filter_upwards [successMass_ge_half hδ h] with n hn
  have hpos : (0 : ℝ) < successMass miss n :=
    lt_of_lt_of_le (by norm_num) hn
  rw [← one_div]
  calc
    (1 : ℝ) / successMass miss n ≤ 1 / (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hn
    _ = 2 := by norm_num

/-- **Success-to-cost, multiplicative form.**  The expected number of retries is
`(1 - miss)⁻¹ ≤ 2`, so the expected repeated work is at most twice the
single-attempt work. -/
theorem div_successMass_le_two_mul {work miss : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hwork : ∀ n, 0 ≤ work n)
    (hmiss : ∀ᶠ n : ℕ in atTop, miss n ≤ Real.exp (-(δ) * scale n)) :
    ∀ᶠ n : ℕ in atTop, work n / successMass miss n ≤ 2 * work n := by
  filter_upwards [inv_successMass_le_two hδ hmiss] with n hinv
  rw [div_eq_mul_inv]
  calc
    work n * (successMass miss n)⁻¹ ≤ work n * 2 :=
      mul_le_mul_of_nonneg_left hinv (hwork n)
    _ = 2 * work n := by ring

/-- **Success-to-cost, exponential form.**  If the single-attempt work is at
most `exp (costExponent n)`, the expected repeated work is at most
`exp (costExponent n + log 2)`.  The additive `log 2` is the constant retry
overhead. -/
theorem div_successMass_le_exp_add {work costExponent miss : ℕ → ℝ}
    (hwork : ∀ n, work n ≤ Real.exp (costExponent n))
    (hsm_nonneg : ∀ n, 0 ≤ successMass miss n)
    (hinv : ∀ᶠ n : ℕ in atTop, (successMass miss n)⁻¹ ≤ 2) :
    ∀ᶠ n : ℕ in atTop,
      work n / successMass miss n ≤ Real.exp (costExponent n + Real.log 2) := by
  filter_upwards [hinv] with n hinv
  have htwo : (2 : ℝ) = Real.exp (Real.log 2) :=
    (Real.exp_log (by norm_num)).symm
  calc
    work n / successMass miss n = work n * (successMass miss n)⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ Real.exp (costExponent n) * 2 :=
      mul_le_mul (hwork n) hinv (inv_nonneg.mpr (hsm_nonneg n))
        (Real.exp_pos _).le
    _ = Real.exp (costExponent n) * Real.exp (Real.log 2) := by
      rw [← htwo]
    _ = Real.exp (costExponent n + Real.log 2) := by rw [← Real.exp_add]

/-! ## 5. The reduced P1 bundle -/

/-- The P1 data with the two paper-level statements exposed as explicit
`Prop`s.  The elementary fields (cutoff, miss probability, work, overhead) are
the same as in `P1Inputs`; the success and cost fields are the props above. -/
structure P1SubInputs where
  /-- The prepass cutoff `B n`. -/
  cutoff : ℕ → ℝ
  /-- The cutoff covers the paper's `exp ((log n)^{2/3})` threshold. -/
  cutoff_ge_rough : ∀ᶠ n : ℕ in atTop, roughThreshold n ≤ cutoff n
  /-- The miss probability of the prepass. -/
  miss : ℕ → ℝ
  /-- A failure probability is nonnegative. -/
  miss_nonneg : ∀ n, 0 ≤ miss n
  /-- A failure probability is at most one. -/
  miss_le_one : ∀ n, miss n ≤ 1
  /-- **Paper-level success**: `PrepassSuccess` for this miss probability. -/
  success : PrepassSuccess miss
  /-- The exponential part of the prepass cost. -/
  costExponent : ℕ → ℝ
  /-- The cost exponent is nonnegative. -/
  costExponent_nonneg : ∀ n, 0 ≤ costExponent n
  /-- **Paper-level cost**: `costExponent = o (H)`. -/
  cost_subexp : PrepassCostSubexp costExponent
  /-- The charged expected work of the prepass. -/
  work : ℕ → ℝ
  /-- Work is nonnegative. -/
  work_nonneg : ∀ n, 0 ≤ work n
  /-- Polynomial overhead degree of the prepass. -/
  overhead : ℕ
  /-- The work is at most a polynomial in the bit length times
  `exp (costExponent n)`. -/
  work_le : ∀ n, work n ≤
    ((n.log2 : ℝ) + 1) ^ overhead * Real.exp (costExponent n)

namespace P1SubInputs

variable (S : P1SubInputs)

/-- The reduced P1 data builds the parent `P1Inputs` bundle. -/
def toP1Inputs : P1Inputs where
  cutoff := S.cutoff
  cutoff_ge_rough := S.cutoff_ge_rough
  miss := S.miss
  miss_nonneg := S.miss_nonneg
  miss_le_one := S.miss_le_one
  success := S.success
  costExponent := S.costExponent
  costExponent_nonneg := S.costExponent_nonneg
  costExponent_littleO := S.cost_subexp
  work := S.work
  work_nonneg := S.work_nonneg
  overhead := S.overhead
  work_le := S.work_le

/-- The success input is exactly the manuscript's `SubexpLoss` shape. -/
theorem subexpLoss : SubexpLoss S.miss := S.toP1Inputs.subexpLoss

/-- The `δ = 2` instance is the C5 prepass slot. -/
theorem slot :
    ∀ᶠ n : ℕ in atTop, S.miss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  S.toP1Inputs.slot

/-- The sublinear cost input in `δ`-slack form. -/
theorem costExponent_sublinear :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      S.costExponent n ≤ δ * scale n :=
  S.toP1Inputs.costExponent_sublinear

/-- The polynomial overhead is absorbed into an arbitrary positive exponent
slack. -/
theorem work_le_exp_add {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      S.work n ≤ Real.exp (S.costExponent n + δ * scale n) :=
  S.toP1Inputs.work_le_exp_add hδ

/-- The charged work, including polynomial overhead and the epoch `+1`, fits in
`exp (ε H)` for every `ε > 0`. -/
theorem work_add_one_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      S.work n + 1 ≤ Real.exp (ε * scale n) :=
  S.toP1Inputs.work_add_one_le_exp hε

/-- The paper's P1 leaf, built from the two explicit props and the elementary
work data.  The loss is the input miss probability and the cost exponent is the
input exponent; neither is replaced by zero. -/
def toP1Leaf : P1Leaf := S.toP1Inputs.toP1Leaf

/-- **Success-to-cost at the P1 endpoint.**  The expected repeated work
`work / (1 - miss)` — including the retries needed to amplify the prepass
success probability — still fits in `exp (ε H)` for every `ε > 0`.  The success
input only contributes the constant factor `2`, which is absorbed by the
`exp (o (H))` cost slack. -/
theorem repeated_work_add_one_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      S.work n / successMass S.miss n + 1 ≤ Real.exp (ε * scale n) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hε4 : 0 < ε / 4 := by positivity
  filter_upwards [S.work_add_one_le_exp hε2,
    successMass_ge_half (δ := ε / 4) hε4 (S.success (ε / 4) hε4),
    scale_grows.eventually_ge_atTop (Real.log 2 / (ε / 2))] with n hwork hp hs
  set E : ℝ := Real.exp ((ε / 2) * scale n) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2 : (2 : ℝ) ≤ E := by
    have hlog2 : Real.log 2 ≤ (ε / 2) * scale n := by
      have h' : Real.log 2 ≤ scale n * (ε / 2) := (div_le_iff₀ hε2).mp hs
      linarith
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ E := Real.exp_le_exp.mpr hlog2
  have hinv : (successMass S.miss n)⁻¹ ≤ 2 := by
    rw [← one_div]
    calc
      (1 : ℝ) / successMass S.miss n ≤ 1 / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hp
      _ = 2 := by norm_num
  have hdiv : S.work n / successMass S.miss n ≤ 2 * S.work n := by
    rw [div_eq_mul_inv]
    calc
      S.work n * (successMass S.miss n)⁻¹ ≤ S.work n * 2 :=
        mul_le_mul_of_nonneg_left hinv (S.work_nonneg n)
      _ = 2 * S.work n := by ring
  have hwork' : S.work n ≤ E := by
    have hpos : (0 : ℝ) < Real.exp ((ε / 2) * scale n) := Real.exp_pos _
    linarith
  calc
    S.work n / successMass S.miss n + 1
        ≤ 2 * S.work n + 1 := by linarith
    _ ≤ 2 * E := by linarith
    _ = E * 2 := by ring
    _ ≤ E * E := mul_le_mul_of_nonneg_left hE2 hEpos.le
    _ = Real.exp (ε * scale n) := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring

end P1SubInputs

/-! ## 6. The combined P1 sub-lemma reduction -/

/-- **The elementary P1 reduction.**  From the two explicit paper-level props and
the elementary data, the P1 bundle gives the manuscript's success statement, the
C5 `δ = 2` slot, the sublinear cost consequence, and the success-to-cost bound on
expected repeated work. -/
theorem p1Sub_reduction (S : P1SubInputs) :
    SubexpLoss S.miss ∧
      (∀ᶠ n : ℕ in atTop, S.miss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        S.costExponent n ≤ δ * scale n) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        S.work n / successMass S.miss n + 1 ≤ Real.exp (ε * scale n)) :=
  ⟨S.subexpLoss, S.slot, S.costExponent_sublinear,
    fun ε hε => S.repeated_work_add_one_le_exp (ε := ε) hε⟩

/-- **The trial-division gap, in the `PrepassCostSubexp` vocabulary.**  The
deterministic trial-division prepass satisfies the success half of P1 with
probability one, but its proved work envelope is not `exp (o (H))`.  Hence it
cannot be the P1 prepass at the paper cutoff. -/
theorem trialDivisionGap_sub :
    (∀ B : ℕ → ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      HardInput n → HasSmallPrimeFactor (B n : ℝ) n →
        (trialPrepass (B n) n).1 ≠ none) ∧
      (∀ B : ℕ → ℕ,
        (∀ᶠ n : ℕ in atTop, roughThreshold n ≤ (B n : ℝ)) →
          ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
            (B n : ℝ) ≤ Real.exp (ε * scale n))) ∧
      ¬ PrepassCostSubexp trialDivisionExponent :=
  ⟨trialPrepass_paper_success, not_trialPrepass_affordable_at_roughThreshold,
    trialDivision_cost_not_subexp⟩

/-! ## Axiom audit -/

#print axioms trialPrepass_splits
#print axioms trialPrepass_work_envelope
#print axioms trialDivisionExponent_eq
#print axioms logB_le_trialDivisionExponent
#print axioms trialDivisionExponent_nonneg
#print axioms trialPrepass_work_le_exp
#print axioms threshold_separation
#print axioms trialDivision_threshold_gap
#print axioms littleO_to_sublinear
#print axioms trialDivision_cost_not_subexp
#print axioms successMass_ge_half
#print axioms inv_successMass_le_two
#print axioms div_successMass_le_two_mul
#print axioms div_successMass_le_exp_add
#print axioms P1SubInputs.toP1Inputs
#print axioms P1SubInputs.subexpLoss
#print axioms P1SubInputs.slot
#print axioms P1SubInputs.costExponent_sublinear
#print axioms P1SubInputs.work_le_exp_add
#print axioms P1SubInputs.work_add_one_le_exp
#print axioms P1SubInputs.toP1Leaf
#print axioms P1SubInputs.repeated_work_add_one_le_exp
#print axioms p1Sub_reduction
#print axioms trialDivisionGap_sub

end

end Cogentic.RandomizedP1Sub
