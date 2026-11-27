import Cogentic.RandomizedConcreteHitMass
import Cogentic.RandomizedEpochAlgebra
import Cogentic.RandomizedEllipticAndGaussian

/-!
# C5.e: the recognizer-coupling stage budget

Blueprint C5.e is leaf **L39** (KB H.8 p.141):

> Recognizer errors in an adaptive first-error union bound `≤ 1/1024`.
> `trace` is shared by the ideal and actual laws, so this goes into `γ`, not `ε`.

`Cogentic.RandomizedConcreteHitMass` records C5.e as an opaque paper-level
`StageBudget` field of `HitMassInputs`.  This file replaces that field by an
explicit decomposition and proves the `StageBudget` reduction.

The decomposition follows the two sentences of L39.

* **The adaptive first-error union bound (e1–e3).**
  A recognizer run may invoke a recognizer at adaptively chosen call sites
  `i : ι`; write `reach i x` for "site `i` is reached on outcome `x`" and
  `err i x` for "the recognizer errs at site `i` on outcome `x`".  The failure
  event is `fail x ↔ ∃ i, reach i x ∧ err i x`; because `reach` is an
  arbitrary history-dependent predicate, this is exactly the first-error event
  of an adaptive protocol (the earliest reached error is one of the reached
  errors, and no independence between call sites is used).
  `pmfProb_firstError_finset_le_card_mul`, `pmfProb_firstError_le_card_mul`,
  `pmfProb_firstError_le_callCap` and `pmfProb_firstError_le_inv1024` prove the
  union bound `P(fail) ≤ #calls · δ` and its arithmetic specialisations.  These
  are genuine proofs, not inputs.

* **The paper-level inputs (P1–P4), kept as explicit `Prop`s.**
  - `PerCallBound D err δ` — every call errs with ideal probability at most
    `δ`, uniformly over the field/class data (the recognizer rate; in the paper
    this is the L27.1 ECM / public elliptic recognition rate, applied uniformly
    over the finite group `H_D`).
  - `AdaptiveCallCap (card ι) callCap` — the adaptive schedule reaches at most
    `callCap` recognizer sites (the H.8 polynomial call cap).
  - `FirstErrorBudget callCap δ` — the product of the two is at most `1/1024`.
    This is the numerical content of L39 and is *not* proved here; it is the
    paper's quota choice.
  - `TraceDetermined D fail` — the recognizer-coupling event is a property of
    the public trace shared by the ideal and actual laws.

* **The `γ` side (e4–e6).**
  `exists_public_set_of_trace_determined` proves that a trace-determined event
  is a preimage of a set of public transcripts, so `fail` (equivalently
  `CouplingInputs.stageBudget.ok`) is a public-trace event.  This is the formal
  content of "the trace is shared ... so this goes into `γ`, not `ε`":
  `hitMassInputsWithCoupling` replaces only the C5.e field of `HitMassInputs`,
  and `goodMass_lower_withCoupling` / `assembledAttempt_hit_prob_ge_withCoupling`
  show that the resulting loss is subtracted from the good-transcript mass
  `γ = 1/4 - loss`, while the TV error `ε` enters exactly once, unchanged.

The paper reading used for P1/P3 is `research/keybreak-polynomial-bit-probes.md`:
couple the capped run to the unlimited run up to the first overflow, control
every eventual relation product by a union bound on the finite group `H_D`, and
note that the coupling error is uniform over fields, so it is subtracted from
the good-field success probability in H.8 rather than added to the sampling TV.
The relevant recognizer failure rates are those of
`RandomizedEllipticAndGaussian.twoStageRecognizer_fail_le` (L27.1/L30); this
file keeps the per-call bound abstract, as `PerCallBound`, because
`ConcreteEpochData` does not expose the recognizer's internal PMF.

The file contains no `sorry`, `admit`, `axiom`, or `native_decide`, and no
loss, mass, count or error is set to zero: the recognizer makes at least one
call with a positive per-call error, and `CouplingInputs.loss_pos` records that
the resulting budget is positive.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace Cogentic.RandomizedC5Coupling

open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedEpochAlgebra
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw

noncomputable section

/-! ## Section 1: The adaptive first-error union bound -/

/-- **Finite union bound.**  If every event `E i`, `i ∈ s`, has probability at
most `δ`, then the probability that some `E i` occurs is at most `|s| · δ`.
This is the elementary counting step behind the adaptive first-error bound. -/
theorem pmfProb_exists_finset_le_card_mul {Ω ι : Type*} [Fintype Ω]
    (μ : PMF Ω) (s : Finset ι) (E : ι → Ω → Prop) {δ : ℝ}
    (h : ∀ i ∈ s, pmfProb μ (E i) ≤ δ) :
    pmfProb μ (fun ω => ∃ i ∈ s, E i ω) ≤ (s.card : ℝ) * δ := by
  calc
    pmfProb μ (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, pmfProb μ (E i) :=
      pmfProb_exists_le_sum μ s E
    _ ≤ ∑ _i ∈ s, δ := Finset.sum_le_sum h
    _ = (s.card : ℝ) * δ := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- **Adaptive first-error union bound, finite-call form.**  The event "some
reached call errs" is contained in the union of the per-call error events, so
it has probability at most `|s| · δ`.  The reachability predicate `reach` is
arbitrary: it may encode the whole adaptive history, and no independence of
the call sites is assumed. -/
theorem pmfProb_firstError_finset_le_card_mul {Ω ι : Type*} [Fintype Ω]
    (μ : PMF Ω) (s : Finset ι) (reach err : ι → Ω → Prop) {δ : ℝ}
    (h : ∀ i ∈ s, pmfProb μ (err i) ≤ δ) :
    pmfProb μ (fun ω => ∃ i ∈ s, reach i ω ∧ err i ω) ≤ (s.card : ℝ) * δ := by
  refine (pmfProb_mono μ ?_).trans (pmfProb_exists_finset_le_card_mul μ s err h)
  intro ω hω
  obtain ⟨i, hi, _hreach, herr⟩ := hω
  exact ⟨i, hi, herr⟩

/-- **Adaptive first-error union bound over all call sites.** -/
theorem pmfProb_firstError_le_card_mul {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (μ : PMF Ω) (reach err : ι → Ω → Prop) {δ : ℝ}
    (h : ∀ i, pmfProb μ (err i) ≤ δ) :
    pmfProb μ (fun ω => ∃ i, reach i ω ∧ err i ω) ≤ (Fintype.card ι : ℝ) * δ := by
  classical
  simpa using
    pmfProb_firstError_finset_le_card_mul μ (Finset.univ) reach err
      (fun i _ => h i)

/-- **Adaptive first-error union bound at the declared call cap.** -/
theorem pmfProb_firstError_le_callCap {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (μ : PMF Ω) (reach err : ι → Ω → Prop) {δ : ℝ} {callCap : ℕ}
    (hδ : 0 ≤ δ) (hcard : Fintype.card ι ≤ callCap)
    (h : ∀ i, pmfProb μ (err i) ≤ δ) :
    pmfProb μ (fun ω => ∃ i, reach i ω ∧ err i ω) ≤ (callCap : ℝ) * δ := by
  have hcardR : (Fintype.card ι : ℝ) ≤ (callCap : ℝ) := by exact_mod_cast hcard
  exact (pmfProb_firstError_le_card_mul μ reach err h).trans
    (mul_le_mul_of_nonneg_right hcardR hδ)

/-- **The L39 numerical form.**  If the call cap times the per-call error is at
most `1/1024`, then the adaptive first-error probability is at most `1/1024`. -/
theorem pmfProb_firstError_le_inv1024 {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (μ : PMF Ω) (reach err : ι → Ω → Prop) {δ : ℝ} {callCap : ℕ}
    (hδ : 0 ≤ δ) (hcard : Fintype.card ι ≤ callCap)
    (h : ∀ i, pmfProb μ (err i) ≤ δ)
    (hbudget : (callCap : ℝ) * δ ≤ 1 / 1024) :
    pmfProb μ (fun ω => ∃ i, reach i ω ∧ err i ω) ≤ 1 / 1024 :=
  (pmfProb_firstError_le_callCap μ reach err hδ hcard h).trans hbudget

/-! ## Section 2: Public-trace events ("into `γ`, not `ε`") -/

/-- **A trace-determined event is public.**  If an event is constant on the
fibres of the shared trace map, then it is the preimage of a set of public
transcripts.  This is the structural justification for charging the L39
coupling error to the good-transcript mass rather than to the TV error: the
event lives on the common public trace. -/
theorem exists_public_set_of_trace_determined {Ω Public : Type*}
    (trace : Ω → Public) (E : Ω → Prop)
    (h : ∀ x y, trace x = trace y → (E x ↔ E y)) :
    ∃ S : Set Public, ∀ x, E x ↔ trace x ∈ S := by
  refine ⟨trace '' {x | E x}, fun x => ⟨fun hx => ⟨x, hx, rfl⟩, ?_⟩⟩
  rintro ⟨y, hy, hxy⟩
  exact (h y x hxy).mp hy

/-! ## Section 3: The explicit C5.e paper inputs -/

/-- **C5.e paper input P1 (uniform per-call recognizer error).**  Every
recognizer call errs with ideal probability at most `δ`, uniformly over the
call site and the field/class data.  In the paper this is the L27.1 ECM /
public elliptic recognition rate, applied uniformly over the finite group
`H_D`. -/
def PerCallBound {N : ℕ} (D : ConcreteEpochData N) {ι : Type*}
    (err : ι → D.Sample → Prop) (δ : ℝ) : Prop :=
  ∀ i, pmfProb D.ideal (err i) ≤ δ

/-- **C5.e paper input P2 (adaptive call cap).**  The adaptive recognizer
schedule reaches at most `callCap` call sites. -/
def AdaptiveCallCap (calls callCap : ℕ) : Prop :=
  calls ≤ callCap

/-- **C5.e paper input P3 (the L39 numerical budget).**  The call cap times the
per-call recognizer error is at most `1/1024`.  This is the paper's quota
choice, kept as an explicit `Prop`; it is not proved here. -/
def FirstErrorBudget (callCap : ℕ) (δ : ℝ) : Prop :=
  (callCap : ℝ) * δ ≤ 1 / 1024

/-- **C5.e paper input P4 (shared public trace).**  The recognizer-coupling
failure event is determined by the public trace that the ideal and actual laws
share.  This is the "`trace` is shared ... so this goes into `γ`" sentence of
L39, isolated as a structural hypothesis. -/
def TraceDetermined {N : ℕ} (D : ConcreteEpochData N)
    (fail : D.Sample → Prop) : Prop :=
  ∀ x y, observe D.toHardEpochData.trace x = observe D.toHardEpochData.trace y →
    (fail x ↔ fail y)

/-- **The C5.e recognizer-coupling inputs.**

The first four fields are data/definitional (`ι`, `err`, `reach`, `fail` and
the equivalence `fail_iff`); the paper-level content is exactly `perCall`,
`calls_le`, `budget` and `trace_determined`. -/
structure CouplingInputs {N : ℕ} (D : ConcreteEpochData N) where
  /-- The finite set of adaptively reachable recognizer call sites. -/
  ι : Type
  [fintypeι : Fintype ι]
  /-- The recognizer error event at each call site. -/
  err : ι → D.Sample → Prop
  /-- The (history-dependent) reachability predicate of each call site. -/
  reach : ι → D.Sample → Prop
  /-- The adaptive first-error event. -/
  fail : D.Sample → Prop
  /-- Failure means that some reached recognizer call errs. -/
  fail_iff : ∀ x, fail x ↔ ∃ i, reach i x ∧ err i x
  /-- The uniform per-call recognizer error. -/
  delta : ℝ
  delta_nonneg : 0 ≤ delta
  delta_pos : 0 < delta
  /-- P1: uniform per-call error bound. -/
  perCall : PerCallBound D err delta
  /-- P2: the adaptive call cap. -/
  callCap : ℕ
  callCap_pos : 0 < callCap
  calls_le : AdaptiveCallCap (Fintype.card ι) callCap
  /-- P3: the L39 numerical budget `callCap · δ ≤ 1/1024`. -/
  budget : FirstErrorBudget callCap delta
  /-- P4: the coupling event is a public-trace event. -/
  trace_determined : TraceDetermined D fail

attribute [instance] CouplingInputs.fintypeι

namespace CouplingInputs

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The C5.e loss `callCap · δ`. -/
def loss (C : CouplingInputs D) : ℝ :=
  (C.callCap : ℝ) * C.delta

/-- The loss is positive: at least one recognizer call is made and its error
probability is positive. -/
theorem loss_pos (C : CouplingInputs D) : 0 < C.loss := by
  unfold loss
  exact mul_pos (by exact_mod_cast C.callCap_pos) C.delta_pos

theorem loss_nonneg (C : CouplingInputs D) : 0 ≤ C.loss := C.loss_pos.le

/-- The paper's numerical L39 budget, in loss notation. -/
theorem loss_le_inv1024 (C : CouplingInputs D) : C.loss ≤ 1 / 1024 :=
  C.budget

/-- The recognizer-coupling loss is well below the `1/4` good-mass margin. -/
theorem loss_le_quarter (C : CouplingInputs D) : C.loss ≤ 1 / 4 :=
  C.loss_le_inv1024.trans (by norm_num)

/-- **Adaptive first-error bound for the coupling event.**  The ideal mass of
the C5.e failure event is at most `callCap · δ`. -/
theorem fail_le_loss [Fintype D.Sample] (C : CouplingInputs D) :
    pmfProb D.ideal C.fail ≤ C.loss := by
  have h := pmfProb_firstError_le_callCap D.ideal C.reach C.err C.delta_nonneg
    C.calls_le C.perCall
  have hcongr : pmfProb D.ideal C.fail =
      pmfProb D.ideal (fun x => ∃ i, C.reach i x ∧ C.err i x) :=
    pmfProb_congr D.ideal C.fail_iff
  rw [hcongr]
  simpa [loss] using h

/-- The L39 numerical failure bound `≤ 1/1024`. -/
theorem fail_le_inv1024 [Fintype D.Sample] (C : CouplingInputs D) :
    pmfProb D.ideal C.fail ≤ 1 / 1024 :=
  C.fail_le_loss.trans C.loss_le_inv1024

/-- The recognizer coupling succeeds on all but `1/1024` of the ideal mass. -/
theorem ok_mass_ge [Fintype D.Sample] (C : CouplingInputs D) :
    (1 : ℝ) - 1 / 1024 ≤ pmfProb D.ideal (fun x => ¬ C.fail x) := by
  rw [pmfProb_compl_eq_one_sub]
  linarith [C.fail_le_inv1024]

/-- **The C5.e `StageBudget` reduction (general loss form).** -/
def stageBudget [Fintype D.Sample] (C : CouplingInputs D) : StageBudget D where
  ok := fun x => ¬ C.fail x
  loss := C.loss
  loss_nonneg := C.loss_nonneg
  fail_le := by
    have hcongr : pmfProb D.ideal (fun x => ¬ ¬ C.fail x) = pmfProb D.ideal C.fail :=
      pmfProb_congr D.ideal (fun x => by simp)
    rw [hcongr]
    exact C.fail_le_loss

/-- **The C5.e `StageBudget` reduction in the paper's literal form**: loss
exactly `1/1024`. -/
def stageBudgetPaper [Fintype D.Sample] (C : CouplingInputs D) : StageBudget D where
  ok := fun x => ¬ C.fail x
  loss := 1 / 1024
  loss_nonneg := by norm_num
  fail_le := by
    have hcongr : pmfProb D.ideal (fun x => ¬ ¬ C.fail x) = pmfProb D.ideal C.fail :=
      pmfProb_congr D.ideal (fun x => by simp)
    rw [hcongr]
    exact C.fail_le_inv1024

/-- **`StageBudget` specification.**  The constructed budget charges a positive
loss, that loss is at most `1/1024`, and the stage fails with ideal mass at
most `1/1024`. -/
theorem stageBudget_spec [Fintype D.Sample] (C : CouplingInputs D) :
    0 < C.stageBudget.loss ∧ C.stageBudget.loss ≤ 1 / 1024 ∧
      pmfProb D.ideal (fun x => ¬ C.stageBudget.ok x) ≤ 1 / 1024 := by
  refine ⟨C.loss_pos, C.loss_le_inv1024, ?_⟩
  exact C.stageBudget.fail_le.trans C.loss_le_inv1024

/-- `stageBudgetPaper` has the exact paper loss and the exact paper failure
bound. -/
theorem stageBudgetPaper_spec [Fintype D.Sample] (C : CouplingInputs D) :
    C.stageBudgetPaper.loss = 1 / 1024 ∧
      pmfProb D.ideal (fun x => ¬ C.stageBudgetPaper.ok x) ≤ 1 / 1024 :=
  ⟨rfl, C.stageBudgetPaper.fail_le⟩

/-- **P4, made explicit.**  The failure event is a preimage of the shared public
trace. -/
theorem exists_trace_fail_set (C : CouplingInputs D) :
    ∃ S : Set (Option (PublicMultiFieldTranscript D.Label D.FieldId N)),
      ∀ x, C.fail x ↔ observe D.toHardEpochData.trace x ∈ S :=
  exists_public_set_of_trace_determined
    (fun x => observe D.toHardEpochData.trace x) C.fail C.trace_determined

/-- P4 for the success event: `stageBudget.ok` is also a public-trace event. -/
theorem exists_trace_ok_set [Fintype D.Sample] (C : CouplingInputs D) :
    ∃ S : Set (Option (PublicMultiFieldTranscript D.Label D.FieldId N)),
      ∀ x, C.stageBudget.ok x ↔ observe D.toHardEpochData.trace x ∉ S := by
  obtain ⟨S, hS⟩ := C.exists_trace_fail_set
  refine ⟨S, fun x => ?_⟩
  rw [show C.stageBudget.ok x = ¬ C.fail x from rfl, hS x]

end CouplingInputs

/-! ## Section 4: Rebuilding the C5 bundle and the `γ`-side accounting -/

variable {N : ℕ} {D : ConcreteEpochData N}

/-- **Replace the C5.e field of `HitMassInputs` by the constructed budget.**
All C5.a–d data are unchanged; only the recognizer-coupling `StageBudget` is
the one constructed from `CouplingInputs`.  The `hgood` hypothesis is the
paper's good-event definition: the concrete good set is exactly
`pre ∧ algebra.ok ∧ coupling.ok`. -/
def hitMassInputsWithCoupling [Fintype D.Sample] (I : HitMassInputs D) (C : CouplingInputs D)
    (hgood : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        I.pre x ∧ I.algebra.ok x ∧ C.stageBudget.ok x) :
    HitMassInputs D where
  pre := I.pre
  pool := I.pool
  survivor := I.survivor
  descent := I.descent
  algebra := I.algebra
  coupling := C.stageBudget
  c5abc_compl_le := I.c5abc_compl_le
  good_iff := hgood

/-- The total loss after the C5.e replacement: only the coupling slot changed,
and it is now the explicit `callCap · δ`. -/
theorem totalLoss_withCoupling [Fintype D.Sample] (I : HitMassInputs D) (C : CouplingInputs D)
    (hgood : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        I.pre x ∧ I.algebra.ok x ∧ C.stageBudget.ok x) :
    (hitMassInputsWithCoupling I C hgood).totalLoss =
      I.preLoss + I.algebra.loss + C.loss := by
  simp [HitMassInputs.totalLoss, HitMassInputs.preLoss, hitMassInputsWithCoupling,
    CouplingInputs.stageBudget]

/-- **C5.e is charged to `γ`.**  With the recognizer-coupling budget in place,
the ideal good-transcript mass is at least `1/4` minus the C5.a–c/D losses and
the explicit edge `callCap · δ`.  No TV error appears in this statement: the
coupling loss sits on the good-mass side. -/
theorem goodMass_lower_withCoupling [Fintype D.Sample]
    (I : HitMassInputs D) (C : CouplingInputs D)
    (hgood : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        I.pre x ∧ I.algebra.ok x ∧ C.stageBudget.ok x) :
    (1 / 4 : ℝ) - (I.preLoss + I.algebra.loss + C.loss) ≤
      pmfProb D.ideal
        (fun x => observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) := by
  have h := (hitMassInputsWithCoupling I C hgood).goodMass_lower
  rwa [totalLoss_withCoupling] at h

/-- **C5.e in the paper's literal `1/1024` form.** -/
theorem goodMass_lower_withCouplingPaper [Fintype D.Sample]
    (I : HitMassInputs D) (C : CouplingInputs D)
    (hgood : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        I.pre x ∧ I.algebra.ok x ∧ C.stageBudget.ok x) :
    (1 / 4 : ℝ) - (I.preLoss + I.algebra.loss + 1 / 1024) ≤
      pmfProb D.ideal
        (fun x => observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) := by
  have h := goodMass_lower_withCoupling (I := I) (C := C) hgood
  have hle : I.preLoss + I.algebra.loss + C.loss ≤
      I.preLoss + I.algebra.loss + 1 / 1024 := by
    linarith [C.loss_le_inv1024]
  linarith only [h, hle]

/-- **C5.e at the final split probability.**  The assembled epoch attempt hits
with probability at least `((1/4 - preLoss - algebra.loss - callCap·δ)/2) - ε`.
The coupling loss is inside the `γ` bracket and is halved together with `γ`;
the TV error `ε` appears exactly once.  This is the formal version of "this
goes into `γ`, not `ε`". -/
theorem assembledAttempt_hit_prob_ge_withCoupling [Fintype D.Sample]
    (I : HitMassInputs D) (C : CouplingInputs D)
    (hgood : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        I.pre x ∧ I.algebra.ok x ∧ C.stageBudget.ok x)
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hcheck : D.toHardEpochData.CongruenceCheck)
    (huniform : D.toHardEpochData.HiddenUniform)
    (hbudget : I.preLoss + I.algebra.loss + C.loss ≤ 1 / 4)
    {ε : ℝ}
    (hTV : pmfTotalVariation D.toHardEpochData.ideal D.toHardEpochData.actual ≤ ε) :
    ((1 / 4 : ℝ) - (I.preLoss + I.algebra.loss + C.loss)) / 2 - ε ≤
      ((D.toHardEpochData.actual.map (D.toHardEpochData.assembledAttempt hN)).toOuterMeasure
        {o | o.1 ≠ none}).toReal := by
  have hbudget' : (hitMassInputsWithCoupling I C hgood).totalLoss ≤ 1 / 4 := by
    rwa [totalLoss_withCoupling]
  have h := assembledAttempt_hit_prob_ge_of_inputs D
    (hitMassInputsWithCoupling I C hgood) hN ho hnot hcheck huniform hbudget' hTV
  rwa [totalLoss_withCoupling] at h

/-- **C5.e as a positive constant margin.**  Since the recognizer budget is at
most `1/1024`, any remaining C5.a–d margin `1/4 - 1/1024 - preLoss -
algebra.loss` is positive whenever the C5.d loss leaves room; the recognizer
coupling does not consume the whole `1/4`. -/
theorem coupling_does_not_consume_quarter (C : CouplingInputs D) :
    (1 : ℝ) / 4 - 1 / 1024 ≤ 1 / 4 - C.loss := by
  linarith [C.loss_le_inv1024]

/-! ## Axiom audit -/

#print axioms pmfProb_exists_finset_le_card_mul
#print axioms pmfProb_firstError_finset_le_card_mul
#print axioms pmfProb_firstError_le_card_mul
#print axioms pmfProb_firstError_le_callCap
#print axioms pmfProb_firstError_le_inv1024
#print axioms exists_public_set_of_trace_determined
#print axioms CouplingInputs.loss_pos
#print axioms CouplingInputs.loss_nonneg
#print axioms CouplingInputs.loss_le_inv1024
#print axioms CouplingInputs.loss_le_quarter
#print axioms CouplingInputs.fail_le_loss
#print axioms CouplingInputs.fail_le_inv1024
#print axioms CouplingInputs.ok_mass_ge
#print axioms CouplingInputs.stageBudget
#print axioms CouplingInputs.stageBudgetPaper
#print axioms CouplingInputs.stageBudget_spec
#print axioms CouplingInputs.stageBudgetPaper_spec
#print axioms CouplingInputs.exists_trace_fail_set
#print axioms CouplingInputs.exists_trace_ok_set
#print axioms totalLoss_withCoupling
#print axioms goodMass_lower_withCoupling
#print axioms goodMass_lower_withCouplingPaper
#print axioms assembledAttempt_hit_prob_ge_withCoupling
#print axioms coupling_does_not_consume_quarter

end

end Cogentic.RandomizedC5Coupling
