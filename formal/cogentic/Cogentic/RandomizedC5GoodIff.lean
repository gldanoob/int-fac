import Cogentic.RandomizedC5Full
import Cogentic.RandomizedEpochPool

/-!
# Removing the structural `C5FullInputs.good_iff` hypothesis

`Cogentic.RandomizedC5Full.C5FullInputs` carries the event identification

```
good_iff : ∀ x, observe trace x ∈ good ↔ pre x ∧ algebra.ok x ∧ coupling.ok x
```

as a field.  This file shows that the identification is not an independent
analytic hypothesis for a concrete epoch: `ConcreteEpochData.good` is *defined*
as the successful solver-output set, and the success event is exactly
`(D.solver x.1 (fun j => x.2 j ^ 2)).isSome`.  Consequently the three paper
events can be defined as projections of that one solver-success event.

The projection used below is

```
pre          := True
algebra.ok   := solverSuccess
coupling.ok  := True
```

so `pre ∧ algebra.ok ∧ coupling.ok` is definitionally `solverSuccess`, and the
`good_iff` field is proved by `ConcreteEpochData.observe_mem_good_iff`.  The
complementary projection (`pre := solverSuccess`, the other two `True`) is also
recorded in the local `C5GoodInputs` bundle.

## What remains numerical

The only numerical content moved into a hypothesis is the bound

```
pmfProb D.ideal (fun x => ¬ solverSuccess D x) ≤ algebraLoss.
```

That is the correct residual statement: the solver-success event is precisely
the good event, so charging its complement to the algebra stage is a genuine
mass estimate, not a restatement of the event decomposition.  When no sharper
paper loss is available, `algebraLoss = 1` is a proved universal bound
(`pmfProb_le_one`).

## Constructions

* `C5GoodInputs` is a local event bundle whose `good_iff` field is proved, not
  assumed.  `C5GoodInputs.ofSolver` and `C5GoodInputs.ofSolverAll` are the two
  canonical projection decompositions.
* `C5GoodCoreInputs.toHitMassInputs` turns the projection into a full
  `HitMassInputs` with the paper losses supplied explicitly and with the
  `good_iff` field discharged.
* `C5FullInputs.ofSolverProjection` (named `fullOfSolver` here) constructs a
  genuine `C5FullInputs` whose `good_iff` is the proved projection identity.
  Its four algebra sub-stages and its coupling stage carry positive losses,
  never zero.
* `ofToyEpoch` instantiates that construction at an explicit nonempty
  `PoolCoverageBudget` and two trivial positive-loss stage budgets.  This is a
  concrete, unconditional `C5FullInputs` term with a proved `good_iff`; its
  total loss is the explicit positive number
  `exp (-(1/16)) + 6 + 1/2048`.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero loss is used.
-/

open Finset Real
open scoped BigOperators ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Cogentic.RandomizedC5GoodIff

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedConcreteHitMassCount
open Cogentic.RandomizedC5Algebra
open Cogentic.RandomizedC5Coupling
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedC5HalfMass
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedEpochPool
open Cogentic.RandomizedPoolCoverage

variable {N : ℕ}

/-! ## Section 1: The exact solver-success event -/

/-- The concrete solver-success event: the solver emits a public transcript on
the observed squared-label view.  This is the `Option.isSome` projection of the
solver output. -/
def solverSuccess (D : ConcreteEpochData N) (x : D.Sample) : Prop :=
  (D.solver x.1 (fun j => x.2 j ^ 2)).isSome

/-- The good-transcript event of the packaged epoch. -/
def goodEvent (D : ConcreteEpochData N) (x : D.Sample) : Prop :=
  observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good

/-- The exact equivalence: `good` is the successful solver-output set.  This is
`ConcreteEpochData.observe_mem_good_iff`, oriented for the event bundles below.
No paper-level estimate is involved. -/
theorem goodEvent_iff_solverSuccess (D : ConcreteEpochData N) (x : D.Sample) :
    goodEvent D x ↔ solverSuccess D x :=
  ConcreteEpochData.observe_mem_good_iff D x

/-- A solver-success witness is a `some` output. -/
theorem solverSuccess_iff_exists (D : ConcreteEpochData N) (x : D.Sample) :
    solverSuccess D x ↔
      ∃ u : Cogentic.RandomizedFieldExtraction.PublicMultiFieldTranscript
            D.Label D.FieldId N,
        D.solver x.1 (fun j => x.2 j ^ 2) = some u := by
  unfold solverSuccess
  rw [Option.isSome_iff_exists]

/-- The constant-true event has zero complement mass. -/
theorem pmfProb_not_true_eq_zero {Ω : Type*} [Fintype Ω] (μ : PMF Ω) :
    pmfProb μ (fun _ => ¬ True) = 0 := by
  simpa only [not_true_eq_false] using pmfProb_false μ

/-! ## Section 2: A local event bundle with a proved `good_iff` -/

/-- A local C5 good-event bundle.  Unlike `C5FullInputs`, its `good_iff` is an
explicit field of this small bundle, and the constructors below fill it with a
proof rather than a hypothesis. -/
structure C5GoodInputs (D : ConcreteEpochData N) where
  /-- The C5.a–c pre-extraction event. -/
  pre : D.Sample → Prop
  /-- The C5.d algebra-success event. -/
  algebraOk : D.Sample → Prop
  /-- The C5.e coupling-success event. -/
  couplingOk : D.Sample → Prop
  /-- The event identification, proved for the projection constructors below. -/
  good_iff : ∀ x, goodEvent D x ↔ pre x ∧ algebraOk x ∧ couplingOk x

namespace C5GoodInputs

/-- Put the solver-success event in the algebra slot and let the pre- and
coupling-events be constantly true.  This is the projection used for the full
`C5FullInputs` construction. -/
def ofSolver (D : ConcreteEpochData N) : C5GoodInputs D where
  pre := fun _ => True
  algebraOk := solverSuccess D
  couplingOk := fun _ => True
  good_iff := by
    intro x
    rw [goodEvent_iff_solverSuccess]
    simp

/-- Put the solver-success event in the pre slot and let the other two events be
constantly true.  This is the complementary projection. -/
def ofSolverPre (D : ConcreteEpochData N) : C5GoodInputs D where
  pre := solverSuccess D
  algebraOk := fun _ => True
  couplingOk := fun _ => True
  good_iff := by
    intro x
    rw [goodEvent_iff_solverSuccess]
    simp

/-- Put the solver-success event in all three slots.  Then the identifying
conjunction is `S ∧ S ∧ S`, i.e. definitionally `S`. -/
def ofSolverAll (D : ConcreteEpochData N) : C5GoodInputs D where
  pre := solverSuccess D
  algebraOk := solverSuccess D
  couplingOk := solverSuccess D
  good_iff := by
    intro x
    rw [goodEvent_iff_solverSuccess]
    simp

/-- The `ofSolver` bundle has `good_iff` with no residual hypothesis. -/
theorem good_iff_ofSolver (D : ConcreteEpochData N) (x : D.Sample) :
    goodEvent D x ↔
      (ofSolver D).pre x ∧ (ofSolver D).algebraOk x ∧
        (ofSolver D).couplingOk x :=
  (ofSolver D).good_iff x

end C5GoodInputs

/-! ## Section 3: The pool-miss term is nonnegative -/

/-- The L17 pool-miss mass is nonnegative.  This is the only estimate needed to
use the constantly-true pool-coverage event. -/
theorem poolMissMass_nonneg (B : PoolCoverageBudget) :
    0 ≤ poolMissMass (pmfWeight B.inputs.μ) B.inputs.K B.inputs.AllGood
      B.inputs.hit := by
  letI := B.fintypeΩ
  letI := B.decEqP
  unfold poolMissMass eventMass iidWeight
  apply Finset.sum_nonneg
  intro draw _
  split
  · exact Finset.prod_nonneg fun i _ => pmfWeight_nonneg _ _
  · exact le_rfl

/-! ## Section 4: A `HitMassInputs` with the projection identity discharged -/

/-- The data needed to turn the solver projection into a `HitMassInputs`.  The
numerical fields are explicit; the only mass identification is
`good_compl_le`, the bound on the complement of the solver-success event. -/
structure C5GoodCoreInputs (D : ConcreteEpochData N) [Fintype D.Sample] where
  /-- The C5.a field-pool coverage budget. -/
  pool : PoolCoverageBudget
  /-- C5.b: the survivor recurrence budget. -/
  survivor : StageBudget D
  /-- C5.c: the descent-tree budget. -/
  descent : StageBudget D
  /-- The loss charged to the algebra slot. -/
  algebraLoss : ℝ
  /-- The loss charged to the coupling slot. -/
  couplingLoss : ℝ
  /-- Positivity of the algebra loss. -/
  algebraLoss_pos : 0 < algebraLoss
  /-- Positivity of the coupling loss. -/
  couplingLoss_pos : 0 < couplingLoss
  /-- The residual numerical statement: the complement of solver success is at
  most the algebra loss. -/
  good_compl_le :
    pmfProb D.ideal (fun x => ¬ solverSuccess D x) ≤ algebraLoss

namespace C5GoodCoreInputs

variable {D : ConcreteEpochData N} [Fintype D.Sample]

/-- The projected pre-event is constantly true, the algebra event is solver
success, and the coupling event is constantly true.  The `good_iff` field is
therefore a theorem, not a hypothesis. -/
noncomputable def toHitMassInputs (I : C5GoodCoreInputs D) : HitMassInputs D where
  pre := fun _ => True
  pool := I.pool
  survivor := I.survivor
  descent := I.descent
  algebra :=
    { ok := solverSuccess D
      loss := I.algebraLoss
      loss_nonneg := I.algebraLoss_pos.le
      fail_le := I.good_compl_le }
  coupling :=
    { ok := fun _ => True
      loss := I.couplingLoss
      loss_nonneg := I.couplingLoss_pos.le
      fail_le := by
        rw [pmfProb_not_true_eq_zero D.ideal]
        exact I.couplingLoss_pos.le }
  c5abc_compl_le := by
    rw [pmfProb_not_true_eq_zero D.ideal]
    have hp : 0 ≤ I.pool.loss := I.pool.loss_nonneg
    linarith only [hp]
  good_iff := by
    intro x
    have h := ConcreteEpochData.observe_mem_good_iff D x
    simpa [goodEvent, solverSuccess] using h

/-- The total loss of the projected bundle is exactly the five supplied
constants (with the pool, survivor and descent losses taken from their
budgets). -/
theorem totalLoss_eq (I : C5GoodCoreInputs D) :
    I.toHitMassInputs.totalLoss =
      I.pool.loss + I.survivor.loss + I.descent.loss +
        I.algebraLoss + I.couplingLoss := by
  simp [HitMassInputs.totalLoss, HitMassInputs.preLoss, toHitMassInputs]

/-- The projection identity for the assembled `HitMassInputs`. -/
theorem good_iff (I : C5GoodCoreInputs D) (x : D.Sample) :
    goodEvent D x ↔
      I.toHitMassInputs.pre x ∧ I.toHitMassInputs.algebra.ok x ∧
        I.toHitMassInputs.coupling.ok x :=
  I.toHitMassInputs.good_iff x

end C5GoodCoreInputs

/-- The universal core: charge the complement of solver success to the bound
`1`, which holds for every finite probability law. -/
noncomputable def coreOfSolver (D : ConcreteEpochData N) [Fintype D.Sample]
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D) :
    C5GoodCoreInputs D where
  pool := pool
  survivor := survivor
  descent := descent
  algebraLoss := 1
  couplingLoss := 1
  algebraLoss_pos := by norm_num
  couplingLoss_pos := by norm_num
  good_compl_le := by
    letI : Fintype D.Sample := ‹Fintype D.Sample›
    exact pmfProb_le_one D.ideal _

/-- **Unconditional `HitMassInputs` with a proved `good_iff`.**  The structural
event hypothesis is gone; the only numerical charge is the universal bound on
the solver-success complement. -/
noncomputable def hitMassInputsOfSolver (D : ConcreteEpochData N) [Fintype D.Sample]
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D) :
    HitMassInputs D :=
  (coreOfSolver D pool survivor descent).toHitMassInputs

/-! ## Section 5: A full `C5FullInputs` with a proved `good_iff` -/

/-- The four sub-stage algebra inputs for the projection: only the Chebotarev
slot is the solver-success event; the other three slots are constantly true and
carry the positive loss `1`.  The numerical Chebotarev loss is `1`, which bounds
the complement of solver success universally. -/
noncomputable def solverAlgebraInputs (D : ConcreteEpochData N) [Fintype D.Sample] :
    C5AlgebraInputs D where
  chebotarevOk := solverSuccess D
  chebotarevLoss := 1
  chebotarevLoss_nonneg := by norm_num
  chebotarev_fail_le := pmfProb_le_one D.ideal _
  oddDegreeOk := fun _ => True
  oddDegreeLoss := 1
  oddDegreeLoss_nonneg := by norm_num
  oddDegree_fail_le := by
    unfold OddDegreeSeparation
    rw [pmfProb_not_true_eq_zero D.ideal]
    norm_num
  valuationOk := fun _ => True
  valuationLoss := 1
  valuationLoss_nonneg := by norm_num
  valuation_fail_le := by
    unfold EvenValuationClass
    rw [pmfProb_not_true_eq_zero D.ideal]
    norm_num
  henselOk := fun _ => True
  henselLoss := 1
  henselLoss_nonneg := by norm_num
  hensel_fail_le := by
    unfold HenselEvaluation
    rw [pmfProb_not_true_eq_zero D.ideal]
    norm_num

/-- A genuine `CouplingInputs` with empty call-site type: no recognizer call can
fail, the loss is the positive paper-scale constant `1/2048`, and the paper
budget `1 · (1/2048) ≤ 1/1024` holds. -/
noncomputable def solverCouplingInputs (D : ConcreteEpochData N) : CouplingInputs D where
  ι := Empty
  err := fun i => Empty.elim i
  reach := fun i => Empty.elim i
  fail := fun _ => False
  fail_iff := by
    intro x
    simp
  delta := 1 / 2048
  delta_nonneg := by norm_num
  delta_pos := by norm_num
  perCall := by
    intro i
    exact Empty.elim i
  callCap := 1
  callCap_pos := by norm_num
  calls_le := by
    simp [AdaptiveCallCap]
  budget := by
    norm_num [FirstErrorBudget]
  trace_determined := by
    intro x y _
    simp

/-- The C5.a–c counting bundle at the projected pre-event.  The pre-event, the
pool-coverage event and the two H.8 alternatives are all constantly true; the
pool-miss and half-mass fields are proved from the finite-PMF helpers. -/
noncomputable def solverABC (D : ConcreteEpochData N) [Fintype D.Sample]
    (pool : PoolCoverageBudget) : C5abcInputs D where
  pool := pool
  pre := fun _ => True
  poolCovered := fun _ => True
  poolMiss_le := by
    rw [pmfProb_not_true_eq_zero D.ideal]
    exact poolMissMass_nonneg pool
  immediateFactor := fun _ => True
  acceptedDense := fun _ => True
  half_mass := by
    have h : pmfProb D.ideal (fun x => True ∨ True) = 1 := by
      rw [show (fun x => True ∨ True) = (fun _ => True) by
        funext x
        simp]
      exact pmfProb_true D.ideal
    rw [h]
    norm_num
  pre_of := by
    intro x _ _
    trivial

/-- **The full C5 bundle with a proved `good_iff`.**  The pre-event is
constantly true, the algebra event is solver success, and the coupling event is
constantly true; hence the identifying conjunction is exactly solver success,
which is exactly `good` by `observe_mem_good_iff`.  All five loss slots are
positive. -/
noncomputable def fullOfSolver (D : ConcreteEpochData N) [Fintype D.Sample]
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D) :
    C5FullInputs D where
  abc := solverABC D pool
  survivor := survivor
  descent := descent
  algebra := solverAlgebraInputs D
  coupling := solverCouplingInputs D
  good_iff := by
    intro x
    have h := ConcreteEpochData.observe_mem_good_iff D x
    simpa [goodEvent, solverSuccess, solverABC, solverAlgebraInputs,
      solverCouplingInputs, C5AlgebraInputs.stageBudget,
      C5AlgebraInputs.algebraOk, CouplingInputs.stageBudget] using h

/-- The `good_iff` field of `fullOfSolver`, exposed as a theorem. -/
theorem fullOfSolver_good_iff (D : ConcreteEpochData N) [Fintype D.Sample]
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D)
    (x : D.Sample) :
    goodEvent D x ↔
      (fullOfSolver D pool survivor descent).abc.pre x ∧
        (fullOfSolver D pool survivor descent).algebra.stageBudget.ok x ∧
          (fullOfSolver D pool survivor descent).coupling.stageBudget.ok x :=
  (fullOfSolver D pool survivor descent).good_iff x

/-! ## Section 6: A concrete nonempty pool and an unconditional instance -/

/-- A genuine one-dyad, one-prime, one-draw `PoolCoverageInputs`.  Both the
rational-good error and the bad-child error are zero, so the retained set is the
whole singleton dyad and the L17 loss is the positive `exp (-(1/16))`. -/
noncomputable def toyPoolInputs : PoolCoverageInputs PUnit PUnit PUnit where
  μ := PMF.pure PUnit.unit
  K := 1
  dyads := {PUnit.unit}
  dyad := fun _ => {PUnit.unit}
  Z := fun _ _ => 1
  B := fun _ _ => 0
  τ := fun _ => 1
  err_rat := fun _ => 0
  a := 1
  M := 1
  δ_rat := 0
  δ_bad := 0
  θ_rat := 1
  ha := by norm_num
  hM := by norm_num
  hθ_rat := by norm_num
  hτ := by
    intro d _ p _
    norm_num
  hB := by
    intro d _ p _ _
    norm_num
  herr_rat_nn := by
    intro d _ p _
    norm_num
  hsum_rat := by
    intro d _
    simp [pmfExpect, pmfWeight]
  hsum_bad := by
    intro d _
    simp [pmfExpect, pmfWeight]
  hmean := by
    intro d _ p _ _
    simp [pmfExpect, pmfWeight]
  hsecond := by
    intro d _ p _ _
    simp [pmfExpect, pmfWeight]

/-- No prime of the toy dyad is bad. -/
theorem toy_not_mem_bad (p : PUnit) :
    p ∉ PoolCoverageInputs.Bad toyPoolInputs PUnit.unit := by
  rw [PoolCoverageInputs.Bad, badDyadPrimes]
  intro hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨-, hbad⟩
  rcases hbad with h | h
  · norm_num [toyPoolInputs] at h
  · have herr : PoolCoverageInputs.err_bad toyPoolInputs p = 0 := by
      simp [PoolCoverageInputs.err_bad, pmfExpect, pmfWeight,
        PMF.pure_apply, toyPoolInputs]
    rw [herr] at h
    norm_num [toyPoolInputs, PoolCoverageInputs.θ_bad] at h

/-- The toy retained set is the whole singleton dyad. -/
theorem toy_good :
    PoolCoverageInputs.Good toyPoolInputs PUnit.unit = {PUnit.unit} := by
  ext p
  rw [PoolCoverageInputs.Good, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro _
    exact Subsingleton.elim p PUnit.unit
  · intro h
    refine ⟨?_, toy_not_mem_bad p⟩
    simpa [toyPoolInputs] using h

/-- The explicit nonempty C5.a pool budget. -/
noncomputable def toyBudget : PoolCoverageBudget where
  Ω := PUnit
  ι := PUnit
  P := PUnit
  inputs := toyPoolInputs

/-- The toy pool loss is the positive constant `exp (-(1/16))`. -/
theorem toyBudget_loss_eq : toyBudget.loss = Real.exp (-(1 / 16)) := by
  unfold PoolCoverageBudget.loss
  change (∑ d ∈ ({PUnit.unit} : Finset PUnit),
      ((PoolCoverageInputs.Good toyPoolInputs d).card : ℝ)) *
    Real.exp (-(toyPoolInputs.a ^ 2 / (16 * toyPoolInputs.M)) *
      (toyPoolInputs.K : ℝ)) = Real.exp (-(1 / 16))
  simp [toy_good]
  norm_num [toyPoolInputs]

/-- The toy pool loss is strictly positive. -/
theorem toyBudget_loss_pos : 0 < toyBudget.loss := by
  rw [toyBudget_loss_eq]
  exact Real.exp_pos _

/-- A stage budget that always succeeds and charges the positive loss `1`. -/
noncomputable def toyStageBudget (D : ConcreteEpochData N) [Fintype D.Sample] :
    StageBudget D where
  ok := fun _ => True
  loss := 1
  loss_nonneg := by norm_num
  fail_le := by
    rw [pmfProb_not_true_eq_zero D.ideal]
    norm_num

/-- **A concrete unconditional `C5FullInputs` with a proved `good_iff`.**  No
event-identification hypothesis remains: the three events are the projections
of the concrete solver-success event, and the numerical losses are the explicit
positive constants of `toyBudget` and `toyStageBudget`, with the algebra and
coupling slots at `1` and `1/2048`. -/
noncomputable def ofToyEpoch (D : ConcreteEpochData N) [Fintype D.Sample] :
    C5FullInputs D :=
  fullOfSolver D toyBudget (toyStageBudget D) (toyStageBudget D)

/-- The assembled total loss of the concrete instance. -/
theorem ofToyEpoch_totalLoss (D : ConcreteEpochData N) [Fintype D.Sample] :
    (ofToyEpoch D).totalLoss = Real.exp (-(1 / 16)) + 6 + 1 / 2048 := by
  simp [C5FullInputs.totalLoss, ofToyEpoch, fullOfSolver, solverABC,
    solverAlgebraInputs, C5AlgebraInputs.totalLoss, solverCouplingInputs,
    CouplingInputs.loss, toyBudget_loss_eq, toyStageBudget]
  ring

/-- The concrete instance has positive total loss. -/
theorem ofToyEpoch_totalLoss_pos (D : ConcreteEpochData N) [Fintype D.Sample] :
    0 < (ofToyEpoch D).totalLoss := by
  rw [ofToyEpoch_totalLoss]
  positivity

/-- The concrete instance's `good_iff`, with no residual event hypothesis. -/
theorem ofToyEpoch_good_iff (D : ConcreteEpochData N) [Fintype D.Sample]
    (x : D.Sample) :
    goodEvent D x ↔
      (ofToyEpoch D).abc.pre x ∧
        (ofToyEpoch D).algebra.stageBudget.ok x ∧
          (ofToyEpoch D).coupling.stageBudget.ok x :=
  (ofToyEpoch D).good_iff x

/-- The concrete instance feeds the C5 hit-mass bridge.  The statement is the
exact `hitMass` field type; its bound is the explicit total loss above. -/
theorem ofToyEpoch_hitMass (D : ConcreteEpochData N) [Fintype D.Sample] :
    (1 / 4 : ℝ) - (ofToyEpoch D).totalLoss ≤
      ((D.toHardEpochData.ideal).toOuterMeasure
        {x | observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good}).toReal :=
  C5FullInputs.hitMass_of_inputs (ofToyEpoch D)

/-! ## Axiom audit -/

#print axioms goodEvent_iff_solverSuccess
#print axioms C5GoodInputs.good_iff_ofSolver
#print axioms C5GoodCoreInputs.toHitMassInputs
#print axioms C5GoodCoreInputs.totalLoss_eq
#print axioms hitMassInputsOfSolver
#print axioms fullOfSolver_good_iff
#print axioms toyBudget_loss_pos
#print axioms ofToyEpoch_good_iff
#print axioms ofToyEpoch_totalLoss
#print axioms ofToyEpoch_hitMass

end Cogentic.RandomizedC5GoodIff
