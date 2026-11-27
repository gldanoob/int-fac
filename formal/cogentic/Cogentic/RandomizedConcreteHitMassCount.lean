import Cogentic.RandomizedConcreteHitMass

/-!
# The C5.a–c half-mass counting field `c5abc_compl_le`

`Cogentic.RandomizedConcreteHitMass.HitMassInputs.c5abc_compl_le` is the one
paper-level numerical field of the concrete C5 bridge:

```
pmfProb D.ideal (fun x => ¬ pre x) ≤ 1 / 2 + pool.loss
```

where `pre` is the C5.a–c pre-extraction event and `pool.loss` is the C5.a
field-pool miss loss.  In the paper (KeyBreak Proposition H.8 p.141) this is the
statement that at least `1 / 2 - o(1)` of the ideal mass **either** finds an
immediate factor **or** produces an accepted field whose good-prime sets are
dense in every selected band.

This file does not postulate that field.  It records the two genuinely separate
ingredients and proves the numerical assembly:

1. **C5.a pool coverage.**  The event `poolCovered` that the `K`-fold field pool
   retains a hit in every used dyad.  Its ideal-law failure mass is dominated by
   the L17 pool-miss mass
   `poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K pool.inputs.AllGood
   pool.inputs.hit`, and hence by `pool.loss` through the existing theorem
   `PoolCoverageBudget.missMass_le_loss`
   (which in turn is `PoolCoverageInputs.missMass_le_trimmed_exp`, assembled from
   `survivor_prob_ge`, `single_prime_hit_prob`, the dyad trimming and the pool
   union bound in `RandomizedEpochPool` / `RandomizedFieldPoolDescent`).  The
   domination itself is the only interface hypothesis: the ideal law on
   `D.Sample` and the abstract pool law `pool.inputs.μ` live on different finite
   spaces, so the paper's "ideal pool draw is the `K`-fold product of `μ`" is
   recorded explicitly instead of being silently coerced.
2. **H.8 half-mass counting.**  The event that the sample *either* yields an
   immediate factor *or* yields an accepted field with dense good-prime sets in
   every selected band has ideal mass at least `1 / 2`.  This is the smallest
   explicit paper-level counting statement; it is a single `Prop` field, not an
   axiom.

Given these, `pre` only has to contain `poolCovered ∧ (immediateFactor ∨
acceptedDense)`.  The complement is then covered by
`¬ poolCovered ∨ ¬ (immediateFactor ∨ acceptedDense)`, and the union bound gives

```
P(¬ pre) ≤ P(¬ poolCovered) + (1 - P(immediateFactor ∨ acceptedDense))
         ≤ pool.loss + 1 / 2.
```

Nothing is set to `1` by fiat: `1 / 2` comes from the H.8 counting field and
`pool.loss` from the proved C5.a estimate.  There is no `sorry`, `admit`,
`axiom`, or `native_decide`; the only non-derived inputs are the two explicitly
documented `Prop` fields above.

`C5abcInputs.toHitMassInputs` fills the `c5abc_compl_le` field of the existing
`HitMassInputs` structure, so a caller only has to provide the other four stage
budgets and the `good_iff` identification.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace Cogentic.RandomizedConcreteHitMassCount

open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedEpochPool
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedPoolCoverage
open Cogentic.RandomizedHiddenOutputLaw

/-- The C5.a–c counting data behind `HitMassInputs.c5abc_compl_le`.

`pre` is the paper's pre-extraction event.  `poolCovered` is the C5.a event that
the field pool covers every retained prime; its failure is charged to the L17
pool-miss mass.  `immediateFactor` and `acceptedDense` are the two alternatives
of the H.8 half-mass counting statement.  The final field says that `pre`
contains the conjunction of the C5.a event with the H.8 alternatives. -/
structure C5abcInputs {N : ℕ} (D : ConcreteEpochData N) where
  /-- The C5.a field-pool coverage budget (a genuine L17 `PoolCoverageInputs`). -/
  pool : PoolCoverageBudget
  /-- The C5.a–c pre-extraction event. -/
  pre : D.Sample → Prop
  /-- C5.a: the field pool covers every retained prime of every used dyad. -/
  poolCovered : D.Sample → Prop
  /-- C5.a interface: the ideal-law pool-miss event is dominated by the L17
  pool-miss mass.  This identifies the ideal pool draw with the `K`-fold product
  of `pool.inputs.μ`; it is the only place where the two finite probability
  spaces are related. -/
  poolMiss_le :
    pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
      poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
        pool.inputs.AllGood pool.inputs.hit
  /-- H.8 alternative 1: the sample yields an immediate proper factor. -/
  immediateFactor : D.Sample → Prop
  /-- H.8 alternative 2: the sample yields an accepted field whose good-prime
  sets are dense in every selected band. -/
  acceptedDense : D.Sample → Prop
  /-- H.8 counting (KB p.141): at least half of the ideal mass yields an
  immediate factor or an accepted dense field.  This is the smallest explicit
  paper-level counting lemma; it is a hypothesis, not an axiom. -/
  half_mass :
    (1 / 2 : ℝ) ≤ pmfProb D.ideal (fun x => immediateFactor x ∨ acceptedDense x)
  /-- The pre-event contains the C5.a pool event together with the H.8
  alternatives. -/
  pre_of : ∀ x, poolCovered x → (immediateFactor x ∨ acceptedDense x) → pre x

namespace C5abcInputs

variable {N : ℕ} {D : ConcreteEpochData N}

/-- **C5.a coverage, with the loss notation.**  The ideal-law pool-miss mass is
at most `pool.loss`, using the L17 theorem `PoolCoverageBudget.missMass_le_loss`. -/
theorem pool_fail_le (I : C5abcInputs D) :
    pmfProb D.ideal (fun x => ¬ I.poolCovered x) ≤ I.pool.loss :=
  I.poolMiss_le.trans I.pool.missMass_le_loss

/-- **H.8 complement form.**  The mass of "neither an immediate factor nor an
accepted dense field" is at most `1 / 2`. -/
theorem half_compl_le [Fintype D.Sample] (I : C5abcInputs D) :
    pmfProb D.ideal (fun x => ¬ (I.immediateFactor x ∨ I.acceptedDense x)) ≤
      (1 / 2 : ℝ) := by
  have hcomp := pmfProb_compl_eq_one_sub D.ideal
    (fun x => I.immediateFactor x ∨ I.acceptedDense x)
  linarith only [hcomp, I.half_mass]

/-- **The `c5abc_compl_le` field, proved from C5.a and H.8.**

The complement of the pre-event is contained in the union of the C5.a pool-miss
event and the H.8 complement; the union bound charges `pool.loss` and `1 / 2`
respectively. -/
theorem compl_le [Fintype D.Sample] (I : C5abcInputs D) :
    pmfProb D.ideal (fun x => ¬ I.pre x) ≤ (1 / 2 : ℝ) + I.pool.loss := by
  have hmono : pmfProb D.ideal (fun x => ¬ I.pre x) ≤
      pmfProb D.ideal
        (fun x => ¬ I.poolCovered x ∨
          ¬ (I.immediateFactor x ∨ I.acceptedDense x)) := by
    apply pmfProb_mono
    intro x hx
    by_cases hc : I.poolCovered x
    · refine Or.inr ?_
      intro hhalf
      exact hx (I.pre_of x hc hhalf)
    · exact Or.inl hc
  have hunion := pmfProb_or_le_add D.ideal
    (fun x => ¬ I.poolCovered x)
    (fun x => ¬ (I.immediateFactor x ∨ I.acceptedDense x))
  have hcover := I.pool_fail_le
  have hhalf := I.half_compl_le
  linarith only [hmono, hunion, hcover, hhalf]

/-- The C5.a–c counting data packaged as the `HitMassInputs` field.  All other
C5 stages are passed through unchanged. -/
noncomputable def toHitMassInputs [Fintype D.Sample] (I : C5abcInputs D)
    (survivor descent algebra coupling : StageBudget D)
    (good_iff : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        I.pre x ∧ algebra.ok x ∧ coupling.ok x) :
    HitMassInputs D where
  pre := I.pre
  pool := I.pool
  survivor := survivor
  descent := descent
  algebra := algebra
  coupling := coupling
  c5abc_compl_le := I.compl_le
  good_iff := good_iff

/-- **End-to-end C5.a–c lower bound.**  The `HitMassInputs` built from
`C5abcInputs` satisfies the existing `HitMassInputs.pre_mass_lower`:
the pre-event carries mass at least `1 / 2 - (pool.loss + survivor.loss +
descent.loss)`.  This is the consumer of `compl_le` inside the C5 assembly. -/
theorem pre_mass_lower [Fintype D.Sample] (I : C5abcInputs D)
    (survivor descent algebra coupling : StageBudget D)
    (good_iff : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        I.pre x ∧ algebra.ok x ∧ coupling.ok x) :
    (1 / 2 : ℝ) - (I.pool.loss + survivor.loss + descent.loss) ≤
      pmfProb D.ideal I.pre := by
  have h := HitMassInputs.pre_mass_lower (D := D)
    ({ pre := I.pre
       pool := I.pool
       survivor := survivor
       descent := descent
       algebra := algebra
       coupling := coupling
       c5abc_compl_le := I.compl_le
       good_iff := good_iff } : HitMassInputs D)
  simpa only [HitMassInputs.preLoss] using h

/-- Constructor for the common case where `pre` is *exactly* the conjunction of
the C5.a pool event and the H.8 alternatives. -/
noncomputable def ofConjunction {N : ℕ} {D : ConcreteEpochData N}
    (pool : PoolCoverageBudget)
    (poolCovered immediateFactor acceptedDense : D.Sample → Prop)
    (poolMiss_le :
      pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
        poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
          pool.inputs.AllGood pool.inputs.hit)
    (half_mass :
      (1 / 2 : ℝ) ≤
        pmfProb D.ideal (fun x => immediateFactor x ∨ acceptedDense x)) :
    C5abcInputs D where
  pool := pool
  pre := fun x => poolCovered x ∧ (immediateFactor x ∨ acceptedDense x)
  poolCovered := poolCovered
  poolMiss_le := poolMiss_le
  immediateFactor := immediateFactor
  acceptedDense := acceptedDense
  half_mass := half_mass
  pre_of := fun _ hc hhalf => ⟨hc, hhalf⟩

end C5abcInputs

/-! ## Axiom audit -/

#print axioms C5abcInputs.pool_fail_le
#print axioms C5abcInputs.half_compl_le
#print axioms C5abcInputs.compl_le
#print axioms C5abcInputs.pre_mass_lower
#print axioms C5abcInputs.toHitMassInputs
#print axioms C5abcInputs.ofConjunction

end Cogentic.RandomizedConcreteHitMassCount
