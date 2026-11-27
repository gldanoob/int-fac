import Cogentic.RandomizedC5HalfMass
import Cogentic.RandomizedC5Algebra
import Cogentic.RandomizedC5Coupling

/-!
# C5 `hitMass` full certificate

`Cogentic.RandomizedConcreteHitMass.HitMassInputs` decomposes the C5 bridge into
five slots:

```
pool       -- C5.a, L17 field-pool coverage
survivor   -- C5.b, L20.1 bad-child recurrence
descent    -- C5.c, L28 descent tree
algebra    -- C5.d, L33–L37, opaque `StageBudget`
coupling   -- C5.e, L39, opaque `StageBudget`
```

Wave 7 replaces the two opaque `StageBudget` slots by their decompositions:

* `Cogentic.RandomizedC5Algebra.C5AlgebraInputs` splits C5.d into the four
  sub-stages L34–L37 and proves `C5AlgebraInputs.stageBudget`, whose loss is the
  explicit sum `chebotarevLoss + oddDegreeLoss + valuationLoss + henselLoss`.
* `Cogentic.RandomizedC5Coupling.CouplingInputs` splits C5.e into the adaptive
  first-error union bound and the public-trace input P1–P4, and proves
  `CouplingInputs.stageBudget`, whose loss is `callCap * delta`.
* `Cogentic.RandomizedConcreteHitMassCount.C5abcInputs` proves the C5.a–c
  `c5abc_compl_le` field from the pool coverage and the H.8 half-mass count.
* `Cogentic.RandomizedC5HalfMass.HalfMassInputs` proves that half-mass count from
  the finite counting statement `#Sample ≤ 2 * #successes` under the uniform
  ideal law.

This file composes them into one `C5FullInputs` bundle and one `HitMassInputs`
value whose `algebra` and `coupling` stages are literally
`C5AlgebraInputs.stageBudget` and `CouplingInputs.stageBudget`.  The assembled
loss is the explicit sum

```
pool.loss + survivor.loss + descent.loss
  + algebra.totalLoss + coupling.loss
```

with no slot set to zero: `algebra.totalLoss` is the sum of the four L34–L37
losses and `coupling.loss` is the positive `callCap * delta` of the recognizer
coupling.

The event identification is kept as the explicit field `good_iff`: the concrete
good-transcript set is exactly the conjunction of the C5.a–c pre-event, the
decomposed C5.d algebra event, and the decomposed C5.e coupling event.  From it
we prove `hitMass_of_inputs`, `goodMass_lower`, and the assembled-attempt bound
`assembledAttempt_hit_prob_ge`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace Cogentic.RandomizedC5Full

open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedConcreteHitMassCount
open Cogentic.RandomizedC5HalfMass
open Cogentic.RandomizedC5Algebra
open Cogentic.RandomizedC5Coupling
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochPool
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedPoolCoverage

/-! ## Section 1: The full C5 bundle -/

/-- **Full C5 inputs.**  All four decomposed ingredient families in one place:

* `abc` is the C5.a–c counting reduction (`C5abcInputs`), which already contains
  the C5.a `PoolCoverageBudget` and the proved `c5abc_compl_le` field;
* `survivor` and `descent` are the C5.b/C5.c recurrence budgets;
* `algebra` is the C5.d decomposition into L34–L37;
* `coupling` is the C5.e decomposition into the adaptive first-error bound and
  the public-trace recognizer inputs;
* `good_iff` identifies the concrete good-transcript set with the conjunction of
  the pre-event, the decomposed algebra event, and the decomposed coupling event.
-/
structure C5FullInputs {N : ℕ} (D : ConcreteEpochData N) [Fintype D.Sample] where
  /-- C5.a–c: pool coverage plus the H.8 half-mass count. -/
  abc : C5abcInputs D
  /-- C5.b: the L20.1 survivor/bad-child recurrence budget. -/
  survivor : StageBudget D
  /-- C5.c: the L28 descent-tree budget. -/
  descent : StageBudget D
  /-- C5.d: the L34–L37 algebra decomposition. -/
  algebra : C5AlgebraInputs D
  /-- C5.e: the L39 recognizer-coupling decomposition. -/
  coupling : CouplingInputs D
  /-- Event identification: the concrete good set is exactly
  `pre ∧ algebra.ok ∧ coupling.ok`. -/
  good_iff : ∀ x,
    (observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) ↔
      abc.pre x ∧ algebra.stageBudget.ok x ∧ coupling.stageBudget.ok x

namespace C5FullInputs

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]

/-- **The assembled `HitMassInputs`.**  The C5.d and C5.e slots are the
decomposed stage budgets of `C5AlgebraInputs` and `CouplingInputs`; the C5.a–c
slot is the proved `C5abcInputs.compl_le`. -/
noncomputable def toHitMassInputs (I : C5FullInputs D) : HitMassInputs D where
  pre := I.abc.pre
  pool := I.abc.pool
  survivor := I.survivor
  descent := I.descent
  algebra := I.algebra.stageBudget
  coupling := I.coupling.stageBudget
  c5abc_compl_le := I.abc.compl_le
  good_iff := I.good_iff

/-- The C5.d slot of the assembled bundle is the L34–L37 stage budget. -/
theorem toHitMassInputs_algebra (I : C5FullInputs D) :
    I.toHitMassInputs.algebra = I.algebra.stageBudget := rfl

/-- The C5.e slot of the assembled bundle is the L39 stage budget. -/
theorem toHitMassInputs_coupling (I : C5FullInputs D) :
    I.toHitMassInputs.coupling = I.coupling.stageBudget := rfl

/-- The total loss of the full certificate, written out as the explicit sum of
the five slots and the two decompositions. -/
noncomputable def totalLoss (I : C5FullInputs D) : ℝ :=
  I.abc.pool.loss + I.survivor.loss + I.descent.loss +
    I.algebra.totalLoss + I.coupling.loss

/-- The assembled `HitMassInputs` charges exactly the explicit full loss. -/
theorem toHitMassInputs_totalLoss (I : C5FullInputs D) :
    I.toHitMassInputs.totalLoss = I.totalLoss := rfl

/-- The full loss is nonnegative: every slot carries a nonnegative budget and the
two decomposed stages are sums/products of nonnegative losses. -/
theorem totalLoss_nonneg (I : C5FullInputs D) : 0 ≤ I.totalLoss := by
  unfold totalLoss
  have hp : 0 ≤ I.abc.pool.loss := I.abc.pool.loss_nonneg
  have hs : 0 ≤ I.survivor.loss := I.survivor.loss_nonneg
  have hd : 0 ≤ I.descent.loss := I.descent.loss_nonneg
  have ha : 0 ≤ I.algebra.totalLoss := I.algebra.totalLoss_nonneg
  have hc : 0 ≤ I.coupling.loss := I.coupling.loss_nonneg
  linarith only [hp, hs, hd, ha, hc]

/-- **C5.a–c pre-event mass.**  `1/2 - (pool + survivor + descent) ≤ P(pre)`,
the existing `C5abcInputs.pre_mass_lower` at the decomposed stage budgets. -/
theorem pre_mass_lower (I : C5FullInputs D) :
    (1 / 2 : ℝ) -
        (I.abc.pool.loss + I.survivor.loss + I.descent.loss) ≤
      pmfProb D.ideal I.abc.pre :=
  I.abc.pre_mass_lower I.survivor I.descent I.algebra.stageBudget
    I.coupling.stageBudget I.good_iff

/-- **C5.d/e post-event failure.**  On the pre-event, the decomposed algebra and
coupling stages fail with mass at most `algebra.totalLoss + coupling.loss`. -/
theorem post_fail_le (I : C5FullInputs D) :
    pmfProb D.ideal
        (fun x => I.abc.pre x ∧
          ¬ ((I.algebra.stageBudget).ok x ∧ (I.coupling.stageBudget).ok x)) ≤
      I.algebra.totalLoss + I.coupling.loss := by
  have h := I.toHitMassInputs.post_fail_le
  simpa only [toHitMassInputs, C5AlgebraInputs.stageBudget,
    CouplingInputs.stageBudget] using h

/-- **Good-transcript mass.**  The ideal good-transcript mass is at least `1/4`
minus the explicit full loss. -/
theorem goodMass_lower (I : C5FullInputs D) :
    (1 / 4 : ℝ) - I.totalLoss ≤
      pmfProb D.ideal
        (fun x => observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) := by
  simpa only [toHitMassInputs_totalLoss] using I.toHitMassInputs.goodMass_lower

/-- **The `hitMass` bridge.**  The exact field type consumed by
`Cogentic.RandomizedEpochAnalyticInputs.C5Inputs`, at the explicit full loss. -/
theorem hitMass_of_inputs (I : C5FullInputs D) :
    (1 / 4 : ℝ) - I.totalLoss ≤
      ((D.toHardEpochData.ideal).toOuterMeasure
        {x | observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good}).toReal := by
  simpa only [toHitMassInputs_totalLoss] using I.toHitMassInputs.hitMass_of_inputs

/-- **Assembled-attempt bound.**  If the full loss leaves room inside `1/4`, the
actual assembled epoch attempt hits with probability at least
`(1/4 - totalLoss) / 2 - ε`, where `ε` is the ideal/actual TV error.  The C5.d/e
losses sit inside the `γ` bracket; the TV error appears exactly once. -/
theorem assembledAttempt_hit_prob_ge (I : C5FullInputs D)
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hcheck : D.toHardEpochData.CongruenceCheck)
    (huniform : D.toHardEpochData.HiddenUniform)
    (hbudget : I.totalLoss ≤ 1 / 4)
    {ε : ℝ}
    (hTV : pmfTotalVariation D.toHardEpochData.ideal D.toHardEpochData.actual ≤ ε) :
    ((1 / 4 : ℝ) - I.totalLoss) / 2 - ε ≤
      ((D.toHardEpochData.actual.map (D.toHardEpochData.assembledAttempt hN)).toOuterMeasure
        {o | o.1 ≠ none}).toReal := by
  have hbudget' : I.toHitMassInputs.totalLoss ≤ 1 / 4 := by
    rwa [toHitMassInputs_totalLoss]
  have h := assembledAttempt_hit_prob_ge_of_inputs D I.toHitMassInputs hN ho hnot
    hcheck huniform hbudget' hTV
  simpa only [toHitMassInputs_totalLoss] using h

/-! ### Paper-literal C5.e form

The coupling loss is the positive `callCap * delta` and is at most `1/1024`.
Replacing it by `1/1024` gives the paper's literal L39 quota while keeping the
other four slots exact. -/

/-- **Good-transcript mass with the paper's L39 quota.**  C5.e is charged its
literal `1/1024` bound instead of `callCap * delta`. -/
theorem goodMass_lower_inv1024 (I : C5FullInputs D) :
    (1 / 4 : ℝ) -
        (I.abc.pool.loss + I.survivor.loss + I.descent.loss +
          I.algebra.totalLoss + 1 / 1024) ≤
      pmfProb D.ideal
        (fun x => observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) := by
  have h := I.goodMass_lower
  have hc : I.coupling.loss ≤ 1 / 1024 := I.coupling.loss_le_inv1024
  unfold totalLoss at h
  linarith only [h, hc]

/-- **Assembled-attempt bound with the paper's L39 quota.** -/
theorem assembledAttempt_hit_prob_ge_inv1024 (I : C5FullInputs D)
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hcheck : D.toHardEpochData.CongruenceCheck)
    (huniform : D.toHardEpochData.HiddenUniform)
    (hbudget : I.abc.pool.loss + I.survivor.loss + I.descent.loss +
      I.algebra.totalLoss + 1 / 1024 ≤ 1 / 4)
    {ε : ℝ}
    (hTV : pmfTotalVariation D.toHardEpochData.ideal D.toHardEpochData.actual ≤ ε) :
    ((1 / 4 : ℝ) -
        (I.abc.pool.loss + I.survivor.loss + I.descent.loss +
          I.algebra.totalLoss + 1 / 1024)) / 2 - ε ≤
      ((D.toHardEpochData.actual.map (D.toHardEpochData.assembledAttempt hN)).toOuterMeasure
        {o | o.1 ≠ none}).toReal := by
  have hbudget_full : I.totalLoss ≤ 1 / 4 := by
    unfold totalLoss
    have hc : I.coupling.loss ≤ 1 / 1024 := I.coupling.loss_le_inv1024
    linarith only [hbudget, hc]
  have h := I.assembledAttempt_hit_prob_ge hN ho hnot hcheck huniform
    hbudget_full hTV
  have hloss : I.totalLoss ≤ I.abc.pool.loss + I.survivor.loss +
      I.descent.loss + I.algebra.totalLoss + 1 / 1024 := by
    unfold totalLoss
    have hc : I.coupling.loss ≤ 1 / 1024 := I.coupling.loss_le_inv1024
    linarith only [hc]
  have hmono : ((1 / 4 : ℝ) -
        (I.abc.pool.loss + I.survivor.loss + I.descent.loss +
          I.algebra.totalLoss + 1 / 1024)) / 2 - ε ≤
      ((1 / 4 : ℝ) - I.totalLoss) / 2 - ε := by
    linarith only [hloss]
  exact hmono.trans h

end C5FullInputs

/-! ## Section 2: Constructors from `C5abcInputs` / `HalfMassInputs` -/

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]

/-- **Full C5 inputs from the C5.a–c counting bundle.**  The pool, pre-event and
H.8 half-mass data are passed through the proved `C5abcInputs`. -/
noncomputable def C5FullInputs.ofC5abc (abc : C5abcInputs D)
    (survivor descent : StageBudget D)
    (algebra : C5AlgebraInputs D) (coupling : CouplingInputs D)
    (good_iff : ∀ x,
      (observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) ↔
        abc.pre x ∧ algebra.stageBudget.ok x ∧ coupling.stageBudget.ok x) :
    C5FullInputs D where
  abc := abc
  survivor := survivor
  descent := descent
  algebra := algebra
  coupling := coupling
  good_iff := good_iff

/-- **Full C5 inputs from the H.8 half-mass count.**  `HalfMassInputs` proves the
C5.a/H.8 half mass from `#Sample ≤ 2 * #successes`; `HalfMassInputs.toC5abcInputs`
then produces the C5.a–c bundle. -/
noncomputable def C5FullInputs.ofHalfMass (H : HalfMassInputs D)
    (pool : PoolCoverageBudget.{0, 0, 0})
    (pre poolCovered : D.Sample → Prop)
    (poolMiss_le :
      pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
        poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
          pool.inputs.AllGood pool.inputs.hit)
    (pre_of : ∀ x, poolCovered x →
      (H.immediateFactor x ∨ H.acceptedDense x) → pre x)
    (survivor descent : StageBudget D)
    (algebra : C5AlgebraInputs D) (coupling : CouplingInputs D)
    (good_iff : ∀ x,
      (observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) ↔
        pre x ∧ algebra.stageBudget.ok x ∧ coupling.stageBudget.ok x) :
    C5FullInputs D :=
  C5FullInputs.ofC5abc (H.toC5abcInputs pool pre poolCovered poolMiss_le pre_of)
    survivor descent algebra coupling good_iff

/-- The half-mass constructor keeps the pre-event and stage budgets unchanged;
only the counting half-mass field is supplied by `HalfMassInputs.half_mass`. -/
theorem C5FullInputs.ofHalfMass_abc_pre (H : HalfMassInputs D)
    (pool : PoolCoverageBudget.{0, 0, 0})
    (pre poolCovered : D.Sample → Prop)
    (poolMiss_le :
      pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
        poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
          pool.inputs.AllGood pool.inputs.hit)
    (pre_of : ∀ x, poolCovered x →
      (H.immediateFactor x ∨ H.acceptedDense x) → pre x)
    (survivor descent : StageBudget D)
    (algebra : C5AlgebraInputs D) (coupling : CouplingInputs D)
    (good_iff : ∀ x,
      (observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) ↔
        pre x ∧ algebra.stageBudget.ok x ∧ coupling.stageBudget.ok x) :
    (C5FullInputs.ofHalfMass H pool pre poolCovered poolMiss_le pre_of
      survivor descent algebra coupling good_iff).abc.pre = pre := rfl

/-! ## Axiom audit -/

#print axioms C5FullInputs.toHitMassInputs
#print axioms C5FullInputs.toHitMassInputs_algebra
#print axioms C5FullInputs.toHitMassInputs_coupling
#print axioms C5FullInputs.toHitMassInputs_totalLoss
#print axioms C5FullInputs.totalLoss_nonneg
#print axioms C5FullInputs.pre_mass_lower
#print axioms C5FullInputs.post_fail_le
#print axioms C5FullInputs.goodMass_lower
#print axioms C5FullInputs.hitMass_of_inputs
#print axioms C5FullInputs.assembledAttempt_hit_prob_ge
#print axioms C5FullInputs.goodMass_lower_inv1024
#print axioms C5FullInputs.assembledAttempt_hit_prob_ge_inv1024
#print axioms C5FullInputs.ofC5abc
#print axioms C5FullInputs.ofHalfMass
#print axioms C5FullInputs.ofHalfMass_abc_pre

end Cogentic.RandomizedC5Full
