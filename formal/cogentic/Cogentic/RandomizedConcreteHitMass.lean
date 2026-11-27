import Cogentic.RandomizedEpochPool
import Cogentic.RandomizedEpochAlgebra
import Cogentic.RandomizedConcreteEpoch
import Cogentic.RandomizedPaperLeafStatements

/-!
# Concrete C5 `hitMass` bridge: decomposition into the paper's C5.a–e pieces

`Cogentic.RandomizedEpochAnalyticInputs.C5Inputs.hitMass` is the one C5 ingredient
that is not one of the twelve manuscript leaves: the claim that the ideal law of
the concrete epoch puts mass at least `1/4 - (total C5 loss)` on good transcripts
(blueprint §2, C5, and KeyBreak Proposition H.8 p.141).  This file decomposes that
bridge into the paper's C5.a–e pieces and proves the numerical assembly.

The formal skeleton is

```
1/4 - totalLoss  ≤  ideal good-mass
```

where

* `totalLoss = preLoss + algebra.loss + coupling.loss`,
* `preLoss  = pool.loss + survivor.loss + descent.loss`.

The pieces map onto the blueprint as follows.

* **C5.a (L17) field-pool coverage.**  `PoolCoverageBudget` carries a genuine
  `RandomizedEpochPool.PoolCoverageInputs`; its numerical loss
  `PoolCoverageBudget.loss` is the right-hand side of
  `PoolCoverageInputs.missMass_le_trimmed_exp`, and
  `PoolCoverageBudget.missMass_le_loss` / `PoolCoverageBudget.coverage` are
  proved from that theorem.  So the C5.a budget is not restated: it is the
  existing coverage estimate specialised to its loss.
* **C5.a/C5.b (L18–L20) survivor/bad-child recurrence.**  `survivor` is a
  `StageBudget` produced by `stageBudget_of_survivorRecurrence`, whose numerical
  bound is `RandomizedFieldPoolDescent.top_sqrt_of_internal_linear_bound`
  (the G.11–G.12 recurrence of L20.1).  The only non-recurrence input is the
  explicit mass identification `pmfProb ≤ δ_top` (paper: the bad-child mass is
  itself a probability); it is a hypothesis of the constructor, not an axiom.
* **C5.c (L28) descent.**  `descent` is a `StageBudget` produced by
  `stageBudget_of_descentTree`, whose numerical bound is
  `RandomizedFieldPoolDescent.pmf_descentTree_elliptic_fail_le_exp`
  (the H.4 bounded-search / `3/4` recognition transfer over an `L`-level tree).
* **C5.d (L33–L37) algebra.**  `algebra` is an explicit `StageBudget` field.
  Its `fail_le` is the genuinely paper-level statement: mask existence (L33),
  character separation (L34, effective Chebotarev), odd-degree square-norm
  algebra (L35), even valuations (L36), and Hensel root evaluation (L37).
* **C5.e (L39) recognizer coupling.**  `coupling` is an explicit `StageBudget`
  field whose `fail_le` is the adaptive first-error / recognizer-coupling bound.
* **The `1/2` in C5.a–c.**  The field `c5abc_compl_le` records the H.8 counting
  statement that, outside the C5.a–c losses, the complement of the pre-event has
  mass at most `1/2` ("probability at least `1/2` of either an immediate factor
  or an accepted field having the dense good-prime sets in every selected band",
  KB p.141).  The `1/4 = 1/2 · 1/2` in H.8 then follows because the final hidden
  sign contributes the extra `1/2` in `RandomizedEpochAlgebra.hit_prob_ge`; that
  downstream step is also formalised here
  (`assembledAttempt_hit_prob_ge_of_inputs`).

Nothing is set to `1/4` by fiat: the `1/4` is produced by the proved arithmetic
`1/4 ≤ 1/2` after the paper-level `1/2` counting field and the proven stage
losses have been subtracted.  There is no `sorry`, `admit`, `axiom`, or
`native_decide`, and the paper-level C5.d/C5.e statements are explicit `Prop`
fields, never axioms.

The final theorem `toC5Inputs_of_hitMassInputs` plugs the per-epoch reduction into
`RandomizedPaperLeafStatements.PaperAnalyticAssumptions.toC5Inputs`, so the wave-2
paper endpoint can consume the concrete C5.a–e data in place of a bare `hitMass`
hypothesis.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace Cogentic.RandomizedConcreteHitMass

open Cogentic.RandomizedPoolCoverage
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedEpochPool
open Cogentic.RandomizedEpochAlgebra
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedHiddenOutputLaw

/-! ## Section 1: Finite-PMF probability bookkeeping

The C5 assembly is a union-bound argument.  The lemmas below are the only
probability facts used; all are proved from `pmfProb`'s definition as a finite
sum. -/

section PMFHelpers

variable {Ω : Type*} [Fintype Ω]

/-- `pmfProb` as a sum of point masses with an indicator. -/
theorem pmfProb_eq_sum_ite (μ : PMF Ω) (E : Ω → Prop) [DecidablePred E] :
    pmfProb μ E = ∑ ω : Ω, if E ω then pmfWeight μ ω else 0 := by
  classical
  rw [pmfProb_eq_sum_filter, Finset.sum_filter]

/-- Complementary events have probabilities summing to one. -/
theorem pmfProb_add_compl (μ : PMF Ω) (E : Ω → Prop) :
    pmfProb μ E + pmfProb μ (fun x => ¬ E x) = 1 := by
  classical
  rw [pmfProb_eq_sum_ite, pmfProb_eq_sum_ite, ← Finset.sum_add_distrib,
    ← pmfWeight_sum_eq_one μ]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x <;> simp [h]

/-- Probability of a complement. -/
theorem pmfProb_compl_eq_one_sub (μ : PMF Ω) (E : Ω → Prop) :
    pmfProb μ (fun x => ¬ E x) = 1 - pmfProb μ E := by
  have h := pmfProb_add_compl μ E
  linarith only [h]

/-- Two-event union bound. -/
theorem pmfProb_or_le_add (μ : PMF Ω) (A B : Ω → Prop) :
    pmfProb μ (fun x => A x ∨ B x) ≤ pmfProb μ A + pmfProb μ B := by
  classical
  rw [pmfProb_eq_sum_ite, pmfProb_eq_sum_ite, pmfProb_eq_sum_ite,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hw := pmfWeight_nonneg μ x
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb] <;> linarith

/-- Pointwise equivalence of events gives equal probabilities. -/
theorem pmfProb_congr (μ : PMF Ω) {E F : Ω → Prop} (h : ∀ x, E x ↔ F x) :
    pmfProb μ E = pmfProb μ F := by
  have hset : {x | E x} = {x | F x} := Set.ext h
  unfold pmfProb
  rw [hset]

/-- Removing the part of `A` where `B` holds: `P(A) - P(A ∧ ¬B) ≤ P(A ∧ B)`.
This is the C5.d/e step: on the pre-event, the only way to fail `B` is the
post-event failure set. -/
theorem pmfProb_sub_and_not_le (μ : PMF Ω) (A B : Ω → Prop) :
    pmfProb μ A - pmfProb μ (fun x => A x ∧ ¬ B x) ≤
      pmfProb μ (fun x => A x ∧ B x) := by
  have hsplit : pmfProb μ A ≤
      pmfProb μ (fun x => A x ∧ B x) +
        pmfProb μ (fun x => A x ∧ ¬ B x) := by
    refine (pmfProb_mono μ ?_).trans (pmfProb_or_le_add μ _ _)
    intro x hx
    by_cases hb : B x
    · exact Or.inl ⟨hx, hb⟩
    · exact Or.inr ⟨hx, hb⟩
  linarith only [hsplit]

end PMFHelpers

/-! ## Section 2: C5.a — the L17 field-pool coverage budget -/

/-- C5.a's field-pool coverage, packaged with its numerical loss.

The payload is a `RandomizedEpochPool.PoolCoverageInputs`; nothing about the
coverage estimate is assumed.  The loss is exactly the right-hand side of
`PoolCoverageInputs.missMass_le_trimmed_exp`, so the C5.a budget is the existing
L17 theorem applied at its canonical constants
`q = a^2 / (16 M)` and `θ_bad = a^3 / (64 M)`. -/
structure PoolCoverageBudget where
  /-- The finite probability space of one field-pool draw. -/
  Ω : Type*
  [fintypeΩ : Fintype Ω]
  /-- The set of used dyads. -/
  ι : Type*
  /-- The prime type. -/
  P : Type*
  [decEqP : DecidableEq P]
  /-- The L17 coverage inputs. -/
  inputs : PoolCoverageInputs Ω ι P

attribute [instance] PoolCoverageBudget.fintypeΩ PoolCoverageBudget.decEqP

namespace PoolCoverageBudget

/-- The C5.a loss: the trimmed-dyad exponential pool-miss bound of L17. -/
noncomputable def loss (B : PoolCoverageBudget) : ℝ :=
  letI := B.fintypeΩ
  letI := B.decEqP
  (∑ d ∈ B.inputs.dyads, ((B.inputs.Good d).card : ℝ)) *
    Real.exp (-(B.inputs.a ^ 2 / (16 * B.inputs.M)) * (B.inputs.K : ℝ))

theorem loss_nonneg (B : PoolCoverageBudget) : 0 ≤ B.loss := by
  unfold loss
  exact mul_nonneg (Finset.sum_nonneg fun d _ => Nat.cast_nonneg _)
    (Real.exp_pos _).le

/-- The L17 coverage estimate with the loss notation: the pool misses a retained
prime with probability at most `loss`.  This is
`PoolCoverageInputs.missMass_le_trimmed_exp`. -/
theorem missMass_le_loss (B : PoolCoverageBudget) :
    poolMissMass (pmfWeight B.inputs.μ) B.inputs.K B.inputs.AllGood B.inputs.hit ≤
      B.loss :=
  B.inputs.missMass_le_trimmed_exp

/-- Full C5.a coverage package with the loss notation: trimmed fraction bound and
pool-miss bound. -/
theorem coverage (B : PoolCoverageBudget) :
    (∀ d ∈ B.inputs.dyads,
        ((B.inputs.Bad d).card : ℝ) ≤
          (B.inputs.δ_rat / B.inputs.θ_rat + B.inputs.δ_bad / B.inputs.θ_bad) *
            ((B.inputs.dyad d).card : ℝ)) ∧
      poolMissMass (pmfWeight B.inputs.μ) B.inputs.K B.inputs.AllGood B.inputs.hit ≤
        B.loss := by
  refine ⟨B.inputs.bad_card_le, ?_⟩
  exact B.missMass_le_loss

end PoolCoverageBudget

/-! ## Section 3: Stage budgets, and the C5.b/c recurrence and descent constructions -/

/-- A stage failure budget for the concrete epoch: an event `ok` on `D.Sample`
that fails with ideal probability at most `loss`.

The field `fail_le` is where a paper-level C5 step is recorded, when the step is
not derivable from an existing theorem.  For the C5.b/C5.c recurrence and descent
stages and for C5.a, the budgets are instead *constructed*, so their `fail_le`
fields are proofs. -/
structure StageBudget {N : ℕ} (D : ConcreteEpochData N) where
  /-- The stage-success event. -/
  ok : D.Sample → Prop
  /-- The ideal-probability loss charged by this stage. -/
  loss : ℝ
  /-- The loss is nonnegative. -/
  loss_nonneg : 0 ≤ loss
  /-- The stage fails on at most the stated ideal mass. -/
  fail_le : pmfProb D.ideal (fun x => ¬ ok x) ≤ loss

/-! ### C5.b/C5.c: the G.11–G.12 survivor recurrence (L20.1) -/

/-- The numerical top bad-child bound produced by the L20.1 recurrence. -/
noncomputable def survivorLoss (C_top C_step η ε_rat ε_in : ℝ) (δ_int : ℕ → ℝ)
    (L : ℕ) : ℝ :=
  C_top *
    (Real.sqrt (C_step ^ L * (δ_int L + (L : ℝ) * (η + ε_rat))) +
      Real.sqrt ε_in + η)

theorem survivorLoss_nonneg {C_top C_step η ε_rat ε_in : ℝ} {δ_int : ℕ → ℝ} {L : ℕ}
    (hC_top : 0 ≤ C_top) (hη : 0 ≤ η) :
    0 ≤ survivorLoss C_top C_step η ε_rat ε_in δ_int L := by
  unfold survivorLoss
  have h1 : 0 ≤ Real.sqrt (C_step ^ L * (δ_int L + (L : ℝ) * (η + ε_rat))) :=
    Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt ε_in := Real.sqrt_nonneg _
  exact mul_nonneg hC_top (by linarith)

/-- **C5.b/C5.c survivor recurrence budget.**  The numerical bound is
`RandomizedFieldPoolDescent.top_sqrt_of_internal_linear_bound` (G.12 on top of the
G.11 linear internal recurrence, blueprint L20.1).  The hypothesis `hmass`
identifies the bad-child mass `δ_top` with the ideal failure probability of the
stage; in the paper this is the definition of `δ_top`, and it is the only
non-recurrence input. -/
noncomputable def stageBudget_of_survivorRecurrence {N : ℕ} (D : ConcreteEpochData N)
    (δ_int : ℕ → ℝ) (L : ℕ) {δ_top C_top C_step η ε_rat ε_in : ℝ}
    (hC_top : 0 ≤ C_top) (hη : 0 ≤ η) (hC_step : 1 ≤ C_step)
    (hα : 0 ≤ η + ε_rat)
    (hrec : ∀ i < L, δ_int i ≤ C_step * (δ_int (i + 1) + η + ε_rat))
    (htop : δ_top ≤ C_top * (Real.sqrt (δ_int 0) + Real.sqrt ε_in + η))
    (fail : D.Sample → Prop)
    (hmass : pmfProb D.ideal fail ≤ δ_top) :
    StageBudget D where
  ok := fun x => ¬ fail x
  loss := survivorLoss C_top C_step η ε_rat ε_in δ_int L
  loss_nonneg := survivorLoss_nonneg hC_top hη
  fail_le := by
    have h := top_sqrt_of_internal_linear_bound δ_int L hC_top hC_step hα hrec htop
    simpa only [survivorLoss, not_not] using hmass.trans h

/-! ### C5.c: the H.4 descent-tree failure bound (L28) -/

/-- The numerical H.4 descent-tree failure bound. -/
noncomputable def descentLoss (b L T : ℕ) (p_ver c U : ℝ) : ℝ :=
  2 * (b : ℝ) ^ L * Real.exp (-((3 * c / (4 * U)) * p_ver) * (T : ℝ))

theorem descentLoss_nonneg (b L T : ℕ) (p_ver c U : ℝ) :
    0 ≤ descentLoss b L T p_ver c U := by
  unfold descentLoss
  exact mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg b) L))
    (Real.exp_pos _).le

/-- **C5.c descent budget.**  The numerical bound is
`RandomizedFieldPoolDescent.pmf_descentTree_elliptic_fail_le_exp`: the union bound
over the nodes of a depth-`L`, degree-`b` descent tree with the `3/4` elliptic
recognition factor and survivor fraction `c / U` (blueprint L28, KB Lemma H.4). -/
noncomputable def stageBudget_of_descentTree {N : ℕ} (D : ConcreteEpochData N)
    [Fintype D.Sample]
    {Node : Type*} [DecidableEq Node] (t : DescentTree Node)
    {b L T : ℕ} {p_ver c U : ℝ}
    (hb : 2 ≤ b) (ht : t.Bounded b L)
    (hp : (3 * c / (4 * U)) * p_ver ≤ 1)
    (Fail : Node → D.Sample → Prop)
    (hnode : ∀ v ∈ t.nodes,
      pmfProb D.ideal (Fail v) ≤ (1 - (3 * c / (4 * U)) * p_ver) ^ T) :
    StageBudget D where
  ok := fun x => ¬ ∃ v ∈ t.nodes, Fail v x
  loss := descentLoss b L T p_ver c U
  loss_nonneg := descentLoss_nonneg b L T p_ver c U
  fail_le := by
    have h := pmf_descentTree_elliptic_fail_le_exp D.ideal t hb ht hp Fail hnode
    simpa only [descentLoss, not_not] using h

/-! ## Section 4: The C5.a–e input bundle -/

/-- **C5 hit-mass inputs for a concrete epoch.**

`pre` is the C5.a–c pre-extraction event (field pool covered, accepted field, rows
and their descendant bookkeeping); `algebra` and `coupling` are the C5.d and C5.e
post-events.  The concrete epoch's `good` set is exactly their conjunction, which
is the paper's definition of `good` in blueprint §1 (`S7` found a nonempty mask and
the `S8` check passed).

The only paper-level numerical field is `c5abc_compl_le`: the H.8 statement that,
outside the C5.a pool loss, the complement of the pre-event has mass at most `1/2`.
The C5.b/C5.c survivor recurrence loss and the C5.c descent loss are *not* added
into that field: `pre_mass_lower` removes them separately from the proved
`StageBudget.fail_le` bounds, via a three-event union bound.  C5.d and C5.e are
explicit `StageBudget` fields because they are paper-level. -/
structure HitMassInputs {N : ℕ} (D : ConcreteEpochData N) where
  /-- The C5.a–c pre-extraction event. -/
  pre : D.Sample → Prop
  /-- C5.a: the L17 field-pool coverage budget. -/
  pool : PoolCoverageBudget
  /-- C5.b/C5.c: the L20.1 survivor/bad-child recurrence budget. -/
  survivor : StageBudget D
  /-- C5.c: the L28 descent-tree budget. -/
  descent : StageBudget D
  /-- C5.d: the L33–L37 algebra budget (paper-level `fail_le`). -/
  algebra : StageBudget D
  /-- C5.e: the L39 recognizer-coupling budget (paper-level `fail_le`). -/
  coupling : StageBudget D
  /-- C5.a–c counting (KB H.8 p.141): outside the C5.a pool loss, the complement
  of the pre-event has ideal mass at most `1/2`.  This is the paper's "probability
  at least `1/2` of either an immediate factor or an accepted field having the
  dense good-prime sets in every selected band".  The C5.b/C5.c survivor and
  descent losses are removed by `pre_mass_lower` from the proved
  `StageBudget.fail_le` fields, not folded into this hypothesis. -/
  c5abc_compl_le :
    pmfProb D.ideal (fun x => ¬ pre x) ≤ (1 / 2 : ℝ) + pool.loss
  /-- Good-event definition: the concrete solver succeeds exactly on the
  conjunction of the C5.a–e stage events.  Blueprint §1 defines
  `good = {S7 found I ≠ ∅ and the S8 check passed}`; this field records that the
  same event is the conjunction of the pre-event, the C5.d algebra event, and the
  C5.e coupling event. -/
  good_iff : ∀ x,
    (observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) ↔
      pre x ∧ algebra.ok x ∧ coupling.ok x

namespace HitMassInputs

variable {N : ℕ} {D : ConcreteEpochData N}

/-- C5.a–c loss: pool coverage plus the survivor recurrence plus the descent. -/
noncomputable def preLoss (I : HitMassInputs D) : ℝ :=
  I.pool.loss + I.survivor.loss + I.descent.loss

/-- Full C5.a–e loss charged to the hit-mass bridge. -/
noncomputable def totalLoss (I : HitMassInputs D) : ℝ :=
  I.preLoss + I.algebra.loss + I.coupling.loss

theorem preLoss_nonneg (I : HitMassInputs D) : 0 ≤ I.preLoss := by
  unfold preLoss
  exact add_nonneg (add_nonneg I.pool.loss_nonneg I.survivor.loss_nonneg)
    I.descent.loss_nonneg

theorem totalLoss_nonneg (I : HitMassInputs D) : 0 ≤ I.totalLoss := by
  unfold totalLoss
  exact add_nonneg (add_nonneg I.preLoss_nonneg I.algebra.loss_nonneg)
    I.coupling.loss_nonneg

/-- C5.a–c give `1/2 - preLoss ≤ P(pre)`.  The C5.a part is the explicit
`c5abc_compl_le` field; the C5.b/C5.c survivor and descent parts are the proved
`StageBudget.fail_le` bounds, combined by a three-event union bound. -/
theorem pre_mass_lower [Fintype D.Sample] (I : HitMassInputs D) :
    (1 / 2 : ℝ) - I.preLoss ≤ pmfProb D.ideal I.pre := by
  have hmono : pmfProb D.ideal
        (fun x => ¬ (I.pre x ∧ I.survivor.ok x ∧ I.descent.ok x)) ≤
      pmfProb D.ideal
        (fun x => ¬ I.pre x ∨ ¬ I.survivor.ok x ∨ ¬ I.descent.ok x) := by
    apply pmfProb_mono
    intro x hx
    by_cases ha : I.pre x
    · by_cases hb : I.survivor.ok x
      · exact Or.inr (Or.inr (fun hc => hx ⟨ha, hb, hc⟩))
      · exact Or.inr (Or.inl hb)
    · exact Or.inl ha
  have hsplit : pmfProb D.ideal
        (fun x => ¬ I.pre x ∨ ¬ I.survivor.ok x ∨ ¬ I.descent.ok x) ≤
      pmfProb D.ideal (fun x => ¬ I.pre x) +
        pmfProb D.ideal (fun x => ¬ I.survivor.ok x ∨ ¬ I.descent.ok x) :=
    pmfProb_or_le_add D.ideal (fun x => ¬ I.pre x)
      (fun x => ¬ I.survivor.ok x ∨ ¬ I.descent.ok x)
  have htail : pmfProb D.ideal
        (fun x => ¬ I.survivor.ok x ∨ ¬ I.descent.ok x) ≤
      I.survivor.loss + I.descent.loss :=
    (pmfProb_or_le_add D.ideal (fun x => ¬ I.survivor.ok x)
      (fun x => ¬ I.descent.ok x)).trans
      (add_le_add I.survivor.fail_le I.descent.fail_le)
  have hcompl : pmfProb D.ideal
        (fun x => ¬ (I.pre x ∧ I.survivor.ok x ∧ I.descent.ok x)) ≤
      (1 / 2 : ℝ) + I.preLoss := by
    have h : pmfProb D.ideal
          (fun x => ¬ (I.pre x ∧ I.survivor.ok x ∧ I.descent.ok x)) ≤
        ((1 / 2 : ℝ) + I.pool.loss) + (I.survivor.loss + I.descent.loss) :=
      hmono.trans (hsplit.trans (add_le_add I.c5abc_compl_le htail))
    unfold preLoss
    linarith only [h]
  have hcomp := pmfProb_compl_eq_one_sub D.ideal
    (fun x => I.pre x ∧ I.survivor.ok x ∧ I.descent.ok x)
  have hE : (1 / 2 : ℝ) - I.preLoss ≤
      pmfProb D.ideal (fun x => I.pre x ∧ I.survivor.ok x ∧ I.descent.ok x) := by
    linarith only [hcomp, hcompl]
  exact hE.trans (pmfProb_mono D.ideal (fun x hx => hx.1))

/-- C5.d/e fail on the pre-event with mass at most `algebra.loss + coupling.loss`. -/
theorem post_fail_le [Fintype D.Sample] (I : HitMassInputs D) :
    pmfProb D.ideal
        (fun x => I.pre x ∧ ¬ (I.algebra.ok x ∧ I.coupling.ok x)) ≤
      I.algebra.loss + I.coupling.loss := by
  have hmono : pmfProb D.ideal
        (fun x => I.pre x ∧ ¬ (I.algebra.ok x ∧ I.coupling.ok x)) ≤
      pmfProb D.ideal (fun x => ¬ I.algebra.ok x ∨ ¬ I.coupling.ok x) := by
    apply pmfProb_mono
    intro x hx
    exact not_and_or.mp hx.2
  have hunion := pmfProb_or_le_add D.ideal
    (fun x => ¬ I.algebra.ok x) (fun x => ¬ I.coupling.ok x)
  linarith only [hmono, hunion, I.algebra.fail_le, I.coupling.fail_le]

/-- **C5 hit-mass reduction.**  The concrete epoch's ideal good-transcript mass is
at least `1/4` minus the total C5.a–e loss.

The proof is the paper's chain: C5.a–c put mass `1/2 - preLoss` on the pre-event
(`pre_mass_lower`); C5.d/e remove at most `algebra.loss + coupling.loss` on that
event (`post_fail_le`); the good event is exactly the remaining conjunction
(`good_iff`); and `1/4 ≤ 1/2`. -/
theorem goodMass_lower [Fintype D.Sample] (I : HitMassInputs D) :
    (1 / 4 : ℝ) - I.totalLoss ≤
      pmfProb D.ideal
        (fun x => observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) := by
  have hpre := I.pre_mass_lower
  have hpostfail := I.post_fail_le
  have hgood_eq : pmfProb D.ideal
        (fun x => I.pre x ∧ I.algebra.ok x ∧ I.coupling.ok x) =
      pmfProb D.ideal
        (fun x => observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) :=
    pmfProb_congr D.ideal (fun x => (I.good_iff x).symm)
  have hpost : pmfProb D.ideal I.pre - (I.algebra.loss + I.coupling.loss) ≤
      pmfProb D.ideal
        (fun x => observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good) := by
    have hsub := pmfProb_sub_and_not_le D.ideal I.pre
      (fun x => I.algebra.ok x ∧ I.coupling.ok x)
    rw [hgood_eq] at hsub
    linarith only [hsub, hpostfail]
  have hquarter : (1 / 4 : ℝ) - I.totalLoss ≤
      (1 / 2 : ℝ) - I.preLoss - (I.algebra.loss + I.coupling.loss) := by
    unfold totalLoss
    linarith
  linarith only [hpre, hpost, hquarter]

/-- The `hitMass` form of `goodMass_lower`, i.e. the exact field type consumed by
`Cogentic.RandomizedEpochAnalyticInputs.C5Inputs`. -/
theorem hitMass_of_inputs [Fintype D.Sample] (I : HitMassInputs D) :
    (1 / 4 : ℝ) - I.totalLoss ≤
      ((D.toHardEpochData.ideal).toOuterMeasure
        {x | observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good}).toReal := by
  have h := I.goodMass_lower (D := D)
  rw [ConcreteEpochData.toHardEpochData_ideal]
  exact h

end HitMassInputs

/-! ## Section 5: Feeding the C5.d/e algebra into the final split probability

This is the downstream use of `RandomizedEpochAlgebra.hit_prob_ge`: once the ideal
good mass is at least `γ`, the actual assembled attempt succeeds with probability
at least `γ / 2 - ε`.  Here `γ = 1/4 - totalLoss`, so the extra `1/2` of the paper
is the hidden-sign factor of C5.d/L38. -/

/-- **C5 → final split probability.**  The concrete C5.a–e data plus the C1/C2
checks and the ideal/actual TV bound give the assembled-attempt hit probability
`(1/4 - totalLoss) / 2 - ε`. -/
theorem assembledAttempt_hit_prob_ge_of_inputs {N : ℕ} (D : ConcreteEpochData N)
    [Fintype D.Sample] (I : HitMassInputs D) (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hcheck : D.toHardEpochData.CongruenceCheck)
    (huniform : D.toHardEpochData.HiddenUniform)
    {ε : ℝ} (hloss : I.totalLoss ≤ 1 / 4)
    (hTV : pmfTotalVariation D.toHardEpochData.ideal D.toHardEpochData.actual ≤ ε) :
    ((1 / 4 : ℝ) - I.totalLoss) / 2 - ε ≤
      ((D.toHardEpochData.actual.map (D.toHardEpochData.assembledAttempt hN)).toOuterMeasure
        {o | o.1 ≠ none}).toReal := by
  have hγ₀ : 0 ≤ (1 / 4 : ℝ) - I.totalLoss := by linarith
  exact hit_prob_ge D.toHardEpochData hN ho hnot hcheck huniform
    { gamma := (1 / 4 : ℝ) - I.totalLoss
      epsilon := ε
      gamma_nonneg := hγ₀
      gamma_le_goodMass := I.hitMass_of_inputs
      tv_le := hTV }

/-! ## Section 6: The per-family `hitMass` bridge -/

/-- The epoch family packaged from concrete S0–S9 epochs. -/
noncomputable def concreteFamily (D : ∀ n, 3 ≤ n → ConcreteEpochData n) :
    ∀ n, 3 ≤ n → HardEpochData n :=
  fun n hN => (D n hN).toHardEpochData

/-- Family-level `hitMass` bridge: if each concrete epoch carries C5.a–e data whose
total loss is at most a loss sequence `loss`, then the ideal good mass is at least
`1/4 - loss` on every hard input. -/
theorem hitMass_of_concreteInputs
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (I : ∀ n (hN : 3 ≤ n), HitMassInputs (D n hN))
    (loss : ℕ → ℝ)
    (hloss : ∀ n (hN : 3 ≤ n), (I n hN).totalLoss ≤ loss n) :
    ∀ n (hN : 3 ≤ n), HardInput n →
      (1 / 4 : ℝ) - loss n ≤
        (((concreteFamily D n hN).ideal).toOuterMeasure
          {x | observe (concreteFamily D n hN).trace x ∈
            (concreteFamily D n hN).good}).toReal := by
  intro n hN _
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fintype ((D n hN).Sample) := inferInstance
  have h := HitMassInputs.hitMass_of_inputs (I n hN)
  have hle : (1 / 4 : ℝ) - loss n ≤ (1 / 4 : ℝ) - (I n hN).totalLoss := by
    linarith only [hloss n hN]
  refine hle.trans ?_
  dsimp only [concreteFamily]
  rw [ConcreteEpochData.toHardEpochData_ideal]
  exact h

/-- **Concrete C5 replaces the bare `hitMass` hypothesis.**  The twelve paper leaves
(`PaperAnalyticAssumptions`) plus the per-epoch C5.a–e data
(`HitMassInputs`) with `totalLoss ≤ slots.total` give the `C5Inputs` ledger,
including its `hitMass` field. -/
noncomputable def toC5Inputs_of_hitMassInputs
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n) {C : ℝ}
    (P : PaperAnalyticAssumptions (concreteFamily D) C)
    (I : ∀ n (hN : 3 ≤ n), HitMassInputs (D n hN))
    (hloss : ∀ n (hN : 3 ≤ n), (I n hN).totalLoss ≤ P.slots.total n) :
    C5Inputs (concreteFamily D) :=
  P.toC5Inputs (fun n hN hhard =>
    hitMass_of_concreteInputs D I P.slots.total hloss n hN hhard)

/-! ## Axiom audit -/

#print axioms pmfProb_add_compl
#print axioms pmfProb_compl_eq_one_sub
#print axioms pmfProb_or_le_add
#print axioms pmfProb_sub_and_not_le
#print axioms PoolCoverageBudget.loss_nonneg
#print axioms PoolCoverageBudget.missMass_le_loss
#print axioms PoolCoverageBudget.coverage
#print axioms stageBudget_of_survivorRecurrence
#print axioms stageBudget_of_descentTree
#print axioms HitMassInputs.pre_mass_lower
#print axioms HitMassInputs.post_fail_le
#print axioms HitMassInputs.goodMass_lower
#print axioms HitMassInputs.hitMass_of_inputs
#print axioms assembledAttempt_hit_prob_ge_of_inputs
#print axioms hitMass_of_concreteInputs
#print axioms toC5Inputs_of_hitMassInputs

end Cogentic.RandomizedConcreteHitMass
