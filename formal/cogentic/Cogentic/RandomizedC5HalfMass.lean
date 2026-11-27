import Cogentic.RandomizedConcreteHitMassCount

/-!
# C5 H.8 half-mass: the counting reduction

`Cogentic.RandomizedConcreteHitMassCount.C5abcInputs.half_mass` is the remaining
paper-level C5 field (KeyBreak Proposition H.8, p.141):

```
1 / 2 ≤ pmfProb D.ideal (fun x => immediateFactor x ∨ acceptedDense x)
```

i.e. at least half of the ideal mass either finds an immediate factor or yields an
accepted field whose good-prime sets are dense in every selected band.

Neither of the two events is defined concretely anywhere in the tree: the field-pool
coverage objects live on a *different* finite space (`PoolCoverageInputs.Ω`) than the
epoch sample space `D.Sample`, and there is no map from a sample to its field draw or
to its "dense prime set".  The paper's statement is a supply/counting estimate for the
ideal input law; it cannot be derived from the already-formalised C5.a losses.

This file therefore performs the honest reduction to a finite **counting** statement
and proves that, under the paper's ideal law (the uniform law on the finite sample
space), the reduction is exact:

* `HalfMassInputs` records the event identification (a finite set `successes` of
  samples, exactly the samples satisfying `immediateFactor ∨ acceptedDense`) and the
  counting hypothesis `#Sample ≤ 2 * #successes`.
* `HalfMassInputs.half_mass` **proves** the C5.a/H.8 half-mass field from that count,
  using the uniform-law card/mass identity `pmfProb_eq_card_div`.
* `HalfMassInputs.half_mass_iff_half_count` shows the two are equivalent under the
  uniform ideal law, so nothing is lost in the reduction (in particular the event is
  *not* set to the whole space and the probability is *not* set to `1`).
* `HalfMassInputs.half_mass_of_count_subset` allows counting a smaller explicitly
  described set that is contained in the union event.
* `HalfMassInputs.toC5abcInputs` fills `C5abcInputs.half_mass`, hence (with the C5.a
  pool budget, the C5.b/C5.c stage budgets, and the pre-event inclusion) recovers
  `C5abcInputs.pre_mass_lower` and `C5abcInputs.compl_le` from the existing module.

A second, independent route is included where the existing split machinery applies
directly: `half_mass_epochAccepted` instantiates
`RandomizedEpochSuccess.epoch_verified_split_probability_half` in the full-good
regime (every sample is a good transcript, ideal = actual), where that theorem yields
mass `1 / 2` for the epoch-trial success event.  The counting route is the general
one; the split route is the degenerate case in which the hidden-sign factor alone
supplies the half.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and nothing is set to `1`
by fiat: the only non-derived inputs are the explicit count and the uniform-law
identification.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace Cogentic.RandomizedC5HalfMass

open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedConcreteHitMassCount
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochPool
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedPoolCoverage

/-! ## Section 1: Uniform-law mass/count identity -/

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]

/-- The constant-one event has mass one under any finite `PMF`. -/
theorem pmfProb_true {Ω : Type*} [Fintype Ω] (μ : PMF Ω) :
    pmfProb μ (fun _ => True) = 1 := by
  classical
  rw [pmfProb_eq_sum_filter]
  have h : (Finset.univ.filter (fun _ : Ω => True)) = Finset.univ := by simp
  rw [h, pmfWeight_sum_eq_one]

/-- **Uniform card/mass identity.**  If the ideal law gives every sample the same
mass `1 / #Sample`, then the mass of an event is its cardinality divided by
`#Sample`.  This is the step turning the H.8 counting statement into the C5.a
probability statement. -/
theorem pmfProb_eq_card_div
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (E : D.Sample → Prop) [DecidablePred E] :
    pmfProb D.ideal E =
      ((Finset.univ.filter E).card : ℝ) / (Fintype.card D.Sample : ℝ) := by
  classical
  rw [pmfProb_eq_sum_filter]
  simp only [huniform, Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv]

/-- The sample space is nonempty (hence the cardinality is positive) whenever the
ideal law is uniform: a `PMF` cannot live on an empty type. -/
theorem card_pos_of_uniform
    (_huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    0 < Fintype.card D.Sample := by
  classical
  have hsum := pmfWeight_sum_eq_one D.ideal
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset D.Sample) with h | h
  · rw [h] at hsum
    simp at hsum
  · exact Finset.card_pos.mpr h

/-! ## Section 2: The H.8 counting structure -/

/-- **The H.8 half-mass counting data.**

`successes` is the finite set of ideal samples that either yield an immediate factor
or yield an accepted dense field; `mem_successes` is the event identification.  The
only numerical input is `half_count`: at least half of the samples are successful.
`ideal_uniform` records that the ideal law is the uniform law on the finite sample
space (the paper's ideal random input law), which is what converts the count into a
probability. -/
structure HalfMassInputs (D : ConcreteEpochData N) [Fintype D.Sample] where
  /-- H.8 alternative 1: the sample yields an immediate proper factor. -/
  immediateFactor : D.Sample → Prop
  /-- H.8 alternative 2: the sample yields an accepted field whose good-prime sets
  are dense in every selected band. -/
  acceptedDense : D.Sample → Prop
  /-- The finite set of samples satisfying one of the two alternatives. -/
  successes : Finset D.Sample
  /-- Event identification: `successes` is exactly the union of the two H.8
  alternatives. -/
  mem_successes : ∀ x, x ∈ successes ↔ immediateFactor x ∨ acceptedDense x
  /-- The ideal law is uniform on the finite sample space. -/
  ideal_uniform : ∀ x : D.Sample,
    pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹
  /-- H.8 counting: at least half of the ideal samples are successful. -/
  half_count : Fintype.card D.Sample ≤ 2 * successes.card

namespace HalfMassInputs

variable (H : HalfMassInputs D)

/-- `successes` is the filter of the union event. -/
theorem successes_eq_filter
    [DecidablePred (fun x => H.immediateFactor x ∨ H.acceptedDense x)] :
    H.successes =
      Finset.univ.filter (fun x => H.immediateFactor x ∨ H.acceptedDense x) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact H.mem_successes x

/-- **C5.a/H.8 half-mass, proved from the count.** -/
theorem half_mass :
    (1 / 2 : ℝ) ≤
      pmfProb D.ideal (fun x => H.immediateFactor x ∨ H.acceptedDense x) := by
  classical
  have hpos := card_pos_of_uniform H.ideal_uniform
  have hmass := pmfProb_eq_card_div H.ideal_uniform
    (fun x => H.immediateFactor x ∨ H.acceptedDense x)
  rw [hmass, ← H.successes_eq_filter]
  rw [le_div_iff₀ (by exact_mod_cast hpos)]
  have hc : (Fintype.card D.Sample : ℝ) ≤ 2 * (H.successes.card : ℝ) := by
    exact_mod_cast H.half_count
  linarith only [hc]

/-- **Exactness of the reduction.**  Under the uniform ideal law, the half-mass
statement is equivalent to the finite count `#Sample ≤ 2 * #successes`.  So the
counting `Prop` is neither stronger nor weaker than the target: it is exactly the
combinatorial content of H.8. -/
theorem half_mass_iff_half_count :
    (1 / 2 : ℝ) ≤
        pmfProb D.ideal (fun x => H.immediateFactor x ∨ H.acceptedDense x) ↔
      Fintype.card D.Sample ≤ 2 * H.successes.card := by
  classical
  constructor
  · intro h
    have hpos := card_pos_of_uniform H.ideal_uniform
    have hmass := pmfProb_eq_card_div H.ideal_uniform
      (fun x => H.immediateFactor x ∨ H.acceptedDense x)
    rw [hmass, ← H.successes_eq_filter,
      le_div_iff₀ (by exact_mod_cast hpos)] at h
    have hcast : (Fintype.card D.Sample : ℝ) ≤ 2 * (H.successes.card : ℝ) := by
      linarith only [h]
    exact_mod_cast hcast
  · intro _
    exact H.half_mass

/-- **Counting a smaller explicit set.**  If every element of a finset `S` satisfies
one of the two H.8 alternatives and `S` already has at least half the samples, then
the union event has half mass.  This is the form in which a concrete band/dyad
argument is expected to supply the count. -/
theorem half_mass_of_count_subset (S : Finset D.Sample)
    (hsub : ∀ x ∈ S, H.immediateFactor x ∨ H.acceptedDense x)
    (hcount : Fintype.card D.Sample ≤ 2 * S.card) :
    (1 / 2 : ℝ) ≤
      pmfProb D.ideal (fun x => H.immediateFactor x ∨ H.acceptedDense x) := by
  classical
  have hpos := card_pos_of_uniform H.ideal_uniform
  have hmassS : pmfProb D.ideal (fun x => x ∈ S) =
      (S.card : ℝ) / (Fintype.card D.Sample : ℝ) := by
    have hfilter : (Finset.univ.filter (fun x : D.Sample => x ∈ S)) = S := by
      ext x
      simp
    rw [pmfProb_eq_card_div H.ideal_uniform (fun x => x ∈ S), hfilter]
  have hmono : pmfProb D.ideal (fun x => x ∈ S) ≤
      pmfProb D.ideal (fun x => H.immediateFactor x ∨ H.acceptedDense x) :=
    pmfProb_mono D.ideal (fun x hx => hsub x hx)
  have hhalf : (1 / 2 : ℝ) ≤
      (S.card : ℝ) / (Fintype.card D.Sample : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hpos)]
    have hc : (Fintype.card D.Sample : ℝ) ≤ 2 * (S.card : ℝ) := by
      exact_mod_cast hcount
    linarith only [hc]
  calc (1 / 2 : ℝ) ≤ (S.card : ℝ) / (Fintype.card D.Sample : ℝ) := hhalf
    _ = pmfProb D.ideal (fun x => x ∈ S) := hmassS.symm
    _ ≤ pmfProb D.ideal
          (fun x => H.immediateFactor x ∨ H.acceptedDense x) := hmono

/-! ## Section 3: Filling the C5.a–c structure -/

/-- **`C5abcInputs` from the H.8 count.**  The C5.a pool budget and the pre-event
inclusion are passed through unchanged; the `half_mass` field is the theorem proved
above.  Nothing is postulated about the pool or the pre-event. -/
noncomputable def toC5abcInputs (H : HalfMassInputs D)
    (pool : PoolCoverageBudget.{0, 0, 0})
    (pre poolCovered : D.Sample → Prop)
    (poolMiss_le :
      pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
        poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
          pool.inputs.AllGood pool.inputs.hit)
    (pre_of : ∀ x, poolCovered x →
      (H.immediateFactor x ∨ H.acceptedDense x) → pre x) :
    C5abcInputs D where
  pool := pool
  pre := pre
  poolCovered := poolCovered
  poolMiss_le := poolMiss_le
  immediateFactor := H.immediateFactor
  acceptedDense := H.acceptedDense
  half_mass := H.half_mass
  pre_of := pre_of

/-- The `c5abc_compl_le` inequality, obtained from the H.8 count plus the existing
C5.a pool-coverage estimate: the complement of the pre-event has mass at most
`1 / 2 + pool.loss`.  This is `C5abcInputs.compl_le` at the constructed inputs. -/
theorem compl_le (H : HalfMassInputs D)
    (pool : PoolCoverageBudget.{0, 0, 0})
    (pre poolCovered : D.Sample → Prop)
    (poolMiss_le :
      pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
        poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
          pool.inputs.AllGood pool.inputs.hit)
    (pre_of : ∀ x, poolCovered x →
      (H.immediateFactor x ∨ H.acceptedDense x) → pre x) :
    pmfProb D.ideal (fun x => ¬ pre x) ≤ (1 / 2 : ℝ) + pool.loss :=
  (H.toC5abcInputs pool pre poolCovered poolMiss_le pre_of).compl_le

/-- The C5.a–c pre-event mass bound `1 / 2 - (pool + survivor + descent) ≤ P(pre)`
for the inputs built from the H.8 count.  This is
`C5abcInputs.pre_mass_lower` at the constructed inputs and is the consumer inside
`RandomizedConcreteHitMass`. -/
theorem pre_mass_lower (H : HalfMassInputs D)
    (pool : PoolCoverageBudget.{0, 0, 0})
    (pre poolCovered : D.Sample → Prop)
    (poolMiss_le :
      pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
        poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
          pool.inputs.AllGood pool.inputs.hit)
    (pre_of : ∀ x, poolCovered x →
      (H.immediateFactor x ∨ H.acceptedDense x) → pre x)
    (survivor descent algebra coupling : StageBudget D)
    (good_iff : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        pre x ∧ algebra.ok x ∧ coupling.ok x) :
    (1 / 2 : ℝ) - (pool.loss + survivor.loss + descent.loss) ≤
      pmfProb D.ideal pre :=
  (H.toC5abcInputs pool pre poolCovered poolMiss_le pre_of).pre_mass_lower
    survivor descent algebra coupling good_iff

/-- The H.8 inputs also feed the full C5.a–c `HitMassInputs` bundle, whose good-event
mass bound `HitMassInputs.goodMass_lower` then yields
`1 / 4 - totalLoss ≤ P(good)`. -/
noncomputable def toHitMassInputs (H : HalfMassInputs D)
    (pool : PoolCoverageBudget.{0, 0, 0})
    (pre poolCovered : D.Sample → Prop)
    (poolMiss_le :
      pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
        poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
          pool.inputs.AllGood pool.inputs.hit)
    (pre_of : ∀ x, poolCovered x →
      (H.immediateFactor x ∨ H.acceptedDense x) → pre x)
    (survivor descent algebra coupling : StageBudget D)
    (good_iff : ∀ x,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
        pre x ∧ algebra.ok x ∧ coupling.ok x) :
    HitMassInputs D :=
  (H.toC5abcInputs pool pre poolCovered poolMiss_le pre_of).toHitMassInputs
    survivor descent algebra coupling good_iff

end HalfMassInputs

/-! ## Section 4: Consistency of the counting hypothesis

The counting input is satisfiable: when one of the alternatives holds on every sample,
the count is immediate.  This only shows that the reduction is not vacuous; it does
**not** assert that the event is a.e. true in the paper's epoch. -/

/-- If one of the two alternatives holds on every sample then the H.8 count holds,
provided the ideal law is uniform. -/
noncomputable def halfMassInputs_of_forall (huniform :
    ∀ x : D.Sample, pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (immediateFactor acceptedDense : D.Sample → Prop)
    (h : ∀ x, immediateFactor x ∨ acceptedDense x) : HalfMassInputs D where
  immediateFactor := immediateFactor
  acceptedDense := acceptedDense
  successes := Finset.univ
  mem_successes := by
    intro x
    simp only [Finset.mem_univ, true_iff]
    exact h x
  ideal_uniform := huniform
  half_count := by
    rw [Finset.card_univ]
    omega

/-! ## Section 5: The split-theorem specialization (full-good regime)

`RandomizedEpochSuccess.epoch_verified_split_probability_half` turns mass `γ` on good
transcripts into mass `γ / 2 - ε` on accepted epoch trials.  With `γ = 1` (every
sample is a good transcript) and `ε = 0` (ideal = actual) it yields the half-mass
bound for the acceptance event.  This is the place where the existing split assembly
applies directly; in the general regime the counting route of Sections 2–3 is what
supplies the half. -/

section EpochAccepted

variable (E : HardEpochData N)

open Cogentic.RandomizedEpochSuccess

/-- Total variation of a law with itself vanishes. -/
theorem pmfTotalVariation_self_eq_zero (p : PMF E.Sample) :
    pmfTotalVariation p p = 0 := by
  unfold pmfTotalVariation
  simp

/-- The epoch-trial acceptance event. -/
noncomputable def epochAccepted : E.Sample → Prop :=
  fun x => (epochTrial E.trace E.good E.data x).1 ≠ none

/-- **The full-good split specialization.**  If every ideal sample is a good
transcript and the ideal law equals the actual law, then the epoch trial accepts with
ideal probability at least `1 / 2`. -/
theorem half_mass_epochAccepted
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hgood : ∀ x : E.Sample, observe E.trace x ∈ E.good)
    (hseen : ∀ t : E.good,
      ∃ x ∈ {x | observe E.trace x = t.val}, x ∈ E.ideal.support)
    (hcheck : E.CongruenceCheck) (huniform : E.HiddenUniform)
    (hactual : E.ideal = E.actual) :
    (1 / 2 : ℝ) ≤ pmfProb E.ideal (epochAccepted E) := by
  classical
  have hγset : {x : E.Sample | observe E.trace x ∈ E.good} = Set.univ :=
    Set.eq_univ_of_forall hgood
  have huniv : (E.ideal.toOuterMeasure (Set.univ : Set E.Sample)).toReal = 1 := by
    rw [PMF.toOuterMeasure_apply]
    simp [PMF.tsum_coe]
  have hγ : (1 : ℝ) ≤
      (E.ideal.toOuterMeasure {x | observe E.trace x ∈ E.good}).toReal := by
    rw [hγset, huniv]
  have hTV : pmfTotalVariation E.ideal E.actual ≤ (0 : ℝ) := by
    rw [hactual]
    exact le_of_eq (pmfTotalVariation_self_eq_zero E E.actual)
  have hsplit := epoch_verified_split_probability_half hN ho hnot E.ideal E.actual
    E.trace E.good E.data hseen hcheck huniform 1 0 (by norm_num) hγ hTV
  rw [← hactual] at hsplit
  rw [PMF.toOuterMeasure_map_apply] at hsplit
  simpa [pmfProb, epochAccepted] using hsplit

/-- `C5abcInputs` with `acceptedDense` instantiated by the epoch-trial acceptance
event, in the full-good regime.  The immediate-factor alternative is left arbitrary. -/
noncomputable def toC5abcInputs_of_epochAccepted
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hgood : ∀ x : D.Sample,
      observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good)
    (hseen : ∀ t : D.toHardEpochData.good,
      ∃ x ∈ {x | observe D.toHardEpochData.trace x = t.val},
        x ∈ D.toHardEpochData.ideal.support)
    (hcheck : D.toHardEpochData.CongruenceCheck)
    (huniform : D.toHardEpochData.HiddenUniform)
    (hactual : D.toHardEpochData.ideal = D.toHardEpochData.actual)
    (pool : PoolCoverageBudget.{0, 0, 0})
    (pre poolCovered : D.Sample → Prop)
    (immediateFactor : D.Sample → Prop)
    (poolMiss_le :
      pmfProb D.ideal (fun x => ¬ poolCovered x) ≤
        poolMissMass (pmfWeight pool.inputs.μ) pool.inputs.K
          pool.inputs.AllGood pool.inputs.hit)
    (pre_of : ∀ x, poolCovered x →
      (immediateFactor x ∨ epochAccepted D.toHardEpochData x) → pre x) :
    C5abcInputs D where
  pool := pool
  pre := pre
  poolCovered := poolCovered
  poolMiss_le := poolMiss_le
  immediateFactor := immediateFactor
  acceptedDense := fun x => epochAccepted D.toHardEpochData x
  half_mass :=
    (half_mass_epochAccepted D.toHardEpochData hN ho hnot hgood hseen hcheck
      huniform hactual).trans
      (pmfProb_mono D.ideal (fun _ hx => Or.inr hx))
  pre_of := pre_of

end EpochAccepted

/-! ## Axiom audit -/

#print axioms pmfProb_true
#print axioms pmfProb_eq_card_div
#print axioms card_pos_of_uniform
#print axioms HalfMassInputs.successes_eq_filter
#print axioms HalfMassInputs.half_mass
#print axioms HalfMassInputs.half_mass_iff_half_count
#print axioms HalfMassInputs.half_mass_of_count_subset
#print axioms HalfMassInputs.toC5abcInputs
#print axioms HalfMassInputs.compl_le
#print axioms HalfMassInputs.pre_mass_lower
#print axioms HalfMassInputs.toHitMassInputs
#print axioms halfMassInputs_of_forall
#print axioms pmfTotalVariation_self_eq_zero
#print axioms half_mass_epochAccepted
#print axioms toC5abcInputs_of_epochAccepted

end Cogentic.RandomizedC5HalfMass
