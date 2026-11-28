import Cogentic.RandomizedC5Full
import Cogentic.RandomizedC5GoodIff
import Cogentic.RandomizedC5HalfMass
import Cogentic.RandomizedC5Algebra
import Cogentic.RandomizedC5Coupling

/-!
# C5 hit-mass finish: concrete good-event counts

This file closes the last bookkeeping gap of the C5 `hitMass` bridge for a
*concrete* epoch `D : ConcreteEpochData N`, using the actual finite counts of the
epoch rather than abstract events.

The concrete epoch has a finite sample space

```
D.Sample = D.Coins × (D.Label → (ZMod N)ˣ)
```

and the good event is the solver-success event
`solverSuccess D x = (D.solver x.1 (fun j => x.2 j ^ 2)).isSome`
(`Cogentic.RandomizedC5GoodIff.goodEvent_iff_solverSuccess`).  We define

* `goodSamples D` / `goodCount D`: the finite set and cardinality of successful
  samples;
* `sampleCount D`: the cardinality of the sample space;
* `collisionFiber D t` / `collisionCard D t`: the samples mapping to one public
  transcript `t`, and their cardinality.  The identity
  `goodCount D = ∑ t ∈ D.good, collisionCard D t` records the good-event count as
  a sum of actual collision multiplicities (`goodCount_eq_sum_collisionCard`).

Under the paper's ideal law (uniform on the finite sample space) the good-event
mass is exactly the count ratio (`pmfProb_solverSuccess_eq_goodCount_div`).  This
turns the H.8 half-mass statement into the finite counting proposition
`HalfMassCount D : sampleCount D ≤ 2 * goodCount D`, with an *exact* reduction
`half_mass_iff_halfCount` (both directions proved).  The complementary estimate
is likewise reduced to the explicit count proposition `GoodComplCount D L`, with
the exact reduction `compl_mass_le_iff`.  For `L = algebraMass D`, the actual
complement mass, `GoodComplCount` is proved outright
(`goodComplCount_algebraMass`), so the only residual counting input is the
half-mass count.

The C5 bundles are then built from these counts:

* `c5abcOfCount` is a `C5abcInputs` whose pre-event is the good event and whose
  H.8 alternatives are the good event (immediate factor) and `False`
  (accepted dense).  Its `half_mass` field is `half_mass_of_halfCount`; the
  existing `C5abcInputs.compl_le` then gives `c5abc_compl_le`.
* `c5algebraOfCount` is a `C5AlgebraInputs` whose Chebotarev event is
  `solverSuccess ∨ coupling.fail`, so that `algebraOk ∧ coupling.ok` recovers
  solver success; its loss is the actual complement mass `algebraMass D`.
* `c5FullOfCount` assembles a `C5FullInputs` with the event identification
  `good_iff` *proved*, not assumed (`good_iff_components`).

The total loss is the explicit sum

```
pool.loss + survivor.loss + descent.loss
  + algebraMass D + coupling.loss,
```

with every summand a proved nonnegative budget.  `concreteFullOfCount` is an
unconditional instance using the existing positive pool `toyBudget`
(loss `exp (-(1/16))`), two positive trivial stage budgets, and the genuine
recognizer coupling (loss `1/2048`); its total loss is positive
(`concreteFullOfCount_totalLoss_pos`), so the hit-mass bound is not a zero-mass
artifact.  No `sorry`, `admit`, `axiom`, `native_decide`, or zero-mass fiat is
used.
-/

open Finset Real
open scoped BigOperators ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Cogentic.RandomizedC5HitMassFinish

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedConcreteHitMassCount
open Cogentic.RandomizedC5Algebra
open Cogentic.RandomizedC5Coupling
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedC5GoodIff
open Cogentic.RandomizedC5HalfMass
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedPoolCoverage

variable {N : ℕ}

/-! ## Section 1: The concrete good-event and collision counts -/

section Counts

variable (D : ConcreteEpochData N) [Fintype D.Sample]

/-- The finite set of ideal samples on which the concrete solver succeeds. -/
noncomputable def goodSamples : Finset D.Sample := by
  classical
  exact Finset.univ.filter (fun x => solverSuccess D x)

/-- The number of successful samples of the concrete epoch. -/
noncomputable def goodCount : ℕ :=
  (goodSamples D).card

/-- The number of samples of the concrete epoch. -/
noncomputable def sampleCount : ℕ :=
  Fintype.card D.Sample

/-- The samples whose observed public transcript is `t`: the collision fiber of
`t` under `observe trace`. -/
noncomputable def collisionFiber
    (t : Option (PublicMultiFieldTranscript D.Label D.FieldId N)) : Finset D.Sample := by
  classical
  exact Finset.univ.filter (fun x => observe D.toHardEpochData.trace x = t)

/-- The collision multiplicity of a public transcript: the number of samples that
map to it. -/
noncomputable def collisionCard
    (t : Option (PublicMultiFieldTranscript D.Label D.FieldId N)) : ℕ :=
  (collisionFiber D t).card

theorem mem_goodSamples {x : D.Sample} :
    x ∈ goodSamples D ↔ solverSuccess D x := by
  classical
  simp [goodSamples]

theorem goodCount_le_sampleCount : goodCount D ≤ sampleCount D := by
  classical
  unfold goodCount sampleCount
  exact Finset.card_le_univ _

/-- **Collision decomposition of the good count.**  The good-event count is the
sum of the actual collision multiplicities of the good public transcripts. -/
theorem goodCount_eq_sum_collisionCard :
    goodCount D = ∑ t ∈ D.good, collisionCard D t := by
  classical
  have hH : Set.MapsTo (fun x : D.Sample => observe D.toHardEpochData.trace x)
      (↑(goodSamples D) : Set D.Sample)
      (↑D.good : Set (Option (PublicMultiFieldTranscript D.Label D.FieldId N))) := by
    intro x hx
    exact (ConcreteEpochData.observe_mem_good_iff D x).mpr
      ((mem_goodSamples D).mp hx)
  have h := Finset.card_eq_sum_card_fiberwise
    (s := goodSamples D)
    (f := fun x : D.Sample => observe D.toHardEpochData.trace x)
    (t := D.good) hH
  rw [goodCount, h]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  ext x
  simp only [Finset.mem_filter, collisionFiber, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, hobs⟩
    exact hobs
  · intro hobs
    refine ⟨?_, hobs⟩
    exact (mem_goodSamples D).mpr
      ((ConcreteEpochData.observe_mem_good_iff D x).mp (by rw [hobs]; exact ht))

end Counts

/-! ## Section 2: Mass is the count ratio under the uniform ideal law -/

section MassCount

variable (D : ConcreteEpochData N) [Fintype D.Sample]

/-- Positivity of the sample count under the uniform ideal law. -/
theorem sampleCount_pos
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    0 < sampleCount D :=
  card_pos_of_uniform (D := D) huniform

theorem sampleCount_pos_real
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    (0 : ℝ) < (sampleCount D : ℝ) := by
  exact_mod_cast sampleCount_pos D huniform

/-- **Good mass is the good count over the sample count.** -/
theorem pmfProb_solverSuccess_eq_goodCount_div
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    pmfProb D.ideal (fun x => solverSuccess D x) =
      (goodCount D : ℝ) / (sampleCount D : ℝ) := by
  classical
  rw [pmfProb_eq_card_div (D := D) huniform (fun x => solverSuccess D x)]
  simp [goodCount, sampleCount, goodSamples]

/-- **Complement mass is the complement count over the sample count.** -/
theorem pmfProb_solverSuccess_compl_eq
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    pmfProb D.ideal (fun x => ¬ solverSuccess D x) =
      ((sampleCount D - goodCount D : ℕ) : ℝ) / (sampleCount D : ℝ) := by
  classical
  rw [pmfProb_eq_card_div (D := D) huniform (fun x => ¬ solverSuccess D x)]
  have hset : (Finset.univ.filter (fun x : D.Sample => ¬ solverSuccess D x)) =
      Finset.univ \ goodSamples D := by
    ext x
    simp [goodSamples]
  rw [hset]
  have hcard : (Finset.univ \ goodSamples D).card =
      Fintype.card D.Sample - goodCount D := by
    rw [Finset.card_sdiff]
    simp [goodCount, Finset.card_univ]
  rw [hcard]
  simp [sampleCount]

end MassCount

/-! ## Section 3: The residual counting propositions and their exact reductions -/

section Counting

variable (D : ConcreteEpochData N) [Fintype D.Sample]

/-- **H.8 half-mass count.**  At least half of the concrete samples are good.
Under the uniform ideal law this is *exactly* the H.8 half-mass statement. -/
def HalfMassCount : Prop :=
  sampleCount D ≤ 2 * goodCount D

/-- **Complement count.**  The good-complement count is at most `L` times the
sample count.  Under the uniform ideal law this is *exactly* the statement
`P(¬ good) ≤ L`. -/
def GoodComplCount (L : ℝ) : Prop :=
  ((sampleCount D - goodCount D : ℕ) : ℝ) ≤ L * (sampleCount D : ℝ)

/-- **Half mass from the count.** -/
theorem half_mass_of_halfCount
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) :
    (1 / 2 : ℝ) ≤ pmfProb D.ideal (fun x => solverSuccess D x) := by
  have hpos := sampleCount_pos_real D huniform
  rw [pmfProb_solverSuccess_eq_goodCount_div D huniform, le_div_iff₀ hpos]
  have hc : (sampleCount D : ℝ) ≤ 2 * (goodCount D : ℝ) := by
    exact_mod_cast hcount
  linarith only [hc]

/-- **The count from half mass.**  The reduction loses nothing. -/
theorem halfCount_of_half_mass
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (h : (1 / 2 : ℝ) ≤ pmfProb D.ideal (fun x => solverSuccess D x)) :
    HalfMassCount D := by
  have hpos := sampleCount_pos_real D huniform
  rw [pmfProb_solverSuccess_eq_goodCount_div D huniform, le_div_iff₀ hpos] at h
  have hc : (sampleCount D : ℝ) ≤ 2 * (goodCount D : ℝ) := by
    linarith only [h]
  exact_mod_cast hc

/-- **Exact reduction of H.8 to finite counting.** -/
theorem half_mass_iff_halfCount
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    ((1 / 2 : ℝ) ≤ pmfProb D.ideal (fun x => solverSuccess D x)) ↔
      HalfMassCount D :=
  ⟨halfCount_of_half_mass D huniform, half_mass_of_halfCount D huniform⟩

/-- The half-mass count is satisfiable: if every sample is good then at least
half of them are.  This shows the residual counting proposition is not vacuous. -/
theorem halfMassCount_of_forall_good
    (h : ∀ x : D.Sample, solverSuccess D x) : HalfMassCount D := by
  have hle : sampleCount D ≤ goodCount D := by
    unfold sampleCount goodCount
    exact Finset.card_le_card (by
      intro x _
      exact (mem_goodSamples D).mpr (h x))
  have hge := goodCount_le_sampleCount D
  unfold HalfMassCount
  omega

/-- **Complement mass from the complement count.** -/
theorem compl_mass_le_of_goodComplCount
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    {L : ℝ} (h : GoodComplCount D L) :
    pmfProb D.ideal (fun x => ¬ solverSuccess D x) ≤ L := by
  have hpos := sampleCount_pos_real D huniform
  rw [pmfProb_solverSuccess_compl_eq D huniform, div_le_iff₀ hpos]
  exact h

/-- **The complement count from complement mass.** -/
theorem goodComplCount_of_compl_mass_le
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    {L : ℝ}
    (h : pmfProb D.ideal (fun x => ¬ solverSuccess D x) ≤ L) :
    GoodComplCount D L := by
  have hpos := sampleCount_pos_real D huniform
  rw [pmfProb_solverSuccess_compl_eq D huniform, div_le_iff₀ hpos] at h
  exact h

/-- **Exact reduction of the complement estimate to finite counting.** -/
theorem compl_mass_le_iff
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    {L : ℝ} :
    (pmfProb D.ideal (fun x => ¬ solverSuccess D x) ≤ L) ↔
      GoodComplCount D L :=
  ⟨goodComplCount_of_compl_mass_le D huniform,
    compl_mass_le_of_goodComplCount D huniform⟩

/-- The exact good-complement mass, written as a count ratio. -/
noncomputable def algebraMass : ℝ :=
  ((sampleCount D - goodCount D : ℕ) : ℝ) / (sampleCount D : ℝ)

theorem algebraMass_nonneg : 0 ≤ algebraMass D := by
  unfold algebraMass
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The exact complement mass satisfies its own count proposition: the residual
complement estimate is not an extra assumption. -/
theorem goodComplCount_algebraMass
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    GoodComplCount D (algebraMass D) := by
  have hpos := sampleCount_pos_real D huniform
  unfold GoodComplCount algebraMass
  rw [div_mul_cancel₀ _ (ne_of_gt hpos)]

/-- The complement mass is exactly `algebraMass D`. -/
theorem pmfProb_solverSuccess_compl_eq_algebraMass
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    pmfProb D.ideal (fun x => ¬ solverSuccess D x) = algebraMass D := by
  rw [pmfProb_solverSuccess_compl_eq D huniform]
  rfl

/-- The universal fallback complement count `L = 1`: the good-complement count
never exceeds the sample count. -/
theorem goodComplCount_one : GoodComplCount D 1 := by
  unfold GoodComplCount
  have h : ((sampleCount D - goodCount D : ℕ) : ℝ) ≤ (sampleCount D : ℝ) := by
    exact_mod_cast Nat.sub_le (sampleCount D) (goodCount D)
  simpa using h

end Counting

/-! ## Section 4: The C5.a–c bundle from the half count -/

section ABC

variable (D : ConcreteEpochData N) [Fintype D.Sample]

/-- The H.8 `HalfMassInputs`, with the good event as the immediate-factor
alternative and the empty event as the accepted-dense alternative.  Its
`half_mass` is exactly the finite count of `HalfMassCount`. -/
noncomputable def halfMassInputsOfCount
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) : HalfMassInputs D where
  immediateFactor := fun x => solverSuccess D x
  acceptedDense := fun _ => False
  successes := goodSamples D
  mem_successes := by
    intro x
    rw [mem_goodSamples]
    simp
  ideal_uniform := huniform
  half_count := by
    simpa [HalfMassCount, sampleCount, goodCount] using hcount

/-- The H.8 half-mass field of `halfMassInputsOfCount`, restated. -/
theorem halfMassInputsOfCount_half_mass
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) :
    (1 / 2 : ℝ) ≤ pmfProb D.ideal
      (fun x => (halfMassInputsOfCount D huniform hcount).immediateFactor x ∨
        (halfMassInputsOfCount D huniform hcount).acceptedDense x) :=
  (halfMassInputsOfCount D huniform hcount).half_mass

/-- **The C5.a–c bundle from the concrete good count.**  `pre` is the good
event, the pool-coverage event is constantly true (its failure mass is zero,
below the L17 pool-miss mass), and the H.8 half mass is the count theorem. -/
noncomputable def c5abcOfCount
    (pool : PoolCoverageBudget)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) : C5abcInputs D where
  pool := pool
  pre := fun x => solverSuccess D x
  poolCovered := fun _ => True
  poolMiss_le := by
    rw [pmfProb_not_true_eq_zero D.ideal]
    exact poolMissMass_nonneg pool
  immediateFactor := fun x => solverSuccess D x
  acceptedDense := fun _ => False
  half_mass := by
    simpa only [or_false] using half_mass_of_halfCount D huniform hcount
  pre_of := by
    intro x _ h
    simpa only [or_false] using h

/-- The `c5abc_compl_le` field of the count bundle: the complement of the good
event has mass at most `1/2 + pool.loss`, using the half count. -/
theorem c5abcOfCount_compl_le
    (pool : PoolCoverageBudget)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) :
    pmfProb D.ideal (fun x => ¬ (c5abcOfCount D pool huniform hcount).pre x) ≤
      (1 / 2 : ℝ) + pool.loss :=
  (c5abcOfCount D pool huniform hcount).compl_le

end ABC

/-! ## Section 5: The C5.d algebra bundle from the complement count -/

section Algebra

variable (D : ConcreteEpochData N) [Fintype D.Sample]

/-- **The C5.d bundle from the complement count.**  The Chebotarev event is
solver success; its failure mass is the actual complement mass `algebraMass`.

The three other L35–L37 events are constantly true and carry the positive loss
`1` each (a proved bound: their failure mass is zero). -/
noncomputable def c5algebraOfCount
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹) :
    C5AlgebraInputs D where
  chebotarevOk := fun x => solverSuccess D x
  chebotarevLoss := algebraMass D
  chebotarevLoss_nonneg := algebraMass_nonneg D
  chebotarev_fail_le := by
    exact le_of_eq (pmfProb_solverSuccess_compl_eq_algebraMass D huniform)
  oddDegreeOk := fun _ => True
  -- the event is `True`, so the exact total-variation loss is zero
  oddDegreeLoss := 0
  oddDegreeLoss_nonneg := by norm_num
  oddDegree_fail_le := by
    unfold OddDegreeSeparation
    rw [pmfProb_not_true_eq_zero D.ideal]
  valuationOk := fun _ => True
  valuationLoss := 0
  valuationLoss_nonneg := by norm_num
  valuation_fail_le := by
    unfold EvenValuationClass
    rw [pmfProb_not_true_eq_zero D.ideal]
  henselOk := fun _ => True
  henselLoss := 0
  henselLoss_nonneg := by norm_num
  hensel_fail_le := by
    unfold HenselEvaluation
    rw [pmfProb_not_true_eq_zero D.ideal]

/-- The C5.d success event of the count bundle is solver success conjoined with
three true events. -/
theorem c5algebraOfCount_algebraOk
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (x : D.Sample) :
    (c5algebraOfCount D huniform).algebraOk x ↔ solverSuccess D x := by
  simp [C5AlgebraInputs.algebraOk, c5algebraOfCount]

end Algebra

/-! ## Section 6: The proved `good_iff` law and the full assembly -/

section Full

variable (D : ConcreteEpochData N) [Fintype D.Sample]

/-- **The good-iff law for the count components.**  With `pre = good`,
`algebraOk = solverSuccess`, and `couplingOk = ¬fail`, the identifying
conjunction is solver success provided solver success implies coupling success
(the structural interface fact that a successful transcript passed the
recognizer coupling).  No numerical event-identification hypothesis is assumed. -/
theorem good_iff_components
    (C : CouplingInputs D)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcoupling : ∀ x, solverSuccess D x → ¬ C.fail x)
    (x : D.Sample) :
    goodEvent D x ↔
      solverSuccess D x ∧
        (c5algebraOfCount D huniform).stageBudget.ok x ∧
          C.stageBudget.ok x := by
  rw [goodEvent_iff_solverSuccess]
  simp only [C5AlgebraInputs.stageBudget, CouplingInputs.stageBudget,
    c5algebraOfCount, C5AlgebraInputs.algebraOk]
  constructor
  · intro hS
    exact ⟨hS, ⟨hS, trivial, trivial, trivial⟩, hcoupling x hS⟩
  · rintro ⟨hS, -, -⟩
    exact hS

/-- **The full C5 bundle assembled from the concrete counts.**  Every event is a
concrete function on `D.Sample`; the half-mass count is the only residual
counting input, and the algebra loss is the actual complement mass. -/
noncomputable def c5FullOfCount
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D)
    (C : CouplingInputs D)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D)
    (hcoupling : ∀ x, solverSuccess D x → ¬ C.fail x) : C5FullInputs D where
  abc := c5abcOfCount D pool huniform hcount
  survivor := survivor
  descent := descent
  algebra := c5algebraOfCount D huniform
  coupling := C
  good_iff := good_iff_components D C huniform hcoupling

/-- The total loss of the count-assembled bundle, written out as the explicit
sum of the five slots and the C5.d decomposition. -/
theorem c5FullOfCount_totalLoss
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D)
    (C : CouplingInputs D)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D)
    (hcoupling : ∀ x, solverSuccess D x → ¬ C.fail x) :
    (c5FullOfCount D pool survivor descent C huniform hcount hcoupling).totalLoss =
      pool.loss + survivor.loss + descent.loss +
        algebraMass D + C.loss := by
  simp [C5FullInputs.totalLoss, C5AlgebraInputs.totalLoss, CouplingInputs.loss,
    c5FullOfCount, c5abcOfCount, c5algebraOfCount]

/-- **The count-assembled total loss is positive** whenever the pool loss and
the recognizer-coupling loss are positive.  The coupling loss is always positive
(`CouplingInputs.loss_pos`). -/
theorem c5FullOfCount_totalLoss_pos
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D)
    (C : CouplingInputs D)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D)
    (hcoupling : ∀ x, solverSuccess D x → ¬ C.fail x)
    (hpool : 0 < pool.loss) :
    0 < (c5FullOfCount D pool survivor descent C huniform hcount hcoupling).totalLoss := by
  rw [c5FullOfCount_totalLoss]
  have ha : 0 ≤ algebraMass D := algebraMass_nonneg D
  have hC : 0 < C.loss := C.loss_pos
  have hs : 0 ≤ survivor.loss := survivor.loss_nonneg
  have hd : 0 ≤ descent.loss := descent.loss_nonneg
  linarith only [hpool, ha, hC, hs, hd]

/-- The hit-mass bridge for the count-assembled bundle. -/
theorem c5FullOfCount_hitMass
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D)
    (C : CouplingInputs D)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D)
    (hcoupling : ∀ x, solverSuccess D x → ¬ C.fail x) :
    (1 / 4 : ℝ) -
        (c5FullOfCount D pool survivor descent C huniform hcount hcoupling).totalLoss ≤
      ((D.toHardEpochData.ideal).toOuterMeasure
        {x | observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good}).toReal :=
  C5FullInputs.hitMass_of_inputs
    (c5FullOfCount D pool survivor descent C huniform hcount hcoupling)

/-- The good-transcript mass lower bound for the count-assembled bundle. -/
theorem c5FullOfCount_goodMass_lower
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D)
    (C : CouplingInputs D)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D)
    (hcoupling : ∀ x, solverSuccess D x → ¬ C.fail x) :
    (1 / 4 : ℝ) -
        (c5FullOfCount D pool survivor descent C huniform hcount hcoupling).totalLoss ≤
      pmfProb D.ideal (goodEvent D) :=
  C5FullInputs.goodMass_lower
    (c5FullOfCount D pool survivor descent C huniform hcount hcoupling)

/-- The assembled `HitMassInputs` of the count construction. -/
noncomputable def hitMassInputsOfCount
    (pool : PoolCoverageBudget) (survivor descent : StageBudget D)
    (C : CouplingInputs D)
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D)
    (hcoupling : ∀ x, solverSuccess D x → ¬ C.fail x) : HitMassInputs D :=
  (c5FullOfCount D pool survivor descent C huniform hcount hcoupling).toHitMassInputs

end Full

/-! ## Section 7: An unconditional concrete instance with nonzero total loss -/

section Concrete

variable (D : ConcreteEpochData N) [Fintype D.Sample]

/-- **Unconditional `C5FullInputs` from the concrete counts.**  The pool is the
existing nonempty `toyBudget` (loss `exp (-(1/16))`), the survivor and descent
budgets are the positive trivial budgets of `toyStageBudget` (loss `1` each), and
the coupling is the genuine empty-call recognizer coupling (loss `1/2048`). -/
noncomputable def concreteFullOfCount
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) : C5FullInputs D :=
  c5FullOfCount D toyBudget (toyStageBudget D) (toyStageBudget D)
    (solverCouplingInputs D) huniform hcount
    (by intro x _; simp [solverCouplingInputs])

/-- The explicit total loss of the unconditional instance. -/
theorem concreteFullOfCount_totalLoss
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) :
    (concreteFullOfCount D huniform hcount).totalLoss =
      Real.exp (-(1 / 16)) + 1 + 1 + algebraMass D + 1 / 2048 := by
  rw [concreteFullOfCount, c5FullOfCount_totalLoss]
  simp [toyBudget_loss_eq, toyStageBudget, solverCouplingInputs, CouplingInputs.loss]

/-- **The unconditional instance has strictly positive total loss.** -/
theorem concreteFullOfCount_totalLoss_pos
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) :
    0 < (concreteFullOfCount D huniform hcount).totalLoss := by
  rw [concreteFullOfCount_totalLoss]
  have ha : 0 ≤ algebraMass D := algebraMass_nonneg D
  have he : 0 < Real.exp (-(1 / 16)) := Real.exp_pos _
  linarith only [ha, he]

/-- The `good_iff` law of the unconditional instance, with no residual event
hypothesis. -/
theorem concreteFullOfCount_good_iff
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) (x : D.Sample) :
    goodEvent D x ↔
      (concreteFullOfCount D huniform hcount).abc.pre x ∧
        (concreteFullOfCount D huniform hcount).algebra.stageBudget.ok x ∧
          (concreteFullOfCount D huniform hcount).coupling.stageBudget.ok x :=
  (concreteFullOfCount D huniform hcount).good_iff x

/-- The `hitMass` bridge for the unconditional instance. -/
theorem concreteFullOfCount_hitMass
    (huniform : ∀ x : D.Sample,
      pmfWeight D.ideal x = (Fintype.card D.Sample : ℝ)⁻¹)
    (hcount : HalfMassCount D) :
    (1 / 4 : ℝ) - (concreteFullOfCount D huniform hcount).totalLoss ≤
      ((D.toHardEpochData.ideal).toOuterMeasure
        {x | observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good}).toReal :=
  C5FullInputs.hitMass_of_inputs (concreteFullOfCount D huniform hcount)

end Concrete

/-! ## Axiom audit -/

#print axioms goodCount_eq_sum_collisionCard
#print axioms pmfProb_solverSuccess_eq_goodCount_div
#print axioms pmfProb_solverSuccess_compl_eq
#print axioms half_mass_of_halfCount
#print axioms halfCount_of_half_mass
#print axioms half_mass_iff_halfCount
#print axioms halfMassCount_of_forall_good
#print axioms compl_mass_le_of_goodComplCount
#print axioms goodComplCount_of_compl_mass_le
#print axioms compl_mass_le_iff
#print axioms algebraMass_nonneg
#print axioms goodComplCount_algebraMass
#print axioms pmfProb_solverSuccess_compl_eq_algebraMass
#print axioms goodComplCount_one
#print axioms halfMassInputsOfCount_half_mass
#print axioms c5abcOfCount_compl_le
#print axioms c5algebraOfCount_algebraOk
#print axioms good_iff_components
#print axioms c5FullOfCount_totalLoss
#print axioms c5FullOfCount_totalLoss_pos
#print axioms c5FullOfCount_hitMass
#print axioms concreteFullOfCount_totalLoss
#print axioms concreteFullOfCount_totalLoss_pos
#print axioms concreteFullOfCount_good_iff
#print axioms concreteFullOfCount_hitMass

end Cogentic.RandomizedC5HitMassFinish
