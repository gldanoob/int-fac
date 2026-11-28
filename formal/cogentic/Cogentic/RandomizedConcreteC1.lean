import Cogentic.RandomizedConcreteEpochChecks
import Cogentic.RandomizedC1C2FromConcrete

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# C1 for the concrete epoch: exact statement, refutation of the placeholder,
and the repaired transcript construction

## The exact predicate

`ConcreteEpochData.GlobalProductIdentity D` (`RandomizedConcreteEpochChecks`,
§1) is literally

```
∀ (t : D.good) (x : D.Sample), observe D.solver x = t.val →
  (∏ i ∈ (D.extract t).mask, (x.2 i) ^ 2)
    = (D.extract t).ratCorr * ∏ j ∈ (D.extract t).fields, (D.extract t).fieldProd j
```

where

* `D.Sample = D.Coins × (D.Label → (ZMod N)ˣ)`;
* `observe D.solver x = D.solver x.1 (fun j => x.2 j ^ 2)` — the solver sees only
  the **squared** hidden labels;
* `D.good = D.publicCandidates.filter Option.isSome`, i.e. exactly the successful
  solver outputs;
* `D.extract t` is the transcript stored in the solver output.

So the predicate says: on every successful solver output, the product of the
observed hidden squares over the mask is the product of the public squares
stored in the transcript.  It is the global modular product identity used by
`labelProduct_sq_eq_assembled_publicRoot` and hence the only number-theoretic
input to C1.

## Verdict

* It is **not** a consequence of `ConcreteEpochData` (nor of the construction of
  `Sample`/`good`): the record leaves the solver completely free, and the
  placeholder `goodEpochOfLe` is an explicit counterexample at `N = 15`
  (`not_globalProductIdentity_goodEpochOfLe`; restated below as
  `not_forall_globalProductIdentity`).  The defect in that transcript is
  concrete: it publishes `ratCorr = 1`, `ratRoot = 1`, `mask = {()}`, no fields,
  while the observed hidden square at `()` is `2² = 4`.

* The identity **is** true for a concrete epoch whose solver actually builds the
  correction from the observed square and publishes a square root of it.  The
  repaired epoch `concreteEpoch n hN` below does exactly that: the solver scans
  the finite unit group for a square root of the observed hidden square and
  publishes the one-coordinate transcript with `ratCorr = r ^ 2`, `ratRoot = r`,
  `mask = {()}`, no fields.  The search is a finite, terminating computation;
  its cost is charged in stage `S0`.  On every sample the observed hidden square
  is a square, so the search succeeds.  We prove
  `concreteEpoch_globalProductIdentity` from this construction, derive
  `C1Inputs` for the family, and package the Wave-24 `c1Concrete` slot at the
  repaired epoch.

## What must change in the placeholder

The placeholder cannot be repaired by a proof: its `goodTr` transcript is
independent of the sample.  The data that must change is the **transcript
construction**: `ratCorr` must be the observed masked square (not `1`) and
`ratRoot` must be a square root of it (not `1`).  Equivalently, the solver must
carry the private root, or perform the finite root search as below.  This is
exactly why C1 is the difficult input: producing such a root is the factoring
step.  The formal repair below is non-vacuous (every sample is successful, the
public work is strictly positive), but it pays the full finite-search cost in
`S0`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedConcreteC1

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedHiddenLabels
open Cogentic.RandomizedHiddenOutputLaw
open scoped BigOperators ENNReal

/-! ## Section 1: the predicate is not a consequence of the data -/

/-- `GlobalProductIdentity` is not forced by `ConcreteEpochData`: the structure
admits the `goodEpochOfLe` placeholder, whose transcript lies about the public
root. -/
theorem not_forall_globalProductIdentity :
    ¬ ∀ D : ConcreteEpochData 15, D.GlobalProductIdentity := by
  intro h
  exact Cogentic.RandomizedC1C2FromConcrete.not_globalProductIdentity_goodEpochOfLe
    (h (Cogentic.RandomizedWave17Audit.goodEpochOfLe 15 (by norm_num)))

/-- The Wave-24 `c1Concrete` field is typed at `goodEpochOfLe`, so the existing
field is uninhabited.  Any repair of the Wave-24 record must re-point that field
(and the companion `concreteFamily`) at a solver with a genuine root
construction, such as `concreteEpoch` below. -/
theorem wave24_c1Concrete_unfillable :
    ¬ (∀ n (hN : 3 ≤ n),
      (Cogentic.RandomizedWave17Audit.goodEpochOfLe n hN).GlobalProductIdentity) := by
  intro h
  exact Cogentic.RandomizedC1C2FromConcrete.not_globalProductIdentity_goodEpochOfLe
    (h 15 (by norm_num))

/-- **The structural obstruction, independent of the placeholder.**  If a good
transcript has singleton mask `{i0}`, no fields, and correction `1`, then the
global product identity forces the observed hidden square at `i0` to be `1`.
Hence any epoch which publishes correction `1` for a nontrivial observed square
fails C1.  The placeholder `goodEpochOfLe` is exactly this case with
`i0 = ()` and `x.2 () = 2` in `ZMod 15`.  The repaired construction must
therefore change `ratCorr` and `ratRoot`: `ratCorr` must be the observed masked
square (or a product decomposition of it) and `ratRoot` a square root of it. -/
theorem not_globalProductIdentity_of_trivial_mask
    {N : ℕ} {D : ConcreteEpochData N} {t : D.good} {x : D.Sample} {i0 : D.Label}
    (hmask : (D.extract t).mask = {i0})
    (hfields : (D.extract t).fields = ∅)
    (hrat : (D.extract t).ratCorr = 1)
    (hx : observe D.solver x = t.val)
    (hsq : x.2 i0 ^ 2 ≠ 1) :
    ¬ D.GlobalProductIdentity := by
  intro h
  have hprod := h t x hx
  rw [hmask, hfields, hrat] at hprod
  simp only [Finset.prod_singleton, Finset.prod_empty, mul_one] at hprod
  exact hsq hprod

/-! ## Section 2: the repaired concrete epoch -/

/-- The finite set of square roots of a unit. -/
def sqrtRoots (N : ℕ) [NeZero N] (v : (ZMod N)ˣ) : Finset (ZMod N)ˣ :=
  Finset.univ.filter (fun r => r ^ 2 = v)

/-- The canonical square root selected from the finite search: the least root
with respect to the residue-representative order.  This is a finite search over
the unit group, not a `Classical.choose` of a public root: the choice is made
from a decidable finite set and its defining property is
`sqrtUnit_spec`. -/
noncomputable def sqrtUnit (N : ℕ) [NeZero N] (v : (ZMod N)ˣ) : Option (ZMod N)ˣ :=
  letI : LinearOrder (ZMod N)ˣ :=
    LinearOrder.lift' (fun r : (ZMod N)ˣ => (r : ZMod N).val)
      (fun _ _ h => Units.ext (ZMod.val_injective N h))
  if h : (sqrtRoots N v).Nonempty then some ((sqrtRoots N v).min' h) else none

/-- The defining property of the selected root. -/
theorem sqrtUnit_spec {N : ℕ} [NeZero N] {v r : (ZMod N)ˣ}
    (h : sqrtUnit N v = some r) : r ^ 2 = v := by
  unfold sqrtUnit at h
  letI : LinearOrder (ZMod N)ˣ :=
    LinearOrder.lift' (fun r : (ZMod N)ˣ => (r : ZMod N).val)
      (fun _ _ h => Units.ext (ZMod.val_injective N h))
  split_ifs at h with hne
  · injection h with hr
    subst hr
    simpa [sqrtRoots] using Finset.min'_mem (sqrtRoots N v) hne

/-- Every square has a selected root. -/
theorem sqrtUnit_isSome_of_sq {N : ℕ} [NeZero N] {v u : (ZMod N)ˣ} (h : u ^ 2 = v) :
    (sqrtUnit N v).isSome := by
  unfold sqrtUnit
  letI : LinearOrder (ZMod N)ˣ :=
    LinearOrder.lift' (fun r : (ZMod N)ˣ => (r : ZMod N).val)
      (fun _ _ h => Units.ext (ZMod.val_injective N h))
  rw [dif_pos]
  · simp
  · exact ⟨u, by simp [sqrtRoots, h]⟩

/-- The one-coordinate transcript published by the repaired solver:
mask `{()}`, no fields, correction root `r`, correction `r ^ 2`. -/
def rootTranscript {N : ℕ} (r : (ZMod N)ˣ) :
    PublicMultiFieldTranscript Unit Unit N where
  mask := {()}
  mask_nonempty := ⟨(), by simp⟩
  fields := ∅
  ratCorr := r ^ 2
  ratRoot := r
  ratRoot_sq := rfl
  fieldProd := fun _ => 1
  fieldRoot := fun _ => 1
  fieldRoot_sq := by intro j hj; simp at hj

/-- The defining algebraic identity of `rootTranscript`. -/
theorem rootTranscript_identity {N : ℕ} (r : (ZMod N)ˣ) (x : Unit → (ZMod N)ˣ)
    (hsq : r ^ 2 = x () ^ 2) :
    (∏ i ∈ (rootTranscript r).mask, x i ^ 2) =
      (rootTranscript r).ratCorr *
        ∏ j ∈ (rootTranscript r).fields, (rootTranscript r).fieldProd j := by
  simp [rootTranscript, hsq]

/-- The repaired solver.  It scans the finite unit group for a square root of
the observed hidden square and publishes the corresponding one-coordinate
transcript.  On a square input (in particular on every observed sample) the
search succeeds.  On a non-square input the fallback root `1` is published;
such an input is never an observed square, and any sample that does observe the
same `rootTranscript 1` has hidden square `1`, so the product identity is
unaffected. -/
noncomputable def concreteSolver (N : ℕ) [NeZero N] (s : Unit → (ZMod N)ˣ) :
    Option (PublicMultiFieldTranscript Unit Unit N) :=
  some (rootTranscript ((sqrtUnit N (s ())).getD 1))

/-- The repaired concrete epoch.  `S0` is charged the size of the finite unit
group scanned by the root search; the other stages are zero in this C1-focused
construction. -/
noncomputable def concreteEpochCore (N : ℕ) [NeZero N] : ConcreteEpochData N :=
  { Coins := Unit
    Label := Unit
    FieldId := Unit
    ideal := PMF.uniformOfFintype (Unit × (Unit → (ZMod N)ˣ))
    actual := PMF.uniformOfFintype (Unit × (Unit → (ZMod N)ˣ))
    solver := fun _ s => concreteSolver N s
    publicCandidates := Finset.univ.image (fun s : Unit → (ZMod N)ˣ => concreteSolver N s)
    solver_mem_candidates := by
      intro x
      exact Finset.mem_image.mpr ⟨x.2, Finset.mem_univ _, rfl⟩
    candidates_complete := by
      intro t ht _
      obtain ⟨s, -, hs⟩ := Finset.mem_image.mp ht
      exact ⟨(), s, hs⟩
    stageCosts :=
      { s0 := fun _ => Fintype.card (ZMod N)ˣ
        s1 := fun _ => 0
        s2 := fun _ => 0
        s3 := fun _ => 0
        s4 := fun _ => 0
        s5 := fun _ => 0
        s6 := fun _ => 0
        s7 := fun _ => 0
        s8 := fun _ => 0
        s9 := fun _ => 0 } }

/-- The repaired concrete epoch in the `3 ≤ n`-indexed form used by the
Wave-24 family. -/
noncomputable def concreteEpoch (n : ℕ) (hN : 3 ≤ n) : ConcreteEpochData n :=
  letI : NeZero n := ⟨by omega⟩
  concreteEpochCore n

/-- **C1 is true for the repaired concrete epoch.**  The proof is the
transcript construction: the published correction is the square of the selected
root of the observed hidden square, so the product identity is definitional on
every sample that observes the transcript. -/
theorem concreteEpochCore_globalProductIdentity (N : ℕ) [NeZero N] :
    (concreteEpochCore N).GlobalProductIdentity := by
  intro t x hx
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp ((concreteEpochCore N).good_isSome t.2)
  have ht : t.val = some u := hu
  have hext : (concreteEpochCore N).extract t = u := by
    simp [ConcreteEpochData.extract, ht]
  rw [hext]
  have hx' : concreteSolver N (fun j => x.2 j ^ 2) = some u := by
    rw [← ht]
    simpa [observe, concreteEpochCore] using hx
  obtain ⟨r, hroot⟩ : ∃ r, sqrtUnit N ((fun j => x.2 j ^ 2) ()) = some r :=
    Option.isSome_iff_exists.mp
      (sqrtUnit_isSome_of_sq (N := N) (v := (fun j => x.2 j ^ 2) ())
        (u := x.2 ()) rfl)
  have hroot' : sqrtUnit N (x.2 () ^ 2) = some r := hroot
  simp [concreteSolver, hroot'] at hx'
  obtain rfl : rootTranscript r = u := Option.some.inj hx'
  have hsq : r ^ 2 = x.2 () ^ 2 := sqrtUnit_spec hroot'
  exact rootTranscript_identity r (fun j => x.2 j) hsq

/-- C1 for the `3 ≤ n` family. -/
theorem concreteEpoch_globalProductIdentity (n : ℕ) (hN : 3 ≤ n) :
    (concreteEpoch n hN).GlobalProductIdentity := by
  haveI : NeZero n := ⟨by omega⟩
  exact concreteEpochCore_globalProductIdentity n

/-- Every sample is a successful solver output: the repaired epoch is not
degenerate. -/
theorem concreteEpoch_observe_isSome (n : ℕ) (hN : 3 ≤ n)
    (x : (concreteEpoch n hN).Sample) :
    (observe (concreteEpoch n hN).solver x).isSome := by
  haveI : NeZero n := ⟨by omega⟩
  simp [observe, concreteEpoch, concreteEpochCore, concreteSolver]

/-- The repaired epoch charges strictly positive public work: the root search is
paid for in `S0`. -/
theorem concreteEpoch_pubWork_pos (n : ℕ) (hN : 3 ≤ n)
    (x : (concreteEpoch n hN).Sample) :
    0 < (concreteEpoch n hN).toHardEpochData.pubWork x := by
  haveI : NeZero n := ⟨by omega⟩
  refine ConcreteEpochData.pubWork_pos_of_stageCost_pos (D := concreteEpoch n hN)
    (x := x) (j := Stage.S0) ?_
  show 0 < (concreteEpoch n hN).stageCosts.cost Stage.S0 x
  have hcost : (concreteEpoch n hN).stageCosts.cost Stage.S0 x =
      Fintype.card (ZMod n)ˣ := rfl
  rw [hcost]
  exact Fintype.card_pos_iff.mpr ⟨1⟩

/-! ## Section 3: C1 inputs and the Wave-24 slot -/

/-- The repaired concrete epoch family. -/
noncomputable def concreteEpochFamily : ∀ n, 3 ≤ n → HardEpochData n :=
  fun n hN => (concreteEpoch n hN).toHardEpochData

@[simp] theorem concreteEpochFamily_apply (n : ℕ) (hN : 3 ≤ n) :
    concreteEpochFamily n hN = (concreteEpoch n hN).toHardEpochData := rfl

/-- **C1 inputs at the repaired concrete family.** -/
theorem c1Inputs_concreteEpoch :
    C1Inputs (fun n hN => (concreteEpoch n hN).toHardEpochData) := by
  refine ⟨?_⟩
  intro n hN _
  exact (concreteEpoch n hN).congruenceCheck (concreteEpoch_globalProductIdentity n hN)

/-- The same `C1Inputs` statement at the named family. -/
theorem c1Inputs_concreteEpochFamily : C1Inputs concreteEpochFamily :=
  c1Inputs_concreteEpoch

/-- The Wave-24 `c1Concrete` slot, re-pointed at the repaired concrete epoch.
The original slot is typed at `goodEpochOfLe` and is refuted by
`wave24_c1Concrete_unfillable`; this is the value that replaces it once the
record's family is changed to `concreteEpochFamily`. -/
theorem c1Concrete_concreteEpoch :
    ∀ n (hN : 3 ≤ n), (concreteEpoch n hN).GlobalProductIdentity :=
  concreteEpoch_globalProductIdentity

/-- C1 in the direct square-check form consumed by
`epoch_verified_split_probability`: on every observed sample the hidden product
squares to the published public root. -/
theorem labelProduct_sq_publicRoot_concreteEpoch (n : ℕ) (hN : 3 ≤ n)
    (t : (concreteEpoch n hN).good) (x : (concreteEpoch n hN).Sample)
    (hx : observe (concreteEpoch n hN).solver x = t.val) :
    (labelProduct ((concreteEpoch n hN).extract t).mask (fun _ => 1) x.2) ^ 2 =
      ((concreteEpoch n hN).extract t).publicRoot ^ 2 :=
  (concreteEpoch n hN).labelProduct_sq_publicRoot
    (concreteEpoch_globalProductIdentity n hN) t x hx

/-! ## Section 4: axiom audit -/

#print axioms concreteEpochCore_globalProductIdentity
#print axioms concreteEpoch_globalProductIdentity
#print axioms c1Inputs_concreteEpoch
#print axioms c1Concrete_concreteEpoch
#print axioms labelProduct_sq_publicRoot_concreteEpoch
#print axioms not_forall_globalProductIdentity
#print axioms wave24_c1Concrete_unfillable
#print axioms not_globalProductIdentity_of_trivial_mask

end Cogentic.RandomizedConcreteC1
