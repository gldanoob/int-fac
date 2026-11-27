import Cogentic.RandomizedConcreteEpoch
import Cogentic.RandomizedEpochAnalyticInputs

/-!
# C1/C2 checks for the concrete S0–S9 epoch (wave 2, W12)

This file closes the C1/C2 part of the concrete-epoch interface started in
`Cogentic.RandomizedConcreteEpoch`.  For a `ConcreteEpochData D` (whose public
data is literally the solver output, with no `Classical.choose` of a transcript
or public root) we prove:

* `ConcreteEpochData.congruenceCheck` — `HardEpochData.CongruenceCheck` for
  `D.toHardEpochData`, from the *global modular product identity* of the public
  multi-field transcript.  Blueprint `research/randomized-epoch-blueprint.md`
  §2 C1, leaf L1: if the good set requires the public check
  `Y² = ∏_{i ∈ I} (observed square i)`, then `(∏ z_i)² = ∏ z_i² = Y²` follows
  from the definition of `observe` (no number theory).  The Lean route is
  `HardEpochData.ofMultiField_congruenceCheck`, which in turn is
  `RandomizedFieldExtraction.labelProduct_sq_eq_assembled_publicRoot`.

* `ConcreteEpochData.hiddenUniform` — `HardEpochData.HiddenUniform` for
  `D.toHardEpochData`, from the *coordinatewise hidden-sign symmetry of the
  ideal law on the mask*.  Blueprint §2 C2, leaves L2–L5: uniform law on a
  square/global sign fiber (L2), the reduced-form root and minimum (L3), the
  non-maximal-order class group and the statement that changing the ideal
  representative changes the root only by a global sign (L4,
  `research/reduced-form-root-signs.md`), and the product/flip law over slots
  with independent public coins (L5, KeyBreak E.5, pp. 91–92).  The Lean route
  is `HardEpochData.ofMultiField_hiddenUniform`.

The two hypotheses are *not* proved here.  They are stated as the explicit
`Prop`-valued predicates `GlobalProductIdentity` and `HiddenSignSymmetry`, with
docstrings pointing at the manuscript, exactly as W12 requires.  Everything
below is a kernel-checked reduction of C1/C2 to those two statements; C3, C4
and C5 are untouched.

No `Classical.choose` is used to obtain the public root: `ConcreteEpochData.extract`
is `Option.get` applied to the solver output together with the proof that a
`good` value is `some`.  The only `choose` in the data path remains the
pre-existing mask-representative selection inside
`PublicMultiFieldTranscript.toTranscriptData`.

The file contains no `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedConcreteEpoch

open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedHiddenLabels
open Cogentic.RandomizedHiddenOutputLaw
open scoped BigOperators ENNReal

variable {N : ℕ}

namespace ConcreteEpochData

/-! ## Section 1: The solver's own transcript and the two paper hypotheses -/

/-- The public multi-field transcript carried by a good solver output.

This is `Option.get` of the solver value at the proof that a `good` candidate is
`some`; it is not a `Classical.choose` of a transcript and it does not select a
public root: the root is the one already stored in the solver output. -/
noncomputable def extract (D : ConcreteEpochData N) :
    D.good → PublicMultiFieldTranscript D.Label D.FieldId N :=
  fun t => Option.get t.val (D.good_isSome t.2)

@[simp] theorem extract_apply (D : ConcreteEpochData N) (t : D.good) :
    D.extract t = Option.get t.val (D.good_isSome t.2) := rfl

/-- The verifier data of the concrete epoch is `toTranscriptData` of the solver's
own transcript.  This is a definitional identity, not an extra hypothesis. -/
@[simp] theorem toHardEpochData_data_eq_extract (D : ConcreteEpochData N) (t : D.good) :
    D.toHardEpochData.data t = (D.extract t).toTranscriptData := rfl

/-- **Global modular product identity of the public multi-field transcript.**

Manuscript: blueprint `research/randomized-epoch-blueprint.md` §2 C1, leaf L1.
For every good solver output `t` and every public sample `x` whose observed
value `observe solver x` is `t`, the product of the observed hidden squares over
the transcript's mask equals the transcript's rational correction times the
product of its per-field products:
`∏_{i ∈ I} (x_i)² = ratCorr * ∏_{j ∈ fields} fieldProd_j`.

This is exactly the `hglobal` hypothesis of
`RandomizedFieldExtraction.multiField_epoch_verified_split_probability_half`,
restricted to the concrete solver.  It is the only number-theoretic input to
C1; it is not proved in this file. -/
def GlobalProductIdentity (D : ConcreteEpochData N) : Prop :=
  ∀ (t : D.good) (x : D.Sample), observe D.solver x = t.val →
    (∏ i ∈ (D.extract t).mask, (x.2 i) ^ 2) =
      (D.extract t).ratCorr * ∏ j ∈ (D.extract t).fields, (D.extract t).fieldProd j

/-- **Coordinatewise hidden-sign symmetry of the ideal law on the mask.**

Manuscript: blueprint `research/randomized-epoch-blueprint.md` §2 C2, leaves
L2–L5 (L2 square/global sign fibers, L3 reduced-form roots, L4 the
non-maximal-order class group and the global-sign representative change of
`research/reduced-form-root-signs.md`, L5 the product/flip law, KeyBreak E.5
pp. 91–92).

For every good solver output `t`, any two public samples `x`, `y` with the same
public coins, whose hidden coordinates agree outside some mask element `i` and
whose squares agree at `i`, have equal ideal mass.  This is exactly the
`huniform` hypothesis of
`RandomizedEpochSuccess.epoch_verified_split_probability` (and of
`RandomizedFieldExtraction.multiField_epoch_verified_split_probability_half`),
restricted to the concrete solver; it is the only number-theoretic input to C2.
It is not proved in this file. -/
def HiddenSignSymmetry (D : ConcreteEpochData N) : Prop :=
  ∀ (t : D.good) (x y : D.Sample), observe D.solver x = t.val → x.1 = y.1 →
    ∀ i ∈ (D.extract t).mask, (x.2 i) ^ 2 = (y.2 i) ^ 2 →
    (∀ j, j ≠ i → x.2 j = y.2 j) → D.ideal x = D.ideal y

/-! ## Section 2: Adapter to `HardEpochData.ofMultiField`

`ConcreteEpochData.toHardEpochData` packages the solver output directly.  The
shared constructor `HardEpochData.ofMultiField` packages the same data from an
explicit extractor; the two agree definitionally, which lets us reuse the
already-proved C1/C2 discharges `ofMultiField_congruenceCheck` and
`ofMultiField_hiddenUniform` instead of duplicating their proofs. -/

/-- The concrete epoch is the `ofMultiField` constructor applied to the solver's
own transcript.  This is the local adapter required by W12. -/
theorem toHardEpochData_eq_ofMultiField (D : ConcreteEpochData N) :
    D.toHardEpochData =
      HardEpochData.ofMultiField D.ideal D.actual D.solver D.good
        D.extract (fun x => D.stageCosts.total x) := rfl

/-! ## Section 3: C1 — `CongruenceCheck` -/

/-- C1 for the concrete epoch: the global product identity discharges
`HardEpochData.CongruenceCheck` via
`HardEpochData.ofMultiField_congruenceCheck`, which is
`labelProduct_sq_eq_assembled_publicRoot` applied to the transcript's own roots.

The public root is the transcript's `publicRoot = ratRoot * ∏ fieldRoot j`,
already present in the solver output; no root is chosen. -/
theorem congruenceCheck (D : ConcreteEpochData N)
    (hglobal : D.GlobalProductIdentity) :
    D.toHardEpochData.CongruenceCheck := by
  rw [D.toHardEpochData_eq_ofMultiField]
  exact HardEpochData.ofMultiField_congruenceCheck D.ideal D.actual D.solver D.good
    D.extract (fun x => D.stageCosts.total x) hglobal

/-- Direct form of C1, by `labelProduct_sq_eq_assembled_publicRoot`: on every
good solver output the hidden label product squares to the assembled public
root.  This is the same statement as `congruenceCheck` with the `ofMultiField`
wrapper unfolded, recorded because it is the exact shape consumed by
`epoch_verified_split_probability`. -/
theorem labelProduct_sq_publicRoot (D : ConcreteEpochData N)
    (hglobal : D.GlobalProductIdentity) (t : D.good) (x : D.Sample)
    (hx : observe D.solver x = t.val) :
    (labelProduct (D.extract t).mask (fun _ => 1) x.2) ^ 2 =
      (D.extract t).publicRoot ^ 2 :=
  labelProduct_sq_eq_assembled_publicRoot (D.extract t).mask (D.extract t).fields
    x.2 (fun i => x.2 i ^ 2) (D.extract t).ratCorr (D.extract t).ratRoot
    (D.extract t).fieldProd (D.extract t).fieldRoot (fun _ _ => rfl)
    (D.extract t).ratRoot_sq (D.extract t).fieldRoot_sq (hglobal t x hx)

/-! ## Section 4: C2 — `HiddenUniform` -/

/-- C2 for the concrete epoch: coordinatewise hidden-sign symmetry on every mask
element discharges `HardEpochData.HiddenUniform` via
`HardEpochData.ofMultiField_hiddenUniform`.

`ofMultiField_hiddenUniform` instantiates the symmetry at the mask element
selected by `PublicMultiFieldTranscript.toTranscriptData` (the representative
`mask_nonempty.choose`), which is why the hypothesis is stated for *every*
`i ∈ mask` rather than for a fixed index. -/
theorem hiddenUniform (D : ConcreteEpochData N)
    (huniform : D.HiddenSignSymmetry) :
    D.toHardEpochData.HiddenUniform := by
  rw [D.toHardEpochData_eq_ofMultiField]
  exact HardEpochData.ofMultiField_hiddenUniform D.ideal D.actual D.solver D.good
    D.extract (fun x => D.stageCosts.total x) huniform

/-- C2 in the exact hypothesis shape of
`RandomizedEpochSuccess.epoch_verified_split_probability`: after unfolding
`HiddenUniform`, the concrete epoch satisfies the conditional flip-invariance
condition at its verifier's `privateIndex`. -/
theorem hiddenUniform_epochVerifiedSplit (D : ConcreteEpochData N)
    (huniform : D.HiddenSignSymmetry) :
    ∀ (t : D.good) (x y : D.Sample), observe D.solver x = t.val → x.1 = y.1 →
      (x.2 (D.toHardEpochData.data t).privateIndex) ^ 2 =
        (y.2 (D.toHardEpochData.data t).privateIndex) ^ 2 →
      (∀ j, j ≠ (D.toHardEpochData.data t).privateIndex → x.2 j = y.2 j) →
      D.ideal x = D.ideal y :=
  D.hiddenUniform huniform

end ConcreteEpochData

namespace ConcreteEpochChecks

/-! ## Section 5: Bundling into `RandomizedEpochAnalyticInputs.C1Inputs`/`C2Inputs` -/

/-- The `n`-indexed epoch family obtained from a family of concrete epochs, with
`HardEpochData` supplied by `ConcreteEpochData.toHardEpochData`. -/
noncomputable def concreteEpochFamily
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n) : ∀ n, 3 ≤ n → HardEpochData n :=
  fun n hN => (D n hN).toHardEpochData

@[simp] theorem concreteEpochFamily_apply
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n) (n : ℕ) (hN : 3 ≤ n) :
    concreteEpochFamily D n hN = (D n hN).toHardEpochData := rfl

/-- **C1 inputs for a concrete epoch family**: the global product identity on
every hard input gives `C1Inputs` at the packaged family. -/
theorem c1Inputs_concreteEpoch
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (hglobal : ∀ n (hN : 3 ≤ n), (D n hN).GlobalProductIdentity) :
    C1Inputs (concreteEpochFamily D) where
  congruenceCheck := fun n hN _ => (D n hN).congruenceCheck (hglobal n hN)

/-- **C2 inputs for a concrete epoch family**: coordinatewise hidden-sign
symmetry on every hard input gives `C2Inputs` at the packaged family. -/
theorem c2Inputs_concreteEpoch
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (huniform : ∀ n (hN : 3 ≤ n), (D n hN).HiddenSignSymmetry) :
    C2Inputs (concreteEpochFamily D) where
  hiddenUniform := fun n hN _ => (D n hN).hiddenUniform (huniform n hN)

/-- **W12 bundle.**  For a family of concrete epochs, the global product
identity and the hidden-sign symmetry discharge both C1 and C2 of
`RandomizedEpochAnalyticInputs` at `concreteEpochFamily D`.  No analytic
estimate (C3, C4, C5) is asserted. -/
theorem c1_and_c2_inputs_concreteEpoch
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (hglobal : ∀ n (hN : 3 ≤ n), (D n hN).GlobalProductIdentity)
    (huniform : ∀ n (hN : 3 ≤ n), (D n hN).HiddenSignSymmetry) :
    C1Inputs (concreteEpochFamily D) ∧ C2Inputs (concreteEpochFamily D) :=
  ⟨c1Inputs_concreteEpoch D hglobal, c2Inputs_concreteEpoch D huniform⟩

/-- **W12 bundle, assembled form.**  With C3, C4 and C5 supplied as explicit
inputs at the concrete family, the two discharged checks complete
`RandomizedEpochAnalyticInputs.EpochAnalyticInputs` for the concrete epoch.  This
shows that C1/C2 are no longer part of the analytic gap for the concrete epoch. -/
noncomputable def epochAnalyticInputs_concreteEpoch
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (hglobal : ∀ n (hN : 3 ≤ n), (D n hN).GlobalProductIdentity)
    (huniform : ∀ n (hN : 3 ≤ n), (D n hN).HiddenSignSymmetry)
    {C : ℝ}
    (c3 : C3Inputs (concreteEpochFamily D))
    (c4 : C4Inputs (concreteEpochFamily D) C)
    (c5 : C5Inputs (concreteEpochFamily D)) :
    EpochAnalyticInputs (concreteEpochFamily D) C where
  c1 := c1Inputs_concreteEpoch D hglobal
  c2 := c2Inputs_concreteEpoch D huniform
  c3 := c3
  c4 := c4
  c5 := c5

/-- Corollary of the assembled bundle: C1/C2 for the concrete epoch feed the
existing reduction `hardEpochAsymptoticBound_of_analyticInputs`, so the
asymptotic bound for the concrete family follows from C3/C4/C5 together with
the two explicit paper hypotheses. -/
theorem hardEpochAsymptoticBound_of_concreteEpoch
    (D : ∀ n, 3 ≤ n → ConcreteEpochData n)
    (hglobal : ∀ n (hN : 3 ≤ n), (D n hN).GlobalProductIdentity)
    (huniform : ∀ n (hN : 3 ≤ n), (D n hN).HiddenSignSymmetry)
    {C : ℝ}
    (c3 : C3Inputs (concreteEpochFamily D))
    (c4 : C4Inputs (concreteEpochFamily D) C)
    (c5 : C5Inputs (concreteEpochFamily D)) :
    HardEpochAsymptoticBound (concreteEpochFamily D) C :=
  hardEpochAsymptoticBound_of_analyticInputs _
    C (epochAnalyticInputs_concreteEpoch D hglobal huniform c3 c4 c5)

/-! ## Section 6: Axiom audit -/

#print axioms ConcreteEpochData.congruenceCheck
#print axioms ConcreteEpochData.labelProduct_sq_publicRoot
#print axioms ConcreteEpochData.hiddenUniform
#print axioms ConcreteEpochData.hiddenUniform_epochVerifiedSplit
#print axioms ConcreteEpochChecks.c1Inputs_concreteEpoch
#print axioms ConcreteEpochChecks.c2Inputs_concreteEpoch
#print axioms ConcreteEpochChecks.c1_and_c2_inputs_concreteEpoch
#print axioms ConcreteEpochChecks.epochAnalyticInputs_concreteEpoch
#print axioms ConcreteEpochChecks.hardEpochAsymptoticBound_of_concreteEpoch

end ConcreteEpochChecks

end Cogentic.RandomizedConcreteEpoch
