import Cogentic.RandomizedEpochAssembly
import Cogentic.RandomizedFieldExtraction

/-!
# Concrete S0–S9 hard-input epoch skeleton

This file closes the *construction-level* part of the vacuity gap recorded in
`research/randomized-gap-audit.md` §1.  A `HardEpochData` is built from an
explicit public solver instead of from a free `data` function:

* `trace` is literally the solver output;
* `good` is exactly the successful solver-output set (the finite universe of
  public values is an explicit field, not a `Fintype` obtained by choice);
* `data` is `PublicMultiFieldTranscript.toTranscriptData` applied to the
  successful solver output;
* `pubWork` is the explicit sum of the ten named blueprint stage costs
  `S0`–`S9`, with a pointwise decomposition theorem and a per-stage lower
  bound.

No `Classical.choose` is used to produce the public transcript, the public
root, or the solver output.  The only `choose` in the data path is the
pre-existing mask-representative selection inside
`PublicMultiFieldTranscript.toTranscriptData`, which is independent of the
solver and does not choose the public root.

The file deliberately proves **no** analytic estimate: there is no C3/C4/C5
success, hit-mass, total-variation, or exponential-work claim.  Concrete stage
cost functions and the sampler laws remain explicit fields of
`ConcreteEpochData`, to be instantiated by the cost and analysis workstreams.
-/

namespace Cogentic.RandomizedConcreteEpoch

open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedHiddenOutputLaw
open scoped BigOperators ENNReal

/-! ## Section 1: The blueprint stages `S0`–`S9` -/

/-- The ten stages `S0`–`S9` of the randomized factoring blueprint.  The
constructors are the canonical stage names; their cost type is
`StageCost N Coins Label` (a `ℕ`-valued function of one sampled epoch input). -/
inductive Stage
  | S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9
  deriving DecidableEq, Repr

instance : Fintype Stage where
  elems := {Stage.S0, Stage.S1, Stage.S2, Stage.S3, Stage.S4,
    Stage.S5, Stage.S6, Stage.S7, Stage.S8, Stage.S9}
  complete := by intro x; cases x <;> simp

namespace Stage

/-- Canonical printed name of a stage. -/
def name : Stage → String
  | S0 => "S0"
  | S1 => "S1"
  | S2 => "S2"
  | S3 => "S3"
  | S4 => "S4"
  | S5 => "S5"
  | S6 => "S6"
  | S7 => "S7"
  | S8 => "S8"
  | S9 => "S9"

/-- Blueprint role of each stage.  These are documentation strings only; the
actual cost of stage `j` is the field `StageCosts.cost j`. -/
def role : Stage → String
  | S0 => "integer parameters and deterministic setup"
  | S1 => "public coins: field pool and multiplier data"
  | S2 => "character probes per field"
  | S3 => "private reduced-class sampler"
  | S4 => "staged private screening (ECM)"
  | S5 => "public descent"
  | S6 => "row records"
  | S7 => "sparse F₂ dependency"
  | S8 => "square root and product check"
  | S9 => "private final gcd"

end Stage

/-- One sampled input of a hard-input epoch on modulus `N`: the public coins
together with the hidden label assignment. -/
abbrev Sample (N : ℕ) (Coins Label : Type) : Type :=
  Coins × (Label → (ZMod N)ˣ)

/-- The type of a single stage cost: `ℕ`-valued public work on one sampled
epoch input. -/
abbrev StageCost (N : ℕ) (Coins Label : Type) : Type :=
  Sample N Coins Label → ℕ

/-- The ten named stage cost functions `S0`–`S9`.  Each field has type
`StageCost N Coins Label`, i.e. `Sample N Coins Label → ℕ`.  Concrete cost
formulae are intentionally left to the instantiation workstreams; this record
makes the public work of the epoch an explicit finite sum rather than an
arbitrary function. -/
structure StageCosts (N : ℕ) (Coins Label : Type) where
  /-- `S0`: integer parameters and deterministic setup. -/
  s0 : StageCost N Coins Label
  /-- `S1`: public coins, field pool and multiplier data. -/
  s1 : StageCost N Coins Label
  /-- `S2`: character probes per field. -/
  s2 : StageCost N Coins Label
  /-- `S3`: private reduced-class sampler. -/
  s3 : StageCost N Coins Label
  /-- `S4`: staged private screening (ECM). -/
  s4 : StageCost N Coins Label
  /-- `S5`: public descent. -/
  s5 : StageCost N Coins Label
  /-- `S6`: row records. -/
  s6 : StageCost N Coins Label
  /-- `S7`: sparse `F₂` dependency. -/
  s7 : StageCost N Coins Label
  /-- `S8`: square root and product check. -/
  s8 : StageCost N Coins Label
  /-- `S9`: private final gcd. -/
  s9 : StageCost N Coins Label

namespace StageCosts

/-- Select the cost function of a named stage. -/
def cost (C : StageCosts N Coins Label) : Stage → StageCost N Coins Label
  | Stage.S0 => C.s0
  | Stage.S1 => C.s1
  | Stage.S2 => C.s2
  | Stage.S3 => C.s3
  | Stage.S4 => C.s4
  | Stage.S5 => C.s5
  | Stage.S6 => C.s6
  | Stage.S7 => C.s7
  | Stage.S8 => C.s8
  | Stage.S9 => C.s9

/-- Total public work charged by the epoch: the explicit sum of the ten named
stage costs. -/
def total (C : StageCosts N Coins Label) (x : Sample N Coins Label) : ℕ :=
  ∑ j : Stage, C.cost j x

/-- The defining sum identity for `StageCosts.total`. -/
theorem total_eq_sum (C : StageCosts N Coins Label) (x : Sample N Coins Label) :
    C.total x = ∑ j : Stage, C.cost j x := rfl

end StageCosts

/-! ## Section 2: Decidable equality on public multi-field transcripts

`HardEpochData` requires `DecidableEq Public`, so the public transcript record
needs decidable equality.  We build it from the computational fields.  The
proof fields are ignored, as they are propositions; this is not a choice of a
transcript or a root. -/

instance instDecidableEqPublicMultiFieldTranscript
    {Label FieldId : Type*} [DecidableEq Label] [Fintype FieldId]
    [DecidableEq FieldId] {N : ℕ} :
    DecidableEq (PublicMultiFieldTranscript Label FieldId N) :=
  fun a b =>
    decidable_of_iff
      (a.mask = b.mask ∧ a.fields = b.fields ∧ a.ratCorr = b.ratCorr ∧
        a.ratRoot = b.ratRoot ∧ (∀ j, a.fieldProd j = b.fieldProd j) ∧
        (∀ j, a.fieldRoot j = b.fieldRoot j))
      (by
        constructor
        · rintro ⟨hmask, hfields, hcorr, hroot, hprod, hroot'⟩
          cases a
          cases b
          simp_all
          exact ⟨funext hprod, funext hroot'⟩
        · intro h
          cases h
          exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩)

/-! ## Section 3: The concrete epoch data -/

/-- A concrete S0–S9 hard-input epoch on modulus `N`, before packaging as
`HardEpochData`.

The public transcript is computed by the explicit solver
`solver : Coins → (Label → (ZMod N)ˣ) → Option (PublicMultiFieldTranscript …)`.
`publicCandidates` is the finite universe of public values the solver may emit;
`solver_mem_candidates` records that every solver output lies in it.  This is
bookkeeping for the finite `good` set, not an assumption about correctness.
`stageCosts` supplies the ten named public-work costs.

No field is a `Classical.choose` of transcript data. -/
structure ConcreteEpochData (N : ℕ) where
  /-- Public coin type. -/
  Coins : Type
  [fintypeCoins : Fintype Coins]
  /-- Hidden label type. -/
  Label : Type
  [fintypeLabel : Fintype Label]
  [decEqLabel : DecidableEq Label]
  /-- Field-identity type for the multi-field extraction. -/
  FieldId : Type
  [fintypeFieldId : Fintype FieldId]
  [decEqFieldId : DecidableEq FieldId]
  /-- Ideal joint law on public coins and hidden labels. -/
  ideal : PMF (Coins × (Label → (ZMod N)ˣ))
  /-- Actual joint law produced by the concrete sampler stack. -/
  actual : PMF (Coins × (Label → (ZMod N)ˣ))
  /-- Explicit public solver, evaluated on a public coin value and the public
  squared-label view `fun j => x.2 j ^ 2` (matching
  `RandomizedHiddenOutputLaw.observe`).  `none` is a rejected transcript. -/
  solver : Coins → (Label → (ZMod N)ˣ) → Option (PublicMultiFieldTranscript Label FieldId N)
  /-- Explicit finite universe of public outputs. -/
  publicCandidates : Finset (Option (PublicMultiFieldTranscript Label FieldId N))
  /-- Every solver output belongs to the explicit public universe. -/
  solver_mem_candidates :
    ∀ x : Coins × (Label → (ZMod N)ˣ), solver x.1 x.2 ∈ publicCandidates
  /-- Conversely, every `some` candidate is actually emitted by the solver on
  some public view.  Together with `solver_mem_candidates` this makes `good`
  exactly the successful solver-output set. -/
  candidates_complete :
    ∀ t ∈ publicCandidates, t.isSome →
      ∃ (c : Coins) (s : Label → (ZMod N)ˣ), solver c s = t
  /-- The ten named public stage costs `S0`–`S9`. -/
  stageCosts : StageCosts N Coins Label

namespace ConcreteEpochData

attribute [instance] fintypeCoins fintypeLabel decEqLabel fintypeFieldId decEqFieldId

/-- Sampled input of a concrete epoch. -/
abbrev Sample (D : ConcreteEpochData N) : Type :=
  D.Coins × (D.Label → (ZMod N)ˣ)

/-- The good set: successful solver outputs inside the explicit public
universe.  This is definitionally a finite filtered set, with no choice. -/
def good (D : ConcreteEpochData N) :
    Finset (Option (PublicMultiFieldTranscript D.Label D.FieldId N)) :=
  D.publicCandidates.filter (fun t => t.isSome)

/-- Membership in `good` is membership in the explicit public universe together
with solver success. -/
theorem mem_good_iff (D : ConcreteEpochData N)
    (t : Option (PublicMultiFieldTranscript D.Label D.FieldId N)) :
    t ∈ D.good ↔ t ∈ D.publicCandidates ∧ t.isSome := by
  exact Finset.mem_filter

/-- `good` is exactly the successful solver-output set: a value is good iff it
is a `some` value emitted by the solver on some public view. -/
theorem mem_good_iff_solver (D : ConcreteEpochData N)
    (t : Option (PublicMultiFieldTranscript D.Label D.FieldId N)) :
    t ∈ D.good ↔
      t.isSome ∧ ∃ (c : D.Coins) (s : D.Label → (ZMod N)ˣ), D.solver c s = t := by
  constructor
  · intro h
    obtain ⟨hc, hs⟩ := (D.mem_good_iff t).mp h
    exact ⟨hs, D.candidates_complete t hc hs⟩
  · rintro ⟨hs, c, s, hcs⟩
    exact (D.mem_good_iff t).mpr ⟨hcs ▸ D.solver_mem_candidates (c, s), hs⟩

/-- Every solver output in the explicit public universe is good, provided it is
a `some` value. -/
theorem some_mem_good_of_solver_eq (D : ConcreteEpochData N)
    {c : D.Coins} {s : D.Label → (ZMod N)ˣ}
    {u : PublicMultiFieldTranscript D.Label D.FieldId N}
    (h : D.solver c s = some u) : some u ∈ D.good := by
  rw [D.mem_good_iff]
  exact ⟨h ▸ D.solver_mem_candidates (c, s), rfl⟩

/-- Every member of `good` is a `some` value, hence carries a transcript. -/
theorem good_isSome (D : ConcreteEpochData N)
    {t : Option (PublicMultiFieldTranscript D.Label D.FieldId N)} (h : t ∈ D.good) :
    t.isSome :=
  (D.mem_good_iff t).mp h |>.2

/-- Package the concrete epoch as the shared `HardEpochData` interface.

`trace` is the solver, `good` is the successful solver-output set, `data` is
`PublicMultiFieldTranscript.toTranscriptData` applied to the solver output, and
`pubWork` is `StageCosts.total`, the explicit sum of `S0`–`S9`. -/
noncomputable def toHardEpochData (D : ConcreteEpochData N) : HardEpochData N where
  Coins := D.Coins
  Label := D.Label
  Public := Option (PublicMultiFieldTranscript D.Label D.FieldId N)
  ideal := D.ideal
  actual := D.actual
  trace := D.solver
  good := D.good
  data := fun t => (Option.get t.val (D.good_isSome t.2)).toTranscriptData
  pubWork := fun x => D.stageCosts.total x

@[simp] theorem toHardEpochData_Coins (D : ConcreteEpochData N) :
    D.toHardEpochData.Coins = D.Coins := rfl

@[simp] theorem toHardEpochData_Label (D : ConcreteEpochData N) :
    D.toHardEpochData.Label = D.Label := rfl

@[simp] theorem toHardEpochData_Public (D : ConcreteEpochData N) :
    D.toHardEpochData.Public =
      Option (PublicMultiFieldTranscript D.Label D.FieldId N) := rfl

@[simp] theorem toHardEpochData_ideal (D : ConcreteEpochData N) :
    D.toHardEpochData.ideal = D.ideal := rfl

@[simp] theorem toHardEpochData_actual (D : ConcreteEpochData N) :
    D.toHardEpochData.actual = D.actual := rfl

@[simp] theorem toHardEpochData_trace (D : ConcreteEpochData N) :
    D.toHardEpochData.trace = D.solver := rfl

@[simp] theorem toHardEpochData_trace_apply (D : ConcreteEpochData N) (c : D.Coins)
    (s : D.Label → (ZMod N)ˣ) :
    D.toHardEpochData.trace c s = D.solver c s := rfl

@[simp] theorem toHardEpochData_good (D : ConcreteEpochData N) :
    D.toHardEpochData.good = D.good := rfl

@[simp] theorem toHardEpochData_data (D : ConcreteEpochData N) (t : D.good) :
    D.toHardEpochData.data t =
      (Option.get t.val (D.good_isSome t.2)).toTranscriptData := rfl

@[simp] theorem toHardEpochData_pubWork (D : ConcreteEpochData N) (x : D.Sample) :
    D.toHardEpochData.pubWork x = D.stageCosts.total x := rfl

/-- The trace of the packaged epoch is the success indicator of the solver:
`observe trace x` lies in `good` exactly when the solver returns `some` on the
public squared-label view. -/
theorem observe_mem_good_iff (D : ConcreteEpochData N) (x : D.Sample) :
    observe D.toHardEpochData.trace x ∈ D.toHardEpochData.good ↔
      (D.solver x.1 (fun j => x.2 j ^ 2)).isSome := by
  rw [toHardEpochData_trace, toHardEpochData_good]
  change observe D.solver x ∈ D.good ↔ (D.solver x.1 (fun j => x.2 j ^ 2)).isSome
  rw [D.mem_good_iff]
  change (D.solver x.1 (fun j => x.2 j ^ 2) ∈ D.publicCandidates ∧
      (D.solver x.1 (fun j => x.2 j ^ 2)).isSome) ↔
    (D.solver x.1 (fun j => x.2 j ^ 2)).isSome
  exact ⟨fun h => h.2,
    fun h => ⟨D.solver_mem_candidates (x.1, fun j => x.2 j ^ 2), h⟩⟩

/-- On a successful solver output, the verifier data is exactly
`PublicMultiFieldTranscript.toTranscriptData` applied to that output.  No
`Classical.choose` of the transcript or of the public root is involved. -/
theorem data_eq_toTranscriptData (D : ConcreteEpochData N) (c : D.Coins)
    (s : D.Label → (ZMod N)ˣ)
    (u : PublicMultiFieldTranscript D.Label D.FieldId N)
    (h : D.solver c s = some u) :
    D.toHardEpochData.data ⟨some u, D.some_mem_good_of_solver_eq h⟩ =
      u.toTranscriptData :=
  rfl

/-! ### Work decomposition -/

/-- Pointwise work decomposition: the packaged public work is the sum of the
ten named stage costs. -/
theorem pubWork_eq_sum (D : ConcreteEpochData N) (x : D.Sample) :
    D.toHardEpochData.pubWork x = ∑ j : Stage, D.stageCosts.cost j x := rfl

/-- Every single named stage is charged by the public work. -/
theorem stageCost_le_pubWork (D : ConcreteEpochData N) (j : Stage) (x : D.Sample) :
    D.stageCosts.cost j x ≤ D.toHardEpochData.pubWork x := by
  rw [D.pubWork_eq_sum]
  exact Finset.single_le_sum (f := fun i : Stage => D.stageCosts.cost i x)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ j)

/-- The public work vanishes exactly when every named stage cost vanishes.
In particular a zero-work epoch cannot be presented with a nonzero stage:
the zero-work oracle would have to claim `S0 = ⋯ = S9 = 0`. -/
theorem pubWork_eq_zero_iff (D : ConcreteEpochData N) (x : D.Sample) :
    D.toHardEpochData.pubWork x = 0 ↔ ∀ j : Stage, D.stageCosts.cost j x = 0 := by
  rw [D.pubWork_eq_sum]
  constructor
  · intro h j
    have hsingle : D.stageCosts.cost j x ≤ 0 := by
      calc
        D.stageCosts.cost j x
            ≤ ∑ i : Stage, D.stageCosts.cost i x :=
              Finset.single_le_sum (f := fun i : Stage => D.stageCosts.cost i x)
                (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
        _ = 0 := h
    omega
  · intro h
    simp only [h, Finset.sum_const_zero]

/-- Positive work of any single stage is charged to the epoch.  This is the
concrete structural obstruction to the zero-work vacuity instance. -/
theorem pubWork_pos_of_stageCost_pos (D : ConcreteEpochData N) {j : Stage}
    {x : D.Sample} (h : 0 < D.stageCosts.cost j x) :
    0 < D.toHardEpochData.pubWork x :=
  lt_of_lt_of_le h (D.stageCost_le_pubWork j x)

end ConcreteEpochData

/-! ## Section 4: A `StageDecomposition`-style record for one epoch -/

/-- A pointwise decomposition of one epoch's public work into the named stages
`S0`–`S9`.  This is the single-epoch form of
`Cogentic.RandomizedEpochWork.StageDecomposition`; it is deliberately stated
without any expected-cost or analytic hypothesis. -/
structure StageDecomposition (N : ℕ) (E : HardEpochData N) where
  /-- Cost charged by each named stage on one sample. -/
  cost : Stage → E.Sample → ℕ
  /-- The public work is exactly the finite sum of the stage costs. -/
  pubWork_eq : ∀ x : E.Sample, E.pubWork x = ∑ j : Stage, cost j x

namespace ConcreteEpochData

/-- The canonical stage decomposition of a concrete epoch. -/
def stageDecomposition (D : ConcreteEpochData N) :
    StageDecomposition N D.toHardEpochData where
  cost := fun j x => D.stageCosts.cost j x
  pubWork_eq := fun x => D.pubWork_eq_sum x

@[simp] theorem stageDecomposition_cost (D : ConcreteEpochData N) (j : Stage)
    (x : D.Sample) :
    D.stageDecomposition.cost j x = D.stageCosts.cost j x := rfl

end ConcreteEpochData

/-! ## Section 5: Axiom audit -/

#print axioms ConcreteEpochData.mem_good_iff
#print axioms ConcreteEpochData.mem_good_iff_solver
#print axioms ConcreteEpochData.observe_mem_good_iff
#print axioms ConcreteEpochData.data_eq_toTranscriptData
#print axioms ConcreteEpochData.pubWork_eq_sum
#print axioms ConcreteEpochData.stageCost_le_pubWork
#print axioms ConcreteEpochData.pubWork_eq_zero_iff
#print axioms ConcreteEpochData.stageDecomposition

end Cogentic.RandomizedConcreteEpoch
