import Cogentic.RandomizedEpochVacuity

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# A costed hard-input epoch interface

`RandomizedEpochVacuity.oracleEpoch_bound` shows that `HardEpochAsymptoticBound`
is vacuous as an algorithmic statement: the transcript data
`data : good → TranscriptData Label N` is an arbitrary function of the public
transcript, and the hidden label assignment is a free coordinate of the law
`E.actual`, so a zero-work epoch can meet the bound by using
`Classical.choose`.

This file repairs the interface in two layers.

## The cost model

A program is a finite decision tree over an input type.  Each internal node asks
one Boolean query of the input and costs one unit; leaves return the output for
free.  The cost is computed from the program's syntax, so it cannot be
self-reported.  The semantic property used below is
`Program.run_eq_of_cost_eq_zero`: a program whose cost is zero on two inputs
produces the same output on them (because a program of zero cost on any input
must be a leaf).

## The costed interface

A `CostedRealization` of a bare epoch `E` contains:

* a seed law and a `samplerProgram` generating the hidden label assignment from
  the seed, with `E.actual` *equal* to the pushforward of the seed law through
  the sampler (`actual_eq`); the seed bundles the public coins together with
  any private sampler randomness, and `coinsOf` exposes the public part;
* a `program` computing the transcript data from the public transcript;
* explicitly declared `helperWork`;
* `pubWork_eq`, which says that on every generated sample the charged work is
  exactly sampler cost plus data-program cost plus helper work.

Thus a costed epoch must exhibit a cheap sampler *and* a cheap data extractor;
the asymptotic hypothesis now asserts the existence of those programs with the
required work bound.  This is the actual algorithmic content that the old
interface was missing.

## What the model does and does not prove

The decision-tree model is a soundness device, not a computational lower bound.
It proves that zero work forces constant programs, which is enough to reject
*zero-work* realizations of the oracle epoch
(`oracleEpoch_no_costedRealization`).  It does not prove that no cheap
subexponential sampler/root extractor exists: a modified oracle declaring
`O(log n)` work would still be below `exp (δ * scale n)`.  That is a genuine
complexity assumption.  The residual assumption is stated explicitly as
`OracleRootExtractionLowerBound` for oracle-shaped epochs with arbitrary
positive work, and `not_costedHardEpochAsymptoticBound_zero_of_oracle` shows
that it is exactly what is needed to exclude such a family at exponent `C = 0`.
-/

namespace Cogentic.RandomizedCostedEpoch

open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochAssembly.Vacuity
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSerializedDriver
open Filter Real
open scoped ENNReal

/-! ## 1. A small deterministic cost model -/

/-- A deterministic costed program from `α` to `β`, represented as a finite
decision tree.  Each internal node performs one Boolean query of the input and
costs one unit; leaves return the output and cost nothing. -/
inductive Program (α β : Type) where
  /-- Return a fixed value. -/
  | leaf (b : β)
  /-- Query the input once; the query costs one unit and chooses a branch. -/
  | query (p : α → Bool) (yes no : Program α β)

namespace Program

variable {α β : Type}

/-- Output of a program on an input. -/
def run : Program α β → α → β
  | leaf b, _ => b
  | query p yes no, a => if p a then run yes a else run no a

/-- Number of queries executed by a program on an input: its cost. -/
def cost : Program α β → α → ℕ
  | leaf _, _ => 0
  | query p yes no, a => if p a then cost yes a + 1 else cost no a + 1

@[simp]
theorem run_leaf (b : β) (a : α) : (leaf b).run a = b := rfl

@[simp]
theorem cost_leaf (b : β) (a : α) : (leaf b).cost a = 0 := rfl

/-- A query always costs at least one unit. -/
theorem one_le_cost_query (p : α → Bool) (yes no : Program α β) (a : α) :
    1 ≤ (query p yes no).cost a := by
  simp only [cost]
  split_ifs <;> omega

/-- **Semantic condition on the cost model.**  A program has cost zero on an
input only if it is a leaf.  This is the fact that makes the costed interface
non-vacuous: there is no free computation of a genuinely input-dependent
transcript datum or hidden label assignment. -/
theorem eq_leaf_of_cost_eq_zero (prog : Program α β) (a : α)
    (h : prog.cost a = 0) : prog = leaf (prog.run a) := by
  cases prog with
  | leaf b => rfl
  | query p yes no =>
      exfalso
      have hpos := one_le_cost_query p yes no a
      omega

/-- **Semantic condition on the cost model (two-input form).**  A program whose
cost is zero on two inputs produces the same output on them, because on each of
them it must be a leaf. -/
theorem run_eq_of_cost_eq_zero (prog : Program α β) (a b : α)
    (ha : prog.cost a = 0) (hb : prog.cost b = 0) : prog.run a = prog.run b := by
  cases prog with
  | leaf c => rfl
  | query p yes no =>
      exfalso
      have hpos := one_le_cost_query p yes no a
      omega

end Program

/-! ## 2. Costed realization of a bare epoch, including sampling -/

/-- A costed realization of a bare epoch `E`.  The hidden label assignment is
generated by `samplerProgram` from a seed, and the actual law is exactly the
pushforward of the seed law through the sampler.  The transcript data is
computed by `program` from the public transcript.  The charged public work is
exactly sampler cost plus data-program cost plus explicitly declared helper
work.  None of these components is self-reported: both programs' costs are
computed from their syntax, and the helper cost is a separate visible field. -/
structure CostedRealization {N : ℕ} (E : HardEpochData N) where
  /-- Seed space carrying all randomness consumed by the epoch's sampler. -/
  Seed : Type
  [fintypeSeed : Fintype Seed]
  /-- Law of the sampler seed. -/
  seedLaw : PMF Seed
  /-- Public coins produced by a seed. -/
  coinsOf : Seed → E.Coins
  /-- Program generating the hidden label assignment from the seed. -/
  samplerProgram : Program Seed (E.Label → (ZMod N)ˣ)
  /-- The actual law is exactly the sampler's pushforward. -/
  actual_eq : E.actual = seedLaw.map (fun s => (coinsOf s, samplerProgram.run s))
  /-- Program computing the transcript data from the public transcript. -/
  program : Program E.Public (TranscriptData E.Label N)
  /-- The program's output is the epoch's declared transcript data. -/
  data_eq : ∀ t : E.good, E.data t = program.run t.val
  /-- Additional declared work (setup, linear algebra, ...). -/
  helperWork : E.Sample → ℕ
  /-- Charged work on every generated sample is exactly sampler cost plus
  data-program cost plus helper work. -/
  pubWork_eq : ∀ s : Seed,
    E.pubWork (coinsOf s, samplerProgram.run s) =
      samplerProgram.cost s +
        program.cost (observe E.trace (coinsOf s, samplerProgram.run s)) +
        helperWork (coinsOf s, samplerProgram.run s)

namespace CostedRealization

attribute [instance] fintypeSeed

end CostedRealization

/-- A hard-input epoch together with a costed realization of its hidden-sample
generation, its transcript data, and its public work. -/
structure CostedHardEpochData (N : ℕ) where
  /-- The underlying bare epoch. -/
  base : HardEpochData N
  /-- The costed realization tying sampling, data, and work to programs. -/
  costed : CostedRealization base

namespace CostedHardEpochData

variable {N : ℕ}

/-- Forget the cost structure. -/
def toHardEpochData (E : CostedHardEpochData N) : HardEpochData N := E.base

/-- A seed for the hidden-sample sampler. -/
abbrev Seed (E : CostedHardEpochData N) : Type := E.costed.Seed

/-- The seed law. -/
def seedLaw (E : CostedHardEpochData N) : PMF E.Seed := E.costed.seedLaw

/-- Public coins produced by a seed. -/
def coinsOf (E : CostedHardEpochData N) : E.Seed → E.base.Coins := E.costed.coinsOf

/-- The program generating the hidden label assignment. -/
def samplerProgram (E : CostedHardEpochData N) :
    Program E.Seed (E.base.Label → (ZMod N)ˣ) :=
  E.costed.samplerProgram

/-- The seed-to-sample map implemented by the epoch. -/
def generated (E : CostedHardEpochData N) (s : E.Seed) : E.base.Sample :=
  (E.coinsOf s, E.samplerProgram.run s)

/-- The program computing the transcript data. -/
def program (E : CostedHardEpochData N) :
    Program E.base.Public (TranscriptData E.base.Label N) :=
  E.costed.program

/-- The declared helper work. -/
def helperWork (E : CostedHardEpochData N) : E.base.Sample → ℕ :=
  E.costed.helperWork

/-- The part of the public work paid for by the data-computing program on a
given sample. -/
def programWork (E : CostedHardEpochData N) (x : E.base.Sample) : ℕ :=
  E.program.cost (observe E.base.trace x)

/-- The actual law is the sampler's pushforward. -/
theorem actual_eq (E : CostedHardEpochData N) :
    E.base.actual = E.seedLaw.map E.generated :=
  E.costed.actual_eq

/-- Public work is exactly sampler cost plus data-program cost plus helper
work on every generated sample. -/
theorem pubWork_eq (E : CostedHardEpochData N) (s : E.Seed) :
    E.base.pubWork (E.generated s) =
      E.samplerProgram.cost s + E.programWork (E.generated s) + E.helperWork (E.generated s) :=
  E.costed.pubWork_eq s

/-- The charged work dominates the sampler cost. -/
theorem sampler_cost_le_pubWork (E : CostedHardEpochData N) (s : E.Seed) :
    E.samplerProgram.cost s ≤ E.base.pubWork (E.generated s) := by
  rw [E.pubWork_eq s]
  omega

/-- The charged work dominates the data-program cost. -/
theorem program_cost_le_pubWork (E : CostedHardEpochData N) (s : E.Seed) :
    E.programWork (E.generated s) ≤ E.base.pubWork (E.generated s) := by
  rw [E.pubWork_eq s]
  omega

/-- Expected public work decomposes into expected sampler cost, expected
data-program cost, and expected helper cost, all taken over the seed law.  In
particular the bound on `pubWork` cannot hide sampling or extraction work that
is absent from the two programs or from the declared helper cost. -/
theorem mean_pubWork_le_of_parts (E : CostedHardEpochData N) {Wsample Wprog Whelp : ℝ}
    (hWsample : 0 ≤ Wsample) (hWprog : 0 ≤ Wprog) (hWhelp : 0 ≤ Whelp)
    (hsample : mean E.seedLaw (fun s => (E.samplerProgram.cost s : ℝ≥0∞)) ≤
      ENNReal.ofReal Wsample)
    (hprog : mean E.seedLaw (fun s => (E.programWork (E.generated s) : ℝ≥0∞)) ≤
      ENNReal.ofReal Wprog)
    (hhelp : mean E.seedLaw (fun s => (E.helperWork (E.generated s) : ℝ≥0∞)) ≤
      ENNReal.ofReal Whelp) :
    mean E.base.actual (fun x => (E.base.pubWork x : ℝ≥0∞)) ≤
      ENNReal.ofReal (Wsample + Wprog + Whelp) := by
  rw [E.actual_eq, mean_map]
  have hpt : ∀ s : E.Seed,
      (E.base.pubWork (E.generated s) : ℝ≥0∞) =
        (E.samplerProgram.cost s : ℝ≥0∞) +
          (E.programWork (E.generated s) : ℝ≥0∞) +
            (E.helperWork (E.generated s) : ℝ≥0∞) := by
    intro s
    rw [E.pubWork_eq s]
    norm_cast
  simp_rw [hpt]
  rw [mean_add, mean_add]
  rw [show Wsample + Wprog + Whelp = (Wsample + Wprog) + Whelp by ring]
  rw [ENNReal.ofReal_add (add_nonneg hWsample hWprog) hWhelp,
    ENNReal.ofReal_add hWsample hWprog]
  exact add_le_add (add_le_add hsample hprog) hhelp

/-- A bound on the expected public work is in particular a bound on the expected
*sampler* work.  This is the quantitative form of the statement that the hidden
sample is no longer free: the costed asymptotic hypothesis controls the program
that generates the hidden label assignment. -/
theorem mean_samplerCost_le_of_mean_pubWork (E : CostedHardEpochData N) {W : ℝ}
    (hW : mean E.base.actual (fun x => (E.base.pubWork x : ℝ≥0∞)) ≤ ENNReal.ofReal W) :
    mean E.seedLaw (fun s => (E.samplerProgram.cost s : ℝ≥0∞)) ≤ ENNReal.ofReal W := by
  rw [E.actual_eq, mean_map] at hW
  refine le_trans ?_ hW
  unfold mean
  exact ENNReal.tsum_le_tsum fun s => by
    have h : (E.samplerProgram.cost s : ℝ≥0∞) ≤
        (E.base.pubWork (E.generated s) : ℝ≥0∞) := by
      exact_mod_cast E.sampler_cost_le_pubWork s
    exact mul_le_mul_right h (E.seedLaw s)

end CostedHardEpochData

/-- A family of costed epochs, viewed as bare epochs by forgetting the cost
structure. -/
def toHardFamily (E : ∀ n, 3 ≤ n → CostedHardEpochData n) :
    ∀ n, 3 ≤ n → HardEpochData n :=
  fun n hN => (E n hN).toHardEpochData

/-! ## 3. The costed asymptotic bound and its end-to-end theorem -/

/-- The costed asymptotic bound.  It is the existing `HardEpochAsymptoticBound`
applied to the underlying bare epoch; the added content is that only epochs
admitting a `CostedRealization` can be passed.  Such a realization must exhibit
both a sampler program generating the hidden labels and a program extracting the
transcript data, with `pubWork` dominating the costs of both.  This is the
algorithmic content missing from the old interface. -/
def CostedHardEpochAsymptoticBound
    (E : ∀ n, 3 ≤ n → CostedHardEpochData n) (C : ℝ) : Prop :=
  HardEpochAsymptoticBound (toHardFamily E) C

/-- The costed bound is definitionally the existing bound on the underlying bare
family. -/
theorem costedHardEpochAsymptoticBound_iff
    (E : ∀ n, 3 ≤ n → CostedHardEpochData n) (C : ℝ) :
    CostedHardEpochAsymptoticBound E C ↔ HardEpochAsymptoticBound (toHardFamily E) C :=
  Iff.rfl

/-- Costed analogue of `assembled_epoch_ratio_eventually`: the costed bound gives
the work-to-hit ratio premise for the underlying bare family.  This is a direct
instantiation of the existing assembly theorem. -/
theorem costed_assembled_epoch_ratio_eventually
    (E : ∀ n, 3 ≤ n → CostedHardEpochData n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : CostedHardEpochAsymptoticBound E C) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epochLaw (toHardFamily E) n)
            (fun a => ((epochAttempt (toHardFamily E) n a).2 + 1 : ℕ)) + 1 ≤
              ENNReal.ofReal W ∧
          S ≤ (((epochLaw (toHardFamily E) n).map
            (epochAttempt (toHardFamily E) n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n) :=
  assembled_epoch_ratio_eventually (toHardFamily E) hC hbound

/-- Costed analogue of `serialized_assembled_epoch_from_critical_line`: under the
critical-line hypothesis, any costed epoch family meeting the costed bound at
exponent `C` yields a certified serialized factoring algorithm with expected
serialized bit cost eventually `≤ exp ((C + ε) * scale n)`.  The proof reuses
the existing assembly theorem rather than reproving it. -/
theorem serialized_costed_assembled_epoch_from_critical_line
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ n, 3 ≤ n → CostedHardEpochData n) {C : ℝ}, 0 ≤ C →
      CostedHardEpochAsymptoticBound E C →
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (epochHard (epochLaw (toHardFamily E)) (epochAttempt (toHardFamily E)))
          n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (epochHard (epochLaw (toHardFamily E)) (epochAttempt (toHardFamily E)))
          n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ := serialized_assembled_epoch_from_critical_line line
  exact ⟨k, sound, fun E C hC hbound => hmain (toHardFamily E) hC hbound⟩

/-! ## 4. Non-vacuity: zero work forces constant sampler and data -/

/-- **Zero work forces a constant sampler.**  If a costed realization charges
zero public work everywhere, then every seed's sampler cost is zero, so by the
model's zero-cost/constant-program property the sampler output is the same for
all seeds. -/
theorem sampler_run_const_of_zero_pubWork {N : ℕ} {E : HardEpochData N}
    (R : CostedRealization E)
    (hzero : ∀ x : E.Sample, E.pubWork x = 0) :
    ∀ s s' : R.Seed, R.samplerProgram.run s = R.samplerProgram.run s' := by
  intro s s'
  have hcs : R.samplerProgram.cost s = 0 := by
    have hpub := R.pubWork_eq s
    rw [hzero (R.coinsOf s, R.samplerProgram.run s)] at hpub
    omega
  have hcs' : R.samplerProgram.cost s' = 0 := by
    have hpub := R.pubWork_eq s'
    rw [hzero (R.coinsOf s', R.samplerProgram.run s')] at hpub
    omega
  exact Program.run_eq_of_cost_eq_zero R.samplerProgram s s' hcs hcs'

/-- If the sampler is constant, then any actual sample whose label assignment
differs from the constant output has probability zero. -/
theorem actual_apply_eq_zero_of_seed_ne {N : ℕ} {E : HardEpochData N}
    (R : CostedRealization E)
    (hconst : ∀ s s' : R.Seed, R.samplerProgram.run s = R.samplerProgram.run s')
    (s0 : R.Seed) {x : E.Sample} (hx : x.2 ≠ R.samplerProgram.run s0) :
    E.actual x = 0 := by
  rw [R.actual_eq, PMF.map_apply, ENNReal.tsum_eq_zero]
  intro s
  by_cases h : x = (R.coinsOf s, R.samplerProgram.run s)
  · exfalso
    apply hx
    have hs := hconst s s0
    have hsecond := congrArg Prod.snd h
    rw [hsecond, hs]
  · simp [h]

/-- **General data criterion.**  If a bare epoch charges zero public work
everywhere and every good transcript is generated by some seed, then in every
costed realization the transcript data is constant on good transcripts.  Thus
nonconstant data also forces positive work. -/
theorem data_constant_of_zero_pubWork {N : ℕ} (E : HardEpochData N)
    (R : CostedRealization E)
    (hzero : ∀ x : E.Sample, E.pubWork x = 0)
    (hsurj : ∀ t : E.good, ∃ s : R.Seed,
      observe E.trace (R.coinsOf s, R.samplerProgram.run s) = t.val) :
    ∀ t1 t2 : E.good, E.data t1 = E.data t2 := by
  intro t1 t2
  obtain ⟨s1, hs1⟩ := hsurj t1
  obtain ⟨s2, hs2⟩ := hsurj t2
  have hc1 : R.program.cost t1.val = 0 := by
    have hpub := R.pubWork_eq s1
    rw [hzero (R.coinsOf s1, R.samplerProgram.run s1), hs1] at hpub
    omega
  have hc2 : R.program.cost t2.val = 0 := by
    have hpub := R.pubWork_eq s2
    rw [hzero (R.coinsOf s2, R.samplerProgram.run s2), hs2] at hpub
    omega
  calc
    E.data t1 = R.program.run t1.val := R.data_eq t1
    _ = R.program.run t2.val :=
        Program.run_eq_of_cost_eq_zero R.program t1.val t2.val hc1 hc2
    _ = E.data t2 := (R.data_eq t2).symm

/-- Contrapositive form of `data_constant_of_zero_pubWork`: nonconstant
transcript data forces positive charged public work somewhere. -/
theorem exists_pos_pubWork_of_data_ne {N : ℕ} (E : HardEpochData N)
    (R : CostedRealization E)
    (hsurj : ∀ t : E.good, ∃ s : R.Seed,
      observe E.trace (R.coinsOf s, R.samplerProgram.run s) = t.val)
    {t1 t2 : E.good} (hne : E.data t1 ≠ E.data t2) :
    ∃ x : E.Sample, 0 < E.pubWork x := by
  by_contra h
  have hle : ∀ x : E.Sample, E.pubWork x ≤ 0 :=
    fun x => le_of_not_gt fun hx => h ⟨x, hx⟩
  exact hne (data_constant_of_zero_pubWork E R
    (fun x => Nat.eq_zero_of_le_zero (hle x)) hsurj t1 t2)

/-! ## 5. The oracle epoch has no costed realization -/

/-- `2` is not `1` in `ZMod N` for `N ≥ 3`. -/
theorem zmod_two_ne_one {N : ℕ} (hN : 3 ≤ N) : (((2 : ℕ) : ZMod N)) ≠ (1 : ZMod N) := by
  intro h
  have h2 : (((2 : ℕ) : ZMod N)).val = 2 := ZMod.val_natCast_of_lt (by omega)
  have h1 : (1 : ZMod N).val = 1 := ZMod.val_one'' (by omega)
  rw [h] at h2
  rw [h1] at h2
  omega

/-- There is a unit of `ZMod N` other than `1` when `N` is odd and `N ≥ 3`. -/
theorem exists_unit_ne_one {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N) :
    ∃ u : (ZMod N)ˣ, u ≠ 1 := by
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  refine ⟨ZMod.unitOfCoprime 2 hcop, ?_⟩
  intro h
  have hcoe : ((ZMod.unitOfCoprime 2 hcop : (ZMod N)ˣ) : ZMod N) = (2 : ZMod N) :=
    ZMod.coe_unitOfCoprime 2 hcop
  have hcoe1 : ((1 : (ZMod N)ˣ) : ZMod N) = (1 : ZMod N) := rfl
  have h21 : (((2 : ℕ) : ZMod N)) = (1 : ZMod N) := by
    rw [← ZMod.coe_unitOfCoprime 2 hcop, h, hcoe1]
  exact zmod_two_ne_one hN h21

/-- The oracle epoch's actual law gives positive mass to every sample. -/
theorem oracleEpoch_actual_ne_zero {N : ℕ} (hN : 3 ≤ N)
    (x : (oracleEpoch N hN).Sample) :
    (oracleEpoch N hN).actual x ≠ 0 := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Nonempty ((oracleEpoch N hN).Sample) :=
    ⟨((), fun _ => (1 : (ZMod N)ˣ))⟩
  have hact : (oracleEpoch N hN).actual x =
      (Fintype.card ((oracleEpoch N hN).Sample) : ℝ≥0∞)⁻¹ :=
    PMF.uniformOfFintype_apply x
  rw [hact]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- The public transcript of a good oracle transcript, viewed explicitly as a
unit.  This is a `def` so that its type is `(ZMod N)ˣ` rather than the
non-reduced projection `(oracleEpoch N hN).Public`. -/
def oraclePublicVal {N : ℕ} (hN : 3 ≤ N) (t : (oracleEpoch N hN).good) : (ZMod N)ˣ := t.val

/-- The public root chosen by the oracle epoch squares back to the public
transcript.  This is the `Classical.choose_spec` fact used by the vacuity file. -/
theorem oracleEpoch_publicRoot_sq {N : ℕ} (hN : 3 ≤ N)
    (t : (oracleEpoch N hN).good) :
    ((oracleEpoch N hN).data t).publicRoot ^ 2 = oraclePublicVal hN t := by
  have hspec := (Classical.choose_spec (Finset.mem_image.mp t.2)).2
  simpa [oracleEpoch, oraclePublicVal] using hspec

/-- **The oracle's data is nonconstant.**  On an odd modulus `N ≥ 5` there are
two good transcripts, `1` and the square of a unit congruent to `2` (which is a
unit because `N` is odd), whose chosen roots differ: the data field includes
`publicRoot`, and equal roots would square to equal transcripts. -/
theorem oracleEpoch_data_ne {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N) (hN5 : 5 ≤ N) :
    ∃ t1 t2 : (oracleEpoch N hN).good,
      (oracleEpoch N hN).data t1 ≠ (oracleEpoch N hN).data t2 := by
  haveI : NeZero N := ⟨by omega⟩
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime 2 hcop
  let t1 : (oracleEpoch N hN).good :=
    ⟨(1 : (ZMod N)ˣ), by
      change (1 : (ZMod N)ˣ) ∈ squareSet N
      exact Finset.mem_image.mpr ⟨(1 : (ZMod N)ˣ), Finset.mem_univ _, by simp⟩⟩
  let t2 : (oracleEpoch N hN).good :=
    ⟨u ^ 2, by
      change u ^ 2 ∈ squareSet N
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩
  refine ⟨t1, t2, ?_⟩
  intro hdata
  have hroot : ((oracleEpoch N hN).data t1).publicRoot =
      ((oracleEpoch N hN).data t2).publicRoot := by
    rw [hdata]
  have hsq1 := oracleEpoch_publicRoot_sq hN t1
  have hsq2 := oracleEpoch_publicRoot_sq hN t2
  have heq : oraclePublicVal hN t1 = oraclePublicVal hN t2 := by
    rw [← hsq1, ← hsq2]
    exact congrArg (fun z : (ZMod N)ˣ => z ^ 2) hroot
  have heqZ : (oraclePublicVal hN t1 : ZMod N) = (oraclePublicVal hN t2 : ZMod N) :=
    congrArg (fun z : (ZMod N)ˣ => (z : ZMod N)) heq
  have hval1 : (oraclePublicVal hN t1 : ZMod N) = (1 : ZMod N) := by
    simp [oraclePublicVal, t1]
  have hval2u : oraclePublicVal hN t2 = u ^ 2 := rfl
  have hval2 : (oraclePublicVal hN t2 : ZMod N) = (u : ZMod N) ^ 2 := by
    rw [hval2u]
    exact Units.val_pow_eq_pow_val (a := u) 2
  have hone : (1 : ZMod N) = (u : ZMod N) ^ 2 := by
    rw [← hval1, ← hval2]
    exact heqZ
  -- The specific inequality `u ^ 2 ≠ 1` for the unit `u = 2`.
  have hu : (u : ZMod N) = (2 : ZMod N) := ZMod.coe_unitOfCoprime 2 hcop
  have hfour : (((4 : ℕ) : ZMod N)).val = 4 := ZMod.val_natCast_of_lt (by omega)
  have honeval : (1 : ZMod N).val = 1 := ZMod.val_one'' (by omega)
  have hsq : ((u : ZMod N) ^ 2) ≠ (1 : ZMod N) := by
    intro h
    have hfour' : ((u : ZMod N) ^ 2) = ((4 : ℕ) : ZMod N) := by
      rw [hu]
      norm_num
    have hv : ((u : ZMod N) ^ 2).val = 4 := by
      rw [hfour']
      exact hfour
    rw [h] at hv
    rw [honeval] at hv
    omega
  exact hsq hone.symm

/-- **Sampler-based non-vacuity.**  There is no costed realization of the oracle
epoch that charges zero public work.  If it did, the sampler cost would be zero
on every seed, so the sampler would be constant; but the oracle's actual law is
uniform, giving positive mass to label assignments other than the constant
output.  This is the stronger reason: the free hidden sample is now charged. -/
theorem oracleEpoch_no_zero_cost_sampler {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (hN5 : 5 ≤ N) :
    ¬ ∃ R : CostedRealization (oracleEpoch N hN),
        ∀ x : (oracleEpoch N hN).Sample, (oracleEpoch N hN).pubWork x = 0 := by
  rintro ⟨R, hzero⟩
  let s0 : R.Seed := R.seedLaw.support_nonempty.some
  have hconst := sampler_run_const_of_zero_pubWork R hzero
  obtain ⟨u, hu1⟩ := exists_unit_ne_one hN hodd
  let ℓ : Unit → (ZMod N)ˣ := fun _ =>
    if R.samplerProgram.run s0 () = u then 1 else u
  have hℓ : ℓ ≠ R.samplerProgram.run s0 := by
    intro heq
    have hpt := congrArg (fun f : Unit → (ZMod N)ˣ => f ()) heq
    by_cases h : R.samplerProgram.run s0 () = u
    · have hℓu : ℓ () = 1 := by simp [ℓ, h]
      rw [hpt] at hℓu
      rw [h] at hℓu
      exact hu1 hℓu
    · have hℓu : ℓ () = u := by simp [ℓ, h]
      rw [hpt] at hℓu
      exact h hℓu
  let x : (oracleEpoch N hN).Sample := ((), ℓ)
  have hx : x.2 ≠ R.samplerProgram.run s0 := hℓ
  have hzeroMass : (oracleEpoch N hN).actual x = 0 :=
    actual_apply_eq_zero_of_seed_ne R hconst s0 hx
  exact oracleEpoch_actual_ne_zero hN x hzeroMass

/-- **Non-vacuity of the costed interface.**  The zero-work `oracleEpoch` of
`RandomizedEpochVacuity` has no costed realization at all: its `pubWork` is
identically zero, so the sampler would have to be zero-cost and hence constant,
contradicting the uniform actual law.  This makes the loophole in the old
interface explicit and checkable. -/
theorem oracleEpoch_no_costedRealization {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (hN5 : 5 ≤ N) :
    ¬ Nonempty (CostedRealization (oracleEpoch N hN)) := by
  rintro ⟨R⟩
  exact oracleEpoch_no_zero_cost_sampler hN hodd hN5 ⟨R, fun _ => rfl⟩

/-- Equivalently: there is no `CostedHardEpochData` whose underlying bare epoch
is the zero-work oracle epoch. -/
theorem oracleEpoch_not_costed {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N) (hN5 : 5 ≤ N) :
    ¬ ∃ C : CostedHardEpochData N, C.base = oracleEpoch N hN := by
  rintro ⟨⟨base, R⟩, hC⟩
  subst hC
  exact oracleEpoch_no_costedRealization hN hodd hN5 ⟨R⟩

/-- The same statement with the zero-work hypothesis written out explicitly. -/
theorem oracleEpoch_not_costed_zero_work {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (hN5 : 5 ≤ N) :
    ¬ ∃ C : CostedHardEpochData N,
        C.base = oracleEpoch N hN ∧ (∀ x : C.base.Sample, C.base.pubWork x = 0) := by
  rintro ⟨C, hC, _⟩
  exact oracleEpoch_not_costed hN hodd hN5 ⟨C, hC⟩

/-! ## 6. Residual asymptotic lower bound -/

/-- The oracle epoch with a modified public-work function.  All semantic data
(uniform ideal/actual laws, public square transcript, chosen square root) are
those of `oracleEpoch`, but the epoch may now declare positive work.  This is
exactly the shape that a cheap sampler/root extractor would occupy. -/
noncomputable def oracleLike {N : ℕ} (hN : 3 ≤ N)
    (pubWork : (oracleEpoch N hN).Sample → ℕ) : HardEpochData N :=
  { oracleEpoch N hN with pubWork := pubWork }

/-- A costed oracle-shaped epoch: the oracle's semantic data, arbitrary declared
work, and a costed realization witnessing a sampler and a data extractor. -/
abbrev OracleLikeCostedEpoch (N : ℕ) (hN : 3 ≤ N) : Type 1 :=
  Σ pubWork : (oracleEpoch N hN).Sample → ℕ,
    CostedRealization (oracleLike hN pubWork)

namespace OracleLikeCostedEpoch

/-- Forget the oracle shape and view the epoch as a general costed hard epoch. -/
noncomputable def toCosted {N : ℕ} {hN : 3 ≤ N} (E : OracleLikeCostedEpoch N hN) :
    CostedHardEpochData N :=
  ⟨oracleLike hN E.1, E.2⟩

end OracleLikeCostedEpoch

/-- The missing asymptotic lower bound for hidden-sample generation and public
root extraction in the oracle epoch.  For every costed oracle-shaped epoch with
*arbitrary positive declared work*, the expected public work exceeds
`exp (δ * scale n)` eventually on hard inputs, for every `δ > 0`.

This covers the deeper loophole: a modified oracle could declare work
`O(log n)`, which is still below `exp (δ * scale n)`.  The zero-work case is
already excluded unconditionally by `oracleEpoch_no_costedRealization`; this
`Prop` is the additional complexity assumption needed to exclude every cheap
sampler/root extractor.  Informally it says that sampling a uniform square root
modulo a hard `N` and extracting its public root is not subexponential.  The
decision-tree model cannot prove it, so it is left as an explicit hypothesis. -/
def OracleRootExtractionLowerBound : Prop :=
  ∀ (E : ∀ (n : ℕ) (hN : 3 ≤ n), OracleLikeCostedEpoch n hN),
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (hN : 3 ≤ n),
      Odd n → ¬n.Prime → ¬IsPrimePow n →
        ENNReal.ofReal (exp (δ * scale n)) <
          mean ((E n hN).toCosted).base.actual
            (fun x => (((E n hN).toCosted).base.pubWork x : ℝ≥0∞))

/-- **Conditional endpoint for the oracle family.**  If the residual
`OracleRootExtractionLowerBound` holds and hard inputs are unbounded, then no
costed oracle-shaped family (with arbitrary positive work) can satisfy the
costed bound at `C = 0`.  This isolates exactly what the cost model does *not*
prove: the nonexistence of a cheap sampler/root extractor at the asymptotic
level. -/
theorem not_costedHardEpochAsymptoticBound_zero_of_oracle
    (hLB : OracleRootExtractionLowerBound)
    (hHard : ∀ N : ℕ, ∃ n ≥ N, Odd n ∧ ¬n.Prime ∧ ¬IsPrimePow n)
    (E : ∀ (n : ℕ) (hN : 3 ≤ n), OracleLikeCostedEpoch n hN) :
    ¬ CostedHardEpochAsymptoticBound (fun n hN => (E n hN).toCosted) 0 := by
  intro hbound
  obtain ⟨Nb, hbN⟩ := Filter.eventually_atTop.mp (hbound (1 / 2) (by norm_num))
  obtain ⟨Nl, hlN⟩ := Filter.eventually_atTop.mp (hLB E (1 / 4) (by norm_num))
  obtain ⟨n, hnmax, hodd, hnp, hnpow⟩ := hHard (max Nb Nl + 4)
  have hn3 : 3 ≤ n := by omega
  have hnb : Nb ≤ n := by omega
  have hnl : Nl ≤ n := by omega
  obtain ⟨-, -, W_pub, γ, ε, -, hmean, hW, -, -, -⟩ := hbN n hnb hn3 hodd hnp hnpow
  have hW' : W_pub ≤ exp ((1 / 4) * scale n) := by
    rw [show (0 + (1 / 2) / 2 : ℝ) = 1 / 4 by norm_num] at hW
    exact hW
  have hle : mean ((E n hn3).toCosted).base.actual
      (fun x => (((E n hn3).toCosted).base.pubWork x : ℝ≥0∞)) ≤
        ENNReal.ofReal (exp ((1 / 4) * scale n)) :=
    hmean.trans (ENNReal.ofReal_le_ofReal hW')
  have hlt := hlN n hnl hn3 hodd hnp hnpow
  exact (not_lt_of_ge hle) hlt

/-! ## 7. Axiom audit -/

#print axioms Program.eq_leaf_of_cost_eq_zero
#print axioms Program.run_eq_of_cost_eq_zero
#print axioms CostedHardEpochData.sampler_cost_le_pubWork
#print axioms CostedHardEpochData.program_cost_le_pubWork
#print axioms CostedHardEpochData.mean_pubWork_le_of_parts
#print axioms CostedHardEpochData.mean_samplerCost_le_of_mean_pubWork
#print axioms costed_assembled_epoch_ratio_eventually
#print axioms serialized_costed_assembled_epoch_from_critical_line
#print axioms sampler_run_const_of_zero_pubWork
#print axioms actual_apply_eq_zero_of_seed_ne
#print axioms data_constant_of_zero_pubWork
#print axioms exists_pos_pubWork_of_data_ne
#print axioms zmod_two_ne_one
#print axioms exists_unit_ne_one
#print axioms oracleEpoch_actual_ne_zero
#print axioms oracleEpoch_publicRoot_sq
#print axioms oracleEpoch_data_ne
#print axioms oracleEpoch_no_zero_cost_sampler
#print axioms oracleEpoch_no_costedRealization
#print axioms oracleEpoch_not_costed
#print axioms oracleEpoch_not_costed_zero_work
#print axioms not_costedHardEpochAsymptoticBound_zero_of_oracle

end Cogentic.RandomizedCostedEpoch
