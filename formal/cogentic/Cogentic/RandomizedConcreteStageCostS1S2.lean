import Cogentic.RandomizedConcreteStageCost
import Cogentic.RandomizedUniformBits
import Cogentic.RandomizedProbeCount

/-!
# Concrete stage costs for `S1` (field pool) and `S2` (character probes)

`Cogentic.RandomizedConcreteEpoch` leaves the ten `StageCosts` fields abstract.
`Cogentic.RandomizedConcreteStageCost` instantiates `S0` and `S7`, and
`RandomizedConcreteStageCostS3`/`S8` instantiate two further stages.  This file
instantiates **the public-coin stages `S1` and `S2`** and proves their
polynomial bit-cost bounds.  The remaining six stages are deliberately *not*
claimed.

## S1: field-pool setup

The blueprint's `S1` draws, for each of `P` fields, a prime `Q`, a residue `r`,
a multiplier, the centered base-`Q` digits, a discrete-Gaussian perturbation and
the setup screens.  The two existing counters used here are those of
`RandomizedUniformBits`:

* each field draw is a rejection sample over a range of `s1PoolRange N =
  2 ^ inputBits N` patterns, so one block has width
  `RandomizedUniformBits.width (s1PoolRange N) = inputBits N` bits;
* `RandomizedUniformBits.expectedBits_lt` bounds the expected number of bits
  consumed by one accepted draw by `2 * width`; the deterministic allowance
  `s1DrawBits N = 2 * width + 1` therefore dominates the existing expected-bit
  counter (`s1_expectedBits_le`, `s1_expectedCoins_le`).

Each field costs two such draws (`Q` and `r`) plus a batch of
`(inputBits + 1)` arithmetic steps on `2 * inputBits`-bit words.  Thus

```
s1PoolSize    N = inputBits N + 1
s1DrawBits    N = 2 * width (2 ^ inputBits N) + 1
s1WordBits    N = 2 * inputBits N
s1FieldArith  N = (inputBits N + 1) * (s1WordBits N)^2
s1FieldCost   N = 2 * s1DrawBits N + s1FieldArith N
s1Cost        N = s1PoolSize N * s1FieldCost N
```

and the proved bound is `s1Cost N ≤ 32 * (inputBits N)^4`.

## S2: character probes

The existing probe counter is `RandomizedProbeCount.card_bad_probe_union`: a
family of `tests.card` nonzero vectors has at most
`tests.card * q^(dim - 1)` zero probes.  The stage budget charges
`s2ProbeTests N = (inputBits N + 1)^3` probes, each probe being a dot product
of `s2ProbeLength N = inputBits N + 1` words of `s2ProbeWordBits N =
inputBits N + 1` bits, at `16` word operations per product, plus one compressed
sign-mask word per probe:

```
s2ProbeArith N = s2ProbeTests N * s2ProbeLength N * s2ProbeWordOps N
s2MaskCost   N = s2ProbeTests N * s2MaskBits N
s2Cost       N = s2ProbeArith N + s2MaskCost N
```

with `s2ProbeWordOps N = 16 * (s2ProbeWordBits N)^2`.  The proved bound is
`s2Cost N ≤ 2048 * (inputBits N)^6`, and the existing union bound is recovered
whenever the actual test family fits the budget
(`card_bad_probe_union_le_s2ProbeTests`).

## Compatibility

`S1S2StageCostAgreement D` identifies the epoch's `S1`/`S2` slots with the
deterministic costs above.  Under it:

* `s1_mean_le`, `s2_mean_le` discharge the C4 mean obligations (the costs are
  deterministic);
* `s1StageC4Bound`, `s2StageC4Bound` package the proved C4 slots;
* `ConcreteC4Hypotheses.ofS0S7_withS1S2` assembles a full
  `ConcreteC4Hypotheses` from the existing `S0`/`S7` assembly plus these two
  slots;
* `ConcreteC4Hypotheses.withS1S2` replaces the `S1`/`S2` slots of an arbitrary
  `ConcreteC4Hypotheses` by the proved ones.

No `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose` is used.
-/

namespace Cogentic.RandomizedConcreteStageCostS1S2

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedConcreteStageCost
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedOneThirdAsymptotic
open Filter Real
open scoped BigOperators ENNReal

/-! ## Section 1: The concrete `S1` field-pool cost -/

/-- The range from which one field-pool entry is drawn: all `inputBits N`-bit
patterns, i.e. the ambient field size `2 ^ inputBits N`. -/
def s1PoolRange (N : ℕ) : ℕ := 2 ^ inputBits N

/-- Number of bits in one rejection block for the field-pool range.  This is
exactly `RandomizedUniformBits.width (s1PoolRange N)`. -/
def s1BlockBits (N : ℕ) : ℕ := RandomizedUniformBits.width (s1PoolRange N)

/-- Deterministic bit allowance for one accepted rejection draw.  The existing
counter `RandomizedUniformBits.expectedBits_lt` gives the strict bound
`expected bits < 2 * width`; one extra bit makes the allowance a natural-number
upper bound. -/
def s1DrawBits (N : ℕ) : ℕ := 2 * s1BlockBits N + 1

/-- Number of fields in the pool: polynomial in the input bit length. -/
def s1PoolSize (N : ℕ) : ℕ := inputBits N + 1

/-- One prime draw and one residue draw per field. -/
def s1DrawsPerField : ℕ := 2

/-- Word width of one setup arithmetic operation: products of two
coefficient-sized input words. -/
def s1WordBits (N : ℕ) : ℕ := 2 * inputBits N

/-- Per-field setup arithmetic: `inputBits + 1` schoolbook operations on
`s1WordBits`-bit words.  This covers the multiplier, digit and perturbation
setup of the blueprint. -/
def s1FieldArith (N : ℕ) : ℕ := (inputBits N + 1) * (s1WordBits N) ^ 2

/-- Bit cost of one field: two rejection draws plus the setup arithmetic. -/
def s1FieldCost (N : ℕ) : ℕ :=
  s1DrawsPerField * s1DrawBits N + s1FieldArith N

/-- Concrete `S1` bit cost: one field cost per pool entry. -/
def s1Cost (N : ℕ) : ℕ := s1PoolSize N * s1FieldCost N

/-- The rejection block width is exactly the input bit length. -/
theorem s1BlockBits_eq (N : ℕ) : s1BlockBits N = inputBits N := by
  unfold s1BlockBits s1PoolRange RandomizedUniformBits.width
  exact Nat.clog_pow 2 (inputBits N) (by norm_num)

/-- The field-pool range is nontrivial, as required by the existing counter. -/
theorem one_lt_s1PoolRange (N : ℕ) : 1 < s1PoolRange N := by
  unfold s1PoolRange
  exact one_lt_pow' (by norm_num) (Nat.ne_of_gt (inputBits_pos N))

/-- One accepted draw fits in `3 * inputBits` bits. -/
theorem s1DrawBits_le (N : ℕ) : s1DrawBits N ≤ 3 * inputBits N := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  unfold s1DrawBits
  rw [s1BlockBits_eq]
  omega

/-- Exact normal form of the per-field arithmetic charge. -/
theorem s1FieldArith_eq (N : ℕ) :
    s1FieldArith N = 4 * (inputBits N) ^ 2 * (inputBits N + 1) := by
  unfold s1FieldArith s1WordBits
  ring

/-- The per-field cost is cubic in the input bit length. -/
theorem s1FieldCost_le (N : ℕ) :
    s1FieldCost N ≤ 14 * (inputBits N) ^ 3 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  unfold s1FieldCost s1DrawsPerField s1FieldArith s1WordBits s1DrawBits
  rw [s1BlockBits_eq]
  nlinarith only [hB]

/-- The pool size is at most twice the input bit length. -/
theorem s1PoolSize_le (N : ℕ) : s1PoolSize N ≤ 2 * inputBits N := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  unfold s1PoolSize
  omega

/-- **Polynomial bit-cost bound for `S1`**: quartic in the input bit length. -/
theorem s1Cost_le_poly (N : ℕ) :
    s1Cost N ≤ 32 * (inputBits N) ^ 4 := by
  have hfield := s1FieldCost_le N
  have hpool := s1PoolSize_le N
  calc
    s1Cost N = s1PoolSize N * s1FieldCost N := rfl
    _ ≤ (2 * inputBits N) * (14 * (inputBits N) ^ 3) :=
      Nat.mul_le_mul hpool hfield
    _ = 28 * (inputBits N) ^ 4 := by ring
    _ ≤ 32 * (inputBits N) ^ 4 :=
      Nat.mul_le_mul_right _ (by norm_num : 28 ≤ 32)

/-- The `S1` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s1Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s1Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 32) hε 4] with N hN
  have hcast : (s1Cost N : ℝ) ≤ 32 * ((N.log2 : ℝ) + 1) ^ 4 := by
    have h := s1Cost_le_poly N
    have h' : (s1Cost N : ℝ) ≤ ((32 * (inputBits N) ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [inputBits] using h'
  exact hcast.trans hN

/-- **The existing expected-bit counter is below the `S1` draw allowance.**  This
pins the deterministic cost `s1DrawBits` to
`RandomizedUniformBits.expectedBits_lt` rather than to an invented formula. -/
theorem s1_expectedBits_le (N : ℕ) :
    (∫⁻ s, RandomizedUniformBits.bitsUsed (s1PoolRange N) s
        ∂(RandomizedUniformBits.blockStream (s1PoolRange N))) ≤
      (s1DrawBits N : ℝ≥0∞) := by
  have h := RandomizedUniformBits.expectedBits_lt (m := s1PoolRange N)
    (one_lt_s1PoolRange N)
  have hw : RandomizedUniformBits.width (s1PoolRange N) = inputBits N :=
    s1BlockBits_eq N
  rw [hw] at h
  refine h.le.trans ?_
  unfold s1DrawBits s1BlockBits
  rw [hw]
  have hle : (2 * (inputBits N : ℝ≥0∞)) ≤
      ((2 * inputBits N + 1 : ℕ) : ℝ≥0∞) := by
    push_cast
    exact le_add_right le_rfl
  exact hle

/-- The same expected-bit bound for the fair-coin presentation of the sampler. -/
theorem s1_expectedCoins_le (N : ℕ) :
    (∫⁻ bits, RandomizedUniformBits.bitsUsed (s1PoolRange N)
        (fun j => RandomizedUniformBits.encodeBlock (bits j))
        ∂(RandomizedUniformBits.coins (s1PoolRange N))) ≤
      (s1DrawBits N : ℝ≥0∞) := by
  have h := RandomizedUniformBits.expectedCoins_lt (m := s1PoolRange N)
    (one_lt_s1PoolRange N)
  unfold s1DrawBits s1BlockBits
  refine h.le.trans ?_
  have hle : (2 * (RandomizedUniformBits.width (s1PoolRange N) : ℝ≥0∞)) ≤
      ((2 * RandomizedUniformBits.width (s1PoolRange N) + 1 : ℕ) : ℝ≥0∞) := by
    push_cast
    exact le_add_right le_rfl
  exact hle

/-! ## Section 2: The concrete `S2` character-probe cost -/

/-- Number of scalar probes charged to `S2`: cubic in the input bit length. -/
def s2ProbeTests (N : ℕ) : ℕ := (inputBits N + 1) ^ 3

/-- Length of one probe: one coefficient per input bit. -/
def s2ProbeLength (N : ℕ) : ℕ := inputBits N + 1

/-- Word width of one probe entry. -/
def s2ProbeWordBits (N : ℕ) : ℕ := inputBits N + 1

/-- Bit operations of one word product: schoolbook multiplication with the
usual four half-products. -/
def s2ProbeWordOps (N : ℕ) : ℕ := 16 * (s2ProbeWordBits N) ^ 2

/-- Arithmetic cost of all probes: one dot product of `s2ProbeLength` words per
test. -/
def s2ProbeArith (N : ℕ) : ℕ :=
  s2ProbeTests N * s2ProbeLength N * s2ProbeWordOps N

/-- Width of one compressed sign-mask word. -/
def s2MaskBits (N : ℕ) : ℕ := inputBits N + 1

/-- Cost of compressing one sign per probe into a masked bit. -/
def s2MaskCost (N : ℕ) : ℕ := s2ProbeTests N * s2MaskBits N

/-- Concrete `S2` bit cost: probe arithmetic plus sign-mask compression. -/
def s2Cost (N : ℕ) : ℕ := s2ProbeArith N + s2MaskCost N

/-- Exact normal form of the probe arithmetic. -/
theorem s2ProbeArith_eq (N : ℕ) :
    s2ProbeArith N = 16 * (inputBits N + 1) ^ 6 := by
  unfold s2ProbeArith s2ProbeTests s2ProbeLength s2ProbeWordOps s2ProbeWordBits
  ring

/-- Exact normal form of the mask cost. -/
theorem s2MaskCost_eq (N : ℕ) :
    s2MaskCost N = (inputBits N + 1) ^ 4 := by
  unfold s2MaskCost s2ProbeTests s2MaskBits
  ring

/-- Exact normal form of the concrete `S2` cost. -/
theorem s2Cost_eq (N : ℕ) :
    s2Cost N = 16 * (inputBits N + 1) ^ 6 + (inputBits N + 1) ^ 4 := by
  rw [s2Cost, s2ProbeArith_eq, s2MaskCost_eq]

theorem s2Cost_nonneg (N : ℕ) : 0 ≤ s2Cost N := Nat.zero_le _

/-- **Polynomial bit-cost bound for `S2`**: sextic in the input bit length. -/
theorem s2Cost_le_poly (N : ℕ) :
    s2Cost N ≤ 2048 * (inputBits N) ^ 6 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  have hbase : 1 ≤ inputBits N + 1 := by omega
  have h46 : (inputBits N + 1) ^ 4 ≤ (inputBits N + 1) ^ 6 := by
    calc
      (inputBits N + 1) ^ 4 = (inputBits N + 1) ^ 4 * 1 := (Nat.mul_one _).symm
      _ ≤ (inputBits N + 1) ^ 4 * (inputBits N + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (one_le_pow₀ hbase)
      _ = (inputBits N + 1) ^ 6 := by ring
  have h17 : 16 * (inputBits N + 1) ^ 6 + (inputBits N + 1) ^ 4 ≤
      17 * (inputBits N + 1) ^ 6 := by
    nlinarith only [h46]
  have hshift : inputBits N + 1 ≤ 2 * inputBits N := by omega
  have hpow : (inputBits N + 1) ^ 6 ≤ 64 * (inputBits N) ^ 6 := by
    calc
      (inputBits N + 1) ^ 6 ≤ (2 * inputBits N) ^ 6 :=
        Nat.pow_le_pow_left hshift 6
      _ = 64 * (inputBits N) ^ 6 := by ring
  calc
    s2Cost N = 16 * (inputBits N + 1) ^ 6 + (inputBits N + 1) ^ 4 := s2Cost_eq N
    _ ≤ 17 * (inputBits N + 1) ^ 6 := h17
    _ ≤ 17 * (64 * (inputBits N) ^ 6) := Nat.mul_le_mul_left _ hpow
    _ = 1088 * (inputBits N) ^ 6 := by ring
    _ ≤ 2048 * (inputBits N) ^ 6 :=
      Nat.mul_le_mul_right _ (by norm_num : 1088 ≤ 2048)

/-- The `S2` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s2Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s2Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 2048) hε 6] with N hN
  have hcast : (s2Cost N : ℝ) ≤ 2048 * ((N.log2 : ℝ) + 1) ^ 6 := by
    have h := s2Cost_le_poly N
    have h' : (s2Cost N : ℝ) ≤ ((2048 * (inputBits N) ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [inputBits] using h'
  exact hcast.trans hN

/-- **The existing bad-probe union bound with the `S2` probe budget.**  If the
actual family of tests fits the charged probe count, the zero-probe count is at
most the charged count times the `RandomizedProbeCount` fiber size.  This pins
`s2ProbeTests` to the existing probe counter. -/
theorem card_bad_probe_union_le_s2ProbeTests
    {I K J : Type*} [Fintype I] [DecidableEq I] [Field K]
    [Fintype K] [DecidableEq K] [Nonempty I]
    (N : ℕ) (tests : Finset J) (vectors : J → I → K)
    (hnonzero : ∀ j ∈ tests, vectors j ≠ 0)
    (hcard : tests.card ≤ s2ProbeTests N) :
    (tests.biUnion fun j => Finset.univ.filter fun u : I → K =>
        vectors j ⬝ᵥ u = 0).card ≤
      s2ProbeTests N * Fintype.card K ^ (Fintype.card I - 1) := by
  calc
    (tests.biUnion fun j => Finset.univ.filter fun u : I → K =>
        vectors j ⬝ᵥ u = 0).card
        ≤ tests.card * Fintype.card K ^ (Fintype.card I - 1) :=
          RandomizedProbeCount.card_bad_probe_union tests vectors hnonzero
    _ ≤ s2ProbeTests N * Fintype.card K ^ (Fintype.card I - 1) :=
      Nat.mul_le_mul_right _ hcard

/-- The same union bound in the full probe space, with the `S2` budget. -/
theorem card_bad_probe_union_mul_field_le_s2ProbeTests
    {I K J : Type*} [Fintype I] [DecidableEq I] [Field K]
    [Fintype K] [DecidableEq K] [Nonempty I]
    (N : ℕ) (tests : Finset J) (vectors : J → I → K)
    (hnonzero : ∀ j ∈ tests, vectors j ≠ 0)
    (hcard : tests.card ≤ s2ProbeTests N) :
    (tests.biUnion fun j => Finset.univ.filter fun u : I → K =>
        vectors j ⬝ᵥ u = 0).card * Fintype.card K ≤
      s2ProbeTests N * Fintype.card (I → K) := by
  calc
    (tests.biUnion fun j => Finset.univ.filter fun u : I → K =>
        vectors j ⬝ᵥ u = 0).card * Fintype.card K
        ≤ (tests.card * Fintype.card K ^ (Fintype.card I - 1)) *
            Fintype.card K :=
          Nat.mul_le_mul_right _
            (RandomizedProbeCount.card_bad_probe_union tests vectors hnonzero)
    _ = tests.card * Fintype.card (I → K) := by
      rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel Fintype.card_pos,
        Fintype.card_fun]
    _ ≤ s2ProbeTests N * Fintype.card (I → K) :=
      Nat.mul_le_mul_right _ hcard

/-! ## Section 3: The `S1`/`S2` stage costs -/

section StageCost

/-- The concrete `S1` stage cost: field-pool setup, independent of the sampled
coins and hidden labels. -/
def s1StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s1Cost N

@[simp] theorem s1StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s1StageCost Coins Label N x = s1Cost N := rfl

theorem s1StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s1StageCost Coins Label N x := Nat.zero_le _

theorem s1StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s1StageCost Coins Label N x ≤ 32 * (inputBits N) ^ 4 :=
  s1Cost_le_poly N

/-- The concrete `S2` stage cost: character probes, independent of the sampled
coins and hidden labels. -/
def s2StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s2Cost N

@[simp] theorem s2StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s2StageCost Coins Label N x = s2Cost N := rfl

theorem s2StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s2StageCost Coins Label N x := Nat.zero_le _

theorem s2StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s2StageCost Coins Label N x ≤ 2048 * (inputBits N) ^ 6 :=
  s2Cost_le_poly N

end StageCost

/-- Identification hypothesis: the concrete epoch `D` charges exactly the
deterministic `S1`/`S2` costs of this file.  This is a modelling statement about
which epoch is being costed, not an analytic estimate. -/
structure S1S2StageCostAgreement {N : ℕ} (D : ConcreteEpochData N) : Prop where
  /-- `S1` is the field-pool setup cost. -/
  s1 : ∀ x : D.Sample, D.stageCosts.s1 x = s1Cost N
  /-- `S2` is the character-probe cost. -/
  s2 : ∀ x : D.Sample, D.stageCosts.s2 x = s2Cost N

namespace S1S2StageCostAgreement

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The `S1` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S1 (H : S1S2StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S1 x = s1Cost N := by
  change D.stageCosts.s1 x = s1Cost N
  exact H.s1 x

/-- The `S2` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S2 (H : S1S2StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S2 x = s2Cost N := by
  change D.stageCosts.s2 x = s2Cost N
  exact H.s2 x

/-- The concrete `S1` work is charged to the epoch's public work. -/
theorem s1Cost_le_pubWork (H : S1S2StageCostAgreement D) (x : D.Sample) :
    s1Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S1 x = s1Cost N := by
    change D.stageCosts.s1 x = s1Cost N
    exact H.s1 x
  have h := D.stageCost_le_pubWork Stage.S1 x
  rwa [hc] at h

/-- The concrete `S2` work is charged to the epoch's public work. -/
theorem s2Cost_le_pubWork (H : S1S2StageCostAgreement D) (x : D.Sample) :
    s2Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S2 x = s2Cost N := by
    change D.stageCosts.s2 x = s2Cost N
    exact H.s2 x
  have h := D.stageCost_le_pubWork Stage.S2 x
  rwa [hc] at h

end S1S2StageCostAgreement

/-! ## Section 4: Compatibility with the family-level `StageDecomposition` -/

/-- The family-level stage decomposition has the concrete `S1` cost in its `S1`
slot. -/
theorem familyStageDecomposition_cost_S1
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S1S2StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S1 n hN x = s1Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s1 x

/-- The family-level stage decomposition has the concrete `S2` cost in its `S2`
slot. -/
theorem familyStageDecomposition_cost_S2
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S1S2StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S2 n hN x = s2Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s2 x

/-- The family-level `S1` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S1_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S1S2StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S1 n hN x ≤ 32 * (inputBits n) ^ 4 := by
  rw [familyStageDecomposition_cost_S1 D H n hN x]
  exact s1Cost_le_poly n

/-- The family-level `S2` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S2_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S1S2StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S2 n hN x ≤ 2048 * (inputBits n) ^ 6 := by
  rw [familyStageDecomposition_cost_S2 D H n hN x]
  exact s2Cost_le_poly n

/-! ## Section 5: Compatibility with `StageC4Bound` and `ConcreteC4Hypotheses` -/

/-- The `S1` mean cost is the deterministic value `s1Cost n`, so the C4 mean
obligation at `S1` is a theorem, not a hypothesis. -/
theorem s1_mean_le (D : ∀ n, ConcreteEpochData n)
    (H : ∀ n, S1S2StageCostAgreement (D n)) (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S1 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s1Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S1 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s1Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S1 x : ℝ≥0∞)) = fun _ => (s1Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S1 x = s1Cost n := by
      change (D n).stageCosts.s1 x = s1Cost n
      exact (H n).s1 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s1Cost n)).symm

/-- The `S2` mean cost is the deterministic value `s2Cost n`, so the C4 mean
obligation at `S2` is a theorem, not a hypothesis. -/
theorem s2_mean_le (D : ∀ n, ConcreteEpochData n)
    (H : ∀ n, S1S2StageCostAgreement (D n)) (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S2 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s2Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S2 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s2Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S2 x : ℝ≥0∞)) = fun _ => (s2Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S2 x = s2Cost n := by
      change (D n).stageCosts.s2 x = s2Cost n
      exact (H n).s2 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s2Cost n)).symm

/-- **The `S1` C4 slot is discharged** with weight `s1Cost n` and any exponent
`c` with `0 < c < C`. -/
def s1StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, S1S2StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S1 where
  weight := fun n => (s1Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s1_mean_le D H n
  weight_le := eventually_s1Cost_le_exp hc

/-- **The `S2` C4 slot is discharged** with weight `s2Cost n` and any exponent
`c` with `0 < c < C`. -/
def s2StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, S1S2StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S2 where
  weight := fun n => (s2Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s2_mean_le D H n
  weight_le := eventually_s2Cost_le_exp hc

/-- **Compatibility with the existing `S0`/`S7` assembly.**  A full
`ConcreteC4Hypotheses` is obtained from `ConcreteC4Hypotheses.ofS0S7` after
filling the `S1`/`S2` slots concretely.  The caller supplies the analytic data
for the six remaining stages; the `S1`/`S2` mean and weight bounds are proved
here from `S1S2StageCostAgreement`.  The hypotheses `W Stage.S1 = s1Cost`,
`W Stage.S2 = s2Cost`, the strict positivity of `c Stage.S1`/`c Stage.S2`, and
their bounds by `C` are the only extra inputs. -/
noncomputable def ConcreteC4Hypotheses.ofS0S7_withS1S2
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ∀ n, StageCostAgreement (D n))
    (H12 : ∀ n, S1S2StageCostAgreement (D n))
    (W : Stage → ℕ → ℝ) (c : Stage → ℝ)
    (hW1 : W Stage.S1 = fun n => (s1Cost n : ℝ))
    (hW2 : W Stage.S2 = fun n => (s2Cost n : ℝ))
    (hc1pos : 0 < c Stage.S1) (hc1C : c Stage.S1 < C)
    (hc2pos : 0 < c Stage.S2) (hc2C : c Stage.S2 < C)
    (hc : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      c j < C)
    (hmean : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (concreteCostFamily D n hN).actual
            (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
          ENNReal.ofReal (W j n))
    (hW : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    {c0 c7 : ℝ} (hc0 : 0 < c0) (h0C : c0 < C)
    (hc7 : 0 < c7) (h7C : c7 < C) :
    ConcreteC4Hypotheses D C := by
  refine ConcreteC4Hypotheses.ofS0S7 D H W c ?_ ?_ ?_ hc0 h0C hc7 h7C
  · intro j hj0 hj7
    by_cases hj1 : j = Stage.S1
    · subst j
      exact hc1C
    · by_cases hj2 : j = Stage.S2
      · subst j
        exact hc2C
      · exact hc j hj0 hj7 hj1 hj2
  · intro j hj0 hj7
    by_cases hj1 : j = Stage.S1
    · subst j
      simpa only [hW1] using
        (Filter.Eventually.of_forall fun n => s1_mean_le D H12 n)
    · by_cases hj2 : j = Stage.S2
      · subst j
        simpa only [hW2] using
          (Filter.Eventually.of_forall fun n => s2_mean_le D H12 n)
      · exact hmean j hj0 hj7 hj1 hj2
  · intro j hj0 hj7
    by_cases hj1 : j = Stage.S1
    · subst j
      simpa only [hW1] using eventually_s1Cost_le_exp hc1pos
    · by_cases hj2 : j = Stage.S2
      · subst j
        simpa only [hW2] using eventually_s2Cost_le_exp hc2pos
      · exact hW j hj0 hj7 hj1 hj2

/-- The assembled hypothesis carries the concrete `s1Cost` weight at `S1`. -/
theorem ConcreteC4Hypotheses.ofS0S7_withS1S2_stageWeight_S1
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ∀ n, StageCostAgreement (D n))
    (H12 : ∀ n, S1S2StageCostAgreement (D n))
    (W : Stage → ℕ → ℝ) (c : Stage → ℝ)
    (hW1 : W Stage.S1 = fun n => (s1Cost n : ℝ))
    (hW2 : W Stage.S2 = fun n => (s2Cost n : ℝ))
    (hc1pos : 0 < c Stage.S1) (hc1C : c Stage.S1 < C)
    (hc2pos : 0 < c Stage.S2) (hc2C : c Stage.S2 < C)
    (hc : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      c j < C)
    (hmean : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (concreteCostFamily D n hN).actual
            (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
          ENNReal.ofReal (W j n))
    (hW : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    {c0 c7 : ℝ} (hc0 : 0 < c0) (h0C : c0 < C)
    (hc7 : 0 < c7) (h7C : c7 < C) :
    (ConcreteC4Hypotheses.ofS0S7_withS1S2 D H H12 W c hW1 hW2 hc1pos hc1C
      hc2pos hc2C hc hmean hW hc0 h0C hc7 h7C).stageWeight Stage.S1 =
      fun n => (s1Cost n : ℝ) := by
  simp [ConcreteC4Hypotheses.ofS0S7_withS1S2, ConcreteC4Hypotheses.ofS0S7,
    combinedWeight, hW1]

/-- The assembled hypothesis carries the concrete `s2Cost` weight at `S2`. -/
theorem ConcreteC4Hypotheses.ofS0S7_withS1S2_stageWeight_S2
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ∀ n, StageCostAgreement (D n))
    (H12 : ∀ n, S1S2StageCostAgreement (D n))
    (W : Stage → ℕ → ℝ) (c : Stage → ℝ)
    (hW1 : W Stage.S1 = fun n => (s1Cost n : ℝ))
    (hW2 : W Stage.S2 = fun n => (s2Cost n : ℝ))
    (hc1pos : 0 < c Stage.S1) (hc1C : c Stage.S1 < C)
    (hc2pos : 0 < c Stage.S2) (hc2C : c Stage.S2 < C)
    (hc : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      c j < C)
    (hmean : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (concreteCostFamily D n hN).actual
            (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
          ENNReal.ofReal (W j n))
    (hW : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S1 → j ≠ Stage.S2 →
      ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    {c0 c7 : ℝ} (hc0 : 0 < c0) (h0C : c0 < C)
    (hc7 : 0 < c7) (h7C : c7 < C) :
    (ConcreteC4Hypotheses.ofS0S7_withS1S2 D H H12 W c hW1 hW2 hc1pos hc1C
      hc2pos hc2C hc hmean hW hc0 h0C hc7 h7C).stageWeight Stage.S2 =
      fun n => (s2Cost n : ℝ) := by
  simp [ConcreteC4Hypotheses.ofS0S7_withS1S2, ConcreteC4Hypotheses.ofS0S7,
    combinedWeight, hW2]

/-- Weights for all ten stages with `S1` and `S2` overridden by the concrete
costs. -/
def overrideWeightS1S2 (W : Stage → ℕ → ℝ) : Stage → ℕ → ℝ
  | Stage.S1 => fun n => (s1Cost n : ℝ)
  | Stage.S2 => fun n => (s2Cost n : ℝ)
  | j => W j

/-- Exponents for all ten stages with `S1` and `S2` overridden by the chosen
exponents. -/
def overrideExponentS1S2 (c1 c2 : ℝ) (c : Stage → ℝ) : Stage → ℝ
  | Stage.S1 => c1
  | Stage.S2 => c2
  | j => c j

/-- **C4 compatibility: replace the `S1`/`S2` slots by the proved ones.**
Every other stage is left exactly as supplied by `Hc4`; only the `S1`/`S2` mean
and weight data are replaced by `s1_mean_le`/`s2_mean_le` and
`eventually_s1Cost_le_exp`/`eventually_s2Cost_le_exp`. -/
noncomputable def ConcreteC4Hypotheses.withS1S2
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H12 : ∀ n, S1S2StageCostAgreement (D n))
    {c1 c2 : ℝ} (hc1 : 0 < c1) (h1C : c1 < C)
    (hc2 : 0 < c2) (h2C : c2 < C) :
    ConcreteC4Hypotheses D C where
  stageWeight := overrideWeightS1S2 Hc4.stageWeight
  stageExponent := overrideExponentS1S2 c1 c2 Hc4.stageExponent
  exponent_lt := by
    intro j
    cases j with
    | S0 => simpa [overrideExponentS1S2] using Hc4.exponent_lt Stage.S0
    | S1 => simpa [overrideExponentS1S2] using h1C
    | S2 => simpa [overrideExponentS1S2] using h2C
    | S3 => simpa [overrideExponentS1S2] using Hc4.exponent_lt Stage.S3
    | S4 => simpa [overrideExponentS1S2] using Hc4.exponent_lt Stage.S4
    | S5 => simpa [overrideExponentS1S2] using Hc4.exponent_lt Stage.S5
    | S6 => simpa [overrideExponentS1S2] using Hc4.exponent_lt Stage.S6
    | S7 => simpa [overrideExponentS1S2] using Hc4.exponent_lt Stage.S7
    | S8 => simpa [overrideExponentS1S2] using Hc4.exponent_lt Stage.S8
    | S9 => simpa [overrideExponentS1S2] using Hc4.exponent_lt Stage.S9
  mean_le := by
    intro j
    cases j with
    | S0 => simpa [overrideWeightS1S2] using Hc4.mean_le Stage.S0
    | S1 =>
        simp only [overrideWeightS1S2]
        exact Filter.Eventually.of_forall fun n hN => s1_mean_le D H12 n hN
    | S2 =>
        simp only [overrideWeightS1S2]
        exact Filter.Eventually.of_forall fun n hN => s2_mean_le D H12 n hN
    | S3 => simpa [overrideWeightS1S2] using Hc4.mean_le Stage.S3
    | S4 => simpa [overrideWeightS1S2] using Hc4.mean_le Stage.S4
    | S5 => simpa [overrideWeightS1S2] using Hc4.mean_le Stage.S5
    | S6 => simpa [overrideWeightS1S2] using Hc4.mean_le Stage.S6
    | S7 => simpa [overrideWeightS1S2] using Hc4.mean_le Stage.S7
    | S8 => simpa [overrideWeightS1S2] using Hc4.mean_le Stage.S8
    | S9 => simpa [overrideWeightS1S2] using Hc4.mean_le Stage.S9
  weight_le := by
    intro j
    cases j with
    | S0 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        Hc4.weight_le Stage.S0
    | S1 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        eventually_s1Cost_le_exp hc1
    | S2 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        eventually_s2Cost_le_exp hc2
    | S3 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        Hc4.weight_le Stage.S3
    | S4 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        Hc4.weight_le Stage.S4
    | S5 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        Hc4.weight_le Stage.S5
    | S6 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        Hc4.weight_le Stage.S6
    | S7 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        Hc4.weight_le Stage.S7
    | S8 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        Hc4.weight_le Stage.S8
    | S9 => simpa [overrideWeightS1S2, overrideExponentS1S2] using
        Hc4.weight_le Stage.S9

/-- The replacement carries the concrete `s1Cost` weight at `S1`. -/
theorem ConcreteC4Hypotheses.withS1S2_stageWeight_S1
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H12 : ∀ n, S1S2StageCostAgreement (D n))
    {c1 c2 : ℝ} (hc1 : 0 < c1) (h1C : c1 < C)
    (hc2 : 0 < c2) (h2C : c2 < C) :
    (ConcreteC4Hypotheses.withS1S2 D Hc4 H12 hc1 h1C hc2 h2C).stageWeight
        Stage.S1 = fun n => (s1Cost n : ℝ) := rfl

/-- The replacement carries the concrete `s2Cost` weight at `S2`. -/
theorem ConcreteC4Hypotheses.withS1S2_stageWeight_S2
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H12 : ∀ n, S1S2StageCostAgreement (D n))
    {c1 c2 : ℝ} (hc1 : 0 < c1) (h1C : c1 < C)
    (hc2 : 0 < c2) (h2C : c2 < C) :
    (ConcreteC4Hypotheses.withS1S2 D Hc4 H12 hc1 h1C hc2 h2C).stageWeight
        Stage.S2 = fun n => (s2Cost n : ℝ) := rfl

/-! ## Section 6: Axiom audit -/

#print axioms s1BlockBits_eq
#print axioms s1DrawBits_le
#print axioms s1FieldCost_le
#print axioms s1Cost_le_poly
#print axioms eventually_s1Cost_le_exp
#print axioms s1_expectedBits_le
#print axioms s1_expectedCoins_le
#print axioms s2ProbeArith_eq
#print axioms s2MaskCost_eq
#print axioms s2Cost_eq
#print axioms s2Cost_le_poly
#print axioms eventually_s2Cost_le_exp
#print axioms card_bad_probe_union_le_s2ProbeTests
#print axioms card_bad_probe_union_mul_field_le_s2ProbeTests
#print axioms S1S2StageCostAgreement.stageDecomposition_cost_S1
#print axioms S1S2StageCostAgreement.stageDecomposition_cost_S2
#print axioms S1S2StageCostAgreement.s1Cost_le_pubWork
#print axioms S1S2StageCostAgreement.s2Cost_le_pubWork
#print axioms familyStageDecomposition_cost_S1
#print axioms familyStageDecomposition_cost_S2
#print axioms familyStageDecomposition_cost_S1_le_poly
#print axioms familyStageDecomposition_cost_S2_le_poly
#print axioms s1_mean_le
#print axioms s2_mean_le
#print axioms s1StageC4Bound
#print axioms s2StageC4Bound
#print axioms ConcreteC4Hypotheses.ofS0S7_withS1S2
#print axioms ConcreteC4Hypotheses.ofS0S7_withS1S2_stageWeight_S1
#print axioms ConcreteC4Hypotheses.ofS0S7_withS1S2_stageWeight_S2
#print axioms ConcreteC4Hypotheses.withS1S2
#print axioms ConcreteC4Hypotheses.withS1S2_stageWeight_S1
#print axioms ConcreteC4Hypotheses.withS1S2_stageWeight_S2

end Cogentic.RandomizedConcreteStageCostS1S2
