import Cogentic.RandomizedConcreteEpoch
import Cogentic.RandomizedConcreteEpochCost
import Cogentic.RandomizedSparseProducts
import Cogentic.RandomizedPadeCost
import Cogentic.RandomizedOneThirdAsymptotic

/-!
# Concrete stage costs for the S0/S7 slots of the S0–S9 epoch (wave 3, W18)

`Cogentic.RandomizedConcreteEpoch` leaves the ten `StageCosts` fields abstract.
This file instantiates **two** of them, `S0` and `S7`, with explicit cost
functions and proves their polynomial bit/field-operation bounds.  The other
eight stages are deliberately *not* claimed.

## S0: deterministic integer parameters

`S0` computes the integer parameters of the epoch from the input bit length.
The bit length of the modulus is `inputBits N = ⌊log₂ N⌋ + 1`.  We define the
degree parameter `s0Degree N = inputBits N / 3`, the cutoff
`s0Cutoff N = 2 ^ (s0Degree N + 1)`, and charge

```
s0Cost N = inputBits N + (s0Degree N + 1)^2 + (s0Degree N + 1)
```

bit operations: one per bit of the input, at most `(degree + 1)` bit operations
per doubling while forming the cutoff, and `(degree + 1)` to emit the parameter
pair.  The proved bound is

```
s0Cost N ≤ 4 * (inputBits N)^2
```

and therefore `s0Cost N ≤ exp (ε * scale N)` eventually for every `ε > 0`.

## S7: sparse `F₂` dependency

The sparse `F₂` linear algebra of `RandomizedSparseProducts` exposes exact
field-operation counters: one `taggedKrylovStep` costs
`(2 * edges + cols)` additions plus `(rows + 2 * cols)` multiplications (this is
`s7StepOps`, and `s7StepOps_eq_taggedKrylovStep_counts` proves it is exactly the
sum of the two counters returned by `taggedKrylovStep_spec`).  With the
dimension and sparsity read off the input bit length,

```
s7Dim N   = inputBits N
s7Edges N = (s7Dim N)^2
s7Steps N = 2 * s7Dim N
s7Cost N  = s7Steps N * s7StepOps (s7Dim N) (s7Dim N) (s7Edges N)
```

we prove `s7Cost N ≤ 12 * (s7Dim N)^4` and again the eventual exponential
bound.  No `RandomizedPadeCost` cost function is a *concrete* per-stage cost
(only a degree-based accounting bound), so S7 is instantiated from the exact
`RandomizedSparseProducts` counters.

## Compatibility

* `PartialStageCosts` carries only `s0` and `s7`; `toStageCosts` extends it with
  eight arbitrary costs, and the `_cost_S0`/`_cost_S7` lemmas recover the two
  concrete stages.
* `StageCostAgreement D` is the identification hypothesis that the epoch `D`
  really uses these two cost functions.  Under it, the canonical
  `ConcreteEpochData.stageDecomposition` and the family-level
  `familyStageDecomposition` have exactly `s0Cost n`/`s7Cost n` at `S0`/`S7`,
  and those costs are charged to `pubWork`.
* The per-stage C4 obligations are *proved*: `s0StageC4Bound` and
  `s7StageC4Bound` exhibit the weights `s0Cost n`/`s7Cost n`, the exponents,
  the mean bounds (the costs are deterministic, so the mean is the constant)
  and the weight bounds.  `ConcreteC4Hypotheses.ofS0S7` assembles a full
  `ConcreteC4Hypotheses` from these proved slots plus the eight remaining
  stages' data.

The identification `StageCostAgreement` is a modelling hypothesis, not an
analytic estimate: it says the concrete epoch is the one whose S0/S7 stages are
the functions defined here.  Nothing about the other eight stages, and no
analytic success/TV/work claim, is asserted.

No `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose` is used.
-/

namespace Cogentic.RandomizedConcreteStageCost

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSparseProducts
open Filter Real
open scoped BigOperators ENNReal

/-! ## Section 1: `S0`, the deterministic integer parameter computation -/

/-- Bit length of the modulus: `⌊log₂ N⌋ + 1`.  This is the "input bit length"
from which the deterministic integer parameters of `S0` are computed. -/
def inputBits (N : ℕ) : ℕ := N.log2 + 1

/-- Degree parameter selected by `S0`: one third of the bit length. -/
def s0Degree (N : ℕ) : ℕ := inputBits N / 3

/-- Cutoff parameter selected by `S0`: `2 ^ (degree + 1)`. -/
def s0Cutoff (N : ℕ) : ℕ := 2 ^ (s0Degree N + 1)

/-- Bit-operation cost of the deterministic `S0` parameter setup.

The model charges one operation per input bit, at most `degree + 1` bit
operations per doubling while forming `2 ^ (degree + 1)`, and `degree + 1` to
emit the parameter pair. -/
def s0Cost (N : ℕ) : ℕ :=
  inputBits N + (s0Degree N + 1) ^ 2 + (s0Degree N + 1)

/-- The degree parameter fits in the bit-length budget. -/
theorem s0Degree_add_one_le_inputBits (N : ℕ) :
    s0Degree N + 1 ≤ inputBits N := by
  have h : N.log2 / 3 ≤ N.log2 := Nat.div_le_self _ _
  unfold s0Degree inputBits
  omega

theorem inputBits_pos (N : ℕ) : 1 ≤ inputBits N := by
  unfold inputBits
  omega

theorem s0Cost_nonneg (N : ℕ) : 0 ≤ s0Cost N := Nat.zero_le _

theorem s0Cost_pos (N : ℕ) : 0 < s0Cost N := by
  have hb : 1 ≤ inputBits N := inputBits_pos N
  unfold s0Cost
  omega

/-- The polynomial bit-cost bound for `S0`. -/
theorem s0Cost_le_poly (N : ℕ) : s0Cost N ≤ 4 * (inputBits N) ^ 2 := by
  have hb : 1 ≤ inputBits N := inputBits_pos N
  have hd : s0Degree N + 1 ≤ inputBits N := s0Degree_add_one_le_inputBits N
  have hsq : (s0Degree N + 1) ^ 2 ≤ (inputBits N) ^ 2 :=
    Nat.pow_le_pow_left hd 2
  have hlin : s0Degree N + 1 ≤ (inputBits N) ^ 2 :=
    hd.trans (by simpa [pow_two] using Nat.le_mul_self (inputBits N))
  have hb2 : inputBits N ≤ (inputBits N) ^ 2 := by
    simpa [pow_two] using Nat.le_mul_self (inputBits N)
  calc
    s0Cost N = inputBits N + (s0Degree N + 1) ^ 2 + (s0Degree N + 1) := rfl
    _ ≤ (inputBits N) ^ 2 + (inputBits N) ^ 2 + (inputBits N) ^ 2 :=
      Nat.add_le_add (Nat.add_le_add hb2 hsq) hlin
    _ = 3 * (inputBits N) ^ 2 := by ring
    _ ≤ 4 * (inputBits N) ^ 2 :=
      Nat.mul_le_mul_right _ (by norm_num : 3 ≤ 4)

/-- The `S0` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s0Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s0Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 4) hε 2] with N hN
  have hcast : (s0Cost N : ℝ) ≤ 4 * ((N.log2 : ℝ) + 1) ^ 2 := by
    have h := s0Cost_le_poly N
    have h' : (s0Cost N : ℝ) ≤ ((4 * (inputBits N) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [inputBits] using h'
  exact hcast.trans hN

section StageCost

/-- The concrete `S0` stage cost: deterministic integer parameter computation,
independent of the sampled coins and hidden labels. -/
def s0StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s0Cost N

@[simp] theorem s0StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s0StageCost Coins Label N x = s0Cost N := rfl

theorem s0StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s0StageCost Coins Label N x := Nat.zero_le _

theorem s0StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s0StageCost Coins Label N x ≤ 4 * (inputBits N) ^ 2 :=
  s0Cost_le_poly N

end StageCost

/-! ## Section 2: `S7`, the sparse `F₂` dependency -/

/-- Matrix dimension of the sparse `F₂` system, read off the input bit length. -/
def s7Dim (N : ℕ) : ℕ := inputBits N

/-- Number of sparse nonzeros: at most one per matrix entry. -/
def s7Edges (N : ℕ) : ℕ := s7Dim N ^ 2

/-- Number of Krylov steps used to extract a dependency: twice the dimension. -/
def s7Steps (N : ℕ) : ℕ := 2 * s7Dim N

/-- Field-operation count of one sparse Krylov step.  This is exactly the sum of
the addition counter `2 * edges + cols` and the multiplication counter
`rows + 2 * cols` of `RandomizedSparseProducts.taggedKrylovStep`. -/
def s7StepOps (rows cols edges : ℕ) : ℕ := (2 * edges + cols) + (rows + 2 * cols)

/-- Concrete `S7` arithmetic cost: the number of Krylov steps times the exact
field-operation count of one sparse step. -/
def s7Cost (N : ℕ) : ℕ :=
  s7Steps N * s7StepOps (s7Dim N) (s7Dim N) (s7Edges N)

/-- The one-step field-operation count is polynomial in the matrix dimensions,
uniformly over rectangular sparse matrices, empty rows/columns and repeated
occurrences. -/
theorem s7StepOps_le_dim (rows cols edges : ℕ) :
    s7StepOps rows cols edges ≤ 8 * (rows + cols + edges + 1) ^ 2 := by
  let s := rows + cols + edges + 1
  have hs : 1 ≤ s := by omega
  have h1 : 2 * edges + cols ≤ 3 * s := by omega
  have h2 : rows + 2 * cols ≤ 3 * s := by omega
  have hsum : s7StepOps rows cols edges ≤ 6 * s := by
    unfold s7StepOps
    omega
  have hsq : 6 * s ≤ 8 * s ^ 2 := by
    calc
      6 * s ≤ 8 * s := Nat.mul_le_mul_right s (by norm_num : 6 ≤ 8)
      _ ≤ 8 * (s * s) := Nat.mul_le_mul_left 8 (Nat.le_mul_self s)
      _ = 8 * s ^ 2 := by ring
  exact hsum.trans hsq

/-- Exact factorization of the concrete `S7` cost. -/
theorem s7Cost_eq (N : ℕ) :
    s7Cost N = 4 * (s7Dim N) ^ 3 + 8 * (s7Dim N) ^ 2 := by
  unfold s7Cost s7Steps s7StepOps s7Edges
  ring

/-- The `S7` cost is nonnegative. -/
theorem s7Cost_nonneg (N : ℕ) : 0 ≤ s7Cost N := Nat.zero_le _

/-- The polynomial field-operation bound for `S7`. -/
theorem s7Cost_le_poly (N : ℕ) : s7Cost N ≤ 12 * (s7Dim N) ^ 4 := by
  have hb : 1 ≤ s7Dim N := by
    unfold s7Dim inputBits
    omega
  have h3 : (s7Dim N) ^ 3 ≤ (s7Dim N) ^ 4 := by
    calc
      (s7Dim N) ^ 3 = (s7Dim N) ^ 3 * 1 := (Nat.mul_one _).symm
      _ ≤ (s7Dim N) ^ 3 * (s7Dim N) := Nat.mul_le_mul_left _ hb
      _ = (s7Dim N) ^ 4 := by ring
  have h2 : (s7Dim N) ^ 2 ≤ (s7Dim N) ^ 4 := by
    calc
      (s7Dim N) ^ 2 = (s7Dim N) ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ (s7Dim N) ^ 2 * (s7Dim N) ^ 2 :=
        Nat.mul_le_mul_left _ (one_le_pow₀ hb)
      _ = (s7Dim N) ^ 4 := by ring
  calc
    s7Cost N = 4 * (s7Dim N) ^ 3 + 8 * (s7Dim N) ^ 2 := s7Cost_eq N
    _ ≤ 4 * (s7Dim N) ^ 4 + 8 * (s7Dim N) ^ 4 :=
      Nat.add_le_add (Nat.mul_le_mul_left 4 h3) (Nat.mul_le_mul_left 8 h2)
    _ = 12 * (s7Dim N) ^ 4 := by ring

/-- The `S7` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s7Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s7Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 12) hε 4] with N hN
  have hcast : (s7Cost N : ℝ) ≤ 12 * ((N.log2 : ℝ) + 1) ^ 4 := by
    have h := s7Cost_le_poly N
    have h' : (s7Cost N : ℝ) ≤ ((12 * (s7Dim N) ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [s7Dim, inputBits] using h'
  exact hcast.trans hN

variable {K I J : Type*} [Field K] [Algebra (ZMod 2) K]
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- **`S7` is the existing sparse-product cost.**  The sum of the two counters
returned by `RandomizedSparseProducts.taggedKrylovStep` is exactly
`s7StepOps` at the matrix dimensions.  This pins the concrete cost above to the
existing sparse `F₂` primitive rather than to an invented formula. -/
theorem s7StepOps_eq_taggedKrylovStep_counts
    (rowIndices : IndexList I) (colIndices : IndexList J)
    (edges : List (I × J)) (d : I → K) (e u x : J → K) :
    (taggedKrylovStep rowIndices colIndices edges d e u x).2.2.1 +
        (taggedKrylovStep rowIndices colIndices edges d e u x).2.2.2 =
      s7StepOps (Fintype.card I) (Fintype.card J) edges.length := by
  rw [taggedKrylovStep_spec]
  unfold s7StepOps
  ring

section StageCost

/-- The concrete `S7` stage cost: sparse `F₂` dependency extraction, independent
of the sampled coins and hidden labels. -/
def s7StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s7Cost N

@[simp] theorem s7StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s7StageCost Coins Label N x = s7Cost N := rfl

theorem s7StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s7StageCost Coins Label N x := Nat.zero_le _

theorem s7StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s7StageCost Coins Label N x ≤ 12 * (s7Dim N) ^ 4 :=
  s7Cost_le_poly N

end StageCost

/-! ## Section 3: Compatibility with the concrete epoch's `StageCosts` -/

/-- The two concrete stages `S0` and `S7`, before the remaining eight stages are
filled in. -/
structure PartialStageCosts (N : ℕ) (Coins Label : Type) where
  /-- `S0`: deterministic integer parameters. -/
  s0 : StageCost N Coins Label
  /-- `S7`: sparse `F₂` dependency. -/
  s7 : StageCost N Coins Label

namespace PartialStageCosts

variable {N : ℕ} {Coins Label : Type}

/-- Extend the two concrete stages with eight arbitrary stage costs. -/
def toStageCosts (P : PartialStageCosts N Coins Label)
    (s1 s2 s3 s4 s5 s6 s8 s9 : StageCost N Coins Label) :
    StageCosts N Coins Label where
  s0 := P.s0
  s1 := s1
  s2 := s2
  s3 := s3
  s4 := s4
  s5 := s5
  s6 := s6
  s7 := P.s7
  s8 := s8
  s9 := s9

@[simp] theorem toStageCosts_cost_S0 (P : PartialStageCosts N Coins Label)
    (s1 s2 s3 s4 s5 s6 s8 s9 : StageCost N Coins Label)
    (x : Sample N Coins Label) :
    (P.toStageCosts s1 s2 s3 s4 s5 s6 s8 s9).cost Stage.S0 x = P.s0 x := rfl

@[simp] theorem toStageCosts_cost_S7 (P : PartialStageCosts N Coins Label)
    (s1 s2 s3 s4 s5 s6 s8 s9 : StageCost N Coins Label)
    (x : Sample N Coins Label) :
    (P.toStageCosts s1 s2 s3 s4 s5 s6 s8 s9).cost Stage.S7 x = P.s7 x := rfl

end PartialStageCosts

/-- The concrete partial stage assignment: `S0` and `S7` are the functions
defined in this file. -/
def concretePartialStageCosts (N : ℕ) (Coins Label : Type) :
    PartialStageCosts N Coins Label where
  s0 := s0StageCost Coins Label N
  s7 := s7StageCost Coins Label N

/-- Identification hypothesis: the concrete epoch `D` charges exactly the
deterministic `S0` and `S7` costs of this file.  This is a modelling statement
about which epoch is being costed, not an analytic estimate. -/
structure StageCostAgreement {N : ℕ} (D : ConcreteEpochData N) : Prop where
  /-- `S0` is the deterministic integer parameter computation. -/
  s0 : ∀ x : D.Sample, D.stageCosts.s0 x = s0Cost N
  /-- `S7` is the sparse `F₂` dependency cost. -/
  s7 : ∀ x : D.Sample, D.stageCosts.s7 x = s7Cost N

namespace StageCostAgreement

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The `S0` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S0 (H : StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S0 x = s0Cost N := by
  change D.stageCosts.s0 x = s0Cost N
  exact H.s0 x

/-- The `S7` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S7 (H : StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S7 x = s7Cost N := by
  change D.stageCosts.s7 x = s7Cost N
  exact H.s7 x

/-- The concrete `S0` work is charged to the epoch's public work. -/
theorem s0Cost_le_pubWork (H : StageCostAgreement D) (x : D.Sample) :
    s0Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S0 x = s0Cost N := by
    change D.stageCosts.s0 x = s0Cost N
    exact H.s0 x
  have h := D.stageCost_le_pubWork Stage.S0 x
  rwa [hc] at h

/-- The concrete `S7` work is charged to the epoch's public work. -/
theorem s7Cost_le_pubWork (H : StageCostAgreement D) (x : D.Sample) :
    s7Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S7 x = s7Cost N := by
    change D.stageCosts.s7 x = s7Cost N
    exact H.s7 x
  have h := D.stageCost_le_pubWork Stage.S7 x
  rwa [hc] at h

end StageCostAgreement

/-! ## Section 4: Compatibility with the family-level `StageDecomposition` -/

/-- The family-level stage decomposition has the concrete `S0` cost in its `S0`
slot. -/
theorem familyStageDecomposition_cost_S0
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S0 n hN x = s0Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s0 x

/-- The family-level stage decomposition has the concrete `S7` cost in its `S7`
slot. -/
theorem familyStageDecomposition_cost_S7
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S7 n hN x = s7Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s7 x

/-- The family-level `S0` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S0_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S0 n hN x ≤ 4 * (inputBits n) ^ 2 := by
  rw [familyStageDecomposition_cost_S0 D H n hN x]
  exact s0Cost_le_poly n

/-- The family-level `S7` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S7_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S7 n hN x ≤ 12 * (s7Dim n) ^ 4 := by
  rw [familyStageDecomposition_cost_S7 D H n hN x]
  exact s7Cost_le_poly n

/-! ## Section 5: Compatibility with `ConcreteC4Hypotheses` -/

/-- The `S0` mean cost is the deterministic value `s0Cost n`, so the C4 mean
obligation at `S0` is a theorem, not a hypothesis. -/
theorem s0_mean_le (D : ∀ n, ConcreteEpochData n) (H : ∀ n, StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S0 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s0Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S0 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s0Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S0 x : ℝ≥0∞)) = fun _ => (s0Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S0 x = s0Cost n := by
      change (D n).stageCosts.s0 x = s0Cost n
      exact (H n).s0 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s0Cost n)).symm

/-- The `S7` mean cost is the deterministic value `s7Cost n`, so the C4 mean
obligation at `S7` is a theorem, not a hypothesis. -/
theorem s7_mean_le (D : ∀ n, ConcreteEpochData n) (H : ∀ n, StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S7 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s7Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S7 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s7Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S7 x : ℝ≥0∞)) = fun _ => (s7Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S7 x = s7Cost n := by
      change (D n).stageCosts.s7 x = s7Cost n
      exact (H n).s7 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s7Cost n)).symm

/-- The proved C4 obligations for a single named stage. -/
structure StageC4Bound (D : ∀ n, ConcreteEpochData n) (C : ℝ) (j : Stage) where
  /-- Weight of the stage at size `n`. -/
  weight : ℕ → ℝ
  /-- Exponential exponent of the stage. -/
  exponent : ℝ
  /-- The exponent is below the ambient ceiling `C`. -/
  exponent_lt : exponent < C
  /-- C4 mean bound. -/
  mean_le : ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
      ENNReal.ofReal (weight n)
  /-- C4 weight bound on the one-third scale. -/
  weight_le : ∀ᶠ n : ℕ in atTop, weight n ≤ exp (exponent * scale n)

/-- **The `S0` C4 slot is discharged** with weight `s0Cost n` and any exponent
`c` with `0 < c < C`. -/
def s0StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S0 where
  weight := fun n => (s0Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s0_mean_le D H n
  weight_le := eventually_s0Cost_le_exp hc

/-- **The `S7` C4 slot is discharged** with weight `s7Cost n` and any exponent
`c` with `0 < c < C`. -/
def s7StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S7 where
  weight := fun n => (s7Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s7_mean_le D H n
  weight_le := eventually_s7Cost_le_exp hc

/-- Weights for all ten stages, overriding `S0` and `S7` with the concrete
costs and leaving the other eight to the caller. -/
def combinedWeight (W : Stage → ℕ → ℝ) : Stage → ℕ → ℝ
  | Stage.S0 => fun n => (s0Cost n : ℝ)
  | Stage.S1 => W Stage.S1
  | Stage.S2 => W Stage.S2
  | Stage.S3 => W Stage.S3
  | Stage.S4 => W Stage.S4
  | Stage.S5 => W Stage.S5
  | Stage.S6 => W Stage.S6
  | Stage.S7 => fun n => (s7Cost n : ℝ)
  | Stage.S8 => W Stage.S8
  | Stage.S9 => W Stage.S9

/-- Exponent assignment overriding `S0` and `S7` with the chosen exponents
`c0`, `c7` and leaving the other eight to the caller. -/
def combinedExponent (c0 c7 : ℝ) (c : Stage → ℝ) : Stage → ℝ
  | Stage.S0 => c0
  | Stage.S1 => c Stage.S1
  | Stage.S2 => c Stage.S2
  | Stage.S3 => c Stage.S3
  | Stage.S4 => c Stage.S4
  | Stage.S5 => c Stage.S5
  | Stage.S6 => c Stage.S6
  | Stage.S7 => c7
  | Stage.S8 => c Stage.S8
  | Stage.S9 => c Stage.S9

/-- **C4 assembly from the two proved slots.**  A full `ConcreteC4Hypotheses`
at ceiling `C` is built from the proved `S0`/`S7` slots and the eight remaining
stages' weights, exponents and eventual bounds.  Only the eight remaining
stages' analytic data is a hypothesis. -/
noncomputable def ConcreteC4Hypotheses.ofS0S7
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ∀ n, StageCostAgreement (D n))
    (W : Stage → ℕ → ℝ) (c : Stage → ℝ)
    (hc : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → c j < C)
    (hmean : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 →
      ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (concreteCostFamily D n hN).actual
            (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
          ENNReal.ofReal (W j n))
    (hW : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 →
      ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    {c0 c7 : ℝ} (hc0 : 0 < c0) (h0C : c0 < C)
    (hc7 : 0 < c7) (h7C : c7 < C) :
    ConcreteC4Hypotheses D C where
  stageWeight := combinedWeight W
  stageExponent := combinedExponent c0 c7 c
  exponent_lt := by
    intro j
    cases j with
    | S0 => exact h0C
    | S1 => exact hc Stage.S1 (by simp) (by simp)
    | S2 => exact hc Stage.S2 (by simp) (by simp)
    | S3 => exact hc Stage.S3 (by simp) (by simp)
    | S4 => exact hc Stage.S4 (by simp) (by simp)
    | S5 => exact hc Stage.S5 (by simp) (by simp)
    | S6 => exact hc Stage.S6 (by simp) (by simp)
    | S7 => exact h7C
    | S8 => exact hc Stage.S8 (by simp) (by simp)
    | S9 => exact hc Stage.S9 (by simp) (by simp)
  mean_le := by
    intro j
    cases j with
    | S0 => exact Filter.Eventually.of_forall fun n => s0_mean_le D H n
    | S1 => exact hmean Stage.S1 (by simp) (by simp)
    | S2 => exact hmean Stage.S2 (by simp) (by simp)
    | S3 => exact hmean Stage.S3 (by simp) (by simp)
    | S4 => exact hmean Stage.S4 (by simp) (by simp)
    | S5 => exact hmean Stage.S5 (by simp) (by simp)
    | S6 => exact hmean Stage.S6 (by simp) (by simp)
    | S7 => exact Filter.Eventually.of_forall fun n => s7_mean_le D H n
    | S8 => exact hmean Stage.S8 (by simp) (by simp)
    | S9 => exact hmean Stage.S9 (by simp) (by simp)
  weight_le := by
    intro j
    cases j with
    | S0 => exact eventually_s0Cost_le_exp hc0
    | S1 => exact hW Stage.S1 (by simp) (by simp)
    | S2 => exact hW Stage.S2 (by simp) (by simp)
    | S3 => exact hW Stage.S3 (by simp) (by simp)
    | S4 => exact hW Stage.S4 (by simp) (by simp)
    | S5 => exact hW Stage.S5 (by simp) (by simp)
    | S6 => exact hW Stage.S6 (by simp) (by simp)
    | S7 => exact eventually_s7Cost_le_exp hc7
    | S8 => exact hW Stage.S8 (by simp) (by simp)
    | S9 => exact hW Stage.S9 (by simp) (by simp)

/-! ## Section 6: Axiom audit -/

#print axioms s0Cost_le_poly
#print axioms eventually_s0Cost_le_exp
#print axioms s7StepOps_le_dim
#print axioms s7Cost_eq
#print axioms s7Cost_le_poly
#print axioms eventually_s7Cost_le_exp
#print axioms s7StepOps_eq_taggedKrylovStep_counts
#print axioms PartialStageCosts.toStageCosts_cost_S0
#print axioms PartialStageCosts.toStageCosts_cost_S7
#print axioms StageCostAgreement.stageDecomposition_cost_S0
#print axioms StageCostAgreement.stageDecomposition_cost_S7
#print axioms StageCostAgreement.s0Cost_le_pubWork
#print axioms StageCostAgreement.s7Cost_le_pubWork
#print axioms familyStageDecomposition_cost_S0
#print axioms familyStageDecomposition_cost_S7
#print axioms familyStageDecomposition_cost_S0_le_poly
#print axioms familyStageDecomposition_cost_S7_le_poly
#print axioms s0_mean_le
#print axioms s7_mean_le
#print axioms s0StageC4Bound
#print axioms s7StageC4Bound
#print axioms ConcreteC4Hypotheses.ofS0S7

end Cogentic.RandomizedConcreteStageCost
