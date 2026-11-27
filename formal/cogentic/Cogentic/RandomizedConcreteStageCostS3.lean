import Cogentic.RandomizedConcreteStageCost
import Cogentic.RandomizedFormReduction
import Cogentic.RandomizedFormReductionSize

/-!
# Concrete stage cost for `S3` (private reduced-form Gauss reduction)

`Cogentic.RandomizedConcreteEpoch` leaves the ten `StageCosts` fields abstract.
`Cogentic.RandomizedConcreteStageCost` instantiates `S0` and `S7`.  This file
instantiates **one further stage**, `S3`, the private reduced-form sampler /
Gauss reduction, and proves its polynomial bit-cost bound.  The other seven
stages are deliberately *not* claimed.

## The cost model

`RandomizedFormReduction.strictSwapCount` is the number of strict swaps in the
certified Gauss reduction of an integral positive-definite form `(a,b,c)`.  The
existing step-count estimate is

```
strictSwapCount a b c ha hdisc ≤ a.toNat.log2 + 1
```

(`RandomizedFormReduction.strictSwapCount_le_log2`).  A reduction consists of one
centering step per level of the recursion, i.e. one after the last strict swap
as well, so the number of centering steps is `strictSwapCount + 1`.  If the
input lead satisfies `a.toNat ≤ N` (for a modulus of bit length
`inputBits N = ⌊log₂ N⌋ + 1`), then

```
strictSwapCount + 1 ≤ inputBits N + 1 = s3Steps N.
```

Each centering step divides `(b + (a-1)/2)` by `a`, and evaluates
`c + 2*b*k + a*k²`; the integers occurring in these operations have at most
`2 * inputBits N` bits (products of two coefficient-sized words).  Charging
four schoolbook multiplications/divisions of such words per step gives
`4 * (2 * inputBits N)² = 16 * (inputBits N)²` bit operations, and one bit per
input bit to emit the form.  Thus

```
s3WordBits N = 2 * inputBits N
s3StepOps  N = 4 * (s3WordBits N)^2
s3Steps    N = inputBits N + 1
s3Cost     N = inputBits N + s3Steps N * s3StepOps N
```

and the proved bound is

```
s3Cost N ≤ 33 * (inputBits N)^3,
```

hence `s3Cost N ≤ exp (ε * scale N)` eventually for every `ε > 0`.

## What is a hypothesis

The only size input to the step count is `a.toNat ≤ N`, bundled in
`ReductionInput`.  The identification of the epoch's `S3` slot with `s3Cost` is
the modelling hypothesis `S3StageCostAgreement`, exactly analogous to
`StageCostAgreement` for `S0`/`S7`.  Nothing analytic (success, TV, hit mass) is
asserted, and no other stage is claimed.

No `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose` is used.
-/

namespace Cogentic.RandomizedConcreteStageCostS3

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedConcreteStageCost
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFormReduction
open Cogentic.RandomizedOneThirdAsymptotic
open Filter Real
open scoped BigOperators ENNReal

/-! ## Section 1: The concrete `S3` cost -/

/-- Number of centering levels available to the reducer: the strict swaps are
bounded by `inputBits N`, and one terminal centering step follows the last
swap. -/
def s3Steps (N : ℕ) : ℕ := inputBits N + 1

/-- Word width used by one centering step.  The shear and the trailing
coefficient involve products of two coefficient-sized integers, so two input
words suffice. -/
def s3WordBits (N : ℕ) : ℕ := 2 * inputBits N

/-- Bit-operation count of one centering step: four schoolbook
multiplications/divisions of `s3WordBits N`-bit words. -/
def s3StepOps (N : ℕ) : ℕ := 4 * (s3WordBits N) ^ 2

/-- Bit cost of emitting the input form, one operation per input bit. -/
def s3ConstructBits (N : ℕ) : ℕ := inputBits N

/-- Concrete `S3` bit cost: form construction plus the reduction steps times
the per-step arithmetic count. -/
def s3Cost (N : ℕ) : ℕ :=
  s3ConstructBits N + s3Steps N * s3StepOps N

/-- Exact normal form of the per-step count. -/
theorem s3StepOps_eq (N : ℕ) :
    s3StepOps N = 16 * (inputBits N) ^ 2 := by
  unfold s3StepOps s3WordBits
  ring

/-- Exact normal form of the concrete `S3` cost. -/
theorem s3Cost_eq (N : ℕ) :
    s3Cost N = inputBits N + 16 * (inputBits N) ^ 2 * (inputBits N + 1) := by
  unfold s3Cost s3ConstructBits s3Steps s3StepOps s3WordBits
  ring

theorem s3Cost_nonneg (N : ℕ) : 0 ≤ s3Cost N := Nat.zero_le _

theorem s3Cost_pos (N : ℕ) : 0 < s3Cost N := by
  have hb : 1 ≤ inputBits N := inputBits_pos N
  rw [s3Cost_eq]
  omega

/-- The polynomial bit-cost bound for `S3`: cubic in the input bit length. -/
theorem s3Cost_le_poly (N : ℕ) :
    s3Cost N ≤ 33 * (inputBits N) ^ 3 := by
  have hb : 1 ≤ inputBits N := inputBits_pos N
  have hb3 : inputBits N ≤ (inputBits N) ^ 3 := by
    calc
      inputBits N = inputBits N * 1 := (Nat.mul_one _).symm
      _ ≤ inputBits N * (inputBits N) ^ 2 :=
        Nat.mul_le_mul_left _ (one_le_pow₀ hb)
      _ = (inputBits N) ^ 3 := by ring
  have hprod : 16 * (inputBits N) ^ 2 * (inputBits N + 1) ≤
      32 * (inputBits N) ^ 3 := by
    have hb1 : inputBits N + 1 ≤ 2 * inputBits N := by omega
    calc
      16 * (inputBits N) ^ 2 * (inputBits N + 1)
          ≤ 16 * (inputBits N) ^ 2 * (2 * inputBits N) :=
            Nat.mul_le_mul_left _ hb1
      _ = 32 * (inputBits N) ^ 3 := by ring
  calc
    s3Cost N
        = inputBits N + 16 * (inputBits N) ^ 2 * (inputBits N + 1) := s3Cost_eq N
    _ ≤ (inputBits N) ^ 3 + 32 * (inputBits N) ^ 3 := Nat.add_le_add hb3 hprod
    _ = 33 * (inputBits N) ^ 3 := by ring

/-- The `S3` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s3Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s3Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 33) hε 3] with N hN
  have hcast : (s3Cost N : ℝ) ≤ 33 * ((N.log2 : ℝ) + 1) ^ 3 := by
    have h := s3Cost_le_poly N
    have h' : (s3Cost N : ℝ) ≤ ((33 * (inputBits N) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [inputBits] using h'
  exact hcast.trans hN

/-! ## Section 2: The existing reduction step count is below `s3Steps` -/

/-- Monotonicity of `Nat.log2`, not available under this name in the imported
core library. -/
theorem log2_le_log2 {m n : ℕ} (h : m ≤ n) : m.log2 ≤ n.log2 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono (by norm_num) (by norm_num) h

/-- The strict-swap count of any form with lead at most `N` is below the `S3`
strict-swap budget `inputBits N`. -/
theorem strictSwapCount_le_inputBits {a b c : ℤ} {N : ℕ}
    (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) (hlead : a.toNat ≤ N) :
    strictSwapCount a b c ha hdisc ≤ inputBits N := by
  have h := strictSwapCount_le_log2 a b c ha hdisc
  have hmono : a.toNat.log2 ≤ N.log2 := log2_le_log2 hlead
  unfold inputBits
  omega

/-- A complete reduction has one centering step per strict swap plus a terminal
centering step, so its total step count is at most `s3Steps N`. -/
theorem strictSwapCount_add_one_le_s3Steps {a b c : ℤ} {N : ℕ}
    (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) (hlead : a.toNat ≤ N) :
    strictSwapCount a b c ha hdisc + 1 ≤ s3Steps N := by
  have h := strictSwapCount_le_inputBits ha hdisc hlead
  unfold s3Steps
  omega

/-- One concrete reduction instance: an integral positive-definite form whose
lead is at most the modulus `N`.  Positivity and definiteness are the exact
preconditions of `RandomizedFormReduction.reduce`; `lead_le` is the size input
to the step-count estimate. -/
structure ReductionInput (N : ℕ) where
  /-- Leading coefficient. -/
  a : ℤ
  /-- Middle coefficient. -/
  b : ℤ
  /-- Trailing coefficient. -/
  c : ℤ
  /-- The lead is positive. -/
  ha : 0 < a
  /-- The form is positive definite. -/
  hdisc : 0 < a * c - b ^ 2
  /-- The lead fits in the modulus size. -/
  lead_le : a.toNat ≤ N

namespace ReductionInput

variable {N : ℕ} (F : ReductionInput N)

/-- Number of centering steps actually performed on this input: one per strict
swap plus the terminal step. -/
def stepCount : ℕ :=
  strictSwapCount F.a F.b F.c F.ha F.hdisc + 1

/-- The step count of the concrete reducer is within the `S3` budget. -/
theorem stepCount_le_s3Steps : F.stepCount ≤ s3Steps N :=
  strictSwapCount_add_one_le_s3Steps F.ha F.hdisc F.lead_le

/-- Bit cost of reducing this concrete input. -/
def cost : ℕ := s3ConstructBits N + F.stepCount * s3StepOps N

/-- The concrete reduction cost is pointwise below the stage cost `s3Cost`. -/
theorem cost_le_s3Cost : F.cost ≤ s3Cost N := by
  unfold cost s3Cost
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right (s3StepOps N) F.stepCount_le_s3Steps) _

end ReductionInput

/-! ## Section 3: The `S3` stage cost and its agreement hypothesis -/

/-- The concrete `S3` stage cost: private reduced-form Gauss reduction, a
deterministic function of the input size alone. -/
def s3StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s3Cost N

@[simp] theorem s3StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s3StageCost Coins Label N x = s3Cost N := rfl

theorem s3StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s3StageCost Coins Label N x := Nat.zero_le _

theorem s3StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s3StageCost Coins Label N x ≤ 33 * (inputBits N) ^ 3 :=
  s3Cost_le_poly N

/-- Identification hypothesis: the concrete epoch `D` charges exactly the
deterministic `S3` cost of this file.  This is a modelling statement about
which epoch is being costed, not an analytic estimate. -/
structure S3StageCostAgreement {N : ℕ} (D : ConcreteEpochData N) : Prop where
  /-- `S3` is the private reduced-form Gauss reduction cost. -/
  s3 : ∀ x : D.Sample, D.stageCosts.s3 x = s3Cost N

namespace S3StageCostAgreement

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The `S3` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S3 (H : S3StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S3 x = s3Cost N := by
  change D.stageCosts.s3 x = s3Cost N
  exact H.s3 x

/-- The concrete `S3` work is charged to the epoch's public work. -/
theorem s3Cost_le_pubWork (H : S3StageCostAgreement D) (x : D.Sample) :
    s3Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S3 x = s3Cost N := by
    change D.stageCosts.s3 x = s3Cost N
    exact H.s3 x
  have h := D.stageCost_le_pubWork Stage.S3 x
  rwa [hc] at h

end S3StageCostAgreement

/-! ## Section 4: Compatibility with the family-level `StageDecomposition` -/

/-- The family-level stage decomposition has the concrete `S3` cost in its `S3`
slot. -/
theorem familyStageDecomposition_cost_S3
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S3StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S3 n hN x = s3Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s3 x

/-- The family-level `S3` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S3_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S3StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S3 n hN x ≤ 33 * (inputBits n) ^ 3 := by
  rw [familyStageDecomposition_cost_S3 D H n hN x]
  exact s3Cost_le_poly n

/-! ## Section 5: Compatibility with `ConcreteC4Hypotheses` -/

/-- The `S3` mean cost is the deterministic value `s3Cost n`, so the C4 mean
obligation at `S3` is a theorem, not a hypothesis. -/
theorem s3_mean_le (D : ∀ n, ConcreteEpochData n)
    (H : ∀ n, S3StageCostAgreement (D n)) (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S3 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s3Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S3 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s3Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S3 x : ℝ≥0∞)) = fun _ => (s3Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S3 x = s3Cost n := by
      change (D n).stageCosts.s3 x = s3Cost n
      exact (H n).s3 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s3Cost n)).symm

/-- **The `S3` C4 slot is discharged** with weight `s3Cost n` and any exponent
`c` with `0 < c < C`. -/
def s3StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, S3StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S3 where
  weight := fun n => (s3Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s3_mean_le D H n
  weight_le := eventually_s3Cost_le_exp hc

/-- **Compatibility with the existing S0/S7 assembly.**  A full
`ConcreteC4Hypotheses` is obtained from `ConcreteC4Hypotheses.ofS0S7` after
filling the `S3` slot concretely.  The caller supplies the analytic data for the
seven remaining stages; the `S3` mean and weight bounds are proved here from
`S3StageCostAgreement`.  The hypothesis `W Stage.S3 = s3Cost`, the strict
positivity of `c Stage.S3`, and its bound `c Stage.S3 < C` are the only extra
inputs.

`hmean`/`hW` are asked only for stages other than `S0`, `S7`, `S3`, matching the
pattern of `ConcreteC4Hypotheses.ofS0S7`. -/
noncomputable def ConcreteC4Hypotheses.ofS0S7_withS3
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ∀ n, StageCostAgreement (D n))
    (H3 : ∀ n, S3StageCostAgreement (D n))
    (W : Stage → ℕ → ℝ) (c : Stage → ℝ)
    (hW3 : W Stage.S3 = fun n => (s3Cost n : ℝ))
    (hc3pos : 0 < c Stage.S3) (hc3C : c Stage.S3 < C)
    (hc : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S3 → c j < C)
    (hmean : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S3 →
      ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (concreteCostFamily D n hN).actual
            (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
          ENNReal.ofReal (W j n))
    (hW : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S3 →
      ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    {c0 c7 : ℝ} (hc0 : 0 < c0) (h0C : c0 < C)
    (hc7 : 0 < c7) (h7C : c7 < C) :
    ConcreteC4Hypotheses D C := by
  refine ConcreteC4Hypotheses.ofS0S7 D H W c ?_ ?_ ?_ hc0 h0C hc7 h7C
  · intro j hj0 hj7
    by_cases hj3 : j = Stage.S3
    · subst j
      exact hc3C
    · exact hc j hj0 hj7 hj3
  · intro j hj0 hj7
    by_cases hj3 : j = Stage.S3
    · subst j
      simpa only [hW3] using
        (Filter.Eventually.of_forall fun n => s3_mean_le D H3 n)
    · exact hmean j hj0 hj7 hj3
  · intro j hj0 hj7
    by_cases hj3 : j = Stage.S3
    · subst j
      simpa only [hW3] using eventually_s3Cost_le_exp hc3pos
    · exact hW j hj0 hj7 hj3

/-- The assembled hypothesis really carries the concrete `s3Cost` weight at
`S3`. -/
theorem ConcreteC4Hypotheses.ofS0S7_withS3_stageWeight_S3
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ∀ n, StageCostAgreement (D n))
    (H3 : ∀ n, S3StageCostAgreement (D n))
    (W : Stage → ℕ → ℝ) (c : Stage → ℝ)
    (hW3 : W Stage.S3 = fun n => (s3Cost n : ℝ))
    (hc3pos : 0 < c Stage.S3) (hc3C : c Stage.S3 < C)
    (hc : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S3 → c j < C)
    (hmean : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S3 →
      ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (concreteCostFamily D n hN).actual
            (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
          ENNReal.ofReal (W j n))
    (hW : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S3 →
      ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    {c0 c7 : ℝ} (hc0 : 0 < c0) (h0C : c0 < C)
    (hc7 : 0 < c7) (h7C : c7 < C) :
    (ConcreteC4Hypotheses.ofS0S7_withS3 D H H3 W c hW3 hc3pos hc3C hc hmean hW
      hc0 h0C hc7 h7C).stageWeight Stage.S3 = fun n => (s3Cost n : ℝ) := by
  simp [ConcreteC4Hypotheses.ofS0S7_withS3, ConcreteC4Hypotheses.ofS0S7,
    combinedWeight, hW3]

/-! ## Section 6: Axiom audit -/

#print axioms s3StepOps_eq
#print axioms s3Cost_eq
#print axioms s3Cost_le_poly
#print axioms eventually_s3Cost_le_exp
#print axioms log2_le_log2
#print axioms strictSwapCount_le_inputBits
#print axioms strictSwapCount_add_one_le_s3Steps
#print axioms ReductionInput.stepCount_le_s3Steps
#print axioms ReductionInput.cost_le_s3Cost
#print axioms S3StageCostAgreement.stageDecomposition_cost_S3
#print axioms S3StageCostAgreement.s3Cost_le_pubWork
#print axioms familyStageDecomposition_cost_S3
#print axioms familyStageDecomposition_cost_S3_le_poly
#print axioms s3_mean_le
#print axioms s3StageC4Bound
#print axioms ConcreteC4Hypotheses.ofS0S7_withS3
#print axioms ConcreteC4Hypotheses.ofS0S7_withS3_stageWeight_S3

end Cogentic.RandomizedConcreteStageCostS3
