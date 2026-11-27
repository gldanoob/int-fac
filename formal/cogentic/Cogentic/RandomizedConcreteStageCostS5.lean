import Cogentic.RandomizedConcreteStageCost
import Cogentic.RandomizedLatticeWindow
import Cogentic.RandomizedAffineWindow
import Cogentic.RandomizedLatticePrimitive
import Cogentic.ModularPowerCost

/-!
# Concrete stage cost for `S5` (public descent / lattice sampling)

`Cogentic.RandomizedConcreteEpoch` leaves the ten `StageCosts` fields abstract.
`Cogentic.RandomizedConcreteStageCost` instantiates `S0` and `S7`; the files
`...S1S2`, `...S3`, `...S469` and `...S8` instantiate further stages.  This
file instantiates **one further stage**, `S5`, the public descent / lattice
sampling stage, and proves its polynomial bit-cost bound.  The remaining
stages are deliberately *not* claimed.

## The existing counters used

No new arithmetic primitive is postulated.  The cost is read off two counters
that already exist in the development:

* **Lattice window.**  `Cogentic.randomizedAffineWindowCard` bounds the number
  of integers in an affine window
  `|a * x - c| ≤ T` by `⌊2 * T / |a|⌋₊ + 1`.  At the blueprint's main exponent
  `a = 3/4` (`RandomizedLatticeWindow.latticeWindow_750`) and window halfwidth
  `T = inputBits N`, the deterministic allowance

  ```
  s5CandidateBound N = 3 * inputBits N + 1
  ```

  dominates the existing cardinality counter.  The theorem
  `window_card_le_s5CandidateBound` states this directly for any finite
  candidate set in the window.

* **Primitivity / gcd.**  `RandomizedLatticePrimitive.gcd_lift` shows that a
  primitive lift `h = z * t + j * N` with `t.gcd j = 1` preserves the gcd with
  the modulus, `t.gcd h = t.gcd N`; `reduced_square_congruence` applies the
  same reduction to the congruence.  One primitive candidate therefore needs
  two gcd computations of input-width words, each charged the existing
  `Cogentic.BinaryModularPower.gcdBudget` counter.  Thus

  ```
  s5GcdsPerCandidate N = 2
  s5PrimitiveOps     N = s5GcdsPerCandidate N * gcdBudget (inputBits N)
  s5Cost             N = s5CandidateBound N * s5PrimitiveOps N
  ```

  and the proved bound is

  ```
  s5Cost N ≤ 384 * (inputBits N)^4,
  ```

  hence `s5Cost N ≤ exp (ε * scale N)` eventually for every `ε > 0`.

## What is a hypothesis

The identification of the epoch's `S5` slot with `s5Cost` is the modelling
hypothesis `S5StageCostAgreement`, exactly analogous to `StageCostAgreement`
for `S0`/`S7`.  Nothing analytic (success, TV, hit mass) is asserted, and no
other stage is claimed.  The concrete window input `WindowInput` records the
candidate set and its window containment; its cardinality is bounded by the
existing affine-window theorem, so its gcd cost is bounded by `s5Cost`.

No `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose` is used.
-/

namespace Cogentic.RandomizedConcreteStageCostS5

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedConcreteStageCost
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.BinaryModularPower
open Filter Real
open scoped BigOperators ENNReal

/-! ## Section 1: The concrete `S5` cost -/

/-- The blueprint's main exponent for the lattice window.  This is the value
`a = 3/4` of the explicit witness `RandomizedLatticeWindow.latticeWindow_750`. -/
noncomputable def s5Slope : ℝ := 3 / 4

/-- The chosen slope is the explicit feasible lattice-window witness
`RandomizedLatticeWindow.latticeWindow_750`. -/
theorem s5Slope_latticeWindow :
    Cogentic.Randomized.LatticeWindow s5Slope (5 / 16) (1 / 64) := by
  simpa [s5Slope] using Cogentic.Randomized.latticeWindow_750

/-- The halfwidth of the affine window sampled by `S5`.  One input bit of
halfwidth is the deterministic allowance used by the public descent stage. -/
def s5HalfWidth (N : ℕ) : ℝ := (inputBits N : ℝ)

/-- Deterministic cardinality allowance for the affine window.  The existing
counter `randomizedAffineWindowCard` gives `⌊2 * T / |a|⌋₊ + 1`; at
`a = 3/4` and `T = inputBits N` this is at most `3 * inputBits N + 1`. -/
def s5CandidateBound (N : ℕ) : ℕ := 3 * inputBits N + 1

/-- Number of gcd computations charged to one primitive candidate: the two
gcds `t.gcd j` and `t.gcd N` appearing in `RandomizedLatticePrimitive`. -/
def s5GcdsPerCandidate : ℕ := 2

/-- Bit-operation count of the primitive reduction of one candidate: two
input-width gcds at the existing `gcdBudget` counter. -/
def s5PrimitiveOps (N : ℕ) : ℕ :=
  s5GcdsPerCandidate * gcdBudget (inputBits N)

/-- Concrete `S5` bit cost: every window candidate is charged one primitive
gcd reduction. -/
def s5Cost (N : ℕ) : ℕ := s5CandidateBound N * s5PrimitiveOps N

/-- Exact normal form of the existing `gcdBudget` counter. -/
theorem gcdBudget_eq (W : ℕ) :
    gcdBudget W = 40 * W ^ 3 + 4 * W ^ 2 + 3 * W + 1 := by
  unfold gcdBudget
  ring

/-- The existing gcd counter is cubic in its width. -/
theorem gcdBudget_le (W : ℕ) (hW : 1 ≤ W) :
    gcdBudget W ≤ 48 * W ^ 3 := by
  have h1 : W ≤ W ^ 3 := by
    calc
      W = W * 1 := (Nat.mul_one W).symm
      _ ≤ W * W ^ 2 := Nat.mul_le_mul_left W (one_le_pow₀ hW)
      _ = W ^ 3 := by ring
  have h2 : W ^ 2 ≤ W ^ 3 := by
    calc
      W ^ 2 = W ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ W ^ 2 * W := Nat.mul_le_mul_left _ hW
      _ = W ^ 3 := by ring
  have h0 : 1 ≤ W ^ 3 := one_le_pow₀ hW
  rw [gcdBudget_eq]
  calc
    40 * W ^ 3 + 4 * W ^ 2 + 3 * W + 1
        ≤ 40 * W ^ 3 + 4 * W ^ 3 + 3 * W ^ 3 + W ^ 3 :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 4 h2))
          (Nat.mul_le_mul_left 3 h1)) h0
    _ = 48 * W ^ 3 := by ring

/-- Exact normal form of the per-candidate primitive cost. -/
theorem s5PrimitiveOps_eq (N : ℕ) :
    s5PrimitiveOps N =
      80 * (inputBits N) ^ 3 + 8 * (inputBits N) ^ 2 +
        6 * inputBits N + 2 := by
  unfold s5PrimitiveOps s5GcdsPerCandidate gcdBudget
  ring

theorem s5CandidateBound_pos (N : ℕ) : 0 < s5CandidateBound N := by
  unfold s5CandidateBound
  have hb : 1 ≤ inputBits N := inputBits_pos N
  omega

theorem s5PrimitiveOps_pos (N : ℕ) : 0 < s5PrimitiveOps N := by
  unfold s5PrimitiveOps s5GcdsPerCandidate
  have hb : 1 ≤ inputBits N := inputBits_pos N
  have hg : 0 < gcdBudget (inputBits N) := by
    rw [gcdBudget_eq]
    omega
  exact Nat.mul_pos (by norm_num) hg

theorem s5Cost_nonneg (N : ℕ) : 0 ≤ s5Cost N := Nat.zero_le _

theorem s5Cost_pos (N : ℕ) : 0 < s5Cost N :=
  Nat.mul_pos (s5CandidateBound_pos N) (s5PrimitiveOps_pos N)

/-- The window cardinality allowance is at most four times the input bit
length. -/
theorem s5CandidateBound_le (N : ℕ) :
    s5CandidateBound N ≤ 4 * inputBits N := by
  have hb : 1 ≤ inputBits N := inputBits_pos N
  unfold s5CandidateBound
  calc
    3 * inputBits N + 1 ≤ 3 * inputBits N + inputBits N :=
      Nat.add_le_add_left hb _
    _ = 4 * inputBits N := by ring

/-- The per-candidate primitive cost is cubic in the input bit length. -/
theorem s5PrimitiveOps_le (N : ℕ) :
    s5PrimitiveOps N ≤ 96 * (inputBits N) ^ 3 := by
  have hb : 1 ≤ inputBits N := inputBits_pos N
  have hg := gcdBudget_le (inputBits N) hb
  unfold s5PrimitiveOps s5GcdsPerCandidate
  calc
    2 * gcdBudget (inputBits N) ≤ 2 * (48 * (inputBits N) ^ 3) :=
      Nat.mul_le_mul_left 2 hg
    _ = 96 * (inputBits N) ^ 3 := by ring

/-- **Polynomial bit-cost bound for `S5`.**  Quartic in the input bit length. -/
theorem s5Cost_le_poly (N : ℕ) :
    s5Cost N ≤ 384 * (inputBits N) ^ 4 := by
  have hc := s5CandidateBound_le N
  have hp := s5PrimitiveOps_le N
  calc
    s5Cost N = s5CandidateBound N * s5PrimitiveOps N := rfl
    _ ≤ (4 * inputBits N) * (96 * (inputBits N) ^ 3) :=
      Nat.mul_le_mul hc hp
    _ = 384 * (inputBits N) ^ 4 := by ring

/-- The `S5` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s5Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s5Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 384) hε 4] with N hN
  have hcast : (s5Cost N : ℝ) ≤ 384 * ((N.log2 : ℝ) + 1) ^ 4 := by
    have h := s5Cost_le_poly N
    have h' : (s5Cost N : ℝ) ≤ ((384 * (inputBits N) ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [inputBits] using h'
  exact hcast.trans hN

/-! ## Section 2: The window count is read off the existing lattice counter -/

/-- The existing affine-window cardinality counter at the `S5` slope and
halfwidth. -/
noncomputable def s5WindowCard (N : ℕ) : ℕ :=
  ⌊2 * s5HalfWidth N / |s5Slope|⌋₊ + 1

/-- The existing cardinality counter is below the deterministic `S5`
allowance. -/
theorem s5WindowCard_le (N : ℕ) :
    s5WindowCard N ≤ s5CandidateBound N := by
  have hnonneg : 0 ≤ 2 * s5HalfWidth N / |s5Slope| := by
    unfold s5HalfWidth s5Slope
    positivity
  have hfloor : ((⌊2 * s5HalfWidth N / |s5Slope|⌋₊ : ℕ) : ℝ) ≤
      2 * s5HalfWidth N / |s5Slope| := Nat.floor_le hnonneg
  have hbound : 2 * s5HalfWidth N / |s5Slope| ≤
      3 * (inputBits N : ℝ) := by
    unfold s5HalfWidth s5Slope
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    have hB : (0 : ℝ) ≤ (inputBits N : ℝ) := by positivity
    nlinarith
  have hnat : ⌊2 * s5HalfWidth N / |s5Slope|⌋₊ ≤ 3 * inputBits N := by
    exact_mod_cast (hfloor.trans hbound)
  unfold s5WindowCard s5CandidateBound
  omega

/-- **`S5` window count from the existing affine-window theorem.**  Any finite
set of integers in the affine window `|(3/4) * x - c| ≤ inputBits N` has at
most `s5CandidateBound N` elements.  This is
`Cogentic.randomizedAffineWindowCard` at the `S5` parameters. -/
theorem window_card_le_s5CandidateBound {N : ℕ} {s : Finset ℤ} {c : ℝ}
    (hwindow : ∀ x ∈ s, |s5Slope * (x : ℝ) - c| ≤ s5HalfWidth N) :
    s.card ≤ s5CandidateBound N := by
  have h := randomizedAffineWindowCard (s := s) (a := s5Slope) (c := c)
    (T := s5HalfWidth N) (by unfold s5Slope; norm_num) hwindow
  have h' : s.card ≤ s5WindowCard N := by
    simpa [s5WindowCard] using h
  exact h'.trans (s5WindowCard_le N)

/-! ## Section 3: Primitivity and the concrete window input -/

/-- One primitive lattice candidate: the lift relation and the coprimality
precondition of `RandomizedLatticePrimitive`. -/
structure PrimitiveCandidate (N : ℕ) where
  /-- Lifted coordinate `t`. -/
  t : ℤ
  /-- Lifted coordinate `h`. -/
  h : ℤ
  /-- Shear coefficient `z`. -/
  z : ℤ
  /-- Denominator coefficient `j`. -/
  j : ℤ
  /-- The lattice lift. -/
  lift : h = z * t + j * (N : ℤ)
  /-- Primitivity of `(t, j)`. -/
  primitive : t.gcd j = 1

namespace PrimitiveCandidate

variable {N : ℕ} (P : PrimitiveCandidate N)

/-- **The existing primitivity counter.**  A primitive lift preserves the gcd
with the modulus: `t.gcd h = t.gcd N`.  This is exactly
`Cogentic.RandomizedLatticePrimitive.gcd_lift`. -/
theorem gcd_eq : P.t.gcd P.h = P.t.gcd (N : ℤ) :=
  Cogentic.RandomizedLatticePrimitive.gcd_lift P.lift P.primitive

end PrimitiveCandidate

/-- A concrete `S5` window sample: a finite candidate set together with its
affine-window containment.  The cardinality is controlled by the existing
lattice-window counter, and each candidate is charged the primitive gcd cost. -/
structure WindowInput (N : ℕ) where
  /-- The integer candidates present in the window. -/
  candidates : Finset ℤ
  /-- The affine centre of the window. -/
  center : ℝ
  /-- Every candidate lies in the halfwidth-`s5HalfWidth N` window. -/
  inWindow : ∀ x ∈ candidates,
    |s5Slope * (x : ℝ) - center| ≤ s5HalfWidth N

namespace WindowInput

variable {N : ℕ} (F : WindowInput N)

/-- Number of candidates actually sampled. -/
def card : ℕ := F.candidates.card

/-- Concrete gcd cost of this window sample. -/
def gcdCost : ℕ := F.card * s5PrimitiveOps N

/-- The actual candidate count is within the `S5` window allowance. -/
theorem card_le : F.card ≤ s5CandidateBound N :=
  window_card_le_s5CandidateBound F.inWindow

/-- The concrete window cost is pointwise below the stage cost `s5Cost`. -/
theorem gcdCost_le_s5Cost : F.gcdCost ≤ s5Cost N := by
  unfold gcdCost s5Cost
  exact Nat.mul_le_mul_right (s5PrimitiveOps N) F.card_le

end WindowInput

/-! ## Section 4: The `S5` stage cost and its agreement hypothesis -/

/-- The concrete `S5` stage cost: public descent / lattice sampling, a
deterministic function of the input size alone. -/
def s5StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s5Cost N

@[simp] theorem s5StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s5StageCost Coins Label N x = s5Cost N := rfl

theorem s5StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s5StageCost Coins Label N x := Nat.zero_le _

theorem s5StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s5StageCost Coins Label N x ≤ 384 * (inputBits N) ^ 4 :=
  s5Cost_le_poly N

/-- Identification hypothesis: the concrete epoch `D` charges exactly the
deterministic `S5` cost of this file.  This is a modelling statement about
which epoch is being costed, not an analytic estimate. -/
structure S5StageCostAgreement {N : ℕ} (D : ConcreteEpochData N) : Prop where
  /-- `S5` is the public descent / lattice sampling cost. -/
  s5 : ∀ x : D.Sample, D.stageCosts.s5 x = s5Cost N

namespace S5StageCostAgreement

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The `S5` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S5 (H : S5StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S5 x = s5Cost N := by
  change D.stageCosts.s5 x = s5Cost N
  exact H.s5 x

/-- The concrete `S5` work is charged to the epoch's public work. -/
theorem s5Cost_le_pubWork (H : S5StageCostAgreement D) (x : D.Sample) :
    s5Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S5 x = s5Cost N := by
    change D.stageCosts.s5 x = s5Cost N
    exact H.s5 x
  have h := D.stageCost_le_pubWork Stage.S5 x
  rwa [hc] at h

end S5StageCostAgreement

/-! ## Section 5: Compatibility with the family-level `StageDecomposition` -/

/-- The family-level stage decomposition has the concrete `S5` cost in its `S5`
slot. -/
theorem familyStageDecomposition_cost_S5
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S5StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S5 n hN x = s5Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s5 x

/-- The family-level `S5` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S5_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S5StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S5 n hN x ≤
      384 * (inputBits n) ^ 4 := by
  rw [familyStageDecomposition_cost_S5 D H n hN x]
  exact s5Cost_le_poly n

/-! ## Section 6: Compatibility with `StageC4Bound` and `ConcreteC4Hypotheses` -/

/-- The `S5` mean cost is the deterministic value `s5Cost n`, so the C4 mean
obligation at `S5` is a theorem, not a hypothesis. -/
theorem s5_mean_le (D : ∀ n, ConcreteEpochData n)
    (H : ∀ n, S5StageCostAgreement (D n)) (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S5 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s5Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S5 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s5Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S5 x : ℝ≥0∞)) = fun _ => (s5Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S5 x = s5Cost n := by
      change (D n).stageCosts.s5 x = s5Cost n
      exact (H n).s5 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s5Cost n)).symm

/-- **The `S5` C4 slot is discharged** with weight `s5Cost n` and any exponent
`c` with `0 < c < C`. -/
def s5StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, S5StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S5 where
  weight := fun n => (s5Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s5_mean_le D H n
  weight_le := eventually_s5Cost_le_exp hc

/-- Weights for all ten stages with `S5` overridden by the concrete cost. -/
def overrideWeightS5 (W : Stage → ℕ → ℝ) : Stage → ℕ → ℝ
  | Stage.S5 => fun n => (s5Cost n : ℝ)
  | j => W j

/-- Exponents for all ten stages with `S5` overridden by the chosen exponent. -/
def overrideExponentS5 (c5 : ℝ) (c : Stage → ℝ) : Stage → ℝ
  | Stage.S5 => c5
  | j => c j

/-- **C4 compatibility: replace the `S5` slot by the proved one.**  Every other
stage is left exactly as supplied by `Hc4`; only the `S5` mean and weight data
are replaced by `s5_mean_le` and `eventually_s5Cost_le_exp`. -/
noncomputable def ConcreteC4Hypotheses.withS5
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H5 : ∀ n, S5StageCostAgreement (D n))
    {c5 : ℝ} (hc5 : 0 < c5) (h5C : c5 < C) :
    ConcreteC4Hypotheses D C where
  stageWeight := overrideWeightS5 Hc4.stageWeight
  stageExponent := overrideExponentS5 c5 Hc4.stageExponent
  exponent_lt := by
    intro j
    cases j with
    | S0 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S0
    | S1 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S1
    | S2 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S2
    | S3 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S3
    | S4 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S4
    | S5 => simpa [overrideExponentS5] using h5C
    | S6 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S6
    | S7 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S7
    | S8 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S8
    | S9 => simpa [overrideExponentS5] using Hc4.exponent_lt Stage.S9
  mean_le := by
    intro j
    cases j with
    | S0 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S0
    | S1 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S1
    | S2 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S2
    | S3 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S3
    | S4 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S4
    | S5 =>
        simp only [overrideWeightS5]
        exact Filter.Eventually.of_forall fun n hN => s5_mean_le D H5 n hN
    | S6 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S6
    | S7 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S7
    | S8 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S8
    | S9 => simpa [overrideWeightS5] using Hc4.mean_le Stage.S9
  weight_le := by
    intro j
    cases j with
    | S0 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S0
    | S1 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S1
    | S2 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S2
    | S3 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S3
    | S4 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S4
    | S5 => simpa [overrideWeightS5, overrideExponentS5] using
        eventually_s5Cost_le_exp hc5
    | S6 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S6
    | S7 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S7
    | S8 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S8
    | S9 => simpa [overrideWeightS5, overrideExponentS5] using Hc4.weight_le Stage.S9

/-- The assembled hypothesis carries the concrete `s5Cost` weight at `S5`. -/
theorem ConcreteC4Hypotheses.withS5_stageWeight_S5
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H5 : ∀ n, S5StageCostAgreement (D n))
    {c5 : ℝ} (hc5 : 0 < c5) (h5C : c5 < C) :
    (ConcreteC4Hypotheses.withS5 D Hc4 H5 hc5 h5C).stageWeight Stage.S5 =
      fun n => (s5Cost n : ℝ) := by
  simp [ConcreteC4Hypotheses.withS5, overrideWeightS5]

/-- **Compatibility with the existing `S0`/`S7` assembly.**  A full
`ConcreteC4Hypotheses` is obtained from `ConcreteC4Hypotheses.ofS0S7` after
filling the `S5` slot concretely.  The caller supplies the analytic data for
the remaining stages; the `S5` mean and weight bounds are proved here from
`S5StageCostAgreement`. -/
noncomputable def ConcreteC4Hypotheses.ofS0S7_withS5
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ∀ n, StageCostAgreement (D n))
    (H5 : ∀ n, S5StageCostAgreement (D n))
    (W : Stage → ℕ → ℝ) (c : Stage → ℝ)
    (hW5 : W Stage.S5 = fun n => (s5Cost n : ℝ))
    (hc5pos : 0 < c Stage.S5) (hc5C : c Stage.S5 < C)
    (hc : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S5 → c j < C)
    (hmean : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S5 →
      ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (concreteCostFamily D n hN).actual
            (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
          ENNReal.ofReal (W j n))
    (hW : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S5 →
      ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    {c0 c7 : ℝ} (hc0 : 0 < c0) (h0C : c0 < C)
    (hc7 : 0 < c7) (h7C : c7 < C) :
    ConcreteC4Hypotheses D C := by
  refine ConcreteC4Hypotheses.ofS0S7 D H W c ?_ ?_ ?_ hc0 h0C hc7 h7C
  · intro j hj0 hj7
    by_cases hj5 : j = Stage.S5
    · subst j
      exact hc5C
    · exact hc j hj0 hj7 hj5
  · intro j hj0 hj7
    by_cases hj5 : j = Stage.S5
    · subst j
      simpa only [hW5] using
        (Filter.Eventually.of_forall fun n => s5_mean_le D H5 n)
    · exact hmean j hj0 hj7 hj5
  · intro j hj0 hj7
    by_cases hj5 : j = Stage.S5
    · subst j
      simpa only [hW5] using eventually_s5Cost_le_exp hc5pos
    · exact hW j hj0 hj7 hj5

/-- The assembled `S0`/`S7`/`S5` hypothesis really carries the concrete
`s5Cost` weight at `S5`. -/
theorem ConcreteC4Hypotheses.ofS0S7_withS5_stageWeight_S5
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (H : ∀ n, StageCostAgreement (D n))
    (H5 : ∀ n, S5StageCostAgreement (D n))
    (W : Stage → ℕ → ℝ) (c : Stage → ℝ)
    (hW5 : W Stage.S5 = fun n => (s5Cost n : ℝ))
    (hc5pos : 0 < c Stage.S5) (hc5C : c Stage.S5 < C)
    (hc : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S5 → c j < C)
    (hmean : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S5 →
      ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (concreteCostFamily D n hN).actual
            (fun x => ((D n).stageCosts.cost j x : ℝ≥0∞)) ≤
          ENNReal.ofReal (W j n))
    (hW : ∀ j, j ≠ Stage.S0 → j ≠ Stage.S7 → j ≠ Stage.S5 →
      ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    {c0 c7 : ℝ} (hc0 : 0 < c0) (h0C : c0 < C)
    (hc7 : 0 < c7) (h7C : c7 < C) :
    (ConcreteC4Hypotheses.ofS0S7_withS5 D H H5 W c hW5 hc5pos hc5C hc hmean hW
      hc0 h0C hc7 h7C).stageWeight Stage.S5 = fun n => (s5Cost n : ℝ) := by
  simp [ConcreteC4Hypotheses.ofS0S7_withS5, ConcreteC4Hypotheses.ofS0S7,
    combinedWeight, hW5]

/-! ## Section 7: Axiom audit -/

#print axioms s5Slope_latticeWindow
#print axioms gcdBudget_eq
#print axioms gcdBudget_le
#print axioms s5PrimitiveOps_eq
#print axioms s5Cost_le_poly
#print axioms eventually_s5Cost_le_exp
#print axioms s5WindowCard_le
#print axioms window_card_le_s5CandidateBound
#print axioms PrimitiveCandidate.gcd_eq
#print axioms WindowInput.card_le
#print axioms WindowInput.gcdCost_le_s5Cost
#print axioms S5StageCostAgreement.stageDecomposition_cost_S5
#print axioms S5StageCostAgreement.s5Cost_le_pubWork
#print axioms familyStageDecomposition_cost_S5
#print axioms familyStageDecomposition_cost_S5_le_poly
#print axioms s5_mean_le
#print axioms s5StageC4Bound
#print axioms ConcreteC4Hypotheses.withS5
#print axioms ConcreteC4Hypotheses.withS5_stageWeight_S5
#print axioms ConcreteC4Hypotheses.ofS0S7_withS5
#print axioms ConcreteC4Hypotheses.ofS0S7_withS5_stageWeight_S5

end Cogentic.RandomizedConcreteStageCostS5
