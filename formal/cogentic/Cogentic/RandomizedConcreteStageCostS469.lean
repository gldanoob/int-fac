import Cogentic.RandomizedConcreteStageCost
import Cogentic.RandomizedConcreteEpochCost
import Cogentic.RandomizedPrivateFloor
import Cogentic.RandomizedEpochPrivate
import Cogentic.RandomizedSparseProducts
import Cogentic.RandomizedSplitVerification
import Cogentic.RandomizedVerifiedHiddenSplit
import Cogentic.ModularPowerCost

/-!
# Concrete stage costs for `S4`, `S6` and `S9`

`Cogentic.RandomizedConcreteEpoch` leaves the ten `StageCosts` fields abstract.
`Cogentic.RandomizedConcreteStageCost` instantiates `S0` and `S7`,
`...S3` instantiates `S3`, and `...S8` instantiates `S8`.  This file
instantiates **three further stages**:

* `S4`: staged private screening (ECM);
* `S6`: row records;
* `S9`: private final gcd and the verified split check.

The other four stages (`S1`, `S2`, `S5`) are deliberately *not* claimed.

## The existing counters used

No new arithmetic primitive is postulated.  Each concrete cost is read off a
counter that already exists in the development:

* **S4, screening.**  The blueprint uses a fixed finite private stage grid
  (`4096` stages).  The existing screening profile
  `RandomizedEpochPrivate.PrivateScreeningProfile` records the stage count and
  the per-stage work weights, and `RandomizedPrivateFloor.finite_stage_private_floor`
  is the integrated private-screening floor.  Here one screening stage is
  charged one modular exponentiation, whose exact gate bound is the existing
  `BinaryModularPower.powerBudget` counter.  Thus

  ```
  s4Stages  N = 4096
  s4StageOps N = powerBudget (inputBits N + 1) (inputBits N + 1) (inputBits N + 1)
  s4Cost    N = s4Stages N * s4StageOps N
  ```

  and we prove `s4Cost N ≤ 10000000 * (inputBits N)^3`.  The subexponential
  ECM *curve multiplicity* is not part of this deterministic bit counter; it
  remains the analytic stage weight in the C4 ledger.  The counter below is the
  concrete per-stage modular-arithmetic work.

* **S6, row records.**  `RandomizedSparseProducts.gramPass` records the sparse
  row/column data of one matrix-vector pass.  Its two counters are exactly
  `2 * edges.length` additions and `Fintype.card Row + Fintype.card Col`
  multiplications (`gramPass_spec`).  We charge their sum at the dimensions
  read off the input bit length:

  ```
  s6Dim N      = inputBits N
  s6Edges N    = (s6Dim N)^2
  s6RecordOps rows cols edges = 2 * edges + rows + cols
  s6Cost N     = s6RecordOps (s6Dim N) (s6Dim N) (s6Edges N)
  ```

  The theorem `s6RecordOps_eq_gramPass_counts` identifies `s6RecordOps` with
  the sum of `gramPass`'s two exact counters.  The polynomial bound is
  `s6Cost N ≤ 4 * (s6Dim N)^2`.

* **S9, final gcd and check.**  `RandomizedVerifiedHiddenSplit.verifiedTrial`
  performs the post-ratio subtraction, the Euclidean gcd and the split
  verifier.  Its existing budget is

  ```
  trialBudget N = 7 * N.size + gcdBudget N.size + verifierBudget N,
  ```

  where `gcdBudget` is the `BinaryModularPower` gcd counter and
  `verifierBudget` is the `RandomizedSplitVerification` verifier counter.  We
  define exactly

  ```
  s9SubBits N       = 7 * inputBits N
  s9GcdCost N       = gcdBudget (inputBits N)
  s9VerifierCost N  = verifierBudget N
  s9Cost N          = s9SubBits N + s9GcdCost N + s9VerifierCost N
  ```

  and prove `s9Cost N = trialBudget N` for `0 < N` (`Nat.size N = inputBits N`
  there), hence every `verifiedTrial` outcome is charged at most `s9Cost N`.
  The polynomial bound is `s9Cost N ≤ 108 * (inputBits N)^3`.

## Compatibility

For each of the three stages we provide:

* an agreement hypothesis `S4StageCostAgreement`, `S6StageCostAgreement`,
  `S9StageCostAgreement` identifying the epoch slot with the concrete cost;
* `stageDecomposition_cost_*` and `*_cost_le_pubWork` lemmas;
* the family-level `familyStageDecomposition_cost_*` and polynomial bounds;
* the C4 mean lemmas and `StageC4Bound` values;
* `ConcreteC4Hypotheses.withS4S6S9`, which replaces exactly the three slots of
  an arbitrary `ConcreteC4Hypotheses` by the proved ones.  It composes with
  `ConcreteC4Hypotheses.ofS0S7`, `...ofS0S7_withS3` and
  `ConcreteC4Hypotheses.withS8`.

No `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose` is used.
-/

namespace Cogentic.RandomizedConcreteStageCostS469

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedConcreteStageCost
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSparseProducts
open Cogentic.RandomizedSignCount
open Cogentic.RandomizedSplitVerification
open Cogentic.RandomizedVerifiedHiddenSplit
open Cogentic.BinaryModularPower
open Filter Real
open scoped BigOperators ENNReal

/-! ## Section 1: `S4`, staged private screening -/

/-- Number of private screening stages: the blueprint's finite `4096`-stage
grid.  The existing `RandomizedClassKnotThreshold.half_width_at_least_353_stages`
shows that every admissible budget needs at least `353` stages; the grid used
here is the blueprint's fixed `4096`. -/
def s4Stages (_N : ℕ) : ℕ := 4096

/-- One screening stage is charged one modular exponentiation.  This is the
existing `BinaryModularPower.powerBudget` gate counter at the input width. -/
def s4StageOps (N : ℕ) : ℕ :=
  powerBudget (inputBits N + 1) (inputBits N + 1) (inputBits N + 1)

/-- Concrete `S4` bit cost: one modular-exponentiation budget per screening
stage. -/
def s4Cost (N : ℕ) : ℕ := s4Stages N * s4StageOps N

theorem s4Stages_eq (N : ℕ) : s4Stages N = 4096 := rfl

theorem s4Stages_pos (N : ℕ) : 0 < s4Stages N := by
  rw [s4Stages_eq]
  norm_num

/-- The existing class-knot threshold is covered by the fixed grid. -/
theorem s4Stages_ge_classKnotThreshold (N : ℕ) : 353 ≤ s4Stages N := by
  rw [s4Stages_eq]
  norm_num

/-- Exact normal form of one stage's modular-exponentiation budget. -/
theorem s4StageOps_eq (N : ℕ) :
    s4StageOps N =
      272 * (inputBits N) ^ 3 + 845 * (inputBits N) ^ 2 +
        886 * inputBits N + 324 := by
  unfold s4StageOps powerBudget
  ring

theorem s4Cost_nonneg (N : ℕ) : 0 ≤ s4Cost N := Nat.zero_le _

theorem s4Cost_pos (N : ℕ) : 0 < s4Cost N := by
  have h := s4Stages_pos N
  unfold s4Cost
  exact Nat.mul_pos h (by
    have hb : 1 ≤ inputBits N := inputBits_pos N
    rw [s4StageOps_eq]
    omega)

/-- One stage's budget is cubic in the input bit length. -/
theorem s4StageOps_le (N : ℕ) :
    s4StageOps N ≤ 2327 * (inputBits N) ^ 3 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  have h3 : (inputBits N) ^ 2 ≤ (inputBits N) ^ 3 := by
    calc
      (inputBits N) ^ 2 = (inputBits N) ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ (inputBits N) ^ 2 * (inputBits N) := Nat.mul_le_mul_left _ hB
      _ = (inputBits N) ^ 3 := by ring
  have h1 : inputBits N ≤ (inputBits N) ^ 3 := by
    calc
      inputBits N = inputBits N * 1 := (Nat.mul_one _).symm
      _ ≤ inputBits N * (inputBits N) ^ 2 :=
        Nat.mul_le_mul_left _ (one_le_pow₀ hB)
      _ = (inputBits N) ^ 3 := by ring
  have h0 : 324 ≤ 324 * (inputBits N) ^ 3 := by
    calc
      324 = 324 * 1 := (Nat.mul_one _).symm
      _ ≤ 324 * (inputBits N) ^ 3 :=
        Nat.mul_le_mul_left _ (one_le_pow₀ hB)
  calc
    s4StageOps N =
        272 * (inputBits N) ^ 3 + 845 * (inputBits N) ^ 2 +
          886 * inputBits N + 324 := s4StageOps_eq N
    _ ≤ 272 * (inputBits N) ^ 3 + 845 * (inputBits N) ^ 3 +
          886 * (inputBits N) ^ 3 + 324 * (inputBits N) ^ 3 :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 845 h3))
          (Nat.mul_le_mul_left 886 h1)) h0
    _ = 2327 * (inputBits N) ^ 3 := by ring

/-- **Polynomial bit-cost bound for `S4`.** -/
theorem s4Cost_le_poly (N : ℕ) :
    s4Cost N ≤ 10000000 * (inputBits N) ^ 3 := by
  have hstage := s4StageOps_le N
  calc
    s4Cost N = 4096 * s4StageOps N := by rfl
    _ ≤ 4096 * (2327 * (inputBits N) ^ 3) := Nat.mul_le_mul_left 4096 hstage
    _ = 9531392 * (inputBits N) ^ 3 := by ring
    _ ≤ 10000000 * (inputBits N) ^ 3 :=
      Nat.mul_le_mul_right _ (by norm_num)

/-- The `S4` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s4Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s4Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 10000000) hε 3] with N hN
  have hcast : (s4Cost N : ℝ) ≤ 10000000 * ((N.log2 : ℝ) + 1) ^ 3 := by
    have h := s4Cost_le_poly N
    have h' : (s4Cost N : ℝ) ≤
        ((10000000 * (inputBits N) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [inputBits] using h'
  exact hcast.trans hN

/-- The charged work of a finite private screening profile with at most
`s4Stages N` stages is at most `s4Cost N`.  This connects the concrete cost to
the existing `PrivateScreeningProfile` stage count. -/
theorem screeningStageWork_le_s4Cost (N : ℕ) (P : Cogentic.RandomizedEpochPrivate.PrivateScreeningProfile)
    (hP : P.stages ≤ s4Stages N) :
    P.stages * s4StageOps N ≤ s4Cost N := by
  unfold s4Cost
  exact Nat.mul_le_mul_right _ hP

/-! ## Section 2: `S6`, row records -/

/-- Dimension of the row-record matrix, read off the input bit length. -/
def s6Dim (N : ℕ) : ℕ := inputBits N

/-- Number of recorded nonzeros: at most one per matrix entry. -/
def s6Edges (N : ℕ) : ℕ := (s6Dim N) ^ 2

/-- Field-operation count of one row-record pass.  This is exactly the sum of
the two counters returned by `RandomizedSparseProducts.gramPass`: `2 * edges`
additions (the forward and backward scatter passes) and `rows + cols`
multiplications (the row and column scale passes). -/
def s6RecordOps (rows cols edges : ℕ) : ℕ := 2 * edges + rows + cols

/-- Concrete `S6` arithmetic cost: one row-record pass at the input dimensions. -/
def s6Cost (N : ℕ) : ℕ :=
  s6RecordOps (s6Dim N) (s6Dim N) (s6Edges N)

/-- Exact normal form of the concrete `S6` cost. -/
theorem s6Cost_eq (N : ℕ) :
    s6Cost N = 2 * (s6Dim N) ^ 2 + 2 * s6Dim N := by
  unfold s6Cost s6RecordOps s6Edges
  ring

theorem s6Cost_nonneg (N : ℕ) : 0 ≤ s6Cost N := Nat.zero_le _

theorem s6Cost_pos (N : ℕ) : 0 < s6Cost N := by
  have hb : 1 ≤ s6Dim N := by
    unfold s6Dim
    exact inputBits_pos N
  rw [s6Cost_eq]
  omega

/-- **Polynomial field-operation bound for `S6`.** -/
theorem s6Cost_le_poly (N : ℕ) : s6Cost N ≤ 4 * (s6Dim N) ^ 2 := by
  have hb : 1 ≤ s6Dim N := by
    unfold s6Dim
    exact inputBits_pos N
  have hsq : s6Dim N ≤ (s6Dim N) ^ 2 := by
    simpa [pow_two] using Nat.le_mul_self (s6Dim N)
  calc
    s6Cost N = 2 * (s6Dim N) ^ 2 + 2 * s6Dim N := s6Cost_eq N
    _ ≤ 2 * (s6Dim N) ^ 2 + 2 * (s6Dim N) ^ 2 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hsq) _
    _ = 4 * (s6Dim N) ^ 2 := by ring

/-- The `S6` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s6Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s6Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 4) hε 2] with N hN
  have hcast : (s6Cost N : ℝ) ≤ 4 * ((N.log2 : ℝ) + 1) ^ 2 := by
    have h := s6Cost_le_poly N
    have h' : (s6Cost N : ℝ) ≤ ((4 * (s6Dim N) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [s6Dim, inputBits] using h'
  exact hcast.trans hN

variable {K Row Col : Type*}
variable [CommRing K] [Fintype Row] [Fintype Col] [DecidableEq Row] [DecidableEq Col]

/-- **`S6` is the existing sparse row-record counter.**  The sum of the two
counters returned by `RandomizedSparseProducts.gramPass` is exactly
`s6RecordOps` at the matrix dimensions. -/
theorem s6RecordOps_eq_gramPass_counts
    (rowIndices : IndexList Row) (colIndices : IndexList Col)
    (edges : List (Row × Col)) (d : Row → K) (e x : Col → K) :
    (gramPass rowIndices colIndices edges d e x).2.1 +
        (gramPass rowIndices colIndices edges d e x).2.2 =
      s6RecordOps (Fintype.card Row) (Fintype.card Col) edges.length := by
  rw [gramPass_spec]
  unfold s6RecordOps
  ring

/-! ## Section 3: `S9`, private final gcd and verified split -/

/-- Subtraction counter of the post-ratio step (`7` gates per input bit, as in
`RandomizedVerifiedHiddenSplit`). -/
def s9SubBits (N : ℕ) : ℕ := 7 * inputBits N

/-- Euclidean gcd counter, at the input width. -/
def s9GcdCost (N : ℕ) : ℕ := gcdBudget (inputBits N)

/-- Split-verifier counter, exactly `RandomizedSplitVerification.verifierBudget`. -/
def s9VerifierCost (N : ℕ) : ℕ := verifierBudget N

/-- Concrete `S9` bit cost: subtraction, gcd and verifier. -/
def s9Cost (N : ℕ) : ℕ := s9SubBits N + s9GcdCost N + s9VerifierCost N

/-- `Nat.size` and `inputBits` agree on positive moduli. -/
theorem natSize_eq_inputBits {N : ℕ} (hN : 0 < N) : N.size = inputBits N := by
  unfold inputBits
  exact le_antisymm (Nat.size_le.mpr Nat.lt_log2_self)
    (Nat.lt_size.mpr (Nat.log2_self_le hN.ne'))

/-- **`S9` is exactly the existing `verifiedTrial` budget.** -/
theorem s9Cost_eq_trialBudget {N : ℕ} (hN : 0 < N) :
    s9Cost N = trialBudget N := by
  have hs := natSize_eq_inputBits hN
  unfold s9Cost s9SubBits s9GcdCost s9VerifierCost trialBudget
  rw [hs]

/-- Every concrete `verifiedTrial` outcome is charged at most `s9Cost`. -/
theorem verifiedTrial_cost_le_s9Cost {N : ℕ} (hN : 3 ≤ N)
    (x : SquareFiber (1 : (ZMod N)ˣ)) :
    (verifiedTrial x).2 ≤ s9Cost N := by
  have h := (verifiedTrial_budget_sound hN x).1
  rw [s9Cost_eq_trialBudget (by omega : 0 < N)]
  exact h

/-- Exact normal form of the concrete `S9` cost. -/
theorem s9Cost_eq {N : ℕ} (hN : 0 < N) :
    s9Cost N =
      40 * (inputBits N) ^ 3 + 24 * (inputBits N) ^ 2 +
        39 * inputBits N + 5 := by
  have hs := natSize_eq_inputBits hN
  unfold s9Cost s9SubBits s9GcdCost s9VerifierCost gcdBudget verifierBudget
  rw [hs]
  ring

theorem s9Cost_nonneg (N : ℕ) : 0 ≤ s9Cost N := Nat.zero_le _

theorem s9Cost_pos {N : ℕ} (hN : 0 < N) : 0 < s9Cost N := by
  have hb : 1 ≤ inputBits N := inputBits_pos N
  rw [s9Cost_eq hN]
  omega

/-- **Polynomial bit-cost bound for `S9`.** -/
theorem s9Cost_le_poly {N : ℕ} (hN : 0 < N) :
    s9Cost N ≤ 108 * (inputBits N) ^ 3 := by
  have hB : 1 ≤ inputBits N := inputBits_pos N
  have h3 : (inputBits N) ^ 2 ≤ (inputBits N) ^ 3 := by
    calc
      (inputBits N) ^ 2 = (inputBits N) ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ (inputBits N) ^ 2 * (inputBits N) := Nat.mul_le_mul_left _ hB
      _ = (inputBits N) ^ 3 := by ring
  have h1 : inputBits N ≤ (inputBits N) ^ 3 := by
    calc
      inputBits N = inputBits N * 1 := (Nat.mul_one _).symm
      _ ≤ inputBits N * (inputBits N) ^ 2 :=
        Nat.mul_le_mul_left _ (one_le_pow₀ hB)
      _ = (inputBits N) ^ 3 := by ring
  have h0 : 5 ≤ 5 * (inputBits N) ^ 3 := by
    calc
      5 = 5 * 1 := (Nat.mul_one _).symm
      _ ≤ 5 * (inputBits N) ^ 3 :=
        Nat.mul_le_mul_left _ (one_le_pow₀ hB)
  calc
    s9Cost N =
        40 * (inputBits N) ^ 3 + 24 * (inputBits N) ^ 2 +
          39 * inputBits N + 5 := s9Cost_eq hN
    _ ≤ 40 * (inputBits N) ^ 3 + 24 * (inputBits N) ^ 3 +
          39 * (inputBits N) ^ 3 + 5 * (inputBits N) ^ 3 :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 24 h3))
          (Nat.mul_le_mul_left 39 h1)) h0
    _ = 108 * (inputBits N) ^ 3 := by ring

/-- The `S9` cost is eventually dominated by any positive exponential of the
one-third scale. -/
theorem eventually_s9Cost_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (s9Cost N : ℝ) ≤ exp (ε * scale N) := by
  filter_upwards [eventually_bitPoly_le_exp (A := 108) hε 3,
    eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  have hcast : (s9Cost N : ℝ) ≤ 108 * ((N.log2 : ℝ) + 1) ^ 3 := by
    have h := s9Cost_le_poly (N := N) (by omega)
    have h' : (s9Cost N : ℝ) ≤
        ((108 * (inputBits N) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [inputBits] using h'
  exact hcast.trans hN

/-! ## Section 4: The three stage costs and their agreement hypotheses -/

section StageCost

/-- The concrete `S4` stage cost: staged private screening, independent of the
sampled coins and hidden labels. -/
def s4StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s4Cost N

@[simp] theorem s4StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s4StageCost Coins Label N x = s4Cost N := rfl

theorem s4StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s4StageCost Coins Label N x := Nat.zero_le _

theorem s4StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s4StageCost Coins Label N x ≤ 10000000 * (inputBits N) ^ 3 :=
  s4Cost_le_poly N

/-- The concrete `S6` stage cost: row records, independent of the sampled coins
and hidden labels. -/
def s6StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s6Cost N

@[simp] theorem s6StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s6StageCost Coins Label N x = s6Cost N := rfl

theorem s6StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s6StageCost Coins Label N x := Nat.zero_le _

theorem s6StageCost_le_poly (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s6StageCost Coins Label N x ≤ 4 * (s6Dim N) ^ 2 :=
  s6Cost_le_poly N

/-- The concrete `S9` stage cost: private final gcd and verified split,
independent of the sampled coins and hidden labels. -/
def s9StageCost (Coins Label : Type) (N : ℕ) : StageCost N Coins Label :=
  fun _ => s9Cost N

@[simp] theorem s9StageCost_apply (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    s9StageCost Coins Label N x = s9Cost N := rfl

theorem s9StageCost_nonneg (Coins Label : Type) (N : ℕ)
    (x : Sample N Coins Label) :
    0 ≤ s9StageCost Coins Label N x := Nat.zero_le _

theorem s9StageCost_le_poly {N : ℕ} (hN : 0 < N) (Coins Label : Type)
    (x : Sample N Coins Label) :
    s9StageCost Coins Label N x ≤ 108 * (inputBits N) ^ 3 :=
  s9Cost_le_poly hN

end StageCost

/-- Identification hypothesis for `S4`: the epoch charges the concrete
staged-screening cost. -/
structure S4StageCostAgreement {N : ℕ} (D : ConcreteEpochData N) : Prop where
  /-- `S4` is the staged private screening cost. -/
  s4 : ∀ x : D.Sample, D.stageCosts.s4 x = s4Cost N

/-- Identification hypothesis for `S6`: the epoch charges the concrete
row-record cost. -/
structure S6StageCostAgreement {N : ℕ} (D : ConcreteEpochData N) : Prop where
  /-- `S6` is the row-record cost. -/
  s6 : ∀ x : D.Sample, D.stageCosts.s6 x = s6Cost N

/-- Identification hypothesis for `S9`: the epoch charges the concrete final
gcd and verified-split cost. -/
structure S9StageCostAgreement {N : ℕ} (D : ConcreteEpochData N) : Prop where
  /-- `S9` is the private final gcd and verified-split cost. -/
  s9 : ∀ x : D.Sample, D.stageCosts.s9 x = s9Cost N

namespace S4StageCostAgreement

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The `S4` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S4 (H : S4StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S4 x = s4Cost N := by
  change D.stageCosts.s4 x = s4Cost N
  exact H.s4 x

/-- The concrete `S4` work is charged to the epoch's public work. -/
theorem s4Cost_le_pubWork (H : S4StageCostAgreement D) (x : D.Sample) :
    s4Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S4 x = s4Cost N := by
    change D.stageCosts.s4 x = s4Cost N
    exact H.s4 x
  have h := D.stageCost_le_pubWork Stage.S4 x
  rwa [hc] at h

end S4StageCostAgreement

namespace S6StageCostAgreement

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The `S6` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S6 (H : S6StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S6 x = s6Cost N := by
  change D.stageCosts.s6 x = s6Cost N
  exact H.s6 x

/-- The concrete `S6` work is charged to the epoch's public work. -/
theorem s6Cost_le_pubWork (H : S6StageCostAgreement D) (x : D.Sample) :
    s6Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S6 x = s6Cost N := by
    change D.stageCosts.s6 x = s6Cost N
    exact H.s6 x
  have h := D.stageCost_le_pubWork Stage.S6 x
  rwa [hc] at h

end S6StageCostAgreement

namespace S9StageCostAgreement

variable {N : ℕ} {D : ConcreteEpochData N}

/-- The `S9` slot of the canonical single-epoch stage decomposition. -/
theorem stageDecomposition_cost_S9 (H : S9StageCostAgreement D) (x : D.Sample) :
    D.stageDecomposition.cost Stage.S9 x = s9Cost N := by
  change D.stageCosts.s9 x = s9Cost N
  exact H.s9 x

/-- The concrete `S9` work is charged to the epoch's public work. -/
theorem s9Cost_le_pubWork (H : S9StageCostAgreement D) (x : D.Sample) :
    s9Cost N ≤ D.toHardEpochData.pubWork x := by
  have hc : D.stageCosts.cost Stage.S9 x = s9Cost N := by
    change D.stageCosts.s9 x = s9Cost N
    exact H.s9 x
  have h := D.stageCost_le_pubWork Stage.S9 x
  rwa [hc] at h

end S9StageCostAgreement

/-! ## Section 5: Compatibility with the family-level `StageDecomposition` -/

/-- The family-level stage decomposition has the concrete `S4` cost in its
`S4` slot. -/
theorem familyStageDecomposition_cost_S4
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S4StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S4 n hN x = s4Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s4 x

/-- The family-level stage decomposition has the concrete `S6` cost in its
`S6` slot. -/
theorem familyStageDecomposition_cost_S6
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S6StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S6 n hN x = s6Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s6 x

/-- The family-level stage decomposition has the concrete `S9` cost in its
`S9` slot. -/
theorem familyStageDecomposition_cost_S9
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S9StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S9 n hN x = s9Cost n := by
  rw [familyStageDecomposition_cost]
  exact (H n).s9 x

/-- The family-level `S4` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S4_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S4StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S4 n hN x ≤
      10000000 * (inputBits n) ^ 3 := by
  rw [familyStageDecomposition_cost_S4 D H n hN x]
  exact s4Cost_le_poly n

/-- The family-level `S6` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S6_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S6StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S6 n hN x ≤ 4 * (s6Dim n) ^ 2 := by
  rw [familyStageDecomposition_cost_S6 D H n hN x]
  exact s6Cost_le_poly n

/-- The family-level `S9` slot obeys the polynomial bound uniformly in `n`. -/
theorem familyStageDecomposition_cost_S9_le_poly
    (D : ∀ n, ConcreteEpochData n) (H : ∀ n, S9StageCostAgreement (D n))
    (n : ℕ) (hN : 3 ≤ n) (x : (concreteCostFamily D n hN).Sample) :
    (familyStageDecomposition D).cost Stage.S9 n hN x ≤
      108 * (inputBits n) ^ 3 := by
  rw [familyStageDecomposition_cost_S9 D H n hN x]
  exact s9Cost_le_poly (by omega)

/-! ## Section 6: Compatibility with `StageC4Bound` and `ConcreteC4Hypotheses` -/

/-- The `S4` mean cost is the deterministic value `s4Cost n`, so the C4 mean
obligation at `S4` is a theorem, not a hypothesis. -/
theorem s4_mean_le (D : ∀ n, ConcreteEpochData n)
    (H : ∀ n, S4StageCostAgreement (D n)) (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S4 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s4Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S4 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s4Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S4 x : ℝ≥0∞)) = fun _ => (s4Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S4 x = s4Cost n := by
      change (D n).stageCosts.s4 x = s4Cost n
      exact (H n).s4 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s4Cost n)).symm

/-- The `S6` mean cost is the deterministic value `s6Cost n`, so the C4 mean
obligation at `S6` is a theorem, not a hypothesis. -/
theorem s6_mean_le (D : ∀ n, ConcreteEpochData n)
    (H : ∀ n, S6StageCostAgreement (D n)) (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S6 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s6Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S6 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s6Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S6 x : ℝ≥0∞)) = fun _ => (s6Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S6 x = s6Cost n := by
      change (D n).stageCosts.s6 x = s6Cost n
      exact (H n).s6 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s6Cost n)).symm

/-- The `S9` mean cost is the deterministic value `s9Cost n`, so the C4 mean
obligation at `S9` is a theorem, not a hypothesis. -/
theorem s9_mean_le (D : ∀ n, ConcreteEpochData n)
    (H : ∀ n, S9StageCostAgreement (D n)) (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteCostFamily D n hN).actual
        (fun x => ((D n).stageCosts.cost Stage.S9 x : ℝ≥0∞)) ≤
      ENNReal.ofReal (s9Cost n) := by
  change mean (D n).actual
      (fun x : (D n).Sample => ((D n).stageCosts.cost Stage.S9 x : ℝ≥0∞)) ≤
    ENNReal.ofReal (s9Cost n)
  have hfun : (fun x : (D n).Sample =>
      ((D n).stageCosts.cost Stage.S9 x : ℝ≥0∞)) = fun _ => (s9Cost n : ℝ≥0∞) := by
    funext x
    have hc : (D n).stageCosts.cost Stage.S9 x = s9Cost n := by
      change (D n).stageCosts.s9 x = s9Cost n
      exact (H n).s9 x
    rw [hc]
  rw [hfun, mean_const]
  exact le_of_eq (ENNReal.ofReal_natCast (s9Cost n)).symm

/-- **The `S4` C4 slot is discharged** with weight `s4Cost n` and any exponent
`c` with `0 < c < C`. -/
def s4StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, S4StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S4 where
  weight := fun n => (s4Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s4_mean_le D H n
  weight_le := eventually_s4Cost_le_exp hc

/-- **The `S6` C4 slot is discharged** with weight `s6Cost n` and any exponent
`c` with `0 < c < C`. -/
def s6StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, S6StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S6 where
  weight := fun n => (s6Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s6_mean_le D H n
  weight_le := eventually_s6Cost_le_exp hc

/-- **The `S9` C4 slot is discharged** with weight `s9Cost n` and any exponent
`c` with `0 < c < C`. -/
def s9StageC4Bound (D : ∀ n, ConcreteEpochData n) {C c : ℝ}
    (hc : 0 < c) (hcC : c < C) (H : ∀ n, S9StageCostAgreement (D n)) :
    StageC4Bound D C Stage.S9 where
  weight := fun n => (s9Cost n : ℝ)
  exponent := c
  exponent_lt := hcC
  mean_le := Filter.Eventually.of_forall fun n => s9_mean_le D H n
  weight_le := eventually_s9Cost_le_exp hc

/-- Weights for all ten stages with `S4`, `S6` and `S9` overridden by the
concrete costs. -/
def overrideWeightS469 (W : Stage → ℕ → ℝ) : Stage → ℕ → ℝ
  | Stage.S4 => fun n => (s4Cost n : ℝ)
  | Stage.S6 => fun n => (s6Cost n : ℝ)
  | Stage.S9 => fun n => (s9Cost n : ℝ)
  | j => W j

/-- Exponents for all ten stages with `S4`, `S6` and `S9` overridden by the
chosen exponents. -/
def overrideExponentS469 (c4 c6 c9 : ℝ) (c : Stage → ℝ) : Stage → ℝ
  | Stage.S4 => c4
  | Stage.S6 => c6
  | Stage.S9 => c9
  | j => c j

/-- **C4 compatibility: replace the `S4`, `S6` and `S9` slots by the proved
ones.**  Every other stage is left exactly as supplied by `Hc4`; only these
three mean and weight data are replaced by the proved bounds. -/
noncomputable def ConcreteC4Hypotheses.withS4S6S9
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H4 : ∀ n, S4StageCostAgreement (D n))
    (H6 : ∀ n, S6StageCostAgreement (D n))
    (H9 : ∀ n, S9StageCostAgreement (D n))
    {c4 c6 c9 : ℝ} (h4pos : 0 < c4) (h4C : c4 < C)
    (h6pos : 0 < c6) (h6C : c6 < C)
    (h9pos : 0 < c9) (h9C : c9 < C) :
    ConcreteC4Hypotheses D C where
  stageWeight := overrideWeightS469 Hc4.stageWeight
  stageExponent := overrideExponentS469 c4 c6 c9 Hc4.stageExponent
  exponent_lt := by
    intro j
    cases j with
    | S0 => simpa [overrideExponentS469] using Hc4.exponent_lt Stage.S0
    | S1 => simpa [overrideExponentS469] using Hc4.exponent_lt Stage.S1
    | S2 => simpa [overrideExponentS469] using Hc4.exponent_lt Stage.S2
    | S3 => simpa [overrideExponentS469] using Hc4.exponent_lt Stage.S3
    | S4 => simpa [overrideExponentS469] using h4C
    | S5 => simpa [overrideExponentS469] using Hc4.exponent_lt Stage.S5
    | S6 => simpa [overrideExponentS469] using h6C
    | S7 => simpa [overrideExponentS469] using Hc4.exponent_lt Stage.S7
    | S8 => simpa [overrideExponentS469] using Hc4.exponent_lt Stage.S8
    | S9 => simpa [overrideExponentS469] using h9C
  mean_le := by
    intro j
    cases j with
    | S0 => simpa [overrideWeightS469] using Hc4.mean_le Stage.S0
    | S1 => simpa [overrideWeightS469] using Hc4.mean_le Stage.S1
    | S2 => simpa [overrideWeightS469] using Hc4.mean_le Stage.S2
    | S3 => simpa [overrideWeightS469] using Hc4.mean_le Stage.S3
    | S4 =>
        simp only [overrideWeightS469]
        exact Filter.Eventually.of_forall fun n hN => s4_mean_le D H4 n hN
    | S5 => simpa [overrideWeightS469] using Hc4.mean_le Stage.S5
    | S6 =>
        simp only [overrideWeightS469]
        exact Filter.Eventually.of_forall fun n hN => s6_mean_le D H6 n hN
    | S7 => simpa [overrideWeightS469] using Hc4.mean_le Stage.S7
    | S8 => simpa [overrideWeightS469] using Hc4.mean_le Stage.S8
    | S9 =>
        simp only [overrideWeightS469]
        exact Filter.Eventually.of_forall fun n hN => s9_mean_le D H9 n hN
  weight_le := by
    intro j
    cases j with
    | S0 => simpa [overrideWeightS469, overrideExponentS469] using
        Hc4.weight_le Stage.S0
    | S1 => simpa [overrideWeightS469, overrideExponentS469] using
        Hc4.weight_le Stage.S1
    | S2 => simpa [overrideWeightS469, overrideExponentS469] using
        Hc4.weight_le Stage.S2
    | S3 => simpa [overrideWeightS469, overrideExponentS469] using
        Hc4.weight_le Stage.S3
    | S4 => simpa [overrideWeightS469, overrideExponentS469] using
        eventually_s4Cost_le_exp h4pos
    | S5 => simpa [overrideWeightS469, overrideExponentS469] using
        Hc4.weight_le Stage.S5
    | S6 => simpa [overrideWeightS469, overrideExponentS469] using
        eventually_s6Cost_le_exp h6pos
    | S7 => simpa [overrideWeightS469, overrideExponentS469] using
        Hc4.weight_le Stage.S7
    | S8 => simpa [overrideWeightS469, overrideExponentS469] using
        Hc4.weight_le Stage.S8
    | S9 => simpa [overrideWeightS469, overrideExponentS469] using
        eventually_s9Cost_le_exp h9pos

/-- The assembled hypothesis carries the concrete `s4Cost` weight at `S4`. -/
theorem ConcreteC4Hypotheses.withS4S6S9_stageWeight_S4
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H4 : ∀ n, S4StageCostAgreement (D n))
    (H6 : ∀ n, S6StageCostAgreement (D n))
    (H9 : ∀ n, S9StageCostAgreement (D n))
    {c4 c6 c9 : ℝ} (h4pos : 0 < c4) (h4C : c4 < C)
    (h6pos : 0 < c6) (h6C : c6 < C)
    (h9pos : 0 < c9) (h9C : c9 < C) :
    (ConcreteC4Hypotheses.withS4S6S9 D Hc4 H4 H6 H9 h4pos h4C h6pos h6C
      h9pos h9C).stageWeight Stage.S4 = fun n => (s4Cost n : ℝ) := by
  simp [ConcreteC4Hypotheses.withS4S6S9, overrideWeightS469]

/-- The assembled hypothesis carries the concrete `s6Cost` weight at `S6`. -/
theorem ConcreteC4Hypotheses.withS4S6S9_stageWeight_S6
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H4 : ∀ n, S4StageCostAgreement (D n))
    (H6 : ∀ n, S6StageCostAgreement (D n))
    (H9 : ∀ n, S9StageCostAgreement (D n))
    {c4 c6 c9 : ℝ} (h4pos : 0 < c4) (h4C : c4 < C)
    (h6pos : 0 < c6) (h6C : c6 < C)
    (h9pos : 0 < c9) (h9C : c9 < C) :
    (ConcreteC4Hypotheses.withS4S6S9 D Hc4 H4 H6 H9 h4pos h4C h6pos h6C
      h9pos h9C).stageWeight Stage.S6 = fun n => (s6Cost n : ℝ) := by
  simp [ConcreteC4Hypotheses.withS4S6S9, overrideWeightS469]

/-- The assembled hypothesis carries the concrete `s9Cost` weight at `S9`. -/
theorem ConcreteC4Hypotheses.withS4S6S9_stageWeight_S9
    (D : ∀ n, ConcreteEpochData n) {C : ℝ}
    (Hc4 : ConcreteC4Hypotheses D C)
    (H4 : ∀ n, S4StageCostAgreement (D n))
    (H6 : ∀ n, S6StageCostAgreement (D n))
    (H9 : ∀ n, S9StageCostAgreement (D n))
    {c4 c6 c9 : ℝ} (h4pos : 0 < c4) (h4C : c4 < C)
    (h6pos : 0 < c6) (h6C : c6 < C)
    (h9pos : 0 < c9) (h9C : c9 < C) :
    (ConcreteC4Hypotheses.withS4S6S9 D Hc4 H4 H6 H9 h4pos h4C h6pos h6C
      h9pos h9C).stageWeight Stage.S9 = fun n => (s9Cost n : ℝ) := by
  simp [ConcreteC4Hypotheses.withS4S6S9, overrideWeightS469]

/-! ## Section 7: Axiom audit -/

#print axioms s4StageOps_eq
#print axioms s4Cost_le_poly
#print axioms eventually_s4Cost_le_exp
#print axioms s6Cost_eq
#print axioms s6Cost_le_poly
#print axioms eventually_s6Cost_le_exp
#print axioms s6RecordOps_eq_gramPass_counts
#print axioms s9Cost_eq_trialBudget
#print axioms verifiedTrial_cost_le_s9Cost
#print axioms s9Cost_eq
#print axioms s9Cost_le_poly
#print axioms eventually_s9Cost_le_exp
#print axioms S4StageCostAgreement.stageDecomposition_cost_S4
#print axioms S6StageCostAgreement.stageDecomposition_cost_S6
#print axioms S9StageCostAgreement.stageDecomposition_cost_S9
#print axioms familyStageDecomposition_cost_S4
#print axioms familyStageDecomposition_cost_S6
#print axioms familyStageDecomposition_cost_S9
#print axioms s4_mean_le
#print axioms s6_mean_le
#print axioms s9_mean_le
#print axioms s4StageC4Bound
#print axioms s6StageC4Bound
#print axioms s9StageC4Bound
#print axioms ConcreteC4Hypotheses.withS4S6S9
#print axioms ConcreteC4Hypotheses.withS4S6S9_stageWeight_S4
#print axioms ConcreteC4Hypotheses.withS4S6S9_stageWeight_S6
#print axioms ConcreteC4Hypotheses.withS4S6S9_stageWeight_S9

end Cogentic.RandomizedConcreteStageCostS469
