import Cogentic.RandomizedEpochOutput
import Cogentic.RandomizedEpochSuccess
import Cogentic.RandomizedFieldExtraction
import Cogentic.RandomizedUniversalSchedule
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma

/-!
# Concrete End-to-End Hard-Input Epoch Assembly and Cost-Budget Combiner

This file builds the concrete hard-input epoch interface and cost-budget assembler
connecting all charged components into both:
1. `Cogentic.RandomizedInputDriver.serialized_epoch_from_critical_line` (fixed schedule), and
2. `Cogentic.RandomizedUniversalSchedule.serialized_balancedEnvelopeInfimum_from_critical_line`
   (universal dyadic multiplexer achieving `balancedEnvelopeInfimum`).

Main contents:
1. Exact cubic/quartic polynomial and asymptotic `L_N[1/3, δ]` bounds on
   `RandomizedVerifiedHiddenSplit.trialBudget`.
2. Finite-sum cost-budget combiners (`eventually_finset_sum_le_exp`,
   `eventually_finset_sum_nat_le_exp`, `eventually_mean_finset_sum_le_exp`) and the
   multi-stage private screening cost summation lemma
   (`eventually_multistage_screening_cost_le_exp` and its specialization to
   `BalancedRationalSchedule.Valid`).
3. Concrete `HardEpochData` structure bundling the public transcript space, ideal/actual
   laws, transcript extractor, and charged public work, together with `assembledAttempt`
   and a direct constructor `HardEpochData.ofMultiField` from `PublicMultiFieldTranscript`.
4. End-to-end epoch ratio assembly and serialized factoring theorems for both fixed
   schedules and the universal balanced schedule at `balancedEnvelopeInfimum`.
-/

namespace Cogentic.RandomizedEpochAssembly

open Cogentic.Randomized
open Cogentic.RandomizedCappedEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochKernel
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenLabels
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedSplitVerification
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedVerifiedHiddenSplit
open Filter Real
open scoped BigOperators ENNReal

/-! ## Section 1: Exact Polynomial and Asymptotic Bounds on `trialBudget` -/

/-- Exact cubic expansion of `trialBudget n` in terms of `n.size`. -/
theorem trialBudget_eq_poly (n : ℕ) :
    trialBudget n = 40 * n.size ^ 3 + 24 * n.size ^ 2 + 39 * n.size + 5 := by
  unfold trialBudget BinaryModularPower.gcdBudget verifierBudget
  ring

/-- Universal cubic upper bound on `trialBudget n` in terms of `n.log2 + 2`. -/
theorem trialBudget_le_cubic (n : ℕ) :
    trialBudget n ≤ 40 * (n.log2 + 2) ^ 3 := by
  have hsize : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  have h1 : trialBudget n ≤ 40 * (n.size + 1) ^ 3 := by
    rw [trialBudget_eq_poly]
    have hge : 40 * n.size ^ 3 + 24 * n.size ^ 2 + 39 * n.size + 5 ≤
        40 * n.size ^ 3 + 120 * n.size ^ 2 + 120 * n.size + 40 := by omega
    calc
      40 * n.size ^ 3 + 24 * n.size ^ 2 + 39 * n.size + 5
          ≤ 40 * n.size ^ 3 + 120 * n.size ^ 2 + 120 * n.size + 40 := hge
      _ = 40 * (n.size + 1) ^ 3 := by ring
  exact h1.trans (Nat.mul_le_mul_left 40 (Nat.pow_le_pow_left (by omega) 3))

/-- Universal quartic upper bound on `trialBudget n` in terms of `n.log2 + 2`. -/
theorem trialBudget_le_quartic (n : ℕ) :
    trialBudget n ≤ 40 * (n.log2 + 2) ^ 4 := by
  refine (trialBudget_le_cubic n).trans ?_
  exact Nat.mul_le_mul_left 40 (Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 4))

/-- Sharp cubic bound on `trialBudget n` in terms of `n.log2 + 1` for positive `n`. -/
theorem trialBudget_le_cubic_of_pos {n : ℕ} (hn : 0 < n) :
    trialBudget n ≤ 108 * (n.log2 + 1) ^ 3 := by
  have hsize : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  have hpos : 1 ≤ n.size := Nat.size_pos.mpr hn
  have hsq : n.size ≤ n.size ^ 2 := by nlinarith
  have hcube : n.size ^ 2 ≤ n.size ^ 3 := by nlinarith
  have h1 : trialBudget n ≤ 108 * n.size ^ 3 := by
    rw [trialBudget_eq_poly]
    nlinarith
  exact h1.trans (Nat.mul_le_mul_left 108 (Nat.pow_le_pow_left hsize 3))

/-- Sharp cubic bound on `trialBudget n + 2` in terms of `n.log2 + 1` for positive `n`. -/
theorem trialBudget_add_two_le_cubic_of_pos {n : ℕ} (hn : 0 < n) :
    trialBudget n + 2 ≤ 110 * (n.log2 + 1) ^ 3 := by
  have h1 := trialBudget_le_cubic_of_pos hn
  have hpow : 1 ≤ (n.log2 + 1) ^ 3 := Nat.one_le_pow 3 (n.log2 + 1) (Nat.succ_pos _)
  omega

/-- Post-ratio verification cost `trialBudget n + 2` is eventually absorbed by any
positive `L_N[1/3, δ]` slack. -/
theorem eventually_trialBudget_add_two_le_exp {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ((trialBudget n + 2 : ℕ) : ℝ) ≤ exp (δ * scale n) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_bitPoly_le_exp (A := 110) hδ 3] with n hn hpoly
  have hnat : ((trialBudget n + 2 : ℕ) : ℝ) ≤ 110 * ((n.log2 : ℝ) + 1) ^ 3 := by
    exact_mod_cast trialBudget_add_two_le_cubic_of_pos (by omega : 0 < n)
  exact hnat.trans hpoly

/-- Any positive constant eventually dominates `exp (-δ * scale n)` for `δ > 0`. -/
theorem eventually_exp_neg_le_const {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, exp (-δ * scale n) ≤ c := by
  filter_upwards [scale_grows.eventually_ge_atTop ((-log c) / δ)] with n hscale
  have hmul : -log c ≤ δ * scale n := by
    have h := (div_le_iff₀ hδ).mp hscale
    linarith only [h]
  calc
    exp (-δ * scale n) ≤ exp (log c) := exp_le_exp.mpr (by linarith only [hmul])
    _ = c := exp_log hc

/-! ## Section 2: Cost-Budget Combiner and Multi-Stage Private Screening Summation -/

/-- Total Epoch Cost Budget Combiner (real terms): summing any finite `Finset` of
budget terms that are each eventually `≤ exp (c j * scale n)` with `c j < D` is
eventually `≤ exp (D * scale n)`. -/
theorem eventually_finset_sum_le_exp {ι : Type*} (s : Finset ι)
    (term : ι → ℕ → ℝ) (c : ι → ℝ) {D : ℝ}
    (hc : ∀ j ∈ s, c j < D)
    (hterm : ∀ j ∈ s, ∀ᶠ n : ℕ in atTop, term j n ≤ exp (c j * scale n)) :
    ∀ᶠ n : ℕ in atTop, (∑ j ∈ s, term j n) ≤ exp (D * scale n) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact Filter.Eventually.of_forall fun n => by simp [(exp_pos _).le]
  · let gap : ℝ := s.inf' hs (fun j => D - c j)
    have hgap : 0 < gap := (Finset.lt_inf'_iff hs).mpr fun j hj => sub_pos.mpr (hc j hj)
    have hle (j : ι) (hj : j ∈ s) : c j ≤ D - gap := by
      have h := Finset.inf'_le (f := fun i => D - c i) hj
      linarith only [h]
    have hall : ∀ᶠ n : ℕ in atTop, ∀ j ∈ s, term j n ≤ exp (c j * scale n) :=
      s.eventually_all.mpr hterm
    filter_upwards [hall, scale_grows.eventually_ge_atTop 0,
      eventually_bitPoly_le_exp (A := (s.card : ℝ)) hgap 0] with n hn hscale hcard
    simp only [pow_zero, mul_one] at hcard
    calc
      ∑ j ∈ s, term j n
          ≤ ∑ j ∈ s, exp (c j * scale n) := Finset.sum_le_sum fun j hj => hn j hj
      _ ≤ ∑ _j ∈ s, exp ((D - gap) * scale n) :=
          Finset.sum_le_sum fun j hj =>
            exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hle j hj) hscale)
      _ = (s.card : ℝ) * exp ((D - gap) * scale n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ exp (gap * scale n) * exp ((D - gap) * scale n) :=
          mul_le_mul_of_nonneg_right hcard (exp_pos _).le
      _ = exp (D * scale n) := by
          rw [← exp_add]
          congr 1
          ring

/-- Total Epoch Cost Budget Combiner (`ℕ`-valued terms). -/
theorem eventually_finset_sum_nat_le_exp {ι : Type*} (s : Finset ι)
    (term : ι → ℕ → ℕ) (c : ι → ℝ) {D : ℝ}
    (hc : ∀ j ∈ s, c j < D)
    (hterm : ∀ j ∈ s, ∀ᶠ n : ℕ in atTop, (term j n : ℝ) ≤ exp (c j * scale n)) :
    ∀ᶠ n : ℕ in atTop, ((∑ j ∈ s, term j n : ℕ) : ℝ) ≤ exp (D * scale n) := by
  filter_upwards [eventually_finset_sum_le_exp s (fun j n => (term j n : ℝ)) c hc hterm]
    with n hn
  simpa only [Nat.cast_sum] using hn

/-- Linearity of `PMF` expectation over a finite `Finset` of `ℝ≥0∞`-valued observables. -/
theorem mean_finset_sum {α ι : Type*} (p : PMF α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    mean p (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, mean p (fun x => f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mean_const]
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [mean_add, ih]

/-- Linearity of `PMF` expectation over a finite `Finset` of `ℕ`-valued cost components. -/
theorem mean_finset_sum_nat {α ι : Type*} (p : PMF α) (s : Finset ι) (f : ι → α → ℕ) :
    mean p (fun x => ((∑ j ∈ s, f j x : ℕ) : ℝ≥0∞)) =
      ∑ j ∈ s, mean p (fun x => (f j x : ℝ≥0∞)) := by
  simpa only [Nat.cast_sum] using mean_finset_sum p s (fun j x => (f j x : ℝ≥0∞))

/-- Combine finitely many expected component budgets into one expected public-work
budget `≤ exp (D * scale n)`. -/
theorem eventually_mean_finset_sum_le_exp {ι : Type*} {α : ℕ → Type*}
    (s : Finset ι) (p : ∀ n, PMF (α n)) (work : ι → ∀ n, α n → ℕ)
    (W : ι → ℕ → ℝ) (c : ι → ℝ) {D : ℝ}
    (hc : ∀ j ∈ s, c j < D)
    (hmean : ∀ j ∈ s, ∀ᶠ n : ℕ in atTop,
      mean (p n) (fun x => (work j n x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hW : ∀ j ∈ s, ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n)) :
    ∀ᶠ n : ℕ in atTop,
      ∃ W_tot : ℝ,
        mean (p n) (fun x => ((∑ j ∈ s, work j n x : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal W_tot ∧
        W_tot ≤ exp (D * scale n) := by
  have hallMean : ∀ᶠ n : ℕ in atTop, ∀ j ∈ s,
      mean (p n) (fun x => (work j n x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n) :=
    s.eventually_all.mpr hmean
  have hsum := eventually_finset_sum_le_exp s (fun j n => max 0 (W j n)) c hc
    (fun j hj => by
      filter_upwards [hW j hj] with n hn
      exact max_le (exp_pos _).le hn)
  filter_upwards [hallMean, hsum] with n hm hs
  refine ⟨∑ j ∈ s, max 0 (W j n), ?_, hs⟩
  rw [mean_finset_sum_nat, ENNReal.ofReal_sum_of_nonneg (fun j _ => le_max_left 0 _)]
  exact Finset.sum_le_sum fun j hj =>
    (hm j hj).trans (ENNReal.ofReal_le_ofReal (le_max_right 0 _))

/-- Multi-Stage Private Screening Cost Summation Lemma:
given `k + 1` private screening stages where stage `i ≤ k` has prefix arrival
probability `≤ exp (-(prefixLoss i) * scale n)` and per-stage recognition cost
`≤ exp ((stageCost i) * scale n)`, with `rowExp + η + stageCost i - prefixLoss i < D`
for all `i ≤ k`, the total expected private screening cost over `rows n ≤ exp ((rowExp + η) * scale n)`
rows is eventually `≤ exp (D * scale n)`. -/
theorem eventually_multistage_screening_cost_le_exp
    (k : ℕ) (rowExp η D : ℝ) (prefixLoss stageCost : ℕ → ℝ)
    (rows : ℕ → ℝ) (arrivalProb stageWork : ℕ → ℕ → ℝ)
    (hrows_nn : ∀ᶠ n : ℕ in atTop, 0 ≤ rows n)
    (hprob_nn : ∀ i ≤ k, ∀ᶠ n : ℕ in atTop, 0 ≤ arrivalProb i n)
    (hwork_nn : ∀ i ≤ k, ∀ᶠ n : ℕ in atTop, 0 ≤ stageWork i n)
    (hrows : ∀ᶠ n : ℕ in atTop, rows n ≤ exp ((rowExp + η) * scale n))
    (hprob : ∀ i ≤ k, ∀ᶠ n : ℕ in atTop, arrivalProb i n ≤ exp (-(prefixLoss i) * scale n))
    (hwork : ∀ i ≤ k, ∀ᶠ n : ℕ in atTop, stageWork i n ≤ exp ((stageCost i) * scale n))
    (hcap : ∀ i ≤ k, rowExp + η + stageCost i - prefixLoss i < D) :
    ∀ᶠ n : ℕ in atTop,
      rows n * (∑ i ∈ Finset.range (k + 1), arrivalProb i n * stageWork i n) ≤
        exp (D * scale n) := by
  have hsum := eventually_finset_sum_le_exp (Finset.range (k + 1))
    (fun i n => rows n * (arrivalProb i n * stageWork i n))
    (fun i => rowExp + η + stageCost i - prefixLoss i)
    (fun i hi => hcap i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    (fun i hi => by
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      filter_upwards [hrows_nn, hprob_nn i hik, hwork_nn i hik,
        hrows, hprob i hik, hwork i hik] with n hr0 hp0 hw0 hr hp hw
      have hstage : arrivalProb i n * stageWork i n ≤
          exp ((stageCost i - prefixLoss i) * scale n) := by
        calc
          arrivalProb i n * stageWork i n
              ≤ exp (-(prefixLoss i) * scale n) * exp (stageCost i * scale n) :=
                mul_le_mul hp hw hw0 (exp_pos _).le
          _ = exp ((stageCost i - prefixLoss i) * scale n) := by
                rw [← exp_add]
                congr 1
                ring
      calc
        rows n * (arrivalProb i n * stageWork i n)
            ≤ exp ((rowExp + η) * scale n) * exp ((stageCost i - prefixLoss i) * scale n) :=
              mul_le_mul hr hstage (mul_nonneg hp0 hw0) (exp_pos _).le
        _ = exp ((rowExp + η + stageCost i - prefixLoss i) * scale n) := by
              rw [← exp_add]
              congr 1
              ring)
  filter_upwards [hsum] with n hn
  simpa only [Finset.mul_sum] using hn

/-- Slack-existence form of the Multi-Stage Private Screening Cost Summation Lemma:
strict stage inequalities `rowExp + stageCost i - prefixLoss i < D` for `i ≤ k` yield
a positive slack `η₀ > 0` such that any row-count exponent `rowExp + η` with `η < η₀`
keeps the total expected private screening cost eventually `≤ exp (D * scale n)`. -/
theorem eventually_multistage_screening_cost_le_exp_of_slack
    (k : ℕ) (rowExp D : ℝ) (prefixLoss stageCost : ℕ → ℝ)
    (hcap : ∀ i ≤ k, rowExp + stageCost i - prefixLoss i < D) :
    ∃ η₀ > (0 : ℝ), ∀ η < η₀,
      ∀ (rows : ℕ → ℝ) (arrivalProb stageWork : ℕ → ℕ → ℝ),
        (∀ᶠ n : ℕ in atTop, 0 ≤ rows n) →
        (∀ i ≤ k, ∀ᶠ n : ℕ in atTop, 0 ≤ arrivalProb i n) →
        (∀ i ≤ k, ∀ᶠ n : ℕ in atTop, 0 ≤ stageWork i n) →
        (∀ᶠ n : ℕ in atTop, rows n ≤ exp ((rowExp + η) * scale n)) →
        (∀ i ≤ k, ∀ᶠ n : ℕ in atTop, arrivalProb i n ≤ exp (-(prefixLoss i) * scale n)) →
        (∀ i ≤ k, ∀ᶠ n : ℕ in atTop, stageWork i n ≤ exp ((stageCost i) * scale n)) →
        ∀ᶠ n : ℕ in atTop,
          rows n * (∑ i ∈ Finset.range (k + 1), arrivalProb i n * stageWork i n) ≤
            exp (D * scale n) := by
  have hne : (Finset.range (k + 1)).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero k)
  let η₀ : ℝ := (Finset.range (k + 1)).inf' hne
    (fun i => D - (rowExp + stageCost i - prefixLoss i))
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff hne).mpr fun i hi =>
    sub_pos.mpr (hcap i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  refine ⟨η₀, hη₀, fun η hη rows arrivalProb stageWork hr0 hp0 hw0 hr hp hw => ?_⟩
  refine eventually_multistage_screening_cost_le_exp k rowExp η D prefixLoss stageCost
    rows arrivalProb stageWork hr0 hp0 hw0 hr hp hw fun i hi => ?_
  have hle : η₀ ≤ D - (rowExp + stageCost i - prefixLoss i) :=
    Finset.inf'_le (f := fun j => D - (rowExp + stageCost j - prefixLoss j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  linarith only [hη, hle]

/-- Direct instantiation of the Multi-Stage Private Screening Cost Summation Lemma for
any valid `BalancedRationalSchedule` at target ceiling `D`:
every schedule satisfying `s.Valid D` accommodates row-count slack `η ≤ s.perturbation.q`
(with `0 < s.perturbation.q`) while keeping total expected private screening cost
eventually `≤ exp (D * scale n)`. -/
theorem balancedSchedule_multistage_screening_cost_le_exp
    (s : BalancedRationalSchedule) {D η : ℝ} (hvalid : s.Valid D)
    (hη : η ≤ s.perturbation.q)
    (rows : ℕ → ℝ) (arrivalProb stageWork : ℕ → ℕ → ℝ)
    (hrows_nn : ∀ᶠ n : ℕ in atTop, 0 ≤ rows n)
    (hprob_nn : ∀ i ≤ s.k, ∀ᶠ n : ℕ in atTop, 0 ≤ arrivalProb i n)
    (hwork_nn : ∀ i ≤ s.k, ∀ᶠ n : ℕ in atTop, 0 ≤ stageWork i n)
    (hrows : ∀ᶠ n : ℕ in atTop,
      rows n ≤ exp ((s.perturbation.b + (∑ j ∈ Finset.range (s.k + 1), s.weight j) + η) * scale n))
    (hprob : ∀ i ≤ s.k, ∀ᶠ n : ℕ in atTop,
      arrivalProb i n ≤ exp (-(∑ j ∈ Finset.range i, s.weight j) * scale n))
    (hwork : ∀ i ≤ s.k, ∀ᶠ n : ℕ in atTop,
      stageWork i n ≤ exp ((s.perturbation.h * s.knot (i + 1)) * scale n)) :
    ∀ᶠ n : ℕ in atTop,
      rows n * (∑ i ∈ Finset.range (s.k + 1), arrivalProb i n * stageWork i n) ≤
        exp (D * scale n) := by
  refine eventually_multistage_screening_cost_le_exp s.k
    (s.perturbation.b + ∑ j ∈ Finset.range (s.k + 1), s.weight j) η D
    (fun i => ∑ j ∈ Finset.range i, s.weight j)
    (fun i => s.perturbation.h * s.knot (i + 1))
    rows arrivalProb stageWork hrows_nn hprob_nn hwork_nn hrows hprob hwork ?_
  intro i hi
  have hgate := hvalid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i (Nat.lt_succ_of_le hi)
  have hsplit :
      (∑ j ∈ Finset.range i, s.weight j) + (∑ j ∈ Finset.Ico i (s.k + 1), s.weight j) =
        ∑ j ∈ Finset.range (s.k + 1), s.weight j :=
    Finset.sum_range_add_sum_Ico s.weight (by omega)
  linarith only [hgate, hsplit, hη]

/-! ## Section 3: Concrete Hard-Input Epoch Structure `HardEpochData` and `assembledAttempt` -/

/-- Charged components of ONE hard-input epoch on input `N`:
the public transcript space `(Coins, Label, Public)`, ideal and actual joint laws,
public transcript map `trace`, good-transcript set `good`, transcript verifier data `data`,
and charged public work `pubWork` (covering field-pool setup, private screening,
public descent, sparse Padé/Krylov linear algebra, and multi-field root extraction). -/
structure HardEpochData (N : ℕ) where
  Coins : Type
  Label : Type
  Public : Type
  [fintypeCoins : Fintype Coins]
  [fintypeLabel : Fintype Label]
  [decEqLabel : DecidableEq Label]
  [decEqPublic : DecidableEq Public]
  ideal : PMF (Coins × (Label → (ZMod N)ˣ))
  actual : PMF (Coins × (Label → (ZMod N)ˣ))
  trace : Coins → (Label → (ZMod N)ˣ) → Public
  good : Finset Public
  data : good → TranscriptData Label N
  pubWork : Coins × (Label → (ZMod N)ˣ) → ℕ

namespace HardEpochData

attribute [instance] fintypeCoins fintypeLabel decEqLabel decEqPublic

/-- Sample space of one hard-input epoch on modulus `N`. -/
abbrev Sample {N : ℕ} (E : HardEpochData N) : Type :=
  E.Coins × (E.Label → (ZMod N)ˣ)

/-- Congruence check on every good public transcript: the hidden label product
squares to the transcript's public root. -/
def CongruenceCheck {N : ℕ} (E : HardEpochData N) : Prop :=
  ∀ (t : E.good) x, observe E.trace x = t.val →
    (labelProduct (E.data t).labels (E.data t).multiplicity x.2) ^ 2 = (E.data t).publicRoot ^ 2

/-- Conditional hidden-sign uniformity of the ideal law on every good public transcript. -/
def HiddenUniform {N : ℕ} (E : HardEpochData N) : Prop :=
  ∀ (t : E.good) x y, observe E.trace x = t.val → x.1 = y.1 →
    (x.2 (E.data t).privateIndex) ^ 2 = (y.2 (E.data t).privateIndex) ^ 2 →
    (∀ j, j ≠ (E.data t).privateIndex → x.2 j = y.2 j) → E.ideal x = E.ideal y

/-- Assemble a concrete `HardEpochData` directly from a multi-field extractor
(`RandomizedFieldExtraction.PublicMultiFieldTranscript`). -/
noncomputable def ofMultiField {N : ℕ} {Coins Label FieldId Public : Type}
    [Fintype Coins] [Fintype Label] [DecidableEq Label] [DecidableEq Public]
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (extract : good → PublicMultiFieldTranscript Label FieldId N)
    (pubWork : Coins × (Label → (ZMod N)ˣ) → ℕ) : HardEpochData N where
  Coins := Coins
  Label := Label
  Public := Public
  ideal := ideal
  actual := actual
  trace := trace
  good := good
  data := fun t => (extract t).toTranscriptData
  pubWork := pubWork

/-- The global modular product identity of `PublicMultiFieldTranscript` discharges
`HardEpochData.CongruenceCheck` via `labelProduct_sq_eq_assembled_publicRoot`. -/
theorem ofMultiField_congruenceCheck {N : ℕ} {Coins Label FieldId Public : Type}
    [Fintype Coins] [Fintype Label] [DecidableEq Label] [DecidableEq Public]
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (extract : good → PublicMultiFieldTranscript Label FieldId N)
    (pubWork : Coins × (Label → (ZMod N)ˣ) → ℕ)
    (hglobal : ∀ (t : good) x, observe trace x = t.val →
      (∏ i ∈ (extract t).mask, (x.2 i) ^ 2) =
        (extract t).ratCorr * ∏ j ∈ (extract t).fields, (extract t).fieldProd j) :
    (ofMultiField ideal actual trace good extract pubWork).CongruenceCheck := by
  intro t x hx
  exact labelProduct_sq_eq_assembled_publicRoot
    (extract t).mask (extract t).fields x.2 (fun i => x.2 i ^ 2)
    (extract t).ratCorr (extract t).ratRoot (extract t).fieldProd (extract t).fieldRoot
    (fun _ _ => rfl) (extract t).ratRoot_sq (extract t).fieldRoot_sq (hglobal t x hx)

/-- Coordinatewise hidden-sign symmetry on every mask element discharges
`HardEpochData.HiddenUniform` for `ofMultiField`. -/
theorem ofMultiField_hiddenUniform {N : ℕ} {Coins Label FieldId Public : Type}
    [Fintype Coins] [Fintype Label] [DecidableEq Label] [DecidableEq Public]
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (extract : good → PublicMultiFieldTranscript Label FieldId N)
    (pubWork : Coins × (Label → (ZMod N)ˣ) → ℕ)
    (huniform : ∀ (t : good) x y, observe trace x = t.val → x.1 = y.1 →
      ∀ i ∈ (extract t).mask, (x.2 i) ^ 2 = (y.2 i) ^ 2 →
      (∀ j, j ≠ i → x.2 j = y.2 j) → ideal x = ideal y) :
    (ofMultiField ideal actual trace good extract pubWork).HiddenUniform := by
  intro t x y hx h1 h2 h3
  exact huniform t x y hx h1 (extract t).mask_nonempty.choose
    (extract t).mask_nonempty.choose_spec h2 h3

/-- Assembled hard-input epoch attempt: charges `E.pubWork x` followed by
`RandomizedEpochSuccess.certifiedEpochTrial`, returning the certified proper factor
pair (if any) and total charged work `E.pubWork x + (certifiedEpochTrial ...).2`. -/
noncomputable def assembledAttempt {N : ℕ} (E : HardEpochData N) (hN : 3 ≤ N)
    (x : E.Sample) : Option (Factors N) × ℕ :=
  let res := certifiedEpochTrial hN E.trace E.good E.data x
  (res.1, E.pubWork x + res.2)

/-- Pointwise work bound of `assembledAttempt`: public work plus `trialBudget N`. -/
theorem assembledAttempt_work_le {N : ℕ} (E : HardEpochData N) (hN : 3 ≤ N) (x : E.Sample) :
    (E.assembledAttempt hN x).2 ≤ E.pubWork x + trialBudget N := by
  have hsound := (epochTrial_budget_sound hN E.trace E.good E.data x).1
  unfold assembledAttempt certifiedEpochTrial
  dsimp only
  omega

/-- Expected charged attempt work plus the retry-loop overhead `1 + 1` is bounded by
`max 0 W_pub + trialBudget N + 2`. -/
theorem assembledAttempt_mean_work_le {N : ℕ} (E : HardEpochData N) (hN : 3 ≤ N)
    {W_pub : ℝ}
    (hpub : mean E.actual (fun x => (E.pubWork x : ℝ≥0∞)) ≤ ENNReal.ofReal W_pub) :
    mean E.actual (fun x => (((E.assembledAttempt hN x).2 + 1 : ℕ) : ℝ≥0∞)) + 1 ≤
      ENNReal.ofReal (max 0 W_pub + ((trialBudget N + 2 : ℕ) : ℝ)) := by
  have hpt (x : E.Sample) :
      (((E.assembledAttempt hN x).2 + 1 : ℕ) : ℝ≥0∞) ≤
        (E.pubWork x : ℝ≥0∞) + ((trialBudget N + 1 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_add]
    exact Nat.cast_le.mpr (by have := E.assembledAttempt_work_le hN x; omega)
  have hmono :
      mean E.actual (fun x => (((E.assembledAttempt hN x).2 + 1 : ℕ) : ℝ≥0∞)) ≤
        mean E.actual (fun x => (E.pubWork x : ℝ≥0∞) + ((trialBudget N + 1 : ℕ) : ℝ≥0∞)) :=
    ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hpt x) (E.actual x)
  have hsum :
      mean E.actual (fun x => (E.pubWork x : ℝ≥0∞) + ((trialBudget N + 1 : ℕ) : ℝ≥0∞)) + 1 =
        mean E.actual (fun x => (E.pubWork x : ℝ≥0∞)) + ((trialBudget N + 2 : ℕ) : ℝ≥0∞) := by
    rw [mean_add, mean_const, add_assoc]
    congr 1
    norm_cast
  calc
    mean E.actual (fun x => (((E.assembledAttempt hN x).2 + 1 : ℕ) : ℝ≥0∞)) + 1
        ≤ mean E.actual (fun x => (E.pubWork x : ℝ≥0∞)) + ((trialBudget N + 2 : ℕ) : ℝ≥0∞) :=
          (add_le_add_left hmono 1).trans_eq hsum
    _ ≤ ENNReal.ofReal (max 0 W_pub) + ENNReal.ofReal ((trialBudget N + 2 : ℕ) : ℝ) := by
          refine add_le_add (hpub.trans (ENNReal.ofReal_le_ofReal (le_max_right 0 W_pub))) ?_
          rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (max 0 W_pub + ((trialBudget N + 2 : ℕ) : ℝ)) := by
          rw [ENNReal.ofReal_add (le_max_left 0 W_pub) (Nat.cast_nonneg _)]

/-- `assembledAttempt` accepts on the exact same sample outcomes as `epochTrial`. -/
theorem assembledAttempt_hit_prob_eq {N : ℕ} (E : HardEpochData N) (hN : 3 ≤ N) :
    ((E.actual.map (E.assembledAttempt hN)).toOuterMeasure {o | o.1 ≠ none}).toReal =
      ((E.actual.map (epochTrial E.trace E.good E.data)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  congr 2
  ext x
  exact certifiedEpochTrial_accepts hN E.trace E.good E.data x

/-- Observed verified split probability of `assembledAttempt` under the actual law,
obtained from `RandomizedEpochSuccess.epoch_verified_split_probability_half` after
discarding zero-ideal-mass transcripts from `E.good`. -/
theorem assembledAttempt_hit_prob_ge {N : ℕ} (E : HardEpochData N)
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬IsPrimePow N)
    (hcheck : E.CongruenceCheck) (huniform : E.HiddenUniform)
    {γ ε : ℝ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (E.ideal.toOuterMeasure {x | observe E.trace x ∈ E.good}).toReal)
    (hTV : pmfTotalVariation E.ideal E.actual ≤ ε) :
    γ / 2 - ε ≤
      ((E.actual.map (E.assembledAttempt hN)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
  classical
  rw [E.assembledAttempt_hit_prob_eq hN]
  let goodSeen : Finset E.Public :=
    E.good.filter (fun t => ∃ x ∈ {x | observe E.trace x = t}, x ∈ E.ideal.support)
  have hsub : goodSeen ⊆ E.good := Finset.filter_subset _ _
  let dataSeen : goodSeen → TranscriptData E.Label N := fun t => E.data ⟨t.val, hsub t.property⟩
  have hseen : ∀ t : goodSeen, ∃ x ∈ {x | observe E.trace x = t.val}, x ∈ E.ideal.support :=
    fun t => (Finset.mem_filter.mp t.property).2
  have hmass_eq :
      E.ideal.toOuterMeasure {x | observe E.trace x ∈ goodSeen} =
        E.ideal.toOuterMeasure {x | observe E.trace x ∈ E.good} := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ E.ideal.support
    · have hiff : observe E.trace x ∈ goodSeen ↔ observe E.trace x ∈ E.good := by
        constructor
        · exact fun h => hsub h
        · exact fun h => Finset.mem_filter.mpr ⟨h, ⟨x, rfl, hx⟩⟩
      simp [Set.indicator_apply, hiff]
    · have hzero : E.ideal x = 0 := by
        simpa [PMF.mem_support_iff] using hx
      simp [Set.indicator_apply, hzero]
  have hboundSeen := epoch_verified_split_probability_half hN ho hnot E.ideal E.actual
    E.trace goodSeen dataSeen hseen
    (fun t x hx => hcheck ⟨t.val, hsub t.property⟩ x hx)
    (fun t x y hx h1 h2 h3 => huniform ⟨t.val, hsub t.property⟩ x y hx h1 h2 h3)
    γ ε hγ₀ (by rwa [hmass_eq]) hTV
  refine hboundSeen.trans ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact E.actual.tsum_coe_indicator_ne_top _
  · apply MeasureTheory.OuterMeasure.mono
    intro x hx
    change (epochTrial E.trace goodSeen dataSeen x).1 ≠ none at hx
    change (epochTrial E.trace E.good E.data x).1 ≠ none
    unfold epochTrial at hx ⊢
    split_ifs at hx with h1
    · have h2 : observe E.trace x ∈ E.good := hsub h1
      rw [dif_pos h2]
      exact hx
    · exact (hx rfl).elim

end HardEpochData

/-! ## Section 4: End-to-End Epoch Assembly and Serialized Factoring Theorems -/

/-- Sample space lifted to all `n : ℕ`: `none` below `3`, and a tagged sample of
`E n h` for `3 ≤ n`. The proof tag lives in `PLift`, so no type-level `if` (and hence
no cast) is needed to define the lifted law and attempt. -/
def epochSpace (E : ∀ n, 3 ≤ n → HardEpochData n) (n : ℕ) : Type :=
  Option (Σ h : PLift (3 ≤ n), (E n h.down).Sample)

noncomputable instance epochSpaceFintype (E : ∀ n, 3 ≤ n → HardEpochData n) (n : ℕ) :
    Fintype (epochSpace E n) := by
  haveI : Fintype (PLift (3 ≤ n)) := Fintype.ofFinite _
  have hf : ∀ h : PLift (3 ≤ n), Fintype (E n h.down).Sample := fun h => by
    haveI : NeZero n := ⟨by have := h.down; omega⟩
    infer_instance
  haveI : Fintype (Σ h : PLift (3 ≤ n), (E n h.down).Sample) := @Sigma.instFintype _ _ hf _
  unfold epochSpace
  infer_instance

/-- Tag a sample of `E n hN` as a point of `epochSpace E n`. -/
def epochEmbed (E : ∀ n, 3 ≤ n → HardEpochData n) {n : ℕ} (hN : 3 ≤ n)
    (x : (E n hN).Sample) : epochSpace E n :=
  some ⟨⟨hN⟩, x⟩

/-- Actual epoch law lifted to all `n : ℕ`. -/
noncomputable def epochLaw (E : ∀ n, 3 ≤ n → HardEpochData n) (n : ℕ) :
    PMF (epochSpace E n) :=
  if h : 3 ≤ n then (E n h).actual.map (epochEmbed E h) else PMF.pure none

/-- Assembled epoch attempt lifted to all `n : ℕ`. -/
noncomputable def epochAttempt (E : ∀ n, 3 ≤ n → HardEpochData n) (n : ℕ) :
    epochSpace E n → Option (Factors n) × ℕ
  | none => (none, 0)
  | some ⟨h, x⟩ => (E n h.down).assembledAttempt h.down x

theorem epochLaw_of_le (E : ∀ n, 3 ≤ n → HardEpochData n) {n : ℕ} (hN : 3 ≤ n) :
    epochLaw E n = (E n hN).actual.map (epochEmbed E hN) :=
  dif_pos hN

theorem epochAttempt_embed (E : ∀ n, 3 ≤ n → HardEpochData n) {n : ℕ} (hN : 3 ≤ n) :
    epochAttempt E n ∘ epochEmbed E hN = (E n hN).assembledAttempt hN :=
  rfl

/-- The asymptotic hard-input epoch premises at target exponent `C`:
for every `δ > 0`, eventually on every hard input `n`, `E n hN` satisfies the
congruence check and hidden-sign symmetry, has expected public work
`≤ exp ((C + δ / 2) * scale n)`, and has ideal-to-actual verified split probability
`γ / 2 - ε ≥ exp (-(δ / 4) * scale n)`. -/
def HardEpochAsymptoticBound (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ (hN : 3 ≤ n), Odd n → ¬n.Prime → ¬IsPrimePow n →
      (E n hN).CongruenceCheck ∧
      (E n hN).HiddenUniform ∧
      ∃ W_pub γ ε : ℝ,
        0 ≤ γ ∧
        mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤ ENNReal.ofReal W_pub ∧
        W_pub ≤ exp ((C + δ / 2) * scale n) ∧
        γ ≤ ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal ∧
        pmfTotalVariation (E n hN).ideal (E n hN).actual ≤ ε ∧
        exp (-(δ / 4) * scale n) ≤ γ / 2 - ε

/-- A positive constant lower bound `c > 0` on `γ / 2 - ε` automatically implies
`HardEpochAsymptoticBound E C`. -/
theorem hardEpochAsymptoticBound_of_const_hit
    (E : ∀ n, 3 ≤ n → HardEpochData n) {C c : ℝ} (hc : 0 < c)
    (hconst : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (hN : 3 ≤ n), Odd n → ¬n.Prime → ¬IsPrimePow n →
        (E n hN).CongruenceCheck ∧
        (E n hN).HiddenUniform ∧
        ∃ W_pub γ ε : ℝ,
          0 ≤ γ ∧
          mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤ ENNReal.ofReal W_pub ∧
          W_pub ≤ exp ((C + δ / 2) * scale n) ∧
          γ ≤ ((E n hN).ideal.toOuterMeasure
            {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal ∧
          pmfTotalVariation (E n hN).ideal (E n hN).actual ≤ ε ∧
          c ≤ γ / 2 - ε) :
    HardEpochAsymptoticBound E C := by
  intro δ hδ
  filter_upwards [hconst δ hδ, eventually_exp_neg_le_const hc (show 0 < δ / 4 by positivity)]
    with n hn hexp hN ho hp hpow
  obtain ⟨hcheck, huniform, W_pub, γ, ε, hγ₀, hpub, hW, hγ, hTV, hhit⟩ := hn hN ho hp hpow
  exact ⟨hcheck, huniform, W_pub, γ, ε, hγ₀, hpub, hW, hγ, hTV, hexp.trans hhit⟩

/-- Core Epoch Assembly Theorem: `HardEpochAsymptoticBound E C` (with `0 ≤ C`)
discharges the exact `(W, S)` work-to-hit ratio premise of both
`serialized_epoch_from_critical_line` and
`serialized_balancedEnvelopeInfimum_from_critical_line`. -/
theorem assembled_epoch_ratio_eventually
    (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : HardEpochAsymptoticBound E C) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epochLaw E n) (fun a => ((epochAttempt E n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((epochLaw E n).map (epochAttempt E n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n) := by
  intro δ hδ
  filter_upwards [hbound δ hδ, eventually_ge_atTop (3 : ℕ),
    scale_grows.eventually_ge_atTop 0,
    eventually_trialBudget_add_two_le_exp (show 0 < δ / 2 by positivity),
    eventually_bitPoly_le_exp (A := 2) (show 0 < δ / 4 by positivity) 0]
    with n hn hN hscale htrial htwo ho hp hpow
  simp only [pow_zero, mul_one] at htwo
  obtain ⟨hcheck, huniform, W_pub, γ, ε, hγ₀, hpub, hWpub, hγ, hTV, hSexp⟩ := hn hN ho hp hpow
  let W : ℝ := max 0 W_pub + ((trialBudget n + 2 : ℕ) : ℝ)
  let S : ℝ := γ / 2 - ε
  have hSpos : 0 < S := (exp_pos _).trans_le hSexp
  have hwork :
      mean (epochLaw E n) (fun a => ((epochAttempt E n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W := by
    rw [epochLaw_of_le E hN, mean_map]
    exact (E n hN).assembledAttempt_mean_work_le hN hpub
  have hhit :
      S ≤ (((epochLaw E n).map (epochAttempt E n)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
    rw [epochLaw_of_le E hN, PMF.map_comp, epochAttempt_embed]
    exact (E n hN).assembledAttempt_hit_prob_ge hN ho hpow hcheck huniform hγ₀ hγ hTV
  have hWle : W ≤ exp ((C + 3 * δ / 4) * scale n) := by
    have hmax : max 0 W_pub ≤ exp ((C + δ / 2) * scale n) :=
      max_le (exp_pos _).le hWpub
    have htr : ((trialBudget n + 2 : ℕ) : ℝ) ≤ exp ((C + δ / 2) * scale n) :=
      htrial.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hscale))
    calc
      W ≤ 2 * exp ((C + δ / 2) * scale n) := by dsimp [W]; linarith only [hmax, htr]
      _ ≤ exp ((δ / 4) * scale n) * exp ((C + δ / 2) * scale n) :=
          mul_le_mul_of_nonneg_right htwo (exp_pos _).le
      _ = exp ((C + 3 * δ / 4) * scale n) := by
          rw [← exp_add]
          congr 1
          ring
  have hratio : W / S ≤ exp ((C + δ) * scale n) := by
    have hWnn : 0 ≤ W := add_nonneg (le_max_left 0 W_pub) (Nat.cast_nonneg _)
    calc
      W / S ≤ exp ((C + 3 * δ / 4) * scale n) / exp (-(δ / 4) * scale n) :=
        div_le_div₀ (exp_pos _).le hWle (exp_pos _) hSexp
      _ = exp ((C + δ) * scale n) := by
        rw [← exp_sub]
        congr 1
        ring
  exact ⟨W, S, hSpos, hwork, hhit, hratio⟩

/-- Fixed-schedule serialized end-to-end theorem from `HardEpochData`:
under the critical-line hypothesis for Dirichlet L-functions, any concrete family
`E : ∀ n, 3 ≤ n → HardEpochData n` satisfying `HardEpochAsymptoticBound E C` (`0 ≤ C`)
yields a certified serialized factoring algorithm whose output bitstrings always decode
to `n.primeFactorsList` and whose expected serialized bit cost is eventually
`≤ ENNReal.ofReal (exp ((C + ε) * scale n))`. -/
theorem serialized_assembled_epoch_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ}, 0 ≤ C →
      HardEpochAsymptoticBound E C →
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound (epochHard (epochLaw E) (epochAttempt E)) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound (epochHard (epochLaw E) (epochAttempt E)) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤ ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ := serialized_epoch_from_critical_line line
  refine ⟨k, sound, fun E C hC hbound => ?_⟩
  exact hmain (epochLaw E) (epochAttempt E) hC (assembled_epoch_ratio_eventually E hC hbound)

/-- Every target ceiling `D` witnessed by a valid `BalancedRationalSchedule` is positive. -/
theorem balancedRationalSchedule_valid_pos {s : BalancedRationalSchedule} {D : ℝ}
    (hvalid : s.Valid D) : 0 < D := by
  have hb : 0.9448547 < s.perturbation.b := hvalid.2.2.1
  have hq : 0 < s.perturbation.q := hvalid.2.2.2.2.2.2.1
  have hwpos : ∀ i < s.k + 1, 0 < s.weight i := hvalid.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htot : s.perturbation.b + (∑ j ∈ Finset.range (s.k + 1), s.weight j) +
      s.perturbation.q < D := hvalid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsum : 0 ≤ ∑ j ∈ Finset.range (s.k + 1), s.weight j :=
    Finset.sum_nonneg fun j hj => (hwpos j (Finset.mem_range.mp hj)).le
  linarith only [hb, hq, hsum, htot]

/-- Universal-schedule serialized end-to-end theorem at `C_* = balancedEnvelopeInfimum`:
under the critical-line hypothesis for Dirichlet L-functions, any family of concrete
hard-input epochs parameterized by `BalancedRationalSchedule` that meets
`HardEpochAsymptoticBound (E s) D` whenever `s.Valid D` yields ONE single universal
serialized factoring algorithm whose outputs always decode to `n.primeFactorsList` and
whose expected serialized bit cost is eventually
`≤ ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n))`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_critical_line
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        HardEpochAsymptoticBound (E s) D) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ := serialized_balancedEnvelopeInfimum_from_critical_line line
  refine ⟨k, sound, fun E hSched => ?_⟩
  exact hmain (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)) fun s D hvalid =>
    assembled_epoch_ratio_eventually (E s) (balancedRationalSchedule_valid_pos hvalid).le
      (hSched s D hvalid)

#print axioms trialBudget_eq_poly
#print axioms trialBudget_le_cubic
#print axioms trialBudget_le_quartic
#print axioms eventually_trialBudget_add_two_le_exp
#print axioms eventually_finset_sum_le_exp
#print axioms eventually_finset_sum_nat_le_exp
#print axioms eventually_mean_finset_sum_le_exp
#print axioms eventually_multistage_screening_cost_le_exp
#print axioms eventually_multistage_screening_cost_le_exp_of_slack
#print axioms balancedSchedule_multistage_screening_cost_le_exp
#print axioms HardEpochData.ofMultiField_congruenceCheck
#print axioms HardEpochData.ofMultiField_hiddenUniform
#print axioms HardEpochData.assembledAttempt_mean_work_le
#print axioms HardEpochData.assembledAttempt_hit_prob_ge
#print axioms assembled_epoch_ratio_eventually
#print axioms serialized_assembled_epoch_from_critical_line
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_critical_line

end Cogentic.RandomizedEpochAssembly
