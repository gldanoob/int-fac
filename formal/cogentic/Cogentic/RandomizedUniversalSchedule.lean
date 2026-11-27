import Cogentic.RandomizedBalancedRationalSchedule
import Cogentic.RandomizedEpochOutput
import Cogentic.RandomizedOneThirdAsymptotic
import Cogentic.RandomizedRestartBudget

namespace Cogentic.RandomizedUniversalSchedule

open Cogentic.Randomized
open Cogentic.RandomizedCappedEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochKernel
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedTotalEpochSplit
open Filter Real
open scoped BigOperators ENNReal

/-! ### Elementary `PMF` expectation helpers -/

private theorem mean_mono {α : Type*} (p : PMF α) {f g : α → ℝ≥0∞}
    (h : ∀ a, f a ≤ g a) : mean p f ≤ mean p g :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) (p a)

private theorem mean_le_of_support {α : Type*} (p : PMF α) {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ c) : mean p f ≤ c := by
  rw [← mean_const p c]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) (p a)
  · have h0 : p a = 0 := by
      by_contra hne
      exact ha ((PMF.mem_support_iff p a).mpr hne)
    simp [h0]

private theorem mean_mul_left {α : Type*} (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    mean p (fun a => c * f a) = c * mean p f := by
  simp only [mean, mul_left_comm _ c, ENNReal.tsum_mul_left]

private theorem mean_mul_right {α : Type*} (p : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    mean p (fun a => f a * c) = mean p f * c := by
  simp only [mean, ← mul_assoc, ENNReal.tsum_mul_right]

private theorem failFlag_le_one {β : Type*} (o : Option β) : failFlag o ≤ 1 := by
  cases o <;> simp [failFlag]

private theorem mean_failFlag_le_one {α β : Type*} (p : PMF α) (f : α → Option β) :
    mean p (fun a => failFlag (f a)) ≤ 1 := by
  rw [← mean_const p 1]
  exact mean_mono p fun a => failFlag_le_one (f a)

/-! ### Truncated split execution and Markov's inequality -/

/-- Execute one hard-input split outcome under a step budget `B` with counter
and dispatch bookkeeping `extra`. If the split finishes within `B` steps, return
its certified factors; otherwise abort at step `B`. -/
def truncateSplit {n : ℕ} (B extra : ℕ) (s : SplitOutcome n) :
    Option (Factors n) × ℕ :=
  if s.work ≤ B then
    (some ⟨(s.left, s.right), s.left_ge, s.right_ge, s.product⟩, s.work + 1 + extra)
  else
    (none, B + 1 + extra)

theorem truncateSplit_work_le {n : ℕ} (B extra : ℕ) (s : SplitOutcome n) :
    (truncateSplit B extra s).2 ≤ B + 1 + extra := by
  unfold truncateSplit
  split_ifs <;> omega

/-- Markov's inequality for a single truncated split call: once the budget is
at least four times a positive mean bound, the abort probability is at most `1/4`. -/
theorem truncateSplit_fail_le {n : ℕ} (p : PMF (SplitOutcome n))
    (B extra : ℕ) {E : ℝ} (hE : 0 < E) (hB : 4 * E ≤ (B : ℝ))
    (hmean : mean p (fun s => (s.work : ℝ≥0∞)) ≤ ENNReal.ofReal E) :
    mean p (fun s => failFlag (truncateSplit B extra s).1) ≤ ENNReal.ofReal (1 / 4) := by
  let q := mean p (fun s => failFlag (truncateSplit B extra s).1)
  have hq1 : q ≤ 1 := mean_failFlag_le_one p (fun s => (truncateSplit B extra s).1)
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq1
  have hpt (s : SplitOutcome n) :
      (B : ℝ≥0∞) * failFlag (truncateSplit B extra s).1 ≤ (s.work : ℝ≥0∞) := by
    unfold truncateSplit
    split_ifs with h
    · simp [failFlag]
    · simp only [failFlag, mul_one]
      exact Nat.cast_le.mpr (by omega)
  have hmarkov : ENNReal.ofReal (4 * E) * q ≤ ENNReal.ofReal E := by
    calc
      ENNReal.ofReal (4 * E) * q
          ≤ (B : ℝ≥0∞) * q := by
            refine mul_le_mul_left ?_ q
            simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hB
      _ = mean p (fun s => (B : ℝ≥0∞) * failFlag (truncateSplit B extra s).1) :=
            (mean_mul_left p (B : ℝ≥0∞) _).symm
      _ ≤ mean p (fun s => (s.work : ℝ≥0∞)) := mean_mono p hpt
      _ ≤ ENNReal.ofReal E := hmean
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmarkov
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hE.le] at hreal
  have hquarter : q.toReal ≤ 1 / 4 := by
    apply (mul_le_mul_iff_of_pos_left hE).mp
    linarith only [hreal]
  have h := ENNReal.ofReal_le_ofReal hquarter
  rwa [ENNReal.ofReal_toReal hqtop] at h

/-! ### Dyadic phase multiplexer with explicit counter bookkeeping -/

private theorem sum_pow_two_range (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), (2 : ℕ) ^ i) + 1 = 2 * 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

private theorem bookkeeping_sum_le (r : ℕ) : (r + 1) * (r + 2) ≤ 6 * 2 ^ r := by
  induction r with
  | zero => decide
  | succ r ih =>
    cases r with
    | zero => decide
    | succ r =>
      have hstep : (r + 3) * (r + 4) ≤ 2 * ((r + 2) * (r + 3)) := by nlinarith
      calc
        (r + 1 + 1 + 1) * (r + 1 + 1 + 2) = (r + 3) * (r + 4) := by ring
        _ ≤ 2 * ((r + 2) * (r + 3)) := hstep
        _ = 2 * ((r + 1 + 1) * (r + 1 + 2)) := by ring
        _ ≤ 2 * (6 * 2 ^ (r + 1)) := Nat.mul_le_mul_left 2 ih
        _ = 6 * 2 ^ (r + 1 + 1) := by rw [pow_succ]; ring

/-- Run schedules `0, ..., k - 1` of phase `r` sequentially with fresh
independent randomness, stopping as soon as any schedule succeeds. Schedule `j`
receives step budget `2^(r - j)` plus `r + 1` bookkeeping steps for the `r`-bit
phase/job/budget counters. -/
noncomputable def runPhaseJobs {n : ℕ} (family : ℕ → PMF (SplitOutcome n))
    (r : ℕ) : ℕ → PMF (Option (Factors n) × ℕ)
  | 0 => PMF.pure (none, 0)
  | k + 1 =>
    (runPhaseJobs family r k).bind fun prev =>
      match prev.1 with
      | some f => PMF.pure (some f, prev.2)
      | none =>
        (family k).map fun s =>
          let res := truncateSplit (2 ^ (r - k)) (r + 1) s
          (res.1, prev.2 + res.2)

/-- One complete phase `r` of the universal multiplexer: run every schedule
`j ≤ r` with step budget `2^(r - j)` and fresh independent randomness. -/
noncomputable def runPhase {n : ℕ} (family : ℕ → PMF (SplitOutcome n)) (r : ℕ) :
    PMF (Option (Factors n) × ℕ) :=
  runPhaseJobs family r (r + 1)

private theorem runPhaseJobs_support_work_le {n : ℕ}
    (family : ℕ → PMF (SplitOutcome n)) (r k : ℕ) :
    ∀ o ∈ (runPhaseJobs family r k).support,
      o.2 ≤ ∑ j ∈ Finset.range k, (2 ^ (r - j) + r + 2) := by
  induction k with
  | zero =>
    intro o ho
    simp only [runPhaseJobs, PMF.mem_support_pure_iff] at ho
    subst ho
    simp
  | succ k ih =>
    intro o ho
    rw [runPhaseJobs, PMF.mem_support_bind_iff] at ho
    obtain ⟨prev, hprev, ho⟩ := ho
    have hprevW := ih prev hprev
    rw [Finset.sum_range_succ]
    cases h1 : prev.1 with
    | some f =>
      simp only [h1, PMF.mem_support_pure_iff] at ho
      subst ho
      exact hprevW.trans (Nat.le_add_right _ _)
    | none =>
      simp only [h1, PMF.mem_support_map_iff] at ho
      obtain ⟨s, _, rfl⟩ := ho
      have htr := truncateSplit_work_le (2 ^ (r - k)) (r + 1) s
      change prev.2 + (truncateSplit (2 ^ (r - k)) (r + 1) s).2 ≤ _
      omega

/-- Every execution of phase `r` (including the branching step on the phase
result) uses at most `8 * 2^r` units of work. -/
theorem runPhase_support_work_le {n : ℕ} (family : ℕ → PMF (SplitOutcome n))
    (r : ℕ) {o : Option (Factors n) × ℕ} (ho : o ∈ (runPhase family r).support) :
    o.2 + 1 ≤ 8 * 2 ^ r := by
  have h0 := runPhaseJobs_support_work_le family r (r + 1) o ho
  have hsum :
      (∑ j ∈ Finset.range (r + 1), (2 ^ (r - j) + r + 2)) =
        (∑ j ∈ Finset.range (r + 1), (2 : ℕ) ^ j) + (r + 1) * (r + 2) := by
    calc
      (∑ j ∈ Finset.range (r + 1), (2 ^ (r - j) + r + 2))
          = (∑ j ∈ Finset.range (r + 1), 2 ^ (r - j)) +
              ∑ _j ∈ Finset.range (r + 1), (r + 2) := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => by omega
      _ = (∑ j ∈ Finset.range (r + 1), (2 : ℕ) ^ j) + (r + 1) * (r + 2) := by
            congr 1
            · simpa only [Nat.add_sub_cancel] using
                Finset.sum_range_reflect (fun i => (2 : ℕ) ^ i) (r + 1)
            · simp
  have hpow := sum_pow_two_range r
  have hbook := bookkeeping_sum_le r
  omega

theorem runPhase_mean_work_le {n : ℕ} (family : ℕ → PMF (SplitOutcome n)) (r : ℕ) :
    mean (runPhase family r) (fun o => ((o.2 + 1 : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (8 * (2 : ℝ) ^ r) := by
  refine (mean_le_of_support (runPhase family r) (c := ((8 * 2 ^ r : ℕ) : ℝ≥0∞)) ?_).trans_eq ?_
  · intro o ho
    exact Nat.cast_le.mpr (runPhase_support_work_le family r ho)
  · rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl

private theorem runPhaseJobs_fail {n : ℕ} (family : ℕ → PMF (SplitOutcome n))
    (r k : ℕ) :
    mean (runPhaseJobs family r k) (fun o => failFlag o.1) =
      ∏ j ∈ Finset.range k,
        mean (family j) (fun s => failFlag (truncateSplit (2 ^ (r - j)) (r + 1) s).1) := by
  induction k with
  | zero => simp [runPhaseJobs, mean_pure, failFlag]
  | succ k ih =>
    let qk := mean (family k) (fun s => failFlag (truncateSplit (2 ^ (r - k)) (r + 1) s).1)
    rw [Finset.prod_range_succ, ← ih, runPhaseJobs, mean_bind, ← mean_mul_right]
    congr 1
    funext prev
    cases h : prev.1 with
    | some f => simp [failFlag, mean_pure]
    | none => simp [failFlag, mean_map]

/-- Phase `r` misses only if every schedule `j ≤ r` misses within its budget. -/
theorem runPhase_fail_le_of_le {n : ℕ} (family : ℕ → PMF (SplitOutcome n))
    {r j : ℕ} (hj : j ≤ r) :
    mean (runPhase family r) (fun o => failFlag o.1) ≤
      mean (family j) (fun s => failFlag (truncateSplit (2 ^ (r - j)) (r + 1) s).1) := by
  rw [runPhase, runPhaseJobs_fail]
  have hmem : j ∈ Finset.range (r + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  rw [← Finset.mul_prod_erase _ _ hmem]
  have hrest :
      (∏ i ∈ (Finset.range (r + 1)).erase j,
        mean (family i) (fun s => failFlag (truncateSplit (2 ^ (r - i)) (r + 1) s).1)) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => zero_le) (fun i _ => mean_failFlag_le_one _ _)
  simpa only [mul_one] using mul_le_mul_right hrest _

/-! ### Capped universal phase sequence with deterministic trial-division fallback -/

/-- Number of dyadic phases before invoking deterministic trial division.
Chosen so `RandomizedTrialFallback.cap n < 2 ^ universalPhaseCap n`. -/
def universalPhaseCap (n : ℕ) : ℕ :=
  (RandomizedTrialFallback.cap n).log2 + 1

/-- Run `rem` consecutive phases starting at phase index `start`, falling back
to deterministic trial division if all phases miss. -/
noncomputable def runPhases {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (family : ℕ → PMF (SplitOutcome n)) : (start rem : ℕ) → PMF (SplitOutcome n)
  | _, 0 => PMF.pure (RandomizedTrialFallback.split n hn hp)
  | start, rem + 1 =>
    (runPhase family start).bind fun o =>
      match o.1 with
      | some f =>
        PMF.pure ⟨f.val.1, f.val.2, o.2 + 1, f.property.1, f.property.2.1, f.property.2.2⟩
      | none =>
        (runPhases hn hp family (start + 1) rem).map fun tail =>
          { tail with work := o.2 + 1 + tail.work }

/-- One single capped universal split law multiplexing a countable family of
split laws for a composite input `n`. -/
noncomputable def universalSplitLaw {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (family : ℕ → PMF (SplitOutcome n)) : PMF (SplitOutcome n) :=
  runPhases hn hp family 0 (universalPhaseCap n)

/-- One single universal `HardKernel` multiplexing a countable family of
hard-input splitters. -/
noncomputable def universalHardKernel (family : ℕ → HardKernel) : HardKernel :=
  fun n hn ho hp hpow =>
    universalSplitLaw hn hp (fun j => family j n hn ho hp hpow)

/-- One single universal `HardKernel` multiplexing a countable family of
epoch-attempt pairs via `epochHard`. -/
noncomputable def universalEpochHard {α : ℕ → ℕ → Type}
    (epoch : ∀ j n, PMF (α j n))
    (attempt : ∀ j n, α j n → Option (Factors n) × ℕ) : HardKernel :=
  universalHardKernel (fun j => epochHard (epoch j) (attempt j))

private theorem runPhases_mean_succ {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (family : ℕ → PMF (SplitOutcome n)) (start rem : ℕ) :
    mean (runPhases hn hp family start (rem + 1)) (fun s => (s.work : ℝ≥0∞)) =
      mean (runPhase family start) (fun o => ((o.2 + 1 : ℕ) : ℝ≥0∞)) +
        mean (runPhase family start) (fun o => failFlag o.1) *
          mean (runPhases hn hp family (start + 1) rem) (fun s => (s.work : ℝ≥0∞)) := by
  let z := mean (runPhases hn hp family (start + 1) rem) (fun s => (s.work : ℝ≥0∞))
  change _ = _ + _ * z
  rw [← mean_mul_right _ _ z, ← mean_add, runPhases, mean_bind]
  congr 1
  funext o
  cases h : o.1 with
  | some f => simp [failFlag, mean_pure]
  | none =>
    simp only [failFlag, one_mul, mean_map, Nat.cast_add, Nat.cast_one]
    exact (mean_add _ _ _).trans (congrArg (· + z) (mean_const _ _))

private theorem runPhases_mean_eq {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (family : ℕ → PMF (SplitOutcome n)) (start rem : ℕ) :
    let w := fun r => mean (runPhase family r) (fun o => ((o.2 + 1 : ℕ) : ℝ≥0∞))
    let q := fun r => mean (runPhase family r) (fun o => failFlag o.1)
    mean (runPhases hn hp family start rem) (fun s => (s.work : ℝ≥0∞)) =
      (∑ k ∈ Finset.range rem, (∏ i ∈ Finset.range k, q (start + i)) * w (start + k)) +
        (∏ i ∈ Finset.range rem, q (start + i)) *
          ((RandomizedTrialFallback.split n hn hp).work : ℝ≥0∞) := by
  dsimp only
  induction rem generalizing start with
  | zero => simp [runPhases, mean_pure]
  | succ rem ih =>
    let w := fun r => mean (runPhase family r) (fun o => ((o.2 + 1 : ℕ) : ℝ≥0∞))
    let q := fun r => mean (runPhase family r) (fun o => failFlag o.1)
    rw [runPhases_mean_succ, ih (start + 1)]
    have hprod_shift (k : ℕ) :
        q start * (∏ i ∈ Finset.range k, q (start + 1 + i)) =
          ∏ i ∈ Finset.range (k + 1), q (start + i) := by
      rw [Finset.prod_range_succ', mul_comm, Nat.add_zero]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 1
      omega
    have hsum_shift :
        w start +
            q start * ∑ k ∈ Finset.range rem,
              (∏ i ∈ Finset.range k, q (start + 1 + i)) * w (start + 1 + k) =
          ∑ k ∈ Finset.range (rem + 1),
            (∏ i ∈ Finset.range k, q (start + i)) * w (start + k) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, hprod_shift k]
        congr 2
        omega
      · simp
    change w start + q start * ((∑ k ∈ Finset.range rem,
        (∏ i ∈ Finset.range k, q (start + 1 + i)) * w (start + 1 + k)) +
        (∏ i ∈ Finset.range rem, q (start + 1 + i)) *
          ((RandomizedTrialFallback.split n hn hp).work : ℝ≥0∞)) = _
    rw [mul_add, ← add_assoc, hsum_shift, ← mul_assoc, hprod_shift rem]

/-- The capped universal multiplexer always has finite expected work, even if
none of the underlying splitters has finite expectation on a given input. -/
theorem universalSplitLaw_mean_ne_top {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (family : ℕ → PMF (SplitOutcome n)) :
    mean (universalSplitLaw hn hp family) (fun s => (s.work : ℝ≥0∞)) ≠ ⊤ := by
  let R := universalPhaseCap n
  let q := fun r => mean (runPhase family r) (fun o => failFlag o.1)
  have hq (r : ℕ) : q r ≤ 1 := mean_failFlag_le_one _ _
  have hS (r : ℕ) : (∏ i ∈ Finset.range r, q i) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => zero_le) (fun i _ => hq i)
  have hle :
      mean (universalSplitLaw hn hp family) (fun s => (s.work : ℝ≥0∞)) ≤
        (∑ r ∈ Finset.range R, ENNReal.ofReal (8 * (2 : ℝ) ^ r)) +
          ((RandomizedTrialFallback.split n hn hp).work : ℝ≥0∞) := by
    rw [universalSplitLaw, runPhases_mean_eq]
    simp only [Nat.zero_add]
    refine add_le_add (Finset.sum_le_sum fun r _ => ?_) ?_
    · simpa only [one_mul] using
        mul_le_mul' (hS r) (runPhase_mean_work_le family r)
    · simpa only [one_mul] using mul_le_mul_left (hS R) _
  refine ne_top_of_le_ne_top ?_ hle
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top, ENNReal.natCast_ne_top _⟩

theorem universalHardKernel_mean_ne_top (family : ℕ → HardKernel)
    (n : ℕ) (hn : 2 ≤ n) (ho : Odd n) (hp : ¬n.Prime) (hpow : ¬IsPrimePow n) :
    mean (universalHardKernel family n hn ho hp hpow) (fun s => (s.work : ℝ≥0∞)) ≠ ⊤ :=
  universalSplitLaw_mean_ne_top hn hp _

/-- Pure finite-horizon dyadic restart envelope with a fallback cost `≤ 2^R`.
Regardless of whether the threshold `m` lies before or after the fallback cap `R`,
the total expected cost is bounded by `25 * 2^m`. -/
private theorem capped_dyadic_envelope (R m : ℕ) (S : ℕ → ℝ)
    (hS1 : ∀ r, S r ≤ 1)
    (hstep : ∀ k, S (m + (k + 1)) ≤ (1 / 4 : ℝ) * S (m + k)) :
    (∑ r ∈ Finset.range R, S r * (8 * (2 : ℝ) ^ r)) + S R * (2 : ℝ) ^ R ≤
      25 * (2 : ℝ) ^ m := by
  by_cases hRm : R ≤ m
  · have hpref :
        (∑ r ∈ Finset.range R, S r * (8 * (2 : ℝ) ^ r)) ≤
          ∑ r ∈ Finset.range R, 8 * (2 : ℝ) ^ r :=
      Finset.sum_le_sum fun r _ => by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hS1 r) (by positivity : 0 ≤ 8 * (2 : ℝ) ^ r)
    have hpow : (2 : ℝ) ^ R ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) hRm
    have hfall : S R * (2 : ℝ) ^ R ≤ (2 : ℝ) ^ R := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hS1 R) (by positivity : 0 ≤ (2 : ℝ) ^ R)
    rw [dyadic_restart_prefix_sum] at hpref
    linarith only [hpref, hfall, hpow, show (0 : ℝ) ≤ (2 : ℝ) ^ m by positivity]
  · have hmR : m ≤ R := Nat.le_of_not_ge hRm
    let d := R - m
    have hR : R = m + d := (Nat.add_sub_of_le hmR).symm
    let p : ℕ → ℝ := fun k => S (m + k)
    have hp : ∀ k, p k ≤ (1 / 4 : ℝ) ^ k :=
      quarter_survival_le p (by simpa [p] using hS1 m) hstep
    have hpref :
        (∑ r ∈ Finset.range m, S r * (8 * (2 : ℝ) ^ r)) ≤ 8 * (2 : ℝ) ^ m := by
      calc
        _ ≤ ∑ r ∈ Finset.range m, 8 * (2 : ℝ) ^ r :=
          Finset.sum_le_sum fun r _ => by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right (hS1 r) (by positivity : 0 ≤ 8 * (2 : ℝ) ^ r)
        _ = 8 * ((2 : ℝ) ^ m - 1) := dyadic_restart_prefix_sum 8 m
        _ ≤ 8 * (2 : ℝ) ^ m := by linarith
    have htail :
        (∑ k ∈ Finset.range d, S (m + k) * (8 * (2 : ℝ) ^ (m + k))) ≤
          16 * (2 : ℝ) ^ m := by
      have heq :
          (∑ k ∈ Finset.range d, S (m + k) * (8 * (2 : ℝ) ^ (m + k))) =
            ∑ k ∈ Finset.range d, (8 * (2 : ℝ) ^ m) * (2 : ℝ) ^ k * p k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp only [p]
        rw [pow_add]
        ring
      rw [heq]
      have hts := dyadic_restart_tail_sum_le (8 * (2 : ℝ) ^ m) (by positivity) p hp d
      have hhalf : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ d := by positivity
      have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
      nlinarith only [hts, hhalf, hpow]
    have hfall : S (m + d) * (2 : ℝ) ^ (m + d) ≤ (2 : ℝ) ^ m := by
      have hpd : p d ≤ (1 / 4 : ℝ) ^ d := hp d
      calc
        S (m + d) * (2 : ℝ) ^ (m + d)
            = (2 : ℝ) ^ m * ((2 : ℝ) ^ d * p d) := by dsimp [p]; rw [pow_add]; ring
        _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ d * (1 / 4 : ℝ) ^ d) := by
            gcongr
        _ = (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ d := by
            rw [← mul_pow]
            norm_num
        _ ≤ (2 : ℝ) ^ m * 1 := by
            gcongr
            exact pow_le_one₀ (by norm_num) (by norm_num)
        _ = (2 : ℝ) ^ m := mul_one _
    rw [hR, Finset.sum_range_add]
    linarith only [hpref, htail, hfall]

private theorem exists_dyadic_bracket {x : ℝ} (hx : 1 ≤ x) :
    ∃ k : ℕ, x ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k ≤ 2 * x := by
  let u : ℕ := ⌊x⌋₊
  have hu1 : 1 ≤ u := Nat.le_floor (by simpa using hx)
  have hu_le : (u : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hu_lt : x < (u : ℝ) + 1 := Nat.lt_floor_add_one x
  let k : ℕ := u.log2 + 1
  have hlo_nat : u + 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.lt_log2_self (n := u))
  have hhi_nat : 2 ^ k ≤ 2 * u := by
    dsimp [k]
    rw [pow_succ']
    exact Nat.mul_le_mul_left 2 (Nat.log2_self_le (by omega))
  refine ⟨k, ?_, ?_⟩
  · have hlo : (u : ℝ) + 1 ≤ (2 : ℝ) ^ k := by exact_mod_cast hlo_nat
    linarith only [hu_lt, hlo]
  · have hhi : (2 : ℝ) ^ k ≤ 2 * (u : ℝ) := by exact_mod_cast hhi_nat
    linarith only [hu_le, hhi]

/-- Core multiplexing guarantee: for every fixed schedule index `j` and every
real upper bound `E` on `family j`'s expected work on `n`, the single universal
split law has expected work at most `200 * 2^j * max 1 E`. -/
theorem universalSplitLaw_mean_le {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (family : ℕ → PMF (SplitOutcome n)) (j : ℕ) {E : ℝ}
    (hmean : mean (family j) (fun s => (s.work : ℝ≥0∞)) ≤ ENNReal.ofReal E) :
    mean (universalSplitLaw hn hp family) (fun s => (s.work : ℝ≥0∞)) ≤
      ENNReal.ofReal (200 * (2 : ℝ) ^ j * max 1 E) := by
  let E' : ℝ := max 1 E
  have hE'1 : 1 ≤ E' := le_max_left 1 E
  have hE'pos : 0 < E' := zero_lt_one.trans_le hE'1
  have hmean' : mean (family j) (fun s => (s.work : ℝ≥0∞)) ≤ ENNReal.ofReal E' :=
    hmean.trans (ENNReal.ofReal_le_ofReal (le_max_right 1 E))
  obtain ⟨k, hk_lo, hk_hi⟩ := exists_dyadic_bracket (show 1 ≤ 4 * E' by linarith)
  let m : ℕ := j + k
  let R : ℕ := universalPhaseCap n
  let q := fun r => mean (runPhase family r) (fun o => failFlag o.1)
  let S := fun r => ∏ i ∈ Finset.range r, q i
  have hq1 (r : ℕ) : q r ≤ 1 := mean_failFlag_le_one _ _
  have hS1 (r : ℕ) : S r ≤ 1 :=
    Finset.prod_le_one (fun _ _ => zero_le) (fun i _ => hq1 i)
  have hStop (r : ℕ) : S r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hS1 r)
  have hq_quarter (r : ℕ) (hr : m ≤ r) : q r ≤ ENNReal.ofReal (1 / 4) := by
    have hjr : j ≤ r := (Nat.le_add_right j k).trans hr
    have hkr : k ≤ r - j := by omega
    have hB : 4 * E' ≤ ((2 ^ (r - j) : ℕ) : ℝ) := by
      push_cast
      exact hk_lo.trans (pow_le_pow_right₀ (by norm_num) hkr)
    exact (runPhase_fail_le_of_le family hjr).trans
      (truncateSplit_fail_le (family j) (2 ^ (r - j)) (r + 1) hE'pos hB hmean')
  have hS_toReal_le (r : ℕ) : (S r).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (hS1 r)
  have hS_step (t : ℕ) : (S (m + (t + 1))).toReal ≤ (1 / 4 : ℝ) * (S (m + t)).toReal := by
    have hmul : S (m + (t + 1)) ≤ ENNReal.ofReal (1 / 4) * S (m + t) := by
      have heq : S (m + (t + 1)) = S (m + t) * q (m + t) := by
        dsimp [S]
        rw [← Nat.add_assoc, Finset.prod_range_succ]
      rw [heq, mul_comm]
      exact mul_le_mul_left (hq_quarter (m + t) (Nat.le_add_right m t)) (S (m + t))
    have htop : ENNReal.ofReal (1 / 4) * S (m + t) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hStop (m + t))
    have h := ENNReal.toReal_mono htop hmul
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)] using h
  have hfall_le : ((RandomizedTrialFallback.split n hn hp).work : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 : ℝ) ^ R) := by
    have hnat : (RandomizedTrialFallback.split n hn hp).work ≤ 2 ^ R :=
      (RandomizedTrialFallback.split_work_le n hn hp).trans
        (Nat.lt_log2_self (n := RandomizedTrialFallback.cap n)).le
    simpa [ENNReal.ofReal_natCast] using (Nat.cast_le (α := ℝ≥0∞)).mpr hnat
  have hsum_bound :
      mean (universalSplitLaw hn hp family) (fun s => (s.work : ℝ≥0∞)) ≤
        ENNReal.ofReal
          ((∑ r ∈ Finset.range R, (S r).toReal * (8 * (2 : ℝ) ^ r)) +
            (S R).toReal * (2 : ℝ) ^ R) := by
    rw [universalSplitLaw, runPhases_mean_eq]
    simp only [Nat.zero_add]
    rw [ENNReal.ofReal_add
      (Finset.sum_nonneg fun r _ => mul_nonneg ENNReal.toReal_nonneg (by positivity))
      (mul_nonneg ENNReal.toReal_nonneg (by positivity)),
      ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg ENNReal.toReal_nonneg (by positivity))]
    refine add_le_add (Finset.sum_le_sum fun r _ => ?_) ?_
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hStop r)]
      exact mul_le_mul_right (runPhase_mean_work_le family r) (S r)
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hStop R)]
      exact mul_le_mul_right hfall_le (S R)
  refine hsum_bound.trans (ENNReal.ofReal_le_ofReal ?_)
  have henv := capped_dyadic_envelope R m (fun r => (S r).toReal)
    hS_toReal_le hS_step
  have hm_bound : (2 : ℝ) ^ m ≤ 8 * (2 : ℝ) ^ j * E' := by
    dsimp [m]
    rw [pow_add]
    have hjpos : (0 : ℝ) ≤ (2 : ℝ) ^ j := by positivity
    nlinarith only [hk_hi, hjpos]
  linarith only [henv, hm_bound]

/-- Per-input domination for `universalHardKernel` by every schedule `j` in the
family. -/
theorem universalHardKernel_mean_le (family : ℕ → HardKernel)
    (n : ℕ) (hn : 2 ≤ n) (ho : Odd n) (hp : ¬n.Prime) (hpow : ¬IsPrimePow n)
    (j : ℕ) {E : ℝ}
    (hmean : mean (family j n hn ho hp hpow) (fun s => (s.work : ℝ≥0∞)) ≤ ENNReal.ofReal E) :
    mean (universalHardKernel family n hn ho hp hpow) (fun s => (s.work : ℝ≥0∞)) ≤
      ENNReal.ofReal (200 * (2 : ℝ) ^ j * max 1 E) :=
  universalSplitLaw_mean_le hn hp (fun i => family i n hn ho hp hpow) j hmean

/-! ### Asymptotic limsup-envelope transfer to one single factoring algorithm -/

/-- One single universal hard-input splitter achieves the infimum exponent `C_*`
of any countable family of hard-input splitters whose exponents approach `C_*`. -/
theorem factor_expected_universal_hard (k : ℕ)
    (prep : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n ∧
      (RandomizedPreprocessing.run k n).2 ≤ (10000 * (k + 1)) ^ 32 * (n.log2 + 2) ^ 32)
    (family : ℕ → HardKernel) {C : ℝ} (hC : 0 ≤ C) (cost : ℕ → ℝ)
    (happrox : ∀ δ > (0 : ℝ), ∃ j : ℕ, cost j ≤ C + δ)
    (hfamily : ∀ j : ℕ, ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 2 ≤ n) (ho : Odd n) (hp : ¬n.Prime) (hpow : ¬IsPrimePow n),
        mean (family j n hn ho hp hpow) (fun s => (s.work : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((cost j + δ) * scale n))) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (factor k (fun m hm => (prep m hm).1) (universalHardKernel family) n hn)
        (fun out => (out.2 : ℝ≥0∞)) ≤ ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  classical
  let B (n : ℕ) : ℝ :=
    if h : 2 ≤ n ∧ Odd n ∧ ¬n.Prime ∧ ¬IsPrimePow n then
      (mean (universalHardKernel family n h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun s => (s.work : ℝ≥0∞))).toReal
    else 0
  refine factor_expected_from_hard k prep (universalHardKernel family) B ?_ ?_ hC ?_
  · intro n
    dsimp only [B]
    split <;> positivity
  · intro n hn ho hp hpow
    have hd : 2 ≤ n ∧ Odd n ∧ ¬n.Prime ∧ ¬IsPrimePow n := ⟨hn, ho, hp, hpow⟩
    simp [B, hd, ENNReal.ofReal_toReal (universalHardKernel_mean_ne_top family n hn ho hp hpow)]
  · let cost' : ℕ × ℕ → ℝ := fun p => cost p.1 + 1 / ((p.2 : ℝ) + 1)
    let charge : ℕ × ℕ → ℕ → ℝ := fun p n => exp (cost' p * scale n)
    refine eventually_work_le_exp_of_approximants hC B charge cost'
      (fun p => 200 * (2 : ℝ) ^ p.1) (fun _ => 0) ?_ ?_ ?_
    · intro δ hδ
      obtain ⟨j, hj⟩ := happrox (δ / 2) (by positivity)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < δ / 2 by positivity)
      exact ⟨(j, m), by dsimp [cost']; linarith only [hj, hm]⟩
    · intro p
      exact Filter.Eventually.of_forall fun _ => le_rfl
    · intro p
      have hpos : (0 : ℝ) < 1 / ((p.2 : ℝ) + 1) := by positivity
      filter_upwards [hfamily p.1 (1 / ((p.2 : ℝ) + 1)) hpos] with n hn
      simp only [pow_zero, mul_one]
      dsimp only [B]
      split
      · rename_i hd
        have hdom := universalHardKernel_mean_le family n hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 p.1
          (hn hd.1 hd.2.1 hd.2.2.1 hd.2.2.2)
        have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdom
        have hnn : 0 ≤ 200 * (2 : ℝ) ^ p.1 * max 1 (charge p n) := by
          exact mul_nonneg (by positivity) (zero_le_one.trans (le_max_left 1 _))
        simpa only [charge, cost', ENNReal.toReal_ofReal hnn] using hreal
      · exact mul_nonneg (by positivity) (zero_le_one.trans (le_max_left 1 _))

/-- One single universal hard-input splitter built from a countable family of
epoch-attempt pairs achieves the infimum exponent `C_*`. -/
theorem factor_expected_universal_epoch {α : ℕ → ℕ → Type}
    (k : ℕ)
    (prep : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n ∧
      (RandomizedPreprocessing.run k n).2 ≤ (10000 * (k + 1)) ^ 32 * (n.log2 + 2) ^ 32)
    (epoch : ∀ j n, PMF (α j n))
    (attempt : ∀ j n, α j n → Option (Factors n) × ℕ)
    {C : ℝ} (hC : 0 ≤ C) (cost : ℕ → ℝ)
    (happrox : ∀ δ > (0 : ℝ), ∃ j : ℕ, cost j ≤ C + δ)
    (hEpoch : ∀ j : ℕ, ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      ∃ W S : ℝ, 0 < S ∧
        mean (epoch j n) (fun a => ((attempt j n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
        S ≤ (((epoch j n).map (attempt j n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        W / S ≤ exp ((cost j + δ) * scale n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (factor k (fun m hm => (prep m hm).1) (universalEpochHard epoch attempt) n hn)
        (fun out => (out.2 : ℝ≥0∞)) ≤ ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  refine factor_expected_universal_hard k prep
    (fun j => epochHard (epoch j) (attempt j)) hC cost happrox ?_
  intro j δ hδ
  filter_upwards [hEpoch j δ hδ] with n h hn ho hp hpow
  obtain ⟨W, S, hS, hwork, hhit, hratio⟩ := h ho hp hpow
  exact (splitLaw_mean_le hn hp (epoch j n) (attempt j n)).trans
    ((epoch_ratio_le_of_real_bounds (epoch j n) (attempt j n) hS hwork hhit).trans
      (ENNReal.ofReal_le_ofReal hratio))

/-- Under the critical-line hypothesis for Dirichlet L-functions, a single
multiplexed serialized factoring algorithm achieves the infimum exponent `C_*`
of any countable family of epoch-attempt pairs. -/
theorem serialized_universal_epoch_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ {α : ℕ → ℕ → Type} (epoch : ∀ j n, PMF (α j n))
      (attempt : ∀ j n, α j n → Option (Factors n) × ℕ)
      {C : ℝ} (_ : 0 ≤ C) (cost : ℕ → ℝ),
      (∀ δ > (0 : ℝ), ∃ j : ℕ, cost j ≤ C + δ) →
      (∀ j : ℕ, ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epoch j n) (fun a => ((attempt j n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((epoch j n).map (attempt j n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((cost j + δ) * scale n)) →
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound (universalEpochHard epoch attempt) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound (universalEpochHard epoch attempt) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤ ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  obtain ⟨k, prep⟩ := RandomizedPreprocessing.of_critical_line line
  let sound := fun m hm => (prep m hm).1
  refine ⟨k, sound, ?_⟩
  intro α epoch attempt C hC cost happrox hEpoch
  exact ⟨fun _ hn _ => outputBits_support_correct k sound (universalEpochHard epoch attempt) hn,
    serializedFactor_expected_eventually k sound (universalEpochHard epoch attempt) hC
      (factor_expected_universal_epoch k prep epoch attempt hC cost happrox hEpoch)⟩

/-! ### Instantiation at `C_* = balancedEnvelopeInfimum` -/

/-- A concrete finite rational parameter tuple and uniform mesh count for the
balanced schedule from `rational_balanced_finite_budget`. -/
structure BalancedRationalSchedule where
  u : ℚ
  b : ℚ
  δ : ℚ
  q : ℚ
  k : ℕ

/-- The real perturbation parameters underlying a rational balanced schedule. -/
def BalancedRationalSchedule.perturbation (s : BalancedRationalSchedule) :
    BalancedPerturbation :=
  ⟨s.u, s.b, s.δ, s.q⟩

/-- Uniform grid knots of a rational balanced schedule. -/
def BalancedRationalSchedule.knot (s : BalancedRationalSchedule) (i : ℕ) : ℝ :=
  balancedUniformKnot s.k i

/-- Equalized rational private weights of a rational balanced schedule. -/
def BalancedRationalSchedule.weight (s : BalancedRationalSchedule) (i : ℕ) : ℝ :=
  balancedUniformWeight s.k (s.u + s.q) (2 / (9 * s.u ^ 2)) i

/-- All scalar, grid, moment, gate, and ratio guarantees established by
`rational_balanced_finite_budget` at target ceiling `D`. -/
def BalancedRationalSchedule.Valid (s : BalancedRationalSchedule) (D : ℝ) : Prop :=
  let p := s.perturbation
  let z := s.knot
  let w := s.weight
  0.58514027 < p.u ∧ p.u < 0.58514029 ∧
  0.9448547 < p.b ∧ p.b < 0.944855 ∧
  1.4199108 < p.δ ∧ p.δ < 1.4199110 ∧
  0 < p.q ∧ p.q < 1 / 10 ^ 6 ∧
  p.lowRaw < D ∧
  z 0 = 0 ∧ z (s.k + 1) = 1 ∧ (∀ i < s.k + 1, z i < z (i + 1)) ∧
  (∀ i < s.k + 1, 0 < w i) ∧
  (∑ i ∈ Finset.range (s.k + 1), z (i + 1) ^ 2 * w i) = p.M ∧
  (∀ i < s.k + 1, p.b + p.h * z (i + 1) + (∑ j ∈ Finset.Ico i (s.k + 1), w j) + p.q < D) ∧
  p.b + (∑ j ∈ Finset.range (s.k + 1), w j) + p.q < D ∧
  ((∑ j ∈ Finset.range (s.k + 1), w j) / p.M) < 1.602

theorem exists_valid_balancedRationalSchedule {ε : ℝ} (hε : 0 < ε) :
    ∃ s : BalancedRationalSchedule, s.Valid (balancedEnvelopeInfimum + ε) := by
  obtain ⟨u, b, δ, q, K, huₗ, huᵤ, hbₗ, hbᵤ, hdₗ, hdᵤ, hq, hq', hraw, hmesh⟩ :=
    rational_balanced_finite_budget hε
  obtain ⟨hz0, hz1, hzstep, hwpos, hwM, hgate, htot, hrat⟩ := hmesh K le_rfl
  exact ⟨⟨u, b, δ, q, K⟩, huₗ, huᵤ, hbₗ, hbᵤ, hdₗ, hdᵤ, hq, hq', hraw,
    hz0, hz1, hzstep, hwpos, hwM, hgate, htot, hrat⟩

theorem balancedEnvelopeInfimum_nonneg : 0 ≤ balancedEnvelopeInfimum := by
  have hlo := balancedEnvelopeInfimum_spec.1
  linarith

/-- Countable canonical sequence of valid rational balanced schedules with
target ceilings `balancedEnvelopeInfimum + 1 / (j + 1)`. -/
noncomputable def canonicalBalancedSchedule (j : ℕ) : BalancedRationalSchedule :=
  Classical.choose
    (exists_valid_balancedRationalSchedule (show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity))

theorem canonicalBalancedSchedule_valid (j : ℕ) :
    (canonicalBalancedSchedule j).Valid (balancedEnvelopeInfimum + 1 / ((j : ℝ) + 1)) :=
  Classical.choose_spec
    (exists_valid_balancedRationalSchedule (show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity))

/-- The single universal hard-input splitter obtained by multiplexing the
canonical sequence of rational balanced schedules. -/
noncomputable def balancedUniversalHard
    {α : BalancedRationalSchedule → ℕ → Type}
    (epoch : ∀ s n, PMF (α s n))
    (attempt : ∀ s n, α s n → Option (Factors n) × ℕ) : HardKernel :=
  universalEpochHard
    (fun j => epoch (canonicalBalancedSchedule j))
    (fun j => attempt (canonicalBalancedSchedule j))

/-- Any family of hard-input epochs parameterized by valid rational balanced
schedules from `rational_balanced_finite_budget` immediately yields ONE single
factoring algorithm achieving `balancedEnvelopeInfimum`
(in `(1.9839824118071388228, 1.9839824118071388230)`). -/
theorem factor_expected_balancedEnvelopeInfimum
    {α : BalancedRationalSchedule → ℕ → Type}
    (k : ℕ)
    (prep : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n ∧
      (RandomizedPreprocessing.run k n).2 ≤ (10000 * (k + 1)) ^ 32 * (n.log2 + 2) ^ 32)
    (epoch : ∀ s n, PMF (α s n))
    (attempt : ∀ s n, α s n → Option (Factors n) × ℕ)
    (hSched : ∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
      ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epoch s n) (fun a => ((attempt s n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((epoch s n).map (attempt s n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((D + δ) * scale n)) :
    1.9839824118071388228 < balancedEnvelopeInfimum ∧
    balancedEnvelopeInfimum < 1.9839824118071388230 ∧
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (factor k (fun m hm => (prep m hm).1) (balancedUniversalHard epoch attempt) n hn)
        (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  refine ⟨balancedEnvelopeInfimum_spec.1, balancedEnvelopeInfimum_spec.2.1, ?_⟩
  refine factor_expected_universal_epoch k prep
    (fun j => epoch (canonicalBalancedSchedule j))
    (fun j => attempt (canonicalBalancedSchedule j))
    balancedEnvelopeInfimum_nonneg
    (fun j => balancedEnvelopeInfimum + 1 / ((j : ℝ) + 1)) ?_ ?_
  · intro δ hδ
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    exact ⟨j, by linarith only [hj]⟩
  · intro j δ hδ
    exact hSched (canonicalBalancedSchedule j) _ (canonicalBalancedSchedule_valid j) δ hδ

/-- Full serialized end-to-end theorem at `C_* = balancedEnvelopeInfimum`:
under the critical-line hypothesis for Dirichlet L-functions, a single
multiplexed algorithm over valid rational balanced schedules emits certified
serialized prime factorizations with expected work
`≤ exp ((balancedEnvelopeInfimum + ε) * scale n)`. -/
theorem serialized_balancedEnvelopeInfimum_from_critical_line
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ {α : BalancedRationalSchedule → ℕ → Type}
      (epoch : ∀ s n, PMF (α s n))
      (attempt : ∀ s n, α s n → Option (Factors n) × ℕ),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
          Odd n → ¬n.Prime → ¬IsPrimePow n →
          ∃ W S : ℝ, 0 < S ∧
            mean (epoch s n) (fun a => ((attempt s n a).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
            S ≤ (((epoch s n).map (attempt s n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
            W / S ≤ exp ((D + δ) * scale n)) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound (balancedUniversalHard epoch attempt) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound (balancedUniversalHard epoch attempt) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤
            ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  obtain ⟨k, prep⟩ := RandomizedPreprocessing.of_critical_line line
  let sound := fun m hm => (prep m hm).1
  refine ⟨k, sound, ?_⟩
  intro α epoch attempt hSched
  obtain ⟨hlo, hhi, hfac⟩ := factor_expected_balancedEnvelopeInfimum k prep epoch attempt hSched
  exact ⟨hlo, hhi,
    fun _ hn _ => outputBits_support_correct k sound (balancedUniversalHard epoch attempt) hn,
    serializedFactor_expected_eventually k sound (balancedUniversalHard epoch attempt)
      balancedEnvelopeInfimum_nonneg hfac⟩

#print axioms truncateSplit_fail_le
#print axioms runPhase_support_work_le
#print axioms runPhase_fail_le_of_le
#print axioms universalSplitLaw_mean_ne_top
#print axioms universalSplitLaw_mean_le
#print axioms universalHardKernel_mean_le
#print axioms factor_expected_universal_hard
#print axioms factor_expected_universal_epoch
#print axioms serialized_universal_epoch_from_critical_line
#print axioms factor_expected_balancedEnvelopeInfimum
#print axioms serialized_balancedEnvelopeInfimum_from_critical_line

end Cogentic.RandomizedUniversalSchedule
