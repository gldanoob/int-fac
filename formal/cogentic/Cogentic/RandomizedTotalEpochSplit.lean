import Cogentic.RandomizedCappedTape
import Cogentic.RandomizedEpochKernel
import Cogentic.RandomizedTrialFallback

namespace Cogentic.RandomizedTotalEpochSplit

open RandomizedCostedFactorLaw RandomizedCappedEpoch RandomizedEpochKernel
open scoped ENNReal

private def fallback {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime) (_ : Unit) : Factors n × ℕ :=
  let s := RandomizedTrialFallback.split n hn hp
  (⟨(s.left,s.right),s.left_ge,s.right_ge,s.product⟩,s.work)

private def outcome {n : ℕ} (v : Factors n × ℕ) : SplitOutcome n :=
  ⟨v.1.val.1, v.1.val.2, v.2, v.1.property.1, v.1.property.2.1, v.1.property.2.2⟩

/-- A single composite input, with a finite number of candidate epochs and
a charged trial-division split on the tape where every one of them misses. -/
def splitTape {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (attempt : α → Option (Factors n) × ℕ) (tape : Fin (RandomizedTrialFallback.cap n) → α) :
    SplitOutcome n :=
  outcome (runTape attempt (fallback hn hp) _ tape)

/-- Execute on a tape by passing its current index and accumulated charge.
The same tape function is used at every iteration. -/
def splitFrom {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (attempt : α → Option (Factors n) × ℕ) (tape : ℕ → α) : SplitOutcome n :=
  outcome (runFrom attempt (fallback hn hp) tape (RandomizedTrialFallback.cap n) 0 0)

theorem splitFrom_eq {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (attempt : α → Option (Factors n) × ℕ) (tape : ℕ → α) :
    splitFrom hn hp attempt tape = splitTape hn hp attempt (fun i => tape i.val) := by
  simp [splitFrom, splitTape, runFrom_eq_runTape]

/-- Law of the actual finite tape interpreter on independent epoch blocks. -/
noncomputable def splitLaw {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (epoch : PMF α) (attempt : α → Option (Factors n) × ℕ) : PMF (SplitOutcome n) :=
  (blockLaw epoch (RandomizedTrialFallback.cap n)).map (splitTape hn hp attempt)

/-- Every tape returns certified factors within a finite charge, even when
all of its proposed epochs fail. -/
theorem splitTape_work_le {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (attempt : α → Option (Factors n) × ℕ) (W : ℕ) (hW : ∀ a, (attempt a).2+1 ≤ W)
    (tape : Fin (RandomizedTrialFallback.cap n) → α) :
    (splitTape hn hp attempt tape).work ≤ RandomizedTrialFallback.cap n * (W+1) := by
  exact (runTape_work_le attempt (fallback hn hp) W hW _ tape).trans
    ((Nat.add_le_add le_rfl (RandomizedTrialFallback.split_work_le n hn hp)).trans_eq
      (by rw [Nat.mul_add, Nat.mul_one]))

/-- Finiteness on small composite inputs uses only boundedly many finite
blocks, even if the candidate never proposes a split on that input. -/
theorem splitLaw_mean_ne_top {α : Type*} [Fintype α] {n : ℕ}
    (hn : 2 ≤ n) (hp : ¬n.Prime) (epoch : PMF α) (attempt : α → Option (Factors n) × ℕ) :
    mean (splitLaw hn hp epoch attempt) (fun s => s.work) ≠ ⊤ := by
  rw [splitLaw, mean_map, mean, tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun a _ => ENNReal.mul_ne_top ((blockLaw epoch _).apply_ne_top a) (by simp))

/-- Only the mean cost and failure probability of one attempt enter the
expected bound. The worst-case trial-division cost is already included. -/
theorem splitLaw_mean_le {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (epoch : PMF α) (attempt : α → Option (Factors n) × ℕ) :
    mean (splitLaw hn hp epoch attempt) (fun s => s.work) ≤
      (mean epoch (fun a => ((attempt a).2+1 : ℕ)) + 1) /
        (1 - mean epoch (fun a => failFlag (attempt a).1)) := by
  have hmap : splitLaw hn hp epoch attempt =
      (run epoch attempt (fallback hn hp) (RandomizedTrialFallback.cap n)).map outcome := by
    rw [← runTape_law, PMF.map_comp]
    rfl
  rw [hmap, mean_map]
  exact cost_le epoch attempt (fallback hn hp) _ (RandomizedTrialFallback.split_work_le n hn hp)

#print axioms splitTape_work_le
#print axioms splitLaw_mean_le

end Cogentic.RandomizedTotalEpochSplit
