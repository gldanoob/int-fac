import Cogentic.RandomizedCostedFactorLaw
import Mathlib.Analysis.SpecificLimits.Normed

namespace Cogentic.RandomizedCappedEpoch

open RandomizedCostedFactorLaw
open scoped ENNReal BigOperators

/-- Sample at most the prescribed number of fresh epochs. Evaluate the
deterministic fallback only after every attempt has failed. The unit charge
pays for branching on the epoch result. -/
noncomputable def run {α β : Type*} (epoch : PMF α) (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) : ℕ → PMF (β × ℕ)
  | 0 => PMF.pure (fallback ())
  | r+1 => epoch.bind fun a =>
    let out := attempt a
    match out.1 with
    | some b => PMF.pure (b, out.2+1)
    | none => (run epoch attempt fallback r).map fun b => (b.1, out.2+1+b.2)

def failFlag {β : Type*} : Option β → ℝ≥0∞
  | none => 1
  | some _ => 0

/-- The expected charge counts the work of missed epochs as well as the cost
of the fallback, weighted by the probability that all epochs missed. -/
theorem cost_succ {α β : Type*} (epoch : PMF α) (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (r : ℕ) :
    mean (run epoch attempt fallback (r+1)) (fun b => b.2) =
      mean epoch (fun a => ((attempt a).2+1 : ℕ)) +
        mean epoch (fun a => failFlag (attempt a).1) *
          mean (run epoch attempt fallback r) (fun b => b.2) := by
  let z := mean (run epoch attempt fallback r) (fun b => b.2)
  have hmul : mean epoch (fun a => failFlag (attempt a).1 * z) =
      mean epoch (fun a => failFlag (attempt a).1) * z := by
    simp only [mean, ← mul_assoc, ENNReal.tsum_mul_right]
  change _ = _ + _ * z
  rw [← hmul, ← mean_add, run, mean_bind]
  congr 1
  funext a
  cases h : (attempt a).1 with
  | some b => simp [h, failFlag, mean_pure]
  | none =>
    simp only [h, mean_map, Nat.cast_add, Nat.cast_one, failFlag, one_mul]
    exact (mean_add _ _ _).trans (congrArg (· + z) (mean_const _ _))

/-- For every finite cap the full expected charge is a finite geometric
sum of actual epoch means plus the cost of reaching the fallback. -/
theorem cost_eq {α β : Type*} (epoch : PMF α) (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (r : ℕ) :
    let w := mean epoch (fun a => ((attempt a).2+1 : ℕ))
    let q := mean epoch (fun a => failFlag (attempt a).1)
    mean (run epoch attempt fallback r) (fun b => b.2) =
      w * (∑ i ∈ Finset.range r, q^i) + q^r * (fallback ()).2 := by
  dsimp only
  induction r with
  | zero => simp [run, mean_pure]
  | succ r ih =>
    let q := mean epoch (fun a => failFlag (attempt a).1)
    have geom : (∑ i ∈ Finset.range (r+1), q^i) = 1 + q*(∑ i ∈ Finset.range r, q^i) := by
      rw [Finset.sum_range_succ', pow_zero, add_comm, Finset.mul_sum]
      simp only [pow_succ']
    rw [cost_succ, ih, geom, pow_succ']
    dsimp [q]
    ring

/-- A predetermined cap at least the deterministic fallback cost makes the
worst-case fallback charge harmless in expectation for every positive success
rate. No success probability is needed when choosing the cap. -/
theorem cost_le {α β : Type*} (epoch : PMF α) (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (r : ℕ) (hr : (fallback ()).2 ≤ r) :
    let w := mean epoch (fun a => ((attempt a).2+1 : ℕ))
    let q := mean epoch (fun a => failFlag (attempt a).1)
    mean (run epoch attempt fallback r) (fun b => b.2) ≤ (w+1)/(1-q) := by
  let w := mean epoch (fun a => ((attempt a).2+1 : ℕ))
  let q := mean epoch (fun a => failFlag (attempt a).1)
  have hflag (o : Option β) : failFlag o ≤ 1 := by cases o <;> simp [failFlag]
  have hq : q ≤ 1 := by
    rw [← mean_const epoch 1]
    apply ENNReal.tsum_le_tsum
    intro a
    exact mul_le_mul_right (hflag (attempt a).1) _
  let S := ∑ i ∈ Finset.range r, q^i
  have hpowers : (r : ℝ≥0∞)*q^r ≤ S := by
    calc
      _ = ∑ _i ∈ Finset.range r, q^r := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => pow_le_pow_of_le_one (show 0 ≤ q from zero_le) hq (Finset.mem_range.mp hi).le
  have hsum : S ≤ (1-q)⁻¹ := by
    rw [← ENNReal.tsum_geometric]
    exact ENNReal.summable.sum_le_tsum _ (fun _ _ => zero_le)
  rw [cost_eq]
  change w*S + q^r*(fallback ()).2 ≤ _
  calc
    _ ≤ w*S + S := by
      refine add_le_add le_rfl ?_
      rw [mul_comm]
      exact (mul_le_mul_left (Nat.cast_le.mpr hr) _).trans hpowers
    _ = (w+1)*S := by rw [add_mul, one_mul]
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_right hsum _

#print axioms cost_eq
#print axioms cost_le

end Cogentic.RandomizedCappedEpoch
