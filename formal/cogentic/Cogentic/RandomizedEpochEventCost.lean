import Cogentic.RandomizedCappedEpoch

namespace Cogentic.RandomizedCappedEpoch

open RandomizedCostedFactorLaw
open scoped ENNReal

/-- The denominator in the finite-retry bound is exactly the probability
that the observed, charged attempt returns a verified output. -/
theorem one_sub_failure_eq_success {α β : Type*} (p : PMF α)
    (attempt : α → Option β × ℕ) :
    1 - mean p (fun a => failFlag (attempt a).1) =
      (p.map attempt).toOuterMeasure {o | o.1 ≠ none} := by
  classical
  let success (a : α) : ℝ≥0∞ := if (attempt a).1 = none then 0 else 1
  have hsum : mean p success + mean p (fun a => failFlag (attempt a).1) = 1 := by
    rw [← mean_add, ← mean_const p 1]
    congr 1
    funext a
    cases h : (attempt a).1 <;> simp [success, failFlag, h]
  have hf : mean p (fun a => failFlag (attempt a).1) ≤ 1 :=
    (le_add_left le_rfl).trans_eq hsum
  rw [ENNReal.sub_eq_of_eq_add (ne_top_of_le_ne_top ENNReal.one_ne_top hf) hsum.symm,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro a
  by_cases h : (attempt a).1 = none <;> simp [success, h]

/-- Separate estimates for the charge and for the probability of the
observed success event bound the ratio used in the factoring recurrence. -/
theorem epoch_ratio_le_of_real_bounds {α β : Type*} (p : PMF α)
    (attempt : α → Option β × ℕ) {W S : ℝ} (hS : 0 < S)
    (work : mean p (fun a => ((attempt a).2+1 : ℕ)) + 1 ≤ ENNReal.ofReal W)
    (hit : S ≤ ((p.map attempt).toOuterMeasure {o | o.1 ≠ none}).toReal) :
    (mean p (fun a => ((attempt a).2+1 : ℕ)) + 1) /
        (1 - mean p (fun a => failFlag (attempt a).1)) ≤ ENNReal.ofReal (W/S) := by
  rw [one_sub_failure_eq_success, ENNReal.ofReal_div_of_pos hS]
  refine ENNReal.div_le_div work ((ENNReal.ofReal_le_ofReal hit).trans ?_)
  exact ENNReal.ofReal_toReal_le

#print axioms one_sub_failure_eq_success
#print axioms epoch_ratio_le_of_real_bounds

end Cogentic.RandomizedCappedEpoch
