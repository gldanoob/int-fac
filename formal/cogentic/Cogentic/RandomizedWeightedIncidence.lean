import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open Finset
open scoped BigOperators

namespace Cogentic.RandomizedWeightedIncidence

variable {H L : Type*}

/-- The square of each label's incident weight counts ordered object pairs. -/
theorem sum_incident_sq_eq (objects : Finset H) (labels : Finset L)
    (R : H → L → Prop) [DecidableRel R] (w : H → ℝ) :
    (∑ l ∈ labels, (∑ x ∈ objects.filter (fun x => R x l), w x) ^ 2) =
      ∑ x ∈ objects, ∑ y ∈ objects,
        ((labels.filter (fun l => R x l ∧ R y l)).card : ℝ) * (w x * w y) := by
  calc
    _ = ∑ l ∈ labels, ∑ x ∈ objects, ∑ y ∈ objects,
        (if R x l then w x else 0) * (if R y l then w y else 0) := by
      simp_rw [sum_filter, pow_two, sum_mul, mul_sum]
    _ = ∑ x ∈ objects, ∑ y ∈ objects, ∑ l ∈ labels,
        (if R x l then w x else 0) * (if R y l then w y else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      have hterm (l : L) :
          (if R x l then w x else 0) * (if R y l then w y else 0) =
            if R x l ∧ R y l then w x * w y else 0 := by
        by_cases hx : R x l <;> by_cases hy : R y l <;> simp [hx, hy]
      simp_rw [hterm, ← sum_filter, sum_const, nsmul_eq_mul]

/-- Pairwise common-label and individual degree bounds control the second
moment of the total weight incident to a label. -/
theorem sum_incident_sq_le (objects : Finset H) (labels : Finset L)
    (R : H → L → Prop) [DecidableRel R] (w : H → ℝ) (D E : ℕ)
    (hw : ∀ x ∈ objects, 0 ≤ w x)
    (hpair : ∀ x ∈ objects, ∀ y ∈ objects, x ≠ y →
      (labels.filter (fun l => R x l ∧ R y l)).card ≤ D)
    (hself : ∀ x ∈ objects, (labels.filter (R x)).card ≤ E) :
    (∑ l ∈ labels, (∑ x ∈ objects.filter (fun x => R x l), w x) ^ 2) ≤
      (D : ℝ) * (∑ x ∈ objects, w x) ^ 2 + (E : ℝ) * ∑ x ∈ objects, w x ^ 2 := by
  classical
  rw [sum_incident_sq_eq]
  calc
    _ ≤ ∑ x ∈ objects, ∑ y ∈ objects,
        ((D : ℝ) * (w x * w y) + (if x = y then (E : ℝ) * w x ^ 2 else 0)) := by
      apply sum_le_sum
      intro x hx
      apply sum_le_sum
      intro y hy
      have hnonneg := mul_nonneg (hw x hx) (hw y hy)
      by_cases hxy : x = y
      · subst y
        rw [if_pos rfl]
        have hcap : ((labels.filter (fun l => R x l ∧ R x l)).card : ℝ) ≤ E := by
          exact_mod_cast (show (labels.filter (fun l => R x l ∧ R x l)).card ≤ E by
            simpa only [and_self] using hself x hx)
        calc
          _ ≤ (E : ℝ) * w x ^ 2 := by
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right hcap hnonneg
          _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hnonneg)
      · rw [if_neg hxy, add_zero]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hpair x hx y hy hxy) hnonneg
    _ = _ := by
      simp only [sum_add_distrib]
      congr 1
      · simp only [pow_two, sum_mul, mul_sum]
        apply sum_congr rfl
        intro x _
        apply sum_congr rfl
        intro y _
        rw [mul_comm (w x) (w y)]
      · rw [mul_sum]
        apply sum_congr rfl
        intro x hx
        simp only [sum_ite_eq, hx, if_true]

#print axioms sum_incident_sq_eq
#print axioms sum_incident_sq_le

end Cogentic.RandomizedWeightedIncidence
