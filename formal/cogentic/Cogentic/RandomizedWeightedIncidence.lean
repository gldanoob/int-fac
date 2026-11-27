import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

theorem mul_le_twice_center_mul_add_sq {a b n μ : ℝ}
    (ha : 0 ≤ a) (han : a ≤ n) (hbn : b ≤ n) :
    a * b ≤ 2 * μ * a + (n - μ) ^ 2 := by
  have h : a * (b - 2 * μ) ≤ (n - μ) ^ 2 := by
    by_cases hn : n ≤ 2 * μ
    · exact (mul_nonpos_of_nonneg_of_nonpos ha (sub_nonpos.mpr (hbn.trans hn))).trans
        (sq_nonneg _)
    · calc
        _ ≤ a * (n - 2 * μ) := mul_le_mul_of_nonneg_left (sub_le_sub_right hbn _) ha
        _ ≤ n * (n - 2 * μ) :=
          mul_le_mul_of_nonneg_right han (sub_nonneg.mpr (le_of_not_ge hn))
        _ ≤ _ := by nlinarith only [sq_nonneg μ]
  nlinarith only [h]

/-- A common pointwise envelope controls a weighted product by one first
moment and the squared deviation of the envelope from the center. -/
theorem sum_weighted_mul_le_twice_center_add_sq (samples : Finset H)
    (w a b n : H → ℝ) (μ : ℝ) (hw : ∀ x ∈ samples, 0 ≤ w x)
    (ha : ∀ x ∈ samples, 0 ≤ a x)
    (han : ∀ x ∈ samples, a x ≤ n x) (hbn : ∀ x ∈ samples, b x ≤ n x) :
    (∑ x ∈ samples, w x * (a x * b x)) ≤
      2 * μ * (∑ x ∈ samples, w x * a x) + ∑ x ∈ samples, w x * (n x - μ) ^ 2 := by
  calc
    _ ≤ ∑ x ∈ samples, w x * (2 * μ * a x + (n x - μ) ^ 2) :=
      sum_le_sum fun x hx => mul_le_mul_of_nonneg_left
        (mul_le_twice_center_mul_add_sq (ha x hx) (han x hx) (hbn x hx)) (hw x hx)
    _ = _ := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1
      exact sum_congr rfl fun _ _ => by ring

/-- Re-centering a weighted squared deviation at a zero-mean center
adds the squared shift times the total weight. -/
theorem sum_weighted_sq_sub_eq_of_centered (samples : Finset H) (w n : H → ℝ)
    (μ ν : ℝ) (hcenter : ∑ x ∈ samples, w x * (n x - ν) = 0) :
    (∑ x ∈ samples, w x * (n x - μ) ^ 2) =
      (∑ x ∈ samples, w x * (n x - ν) ^ 2) +
        (ν - μ) ^ 2 * (∑ x ∈ samples, w x) := by
  calc
    _ = ∑ x ∈ samples, (w x * (n x - ν) ^ 2 +
        (2 * (ν - μ) * (w x * (n x - ν)) + (ν - μ) ^ 2 * w x)) :=
      sum_congr rfl fun _ _ => by ring
    _ = _ := by simp only [sum_add_distrib, ← mul_sum, hcenter, mul_zero, zero_add]

#print axioms mul_le_twice_center_mul_add_sq
#print axioms sum_weighted_mul_le_twice_center_add_sq
#print axioms sum_weighted_sq_sub_eq_of_centered
#print axioms sum_incident_sq_eq
#print axioms sum_incident_sq_le

end Cogentic.RandomizedWeightedIncidence
