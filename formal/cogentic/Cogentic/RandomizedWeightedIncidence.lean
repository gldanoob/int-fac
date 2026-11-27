import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators Finset

namespace Cogentic.RandomizedWeightedIncidence

variable {H L : Type*}

/-- Reindexing by object counts its weight once per incident label. -/
theorem sum_incident_eq_degree_mul (objects : Finset H) (labels : Finset L)
    (R : H → L → Prop) [DecidableRel R] (w : H → ℝ) :
    (∑ l ∈ labels, ∑ x ∈ objects.filter (fun x => R x l), w x) =
      ∑ x ∈ objects, ((labels.filter (R x)).card : ℝ) * w x := by
  simp_rw [sum_filter]
  rw [sum_comm]
  simp_rw [← sum_filter, sum_const, nsmul_eq_mul]

/-- Each pair contributes its weight once for every shared label. -/
theorem sum_incident_pair_weights_eq (objects : Finset H) (labels : Finset L)
    (R : H → L → Prop) [DecidableRel R] (w : H → H → ℝ) :
    (∑ l ∈ labels, ∑ x ∈ objects.filter (fun x => R x l),
      ∑ y ∈ objects.filter (fun y => R y l), w x y) =
      ∑ x ∈ objects, ∑ y ∈ objects,
        ((labels.filter (fun l => R x l ∧ R y l)).card : ℝ) * w x y := by
  calc
    _ = ∑ l ∈ labels, ∑ z ∈ (objects ×ˢ objects).filter (fun z => R z.1 l ∧ R z.2 l),
        w z.1 z.2 := by
      apply sum_congr rfl
      intro l _
      rw [filter_product (fun x => R x l) (fun y => R y l)]
      exact (sum_product' _ _ w).symm
    _ = _ := by
      rw [sum_incident_eq_degree_mul]
      exact sum_product _ _ (fun p : H × H =>
        ((labels.filter (fun l => R p.1 l ∧ R p.2 l)).card : ℝ) * w p.1 p.2)

/-- With nonnegative weights, the smaller incident degree controls each pair. -/
theorem sum_incident_pair_weights_le (objects : Finset H) (labels : Finset L)
    (R : H → L → Prop) [DecidableRel R] (w : H → H → ℝ) (d : H → ℕ)
    (hw : ∀ x ∈ objects, ∀ y ∈ objects, 0 ≤ w x y)
    (hd : ∀ x ∈ objects, (labels.filter (R x)).card ≤ d x) :
    (∑ l ∈ labels, ∑ x ∈ objects.filter (fun x => R x l),
      ∑ y ∈ objects.filter (fun y => R y l), w x y) ≤
      ∑ x ∈ objects, ∑ y ∈ objects, (min (d x) (d y) : ℝ) * w x y := by
  rw [sum_incident_pair_weights_eq]
  apply sum_le_sum
  intro x hx
  apply sum_le_sum
  intro y hy
  have hleft : (labels.filter (fun l => R x l ∧ R y l)).card ≤ (labels.filter (R x)).card :=
    card_le_card fun _ hl =>
      mem_filter.mpr ⟨(mem_filter.mp hl).1, (mem_filter.mp hl).2.1⟩
  have hright : (labels.filter (fun l => R x l ∧ R y l)).card ≤ (labels.filter (R y)).card :=
    card_le_card fun _ hl =>
      mem_filter.mpr ⟨(mem_filter.mp hl).1, (mem_filter.mp hl).2.2⟩
  have hdegree : (labels.filter (fun l => R x l ∧ R y l)).card ≤ min (d x) (d y) :=
    le_min (hleft.trans (hd x hx)) (hright.trans (hd y hy))
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) (hw x hx y hy)

theorem sum_incident_pair_weights_le_of_degree_le (objects : Finset H) (labels : Finset L)
    (R : H → L → Prop) [DecidableRel R] (w : H → H → ℝ) (d : ℕ)
    (hw : ∀ x ∈ objects, ∀ y ∈ objects, 0 ≤ w x y)
    (hd : ∀ x ∈ objects, (labels.filter (R x)).card ≤ d) :
    (∑ l ∈ labels, ∑ x ∈ objects.filter (fun x => R x l),
      ∑ y ∈ objects.filter (fun y => R y l), w x y) ≤
      (d : ℝ) * ∑ x ∈ objects, ∑ y ∈ objects, w x y := by
  simpa only [min_self, ← mul_sum] using
    sum_incident_pair_weights_le objects labels R w (fun _ => d) hw hd

/-- The square of each label's incident weight counts ordered object pairs. -/
theorem sum_incident_sq_eq (objects : Finset H) (labels : Finset L)
    (R : H → L → Prop) [DecidableRel R] (w : H → ℝ) :
    (∑ l ∈ labels, (∑ x ∈ objects.filter (fun x => R x l), w x) ^ 2) =
      ∑ x ∈ objects, ∑ y ∈ objects,
        ((labels.filter (fun l => R x l ∧ R y l)).card : ℝ) * (w x * w y) := by
  simpa only [pow_two, sum_mul_sum] using
    sum_incident_pair_weights_eq objects labels R (fun x y => w x * w y)

/-- The second moment of label mass is bounded by its largest possible
value times the incidence degree bound and total object weight. -/
theorem sum_incident_sq_le_of_mass_cap (objects : Finset H) (labels : Finset L)
    (R : H → L → Prop) [DecidableRel R] (w : H → ℝ) (d : ℕ) (C : ℝ)
    (hw : ∀ x ∈ objects, 0 ≤ w x) (hC : 0 ≤ C)
    (hd : ∀ x ∈ objects, (labels.filter (R x)).card ≤ d)
    (hcap : ∀ l ∈ labels, (∑ x ∈ objects.filter (fun x => R x l), w x) ≤ C) :
    (∑ l ∈ labels, (∑ x ∈ objects.filter (fun x => R x l), w x) ^ 2) ≤
      C * (d : ℝ) * ∑ x ∈ objects, w x := by
  calc
    _ ≤ ∑ l ∈ labels, C * ∑ x ∈ objects.filter (fun x => R x l), w x := by
      apply sum_le_sum
      intro l hl
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hcap l hl)
        (sum_nonneg fun x hx => hw x (mem_filter.mp hx).1)
    _ = C * ∑ x ∈ objects, ((labels.filter (R x)).card : ℝ) * w x := by
      rw [← mul_sum, sum_incident_eq_degree_mul]
    _ ≤ C * ∑ x ∈ objects, (d : ℝ) * w x :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hd x hx)) (hw x hx)) hC
    _ = _ := by rw [← mul_sum, mul_assoc]

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

/-- A finite cover by sets of size at least two has total cardinality minus
one per set at least half the number of covered vertices. -/
theorem card_le_twice_sum_card_sub_one_of_cover [DecidableEq L]
    (vertices : Finset L) (indices : Finset H) (edge : H → Finset L)
    (hcover : vertices ⊆ indices.biUnion edge)
    (hsize : ∀ i ∈ indices, 2 ≤ (edge i).card) :
    vertices.card ≤ 2 * ∑ i ∈ indices, ((edge i).card - 1) := by
  calc
    vertices.card ≤ (indices.biUnion edge).card := card_le_card hcover
    _ ≤ ∑ i ∈ indices, (edge i).card := card_biUnion_le
    _ ≤ 2 * ∑ i ∈ indices, ((edge i).card - 1) := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have h := hsize i hi
      omega

#print axioms card_le_twice_sum_card_sub_one_of_cover
#print axioms mul_le_twice_center_mul_add_sq
#print axioms sum_weighted_mul_le_twice_center_add_sq
#print axioms sum_weighted_sq_sub_eq_of_centered
#print axioms sum_incident_eq_degree_mul
#print axioms sum_incident_pair_weights_eq
#print axioms sum_incident_pair_weights_le
#print axioms sum_incident_pair_weights_le_of_degree_le
#print axioms sum_incident_sq_le_of_mass_cap
#print axioms sum_incident_sq_eq
#print axioms sum_incident_sq_le

end Cogentic.RandomizedWeightedIncidence
