import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Cogentic.RandomizedRectangularAbel

/-- The rectangular prefix sum through row i and column j, inclusive. -/
def rectangularPrefix {R : Type*} [AddCommMonoid R] (d : ℕ → ℕ → R) (i j : ℕ) : R :=
  ∑ k ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (j + 1), d k l

/-- The mixed forward difference of the weight array. -/
def mixedDifference {R : Type*} [Sub R] (w : ℕ → ℕ → R) (i j : ℕ) : R :=
  (w i j - w (i + 1) j) - (w i (j + 1) - w (i + 1) (j + 1))

private theorem sum_range_zero_end {R : Type*} [CommRing R]
    (n : ℕ) (f g : ℕ → R) (hzero : f n = 0) :
    (∑ i ∈ Finset.range n, f i * g i) =
      ∑ i ∈ Finset.range n, (f i - f (i + 1)) * (∑ k ∈ Finset.range (i + 1), g k) := by
  cases n with
  | zero => simp
  | succ n =>
    have hab := Finset.sum_range_by_parts f g (n + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at hab
    have hflip (i : ℕ) :
        (f (i + 1) - f i) * (∑ k ∈ Finset.range (i + 1), g k) =
          -((f i - f (i + 1)) * (∑ k ∈ Finset.range (i + 1), g k)) := by ring
    simp_rw [hflip, Finset.sum_neg_distrib, sub_neg_eq_add] at hab
    rw [hab]
    conv_rhs => rw [Finset.sum_range_succ, hzero, sub_zero]
    exact add_comm _ _

/-- Finite rectangular summation by parts with a zero boundary on each
upper face. Either side length may be zero. -/
theorem sum_eq_sum_prefix_mul_difference {R : Type*} [CommRing R]
    (m n : ℕ) (d w : ℕ → ℕ → R)
    (hrow : ∀ j, w m j = 0) (hcolumn : ∀ i, w i n = 0) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, d i j * w i j) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, rectangularPrefix d i j * mixedDifference w i j := by
  calc
    _ = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m, w i j * d i j := by
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m,
        (w i j - w (i + 1) j) * (∑ k ∈ Finset.range (i + 1), d k j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_range_zero_end m (fun i => w i j) (fun i => d i j) (hrow j)
    _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
        (w i j - w (i + 1) j) * (∑ k ∈ Finset.range (i + 1), d k j) := Finset.sum_comm
    _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
        mixedDifference w i j * (∑ l ∈ Finset.range (j + 1), ∑ k ∈ Finset.range (i + 1), d k l) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_range_zero_end n (fun j => w i j - w (i + 1) j)
        (fun j => ∑ k ∈ Finset.range (i + 1), d k j) (by simp only [hcolumn, sub_self])
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [rectangularPrefix, Finset.sum_comm, mul_comm]

/-- The total mixed variation controls a weighted array whenever each
rectangular prefix sum is bounded in norm. -/
theorem norm_sum_le_prefix_bound_mul_variation {R : Type*} [SeminormedCommRing R]
    (m n : ℕ) (d w : ℕ → ℕ → R) (E : ℝ)
    (hrow : ∀ j, w m j = 0) (hcolumn : ∀ i, w i n = 0)
    (hprefix : ∀ i < m, ∀ j < n, ‖rectangularPrefix d i j‖ ≤ E) :
    ‖∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, d i j * w i j‖ ≤
      E * (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, ‖mixedDifference w i j‖) := by
  rw [sum_eq_sum_prefix_mul_difference m n d w hrow hcolumn]
  calc
    _ ≤ ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
        ‖rectangularPrefix d i j * mixedDifference w i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
        E * ‖mixedDifference w i j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (hprefix i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)) (norm_nonneg _))
    _ = _ := by simp_rw [Finset.mul_sum]

#print axioms sum_eq_sum_prefix_mul_difference
#print axioms norm_sum_le_prefix_bound_mul_variation

end Cogentic.RandomizedRectangularAbel
