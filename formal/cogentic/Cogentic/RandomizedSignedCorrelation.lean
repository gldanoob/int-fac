import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open Finset
open scoped BigOperators

namespace Cogentic.RandomizedSignedCorrelation

variable {X I : Type*} [DecidableEq I]

def correlation {R : Type*} [Semiring R] (samples : Finset X) (f : I → X → R)
    (i j : I) : R :=
  ∑ x ∈ samples, f i x * f j x

/-- The square-sum of a signed sum splits into diagonal terms and ordered
off-diagonal correlations. -/
theorem sum_sq_eq_diagonal_add_offDiagonal {R : Type*} [Semiring R]
    (samples : Finset X) (indices : Finset I) (f : I → X → R) :
    (∑ x ∈ samples, (∑ i ∈ indices, f i x) ^ 2) =
      (∑ i ∈ indices, ∑ x ∈ samples, (f i x) ^ 2) +
        ∑ i ∈ indices, ∑ j ∈ indices.erase i, correlation samples f i j := by
  calc
    _ = ∑ x ∈ samples, ∑ i ∈ indices, ∑ j ∈ indices, f i x * f j x := by
      simp_rw [pow_two, sum_mul_sum]
    _ = ∑ i ∈ indices, ∑ j ∈ indices, correlation samples f i j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ = _ := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      simp_rw [pow_two]
      exact (add_sum_erase indices (correlation samples f i) hi).symm

/-- Uniform correlation bounds control the square-sum without requiring
nonnegative summands or exact orthogonality. -/
theorem sum_sq_le_of_correlation_bounds
    (samples : Finset X) (indices : Finset I) (f : I → X → ℝ)
    (diagonal offDiagonal : ℝ)
    (hdiag : ∀ i ∈ indices, (∑ x ∈ samples, (f i x) ^ 2) ≤ diagonal)
    (hoff : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → correlation samples f i j ≤ offDiagonal) :
    (∑ x ∈ samples, (∑ i ∈ indices, f i x) ^ 2) ≤
      (indices.card : ℝ) * diagonal +
        (indices.card : ℝ) * ((indices.card - 1 : ℕ) : ℝ) * offDiagonal := by
  rw [sum_sq_eq_diagonal_add_offDiagonal]
  apply add_le_add
  · calc
      _ ≤ ∑ _i ∈ indices, diagonal := sum_le_sum hdiag
      _ = _ := by simp [nsmul_eq_mul]
  · calc
      _ ≤ ∑ i ∈ indices, ∑ _j ∈ indices.erase i, offDiagonal := by
        apply sum_le_sum
        intro i hi
        apply sum_le_sum
        intro j hj
        obtain ⟨hne, hj'⟩ := mem_erase.mp hj
        exact hoff i hi j hj' hne.symm
      _ = ∑ _i ∈ indices, ((indices.card - 1 : ℕ) : ℝ) * offDiagonal := by
        apply sum_congr rfl
        intro i hi
        simp only [sum_const, nsmul_eq_mul, card_erase_of_mem hi]
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]

#print axioms sum_sq_eq_diagonal_add_offDiagonal
#print axioms sum_sq_le_of_correlation_bounds

end Cogentic.RandomizedSignedCorrelation
