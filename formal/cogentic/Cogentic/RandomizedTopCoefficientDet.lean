import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block

open Polynomial
open scoped BigOperators Polynomial

namespace Cogentic.RandomizedTopCoefficientDet

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Multiplication by p, projected onto coefficient degrees d through d+r−1. -/
noncomputable def topProjection (d : ℕ) (p : R[X]) : Matrix (Fin r) (Fin r) R :=
  fun i j => (p * X ^ (j : ℕ)).coeff (d + (i : ℕ))

/-- The polynomial with the prescribed r coefficient slots. -/
noncomputable def slotPolynomial (w : Fin r → R) : R[X] :=
  ∑ j : Fin r, X ^ (j : ℕ) * C (w j)

theorem topProjection_mulVec (d : ℕ) (p : R[X]) (w : Fin r → R) (i : Fin r) :
    (topProjection d p).mulVec w i = (p * slotPolynomial w).coeff (d + (i : ℕ)) := by
  simp only [topProjection, slotPolynomial, Matrix.mulVec, dotProduct, Finset.mul_sum,
    finsetSum_coeff, ← mul_assoc, coeff_mul_C]

theorem topProjection_isUpperTriangular {d : ℕ} {p : R[X]} (hp : p.natDegree ≤ d) :
    (topProjection (r := r) d p).IsUpperTriangular := by
  intro i j hij
  have hji : (j : ℕ) < (i : ℕ) := hij
  have hj : (j : ℕ) ≤ d + (i : ℕ) := by omega
  change (p * X ^ (j : ℕ)).coeff (d + (i : ℕ)) = 0
  rw [coeff_mul_X_pow', if_pos hj]
  apply coeff_eq_zero_of_natDegree_lt
  omega

/-- The diagonal coefficient controls the top projection determinant,
including the empty matrix. -/
theorem det_topProjection {d : ℕ} {p : R[X]} (hp : p.natDegree ≤ d) :
    (topProjection (r := r) d p).det = p.coeff d ^ r := by
  rw [Matrix.det_of_isUpperTriangular (topProjection_isUpperTriangular hp)]
  simp [topProjection]

theorem det_topProjection_mul {d : ℕ} {p : R[X]} (hp : p.natDegree ≤ d)
    (basis : Matrix (Fin r) (Fin r) R) :
    (topProjection d p * basis).det = p.coeff d ^ r * basis.det := by
  rw [Matrix.det_mul, det_topProjection hp]

noncomputable def quadratic (c₀ c₁ c₂ : R) : R[X] :=
  monomial 0 c₀ + monomial 1 c₁ + monomial 2 c₂

private theorem quadratic_natDegree_le (c₀ c₁ c₂ : R) :
    (quadratic c₀ c₁ c₂).natDegree ≤ 2 := by
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · exact (natDegree_monomial_le c₀).trans (by decide)
    · exact (natDegree_monomial_le c₁).trans (by decide)
  · exact natDegree_monomial_le c₂

/-- For a quadratic multiplier the projected degrees are 2 through r+1. -/
theorem det_quadratic_topProjection (c₀ c₁ c₂ : R) :
    (topProjection (r := r) 2 (quadratic c₀ c₁ c₂)).det = c₂ ^ r := by
  rw [det_topProjection (quadratic_natDegree_le c₀ c₁ c₂)]
  simp [quadratic, coeff_monomial]

theorem det_quadratic_topProjection_mul (c₀ c₁ c₂ : R)
    (basis : Matrix (Fin r) (Fin r) R) :
    (topProjection 2 (quadratic c₀ c₁ c₂) * basis).det = c₂ ^ r * basis.det := by
  rw [Matrix.det_mul, det_quadratic_topProjection]

#print axioms topProjection_mulVec
#print axioms det_quadratic_topProjection
#print axioms det_quadratic_topProjection_mul

end Cogentic.RandomizedTopCoefficientDet
