import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedReducedFormMinimum

/-- The value of the binary form with coefficients A, 2b, C. -/
def form (A b C x y : ℤ) : ℤ := A * x ^ 2 + 2 * b * x * y + C * y ^ 2

/-- In the closed reduced region, the first coefficient is the minimum over
nonzero integer vectors, including boundary forms. -/
theorem min_le_value {A b C x y : ℤ} (hA : 0 < A) (hb : |2 * b| ≤ A)
    (hAC : A ≤ C) (hxy : x ≠ 0 ∨ y ≠ 0) :
    A ≤ form A b C x y := by
  have hmix : -(A * (|x| * |y|)) ≤ 2 * b * x * y := by
    have hbound : |2 * b * x * y| ≤ A * (|x| * |y|) := by
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact (neg_le_neg hbound).trans (neg_abs_le _)
  have hy : A * y ^ 2 ≤ C * y ^ 2 := mul_le_mul_of_nonneg_right hAC (sq_nonneg y)
  have hunit : 1 ≤ x ^ 2 + y ^ 2 - |x| * |y| := by
    by_cases hx : x = 0
    · have hy' : y ≠ 0 := hxy.resolve_left (fun h => h hx)
      have hy1 : (1 : ℤ) ≤ |y| := by
        have h := abs_pos.mpr hy'
        omega
      have hsq : (1 : ℤ) ≤ y ^ 2 := by
        simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 1) hy1 2
      simpa [hx] using hsq
    · by_cases hy' : y = 0
      · have hx1 : (1 : ℤ) ≤ |x| := by
          have h := abs_pos.mpr hx
          omega
        have hsq : (1 : ℤ) ≤ x ^ 2 := by
          simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 1) hx1 2
        simpa [hy'] using hsq
      · have hx1 : (1 : ℤ) ≤ |x| := by
          have h := abs_pos.mpr hx
          omega
        have hy1 : (1 : ℤ) ≤ |y| := by
          have h := abs_pos.mpr hy'
          omega
        have hprod : (1 : ℤ) ≤ |x| * |y| := by
          simpa using mul_le_mul hx1 hy1 (by decide : (0 : ℤ) ≤ 1) (abs_nonneg x)
        have hsq := sq_nonneg (|x| - |y|)
        have habsx : |x| ^ 2 = x ^ 2 := sq_abs x
        have habsy : |y| ^ 2 = y ^ 2 := sq_abs y
        nlinarith only [hprod, hsq, habsx, habsy]
  have hscaled := mul_le_mul_of_nonneg_left hunit hA.le
  unfold form
  nlinarith only [hmix, hy, hscaled]

@[simp] theorem value_at_first (A b C : ℤ) : form A b C 1 0 = A := by
  simp [form]

/-- For determinant N, a reduced leading coefficient satisfies 3 A² ≤ 4N. -/
theorem leading_square_bound {A b C N : ℤ} (hA : 0 < A) (hb : |2 * b| ≤ A)
    (hAC : A ≤ C) (hdet : A * C = b ^ 2 + N) :
    3 * A ^ 2 ≤ 4 * N := by
  have hsq := pow_le_pow_left₀ (abs_nonneg (2 * b)) hb 2
  rw [sq_abs] at hsq
  have hprod := mul_le_mul_of_nonneg_left hAC hA.le
  nlinarith only [hsq, hprod, hdet]

/-- An integral root of minus N modulo A inside the reduced strip gives an
integer reduced representative when A² ≤ N. -/
theorem reduced_representative {A b N : ℤ} (hA : 0 < A) (hroot : A ∣ b ^ 2 + N)
    (hb : 2 * |b| ≤ A) (hbound : A ^ 2 ≤ N) :
    ∃ C : ℤ, |2 * b| ≤ A ∧ A ≤ C ∧ A * C = b ^ 2 + N ∧
      ∀ x y : ℤ, x ≠ 0 ∨ y ≠ 0 → A ≤ form A b C x y := by
  obtain ⟨C, hC⟩ := hroot
  have hb' : |2 * b| ≤ A := by simpa [abs_mul] using hb
  have hAC : A ≤ C := by
    have hprod : A * A ≤ A * C := by nlinarith only [sq_nonneg b, hbound, hC]
    exact (mul_le_mul_iff_of_pos_left hA).1 hprod
  exact ⟨C, hb', hAC, hC.symm, fun _ _ hxy => min_le_value hA hb' hAC hxy⟩

end Cogentic.RandomizedReducedFormMinimum
