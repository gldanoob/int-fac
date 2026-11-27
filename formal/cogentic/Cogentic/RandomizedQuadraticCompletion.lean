import Cogentic.RandomizedPrimitiveQuadraticRoot
import Mathlib.Data.Int.ModEq

namespace Cogentic.RandomizedQuadraticCompletion

open RandomizedPrimitiveQuadraticRoot (formValue)

/-- The coordinates of (x,y) in the determinant-one basis with columns
(r,q) and (u,v), given by the integral inverse matrix. -/
theorem second_column_coordinates {r q u v x y : ℤ} (hS : r * v - q * u = 1) :
    x = (v * x - u * y) * r + (r * y - q * x) * u ∧
      y = (v * x - u * y) * q + (r * y - q * x) * v := by
  constructor
  · calc
      x = (r * v - q * u) * x := by rw [hS, one_mul]
      _ = _ := by ring
  · calc
      y = (r * v - q * u) * y := by rw [hS, one_mul]
      _ = _ := by ring

/-- Two determinant-one completions with the same first column have second
columns differing by an integer multiple of that first column. -/
theorem second_columns_of_completions {r q u v x y : ℤ}
    (hS : r * v - q * u = 1) (hT : r * y - q * x = 1) :
    ∃ k : ℤ, x = k * r + u ∧ y = k * q + v := by
  refine ⟨v * x - u * y, ?_⟩
  simpa only [hT, one_mul] using second_column_coordinates (x := x) (y := y) hS

/-- The full mixed coefficient after substituting the two indicated columns. -/
def mixedCoeff (a b c r q u v : ℤ) : ℤ :=
  2 * a * r * u + b * (r * v + q * u) + 2 * c * q * v

theorem formValue_after_completion (a b c r q u v s t : ℤ) :
    formValue a b c (r * s + u * t) (q * s + v * t) =
      formValue a b c r q * s ^ 2 +
        mixedCoeff a b c r q u v * s * t + formValue a b c u v * t ^ 2 := by
  unfold formValue mixedCoeff
  ring

/-- The mixed coefficient changes by the determinant of the new completion
and a multiple of twice the form value at the fixed first column. -/
theorem mixedCoeff_completion {a b c r q u v x y : ℤ} (hS : r * v - q * u = 1) :
    mixedCoeff a b c r q x y =
      (r * y - q * x) * mixedCoeff a b c r q u v +
        2 * formValue a b c r q * (v * x - u * y) := by
  obtain ⟨hx, hy⟩ := second_column_coordinates (x := x) (y := y) hS
  calc
    mixedCoeff a b c r q x y =
        mixedCoeff a b c r q ((v * x - u * y) * r + (r * y - q * x) * u)
          ((v * x - u * y) * q + (r * y - q * x) * v) := by rw [← hx, ← hy]
    _ = _ := by unfold mixedCoeff formValue; ring

theorem mixedCoeff_modEq_completion {a b c r q u v x y : ℤ} (hS : r * v - q * u = 1) :
    mixedCoeff a b c r q x y ≡ (r * y - q * x) * mixedCoeff a b c r q u v
      [ZMOD 2 * formValue a b c r q] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨u * y - v * x, ?_⟩
  rw [mixedCoeff_completion (x := x) (y := y) hS]
  ring

/-- A unimodular completion gives one of the two signed mixed coefficients
modulo twice the represented value. -/
theorem mixedCoeff_modEq_of_det_sign {a b c r q u v x y : ℤ}
    (hS : r * v - q * u = 1) (hT : r * y - q * x = 1 ∨ r * y - q * x = -1) :
    (mixedCoeff a b c r q x y ≡ mixedCoeff a b c r q u v [ZMOD 2 * formValue a b c r q]) ∨
      (mixedCoeff a b c r q x y ≡ -mixedCoeff a b c r q u v [ZMOD 2 * formValue a b c r q]) := by
  have hm := mixedCoeff_modEq_completion (a := a) (b := b) (c := c) (x := x) (y := y) hS
  rcases hT with h | h
  · exact Or.inl (by simpa only [h, one_mul] using hm)
  · exact Or.inr (by simpa only [h, neg_one_mul] using hm)

#print axioms second_columns_of_completions
#print axioms formValue_after_completion
#print axioms mixedCoeff_completion
#print axioms mixedCoeff_modEq_of_det_sign

end Cogentic.RandomizedQuadraticCompletion
