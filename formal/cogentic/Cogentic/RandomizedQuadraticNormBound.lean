import Cogentic.RandomizedPrimitiveQuadraticRoot
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith

namespace Cogentic.RandomizedQuadraticNormBound

open RandomizedPrimitiveQuadraticRoot (formValue)

/-- The full middle coefficient convention gives discriminant `b² - 4ac`. -/
theorem abs_discriminant_le_scaled_value_of_y_ne_zero {a b c D x y : ℤ}
    (hD : D = b ^ 2 - 4 * a * c) (hneg : D < 0) (hy : y ≠ 0) :
    |D| ≤ 4 * a * formValue a b c x y := by
  have hy' : 1 ≤ y ^ 2 := by
    have h := sq_pos_of_ne_zero hy
    omega
  have hscale : 0 ≤ (-D) * (y ^ 2 - 1) :=
    mul_nonneg (neg_nonneg.mpr hneg.le) (sub_nonneg.mpr hy')
  have hcomplete : 4 * a * formValue a b c x y = (2 * a * x + b * y) ^ 2 - D * y ^ 2 := by
    rw [hD]
    unfold formValue
    ring
  rw [hcomplete, abs_of_neg hneg]
  nlinarith only [hscale, sq_nonneg (2 * a * x + b * y)]

/-- A primitive vector is horizontal with value `a`, or its scaled value
is at least the magnitude of the discriminant. -/
theorem primitive_value_or_discriminant_bound {a b c D x y : ℤ}
    (hD : D = b ^ 2 - 4 * a * c) (hneg : D < 0) (hprimitive : x.gcd y = 1) :
    (y = 0 ∧ formValue a b c x y = a) ∨
      (y ≠ 0 ∧ |D| ≤ 4 * a * formValue a b c x y) := by
  by_cases hy : y = 0
  · subst y
    rw [Int.gcd_zero_right] at hprimitive
    refine Or.inl ⟨rfl, ?_⟩
    obtain hx | hx := Int.natAbs_eq_iff.mp hprimitive <;> simp [formValue, hx]
  · exact Or.inr ⟨hy, abs_discriminant_le_scaled_value_of_y_ne_zero hD hneg hy⟩

/-- A forbidden nonunit lead excludes the horizontal value. -/
theorem abs_discriminant_le_scaled_value_of_coprime {a b c D x y Z : ℤ}
    (hD : D = b ^ 2 - 4 * a * c) (hneg : D < 0) (hprimitive : x.gcd y = 1)
    (ha : 1 < a) (hdvd : a ∣ Z) (hcoprime : IsCoprime (formValue a b c x y) Z) :
    |D| ≤ 4 * a * formValue a b c x y := by
  rcases primitive_value_or_discriminant_bound hD hneg hprimitive with
    ⟨_, hval⟩ | ⟨_, hbound⟩
  · rw [hval] at hcoprime
    have hu := Int.isUnit_iff.mp (hcoprime.isUnit_of_dvd hdvd)
    omega
  · exact hbound

#print axioms abs_discriminant_le_scaled_value_of_y_ne_zero
#print axioms primitive_value_or_discriminant_bound
#print axioms abs_discriminant_le_scaled_value_of_coprime

end Cogentic.RandomizedQuadraticNormBound
