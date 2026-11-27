import Cogentic.RandomizedPrimitiveQuadraticRoot
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith

namespace Cogentic.RandomizedQuadraticNormBound

open RandomizedPrimitiveQuadraticRoot (formValue)

private theorem complete_square {a b c D : ℤ} (hD : D = b ^ 2 - 4 * a * c) (x y : ℤ) :
    4 * a * formValue a b c x y = (2 * a * x + b * y) ^ 2 - D * y ^ 2 := by
  rw [hD]
  unfold formValue
  ring

/-- The full middle coefficient convention gives discriminant `b² - 4ac`. -/
theorem abs_discriminant_le_scaled_value_of_y_ne_zero {a b c D x y : ℤ}
    (hD : D = b ^ 2 - 4 * a * c) (hneg : D < 0) (hy : y ≠ 0) :
    |D| ≤ 4 * a * formValue a b c x y := by
  have hy' : 1 ≤ y ^ 2 := by
    have h := sq_pos_of_ne_zero hy
    omega
  have hscale : 0 ≤ (-D) * (y ^ 2 - 1) :=
    mul_nonneg (neg_nonneg.mpr hneg.le) (sub_nonneg.mpr hy')
  rw [complete_square hD, abs_of_neg hneg]
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

/-- An even lead excludes the horizontal vector when its value must be odd. -/
theorem abs_discriminant_le_scaled_value_of_odd {a b c D x y : ℤ}
    (hD : D = b ^ 2 - 4 * a * c) (hneg : D < 0)
    (hprimitive : x.gcd y = 1) (ha : Even a) (hodd : Odd (formValue a b c x y)) :
    |D| ≤ 4 * a * formValue a b c x y := by
  rcases primitive_value_or_discriminant_bound hD hneg hprimitive with
    ⟨_, hval⟩ | ⟨_, hbound⟩
  · rw [hval] at hodd
    exact (Int.not_odd_iff_even.mpr ha hodd).elim
  · exact hbound

/-- One of three primitive vectors with second coordinate one represents an odd
value within the stated additive error of the discriminant bound. -/
theorem exists_odd_value_le_abs_discriminant_add {a b c D : ℤ}
    (hD : D = b ^ 2 - 4 * a * c) (hneg : D < 0) (ha : 0 < a)
    (ha_even : Even a) (hb_odd : Odd b) (hb : |b| ≤ a) :
    ∃ x : ℤ, (x = -1 ∨ x = 0 ∨ x = 1) ∧ x.gcd 1 = 1 ∧
      Odd (formValue a b c x 1) ∧ |2 * a * x + b| ≤ 2 * a ∧
      4 * a * formValue a b c x 1 ≤ |D| + 4 * a ^ 2 := by
  have hchoose : ∃ x : ℤ, (x = -1 ∨ x = 0 ∨ x = 1) ∧
      Odd (formValue a b c x 1) ∧ |2 * a * x + b| ≤ 2 * a := by
    rcases Int.even_or_odd c with hc | hc
    · obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
      by_cases hb₀ : 0 ≤ b
      · refine ⟨-1, Or.inl rfl, ?_, ?_⟩
        · rw [show formValue a b c (-1) 1 = a - b + c by unfold formValue; ring]
          exact (ha_even.sub_odd hb_odd).add_even hc
        · apply abs_le.mpr
          rw [mul_neg_one]
          constructor <;> omega
      · refine ⟨1, Or.inr (Or.inr rfl), ?_, ?_⟩
        · simpa [formValue] using (ha_even.add_odd hb_odd).add_even hc
        · apply abs_le.mpr
          rw [mul_one]
          constructor <;> omega
    · exact ⟨0, Or.inr (Or.inl rfl), by simpa [formValue] using hc,
        by simpa only [mul_zero, zero_add] using hb.trans (by omega)⟩
  obtain ⟨x, hx, hodd, hres⟩ := hchoose
  refine ⟨x, hx, Int.gcd_one_right x, hodd, hres, ?_⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hres 2
  rw [sq_abs] at hsq
  rw [complete_square hD, one_pow, mul_one, abs_of_neg hneg]
  nlinarith only [hsq]

#print axioms abs_discriminant_le_scaled_value_of_y_ne_zero
#print axioms primitive_value_or_discriminant_bound
#print axioms abs_discriminant_le_scaled_value_of_coprime
#print axioms abs_discriminant_le_scaled_value_of_odd
#print axioms exists_odd_value_le_abs_discriminant_add

end Cogentic.RandomizedQuadraticNormBound
