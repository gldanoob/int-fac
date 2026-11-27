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

/-- Clearing the positive denominator gives the window estimate over
ordered rings, including the integers. -/
theorem discriminant_window_mul {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {t D v Z : R}
    (ht : 0 ≤ t) (hD : 0 ≤ D) (hZ : 0 ≤ Z) (hnorm : t ^ 2 + D * v ^ 2 = 4 * Z ^ 2) :
    0 ≤ 2 * Z - t ∧ (2 * Z - t) * (2 * Z) ≤ D * v ^ 2 := by
  have h2Z : 0 ≤ 2 * Z := by linarith only [hZ]
  have hsq : t ^ 2 ≤ (2 * Z) ^ 2 := by
    nlinarith only [hnorm, mul_nonneg hD (sq_nonneg v)]
  have hgap : 0 ≤ 2 * Z - t := sub_nonneg.mpr (le_of_sq_le_sq hsq h2Z)
  refine ⟨hgap, ?_⟩
  calc
    _ ≤ (2 * Z - t) * (2 * Z + t) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht) hgap
    _ = D * v ^ 2 := by nlinarith only [hnorm]

theorem discriminant_window {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {t D v Z : R}
    (ht : 0 ≤ t) (hD : 0 ≤ D) (hZ : 0 < Z) (hnorm : t ^ 2 + D * v ^ 2 = 4 * Z ^ 2) :
    0 ≤ 2 * Z - t ∧ 2 * Z - t ≤ D * v ^ 2 / (2 * Z) := by
  obtain ⟨hgap, hmul⟩ := discriminant_window_mul ht hD hZ.le hnorm
  have h2Z : 0 < 2 * Z := by linarith only [hZ]
  exact ⟨hgap, (le_div_iff₀ h2Z).mpr hmul⟩

theorem discriminant_window_of_discriminant_le {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {t D c V v Z : R}
    (ht : 0 ≤ t) (hD : 0 ≤ D) (hZ : 0 < Z) (hupper : D ≤ c * V ^ 2)
    (hnorm : t ^ 2 + D * v ^ 2 = 4 * Z ^ 2) :
    0 ≤ 2 * Z - t ∧ 2 * Z - t ≤ c * (v * V) ^ 2 / (2 * Z) := by
  obtain ⟨hgap, hw⟩ := discriminant_window ht hD hZ hnorm
  refine ⟨hgap, hw.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by linarith only [hZ])
  have h := mul_le_mul_of_nonneg_right hupper (sq_nonneg v)
  exact h.trans_eq (by ring)

/-- A lower bound for the discriminant coefficient bounds the height
coordinate. The absolute value also covers signed coordinates. -/
theorem abs_mul_le_two_of_sq_le_discriminant {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {t D V v Z : R}
    (hZ : 0 ≤ Z) (hD : V ^ 2 ≤ D) (hnorm : t ^ 2 + D * v ^ 2 = 4 * Z ^ 2) :
    |v * V| ≤ 2 * Z := by
  apply abs_le_of_sq_le_sq _ (by linarith only [hZ])
  have hmul := mul_le_mul_of_nonneg_right hD (sq_nonneg v)
  nlinarith only [hnorm, hmul, sq_nonneg t]

#print axioms discriminant_window_mul
#print axioms discriminant_window
#print axioms discriminant_window_of_discriminant_le
#print axioms abs_mul_le_two_of_sq_le_discriminant
#print axioms abs_discriminant_le_scaled_value_of_y_ne_zero
#print axioms primitive_value_or_discriminant_bound
#print axioms abs_discriminant_le_scaled_value_of_coprime
#print axioms abs_discriminant_le_scaled_value_of_odd
#print axioms exists_odd_value_le_abs_discriminant_add

end Cogentic.RandomizedQuadraticNormBound
