import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedPrimitiveQuadraticRoot

/-- Evaluate a binary quadratic form using its full middle coefficient. -/
def formValue (a b c x y : ℤ) : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2

private def cross (a b c r Q u v : ℤ) : ℤ :=
  2 * a * r * u + b * (r * v + Q * u) + 2 * c * Q * v

private theorem primitive_completion {r Q : ℤ} (hgcd : r.gcd Q = 1) :
    ∃ u v : ℤ, r * v - Q * u = 1 := by
  refine ⟨-Int.gcdB r Q, Int.gcdA r Q, ?_⟩
  have h := Int.gcd_eq_gcd_ab r Q
  rw [hgcd] at h
  simpa only [Int.natCast_one, mul_neg, sub_neg_eq_add] using h.symm

/-- A homogeneous quadratic vanishing at a primitive pair has the
corresponding primitive integer linear factor. -/
theorem factor_of_primitive_root {a b c r Q : ℤ} (hgcd : r.gcd Q = 1)
    (hroot : formValue a b c r Q = 0) :
    ∃ l m : ℤ, ∀ x y : ℤ, formValue a b c x y = (Q * x - r * y) * (l * x + m * y) := by
  obtain ⟨u, v, hdet⟩ := primitive_completion hgcd
  let B := cross a b c r Q u v
  let C := formValue a b c u v
  refine ⟨-B * v + C * Q, B * u - C * r, ?_⟩
  intro x y
  let s := v * x - u * y
  let t := -Q * x + r * y
  have hs : r * s + u * t = x := calc
    _ = (r * v - Q * u) * x := by unfold s t; ring
    _ = _ := by rw [hdet, one_mul]
  have ht : Q * s + v * t = y := calc
    _ = (r * v - Q * u) * y := by unfold s t; ring
    _ = _ := by rw [hdet, one_mul]
  calc
    formValue a b c x y = formValue a b c (r * s + u * t) (Q * s + v * t) := by rw [hs, ht]
    _ = formValue a b c r Q * s ^ 2 + B * s * t + C * t ^ 2 := by
      unfold B C formValue cross
      ring
    _ = _ := by rw [hroot]; unfold s t; ring

/-- An integral binary quadratic with a primitive zero has square discriminant. -/
theorem square_discriminant_of_primitive_root {a b c r Q : ℤ} (hgcd : r.gcd Q = 1)
    (hroot : formValue a b c r Q = 0) :
    ∃ s : ℤ, b ^ 2 - 4 * a * c = s ^ 2 := by
  obtain ⟨u, v, hdet⟩ := primitive_completion hgcd
  refine ⟨cross a b c r Q u v, ?_⟩
  calc
    b ^ 2 - 4 * a * c = (r * v - Q * u) ^ 2 * (b ^ 2 - 4 * a * c) := by rw [hdet]; ring
    _ = cross a b c r Q u v ^ 2 - 4 * formValue a b c r Q * formValue a b c u v := by
      unfold cross formValue
      ring
    _ = _ := by rw [hroot]; ring

/-- A common primitive evaluation with a shared factor forces a square
discriminant for the combination that cancels their values. -/
theorem square_discriminant_of_common_multiple
    {a b c A B C r Q p n₁ n₂ : ℤ} (hgcd : r.gcd Q = 1)
    (hh : formValue a b c r Q = p * n₁) (hg : formValue A B C r Q = p * n₂) :
    ∃ s : ℤ,
      (n₂ * b - n₁ * B) ^ 2 - 4 * (n₂ * a - n₁ * A) * (n₂ * c - n₁ * C) = s ^ 2 := by
  apply square_discriminant_of_primitive_root hgcd
  calc
    formValue (n₂ * a - n₁ * A) (n₂ * b - n₁ * B) (n₂ * c - n₁ * C) r Q =
        n₂ * formValue a b c r Q - n₁ * formValue A B C r Q := by
      unfold formValue
      ring
    _ = 0 := by rw [hh, hg]; ring

#print axioms factor_of_primitive_root
#print axioms square_discriminant_of_primitive_root
#print axioms square_discriminant_of_common_multiple

end Cogentic.RandomizedPrimitiveQuadraticRoot
