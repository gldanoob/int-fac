import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
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

private theorem discriminant_transform (a b c x y u v : ℤ) :
    (x * v - y * u) ^ 2 * (b ^ 2 - 4 * a * c) =
      cross a b c x y u v ^ 2 - 4 * formValue a b c x y * formValue a b c u v := by
  unfold cross formValue
  ring

/-- For a form of negative discriminant, the product of its values controls
the squared determinant of the two representing vectors. -/
theorem formValue_product_identity {a b c D : ℤ} (hD : D = b ^ 2 - 4 * a * c)
    (hneg : D < 0) (x y u v : ℤ) :
    4 * formValue a b c x y * formValue a b c u v =
      (2 * a * x * u + b * (x * v + y * u) + 2 * c * y * v) ^ 2 +
        |D| * (x * v - y * u) ^ 2 := by
  have h := discriminant_transform a b c x y u v
  rw [← hD] at h
  rw [abs_of_neg hneg]
  unfold cross at h
  nlinarith only [h]

theorem det_eq_zero_of_small_formValue_product {a b c D x y u v : ℤ}
    (hD : D = b ^ 2 - 4 * a * c) (hneg : D < 0)
    (hsmall : 4 * formValue a b c x y * formValue a b c u v < |D|) :
    x * v - y * u = 0 := by
  by_contra hdet
  have hsq : 1 ≤ (x * v - y * u) ^ 2 := by
    have h := sq_pos_of_ne_zero hdet
    omega
  have hscale := mul_le_mul_of_nonneg_left hsq (abs_nonneg D)
  have h := formValue_product_identity hD hneg x y u v
  linarith only [hsmall, hscale, h, sq_nonneg (2 * a * x * u + b * (x * v + y * u) + 2 * c * y * v)]

theorem primitive_pair_eq_or_neg_of_det_zero {x y u v : ℤ}
    (hxy : x.gcd y = 1) (huv : u.gcd v = 1) (hdet : x * v - y * u = 0) :
    (u = x ∧ v = y) ∨ (u = -x ∧ v = -y) := by
  obtain ⟨s, t, h⟩ := primitive_completion hxy
  let k := t * u - s * v
  have hu : u = k * x := calc
    u = (x * t - y * s) * u := by rw [h, one_mul]
    _ = k * x + (x * v - y * u) * s := by unfold k; ring
    _ = k * x := by rw [hdet, zero_mul, add_zero]
  have hv : v = k * y := calc
    v = (x * t - y * s) * v := by rw [h, one_mul]
    _ = k * y + (x * v - y * u) * t := by unfold k; ring
    _ = k * y := by rw [hdet, zero_mul, add_zero]
  have hk : k * (x * Int.gcdA u v + y * Int.gcdB u v) = 1 := by
    have hbez := Int.gcd_eq_gcd_ab u v
    rw [huv, Int.natCast_one] at hbez
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← hu, ← hv, ← hbez]
  obtain hpos | hneg := Int.eq_one_or_neg_one_of_mul_eq_one hk
  · exact Or.inl ⟨by simpa only [hpos, one_mul] using hu, by simpa only [hpos, one_mul] using hv⟩
  · exact Or.inr ⟨by simpa only [hneg, neg_one_mul] using hu, by simpa only [hneg, neg_one_mul] using hv⟩

/-- Two primitive vectors with product of values below the discriminant
threshold agree up to a simultaneous sign. -/
theorem primitive_pair_eq_or_neg_of_small_formValue_product {a b c D x y u v : ℤ}
    (hD : D = b ^ 2 - 4 * a * c) (hneg : D < 0)
    (hxy : x.gcd y = 1) (huv : u.gcd v = 1)
    (hsmall : 4 * formValue a b c x y * formValue a b c u v < |D|) :
    (u = x ∧ v = y) ∨ (u = -x ∧ v = -y) :=
  primitive_pair_eq_or_neg_of_det_zero hxy huv (det_eq_zero_of_small_formValue_product hD hneg hsmall)

/-- An integral binary quadratic with a primitive zero has square discriminant. -/
theorem square_discriminant_of_primitive_root {a b c r Q : ℤ} (hgcd : r.gcd Q = 1)
    (hroot : formValue a b c r Q = 0) :
    ∃ s : ℤ, b ^ 2 - 4 * a * c = s ^ 2 := by
  obtain ⟨u, v, hdet⟩ := primitive_completion hgcd
  refine ⟨cross a b c r Q u v, ?_⟩
  calc
    b ^ 2 - 4 * a * c = (r * v - Q * u) ^ 2 * (b ^ 2 - 4 * a * c) := by rw [hdet]; ring
    _ = cross a b c r Q u v ^ 2 - 4 * formValue a b c r Q * formValue a b c u v :=
      discriminant_transform a b c r Q u v
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

#print axioms formValue_product_identity
#print axioms det_eq_zero_of_small_formValue_product
#print axioms primitive_pair_eq_or_neg_of_det_zero
#print axioms primitive_pair_eq_or_neg_of_small_formValue_product
#print axioms factor_of_primitive_root
#print axioms square_discriminant_of_primitive_root
#print axioms square_discriminant_of_common_multiple

end Cogentic.RandomizedPrimitiveQuadraticRoot
