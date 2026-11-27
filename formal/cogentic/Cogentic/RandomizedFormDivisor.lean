import Cogentic.RandomizedReducedFormRoot
import Mathlib.Tactic.LinearCombination

namespace Cogentic.RandomizedFormDivisor

open RandomizedReducedFormRoot

/-- On the sublattice prescribed by r, division by M gives an integral form.
Its determinant agrees with that of the original form. -/
theorem prescribed_divisor {A b C M r k : ℤ}
    (hroot : formValue A b C r 1 = M * k) :
    (A * M) * k - (A * r + b) ^ 2 = A * C - b ^ 2 ∧
    ∀ x y : ℤ, M * formValue (A * M) (A * r + b) k x y =
      formValue A b C (M * x + r * y) y := by
  have hk : A * r ^ 2 + 2 * b * r + C = M * k := by
    simpa [formValue] using hroot
  constructor
  · linear_combination -A * hk
  · intro x y
    unfold formValue
    linear_combination -y ^ 2 * hk

/-- The divided value is represented by the new integer coefficients. -/
theorem quotient_value {A b C M r k x y : ℤ} (hM : M ≠ 0)
    (hroot : formValue A b C r 1 = M * k) :
    formValue A b C (M * x + r * y) y / M = formValue (A * M) (A * r + b) k x y := by
  rw [← (prescribed_divisor hroot).2, Int.mul_ediv_cancel_left _ hM]

/-- Complementary integral substitution reverses the divisor transform. -/
theorem reverse_prescribed_divisor {A b C M r k x y : ℤ} (hM : M ≠ 0)
    (hroot : formValue A b C r 1 = M * k) :
    formValue (A * M) (A * r + b) k (x - r * y) (M * y) =
      M * formValue A b C x y := by
  apply mul_left_cancel₀ hM
  rw [(prescribed_divisor hroot).2]
  unfold formValue
  ring

private theorem mod_inverse {s N : ℤ} (hs : s.gcd N = 1) :
    s * s.gcdA N ≡ 1 [ZMOD N] := by
  have hb := Int.gcd_eq_gcd_ab s N
  rw [hs, Int.natCast_one] at hb
  exact Int.modEq_iff_dvd.mpr ⟨s.gcdB N, by rw [hb]; ring⟩

private theorem cancel_square_factor {M v z s N : ℤ}
    (hs : s ^ 2 ≡ M [ZMOD N]) (hunit : M.gcd N = 1) (hz : z ^ 2 ≡ M * v [ZMOD N]) :
    (z * s.gcdA N) ^ 2 ≡ v [ZMOD N] := by
  have hi := mod_inverse ((gcd_root_iff hs).mpr hunit)
  calc
    _ = z ^ 2 * (s.gcdA N) ^ 2 := by ring
    _ ≡ (M * v) * (s.gcdA N) ^ 2 [ZMOD N] := hz.mul_right _
    _ ≡ (s ^ 2 * v) * (s.gcdA N) ^ 2 [ZMOD N] := (hs.symm.mul_right v).mul_right _
    _ = v * (s * s.gcdA N) ^ 2 := by ring
    _ ≡ v [ZMOD N] := by simpa using (hi.pow 2).mul_left v

/-- A private root of the original represented value can be divided by a
known modular root of M to obtain a root of the divided form's value. -/
theorem normalize_private_root {A b C M r k x y z s N : ℤ}
    (hroot : formValue A b C r 1 = M * k)
    (hs : s ^ 2 ≡ M [ZMOD N]) (hunit : M.gcd N = 1)
    (hz : z ^ 2 ≡ formValue A b C (M * x + r * y) y [ZMOD N]) :
    (z * s.gcdA N) ^ 2 ≡ formValue (A * M) (A * r + b) k x y [ZMOD N] :=
  cancel_square_factor hs hunit ((prescribed_divisor hroot).2 x y ▸ hz)

/-- Known modular square roots of A and M compose to normalize the linear
norm root of the transformed form. -/
theorem compose_form_root {A b C M r k x y s t N : ℤ}
    (hroot : formValue A b C r 1 = M * k) (hdisc : b ^ 2 + N = A * C)
    (hs : s ^ 2 ≡ A [ZMOD N]) (ht : t ^ 2 ≡ M [ZMOD N])
    (hAunit : A.gcd N = 1) (hMunit : M.gcd N = 1) :
    (((A * M) * x + (A * r + b) * y) * s.gcdA N * t.gcdA N) ^ 2 ≡
      formValue (A * M) (A * r + b) k x y [ZMOD N] := by
  have hz := cancel_square_factor hs hAunit (lead_square (x := M * x + r * y) (y := y) hdisc)
  have he : A * (M * x + r * y) + b * y = (A * M) * x + (A * r + b) * y := by ring
  rw [← he]
  exact normalize_private_root hroot ht hMunit hz

end Cogentic.RandomizedFormDivisor
