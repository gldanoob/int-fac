import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedReducedFormRoot

def formValue (a b c x y : ℤ) : ℤ :=
  a * x ^ 2 + 2 * b * x * y + c * y ^ 2

theorem norm_identity {a b c N x y : ℤ} (hdisc : b ^ 2 + N = a * c) :
    (a * x + b * y) ^ 2 + N * y ^ 2 = a * formValue a b c x y := by
  calc
    _ = a * formValue a b c x y + (b ^ 2 + N - a * c) * y ^ 2 := by
      unfold formValue
      ring
    _ = _ := by rw [hdisc, sub_self, zero_mul, add_zero]

theorem lead_square {a b c N x y : ℤ} (hdisc : b ^ 2 + N = a * c) :
    (a * x + b * y) ^ 2 ≡ a * formValue a b c x y [ZMOD N] := by
  apply Int.modEq_iff_dvd.2
  refine ⟨y ^ 2, ?_⟩
  rw [← norm_identity (x := x) (y := y) hdisc]
  ring

theorem normalized_root {a b c q N x y : ℤ} (ha : a = q ^ 2)
    (hdisc : b ^ 2 + N = a * c) (hq : q.gcd N = 1) :
    ((a * x + b * y) * q.gcdA N) ^ 2 ≡ formValue a b c x y [ZMOD N] := by
  have hbez := Int.gcd_eq_gcd_ab q N
  rw [hq, Int.natCast_one] at hbez
  have hinv : q * q.gcdA N ≡ 1 [ZMOD N] :=
    Int.modEq_iff_dvd.2 ⟨q.gcdB N, by rw [hbez]; ring⟩
  calc
    _ = (a * x + b * y) ^ 2 * (q.gcdA N) ^ 2 := by ring
    _ ≡ (a * formValue a b c x y) * (q.gcdA N) ^ 2 [ZMOD N] :=
      (lead_square hdisc).mul_right _
    _ = formValue a b c x y * (q * q.gcdA N) ^ 2 := by rw [ha]; ring
    _ ≡ formValue a b c x y [ZMOD N] := by simpa using (hinv.pow 2).mul_left (formValue a b c x y)

theorem gcd_root_iff {z A N : ℤ} (hroot : z ^ 2 ≡ A [ZMOD N]) :
    z.gcd N = 1 ↔ A.gcd N = 1 := by
  have hg : (z ^ 2).gcd N = A.gcd N := by
    rw [← Int.gcd_emod (z ^ 2) N, ← Int.gcd_emod A N]
    rw [show z ^ 2 % N = A % N from hroot]
  constructor
  · intro hz
    exact hg ▸ Int.gcd_pow_left_of_gcd_eq_one hz
  · intro hA
    have hd := Int.gcd_dvd_gcd_mul_right_left z N z
    rw [← pow_two, hg, hA] at hd
    exact Nat.dvd_one.mp hd

/-- A change of the second basis vector leaves the first column unchanged. -/
theorem shear (a b c k x y : ℤ) :
    (b + a * k) ^ 2 - a * (c + 2 * b * k + a * k ^ 2) = b ^ 2 - a * c ∧
      formValue a (b + a * k) (c + 2 * b * k + a * k ^ 2) x y =
        formValue a b c (x + k * y) y := by
  constructor <;> simp only [formValue] <;> ring

/-- A rotation takes the old second basis vector as its new first column. -/
theorem rotate (a b c x y : ℤ) :
    (-b) ^ 2 - c * a = b ^ 2 - a * c ∧
      formValue c (-b) a x y = formValue a b c (-y) x := by
  constructor <;> simp only [formValue] <;> ring

end Cogentic.RandomizedReducedFormRoot
