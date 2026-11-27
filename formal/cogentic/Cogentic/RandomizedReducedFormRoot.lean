import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int
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

private theorem gcdA_inverse_modEq {q N : ℤ} (hq : q.gcd N = 1) :
    q * q.gcdA N ≡ 1 [ZMOD N] := by
  have hbez := Int.gcd_eq_gcd_ab q N
  rw [hq, Int.natCast_one] at hbez
  exact Int.modEq_iff_dvd.2 ⟨q.gcdB N, by rw [hbez]; ring⟩

theorem normalized_root {a b c q N x y : ℤ} (ha : a = q ^ 2)
    (hdisc : b ^ 2 + N = a * c) (hq : q.gcd N = 1) :
    ((a * x + b * y) * q.gcdA N) ^ 2 ≡ formValue a b c x y [ZMOD N] := by
  have hinv := gcdA_inverse_modEq hq
  calc
    _ = (a * x + b * y) ^ 2 * (q.gcdA N) ^ 2 := by ring
    _ ≡ (a * formValue a b c x y) * (q.gcdA N) ^ 2 [ZMOD N] :=
      (lead_square hdisc).mul_right _
    _ = formValue a b c x y * (q * q.gcdA N) ^ 2 := by rw [ha]; ring
    _ ≡ formValue a b c x y [ZMOD N] := by simpa using (hinv.pow 2).mul_left (formValue a b c x y)

/-- A nonzero second coordinate contributes at least the modulus to the norm. -/
theorem norm_size_lower_of_y_ne_zero {a b c N x y : ℤ} (hN : 0 < N)
    (hdisc : b ^ 2 + N = a * c) (hy : y ≠ 0) :
    N ≤ a * formValue a b c x y := by
  have hypos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hyone : 1 ≤ y ^ 2 := by omega
  rw [← norm_identity (x := x) (y := y) hdisc]
  calc
    N = N * 1 := by rw [mul_one]
    _ ≤ N * y ^ 2 := mul_le_mul_of_nonneg_left hyone hN.le
    _ ≤ _ := le_add_of_nonneg_left (sq_nonneg _)

/-- A primitive column with zero second coordinate gives the original
square and its normalized root has one of the two global signs. -/
theorem normalized_root_of_y_zero {a b c q N x y : ℤ} (ha : a = q ^ 2)
    (hq : q.gcd N = 1) (hy : y = 0) (hprim : x.gcd y = 1) :
    formValue a b c x y = q ^ 2 ∧
      ((a * x + b * y) * q.gcdA N ≡ q [ZMOD N] ∨
        (a * x + b * y) * q.gcdA N ≡ -q [ZMOD N]) := by
  have hxabs : x.natAbs = (1 : ℤ).natAbs := by
    simpa [hy] using hprim
  have hsign := Int.natAbs_eq_natAbs_iff.mp hxabs
  have hx : x ^ 2 = 1 := by
    rcases hsign with h | h <;> simp [h]
  have hcong : (a * x + b * y) * q.gcdA N ≡ q * x [ZMOD N] := by
    calc
      _ = (q * x) * (q * q.gcdA N) := by rw [ha, hy]; ring
      _ ≡ (q * x) * 1 [ZMOD N] := (gcdA_inverse_modEq hq).mul_left _
      _ = _ := by rw [mul_one]
  refine ⟨by simp [formValue, ha, hy, hx], ?_⟩
  rcases hsign with h | h
  · exact Or.inl (by simpa [h] using hcong)
  · exact Or.inr (by simpa [h] using hcong)

/-- Below the product-size threshold only the original globally signed
root can arise from a primitive column. -/
theorem reduced_form_small_only_global_root {a b c q N x y : ℤ} (ha : a = q ^ 2)
    (hN : 0 < N) (hdisc : b ^ 2 + N = a * c) (hq : q.gcd N = 1)
    (hprim : x.gcd y = 1) (hsmall : q ^ 2 * formValue a b c x y < N) :
    y = 0 ∧ formValue a b c x y = q ^ 2 ∧
      ((a * x + b * y) * q.gcdA N ≡ q [ZMOD N] ∨
        (a * x + b * y) * q.gcdA N ≡ -q [ZMOD N]) := by
  have hy : y = 0 := by
    by_contra h
    exact (not_le_of_gt hsmall) (ha ▸ norm_size_lower_of_y_ne_zero hN hdisc h)
  exact ⟨hy, normalized_root_of_y_zero ha hq hy hprim⟩

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
  constructor
  · ring
  · unfold formValue
    ring

/-- A rotation takes the old second basis vector as its new first column. -/
theorem rotate (a b c x y : ℤ) :
    (-b) ^ 2 - c * a = b ^ 2 - a * c ∧
      formValue c (-b) a x y = formValue a b c (-y) x := by
  constructor
  · ring
  · unfold formValue
    ring

end Cogentic.RandomizedReducedFormRoot
