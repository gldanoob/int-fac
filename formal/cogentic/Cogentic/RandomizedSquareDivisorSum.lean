import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedSquareDivisorSum

open Finset
open scoped BigOperators

/-- The positive integers whose square divides a positive index. -/
def squareRootDivisors (m : ℕ) : Finset ℕ :=
  (Ioc 0 m.sqrt).filter (fun b => b ^ 2 ∣ m)

theorem mem_squareRootDivisors {b m : ℕ} (hm : 0 < m) :
    b ∈ squareRootDivisors m ↔ 0 < b ∧ b ^ 2 ∣ m := by
  simp only [squareRootDivisors, mem_filter, mem_Ioc]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hb, hdvd⟩
    exact ⟨⟨hb, Nat.le_sqrt'.mpr (Nat.le_of_dvd hm hdvd)⟩, hdvd⟩

/-- Summing square divisors in the opposite order counts their positive multiples. -/
theorem weighted_sum_squareRootDivisors_eq (X : ℕ) :
    (∑ m ∈ Ioc 0 X, ∑ b ∈ squareRootDivisors m, b) =
      ∑ b ∈ Ioc 0 X.sqrt, b * (X / b ^ 2) := by
  calc
    _ = ∑ m ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X.sqrt, if b ^ 2 ∣ m then b else 0 := by
      apply sum_congr rfl
      intro m hm
      obtain ⟨hm₀, hmX⟩ := mem_Ioc.mp hm
      rw [← sum_filter]
      congr 1
      ext b
      simp only [mem_squareRootDivisors hm₀, mem_filter, mem_Ioc]
      constructor
      · rintro ⟨hb, hdvd⟩
        exact ⟨⟨hb, Nat.le_sqrt'.mpr ((Nat.le_of_dvd hm₀ hdvd).trans hmX)⟩, hdvd⟩
      · exact fun h => ⟨h.1.1, h.2⟩
    _ = ∑ b ∈ Ioc 0 X.sqrt, ∑ m ∈ Ioc 0 X, if b ^ 2 ∣ m then b else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro b _
      rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
      rfl

theorem weighted_sum_squareRootDivisors_le_harmonic (X : ℕ) :
    (((∑ m ∈ Ioc 0 X, ∑ b ∈ squareRootDivisors m, b) : ℕ) : ℝ) ≤
      (X : ℝ) * ∑ b ∈ Ioc 0 X.sqrt, 1 / (b : ℝ) := by
  rw [weighted_sum_squareRootDivisors_eq, Nat.cast_sum, mul_sum]
  apply sum_le_sum
  intro b hb
  have hb₀ : 0 < (b : ℝ) := Nat.cast_pos.mpr (mem_Ioc.mp hb).1
  rw [mul_one_div]
  apply (le_div_iff₀ hb₀).mpr
  calc
    _ = ((X / b ^ 2 * b ^ 2 : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_pow]
      ring
    _ ≤ _ := Nat.cast_le.mpr (Nat.div_mul_le_self X (b ^ 2))

/-- Every positive square-root divisor, including the largest, is
bounded by the weighted square-divisor sum. -/
theorem le_sum_squareRootDivisors {b m : ℕ} (hm : 0 < m) (hb : 0 < b) (hdvd : b ^ 2 ∣ m) :
    b ≤ ∑ j ∈ squareRootDivisors m, j :=
  single_le_sum (f := fun j : ℕ => j) (fun _ _ => Nat.zero_le _)
    ((mem_squareRootDivisors hm).mpr ⟨hb, hdvd⟩)

theorem sum_squareRootDivisor_selection_le_harmonic (X : ℕ) (w : ℕ → ℕ)
    (hw : ∀ m ∈ Ioc 0 X, 0 < w m ∧ (w m) ^ 2 ∣ m) :
    (((∑ m ∈ Ioc 0 X, w m) : ℕ) : ℝ) ≤ (X : ℝ) * ∑ b ∈ Ioc 0 X.sqrt, 1 / (b : ℝ) := by
  apply le_trans _ (weighted_sum_squareRootDivisors_le_harmonic X)
  have h : (∑ m ∈ Ioc 0 X, w m) ≤ ∑ m ∈ Ioc 0 X, ∑ b ∈ squareRootDivisors m, b :=
    sum_le_sum fun m hm => le_sum_squareRootDivisors (mem_Ioc.mp hm).1 (hw m hm).1 (hw m hm).2
  exact Nat.cast_le.mpr h

#print axioms weighted_sum_squareRootDivisors_eq
#print axioms weighted_sum_squareRootDivisors_le_harmonic
#print axioms le_sum_squareRootDivisors
#print axioms sum_squareRootDivisor_selection_le_harmonic

end Cogentic.RandomizedSquareDivisorSum
