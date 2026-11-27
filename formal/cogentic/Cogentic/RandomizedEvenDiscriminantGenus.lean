import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.GCD

namespace Cogentic.RandomizedEvenDiscriminantGenus

/-- Canonical reduction inequalities for a positive form with middle coefficient `2 * b`. -/
def Reduced (A b C : ℤ) : Prop :=
  0 < A ∧ 2 * |b| ≤ A ∧ A ≤ C ∧ ((2 * |b| = A ∨ A = C) → 0 ≤ b)

def Primitive (A b C : ℤ) : Prop :=
  Nat.gcd (A.gcd (2 * b)) C.natAbs = 1

private theorem double_odd_mod_four {N : ℤ} (hN : Odd N) : 2 * N % 4 = 2 := by
  obtain ⟨k, hk⟩ := hN
  omega

private theorem square_mod_four (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rw [pow_two, Int.mul_emod]
  rcases hx with h | h | h | h <;> simp [h]

/-- A form of discriminant `-8 * N` has neither non-diagonal reduction boundary. -/
theorem boundaries_impossible {N A b C : ℤ} (hN : Odd N)
    (hdisc : A * C - b ^ 2 = 2 * N) : 2 * |b| ≠ A ∧ A ≠ C := by
  have h4 : (A * C - b ^ 2) % 4 = 2 := hdisc ▸ double_odd_mod_four hN
  constructor
  · intro hboundary
    have hA2 : A % 2 = 0 := by omega
    have hAC2 : (A * C) % 2 = 0 := by simp [Int.mul_emod A C 2, hA2]
    have hb2 : b ^ 2 % 2 = 0 := by omega
    have hbeven : b % 2 = 0 := by
      have h : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases h with h | h
      · exact h
      · rw [pow_two, Int.mul_emod, h] at hb2
        contradiction
    have hA4 : A % 4 = 0 := by
      rcases le_or_gt 0 b with hb | hb
      · rw [abs_of_nonneg hb] at hboundary
        omega
      · rw [abs_of_neg hb] at hboundary
        omega
    have hAC4 : (A * C) % 4 = 0 := by simp [Int.mul_emod A C 4, hA4]
    have hb4 : b ^ 2 % 4 = 0 := by
      have h : b % 4 = 0 ∨ b % 4 = 2 := by omega
      rw [pow_two, Int.mul_emod]
      rcases h with h | h <;> simp [h]
    rw [Int.sub_emod, hAC4, hb4] at h4
    contradiction
  · intro hboundary
    subst C
    rw [← pow_two, Int.sub_emod] at h4
    rcases square_mod_four A with hA | hA <;>
      rcases square_mod_four b with hb | hb <;> simp [hA, hb] at h4

/-- The ambiguous boundary alternatives reduce to the diagonal in this discriminant. -/
theorem ambiguous_representative_diagonal {N A b C : ℤ} (hN : Odd N)
    (hdisc : A * C - b ^ 2 = 2 * N) (hamb : b = 0 ∨ 2 * |b| = A ∨ A = C) :
    b = 0 ∧ A * C = 2 * N := by
  have hb : b = 0 := by
    rcases hamb with hb | hb | hb
    · exact hb
    · exact False.elim ((boundaries_impossible hN hdisc).1 hb)
    · exact False.elim ((boundaries_impossible hN hdisc).2 hb)
  exact ⟨hb, by simpa [hb] using hdisc⟩

theorem diagonal_primitive_iff (A C : ℤ) : Primitive A 0 C ↔ A.gcd C = 1 := by
  simp [Primitive, Int.gcd_def]

/-- The primitive reduced representatives satisfying an ambiguous boundary condition
are exactly the ordered coprime factor pairs of `2 * N`. -/
theorem primitive_reduced_ambiguous_iff {N A b C : ℤ} (hN : Odd N) :
    (Reduced A b C ∧ A * C - b ^ 2 = 2 * N ∧ Primitive A b C ∧
      (b = 0 ∨ 2 * |b| = A ∨ A = C)) ↔
    (b = 0 ∧ 0 < A ∧ A ≤ C ∧ A * C = 2 * N ∧ A.gcd C = 1) := by
  constructor
  · rintro ⟨hred, hd, hprim, hamb⟩
    obtain ⟨rfl, hAC⟩ := ambiguous_representative_diagonal hN hd hamb
    exact ⟨rfl, hred.1, hred.2.2.1, hAC, (diagonal_primitive_iff A C).1 hprim⟩
  · rintro ⟨rfl, hA, hle, hAC, hcop⟩
    refine ⟨?_, by simpa using hAC, (diagonal_primitive_iff A C).2 hcop, Or.inl rfl⟩
    simpa [Reduced] using ⟨hA, hA.le, hle⟩

end Cogentic.RandomizedEvenDiscriminantGenus
