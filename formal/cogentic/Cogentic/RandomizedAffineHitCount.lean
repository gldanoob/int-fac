import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

namespace Cogentic.RandomizedAffineHitCount

open scoped BigOperators

theorem interval_hit {m l u N : ℤ} (hN : 0 < N) (hlu : l ≤ u) (hlen : u - l ≤ N) :
    (m - l) / N - (m - u) / N = if (m - l) % N < u - l then (1 : ℤ) else 0 := by
  have hrem₀ := Int.emod_nonneg (m - l) (Int.ne_of_gt hN)
  have hrem₁ := Int.emod_lt_of_pos (m - l) hN
  have hdiv := Int.mul_ediv_add_emod (m - l) N
  split
  · rename_i hh
    have hq : (m - u) / N = (m - l) / N - 1 := by
      apply (Int.ediv_eq_iff_of_pos hN).2
      rw [sub_mul, one_mul, mul_comm ((m - l) / N) N]
      omega
    omega
  · rename_i hh
    have hq : (m - u) / N = (m - l) / N := by
      apply (Int.ediv_eq_iff_of_pos hN).2
      rw [mul_comm ((m - l) / N) N]
      omega
    omega

theorem circular_hit_iff {m l u N : ℤ} (hN : 0 < N) (hlen : u - l ≤ N) :
    (m - l) % N < u - l ↔ ∃ y : ℤ, l ≤ y ∧ y < u ∧ m ≡ y [ZMOD N] := by
  constructor
  · intro hh
    refine ⟨l + (m - l) % N, ?_, by omega, ?_⟩
    · have := Int.emod_nonneg (m - l) (Int.ne_of_gt hN)
      omega
    · apply Int.modEq_iff_dvd.2
      refine ⟨-((m - l) / N), ?_⟩
      have := Int.mul_ediv_add_emod (m - l) N
      rw [Int.mul_neg]
      omega
  · rintro ⟨y, hly, hyu, hmy⟩
    have hsub : (m - l) % N = (y - l) % N := hmy.sub (Int.ModEq.refl l)
    rw [hsub, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- The number of candidate offsets is the difference of two affine floor sums. -/
def linear_hit_count (N b X B : ℤ) (n : ℕ) : ℤ :=
  ∑ r ∈ Finset.range n,
    ((b ^ 2 + 2 * b * (r : ℤ) + B ^ 2) / N -
      (b ^ 2 + 2 * b * (r : ℤ) - (X + 1)) / N)

theorem linear_hit_count_eq_card {N b X B : ℤ} (hN : 0 < N) (hX : 0 ≤ X)
    (hlen : X + B ^ 2 + 1 ≤ N) (n : ℕ) :
    linear_hit_count N b X B n =
      ((Finset.range n).filter fun (r : ℕ) =>
        (b ^ 2 + 2 * b * (r : ℤ) + B ^ 2) % N < X + B ^ 2 + 1).card := by
  classical
  unfold linear_hit_count
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  have h := interval_hit (m := b ^ 2 + 2 * b * (r : ℤ)) (l := -(B ^ 2))
    (u := X + 1) hN (by nlinarith [sq_nonneg B]) (by omega)
  simpa [sub_neg_eq_add, add_assoc, add_left_comm, add_comm] using h

theorem linear_hit_count_increment {N b X B : ℤ} (hN : 0 < N) (hX : 0 ≤ X)
    (hlen : X + B ^ 2 + 1 ≤ N) (n : ℕ) :
    linear_hit_count N b X B n ≤ linear_hit_count N b X B (n + 1) ∧
      linear_hit_count N b X B (n + 1) ≤ linear_hit_count N b X B n + 1 := by
  unfold linear_hit_count
  rw [Finset.sum_range_succ]
  have h := interval_hit (m := b ^ 2 + 2 * b * (n : ℤ)) (l := -(B ^ 2))
    (u := X + 1) hN (by nlinarith [sq_nonneg B]) (by omega)
  rw [sub_neg_eq_add] at h
  rw [h]
  split <;> omega

theorem linear_hit_count_monotone {N b X B : ℤ} (hN : 0 < N) (hX : 0 ≤ X)
    (hlen : X + B ^ 2 + 1 ≤ N) : Monotone (linear_hit_count N b X B) :=
  monotone_nat_of_le_succ fun n => (linear_hit_count_increment hN hX hlen n).1

end Cogentic.RandomizedAffineHitCount
