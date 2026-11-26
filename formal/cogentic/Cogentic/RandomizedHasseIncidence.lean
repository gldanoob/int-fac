import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Order.Lemmas

namespace Cogentic.RandomizedHasseIncidence

open Finset
open scoped BigOperators

/-- Every rich centre contributes at least `k` incidences, while each witness
contributes at most `m` incidences. -/
theorem rich_centres_mul_le {α β : Type*} (C : Finset α) (W : Finset β)
    (R : α → β → Prop) [DecidableRel R] (k m : ℕ)
    (hm : ∀ w ∈ W, (C.filter fun c ↦ R c w).card ≤ m) :
    (C.filter fun c ↦ k ≤ (W.filter (R c)).card).card * k ≤ m * W.card := by
  let rich := C.filter fun c ↦ k ≤ (W.filter (R c)).card
  calc
    rich.card * k = ∑ _c ∈ rich, k := by simp
    _ ≤ ∑ c ∈ rich, (W.filter (R c)).card := by
      exact sum_le_sum fun c hc ↦ (mem_filter.mp hc).2
    _ ≤ ∑ c ∈ C, (W.filter (R c)).card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ Nat.zero_le _
    _ = ∑ w ∈ W, (C.filter fun c ↦ R c w).card := by
      simp only [card_eq_sum_ones, sum_filter]
      exact sum_comm
    _ ≤ ∑ _w ∈ W, m := sum_le_sum hm
    _ = m * W.card := by simp [Nat.mul_comm]

/-- A witness in an integer Hasse window of radius at most `r` can meet at most
`2 * r + 1` centres, even if the actual radius depends on the centre. -/
theorem rich_integer_centres_mul_le (C W : Finset ℤ) (R : ℤ → ℤ → Prop) [DecidableRel R]
    (r k : ℕ) (hnear : ∀ c ∈ C, ∀ w ∈ W, R c w → |w - c| ≤ (r : ℤ)) :
    (C.filter fun c ↦ k ≤ (W.filter (R c)).card).card * k ≤ (2 * r + 1) * W.card := by
  apply rich_centres_mul_le C W R k (2 * r + 1)
  intro w hw
  calc
    (C.filter fun c ↦ R c w).card ≤ (Icc (w - r) (w + r)).card := by
      apply card_le_card
      intro c hc
      obtain ⟨hc, hcw⟩ := mem_filter.mp hc
      have ⟨hlo, hhi⟩ := abs_le.mp (hnear c hc w hw hcw)
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    _ = 2 * r + 1 := by
      rw [Int.card_Icc]
      omega

/-- For `c = p + 1` with `p ≤ 2 * P`, the Hasse incidence `(w - c)^2 ≤ 4 * p`
has a common integer radius of `sqrt (8 * P)`. -/
theorem rich_hasse_centres_mul_le (C W : Finset ℤ) (P k : ℕ)
    (hC : ∀ c ∈ C, c ≤ 2 * (P : ℤ) + 1) :
    (C.filter fun c ↦ k ≤ (W.filter fun w ↦ (w - c)^2 ≤ 4 * (c - 1)).card).card * k ≤
      (2 * Nat.sqrt (8 * P) + 1) * W.card := by
  apply rich_integer_centres_mul_le C W (fun c w ↦ (w - c)^2 ≤ 4 * (c - 1))
  intro c hc w _ hcw
  rw [← Int.sqrt_natCast]
  apply (Int.abs_le_sqrt_iff_sq_le (Int.natCast_nonneg _)).mpr
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hcp := hC c hc
  omega

end Cogentic.RandomizedHasseIncidence

#print axioms Cogentic.RandomizedHasseIncidence.rich_centres_mul_le
#print axioms Cogentic.RandomizedHasseIncidence.rich_integer_centres_mul_le
#print axioms Cogentic.RandomizedHasseIncidence.rich_hasse_centres_mul_le
