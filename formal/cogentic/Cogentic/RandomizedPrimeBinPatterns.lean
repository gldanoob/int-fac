import Cogentic.RandomizedPrimeBinBias
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- A sum-of-indices fiber containing at least the rounded-down average number of patterns. -/
theorem exists_large_primeBin_pattern_fiber (J k : ℕ) :
    ∃ a ∈ range (k * (J - 1) + 1),
      J.choose k / (k * (J - 1) + 1) ≤
        (((range J).powersetCard k).filter fun s ↦ (∑ i ∈ s, i) = a).card := by
  let slots := range (k * (J - 1) + 1)
  refine Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to (t := slots) ?_ ?_ ?_
  · intro s hs
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
    have hbound : (∑ i ∈ s, i) ≤ k * (J - 1) := by
      calc
        _ ≤ ∑ _ ∈ s, (J - 1) := sum_le_sum (fun i hi ↦ by
          have := mem_range.mp (hsub hi)
          omega)
        _ = _ := by simp [hcard]
    exact mem_range.mpr (by omega)
  · exact ⟨0, mem_range.mpr (Nat.zero_lt_succ _)⟩
  · simpa [slots, Nat.mul_comm] using
      Nat.div_mul_le_self (J.choose k) (k * (J - 1) + 1)

/-- Form the integer products belonging to a pool of occupied-bin patterns. -/
def primeBinPatternProducts {ι : Type} [DecidableEq ι] (A B : ι → ℕ)
    (patterns : Finset (Finset ι)) : Finset ℕ :=
  patterns.biUnion fun s ↦ primeBinProducts (fun i : s ↦ A i) (fun i : s ↦ B i)

theorem primeBinPatternProducts_card {ι : Type} [DecidableEq ι] (A B : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (patterns : Finset (Finset ι)) :
    (primeBinPatternProducts A B patterns).card =
      ∑ s ∈ patterns, (primeBinProducts (fun i : s ↦ A i) (fun i : s ↦ B i)).card := by
  unfold primeBinPatternProducts
  apply Finset.card_biUnion
  exact fun _ _ _ _ hne ↦ primeBinProducts_disjoint_patterns A B hdisj hne

theorem primeBinPatternProducts_card_lower {ι : Type} [DecidableEq ι] (A B : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (patterns : Finset (Finset ι)) (k m : ℕ)
    (hsize : ∀ s ∈ patterns, s.card = k)
    (hpop : ∀ s ∈ patterns, ∀ i ∈ s, m ≤ (primeBin (A i) (B i)).card) :
    patterns.card * m^k ≤ (primeBinPatternProducts A B patterns).card := by
  rw [primeBinPatternProducts_card A B hdisj]
  calc
    _ = ∑ _ ∈ patterns, m^k := by simp
    _ ≤ _ := sum_le_sum fun s hs ↦ by
      rw [primeBinProducts_card _ _ (fun i j hij ↦ hdisj (Subtype.val_injective.ne hij))]
      calc
        m^k = ∏ _ : s, m := by simp [hsize s hs]
        _ ≤ _ := Finset.prod_le_prod' fun i _ ↦ hpop s hs i i.property

end Cogentic.Randomized
