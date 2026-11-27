import Cogentic.RandomizedPrimeBinPatterns
import Cogentic.RandomizedPrimeBinProgression

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- The progression estimate for the union of any family of occupied-bin patterns. -/
def PrimePatternProgressionBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
    {ι : Type} [DecidableEq ι] (A B : ι → ℕ) (patterns : Finset (Finset ι)),
    Pairwise (fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
    (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
    let S := primeBinPatternProducts A B patterns
    |((S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))).card : ℝ) -
      ((S.filter (fun n ↦ n.Coprime q)).card : ℝ) / q.totient| ≤
        ∑ s ∈ patterns, ∏ i ∈ s, 2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i)

theorem primePattern_progression_of_bin_progression (h : PrimeBinProgressionBound) :
    PrimePatternProgressionBound := by
  classical
  obtain ⟨K, hK, bound⟩ := h
  refine ⟨K, hK, ?_⟩
  intro q _ r ι _ A B patterns hdisj hA hAB
  let bins (s : Finset ι) := primeBinProducts (fun i : s ↦ A i) (fun i : s ↦ B i)
  have hcard (p : ℕ → Prop) [DecidablePred p] :
      (((primeBinPatternProducts A B patterns).filter p).card : ℝ) =
        ∑ s ∈ patterns, (((bins s).filter p).card : ℝ) := by
    rw [primeBinPatternProducts, Finset.filter_biUnion, Finset.card_biUnion, Nat.cast_sum]
    intro s _ t _ hst
    exact (primeBinProducts_disjoint_patterns A B hdisj hst).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  dsimp only
  rw [hcard, hcard, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s _
  rw [← Finset.prod_coe_sort s (fun i ↦
    2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i))]
  exact bound q r (fun i : s ↦ A i) (fun i : s ↦ B i)
      (fun _ _ hij ↦ hdisj (Subtype.val_injective.ne hij))
      (fun i ↦ hA i) (fun i ↦ hAB i)

end Cogentic.Randomized

#print axioms Cogentic.Randomized.primePattern_progression_of_bin_progression
