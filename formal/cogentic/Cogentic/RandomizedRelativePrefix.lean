import Cogentic.RandomizedProductPerron
import Cogentic.RandomizedPrimeBinSupply
import Cogentic.RandomizedPrimeBinPatterns

namespace Cogentic.Randomized

open scoped BigOperators

/-- Multiplying the per-bin square-root savings produces a saving in the
product size, with respect to the number of distinct integer products. -/
private theorem product_saving {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (H : ι → ℝ) {X U : ℝ} (hX : 0 < X)
    (hH : ∀ i, 0 ≤ H i) (hsize : X ≤ ∏ i, (B i : ℝ))
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hbin : ∀ i, H i * Real.sqrt (B i) ≤ U * (primeBin (A i) (B i)).card) :
    (∏ i, H i) ≤ (U ^ Fintype.card ι / Real.sqrt X) * (primeBinProducts A B).card := by
  have h := Finset.prod_le_prod (s := Finset.univ)
    (fun i _ => mul_nonneg (hH i) (Real.sqrt_nonneg _)) (fun i _ => hbin i)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.sqrt_prod _ (fun _ _ => Nat.cast_nonneg _)] at h
  rw [primeBinProducts_card A B hdisj, Nat.cast_prod, div_mul_eq_mul_div, le_div_iff₀ (Real.sqrt_pos.mpr hX)]
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsize)
    (Finset.prod_nonneg (fun i _ => hH i))).trans h

/-- A sharp prefix of one prime product pattern saves the square root of the
product scale. The loss per slot is explicit even when the number of slots varies. -/
theorem primeBin_relative_prefix_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C K E : ℝ, 0 < C ∧ 0 < K ∧ 0 ≤ E ∧
    ∀ (X : ℝ) (m q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ) (U : ℝ),
      2 ≤ X → Real.exp 1 ≤ X →
      X ≤ (m : ℝ) + 1/2 → (m : ℝ) + 1/2 ≤ 2*X →
      (∀ n ∈ primeBinProducts A B, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*X) →
      (Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      (∀ i, 2 ≤ A i) → (∀ i, A i < B i) →
      (∀ i, 2 * E * (1 + Real.log (3 * (B i : ℝ)))^2 * Real.sqrt (B i) ≤
        (B i : ℝ) - A i) →
      X ≤ ∏ i, (B i : ℝ) → 0 ≤ U →
      (∀ i, 2*C*(B i : ℝ)*(1+Real.log (q*((B i : ℝ)+X^3+2)))^3 * Real.log (B i) ≤
        U * ((B i : ℝ) - A i)) →
      ‖∑ n ∈ (primeBinProducts A B).filter (· ≤ m), χ n‖ ≤
        ((4*Real.exp 2/Real.pi)*Real.log X*(U^Fintype.card ι/Real.sqrt X) + K/X^2) *
          (primeBinProducts A B).card := by
  obtain ⟨C, K, hC, hK, prefixBound⟩ := primeBin_product_prefix_from_critical_line line
  obtain ⟨E, hE, supply⟩ := primeBin_supply_from_critical_line line
  refine ⟨C,K,E,hC,hK,hE,?_⟩
  intro X m q _ χ hχ ι _ _ A B U hX heX hcut hcut' hP hdisj hA hAB hwidth hsize hU hslot
  let H i := C * Real.sqrt (B i) * (1+Real.log (q*((B i : ℝ)+X^3+2)))^3
  have hH i : 0 ≤ H i := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
    have harg : 1 ≤ (q : ℝ) * ((B i : ℝ)+X^3+2) :=
      one_le_mul_of_one_le_of_one_le hq (by linarith [Nat.cast_nonneg (α := ℝ) (B i), show 0 ≤ X^3 by positivity])
    dsimp [H]
    have := Real.log_nonneg harg
    positivity
  have hbin i : H i * Real.sqrt (B i) ≤ U * (primeBin (A i) (B i)).card := by
    have hBi : 1 < B i := by have := hA i; have := hAB i; omega
    have hlo : 0 < Real.log (B i) := Real.log_pos (by exact_mod_cast hBi)
    have count := supply (A i) (B i) (hA i) (hAB i).le
    have hmass : (B i : ℝ) - A i ≤ 2 * ((primeBin (A i) (B i)).card * Real.log (B i)) := by
      linarith only [count, hwidth i]
    have h := (hslot i).trans (mul_le_mul_of_nonneg_left hmass hU)
    have hcancel : C * (B i : ℝ) * (1+Real.log (q*((B i : ℝ)+X^3+2)))^3 ≤
        U * (primeBin (A i) (B i)).card := by
      apply (le_of_mul_le_mul_right ?_ hlo)
      linarith only [h]
    calc
      _ = C * (Real.sqrt (B i))^2 * (1+Real.log (q*((B i : ℝ)+X^3+2)))^3 := by dsimp [H]; ring
      _ ≤ _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]; exact hcancel
  have hprod := product_saving A B H (by linarith : 0 < X) hH hsize hdisj hbin
  have hp := prefixBound X m q χ hχ A B hX heX hcut hcut' hP hdisj (fun i => (hA i).trans (hAB i).le)
    (fun i => (hAB i).le)
  have hl : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  calc
    _ ≤ (4*Real.exp 2/Real.pi)*((∏ i, H i)*Real.log X) + K/X^2*(primeBinProducts A B).card := hp
    _ ≤ (4*Real.exp 2/Real.pi)*(((U^Fintype.card ι/Real.sqrt X)*(primeBinProducts A B).card)*Real.log X) +
          K/X^2*(primeBinProducts A B).card := by gcongr
    _ = _ := by ring

/-- A relative prefix error survives a disjoint union of patterns with the
same coefficient. Its normalization is the total population of the union. -/
theorem primePattern_relative_prefix {ι : Type} [DecidableEq ι] (A B : ι → ℕ)
    (patterns : Finset (Finset ι)) (m : ℕ) (f : ℕ → ℂ) (R : ℝ)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hprefix : ∀ s ∈ patterns,
      let P := primeBinProducts (fun i : s => A i) (fun i : s => B i)
      ‖∑ n ∈ P.filter (· ≤ m), f n‖ ≤ R * P.card) :
    let S := primeBinPatternProducts A B patterns
    ‖∑ n ∈ S.filter (· ≤ m), f n‖ ≤ R * S.card := by
  classical
  let P (s : Finset ι) := primeBinProducts (fun i : s => A i) (fun i : s => B i)
  have hd : (patterns : Set (Finset ι)).PairwiseDisjoint (fun s => (P s).filter (· ≤ m)) := by
    intro s _ t _ hst
    exact (primeBinProducts_disjoint_patterns A B hdisj hst).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  dsimp only
  rw [primeBinPatternProducts_card A B hdisj, Nat.cast_sum, Finset.mul_sum]
  unfold primeBinPatternProducts
  rw [Finset.filter_biUnion, Finset.sum_biUnion hd]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hprefix)

#print axioms primePattern_relative_prefix
#print axioms primeBin_relative_prefix_from_critical_line

end Cogentic.Randomized
