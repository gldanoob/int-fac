import Cogentic.RandomizedPrimeBinSupply

namespace Cogentic.Randomized

open scoped BigOperators

/-- Divide any product error by the actual size of the disjoint-bin product set.
A per-bin supply of half the interval width suffices for the normalization. -/
theorem primeBinProducts_div_le_of_half_width {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i < B i)
    (hsupply : ∀ i, ((B i : ℝ) - (A i : ℝ)) / 2 ≤
      ((primeBin (A i) (B i)).card : ℝ) * Real.log (B i))
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) {error : ℝ} (herr : error ≤ ∏ i, E i) :
    0 < (primeBinProducts A B).card ∧
      error / ((primeBinProducts A B).card : ℝ) ≤
        ∏ i, 2 * E i * Real.log (B i) / ((B i : ℝ) - (A i : ℝ)) := by
  have hwidth (i : ι) : 0 < (B i : ℝ) - (A i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hAB i)
  have hlog (i : ι) : 0 < Real.log (B i) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < B i by have := hA i; have := hAB i; omega)
  have hcard (i : ι) : 0 < ((primeBin (A i) (B i)).card : ℝ) := by
    have hprod := (half_pos (hwidth i)).trans_le (hsupply i)
    exact pos_of_mul_pos_left hprod (hlog i).le
  rw [primeBinProducts_card A B hdisj]
  refine ⟨Finset.prod_pos (fun i _ => Nat.cast_pos.mp (hcard i)), ?_⟩
  rw [Nat.cast_prod]
  calc
    _ ≤ (∏ i, E i) / ∏ i, ((primeBin (A i) (B i)).card : ℝ) :=
      div_le_div_of_nonneg_right herr (Finset.prod_nonneg fun i _ => (hcard i).le)
    _ = ∏ i, E i / ((primeBin (A i) (B i)).card : ℝ) := by rw [Finset.prod_div_distrib]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · exact fun i _ => div_nonneg (hE i) (hcard i).le
      intro i _
      apply (div_le_div_iff₀ (hcard i) (hwidth i)).2
      calc
        _ ≤ E i * (2 * (((primeBin (A i) (B i)).card : ℝ) * Real.log (B i))) :=
          mul_le_mul_of_nonneg_left (by linarith only [hsupply i]) (hE i)
        _ = _ := by ring

/-- On bins whose widths dominate twice the principal error, the normalized
nonprincipal character sum over the distinct integer products has a product bound. -/
theorem primeBinProducts_relative_error_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        Pairwise (fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (∀ i, 2 ≤ A i) → (∀ i, A i < B i) →
        (∀ i, 2 * C * (1 + Real.log (3 * (B i : ℝ))) ^ 2 * Real.sqrt (B i) ≤
          (B i : ℝ) - (A i : ℝ)) →
        0 < (primeBinProducts A B).card ∧
          ‖∑ m ∈ primeBinProducts A B, χ m‖ / ((primeBinProducts A B).card : ℝ) ≤
            ∏ i, 4 * K * (1 + Real.log (3 * q * B i)) ^ 2 * Real.sqrt (B i) *
              Real.log (B i) / ((B i : ℝ) - (A i : ℝ)) := by
  obtain ⟨C, hC, supply⟩ := primeBin_supply_from_critical_line line
  obtain ⟨K, hK, bias⟩ := primeBin_product_from_critical_line line
  refine ⟨C, K, hC, hK, ?_⟩
  intro q _ χ hχ ι _ _ A B hdisj hA hAB hwidth
  let E (i : ι) := 2 * K * (1 + Real.log (3 * q * B i)) ^ 2 * Real.sqrt (B i)
  have hsupply (i : ι) : ((B i : ℝ) - (A i : ℝ)) / 2 ≤
      ((primeBin (A i) (B i)).card : ℝ) * Real.log (B i) := by
    linarith only [supply (A i) (B i) (hA i) (hAB i).le, hwidth i]
  have herr : ‖∑ m ∈ primeBinProducts A B, χ m‖ ≤ ∏ i, E i := by
    rw [primeBinProducts_character_sum χ A B hdisj]
    exact bias q χ hχ A B hA (fun i => (hAB i).le)
  obtain ⟨hpos, hrel⟩ := primeBinProducts_div_le_of_half_width A B hdisj hA hAB hsupply
    E (fun i => by dsimp [E]; positivity) herr
  refine ⟨hpos, hrel.trans_eq ?_⟩
  apply Finset.prod_congr rfl
  intro i _
  dsimp [E]
  ring

#print axioms primeBinProducts_div_le_of_half_width
#print axioms primeBinProducts_relative_error_from_critical_line

end Cogentic.Randomized
