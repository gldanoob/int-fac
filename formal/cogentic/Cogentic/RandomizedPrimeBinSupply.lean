import Cogentic.PrincipalBand
import Cogentic.RandomizedPrimeBinBias

namespace Cogentic.Randomized

open scoped BigOperators

/-- Lower prime supply for integer bins `(A,B]` with a uniform square-root
error at the upper endpoint. -/
def PrimeBinSupplyBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ A B : ℕ, 2 ≤ A → A ≤ B →
    (B : ℝ) - (A : ℝ) - K * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt B ≤
      ((primeBin A B).card : ℝ) * Real.log B

private theorem sum_log_primeBin_eq {A B : ℕ} (hAB : A ≤ B) :
    (∑ p ∈ primeBin A B, Real.log p) = Chebyshev.theta B - Chebyshev.theta A := by
  have hbin : primeBin A B = Nat.primesLE B \ Nat.primesLE A := by
    ext p
    simp only [primeBin, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hA, hB⟩, hp⟩
      exact ⟨⟨hB, hp⟩, fun h => (not_le_of_gt hA) h.1⟩
    · rintro ⟨⟨hB, hp⟩, hA⟩
      exact ⟨⟨lt_of_not_ge (fun h => hA ⟨h, hp⟩), hB⟩, hp⟩
  rw [hbin, Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  exact eq_sub_of_add_eq (Finset.sum_sdiff (Nat.primesLE_mono hAB))

theorem primeBin_supply_from_critical_line (line : DirichletLZerosOnLine) :
    PrimeBinSupplyBound := by
  obtain ⟨c, hc, hθ⟩ := Window.principal_theta_from_critical_line line
  refine ⟨2 * c, by linarith, ?_⟩
  intro A B hA hAB
  have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  let err : ℝ := c * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt B
  have hAerr : |Chebyshev.theta A - (A : ℝ)| ≤ err :=
    (hθ B A hAr hABr).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hABr)
      (mul_nonneg hc (sq_nonneg _)))
  have hBerr : |Chebyshev.theta B - (B : ℝ)| ≤ err := hθ B B (hAr.trans hABr) le_rfl
  have hθbin : (B : ℝ) - (A : ℝ) - 2 * err ≤ Chebyshev.theta B - Chebyshev.theta A := by
    linarith only [(abs_le.mp hAerr).2, (abs_le.mp hBerr).1]
  have hlog : (∑ p ∈ primeBin A B, Real.log p) ≤ ((primeBin A B).card : ℝ) * Real.log B := calc
    _ ≤ ∑ _p ∈ primeBin A B, Real.log B := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpB, hpPrime⟩ := Finset.mem_filter.mp hp
      exact Real.log_le_log (Nat.cast_pos.mpr hpPrime.pos)
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpB).2)
    _ = _ := by simp [nsmul_eq_mul]
  rw [sum_log_primeBin_eq hAB] at hlog
  simpa only [err, mul_assoc] using hθbin.trans hlog

#print axioms primeBin_supply_from_critical_line

end Cogentic.Randomized
