import Cogentic.CharacterEstimate
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- Primes in the sharp interval `(A, B]`. -/
def primeBin (A B : ℕ) : Finset ℕ := (Ioc A B).filter Nat.Prime

private theorem primeBin_sum_eq {q A B : ℕ} (χ : DirichletCharacter ℂ q) (hAB : A ≤ B) :
    (∑ p ∈ primeBin A B, χ p) = Window.primeCount χ B - Window.primeCount χ A := by
  have hdisj : Disjoint (Icc 0 A) (Ioc A B) := Finset.disjoint_left.mpr (by
    intro p hp hq
    exact (not_lt_of_ge (mem_Icc.mp hp).2) (mem_Ioc.mp hq).1)
  have hunion : Icc 0 A ∪ Ioc A B = Icc 0 B := by
    ext p
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  unfold primeBin Window.primeCount
  simp only [Nat.floor_natCast, sum_filter]
  rw [← hunion, sum_union hdisj, add_sub_cancel_left]

/-- Uniform character bound for independent choices of primes from sharp bins. -/
def PrimeBinProductBound : Prop :=
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        ‖∑ p ∈ Fintype.piFinset (fun i ↦ primeBin (A i) (B i)),
            χ (∏ i, (p i : ZMod q))‖ ≤
          ∏ i, 2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i)

/-- The sharp-bin bound follows by subtraction at the two interval endpoints. -/
theorem primeBin_product_from_critical_line (line : DirichletLZerosOnLine) :
    PrimeBinProductBound := by
  obtain ⟨K, hK, bound⟩ := Window.nonprincipal_prime_count_from_critical_line line
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ ι _ _ A B hA hAB
  have hbin (i : ι) :
      ‖∑ p ∈ primeBin (A i) (B i), χ p‖ ≤
        2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i) := by
    have hAr : (2 : ℝ) ≤ A i := by exact_mod_cast hA i
    have hABr : (A i : ℝ) ≤ B i := by exact_mod_cast hAB i
    have hBr := hAr.trans hABr
    have ha := bound q χ hχ (B i) (A i) hAr hABr
    have hb := bound q χ hχ (B i) (B i) hBr le_rfl
    rw [← Real.sqrt_eq_rpow] at ha hb
    have hscale : 0 ≤ K * (1 + Real.log (3 * q * B i))^2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hABr) hscale
    rw [primeBin_sum_eq χ (hAB i)]
    calc
      _ ≤ ‖Window.primeCount χ (B i)‖ + ‖Window.primeCount χ (A i)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hb ha
      _ ≤ _ := add_le_add le_rfl hscaled
      _ = _ := by ring
  simp_rw [map_prod]
  rw [← Finset.prod_univ_sum (fun i : ι ↦ primeBin (A i) (B i))
    (fun _ (p : ℕ) ↦ χ p)]
  calc
    _ = ∏ i, ‖∑ p ∈ primeBin (A i) (B i), χ p‖ := norm_prod _ _
    _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hbin i)

/-- The corresponding normalized bound uses the actual cardinalities of the bins. -/
theorem primeBin_average_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ),
        (∀ i, 2 ≤ A i) → (∀ i, A i ≤ B i) →
        ‖∑ p ∈ Fintype.piFinset (fun i ↦ primeBin (A i) (B i)),
            χ (∏ i, (p i : ZMod q))‖ /
            (Fintype.piFinset (fun i ↦ primeBin (A i) (B i))).card ≤
          ∏ i, (2 * K * (1 + Real.log (3 * q * B i))^2 * Real.sqrt (B i)) /
            (primeBin (A i) (B i)).card := by
  obtain ⟨K, hK, bound⟩ := primeBin_product_from_critical_line line
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ ι _ _ A B hA hAB
  rw [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_div_distrib]
  exact div_le_div_of_nonneg_right (bound q χ hχ A B hA hAB) (by positivity)

end Cogentic.Randomized
