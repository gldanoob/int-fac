import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Cogentic.RandomizedMarginalModes

open Finset

/-- An injection into a frequency grid cannot increase its squared energy. -/
private theorem restricted_energy {S A : Type*} [Fintype S] [Fintype A]
    (i : S ↪ A) (f : A → ℝ) : ∑ s, f (i s) ^ 2 ≤ ∑ a, f a ^ 2 := by
  classical
  calc
    _ = ∑ a ∈ (univ : Finset S).image i, f a ^ 2 := (sum_image i.injective.injOn).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg fun a ↦ sq_nonneg (f a)

/-- The same phase can govern both grids. Only separate marginal energy
bounds are required, since the two squared arrays can be summed separately. -/
theorem coupled_mode_sum {Ω S A B : Type*} [Fintype S] [Fintype A] [Fintype B]
    (phases : Finset Ω) (w : Ω → ℝ) (hw : ∀ o ∈ phases, 0 ≤ w o)
    (i : S ↪ A) (j : S ↪ B) (f : Ω → A → ℝ) (g : Ω → B → ℝ) :
    2 * (∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s)) ≤
      (∑ o ∈ phases, w o * ∑ a, f o a ^ 2) + ∑ o ∈ phases, w o * ∑ b, g o b ^ 2 := by
  classical
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro o ho
  have hpair : 2 * (∑ s, f o (i s) * g o (j s)) ≤
      (∑ s, f o (i s) ^ 2) + ∑ s, g o (j s) ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun s _ ↦ by nlinarith only [sq_nonneg (f o (i s) - g o (j s))]
  have h := hpair.trans (add_le_add (restricted_energy i (f o)) (restricted_energy j (g o)))
  have hm := mul_le_mul_of_nonneg_left h (hw o ho)
  linarith only [hm]

end Cogentic.RandomizedMarginalModes
