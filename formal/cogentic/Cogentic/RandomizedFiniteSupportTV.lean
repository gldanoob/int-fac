import Cogentic.RandomizedSamplerTransfer

open Finset
open scoped BigOperators

namespace Cogentic.RandomizedFiniteSupportTV

open RandomizedSamplerTransfer (totalVariation mean_difference_le_totalVariation)

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]

theorem uniform_mass_outside_eq (S : Finset Ω) :
    (∑ _z ∈ univ \ S, (1 : ℝ) / (Fintype.card Ω : ℝ)) =
      1 - (S.card : ℝ) / (Fintype.card Ω : ℝ) := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← sum_div, sum_const, nsmul_eq_mul, mul_one,
    card_sdiff_of_subset (subset_univ S), card_univ,
    Nat.cast_sub (by simpa using card_le_card (subset_univ S)), sub_div, div_self hn]

/-- A probability mass supported on `S` misses at least the uniform mass
outside `S` in total variation. -/
theorem uniform_mass_outside_le_totalVariation (S : Finset Ω) (p : Ω → ℝ)
    (hp : ∑ z, p z = 1) (hS : ∀ z ∉ S, p z = 0) :
    (∑ _z ∈ univ \ S, (1 : ℝ) / (Fintype.card Ω : ℝ)) ≤
      totalVariation p (fun _ => 1 / (Fintype.card Ω : ℝ)) := by
  let q : ℝ := 1 / (Fintype.card Ω : ℝ)
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq : (∑ _z : Ω, q) = 1 := by
    simp [q, nsmul_eq_mul, hn]
  let test (z : Ω) : ℝ := if z ∉ S then 1 else 0
  have htest₀ (z : Ω) : 0 ≤ test z := by unfold test; split <;> norm_num
  have htest₁ (z : Ω) : test z ≤ 1 := by unfold test; split <;> norm_num
  have h := mean_difference_le_totalVariation (hp.trans hq.symm) test htest₀ htest₁
  have hp₀ : ∑ z, p z * test z = 0 := by
    apply sum_eq_zero
    intro z _
    by_cases hz : z ∈ S
    · simp [test, hz]
    · simp [hS z hz]
  have hqsum : ∑ z, q * test z = ∑ _z ∈ univ \ S, q := by
    have hcomplement : univ \ S = univ.filter (fun z => z ∉ S) := by ext z; simp
    rw [hcomplement, sum_filter]
    simp only [test, mul_ite, mul_one, mul_zero]
  rw [hp₀, hqsum, zero_sub, abs_neg,
    abs_of_nonneg (sum_nonneg fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))] at h
  exact h

theorem uniform_mass_off_image_ge {A : Type*} (S : Finset A) (f : A → Ω) :
    1 - (S.card : ℝ) / (Fintype.card Ω : ℝ) ≤
      ∑ _z ∈ univ \ S.image f, (1 : ℝ) / (Fintype.card Ω : ℝ) := by
  rw [uniform_mass_outside_eq]
  apply sub_le_sub_left
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_image_le) (Nat.cast_nonneg _)

/-- Mass of the fiber of `f` at an output point. -/
def fiberMass {A : Type*} (S : Finset A) (f : A → Ω) (w : A → ℝ) (z : Ω) : ℝ :=
  ∑ x ∈ S.filter (fun x => f x = z), w x

/-- Every finite weighted image law has total variation from uniform at least
one minus the ratio of the number of input points to the number of outputs. -/
theorem one_sub_card_div_le_totalVariation_fiberMass {A : Type*}
    (S : Finset A) (f : A → Ω) (w : A → ℝ) (hw : ∑ x ∈ S, w x = 1) :
    1 - (S.card : ℝ) / (Fintype.card Ω : ℝ) ≤
      totalVariation (fiberMass S f w) (fun _ => 1 / (Fintype.card Ω : ℝ)) := by
  apply (uniform_mass_off_image_ge S f).trans
  apply uniform_mass_outside_le_totalVariation
  · unfold fiberMass
    rw [sum_fiberwise_of_maps_to (fun x _ => mem_univ (f x)), hw]
  · intro z hz
    unfold fiberMass
    apply sum_eq_zero
    intro x hx
    obtain ⟨hxS, hfx⟩ := mem_filter.mp hx
    exact (hz (mem_image.mpr ⟨x, hxS, hfx⟩)).elim

#print axioms uniform_mass_outside_eq
#print axioms uniform_mass_outside_le_totalVariation
#print axioms uniform_mass_off_image_ge
#print axioms one_sub_card_div_le_totalVariation_fiberMass

end Cogentic.RandomizedFiniteSupportTV
