import Cogentic.RandomizedSamplerTransfer
import Mathlib.Tactic.FieldSimp

namespace Cogentic.RandomizedSamplerTransfer

open Finset
open scoped BigOperators

variable {Z : Type*} [Fintype Z]

/-- A pointwise common lower bound on two normalized laws bounds their total variation. -/
theorem totalVariation_le_of_common_mass (p q r : Z → ℝ)
    (hp : ∑ z, p z = 1) (hq : ∑ z, q z = 1)
    (hrp : ∀ z, r z ≤ p z) (hrq : ∀ z, r z ≤ q z) :
    totalVariation p q ≤ 1 - ∑ z, r z := by
  have hpoint (z : Z) : |p z-q z| ≤ (p z-r z)+(q z-r z) :=
    abs_le.mpr ⟨by linarith only [hrp z], by linarith only [hrq z]⟩
  have h := sum_le_sum (s := univ) fun z _ ↦ hpoint z
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, hp, hq] at h
  unfold totalVariation
  linarith only [h]

/-- For weights bounded by `B`, normalizing them changes the uniform law
by at most the relative mass missing from the constant weight `B`. -/
theorem normalized_weights_totalVariation_le_missing_mass (w : Z → ℝ) (B : ℝ)
    (hB : 0 < B) (hw₀ : ∀ z, 0 ≤ w z) (hwB : ∀ z, w z ≤ B) (hS : 0 < ∑ z, w z) :
    totalVariation (fun z ↦ w z/(∑ y, w y)) (fun _ ↦ 1/(Fintype.card Z : ℝ)) ≤
      1-(∑ z, w z)/(B*(Fintype.card Z : ℝ)) := by
  let S := ∑ z, w z
  let n : ℝ := Fintype.card Z
  have hcap : S ≤ B*n := by
    calc
      _ ≤ ∑ _z : Z, B := sum_le_sum (fun z _ ↦ hwB z)
      _ = _ := by simp [n, nsmul_eq_mul, mul_comm]
  have hBn : 0 < B*n := hS.trans_le hcap
  have hn : 0 < n := pos_of_mul_pos_right hBn hB.le
  let r (z : Z) := w z/(B*n)
  have hp : (∑ z, w z/S) = 1 := by rw [← sum_div, div_self hS.ne']
  have hq : (∑ _z : Z, 1/n) = 1 := by rw [← sum_div]; simp [n, hn.ne']
  have hrp (z : Z) : r z ≤ w z/S := div_le_div_of_nonneg_left (hw₀ z) hS hcap
  have hrq (z : Z) : r z ≤ 1/n := by
    have he : 1/n = B/(B*n) := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (hwB z) hBn.le
  have h := totalVariation_le_of_common_mass (fun z ↦ w z/S) (fun _ ↦ 1/n) r hp hq hrp hrq
  simpa only [r, ← sum_div] using h

private theorem weight_deficit_le (w : Z → ℝ) (B : ℝ) (E : Finset Z)
    (hw₀ : ∀ z, 0 ≤ w z) (hconst : ∀ z ∉ E, w z = B) :
    (∑ z, (B-w z)) ≤ B*(E.card : ℝ) := by
  calc
    _ = ∑ z ∈ E, (B-w z) := (sum_subset (subset_univ E) fun z _ hz ↦ by rw [hconst z hz, sub_self]).symm
    _ ≤ ∑ _z ∈ E, B := sum_le_sum (fun z _ ↦ sub_le_self _ (hw₀ z))
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

/-- If all weight deficits are confined to `E`, the total variation after
normalization is at most the uniform fraction of exceptional points. -/
theorem deficient_weights_totalVariation_le (w : Z → ℝ) (B : ℝ) (E : Finset Z)
    (hB : 0 < B) (hw₀ : ∀ z, 0 ≤ w z) (hwB : ∀ z, w z ≤ B)
    (hconst : ∀ z ∉ E, w z = B) (hS : 0 < ∑ z, w z) :
    totalVariation (fun z ↦ w z/(∑ y, w y)) (fun _ ↦ 1/(Fintype.card Z : ℝ)) ≤
      (E.card : ℝ)/(Fintype.card Z : ℝ) := by
  have hcap : (∑ z, w z) ≤ B*(Fintype.card Z : ℝ) := by
    have h := sum_le_sum (s := univ) (fun z _ ↦ hwB z)
    simpa [nsmul_eq_mul, mul_comm] using h
  have hBn : 0 < B*(Fintype.card Z : ℝ) := hS.trans_le hcap
  have hn := pos_of_mul_pos_right hBn hB.le
  calc
    _ ≤ 1-(∑ z, w z)/(B*(Fintype.card Z : ℝ)) :=
      normalized_weights_totalVariation_le_missing_mass w B hB hw₀ hwB hS
    _ = (∑ z, (B-w z))/(B*(Fintype.card Z : ℝ)) := by
      rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
      field_simp
    _ ≤ (B*(E.card : ℝ))/(B*(Fintype.card Z : ℝ)) :=
      div_le_div_of_nonneg_right (weight_deficit_le w B E hw₀ hconst) hBn.le
    _ = _ := by field_simp

/-- A proper exceptional set guarantees that the weights have positive total mass. -/
theorem deficient_weights_totalVariation_le_of_card_lt (w : Z → ℝ) (B : ℝ) (E : Finset Z)
    (hB : 0 < B) (hw₀ : ∀ z, 0 ≤ w z) (hwB : ∀ z, w z ≤ B)
    (hconst : ∀ z ∉ E, w z = B) (hE : E.card < Fintype.card Z) :
    totalVariation (fun z ↦ w z/(∑ y, w y)) (fun _ ↦ 1/(Fintype.card Z : ℝ)) ≤
      (E.card : ℝ)/(Fintype.card Z : ℝ) := by
  apply deficient_weights_totalVariation_le w B E hB hw₀ hwB hconst
  have h := weight_deficit_le w B E hw₀ hconst
  rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at h
  have hcard : (E.card : ℝ) < Fintype.card Z := by exact_mod_cast hE
  have hpos := mul_pos hB (sub_pos.mpr hcard)
  nlinarith only [h, hpos]

end Cogentic.RandomizedSamplerTransfer
