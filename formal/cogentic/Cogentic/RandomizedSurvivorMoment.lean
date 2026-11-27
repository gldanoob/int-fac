import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- A finite weighted second moment gives surviving outcomes even when bad incidence
is correlated with the total count. -/
theorem survivorMoment {ι : Type*} (s : Finset ι) (w Z B : ι → ℝ)
    {a M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hB : ∀ i ∈ s, 0 ≤ B i) (hwtotal : ∑ i ∈ s, w i = 1)
    (hmean : a ≤ ∑ i ∈ s, w i * Z i)
    (hsecond : ∑ i ∈ s, w i * Z i ^ 2 ≤ M)
    (hbad : M * (∑ i ∈ s, w i * B i) ≤ a ^ 3 / 64) :
    a ^ 2 / (8 * M) ≤
      ∑ i ∈ s.filter (fun i => a / 2 ≤ Z i ∧ Z i ≤ 4 * M / a ∧ B i ≤ a / 4), w i := by
  let large := s.filter (fun i => a / 2 ≤ Z i)
  let good := s.filter (fun i => a / 2 ≤ Z i ∧ Z i ≤ 4 * M / a ∧ B i ≤ a / 4)
  have hslarge : large ⊆ s := filter_subset _ _
  have hlargeMean : a / 2 ≤ ∑ i ∈ large, w i * Z i := by
    have h := sum_le_sum (s := s) (fun i hi => show
        w i * Z i ≤ (if a / 2 ≤ Z i then w i * Z i else 0) + (a / 2) * w i by
      split_ifs with h
      · linarith [mul_nonneg (show 0 ≤ a / 2 by positivity) (hw i hi)]
      · nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge h) (hw i hi)])
    rw [sum_add_distrib, ← sum_filter, ← mul_sum, hwtotal, mul_one] at h
    linarith
  have hCS : (∑ i ∈ large, w i * Z i) ^ 2 ≤
      (∑ i ∈ large, w i) * ∑ i ∈ large, w i * Z i ^ 2 :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul large
      (fun i hi => hw i (hslarge hi))
      (fun i hi => mul_nonneg (hw i (hslarge hi)) (sq_nonneg _))
      (fun _ _ => by ring_nf; rfl)
  have hlarge : a ^ 2 / 4 ≤ M * ∑ i ∈ large, w i := by
    have hsub := sum_le_sum_of_subset_of_nonneg hslarge
      (fun i hi _ => mul_nonneg (hw i hi) (sq_nonneg (Z i)))
    have hmul := mul_le_mul_of_nonneg_left (hsub.trans hsecond)
      (sum_nonneg fun i hi => hw i (hslarge hi))
    have hsq := pow_le_pow_left₀ (show 0 ≤ a / 2 by positivity) hlargeMean 2
    nlinarith
  have hdel := sum_le_sum (s := s) (fun i hi => show
      M * (if a / 2 ≤ Z i then w i else 0) ≤
        M * (if a / 2 ≤ Z i ∧ Z i ≤ 4 * M / a ∧ B i ≤ a / 4 then w i else 0) +
        a ^ 2 / (16 * M) * (w i * Z i ^ 2) + (4 * M / a) * (w i * B i) by
    have hwi := hw i hi
    have hBi := hB i hi
    have h1 : 0 ≤ a ^ 2 / (16 * M) * (w i * Z i ^ 2) := by positivity
    have h2 : 0 ≤ (4 * M / a) * (w i * B i) := by positivity
    by_cases hz : a / 2 ≤ Z i
    · by_cases hu : Z i ≤ 4 * M / a
      · by_cases hb : B i ≤ a / 4
        · simp [hz, hu, hb]; linarith
        · simp [hz, hu, hb]
          have hfactor : M ≤ (4 * M / a) * B i := by
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ ha).2
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hfactor (hw i hi)]
      · simp [hz, hu]
        have hcut : 4 * M ≤ Z i * a := (div_le_iff₀ ha).1 (le_of_not_ge hu)
        have hsq := pow_le_pow_left₀ (show 0 ≤ 4 * M by positivity) hcut 2
        have hfactor : M ≤ a ^ 2 / (16 * M) * Z i ^ 2 := by
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ (show 0 < 16 * M by positivity)).2
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hfactor (hw i hi)]
    · simp [hz]
      linarith)
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum,
    ← sum_filter, ← sum_filter] at hdel
  have hsecond' := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ a ^ 2 / (16 * M) by positivity)
  have hbad' : (4 * M / a) * (∑ i ∈ s, w i * B i) ≤ a ^ 2 / 16 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha).2
    nlinarith
  have hsimp : a ^ 2 / (16 * M) * M = a ^ 2 / 16 := by
    field_simp
  rw [hsimp] at hsecond'
  apply (div_le_iff₀ (show 0 < 8 * M by positivity)).2
  change a ^ 2 ≤ (∑ i ∈ good, w i) * (8 * M)
  change M * (∑ i ∈ large, w i) ≤ M * (∑ i ∈ good, w i) + _ + _ at hdel
  nlinarith

/-- The retained outcomes have at least a quarter of the target count after deletion. -/
theorem survivorMoment_count {ι : Type*} (s : Finset ι) (w Z B : ι → ℝ)
    {a M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hB : ∀ i ∈ s, 0 ≤ B i)
    (hwtotal : ∑ i ∈ s, w i = 1)
    (hmean : a ≤ ∑ i ∈ s, w i * Z i)
    (hsecond : ∑ i ∈ s, w i * Z i ^ 2 ≤ M)
    (hbad : M * (∑ i ∈ s, w i * B i) ≤ a ^ 3 / 64) :
    a ^ 2 / (8 * M) ≤
      ∑ i ∈ s.filter (fun i => a / 4 ≤ Z i - B i ∧ Z i ≤ 4 * M / a), w i := by
  apply (survivorMoment s w Z B ha hM hw hB hwtotal hmean hsecond hbad).trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨his, hZ, hu, hB⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨his, by linarith, hu⟩
  · intro i hi _
    exact hw i (mem_filter.mp hi).1

end Cogentic.Randomized
