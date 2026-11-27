import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedStableEnergy

private theorem neg_base_le_signed_gap {a x u : ℝ}
    (hx₀ : 0 ≤ x) (hx : x ≤ a) (hu : -1 ≤ u) : -a ≤ u * x := by
  have h := mul_le_mul_of_nonneg_right hu hx₀
  linarith only [h, hx]

/-- The three-site energy exceeds one by at least twice the squared
distance of the parameter from one. -/
theorem three_site_energy_ge {a x y u v : ℝ} (ha : a ≤ 1)
    (hx₀ : 0 ≤ x) (hy₀ : 0 ≤ y) (hx : x ≤ a) (hy : y ≤ a)
    (hu : -1 ≤ u) (hv : -1 ≤ v) :
    1 + 2 * (1 - a) ^ 2 ≤ 3 + 2 * (u * x + v * y + u * v * x * y) := by
  have hux : 1 - a ≤ 1 + u * x := by linarith only [neg_base_le_signed_gap hx₀ hx hu]
  have hvy : 1 - a ≤ 1 + v * y := by linarith only [neg_base_le_signed_gap hy₀ hy hv]
  have hnonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha
  have hprod := mul_le_mul hux hvy hnonneg (hnonneg.trans hux)
  nlinarith only [hprod]

private theorem base_pos {a : ℝ} (ha₀ : 0 ≤ a) : 0 < 1 + a := by linarith

private theorem stable_denominator_pos {a : ℝ} (ha₀ : 0 ≤ a) (ha : a < 1) :
    0 < 1 - a ^ 2 := by
  nlinarith only [mul_pos (sub_pos.mpr ha) (base_pos ha₀)]

/-- The normalized energy for consecutive opposite unit entries. -/
theorem nearest_opposite_energy {a : ℝ} (ha₀ : 0 ≤ a) (ha : a < 1) :
    (2 - 2 * a) / (1 - a ^ 2) = 2 / (1 + a) := by
  field_simp [(stable_denominator_pos ha₀ ha).ne', (base_pos ha₀).ne']
  ring

/-- The two-site energy is minimized by consecutive opposite entries.
The three-site energy and the spectral lower bound for at least four
sites both exceed this minimum. -/
theorem normalized_energy_cases {a x y u v : ℝ} (ha : a < 1)
    (hx₀ : 0 ≤ x) (hy₀ : 0 ≤ y) (hx : x ≤ a) (hy : y ≤ a)
    (hu : -1 ≤ u) (hv : -1 ≤ v) :
    2 / (1 + a) ≤ (2 + 2 * u * x) / (1 - a ^ 2) ∧
      2 / (1 + a) < (3 + 2 * (u * x + v * y + u * v * x * y)) / (1 - a ^ 2) ∧
      (2 : ℝ) / (1 + a) < 4 / (1 + a) ^ 2 := by
  have ha₀ := hx₀.trans hx
  have hden := stable_denominator_pos ha₀ ha
  have hmin := nearest_opposite_energy ha₀ ha
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmin]
    apply div_le_div_of_nonneg_right _ hden.le
    have hux := neg_base_le_signed_gap hx₀ hx hu
    linarith only [hux]
  · rw [← hmin]
    apply div_lt_div_of_pos_right _ hden
    have hthree := three_site_energy_ge ha.le hx₀ hy₀ hx hy hu hv
    nlinarith only [hthree, sq_nonneg (2 * a - 1)]
  · have hbase := base_pos ha₀
    apply (lt_div_iff₀ (sq_pos_of_pos hbase)).2
    calc
      _ = 2 * (1 + a) := by field_simp [hbase.ne']
      _ < _ := by linarith only [ha]

#print axioms three_site_energy_ge
#print axioms nearest_opposite_energy
#print axioms normalized_energy_cases

end Cogentic.RandomizedStableEnergy
