import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

open scoped Finset

namespace Cogentic.RandomizedCenteredBoxRatio

/-- The cross-multiplied cardinality bound for a dilated centered interval. -/
theorem two_mul_floor_add_one_le {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m) :
    2 * Nat.floor ((m : ℝ) * x) + 1 ≤ (2 * m - 1) * (2 * Nat.floor x + 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfloor : Nat.floor ((m : ℝ) * x) < m * (Nat.floor x + 1) := by
    apply (Nat.floor_lt (mul_nonneg hmR.le hx)).2
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact mul_lt_mul_of_pos_left (Nat.lt_floor_add_one x) hmR
  rw [Nat.mul_add, Nat.mul_one] at hfloor
  have hfactor : m ≤ 2 * m - 1 := by omega
  calc
    _ ≤ 2 * (m * Nat.floor x) + (2 * m - 1) := by omega
    _ = m * (2 * Nat.floor x) + (2 * m - 1) := by ac_rfl
    _ ≤ (2 * m - 1) * (2 * Nat.floor x) + (2 * m - 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hfactor) _
    _ = _ := by rw [Nat.mul_add, Nat.mul_one]

/-- The integer interval of radius `Nat.floor x` centered at zero. -/
noncomputable def centeredInterval (x : ℝ) : Finset ℤ :=
  Finset.Icc (-(Nat.floor x : ℤ)) (Nat.floor x : ℤ)

theorem card_centeredInterval (x : ℝ) : (centeredInterval x).card = 2 * Nat.floor x + 1 := by
  rw [centeredInterval, Int.card_Icc]
  omega

theorem card_centeredInterval_mul_le {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m) :
    (centeredInterval ((m : ℝ) * x)).card ≤ (2 * m - 1) * (centeredInterval x).card := by
  simp only [card_centeredInterval]
  exact two_mul_floor_add_one_le hx hm

noncomputable def centeredBox (x y z : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  centeredInterval x ×ˢ (centeredInterval y ×ˢ centeredInterval z)

/-- The three coordinate enlargements cost at most 47 · 23 · 15 points
per point of the inner integer box. -/
theorem card_centeredBox_dilate_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (centeredBox (24 * x) (12 * y) (8 * z)).card ≤ 16215 * (centeredBox x y z).card := by
  have hx' : (centeredInterval (24 * x)).card ≤ 47 * (centeredInterval x).card := by
    exact_mod_cast card_centeredInterval_mul_le hx (m := 24) (by decide)
  have hy' : (centeredInterval (12 * y)).card ≤ 23 * (centeredInterval y).card := by
    exact_mod_cast card_centeredInterval_mul_le hy (m := 12) (by decide)
  have hz' : (centeredInterval (8 * z)).card ≤ 15 * (centeredInterval z).card := by
    exact_mod_cast card_centeredInterval_mul_le hz (m := 8) (by decide)
  simp only [centeredBox, Finset.card_product]
  calc
    _ ≤ (47 * (centeredInterval x).card) *
        ((23 * (centeredInterval y).card) * (15 * (centeredInterval z).card)) :=
      Nat.mul_le_mul hx' (Nat.mul_le_mul hy' hz')
    _ = _ := by ring

#print axioms two_mul_floor_add_one_le
#print axioms card_centeredInterval
#print axioms card_centeredBox_dilate_le

end Cogentic.RandomizedCenteredBoxRatio
