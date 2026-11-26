import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Ring.Parity

namespace Cogentic.RandomizedHiddenLabels

variable {Label Row G : Type*} [CommGroup G]

/-- Occurrences of the same hidden root use its label's total multiplicity. -/
def labelProduct (labels : Finset Label) (multiplicity : Label → ℕ) (roots : Label → G) : G :=
  ∏ i ∈ labels, roots i ^ multiplicity i

theorem row_products_eq_labelProduct (rows : Finset Row) (labels : Finset Label)
    (multiplicity : Row → Label → ℕ) (roots : Label → G) :
    (∏ row ∈ rows, labelProduct labels (multiplicity row) roots) =
      labelProduct labels (fun i => ∑ row ∈ rows, multiplicity row i) roots := by
  unfold labelProduct
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ =>
    Finset.prod_pow_eq_pow_sum rows (fun row => multiplicity row i) (roots i)

variable [DecidableEq Label]

theorem labelProduct_update (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) (t : G) :
    labelProduct labels multiplicity (Function.update roots i (t * roots i)) =
      t ^ multiplicity i * labelProduct labels multiplicity roots := by
  unfold labelProduct
  rw [← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ _ hi]
  have same :
      (∏ j ∈ labels.erase i, Function.update roots i (t * roots i) j ^ multiplicity j) =
        ∏ j ∈ labels.erase i, roots j ^ multiplicity j :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [same, Function.update_self, mul_pow, mul_assoc]

theorem labelProduct_update_even (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) (heven : Even (multiplicity i))
    {t : G} (ht : t ^ 2 = 1) :
    labelProduct labels multiplicity (Function.update roots i (t * roots i)) =
      labelProduct labels multiplicity roots := by
  obtain ⟨k, hk⟩ := heven
  rw [labelProduct_update labels multiplicity roots hi, hk, ← two_mul, pow_mul, ht,
    one_pow, one_mul]

theorem labelProduct_update_odd (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i))
    {t : G} (ht : t ^ 2 = 1) :
    labelProduct labels multiplicity (Function.update roots i (t * roots i)) =
      t * labelProduct labels multiplicity roots := by
  obtain ⟨k, hk⟩ := hodd
  rw [labelProduct_update labels multiplicity roots hi, hk, pow_add, pow_mul, ht,
    one_pow, one_mul, pow_one]

theorem labelProduct_update_square (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) {t : G} (ht : t ^ 2 = 1) :
    (labelProduct labels multiplicity (Function.update roots i (t * roots i))) ^ 2 =
      (labelProduct labels multiplicity roots) ^ 2 := by
  rw [labelProduct_update labels multiplicity roots hi, mul_pow, ← pow_mul,
    Nat.mul_comm (multiplicity i) 2, pow_mul, ht, one_pow, one_mul]

/-- Varying one odd label over its square fiber covers the output square fiber
exactly once, with every other label fixed. -/
theorem existsUnique_replacement (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i))
    (target : G) (hsquare : target ^ 2 = (labelProduct labels multiplicity roots) ^ 2) :
    ∃! x : G, x ^ 2 = (roots i) ^ 2 ∧
      labelProduct labels multiplicity (Function.update roots i x) = target := by
  let base := labelProduct labels multiplicity roots
  let t := target * base⁻¹
  have ht : t ^ 2 = 1 := by
    dsimp [t, base]
    rw [mul_pow, inv_pow, hsquare, mul_inv_cancel]
  refine ⟨t * roots i, ⟨by rw [mul_pow, ht, one_mul], ?_⟩, ?_⟩
  · rw [labelProduct_update_odd labels multiplicity roots hi hodd ht]
    simp [t, base, mul_assoc]
  · intro x hx
    let u := x * (roots i)⁻¹
    have hu : u ^ 2 = 1 := by
      dsimp [u]
      rw [mul_pow, inv_pow, hx.1, mul_inv_cancel]
    have hx' : u * roots i = x := by simp [u, mul_assoc]
    have hout : u * base = target := by
      have flip := labelProduct_update_odd labels multiplicity roots hi hodd hu
      rw [hx', hx.2] at flip
      exact flip.symm
    have hut : u = t := by
      calc
        u = (u * base) * base⁻¹ := by simp [mul_assoc]
        _ = t := by simp only [t, hout]
    rw [← hx', hut]

end Cogentic.RandomizedHiddenLabels
