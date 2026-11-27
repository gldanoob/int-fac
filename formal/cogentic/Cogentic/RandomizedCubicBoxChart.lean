import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Cogentic.RandomizedCubicBoxChart

variable {K : Type*} [Field K]

abbrev onChart (q : K × K × K) : Prop :=
  q.2.2 ≠ 0 ∧ q.1 * q.2.2 = q.2.1 ^ 2

def point (t z : K) : K × K × K := (z * t ^ 2, z * t, z)

/-- The open chart z ≠ 0 is parametrized by the slope y/z and the last coordinate. -/
def chartEquiv (K : Type*) [Field K] :
    (K × {z : K // z ≠ 0}) ≃ {q : K × K × K // onChart q} where
  toFun tz := ⟨point tz.1 tz.2, tz.2.property, by dsimp [point]; ring⟩
  invFun q := (q.val.2.1 / q.val.2.2, ⟨q.val.2.2, q.property.1⟩)
  left_inv := by
    rintro ⟨t, z⟩
    apply Prod.ext
    · change (z : K) * t / (z : K) = t
      field_simp [z.property]
    · exact Subtype.ext rfl
  right_inv := by
    rintro ⟨⟨x, y, z⟩, hz, hxy⟩
    apply Subtype.ext
    change (z * (y / z) ^ 2, z * (y / z), z) = (x, y, z)
    have hx : z * (y / z) ^ 2 = x := by
      calc
        _ = y ^ 2 / z := by field_simp [hz]
        _ = x := (div_eq_iff hz).mpr hxy.symm
    have hy : z * (y / z) = y := by field_simp [hz]
    exact Prod.ext hx (Prod.ext hy rfl)

variable [Fintype K] [DecidableEq K]

/-- Any weight on chart points can be summed in slope and height coordinates. -/
theorem sum_chart {A : Type*} [AddCommMonoid A] (w : K × K × K → A) :
    (∑ q : {q : K × K × K // onChart q}, w q.val) =
      ∑ t : K, ∑ z : {z : K // z ≠ 0}, w (point t z) := by
  symm
  rw [← Fintype.sum_prod_type' (fun (t : K) (z : {z : K // z ≠ 0}) => w (point t z))]
  exact Fintype.sum_equiv (chartEquiv K) _ _ (fun _ => rfl)

/-- Count the chart points in any finite box by testing the parametrized points. -/
theorem card_box (box : Finset (K × K × K)) :
    (box.filter onChart).card =
      ∑ t : K, ∑ z : {z : K // z ≠ 0}, if point t z ∈ box then (1 : ℕ) else 0 := by
  have hbox : box.subtype onChart =
      Finset.univ.filter (fun q : {q : K × K × K // onChart q} => q.val ∈ box) := by
    ext q
    simp
  rw [← Finset.card_subtype, hbox, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact sum_chart (fun q => if q ∈ box then (1 : ℕ) else 0)

#print axioms chartEquiv
#print axioms sum_chart
#print axioms card_box

end Cogentic.RandomizedCubicBoxChart
