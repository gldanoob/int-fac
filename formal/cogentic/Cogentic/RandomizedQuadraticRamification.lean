import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

variable {R : Type*} [CommRing R]

/-- The square-over-norm expression on a scalar shift uses the product
of the two conjugate evaluations in the denominator. -/
theorem quadratic_shift_norm {a r s T P : R} (hT : r+s = T) (hP : r*s = P) :
    (a+r)*(a+s) = a^2+T*a+P := by
  rw [← hT, ← hP]
  ring

theorem quadratic_discriminant_eq_diff_sq {r s T P : R} (hT : r+s = T) (hP : r*s = P) :
    T^2-4*P = (r-s)^2 := by
  rw [← hT, ← hP]
  ring

theorem quadratic_discriminant_eq_zero_of_coincident {r s T P : R}
    (hT : r+s = T) (hP : r*s = P) (hrs : r = s) : T^2-4*P = 0 := by
  rw [quadratic_discriminant_eq_diff_sq hT hP, hrs, sub_self, zero_pow (by decide)]

/-- Distinct evaluations of the quadratic generator remain distinct
after a common scalar shift. If their sum is a unit, they cannot be negatives. -/
theorem quadratic_shift_ne_global_sign {a r s T : R} (hT : r+s = T)
    (hrs : r ≠ s) (hunit : IsUnit (2*a+T)) :
    a+r ≠ a+s ∧ a+r ≠ -(a+s) := by
  have : Nontrivial R := nontrivial_of_ne r s hrs
  refine ⟨fun h => hrs (add_left_cancel h), ?_⟩
  intro h
  apply hunit.ne_zero
  calc
    2*a+T = (a+r)+(a+s) := by rw [← hT]; ring
    _ = 0 := by rw [h, neg_add_cancel]

/-- Normalizing the square of one evaluation by the quadratic norm
equals its ratio to the conjugate evaluation. -/
theorem quadratic_square_over_norm (x y : Rˣ) : x^2*(x*y)⁻¹ = x*y⁻¹ := by
  calc
    _ = (x*x⁻¹)*(x*y⁻¹) := by rw [pow_two, mul_inv_rev]; ac_rfl
    _ = _ := by simp

/-- The positive sign detects coincidence of the two evaluations. -/
theorem quadratic_shift_ratio_eq_one_iff {a r s : R} (x y : Rˣ)
    (hx : (x : R) = a+r) (hy : (y : R) = a+s) :
    x*y⁻¹ = 1 ↔ r = s := by
  rw [mul_inv_eq_iff_eq_mul, one_mul]
  constructor
  · intro h
    have hv := congrArg Units.val h
    rw [hx, hy] at hv
    exact add_left_cancel hv
  · intro h
    apply Units.ext
    rw [hx, hy, h]

/-- The negative sign occurs precisely when the sum of the two shifted
evaluations vanishes. -/
theorem quadratic_shift_ratio_eq_neg_one_iff {a r s T : R} (x y : Rˣ)
    (hx : (x : R) = a+r) (hy : (y : R) = a+s) (hT : r+s = T) :
    x*y⁻¹ = -1 ↔ 2*a+T = 0 := by
  have he : (a+r)+(a+s) = 2*a+T := by rw [← hT]; ring
  rw [mul_inv_eq_iff_eq_mul, neg_one_mul]
  constructor
  · intro h
    have hv := congrArg Units.val h
    rw [Units.val_neg, hx, hy] at hv
    rw [← he, hv, neg_add_cancel]
  · intro h
    apply Units.ext
    rw [Units.val_neg, hx, hy]
    calc
      a+r = (a+r)+(a+s)-(a+s) := by ring
      _ = -(a+s) := by rw [he, h, zero_sub]

/-- If the two shifted evaluations and their sum are units, distinct
evaluations give a square-over-norm quotient outside the global signs. -/
theorem quadratic_normalized_not_global_sign {a r s T : R} (hT : r+s = T)
    (hrs : r ≠ s) (hu : IsUnit (a+r)) (hv : IsUnit (a+s)) (hsum : IsUnit (2*a+T)) :
    hu.unit^2*(hu.unit*hv.unit)⁻¹ ≠ 1 ∧ hu.unit^2*(hu.unit*hv.unit)⁻¹ ≠ -1 := by
  have : Nontrivial R := nontrivial_of_ne r s hrs
  rw [quadratic_square_over_norm]
  exact ⟨fun h => hrs ((quadratic_shift_ratio_eq_one_iff _ _ hu.unit_spec hv.unit_spec).mp h),
    fun h => hsum.ne_zero ((quadratic_shift_ratio_eq_neg_one_iff _ _ hu.unit_spec hv.unit_spec hT).mp h)⟩

/-- The same local obstruction holds over the residue ring of any modulus. -/
theorem zmod_quadratic_normalized_not_global_sign {n : ℕ} {a r s T : ZMod n}
    (hT : r+s = T) (hrs : r ≠ s) (hu : IsUnit (a+r)) (hv : IsUnit (a+s))
    (hsum : IsUnit (2*a+T)) :
    hu.unit^2*(hu.unit*hv.unit)⁻¹ ≠ 1 ∧ hu.unit^2*(hu.unit*hv.unit)⁻¹ ≠ -1 :=
  quadratic_normalized_not_global_sign hT hrs hu hv hsum

/-- Global signs for all admissible scalar shifts force coincident roots
and hence zero discriminant as soon as one shift has the three required units. -/
theorem quadratic_discriminant_zero_of_all_global_sign {r s T P : R}
    (hT : r+s = T) (hP : r*s = P)
    (hshift : ∃ a, IsUnit (a+r) ∧ IsUnit (a+s) ∧ IsUnit (2*a+T))
    (hsign : ∀ a (hu : IsUnit (a+r)) (hv : IsUnit (a+s)),
      hu.unit^2*(hu.unit*hv.unit)⁻¹ = 1 ∨ hu.unit^2*(hu.unit*hv.unit)⁻¹ = -1) :
    T^2-4*P = 0 := by
  apply quadratic_discriminant_eq_zero_of_coincident hT hP
  by_contra hrs
  obtain ⟨a, hu, hv, hs⟩ := hshift
  have hn := quadratic_normalized_not_global_sign hT hrs hu hv hs
  exact (hsign a hu hv).elim hn.1 hn.2

/-- Over a finite field of odd characteristic, at most three shifts
are forbidden by the three unit conditions. -/
theorem finite_field_quadratic_shift_units {F : Type*} [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (hsize : 3 < Fintype.card F) (r s T : F) :
    ∃ a, IsUnit (a+r) ∧ IsUnit (a+s) ∧ IsUnit (2*a+T) := by
  classical
  let S : Finset F := {-r, -s, -T/2}
  have hc : S.card ≤ 3 := Finset.card_le_three
  obtain ⟨a, ha⟩ : ∃ a, a ∉ S := by
    by_contra! hn
    have he : (Finset.univ : Finset F) ⊆ S := fun a _ => hn a
    exact (not_le_of_gt hsize) ((by simpa using Finset.card_le_card he : Fintype.card F ≤ S.card).trans hc)
  refine ⟨a, isUnit_iff_ne_zero.mpr ?_, isUnit_iff_ne_zero.mpr ?_, isUnit_iff_ne_zero.mpr ?_⟩
  · intro h
    have he : a = -r := by
      calc
        a = (a+r)-r := by ring
        _ = -r := by rw [h, zero_sub]
    exact ha (by simp [S,he])
  · intro h
    have he : a = -s := by
      calc
        a = (a+s)-s := by ring
        _ = -s := by rw [h, zero_sub]
    exact ha (by simp [S,he])
  · intro h
    have he : a = -T/2 := (eq_div_iff_mul_eq h2).mpr (by
      calc
        a*2 = (2*a+T)-T := by ring
        _ = -T := by rw [h, zero_sub])
    exact ha (by simp [S,he])

/-- In the finite-field setting the scalar-shift existence premise is automatic. -/
theorem finite_field_quadratic_discriminant_zero_of_all_global_sign {F : Type*}
    [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (hsize : 3 < Fintype.card F)
    {r s T P : F} (hT : r+s = T) (hP : r*s = P)
    (hsign : ∀ a (hu : IsUnit (a+r)) (hv : IsUnit (a+s)),
      hu.unit^2*(hu.unit*hv.unit)⁻¹ = 1 ∨ hu.unit^2*(hu.unit*hv.unit)⁻¹ = -1) :
    T^2-4*P = 0 :=
  quadratic_discriminant_zero_of_all_global_sign hT hP
    (finite_field_quadratic_shift_units h2 hsize r s T) hsign

end Cogentic.Randomized
