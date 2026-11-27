import Cogentic.RandomizedClassSignFibers
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Coset.Card

namespace Cogentic.RandomizedTargetGenus

open RandomizedSignCount RandomizedClassSignFibers

variable {G V : Type*} [CommGroup G] [Group V]

/-- If the quotient has exponent two and its order is the size of the
two-torsion of G, surjectivity forces the kernel to be the square subgroup. -/
theorem ker_eq_squares_of_card [Finite G] (norm : G →* V) (hsurj : Function.Surjective norm)
    (exponent_two : ∀ v : V, v ^ 2 = 1)
    (hcard : Nat.card V = Nat.card (powMonoidHom (α := G) 2).ker) :
    norm.ker = (powMonoidHom (α := G) 2).range := by
  have hsub : (powMonoidHom (α := G) 2).range ≤ norm.ker := by
    rintro _ ⟨x, rfl⟩
    change norm (x ^ 2) = 1
    rw [map_pow, exponent_two]
  have hn := Subgroup.card_eq_card_quotient_mul_card_subgroup norm.ker
  have hs := Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom (α := G) 2).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective norm hsurj).toEquiv, hcard] at hn
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
    (powMonoidHom (α := G) 2)).toEquiv, mul_comm] at hs
  have hpos : 0 < Nat.card (powMonoidHom (α := G) 2).ker := Nat.card_pos
  have hmul : Nat.card (powMonoidHom (α := G) 2).ker * Nat.card norm.ker =
      Nat.card (powMonoidHom (α := G) 2).ker * Nat.card (powMonoidHom (α := G) 2).range :=
    hn.symm.trans hs
  exact (Subgroup.eq_of_le_of_card_ge hsub (Nat.eq_of_mul_eq_mul_left hpos hmul).le).symm

/-- The public outputs of P times a square are precisely the target norm class. -/
theorem target_support (norm : G →* V) (hker : norm.ker = (powMonoidHom (α := G) 2).range)
    (P y : G) : (∃ x : G, P * x ^ 2 = y) ↔ norm y = norm P := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ^ 2 ∈ norm.ker := by rw [hker]; exact ⟨x, rfl⟩
    simp only [map_mul, MonoidHom.mem_ker.mp hx, mul_one]
  · intro h
    have hx : P⁻¹ * y ∈ norm.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [hker] at hx
    obtain ⟨x, hx⟩ := hx
    refine ⟨x, ?_⟩
    change x ^ 2 = P⁻¹ * y at hx
    simp [hx]

/-- Every point in the target norm class has exactly the two-torsion number
of private lifts. -/
theorem target_fiber_card (norm : G →* V)
    (hker : norm.ker = (powMonoidHom (α := G) 2).range) (P y : G)
    (hy : norm y = norm P) :
    Nat.card {x : G // P * x ^ 2 = y} = Nat.card (powMonoidHom (α := G) 2).ker := by
  obtain ⟨a, ha⟩ := (target_support norm hker P y).2 hy
  have equiv : {x : G // P * x ^ 2 = y} ≃ SquareFiber a :=
    Equiv.subtypeEquivRight fun _ => by rw [← ha, mul_right_inj]
  exact Nat.card_congr (equiv.trans (squareFiberEquivTwoTorsion a))

/-- Uniform sampling in G followed by multiplication of a square by P gives
the uniform law on the target norm class, in cross-multiplied finite counts. -/
theorem target_uniform [Finite G] (norm : G →* V)
    (hker : norm.ker = (powMonoidHom (α := G) 2).range) (P y : G)
    (hy : norm y = norm P) :
    Nat.card {x : G // P * x ^ 2 = y} * Nat.card {z : G // norm z = norm P} = Nat.card G := by
  have hclass : Nat.card {z : G // norm z = norm P} = Nat.card norm.ker :=
    Nat.card_congr (norm.fiberEquivKer P)
  rw [target_fiber_card norm hker P y hy, hclass, hker, mul_comm]
  have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom (α := G) 2).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
    (powMonoidHom (α := G) 2)).toEquiv] at hcount
  exact hcount.symm

/-- Retargeting by a known square permutes the uniform input, preserving the
law for every public event. This does not require the quotient hypothesis. -/
theorem retarget_square_card (P s : G) (event : G → Prop) :
    Nat.card {x : G // event ((P * s ^ 2) * x ^ 2)} =
      Nat.card {x : G // event (P * x ^ 2)} :=
  Nat.card_congr ((Equiv.mulLeft s).subtypeEquiv fun x => by
    change event ((P * s ^ 2) * x ^ 2) ↔ event (P * (s * x) ^ 2)
    rw [mul_pow, mul_assoc])

/-- Any two public targets in the same norm class induce the same output law. -/
theorem same_norm_target_card (norm : G →* V)
    (hker : norm.ker = (powMonoidHom (α := G) 2).range) {P P' : G}
    (hnorm : norm P' = norm P) (event : G → Prop) :
    Nat.card {x : G // event (P' * x ^ 2)} =
      Nat.card {x : G // event (P * x ^ 2)} := by
  obtain ⟨s, hs⟩ := (target_support norm hker P P').2 hnorm
  rw [← hs]
  exact retarget_square_card P s event

end Cogentic.RandomizedTargetGenus
