import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Cogentic.Randomized

variable {A G V : Type*} [AddCommGroup A] [AddCommGroup G] [AddCommGroup V]

/-- If the parities of every integral relation lie in `U`, the parity
quotient is a homomorphic image of the image of the class map. -/
theorem exists_surjective_classRange_to_parityQuotient {R : Type*} [Ring R] [Module R V]
    (classMap : A →+ G) (parity : A →+ V) (U : Submodule R V)
    (hparity : Function.Surjective parity) (hU : ∀ a, classMap a = 0 → parity a ∈ U) :
    ∃ f : classMap.range →+ V ⧸ U, Function.Surjective f := by
  let q := U.mkQ.toAddMonoidHom.comp parity
  have hker : classMap.ker ≤ q.ker := by
    intro a ha
    change U.mkQ (parity a) = 0
    exact (Submodule.Quotient.mk_eq_zero U).mpr (hU a ha)
  let lift := QuotientAddGroup.lift classMap.ker q hker
  have hlift : Function.Surjective lift := by
    intro v
    obtain ⟨a, ha⟩ := (U.mkQ_surjective.comp hparity) v
    exact ⟨QuotientAddGroup.mk a, ha⟩
  let e := QuotientAddGroup.quotientKerEquivRange classMap
  exact ⟨lift.comp e.symm.toAddMonoidHom, hlift.comp e.symm.surjective⟩

/-- The parity quotient's cardinality divides the cardinality of the
obstruction group by the first isomorphism theorem and Lagrange's theorem. -/
theorem parityQuotient_card_dvd {R : Type*} [Ring R] [Module R V]
    (classMap : A →+ G) (parity : A →+ V) (U : Submodule R V)
    (hparity : Function.Surjective parity) (hU : ∀ a, classMap a = 0 → parity a ∈ U) :
    Nat.card (V ⧸ U) ∣ Nat.card G := by
  obtain ⟨f, hf⟩ := exists_surjective_classRange_to_parityQuotient classMap parity U hparity hU
  exact (AddSubgroup.card_dvd_of_surjective f hf).trans
    (AddSubgroup.card_addSubgroup_dvd_card classMap.range)

theorem parityQuotient_card_le {R : Type*} [Ring R] [Module R V] [Finite G]
    (classMap : A →+ G) (parity : A →+ V) (U : Submodule R V)
    (hparity : Function.Surjective parity) (hU : ∀ a, classMap a = 0 → parity a ∈ U) :
    Nat.card (V ⧸ U) ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos (parityQuotient_card_dvd classMap parity U hparity hU)

/-- The binary parity codimension is bounded by the power of two dividing
the size of the obstruction group. -/
theorem binary_parityQuotient_pow_finrank_dvd [Module (ZMod 2) V] [Finite G]
    (classMap : A →+ G) (parity : A →+ V) (U : Submodule (ZMod 2) V)
    (hparity : Function.Surjective parity) (hU : ∀ a, classMap a = 0 → parity a ∈ U) :
    2 ^ Module.finrank (ZMod 2) (V ⧸ U) ∣ Nat.card G := by
  obtain ⟨f, hf⟩ := exists_surjective_classRange_to_parityQuotient classMap parity U hparity hU
  let _ : Finite (V ⧸ U) := Finite.of_surjective f hf
  let _ : Module.Finite (ZMod 2) (V ⧸ U) := Module.Finite.of_finite
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V ⧸ U)
  rw [Nat.card_zmod] at hcard
  rw [← hcard]
  exact parityQuotient_card_dvd classMap parity U hparity hU

theorem binary_parityQuotient_pow_finrank_le [Module (ZMod 2) V] [Finite G]
    (classMap : A →+ G) (parity : A →+ V) (U : Submodule (ZMod 2) V)
    (hparity : Function.Surjective parity) (hU : ∀ a, classMap a = 0 → parity a ∈ U) :
    2 ^ Module.finrank (ZMod 2) (V ⧸ U) ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos (binary_parityQuotient_pow_finrank_dvd classMap parity U hparity hU)

end Cogentic.Randomized
