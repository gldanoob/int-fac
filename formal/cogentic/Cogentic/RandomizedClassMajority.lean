import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Card

namespace Cogentic.RandomizedClassMajority

variable {G : Type*} [Group G] [DecidableEq G]

/-- First factors in A whose complementary factors for t lie in B. -/
def goodChoices (A B : Finset G) (t : G) : Finset G :=
  A.filter (fun a => a⁻¹ * t ∈ B)

private theorem goodChoices_eq_inter (A B : Finset G) (t : G) :
    goodChoices A B t =
      A ∩ B.map (((Equiv.inv G).trans (Equiv.mulRight t)).symm.toEmbedding) := by
  ext a
  rw [goodChoices, Finset.mem_filter, Finset.mem_inter, Finset.mem_map_equiv]
  rfl

variable [Fintype G]

/-- The finite-group convolution coefficient is bounded below by the sum
of the two set sizes minus the group size. -/
theorem card_goodChoices_ge (A B : Finset G) (t : G) :
    A.card + B.card - Fintype.card G ≤ (goodChoices A B t).card := by
  rw [goodChoices_eq_inter, Finset.card_inter, Finset.card_map]
  exact Nat.sub_le_sub_left (Finset.card_le_univ _) _

theorem card_majority_goodChoices_ge (A : Finset G) (t : G) :
    2 * A.card - Fintype.card G ≤ (goodChoices A A t).card := by
  simpa only [Nat.two_mul] using card_goodChoices_ge A A t

/-- Removing at most b rejected first factors loses at most b choices. -/
theorem card_goodChoices_excluding_ge (A B bad : Finset G) (t : G) {b : ℕ}
    (hbad : bad.card ≤ b) :
    A.card + B.card - Fintype.card G - b ≤ (goodChoices A B t \ bad).card := by
  have hcount := card_goodChoices_ge A B t
  have hsplit := Finset.card_sdiff_add_card_inter (goodChoices A B t) bad
  have hinter : (goodChoices A B t ∩ bad).card ≤ b :=
    (Finset.card_le_card Finset.inter_subset_right).trans hbad
  omega

theorem card_majority_goodChoices_excluding_ge (A bad : Finset G) (t : G) {b : ℕ}
    (hbad : bad.card ≤ b) :
    2 * A.card - Fintype.card G - b ≤ (goodChoices A A t \ bad).card := by
  simpa only [Nat.two_mul] using card_goodChoices_excluding_ge A A bad t hbad

#print axioms card_goodChoices_ge
#print axioms card_majority_goodChoices_ge
#print axioms card_majority_goodChoices_excluding_ge

end Cogentic.RandomizedClassMajority
