import Cogentic.FixedSchedule

namespace Cogentic.Construction

/-- The signed integer coefficient pair lies in the deterministic positive
    enumeration rectangle. -/
def inCoefficientBox (n : ℕ) (k : ℤ×ℤ) : Prop :=
  let b := n.log2+1
  0<k.1 ∧ k.1≤2*(b:ℤ)^2*Fixed.U b*Fixed.A b ∧ 0<k.2 ∧ k.2≤2*(b:ℤ)^2*Fixed.U b

instance (n : ℕ) (k : ℤ×ℤ) : Decidable (inCoefficientBox n k) := by unfold inCoefficientBox; infer_instance

theorem inCoefficientBox.nat_ranges {n : ℕ} {k : ℤ×ℤ} (h : inCoefficientBox n k) :
    let b := n.log2+1
    (1≤k.1.toNat ∧ k.1.toNat≤2*b^2*Fixed.U b*Fixed.A b) ∧
    (1≤k.2.toNat ∧ k.2.toNat≤2*b^2*Fixed.U b) := by
  intro b
  obtain ⟨hp,hu,hq,hv⟩ := h
  exact ⟨⟨by omega,Int.toNat_le.mpr (by exact_mod_cast hu)⟩,
    ⟨by omega,Int.toNat_le.mpr (by exact_mod_cast hv)⟩⟩

end Cogentic.Construction
