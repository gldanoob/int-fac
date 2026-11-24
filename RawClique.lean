import Std

namespace RawClique

-- capacity is the bit lower bound for one ib gate's raw settings.
-- Every mid gate sends one residue to each ib gate outside its group.
theorem width_and_settings (capacity gates t settings width : Nat)
    (ht : t ≤ gates)
    (localCost : capacity * t ≤ settings)
    (crossCost : capacity * (gates - t) ≤ width) :
    capacity * gates ≤ settings + width := by
  calc
    capacity * gates = capacity * (t + (gates - t)) := by
      rw [Nat.add_sub_of_le ht]
    _ = capacity * t + capacity * (gates - t) := Nat.mul_add _ _ _
    _ ≤ settings + width := Nat.add_le_add localCost crossCost

-- In the pinned network there are 2*S gates per layer and each message
-- carries at least 8*S^2 bits' worth of raw residue choices (log base 2).
theorem raw_cost (s b t settings width r cost : Nat)
    (fits : b ≤ 4 * s^4) (ht : t ≤ 2*s)
    (localCost : ((2*s)*(8*s^2))*t ≤ settings)
    (crossCost : ((2*s)*(8*s^2))*(2*s-t) ≤ width)
    (paySettings : settings ≤ cost) (payPad : 2*width ≤ r*cost) :
    16*b ≤ (2+r)*cost := by
  have cap := width_and_settings _ _ _ _ _ ht localCost crossCost
  have scale : ((2*s)*(8*s^2))*(2*s) = 8*(4*s^4) := by
    simp only [Nat.pow_succ, Nat.pow_zero]
    ac_rfl
  rw [scale] at cap
  have low := Nat.mul_le_mul_left 8 fits
  rw [Nat.add_mul]
  omega

end RawClique
