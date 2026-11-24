import Std

-- A useful oracle answer can contain extra factors. Count progress inside the
-- group exponent, where gcd(current, exponent) always divides the exponent.
theorem orderQueryDoubles {current answer order exponent : Nat}
    (positive : 0 < exponent) (localOrder : order ∣ exponent)
    (validAnswer : order ∣ answer) (needed : ¬ order ∣ current) :
    2 * current.gcd exponent ≤ (current.lcm answer).gcd exponent := by
  have grows := Nat.gcd_dvd_gcd_of_dvd_left exponent (Nat.dvd_lcm_left current answer)
  have includes : order ∣ (current.lcm answer).gcd exponent :=
    Nat.dvd_gcd (Nat.dvd_trans validAnswer (Nat.dvd_lcm_right current answer)) localOrder
  obtain ⟨k, hk⟩ := grows
  have newPos := Nat.gcd_pos_of_pos_right (current.lcm answer) positive
  have hk' : 2 ≤ k := by
    apply Classical.byContradiction
    intro small
    have cases : k = 0 ∨ k = 1 := by omega
    rcases cases with zero | one
    · simp [zero] at hk
      omega
    · simp [one] at hk
      rw [hk] at includes
      exact needed (Nat.dvd_trans includes (Nat.gcd_dvd_left current exponent))
  rw [hk, Nat.mul_comm 2]
  exact Nat.mul_le_mul_left _ hk'

-- Exponent is fixed across queries on one modulus. The initial accumulator
-- may be arbitrary because its gcd with a positive exponent is at least one.
theorem orderQueryCount {exponent count : Nat} (positive : 0 < exponent)
    (current : Nat → Nat)
    (step : ∀ j < count, 2 * (current j).gcd exponent ≤ (current (j + 1)).gcd exponent) :
    2 ^ count ≤ exponent := by
  have bound (j : Nat) (within : j ≤ count) : 2 ^ j ≤ (current j).gcd exponent := by
    induction j with
    | zero => exact Nat.gcd_pos_of_pos_right _ positive
    | succ j ih =>
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (ih (by omega))) (step j (by omega))
  exact Nat.le_trans (bound count (by omega)) (Nat.le_of_dvd positive (Nat.gcd_dvd_right _ _))
