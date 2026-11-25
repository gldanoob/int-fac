import ModularPower

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

namespace OrderCertificate

/-- Inspect the first `steps` residues in x, x², x⁴, ... modulo n. -/
def scan (n x : Nat) : Nat → Option Nat
  | 0 => none
  | steps + 1 =>
    let divisor := n.gcd (x - 1)
    if 1 < divisor ∧ divisor < n then some divisor
    else scan n ((x * x) % n) steps

def squareAt (n x : Nat) : Nat → Nat
  | 0 => x
  | i + 1 => squareAt n ((x * x) % n) i

theorem scan_sound {n x steps divisor : Nat} (hit : scan n x steps = some divisor) :
    1 < divisor ∧ divisor < n ∧ divisor ∣ n := by
  induction steps generalizing x with
  | zero => simp [scan] at hit
  | succ _ ih =>
    simp only [scan] at hit
    split at hit
    · rename_i yes
      cases hit
      exact ⟨yes.1, yes.2, Nat.gcd_dvd_left _ _⟩
    · exact ih hit

/-- A residue which is one modulo p and not one modulo q separates n even
when its factorization has other primes or repeated prime powers. -/
theorem scan_hits {n x steps i p q : Nat} (hn : 0 < n) (hp : 1 < p)
    (pn : p ∣ n) (qn : q ∣ n) (within : i < steps)
    (left : p ∣ squareAt n x i - 1) (right : ¬ q ∣ squareAt n x i - 1) :
    ∃ divisor, scan n x steps = some divisor := by
  induction steps generalizing x i with
  | zero => omega
  | succ _ ih =>
    simp only [scan]
    split
    · exact ⟨_, rfl⟩
    · rename_i failed
      cases i with
      | zero =>
        change p ∣ x - 1 at left
        change ¬ q ∣ x - 1 at right
        have divides := Nat.dvd_gcd pn left
        have big := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn) divides
        have bound := Nat.gcd_le_left (x - 1) hn
        have strict : n.gcd (x - 1) ≠ n := by
          intro h
          have d := Nat.gcd_dvd_right n (x - 1)
          rw [h] at d
          exact right (Nat.dvd_trans qn d)
        exact False.elim (failed (by omega))
      | succ j => exact ih (by omega) left right

/-- This concrete verified order certificate for 77 needs only the first gcd. -/
example : ModularPower.powMod 2 30 77 = 1 ∧ scan 77 (ModularPower.powMod 2 15 77) 1 = some 7 := by
  simp only [ModularPower.powMod_def]
  decide

end OrderCertificate
