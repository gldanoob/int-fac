import Std

namespace ModularPower

/-- Square-and-multiply with one recursive call per exponent bit. -/
def powMod (a e n : Nat) : Nat :=
  if e = 0 then 1 % n else
    let half := powMod a (e/2) n
    let square := half * half % n
    if e % 2 = 0 then square else square * (a % n) % n
termination_by e
decreasing_by omega

theorem powMod_def (a e n : Nat) : powMod a e n = a ^ e % n := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rw [powMod]
    split
    · rename_i h; simp [h]
    · rename_i h
      have half := ih (e/2) (by omega)
      have square : powMod a (e/2) n * powMod a (e/2) n % n = a^(e/2*2) % n := by
        rw [half, Nat.pow_mul, Nat.pow_two, Nat.mod_mul_mod, Nat.mul_mod_mod]
      dsimp only
      split
      · rename_i even
        rw [square, show e/2*2 = e by omega]
      · rename_i odd
        rw [square, Nat.mod_mul_mod, Nat.mul_mod_mod, ← Nat.pow_succ,
          show (e/2*2).succ = e by omega]

/-- Each nonzero exponent squares once, and odd exponents multiply once more. -/
def multiplyCount (e : Nat) : Nat :=
  if e = 0 then 0 else multiplyCount (e/2) + (if e % 2 = 0 then 1 else 2)
termination_by e
decreasing_by omega

theorem multiplyCount_le {e bits : Nat} (fits : e < 2^bits) : multiplyCount e ≤ 2*bits := by
  induction bits generalizing e with
  | zero =>
    have : e = 0 := by simpa using fits
    simp [this, multiplyCount]
  | succ bits ih =>
    rw [Nat.pow_succ] at fits
    have half := ih (e := e/2) (by omega)
    rw [multiplyCount]
    split
    · omega
    · split <;> omega

end ModularPower
