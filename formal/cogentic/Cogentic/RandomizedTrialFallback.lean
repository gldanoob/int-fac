import Cogentic.CandidateSieveCost
import Cogentic.IndexCapCost
import Cogentic.RandomizedCostedFactorLaw

namespace Cogentic.RandomizedTrialFallback

open BinaryDivision BinaryPresieve

/-- Trial division returns a canonical divisor. Compute and canonicalize
the other factor with restoring division before returning the two words. -/
def splitWords (n : List Bool) : Option (List Bool × List Bool) × ℕ :=
  let trial := trialFactor n
  match trial.1 with
  | none => (none, trial.2 + 1)
  | some d =>
    let out := divide d n
    let q := BinarySaturation.canonical out.quotient
    (some (d, q.1), trial.2 + out.gates + q.2 + 1)

/-- A binary-encoded epoch cap that covers trial division and the quotient. -/
def cap (n : ℕ) : ℕ := 8192 * (n + 2) ^ 4

theorem cap_size_le (n : ℕ) : (cap n).size ≤ 4 * n.size + 22 := by
  have hcap : cap n = trialFactorCap n <<< 1 := by
    rw [Nat.shiftLeft_eq]
    unfold cap trialFactorCap
    ring
  rw [hcap, Nat.size_shiftLeft (by unfold trialFactorCap; positivity)]
  have hs := trialFactorCap_size_le n
  omega

theorem splitWords_spec {n : ℕ} (hn : 2 ≤ n) :
    (splitWords n.bits).1 =
        (if n.minFac < n then some (n.minFac.bits, (n / n.minFac).bits) else none) ∧
      (splitWords n.bits).2 ≤ cap n := by
  let x := n + 2
  have hs : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsize : n.size ≤ x := hs.trans (by dsimp [x]; omega)
  have h1 : x ≤ x ^ 4 := Nat.le_self_pow (by decide) _
  have h2 : x ^ 2 ≤ x ^ 4 := Nat.pow_le_pow_right (by dsimp [x]; omega) (by decide)
  have h4 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by dsimp [x]; omega)
  have hwork := trialFactor_work_le hn
  change (trialFactor n.bits).2 ≤ 4096 * x ^ 4 at hwork
  unfold splitWords
  dsimp only
  rw [trialFactor_spec hn]
  by_cases hcomp : n.minFac < n
  · simp only [if_pos hcomp]
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    obtain ⟨hq, _, hdiv⟩ := divide_naturals n n.minFac hp.pos
    obtain ⟨hc, hw⟩ := BinarySaturation.canonical_spec (divide n.minFac.bits n.bits).quotient
    change value (divide n.minFac.bits n.bits).quotient = n / n.minFac at hq
    rw [hq] at hc
    rw [BinaryIndexCap.quotient_length, Nat.size_eq_bits_len] at hw
    refine ⟨congrArg (fun q => some (n.minFac.bits, q)) hc, ?_⟩
    change (trialFactor n.bits).2 + (divide n.minFac.bits n.bits).gates +
      (BinarySaturation.canonical (divide n.minFac.bits n.bits).quotient).2 + 1 ≤ 8192 * x ^ 4
    have hd : n.minFac.size ≤ x := (Nat.size_le_size hcomp.le).trans hsize
    have hb : (divide n.minFac.bits n.bits).gates ≤ x * (20 * x + 1) := by
      refine hdiv.trans (Nat.mul_le_mul hsize ?_)
      omega
    rw [hw]
    nlinarith only [hwork, hb, hsize, h1, h2, h4]
  · simp only [if_neg hcomp, true_and]
    change (trialFactor n.bits).2 + 1 ≤ 8192 * x ^ 4
    omega

/-- The costed fallback for one composite input. The natural values here
interpret the two canonical binary words returned by the executable split. -/
def split (n : ℕ) (hn : 2 ≤ n) (hp : ¬ n.Prime) :
    RandomizedCostedFactorLaw.SplitOutcome n :=
  let out := splitWords n.bits
  let pair := out.1.getD ([], [])
  have hcomp := (Nat.not_prime_iff_minFac_lt hn).mp hp
  have heq : out.1 = some (n.minFac.bits, (n / n.minFac).bits) :=
    (splitWords_spec hn).1.trans (if_pos hcomp)
  have hleft : value pair.1 = n.minFac := by simp [pair, heq, value_bits]
  have hright : value pair.2 = n / n.minFac := by simp [pair, heq, value_bits]
  have hprod : value pair.1 * value pair.2 = n := by
    rw [hleft, hright, Nat.mul_div_cancel' (Nat.minFac_dvd n)]
  have hl : 2 ≤ value pair.1 := hleft.symm ▸ (Nat.minFac_prime (by omega : n ≠ 1)).two_le
  have hr : 2 ≤ value pair.2 := by
    by_contra! h
    have hlt := hleft.trans_lt hcomp
    rcases (by omega : value pair.2 = 0 ∨ value pair.2 = 1) with h0 | h1
    · simp [h0] at hprod
      omega
    · simp [h1] at hprod
      omega
  ⟨value pair.1, value pair.2, out.2, hl, hr, hprod⟩

theorem split_work_le (n : ℕ) (hn : 2 ≤ n) (hp : ¬ n.Prime) :
    (split n hn hp).work ≤ cap n :=
  (splitWords_spec hn).2

#print axioms splitWords_spec
#print axioms split_work_le
#print axioms cap_size_le

end Cogentic.RandomizedTrialFallback
