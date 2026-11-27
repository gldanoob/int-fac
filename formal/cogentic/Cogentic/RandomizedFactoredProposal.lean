import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedFactoredProposal

open scoped BigOperators ArithmeticFunction.omega
open UniqueFactorizationMonoid

/-- The squarefree divisors of a nonzero denominator are the divisors of its
radical, so their count depends only on the distinct prime factors. -/
theorem squarefree_divisor_count {t : ℕ} (ht : t ≠ 0) :
    (t.divisors.filter Squarefree).card = 2 ^ ω t := by
  classical
  have hrad : t.divisors.filter Squarefree = (radical t).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨fun ⟨⟨hdt, _⟩, hsq⟩ => ⟨(dvd_radical_iff hsq.isRadical ht).2 hdt, radical_ne_zero⟩,
      fun ⟨hdr, _⟩ => ⟨⟨hdr.trans radical_dvd_self, ht⟩, squarefree_radical.squarefree_of_dvd hdr⟩⟩
  rw [hrad, Nat.card_divisors radical_ne_zero]
  have hfactor (p : ℕ) (hp : p ∈ (radical t).primeFactors) :
      (radical t).factorization p + 1 = 2 := by
    obtain ⟨hp', hpd, _⟩ := Nat.mem_primeFactors.mp hp
    rw [Nat.factorization_eq_one_of_squarefree squarefree_radical hp' hpd]
  rw [Finset.prod_congr rfl hfactor, Finset.prod_const, Nat.primeFactors_radical]
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

/-- Independent binary signs have the same count as the squarefree divisor
representations of the denominator. -/
theorem sign_assignment_count (t : ℕ) :
    Fintype.card ((↥t.primeFactors) → Bool) = 2 ^ ω t := by
  rw [Fintype.card_fun]
  simp only [Fintype.card_bool, Fintype.card_coe]
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

/-- Every divisor of an admissible denominator occurs in exactly one bucket.
The complementary factor fits in the second draw's prescribed range. -/
theorem unique_divisor_bucket {t d J : ℕ} (ht : t ≠ 0) (htop : t < 2 ^ (J + 1))
    (hdvd : d ∣ t) :
    ∃! j, j ≤ J ∧ 2 ^ j ≤ d ∧ d < 2 ^ (j + 1) ∧
      0 < t / d ∧ t / d ≤ 2 ^ (J + 1 - j) := by
  have hd : d ≠ 0 := by
    rintro rfl
    exact ht (by simpa using hdvd)
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero ht) hdvd
  let j := Nat.log 2 d
  have hj : j ≤ J := Nat.lt_succ_iff.mp
    ((Nat.log_lt_iff_lt_pow (by decide) hd).2 (hle.trans_lt htop))
  have hjlo : 2 ^ j ≤ d := Nat.pow_log_le_self 2 hd
  have hjhi : d < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by decide) d
  have hpow : (2 : ℕ) ^ (J + 1 - j) * 2 ^ j = 2 ^ (J + 1) := by
    rw [← pow_add, show J + 1 - j + j = J + 1 by omega]
  have hquot : t / d < 2 ^ (J + 1 - j) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hd)).2
    exact htop.trans_le (hpow ▸ Nat.mul_le_mul_left _ hjlo)
  refine ⟨j, ⟨hj, hjlo, hjhi, Nat.div_pos hle (Nat.pos_of_ne_zero hd), hquot.le⟩, ?_⟩
  intro j' hj'
  exact (Nat.log_eq_of_pow_le_of_lt_pow hj'.2.1 hj'.2.2.1).symm

/-- The dyadic bucket and its two factored draws give the same mass to every
admitted ordered divisor pair. The second draw has range length 2^(J+1-j). -/
theorem dyadic_pair_mass (J j : ℕ) (hj : j ≤ J) :
    1 / ((J : ℝ) + 1) * (1 / (2 : ℝ) ^ (j + 1)) * (1 / (2 : ℝ) ^ (J + 1 - j)) =
      1 / (4 * (2 : ℝ) ^ J * ((J : ℝ) + 1)) := by
  have hpow : (2 : ℝ) ^ (j + 1) * 2 ^ (J + 1 - j) = 4 * 2 ^ J := by
    rw [← pow_add, show j + 1 + (J + 1 - j) = J + 2 by omega, pow_add]
    ring
  rw [div_mul_div_comm, div_mul_div_comm, one_mul, one_mul, mul_assoc, hpow, mul_comm ((J : ℝ) + 1)]

/-- For a valid pair there is one selected winding integer, one sign assignment,
and one padded slot for each squarefree divisor representation. Their masses
sum to a value independent of the denominator. -/
theorem valid_pair_mass {t : ℕ} (ht : t ≠ 0) (pairMass : ℝ) (windings padding : ℕ) :
    (∑ _d ∈ t.divisors.filter Squarefree,
        pairMass * (1 / (windings : ℝ)) *
          (1 / (Fintype.card ((↥t.primeFactors) → Bool) : ℝ)) * (1 / (padding : ℝ))) =
      pairMass * (1 / (windings : ℝ)) * (1 / (padding : ℝ)) := by
  classical
  rw [Finset.sum_const, nsmul_eq_mul, squarefree_divisor_count ht, sign_assignment_count]
  push_cast
  have hsign : (2 : ℝ) ^ ω t ≠ 0 := by positivity
  field_simp

/-- At padding eight, the common mass is 1/(32 T (J+1) K) with T=2^J. -/
theorem padded_proposal_mass {t : ℕ} (ht : t ≠ 0) (J K : ℕ) :
    (∑ _d ∈ t.divisors.filter Squarefree,
        (1 / (4 * (2 : ℝ) ^ J * ((J : ℝ) + 1))) * (1 / (K : ℝ)) *
          (1 / (Fintype.card ((↥t.primeFactors) → Bool) : ℝ)) * (1 / (8 : ℝ))) =
      1 / (32 * (2 : ℝ) ^ J * ((J : ℝ) + 1) * (K : ℝ)) := by
  calc
    _ = (1 / (4 * (2 : ℝ) ^ J * ((J : ℝ) + 1))) * (1 / (K : ℝ)) * (1 / (8 : ℝ)) := by
      simpa only [Nat.cast_ofNat] using
        valid_pair_mass ht (1 / (4 * (2 : ℝ) ^ J * ((J : ℝ) + 1))) K 8
    _ = _ := by
      rw [div_mul_div_comm, div_mul_div_comm, one_mul, one_mul]
      congr 1
      ring

end Cogentic.RandomizedFactoredProposal
