import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-! A large prime inertia degree rules out a nontrivial intermediate number field. -/

namespace Cogentic.RandomizedSubfieldDegree

open Module
open scoped NumberField BigOperators Polynomial

/-- Each inertia degree is bounded by the rank of a finite flat extension. -/
private theorem inertiaDeg_le_finrank {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S] (P : Ideal S) [P.IsPrime] :
    P.inertiaDeg R ≤ finrank R S := by
  classical
  let p := P.under R
  let : p.IsPrime := Ideal.IsPrime.under R P
  let : Fintype (p.primesOver S) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  let Q : p.primesOver S := ⟨P, ⟨inferInstance, Ideal.over_under P⟩⟩
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S]
  calc
    P.inertiaDeg R ≤ P.ramificationIdx R * P.inertiaDeg R :=
      Nat.le_mul_of_pos_left _ (P.ramificationIdx_pos R)
    _ ≤ ∑ Q' : p.primesOver S, Q'.1.ramificationIdx R * Q'.1.inertiaDeg R :=
      Finset.single_le_sum (f := fun Q' : p.primesOver S =>
        Q'.1.ramificationIdx R * Q'.1.inertiaDeg R)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ Q)

variable {E K : Type*} [Field E] [Field K] [NumberField E] [NumberField K]
variable [Algebra E K] [IsScalarTower ℚ E K]

omit [IsScalarTower ℚ E K] in
/-- In a tower, a prime absolute inertia degree is at most the larger of
the two global degrees. No unramified or Galois hypotheses are needed. -/
theorem prime_inertiaDeg_le_max (P : Ideal (𝓞 K)) [P.IsPrime]
    (hp : Nat.Prime (P.inertiaDeg ℤ)) :
    P.inertiaDeg ℤ ≤ max (finrank ℚ E) (finrank E K) := by
  let Q := P.under (𝓞 E)
  let : Q.IsPrime := Ideal.IsPrime.under (𝓞 E) P
  let : P.LiesOver Q := Ideal.over_under P
  have hbot : Q.inertiaDeg ℤ ≤ finrank ℚ E :=
    (inertiaDeg_le_finrank Q).trans_eq (NumberField.RingOfIntegers.rank E)
  have htop : P.inertiaDeg (𝓞 E) ≤ finrank E K :=
    (inertiaDeg_le_finrank P).trans_eq (IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K).symm
  have htower := Ideal.inertiaDeg_tower (R := ℤ) Q P
  rw [htower] at hp ⊢
  rcases Nat.prime_mul_iff.mp hp with ⟨_, h⟩ | ⟨_, h⟩
  · simpa only [h, mul_one] using hbot.trans (le_max_left _ (finrank E K))
  · simpa only [h, one_mul] using htop.trans (le_max_right (finrank ℚ E) _)

/-- If both tower degrees exceed one, the absolute inertia degree of any prime
ideal with prime inertia degree is at most half the absolute field degree. -/
theorem prime_inertiaDeg_le_half (P : Ideal (𝓞 K)) [P.IsPrime]
    (hE : 1 < finrank ℚ E) (hK : 1 < finrank E K)
    (hp : Nat.Prime (P.inertiaDeg ℤ)) :
    P.inertiaDeg ℤ ≤ finrank ℚ K / 2 := by
  have hd := Module.finrank_mul_finrank ℚ E K
  have hleft : finrank ℚ E * 2 ≤ finrank ℚ K := by
    rw [← hd]
    exact Nat.mul_le_mul_left _ hK
  have hright : finrank E K * 2 ≤ finrank ℚ K := by
    rw [← hd, Nat.mul_comm (finrank E K) 2]
    exact Nat.mul_le_mul_right _ hE
  have hmax : max (finrank ℚ E) (finrank E K) ≤ finrank ℚ K / 2 := by
    exact max_le (by omega) (by omega)
  exact (prime_inertiaDeg_le_max (E := E) P hp).trans hmax

/-- A specified prime degree larger than half the field degree cannot occur as
an inertia degree in a tower with both degrees greater than one. -/
theorem inertiaDeg_ne_large_prime (P : Ideal (𝓞 K)) [P.IsPrime] {q : ℕ}
    (hE : 1 < finrank ℚ E) (hK : 1 < finrank E K)
    (hq : Nat.Prime q) (hlarge : finrank ℚ K / 2 < q) :
    P.inertiaDeg ℤ ≠ q := by
  intro he
  have h := prime_inertiaDeg_le_half P hE hK (he ▸ hq)
  exact (not_lt_of_ge (he ▸ h)) hlarge

/-- Away from primes dividing the conductor exponent, the same obstruction applies
to the degrees of monic irreducible factors of the reduced minimal polynomial. -/
theorem factor_degree_not_prime_of_half_lt {p : ℕ} [Fact p.Prime]
    (θ : 𝓞 K) (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    (hE : 1 < finrank ℚ E) (hK : 1 < finrank E K)
    (Q : (ZMod p)[X]) (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p)
    (hlarge : finrank ℚ K / 2 < Q.natDegree) : ¬ Nat.Prime Q.natDegree := by
  intro hq
  let P := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩
  have he : P.1.inertiaDeg ℤ = Q.natDegree :=
    NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ
  exact inertiaDeg_ne_large_prime P.1 hE hK hq hlarge he

end Cogentic.RandomizedSubfieldDegree
