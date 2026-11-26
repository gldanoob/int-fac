import Cogentic.RandomizedCRTSigns
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Cogentic.RandomizedOddSplit

open RandomizedHiddenLabels RandomizedSignCount RandomizedCRTSigns

noncomputable def factorPrime (N : ℕ) (i : Fin N.primeFactors.card) : ℕ :=
  (N.primeFactors.equivFin.symm i).val

theorem factorPrime_mem (N : ℕ) (i : Fin N.primeFactors.card) :
    factorPrime N i ∈ N.primeFactors := (N.primeFactors.equivFin.symm i).property

private theorem factorPrime_injective (N : ℕ) : Function.Injective (factorPrime N) :=
  fun _ _ h => N.primeFactors.equivFin.symm.injective (Subtype.ext h)

theorem factorization_indexed_product {N : ℕ} (hn : N ≠ 0) :
    (∏ i : Fin N.primeFactors.card, factorPrime N i ^ N.factorization (factorPrime N i)) = N := by
  calc
    (∏ i : Fin N.primeFactors.card, factorPrime N i ^ N.factorization (factorPrime N i)) =
        ∏ p : N.primeFactors, p.val ^ N.factorization p.val :=
      Fintype.prod_equiv N.primeFactors.equivFin.symm _ _ fun _ => rfl
    _ = ∏ p ∈ N.primeFactors, p ^ N.factorization p :=
      Finset.prod_coe_sort N.primeFactors (fun p : ℕ => p ^ N.factorization p)
    _ = N.factorization.prod (· ^ ·) := by rw [Finsupp.prod, Nat.support_factorization]
    _ = N := Nat.prod_factorization_pow_eq_self hn

theorem two_le_factor_count {N : ℕ} (hn : 3 ≤ N) (hnot : ¬ IsPrimePow N) :
    2 ≤ N.primeFactors.card := by
  have h := (Nat.not_isPrimePow_iff_nontrivial_of_two_le (by omega : 2 ≤ N)).mp hnot
  exact Finset.one_lt_card_iff_nontrivial.mpr h

private theorem factorPrime_odd {N : ℕ} (ho : Odd N) (i : Fin N.primeFactors.card) :
    Odd (factorPrime N i) :=
  Nat.coprime_two_left.mp <|
    ho.coprime_two_left.coprime_dvd_right (Nat.mem_primeFactors.mp (factorPrime_mem N i)).2.1

private theorem factorExponent_pos {N : ℕ} (hn : N ≠ 0) (i : Fin N.primeFactors.card) :
    0 < N.factorization (factorPrime N i) := by
  have hm := Nat.mem_primeFactors.mp (factorPrime_mem N i)
  exact hm.1.factorization_pos_of_dvd hn hm.2.1

private noncomputable def signsForModulus {N k : ℕ} (p e : Fin k → ℕ)
    (distinct : Function.Injective p) (hp : ∀ i, (p i).Prime) (ho : ∀ i, Odd (p i))
    (he : ∀ i, 0 < e i) (hprod : (∏ i, p i ^ e i) = N) :
    SquareFiber (1 : (ZMod N)ˣ) ≃ SignCube k :=
  hprod ▸ crtSigns p e distinct hp ho he

/-- The CRT cube indexed by the distinct prime divisors of an odd modulus. -/
noncomputable def oddSigns {N : ℕ} (hn : 3 ≤ N) (ho : Odd N) :
    SquareFiber (1 : (ZMod N)ˣ) ≃ SignCube N.primeFactors.card :=
  signsForModulus (factorPrime N) (fun i => N.factorization (factorPrime N i))
    (factorPrime_injective N) (fun i => Nat.prime_of_mem_primeFactors (factorPrime_mem N i))
    (factorPrime_odd ho) (factorExponent_pos (by omega)) (factorization_indexed_product (by omega))

/-- Integer gcd taken from the canonical nonnegative representative of a square root of one. -/
def splitGcd {N : ℕ} (x : SquareFiber (1 : (ZMod N)ˣ)) : ℕ :=
  Nat.gcd ((x.val : ZMod N).val - 1) N

private theorem proper_gcd_iff_mixed_of_product {k N : ℕ} (p e : Fin k → ℕ)
    (distinct : Function.Injective p) (hp : ∀ i, (p i).Prime) (ho : ∀ i, Odd (p i))
    (he : ∀ i, 0 < e i) (hprod : (∏ i, p i ^ e i) = N) (hn : 3 ≤ N)
    (oddN : Odd N) (x : SquareFiber (1 : (ZMod N)ˣ)) :
    (1 < splitGcd x ∧ splitGcd x < N) ↔
      (∃ i, signsForModulus p e distinct hp ho he hprod x i = true) ∧
      ∃ i, signsForModulus p e distinct hp ho he hprod x i = false := by
  subst N
  let N := ∏ i, p i ^ e i
  let signs := crtSigns p e distinct hp ho he
  let n := (x.val : ZMod N).val
  change (1 < Nat.gcd (n - 1) N ∧ Nat.gcd (n - 1) N < N) ↔
    (∃ i, signs x i = true) ∧ ∃ i, signs x i = false
  let : NeZero N := ⟨by omega⟩
  let : Fact (1 < N) := ⟨by omega⟩
  have npos : 1 ≤ n := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr (Units.ne_zero x.val))
  have rep : (n : ZMod N) = x.val := ZMod.natCast_zmod_val _
  constructor
  · intro proper
    classical
    constructor
    · by_contra notPositive
      have allNegative (i : Fin k) : signs x i = false := by
        cases h : signs x i
        · rfl
        · exact (notPositive ⟨i, h⟩).elim
      let negRoot : SquareFiber (1 : (ZMod N)ˣ) := ⟨-1, by simp⟩
      have negBits (i : Fin k) : signs negRoot i = false := by
        cases h : signs negRoot i
        · rfl
        · have equal := (crtSigns_true p e distinct hp ho he negRoot i).mp h
          have prime_gt : 2 < p i := by
            rcases ho i with ⟨r, hr⟩
            have := (hp i).two_le
            omega
          let : Fact (2 < p i ^ e i) := ⟨prime_gt.trans_le (Nat.le_pow (he i))⟩
          let reduce : ZMod N →+* ZMod (p i ^ e i) :=
            ZMod.castHom (Finset.dvd_prod_of_mem (fun j => p j ^ e j) (Finset.mem_univ i)) _
          change reduce (-1) = 1 at equal
          rw [map_neg, map_one] at equal
          exact (ZMod.neg_one_ne_one equal).elim
      have hx : x = negRoot := signs.injective (funext fun i => (allNegative i).trans (negBits i).symm)
      have nplus : N ∣ n + 1 := by
        apply (ZMod.natCast_eq_zero_iff _ _).mp
        rw [Nat.cast_add, rep, hx]
        simp [negRoot]
      have d_two : Nat.gcd (n - 1) N ∣ 2 := by
        have hp := (Nat.gcd_dvd_right (n - 1) N).trans nplus
        have hm := Nat.gcd_dvd_left (n - 1) N
        have hsub : (n + 1) - (n - 1) = 2 := by omega
        exact hsub ▸ Nat.dvd_sub hp hm
      have hco := oddN.coprime_two_right.coprime_dvd_left (Nat.gcd_dvd_right (n - 1) N)
      exact (Nat.not_lt_of_ge (hco.eq_one_of_dvd d_two).le) proper.1
    · by_contra notNegative
      have allPositive (i : Fin k) : signs x i = true := by
        cases h : signs x i
        · exact (notNegative ⟨i, h⟩).elim
        · rfl
      let oneRoot : SquareFiber (1 : (ZMod N)ˣ) := ⟨1, rfl⟩
      have oneBits (i : Fin k) : signs oneRoot i = true := by
        apply (crtSigns_true p e distinct hp ho he oneRoot i).mpr
        let reduce : ZMod N →+* ZMod (p i ^ e i) :=
          ZMod.castHom (Finset.dvd_prod_of_mem (fun j => p j ^ e j) (Finset.mem_univ i)) _
        change reduce 1 = 1
        exact map_one reduce
      have hx : x = oneRoot := signs.injective (funext fun i => (allPositive i).trans (oneBits i).symm)
      have nminus : N ∣ n - 1 := (Nat.modEq_iff_dvd' npos).mp <|
        (ZMod.natCast_eq_natCast_iff 1 n N).mp (by rw [rep, hx]; simp [oneRoot])
      have hg : N ∣ Nat.gcd (n - 1) N := Nat.dvd_gcd nminus (dvd_refl N)
      have gpos := Nat.gcd_pos_of_pos_right (n - 1) (by omega : 0 < N)
      exact (Nat.not_lt_of_ge (Nat.le_of_dvd gpos hg)) proper.2
  · rintro ⟨positive, negative⟩
    exact proper_gcd_of_mixed p e distinct hp ho he x n npos rep positive negative

theorem proper_gcd_iff_mixed {N : ℕ} (hn : 3 ≤ N) (ho : Odd N)
    (x : SquareFiber (1 : (ZMod N)ˣ)) :
    (1 < splitGcd x ∧ splitGcd x < N) ↔
      (∃ i, oddSigns hn ho x i = true) ∧ ∃ i, oddSigns hn ho x i = false :=
  proper_gcd_iff_mixed_of_product (factorPrime N) (fun i => N.factorization (factorPrime N i))
    (factorPrime_injective N) (fun i => Nat.prime_of_mem_primeFactors (factorPrime_mem N i))
    (factorPrime_odd ho) (factorExponent_pos (by omega)) (factorization_indexed_product (by omega))
    hn ho x

private theorem favorable_fraction {k : ℕ} (hk : 2 ≤ k) :
    ((2 ^ k - 2 : ℕ) : ℚ) / ((2 ^ k : ℕ) : ℚ) = 1 - 2 / (2 : ℚ) ^ k ∧
      (1 : ℚ) / 2 ≤ 1 - 2 / (2 : ℚ) ^ k := by
  have hfour : 4 ≤ (2 : ℕ) ^ k := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk
  have hq : (4 : ℚ) ≤ 2 ^ k := by exact_mod_cast hfour
  have hpos : (0 : ℚ) < 2 ^ k := pow_pos (by decide) _
  rw [Nat.cast_sub (by omega), Nat.cast_pow]
  constructor
  · norm_num
    field_simp
  · have h := (div_le_iff₀ hpos).mpr (show (2 : ℚ) ≤ (1 / 2) * 2 ^ k by linarith)
    linarith

variable {Label : Type*} [DecidableEq Label]

/-- With one odd private label varied uniformly, exactly the mixed outcomes
give a proper integer gcd with an odd non-prime-power modulus. -/
theorem hidden_split_fraction {N : ℕ} (hn : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (labels : Finset Label) (multiplicity : Label → ℕ) (roots : Label → (ZMod N)ˣ)
    {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i))
    (publicRoot : SquareFiber (labelProduct labels multiplicity roots)) :
    let k := N.primeFactors.card
    let signs := comparisonSigns labels multiplicity roots hi hodd publicRoot (oddSigns hn ho)
    let all := Finset.univ.map signs.symm.toEmbedding
    let favorable := (usefulSigns k).map signs.symm.toEmbedding
    (∀ x, x ∈ favorable ↔
      let D := splitGcd (compareRoot publicRoot (replacementOutput labels multiplicity roots i hi x))
      1 < D ∧ D < N) ∧
    favorable.card = 2 ^ k - 2 ∧ all.card = 2 ^ k ∧
    (favorable.card : ℚ) / all.card = 1 - 2 / (2 : ℚ) ^ k ∧
    (1 : ℚ) / 2 ≤ (favorable.card : ℚ) / all.card := by
  let k := N.primeFactors.card
  have hk := two_le_factor_count hn hnot
  have counts := proper_sign_count labels multiplicity roots hi hodd hk publicRoot (oddSigns hn ho)
  refine ⟨?_, counts.1, counts.2.1, counts.2.2.trans (favorable_fraction hk).1, ?_⟩
  · intro replacement
    rw [mem_mixed_comparison, comparisonSigns_apply, ← proper_gcd_iff_mixed hn ho]
  · exact (favorable_fraction hk).2.trans_eq ((favorable_fraction hk).1.symm.trans counts.2.2.symm)

end Cogentic.RandomizedOddSplit
