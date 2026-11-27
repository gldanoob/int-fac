import Cogentic.CharacterEstimate
import Cogentic.RandomizedGenusMixing
import Cogentic.RandomizedPrimeBinBias
import Cogentic.RandomizedPrimeBinSupply
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Staged Smooth Leading-Coefficient Supply and Rankin Prefix Bounds

This file formalizes:
1. Elementary abelian genus characters `χ_S` and the Kronecker/splitting character `χ_{-8N}`
   modulo `8 * N` for odd `N ≥ 3`, with nontriviality of both `χ_S` and `χ_S * χ_{-8N}`.
2. Split-prime dyadic band counts, normalized genus-character bias bounds under Dirichlet GRH
   (`DirichletLZerosOnLine`), and stability under deleting exceptional subsets `E`.
3. Product genus mixing via `Cogentic.RandomizedGenusMixing.identity_mass_bias` together with
   a repeated-prime collision bound yielding distinct squarefree principal-genus tuples.
4. Elementary Rankin prefix upper bounds: the divisor-weight bound `∑_{m₀ ≤ U} 2^{ω(m₀)} ≤ U(1 + log U)`,
   the certified-prefix weighted count bound, and Rankin's inequality for smooth reciprocals.
-/

namespace Cogentic.RandomizedReducedFormSupply

open scoped BigOperators NumberTheorySymbols
open Finset

/-!
## Section 1: Genus characters and splitting character modulo `8 * N`
-/

/-- The quadratic character `χ_{-8}` modulo `8`, taking `+1` on `{1, 3}` and `-1` on `{5, 7}`. -/
def chiNeg8Int : DirichletCharacter ℤ 8 where
  toFun x := match x.val with
    | 1 | 3 => 1
    | 5 | 7 => -1
    | _ => 0
  map_one' := by decide
  map_mul' x y := by revert x y; decide
  map_nonunit' x hx := by revert x hx; decide

/-- The quadratic character `χ_{8}` modulo `8`, taking `+1` on `{1, 7}` and `-1` on `{3, 5}`. -/
def chi8Int : DirichletCharacter ℤ 8 where
  toFun x := match x.val with
    | 1 | 7 => 1
    | 3 | 5 => -1
    | _ => 0
  map_one' := by decide
  map_mul' x y := by revert x y; decide
  map_nonunit' x hx := by revert x hx; decide

/-- The 2-part of the splitting character `χ_{-8N}` modulo `8`. -/
def twoPartCharInt (N : ℕ) : DirichletCharacter ℤ 8 :=
  if N % 4 = 1 then chiNeg8Int else chi8Int

theorem twoPartCharInt_five (N : ℕ) : twoPartCharInt N (5 : ZMod 8) = -1 := by
  unfold twoPartCharInt
  split_ifs <;> decide

theorem twoPartCharInt_eq_one_or_neg_one (N : ℕ) {x : ZMod 8} (hx : IsUnit x) :
    twoPartCharInt N x = 1 ∨ twoPartCharInt N x = -1 := by
  unfold twoPartCharInt
  split_ifs <;> (revert x hx; decide)

/-- The Legendre character at an odd prime factor `ℓ ∣ N`, lifted to level `8 * N`. -/
noncomputable def primeGenusCharInt (N ℓ : ℕ) : DirichletCharacter ℤ (8 * N) :=
  if h : ℓ.Prime ∧ ℓ ∣ N then
    have : Fact ℓ.Prime := ⟨h.1⟩
    DirichletCharacter.changeLevel (dvd_mul_of_dvd_right h.2 8) (quadraticChar (ZMod ℓ))
  else
    1

/-- The elementary abelian genus character `χ_S` indexed by a subset `S ⊆ N.primeFactors`,
    valued in `ℤ` as a Dirichlet character modulo `8 * N`. -/
noncomputable def genusCharInt (N : ℕ) (S : Finset ℕ) : DirichletCharacter ℤ (8 * N) :=
  ∏ ℓ ∈ S, primeGenusCharInt N ℓ

/-- Real-valued genus character `χ_S` modulo `8 * N`. -/
noncomputable def genusCharReal (N : ℕ) (S : Finset ℕ) : DirichletCharacter ℝ (8 * N) :=
  (genusCharInt N S).ringHomComp (Int.castRingHom ℝ)

/-- Complex-valued genus character `χ_S` modulo `8 * N`. -/
noncomputable def genusChar (N : ℕ) (S : Finset ℕ) : DirichletCharacter ℂ (8 * N) :=
  (genusCharInt N S).ringHomComp (Int.castRingHom ℂ)

/-- The integer-valued Kronecker/splitting character `χ_{-8N}` modulo `8 * N`. -/
noncomputable def splittingCharInt (N : ℕ) : DirichletCharacter ℤ (8 * N) :=
  DirichletCharacter.changeLevel (dvd_mul_right 8 N) (twoPartCharInt N) *
    ∏ ℓ ∈ N.primeFactors, (primeGenusCharInt N ℓ) ^ (N.factorization ℓ)

/-- The complex-valued Kronecker/splitting character `χ_{-8N}` modulo `8 * N`. -/
noncomputable def splittingChar (N : ℕ) : DirichletCharacter ℂ (8 * N) :=
  (splittingCharInt N).ringHomComp (Int.castRingHom ℂ)

private lemma isCoprime_int_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    IsCoprime (a : ℤ) (b : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  exact h.gcd_eq_one

private lemma coprime_eight_mul_iff_coprime_two_mul {N a : ℕ} :
    Nat.Coprime a (8 * N) ↔ Nat.Coprime a (2 * N) := by
  constructor
  · intro h
    have h2 : Nat.Coprime a 2 :=
      (Nat.Coprime.coprime_mul_right_right h).coprime_dvd_right (by norm_num)
    exact h2.mul_right (Nat.Coprime.coprime_mul_left_right h)
  · intro h
    have h2 : Nat.Coprime a 2 := Nat.Coprime.coprime_mul_right_right h
    have h8 : Nat.Coprime a 8 := by
      simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using h2.pow_right 3
    exact h8.mul_right (Nat.Coprime.coprime_mul_left_right h)

private lemma mulChar_finset_prod_apply {R S ι : Type*} [CommMonoid R] [CommMonoidWithZero S]
    (s : Finset ι) (f : ι → MulChar R S) {x : R} (hx : IsUnit x) :
    (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MulChar.one_apply hx]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, MulChar.mul_apply, ih]

private lemma mulChar_pow_apply {R S : Type*} [CommMonoid R] [CommMonoidWithZero S]
    (χ : MulChar R S) (k : ℕ) {x : R} (hx : IsUnit x) :
    (χ ^ k) x = (χ x) ^ k := by
  induction k with
  | zero => simp [MulChar.one_apply hx]
  | succ k ih => rw [pow_succ, pow_succ, MulChar.mul_apply, ih]

lemma primeGenusCharInt_apply_of_coprime {N ℓ a : ℕ}
    (hℓp : ℓ.Prime) (hℓd : ℓ ∣ N) (ha : Nat.Coprime a (8 * N)) :
    primeGenusCharInt N ℓ (a : ZMod (8 * N)) = @legendreSym ℓ ⟨hℓp⟩ (a : ℤ) := by
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have haZ : IsCoprime (a : ℤ) ((8 * N : ℕ) : ℤ) := isCoprime_int_of_coprime ha
  have hdef : primeGenusCharInt N ℓ =
      DirichletCharacter.changeLevel (dvd_mul_of_dvd_right hℓd 8) (quadraticChar (ZMod ℓ)) := by
    unfold primeGenusCharInt
    rw [dif_pos ⟨hℓp, hℓd⟩]
  rw [hdef]
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd'
    (quadraticChar (ZMod ℓ)) (dvd_mul_of_dvd_right hℓd 8) haZ
  simpa [legendreSym] using h1

lemma primeGenusCharInt_eq_one_or_neg_one {N ℓ : ℕ} {x : ZMod (8 * N)} (hx : IsUnit x) :
    primeGenusCharInt N ℓ x = 1 ∨ primeGenusCharInt N ℓ x = -1 := by
  unfold primeGenusCharInt
  split_ifs with h
  · have : Fact ℓ.Prime := ⟨h.1⟩
    obtain ⟨u, rfl⟩ := hx
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd _ (dvd_mul_of_dvd_right h.2 8) u]
    have hunit : IsUnit (ZMod.cast (u : ZMod (8 * N)) : ZMod ℓ) := by
      have hcast : (ZMod.cast (u : ZMod (8 * N)) : ZMod ℓ) =
          ZMod.castHom (dvd_mul_of_dvd_right h.2 8) (ZMod ℓ) (u : ZMod (8 * N)) :=
        (ZMod.castHom_apply (u : ZMod (8 * N))).symm
      rw [hcast]
      exact u.isUnit.map _
    have hne : (ZMod.cast (u : ZMod (8 * N)) : ZMod ℓ) ≠ 0 := by
      intro h0
      rw [h0] at hunit
      exact not_isUnit_zero hunit
    exact quadraticChar_dichotomy hne
  · left
    exact MulChar.one_apply hx

lemma genusCharInt_eq_one_or_neg_one {N : ℕ} (S : Finset ℕ) {x : ZMod (8 * N)} (hx : IsUnit x) :
    genusCharInt N S x = 1 ∨ genusCharInt N S x = -1 := by
  rw [genusCharInt, mulChar_finset_prod_apply S _ hx]
  induction S using Finset.induction_on with
  | empty => left; simp
  | insert ℓ s hℓ ih =>
    rw [Finset.prod_insert hℓ]
    rcases primeGenusCharInt_eq_one_or_neg_one (N := N) (ℓ := ℓ) hx with h1 | h1 <;>
      rcases ih with h2 | h2 <;> simp [h1, h2]

lemma splittingCharInt_eq_one_or_neg_one {N : ℕ} {x : ZMod (8 * N)} (hx : IsUnit x) :
    splittingCharInt N x = 1 ∨ splittingCharInt N x = -1 := by
  obtain ⟨u, rfl⟩ := hx
  rw [splittingCharInt, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd _ (dvd_mul_right 8 N) u,
    mulChar_finset_prod_apply _ _ u.isUnit]
  have h2u : IsUnit (ZMod.cast (u : ZMod (8 * N)) : ZMod 8) := by
    have hcast : (ZMod.cast (u : ZMod (8 * N)) : ZMod 8) =
        ZMod.castHom (dvd_mul_right 8 N) (ZMod 8) (u : ZMod (8 * N)) :=
      (ZMod.castHom_apply (u : ZMod (8 * N))).symm
    rw [hcast]
    exact u.isUnit.map _
  have h2 := twoPartCharInt_eq_one_or_neg_one N h2u
  have hprod : (∏ ℓ ∈ N.primeFactors, (primeGenusCharInt N ℓ ^ N.factorization ℓ) (u : ZMod (8 * N))) = 1 ∨
      (∏ ℓ ∈ N.primeFactors, (primeGenusCharInt N ℓ ^ N.factorization ℓ) (u : ZMod (8 * N))) = -1 := by
    induction N.primeFactors using Finset.induction_on with
    | empty => left; simp
    | insert ℓ s hℓ ih =>
      rw [Finset.prod_insert hℓ, mulChar_pow_apply _ _ u.isUnit]
      have hℓ1 : (primeGenusCharInt N ℓ (u : ZMod (8 * N))) ^ N.factorization ℓ = 1 ∨
          (primeGenusCharInt N ℓ (u : ZMod (8 * N))) ^ N.factorization ℓ = -1 := by
        rcases primeGenusCharInt_eq_one_or_neg_one (N := N) (ℓ := ℓ) u.isUnit with h | h
        · left; simp [h]
        · rw [h]
          rcases Nat.even_or_odd (N.factorization ℓ) with he | ho
          · left; exact he.neg_one_pow
          · right; exact ho.neg_one_pow
      rcases hℓ1 with h1 | h1 <;> rcases ih with h2' | h2' <;> simp [h1, h2']
  rcases h2 with h2 | h2 <;> rcases hprod with h3 | h3 <;> simp [h2, h3]

lemma genusCharReal_apply (N : ℕ) (S : Finset ℕ) (x : ZMod (8 * N)) :
    genusCharReal N S x = (genusCharInt N S x : ℝ) := rfl

lemma genusChar_apply (N : ℕ) (S : Finset ℕ) (x : ZMod (8 * N)) :
    genusChar N S x = (genusCharInt N S x : ℂ) := rfl

lemma genusChar_eq_ofReal_genusCharReal (N : ℕ) (S : Finset ℕ) (x : ZMod (8 * N)) :
    genusChar N S x = ((genusCharReal N S x : ℝ) : ℂ) := by
  simp [genusChar_apply, genusCharReal_apply]

lemma splittingChar_apply (N : ℕ) (x : ZMod (8 * N)) :
    splittingChar N x = (splittingCharInt N x : ℂ) := rfl

lemma abs_genusCharReal_le_one (N : ℕ) (S : Finset ℕ) (x : ZMod (8 * N)) :
    |genusCharReal N S x| ≤ 1 := by
  rw [genusCharReal_apply]
  by_cases hx : IsUnit x
  · rcases genusCharInt_eq_one_or_neg_one S hx with h | h <;> simp [h]
  · simp [MulChar.map_nonunit _ hx]

private lemma neg_one_pow_eq_mod_two (k : ℕ) : (-1 : ℤ) ^ k = (-1 : ℤ) ^ (k % 2) := by
  conv_lhs => rw [← Nat.div_add_mod k 2]
  rw [pow_add, pow_mul]
  norm_num

private lemma twoPartCharInt_eq_jacobi_sign {N p : ℕ} (hN : Odd N) (hp : Odd p) :
    twoPartCharInt N (p : ZMod 8) = J(-2 | p) * (-1) ^ (N / 2 * (p / 2)) := by
  rw [jacobiSym.at_neg_two hp]
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have := Nat.odd_iff.mp hp
    omega
  have hN4 : N % 4 = 1 ∨ N % 4 = 3 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hN)
  have hcast : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact (Nat.mod_modEq p 8).symm
  have hp2 : (p / 2) % 2 = (p % 8) / 2 % 2 := by omega
  have hN2 : (N / 2) % 2 = (N % 4) / 2 := by omega
  have hpow : (-1 : ℤ) ^ (N / 2 * (p / 2)) = (-1 : ℤ) ^ ((N % 4 / 2) * ((p % 8) / 2 % 2)) := by
    rw [neg_one_pow_eq_mod_two, neg_one_pow_eq_mod_two ((N % 4 / 2) * ((p % 8) / 2 % 2))]
    congr 1
    rw [Nat.mul_mod, hN2, hp2, Nat.mul_mod]
  rw [hcast, hpow, twoPartCharInt]
  rcases hN4 with hN1 | hN3
  · rw [if_pos hN1]
    rcases hp8 with h | h | h | h <;> rw [h, hN1] <;> decide
  · rw [if_neg (by omega : N % 4 ≠ 1)]
    rcases hp8 with h | h | h | h <;> rw [h, hN3] <;> decide

private lemma jacobiSym_finset_prod_pow (a : ℤ) (s : Finset ℕ) (e : ℕ → ℕ)
    (hmem : ∀ ℓ ∈ s, ℓ.Prime) :
    J(a | ∏ ℓ ∈ s, ℓ ^ e ℓ) =
      ∏ ℓ ∈ s, (if h : ℓ.Prime then @legendreSym ℓ ⟨h⟩ a else 1) ^ (e ℓ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert ℓ s hℓ ih =>
    rw [Finset.prod_insert hℓ, Finset.prod_insert hℓ]
    have hℓp : ℓ.Prime := hmem ℓ (Finset.mem_insert_self ℓ s)
    have h1 : ℓ ^ e ℓ ≠ 0 := pow_ne_zero _ hℓp.ne_zero
    have h2 : (∏ x ∈ s, x ^ e x) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun q hq =>
        pow_ne_zero _ (hmem q (Finset.mem_insert_of_mem hq)).ne_zero
    rw [jacobiSym.mul_right' a h1 h2, jacobiSym.pow_right, dif_pos hℓp,
      ← @jacobiSym.legendreSym.to_jacobiSym ℓ ⟨hℓp⟩ a]
    congr 1
    exact ih (fun q hq => hmem q (Finset.mem_insert_of_mem hq))

private lemma jacobiSym_eq_prod_primeFactors (a : ℤ) {N : ℕ} (hN : N ≠ 0) :
    J(a | N) = ∏ ℓ ∈ N.primeFactors,
      (if h : ℓ.Prime then @legendreSym ℓ ⟨h⟩ a else 1) ^ (N.factorization ℓ) := by
  have hprod : (∏ ℓ ∈ N.primeFactors, ℓ ^ N.factorization ℓ) = N := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hN
  conv_lhs => rw [← hprod]
  exact jacobiSym_finset_prod_pow a N.primeFactors N.factorization
    (fun _ hℓ => Nat.prime_of_mem_primeFactors hℓ)

/-- Quadratic reciprocity bridge: for odd `N` and any prime `p` coprime to `2 * N`,
    `splittingCharInt N p` equals the Legendre symbol `(-2 * N / p)`. -/
theorem splittingCharInt_eq_legendreSym {N p : ℕ} (hN : Odd N) (hp : p.Prime)
    (hcop : Nat.Coprime p (2 * N)) :
    splittingCharInt N (p : ZMod (8 * N)) = @legendreSym p ⟨hp⟩ (-2 * (N : ℤ)) := by
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    have := Nat.Coprime.coprime_mul_right_right hcop
    norm_num at this
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hcop8 : Nat.Coprime p (8 * N) := coprime_eight_mul_iff_coprime_two_mul.mpr hcop
  have hpZ : IsCoprime (p : ℤ) ((8 * N : ℕ) : ℤ) := isCoprime_int_of_coprime hcop8
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hunit : IsUnit (p : ZMod (8 * N)) := (ZMod.isUnit_iff_coprime p (8 * N)).2 hcop8
  have h2part :
      DirichletCharacter.changeLevel (dvd_mul_right 8 N) (twoPartCharInt N) (p : ZMod (8 * N)) =
        twoPartCharInt N (p : ZMod 8) := by
    simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd'
      (twoPartCharInt N) (dvd_mul_right 8 N) hpZ
  rw [splittingCharInt, MulChar.mul_apply, h2part, mulChar_finset_prod_apply _ _ hunit]
  have hprod :
      (∏ ℓ ∈ N.primeFactors, (primeGenusCharInt N ℓ ^ N.factorization ℓ) (p : ZMod (8 * N))) =
        J((p : ℤ) | N) := by
    rw [jacobiSym_eq_prod_primeFactors (p : ℤ) hN0]
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    have hℓp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
    have hℓd : ℓ ∣ N := Nat.dvd_of_mem_primeFactors hℓ
    rw [mulChar_pow_apply _ _ hunit, primeGenusCharInt_apply_of_coprime hℓp hℓd hcop8, dif_pos hℓp]
  rw [hprod]
  have : Fact p.Prime := ⟨hp⟩
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mul_left,
    jacobiSym.quadratic_reciprocity hN hp_odd]
  have h2 := twoPartCharInt_eq_jacobi_sign hN hp_odd
  simpa [mul_assoc] using congrArg (· * J((p : ℤ) | N)) h2

private lemma coprime_of_modEq_coprime {u a m : ℕ} (hmod : u ≡ a [MOD m]) (ha : Nat.Coprime a m) :
    Nat.Coprime u m := by
  have h1 : u.gcd m = (u % m).gcd m := by
    rw [Nat.gcd_comm u m, Nat.gcd_rec m u, Nat.gcd_comm]
  have h2 : a.gcd m = (a % m).gcd m := by
    rw [Nat.gcd_comm a m, Nat.gcd_rec m a, Nat.gcd_comm]
  rw [Nat.Coprime, h1, show u % m = a % m from hmod, ← h2]
  exact ha.gcd_eq_one

/-- For every subset `S : Finset ℕ` (including `S = ∅`), `χ_S * χ_{-8N}` is nontrivial
    modulo `8 * N` whenever `N` is odd. -/
theorem genusChar_mul_splittingChar_ne_one {N : ℕ} (hN : Odd N) (S : Finset ℕ) :
    genusChar N S * splittingChar N ≠ 1 := by
  have hcop8N : Nat.Coprime 8 N := by
    have h2 : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hN
    simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using h2.pow_left 3
  obtain ⟨u, hu8, huN⟩ := Nat.chineseRemainder hcop8N 5 1
  have hu_cop8 : Nat.Coprime u 8 := coprime_of_modEq_coprime hu8 (by norm_num)
  have hu_copN : Nat.Coprime u N := coprime_of_modEq_coprime huN (Nat.coprime_one_left N)
  have hu_cop : Nat.Coprime u (8 * N) := hu_cop8.mul_right hu_copN
  have hu_unit : IsUnit (u : ZMod (8 * N)) := (ZMod.isUnit_iff_coprime u (8 * N)).2 hu_cop
  have huZ : IsCoprime (u : ℤ) ((8 * N : ℕ) : ℤ) := isCoprime_int_of_coprime hu_cop
  have hprime_one : ∀ ℓ : ℕ, primeGenusCharInt N ℓ (u : ZMod (8 * N)) = 1 := by
    intro ℓ
    by_cases h : ℓ.Prime ∧ ℓ ∣ N
    · have : Fact ℓ.Prime := ⟨h.1⟩
      have hdef : primeGenusCharInt N ℓ =
          DirichletCharacter.changeLevel (dvd_mul_of_dvd_right h.2 8) (quadraticChar (ZMod ℓ)) := by
        unfold primeGenusCharInt; rw [dif_pos h]
      rw [hdef]
      have hcl := DirichletCharacter.changeLevel_eq_cast_of_dvd'
        (quadraticChar (ZMod ℓ)) (dvd_mul_of_dvd_right h.2 8) huZ
      have huℓ : (u : ZMod ℓ) = 1 := by
        rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact huN.of_dvd h.2
      have hcl' : DirichletCharacter.changeLevel (dvd_mul_of_dvd_right h.2 8)
          (quadraticChar (ZMod ℓ)) (u : ZMod (8 * N)) = quadraticChar (ZMod ℓ) (u : ZMod ℓ) := by
        simpa using hcl
      rw [hcl', huℓ, map_one]
    · unfold primeGenusCharInt
      rw [dif_neg h]
      exact MulChar.one_apply hu_unit
  have hχS : genusCharInt N S (u : ZMod (8 * N)) = 1 := by
    rw [genusCharInt, mulChar_finset_prod_apply _ _ hu_unit]
    exact Finset.prod_eq_one fun ℓ _ => hprime_one ℓ
  have hsplit : splittingCharInt N (u : ZMod (8 * N)) = -1 := by
    have h2part :
        DirichletCharacter.changeLevel (dvd_mul_right 8 N) (twoPartCharInt N) (u : ZMod (8 * N)) =
          twoPartCharInt N (u : ZMod 8) := by
      simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd'
        (twoPartCharInt N) (dvd_mul_right 8 N) huZ
    rw [splittingCharInt, MulChar.mul_apply, h2part, mulChar_finset_prod_apply _ _ hu_unit]
    have hprod1 : (∏ ℓ ∈ N.primeFactors, (primeGenusCharInt N ℓ ^ N.factorization ℓ) (u : ZMod (8 * N))) = 1 := by
      refine Finset.prod_eq_one fun ℓ _ => ?_
      rw [mulChar_pow_apply _ _ hu_unit, hprime_one ℓ, one_pow]
    have hu5 : (u : ZMod 8) = (5 : ZMod 8) := by
      have h5 : ((u : ℕ) : ZMod 8) = ((5 : ℕ) : ZMod 8) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu8
      simpa using h5
    rw [hprod1, mul_one, hu5, twoPartCharInt_five]
  intro heq
  have hval := congrArg (fun χ : DirichletCharacter ℂ (8 * N) => χ (u : ZMod (8 * N))) heq
  rw [MulChar.mul_apply, genusChar_apply, splittingChar_apply, hχS, hsplit,
    MulChar.one_apply hu_unit] at hval
  norm_num at hval

/-- In particular, the splitting character `χ_{-8N}` itself is nontrivial modulo `8 * N`. -/
theorem splittingChar_ne_one {N : ℕ} (hN : Odd N) : splittingChar N ≠ 1 := by
  have h := genusChar_mul_splittingChar_ne_one hN ∅
  simpa [genusChar, genusCharInt] using h

/-- For every nonempty subset `S ⊆ N.primeFactors`, the genus character `χ_S` is nontrivial
    modulo `8 * N`. -/
theorem genusChar_ne_one {N : ℕ} (hN : Odd N) {S : Finset ℕ}
    (hS : S ⊆ N.primeFactors) (hne : S.Nonempty) :
    genusChar N S ≠ 1 := by
  obtain ⟨ℓ, hℓS⟩ := hne
  have hℓN : ℓ ∈ N.primeFactors := hS hℓS
  have hℓp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓN
  have hℓd : ℓ ∣ N := Nat.dvd_of_mem_primeFactors hℓN
  have hℓ2 : ℓ ≠ 2 := hN.ne_two_of_dvd_nat hℓd
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hchar : ringChar (ZMod ℓ) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hℓ2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod ℓ) hchar
  let k := N.factorization ℓ
  let M := N / ℓ ^ k
  have hkpos : 0 < k := Nat.Prime.factorization_pos_of_dvd hℓp hN.pos.ne' hℓd
  have hpow_dvd : ℓ ^ k ∣ N := Nat.ordProj_dvd N ℓ
  have hN_eq : ℓ ^ k * M = N := Nat.mul_div_cancel' hpow_dvd
  have hcop_ℓM : Nat.Coprime (ℓ ^ k) M := by
    have hnot : ¬ ℓ ∣ M := by
      intro hdvd
      have : ℓ ^ (k + 1) ∣ N := by
        rw [← hN_eq, pow_succ]
        exact mul_dvd_mul_left (ℓ ^ k) hdvd
      have hle := (hℓp.pow_dvd_iff_le_factorization hN.pos.ne').mp this
      omega
    exact (hℓp.coprime_iff_not_dvd.mpr hnot).pow_left k
  have hcop_ℓ8 : Nat.Coprime (ℓ ^ k) 8 := by
    have hcop_ℓ2 : Nat.Coprime ℓ 2 :=
      (Nat.coprime_primes hℓp Nat.prime_two).mpr hℓ2
    simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using (hcop_ℓ2.pow_left k).pow_right 3
  have hcop_split : Nat.Coprime (ℓ ^ k) (8 * M) := hcop_ℓ8.mul_right hcop_ℓM
  obtain ⟨v, hvℓk, hv8M⟩ := Nat.chineseRemainder hcop_split (a : ZMod ℓ).val 1
  have ha_ne : (a : ZMod ℓ) ≠ 0 := by
    intro h0
    have := a.isUnit
    rw [h0] at this
    exact not_isUnit_zero this
  have ha_not_dvd : ¬ ℓ ∣ (a : ZMod ℓ).val := by
    intro hdvd
    apply ha_ne
    rw [← ZMod.natCast_zmod_val (a : ZMod ℓ), ZMod.natCast_eq_zero_iff]
    exact hdvd
  have hv_not_dvd : ¬ ℓ ∣ v := by
    intro hdvd
    apply ha_not_dvd
    have hmod : v ≡ (a : ZMod ℓ).val [MOD ℓ] := hvℓk.of_dvd (dvd_pow_self ℓ hkpos.ne')
    exact (Nat.ModEq.dvd_iff hmod (dvd_refl ℓ)).mp hdvd
  have hv_cop_ℓk : Nat.Coprime v (ℓ ^ k) :=
    (hℓp.coprime_iff_not_dvd.mpr hv_not_dvd).symm.pow_right k
  have hv_cop_8M : Nat.Coprime v (8 * M) :=
    coprime_of_modEq_coprime hv8M (Nat.coprime_one_left (8 * M))
  have hv_cop : Nat.Coprime v (8 * N) := by
    have h8N : 8 * N = ℓ ^ k * (8 * M) := by rw [← hN_eq]; ring
    rw [h8N]
    exact hv_cop_ℓk.mul_right hv_cop_8M
  have hv_unit : IsUnit (v : ZMod (8 * N)) := (ZMod.isUnit_iff_coprime v (8 * N)).2 hv_cop
  have hvZ : IsCoprime (v : ℤ) ((8 * N : ℕ) : ℤ) := isCoprime_int_of_coprime hv_cop
  have hv_at_ℓ : primeGenusCharInt N ℓ (v : ZMod (8 * N)) = -1 := by
    have hdef : primeGenusCharInt N ℓ =
        DirichletCharacter.changeLevel (dvd_mul_of_dvd_right hℓd 8) (quadraticChar (ZMod ℓ)) := by
      unfold primeGenusCharInt; rw [dif_pos ⟨hℓp, hℓd⟩]
    rw [hdef]
    have hcl : DirichletCharacter.changeLevel (dvd_mul_of_dvd_right hℓd 8)
        (quadraticChar (ZMod ℓ)) (v : ZMod (8 * N)) = quadraticChar (ZMod ℓ) (v : ZMod ℓ) := by
      simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd'
        (quadraticChar (ZMod ℓ)) (dvd_mul_of_dvd_right hℓd 8) hvZ
    have hmod : v ≡ (a : ZMod ℓ).val [MOD ℓ] := hvℓk.of_dvd (dvd_pow_self ℓ hkpos.ne')
    have hv_eq : (v : ZMod ℓ) = (a : ZMod ℓ) := by
      have : (v : ZMod ℓ) = ((a : ZMod ℓ).val : ZMod ℓ) :=
        (ZMod.natCast_eq_natCast_iff v (a : ZMod ℓ).val ℓ).mpr hmod
      simpa [ZMod.natCast_zmod_val] using this
    rw [hcl, hv_eq]
    exact ha
  have hv_other : ∀ q ∈ S, q ≠ ℓ → primeGenusCharInt N q (v : ZMod (8 * N)) = 1 := by
    intro q hqS hqne
    have hqN : q ∈ N.primeFactors := hS hqS
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqN
    have hqd : q ∣ N := Nat.dvd_of_mem_primeFactors hqN
    have : Fact q.Prime := ⟨hqp⟩
    have hq_cop : Nat.Coprime q (ℓ ^ k) :=
      ((Nat.coprime_primes hqp hℓp).mpr hqne).pow_right k
    have hqM : q ∣ M := hq_cop.dvd_of_dvd_mul_left (hN_eq.symm ▸ hqd)
    have hq8M : q ∣ 8 * M := dvd_mul_of_dvd_right hqM 8
    have hdef : primeGenusCharInt N q =
        DirichletCharacter.changeLevel (dvd_mul_of_dvd_right hqd 8) (quadraticChar (ZMod q)) := by
      unfold primeGenusCharInt; rw [dif_pos ⟨hqp, hqd⟩]
    rw [hdef]
    have hcl : DirichletCharacter.changeLevel (dvd_mul_of_dvd_right hqd 8)
        (quadraticChar (ZMod q)) (v : ZMod (8 * N)) = quadraticChar (ZMod q) (v : ZMod q) := by
      simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd'
        (quadraticChar (ZMod q)) (dvd_mul_of_dvd_right hqd 8) hvZ
    have hvq : (v : ZMod q) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hv8M.of_dvd hq8M
    rw [hcl, hvq, map_one]
  have hχS_val : genusCharInt N S (v : ZMod (8 * N)) = -1 := by
    rw [genusCharInt, mulChar_finset_prod_apply S _ hv_unit,
      ← Finset.mul_prod_erase S _ hℓS, hv_at_ℓ]
    have hrest : (∏ q ∈ S.erase ℓ, primeGenusCharInt N q (v : ZMod (8 * N))) = 1 :=
      Finset.prod_eq_one fun q hq => hv_other q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)
    rw [hrest, mul_one]
  intro heq
  have hval := congrArg (fun χ : DirichletCharacter ℂ (8 * N) => χ (v : ZMod (8 * N))) heq
  rw [genusChar_apply, hχS_val, MulChar.one_apply hv_unit] at hval
  norm_num at hval

/-!
## Section 2: Split-prime band supply and genus-character bias under Dirichlet GRH
-/

/-- Primes in `(A, B]` coprime to `8 * N` (equivalently, coprime to `2 * N`). -/
def coprimePrimeBin (N A B : ℕ) : Finset ℕ :=
  (Cogentic.Randomized.primeBin A B).filter (fun p => Nat.Coprime p (8 * N))

/-- Primes in `(A, B]` coprime to `2 * N` that split in `ℚ(√(-2N))` (`χ_{-8N}(p) = 1`). -/
noncomputable def splitPrimeBin (N A B : ℕ) : Finset ℕ :=
  (Cogentic.Randomized.primeBin A B).filter (fun p => splittingCharInt N (p : ZMod (8 * N)) = 1)

lemma splitPrimeBin_subset_coprimePrimeBin (N A B : ℕ) [NeZero (8 * N)] :
    splitPrimeBin N A B ⊆ coprimePrimeBin N A B := by
  intro p hp
  simp only [splitPrimeBin, coprimePrimeBin, Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  by_contra hncop
  have hnu : ¬ IsUnit (p : ZMod (8 * N)) := by
    rwa [ZMod.isUnit_iff_coprime]
  have h0 := (splittingCharInt N).map_nonunit hnu
  rw [h0] at hp
  exact zero_ne_one hp.2

lemma mem_splitPrimeBin_iff {N A B p : ℕ} (hN : Odd N) :
    p ∈ splitPrimeBin N A B ↔
      ∃ hp : p ∈ Cogentic.Randomized.primeBin A B,
        Nat.Coprime p (2 * N) ∧
          @legendreSym p ⟨(Finset.mem_filter.mp hp).2⟩ (-2 * (N : ℤ)) = 1 := by
  have : NeZero (8 * N) := ⟨by positivity [hN.pos]⟩
  constructor
  · intro hp
    have hcop8 := (Finset.mem_filter.mp (splitPrimeBin_subset_coprimePrimeBin N A B hp)).2
    have hcop2 := coprime_eight_mul_iff_coprime_two_mul.mp hcop8
    have hbin := (Finset.mem_filter.mp hp).1
    have hprime := (Finset.mem_filter.mp hbin).2
    have hval := (Finset.mem_filter.mp hp).2
    rw [splittingCharInt_eq_legendreSym hN hprime hcop2] at hval
    exact ⟨hbin, hcop2, hval⟩
  · rintro ⟨hbin, hcop2, hleg⟩
    have hprime := (Finset.mem_filter.mp hbin).2
    simp only [splitPrimeBin, Finset.mem_filter]
    exact ⟨hbin, by rw [splittingCharInt_eq_legendreSym hN hprime hcop2]; exact hleg⟩

private lemma primeBin_sum_eq_primeCount_sub {q A B : ℕ} (χ : DirichletCharacter ℂ q) (hAB : A ≤ B) :
    (∑ p ∈ Cogentic.Randomized.primeBin A B, χ (p : ZMod q)) =
      Cogentic.Window.primeCount χ B - Cogentic.Window.primeCount χ A := by
  have hdisj : Disjoint (Icc 0 A) (Ioc A B) := Finset.disjoint_left.mpr fun p hp hq =>
    (not_lt_of_ge (mem_Icc.mp hp).2) (mem_Ioc.mp hq).1
  have hunion : Icc 0 A ∪ Ioc A B = Icc 0 B := by
    ext p
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  unfold Cogentic.Randomized.primeBin Cogentic.Window.primeCount
  simp only [Nat.floor_natCast, sum_filter]
  rw [← hunion, sum_union hdisj, add_sub_cancel_left]

/-- Exact identity relating the split-prime count to the coprime-prime count and `∑ χ_{-8N}(p)`. -/
theorem two_mul_splitPrimeBin_card (N A B : ℕ) [NeZero (8 * N)] :
    2 * ((splitPrimeBin N A B).card : ℝ) =
      ((coprimePrimeBin N A B).card : ℝ) +
        (∑ p ∈ Cogentic.Randomized.primeBin A B, splittingChar N (p : ZMod (8 * N))).re := by
  have hsum :
      (∑ p ∈ Cogentic.Randomized.primeBin A B, splittingChar N (p : ZMod (8 * N))).re =
        ∑ p ∈ coprimePrimeBin N A B, (splittingCharInt N (p : ZMod (8 * N)) : ℝ) := by
    rw [Complex.re_sum]
    have hfilter :
        ∑ p ∈ Cogentic.Randomized.primeBin A B, (splittingChar N (p : ZMod (8 * N))).re =
          ∑ p ∈ coprimePrimeBin N A B, (splittingChar N (p : ZMod (8 * N))).re := by
      rw [coprimePrimeBin, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : Nat.Coprime p (8 * N)
      · simp [hc]
      · have hnu : ¬ IsUnit (p : ZMod (8 * N)) := by rwa [ZMod.isUnit_iff_coprime]
        simp [hc, MulChar.map_nonunit _ hnu]
    rw [hfilter]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [splittingChar_apply]
  rw [hsum]
  have hcard :
      ((coprimePrimeBin N A B).card : ℝ) +
        ∑ p ∈ coprimePrimeBin N A B, (splittingCharInt N (p : ZMod (8 * N)) : ℝ) =
      ∑ p ∈ coprimePrimeBin N A B, (1 + (splittingCharInt N (p : ZMod (8 * N)) : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard]
  have hsplit_eq :
      splitPrimeBin N A B =
        (coprimePrimeBin N A B).filter (fun p : ℕ => splittingCharInt N (p : ZMod (8 * N)) = 1) := by
    ext p
    simp only [splitPrimeBin, coprimePrimeBin, Finset.mem_filter]
    constructor
    · intro hp
      have hsub := splitPrimeBin_subset_coprimePrimeBin N A B (Finset.mem_filter.mpr hp)
      exact ⟨⟨hp.1, (Finset.mem_filter.mp hsub).2⟩, hp.2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [hsplit_eq, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hunit : IsUnit (p : ZMod (8 * N)) :=
    (ZMod.isUnit_iff_coprime p (8 * N)).2 (Finset.mem_filter.mp hp).2
  rcases splittingCharInt_eq_one_or_neg_one hunit with h1 | hm1
  · simp [h1]; norm_num
  · simp [hm1]

/-- Exact character-sum identity on split primes: averaging `χ_S` over `splitPrimeBin`
    equals half the sum of `χ_S` and `χ_S * χ_{-8N}` over the full `primeBin`, with zero
    exceptional prime error. -/
theorem two_mul_splitPrimeBin_genus_sum (N A B : ℕ) [NeZero (8 * N)] (S : Finset ℕ) :
    2 * (∑ p ∈ splitPrimeBin N A B, genusChar N S (p : ZMod (8 * N))) =
      (∑ p ∈ Cogentic.Randomized.primeBin A B, genusChar N S (p : ZMod (8 * N))) +
        (∑ p ∈ Cogentic.Randomized.primeBin A B,
          (genusChar N S * splittingChar N) (p : ZMod (8 * N))) := by
  rw [← Finset.sum_add_distrib, splitPrimeBin, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hc : IsUnit (p : ZMod (8 * N))
  · rcases splittingCharInt_eq_one_or_neg_one hc with h1 | hm1
    · simp [h1, MulChar.mul_apply, splittingChar_apply]; ring
    · simp [hm1, MulChar.mul_apply, splittingChar_apply]
  · have hs0 : splittingCharInt N (p : ZMod (8 * N)) = 0 := MulChar.map_nonunit _ hc
    simp [hs0, MulChar.map_nonunit _ hc]

private lemma card_sdiff_coprimePrimeBin_le (N A B : ℕ) (hA : 2 ≤ A) (hN : 1 ≤ N) :
    ((Cogentic.Randomized.primeBin A B \ coprimePrimeBin N A B).card : ℝ) ≤
      Real.log N / Real.log 2 := by
  have hsub : Cogentic.Randomized.primeBin A B \ coprimePrimeBin N A B ⊆ N.primeFactors := by
    intro p hp
    simp only [Finset.mem_sdiff, coprimePrimeBin, Finset.mem_filter, Cogentic.Randomized.primeBin,
      Finset.mem_Ioc] at hp
    have hp_prime : p.Prime := hp.1.2
    have hp_gt2 : 2 < p := lt_of_le_of_lt hA hp.1.1.1
    have hncop : ¬ Nat.Coprime p (8 * N) := fun hc => hp.2 ⟨hp.1, hc⟩
    have hdvd8N : p ∣ 8 * N := (hp_prime.coprime_iff_not_dvd.not.mp hncop |> not_not.mp)
    have hcop8 : Nat.Coprime p 8 := by
      have hp2 : Nat.Coprime p 2 := (Nat.coprime_primes hp_prime Nat.prime_two).mpr (by omega)
      simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hp2.pow_right 3
    have hdvdN : p ∣ N := hcop8.dvd_of_dvd_mul_left hdvd8N
    exact Nat.mem_primeFactors.mpr ⟨hp_prime, hdvdN, by omega⟩
  have hcard_le : (Cogentic.Randomized.primeBin A B \ coprimePrimeBin N A B).card ≤ N.primeFactors.card :=
    Finset.card_le_card hsub
  have hpow : 2 ^ N.primeFactors.card ≤ N := by
    calc
      2 ^ N.primeFactors.card = ∏ _p ∈ N.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ N.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ N := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowR : (2 : ℝ) ^ N.primeFactors.card ≤ (N : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow] at hlog
  have h1 : (N.primeFactors.card : ℝ) ≤ Real.log N / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr hlog
  exact (Nat.cast_le.mpr hcard_le).trans h1

private lemma log_48_le_const_mul {N P : ℕ} (hN : 3 ≤ N) (hP : 2 ≤ P) :
    1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ)) ≤
      (1 + Real.log 48) * (1 + Real.log ((N : ℝ) * P)) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hNP : (1 : ℝ) ≤ (N : ℝ) * P := by nlinarith
  have hlogNP : 0 ≤ Real.log ((N : ℝ) * P) := Real.log_nonneg hNP
  have h48 : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
  have hmul : 3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ) = 48 * ((N : ℝ) * P) := by
    push_cast; ring
  rw [hmul, Real.log_mul (by norm_num) (by positivity)]
  nlinarith

private lemma nonprincipal_dyadic_sum_bound (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N P : ℕ) [NeZero (8 * N)], 3 ≤ N → 2 ≤ P →
      ∀ (χ : DirichletCharacter ℂ (8 * N)), χ ≠ 1 →
        ‖∑ p ∈ Cogentic.Randomized.primeBin P (2 * P), χ (p : ZMod (8 * N))‖ ≤
          K * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
  obtain ⟨K₀, hK₀, hbound⟩ := Cogentic.Window.nonprincipal_prime_count_from_critical_line line
  refine ⟨2 * K₀ * Real.sqrt 2 * (1 + Real.log 48) ^ 2, by positivity, ?_⟩
  intro N P _ hN hP χ hχ
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have h2Pr : (P : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by push_cast; linarith
  have hA := hbound (8 * N) χ hχ (2 * P : ℕ) P hPr h2Pr
  have hB := hbound (8 * N) χ hχ (2 * P : ℕ) (2 * P : ℕ) (hPr.trans h2Pr) le_rfl
  rw [← Real.sqrt_eq_rpow] at hA hB
  rw [primeBin_sum_eq_primeCount_sub χ (by omega : P ≤ 2 * P)]
  have hDpos : 0 ≤ 1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ)) := by
    have : (1 : ℝ) ≤ 3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ) := by
      have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
      push_cast; nlinarith
    linarith [Real.log_nonneg this]
  have hDle := log_48_le_const_mul hN hP
  have hDsq : (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ))) ^ 2 ≤
      (1 + Real.log 48) ^ 2 * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
    calc
      _ ≤ ((1 + Real.log 48) * (1 + Real.log ((N : ℝ) * P))) ^ 2 :=
        pow_le_pow_left₀ hDpos hDle 2
      _ = _ := by ring
  have hsqrt : Real.sqrt ((2 * P : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt P := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
  calc
    ‖Cogentic.Window.primeCount χ (2 * P : ℕ) - Cogentic.Window.primeCount χ P‖
        ≤ ‖Cogentic.Window.primeCount χ (2 * P : ℕ)‖ + ‖Cogentic.Window.primeCount χ P‖ :=
      norm_sub_le _ _
    _ ≤ (K₀ * (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ))) ^ 2) *
          Real.sqrt ((2 * P : ℕ) : ℝ) +
        (K₀ * (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ))) ^ 2) *
          Real.sqrt P := add_le_add hB hA
    _ ≤ (K₀ * (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ))) ^ 2) *
          Real.sqrt ((2 * P : ℕ) : ℝ) +
        (K₀ * (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ))) ^ 2) *
          Real.sqrt ((2 * P : ℕ) : ℝ) := by
      gcongr
    _ = 2 * K₀ * Real.sqrt 2 * Real.sqrt P *
          (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * ((2 * P : ℕ) : ℝ))) ^ 2 := by
      rw [hsqrt]; ring
    _ ≤ 2 * K₀ * Real.sqrt 2 * Real.sqrt P *
          ((1 + Real.log 48) ^ 2 * (1 + Real.log ((N : ℝ) * P)) ^ 2) := by
      gcongr
    _ = _ := by ring

/-- Under Dirichlet GRH, the number of split primes in `(P, 2P]` coprime to `2 * N`
    equals `(1/2) * |primes in (P, 2P]| + O(sqrt(P) * (1 + log(N * P))^2)`. -/
theorem splitPrimeBin_card_approx_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N P : ℕ), Odd N → 3 ≤ N → 2 ≤ P →
      |((splitPrimeBin N P (2 * P)).card : ℝ) -
          (1 / 2 : ℝ) * ((Cogentic.Randomized.primeBin P (2 * P)).card : ℝ)| ≤
        C * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
  obtain ⟨K, hK, hsum⟩ := nonprincipal_dyadic_sum_bound line
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K / 2 + (2 * Real.log 2)⁻¹, by positivity, fun N P hNodd hN hP => ?_⟩
  have : NeZero (8 * N) := ⟨by omega⟩
  have hcard := two_mul_splitPrimeBin_card N P (2 * P)
  have hsub : coprimePrimeBin N P (2 * P) ⊆ Cogentic.Randomized.primeBin P (2 * P) :=
    Finset.filter_subset _ _
  have hdiff_card :
      ((coprimePrimeBin N P (2 * P)).card : ℝ) =
        ((Cogentic.Randomized.primeBin P (2 * P)).card : ℝ) -
          ((Cogentic.Randomized.primeBin P (2 * P) \ coprimePrimeBin N P (2 * P)).card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    have hR : ((Cogentic.Randomized.primeBin P (2 * P) \ coprimePrimeBin N P (2 * P)).card : ℝ) +
        ((coprimePrimeBin N P (2 * P)).card : ℝ) =
        ((Cogentic.Randomized.primeBin P (2 * P)).card : ℝ) := by exact_mod_cast h
    linarith
  have heq :
      ((splitPrimeBin N P (2 * P)).card : ℝ) -
        (1 / 2 : ℝ) * ((Cogentic.Randomized.primeBin P (2 * P)).card : ℝ) =
      (1 / 2 : ℝ) * ((∑ p ∈ Cogentic.Randomized.primeBin P (2 * P),
          splittingChar N (p : ZMod (8 * N))).re -
        ((Cogentic.Randomized.primeBin P (2 * P) \ coprimePrimeBin N P (2 * P)).card : ℝ)) := by
    linarith
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]
  have hre :
      |(∑ p ∈ Cogentic.Randomized.primeBin P (2 * P),
          splittingChar N (p : ZMod (8 * N))).re| ≤
        K * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 :=
    (Complex.abs_re_le_norm _).trans (hsum N P hN hP (splittingChar N) (splittingChar_ne_one hNodd))
  have hbad := card_sdiff_coprimePrimeBin_le N P (2 * P) hP (by omega)
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hlogNP : 0 ≤ Real.log ((N : ℝ) * P) := Real.log_nonneg (by nlinarith)
  have hlogN_le : Real.log N ≤ 1 + Real.log ((N : ℝ) * P) := by
    have := Real.log_le_log (by linarith) (show (N : ℝ) ≤ (N : ℝ) * P by nlinarith)
    linarith
  have hD1 : 1 ≤ 1 + Real.log ((N : ℝ) * P) := by linarith
  have hDsq : 1 + Real.log ((N : ℝ) * P) ≤ (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
    nlinarith [sq_nonneg ((1 + Real.log ((N : ℝ) * P)) - 1)]
  have hsqrt1 : 1 ≤ Real.sqrt P := Real.one_le_sqrt.mpr (by linarith)
  have hbad' :
      ((Cogentic.Randomized.primeBin P (2 * P) \ coprimePrimeBin N P (2 * P)).card : ℝ) ≤
        (Real.log 2)⁻¹ * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
    calc
      _ ≤ Real.log N / Real.log 2 := hbad
      _ = (Real.log 2)⁻¹ * Real.log N := by ring
      _ ≤ (Real.log 2)⁻¹ * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
        gcongr
        exact hlogN_le.trans hDsq
      _ ≤ (Real.log 2)⁻¹ * (Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2) := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hsqrt1
      _ = _ := by ring
  have htri :
      |(∑ p ∈ Cogentic.Randomized.primeBin P (2 * P),
          splittingChar N (p : ZMod (8 * N))).re -
        ((Cogentic.Randomized.primeBin P (2 * P) \ coprimePrimeBin N P (2 * P)).card : ℝ)| ≤
        |(∑ p ∈ Cogentic.Randomized.primeBin P (2 * P),
            splittingChar N (p : ZMod (8 * N))).re| +
          ((Cogentic.Randomized.primeBin P (2 * P) \ coprimePrimeBin N P (2 * P)).card : ℝ) := by
    calc
      _ ≤ |(∑ p ∈ Cogentic.Randomized.primeBin P (2 * P),
              splittingChar N (p : ZMod (8 * N))).re| +
            |((Cogentic.Randomized.primeBin P (2 * P) \ coprimePrimeBin N P (2 * P)).card : ℝ)| :=
        abs_sub _ _
      _ = _ := by rw [Nat.abs_cast]
  calc
    (1 / 2 : ℝ) * _ ≤ (1 / 2 : ℝ) * (K * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 +
        (Real.log 2)⁻¹ * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2) := by
      gcongr
      exact htri.trans (add_le_add hre hbad')
    _ = (K / 2 + (2 * Real.log 2)⁻¹) * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
      ring

/-- Under Dirichlet GRH, the split-prime band `(P, 2P]` has at least
    `P / (2 * log(2P)) - O(sqrt(P) * (1 + log(N * P))^2)` primes. -/
theorem splitPrimeBin_card_lower_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N P : ℕ), Odd N → 3 ≤ N → 2 ≤ P →
      (P : ℝ) / (2 * Real.log (2 * (P : ℝ))) -
          C * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 ≤
        ((splitPrimeBin N P (2 * P)).card : ℝ) := by
  obtain ⟨K₀, hK₀, hsup⟩ := Cogentic.Randomized.primeBin_supply_from_critical_line line
  obtain ⟨C₁, hC₁, hsplit⟩ := splitPrimeBin_card_approx_from_critical_line line
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨C₁ + K₀ * Real.sqrt 2 * (1 + Real.log 6) ^ 2 / (2 * Real.log 4), by positivity,
    fun N P hNodd hN hP => ?_⟩
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hlog2P_ge : Real.log 4 ≤ Real.log (2 * (P : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog2P_pos : 0 < Real.log (2 * (P : ℝ)) := hlog4.trans_le hlog2P_ge
  have hbin := hsup P (2 * P) hP (by omega)
  have hbin_cast :
      (P : ℝ) - K₀ * (1 + Real.log (6 * (P : ℝ))) ^ 2 * Real.sqrt (2 * (P : ℝ)) ≤
        ((Cogentic.Randomized.primeBin P (2 * P)).card : ℝ) * Real.log (2 * (P : ℝ)) := by
    have : ((2 * P : ℕ) : ℝ) = 2 * (P : ℝ) := by push_cast; ring
    rw [this] at hbin
    have h6 : 3 * (2 * (P : ℝ)) = 6 * (P : ℝ) := by ring
    rw [h6] at hbin
    linarith
  have hbin_div :
      (P : ℝ) / Real.log (2 * (P : ℝ)) -
          K₀ * (1 + Real.log (6 * (P : ℝ))) ^ 2 * Real.sqrt (2 * (P : ℝ)) / Real.log (2 * (P : ℝ)) ≤
        ((Cogentic.Randomized.primeBin P (2 * P)).card : ℝ) := by
    rw [← sub_div]
    exact (div_le_iff₀ hlog2P_pos).mpr hbin_cast
  have hlog6 : 1 + Real.log (6 * (P : ℝ)) ≤ (1 + Real.log 6) * (1 + Real.log ((N : ℝ) * P)) := by
    have hP_le : (P : ℝ) ≤ (N : ℝ) * P := by nlinarith
    have hlogP_le : Real.log P ≤ Real.log ((N : ℝ) * P) := Real.log_le_log (by linarith) hP_le
    have hlogNP : 0 ≤ Real.log ((N : ℝ) * P) := Real.log_nonneg (by nlinarith)
    have h6nn : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    rw [Real.log_mul (by norm_num) (by linarith)]
    nlinarith
  have hlog6_nn : 0 ≤ 1 + Real.log (6 * (P : ℝ)) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ 6 * (P : ℝ) by linarith)]
  have hlog6_sq :
      (1 + Real.log (6 * (P : ℝ))) ^ 2 ≤
        (1 + Real.log 6) ^ 2 * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
    calc
      _ ≤ ((1 + Real.log 6) * (1 + Real.log ((N : ℝ) * P))) ^ 2 :=
        pow_le_pow_left₀ hlog6_nn hlog6 2
      _ = _ := by ring
  have herr_bin :
      K₀ * (1 + Real.log (6 * (P : ℝ))) ^ 2 * Real.sqrt (2 * (P : ℝ)) / Real.log (2 * (P : ℝ)) ≤
        K₀ * Real.sqrt 2 * (1 + Real.log 6) ^ 2 / Real.log 4 *
          Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
    rw [Real.sqrt_mul (by norm_num)]
    calc
      _ ≤ K₀ * ((1 + Real.log 6) ^ 2 * (1 + Real.log ((N : ℝ) * P)) ^ 2) *
            (Real.sqrt 2 * Real.sqrt P) / Real.log 4 := by
        gcongr
      _ = _ := by ring
  have hsp := (abs_le.mp (hsplit N P hNodd hN hP)).1
  have hhalf :
      (P : ℝ) / (2 * Real.log (2 * (P : ℝ))) -
          K₀ * Real.sqrt 2 * (1 + Real.log 6) ^ 2 / (2 * Real.log 4) *
            Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 ≤
        (1 / 2 : ℝ) * ((Cogentic.Randomized.primeBin P (2 * P)).card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hbin_div (by positivity : (0 : ℝ) ≤ 1 / 2)
    have h2 :
        (1 / 2 : ℝ) *
            (K₀ * (1 + Real.log (6 * (P : ℝ))) ^ 2 * Real.sqrt (2 * (P : ℝ)) /
              Real.log (2 * (P : ℝ))) ≤
          K₀ * Real.sqrt 2 * (1 + Real.log 6) ^ 2 / (2 * Real.log 4) *
            Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
      calc
        _ ≤ (1 / 2 : ℝ) * (K₀ * Real.sqrt 2 * (1 + Real.log 6) ^ 2 / Real.log 4 *
              Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2) := by
          gcongr
        _ = _ := by ring
    have h3 : (1 / 2 : ℝ) * ((P : ℝ) / Real.log (2 * (P : ℝ))) =
        (P : ℝ) / (2 * Real.log (2 * (P : ℝ))) := by ring
    linarith
  linarith

/-- Under Dirichlet GRH, the unnormalized genus-character sum over split primes in `(P, 2P]`
    is `O(sqrt(P) * (1 + log(N * P))^2)` uniformly over all nonempty `S ⊆ N.primeFactors`. -/
theorem splitPrimeBin_genus_sum_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N P : ℕ), Odd N → 3 ≤ N → 2 ≤ P →
      ∀ S ⊆ N.primeFactors, S.Nonempty →
        |∑ p ∈ splitPrimeBin N P (2 * P), genusCharReal N S (p : ZMod (8 * N))| ≤
          C * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
  obtain ⟨K, hK, hsum⟩ := nonprincipal_dyadic_sum_bound line
  refine ⟨K, hK, fun N P hNodd hN hP S hS hne => ?_⟩
  have : NeZero (8 * N) := ⟨by omega⟩
  have h1 := hsum N P hN hP (genusChar N S) (genusChar_ne_one hNodd hS hne)
  have h2 := hsum N P hN hP (genusChar N S * splittingChar N) (genusChar_mul_splittingChar_ne_one hNodd S)
  have hid := two_mul_splitPrimeBin_genus_sum N P (2 * P) S
  have hcast :
      ‖∑ p ∈ splitPrimeBin N P (2 * P), genusChar N S (p : ZMod (8 * N))‖ =
        |∑ p ∈ splitPrimeBin N P (2 * P), genusCharReal N S (p : ZMod (8 * N))| := by
    have heq :
        (∑ p ∈ splitPrimeBin N P (2 * P), genusChar N S (p : ZMod (8 * N))) =
          ((∑ p ∈ splitPrimeBin N P (2 * P), genusCharReal N S (p : ZMod (8 * N)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => genusChar_eq_ofReal_genusCharReal N S _
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have h2norm :
      2 * ‖∑ p ∈ splitPrimeBin N P (2 * P), genusChar N S (p : ZMod (8 * N))‖ ≤
        2 * (K * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2) := by
    calc
      2 * ‖∑ p ∈ splitPrimeBin N P (2 * P), genusChar N S (p : ZMod (8 * N))‖
          = ‖(2 : ℂ) * ∑ p ∈ splitPrimeBin N P (2 * P), genusChar N S (p : ZMod (8 * N))‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      _ = ‖(∑ p ∈ Cogentic.Randomized.primeBin P (2 * P), genusChar N S (p : ZMod (8 * N))) +
            (∑ p ∈ Cogentic.Randomized.primeBin P (2 * P),
              (genusChar N S * splittingChar N) (p : ZMod (8 * N)))‖ := by rw [hid]
      _ ≤ ‖∑ p ∈ Cogentic.Randomized.primeBin P (2 * P), genusChar N S (p : ZMod (8 * N))‖ +
            ‖∑ p ∈ Cogentic.Randomized.primeBin P (2 * P),
              (genusChar N S * splittingChar N) (p : ZMod (8 * N))‖ := norm_add_le _ _
      _ ≤ K * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 +
            K * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 := add_le_add h1 h2
      _ = _ := by ring
  rw [← hcast]
  linarith

/-- Under Dirichlet GRH, for any dyadic split-prime band `(P, 2P]` above the polylog threshold
    `C_thresh * (1 + log(N * P))^3 ≤ sqrt(P)`, the band size is at least `P / (4 * log(2P))`
    and the normalized average of every nontrivial genus character `χ_S` is bounded by
    `C_bias * P^(-1/2) * (1 + log(N * P))^3`. -/
theorem splitPrimeBin_genus_bias_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C_thresh C_bias : ℝ, 0 ≤ C_thresh ∧ 0 ≤ C_bias ∧
      ∀ (N P : ℕ), Odd N → 3 ≤ N → 2 ≤ P →
        C_thresh * (1 + Real.log ((N : ℝ) * P)) ^ 3 ≤ Real.sqrt P →
          (P : ℝ) / (4 * Real.log (2 * (P : ℝ))) ≤ ((splitPrimeBin N P (2 * P)).card : ℝ) ∧
          ∀ S ⊆ N.primeFactors, S.Nonempty →
            |(∑ p ∈ splitPrimeBin N P (2 * P), genusCharReal N S (p : ZMod (8 * N))) /
                ((splitPrimeBin N P (2 * P)).card : ℝ)| ≤
              C_bias * (P : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log ((N : ℝ) * P)) ^ 3 := by
  obtain ⟨C_low, hC_low, hlower⟩ := splitPrimeBin_card_lower_from_critical_line line
  obtain ⟨C_sum, hC_sum, hsum⟩ := splitPrimeBin_genus_sum_from_critical_line line
  let C_log : ℝ := 1 + Real.log 2
  have hC_log : 0 < C_log := by dsimp [C_log]; linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  refine ⟨4 * C_low * C_log, 4 * C_sum * C_log, by positivity, by positivity, ?_⟩
  intro N P hNodd hN hP hthresh
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hlog2P_pos : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by linarith)
  have hlog2P_le : Real.log (2 * (P : ℝ)) ≤ C_log * (1 + Real.log ((N : ℝ) * P)) := by
    have hP_le : (P : ℝ) ≤ (N : ℝ) * P := by nlinarith
    have hlogP_le : Real.log P ≤ Real.log ((N : ℝ) * P) := Real.log_le_log hPpos hP_le
    have hlogNP : 0 ≤ Real.log ((N : ℝ) * P) := Real.log_nonneg (by nlinarith)
    have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [Real.log_mul (by norm_num) hPpos.ne']
    dsimp [C_log]
    nlinarith
  have hcard_main :
      (P : ℝ) / (4 * Real.log (2 * (P : ℝ))) ≤ ((splitPrimeBin N P (2 * P)).card : ℝ) := by
    have hlow := hlower N P hNodd hN hP
    have herr_le :
        C_low * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 ≤
          (P : ℝ) / (4 * Real.log (2 * (P : ℝ))) := by
      rw [le_div_iff₀ (by positivity)]
      have hmul :
          C_low * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 * (4 * Real.log (2 * (P : ℝ))) ≤
            (4 * C_low * C_log * (1 + Real.log ((N : ℝ) * P)) ^ 3) * Real.sqrt P := by
        calc
          _ ≤ C_low * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2 *
                (4 * (C_log * (1 + Real.log ((N : ℝ) * P)))) := by gcongr
          _ = _ := by ring
      calc
        _ ≤ (4 * C_low * C_log * (1 + Real.log ((N : ℝ) * P)) ^ 3) * Real.sqrt P := hmul
        _ ≤ Real.sqrt P * Real.sqrt P :=
          mul_le_mul_of_nonneg_right hthresh (Real.sqrt_nonneg _)
        _ = (P : ℝ) := Real.mul_self_sqrt hPpos.le
    have hq : (P : ℝ) / (2 * Real.log (2 * (P : ℝ))) - (P : ℝ) / (4 * Real.log (2 * (P : ℝ))) =
        (P : ℝ) / (4 * Real.log (2 * (P : ℝ))) := by ring
    linarith
  refine ⟨hcard_main, fun S hS hne => ?_⟩
  have hcard_pos : 0 < ((splitPrimeBin N P (2 * P)).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hcard_main
  rw [abs_div, abs_of_pos hcard_pos]
  have hnum := hsum N P hNodd hN hP S hS hne
  have hrpow : Real.sqrt P / (P : ℝ) = (P : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one (P : ℝ), ← Real.rpow_add hPpos]
    norm_num
  calc
    |∑ p ∈ splitPrimeBin N P (2 * P), genusCharReal N S (p : ZMod (8 * N))| /
        ((splitPrimeBin N P (2 * P)).card : ℝ)
      ≤ (C_sum * Real.sqrt P * (1 + Real.log ((N : ℝ) * P)) ^ 2) /
          ((P : ℝ) / (4 * Real.log (2 * (P : ℝ)))) := by
        exact div_le_div₀ (by positivity) hnum (by positivity) hcard_main
    _ = 4 * C_sum * (Real.sqrt P / (P : ℝ)) * Real.log (2 * (P : ℝ)) *
          (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
        field_simp [hPpos.ne', hlog2P_pos.ne']
    _ ≤ 4 * C_sum * (Real.sqrt P / (P : ℝ)) * (C_log * (1 + Real.log ((N : ℝ) * P))) *
          (1 + Real.log ((N : ℝ) * P)) ^ 2 := by
        gcongr
    _ = (4 * C_sum * C_log) * (P : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log ((N : ℝ) * P)) ^ 3 := by
        rw [hrpow]; ring

/-- Deleting an exceptional subset `E ⊆ B` of relative size `≤ ε < 1` increases the normalized
    character bias of any `[-1, 1]`-bounded function from `≤ δ` to at most `(δ + ε) / (1 - ε)`. -/
theorem average_bias_after_deletion {α : Type*} [DecidableEq α]
    (B E : Finset α) (f : α → ℝ) {δ ε : ℝ}
    (hEB : E ⊆ B) (hBne : B.Nonempty) (hf : ∀ x ∈ B, |f x| ≤ 1)
    (hbias : |(∑ x ∈ B, f x) / (B.card : ℝ)| ≤ δ)
    (hE : (E.card : ℝ) ≤ ε * (B.card : ℝ)) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (1 - ε) * (B.card : ℝ) ≤ ((B \ E).card : ℝ) ∧
    (B \ E).Nonempty ∧
    |(∑ x ∈ B \ E, f x) / ((B \ E).card : ℝ)| ≤ (δ + ε) / (1 - ε) := by
  have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.mpr hBne.card_pos
  have hcard_eq : ((B \ E).card : ℝ) + (E.card : ℝ) = (B.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hEB
  have hrem_ge : (1 - ε) * (B.card : ℝ) ≤ ((B \ E).card : ℝ) := by nlinarith
  have hrem_pos : (0 : ℝ) < ((B \ E).card : ℝ) :=
    lt_of_lt_of_le (mul_pos (by linarith) hBpos) hrem_ge
  have hrem_ne : (B \ E).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hrem_pos)
  refine ⟨hrem_ge, hrem_ne, ?_⟩
  rw [abs_div, abs_of_pos hBpos] at hbias
  have hBsum : |∑ x ∈ B, f x| ≤ δ * (B.card : ℝ) := (div_le_iff₀ hBpos).mp hbias
  have hEsum : |∑ x ∈ E, f x| ≤ (E.card : ℝ) := by
    calc
      |∑ x ∈ E, f x| ≤ ∑ x ∈ E, |f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ E, (1 : ℝ) := Finset.sum_le_sum fun x hx => hf x (hEB hx)
      _ = (E.card : ℝ) := by simp
  have hsdiff_sum : (∑ x ∈ B \ E, f x) = (∑ x ∈ B, f x) - (∑ x ∈ E, f x) :=
    Finset.sum_sdiff_eq_sub hEB
  have hnum : |∑ x ∈ B \ E, f x| ≤ (δ + ε) * (B.card : ℝ) := by
    rw [hsdiff_sum]
    calc
      |(∑ x ∈ B, f x) - (∑ x ∈ E, f x)| ≤ |∑ x ∈ B, f x| + |∑ x ∈ E, f x| := abs_sub _ _
      _ ≤ δ * (B.card : ℝ) + (E.card : ℝ) := add_le_add hBsum hEsum
      _ ≤ δ * (B.card : ℝ) + ε * (B.card : ℝ) := by linarith
      _ = (δ + ε) * (B.card : ℝ) := by ring
  have hδnn : 0 ≤ δ := le_trans (by positivity) hbias
  rw [abs_div, abs_of_pos hrem_pos]
  calc
    |∑ x ∈ B \ E, f x| / ((B \ E).card : ℝ)
      ≤ ((δ + ε) * (B.card : ℝ)) / ((1 - ε) * (B.card : ℝ)) :=
        div_le_div₀ (by positivity) hnum (mul_pos (by linarith) hBpos) hrem_ge
    _ = (δ + ε) / (1 - ε) := mul_div_mul_right _ _ hBpos.ne'

/-- Under Dirichlet GRH, after deleting any exceptional subset `E ⊆ splitPrimeBin N P (2 * P)`
    of relative size `≤ ε < 1`, the normalized bias of every nontrivial genus character `χ_S`
    on `splitPrimeBin N P (2 * P) \ E` is at most `(O(P^(-1/2) * (1 + log(N * P))^3) + ε) / (1 - ε)`. -/
theorem splitPrimeBin_genus_bias_after_deletion_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C_thresh C_bias : ℝ, 0 ≤ C_thresh ∧ 0 ≤ C_bias ∧
      ∀ (N P : ℕ), Odd N → 3 ≤ N → 2 ≤ P →
        C_thresh * (1 + Real.log ((N : ℝ) * P)) ^ 3 ≤ Real.sqrt P →
        ∀ (E : Finset ℕ) (ε : ℝ),
          E ⊆ splitPrimeBin N P (2 * P) →
          (E.card : ℝ) ≤ ε * ((splitPrimeBin N P (2 * P)).card : ℝ) →
          0 ≤ ε → ε < 1 →
            (splitPrimeBin N P (2 * P) \ E).Nonempty ∧
            ∀ S ⊆ N.primeFactors, S.Nonempty →
              |(∑ p ∈ splitPrimeBin N P (2 * P) \ E, genusCharReal N S (p : ZMod (8 * N))) /
                  ((splitPrimeBin N P (2 * P) \ E).card : ℝ)| ≤
                (C_bias * (P : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log ((N : ℝ) * P)) ^ 3 + ε) /
                  (1 - ε) := by
  obtain ⟨C_thresh, C_bias, hCt, hCb, hmain⟩ := splitPrimeBin_genus_bias_from_critical_line line
  refine ⟨C_thresh, C_bias, hCt, hCb, fun N P hNodd hN hP hthresh E ε hEB hE hε0 hε1 => ?_⟩
  obtain ⟨hcard, hbias⟩ := hmain N P hNodd hN hP hthresh
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hlog2P_pos : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by
    have : (2 : ℝ) ≤ P := by exact_mod_cast hP
    linarith)
  have hBne : (splitPrimeBin N P (2 * P)).Nonempty :=
    Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le (by positivity) hcard))
  have hrem_ne : (splitPrimeBin N P (2 * P) \ E).Nonempty := by
    have hcard_eq : ((splitPrimeBin N P (2 * P) \ E).card : ℝ) + (E.card : ℝ) =
        ((splitPrimeBin N P (2 * P)).card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hEB
    have hBpos : (0 : ℝ) < ((splitPrimeBin N P (2 * P)).card : ℝ) := Nat.cast_pos.mpr hBne.card_pos
    have hpos : (0 : ℝ) < ((splitPrimeBin N P (2 * P) \ E).card : ℝ) :=
      lt_of_lt_of_le (mul_pos (sub_pos.mpr hε1) hBpos) (by nlinarith)
    exact Finset.card_pos.mp (Nat.cast_pos.mp hpos)
  refine ⟨hrem_ne, fun S hS hne => ?_⟩
  exact (average_bias_after_deletion (splitPrimeBin N P (2 * P)) E
    (fun p => genusCharReal N S (p : ZMod (8 * N))) hEB hBne
    (fun p _ => abs_genusCharReal_le_one N S _)
    (hbias S hS hne) hE hε0 hε1).2.2

/-!
## Section 3: Product genus mixing and distinct squarefree tuple counts
-/

/-- The elementary abelian genus sign group `(ℤˣ)^{ω(N)}` indexed by prime factors of `N`. -/
abbrev GenusGroup (N : ℕ) := {ℓ : ℕ // ℓ ∈ N.primeFactors} → ℤˣ

/-- Index set of genus characters: subsets of prime factors of `N`, of cardinality `2^{ω(N)}`. -/
abbrev GenusCharIndex (N : ℕ) := Finset {ℓ : ℕ // ℓ ∈ N.primeFactors}

theorem card_genusCharIndex (N : ℕ) :
    Fintype.card (GenusCharIndex N) = 2 ^ N.primeFactors.card := by
  simp [GenusCharIndex, Fintype.card_finset, Fintype.card_coe]

/-- The genus-label map sending an integer `a` coprime to `N` to its Legendre-symbol vector
    in `GenusGroup N`. -/
noncomputable def genusMap (N a : ℕ) : GenusGroup N :=
  fun ℓ =>
    if h : ℓ.1.Prime then
      if @legendreSym ℓ.1 ⟨h⟩ (a : ℤ) = 1 then 1 else -1
    else 1

/-- The multiplicative sign character `χ_S : GenusGroup N →* ℝ` associated to `S : GenusCharIndex N`. -/
noncomputable def genusCharOnGroup (N : ℕ) (S : GenusCharIndex N) : GenusGroup N →* ℝ where
  toFun g := ∏ ℓ ∈ S, ((g ℓ : ℤ) : ℝ)
  map_one' := by simp
  map_mul' g₁ g₂ := by
    simp only [Pi.mul_apply, Units.val_mul, Int.cast_mul, Finset.prod_mul_distrib]

/-- Exact character orthogonality on `GenusGroup N`. -/
theorem genusCharOnGroup_orthogonal (N : ℕ) (g : GenusGroup N) :
    (∑ S : GenusCharIndex N, genusCharOnGroup N S g) =
      if g = 1 then (Fintype.card (GenusCharIndex N) : ℝ) else 0 := by
  have hsum :
      (∑ S : GenusCharIndex N, genusCharOnGroup N S g) =
        ∏ ℓ : {ℓ : ℕ // ℓ ∈ N.primeFactors}, (1 + ((g ℓ : ℤ) : ℝ)) := by
    have h := Finset.prod_one_add (s := (Finset.univ : Finset {ℓ : ℕ // ℓ ∈ N.primeFactors}))
      (f := fun ℓ => ((g ℓ : ℤ) : ℝ))
    rw [Finset.powerset_univ] at h
    simpa [genusCharOnGroup] using h.symm
  rw [hsum]
  by_cases hg : g = 1
  · subst hg
    simp [Fintype.card_coe, show (1 : ℝ) + 1 = 2 by norm_num]
  · rw [if_neg hg]
    have hex : ∃ ℓ : {ℓ : ℕ // ℓ ∈ N.primeFactors}, g ℓ ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hg (funext hall)
    obtain ⟨ℓ₀, hℓ₀⟩ := hex
    have hm1 : g ℓ₀ = -1 := (Int.units_eq_one_or (g ℓ₀)).resolve_left hℓ₀
    exact Finset.prod_eq_zero (Finset.mem_univ ℓ₀) (by simp [hm1])

private lemma legendreSym_eq_one_or_neg_one_of_coprime {ℓ a : ℕ} (hℓ : ℓ.Prime)
    (hcop : Nat.Coprime a ℓ) :
    @legendreSym ℓ ⟨hℓ⟩ (a : ℤ) = 1 ∨ @legendreSym ℓ ⟨hℓ⟩ (a : ℤ) = -1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hne : ((a : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h0
    have : (a : ZMod ℓ) = 0 := by simpa using h0
    have hdvd : ℓ ∣ a := (ZMod.natCast_eq_zero_iff a ℓ).mp this
    have : ℓ ∣ Nat.gcd a ℓ := Nat.dvd_gcd hdvd (dvd_refl ℓ)
    rw [hcop.gcd_eq_one] at this
    exact hℓ.not_dvd_one this
  simpa [legendreSym] using quadraticChar_dichotomy hne

theorem genusMap_mul_of_coprime {N a b : ℕ} (ha : Nat.Coprime a N) (hb : Nat.Coprime b N) :
    genusMap N (a * b) = genusMap N a * genusMap N b := by
  funext ℓ
  have hℓp : ℓ.1.Prime := Nat.prime_of_mem_primeFactors ℓ.2
  have hℓd : ℓ.1 ∣ N := Nat.dvd_of_mem_primeFactors ℓ.2
  have : Fact ℓ.1.Prime := ⟨hℓp⟩
  have haℓ : Nat.Coprime a ℓ.1 := ha.coprime_dvd_right hℓd
  have hbℓ : Nat.Coprime b ℓ.1 := hb.coprime_dvd_right hℓd
  simp only [Pi.mul_apply, genusMap, dif_pos hℓp, Nat.cast_mul, legendreSym.mul]
  rcases legendreSym_eq_one_or_neg_one_of_coprime hℓp haℓ with ha1 | ha1 <;>
    rcases legendreSym_eq_one_or_neg_one_of_coprime hℓp hbℓ with hb1 | hb1 <;>
    simp [ha1, hb1]

theorem genusMap_finset_prod_of_coprime {ι : Type*} (s : Finset ι) {N : ℕ} (f : ι → ℕ)
    (hcop : ∀ i ∈ s, Nat.Coprime (f i) N) :
    genusMap N (∏ i ∈ s, f i) = ∏ i ∈ s, genusMap N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext ℓ
    have hℓp : ℓ.1.Prime := Nat.prime_of_mem_primeFactors ℓ.2
    have : Fact ℓ.1.Prime := ⟨hℓp⟩
    simp [genusMap, dif_pos hℓp]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : Nat.Coprime (f a) N := hcop a (Finset.mem_insert_self a s)
    have hfs : Nat.Coprime (∏ i ∈ s, f i) N :=
      Nat.Coprime.prod_left fun i hi => hcop i (Finset.mem_insert_of_mem hi)
    rw [genusMap_mul_of_coprime hfa hfs, ih (fun i hi => hcop i (Finset.mem_insert_of_mem hi))]

theorem genusCharOnGroup_genusMap_eq {N a : ℕ} (S : GenusCharIndex N)
    (ha : Nat.Coprime a (8 * N)) :
    genusCharOnGroup N S (genusMap N a) =
      genusCharReal N (S.image Subtype.val) (a : ZMod (8 * N)) := by
  have hunit : IsUnit (a : ZMod (8 * N)) := (ZMod.isUnit_iff_coprime a (8 * N)).2 ha
  rw [genusCharReal_apply, genusCharInt, mulChar_finset_prod_apply _ _ hunit, Int.cast_prod,
    Finset.prod_image (fun _ _ _ _ h => Subtype.ext h)]
  dsimp [genusCharOnGroup]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  have hℓp : ℓ.1.Prime := Nat.prime_of_mem_primeFactors ℓ.2
  have hℓd : ℓ.1 ∣ N := Nat.dvd_of_mem_primeFactors ℓ.2
  have haℓ : Nat.Coprime a ℓ.1 :=
    (Nat.Coprime.coprime_mul_left_right ha).coprime_dvd_right hℓd
  rw [primeGenusCharInt_apply_of_coprime hℓp hℓd ha]
  simp only [genusMap, dif_pos hℓp]
  rcases legendreSym_eq_one_or_neg_one_of_coprime hℓp haℓ with h | h <;> simp [h]

theorem genusMap_eq_one_iff_all_genusChar {N a : ℕ} (ha : Nat.Coprime a (8 * N)) :
    genusMap N a = 1 ↔ ∀ S ⊆ N.primeFactors, genusCharReal N S (a : ZMod (8 * N)) = 1 := by
  constructor
  · intro hg S hS
    let S' : GenusCharIndex N := S.attach.image fun x => ⟨x.1, hS x.2⟩
    have himg : S'.image Subtype.val = S := by
      ext x
      simp only [S', Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨a, _, ⟨y, hy, hya⟩, hax⟩
        subst hax
        have hya' := congrArg Subtype.val hya
        simp only at hya'
        subst hya'
        exact hy
      · intro hx
        exact ⟨x, hS hx, ⟨x, hx, rfl⟩, rfl⟩
    rw [← himg, ← genusCharOnGroup_genusMap_eq S' ha, hg, map_one]
  · intro hall
    funext ℓ
    have h1 := hall {ℓ.1} (Finset.singleton_subset_iff.mpr ℓ.2)
    have hℓp : ℓ.1.Prime := Nat.prime_of_mem_primeFactors ℓ.2
    have hℓd : ℓ.1 ∣ N := Nat.dvd_of_mem_primeFactors ℓ.2
    rw [genusCharReal_apply, genusCharInt, Finset.prod_singleton,
      primeGenusCharInt_apply_of_coprime hℓp hℓd ha] at h1
    have hleg : @legendreSym ℓ.1 ⟨hℓp⟩ (a : ℤ) = 1 := by exact_mod_cast h1
    simp [genusMap, dif_pos hℓp, hleg]

/-- Product genus mixing via `Cogentic.RandomizedGenusMixing.identity_mass_bias`:
    for `m` nonempty prime-band slots `P i` (all elements coprime to `8 * N`) with per-slot
    genus-character bias `≤ δ`, the fraction of ordered tuples in the principal genus is at least
    `g⁻¹ * (1 - (g - 1) * δ^m)` where `g = 2^{ω(N)}`. -/
theorem principal_genus_tuple_fraction_lower {N m : ℕ}
    (P : Fin m → Finset ℕ)
    (hPne : ∀ i, (P i).Nonempty)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbias : ∀ i (S : Finset ℕ), S ⊆ N.primeFactors → S.Nonempty →
      |(∑ p ∈ P i, genusCharReal N S (p : ZMod (8 * N))) / ((P i).card : ℝ)| ≤ δ) :
    let g : ℝ := (2 ^ N.primeFactors.card : ℕ)
    g⁻¹ * (1 - (g - 1) * δ ^ m) ≤
      (((Finset.univ : Finset (∀ i : Fin m, {p : ℕ // p ∈ P i})).filter
        (fun t => (∏ i : Fin m, genusMap N (t i).1) = 1)).card : ℝ) /
        ∏ i : Fin m, ((P i).card : ℝ) := by
  let Ω (i : Fin m) := {p : ℕ // p ∈ P i}
  let point (i : Fin m) (v : Ω i) : GenusGroup N := genusMap N v.1
  let weight (i : Fin m) (_ : Ω i) : ℝ := 1 / (Fintype.card (Ω i) : ℝ)
  have hcardΩ (i : Fin m) : Fintype.card (Ω i) = (P i).card := Fintype.card_coe (P i)
  have hnormal (i : Fin m) : (∑ v : Ω i, weight i v) = 1 := by
    have hpos : (Fintype.card (Ω i) : ℝ) ≠ 0 := by
      rw [hcardΩ]
      exact Nat.cast_ne_zero.mpr (hPne i).card_pos.ne'
    simp [weight, hpos]
  have hbm : ∀ (i : Fin m) (S : GenusCharIndex N), S ≠ ∅ →
      |Cogentic.RandomizedGenusMixing.bandMean point weight (genusCharOnGroup N) i S| ≤ δ := by
    intro i S hSne
    have hSimg_sub : S.image Subtype.val ⊆ N.primeFactors := by
      intro ℓ hℓ
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hℓ
      exact x.2
    have hSimg_ne : (S.image Subtype.val).Nonempty :=
      (Finset.nonempty_iff_ne_empty.mpr hSne).image _
    have heq :
        Cogentic.RandomizedGenusMixing.bandMean point weight (genusCharOnGroup N) i S =
          (∑ p ∈ P i, genusCharReal N (S.image Subtype.val) (p : ZMod (8 * N))) /
            ((P i).card : ℝ) := by
      unfold Cogentic.RandomizedGenusMixing.bandMean
      simp only [point, weight, ← Finset.sum_mul, hcardΩ, div_eq_mul_inv, one_mul]
      congr 1
      rw [← Finset.sum_coe_sort (P i)]
      refine Finset.sum_congr rfl fun v _ => ?_
      exact genusCharOnGroup_genusMap_eq S (hPcop i v.1 v.2)
    rw [heq]
    exact hbias i (S.image Subtype.val) hSimg_sub hSimg_ne
  have hmix := Cogentic.RandomizedGenusMixing.identity_mass_bias
    (point := point) (weight := weight) (χ := genusCharOnGroup N)
    (trivial := (∅ : GenusCharIndex N)) (bias := fun _ => δ)
    (genusCharOnGroup_orthogonal N) (fun _ => by simp [genusCharOnGroup]) hnormal hbm
  rw [Cogentic.RandomizedGenusMixing.empirical_identity_mass, card_genusCharIndex] at hmix
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcardΩ] at hmix
  have hgpos : (0 : ℝ) < ((2 ^ N.primeFactors.card : ℕ) : ℝ) := by positivity
  have hlo := (abs_le.mp hmix).1
  dsimp only
  rw [inv_mul_le_iff₀ hgpos]
  linarith

/-- Repeated-prime collision bound: for `m` band slots `P i` each of size at least `M_min > 0`,
    the fraction of ordered tuples with a repeated prime is at most `m^2 / M_min`. -/
theorem repeated_prime_collision_fraction_le {m M_min : ℕ}
    (P : Fin m → Finset ℕ) (hM : 0 < M_min) (hPsize : ∀ i, M_min ≤ (P i).card) :
    (((Finset.univ : Finset (∀ i : Fin m, {p : ℕ // p ∈ P i})).filter
      (fun t => ¬ Function.Injective (fun i => (t i).1))).card : ℝ) /
        ∏ i : Fin m, ((P i).card : ℝ) ≤
      (m : ℝ) ^ 2 / (M_min : ℝ) := by
  let Ω (i : Fin m) := {p : ℕ // p ∈ P i}
  let Coll := (Finset.univ : Finset (∀ i : Fin m, Ω i)).filter
    (fun t => ¬ Function.Injective (fun i => (t i).1))
  let PairColl (pair : Fin m × Fin m) :=
    (Finset.univ : Finset (∀ i : Fin m, Ω i)).filter (fun t => (t pair.1).1 = (t pair.2).1)
  let OffDiag := (Finset.univ : Finset (Fin m × Fin m)).filter (fun pair => pair.1 ≠ pair.2)
  have hsub : Coll ⊆ OffDiag.biUnion PairColl := by
    intro t ht
    have hnot := (Finset.mem_filter.mp ht).2
    unfold Function.Injective at hnot
    push Not at hnot
    obtain ⟨i, j, hij_eq, hij_ne⟩ := hnot
    exact Finset.mem_biUnion.mpr
      ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij_ne⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij_eq⟩⟩
  have hpair_card : ∀ pair ∈ OffDiag,
      ((PairColl pair).card : ℝ) * (M_min : ℝ) ≤ ∏ k : Fin m, ((P k).card : ℝ) := by
    intro ⟨i, j⟩ hp
    have hij : i ≠ j := (Finset.mem_filter.mp hp).2
    let Scompl : Finset (Fin m) := Finset.univ.erase j
    let restrict : (∀ k : Fin m, Ω k) → (∀ k : Scompl, Ω k.1) :=
      fun t k => t k.1
    have hinj : Set.InjOn restrict (PairColl (i, j) : Set (∀ k : Fin m, Ω k)) := by
      intro t₁ ht₁ t₂ ht₂ heq
      have h1 : (t₁ i).1 = (t₁ j).1 := (Finset.mem_filter.mp ht₁).2
      have h2 : (t₂ i).1 = (t₂ j).1 := (Finset.mem_filter.mp ht₂).2
      funext k
      by_cases hkj : k = j
      · subst k
        have hi_mem : i ∈ Scompl := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
        have hi_eq := congrFun heq ⟨i, hi_mem⟩
        apply Subtype.ext
        rw [← h1, ← h2]
        exact congrArg Subtype.val hi_eq
      · have hk_mem : k ∈ Scompl := Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩
        exact congrFun heq ⟨k, hk_mem⟩
    have hcard_le : (PairColl (i, j)).card ≤ Fintype.card (∀ k : Scompl, Ω k.1) := by
      calc
        (PairColl (i, j)).card = ((PairColl (i, j)).image restrict).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (∀ k : Scompl, Ω k.1)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = _ := Finset.card_univ
    have hprod_compl :
        Fintype.card (∀ k : Scompl, Ω k.1) * (P j).card = ∏ k : Fin m, (P k).card := by
      rw [Fintype.card_pi]
      have h1 : (∏ k : Scompl, Fintype.card (Ω k.1)) = ∏ k ∈ Scompl, (P k).card := by
        calc
          (∏ k : Scompl, Fintype.card (Ω k.1)) = ∏ k : Scompl, (P k.1).card :=
            Finset.prod_congr rfl fun k _ => Fintype.card_coe (P k.1)
          _ = ∏ k ∈ Scompl, (P k).card := Finset.prod_coe_sort Scompl (fun k => (P k).card)
      rw [h1, mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun k => (P k).card) (Finset.mem_univ j)
    have hmul_nat : (PairColl (i, j)).card * M_min ≤ ∏ k : Fin m, (P k).card := by
      calc
        (PairColl (i, j)).card * M_min
            ≤ Fintype.card (∀ k : Scompl, Ω k.1) * (P j).card :=
          Nat.mul_le_mul hcard_le (hPsize j)
        _ = ∏ k : Fin m, (P k).card := hprod_compl
    exact_mod_cast hmul_nat
  have htot_pos : (0 : ℝ) < ∏ k : Fin m, ((P k).card : ℝ) := by
    refine Finset.prod_pos fun k _ => ?_
    exact Nat.cast_pos.mpr (lt_of_lt_of_le hM (hPsize k))
  have hMpos : (0 : ℝ) < (M_min : ℝ) := Nat.cast_pos.mpr hM
  have hunion : (Coll.card : ℝ) ≤ ∑ pair ∈ OffDiag, ((PairColl pair).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hOffCard : (OffDiag.card : ℝ) ≤ (m : ℝ) ^ 2 := by
    have hle : OffDiag.card ≤ Fintype.card (Fin m × Fin m) :=
      (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ
    rw [Fintype.card_prod, Fintype.card_fin, ← sq] at hle
    exact_mod_cast hle
  have hsum_le :
      (∑ pair ∈ OffDiag, ((PairColl pair).card : ℝ)) * (M_min : ℝ) ≤
        (m : ℝ) ^ 2 * ∏ k : Fin m, ((P k).card : ℝ) := by
    rw [Finset.sum_mul]
    calc
      ∑ pair ∈ OffDiag, ((PairColl pair).card : ℝ) * (M_min : ℝ)
          ≤ ∑ _pair ∈ OffDiag, ∏ k : Fin m, ((P k).card : ℝ) :=
        Finset.sum_le_sum hpair_card
      _ = (OffDiag.card : ℝ) * ∏ k : Fin m, ((P k).card : ℝ) := by simp [nsmul_eq_mul]
      _ ≤ (m : ℝ) ^ 2 * ∏ k : Fin m, ((P k).card : ℝ) :=
        mul_le_mul_of_nonneg_right hOffCard htot_pos.le
  rw [div_le_div_iff₀ htot_pos hMpos]
  calc
    (Coll.card : ℝ) * (M_min : ℝ)
        ≤ (∑ pair ∈ OffDiag, ((PairColl pair).card : ℝ)) * (M_min : ℝ) :=
      mul_le_mul_of_nonneg_right hunion hMpos.le
    _ ≤ (m : ℝ) ^ 2 * ∏ k : Fin m, ((P k).card : ℝ) := hsum_le

/-- Combined principal-genus and distinct-prime tuple fraction lower bound. -/
theorem principal_genus_distinct_tuple_fraction_lower {N m M_min : ℕ}
    (P : Fin m → Finset ℕ) (hM : 0 < M_min) (hPsize : ∀ i, M_min ≤ (P i).card)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbias : ∀ i (S : Finset ℕ), S ⊆ N.primeFactors → S.Nonempty →
      |(∑ p ∈ P i, genusCharReal N S (p : ZMod (8 * N))) / ((P i).card : ℝ)| ≤ δ) :
    let g : ℝ := (2 ^ N.primeFactors.card : ℕ)
    g⁻¹ * (1 - (g - 1) * δ ^ m) - (m : ℝ) ^ 2 / (M_min : ℝ) ≤
      (((Finset.univ : Finset (∀ i : Fin m, {p : ℕ // p ∈ P i})).filter
        (fun t => (∏ i : Fin m, genusMap N (t i).1) = 1 ∧
          Function.Injective (fun i => (t i).1))).card : ℝ) /
        ∏ i : Fin m, ((P i).card : ℝ) := by
  have hPne : ∀ i, (P i).Nonempty := fun i => Finset.card_pos.mp (lt_of_lt_of_le hM (hPsize i))
  have hprin := principal_genus_tuple_fraction_lower P hPne hPcop hδ hbias
  have hcoll := repeated_prime_collision_fraction_le P hM hPsize
  let U := (Finset.univ : Finset (∀ i : Fin m, {p : ℕ // p ∈ P i}))
  let A := U.filter (fun t => (∏ i : Fin m, genusMap N (t i).1) = 1)
  let B := U.filter (fun t => ¬ Function.Injective (fun i => (t i).1))
  let C := U.filter (fun t => (∏ i : Fin m, genusMap N (t i).1) = 1 ∧
    Function.Injective (fun i => (t i).1))
  have hsub : A ⊆ C ∪ B := by
    intro t ht
    have h1 := (Finset.mem_filter.mp ht).2
    by_cases hinj : Function.Injective (fun i => (t i).1)
    · exact Finset.mem_union_left B (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, hinj⟩)
    · exact Finset.mem_union_right C (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj⟩)
  have hcard_le : (A.card : ℝ) ≤ (C.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le C B)
  have htot_pos : (0 : ℝ) < ∏ i : Fin m, ((P i).card : ℝ) :=
    Finset.prod_pos fun i _ => Nat.cast_pos.mpr (lt_of_lt_of_le hM (hPsize i))
  have hdiv : (A.card : ℝ) / (∏ i : Fin m, ((P i).card : ℝ)) ≤
      (C.card : ℝ) / (∏ i : Fin m, ((P i).card : ℝ)) +
      (B.card : ℝ) / (∏ i : Fin m, ((P i).card : ℝ)) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hcard_le htot_pos.le
  dsimp only at hprin ⊢
  linarith

/-- Every distinct principal-genus tuple of primes coprime to `8 * N` multiplies to a
    squarefree integer coprime to `8 * N` in the principal genus. -/
theorem distinct_prime_tuple_prod_squarefree_and_principal {N m : ℕ}
    (P : Fin m → Finset ℕ)
    (hPprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N))
    (t : ∀ i : Fin m, {p : ℕ // p ∈ P i})
    (hprin : (∏ i : Fin m, genusMap N (t i).1) = 1)
    (hinj : Function.Injective (fun i => (t i).1)) :
    let A := ∏ i : Fin m, (t i).1
    Squarefree A ∧ Nat.Coprime A (8 * N) ∧
      ∀ S ⊆ N.primeFactors, genusCharReal N S (A : ZMod (8 * N)) = 1 := by
  dsimp only
  have hsqf : Squarefree (∏ i : Fin m, (t i).1) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij => ?_)
      (fun i _ => (hPprime i (t i).1 (t i).2).squarefree)
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hPprime i (t i).1 (t i).2) (hPprime j (t j).1 (t j).2)).mpr
        (fun heq => hij (hinj heq)))
  have hcop8 : Nat.Coprime (∏ i : Fin m, (t i).1) (8 * N) :=
    Nat.Coprime.prod_left fun i _ => hPcop i (t i).1 (t i).2
  have hcopN : ∀ i ∈ (Finset.univ : Finset (Fin m)), Nat.Coprime (t i).1 N :=
    fun i _ => Nat.Coprime.coprime_mul_left_right (hPcop i (t i).1 (t i).2)
  have hgenus : genusMap N (∏ i : Fin m, (t i).1) = 1 := by
    rw [genusMap_finset_prod_of_coprime Finset.univ (fun i => (t i).1) hcopN, hprin]
  exact ⟨hsqf, hcop8, (genusMap_eq_one_iff_all_genusChar hcop8).mp hgenus⟩

/-!
## Section 4: Elementary Rankin prefix upper bounds
-/

private lemma two_pow_omega_le_divisors_card {m : ℕ} (hm : 0 < m) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  let f : Finset ℕ → ℕ := fun S => ∏ p ∈ S, p
  have hinj : Set.InjOn f (m.primeFactors.powerset : Set (Finset ℕ)) := by
    intro S hS T hT heq
    have hSp : ∀ p ∈ S, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp)
    have hTp : ∀ p ∈ T, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hT hp)
    rw [← Nat.primeFactors_prod hSp, ← Nat.primeFactors_prod hTp]
    exact congrArg Nat.primeFactors heq
  have hsub : m.primeFactors.powerset.image f ⊆ m.divisors := by
    intro d hd
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
    have hSsub : S ⊆ m.primeFactors := Finset.mem_powerset.mp hS
    have hdvd : (∏ p ∈ S, p) ∣ m :=
      (Finset.prod_dvd_prod_of_subset S m.primeFactors id hSsub).trans (Nat.prod_primeFactors_dvd m)
    exact Nat.mem_divisors.mpr ⟨hdvd, hm.ne'⟩
  calc
    2 ^ m.primeFactors.card = m.primeFactors.powerset.card := (Finset.card_powerset _).symm
    _ = (m.primeFactors.powerset.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ m.divisors.card := Finset.card_le_card hsub

private lemma harmonic_le_one_add_log {U : ℕ} (hU : 1 ≤ U) :
    (∑ d ∈ Finset.Icc 1 U, (1 / (d : ℝ))) ≤ 1 + Real.log U := by
  induction U with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp
    | succ n =>
      have hn1 : 1 ≤ n + 1 := by omega
      have hsplit : Finset.Icc 1 (n + 2) = insert (n + 2) (Finset.Icc 1 (n + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnotmem : n + 2 ∉ Finset.Icc 1 (n + 1) := by simp
      rw [hsplit, Finset.sum_insert hnotmem]
      have hstep : 1 / ((n + 2 : ℕ) : ℝ) ≤ Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) := by
        have hpos1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hpos2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
        have hratio : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := div_pos hpos1 hpos2
        have hlog := Real.log_le_sub_one_of_pos hratio
        rw [Real.log_div hpos1.ne' hpos2.ne'] at hlog
        have hdiff : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) - 1 = -(1 / ((n + 2 : ℕ) : ℝ)) := by
          push_cast; field_simp; ring
        linarith
      linarith [ih hn1]

/-- Elementary divisor-weight sum bound: `∑_{m₀ ∈ [1, U]} 2^{ω(m₀)} ≤ U * (1 + log U)`. -/
theorem sum_two_pow_omega_le {U : ℕ} (hU : 1 ≤ U) :
    (∑ m₀ ∈ Finset.Icc 1 U, (2 : ℝ) ^ m₀.primeFactors.card) ≤ (U : ℝ) * (1 + Real.log U) := by
  have h1 :
      (∑ m₀ ∈ Finset.Icc 1 U, (2 : ℝ) ^ m₀.primeFactors.card) ≤
        ∑ m₀ ∈ Finset.Icc 1 U, (m₀.divisors.card : ℝ) := by
    refine Finset.sum_le_sum fun m₀ hm₀ => ?_
    have hm0pos : 0 < m₀ := (Finset.mem_Icc.mp hm₀).1
    exact_mod_cast two_pow_omega_le_divisors_card hm0pos
  have h2 :
      (∑ m₀ ∈ Finset.Icc 1 U, m₀.divisors.card) =
        ∑ d ∈ Finset.Icc 1 U, U / d := by
    have hdouble :
        (∑ m₀ ∈ Finset.Icc 1 U, m₀.divisors.card) =
          ∑ d ∈ Finset.Icc 1 U, ((Finset.Icc 1 U).filter (fun m₀ => d ∣ m₀)).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      calc
        ∑ m₀ ∈ Finset.Icc 1 U, ∑ _d ∈ m₀.divisors, 1
            = ∑ m₀ ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc 1 U, if d ∣ m₀ then 1 else 0 := by
          refine Finset.sum_congr rfl fun m₀ hm₀ => ?_
          rw [← Finset.sum_filter]
          congr 1
          ext d
          simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
          have hm₀_pos : 0 < m₀ := (Finset.mem_Icc.mp hm₀).1
          have hm₀_le : m₀ ≤ U := (Finset.mem_Icc.mp hm₀).2
          constructor
          · rintro ⟨hdvd, _⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hm₀_pos, (Nat.le_of_dvd hm₀_pos hdvd).trans hm₀_le⟩, hdvd⟩
          · rintro ⟨_, hdvd⟩
            exact ⟨hdvd, hm₀_pos.ne'⟩
        _ = ∑ d ∈ Finset.Icc 1 U, ∑ m₀ ∈ Finset.Icc 1 U, if d ∣ m₀ then 1 else 0 :=
          Finset.sum_comm
    rw [hdouble]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hbi : ((Finset.Icc 1 U).filter (fun m₀ => d ∣ m₀)) =
        (Finset.Icc 1 (U / d)).image (fun k => d * k) := by
      ext m₀
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hm1, hmU⟩, k, rfl⟩
        have hkpos : 1 ≤ k := by
          by_contra hk0
          have : k = 0 := by omega
          subst this; omega
        exact ⟨k, ⟨hkpos, (Nat.le_div_iff_mul_le hdpos).mpr (by rw [mul_comm]; exact hmU)⟩, rfl⟩
      · rintro ⟨k, ⟨hk1, hkle⟩, rfl⟩
        have hmul : d * k ≤ U := by
          rw [mul_comm]
          exact (Nat.le_div_iff_mul_le hdpos).mp hkle
        exact ⟨⟨Nat.mul_pos hdpos hk1, hmul⟩, ⟨k, rfl⟩⟩
    rw [hbi, Finset.card_image_of_injective _ (mul_right_injective₀ hdpos.ne'), Nat.card_Icc]
    exact Nat.add_sub_cancel (U / d) 1
  have h3 : (∑ m₀ ∈ Finset.Icc 1 U, (m₀.divisors.card : ℝ)) ≤
      (U : ℝ) * ∑ d ∈ Finset.Icc 1 U, (1 / (d : ℝ)) := by
    rw [← Nat.cast_sum, h2, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
    rw [mul_one_div, le_div_iff₀ hdpos]
    exact_mod_cast (mul_comm d (U / d) ▸ Nat.mul_div_le U d)
  calc
    (∑ m₀ ∈ Finset.Icc 1 U, (2 : ℝ) ^ m₀.primeFactors.card)
        ≤ (U : ℝ) * ∑ d ∈ Finset.Icc 1 U, (1 / (d : ℝ)) := h1.trans h3
    _ ≤ (U : ℝ) * (1 + Real.log U) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log hU) (Nat.cast_nonneg U)

/-- `d` is `Y`-smooth: `d ≥ 1` and every prime divisor of `d` is at most `Y`. -/
def IsSmooth (Y d : ℕ) : Prop :=
  0 < d ∧ ∀ p ∈ d.primeFactors, p ≤ Y

instance (Y d : ℕ) : Decidable (IsSmooth Y d) := by
  unfold IsSmooth
  infer_instance

/-- Primes at most `Y`. -/
def primesUpTo (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter Nat.Prime

/-- `Y`-smooth integers in `[T, U]`. -/
def smoothBandParts (T Y U : ℕ) : Finset ℕ :=
  (Finset.Icc T U).filter (IsSmooth Y)

/-- Integers `A ∈ [1, U]` admitting a certified prefix factorization `A = m₀ * ∏ i, d i`
    with pairwise coprime `Y_i`-smooth band parts `d_i ≥ T_i` whose product has at most `M`
    distinct prime factors. -/
noncomputable def certifiedPrefixSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T Y : ι → ℕ) (U M : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.Icc 1 U ×ˢ Fintype.piFinset (fun i => smoothBandParts (T i) (Y i) U)).filter
    (fun p => p.1 * (∏ i, p.2 i) ≤ U ∧
      (∏ i, p.2 i).primeFactors.card ≤ M ∧
      Pairwise (fun i k => Nat.Coprime (p.2 i) (p.2 k)))).image
    (fun p => p.1 * ∏ i, p.2 i)

/-- Weighted count of certified prefix integers:
    `∑_{A ∈ certifiedPrefixSet} 2^{ω(A)} ≤ 2^M * U * (1 + log U) * ∏_i ∑_{d_i ∈ [T_i, U], P^+(d_i) ≤ Y_i} 1/d_i`. -/
theorem certified_prefix_weighted_count_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T Y : ι → ℕ) (U M : ℕ) (hU : 1 ≤ U) (hT : ∀ i, 1 ≤ T i) :
    (∑ A ∈ certifiedPrefixSet T Y U M, (2 : ℝ) ^ A.primeFactors.card) ≤
      (2 : ℝ) ^ M * (U : ℝ) * (1 + Real.log U) *
        ∏ i : ι, ∑ d ∈ smoothBandParts (T i) (Y i) U, (1 / (d : ℝ)) := by
  classical
  let Dset := Fintype.piFinset (fun i : ι => smoothBandParts (T i) (Y i) U)
  let Tuples := (Finset.Icc 1 U ×ˢ Dset).filter
    (fun p => p.1 * (∏ i, p.2 i) ≤ U ∧
      (∏ i, p.2 i).primeFactors.card ≤ M ∧
      Pairwise (fun i k => Nat.Coprime (p.2 i) (p.2 k)))
  have hstep1 :
      (∑ A ∈ certifiedPrefixSet T Y U M, (2 : ℝ) ^ A.primeFactors.card) ≤
        ∑ p ∈ Tuples, (2 : ℝ) ^ (p.1 * ∏ i, p.2 i).primeFactors.card := by
    have hcert : certifiedPrefixSet T Y U M = Tuples.image (fun p => p.1 * ∏ i, p.2 i) := by
      unfold certifiedPrefixSet
      rfl
    rw [hcert]
    exact Finset.sum_image_le_of_nonneg (f := fun A : ℕ => (2 : ℝ) ^ A.primeFactors.card)
      fun _ _ => by positivity
  have hstep2 :
      (∑ p ∈ Tuples, (2 : ℝ) ^ (p.1 * ∏ i, p.2 i).primeFactors.card) ≤
        ∑ d ∈ Dset, ∑ m₀ ∈ Finset.Icc 1 (U / ∏ i, d i),
          (2 : ℝ) ^ M * (2 : ℝ) ^ m₀.primeFactors.card := by
    let BigTuples := Dset.sigma (fun d => Finset.Icc 1 (U / ∏ i, d i))
    have hmap :
        (∑ p ∈ Tuples, (2 : ℝ) ^ (p.1 * ∏ i, p.2 i).primeFactors.card) ≤
          ∑ p ∈ Tuples, (2 : ℝ) ^ M * (2 : ℝ) ^ p.1.primeFactors.card := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1).1
      have hp2 : p.2 ∈ Dset := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
      have hDpos : 0 < ∏ i, p.2 i :=
        Finset.prod_pos fun i _ =>
          lt_of_lt_of_le (hT i) (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp2 i)).1).1
      have hMle : (∏ i, p.2 i).primeFactors.card ≤ M := (Finset.mem_filter.mp hp).2.2.1
      have hpf : (p.1 * ∏ i, p.2 i).primeFactors.card ≤ p.1.primeFactors.card + M := by
        rw [Nat.primeFactors_mul (by omega) hDpos.ne']
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hMle _)
      calc
        (2 : ℝ) ^ (p.1 * ∏ i, p.2 i).primeFactors.card
            ≤ (2 : ℝ) ^ (p.1.primeFactors.card + M) :=
          pow_le_pow_right₀ (by norm_num) hpf
        _ = (2 : ℝ) ^ M * (2 : ℝ) ^ p.1.primeFactors.card := by rw [pow_add, mul_comm]
    refine hmap.trans ?_
    have hsigma :
        (∑ d ∈ Dset, ∑ m₀ ∈ Finset.Icc 1 (U / ∏ i, d i),
            (2 : ℝ) ^ M * (2 : ℝ) ^ m₀.primeFactors.card) =
          ∑ x ∈ BigTuples, (2 : ℝ) ^ M * (2 : ℝ) ^ x.2.primeFactors.card :=
      (Finset.sum_sigma' Dset (fun d => Finset.Icc 1 (U / ∏ i, d i))
        (fun _ m₀ => (2 : ℝ) ^ M * (2 : ℝ) ^ m₀.primeFactors.card))
    rw [hsigma]
    let embed : ℕ × (ι → ℕ) → Σ _d : ι → ℕ, ℕ := fun p => ⟨p.2, p.1⟩
    have hinj : Function.Injective embed := fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h => by
      cases h; rfl
    have hsub : Tuples.image embed ⊆ BigTuples := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hp_prod := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp_prod.1).1
      have hDpos : 0 < ∏ i, p.2 i :=
        Finset.prod_pos fun i _ =>
          lt_of_lt_of_le (hT i) (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp_prod.2 i)).1).1
      have hmul_le : p.1 * ∏ i, p.2 i ≤ U := (Finset.mem_filter.mp hp).2.1
      exact Finset.mem_sigma.mpr ⟨hp_prod.2,
        Finset.mem_Icc.mpr ⟨hp1, (Nat.le_div_iff_mul_le hDpos).mpr hmul_le⟩⟩
    calc
      ∑ p ∈ Tuples, (2 : ℝ) ^ M * (2 : ℝ) ^ p.1.primeFactors.card
          = ∑ x ∈ Tuples.image embed, (2 : ℝ) ^ M * (2 : ℝ) ^ x.2.primeFactors.card := by
        rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      _ ≤ ∑ x ∈ BigTuples, (2 : ℝ) ^ M * (2 : ℝ) ^ x.2.primeFactors.card :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hstep3 :
      (∑ d ∈ Dset, ∑ m₀ ∈ Finset.Icc 1 (U / ∏ i, d i),
          (2 : ℝ) ^ M * (2 : ℝ) ^ m₀.primeFactors.card) ≤
        (2 : ℝ) ^ M * (U : ℝ) * (1 + Real.log U) *
          ∑ d ∈ Dset, ∏ i : ι, (1 / (d i : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [← Finset.mul_sum]
    have hDpos : 0 < ∏ i, d i :=
      Finset.prod_pos fun i _ =>
        lt_of_lt_of_le (hT i) (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hd i)).1).1
    have hDposR : (0 : ℝ) < (∏ i, d i : ℕ) := Nat.cast_pos.mpr hDpos
    have hprod_inv : (∏ i : ι, (1 / (d i : ℝ))) = 1 / ((∏ i, d i : ℕ) : ℝ) := by
      simp [one_div, Finset.prod_inv_distrib, Nat.cast_prod]
    rw [hprod_inv]
    have hinner :
        (∑ m₀ ∈ Finset.Icc 1 (U / ∏ i, d i), (2 : ℝ) ^ m₀.primeFactors.card) ≤
          (U : ℝ) * (1 + Real.log U) * (1 / ((∏ i, d i : ℕ) : ℝ)) := by
      by_cases hq : 1 ≤ U / ∏ i, d i
      · have hqleU : U / ∏ i, d i ≤ U := Nat.div_le_self U _
        have hqleR : ((U / ∏ i, d i : ℕ) : ℝ) ≤ (U : ℝ) / ((∏ i, d i : ℕ) : ℝ) :=
          (le_div_iff₀ hDposR).mpr (by exact_mod_cast Nat.div_mul_le_self U (∏ i, d i))
        have hlog_le : Real.log ((U / ∏ i, d i : ℕ) : ℝ) ≤ Real.log U :=
          Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqleU)
        have h1log : 0 ≤ 1 + Real.log U := by
          linarith [Real.log_nonneg (show (1 : ℝ) ≤ U by exact_mod_cast hU)]
        calc
          (∑ m₀ ∈ Finset.Icc 1 (U / ∏ i, d i), (2 : ℝ) ^ m₀.primeFactors.card)
              ≤ ((U / ∏ i, d i : ℕ) : ℝ) * (1 + Real.log ((U / ∏ i, d i : ℕ) : ℝ)) :=
            sum_two_pow_omega_le hq
          _ ≤ ((U : ℝ) / ((∏ i, d i : ℕ) : ℝ)) * (1 + Real.log U) :=
            mul_le_mul hqleR (by linarith)
              (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (U / ∏ i, d i : ℕ) by exact_mod_cast hq)])
              (by positivity)
          _ = (U : ℝ) * (1 + Real.log U) * (1 / ((∏ i, d i : ℕ) : ℝ)) := by ring
      · have hq0 : U / ∏ i, d i = 0 := Nat.lt_one_iff.mp (not_le.mp hq)
        rw [hq0]
        simp only [show Finset.Icc 1 0 = ∅ by decide, Finset.sum_empty]
        have hlogU : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
        positivity
    calc
      (2 : ℝ) ^ M * ∑ m₀ ∈ Finset.Icc 1 (U / ∏ i, d i), (2 : ℝ) ^ m₀.primeFactors.card
          ≤ (2 : ℝ) ^ M * ((U : ℝ) * (1 + Real.log U) * (1 / ((∏ i, d i : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = _ := by ring
  have hfactor :
      (∑ d ∈ Dset, ∏ i : ι, (1 / (d i : ℝ))) =
        ∏ i : ι, ∑ d ∈ smoothBandParts (T i) (Y i) U, (1 / (d : ℝ)) := by
    exact (Finset.prod_univ_sum (fun i : ι => smoothBandParts (T i) (Y i) U)
      (fun _ (d : ℕ) => (1 / (d : ℝ)))).symm
  calc
    (∑ A ∈ certifiedPrefixSet T Y U M, (2 : ℝ) ^ A.primeFactors.card)
        ≤ _ := hstep1.trans (hstep2.trans hstep3)
    _ = _ := by rw [hfactor]

private lemma geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), r ^ k) ≤ (1 - r)⁻¹ := by
  have hne : r - 1 ≠ 0 := by linarith
  have hpos : 0 < 1 - r := by linarith
  have heq : (∑ k ∈ Finset.range (K + 1), r ^ k) = (1 - r ^ (K + 1)) / (1 - r) := by
    have h := geom_sum_eq hr1.ne (K + 1)
    rw [h]
    field_simp [hne, hpos.ne']
    ring
  rw [heq, inv_eq_one_div]
  exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 (K + 1)]) hpos.le

private lemma smooth_rpow_sum_le_euler_prod {Y : ℕ} {β : ℝ} (hβ0 : 0 < β)
    (S : Finset ℕ) (hS : ∀ d ∈ S, IsSmooth Y d) :
    (∑ d ∈ S, (d : ℝ) ^ (-β)) ≤
      ∏ p ∈ primesUpTo Y, (1 - (p : ℝ) ^ (-β))⁻¹ := by
  classical
  let P := primesUpTo Y
  let K := S.sup id
  let Box := Fintype.piFinset (fun _ : P => Finset.range (K + 1))
  let toExp : ℕ → (P → ℕ) := fun d p => d.factorization p.1
  have hprod_eq : ∀ d ∈ S, (∏ p ∈ P, p ^ d.factorization p) = d := by
    intro d hd
    have hsm := hS d hd
    have hsub : d.primeFactors ⊆ P := by
      intro p hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_le, hsm.2 p hp⟩,
          Nat.prime_of_mem_primeFactors hp⟩
    calc
      (∏ p ∈ P, p ^ d.factorization p)
          = ∏ p ∈ d.primeFactors, p ^ d.factorization p := by
        refine (Finset.prod_subset hsub fun p _ hp => ?_).symm
        have h0 : d.factorization p = 0 :=
          Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
        simp [h0]
      _ = d := by
        simpa [Finsupp.prod, Nat.support_factorization] using
          Nat.prod_factorization_pow_eq_self hsm.1.ne'
  have hinj : Set.InjOn toExp (S : Set ℕ) := by
    intro d₁ hd₁ d₂ hd₂ heq
    rw [← hprod_eq d₁ hd₁, ← hprod_eq d₂ hd₂]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := congrFun heq ⟨p, hp⟩
    dsimp [toExp] at this
    rw [this]
  have hmaps : S.image toExp ⊆ Box := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    refine Fintype.mem_piFinset.mpr fun p => Finset.mem_range.mpr ?_
    have hle_d : d.factorization p.1 ≤ d := by
      have hp_prime : p.1.Prime := (Finset.mem_filter.mp p.2).2
      have hpow : 2 ^ d.factorization p.1 ≤ d := by
        calc
          2 ^ d.factorization p.1 ≤ p.1 ^ d.factorization p.1 :=
            Nat.pow_le_pow_left hp_prime.two_le _
          _ ≤ d := Nat.le_of_dvd (hS d hd).1 (Nat.ordProj_dvd d p.1)
      exact (Nat.lt_two_pow_self.le).trans hpow
    have hd_le_K : d ≤ K := Finset.le_sup (f := id) hd
    show d.factorization p.1 < K + 1
    omega
  have hrpow_eq : ∀ d ∈ S, (d : ℝ) ^ (-β) = ∏ p : P, ((p.1 : ℝ) ^ (-β)) ^ (toExp d p) := by
    intro d hd
    have hd_eq := hprod_eq d hd
    have hcast : (d : ℝ) = ∏ p : P, ((p.1 : ℝ) ^ (toExp d p)) := by
      conv_lhs => rw [← hd_eq]
      rw [Nat.cast_prod, ← Finset.prod_coe_sort P]
      refine Finset.prod_congr rfl fun p _ => by simp [toExp]
    rw [hcast, ← Real.finsetProd_rpow Finset.univ (fun p : P => (p.1 : ℝ) ^ (toExp d p))
      (fun p _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hp_pos : (0 : ℝ) < p.1 := Nat.cast_pos.mpr (Finset.mem_filter.mp p.2).2.pos
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le, mul_comm,
      Real.rpow_mul hp_pos.le, Real.rpow_natCast]
  have hbox_prod :
      (∑ e ∈ Box, ∏ p : P, ((p.1 : ℝ) ^ (-β)) ^ (e p)) =
        ∏ p : P, ∑ k ∈ Finset.range (K + 1), ((p.1 : ℝ) ^ (-β)) ^ k :=
    (Finset.prod_univ_sum (fun _ : P => Finset.range (K + 1))
      (fun (p : P) (k : ℕ) => ((p.1 : ℝ) ^ (-β)) ^ k)).symm
  calc
    ∑ d ∈ S, (d : ℝ) ^ (-β)
        = ∑ d ∈ S, ∏ p : P, ((p.1 : ℝ) ^ (-β)) ^ (toExp d p) :=
      Finset.sum_congr rfl hrpow_eq
    _ = ∑ e ∈ S.image toExp, ∏ p : P, ((p.1 : ℝ) ^ (-β)) ^ (e p) :=
      (Finset.sum_image (f := fun e : P → ℕ => ∏ p : P, ((p.1 : ℝ) ^ (-β)) ^ (e p)) hinj).symm
    _ ≤ ∑ e ∈ Box, ∏ p : P, ((p.1 : ℝ) ^ (-β)) ^ (e p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hmaps fun _ _ _ =>
        Finset.prod_nonneg fun _ _ => by positivity
    _ = ∏ p : P, ∑ k ∈ Finset.range (K + 1), ((p.1 : ℝ) ^ (-β)) ^ k := hbox_prod
    _ ≤ ∏ p : P, (1 - (p.1 : ℝ) ^ (-β))⁻¹ := by
      refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun _ _ => by positivity) fun p _ => ?_
      have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast (Finset.mem_filter.mp p.2).2.two_le
      have hr0 : 0 ≤ (p.1 : ℝ) ^ (-β) := Real.rpow_nonneg (by linarith) _
      have hr1 : (p.1 : ℝ) ^ (-β) < 1 := by
        rw [Real.rpow_neg (by linarith)]
        exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) hβ0)
      exact geom_sum_le_inv_one_sub hr0 hr1 K
    _ = ∏ p ∈ P, (1 - (p : ℝ) ^ (-β))⁻¹ :=
      Finset.prod_coe_sort P (fun p : ℕ => (1 - (p : ℝ) ^ (-β))⁻¹)

/-- Rankin's inequality for any finite set `S` of `Y`-smooth integers `≥ T`:
    for any `β ∈ (0, 1)`, `∑_{d ∈ S} 1/d ≤ T^(β - 1) * ∏_{p ≤ Y, p.Prime} (1 - p^(-β))⁻¹`. -/
theorem rankin_smooth_reciprocal_finset_le {T Y : ℕ} {β : ℝ}
    (hT : 1 ≤ T) (hβ0 : 0 < β) (hβ1 : β < 1)
    (S : Finset ℕ) (hS : ∀ d ∈ S, T ≤ d ∧ IsSmooth Y d) :
    (∑ d ∈ S, (1 / (d : ℝ))) ≤
      (T : ℝ) ^ (β - 1) * ∏ p ∈ primesUpTo Y, (1 - (p : ℝ) ^ (-β))⁻¹ := by
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hstep :
      (∑ d ∈ S, (1 / (d : ℝ))) ≤ (T : ℝ) ^ (β - 1) * ∑ d ∈ S, (d : ℝ) ^ (-β) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hdT : (T : ℝ) ≤ d := Nat.cast_le.mpr (hS d hd).1
    have hdpos : (0 : ℝ) < d := lt_of_lt_of_le hTpos hdT
    have hsplit : 1 / (d : ℝ) = (d : ℝ) ^ (β - 1) * (d : ℝ) ^ (-β) := by
      rw [← Real.rpow_add hdpos, show β - 1 + -β = -1 by ring, Real.rpow_neg_one, one_div]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hTpos hdT (by linarith)) (Real.rpow_nonneg hdpos.le _)
  exact hstep.trans
    (mul_le_mul_of_nonneg_left (smooth_rpow_sum_le_euler_prod hβ0 S fun d hd => (hS d hd).2)
      (Real.rpow_nonneg hTpos.le _))

/-- Infinite-sum (`tsum`) version of Rankin's inequality over all `Y`-smooth integers `d ≥ T`. -/
theorem rankin_smooth_reciprocal_tsum_le {T Y : ℕ} {β : ℝ}
    (hT : 1 ≤ T) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun d : {d : ℕ // T ≤ d ∧ IsSmooth Y d} => (1 / (d.1 : ℝ))) ∧
    (∑' d : {d : ℕ // T ≤ d ∧ IsSmooth Y d}, (1 / (d.1 : ℝ))) ≤
      (T : ℝ) ^ (β - 1) * ∏ p ∈ primesUpTo Y, (1 - (p : ℝ) ^ (-β))⁻¹ := by
  let B := (T : ℝ) ^ (β - 1) * ∏ p ∈ primesUpTo Y, (1 - (p : ℝ) ^ (-β))⁻¹
  have hfin : ∀ s : Finset {d : ℕ // T ≤ d ∧ IsSmooth Y d},
      (∑ d ∈ s, (1 / (d.1 : ℝ))) ≤ B := by
    intro s
    have himg : (∑ d ∈ s, (1 / (d.1 : ℝ))) = ∑ n ∈ s.image Subtype.val, (1 / (n : ℝ)) := by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    rw [himg]
    exact rankin_smooth_reciprocal_finset_le hT hβ0 hβ1 (s.image Subtype.val) fun n hn => by
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hn
      exact d.2
  have hsum : Summable (fun d : {d : ℕ // T ≤ d ∧ IsSmooth Y d} => (1 / (d.1 : ℝ))) :=
    summable_of_sum_le (fun _ => by positivity) hfin
  exact ⟨hsum, hsum.tsum_le_of_sum_le hfin⟩

/-- Combined certified-prefix Rankin upper bound: bounds the `2^{ω(A)}`-weighted count of
    certified prefix integers directly by the product of Rankin Euler bounds across bands. -/
theorem certified_prefix_rankin_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T Y : ι → ℕ) (β : ι → ℝ) (U M : ℕ)
    (hU : 1 ≤ U) (hT : ∀ i, 1 ≤ T i) (hβ0 : ∀ i, 0 < β i) (hβ1 : ∀ i, β i < 1) :
    (∑ A ∈ certifiedPrefixSet T Y U M, (2 : ℝ) ^ A.primeFactors.card) ≤
      (2 : ℝ) ^ M * (U : ℝ) * (1 + Real.log U) *
        ∏ i : ι, ((T i : ℝ) ^ (β i - 1) *
          ∏ p ∈ primesUpTo (Y i), (1 - (p : ℝ) ^ (-β i))⁻¹) := by
  refine (certified_prefix_weighted_count_le T Y U M hU hT).trans ?_
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => by positivity) fun i _ => ?_
  exact rankin_smooth_reciprocal_finset_le (hT i) (hβ0 i) (hβ1 i)
    (smoothBandParts (T i) (Y i) U) fun d hd =>
      ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1, (Finset.mem_filter.mp hd).2⟩

#print axioms splittingCharInt_eq_legendreSym
#print axioms genusChar_ne_one
#print axioms genusChar_mul_splittingChar_ne_one
#print axioms splitPrimeBin_card_approx_from_critical_line
#print axioms splitPrimeBin_genus_bias_from_critical_line
#print axioms splitPrimeBin_genus_bias_after_deletion_from_critical_line
#print axioms principal_genus_tuple_fraction_lower
#print axioms repeated_prime_collision_fraction_le
#print axioms principal_genus_distinct_tuple_fraction_lower
#print axioms sum_two_pow_omega_le
#print axioms certified_prefix_weighted_count_le
#print axioms rankin_smooth_reciprocal_finset_le
#print axioms rankin_smooth_reciprocal_tsum_le
#print axioms certified_prefix_rankin_bound

end Cogentic.RandomizedReducedFormSupply
