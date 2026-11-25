import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Integer form of the dense-prime saturation step of Cogentic Lemma 11.1. -/
namespace Cogentic

open UniqueFactorizationMonoid

private def primeProduct {P : Finset ℕ} (xs : Multiset P) : ℕ :=
  (xs.map Subtype.val).prod

private theorem primeProduct_injective {P : Finset ℕ} (hp : ∀ a ∈ P, Nat.Prime a) :
    Function.Injective (primeProduct (P := P)) := by
  have recover (xs : Multiset P) :
      normalizedFactors (primeProduct xs) = xs.map Subtype.val := by
    apply Nat.factors_multiset_prod_of_irreducible
    intro x hx
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hx
    exact (Nat.irreducible_iff_prime).mpr (Nat.prime_iff.mp (hp a a.property))
  intro xs ys h
  apply Multiset.map_injective Subtype.val_injective
  rw [← recover xs, ← recover ys, h]

private theorem primeProduct_le {P : Finset ℕ} {B : ℕ} (hb : ∀ a ∈ P, a ≤ B)
    (xs : Multiset P) : primeProduct xs ≤ B ^ xs.card := by
  induction xs using Multiset.induction_on with
  | empty => simp [primeProduct]
  | cons a xs ih =>
    simpa [primeProduct, pow_succ, Nat.mul_comm] using Nat.mul_le_mul (hb a a.property) ih

private theorem primeProduct_killed {P : Finset ℕ} {p E : ℕ}
    (hE : ∀ a ∈ P, (a : ZMod p) ^ E = 1) (xs : Multiset P) :
    (primeProduct xs : ZMod p)^E = 1 := by
  induction xs using Multiset.induction_on with
  | empty => simp [primeProduct]
  | cons a xs ih =>
    simpa [primeProduct, mul_pow, hE a a.property] using ih

/-- All length-k multisets of the accepted primes give distinct roots modulo p
of X^g-1 for g=gcd(E,p-1), whenever their products fit below p. -/
theorem prime_products_le_gcd {p E B k : ℕ} [Fact p.Prime] (P : Finset ℕ)
    (hP : ∀ a ∈ P, Nat.Prime a) (bound : ∀ a ∈ P, a ≤ B) (fits : B^k < p)
    (positive : 0 < E) (killed : ∀ a ∈ P, (a : ZMod p)^E = 1) :
    (P.card + k - 1).choose k ≤ E.gcd (p-1) := by
  classical
  let g := E.gcd (p-1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ positive
  let roots := (Polynomial.nthRoots g (1 : ZMod p)).toFinset
  have small (s : Sym P k) : primeProduct (s : Multiset P) < p := by
    exact (primeProduct_le bound _).trans_lt (s.property.symm ▸ fits)
  let send (s : Sym P k) : roots := by
    let x : ZMod p := primeProduct (s : Multiset P)
    have hE : x ^ E = 1 := primeProduct_killed killed _
    have hx : x ≠ 0 := by
      intro h
      simp [h, zero_pow positive.ne'] at hE
    have hk : orderOf x ∣ g := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hE)
      (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hx))
    exact ⟨x, Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hg).mpr
      (orderOf_dvd_iff_pow_eq_one.mp hk))⟩
  have hinj : Function.Injective send := by
    intro a b h
    have eq : (primeProduct (a : Multiset P) : ZMod p) = (primeProduct (b : Multiset P) : ZMod p) :=
      congrArg Subtype.val h
    have vals := congrArg ZMod.val eq
    rw [ZMod.val_natCast_of_lt (small a), ZMod.val_natCast_of_lt (small b)] at vals
    exact Subtype.ext (primeProduct_injective hP vals)
  calc
    _ = Fintype.card (Sym P k) := by rw [Sym.card_sym_eq_choose, Fintype.card_coe]
    _ ≤ Fintype.card roots := Fintype.card_le_of_injective send hinj
    _ ≤ _ := by
      rw [Fintype.card_coe]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

/-- No real logarithms enter the algorithm's dense-prime count guard. -/
theorem count_to_index {p E β k h : ℕ} [Fact p.Prime] (P : Finset ℕ)
    (hP : ∀ a ∈ P, Nat.Prime a) (bound : ∀ a ∈ P, a ≤ 2^β)
    (accept : 2^β ≤ 3*β*P.card) (fits : (2^β)^k < p)
    (last : p-1 < (2^β)^(k+1)) (budget : 3*β*k ≤ h)
    (positive : 0 < E) (killed : ∀ a ∈ P, (a : ZMod p)^E = 1) :
    (p-1) / E.gcd (p-1) < 2^β * h^k := by
  let g := E.gcd (p-1)
  have hr : 0 < P.card := by
    by_contra! hn
    have hz : P.card = 0 := Nat.eq_zero_of_le_zero hn
    simp [hz] at accept
  have many : P.card^k ≤ k^k * g := by
    have h := Nat.pow_sub_le_descFactorial (P.card + k - 1) k
    rw [show P.card + k - 1 + 1 - k = P.card by omega,
      Nat.descFactorial_eq_factorial_mul_choose] at h
    exact h.trans (Nat.mul_le_mul k.factorial_le_pow
      (prime_products_le_gcd P hP bound fits positive killed))
  have lower : (2^β)^k ≤ g*h^k := calc
    _ ≤ (3*β*P.card)^k := Nat.pow_le_pow_left accept k
    _ = (3*β)^k * P.card^k := Nat.mul_pow ..
    _ ≤ (3*β)^k * (k^k*g) := Nat.mul_le_mul_left _ many
    _ = g * (3*β*k)^k := by simp only [Nat.mul_pow]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left budget k)
  apply Nat.lt_of_mul_lt_mul_left (a := g)
  calc
    g * ((p-1) / g) = p-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
    _ < (2^β)^(k+1) := last
    _ = (2^β)^k * 2^β := Nat.pow_succ ..
    _ ≤ (g*h^k) * 2^β := Nat.mul_le_mul_right _ lower
    _ = _ := by ac_rfl

/-- A dyadic upper bound on the missing index, computed without the unknown p.
The floor in the exponent is already sufficient. -/
def indexCap (bits β : ℕ) : ℕ := 2^β * 2^(bits * Nat.clog 2 (6*bits) / β)

def saturate (E bits β : ℕ) : ℕ :=
  E * (Finset.Icc 1 (indexCap bits β)).lcm id

/-- Given only the accepted primes and their modular power certificates on N,
the computed exponent is divisible by p-1 for every prime p dividing N.
The input to the program does not include p. -/
theorem saturate_all_prime_factors {N E β bits : ℕ} (P : Finset ℕ)
    (input : 0 < N) (length : N < 2^bits) (beta : 0 < β) (positive : 0 < E)
    (primes : ∀ a ∈ P, Nat.Prime a) (bound : ∀ a ∈ P, a ≤ 2^β)
    (accept : 2^β ≤ 3*β*P.card) (checked : ∀ a ∈ P, (a : ZMod N)^E = 1)
    {p : ℕ} (prime : p.Prime) (divides : p ∣ N) : p-1 ∣ saturate E bits β := by
  let : Fact p.Prime := ⟨prime⟩
  let k := Nat.log (2^β) (p-1)
  let g := E.gcd (p-1)
  have groupPos : 0 < p-1 := Nat.sub_pos_of_lt prime.one_lt
  have small := Nat.pow_log_le_self (2^β) groupPos.ne'
  have maxPower : (2^β)^k ≤ p-1 := small
  have base : 1 < 2^β := Nat.one_lt_pow beta.ne' (by decide)
  have nextPower : p-1 < (2^β)^(k+1) := Nat.lt_pow_succ_log_self base _
  have bitsUsed : β*k ≤ bits := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [Nat.pow_mul]
    exact maxPower.trans ((Nat.sub_le _ _).trans ((Nat.le_of_dvd input divides).trans length.le))
  have localCert (a : ℕ) (ha : a ∈ P) : (a : ZMod p)^E = 1 := by
    simpa only [map_pow, map_natCast, map_one] using congrArg (ZMod.castHom divides (ZMod p)) (checked a ha)
  have indexLt : (p-1) / g < 2^β * (6*bits)^k := by
    apply count_to_index P primes bound accept (maxPower.trans_lt (Nat.sub_lt prime.pos (by decide)))
      nextPower _ positive localCert
    nlinarith [bitsUsed]
  have powerBound : (6*bits)^k ≤ 2^(bits * Nat.clog 2 (6*bits) / β) := calc
    _ ≤ (2^Nat.clog 2 (6*bits))^k := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) k
    _ = 2^(Nat.clog 2 (6*bits) * k) := (Nat.pow_mul ..).symm
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      apply (Nat.le_div_iff_mul_le beta).mpr
      calc
        _ = (β*k) * Nat.clog 2 (6*bits) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ bitsUsed
  have member : (p-1)/g ∈ Finset.Icc 1 (indexCap bits β) :=
    Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd groupPos (Nat.gcd_dvd_right ..))
      (Nat.gcd_pos_of_pos_left _ positive),
      indexLt.le.trans (Nat.mul_le_mul_left _ powerBound)⟩
  have indexDiv := Finset.dvd_lcm (f := id) member
  have whole := Nat.mul_dvd_mul (Nat.gcd_dvd_left E (p-1)) indexDiv
  simpa [saturate, g, Nat.mul_div_cancel' (Nat.gcd_dvd_right E (p-1))] using whole

end Cogentic
