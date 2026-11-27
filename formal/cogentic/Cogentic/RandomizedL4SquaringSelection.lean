import Cogentic.RandomizedL4Faithful
import Mathlib.Data.Nat.ChineseRemainder

/-!
# L4 squaring selection

This file attacks the primitive-selection residual of the faithful ideal-squaring
input, `Cogentic.RandomizedL4Faithful.SquaringPrimitiveSelection`.

For a reduced form `[A,b,C]` put `g = gcd(A, 2|b|)` and `q = A / g`.  The
squaring leading coefficient is `q²`.  The arithmetic root law
(`Cogentic.RandomizedL4Faithful.squaringRootLaw`) produces a root `b'` of
`-2N` modulo `q²`; the remaining point is to choose a root whose associated
coefficient makes the form primitive.

The main results are:

* `squaringPrimitiveSelection_of_odd`: for odd `N` the selection statement holds
  unconditionally.  The proof is a local construction at each prime dividing
  `q`, followed by a Chinese-remainder assembly.  At an odd prime `p` the key
  local fact is that, whenever `p^(2e) ∣ b²+2N`, one can choose a root whose
  associated quotient `(b²+2N)/p^(2e)` is a `p`-adic unit.  This is
  `odd_local_choice_int` below, proved by induction on `e` (the induction step
  is the classical observation that if every root is divisible by `p`, then
  `p²` divides `2N` and the problem descends to `N/p²`).

* `squaringPrimitiveSelection_of_twoAdic`: for arbitrary `N`, the same
  assembly reduces the selection statement to the explicit local condition
  `TwoAdicChoice N` at the single prime `2`.  `twoAdicChoice_of_odd` shows that
  this condition is vacuous for odd `N`, recovering the unconditional odd case.

Nothing here is a `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL4SquaringSelection

open Cogentic.RandomizedL4
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedL4Faithful

noncomputable section

/-! ## A local choice lemma at an odd prime

We work with an abstract integer `D` in place of `2N`, so that the induction can
descend from `D` to `D / p²`. -/

/-- **Odd-prime local choice.**  Let `p ≠ 2` be prime and `e > 0`.  If `D` has
a square root modulo `p^(2e)`, then there are `b s` with
`b² + D = p^(2e) * s` and `p ∤ s`. -/
private theorem odd_local_choice_int (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ e : ℕ, 0 < e → ∀ D : ℤ,
      (∃ b : ℤ, ∃ s : ℤ, b ^ 2 + D = ((p : ℤ) ^ (2 * e)) * s) →
      ∃ b : ℤ, ∃ s : ℤ,
        b ^ 2 + D = ((p : ℤ) ^ (2 * e)) * s ∧ ¬ (p : ℤ) ∣ s := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro he D hroot
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    set M : ℤ := (p : ℤ) ^ (2 * e) with hMdef
    have hpM : (p : ℤ) ∣ M := by
      dsimp only [M]
      exact dvd_pow_self (p : ℤ) (by omega)
    by_cases hnon : ∃ b s : ℤ, b ^ 2 + D = M * s ∧ ¬ (p : ℤ) ∣ b
    · obtain ⟨b, s, hEq, hpb⟩ := hnon
      by_cases hs : (p : ℤ) ∣ s
      · refine ⟨b + M, s + 2 * b + M, ?_, ?_⟩
        · rw [hMdef] at hEq ⊢
          calc
            (b + M) ^ 2 + D = (b ^ 2 + D) + 2 * b * M + M ^ 2 := by ring
            _ = M * s + 2 * b * M + M ^ 2 := by rw [hEq]
            _ = M * (s + 2 * b + M) := by ring
        · intro h
          have h2b : (p : ℤ) ∣ 2 * b := by
            have hsub := dvd_sub h (dvd_add hs hpM)
            have heq : s + 2 * b + M - (s + M) = 2 * b := by ring
            rwa [heq] at hsub
          rcases hpZ.dvd_mul.mp h2b with h2 | hb
          · have h2' : p ∣ 2 := by exact_mod_cast h2
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
          · exact hpb hb
      · exact ⟨b, s, hEq, hs⟩
    · -- every root is divisible by `p`
      have hall : ∀ b s : ℤ, b ^ 2 + D = M * s → (p : ℤ) ∣ b := by
        intro b s hEq
        by_contra hb
        exact hnon ⟨b, s, hEq, hb⟩
      obtain ⟨b0, s0, hroot0⟩ := hroot
      have hpb0 : (p : ℤ) ∣ b0 := hall b0 s0 hroot0
      have hp2M : (p : ℤ) ^ 2 ∣ M := by
        dsimp only [M]
        exact pow_dvd_pow (p : ℤ) (by omega : 2 ≤ 2 * e)
      have hp2b0 : (p : ℤ) ^ 2 ∣ b0 ^ 2 := pow_dvd_pow_of_dvd hpb0 2
      have hp2D : (p : ℤ) ^ 2 ∣ D := by
        have h1 : (p : ℤ) ^ 2 ∣ M * s0 := dvd_mul_of_dvd_left hp2M s0
        have h2 : (p : ℤ) ^ 2 ∣ b0 ^ 2 + D := by
          rw [hroot0]
          exact h1
        have h3 := dvd_sub h2 hp2b0
        simpa using h3
      obtain ⟨D', hD'⟩ := hp2D
      obtain ⟨y0, hy0⟩ := hpb0
      have hMfact : M = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * (e - 1)) := by
        dsimp only [M]
        rw [show 2 * e = 2 + 2 * (e - 1) by omega, pow_add]
      have hcancel : y0 ^ 2 + D' = (p : ℤ) ^ (2 * (e - 1)) * s0 := by
        have h := hroot0
        rw [hy0, hD', hMfact] at h
        have h' : (p : ℤ) ^ 2 * (y0 ^ 2 + D') =
            (p : ℤ) ^ 2 * ((p : ℤ) ^ (2 * (e - 1)) * s0) := by
          calc
            (p : ℤ) ^ 2 * (y0 ^ 2 + D')
                = (p * y0) ^ 2 + (p : ℤ) ^ 2 * D' := by ring
            _ = (p : ℤ) ^ 2 * ((p : ℤ) ^ (2 * (e - 1)) * s0) := by
              simpa [mul_assoc] using h
        exact mul_left_cancel₀ (pow_ne_zero 2 hpne) h'
      by_cases he1 : e = 1
      · subst he1
        have hM1 : M = (p : ℤ) ^ 2 := by
          dsimp only [M]
        by_cases hD'unit : (p : ℤ) ∣ D'
        · refine ⟨p * 1, 1 ^ 2 + D', ?_, ?_⟩
          · dsimp
            rw [hM1, hD']
            ring
          · intro h
            have h1 : (p : ℤ) ∣ 1 := by
              have := dvd_sub h hD'unit
              simpa using this
            exact hpZ.not_dvd_one h1
        · refine ⟨p * 0, 0 ^ 2 + D', ?_, ?_⟩
          · dsimp
            rw [hM1, hD']
            ring
          · simpa using hD'unit
      · -- induction step `e ≥ 2`
        have he'pos : 0 < e - 1 := by omega
        obtain ⟨y, s', hEq', hs'unit⟩ :=
          ih (e - 1) (by omega) he'pos D' ⟨y0, s0, hcancel⟩
        refine ⟨p * y, s', ?_, hs'unit⟩
        have hMstep : M = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * (e - 1)) := hMfact
        rw [hMstep]
        calc
          (p * y) ^ 2 + D = (p : ℤ) ^ 2 * (y ^ 2 + D') := by rw [hD']; ring
          _ = (p : ℤ) ^ 2 * ((p : ℤ) ^ (2 * (e - 1)) * s') := by rw [hEq']
          _ = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * (e - 1)) * s' := by ring

/-- **The explicit `2`-adic local choice.**  This is the only local input not
proved in this file.  It says that whenever `-2N` has a square root modulo
`2^(2e)` (`e > 0`), one can choose a root whose associated quotient
`(b²+2N)/2^(2e)` is odd.  For odd `N` this statement is vacuous
(`twoAdicChoice_of_odd`); for even `N` it is the precise extra condition needed
at the prime `2`. -/
def TwoAdicChoice (N : ℕ) : Prop :=
  ∀ e : ℕ, 0 < e →
    (∃ b : ℤ, ((2 : ℤ) ^ (2 * e)) ∣ b ^ 2 + 2 * (N : ℤ)) →
      ∃ b s : ℤ,
        b ^ 2 + 2 * (N : ℤ) = (2 : ℤ) ^ (2 * e) * s ∧ ¬ (2 : ℤ) ∣ s

/-- For odd `N` the modulus `4` obstruction makes the `2`-adic hypothesis
vacuous: `-2N ≡ 2 (mod 4)` is not a square. -/
theorem twoAdicChoice_of_odd (N : ℕ) (hN : Odd N) : TwoAdicChoice N := by
  intro e he hroot
  exfalso
  obtain ⟨b, hb⟩ := hroot
  have h4dvd : (4 : ℤ) ∣ b ^ 2 + 2 * (N : ℤ) := by
    have h4p : (4 : ℤ) ∣ (2 : ℤ) ^ (2 * e) := by
      have h : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ (2 * e) :=
        pow_dvd_pow (2 : ℤ) (by omega : 2 ≤ 2 * e)
      simpa using h
    exact dvd_trans h4p hb
  have hcast : ((b ^ 2 + 2 * (N : ℤ) : ℤ) : ZMod 4) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h4dvd
  push_cast at hcast
  have h4 : (4 : ZMod 4) = 0 := by decide
  obtain ⟨k, rfl⟩ := hN
  have hNcast : ((2 * k + 1 : ℕ) : ZMod 4) = 2 * (k : ZMod 4) + 1 := by
    push_cast
    ring
  have h2N : 2 * ((2 * k + 1 : ℕ) : ZMod 4) = 2 := by
    rw [hNcast]
    calc
      2 * (2 * (k : ZMod 4) + 1) = 4 * (k : ZMod 4) + 2 := by ring
      _ = 2 := by rw [h4]; ring
  have hb2 : (b : ZMod 4) ^ 2 = 2 := by
    rw [h2N] at hcast
    have h1 : (b : ZMod 4) ^ 2 = -2 := eq_neg_of_add_eq_zero_left hcast
    rwa [show (-2 : ZMod 4) = 2 by decide] at h1
  have hno : ∀ y : ZMod 4, y ^ 2 ≠ 2 := by decide
  exact hno (b : ZMod 4) hb2

/-- Product of pairwise coprime natural divisors divides a common multiple. -/
private theorem coprime_prod_dvd {ι : Type*} (s : Finset ι) (f : ι → ℕ) {z : ℕ}
    (hcop : (s : Set ι).Pairwise fun i j => (f i).Coprime (f j))
    (hdvd : ∀ i ∈ s, f i ∣ z) : (∏ i ∈ s, f i) ∣ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop_s : (s : Set ι).Pairwise fun i j => (f i).Coprime (f j) :=
      hcop.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    have ih' := ih hcop_s (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))
    have hcop_a : (f a).Coprime (∏ i ∈ s, f i) := by
      rw [Nat.coprime_prod_right_iff]
      intro i hi
      exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    exact hcop_a.mul_dvd_of_dvd_of_dvd (hdvd a (Finset.mem_insert_self a s)) ih'

/-- **Assembly step.**  Given suitable local choices at every prime dividing `q`,
choose a global root `b` and quotient `C` making `[q², b, C]` primitive. -/
private theorem exists_primitive_form_of_picks
    (N q : ℕ) (hq : 0 < q)
    (hpick : ∀ p ∈ q.primeFactors, ∃ b s : ℤ,
      b ^ 2 + 2 * (N : ℤ) = (p : ℤ) ^ (2 * q.factorization p) * s ∧
        ¬ (p : ℤ) ∣ s) :
    ∃ b : ℤ, ∃ C : ℕ, IsPrimitiveForm N ((q ^ 2 : ℕ) : ℤ) b (C : ℤ) := by
  classical
  choose bfun sfun hEqZ hprop using hpick
  let a : ℕ → ℕ := fun p => if hp : p ∈ q.primeFactors then (bfun p hp).natAbs else 0
  let sf : ℕ → ℕ := fun p => p ^ (2 * q.factorization p + 1)
  let l : List ℕ := q.primeFactors.toList
  have hnodup : l.Nodup := Finset.nodup_toList _
  have hco : l.Pairwise fun p p' => (sf p).Coprime (sf p') := by
    refine hnodup.pairwise_of_forall_ne ?_
    intro p hp p' hp' hne
    have hpq : p.Prime := Nat.prime_of_mem_primeFactors (by simpa [l] using hp)
    have hp'q : p'.Prime := Nat.prime_of_mem_primeFactors (by simpa [l] using hp')
    exact Nat.coprime_pow_primes _ _ hpq hp'q hne
  let xsub := Nat.chineseRemainderOfList a sf l hco
  let x : ℕ := xsub
  have hx : ∀ p ∈ q.primeFactors, x ≡ a p [MOD sf p] := by
    intro p hp
    exact xsub.prop p (by simpa [l] using (Finset.mem_toList.mpr hp))
  -- Nonnegativity of the local quotient.
  have hspos : ∀ (p : ℕ) (hp : p ∈ q.primeFactors), 0 ≤ sfun p hp := by
    intro p hp
    have hppos : (0 : ℤ) < (p : ℤ) ^ (2 * q.factorization p) := by
      exact pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) _
    have h := hEqZ p hp
    nlinarith [sq_nonneg (bfun p hp), Int.natCast_nonneg N]
  -- The local integer equation, transported to `ℕ`.
  have hnatEq : ∀ (p : ℕ) (hp : p ∈ q.primeFactors),
      (a p) ^ 2 + 2 * N = p ^ (2 * q.factorization p) * (sfun p hp).natAbs := by
    intro p hp
    have hs := hspos p hp
    have hap : a p = (bfun p hp).natAbs := by
      dsimp only [a]
      rw [dif_pos hp]
    have hcast : (((bfun p hp).natAbs ^ 2 + 2 * N : ℕ) : ℤ) =
        (((p ^ (2 * q.factorization p) * (sfun p hp).natAbs : ℕ)) : ℤ) := by
      calc
        (((bfun p hp).natAbs ^ 2 + 2 * N : ℕ) : ℤ)
            = ((bfun p hp).natAbs : ℤ) ^ 2 + 2 * (N : ℤ) := by push_cast; ring
        _ = (bfun p hp) ^ 2 + 2 * (N : ℤ) := by rw [Int.natAbs_sq]
        _ = (p : ℤ) ^ (2 * q.factorization p) * sfun p hp := hEqZ p hp
        _ = (p : ℤ) ^ (2 * q.factorization p) * ((sfun p hp).natAbs : ℤ) := by
              rw [Int.natAbs_of_nonneg hs]
        _ = (((p ^ (2 * q.factorization p) * (sfun p hp).natAbs : ℕ)) : ℤ) := by
              push_cast; ring
    have hnatEq' : (bfun p hp).natAbs ^ 2 + 2 * N =
        p ^ (2 * q.factorization p) * (sfun p hp).natAbs := by
      exact_mod_cast hcast
    rw [hap]
    exact hnatEq'
  -- The local condition modulo one higher power.
  have hmodsucc : ∀ (p : ℕ) (hp : p ∈ q.primeFactors),
      x ^ 2 + 2 * N ≡ p ^ (2 * q.factorization p) * (sfun p hp).natAbs
        [MOD p ^ (2 * q.factorization p + 1)] := by
    intro p hp
    have hx' := hx p hp
    have hsq : x ^ 2 + 2 * N ≡ (a p) ^ 2 + 2 * N [MOD sf p] := by
      simpa [sf] using (hx'.pow 2).add (Nat.ModEq.refl (2 * N))
    have := hsq.trans (by rw [hnatEq p hp])
    simpa [sf] using this
  -- Divisibility at each prime power.
  have hpdiv : ∀ p ∈ q.primeFactors, p ^ (2 * q.factorization p) ∣ x ^ 2 + 2 * N := by
    intro p hp
    have h := (hmodsucc p hp).of_dvd
      (pow_dvd_pow p (by omega : 2 * q.factorization p ≤ 2 * q.factorization p + 1))
    exact Nat.modEq_zero_iff_dvd.mp (h.trans (by
      rw [Nat.modEq_zero_iff_dvd]
      exact dvd_mul_right _ _))
  have hcop : (q.primeFactors : Set ℕ).Pairwise fun p p' =>
      (p ^ (2 * q.factorization p)).Coprime (p' ^ (2 * q.factorization p')) := by
    intro p hp p' hp' hne
    exact Nat.coprime_pow_primes _ _
      (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hp') hne
  have hq2dvd : q ^ 2 ∣ x ^ 2 + 2 * N := by
    have hprod := coprime_prod_dvd q.primeFactors
      (fun p => p ^ (2 * q.factorization p)) hcop hpdiv
    have hqprod : q = ∏ p ∈ q.primeFactors, p ^ q.factorization p := by
      simpa [Finsupp.prod, Nat.support_factorization] using
        (Nat.prod_factorization_pow_eq_self hq.ne').symm
    have hq2prod : q ^ 2 = ∏ p ∈ q.primeFactors, p ^ (2 * q.factorization p) := by
      conv_lhs => rw [hqprod]
      rw [pow_two, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_two, ← pow_mul]
      congr 1
      ring
    rwa [← hq2prod] at hprod
  let C : ℕ := (x ^ 2 + 2 * N) / q ^ 2
  have hCeq : q ^ 2 * C = x ^ 2 + 2 * N := Nat.mul_div_cancel' hq2dvd
  refine ⟨(x : ℤ), C, ?_, ?_, ?_⟩
  · -- positivity of the leading coefficient
    have : (0 : ℤ) < (q : ℤ) ^ 2 := by
      exact pow_pos (by exact_mod_cast hq) _
    push_cast
    exact this
  · -- discriminant identity
    push_cast
    have h := hCeq
    linarith
  · -- primitivity
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    rintro r hr hrdiv
    have hrq : r ∣ q := by
      have h1 : r ∣ ((q ^ 2 : ℤ).natAbs) :=
        (hrdiv.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left _ _)
      have h2 : r ∣ q ^ 2 := by simpa using h1
      exact hr.dvd_of_dvd_pow h2
    have hrmem : r ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrq, hq.ne'⟩
    have hrs : ¬ (r : ℤ) ∣ sfun r hrmem := hprop r hrmem
    have hCz : ¬ (r : ℤ) ∣ (C : ℤ) := by
      intro hCdiv
      set e : ℕ := q.factorization r with he
      set Q : ℕ := q / r ^ e with hQ
      have hpowdvd : r ^ e ∣ q := Nat.ordProj_dvd q r
      have hqeq : r ^ e * Q = q := Nat.mul_div_cancel' hpowdvd
      have hq2eq : q ^ 2 = r ^ (2 * e) * Q ^ 2 := by
        rw [← hqeq, mul_pow, ← pow_mul]
        congr 1
        ring
      -- congruence modulo `r^(2e+1)` in `ℤ`
      have hmod := hmodsucc r hrmem
      have hmodZ : ((x ^ 2 + 2 * N : ℕ) : ℤ) ≡
          (((r ^ (2 * e) * (sfun r hrmem).natAbs : ℕ)) : ℤ)
            [ZMOD ((r : ℤ) ^ (2 * e + 1))] := by
        exact Int.natCast_modEq_iff.mpr (by simpa [he] using hmod)
      have hsposr := hspos r hrmem
      have hscast : ((sfun r hrmem).natAbs : ℤ) = sfun r hrmem :=
        Int.natAbs_of_nonneg hsposr
      have hZe : ((q : ℤ) ^ 2 * (C : ℤ)) = ((x : ℤ) ^ 2 + 2 * (N : ℤ)) := by
        have h := hCeq
        linarith
      have hq2eqZ : ((q : ℤ) ^ 2) = (r : ℤ) ^ (2 * e) * (Q : ℤ) ^ 2 := by
        have := hq2eq
        exact_mod_cast this
      have hZeq' : ((x : ℤ) ^ 2 + 2 * (N : ℤ)) =
          (r : ℤ) ^ (2 * e) * ((Q : ℤ) ^ 2 * (C : ℤ)) := by
        rw [← hZe, hq2eqZ]
        ring
      have hmod' : (r : ℤ) ^ (2 * e) * ((Q : ℤ) ^ 2 * (C : ℤ)) ≡
          (r : ℤ) ^ (2 * e) * sfun r hrmem [ZMOD (r : ℤ) ^ (2 * e + 1)] := by
        simpa [hZeq', hscast] using hmodZ
      have hcancel : (Q : ℤ) ^ 2 * (C : ℤ) ≡ sfun r hrmem [ZMOD (r : ℤ)] := by
        have hcong : (r : ℤ) ^ (2 * e) * ((Q : ℤ) ^ 2 * (C : ℤ)) ≡
            (r : ℤ) ^ (2 * e) * sfun r hrmem
              [ZMOD (r : ℤ) ^ (2 * e) * (r : ℤ)] := by
          rw [show (r : ℤ) ^ (2 * e) * (r : ℤ) = (r : ℤ) ^ (2 * e + 1) by
            rw [pow_succ]]
          exact hmod'
        exact Int.ModEq.mul_left_cancel'
          (pow_ne_zero (2 * e) (by exact_mod_cast hr.ne_zero)) hcong
      have hrQ : (r : ℤ) ∣ (Q : ℤ) ^ 2 * (C : ℤ) :=
        dvd_mul_of_dvd_right hCdiv _
      have hrsZ : (r : ℤ) ∣ sfun r hrmem := (Int.ModEq.dvd_iff hcancel).mp hrQ
      exact hrs hrsZ
    have hrCz : (r : ℤ) ∣ (C : ℤ) := by
      have hrC : r ∣ (C : ℤ).natAbs := hrdiv.trans (Nat.gcd_dvd_right _ _)
      exact (Int.dvd_natAbs).mp (by exact_mod_cast hrC)
    exact hCz hrCz

/-- **The primitive-selection residual for odd `N`.** -/
theorem squaringPrimitiveSelection_of_odd (N : ℕ) (hN : Odd N) :
    SquaringPrimitiveSelection N := by
  intro A b C hred b' hb'
  obtain ⟨hdisc, hA, hlo, hhi, hAC, hbeq, hprim⟩ := hred
  let g : ℕ := Nat.gcd A (2 * b.natAbs)
  let q : ℕ := A / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hA
  have hgdvd : g ∣ A := Nat.gcd_dvd_left _ _
  have hqg : q * g = A := Nat.div_mul_cancel hgdvd
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hA hgdvd) hgpos
  -- The quotient `q` is odd.
  have hqodd : Odd q := by
    by_contra hqnot
    have hqeven : Even q := Nat.not_odd_iff_even.mp hqnot
    have h2q : 2 ∣ q := even_iff_two_dvd.mp hqeven
    have h2A : 2 ∣ A := by
      rw [← hqg]
      exact dvd_mul_of_dvd_left h2q g
    -- `b` is even because `b² = A C - 2N`.
    have hbZ : (b : ZMod 2) = 0 := by
      have h := congrArg (fun z : ℤ => (z : ZMod 2)) hdisc
      push_cast at h
      have hA0 : (A : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff A 2).mpr h2A
      have h2N0 : (2 : ZMod 2) * (N : ZMod 2) = 0 := by
        rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
      rw [hA0, h2N0] at h
      have hsq : (b : ZMod 2) ^ 2 = 0 := by simpa using h
      exact (by decide : ∀ x : ZMod 2, x ^ 2 = 0 → x = 0) (b : ZMod 2) hsq
    have h2b : (2 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp hbZ
    have h2bNat : 2 ∣ b.natAbs := by
      have h : ((2 : ℤ).natAbs ∣ b.natAbs) := Int.natAbs_dvd_natAbs.mpr h2b
      simpa using h
    have h2g : 2 ∣ g := by
      dsimp only [g]
      exact Nat.dvd_gcd h2A (dvd_mul_right 2 _)
    have h4A : 4 ∣ A := by
      rw [← hqg]
      obtain ⟨g', hg'⟩ := h2g
      obtain ⟨q', hq'⟩ := h2q
      refine ⟨g' * q', ?_⟩
      rw [hq', hg']
      ring
    have hACnat : A * C = b.natAbs ^ 2 + 2 * N := by
      have hZ : (A : ℤ) * (C : ℤ) = (b.natAbs : ℤ) ^ 2 + 2 * (N : ℤ) := by
        rw [Int.natAbs_sq]
        linarith
      exact_mod_cast hZ
    have h4b2 : 4 ∣ b.natAbs ^ 2 := by
      obtain ⟨k, hk⟩ := h2bNat
      refine ⟨k ^ 2, ?_⟩
      rw [hk]
      ring
    have h4AC : 4 ∣ A * C := dvd_mul_of_dvd_left h4A C
    have h42N : 4 ∣ 2 * N := by
      rw [hACnat] at h4AC
      exact (Nat.dvd_add_right h4b2).mp h4AC
    have h2N : 2 ∣ N := by
      obtain ⟨k, hk⟩ := h42N
      refine ⟨k, ?_⟩
      omega
    rcases hN with ⟨m, hm⟩
    rcases h2N with ⟨k, hk⟩
    omega
  -- Local choices at every prime factor of `q`.
  have hpick : ∀ p ∈ q.primeFactors, ∃ b s : ℤ,
      b ^ 2 + 2 * (N : ℤ) = (p : ℤ) ^ (2 * q.factorization p) * s ∧
        ¬ (p : ℤ) ∣ s := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hepos : 0 < q.factorization p :=
      hpprime.factorization_pos_of_dvd hqpos.ne' hpq
    have hp2 : p ≠ 2 := by
      intro h
      subst h
      exact Nat.not_even_iff_odd.mpr hqodd (even_iff_two_dvd.mpr hpq)
    -- the root survives reduction to `p^(2e)`
    have hpowe_dvd_q2 : ((p ^ (2 * q.factorization p) : ℕ) : ℤ) ∣ (q : ℤ) ^ 2 := by
      have h : p ^ (2 * q.factorization p) ∣ q ^ 2 := by
        have h1 : p ^ (q.factorization p) ∣ q := Nat.ordProj_dvd q p
        have h2 : (p ^ (q.factorization p)) ^ 2 ∣ q ^ 2 := pow_dvd_pow_of_dvd h1 2
        convert h2 using 1
        rw [← pow_mul]
        congr 1
        ring
      exact_mod_cast h
    have hroot : ∃ b0 : ℤ, ∃ s : ℤ,
        b0 ^ 2 + 2 * (N : ℤ) = (p : ℤ) ^ (2 * q.factorization p) * s := by
      obtain ⟨s, hs⟩ := hpowe_dvd_q2.trans hb'
      refine ⟨b', s, ?_⟩
      have hcast : ((p ^ (2 * q.factorization p) : ℕ) : ℤ) =
          (p : ℤ) ^ (2 * q.factorization p) := by push_cast; ring
      rw [← hcast]
      exact hs
    exact odd_local_choice_int p hpprime hp2 (q.factorization p) hepos (2 * (N : ℤ)) hroot
  have hmain := exists_primitive_form_of_picks N q hqpos hpick
  simpa [q, g] using hmain

/-- **Reduction of the primitive-selection residual to the explicit `2`-adic
local condition.**  All odd-prime local choices are constructed in this file;
`TwoAdicChoice` is exactly the remaining local input at `2`. -/
theorem squaringPrimitiveSelection_of_twoAdic (N : ℕ) (h2 : TwoAdicChoice N) :
    SquaringPrimitiveSelection N := by
  intro A b C hred b' hb'
  obtain ⟨hdisc, hA, hlo, hhi, hAC, hbeq, hprim⟩ := hred
  let g : ℕ := Nat.gcd A (2 * b.natAbs)
  let q : ℕ := A / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hA
  have hgdvd : g ∣ A := Nat.gcd_dvd_left _ _
  have hqg : q * g = A := Nat.div_mul_cancel hgdvd
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hA hgdvd) hgpos
  have hpick : ∀ p ∈ q.primeFactors, ∃ b s : ℤ,
      b ^ 2 + 2 * (N : ℤ) = (p : ℤ) ^ (2 * q.factorization p) * s ∧
        ¬ (p : ℤ) ∣ s := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hepos : 0 < q.factorization p :=
      hpprime.factorization_pos_of_dvd hqpos.ne' hpq
    have hpowe_dvd_q2 : ((p ^ (2 * q.factorization p) : ℕ) : ℤ) ∣ (q : ℤ) ^ 2 := by
      have h : p ^ (2 * q.factorization p) ∣ q ^ 2 := by
        have h1 : p ^ (q.factorization p) ∣ q := Nat.ordProj_dvd q p
        have h2 : (p ^ (q.factorization p)) ^ 2 ∣ q ^ 2 := pow_dvd_pow_of_dvd h1 2
        convert h2 using 1
        rw [← pow_mul]
        congr 1
        ring
      exact_mod_cast h
    have hroot : ∃ b0 : ℤ, ∃ s : ℤ,
        b0 ^ 2 + 2 * (N : ℤ) = (p : ℤ) ^ (2 * q.factorization p) * s := by
      obtain ⟨s, hs⟩ := hpowe_dvd_q2.trans hb'
      refine ⟨b', s, ?_⟩
      have hcast : ((p ^ (2 * q.factorization p) : ℕ) : ℤ) =
          (p : ℤ) ^ (2 * q.factorization p) := by push_cast; ring
      rw [← hcast]
      exact hs
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨b0, s0, hEq0⟩ := hroot
      exact h2 (q.factorization 2) hepos ⟨b0, ⟨s0, by simpa using hEq0⟩⟩
    · exact odd_local_choice_int p hpprime hp2 (q.factorization p) hepos
        (2 * (N : ℤ)) hroot
  have hmain := exists_primitive_form_of_picks N q hqpos hpick
  simpa [q, g] using hmain

/-- The odd case also follows from the general reduction, since the `2`-adic
choice is vacuous for odd `N`. -/
theorem squaringPrimitiveSelection_of_odd_viaTwoAdic (N : ℕ) (hN : Odd N) :
    SquaringPrimitiveSelection N :=
  squaringPrimitiveSelection_of_twoAdic N (twoAdicChoice_of_odd N hN)

/-! ## Axiom audit -/

#print axioms twoAdicChoice_of_odd
#print axioms squaringPrimitiveSelection_of_odd
#print axioms squaringPrimitiveSelection_of_twoAdic
#print axioms squaringPrimitiveSelection_of_odd_viaTwoAdic

end

end Cogentic.RandomizedL4SquaringSelection
