import Cogentic.RandomizedL30Raw

/-!
# L30: constructing the global odd smooth lower bound

`Cogentic/RandomizedL30Younis.lean` reduces the Younis half of KeyBreak
Proposition H.3 to two analytic statements:

* `YounisOddRelativeShortInterval A` — relative short-interval density;
* `YounisOddGlobalLower B` — the global odd smooth lower bound
  `Ψ_odd(p², Y) ≥ B p² exp (-(1 + ε) t_p)`.

The first is genuinely a short-interval theorem.  The second, however, is a
*global* count: it only asks for many odd smooth orders below `p²`, and it can
be discharged by an explicit construction instead of by a contour argument.

This file removes `YounisOddGlobalLower` from the interface:

1. **Explicit construction.**  Given a finite set `P` of odd primes at most the
   smoothness cutoff `Y`, every `k`-subset `s ⊆ P` produces the order
   `2 · ∏_{q ∈ s} q`.  These orders are odd (`n ≡ 2 (mod 4)`), distinct, `Y`-smooth
   and at most `p²` whenever `2 Y^k ≤ p²`.  Their number is the binomial
   coefficient `P.card.choose k`, so
   `P.card.choose k ≤ globalOddSmoothCount`.

2. **The smallest counting input.**  `OddPrimeSupply Y J` is the finite
   statement that there are at least `J` odd primes at most `Y`.
   `younisOddGlobalLower_of_primeSupply` proves `YounisOddGlobalLower B` from
   this supply together with the single arithmetic inequality
   `B p² exp (-(1+ε)t) ≤ J.choose k`.  The corollary
   `younisOddGlobalLower_of_primeSupply_pow` replaces the binomial coefficient
   by the elementary lower bound `(J/k)^k` (valid for `1 ≤ k ≤ J`), so the input
   becomes the explicit threshold `B p² exp (-(1+ε)t) ≤ (J/k)^k`.

3. **A concrete cutoff, unconditionally.**  For the concrete cutoff
   `Y = exp (2 log p + 3 log 2) = 8 p²` every integer below `p²` is smooth, and
   the odd-half orders are exactly `2, 6, 10, …`.  Counting them gives
   `YounisOddGlobalLower 8` with no analytic input and no prime-counting
   hypothesis.  This is the analogue for L30 of
   `Cogentic.RandomizedL20_2SmoothLower.smoothNumberCountLower_twoPow`: a
   concrete pair for which the Prop is proved outright.

4. **`ConstructedInputs`.**  A version of `RawInputs` in which the opaque field
   `younis_global` is replaced by the explicit data `k`, `J`, `OddPrimeSupply`
   and the arithmetic inequality.  `ConstructedInputs.younis_global` proves the
   former field, and `toRawInputs` rebuilds `RawInputs`, so the global
   lower-bound Prop is no longer an assumption.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count is set
to zero: the constructed set always contains at least the order `2`, and the
binomial count is a genuine cardinality.
-/

namespace Cogentic.RandomizedL30Global

open Filter Real
open scoped Classical
open Cogentic.Randomized
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Raw

noncomputable section

/-! ## The explicit construction `2 · ∏ q` -/

/-- The orders obtained from `k`-subsets of a set `P` of odd primes:
`2 · ∏_{q ∈ s} q`.  The factor `2` makes the order divisible by `2` but not by
`4`, which is exactly the parity condition `IsOddHalfOrder`. -/
def constructedOddOrders (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (P.powersetCard k).image (fun s => 2 * ∏ q ∈ s, q)

/-- Membership in `constructedOddOrders`, in the form used by the proofs. -/
theorem mem_constructedOddOrders {P : Finset ℕ} {k m : ℕ} :
    m ∈ constructedOddOrders P k ↔
      ∃ s ∈ P.powersetCard k, 2 * ∏ q ∈ s, q = m := by
  rw [constructedOddOrders, Finset.mem_image]

/-- A product of distinct odd primes is odd. -/
theorem odd_prod_of_prime_ne_two {P s : Finset ℕ}
    (hs : s ⊆ P) (hP : ∀ q ∈ P, q.Prime ∧ q ≠ 2) :
    Odd (∏ q ∈ s, q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have haP : a ∈ P := hs (Finset.mem_insert_self a s)
    have hsP : s ⊆ P := fun q hq => hs (Finset.mem_insert_of_mem hq)
    exact ((hP a haP).1.odd_of_ne_two (hP a haP).2).mul (ih hsP)

/-- For odd `n`, the order `2 n` is `2` modulo `4`. -/
theorem two_mul_odd_mod_four {n : ℕ} (hn : Odd n) : (2 * n) % 4 = 2 := by
  obtain ⟨a, rfl⟩ := hn
  omega

/-- Every `k`-subset product is at most `Y^k`. -/
theorem prod_subset_le_cutoff_pow {P : Finset ℕ} {s : Finset ℕ} {k : ℕ} {Y : ℝ}
    (hs : s ∈ P.powersetCard k) (hle : ∀ q ∈ P, (q : ℝ) ≤ Y) :
    ((∏ q ∈ s, q : ℕ) : ℝ) ≤ Y ^ k := by
  have hsP : s ⊆ P := (Finset.mem_powersetCard.mp hs).1
  have hk : s.card = k := (Finset.mem_powersetCard.mp hs).2
  have hstep : (∏ q ∈ s, (q : ℝ)) ≤ ∏ _q ∈ s, Y :=
    Finset.prod_le_prod (fun q _ => Nat.cast_nonneg q)
      (fun q hq => hle q (hsP hq))
  rw [Finset.prod_const, hk, ← Nat.cast_prod] at hstep
  exact hstep

/-- **The constructed set consists of global odd smooth orders.**  If every
prime of `P` is odd and at most the cutoff `Y`, and `2 Y^k ≤ p²`, then each
`2 · ∏_{q ∈ s} q` lands in `globalOddSmoothOrders`. -/
theorem constructedOddOrders_subset_globalOdd
    {p t err : ℕ → ℝ} {n k : ℕ} {P : Finset ℕ}
    (hy2 : 2 ≤ smoothCutoff t err n)
    (hprime : ∀ q ∈ P, q.Prime ∧ q ≠ 2 ∧ (q : ℝ) ≤ smoothCutoff t err n)
    (hpow : 2 * (smoothCutoff t err n) ^ k ≤ p n ^ 2) :
    constructedOddOrders P k ⊆ globalOddSmoothOrders p t err n := by
  intro m hm
  rw [mem_constructedOddOrders] at hm
  obtain ⟨s, hs, rfl⟩ := hm
  have hsP : s ⊆ P := (Finset.mem_powersetCard.mp hs).1
  have hprod_le : ((∏ q ∈ s, q : ℕ) : ℝ) ≤ (smoothCutoff t err n) ^ k :=
    prod_subset_le_cutoff_pow hs (fun q hq => (hprime q hq).2.2)
  have hmreal : ((2 * ∏ q ∈ s, q : ℕ) : ℝ) ≤ p n ^ 2 := by
    have hcast : ((2 * ∏ q ∈ s, q : ℕ) : ℝ) =
        2 * ((∏ q ∈ s, q : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      norm_num
    rw [hcast]
    exact (mul_le_mul_of_nonneg_left hprod_le (by norm_num)).trans hpow
  have hmle : 2 * ∏ q ∈ s, q ≤ ⌊p n ^ 2⌋₊ := Nat.le_floor hmreal
  have hprod_pos : 0 < ∏ q ∈ s, q :=
    Finset.prod_pos fun q hq => (hprime q (hsP hq)).1.pos
  have hmpos : 1 ≤ 2 * ∏ q ∈ s, q := by omega
  rw [globalOddSmoothOrders, globalSmoothOrders, Finset.mem_filter, Finset.mem_filter]
  refine ⟨⟨Finset.mem_Icc.mpr ⟨hmpos, hmle⟩, ?_⟩, ?_⟩
  · intro r hr
    have hrprime : Nat.Prime r := Nat.prime_of_mem_primeFactors hr
    have hrdvd : r ∣ 2 * ∏ q ∈ s, q := Nat.dvd_of_mem_primeFactors hr
    rcases hrprime.dvd_mul.mp hrdvd with h2 | hprod
    · have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).mp h2
      rw [hr2]
      exact hy2
    · obtain ⟨q, hqs, hrq⟩ :=
        ((Nat.prime_iff.mp hrprime).dvd_finsetProd_iff (fun q : ℕ => q)).mp hprod
      have hqprime : Nat.Prime q := (hprime q (hsP hqs)).1
      have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hrprime hqprime).mp hrq
      rw [hrq']
      exact (hprime q (hsP hqs)).2.2
  · exact two_mul_odd_mod_four (odd_prod_of_prime_ne_two hsP (fun q hq => ⟨(hprime q hq).1, (hprime q hq).2.1⟩))

/-- **The constructed orders are distinct.**  Two `k`-subset products of odd
primes coincide only when the subsets coincide, by unique factorisation. -/
theorem constructedOddOrders_card (P : Finset ℕ) (k : ℕ)
    (hprime : ∀ q ∈ P, q.Prime ∧ q ≠ 2) :
    (constructedOddOrders P k).card = P.card.choose k := by
  rw [constructedOddOrders, Finset.card_image_of_injOn, Finset.card_powersetCard]
  intro s hs t ht heq
  have hsP : s ⊆ P := (Finset.mem_powersetCard.mp hs).1
  have htP : t ⊆ P := (Finset.mem_powersetCard.mp ht).1
  have hprod : (∏ q ∈ s, q) = (∏ q ∈ t, q) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : (0 : ℕ) < 2) heq
  ext q
  constructor
  · intro hq
    have hqprime : q.Prime := (hprime q (hsP hq)).1
    have hdvd : q ∣ ∏ x ∈ t, x := by
      rw [← hprod]
      exact Finset.dvd_prod_of_mem (f := fun x : ℕ => x) hq
    obtain ⟨r, hrt, hqr⟩ :=
      ((Nat.prime_iff.mp hqprime).dvd_finsetProd_iff (fun x : ℕ => x)).mp hdvd
    have hrprime : r.Prime := (hprime r (htP hrt)).1
    have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hqprime hrprime).mp hqr
    rwa [hqr']
  · intro hq
    have hqprime : q.Prime := (hprime q (htP hq)).1
    have hdvd : q ∣ ∏ x ∈ s, x := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem (f := fun x : ℕ => x) hq
    obtain ⟨r, hrs, hqr⟩ :=
      ((Nat.prime_iff.mp hqprime).dvd_finsetProd_iff (fun x : ℕ => x)).mp hdvd
    have hrprime : r.Prime := (hprime r (hsP hrs)).1
    have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hqprime hrprime).mp hqr
    rwa [hqr']

/-- **The binomial lower bound.**  A set `P` of odd primes at most `Y`, with
`2 Y^k ≤ p²`, gives at least `P.card.choose k` global odd smooth orders. -/
theorem globalOddSmoothCount_ge_choose
    {p t err : ℕ → ℝ} {n k : ℕ} {P : Finset ℕ}
    (hy2 : 2 ≤ smoothCutoff t err n)
    (hprime : ∀ q ∈ P, q.Prime ∧ q ≠ 2 ∧ (q : ℝ) ≤ smoothCutoff t err n)
    (hpow : 2 * (smoothCutoff t err n) ^ k ≤ p n ^ 2) :
    ((P.card.choose k : ℕ) : ℝ) ≤ globalOddSmoothCount p t err n := by
  have hcard : (constructedOddOrders P k).card = P.card.choose k :=
    constructedOddOrders_card P k fun q hq => ⟨(hprime q hq).1, (hprime q hq).2.1⟩
  have hsub : constructedOddOrders P k ⊆ globalOddSmoothOrders p t err n :=
    constructedOddOrders_subset_globalOdd hy2 hprime hpow
  have hle : (constructedOddOrders P k).card ≤ (globalOddSmoothOrders p t err n).card :=
    Finset.card_le_card hsub
  unfold globalOddSmoothCount
  rw [← hcard]
  exact_mod_cast hle

/-! ## The smallest explicit counting input -/

/-- **The explicit prime supply.**  There are at least `J` odd primes at most
`Y`.  This is the only counting information needed by the construction; it is
a finite, fully explicit statement, not a smooth-number estimate. -/
def OddPrimeSupply (Y : ℝ) (J : ℕ) : Prop :=
  ∃ P : Finset ℕ, (∀ q ∈ P, q.Prime ∧ q ≠ 2 ∧ (q : ℝ) ≤ Y) ∧ J ≤ P.card

/-- **`YounisOddGlobalLower` from the prime supply.**  If at each scale there
are `J n` odd primes at most the cutoff, `2 Y^k ≤ p²`, and the binomial
coefficient dominates the required count, then the global odd smooth lower
bound holds.  This replaces the analytic Prop by finite data. -/
theorem younisOddGlobalLower_of_primeSupply
    {p t err : ℕ → ℝ} {B : ℝ} {k J : ℕ → ℕ}
    (hy2 : ∀ n, 2 ≤ smoothCutoff t err n)
    (hsupply : ∀ n, OddPrimeSupply (smoothCutoff t err n) (J n))
    (hpow : ∀ n, 2 * (smoothCutoff t err n) ^ (k n) ≤ p n ^ 2)
    (hchoose : ∀ n,
      B * p n ^ 2 * exp (-(1 + err n) * t n) ≤ ((J n).choose (k n) : ℝ)) :
    YounisOddGlobalLower B p t err := by
  intro n
  obtain ⟨P, hP, hJP⟩ := hsupply n
  have hmono : ((J n).choose (k n) : ℝ) ≤ ((P.card.choose (k n) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_le_choose (k n) hJP
  have hcount := globalOddSmoothCount_ge_choose (p := p) (t := t) (err := err)
    (n := n) (k := k n) (P := P) (hy2 n) hP (hpow n)
  exact (hchoose n).trans (hmono.trans hcount)

/-- **`YounisOddGlobalLower` from an explicit power threshold.**  The binomial
coefficient is bounded below by `(J / k)^k` for `1 ≤ k ≤ J`, so the arithmetic
input can be stated as the single inequality
`B p² exp (-(1+ε)t) ≤ (J/k)^k`. -/
theorem younisOddGlobalLower_of_primeSupply_pow
    {p t err : ℕ → ℝ} {B : ℝ} {k J : ℕ → ℕ}
    (hy2 : ∀ n, 2 ≤ smoothCutoff t err n)
    (hsupply : ∀ n, OddPrimeSupply (smoothCutoff t err n) (J n))
    (hpow : ∀ n, 2 * (smoothCutoff t err n) ^ (k n) ≤ p n ^ 2)
    (hk1 : ∀ n, 1 ≤ k n) (hkJ : ∀ n, k n ≤ J n)
    (hthreshold : ∀ n, B * p n ^ 2 * exp (-(1 + err n) * t n) ≤
      ((J n : ℝ) / (k n : ℝ)) ^ (k n)) :
    YounisOddGlobalLower B p t err := by
  refine younisOddGlobalLower_of_primeSupply hy2 hsupply hpow ?_
  intro n
  exact (hthreshold n).trans
    (choose_ge_div_pow (J := J n) (k := k n) (hk1 n) (hkJ n))

/-! ## A concrete cutoff, proved outright -/

/-- The concrete cutoff exponent `t = 2 log p + 3 log 2`, so that
`Y = exp t = 8 p²` is strictly larger than `p²`. -/
def allSmoothT (p : ℕ → ℝ) : ℕ → ℝ :=
  fun n => 2 * Real.log (p n) + 3 * Real.log 2

/-- The concrete relative error `ε = 0`. -/
def allSmoothErr : ℕ → ℝ := fun _ => 0

/-- `exp (2 log p + 3 log 2) = 8 p²`. -/
theorem exp_allSmoothT {p : ℕ → ℝ} {n : ℕ} (hp : 0 < p n) :
    Real.exp (allSmoothT p n) = 8 * p n ^ 2 := by
  unfold allSmoothT
  rw [Real.exp_add]
  have h1 : Real.exp (2 * Real.log (p n)) = p n ^ 2 := by
    rw [show (2 : ℝ) * Real.log (p n) =
        Real.log (p n) + Real.log (p n) by ring,
      Real.exp_add, Real.exp_log hp]
    ring
  have h2 : Real.exp (3 * Real.log 2) = 8 := by
    rw [show (3 : ℝ) * Real.log 2 =
        Real.log 2 + Real.log 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [h1, h2]
  ring

/-- The concrete cutoff is `8 p²`. -/
theorem smoothCutoff_allSmooth {p : ℕ → ℝ} {n : ℕ} (hp : 0 < p n) :
    smoothCutoff (allSmoothT p) allSmoothErr n = 8 * p n ^ 2 := by
  unfold smoothCutoff allSmoothErr
  rw [show (1 + 0) * allSmoothT p n = allSmoothT p n by ring]
  exact exp_allSmoothT hp

/-- With the concrete cutoff `8 p²`, every integer in `[1, p²]` is smooth, so
the global smooth range is the full interval. -/
theorem globalSmoothOrders_allSmooth {p : ℕ → ℝ} {n : ℕ} (hp : 0 < p n) :
    globalSmoothOrders p (allSmoothT p) allSmoothErr n =
      Finset.Icc 1 ⌊p n ^ 2⌋₊ := by
  ext m
  rw [globalSmoothOrders, Finset.mem_filter]
  constructor
  · rintro ⟨hm, _⟩
    exact hm
  · intro hm
    refine ⟨hm, ?_⟩
    obtain ⟨_, h2⟩ := Finset.mem_Icc.mp hm
    intro q hq
    have hqle : q ≤ m := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
    have hmle : (m : ℝ) ≤ p n ^ 2 :=
      (Nat.cast_le.mpr h2).trans (Nat.floor_le (by positivity))
    have hcut : p n ^ 2 ≤ smoothCutoff (allSmoothT p) allSmoothErr n := by
      rw [smoothCutoff_allSmooth hp]
      nlinarith [sq_nonneg (p n)]
    exact (Nat.cast_le.mpr hqle).trans (hmle.trans hcut)

/-- **Counting the odd-half integers.**  Among `1, …, N` there are at least
`N / 4` integers `≡ 2 (mod 4)`, namely `2, 6, 10, …`. -/
theorem card_oddHalf_Icc_ge_div_four (N : ℕ) :
    N / 4 ≤ ((Finset.Icc 1 N).filter IsOddHalfOrder).card := by
  classical
  let S : Finset ℕ := (Finset.range (N / 4)).image (fun j => 4 * j + 2)
  have hcard : S.card = N / 4 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  have hsub : S ⊆ (Finset.Icc 1 N).filter IsOddHalfOrder := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    have hjlt : j < N / 4 := Finset.mem_range.mp hj
    have hj1 : j + 1 ≤ N / 4 := by omega
    have hmul : 4 * (j + 1) ≤ 4 * (N / 4) := Nat.mul_le_mul_left 4 hj1
    have hdiv : 4 * (N / 4) ≤ N := by
      rw [mul_comm]
      exact Nat.div_mul_le_self N 4
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    show (4 * j + 2) % 4 = 2
    omega
  calc N / 4 = S.card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **The concrete prime supply is non-vacuous.**  For the cutoff `8 p²`, the
single odd prime `3` already gives `OddPrimeSupply … 1`. -/
theorem oddPrimeSupply_allSmooth {p : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    OddPrimeSupply (smoothCutoff (allSmoothT p) allSmoothErr n) 1 := by
  have hp0 : 0 < p n := by linarith
  refine ⟨{3}, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_singleton] at hq
    subst q
    refine ⟨Nat.prime_three, by norm_num, ?_⟩
    rw [smoothCutoff_allSmooth hp0]
    have hsq : (2 : ℝ) ^ 2 ≤ p n ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ p n) 2
    norm_num at hsq
    push_cast
    linarith
  · simp

/-- **The global lower bound for the concrete cutoff `Y = 8 p²`.**  Since all
integers below `p²` are smooth, the odd-half orders alone give at least
`⌊p²⌋ / 4 ≥ 1` smooth orders, while the right-hand side is exactly `1` for
`B = 8`. -/
theorem younisOddGlobalLower_allSmooth (p : ℕ → ℝ) (hp : ∀ n, 2 ≤ p n) :
    YounisOddGlobalLower 8 p (allSmoothT p) allSmoothErr := by
  intro n
  have hp0 : 0 < p n := by linarith [hp n]
  have hN : 4 ≤ ⌊p n ^ 2⌋₊ := by
    apply Nat.le_floor
    have hpp : (2 : ℝ) ≤ p n := hp n
    have hsq : (2 : ℝ) ^ 2 ≤ p n ^ 2 := pow_le_pow_left₀ (by norm_num) hpp 2
    norm_num at hsq ⊢
    exact hsq
  have hcount : (1 : ℝ) ≤ globalOddSmoothCount p (allSmoothT p) allSmoothErr n := by
    unfold globalOddSmoothCount
    rw [globalOddSmoothOrders, globalSmoothOrders_allSmooth hp0]
    have hc := card_oddHalf_Icc_ge_div_four ⌊p n ^ 2⌋₊
    have hquarter : 1 ≤ ⌊p n ^ 2⌋₊ / 4 := by omega
    have hquarterR : (1 : ℝ) ≤ ((⌊p n ^ 2⌋₊ / 4 : ℕ) : ℝ) := by
      exact_mod_cast hquarter
    exact hquarterR.trans (by exact_mod_cast hc)
  have hL : 8 * p n ^ 2 * exp (-(1 + allSmoothErr n) * allSmoothT p n) = 1 := by
    have ht : exp (-(1 + allSmoothErr n) * allSmoothT p n) = 1 / (8 * p n ^ 2) := by
      unfold allSmoothErr
      rw [show -(1 + 0) * allSmoothT p n = -allSmoothT p n by ring,
        Real.exp_neg, exp_allSmoothT hp0]
      ring
    rw [ht]
    have hp2 : (0 : ℝ) < p n ^ 2 := by positivity
    field_simp
  rw [hL]
  exact hcount

/-! ## Removing the global field from `RawInputs` -/

/-- `RawInputs` with the opaque `younis_global` field replaced by explicit
finite counting data.  The relative short-interval density remains an analytic
input; the global lower bound is constructed. -/
structure ConstructedInputs where
  /-- The prime whose genus-two order is counted at scale `n`. -/
  p : ℕ → ℝ
  /-- The paper's `t_p`. -/
  t : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The prime is at least `2`. -/
  p_ge_two : ∀ n, 2 ≤ p n
  /-- `t_p ≥ 0`. -/
  t_nonneg : ∀ n, 0 ≤ t n
  /-- `ε ≥ -1`. -/
  err_ge_neg_one : ∀ n, -1 ≤ err n
  /-- The finite set of quintic models attached to order `m`. -/
  fibreModels : ℕ → ℕ → Finset ℕ
  /-- Relative short-interval density constant. -/
  A : ℝ
  /-- Global odd smooth lower-bound constant. -/
  B : ℝ
  /-- `A > 0`. -/
  A_pos : 0 < A
  /-- `B > 0`. -/
  B_pos : 0 < B
  /-- The interval-cardinality relation `A B ≥ 4`. -/
  AB_ge_four : 4 ≤ A * B
  /-- Younis's relative short-interval density for odd smooth orders. -/
  younis_relative : YounisOddRelativeShortInterval A p t err
  /-- The number of prime factors used in each constructed order. -/
  k : ℕ → ℕ
  /-- The number of odd primes supplied at each scale. -/
  J : ℕ → ℕ
  /-- The cutoff is at least `2`, so the factor `2` is smooth. -/
  cutoff_ge_two : ∀ n, 2 ≤ smoothCutoff t err n
  /-- **The explicit prime supply** replacing the global smooth count. -/
  prime_supply : ∀ n, OddPrimeSupply (smoothCutoff t err n) (J n)
  /-- **The range constraint** `2 Y^k ≤ p²`. -/
  smooth_pow_le : ∀ n, 2 * (smoothCutoff t err n) ^ (k n) ≤ p n ^ 2
  /-- **The arithmetic count inequality** `B p² exp (-(1+ε)t) ≤ J.choose k`. -/
  choose_lower : ∀ n,
    B * p n ^ 2 * exp (-(1 + err n) * t n) ≤ ((J n).choose (k n) : ℝ)
  /-- The raw LPP model count with the explicit loss `log p + 1`. -/
  lpp_raw_log : LPPRawLogModelCount p t err fibreModels

namespace ConstructedInputs

variable (S : ConstructedInputs)

/-- **The global odd smooth lower bound, now a theorem.** -/
theorem younis_global : YounisOddGlobalLower S.B S.p S.t S.err :=
  younisOddGlobalLower_of_primeSupply S.cutoff_ge_two S.prime_supply
    S.smooth_pow_le S.choose_lower

/-- **The reduction back to `RawInputs`.**  The global field is supplied by
`ConstructedInputs.younis_global`; every other field is carried through. -/
noncomputable def toRawInputs : RawInputs where
  p := S.p
  t := S.t
  err := S.err
  p_ge_two := S.p_ge_two
  t_nonneg := S.t_nonneg
  err_ge_neg_one := S.err_ge_neg_one
  fibreModels := S.fibreModels
  A := S.A
  B := S.B
  A_pos := S.A_pos
  B_pos := S.B_pos
  AB_ge_four := S.AB_ge_four
  younis_relative := S.younis_relative
  younis_global := S.younis_global
  lpp_raw_log := S.lpp_raw_log

/-- **The Younis odd central count** from the constructed inputs. -/
theorem younisOddCentralCount : YounisOddCentralCount S.p S.t S.err :=
  S.toRawInputs.younisOddCentralCount

/-- **The unrestricted Younis central count** from the constructed inputs. -/
theorem younisShortIntervalCount : YounisShortIntervalCount S.p S.t S.err :=
  S.toRawInputs.younisShortIntervalCount

/-- **The LPP per-order fibre count** from the constructed inputs. -/
theorem lppOrderFibreCount :
    LPPOrderFibreCount S.p S.t S.err S.fibreModels :=
  S.toRawInputs.lppOrderFibreCount

end ConstructedInputs

/-! ## Axiom audit -/

#print axioms mem_constructedOddOrders
#print axioms odd_prod_of_prime_ne_two
#print axioms two_mul_odd_mod_four
#print axioms prod_subset_le_cutoff_pow
#print axioms constructedOddOrders_subset_globalOdd
#print axioms constructedOddOrders_card
#print axioms globalOddSmoothCount_ge_choose
#print axioms younisOddGlobalLower_of_primeSupply
#print axioms younisOddGlobalLower_of_primeSupply_pow
#print axioms exp_allSmoothT
#print axioms smoothCutoff_allSmooth
#print axioms globalSmoothOrders_allSmooth
#print axioms card_oddHalf_Icc_ge_div_four
#print axioms oddPrimeSupply_allSmooth
#print axioms younisOddGlobalLower_allSmooth
#print axioms ConstructedInputs.younis_global
#print axioms ConstructedInputs.toRawInputs
#print axioms ConstructedInputs.younisOddCentralCount
#print axioms ConstructedInputs.younisShortIntervalCount
#print axioms ConstructedInputs.lppOrderFibreCount

end

end Cogentic.RandomizedL30Global
