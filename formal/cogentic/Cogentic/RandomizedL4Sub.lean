import Cogentic.RandomizedL4

set_option linter.style.haveILetI false

/-!
# L4Sub: elementary sub-lemmas of the L4 principal-genus bridge

`Cogentic.RandomizedL4` isolates three algebraic ingredients behind the private
quadratic-form supply:

* `PrincipalGenusBridge` --- principal-genus tuples give a root of `-2 * N`
  modulo the product;
* `BandProductSmall` --- the product of one prime from each band is at most
  `√(2 * N)`;
* `exists_reducedForm_of_centered_root` --- a centred root plus smallness gives a
  reduced primitive form.

This file rewrites the first two ingredients as finer statements that are either
elementary or exactly the missing arithmetic input, and restates the third in
the local-splitting form produced by the CRT step.

## What is proved here

* `LocallySplit` (`-2 * N` is a square modulo `p`) and its equivalence with
  integer divisibility.
* The CRT assembly `locallySplit_mul` / `locallySplit_finset_prod`: local roots
  modulo pairwise coprime moduli produce a root modulo their product.
* The ramification/splitting implication
  `locallySplit_of_legendreSym` and its converse: for an odd prime `p ∤ N`,
  local splitting is equivalent to `legendreSym p (-2 * N) = 1`.  This is the
  elementary content of the splitting character at the band primes.
* `PrincipalGenusBridge` is *equivalent* to the product-level local-splitting
  statement `PrincipalGenusSplit`; the CRT step is the only content beyond that.
* Bands whose primes are split (`BandSplit`) satisfy `PrincipalGenusBridge`
  with no further genus-theoretic input, and `BandSplit` follows from the
  manuscript's `splitPrimeBin` membership.
* `BandProductSmall` follows from a per-band maximum bound, from a uniform band
  bound, and from the paper-shaped condition `∏ max(P i) ≤ √(2N)`.
* `exists_reducedForm_of_locallySplit` and the `IsReducedForm` witness form of
  the reduced-form construction; reduced forms are primitive forms.

The Gauss composition and ideal-squaring laws of `RandomizedL4` are kept as the
explicit `Prop`s `FormCompositionLaw` and `IdealSquaringLaw` (re-exported
through `L4SubInputs`).  Nothing here is a `sorry`, `admit`, `axiom`, or
`native_decide`, and no loss is set to zero.
-/

namespace Cogentic.RandomizedL4Sub

open Finset
open scoped BigOperators

open Cogentic.RandomizedL4
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedReducedFormSupply
open Cogentic.RandomizedEpochPrivate

noncomputable section

/-!
## Section 1: Local splitting and CRT

`LocallySplit N p` records the local condition actually used by the centred-root
construction: `-2 * N` is a square modulo `p`.  For a prime `p` this is exactly
the splitting condition `χ_{-8N}(p) = 1`.
-/

/-- `-2 * N` is a square modulo `p`. -/
def LocallySplit (N p : ℕ) : Prop :=
  ∃ x : ZMod p, x ^ 2 = -2 * (N : ZMod p)

/-- `LocallySplit` is the existence of a square root, in `IsSquare` form. -/
theorem locallySplit_iff_isSquare {N p : ℕ} :
    LocallySplit N p ↔ IsSquare (-2 * (N : ZMod p)) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hx, pow_two]⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [hx, pow_two]⟩

/-- For a positive modulus, local splitting is exactly integral divisibility of
`b ^ 2 + 2 * N` by `p`. -/
theorem locallySplit_iff_int_dvd (N p : ℕ) [NeZero p] :
    LocallySplit N p ↔ ∃ b : ℤ, (p : ℤ) ∣ b ^ 2 + 2 * (N : ℤ) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(x.val : ℤ), ?_⟩
    have h : (((x.val : ℤ) ^ 2 + 2 * (N : ℤ) : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, hx]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  · rintro ⟨b, hb⟩
    refine ⟨(b : ZMod p), ?_⟩
    have h : (((b ^ 2 + 2 * (N : ℤ) : ℤ)) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb
    push_cast at h
    linear_combination h

/-- A root modulo a multiple restricts to a root modulo any divisor. -/
theorem locallySplit_of_dvd {N d M : ℕ} (hd : d ∣ M) (h : LocallySplit N M) :
    LocallySplit N d := by
  obtain ⟨x, hx⟩ := h
  refine ⟨ZMod.castHom hd (ZMod d) x, ?_⟩
  have h := congrArg (ZMod.castHom hd (ZMod d)) hx
  simp only [map_pow, map_mul, map_neg, map_ofNat, map_natCast] at h
  exact h

/-- CRT for two local roots: a root modulo each of two coprime moduli assembles
to a root modulo the product. -/
theorem locallySplit_mul_of_coprime {N m n : ℕ} (hcop : m.Coprime n)
    (hm : LocallySplit N m) (hn : LocallySplit N n) :
    LocallySplit N (m * n) := by
  obtain ⟨x, hx⟩ := hm
  obtain ⟨y, hy⟩ := hn
  let e := ZMod.chineseRemainder hcop
  refine ⟨e.symm (x, y), ?_⟩
  apply e.injective
  rw [map_pow, map_mul, map_neg, map_ofNat, map_natCast, e.apply_symm_apply]
  ext
  · simpa using hx
  · simpa using hy

/-- CRT over a finite pairwise coprime family. -/
theorem locallySplit_finset_prod {ι : Type*} (N : ℕ) (s : Finset ι) (f : ι → ℕ)
    (hcop : (s : Set ι).Pairwise fun i j => (f i).Coprime (f j))
    (h : ∀ i ∈ s, LocallySplit N (f i)) :
    LocallySplit N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h1 : LocallySplit N 1 := ⟨0, Subsingleton.elim _ _⟩
      simpa using h1
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hcop_a : (f a).Coprime (∏ i ∈ s, f i) :=
        Nat.Coprime.prod_right fun i hi =>
          hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
            (fun h => ha (h ▸ hi))
      have hprod : LocallySplit N (∏ i ∈ s, f i) :=
        ih (hcop.mono fun _ hx => Finset.mem_insert_of_mem hx)
          fun i hi => h i (Finset.mem_insert_of_mem hi)
      exact locallySplit_mul_of_coprime hcop_a (h a (Finset.mem_insert_self a s)) hprod

/-!
## Section 2: Ramification and the splitting character

For an odd prime `p ∤ N`, `-2 * N` is a unit modulo `p`, so Euler's criterion
identifies local splitting with `legendreSym p (-2 * N) = 1`.  The 2-part is
handled by the coprimality hypothesis `p ≠ 2`; no odd-prime ramification can
occur when `p ∤ N`.
-/

/-- `-2 * N` is nonzero modulo an odd prime `p` that does not divide `N`. -/
theorem intCast_neg_two_mul_N_ne_zero {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hndvd : ¬ p ∣ N) :
    ((-2 * (N : ℤ) : ℤ) : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : (p : ℤ) ∣ (-2 * (N : ℤ) : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hdvd' : (p : ℤ) ∣ (2 * N : ℤ) := by
    have : (p : ℤ) ∣ -(2 * (N : ℤ)) := by simpa using hdvd
    exact dvd_neg.mp this
  have h2N : p ∣ 2 * N := Int.natCast_dvd_natCast.mp hdvd'
  rcases hp.dvd_mul.mp h2N with h2 | hN
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · exact hndvd hN

/-- The splitting character at an odd band prime: `legendreSym p (-2 * N) = 1`
implies local splitting.  This is the ramification step used by the manuscript's
`splitPrimeBin` bands. -/
theorem locallySplit_of_legendreSym {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hndvd : ¬ p ∣ N)
    (hleg : @legendreSym p ⟨hp⟩ (-2 * (N : ℤ)) = 1) :
    LocallySplit N p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne := intCast_neg_two_mul_N_ne_zero hp hp2 hndvd
  have hs : IsSquare ((-2 * (N : ℤ) : ℤ) : ZMod p) :=
    (legendreSym.eq_one_iff p hne).mp hleg
  obtain ⟨x, hx⟩ := hs
  refine ⟨x, ?_⟩
  rw [pow_two, ← hx]
  push_cast
  ring

/-- Converse splitting implication: a local root forces the Legendre symbol to
be `1` at an odd band prime. -/
theorem legendreSym_of_locallySplit {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hndvd : ¬ p ∣ N) (h : LocallySplit N p) :
    @legendreSym p ⟨hp⟩ (-2 * (N : ℤ)) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne := intCast_neg_two_mul_N_ne_zero hp hp2 hndvd
  refine (legendreSym.eq_one_iff p hne).mpr ?_
  obtain ⟨x, hx⟩ := h
  refine ⟨x, ?_⟩
  simpa [pow_two] using hx.symm

/-- Local splitting is equivalent to the splitting character for odd band
primes. -/
theorem locallySplit_iff_legendreSym {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hndvd : ¬ p ∣ N) :
    LocallySplit N p ↔ @legendreSym p ⟨hp⟩ (-2 * (N : ℤ)) = 1 :=
  ⟨legendreSym_of_locallySplit hp hp2 hndvd, locallySplit_of_legendreSym hp hp2 hndvd⟩

/-- There is no root of `-2 * N` modulo `2 ^ k` for `k ≥ 2` when `N` is odd:
`-2 * N ≡ 2 (mod 4)` is not a square.  This is the 2-adic ramification
obstruction, and the reason the band modulus is always odd. -/
theorem not_locallySplit_two_pow_of_odd {N k : ℕ} (hN : Odd N) (hk : 2 ≤ k) :
    ¬ LocallySplit N (2 ^ k) := by
  rintro ⟨x, hx⟩
  have h4dvd : 4 ∣ 2 ^ k := by
    have : (2 : ℕ) ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
    simpa using this
  have hcast := congrArg (ZMod.castHom h4dvd (ZMod 4)) hx
  rw [map_pow, map_mul, map_neg, map_ofNat, map_natCast] at hcast
  obtain ⟨m, rfl⟩ := hN
  have hrhs : (-2 * ((2 * m + 1 : ℕ) : ZMod 4)) = 2 := by
    push_cast
    have h4 : (4 : ZMod 4) = 0 := rfl
    have hneg2 : (-2 : ZMod 4) = 2 := by decide
    calc
      -2 * (2 * (m : ZMod 4) + 1) =
          -(4 : ZMod 4) * (m : ZMod 4) + (-2 : ZMod 4) := by ring
      _ = 2 := by rw [h4, neg_zero, zero_mul, zero_add, hneg2]
  rw [hrhs] at hcast
  have hno : ∀ y : ZMod 4, y ^ 2 ≠ 2 := by decide
  exact hno (ZMod.castHom h4dvd (ZMod 4) x) hcast

/-- The manuscript's split-prime bands satisfy local splitting: every element of
`splitPrimeBin` splits for `-2 * N`. -/
theorem locallySplit_of_mem_splitPrimeBin {N A B p : ℕ} (hN : Odd N)
    (hp : p ∈ splitPrimeBin N A B) : LocallySplit N p := by
  obtain ⟨hbin, hcop, hleg⟩ := (mem_splitPrimeBin_iff hN).mp hp
  have hprime : p.Prime := (Finset.mem_filter.mp hbin).2
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    have h2dvd : 2 ∣ 2 * N := dvd_mul_right 2 N
    have hgm : Nat.gcd 2 (2 * N) = 1 := hcop.gcd_eq_one
    have hdiv : 2 ∣ Nat.gcd 2 (2 * N) := Nat.dvd_gcd (dvd_refl 2) h2dvd
    rw [hgm] at hdiv
    omega
  have hndvd : ¬ p ∣ N := by
    intro hdiv
    have hp2N : p ∣ 2 * N := hdiv.trans (dvd_mul_left N 2)
    exact hprime.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hp2N)
  exact locallySplit_of_legendreSym hprime hp2 hndvd hleg

/-!
## Section 3: The principal-genus bridge, split into CRT plus local splitting

`PrincipalGenusSplit` is the product-level local-splitting statement.  The only
difference between it and `PrincipalGenusBridge` is the transfer between a
`ZMod` root and an integer divisibility witness, which is elementary for a
positive product.  The genus-theoretic input is therefore exactly
`PrincipalGenusSplit`; on the manuscript's bands it is discharged by `BandSplit`.
-/

/-- Product-level local splitting for principal-genus tuples. -/
def PrincipalGenusSplit (N : ℕ) (m : ℕ) (P : Fin m → Finset ℕ) : Prop :=
  ∀ t : ∀ i : Fin m, {p : ℕ // p ∈ P i},
    (∏ i, genusMap N (t i).1) = 1 →
    Function.Injective (fun i => (t i).1) →
      LocallySplit N (∏ i, (t i).1)

/-- `PrincipalGenusBridge` and `PrincipalGenusSplit` differ only by the
elementary `ZMod`/integer-divisibility transfer. -/
theorem principalGenusBridge_iff_split {N m : ℕ} {P : Fin m → Finset ℕ}
    (hpos : ∀ i, ∀ p ∈ P i, 0 < p) :
    PrincipalGenusBridge N m P ↔ PrincipalGenusSplit N m P := by
  constructor
  · intro h t hgenus hinj
    have hprod : 0 < ∏ i, (t i).1 :=
      Finset.prod_pos fun i _ => hpos i (t i).1 (t i).2
    haveI : NeZero (∏ i, (t i).1) := ⟨hprod.ne'⟩
    obtain ⟨b, hb⟩ := h t hgenus hinj
    exact (locallySplit_iff_int_dvd N (∏ i, (t i).1)).mpr ⟨b, hb⟩
  · intro h t hgenus hinj
    have hprod : 0 < ∏ i, (t i).1 :=
      Finset.prod_pos fun i _ => hpos i (t i).1 (t i).2
    haveI : NeZero (∏ i, (t i).1) := ⟨hprod.ne'⟩
    exact (locallySplit_iff_int_dvd N (∏ i, (t i).1)).mp (h t hgenus hinj)

/-- A band family all of whose primes split. -/
def BandSplit (N : ℕ) (m : ℕ) (P : Fin m → Finset ℕ) : Prop :=
  ∀ i, ∀ p ∈ P i, LocallySplit N p

/-- **CRT reduction of the principal-genus bridge.**  If every band prime splits,
then the CRT assembles the local roots into a root modulo the full product, and
no genus-theoretic hypothesis is needed. -/
theorem principalGenusBridge_of_bandSplit {N m : ℕ} {P : Fin m → Finset ℕ}
    (hsplit : BandSplit N m P) (hprime : ∀ i, ∀ p ∈ P i, p.Prime) :
    PrincipalGenusBridge N m P := by
  intro t _ hinj
  have hprod : 0 < ∏ i, (t i).1 :=
    Finset.prod_pos fun i _ => (hprime i (t i).1 (t i).2).pos
  have hcop : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).Pairwise
      fun i j => ((t i).1).Coprime ((t j).1) := by
    intro i _ j _ hij
    have hne : (t i).1 ≠ (t j).1 := fun h => hij (hinj h)
    exact (Nat.coprime_primes (hprime i (t i).1 (t i).2)
      (hprime j (t j).1 (t j).2)).mpr hne
  have hloc : LocallySplit N (∏ i, (t i).1) :=
    locallySplit_finset_prod N Finset.univ (fun i => (t i).1) hcop
      fun i _ => hsplit i (t i).1 (t i).2
  haveI : NeZero (∏ i, (t i).1) := ⟨hprod.ne'⟩
  obtain ⟨b, hb⟩ := (locallySplit_iff_int_dvd N (∏ i, (t i).1)).mp hloc
  exact ⟨b, hb⟩

/-- Bands contained in `splitPrimeBin` satisfy `BandSplit`. -/
theorem bandSplit_of_subset_splitPrimeBin {N m : ℕ} {P : Fin m → Finset ℕ}
    {A B : ℕ} (hN : Odd N) (hsub : ∀ i, P i ⊆ splitPrimeBin N A B) :
    BandSplit N m P :=
  fun i _p hp => locallySplit_of_mem_splitPrimeBin hN (hsub i hp)

/-!
## Section 4: The small-band-product bound

`BandProductSmall` is reduced to a per-band maximum bound and to a uniform
per-band bound.  The paper's "total bits" constraint is the statement
`∏ max(P i) ≤ √(2N)`.
-/

/-- The band product is at most `√(2N)` when each band is bounded by its maximum. -/
def BandProductSmallByMax (N : ℕ) (m : ℕ) (P : Fin m → Finset ℕ) : Prop :=
  (∏ i, (P i).sup id) ^ 2 ≤ 2 * N

/-- A per-band maximum bound implies the small-band-product input. -/
theorem bandProductSmall_of_max {N m : ℕ} {P : Fin m → Finset ℕ}
    (h : BandProductSmallByMax N m P) : BandProductSmall N m P := by
  intro t
  have hle : ∏ i, (t i).1 ≤ ∏ i, (P i).sup id :=
    Finset.prod_le_prod' fun i _ => Finset.le_sup (f := id) (t i).2
  exact (Nat.pow_le_pow_left hle 2).trans h

/-- The paper-shaped form of the band bound: `∏ max(P i) ≤ √(2N)`. -/
theorem bandProductSmall_of_max_le_sqrt {N m : ℕ} {P : Fin m → Finset ℕ}
    (h : ∏ i, (P i).sup id ≤ Nat.sqrt (2 * N)) : BandProductSmall N m P := by
  intro t
  have hle : ∏ i, (t i).1 ≤ Nat.sqrt (2 * N) :=
    (Finset.prod_le_prod' fun i _ => Finset.le_sup (f := id) (t i).2).trans h
  exact (Nat.pow_le_pow_left hle 2).trans (Nat.sqrt_le' (2 * N))

/-- A uniform bound `p ≤ B` on every band prime, with `B ^ m ≤ √(2N)`. -/
theorem bandProductSmall_of_uniform_bound {N m B : ℕ} {P : Fin m → Finset ℕ}
    (hB : ∀ i, ∀ p ∈ P i, p ≤ B) (hBm : (B ^ m) ^ 2 ≤ 2 * N) :
    BandProductSmall N m P := by
  intro t
  have hle : ∏ i, (t i).1 ≤ B ^ m := by
    have := Finset.prod_le_prod' (s := Finset.univ)
      (f := fun i => (t i).1) (g := fun _ => B) fun i _ => hB i (t i).1 (t i).2
    simpa using this
  exact (Nat.pow_le_pow_left hle 2).trans hBm

/-- Sanity check for the empty band family. -/
theorem bandProductSmall_zero_iff (N : ℕ) (P : Fin 0 → Finset ℕ) :
    BandProductSmall N 0 P ↔ 1 ≤ 2 * N := by
  constructor
  · intro h
    simpa using h (fun i => nomatch i)
  · intro h t
    simpa using h

/-!
## Section 5: The reduced-form construction

The centred-root theorem of `RandomizedL4` is restated with the local-splitting
input produced by the CRT step, and unpacked into an `IsReducedForm` witness.
-/

/-- **Reduced-form construction from a local root.**  If `A > 0`, `(A, 2N) = 1`,
`A ^ 2 ≤ 2N`, and `-2N` is a square modulo `A`, then `A` is the leading
coefficient of a canonical reduced primitive form of discriminant `-8N`. -/
theorem exists_reducedForm_of_locallySplit {N A : ℕ} (hA : 0 < A)
    (hcop : Nat.Coprime A (2 * N)) (hsmall : A ^ 2 ≤ 2 * N)
    (hsplit : LocallySplit N A) :
    ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = A := by
  haveI : NeZero A := ⟨hA.ne'⟩
  obtain ⟨b, hb⟩ := (locallySplit_iff_int_dvd N A).mp hsplit
  exact exists_reducedForm_of_centered_root hA hcop hsmall hb

/-- The construction in `IsReducedForm` form, exposing the middle coefficient
and the computed third coefficient. -/
theorem exists_isReducedForm_of_locallySplit {N A : ℕ} (hA : 0 < A)
    (hcop : Nat.Coprime A (2 * N)) (hsmall : A ^ 2 ≤ 2 * N)
    (hsplit : LocallySplit N A) :
    ∃ (b : ℤ) (C : ℕ), IsReducedForm N A b C := by
  obtain ⟨f, hf, hfA⟩ := exists_reducedForm_of_locallySplit hA hcop hsmall hsplit
  rcases f with ⟨A', b, C⟩
  simp only at hfA
  subst hfA
  exact ⟨b, C, mem_reducedForms.mp hf⟩

/-- Canonical reduced forms are primitive in the sense used by the composition
and ideal-squaring laws. -/
theorem isPrimitiveForm_of_isReducedForm {N A : ℕ} {b : ℤ} {C : ℕ}
    (h : IsReducedForm N A b C) : IsPrimitiveForm N (A : ℤ) b (C : ℤ) := by
  obtain ⟨hdisc, hA, _hlo, _hhi, _hAC, _hb, hprim⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hA
  · exact hdisc
  · simpa using hprim

/-!
## Section 6: The reduced input record

The two genuinely missing class-group laws remain explicit `Prop` fields.  The
principal-genus bridge is now derived from `BandSplit` by CRT, and the band
smallness is a standalone elementary input.
-/

/-- The elementary inputs of L4/L25/L36 after the principal-genus bridge has
been split into `BandSplit` plus CRT.  The Gauss composition and ideal-squaring
laws remain explicit unproved inputs, exactly as in `RandomizedL4`. -/
structure L4SubInputs (N : ℕ) (m : ℕ) (P : Fin m → Finset ℕ) where
  /-- Every band prime splits for `-2 * N`. -/
  band_split : BandSplit N m P
  /-- The band product is at most `√(2N)`. -/
  band_small : BandProductSmall N m P
  /-- Gauss/Dirichlet composition in the non-maximal order. -/
  form_composition : FormCompositionLaw N
  /-- The ideal-squaring congruence. -/
  ideal_squaring : IdealSquaringLaw N

/-- Assemble the L4 inputs: the principal-genus bridge is discharged by CRT
from `BandSplit`. -/
theorem L4SubInputs.toL4Inputs {N m : ℕ} {P : Fin m → Finset ℕ}
    (I : L4SubInputs N m P)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) : L4Inputs N m P :=
  { principal_genus := principalGenusBridge_of_bandSplit I.band_split hprime
    band_small := I.band_small
    form_composition := I.form_composition
    ideal_squaring := I.ideal_squaring }

/-- **The private-supply record from the reduced L4 inputs.**  Every field is
passed through unchanged; only the realized supply is rebuilt from `BandSplit`
plus CRT. -/
def toPrivateSupplyInputs {N : ℕ} (hNpos : 0 < N) (hN3 : 3 ≤ N)
    (m : ℕ) (hm : 0 < m) (P : Fin m → Finset ℕ)
    (hPprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N))
    (hPne : ∀ i, (P i).Nonempty)
    (hPdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (M_min : ℕ) (hM_min : 0 < M_min)
    (hPsize : ∀ i, M_min ≤ (P i).card)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbias : ∀ i (S : Finset ℕ), S ⊆ N.primeFactors → S.Nonempty →
      |(∑ p ∈ P i, genusCharReal N S (p : ZMod (8 * N))) / ((P i).card : ℝ)| ≤ δ)
    (classBounds : PrivateSupplyClassBounds N)
    (I : L4SubInputs N m P) : PrivateSupplyInputs N :=
  Cogentic.RandomizedL4.toPrivateSupplyInputs hNpos hN3 m hm P hPprime hPcop hPne
    hPdisj M_min hM_min hPsize δ hδ hbias classBounds (I.toL4Inputs hPprime)

/-- **The L4 supply bridge with the principal-genus input discharged by
splitting bands.**  From `BandSplit`, the elementary band-size bound, and prime
coprimality, every principal-genus distinct band tuple is realized as the leading
coefficient of a reduced form. -/
theorem realized_of_l4SubInputs {N m : ℕ} {P : Fin m → Finset ℕ}
    (I : L4SubInputs N m P)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4Inputs (I.toL4Inputs hprime) hprime hPcop

/-- **From splitPrimeBin bands to realized principal-genus tuples.**  This is the
manuscript-shaped corollary: if every band is a subset of `splitPrimeBin`, the
only remaining hypotheses are the elementary band bound, primality/coprimality,
and the two explicit class-group laws. -/
theorem realized_of_splitPrimeBin_bands {N m : ℕ} {P : Fin m → Finset ℕ}
    {A B : ℕ} (hN : Odd N)
    (hsub : ∀ i, P i ⊆ splitPrimeBin N A B)
    (hband : BandProductSmall N m P)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N))
    (hcomp : FormCompositionLaw N) (hsq : IdealSquaringLaw N) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    { band_split := bandSplit_of_subset_splitPrimeBin hN hsub
      band_small := hband
      form_composition := hcomp
      ideal_squaring := hsq }
    hprime hPcop

/-! ## Axiom audit -/

#print axioms locallySplit_iff_int_dvd
#print axioms locallySplit_of_dvd
#print axioms locallySplit_mul_of_coprime
#print axioms locallySplit_finset_prod
#print axioms locallySplit_of_legendreSym
#print axioms legendreSym_of_locallySplit
#print axioms not_locallySplit_two_pow_of_odd
#print axioms locallySplit_of_mem_splitPrimeBin
#print axioms principalGenusBridge_iff_split
#print axioms principalGenusBridge_of_bandSplit
#print axioms bandSplit_of_subset_splitPrimeBin
#print axioms bandProductSmall_of_max
#print axioms bandProductSmall_of_max_le_sqrt
#print axioms bandProductSmall_of_uniform_bound
#print axioms exists_reducedForm_of_locallySplit
#print axioms exists_isReducedForm_of_locallySplit
#print axioms isPrimitiveForm_of_isReducedForm
#print axioms L4SubInputs.toL4Inputs
#print axioms toPrivateSupplyInputs
#print axioms realized_of_l4SubInputs
#print axioms realized_of_splitPrimeBin_bands

end

end Cogentic.RandomizedL4Sub
