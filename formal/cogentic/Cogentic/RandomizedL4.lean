import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedEpochPrivate
import Cogentic.RandomizedEvenDiscriminantGenus

/-!
# L4 / L25 / L36: non-maximal-order forms, ideal squaring, and the principal genus

The manuscript's L4/L25/L36 (`research/randomized-end-to-end-wave6-brief.md` W41)
is the algebraic bridge behind the private quadratic-form supply of
`Cogentic.RandomizedEpochPrivate.PrivateSupplyInputs.realized`:

> every squarefree principal-genus product of distinct split primes, one from
> each band, is the leading coefficient of a reduced primitive form of
> discriminant `-8N`.

The manuscript treats this as an exact identification (blueprint §2 C2 and
C5.b/C5.d, KB E.4 p.89, `research/keybreak-quadratic-class-integration.md`
§Alternative), which is why `RandomizedPaperLeafStatements.AlgebraicLeaf` carries
the zero deficit.  This file separates the three algebraic ingredients and
proves the leaf and supply reductions from them.  It does **not** prove the
class-group theory: that theory is stated as the explicit inputs below.

## What is proved and what is assumed

* `exists_reducedForm_of_centered_root` is proved unconditionally: if
  `A > 0`, `(A, 2N) = 1`, `A² ≤ 2N`, and `-2N` is a square modulo `A`, then
  `A` is the leading coefficient of a canonical reduced form
  `[A, 2b, C] ∈ ReducedForms N`.  The middle coefficient is the centred
  representative of the root, and `C = (b² + 2N) / A`.  Primitivity is a
  consequence of `(A, 2N) = 1`, and `A ≤ C` is the smallness input.

* `PrincipalGenusBridge` is the **missing principal-genus/splitting input**.
  It is stronger than `∏ genusMap N p = 1` because `genusMap` records only the
  odd prime divisors of `N`, while a root of `-2N` requires the full splitting
  character `χ_{-8N}` at every band prime.  In the manuscript the bands are cut
  from `splitPrimeBin`, so the bridge holds there; here it is an explicit field,
  not an axiom or a `sorry`.

* `BandProductSmall` is the **missing band-size input**: the product of one
  prime from each band is at most `√(2N)`.  This is the paper's
  "total bits `⌊(n-1)/2⌋ - 2`, stays below `√N/2`" constraint of
  `research/keybreak-quadratic-class-integration.md`; without it an arbitrary
  principal-genus product need not occur as a reduced leading coefficient.

* `FormCompositionLaw` and `IdealSquaringLaw` record the two remaining
  non-maximal-order ingredients (Gauss/Dirichlet composition and the squaring
  congruence of the note) as explicit `Prop`s for audit.

Nothing here is a `sorry`, an `admit`, an `axiom`, or `native_decide`.  The
`AlgebraicLeaf` deficit is zero because the inputs are exact identities (the
paper's own convention, see `AlgebraicLeaf.loss_zero`), not because an analytic
estimate has been silently discarded: `unrealizedTuples_card_eq_zero` proves the
finite set of unrealized principal-genus tuples is empty.  The nontrivial
content is `realized_of_l4Inputs`.
-/

namespace Cogentic.RandomizedL4

open Filter Real
open scoped BigOperators

open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochPrivate
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedReducedFormSupply

noncomputable section

/-!
## Section 1: The centred root and the reduced representative

This is the part of the bridge that is pure form arithmetic and is proved here.
-/

/-- The centred representative of `b` modulo `A`, chosen in `(-A/2, A/2]`. -/
def centeredRep (A : ℕ) (b : ℤ) : ℤ :=
  if 2 * (b % (A : ℤ)) ≤ (A : ℤ) then b % (A : ℤ) else b % (A : ℤ) - (A : ℤ)

/-- The centred representative is congruent to the original residue modulo `A`. -/
theorem centeredRep_cast (A : ℕ) (hA : 0 < A) (b : ℤ) :
    ((centeredRep A b : ℤ) : ZMod A) = (b : ZMod A) := by
  rw [centeredRep]
  set r : ℤ := b % (A : ℤ) with hrdef
  have hAne : (A : ℤ) ≠ 0 := by exact_mod_cast hA.ne'
  have hr : r = b - (A : ℤ) * (b / (A : ℤ)) := by
    rw [hrdef]
    have h := Int.emod_add_mul_ediv b (A : ℤ)
    linarith
  have hrcast : (r : ZMod A) = (b : ZMod A) := by
    rw [hr]
    push_cast
    rw [ZMod.natCast_self, zero_mul, sub_zero]
  split_ifs with h
  · exact hrcast
  · rw [Int.cast_sub, hrcast]
    have hAc : (((A : ℤ)) : ZMod A) = 0 := by
      push_cast
      exact ZMod.natCast_self A
    rw [hAc, sub_zero]

/-- The centred representative satisfies `-A < 2b ≤ A`. -/
theorem centeredRep_bounds (A : ℕ) (hA : 0 < A) (b : ℤ) :
    -(A : ℤ) < 2 * centeredRep A b ∧ 2 * centeredRep A b ≤ (A : ℤ) := by
  rw [centeredRep]
  set r : ℤ := b % (A : ℤ) with hrdef
  have hAne : (A : ℤ) ≠ 0 := by exact_mod_cast hA.ne'
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    exact Int.emod_nonneg b hAne
  have hrA : r < (A : ℤ) := by
    rw [hrdef]
    exact Int.emod_lt_of_pos b (by exact_mod_cast hA)
  split_ifs with h
  · omega
  · push Not at h
    omega

/-- A root of `-2N` modulo `A` survives centring. -/
theorem centeredRep_dvd (A : ℕ) (hA : 0 < A) (N : ℕ) {b : ℤ}
    (h : (A : ℤ) ∣ b ^ 2 + 2 * (N : ℤ)) :
    (A : ℤ) ∣ centeredRep A b ^ 2 + 2 * (N : ℤ) := by
  have hdvd : (A : ℤ) ∣ centeredRep A b - b := by
    have h0 : (((centeredRep A b - b : ℤ)) : ZMod A) = 0 := by
      rw [Int.cast_sub, centeredRep_cast A hA b, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  have hdvd2 : (A : ℤ) ∣ centeredRep A b ^ 2 - b ^ 2 := by
    have hfac : centeredRep A b ^ 2 - b ^ 2 =
        (centeredRep A b - b) * (centeredRep A b + b) := by ring
    rw [hfac]
    exact dvd_mul_of_dvd_left hdvd _
  have hsum := dvd_add hdvd2 h
  have hEq : (centeredRep A b ^ 2 - b ^ 2) + (b ^ 2 + 2 * (N : ℤ)) =
      centeredRep A b ^ 2 + 2 * (N : ℤ) := by ring
  rwa [hEq] at hsum

/-- **Centred-root reduction.**  A centred root of `-2N` modulo `A`, together with
`(A, 2N) = 1` and `A² ≤ 2N`, produces a canonical reduced form of discriminant
`-8N` with leading coefficient exactly `A`. -/
theorem exists_reducedForm_of_centered_root {N A : ℕ} (hA : 0 < A)
    (hcop : Nat.Coprime A (2 * N)) (hsmall : A ^ 2 ≤ 2 * N)
    {b : ℤ} (hroot : (A : ℤ) ∣ b ^ 2 + 2 * (N : ℤ)) :
    ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = A := by
  let b' : ℤ := centeredRep A b
  have hbroot : (A : ℤ) ∣ b' ^ 2 + 2 * (N : ℤ) := centeredRep_dvd A hA N hroot
  have hbounds := centeredRep_bounds A hA b
  have hdivN : A ∣ b'.natAbs ^ 2 + 2 * N := by
    have hZ : (A : ℤ) ∣ ((b'.natAbs ^ 2 + 2 * N : ℕ) : ℤ) := by
      have hcast : ((b'.natAbs ^ 2 + 2 * N : ℕ) : ℤ) = b' ^ 2 + 2 * (N : ℤ) := by
        push_cast
        rw [sq_abs]
      rw [hcast]
      exact hbroot
    exact_mod_cast hZ
  let C : ℕ := (b'.natAbs ^ 2 + 2 * N) / A
  have hAC : A * C = b'.natAbs ^ 2 + 2 * N := Nat.mul_div_cancel' hdivN
  have hdisc : (A : ℤ) * (C : ℤ) - b' ^ 2 = 2 * (N : ℤ) := by
    have hACz : (A : ℤ) * (C : ℤ) = ((b'.natAbs ^ 2 + 2 * N : ℕ) : ℤ) := by
      exact_mod_cast hAC
    have hACz' : (A : ℤ) * (C : ℤ) = b' ^ 2 + 2 * (N : ℤ) := by
      rw [hACz]
      push_cast
      rw [sq_abs]
    rw [hACz']
    ring
  have hACle : A ≤ C := by
    have hmul : A * A ≤ A * C := by
      rw [hAC]
      have hA2 : A ^ 2 ≤ 2 * N := hsmall
      nlinarith [Nat.zero_le (b'.natAbs ^ 2)]
    exact Nat.le_of_mul_le_mul_left hmul hA
  have heqpos : A = C → 0 ≤ b' := by
    intro hAeq
    have hAA : A * A = b'.natAbs ^ 2 + 2 * N := by
      calc
        A * A = A * C := by rw [hAeq]
        _ = b'.natAbs ^ 2 + 2 * N := hAC
    have hAA' : A ^ 2 = b'.natAbs ^ 2 + 2 * N := by simpa [pow_two] using hAA
    have hb2 : b'.natAbs ^ 2 = 0 := by nlinarith [hAA', hsmall]
    have hbabs : b'.natAbs = 0 := by
      rw [pow_two] at hb2
      rcases Nat.mul_eq_zero.mp hb2 with h | h <;> exact h
    have hb0 : b' = 0 := Int.natAbs_eq_zero.mp hbabs
    simp [hb0]
  have hprim : Nat.gcd (Nat.gcd A (2 * b'.natAbs)) C = 1 := by
    set g := Nat.gcd (Nat.gcd A (2 * b'.natAbs)) C with hg
    have hgA : g ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hgC : g ∣ C := Nat.gcd_dvd_right _ _
    have hg2b : g ∣ 2 * b'.natAbs :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have hAodd : Odd A := by
      rcases Nat.even_or_odd A with he | ho
      · exfalso
        obtain ⟨k, hk⟩ := he
        have h2A : 2 ∣ A := ⟨k, by omega⟩
        have h2 : 2 ∣ Nat.gcd A (2 * N) := Nat.dvd_gcd h2A (dvd_mul_right 2 N)
        rw [hcop.gcd_eq_one] at h2
        omega
      · exact ho
    have hgodd : Odd g := by
      rcases Nat.even_or_odd g with he | ho
      · exfalso
        obtain ⟨j, hj⟩ := he
        obtain ⟨k, hk⟩ := hgA
        have hAeven : Even A := by
          refine ⟨j * k, ?_⟩
          rw [hk, hj]
          ring
        exact (Nat.not_even_iff_odd.mpr hAodd) hAeven
      · exact ho
    have hgb : g ∣ b'.natAbs := by
      have hcopg2 : Nat.Coprime g 2 := (Nat.coprime_two_left.mpr hgodd).symm
      exact hcopg2.dvd_of_dvd_mul_left hg2b
    have hgb2 : g ∣ b'.natAbs ^ 2 := by
      simpa [pow_two] using dvd_mul_of_dvd_left hgb b'.natAbs
    have hgAC : g ∣ A * C := dvd_mul_of_dvd_left hgA C
    have hgsum : g ∣ b'.natAbs ^ 2 + 2 * N := by
      rw [← hAC]
      exact hgAC
    have hg2N : g ∣ 2 * N := (Nat.dvd_add_right hgb2).mp hgsum
    have hggcd : g ∣ Nat.gcd A (2 * N) := Nat.dvd_gcd hgA hg2N
    rw [hcop.gcd_eq_one] at hggcd
    exact Nat.dvd_one.mp hggcd
  exact ⟨(A, b', C), mem_reducedForms.mpr
    ⟨hdisc, hA, hbounds.1, hbounds.2, hACle, heqpos, hprim⟩, rfl⟩

/-!
## Section 2: The explicit algebraic inputs

The three manuscript ingredients are the principal-genus/splitting bridge, the
form-composition law of the non-maximal order `ℤ[√(-2N)]`, and the ideal-squaring
congruence.  The band-size bound is the arithmetic constraint that makes the
constructed leading coefficient small enough to be reduced.
-/

/-- Primitive form of discriminant `-8N` (not necessarily reduced). -/
def IsPrimitiveForm (N : ℕ) (A b C : ℤ) : Prop :=
  0 < A ∧ A * C - b ^ 2 = 2 * (N : ℤ) ∧
    Nat.gcd (Nat.gcd A.natAbs (2 * b.natAbs)) C.natAbs = 1

/-- **Principal-genus/splitting bridge (missing input).**

For a tuple of distinct band primes whose product lies in the principal genus,
`-2N` is a square modulo the product.  This bundles the reciprocity step
`(ℓ/p) = (p/ℓ)` over the odd prime divisors `ℓ ∣ N`, the 2-part of the full
splitting character `χ_{-8N}`, and the CRT assembly.  It is deliberately
stronger than `∏ genusMap N p = 1`: `genusMap` sees only the odd part, whereas
the root needs `χ_{-8N}(p) = 1` at every band prime.  The manuscript's bands are
cut from `splitPrimeBin`, so this is exactly where the split-prime supply enters
the class-group bridge. -/
def PrincipalGenusBridge (N : ℕ) (m : ℕ) (P : Fin m → Finset ℕ) : Prop :=
  ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
    (∏ i, genusMap N (t i).1) = 1 →
    Function.Injective (fun i => (t i).1) →
      ∃ b : ℤ, ((∏ i, (t i).1 : ℕ) : ℤ) ∣ b ^ 2 + 2 * (N : ℤ)

/-- **Band-size input (missing input).**  The product of one prime from each band
is at most `√(2N)`.  This is the paper's "total bits `⌊(n-1)/2⌋ - 2`, stays below
`√N/2`" band constraint; it is what makes the centred root produce a form with
`A ≤ C`, hence a genuinely reduced representative. -/
def BandProductSmall (N : ℕ) (m : ℕ) (P : Fin m → Finset ℕ) : Prop :=
  ∀ t : ∀ i : Fin m, {p : ℕ // p ∈ P i}, (∏ i, (t i).1) ^ 2 ≤ 2 * N

/-- **Gauss/Dirichlet composition (recorded input).**  The product of the classes
of two primitive forms of discriminant `-8N` is represented by a primitive form
whose leading coefficient divides the product of the two leading coefficients.
This is the composition law of the proper class group of the non-maximal order
`ℤ[√(-2N)]`. -/
def FormCompositionLaw (N : ℕ) : Prop :=
  ∀ (A₁ b₁ C₁ A₂ b₂ C₂ : ℤ),
    IsPrimitiveForm N A₁ b₁ C₁ → IsPrimitiveForm N A₂ b₂ C₂ →
      ∃ (A b C : ℤ), IsPrimitiveForm N A b C ∧ A ∣ A₁ * A₂

/-- **Ideal-squaring law (recorded input).**  The square of the class of a
primitive form of discriminant `-8N` has a primitive representative whose
leading coefficient is `A² / d²` for some `d > 0`; this is the form-level shadow
of `I² / g = (a, b + √(-2N))` with `a = (t/g)²` from
`research/keybreak-quadratic-class-integration.md`. -/
def IdealSquaringLaw (N : ℕ) : Prop :=
  ∀ (A : ℕ) (b : ℤ) (C : ℕ), IsReducedForm N A b C →
    ∃ (a : ℕ) (b' : ℤ) (C' : ℕ) (d : ℕ),
      0 < a ∧ 0 < d ∧ a * d ^ 2 = A ^ 2 ∧ IsPrimitiveForm N (a : ℤ) b' C'

/-- The algebraic inputs of L4/L25/L36 for one band family `P`.  The two unary
laws (`form_composition`, `ideal_squaring`) are recorded for audit; the supply
reduction consumes `principal_genus` and `band_small`. -/
structure L4Inputs (N : ℕ) (m : ℕ) (P : Fin m → Finset ℕ) where
  /-- The principal-genus/splitting bridge. -/
  principal_genus : PrincipalGenusBridge N m P
  /-- The band product is at most `√(2N)`. -/
  band_small : BandProductSmall N m P
  /-- Gauss/Dirichlet form composition in the non-maximal order. -/
  form_composition : FormCompositionLaw N
  /-- The ideal-squaring congruence. -/
  ideal_squaring : IdealSquaringLaw N

/-!
## Section 3: The `PrivateSupplyInputs.realized` reduction
-/

/-- **The supply bridge.**  From the algebraic inputs, every squarefree
principal-genus product of distinct band primes is the leading coefficient of a
reduced primitive form of discriminant `-8N`.  This is exactly the shape of
`PrivateSupplyInputs.realized`. -/
theorem realized_of_l4Inputs {N m : ℕ} {P : Fin m → Finset ℕ}
    (I : L4Inputs N m P)
    (hPprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 := by
  intro t hgenus hinj
  have hApos : 0 < ∏ i, (t i).1 :=
    Finset.prod_pos fun i _ => (hPprime i (t i).1 (t i).2).pos
  have hcop : Nat.Coprime (∏ i, (t i).1) (2 * N) := by
    have hdvd : 2 * N ∣ 8 * N := ⟨4, by ring⟩
    have h1 : ∀ i, Nat.Coprime (t i).1 (2 * N) :=
      fun i => ((hPcop i (t i).1 (t i).2)).coprime_dvd_right hdvd
    exact Nat.Coprime.prod_left fun i _ => h1 i
  obtain ⟨b, hb⟩ := I.principal_genus t hgenus hinj
  exact exists_reducedForm_of_centered_root hApos hcop (I.band_small t) hb

/-- **Literal `PrivateSupplyInputs.realized`.**  Fill the `realized` field of a
private-supply record from the L4 algebraic inputs; every other field is passed
through unchanged. -/
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
    (I : L4Inputs N m P) : PrivateSupplyInputs N where
  hNpos := hNpos
  hN3 := hN3
  m := m
  hm := hm
  P := P
  hPprime := hPprime
  hPcop := hPcop
  hPne := hPne
  hPdisj := hPdisj
  M_min := M_min
  hM_min := hM_min
  hPsize := hPsize
  δ := δ
  hδ := hδ
  hbias := hbias
  realized := realized_of_l4Inputs I hPprime hPcop
  classBounds := classBounds

/-!
## Section 4: The `AlgebraicLeaf` reduction
-/

/-- The finite set of principal-genus distinct band tuples whose product is *not*
the leading coefficient of a reduced form.  This is the genuine algebraic defect
of one band family; the inputs prove it empty, so the leaf's zero deficit is
derived rather than assumed. -/
noncomputable def unrealizedTuples {N m : ℕ} (P : Fin m → Finset ℕ) :
    Finset (∀ i : Fin m, {p : ℕ // p ∈ P i}) := by
  classical
  exact Finset.univ.filter (fun t =>
    (∏ i, genusMap N (t i).1) = 1 ∧
      Function.Injective (fun i => (t i).1) ∧
      ¬ ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1)

/-- The algebraic inputs make the unrealized set empty. -/
theorem unrealizedTuples_eq_empty {N m : ℕ} {P : Fin m → Finset ℕ}
    (I : L4Inputs N m P)
    (hPprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    unrealizedTuples (N := N) P = ∅ := by
  classical
  by_contra hne
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  simp only [unrealizedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨hgenus, hinj, hnot⟩ := ht
  exact hnot (realized_of_l4Inputs I hPprime hPcop t hgenus hinj)

/-- Consequently the algebraic failure mass is zero: the zero deficit of
`AlgebraicLeaf` is the exactness of the supply bridge, not a discarded estimate. -/
theorem unrealizedTuples_card_eq_zero {N m : ℕ} {P : Fin m → Finset ℕ}
    (I : L4Inputs N m P)
    (hPprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    ((unrealizedTuples (N := N) P).card : ℝ) = 0 := by
  rw [unrealizedTuples_eq_empty I hPprime hPcop]
  simp

/-- **The L4/L25/L36 `AlgebraicLeaf`.**  The loss is identically zero because the
manuscript input is an exact identity: form composition, ideal squaring, and the
principal-genus bridge introduce no analytic error.  This is the paper's own
`AlgebraicLeaf` convention (`AlgebraicLeaf.loss_zero`), not an estimate that has
been set to zero; the substantive reduction is `realized_of_l4Inputs`. -/
def L4Inputs.toAlgebraicLeaf {N m : ℕ} {P : Fin m → Finset ℕ}
    (_I : L4Inputs N m P) : AlgebraicLeaf where
  loss := fun _ => 0
  loss_nonneg := fun _ => le_refl 0
  loss_zero := fun _ => rfl

/-- The `C5Inputs.classGroupGenus` slot of the algebraic leaf, in the shape
consumed by `PaperAnalyticAssumptions.slot_le`. -/
theorem L4Inputs.toAlgebraicLeaf_slot {N m : ℕ} {P : Fin m → Finset ℕ}
    (I : L4Inputs N m P) (slots : C5LossSlots)
    (h : slots .classGroupGenus = I.toAlgebraicLeaf.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .classGroupGenus n ≤ exp (-(2 : ℝ) * scale n) := by
  rw [h]
  exact I.toAlgebraicLeaf.slot

/-! ## Axiom audit -/

#print axioms centeredRep_cast
#print axioms centeredRep_bounds
#print axioms centeredRep_dvd
#print axioms exists_reducedForm_of_centered_root
#print axioms realized_of_l4Inputs
#print axioms toPrivateSupplyInputs
#print axioms unrealizedTuples_eq_empty
#print axioms unrealizedTuples_card_eq_zero
#print axioms L4Inputs.toAlgebraicLeaf
#print axioms L4Inputs.toAlgebraicLeaf_slot

end

end Cogentic.RandomizedL4
