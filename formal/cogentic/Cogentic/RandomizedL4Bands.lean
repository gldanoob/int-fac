import Cogentic.RandomizedL4Cox
import Cogentic.RandomizedL4SquaringSelection

set_option linter.style.haveILetI false

/-!
# L4Bands: split-prime bands and the finished L4 leaf

`Cogentic.RandomizedL4Sub` reduced the principal-genus bridge of L4 to the two
band inputs

* `BandSplit N m P` --- every prime in every band splits in `ℚ(√(-2N))`;
* `BandProductSmall N m P` --- the product of one prime from each band is at
  most `√(2N)`,

and `Cogentic.RandomizedL4Cox` / `Cogentic.RandomizedL4SquaringSelection` have
now discharged the two class-group laws for odd `N`:

* `faithfulCompositionCox N` proves the full `d²`-corrected Cox composition law;
* `squaringPrimitiveSelection_of_odd N hN` proves the primitive-selection
  residual, which together with the already-proved `squaringRootLaw N` gives
  `ExplicitIdealSquaring N`.

This file closes the band side and assembles the leaf.

## The paper's bands

The manuscript cuts each band from the split-prime bin of a dyadic interval.
We model the one-coordinate recipe by arbitrary endpoints

`splitPrimeBands N lo hi i = splitPrimeBin N (lo i) (hi i)`,

and the dyadic specialization

`dyadicSplitPrimeBands N b i = splitPrimeBin N (2^(b i - 1)) (2^(b i))`.

`BandSplit` is then unconditional for odd `N`, because every element of
`splitPrimeBin` splits by construction (`bandSplit_of_subset_splitPrimeBin`).

`BandProductSmall` is a genuine magnitude condition: for an arbitrary family of
split primes it is false (the bands may contain primes far above `√N`).  The
smallest faithful input is the product of the band upper endpoints.  We prove

* `bandProductSmall_of_splitPrimeBin_endpoints`: if `P i ⊆ splitPrimeBin N
  (lo i) (hi i)` and `(∏ i, hi i)^2 ≤ 2N`, then `BandProductSmall N m P`;
* `bandProductSmall_of_bitBudget`: the paper-shaped form with
  `hi i = 2^(b i)` and total bit budget `(2^(∑ i, b i))^2 ≤ 2N`;
* the corresponding statements for the two concrete band families, and for
  arbitrary subfamilies of `splitPrimeBin` (the form obtained after deleting
  exceptional primes).

Thus the only remaining arithmetic input is an explicit band-size inequality;
no prime-count, splitting or class-group input remains.

## Assembly

`L4SubInputs.ofOddSplitBands` builds the reduced input record using the proved
Cox and squaring laws, and `realized_of_splitPrimeBands` /
`realized_of_dyadicSplitPrimeBands` are the manuscript-shaped realization
corollaries for the split-prime bands.  Primality and coprimality of the band
primes are read off from `splitPrimeBin`, so they are not hypotheses of the
concrete corollaries.

Nothing here is a `sorry`, `admit`, `axiom`, or `native_decide`, and no loss is
set to zero.
-/

namespace Cogentic.RandomizedL4Bands

open Finset
open scoped BigOperators

open Cogentic.RandomizedL4
open Cogentic.RandomizedL4Sub
open Cogentic.RandomizedL4Faithful
open Cogentic.RandomizedL4Composition
open Cogentic.RandomizedL4Cox
open Cogentic.RandomizedL4SquaringSelection
open Cogentic.RandomizedReducedFormSupply
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedEpochPrivate

noncomputable section

/-!
## Section 1: The paper's split-prime bands
-/

/-- The split-prime bands of the paper: band `i` is the set of split primes in
the interval `(lo i, hi i]`. -/
noncomputable def splitPrimeBands (N : ℕ) {m : ℕ} (lo hi : Fin m → ℕ) :
    Fin m → Finset ℕ :=
  fun i => splitPrimeBin N (lo i) (hi i)

/-- The dyadic specialization: band `i` is the split primes in
`(2^(b i - 1), 2^(b i)]`.  The exponents `b i` are the per-band bit
allocations of the paper's one-coordinate recipe. -/
noncomputable def dyadicSplitPrimeBands (N : ℕ) {m : ℕ} (b : Fin m → ℕ) :
    Fin m → Finset ℕ :=
  splitPrimeBands N (fun i => 2 ^ (b i - 1)) (fun i => 2 ^ b i)

/-- A band prime is at most its band upper endpoint. -/
theorem le_upper_of_mem_splitPrimeBin {N A B p : ℕ}
    (hp : p ∈ splitPrimeBin N A B) : p ≤ B := by
  have hbin : p ∈ Cogentic.Randomized.primeBin A B := (Finset.mem_filter.mp hp).1
  exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hbin).1).2

/-- A band prime is prime. -/
theorem prime_of_mem_splitPrimeBin {N A B p : ℕ}
    (hp : p ∈ splitPrimeBin N A B) : p.Prime := by
  have hbin : p ∈ Cogentic.Randomized.primeBin A B := (Finset.mem_filter.mp hp).1
  exact (Finset.mem_filter.mp hbin).2

/-- A band prime is at most the upper endpoint of its band. -/
theorem le_upper_of_mem_splitPrimeBands {N m : ℕ} {lo hi : Fin m → ℕ}
    {i : Fin m} {p : ℕ} (hp : p ∈ splitPrimeBands N lo hi i) : p ≤ hi i :=
  le_upper_of_mem_splitPrimeBin hp

/-- A band prime is prime. -/
theorem prime_of_mem_splitPrimeBands {N m : ℕ} {lo hi : Fin m → ℕ}
    {i : Fin m} {p : ℕ} (hp : p ∈ splitPrimeBands N lo hi i) : p.Prime :=
  prime_of_mem_splitPrimeBin hp

/-- A band prime is coprime to `8 * N` for odd `N`. -/
theorem coprime_eight_mul_of_mem_splitPrimeBin {N A B p : ℕ} (hN : Odd N)
    (hp : p ∈ splitPrimeBin N A B) : Nat.Coprime p (8 * N) := by
  haveI : NeZero (8 * N) := ⟨by have h := hN.pos; omega⟩
  exact (Finset.mem_filter.mp
    (splitPrimeBin_subset_coprimePrimeBin N A B hp)).2

/-- A band prime is coprime to `8 * N` for odd `N`. -/
theorem coprime_eight_mul_of_mem_splitPrimeBands {N m : ℕ} {lo hi : Fin m → ℕ}
    (hN : Odd N) {i : Fin m} {p : ℕ}
    (hp : p ∈ splitPrimeBands N lo hi i) : Nat.Coprime p (8 * N) :=
  coprime_eight_mul_of_mem_splitPrimeBin hN hp

/-!
## Section 2: `BandSplit`
-/

/-- **Every split-prime band family splits.**  This is unconditional (for odd
`N`): each element of `splitPrimeBin` carries a local square root of `-2N`
modulo that prime. -/
theorem bandSplit_splitPrimeBands {N m : ℕ} (lo hi : Fin m → ℕ)
    (hN : Odd N) : BandSplit N m (splitPrimeBands N lo hi) :=
  fun _i _p hp => locallySplit_of_mem_splitPrimeBin hN hp

/-- The dyadic specialization of `bandSplit_splitPrimeBands`. -/
theorem bandSplit_dyadicSplitPrimeBands {N m : ℕ} (b : Fin m → ℕ)
    (hN : Odd N) : BandSplit N m (dyadicSplitPrimeBands N b) :=
  bandSplit_splitPrimeBands _ _ hN

/-- **`BandSplit` for arbitrary subfamilies of split-prime bins.**  This is the
form used by the paper after deleting exceptional primes from each band. -/
theorem bandSplit_of_subset_splitPrimeBin_endpoints {N m : ℕ}
    {P : Fin m → Finset ℕ} {lo hi : Fin m → ℕ}
    (hN : Odd N) (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (hi i)) :
    BandSplit N m P :=
  fun i _p hp => locallySplit_of_mem_splitPrimeBin hN (hsub i hp)

/-!
## Section 3: `BandProductSmall`
-/

/-- **The smallest explicit band-size input.**  If every band is contained in
a split-prime bin with upper endpoints `hi i` and the product of the endpoints
squares to at most `2N`, then the product of one prime from each band is at
most `√(2N)`. -/
theorem bandProductSmall_of_splitPrimeBin_endpoints {N m : ℕ}
    {P : Fin m → Finset ℕ} {lo hi : Fin m → ℕ}
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (hi i))
    (hbound : (∏ i, hi i) ^ 2 ≤ 2 * N) :
    BandProductSmall N m P := by
  intro t
  have hle : ∏ i, (t i).1 ≤ ∏ i, hi i :=
    Finset.prod_le_prod' fun i _ =>
      le_upper_of_mem_splitPrimeBin (hsub i (t i).2)
  exact (Nat.pow_le_pow_left hle 2).trans hbound

/-- The paper-shaped bit form of the band-size input: if the upper endpoint of
band `i` is `2^(b i)` and the total bit budget satisfies
`(2^(∑ i, b i))^2 ≤ 2N`, then `BandProductSmall` holds. -/
theorem bandProductSmall_of_bitBudget {N m : ℕ} {P : Fin m → Finset ℕ}
    {lo : Fin m → ℕ} {b : Fin m → ℕ}
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (2 ^ b i))
    (hbudget : (2 ^ (∑ i, b i)) ^ 2 ≤ 2 * N) :
    BandProductSmall N m P := by
  refine bandProductSmall_of_splitPrimeBin_endpoints hsub ?_
  have hprod : (∏ i, (2 : ℕ) ^ b i) = 2 ^ (∑ i, b i) := by
    simpa using (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin m)) b (2 : ℕ))
  simpa [hprod] using hbudget

/-- **The band-size bound for the concrete split-prime bands.** -/
theorem bandProductSmall_splitPrimeBands {N m : ℕ} (lo hi : Fin m → ℕ)
    (hbound : (∏ i, hi i) ^ 2 ≤ 2 * N) :
    BandProductSmall N m (splitPrimeBands N lo hi) :=
  bandProductSmall_of_splitPrimeBin_endpoints (fun _ => subset_rfl) hbound

/-- **The band-size bound for the dyadic split-prime bands.** -/
theorem bandProductSmall_dyadicSplitPrimeBands {N m : ℕ} (b : Fin m → ℕ)
    (hbudget : (2 ^ (∑ i, b i)) ^ 2 ≤ 2 * N) :
    BandProductSmall N m (dyadicSplitPrimeBands N b) :=
  bandProductSmall_of_bitBudget (fun _ => subset_rfl) hbudget

/-- The maximal-element form of the band-size input, for arbitrary band
families: the product of the actual band maxima is at most `√(2N)`. -/
theorem bandProductSmall_of_max_le_sqrt_bands {N m : ℕ} {P : Fin m → Finset ℕ}
    (h : ∏ i, (P i).sup id ≤ Nat.sqrt (2 * N)) : BandProductSmall N m P :=
  bandProductSmall_of_max_le_sqrt h

/-!
## Section 4: The Cox composition law and the squaring law
-/

/-- **The faithful ideal-squaring input for odd `N`.**  The root law is proved
in `RandomizedL4Faithful`; the primitive-selection residual is proved in
`RandomizedL4SquaringSelection`. -/
theorem explicitIdealSquaring_of_odd (N : ℕ) (hN : Odd N) :
    ExplicitIdealSquaring N :=
  (explicitIdealSquaring_iff_root_and_selection N).mpr
    ⟨squaringRootLaw N, squaringPrimitiveSelection_of_odd N hN⟩

/-!
## Section 5: Assembling `L4SubInputs` and realization
-/

/-- **The reduced L4 inputs from splitting bands and the band-size bound.**
The two class-group fields are the proved Cox composition law and the proved
ideal-squaring law for odd `N`. -/
theorem L4SubInputs.ofOddSplitBands {N m : ℕ} {P : Fin m → Finset ℕ}
    (hN : Odd N) (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P) :
    L4SubInputs N m P :=
  { band_split := hsplit
    band_small := hsmall
    form_composition := formCompositionLaw_of_cox (faithfulCompositionCox N)
    ideal_squaring := idealSquaringLaw_of_explicit (explicitIdealSquaring_of_odd N hN) }

/-- **The reduced L4 inputs for the paper's split-prime bands.**  The only
arithmetic hypothesis is the explicit endpoint product bound. -/
theorem L4SubInputs.ofSplitPrimeBands {N m : ℕ} {lo hi : Fin m → ℕ}
    (hN : Odd N) (hbound : (∏ i, hi i) ^ 2 ≤ 2 * N) :
    L4SubInputs N m (splitPrimeBands N lo hi) :=
  L4SubInputs.ofOddSplitBands hN
    (bandSplit_splitPrimeBands lo hi hN)
    (bandProductSmall_splitPrimeBands lo hi hbound)

/-- **The reduced L4 inputs for the dyadic split-prime bands.** -/
theorem L4SubInputs.ofDyadicSplitPrimeBands {N m : ℕ} {b : Fin m → ℕ}
    (hN : Odd N) (hbudget : (2 ^ (∑ i, b i)) ^ 2 ≤ 2 * N) :
    L4SubInputs N m (dyadicSplitPrimeBands N b) :=
  L4SubInputs.ofOddSplitBands hN
    (bandSplit_dyadicSplitPrimeBands b hN)
    (bandProductSmall_dyadicSplitPrimeBands b hbudget)

/-- **The reduced L4 inputs for arbitrary subfamilies of split-prime bins.**
This covers the paper's bands after deleting exceptional primes. -/
theorem L4SubInputs.ofSplitPrimeBin_subsets {N m : ℕ} {P : Fin m → Finset ℕ}
    {lo hi : Fin m → ℕ} (hN : Odd N)
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (hi i))
    (hbound : (∏ i, hi i) ^ 2 ≤ 2 * N) :
    L4SubInputs N m P :=
  L4SubInputs.ofOddSplitBands hN
    (bandSplit_of_subset_splitPrimeBin_endpoints hN hsub)
    (bandProductSmall_of_splitPrimeBin_endpoints hsub hbound)

/-- **The bit-budget form of `L4SubInputs` for subfamilies of split-prime
bins.** -/
theorem L4SubInputs.ofSplitPrimeBin_bitBudget {N m : ℕ} {P : Fin m → Finset ℕ}
    {lo : Fin m → ℕ} {b : Fin m → ℕ} (hN : Odd N)
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (2 ^ b i))
    (hbudget : (2 ^ (∑ i, b i)) ^ 2 ≤ 2 * N) :
    L4SubInputs N m P :=
  L4SubInputs.ofOddSplitBands hN
    (bandSplit_of_subset_splitPrimeBin_endpoints hN hsub)
    (bandProductSmall_of_bitBudget hsub hbudget)

/-- **Realization from arbitrary splitting bands, Cox composition and
squaring.**  All band primes are assumed prime and coprime to `8N`. -/
theorem realized_of_oddSplitBands {N m : ℕ} {P : Fin m → Finset ℕ}
    (hN : Odd N) (hsplit : BandSplit N m P) (hsmall : BandProductSmall N m P)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    (L4SubInputs.ofOddSplitBands hN hsplit hsmall) hprime hPcop

/-- **Realization for the paper's split-prime bands.**  Primality and
coprimality of the band primes are discharged by membership in `splitPrimeBin`;
the only arithmetic input is the endpoint product bound. -/
theorem realized_of_splitPrimeBands {N m : ℕ} {lo hi : Fin m → ℕ}
    (hN : Odd N) (hbound : (∏ i, hi i) ^ 2 ≤ 2 * N) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ splitPrimeBands N lo hi i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    (L4SubInputs.ofSplitPrimeBands hN hbound)
    (fun _ _ hp => prime_of_mem_splitPrimeBands hp)
    (fun _ _ hp => coprime_eight_mul_of_mem_splitPrimeBands hN hp)

/-- **Realization for the dyadic split-prime bands**, with the paper's total
bit budget `(2^(∑ i, b i))^2 ≤ 2N`. -/
theorem realized_of_dyadicSplitPrimeBands {N m : ℕ} {b : Fin m → ℕ}
    (hN : Odd N) (hbudget : (2 ^ (∑ i, b i)) ^ 2 ≤ 2 * N) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ dyadicSplitPrimeBands N b i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    (L4SubInputs.ofDyadicSplitPrimeBands hN hbudget)
    (fun _ _ hp => prime_of_mem_splitPrimeBands hp)
    (fun _ _ hp => coprime_eight_mul_of_mem_splitPrimeBands hN hp)

/-- **Realization for arbitrary subfamilies of split-prime bins.**  This is the
paper-shaped corollary after deleting any exceptional primes: membership in
`splitPrimeBin` supplies primality and coprimality to `8N`, and the endpoint
product bound supplies `BandProductSmall`. -/
theorem realized_of_splitPrimeBin_subsets {N m : ℕ} {P : Fin m → Finset ℕ}
    {lo hi : Fin m → ℕ} (hN : Odd N)
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (hi i))
    (hbound : (∏ i, hi i) ^ 2 ≤ 2 * N) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    (L4SubInputs.ofSplitPrimeBin_subsets hN hsub hbound)
    (fun _ _ hp => prime_of_mem_splitPrimeBin (hsub _ hp))
    (fun _ _ hp => coprime_eight_mul_of_mem_splitPrimeBin hN (hsub _ hp))

/-- **Realization for subfamilies of split-prime bins under the paper's total
bit budget.** -/
theorem realized_of_splitPrimeBin_bitBudget {N m : ℕ} {P : Fin m → Finset ℕ}
    {lo : Fin m → ℕ} {b : Fin m → ℕ} (hN : Odd N)
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (2 ^ b i))
    (hbudget : (2 ^ (∑ i, b i)) ^ 2 ≤ 2 * N) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs
    (L4SubInputs.ofSplitPrimeBin_bitBudget hN hsub hbudget)
    (fun _ _ hp => prime_of_mem_splitPrimeBin (hsub _ hp))
    (fun _ _ hp => coprime_eight_mul_of_mem_splitPrimeBin hN (hsub _ hp))

/-!
## Section 6: A concrete non-vacuous instance

The single band of split primes up to `√(2N)` already satisfies both band
inputs unconditionally for odd `N`.  It is the maximal admissible one-band
family, and it shows that the reduced leaf is not vacuous; the paper's
multi-band case differs only in the explicit endpoint product bound.
-/

/-- The one-band family of all split primes up to `√(2N)`. -/
noncomputable def fullSplitBand (N : ℕ) : Fin 1 → Finset ℕ :=
  fun _ => splitPrimeBin N 0 (Nat.sqrt (2 * N))

/-- The maximal one-band family satisfies `BandProductSmall` unconditionally. -/
theorem bandProductSmall_fullSplitBand (N : ℕ) :
    BandProductSmall N 1 (fullSplitBand N) := by
  refine bandProductSmall_splitPrimeBands (fun _ => 0) (fun _ => Nat.sqrt (2 * N)) ?_
  simpa using Nat.sqrt_le' (2 * N)

/-- The maximal one-band family satisfies `BandSplit` for odd `N`. -/
theorem bandSplit_fullSplitBand (N : ℕ) (hN : Odd N) :
    BandSplit N 1 (fullSplitBand N) :=
  bandSplit_splitPrimeBands _ _ hN

/-- **Unconditional `L4SubInputs` for the maximal one-band family.** -/
theorem L4SubInputs.fullSplitBand (N : ℕ) (hN : Odd N) :
    L4SubInputs N 1 (fullSplitBand N) :=
  L4SubInputs.ofOddSplitBands hN (bandSplit_fullSplitBand N hN)
    (bandProductSmall_fullSplitBand N)

/-- **Unconditional realization for the maximal one-band family.** -/
theorem realized_fullSplitBand (N : ℕ) (hN : Odd N) :
    ∀ (t : ∀ _i : Fin 1, {p : ℕ // p ∈ fullSplitBand N _i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs (L4SubInputs.fullSplitBand N hN)
    (fun _ _ hp => prime_of_mem_splitPrimeBin hp)
    (fun _ _ hp => coprime_eight_mul_of_mem_splitPrimeBin hN hp)

/-! ## Axiom audit -/

#print axioms le_upper_of_mem_splitPrimeBin
#print axioms prime_of_mem_splitPrimeBin
#print axioms coprime_eight_mul_of_mem_splitPrimeBin
#print axioms coprime_eight_mul_of_mem_splitPrimeBands
#print axioms bandSplit_splitPrimeBands
#print axioms bandSplit_dyadicSplitPrimeBands
#print axioms bandSplit_of_subset_splitPrimeBin_endpoints
#print axioms bandProductSmall_of_splitPrimeBin_endpoints
#print axioms bandProductSmall_of_bitBudget
#print axioms bandProductSmall_splitPrimeBands
#print axioms bandProductSmall_dyadicSplitPrimeBands
#print axioms bandProductSmall_of_max_le_sqrt_bands
#print axioms explicitIdealSquaring_of_odd
#print axioms L4SubInputs.ofOddSplitBands
#print axioms L4SubInputs.ofSplitPrimeBands
#print axioms L4SubInputs.ofDyadicSplitPrimeBands
#print axioms L4SubInputs.ofSplitPrimeBin_subsets
#print axioms L4SubInputs.ofSplitPrimeBin_bitBudget
#print axioms realized_of_oddSplitBands
#print axioms realized_of_splitPrimeBands
#print axioms realized_of_dyadicSplitPrimeBands
#print axioms realized_of_splitPrimeBin_subsets
#print axioms realized_of_splitPrimeBin_bitBudget
#print axioms bandProductSmall_fullSplitBand
#print axioms bandSplit_fullSplitBand
#print axioms L4SubInputs.fullSplitBand
#print axioms realized_fullSplitBand

end

end Cogentic.RandomizedL4Bands
