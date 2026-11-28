import Cogentic.RandomizedL4Bands
import Cogentic.RandomizedBalancedAllocation
import Mathlib.Data.Nat.Size

set_option linter.style.haveILetI false

/-!
# L4BitBudget: the paper's band bit budget and the realized split band

`Cogentic.RandomizedL4Bands.realized_of_splitPrimeBands` reduces the L4
realization to the single scalar band-size condition

`(∏ i, hi i) ^ 2 ≤ 2 * N`,

where band `i` is a subfamily of `splitPrimeBin N (lo i) (hi i)`.  The dyadic
form uses `hi i = 2 ^ (b i)` and the total bit condition
`(2 ^ (∑ i, b i)) ^ 2 ≤ 2 * N`.

This file discharges that condition for the parameters used by the paper's
one-coordinate band recipe.  The manuscript allocates

`⌊(n - 1) / 2⌋ - 2`

bits to the private coordinates (see
`Cogentic.RandomizedBalancedAllocation.coordinateBits`).  We prove:

* `paperBitBudget` is exactly this quantity;
* `two_mul_paperBitBudget_le`: the elementary scalar inequality
  `2 * paperBitBudget n ≤ n`;
* `paperBitBudget_pow_sq_le`: if `2 ^ n ≤ N` then
  `(2 ^ paperBitBudget n) ^ 2 ≤ 2 * N`.  Thus the paper's total bit budget
  satisfies the L4 band-size condition with no further hypothesis;
* `bandProductSmall_of_paperBits` and `bandProductSmall_of_coordinateBits`:
  the general `m`-band `BandProductSmall` condition follows from
  `∑ i, b i ≤ paperBitBudget n` (or equality with `coordinateBits n`) and
  `2 ^ n ≤ N`;
* `realized_of_splitPrimeBands_paperBits` / `realized_dyadic_of_paperBits`:
  the corresponding realization theorems for arbitrary and dyadic split-prime
  bands;
* `paperSplitBand`: the one-band family with the paper's budget, its
  `BandProductSmall`, `L4SubInputs`, and realization `realized_paperSplitBand`.
  This is the bit-budget analogue of
  `RandomizedL4Bands.realized_fullSplitBand`;
* positivity: `paperBitBudget n > 0` for `n ≥ 7`, the endpoint is `> 1`, and
  the allocation `b ≡ paperBitBudget n` has positive total.  Hence the budget
  is genuinely positive, not a zero-budget degeneration;
* `unrealizedTuples_fullSplitBand_card_eq_zero` and
  `unrealizedTuples_paperSplitBand_card_eq_zero`: the cardinality statement
  consumed by the Wave 13 L4 leaf, for the maximal band and for the paper's
  bit-budget band.

Nothing here is a `sorry`, `admit`, `axiom`, or `native_decide`, and the bit
budget is never set to zero.
-/

namespace Cogentic.RandomizedL4BitBudget

open Finset
open scoped BigOperators

open Cogentic.RandomizedL4
open Cogentic.RandomizedL4Bands
open Cogentic.RandomizedL4Sub
open Cogentic.RandomizedReducedFormSupply
open Cogentic.RandomizedFormGroup

noncomputable section

/-!
## Section 1: The paper's total bit budget
-/

/-- The paper's total private bit budget `⌊(n - 1) / 2⌋ - 2`, written in the
same normalization as `RandomizedBalancedAllocation.coordinateBits`. -/
abbrev paperBitBudget (n : ℕ) : ℕ :=
  Cogentic.RandomizedBalancedAllocation.coordinateBits n

/-- The explicit arithmetic form of the paper's bit budget. -/
theorem paperBitBudget_eq (n : ℕ) : paperBitBudget n = (n - 1) / 2 - 2 := rfl

/-- **The smallest scalar inequality for the bit budget.**  Twice the paper's
bit budget is at most `n - 1`. -/
theorem two_mul_paperBitBudget_le_pred (n : ℕ) : 2 * paperBitBudget n ≤ n - 1 := by
  rw [paperBitBudget_eq]
  set d : ℕ := (n - 1) / 2 with hd
  have hd2 : d * 2 ≤ n - 1 := Nat.div_mul_le_self (n - 1) 2
  have hsub : (d - 2) * 2 ≤ d * 2 := Nat.mul_le_mul_right 2 (Nat.sub_le d 2)
  have hmain : (d - 2) * 2 ≤ n - 1 := hsub.trans hd2
  simpa [mul_comm] using hmain

/-- Twice the paper's bit budget is at most the input bit length. -/
theorem two_mul_paperBitBudget_le (n : ℕ) : 2 * paperBitBudget n ≤ n :=
  (two_mul_paperBitBudget_le_pred n).trans (Nat.sub_le n 1)

/-- The exponent identity `(2 ^ k) ^ 2 = 2 ^ (2 * k)`. -/
private theorem two_pow_sq_eq (k : ℕ) : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by
  calc
    (2 ^ k) ^ 2 = (2 ^ k) * (2 ^ k) := by ring
    _ = 2 ^ (k + k) := by rw [← pow_add]
    _ = 2 ^ (2 * k) := by
          congr 1
          ring

/-- **The paper's budget is below `√N`.**  From `2 ^ (n - 1) ≤ N`, the square
of the paper's endpoint is already at most `N` (stronger than the `2 * N` used by
L4). -/
theorem paperBitBudget_pow_sq_le_modulus {N n : ℕ} (hN : 2 ^ (n - 1) ≤ N) :
    (2 ^ paperBitBudget n) ^ 2 ≤ N := by
  have h2k : 2 * paperBitBudget n ≤ n - 1 := two_mul_paperBitBudget_le_pred n
  have hpow : 2 ^ (2 * paperBitBudget n) ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) h2k
  rw [two_pow_sq_eq]
  exact hpow.trans hN

/-- **The paper's bit budget satisfies the L4 band-size condition** from the
weaker hypothesis `2 ^ (n - 1) ≤ N`. -/
theorem paperBitBudget_pow_sq_le_of_size {N n : ℕ} (hN : 2 ^ (n - 1) ≤ N) :
    (2 ^ paperBitBudget n) ^ 2 ≤ 2 * N :=
  (paperBitBudget_pow_sq_le_modulus hN).trans
    (Nat.le_mul_of_pos_left N (by norm_num))

/-- **The paper's bit budget satisfies the L4 band-size condition.**  If the
modulus has at least `n` bits (`2 ^ n ≤ N`), then the single-band upper endpoint
`2 ^ paperBitBudget n` has square at most `2 * N`. -/
theorem paperBitBudget_pow_sq_le {N n : ℕ} (hN : 2 ^ n ≤ N) :
    (2 ^ paperBitBudget n) ^ 2 ≤ 2 * N :=
  paperBitBudget_pow_sq_le_of_size
    ((Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)).trans hN)

/-- **The paper's bit budget at the actual input bit length.**  For every
positive `N`, using `n = N.size`, the paper's single-band endpoint satisfies the
L4 band-size condition. -/
theorem paperBitBudget_pow_sq_le_natSize (N : ℕ) (hN : 0 < N) :
    (2 ^ paperBitBudget N.size) ^ 2 ≤ 2 * N := by
  refine paperBitBudget_pow_sq_le_of_size ?_
  have hlt : N.size - 1 < N.size :=
    Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp (Nat.size_pos.mpr hN))
  exact Nat.lt_size.mp hlt

/-- The paper's band upper endpoint when the whole budget is assigned to one
band. -/
def paperBandUpper (n : ℕ) : ℕ := 2 ^ paperBitBudget n

/-- The paper's band endpoint is positive. -/
theorem paperBandUpper_pos (n : ℕ) : 0 < paperBandUpper n :=
  pow_pos (by norm_num) _

/-- For `n ≥ 7` the paper's budget is strictly positive (the first positive
value is `1` at `n = 7`). -/
theorem paperBitBudget_pos {n : ℕ} (hn : 7 ≤ n) : 0 < paperBitBudget n := by
  rw [paperBitBudget_eq]
  have h6 : 6 ≤ n - 1 := by omega
  have h3 : 3 ≤ (n - 1) / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by omega)
  omega

/-- The budget is not zero at the paper's first nontrivial scale. -/
theorem paperBitBudget_ne_zero {n : ℕ} (hn : 7 ≤ n) : paperBitBudget n ≠ 0 :=
  Nat.ne_of_gt (paperBitBudget_pos hn)

/-- The paper's band endpoint is genuinely above `1` once the budget is
positive, so the band is a nondegenerate interval. -/
theorem one_lt_paperBandUpper {n : ℕ} (hn : 7 ≤ n) : 1 < paperBandUpper n := by
  unfold paperBandUpper
  exact one_lt_pow' (by norm_num) (paperBitBudget_ne_zero hn)

/-- A concrete positive witness: at `n = 7` the paper's budget is `1`. -/
theorem paperBitBudget_seven : paperBitBudget 7 = 1 := by decide

/-- A concrete positive witness: at `n = 7` the budget is strictly positive. -/
theorem paperBitBudget_seven_pos : 0 < paperBitBudget 7 := by decide

/-- **The budget is genuinely positive.**  For `n ≥ 7` there is an allocation of
one band whose total bit count is positive and still within the paper's budget. -/
theorem exists_positive_paperAllocation {n : ℕ} (hn : 7 ≤ n) :
    ∃ b : Fin 1 → ℕ, 0 < ∑ i, b i ∧ ∑ i, b i ≤ paperBitBudget n := by
  refine ⟨fun _ => paperBitBudget n, ?_, ?_⟩
  · simpa using paperBitBudget_pos hn
  · simp

/-!
## Section 2: The band-size condition for `m` bands
-/

/-- **The explicit scalar band-size inequality.**  With `m` bands whose
per-band bit allocations sum to at most the paper's total budget, the product of
the dyadic upper endpoints has square at most `2 * N`. -/
theorem paperBandProductBound {N n m : ℕ} (hN : 2 ^ n ≤ N)
    (b : Fin m → ℕ) (hbits : ∑ i, b i ≤ paperBitBudget n) :
    (∏ i, (2 : ℕ) ^ b i) ^ 2 ≤ 2 * N := by
  have hprod : (∏ i, (2 : ℕ) ^ b i) = 2 ^ (∑ i, b i) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin m)) b (2 : ℕ))
  rw [hprod]
  have hpow : 2 ^ (∑ i, b i) ≤ 2 ^ paperBitBudget n :=
    Nat.pow_le_pow_right (by norm_num) hbits
  exact (Nat.pow_le_pow_left hpow 2).trans (paperBitBudget_pow_sq_le hN)

/-- The endpoint product in the single exponent form `2 ^ (∑ i, b i)`. -/
theorem paperBitBudget_sum_pow_sq_le {N n m : ℕ} (hN : 2 ^ n ≤ N)
    (b : Fin m → ℕ) (hbits : ∑ i, b i ≤ paperBitBudget n) :
    (2 ^ (∑ i, b i)) ^ 2 ≤ 2 * N := by
  have hprod : (∏ i, (2 : ℕ) ^ b i) = 2 ^ (∑ i, b i) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin m)) b (2 : ℕ))
  rw [← hprod]
  exact paperBandProductBound hN b hbits

/-- **`BandProductSmall` from the paper's total bit budget.**  Every band is a
subfamily of a split-prime bin with upper endpoint `2 ^ (b i)`; the only
arithmetic input is the scalar inequality `∑ i, b i ≤ paperBitBudget n` and
`2 ^ n ≤ N`. -/
theorem bandProductSmall_of_paperBits {N n m : ℕ} {P : Fin m → Finset ℕ}
    {lo b : Fin m → ℕ}
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (2 ^ b i))
    (hbits : ∑ i, b i ≤ paperBitBudget n)
    (hN : 2 ^ n ≤ N) :
    BandProductSmall N m P := by
  refine bandProductSmall_of_bitBudget hsub ?_
  exact paperBitBudget_sum_pow_sq_le hN b hbits

/-- **`BandProductSmall` when the allocation has exactly the paper's total.**
This is the form in which the manuscript allocates the private bits. -/
theorem bandProductSmall_of_coordinateBits {N n m : ℕ} {P : Fin m → Finset ℕ}
    {lo b : Fin m → ℕ}
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (2 ^ b i))
    (hbits : ∑ i, b i = Cogentic.RandomizedBalancedAllocation.coordinateBits n)
    (hN : 2 ^ n ≤ N) :
    BandProductSmall N m P := by
  refine bandProductSmall_of_paperBits hsub ?_ hN
  rw [hbits]

/-- **`BandProductSmall` for the dyadic split-prime bands** under the paper's
total bit budget. -/
theorem bandProductSmall_dyadic_of_paperBits {N n m : ℕ} {b : Fin m → ℕ}
    (hbits : ∑ i, b i ≤ paperBitBudget n) (hN : 2 ^ n ≤ N) :
    BandProductSmall N m (dyadicSplitPrimeBands N b) := by
  refine bandProductSmall_dyadicSplitPrimeBands b ?_
  exact paperBitBudget_sum_pow_sq_le hN b hbits

/-!
## Section 3: Realization under the bit budget
-/

/-- **Realization for arbitrary split-prime band subfamilies under the paper's
bit budget.**  This is the bit-budget form of
`RandomizedL4Bands.realized_of_splitPrimeBands`, with the endpoint product
condition replaced by the scalar count `∑ i, b i ≤ paperBitBudget n`. -/
theorem realized_of_splitPrimeBands_paperBits {N n m : ℕ}
    {P : Fin m → Finset ℕ} {lo b : Fin m → ℕ}
    (hNodd : Odd N)
    (hsub : ∀ i, P i ⊆ splitPrimeBin N (lo i) (2 ^ b i))
    (hbits : ∑ i, b i ≤ paperBitBudget n)
    (hN : 2 ^ n ≤ N) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 := by
  refine realized_of_splitPrimeBin_bitBudget hNodd hsub ?_
  exact paperBitBudget_sum_pow_sq_le hN b hbits

/-- **Realization for the paper's dyadic split-prime bands.** -/
theorem realized_dyadic_of_paperBits {N n m : ℕ} {b : Fin m → ℕ}
    (hNodd : Odd N)
    (hbits : ∑ i, b i ≤ paperBitBudget n)
    (hN : 2 ^ n ≤ N) :
    ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ dyadicSplitPrimeBands N b i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 := by
  refine realized_of_splitPrimeBin_bitBudget hNodd (fun _ => subset_rfl) ?_
  exact paperBitBudget_sum_pow_sq_le hN b hbits

/-!
## Section 4: The one-band paper family

This is the bit-budget analogue of `RandomizedL4Bands.fullSplitBand`: the
maximal one-band family is replaced by the band with the paper's actual endpoint
`2 ^ paperBitBudget n`.
-/

/-- The paper's one-band split-prime family: all split primes in
`(0, 2 ^ paperBitBudget n]`. -/
noncomputable def paperSplitBand (N n : ℕ) : Fin 1 → Finset ℕ :=
  fun _ => splitPrimeBin N 0 (paperBandUpper n)

/-- Unfolding the paper band as a `splitPrimeBin`. -/
theorem paperSplitBand_apply (N n : ℕ) :
    paperSplitBand N n = fun _ => splitPrimeBin N 0 (paperBandUpper n) := rfl

/-- Raising the upper endpoint enlarges a split-prime bin. -/
theorem splitPrimeBin_subset_of_upper {N A B B' : ℕ} (hB : B ≤ B') :
    splitPrimeBin N A B ⊆ splitPrimeBin N A B' := by
  intro p hp
  simp only [splitPrimeBin, Cogentic.Randomized.primeBin,
    Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
  exact ⟨⟨⟨hp.1.1.1, hp.1.1.2.trans hB⟩, hp.1.2⟩, hp.2⟩

/-- The paper band is contained in the maximal band `fullSplitBand`. -/
theorem paperSplitBand_subset_fullSplitBand {N n : ℕ} (hN : 2 ^ n ≤ N) :
    ∀ i, paperSplitBand N n i ⊆ fullSplitBand N i := by
  intro i
  have hle : paperBandUpper n ≤ Nat.sqrt (2 * N) := by
    rw [Nat.le_sqrt]
    simpa [paperBandUpper, pow_two] using paperBitBudget_pow_sq_le hN
  simpa [paperSplitBand, fullSplitBand] using
    splitPrimeBin_subset_of_upper (N := N) (A := 0) (B := paperBandUpper n)
      (B' := Nat.sqrt (2 * N)) hle

/-- **The paper's band satisfies `BandProductSmall`.** -/
theorem bandProductSmall_paperSplitBand {N n : ℕ} (hN : 2 ^ n ≤ N) :
    BandProductSmall N 1 (paperSplitBand N n) := by
  refine bandProductSmall_splitPrimeBands (fun _ => 0) (fun _ => paperBandUpper n) ?_
  simpa [paperBandUpper] using paperBitBudget_pow_sq_le (N := N) hN

/-- **`BandSplit` for the paper's band** for odd `N`. -/
theorem bandSplit_paperSplitBand {N n : ℕ} (hNodd : Odd N) :
    BandSplit N 1 (paperSplitBand N n) :=
  bandSplit_splitPrimeBands (fun _ => 0) (fun _ => paperBandUpper n) hNodd

/-- **The reduced L4 inputs for the paper's one-band family.**  The only
arithmetic hypothesis is the bit-budget inequality `2 ^ n ≤ N`. -/
theorem L4SubInputs_of_paperSplitBand {N n : ℕ} (hNodd : Odd N)
    (hN : 2 ^ n ≤ N) :
    L4SubInputs N 1 (paperSplitBand N n) :=
  L4SubInputs.ofOddSplitBands hNodd (bandSplit_paperSplitBand hNodd)
    (bandProductSmall_paperSplitBand hN)

/-- **Realization for the paper's one-band family.**  Primality and
coprimality are read off from `splitPrimeBin`, exactly as in
`RandomizedL4Bands.realized_fullSplitBand`; the extra hypothesis is the explicit
bit budget `2 ^ n ≤ N`. -/
theorem realized_paperSplitBand {N n : ℕ} (hNodd : Odd N) (hN : 2 ^ n ≤ N) :
    ∀ (t : ∀ _i : Fin 1, {p : ℕ // p ∈ paperSplitBand N n _i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs (L4SubInputs_of_paperSplitBand hNodd hN)
    (fun _ _ hp => prime_of_mem_splitPrimeBin hp)
    (fun _ _ hp => coprime_eight_mul_of_mem_splitPrimeBin hNodd hp)

/-- Realization for the paper band obtained from the maximal-band theorem via
the subset inclusion. -/
theorem realized_paperSplitBand_via_full {N n : ℕ} (hNodd : Odd N)
    (hN : 2 ^ n ≤ N) :
    ∀ (t : ∀ _i : Fin 1, {p : ℕ // p ∈ paperSplitBand N n _i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 := by
  refine realized_of_splitPrimeBin_subsets hNodd (paperSplitBand_subset_fullSplitBand hN) ?_
  simpa using Nat.sqrt_le' (2 * N)

/-- **The paper band's realization directly from `realized_fullSplitBand`.**  A
paper-band tuple is a maximal-band tuple by
`paperSplitBand_subset_fullSplitBand`, so the unconditional maximal-band theorem
applies. -/
theorem realized_paperSplitBand_from_full {N n : ℕ} (hNodd : Odd N)
    (hN : 2 ^ n ≤ N) :
    ∀ (t : ∀ _i : Fin 1, {p : ℕ // p ∈ paperSplitBand N n _i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 := by
  intro t hgenus hinj
  let t' : ∀ _i : Fin 1, {p : ℕ // p ∈ fullSplitBand N _i} :=
    fun i => ⟨(t i).1, paperSplitBand_subset_fullSplitBand hN i (t i).2⟩
  have hgenus' : (∏ i, genusMap N (t' i).1) = 1 := by simpa [t'] using hgenus
  have hinj' : Function.Injective (fun i => (t' i).1) := by simpa [t'] using hinj
  simpa [t'] using realized_fullSplitBand N hNodd t' hgenus' hinj'

/-- **`realized_fullSplitBand` under the paper's explicit bit budget.**  The
maximal-band theorem restricts to the paper's budgeted band, because
`paperSplitBand_subset_fullSplitBand` puts every budgeted tuple inside
`fullSplitBand`. -/
theorem realized_fullSplitBand_of_bitBudget {N n : ℕ} (hNodd : Odd N)
    (hN : 2 ^ n ≤ N) :
    ∀ (t : ∀ _i : Fin 1, {p : ℕ // p ∈ paperSplitBand N n _i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_paperSplitBand_from_full hNodd hN

/-- **The paper band at the actual input bit length.**  For every positive `N`,
the band with the manuscript's total budget `⌊(N.size - 1) / 2⌋ - 2` satisfies
`BandProductSmall`. -/
theorem bandProductSmall_paperSplitBand_natSize (N : ℕ) (hN : 0 < N) :
    BandProductSmall N 1 (paperSplitBand N N.size) := by
  refine bandProductSmall_splitPrimeBands (fun _ => 0)
    (fun _ => paperBandUpper N.size) ?_
  simpa [paperBandUpper] using paperBitBudget_pow_sq_le_natSize N hN

/-- **The paper band at the actual input bit length satisfies the reduced L4
inputs.** -/
theorem L4SubInputs_of_paperSplitBand_natSize (N : ℕ) (hN : 0 < N)
    (hNodd : Odd N) :
    L4SubInputs N 1 (paperSplitBand N N.size) :=
  L4SubInputs.ofOddSplitBands hNodd (bandSplit_paperSplitBand hNodd)
    (bandProductSmall_paperSplitBand_natSize N hN)

/-- **Realization for the paper band at the actual input bit length.**  For
every odd positive `N`, the manuscript-shaped band with total budget
`⌊(N.size - 1) / 2⌋ - 2` realizes every principal-genus injective tuple as a
reduced form. -/
theorem realized_paperSplitBand_natSize (N : ℕ) (hN : 0 < N) (hNodd : Odd N) :
    ∀ (t : ∀ _i : Fin 1, {p : ℕ // p ∈ paperSplitBand N N.size _i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_of_l4SubInputs (L4SubInputs_of_paperSplitBand_natSize N hN hNodd)
    (fun _ _ hp => prime_of_mem_splitPrimeBin hp)
    (fun _ _ hp => coprime_eight_mul_of_mem_splitPrimeBin hNodd hp)

/-!
## Section 5: The `unrealizedTuples` cardinality statement

The Wave 13 L4 leaf uses the real-valued cardinality
`((unrealizedTuples (N := N) (fullSplitBand N)).card : ℝ) = 0`.  We prove it
both for the maximal band and for the paper's bit-budget band.
-/

/-- A general cardinality form: a realized family has no unrealized tuples. -/
theorem unrealizedTuples_card_eq_zero_of_realized {N m : ℕ}
    {P : Fin m → Finset ℕ}
    (hreal : ∀ t : ∀ i : Fin m, {p : ℕ // p ∈ P i},
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1) :
    ((unrealizedTuples (N := N) P).card : ℝ) = 0 := by
  classical
  have hempty : unrealizedTuples (N := N) P = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro t ht
    simp only [unrealizedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact ht.2.2 (hreal t ht.1 ht.2.1)
  rw [hempty]
  simp

/-- **The maximal split band has no unrealized tuples.** -/
theorem unrealizedTuples_fullSplitBand_eq_empty (N : ℕ) (hN : Odd N) :
    unrealizedTuples (N := N) (fullSplitBand N) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  simp only [unrealizedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  exact ht.2.2 (realized_fullSplitBand N hN t ht.1 ht.2.1)

/-- **The Wave 13 L4 cardinality statement for the maximal split band.**  This is
exactly the real-valued cardinality consumed by `wave13L4Loss`. -/
theorem unrealizedTuples_fullSplitBand_card_eq_zero (N : ℕ) (hN : Odd N) :
    ((unrealizedTuples (N := N) (fullSplitBand N)).card : ℝ) = 0 := by
  rw [unrealizedTuples_fullSplitBand_eq_empty N hN]
  simp

/-- **The paper's bit-budget band has no unrealized tuples.** -/
theorem unrealizedTuples_paperSplitBand_eq_empty {N n : ℕ} (hNodd : Odd N)
    (hN : 2 ^ n ≤ N) :
    unrealizedTuples (N := N) (paperSplitBand N n) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  simp only [unrealizedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  exact ht.2.2 (realized_paperSplitBand hNodd hN t ht.1 ht.2.1)

/-- **The Wave 13 L4 cardinality statement for the paper's bit-budget band.** -/
theorem unrealizedTuples_paperSplitBand_card_eq_zero {N n : ℕ} (hNodd : Odd N)
    (hN : 2 ^ n ≤ N) :
    ((unrealizedTuples (N := N) (paperSplitBand N n)).card : ℝ) = 0 := by
  rw [unrealizedTuples_paperSplitBand_eq_empty hNodd hN]
  simp

/-! ## Axiom audit -/

#print axioms two_mul_paperBitBudget_le_pred
#print axioms two_mul_paperBitBudget_le
#print axioms paperBitBudget_pow_sq_le_modulus
#print axioms paperBitBudget_pow_sq_le_of_size
#print axioms paperBitBudget_pow_sq_le
#print axioms paperBitBudget_pow_sq_le_natSize
#print axioms paperBitBudget_pos
#print axioms paperBitBudget_ne_zero
#print axioms paperBandUpper_pos
#print axioms one_lt_paperBandUpper
#print axioms exists_positive_paperAllocation
#print axioms paperBandProductBound
#print axioms paperBitBudget_sum_pow_sq_le
#print axioms bandProductSmall_of_paperBits
#print axioms bandProductSmall_of_coordinateBits
#print axioms bandProductSmall_dyadic_of_paperBits
#print axioms realized_of_splitPrimeBands_paperBits
#print axioms realized_dyadic_of_paperBits
#print axioms splitPrimeBin_subset_of_upper
#print axioms paperSplitBand_subset_fullSplitBand
#print axioms bandProductSmall_paperSplitBand
#print axioms bandSplit_paperSplitBand
#print axioms L4SubInputs_of_paperSplitBand
#print axioms realized_paperSplitBand
#print axioms realized_paperSplitBand_via_full
#print axioms realized_paperSplitBand_from_full
#print axioms realized_fullSplitBand_of_bitBudget
#print axioms bandProductSmall_paperSplitBand_natSize
#print axioms L4SubInputs_of_paperSplitBand_natSize
#print axioms realized_paperSplitBand_natSize
#print axioms unrealizedTuples_card_eq_zero_of_realized
#print axioms unrealizedTuples_fullSplitBand_eq_empty
#print axioms unrealizedTuples_fullSplitBand_card_eq_zero
#print axioms unrealizedTuples_paperSplitBand_eq_empty
#print axioms unrealizedTuples_paperSplitBand_card_eq_zero

end

end Cogentic.RandomizedL4BitBudget
