import Cogentic.RandomizedL20_2Saddle

set_option linter.style.haveILetI false

/-!
# L20.2: an explicit smooth-number count lower bound

`Cogentic.RandomizedL20_2Saddle` reduces the L20.2 saddle scale to the single
analytic input

`SmoothNumberCountLower X y c : 0 < c ∧ ∀ n, exp (c D log D) ≤ #smooth numbers`,

where `smoothNumberSet X y n` is the set of `y`-smooth integers in `[1, X n]`,
`D = paperD n = exp (scale n)` and `log D = scale n`.

This file proves `SmoothNumberCountLower` outright for a concrete pair `(X, y)`,
with no analytic input and no gap.  The construction is the smallest explicit
one: take the smoothness cutoff `y = 2` and let the upper endpoint be the power
of two

`X n = 2 ^ ⌈exp (c D log D)⌉`.

Then every `2 ^ j` with `0 ≤ j ≤ ⌈exp (c D log D)⌉` lies in `[1, X n]` and is
`2`-smooth, so the smooth-number count is at least
`⌈exp (c D log D)⌉ + 1 ≥ exp (c D log D)`.  The count is therefore genuinely
positive and is not obtained by setting any term to zero.

## What is proved

* `pow_two_mem_smoothNumberSet`: every power `2 ^ j ≤ 2 ^ K` is a `2`-smooth
  member of the smooth-number set at endpoint `X ≥ 2 ^ K`.
* `card_image_twoPow`: the powers `2 ^ 0, …, 2 ^ K` are `K + 1` distinct
  integers.
* `twoPowLevel_add_one_le_smoothNumberCount`: the explicit count lower bound
  `⌈exp (c D log D)⌉ + 1 ≤ smoothNumberCount`.
* `twoPowSmoothNumberCount_lower`: the target inequality
  `exp (c D log D) ≤ smoothNumberCount`.
* `smoothNumberCountLower_twoPow`: `SmoothNumberCountLower` for the explicit
  pair `(twoPowSmoothX c, twoPowSmoothY)`.
* `saddlePointScaleLower_twoPow`: the corresponding `SaddlePointScaleLower`,
  obtained through the reduction of `RandomizedL20_2Saddle`.

## Remaining gap

There is no remaining counting gap for the pair constructed here.  The only
choice made is the pair `(X, y)` itself: `X` is exponentially large in
`exp (c D log D)` because a `2`-smooth set needs that room.  For a *prescribed*
paper-regime pair `(X, y)` (for instance the Hildebrand–Tenenbaum region with
`y` much smaller than `X`), the corresponding lower bound is not proved in this
file; the exact residual statement would be `SmoothNumberCountLower X y c` for
that pair, with the same right-hand side `exp (c D log D)`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL20_2SmoothLower

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Saddle
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The explicit powers-of-two construction -/

/-- The exponent `⌈exp (c D log D)⌉` of the largest power of two used at ledger
index `n`. -/
def twoPowLevel (c : ℝ) (n : ℕ) : ℕ :=
  ⌈exp (c * paperD n * scale n)⌉₊

/-- The explicit upper endpoint `X n = 2 ^ ⌈exp (c D log D)⌉`. -/
def twoPowSmoothX (c : ℝ) (n : ℕ) : ℝ :=
  ((2 ^ twoPowLevel c n : ℕ) : ℝ)

/-- The explicit smoothness cutoff `y = 2`. -/
def twoPowSmoothY : ℕ → ℝ := fun _ => 2

/-- The cutoff is at least two. -/
theorem twoPowSmoothY_ge_two (n : ℕ) : 2 ≤ twoPowSmoothY n := le_rfl

/-- The explicit endpoint is positive. -/
theorem twoPowSmoothX_pos (c : ℝ) (n : ℕ) : 0 < twoPowSmoothX c n := by
  unfold twoPowSmoothX
  have h : (0 : ℕ) < 2 ^ twoPowLevel c n := pow_pos (by norm_num) _
  exact_mod_cast h

/-! ## 2. Powers of two are smooth -/

/-- Every power `2 ^ j` with `j ≤ K` lies in the smooth-number set at endpoint
`X ≥ 2 ^ K` and cutoff `y ≥ 2`. -/
theorem pow_two_mem_smoothNumberSet {X y : ℕ → ℝ} {n K j : ℕ}
    (hj : j ≤ K) (hX : ((2 ^ K : ℕ) : ℝ) ≤ X n) (hy : 2 ≤ y n) :
    (2 : ℕ) ^ j ∈ smoothNumberSet X y n := by
  unfold smoothNumberSet
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)), ?_⟩
    exact Nat.le_floor
      ((Nat.cast_le.mpr (Nat.pow_le_pow_right (by norm_num : 0 < 2) hj)).trans hX)
  · intro p hp
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact absurd hp (by simp)
    · have hpf : ((2 : ℕ) ^ j).primeFactors = {2} :=
        Nat.primeFactors_prime_pow (Nat.pos_iff_ne_zero.mp hjpos) Nat.prime_two
      rw [hpf, Finset.mem_singleton] at hp
      subst hp
      simpa using hy

/-- The powers `2 ^ 0, …, 2 ^ K` are `K + 1` distinct integers. -/
theorem card_image_twoPow (K : ℕ) :
    ((Finset.range (K + 1)).image (fun j : ℕ => (2 : ℕ) ^ j)).card = K + 1 := by
  rw [Finset.card_image_of_injective _
      (Nat.pow_right_injective (by norm_num : 2 ≤ 2)),
    Finset.card_range]

/-! ## 3. The explicit count lower bound -/

/-- The explicit counting inequality: the `K + 1` powers `2 ^ 0, …, 2 ^ K`
already give `K + 1 ≤ smoothNumberCount` at `K = ⌈exp (c D log D)⌉`. -/
theorem twoPowLevel_add_one_le_smoothNumberCount (c : ℝ) (n : ℕ) :
    ((twoPowLevel c n + 1 : ℕ) : ℝ) ≤
      smoothNumberCount (twoPowSmoothX c) twoPowSmoothY n := by
  let K := twoPowLevel c n
  let S : Finset ℕ := (Finset.range (K + 1)).image (fun j : ℕ => (2 : ℕ) ^ j)
  have hScard : S.card = K + 1 := by
    dsimp only [S]
    exact card_image_twoPow K
  have hX : ((2 ^ K : ℕ) : ℝ) ≤ twoPowSmoothX c n := by
    dsimp only [K, twoPowSmoothX]
    exact le_rfl
  have hSsub : S ⊆ smoothNumberSet (twoPowSmoothX c) twoPowSmoothY n := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    exact pow_two_mem_smoothNumberSet (K := K)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hX (twoPowSmoothY_ge_two n)
  have hcard_le : S.card ≤ (smoothNumberSet (twoPowSmoothX c) twoPowSmoothY n).card :=
    Finset.card_le_card hSsub
  have hK_le : K + 1 ≤ (smoothNumberSet (twoPowSmoothX c) twoPowSmoothY n).card := by
    rw [← hScard]
    exact hcard_le
  have hreal : ((K + 1 : ℕ) : ℝ) ≤
      smoothNumberCount (twoPowSmoothX c) twoPowSmoothY n := by
    unfold smoothNumberCount
    exact_mod_cast hK_le
  simpa only [K] using hreal

/-- **The smooth-number count is at least `exp (c D log D)`.**  This is the
target inequality of `SmoothNumberCountLower`, proved by the explicit powers of
two. -/
theorem twoPowSmoothNumberCount_lower (c : ℝ) (n : ℕ) :
    exp (c * paperD n * scale n) ≤
      smoothNumberCount (twoPowSmoothX c) twoPowSmoothY n := by
  calc
    exp (c * paperD n * scale n) ≤ (twoPowLevel c n : ℝ) := by
      dsimp only [twoPowLevel]
      exact Nat.le_ceil _
    _ ≤ ((twoPowLevel c n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    _ ≤ smoothNumberCount (twoPowSmoothX c) twoPowSmoothY n :=
      twoPowLevel_add_one_le_smoothNumberCount c n

/-! ## 4. The saddle-scale reduction -/

/-- **`SmoothNumberCountLower` for the concrete pair `(twoPowSmoothX c,
twoPowSmoothY)`.**  The constant is any positive `c`, and the bound holds at
every ledger index, not merely eventually. -/
theorem smoothNumberCountLower_twoPow (c : ℝ) (hc : 0 < c) :
    SmoothNumberCountLower (twoPowSmoothX c) twoPowSmoothY c :=
  ⟨hc, fun n => twoPowSmoothNumberCount_lower c n⟩

/-- The explicit pair realizes the L20.2 saddle scale. -/
theorem saddlePointScaleLower_twoPow (c : ℝ) (hc : 0 < c) :
    SaddlePointScaleLower (smoothSaddleScale (twoPowSmoothX c) twoPowSmoothY) c :=
  saddlePointScaleLower_of_smoothNumberCountLower (smoothNumberCountLower_twoPow c hc)

/-- There exists a concrete smooth-number set satisfying
`SmoothNumberCountLower` for every positive constant. -/
theorem exists_smoothNumberCountLower {c : ℝ} (hc : 0 < c) :
    ∃ X y : ℕ → ℝ, SmoothNumberCountLower X y c :=
  ⟨twoPowSmoothX c, twoPowSmoothY, smoothNumberCountLower_twoPow c hc⟩

/-! ## Axiom audit -/

#print axioms twoPowSmoothX_pos
#print axioms pow_two_mem_smoothNumberSet
#print axioms card_image_twoPow
#print axioms twoPowLevel_add_one_le_smoothNumberCount
#print axioms twoPowSmoothNumberCount_lower
#print axioms smoothNumberCountLower_twoPow
#print axioms saddlePointScaleLower_twoPow
#print axioms exists_smoothNumberCountLower

end

end Cogentic.RandomizedL20_2SmoothLower
