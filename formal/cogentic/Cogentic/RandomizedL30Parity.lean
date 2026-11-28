import Cogentic.RandomizedL30Dickman

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-!
# L30: the odd-half parity fraction of the central smooth orders

`Cogentic/RandomizedL30Dickman` isolated the parity residual

```
CentralOddHalfParity θ p ε :
  ∀ᶠ n, θ * # {m ∈ (p² - p^{3/2}/2, p²] : m is y-smooth}
            ≤ # {m ∈ ... : m % 4 = 2} ,
```

`y = smoothCutoff (paperT p) (paperError ε) n`, and used it together with the
large-prime Buchstab lower bound to obtain the sharp odd-half central count.
This file analyses the parity residual itself.

## 1. The exact dilation identities (proved)

Write `C₀ = (p² - p^{3/2}/2, p²]` for the central interval and

```
C₁ = (p²/2 - p^{3/2}/4, p²/2] ,   C₂ = (p²/4 - p^{3/2}/8, p²/4]
```

for the halved and quartered central intervals.  Doubling `k ↦ 2 k` is a
bijection between the integers of `C_{j+1}` and the *even* integers of `C_j`,
and it preserves `y`-smoothness for `y ≥ 2`.  Consequently, with
`halfSmoothCount` and `quarterSmoothCount` the smooth counts of `C₁` and `C₂`:

* `centralOddSmoothCount_eq_half_sub_quarter`:
  `# {m ∈ C₀ : m % 4 = 2, smooth} = halfSmoothCount - quarterSmoothCount`.

  This is the divisor-sum ("2-adic valuation") identity: splitting the smooth
  numbers of `C₀` by their `2`-adic valuation `v₂`, the odd-half class is
  exactly `v₂ = 1`, the class `m ≡ 0 (mod 4)` is the image of `C₂`, and the
  even part of `C₀` is the image of all of `C₁`.
* `centralOddSmoothCount_eq_halfOdd_card`: the odd-half central count is
  exactly the number of *odd* smooth integers of `C₁`.  Hence the parity
  fraction of `C₀` is an odd-density statement for `C₁`.

## 2. The exact residual (proved equivalences and reductions)

`centralOddHalfParity_iff_half_sub_quarter` rewrites the target as the
single parity-free cardinality inequality

```
θ * # {smooth in C₀} ≤ halfSmoothCount - quarterSmoothCount ,
```

and `centralOddHalfParity_of_intervalCard` / `..._of_rpow` are sufficient
versions in which the left side is replaced by the explicit cardinality
`|C₀|` (or `p^{3/2}`), so that no parity condition survives:

```
θ * |C₀| ≤ halfSmoothCount - quarterSmoothCount   ⟹   CentralOddHalfParity θ .
```

`centralOddHalfParity_implies_halfOdd` records the converse-looking necessary
condition: the target forces at least a `θ` fraction of the smooth numbers of
the *halved* interval to be odd.

`centralOddHalfParity_iff_oddCentral` gives the sharpest exact form,
`θ · # {odd smooth in C₀} + # {smooth in C₂} ≤ (1 - θ) · # {smooth in C₁}`,
in which the residue class `m % 4 = 2` has disappeared completely.

## 3. The density route cannot give a fixed positive constant (proved)

`centralOddHalfParity_of_relative_global` composes the relative short-interval
density `YounisOddRelativeShortInterval A` with the global odd lower bound
`YounisOddGlobalLower B`.  The parity fraction produced is

```
A * B * exp (-(1+ε) t_p) ,
```

which `densityFraction_tendsto_zero` shows tends to `0` at the paper scale;
`densityFraction_lt_of_pos` therefore shows that this route yields **no** fixed
`θ > 0`.  This is the precise sense in which the global parity bound
`globalOddSmoothCount ≤ p²/4 + 1/2` (an *upper* bound) cannot be transferred to
the central interval by a density argument.

## 4. A non-vacuous instance, and the failure of `θ = 1/2` (proved)

`centralOddHalfParity_thirteen` proves the target outright, with
`θ = 1/4`, for the constant prime scale `p ≡ 13` and the relative error that
makes the paper cutoff exactly `p² = 169`.  At this (all-smooth) cutoff
`C₀ = [146, 169]` has `24` integers, `6` of them `≡ 2 (mod 4)`, so the fraction
is exactly `1/4`.  This shows the residual is consistent and not vacuously
satisfiable only at `θ = 0`.

`thirteen_not_half` proves that `CentralOddHalfParity (1/2)` **fails** at the
same schedule.  Hence no all-smooth or pure-dilation argument can reach the
paper's `θ = 1/2` (`3/8`): the generic parity density of the odd-half residue
class is `1/4`, and the extra factor must come from the sparsity of smooth
numbers at `Y = p^{o(1)}`.

## The exact residual

The target is *equivalent* (proved, §2) to the single cardinality inequality

```
θ * # {smooth in C₀} ≤ halfSmoothCount - quarterSmoothCount ,
```

and to

```
θ * # {odd smooth in C₀} + quarterSmoothCount ≤ (1 - θ) * halfSmoothCount .
```

At a growing prime scale with a *constant* relative error `ε` the paper cutoff is
`exp ((1+ε) t_p) = p^{o(1)}`, so the all-smooth computation of §4 does not
apply: the cutoff never dominates `p²`.  What is missing is a lower bound for
the number of *odd* `y`-smooth integers in `C₁`, i.e. for the difference
`halfSmoothCount - quarterSmoothCount`; the inclusion `C₂ ⊆ C₁` supplies only
the trivial `halfSmoothCount - quarterSmoothCount ≥ 0`.  This is a
short-interval equidistribution statement for the parity of smooth numbers; it
is not implied by the global parity bound (which is an upper bound, §3), by the
Rankin/saddle upper bounds, or by the Buchstab lower bound on the central
interval (which does not see `m % 4`).  The non-vacuity computation of §4 shows
that in the all-smooth regime the fraction is exactly the generic `1/4`, so the
paper's `θ = 1/2` genuinely needs the sparse-cutoff regime.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count is set
to zero.
-/

namespace Cogentic.RandomizedL30Parity

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30CentralCount
open Cogentic.RandomizedL30Dickman
open Cogentic.Randomized

noncomputable section

/-! ## 1. The halved and quartered central intervals -/

/-- The halved central interval `(p²/2 - p^{3/2}/4, p²/2]` as a finite set of
integers.  It is exactly the image of the central interval under division by
`2` on even integers. -/
def halfOrderInterval (p : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  Finset.Icc ⌈p n ^ 2 / 2 - p n ^ ((3 : ℝ) / 2) / 4⌉₊ ⌊p n ^ 2 / 2⌋₊

/-- The quartered central interval `(p²/4 - p^{3/2}/8, p²/4]` as a finite set
of integers.  It is the halved interval of the halved interval. -/
def quarterOrderInterval (p : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  Finset.Icc ⌈p n ^ 2 / 4 - p n ^ ((3 : ℝ) / 2) / 8⌉₊ ⌊p n ^ 2 / 4⌋₊

/-- The `y`-smooth integers of the halved central interval. -/
noncomputable def halfSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (halfOrderInterval p n).filter (IsSmoothUpTo (smoothCutoff t err n))

/-- The `y`-smooth integers of the quartered central interval. -/
noncomputable def quarterSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (quarterOrderInterval p n).filter (IsSmoothUpTo (smoothCutoff t err n))

/-- The number of `y`-smooth integers of the halved central interval. -/
noncomputable def halfSmoothCount (p t err : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((halfSmoothOrders p t err n).card : ℝ)

/-- The number of `y`-smooth integers of the quartered central interval. -/
noncomputable def quarterSmoothCount (p t err : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((quarterSmoothOrders p t err n).card : ℝ)

/-- The even central smooth orders.  Their doubles-halves are the smooth
integers of `C₁`. -/
noncomputable def centralEvenSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (centralSmoothOrders p t err n).filter (fun m => m % 2 = 0)

/-- The odd central smooth orders.  Together with the even ones they partition
the central smooth orders; they correspond to no dilation class and are the
genuinely non-parity part of the residual. -/
noncomputable def centralOddParitySmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (centralSmoothOrders p t err n).filter (fun m => m % 2 = 1)

/-- The odd smooth integers of the halved central interval.  They correspond
under doubling exactly to the central odd-half smooth orders. -/
noncomputable def halfOddSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (halfSmoothOrders p t err n).filter (fun k => k % 2 = 1)

/-- The even smooth integers of the halved central interval.  They correspond
under halving exactly to the smooth integers of `C₂`. -/
noncomputable def halfEvenSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (halfSmoothOrders p t err n).filter (fun k => k % 2 = 0)

/-- The number of odd smooth integers of the halved central interval. -/
noncomputable def halfOddSmoothCount (p t err : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((halfOddSmoothOrders p t err n).card : ℝ)

/-! ## 2. Doubling and the nested intervals -/

/-- **The halved interval is the halved central interval.**  For every natural
`k`, the double `2 k` lies in the central interval exactly when `k` lies in the
halved interval.  This is the endpoint-exact form of `C₀ = 2 C₁`: the ceiling
and floor roundings match because `k` and `2 k` are integers. -/
theorem mem_halfOrderInterval_iff_two_mul {p : ℕ → ℝ} {n k : ℕ} :
    k ∈ halfOrderInterval p n ↔ 2 * k ∈ centralOrderInterval p n := by
  unfold halfOrderInterval centralOrderInterval
  rw [Finset.mem_Icc, Finset.mem_Icc]
  have hceil : ⌈p n ^ 2 / 2 - p n ^ ((3 : ℝ) / 2) / 4⌉₊ ≤ k ↔
      ⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ ≤ 2 * k := by
    rw [Nat.ceil_le, Nat.ceil_le]
    push_cast
    constructor <;> intro h <;> linarith
  have hfloor : k ≤ ⌊p n ^ 2 / 2⌋₊ ↔ 2 * k ≤ ⌊p n ^ 2⌋₊ := by
    rw [Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ p n ^ 2 / 2),
      Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ p n ^ 2)]
    push_cast
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hceil.mp h1, hfloor.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hceil.mpr h1, hfloor.mpr h2⟩

/-- **The quartered interval is the halved halved interval.** -/
theorem mem_quarterOrderInterval_iff_two_mul {p : ℕ → ℝ} {n j : ℕ} :
    j ∈ quarterOrderInterval p n ↔ 2 * j ∈ halfOrderInterval p n := by
  unfold quarterOrderInterval halfOrderInterval
  rw [Finset.mem_Icc, Finset.mem_Icc]
  have hceil : ⌈p n ^ 2 / 4 - p n ^ ((3 : ℝ) / 2) / 8⌉₊ ≤ j ↔
      ⌈p n ^ 2 / 2 - p n ^ ((3 : ℝ) / 2) / 4⌉₊ ≤ 2 * j := by
    rw [Nat.ceil_le, Nat.ceil_le]
    push_cast
    constructor <;> intro h <;> linarith
  have hfloor : j ≤ ⌊p n ^ 2 / 4⌋₊ ↔ 2 * j ≤ ⌊p n ^ 2 / 2⌋₊ := by
    rw [Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ p n ^ 2 / 4),
      Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ p n ^ 2 / 2)]
    push_cast
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hceil.mp h1, hfloor.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hceil.mpr h1, hfloor.mpr h2⟩

/-- **Doubling preserves smoothness.**  For `y ≥ 2`, an integer `2 k` is
`y`-smooth exactly when `k` is. -/
theorem isSmoothUpTo_two_mul_iff {y : ℝ} (hy : 2 ≤ y) {k : ℕ} (hk : k ≠ 0) :
    IsSmoothUpTo y (2 * k) ↔ IsSmoothUpTo y k := by
  have hpf : (2 * k).primeFactors = insert 2 k.primeFactors := by
    rw [Nat.primeFactors_mul (by norm_num) hk, Nat.Prime.primeFactors Nat.prime_two]
    rfl
  unfold IsSmoothUpTo
  rw [hpf]
  constructor
  · intro h q hq
    exact h q (Finset.mem_insert_of_mem hq)
  · intro h q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hy
    · exact h q hq

/-! ## 3. Endpoint positivity of the nested intervals -/

/-- For `p ≥ 2` the lower endpoint of the halved interval is at least `1`. -/
theorem one_le_half_lower {p : ℝ} (hp : 2 ≤ p) :
    (1 : ℝ) ≤ p ^ 2 / 2 - p ^ ((3 : ℝ) / 2) / 4 := by
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hmono : p ^ ((3 : ℝ) / 2) ≤ p ^ 2 := by
    rw [← Real.rpow_natCast p 2]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hp4 : (4 : ℝ) ≤ p ^ 2 := by nlinarith [sq_nonneg (p - 2), hp]
  nlinarith

/-- For `p ≥ 2` the lower endpoint of the quartered interval is positive. -/
theorem quarter_lower_pos {p : ℝ} (hp : 2 ≤ p) :
    (0 : ℝ) < p ^ 2 / 4 - p ^ ((3 : ℝ) / 2) / 8 := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hmono : p ^ ((3 : ℝ) / 2) ≤ p ^ 2 := by
    rw [← Real.rpow_natCast p 2]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hpos : (0 : ℝ) < p ^ 2 := pow_pos hp0 2
  nlinarith

/-- Every element of the central interval is at least `2` for `p ≥ 2`. -/
theorem two_le_of_mem_centralOrderInterval {p : ℕ → ℝ} {n m : ℕ}
    (hp : 2 ≤ p n) (hm : m ∈ centralOrderInterval p n) : 2 ≤ m := by
  have hlow := two_le_centralInterval_lower (p := p n) hp
  have hceil : (2 : ℕ) ≤ ⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ := by
    have hR : (2 : ℝ) ≤ (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℝ) :=
      hlow.trans (Nat.le_ceil _)
    exact_mod_cast hR
  exact hceil.trans (Finset.mem_Icc.mp hm).1

/-- Every element of the central interval is positive for `p ≥ 1`. -/
theorem pos_of_mem_centralOrderInterval {p : ℕ → ℝ} {n m : ℕ}
    (hp : 1 ≤ p n) (hm : m ∈ centralOrderInterval p n) : 0 < m := by
  have hp0 : (0 : ℝ) < p n := by linarith
  have hmono : p n ^ ((3 : ℝ) / 2) ≤ p n ^ 2 := by
    rw [← Real.rpow_natCast (p n) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp (by norm_num)
  have hL : (0 : ℝ) < p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 := by
    have h2 : (0 : ℝ) < p n ^ 2 := pow_pos hp0 2
    nlinarith
  have hceil : (1 : ℕ) ≤ ⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ := by
    have hR : (0 : ℝ) < (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℝ) :=
      lt_of_lt_of_le hL (Nat.le_ceil _)
    have hpos₀ : 0 < ⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ := by exact_mod_cast hR
    omega
  exact lt_of_lt_of_le hceil (Finset.mem_Icc.mp hm).1

/-- Every element of the halved interval is positive for `p ≥ 2`. -/
theorem one_le_of_mem_halfOrderInterval {p : ℕ → ℝ} {n k : ℕ}
    (hp : 2 ≤ p n) (hk : k ∈ halfOrderInterval p n) : 1 ≤ k := by
  have hlow := one_le_half_lower (p := p n) hp
  have hceil : (1 : ℕ) ≤ ⌈p n ^ 2 / 2 - p n ^ ((3 : ℝ) / 2) / 4⌉₊ := by
    have hR : (1 : ℝ) ≤ (⌈p n ^ 2 / 2 - p n ^ ((3 : ℝ) / 2) / 4⌉₊ : ℝ) :=
      hlow.trans (Nat.le_ceil _)
    exact_mod_cast hR
  exact hceil.trans (Finset.mem_Icc.mp hk).1

/-- Every element of the quartered interval is positive for `p ≥ 2`. -/
theorem one_le_of_mem_quarterOrderInterval {p : ℕ → ℝ} {n j : ℕ}
    (hp : 2 ≤ p n) (hj : j ∈ quarterOrderInterval p n) : 1 ≤ j := by
  have hlow := quarter_lower_pos (p := p n) hp
  have hceil : (1 : ℕ) ≤ ⌈p n ^ 2 / 4 - p n ^ ((3 : ℝ) / 2) / 8⌉₊ := by
    have hR : (0 : ℝ) < (⌈p n ^ 2 / 4 - p n ^ ((3 : ℝ) / 2) / 8⌉₊ : ℝ) :=
      lt_of_lt_of_le hlow (Nat.le_ceil _)
    have : 0 < ⌈p n ^ 2 / 4 - p n ^ ((3 : ℝ) / 2) / 8⌉₊ := by exact_mod_cast hR
    omega
  exact hceil.trans (Finset.mem_Icc.mp hj).1

/-! ## 4. The doubling bijections -/

/-- **The smooth even central orders are the doubles of the halved smooth
orders.** -/
theorem centralEvenSmoothOrders_eq_image {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hy : 2 ≤ smoothCutoff t err n) :
    centralEvenSmoothOrders p t err n =
      (halfSmoothOrders p t err n).image (fun k => 2 * k) := by
  ext m
  constructor
  · intro hm
    rw [centralEvenSmoothOrders, Finset.mem_filter] at hm
    obtain ⟨hmS, hm2⟩ := hm
    have hmI : m ∈ centralOrderInterval p n := (Finset.mem_filter.mp hmS).1
    have hmSmooth : IsSmoothUpTo (smoothCutoff t err n) m :=
      (Finset.mem_filter.mp hmS).2
    have hm_ge : 2 ≤ m := two_le_of_mem_centralOrderInterval hp hmI
    obtain ⟨k, hk⟩ := Nat.even_iff.mpr hm2
    have htwo : 2 * k = m := by omega
    have hk_ne : k ≠ 0 := by omega
    rw [Finset.mem_image]
    refine ⟨k, ?_, htwo⟩
    rw [halfSmoothOrders, Finset.mem_filter]
    refine ⟨mem_halfOrderInterval_iff_two_mul.mpr (htwo ▸ hmI), ?_⟩
    rw [← isSmoothUpTo_two_mul_iff hy hk_ne, htwo]
    exact hmSmooth
  · intro hm
    rw [Finset.mem_image] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    rw [halfSmoothOrders, Finset.mem_filter] at hk
    obtain ⟨hkI, hkS⟩ := hk
    have hk_ge : 1 ≤ k := one_le_of_mem_halfOrderInterval hp hkI
    have hk_ne : k ≠ 0 := by omega
    rw [centralEvenSmoothOrders, Finset.mem_filter]
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_halfOrderInterval_iff_two_mul.mp hkI
    · exact isSmoothUpTo_two_mul_iff hy hk_ne |>.mpr hkS
    · show (2 * k) % 2 = 0
      omega

/-- **The smooth even orders of the halved interval are the doubles of the
quartered smooth orders.** -/
theorem halfEvenSmoothOrders_eq_image {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hy : 2 ≤ smoothCutoff t err n) :
    halfEvenSmoothOrders p t err n =
      (quarterSmoothOrders p t err n).image (fun j => 2 * j) := by
  ext k
  constructor
  · intro hk
    rw [halfEvenSmoothOrders, Finset.mem_filter] at hk
    obtain ⟨hkS, hk2⟩ := hk
    have hkI : k ∈ halfOrderInterval p n := (Finset.mem_filter.mp hkS).1
    have hkSmooth : IsSmoothUpTo (smoothCutoff t err n) k :=
      (Finset.mem_filter.mp hkS).2
    have hk_ge : 1 ≤ k := one_le_of_mem_halfOrderInterval hp hkI
    obtain ⟨j, hj⟩ := Nat.even_iff.mpr hk2
    have htwo : 2 * j = k := by omega
    have hj_ne : j ≠ 0 := by omega
    rw [Finset.mem_image]
    refine ⟨j, ?_, htwo⟩
    rw [quarterSmoothOrders, Finset.mem_filter]
    refine ⟨mem_quarterOrderInterval_iff_two_mul.mpr (htwo ▸ hkI), ?_⟩
    rw [← isSmoothUpTo_two_mul_iff hy hj_ne, htwo]
    exact hkSmooth
  · intro hk
    rw [Finset.mem_image] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    rw [quarterSmoothOrders, Finset.mem_filter] at hj
    obtain ⟨hjI, hjS⟩ := hj
    have hj_ge : 1 ≤ j := one_le_of_mem_quarterOrderInterval hp hjI
    have hj_ne : j ≠ 0 := by omega
    rw [halfEvenSmoothOrders, Finset.mem_filter]
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_quarterOrderInterval_iff_two_mul.mp hjI
    · exact isSmoothUpTo_two_mul_iff hy hj_ne |>.mpr hjS
    · show (2 * j) % 2 = 0
      omega

/-- **The central odd-half orders are the doubles of the odd smooth halved
orders.**  This is the exact bijection between the parity class `m % 4 = 2` of
`C₀` and the odd (hence automatically odd-half after doubling) smooth numbers
of `C₁`. -/
theorem centralOddSmoothOrders_eq_image_halfOdd {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hy : 2 ≤ smoothCutoff t err n) :
    centralOddSmoothOrders p t err n =
      (halfOddSmoothOrders p t err n).image (fun k => 2 * k) := by
  ext m
  constructor
  · intro hm
    rw [centralOddSmoothOrders, Finset.mem_filter] at hm
    obtain ⟨hmS, hm4⟩ := hm
    have hm4' : m % 4 = 2 := hm4
    have hmI : m ∈ centralOrderInterval p n := (Finset.mem_filter.mp hmS).1
    have hmSmooth : IsSmoothUpTo (smoothCutoff t err n) m :=
      (Finset.mem_filter.mp hmS).2
    have hm_ge : 2 ≤ m := two_le_of_mem_centralOrderInterval hp hmI
    have hm2 : m % 2 = 0 := by omega
    obtain ⟨k, hk⟩ := Nat.even_iff.mpr hm2
    have htwo : 2 * k = m := by omega
    have hk_ne : k ≠ 0 := by omega
    have hkodd : k % 2 = 1 := by omega
    rw [Finset.mem_image]
    refine ⟨k, ?_, htwo⟩
    rw [halfOddSmoothOrders, Finset.mem_filter]
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hkodd⟩
    · exact mem_halfOrderInterval_iff_two_mul.mpr (htwo ▸ hmI)
    · rw [← isSmoothUpTo_two_mul_iff hy hk_ne, htwo]
      exact hmSmooth
  · intro hm
    rw [Finset.mem_image] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    rw [halfOddSmoothOrders, Finset.mem_filter] at hk
    obtain ⟨hkH, hkodd⟩ := hk
    rw [halfSmoothOrders, Finset.mem_filter] at hkH
    obtain ⟨hkI, hkS⟩ := hkH
    have hk_ge : 1 ≤ k := one_le_of_mem_halfOrderInterval hp hkI
    have hk_ne : k ≠ 0 := by omega
    rw [centralOddSmoothOrders, Finset.mem_filter]
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_halfOrderInterval_iff_two_mul.mp hkI
    · exact isSmoothUpTo_two_mul_iff hy hk_ne |>.mpr hkS
    · show (2 * k) % 4 = 2
      omega

/-- The even and odd smooth orders of the halved interval partition its smooth
orders. -/
theorem halfSmoothOrders_card_eq_odd_add_even (p t err : ℕ → ℝ) (n : ℕ) :
    (halfSmoothOrders p t err n).card =
      (halfOddSmoothOrders p t err n).card +
        (halfEvenSmoothOrders p t err n).card := by
  have hoddEq : halfOddSmoothOrders p t err n =
      (halfSmoothOrders p t err n).filter (fun k => ¬ k % 2 = 0) := by
    unfold halfOddSmoothOrders
    apply Finset.filter_congr
    intro k _
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := halfSmoothOrders p t err n) (p := fun k => k % 2 = 0)
  rw [← hoddEq] at hsplit
  unfold halfEvenSmoothOrders
  omega

/-- **The odd-half count is the odd smooth count of the halved interval**
(cardinality form). -/
theorem centralOddSmoothOrders_card_eq_halfOdd {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hy : 2 ≤ smoothCutoff t err n) :
    (centralOddSmoothOrders p t err n).card =
      (halfOddSmoothOrders p t err n).card := by
  have himg := centralOddSmoothOrders_eq_image_halfOdd (p := p) (t := t) (err := err)
    (n := n) hp hy
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega)]

/-- **The odd-half central count is the odd smooth count of the halved
interval.** -/
theorem centralOddSmoothCount_eq_halfOdd_card {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hy : 2 ≤ smoothCutoff t err n) :
    centralOddSmoothCount p t err n = halfOddSmoothCount p t err n := by
  unfold centralOddSmoothCount halfOddSmoothCount
  exact_mod_cast centralOddSmoothOrders_card_eq_halfOdd (p := p) (t := t) (err := err)
    (n := n) hp hy

/-- **The divisor-sum (`2`-adic valuation) identity.**  The number of odd-half
central smooth orders equals the smooth count of the halved interval minus the
smooth count of the quartered interval.  Splitting the central smooth numbers
by `v₂`: the `v₂ = 0` class contributes the unknown odd part, the `v₂ = 1`
class is the odd-half count, and the classes `v₂ ≥ 2` are exactly the doubles
of the smooth numbers of `C₂`. -/
theorem centralOddSmoothCount_eq_half_sub_quarter {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hy : 2 ≤ smoothCutoff t err n) :
    centralOddSmoothCount p t err n =
      halfSmoothCount p t err n - quarterSmoothCount p t err n := by
  have hodd := centralOddSmoothOrders_card_eq_halfOdd (p := p) (t := t) (err := err)
    (n := n) hp hy
  have hpart := halfSmoothOrders_card_eq_odd_add_even p t err n
  have heven := halfEvenSmoothOrders_eq_image (p := p) (t := t) (err := err) (n := n) hp hy
  have hquarter : (halfEvenSmoothOrders p t err n).card =
      (quarterSmoothOrders p t err n).card := by
    rw [heven, Finset.card_image_of_injective _ (fun a b h => by omega)]
  have hle : (halfEvenSmoothOrders p t err n).card ≤ (halfSmoothOrders p t err n).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hsub : (halfOddSmoothOrders p t err n).card =
      (halfSmoothOrders p t err n).card - (halfEvenSmoothOrders p t err n).card := by
    omega
  unfold centralOddSmoothCount halfSmoothCount quarterSmoothCount
  rw [hodd, hsub, Nat.cast_sub hle, hquarter]

/-! ## 5. Reformulations and reductions of the parity residual -/

/-- **The parity residual in parity-free form.**  `CentralOddHalfParity θ` is
equivalent to the single cardinality inequality
`θ |smooth C₀| ≤ halfSmoothCount - quarterSmoothCount`. -/
theorem centralOddHalfParity_iff_half_sub_quarter {θ : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (hy : ∀ᶠ n in atTop, 2 ≤ smoothCutoff (paperT p) (paperError ε) n) :
    CentralOddHalfParity θ p ε ↔
      ∀ᶠ n in atTop,
        θ * ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
          halfSmoothCount p (paperT p) (paperError ε) n -
            quarterSmoothCount p (paperT p) (paperError ε) n := by
  constructor
  · intro h
    filter_upwards [h, hy] with n hn hyn
    rwa [centralOddSmoothCount_eq_half_sub_quarter (hp n) hyn] at hn
  · intro h
    filter_upwards [h, hy] with n hn hyn
    rwa [centralOddSmoothCount_eq_half_sub_quarter (hp n) hyn]

/-- **The parity residual as an odd-density statement for the halved
interval.** -/
theorem centralOddHalfParity_iff_halfOdd {θ : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (hy : ∀ᶠ n in atTop, 2 ≤ smoothCutoff (paperT p) (paperError ε) n) :
    CentralOddHalfParity θ p ε ↔
      ∀ᶠ n in atTop,
        θ * ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
          halfOddSmoothCount p (paperT p) (paperError ε) n := by
  constructor
  · intro h
    filter_upwards [h, hy] with n hn hyn
    rwa [centralOddSmoothCount_eq_halfOdd_card (hp n) hyn] at hn
  · intro h
    filter_upwards [h, hy] with n hn hyn
    rwa [centralOddSmoothCount_eq_halfOdd_card (hp n) hyn]

/-- The central smooth orders are contained in the central interval. -/
theorem centralSmoothOrders_card_le_interval (p t err : ℕ → ℝ) (n : ℕ) :
    ((centralSmoothOrders p t err n).card : ℝ) ≤
      ((centralOrderInterval p n).card : ℝ) := by
  have hsub : centralSmoothOrders p t err n ⊆ centralOrderInterval p n :=
    fun _ hm => (Finset.mem_filter.mp hm).1
  exact_mod_cast Finset.card_le_card hsub

/-- **The central smooth orders split as odd plus even-halved.**  The even part
is the double of the smooth numbers of `C₁`, hence `halfSmoothCount`. -/
theorem centralSmoothOrders_card_eq_oddCentral_add_half {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hy : 2 ≤ smoothCutoff t err n) :
    ((centralSmoothOrders p t err n).card : ℝ) =
      ((centralOddParitySmoothOrders p t err n).card : ℝ) +
        halfSmoothCount p t err n := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := centralSmoothOrders p t err n) (p := fun m => m % 2 = 0)
  have hEq : centralOddParitySmoothOrders p t err n =
      (centralSmoothOrders p t err n).filter (fun m => ¬ m % 2 = 0) := by
    unfold centralOddParitySmoothOrders
    apply Finset.filter_congr
    intro m _
    omega
  rw [← hEq] at hsplit
  have heven := centralEvenSmoothOrders_eq_image (p := p) (t := t) (err := err)
    (n := n) hp hy
  have hhalf : ((centralEvenSmoothOrders p t err n).card : ℝ) = halfSmoothCount p t err n := by
    unfold halfSmoothCount
    rw [heven, Finset.card_image_of_injective _ (fun a b h => by omega)]
  have hnat : (centralSmoothOrders p t err n).card =
      (centralEvenSmoothOrders p t err n).card +
        (centralOddParitySmoothOrders p t err n).card := by
    unfold centralEvenSmoothOrders
    omega
  rw [hnat]
  push_cast
  rw [hhalf]
  ring

/-- The halved smooth count never exceeds the central smooth count: the halved
interval is `C₀ / 2`. -/
theorem halfSmoothCount_le_smoothOrderCount {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) (hy : 2 ≤ smoothCutoff t err n) :
    halfSmoothCount p t err n ≤ ((centralSmoothOrders p t err n).card : ℝ) := by
  have hS := centralSmoothOrders_card_eq_oddCentral_add_half (p := p) (t := t) (err := err)
    (n := n) hp hy
  have hnonneg : (0 : ℝ) ≤ ((centralOddParitySmoothOrders p t err n).card : ℝ) := by
    positivity
  linarith

/-- **A sufficient parity-free interval count.**  If the halved-minus-quartered
smooth count dominates `θ |C₀|`, then the odd-half fraction `θ` holds.  No
parity condition survives on the left-hand side. -/
theorem centralOddHalfParity_of_intervalCard {θ : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (hy : ∀ᶠ n in atTop, 2 ≤ smoothCutoff (paperT p) (paperError ε) n)
    (hθ : 0 ≤ θ)
    (h : ∀ᶠ n in atTop,
      θ * ((centralOrderInterval p n).card : ℝ) ≤
        halfSmoothCount p (paperT p) (paperError ε) n -
          quarterSmoothCount p (paperT p) (paperError ε) n) :
    CentralOddHalfParity θ p ε := by
  filter_upwards [h, hy] with n hn hyn
  have hid := centralOddSmoothCount_eq_half_sub_quarter
    (p := p) (t := paperT p) (err := paperError ε) (n := n) (hp n) hyn
  have hcard := centralSmoothOrders_card_le_interval p (paperT p) (paperError ε) n
  rw [hid]
  calc
    θ * ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ)
        ≤ θ * ((centralOrderInterval p n).card : ℝ) :=
          mul_le_mul_of_nonneg_left hcard hθ
    _ ≤ halfSmoothCount p (paperT p) (paperError ε) n -
          quarterSmoothCount p (paperT p) (paperError ε) n := hn

/-- **The sufficient count on the `p^{3/2}` scale.** -/
theorem centralOddHalfParity_of_rpow {θ : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (hy : ∀ᶠ n in atTop, 2 ≤ smoothCutoff (paperT p) (paperError ε) n)
    (hθ : 0 ≤ θ)
    (h : ∀ᶠ n in atTop,
      θ * p n ^ ((3 : ℝ) / 2) ≤
        halfSmoothCount p (paperT p) (paperError ε) n -
          quarterSmoothCount p (paperT p) (paperError ε) n) :
    CentralOddHalfParity θ p ε := by
  refine centralOddHalfParity_of_intervalCard hp hy hθ ?_
  filter_upwards [h] with n hn
  refine (mul_le_mul_of_nonneg_left
    (centralOrderInterval_card_le_three_halves (p := p) (n := n) (hp n)) hθ).trans hn

/-- **Necessary condition: the halved interval must have a `θ` fraction of odd
smooth numbers.**  Since the central smooth orders contain the doubles of *all*
smooth numbers of the halved interval, the target forces
`θ halfSmoothCount ≤ halfOddSmoothCount`. -/
theorem centralOddHalfParity_implies_halfOdd {θ : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (hy : ∀ᶠ n in atTop, 2 ≤ smoothCutoff (paperT p) (paperError ε) n)
    (hθ : 0 ≤ θ) (h : CentralOddHalfParity θ p ε) :
    ∀ᶠ n in atTop,
      θ * halfSmoothCount p (paperT p) (paperError ε) n ≤
        halfOddSmoothCount p (paperT p) (paperError ε) n := by
  filter_upwards [h, hy] with n hn hyn
  rw [centralOddSmoothCount_eq_halfOdd_card (hp n) hyn] at hn
  have hhalf_le := halfSmoothCount_le_smoothOrderCount
    (p := p) (t := paperT p) (err := paperError ε) (n := n) (hp n) hyn
  calc
    θ * halfSmoothCount p (paperT p) (paperError ε) n
        ≤ θ * ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) :=
          mul_le_mul_of_nonneg_left hhalf_le hθ
    _ ≤ halfOddSmoothCount p (paperT p) (paperError ε) n := hn

/-- **The exact parity-free form of the residual.**  Using the partition of the
central smooth orders into the odd part and the double of `C₁`, the target is
equivalent to

```
θ · # {odd smooth in C₀} + # {smooth in C₂} ≤ (1 - θ) · # {smooth in C₁} .
```

Every term is now either a plain smooth count (`C₁`, `C₂`) or the count of odd
smooth numbers in `C₀`; in particular the odd-half residue class `m % 4 = 2` has
disappeared. -/
theorem centralOddHalfParity_iff_oddCentral {θ : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (hy : ∀ᶠ n in atTop, 2 ≤ smoothCutoff (paperT p) (paperError ε) n) :
    CentralOddHalfParity θ p ε ↔
      ∀ᶠ n in atTop,
        θ * ((centralOddParitySmoothOrders p (paperT p) (paperError ε) n).card : ℝ) +
            quarterSmoothCount p (paperT p) (paperError ε) n ≤
          (1 - θ) * halfSmoothCount p (paperT p) (paperError ε) n := by
  rw [centralOddHalfParity_iff_half_sub_quarter hp hy]
  constructor
  · intro h
    filter_upwards [h, hy] with n hn hyn
    have hS := centralSmoothOrders_card_eq_oddCentral_add_half
      (p := p) (t := paperT p) (err := paperError ε) (n := n) (hp n) hyn
    rw [hS] at hn
    nlinarith
  · intro h
    filter_upwards [h, hy] with n hn hyn
    have hS := centralSmoothOrders_card_eq_oddCentral_add_half
      (p := p) (t := paperT p) (err := paperError ε) (n := n) (hp n) hyn
    rw [hS]
    nlinarith

/-! ## 6. The density route produces only a vanishing fraction -/

/-- **The density route.**  Composing the relative short-interval density with
the global odd lower bound yields the parity inequality with the
`n`-dependent fraction `A B exp (-(1+ε) t_p)`:

```
A B exp (-(1+ε) t_p) * |centralSmoothOrders| ≤ centralOddSmoothCount .
```

The fraction is not a fixed constant: at the paper scale it tends to `0`
(§6, `densityFraction_tendsto_zero`). -/
theorem centralOddHalfParity_of_relative_global
    {A B : ℝ} {p : ℕ → ℝ} {ε : ℝ} (hA : 0 ≤ A) (hp : ∀ n, 2 ≤ p n)
    (hrel : ∀ n,
      A * ((centralOrderInterval p n).card : ℝ) *
          (globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2) ≤
        centralOddSmoothCount p (paperT p) (paperError ε) n)
    (hglob : ∀ n,
      B * p n ^ 2 * Real.exp (-(1 + paperError ε n) * paperT p n) ≤
        globalOddSmoothCount p (paperT p) (paperError ε) n) :
    ∀ n,
      A * B * Real.exp (-(1 + ε) * paperT p n) *
          ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
        centralOddSmoothCount p (paperT p) (paperError ε) n := by
  intro n
  have hp_pos : (0 : ℝ) < p n := by linarith [hp n]
  have hp2 : (0 : ℝ) < p n ^ 2 := pow_pos hp_pos 2
  have hcard := centralSmoothOrders_card_le_interval p (paperT p) (paperError ε) n
  have hoff_nonneg : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  have hcount_nonneg : (0 : ℝ) ≤
      centralOddSmoothCount p (paperT p) (paperError ε) n := by
    unfold centralOddSmoothCount
    positivity
  simp only [paperError] at hglob
  by_cases hB : 0 ≤ B
  · -- divide the global bound by `p²`
    have hdiv : B * Real.exp (-(1 + ε) * paperT p n) ≤
        globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2 := by
      rw [le_div_iff₀ hp2]
      nlinarith [hglob n]
    have hstep1 : A * B * Real.exp (-(1 + ε) * paperT p n) *
          ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤
        A * ((centralOrderInterval p n).card : ℝ) *
          (B * Real.exp (-(1 + ε) * paperT p n)) := by
      have hcoef : (0 : ℝ) ≤ A * (B * Real.exp (-(1 + ε) * paperT p n)) := by
        have he : (0 : ℝ) < Real.exp (-(1 + ε) * paperT p n) := Real.exp_pos _
        have := mul_nonneg hA hB
        positivity
      have := mul_le_mul_of_nonneg_left hcard hcoef
      calc
        A * B * Real.exp (-(1 + ε) * paperT p n) *
              ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ)
            = (A * (B * Real.exp (-(1 + ε) * paperT p n))) *
                ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
              ring
        _ ≤ (A * (B * Real.exp (-(1 + ε) * paperT p n))) *
              ((centralOrderInterval p n).card : ℝ) := this
        _ = A * ((centralOrderInterval p n).card : ℝ) *
              (B * Real.exp (-(1 + ε) * paperT p n)) := by ring
    have hstep2 : A * ((centralOrderInterval p n).card : ℝ) *
          (B * Real.exp (-(1 + ε) * paperT p n)) ≤
        A * ((centralOrderInterval p n).card : ℝ) *
          (globalOddSmoothCount p (paperT p) (paperError ε) n / p n ^ 2) :=
      mul_le_mul_of_nonneg_left hdiv (mul_nonneg hA hoff_nonneg)
    exact hstep1.trans (hstep2.trans (hrel n))
  · -- a negative `B` makes the left side nonpositive
    have hBneg : B < 0 := lt_of_not_ge hB
    have hleft : A * B * Real.exp (-(1 + ε) * paperT p n) *
          ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) ≤ 0 := by
      have he : (0 : ℝ) < Real.exp (-(1 + ε) * paperT p n) := Real.exp_pos _
      have hSQ : (0 : ℝ) ≤
          ((centralSmoothOrders p (paperT p) (paperError ε) n).card : ℝ) := by
        positivity
      have hAB : A * B ≤ 0 := by
        simpa only [mul_comm] using mul_nonpos_of_nonpos_of_nonneg hBneg.le hA
      have hABe : A * B * Real.exp (-(1 + ε) * paperT p n) ≤ 0 := by
        simpa only [mul_assoc] using mul_nonpos_of_nonpos_of_nonneg hAB he.le
      exact mul_nonpos_of_nonpos_of_nonneg hABe hSQ
    exact hleft.trans hcount_nonneg

/-- At the paper scale the density-route fraction tends to `0`. -/
theorem densityFraction_tendsto_zero {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : -1 < ε) :
    Tendsto (fun n => Real.exp (-(1 + ε) * paperT p n)) atTop (nhds 0) := by
  have hα : (0 : ℝ) < 1 + ε := by linarith
  have hneg : Tendsto (fun n => (-(1 + ε)) * paperT p n) atTop atBot :=
    (tendsto_paperT_of_growth h).const_mul_atTop_of_neg (by linarith)
  exact Real.tendsto_exp_atBot.comp hneg

/-- **No fixed positive fraction comes from the density route.**  For every
fixed `θ > 0`, the composed fraction `A B exp (-(1+ε) t_p)` is eventually
strictly below `θ`. -/
theorem densityFraction_lt_of_pos {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : -1 < ε) {A B θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n in atTop, A * B * Real.exp (-(1 + ε) * paperT p n) < θ := by
  have htend := (densityFraction_tendsto_zero h hε).const_mul (A * B)
  have h0 : A * B * 0 = 0 := by ring
  rw [h0] at htend
  exact (tendsto_order.mp htend).2 θ hθ

/-! ## 7. A non-vacuous instance on the paper schedule -/

/-- The constant prime scale `p = 13`, which is prime and has `p² = 169`. -/
def thirteenP : ℕ → ℝ := fun _ => 13

/-- The paper scale at `p = 13`. -/
def thirteenT : ℝ := Real.sqrt (Real.log 13 * Real.log (Real.log 13))

/-- The relative error normalising the paper cutoff to `p² = 169`. -/
def thirteenEps : ℝ := Real.log 169 / thirteenT - 1

theorem thirteenT_pos : 0 < thirteenT := by
  unfold thirteenT
  apply Real.sqrt_pos_of_pos
  apply mul_pos
  · exact Real.log_pos (by norm_num)
  · apply Real.log_pos
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by nlinarith [Real.exp_one_lt_three])

theorem thirteenP_paperT (n : ℕ) : paperT thirteenP n = thirteenT := rfl

theorem thirteen_one_add_eps :
    (1 + thirteenEps) * thirteenT = Real.log 169 := by
  unfold thirteenEps
  field_simp [thirteenT_pos.ne']
  ring

theorem thirteen_cutoff (n : ℕ) :
    smoothCutoff (paperT thirteenP) (paperError thirteenEps) n = 169 := by
  unfold smoothCutoff
  simp only [paperError]
  rw [thirteenP_paperT, thirteen_one_add_eps]
  exact Real.exp_log (by norm_num)

/-- For `p ≥ 1` and an all-dominating cutoff, every integer of the central
interval is smooth. -/
theorem centralSmoothOrders_eq_interval_of_cutoff_ge
    {p t err : ℕ → ℝ} {n : ℕ} (hp1 : 1 ≤ p n)
    (hge : p n ^ 2 ≤ smoothCutoff t err n) :
    centralSmoothOrders p t err n = centralOrderInterval p n := by
  ext m
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).1
  · intro hm
    have hm_le : m ≤ ⌊p n ^ 2⌋₊ := (Finset.mem_Icc.mp hm).2
    rw [centralSmoothOrders, Finset.mem_filter]
    refine ⟨hm, ?_⟩
    unfold IsSmoothUpTo
    intro q hq
    have hq_le_m : q ≤ m :=
      Nat.le_of_dvd (pos_of_mem_centralOrderInterval hp1 hm)
        (Nat.dvd_of_mem_primeFactors hq)
    have hm_real : (m : ℝ) ≤ p n ^ 2 :=
      (Nat.cast_le.mpr hm_le).trans (Nat.floor_le (by positivity))
    have hq_real : (q : ℝ) ≤ p n ^ 2 := (Nat.cast_le.mpr hq_le_m).trans hm_real
    exact hq_real.trans hge

/-- `13^{3/2} = 13 √13` lies strictly between `46` and `48`. -/
theorem thirteen_rpow_bounds :
    (46 : ℝ) < (13 : ℝ) ^ ((3 : ℝ) / 2) ∧ (13 : ℝ) ^ ((3 : ℝ) / 2) < 48 := by
  have hsq : Real.sqrt 13 * Real.sqrt 13 = 13 := Real.mul_self_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 13 := Real.sqrt_pos.mpr (by norm_num)
  have hval : (13 : ℝ) ^ ((3 : ℝ) / 2) = 13 * Real.sqrt 13 :=
    rpow_three_halves_eq 13 (by norm_num)
  rw [hval]
  constructor
  · nlinarith [sq_nonneg (13 * Real.sqrt 13 - 46)]
  · nlinarith [sq_nonneg (48 - 13 * Real.sqrt 13)]

/-- The central interval at `p = 13` is the integer interval `[146, 169]`. -/
theorem thirteen_centralInterval (n : ℕ) :
    centralOrderInterval thirteenP n = Finset.Icc 146 169 := by
  unfold centralOrderInterval thirteenP
  rw [show ((13 : ℝ) ^ 2) = 169 by norm_num]
  have hbounds := thirteen_rpow_bounds
  have hceil : ⌈(169 : ℝ) - (13 : ℝ) ^ ((3 : ℝ) / 2) / 2⌉₊ = 146 := by
    apply le_antisymm
    · rw [Nat.ceil_le]
      nlinarith [hbounds.1]
    · have hlt : 145 < ⌈(169 : ℝ) - (13 : ℝ) ^ ((3 : ℝ) / 2) / 2⌉₊ := by
        rw [Nat.lt_ceil]
        push_cast
        nlinarith [hbounds.2]
      omega
  have hfloor : ⌊(169 : ℝ)⌋₊ = 169 := by norm_num
  rw [hceil, hfloor]

/-- The paper schedule at `p = 13` sees the full central interval
`[146, 169]`: the cutoff `169` dominates `p²`. -/
theorem thirteen_smoothOrders (n : ℕ) :
    centralSmoothOrders thirteenP (paperT thirteenP) (paperError thirteenEps) n =
      Finset.Icc 146 169 := by
  rw [centralSmoothOrders_eq_interval_of_cutoff_ge
    (by norm_num [thirteenP] : (1 : ℝ) ≤ thirteenP n)]
  · exact thirteen_centralInterval n
  · rw [thirteen_cutoff]
    norm_num [thirteenP]

theorem thirteen_interval_card :
    ((Finset.Icc 146 169).card : ℝ) = 24 := by
  rw [Nat.card_Icc]
  norm_num

theorem thirteen_oddHalf_card :
    (((Finset.Icc 146 169).filter IsOddHalfOrder).card : ℝ) = 6 := by
  have hset : (Finset.Icc 146 169).filter IsOddHalfOrder =
      ({146, 150, 154, 158, 162, 166} : Finset ℕ) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton, IsOddHalfOrder]
    omega
  have h : ((Finset.Icc 146 169).filter IsOddHalfOrder).card = 6 := by
    rw [hset]
    norm_num
  exact_mod_cast h

/-- **The parity residual holds with `θ = 1/4` at `p = 13`.**  The cutoff equals
`p² = 169`, so `C₀ = [146, 169]` and exactly `6` of its `24` integers are
`≡ 2 (mod 4)`. -/
theorem centralOddHalfParity_thirteen :
    CentralOddHalfParity (1 / 4) thirteenP thirteenEps := by
  refine Filter.Eventually.of_forall (fun n => ?_)
  have hS := thirteen_smoothOrders n
  have hcard : ((centralSmoothOrders thirteenP (paperT thirteenP)
      (paperError thirteenEps) n).card : ℝ) = 24 := by
    rw [hS]
    exact thirteen_interval_card
  have hodd : centralOddSmoothCount thirteenP (paperT thirteenP)
      (paperError thirteenEps) n = 6 := by
    unfold centralOddSmoothCount centralOddSmoothOrders
    rw [hS]
    exact thirteen_oddHalf_card
  rw [hcard, hodd]
  norm_num

/-- **The parity fraction `1/2` is not universal.**  At the constant prime scale
`p = 13` with the all-smooth cutoff `p²`, the odd-half fraction is exactly
`1/4`; hence `CentralOddHalfParity (1/2)` fails there.  Any proof of the paper's
`θ = 1/2` (or `3/8`) must therefore use the sparsity of smooth numbers at the
paper cutoff `Y = p^{o(1)}`: an all-smooth or pure-dilation argument cannot give
more than the generic parity density `1/4`. -/
theorem thirteen_not_half :
    ¬ CentralOddHalfParity (1 / 2) thirteenP thirteenEps := by
  intro h
  have hcard : ∀ n, ((centralSmoothOrders thirteenP (paperT thirteenP)
      (paperError thirteenEps) n).card : ℝ) = 24 := by
    intro n
    rw [thirteen_smoothOrders n]
    exact thirteen_interval_card
  have hodd : ∀ n, centralOddSmoothCount thirteenP (paperT thirteenP)
      (paperError thirteenEps) n = 6 := by
    intro n
    unfold centralOddSmoothCount centralOddSmoothOrders
    rw [thirteen_smoothOrders n]
    exact thirteen_oddHalf_card
  obtain ⟨n, hn⟩ := h.exists
  rw [hcard n, hodd n] at hn
  norm_num at hn

/-! ## Axiom audit -/

#print axioms mem_halfOrderInterval_iff_two_mul
#print axioms mem_quarterOrderInterval_iff_two_mul
#print axioms isSmoothUpTo_two_mul_iff
#print axioms one_le_half_lower
#print axioms quarter_lower_pos
#print axioms two_le_of_mem_centralOrderInterval
#print axioms centralEvenSmoothOrders_eq_image
#print axioms halfEvenSmoothOrders_eq_image
#print axioms centralOddSmoothOrders_eq_image_halfOdd
#print axioms centralOddSmoothCount_eq_halfOdd_card
#print axioms halfSmoothOrders_card_eq_odd_add_even
#print axioms centralOddSmoothCount_eq_half_sub_quarter
#print axioms centralOddHalfParity_iff_half_sub_quarter
#print axioms centralOddHalfParity_iff_halfOdd
#print axioms centralSmoothOrders_card_le_interval
#print axioms centralOddHalfParity_of_intervalCard
#print axioms centralOddHalfParity_of_rpow
#print axioms centralOddHalfParity_implies_halfOdd
#print axioms centralSmoothOrders_card_eq_oddCentral_add_half
#print axioms halfSmoothCount_le_smoothOrderCount
#print axioms centralOddHalfParity_iff_oddCentral
#print axioms pos_of_mem_centralOrderInterval
#print axioms centralOddHalfParity_of_relative_global
#print axioms densityFraction_tendsto_zero
#print axioms densityFraction_lt_of_pos
#print axioms thirteenT_pos
#print axioms thirteen_cutoff
#print axioms centralSmoothOrders_eq_interval_of_cutoff_ge
#print axioms thirteen_rpow_bounds
#print axioms thirteen_centralInterval
#print axioms thirteen_smoothOrders
#print axioms thirteen_oddHalf_card
#print axioms centralOddHalfParity_thirteen
#print axioms thirteen_not_half

end

end Cogentic.RandomizedL30Parity
