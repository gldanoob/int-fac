import Cogentic.RandomizedL21_2PaperLocal

set_option linter.style.haveILetI false

/-!
# L21.2: from a positive prime-bin count to the literal short-interval count

`Cogentic.RandomizedL21_2PaperLocal` isolates the residual local input

```
ShortIntervalSmoothCountLower p c X :
  ∀ᶠ n, √(X n) * exp (-(R n)) ≤ #(shortSmoothInterval (p n) (smoothCutoff c X n)) ,
```

where `shortSmoothInterval p y` is the literal finite set of `y`-smooth
integers in the open interval `(p - √p, p + √p)`.  The existing construction of
`Cogentic.RandomizedSmoothDensity` produces the prime-bin count

```
centeredBinProducts P δ J k a
```

whose every element lies in the *multiplicative* strip

```
P ^ k ≤ x ≤ P ^ k * exp (k δ) .
```

This file performs the exact interval transfer from that strip to the literal
`√p`-window, and hence to `LocalSmoothCountLower` and the L21.2 density bundle.

## 1. The general transfer

`centeredBinProducts_subset_shortSmoothInterval` states that if

```
p - √p < P ^ k        and        P ^ k * exp (k δ) < p + √p
```

and every bin floor is at most the smoothness cutoff, then every bin product is
a member of `shortSmoothInterval p (smoothCutoff c X n)`.  The proof reads the
multiplicative strip `centeredBinProducts_mem_strip` and the smoothness
`centeredBinProducts_smooth` directly off the bin construction, and converts
the strict real inequalities to the `floor`/`ceil` endpoints of
`shortSmoothInterval` with `nat_floor_lt_iff` and `Nat.lt_ceil`.

## 2. Factor-four interval bookkeeping

The middle half of the `√p`-window is the factor-four neighbourhood

```
[p - √p/4, p + √p/4] .
```

`strip_bounds_of_factorFour` proves that a strip lying in this middle half lies
in the full open window.  The quarter-window margin is the L21.2 analogue of the
`p² / 4` bookkeeping of `Cogentic.RandomizedL30SmoothDensity.paperDensityP`: it
keeps the endpoint comparisons away from the exact square-root boundary and
makes the factor-four loss explicit.  We also record the elementary endpoint
bounds `3 p / 4 ≤ p - √p` and `p + √p ≤ 5 p / 4` for `p ≥ 16`.

## 3. Large-cutoff regime and the witness scale

At a cutoff `y ≥ p³` no bin-floor bookkeeping is needed at all: if
`x ≤ P^k exp (k δ) < p + √p`, then every prime factor of `x` is at most `x`,
and `p + √p ≤ p³ ≤ y`.  This is the regime used below.

The concrete witness is

```
p_n = 4^(n+4),      c = 1,      X_n = exp ((n+4)^4) .
```

Writing `U_n = log X_n = (n+4)^4` and
`T_n = √(U_n log U_n)`, one has `T_n ≥ 2 (n+4)^2`, while
`log (p_n³) = 3 (n+4) log 4`; hence `smoothCutoff 1 X n ≥ p_n³` for every band.
The witness therefore has a genuinely positive smoothness cutoff, dominates
every bin floor, and leaves the *only* residual estimate as the positive
prime-bin count at the growing paper cutoff.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or error
is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2ShortIntervalTransfer

open Filter Real
open Cogentic.Randomized
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Density
open Cogentic.RandomizedL21_2LocalCount
open Cogentic.RandomizedL21_2PaperLocal

/-! ## 1. Membership in the literal short interval -/

/-- A single prime-bin product is a member of the literal smooth short
interval, provided the whole multiplicative strip lies in the open `√p`-window
and every bin floor is at most the cutoff. -/
theorem mem_shortSmoothInterval_of_mem_centeredBinProducts
    {P δ y : ℝ} {J k a m : ℕ} {p : ℝ}
    (hp : 1 < p)
    (hm : m ∈ centeredBinProducts P δ J k a)
    (hP : 0 ≤ P) (hk : 0 < k)
    (hlo : p - Real.sqrt p < P ^ k)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) < p + Real.sqrt p)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a k (j + 1) : ℝ) ≤ y) :
    m ∈ shortSmoothInterval p y := by
  have hstrip := centeredBinProducts_mem_strip hP hk hm
  have hlow_nonneg : 0 ≤ p - Real.sqrt p := by
    have h := (Real.sqrt_le_self_iff).mpr (Or.inr hp.le)
    linarith
  have hm_low : p - Real.sqrt p < (m : ℝ) := lt_of_lt_of_le hlo hstrip.1
  have hm_high : (m : ℝ) < p + Real.sqrt p := lt_of_le_of_lt hstrip.2 hhi
  have hsmooth : SmoothUpTo y m := centeredBinProducts_smooth hfloor hm
  rw [mem_shortSmoothInterval]
  exact ⟨(nat_floor_lt_iff hlow_nonneg).mpr hm_low, Nat.lt_ceil.mpr hm_high, hsmooth⟩

/-- The full prime-bin set is contained in the literal smooth short interval. -/
theorem centeredBinProducts_subset_shortSmoothInterval
    {P δ y : ℝ} {J k a : ℕ} {p : ℝ}
    (hp : 1 < p)
    (hP : 0 ≤ P) (hk : 0 < k)
    (hlo : p - Real.sqrt p < P ^ k)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) < p + Real.sqrt p)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a k (j + 1) : ℝ) ≤ y) :
    centeredBinProducts P δ J k a ⊆ shortSmoothInterval p y := by
  intro m hm
  exact mem_shortSmoothInterval_of_mem_centeredBinProducts hp hm hP hk hlo hhi hfloor

/-- A positive prime-bin count bounds the literal short-interval smooth count
from below. -/
theorem card_centeredBinProducts_le_shortSmoothCount
    {P δ y : ℝ} {J k a : ℕ} {p : ℝ}
    (hp : 1 < p)
    (hP : 0 ≤ P) (hk : 0 < k)
    (hlo : p - Real.sqrt p < P ^ k)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) < p + Real.sqrt p)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a k (j + 1) : ℝ) ≤ y) :
    ((centeredBinProducts P δ J k a).card : ℝ) ≤ shortSmoothCount p y := by
  have hsub := centeredBinProducts_subset_shortSmoothInterval hp hP hk hlo hhi hfloor
  unfold shortSmoothCount
  exact_mod_cast Finset.card_le_card hsub

/-! ## 2. Factor-four interval bookkeeping -/

/-- For `p ≥ 16`, `√p ≤ p / 4`. -/
theorem sqrt_le_quarter {p : ℝ} (hp : 16 ≤ p) : Real.sqrt p ≤ p / 4 := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have hsq : p ≤ (p / 4) ^ 2 := by nlinarith [sq_nonneg (p - 16)]
  exact hsq

/-- The lower endpoint of the `√p`-window is at least `3 p / 4` for `p ≥ 16`. -/
theorem three_quarters_le_sub_sqrt {p : ℝ} (hp : 16 ≤ p) :
    3 * p / 4 ≤ p - Real.sqrt p := by
  have h := sqrt_le_quarter hp
  linarith

/-- The upper endpoint of the `√p`-window is at most `5 p / 4` for `p ≥ 16`. -/
theorem add_sqrt_le_five_quarters {p : ℝ} (hp : 16 ≤ p) :
    p + Real.sqrt p ≤ 5 * p / 4 := by
  have h := sqrt_le_quarter hp
  linarith

/-- **Factor-four bookkeeping.**  The middle half of the `√p`-window is
`[p - √p/4, p + √p/4]`; a strip lying there lies in the full open window.  The
quarter-window margin is the factor-four slack that keeps the endpoint
comparisons away from the exact square-root boundary. -/
theorem strip_bounds_of_factorFour
    {p P δ : ℝ} {k : ℕ}
    (hlo : p - Real.sqrt p / 4 < P ^ k)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) < p + Real.sqrt p / 4) :
    p - Real.sqrt p < P ^ k ∧
      P ^ k * Real.exp ((k : ℝ) * δ) < p + Real.sqrt p := by
  have hquarter_le : Real.sqrt p / 4 ≤ Real.sqrt p := by
    have := Real.sqrt_nonneg p
    linarith
  exact ⟨lt_of_le_of_lt (by linarith) hlo,
    lt_of_lt_of_le hhi (by linarith)⟩

/-! ## 3. The general eventual transfer -/

/-- **A positive prime-bin count gives the literal short-interval count.**  At
every band the strip is inside the open `√p`-window, every bin floor is at most
the smoothness cutoff, and the bin count dominates the paper demand.  Then
`ShortIntervalSmoothCountLower` holds. -/
theorem shortIntervalSmoothCountLower_of_binCount
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, p n - Real.sqrt (p n) < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < p n + Real.sqrt (p n))
    (hfloor : ∀ᶠ n : ℕ in atTop, ∀ j < J n,
      (centeredBinFloor (P n) (δ n) (a n) (k n) (j + 1) : ℝ) ≤
        smoothCutoff c X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    ShortIntervalSmoothCountLower p c X := by
  filter_upwards [hp, hlo, hhi, hfloor, hcount] with n hp1 hlon hhin hfloorn hcountn
  exact hcountn.trans
    (card_centeredBinProducts_le_shortSmoothCount (p := p n)
      (y := smoothCutoff c X n) hp1 (hP n) (hk n) hlon hhin hfloorn)

/-- The factor-four form of the general transfer: the strip lies in the middle
half `[p - √p/4, p + √p/4]` of the window. -/
theorem shortIntervalSmoothCountLower_of_binCount_factorFour
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, p n - Real.sqrt (p n) / 4 < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < p n + Real.sqrt (p n) / 4)
    (hfloor : ∀ᶠ n : ℕ in atTop, ∀ j < J n,
      (centeredBinFloor (P n) (δ n) (a n) (k n) (j + 1) : ℝ) ≤
        smoothCutoff c X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    ShortIntervalSmoothCountLower p c X := by
  have hbounds : ∀ᶠ n : ℕ in atTop,
      p n - Real.sqrt (p n) < P n ^ k n ∧
        P n ^ k n * Real.exp ((k n : ℝ) * δ n) < p n + Real.sqrt (p n) := by
    filter_upwards [hlo, hhi] with n h1 h2
    exact strip_bounds_of_factorFour h1 h2
  exact shortIntervalSmoothCountLower_of_binCount hp hP hk
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2) hfloor hcount

/-! ## 4. The large-cutoff regime -/

/-- Every bin product is strictly positive. -/
theorem centeredBinProducts_pos {P δ : ℝ} {J k a : ℕ} {m : ℕ}
    (hm : m ∈ centeredBinProducts P δ J k a) : 0 < m := by
  classical
  unfold centeredBinProducts primeBinPatternProducts at hm
  obtain ⟨s, _hs, hprod⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hprod
  exact Finset.prod_pos fun i _ =>
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hf i)).2.pos

/-- At cutoff `y ≥ p³`, membership in the strip already forces smoothness: the
whole product is below `p + √p`, hence below `p³`. -/
theorem mem_shortSmoothInterval_of_mem_centeredBinProducts_of_largeCutoff
    {P δ y : ℝ} {J k a m : ℕ} {p : ℝ}
    (hp1 : 1 < p) (hp2 : 2 ≤ p)
    (hm : m ∈ centeredBinProducts P δ J k a)
    (hP : 0 ≤ P) (hk : 0 < k)
    (hlo : p - Real.sqrt p < P ^ k)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) < p + Real.sqrt p)
    (hcut : p ^ 3 ≤ y) :
    m ∈ shortSmoothInterval p y := by
  have hstrip := centeredBinProducts_mem_strip hP hk hm
  have hmpos : 0 < m := centeredBinProducts_pos hm
  have hp_pos : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hlow_nonneg : 0 ≤ p - Real.sqrt p := by
    have h := (Real.sqrt_le_self_iff).mpr (Or.inr hp1.le)
    linarith
  have hm_low : p - Real.sqrt p < (m : ℝ) := lt_of_lt_of_le hlo hstrip.1
  have hm_high : (m : ℝ) < p + Real.sqrt p := lt_of_le_of_lt hstrip.2 hhi
  have hsqrt_le_p : Real.sqrt p ≤ p :=
    (Real.sqrt_le_self_iff).mpr (Or.inr (by linarith : (1 : ℝ) ≤ p))
  have hp2sq : (2 : ℝ) ≤ p ^ 2 := by nlinarith [hp2, hp_pos]
  have h2p : 2 * p ≤ p ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hp2sq hp_pos.le
    nlinarith
  have hp3_ge : p + Real.sqrt p ≤ p ^ 3 := by linarith
  have hsmooth : SmoothUpTo y m := by
    intro q hq
    have hq_dvd : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    have hq_le_m : q ≤ m := Nat.le_of_dvd hmpos hq_dvd
    have hq_real : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hq_le_m
    exact hq_real.trans (le_of_lt (lt_of_lt_of_le hm_high (le_trans hp3_ge hcut)))
  rw [mem_shortSmoothInterval]
  exact ⟨(nat_floor_lt_iff hlow_nonneg).mpr hm_low, Nat.lt_ceil.mpr hm_high, hsmooth⟩

/-- The large-cutoff containment statement in subset form. -/
theorem centeredBinProducts_subset_shortSmoothInterval_of_largeCutoff
    {P δ y : ℝ} {J k a : ℕ} {p : ℝ}
    (hp1 : 1 < p) (hp2 : 2 ≤ p)
    (hP : 0 ≤ P) (hk : 0 < k)
    (hlo : p - Real.sqrt p < P ^ k)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) < p + Real.sqrt p)
    (hcut : p ^ 3 ≤ y) :
    centeredBinProducts P δ J k a ⊆ shortSmoothInterval p y := by
  intro m hm
  exact mem_shortSmoothInterval_of_mem_centeredBinProducts_of_largeCutoff
    hp1 hp2 hm hP hk hlo hhi hcut

/-- A positive prime-bin count bounds the short-interval smooth count from
below at cutoff `y ≥ p³`. -/
theorem card_centeredBinProducts_le_shortSmoothCount_of_largeCutoff
    {P δ y : ℝ} {J k a : ℕ} {p : ℝ}
    (hp1 : 1 < p) (hp2 : 2 ≤ p)
    (hP : 0 ≤ P) (hk : 0 < k)
    (hlo : p - Real.sqrt p < P ^ k)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) < p + Real.sqrt p)
    (hcut : p ^ 3 ≤ y) :
    ((centeredBinProducts P δ J k a).card : ℝ) ≤ shortSmoothCount p y := by
  have hsub := centeredBinProducts_subset_shortSmoothInterval_of_largeCutoff
    (P := P) (δ := δ) (y := y) (J := J) (k := k) (a := a) (p := p)
    hp1 hp2 hP hk hlo hhi hcut
  unfold shortSmoothCount
  exact_mod_cast Finset.card_le_card hsub

/-- **The large-cutoff eventual transfer.**  If the bin strip lies in the
`√p`-window and the cutoff dominates `p³`, then a positive bin count gives
`ShortIntervalSmoothCountLower`.  No bin-floor hypothesis remains. -/
theorem shortIntervalSmoothCountLower_of_binCount_largeCutoff
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp2 : ∀ᶠ n : ℕ in atTop, 2 ≤ p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, p n - Real.sqrt (p n) < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < p n + Real.sqrt (p n))
    (hcut : ∀ᶠ n : ℕ in atTop, p n ^ 3 ≤ smoothCutoff c X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    ShortIntervalSmoothCountLower p c X := by
  filter_upwards [hp2, hlo, hhi, hcut, hcount] with n hp2n hlon hhin hcutn hcountn
  have hp1 : 1 < p n := by linarith
  exact hcountn.trans
    (card_centeredBinProducts_le_shortSmoothCount_of_largeCutoff
      hp1 hp2n (hP n) (hk n) hlon hhin hcutn)

/-- The factor-four form of the large-cutoff transfer. -/
theorem shortIntervalSmoothCountLower_of_binCount_largeCutoff_factorFour
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp2 : ∀ᶠ n : ℕ in atTop, 2 ≤ p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, p n - Real.sqrt (p n) / 4 < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < p n + Real.sqrt (p n) / 4)
    (hcut : ∀ᶠ n : ℕ in atTop, p n ^ 3 ≤ smoothCutoff c X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    ShortIntervalSmoothCountLower p c X := by
  have hbounds : ∀ᶠ n : ℕ in atTop,
      p n - Real.sqrt (p n) < P n ^ k n ∧
        P n ^ k n * Real.exp ((k n : ℝ) * δ n) < p n + Real.sqrt (p n) := by
    filter_upwards [hlo, hhi] with n h1 h2
    exact strip_bounds_of_factorFour h1 h2
  exact shortIntervalSmoothCountLower_of_binCount_largeCutoff
    hp2 hP hk (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2) hcut hcount

/-- **`LocalSmoothCountLower` from the general bin count.**  This is the
arbitrary-cutoff form, with the bin-floor domination kept explicit. -/
theorem localSmoothCountLower_of_binCount
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, p n - Real.sqrt (p n) < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < p n + Real.sqrt (p n))
    (hfloor : ∀ᶠ n : ℕ in atTop, ∀ j < J n,
      (centeredBinFloor (P n) (δ n) (a n) (k n) (j + 1) : ℝ) ≤
        smoothCutoff c X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    LocalSmoothCountLower p c X :=
  localSmoothCountLower_of_shortInterval hp
    (shortIntervalSmoothCountLower_of_binCount hp hP hk hlo hhi hfloor hcount)

/-- **`LocalSmoothCountLower` from the large-cutoff bin count.** -/
theorem localSmoothCountLower_of_binCount_largeCutoff
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp2 : ∀ᶠ n : ℕ in atTop, 2 ≤ p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, p n - Real.sqrt (p n) < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < p n + Real.sqrt (p n))
    (hcut : ∀ᶠ n : ℕ in atTop, p n ^ 3 ≤ smoothCutoff c X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    LocalSmoothCountLower p c X :=
  localSmoothCountLower_of_shortInterval
    (hp2.mono fun _ hn => by linarith)
    (shortIntervalSmoothCountLower_of_binCount_largeCutoff
      hp2 hP hk hlo hhi hcut hcount)

/-! ## 5. Positivity of the transferred counts -/

/-- The paper demand is positive whenever `X > 0`. -/
theorem demand_pos {c : ℝ} {X : ℕ → ℝ} {n : ℕ} (hX : 0 < X n) :
    0 < Real.sqrt (X n) * Real.exp (-(repLog c X n)) :=
  mul_pos (Real.sqrt_pos.mpr hX) (Real.exp_pos _)

/-- A lower bound by the positive demand makes the bin count positive. -/
theorem binCount_pos_of_demand_le
    {P δ : ℝ} {J k a : ℕ} {c : ℝ} {X : ℕ → ℝ} {n : ℕ}
    (hX : 0 < X n)
    (hcount : Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
      ((centeredBinProducts P δ J k a).card : ℝ)) :
    0 < ((centeredBinProducts P δ J k a).card : ℝ) :=
  lt_of_lt_of_le (demand_pos (c := c) hX) hcount

/-- A bin count dominating the positive demand also makes the literal
short-interval count strictly positive. -/
theorem shortSmoothCount_pos_of_demand_le_of_subset
    {p y : ℝ} {S : Finset ℕ} {c : ℝ} {X : ℕ → ℝ} {n : ℕ}
    (hX : 0 < X n)
    (hsub : S ⊆ shortSmoothInterval p y)
    (hcount : Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤ (S.card : ℝ)) :
    0 < shortSmoothCount p y := by
  have hcard : ((S.card : ℝ)) ≤ shortSmoothCount p y := by
    unfold shortSmoothCount
    exact_mod_cast Finset.card_le_card hsub
  exact lt_of_lt_of_le (demand_pos (c := c) hX) (hcount.trans hcard)

/-! ## 6. The concrete witness with a large cutoff -/

/-- The witness centre `p_n = 4^(n+4)`.  Its square root is the integer
`2^(n+4)`, which keeps the interval endpoints exact. -/
def largeCutoffP (n : ℕ) : ℝ := (4 : ℝ) ^ (n + 4)

/-- The witness dyadic bound `X_n = exp ((n+4)^4)`.  The fourth power makes
`log X_n` grow polynomially, so the paper cutoff `exp (c √(U log U))` grows
faster than every fixed power of `p_n`. -/
def largeCutoffX (n : ℕ) : ℝ := Real.exp (((n : ℝ) + 4) ^ 4)

/-- The witness stage-one constant `c = 1`. -/
def largeCutoffC : ℝ := 1

@[simp] theorem largeCutoffC_eq : largeCutoffC = 1 := rfl

theorem largeCutoffP_pos (n : ℕ) : 0 < largeCutoffP n := by
  unfold largeCutoffP
  positivity

theorem largeCutoffP_ge_two (n : ℕ) : 2 ≤ largeCutoffP n := by
  unfold largeCutoffP
  have h : (4 : ℝ) ^ 1 ≤ (4 : ℝ) ^ (n + 4) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at h ⊢
  linarith

theorem largeCutoffP_ge_sixteen (n : ℕ) : 16 ≤ largeCutoffP n := by
  unfold largeCutoffP
  have h : (4 : ℝ) ^ 2 ≤ (4 : ℝ) ^ (n + 4) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at h ⊢
  exact h

/-- The exact square root at the witness centre. -/
theorem largeCutoffP_sqrt (n : ℕ) :
    Real.sqrt (largeCutoffP n) = (2 : ℝ) ^ (n + 4) := by
  unfold largeCutoffP
  have hsq : (4 : ℝ) ^ (n + 4) = ((2 : ℝ) ^ (n + 4)) ^ 2 := by
    calc
      (4 : ℝ) ^ (n + 4) = ((2 : ℝ) ^ 2) ^ (n + 4) := by norm_num
      _ = (2 : ℝ) ^ (2 * (n + 4)) := by rw [pow_mul]
      _ = (2 : ℝ) ^ ((n + 4) * 2) := by rw [mul_comm]
      _ = ((2 : ℝ) ^ (n + 4)) ^ 2 := by rw [pow_mul]
  rw [hsq, Real.sqrt_sq (by positivity)]

theorem largeCutoffX_pos (n : ℕ) : 0 < largeCutoffX n := by
  unfold largeCutoffX
  exact Real.exp_pos _

theorem largeCutoffX_gt_one (n : ℕ) : 1 < largeCutoffX n := by
  unfold largeCutoffX
  rw [Real.one_lt_exp_iff]
  positivity

/-- `log X_n = (n+4)^4`. -/
theorem bandLog_largeCutoffX (n : ℕ) :
    bandLog largeCutoffX n = ((n : ℝ) + 4) ^ 4 := by
  unfold bandLog largeCutoffX
  rw [Real.log_exp]

/-- At the witness scale, `T_X = √(U log U) ≥ 2 (n+4)^2`. -/
theorem paperRate_largeCutoffX_ge (n : ℕ) :
    2 * (((n : ℝ) + 4) ^ 2) ≤ paperRate largeCutoffX n := by
  unfold paperRate
  rw [bandLog_largeCutoffX]
  set a : ℝ := (n : ℝ) + 4 with ha
  have ha4 : (4 : ℝ) ≤ a := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    dsimp only [a]
    linarith
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hlog4_ge_one : (1 : ℝ) ≤ Real.log 4 := by
    have hexp : Real.exp 1 ≤ (4 : ℝ) := by
      have h := Real.exp_one_lt_three
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hloga_ge_one : (1 : ℝ) ≤ Real.log a := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) ha4
    linarith
  have hlog4 : Real.log (a ^ 4) = 4 * Real.log a := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog4]
  have hsq : (2 * a ^ 2) ^ 2 ≤ a ^ 4 * (4 * Real.log a) := by
    have hpow : (0 : ℝ) ≤ a ^ 4 := pow_nonneg ha0 4
    have hlog : (4 : ℝ) ≤ 4 * Real.log a := by nlinarith
    nlinarith
  exact Real.le_sqrt_of_sq_le hsq

/-- The witness cutoff dominates `p³` at every band. -/
theorem largeCutoffX_cutoff_ge_cube (n : ℕ) :
    largeCutoffP n ^ 3 ≤ smoothCutoff largeCutoffC largeCutoffX n := by
  unfold smoothCutoff logCutoff
  rw [largeCutoffC_eq, one_mul]
  have hT := paperRate_largeCutoffX_ge n
  have hp3log : Real.log (largeCutoffP n ^ 3) =
      3 * ((n : ℝ) + 4) * Real.log 4 := by
    unfold largeCutoffP
    rw [Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog4_le_two : Real.log 4 ≤ 2 := by
    have hlog2_le_one : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have ha4 : (4 : ℝ) ≤ (n : ℝ) + 4 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hTge : 3 * ((n : ℝ) + 4) * Real.log 4 ≤ paperRate largeCutoffX n := by
    have h1 : 3 * ((n : ℝ) + 4) * Real.log 4 ≤ 3 * ((n : ℝ) + 4) * 2 := by
      have hcoef : (0 : ℝ) ≤ 3 * ((n : ℝ) + 4) := by positivity
      nlinarith
    have h2 : 3 * ((n : ℝ) + 4) * 2 ≤ 2 * (((n : ℝ) + 4) ^ 2) := by
      nlinarith [ha4]
    linarith
  have hlog_le : Real.log (largeCutoffP n ^ 3) ≤ paperRate largeCutoffX n := by
    rw [hp3log]
    exact hTge
  exact (Real.log_le_iff_le_exp (pow_pos (largeCutoffP_pos n) 3)).mp hlog_le

/-- **The witness transfer with a large cutoff.**  The interval bookkeeping is
reduced to the factor-four bounds, the cutoff domination is proved
unconditionally (`largeCutoffX_cutoff_ge_cube`), and the only remaining
hypothesis is the positive prime-bin count at the growing cutoff. -/
theorem largeCutoff_shortIntervalSmoothCountLower
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop,
      largeCutoffP n - Real.sqrt (largeCutoffP n) / 4 < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) <
        largeCutoffP n + Real.sqrt (largeCutoffP n) / 4)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (largeCutoffX n) * Real.exp (-(repLog largeCutoffC largeCutoffX n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    ShortIntervalSmoothCountLower largeCutoffP largeCutoffC largeCutoffX :=
  shortIntervalSmoothCountLower_of_binCount_largeCutoff_factorFour
    (p := largeCutoffP) (c := largeCutoffC) (X := largeCutoffX)
    (P := P) (δ := δ) (J := J) (k := k) (a := a)
    (Eventually.of_forall largeCutoffP_ge_two)
    hP hk hlo hhi
    (Eventually.of_forall largeCutoffX_cutoff_ge_cube)
    hcount

/-- The witness scale gives `LocalSmoothCountLower` from the bin count. -/
theorem largeCutoff_localSmoothCountLower
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop,
      largeCutoffP n - Real.sqrt (largeCutoffP n) / 4 < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) <
        largeCutoffP n + Real.sqrt (largeCutoffP n) / 4)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (largeCutoffX n) * Real.exp (-(repLog largeCutoffC largeCutoffX n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    LocalSmoothCountLower largeCutoffP largeCutoffC largeCutoffX :=
  localSmoothCountLower_of_shortInterval
    (Eventually.of_forall fun n => by linarith [largeCutoffP_ge_two n])
    (largeCutoff_shortIntervalSmoothCountLower hP hk hlo hhi hcount)

/-- The witness bin count is eventually strictly positive. -/
theorem largeCutoff_binCount_pos
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (largeCutoffX n) * Real.exp (-(repLog largeCutoffC largeCutoffX n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      0 < ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ) := by
  filter_upwards [hcount] with n hn
  exact binCount_pos_of_demand_le (largeCutoffX_pos n) hn

/-- The witness short-interval smooth count is eventually strictly positive. -/
theorem largeCutoff_shortSmoothCount_pos
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop,
      largeCutoffP n - Real.sqrt (largeCutoffP n) / 4 < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) <
        largeCutoffP n + Real.sqrt (largeCutoffP n) / 4)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (largeCutoffX n) * Real.exp (-(repLog largeCutoffC largeCutoffX n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      0 < shortSmoothCount (largeCutoffP n)
        (smoothCutoff largeCutoffC largeCutoffX n) := by
  filter_upwards
    [largeCutoff_shortIntervalSmoothCountLower hP hk hlo hhi hcount] with n hn
  exact lt_of_lt_of_le (demand_pos (c := largeCutoffC) (largeCutoffX_pos n)) hn

end Cogentic.RandomizedL21_2ShortIntervalTransfer

/-! ## 7. The L21.2 density bundle from the bin count -/

namespace Cogentic.RandomizedL21_2Density

open Filter Real
open Cogentic.Randomized
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2Density
open Cogentic.RandomizedL21_2LocalCount
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2ShortIntervalTransfer
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-- **The L21.2 density bundle with the local count supplied by a positive
prime-bin count.**  Every other field of `D` is inherited; `localCount` is
replaced by the short-interval transfer. -/
def L21_2DensityInputs.ofBinCountLargeCutoff (D : L21_2DensityInputs)
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp2 : ∀ᶠ n : ℕ in atTop, 2 ≤ D.p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, D.p n - Real.sqrt (D.p n) < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < D.p n + Real.sqrt (D.p n))
    (hcut : ∀ᶠ n : ℕ in atTop, D.p n ^ 3 ≤ smoothCutoff D.c D.X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (D.X n) * Real.exp (-(repLog D.c D.X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    L21_2DensityInputs :=
  { D with
    localCount := localSmoothCountLower_of_binCount_largeCutoff
      (p := D.p) (c := D.c) (X := D.X)
      hp2 hP hk hlo hhi hcut hcount }

/-- The Perron bundle obtained from the bin count. -/
def L21_2DensityInputs.toPerronInputsOfBinCountLargeCutoff (D : L21_2DensityInputs)
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp2 : ∀ᶠ n : ℕ in atTop, 2 ≤ D.p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, D.p n - Real.sqrt (D.p n) < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < D.p n + Real.sqrt (D.p n))
    (hcut : ∀ᶠ n : ℕ in atTop, D.p n ^ 3 ≤ smoothCutoff D.c D.X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (D.X n) * Real.exp (-(repLog D.c D.X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ)) :
    L21_2PerronInputs :=
  (D.ofBinCountLargeCutoff hp2 hP hk hlo hhi hcut hcount).toPerronInputs

/-- **Paper assumptions from the bin count.**  The remaining eleven leaves plus
the explicit L21.2 density data with `localCount` supplied by the prime-bin
count give the full paper assumptions. -/
def L21_2DensityInputs.paperAssumptions_of_binCountLargeCutoff
    (D : L21_2DensityInputs)
    {P δ : ℕ → ℝ} {J k a : ℕ → ℕ}
    (hp2 : ∀ᶠ n : ℕ in atTop, 2 ≤ D.p n)
    (hP : ∀ n, 0 ≤ P n) (hk : ∀ n, 0 < k n)
    (hlo : ∀ᶠ n : ℕ in atTop, D.p n - Real.sqrt (D.p n) < P n ^ k n)
    (hhi : ∀ᶠ n : ℕ in atTop,
      P n ^ k n * Real.exp ((k n : ℝ) * δ n) < D.p n + Real.sqrt (D.p n))
    (hcut : ∀ᶠ n : ℕ in atTop, D.p n ^ 3 ≤ smoothCutoff D.c D.X n)
    (hcount : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (D.X n) * Real.exp (-(repLog D.c D.X n)) ≤
        ((centeredBinProducts (P n) (δ n) (J n) (k n) (a n)).card : ℝ))
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (A : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2DensityInputs.paperAssumptions_of_density
    (D.ofBinCountLargeCutoff hp2 hP hk hlo hhi hcut hcount) A

end Cogentic.RandomizedL21_2Density

/-! ## Axiom audit -/

namespace Cogentic.RandomizedL21_2ShortIntervalTransfer

#print axioms mem_shortSmoothInterval_of_mem_centeredBinProducts
#print axioms centeredBinProducts_subset_shortSmoothInterval
#print axioms card_centeredBinProducts_le_shortSmoothCount
#print axioms sqrt_le_quarter
#print axioms three_quarters_le_sub_sqrt
#print axioms add_sqrt_le_five_quarters
#print axioms strip_bounds_of_factorFour
#print axioms shortIntervalSmoothCountLower_of_binCount
#print axioms shortIntervalSmoothCountLower_of_binCount_factorFour
#print axioms centeredBinProducts_pos
#print axioms mem_shortSmoothInterval_of_mem_centeredBinProducts_of_largeCutoff
#print axioms centeredBinProducts_subset_shortSmoothInterval_of_largeCutoff
#print axioms card_centeredBinProducts_le_shortSmoothCount_of_largeCutoff
#print axioms shortIntervalSmoothCountLower_of_binCount_largeCutoff
#print axioms shortIntervalSmoothCountLower_of_binCount_largeCutoff_factorFour
#print axioms localSmoothCountLower_of_binCount
#print axioms localSmoothCountLower_of_binCount_largeCutoff
#print axioms demand_pos
#print axioms binCount_pos_of_demand_le
#print axioms shortSmoothCount_pos_of_demand_le_of_subset
#print axioms largeCutoffP_sqrt
#print axioms paperRate_largeCutoffX_ge
#print axioms largeCutoffX_cutoff_ge_cube
#print axioms largeCutoff_shortIntervalSmoothCountLower
#print axioms largeCutoff_localSmoothCountLower
#print axioms largeCutoff_binCount_pos
#print axioms largeCutoff_shortSmoothCount_pos

end Cogentic.RandomizedL21_2ShortIntervalTransfer

#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.ofBinCountLargeCutoff
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toPerronInputsOfBinCountLargeCutoff
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.paperAssumptions_of_binCountLargeCutoff


