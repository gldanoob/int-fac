import Cogentic.RandomizedL30BuchstabProof
import Cogentic.RandomizedL30CentralCount

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# L30: the positive-proportion sub-interval Buchstab reduction

`Cogentic.RandomizedL30BuchstabProof` isolated the large-prime Buchstab
short-interval lower bound

```
BuchstabLargePrimeShortIntervalLower c p ε
```

and observed that it is already implied by the *sub-interval* statement
`BuchstabLargePrimeSubIntervalLower η c p ε`, which only asks for the pairs
`a P` lying in the top `η`-fraction

```
(p² - η p^{3/2}, p²]
```

of the central Hasse interval.  The present file makes that reduction exact and
identifies the shortest remaining smooth-number input.

## What is proved

* `centralSmoothOrders_window_card_eq_large_add_small`: the **windowed**
  Buchstab split.  For every threshold `T` and every `p ≥ 2`, the `y`-smooth
  central orders above `T` are *exactly* the large-prime pairs above `T` plus
  the small-prime pairs above `T`.  The proof uses the one-prime bijection
  `(P, a) ↦ aP` of `RandomizedL30Dickman` and the fact that a filtered image of
  an injective map has the cardinality of the filtered domain.

* `buchstabSmallPrimePairs_window_card_le_sqrtSmooth`: the small-prime part in
  any window is bounded by the `√y`-smooth central orders in that same window.

* `card_largePrimePairs_window_eq_largePrimeSmoothWindow`: an **exact
  characterization**.  The large-prime Buchstab pairs above `T` are in
  bijection with the `y`-smooth central orders above `T` that have a prime
  factor larger than `√y`.  Consequently
  `buchstabLargePrimeSubIntervalLower_iff_largePrimeSmoothWindowLower` states
  the sub-interval bound as a purely smooth-number lower bound, with no
  prime-pair bookkeeping left.

* `buchstabLargePrimeSubIntervalLower_of_window`: an explicit transfer.  A
  lower bound `C p^{3/2} ρ(u)` for the *total* `y`-smooth central orders in the
  top window, together with an upper bound `D p^{3/2} ρ(u)` for the
  `√y`-smooth ones (`c + D ≤ C`), gives the positive-proportion sub-interval
  lower bound with constant `c`.  Composing with
  `buchstabLargePrimeShortIntervalLower_of_subInterval` gives the full target.

* `windowSmoothLower_of_subInterval`: conversely, the sub-interval bound
  implies the total-window lower bound, so the window lower bound is a
  necessary residual rather than an extra assumption.

* `buchstabLargePrimeSubIntervalLower_mono_eta`: enlarging the sub-interval
  (increasing `η`) preserves a lower bound with the same constant.

* `buchstabLargePrimeSubIntervalLower_of_shortInterval_large_eta` and
  `buchstabLargePrimeSubIntervalLower_iff_shortInterval_large_eta`: for
  `η > 1/2` the top window already contains the whole central interval, so the
  sub-interval statement is *equivalent* to the full large-prime statement.
  Combined with the forward implication, every sub-interval statement for any
  `η > 0` implies the target, while for `η ≤ 1/2` it is strictly stronger.

* `buchstabLargePrimeSubIntervalLower_smallWitness`: the sub-interval
  predicate is inhabited at `p = 9`, `η = 1/2`, `c = 1/27` by the pair
  `(71, 1)`.

## What is *not* proved, and why

The sub-interval statement is **not** proved here and is not assumed anywhere.
The file records the structural obstruction to the obvious construction.
Under the paper growth hypothesis the cutoff satisfies `y < √p`, and then every
large-prime Buchstab pair obeys

```
a > p^{3/2} / 2.
```

Indeed `a P ≥ p² - p^{3/2}/2` and `P ≤ y < √p`.  Hence the cofactor is forced
to be huge (`a → ∞`), and `eventually_cofactor_gt` shows that for every fixed
`A` there is eventually no pair with cofactor `≤ A`.  In particular `a = 1` —
`P` a prime near `p²` — gives no pair at all eventually.

Consequently the naive "primes in an interval of length `x^{1/2+δ}`" input at
the scale `x = p²` does not address this problem: such primes exceed the
Buchstab cutoff `P ≤ y`.  The genuine missing input is a short-interval lower
bound for *smooth cofactors* `a` in the windows
`((p² - η p^{3/2})/P, p²/P]`, `P ≤ y`; equivalently the total-window smooth
lower bound together with the windowed `√y`-smooth upper bound above.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or mass is
set to zero.
-/

namespace Cogentic.RandomizedL30BuchstabSubInterval

open Filter Real
open scoped Classical BigOperators
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30CentralCount
open Cogentic.RandomizedL30Dickman
open Cogentic.RandomizedL30RankinEuler
open Cogentic.RandomizedL30BuchstabProof
open Cogentic.Randomized

noncomputable section

/-! ## 1. The windowed Buchstab split -/

/-- The one-prime Buchstab image is exactly the set of `y`-smooth central
orders.  This is the set form of `buchstabOnePairs_card_eq_smoothCount`. -/
theorem buchstabOnePairs_image_eq_centralSmoothOrders
    {p t err : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) :
    (buchstabOnePairs p t err n).image (fun q : ℕ × ℕ => q.2 * q.1) =
      centralSmoothOrders p t err n :=
  Finset.Subset.antisymm buchstabOnePairs_image_subset
    (centralSmoothOrders_subset_buchstabImage hp)

/-- **Windowed Buchstab split.**  For every threshold `T`, the central
`y`-smooth orders strictly above `T` are exactly the large-prime pairs above
`T` plus the small-prime pairs above `T`. -/
theorem centralSmoothOrders_window_card_eq_large_add_small
    {p t err : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) (T : ℝ) :
    (((centralSmoothOrders p t err n).filter (fun m : ℕ => T < (m : ℝ))).card : ℝ) =
      (((buchstabLargePrimePairs p t err n).filter
          (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) +
        (((buchstabSmallPrimePairs p t err n).filter
          (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) := by
  classical
  have hset := buchstabOnePairs_image_eq_centralSmoothOrders
    (p := p) (t := t) (err := err) (n := n) hp
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.2 * q.1)
      ↑((buchstabOnePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))) := by
    intro x hx y hy hxy
    have hx' : x ∈ (buchstabOnePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by simpa using hx
    have hy' : y ∈ (buchstabOnePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by simpa using hy
    exact buchstabOnePairs_injOn
      (Finset.mem_of_mem_filter x hx')
      (Finset.mem_of_mem_filter y hy') hxy
  have hcard : ((centralSmoothOrders p t err n).filter
        (fun m : ℕ => T < (m : ℝ))).card =
      ((buchstabOnePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card := by
    calc
      ((centralSmoothOrders p t err n).filter
          (fun m : ℕ => T < (m : ℝ))).card =
          (((buchstabOnePairs p t err n).filter
            (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).image
              (fun q : ℕ × ℕ => q.2 * q.1)).card := by
            rw [← hset, Finset.filter_image]
            simp only [Nat.cast_mul]
      _ = ((buchstabOnePairs p t err n).filter
            (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card :=
          Finset.card_image_of_injOn hinj
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (buchstabOnePairs p t err n).filter
      (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)))
    (p := fun q : ℕ × ℕ => Real.sqrt (smoothCutoff t err n) < (q.1 : ℝ))
  have hL : ((buchstabOnePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).filter
        (fun q : ℕ × ℕ => Real.sqrt (smoothCutoff t err n) < (q.1 : ℝ)) =
      (buchstabLargePrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by
    rw [buchstabLargePrimePairs]
    ext q
    simp only [Finset.mem_filter]
    tauto
  have hSm : ((buchstabOnePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).filter
        (fun q : ℕ × ℕ => ¬ Real.sqrt (smoothCutoff t err n) < (q.1 : ℝ)) =
      (buchstabSmallPrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by
    rw [buchstabSmallPrimePairs]
    ext q
    simp only [Finset.mem_filter]
    tauto
  rw [hL, hSm] at hsplit
  have hmain : ((centralSmoothOrders p t err n).filter
        (fun m : ℕ => T < (m : ℝ))).card =
      ((buchstabLargePrimePairs p t err n).filter
          (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card +
        ((buchstabSmallPrimePairs p t err n).filter
          (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card := by
    rw [hcard]
    exact hsplit.symm
  exact_mod_cast hmain

/-! ## 2. The small-prime part in a window -/

/-- The small-prime pairs above a threshold land in the `√y`-smooth central
orders above that threshold. -/
theorem buchstabSmallPrimePairs_window_image_subset
    {p t err : ℕ → ℝ} {n : ℕ} (T : ℝ) :
    ((buchstabSmallPrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).image
        (fun q : ℕ × ℕ => q.2 * q.1) ⊆
      (((centralOrderInterval p n).filter (fun m : ℕ => T < (m : ℝ))).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))) := by
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨q, hq, rfl⟩ := hm
  rw [Finset.mem_filter] at hq
  obtain ⟨hqsmall, hqT⟩ := hq
  have himg := buchstabSmallPrimePairs_image_subset
    (p := p) (t := t) (err := err) (n := n)
    (Finset.mem_image.mpr ⟨q, hqsmall, rfl⟩)
  rw [Finset.mem_filter] at himg
  have hqT' : T < ((q.2 * q.1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact hqT
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨himg.1, hqT'⟩, himg.2⟩

/-- The small-prime window count is bounded by the `√y`-smooth central count in
the same window. -/
theorem buchstabSmallPrimePairs_window_card_le_sqrtSmooth
    {p t err : ℕ → ℝ} {n : ℕ} (T : ℝ) :
    (((buchstabSmallPrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) ≤
      ((((centralOrderInterval p n).filter (fun m : ℕ => T < (m : ℝ))).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff t err n)))).card : ℝ) := by
  classical
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.2 * q.1)
      ↑((buchstabSmallPrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))) := by
    intro x hx y hy hxy
    have hxw : x ∈ (buchstabSmallPrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by simpa using hx
    have hyw : y ∈ (buchstabSmallPrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by simpa using hy
    have hx' : x ∈ buchstabSmallPrimePairs p t err n :=
      Finset.mem_of_mem_filter x hxw
    have hy' : y ∈ buchstabSmallPrimePairs p t err n :=
      Finset.mem_of_mem_filter y hyw
    exact buchstabOnePairs_injOn
      (Finset.mem_filter.mp hx').1 (Finset.mem_filter.mp hy').1 hxy
  have hcard := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card
    (buchstabSmallPrimePairs_window_image_subset
      (p := p) (t := t) (err := err) (n := n) T)
  calc
    (((buchstabSmallPrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) =
        ((((buchstabSmallPrimePairs p t err n).filter
          (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).image
            (fun q : ℕ × ℕ => q.2 * q.1)).card : ℝ) := by
          rw [← hcard]
    _ ≤ _ := by exact_mod_cast hle

/-! ## 3. Exact characterization by smooth orders with a large prime factor -/

/-- The `y`-smooth central orders above `T` having at least one prime factor
strictly larger than `√y`.  This is the smooth-number form of the large-prime
Buchstab window. -/
def LargePrimeSmoothWindow (p t err : ℕ → ℝ) (n : ℕ) (T : ℝ) : Finset ℕ :=
  ((centralSmoothOrders p t err n).filter (fun m : ℕ => T < (m : ℝ))).filter
    (fun m : ℕ => ∃ P ∈ m.primeFactors,
      Real.sqrt (smoothCutoff t err n) < (P : ℝ))

/-- **The large-prime Buchstab window is exactly the smooth window with a large
prime factor.**  The product map `(P, a) ↦ aP` is injective on the Buchstab
pairs and its image is precisely the set of `y`-smooth central orders above `T`
which have a prime factor larger than `√y`. -/
theorem card_largePrimePairs_window_eq_largePrimeSmoothWindow
    {p t err : ℕ → ℝ} {n : ℕ} (hp : 2 ≤ p n) (T : ℝ) :
    (((buchstabLargePrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) =
      ((LargePrimeSmoothWindow p t err n T).card : ℝ) := by
  classical
  let LW := (buchstabLargePrimePairs p t err n).filter
    (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.2 * q.1) ↑LW := by
    intro x hx y hy hxy
    have hxw : x ∈ (buchstabLargePrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by simpa [LW] using hx
    have hyw : y ∈ (buchstabLargePrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by simpa [LW] using hy
    have hx' : x ∈ buchstabLargePrimePairs p t err n :=
      Finset.mem_of_mem_filter x hxw
    have hy' : y ∈ buchstabLargePrimePairs p t err n :=
      Finset.mem_of_mem_filter y hyw
    exact buchstabOnePairs_injOn
      (buchstabLargePrimePairs_subset hx')
      (buchstabLargePrimePairs_subset hy') hxy
  have himg : LW.image (fun q : ℕ × ℕ => q.2 * q.1) =
      LargePrimeSmoothWindow p t err n T := by
    ext m
    constructor
    · intro hm
      rw [Finset.mem_image] at hm
      obtain ⟨q, hq, rfl⟩ := hm
      have hq' : q ∈ (buchstabLargePrimePairs p t err n).filter
          (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ)) := by simpa [LW] using hq
      rw [Finset.mem_filter] at hq'
      obtain ⟨hqlarge, hqT⟩ := hq'
      have hqone : q ∈ buchstabOnePairs p t err n :=
        buchstabLargePrimePairs_subset hqlarge
      obtain ⟨hPmem, hPprime, hamem, _hsmooth, _hI⟩ :=
        mem_buchstabOnePairs.mp hqone
      have ha_ne : q.2 ≠ 0 := by
        have := (Finset.mem_Icc.mp hamem).1
        omega
      have hprod_ne : q.2 * q.1 ≠ 0 :=
        Nat.mul_ne_zero ha_ne hPprime.ne_zero
      have hPbig : Real.sqrt (smoothCutoff t err n) < (q.1 : ℝ) :=
        (Finset.mem_filter.mp hqlarge).2
      have hcentral : q.2 * q.1 ∈ centralSmoothOrders p t err n :=
        buchstabOnePairs_image_subset
          (Finset.mem_image.mpr ⟨q, hqone, rfl⟩)
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨hcentral, ?_⟩
        rw [Nat.cast_mul]
        exact hqT
      · refine ⟨q.1, ?_, hPbig⟩
        exact Nat.mem_primeFactors.mpr
          ⟨hPprime, Nat.dvd_mul_left q.1 q.2, hprod_ne⟩
    · intro hm
      unfold LargePrimeSmoothWindow at hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hmwin, hmP⟩ := hm
      rw [Finset.mem_filter] at hmwin
      obtain ⟨hmcentral, hmT⟩ := hmwin
      obtain ⟨P, hPmem, hPbig⟩ := hmP
      have hPprime : P.Prime := Nat.prime_of_mem_primeFactors hPmem
      rw [← buchstabOnePairs_image_eq_centralSmoothOrders
        (p := p) (t := t) (err := err) (n := n) hp] at hmcentral
      rw [Finset.mem_image] at hmcentral
      obtain ⟨q, hqone, rfl⟩ := hmcentral
      obtain ⟨_hQmem, hQprime, hamem, hsmooth, _hI⟩ :=
        mem_buchstabOnePairs.mp hqone
      have ha_ne : q.2 ≠ 0 := by
        have := (Finset.mem_Icc.mp hamem).1
        omega
      have hPdvd : P ∣ q.2 * q.1 := Nat.dvd_of_mem_primeFactors hPmem
      have hPle : P ≤ q.1 := by
        rcases hPprime.dvd_mul.mp hPdvd with h | h
        · have hmem : P ∈ q.2.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hPprime, h, ha_ne⟩
          exact hsmooth P hmem
        · rcases (Nat.dvd_prime hQprime).mp h with h1 | h1
          · exact absurd h1 hPprime.ne_one
          · exact le_of_eq h1
      have hQbig : Real.sqrt (smoothCutoff t err n) < (q.1 : ℝ) :=
        lt_of_lt_of_le hPbig (by exact_mod_cast hPle)
      refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hqone, hQbig⟩
      · rw [Nat.cast_mul] at hmT
        exact hmT
  calc
    (((buchstabLargePrimePairs p t err n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) =
        ((LW.image (fun q : ℕ × ℕ => q.2 * q.1)).card : ℝ) := by
          rw [Finset.card_image_of_injOn hinj]
    _ = ((LargePrimeSmoothWindow p t err n T).card : ℝ) := by rw [himg]

/-- The large-prime sub-interval statement in purely smooth-number form: the
number of `y`-smooth central orders in the top window with a prime factor
larger than `√y` is at least `c p^{3/2} ρ(u)`. -/
def LargePrimeSmoothWindowLower (η c : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    c * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) ≤
      ((LargePrimeSmoothWindow p (paperT p) (paperError ε) n
        (p n ^ 2 - η * p n ^ ((3 : ℝ) / 2))).card : ℝ)

/-- **The sub-interval Buchstab statement is exactly a smooth-window lower
bound.**  No prime-pair bookkeeping remains: the residual is the number of
`y`-smooth central orders in the top window with a large prime factor. -/
theorem buchstabLargePrimeSubIntervalLower_iff_largePrimeSmoothWindowLower
    {η c : ℝ} {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} :
    BuchstabLargePrimeSubIntervalLower η c p ε ↔
      LargePrimeSmoothWindowLower η c p ε := by
  have hp2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ p n := by
    filter_upwards [h.eventually_sixteen] with n hn
    linarith
  constructor
  · intro hsub
    filter_upwards [hsub, hp2] with n hn hp
    have hcard := card_largePrimePairs_window_eq_largePrimeSmoothWindow
      (p := p) (t := paperT p) (err := paperError ε) (n := n) hp
      (p n ^ 2 - η * p n ^ ((3 : ℝ) / 2))
    have hn' : c * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) ≤
        (((buchstabLargePrimePairs p (paperT p) (paperError ε) n).filter
          (fun q : ℕ × ℕ =>
            p n ^ 2 - η * p n ^ ((3 : ℝ) / 2) < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) := by
      simpa [BuchstabLargePrimeSubIntervalLower, Nat.cast_mul, mul_assoc] using hn
    rw [hcard] at hn'
    exact hn'
  · intro hlw
    filter_upwards [hlw, hp2] with n hn hp
    have hcard := card_largePrimePairs_window_eq_largePrimeSmoothWindow
      (p := p) (t := paperT p) (err := paperError ε) (n := n) hp
      (p n ^ 2 - η * p n ^ ((3 : ℝ) / 2))
    rw [← hcard] at hn
    simpa [BuchstabLargePrimeSubIntervalLower, Nat.cast_mul, mul_assoc] using hn

/-! ## 4. The explicit window residual and its transfer -/

/-- The total `y`-smooth central orders in the top `η`-window number at least
`C p^{3/2} ρ(u)`.  This is the lower-bound half of the residual. -/
def WindowSmoothLower (η C : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    C * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) ≤
      (((centralSmoothOrders p (paperT p) (paperError ε) n).filter
        (fun m : ℕ => p n ^ 2 - η * p n ^ ((3 : ℝ) / 2) < (m : ℝ))).card : ℝ)

/-- The `√y`-smooth central orders in the same top `η`-window number at most
`D p^{3/2} ρ(u)`.  This is the short-interval upper-bound half of the residual;
it is the windowed form of `CentralSqrtSmoothUpper`. -/
def WindowSqrtSmoothUpper (η D : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    ((((centralOrderInterval p n).filter
        (fun m : ℕ => p n ^ 2 - η * p n ^ ((3 : ℝ) / 2) < (m : ℝ))).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff (paperT p) (paperError ε) n)))).card : ℝ) ≤
      D * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n)

/-- **The positive-proportion sub-interval transfer.**  A total-window lower
bound `(c + D) p^{3/2} ρ(u)` and a `√y`-window upper bound `D p^{3/2} ρ(u)` give
the large-prime lower bound `c p^{3/2} ρ(u)` on the same top window. -/
theorem buchstabLargePrimeSubIntervalLower_of_window
    {η D c C : ℝ} (_hη : 0 < η) (hCD : c + D ≤ C)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ}
    (hlow : WindowSmoothLower η C p ε)
    (hup : WindowSqrtSmoothUpper η D p ε) :
    BuchstabLargePrimeSubIntervalLower η c p ε := by
  have hp2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ p n := by
    filter_upwards [h.eventually_sixteen] with n hn
    linarith
  filter_upwards [hlow, hup, hp2] with n hnlow hnup hp
  let T : ℝ := p n ^ 2 - η * p n ^ ((3 : ℝ) / 2)
  have hsplit := centralSmoothOrders_window_card_eq_large_add_small
    (p := p) (t := paperT p) (err := paperError ε) (n := n) hp T
  have hsmall : (((buchstabSmallPrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) ≤
      ((((centralOrderInterval p n).filter (fun m : ℕ => T < (m : ℝ))).filter
        (IsSmoothUpTo (Real.sqrt (smoothCutoff (paperT p) (paperError ε) n)))).card : ℝ) :=
    buchstabSmallPrimePairs_window_card_le_sqrtSmooth (p := p)
      (t := paperT p) (err := paperError ε) (n := n) T
  have hsmallD : (((buchstabSmallPrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) ≤
      D * p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n) := by
    refine hsmall.trans ?_
    simpa [T] using hnup
  let X : ℝ := p n ^ ((3 : ℝ) / 2) * dickmanRho (paperDensityU p ε n)
  have hp0 : (0 : ℝ) < p n := by linarith
  have hX0 : 0 ≤ X :=
    mul_nonneg (Real.rpow_nonneg hp0.le _) (dickmanRho_nonneg _)
  have hlowX : C * X ≤
      (((centralSmoothOrders p (paperT p) (paperError ε) n).filter
        (fun m : ℕ => T < (m : ℝ))).card : ℝ) := by
    simpa [X, T, mul_assoc] using hnlow
  have hsmallX : (((buchstabSmallPrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) ≤ D * X := by
    simpa [X, mul_assoc] using hsmallD
  have hle : c ≤ C - D := by linarith
  have hCDX : c * X ≤ (C - D) * X := mul_le_mul_of_nonneg_right hle hX0
  have hCDX' : c * X ≤ C * X - D * X := by nlinarith [hCDX]
  have hgoal : c * X ≤
      (((buchstabLargePrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) := by
    nlinarith only [hlowX, hsmallX, hCDX', hsplit]
  simpa [BuchstabLargePrimeSubIntervalLower, X, T, Nat.cast_mul, mul_assoc] using hgoal

/-- **The full short-interval Buchstab lower bound from the two window
bounds.** -/
theorem buchstabLargePrimeShortIntervalLower_of_window
    {η D c C : ℝ} (hη : 0 < η) (hCD : c + D ≤ C)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ}
    (hlow : WindowSmoothLower η C p ε)
    (hup : WindowSqrtSmoothUpper η D p ε) :
    BuchstabLargePrimeShortIntervalLower c p ε :=
  buchstabLargePrimeShortIntervalLower_of_subInterval hη
    (buchstabLargePrimeSubIntervalLower_of_window hη hCD h hlow hup)

/-- The sub-interval statement implies the total-window lower bound with the
same constant (the large-prime pairs are a subset of the smooth window).  Thus
`WindowSmoothLower` is a necessary residual, not an extra assumption. -/
theorem windowSmoothLower_of_subInterval
    {η c : ℝ} {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ}
    (hsub : BuchstabLargePrimeSubIntervalLower η c p ε) :
    WindowSmoothLower η c p ε := by
  have hp2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ p n := by
    filter_upwards [h.eventually_sixteen] with n hn
    linarith
  filter_upwards [hsub, hp2] with n hn hp
  let T : ℝ := p n ^ 2 - η * p n ^ ((3 : ℝ) / 2)
  have hsplit := centralSmoothOrders_window_card_eq_large_add_small
    (p := p) (t := paperT p) (err := paperError ε) (n := n) hp T
  have hnonneg : (0 : ℝ) ≤
      (((buchstabSmallPrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) := by
    positivity
  have hle : (((buchstabLargePrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ => T < (q.2 : ℝ) * (q.1 : ℝ))).card : ℝ) ≤
      (((centralSmoothOrders p (paperT p) (paperError ε) n).filter
        (fun m : ℕ => T < (m : ℝ))).card : ℝ) := by
    nlinarith only [hsplit, hnonneg]
  refine hn.trans ?_
  simpa [BuchstabLargePrimeSubIntervalLower, T, Nat.cast_mul, mul_assoc] using hle

/-! ## 5. Monotonicity in the window parameter -/

/-- Enlarging the top sub-interval (`η₁ ≤ η₂`) preserves a lower bound with the
same constant: the `η₁`-pairs are a subset of the `η₂`-pairs. -/
theorem buchstabLargePrimeSubIntervalLower_mono_eta
    {η₁ η₂ c : ℝ} {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ᶠ n in atTop, 0 ≤ p n) (hη : η₁ ≤ η₂)
    (h : BuchstabLargePrimeSubIntervalLower η₁ c p ε) :
    BuchstabLargePrimeSubIntervalLower η₂ c p ε := by
  filter_upwards [h, hp] with n hn hpn
  have hsub : ((buchstabLargePrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ =>
          p n ^ 2 - η₁ * p n ^ ((3 : ℝ) / 2) < (q.2 * q.1 : ℝ))) ⊆
      ((buchstabLargePrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ =>
          p n ^ 2 - η₂ * p n ^ ((3 : ℝ) / 2) < (q.2 * q.1 : ℝ))) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hpow : 0 ≤ p n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hpn _
    have hmul : η₁ * p n ^ ((3 : ℝ) / 2) ≤ η₂ * p n ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hη hpow
    linarith [hq.2, hmul]
  have hcard := Finset.card_le_card hsub
  exact hn.trans (by exact_mod_cast hcard)

/-- For `η > 1/2` the top window contains the whole central interval, so the
sub-interval statement is *the same* as the full large-prime statement. -/
theorem buchstabLargePrimeSubIntervalLower_of_shortInterval_large_eta
    {η c : ℝ} (hη : (1 : ℝ) / 2 < η) {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ᶠ n in atTop, (2 : ℝ) ≤ p n)
    (h : BuchstabLargePrimeShortIntervalLower c p ε) :
    BuchstabLargePrimeSubIntervalLower η c p ε := by
  filter_upwards [h, hp] with n hn hp2
  have hp0 : (0 : ℝ) < p n := by linarith
  have hpow : (0 : ℝ) < p n ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hsub : ((buchstabLargePrimePairs p (paperT p) (paperError ε) n).filter
        (fun q : ℕ × ℕ =>
          p n ^ 2 - η * p n ^ ((3 : ℝ) / 2) < (q.2 * q.1 : ℝ))) =
      buchstabLargePrimePairs p (paperT p) (paperError ε) n := by
    apply Finset.filter_true_of_mem
    intro q hq
    have hqone : q ∈ buchstabOnePairs p (paperT p) (paperError ε) n :=
      buchstabLargePrimePairs_subset hq
    obtain ⟨_, _, _, _, hI⟩ := mem_buchstabOnePairs.mp hqone
    have hceil : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 ≤
        ((⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have hmem := (Finset.mem_Icc.mp hI).1
    have hcast : ((⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℕ) : ℝ) ≤
        ((q.2 * q.1 : ℕ) : ℝ) := by exact_mod_cast hmem
    have hlow : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 ≤
        ((q.2 * q.1 : ℕ) : ℝ) := hceil.trans hcast
    have hlow' : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 ≤
        (q.2 : ℝ) * (q.1 : ℝ) := by
      rw [Nat.cast_mul] at hlow
      exact hlow
    have hlt : p n ^ 2 - η * p n ^ ((3 : ℝ) / 2) <
        p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 := by nlinarith
    exact hlt.trans_le hlow'
  rw [hsub]
  exact hn

/-- For `η > 1/2` the sub-interval statement and the full large-prime statement
are equivalent. -/
theorem buchstabLargePrimeSubIntervalLower_iff_shortInterval_large_eta
    {η c : ℝ} (hη : (1 : ℝ) / 2 < η) {p : ℕ → ℝ} {ε : ℝ}
    (hp : ∀ᶠ n in atTop, (2 : ℝ) ≤ p n) :
    BuchstabLargePrimeSubIntervalLower η c p ε ↔
      BuchstabLargePrimeShortIntervalLower c p ε :=
  ⟨fun h => buchstabLargePrimeShortIntervalLower_of_subInterval
      (by linarith) h,
    fun h => buchstabLargePrimeSubIntervalLower_of_shortInterval_large_eta hη hp h⟩

/-! ## 6. The cofactor is forced to be large -/

/-- **Every large-prime Buchstab pair has a large cofactor.**  If the cutoff is
below `√p`, then `a > p^{3/2}/2`.  The proof uses
`a P ≥ p² - p^{3/2}/2` and `P ≤ y < √p`. -/
theorem cofactor_gt_half_rpow_of_largePrimePair
    {p t err : ℕ → ℝ} {n : ℕ} {q : ℕ × ℕ}
    (hp : 2 ≤ p n) (hy : smoothCutoff t err n < Real.sqrt (p n))
    (hq : q ∈ buchstabLargePrimePairs p t err n) :
    p n ^ ((3 : ℝ) / 2) / 2 < (q.2 : ℝ) := by
  have hbase : q ∈ buchstabOnePairs p t err n :=
    buchstabLargePrimePairs_subset hq
  obtain ⟨hPmem, _hPprime, _hamem, _hsmooth, hI⟩ := mem_buchstabOnePairs.mp hbase
  have hp0 : (0 : ℝ) < p n := by linarith
  have hp1 : (1 : ℝ) ≤ p n := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (p n) := Real.sqrt_pos.mpr hp0
  have hsq : Real.sqrt (p n) * Real.sqrt (p n) = p n := Real.mul_self_sqrt hp0.le
  have hpow : p n ^ ((3 : ℝ) / 2) = p n * Real.sqrt (p n) :=
    Cogentic.RandomizedL30CentralCount.rpow_three_halves_eq (p n) hp0
  have hypos : (0 : ℝ) < smoothCutoff t err n := Real.exp_pos _
  have hq1pos : (0 : ℝ) < (q.1 : ℝ) := by
    have := (Finset.mem_Icc.mp hPmem).1
    exact_mod_cast (by omega : 0 < q.1)
  have hPle : (q.1 : ℝ) ≤ smoothCutoff t err n := by
    have hfloor : q.1 ≤ ⌊smoothCutoff t err n⌋₊ := (Finset.mem_Icc.mp hPmem).2
    exact (Nat.cast_le.mpr hfloor).trans (Nat.floor_le hypos.le)
  have hprod_lower : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 ≤
      (q.2 : ℝ) * (q.1 : ℝ) := by
    have hceil : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 ≤
        ((⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have hmem := (Finset.mem_Icc.mp hI).1
    have hcast : ((⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℕ) : ℝ) ≤
        ((q.2 * q.1 : ℕ) : ℝ) := by exact_mod_cast hmem
    exact hceil.trans (hcast.trans (by rw [Nat.cast_mul]))
  have hq2_nonneg : (0 : ℝ) ≤ (q.2 : ℝ) := Nat.cast_nonneg _
  have hprod_le : (q.2 : ℝ) * (q.1 : ℝ) ≤
      (q.2 : ℝ) * smoothCutoff t err n :=
    mul_le_mul_of_nonneg_left hPle hq2_nonneg
  have hq2_ge : (p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2) /
        smoothCutoff t err n ≤ (q.2 : ℝ) := by
    rw [div_le_iff₀ hypos]
    calc
      p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 ≤ (q.2 : ℝ) * (q.1 : ℝ) := hprod_lower
      _ ≤ (q.2 : ℝ) * smoothCutoff t err n := hprod_le
  have hnum_pos : (0 : ℝ) < p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 := by
    have hle : p n ^ ((3 : ℝ) / 2) ≤ p n ^ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le hp1
        (by norm_num : ((3 : ℝ) / 2) ≤ (2 : ℝ))
      simpa [Real.rpow_natCast] using h
    have hp2 : (4 : ℝ) ≤ p n ^ 2 := by nlinarith [hp]
    nlinarith
  have hkey : p n ^ ((3 : ℝ) / 2) / 2 <
      (p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2) / smoothCutoff t err n := by
    rw [lt_div_iff₀ hypos]
    have hstep : p n ^ ((3 : ℝ) / 2) / 2 * smoothCutoff t err n <
        p n ^ ((3 : ℝ) / 2) / 2 * Real.sqrt (p n) :=
      mul_lt_mul_of_pos_left hy (by positivity)
    have hsqrt_eq : p n ^ ((3 : ℝ) / 2) / 2 * Real.sqrt (p n) = p n ^ 2 / 2 := by
      rw [hpow]
      field_simp [hs0.ne']
      nlinarith [hsq]
    have hhalf : p n ^ 2 / 2 ≤ p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 := by
      have hle : p n ^ ((3 : ℝ) / 2) ≤ p n ^ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le hp1
          (by norm_num : ((3 : ℝ) / 2) ≤ (2 : ℝ))
        simpa [Real.rpow_natCast] using h
      linarith
    linarith
  exact lt_of_lt_of_le hkey hq2_ge

/-- The paper cutoff is eventually below `√p`. -/
theorem eventually_smoothCutoff_lt_sqrt
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      smoothCutoff (paperT p) (paperError ε) n < Real.sqrt (p n) := by
  filter_upwards [h.eventually_sixteen,
    eventually_one_add_mul_paperT_lt_half_log h hε] with n h16 hsmall
  have hp0 : (0 : ℝ) < p n := by linarith
  have hexp : smoothCutoff (paperT p) (paperError ε) n =
      Real.exp ((1 + ε) * paperT p n) := by
    simp [smoothCutoff, paperError]
  rw [hexp]
  calc
    Real.exp ((1 + ε) * paperT p n) < Real.exp (Real.log (p n) / 2) :=
      Real.exp_lt_exp.mpr hsmall
    _ = Real.sqrt (p n) := by
      rw [← Real.log_sqrt hp0.le, Real.exp_log (Real.sqrt_pos.mpr hp0)]

/-- **Eventually every large-prime pair has cofactor strictly greater than
one.**  In particular the `a = 1` slice — primes near `p²` — contributes no
Buchstab pair at all. -/
theorem eventually_one_lt_cofactor
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ q ∈ buchstabLargePrimePairs p (paperT p) (paperError ε) n,
        (1 : ℝ) < (q.2 : ℝ) := by
  filter_upwards [h.eventually_sixteen, eventually_smoothCutoff_lt_sqrt h hε]
    with n h16 hy
  have hp2 : (2 : ℝ) ≤ p n := by linarith
  have hp0 : (0 : ℝ) < p n := by linarith
  intro q hq
  have hgt := cofactor_gt_half_rpow_of_largePrimePair hp2 hy hq
  have hs1 : (1 : ℝ) ≤ Real.sqrt (p n) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have hpow : p n ^ ((3 : ℝ) / 2) = p n * Real.sqrt (p n) :=
    Cogentic.RandomizedL30CentralCount.rpow_three_halves_eq (p n) hp0
  have htwo : (2 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) := by
    rw [hpow]
    nlinarith
  linarith

/-- **Every fixed cofactor is eventually excluded.**  For every `A : ℕ`, every
large-prime Buchstab pair has cofactor `> A` eventually.  In particular there is
no pair with a bounded cofactor, which rules out the "small smooth number `a`"
constructions at the central scale. -/
theorem eventually_cofactor_gt
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∀ᶠ n in atTop,
      ∀ q ∈ buchstabLargePrimePairs p (paperT p) (paperError ε) n,
        (A : ℝ) < (q.2 : ℝ) := by
  have harg : Tendsto (fun n => ((3 : ℝ) / 2) * Real.log (p n)) atTop atTop :=
    h.tendsto_log.const_mul_atTop (by norm_num)
  have hexp : Tendsto (fun n => Real.exp (((3 : ℝ) / 2) * Real.log (p n)))
      atTop atTop :=
    Real.tendsto_exp_atTop.comp harg
  have hpow : Tendsto (fun n => p n ^ ((3 : ℝ) / 2)) atTop atTop := by
    refine hexp.congr' ?_
    filter_upwards [h.eventually_sixteen] with n hn
    have hp0 : (0 : ℝ) < p n := by linarith
    rw [Real.rpow_def_of_pos hp0]
    congr 1
    ring
  have hhalf : Tendsto (fun n => p n ^ ((3 : ℝ) / 2) / 2) atTop atTop :=
    hpow.atTop_div_const (by norm_num)
  filter_upwards [h.eventually_sixteen, eventually_smoothCutoff_lt_sqrt h hε,
    hhalf.eventually_gt_atTop (A : ℝ)] with n h16 hy hA
  have hp2 : (2 : ℝ) ≤ p n := by linarith
  intro q hq
  have hcof := cofactor_gt_half_rpow_of_largePrimePair hp2 hy hq
  linarith

/-! ## 7. Non-vacuity of the sub-interval predicate -/

/-- The sub-interval predicate is inhabited at the explicit witness
`p = 9`, `ε = log 81 / t - 1`, `η = 1/2`, `c = 1/27`: the pair `(71, 1)`
lies in the top half of the central interval. -/
theorem buchstabLargePrimeSubIntervalLower_smallWitness :
    BuchstabLargePrimeSubIntervalLower (1 / 2) (1 / 27) smallWitnessP smallWitnessEps := by
  refine Filter.Eventually.of_forall (fun n => ?_)
  have hmem := smallWitness_pair_mem n
  have hmem' : (71, 1) ∈
      (buchstabLargePrimePairs smallWitnessP
        (paperT smallWitnessP) (paperError smallWitnessEps) n).filter
        (fun q : ℕ × ℕ =>
          smallWitnessP n ^ 2 - (1 / 2) * smallWitnessP n ^ ((3 : ℝ) / 2) <
            (q.2 * q.1 : ℝ)) := by
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    rw [smallWitness_rpow]
    norm_num [smallWitnessP]
  have hcard_pos : 0 <
      ((buchstabLargePrimePairs smallWitnessP
        (paperT smallWitnessP) (paperError smallWitnessEps) n).filter
        (fun q : ℕ × ℕ =>
          smallWitnessP n ^ 2 - (1 / 2) * smallWitnessP n ^ ((3 : ℝ) / 2) <
            (q.2 * q.1 : ℝ))).card :=
    Finset.card_pos.mpr ⟨(71, 1), hmem'⟩
  have hcard_ge : (1 : ℝ) ≤
      (((buchstabLargePrimePairs smallWitnessP
        (paperT smallWitnessP) (paperError smallWitnessEps) n).filter
        (fun q : ℕ × ℕ =>
          smallWitnessP n ^ 2 - (1 / 2) * smallWitnessP n ^ ((3 : ℝ) / 2) <
            (q.2 * q.1 : ℝ))).card : ℝ) := by
    exact_mod_cast hcard_pos
  have hleft : (1 / 27) * smallWitnessP n ^ ((3 : ℝ) / 2) *
        dickmanRho (paperDensityU smallWitnessP smallWitnessEps n) = 1 := by
    rw [smallWitness_rpow, smallWitness_paperDensityU, dickmanRho_one]
    norm_num
  rw [hleft]
  exact hcard_ge

/-! ## Axiom audit -/

#print axioms buchstabOnePairs_image_eq_centralSmoothOrders
#print axioms centralSmoothOrders_window_card_eq_large_add_small
#print axioms buchstabSmallPrimePairs_window_image_subset
#print axioms buchstabSmallPrimePairs_window_card_le_sqrtSmooth
#print axioms card_largePrimePairs_window_eq_largePrimeSmoothWindow
#print axioms buchstabLargePrimeSubIntervalLower_iff_largePrimeSmoothWindowLower
#print axioms buchstabLargePrimeSubIntervalLower_of_window
#print axioms buchstabLargePrimeShortIntervalLower_of_window
#print axioms windowSmoothLower_of_subInterval
#print axioms buchstabLargePrimeSubIntervalLower_mono_eta
#print axioms buchstabLargePrimeSubIntervalLower_of_shortInterval_large_eta
#print axioms buchstabLargePrimeSubIntervalLower_iff_shortInterval_large_eta
#print axioms cofactor_gt_half_rpow_of_largePrimePair
#print axioms eventually_smoothCutoff_lt_sqrt
#print axioms eventually_one_lt_cofactor
#print axioms eventually_cofactor_gt
#print axioms buchstabLargePrimeSubIntervalLower_smallWitness

end

end Cogentic.RandomizedL30BuchstabSubInterval
