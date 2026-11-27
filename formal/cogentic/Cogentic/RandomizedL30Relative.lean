import Cogentic.RandomizedL30Younis

/-!
# L30: the relative short-interval density from an explicit interval count

`Cogentic/RandomizedL30Younis.lean` isolates the two analytic halves of
Younis's central genus-two count:

* `YounisOddRelativeShortInterval A` — relative short-interval density of odd
  smooth orders;
* `YounisOddGlobalLower B` — the global odd smooth lower bound.

This file addresses only the first half.  It has two parts.

## 1. The smallest explicit short-interval count

The relative-density statement compares the central odd smooth count with the
*global* odd smooth count through the factor
`A * |centralOrderInterval| * (globalOddSmoothCount / p²)`.  The global count
admits the unconditional parity bound

`globalOddSmoothCount ≤ p² / 4 + 1 / 2 ≤ 3 p² / 8`   (`p ≥ 2`),

because an odd-half order is `n = 2 s` with `s` odd, and at most half of the
integers up to `p²` are even, half of those have `s` odd.  Consequently the
relative statement follows from the single interval count

`a * |centralOrderInterval| ≤ centralOddSmoothCount`

with `a = 3 A / 8`.  This is the smallest explicit short-interval count needed
for the reduction; it involves no global smooth-number input.  The reduction is
`younisOddRelative_of_intervalDensity`.

## 2. A concrete constructed local smooth set

To show the reduced statement is not vacuous, we construct an explicit set of
odd-half orders in the central interval and prove the interval count for it.
The set is

`{ p_n² - (4 j + 2) : 0 ≤ j < 8^{n+3} }`,

with the concrete order scale `p_n = 4^{n+4}`.  Every element is `≡ 2 (mod 4)`,
lies in `(p_n² - p_n^{3/2}/2, p_n²]`, and is smooth for the concrete cutoff
`Y_n = exp (3 log p_n) = p_n³`, so it is an odd smooth order.  The set has
exactly `8^{n+3}` elements, and the interval has at most
`4 · 8^{n+3} + 1` elements, so the interval density holds with `a = 1/5`.
Applying the reduction gives `YounisOddRelativeShortInterval (1/2)` for this
concrete data.

The witness uses a large smoothness cutoff (`Y = p³`); it is a consistency and
non-vacuity check for the reduced statement, not a substitute for the paper's
analytic short-interval theorem at `Y = exp ((1 + ε) t_p)`.  The order scale is
not required to be prime by the formal predicate, and the witness is not meant
as a prime-order instance.  The reduction in part 1 is the paper-facing result:
it isolates the interval count with no global smooth-number hypothesis and no
hidden constant.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count or error
is set to zero.
-/

namespace Cogentic.RandomizedL30Relative

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis

noncomputable section

/-! ## The reduced interval count -/

/-- **The smallest explicit short-interval count.**  The number of odd smooth
orders in the central interval is at least `a` times the whole interval length.
This is the one counting statement from which the relative density follows
using only the unconditional parity bound on the global smooth count. -/
def YounisOddIntervalDensity (a : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, a * ((centralOrderInterval p n).card : ℝ) ≤ centralOddSmoothCount p t err n

/-! ## The global parity bound -/

/-- Among the integers `1, …, N`, at most `N / 4 + 1 / 2` are `≡ 2 (mod 4)`.
This is the parity content behind the upper bound on the global odd smooth
count. -/
theorem card_oddHalf_Icc_le (N : ℕ) :
    (((Finset.Icc 1 N).filter IsOddHalfOrder).card : ℝ) ≤ (N : ℝ) / 4 + 1 / 2 := by
  let g : ℕ → ℕ := fun s => 4 * s + 2
  have hsub : (Finset.Icc 1 N).filter IsOddHalfOrder ⊆
      (Finset.range ((N + 2) / 4)).image g := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmN⟩, hmod⟩ := hm
    rw [Finset.mem_image]
    refine ⟨m / 4, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hmeq : m = 4 * (m / 4) + 2 := by
        have h := Nat.div_add_mod m 4
        rw [hmod] at h
        have h' : 4 * (m / 4) + 2 = m := h
        exact h'.symm
      have hle : 4 * (m / 4 + 1) ≤ N + 2 := by nlinarith
      have hq : m / 4 + 1 ≤ (N + 2) / 4 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
        simpa only [Nat.mul_comm] using hle
      exact Nat.lt_of_succ_le hq
    · dsimp only [g]
      have hmeq : m = 4 * (m / 4) + 2 := by
        have h := Nat.div_add_mod m 4
        rw [hmod] at h
        have h' : 4 * (m / 4) + 2 = m := h
        exact h'.symm
      omega
  have hcard : ((Finset.Icc 1 N).filter IsOddHalfOrder).card ≤
      ((Finset.range ((N + 2) / 4)).image g).card := Finset.card_le_card hsub
  have hcard' : ((Finset.Icc 1 N).filter IsOddHalfOrder).card ≤ (N + 2) / 4 := by
    calc
      ((Finset.Icc 1 N).filter IsOddHalfOrder).card
          ≤ ((Finset.range ((N + 2) / 4)).image g).card := hcard
      _ ≤ (Finset.range ((N + 2) / 4)).card := Finset.card_image_le
      _ = (N + 2) / 4 := Finset.card_range _
  have hcast : (((N + 2) / 4 : ℕ) : ℝ) ≤ ((N : ℝ) + 2) / 4 := by
    have h := (Nat.cast_div_le (α := ℝ) (m := N + 2) (n := 4))
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have h1 : (((Finset.Icc 1 N).filter IsOddHalfOrder).card : ℝ) ≤
      (((N + 2) / 4 : ℕ) : ℝ) := by exact_mod_cast hcard'
  linarith only [h1, hcast]

/-- The global odd smooth count is at most `p² / 4 + 1 / 2` for `p ≥ 2`.
The smoothness restriction can only shrink the set, so this is a parity bound,
not a smooth-number estimate. -/
theorem globalOddSmoothCount_le_quarter_sq {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) :
    globalOddSmoothCount p t err n ≤ p n ^ 2 / 4 + 1 / 2 := by
  let N : ℕ := ⌊p n ^ 2⌋₊
  have hsub : globalOddSmoothOrders p t err n ⊆
      (Finset.Icc 1 N).filter IsOddHalfOrder := by
    intro m hm
    rw [globalOddSmoothOrders, globalSmoothOrders, Finset.mem_filter] at hm
    obtain ⟨hmS, hodd⟩ := hm
    obtain ⟨hmI, _⟩ := Finset.mem_filter.mp hmS
    exact Finset.mem_filter.mpr ⟨hmI, hodd⟩
  have hcard : globalOddSmoothCount p t err n ≤
      (((Finset.Icc 1 N).filter IsOddHalfOrder).card : ℝ) := by
    unfold globalOddSmoothCount
    exact_mod_cast Finset.card_le_card hsub
  have hbound := card_oddHalf_Icc_le N
  have hfloor : (N : ℝ) ≤ p n ^ 2 := Nat.floor_le (by positivity)
  linarith only [hcard, hbound, hfloor]

/-! ## The reduction to the interval count -/

/-- **Relative density from the explicit interval count.**  If the central
interval contains at least `a` times its length in odd smooth orders, and
`3 A / 8 ≤ a`, then the relative short-interval density holds with constant
`A`.  The factor `3 / 8` is the worst-case parity density of the global odd
smooth range. -/
theorem younisOddRelative_of_intervalDensity
    {A a : ℝ} {p t err : ℕ → ℝ}
    (hA : 0 ≤ A) (hp : ∀ n, 2 ≤ p n) (ha : 3 * A / 8 ≤ a)
    (hdens : YounisOddIntervalDensity a p t err) :
    YounisOddRelativeShortInterval A p t err := by
  intro n
  have hp_pos : (0 : ℝ) < p n := by linarith [hp n]
  have hp2 : (0 : ℝ) < p n ^ 2 := pow_pos hp_pos 2
  have hp4 : (4 : ℝ) ≤ p n ^ 2 := by
    have hp2' : (2 : ℝ) ≤ p n := by exact_mod_cast hp n
    nlinarith [sq_nonneg (p n - 2), hp2']
  have hG := globalOddSmoothCount_le_quarter_sq (p := p) (t := t) (err := err) (hp n)
  have hratio : globalOddSmoothCount p t err n / p n ^ 2 ≤ 3 / 8 := by
    rw [div_le_iff₀ hp2]
    nlinarith only [hG, hp4]
  have hK : (0 : ℝ) ≤ ((centralOrderInterval p n).card : ℝ) := by positivity
  calc
    A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p t err n / p n ^ 2)
        ≤ A * ((centralOrderInterval p n).card : ℝ) * (3 / 8) :=
          mul_le_mul_of_nonneg_left hratio (mul_nonneg hA hK)
    _ = (3 * A / 8) * ((centralOrderInterval p n).card : ℝ) := by ring
    _ ≤ a * ((centralOrderInterval p n).card : ℝ) :=
          mul_le_mul_of_nonneg_right ha hK
    _ ≤ centralOddSmoothCount p t err n := hdens n

/-! ## The concrete witness -/

/-- The explicit order scale `p_n = 4^{n+4}`.  This choice makes `p_n²` and
`p_n^{3/2}` integers, which keeps the interval arithmetic exact. -/
def witnessP (n : ℕ) : ℝ := (4 : ℝ) ^ (n + 4)

/-- `p_n²` as a natural number. -/
def witnessTop (n : ℕ) : ℕ := 4 ^ (2 * (n + 4))

/-- The number of explicit odd smooth orders `p_n² - (4 j + 2)` used at index
`n`; it equals `p_n^{3/2} / 8`. -/
def witnessLevel (n : ℕ) : ℕ := 8 ^ (n + 3)

/-- The explicit cutoff exponent `3 log p_n`, so that
`exp ((1 + ε) t) = p_n³` with `ε = 0`. -/
def witnessT (n : ℕ) : ℝ := 3 * Real.log (witnessP n)

/-- The explicit relative error. -/
def witnessErr : ℕ → ℝ := fun _ => 0

/-- The relative-density constant of the witness. -/
def witnessA : ℝ := 1 / 2

/-- The interval-density constant of the witness. -/
def witnessDensity : ℝ := 1 / 5

/-- The concrete local set of odd-half orders
`{ p_n² - (4 j + 2) : j < 8^{n+3} }`. -/
def witnessLocalSet (n : ℕ) : Finset ℕ :=
  (Finset.range (witnessLevel n)).image (fun j => witnessTop n - (4 * j + 2))

/-- The explicit scale is at least two. -/
theorem witnessP_ge_two (n : ℕ) : 2 ≤ witnessP n := by
  unfold witnessP
  have h : (4 : ℝ) ≤ (4 : ℝ) ^ (n + 4) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
      (by omega : 1 ≤ n + 4)
  linarith

/-- The explicit scale is positive. -/
theorem witnessP_pos (n : ℕ) : 0 < witnessP n := by
  unfold witnessP
  positivity

/-- `p_n²` is the natural number `witnessTop n`. -/
theorem witnessP_sq (n : ℕ) : witnessP n ^ 2 = (witnessTop n : ℝ) := by
  unfold witnessP witnessTop
  rw [← pow_mul]
  push_cast
  ring

/-- `p_n^{3/2} = 8^{n+4}`. -/
theorem witnessP_rpow_three_halves (n : ℕ) :
    witnessP n ^ ((3 : ℝ) / 2) = (8 : ℝ) ^ (n + 4) := by
  unfold witnessP
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  calc
    ((4 : ℝ) ^ (n + 4)) ^ ((3 : ℝ) / 2)
        = ((4 : ℝ) ^ ((n + 4 : ℕ) : ℝ)) ^ ((3 : ℝ) / 2) := by
            rw [Real.rpow_natCast]
    _ = (4 : ℝ) ^ (((n + 4 : ℕ) : ℝ) * ((3 : ℝ) / 2)) :=
          (Real.rpow_mul h4 ((n + 4 : ℕ) : ℝ) ((3 : ℝ) / 2)).symm
    _ = (4 : ℝ) ^ (((3 : ℝ) / 2) * ((n + 4 : ℕ) : ℝ)) := by rw [mul_comm]
    _ = ((4 : ℝ) ^ ((3 : ℝ) / 2)) ^ ((n + 4 : ℕ) : ℝ) :=
          Real.rpow_mul h4 ((3 : ℝ) / 2) ((n + 4 : ℕ) : ℝ)
    _ = ((4 : ℝ) ^ ((3 : ℝ) / 2)) ^ (n + 4) := by rw [Real.rpow_natCast]
    _ = (8 : ℝ) ^ (n + 4) := by
          congr 1
          rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) h4]
          have hs : Real.sqrt 4 = 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
            norm_num
          rw [hs]
          norm_num

/-- `8^{n+4} / 2 = 4 · witnessLevel n`. -/
theorem witness_eight_pow_half (n : ℕ) :
    (8 : ℝ) ^ (n + 4) / 2 = 4 * (witnessLevel n : ℝ) := by
  unfold witnessLevel
  rw [show n + 4 = (n + 3) + 1 by omega, pow_succ]
  rw [Nat.cast_pow]
  norm_num
  ring

/-- The lower endpoint of the central interval is `witnessTop n - 4 · level`. -/
theorem witness_lower_endpoint (n : ℕ) :
    witnessP n ^ 2 - witnessP n ^ ((3 : ℝ) / 2) / 2 =
      (witnessTop n : ℝ) - 4 * (witnessLevel n : ℝ) := by
  rw [witnessP_sq, witnessP_rpow_three_halves, witness_eight_pow_half]

/-- `witnessTop n` is divisible by four. -/
theorem witnessTop_dvd_four (n : ℕ) : 4 ∣ witnessTop n := by
  unfold witnessTop
  refine ⟨4 ^ (2 * (n + 4) - 1), ?_⟩
  have hk : 2 * (n + 4) = (2 * (n + 4) - 1) + 1 := by omega
  calc
    4 ^ (2 * (n + 4)) = 4 ^ ((2 * (n + 4) - 1) + 1) := by
      conv_lhs => rw [hk]
    _ = 4 ^ (2 * (n + 4) - 1) * 4 := by rw [pow_succ]
    _ = 4 * 4 ^ (2 * (n + 4) - 1) := by rw [mul_comm]

/-- Every element of the local set is a natural number below `witnessTop n`. -/
theorem witness_local_element_lt (n j : ℕ) (hj : j < witnessLevel n) :
    4 * j + 2 < witnessTop n := by
  have hltlevel : 4 * j + 2 < 4 * witnessLevel n := by omega
  have htop : witnessTop n = 4 ^ (2 * (n + 4)) := rfl
  have hcmp : 4 * witnessLevel n ≤ witnessTop n := by
    unfold witnessLevel witnessTop
    have h1 : 4 * 8 ^ (n + 3) = 2 ^ (3 * (n + 3) + 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
        show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
      rw [← pow_add]
      congr 1
      ring
    have h2 : 4 ^ (2 * (n + 4)) = 2 ^ (4 * (n + 4)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      congr 1
      ring
    rw [h1, h2]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  omega

/-- The local set is contained in the central odd smooth orders. -/
theorem witnessLocalSet_subset (n : ℕ) :
    witnessLocalSet n ⊆ centralOddSmoothOrders witnessP witnessT witnessErr n := by
  intro m hm
  rw [witnessLocalSet, Finset.mem_image] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  rw [Finset.mem_range] at hj
  have hlt := witness_local_element_lt n j hj
  have hle : 4 * j + 2 ≤ witnessTop n := hlt.le
  have hmem_cast : ((witnessTop n - (4 * j + 2) : ℕ) : ℝ) =
      (witnessTop n : ℝ) - (4 * (j : ℝ) + 2) := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [centralOddSmoothOrders, Finset.mem_filter]
  constructor
  · rw [centralSmoothOrders, Finset.mem_filter]
    constructor
    · rw [centralOrderInterval, Finset.mem_Icc]
      constructor
      · rw [Nat.ceil_le]
        have hstart := witness_lower_endpoint n
        have hj1 : j + 1 ≤ witnessLevel n := Nat.succ_le_of_lt hj
        have hjreal : (j : ℝ) + 1 ≤ (witnessLevel n : ℝ) := by exact_mod_cast hj1
        have hlt' : (4 * (j : ℝ) + 2) < 4 * (witnessLevel n : ℝ) := by
          nlinarith
        rw [hstart, hmem_cast]
        linarith
      · have htop_floor : ⌊witnessP n ^ 2⌋₊ = witnessTop n := by
          rw [witnessP_sq, Nat.floor_natCast]
        rw [htop_floor]
        exact Nat.sub_le _ _
    · intro q hq
      have hq_dvd : q ∣ witnessTop n - (4 * j + 2) := Nat.dvd_of_mem_primeFactors hq
      have hpos : 0 < witnessTop n - (4 * j + 2) := by omega
      have hq_le : q ≤ witnessTop n - (4 * j + 2) := Nat.le_of_dvd hpos hq_dvd
      have hle_top : q ≤ witnessTop n := hq_le.trans (Nat.sub_le _ _)
      have hq_real : (q : ℝ) ≤ witnessP n ^ 2 := by
        rw [witnessP_sq]
        exact_mod_cast hle_top
      have hsmooth : smoothCutoff witnessT witnessErr n = witnessP n ^ 3 := by
        unfold smoothCutoff witnessT witnessErr
        rw [show (1 + (0 : ℝ)) * (3 * Real.log (witnessP n)) =
            (3 : ℕ) * Real.log (witnessP n) by norm_num]
        rw [Real.exp_nat_mul, Real.exp_log (witnessP_pos n)]
      rw [hsmooth]
      have hp1 : (1 : ℝ) ≤ witnessP n := by linarith [witnessP_ge_two n]
      have hp23 : witnessP n ^ 2 ≤ witnessP n ^ 3 :=
        pow_le_pow_right₀ hp1 (by norm_num : 2 ≤ 3)
      exact hq_real.trans hp23
  · -- odd-half condition
    obtain ⟨C, hC⟩ := witnessTop_dvd_four n
    have hCj : j + 1 ≤ C := by
      have hlt4 : 4 * (j + 1) ≤ 4 * C := by
        rw [← hC]
        omega
      omega
    have hm_eq : witnessTop n - (4 * j + 2) = 4 * (C - (j + 1)) + 2 := by
      rw [hC]
      omega
    rw [IsOddHalfOrder, hm_eq]
    omega

/-- The local set has exactly `witnessLevel n` elements. -/
theorem witnessLocalSet_card (n : ℕ) :
    (witnessLocalSet n).card = witnessLevel n := by
  unfold witnessLocalSet
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range _
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    have hlt_a := witness_local_element_lt n a ha
    have hlt_b := witness_local_element_lt n b hb
    have hle_a : 4 * a + 2 ≤ witnessTop n := hlt_a.le
    have hle_b : 4 * b + 2 ≤ witnessTop n := hlt_b.le
    simp only at hab
    omega

/-- The explicit interval count for the witness: the central odd smooth count
is at least `witnessLevel n`. -/
theorem witnessLevel_le_centralOddSmoothCount (n : ℕ) :
    (witnessLevel n : ℝ) ≤
      centralOddSmoothCount witnessP witnessT witnessErr n := by
  have hsub := witnessLocalSet_subset n
  have hcard : (witnessLocalSet n).card ≤
      (centralOddSmoothOrders witnessP witnessT witnessErr n).card :=
    Finset.card_le_card hsub
  rw [witnessLocalSet_card] at hcard
  unfold centralOddSmoothCount
  exact_mod_cast hcard

/-- The central interval has at most `4 · witnessLevel n + 1` elements. -/
theorem witness_centralOrderInterval_card_le (n : ℕ) :
    ((centralOrderInterval witnessP n).card : ℝ) ≤
      4 * (witnessLevel n : ℝ) + 1 := by
  let L : ℝ := witnessP n ^ 2 - witnessP n ^ ((3 : ℝ) / 2) / 2
  let a : ℕ := ⌈L⌉₊
  let b : ℕ := ⌊witnessP n ^ 2⌋₊
  have hb : b = witnessTop n := by
    dsimp only [b]
    rw [witnessP_sq, Nat.floor_natCast]
  have hL_nonneg : 0 ≤ L := by
    have hp2 : (4 : ℝ) ≤ witnessP n ^ 2 := by
      have hp : (2 : ℝ) ≤ witnessP n := witnessP_ge_two n
      nlinarith [sq_nonneg (witnessP n - 2), hp]
    have hquarter : witnessP n ^ ((3 : ℝ) / 2) / 2 ≤ witnessP n ^ 2 := by
      -- `p^{3/2} / 2 ≤ p²` is immediate for `p ≥ 2`.
      have hp32 : witnessP n ^ ((3 : ℝ) / 2) ≤ witnessP n ^ 2 := by
        have hp1 : (1 : ℝ) ≤ witnessP n := by
          linarith [witnessP_ge_two n]
        simpa using Real.rpow_le_rpow_of_exponent_le hp1
          (by norm_num : ((3 : ℝ) / 2) ≤ (2 : ℝ))
      linarith
    dsimp only [L]
    linarith
  have ha_le_b : a ≤ b := by
    rw [show a = ⌈L⌉₊ from rfl, Nat.ceil_le]
    rw [hb]
    have hL_eq : L = (witnessTop n : ℝ) - 4 * (witnessLevel n : ℝ) :=
      witness_lower_endpoint n
    rw [hL_eq]
    linarith
  have hcard : ((centralOrderInterval witnessP n).card : ℝ) =
      (b : ℝ) + 1 - (a : ℝ) := by
    dsimp only [centralOrderInterval, a, b, L]
    rw [Nat.card_Icc]
    have hab : a ≤ b + 1 := le_trans ha_le_b (Nat.le_succ b)
    rw [Nat.cast_sub hab]
    push_cast
    ring
  have ha_ge : L ≤ (a : ℝ) := Nat.le_ceil L
  have hL_eq : L = (witnessTop n : ℝ) - 4 * (witnessLevel n : ℝ) :=
    witness_lower_endpoint n
  have ha_real : (witnessTop n : ℝ) - 4 * (witnessLevel n : ℝ) ≤ (a : ℝ) := by
    rw [← hL_eq]
    exact ha_ge
  have hb_real : (b : ℝ) = (witnessTop n : ℝ) := by rw [hb]
  rw [hcard, hb_real]
  linarith

/-- The witness satisfies the explicit interval count with constant `1/5`. -/
theorem witness_intervalDensity :
    YounisOddIntervalDensity witnessDensity witnessP witnessT witnessErr := by
  intro n
  have hC := witnessLevel_le_centralOddSmoothCount n
  have hK := witness_centralOrderInterval_card_le n
  have hlevel_one : (1 : ℝ) ≤ (witnessLevel n : ℝ) := by
    have hpos : 0 < witnessLevel n := by
      unfold witnessLevel
      positivity
    have h1 : 1 ≤ witnessLevel n := by omega
    exact_mod_cast h1
  have hK' : witnessDensity * ((centralOrderInterval witnessP n).card : ℝ) ≤
      witnessDensity * (4 * (witnessLevel n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hK (by norm_num [witnessDensity])
  have hlevel : witnessDensity * (4 * (witnessLevel n : ℝ) + 1) ≤
      (witnessLevel n : ℝ) := by
    unfold witnessDensity
    nlinarith [hlevel_one]
  exact hK'.trans (hlevel.trans hC)

/-- **The concrete relative short-interval density.**  With the explicit order
scale `p_n = 4^{n+4}`, cutoff `Y_n = p_n³`, zero relative error, and constant
`1/2`, Younis's relative short-interval density holds for the constructed local
set of odd smooth orders. -/
theorem witness_relative :
    YounisOddRelativeShortInterval witnessA witnessP witnessT witnessErr := by
  refine younisOddRelative_of_intervalDensity
    (A := witnessA) (a := witnessDensity)
    (by norm_num [witnessA]) (fun n => witnessP_ge_two n) ?_
    witness_intervalDensity
  norm_num [witnessA, witnessDensity]

/-- The relative short-interval statement is not vacuous: there are explicit
`A > 0`, `p`, `t`, `err` for which it holds. -/
theorem exists_younisOddRelativeShortInterval :
    ∃ (A : ℝ) (p t err : ℕ → ℝ),
      0 < A ∧ YounisOddRelativeShortInterval A p t err :=
  ⟨witnessA, witnessP, witnessT, witnessErr, by norm_num [witnessA], witness_relative⟩

/-! ## Axiom audit -/

#print axioms card_oddHalf_Icc_le
#print axioms globalOddSmoothCount_le_quarter_sq
#print axioms younisOddRelative_of_intervalDensity
#print axioms witnessP_ge_two
#print axioms witnessP_sq
#print axioms witnessP_rpow_three_halves
#print axioms witness_eight_pow_half
#print axioms witness_lower_endpoint
#print axioms witnessTop_dvd_four
#print axioms witness_local_element_lt
#print axioms witnessLocalSet_subset
#print axioms witnessLocalSet_card
#print axioms witnessLevel_le_centralOddSmoothCount
#print axioms witness_centralOrderInterval_card_le
#print axioms witness_intervalDensity
#print axioms witness_relative
#print axioms exists_younisOddRelativeShortInterval

end

end Cogentic.RandomizedL30Relative
