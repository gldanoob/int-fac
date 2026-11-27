import Cogentic.RandomizedL30Analytic

/-!
# L30: reducing the Younis and LPP count inputs

`Cogentic/RandomizedL30Analytic.lean` states the two analytic counting
hypotheses of KeyBreak Proposition H.3 directly on explicit finite sets:

* `YounisShortIntervalCount p t err` — the central genus-two Hasse interval
  contains at least `p^{3/2} exp (-(1 + ε) t_p)` smooth orders;
* `LPPOrderFibreCount p t err fibreModels` — every eligible smooth order
  carries at least `p^{7/2} exp (-(1 + ε) t_p)` quintic models.

This file reduces each of those two statements to strictly smaller explicit
paper-level propositions, and assembles the result into
`Cogentic.RandomizedL30Analytic.AnalyticInputs`.

## Younis

The paper's argument has two independent analytic halves.  In the `s`-coordinate
(`n = 2s`, `s` odd) the central interval has length `≍ p^{3/2}`, and:

* `YounisOddRelativeShortInterval A` is Younis's relative short-interval
  density: the number of odd smooth orders in the central interval is at least
  `A` times the interval length times the global odd smooth density;
* `YounisOddGlobalLower B` is the classical global lower bound
  `Ψ_odd(p², Y) ≥ B p² exp (-(1 + ε) t_p)`, obtained in the paper by
  multiplying `k ≍ log p / log Y` distinct primes (Hildebrand–Tenenbaum /
  Canfield–Erdős–Pomerance range).

The constants `A` and `B` are explicit parameters: the Lean interval is the
one-sided `(p² - p^{3/2}/2, p²]`, so a fixed numerical value would silently
build the one-sided/two-sided conversion into an analytic hypothesis.  The
reduction `younisOddCentralCount_of_density` requires only `A B ≥ 4`, the
arithmetic relation forced by the interval-cardinality loss.

The elementary interval-cardinality lemma
`centralOrderInterval_card_ge_quarter` supplies `p^{3/2}/4 ≤ |interval|`.
Multiplying the two analytic bounds then gives the odd central count
`YounisOddCentralCount`.  Splitting the odd part off is faithful to the paper:
the parity condition is exactly what makes the genus-two model count work, and
the odd set is a subset of `centralSmoothOrders`, so a lower bound on it implies
the stated count.

The existing smooth-number estimate `Cogentic.Randomized.smoothCount_rankin_upper`
is an *upper* bound and cannot discharge `YounisOddGlobalLower`.  The
conditional lower construction
`Cogentic.Randomized.centeredBinProducts_density_from_critical_line` counts a
different object (prime-bin products in a multiplicative strip) under the
Dirichlet zero-free line, and converting it into the global smooth lower bound
would require the full parameter arithmetic of that construction; it is
therefore not used here, and the global lower bound is kept as the smallest
explicit analytic input.

## LPP

Lenstra–Pila–Pomerance II, Theorem 1.1 gives, for each non-exceptional
eligible order, at least `p^{9/2} / Q` nonsingular quintic models, where `Q` is
the explicit polylogarithmic loss.  Dividing by the `p - 1` normalization to
make the quintic monic and absorbing the `1 / polylog` into the `1 + o(1)`
error is the separate elementary inequality

* `LPPNormalization p t err Q : 0 < Q ∧ Q ≤ p · exp ((1 + ε) t_p)`.

`LPPRawModelCount` is the raw per-order theorem, and
`lppOrderFibreCount_of_raw` performs the normalization arithmetic
`p^{9/2} / (p exp ((1+ε)t)) = p^{7/2} exp (-(1+ε)t)`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count or
error is set to zero.
-/

namespace Cogentic.RandomizedL30Younis

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub

noncomputable section

/-! ## The odd smooth-order objects -/

/-- The parity condition of the genus-two order: `n = 2 s` with `s` odd, i.e.
`n ≡ 2 (mod 4)`.  The paper's central interval is counted along these orders
because the odd trace of the Jacobian is exactly what the LPP model count
requires. -/
def IsOddHalfOrder (m : ℕ) : Prop := m % 4 = 2

/-- The global `Y`-smooth integers up to `p²`, the same finite set used by
`Cogentic.Randomized.smoothCount_rankin_upper`. -/
noncomputable def globalSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊p n ^ 2⌋₊).filter (IsSmoothUpTo (smoothCutoff t err n))

/-- The odd part of the global smooth range. -/
noncomputable def globalOddSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (globalSmoothOrders p t err n).filter IsOddHalfOrder

/-- The global odd smooth count, as a real number. -/
noncomputable def globalOddSmoothCount (p t err : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((globalOddSmoothOrders p t err n).card : ℝ)

/-- The odd smooth orders in the central genus-two Hasse interval. -/
noncomputable def centralOddSmoothOrders (p t err : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (centralSmoothOrders p t err n).filter IsOddHalfOrder

/-- The central odd smooth count, as a real number. -/
noncomputable def centralOddSmoothCount (p t err : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((centralOddSmoothOrders p t err n).card : ℝ)

/-- The central odd smooth orders are a subset of the global odd smooth range. -/
theorem centralOddSmoothOrders_subset_globalOdd {p t err : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) :
    centralOddSmoothOrders p t err n ⊆ globalOddSmoothOrders p t err n := by
  intro m hm
  rw [centralOddSmoothOrders, Finset.mem_filter] at hm
  obtain ⟨hmc, hodd⟩ := hm
  rw [globalOddSmoothOrders, Finset.mem_filter]
  exact ⟨by simpa [globalSmoothOrders, IsSmoothUpTo] using
    (centralSmoothOrders_subset_global hp hmc), hodd⟩

/-- The central odd count never exceeds the central count. -/
theorem centralOddSmoothCount_le_smoothOrderCount (p t err : ℕ → ℝ) (n : ℕ) :
    centralOddSmoothCount p t err n ≤ smoothOrderCount p t err n := by
  unfold centralOddSmoothCount smoothOrderCount
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-! ## The Younis sub-propositions -/

/-- **Younis, odd-order central count.**  The central genus-two Hasse interval
contains at least `p^{3/2} exp (-(1+ε) t_p)` orders `n = 2s` with `s` odd and
`n` smooth.  This is the paper's actual count; the parity condition is what the
LPP model construction requires.  It is a subset of `centralSmoothOrders`, not
all of it. -/
def YounisOddCentralCount (p t err : ℕ → ℝ) : Prop :=
  ∀ n, p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * t n) ≤
    centralOddSmoothCount p t err n

/-- **Younis, relative short-interval density.**  In the central interval, the
number of odd `Y`-smooth orders is at least `A` times the interval length times
the global odd smooth density `Ψ_odd(p², Y) / p²`.  The constant `A` is kept
explicit because the Lean interval is the one-sided `(p² - p^{3/2}/2, p²]`
rather than the paper's full two-sided window; the factor is part of the
analytic statement and is not silently chosen here. -/
def YounisOddRelativeShortInterval (A : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, A * ((centralOrderInterval p n).card : ℝ) *
      (globalOddSmoothCount p t err n / p n ^ 2) ≤
    centralOddSmoothCount p t err n

/-- **Global odd smooth lower bound.**  `Ψ_odd(p², Y) ≥ B p² exp (-(1+ε) t_p)`.
This is the classical global smooth-number estimate at `x = p²`, stated only
for the odd-half integers `n = 2s` with `s` odd.  The constant `B` is explicit
for the same reason as in `YounisOddRelativeShortInterval`. -/
def YounisOddGlobalLower (B : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ n, B * p n ^ 2 * exp (-(1 + err n) * t n) ≤
    globalOddSmoothCount p t err n

/-! ## The elementary interval cardinality -/

/-- The central integer interval `(p² - p^{3/2}/2, p²]` contains at least
`p^{3/2}/4` integers for `p ≥ 2`.  This is the only elementary input needed to
pass from a density estimate to the stated `p^{3/2}` count; the factor `4`
absorbs the rounding of both endpoints, and the small-prime case `p < 2^{4/3}`
is handled by the nonemptiness of the interval. -/
theorem centralOrderInterval_card_ge_quarter {p : ℕ → ℝ} {n : ℕ}
    (hp : 2 ≤ p n) :
    p n ^ ((3 : ℝ) / 2) / 4 ≤ ((centralOrderInterval p n).card : ℝ) := by
  let L : ℝ := p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2
  let a : ℕ := ⌈L⌉₊
  let b : ℕ := ⌊p n ^ 2⌋₊
  have hp_pos : (0 : ℝ) < p n := by linarith
  have hL_nonneg : 0 ≤ L :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_central_lower hp)
  have ha_le_b : a ≤ b := by
    dsimp [a, b]
    apply Nat.le_floor
    have hceil : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL_nonneg
    have hhalf : (1 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) / 2 := by
      have h2 : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ p n ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by norm_num) hp (by norm_num)
      have h2v : (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
        rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]
      have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by norm_num)
      rw [h2v] at h2
      nlinarith
    have hLp1 : L + 1 ≤ p n ^ 2 := by
      dsimp [L]
      linarith
    linarith
  have hcard : ((centralOrderInterval p n).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
    dsimp [centralOrderInterval, a, b]
    rw [Nat.card_Icc]
    have hab : a ≤ b + 1 := by omega
    rw [Nat.cast_sub hab]
    push_cast
    ring
  have hb_ge : p n ^ 2 - 1 ≤ (b : ℝ) := by
    dsimp [b]
    have hlt := Nat.lt_floor_add_one (p n ^ 2)
    have hfloor : (⌊p n ^ 2⌋₊ : ℝ) ≤ p n ^ 2 := Nat.floor_le (by positivity)
    linarith
  have ha_le : (a : ℝ) ≤ L + 1 := by
    dsimp [a]
    exact (Nat.ceil_lt_add_one hL_nonneg).le
  have hmain : p n ^ ((3 : ℝ) / 2) / 2 - 1 ≤
      ((centralOrderInterval p n).card : ℝ) := by
    rw [hcard]
    dsimp [L] at ha_le ⊢
    linarith
  by_cases h4 : p n ^ ((3 : ℝ) / 2) ≤ 4
  · have hquarter : p n ^ ((3 : ℝ) / 2) / 4 ≤ 1 := by linarith
    have hcardpos : 1 ≤ ((centralOrderInterval p n).card : ℝ) := by
      have hpos : 0 < (centralOrderInterval p n).card := by
        apply Finset.card_pos.mpr
        refine ⟨a, ?_⟩
        dsimp [centralOrderInterval, a, b]
        rw [Finset.mem_Icc]
        exact ⟨le_rfl, ha_le_b⟩
      exact_mod_cast hpos
    linarith
  · push Not at h4
    linarith

/-! ## Younis's count from the odd count and from the two halves -/

/-- **The Younis count from the odd-order count.**  The odd orders are a subset
of `centralSmoothOrders`, so the paper's parity-restricted count implies the
count on the whole smooth set. -/
theorem younisShortIntervalCount_of_odd {p t err : ℕ → ℝ}
    (hodd : YounisOddCentralCount p t err) :
    YounisShortIntervalCount p t err := by
  intro n
  exact (hodd n).trans (centralOddSmoothCount_le_smoothOrderCount p t err n)

/-- **The odd-order count from relative density plus the global lower bound.**
If relative density holds with constant `A`, the global odd lower bound holds
with constant `B`, and `A B ≥ 4`, then the two halves give the odd count.  The
factor `4` is exactly the interval-cardinality loss
`|interval| ≥ p^{3/2}/4`; the condition `A B ≥ 4` is the only arithmetic
relation between the two constants, so neither density constant is chosen here.
-/
theorem younisOddCentralCount_of_density {p t err : ℕ → ℝ} {A B : ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A) (hB : 0 < B) (hAB : 4 ≤ A * B)
    (hrel : YounisOddRelativeShortInterval A p t err)
    (hglob : YounisOddGlobalLower B p t err) :
    YounisOddCentralCount p t err := by
  intro n
  have hp_pos : (0 : ℝ) < p n := by linarith [hp n]
  have hp2 : (0 : ℝ) < p n ^ 2 := by positivity
  have hcard := centralOrderInterval_card_ge_quarter (hp n)
  have hdiv : B * exp (-(1 + err n) * t n) ≤
      globalOddSmoothCount p t err n / p n ^ 2 := by
    rw [le_div_iff₀ hp2]
    have h := hglob n
    nlinarith
  have hcoef : (0 : ℝ) ≤ A * B * exp (-(1 + err n) * t n) := by positivity
  have hcardmul := mul_le_mul_of_nonneg_left hcard hcoef
  have hABone : (1 : ℝ) ≤ A * B / 4 := by nlinarith
  have hbase : (0 : ℝ) ≤ p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * t n) := by
    positivity
  have hbasescale : p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * t n) ≤
      (A * B / 4) * (p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * t n)) := by
    calc
      p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * t n)
          = (1 : ℝ) * (p n ^ ((3 : ℝ) / 2) *
              exp (-(1 + err n) * t n)) := by ring
      _ ≤ (A * B / 4) * (p n ^ ((3 : ℝ) / 2) *
              exp (-(1 + err n) * t n)) :=
            mul_le_mul_of_nonneg_right hABone hbase
  have hstep1 : (A * B / 4) * (p n ^ ((3 : ℝ) / 2) *
        exp (-(1 + err n) * t n)) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (B * exp (-(1 + err n) * t n)) := by
    calc
      (A * B / 4) * (p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * t n))
          = (A * B * exp (-(1 + err n) * t n)) *
              (p n ^ ((3 : ℝ) / 2) / 4) := by ring
      _ ≤ (A * B * exp (-(1 + err n) * t n)) *
            ((centralOrderInterval p n).card : ℝ) := hcardmul
      _ = A * ((centralOrderInterval p n).card : ℝ) *
            (B * exp (-(1 + err n) * t n)) := by ring
  have hstep2 : A * ((centralOrderInterval p n).card : ℝ) *
        (B * exp (-(1 + err n) * t n)) ≤
      A * ((centralOrderInterval p n).card : ℝ) *
        (globalOddSmoothCount p t err n / p n ^ 2) :=
    mul_le_mul_of_nonneg_left hdiv (by positivity)
  exact hbasescale.trans (hstep1.trans (hstep2.trans (hrel n)))

/-! ## The LPP raw count and its normalization -/

/-- **Lenstra–Pila–Pomerance II, Theorem 1.1, raw per-order count.**  Every
eligible smooth order in the central interval carries at least
`p^{9/2} / Q` nonsingular quintic models, where `Q` is the explicit
polylogarithmic loss.  This is the model-count theorem before the `p - 1`
monic normalization and before absorbing `1 / polylog` into `err`. -/
def LPPRawModelCount (p t err : ℕ → ℝ) (fibreModels : ℕ → ℕ → Finset ℕ)
    (Q : ℕ → ℝ) : Prop :=
  ∀ n m, m ∈ centralSmoothOrders p t err n →
    p n ^ ((9 : ℝ) / 2) / Q n ≤ ((fibreModels n m).card : ℝ)

/-- **The LPP normalization.**  The polylogarithmic loss `Q` is at most
`p · exp ((1 + ε) t_p)`.  Dividing the raw `p^{9/2}` count by `p - 1` and by
`Q`, this is exactly the statement that the loss is absorbed by the
`1 + o(1)` error. -/
def LPPNormalization (p t err : ℕ → ℝ) (Q : ℕ → ℝ) : Prop :=
  ∀ n, 0 < Q n ∧ Q n ≤ p n * exp ((1 + err n) * t n)

/-- **LPP after normalization.**  The raw count `p^{9/2} / Q` and the
normalization `Q ≤ p exp ((1+ε)t)` give the stated
`p^{7/2} exp (-(1+ε)t)` per-order count. -/
theorem lppOrderFibreCount_of_raw {p t err : ℕ → ℝ}
    {fibreModels : ℕ → ℕ → Finset ℕ} {Q : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n)
    (hQ : LPPNormalization p t err Q)
    (hraw : LPPRawModelCount p t err fibreModels Q) :
    LPPOrderFibreCount p t err fibreModels := by
  intro n m hm
  have hp_pos : (0 : ℝ) < p n := by linarith [hp n]
  obtain ⟨hQpos, hQle⟩ := hQ n
  have hp9 : (0 : ℝ) < p n ^ ((9 : ℝ) / 2) := Real.rpow_pos_of_pos hp_pos _
  have hdiv_le : p n ^ ((9 : ℝ) / 2) /
        (p n * exp ((1 + err n) * t n)) ≤
      p n ^ ((9 : ℝ) / 2) / Q n := by
    apply div_le_div_of_nonneg_left hp9.le hQpos hQle
  have heq : p n ^ ((9 : ℝ) / 2) /
        (p n * exp ((1 + err n) * t n)) =
      p n ^ ((7 : ℝ) / 2) * exp (-(1 + err n) * t n) := by
    have hsplit : p n ^ ((9 : ℝ) / 2) = p n ^ ((7 : ℝ) / 2) * p n := by
      rw [show ((9 : ℝ) / 2) = (7 : ℝ) / 2 + 1 by norm_num,
        Real.rpow_add hp_pos, Real.rpow_one]
    rw [hsplit]
    rw [show p n ^ ((7 : ℝ) / 2) * p n /
          (p n * exp ((1 + err n) * t n)) =
        p n ^ ((7 : ℝ) / 2) / exp ((1 + err n) * t n) by field_simp]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  rw [heq] at hdiv_le
  exact hdiv_le.trans (hraw n m hm)

/-! ## The bundled reduction -/

/-- The elementary Cantor/H.5 data, separated from the two counting estimates.
These are exactly the non-counting fields of `AnalyticInputs`. -/
structure CantorCostInputs where
  /-- `k_y`. -/
  k : ℕ → ℝ
  /-- `k_y ≥ 0`. -/
  k_nonneg : ∀ n, 0 ≤ k n
  /-- The polynomial factor of H.5. -/
  polyFactor : ℕ → ℝ
  /-- The polynomial factor is nonnegative. -/
  polyFactor_nonneg : ∀ n, 0 ≤ polyFactor n
  /-- The confidence parameter `L_c`. -/
  Lc : ℕ → ℝ
  /-- `L_c ≥ 1`. -/
  Lc_ge_one : ∀ n, 1 ≤ Lc n
  /-- The per-call cost. -/
  trialCost : ℕ → ℝ
  /-- **KB (H.5), literal cost form.** -/
  cantor_literal : CantorArithmeticCostLiteral k polyFactor Lc trialCost
  /-- **KB H.3, genus-two Jacobian/Cantor correctness.** -/
  cantor_arithmetic : Prop
  /-- The Cantor/Jacobian correctness proposition holds. -/
  cantor_arithmetic_holds : cantor_arithmetic

/-- The smaller explicit analytic propositions replacing `YounisShortIntervalCount`
and `LPPOrderFibreCount`, together with the data they refer to. -/
structure YounisLPPInputs where
  /-- The prime whose genus-two order is counted at scale `n`. -/
  p : ℕ → ℝ
  /-- The paper's `t_p = √(log p · log log p)`. -/
  t : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The prime is at least `2`. -/
  p_ge_two : ∀ n, 2 ≤ p n
  /-- The finite set of quintic models attached to order `m`. -/
  fibreModels : ℕ → ℕ → Finset ℕ
  /-- The polylogarithmic loss in the raw LPP count. -/
  Q : ℕ → ℝ
  /-- The relative short-interval density constant. -/
  A : ℝ
  /-- The global smooth lower-bound constant. -/
  B : ℝ
  /-- `A > 0`. -/
  A_pos : 0 < A
  /-- `B > 0`. -/
  B_pos : 0 < B
  /-- The arithmetic relation forced by the interval-cardinality loss. -/
  AB_ge_four : 4 ≤ A * B
  /-- Younis's relative short-interval density for odd smooth orders. -/
  younis_relative : YounisOddRelativeShortInterval A p t err
  /-- The global odd smooth lower bound. -/
  younis_global : YounisOddGlobalLower B p t err
  /-- The LPP normalization. -/
  lpp_normalization : LPPNormalization p t err Q
  /-- The raw LPP per-order model count. -/
  lpp_raw : LPPRawModelCount p t err fibreModels Q

namespace YounisLPPInputs

variable (S : YounisLPPInputs)

/-- **The Younis odd-order count** from the two smaller analytic halves. -/
theorem younisOddCentralCount :
    YounisOddCentralCount S.p S.t S.err :=
  younisOddCentralCount_of_density S.p_ge_two S.A_pos S.B_pos S.AB_ge_four
    S.younis_relative S.younis_global

/-- **The Younis count** from the odd-order count. -/
theorem younisShortIntervalCount :
    YounisShortIntervalCount S.p S.t S.err :=
  younisShortIntervalCount_of_odd S.younisOddCentralCount

/-- **The LPP per-order fibre count** from the raw theorem and normalization. -/
theorem lppOrderFibreCount :
    LPPOrderFibreCount S.p S.t S.err S.fibreModels :=
  lppOrderFibreCount_of_raw S.p_ge_two S.lpp_normalization S.lpp_raw

/-- **The reduction to `AnalyticInputs`.**  The two counting fields are
discharged by `younisShortIntervalCount` and `lppOrderFibreCount`; the remaining
fields are the explicit H.5 cost and Cantor-correctness data. -/
noncomputable def toAnalyticInputs (C : CantorCostInputs) : AnalyticInputs where
  p := S.p
  t := S.t
  err := S.err
  p_ge_two := S.p_ge_two
  k := C.k
  k_nonneg := C.k_nonneg
  polyFactor := C.polyFactor
  polyFactor_nonneg := C.polyFactor_nonneg
  Lc := C.Lc
  Lc_ge_one := C.Lc_ge_one
  trialCost := C.trialCost
  fibreModels := S.fibreModels
  younis := S.younisShortIntervalCount
  lpp := S.lppOrderFibreCount
  cantor_literal := C.cantor_literal
  cantor_arithmetic := C.cantor_arithmetic
  cantor_arithmetic_holds := C.cantor_arithmetic_holds

/-- The resulting `PaperInputs`, via the reduction proved in
`RandomizedL30Analytic`. -/
noncomputable def toPaperInputs (C : CantorCostInputs) : PaperInputs :=
  (S.toAnalyticInputs C).toPaperInputs

end YounisLPPInputs

/-! ## Axiom audit -/

#print axioms centralOddSmoothOrders_subset_globalOdd
#print axioms centralOddSmoothCount_le_smoothOrderCount
#print axioms centralOrderInterval_card_ge_quarter
#print axioms younisShortIntervalCount_of_odd
#print axioms younisOddCentralCount_of_density
#print axioms lppOrderFibreCount_of_raw
#print axioms YounisLPPInputs.younisOddCentralCount
#print axioms YounisLPPInputs.younisShortIntervalCount
#print axioms YounisLPPInputs.lppOrderFibreCount
#print axioms YounisLPPInputs.toAnalyticInputs
#print axioms YounisLPPInputs.toPaperInputs

end

end Cogentic.RandomizedL30Younis
