import Cogentic.RandomizedL27Analytic

/-!
# L27 Deuring reduction: the Hurwitz and `j`-line inputs behind LP §7

`Cogentic.RandomizedL27Analytic` leaves two paper-level `Prop`s for the
Deuring/Lenstra distribution of elliptic-curve orders:

* `DeuringSmoothOrderCount` — every stage-one-smooth order in the Hasse window is
  realised by at least `κ√p` curves;
* `HasseWindowCurveTotal` — the total number of curves in the Hasse window is at
  most `4p`.

This file reduces each of them to strictly smaller, explicitly named statements.

## Deuring side

The per-order bound is split through the Frobenius discriminant

`D(p,j) = 4p - (p + 1 - j)²`

and an abstract Hurwitz class number `H : ℤ → ℝ`.  The two remaining inputs are

* `DeuringTraceFormula` — the Deuring/Waterhouse correspondence, in the
  one-sided form needed here: a smooth order is realised by at least the Hurwitz
  weight `H (D(p,j))` of curves;
* `HurwitzClassLower` — the Siegel/Brauer–Siegel lower bound at the Hasse scale:
  `H (D(p,j)) ≥ κ√p` on stage-one-smooth orders.

Both are quoted theorems of LP §7.  The reduction
`deuringSmoothOrderCount_of_hurwitz` composes them, and
`deuringSmoothOrderCount_iff_split` records that the intermediate Hurwitz
weight is lossless: a pointwise lower bound is equivalent to the existence of
such a weight.

The discriminant is compatible with the existing Hasse input: for a nonzero
order `j`, `0 ≤ D(p,j)`, and always `D(p,j) ≤ 4p`
(`frobeniusDisc_nonneg_of_orderCount_ne_zero`,
`frobeniusDisc_le_four_mul`).  The Hasse estimate used is exactly
`RandomizedL27_1.HasseBound`.

## Curve-total side

The `≤ 4p` total is reduced to the elementary `j`-line stratification

* `JInvariantStratification` — at most `p` `j`-invariants, each with at most two
  twists, except at most two exceptional invariants (`0` and `1728`) with at
  most six twists.  This totals at most `2p + 8` curves
  (`sum_multiplicity_le_two_mul_add_eight`), hence at most `4p` for `p ≥ 4`
  (`hasseWindowCurveTotal_of_jInvariant`).  The hypothesis `4 ≤ p` is the
  small-prime prepass (the target prime is an odd prime `≥ 5` after removing
  `2` and `3`); for `p = 2` the direct total is supplied by the caller.

## What the existing dyadic modules do and do not supply

`RandomizedHasseIncidence` and `RandomizedEllipticAndGaussian` prove dyadic
exceptional-prime incidence and recursive-splitting failure bounds.  They do not
count elliptic curves by order, supply the Hurwitz class-number lower bound, or
bound the `j`-line total, so none of the sub-Props below can be discharged from
those modules.  The one existing estimate used directly is the Hasse interval
`RandomizedL27_1.HasseBound`, which places every realised order in the interval
and hence makes the Frobenius discriminant nonnegative.

No discriminant, class number, or curve count is set to zero:
`L27DeuringInputs` stores every remaining paper input, and `toPaperInputs`
merely reassembles `L27PaperInputs`.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL27Deuring

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. Frobenius trace and discriminant -/

/-- The Frobenius trace `t = p + 1 - j` of a curve with `j` points over `F_p`. -/
def hasseTrace (p j : ℕ) : ℤ := (p : ℤ) + 1 - (j : ℤ)

/-- The Frobenius discriminant `4p - t²`.  This is the positive integer whose
Hurwitz class number controls the number of curves with exactly `p + 1 - t`
points; it is nonnegative inside the Hasse interval. -/
def frobeniusDisc (p j : ℕ) : ℤ := 4 * (p : ℤ) - hasseTrace p j ^ 2

/-- The discriminant is never above `4p`. -/
theorem frobeniusDisc_le_four_mul (p j : ℕ) :
    frobeniusDisc p j ≤ 4 * (p : ℤ) := by
  unfold frobeniusDisc
  have h : (0 : ℤ) ≤ hasseTrace p j ^ 2 := sq_nonneg _
  linarith

/-- Inside the Hasse interval the Frobenius discriminant is nonnegative.  The
only input is the Hasse endpoint estimate. -/
theorem frobeniusDisc_nonneg {p j : ℕ}
    (h : |(j : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)) :
    0 ≤ frobeniusDisc p j := by
  have ht : |((p : ℝ) + 1 - (j : ℝ))| ≤ 2 * Real.sqrt (p : ℝ) := by
    rw [abs_sub_comm]
    exact h
  have hsq : ((p : ℝ) + 1 - (j : ℝ)) ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 := by
    rw [sq_le_sq,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (p : ℝ))]
    exact ht
  have h4 : (2 * Real.sqrt (p : ℝ)) ^ 2 = 4 * (p : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    ring
  have hcast : ((frobeniusDisc p j : ℤ) : ℝ) =
      4 * (p : ℝ) - ((p : ℝ) + 1 - (j : ℝ)) ^ 2 := by
    unfold frobeniusDisc hasseTrace
    push_cast
    ring
  have hnonneg : (0 : ℝ) ≤ ((frobeniusDisc p j : ℤ) : ℝ) := by
    rw [hcast]
    nlinarith [hsq, h4]
  exact_mod_cast hnonneg

/-- A realised curve order lies in the Hasse interval, so its Frobenius
discriminant is nonnegative. -/
theorem frobeniusDisc_nonneg_of_orderCount_ne_zero {I : L27_1Inputs} {n j : ℕ}
    (h : I.orderCount n j ≠ 0) : 0 ≤ frobeniusDisc (I.p n) j :=
  frobeniusDisc_nonneg (I.hasse n j h)

/-- A stage-one-smooth order is realised, hence its Frobenius discriminant is
nonnegative.  This is the point where the existing `HasseBound` is used. -/
theorem frobeniusDisc_nonneg_of_smooth {I : L27_1Inputs} {n j : ℕ}
    (hs : I.smooth n j = true) : 0 ≤ frobeniusDisc (I.p n) j :=
  frobeniusDisc_nonneg_of_orderCount_ne_zero (I.smooth_realized n j hs)

/-! ## 2. Splitting `DeuringSmoothOrderCount` through the Hurwitz count -/

/-- **Deuring's trace correspondence, one-sided.**  A stage-one-smooth order
`j` is realised by at least the Hurwitz class number of its Frobenius
discriminant `4p - (p + 1 - j)²`.  The sum over twists is absorbed into
`hurwitz`; only the direction needed by Deuring's lower bound is retained. -/
def DeuringTraceFormula (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool)
    (orderCount : ℕ → ℕ → ℕ) (hurwitz : ℤ → ℝ) : Prop :=
  ∀ n j, smooth n j = true →
    hurwitz (frobeniusDisc (p n) j) ≤ (orderCount n j : ℝ)

/-- **Hurwitz class-number lower bound at the Hasse scale.**  At every
Frobenius discriminant attached to a stage-one-smooth order, the Hurwitz class
number is at least `κ√p`.  This is the Siegel/Brauer–Siegel lower bound in the
explicit normalization used by LP §7. -/
def HurwitzClassLower (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool)
    (hurwitz : ℤ → ℝ) (κ : ℝ) : Prop :=
  ∀ n j, smooth n j = true →
    κ * Real.sqrt (p n) ≤ hurwitz (frobeniusDisc (p n) j)

/-- The Deuring correspondence and the Hurwitz lower bound compose to the
per-order Deuring/Lenstra count. -/
theorem deuringSmoothOrderCount_of_hurwitz {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {orderCount : ℕ → ℕ → ℕ} {κ : ℝ}
    {hurwitz : ℤ → ℝ}
    (htrace : DeuringTraceFormula p smooth orderCount hurwitz)
    (hlower : HurwitzClassLower p smooth hurwitz κ) :
    DeuringSmoothOrderCount p smooth orderCount κ := by
  intro n j hs
  exact (hlower n j hs).trans (htrace n j hs)

/-- **The Deuring/Hurwitz split is lossless.**  A pointwise lower bound on the
curve count is equivalent to the existence of an intermediate Hurwitz-weighted
count that is dominated by the curve count and itself obeys the analytic lower
bound.  The forward direction takes the curve count itself as the weight, so no
curve is discarded. -/
theorem deuringSmoothOrderCount_iff_split {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {orderCount : ℕ → ℕ → ℕ} {κ : ℝ} :
    DeuringSmoothOrderCount p smooth orderCount κ ↔
      ∃ hurwitz : ℕ → ℕ → ℝ,
        (∀ n j, hurwitz n j ≤ (orderCount n j : ℝ)) ∧
          ∀ n j, smooth n j = true → κ * Real.sqrt (p n) ≤ hurwitz n j := by
  constructor
  · intro h
    exact ⟨fun n j => (orderCount n j : ℝ), fun _ _ => le_rfl,
      fun n j hs => h n j hs⟩
  · rintro ⟨hurwitz, hdom, hlow⟩ n j hs
    exact (hlow n j hs).trans (hdom n j)

/-! ## 3. The `j`-line stratification behind `HasseWindowCurveTotal` -/

/-- **Multiplicity sum over the `j`-line.**  At most `p` invariants, each
contributing at most two twists except for at most two exceptional invariants
contributing at most six, total at most `2p + 8` curves. -/
theorem sum_multiplicity_le_two_mul_add_eight (strata exc : Finset ℕ)
    (m : ℕ → ℕ) (p : ℕ)
    (hcard : strata.card ≤ p) (hsub : exc ⊆ strata) (hexc : exc.card ≤ 2)
    (hm : ∀ x ∈ strata, x ∉ exc → m x ≤ 2)
    (hme : ∀ x ∈ exc, m x ≤ 6) :
    (∑ x ∈ strata, (m x : ℝ)) ≤ 2 * (p : ℝ) + 8 := by
  have hsplit : (∑ x ∈ strata, (m x : ℝ)) =
      (∑ x ∈ exc, (m x : ℝ)) + (∑ x ∈ (strata \ exc), (m x : ℝ)) := by
    rw [← Finset.sum_sdiff hsub, add_comm]
  have he : (∑ x ∈ exc, (m x : ℝ)) ≤ 6 * (exc.card : ℝ) := by
    calc
      (∑ x ∈ exc, (m x : ℝ)) ≤ ∑ _x ∈ exc, (6 : ℝ) :=
        Finset.sum_le_sum fun x hx => by exact_mod_cast hme x hx
      _ = 6 * (exc.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hd : (∑ x ∈ (strata \ exc), (m x : ℝ)) ≤
      2 * ((strata \ exc).card : ℝ) := by
    calc
      (∑ x ∈ (strata \ exc), (m x : ℝ)) ≤ ∑ _x ∈ (strata \ exc), (2 : ℝ) :=
        Finset.sum_le_sum fun x hx => by
          rw [Finset.mem_sdiff] at hx
          exact_mod_cast hm x hx.1 hx.2
      _ = 2 * ((strata \ exc).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hsubcard : exc.card ≤ strata.card := Finset.card_le_card hsub
  have hdcard : ((strata \ exc).card : ℝ) =
      (strata.card : ℝ) - (exc.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub hsubcard]
  have hc : (strata.card : ℝ) ≤ (p : ℝ) := by exact_mod_cast hcard
  have h2e : (exc.card : ℝ) ≤ 2 := by exact_mod_cast hexc
  rw [hsplit]
  nlinarith [he, hd, hdcard, hc, h2e]

/-- **The `j`-line stratification of the curve count.**  The geometric form of
the `2p + 8` total: at most `p` `j`-invariants, at most two exceptional
invariants (`0` and `1728`), and twist multiplicities at most `2` away from the
exceptions and at most `6` at them. -/
def JInvariantStratification (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) : Prop :=
  ∀ n, ∃ (strata : Finset ℕ) (m : ℕ → ℕ) (exc : Finset ℕ),
    strata.card ≤ p n ∧ exc ⊆ strata ∧ exc.card ≤ 2 ∧
      (∀ x ∈ strata, x ∉ exc → m x ≤ 2) ∧
        (∀ x ∈ exc, m x ≤ 6) ∧
          curveTotal orderCount orderTop n = ∑ x ∈ strata, (m x : ℝ)

/-- The sharp `2p + 8` total curve count. -/
def JInvariantCurveTotal (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) : Prop :=
  ∀ n, curveTotal orderCount orderTop n ≤ 2 * (p n : ℝ) + 8

/-- The stratification implies the `2p + 8` total. -/
theorem jInvariantCurveTotal_of_stratification {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JInvariantStratification p orderCount orderTop) :
    JInvariantCurveTotal p orderCount orderTop := by
  intro n
  obtain ⟨strata, m, exc, hcard, hsub, hexc, hm, hme, htotal⟩ := h n
  rw [htotal]
  exact sum_multiplicity_le_two_mul_add_eight strata exc m (p n)
    hcard hsub hexc hm hme

/-- `2p + 8 ≤ 4p` for `p ≥ 4`, the elementary small-prime threshold. -/
theorem two_mul_add_eight_le_four_mul {p : ℕ} (hp : 4 ≤ p) :
    2 * (p : ℝ) + 8 ≤ 4 * (p : ℝ) := by
  have hp' : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  linarith

/-- **`HasseWindowCurveTotal` from the `j`-line stratification.**  The sharper
`2p + 8` count implies the paper's `4p` total once the small primes have been
removed (`4 ≤ p`). -/
theorem hasseWindowCurveTotal_of_jInvariant {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JInvariantCurveTotal p orderCount orderTop) (hp : ∀ n, 4 ≤ p n) :
    HasseWindowCurveTotal p orderCount orderTop := by
  intro n
  have hle := two_mul_add_eight_le_four_mul (hp n)
  linarith [h n]

/-- **`HasseWindowCurveTotal` without a global small-prime hypothesis.**  The
sharp `2p + 8` count covers every `p ≥ 4`; only the finitely many indices with
`p < 4` need the paper's `4p` bound directly.  This is the form used when the
target prime is not known to be prime in the interface (for a prime `p > 3`,
the fallback set is empty). -/
theorem hasseWindowCurveTotal_of_jInvariant_and_small {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JInvariantCurveTotal p orderCount orderTop)
    (hsmall : ∀ n, p n < 4 →
      curveTotal orderCount orderTop n ≤ 4 * (p n : ℝ)) :
    HasseWindowCurveTotal p orderCount orderTop := by
  intro n
  by_cases hp : p n < 4
  · exact hsmall n hp
  · have hp4 : 4 ≤ p n := by omega
    have hle := two_mul_add_eight_le_four_mul hp4
    linarith [h n]

/-- The total count is monotone under pointwise domination of the order
counts: bounding a model count bounds any smaller curve count. -/
theorem hasseWindowCurveTotal_of_dominated {p : ℕ → ℕ}
    {modelCount orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hdom : ∀ n j, orderCount n j ≤ modelCount n j)
    (h : HasseWindowCurveTotal p modelCount orderTop) :
    HasseWindowCurveTotal p orderCount orderTop := by
  intro n
  have hle : curveTotal orderCount orderTop n ≤
      curveTotal modelCount orderTop n := by
    unfold curveTotal
    exact Finset.sum_le_sum fun j _ => by exact_mod_cast hdom n j
  exact hle.trans (h n)

/-- The sharp `2p + 8` count is likewise monotone under pointwise domination. -/
theorem jInvariantCurveTotal_of_dominated {p : ℕ → ℕ}
    {modelCount orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hdom : ∀ n j, orderCount n j ≤ modelCount n j)
    (h : JInvariantCurveTotal p modelCount orderTop) :
    JInvariantCurveTotal p orderCount orderTop := by
  intro n
  have hle : curveTotal orderCount orderTop n ≤
      curveTotal modelCount orderTop n := by
    unfold curveTotal
    exact Finset.sum_le_sum fun j _ => by exact_mod_cast hdom n j
  exact hle.trans (h n)

/-! ## 4. The bundled smallest Deuring inputs -/

/-- **The smallest explicit inputs behind LP §7's Deuring counts.**

* `hurwitz` — the Hurwitz class number of the Frobenius discriminant;
* `deuring_trace` — the one-sided Deuring/Waterhouse correspondence;
* `hurwitz_class_lower` — the Hurwitz lower bound `κ√p` on smooth orders;
* `j_invariant_strata` — the elementary `j`-line stratification of the curves;
* `p_ge_four` — the small-prime prepass (`2, 3` removed), needed to turn the
  sharp `2p + 8` total into the paper's `4p`.

No field sets a count or probability to zero. -/
structure L27DeuringInputs (I : L27_1Inputs) where
  /-- The Hurwitz class number of a Frobenius discriminant. -/
  hurwitz : ℤ → ℝ
  /-- The Deuring/Waterhouse trace correspondence. -/
  deuring_trace : DeuringTraceFormula I.p I.smooth I.orderCount hurwitz
  /-- The Hurwitz class-number lower bound on smooth orders. -/
  hurwitz_class_lower : HurwitzClassLower I.p I.smooth hurwitz I.κ
  /-- The `j`-line stratification of the curves. -/
  j_invariant_strata : JInvariantStratification I.p I.orderCount I.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  p_ge_four : ∀ n, 4 ≤ I.p n

namespace L27DeuringInputs

variable {I : L27_1Inputs}

/-- The per-order Deuring/Lenstra bound from the Hurwitz split. -/
theorem deuringSmoothOrderCount (D : L27DeuringInputs I) :
    DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ :=
  RandomizedL27Deuring.deuringSmoothOrderCount_of_hurwitz
    D.deuring_trace D.hurwitz_class_lower

/-- The sharp `2p + 8` total from the `j`-line stratification. -/
theorem jInvariantCurveTotal (D : L27DeuringInputs I) :
    JInvariantCurveTotal I.p I.orderCount I.orderTop :=
  jInvariantCurveTotal_of_stratification D.j_invariant_strata

/-- The paper's `≤ 4p` total from the sharp `2p + 8` total and the small-prime
prepass. -/
theorem hasseWindowCurveTotal (D : L27DeuringInputs I) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  hasseWindowCurveTotal_of_jInvariant D.jInvariantCurveTotal D.p_ge_four

/-- The bundled `DeuringLenstraCounts` hypothesis of `L27_1Sub`. -/
theorem deuringLenstraCounts (D : L27DeuringInputs I) :
    DeuringLenstraCounts I :=
  deuringLenstraCounts_of_components D.deuringSmoothOrderCount D.hasseWindowCurveTotal

/-- Reassemble `L27PaperInputs` from the smaller Deuring inputs and the five
remaining LP §7 inputs (Hasse, the three gcd-exit facts, and stage-one
success). -/
theorem toPaperInputs (D : L27DeuringInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    L27PaperInputs I where
  deuring_smooth_order_count := D.deuringSmoothOrderCount
  hasse_window_curve_total := D.hasseWindowCurveTotal
  hasse_bound := hhasse
  gcd_exit_nonneg := h0
  gcd_exit_le_inv := h1
  gcd_exit_le_failure := h2
  stage_one_smooth_success := hstage

/-- The L27.1 ledger from the smaller Deuring inputs. -/
theorem reduced_ledger (D : L27DeuringInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L27PaperInputs.reduced_ledger (D.toPaperInputs hhasse h0 h1 h2 hstage) hbudget hlog

/-- The manuscript-rate deficit bound from the smaller Deuring inputs. -/
theorem reduced_paper (D : L27DeuringInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  L27PaperInputs.reduced_paper (D.toPaperInputs hhasse h0 h1 h2 hstage) hbudget hlog

/-- The L27.1 `RatedLeaf` from the smaller Deuring inputs. -/
def toRatedLeaf (D : L27DeuringInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf :=
  L27PaperInputs.toRatedLeaf (D.toPaperInputs hhasse h0 h1 h2 hstage) hbudget hlog

/-- The `C5` slot `exp (-2H)` for the assembled leaf. -/
theorem slot (D : L27DeuringInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop,
      (D.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog).loss n ≤
        Real.exp (-(2 : ℝ) * scale n) :=
  (D.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog).slot

end L27DeuringInputs

/-! ## 5. Capstone reduction -/

/-- **The full reduction from the smallest Deuring inputs.**  The Hurwitz split,
the `j`-line stratification, Hasse, the three gcd-exit facts, stage-one success,
the curve budget, and the `log₂` multiplier imply both bundled `L27_1Sub`
hypotheses and both deficit conclusions. -/
theorem reduction_of_deuring {I : L27_1Inputs} (D : L27DeuringInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) := by
  let P : L27PaperInputs I := D.toPaperInputs hhasse h0 h1 h2 hstage
  exact ⟨L27PaperInputs.deuring P, L27PaperInputs.elliptic P,
    L27PaperInputs.reduced_ledger P hbudget hlog,
    L27PaperInputs.reduced_paper P hbudget hlog⟩

/-- The Deuring half of the capstone, stated on its own: the Hurwitz split and
the `j`-line stratification already give `DeuringLenstraCounts`. -/
theorem deuringLenstraCounts_of_deuring {I : L27_1Inputs}
    (D : L27DeuringInputs I) : DeuringLenstraCounts I :=
  D.deuringLenstraCounts

/-- **Compatibility with `RandomizedL27Analytic`.**  Rebuilding the paper inputs
from the smaller Deuring inputs yields exactly the same bundled Deuring/Lenstra
hypothesis as `L27Analytic`'s `L27PaperInputs`. -/
theorem deuringLenstraCounts_via_paperInputs {I : L27_1Inputs}
    (D : L27DeuringInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    DeuringLenstraCounts I :=
  L27PaperInputs.deuring (D.toPaperInputs hhasse h0 h1 h2 hstage)

/-! ## Axiom audit -/

#print axioms frobeniusDisc_le_four_mul
#print axioms frobeniusDisc_nonneg
#print axioms frobeniusDisc_nonneg_of_orderCount_ne_zero
#print axioms frobeniusDisc_nonneg_of_smooth
#print axioms deuringSmoothOrderCount_of_hurwitz
#print axioms deuringSmoothOrderCount_iff_split
#print axioms sum_multiplicity_le_two_mul_add_eight
#print axioms jInvariantCurveTotal_of_stratification
#print axioms two_mul_add_eight_le_four_mul
#print axioms hasseWindowCurveTotal_of_jInvariant
#print axioms hasseWindowCurveTotal_of_jInvariant_and_small
#print axioms hasseWindowCurveTotal_of_dominated
#print axioms jInvariantCurveTotal_of_dominated
#print axioms L27DeuringInputs.deuringSmoothOrderCount
#print axioms L27DeuringInputs.jInvariantCurveTotal
#print axioms L27DeuringInputs.hasseWindowCurveTotal
#print axioms L27DeuringInputs.deuringLenstraCounts
#print axioms L27DeuringInputs.toPaperInputs
#print axioms L27DeuringInputs.reduced_ledger
#print axioms L27DeuringInputs.reduced_paper
#print axioms L27DeuringInputs.toRatedLeaf
#print axioms L27DeuringInputs.slot
#print axioms reduction_of_deuring
#print axioms deuringLenstraCounts_of_deuring
#print axioms deuringLenstraCounts_via_paperInputs

end

end Cogentic.RandomizedL27Deuring
