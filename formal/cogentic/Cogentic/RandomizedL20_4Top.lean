import Cogentic.RandomizedL20_4Conditioned
import Cogentic.RandomizedL19SecondMoment

/-!
# L20.4 top: `TopG12Comparison` from the explicit additive comparison,
and the depth-form reduction of the C5 top step

`Cogentic.RandomizedL20_4` states the KeyBreak G.12 top square-root comparison as
the `Prop`

`TopG12Comparison top Ctop interior epsIn eta` :
`top ≤ Ctop * (√(interior 0) + √(epsIn) + eta)`,

and `Cogentic.RandomizedL20_4Conditioned` proves its linear-majorant consequence
`topG12LinearComparison_of_comparison` and the one-constant additive reduction
`topG12Comparison_of_additive`.

This file does three things.

## 1. `TopG12Comparison` from the explicit additive comparison

The G.54--G.55 Cauchy--Schwarz step produces **three separate terms with three
separate polynomial constants**: the internal square root, the incoming
square root and the elliptic deletion fraction.  Forcing them to share one
constant is a loss.  `TopG12AdditiveThreeComparison` keeps the three constants
`Cint`, `Cin`, `Cell` explicit; `topG12Comparison_of_additiveThree` proves
`TopG12Comparison` as soon as each is eventually dominated by `Ctop` and the
elliptic fraction is nonnegative.  No term is dropped and no constant is set to
one.  `topG12Comparison_iff_additiveThree` records that with a common constant
`Ctop` the two forms are literally equivalent, so the additive form is the
smallest explicit rendering of the G.12 analytic content.

## 2. The depth form at the G.11 base level

The right-hand side of `TopG12Comparison` still contains `interior 0`, a
*derived* quantity.  The G.11 recurrence
(`internal_linear_recurrence_bound`) bounds it by the explicit majorant
`step^L * (δ_L + L(η + ε_rat))`.  Two explicit base-level forms are isolated:

* `TopG12AdditiveDepthComparison` — additive terms at the depth majorant
  `step^L * (δ_L + L(η + ε_rat))`;
* `TopG12AdditiveExactComparison` — additive terms at the sharp geometric
  majorant `step^L * δ_L + (∑_{i<L} step^{i+1}) * (η + ε_rat)`, which avoids
  the extra factor `L` and needs only `0 ≤ step`.

`topG12LinearComparison_of_additiveDepth` (and its exact counterpart, via
`exactMajorant_le_depthMajorant`) factor these into the shape consumed by
`G12TopInputs.top_bound`.

**Direction.**  The recurrence gives `δ₀ ≤ majorant`, hence
`√δ₀ ≤ √majorant`: the depth form has the *larger* right-hand side and is
therefore **weaker** than `TopG12Comparison`.  It cannot reprove
`TopG12Comparison` (that would need the reverse inequality).  What it does give
is the reverse implication `topG12AdditiveDepth_of_comparison`: the depth form
is an exact consequence of the comparison, and — as the consumer reduction below
shows — it is already strong enough for the C5 top conclusion.  So the depth
form is an explicit input strictly weaker than `TopG12Comparison` that still
yields `SubexpLoss top`, which is the paper's actual G.12 output.

## 3. The consumer reduction

`top_subexp_of_additiveDepth` redoes the `G12TopInputs.top_subexp` argument with
`TopG12Comparison` replaced by `TopG12AdditiveDepthComparison`: the G.11
majorant is itself `D^{-B}` (`majorant_le_exp_neg`), and `top_le_exp_neg`
concludes.  `TopG12AdditiveData` packages this as a bundle whose `comparison`
field is the explicit additive depth form instead of the derived-`δ₀` form.
`TopG12ThreeData` packages the three-constant additive form of §1 and *does*
realize `G12TopInputs` (hence `TopG12Comparison` is derived, not assumed).

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss: every constant,
depth factor and exponent stays explicit, and no term is replaced by `0`.
-/

namespace Cogentic.RandomizedL20_4Top

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned

/-! ## 1. The additive comparison with three explicit constants -/

/-- The G.54--G.55 additive comparison at the derived level `δ₀`, with the
internal, incoming and elliptic terms carrying their own explicit polynomial
constants `Cint`, `Cin`, `Cell`.  This is the literal three-term output of the
two Cauchy--Schwarz steps. -/
def TopG12AdditiveThreeComparison (top Cint Cin Cell : ℕ → ℝ)
    (interior : ℕ → ℕ → ℝ) (epsIn eta : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    top n ≤ Cint n * Real.sqrt (interior n 0) +
      Cin n * Real.sqrt (epsIn n) + Cell n * eta n

/-- **`TopG12Comparison` from the explicit three-term additive comparison.**
Each of the three constants is eventually dominated by `Ctop`, and the elliptic
fraction is nonnegative (it is a deletion fraction).  The three terms are summed
with no cancellation and no discarded factor. -/
theorem topG12Comparison_of_additiveThree {top Ctop Cint Cin Cell : ℕ → ℝ}
    {interior : ℕ → ℕ → ℝ} {epsIn eta : ℕ → ℝ}
    (h : TopG12AdditiveThreeComparison top Cint Cin Cell interior epsIn eta)
    (hInt : ∀ᶠ n : ℕ in atTop, Cint n ≤ Ctop n)
    (hIn : ∀ᶠ n : ℕ in atTop, Cin n ≤ Ctop n)
    (hEll : ∀ᶠ n : ℕ in atTop, Cell n ≤ Ctop n)
    (hη : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n) :
    TopG12Comparison top Ctop interior epsIn eta := by
  filter_upwards [h, hInt, hIn, hEll, hη] with n hn hInt' hIn' hEll' hη'
  have h1 : Cint n * Real.sqrt (interior n 0) ≤
      Ctop n * Real.sqrt (interior n 0) :=
    mul_le_mul_of_nonneg_right hInt' (Real.sqrt_nonneg _)
  have h2 : Cin n * Real.sqrt (epsIn n) ≤ Ctop n * Real.sqrt (epsIn n) :=
    mul_le_mul_of_nonneg_right hIn' (Real.sqrt_nonneg _)
  have h3 : Cell n * eta n ≤ Ctop n * eta n :=
    mul_le_mul_of_nonneg_right hEll' hη'
  have hsum : Cint n * Real.sqrt (interior n 0) + Cin n * Real.sqrt (epsIn n) +
        Cell n * eta n ≤
      Ctop n * Real.sqrt (interior n 0) + Ctop n * Real.sqrt (epsIn n) +
        Ctop n * eta n :=
    add_le_add (add_le_add h1 h2) h3
  have hgoal : Ctop n * (Real.sqrt (interior n 0) + Real.sqrt (epsIn n) + eta n) =
      Ctop n * Real.sqrt (interior n 0) + Ctop n * Real.sqrt (epsIn n) +
        Ctop n * eta n := by ring
  rw [hgoal]
  exact hn.trans hsum

/-- With a common constant `Ctop` in all three terms, the additive comparison is
**exactly** `TopG12Comparison`: the two are related by distributivity alone, so
no sign hypothesis is needed.  Hence the additive form loses nothing and is the
smallest explicit rendering of the G.12 analytic content. -/
theorem topG12Comparison_iff_additiveThree {top Ctop : ℕ → ℝ}
    {interior : ℕ → ℕ → ℝ} {epsIn eta : ℕ → ℝ} :
    TopG12AdditiveThreeComparison top Ctop Ctop Ctop interior epsIn eta ↔
      TopG12Comparison top Ctop interior epsIn eta := by
  constructor
  · intro h
    filter_upwards [h] with n hn
    have hgoal : Ctop n * (Real.sqrt (interior n 0) + Real.sqrt (epsIn n) + eta n) =
        Ctop n * Real.sqrt (interior n 0) + Ctop n * Real.sqrt (epsIn n) +
          Ctop n * eta n := by ring
    rw [hgoal]
    exact hn
  · intro hcmp
    filter_upwards [hcmp] with n hn
    have hgoal : Ctop n * (Real.sqrt (interior n 0) + Real.sqrt (epsIn n) + eta n) =
        Ctop n * Real.sqrt (interior n 0) + Ctop n * Real.sqrt (epsIn n) +
          Ctop n * eta n := by ring
    rw [← hgoal]
    exact hn

/-! ## 2. The additive comparison at the explicit G.11 depth majorant -/

/-- The G.12 additive comparison evaluated at the explicit G.11 depth majorant
`step^L * (δ_L + L(η + ε_rat))` instead of at the derived level `δ₀`.  It
mentions only the base mass `δ_L`, the step, the two error fractions and the
depth `L`. -/
def TopG12AdditiveDepthComparison (top Ctop : ℕ → ℝ) (interior : ℕ → ℕ → ℝ)
    (step eta epsRat epsIn : ℕ → ℝ) (L : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    top n ≤ Ctop n *
        Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) +
      Ctop n * Real.sqrt (epsIn n) + Ctop n * eta n

/-- The G.12 additive comparison at the sharp geometric G.11 majorant
`step^L * δ_L + (∑_{i<L} step^{i+1}) * (η + ε_rat)`.  Same explicit input as
`TopG12AdditiveDepthComparison` but without the extra `L` factor. -/
def TopG12AdditiveExactComparison (top Ctop : ℕ → ℝ) (interior : ℕ → ℕ → ℝ)
    (step eta epsRat epsIn : ℕ → ℝ) (L : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    top n ≤ Ctop n *
        Real.sqrt (step n ^ L * interior n L +
          (∑ i ∈ Finset.range L, step n ^ (i + 1)) * (eta n + epsRat n)) +
      Ctop n * Real.sqrt (epsIn n) + Ctop n * eta n

/-- The depth form factors into the linear majorant form consumed by
`G12TopInputs.top_bound`.  Only distributivity is used. -/
theorem topG12LinearComparison_of_additiveDepth {top Ctop : ℕ → ℝ}
    {interior : ℕ → ℕ → ℝ} {step eta epsRat epsIn : ℕ → ℝ} {L : ℕ}
    (h : TopG12AdditiveDepthComparison top Ctop interior step eta epsRat epsIn L) :
    TopG12LinearComparison top Ctop interior step eta epsRat epsIn L := by
  filter_upwards [h] with n hn
  calc top n ≤ Ctop n *
        Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) +
        Ctop n * Real.sqrt (epsIn n) + Ctop n * eta n := hn
    _ = Ctop n *
        (Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) +
          Real.sqrt (epsIn n) + eta n) := by ring

/-- The sharp geometric majorant is at most the depth majorant
`step^L * (δ_L + L(η + ε_rat))`: each of the `L` propagated error terms is
charged `step^L`, so `∑_{i<L} step^{i+1} ≤ L * step^L` for `step ≥ 1`.  This is
the scalar inequality inside `internal_linear_recurrence_bound`, recorded
separately. -/
theorem exactMajorant_le_depthMajorant {C η ε δL : ℝ} {L : ℕ}
    (hC : 1 ≤ C) (hα : 0 ≤ η + ε) :
    C ^ L * δL + (∑ i ∈ Finset.range L, C ^ (i + 1)) * (η + ε) ≤
      C ^ L * (δL + (L : ℝ) * (η + ε)) := by
  have hsum : ∑ i ∈ Finset.range L, C ^ (i + 1) ≤ (L : ℝ) * C ^ L := by
    calc ∑ i ∈ Finset.range L, C ^ (i + 1) ≤ ∑ _i ∈ Finset.range L, C ^ L := by
          apply Finset.sum_le_sum
          intro i hi
          exact pow_le_pow_right₀ hC (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      _ = (L : ℝ) * C ^ L := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmul : (∑ i ∈ Finset.range L, C ^ (i + 1)) * (η + ε) ≤
      ((L : ℝ) * C ^ L) * (η + ε) :=
    mul_le_mul_of_nonneg_right hsum hα
  have hgoal : C ^ L * (δL + (L : ℝ) * (η + ε)) =
      C ^ L * δL + (C ^ L * (L : ℝ)) * (η + ε) := by ring
  rw [hgoal]
  have hmul' : (∑ i ∈ Finset.range L, C ^ (i + 1)) * (η + ε) ≤
      (C ^ L * (L : ℝ)) * (η + ε) := by
    refine hmul.trans (le_of_eq ?_)
    ring
  linarith [hmul']

/-- The sharp additive form implies the depth additive form (monotone square
root applied to `exactMajorant_le_depthMajorant`). -/
theorem topG12AdditiveDepth_of_additiveExact {top Ctop : ℕ → ℝ}
    {interior : ℕ → ℕ → ℝ} {step eta epsRat epsIn : ℕ → ℝ} {L : ℕ}
    (h : TopG12AdditiveExactComparison top Ctop interior step eta epsRat epsIn L)
    (hstep : ∀ᶠ n : ℕ in atTop, 1 ≤ step n)
    (hα : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n)
    (hCtop : ∀ᶠ n : ℕ in atTop, 0 ≤ Ctop n) :
    TopG12AdditiveDepthComparison top Ctop interior step eta epsRat epsIn L := by
  filter_upwards [h, hstep, hα, hCtop] with n hn hstep' hα' hCtop'
  have hmaj : step n ^ L * interior n L +
        (∑ i ∈ Finset.range L, step n ^ (i + 1)) * (eta n + epsRat n) ≤
      step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n)) :=
    exactMajorant_le_depthMajorant hstep' hα'
  have hsqrt : Real.sqrt (step n ^ L * interior n L +
        (∑ i ∈ Finset.range L, step n ^ (i + 1)) * (eta n + epsRat n)) ≤
      Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) :=
    Real.sqrt_le_sqrt hmaj
  have hkey : Ctop n * Real.sqrt (step n ^ L * interior n L +
        (∑ i ∈ Finset.range L, step n ^ (i + 1)) * (eta n + epsRat n)) ≤
      Ctop n * Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) :=
    mul_le_mul_of_nonneg_left hsqrt hCtop'
  exact hn.trans (add_le_add (add_le_add hkey le_rfl) le_rfl)

/-- The exact form factors into the linear majorant form. -/
theorem topG12LinearComparison_of_additiveExact {top Ctop : ℕ → ℝ}
    {interior : ℕ → ℕ → ℝ} {step eta epsRat epsIn : ℕ → ℝ} {L : ℕ}
    (h : TopG12AdditiveExactComparison top Ctop interior step eta epsRat epsIn L)
    (hstep : ∀ᶠ n : ℕ in atTop, 1 ≤ step n)
    (hα : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n)
    (hCtop : ∀ᶠ n : ℕ in atTop, 0 ≤ Ctop n) :
    TopG12LinearComparison top Ctop interior step eta epsRat epsIn L :=
  topG12LinearComparison_of_additiveDepth
    (topG12AdditiveDepth_of_additiveExact h hstep hα hCtop)

/-! ## 3. The depth form is a consequence of `TopG12Comparison` -/

/-- **The comparison implies the depth form.**  The G.11 recurrence bounds `δ₀`
by the depth majorant, so the larger-right-hand-side depth form follows from
`TopG12Comparison` with no loss of constant.  (The converse is false in general:
the depth form has the larger right-hand side and is strictly weaker.) -/
theorem topG12AdditiveDepth_of_comparison {top Ctop : ℕ → ℝ}
    {interior : ℕ → ℕ → ℝ} {step eta epsRat epsIn : ℕ → ℝ} {L : ℕ}
    (hcmp : TopG12Comparison top Ctop interior epsIn eta)
    (hrec : G11InteriorRecurrence interior L step eta epsRat)
    (hstep : ∀ᶠ n : ℕ in atTop, 1 ≤ step n)
    (hα : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n)
    (hCtop : ∀ᶠ n : ℕ in atTop, 0 ≤ Ctop n) :
    TopG12AdditiveDepthComparison top Ctop interior step eta epsRat epsIn L := by
  filter_upwards [hcmp, hrec, hstep, hα, hCtop] with n hcmp' hrec' hstep' hα' hCtop'
  have hint : interior n 0 ≤
      step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n)) :=
    internal_linear_recurrence_bound (interior n) L hstep' hα' hrec'
  have hsqrt : Real.sqrt (interior n 0) ≤
      Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) :=
    Real.sqrt_le_sqrt hint
  have hkey : Ctop n * Real.sqrt (interior n 0) ≤
      Ctop n * Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) :=
    mul_le_mul_of_nonneg_left hsqrt hCtop'
  have hcmp'' : top n ≤
      Ctop n * Real.sqrt (interior n 0) + Ctop n * Real.sqrt (epsIn n) +
        Ctop n * eta n := by
    refine hcmp'.trans (le_of_eq ?_)
    ring
  exact hcmp''.trans (add_le_add (add_le_add hkey le_rfl) le_rfl)

/-! ## 4. The G.11 depth majorant is itself `D^{-B}` -/

/-- **The depth majorant is subexponential.**  A subexponential base mass
`δ_L ≤ exp (-A H)`, subexponential errors `η + ε_rat ≤ exp (-A H)`, a depth
factor `step^L ≤ exp (c_int H)` and `(L+1) ≤ exp H` give
`step^L (δ_L + L(η+ε_rat)) ≤ exp (-T H)` as soon as `T + c_int + 1 ≤ A`.  This
is the `hinner`--`h5` computation of `interior_zero_le_exp`, isolated. -/
theorem majorant_le_exp_neg {L : ℕ} {δ : ℕ → ℝ} {Cstep η ε T cInt A H : ℝ}
    (heta : 0 ≤ η) (heps : 0 ≤ ε) (hC : 1 ≤ Cstep) (hH : 0 ≤ H)
    (hL : (L : ℝ) + 1 ≤ Real.exp H)
    (hstep : Cstep ^ L ≤ Real.exp (cInt * H))
    (hbase : δ L ≤ Real.exp (-A * H))
    (halpha : η + ε ≤ Real.exp (-A * H))
    (hA : T + cInt + 1 ≤ A) :
    Cstep ^ L * (δ L + (L : ℝ) * (η + ε)) ≤ Real.exp (-T * H) := by
  have hα : 0 ≤ η + ε := add_nonneg heta heps
  have hE : 0 ≤ Real.exp (-A * H) := (Real.exp_pos _).le
  have hinner : δ L + (L : ℝ) * (η + ε) ≤ ((L : ℝ) + 1) * Real.exp (-A * H) := by
    have h1 : (L : ℝ) * (η + ε) ≤ (L : ℝ) * Real.exp (-A * H) :=
      mul_le_mul_of_nonneg_left halpha (Nat.cast_nonneg L)
    have h2 : δ L + (L : ℝ) * (η + ε) ≤
        Real.exp (-A * H) + (L : ℝ) * Real.exp (-A * H) := add_le_add hbase h1
    have h3 : Real.exp (-A * H) + (L : ℝ) * Real.exp (-A * H) =
        ((L : ℝ) + 1) * Real.exp (-A * H) := by ring
    linarith
  have hstepnn : 0 ≤ Cstep ^ L := pow_nonneg (by linarith) L
  have h4 : Cstep ^ L * (δ L + (L : ℝ) * (η + ε)) ≤
      Cstep ^ L * (((L : ℝ) + 1) * Real.exp (-A * H)) :=
    mul_le_mul_of_nonneg_left hinner hstepnn
  have hLE : ((L : ℝ) + 1) * Real.exp (-A * H) ≤ Real.exp H * Real.exp (-A * H) :=
    mul_le_mul_of_nonneg_right hL hE
  have h5 : Cstep ^ L * (((L : ℝ) + 1) * Real.exp (-A * H)) ≤
      Real.exp (cInt * H) * (Real.exp H * Real.exp (-A * H)) :=
    mul_le_mul hstep hLE (by positivity) (Real.exp_pos _).le
  have h6 : Real.exp (cInt * H) * (Real.exp H * Real.exp (-A * H)) =
      Real.exp ((cInt + 1 - A) * H) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h7 : Real.exp ((cInt + 1 - A) * H) ≤ Real.exp (-T * H) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hA, hH]
  exact h4.trans (h5.trans (h6.trans_le h7))

/-! ## 5. The C5 top conclusion from the depth form -/

/-- **The G.12 top mass is `D^{-B}` for every `B`, from the additive depth
comparison.**  This is `top_subexp_of_concentration` with `TopG12Comparison`
replaced by `TopG12AdditiveDepthComparison`: the depth majorant is bounded by
`exp (-2 (B + c_top + 1) H)` via `majorant_le_exp_neg`, and `top_le_exp_neg`
finishes.  The constants `Ctop`, `cTop`, `cInt` and the depth `L` stay explicit.
-/
theorem top_subexp_of_additiveDepth {L : ℕ} (interior : ℕ → ℕ → ℝ)
    (step eta epsRat epsIn top Ctop : ℕ → ℝ) (cTop cInt : ℝ)
    (interior_nonneg : ∀ n i, 0 ≤ interior n i)
    (eta_nonneg : ∀ n, 0 ≤ eta n)
    (epsRat_nonneg : ∀ n, 0 ≤ epsRat n)
    (epsIn_nonneg : ∀ n, 0 ≤ epsIn n)
    (_top_nonneg : ∀ n, 0 ≤ top n)
    (_Ctop_nonneg : ∀ n, 0 ≤ Ctop n)
    (cTop_nonneg : 0 ≤ cTop)
    (recurrence : G11InteriorRecurrence interior L step eta epsRat)
    (step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n)
    (alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n)
    (depth_bound : ∀ᶠ n : ℕ in atTop,
      step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n))
    (additive : TopG12AdditiveDepthComparison top Ctop interior step eta epsRat epsIn L)
    (Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n))
    (base_subexp : SubexpLoss fun n => interior n L)
    (eta_subexp : SubexpLoss eta)
    (epsRat_subexp : SubexpLoss epsRat)
    (epsIn_subexp : SubexpLoss epsIn) :
    SubexpLoss top := by
  intro B hB
  let T : ℝ := 2 * (B + cTop + 1)
  have hTpos : 0 < T := by dsimp [T]; nlinarith [hB, cTop_nonneg]
  let A : ℝ := max (T + cInt + 1) 1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hAT : T + cInt + 1 ≤ A := le_max_left _ _
  have hcpos : 0 < B + cTop + 1 := by linarith [hB, cTop_nonneg]
  filter_upwards [step_ge_one, alpha_nonneg, recurrence, additive,
    Ctop_le, depth_bound, base_subexp A hApos,
    subexpLoss_add eta_subexp epsRat_subexp A hApos,
    eta_subexp (B + cTop + 1) hcpos, epsIn_subexp T hTpos,
    scale_grows.eventually_ge_atTop 0,
    scale_grows.eventually_ge_atTop
      (max (Real.log 3) (Real.log ((L : ℝ) + 1) + 1))]
    with n hstep hα hrec hadd hC hdepth hbase halpha heta hin hH0 hHbig
  have hH : 0 ≤ scale n := hH0
  have hH3 : Real.log 3 ≤ scale n := le_trans (le_max_left _ _) hHbig
  have hHL : (L : ℝ) + 1 ≤ Real.exp (scale n) := by
    have hlog : Real.log ((L : ℝ) + 1) ≤ scale n := by
      have hle : Real.log ((L : ℝ) + 1) + 1 ≤
          max (Real.log 3) (Real.log ((L : ℝ) + 1) + 1) := le_max_right _ _
      linarith
    calc (L : ℝ) + 1 = Real.exp (Real.log ((L : ℝ) + 1)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (scale n) := Real.exp_le_exp.mpr hlog
  have hstepL : step n ^ L ≤ Real.exp (cInt * scale n) := by
    have hfac : step n ^ L ≤ step n ^ L * ((L : ℝ) + 1) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      have h1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith
      nlinarith [pow_nonneg (show 0 ≤ step n by linarith) L]
    exact hfac.trans hdepth
  have hmaj : step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n)) ≤
      Real.exp (-T * scale n) :=
    majorant_le_exp_neg (δ := interior n) (Cstep := step n) (η := eta n)
      (ε := epsRat n) (T := T) (cInt := cInt) (A := A) (H := scale n)
      (eta_nonneg n) (epsRat_nonneg n) hstep hH hHL hstepL hbase halpha hAT
  have hsqrt : Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) ≤
      Real.exp (-(B + cTop + 1) * scale n) := by
    have hsq : step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n)) ≤
        (Real.exp (-(B + cTop + 1) * scale n)) ^ 2 := by
      refine hmaj.trans (le_of_eq ?_)
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n)))
        ≤ Real.sqrt ((Real.exp (-(B + cTop + 1) * scale n)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.exp (-(B + cTop + 1) * scale n) := Real.sqrt_sq (Real.exp_pos _).le
  have hint_nn : 0 ≤ step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n)) :=
    mul_nonneg (pow_nonneg (by linarith) L)
      (add_nonneg (interior_nonneg n L)
        (mul_nonneg (Nat.cast_nonneg L) (add_nonneg (eta_nonneg n) (epsRat_nonneg n))))
  have htop : top n ≤ Ctop n *
      (Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) +
        Real.sqrt (epsIn n) + eta n) := by
    refine hadd.trans (le_of_eq ?_)
    ring
  exact top_le_exp_neg (δtop := top n) (C := Ctop n)
    (intMass := step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n)))
    (inMass := epsIn n) (eta := eta n) (B := B) (cTop := cTop) (H := scale n)
    hB hH hH3 hint_nn (epsIn_nonneg n) (eta_nonneg n) hC
    (by simpa [T] using hmaj) (by simpa [T] using hin) heta htop

/-! ## 6. The consumable bundles -/

/-- The G.12 top data with the `comparison` field replaced by the explicit
additive comparison at the G.11 depth majorant.  This is strictly weaker than
`TopG12Comparison` yet still yields `SubexpLoss top`; the derived `δ₀` value
never appears. -/
structure TopG12AdditiveData where
  /-- Depth of the internal G.11 recurrence. -/
  L : ℕ
  /-- Internal normalized bad-child masses `δ_i`, `i = 0 … L`. -/
  interior : ℕ → ℕ → ℝ
  /-- G.11 step multiplier. -/
  step : ℕ → ℝ
  /-- Elliptic deletion fraction `η` (L21.2). -/
  eta : ℕ → ℝ
  /-- G.11 rational error `ε_rat`. -/
  epsRat : ℕ → ℝ
  /-- Incoming exceptional mass. -/
  epsIn : ℕ → ℝ
  /-- Resulting top bad-child mass `δ_top`. -/
  top : ℕ → ℝ
  /-- The G.12 top constant. -/
  Ctop : ℕ → ℝ
  /-- Exponent of the top constant. -/
  cTop : ℝ
  /-- Exponent of the depth factor. -/
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  epsRat_nonneg : ∀ n, 0 ≤ epsRat n
  epsIn_nonneg : ∀ n, 0 ≤ epsIn n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  recurrence : G11InteriorRecurrence interior L step eta epsRat
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  /-- The additive G.12 comparison at the explicit G.11 depth majorant. -/
  additive_comparison : TopG12AdditiveDepthComparison top Ctop interior step eta epsRat epsIn L
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)
  base_subexp : SubexpLoss fun n => interior n L
  eta_subexp : SubexpLoss eta
  epsRat_subexp : SubexpLoss epsRat
  epsIn_subexp : SubexpLoss epsIn

namespace TopG12AdditiveData

/-- The depth form gives the linear majorant form consumed by
`G12TopInputs.top_bound`. -/
theorem linearComparison (S : TopG12AdditiveData) :
    TopG12LinearComparison S.top S.Ctop S.interior S.step S.eta S.epsRat S.epsIn S.L :=
  topG12LinearComparison_of_additiveDepth S.additive_comparison

/-- The four explicit interior fields assemble `InteriorSubProps`. -/
theorem interiorConcentration (S : TopG12AdditiveData) :
    InteriorSubProps S.interior S.L S.eta S.epsRat S.epsIn where
  base_subexp := S.base_subexp
  eta_subexp := S.eta_subexp
  epsRat_subexp := S.epsRat_subexp
  epsIn_subexp := S.epsIn_subexp

/-- **The G.12 top mass is subexponential** from the additive depth comparison. -/
theorem top_subexp (S : TopG12AdditiveData) : SubexpLoss S.top :=
  top_subexp_of_additiveDepth S.interior S.step S.eta S.epsRat S.epsIn S.top S.Ctop
    S.cTop S.cInt S.interior_nonneg S.eta_nonneg S.epsRat_nonneg S.epsIn_nonneg
    S.top_nonneg S.Ctop_nonneg S.cTop_nonneg S.recurrence S.step_ge_one
    S.alpha_nonneg S.depth_bound S.additive_comparison S.Ctop_le S.base_subexp
    S.eta_subexp S.epsRat_subexp S.epsIn_subexp

end TopG12AdditiveData

/-- The G.12 top data with the `comparison` field replaced by the explicit
three-constant additive comparison at `δ₀`.  Here `TopG12Comparison` is a
*derived* theorem (`comparison`), so the bundle realizes `G12TopInputs`. -/
structure TopG12ThreeData where
  L : ℕ
  interior : ℕ → ℕ → ℝ
  step : ℕ → ℝ
  eta : ℕ → ℝ
  epsRat : ℕ → ℝ
  epsIn : ℕ → ℝ
  top : ℕ → ℝ
  Ctop : ℕ → ℝ
  cTop : ℝ
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  epsRat_nonneg : ∀ n, 0 ≤ epsRat n
  epsIn_nonneg : ∀ n, 0 ≤ epsIn n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  recurrence : G11InteriorRecurrence interior L step eta epsRat
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  /-- The explicit three-constant additive comparison at `δ₀`. -/
  additive_comparison :
    TopG12AdditiveThreeComparison top Ctop Ctop Ctop interior epsIn eta
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)
  base_subexp : SubexpLoss fun n => interior n L
  eta_subexp : SubexpLoss eta
  epsRat_subexp : SubexpLoss epsRat
  epsIn_subexp : SubexpLoss epsIn

namespace TopG12ThreeData

/-- **`TopG12Comparison` proved from the explicit additive comparison** (the
`comparison` field is derived, not assumed). -/
theorem comparison (S : TopG12ThreeData) :
    TopG12Comparison S.top S.Ctop S.interior S.epsIn S.eta :=
  topG12Comparison_of_additiveThree S.additive_comparison
    (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall S.eta_nonneg)

/-- The bundle realizes `G12TopInputs` with the derived comparison. -/
noncomputable def toG12TopInputs (S : TopG12ThreeData) : G12TopInputs where
  L := S.L
  interior := S.interior
  step := S.step
  eta := S.eta
  epsRat := S.epsRat
  epsIn := S.epsIn
  top := S.top
  Ctop := S.Ctop
  cTop := S.cTop
  cInt := S.cInt
  interior_nonneg := S.interior_nonneg
  eta_nonneg := S.eta_nonneg
  epsRat_nonneg := S.epsRat_nonneg
  epsIn_nonneg := S.epsIn_nonneg
  top_nonneg := S.top_nonneg
  Ctop_nonneg := S.Ctop_nonneg
  cTop_nonneg := S.cTop_nonneg
  recurrence := S.recurrence
  step_ge_one := S.step_ge_one
  alpha_nonneg := S.alpha_nonneg
  depth_bound := S.depth_bound
  comparison := S.comparison
  Ctop_le := S.Ctop_le
  base_subexp := S.base_subexp
  eta_subexp := S.eta_subexp
  epsRat_subexp := S.epsRat_subexp
  epsIn_subexp := S.epsIn_subexp

/-- The G.12 top mass is subexponential. -/
theorem top_subexp (S : TopG12ThreeData) : SubexpLoss S.top :=
  S.toG12TopInputs.top_subexp

end TopG12ThreeData

/-! ## Axiom audit -/

#print axioms topG12Comparison_of_additiveThree
#print axioms topG12Comparison_iff_additiveThree
#print axioms topG12LinearComparison_of_additiveDepth
#print axioms exactMajorant_le_depthMajorant
#print axioms topG12AdditiveDepth_of_additiveExact
#print axioms topG12LinearComparison_of_additiveExact
#print axioms topG12AdditiveDepth_of_comparison
#print axioms majorant_le_exp_neg
#print axioms top_subexp_of_additiveDepth
#print axioms TopG12AdditiveData.linearComparison
#print axioms TopG12AdditiveData.interiorConcentration
#print axioms TopG12AdditiveData.top_subexp
#print axioms TopG12ThreeData.comparison
#print axioms TopG12ThreeData.toG12TopInputs
#print axioms TopG12ThreeData.top_subexp

end Cogentic.RandomizedL20_4Top
