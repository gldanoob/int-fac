import Cogentic.RandomizedL27Waterhouse
import Cogentic.RandomizedL27Fiber
import Cogentic.RandomizedL27KillLaw

/-!
# L27 Hasse: the point-count bound for the concrete curve models

The L27.1 development states Hasse's theorem as the abstract predicate

`HasseBound p orderCount : ∀ n j, orderCount n j ≠ 0 →
  |(j : ℝ) - ((p n : ℝ) + 1)| ≤ 2 * Real.sqrt (p n)`

in `Cogentic.RandomizedL27_1`.  This file connects that predicate to the two
concrete curve-count models already built in the tree:

* the raw isomorphism-class model of `Cogentic.RandomizedL27Waterhouse`
  (`CurveModel`, `curvePointCount`, `rawCurveOrderCount`);
* the actual affine `j`-line model of `Cogentic.RandomizedL27Fiber`
  (`CurveOver`, `curveOrder`, `curveOrderCount`).

## What Mathlib supplies

At the pinned Mathlib revision there is **no** Hasse bound for elliptic curves
over finite fields.  Mathlib has the affine group law
`WeierstrassCurve.Affine.Point`, its cardinality, and the discriminant, but no
Frobenius trace theorem and no estimate on `Nat.card (Affine.Point E)`.  The
exact missing theorem is therefore exposed here, not hidden:

* `PointCountHasse p` — for every nonsingular Weierstrass equation over
  `ZMod p`, `|curvePointCount - (p + 1)| ≤ 2√p`;
* `CurveOrderHasse p` — the same statement for Mathlib's point group
  `Affine.Point`, i.e. `|Nat.card (Affine.Point E) - (p + 1)| ≤ 2√p`.

The two forms are proved equivalent (`pointCountHasse_iff_curveOrderHasse`),
using the concrete bridge
`curvePointCount = Nat.card (Affine.Point ·)`.  From either form we prove
`HasseBound` for `rawCurveOrderCount` and for any finite `curveOrderCount`
model.  These are the only unproved inputs of this file.

## Hasse is stronger than the L27 derivation needs

The actual L27.1 reduction never uses the numerical Hasse interval.  Its only
mathematical use of `HasseBound` is the positivity of stage-one-smooth orders
(`smooth_order_pos_of_two_le`); the upper endpoint additionally gives the
support statement `orderCount n j ≠ 0 → j ≤ orderTop n`, used by the interface
lemmas `orderCount_eq_zero_of_orderTop_lt` and `smooth_order_le_orderTop`.
Both are consequences of the weaker counting statement `HasseSupport`:

`(∀ n j, orderCount n j ≠ 0 → 0 < j) ∧
   ∀ n j, orderCount n j ≠ 0 → j ≤ orderTop n`.

We prove:

* `HasseBound` implies `HasseSupport` for `p ≥ 2` and the integer endpoint
  `orderTop` (`hasseSupport_of_hasseBound`);
* `HasseSupport` gives the two interface lemmas (`..._of_support`);
* the actual fiber model supplies `HasseSupport` **without any Hasse input**,
  from `curveOrder_pos` and the order bound stored in `ActualFiberInput`
  (`hasseSupport_of_actualFiberInput`);
* the stage-one bundles `L27GCDModelInputs` and `L27KillLawInputs` can be built
  from `HasseSupport` instead of from `smooth_order_pos_of_two_le`
  (`gcdModelInputsOfSupport`, `killLawInputsOfSupport`);
* the full L27.1 ledger and manuscript rates are rederived from
  `DeuringLenstraCounts`, the stage-one success law, the curve budget, and the
  log-factor input, with **no** `HasseBound` and no `EllipticCurveGroupLaw`
  (`reduced_ledger_of_stage`, `reduced_paper_of_stage`), and then from
  `HasseSupport` alone (`reduced_ledger_of_support`, `reduced_paper_of_support`)
  or from `ActualFiberInput` alone (`reduced_ledger_of_actualFiberInput`).

A counterexample (`hasseSupport_not_implies_hasseBound`) shows that this
weakening is strict: support can hold while the Hasse interval fails.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no curve count is
set to zero.
-/

namespace Cogentic.RandomizedL27Hasse

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27GcdModel
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27StageOne
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL27Fiber
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open WeierstrassCurve

noncomputable section

set_option linter.style.haveILetI false

/-! ## 1. The exact residual: Hasse's theorem on the concrete models -/

/-- **Hasse's theorem on the affine point count.**  For every nonsingular
Weierstrass equation over `F_p`, the number of projective points lies in the
Hasse interval.  This is the classical theorem; it is not available in the
pinned Mathlib and is the sole geometric residual of the concrete model. -/
def PointCountHasse (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ W : CurveModel p,
    |(curvePointCount p W : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)

/-- The prime-indexed family form of `PointCountHasse`. -/
def PointCountHasseFamily (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime) : Prop :=
  ∀ n, @PointCountHasse (p n) ⟨hp n⟩

/-- **Hasse's theorem on Mathlib's point group.**  For every elliptic curve over
`F_p`, `#E(F_p) = Nat.card (Affine.Point E)` lies in the Hasse interval.  This
is the same classical theorem, stated on the group used by `curveOrder`. -/
def CurveOrderHasse (p : ℕ) : Prop :=
  ∀ E : CurveOver p,
    |(curveOrder E : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)

/-- The prime-indexed family form of `CurveOrderHasse`. -/
def CurveOrderHasseFamily (p : ℕ → ℕ) : Prop := ∀ n, CurveOrderHasse (p n)

/-! ## 2. The point-count bridge -/

/-- Adjoining a zero adds one to `Nat.card`. -/
theorem natCard_withZero {α : Type*} [Fintype α] :
    Nat.card (WithZero α) = Nat.card α + 1 := by
  letI : Fintype (WithZero α) := inferInstanceAs (Fintype (Option α))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_option

/-- The concrete affine point count is the cardinality of Mathlib's nonsingular
point group.  The affine solutions of a nonsingular Weierstrass equation are
exactly the nonsingular affine points, and the point at infinity contributes
the `+ 1`. -/
theorem curvePointCount_eq_natCard {p : ℕ} [Fact p.Prime] [NeZero p]
    (W : CurveModel p) :
    curvePointCount p W = Nat.card (WeierstrassCurve.Affine.Point W.1) := by
  letI : Fintype (ZMod p) := ZMod.fintype p
  have hE : W.1.IsElliptic := (curveNonsingular_iff_isElliptic p W.1).mp W.2
  have hns : ∀ q : ZMod p × ZMod p, W.1.toAffine.Equation q.1 q.2 ↔
      W.1.toAffine.Nonsingular q.1 q.2 :=
    fun q => WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := W.1.toAffine) (x := q.1) (y := q.2)
  haveI : Fintype {q : ZMod p × ZMod p // W.1.toAffine.Nonsingular q.1 q.2} :=
    Fintype.ofEquiv {q : ZMod p × ZMod p // W.1.toAffine.Equation q.1 q.2}
      (Equiv.subtypeEquivRight hns)
  have hcard : (Finset.univ.filter (fun q : ZMod p × ZMod p =>
        W.1.toAffine.Equation q.1 q.2)).card
      = Nat.card {q : ZMod p × ZMod p // W.1.toAffine.Equation q.1 q.2} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    curvePointCount p W = (Finset.univ.filter (fun q : ZMod p × ZMod p =>
          W.1.toAffine.Equation q.1 q.2)).card + 1 := rfl
    _ = Nat.card {q : ZMod p × ZMod p // W.1.toAffine.Equation q.1 q.2} + 1 := by
          rw [hcard]
    _ = Nat.card {q : ZMod p × ZMod p // W.1.toAffine.Nonsingular q.1 q.2} + 1 := by
          rw [Nat.card_congr (Equiv.subtypeEquivRight hns)]
    _ = Nat.card (WithZero {q : ZMod p × ZMod p //
          W.1.toAffine.Nonsingular q.1 q.2}) := by
          rw [natCard_withZero]
    _ = Nat.card (WeierstrassCurve.Affine.Point W.1) := by
          exact (Nat.card_congr
            (WeierstrassCurve.Affine.nonsingularPointEquiv W.1.toAffine)).symm

/-- The affine point count of a `CurveOver` equals its `curveOrder`. -/
theorem curvePointCount_eq_curveOrder {p : ℕ} [Fact p.Prime] [NeZero p]
    (E : CurveOver p) :
    curvePointCount p
        ⟨E.1, (curveNonsingular_iff_isElliptic p E.1).mpr E.2⟩ = curveOrder E :=
  curvePointCount_eq_natCard _

/-- The `CurveModel` version of `curvePointCount_eq_curveOrder`, phrased without
changing the representative. -/
theorem curvePointCount_eq_curveOrder_model {p : ℕ} [Fact p.Prime] [NeZero p]
    (W : CurveModel p) :
    curvePointCount p W =
      curveOrder ⟨W.1, (curveNonsingular_iff_isElliptic p W.1).mp W.2⟩ :=
  curvePointCount_eq_natCard W

/-- The two concrete forms of Hasse's theorem are equivalent. -/
theorem pointCountHasse_iff_curveOrderHasse (p : ℕ) [Fact p.Prime] [NeZero p] :
    PointCountHasse p ↔ CurveOrderHasse p := by
  constructor
  · intro h E
    have hh := h ⟨E.1, (curveNonsingular_iff_isElliptic p E.1).mpr E.2⟩
    rwa [curvePointCount_eq_curveOrder E] at hh
  · intro h W
    have hh := h ⟨W.1, (curveNonsingular_iff_isElliptic p W.1).mp W.2⟩
    simpa [curvePointCount_eq_curveOrder_model W] using hh

/-! ## 3. Reduction to `HasseBound` for the concrete counts -/

/-- **From the point-count Hasse theorem to `HasseBound` for the raw
isomorphism-class count.**  A nonzero raw class count means that some class has
exactly `j` points, and its representative satisfies the Hasse interval. -/
theorem hasseBound_of_pointCountHasse {p : ℕ → ℕ} (hp : ∀ n, (p n).Prime)
    (h : PointCountHasseFamily p hp) :
    HasseBound p (rawCurveOrderCount p hp) := by
  intro n j hne
  letI : Fact (p n).Prime := ⟨hp n⟩
  have hraw : rawCurveCount (p n) j ≠ 0 := by
    simpa [rawCurveOrderCount, rawCurveCountAt] using hne
  obtain ⟨E, hE⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hraw)
  have hclass : classHasPointCount (p n) E j := (Finset.mem_filter.mp hE).2
  obtain ⟨W, -, hWj⟩ := hclass
  have hW := h n W
  rwa [hWj] at hW

/-- **From the point-group Hasse theorem to `HasseBound` for a finite fiber
model.**  A nonzero `curveOrderCount` means that some curve in the finite set
has order `j`. -/
theorem hasseBound_of_curveOrderHasse {p : ℕ → ℕ} (h : CurveOrderHasseFamily p)
    (curves : ∀ n, Finset (CurveOver (p n))) :
    HasseBound p (fun n j => curveOrderCount (curves n) j) := by
  intro n j hne
  obtain ⟨E, hE⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  have hEq : curveOrder E = j := (Finset.mem_filter.mp hE).2
  rw [← hEq]
  exact h n E

/-- The point-count form directly gives `HasseBound` for a finite fiber model,
using the point-count bridge. -/
theorem hasseBound_curveOrderCount_of_pointCountHasse {p : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime) (h : PointCountHasseFamily p hp)
    [hne : ∀ n, NeZero (p n)]
    (curves : ∀ n, Finset (CurveOver (p n))) :
    HasseBound p (fun n j => curveOrderCount (curves n) j) := by
  apply hasseBound_of_curveOrderHasse
  intro n
  letI : Fact (p n).Prime := ⟨hp n⟩
  letI : NeZero (p n) := hne n
  exact (pointCountHasse_iff_curveOrderHasse (p n)).mp (h n)

/-! ## 4. The weaker counting statement actually used by L27 -/

/-- **The support form of Hasse.**  Every realised order is positive and lies
below the integer endpoint `orderTop`.  This retains exactly the two facts used
by the L27.1 derivation: positivity of smooth orders and the support of the
finite sums over `Finset.range (orderTop + 1)`. -/
def HasseSupport (orderCount : ℕ → ℕ → ℕ) (orderTop : ℕ → ℕ) : Prop :=
  (∀ n j, orderCount n j ≠ 0 → 0 < j) ∧
    ∀ n j, orderCount n j ≠ 0 → j ≤ orderTop n

/-- Strict AM–GM at `p ≥ 2`: `2√p < p + 1`. -/
theorem two_mul_sqrt_lt_add_one_of_two_le {p : ℕ} (hp : 2 ≤ p) :
    2 * Real.sqrt (p : ℝ) < (p : ℝ) + 1 := by
  have hp1 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
    Real.mul_self_sqrt hp1.le
  have hsqrt_ne_one : Real.sqrt (p : ℝ) ≠ 1 := by
    intro h
    have hp_eq : (p : ℝ) = 1 := by rw [← hsq, h]; norm_num
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpos : 0 < (Real.sqrt (p : ℝ) - 1) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hsqrt_ne_one)
  nlinarith

/-- `HasseBound` plus the integer endpoint implies `HasseSupport` for `p ≥ 2`.
The lower endpoint gives positivity (strictly, since `2√p < p + 1`), and the
upper endpoint gives `j ≤ orderTop`. -/
theorem hasseSupport_of_hasseBound {p : ℕ → ℕ} {orderCount : ℕ → ℕ → ℕ}
    {orderTop : ℕ → ℕ} (hhasse : HasseBound p orderCount)
    (hp2 : ∀ n, 2 ≤ p n)
    (htop : ∀ n, (p n : ℝ) + 1 + 2 * Real.sqrt (p n) ≤ (orderTop n : ℝ)) :
    HasseSupport orderCount orderTop := by
  constructor
  · intro n j hne
    have hlow := hasse_lower (hhasse n j hne)
    have hstrict := two_mul_sqrt_lt_add_one_of_two_le (hp2 n)
    have hpos : (0 : ℝ) < (p n : ℝ) + 1 - 2 * Real.sqrt (p n) := by linarith
    have hjR : (0 : ℝ) < (j : ℝ) := by linarith
    exact_mod_cast hjR
  · intro n j hne
    exact hasse_order_le_orderTop (hhasse n j hne) (htop n)

/-- Support replaces the upper Hasse endpoint in the `zero-above-`orderTop`
interface lemma. -/
theorem orderCount_eq_zero_of_orderTop_lt_of_support {orderCount : ℕ → ℕ → ℕ}
    {orderTop : ℕ → ℕ} (hsupp : HasseSupport orderCount orderTop) {n j : ℕ}
    (hj : orderTop n < j) : orderCount n j = 0 := by
  by_contra hne
  have hle := hsupp.2 n j hne
  omega

/-- Support replaces the upper Hasse endpoint in the smooth-order window
lemma. -/
theorem smooth_order_le_orderTop_of_support {orderCount : ℕ → ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {orderTop : ℕ → ℕ}
    (hsupp : HasseSupport orderCount orderTop)
    (hreal : ∀ n j, smooth n j = true → orderCount n j ≠ 0)
    {n j : ℕ} (hs : smooth n j = true) : j ≤ orderTop n :=
  hsupp.2 n j (hreal n j hs)

/-- Support replaces the lower Hasse endpoint in the positivity of smooth
orders. -/
theorem smooth_order_pos_of_support {orderCount : ℕ → ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {orderTop : ℕ → ℕ}
    (hsupp : HasseSupport orderCount orderTop)
    (hreal : ∀ n j, smooth n j = true → orderCount n j ≠ 0)
    {n j : ℕ} (hs : smooth n j = true) : 0 < j :=
  hsupp.1 n j (hreal n j hs)

/-- **The actual fiber model supplies `HasseSupport` with no Hasse input.**
`curveOrder` is positive because every curve contains the point at infinity, and
the order top is already part of the finite fiber data. -/
theorem hasseSupport_curveOrderCount {p : ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hp : ∀ n, 0 < p n)
    (curves : ∀ n, Finset (CurveOver (p n)))
    (hbound : ∀ n (E : CurveOver (p n)), E ∈ curves n → curveOrder E ≤ orderTop n) :
    HasseSupport (fun n j => curveOrderCount (curves n) j) orderTop := by
  constructor
  · intro n j hne
    letI : NeZero (p n) := ⟨Nat.pos_iff_ne_zero.mp (hp n)⟩
    obtain ⟨E, hE⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    have hEq : curveOrder E = j := (Finset.mem_filter.mp hE).2
    rw [← hEq]
    exact curveOrder_pos E
  · intro n j hne
    obtain ⟨E, hE⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    have hEq : curveOrder E = j := (Finset.mem_filter.mp hE).2
    have hmem : E ∈ curves n := (Finset.mem_filter.mp hE).1
    rw [← hEq]
    exact hbound n E hmem

/-- **`ActualFiberInput` supplies `HasseSupport`.**  The twist-fiber count is
irrelevant here; only the order bound and `curveOrder_pos` are used. -/
theorem hasseSupport_of_actualFiberInput {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ} (hp : ∀ n, 0 < p n)
    (h : ActualFiberInput p orderCount orderTop) :
    HasseSupport orderCount orderTop := by
  constructor
  · intro n j hne
    obtain ⟨curves, hcount, _, _⟩ := h n
    have hne' : curveOrderCount curves j ≠ 0 := by
      rw [curveOrderCount, ← hcount j]
      exact hne
    letI : NeZero (p n) := ⟨Nat.pos_iff_ne_zero.mp (hp n)⟩
    obtain ⟨E, hE⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne')
    have hEq : curveOrder E = j := (Finset.mem_filter.mp hE).2
    rw [← hEq]
    exact curveOrder_pos E
  · intro n j hne
    obtain ⟨curves, hcount, hbound, _⟩ := h n
    have hne' : curveOrderCount curves j ≠ 0 := by
      rw [curveOrderCount, ← hcount j]
      exact hne
    obtain ⟨E, hE⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne')
    have hEq : curveOrder E = j := (Finset.mem_filter.mp hE).2
    have hmem : E ∈ curves := (Finset.mem_filter.mp hE).1
    rw [← hEq]
    exact hbound E hmem

/-- **The weakening is strict.**  A supported order count need not satisfy the
Hasse interval: for `p = 2`, the single order `6` is positive and below the top
`6`, but `|6 - 3| = 3 > 2√2`. -/
theorem hasseSupport_not_implies_hasseBound :
    ∃ (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ) (orderTop : ℕ → ℕ),
      HasseSupport orderCount orderTop ∧ ¬ HasseBound p orderCount := by
  refine ⟨fun _ => 2, fun _ j => if j = 6 then 1 else 0, fun _ => 6, ?_, ?_⟩
  · constructor
    · intro n j hne
      by_cases h : j = 6
      · subst j
        norm_num
      · simp [h] at hne
    · intro n j hne
      by_cases h : j = 6
      · subst j
        norm_num
      · simp [h] at hne
  · intro h
    have h6 := h 0 6 (by simp)
    norm_num at h6
    have hbad : ¬ (3 ≤ 2 * Real.sqrt (2 : ℝ)) := by
      have hs : Real.sqrt (2 : ℝ) < 3 / 2 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      nlinarith
    exact hbad h6

/-! ## 5. Building the stage-one bundles from support alone -/

/-- The pointwise gcd/kill stage-one bundle with positivity supplied by
`HasseSupport` rather than Hasse's theorem. -/
noncomputable def gcdModelInputsOfSupport (I : L27_1Inputs)
    (hsupp : HasseSupport I.orderCount I.orderTop)
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (pointKill : ℕ → ℕ → ℕ)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : ∀ n j, I.smooth n j = true →
      (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n))
    (hcutoff : StageOneCutoffExpOne I.y) : L27GCDModelInputs I where
  gcdFail_eq := hgf
  noFactorData := D
  pointKill := pointKill
  smooth_order_pos := fun n j hs => hsupp.1 n j (I.smooth_realized n j hs)
  success_ge_killed := hsuccess
  point_fraction := hkill
  cutoff := hcutoff

/-- The finite-sum kill-law bundle with positivity supplied by `HasseSupport`. -/
noncomputable def killLawInputsOfSupport (I : L27_1Inputs)
    (hsupp : HasseSupport I.orderCount I.orderTop)
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (pointKill : ℕ → ℕ → ℕ)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : KillMassLaw I pointKill)
    (hcutoff : StageOneCutoffExpOne I.y) : L27KillLawInputs I where
  gcdFail_eq := hgf
  noFactorData := D
  pointKill := pointKill
  smooth_order_pos := fun n j hs => hsupp.1 n j (I.smooth_realized n j hs)
  success_ge_killed := hsuccess
  kill_mass := hkill
  cutoff := hcutoff

/-! ## 6. The L27.1 reduction without `HasseBound` -/

/-- The per-curve success lower bound from the Deuring counts and the stage-one
success law alone. -/
theorem cRate_mul_density_le_success_of_stage {I : L27_1Inputs}
    (h : DeuringLenstraCounts I)
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) (n : ℕ) :
    I.cRate * I.D n ≤ I.success n := by
  have hp : (0 : ℝ) < (I.p n : ℝ) := by exact_mod_cast I.p_pos n
  have hSF : I.SF n / Real.log (I.y n) ≤ I.success n := by
    simpa [L27_1Inputs.SF, L27_1Inputs.SC, L27_1Inputs.CT, smoothFraction]
      using hstage n
  simpa [L27_1Inputs.cRate, L27_1Inputs.D, density] using
    cRate_density_le_of_fraction (κ := I.κ) (psi := I.psi n) (p := (I.p n : ℝ))
      (y := I.y n) (SF := I.SF n) (success := I.success n)
      hp (I.y_gt_one n) (smoothFraction_lower_of I h n) hSF

/-- The joint failure bound from the Deuring counts and the stage-one success
law alone. -/
theorem splitFail_le_exp_of_stage (I : L27_1Inputs)
    (h : DeuringLenstraCounts I)
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) (n : ℕ) :
    I.splitFail n ≤ Real.exp (-(I.cRate * I.rate n)) := by
  have hd1 : I.cRate * I.D n ≤ 1 :=
    (cRate_mul_density_le_success_of_stage (I := I) h hstage n).trans
      (I.success_le_one n)
  have hs : I.cRate * I.D n ≤ I.success n :=
    cRate_mul_density_le_success_of_stage (I := I) h hstage n
  have hjoint : (1 - I.success n) ^ I.curves n ≤
      Real.exp (-(((I.curves n : ℝ)) * (I.cRate * I.D n))) :=
    joint_failure_le_exp hd1 hs (I.success_le_one n)
  have hexp : Real.exp (-(((I.curves n : ℝ)) * (I.cRate * I.D n))) =
      Real.exp (-(I.cRate * I.rate n)) := by
    congr 1
    unfold L27_1Inputs.rate L27_1Inputs.D density
    ring
  calc
    I.splitFail n = (1 - I.success n) ^ I.curves n := I.independence n
    _ ≤ Real.exp (-(((I.curves n : ℝ)) * (I.cRate * I.D n))) := hjoint
    _ = Real.exp (-(I.cRate * I.rate n)) := hexp

/-- The joint failure is nonnegative. -/
theorem splitFail_nonneg_of_stage (I : L27_1Inputs) (n : ℕ) : 0 ≤ I.splitFail n := by
  unfold L27_1Inputs.splitFail
  rw [I.independence n]
  refine pow_nonneg ?_ _
  have h := I.success_le_one n
  linarith

/-- **The L27.1 ledger without `HasseBound`.**  The only elliptic input is the
stage-one success law. -/
theorem reduced_ledger_of_stage (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I)
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  filter_upwards [hbudget, hlog (I.η / 2) (by linarith [I.η_pos]),
    scale_grows.eventually_ge_atTop 0] with n hb hl hs
  have hbudget' : (2 + I.η) * scale n ≤ I.cRate * I.rate n := by
    simpa [L27_1Inputs.cRate, L27_1Inputs.rate, L27_1Inputs.D, density] using hb
  have hfail := splitFail_le_exp_of_stage I hdeuring hstage n
  have h := loss_le_exp_of_budget (H := scale n) (E := I.cRate * I.rate n)
    (L := ((I.cofactor n).log2 : ℝ)) (fail := I.splitFail n) (η := I.η)
    hs I.η_pos hbudget' (splitFail_nonneg_of_stage I n) hl hfail
  simpa [L27_1Inputs.loss] using h

/-- **The L27.1 manuscript rate without `HasseBound`.** -/
theorem reduced_paper_of_stage (I : L27_1Inputs)
    (hdeuring : DeuringLenstraCounts I)
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) := by
  filter_upwards [hbudget, hlog (I.η / 2) (by linarith [I.η_pos]),
    scale_grows.eventually_ge_atTop 0] with n hb hl hs
  have hbudget' : (2 + I.η) * scale n ≤ I.cRate * I.rate n := by
    simpa [L27_1Inputs.cRate, L27_1Inputs.rate, L27_1Inputs.D, density] using hb
  have hfail := splitFail_le_exp_of_stage I hdeuring hstage n
  have h := loss_le_exp_half_of_budget (H := scale n) (E := I.cRate * I.rate n)
    (L := ((I.cofactor n).log2 : ℝ)) (fail := I.splitFail n) (η := I.η)
    hs hbudget' (splitFail_nonneg_of_stage I n) hl hfail
  have hgoal : Real.exp (-((I.cRate * I.rate n) / 2)) =
      Real.exp (-((I.cRate / 2) * I.rate n)) := by
    congr 1
    ring
  simpa [L27_1Inputs.loss, hgoal] using h

/-- **The L27.1 ledger from `HasseSupport` alone.**  This is the capstone of
the weakening: no `HasseBound` and no `EllipticCurveGroupLaw` are used. -/
theorem reduced_ledger_of_support (I : L27_1Inputs)
    (hsupp : HasseSupport I.orderCount I.orderTop)
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (pointKill : ℕ → ℕ → ℕ)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : ∀ n j, I.smooth n j = true →
      (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n))
    (hcutoff : StageOneCutoffExpOne I.y)
    (hdeuring : DeuringLenstraCounts I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  have S : L27GCDModelInputs I :=
    gcdModelInputsOfSupport I hsupp hgf D pointKill hsuccess hkill hcutoff
  exact reduced_ledger_of_stage I hdeuring
    S.toStageOneInputs.stageOneSuccess hbudget hlog

/-- **The L27.1 manuscript rate from `HasseSupport` alone.** -/
theorem reduced_paper_of_support (I : L27_1Inputs)
    (hsupp : HasseSupport I.orderCount I.orderTop)
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (pointKill : ℕ → ℕ → ℕ)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : ∀ n j, I.smooth n j = true →
      (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n))
    (hcutoff : StageOneCutoffExpOne I.y)
    (hdeuring : DeuringLenstraCounts I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) := by
  have S : L27GCDModelInputs I :=
    gcdModelInputsOfSupport I hsupp hgf D pointKill hsuccess hkill hcutoff
  exact reduced_paper_of_stage I hdeuring
    S.toStageOneInputs.stageOneSuccess hbudget hlog

/-- **The L27.1 ledger from the actual fiber model, without Hasse.**  The
`ActualFiberInput` already stores the order bound and the twist-fiber count; no
point-count theorem is needed. -/
theorem reduced_ledger_of_actualFiberInput (I : L27_1Inputs)
    (hp : ∀ n, 0 < I.p n)
    (hcurves : ActualFiberInput I.p I.orderCount I.orderTop)
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (pointKill : ℕ → ℕ → ℕ)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : ∀ n j, I.smooth n j = true →
      (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n))
    (hcutoff : StageOneCutoffExpOne I.y)
    (hdeuring : DeuringLenstraCounts I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  reduced_ledger_of_support I
    (hasseSupport_of_actualFiberInput hp hcurves)
    hgf D pointKill hsuccess hkill hcutoff hdeuring hbudget hlog

/-- **The L27.1 manuscript rate from the actual fiber model, without Hasse.** -/
theorem reduced_paper_of_actualFiberInput (I : L27_1Inputs)
    (hp : ∀ n, 0 < I.p n)
    (hcurves : ActualFiberInput I.p I.orderCount I.orderTop)
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (pointKill : ℕ → ℕ → ℕ)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : ∀ n j, I.smooth n j = true →
      (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n))
    (hcutoff : StageOneCutoffExpOne I.y)
    (hdeuring : DeuringLenstraCounts I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  reduced_paper_of_support I
    (hasseSupport_of_actualFiberInput hp hcurves)
    hgf D pointKill hsuccess hkill hcutoff hdeuring hbudget hlog

/-! ## Axiom audit -/

#print axioms natCard_withZero
#print axioms curvePointCount_eq_natCard
#print axioms curvePointCount_eq_curveOrder
#print axioms pointCountHasse_iff_curveOrderHasse
#print axioms hasseBound_of_pointCountHasse
#print axioms hasseBound_of_curveOrderHasse
#print axioms hasseBound_curveOrderCount_of_pointCountHasse
#print axioms two_mul_sqrt_lt_add_one_of_two_le
#print axioms hasseSupport_of_hasseBound
#print axioms orderCount_eq_zero_of_orderTop_lt_of_support
#print axioms smooth_order_le_orderTop_of_support
#print axioms smooth_order_pos_of_support
#print axioms hasseSupport_curveOrderCount
#print axioms hasseSupport_of_actualFiberInput
#print axioms hasseSupport_not_implies_hasseBound
#print axioms gcdModelInputsOfSupport
#print axioms killLawInputsOfSupport
#print axioms cRate_mul_density_le_success_of_stage
#print axioms splitFail_le_exp_of_stage
#print axioms reduced_ledger_of_stage
#print axioms reduced_paper_of_stage
#print axioms reduced_ledger_of_support
#print axioms reduced_paper_of_support
#print axioms reduced_ledger_of_actualFiberInput
#print axioms reduced_paper_of_actualFiberInput

end

end Cogentic.RandomizedL27Hasse
