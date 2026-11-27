import Cogentic.RandomizedL27Stratification
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# L27 fibers of the actual `j`-line over `F_p`

`Cogentic.RandomizedL27Stratification` isolates `JLineFiberInput` as the smallest
combinatorial input behind the `≤ 4p` Hasse-window curve total.  The present file
connects that input to the actual elliptic curves over `F_p`.

## The curve model

For a modulus `p` (a prime in the application), write

* `CurveOver p` for the elliptic Weierstrass curves over `ZMod p`;
* `curveJ E` for the `j`-invariant of `E`, regarded as a natural number in
  `[0, p)` (the affine `j`-invariant of an elliptic curve lies in `F_p`; the
  stratum at infinity is never realized);
* `curveOrder E` for the order `#E(F_p)` of the curve.

The actual `j`-line cardinality bound is then **automatic**: the image of `curveJ`
on any finite set of curves is contained in `Finset.range p`, so it has at most
`p` elements (`curveJ_image_card_le`).  This is the `p` (not `p + 1`) of
`JLineCardBound`.

## The remaining finite count

The only geometric input retained explicitly is the twist-fiber count: at most
two curve classes over every `j ≠ 0, 1728`, and at most six over the exceptional
values `0` and `1728`.  The exceptional values are taken in `ZMod p` and then
transported to `ℕ` by `ZMod.val`, so the statement is correct for every modulus,
including the small characteristics in which `1728 = 0`.

`ActualTwistFiberBound` records exactly this finite count for a set of curve-class
representatives.  `jLineFiberInput_of_actualFiberInput` proves that it, together
with the order-fiber description of `orderCount`, yields `JLineFiberInput`.
No `j`-cardinality hypothesis is needed.

The consequences for the sharp `2p + 8` total, the paper's `4p` total, and the
bundled Deuring/Lenstra ledger are recorded at the end.

No `sorry`, `admit`, `axiom`, or `native_decide`; no count is set to zero.
-/

namespace Cogentic.RandomizedL27Fiber

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Stratification
open Cogentic.RandomizedOneThirdAsymptotic
open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

/-! ## 1. The actual elliptic curves and their `j`-invariants -/

/-- An elliptic Weierstrass curve over `ZMod p`, i.e. an actual elliptic curve
over `F_p` when `p` is prime.  A `Finset` of these is intended to contain one
representative of each `F_p`-isomorphism class in the Hasse window. -/
abbrev CurveOver (p : ℕ) : Type :=
  { W : WeierstrassCurve (ZMod p) // W.IsElliptic }

/-- The `j`-invariant of an actual curve, as a natural number in `[0, p)`.
The value is the representative in `Finset.range p` of the field element `j`. -/
def curveJ {p : ℕ} (E : CurveOver p) : ℕ :=
  letI : E.1.IsElliptic := E.2
  (E.1.j).val

/-- The order `#E(F_p)` of an actual curve. -/
def curveOrder {p : ℕ} (E : CurveOver p) : ℕ :=
  Nat.card (Affine.Point E.1)

/-- The points of an elliptic curve over a positive modulus form a finite type.
This makes `curveOrder` the genuine cardinality `#E(F_p)`, not a default value. -/
instance fintypePoint {p : ℕ} [NeZero p] (E : CurveOver p) : Fintype (Affine.Point E.1) := by
  haveI : Fintype (ZMod p) := ZMod.fintype p
  let e := WeierstrassCurve.Affine.nonsingularPointEquiv E.1
  let f : Affine.Point E.1 → Option (ZMod p × ZMod p) := fun P =>
    Option.map (fun x : { xy : ZMod p × ZMod p // Affine.Nonsingular E.1 xy.1 xy.2 } =>
      (x.1.1, x.1.2)) (e P)
  have hval : Function.Injective
      (fun x : { xy : ZMod p × ZMod p // Affine.Nonsingular E.1 xy.1 xy.2 } =>
        (x.1.1, x.1.2)) := by
    intro x y hxy
    exact Subtype.ext (Prod.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  have hf : Function.Injective f := by
    intro P Q hPQ
    apply e.injective
    exact Option.map_injective hval hPQ
  exact Fintype.ofInjective f hf

/-- The order of an actual curve is the cardinality of its point type. -/
theorem curveOrder_eq_card {p : ℕ} [NeZero p] (E : CurveOver p) :
    curveOrder E = Fintype.card (Affine.Point E.1) := by
  unfold curveOrder
  rw [Nat.card_eq_fintype_card]

/-- Every actual curve has at least the point at infinity, so its order is
positive.  In particular the model never assigns the order `0`. -/
theorem curveOrder_pos {p : ℕ} [NeZero p] (E : CurveOver p) : 0 < curveOrder E := by
  rw [curveOrder_eq_card]
  exact Fintype.card_pos_iff.mpr ⟨Affine.Point.zero⟩

/-- The `j`-invariant of an actual curve lies in `[0, p)`. -/
theorem curveJ_lt {p : ℕ} (hp : 0 < p) (E : CurveOver p) : curveJ E < p := by
  unfold curveJ
  exact @ZMod.val_lt p ⟨hp.ne'⟩ _

/-- **The actual `j`-line cardinality.**  Any finite set of elliptic curves over
`F_p` realizes at most `p` distinct `j`-invariants, because `curveJ` takes values
in `F_p = {0, …, p - 1}`.  This discharges `JLineCardBound` without a geometric
hypothesis. -/
theorem curveJ_image_card_le {p : ℕ} (hp : 0 < p) (curves : Finset (CurveOver p)) :
    (curves.image curveJ).card ≤ p := by
  calc
    (curves.image curveJ).card ≤ (Finset.range p).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨E, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (curveJ_lt hp E)
    _ = p := Finset.card_range p

/-! ## 2. The twist-fiber finite count -/

/-- The two exceptional `j`-invariants `0` and `1728`, transported to `ℕ` by the
canonical representative of `ZMod p`.  In characteristics `2` and `3` these two
values coincide, so the set has at most two elements in every case. -/
def exceptionalJ (p : ℕ) : Finset ℕ :=
  {0, (1728 : ZMod p).val}

/-- The exceptional set has at most two elements. -/
theorem exceptionalJ_card_le_two (p : ℕ) : (exceptionalJ p).card ≤ 2 := by
  unfold exceptionalJ
  simpa using Finset.card_le_two (a := 0) (b := (1728 : ZMod p).val)

/-- **The twist-fiber finite count for actual curves.**  For a set of
curve-class representatives over `F_p`, every non-exceptional `j`-fiber has at
most two classes, and the fibers over the exceptional values `0` and `1728` have
at most six.  This is the only remaining mathematical input in the reduction;
it is the standard quadratic-twist/automorphism count. -/
def ActualTwistFiberBound {p : ℕ} (curves : Finset (CurveOver p)) : Prop :=
  (∀ x : ℕ, x ∉ exceptionalJ p →
      (curves.filter fun E => curveJ E = x).card ≤ 2) ∧
    ∀ x : ℕ, x ∈ exceptionalJ p →
      (curves.filter fun E => curveJ E = x).card ≤ 6

/-- **The actual twist count gives the abstract twist-fiber bound.**  The
exception set is the intersection of the realized `j`-values with
`{0, 1728}`; it is contained in the image by construction and has at most two
elements.  This is the exact passage from the finite count to `TwistFiberBound`
used in `JLineFiberInput`. -/
theorem twistFiberBound_of_actual {q : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ} {n : ℕ}
    (curves : Finset (CurveOver (q n))) (order : CurveOver (q n) → ℕ)
    (hcount : ∀ j, orderCount n j =
      (curves.filter fun E => order E = j).card)
    (hbound : ∀ E ∈ curves, order E ≤ orderTop n)
    (htwist : ActualTwistFiberBound curves) :
    TwistFiberBound
      (JLinePartition.ofOrderFiber curves order curveJ orderTop n hcount hbound) := by
  refine ⟨curves.image curveJ ∩ exceptionalJ (q n), ?_, ?_, ?_, ?_⟩
  · exact Finset.inter_subset_left
  · exact (Finset.card_le_card Finset.inter_subset_right).trans
      (exceptionalJ_card_le_two (q n))
  · intro x hximage hxnot
    have hxnotexc : x ∉ exceptionalJ (q n) := by
      intro hx
      exact hxnot (Finset.mem_inter.mpr ⟨hximage, hx⟩)
    change (curves.filter fun E => curveJ E = x).card ≤ 2
    exact htwist.1 x hxnotexc
  · intro x hx
    have hxexc : x ∈ exceptionalJ (q n) := (Finset.mem_inter.mp hx).2
    change (curves.filter fun E => curveJ E = x).card ≤ 6
    exact htwist.2 x hxexc

/-- **The actual `j`-cardinality bound gives `JLineCardBound`.**  This is the
same passage as `curveJ_image_card_le`, stated for the partition built from the
order fibers. -/
theorem jLineCardBound_of_curves {q : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ} {n : ℕ}
    (hp : 0 < q n)
    (curves : Finset (CurveOver (q n))) (order : CurveOver (q n) → ℕ)
    (hcount : ∀ j, orderCount n j =
      (curves.filter fun E => order E = j).card)
    (hbound : ∀ E ∈ curves, order E ≤ orderTop n) :
    JLineCardBound q
      (JLinePartition.ofOrderFiber curves order curveJ orderTop n hcount hbound) := by
  change (curves.image curveJ).card ≤ q n
  exact curveJ_image_card_le hp curves

/-! ## 3. The reduction to the actual curve counts -/

/-- **The actual finite curve data behind `JLineFiberInput`.**  For every index
`n`, a finite set of elliptic-curve representatives over `F_p` whose order
fibers are `orderCount n`, whose orders lie in the Hasse window up to
`orderTop n`, and whose twist fibers obey the at most two/at most six count.

Only the order-fiber identity, the order bound, and `ActualTwistFiberBound` are
inputs.  In particular the `j`-line cardinality is not an input. -/
def ActualFiberInput (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) : Prop :=
  ∀ n, ∃ curves : Finset (CurveOver (p n)),
    (∀ j, orderCount n j =
      (curves.filter fun E => curveOrder E = j).card) ∧
    (∀ E ∈ curves, curveOrder E ≤ orderTop n) ∧
    ActualTwistFiberBound curves

/-- The order-fiber count of a finite set of actual curves: `curveOrderCount p
curves j` is the number of curve classes of order exactly `j`. -/
def curveOrderCount {p : ℕ} (curves : Finset (CurveOver p)) (j : ℕ) : ℕ :=
  (curves.filter fun E => curveOrder E = j).card

/-- **The `j`-fiber partition gives the sharp finite count `2 #j + 8`.**  This
is the combinatorial heart of the `2p + 8` bound, stated directly on an actual
set of curve classes: summing the twist-fiber cardinalities over the realized
`j`-invariants and using at most six at the at most two exceptional values
gives `#curves ≤ 2 #(image curveJ) + 8`. -/
theorem card_le_two_mul_jImageCard_add_eight {p : ℕ}
    (curves : Finset (CurveOver p)) (htwist : ActualTwistFiberBound curves) :
    (curves.card : ℝ) ≤ 2 * ((curves.image curveJ).card : ℝ) + 8 := by
  let strata := curves.image curveJ
  let exc := strata ∩ exceptionalJ p
  let m : ℕ → ℕ := fun x => (curves.filter fun E => curveJ E = x).card
  have hsub : exc ⊆ strata := Finset.inter_subset_left
  have hexc : exc.card ≤ 2 :=
    (Finset.card_le_card Finset.inter_subset_right).trans
      (exceptionalJ_card_le_two p)
  have hm : ∀ x ∈ strata, x ∉ exc → m x ≤ 2 := by
    intro x _ hxnot
    have hxnotexc : x ∉ exceptionalJ p := by
      intro hx
      exact hxnot (Finset.mem_inter.mpr ⟨by assumption, hx⟩)
    exact htwist.1 x hxnotexc
  have hme : ∀ x ∈ exc, m x ≤ 6 := by
    intro x hx
    exact htwist.2 x (Finset.mem_inter.mp hx).2
  have hsum : curves.card = ∑ x ∈ strata, m x := by
    simpa [strata, m] using Finset.card_eq_sum_card_image curveJ curves
  have hbound := sum_multiplicity_le_two_mul_add_eight strata exc m strata.card
    le_rfl hsub hexc hm hme
  rw [hsum, Nat.cast_sum]
  exact hbound

/-- **The actual curve count is at most `2p + 8`.**  Combining the finite `j`-line
count `#j ≤ p` with the twist-fiber bound gives the sharp total for the actual
elliptic curve classes over `F_p`. -/
theorem card_le_two_mul_add_eight {p : ℕ} (hp : 0 < p)
    (curves : Finset (CurveOver p)) (htwist : ActualTwistFiberBound curves) :
    (curves.card : ℝ) ≤ 2 * (p : ℝ) + 8 := by
  have h1 := card_le_two_mul_jImageCard_add_eight curves htwist
  have h2 : ((curves.image curveJ).card : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast curveJ_image_card_le hp curves
  linarith

/-- **`JLineFiberInput` from the actual elliptic curves over `F_p`.**  The
`j`-line cardinality is automatic from `curveJ : CurveOver p → {0, …, p - 1}`;
the only remaining input is the explicit twist-fiber count. -/
theorem jLineFiberInput_of_actualFiberInput {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hp : ∀ n, 0 < p n) (h : ActualFiberInput p orderCount orderTop) :
    JLineFiberInput p orderCount orderTop := by
  intro n
  obtain ⟨curves, hcount, hbound, htwist⟩ := h n
  exact ⟨JLinePartition.ofOrderFiber curves curveOrder curveJ orderTop n hcount hbound,
    jLineCardBound_of_curves (hp n) curves curveOrder hcount hbound,
    twistFiberBound_of_actual curves curveOrder hcount hbound htwist⟩

/-- **`JLineFiberInput` for the actual order-fiber counts.**  This version does
not assume that a separately given `orderCount` agrees with the curve set: the
`orderCount` is *defined* as the number of actual curves of each order.  Only
the Hasse-window bound and the twist-fiber count remain as hypotheses. -/
theorem jLineFiberInput_of_curveOrderCount {p : ℕ → ℕ}
    {orderTop : ℕ → ℕ}
    (hp : ∀ n, 0 < p n)
    (curves : ∀ n, Finset (CurveOver (p n)))
    (hbound : ∀ n (E : CurveOver (p n)), E ∈ curves n → curveOrder E ≤ orderTop n)
    (htwist : ∀ n, ActualTwistFiberBound (curves n)) :
    JLineFiberInput p (fun n j => curveOrderCount (curves n) j) orderTop := by
  apply jLineFiberInput_of_actualFiberInput hp
  intro n
  exact ⟨curves n, fun _ => rfl, hbound n, htwist n⟩

/-- **The sharp `2p + 8` total from the actual curve counts.** -/
theorem jInvariantCurveTotal_of_actualFiberInput {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hp : ∀ n, 0 < p n) (h : ActualFiberInput p orderCount orderTop) :
    JInvariantCurveTotal p orderCount orderTop :=
  jInvariantCurveTotal_of_fiberInput (jLineFiberInput_of_actualFiberInput hp h)

/-- **The paper's `≤ 4p` total from the actual curve counts.** -/
theorem hasseWindowCurveTotal_of_actualFiberInput {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hp : ∀ n, 0 < p n) (hp4 : ∀ n, 4 ≤ p n)
    (h : ActualFiberInput p orderCount orderTop) :
    HasseWindowCurveTotal p orderCount orderTop :=
  hasseWindowCurveTotal_of_fiberInput
    (jLineFiberInput_of_actualFiberInput hp h) hp4

/-! ## 4. The bundled Deuring/Lenstra consequences -/

/-- **`DeuringLenstraCounts` from actual curve classes over `F_p`.**  The Hurwitz
weight, the Deuring trace formula, the Hurwitz lower bound, and the small-prime
prepass are unchanged; the `j`-line field is now supplied by
`ActualFiberInput`. -/
theorem deuringLenstraCounts_of_actualFiberInput {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ)
    (htrace : DeuringTraceFormula I.p I.smooth I.orderCount hurwitz)
    (hlower : HurwitzClassLower I.p I.smooth hurwitz I.κ)
    (hcurves : ActualFiberInput I.p I.orderCount I.orderTop)
    (hp : ∀ n, 4 ≤ I.p n) :
    DeuringLenstraCounts I :=
  deuringLenstraCounts_of_fiberInput hurwitz htrace hlower
    (jLineFiberInput_of_actualFiberInput I.p_pos hcurves) hp

/-- **The full L27.1 capstone from actual curve classes over `F_p`.** -/
theorem reduction_of_actualFiberInput {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ)
    (htrace : DeuringTraceFormula I.p I.smooth I.orderCount hurwitz)
    (hlower : HurwitzClassLower I.p I.smooth hurwitz I.κ)
    (hcurves : ActualFiberInput I.p I.orderCount I.orderTop)
    (hp : ∀ n, 4 ≤ I.p n)
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
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  reduction_of_fiberInput hurwitz htrace hlower
    (jLineFiberInput_of_actualFiberInput I.p_pos hcurves) hp
    hhasse h0 h1 h2 hstage hbudget hlog

/-! ## Axiom audit -/

#print axioms curveOrder_eq_card
#print axioms curveOrder_pos
#print axioms curveJ_lt
#print axioms curveJ_image_card_le
#print axioms exceptionalJ_card_le_two
#print axioms jLineCardBound_of_curves
#print axioms twistFiberBound_of_actual
#print axioms card_le_two_mul_jImageCard_add_eight
#print axioms card_le_two_mul_add_eight
#print axioms jLineFiberInput_of_actualFiberInput
#print axioms jLineFiberInput_of_curveOrderCount
#print axioms jInvariantCurveTotal_of_actualFiberInput
#print axioms hasseWindowCurveTotal_of_actualFiberInput
#print axioms deuringLenstraCounts_of_actualFiberInput
#print axioms reduction_of_actualFiberInput

end

end Cogentic.RandomizedL27Fiber
