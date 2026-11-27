import Cogentic.RandomizedL27Deuring
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# L27 stratification: the `j`-line fiber count behind `HasseWindowCurveTotal`

`Cogentic.RandomizedL27Deuring` reduces the LP §7 Deuring inputs to
`JInvariantStratification`:

* at most `p` `j`-invariants;
* at most two twists for each ordinary invariant, and at most six at each of at
  most two exceptional invariants (`0` and `1728`);
* the total curve count is the sum of the twist multiplicities.

This file does not reprove the geometry of the `j`-line.  Instead it isolates
the *smallest combinatorial sub-Props* behind that stratification and proves
the reduction.

## The sub-Props

The curve count `curveTotal` is an `ℝ`-valued sum over **group orders**, while a
`j`-line stratification is a sum over **`j`-invariants**.  The geometric input
that bridges the two is therefore a finite set of curve classes, each labelled
by the `j`-invariant of its isomorphism class:

* `JLinePartition` — the finite curve-class model together with the identity
  `curveTotal = #curveClasses` (the partition of curves by `j`-invariant);
* `JLineCardBound` — at most `p` realized `j`-invariants;
* `TwistFiberBound` — the fiber over each ordinary invariant has at most two
  classes and the fibers over at most two exceptional invariants have at most
  six classes.

`JLineFiberInput` bundles these three statements.  The main equivalence
`jLineFiberInput_iff_jInvariantStratification` proves that this model is
**lossless**: every stratification produces such a model (by taking the sigma
type of the multiplicity function), and every model produces a stratification
(by taking the fibers of the `j`-invariant map).  Hence no curve is discarded
and no multiplicity is set to zero.

The existing `RandomizedHasseIncidence` and `RandomizedEllipticAndGaussian`
modules only bound Hasse-interval incidences of prime centres and recursive
splitting failures; they do not count `j`-fibers of elliptic curves.  The fiber
bounds are therefore kept as the explicit combinatorial input below, while the
order-count identity is derived in `curveTotal_eq_card_of_orderFiber` from the
fiberwise definition of `orderCount`.

The elementary counting lemma
`JInvariantStratification → JInvariantCurveTotal` is already proved in
`RandomizedL27Deuring`; this file re-exports the composite reduction
`JLineFiberInput → JInvariantCurveTotal → HasseWindowCurveTotal`, together with
a constructor `L27DeuringInputs.ofFiberInput` that replaces only the
`j_invariant_strata` field of the bundled Deuring inputs.

No `sorry`, `admit`, `axiom`, or `native_decide`; no count is set to zero.
-/

namespace Cogentic.RandomizedL27Stratification

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The natural-valued total and its real cast -/

/-- The total number of curves in the Hasse window, before casting to `ℝ`. -/
def curveTotalNat (orderCount : ℕ → ℕ → ℕ) (orderTop : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (orderTop n + 1), orderCount n j

/-- `curveTotal` is the cast of the natural-valued total. -/
theorem curveTotal_eq_natCast (orderCount : ℕ → ℕ → ℕ) (orderTop : ℕ → ℕ)
    (n : ℕ) :
    curveTotal orderCount orderTop n = (curveTotalNat orderCount orderTop n : ℝ) := by
  unfold curveTotal curveTotalNat
  push_cast
  rfl

/-- The natural total is monotone under pointwise domination of the order
counts. -/
theorem curveTotalNat_le_of_pointwise {orderCount modelCount : ℕ → ℕ → ℕ}
    {orderTop : ℕ → ℕ} (h : ∀ n j, orderCount n j ≤ modelCount n j) (n : ℕ) :
    curveTotalNat orderCount orderTop n ≤ curveTotalNat modelCount orderTop n := by
  unfold curveTotalNat
  exact Finset.sum_le_sum fun j _ => h n j

/-! ## 2. The total as an order-fiber count -/

/-- **`curveTotal` is the number of curve classes when `orderCount` is its
order-fiber count.**  If `orderCount n j` counts the curve classes with exactly
`j` points and every realized order lies at most at `orderTop n`, then the sum
of the order fibers is the total number of classes.  This discharges the total
identity in `JLinePartition` from the fiberwise definition of `orderCount`
rather than taking it as an extra hypothesis. -/
theorem curveTotal_eq_card_of_orderFiber {α : Type*} {orderCount : ℕ → ℕ → ℕ}
    (curves : Finset α) (order : α → ℕ) (orderTop : ℕ → ℕ) (n : ℕ)
    (horderCount : ∀ j, orderCount n j =
      (curves.filter fun a => order a = j).card)
    (hbound : ∀ a ∈ curves, order a ≤ orderTop n) :
    curveTotal orderCount orderTop n = (curves.card : ℝ) := by
  have hmaps : (curves : Set α).MapsTo order
      (Finset.range (orderTop n + 1) : Finset ℕ) := by
    intro a ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha))
  have hcard := Finset.card_eq_sum_card_fiberwise (f := order)
    (s := curves) (t := Finset.range (orderTop n + 1)) hmaps
  calc
    curveTotal orderCount orderTop n =
        ∑ j ∈ Finset.range (orderTop n + 1), (orderCount n j : ℝ) := rfl
    _ = ∑ j ∈ Finset.range (orderTop n + 1),
        ((curves.filter fun a => order a = j).card : ℝ) :=
      Finset.sum_congr rfl fun j _ => by rw [horderCount j]
    _ = ((∑ j ∈ Finset.range (orderTop n + 1),
        (curves.filter fun a => order a = j).card : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    _ = (curves.card : ℝ) := by rw [hcard]

/-! ## 3. The fiber model of the `j`-line -/

/-- **Partition of the Hasse-window curves by `j`-invariant.**  A finite set of
curve classes whose cardinality is exactly the total curve count, together with
the `j`-invariant label of each class.

This is the smallest geometric object needed to speak about the `j`-line: it
records that the total count is a sum over `j`-fibers, without yet imposing the
twist bounds. -/
structure JLinePartition (orderCount : ℕ → ℕ → ℕ) (orderTop : ℕ → ℕ) (n : ℕ) where
  /-- The finite type of curve classes. -/
  CurveClass : Type
  /-- The curve classes in the Hasse window. -/
  curves : Finset CurveClass
  /-- The `j`-invariant of a curve class. -/
  jInv : CurveClass → ℕ
  /-- The total curve count is the number of curve classes. -/
  total_eq : curveTotal orderCount orderTop n = (curves.card : ℝ)

/-- A `JLinePartition` built from a finite curve set whose order fibers are the
given `orderCount`.  The `j`-invariant labelling is independent of the order
map; only the total identity uses the order-fiber hypothesis. -/
def JLinePartition.ofOrderFiber {α : Type} {orderCount : ℕ → ℕ → ℕ}
    (curves : Finset α) (order jInv : α → ℕ) (orderTop : ℕ → ℕ) (n : ℕ)
    (horderCount : ∀ j, orderCount n j =
      (curves.filter fun a => order a = j).card)
    (hbound : ∀ a ∈ curves, order a ≤ orderTop n) :
    JLinePartition orderCount orderTop n where
  CurveClass := α
  curves := curves
  jInv := jInv
  total_eq := curveTotal_eq_card_of_orderFiber curves order orderTop n
    horderCount hbound

/-- **The `j`-line cardinality bound.**  A curve-class model has at most `p n`
distinct `j`-invariants.  Over `F_p` this is the statement that the `j`-line has
`p + 1` points, of which the stratification uses at most `p`; the small-prime
prepass is handled separately in `RandomizedL27Deuring`. -/
def JLineCardBound (p : ℕ → ℕ) {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    {n : ℕ} (P : JLinePartition orderCount orderTop n) : Prop :=
  (P.curves.image P.jInv).card ≤ p n

/-- **The twist-fiber bound.**  Away from at most two exceptional invariants
(`0` and `1728`) every `j`-fiber has at most two curve classes (a quadratic
twist); at the exceptions each fiber has at most six. -/
def TwistFiberBound {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ} {n : ℕ}
    (P : JLinePartition orderCount orderTop n) : Prop :=
  ∃ exc : Finset ℕ,
    exc ⊆ P.curves.image P.jInv ∧
      exc.card ≤ 2 ∧
        (∀ x ∈ P.curves.image P.jInv, x ∉ exc →
          (P.curves.filter fun a => P.jInv a = x).card ≤ 2) ∧
          ∀ x ∈ exc, (P.curves.filter fun a => P.jInv a = x).card ≤ 6

/-- **The smallest explicit combinatorial input behind `HasseWindowCurveTotal`.**
Every `n` admits a finite partition of its Hasse-window curves by `j`-invariant,
with at most `p n` realized invariants and with the twist multiplicities bounded
by two, except at at most two exceptional invariants where they are bounded by
six. -/
def JLineFiberInput (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) : Prop :=
  ∀ n, ∃ P : JLinePartition orderCount orderTop n,
    JLineCardBound p P ∧ TwistFiberBound P

/-! ## 4. The fiber model gives the stratification -/

/-- **Fiber model → `JInvariantStratification`.**  Taking the image of the
`j`-invariant map as the strata and the fiber cardinalities as the twist
multiplicities recovers the stratification of `RandomizedL27Deuring` exactly.
The identity is `Finset.card_eq_sum_card_image`. -/
theorem jInvariantStratification_of_fiberInput {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JLineFiberInput p orderCount orderTop) :
    JInvariantStratification p orderCount orderTop := by
  intro n
  obtain ⟨P, hcard, exc, hsub, hexc, htwo, hsix⟩ := h n
  refine ⟨P.curves.image P.jInv,
    fun x => (P.curves.filter fun a => P.jInv a = x).card,
    exc, hcard, hsub, hexc, htwo, hsix, ?_⟩
  rw [P.total_eq]
  have hsum := Finset.card_eq_sum_card_image P.jInv P.curves
  rw [hsum]
  push_cast
  rfl

/-- **`JLineFiberInput` → the sharp `2p + 8` curve total.** -/
theorem jInvariantCurveTotal_of_fiberInput {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JLineFiberInput p orderCount orderTop) :
    JInvariantCurveTotal p orderCount orderTop :=
  jInvariantCurveTotal_of_stratification
    (jInvariantStratification_of_fiberInput h)

/-- **`JLineFiberInput` → the paper's `≤ 4p` Hasse-window total**, under the
small-prime prepass `4 ≤ p`. -/
theorem hasseWindowCurveTotal_of_fiberInput {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JLineFiberInput p orderCount orderTop) (hp : ∀ n, 4 ≤ p n) :
    HasseWindowCurveTotal p orderCount orderTop :=
  hasseWindowCurveTotal_of_jInvariant (jInvariantCurveTotal_of_fiberInput h) hp

/-- **`JLineFiberInput` → the paper's `≤ 4p` total without a global small-prime
hypothesis.**  Only the indices with `p < 4` need the direct estimate. -/
theorem hasseWindowCurveTotal_of_fiberInput_and_small {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JLineFiberInput p orderCount orderTop)
    (hsmall : ∀ n, p n < 4 →
      curveTotal orderCount orderTop n ≤ 4 * (p n : ℝ)) :
    HasseWindowCurveTotal p orderCount orderTop :=
  hasseWindowCurveTotal_of_jInvariant_and_small
    (jInvariantCurveTotal_of_fiberInput h) hsmall

/-! ## 5. The `j`-line cardinality variant

The true `j`-line over `F_p` has `p + 1` points.  The paper's stratification uses
`p`; the next two results record that the argument still yields the `≤ 4p`
conclusion from `p + 1` realized invariants as soon as `5 ≤ p`, so the choice of
`p` versus `p + 1` is not a hidden extra hypothesis. -/

/-- The sharp `2(p + 1) + 8` total from a `p + 1`-cardinality stratification. -/
def JInvariantCurveTotalSucc (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) : Prop :=
  ∀ n, curveTotal orderCount orderTop n ≤ 2 * ((p n : ℝ) + 1) + 8

/-- A `p + 1`-cardinality version of the stratification. -/
def JInvariantStratificationSucc (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) : Prop :=
  ∀ n, ∃ (strata : Finset ℕ) (m : ℕ → ℕ) (exc : Finset ℕ),
    strata.card ≤ p n + 1 ∧ exc ⊆ strata ∧ exc.card ≤ 2 ∧
      (∀ x ∈ strata, x ∉ exc → m x ≤ 2) ∧
        (∀ x ∈ exc, m x ≤ 6) ∧
          curveTotal orderCount orderTop n = ∑ x ∈ strata, (m x : ℝ)

/-- The `p + 1`-cardinality stratification gives the `2(p + 1) + 8` total. -/
theorem jInvariantCurveTotalSucc_of_stratificationSucc {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JInvariantStratificationSucc p orderCount orderTop) :
    JInvariantCurveTotalSucc p orderCount orderTop := by
  intro n
  obtain ⟨strata, m, exc, hcard, hsub, hexc, hm, hme, htotal⟩ := h n
  rw [htotal]
  have hle := sum_multiplicity_le_two_mul_add_eight strata exc m (p n + 1)
    hcard hsub hexc hm hme
  have hcast : ((p n + 1 : ℕ) : ℝ) = (p n : ℝ) + 1 := by push_cast; ring
  linarith

/-- `2(p + 1) + 8 ≤ 4p` for `p ≥ 5`. -/
theorem two_mul_succ_add_eight_le_four_mul {p : ℕ} (hp : 5 ≤ p) :
    2 * ((p : ℝ) + 1) + 8 ≤ 4 * (p : ℝ) := by
  have hp' : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  linarith

/-- The `p + 1`-cardinality stratification still gives `≤ 4p` once `5 ≤ p`. -/
theorem hasseWindowCurveTotal_of_stratificationSucc {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JInvariantStratificationSucc p orderCount orderTop) (hp : ∀ n, 5 ≤ p n) :
    HasseWindowCurveTotal p orderCount orderTop := by
  intro n
  have hle := two_mul_succ_add_eight_le_four_mul (hp n)
  linarith [jInvariantCurveTotalSucc_of_stratificationSucc h n]

/-! ## 6. Losslessness of the fiber model -/

/-- The fiber cardinality of the sigma-type model built from a multiplicity
function.  This is the computation `#(fiber over x) = m x` used in the converse
direction. -/
theorem fiber_card_sigma {strata : Finset ℕ} {m : ℕ → ℕ} {x : ℕ}
    (hx : x ∈ strata) :
    ((strata.sigma fun y => (Finset.univ : Finset (Fin (m y)))).filter
        (fun a => a.1 = x)).card = m x := by
  rw [Finset.filter_sigma]
  rw [Finset.card_sigma]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hyx
    simp [hyx]
  · intro hxnot
    exact (hxnot hx).elim

/-- **`JInvariantStratification` → `JLineFiberInput`.**  Every stratification
is realized by a fiber model: take the sigma type `Σ x, Fin (m x)` over the
strata, with the first projection as `j`-invariant.  The zero-multiplicity
strata disappear from the image, so the cardinality bound only gets sharper and
the exception set is intersected with the image. -/
theorem fiberInput_of_jInvariantStratification {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (h : JInvariantStratification p orderCount orderTop) :
    JLineFiberInput p orderCount orderTop := by
  intro n
  obtain ⟨strata, m, exc, hcard, hsub, hexc, hm, hme, htotal⟩ := h n
  let curves : Finset (Σ x : ℕ, Fin (m x)) :=
    strata.sigma fun x => Finset.univ
  let jInv : (Σ x : ℕ, Fin (m x)) → ℕ := fun a => a.1
  have hcard_curves : (curves.card : ℝ) = ∑ x ∈ strata, (m x : ℝ) := by
    simp only [curves]
    rw [Finset.card_sigma]
    simp
  let P : JLinePartition orderCount orderTop n :=
    { CurveClass := Σ x : ℕ, Fin (m x)
      curves := curves
      jInv := jInv
      total_eq := by rw [htotal, hcard_curves] }
  have himage_subset : P.curves.image P.jInv ⊆ strata := by
    intro x hx
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hx
    have ha' : a.1 ∈ strata := (Finset.mem_sigma.mp ha).1
    cases hEq
    exact ha'
  have hfiber : ∀ x ∈ P.curves.image P.jInv,
      (P.curves.filter fun a => P.jInv a = x).card = m x := by
    intro x hx
    have hxstrata : x ∈ strata := himage_subset hx
    change ((strata.sigma fun y => (Finset.univ : Finset (Fin (m y)))).filter
        (fun a => a.1 = x)).card = m x
    exact fiber_card_sigma hxstrata
  let exc' : Finset ℕ := exc.filter fun x => x ∈ P.curves.image P.jInv
  refine ⟨P, ?_, exc', ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_le_card himage_subset).trans hcard
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · exact (Finset.card_filter_le _ _).trans hexc
  · intro x hx hxnot
    have hxstrata : x ∈ strata := himage_subset hx
    have hxexc : x ∉ exc := by
      intro hxin
      exact hxnot (Finset.mem_filter.mpr ⟨hxin, hx⟩)
    rw [hfiber x hx]
    exact hm x hxstrata hxexc
  · intro x hx
    have hxexc : x ∈ exc := (Finset.mem_filter.mp hx).1
    rw [hfiber x ((Finset.mem_filter.mp hx).2)]
    exact hme x hxexc

/-- **The fiber model is lossless.**  `JLineFiberInput` and
`JInvariantStratification` are equivalent: the curve classes and `j`-labels
determine the strata and multiplicities, and conversely the sigma type of the
multiplicity function realizes any stratification without changing the total. -/
theorem jLineFiberInput_iff_jInvariantStratification {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ} :
    JLineFiberInput p orderCount orderTop ↔
      JInvariantStratification p orderCount orderTop :=
  ⟨jInvariantStratification_of_fiberInput,
    fiberInput_of_jInvariantStratification⟩

end

end Cogentic.RandomizedL27Stratification

/-! ## 7. The bundled Deuring inputs from the fiber model -/

namespace Cogentic.RandomizedL27Deuring
namespace L27DeuringInputs

open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Stratification

variable {I : L27_1Inputs}

/-- **The smallest Deuring inputs, with the `j`-line field supplied in fiber
form.**  This is `L27DeuringInputs` with only `j_invariant_strata` replaced by
the strictly more explicit `JLineFiberInput`; the Hurwitz weight, the Deuring
trace formula, the Hurwitz lower bound, and the small-prime prepass are
unchanged. -/
def ofFiberInput (hurwitz : ℤ → ℝ)
    (htrace : DeuringTraceFormula I.p I.smooth I.orderCount hurwitz)
    (hlower : HurwitzClassLower I.p I.smooth hurwitz I.κ)
    (hfib : JLineFiberInput I.p I.orderCount I.orderTop)
    (hp : ∀ n, 4 ≤ I.p n) : L27DeuringInputs I where
  hurwitz := hurwitz
  deuring_trace := htrace
  hurwitz_class_lower := hlower
  j_invariant_strata := jInvariantStratification_of_fiberInput hfib
  p_ge_four := hp

/-- The sharp `2p + 8` total from the fiber form of the `j`-line input. -/
theorem jInvariantCurveTotal_of_fiberInput
    (hfib : JLineFiberInput I.p I.orderCount I.orderTop) :
    JInvariantCurveTotal I.p I.orderCount I.orderTop :=
  Cogentic.RandomizedL27Stratification.jInvariantCurveTotal_of_fiberInput hfib

/-- The paper's `≤ 4p` total from the fiber form of the `j`-line input and the
small-prime prepass already stored in `L27DeuringInputs`. -/
theorem hasseWindowCurveTotal_of_fiberInput (D : L27DeuringInputs I)
    (hfib : JLineFiberInput I.p I.orderCount I.orderTop) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  Cogentic.RandomizedL27Stratification.hasseWindowCurveTotal_of_fiberInput
    hfib D.p_ge_four

end L27DeuringInputs
end Cogentic.RandomizedL27Deuring

namespace Cogentic.RandomizedL27Stratification

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-- **`DeuringLenstraCounts` from the fiber form of the `j`-line input.**  The
Hurwitz split and the `j`-line fiber count are the only Deuring ingredients. -/
theorem deuringLenstraCounts_of_fiberInput {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ)
    (htrace : DeuringTraceFormula I.p I.smooth I.orderCount hurwitz)
    (hlower : HurwitzClassLower I.p I.smooth hurwitz I.κ)
    (hfib : JLineFiberInput I.p I.orderCount I.orderTop)
    (hp : ∀ n, 4 ≤ I.p n) :
    DeuringLenstraCounts I :=
  (L27DeuringInputs.ofFiberInput (I := I) hurwitz htrace hlower hfib hp).deuringLenstraCounts

/-- **The full L27.1 ledger from the fiber form of the `j`-line input.**  All
non-Deuring fields are passed through unchanged. -/
theorem reduced_ledger_of_fiberInput {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ)
    (htrace : DeuringTraceFormula I.p I.smooth I.orderCount hurwitz)
    (hlower : HurwitzClassLower I.p I.smooth hurwitz I.κ)
    (hfib : JLineFiberInput I.p I.orderCount I.orderTop)
    (hp : ∀ n, 4 ≤ I.p n)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  (L27DeuringInputs.ofFiberInput (I := I) hurwitz htrace hlower hfib hp).reduced_ledger
    hhasse h0 h1 h2 hstage hbudget hlog

/-- **The manuscript-rate deficit from the fiber form of the `j`-line input.** -/
theorem reduced_paper_of_fiberInput {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ)
    (htrace : DeuringTraceFormula I.p I.smooth I.orderCount hurwitz)
    (hlower : HurwitzClassLower I.p I.smooth hurwitz I.κ)
    (hfib : JLineFiberInput I.p I.orderCount I.orderTop)
    (hp : ∀ n, 4 ≤ I.p n)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  (L27DeuringInputs.ofFiberInput (I := I) hurwitz htrace hlower hfib hp).reduced_paper
    hhasse h0 h1 h2 hstage hbudget hlog

/-- **The full L27.1 capstone from the fiber form of the `j`-line input.**  The
Hurwitz weight, the Deuring trace formula, the Hurwitz lower bound, the `j`-line
fiber count, and the small-prime prepass replace the whole bundled
`L27DeuringInputs`; all remaining LP §7 inputs are passed through. -/
theorem reduction_of_fiberInput {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ)
    (htrace : DeuringTraceFormula I.p I.smooth I.orderCount hurwitz)
    (hlower : HurwitzClassLower I.p I.smooth hurwitz I.κ)
    (hfib : JLineFiberInput I.p I.orderCount I.orderTop)
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
  reduction_of_deuring
    (L27DeuringInputs.ofFiberInput (I := I) hurwitz htrace hlower hfib hp)
    hhasse h0 h1 h2 hstage hbudget hlog

/-! ## 8. Monotonicity in the order counts -/

/-- The sharp `2p + 8` fiber total is monotone under pointwise domination of the
order counts. -/
theorem jInvariantCurveTotal_of_fiberInput_dominated {p : ℕ → ℕ}
    {modelCount orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hdom : ∀ n j, orderCount n j ≤ modelCount n j)
    (h : JInvariantCurveTotal p modelCount orderTop) :
    JInvariantCurveTotal p orderCount orderTop :=
  jInvariantCurveTotal_of_dominated hdom h

/-! ## Axiom audit -/

#print axioms curveTotal_eq_natCast
#print axioms curveTotalNat_le_of_pointwise
#print axioms curveTotal_eq_card_of_orderFiber
#print axioms JLinePartition.ofOrderFiber
#print axioms jInvariantStratification_of_fiberInput
#print axioms jInvariantCurveTotal_of_fiberInput
#print axioms hasseWindowCurveTotal_of_fiberInput
#print axioms hasseWindowCurveTotal_of_fiberInput_and_small
#print axioms jInvariantCurveTotalSucc_of_stratificationSucc
#print axioms two_mul_succ_add_eight_le_four_mul
#print axioms hasseWindowCurveTotal_of_stratificationSucc
#print axioms fiber_card_sigma
#print axioms fiberInput_of_jInvariantStratification
#print axioms jLineFiberInput_iff_jInvariantStratification
#print axioms Cogentic.RandomizedL27Deuring.L27DeuringInputs.ofFiberInput
#print axioms Cogentic.RandomizedL27Deuring.L27DeuringInputs.jInvariantCurveTotal_of_fiberInput
#print axioms Cogentic.RandomizedL27Deuring.L27DeuringInputs.hasseWindowCurveTotal_of_fiberInput
#print axioms deuringLenstraCounts_of_fiberInput
#print axioms reduced_ledger_of_fiberInput
#print axioms reduced_paper_of_fiberInput
#print axioms reduction_of_fiberInput
#print axioms jInvariantCurveTotal_of_fiberInput_dominated

end

end Cogentic.RandomizedL27Stratification
