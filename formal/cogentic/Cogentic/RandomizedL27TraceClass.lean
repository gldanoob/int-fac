import Cogentic.RandomizedL27Hurwitz

/-!
# L27 trace classes: removing the two trace-class `Prop`s

`Cogentic.RandomizedL27Hurwitz` stores two fields of `L27HurwitzInputs` that are
not paper-level theorems in their own right:

* `trace_class_lower : DeuringTraceClassLower I.p traceCount hurwitz` — the
  one-sided Deuring/Waterhouse count at a fixed Frobenius trace;
* `orderCountContainsTrace : OrderCountContainsTraceClass I.p I.smooth
  I.orderCount traceCount` — the curves of a fixed trace are contained in the
  curves of that group order.

Both are stated for an *abstract* function `traceCount`, so as written they
cannot be theorems: they are compatible only when `traceCount` really is the
trace fiber of the curve model.  This file fixes the canonical fiber

`traceCountOfOrder p orderCount n t = orderCount n (p + 1 - t)`

(the group order of a curve with trace `t`), and then

* proves `OrderCountContainsTraceClass` **unconditionally** from the
  smooth-order definition: a curve with `j` points has Frobenius trace
  `p + 1 - j`, so its trace fiber is the order fiber;
* proves `DeuringTraceClassLower` from the exact Deuring/Waterhouse identity
  written directly on the order count, and, more generally, from the
  one-sided trace count `DeuringTraceCountLower`, which is the smallest
  explicit curve-count input needed by the reduction.

The remaining Deuring input is therefore a single statement about the concrete
curve model rather than two statements about a free-floating `traceCount`:

* `DeuringWaterhouseExactOrder` — the classical exact identity
  `#curves with trace t = H(4p - t²)`; or, weaker,
* `DeuringTraceCountLower` — the one-sided inequality
  `H(4p - t²) ≤ #curves with trace t`.

`L27TraceClassInputs` bundles the latter, and `toHurwitzInputs` reassembles
`L27HurwitzInputs` with the two trace-class fields *discharged*.  All downstream
L27.1 conclusions are re-exported.  No `sorry`, `admit`, `axiom`, or
`native_decide` is used, and no count is set to zero.
-/

namespace Cogentic.RandomizedL27TraceClass

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The trace fiber of the curve model -/

/-- The group order of a curve over `F_p` with Frobenius trace `t`:
`p + 1 - t`, read as a natural number.  Traces occurring with a positive
Frobenius discriminant satisfy `t ≤ p + 1`, so this is the honest order; on
the rest of `ℤ` the value is irrelevant for the Deuring count. -/
def traceOrder (p : ℕ) (t : ℤ) : ℕ := ((p : ℤ) + 1 - t).toNat

/-- A curve with `j` points has Frobenius trace `p + 1 - j`, hence trace order
`j`.  This is the smooth-order/group-order compatibility used below. -/
theorem traceOrder_hasseTrace (p j : ℕ) :
    traceOrder p (hasseTrace p j) = j := by
  unfold traceOrder hasseTrace
  have h : (p : ℤ) + 1 - ((p : ℤ) + 1 - (j : ℤ)) = (j : ℤ) := by ring
  rw [h]
  simp

/-- On the positive-discriminant part of the Hasse window, the trace does not
exceed `p + 1`, so `traceOrder` is the honest group order `p + 1 - t`. -/
theorem traceOrder_arg_nonneg {p : ℕ} {t : ℤ} (ht : 0 < traceDisc p t) :
    t ≤ (p : ℤ) + 1 := by
  unfold traceDisc at ht
  by_contra h
  push Not at h
  have hge : (p : ℤ) + 2 ≤ t := by omega
  have hsq : ((p : ℤ) + 2) ^ 2 ≤ t ^ 2 :=
    pow_le_pow_left₀ (by omega) hge 2
  nlinarith

/-- **The canonical trace count.**  The number of curves over `F_p` with
Frobenius trace `t` is the order count at the group order `p + 1 - t`.  This is
the function the two trace-class `Prop`s of `RandomizedL27Hurwitz` implicitly
refer to; fixing it turns those `Prop`s into theorems. -/
def traceCountOfOrder (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ) : ℕ → ℤ → ℕ :=
  fun n t => orderCount n (traceOrder (p n) t)

/-- A `traceCount` is compatible with the order model when the curves of trace
`p + 1 - j` are exactly the curves with `j` points. -/
def TraceCountAgreesOnOrder (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (traceCount : ℕ → ℤ → ℕ) : Prop :=
  ∀ n j, traceCount n (hasseTrace (p n) j) = orderCount n j

/-- The canonical trace count agrees with the order count at every order. -/
theorem traceCountOfOrder_agrees (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ) :
    TraceCountAgreesOnOrder p orderCount (traceCountOfOrder p orderCount) := by
  intro n j
  unfold traceCountOfOrder
  rw [traceOrder_hasseTrace]

/-- **`OrderCountContainsTraceClass` from the smooth-order definition.**  If
`traceCount` is the trace fiber of the order model, then the trace class of a
smooth order is contained in the order count — in fact the two counts are
equal.  The smooth hypothesis is not needed. -/
theorem orderCountContainsTraceClass_of_agrees {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {orderCount : ℕ → ℕ → ℕ}
    {traceCount : ℕ → ℤ → ℕ}
    (h : TraceCountAgreesOnOrder p orderCount traceCount) :
    OrderCountContainsTraceClass p smooth orderCount traceCount := by
  intro n j _
  exact le_of_eq (h n j)

/-- **The first old `Prop` is a theorem for the canonical trace count.** -/
theorem orderCountContainsTraceClass_traceCountOfOrder (p : ℕ → ℕ)
    (smooth : ℕ → ℕ → Bool) (orderCount : ℕ → ℕ → ℕ) :
    OrderCountContainsTraceClass p smooth orderCount
      (traceCountOfOrder p orderCount) :=
  orderCountContainsTraceClass_of_agrees
    (traceCountOfOrder_agrees p orderCount)

/-! ## 2. The Deuring/Waterhouse trace identity -/

/-- **The exact Deuring/Waterhouse identity on the order model.**  For every
trace `t` with positive Frobenius discriminant, the number of curves with group
order `p + 1 - t` is exactly the Hurwitz class number `H(4p - t²)`.  This is the
classical exact trace identity, stated without a separate abstract
`traceCount`. -/
def DeuringWaterhouseExactOrder (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (hurwitz : ℤ → ℝ) : Prop :=
  ∀ n t, 0 < traceDisc (p n) t →
    (orderCount n (traceOrder (p n) t) : ℝ) = hurwitz (traceDisc (p n) t)

/-- The exact identity through the canonical trace count is definitionally the
same statement as `DeuringWaterhouseExactOrder`. -/
theorem deuringWaterhouseExact_traceCountOfOrder_iff {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {hurwitz : ℤ → ℝ} :
    DeuringWaterhouseExact p (traceCountOfOrder p orderCount) hurwitz ↔
      DeuringWaterhouseExactOrder p orderCount hurwitz :=
  Iff.rfl

/-- **`DeuringTraceClassLower` from the exact trace identity.**  The one-sided
trace-class count is the inequality half of the exact Deuring/Waterhouse
identity. -/
theorem deuringTraceClassLower_traceCountOfOrder_of_exact {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {hurwitz : ℤ → ℝ}
    (h : DeuringWaterhouseExactOrder p orderCount hurwitz) :
    DeuringTraceClassLower p (traceCountOfOrder p orderCount) hurwitz := by
  intro n t ht
  exact le_of_eq (h n t ht).symm

/-- **The smallest explicit curve-count input.**  The one-sided
Deuring/Waterhouse lower bound, stated directly on the order count: every
positive Frobenius discriminant `4p - t²` is realised by at least its Hurwitz
weight in curves with `p + 1 - t` points.  This is exactly
`DeuringTraceClassLower` after fixing the trace count to the order fiber. -/
def DeuringTraceCountLower (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (hurwitz : ℤ → ℝ) : Prop :=
  ∀ n t, 0 < traceDisc (p n) t →
    hurwitz (traceDisc (p n) t) ≤ (orderCount n (traceOrder (p n) t) : ℝ)

/-- The exact Deuring/Waterhouse identity implies the one-sided curve-count
input.  No curve is lost: the identity is used in the direction needed by the
Deuring lower bound. -/
theorem deuringTraceCountLower_of_exact {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {hurwitz : ℤ → ℝ}
    (h : DeuringWaterhouseExactOrder p orderCount hurwitz) :
    DeuringTraceCountLower p orderCount hurwitz := by
  intro n t ht
  exact le_of_eq (h n t ht).symm

/-- The one-sided curve-count input gives `DeuringTraceClassLower` for the
canonical trace count. -/
theorem deuringTraceClassLower_traceCountOfOrder_of_lower {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {hurwitz : ℤ → ℝ}
    (h : DeuringTraceCountLower p orderCount hurwitz) :
    DeuringTraceClassLower p (traceCountOfOrder p orderCount) hurwitz := by
  intro n t ht
  exact h n t ht

/-- **Both trace-class `Prop`s, from the exact identity.**  This is the direct
discharge of the two fields of `L27HurwitzInputs`: the lower bound is the exact
identity read as an inequality, and the containment is the smooth-order/trace
compatibility of §1. -/
theorem traceClassProps_of_exact {p : ℕ → ℕ} {orderCount : ℕ → ℕ → ℕ}
    {hurwitz : ℤ → ℝ} (smooth : ℕ → ℕ → Bool)
    (h : DeuringWaterhouseExactOrder p orderCount hurwitz) :
    DeuringTraceClassLower p (traceCountOfOrder p orderCount) hurwitz ∧
      OrderCountContainsTraceClass p smooth orderCount
        (traceCountOfOrder p orderCount) :=
  ⟨deuringTraceClassLower_traceCountOfOrder_of_exact h,
    orderCountContainsTraceClass_traceCountOfOrder p smooth orderCount⟩

/-- **Both trace-class `Prop`s, from the minimal one-sided input.** -/
theorem traceClassProps_of_lower {p : ℕ → ℕ} {orderCount : ℕ → ℕ → ℕ}
    {hurwitz : ℤ → ℝ} (smooth : ℕ → ℕ → Bool)
    (h : DeuringTraceCountLower p orderCount hurwitz) :
    DeuringTraceClassLower p (traceCountOfOrder p orderCount) hurwitz ∧
      OrderCountContainsTraceClass p smooth orderCount
        (traceCountOfOrder p orderCount) :=
  ⟨deuringTraceClassLower_traceCountOfOrder_of_lower h,
    orderCountContainsTraceClass_traceCountOfOrder p smooth orderCount⟩

/-- **Lossless split of the two old trace-class `Prop`s.**  For the canonical
trace count, their conjunction is exactly the single one-sided order-model
input; the containment half is automatic and the lower half is the Deuring
inequality.  Hence replacing the two `Prop`s by `DeuringTraceCountLower` loses
nothing. -/
theorem traceClassLower_and_contains_iff {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {hurwitz : ℤ → ℝ}
    (smooth : ℕ → ℕ → Bool) :
    (DeuringTraceClassLower p (traceCountOfOrder p orderCount) hurwitz ∧
        OrderCountContainsTraceClass p smooth orderCount
          (traceCountOfOrder p orderCount)) ↔
      DeuringTraceCountLower p orderCount hurwitz := by
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨deuringTraceClassLower_traceCountOfOrder_of_lower h,
      orderCountContainsTraceClass_traceCountOfOrder p smooth orderCount⟩

/-! ## 3. The bundled inputs with the trace-class Props discharged -/

/-- **The L27 Hurwitz/Deuring inputs without the two trace-class `Prop`s.**

Compared with `L27HurwitzInputs`, the abstract `traceCount` and the two fields
`trace_class_lower` and `orderCount_contains_trace` are gone.  In their place is
the single concrete curve-count input `trace_count_lower`, which is exactly the
one-sided Deuring/Waterhouse inequality on the order model.  The analytic
Hurwitz leaves (`c`, `θ`, `siegel_lower`, `disc_scale`) and the two geometric
fields (`j_invariant_strata`, `p_ge_four`) are unchanged.

No field sets a class number, curve count, or probability to zero. -/
structure L27TraceClassInputs (I : L27_1Inputs) where
  /-- The Hurwitz class number `H(-D)`. -/
  hurwitz : ℤ → ℝ
  /-- Siegel constant in `H(-D) ≥ c√D`. -/
  c : ℝ
  /-- Nondegeneracy fraction `D(p,j) ≥ θp` on smooth orders. -/
  θ : ℝ
  /-- The Siegel constant is positive. -/
  c_pos : 0 < c
  /-- The nondegeneracy fraction is positive. -/
  θ_pos : 0 < θ
  /-- The Hasse-scale constant is below the Siegel constant at scale `√θ`. -/
  kappa_le : I.κ ≤ c * Real.sqrt θ
  /-- Siegel's lower bound on Frobenius-trace discriminants. -/
  siegel_lower : HurwitzSiegelLowerTrace I.p hurwitz c
  /-- Smooth Frobenius discriminants retain a `θ`-fraction of the Hasse width. -/
  disc_scale : HurwitzDiscriminantScale I.p I.smooth θ
  /-- The one-sided Deuring/Waterhouse count on the order model. -/
  trace_count_lower : DeuringTraceCountLower I.p I.orderCount hurwitz
  /-- The `j`-line stratification of the curves. -/
  j_invariant_strata : JInvariantStratification I.p I.orderCount I.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  p_ge_four : ∀ n, 4 ≤ I.p n

/-- **The new inputs with the two trace-class fields discharged.**  The canonical
trace count is supplied by the model, `OrderCountContainsTraceClass` is proved
unconditionally, and `DeuringTraceClassLower` follows from the one-sided
order-model input. -/
def L27TraceClassInputs.ofLeaves {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ) {c θ : ℝ}
    (c_pos : 0 < c) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ c * Real.sqrt θ)
    (siegel : HurwitzSiegelLowerTrace I.p hurwitz c)
    (scale : HurwitzDiscriminantScale I.p I.smooth θ)
    (trace : DeuringTraceCountLower I.p I.orderCount hurwitz)
    (strata : JInvariantStratification I.p I.orderCount I.orderTop)
    (hp4 : ∀ n, 4 ≤ I.p n) : L27TraceClassInputs I where
  hurwitz := hurwitz
  c := c
  θ := θ
  c_pos := c_pos
  θ_pos := θ_pos
  kappa_le := kappa_le
  siegel_lower := siegel
  disc_scale := scale
  trace_count_lower := trace
  j_invariant_strata := strata
  p_ge_four := hp4

/-- **The exact Deuring/Waterhouse identity suffices.**  Starting from the exact
trace identity, the one-sided curve-count input is derived and the bundle is
built. -/
def L27TraceClassInputs.ofExact {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ) {c θ : ℝ}
    (c_pos : 0 < c) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ c * Real.sqrt θ)
    (siegel : HurwitzSiegelLowerTrace I.p hurwitz c)
    (scale : HurwitzDiscriminantScale I.p I.smooth θ)
    (exact : DeuringWaterhouseExactOrder I.p I.orderCount hurwitz)
    (strata : JInvariantStratification I.p I.orderCount I.orderTop)
    (hp4 : ∀ n, 4 ≤ I.p n) : L27TraceClassInputs I :=
  ofLeaves hurwitz c_pos θ_pos kappa_le siegel scale
    (deuringTraceCountLower_of_exact exact) strata hp4

namespace L27TraceClassInputs

variable {I : L27_1Inputs}

/-- **Reassemble `L27HurwitzInputs`.**  The two trace-class fields are filled by
the theorems of §§1–2, so this constructor removes them from the input set. -/
def toHurwitzInputs (D : L27TraceClassInputs I) : L27HurwitzInputs I where
  hurwitz := D.hurwitz
  traceCount := traceCountOfOrder I.p I.orderCount
  c := D.c
  θ := D.θ
  c_pos := D.c_pos
  θ_pos := D.θ_pos
  kappa_le := D.kappa_le
  siegel_lower := D.siegel_lower
  disc_scale := D.disc_scale
  trace_class_lower :=
    deuringTraceClassLower_traceCountOfOrder_of_lower D.trace_count_lower
  orderCount_contains_trace :=
    orderCountContainsTraceClass_traceCountOfOrder I.p I.smooth I.orderCount
  j_invariant_strata := D.j_invariant_strata
  p_ge_four := D.p_ge_four

/-- The Hurwitz class-number lower bound from the new inputs. -/
theorem hurwitzClassLower (D : L27TraceClassInputs I) :
    HurwitzClassLower I.p I.smooth D.hurwitz I.κ :=
  D.toHurwitzInputs.hurwitzClassLower

/-- The one-sided Deuring trace formula from the new inputs. -/
theorem deuringTraceFormula (D : L27TraceClassInputs I) :
    DeuringTraceFormula I.p I.smooth I.orderCount D.hurwitz :=
  D.toHurwitzInputs.deuringTraceFormula

/-- Reassemble the smaller `L27DeuringInputs` bundle. -/
def toDeuringInputs (D : L27TraceClassInputs I) : L27DeuringInputs I :=
  D.toHurwitzInputs.toDeuringInputs

/-- The per-order Deuring/Lenstra bound. -/
theorem deuringSmoothOrderCount (D : L27TraceClassInputs I) :
    DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ :=
  D.toHurwitzInputs.deuringSmoothOrderCount

/-- The sharp `2p + 8` total. -/
theorem jInvariantCurveTotal (D : L27TraceClassInputs I) :
    JInvariantCurveTotal I.p I.orderCount I.orderTop :=
  D.toHurwitzInputs.jInvariantCurveTotal

/-- The paper's `≤ 4p` total. -/
theorem hasseWindowCurveTotal (D : L27TraceClassInputs I) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  D.toHurwitzInputs.hasseWindowCurveTotal

/-- The bundled `DeuringLenstraCounts` hypothesis of `L27_1Sub`. -/
theorem deuringLenstraCounts (D : L27TraceClassInputs I) :
    DeuringLenstraCounts I :=
  D.toHurwitzInputs.deuringLenstraCounts

/-- Reassemble `L27PaperInputs` from the new inputs and the five remaining
LP §7 inputs. -/
theorem toPaperInputs (D : L27TraceClassInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    L27PaperInputs I :=
  D.toHurwitzInputs.toPaperInputs hhasse h0 h1 h2 hstage

/-- The L27.1 ledger from the new inputs. -/
theorem reduced_ledger (D : L27TraceClassInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  D.toHurwitzInputs.reduced_ledger hhasse h0 h1 h2 hstage hbudget hlog

/-- The manuscript-rate deficit bound from the new inputs. -/
theorem reduced_paper (D : L27TraceClassInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  D.toHurwitzInputs.reduced_paper hhasse h0 h1 h2 hstage hbudget hlog

/-- The L27.1 `RatedLeaf` from the new inputs. -/
def toRatedLeaf (D : L27TraceClassInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf :=
  D.toHurwitzInputs.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog

/-- The `C5` slot `exp (-2H)` for the assembled leaf. -/
theorem slot (D : L27TraceClassInputs I)
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
  D.toHurwitzInputs.slot hhasse h0 h1 h2 hstage hbudget hlog

end L27TraceClassInputs

/-! ## 4. Capstone reduction -/

/-- **The full reduction from the trace-class-discharged inputs.**  The two old
trace-class `Prop`s are no longer hypotheses: the only Deuring input is the
one-sided curve count `DeuringTraceCountLower` on the order model. -/
theorem reduction_of_traceClass {I : L27_1Inputs}
    (D : L27TraceClassInputs I)
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
  reduction_of_hurwitz D.toHurwitzInputs hhasse h0 h1 h2 hstage hbudget hlog

/-- The Deuring half of the capstone from the new inputs. -/
theorem deuringLenstraCounts_of_traceClass {I : L27_1Inputs}
    (D : L27TraceClassInputs I) : DeuringLenstraCounts I :=
  D.deuringLenstraCounts

/-- **Compatibility with `RandomizedL27Hurwitz`.**  The new bundle reassembles
the old one, so every downstream theorem remains available unchanged. -/
theorem toHurwitzInputs_toDeuringInputs {I : L27_1Inputs}
    (D : L27TraceClassInputs I) :
    D.toHurwitzInputs.toDeuringInputs = D.toDeuringInputs :=
  rfl

/-! ## Axiom audit -/

#print axioms traceOrder_hasseTrace
#print axioms traceOrder_arg_nonneg
#print axioms traceCountOfOrder_agrees
#print axioms orderCountContainsTraceClass_of_agrees
#print axioms orderCountContainsTraceClass_traceCountOfOrder
#print axioms deuringWaterhouseExact_traceCountOfOrder_iff
#print axioms deuringTraceClassLower_traceCountOfOrder_of_exact
#print axioms deuringTraceCountLower_of_exact
#print axioms deuringTraceClassLower_traceCountOfOrder_of_lower
#print axioms traceClassProps_of_exact
#print axioms traceClassProps_of_lower
#print axioms traceClassLower_and_contains_iff
#print axioms L27TraceClassInputs.ofLeaves
#print axioms L27TraceClassInputs.ofExact
#print axioms L27TraceClassInputs.toHurwitzInputs
#print axioms L27TraceClassInputs.hurwitzClassLower
#print axioms L27TraceClassInputs.deuringTraceFormula
#print axioms L27TraceClassInputs.toDeuringInputs
#print axioms L27TraceClassInputs.deuringSmoothOrderCount
#print axioms L27TraceClassInputs.jInvariantCurveTotal
#print axioms L27TraceClassInputs.hasseWindowCurveTotal
#print axioms L27TraceClassInputs.deuringLenstraCounts
#print axioms L27TraceClassInputs.toPaperInputs
#print axioms L27TraceClassInputs.reduced_ledger
#print axioms L27TraceClassInputs.reduced_paper
#print axioms L27TraceClassInputs.toRatedLeaf
#print axioms L27TraceClassInputs.slot
#print axioms reduction_of_traceClass
#print axioms deuringLenstraCounts_of_traceClass
#print axioms toHurwitzInputs_toDeuringInputs

end

end Cogentic.RandomizedL27TraceClass
