import Cogentic.RandomizedL27ClassNumber
import Cogentic.RandomizedL27Waterhouse
import Cogentic.RandomizedL27Weighted
import Cogentic.RandomizedL27Fiber
import Cogentic.RandomizedL27Window
import Cogentic.RandomizedL27StageOneFinish

/-!
# L27 Hurwitz assembly: an actual `L27HurwitzInputs` from reduced data

`Cogentic.RandomizedL27Hurwitz` reduces the LP §7 Deuring/Hurwitz block to the
bundle `L27HurwitzInputs I`, which is then consumed as an opaque field of
`L27StageOneFinishInputs`.  The present file *constructs* that bundle from the
reduced data that the earlier files isolate:

* `DirichletClassNumberInput hurwitz L1` — the standard Dirichlet class-number
  formula together with the positivity of the unit weight and the class number
  and the domination of the weighted class number by the Hurwitz class number
  (`Cogentic.RandomizedL27ClassNumber`);
* a uniform lower bound `l ≤ L(1, χ_D)` on Frobenius discriminants, at the
  Hasse scale `κ ≤ (classNumberFormulaConstant * l) * √θ`; equivalently (given
  the class-number formula) the absence of an exceptional `L(1, χ)` sequence,
  which is derived here as `noExceptional`;
* the modelled, weighted Deuring/Waterhouse identity
  `WaterhouseWeightedModelCount` on the finite Weierstrass model
  (`Cogentic.RandomizedL27Weighted`), together with the model-domination
  hypothesis `rawCurveOrderCount ≤ orderCount`;
* the `j`-line fibre count `JLineFiberInput`
  (`Cogentic.RandomizedL27Stratification`, `Cogentic.RandomizedL27Fiber`);
* the central trace window `CentralTraceWindow` (`Cogentic.RandomizedL27Window`,
  `Cogentic.RandomizedL27Scale`);
* the small-prime prepass `4 ≤ p` already required by `L27HurwitzInputs`.

## What is derived, not assumed

Starting from `L27HurwitzAssemblyInputs I`:

* `siegelLower` — the Siegel trace leaf, from the class-number formula and the
  explicit `L`-lower bound
  (`hurwitzSiegelLowerTrace_of_classNumberFormula`);
* `deuringTraceCountLower` — the one-sided order-model Deuring/Waterhouse
  count, from the weighted model identity and the model domination
  (`deuringTraceCountLower_of_dominated_model`);
* `traceClassLower` — the trace-class form of the Deuring count for the
  canonical trace fibre `traceCountOfOrder`
  (`deuringTraceClassLower_traceCountOfOrder_of_lower`);
* `orderCountContainsTrace` — the order-count containment, unconditionally from
  the canonical trace fibre
  (`orderCountContainsTraceClass_traceCountOfOrder`);
* `jInvariantStrata` — the `j`-line stratification, from the fibre input
  (`jInvariantStratification_of_fiberInput`);
* `discScale` — the discriminant scale, from the central trace window
  (`hurwitzDiscriminantScale_of_centralTraceWindow`).

`toHurwitzInputs` assembles the genuine `L27HurwitzInputs I`; consequently the
`hurwitz` field of `L27StageOneFinishInputs` is no longer an opaque paper
hypothesis.  `toStageOneFinishInputs` builds the whole finish bundle from the
assembly data, the kill-law data, Hasse, the curve budget, and the L27.2
multiplier.

The class-number and the `L`-value are positive on Frobenius discriminants
(`hurwitz_pos`), and the trace fibre is nonzero on every positive Frobenius
discriminant (`orderCount_trace_pos`, `traceCount_pos`).  No class number, curve
count, or probability is set to zero.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL27HurwitzAssembly

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27ClassNumber
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Fiber
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27Scale
open Cogentic.RandomizedL27Siegel
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Stratification
open Cogentic.RandomizedL27TraceClass
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL27Weighted
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The reduced assembly data -/

/-- **The genuinely classical inputs left behind the LP §7 Hurwitz block.**

The class-number side is bundled as `classInput : DirichletClassNumberInput
hurwitz L1`: the imaginary-quadratic order class-number formula, the positivity
of the unit weight and the class number, and the domination of the weighted
class number by the Hurwitz class number.  The analytic side is the explicit
uniform lower bound `l ≤ L(1, χ_D)`, compatible with the Hasse scale
`κ ≤ (classNumberFormulaConstant * l) * √θ`.  The curve side is the finite
weighted Deuring/Waterhouse identity on the Weierstrass model, the domination
of the model count by the abstract order count, and the `j`-line fibre count.
The geometric side is the central trace window and the small-prime prepass.

No field sets a count or a class number to zero; `l` and `c = 1/(2π) · l` are
positive. -/
structure L27HurwitzAssemblyInputs (I : L27_1Inputs) where
  /-- The Hurwitz class number `H(-D)`. -/
  hurwitz : ℤ → ℝ
  /-- The quadratic `L`-value `L(1, χ_D)`. -/
  L1 : ℤ → ℝ
  /-- The Dirichlet class-number formula and the arithmetic positivity data. -/
  classInput : DirichletClassNumberInput hurwitz L1
  /-- The uniform lower bound for `L(1, χ_D)`. -/
  l : ℝ
  /-- The `L`-lower bound is positive. -/
  l_pos : 0 < l
  /-- `l` is a lower bound for the quadratic `L`-value on Frobenius
  discriminants. -/
  l_one_lower : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D
  /-- Nondegeneracy fraction `D(p,j) ≥ θp` on the central window. -/
  θ : ℝ
  /-- The nondegeneracy fraction is positive. -/
  θ_pos : 0 < θ
  /-- The Hasse-scale constant is below the Siegel constant `(1/(2π)) l` at
  scale `√θ`. -/
  kappa_le : I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ
  /-- Smooth orders lie in the central trace window `t² ≤ (4 - θ)p`. -/
  central_trace : CentralTraceWindow I.p I.smooth θ
  /-- The target prime is prime, so the curve model is over a field. -/
  p_prime : ∀ n, (I.p n).Prime
  /-- The explicit finite raw equation-count form of Deuring/Waterhouse. -/
  waterhouse_model : ∀ n,
    WaterhouseWeightedModelCount (I.p n) (p_prime n) hurwitz
  /-- The abstract order count dominates the raw finite curve count. -/
  orderCount_dominates_raw : ∀ n j,
    rawCurveOrderCount I.p p_prime n j ≤ I.orderCount n j
  /-- The `j`-line fibre count. -/
  fiber : JLineFiberInput I.p I.orderCount I.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  p_ge_four : ∀ n, 4 ≤ I.p n

namespace L27HurwitzAssemblyInputs

variable {I : L27_1Inputs}

/-! ## 2. The class-number and `L`-value fields -/

/-- The lower half of the class-number formula carried by the bundle. -/
theorem hurwitzFormulaLower (D : L27HurwitzAssemblyInputs I) :
    HurwitzClassNumberFormulaLower D.hurwitz D.L1 classNumberFormulaConstant :=
  D.classInput.hurwitzFormulaLower

/-- The quadratic `L`-value is positive on Frobenius discriminants. -/
theorem L1_pos (D : L27HurwitzAssemblyInputs I) :
    ∀ E : ℤ, IsFrobeniusDiscriminant E → 0 < D.L1 E :=
  D.classInput.L1_pos

/-- **The `L`-lower bound is exactly the absence of an exceptional
`L(1, χ)` sequence.**  The uniform bound `l ≤ L(1, χ_D)` gives
`DirichletLOneInput`, and the pointwise positivity derived from the
class-number formula turns this into `NoExceptionalLOneSequence`. -/
theorem noExceptional (D : L27HurwitzAssemblyInputs I) :
    NoExceptionalLOneSequence D.L1 := by
  have hDL : DirichletLOneInput D.L1 := ⟨D.l, D.l_pos, D.l_one_lower⟩
  exact (dirichletLOneInput_iff_noExceptionalSequence D.L1_pos).mp hDL

/-- The quadratic `L`-value has an explicit uniform positive lower bound. -/
theorem exists_l_one_lower (D : L27HurwitzAssemblyInputs I) :
    ∃ l : ℝ, DirichletLOneLower D.L1 l :=
  ⟨D.l, D.l_pos, D.l_one_lower⟩

/-- The Hurwitz class number is positive on Frobenius discriminants: it
dominates the positive weighted class number.  This is the no-zero-count check
on the class-number side. -/
theorem hurwitz_pos (D : L27HurwitzAssemblyInputs I) {E : ℤ}
    (hE : IsFrobeniusDiscriminant E) : 0 < D.hurwitz E := by
  have hclass : 0 < D.classInput.classNumber E :=
    D.classInput.classNumber_pos E hE
  have hweight : 0 < D.classInput.weight E :=
    D.classInput.weight_pos E hE
  have hdom : D.classInput.classNumber E / D.classInput.weight E ≤ D.hurwitz E :=
    D.classInput.hurwitz_dominates E hE
  exact lt_of_lt_of_le (div_pos hclass hweight) hdom

/-! ## 3. The Siegel and Deuring fields -/

/-- **The Siegel trace leaf.**  The class-number formula, the positivity of the
weight, the domination by the Hurwitz class number, and the uniform `L`-lower
bound give `H(-D) ≥ (1/(2π) l) √D` on Frobenius-trace discriminants. -/
theorem siegelLower (D : L27HurwitzAssemblyInputs I) :
    HurwitzSiegelLowerTrace I.p D.hurwitz
      (classNumberFormulaConstant * D.l) :=
  hurwitzSiegelLowerTrace_of_classNumberFormula (p := I.p)
    (fun n => I.p_pos n) D.classInput.formula D.classInput.weight_pos
    D.classInput.hurwitz_dominates D.l_pos D.l_one_lower

/-- **The one-sided order-model Deuring/Waterhouse count.**  The explicit finite
weighted model identity, the model domination, and the passage from the
weighted count to the raw class count give
`H(4p - t²) ≤ #curves with trace t`. -/
theorem deuringTraceCountLower (D : L27HurwitzAssemblyInputs I) :
    DeuringTraceCountLower I.p I.orderCount D.hurwitz :=
  deuringTraceCountLower_of_dominated_model D.p_prime
    (fun n => waterhouseWeighted_of_modelCount (D.waterhouse_model n))
    D.orderCount_dominates_raw

/-- The canonical trace fibre attached to the order model.  The parameter keeps
the projection notation `D.traceCount`; its value is independent of `D`. -/
def traceCount (_D : L27HurwitzAssemblyInputs I) : ℕ → ℤ → ℕ :=
  traceCountOfOrder I.p I.orderCount

/-- **The trace-class form of the Deuring count**, on the canonical trace
fibre `traceCountOfOrder`. -/
theorem traceClassLower (D : L27HurwitzAssemblyInputs I) :
    DeuringTraceClassLower I.p D.traceCount D.hurwitz :=
  deuringTraceClassLower_traceCountOfOrder_of_lower D.deuringTraceCountLower

/-- **The order-count containment** of a fixed trace fibre.  This is
unconditional for the canonical trace count. -/
theorem orderCountContainsTrace (D : L27HurwitzAssemblyInputs I) :
    OrderCountContainsTraceClass I.p I.smooth I.orderCount D.traceCount :=
  orderCountContainsTraceClass_traceCountOfOrder I.p I.smooth I.orderCount

/-- The trace fibre is nonzero at every positive Frobenius discriminant.  The
positive Hurwitz class number is dominated by the curve count. -/
theorem orderCount_trace_pos (D : L27HurwitzAssemblyInputs I) {n : ℕ} {t : ℤ}
    (ht : 0 < traceDisc (I.p n) t) :
    0 < I.orderCount n (traceOrder (I.p n) t) := by
  have hdisc : IsFrobeniusDiscriminant (traceDisc (I.p n) t) :=
    ⟨I.p n, I.p_pos n, t, ht, rfl⟩
  have hh : 0 < D.hurwitz (traceDisc (I.p n) t) := D.hurwitz_pos hdisc
  have hle : D.hurwitz (traceDisc (I.p n) t) ≤
      (I.orderCount n (traceOrder (I.p n) t) : ℝ) :=
    D.deuringTraceCountLower n t ht
  have hposR : (0 : ℝ) < (I.orderCount n (traceOrder (I.p n) t) : ℝ) :=
    lt_of_lt_of_le hh hle
  exact_mod_cast hposR

/-- The canonical trace count is nonzero at every positive Frobenius
discriminant. -/
theorem traceCount_pos (D : L27HurwitzAssemblyInputs I) {n : ℕ} {t : ℤ}
    (ht : 0 < traceDisc (I.p n) t) : 0 < D.traceCount n t :=
  D.orderCount_trace_pos ht

/-! ## 4. The geometric fields -/

/-- The discriminant scale, obtained from the central trace window. -/
theorem discScale (D : L27HurwitzAssemblyInputs I) :
    HurwitzDiscriminantScale I.p I.smooth D.θ :=
  hurwitzDiscriminantScale_of_centralTraceWindow D.central_trace

/-- The `j`-line stratification, obtained from the fibre input. -/
theorem jInvariantStrata (D : L27HurwitzAssemblyInputs I) :
    JInvariantStratification I.p I.orderCount I.orderTop :=
  jInvariantStratification_of_fiberInput D.fiber

/-- The Siegel constant `(1/(2π)) l` is positive. -/
theorem siegelConstant_pos (D : L27HurwitzAssemblyInputs I) :
    0 < classNumberFormulaConstant * D.l :=
  mul_pos classNumberFormulaConstant_pos D.l_pos

/-! ## 5. The assembled `L27HurwitzInputs` -/

/-- **The actual `L27HurwitzInputs`.**  Every field is either one of the
reduced inputs of §1 or derived in §§2–4.  In particular the Siegel leaf, the
trace-class Deuring count, the order-count containment, and the discriminant
scale are no longer opaque hypotheses. -/
def toHurwitzInputs (D : L27HurwitzAssemblyInputs I) : L27HurwitzInputs I where
  hurwitz := D.hurwitz
  traceCount := D.traceCount
  c := classNumberFormulaConstant * D.l
  θ := D.θ
  c_pos := D.siegelConstant_pos
  θ_pos := D.θ_pos
  kappa_le := D.kappa_le
  siegel_lower := D.siegelLower
  disc_scale := D.discScale
  trace_class_lower := D.traceClassLower
  orderCount_contains_trace := D.orderCountContainsTrace
  j_invariant_strata := D.jInvariantStrata
  p_ge_four := D.p_ge_four

/-- The assembled bundle has the same Hurwitz class number as the reduced
data. -/
theorem toHurwitzInputs_hurwitz (D : L27HurwitzAssemblyInputs I) :
    D.toHurwitzInputs.hurwitz = D.hurwitz := rfl

/-- The assembled bundle has the canonical trace count. -/
theorem toHurwitzInputs_traceCount (D : L27HurwitzAssemblyInputs I) :
    D.toHurwitzInputs.traceCount = traceCountOfOrder I.p I.orderCount := rfl

/-- The assembled Siegel constant. -/
theorem toHurwitzInputs_c (D : L27HurwitzAssemblyInputs I) :
    D.toHurwitzInputs.c = classNumberFormulaConstant * D.l := rfl

/-! ## 6. Delegation to the downstream L27.1 conclusions -/

/-- Reassemble the smaller `L27DeuringInputs` bundle. -/
def toDeuringInputs (D : L27HurwitzAssemblyInputs I) : L27DeuringInputs I :=
  D.toHurwitzInputs.toDeuringInputs

/-- The per-order Deuring/Lenstra count. -/
theorem deuringSmoothOrderCount (D : L27HurwitzAssemblyInputs I) :
    DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ :=
  D.toHurwitzInputs.deuringSmoothOrderCount

/-- The sharp `2p + 8` curve total. -/
theorem jInvariantCurveTotal (D : L27HurwitzAssemblyInputs I) :
    JInvariantCurveTotal I.p I.orderCount I.orderTop :=
  D.toHurwitzInputs.jInvariantCurveTotal

/-- The paper's `≤ 4p` curve total. -/
theorem hasseWindowCurveTotal (D : L27HurwitzAssemblyInputs I) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  D.toHurwitzInputs.hasseWindowCurveTotal

/-- The bundled `DeuringLenstraCounts` hypothesis. -/
theorem deuringLenstraCounts (D : L27HurwitzAssemblyInputs I) :
    DeuringLenstraCounts I :=
  D.toHurwitzInputs.deuringLenstraCounts

/-- Reassemble `L27PaperInputs` from the assembly data and the five remaining
LP §7 inputs. -/
theorem toPaperInputs (D : L27HurwitzAssemblyInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    L27PaperInputs I :=
  D.toHurwitzInputs.toPaperInputs hhasse h0 h1 h2 hstage

/-- The L27.1 ledger. -/
theorem reduced_ledger (D : L27HurwitzAssemblyInputs I)
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

/-- The manuscript-rate deficit bound. -/
theorem reduced_paper (D : L27HurwitzAssemblyInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop,
      I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  D.toHurwitzInputs.reduced_paper hhasse h0 h1 h2 hstage hbudget hlog

/-- The L27.1 `RatedLeaf`. -/
def toRatedLeaf (D : L27HurwitzAssemblyInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf :=
  D.toHurwitzInputs.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog

/-- The `C5` slot `exp (-2H)`. -/
theorem slot (D : L27HurwitzAssemblyInputs I)
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

/-! ## 7. The stage-one finish bundle rebuilt -/

/-- **The full `L27StageOneFinishInputs`.**  The `hurwitz` field is the genuine
bundle `toHurwitzInputs`, built from the reduced classical data; the remaining
fields are the kill-law data, Hasse, the curve budget, and the L27.2
multiplier. -/
def toStageOneFinishInputs (D : L27HurwitzAssemblyInputs I)
    (S : L27KillLawInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : L27StageOneFinishInputs I where
  killLaw := S
  hurwitz := D.toHurwitzInputs
  hasse := hhasse
  curve_budget := hbudget
  log_factor_subexp := hlog

/-- **The `hurwitz` field of the finish bundle is the assembled bundle.**  This
is the field-by-field replacement of the previously opaque paper field. -/
theorem stageOneFinish_hurwitz (D : L27HurwitzAssemblyInputs I)
    (S : L27KillLawInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    (D.toStageOneFinishInputs S hhasse hbudget hlog).hurwitz =
      D.toHurwitzInputs := rfl

/-- **The full L27.1 reduction from the assembly data.**  The reduced
class-number/`L`-value data, the weighted model identity, the `j`-line fibre
count, the central window, the kill-law data, Hasse, the curve budget, and the
`log₂` multiplier imply both bundled `L27_1Sub` hypotheses and both deficit
conclusions. -/
theorem reduction_of_assembly (D : L27HurwitzAssemblyInputs I)
    (S : L27KillLawInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  (D.toStageOneFinishInputs S hhasse hbudget hlog).reduction

/-! ## 8. Interface with the actual `F_p` curve model -/

/-- **The `j`-line stratification from actual curve classes.**  This is the
form of the fibre input produced by `Cogentic.RandomizedL27Fiber`: the finite
set of curves over `F_p`, its order fibres, the Hasse-window bound, and the
twist-fibre count. -/
theorem jInvariantStrata_of_actualFiber {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hp : ∀ n, 0 < p n) (h : ActualFiberInput p orderCount orderTop) :
    JInvariantStratification p orderCount orderTop :=
  jInvariantStratification_of_fiberInput
    (jLineFiberInput_of_actualFiberInput hp h)

/-- The actual-curve form of the `j`-line fibre input. -/
theorem fiberInput_of_actualFiber {p : ℕ → ℕ}
    {orderCount : ℕ → ℕ → ℕ} {orderTop : ℕ → ℕ}
    (hp : ∀ n, 0 < p n) (h : ActualFiberInput p orderCount orderTop) :
    JLineFiberInput p orderCount orderTop :=
  jLineFiberInput_of_actualFiberInput hp h

/-! ## Axiom audit -/

#print axioms L27HurwitzAssemblyInputs.hurwitzFormulaLower
#print axioms L27HurwitzAssemblyInputs.L1_pos
#print axioms L27HurwitzAssemblyInputs.noExceptional
#print axioms L27HurwitzAssemblyInputs.exists_l_one_lower
#print axioms L27HurwitzAssemblyInputs.hurwitz_pos
#print axioms L27HurwitzAssemblyInputs.siegelLower
#print axioms L27HurwitzAssemblyInputs.deuringTraceCountLower
#print axioms L27HurwitzAssemblyInputs.traceClassLower
#print axioms L27HurwitzAssemblyInputs.orderCountContainsTrace
#print axioms L27HurwitzAssemblyInputs.orderCount_trace_pos
#print axioms L27HurwitzAssemblyInputs.traceCount_pos
#print axioms L27HurwitzAssemblyInputs.discScale
#print axioms L27HurwitzAssemblyInputs.jInvariantStrata
#print axioms L27HurwitzAssemblyInputs.siegelConstant_pos
#print axioms L27HurwitzAssemblyInputs.toHurwitzInputs
#print axioms L27HurwitzAssemblyInputs.toHurwitzInputs_hurwitz
#print axioms L27HurwitzAssemblyInputs.toHurwitzInputs_traceCount
#print axioms L27HurwitzAssemblyInputs.toHurwitzInputs_c
#print axioms L27HurwitzAssemblyInputs.toDeuringInputs
#print axioms L27HurwitzAssemblyInputs.deuringSmoothOrderCount
#print axioms L27HurwitzAssemblyInputs.jInvariantCurveTotal
#print axioms L27HurwitzAssemblyInputs.hasseWindowCurveTotal
#print axioms L27HurwitzAssemblyInputs.deuringLenstraCounts
#print axioms L27HurwitzAssemblyInputs.toPaperInputs
#print axioms L27HurwitzAssemblyInputs.reduced_ledger
#print axioms L27HurwitzAssemblyInputs.reduced_paper
#print axioms L27HurwitzAssemblyInputs.toRatedLeaf
#print axioms L27HurwitzAssemblyInputs.slot
#print axioms L27HurwitzAssemblyInputs.toStageOneFinishInputs
#print axioms L27HurwitzAssemblyInputs.stageOneFinish_hurwitz
#print axioms L27HurwitzAssemblyInputs.reduction_of_assembly
#print axioms jInvariantStrata_of_actualFiber
#print axioms fiberInput_of_actualFiber

end L27HurwitzAssemblyInputs

end

end Cogentic.RandomizedL27HurwitzAssembly
