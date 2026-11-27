import Cogentic.RandomizedL27Hurwitz

/-!
# L27 discriminant scale: the central-trace hypothesis

`Cogentic.RandomizedL27Hurwitz` reduces the Deuring/Lenstra counts to a
Siegel lower bound and the geometric leaf

`HurwitzDiscriminantScale p smooth θ : ∀ n j, smooth n j = true →
  θ * p ≤ 4p - (p + 1 - j)²`.

`HasseBound` only gives `0 ≤ 4p - (p + 1 - j)²`; near the two Hasse endpoints
the quadratic term is `4p`, so the scale inequality is false there.  The
predicate `smooth` in `L27_1Inputs` is an arbitrary field: the interface only
records that a smooth order is realised and bounded by the stage-one cutoff.
Consequently `HasseBound` does **not** imply `HurwitzDiscriminantScale`, and
the scale leaf is a genuine extra geometric hypothesis, not a consequence of
the existing Hasse input.  `hasseBound_not_imply_hurwitzDiscriminantScale`
below gives a concrete countermodel.

The paper's actual restriction is on the Frobenius trace: a counted smooth
order lies in the *central window*

`t² ≤ (4 - θ)p`,  where `t = p + 1 - j`.

This is exactly equivalent, algebraically, to `θp ≤ 4p - t²`; it is the
smallest explicit statement that rules out the Hasse endpoints.  The special
case `θ = 1` is the existing `CentralTrace`, `t² ≤ 3p`, which gives `D ≥ p`.
The stronger paper-side condition `t² ≤ (1 - θ)p` used for `θ < 1` is also
recorded; it implies the central window.

The main reduction replaces the `disc_scale` field of `L27HurwitzInputs` by
the central-window field and reassembles the original bundle.  No count, class
number, or loss is set to zero; no `sorry`, `admit`, `axiom`, or
`native_decide` is used.
-/

namespace Cogentic.RandomizedL27Scale

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

/-! ## 1. The central window in trace coordinates -/

/-- The central Hasse window for the trace `t = p + 1 - j`:
`t² ≤ (4 - θ)p`.  Equivalently, the Frobenius discriminant
`D = 4p - t²` retains a `θ`-fraction of the Hasse width. -/
def InCentralWindow (p : ℕ → ℕ) (θ : ℝ) (n j : ℕ) : Prop :=
  ((hasseTrace (p n) j : ℝ)) ^ 2 ≤ (4 - θ) * (p n : ℝ)

/-- Cast form of the Frobenius discriminant in terms of the trace. -/
theorem frobeniusDisc_cast (p : ℕ) (j : ℕ) :
    ((frobeniusDisc p j : ℤ) : ℝ) =
      4 * (p : ℝ) - ((hasseTrace p j : ℝ)) ^ 2 := by
  unfold frobeniusDisc hasseTrace
  push_cast
  ring

/-- Pointwise form of the equivalence between the discriminant scale and the
central window. -/
theorem discScale_pointwise_iff_centralWindow {p : ℕ → ℕ} {θ : ℝ} {n j : ℕ} :
    θ * (p n : ℝ) ≤ (frobeniusDisc (p n) j : ℝ) ↔
      InCentralWindow p θ n j := by
  unfold InCentralWindow
  rw [frobeniusDisc_cast]
  constructor <;> intro h <;> linarith

/-- **The discriminant scale is exactly the statement that smooth orders lie
in the central window.**  This is the lossless reformulation of
`HurwitzDiscriminantScale`; it identifies the precise geometric content that
`HasseBound` does not supply. -/
theorem hurwitzDiscriminantScale_iff_centralWindow {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} :
    HurwitzDiscriminantScale p smooth θ ↔
      ∀ n j, smooth n j = true → InCentralWindow p θ n j := by
  constructor
  · intro h n j hs
    exact (discScale_pointwise_iff_centralWindow.mp (h n j hs))
  · intro h n j hs
    exact (discScale_pointwise_iff_centralWindow.mpr (h n j hs))

/-- **The smallest explicit central-trace leaf.**  Every smooth order has
trace in the central window `t² ≤ (4 - θ)p`.  This is the geometric hypothesis
needed by `HurwitzDiscriminantScale`; it is stated on the trace alone, with no
reference to the Hurwitz count or the curve model. -/
def CentralTraceWindow (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool) (θ : ℝ) : Prop :=
  ∀ n j, smooth n j = true → InCentralWindow p θ n j

/-- The central-window leaf gives the discriminant scale. -/
theorem hurwitzDiscriminantScale_of_centralTraceWindow {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    (h : CentralTraceWindow p smooth θ) :
    HurwitzDiscriminantScale p smooth θ :=
  hurwitzDiscriminantScale_iff_centralWindow.mpr h

/-- The discriminant scale gives the central-window leaf. -/
theorem centralTraceWindow_of_hurwitzDiscriminantScale {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    (h : HurwitzDiscriminantScale p smooth θ) :
    CentralTraceWindow p smooth θ :=
  hurwitzDiscriminantScale_iff_centralWindow.mp h

/-- The two geometric leaves are equivalent. -/
theorem hurwitzDiscriminantScale_iff_centralTraceWindow {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} :
    HurwitzDiscriminantScale p smooth θ ↔
      CentralTraceWindow p smooth θ :=
  hurwitzDiscriminantScale_iff_centralWindow

/-- **The paper's stronger central-trace inequality.**  For `0 < θ < 1`, the
paper-side condition `t² ≤ (1 - θ)p` places the trace inside the central
window.  It is stronger than necessary for the scale reduction, but it is the
form sometimes used when the counted orders are required to stay near the
centre of the Hasse interval. -/
def CentralTraceFraction (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool) (θ : ℝ) : Prop :=
  ∀ n j, smooth n j = true →
    ((hasseTrace (p n) j : ℝ)) ^ 2 ≤ (1 - θ) * (p n : ℝ)

/-- The paper's `(1 - θ)p` trace bound implies the central window. -/
theorem centralTraceWindow_of_centralTraceFraction {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    (h : CentralTraceFraction p smooth θ) :
    CentralTraceWindow p smooth θ := by
  intro n j hs
  have hp : (0 : ℝ) ≤ (p n : ℝ) := by positivity
  have hle : (1 - θ) * (p n : ℝ) ≤ (4 - θ) * (p n : ℝ) := by
    nlinarith
  exact (h n j hs).trans hle

/-- The paper's `(1 - θ)p` trace bound implies the discriminant scale. -/
theorem hurwitzDiscriminantScale_of_centralTraceFraction {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ}
    (h : CentralTraceFraction p smooth θ) :
    HurwitzDiscriminantScale p smooth θ :=
  hurwitzDiscriminantScale_of_centralTraceWindow
    (centralTraceWindow_of_centralTraceFraction h)

/-- The existing `CentralTrace` is the central window at `θ = 1`. -/
theorem centralTraceWindow_one_of_centralTrace {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} (h : CentralTrace p smooth) :
    CentralTraceWindow p smooth 1 := by
  intro n j hs
  unfold InCentralWindow
  have h1 : (4 : ℝ) - 1 = 3 := by norm_num
  rw [h1]
  exact h n j hs

/-- The `θ = 1` central window is the existing `CentralTrace`. -/
theorem centralTrace_of_centralTraceWindow_one {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} (h : CentralTraceWindow p smooth 1) :
    CentralTrace p smooth := by
  intro n j hs
  have hw := h n j hs
  unfold InCentralWindow at hw
  have h1 : (4 : ℝ) - 1 = 3 := by norm_num
  rw [h1] at hw
  exact hw

/-- The two `θ = 1` formulations agree. -/
theorem centralTraceWindow_one_iff_centralTrace {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} :
    CentralTraceWindow p smooth 1 ↔ CentralTrace p smooth :=
  ⟨centralTrace_of_centralTraceWindow_one, centralTraceWindow_one_of_centralTrace⟩

/-- **Hasse alone does not give the scale.**  A concrete model: at `p = 4`
the order `j = 9` sits exactly on the Hasse endpoint, has Frobenius
discriminant `0`, and is declared smooth.  `HasseBound` holds (the order count
is nonzero only at that admissible order), but `θ = 1` fails.  Thus the central
window must be an explicit hypothesis of the L27 reduction. -/
theorem hasseBound_not_imply_hurwitzDiscriminantScale :
    ∃ (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ) (smooth : ℕ → ℕ → Bool),
      HasseBound p orderCount ∧ ¬ HurwitzDiscriminantScale p smooth 1 := by
  refine ⟨fun _ => 4, fun _ j => if j = 9 then 1 else 0,
    fun _ j => if j = 9 then true else false, ?_, ?_⟩
  · intro n j hj
    by_cases h : j = 9
    · subst j
      norm_num
    · simp [h] at hj
  · intro h
    have h9 := h 0 9 (by simp)
    norm_num [frobeniusDisc, hasseTrace] at h9

/-! ## 2. Reduction to `L27HurwitzInputs` -/

/-- **The Hurwitz bundle with the scale field replaced by the central window.**

This is `L27HurwitzInputs` with `disc_scale` replaced by the strictly more
primitive geometric hypothesis `central_trace`.  Every other field, including
the Hurwitz count, the Deuring trace class and the `j`-line stratification, is
unchanged. -/
structure L27HurwitzWindowInputs (I : L27_1Inputs) where
  /-- The Hurwitz class number `H(-D)`. -/
  hurwitz : ℤ → ℝ
  /-- Number of curves over `F_p` with a given Frobenius trace. -/
  traceCount : ℕ → ℤ → ℕ
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
  /-- Smooth traces lie in the central window `t² ≤ (4 - θ)p`. -/
  central_trace : CentralTraceWindow I.p I.smooth θ
  /-- One-sided Deuring/Waterhouse at fixed trace. -/
  trace_class_lower : DeuringTraceClassLower I.p traceCount hurwitz
  /-- Curves of a fixed trace are contained in the curves of that order. -/
  orderCount_contains_trace :
    OrderCountContainsTraceClass I.p I.smooth I.orderCount traceCount
  /-- The `j`-line stratification of the curves. -/
  j_invariant_strata : JInvariantStratification I.p I.orderCount I.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  p_ge_four : ∀ n, 4 ≤ I.p n

namespace L27HurwitzWindowInputs

variable {I : L27_1Inputs}

/-- The central-window input reconstructs the original `L27HurwitzInputs` by
proving the `disc_scale` field from the trace bound. -/
def toHurwitzInputs (D : L27HurwitzWindowInputs I) : L27HurwitzInputs I where
  hurwitz := D.hurwitz
  traceCount := D.traceCount
  c := D.c
  θ := D.θ
  c_pos := D.c_pos
  θ_pos := D.θ_pos
  kappa_le := D.kappa_le
  siegel_lower := D.siegel_lower
  disc_scale := hurwitzDiscriminantScale_of_centralTraceWindow D.central_trace
  trace_class_lower := D.trace_class_lower
  orderCount_contains_trace := D.orderCount_contains_trace
  j_invariant_strata := D.j_invariant_strata
  p_ge_four := D.p_ge_four

/-- Reassembly of `L27DeuringInputs` from the central-window bundle. -/
def toDeuringInputs (D : L27HurwitzWindowInputs I) : L27DeuringInputs I :=
  D.toHurwitzInputs.toDeuringInputs

/-- The per-order Deuring/Lenstra bound from the central-window bundle. -/
theorem deuringSmoothOrderCount (D : L27HurwitzWindowInputs I) :
    DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ :=
  D.toHurwitzInputs.deuringSmoothOrderCount

/-- The sharp `2p + 8` total. -/
theorem jInvariantCurveTotal (D : L27HurwitzWindowInputs I) :
    JInvariantCurveTotal I.p I.orderCount I.orderTop :=
  D.toHurwitzInputs.jInvariantCurveTotal

/-- The paper's `≤ 4p` total. -/
theorem hasseWindowCurveTotal (D : L27HurwitzWindowInputs I) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  D.toHurwitzInputs.hasseWindowCurveTotal

/-- The bundled `DeuringLenstraCounts` hypothesis of `L27_1Sub`. -/
theorem deuringLenstraCounts (D : L27HurwitzWindowInputs I) :
    DeuringLenstraCounts I :=
  D.toHurwitzInputs.deuringLenstraCounts

/-- Reassemble `L27PaperInputs` from the central-window bundle. -/
theorem toPaperInputs (D : L27HurwitzWindowInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    L27PaperInputs I :=
  D.toHurwitzInputs.toPaperInputs hhasse h0 h1 h2 hstage

/-- The L27.1 ledger from the central-window bundle. -/
theorem reduced_ledger (D : L27HurwitzWindowInputs I)
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

/-- The manuscript-rate deficit bound from the central-window bundle. -/
theorem reduced_paper (D : L27HurwitzWindowInputs I)
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

/-- The L27.1 `RatedLeaf` from the central-window bundle. -/
def toRatedLeaf (D : L27HurwitzWindowInputs I)
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
theorem slot (D : L27HurwitzWindowInputs I)
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

end L27HurwitzWindowInputs

/-! ## 3. Direct construction of `L27HurwitzInputs` -/

/-- **Direct reduction.**  The central-window trace hypothesis, the Siegel
bound, the trace-class count, the order-count containment, the `j`-line
stratification and the small-prime prepass reassemble `L27HurwitzInputs`
without ever assuming the discriminant scale separately. -/
def toHurwitzInputs_of_central {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ) (traceCount : ℕ → ℤ → ℕ) {c θ : ℝ}
    (c_pos : 0 < c) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ c * Real.sqrt θ)
    (siegel : HurwitzSiegelLowerTrace I.p hurwitz c)
    (central : CentralTraceWindow I.p I.smooth θ)
    (trace : DeuringTraceClassLower I.p traceCount hurwitz)
    (contains : OrderCountContainsTraceClass I.p I.smooth I.orderCount traceCount)
    (strata : JInvariantStratification I.p I.orderCount I.orderTop)
    (hp4 : ∀ n, 4 ≤ I.p n) :
    L27HurwitzInputs I where
  hurwitz := hurwitz
  traceCount := traceCount
  c := c
  θ := θ
  c_pos := c_pos
  θ_pos := θ_pos
  kappa_le := kappa_le
  siegel_lower := siegel
  disc_scale := hurwitzDiscriminantScale_of_centralTraceWindow central
  trace_class_lower := trace
  orderCount_contains_trace := contains
  j_invariant_strata := strata
  p_ge_four := hp4

/-- Direct reduction from the paper's stronger `(1 - θ)p` trace bound. -/
def toHurwitzInputs_of_centralTraceFraction {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ) (traceCount : ℕ → ℤ → ℕ) {c θ : ℝ}
    (c_pos : 0 < c) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ c * Real.sqrt θ)
    (siegel : HurwitzSiegelLowerTrace I.p hurwitz c)
    (central : CentralTraceFraction I.p I.smooth θ)
    (trace : DeuringTraceClassLower I.p traceCount hurwitz)
    (contains : OrderCountContainsTraceClass I.p I.smooth I.orderCount traceCount)
    (strata : JInvariantStratification I.p I.orderCount I.orderTop)
    (hp4 : ∀ n, 4 ≤ I.p n) :
    L27HurwitzInputs I :=
  toHurwitzInputs_of_central hurwitz traceCount c_pos θ_pos kappa_le siegel
    (centralTraceWindow_of_centralTraceFraction central) trace contains strata hp4

/-- **Direct reduction from the existing `θ = 1` central trace.**  This is the
smallest form of the paper hypothesis already named in
`RandomizedL27Hurwitz`: smooth orders satisfy `t² ≤ 3p`, so `D ≥ p` and the
Hasse-scale constant is `c` rather than `c√θ`. -/
def toHurwitzInputs_of_centralTrace_one {I : L27_1Inputs}
    (hurwitz : ℤ → ℝ) (traceCount : ℕ → ℤ → ℕ) {c : ℝ}
    (c_pos : 0 < c) (kappa_le : I.κ ≤ c)
    (siegel : HurwitzSiegelLowerTrace I.p hurwitz c)
    (central : CentralTrace I.p I.smooth)
    (trace : DeuringTraceClassLower I.p traceCount hurwitz)
    (contains : OrderCountContainsTraceClass I.p I.smooth I.orderCount traceCount)
    (strata : JInvariantStratification I.p I.orderCount I.orderTop)
    (hp4 : ∀ n, 4 ≤ I.p n) :
    L27HurwitzInputs I :=
  toHurwitzInputs_of_central hurwitz traceCount c_pos zero_lt_one
    (by simpa using kappa_le) siegel
    (centralTraceWindow_one_of_centralTrace central) trace contains strata hp4

/-- **Capstone reduction.**  The central-window bundle plus the five remaining
LP §7 inputs implies both bundled `L27_1Sub` hypotheses and both deficit
conclusions. -/
theorem reduction_of_scale {I : L27_1Inputs} (D : L27HurwitzWindowInputs I)
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

/-- The Deuring half of the capstone from the central-window bundle. -/
theorem deuringLenstraCounts_of_scale {I : L27_1Inputs}
    (D : L27HurwitzWindowInputs I) : DeuringLenstraCounts I :=
  D.deuringLenstraCounts

/-- **No-loss check.**  The central-window field and the original discriminant
scale field carry the same geometric content; the central form simply exposes
the trace inequality that the paper assumes. -/
theorem centralTraceWindow_iff_discScale {p : ℕ → ℕ}
    {smooth : ℕ → ℕ → Bool} {θ : ℝ} :
    CentralTraceWindow p smooth θ ↔ HurwitzDiscriminantScale p smooth θ :=
  hurwitzDiscriminantScale_iff_centralTraceWindow.symm

/-! ## Axiom audit -/

#print axioms frobeniusDisc_cast
#print axioms discScale_pointwise_iff_centralWindow
#print axioms hurwitzDiscriminantScale_iff_centralWindow
#print axioms hurwitzDiscriminantScale_of_centralTraceWindow
#print axioms centralTraceWindow_of_hurwitzDiscriminantScale
#print axioms hurwitzDiscriminantScale_iff_centralTraceWindow
#print axioms centralTraceWindow_of_centralTraceFraction
#print axioms hurwitzDiscriminantScale_of_centralTraceFraction
#print axioms centralTraceWindow_one_of_centralTrace
#print axioms centralTrace_of_centralTraceWindow_one
#print axioms centralTraceWindow_one_iff_centralTrace
#print axioms hasseBound_not_imply_hurwitzDiscriminantScale
#print axioms L27HurwitzWindowInputs.toHurwitzInputs
#print axioms L27HurwitzWindowInputs.toDeuringInputs
#print axioms L27HurwitzWindowInputs.deuringLenstraCounts
#print axioms L27HurwitzWindowInputs.toPaperInputs
#print axioms L27HurwitzWindowInputs.reduced_ledger
#print axioms L27HurwitzWindowInputs.reduced_paper
#print axioms L27HurwitzWindowInputs.toRatedLeaf
#print axioms L27HurwitzWindowInputs.slot
#print axioms toHurwitzInputs_of_central
#print axioms toHurwitzInputs_of_centralTraceFraction
#print axioms toHurwitzInputs_of_centralTrace_one
#print axioms reduction_of_scale
#print axioms deuringLenstraCounts_of_scale
#print axioms centralTraceWindow_iff_discScale

end

end Cogentic.RandomizedL27Scale
