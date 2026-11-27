import Cogentic.RandomizedL27_1Sub

/-!
# L27 analytic reduction: the smallest paper-level elliptic and Deuring inputs

`Cogentic.RandomizedL27_1Sub` proves the L27.1/L27.2 conclusions from two
bundled paper-level hypotheses:

* `DeuringLenstraCounts` — the smooth-order Deuring/Hurwitz lower bound together
  with the `≤ 4p` total Hasse-window count;
* `EllipticCurveGroupLaw` — Hasse's theorem, the gcd-exit lemma, and the
  stage-one success bound.

This file splits each bundle into its smallest independent paper-level parts and
proves that those parts imply the bundles.  No elliptic-curve existence,
Hurwitz class-number formula, or group-law correctness is reproved here: the
reduction only uses the elementary chain already established in
`RandomizedL27_1Sub`.

The paper-level inputs retained here are:

* `DeuringSmoothOrderCount` — every stage-one-smooth order `j` in the Hasse
  window is realised by at least `κ√p` curves (Deuring's theorem plus the
  Hurwitz class-number lower bound);
* `HasseWindowCurveTotal` — the Hasse window contains at most `4p` curves;
* `HasseBound` — Hasse's theorem `|#E(F_p) - (p+1)| ≤ 2√p` (reused from
  `RandomizedL27_1`);
* `GCDExitNonneg`, `GCDExitLeInv`, `GCDExitLeFailure` — the three components of
  the gcd-exit lemma over `Z/nZ`;
* `StageOneSmoothMultiplicative` — the division-free form
  `SC ≤ success · log y · CT` of the stage-one success bound, equivalent to
  `StageOneSuccess` when `y > 1` and `CT > 0`.

`L27PaperInputs` bundles exactly these statements.  `L27AnalyticCertificate`
adds the curve budget and the `log₂` subexponential multiplier and produces the
same `RatedLeaf`, ledger, and manuscript-rate conclusions as
`RandomizedL27_1Sub`.

**Why the two Deuring fields are not discharged from the existing modules.**
`RandomizedHasseIncidence` and `RandomizedEllipticAndGaussian` provide the
dyadic *Hasse-interval incidence* estimate: a bound on the number of prime
centres `p` whose interval `[(p+1)-2√p, (p+1)+2√p]` contains many witnesses
from a fixed set.  That is an exceptional-prime deletion statement, not a count
of curves over `F_p` by order; it gives neither the per-order Hurwitz lower
bound nor the total `4p` curve count.  Likewise
`RandomizedEllipticAndGaussian` proves recursive-splitting failure bounds
*conditional on an elliptic splitter*, not the group law or Hasse's theorem for
`#E(F_p)`.  Those estimates therefore cannot discharge
`DeuringSmoothOrderCount`, `HasseWindowCurveTotal`, or `HasseBound`; the present
file keeps exactly those (and the three gcd-exit facts and the stage-one
success bound) as the smallest paper-level `Prop`s, and reuses all the
elementary Hasse-interval arithmetic, Chernoff, union-bound, fraction, and
curve-budget lemmas of `RandomizedL27_1Sub`.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL27Analytic

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The Deuring/Lenstra estimate, split into two paper-level parts -/

/-- **Deuring/Lenstra, per smooth order.**  Every stage-one-smooth order in the
Hasse window is realised by at least `κ√p` curves over `F_p`.  This is the
pointwise Hurwitz class-number lower bound of LP §7; the factor `√p` is the
Deuring normalization. -/
def DeuringSmoothOrderCount (p : ℕ → ℕ) (smooth : ℕ → ℕ → Bool)
    (orderCount : ℕ → ℕ → ℕ) (κ : ℝ) : Prop :=
  ∀ n j, smooth n j = true → κ * Real.sqrt (p n) ≤ (orderCount n j : ℝ)

/-- **The Hasse-window total count.**  Summing the Deuring order counts over
the integer Hasse window gives at most `4p` curves.  This is the total curve
count of LP §7, separated from the per-order lower bound. -/
def HasseWindowCurveTotal (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) : Prop :=
  ∀ n, curveTotal orderCount orderTop n ≤ 4 * (p n : ℝ)

/-- The two Deuring/Lenstra components imply the bundled
`DeuringLenstraCounts` hypothesis of `L27_1Sub`. -/
theorem deuringLenstraCounts_of_components {I : L27_1Inputs}
    (hcount : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ)
    (htotal : HasseWindowCurveTotal I.p I.orderCount I.orderTop) :
    DeuringLenstraCounts I :=
  ⟨hcount, htotal⟩

/-- Conversely, the bundled Deuring/Lenstra hypothesis gives the per-order
part. -/
theorem deuringSmoothOrderCount_of_counts {I : L27_1Inputs}
    (h : DeuringLenstraCounts I) :
    DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ :=
  h.1

/-- Conversely, the bundled Deuring/Lenstra hypothesis gives the total-window
part. -/
theorem hasseWindowCurveTotal_of_counts {I : L27_1Inputs}
    (h : DeuringLenstraCounts I) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  h.2

/-- The split of `DeuringLenstraCounts` is exact: the bundle is definitionally
the conjunction of its two paper-level parts. -/
theorem deuringLenstraCounts_iff_components {I : L27_1Inputs} :
    DeuringLenstraCounts I ↔
      DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ ∧
        HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  Iff.rfl

/-! ## 2. The elliptic-curve group-law estimate, split into its parts -/

/-- **Gcd-exit nonnegativity.**  The bad singular/gcd-exit probability is a
probability, hence nonnegative. -/
def GCDExitNonneg (gcdFail : ℕ → ℝ) : Prop :=
  ∀ n, 0 ≤ gcdFail n

/-- **Gcd-exit probability bound.**  A random Weierstrass curve that is
singular modulo the target prime has gcd-exit probability at most `1/p`. -/
def GCDExitLeInv (p : ℕ → ℕ) (gcdFail : ℕ → ℝ) : Prop :=
  ∀ n, gcdFail n ≤ 1 / (p n : ℝ)

/-- **Gcd-exit containment.**  The bad all-singular event is contained in the
no-factor event. -/
def GCDExitLeFailure (gcdFail noFactor : ℕ → ℝ) : Prop :=
  ∀ n, gcdFail n ≤ noFactor n

/-- The three gcd-exit components imply the bundled `GCDExitBound` hypothesis
of `L27_1Sub`. -/
theorem gcdExitBound_of_components {p : ℕ → ℕ} {gcdFail noFactor : ℕ → ℝ}
    (h0 : GCDExitNonneg gcdFail)
    (h1 : GCDExitLeInv p gcdFail)
    (h2 : GCDExitLeFailure gcdFail noFactor) :
    GCDExitBound p gcdFail noFactor :=
  ⟨h0, h1, h2⟩

/-- Conversely, `GCDExitBound` gives nonnegativity. -/
theorem gcdExitNonneg_of_bound {p : ℕ → ℕ} {gcdFail noFactor : ℕ → ℝ}
    (h : GCDExitBound p gcdFail noFactor) : GCDExitNonneg gcdFail :=
  h.1

/-- Conversely, `GCDExitBound` gives the `1/p` bound. -/
theorem gcdExitLeInv_of_bound {p : ℕ → ℕ} {gcdFail noFactor : ℕ → ℝ}
    (h : GCDExitBound p gcdFail noFactor) : GCDExitLeInv p gcdFail :=
  h.2.1

/-- Conversely, `GCDExitBound` gives containment in the no-factor event. -/
theorem gcdExitLeFailure_of_bound {p : ℕ → ℕ} {gcdFail noFactor : ℕ → ℝ}
    (h : GCDExitBound p gcdFail noFactor) : GCDExitLeFailure gcdFail noFactor :=
  h.2.2

/-- The split of `GCDExitBound` is exact. -/
theorem gcdExitBound_iff_components {p : ℕ → ℕ} {gcdFail noFactor : ℕ → ℝ} :
    GCDExitBound p gcdFail noFactor ↔
      GCDExitNonneg gcdFail ∧ GCDExitLeInv p gcdFail ∧
        GCDExitLeFailure gcdFail noFactor :=
  Iff.rfl

/-- **Division-free stage-one success bound.**  On the event that the curve
order is stage-one smooth, a random point is killed by the stage-one scalar with
probability at least `1 / log y`.  Cleared of the two positive denominators,
this is `SC ≤ success · log y · CT`. -/
def StageOneSmoothMultiplicative (smoothCurves curveTotal : ℕ → ℝ)
    (y success : ℕ → ℝ) : Prop :=
  ∀ n, smoothCurves n ≤ success n * Real.log (y n) * curveTotal n

/-- The division-free stage-one bound implies the bundled `StageOneSuccess`
hypothesis, using `CT > 0` and `log y > 0`. -/
theorem stageOneSuccess_of_multiplicative {I : L27_1Inputs}
    (h : StageOneSmoothMultiplicative I.SC I.CT I.y I.success) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success := by
  intro n
  have hCT : 0 < I.CT n := I.curveTotal_pos n
  have hlog : 0 < Real.log (I.y n) := I.log_y_pos n
  have hn : I.SC n ≤ I.success n * Real.log (I.y n) * I.CT n := h n
  change (I.SC n / I.CT n) / Real.log (I.y n) ≤ I.success n
  rw [div_le_iff₀ hlog, div_le_iff₀ hCT]
  exact hn

/-- Conversely, `StageOneSuccess` gives the division-free form. -/
theorem stageOneSmoothMultiplicative_of_success {I : L27_1Inputs}
    (h : StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    StageOneSmoothMultiplicative I.SC I.CT I.y I.success := by
  intro n
  have hCT : 0 < I.CT n := I.curveTotal_pos n
  have hlog : 0 < Real.log (I.y n) := I.log_y_pos n
  have hn := h n
  change (I.SC n / I.CT n) / Real.log (I.y n) ≤ I.success n at hn
  rw [div_le_iff₀ hlog, div_le_iff₀ hCT] at hn
  exact hn

/-- The division-free and divided forms of the stage-one bound are equivalent
under the positivity already carried by `L27_1Inputs`. -/
theorem stageOneSuccess_iff_multiplicative {I : L27_1Inputs} :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success ↔
      StageOneSmoothMultiplicative I.SC I.CT I.y I.success :=
  ⟨stageOneSmoothMultiplicative_of_success, stageOneSuccess_of_multiplicative⟩

/-- The two elliptic components (Hasse, gcd exits, stage-one success) imply the
bundled `EllipticCurveGroupLaw` hypothesis of `L27_1Sub`. -/
theorem ellipticCurveGroupLaw_of_components {I : L27_1Inputs}
    (hhasse : HasseBound I.p I.orderCount)
    (hgcd : GCDExitBound I.p I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    EllipticCurveGroupLaw I :=
  ⟨hhasse, hgcd, hstage⟩

/-- The split of `EllipticCurveGroupLaw` into Hasse, the gcd-exit lemma, and
the stage-one success bound is exact. -/
theorem ellipticCurveGroupLaw_iff_components {I : L27_1Inputs} :
    EllipticCurveGroupLaw I ↔
      HasseBound I.p I.orderCount ∧
        GCDExitBound I.p I.gcdFail (fun n => 1 - I.success n) ∧
          StageOneSuccess
            (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success :=
  Iff.rfl

/-! ## 3. The bundled smallest paper-level inputs -/

/-- **The smallest explicit paper-level inputs of L27.1.**  Every field is a
single named theorem from LP §7:

* `DeuringSmoothOrderCount` — Deuring plus the Hurwitz class-number bound;
* `HasseWindowCurveTotal` — the total `≤ 4p` curve count;
* `hasse_bound` — Hasse's theorem (reused from `RandomizedL27_1`);
* the three `GCDExit*` fields — Lemma 7.2 over `Z/nZ`;
* `stage_one_smooth_success` — the stage-one smooth-order success bound.

No elementary counting, interval arithmetic, Chernoff step, or curve-budget
manipulation is included; those are proved in `RandomizedL27_1Sub`. -/
structure L27PaperInputs (I : L27_1Inputs) where
  /-- Deuring/Hurwitz per smooth order. -/
  deuring_smooth_order_count : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ
  /-- Total number of curves in the Hasse window is at most `4p`. -/
  hasse_window_curve_total : HasseWindowCurveTotal I.p I.orderCount I.orderTop
  /-- Hasse's theorem. -/
  hasse_bound : HasseBound I.p I.orderCount
  /-- Nonnegativity of the gcd-exit probability. -/
  gcd_exit_nonneg : GCDExitNonneg I.gcdFail
  /-- Gcd-exit probability at most `1/p`. -/
  gcd_exit_le_inv : GCDExitLeInv I.p I.gcdFail
  /-- The gcd-exit event is contained in the no-factor event. -/
  gcd_exit_le_failure : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n)
  /-- Stage-one success on a smooth order. -/
  stage_one_smooth_success :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success

namespace L27PaperInputs

/-- The bundled Deuring/Lenstra hypothesis. -/
theorem deuring {I : L27_1Inputs} (P : L27PaperInputs I) :
    DeuringLenstraCounts I := by
  obtain ⟨hcount, htotal, -, -, -, -, -⟩ := P
  exact deuringLenstraCounts_of_components hcount htotal

/-- The bundled elliptic-curve group-law hypothesis. -/
theorem elliptic {I : L27_1Inputs} (P : L27PaperInputs I) :
    EllipticCurveGroupLaw I := by
  obtain ⟨-, -, hhasse, h0, h1, h2, hstage⟩ := P
  exact ellipticCurveGroupLaw_of_components hhasse
    (gcdExitBound_of_components h0 h1 h2) hstage

/-- The Deuring/Lenstra smooth-curve lower bound, through the existing
`RandomizedL27_1Sub` reduction. -/
theorem deuringSmoothCount {I : L27_1Inputs} (P : L27PaperInputs I) (n : ℕ) :
    I.κ * Real.sqrt (I.p n) * I.psi n ≤ I.SC n :=
  Cogentic.RandomizedL27_1Sub.deuringSmoothCount_of I (deuring P) n

/-- The smooth-fraction lower bound `κψ/(4√p) ≤ SF`. -/
theorem smoothFraction_lower {I : L27_1Inputs} (P : L27PaperInputs I) (n : ℕ) :
    I.κ * I.psi n / (4 * Real.sqrt (I.p n)) ≤ I.SF n :=
  Cogentic.RandomizedL27_1Sub.smoothFraction_lower_of I (deuring P) n

/-- The per-curve LP density lower bound. -/
theorem cRate_mul_density_le_success {I : L27_1Inputs} (P : L27PaperInputs I) (n : ℕ) :
    I.cRate * I.D n ≤ I.success n :=
  Cogentic.RandomizedL27_1Sub.cRate_mul_density_le_success_of I (deuring P) (elliptic P) n

/-- The joint failure bound of the independent curve draws. -/
theorem splitFail_le_exp {I : L27_1Inputs} (P : L27PaperInputs I) (n : ℕ) :
    I.splitFail n ≤ Real.exp (-(I.cRate * I.rate n)) :=
  Cogentic.RandomizedL27_1Sub.splitFail_le_exp_of I (deuring P) (elliptic P) n

/-- The `exp (-2H)` ledger, from the paper inputs, the curve budget, and the
`log₂` subexponential multiplier. -/
theorem reduced_ledger {I : L27_1Inputs} (P : L27PaperInputs I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  Cogentic.RandomizedL27_1Sub.reduced_ledger I (deuring P) (elliptic P) hbudget hlog

/-- The manuscript-rate deficit bound. -/
theorem reduced_paper {I : L27_1Inputs} (P : L27PaperInputs I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  Cogentic.RandomizedL27_1Sub.reduced_paper I (deuring P) (elliptic P) hbudget hlog

/-- The L27.1 `RatedLeaf` assembled from the smallest paper-level inputs. -/
def toRatedLeaf {I : L27_1Inputs} (P : L27PaperInputs I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf :=
  Cogentic.RandomizedL27_1Sub.toRatedLeaf I (deuring P) (elliptic P) hbudget hlog

/-- The `C5` slot `exp (-2H)` for the assembled leaf. -/
theorem slot {I : L27_1Inputs} (P : L27PaperInputs I)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop,
      (toRatedLeaf P hbudget hlog).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  Cogentic.RandomizedL27_1Sub.toRatedLeaf_slot I (deuring P) (elliptic P) hbudget hlog

/-- Compatibility: the paper-level inputs of an already-bundled `L27_1Inputs`
are exactly the fields isolated above. -/
theorem ofInputs (I : L27_1Inputs) : L27PaperInputs I where
  deuring_smooth_order_count := I.deuring_count
  hasse_window_curve_total := I.curve_total_le
  hasse_bound := I.hasse
  gcd_exit_nonneg := I.gcd_exit.1
  gcd_exit_le_inv := I.gcd_exit.2.1
  gcd_exit_le_failure := I.gcd_exit.2.2
  stage_one_smooth_success := I.stage_one

end L27PaperInputs

/-! ## 4. Adding the curve budget and the recursive multiplier -/

/-- **An L27 analytic certificate.**  The smallest paper-level elliptic inputs,
the paper's curve-count choice (`CurveBudget`), and the L27.2 `log₂`
subexponential multiplier.  This is exactly the data consumed by
`RandomizedL27_1Sub.reduced_ledger`, `reduced_paper`, and `toRatedLeaf`. -/
structure L27AnalyticCertificate (I : L27_1Inputs) extends L27PaperInputs I where
  /-- The paper's curve-count choice. -/
  curve_budget : CurveBudget I.p I.y I.psi I.curves I.κ I.η
  /-- The L27.2 recursive multiplier. -/
  log_factor_subexp : LogFactorSubexp I.cofactor

namespace L27AnalyticCertificate

/-- The certificate's bundled Deuring/Lenstra hypothesis. -/
theorem deuring {I : L27_1Inputs} (C : L27AnalyticCertificate I) :
    DeuringLenstraCounts I :=
  L27PaperInputs.deuring (L27AnalyticCertificate.toL27PaperInputs C)

/-- The certificate's bundled elliptic group-law hypothesis. -/
theorem elliptic {I : L27_1Inputs} (C : L27AnalyticCertificate I) :
    EllipticCurveGroupLaw I :=
  L27PaperInputs.elliptic (L27AnalyticCertificate.toL27PaperInputs C)

/-- The L27.1/L27.2 `exp (-2H)` ledger. -/
theorem ledger {I : L27_1Inputs} (C : L27AnalyticCertificate I) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L27PaperInputs.reduced_ledger (L27AnalyticCertificate.toL27PaperInputs C)
    (L27AnalyticCertificate.curve_budget C) (L27AnalyticCertificate.log_factor_subexp C)

/-- The manuscript-rate deficit bound. -/
theorem paper {I : L27_1Inputs} (C : L27AnalyticCertificate I) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  L27PaperInputs.reduced_paper (L27AnalyticCertificate.toL27PaperInputs C)
    (L27AnalyticCertificate.curve_budget C) (L27AnalyticCertificate.log_factor_subexp C)

/-- The `RatedLeaf` assembled from the certificate. -/
def toRatedLeaf {I : L27_1Inputs} (C : L27AnalyticCertificate I) : RatedLeaf :=
  L27PaperInputs.toRatedLeaf (L27AnalyticCertificate.toL27PaperInputs C)
    (L27AnalyticCertificate.curve_budget C) (L27AnalyticCertificate.log_factor_subexp C)

/-- The `C5` slot `exp (-2H)` for the certificate's leaf. -/
theorem slot {I : L27_1Inputs} (C : L27AnalyticCertificate I) :
    ∀ᶠ n : ℕ in atTop,
      (toRatedLeaf C).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  (toRatedLeaf C).slot

end L27AnalyticCertificate

/-! ## 5. Capstone reductions -/

/-- **The full reduction from the smallest components.**  The per-order Deuring
bound, the total-window bound, Hasse, the three gcd-exit facts, and the
stage-one smooth success bound imply both bundled `L27_1Sub` hypotheses and its
two deficit conclusions. -/
theorem reduction_of_components {I : L27_1Inputs}
    (hcount : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ)
    (htotal : HasseWindowCurveTotal I.p I.orderCount I.orderTop)
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
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) := by
  let P : L27PaperInputs I :=
    { deuring_smooth_order_count := hcount
      hasse_window_curve_total := htotal
      hasse_bound := hhasse
      gcd_exit_nonneg := h0
      gcd_exit_le_inv := h1
      gcd_exit_le_failure := h2
      stage_one_smooth_success := hstage }
  exact ⟨L27PaperInputs.deuring P, L27PaperInputs.elliptic P,
    L27PaperInputs.reduced_ledger P hbudget hlog,
    L27PaperInputs.reduced_paper P hbudget hlog⟩

/-- **The full reduction from the division-free stage-one form.**  Same as
`reduction_of_components`, but the stage-one input is the paper's multiplicative
bound `SC ≤ success · log y · CT`. -/
theorem reduction_of_multiplicative {I : L27_1Inputs}
    (hcount : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ)
    (htotal : HasseWindowCurveTotal I.p I.orderCount I.orderTop)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSmoothMultiplicative I.SC I.CT I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  reduction_of_components hcount htotal hhasse h0 h1 h2
    (stageOneSuccess_of_multiplicative hstage) hbudget hlog

/-- **The full certificate theorem.**  An `L27AnalyticCertificate` yields both
bundled hypotheses, the ledger, the manuscript rate, and the `RatedLeaf`. -/
theorem reduction_of_certificate {I : L27_1Inputs}
    (C : L27AnalyticCertificate I) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  ⟨L27AnalyticCertificate.deuring C, L27AnalyticCertificate.elliptic C,
    L27AnalyticCertificate.ledger C, L27AnalyticCertificate.paper C⟩

/-- **Compatibility with the bundled `L27_1Inputs`.**  Reconstructing the paper
inputs from the parent structure and applying the certificate gives the same
ledger as `RandomizedL27_1Sub.reduced_ledger_inputs`. -/
theorem reduced_ledger_inputs_via (I : L27_1Inputs) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L27PaperInputs.reduced_ledger (L27PaperInputs.ofInputs I)
    I.curve_budget I.logFactor_subexp

/-- The manuscript-rate compatibility theorem. -/
theorem reduced_paper_inputs_via (I : L27_1Inputs) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  L27PaperInputs.reduced_paper (L27PaperInputs.ofInputs I)
    I.curve_budget I.logFactor_subexp

/-! ## Axiom audit -/

#print axioms deuringLenstraCounts_of_components
#print axioms deuringSmoothOrderCount_of_counts
#print axioms hasseWindowCurveTotal_of_counts
#print axioms deuringLenstraCounts_iff_components
#print axioms gcdExitBound_of_components
#print axioms gcdExitNonneg_of_bound
#print axioms gcdExitLeInv_of_bound
#print axioms gcdExitLeFailure_of_bound
#print axioms gcdExitBound_iff_components
#print axioms stageOneSuccess_of_multiplicative
#print axioms stageOneSmoothMultiplicative_of_success
#print axioms stageOneSuccess_iff_multiplicative
#print axioms ellipticCurveGroupLaw_of_components
#print axioms ellipticCurveGroupLaw_iff_components
#print axioms L27PaperInputs.deuring
#print axioms L27PaperInputs.elliptic
#print axioms L27PaperInputs.deuringSmoothCount
#print axioms L27PaperInputs.smoothFraction_lower
#print axioms L27PaperInputs.cRate_mul_density_le_success
#print axioms L27PaperInputs.splitFail_le_exp
#print axioms L27PaperInputs.reduced_ledger
#print axioms L27PaperInputs.reduced_paper
#print axioms L27PaperInputs.toRatedLeaf
#print axioms L27PaperInputs.slot
#print axioms L27PaperInputs.ofInputs
#print axioms L27AnalyticCertificate.ledger
#print axioms L27AnalyticCertificate.paper
#print axioms L27AnalyticCertificate.toRatedLeaf
#print axioms L27AnalyticCertificate.slot
#print axioms reduction_of_components
#print axioms reduction_of_multiplicative
#print axioms reduction_of_certificate
#print axioms reduced_ledger_inputs_via
#print axioms reduced_paper_inputs_via

end

end Cogentic.RandomizedL27Analytic
