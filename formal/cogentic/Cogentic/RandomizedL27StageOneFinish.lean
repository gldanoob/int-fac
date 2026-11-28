import Cogentic.RandomizedL27KillLaw
import Cogentic.RandomizedL27Hurwitz

/-!
# L27 stage one finish: the kill-mass bundle and the L27.1 loss cap

`Cogentic.RandomizedL27KillLaw` isolates the smallest finite-sum data behind the
stage-one estimate: the singular-curve count `p / p² = 1/p`, the no-factor count
at the same scale, the killed-point count on a smooth curve, and the summed
`1 / log y` kill-mass law.  It proves `StageOneConditionalLower`,
`StageOneSuccess`, the gcd-exit bound, and the cap `success ≤ 1 - 1/p`, but it
leaves the Deuring/Hurwitz distribution and Hasse's theorem to their own
reductions.

This file is the assembly step.  It takes

* `S : L27KillLawInputs I` — the kill-mass/gcd-cover data;
* `H : L27HurwitzInputs I` — the genuinely deep Deuring/Hurwitz block (Siegel
  lower bound, Deuring/Waterhouse trace count, discriminant scale, `j`-line
  fibre count, small-prime prepass), as reduced in
  `Cogentic.RandomizedL27Hurwitz`;
* `HasseBound I.p I.orderCount` — the genuinely deep group-law input (Hasse's
  theorem);
* the paper's curve-count choice `CurveBudget` and the L27.2 multiplier
  `LogFactorSubexp`;

and proves every remaining numeric field:

1. `success_le_one_sub_inv` — the per-curve success is at most `1 - 1/p`, from
   the no-factor count `1/p ≤ 1 - success`;
2. `curveFail_ge_inv` — equivalently the per-curve failure is at least `1/p`;
3. `gcdExitNonneg`, `gcdExitLeInv`, `gcdExitLeFailure`, and `gcdExitBound` —
   the three gcd-exit components and their bundle, from the concrete
   `p²`-curve model;
4. `stageOneConditional`, `stageOneSmoothMultiplicative`, `stageOneSuccess` —
   the conditional `1 / log y` lower bound and the division-free stage-one
   estimate, through the finite-sum kill mass;
5. `deuringSmoothOrderCount`, `hasseWindowCurveTotal`, `deuringLenstraCounts`,
   `ellipticCurveGroupLaw` — the two bundled `L27_1Sub` hypotheses;
6. `loss_le_exp_ledger` and `loss_le_exp_paper` — the final L27.1 caps
   `loss ≤ exp (-2H)` and `loss ≤ exp (-(cRate/2) · rate)`, with the budget
   arithmetic `(2 + η)H ≤ E` performed explicitly rather than assumed.

The bundle `L27StageOneFinishInputs` records exactly the kill-law data, the
Hurwitz block, Hasse, the budget, and the `log₂` multiplier.  Nothing else is
assumed: no curve count is set to zero, no probability is discarded, and the
only explicit mathematical inputs left are the Hurwitz bound and the group law.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL27StageOneFinish

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27StageOne
open Cogentic.RandomizedL27GcdModel
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The numeric fields of the kill-law data -/

/-- **The success probability is at most `1 - 1/p`.**  The no-factor event is
counted at the `p²` scale and contains all `p` singular curves, so its
probability is at least `1/p`; since it is `1 - success`, this caps the
per-curve success. -/
theorem success_le_one_sub_inv_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) (n : ℕ) :
    I.success n ≤ 1 - 1 / (I.p n : ℝ) := by
  have h : (1 : ℝ) / (I.p n : ℝ) ≤ 1 - I.success n :=
    PaperNoFactorCurveCount.inv_le S.noFactorData I.p_pos n
  linarith

/-- The per-curve failure probability is at least `1/p`.  This is the same
count inequality as `success_le_one_sub_inv`, written in terms of the failure. -/
theorem curveFail_ge_inv_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) (n : ℕ) :
    (1 : ℝ) / (I.p n : ℝ) ≤ I.curveFail n := by
  have h := success_le_one_sub_inv_of_killLaw S n
  dsimp [L27_1Inputs.curveFail]
  linarith

/-- Nonnegativity of the gcd-exit probability, from the finite curve counts. -/
theorem gcdExitNonneg_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) : GCDExitNonneg I.gcdFail :=
  S.gcdModel.nonneg

/-- The gcd-exit probability is at most `1/p`, from `bad · p ≤ total`. -/
theorem gcdExitLeInv_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) : GCDExitLeInv I.p I.gcdFail :=
  S.gcdModel.leInv I.p_pos

/-- The bad gcd-exit event is contained in the no-factor event, from the
count-level containment `bad ≤ noFac`. -/
theorem gcdExitLeFailure_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) :
    GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n) :=
  S.gcdModel.leFailure

/-- The bundled gcd-exit bound, assembled from the concrete curve model. -/
theorem gcdExitBound_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) :
    GCDExitBound I.p I.gcdFail (fun n => 1 - I.success n) :=
  S.gcdModel.bound I.p_pos

/-! ## 2. Stage one from the finite-sum kill mass -/

/-- **The stage-one conditional lower bound** from the summed kill law.  The
conditional success is the explicit ratio `killedPointMass / smoothPointMass`;
no point mass is discarded. -/
theorem stageOneConditional_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I S.pointKill) I.y :=
  stageOneConditionalLower_of_killMass I S.pointKill S.smooth_order_pos
    S.success_ge_killed S.kill_mass
    (stageOneCutoffLogGeOne_of_expOne S.cutoff)

/-- The division-free stage-one bound `SC ≤ success · log y · CT`. -/
theorem stageOneSmoothMultiplicative_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) :
    StageOneSmoothMultiplicative I.SC I.CT I.y I.success :=
  stageOneSmoothMultiplicative_of_conditional
    (stageOneConditional_of_killLaw S)

/-- The bundled stage-one success bound. -/
theorem stageOneSuccess_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop)
      I.y I.success :=
  stageOneSuccess_of_conditional (stageOneConditional_of_killLaw S)

/-- **The stage-one bundle constructed from the kill-law inputs.**  The curve
count model, the conditional success, and the `1 / log y` lower bound are the
three fields of `L27StageOneInputs`, all discharged here. -/
def stageOneInputs_of_killLaw {I : L27_1Inputs}
    (S : L27KillLawInputs I) : L27StageOneInputs I where
  gcd_model := S.gcdModel
  condSuccess := conditionalSuccess I S.pointKill
  stage_one_conditional := stageOneConditional_of_killLaw S

/-! ## 3. The Hurwitz/group-law side and the bundled finish inputs -/

/-- **The L27 stage-one finish bundle.**  It contains exactly

* `killLaw` — the kill-mass/gcd-cover data of `L27KillLawInputs`;
* `hurwitz` — the deep Deuring/Hurwitz block of `L27HurwitzInputs`;
* `hasse` — the group law, Hasse's theorem;
* `curve_budget` — the paper's curve-count choice;
* `log_factor_subexp` — the L27.2 `log₂` multiplier.

Every numeric estimate (the `1 - 1/p` success cap, the gcd-exit bound, the
stage-one conditional bound, the Deuring/Lenstra and group-law bundles, and the
two final loss caps) is proved from these fields below. -/
structure L27StageOneFinishInputs (I : L27_1Inputs) where
  /-- The kill-mass/gcd-cover data. -/
  killLaw : L27KillLawInputs I
  /-- The Hurwitz/Deuring block. -/
  hurwitz : L27HurwitzInputs I
  /-- Hasse's theorem. -/
  hasse : HasseBound I.p I.orderCount
  /-- The paper's curve-count choice. -/
  curve_budget : CurveBudget I.p I.y I.psi I.curves I.κ I.η
  /-- The L27.2 `log₂` multiplier. -/
  log_factor_subexp : LogFactorSubexp I.cofactor

namespace L27StageOneFinishInputs

variable {I : L27_1Inputs}

/-- The `1 - 1/p` success cap. -/
theorem success_le_one_sub_inv (F : L27StageOneFinishInputs I) (n : ℕ) :
    I.success n ≤ 1 - 1 / (I.p n : ℝ) :=
  success_le_one_sub_inv_of_killLaw F.killLaw n

/-- The `1/p` failure floor. -/
theorem curveFail_ge_inv (F : L27StageOneFinishInputs I) (n : ℕ) :
    (1 : ℝ) / (I.p n : ℝ) ≤ I.curveFail n :=
  curveFail_ge_inv_of_killLaw F.killLaw n

/-- The bundled gcd-exit bound. -/
theorem gcdExitBound (F : L27StageOneFinishInputs I) :
    GCDExitBound I.p I.gcdFail (fun n => 1 - I.success n) :=
  gcdExitBound_of_killLaw F.killLaw

/-- The stage-one conditional `1 / log y` bound. -/
theorem stageOneConditional (F : L27StageOneFinishInputs I) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I F.killLaw.pointKill) I.y :=
  stageOneConditional_of_killLaw F.killLaw

/-- The division-free stage-one bound. -/
theorem stageOneSmoothMultiplicative (F : L27StageOneFinishInputs I) :
    StageOneSmoothMultiplicative I.SC I.CT I.y I.success :=
  stageOneSmoothMultiplicative_of_killLaw F.killLaw

/-- The bundled stage-one success bound. -/
theorem stageOneSuccess (F : L27StageOneFinishInputs I) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop)
      I.y I.success :=
  stageOneSuccess_of_killLaw F.killLaw

/-- The per-order Deuring/Lenstra count, from the Hurwitz leaves. -/
theorem deuringSmoothOrderCount (F : L27StageOneFinishInputs I) :
    DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ :=
  F.hurwitz.deuringSmoothOrderCount

/-- The `≤ 4p` Hasse-window curve total, from the `j`-line stratification. -/
theorem hasseWindowCurveTotal (F : L27StageOneFinishInputs I) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  F.hurwitz.hasseWindowCurveTotal

/-- The bundled `DeuringLenstraCounts` hypothesis of `L27_1Sub`. -/
theorem deuringLenstraCounts (F : L27StageOneFinishInputs I) :
    DeuringLenstraCounts I :=
  F.hurwitz.deuringLenstraCounts

/-- The bundled `EllipticCurveGroupLaw` hypothesis of `L27_1Sub`, assembled
from Hasse, the gcd-exit bound, and the stage-one success bound. -/
theorem ellipticCurveGroupLaw (F : L27StageOneFinishInputs I) :
    EllipticCurveGroupLaw I :=
  ellipticCurveGroupLaw_of_components F.hasse F.gcdExitBound F.stageOneSuccess

/-- Reassemble `L27PaperInputs` from the finish bundle.  The two Deuring fields
come from the Hurwitz block, Hasse is explicit, and the three gcd-exit facts and
the stage-one bound come from the kill-law data. -/
theorem paperInputs (F : L27StageOneFinishInputs I) : L27PaperInputs I where
  deuring_smooth_order_count := F.deuringSmoothOrderCount
  hasse_window_curve_total := F.hasseWindowCurveTotal
  hasse_bound := F.hasse
  gcd_exit_nonneg := gcdExitNonneg_of_killLaw F.killLaw
  gcd_exit_le_inv := gcdExitLeInv_of_killLaw F.killLaw
  gcd_exit_le_failure := gcdExitLeFailure_of_killLaw F.killLaw
  stage_one_smooth_success := F.stageOneSuccess

/-- The full `L27AnalyticCertificate`: the paper inputs plus the curve budget
and the `log₂` multiplier. -/
theorem certificate (F : L27StageOneFinishInputs I) : L27AnalyticCertificate I where
  toL27PaperInputs := F.paperInputs
  curve_budget := F.curve_budget
  log_factor_subexp := F.log_factor_subexp

/-! ## 4. The final L27.1 loss caps -/

/-- **The L27.1 ledger cap `loss ≤ exp (-2H)`.**  The budget arithmetic is
performed explicitly: from `(2 + η)H ≤ cRate · rate` and the per-curve failure
`splitFail ≤ exp (-cRate · rate)`, the `log₂` multiplier
`exp ((η/2)H)` is absorbed into `exp (-2H)`. -/
theorem loss_le_exp_ledger (F : L27StageOneFinishInputs I) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  filter_upwards [F.curve_budget,
    F.log_factor_subexp (I.η / 2) (by linarith [I.η_pos]),
    scale_grows.eventually_ge_atTop 0] with n hb hl hs
  have hbudget' : (2 + I.η) * scale n ≤ I.cRate * I.rate n := by
    simpa [L27_1Inputs.cRate, L27_1Inputs.rate, L27_1Inputs.D, density] using hb
  have hfail : I.splitFail n ≤ Real.exp (-(I.cRate * I.rate n)) :=
    L27PaperInputs.splitFail_le_exp F.paperInputs n
  have h := loss_le_exp_of_budget (H := scale n) (E := I.cRate * I.rate n)
    (L := ((I.cofactor n).log2 : ℝ)) (fail := I.splitFail n) (η := I.η)
    hs I.η_pos hbudget' (splitFail_nonneg_of I n) hl hfail
  simpa [L27_1Inputs.loss] using h

/-- **The manuscript-rate loss cap
`loss ≤ exp (-(cRate/2) · rate)`.**  The same budget arithmetic, with the
headroom absorbed into `exp (-E/2)` instead of `exp (-2H)`. -/
theorem loss_le_exp_paper (F : L27StageOneFinishInputs I) :
    ∀ᶠ n : ℕ in atTop,
      I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) := by
  filter_upwards [F.curve_budget,
    F.log_factor_subexp (I.η / 2) (by linarith [I.η_pos]),
    scale_grows.eventually_ge_atTop 0] with n hb hl hs
  have hbudget' : (2 + I.η) * scale n ≤ I.cRate * I.rate n := by
    simpa [L27_1Inputs.cRate, L27_1Inputs.rate, L27_1Inputs.D, density] using hb
  have hfail : I.splitFail n ≤ Real.exp (-(I.cRate * I.rate n)) :=
    L27PaperInputs.splitFail_le_exp F.paperInputs n
  have h := loss_le_exp_half_of_budget (H := scale n) (E := I.cRate * I.rate n)
    (L := ((I.cofactor n).log2 : ℝ)) (fail := I.splitFail n) (η := I.η)
    hs hbudget' (splitFail_nonneg_of I n) hl hfail
  have hgoal : Real.exp (-((I.cRate * I.rate n) / 2)) =
      Real.exp (-((I.cRate / 2) * I.rate n)) := by
    congr 1
    ring
  simpa [L27_1Inputs.loss, hgoal] using h

/-- **The full L27.1 reduction from the finish bundle.**  Both bundled
`L27_1Sub` hypotheses and both deficit conclusions follow from the kill-law
data, the Hurwitz block, Hasse, the curve budget, and the `log₂` multiplier. -/
theorem reduction (F : L27StageOneFinishInputs I) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  ⟨F.deuringLenstraCounts, F.ellipticCurveGroupLaw,
    F.loss_le_exp_ledger, F.loss_le_exp_paper⟩

/-- The `RatedLeaf` assembled from the finish bundle. -/
def toRatedLeaf (F : L27StageOneFinishInputs I) : RatedLeaf :=
  L27AnalyticCertificate.toRatedLeaf F.certificate

/-- The `C5` slot `exp (-2H)` for the assembled leaf. -/
theorem slot (F : L27StageOneFinishInputs I) :
    ∀ᶠ n : ℕ in atTop,
      (F.toRatedLeaf).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  (F.toRatedLeaf).slot

end L27StageOneFinishInputs

/-! ## 5. Capstones stated directly on the data -/

/-- **The final L27.1 loss caps from the kill-law and Hurwitz data directly.**
No intermediate bundle is required: the kill-mass/gcd-cover data, the Hurwitz
block, Hasse, the curve budget, and the `log₂` multiplier imply both caps. -/
theorem loss_cap_of_killLaw_and_hurwitz {I : L27_1Inputs}
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  let F : L27StageOneFinishInputs I :=
    { killLaw := S
      hurwitz := H
      hasse := hhasse
      curve_budget := hbudget
      log_factor_subexp := hlog }
  ⟨F.loss_le_exp_ledger, F.loss_le_exp_paper⟩

/-- **The full L27.1 reduction from the kill-law and Hurwitz data directly.**
This is `loss_cap_of_killLaw_and_hurwitz` together with the two bundled
hypotheses, all assembled from the same data. -/
theorem reduction_of_killLaw_and_hurwitz {I : L27_1Inputs}
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  let F : L27StageOneFinishInputs I :=
    { killLaw := S
      hurwitz := H
      hasse := hhasse
      curve_budget := hbudget
      log_factor_subexp := hlog }
  F.reduction

/-- The `L27AnalyticCertificate` built directly from the kill-law and Hurwitz
data. -/
theorem certificate_of_killLaw_and_hurwitz {I : L27_1Inputs}
    (S : L27KillLawInputs I) (H : L27HurwitzInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : L27AnalyticCertificate I :=
  { toL27PaperInputs :=
      H.toPaperInputs hhasse
        (gcdExitNonneg_of_killLaw S)
        (gcdExitLeInv_of_killLaw S)
        (gcdExitLeFailure_of_killLaw S)
        (stageOneSuccess_of_killLaw S)
    curve_budget := hbudget
    log_factor_subexp := hlog }

/-! ## Axiom audit -/

#print axioms success_le_one_sub_inv_of_killLaw
#print axioms curveFail_ge_inv_of_killLaw
#print axioms gcdExitNonneg_of_killLaw
#print axioms gcdExitLeInv_of_killLaw
#print axioms gcdExitLeFailure_of_killLaw
#print axioms gcdExitBound_of_killLaw
#print axioms stageOneConditional_of_killLaw
#print axioms stageOneSmoothMultiplicative_of_killLaw
#print axioms stageOneSuccess_of_killLaw
#print axioms stageOneInputs_of_killLaw
#print axioms L27StageOneFinishInputs.success_le_one_sub_inv
#print axioms L27StageOneFinishInputs.curveFail_ge_inv
#print axioms L27StageOneFinishInputs.gcdExitBound
#print axioms L27StageOneFinishInputs.stageOneConditional
#print axioms L27StageOneFinishInputs.stageOneSmoothMultiplicative
#print axioms L27StageOneFinishInputs.stageOneSuccess
#print axioms L27StageOneFinishInputs.deuringSmoothOrderCount
#print axioms L27StageOneFinishInputs.hasseWindowCurveTotal
#print axioms L27StageOneFinishInputs.deuringLenstraCounts
#print axioms L27StageOneFinishInputs.ellipticCurveGroupLaw
#print axioms L27StageOneFinishInputs.paperInputs
#print axioms L27StageOneFinishInputs.certificate
#print axioms L27StageOneFinishInputs.loss_le_exp_ledger
#print axioms L27StageOneFinishInputs.loss_le_exp_paper
#print axioms L27StageOneFinishInputs.reduction
#print axioms L27StageOneFinishInputs.toRatedLeaf
#print axioms L27StageOneFinishInputs.slot
#print axioms loss_cap_of_killLaw_and_hurwitz
#print axioms reduction_of_killLaw_and_hurwitz
#print axioms certificate_of_killLaw_and_hurwitz

end

end Cogentic.RandomizedL27StageOneFinish
