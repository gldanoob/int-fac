import Cogentic.RandomizedL27Deuring

/-!
# L27 stage one: gcd exits and the smooth-order success bound

`Cogentic.RandomizedL27Analytic` leaves the following four paper-level inputs:

* `GCDExitNonneg` — the bad gcd-exit probability is nonnegative;
* `GCDExitLeInv` — a random curve singular modulo the target prime exits with
  probability at most `1 / p`;
* `GCDExitLeFailure` — the bad all-singular event is contained in the no-factor
  event;
* `StageOneSmoothMultiplicative` — the division-free form
  `SC ≤ success · log y · CT` of the stage-one smooth-order success bound.

This file reduces each of them to strictly smaller explicit statements and
proves that the smaller statements reassemble `L27PaperInputs`.

## Gcd exits

The three `GCDExit*` facts are reduced to a finite curve-count model.  For each
index `n` there are `T n` curves, `B n` of them are bad (singular modulo the
target prime and producing no factor), and `N n` of them lie in the no-factor
event.  The model records

* `0 < T n` (there is at least one curve);
* `gcdFail n = B n / T n` and `noFactor n = N n / T n`;
* `B n · p n ≤ T n` (at most a `1 / p` fraction of curves is bad);
* `B n ≤ N n` (the bad event is contained in the no-factor event).

Nonnegativity is then immediate from the counts; the `1 / p` bound is the
cleared fraction estimate; containment is monotonicity of the count fraction.
The paper's Lemma 7.2 is exactly the two counting inequalities, and no
probability is set to zero.

## Stage one

The faithful paper-level split uses the conditional success probability
`condSuccess`: a random point on a smooth-order curve is killed with probability
at least `condSuccess`, and `condSuccess ≥ 1 / log y`.  The overall per-curve
success is at least `smoothFraction · condSuccess`, so
`SF / log y ≤ success`, which is exactly the manuscript's stage-one bound.  The
reduction therefore isolates

* `StageOneConditionalLower` — the probability decomposition
  `SF · condSuccess ≤ success` together with `1 ≤ condSuccess · log y`.

This route does *not* strengthen the paper's `1 / log y` estimate.  As a
convenience, `StageOneSmoothKillsAll` records the stronger full-kill statement
(every point on a smooth-order curve is killed); with the explicit cutoff
`StageOneCutoffExpOne` (`e ≤ y`) it is a special case of the conditional route.
The factor `log y` is never discarded: it is either kept in the conditional
estimate or absorbed by `1 ≤ log y`.

## What the existing elliptic and smooth modules supply

`RandomizedEllipticAndGaussian` proves recursive-splitting failure bounds
conditional on an elliptic splitter (`twoStageRecognizer_fail_le`,
`twoStageRecognizer_success_ge`) and dyadic Hasse-interval incidence estimates.
Those are statements about a *different* splitting kernel and about prime
centres; they give neither the per-curve singular count `B · p ≤ T` nor the
stage-one point-kill law.  Likewise the smooth-number and smooth-order modules
(`RandomizedSmoothDensity`, `RandomizedL30*`) count smooth integers/orders, not
the probability that the stage-one scalar kills a random point.  The
sub-`Prop`s below are therefore kept explicit, exactly as in
`RandomizedL27Analytic` and `RandomizedL27Deuring`.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL27StageOne

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. Gcd exits: the finite curve-count model -/

/-- **The gcd-exit counting estimates.**  Among `total n` curves, `bad n` are bad
(singular modulo the target prime and producing no factor), and at most a `1/p`
fraction is bad: `bad n · p n ≤ total n`. -/
def GCDExitCurveCountBound (p : ℕ → ℕ) (total bad : ℕ → ℕ) : Prop :=
  ∀ n, (bad n : ℝ) * (p n : ℝ) ≤ (total n : ℝ)

/-- **The gcd-exit containment estimate.**  Every bad curve lies in the
no-factor event. -/
def GCDExitCurveContainment (bad noFac : ℕ → ℕ) : Prop :=
  ∀ n, bad n ≤ noFac n

/-- **The finite curve-count model behind the three `GCDExit*` facts.**  The
fields `total_pos`, `gcdFail_eq`, `noFactor_eq`, `count_bound`, and
`containment` are the explicit paper-level data; no field is a probability set
to zero. -/
structure GCDExitCurveModel (p : ℕ → ℕ) (gcdFail noFactor : ℕ → ℝ) where
  /-- Total number of curves. -/
  total : ℕ → ℕ
  /-- Number of bad curves (singular modulo `p`, no factor). -/
  bad : ℕ → ℕ
  /-- Number of curves in the no-factor event. -/
  noFac : ℕ → ℕ
  /-- There is at least one curve. -/
  total_pos : ∀ n, 0 < total n
  /-- The bad-gcd probability is the bad-curve fraction. -/
  gcdFail_eq : ∀ n, gcdFail n = (bad n : ℝ) / (total n : ℝ)
  /-- The no-factor probability is the no-factor curve fraction. -/
  noFactor_eq : ∀ n, noFactor n = (noFac n : ℝ) / (total n : ℝ)
  /-- At most a `1/p` fraction of curves is bad. -/
  count_bound : GCDExitCurveCountBound p total bad
  /-- The bad event is contained in the no-factor event. -/
  containment : GCDExitCurveContainment bad noFac

namespace GCDExitCurveModel

variable {p : ℕ → ℕ} {gcdFail noFactor : ℕ → ℝ}

/-- Nonnegativity of the gcd-exit probability, from the curve counts. -/
theorem nonneg (M : GCDExitCurveModel p gcdFail noFactor) :
    GCDExitNonneg gcdFail := by
  intro n
  rw [M.gcdFail_eq n]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The gcd-exit probability is at most `1/p`, from `bad · p ≤ total`. -/
theorem leInv (M : GCDExitCurveModel p gcdFail noFactor)
    (hp : ∀ n, 0 < p n) : GCDExitLeInv p gcdFail := by
  intro n
  have ht : (0 : ℝ) < (M.total n : ℝ) := by exact_mod_cast M.total_pos n
  have hp' : (0 : ℝ) < (p n : ℝ) := by exact_mod_cast hp n
  rw [M.gcdFail_eq n, div_le_iff₀ ht]
  have hbound : (M.bad n : ℝ) * (p n : ℝ) ≤ (M.total n : ℝ) :=
    M.count_bound n
  calc
    (M.bad n : ℝ) = ((M.bad n : ℝ) * (p n : ℝ)) / (p n : ℝ) := by
      field_simp [hp'.ne']
    _ ≤ (M.total n : ℝ) / (p n : ℝ) :=
      div_le_div_of_nonneg_right hbound hp'.le
    _ = (1 / (p n : ℝ)) * (M.total n : ℝ) := by ring

/-- The bad gcd-exit event is contained in the no-factor event, from the
count-level containment `bad ≤ noFac`. -/
theorem leFailure (M : GCDExitCurveModel p gcdFail noFactor) :
    GCDExitLeFailure gcdFail noFactor := by
  intro n
  rw [M.gcdFail_eq n, M.noFactor_eq n]
  exact div_le_div_of_nonneg_right (by exact_mod_cast M.containment n)
    (Nat.cast_nonneg _)

/-- The model implies the bundled `GCDExitBound` hypothesis. -/
theorem bound (M : GCDExitCurveModel p gcdFail noFactor)
    (hp : ∀ n, 0 < p n) : GCDExitBound p gcdFail noFactor :=
  gcdExitBound_of_components M.nonneg (M.leInv hp) M.leFailure

end GCDExitCurveModel

/-- Reassembly of the three `GCDExit*` components from the curve-count
model. -/
theorem gcdExitComponents_of_curveModel {p : ℕ → ℕ} {gcdFail noFactor : ℕ → ℝ}
    (M : GCDExitCurveModel p gcdFail noFactor) (hp : ∀ n, 0 < p n) :
    GCDExitNonneg gcdFail ∧ GCDExitLeInv p gcdFail ∧
      GCDExitLeFailure gcdFail noFactor :=
  ⟨M.nonneg, M.leInv hp, M.leFailure⟩

/-- The curve-count model gives the bundled `GCDExitBound` directly. -/
theorem gcdExitBound_of_curveModel {p : ℕ → ℕ} {gcdFail noFactor : ℕ → ℝ}
    (M : GCDExitCurveModel p gcdFail noFactor) (hp : ∀ n, 0 < p n) :
    GCDExitBound p gcdFail noFactor :=
  M.bound hp

/-! ## 2. Stage one: conditional success on smooth orders -/

/-- **The stage-one conditional-success estimate.**  `condSuccess n` is the
probability that a random point is killed by the stage-one scalar, conditional
on the curve order being stage-one smooth.  The overall per-curve success is at
least `smoothFraction · condSuccess`, and the paper's stage-one estimate is
exactly `condSuccess ≥ 1 / log y`.  Both fields are kept as explicit inputs;
neither probability is set to zero. -/
def StageOneConditionalLower (smoothFraction success condSuccess y : ℕ → ℝ) : Prop :=
  (∀ n, smoothFraction n * condSuccess n ≤ success n) ∧
    ∀ n, 1 ≤ condSuccess n * Real.log (y n)

/-- **The stage-one full-kill estimate.**  On a curve whose group order is
stage-one smooth, the stage-one scalar kills every point; hence the total mass
of smooth curves is at most `success · CT`.  This is the stronger group-law
content of the stage-one bound, with no `log y` factor. -/
def StageOneSmoothKillsAll (smoothCurves curveTotal success : ℕ → ℝ) : Prop :=
  ∀ n, smoothCurves n ≤ success n * curveTotal n

/-- **The cutoff is at least `e`**, so `log y ≥ 1`.  This is the only arithmetic
input needed to convert the full-kill bound into the manuscript's form with the
`log y` factor. -/
def StageOneCutoffExpOne (y : ℕ → ℝ) : Prop :=
  ∀ n, Real.exp 1 ≤ y n

/-- A cutoff at least `3` is at least `e`; this is the natural integer form of
the cutoff hypothesis. -/
theorem stageOneCutoffExpOne_of_three_le {y : ℕ → ℝ} (hy : ∀ n, 3 ≤ y n) :
    StageOneCutoffExpOne y :=
  fun n => (le_of_lt Real.exp_one_lt_three).trans (hy n)

/-- `log y ≥ 1` from `y ≥ e`. -/
theorem log_ge_one_of_exp_one_le {y : ℝ} (h : Real.exp 1 ≤ y) :
    1 ≤ Real.log y := by
  have h' := Real.log_le_log (Real.exp_pos 1) h
  rwa [Real.log_exp] at h'

/-- The cutoff sub-`Prop` gives `log y ≥ 1`. -/
theorem stageOneCutoffLogGeOne_of_expOne {y : ℕ → ℝ}
    (h : StageOneCutoffExpOne y) :
    ∀ n, 1 ≤ Real.log (y n) :=
  fun n => log_ge_one_of_exp_one_le (h n)

/-- The smooth curve count is nonnegative. -/
theorem smoothCurves_nonneg (smooth : ℕ → ℕ → Bool) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) (n : ℕ) :
    0 ≤ smoothCurves smooth orderCount orderTop n := by
  unfold smoothCurves
  exact Finset.sum_nonneg fun j _ => by positivity

/-- **The full-kill bound implies the division-free stage-one bound.**  The
manuscript's `log y` factor is absorbed by `1 ≤ log y`: from
`SC ≤ success · CT` and `success ≥ 0`, multiplying by `log y ≥ 1` gives
`SC ≤ success · log y · CT`. -/
theorem stageOneSmoothMultiplicative_of_killsAll {I : L27_1Inputs}
    (hk : StageOneSmoothKillsAll I.SC I.CT I.success)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    StageOneSmoothMultiplicative I.SC I.CT I.y I.success := by
  intro n
  have hCT : 0 < I.CT n := I.curveTotal_pos n
  have hSC : 0 ≤ I.SC n := by
    simpa [L27_1Inputs.SC] using
      smoothCurves_nonneg I.smooth I.orderCount I.orderTop n
  have hsuccess : 0 ≤ I.success n := by
    have hmul : 0 ≤ I.success n * I.CT n := hSC.trans (hk n)
    by_contra hneg
    push Not at hneg
    nlinarith [hmul, hCT, hneg]
  have hCTle : I.CT n ≤ Real.log (I.y n) * I.CT n := by
    have hle : (1 : ℝ) * I.CT n ≤ Real.log (I.y n) * I.CT n :=
      mul_le_mul_of_nonneg_right (hlog n) hCT.le
    simpa using hle
  calc
    I.SC n ≤ I.success n * I.CT n := hk n
    _ ≤ I.success n * (Real.log (I.y n) * I.CT n) :=
      mul_le_mul_of_nonneg_left hCTle hsuccess
    _ = I.success n * Real.log (I.y n) * I.CT n := by ring

/-- **The conditional bound implies the division-free stage-one bound.**  This
is the faithful paper-level reduction: the overall success is at least the
smooth fraction times the conditional success, and the conditional success is
at least `1 / log y`.  No stronger full-kill assumption is used. -/
theorem stageOneSmoothMultiplicative_of_conditional {I : L27_1Inputs}
    {condSuccess : ℕ → ℝ}
    (h : StageOneConditionalLower
      (fun n => I.SC n / I.CT n) I.success condSuccess I.y) :
    StageOneSmoothMultiplicative I.SC I.CT I.y I.success := by
  intro n
  have hCT : 0 < I.CT n := I.curveTotal_pos n
  have hlog : 0 < Real.log (I.y n) := I.log_y_pos n
  have hSC : 0 ≤ I.SC n := by
    simpa [L27_1Inputs.SC] using
      smoothCurves_nonneg I.smooth I.orderCount I.orderTop n
  let sf : ℝ := I.SC n / I.CT n
  let c : ℝ := condSuccess n
  let L : ℝ := Real.log (I.y n)
  let T : ℝ := I.CT n
  have hsf : 0 ≤ sf := div_nonneg hSC hCT.le
  have hc : 0 ≤ c := by
    have hn := h.2 n
    change 1 ≤ c * L at hn
    by_contra hneg
    push Not at hneg
    nlinarith [hn, hlog, hneg]
  have hmain : sf * c ≤ I.success n := h.1 n
  have hcL : 1 ≤ c * L := h.2 n
  have hLCT : 0 ≤ L * T := mul_nonneg hlog.le hCT.le
  have hscale : sf * T ≤ sf * (c * L) * T := by
    calc
      sf * T = (sf * T) * 1 := by ring
      _ ≤ (sf * T) * (c * L) :=
        mul_le_mul_of_nonneg_left hcL (mul_nonneg hsf hCT.le)
      _ = sf * (c * L) * T := by ring
  have hstep : sf * (c * L) * T ≤ I.success n * L * T := by
    calc
      sf * (c * L) * T = (sf * c) * (L * T) := by ring
      _ ≤ I.success n * (L * T) :=
        mul_le_mul_of_nonneg_right hmain hLCT
      _ = I.success n * L * T := by ring
  calc
    I.SC n = sf * T := by
      dsimp [sf, T]
      field_simp [hCT.ne']
    _ ≤ sf * (c * L) * T := hscale
    _ ≤ I.success n * L * T := hstep
    _ = I.success n * Real.log (I.y n) * I.CT n := by
      dsimp [L, T]

/-- The full-kill bound and the cutoff estimate give the bundled
`StageOneSuccess` hypothesis. -/
theorem stageOneSuccess_of_killsAll {I : L27_1Inputs}
    (hk : StageOneSmoothKillsAll I.SC I.CT I.success)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success :=
  stageOneSuccess_of_multiplicative
    (stageOneSmoothMultiplicative_of_killsAll hk hlog)

/-- The full-kill route is a special case of the conditional route, with
conditional success identically `1`. -/
theorem stageOneConditionalLower_of_killsAll {I : L27_1Inputs}
    (hk : StageOneSmoothKillsAll I.SC I.CT I.success)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (fun _ => 1) I.y := by
  constructor
  · intro n
    have hCT : 0 < I.CT n := I.curveTotal_pos n
    have hle : I.SC n / I.CT n ≤ I.success n := by
      rw [div_le_iff₀ hCT]
      simpa [mul_comm] using hk n
    simpa using hle
  · intro n
    simpa using hlog n

/-- The conditional bound gives the bundled `StageOneSuccess` hypothesis. -/
theorem stageOneSuccess_of_conditional {I : L27_1Inputs}
    {condSuccess : ℕ → ℝ}
    (h : StageOneConditionalLower
      (fun n => I.SC n / I.CT n) I.success condSuccess I.y) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success :=
  stageOneSuccess_of_multiplicative
    (stageOneSmoothMultiplicative_of_conditional h)

/-! ## 3. The bundled smallest stage-one inputs -/

/-- **The smallest explicit stage-one inputs.**  Each field is a single
paper-level statement:

* `gcd_model` — the finite curve counts behind Lemma 7.2;
* `condSuccess` and `stage_one_conditional` — the conditional probability that
  a random point is killed on a smooth-order curve, together with the paper's
  `1 / log y` lower bound and the probability decomposition of the overall
  success;
* optionally, `of_killsAll` packages the stronger full-kill route.

No probability is set to zero, and no curve count or point-kill mass is
discarded. -/
structure L27StageOneInputs (I : L27_1Inputs) where
  /-- Finite curve counts and the two gcd-exit counting estimates. -/
  gcd_model : GCDExitCurveModel I.p I.gcdFail (fun n => 1 - I.success n)
  /-- The conditional success probability on a smooth-order curve. -/
  condSuccess : ℕ → ℝ
  /-- The probability decomposition and the paper's `1 / log y` conditional
  lower bound. -/
  stage_one_conditional :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success condSuccess I.y

/-- The stronger full-kill route packaged as the smallest inputs.  This is a
convenience constructor: it is not needed for the manuscript estimate and is
strictly stronger than the conditional route. -/
def L27StageOneInputs.of_killsAll (I : L27_1Inputs)
    (M : GCDExitCurveModel I.p I.gcdFail (fun n => 1 - I.success n))
    (hk : StageOneSmoothKillsAll I.SC I.CT I.success)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) : L27StageOneInputs I where
  gcd_model := M
  condSuccess := fun _ => 1
  stage_one_conditional := stageOneConditionalLower_of_killsAll hk hlog

namespace L27StageOneInputs

variable {I : L27_1Inputs}

/-- Nonnegativity of the gcd-exit probability. -/
theorem gcdExitNonneg (S : L27StageOneInputs I) : GCDExitNonneg I.gcdFail :=
  S.gcd_model.nonneg

/-- The gcd-exit probability is at most `1/p`. -/
theorem gcdExitLeInv (S : L27StageOneInputs I) : GCDExitLeInv I.p I.gcdFail :=
  S.gcd_model.leInv I.p_pos

/-- The bad gcd-exit event is contained in the no-factor event. -/
theorem gcdExitLeFailure (S : L27StageOneInputs I) :
    GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n) :=
  S.gcd_model.leFailure

/-- The bundled gcd-exit bound. -/
theorem gcdExitBound (S : L27StageOneInputs I) :
    GCDExitBound I.p I.gcdFail (fun n => 1 - I.success n) :=
  S.gcd_model.bound I.p_pos

/-- The division-free stage-one smooth-order bound. -/
theorem stageOneSmoothMultiplicative (S : L27StageOneInputs I) :
    StageOneSmoothMultiplicative I.SC I.CT I.y I.success :=
  stageOneSmoothMultiplicative_of_conditional S.stage_one_conditional

/-- The bundled stage-one success bound. -/
theorem stageOneSuccess (S : L27StageOneInputs I) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success :=
  stageOneSuccess_of_conditional S.stage_one_conditional

/-- The four target `L27Analytic` sub-`Prop`s, reassembled from the smaller
stage-one inputs. -/
theorem toComponents (S : L27StageOneInputs I) :
    GCDExitNonneg I.gcdFail ∧ GCDExitLeInv I.p I.gcdFail ∧
      GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n) ∧
      StageOneSmoothMultiplicative I.SC I.CT I.y I.success :=
  ⟨S.gcdExitNonneg, S.gcdExitLeInv, S.gcdExitLeFailure,
    S.stageOneSmoothMultiplicative⟩

/-- The elliptic-curve group-law bundle, from Hasse and the new stage inputs. -/
theorem ellipticCurveGroupLaw (S : L27StageOneInputs I)
    (hhasse : HasseBound I.p I.orderCount) : EllipticCurveGroupLaw I :=
  ellipticCurveGroupLaw_of_components hhasse S.gcdExitBound S.stageOneSuccess

/-- Reassemble `L27PaperInputs` from the Deuring side and the new stage
inputs. -/
theorem toPaperInputs (S : L27StageOneInputs I)
    (hcount : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ)
    (htotal : HasseWindowCurveTotal I.p I.orderCount I.orderTop)
    (hhasse : HasseBound I.p I.orderCount) : L27PaperInputs I where
  deuring_smooth_order_count := hcount
  hasse_window_curve_total := htotal
  hasse_bound := hhasse
  gcd_exit_nonneg := S.gcdExitNonneg
  gcd_exit_le_inv := S.gcdExitLeInv
  gcd_exit_le_failure := S.gcdExitLeFailure
  stage_one_smooth_success := S.stageOneSuccess

/-- The `L27PaperInputs` assembled through the existing Deuring reduction. -/
theorem paperInputs_of_deuring {I : L27_1Inputs} (D : L27DeuringInputs I)
    (S : L27StageOneInputs I) (hhasse : HasseBound I.p I.orderCount) :
    L27PaperInputs I :=
  D.toPaperInputs hhasse S.gcdExitNonneg S.gcdExitLeInv S.gcdExitLeFailure
    S.stageOneSuccess

end L27StageOneInputs

/-! ## 4. Capstone reductions -/

/-- **The full reduction from the smaller stage-one inputs.**  The per-order
Deuring count, the total-window count, Hasse's theorem, the finite gcd-exit
curve model, the conditional stage-one estimate, the curve budget, and the
`log₂` multiplier imply both bundled `L27_1Sub` hypotheses and both deficit
conclusions. -/
theorem reduction_of_stageInputs {I : L27_1Inputs} (S : L27StageOneInputs I)
    (hcount : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ)
    (htotal : HasseWindowCurveTotal I.p I.orderCount I.orderTop)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) := by
  let P : L27PaperInputs I := S.toPaperInputs hcount htotal hhasse
  exact ⟨L27PaperInputs.deuring P, L27PaperInputs.elliptic P,
    L27PaperInputs.reduced_ledger P hbudget hlog,
    L27PaperInputs.reduced_paper P hbudget hlog⟩

/-- **The full reduction from the `L27DeuringInputs` bundle and the new stage
inputs.**  This is the composition of `RandomizedL27Deuring`'s Deuring
reduction with the stage-one reduction of this file. -/
theorem reduction_of_deuring_and_stage {I : L27_1Inputs}
    (D : L27DeuringInputs I) (S : L27StageOneInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  reduction_of_stageInputs S D.deuringSmoothOrderCount D.hasseWindowCurveTotal
    hhasse hbudget hlog

/-- Compatibility: the original `L27PaperInputs` still gives the four
`GCDExit*`/stage-one fields without going through the count model. -/
theorem stageFields_of_paperInputs {I : L27_1Inputs} (P : L27PaperInputs I) :
    GCDExitNonneg I.gcdFail ∧ GCDExitLeInv I.p I.gcdFail ∧
      GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n) ∧
      StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop)
        I.y I.success :=
  ⟨P.gcd_exit_nonneg, P.gcd_exit_le_inv, P.gcd_exit_le_failure,
    P.stage_one_smooth_success⟩

/-! ## Axiom audit -/

#print axioms GCDExitCurveModel.nonneg
#print axioms GCDExitCurveModel.leInv
#print axioms GCDExitCurveModel.leFailure
#print axioms GCDExitCurveModel.bound
#print axioms gcdExitComponents_of_curveModel
#print axioms gcdExitBound_of_curveModel
#print axioms stageOneCutoffExpOne_of_three_le
#print axioms log_ge_one_of_exp_one_le
#print axioms stageOneCutoffLogGeOne_of_expOne
#print axioms smoothCurves_nonneg
#print axioms stageOneSmoothMultiplicative_of_killsAll
#print axioms stageOneSuccess_of_killsAll
#print axioms stageOneSmoothMultiplicative_of_conditional
#print axioms stageOneConditionalLower_of_killsAll
#print axioms stageOneSuccess_of_conditional
#print axioms L27StageOneInputs.of_killsAll
#print axioms L27StageOneInputs.gcdExitNonneg
#print axioms L27StageOneInputs.gcdExitLeInv
#print axioms L27StageOneInputs.gcdExitLeFailure
#print axioms L27StageOneInputs.gcdExitBound
#print axioms L27StageOneInputs.stageOneSmoothMultiplicative
#print axioms L27StageOneInputs.stageOneSuccess
#print axioms L27StageOneInputs.toComponents
#print axioms L27StageOneInputs.ellipticCurveGroupLaw
#print axioms L27StageOneInputs.toPaperInputs
#print axioms L27StageOneInputs.paperInputs_of_deuring
#print axioms reduction_of_stageInputs
#print axioms reduction_of_deuring_and_stage
#print axioms stageFields_of_paperInputs

end

end Cogentic.RandomizedL27StageOne
