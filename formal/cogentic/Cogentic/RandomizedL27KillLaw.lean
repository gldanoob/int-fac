import Cogentic.RandomizedL27GcdModel

/-!
# L27 kill law: the stage-one point kill in smallest finite-sum form

`Cogentic.RandomizedL27GcdModel` proves `StageOneConditionalLower` from the
pointwise paper law

`j ≤ pointKill n j * log y`  for every smooth order `j`.

Only the *weighted sum* of that inequality against the Deuring curve counts is
ever used in the proof.  This file isolates that sum.  It is the smallest
explicit finite-sum statement behind the paper's `1 / log y` point-kill law,
and it is *exactly* equivalent, in the nondegenerate case, to the two mass
inequalities

* `SC * killedPointMass ≤ success * CT * smoothPointMass` — the product of the
  smooth curve fraction and the conditional kill fraction is bounded by the
  unconditional success probability;
* `smoothPointMass ≤ killedPointMass * log y` — the paper's `1 / log y`
  fraction, summed against the Deuring weights.

## Contents

* `PointKillLaw` — the pointwise paper law, verbatim.
* `KillMassLaw` — the summed finite-sum law.
* `pointKillLaw_implies_killMass` — the pointwise law implies the sum.
* `stageOneConditionalLower_of_killMass` — `StageOneConditionalLower` from the
  **finite-sum** law, with no pointwise hypothesis.
* `stageOneConditionalLower_iff_killMass` — in the nondegenerate case the
  conditional lower bound is exactly the pair of mass inequalities, so no
  estimate is lost or hidden.
* `killMassLaw_strictly_weaker` — a two-order example in which the summed law
  holds but the pointwise law fails: the reduction is genuinely smaller.
* `scalarKillCount` and the `scalarCovers` results — the paper's concrete
  mechanism: the stage-one scalar `M` kills the points whose order divides
  `M`, so on a curve of order `j` with `j ∣ M` all `j` points are killed.  On a
  cyclic group the killed count is `Nat.gcd j M`.
* `L27KillLawInputs` — the gcd-exit and kill-law data with `kill_mass` in place
  of the pointwise field, reassembling `L27StageOneInputs`, the L27.1
  reduction, and the `1 - 1/p` success cap.

No probability is set to zero, no killed point is discarded, and no `sorry`,
`admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL27KillLaw

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27StageOne
open Cogentic.RandomizedL27GcdModel
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The pointwise law and its finite-sum form -/

/-- **The paper's point-kill law.**  On every stage-one-smooth curve of order
`j`, the stage-one scalar kills at least a `1 / log y` fraction of the `j`
points.  This is the hypothesis used by
`stageOneConditionalLower_of_pointKill`. -/
def PointKillLaw (I : L27_1Inputs) (pointKill : ℕ → ℕ → ℕ) : Prop :=
  ∀ n j, I.smooth n j = true →
    (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n)

/-- **The finite-sum kill law.**  The `1 / log y` point fraction, summed
against the Deuring curve counts, bounds the whole smooth point mass.  This is
the smallest finite-sum statement used by the conditional-success proof; it
does not require the pointwise inequality at every order. -/
def KillMassLaw (I : L27_1Inputs) (pointKill : ℕ → ℕ → ℕ) : Prop :=
  ∀ n, smoothPointMass I n ≤
    killedPointMass I pointKill n * Real.log (I.y n)

/-- The pointwise paper law implies its weighted-sum form. -/
theorem pointKillLaw_implies_killMass (I : L27_1Inputs)
    (pointKill : ℕ → ℕ → ℕ) (h : PointKillLaw I pointKill) :
    KillMassLaw I pointKill :=
  fun n => pointMass_le_killedMass_mul_log I pointKill h n

/-- The finite-sum shape is strictly weaker than the pointwise shape.  With two
smooth orders `1, 2`, unit Deuring weights, `log y = 1`, and killed counts
`pointKill 1 = 2`, `pointKill 2 = 1`, the weighted mass inequality holds with
equality (`3 ≤ 3`), while the pointwise inequality fails at `j = 2`. -/
theorem killMassLaw_strictly_weaker :
    ∃ (orderCount pointKill : ℕ → ℕ) (logy : ℝ),
      (∑ j ∈ ({1, 2} : Finset ℕ), (j : ℝ) * (orderCount j : ℝ)) ≤
        (∑ j ∈ ({1, 2} : Finset ℕ),
          (pointKill j : ℝ) * (orderCount j : ℝ)) * logy ∧
      ¬ (∀ j ∈ ({1, 2} : Finset ℕ),
        (j : ℝ) ≤ (pointKill j : ℝ) * logy) := by
  refine ⟨fun _ => 1, fun j => if j = 2 then 1 else 2, 1, ?_, ?_⟩
  · norm_num [Finset.sum_insert]
  · intro h
    have h2 := h 2 (by norm_num)
    norm_num at h2

/-! ## 2. `StageOneConditionalLower` from the finite-sum law -/

/-- **The finite-sum kill law gives `StageOneConditionalLower`.**  This is
`stageOneConditionalLower_of_pointKill` with the pointwise hypothesis replaced
by its weighted sum.  The conditional success is the explicit killed mass
divided by the smooth point mass; no probability is set to zero. -/
theorem stageOneConditionalLower_of_killMass (I : L27_1Inputs)
    (pointKill : ℕ → ℕ → ℕ)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : KillMassLaw I pointKill)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I pointKill) I.y := by
  constructor
  · intro n
    have hCT : 0 < I.CT n := I.curveTotal_pos n
    have hSC : 0 ≤ I.SC n := by
      simpa [L27_1Inputs.SC] using
        smoothCurves_nonneg I.smooth I.orderCount I.orderTop n
    have hP : 0 ≤ smoothPointMass I n := smoothPointMass_nonneg I n
    have hK : 0 ≤ killedPointMass I pointKill n :=
      killedPointMass_nonneg I pointKill n
    have hSCP : I.SC n ≤ smoothPointMass I n :=
      smoothCurves_le_pointMass I horder n
    have hKP : killedPointMass I pointKill n ≤ I.success n * I.CT n :=
      hsuccess n
    by_cases hP0 : smoothPointMass I n = 0
    · have hSC0 : I.SC n = 0 := le_antisymm (by simpa [hP0] using hSCP) hSC
      have hzero : I.SC n / I.CT n * conditionalSuccess I pointKill n = 0 := by
        rw [hSC0, conditionalSuccess]
        simp [hP0]
      rw [hzero]
      exact success_nonneg I n
    · have hPpos : 0 < smoothPointMass I n := lt_of_le_of_ne hP (Ne.symm hP0)
      have hcond : conditionalSuccess I pointKill n =
          killedPointMass I pointKill n / smoothPointMass I n := by
        unfold conditionalSuccess
        simp [hP0]
      rw [hcond]
      have hmain : (I.SC n / I.CT n) *
            (killedPointMass I pointKill n / smoothPointMass I n) ≤
          killedPointMass I pointKill n / I.CT n := by
        rw [div_mul_div_comm]
        rw [div_le_div_iff₀ (mul_pos hCT hPpos) hCT]
        have hmul : I.SC n * killedPointMass I pointKill n ≤
            smoothPointMass I n * killedPointMass I pointKill n :=
          mul_le_mul_of_nonneg_right hSCP hK
        calc
          (I.SC n * killedPointMass I pointKill n) * I.CT n
              ≤ (smoothPointMass I n * killedPointMass I pointKill n) *
                  I.CT n :=
            mul_le_mul_of_nonneg_right hmul hCT.le
          _ = killedPointMass I pointKill n *
                (I.CT n * smoothPointMass I n) := by ring
      have hKC : killedPointMass I pointKill n / I.CT n ≤ I.success n := by
        rw [div_le_iff₀ hCT]
        exact hKP
      exact hmain.trans hKC
  · intro n
    have hP : 0 ≤ smoothPointMass I n := smoothPointMass_nonneg I n
    by_cases hP0 : smoothPointMass I n = 0
    · have hcond : conditionalSuccess I pointKill n = 1 := by
        unfold conditionalSuccess
        simp [hP0]
      rw [hcond]
      simpa using hlog n
    · have hPpos : 0 < smoothPointMass I n := lt_of_le_of_ne hP (Ne.symm hP0)
      have hcond : conditionalSuccess I pointKill n =
          killedPointMass I pointKill n / smoothPointMass I n := by
        unfold conditionalSuccess
        simp [hP0]
      rw [hcond]
      have hEq : (killedPointMass I pointKill n / smoothPointMass I n) *
            Real.log (I.y n) =
          (killedPointMass I pointKill n * Real.log (I.y n)) /
            smoothPointMass I n := by ring
      rw [hEq, one_le_div hPpos]
      exact hkill n

/-- The pointwise paper law recovers `StageOneConditionalLower` through the
finite-sum reduction.  This is the same conclusion as
`stageOneConditionalLower_of_pointKill`, now obtained without using the
pointwise law anywhere past the sum. -/
theorem stageOneConditionalLower_of_pointKill_law (I : L27_1Inputs)
    (pointKill : ℕ → ℕ → ℕ)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : PointKillLaw I pointKill)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I pointKill) I.y :=
  stageOneConditionalLower_of_killMass I pointKill horder hsuccess
    (pointKillLaw_implies_killMass I pointKill hkill) hlog

/-! ## 3. Exact characterization by the two mass inequalities -/

/-- **Smallest explicit form of the conditional lower bound.**  When the smooth
point mass is positive, `StageOneConditionalLower` with the explicit
conditional success `killedPointMass / smoothPointMass` holds *iff* the two
finite-sum mass inequalities

* `SC * killedPointMass ≤ success * CT * smoothPointMass`, and
* `smoothPointMass ≤ killedPointMass * log y`

hold.  Both directions are proved, so this is an exact reduction and not just a
sufficient set of hypotheses. -/
theorem stageOneConditionalLower_iff_killMass (I : L27_1Inputs)
    (pointKill : ℕ → ℕ → ℕ)
    (hP : ∀ n, 0 < smoothPointMass I n) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
        (conditionalSuccess I pointKill) I.y ↔
      (∀ n, I.SC n * killedPointMass I pointKill n ≤
          I.success n * I.CT n * smoothPointMass I n) ∧
      KillMassLaw I pointKill := by
  have hcond : ∀ n, conditionalSuccess I pointKill n =
      killedPointMass I pointKill n / smoothPointMass I n := by
    intro n
    unfold conditionalSuccess
    simp [(hP n).ne']
  constructor
  · intro h
    constructor
    · intro n
      have hCT : 0 < I.CT n := I.curveTotal_pos n
      have hPn : 0 < smoothPointMass I n := hP n
      have h1 := h.1 n
      rw [hcond n, div_mul_div_comm] at h1
      have hle := (div_le_iff₀ (mul_pos hCT hPn)).1 h1
      calc
        I.SC n * killedPointMass I pointKill n
            ≤ I.success n * (I.CT n * smoothPointMass I n) := hle
        _ = I.success n * I.CT n * smoothPointMass I n := by ring
    · intro n
      have hPn : 0 < smoothPointMass I n := hP n
      have h2 := h.2 n
      rw [hcond n, div_mul_eq_mul_div] at h2
      exact (one_le_div hPn).1 h2
  · intro h
    constructor
    · intro n
      have hCT : 0 < I.CT n := I.curveTotal_pos n
      have hPn : 0 < smoothPointMass I n := hP n
      rw [hcond n, div_mul_div_comm,
        div_le_iff₀ (mul_pos hCT hPn)]
      calc
        I.SC n * killedPointMass I pointKill n
            ≤ I.success n * I.CT n * smoothPointMass I n := h.1 n
        _ = I.success n * (I.CT n * smoothPointMass I n) := by ring
    · intro n
      have hPn : 0 < smoothPointMass I n := hP n
      rw [hcond n, div_mul_eq_mul_div, one_le_div hPn]
      exact h.2 n

/-- Sufficient form: the two explicit mass inequalities give
`StageOneConditionalLower`. -/
theorem stageOneConditionalLower_of_massInequalities (I : L27_1Inputs)
    (pointKill : ℕ → ℕ → ℕ)
    (hP : ∀ n, 0 < smoothPointMass I n)
    (hprod : ∀ n, I.SC n * killedPointMass I pointKill n ≤
      I.success n * I.CT n * smoothPointMass I n)
    (hmass : KillMassLaw I pointKill) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I pointKill) I.y :=
  (stageOneConditionalLower_iff_killMass I pointKill hP).2 ⟨hprod, hmass⟩

/-! ## 4. The paper's concrete scalar mechanism -/

/-- Number of points of a cyclic group of order `j` killed by the scalar `M`:
exactly the points whose order divides `M`, i.e. `gcd j M` points. -/
def scalarKillCount (M j : ℕ) : ℕ :=
  Nat.gcd j M

/-- The scalar-killed count never exceeds the positive group order. -/
theorem scalarKillCount_le (M j : ℕ) (hj : 0 < j) :
    scalarKillCount M j ≤ j :=
  Nat.gcd_le_left M hj

/-- If the stage-one scalar is divisible by the smooth order, every point on a
cyclic curve of that order is killed. -/
theorem scalarKillCount_eq_self_of_dvd {M j : ℕ} (h : j ∣ M) :
    scalarKillCount M j = j :=
  Nat.gcd_eq_left h

/-- The scalar mechanism satisfies the pointwise paper law as soon as the
stage-one cutoff has `log y ≥ 1`: on a curve of order `j` with `j ∣ M`, all `j`
points are killed. -/
theorem scalarCovers_pointKillLaw (I : L27_1Inputs) (M : ℕ → ℕ)
    (hcover : ∀ n j, I.smooth n j = true → j ∣ M n)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    PointKillLaw I (fun n j => scalarKillCount (M n) j) := by
  intro n j hs
  change (j : ℝ) ≤ (scalarKillCount (M n) j : ℝ) * Real.log (I.y n)
  rw [scalarKillCount_eq_self_of_dvd (hcover n j hs)]
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  calc
    (j : ℝ) = (j : ℝ) * 1 := (mul_one _).symm
    _ ≤ (j : ℝ) * Real.log (I.y n) :=
      mul_le_mul_of_nonneg_left (hlog n) hj

/-- Under the scalar-cover hypothesis the killed point mass is the entire
smooth point mass: no killed point is discarded, and no point is counted
twice. -/
theorem killedPointMass_scalarCovers (I : L27_1Inputs) (M : ℕ → ℕ)
    (hcover : ∀ n j, I.smooth n j = true → j ∣ M n) (n : ℕ) :
    killedPointMass I (fun n j => scalarKillCount (M n) j) n =
      smoothPointMass I n := by
  unfold killedPointMass smoothPointMass
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases h : I.smooth n j = true
  · simp only [h, if_true]
    rw [scalarKillCount_eq_self_of_dvd (hcover n j h)]
  · simp [h]

/-- The scalar-cover mechanism gives the finite-sum kill law. -/
theorem scalarCovers_killMassLaw (I : L27_1Inputs) (M : ℕ → ℕ)
    (hcover : ∀ n j, I.smooth n j = true → j ∣ M n)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    KillMassLaw I (fun n j => scalarKillCount (M n) j) := by
  intro n
  rw [killedPointMass_scalarCovers I M hcover n]
  exact le_mul_of_one_le_right (smoothPointMass_nonneg I n) (hlog n)

/-- **`StageOneConditionalLower` from the paper's scalar kill mechanism.**  The
explicit killed-point count `gcd j M` satisfies the summed `1 / log y` law. -/
theorem stageOneConditionalLower_of_scalarCovers (I : L27_1Inputs)
    (M : ℕ → ℕ)
    (hcover : ∀ n j, I.smooth n j = true → j ∣ M n)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n,
      killedPointMass I (fun n j => scalarKillCount (M n) j) n ≤
        I.success n * I.CT n)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I (fun n j => scalarKillCount (M n) j)) I.y :=
  stageOneConditionalLower_of_killMass I
    (fun n j => scalarKillCount (M n) j) horder hsuccess
    (scalarCovers_killMassLaw I M hcover hlog) hlog

/-! ## 5. The bundled finite-sum kill inputs -/

/-- **The smallest explicit kill-law inputs.**  This is `L27GCDModelInputs`
with the pointwise field `point_fraction` replaced by the finite-sum law
`kill_mass`.  Every field is a paper-level count or inequality:

* `gcdFail_eq` — the singular-curve probability is exactly `1/p`;
* `noFactorData` — the no-factor count at the `p²` scale, containing the
  singular curves;
* `pointKill`, `kill_mass` — the killed-point count on a smooth curve and its
  summed `1 / log y` law;
* `success_ge_killed` — the killed-point mass is part of the success mass;
* `smooth_order_pos` — smooth orders are positive;
* `cutoff` — the stage-one cutoff satisfies `e ≤ y`.

No probability is set to zero and no point mass is discarded. -/
structure L27KillLawInputs (I : L27_1Inputs) where
  /-- The paper's singular-curve probability is exactly `1/p`. -/
  gcdFail_eq : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ)
  /-- The no-factor curve count at the singular-curve scale. -/
  noFactorData : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n)
  /-- Number of points killed on a curve of order `j`. -/
  pointKill : ℕ → ℕ → ℕ
  /-- Smooth curve orders are positive. -/
  smooth_order_pos : ∀ n j, I.smooth n j = true → 0 < j
  /-- The killed-point mass is contained in the success mass. -/
  success_ge_killed : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n
  /-- The finite-sum form of the paper's `1 / log y` point-kill law. -/
  kill_mass : KillMassLaw I pointKill
  /-- The stage-one cutoff satisfies `e ≤ y`. -/
  cutoff : StageOneCutoffExpOne I.y

namespace L27KillLawInputs

variable {I : L27_1Inputs}

/-- The concrete singular-curve `GCDExitCurveModel`. -/
noncomputable def gcdModel (S : L27KillLawInputs I) :
    GCDExitCurveModel I.p I.gcdFail (fun n => 1 - I.success n) :=
  paperGCDModelOfL27 I S.gcdFail_eq S.noFactorData

/-- The conditional success law from the finite-sum kill law. -/
theorem stageOneConditional (S : L27KillLawInputs I) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I S.pointKill) I.y :=
  stageOneConditionalLower_of_killMass I S.pointKill S.smooth_order_pos
    S.success_ge_killed S.kill_mass
    (stageOneCutoffLogGeOne_of_expOne S.cutoff)

/-- Reassemble `L27StageOneInputs` from the curve-count and finite-sum kill
data. -/
noncomputable def toStageOneInputs (S : L27KillLawInputs I) :
    L27StageOneInputs I where
  gcd_model := S.gcdModel
  condSuccess := conditionalSuccess I S.pointKill
  stage_one_conditional := S.stageOneConditional

/-- The bundled gcd-exit bound. -/
theorem gcdExitBound (S : L27KillLawInputs I) :
    GCDExitBound I.p I.gcdFail (fun n => 1 - I.success n) :=
  S.gcdModel.bound I.p_pos

/-- The bundled stage-one success bound. -/
theorem stageOneSuccess (S : L27KillLawInputs I) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop)
      I.y I.success :=
  stageOneSuccess_of_conditional S.stageOneConditional

/-- **The success probability is at most `1 - 1/p`.**  The no-factor event has
to contain the singular fraction `1/p`, so the model cannot set the failure
probability to zero. -/
theorem success_le_one_sub_inv (S : L27KillLawInputs I) (n : ℕ) :
    I.success n ≤ 1 - 1 / (I.p n : ℝ) := by
  have h : 1 / (I.p n : ℝ) ≤ 1 - I.success n :=
    PaperNoFactorCurveCount.inv_le S.noFactorData I.p_pos n
  linarith

/-- The four `L27Analytic` sub-`Prop`s, from the finite-sum kill model. -/
theorem toComponents (S : L27KillLawInputs I) :
    GCDExitNonneg I.gcdFail ∧ GCDExitLeInv I.p I.gcdFail ∧
      GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n) ∧
      StageOneSmoothMultiplicative I.SC I.CT I.y I.success :=
  S.toStageOneInputs.toComponents

/-- Reassemble `L27PaperInputs` from the finite-sum kill model and the Deuring
side. -/
theorem toPaperInputs (S : L27KillLawInputs I)
    (hcount : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ)
    (htotal : HasseWindowCurveTotal I.p I.orderCount I.orderTop)
    (hhasse : HasseBound I.p I.orderCount) : L27PaperInputs I :=
  S.toStageOneInputs.toPaperInputs hcount htotal hhasse

/-- **The L27.1 reduction from the finite-sum kill model.** -/
theorem reduction (S : L27KillLawInputs I)
    (hcount : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ)
    (htotal : HasseWindowCurveTotal I.p I.orderCount I.orderTop)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  reduction_of_stageInputs S.toStageOneInputs hcount htotal hhasse hbudget hlog

end L27KillLawInputs

/-- The pointwise model of `RandomizedL27GcdModel` is an instance of the
finite-sum model: its `point_fraction` field implies `kill_mass`. -/
noncomputable def L27GCDModelInputs.toKillLawInputs {I : L27_1Inputs}
    (S : L27GCDModelInputs I) : L27KillLawInputs I where
  gcdFail_eq := S.gcdFail_eq
  noFactorData := S.noFactorData
  pointKill := S.pointKill
  smooth_order_pos := S.smooth_order_pos
  success_ge_killed := S.success_ge_killed
  kill_mass := pointKillLaw_implies_killMass I S.pointKill S.point_fraction
  cutoff := S.cutoff

/-- Direct construction of `L27KillLawInputs` with smooth-order positivity
derived from `p ≥ 2`. -/
noncomputable def L27KillLawInputs.of_two_le (I : L27_1Inputs)
    (hp : ∀ n, 2 ≤ I.p n)
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n))
    (pointKill : ℕ → ℕ → ℕ)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : KillMassLaw I pointKill)
    (hcutoff : StageOneCutoffExpOne I.y) : L27KillLawInputs I where
  gcdFail_eq := hgf
  noFactorData := D
  pointKill := pointKill
  smooth_order_pos := fun _ _ hs => smooth_order_pos_of_two_le I hp hs
  success_ge_killed := hsuccess
  kill_mass := hkill
  cutoff := hcutoff

/-! ## Axiom audit -/

#print axioms pointKillLaw_implies_killMass
#print axioms killMassLaw_strictly_weaker
#print axioms stageOneConditionalLower_of_killMass
#print axioms stageOneConditionalLower_of_pointKill_law
#print axioms stageOneConditionalLower_iff_killMass
#print axioms stageOneConditionalLower_of_massInequalities
#print axioms scalarKillCount_le
#print axioms scalarKillCount_eq_self_of_dvd
#print axioms scalarCovers_pointKillLaw
#print axioms killedPointMass_scalarCovers
#print axioms scalarCovers_killMassLaw
#print axioms stageOneConditionalLower_of_scalarCovers
#print axioms L27KillLawInputs.gcdModel
#print axioms L27KillLawInputs.stageOneConditional
#print axioms L27KillLawInputs.toStageOneInputs
#print axioms L27KillLawInputs.gcdExitBound
#print axioms L27KillLawInputs.stageOneSuccess
#print axioms L27KillLawInputs.success_le_one_sub_inv
#print axioms L27KillLawInputs.toComponents
#print axioms L27KillLawInputs.toPaperInputs
#print axioms L27KillLawInputs.reduction
#print axioms L27GCDModelInputs.toKillLawInputs
#print axioms L27KillLawInputs.of_two_le

end

end Cogentic.RandomizedL27KillLaw
