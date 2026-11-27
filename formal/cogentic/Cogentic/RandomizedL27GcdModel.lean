import Cogentic.RandomizedL27StageOne

/-!
# L27 gcd exits and stage one: explicit curve-count and point-kill models

`Cogentic.RandomizedL27StageOne` reduces the gcd-exit hypotheses to a finite
`GCDExitCurveModel` and the stage-one hypothesis to the conditional-success
statement `StageOneConditionalLower`, but leaves the *data* of those two models
abstract.  This file supplies the paper's singular-curve count and the paper's
point-kill law as concrete, smallest-possible inputs.

## Gcd exits: the singular-curve count

A Weierstrass curve `y² = x³ + ax + b` over `F_p` is singular exactly when its
discriminant `-16 (4a³ + 27b²)` vanishes.  There are `p²` pairs `(a, b)`, and
`p` of them are singular for the target prime `p` (the paper's Lemma 7.2 count;
the `≤` form is all that is used).  Hence the bad fraction is exactly `1 / p`.
The file records this as

* `singularCurveTotal p n = p n ^ 2` — total number of curves;
* `singularCurveCount p n = p n` — number of singular curves;
* `PaperNoFactorCurveCount` — the number of curves in the no-factor event,
  together with its two count inequalities.

`paperGCDModelOf` then builds the concrete `GCDExitCurveModel` with `total` and
`bad` equal to those counts, `gcdFail = 1 / p`, and the no-factor count supplied
by `PaperNoFactorCurveCount`.  No probability is set to zero: the no-factor
probability is the genuine fraction `noFac / p²`, and containment is the count
inequality `p ≤ noFac`.

## Stage one: the paper's conditional kill law

For a curve whose group order is stage-one smooth, the paper's stage-one scalar
kills at least a `1 / log y` fraction of the points.  The file models the killed
points by a count `pointKill n j` and isolates the two smallest statements:

* `point_fraction` — `j ≤ pointKill n j · log y` on every smooth order `j`
  (a fraction `1 / log y` of the `j` points is killed);
* `success_ge_killed` — the killed-point mass on smooth curves is contained in
  the total success mass: `killedPointMass ≤ success · CT`.

`stageOneConditionalLower_of_pointKill` proves `StageOneConditionalLower` with
the explicit conditional success

`condSuccess n = killedPointMass n / smoothPointMass n`

(and `condSuccess n = 1` in the degenerate case where there are no smooth
points).  The proof is pure finite-sum arithmetic: `SC ≤ smoothPointMass` since
smooth orders are positive, and the `1 / log y` law is summed against the curve
counts.  No probability decomposition is hidden: both count inequalities are
fields of the model.

`L27GCDModelInputs` bundles the singular-curve model, the no-factor counts, the
point-kill law, and the cutoff `e ≤ y`; it reassembles `L27StageOneInputs`, both
`L27_1Sub` hypotheses, and the final L27.1 reduction.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL27GcdModel

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27StageOne
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The paper's singular-curve count -/

/-- Total number of Weierstrass curves `y² = x³ + ax + b` over `F_p`: `p²`
pairs `(a, b)`. -/
def singularCurveTotal (p : ℕ → ℕ) (n : ℕ) : ℕ :=
  p n ^ 2

/-- Number of singular Weierstrass curves over `F_p`: the solutions of
`4a³ + 27b² = 0`, of which there are `p` for the target prime `p`.  This is the
paper's Lemma 7.2 count. -/
def singularCurveCount (p : ℕ → ℕ) (n : ℕ) : ℕ :=
  p n

/-- **The singular fraction is `1 / p`.**  The bad count `p` over the total
`p²` is exactly `1/p`. -/
theorem singularCurveCount_fraction (p : ℕ → ℕ) (hp : ∀ n, 0 < p n) (n : ℕ) :
    (singularCurveCount p n : ℝ) / (singularCurveTotal p n : ℝ) =
      1 / (p n : ℝ) := by
  have hp' : (p n : ℝ) ≠ 0 := by exact_mod_cast (hp n).ne'
  unfold singularCurveCount singularCurveTotal
  rw [pow_two, Nat.cast_mul]
  field_simp [hp']

/-- **The counting estimate `bad · p ≤ total`.**  The singular count `p` times
`p` is at most the total `p²`. -/
theorem singularCurveCount_mul_le (p : ℕ → ℕ) (n : ℕ) :
    singularCurveCount p n * p n ≤ singularCurveTotal p n := by
  unfold singularCurveCount singularCurveTotal
  rw [pow_two]

/-- The singular-curve fraction is at most `1 / p`, in the cleared form used by
`GCDExitCurveCountBound`. -/
theorem singularCurveCount_mul_le_cast (p : ℕ → ℕ) (n : ℕ) :
    (singularCurveCount p n : ℝ) * (p n : ℝ) ≤
      (singularCurveTotal p n : ℝ) := by
  exact_mod_cast singularCurveCount_mul_le p n

/-- **The no-factor curve count at the paper's singular-curve scale.**  `noFac`
is the number of curves in the no-factor event among the `p²` Weierstrass
curves; its fraction is the no-factor probability, and it contains every
singular curve. -/
structure PaperNoFactorCurveCount (p : ℕ → ℕ) (noFactor : ℕ → ℝ) where
  /-- Number of curves in the no-factor event. -/
  noFac : ℕ → ℕ
  /-- The no-factor probability is the no-factor curve fraction. -/
  noFac_eq : ∀ n, noFactor n = (noFac n : ℝ) / (singularCurveTotal p n : ℝ)
  /-- Every singular curve produces no factor. -/
  bad_le_noFac : ∀ n, singularCurveCount p n ≤ noFac n
  /-- The count is a subset of all curves. -/
  noFac_le_total : ∀ n, noFac n ≤ singularCurveTotal p n

namespace PaperNoFactorCurveCount

variable {p : ℕ → ℕ} {noFactor : ℕ → ℝ}

/-- Positivity of the total curve count. -/
theorem total_pos (hp : ∀ n, 0 < p n) (n : ℕ) :
    (0 : ℝ) < (singularCurveTotal p n : ℝ) := by
  unfold singularCurveTotal
  exact_mod_cast pow_pos (hp n) 2

/-- The no-factor probability is nonnegative. -/
theorem nonneg (D : PaperNoFactorCurveCount p noFactor) (hp : ∀ n, 0 < p n)
    (n : ℕ) : 0 ≤ noFactor n := by
  rw [D.noFac_eq n]
  exact div_nonneg (Nat.cast_nonneg _) (total_pos hp n).le

/-- The no-factor probability is at most one. -/
theorem le_one (D : PaperNoFactorCurveCount p noFactor) (hp : ∀ n, 0 < p n)
    (n : ℕ) : noFactor n ≤ 1 := by
  rw [D.noFac_eq n]
  rw [div_le_one₀ (total_pos hp n)]
  exact_mod_cast D.noFac_le_total n

/-- **The no-factor event contains the singular fraction `1/p`.**  This is the
count-level form of `p ≤ noFac`; for `noFactor = 1 - success` it says that the
success probability cannot exceed `1 - 1/p`. -/
theorem inv_le (D : PaperNoFactorCurveCount p noFactor) (hp : ∀ n, 0 < p n)
    (n : ℕ) : 1 / (p n : ℝ) ≤ noFactor n := by
  have hT : (0 : ℝ) < (singularCurveTotal p n : ℝ) := total_pos hp n
  have hdiv : (singularCurveCount p n : ℝ) / (singularCurveTotal p n : ℝ) ≤
      (D.noFac n : ℝ) / (singularCurveTotal p n : ℝ) :=
    div_le_div_of_nonneg_right
      (by exact_mod_cast D.bad_le_noFac n) hT.le
  rw [D.noFac_eq n]
  calc
    1 / (p n : ℝ) =
        (singularCurveCount p n : ℝ) / (singularCurveTotal p n : ℝ) :=
      (singularCurveCount_fraction p hp n).symm
    _ ≤ (D.noFac n : ℝ) / (singularCurveTotal p n : ℝ) := hdiv

end PaperNoFactorCurveCount

/-- **The concrete gcd-exit curve model.**  The total is `p²`, the bad count is
the singular count `p`, the bad probability is `1/p`, and the no-factor
probability is the supplied count fraction.  Nonnegativity, the `1/p` bound,
and containment are then the three paper-level statements in count form. -/
noncomputable def paperGCDModelOf (p : ℕ → ℕ) (hp : ∀ n, 0 < p n)
    (gcdFail noFactor : ℕ → ℝ)
    (hgf : ∀ n, gcdFail n = 1 / (p n : ℝ))
    (D : PaperNoFactorCurveCount p noFactor) :
    GCDExitCurveModel p gcdFail noFactor where
  total := singularCurveTotal p
  bad := singularCurveCount p
  noFac := D.noFac
  total_pos := by
    intro n
    unfold singularCurveTotal
    exact pow_pos (hp n) 2
  gcdFail_eq := by
    intro n
    rw [hgf n]
    exact (singularCurveCount_fraction p hp n).symm
  noFactor_eq := D.noFac_eq
  count_bound := singularCurveCount_mul_le_cast p
  containment := D.bad_le_noFac

/-- The paper's singular-curve model with the canonical bad probability
`gcdFail = 1 / p`. -/
noncomputable def paperGCDModel (p : ℕ → ℕ) (hp : ∀ n, 0 < p n)
    (noFactor : ℕ → ℝ) (D : PaperNoFactorCurveCount p noFactor) :
    GCDExitCurveModel p (fun n => 1 / (p n : ℝ)) noFactor :=
  paperGCDModelOf p hp _ noFactor (fun _ => rfl) D

/-- The concrete model for the L27 data: the paper's singular-curve probability
is `1/p`, and the no-factor event is counted at the `p²` scale. -/
noncomputable def paperGCDModelOfL27 (I : L27_1Inputs)
    (hgf : ∀ n, I.gcdFail n = 1 / (I.p n : ℝ))
    (D : PaperNoFactorCurveCount I.p (fun n => 1 - I.success n)) :
    GCDExitCurveModel I.p I.gcdFail (fun n => 1 - I.success n) :=
  paperGCDModelOf I.p I.p_pos I.gcdFail (fun n => 1 - I.success n) hgf D

/-- The singular-curve model directly gives the bundled `GCDExitBound`. -/
theorem gcdExitBound_of_paperSingular (p : ℕ → ℕ) (hp : ∀ n, 0 < p n)
    (gcdFail noFactor : ℕ → ℝ)
    (hgf : ∀ n, gcdFail n = 1 / (p n : ℝ))
    (D : PaperNoFactorCurveCount p noFactor) :
    GCDExitBound p gcdFail noFactor :=
  (paperGCDModelOf p hp gcdFail noFactor hgf D).bound hp

/-! ## 2. Smooth-order point masses -/

/-- Total number of points on stage-one-smooth curves, weighted by the Deuring
curve count. -/
def smoothPointMass (I : L27_1Inputs) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (I.orderTop n + 1),
    if I.smooth n j then (j : ℝ) * (I.orderCount n j : ℝ) else 0

/-- Number of points killed by the stage-one scalar on stage-one-smooth curves,
weighted by the Deuring curve count.  `pointKill n j` is the number of killed
points on a curve of order `j`. -/
def killedPointMass (I : L27_1Inputs) (pointKill : ℕ → ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (I.orderTop n + 1),
    if I.smooth n j then (pointKill n j : ℝ) * (I.orderCount n j : ℝ) else 0

/-- The conditional success probability on a smooth-order curve: the killed
point mass divided by the total point mass.  In the degenerate case of no
smooth points it is set to `1`, which still satisfies the `1 / log y` lower
bound under the cutoff hypothesis. -/
def conditionalSuccess (I : L27_1Inputs) (pointKill : ℕ → ℕ → ℕ)
    (n : ℕ) : ℝ :=
  if smoothPointMass I n = 0 then 1
  else killedPointMass I pointKill n / smoothPointMass I n

/-- The smooth point mass is nonnegative. -/
theorem smoothPointMass_nonneg (I : L27_1Inputs) (n : ℕ) :
    0 ≤ smoothPointMass I n := by
  unfold smoothPointMass
  apply Finset.sum_nonneg
  intro j _
  by_cases h : I.smooth n j = true
  · simp only [h, if_true]
    positivity
  · simp [h]

/-- The killed point mass is nonnegative. -/
theorem killedPointMass_nonneg (I : L27_1Inputs) (pointKill : ℕ → ℕ → ℕ)
    (n : ℕ) : 0 ≤ killedPointMass I pointKill n := by
  unfold killedPointMass
  apply Finset.sum_nonneg
  intro j _
  by_cases h : I.smooth n j = true
  · simp only [h, if_true]
    positivity
  · simp [h]

/-- The per-curve success probability is nonnegative.  This follows from the
stage-one bound itself: `SF / log y ≤ success` with `SF ≥ 0` and `log y > 0`. -/
theorem success_nonneg (I : L27_1Inputs) (n : ℕ) : 0 ≤ I.success n := by
  have hstage : smoothFraction I.smooth I.orderCount I.orderTop n /
      Real.log (I.y n) ≤ I.success n := I.stage_one n
  have hSF : 0 ≤ smoothFraction I.smooth I.orderCount I.orderTop n := by
    unfold smoothFraction
    exact div_nonneg
      (by simpa [L27_1Inputs.SC] using
        smoothCurves_nonneg I.smooth I.orderCount I.orderTop n)
      (I.curveTotal_pos n).le
  have hlog : 0 < Real.log (I.y n) := I.log_y_pos n
  exact (div_nonneg hSF hlog.le).trans hstage

/-- **Smooth curve count is at most the smooth point mass.**  Every smooth
curve has a positive order, and a curve of order `j` contributes `j` points. -/
theorem smoothCurves_le_pointMass (I : L27_1Inputs)
    (horder : ∀ n j, I.smooth n j = true → 0 < j) (n : ℕ) :
    I.SC n ≤ smoothPointMass I n := by
  unfold L27_1Inputs.SC smoothCurves smoothPointMass
  apply Finset.sum_le_sum
  intro j _
  by_cases h : I.smooth n j = true
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast horder n j h
    have hc : (0 : ℝ) ≤ (I.orderCount n j : ℝ) := Nat.cast_nonneg _
    simp only [h, if_true]
    calc
      (I.orderCount n j : ℝ) = 1 * (I.orderCount n j : ℝ) := (one_mul _).symm
      _ ≤ (j : ℝ) * (I.orderCount n j : ℝ) :=
        mul_le_mul_of_nonneg_right hj1 hc
  · simp [h]

/-- **Summed point-kill law.**  If at least a `1 / log y` fraction of the points
on every smooth curve is killed, then the whole smooth point mass is at most
`log y` times the killed mass. -/
theorem pointMass_le_killedMass_mul_log (I : L27_1Inputs)
    (pointKill : ℕ → ℕ → ℕ)
    (hkill : ∀ n j, I.smooth n j = true →
      (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n))
    (n : ℕ) :
    smoothPointMass I n ≤ killedPointMass I pointKill n * Real.log (I.y n) := by
  unfold smoothPointMass killedPointMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  by_cases h : I.smooth n j = true
  · have hc : (0 : ℝ) ≤ (I.orderCount n j : ℝ) := Nat.cast_nonneg _
    simp only [h, if_true]
    calc
      (j : ℝ) * (I.orderCount n j : ℝ)
          ≤ ((pointKill n j : ℝ) * Real.log (I.y n)) *
              (I.orderCount n j : ℝ) :=
        mul_le_mul_of_nonneg_right (hkill n j h) hc
      _ = (pointKill n j : ℝ) * (I.orderCount n j : ℝ) *
            Real.log (I.y n) := by ring
  · simp [h]

/-- A smooth order is positive, hence the `SC ≤ pointMass` comparison holds.
This is derived from Hasse's theorem and the target prime being at least `2`
(in the paper the least eligible prime factor is at least `5` after the
small-prime prepass, and `2` already suffices here). -/
theorem smooth_order_pos_of_two_le (I : L27_1Inputs)
    (hp : ∀ n, 2 ≤ I.p n) {n j : ℕ} (hs : I.smooth n j = true) : 0 < j := by
  have hne : I.orderCount n j ≠ 0 := I.smooth_realized n j hs
  have hhasse := I.hasse n j hne
  have hlow := hasse_lower hhasse
  have hpR : (2 : ℝ) ≤ (I.p n : ℝ) := by exact_mod_cast hp n
  have hp1 : (0 : ℝ) < (I.p n : ℝ) := by linarith
  have hsqrt_ne : Real.sqrt (I.p n) ≠ 1 := by
    intro h
    have hsq := Real.sq_sqrt hp1.le
    have hp_eq : (I.p n : ℝ) = 1 := by rw [← hsq, h]; norm_num
    linarith
  have hsqpos : 0 < (Real.sqrt (I.p n) - 1) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hsqrt_ne)
  have hstrict : 2 * Real.sqrt (I.p n) < (I.p n : ℝ) + 1 := by
    nlinarith [hsqpos, Real.sq_sqrt hp1.le]
  have hposR : (0 : ℝ) < (j : ℝ) := by linarith
  exact_mod_cast hposR

/-- **The paper's conditional success law implies `StageOneConditionalLower`.**
The two explicit inputs are the summed fraction law and the containment of the
killed mass in the success mass.  The conditional success is the actual ratio
`killedPointMass / smoothPointMass`; no probability is discarded. -/
theorem stageOneConditionalLower_of_pointKill (I : L27_1Inputs)
    (pointKill : ℕ → ℕ → ℕ)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n, killedPointMass I pointKill n ≤ I.success n * I.CT n)
    (hkill : ∀ n j, I.smooth n j = true →
      (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n))
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
      exact pointMass_le_killedMass_mul_log I pointKill hkill n

/-- The full-kill law is the special case `pointKill n j = j`: it yields
`StageOneSmoothKillsAll` from the single containment of the smooth point mass in
the success mass. -/
theorem stageOneSmoothKillsAll_of_pointMass (I : L27_1Inputs)
    (horder : ∀ n j, I.smooth n j = true → 0 < j)
    (hsuccess : ∀ n, smoothPointMass I n ≤ I.success n * I.CT n) :
    StageOneSmoothKillsAll I.SC I.CT I.success :=
  fun n => (smoothCurves_le_pointMass I horder n).trans (hsuccess n)

/-- With full kill (`pointKill n j = j`), the paper's fraction law reduces to
the cutoff estimate `1 ≤ log y`. -/
theorem pointKill_self_fraction (I : L27_1Inputs)
    (hlog : ∀ n, 1 ≤ Real.log (I.y n)) :
    ∀ n j, I.smooth n j = true →
      (j : ℝ) ≤ (j : ℝ) * Real.log (I.y n) := by
  intro n j _
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  simpa using mul_le_mul_of_nonneg_left (hlog n) hj

/-! ## 3. The bundled smallest explicit inputs -/

/-- **The smallest explicit gcd/kill inputs.**  Every field is a single
paper-level count or law:

* `gcdFail_eq` — the singular-curve probability is exactly `1/p`;
* `noFactorData` — the no-factor count at the `p²` scale, containing the
  singular curves;
* `pointKill`, `point_fraction` — the number of killed points on a smooth
  curve and the paper's `1 / log y` fraction;
* `success_ge_killed` — the killed-point mass is part of the success mass;
* `smooth_order_pos` — smooth orders are positive;
* `cutoff` — the stage-one cutoff satisfies `e ≤ y`.

No probability is set to zero and no point mass is discarded. -/
structure L27GCDModelInputs (I : L27_1Inputs) where
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
  /-- The paper's conditional kill law: a `1 / log y` fraction of the points on
  a smooth curve is killed. -/
  point_fraction : ∀ n j, I.smooth n j = true →
    (j : ℝ) ≤ (pointKill n j : ℝ) * Real.log (I.y n)
  /-- The stage-one cutoff satisfies `e ≤ y`. -/
  cutoff : StageOneCutoffExpOne I.y

namespace L27GCDModelInputs

variable {I : L27_1Inputs}

/-- The concrete singular-curve `GCDExitCurveModel`. -/
noncomputable def gcdModel (S : L27GCDModelInputs I) :
    GCDExitCurveModel I.p I.gcdFail (fun n => 1 - I.success n) :=
  paperGCDModelOfL27 I S.gcdFail_eq S.noFactorData

/-- The conditional success law with the explicit ratio. -/
theorem stageOneConditional (S : L27GCDModelInputs I) :
    StageOneConditionalLower (fun n => I.SC n / I.CT n) I.success
      (conditionalSuccess I S.pointKill) I.y :=
  stageOneConditionalLower_of_pointKill I S.pointKill S.smooth_order_pos
    S.success_ge_killed S.point_fraction
    (stageOneCutoffLogGeOne_of_expOne S.cutoff)

/-- Reassemble `L27StageOneInputs` from the concrete curve-count and kill-law
data. -/
noncomputable def toStageOneInputs (S : L27GCDModelInputs I) :
    L27StageOneInputs I where
  gcd_model := S.gcdModel
  condSuccess := conditionalSuccess I S.pointKill
  stage_one_conditional := S.stageOneConditional

/-- The bundled gcd-exit bound. -/
theorem gcdExitBound (S : L27GCDModelInputs I) :
    GCDExitBound I.p I.gcdFail (fun n => 1 - I.success n) :=
  S.gcdModel.bound I.p_pos

/-- The bundled stage-one success bound. -/
theorem stageOneSuccess (S : L27GCDModelInputs I) :
    StageOneSuccess (smoothFraction I.smooth I.orderCount I.orderTop)
      I.y I.success :=
  stageOneSuccess_of_conditional S.stageOneConditional

/-- **The success probability is at most `1 - 1/p`.**  The no-factor event has
to contain the singular fraction `1/p`, so the model cannot set the failure
probability to zero. -/
theorem success_le_one_sub_inv (S : L27GCDModelInputs I) (n : ℕ) :
    I.success n ≤ 1 - 1 / (I.p n : ℝ) := by
  have h : 1 / (I.p n : ℝ) ≤ 1 - I.success n :=
    PaperNoFactorCurveCount.inv_le S.noFactorData I.p_pos n
  linarith

/-- The four `L27Analytic` sub-`Prop`s, from the concrete models. -/
theorem toComponents (S : L27GCDModelInputs I) :
    GCDExitNonneg I.gcdFail ∧ GCDExitLeInv I.p I.gcdFail ∧
      GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n) ∧
      StageOneSmoothMultiplicative I.SC I.CT I.y I.success :=
  S.toStageOneInputs.toComponents

/-- Reassemble `L27PaperInputs` from the concrete gcd/kill model and the Deuring
side. -/
theorem toPaperInputs (S : L27GCDModelInputs I)
    (hcount : DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ)
    (htotal : HasseWindowCurveTotal I.p I.orderCount I.orderTop)
    (hhasse : HasseBound I.p I.orderCount) : L27PaperInputs I :=
  S.toStageOneInputs.toPaperInputs hcount htotal hhasse

/-- **The L27.1 reduction from the concrete gcd/kill model.** -/
theorem reduction (S : L27GCDModelInputs I)
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

end L27GCDModelInputs

/-- Direct construction of `L27GCDModelInputs` from the paper's singular count
with the positivity of smooth orders derived from `p ≥ 2`. -/
noncomputable def L27GCDModelInputs.of_two_le (I : L27_1Inputs)
    (hp : ∀ n, 2 ≤ I.p n)
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
  smooth_order_pos := fun _ _ hs => smooth_order_pos_of_two_le I hp hs
  success_ge_killed := hsuccess
  point_fraction := hkill
  cutoff := hcutoff

/-! ## Axiom audit -/

#print axioms singularCurveCount_fraction
#print axioms singularCurveCount_mul_le
#print axioms PaperNoFactorCurveCount.nonneg
#print axioms PaperNoFactorCurveCount.le_one
#print axioms PaperNoFactorCurveCount.inv_le
#print axioms paperGCDModelOf
#print axioms paperGCDModel
#print axioms paperGCDModelOfL27
#print axioms gcdExitBound_of_paperSingular
#print axioms smoothPointMass_nonneg
#print axioms killedPointMass_nonneg
#print axioms success_nonneg
#print axioms smoothCurves_le_pointMass
#print axioms pointMass_le_killedMass_mul_log
#print axioms smooth_order_pos_of_two_le
#print axioms stageOneConditionalLower_of_pointKill
#print axioms stageOneSmoothKillsAll_of_pointMass
#print axioms pointKill_self_fraction
#print axioms L27GCDModelInputs.gcdModel
#print axioms L27GCDModelInputs.stageOneConditional
#print axioms L27GCDModelInputs.toStageOneInputs
#print axioms L27GCDModelInputs.gcdExitBound
#print axioms L27GCDModelInputs.stageOneSuccess
#print axioms L27GCDModelInputs.success_le_one_sub_inv
#print axioms L27GCDModelInputs.toComponents
#print axioms L27GCDModelInputs.toPaperInputs
#print axioms L27GCDModelInputs.reduction
#print axioms L27GCDModelInputs.of_two_le

end

end Cogentic.RandomizedL27GcdModel
