import Cogentic.RandomizedPaperLeafStatements

/-!
# L27.1: the Lenstra–Pomerance ECM failure estimate

The manuscript's L27.1 (blueprint §2 C5.b `[INFRA]`, Lenstra–Pomerance,
*A rigorous time bound for factoring integers*, Theorem 7.1;
`research/keybreak-private-elliptic-recognition.md` §"Transfer to the
private-coordinate procedure") bounds the failure probability of `m`
independent elliptic-curve trials over `Z/nZ` by

`c₆ ^ (#curves · ψ₀ / (√p log y))`,  `0 < c₆ < 1`,

where `p` is the least prime factor of the current cofactor, `y` is the
stage-one cutoff, and `ψ₀` counts the stage-one smooth orders in the Hasse
window.  The paper's proof splits into four inputs, all stated here as explicit
`Prop`s and none of them proved:

1. **Curves over `Z/nZ` and gcd exits** (`GCDExitBound`): a random Weierstrass
   curve and point either produce a nontrivial gcd of `n` during the group law
   (a *gcd exit*, counted as success) or are a well-defined curve modulo `p`;
   the bad all-singular event has probability at most `1/p` and is contained in
   the no-factor event.

2. **Hasse** (`HasseBound`): every realised order `#E(F_p)` lies in
   `[p + 1 - 2√p, p + 1 + 2√p]`.  This is what lets the finite sums over curve
   orders run over `Finset.range (orderTop + 1)`.

3. **Deuring/Lenstra counts** (`deuring_count`, `psi_card`, `curve_total_le`):
   each stage-one smooth order is realised by at least `κ√p` curves (the
   Hurwitz class-number scale), `ψ₀` counts those orders, and the total number
   of curves in the Hasse window is at most `4p`.

4. **Stage-one success given a smooth order** (`StageOneSuccess`): the success
   probability of one curve is at least `smoothFraction / log y`.

The per-curve failure is then `1 - success ≤ exp (-(κ/4) · ψ₀/(√p log y))`,
which is exactly `c₆ ^ (ψ₀/(√p log y))` for `c₆ = exp (-κ/4)`.  Independence of
the `m` curve draws multiplies the exponent (`independence`), giving the paper's
rate.  The recursive L27.2 assembly multiplies the per-node failure by
`log₂ (cofactor)`, recorded as `LogFactorSubexp`; the small-factor prepass
`δ_small` is charged to the separate P1 leaf, so it is not smuggled into this
one.

The `ledger` field is the paper's curve-count choice (`CurveBudget`, the
`#curves ≥ exp((1/(2c) + η) T_y)` selection of `private-elliptic-recognition.md`
§Transfer): `m · ψ₀/(√p log y)` exceeds `(2 + η) H/(κ/4)` with a fixed headroom
`η > 0`.  This is the estimate that the quoted rate alone does not supply; it is
recorded as an input, never set to zero.  (L27.3's eligible-band count is a
supply input for the surrounding assembly and does not enter this loss.)  The
reduction then produces a genuine `RatedLeaf` and its `C5` slot.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL27_1

open Filter Real
open scoped BigOperators

open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## The paper-level sub-lemmas as explicit `Prop`s -/

/-- **Hasse's theorem** (LP §7).  Every curve order realised over `F_p` lies in
the Hasse interval `[p + 1 - 2√p, p + 1 + 2√p]`. -/
def HasseBound (p : ℕ → ℕ) (orderCount : ℕ → ℕ → ℕ) : Prop :=
  ∀ n j : ℕ, orderCount n j ≠ 0 →
    |(j : ℝ) - ((p n : ℝ) + 1)| ≤ 2 * Real.sqrt (p n)

/-- **Deuring/Lenstra count** (LP §7, Deuring's theorem together with the
Hurwitz class-number bound).  The `ψ₀` stage-one-smooth orders in the Hasse
window carry at least a `κ`-fraction of the `√p` curve classes:
`smoothCurves ≥ κ√p ψ₀`. -/
def DeuringSmoothCount (p : ℕ → ℕ) (psi smoothCurves : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∀ n, κ * Real.sqrt (p n) * psi n ≤ smoothCurves n

/-- **Curves over `Z/nZ` and gcd exits** (LP §7, Lemma 7.2).  A random
Weierstrass curve that is singular modulo the target prime produces a
nontrivial gcd of `n` with probability at least `1 - 1/p`; the bad event is one
of the no-factor events. -/
def GCDExitBound (p : ℕ → ℕ) (gcdFail noFactor : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ gcdFail n) ∧
    (∀ n, gcdFail n ≤ 1 / (p n : ℝ)) ∧
      ∀ n, gcdFail n ≤ noFactor n

/-- **Stage-one success given a smooth order.**  On the event that the order of
the curve is stage-one smooth, a random point is killed by the stage-one scalar
with probability at least `1 / log y`; hence the per-curve success probability
is at least `smoothFraction / log y`. -/
def StageOneSuccess (smoothFraction : ℕ → ℝ) (y : ℕ → ℝ) (success : ℕ → ℝ) : Prop :=
  ∀ n, smoothFraction n / Real.log (y n) ≤ success n

/-- **Curve-count choice (the paper's §Transfer parameter selection).**  The
number of curves `m` and the smooth density are chosen so that the LP exponent
exceeds `(2 + η) H / (κ/4)`, i.e. the failure `c₆ ^ (m ψ₀/(√p log y))` beats
`exp (-(2 + η) H)`.  This is an eventual choice; it is the extra estimate that
`RatedLeaf` records in its `ledger` field. -/
def CurveBudget (p : ℕ → ℕ) (y : ℕ → ℝ) (psi : ℕ → ℝ) (curves : ℕ → ℕ)
    (κ η : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (2 + η) * scale n ≤ (κ / 4) * ((curves n : ℝ) * (psi n / (Real.sqrt (p n) * Real.log (y n))))

/-- **L27.2 recursive multiplier.**  The `log₂` of the current cofactor is
subexponential on the `scale` (it is `exp (o(H))`); this is what lets the
recursive splitting factor `log₂ (cofactor)` be absorbed into the LP exponent. -/
def LogFactorSubexp (cofactor : ℕ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ((cofactor n).log2 : ℝ) ≤ exp (δ * scale n)

/-! ## Counting curves by their group order -/

/-- Number of curves over `F_p` whose group order is stage-one smooth, weighted
by the Deuring count `orderCount` of curves with each order. -/
def smoothCurves (smooth : ℕ → ℕ → Bool) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (orderTop n + 1),
    if smooth n j then (orderCount n j : ℝ) else 0

/-- Total number of curves over `F_p` in the Hasse window. -/
def curveTotal (orderCount : ℕ → ℕ → ℕ) (orderTop : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (orderTop n + 1), (orderCount n j : ℝ)

/-- Number of stage-one-smooth orders in the Hasse window. -/
def smoothCount (smooth : ℕ → ℕ → Bool) (orderTop : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (orderTop n + 1), if smooth n j then (1 : ℝ) else 0

/-- Fraction of curves over `F_p` whose order is stage-one smooth. -/
def smoothFraction (smooth : ℕ → ℕ → Bool) (orderCount : ℕ → ℕ → ℕ)
    (orderTop : ℕ → ℕ) (n : ℕ) : ℝ :=
  smoothCurves smooth orderCount orderTop n / curveTotal orderCount orderTop n

/-- LP's smooth density `ψ₀ / (√p log y)`, the per-curve success exponent. -/
def density (p : ℕ → ℕ) (y : ℕ → ℝ) (psi : ℕ → ℝ) (n : ℕ) : ℝ :=
  psi n / (Real.sqrt (p n) * Real.log (y n))

/-! ## The decomposed L27.1 inputs -/

/-- The four paper-level ECM inputs together with the explicit counting data and
the L27.2/L27.3 bookkeeping.  Every field is a hypothesis: the manuscript proves
the numbered inputs, and this file proves that they imply the `RatedLeaf` and its
`C5` slot.

The fields `hasse`, `deuring_count`, `gcd_exit` and `stage_one` are the four
Lenstra–Pomerance sub-lemmas named in the blueprint.  `curve_budget` is the
parameter choice (the `ledger` estimate); `logFactor_subexp` is the recursive
splitting multiplier of L27.2.  The deficit `loss` built below is
`log₂ (cofactor) · (1 - success) ^ curves`, so no loss is set to zero. -/
structure L27_1Inputs where
  /-- The target prime: the least eligible prime factor of the current
  cofactor. -/
  p : ℕ → ℕ
  /-- Stage-one cutoff `y`. -/
  y : ℕ → ℝ
  /-- Stage-one power bound `w ≥ y`. -/
  w : ℕ → ℝ
  /-- Number of independent curves drawn at each node. -/
  curves : ℕ → ℕ
  /-- LP's `ψ₀`: the number of stage-one smooth orders in the Hasse window. -/
  psi : ℕ → ℝ
  /-- Deuring/Lenstra count: the number of curves over `F_p` with exactly `j`
  points. -/
  orderCount : ℕ → ℕ → ℕ
  /-- An integer upper endpoint of the Hasse window. -/
  orderTop : ℕ → ℕ
  /-- The stage-one smoothness predicate on curve orders. -/
  smooth : ℕ → ℕ → Bool
  /-- Per-curve success probability. -/
  success : ℕ → ℝ
  /-- Probability of the bad gcd-exit event (singular curve, no factor). -/
  gcdFail : ℕ → ℝ
  /-- Joint failure probability of the `curves` independent draws. -/
  jointFail : ℕ → ℝ
  /-- The current cofactor whose prime factors are being split recursively. -/
  cofactor : ℕ → ℕ
  /-- The Deuring constant. -/
  κ : ℝ
  /-- Headroom in the curve-count choice. -/
  η : ℝ
  /-- The target prime is positive. -/
  p_pos : ∀ n, 0 < p n
  /-- The stage-one cutoff exceeds one. -/
  y_gt_one : ∀ n, 1 < y n
  /-- The stage-one power bound dominates the cutoff. -/
  y_le_w : ∀ n, y n ≤ w n
  /-- `ψ₀` is a count. -/
  psi_nonneg : ∀ n, 0 ≤ psi n
  /-- The Deuring constant is positive. -/
  κ_pos : 0 < κ
  /-- The curve-count headroom is positive. -/
  η_pos : 0 < η
  /-- The cofactor has a nontrivial `log₂`. -/
  cofactor_ge_two : ∀ n, 2 ≤ cofactor n
  /-- The Hasse endpoint bounds the window. -/
  orderTop_spec : ∀ n, (p n : ℝ) + 1 + 2 * Real.sqrt (p n) ≤ (orderTop n : ℝ)
  /-- There is at least one curve. -/
  curveTotal_pos : ∀ n, 0 < curveTotal orderCount orderTop n
  /-- The Hasse window contains at most `4p` curves. -/
  curve_total_le : ∀ n, curveTotal orderCount orderTop n ≤ 4 * (p n : ℝ)
  /-- **Hasse** (LP §7). -/
  hasse : HasseBound p orderCount
  /-- A smooth order is actually realised by a curve. -/
  smooth_realized : ∀ n j, smooth n j = true → orderCount n j ≠ 0
  /-- A smooth order lies below the stage-one power bound. -/
  smooth_bound : ∀ n j, smooth n j = true → (j : ℝ) ≤ w n
  /-- `ψ₀` counts the smooth orders of the window. -/
  psi_card : ∀ n, psi n ≤ smoothCount smooth orderTop n
  /-- **Deuring/Lenstra count** (LP §7): each smooth order is realised by at
  least `κ√p` curves. -/
  deuring_count : ∀ n j, smooth n j = true →
    κ * Real.sqrt (p n) ≤ (orderCount n j : ℝ)
  /-- **Stage-one success given a smooth order** (LP §7). -/
  stage_one : StageOneSuccess (smoothFraction smooth orderCount orderTop) y success
  /-- The success probability is at most one. -/
  success_le_one : ∀ n, success n ≤ 1
  /-- **Curves over `Z/nZ`, gcd exits** (LP §7, Lemma 7.2). -/
  gcd_exit : GCDExitBound p gcdFail (fun n => 1 - success n)
  /-- Independence of the curve draws: the joint failure is the product of the
  per-curve failures. -/
  independence : ∀ n, jointFail n = (1 - success n) ^ curves n
  /-- **Curve-count choice** (the paper's §Transfer parameter selection): the
  LP exponent beats `(2 + η)H/(κ/4)`. -/
  curve_budget : CurveBudget p y psi curves κ η
  /-- **L27.2 multiplier**: `log₂ (cofactor)` is subexponential on the scale. -/
  logFactor_subexp : LogFactorSubexp cofactor

namespace L27_1Inputs

variable (I : L27_1Inputs)

/-! ## The numeric objects -/

/-- The smooth curve count. -/
def SC (n : ℕ) : ℝ := smoothCurves I.smooth I.orderCount I.orderTop n

/-- The total curve count. -/
def CT (n : ℕ) : ℝ := curveTotal I.orderCount I.orderTop n

/-- The smooth fraction. -/
def SF (n : ℕ) : ℝ := I.SC n / I.CT n

/-- The LP per-curve success exponent constant `κ/4`. -/
def cRate : ℝ := I.κ / 4

/-- LP's smooth density `ψ₀/(√p log y)`. -/
def D (n : ℕ) : ℝ := density I.p I.y I.psi n

/-- The full Thm 7.1 exponent at the paper's curve count:
`#curves · ψ₀/(√p log y)`. -/
def rate (n : ℕ) : ℝ := (I.curves n : ℝ) * I.D n

/-- The per-curve failure probability. -/
def curveFail (n : ℕ) : ℝ := 1 - I.success n

/-- The joint failure of the independent curve draws. -/
def splitFail (n : ℕ) : ℝ := I.jointFail n

/-- LP's constant `c₆ = exp (-κ/4) = exp (-cRate)`, which lies in `(0, 1)`. -/
def c6 : ℝ := exp (-I.cRate)

/-- The L27.1/L27.2 deficit: `log₂ (cofactor)` times the per-node ECM failure.
The small-factor prepass `δ_small` is the separate P1 leaf and is not included. -/
def loss (n : ℕ) : ℝ := ((I.cofactor n).log2 : ℝ) * I.splitFail n

/-! ## Positivity bookkeeping -/

theorem p_pos_real (n : ℕ) : (0 : ℝ) < (I.p n : ℝ) := by
  exact_mod_cast I.p_pos n

theorem sqrt_p_pos (n : ℕ) : 0 < Real.sqrt (I.p n) :=
  Real.sqrt_pos.mpr (I.p_pos_real n)

theorem sqrt_p_ne (n : ℕ) : Real.sqrt (I.p n) ≠ 0 := (I.sqrt_p_pos n).ne'

theorem log_y_pos (n : ℕ) : 0 < Real.log (I.y n) := Real.log_pos (I.y_gt_one n)

theorem cRate_pos : 0 < I.cRate := by
  unfold cRate
  linarith [I.κ_pos]

theorem D_nonneg (n : ℕ) : 0 ≤ I.D n := by
  unfold D density
  exact div_nonneg (I.psi_nonneg n)
    (mul_pos (I.sqrt_p_pos n) (I.log_y_pos n)).le

/-! ## Hasse: the curve-order support lies in the window -/

/-- Hasse plus the integer endpoint: no curve has an order above `orderTop`. -/
theorem orderCount_eq_zero_of_orderTop_lt {n j : ℕ} (hj : I.orderTop n < j) :
    I.orderCount n j = 0 := by
  by_contra hne
  have hh := I.hasse n j hne
  have hupper : (j : ℝ) - ((I.p n : ℝ) + 1) ≤ 2 * Real.sqrt (I.p n) :=
    (abs_le.mp hh).2
  have htop := I.orderTop_spec n
  have hjr : (j : ℝ) ≤ (I.orderTop n : ℝ) := by linarith
  have hlt : (I.orderTop n : ℝ) < (j : ℝ) := by exact_mod_cast hj
  linarith

/-- Every stage-one smooth order is inside the summed window. -/
theorem smooth_order_le_orderTop {n j : ℕ} (hs : I.smooth n j = true) :
    j ≤ I.orderTop n := by
  by_contra h
  push Not at h
  exact I.smooth_realized n j hs (I.orderCount_eq_zero_of_orderTop_lt h)

/-! ## Deuring/Lenstra counts imply the smooth-count lower bound -/

/-- **Deuring/Lenstra count.**  The smooth orders carry at least `κ√p ψ₀`
curves. -/
theorem deuring_smooth_count (n : ℕ) :
    I.κ * Real.sqrt (I.p n) * I.psi n ≤ I.SC n := by
  have hpoint : ∀ j ∈ Finset.range (I.orderTop n + 1),
      (if I.smooth n j then (I.κ * Real.sqrt (I.p n) : ℝ) else 0) ≤
        (if I.smooth n j then (I.orderCount n j : ℝ) else 0) := by
    intro j hj
    by_cases h : I.smooth n j = true
    · simp only [h, if_true]
      exact I.deuring_count n j h
    · simp [h]
  have hsum : (∑ j ∈ Finset.range (I.orderTop n + 1),
        (if I.smooth n j then (I.κ * Real.sqrt (I.p n) : ℝ) else 0)) ≤ I.SC n := by
    simpa [SC, smoothCurves] using Finset.sum_le_sum hpoint
  have hfactor :
      (∑ j ∈ Finset.range (I.orderTop n + 1),
        (if I.smooth n j then (I.κ * Real.sqrt (I.p n) : ℝ) else 0)) =
      (I.κ * Real.sqrt (I.p n)) * smoothCount I.smooth I.orderTop n := by
    rw [smoothCount, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : I.smooth n j = true <;> simp [h]
  have hpsi := I.psi_card n
  have hk : 0 ≤ I.κ * Real.sqrt (I.p n) :=
    mul_nonneg I.κ_pos.le (Real.sqrt_nonneg _)
  calc
    I.κ * Real.sqrt (I.p n) * I.psi n
        = (I.κ * Real.sqrt (I.p n)) * I.psi n := by ring
    _ ≤ (I.κ * Real.sqrt (I.p n)) * smoothCount I.smooth I.orderTop n :=
        mul_le_mul_of_nonneg_left hpsi hk
    _ = (∑ j ∈ Finset.range (I.orderTop n + 1),
          (if I.smooth n j then (I.κ * Real.sqrt (I.p n) : ℝ) else 0)) := hfactor.symm
    _ ≤ I.SC n := hsum

/-- `deuring_smooth_count` in the bundled paper shape. -/
theorem deuringSmoothCount : DeuringSmoothCount I.p I.psi I.SC I.κ :=
  I.deuring_smooth_count

/-- The smooth fraction is at least `κψ₀/(4√p)`. -/
theorem smoothFraction_lower (n : ℕ) :
    I.κ * I.psi n / (4 * Real.sqrt (I.p n)) ≤ I.SF n := by
  have hnum : 0 ≤ I.κ * Real.sqrt (I.p n) * I.psi n :=
    mul_nonneg (mul_nonneg I.κ_pos.le (Real.sqrt_nonneg _)) (I.psi_nonneg n)
  have hden : 0 < I.CT n := I.curveTotal_pos n
  have hle : I.CT n ≤ 4 * (I.p n : ℝ) := I.curve_total_le n
  have hp : (0 : ℝ) < (I.p n : ℝ) := I.p_pos_real n
  have h1 : I.κ * Real.sqrt (I.p n) * I.psi n / (4 * (I.p n : ℝ)) ≤
      I.κ * Real.sqrt (I.p n) * I.psi n / I.CT n :=
    div_le_div_of_nonneg_left hnum hden hle
  have h2 : I.κ * Real.sqrt (I.p n) * I.psi n / (4 * (I.p n : ℝ)) =
      I.κ * I.psi n / (4 * Real.sqrt (I.p n)) := by
    have hsq : Real.sqrt (I.p n) * Real.sqrt (I.p n) = (I.p n : ℝ) :=
      Real.mul_self_sqrt hp.le
    calc
      I.κ * Real.sqrt (I.p n) * I.psi n / (4 * (I.p n : ℝ))
          = I.κ * Real.sqrt (I.p n) * I.psi n /
              (4 * (Real.sqrt (I.p n) * Real.sqrt (I.p n))) := by rw [hsq]
      _ = I.κ * I.psi n / (4 * Real.sqrt (I.p n)) := by
        have hs : Real.sqrt (I.p n) ≠ 0 := I.sqrt_p_ne n
        field_simp [hs]
  calc
    I.κ * I.psi n / (4 * Real.sqrt (I.p n))
        = I.κ * Real.sqrt (I.p n) * I.psi n / (4 * (I.p n : ℝ)) := h2.symm
    _ ≤ I.κ * Real.sqrt (I.p n) * I.psi n / I.CT n := h1
    _ ≤ I.SC n / I.CT n := div_le_div_of_nonneg_right (I.deuring_smooth_count n) hden.le
    _ = I.SF n := rfl

/-! ## The per-curve failure estimate -/

/-- The per-curve success probability is at least the LP density times `κ/4`. -/
theorem cRate_mul_density_le_success (n : ℕ) : I.cRate * I.D n ≤ I.success n := by
  have hlog : 0 < Real.log (I.y n) := I.log_y_pos n
  have hdiv : I.κ * I.psi n / (4 * Real.sqrt (I.p n)) / Real.log (I.y n) ≤
      I.SF n / Real.log (I.y n) :=
    div_le_div_of_nonneg_right (I.smoothFraction_lower n) hlog.le
  have hEq : I.κ * I.psi n / (4 * Real.sqrt (I.p n)) / Real.log (I.y n) =
      I.cRate * I.D n := by
    unfold cRate D density
    have hs : Real.sqrt (I.p n) ≠ 0 := I.sqrt_p_ne n
    have hl : Real.log (I.y n) ≠ 0 := hlog.ne'
    field_simp [hs, hl]
  calc
    I.cRate * I.D n
        = I.κ * I.psi n / (4 * Real.sqrt (I.p n)) / Real.log (I.y n) := hEq.symm
    _ ≤ I.SF n / Real.log (I.y n) := hdiv
    _ ≤ I.success n := by
        simpa [SF, SC, CT, smoothFraction] using I.stage_one n

theorem success_nonneg (n : ℕ) : 0 ≤ I.success n :=
  (mul_nonneg I.cRate_pos.le (I.D_nonneg n)).trans (I.cRate_mul_density_le_success n)

theorem curveFail_nonneg (n : ℕ) : 0 ≤ I.curveFail n := by
  unfold curveFail
  linarith [I.success_le_one n]

theorem curveFail_le_one (n : ℕ) : I.curveFail n ≤ 1 := by
  unfold curveFail
  linarith [I.success_nonneg n]

/-- One curve fails with probability at most `exp (-(κ/4) ψ₀/(√p log y))`. -/
theorem curveFail_le_exp (n : ℕ) :
    I.curveFail n ≤ exp (-(I.cRate * I.D n)) := by
  have h1 : I.curveFail n ≤ 1 - I.cRate * I.D n := by
    unfold curveFail
    linarith [I.cRate_mul_density_le_success n]
  exact h1.trans (Real.one_sub_le_exp_neg (I.cRate * I.D n))

theorem splitFail_nonneg (n : ℕ) : 0 ≤ I.splitFail n := by
  unfold splitFail
  rw [I.independence n]
  exact pow_nonneg (I.curveFail_nonneg n) _

/-- **LP Theorem 7.1.**  The joint failure of `#curves` independent draws is at
most `exp (-(κ/4) · #curves · ψ₀/(√p log y))`. -/
theorem splitFail_le_exp (n : ℕ) :
    I.splitFail n ≤ exp (-(I.cRate * I.rate n)) := by
  have hpow := pow_le_pow_left₀ (I.curveFail_nonneg n) (I.curveFail_le_exp n) (I.curves n)
  have hexp : (exp (-(I.cRate * I.D n))) ^ I.curves n =
      exp (-(I.cRate * I.rate n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    unfold rate
    ring
  unfold splitFail
  rw [I.independence n]
  exact hpow.trans_eq hexp

/-! ## The paper's constant `c₆` -/

theorem c6_pos : 0 < I.c6 := exp_pos _

theorem c6_lt_one : I.c6 < 1 := by
  unfold c6
  have h : Real.exp (-I.cRate) < Real.exp 0 :=
    Real.exp_lt_exp.mpr (by linarith [I.cRate_pos])
  simpa using h

/-- `c₆ ^ x = exp (-(κ/4) x)`. -/
theorem c6_rpow_rate (n : ℕ) :
    I.c6 ^ I.rate n = exp (-(I.cRate * I.rate n)) := by
  unfold c6
  rw [Real.rpow_def_of_pos (exp_pos _), Real.log_exp]
  congr 1
  ring

/-- The paper's exact shape: failure at most `c₆ ^ (#curves · ψ₀/(√p log y))`. -/
theorem splitFail_le_c6_rpow (n : ℕ) :
    I.splitFail n ≤ I.c6 ^ I.rate n := by
  rw [I.c6_rpow_rate n]
  exact I.splitFail_le_exp n

/-! ## The `RatedLeaf` rate and the ledger -/

theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n := by
  unfold loss
  exact mul_nonneg (Nat.cast_nonneg _) (I.splitFail_nonneg n)

/-- **The manuscript's own rate.**  The recursive-splitting deficit
`log₂(cofactor) · δ_split` is at most `exp (-(κ/8) · #curves · ψ₀/(√p log y))`.
The factor `κ/8 = cRate/2` absorbs the subexponential `log₂` multiplier. -/
theorem paper : ∀ᶠ n : ℕ in atTop,
    I.loss n ≤ exp (-((I.cRate / 2) * I.rate n)) := by
  filter_upwards [I.curve_budget, I.logFactor_subexp (I.η / 2) (by linarith [I.η_pos]),
    scale_grows.eventually_ge_atTop 0] with n hbudget hlog hscale
  have hbudget' : (2 + I.η) * scale n ≤ I.cRate * I.rate n := by
    simpa [cRate, rate, D, density] using hbudget
  have hhalf : (I.η / 2) * scale n ≤ (I.cRate / 2) * I.rate n := by
    nlinarith only [hbudget', hscale, I.η_pos]
  calc
    I.loss n = ((I.cofactor n).log2 : ℝ) * I.splitFail n := rfl
    _ ≤ exp ((I.η / 2) * scale n) * exp (-(I.cRate * I.rate n)) :=
        mul_le_mul hlog (I.splitFail_le_exp n) (I.splitFail_nonneg n) (exp_pos _).le
    _ = exp ((I.η / 2) * scale n - I.cRate * I.rate n) := by
        rw [← exp_add]
        congr 1
    _ ≤ exp (-((I.cRate / 2) * I.rate n)) := by
        apply exp_le_exp.mpr
        nlinarith only [hhalf]

/-- **The explicit extra estimate (`ledger`).**  With the paper's curve-count
choice, the L27.1/L27.2 deficit is eventually at most `exp (-2H)`.  The headroom
`η > 0` absorbs the `log₂(cofactor)` multiplier without setting it to zero. -/
theorem ledger : ∀ᶠ n : ℕ in atTop,
    I.loss n ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [I.curve_budget, I.logFactor_subexp (I.η / 2) (by linarith [I.η_pos]),
    scale_grows.eventually_ge_atTop 0] with n hbudget hlog hscale
  have hbudget' : (2 + I.η) * scale n ≤ I.cRate * I.rate n := by
    simpa [cRate, rate, D, density] using hbudget
  have hsplit : I.splitFail n ≤ exp (-(2 + I.η) * scale n) := by
    refine (I.splitFail_le_exp n).trans (exp_le_exp.mpr ?_)
    nlinarith only [hbudget']
  calc
    I.loss n = ((I.cofactor n).log2 : ℝ) * I.splitFail n := rfl
    _ ≤ exp ((I.η / 2) * scale n) * exp (-(2 + I.η) * scale n) :=
        mul_le_mul hlog hsplit (I.splitFail_nonneg n) (exp_pos _).le
    _ = exp (((I.η / 2) - (2 + I.η)) * scale n) := by
        rw [← exp_add]
        congr 1
        ring
    _ ≤ exp (-(2 : ℝ) * scale n) := by
        apply exp_le_exp.mpr
        nlinarith only [hscale, I.η_pos]

/-! ## The `RatedLeaf` and its `C5` slot -/

/-- **L27.1 as a `RatedLeaf`.**  The paper rate is
`#curves · ψ₀/(√p log y)`; the explicit `ledger` estimate is the paper's
curve-count choice. -/
def toRatedLeaf : RatedLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  rate := I.rate
  c := I.cRate / 2
  c_pos := by
    unfold cRate
    linarith [I.κ_pos]
  paper := I.paper
  ledger := I.ledger

/-- The `C5LossSlots.ecmRecognition` slot, once identified with this file's
`loss`, satisfies the C5 `exp (-2H)` requirement. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots C5Leaf.ecmRecognition = I.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots C5Leaf.ecmRecognition n ≤ exp (-(2 : ℝ) * scale n) := by
  rw [h]
  exact I.ledger

/-- The reduction through `RatedLeaf.slot`. -/
theorem toRatedLeaf_slot :
    ∀ᶠ n : ℕ in atTop,
      I.toRatedLeaf.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  I.toRatedLeaf.slot

end L27_1Inputs

/-! ## Axiom audit -/

#print axioms L27_1Inputs.deuring_smooth_count
#print axioms L27_1Inputs.smoothFraction_lower
#print axioms L27_1Inputs.cRate_mul_density_le_success
#print axioms L27_1Inputs.curveFail_le_exp
#print axioms L27_1Inputs.splitFail_le_exp
#print axioms L27_1Inputs.c6_lt_one
#print axioms L27_1Inputs.splitFail_le_c6_rpow
#print axioms L27_1Inputs.loss_nonneg
#print axioms L27_1Inputs.paper
#print axioms L27_1Inputs.ledger
#print axioms L27_1Inputs.toRatedLeaf
#print axioms L27_1Inputs.slot_le
#print axioms L27_1Inputs.toRatedLeaf_slot

end

end Cogentic.RandomizedL27_1
