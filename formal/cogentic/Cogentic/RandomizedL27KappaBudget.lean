import Cogentic.RandomizedWave18Audit

/-!
# L27: the `κ` budget between `CurveBudget`, `θ ≤ 4`, and the Hurwitz assembly

`Cogentic.RandomizedWave18Audit.theta_le_four_of_curveBudget` proves that the
paper's curve budget

`(2 + η) H ≤ (κ/4) · #curves · ψ/(√p log y)`

forces `θ ≤ 4` (through the central-trace window and the existence of a smooth
order).  The present file isolates the scalar consequences of that fact for the
Hurwitz assembly.

## The direction of the scalar inference

The assembly's Siegel field is

`I.κ ≤ (classNumberFormulaConstant * l) * √θ`.

Once `θ ≤ 4` is known, `√θ ≤ 2`, so this **implies** the constant-only bound

`I.κ ≤ 2 * (classNumberFormulaConstant * l)`;

this is `kappa_le_two_const_of_curveBudget` and
`L27HurwitzAssemblyInputs.kappa_le_weakened`, the exact form recorded by the
wave-18 audit (`l27KappaLe_weakened`).

The *converse* inference — deriving `κ ≤ c√θ` from `κ ≤ 2c` and `θ ≤ 4` — is
false, because `θ ≤ 4` gives the opposite inequality `c√θ ≤ 2c` at the level of
the constants.  `weakened_and_theta_le_four_not_imply_kappa_le_sqrt` is the
explicit scalar counterexample (`c = 1`, `κ = 2`, `θ = 1`).

## The exact missing scalar

For `c > 0` and `κ, θ ≥ 0` the assembly field is equivalent to the squared
scalar inequality

`(κ / c)^2 ≤ θ`,

proved as `kappa_le_iff_sq_div_le` and `kappa_le_iff_sq_le`.  This squared
inequality is the *smallest explicit scalar condition* that upgrades the
weakened bound to the assembly bound: it is equivalent to the assembly bound, so
no condition stated only in terms of the upper end `θ ≤ 4` and the weakened
bound can do it.  The structure `L27KappaBudgetInputs` carries exactly this
scalar condition in place of `kappa_le`, and `toAssembly`,
`toHurwitzInputs`, `toStageOneFinishInputs` and `reduction` show that it
reconstructs the whole L27 Hurwitz/stage-one pipeline.

## Does `CurveBudget` itself force the weakened bound?

No.  `CurveBudget` is monotone *increasing* in `κ`: raising `κ` only makes its
right-hand side larger (`curveBudget_mono_kappa`).  Moreover, for **every** real
`B` there are parameters with `B < κ` satisfying `CurveBudget`
(`exists_curveBudget_kappa_gt`), so no statement of the form `CurveBudget ⇒
κ ≤ 2c` can hold (`curveBudget_not_forces_kappa_le_two_const`).  The weakened
bound is a consequence of the *Siegel* side of the assembly (the `kappa_le`
field), not of the curve budget alone.

All constants are kept positive: `classNumberFormulaConstant = 1/(2π) > 0`,
`l > 0`, `I.κ > 0`.  No `sorry`, `admit`, `axiom`, `native_decide`, and no bound
is replaced by zero.
-/

namespace Cogentic.RandomizedL27KappaBudget

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27ClassNumber
open Cogentic.RandomizedL27Fiber
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27HurwitzAssembly
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27Scale
open Cogentic.RandomizedL27Siegel
open Cogentic.RandomizedL27StageOne
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Stratification
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL27Weighted
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements

noncomputable section

/-! ## 1. `√θ ≤ 2` and the valid weakening -/

/-- `√θ ≤ 2` as soon as `θ ≤ 4` (no lower bound on `θ` is needed: for `θ < 0`
the square root is `0`). -/
theorem sqrt_le_two_of_le_four {θ : ℝ} (hθ : θ ≤ 4) : Real.sqrt θ ≤ 2 := by
  rw [Real.sqrt_le_iff]
  exact ⟨by norm_num, by nlinarith⟩

/-- **The valid scalar direction.**  An upper bound `κ ≤ c√θ` together with
`θ ≤ 4` gives the constant-only bound `κ ≤ 2c`.  This is the direction used by
the wave-18 audit; the converse is refuted below. -/
theorem kappa_le_two_mul_of_sqrt {κ c θ : ℝ} (hc : 0 ≤ c)
    (h : κ ≤ c * Real.sqrt θ) (hθ : θ ≤ 4) : κ ≤ 2 * c := by
  have hsqrt : Real.sqrt θ ≤ 2 := sqrt_le_two_of_le_four hθ
  have hmul : c * Real.sqrt θ ≤ c * 2 :=
    mul_le_mul_of_nonneg_left hsqrt hc
  linarith

/-- **The audit's weakening, with the curve budget providing `θ ≤ 4`.**  For any
`L27_1Inputs` (whose `curve_budget` field is the paper's curve-count choice), the
central-trace window and the assembly Siegel bound imply
`κ ≤ 2c`.  The curve budget is used only through
`theta_le_four_of_curveBudget`. -/
theorem kappa_le_two_const_of_curveBudget (I : L27_1Inputs) {c θ : ℝ}
    (hc : 0 ≤ c) (hcentral : CentralTraceWindow I.p I.smooth θ)
    (hκ : I.κ ≤ c * Real.sqrt θ) : I.κ ≤ 2 * c :=
  kappa_le_two_mul_of_sqrt hc hκ
    (Cogentic.RandomizedWave18Audit.theta_le_four_of_curveBudget I hcentral)

/-- **The weakened `κ` bound for the Hurwitz assembly.**  The assembly's
`kappa_le` field and its central-trace field, together with the curve budget
carried by `I`, give `κ ≤ 2 · (classNumberFormulaConstant · l)`.  No additional
hypothesis is needed. -/
theorem L27HurwitzAssemblyInputs.kappa_le_weakened {I : L27_1Inputs}
    (D : L27HurwitzAssemblyInputs I) :
    I.κ ≤ 2 * (classNumberFormulaConstant * D.l) :=
  kappa_le_two_const_of_curveBudget I
    (mul_pos classNumberFormulaConstant_pos D.l_pos).le
    D.central_trace D.kappa_le

/-! ## 2. The converse is false -/

/-- **The weakened bound plus `θ ≤ 4` does not imply `κ ≤ c√θ`.**  At `c = 1`,
`κ = 2`, `θ = 1` we have `κ = 2c` and `θ ≤ 4`, but `c√θ = 1 < 2`.  This is the
explicit scalar obstruction behind the reversed reading of the paper's bound:
`θ ≤ 4` gives `√θ ≤ 2`, hence `c√θ ≤ 2c`, which is the wrong direction. -/
theorem weakened_and_theta_le_four_not_imply_kappa_le_sqrt :
    ¬ ∀ (κ c θ : ℝ), 0 < c → 0 < θ → θ ≤ 4 →
      κ ≤ 2 * c → κ ≤ c * Real.sqrt θ := by
  intro h
  have h2 : (2 : ℝ) ≤ 1 * Real.sqrt 1 :=
    h 2 1 1 one_pos one_pos (by norm_num) (by norm_num)
  rw [Real.sqrt_one, mul_one] at h2
  norm_num at h2

/-! ## 3. The exact scalar bridge -/

/-- **The assembly bound is equivalent to a squared scalar inequality.**  For
`c > 0` and `κ, θ ≥ 0`,
`κ ≤ c√θ ↔ (κ/c)^2 ≤ θ`.  This is the smallest explicit scalar condition that
replaces `kappa_le`: it is equivalent to it, so no condition using only the
*upper* end `θ ≤ 4` and the weakened bound `κ ≤ 2c` can replace it (see
`weakened_and_theta_le_four_not_imply_kappa_le_sqrt`). -/
theorem kappa_le_iff_sq_div_le {κ c θ : ℝ} (hc : 0 < c) (hκ : 0 ≤ κ)
    (hθ : 0 ≤ θ) : κ ≤ c * Real.sqrt θ ↔ (κ / c) ^ 2 ≤ θ := by
  constructor
  · intro h
    have h1 : κ / c ≤ Real.sqrt θ := by
      rw [div_le_iff₀ hc]
      linarith
    have h2 : 0 ≤ κ / c := div_nonneg hκ hc.le
    have hmul : (κ / c) ^ 2 ≤ (Real.sqrt θ) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self h2 h1
    rwa [Real.sq_sqrt hθ] at hmul
  · intro h
    have h2 : 0 ≤ κ / c := div_nonneg hκ hc.le
    have h1 : κ / c ≤ Real.sqrt θ := by
      rw [Real.le_sqrt h2 hθ]
      exact h
    have hmul : κ ≤ Real.sqrt θ * c := (div_le_iff₀ hc).mp h1
    linarith

/-- The forward (squared) form of `kappa_le_iff_sq_div_le`. -/
theorem kappa_le_of_sq_div_le {κ c θ : ℝ} (hc : 0 < c) (hκ : 0 ≤ κ)
    (h : (κ / c) ^ 2 ≤ θ) : κ ≤ c * Real.sqrt θ :=
  (kappa_le_iff_sq_div_le hc hκ ((sq_nonneg (κ / c)).trans h)).mpr h

/-- **The bridge with the Siegel constant `c = classNumberFormulaConstant * l`.**
The assembly's `κ` field is equivalent to `(κ / (classNumberFormulaConstant *
l))^2 ≤ θ`. -/
theorem kappa_le_iff_sq_le {I : L27_1Inputs} {l θ : ℝ} (hl : 0 < l)
    (hθ : 0 ≤ θ) :
    I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ ↔
      (I.κ / (classNumberFormulaConstant * l)) ^ 2 ≤ θ :=
  kappa_le_iff_sq_div_le (mul_pos classNumberFormulaConstant_pos hl)
    I.κ_pos.le hθ

/-- **The minimal replacement for the assembly scalar field.**  Given the
central-trace window (so the curve budget supplies `θ ≤ 4`) and the weakened
bound `κ ≤ 2c`, the exact additional scalar hypothesis needed to recover the
assembly bound `κ ≤ c√θ` is `(κ/c)^2 ≤ θ`.  The weakened bound and the upper end
`θ ≤ 4` are recorded explicitly to display the intended reduction; the squared
inequality is the only scalar content. -/
theorem kappa_le_of_curveBudget_and_weakened (I : L27_1Inputs) {c θ : ℝ}
    (hcentral : CentralTraceWindow I.p I.smooth θ)
    (hweak : I.κ ≤ 2 * c)
    (hsq : (I.κ / c) ^ 2 ≤ θ) :
    I.κ ≤ c * Real.sqrt θ := by
  have hc : 0 < c := by
    have hpos := I.κ_pos
    linarith
  -- `CurveBudget` gives `θ ≤ 4`, so `√θ ≤ 2` and `hweak` is indeed the natural
  -- weakening of the conclusion; the missing scalar content is `hsq`.
  have hθ4 : θ ≤ 4 :=
    Cogentic.RandomizedWave18Audit.theta_le_four_of_curveBudget I hcentral
  have _hsqrt : Real.sqrt θ ≤ 2 := sqrt_le_two_of_le_four hθ4
  exact kappa_le_of_sq_div_le hc I.κ_pos.le hsq

/-- The same bridge in the exact shape of `L27HurwitzAssemblyInputs.kappa_le`. -/
theorem kappa_le_of_curveBudget_and_weakened_const (I : L27_1Inputs) {l θ : ℝ}
    (_hl : 0 < l) (hcentral : CentralTraceWindow I.p I.smooth θ)
    (hweak : I.κ ≤ 2 * (classNumberFormulaConstant * l))
    (hsq : (I.κ / (classNumberFormulaConstant * l)) ^ 2 ≤ θ) :
    I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ :=
  kappa_le_of_curveBudget_and_weakened I hcentral hweak hsq

/-! ## 4. The curve budget does not bound `κ` from above -/

/-- **`CurveBudget` is monotone increasing in `κ`.**  Raising `κ` only increases
the right-hand side, while the left-hand side is unchanged. -/
theorem curveBudget_mono_kappa (I : L27_1Inputs) {κ' : ℝ} (hκ : I.κ ≤ κ')
    (hb : CurveBudget I.p I.y I.psi I.curves I.κ I.η) :
    CurveBudget I.p I.y I.psi I.curves κ' I.η := by
  filter_upwards [hb] with n hn
  have hden : 0 < Real.sqrt (I.p n) * Real.log (I.y n) :=
    mul_pos (I.sqrt_p_pos n) (I.log_y_pos n)
  have hX : 0 ≤ (I.curves n : ℝ) *
      (I.psi n / (Real.sqrt (I.p n) * Real.log (I.y n))) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (I.psi_nonneg n) hden.le)
  have hfac : I.κ / 4 ≤ κ' / 4 := by linarith
  calc
    (2 + I.η) * scale n
        ≤ (I.κ / 4) * ((I.curves n : ℝ) *
            (I.psi n / (Real.sqrt (I.p n) * Real.log (I.y n)))) := hn
    _ ≤ (κ' / 4) * ((I.curves n : ℝ) *
            (I.psi n / (Real.sqrt (I.p n) * Real.log (I.y n)))) :=
      mul_le_mul_of_nonneg_right hfac hX

/-- **`CurveBudget` admits arbitrarily large `κ`.**  With `p = 4`, `y = 2`,
`ψ = 1`, `η = 1` and the number of curves chosen as the ceiling of
`3 · H · 4 · (√4 log 2)/κ`, the budget holds for every positive `κ`.  Hence the
budget alone gives no upper bound on the Deuring constant. -/
theorem exists_curveBudget_kappa_gt (B : ℝ) :
    ∃ (κ η : ℝ) (p : ℕ → ℕ) (y psi : ℕ → ℝ) (curves : ℕ → ℕ),
      B < κ ∧ CurveBudget p y psi curves κ η := by
  let κ : ℝ := |B| + 1
  let curves : ℕ → ℕ := fun n =>
    ⌈(2 + 1) * scale n * 4 * (Real.sqrt 4 * Real.log 2) / κ⌉₊
  refine ⟨κ, 1, fun _ => 4, fun _ => 2, fun _ => 1, curves, ?_, ?_⟩
  · show B < |B| + 1
    linarith [le_abs_self B]
  · filter_upwards [scale_grows.eventually_ge_atTop 0] with n hs
    have hκ : 0 < κ := by
      change 0 < |B| + 1
      positivity
    have hd : 0 < Real.sqrt (4 : ℝ) * Real.log 2 := by
      have h4 : (0 : ℝ) < Real.sqrt 4 := Real.sqrt_pos.mpr (by norm_num)
      have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    have hT : 0 ≤ (2 + 1) * scale n * 4 * (Real.sqrt 4 * Real.log 2) / κ := by
      have h3 : (0 : ℝ) ≤ 2 + 1 := by norm_num
      exact div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg h3 hs) (by norm_num)) hd.le) hκ.le
    have hceil : (2 + 1) * scale n * 4 * (Real.sqrt 4 * Real.log 2) / κ
        ≤ ((curves n : ℕ) : ℝ) := Nat.le_ceil _
    have hright : (κ / 4) *
        ((2 + 1) * scale n * 4 * (Real.sqrt 4 * Real.log 2) / κ
          * (1 / (Real.sqrt 4 * Real.log 2)))
        = (2 + 1) * scale n := by
      field_simp [hκ.ne', hd.ne']
    have hmono : (κ / 4) *
        ((2 + 1) * scale n * 4 * (Real.sqrt 4 * Real.log 2) / κ
          * (1 / (Real.sqrt 4 * Real.log 2)))
        ≤ (κ / 4) * (((curves n : ℕ) : ℝ) *
          (1 / (Real.sqrt 4 * Real.log 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hceil (by positivity)
    calc
      (2 + 1) * scale n
          = (κ / 4) *
              ((2 + 1) * scale n * 4 * (Real.sqrt 4 * Real.log 2) / κ
                * (1 / (Real.sqrt 4 * Real.log 2))) := hright.symm
      _ ≤ (κ / 4) * (((curves n : ℕ) : ℝ) *
            (1 / (Real.sqrt 4 * Real.log 2))) := hmono

/-- **`CurveBudget` alone does not force the weakened `κ` bound.**  For every
constant `c` there are curve-budget data with `κ > 2c`; hence the implication
`CurveBudget ⇒ κ ≤ 2c` is false.  The weakened bound comes from the Siegel side
of the assembly (`L27HurwitzAssemblyInputs.kappa_le_weakened`), not from the
curve budget. -/
theorem curveBudget_not_forces_kappa_le_two_const (c : ℝ) :
    ¬ ∀ (κ η : ℝ) (p : ℕ → ℕ) (y psi : ℕ → ℝ) (curves : ℕ → ℕ),
        CurveBudget p y psi curves κ η → κ ≤ 2 * c := by
  intro h
  obtain ⟨κ, η, p, y, psi, curves, hlt, hb⟩ := exists_curveBudget_kappa_gt (2 * c)
  exact (not_le.mpr hlt) (h κ η p y psi curves hb)

/-! ## 5. The reduced assembly bundle -/

/-- **The Hurwitz assembly with the scalar field replaced by the exact squared
bridge.**  Every field of `L27HurwitzAssemblyInputs` except `kappa_le` is
retained; the Siegel scale field is carried as the equivalent scalar inequality
`(κ / (classNumberFormulaConstant * l))^2 ≤ θ`
(`kappa_le_iff_sq_le`).  Positive constants are kept as fields (`l_pos`,
`θ_pos`). -/
structure L27KappaBudgetInputs (I : L27_1Inputs) where
  /-- The Hurwitz class number `H(-D)`. -/
  hurwitz : ℤ → ℝ
  /-- The quadratic `L`-value `L(1, χ_D)`. -/
  L1 : ℤ → ℝ
  /-- The Dirichlet class-number formula and arithmetic positivity data. -/
  classInput : DirichletClassNumberInput hurwitz L1
  /-- The uniform lower bound for `L(1, χ_D)`. -/
  l : ℝ
  /-- The `L`-lower bound is positive. -/
  l_pos : 0 < l
  /-- `l` is a lower bound on Frobenius discriminants. -/
  l_one_lower : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D
  /-- Nondegeneracy fraction `D(p,j) ≥ θp` on the central window. -/
  θ : ℝ
  /-- The nondegeneracy fraction is positive. -/
  θ_pos : 0 < θ
  /-- **The exact scalar bridge**: the squared form of
  `κ ≤ (classNumberFormulaConstant * l) √θ`. -/
  kappa_sq_le : (I.κ / (classNumberFormulaConstant * l)) ^ 2 ≤ θ
  /-- Smooth orders lie in the central trace window `t² ≤ (4 - θ)p`. -/
  central_trace : CentralTraceWindow I.p I.smooth θ
  /-- The target prime is prime. -/
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

namespace L27KappaBudgetInputs

variable {I : L27_1Inputs}

/-- **The assembly bound from the squared bridge.**  This is the reduction of
the `kappa_le` field to the scalar inequality of §3. -/
theorem kappa_le (D : L27KappaBudgetInputs I) :
    I.κ ≤ (classNumberFormulaConstant * D.l) * Real.sqrt D.θ :=
  kappa_le_of_sq_div_le (mul_pos classNumberFormulaConstant_pos D.l_pos)
    I.κ_pos.le D.kappa_sq_le

/-- **The weakened bound derived from the bridge and the curve budget.**  The
bridge gives the assembly bound, and the curve budget (a field of `I`) gives
`θ ≤ 4`; hence `κ ≤ 2 · (classNumberFormulaConstant · l)`. -/
theorem kappa_weakened (D : L27KappaBudgetInputs I) :
    I.κ ≤ 2 * (classNumberFormulaConstant * D.l) :=
  kappa_le_two_const_of_curveBudget I
    (mul_pos classNumberFormulaConstant_pos D.l_pos).le
    D.central_trace D.kappa_le

/-- **The full `L27HurwitzAssemblyInputs`.**  The squared scalar bridge fills
the `kappa_le` slot; every other assembly field is copied. -/
def toAssembly (D : L27KappaBudgetInputs I) : L27HurwitzAssemblyInputs I where
  hurwitz := D.hurwitz
  L1 := D.L1
  classInput := D.classInput
  l := D.l
  l_pos := D.l_pos
  l_one_lower := D.l_one_lower
  θ := D.θ
  θ_pos := D.θ_pos
  kappa_le := D.kappa_le
  central_trace := D.central_trace
  p_prime := D.p_prime
  waterhouse_model := D.waterhouse_model
  orderCount_dominates_raw := D.orderCount_dominates_raw
  fiber := D.fiber
  p_ge_four := D.p_ge_four

/-- The reconstructed assembly has the original Hurwitz class number. -/
theorem toAssembly_hurwitz (D : L27KappaBudgetInputs I) :
    D.toAssembly.hurwitz = D.hurwitz := rfl

/-- The reconstructed assembly has the original `L`-lower bound. -/
theorem toAssembly_l (D : L27KappaBudgetInputs I) :
    D.toAssembly.l = D.l := rfl

/-- The reconstructed assembly has the original `θ`. -/
theorem toAssembly_theta (D : L27KappaBudgetInputs I) :
    D.toAssembly.θ = D.θ := rfl

/-- **The assembled `L27HurwitzInputs`.**  All the Siegel/Deuring/geometric
leaves of the Hurwitz block are derived by
`Cogentic.RandomizedL27HurwitzAssembly`, starting from the reconstructed
assembly. -/
def toHurwitzInputs (D : L27KappaBudgetInputs I) : L27HurwitzInputs I :=
  D.toAssembly.toHurwitzInputs

/-- **The assembled `L27StageOneFinishInputs`.**  The kill law, Hasse, the curve
budget and the `log₂` multiplier are supplied explicitly; the Hurwitz block is
the reconstructed one. -/
def toStageOneFinishInputs (D : L27KappaBudgetInputs I)
    (S : L27KillLawInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : L27StageOneFinishInputs I :=
  D.toAssembly.toStageOneFinishInputs S hhasse hbudget hlog

/-- **The full L27.1 reduction from the reduced assembly data.**  Both bundled
`L27_1Sub` hypotheses and both deficit caps follow. -/
theorem reduction (D : L27KappaBudgetInputs I)
    (S : L27KillLawInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  (D.toStageOneFinishInputs S hhasse hbudget hlog).reduction

/-- The `L27PaperInputs` block from the reduced assembly data and the five
remaining LP §7 inputs. -/
theorem toPaperInputs (D : L27KappaBudgetInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    L27PaperInputs I :=
  D.toAssembly.toPaperInputs hhasse h0 h1 h2 hstage

/-- The `RatedLeaf` from the reduced assembly data. -/
def toRatedLeaf (D : L27KappaBudgetInputs I)
    (S : L27KillLawInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf :=
  (D.toStageOneFinishInputs S hhasse hbudget hlog).toRatedLeaf

end L27KappaBudgetInputs

/-- **Every full assembly is a budget input, with no loss.**  The squared bridge
is obtained from the assembly's `kappa_le` field by `kappa_le_iff_sq_le`.
Together with `L27KappaBudgetInputs.toAssembly` this shows that the squared
scalar condition is *equivalent* to the assembly field, so it is the smallest
explicit scalar replacement for `kappa_le`. -/
def L27HurwitzAssemblyInputs.toKappaBudget {I : L27_1Inputs}
    (D : L27HurwitzAssemblyInputs I) : L27KappaBudgetInputs I where
  hurwitz := D.hurwitz
  L1 := D.L1
  classInput := D.classInput
  l := D.l
  l_pos := D.l_pos
  l_one_lower := D.l_one_lower
  θ := D.θ
  θ_pos := D.θ_pos
  kappa_sq_le := (kappa_le_iff_sq_le D.l_pos D.θ_pos.le).mp D.kappa_le
  central_trace := D.central_trace
  p_prime := D.p_prime
  waterhouse_model := D.waterhouse_model
  orderCount_dominates_raw := D.orderCount_dominates_raw
  fiber := D.fiber
  p_ge_four := D.p_ge_four

/-! ## 6. Summary of the scalar inequalities -/

/-- **The complete scalar reduction, packaged.**  For `c = classNumberFormulaConstant * l`:

* the assembly bound implies the weakened bound (`κ ≤ 2c`);
* the weakened bound and `θ ≤ 4` do **not** imply the assembly bound
  (`weakened_and_theta_le_four_not_imply_kappa_le_sqrt`);
* the exact additional scalar condition is `(κ/c)^2 ≤ θ`, which is equivalent to
  the assembly bound (`kappa_le_iff_sq_div_le`). -/
theorem kappa_budget_summary {I : L27_1Inputs} {l θ : ℝ} (hl : 0 < l)
    (hθ : 0 ≤ θ) :
    (I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ →
        θ ≤ 4 → I.κ ≤ 2 * (classNumberFormulaConstant * l)) ∧
      (I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ ↔
        (I.κ / (classNumberFormulaConstant * l)) ^ 2 ≤ θ) ∧
      (¬ ∀ (κ c θ : ℝ), 0 < c → 0 < θ → θ ≤ 4 →
        κ ≤ 2 * c → κ ≤ c * Real.sqrt θ) := by
  refine ⟨?_, kappa_le_iff_sq_le hl hθ, weakened_and_theta_le_four_not_imply_kappa_le_sqrt⟩
  intro hκ hθ4
  exact kappa_le_two_mul_of_sqrt (mul_pos classNumberFormulaConstant_pos hl).le hκ hθ4

/-! ## Axiom audit -/

#print axioms sqrt_le_two_of_le_four
#print axioms kappa_le_two_mul_of_sqrt
#print axioms kappa_le_two_const_of_curveBudget
#print axioms L27HurwitzAssemblyInputs.kappa_le_weakened
#print axioms weakened_and_theta_le_four_not_imply_kappa_le_sqrt
#print axioms kappa_le_iff_sq_div_le
#print axioms kappa_le_of_sq_div_le
#print axioms kappa_le_iff_sq_le
#print axioms kappa_le_of_curveBudget_and_weakened
#print axioms kappa_le_of_curveBudget_and_weakened_const
#print axioms curveBudget_mono_kappa
#print axioms exists_curveBudget_kappa_gt
#print axioms curveBudget_not_forces_kappa_le_two_const
#print axioms kappa_budget_summary
#print axioms L27KappaBudgetInputs.kappa_le
#print axioms L27KappaBudgetInputs.kappa_weakened
#print axioms L27KappaBudgetInputs.toAssembly
#print axioms L27KappaBudgetInputs.toHurwitzInputs
#print axioms L27KappaBudgetInputs.toStageOneFinishInputs
#print axioms L27KappaBudgetInputs.reduction
#print axioms L27KappaBudgetInputs.toPaperInputs
#print axioms L27KappaBudgetInputs.toRatedLeaf
#print axioms L27HurwitzAssemblyInputs.toKappaBudget

end

end Cogentic.RandomizedL27KappaBudget
