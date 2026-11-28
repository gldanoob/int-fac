import Cogentic.RandomizedL18_4Inhabitant
import Cogentic.RandomizedL19ConcreteAssembly
import Cogentic.RandomizedL20_2SourceWitness
import Cogentic.RandomizedL20_4Sub
import Cogentic.RandomizedL20_4Top
import Cogentic.RandomizedL27_1
import Cogentic.RandomizedL27Hurwitz
import Cogentic.RandomizedL27KillLaw
import Cogentic.RandomizedL27StageOneFinish
import Cogentic.RandomizedL30Sub
import Cogentic.RandomizedPaperEndpointWave28
import Cogentic.RandomizedL34EffectiveInhabitant
import Cogentic.RandomizedL34EffectiveChebotarev
import Cogentic.RandomizedP1Prepass
import Cogentic.RandomizedConcreteEpoch
import Cogentic.RandomizedConcreteC1
import Cogentic.RandomizedConcreteHitMass

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Zero-index audit: the `n = 0` behaviour of every `PaperResidualFor29` record

The *unguarded* form of `L18_4Certificate` was uninhabited because two families
of fields were stated for **all** `n`, while `scale 0 = 0`:

* the `D^{O(1)}` upper bounds gave `W 0 ≤ 1` and `d 0 ≤ 1`;
* the cell-width lower bound gives
  `exp (3 W 0 / 4) ≤ B 0 - A 0 ≤ exp (W 0) - 2 ≤ exp 1 - 2 < 1`.

The same argument works at every index with `scale n ≤ 0`; in particular
`scale 1 = 0` and `scale 2 < 0`.  Hence the exact guard is `3 ≤ n`, not `1 ≤ n`,
and the interface now asserts the upper bounds only there.  This file records
the obstruction for the unguarded form (`unguarded_bounds_inconsistent`) and
proves that `3` is the first admissible index.

After the repair, no record of `PaperResidualFor29` is refutable at `n = 0`:
`L18_4Certificate` is inhabited exactly modulo `L18_4CoreResidual`
(`W_dominates` and `cellSupply`), and every other record receives an explicit
inhabitant below.  For each record the audit either constructs a genuine
inhabitant (no zero loss, no zero count) or states the exact residual interface.
The constructions for L19/L20.2 come from the existing concrete assemblies;
L20.4, L27, L34 and P1 are constructed explicitly below.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss substitution is
used.
-/

namespace Cogentic.RandomizedZeroIndexAudit

open Filter Real
open scoped BigOperators ENNReal Classical

open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19ZeroMode
open Cogentic.RandomizedL19Thin
open Cogentic.RandomizedL18_4ThinFinish
open Cogentic.RandomizedL19ConcreteAssembly
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_2SourceWitness
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Top
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27GcdModel
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34EffectiveChebotarev
open Cogentic.RandomizedL34EffectiveInhabitant
open Cogentic.RandomizedL34ZeroFreeArithmetic
open Cogentic.RandomizedP1Sub
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave28
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedL27Deuring

noncomputable section

/-! ## 1. The ledger scale at the small indices -/

theorem audit_scale_zero : scale 0 = 0 := by
  simp [scale]

theorem audit_scale_one : scale 1 = 0 := by
  simp [scale]

/-- The exact obstruction of `L18_4Certificate` is `scale n ≤ 0`.  It occurs at
`n = 0`, `n = 1` and `n = 2`; the first index with `0 < scale n` is `3`. -/
theorem audit_scale_nonpos_of_le_two {n : ℕ} (hn : n ≤ 2) : scale n ≤ 0 := by
  interval_cases n
  · simpa using le_of_eq audit_scale_zero
  · simpa using le_of_eq audit_scale_one
  · exact Cogentic.RandomizedL19EnergyMassFinite.scale_two_neg.le

theorem audit_scale_pos_of_three_le {n : ℕ} (hn : 3 ≤ n) : 0 < scale n :=
  Cogentic.RandomizedL19EnergyMassFinite.scale_pos_of_three_le hn

/-! ## 2. L18.4: the guard repair and the post-guard residual

The commit `Guard the L18.4 growth fields at the paper regime` changed every
pointwise `D^{O(1)}` bound of `L18_4Ambient`/`L18_4Certificate` to
`∀ n, 3 ≤ n → ...`.  The generic lemmas below record the *pre-repair*
obstruction: they apply only to unguarded hypotheses and are no longer fields of
the current certificate.  The post-guard certificate is not refutable; it is
inhabited exactly modulo `L18_4CoreResidual` (`W_dominates` and `cellSupply`).
-/

/-- **The post-guard L18.4 certificate.**  The concrete core supplies every
guarded `D^{O(1)}` bound; only the two honest analytic residuals of
`L18_4CoreResidual` remain. -/
theorem audit_nonempty_L18_4Certificate_of_residual (r : L18_4CoreResidual) :
    Nonempty L18_4Certificate :=
  Cogentic.RandomizedL18_4.nonempty_L18_4Certificate_of_residual r

/-- **Historical pre-repair obstruction.**  If the two pointwise `D^{O(1)}`
bounds were asserted *unguarded* at an index with `scale n ≤ 0`, they would force
`W n ≤ 1` and `d n ≤ 1`, while the cell-width lower bound and `B ≤ exp W`
force `1 ≤ exp (3W/4) ≤ B - A ≤ exp W - 2 < 1`.  This is the exact obstruction
that the guard `3 ≤ n` removes. -/
theorem unguarded_bounds_inconsistent
    {W d : ℕ → ℝ} {A B : ℕ → ℕ} {cW cd : ℝ}
    (hWnn : ∀ n, 0 ≤ W n) (hdpos : ∀ n, 0 < d n)
    (hcW : 0 ≤ cW) (hcd : 0 ≤ cd)
    (hWub : ∀ n, W n ≤ Real.exp (cW * scale n))
    (hdub : ∀ n, d n ≤ Real.exp (cd * scale n))
    (hA : ∀ n, 2 ≤ A n)
    (hV : ∀ n, (B n : ℝ) ≤ Real.exp (W n))
    (hwidth : ∀ n, Real.exp (W n) / (d n * Real.exp (W n / 4)) ≤
      (B n : ℝ) - (A n : ℝ))
    {n : ℕ} (hs : scale n ≤ 0) : False := by
  have hWle : W n ≤ 1 := by
    have h : W n ≤ Real.exp (cW * scale n) := hWub n
    have hmul : cW * scale n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcW hs
    have hexp : Real.exp (cW * scale n) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hmul
    linarith
  have hdle : d n ≤ 1 := by
    have h : d n ≤ Real.exp (cd * scale n) := hdub n
    have hmul : cd * scale n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcd hs
    have hexp : Real.exp (cd * scale n) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hmul
    linarith
  have hB : (B n : ℝ) ≤ Real.exp (W n) := hV n
  have hAn : (2 : ℝ) ≤ (A n : ℝ) := by exact_mod_cast hA n
  have hw : Real.exp (W n) / (d n * Real.exp (W n / 4)) ≤
      (B n : ℝ) - (A n : ℝ) := hwidth n
  have hden_pos : 0 < d n * Real.exp (W n / 4) :=
    mul_pos (hdpos n) (exp_pos _)
  have hden_le : d n * Real.exp (W n / 4) ≤ Real.exp (W n / 4) := by
    simpa using mul_le_mul_of_nonneg_right hdle (exp_pos (W n / 4)).le
  have hlow : Real.exp (W n) / Real.exp (W n / 4) ≤
      Real.exp (W n) / (d n * Real.exp (W n / 4)) :=
    div_le_div_of_nonneg_left (exp_pos _).le hden_pos hden_le
  have hlow_eq : Real.exp (W n) / Real.exp (W n / 4) =
      Real.exp (3 * W n / 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hlow_ge : (1 : ℝ) ≤ Real.exp (3 * W n / 4) :=
    Real.one_le_exp (by nlinarith [hWnn n])
  have h1 : (1 : ℝ) ≤ (B n : ℝ) - (A n : ℝ) := by
    calc
      (1 : ℝ) ≤ Real.exp (3 * W n / 4) := hlow_ge
      _ = Real.exp (W n) / Real.exp (W n / 4) := hlow_eq.symm
      _ ≤ Real.exp (W n) / (d n * Real.exp (W n / 4)) := hlow
      _ ≤ (B n : ℝ) - (A n : ℝ) := hw
  have hExp : Real.exp (W n) ≤ Real.exp 1 := Real.exp_le_exp.mpr hWle
  have hupper : (B n : ℝ) - (A n : ℝ) ≤ Real.exp 1 - 2 := by
    nlinarith
  have he1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  linarith

/-- The former contradiction at `n = 0`, recovered from the unguarded fields.
This is what the paper-regime guard makes unavailable. -/
theorem unguarded_bounds_inconsistent_at_zero
    {W d : ℕ → ℝ} {A B : ℕ → ℕ} {cW cd : ℝ}
    (hWnn : ∀ n, 0 ≤ W n) (hdpos : ∀ n, 0 < d n)
    (hcW : 0 ≤ cW) (hcd : 0 ≤ cd)
    (hWub : ∀ n, W n ≤ Real.exp (cW * scale n))
    (hdub : ∀ n, d n ≤ Real.exp (cd * scale n))
    (hA : ∀ n, 2 ≤ A n)
    (hV : ∀ n, (B n : ℝ) ≤ Real.exp (W n))
    (hwidth : ∀ n, Real.exp (W n) / (d n * Real.exp (W n / 4)) ≤
      (B n : ℝ) - (A n : ℝ)) : False :=
  unguarded_bounds_inconsistent hWnn hdpos hcW hcd hWub hdub hA hV hwidth
    (n := 0) (by simp [audit_scale_zero])

/-- The `1 ≤ n` guard is **insufficient**: at `n = 1` the scale is still zero. -/
theorem guard_one_le_insufficient : ¬ ∀ n : ℕ, 1 ≤ n → 0 < scale n := by
  intro h
  have h1 : 0 < scale 1 := h 1 le_rfl
  rw [audit_scale_one] at h1
  exact lt_irrefl 0 h1

/-- The exact guard is `3 ≤ n`; at `n = 3` the scale is genuinely positive. -/
theorem guard_three_le : ∀ n : ℕ, 3 ≤ n → 0 < scale n :=
  fun _ hn => audit_scale_pos_of_three_le hn

/-! ## 3. A positive subexponential sequence used by the witnesses -/

/-- `exp (-(scale n)^2)` is a genuine `SubexpLoss`: positive at every index,
and faster than every `exp (-B · scale n)`. -/
theorem subexpLoss_exp_neg_sq :
    SubexpLoss (fun n : ℕ => Real.exp (-(scale n) ^ 2)) := by
  intro B hB
  filter_upwards [scale_grows.eventually_ge_atTop B] with n hn
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ scale n := le_trans hB.le hn
  nlinarith

theorem exp_neg_sq_pos (n : ℕ) : 0 < Real.exp (-(scale n) ^ 2) :=
  Real.exp_pos _

/-! ## 4. L19: every record is inhabited -/

theorem nonempty_PoissonQuotientInputs : Nonempty PoissonQuotientInputs :=
  ⟨poissonWitness⟩

theorem nonempty_EnergyScaleInputs :
    Nonempty (EnergyScaleInputs poissonWitness.W) :=
  ⟨poissonM₁⟩

theorem nonempty_ZeroModeCertificate :
    Nonempty (ZeroModeCertificate poissonWitness.W) :=
  ⟨commonZeroModeCertificate⟩

theorem nonempty_ThinLatticeData : Nonempty ThinLatticeData :=
  ⟨commonThinData⟩

theorem nonempty_LatticeThinInputs : Nonempty LatticeThinInputs :=
  ⟨commonThinData.toLatticeThinInputs⟩

/-- **The whole L19 record is inhabited**, with genuinely positive Poisson,
zero-mode and thin losses. -/
theorem nonempty_Wave15L19Inputs : Nonempty Wave15L19Inputs :=
  ⟨wave15L19Concrete⟩

theorem wave15L19Concrete_thin_loss_pos (n : ℕ) :
    0 < wave15L19Concrete.toL19FullCertificate.toL19Inputs.thin.loss n :=
  Wave15L19Inputs.thin_loss_pos wave15L19Concrete n

/-! ## 5. L20.2: the cells and the concentration source -/

/-- A finite one-point cell with actual score `1/2` and proxy `1/4`. -/
def cellWitness (L : ℝ) (hL : (1 / 4 : ℝ) ≤ L) : RandomizedL20_2.CellData 0 L where
  Ω := PUnit
  fintypeΩ := inferInstance
  w := fun _ => 1
  w_nonneg := by intro ω; norm_num
  w_sum := by simp
  P := PUnit
  fintypeP := inferInstance
  decEqP := inferInstance
  f := fun _ _ => 1 / 2
  proxy := fun _ _ => 1 / 4
  f_nonneg := by intro p ω; norm_num
  f_le_one := by intro p ω; norm_num
  proxy_nonneg := by intro p ω; norm_num
  proxy_le := by intro p ω; simpa using hL

theorem nonempty_CellData_zero : Nonempty (RandomizedL20_2.CellData 0 1) :=
  ⟨cellWitness 1 (by norm_num)⟩

theorem nonempty_SaddleConcentrationSource : Nonempty SaddleConcentrationSource :=
  ⟨source⟩

theorem nonempty_L20_2Inputs : Nonempty L20_2Inputs :=
  ⟨source.toInputs⟩

/-! ## 6. L20.4: dyad data and the top comparison threshold -/

/-- A positive dyad: one prime, error `exp (-(scale n)^2)`. -/
noncomputable def dyadWitness : DyadData PUnit where
  dyad := fun _ => {PUnit.unit}
  err := fun n _ => Real.exp (-(scale n) ^ 2)
  err_nonneg := by intro n p; exact (exp_neg_sq_pos n).le
  avg := fun n => Real.exp (-(scale n) ^ 2)
  avg_def := by
    intro n
    simp
  avg_subexp := subexpLoss_exp_neg_sq

theorem nonempty_DyadData : Nonempty (DyadData PUnit) :=
  ⟨dyadWitness⟩

/-- The top comparison threshold with `L = 0`: all internal and exceptional
masses are the genuine positive sequence `exp (-(scale n)^2)`, and the top mass
is exactly the comparison right-hand side. -/
noncomputable def topWitness : TopG12AdditiveData where
  L := 0
  interior := fun n _ => Real.exp (-(scale n) ^ 2)
  step := fun _ => 1
  eta := fun n => Real.exp (-(scale n) ^ 2)
  epsRat := fun n => Real.exp (-(scale n) ^ 2)
  epsIn := fun n => Real.exp (-(scale n) ^ 2)
  top := fun n => 2 * Real.sqrt (Real.exp (-(scale n) ^ 2)) +
    Real.exp (-(scale n) ^ 2)
  Ctop := fun _ => 1
  cTop := 0
  cInt := 0
  interior_nonneg := by intro n i; exact (exp_neg_sq_pos n).le
  eta_nonneg := by intro n; exact (exp_neg_sq_pos n).le
  epsRat_nonneg := by intro n; exact (exp_neg_sq_pos n).le
  epsIn_nonneg := by intro n; exact (exp_neg_sq_pos n).le
  top_nonneg := by
    intro n
    have h : 0 ≤ Real.sqrt (Real.exp (-(scale n) ^ 2)) := Real.sqrt_nonneg _
    have hq : 0 ≤ Real.exp (-(scale n) ^ 2) := (exp_neg_sq_pos n).le
    nlinarith
  Ctop_nonneg := by intro n; norm_num
  cTop_nonneg := by norm_num
  recurrence := by
    refine Filter.Eventually.of_forall ?_
    intro n i hi
    omega
  step_ge_one := by
    refine Filter.Eventually.of_forall ?_
    intro n
    norm_num
  alpha_nonneg := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have h : 0 ≤ Real.exp (-(scale n) ^ 2) := (exp_neg_sq_pos n).le
    nlinarith
  depth_bound := by
    refine Filter.Eventually.of_forall ?_
    intro n
    simp
  additive_comparison := by
    refine Filter.Eventually.of_forall ?_
    intro n
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
    apply le_of_eq
    ring
  Ctop_le := by
    refine Filter.Eventually.of_forall ?_
    intro n
    simp
  base_subexp := subexpLoss_exp_neg_sq
  eta_subexp := subexpLoss_exp_neg_sq
  epsRat_subexp := subexpLoss_exp_neg_sq
  epsIn_subexp := subexpLoss_exp_neg_sq

theorem nonempty_TopG12AdditiveData : Nonempty TopG12AdditiveData :=
  ⟨topWitness⟩

theorem nonempty_topComparison :
    Nonempty (TopG12AdditiveDepthComparison topWitness.top topWitness.Ctop
      topWitness.interior topWitness.step topWitness.eta topWitness.epsRat
      topWitness.epsIn topWitness.L) :=
  ⟨topWitness.additive_comparison⟩

/-! ## 7. L27: an explicit `L27_1Inputs` and `L27StageOneFinishInputs` -/

theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
  simpa using h

theorem log_three_le_two : Real.log 3 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith

theorem sqrt_five_le_three : Real.sqrt 5 ≤ 3 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

theorem two_le_sqrt_five : (2 : ℝ) ≤ Real.sqrt 5 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

noncomputable def zP : ℕ → ℕ := fun _ => 5
noncomputable def zY : ℕ → ℝ := fun _ => 3
noncomputable def zW : ℕ → ℝ := fun _ => 4
noncomputable def zPsi : ℕ → ℝ := fun _ => 1
noncomputable def zCurves : ℕ → ℕ :=
  fun n => Nat.ceil (100 * (scale n) ^ 2) + 100
noncomputable def zOrderCount : ℕ → ℕ → ℕ :=
  fun _ j => if j = 2 then 5 else if j = 7 then 9 else 0
noncomputable def zOrderTop : ℕ → ℕ := fun _ => 11
noncomputable def zSmooth : ℕ → ℕ → Bool := fun _ j => decide (j = 2)
noncomputable def zSuccess : ℕ → ℝ := fun _ => 4 / 5
noncomputable def zGcdFail : ℕ → ℝ := fun _ => 1 / 5
noncomputable def zJointFail : ℕ → ℝ := fun n => (1 / 5 : ℝ) ^ zCurves n
noncomputable def zCofactor : ℕ → ℕ := fun _ => 2
noncomputable def zKappa : ℝ := 1
noncomputable def zEta : ℝ := 1

theorem zCurveTotal_eq (n : ℕ) : curveTotal zOrderCount zOrderTop n = 14 := by
  simp [curveTotal, zOrderCount, zOrderTop, Finset.sum_range_succ]
  norm_num

theorem zSmoothCount_eq (n : ℕ) :
    smoothCount zSmooth zOrderTop n = 1 := by
  simp [smoothCount, zSmooth, zOrderTop]

theorem zSC_eq (n : ℕ) : smoothCurves zSmooth zOrderCount zOrderTop n = 5 := by
  simp [smoothCurves, zSmooth, zOrderCount, zOrderTop]

/-- **The explicit `L27_1Inputs`.**  `p = 5`, `y = 3`, `w = 4`, one smooth order
at `j = 2` with five curves and a filler of nine curves at `j = 7`; success
`4/5`, singular fraction `1/5`, cofactor `2`. -/
noncomputable def zL27 : L27_1Inputs where
  p := zP
  y := zY
  w := zW
  curves := zCurves
  psi := zPsi
  orderCount := zOrderCount
  orderTop := zOrderTop
  smooth := zSmooth
  success := zSuccess
  gcdFail := zGcdFail
  jointFail := zJointFail
  cofactor := zCofactor
  κ := zKappa
  η := zEta
  p_pos := by intro n; norm_num [zP]
  y_gt_one := by intro n; norm_num [zY]
  y_le_w := by intro n; norm_num [zY, zW]
  psi_nonneg := by intro n; norm_num [zPsi]
  κ_pos := by norm_num [zKappa]
  η_pos := by norm_num [zEta]
  cofactor_ge_two := by intro n; norm_num [zCofactor]
  orderTop_spec := by
    intro n
    simp only [zP, zOrderTop]
    push_cast
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  curveTotal_pos := by
    intro n
    rw [zCurveTotal_eq]
    norm_num
  curve_total_le := by
    intro n
    rw [zCurveTotal_eq]
    norm_num [zP]
  hasse := by
    intro n j hj
    simp only [zOrderCount] at hj
    split_ifs at hj with h2 h7
    · subst h2
      change |(2 : ℝ) - ((5 : ℝ) + 1)| ≤ 2 * Real.sqrt (5 : ℝ)
      have h4 : |(2 : ℝ) - ((5 : ℝ) + 1)| = 4 := by norm_num
      rw [h4]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    · subst h7
      change |(7 : ℝ) - ((5 : ℝ) + 1)| ≤ 2 * Real.sqrt (5 : ℝ)
      have h1 : |(7 : ℝ) - ((5 : ℝ) + 1)| = 1 := by norm_num
      rw [h1]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    · omega
  smooth_realized := by
    intro n j hj
    simp only [zSmooth] at hj
    simp only [decide_eq_true_eq] at hj
    subst hj
    norm_num [zOrderCount]
  smooth_bound := by
    intro n j hj
    simp only [zSmooth] at hj
    simp only [decide_eq_true_eq] at hj
    subst hj
    norm_num [zW]
  psi_card := by
    intro n
    rw [zSmoothCount_eq]
    norm_num [zPsi]
  deuring_count := by
    intro n j hj
    simp only [zSmooth] at hj
    simp only [decide_eq_true_eq] at hj
    subst hj
    change (1 : ℝ) * Real.sqrt (5 : ℝ) ≤ (5 : ℝ)
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  stage_one := by
    intro n
    have hlog : (1 : ℝ) ≤ Real.log (zY n) := by
      simpa [zY] using one_le_log_three
    have hlogpos : 0 < Real.log (zY n) := lt_of_lt_of_le zero_lt_one hlog
    have hSF : smoothFraction zSmooth zOrderCount zOrderTop n = 5 / 14 := by
      unfold smoothFraction
      rw [zSC_eq, zCurveTotal_eq]
    rw [hSF]
    rw [div_le_iff₀ hlogpos]
    simp only [zSuccess]
    nlinarith [hlog]
  success_le_one := by intro n; norm_num [zSuccess]
  gcd_exit := by
    refine ⟨?_, ?_, ?_⟩
    · intro n; norm_num [zGcdFail]
    · intro n; norm_num [zGcdFail, zP]
    · intro n; norm_num [zGcdFail, zSuccess]
  independence := by
    intro n
    norm_num [zJointFail, zSuccess]
  curve_budget := by
    filter_upwards [scale_grows.eventually_ge_atTop 1] with n hn
    have hs : 0 ≤ scale n := by linarith
    have hceil : 100 * (scale n) ^ 2 ≤ (Nat.ceil (100 * (scale n) ^ 2) : ℝ) :=
      Nat.le_ceil _
    have hcurve : (100 : ℝ) * (scale n) ^ 2 ≤ (zCurves n : ℝ) := by
      unfold zCurves
      push_cast
      linarith
    have hden_pos : 0 < Real.sqrt 5 * Real.log 3 := by positivity
    have hden_le : Real.sqrt 5 * Real.log 3 ≤ 6 := by
      have h1 := sqrt_five_le_three
      have h2 := log_three_le_two
      have h3 : 0 ≤ Real.log 3 := le_trans zero_le_one one_le_log_three
      nlinarith
    have hfrac : (1 / 6 : ℝ) ≤ 1 / (Real.sqrt 5 * Real.log 3) :=
      one_div_le_one_div_of_le hden_pos hden_le
    have hmul : (1 / 6 : ℝ) * (zCurves n : ℝ) ≤
        (zCurves n : ℝ) * (1 / (Real.sqrt 5 * Real.log 3)) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
    have hmain : (2 + 1 : ℝ) * scale n ≤
        (1 / 4 : ℝ) * ((zCurves n : ℝ) * (1 / (Real.sqrt 5 * Real.log 3))) := by
      nlinarith [hcurve, hs, hmul]
    simpa only [zKappa, zPsi, zP, zY, zEta, Nat.cast_ofNat] using hmain
  logFactor_subexp := by
    intro δ hδ
    filter_upwards [scale_grows.eventually_ge_atTop 0] with n hn
    have hcof : ((zCofactor n).log2 : ℝ) = 1 := by norm_num [zCofactor]
    rw [hcof]
    exact Real.one_le_exp (mul_nonneg hδ.le hn)

theorem zSmoothPointMass (n : ℕ) :
    smoothPointMass zL27 n = 10 := by
  simp [smoothPointMass, zL27, zSmooth, zOrderCount, zOrderTop]
  norm_num

theorem zKilledPointMass (n : ℕ) :
    killedPointMass zL27 (fun _ j => if j = 2 then 2 else 0) n = 10 := by
  simp [killedPointMass, zL27, zSmooth, zOrderCount, zOrderTop]
  norm_num

theorem zL27_CT (n : ℕ) : zL27.CT n = 14 :=
  zCurveTotal_eq n

/-- **The L27.1 kill-law data** at the explicit witness. -/
noncomputable def zKillLaw : L27KillLawInputs zL27 where
  gcdFail_eq := by intro n; norm_num [zL27, zGcdFail, zP]
  noFactorData :=
    { noFac := fun _ => 5
      noFac_eq := by intro n; norm_num [zL27, zP, zSuccess, singularCurveTotal]
      bad_le_noFac := by intro n; simp [singularCurveCount, zL27, zP]
      noFac_le_total := by intro n; simp [singularCurveTotal, zL27, zP] }
  pointKill := fun _ j => if j = 2 then 2 else 0
  smooth_order_pos := by
    intro n j hj
    simp only [zL27, zSmooth] at hj
    simp only [decide_eq_true_eq] at hj
    omega
  success_ge_killed := by
    intro n
    rw [zKilledPointMass, zL27_CT]
    norm_num [zL27, zSuccess]
  kill_mass := by
    intro n
    rw [zSmoothPointMass, zKilledPointMass]
    have hlog : (1 : ℝ) ≤ Real.log (zL27.y n) := by
      simpa [zL27, zY] using one_le_log_three
    nlinarith
  cutoff := by
    intro n
    change Real.exp 1 ≤ (3 : ℝ)
    exact Real.exp_one_lt_three.le

/-- The Hurwitz function `H(-D) = 2√D` on positive `D`. -/
noncomputable def zHurwitz : ℤ → ℝ := fun d =>
  if 0 < d then 2 * Real.sqrt (d : ℝ) else 0

/-- A trace count realising the one-sided Deuring bound. -/
noncomputable def zTraceCount : ℕ → ℤ → ℕ := fun n t =>
  Nat.ceil (2 * Real.sqrt (max (((traceDisc (zP n) t : ℤ) : ℝ)) 0)) + 1

/-- **The L27 Hurwitz/Deuring block** at the explicit witness. -/
noncomputable def zHurwitzInputs : L27HurwitzInputs zL27 where
  hurwitz := zHurwitz
  traceCount := zTraceCount
  c := 2
  θ := 1 / 2
  c_pos := by norm_num
  θ_pos := by norm_num
  kappa_le := by
    change (1 : ℝ) ≤ 2 * Real.sqrt (1 / 2)
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      Real.sqrt_nonneg (1 / 2 : ℝ)]
  siegel_lower := by
    intro n t ht
    simp only [zHurwitz]
    rw [if_pos ht]
  disc_scale := by
    intro n j hj
    simp only [zL27, zSmooth] at hj
    simp only [decide_eq_true_eq] at hj
    subst hj
    norm_num [zL27, zP, frobeniusDisc, hasseTrace]
  trace_class_lower := by
    intro n t ht
    simp only [zL27] at ht ⊢
    have hval : zHurwitz (traceDisc (zP n) t) =
        2 * Real.sqrt ((traceDisc (zP n) t : ℤ) : ℝ) := by
      simp [zHurwitz, ht]
    rw [hval]
    simp only [zTraceCount]
    have hmax : max (((traceDisc (zP n) t : ℤ) : ℝ)) 0 =
        ((traceDisc (zP n) t : ℤ) : ℝ) := by
      rw [max_eq_left]
      exact_mod_cast ht.le
    rw [hmax]
    have hceil := Nat.le_ceil (2 * Real.sqrt ((traceDisc (zP n) t : ℤ) : ℝ))
    push_cast
    linarith
  orderCount_contains_trace := by
    intro n j hj
    simp only [zL27, zSmooth] at hj
    simp only [decide_eq_true_eq] at hj
    subst hj
    norm_num [zL27, zP, zOrderCount, zTraceCount, hasseTrace, traceDisc]
  j_invariant_strata := by
    intro n
    refine ⟨{0, 1, 2}, (fun x => if x = 0 then 6 else if x = 1 then 6 else 2),
      {0, 1}, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [zL27, zP]
    · decide
    · decide
    · intro x hx hxnot
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact absurd (by simp) hxnot
      · exact absurd (by simp) hxnot
      · norm_num
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · norm_num
      · norm_num
    · change curveTotal zOrderCount zOrderTop n =
        ∑ x ∈ ({0, 1, 2} : Finset ℕ),
          ((if x = 0 then 6 else if x = 1 then 6 else 2 : ℕ) : ℝ)
      rw [zCurveTotal_eq]
      norm_num [Finset.sum_insert]
  p_ge_four := by intro n; norm_num [zL27, zP]

/-- **The L27 stage-one finish bundle** at the explicit witness. -/
noncomputable def zL27Finish : L27StageOneFinishInputs zL27 where
  killLaw := zKillLaw
  hurwitz := zHurwitzInputs
  hasse := zL27.hasse
  curve_budget := zL27.curve_budget
  log_factor_subexp := zL27.logFactor_subexp

theorem nonempty_L27_1Inputs : Nonempty L27_1Inputs :=
  ⟨zL27⟩

theorem nonempty_L27StageOneFinishInputs :
    Nonempty (L27StageOneFinishInputs zL27) :=
  ⟨zL27Finish⟩

theorem nonempty_HasseBound : Nonempty (HasseBound zP zOrderCount) :=
  ⟨zL27.hasse⟩

theorem nonempty_CurveBudget :
    Nonempty (CurveBudget zP zY zPsi zCurves zKappa zEta) :=
  ⟨zL27.curve_budget⟩

/-! ## 8. L34: `Wave28L34Inputs` and `L34ChebotarevSidesInputs` -/

/-- The effective-Chebotarev inhabitant has `F = 1` and `log |Δ| = 1`. -/
theorem effectiveInhabitant_F :
    effectiveInhabitant.toL34ChebotarevSidesInputs.F = fun _ => 1 := rfl

theorem effectiveInhabitant_discLog :
    effectiveInhabitant.toL34ChebotarevSidesInputs.discLog = fun _ => 1 := rfl

/-- **A `Wave28L34Inputs` inhabitant.**  All non-`β₀` fields are the explicit
effective-Chebotarev inhabitant; `β₀ = 1/2` satisfies the GRH residual
`β₀ ≤ 1/2`, and the vacuous zero-free field is `zeroRealPart = 1/2`. -/
noncomputable def zWave28 : Wave28L34Inputs :=
  let eff := effectiveInhabitant.toL34ChebotarevSidesInputs
  { beta0 := fun _ => 1 / 2
    zeroRealPart := fun _ => 1 / 2
    degree := eff.degree
    discLog := eff.discLog
    F := eff.F
    T := eff.T
    count := eff.count
    inertCount := eff.inertCount
    degreeOneInert := eff.degreeOneInert
    liX := eff.liX
    liBeta0 := eff.liBeta0
    pTrial := eff.pTrial
    actualMiss := eff.actualMiss
    classCount := eff.classCount
    R := eff.R
    K := eff.K
    C := eff.C
    cZ := eff.cZ
    cz := eff.cz
    cbr := eff.cbr
    csel := eff.csel
    Ch := eff.Ch
    zeroFree :=
      { cz_pos := eff.zeroFree.cz_pos
        above_beta := by
          intro n h
          norm_num at h }
    range := eff.range
    T_ge_one := eff.T_ge_one
    cheb := eff.cheb
    inert_ge_count := eff.inert_ge_count
    bracket := eff.bracket
    error_scalar := eff.error_scalar
    degree_loss_scalar := eff.degree_loss_scalar
    degree_one_reduction := eff.degree_one_reduction
    selection := eff.selection
    budget := eff.budget
    classCount_pos := eff.classCount_pos
    classCubic := eff.classCubic
    constant_margin := eff.constant_margin
    scale_cubic := eff.scale_cubic
    actualMiss_nonneg := eff.actualMiss_nonneg
    union_bound := eff.union_bound
    pTrial_nonneg := eff.pTrial_nonneg
    pTrial_le_one := eff.pTrial_le_one
    starkF_pos := eff.stark.F_pos
    beta0_le_half := by intro n; norm_num
    paperBeta0_ge_half := by
      intro n
      rw [show eff.F = fun _ => 1 from rfl,
        show eff.discLog = fun _ => 1 from rfl]
      norm_num [paperBeta0] }

theorem nonempty_Wave28L34Inputs : Nonempty Wave28L34Inputs :=
  ⟨zWave28⟩

theorem nonempty_L34ChebotarevSidesInputs :
    Nonempty L34ChebotarevSidesInputs :=
  ⟨zWave28.toL34ChebotarevSidesInputs⟩

theorem zWave28_beta0_le_half (n : ℕ) : zWave28.beta0 n ≤ 1 / 2 :=
  zWave28.beta0_le_half n

/-! ## 9. C5 and P1 -/

/-! ### A genuine `FailureData` inhabitant (guarded at `1 ≤ n`) -/

noncomputable def failK : ℕ → ℝ := fun _ => 1200

noncomputable def failLc : ℕ → ℝ := fun n => (n : ℝ) ^ 2 + 1

noncomputable def failPTrial : ℕ → ℝ := fun _ => 1 / 2

noncomputable def failRcurve : ℕ → ℕ := fun n =>
  Nat.ceil (Real.exp (((101 : ℝ) / 100) * (Real.log 2 * failK n)) * failLc n)

def failNodes : ℕ → ℕ := fun _ => 1

noncomputable def failFailure : ℕ → ℝ := fun n => (1 / 2) ^ (failRcurve n) / 2

theorem failK_nonneg (n : ℕ) : 0 ≤ failK n := by norm_num [failK]

theorem failK_large (n : ℕ) : 1200 ≤ failK n := le_rfl

theorem failLc_ge_one (n : ℕ) : 1 ≤ failLc n := by
  unfold failLc
  nlinarith [sq_nonneg (n : ℝ)]

theorem scale_le_log {n : ℕ} (hlog : 1 ≤ Real.log n) : scale n ≤ Real.log n := by
  have hlogpos : 0 < Real.log n := zero_lt_one.trans_le hlog
  have hloglog_nonneg : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlog
  have hlogs : Real.log (Real.log n) ≤ Real.log n := by
    linarith only [Real.log_le_sub_one_of_pos hlogpos]
  have h2 : (Real.log (Real.log n)) ^ (2 / 3 : ℝ) ≤
      (Real.log n) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hloglog_nonneg hlogs (by norm_num)
  have h3 : 0 ≤ (Real.log n) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (le_of_lt hlogpos) _
  calc
    scale n = (Real.log n) ^ (1 / 3 : ℝ) *
        (Real.log (Real.log n)) ^ (2 / 3 : ℝ) := rfl
    _ ≤ (Real.log n) ^ (1 / 3 : ℝ) * (Real.log n) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left h2 h3
    _ = Real.log n := by rw [← Real.rpow_add hlogpos]; norm_num

theorem failConfidence : ∀ B : ℝ, 0 < B →
    ∀ᶠ n : ℕ in atTop, B * scale n + Real.log (2 * (n : ℝ)) ≤ 64 * failLc n := by
  intro B hB
  have hlogev : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hlogev, eventually_ge_atTop (max 3 (max 1 ⌈B + 1⌉₊))] with n hlog hn
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hceil : ⌈B + 1⌉₊ ≤ n := le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) hn
  have hB1 : B + 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil (B + 1)) (by exact_mod_cast hceil)
  have hBn : B ≤ (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hscale : scale n ≤ Real.log n := scale_le_log hlog
  have hlogn : Real.log n ≤ (n : ℝ) := by
    linarith only [Real.log_le_sub_one_of_pos hnpos]
  have hBscale : B * scale n ≤ (n : ℝ) ^ 2 := by
    have h1 : B * scale n ≤ B * (n : ℝ) :=
      mul_le_mul_of_nonneg_left (hscale.trans hlogn) hB.le
    have h2 : B * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hBn (by positivity)
    nlinarith
  have hlog2n : Real.log (2 * (n : ℝ)) ≤ (n : ℝ) ^ 2 + 1 := by
    have hmul : Real.log (2 * (n : ℝ)) =
        Real.log 2 + Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hnpos)]
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    linarith
  unfold failLc
  nlinarith

theorem failUseful (n : ℕ) :
    Real.exp (-(((201 : ℝ) / 200) * (Real.log 2 * failK n))) ≤ failPTrial n := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hge : Real.log 2 ≤ ((201 : ℝ) / 200) * (Real.log 2 * failK n) := by
    unfold failK
    nlinarith
  unfold failPTrial
  calc
    Real.exp (-(((201 : ℝ) / 200) * (Real.log 2 * failK n))) ≤
        Real.exp (-(Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num

theorem failCurveCap (n : ℕ) :
    Real.exp (((101 : ℝ) / 100) * (Real.log 2 * failK n)) * failLc n ≤
      (failRcurve n : ℝ) := by
  unfold failRcurve
  exact Nat.le_ceil _

theorem failNodes_pos : ∀ n : ℕ, 1 ≤ n → 0 < failNodes n := by
  intro n _
  simp [failNodes]

theorem failFactorTreeNodes : FactorTreeNodes failNodes := by
  intro n hn
  simp only [failNodes]
  omega

theorem failFailure_pos (n : ℕ) : 0 < failFailure n := by
  unfold failFailure
  positivity

theorem failUnion (n : ℕ) : failFailure n ≤
    (failNodes n : ℝ) * (1 - failPTrial n) ^ (failRcurve n) := by
  have hpos : (0 : ℝ) < (1 / 2) ^ (failRcurve n) := pow_pos (by norm_num) _
  simp only [failNodes, failFailure, failPTrial, Nat.cast_one, one_mul]
  have hbase : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hbase]
  linarith

/-- **The current `FailureData` is inhabited**, with strictly positive failure.
The `2n` tree bound is guarded at `1 ≤ n`; `nodes 0 = 1` is allowed. -/
noncomputable def failureDataWitness : FailureData where
  k := failK
  k_nonneg := failK_nonneg
  k_large := failK_large
  Lc := failLc
  Lc_ge_one := failLc_ge_one
  confidence_dominates := failConfidence
  pTrial := failPTrial
  pTrial_nonneg := fun _ => by norm_num [failPTrial]
  pTrial_le_one := fun _ => by norm_num [failPTrial]
  useful_prime_split := failUseful
  Rcurve := failRcurve
  curve_trial_cap := failCurveCap
  nodes := failNodes
  nodes_pos := failNodes_pos
  factor_tree_nodes := failFactorTreeNodes
  failure := failFailure
  failure_pos := failFailure_pos
  failure_union := failUnion

theorem nonempty_failureData_audit : Nonempty FailureData :=
  ⟨failureDataWitness⟩

/-- The P1 witness miss, `exp (-(scale n)^2)`, positive at every index. -/
noncomputable def p1MissWitness (n : ℕ) : ℝ := Real.exp (-(scale n) ^ 2)

theorem p1MissWitness_pos (n : ℕ) : 0 < p1MissWitness n :=
  Real.exp_pos _

theorem p1MissWitness_success : PrepassSuccess p1MissWitness := by
  intro δ hδ
  filter_upwards [scale_grows.eventually_ge_atTop δ] with n hn
  unfold p1MissWitness
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ scale n := le_trans hδ.le hn
  nlinarith

noncomputable def p1CostWitness : ℕ → ℝ := fun _ => 1

theorem p1CostWitness_pos (n : ℕ) : 0 < p1CostWitness n := by
  norm_num [p1CostWitness]

noncomputable def p1CostWitness_rate : SubexpCostRate p1CostWitness where
  eps := fun _ => 0
  eps_nonneg := fun _ => le_rfl
  eps_tendsto := tendsto_const_nhds
  cost_le_exp := by
    refine Filter.Eventually.of_forall ?_
    intro n
    simp [p1CostWitness]

noncomputable def p1Witness : SubexpPrepassInput where
  miss := p1MissWitness
  miss_nonneg := fun n => (p1MissWitness_pos n).le
  success := p1MissWitness_success
  cost := p1CostWitness
  cost_nonneg := fun n => (p1CostWitness_pos n).le
  cost_subexp := p1CostWitness_rate

theorem nonempty_subexpPrepassInput : Nonempty SubexpPrepassInput :=
  ⟨p1Witness⟩

theorem p1Witness_miss_pos (n : ℕ) : 0 < p1Witness.miss n :=
  p1MissWitness_pos n

/-- A genuine (positive-loss) stage budget on any concrete epoch: the stage
succeeds everywhere and charges the positive loss `1`. -/
noncomputable def stageBudgetWitness {N : ℕ} [NeZero N] (D : ConcreteEpochData N) :
    StageBudget D where
  ok := fun _ => True
  loss := 1
  loss_nonneg := by norm_num
  fail_le := Cogentic.RandomizedFieldPoolDescent.pmfProb_le_one D.ideal _

theorem nonempty_stageBudget :
    Nonempty (StageBudget
      (Cogentic.RandomizedConcreteC1.concreteEpoch 3 (by norm_num))) := by
  haveI : NeZero 3 := ⟨by norm_num⟩
  exact ⟨stageBudgetWitness _⟩

/-! ## 10. The compile-checked status table -/

inductive ZeroIndexStatus where
  | inhabited
  | guarded
  deriving DecidableEq, Repr

/-- The status of every record scanned at `n = 0`.  `L18_4Certificate` is
`guarded`: after the growth-field repair it is not refutable, but it is
inhabited only modulo `L18_4CoreResidual` (`W_dominates` and `cellSupply`).
Every other record has an explicit unconditional inhabitant above. -/
def zeroIndexStatusTable : List (String × ZeroIndexStatus) :=
  [ ("L18_4Certificate", .guarded),
    ("L18_4CoreResidual", .guarded),
    ("PoissonQuotientInputs", .inhabited),
    ("EnergyScaleInputs", .inhabited),
    ("ZeroModeCertificate", .inhabited),
    ("ThinLatticeData", .inhabited),
    ("LatticeThinInputs", .inhabited),
    ("Wave15L19Inputs", .inhabited),
    ("CellData (L20.2)", .inhabited),
    ("SaddleConcentrationSource", .inhabited),
    ("L20_2Inputs", .inhabited),
    ("DyadData (L20.4)", .inhabited),
    ("TopG12AdditiveData (L20.4)", .inhabited),
    ("TopG12AdditiveDepthComparison", .inhabited),
    ("L27_1Inputs", .inhabited),
    ("L27StageOneFinishInputs", .inhabited),
    ("HasseBound", .inhabited),
    ("CurveBudget", .inhabited),
    ("Wave28L34Inputs", .inhabited),
    ("L34ChebotarevSidesInputs", .inhabited),
    ("FailureData", .inhabited),
    ("SubexpPrepassInput", .inhabited),
    ("StageBudget", .inhabited) ]

theorem zeroIndexStatusTable_length : zeroIndexStatusTable.length = 23 := rfl

end

end Cogentic.RandomizedZeroIndexAudit
