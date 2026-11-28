import Cogentic.RandomizedPaperEndpointWave17
import Cogentic.RandomizedL20_2
import Cogentic.RandomizedL30GlobalLower
import Cogentic.RandomizedL30LPP
import Cogentic.RandomizedL30SharpWitness
import Cogentic.RandomizedL30Younis

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Wave 17 audit: field-by-field status of `Wave17Inputs`

This file audits every field of
`Cogentic.RandomizedPaperEndpointWave17.Wave17Inputs` and of its only wave-17
sub-record, `Wave17L21_2Inputs`.  Each field is classified as

* `(a) proved` — its type is unconditionally inhabited (or a two-line
  consequence of the preceding data);
* `(b) reduced` — a named classical/analytic statement with a proven reduction
  to the smallest interface; or
* `(c) impossible` — no inhabitant exists.

## The L30 record is repaired

The current repository has the `n = 0`-guarded tree bound
`FactorTreeNodes nodes := ∀ n, 1 ≤ n → nodes n ≤ 2 * n` and the guarded
`nodes_pos : ∀ n, 1 ≤ n → 0 < nodes n`; `failure_union` and `failure_pos` are
unguarded.  There is no contradiction at `n = 0` any more: `nodes 0` may be `1`.

This file proves non-vacuity with an explicit witness
(`failureDataWitness`): `k = 1200`, `pTrial = 1/2`, `Lc n = n² + 1`,
`Rcurve n = ⌈exp ((101/100) log 2 · 1200) · Lc n⌉`, `nodes n = 1`, and the
strictly positive failure `(1/2) ^ Rcurve n / 2`.  The full L30 record
`wave14L30InputsWitness` is then assembled from the genuine constant-scale count
witness (`p = 4`, central odd count `1`, global odd count `4`) and the unit
Cantor data.  Hence `nonempty_failureData` and `nonempty_wave14L30Inputs`.

## The C5 ledger adapter is now satisfiable

The count-assembled C5 bundle has
`c5TotalLoss = pool.loss + survivor.loss + descent.loss
 + algebraMass + coupling.loss` (`Wave15C5Data.toC5_totalLoss`), with every
summand nonnegative and `algebraMass = 0` when all samples are good.  This file
constructs C5 data with arbitrarily small total loss:

* the pool loss is `exp (-(K:ℝ)/16)` (`smallPool_loss_eq`) and `K` is chosen as
  `⌈16 log (4/η)⌉`, so it is at most `η/4` (`smallPool_loss_le`);
* the survivor and descent stage budgets have loss `η/4` (`smallStage`);
* the recognizer coupling has loss `min (η/4) (1/2048)` (`smallCoupling`);
* the standard one-point epoch `goodEpoch n` has a constant `some` solver, so
  every sample is good and `algebraMass = 0`
  (`algebraMass_eq_zero_of_all_good`), with a uniform ideal law
  (`goodEpoch_uniform`) and `HalfMassCount` (`goodEpoch_halfMass`).

Hence `c5TotalLoss_goodC5Data_le : c5TotalLoss … ≤ η n`, and the C5 side of
`loss_le` can always be made smaller than the (strictly positive) ledger total
`wave17Slots … .total n` (`wave17Slots_total_pos`).
`nonempty_wave17Inputs_of_analytic` assembles the whole `Wave17Inputs` record on
this standard family from the ten analytic leaf records and C1–C4.  So there is
no structural obstruction left: `Wave17Inputs` is inhabited **modulo exactly
the genuine analytic inputs** listed in `wave17_remaining_inputs` and
`nonempty_wave17Inputs_of_remaining`.

## The other fields

All remaining fields are `(a)` or `(b)`.  In particular:

* `l4N`, `l4Bits`, `l4N_odd`, `l4Bits_budget` are inhabited with a genuine
  nonzero budget (`N = 9`, `bits = 3`, `2 ^ 3 = 8 ≤ 9`);
* the structural fields of `Wave17L21_2Inputs` (Fourier and two-scale fields)
  are inhabited with a *nonzero* discrepancy profile: `N = 1` and
  `coeff n 0 = exp (-paperRate X n / 4)`, whose low-band energy is the nonzero
  `exp (-paperRate X n / 2)` (`coreWitness`, `nonempty_l21_2StructuralCore`);
* `Ksum_le` is a theorem (wave 17), and the derived `Kline` is an absolute
  constant — the growing-vs-constant defect of wave 16 is gone
  (`wave17_Ksum_le`, `wave17_referencePerron_absolute`);
* `lineBound` is reduced to the named classical input
  `ClassicalLogDerivLineBound` by a proven exponent-monotonicity step
  (`verticalLineBound_of_classicalLogDeriv_exponent`); `hRH` is
  `RiemannZetaZerosOnLine`; `verticalTail`, `localCount`, `b_le_B` and
  `a_ge_log_two` are the remaining named L21.2 inputs, listed in
  `wave17_l21_2_residual_analytic_inputs`;
* `c1`/`c2` are reduced to `GlobalProductIdentity`/`HiddenSignSymmetry`
  (`c1Inputs_of_concrete`, `c2Inputs_of_concrete`).

No `sorry`, `admit`, `axiom`, `native_decide` is used, and no loss is set to
zero by fiat.  (The only zeros below are the *proved* zero L4 defect —
`wave15L4Loss_zero` — and the provably-zero `True`-event probabilities used in
the existing C5 count bundle.)
-/

namespace Cogentic.RandomizedWave17Audit

universe u

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedP1Sub
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL4BitBudget
open Cogentic.RandomizedEpochPool
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedC5GoodIff
open Cogentic.RandomizedC5Coupling
open Cogentic.RandomizedC5HitMassFinish
open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpoch.ConcreteEpochChecks
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedPaperEndpointWave17

/-! ## 1. The field-status vocabulary -/

/-- The three-way classification requested by the audit. -/
inductive FieldStatus
  /-- `(a)` proved unconditionally (or inhabited by explicit data). -/
  | proved
  /-- `(b)` reduced to a named classical/analytic input with a proven reduction. -/
  | reduced
  /-- `(c)` structurally uninhabited / contradictory. -/
  | impossible
  deriving DecidableEq, Repr

/-- The twenty-two fields of `Wave17Inputs`, in declaration order. -/
inductive Wave17Field
  | l18_4 | l19 | l20_2 | l20_4 | l21_2
  | l4N | l4Bits | l4N_odd | l4Bits_budget
  | l27_data | l27_finish | l30 | l34 | p1
  | c1 | c2 | c3 | c4
  | concrete | concrete_eq | c5Data | loss_le
  deriving DecidableEq, Repr

/-- The requested field-status table.  The four L4 scalar fields are proved
(the bit-budget realization `realized_fullSplitBand_of_bitBudget` is a theorem,
and `N = 9`, `bits = 3` inhabits them); `l30` is a named, inhabited record
(`nonempty_wave14L30Inputs`); and the C5 ledger adapter `loss_le` is now
satisfiable (`c5TotalLoss_goodC5Data_le`).  No field is impossible. -/
def Wave17Field.status : Wave17Field → FieldStatus
  | .l4N => .proved
  | .l4Bits => .proved
  | .l4N_odd => .proved
  | .l4Bits_budget => .proved
  | _ => .reduced

/-- The explicit field list (avoids a `Fintype` instance, which the pinned
toolchain does not derive for this enumeration). -/
def allWave17Fields : List Wave17Field :=
  [ .l18_4, .l19, .l20_2, .l20_4, .l21_2
  , .l4N, .l4Bits, .l4N_odd, .l4Bits_budget
  , .l27_data, .l27_finish, .l30, .l34, .p1
  , .c1, .c2, .c3, .c4
  , .concrete, .concrete_eq, .c5Data, .loss_le ]

/-- The table has exactly the 22 declared fields. -/
theorem allWave17Fields_length : allWave17Fields.length = 22 := rfl

/-! ## 2. The L30 failure data is inhabited -/

/-- The guarded tree bound gives the `2n` bound on the epoch regime. -/
theorem nodes_le_two_mul {nodes : ℕ → ℕ} (h : FactorTreeNodes nodes) {n : ℕ}
    (hn : 1 ≤ n) : nodes n ≤ 2 * n :=
  h n hn

/-- The witness scale `k = 1200`. -/
noncomputable def failK : ℕ → ℝ := fun _ => 1200

/-- The witness confidence parameter `L_c = n² + 1`. -/
noncomputable def failLc : ℕ → ℝ := fun n => (n : ℝ) ^ 2 + 1

/-- The witness split probability `1/2`. -/
noncomputable def failPTrial : ℕ → ℝ := fun _ => 1 / 2

/-- The witness trial cap defined so that the explicit cap holds with equality
up to the ceiling. -/
noncomputable def failRcurve : ℕ → ℕ := fun n =>
  Nat.ceil (Real.exp (((101 : ℝ) / 100) * (Real.log 2 * failK n)) * failLc n)

/-- The witness tree has one node at every scale, including `n = 0`; the `2n`
bound is only required for `1 ≤ n`. -/
def failNodes : ℕ → ℕ := fun _ => 1

/-- The witness failure probability `(1/2) ^ Rcurve / 2`, genuinely positive at
every scale (including `0`). -/
noncomputable def failFailure : ℕ → ℝ := fun n => (1 / 2) ^ (failRcurve n) / 2

theorem failK_nonneg (n : ℕ) : 0 ≤ failK n := by norm_num [failK]

theorem failK_large (n : ℕ) : 1200 ≤ failK n := le_rfl

theorem failLc_ge_one (n : ℕ) : 1 ≤ failLc n := by
  unfold failLc
  nlinarith [sq_nonneg (n : ℝ)]

/-- `scale n ≤ log n` at every `n` with `log n ≥ 1`. -/
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

/-- **The union bound holds at every scale**, including `0`: with `nodes 0 = 1`
the right-hand side is `(1/2) ^ Rcurve 0`, and the failure is half of it. -/
theorem failUnion (n : ℕ) : failFailure n ≤
    (failNodes n : ℝ) * (1 - failPTrial n) ^ (failRcurve n) := by
  have hpos : (0 : ℝ) < (1 / 2) ^ (failRcurve n) := pow_pos (by norm_num) _
  simp only [failNodes, failFailure, failPTrial, Nat.cast_one, one_mul]
  have hbase : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hbase]
  linarith

/-- **The current `FailureData` is inhabited**, with genuinely nonzero data:
`k = 1200`, `pTrial = 1/2`, `Lc = n² + 1`, `nodes = 1`, and the strictly
positive failure `(1/2) ^ Rcurve n / 2`. -/
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

theorem nonempty_failureData : Nonempty FailureData :=
  ⟨failureDataWitness⟩

theorem failureDataWitness_failure_pos (n : ℕ) :
    0 < failureDataWitness.failure n :=
  failFailure_pos n

/-! ## 3. The C5 loss is satisfiable: small data and ledger domination -/

def goodTr (N : ℕ) : PublicMultiFieldTranscript Unit Unit N where
  mask := {()}
  mask_nonempty := ⟨(), by simp⟩
  fields := ∅
  ratCorr := 1
  ratRoot := 1
  ratRoot_sq := by simp
  fieldProd := fun _ => 1
  fieldRoot := fun _ => 1
  fieldRoot_sq := by intro j hj; simp at hj

/-- A concrete epoch with one sample, always-successful solver, and uniform law. -/
noncomputable def goodEpoch (N : ℕ) (hN : N ≠ 0) : ConcreteEpochData N := by
  haveI : NeZero N := ⟨hN⟩
  exact
    { Coins := Unit
      Label := Unit
      FieldId := Unit
      ideal := PMF.uniformOfFintype (Unit × (Unit → (ZMod N)ˣ))
      actual := PMF.uniformOfFintype (Unit × (Unit → (ZMod N)ˣ))
      solver := fun _ _ => some (goodTr N)
      publicCandidates := {some (goodTr N)}
      solver_mem_candidates := by intro x; simp
      candidates_complete := by
        intro t ht hsome
        simp only [Finset.mem_singleton] at ht
        subst ht
        exact ⟨(), fun _ => 1, rfl⟩
      stageCosts :=
        { s0 := fun _ => 0, s1 := fun _ => 0, s2 := fun _ => 0, s3 := fun _ => 0
          s4 := fun _ => 0, s5 := fun _ => 0, s6 := fun _ => 0, s7 := fun _ => 0
          s8 := fun _ => 0, s9 := fun _ => 0 } }


/-- Weight of a uniform PMF on a finite nonempty type. -/
theorem pmfWeight_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    pmfWeight (PMF.uniformOfFintype α) a = (Fintype.card α : ℝ)⁻¹ := by
  unfold pmfWeight
  rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

noncomputable def goodEpochOfLe (n : ℕ) (hN : 3 ≤ n) : ConcreteEpochData n :=
  goodEpoch n (by omega)

theorem goodEpoch_solverSuccess (N : ℕ) (hN : N ≠ 0)
    (x : (goodEpoch N hN).Sample) :
    solverSuccess (goodEpoch N hN) x := by
  simp [solverSuccess, goodEpoch]

theorem goodEpoch_good (N : ℕ) (hN : N ≠ 0) :
    (goodEpoch N hN).good = {some (goodTr N)} := by
  unfold ConcreteEpochData.good goodEpoch
  rw [Finset.filter_singleton]
  rfl

theorem algebraMass_eq_zero_of_all_good {N : ℕ} (D : ConcreteEpochData N)
    [Fintype D.Sample] (hgood : ∀ x : D.Sample, solverSuccess D x) :
    algebraMass D = 0 := by
  classical
  unfold algebraMass goodCount sampleCount goodSamples
  have h : Finset.univ.filter (fun x : D.Sample => solverSuccess D x) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro x _
    exact hgood x
  rw [h]
  simp

theorem goodEpoch_algebraMass (n : ℕ) (hN : 3 ≤ n) :
    @algebraMass n (goodEpochOfLe n hN) (sampleFintype hN (goodEpochOfLe n hN)) = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  exact algebraMass_eq_zero_of_all_good (goodEpochOfLe n hN) (goodEpoch_solverSuccess n (by omega))

theorem goodEpoch_uniform (n : ℕ) (hN : 3 ≤ n)
    (x : Unit × (Unit → (ZMod n)ˣ)) :
    pmfWeight (goodEpochOfLe n hN).ideal x =
      (@Fintype.card (goodEpochOfLe n hN).Sample (sampleFintype hN (goodEpochOfLe n hN)) : ℝ)⁻¹ := by
  haveI : NeZero n := ⟨by omega⟩
  change pmfWeight (PMF.uniformOfFintype (Unit × (Unit → (ZMod n)ˣ))) x =
    (Fintype.card (Unit × (Unit → (ZMod n)ˣ)) : ℝ)⁻¹
  rw [pmfWeight_uniformOfFintype]

theorem goodEpoch_halfMass (n : ℕ) (hN : 3 ≤ n) :
    @HalfMassCount n (goodEpochOfLe n hN) (sampleFintype hN (goodEpochOfLe n hN)) := by
  haveI : NeZero n := ⟨by omega⟩
  exact halfMassCount_of_forall_good (goodEpochOfLe n hN) (goodEpoch_solverSuccess n (by omega))

/-! ## Small C5 data -/

noncomputable def smallPoolInputs (K : ℕ) : PoolCoverageInputs PUnit PUnit PUnit where
  μ := PMF.pure PUnit.unit
  K := K
  dyads := {PUnit.unit}
  dyad := fun _ => {PUnit.unit}
  Z := fun _ _ => 1
  B := fun _ _ => 0
  τ := fun _ => 1
  err_rat := fun _ => 0
  a := 1
  M := 1
  δ_rat := 0
  δ_bad := 0
  θ_rat := 1
  ha := by norm_num
  hM := by norm_num
  hθ_rat := by norm_num
  hτ := by intro d _ p _; norm_num
  hB := by intro d _ p _ _; norm_num
  herr_rat_nn := by intro d _ p _; norm_num
  hsum_rat := by intro d _; simp
  hsum_bad := by intro d _; simp [pmfExpect, pmfWeight]
  hmean := by intro d _ p _ _; simp [pmfExpect, pmfWeight]
  hsecond := by intro d _ p _ _; simp [pmfExpect, pmfWeight]

noncomputable def smallPool (K : ℕ) : PoolCoverageBudget where
  Ω := PUnit
  ι := PUnit
  P := PUnit
  inputs := smallPoolInputs K

theorem smallPool_good (K : ℕ) :
    PoolCoverageInputs.Good (smallPoolInputs K) PUnit.unit = {PUnit.unit} := by
  ext p
  rw [PoolCoverageInputs.Good, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro _
    exact Subsingleton.elim p PUnit.unit
  · intro h
    subst h
    refine ⟨by simp [smallPoolInputs], ?_⟩
    rw [PoolCoverageInputs.Bad, badDyadPrimes]
    intro hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨-, hbad⟩
    rcases hbad with h | h
    · simp [smallPoolInputs] at h
      linarith
    · have herr : PoolCoverageInputs.err_bad (smallPoolInputs K) PUnit.unit = 0 := by
        simp [PoolCoverageInputs.err_bad, pmfExpect, pmfWeight,
          PMF.pure_apply, smallPoolInputs]
      rw [herr] at h
      simp [smallPoolInputs, PoolCoverageInputs.θ_bad] at h
      linarith

theorem smallPool_loss_eq (K : ℕ) :
    (smallPool K).loss = Real.exp (-(K : ℝ) / 16) := by
  have hg : (PoolCoverageInputs.Good (smallPoolInputs K) PUnit.unit).card = 1 := by
    rw [smallPool_good]
    simp
  change (∑ d ∈ ({PUnit.unit} : Finset PUnit),
      ((PoolCoverageInputs.Good (smallPoolInputs K) d).card : ℝ)) *
    Real.exp (-((1 : ℝ) ^ 2 / (16 * 1)) * (K : ℝ)) = Real.exp (-(K : ℝ) / 16)
  rw [Finset.sum_singleton, hg]
  norm_num
  ring_nf

theorem smallPool_loss_le (η : ℝ) (hη : 0 < η) :
    (smallPool (Nat.ceil (16 * Real.log (4 / η)))).loss ≤ η / 4 := by
  rw [smallPool_loss_eq]
  have hK : (16 * Real.log (4 / η) : ℝ) ≤
      (Nat.ceil (16 * Real.log (4 / η)) : ℝ) := Nat.le_ceil _
  have hlog : Real.exp (-(16 * Real.log (4 / η)) / 16) = η / 4 := by
    have hpos : (0 : ℝ) < 4 / η := by positivity
    rw [show -(16 * Real.log (4 / η)) / 16 = -Real.log (4 / η) by ring,
      Real.exp_neg, Real.exp_log hpos]
    field_simp
  calc
    Real.exp (-(Nat.ceil (16 * Real.log (4 / η)) : ℝ) / 16) ≤
        Real.exp (-(16 * Real.log (4 / η)) / 16) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = η / 4 := hlog

noncomputable def smallStage {N : ℕ} (D : ConcreteEpochData N) [Fintype D.Sample]
    (ε : ℝ) (hε : 0 ≤ ε) : StageBudget D where
  ok := fun _ => True
  loss := ε
  loss_nonneg := hε
  fail_le := by
    rw [pmfProb_not_true_eq_zero D.ideal]
    exact hε

noncomputable def smallCoupling {N : ℕ} (D : ConcreteEpochData N) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδpos : 0 < δ) (hbudget : δ ≤ 1 / 1024) : CouplingInputs D where
  ι := Empty
  err := fun i => Empty.elim i
  reach := fun i => Empty.elim i
  fail := fun _ => False
  fail_iff := by intro x; simp
  delta := δ
  delta_nonneg := hδ0
  delta_pos := hδpos
  perCall := by intro i; exact Empty.elim i
  callCap := 1
  callCap_pos := by norm_num
  calls_le := by simp [AdaptiveCallCap]
  budget := by simpa [FirstErrorBudget] using hbudget
  trace_determined := by intro x y _; simp

theorem smallCoupling_loss_eq {N : ℕ} (D : ConcreteEpochData N) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδpos : 0 < δ) (hbudget : δ ≤ 1 / 1024) :
    (smallCoupling D δ hδ0 hδpos hbudget).loss = δ := by
  unfold CouplingInputs.loss smallCoupling
  norm_num

noncomputable def goodC5Data (η : ℕ → ℝ) (hη : ∀ n, 0 < η n) :
    Wave15C5Data (fun n hN => goodEpochOfLe n hN) where
  pool n _ := smallPool (Nat.ceil (16 * Real.log (4 / η n)))
  survivor n hN := by
    letI := sampleFintype hN (goodEpochOfLe n hN)
    exact smallStage (goodEpochOfLe n hN) (η n / 4)
      (div_nonneg (le_of_lt (hη n)) (by norm_num))
  descent n hN := by
    letI := sampleFintype hN (goodEpochOfLe n hN)
    exact smallStage (goodEpochOfLe n hN) (η n / 4)
      (div_nonneg (le_of_lt (hη n)) (by norm_num))
  coupling n hN := by
    letI := sampleFintype hN (goodEpochOfLe n hN)
    exact smallCoupling (goodEpochOfLe n hN) (min (η n / 4) (1 / 2048))
      (le_min (div_nonneg (le_of_lt (hη n)) (by norm_num)) (by norm_num))
      (lt_min (div_pos (hη n) (by norm_num)) (by norm_num))
      (le_trans (min_le_right _ _) (by norm_num))
  huniform n hN x := goodEpoch_uniform n hN x
  hcount n hN := goodEpoch_halfMass n hN
  hcoupling n hN x _ := by
    simp [smallCoupling]

theorem c5TotalLoss_goodC5Data_le (η : ℕ → ℝ) (hη : ∀ n, 0 < η n)
    (n : ℕ) (hN : 3 ≤ n) :
    c5TotalLoss hN (goodEpochOfLe n hN) ((goodC5Data η hη).toC5 n hN) ≤ η n := by
  letI := sampleFintype hN (goodEpochOfLe n hN)
  rw [Wave15C5Data.toC5_totalLoss (C := goodC5Data η hη) n hN]
  have hpool : (smallPool (Nat.ceil (16 * Real.log (4 / η n)))).loss ≤ η n / 4 :=
    smallPool_loss_le (η n) (hη n)
  have hsurv : (smallStage (goodEpochOfLe n hN) (η n / 4)
      (div_nonneg (le_of_lt (hη n)) (by norm_num))).loss ≤ η n / 4 := le_rfl
  have hdesc : (smallStage (goodEpochOfLe n hN) (η n / 4)
      (div_nonneg (le_of_lt (hη n)) (by norm_num))).loss ≤ η n / 4 := le_rfl
  have hcoup : (smallCoupling (goodEpochOfLe n hN) (min (η n / 4) (1 / 2048))
      (le_min (div_nonneg (le_of_lt (hη n)) (by norm_num)) (by norm_num))
      (lt_min (div_pos (hη n) (by norm_num)) (by norm_num))
      (le_trans (min_le_right _ _) (by norm_num))).loss ≤ η n / 4 := by
    rw [smallCoupling_loss_eq]
    exact min_le_left _ _
  have halg : @algebraMass n (goodEpochOfLe n hN)
      (sampleFintype hN (goodEpochOfLe n hN)) = 0 := goodEpoch_algebraMass n hN
  simp only [goodC5Data]
  rw [halg]
  linarith

/-! ## Assembly modulo the analytic leaves -/

theorem wave17Slots_total_pos
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source.{0})
    (l21_2 : Wave17L21_2Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (l4N l4Bits : ℕ) (l4N_odd : Odd l4N) (l4Bits_budget : 2 ^ l4Bits ≤ l4N)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    0 < (wave17Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish
      l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1).total n := by
  rw [wave17Slots_eq, wave15Slots_total_eq]
  have h18 : 0 ≤ l18_4.toInputs.loss n := l18_4.toInputs.loss_nonneg n
  have h19a : 0 ≤ l19.toL19FullCertificate.toL19Inputs.poisson.loss n :=
    l19.toL19FullCertificate.toL19Inputs.poisson.loss_nonneg n
  have h19b : 0 ≤ l19.toL19FullCertificate.toL19Inputs.zeroMode.loss n :=
    l19.toL19FullCertificate.toL19Inputs.zeroMode.loss_nonneg n
  have h19c : 0 ≤ l19.toL19FullCertificate.toL19Inputs.thin.loss n :=
    l19.toL19FullCertificate.toL19Inputs.thin.loss_nonneg n
  have h202 : 0 ≤ (wave14L20_2Leaf l20_2).loss n := (wave14L20_2Leaf l20_2).loss_nonneg n
  have h204 : 0 ≤ l20_4.toSubexpLeaf.loss n := l20_4.toSubexpLeaf.loss_nonneg n
  have h212 : 0 ≤ (wave14L21_2Leaf l21_2.toL21_2LeafData).loss n :=
    (wave14L21_2Leaf l21_2.toL21_2LeafData).loss_nonneg n
  have h27 : 0 ≤ (wave15L27Leaf l27_data l27_finish).loss n :=
    (wave15L27Leaf l27_data l27_finish).loss_nonneg n
  have h30 : 0 < l30.toSubexpLeaf.loss n := by
    change 0 < l30.failure.failure n
    exact l30.failure.failure_pos n
  have h34 : 0 ≤ (wave15L34Leaf l34).loss n := (wave15L34Leaf l34).loss_nonneg n
  have h4 : 0 ≤ (wave15L4Leaf l4N l4Bits l4N_odd l4Bits_budget).loss n :=
    (wave15L4Leaf l4N l4Bits l4N_odd l4Bits_budget).loss_nonneg n
  have hp1 : 0 ≤ (wave14P1Leaf p1).loss n := (wave14P1Leaf p1).loss_nonneg n
  linarith

theorem nonempty_wave17Inputs_of_analytic (D : ℝ)
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source.{0})
    (l21_2 : Wave17L21_2Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (p1 : SubexpPrepassInput)
    (c1 : C1Inputs (fun n hN => (goodEpochOfLe n hN).toHardEpochData))
    (c2 : C2Inputs (fun n hN => (goodEpochOfLe n hN).toHardEpochData))
    (c3 : C3Inputs (fun n hN => (goodEpochOfLe n hN).toHardEpochData))
    (c4 : C4Inputs (fun n hN => (goodEpochOfLe n hN).toHardEpochData) D) :
    Nonempty (Wave17Inputs (fun n hN => (goodEpochOfLe n hN).toHardEpochData) D) := by
  classical
  let ledger : ℕ → ℝ := fun n =>
    (wave17Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish l30 l34
      9 3 (by decide) (by decide) p1).total n
  have hledger_pos : ∀ n, 0 < ledger n := fun n =>
    wave17Slots_total_pos l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish l30 l34
      9 3 (by decide) (by decide) p1 n
  let c5 : Wave15C5Data (fun n hN => goodEpochOfLe n hN) :=
    goodC5Data (fun n => ledger n / 2) (fun n => half_pos (hledger_pos n))
  refine ⟨{
    l18_4 := l18_4
    l19 := l19
    l20_2 := l20_2
    l20_4 := l20_4
    l21_2 := l21_2
    l4N := 9
    l4Bits := 3
    l4N_odd := by decide
    l4Bits_budget := by decide
    l27_data := l27_data
    l27_finish := l27_finish
    l30 := l30
    l34 := l34
    p1 := p1
    c1 := c1
    c2 := c2
    c3 := c3
    c4 := c4
    concrete := fun n hN => goodEpochOfLe n hN
    concrete_eq := fun n hN => rfl
    c5Data := c5
    loss_le := ?_ }⟩
  intro n hN
  have hsmall := c5TotalLoss_goodC5Data_le (fun n => ledger n / 2)
    (fun n => half_pos (hledger_pos n)) n hN
  have hhalf : ledger n / 2 ≤ ledger n := by
    have := hledger_pos n
    linarith
  exact hsmall.trans hhalf


/-! ## 4. The L4 bit-budget fields are proved and inhabited -/

/-- The L4 scalar data carried by `Wave17Inputs`: an odd modulus and a bit
budget inside it. -/
structure L4BudgetWitness where
  N : ℕ
  bits : ℕ
  odd : Odd N
  budget : 2 ^ bits ≤ N

/-- A genuine nonzero witness: `N = 9`, `bits = 3`, `2 ^ 3 = 8 ≤ 9`. -/
def l4BudgetWitness : L4BudgetWitness where
  N := 9
  bits := 3
  odd := by decide
  budget := by decide

theorem l4BudgetWitness_N_pos : 0 < l4BudgetWitness.N := by decide

theorem l4BudgetWitness_bits_pos : 0 < l4BudgetWitness.bits := by decide

theorem l4BudgetWitness_band_pos : 0 < 2 ^ l4BudgetWitness.bits :=
  pow_pos (by norm_num) _

/-- The L4 defect of the witness is the *proved* zero of
`wave15L4Loss_zero`, not a fiat zero. -/
theorem l4BudgetWitness_loss_zero (n : ℕ) :
    wave15L4Loss l4BudgetWitness.N l4BudgetWitness.bits n = 0 :=
  wave15L4Loss_zero l4BudgetWitness.odd l4BudgetWitness.budget n

/-- The L4 leaf of the witness is the proved algebraic leaf. -/
theorem l4BudgetWitness_leaf_loss (n : ℕ) :
    (wave15L4Leaf l4BudgetWitness.N l4BudgetWitness.bits
      l4BudgetWitness.odd l4BudgetWitness.budget).loss n = 0 :=
  wave15L4Leaf_loss _ _ _ _ n

/-! ## 5. The genuine L30 count witness (constant scale `p = 4`) -/

/-- The constant prime scale of the witness. -/
def cnsP : ℕ → ℝ := fun _ => 4

/-- The paper scale `t_p` at the constant scale `p = 4`. -/
noncomputable def cnsT0 : ℝ := Real.sqrt (Real.log 4 * Real.log (Real.log 4))

/-- The relative error that normalises the paper cutoff to `exp ((1+ε)t) = 768`. -/
noncomputable def cnsErr : ℕ → ℝ := fun _ => Real.log 768 / cnsT0 - 1

lemma log_four_gt_one : (1 : ℝ) < Real.log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  nlinarith [Real.log_two_gt_d9]

theorem cnsT0_pos : 0 < cnsT0 := by
  unfold cnsT0
  exact Real.sqrt_pos_of_pos
    (mul_pos (by linarith [log_four_gt_one]) (Real.log_pos log_four_gt_one))

theorem cnsT0_ne_zero : cnsT0 ≠ 0 := cnsT0_pos.ne'

/-- The paper scale at the witness is the constant `cnsT0`. -/
theorem cns_paperT (n : ℕ) : paperT cnsP n = cnsT0 := rfl

/-- The witness normalisation `(1+ε)t = log 768`. -/
theorem cns_one_add_err_mul (n : ℕ) :
    (1 + cnsErr n) * paperT cnsP n = Real.log 768 := by
  rw [cns_paperT]
  unfold cnsErr
  field_simp [cnsT0_ne_zero]
  ring

/-- The paper cutoff at the witness is exactly `768`. -/
theorem cns_cutoff (n : ℕ) : Cogentic.RandomizedL30Analytic.smoothCutoff (paperT cnsP) cnsErr n = 768 := by
  unfold Cogentic.RandomizedL30Analytic.smoothCutoff
  rw [cns_one_add_err_mul, Real.exp_log (by norm_num)]

/-- The exponential factor at the witness is `1/768`. -/
theorem cns_exp_neg (n : ℕ) :
    Real.exp (-(1 + cnsErr n) * paperT cnsP n) = 1 / 768 := by
  rw [show -(1 + cnsErr n) * paperT cnsP n =
      -((1 + cnsErr n) * paperT cnsP n) by ring]
  rw [cns_one_add_err_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]

/-- A number at most `y` is `y`-smooth. -/
lemma smooth_of_le {y : ℝ} {m : ℕ} (hm : (m : ℝ) ≤ y) : IsSmoothUpTo y m := by
  intro q hq
  have hdvd : q ∣ m := Nat.dvd_of_mem_primeFactors hq
  have hmne : m ≠ 0 := (Nat.mem_primeFactors.mp hq).2.2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmne
  have hqm : q ≤ m := Nat.le_of_dvd hmpos hdvd
  have hqmR : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqm
  exact hqmR.trans hm

/-- The odd-half filter is the arithmetic progression `m % 4 = 2`. -/
lemma oddHalf_filter_eq (s : Finset ℕ) :
    s.filter IsOddHalfOrder = s.filter (fun m => m % 4 = 2) := by
  apply Finset.filter_congr
  intro x _
  rfl

/-- The central order interval at `p = 4` is `(12, 16]`. -/
theorem cns_centralInterval (n : ℕ) :
    centralOrderInterval cnsP n = Finset.Icc 12 16 := by
  simp [centralOrderInterval, cnsP]
  norm_num

/-- Every order in the central interval is smooth at the witness cutoff `768`. -/
theorem cns_centralSmooth (n : ℕ) :
    centralSmoothOrders cnsP (paperT cnsP) cnsErr n = Finset.Icc 12 16 := by
  classical
  rw [centralSmoothOrders, cns_centralInterval]
  rw [Finset.filter_true_of_mem]
  intro m hm
  rw [cns_cutoff]
  apply smooth_of_le
  have hm16 : m ≤ 16 := (Finset.mem_Icc.mp hm).2
  have hm16R : (m : ℝ) ≤ 16 := by exact_mod_cast hm16
  linarith

/-- The central odd smooth orders are exactly `{14}`. -/
theorem cns_centralOdd (n : ℕ) :
    centralOddSmoothOrders cnsP (paperT cnsP) cnsErr n = ({14} : Finset ℕ) := by
  classical
  rw [centralOddSmoothOrders, cns_centralSmooth, oddHalf_filter_eq]
  decide

/-- **The central odd count at the witness is the genuine nonzero number `1`.** -/
theorem cns_centralOddCount (n : ℕ) :
    centralOddSmoothCount cnsP (paperT cnsP) cnsErr n = 1 := by
  unfold centralOddSmoothCount
  rw [cns_centralOdd]
  norm_num

/-- The global smooth range up to `p^2 = 16` is the whole interval `[1,16]`. -/
theorem cns_globalSmooth (n : ℕ) :
    globalSmoothOrders cnsP (paperT cnsP) cnsErr n = Finset.Icc 1 16 := by
  classical
  unfold globalSmoothOrders
  rw [show ⌊cnsP n ^ 2⌋₊ = 16 by norm_num [cnsP]]
  rw [Finset.filter_true_of_mem]
  intro m hm
  rw [cns_cutoff]
  apply smooth_of_le
  have hm16 : m ≤ 16 := (Finset.mem_Icc.mp hm).2
  have hm16R : (m : ℝ) ≤ 16 := by exact_mod_cast hm16
  linarith

/-- The global odd-half smooth orders are exactly `{2, 6, 10, 14}`. -/
theorem cns_globalOdd (n : ℕ) :
    globalOddSmoothOrders cnsP (paperT cnsP) cnsErr n =
      ({2, 6, 10, 14} : Finset ℕ) := by
  classical
  rw [globalOddSmoothOrders, cns_globalSmooth, oddHalf_filter_eq]
  decide

/-- **The global odd count at the witness is the genuine nonzero number `4`.** -/
theorem cns_globalOddCount (n : ℕ) :
    globalOddSmoothCount cnsP (paperT cnsP) cnsErr n = 4 := by
  unfold globalOddSmoothCount
  rw [cns_globalOdd]
  norm_num

theorem cns_p_ge_two (n : ℕ) : 2 ≤ cnsP n := by norm_num [cnsP]

theorem cns_err_ge_neg_one (n : ℕ) : -1 ≤ cnsErr n := by
  unfold cnsErr
  have h : 0 ≤ Real.log 768 / cnsT0 :=
    div_nonneg (Real.log_nonneg (by norm_num)) cnsT0_pos.le
  linarith

/-! ## 5b. The explicit `Wave14L30Counts` inhabitant -/

/-- **The repaired `Wave14L30Counts` is inhabited** by the sharp witness of
`RandomizedL30SharpWitness`: the central odd count is `1`, the global odd count
is `4`, and the four constants are `1/4`, `16`, `1/16`, `1/4`. -/
noncomputable def witnessL30Counts : Wave14L30Counts :=
  Cogentic.RandomizedL30SharpWitness.witnessL30Counts

/-- The repaired L30 record is inhabited (with the genuine count witness). -/
theorem nonempty_wave14L30Counts : Nonempty Wave14L30Counts :=
  ⟨witnessL30Counts⟩

/-- The unit Cantor/H.5 cost data.  The cost is the genuine `h5TrialCost` and
the correctness proposition is `True`. -/
noncomputable def witnessCantor : CantorCostInputs :=
  cantorCostInputsOf (fun _ => 0) (fun _ => 1) (fun _ => 1)
    (fun _ => le_rfl) (fun _ => zero_le_one) (fun _ => le_rfl) True trivial

/-! ## 6. The L30 record is inhabited -/

/-- **The full L30 record is inhabited**: the genuine constant-scale count
witness (`p = 4`, central odd count `1`, global odd count `4`), the nonzero unit
Cantor/H.5 cost data, and the explicit `FailureData` witness. -/
noncomputable def wave14L30InputsWitness : Wave14L30Inputs where
  counts := witnessL30Counts
  cantor := witnessCantor
  failure := failureDataWitness

theorem nonempty_wave14L30Inputs : Nonempty Wave14L30Inputs :=
  ⟨wave14L30InputsWitness⟩

/-- The L30 failure probability of the witness is strictly positive. -/
theorem wave14L30InputsWitness_failure_pos (n : ℕ) :
    0 < wave14L30InputsWitness.failure.failure n :=
  failureDataWitness_failure_pos n

/-- The witness keeps the genuine central odd count `1`. -/
theorem wave14L30InputsWitness_centralCount (n : ℕ) :
    centralOddSmoothCount cnsP (paperT cnsP) cnsErr n = 1 :=
  cns_centralOddCount n

/-- The witness keeps the genuine global odd count `4`. -/
theorem wave14L30InputsWitness_globalCount (n : ℕ) :
    globalOddSmoothCount cnsP (paperT cnsP) cnsErr n = 4 :=
  cns_globalOddCount n

/-! ## 7. Non-vacuity of the L21.2 structural data (nonzero profile) -/

/-- The wave-17 L21.2 record with the four genuinely analytic fields and the
two growth/normalization fields removed.  The remaining 19 fields are the
finite Fourier/tent data, the scalar constants, and the two-scale growth
relations; this is the largest part of `Wave17L21_2Inputs` that is not a named
analytic input. -/
structure L21_2StructuralCore where
  profile : TentProfile
  c : ℝ
  Cper : ℝ
  KlineRaw : ℝ
  Ktail : ℝ
  p : ℕ → ℝ
  X_gt_one : ∀ n, 1 < profile.X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  U_ge_three : ∀ n, 3 ≤ bandLog profile.X n
  Cper_ge_three : 3 ≤ Cper
  Kline_raw_nonneg : 0 ≤ KlineRaw
  Ktail_nonneg : 0 ≤ Ktail
  p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < p n
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.lowEnergy n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n)
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.middleEnergy n ≤ Real.exp (-((1 / c) - δ) * paperRate profile.X n)
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n)
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog profile.X n
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog profile.X n ≤ Real.exp (scale n)

/-- The witness log-scale `U n = max 3 (exp (scale n / 2))`. -/
noncomputable def coreU (n : ℕ) : ℝ := max 3 (Real.exp (scale n / 2))

/-- The witness centre bound `X n = exp (U n)`. -/
noncomputable def coreX (n : ℕ) : ℝ := Real.exp (coreU n)

theorem coreU_ge_three (n : ℕ) : 3 ≤ coreU n := le_max_left _ _

theorem coreU_pos (n : ℕ) : 0 < coreU n := lt_of_lt_of_le (by norm_num) (coreU_ge_three n)

/-- The witness profile: one Fourier mode, at frequency `0`, with the nonzero
coefficient `exp (-paperRate X n / 4)`. -/
noncomputable def coreProfile : TentProfile where
  X := coreX
  N := fun _ => 1
  N_pos := fun _ => by norm_num
  coeff := fun n _ => (Real.exp (-(paperRate coreX n / 4)) : ℂ)
  freq := fun _ _ => 0

theorem coreProfile_X (n : ℕ) : coreProfile.X n = coreX n := rfl

theorem bandLog_coreX (n : ℕ) : bandLog coreX n = coreU n := by
  unfold bandLog coreX
  exact Real.log_exp _

theorem coreProfile_lowEnergy (n : ℕ) :
    coreProfile.lowEnergy n = Real.exp (-(paperRate coreX n / 2)) := by
  classical
  letI := coreProfile.neZero n
  unfold TentProfile.lowEnergy TentProfile.lowSet
  have hfilter : (Finset.univ.filter (fun j : ZMod (coreProfile.N n) =>
      |coreProfile.freq n j| ≤ 1)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro j _
    simp [coreProfile]
  rw [hfilter]
  haveI hsub : Subsingleton (ZMod (coreProfile.N n)) := by
    have hN : coreProfile.N n = 1 := rfl
    rw [hN]
    infer_instance
  rw [Finset.sum_eq_single (0 : ZMod (coreProfile.N n))]
  · simp only [coreProfile, Complex.normSq_ofReal]
    rw [← Real.exp_add]
    congr 1
    ring
  · intro b _ hb
    exact absurd (Subsingleton.elim b 0) hb
  · intro h
    exact absurd (Finset.mem_univ (0 : ZMod (coreProfile.N n))) h

theorem coreProfile_middleEnergy (n : ℕ) : coreProfile.middleEnergy n = 0 := by
  classical
  letI := coreProfile.neZero n
  unfold TentProfile.middleEnergy TentProfile.middleSet TentProfile.nonLowSet
  have hempty : (Finset.univ.filter (fun j : ZMod (coreProfile.N n) =>
      ¬ |coreProfile.freq n j| ≤ 1)) = (∅ : Finset (ZMod (coreProfile.N n))) := by
    apply Finset.filter_false_of_mem
    intro j _
    simp [coreProfile]
  rw [hempty]
  simp

theorem coreProfile_tailEnergy (n : ℕ) : coreProfile.tailEnergy n = 0 := by
  classical
  letI := coreProfile.neZero n
  unfold TentProfile.tailEnergy TentProfile.tailSet TentProfile.nonLowSet
  have hempty : (Finset.univ.filter (fun j : ZMod (coreProfile.N n) =>
      ¬ |coreProfile.freq n j| ≤ 1)) = (∅ : Finset (ZMod (coreProfile.N n))) := by
    apply Finset.filter_false_of_mem
    intro j _
    simp [coreProfile]
  rw [hempty]
  simp

/-- The low-band energy is genuinely nonzero. -/
theorem coreProfile_lowEnergy_pos (n : ℕ) : 0 < coreProfile.lowEnergy n := by
  rw [coreProfile_lowEnergy]
  exact Real.exp_pos _

theorem coreU_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ coreU n := by
  intro m hm
  have hε : 0 < 1 / m := by positivity
  have h := Cogentic.RandomizedL20_2.L20_2Inputs.eventually_pow_le_const_mul_exp
    (k := 2) (c := 1 / 2) (ε := 1 / m) (by norm_num) hε
  filter_upwards [h] with n hn
  have hmpos : 0 < m := hm
  have h2 : m * (scale n) ^ 2 ≤ Real.exp (scale n / 2) := by
    have := mul_le_mul_of_nonneg_left hn hmpos.le
    field_simp at this
    linarith
  exact h2.trans (le_max_right _ _)

theorem coreU_le_exp : ∀ᶠ n : ℕ in atTop, coreU n ≤ Real.exp (scale n) := by
  filter_upwards [scale_grows.eventually_ge_atTop (Real.log 3),
    scale_grows.eventually_ge_atTop 0] with n h3 h0
  have h3' : 3 ≤ Real.exp (scale n) := by
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (scale n) := Real.exp_le_exp.mpr h3
  have hhalf : Real.exp (scale n / 2) ≤ Real.exp (scale n) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact max_le h3' hhalf

/-- **The L21.2 structural core is inhabited, with a nonzero profile.**  The
witness has `c = 1/2`, `Cper = 3`, `KlineRaw = Ktail = 1`, `p = 2`, the
one-mode profile `coreProfile`, and `X n = exp (max 3 (exp (scale n / 2)))`.
Its low-band energy is the strictly positive `exp (-paperRate X n / 2)`. -/
noncomputable def coreWitness : L21_2StructuralCore where
  profile := coreProfile
  c := 1 / 2
  Cper := 3
  KlineRaw := 1
  Ktail := 1
  p := fun _ => 2
  X_gt_one := fun n => by
    change 1 < coreX n
    exact Real.one_lt_exp_iff.mpr (coreU_pos n)
  c_pos := by norm_num
  c_le_one := by norm_num
  U_ge_three := fun n => by
    change 3 ≤ bandLog coreX n
    rw [bandLog_coreX]
    exact coreU_ge_three n
  Cper_ge_three := le_rfl
  Kline_raw_nonneg := by norm_num
  Ktail_nonneg := by norm_num
  p_gt_one := Filter.Eventually.of_forall (fun _ => by norm_num)
  fourierLow := by
    intro δ hδ
    refine Filter.Eventually.of_forall ?_
    intro n
    rw [coreProfile_lowEnergy]
    change Real.exp (-(paperRate coreX n / 2)) ≤
      Real.exp (-(((2 * (1 / 2)) / 3) - δ) * paperRate coreX n)
    apply Real.exp_le_exp.mpr
    have hT : 0 ≤ paperRate coreX n := Real.sqrt_nonneg _
    have hcoef : (1 / 3 : ℝ) - δ ≤ 1 / 2 := by linarith
    nlinarith
  fourierMiddle := by
    intro δ hδ
    refine Filter.Eventually.of_forall ?_
    intro n
    rw [coreProfile_middleEnergy]
    exact (Real.exp_pos _).le
  fourierTail := by
    intro δ hδ
    refine Filter.Eventually.of_forall ?_
    intro n
    rw [coreProfile_tailEnergy]
    exact (Real.exp_pos _).le
  U_dominates := fun m hm => by
    filter_upwards [coreU_dominates m hm] with n hn
    change m * scale n ^ 2 ≤ bandLog coreX n
    rw [bandLog_coreX]
    exact hn
  U_le_exp := by
    filter_upwards [coreU_le_exp] with n hn
    change bandLog coreX n ≤ Real.exp (scale n)
    rw [bandLog_coreX]
    exact hn

theorem nonempty_l21_2StructuralCore : Nonempty L21_2StructuralCore :=
  ⟨coreWitness⟩

/-! ## 8. The growing-vs-constant check inside L21.2 -/

/-- **The wave-17 `Ksum_le` is proved**, at the absolute reference constant and
the derived line constant: no field of `Wave17L21_2Inputs` is a growing LHS
against a constant RHS.  This is the theorem `Wave17L21_2Inputs.Ksum_le`,
restated pointwise. -/
theorem wave17_Ksum_le (D : Wave17L21_2Inputs) :
    ∀ᶠ n : ℕ in atTop,
      (fun _ => wave17KrefConst) n + (fun _ => wave17KcontConst) n +
          (fun _ => D.Ktail) n ≤
        (D.Kline / Real.pi) *
          (1 + Real.log (D.profile.X n ^ 3 / perronRe)) :=
  D.Ksum_le

/-- The derived line constant is exactly the advertised maximum of the raw line
constant and `π (Kref + Kcont + Ktail)`. -/
theorem wave17_Kline_eq (D : Wave17L21_2Inputs) : D.Kline =
    max D.KlineRaw (Real.pi *
      (wave17KrefConst + wave17KcontConst + D.Ktail)) :=
  D.Kline_eq

/-- **The wave-16 growing-vs-constant defect, restated as a positive result.**
For every `c ≤ 1` and every `X` with `log X ≥ 3`, the absolute reference
Perron bound holds at the single constant `wave17KrefConst`. -/
theorem wave17_referencePerron_absolute {X : ℕ → ℝ} {c : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hc : c ≤ 1) :
    ReferencePerronBound X c (fun _ => wave17KrefConst) 2 :=
  referencePerronBound_absolute hX hU hc

/-! ## 9. The `lineBound` reduction to the classical input -/

/-- **The classical `ζ'/ζ` line estimate is the named input behind
`lineBound`.**  The reduction `verticalLineBound_of_classicalLogDeriv` gives a
`VerticalLineBound` at exponent `2`; since `log X ≥ 3`, the monomial
`(log X)^2` is at most `(log X)^(Cper-1)` for every `Cper ≥ 3`, so the record's
exponent is reached at the same constant. -/
theorem verticalLineBound_of_classicalLogDeriv_exponent {X : ℕ → ℝ} {Cper : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hC : 3 ≤ Cper)
    (h : ClassicalLogDerivLineBound) :
    ∃ K : ℝ, 0 < K ∧ VerticalLineBound X (fun _ => K) (Cper - 1) := by
  obtain ⟨K, hK, hKb⟩ :=
    Cogentic.RandomizedL21_2LineBound.verticalLineBound_of_classicalLogDeriv hX hU h
  refine ⟨K, hK, ?_⟩
  filter_upwards [hKb] with n hn
  intro u hu
  refine (hn u hu).trans ?_
  have hL1 : 1 ≤ bandLog X n := by linarith [hU n]
  have hL0 : 0 ≤ bandLog X n := by linarith
  have hexp : (bandLog X n) ^ (2 : ℝ) ≤ (bandLog X n) ^ (Cper - 1) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hK0 : 0 ≤ K := le_of_lt hK
  exact mul_le_mul_of_nonneg_left hexp hK0

/-! ## 10. C1/C2 are reduced to the concrete epoch's named data -/

/-- `C1Inputs` for an ambient epoch that is the packaged concrete family: the
named input is `GlobalProductIdentity`. -/
theorem c1Inputs_of_concrete {E : ∀ n, 3 ≤ n → HardEpochData n}
    {concrete : ∀ n, 3 ≤ n → ConcreteEpochData n}
    (hglobal : ∀ n (hN : 3 ≤ n), (concrete n hN).GlobalProductIdentity)
    (heq : ∀ n (hN : 3 ≤ n), E n hN = (concrete n hN).toHardEpochData) :
    C1Inputs E where
  congruenceCheck := fun n hN _ => by
    rw [heq n hN]
    exact (concrete n hN).congruenceCheck (hglobal n hN)

/-- `C2Inputs` for an ambient epoch that is the packaged concrete family: the
named input is `HiddenSignSymmetry`. -/
theorem c2Inputs_of_concrete {E : ∀ n, 3 ≤ n → HardEpochData n}
    {concrete : ∀ n, 3 ≤ n → ConcreteEpochData n}
    (huniform : ∀ n (hN : 3 ≤ n), (concrete n hN).HiddenSignSymmetry)
    (heq : ∀ n (hN : 3 ≤ n), E n hN = (concrete n hN).toHardEpochData) :
    C2Inputs E where
  hiddenUniform := fun n hN _ => by
    rw [heq n hN]
    exact (concrete n hN).hiddenUniform (huniform n hN)



/-! ## 11. The remaining genuinely analytic inputs -/

/-- **The residual analytic content of the wave-17 L21.2 record.**  It is the
conjunction of the six fields that are not theorems and not structural data:

* `hRH` — the Riemann hypothesis for `ζ`;
* `lineBound` — the `ζ'/ζ` line bound at `Re s = 2/3` (reduced to
  `ClassicalLogDerivLineBound` by `verticalLineBound_of_classicalLogDeriv_exponent`);
* `verticalTail` — the vertical tail estimate;
* `localCount` — the literal short-interval smooth count;
* `b_le_B`, `a_ge_log_two` — the two growth relations of the paper parameters.

The remaining fields are *discharged by theorems*: `Ksum_le`
(`Wave17L21_2Inputs.Ksum_le`), `referencePerron`
(`referencePerronBound_absolute`) and `horizontalRemainder`
(`horizontalRemainderBound_of_contourRemainder` composed with the off-pole
strip estimate). -/
structure Wave17L21_2Residual (D : Wave17L21_2Inputs) : Prop where
  /-- `hRH`: the Riemann hypothesis. -/
  rh : RiemannZetaZerosOnLine
  /-- The genuine `ζ'/ζ` line bound at the raw constant. -/
  line : VerticalLineBound D.profile.X (fun _ => D.KlineRaw) (D.Cper - 1)
  /-- The genuine vertical-tail estimate. -/
  tail : VerticalTailBound D.profile.X (fun _ => D.Ktail) (D.Cper - 1)
  /-- The literal short-interval smooth count. -/
  localCount : ShortIntervalSmoothCountLower D.p D.c D.profile.X
  /-- `b ≤ B`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop,
    bOf D.profile.X D.c n ≤ logCutoff D.c D.profile.X n
  /-- `e^a ≥ 2`. -/
  a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf D.profile.X D.c n

/-- **The single theorem listing the remaining genuinely analytic inputs of
the wave-17 L21.2 record.** -/
theorem wave17_l21_2_residual_analytic_inputs (D : Wave17L21_2Inputs) :
    Wave17L21_2Residual D where
  rh := D.hRH
  line := D.lineBound
  tail := D.verticalTail
  localCount := D.localCount
  b_le_B := D.b_le_B
  a_ge_log_two := D.a_ge_log_two

/-- The L21.2 fields that *are* theorems, for contrast with the residual
theorem: the reference-Perron field is the absolute bound, the horizontal field
is the off-pole strip bound, and `Ksum_le` is proved. -/
theorem wave17_l21_2_discharged_fields (D : Wave17L21_2Inputs) :
    ReferencePerronBound D.profile.X D.c (fun _ => wave17KrefConst)
        (D.Cper - 1) ∧
      HorizontalRemainderBound D.profile.X D.c (fun _ => wave17KcontConst)
        (D.Cper - 1) ∧
      (∀ᶠ n : ℕ in atTop,
        (fun _ => wave17KrefConst) n + (fun _ => wave17KcontConst) n +
            (fun _ => D.Ktail) n ≤
          (D.Kline / Real.pi) *
            (1 + Real.log (D.profile.X n ^ 3 / perronRe))) :=
  ⟨D.toL21_2LeafData_referencePerron, D.toL21_2LeafData_horizontalRemainder,
    D.Ksum_le⟩

/-- **The standard one-point epoch family** on which the C5 side is
discharged: uniform ideal law, always-successful solver, so `algebraMass = 0`,
and the small C5 budgets of §3 are available. -/
noncomputable def Egood (n : ℕ) (hN : 3 ≤ n) : HardEpochData n :=
  (goodEpochOfLe n hN).toHardEpochData

/-- **The genuine analytic inputs of the wave-17 record**, for the standard
family `Egood`.  Everything else is proved (the L4 scalar fields) or
constructed (the concrete epoch, the C5 data and the ledger adapter
`loss_le`, by `nonempty_wave17Inputs_of_remaining`). -/
structure Wave17Remaining (D : ℝ) where
  /-- The ten analytic leaf records. -/
  l18_4 : L18_4Certificate
  l19 : Wave15L19Inputs
  l20_2 : SaddleConcentrationSource
  l20_4 : Wave14L20_4Source.{0}
  l21_2 : Wave17L21_2Inputs
  l27_data : L27_1Inputs
  l27_finish : L27StageOneFinishInputs l27_data
  l30 : Wave14L30Inputs
  l34 : L34ChebotarevSidesInputs
  p1 : SubexpPrepassInput
  /-- C1–C4 at the standard family. -/
  c1 : C1Inputs Egood
  c2 : C2Inputs Egood
  c3 : C3Inputs Egood
  c4 : C4Inputs Egood D

/-- **The complete list of remaining genuine inputs of the wave-17 record.**
The L4 scalar data is proved (`l4BudgetWitness`, `N = 9`, `bits = 3`); the
concrete epoch, the C5 data and `loss_le` are constructed. -/
theorem wave17_remaining_inputs {D : ℝ} (R : Wave17Remaining D) :
    Nonempty L18_4Certificate ∧ Nonempty Wave15L19Inputs ∧
      Nonempty SaddleConcentrationSource ∧ Nonempty (Wave14L20_4Source.{0}) ∧
      Nonempty Wave17L21_2Inputs ∧ Nonempty L27_1Inputs ∧
      Nonempty (L27StageOneFinishInputs R.l27_data) ∧
      Nonempty Wave14L30Inputs ∧ Nonempty L34ChebotarevSidesInputs ∧
      Nonempty SubexpPrepassInput ∧ Nonempty (C1Inputs Egood) ∧
      Nonempty (C2Inputs Egood) ∧ Nonempty (C3Inputs Egood) ∧
      Nonempty (C4Inputs Egood D) :=
  ⟨⟨R.l18_4⟩, ⟨R.l19⟩, ⟨R.l20_2⟩, ⟨R.l20_4⟩, ⟨R.l21_2⟩, ⟨R.l27_data⟩,
    ⟨R.l27_finish⟩, ⟨R.l30⟩, ⟨R.l34⟩, ⟨R.p1⟩, ⟨R.c1⟩, ⟨R.c2⟩, ⟨R.c3⟩,
    ⟨R.c4⟩⟩

/-- **The wave-17 record is inhabited modulo exactly the analytic inputs.**
The L4 fields are the proved bit-budget witness, the concrete epoch is the
standard one-point family `Egood`, and the C5 data is the small-budget
construction of §3; `loss_le` is discharged by
`c5TotalLoss_goodC5Data_le`. -/
theorem nonempty_wave17Inputs_of_remaining {D : ℝ} (R : Wave17Remaining D) :
    Nonempty (Wave17Inputs Egood D) :=
  nonempty_wave17Inputs_of_analytic D R.l18_4 R.l19 R.l20_2 R.l20_4 R.l21_2
    R.l27_data R.l27_finish R.l30 R.l34 R.p1 R.c1 R.c2 R.c3 R.c4

/-- The remaining record still carries all six L21.2 residual analytic inputs. -/
theorem wave17_remaining_l21_2_residual {D : ℝ}
    (R : Wave17Remaining D) : Wave17L21_2Residual R.l21_2 :=
  wave17_l21_2_residual_analytic_inputs R.l21_2

/-! ## 11b. The sample-space counting fields are not empty-sample vacuous -/

/-- **The concrete sample space is nonempty.**  `D.Sample = D.Coins × (D.Label →
(ZMod N)ˣ)` and the ideal law is a genuine `PMF`, whose support is nonempty.
Thus the uniform-law field `Wave15C5Data.huniform` and the half-mass count are
not vacuous on an empty sample. -/
theorem sample_card_pos {N : ℕ} [NeZero N] (D : ConcreteEpochData N) :
    0 < Fintype.card D.Sample := by
  obtain ⟨x, _⟩ := D.ideal.support_nonempty
  exact Fintype.card_pos_iff.mpr ⟨x⟩

/-- **The half-mass count is satisfiable with a nonzero count**: if every sample
is good, then at least half are. -/
theorem halfMassCount_of_all_good {N : ℕ} [NeZero N] (D : ConcreteEpochData N)
    (h : ∀ x : D.Sample, solverSuccess D x) : HalfMassCount D :=
  halfMassCount_of_forall_good D h

/-! ## 11c. A nonzero inhabitant of the P1 interface -/

/-- The witness miss probability `exp (-(scale n)^2)`, genuinely positive. -/
noncomputable def p1MissWitness (n : ℕ) : ℝ := Real.exp (-(scale n) ^ 2)

/-- The witness miss probability is strictly positive at every scale. -/
theorem p1MissWitness_pos (n : ℕ) : 0 < p1MissWitness n := Real.exp_pos _

/-- The witness miss probability is `exp (-δ H)` eventually for every `δ > 0`:
the square of the scale eventually dominates every fixed multiple of the
scale. -/
theorem p1MissWitness_success : PrepassSuccess p1MissWitness := by
  intro δ hδ
  filter_upwards [scale_grows.eventually_ge_atTop δ] with n hn
  unfold p1MissWitness
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ scale n := le_trans hδ.le hn
  nlinarith

/-- The witness cost `1`, with the zero subexponential rate.  It is nonzero. -/
noncomputable def p1CostWitness : ℕ → ℝ := fun _ => 1

theorem p1CostWitness_pos (n : ℕ) : 0 < p1CostWitness n := by norm_num [p1CostWitness]

noncomputable def p1CostWitness_rate : SubexpCostRate p1CostWitness where
  eps := fun _ => 0
  eps_nonneg := fun _ => le_rfl
  eps_tendsto := tendsto_const_nhds
  cost_le_exp := by
    refine Filter.Eventually.of_forall ?_
    intro n
    simp [p1CostWitness]

/-- **The P1 interface is inhabited with a nonzero miss probability and a
nonzero cost.**  This witnesses consistency of the interface, not the paper's
asymptotic P1 estimate (which is the analytic input `PrepassSuccess`). -/
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

theorem p1Witness_cost_pos (n : ℕ) : 0 < p1Witness.cost n :=
  p1CostWitness_pos n

/-! ## 12. The compile-checked status table -/

/-- The status table: one pair per field, in declaration order. -/
def wave17StatusTable : List (Wave17Field × FieldStatus) :=
  allWave17Fields.map (fun f => (f, f.status))

theorem wave17StatusTable_length : wave17StatusTable.length = 22 := rfl

/-- The proved fields are exactly the four L4 scalar fields. -/
theorem status_eq_proved_iff (f : Wave17Field) :
    f.status = FieldStatus.proved ↔
      f = .l4N ∨ f = .l4Bits ∨ f = .l4N_odd ∨ f = .l4Bits_budget := by
  cases f <;> simp [Wave17Field.status]

/-- No field is impossible after the C5 repair. -/
theorem status_eq_impossible_iff (f : Wave17Field) :
    f.status = FieldStatus.impossible ↔ False := by
  cases f <;> simp [Wave17Field.status]

/-- The reduced fields are exactly the remaining eighteen. -/
theorem status_eq_reduced_iff (f : Wave17Field) :
    f.status = FieldStatus.reduced ↔
      f ≠ .l4N ∧ f ≠ .l4Bits ∧ f ≠ .l4N_odd ∧ f ≠ .l4Bits_budget := by
  cases f <;> simp [Wave17Field.status]

/-! ## Axiom audit -/

#print axioms nodes_le_two_mul
#print axioms nonempty_failureData
#print axioms failureDataWitness
#print axioms failureDataWitness_failure_pos
#print axioms wave17Slots_total_pos
#print axioms c5TotalLoss_goodC5Data_le
#print axioms nonempty_wave17Inputs_of_analytic
#print axioms algebraMass_eq_zero_of_all_good
#print axioms goodEpoch_uniform
#print axioms goodEpoch_halfMass
#print axioms smallPool_loss_eq
#print axioms smallPool_loss_le
#print axioms smallCoupling_loss_eq
#print axioms l4BudgetWitness
#print axioms l4BudgetWitness_loss_zero
#print axioms cns_centralOddCount
#print axioms cns_globalOddCount
#print axioms witnessL30Counts
#print axioms nonempty_wave14L30Counts
#print axioms witnessCantor
#print axioms wave14L30InputsWitness
#print axioms nonempty_wave14L30Inputs
#print axioms wave14L30InputsWitness_failure_pos
#print axioms coreProfile_lowEnergy
#print axioms coreProfile_lowEnergy_pos
#print axioms coreProfile_middleEnergy
#print axioms coreProfile_tailEnergy
#print axioms coreWitness
#print axioms nonempty_l21_2StructuralCore
#print axioms wave17_Ksum_le
#print axioms wave17_Kline_eq
#print axioms wave17_referencePerron_absolute
#print axioms verticalLineBound_of_classicalLogDeriv_exponent
#print axioms c1Inputs_of_concrete
#print axioms c2Inputs_of_concrete
#print axioms wave17_l21_2_residual_analytic_inputs
#print axioms wave17_l21_2_discharged_fields
#print axioms Egood
#print axioms wave17_remaining_inputs
#print axioms nonempty_wave17Inputs_of_remaining
#print axioms wave17_remaining_l21_2_residual
#print axioms p1MissWitness_success
#print axioms p1CostWitness_rate
#print axioms p1Witness
#print axioms nonempty_subexpPrepassInput
#print axioms sample_card_pos
#print axioms halfMassCount_of_all_good
#print axioms status_eq_proved_iff
#print axioms status_eq_impossible_iff
#print axioms status_eq_reduced_iff

end Cogentic.RandomizedWave17Audit
