import Cogentic.RandomizedPaperEndpointWave29
import Cogentic.RandomizedL19ConcreteAssembly
import Cogentic.RandomizedL20_2SourceWitness
import Cogentic.RandomizedL20_4SourceWitness
import Cogentic.RandomizedConcreteC1
import Cogentic.RandomizedL30CountsNonvacuous
import Cogentic.RandomizedWave17Audit

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 29: maximal explicit inhabitation and the exact blocker list

`Cogentic.RandomizedPaperEndpointWave29.PaperResidualFor29 E D` is the E-generic
residual record of the paper endpoint.  This file

1. constructs every field that can be constructed from the concrete witnesses
   already in the tree;
2. proves that the remaining fields are *exactly* the analytic residual
   `Wave29Residual`;
3. records which leaf witnesses do **not** apply, and why.

## Constructed without analytic input (at the repaired epoch)

* `l19` — `RandomizedL19ConcreteAssembly.wave15L19Concrete`, with genuinely
  positive Poisson/zero-mode/thin losses;
* `l20_2` — `RandomizedL20_2SourceWitness.source`, with positive loss
  `(1/2) / paperSaddleMass n`;
* `c1` — `concreteEpoch_globalProductIdentity` at the repaired epoch;
* `c2` — the repaired epoch's ideal law is uniform, so `HiddenSignSymmetry` is
  automatic;
* `c3` — the repaired epoch has `ideal = actual` definitionally, so the total
  variation is exactly `0` (an equality, not an estimate);
* `concrete`/`concrete_eq` — the repaired `concreteEpoch` family;
* `c5Data`/`loss_le` — the explicit pool/stage/coupling budgets
  (`repairedEpochC5Data`) at half the ledger, with the domination following
  from `wave29Slots_total_nonneg`;
* `l20_4` — *derived from `l21`*: the only missing field of
  `L20_4SourcedLeafInputs` is an `L21_2Inputs`, and
  `l21.toL21_2LeafData.toAbelInputs.toInputs` supplies it, after which
  `RandomizedL20_4SourceWitness.sourcedLeafOfElliptic` fills the leaf.

## The exact residual

`Wave29Residual E D` has eight fields: `l18_4`, `l21`, `l27_data`,
`l27_finish`, `l30`, `l34`, `p1`, `c4`.  We prove

```
Nonempty (PaperResidualFor29 repairedEpoch D) ↔
  Nonempty (Wave29Residual repairedEpoch D)
```

so the record has no hidden E-side or C5-side obstruction beyond those eight
leaves.

## Blockers and witnesses that do not transport

* `l21.zetaRH` is the Riemann hypothesis for `ζ`; `l21.localCount` is the
  literal central short-interval smooth count.  Neither is constructed here.
* `l30.counts.short_interval` is the sharp Younis interval count and
  `l30.counts.growth` forces the prime scale `p → ∞`.  The existing constant
  witness `p = 4` (`RandomizedL30SharpWitness.witnessL30Counts`) violates
  `PaperDensityGrowth`; this is proved below
  (`not_paperDensityGrowth_sharpWitness`,
  `no_wave26Counts_of_p_four`).  The Cantor and H.3 failure sub-fields *are*
  inhabited (`nonempty_cantorCostInputs`, `nonempty_failureData`).
* `l27_data`/`l27_finish` carry the L27.1 Hurwitz/Siegel/Waterhouse/Deuring,
  Hasse, gcd-exit, curve-budget and `log₂` inputs.  No inhabitant exists in the
  tree.
* `l34` carries the Dedekind zero-free region, the effective Chebotarev
  residual, the `T^6` range and the GRH residual `β₀ ≤ 1/2`; the Stark field is
  derived, but these four are not.
* `p1` carries the H.3 prepass success.  `SubexpPrepassInput` is structurally
  inhabited by the degenerate `miss = 0`/`cost = 1` record, but that changes the
  paper's loss and is **not** used here.
* `c4` is the expected public-work budget.  The repaired C1 epoch charges
  `φ(n)` (the finite root search), and `log n / scale n → ∞`, so this C1 repair
  cannot also supply C4; C4 is left as a residual.  (The corresponding formal
  lower bound on `φ(n)` is not needed for the reduction and is not proved here.)

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss substitution is
used.
-/

noncomputable section

namespace Cogentic.RandomizedWave29Inhabitation

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpoch.ConcreteEpochChecks
open Cogentic.RandomizedConcreteC1
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochTV
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19ConcreteAssembly
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_2SourceWitness
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedP1Sub
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30SharpWitness
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30CountsNonvacuous
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave24
open Cogentic.RandomizedPaperEndpointWave26
open Cogentic.RandomizedPaperEndpointWave27
open Cogentic.RandomizedPaperEndpointWave28
open Cogentic.RandomizedPaperEndpointWave29
open Cogentic.RandomizedWave17Audit
open Cogentic.RandomizedC5GoodIff
open Cogentic.RandomizedC5HitMassFinish

universe u

/-! ## The repaired concrete epoch and its C1/C2/C3 data -/

/-- The repaired concrete epoch family of `RandomizedConcreteC1`, which carries
a genuine square root and therefore satisfies the global product identity. -/
abbrev repairedEpoch : ∀ n, 3 ≤ n → HardEpochData n :=
  Cogentic.RandomizedConcreteC1.concreteEpochFamily

/-- The repaired epoch's C1 input, from `concreteEpoch_globalProductIdentity`. -/
theorem c1_repairedEpoch : C1Inputs repairedEpoch :=
  Cogentic.RandomizedConcreteC1.c1Inputs_concreteEpochFamily

/-- The repaired epoch's ideal law is uniform, so the hidden-sign symmetry is
automatic. -/
theorem repairedEpoch_hiddenSignSymmetry (n : ℕ) (hN : 3 ≤ n) :
    (concreteEpoch n hN).HiddenSignSymmetry := by
  haveI : NeZero n := ⟨by omega⟩
  intro t x y _ _ _ _ _ _
  haveI : Nonempty (concreteEpoch n hN).Sample := ⟨x⟩
  change (concreteEpoch n hN).ideal x = (concreteEpoch n hN).ideal y
  rw [show (concreteEpoch n hN).ideal =
      PMF.uniformOfFintype (concreteEpoch n hN).Sample from rfl]
  rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]

/-- The repaired epoch's C2 input. -/
theorem c2_repairedEpoch : C2Inputs repairedEpoch :=
  Cogentic.RandomizedConcreteEpoch.ConcreteEpochChecks.c2Inputs_concreteEpoch
    concreteEpoch repairedEpoch_hiddenSignSymmetry

/-- The repaired epoch's actual law is definitionally the ideal law, so its
total-variation budget is exactly zero (not an estimate). -/
theorem repairedEpoch_tv_le (n : ℕ) (hN : 3 ≤ n) (_hn : HardInput n) :
    pmfTotalVariation (repairedEpoch n hN).ideal (repairedEpoch n hN).actual ≤ 0 := by
  have h : (repairedEpoch n hN).ideal = (repairedEpoch n hN).actual := rfl
  rw [h]
  exact le_of_eq (pmfTotalVariation_self _)

/-- The repaired epoch's C3 input at `ε = 0`.  This is exact: `ideal = actual`
definitionally. -/
noncomputable def c3_repairedEpoch : C3Inputs repairedEpoch where
  epsilon := fun _ => 0
  epsilon_nonneg := by intro _; norm_num
  epsilon_le := by intro _; norm_num
  tv_le := repairedEpoch_tv_le

/-! ## L20.4 from the L21.2 residual

`L20_4SourcedLeafInputs` is inhabited as soon as one `L21_2Inputs` is supplied
(`RandomizedL20_4SourceWitness.sourcedLeafOfElliptic`).  The Wave-27 L21.2
residual assembles an `L21_2Inputs` through `L21_2LeafData.toAbelInputs`, so the
L20.4 source is *derived* from `l21`, not assumed separately. -/

/-- The literal `L21_2Inputs` assembled from the Wave-27 L21.2 residual. -/
noncomputable def l21InputsOfResidual (l21 : Wave27L21Inputs) : L21_2Inputs :=
  l21.toL21_2LeafData.toAbelInputs.toInputs

/-- The L20.4 sourced leaf built from the L21.2 residual. -/
noncomputable def l20_4OfL21 (l21 : Wave27L21Inputs) : Wave14L20_4Source where
  Ω := Bool
  P := ℕ
  instΩ := inferInstance
  instP := inferInstance
  data := Cogentic.RandomizedL20_4SourceWitness.sourcedLeafOfElliptic
    (l21InputsOfResidual l21)

/-! ## C5 data at the repaired epoch

Everything except the analytic leaf losses is concrete: the pool of
`smallPool`, the two stage budgets `smallStage`, the recognizer coupling
`smallCoupling`, and the uniform/H.8/coupling checks of the repaired epoch. -/

/-- Every sample of the repaired epoch is a solver success (the solver always
returns the one-coordinate root transcript). -/
theorem repairedEpoch_solverSuccess (n : ℕ) (hN : 3 ≤ n)
    (x : (concreteEpoch n hN).Sample) :
    solverSuccess (concreteEpoch n hN) x := by
  haveI : NeZero n := ⟨by omega⟩
  unfold solverSuccess
  simp [concreteEpoch, concreteEpochCore, concreteSolver]

/-- The repaired epoch's ideal law is uniform at the C5 sample instance. -/
theorem repairedEpoch_uniform (n : ℕ) (hN : 3 ≤ n)
    (x : (concreteEpoch n hN).Sample) :
    pmfWeight (concreteEpoch n hN).ideal x =
      (@Fintype.card ((concreteEpoch n hN).Sample)
        (sampleFintype hN (concreteEpoch n hN)) : ℝ)⁻¹ := by
  haveI : NeZero n := ⟨by omega⟩
  dsimp only [ConcreteEpochData.Sample, concreteEpoch, concreteEpochCore] at x ⊢
  change pmfWeight (PMF.uniformOfFintype (Unit × (Unit → (ZMod n)ˣ))) x =
    (Fintype.card (Unit × (Unit → (ZMod n)ˣ)) : ℝ)⁻¹
  rw [pmfWeight_uniformOfFintype]

/-- H.8 half-mass for the repaired epoch: every sample is good. -/
theorem repairedEpoch_halfMass (n : ℕ) (hN : 3 ≤ n) :
    @HalfMassCount n (concreteEpoch n hN) (sampleFintype hN (concreteEpoch n hN)) :=
  @halfMassCount_of_forall_good n (concreteEpoch n hN)
    (sampleFintype hN (concreteEpoch n hN)) (repairedEpoch_solverSuccess n hN)

/-- **The explicit C5 data at the repaired epoch, at budget `η`.** -/
noncomputable def repairedEpochC5Data (η : ℕ → ℝ) (hη : ∀ n, 0 < η n) :
    Wave15C5Data concreteEpoch where
  pool n _ := smallPool (Nat.ceil (16 * Real.log (4 / η n)))
  survivor n hN := by
    letI : Fintype (concreteEpoch n hN).Sample := sampleFintype hN (concreteEpoch n hN)
    exact smallStage (concreteEpoch n hN) (η n / 4)
      (div_nonneg (le_of_lt (hη n)) (by norm_num))
  descent n hN := by
    letI : Fintype (concreteEpoch n hN).Sample := sampleFintype hN (concreteEpoch n hN)
    exact smallStage (concreteEpoch n hN) (η n / 4)
      (div_nonneg (le_of_lt (hη n)) (by norm_num))
  coupling n hN := by
    letI : Fintype (concreteEpoch n hN).Sample := sampleFintype hN (concreteEpoch n hN)
    exact smallCoupling (concreteEpoch n hN) (min (η n / 4) (1 / 2048))
      (le_min (div_nonneg (le_of_lt (hη n)) (by norm_num)) (by norm_num))
      (lt_min (div_pos (hη n) (by norm_num)) (by norm_num))
      (le_trans (min_le_right _ _) (by norm_num))
  huniform n hN x := repairedEpoch_uniform n hN x
  hcount n hN := repairedEpoch_halfMass n hN
  hcoupling n hN x _ := by
    simp [smallCoupling]

/-- The repaired-epoch C5 total loss is at most the chosen budget `η`. -/
theorem repairedEpochC5_totalLoss_le (η : ℕ → ℝ) (hη : ∀ n, 0 < η n)
    (n : ℕ) (hN : 3 ≤ n) :
    c5TotalLoss hN (concreteEpoch n hN) ((repairedEpochC5Data η hη).toC5 n hN) ≤ η n := by
  letI : Fintype (concreteEpoch n hN).Sample := sampleFintype hN (concreteEpoch n hN)
  rw [Wave15C5Data.toC5_totalLoss (C := repairedEpochC5Data η hη) n hN]
  have hpool : (smallPool (Nat.ceil (16 * Real.log (4 / η n)))).loss ≤ η n / 4 :=
    smallPool_loss_le (η n) (hη n)
  have hsurv : (smallStage (concreteEpoch n hN) (η n / 4)
      (div_nonneg (le_of_lt (hη n)) (by norm_num))).loss ≤ η n / 4 := le_rfl
  have hdesc : (smallStage (concreteEpoch n hN) (η n / 4)
      (div_nonneg (le_of_lt (hη n)) (by norm_num))).loss ≤ η n / 4 := le_rfl
  have hcoup : (smallCoupling (concreteEpoch n hN) (min (η n / 4) (1 / 2048))
      (le_min (div_nonneg (le_of_lt (hη n)) (by norm_num)) (by norm_num))
      (lt_min (div_pos (hη n) (by norm_num)) (by norm_num))
      (le_trans (min_le_right _ _) (by norm_num))).loss ≤ η n / 4 := by
    rw [smallCoupling_loss_eq]
    exact min_le_left _ _
  have halg : @algebraMass n (concreteEpoch n hN)
      (sampleFintype hN (concreteEpoch n hN)) = 0 :=
    @algebraMass_eq_zero_of_all_good n (concreteEpoch n hN)
      (sampleFintype hN (concreteEpoch n hN))
      (repairedEpoch_solverSuccess n hN)
  simp only [repairedEpochC5Data]
  rw [halg]
  linarith

/-! ## The combined ledger, term by term -/

/-- **The Wave-29 ledger total is the sum of the twelve genuine leaf losses**
(the L18.4 certificate loss, the three L19 losses, and the eight remaining
leaves).  Nothing is dropped or set to zero. -/
theorem wave29Slots_total_eq
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n =
      l18_4.toInputs.loss n +
        l19.toL19FullCertificate.toL19Inputs.poisson.loss n +
        l19.toL19FullCertificate.toL19Inputs.zeroMode.loss n +
        l19.toL19FullCertificate.toL19Inputs.thin.loss n +
        (wave14L20_2Leaf l20_2).loss n + l20_4.toSubexpLeaf.loss n +
        (wave14L21_2Leaf l21.toL21_2LeafData).loss n +
        (wave15L27Leaf l27_data l27_finish).loss n +
        l30.toSubexpLeaf.loss n +
        (wave15L34Leaf l34.toL34ChebotarevSidesInputs).loss n +
        (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget).loss n +
        (wave14P1Leaf p1).loss n := by
  unfold wave29Slots
  simpa only [wave27Slots] using
    fullyDischargedSlots_total_eq l18_4 l19.toL19FullCertificate
      (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
      (wave14L21_2Leaf l21.toL21_2LeafData)
      (wave15L27Leaf l27_data l27_finish) l30.toSubexpLeaf
      (wave15L34Leaf l34.toL34ChebotarevSidesInputs)
      (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
      (wave14P1Leaf p1) n

/-- The ledger total is nonnegative: every one of its twelve summands is a
genuine nonnegative loss. -/
theorem wave29Slots_total_nonneg
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    0 ≤ (wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n := by
  rw [wave29Slots_total_eq l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 n]
  have h18 : 0 ≤ l18_4.toInputs.loss n := l18_4.toInputs.loss_nonneg n
  have h19a :
      0 ≤ l19.toL19FullCertificate.toL19Inputs.poisson.loss n :=
    l19.toL19FullCertificate.toL19Inputs.poisson.loss_nonneg n
  have h19b :
      0 ≤ l19.toL19FullCertificate.toL19Inputs.zeroMode.loss n :=
    l19.toL19FullCertificate.toL19Inputs.zeroMode.loss_nonneg n
  have h19c :
      0 ≤ l19.toL19FullCertificate.toL19Inputs.thin.loss n :=
    l19.toL19FullCertificate.toL19Inputs.thin.loss_nonneg n
  have h202 : 0 ≤ (wave14L20_2Leaf l20_2).loss n :=
    (wave14L20_2Leaf l20_2).loss_nonneg n
  have h204 : 0 ≤ l20_4.toSubexpLeaf.loss n := l20_4.toSubexpLeaf.loss_nonneg n
  have h212 : 0 ≤ (wave14L21_2Leaf l21.toL21_2LeafData).loss n :=
    (wave14L21_2Leaf l21.toL21_2LeafData).loss_nonneg n
  have h27 : 0 ≤ (wave15L27Leaf l27_data l27_finish).loss n :=
    (wave15L27Leaf l27_data l27_finish).loss_nonneg n
  have h30 : 0 ≤ l30.toSubexpLeaf.loss n := l30.toSubexpLeaf.loss_nonneg n
  have h34 : 0 ≤ (wave15L34Leaf l34.toL34ChebotarevSidesInputs).loss n :=
    (wave15L34Leaf l34.toL34ChebotarevSidesInputs).loss_nonneg n
  have h4 : 0 ≤ (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget).loss n :=
    (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget).loss_nonneg n
  have hp1 : 0 ≤ (wave14P1Leaf p1).loss n := (wave14P1Leaf p1).loss_nonneg n
  linarith

/-- The ledger total is strictly positive: the H.3 failure loss of `l30` is
strictly positive (`FailureData.failure_pos`) while every other summand is
nonnegative. -/
theorem wave29Slots_total_pos
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    0 < (wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1).total n := by
  rw [wave29Slots_total_eq l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 n]
  have h18 : 0 ≤ l18_4.toInputs.loss n := l18_4.toInputs.loss_nonneg n
  have h19a :
      0 ≤ l19.toL19FullCertificate.toL19Inputs.poisson.loss n :=
    l19.toL19FullCertificate.toL19Inputs.poisson.loss_nonneg n
  have h19b :
      0 ≤ l19.toL19FullCertificate.toL19Inputs.zeroMode.loss n :=
    l19.toL19FullCertificate.toL19Inputs.zeroMode.loss_nonneg n
  have h19c :
      0 ≤ l19.toL19FullCertificate.toL19Inputs.thin.loss n :=
    l19.toL19FullCertificate.toL19Inputs.thin.loss_nonneg n
  have h202 : 0 ≤ (wave14L20_2Leaf l20_2).loss n :=
    (wave14L20_2Leaf l20_2).loss_nonneg n
  have h204 : 0 ≤ l20_4.toSubexpLeaf.loss n := l20_4.toSubexpLeaf.loss_nonneg n
  have h212 : 0 ≤ (wave14L21_2Leaf l21.toL21_2LeafData).loss n :=
    (wave14L21_2Leaf l21.toL21_2LeafData).loss_nonneg n
  have h27 : 0 ≤ (wave15L27Leaf l27_data l27_finish).loss n :=
    (wave15L27Leaf l27_data l27_finish).loss_nonneg n
  have h30 : 0 < l30.toSubexpLeaf.loss n := by
    change 0 < l30.failure.failure n
    exact l30.failure.failure_pos n
  have h34 : 0 ≤ (wave15L34Leaf l34.toL34ChebotarevSidesInputs).loss n :=
    (wave15L34Leaf l34.toL34ChebotarevSidesInputs).loss_nonneg n
  have h4 : 0 ≤ (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget).loss n :=
    (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget).loss_nonneg n
  have hp1 : 0 ≤ (wave14P1Leaf p1).loss n := (wave14P1Leaf p1).loss_nonneg n
  linarith

/-! ## The residual record -/

/-- **The genuinely analytic residual of the Wave-29 record.**

Everything *outside* these fields is constructed in this file at the repaired
epoch:

* `l19` is `RandomizedL19ConcreteAssembly.wave15L19Concrete`;
* `l20_2` is `RandomizedL20_2SourceWitness.source`;
* `l20_4` is derived from `l21` by `RandomizedL20_4SourceWitness`;
* `c1`, `c2`, `c3` are the repaired epoch's congruence check, hidden-sign
  uniformity and exact `ε = 0` total-variation budget;
* `concrete`/`concrete_eq` are `concreteEpoch`/`rfl`;
* `c5Data` and `loss_le` are built from the ledger by
  `repairedEpochC5Data`.

The fields below are the blockers.  In particular `l21.zetaRH` is the Riemann
hypothesis, `l21.localCount` and `l30.counts.short_interval` are the two literal
Younis/L21.2 counting leaves, `l27_data`/`l27_finish` carry the Hurwitz/Siegel/
Waterhouse/Deuring block, `l34` the Dedekind zero-free region and effective
Chebotarev input, `p1` the H.3 prepass success, and `c4` the expected public-work
budget. -/
structure Wave29Residual (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- L21.2: the Riemann hypothesis and the central short-interval smooth count. -/
  l21 : Wave27L21Inputs
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- L30 with both density fields derived. -/
  l30 : Wave26L30Inputs
  /-- L34 with the Stark field derived. -/
  l34 : Wave28L34Inputs
  /-- P1: the explicit prepass. -/
  p1 : SubexpPrepassInput
  /-- C4: the expected public-work budget. -/
  c4 : C4Inputs E D

namespace Wave29Residual

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The reduction: the residual record fills the whole Wave-29 record at the
repaired epoch.**  The L20.4 source is derived from `l21` (its only missing
field is an `L21_2Inputs`, which `l21.toL21_2LeafData` supplies); the C5 data is
`repairedEpochC5Data` at half the ledger, so the domination `loss_le` follows
from the nonnegativity of the ledger. -/
noncomputable def toPaperResidualFor29 (R : Wave29Residual repairedEpoch D) :
    PaperResidualFor29 repairedEpoch D := by
  let ledger : ℕ → ℝ := fun n =>
    (wave29Slots R.l18_4 Cogentic.RandomizedL19ConcreteAssembly.wave15L19Concrete
      Cogentic.RandomizedL20_2SourceWitness.source (l20_4OfL21 R.l21) R.l21
      R.l27_data R.l27_finish R.l30 R.l34 R.p1).total n
  have hledger : ∀ n, 0 < ledger n := fun n =>
    wave29Slots_total_pos R.l18_4
      Cogentic.RandomizedL19ConcreteAssembly.wave15L19Concrete
      Cogentic.RandomizedL20_2SourceWitness.source (l20_4OfL21 R.l21) R.l21
      R.l27_data R.l27_finish R.l30 R.l34 R.p1 n
  refine
    { l18_4 := R.l18_4
      l19 := Cogentic.RandomizedL19ConcreteAssembly.wave15L19Concrete
      l20_2 := Cogentic.RandomizedL20_2SourceWitness.source
      l20_4 := l20_4OfL21 R.l21
      l21 := R.l21
      l27_data := R.l27_data
      l27_finish := R.l27_finish
      l30 := R.l30
      l34 := R.l34
      p1 := R.p1
      c1 := c1_repairedEpoch
      c2 := c2_repairedEpoch
      c3 := c3_repairedEpoch
      c4 := R.c4
      concrete := concreteEpoch
      concrete_eq := fun _ _ => rfl
      c5Data := repairedEpochC5Data (fun n => ledger n / 2)
        (fun n => half_pos (hledger n))
      loss_le := ?_ }
  intro n hN
  have hle := repairedEpochC5_totalLoss_le (fun m => ledger m / 2)
    (fun m => half_pos (hledger m)) n hN
  have hhalf : ledger n / 2 ≤ ledger n := by linarith [hledger n]
  exact hle.trans (by simpa only [ledger] using hhalf)

end Wave29Residual

/-- **The exact status of `PaperResidualFor29` at the repaired epoch.**  A full
inhabitant exists if and only if the eight residual leaves exist.  The forward
direction simply projects the fields; the backward direction is
`Wave29Residual.toPaperResidualFor29`. -/
theorem nonempty_paperResidualFor29_iff (D : ℝ) :
    Nonempty (PaperResidualFor29 repairedEpoch D) ↔
      Nonempty (Wave29Residual repairedEpoch D) := by
  constructor
  · rintro ⟨I⟩
    exact ⟨{ l18_4 := I.l18_4, l21 := I.l21, l27_data := I.l27_data
             l27_finish := I.l27_finish, l30 := I.l30, l34 := I.l34,
             p1 := I.p1, c4 := I.c4 }⟩
  · rintro ⟨R⟩
    exact ⟨R.toPaperResidualFor29⟩

/-! ## The unconditionally inhabited part -/

/-- **The part of the Wave-29 record that is constructed with no analytic
residual**: the L19 certificate, the L20.2 source, and C1/C2/C3 at the repaired
epoch.  (`l20_4`, `c5Data` and `loss_le` additionally need `l21` and the ledger,
and are handled in `Wave29Residual.toPaperResidualFor29`.) -/
structure Wave29ExplicitPart where
  /-- L19.4–L19.6, the concrete assembly at the common scale. -/
  l19 : Wave15L19Inputs
  /-- L20.2, the paper-mass concentration source. -/
  l20_2 : SaddleConcentrationSource
  /-- C1 at the repaired epoch. -/
  c1 : C1Inputs repairedEpoch
  /-- C2 at the repaired epoch. -/
  c2 : C2Inputs repairedEpoch
  /-- C3 at the repaired epoch (`ε = 0`). -/
  c3 : C3Inputs repairedEpoch

/-- The explicit part, with every field a concrete witness. -/
noncomputable def explicitPart : Wave29ExplicitPart where
  l19 := Cogentic.RandomizedL19ConcreteAssembly.wave15L19Concrete
  l20_2 := Cogentic.RandomizedL20_2SourceWitness.source
  c1 := c1_repairedEpoch
  c2 := c2_repairedEpoch
  c3 := c3_repairedEpoch

/-- **The explicit part is inhabited.** -/
theorem nonempty_explicitPart : Nonempty Wave29ExplicitPart :=
  ⟨explicitPart⟩

/-- The L20.4 source is inhabited as soon as the L21.2 residual is; this is the
exact content of `RandomizedL20_4SourceWitness` fed by
`l21.toL21_2LeafData.toAbelInputs.toInputs`. -/
theorem nonempty_l20_4_of_l21 (l21 : Wave27L21Inputs) :
    Nonempty Wave14L20_4Source.{0} :=
  ⟨l20_4OfL21 l21⟩

/-! ## Exact blocker extractors -/

section Blockers

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- The record forces the Riemann hypothesis for `ζ`. -/
theorem zetaRH_of_record (I : PaperResidualFor29 E D) : RiemannZetaZerosOnLine :=
  I.l21.zetaRH

/-- The record forces the literal L21.2 central short-interval smooth count. -/
theorem localCount_of_record (I : PaperResidualFor29 E D) :
    ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  I.l21.localCount

/-- The record forces the sharp L30 central interval count. -/
theorem l30_shortInterval_of_record (I : PaperResidualFor29 E D) :
    YounisOddPaperSharpIntervalCount I.l30.counts.c I.l30.counts.p
      I.l30.counts.ε :=
  I.l30.counts.short_interval

/-- The record forces the paper density growth `p → ∞`. -/
theorem l30_growth_of_record (I : PaperResidualFor29 E D) :
    PaperDensityGrowth I.l30.counts.p :=
  I.l30.counts.growth

/-- The record forces the Dedekind zero-free region of L34. -/
theorem l34_zeroFree_of_record (I : PaperResidualFor29 E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz
      I.l34.discLog :=
  I.l34.zeroFree

/-- The record forces the effective Chebotarev residual of L34. -/
theorem l34_cheb_of_record (I : PaperResidualFor29 E D) :
    ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
      I.l34.count I.l34.liX I.l34.liBeta0 :=
  I.l34.cheb

/-- The record forces the `T^6` range of L34. -/
theorem l34_range_of_record (I : PaperResidualFor29 E D) :
    ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog :=
  I.l34.range

/-- The record forces the GRH residual `β₀ ≤ 1/2` of L34. -/
theorem l34_beta0_half_of_record (I : PaperResidualFor29 E D) :
    ∀ n, I.l34.beta0 n ≤ 1 / 2 :=
  I.l34.beta0_le_half

/-- The record forces the Hurwitz/Siegel/Waterhouse block of L27.1. -/
theorem l27_hurwitz_of_record (I : PaperResidualFor29 E D) :
    Nonempty (L27HurwitzInputs I.l27_data) :=
  ⟨I.l27_finish.hurwitz⟩

/-- The record forces Hasse's theorem for the L27.1 curve counts. -/
theorem l27_hasse_of_record (I : PaperResidualFor29 E D) :
    HasseBound I.l27_data.p I.l27_data.orderCount :=
  I.l27_finish.hasse

/-- The record forces the full L18.4 certificate, in particular its large-sieve
and numerator-support data. -/
theorem l18_4_of_record (I : PaperResidualFor29 E D) :
    Nonempty L18_4Certificate :=
  ⟨I.l18_4⟩

/-- The record forces the P1 success statement. -/
theorem p1_success_of_record (I : PaperResidualFor29 E D) :
    PrepassSuccess I.p1.miss :=
  I.p1.success

/-- The record forces the C4 expected-work budget. -/
theorem c4_of_record (I : PaperResidualFor29 E D) : C4Inputs E D :=
  I.c4

end Blockers

/-! ## Why the concrete L30 witness does not discharge `l30`

The explicit `Wave14L30Counts` witness is at the *constant* prime scale `p = 4`.
`Wave26L30Counts` requires `PaperDensityGrowth p`, which forces `p → ∞`; the
constant witness therefore cannot be substituted.  This is the precise reason
the sharp-count non-vacuity result does not close the Wave-29 L30 leaf. -/

theorem not_paperDensityGrowth_const_four :
    ¬ PaperDensityGrowth (fun _ : ℕ => (4 : ℝ)) := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h.1
  have h4 := hN N le_rfl
  norm_num at h4

/-- The constant sharp-count witness does not satisfy the Wave-26 growth
hypothesis. -/
theorem not_paperDensityGrowth_sharpWitness :
    ¬ PaperDensityGrowth
      (Cogentic.RandomizedL30SharpWitness.witnessL30Counts.p) := by
  change ¬ PaperDensityGrowth (fun _ : ℕ => (4 : ℝ))
  exact not_paperDensityGrowth_const_four

/-- **No `Wave26L30Counts` can use the constant `p = 4` witness.** -/
theorem no_wave26Counts_of_p_four (S : Wave26L30Counts)
    (hp : S.p = Cogentic.RandomizedL30SharpWitness.witnessL30Counts.p) : False := by
  have hg : PaperDensityGrowth S.p := S.growth
  rw [hp] at hg
  exact not_paperDensityGrowth_sharpWitness hg

/-! ## The non-counting L30 sub-fields are inhabited -/

/-- The Cantor/H.5 cost data is inhabited. -/
theorem nonempty_cantorCostInputs : Nonempty CantorCostInputs :=
  ⟨Cogentic.RandomizedL30CountsNonvacuous.witnessCantor⟩

/-- The H.3 failure data is inhabited (with strictly positive failure). -/
theorem nonempty_failureData : Nonempty FailureData :=
  Cogentic.RandomizedL30CountsNonvacuous.nonempty_failureData

/-! ## Residual accounting -/

/-- The exact Wave-29 blocker list.  Every entry is a field of the residual
record (or of one of its leaves) that is not constructed in this file. -/
def wave29BlockerFields : List String :=
  ["l18_4.largeSieve", "l18_4.mass", "l18_4.thinData",
   "l21.zetaRH", "l21.localCount",
   "l27_data.deuring_count", "l27_data.gcd_exit", "l27_data.curve_budget",
   "l27_data.logFactor_subexp", "l27_finish.killLaw", "l27_finish.hurwitz",
   "l30.counts.short_interval", "l30.counts.growth",
   "l34.zeroFree", "l34.cheb", "l34.range", "l34.beta0_le_half",
   "p1.success", "c4.work_le"]

theorem wave29BlockerFields_length : wave29BlockerFields.length = 19 := rfl

/-- The blockers form a nonempty list. -/
theorem wave29BlockerFields_ne_nil : wave29BlockerFields ≠ [] := by
  simp [wave29BlockerFields]

/-! ## Axiom audit -/

#print axioms c1_repairedEpoch
#print axioms c2_repairedEpoch
#print axioms c3_repairedEpoch
#print axioms l21InputsOfResidual
#print axioms l20_4OfL21
#print axioms repairedEpoch_uniform
#print axioms repairedEpoch_halfMass
#print axioms repairedEpochC5Data
#print axioms repairedEpochC5_totalLoss_le
#print axioms wave29Slots_total_eq
#print axioms wave29Slots_total_nonneg
#print axioms wave29Slots_total_pos
#print axioms Wave29Residual.toPaperResidualFor29
#print axioms nonempty_paperResidualFor29_iff
#print axioms explicitPart
#print axioms nonempty_explicitPart
#print axioms nonempty_l20_4_of_l21
#print axioms zetaRH_of_record
#print axioms l30_shortInterval_of_record
#print axioms l34_zeroFree_of_record
#print axioms l27_hurwitz_of_record
#print axioms not_paperDensityGrowth_const_four
#print axioms not_paperDensityGrowth_sharpWitness
#print axioms no_wave26Counts_of_p_four
#print axioms nonempty_cantorCostInputs
#print axioms nonempty_failureData
#print axioms wave29BlockerFields_length

end Cogentic.RandomizedWave29Inhabitation
