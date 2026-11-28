import Cogentic.RandomizedPaperEndpointWave17
import Cogentic.RandomizedWave17Audit
import Cogentic.RandomizedL21_2LineMinimal
import Cogentic.RandomizedL21_2CentralBin
import Cogentic.RandomizedL30LeafFromGRH
import Cogentic.RandomizedL30Sharp
import Cogentic.RandomizedL30UpperDensity
import Cogentic.RandomizedL27LOneSiegel
import Cogentic.RandomizedL34EffectiveChebotarev
import Cogentic.RandomizedL18_4MassGRH
import Cogentic.RandomizedL18_4SieveFinish
import Cogentic.RandomizedP1Prepass

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 18: the honest residual inputs of the paper endpoint

`Cogentic.RandomizedPaperEndpointWave17.Wave17Inputs` is inhabited modulo the
ten analytic leaf records collected in
`Cogentic.RandomizedWave17Audit.Wave17Remaining`.  That record is already much
smaller than the full leaf bundle, but several of its fields are still *bundles*
whose internal analytic content is not visible at the top level.

This file exposes the remaining paper/classical content in **named form**:

* `line : DirichletLZerosOnLine` and `zetaRH : RiemannZetaZerosOnLine` — GRH
  for Dirichlet `L`-functions and its Riemann-zeta specialization used by the
  Perron contour;
* the L21.2 residual: `ZetaLineZeroFree` for the chosen profile, the classical
  `O (log²)` line bound, the literal central short-interval smooth count, the
  vertical-tail estimate, the two paper parameter relations and the full
  Fourier/two-scale profile;
* the L30 residual: the sharp global odd upper density
  `GlobalOddUpperDensitySharp` and the sharp central interval count
  `YounisOddPaperSharpIntervalCount`, both at the true Dickman exponent
  `u log u`, together with the eventual explicit binomial lower bound, the
  Cantor data and the actual H.3 failure data;
* the L27 residual: `SiegelLOneLower` with the class-number formula, Hasse,
  the Waterhouse weighted model, the finite-sum kill law and the curve-budget
  arithmetic;
* the L34 residual: `L34EffectiveChebotarevInputs` (which itself contains the
  Dedekind zero-free region, the `T⁶` height range and Stark's exceptional-zero
  input);
* the L18.4 and L19 certificates;
* `SubexpPrepassInput` and C1–C4.

The main reduction `PaperResidualInputs.toWave17Remaining` assembles the
wave-17 remaining record, and `PaperResidualInputs.nonempty_wave17Inputs`
feeds `nonempty_wave17Inputs_of_remaining`.  The endpoint
`serialized_assembled_balancedEnvelopeInfimum_from_wave18Inputs` is then the
wave-17 endpoint specialized to the standard one-point epoch family and driven
by the residual inputs.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count or
probability is replaced by zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave18

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2LineMinimal
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27ClassNumber
open Cogentic.RandomizedL27Fiber
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27HurwitzAssembly
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27LOneSiegel
open Cogentic.RandomizedL27Scale
open Cogentic.RandomizedL27Siegel
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Stratification
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL27Weighted
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30UpperDensity
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34EffectiveChebotarev
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperEndpointWave17
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver

universe u

/-! ## The named residual inputs -/

/-- **The honest remaining paper/classical inputs of the endpoint.**

Every field is a named analytic or arithmetic hypothesis.  Structural data
(epochs, C5 budgets, the ledger adapter) are *not* fields: they are constructed
by the wave-17 audit. -/
structure PaperResidualInputs (D : ℝ) where
  /-- **GRH for Dirichlet `L`-functions.** -/
  line : DirichletLZerosOnLine
  /-- GRH for the Riemann zeta function, the specialization consumed by the
  L21.2 Perron contour. -/
  zetaRH : RiemannZetaZerosOnLine

  -- L21.2
  /-- The Fourier/tent discrepancy profile. -/
  l21Profile : TentProfile
  /-- The stage-one constant. -/
  l21c : ℝ
  /-- The final Perron exponent. -/
  l21Cper : ℝ
  /-- The given vertical-tail constant. -/
  l21Ktail : ℝ
  /-- The centre sequence of the short-interval count. -/
  l21p : ℕ → ℝ
  /-- The profile is above one at every band. -/
  l21X_gt_one : ∀ n, 1 < l21Profile.X n
  /-- `c > 0`. -/
  l21c_pos : 0 < l21c
  /-- `c ≤ 1`. -/
  l21c_le_one : l21c ≤ 1
  /-- `log X ≥ 3`. -/
  l21U_ge_three : ∀ n, 3 ≤ bandLog l21Profile.X n
  /-- `Cper ≥ 3`. -/
  l21Cper_ge_three : 3 ≤ l21Cper
  /-- The tail constant is nonnegative. -/
  l21Ktail_nonneg : 0 ≤ l21Ktail
  /-- **The open zero-free line input**: `ζ` has no zero on
  `Re s = 2/3`, `|Im s| ≤ 2 X³`. -/
  l21ZeroFree : ZetaLineZeroFree l21Profile.X
  /-- **The classical `O (log²)` line bound** on the same height range. -/
  l21ClassicalLine : ClassicalLogDerivLineBoundOn l21Profile.X
  /-- The genuine vertical-tail estimate at the given constant. -/
  l21VerticalTail : VerticalTailBound l21Profile.X (fun _ => l21Ktail)
    (l21Cper - 1)
  /-- The centre is eventually larger than one. -/
  l21p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < l21p n
  /-- **The literal central short-interval smooth count.** -/
  l21CentralCount : ShortIntervalSmoothCountLower l21p l21c l21Profile.X
  /-- `b ≤ B` for the paper parameters. -/
  l21b_le_B : ∀ᶠ n : ℕ in atTop,
    bOf l21Profile.X l21c n ≤ logCutoff l21c l21Profile.X n
  /-- `e^a ≥ 2`. -/
  l21a_ge_log_two : ∀ᶠ n : ℕ in atTop,
    Real.log 2 ≤ aOf l21Profile.X l21c n
  /-- Low-frequency Fourier energy bound. -/
  l21FourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.lowEnergy n ≤
      Real.exp (-(((2 * l21c) / 3) - δ) * paperRate l21Profile.X n)
  /-- Middle-frequency Fourier energy bound. -/
  l21FourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.middleEnergy n ≤
      Real.exp (-((1 / l21c) - δ) * paperRate l21Profile.X n)
  /-- High-frequency Fourier energy bound. -/
  l21FourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.tailEnergy n ≤ Real.exp (-δ * paperRate l21Profile.X n)
  /-- Two-scale separation. -/
  l21U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog l21Profile.X n
  /-- `log X ≤ exp (scale n)`. -/
  l21U_le_exp : ∀ᶠ n : ℕ in atTop,
    bandLog l21Profile.X n ≤ Real.exp (scale n)

  -- L30
  /-- The prime whose genus-two order is counted. -/
  l30p : ℕ → ℝ
  /-- Paper density growth of `l30p`. -/
  l30Growth : PaperDensityGrowth l30p
  /-- The `1 + o(1)` relative error. -/
  l30ε : ℝ
  /-- `ε > 0`. -/
  l30ε_pos : 0 < l30ε
  /-- The relative short-interval density constant. -/
  l30A : ℝ
  /-- The global smooth lower-bound constant. -/
  l30B : ℝ
  /-- `B > 0`. -/
  l30B_pos : 0 < l30B
  /-- `B ≤ 1/8`. -/
  l30B_le_eighth : l30B ≤ 1 / 8
  /-- `4 ≤ A B`. -/
  l30AB_ge_four : 4 ≤ l30A * l30B
  /-- The paper short-count constant. -/
  l30c : ℝ
  /-- The global odd upper-density constant. -/
  l30C : ℝ
  /-- `A > 0`. -/
  l30A_pos : 0 < l30A
  /-- `32 ≤ A`. -/
  l30A_ge_32 : 32 ≤ l30A
  /-- `A C ≤ c`. -/
  l30AC_le : l30A * l30C ≤ l30c
  /-- `C > 0`. -/
  l30C_pos : 0 < l30C
  /-- **The sharp paper-scale global odd upper density.**  The exponential
  factor is the true Dickman exponent `u log u`, not the unsound
  `exp (-(1+ε)t_p)`. -/
  l30SharpUpper : GlobalOddUpperDensitySharp l30C l30p l30ε
  /-- **The sharp central Younis interval count**, with the same exponent
  `u log u` on the local lower-bound side. -/
  l30SharpCentral : YounisOddPaperSharpIntervalCount l30c l30p l30ε
  /-- **The eventual explicit binomial lower bound.** -/
  l30Binomial : EventuallyGlobalOddBinomialCount l30B l30p
    (paperT l30p) (paperError l30ε)
  /-- The Cantor/H.5 cost and correctness data. -/
  l30Cantor : CantorCostInputs
  /-- The actual H.3 failure data. -/
  l30Failure : FailureData

  -- L27
  /-- The parent ECM data. -/
  l27Data : L27_1Inputs
  /-- The quadratic `L`-value `L(1, χ_D)`. -/
  l27L1 : ℤ → ℝ
  /-- **Siegel's constant lower bound.** -/
  l27Siegel : SiegelLOneLower l27L1
  /-- The Hurwitz class number `H(-D)`. -/
  l27Hurwitz : ℤ → ℝ
  /-- **The Dirichlet class-number formula** and positivity data. -/
  l27ClassNumber : DirichletClassNumberInput l27Hurwitz l27L1
  /-- The nondegeneracy fraction. -/
  l27θ : ℝ
  /-- `θ > 0`. -/
  l27θ_pos : 0 < l27θ
  /-- The Hasse-scale constant is below the Siegel constant at scale `√θ`. -/
  l27KappaLe : l27Data.κ ≤
    (classNumberFormulaConstant * Classical.choose l27Siegel) * Real.sqrt l27θ
  /-- Smooth orders lie in the central trace window. -/
  l27CentralTrace : CentralTraceWindow l27Data.p l27Data.smooth l27θ
  /-- The target prime is prime. -/
  l27Prime : ∀ n, (l27Data.p n).Prime
  /-- **The Waterhouse weighted model count.** -/
  l27WeightedModel : ∀ n,
    WaterhouseWeightedModelCount (l27Data.p n) (l27Prime n) l27Hurwitz
  /-- The order count dominates the raw curve count. -/
  l27OrderDominates : ∀ n j,
    rawCurveOrderCount l27Data.p l27Prime n j ≤ l27Data.orderCount n j
  /-- The `j`-line fibre count. -/
  l27Fiber : JLineFiberInput l27Data.p l27Data.orderCount l27Data.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  l27PGeFour : ∀ n, 4 ≤ l27Data.p n
  /-- **The finite-sum kill law.** -/
  l27KillLaw : L27KillLawInputs l27Data
  /-- **Hasse's theorem.** -/
  l27Hasse : HasseBound l27Data.p l27Data.orderCount
  /-- **The paper's curve-count budget.** -/
  l27CurveBudget : CurveBudget l27Data.p l27Data.y l27Data.psi l27Data.curves
    l27Data.κ l27Data.η
  /-- The L27.2 `log₂` multiplier. -/
  l27LogFactor : LogFactorSubexp l27Data.cofactor

  -- L34
  /-- **The effective Chebotarev input**, including the Dedekind zero-free
  region `zeroFree`, the `T⁶` height range `range` and Stark's
  exceptional-zero input `stark`. -/
  l34 : L34EffectiveChebotarevInputs

  -- L18.4 and L19
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate, with the L19.6 thin slot built from lattice
  data. -/
  l19 : Wave15L19Inputs

  -- L20.2 and L20.4
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source.{0}

  -- P1 and C1–C4
  /-- P1: the explicit `exp (o(H))`-cost prepass. -/
  p1 : SubexpPrepassInput
  /-- C1: the public congruence check. -/
  c1 : C1Inputs Egood
  /-- C2: conditional hidden-sign uniformity. -/
  c2 : C2Inputs Egood
  /-- C3: the ideal/actual total-variation budget. -/
  c3 : C3Inputs Egood
  /-- C4: the expected public-work budget. -/
  c4 : C4Inputs Egood D

/-! ## Reducing the named residuals to the wave-17 leaves -/

namespace PaperResidualInputs

variable {D : ℝ}

/-- The GRH hypothesis for Dirichlet `L`-functions is part of the record (as
the parameter `line`); the Riemann-zeta specialization is the explicit field
`zetaRH`.  The Dirichlet hypothesis also implies the L30 global lower bound
through `eventually_younisOddGlobalLower_paper`. -/
theorem l21_zeroFree_of_minimal (R : PaperResidualInputs D) :
    ZetaLineZeroFree R.l21Profile.X :=
  R.l21ZeroFree

/-- The zero-free line field is also a consequence of the Riemann-zeta GRH
field, so it is not an independent extra assumption. -/
theorem l21_zeroFree_of_zetaRH (R : PaperResidualInputs D) :
    ZetaLineZeroFree R.l21Profile.X :=
  zetaLineZeroFree_of_RH R.zetaRH

/-- The sharp global odd upper density carried by the residual record. -/
theorem l30_globalUpper (R : PaperResidualInputs D) :
    GlobalOddUpperDensitySharp R.l30C R.l30p R.l30ε :=
  R.l30SharpUpper

/-- The sharp central interval count carried by the residual record. -/
theorem l30_sharpCentral (R : PaperResidualInputs D) :
    YounisOddPaperSharpIntervalCount R.l30c R.l30p R.l30ε :=
  R.l30SharpCentral

/-- **The L21.2 leaf from the named residual data.**  The line bound is the
classical `O (log²)` estimate upgraded to the paper exponent `Cper - 1`; the
constant is the positive one produced by
`verticalLineBound_of_classicalLogDerivOn_exponent`, so it is an absolute (not
growing) line constant. -/
noncomputable def toL21_2 (R : PaperResidualInputs D) : Wave17L21_2Inputs :=
  let h := verticalLineBound_of_classicalLogDerivOn_exponent
    (X := R.l21Profile.X) (C := R.l21Cper)
    R.l21X_gt_one R.l21U_ge_three R.l21Cper_ge_three R.l21ClassicalLine
  let K := Classical.choose h
  let hK := Classical.choose_spec h
  { profile := R.l21Profile
    c := R.l21c
    Cper := R.l21Cper
    KlineRaw := K
    Ktail := R.l21Ktail
    p := R.l21p
    X_gt_one := R.l21X_gt_one
    c_pos := R.l21c_pos
    c_le_one := R.l21c_le_one
    U_ge_three := R.l21U_ge_three
    Cper_ge_three := R.l21Cper_ge_three
    Kline_raw_nonneg := hK.1.le
    Ktail_nonneg := R.l21Ktail_nonneg
    hRH := R.zetaRH
    lineBound := hK.2
    verticalTail := R.l21VerticalTail
    p_gt_one := R.l21p_gt_one
    localCount := R.l21CentralCount
    b_le_B := R.l21b_le_B
    a_ge_log_two := R.l21a_ge_log_two
    fourierLow := R.l21FourierLow
    fourierMiddle := R.l21FourierMiddle
    fourierTail := R.l21FourierTail
    U_dominates := R.l21U_dominates
    U_le_exp := R.l21U_le_exp }

/-- **The L30 leaf from the named residual data.**  The global upper density is
the paper-scale smooth upper estimate through the odd-parity inclusion
(`eventuallyGlobalOddUpperDensity_of_paperScaleSmoothUpper`); the global lower
bound is the GRH theorem `eventually_younisOddGlobalLower_paper`; the explicit
binomial bound is the named `l30Binomial`. -/
noncomputable def toL30 (R : PaperResidualInputs D) : Wave14L30Inputs := by
  classical
  let counts : EventuallyL30Counts :=
    EventuallyL30Counts.ofPaperGRHWithB R.line R.l30p R.l30Growth R.l30ε_pos
      R.l30B_pos R.l30B_le_eighth R.l30A R.l30A_pos R.l30AB_ge_four
      R.l30c R.l30C R.l30AC_le R.l30SharpCentral R.l30SharpUpper
  let inputs : EventuallyL30Inputs :=
    { counts := counts, cantor := R.l30Cantor, failure := R.l30Failure }
  exact inputs.toWave14L30Inputs R.l30Binomial

/-- **The L27 stage-one finish bundle from the named residual data.**  The
Siegel constant is the exposed constant `l27l`; the class-number formula, the
Waterhouse weighted model, Hasse's theorem, the kill law and the budget
arithmetic are passed in named form, and
`toAssemblyInputs_of_siegel` performs the reduction to the Hurwitz block. -/
noncomputable def toL27Finish (R : PaperResidualInputs D) :
    L27StageOneFinishInputs R.l27Data :=
  let l := Classical.choose R.l27Siegel
  let hS : SiegelLOneLowerAt R.l27L1 l := Classical.choose_spec R.l27Siegel
  let assembly : L27HurwitzAssemblyInputs R.l27Data :=
    toAssemblyInputs_of_siegel R.l27Hurwitz R.l27L1 R.l27ClassNumber hS
      R.l27θ_pos R.l27KappaLe R.l27CentralTrace R.l27Prime R.l27WeightedModel
      R.l27OrderDominates R.l27Fiber R.l27PGeFour
  { killLaw := R.l27KillLaw
    hurwitz := assembly.toHurwitzInputs
    hasse := R.l27Hasse
    curve_budget := R.l27CurveBudget
    log_factor_subexp := R.l27LogFactor }

/-- The Siegel lower bound, exposed from the named hypothesis. -/
theorem toL27_siegelLower (R : PaperResidualInputs D) :
    SiegelLOneLower R.l27L1 :=
  R.l27Siegel

/-- **The L34 Chebotarev sides from the named effective-Chebotarev input.** -/
noncomputable def toL34 (R : PaperResidualInputs D) :
    L34ChebotarevSidesInputs :=
  R.l34.toL34ChebotarevSidesInputs

/-- The Dedekind classical zero-free region carried by the L34 residual. -/
theorem toL34_zeroFree (R : PaperResidualInputs D) :
    DedekindZeroFreeInput R.l34.beta0 R.l34.zeroRealPart R.l34.cz R.l34.discLog :=
  R.l34.zeroFree

/-- The `T⁶` height range carried by the L34 residual. -/
theorem toL34_range (R : PaperResidualInputs D) :
    ChebotarevT6RangeInput R.l34.K R.l34.T R.l34.degree R.l34.discLog :=
  R.l34.range

/-- Stark's exceptional-zero input carried by the L34 residual. -/
theorem toL34_stark (R : PaperResidualInputs D) :
    StarkExceptionalZeroInput R.l34.beta0 R.l34.F R.l34.discLog :=
  R.l34.stark

/-- **The wave-17 remaining record from the named residual inputs.** -/
noncomputable def toWave17Remaining (R : PaperResidualInputs D) :
    Wave17Remaining D where
  l18_4 := R.l18_4
  l19 := R.l19
  l20_2 := R.l20_2
  l20_4 := R.l20_4
  l21_2 := R.toL21_2
  l27_data := R.l27Data
  l27_finish := R.toL27Finish
  l30 := R.toL30
  l34 := R.toL34
  p1 := R.p1
  c1 := R.c1
  c2 := R.c2
  c3 := R.c3
  c4 := R.c4

/-- **The wave-17 inputs are inhabited from the named residual inputs.** -/
theorem nonempty_wave17Inputs (R : PaperResidualInputs D) :
    Nonempty (Wave17Inputs Egood D) :=
  nonempty_wave17Inputs_of_remaining R.toWave17Remaining

/-- **The direct wave-17 input** obtained from the named residual inputs. -/
noncomputable def toWave17Inputs (R : PaperResidualInputs D) :
    Wave17Inputs Egood D :=
  Classical.choice R.nonempty_wave17Inputs

/-- The L21.2 reduction keeps the profile, the stage-one constant and the
centre sequence, so the loss is not changed. -/
theorem toL21_2_data (R : PaperResidualInputs D) :
    R.toL21_2.profile = R.l21Profile ∧
      R.toL21_2.c = R.l21c ∧ R.toL21_2.p = R.l21p :=
  ⟨rfl, rfl, rfl⟩

end PaperResidualInputs

/-! ## The endpoint -/

/-- The standard one-point epoch family packaged as a schedule-indexed family. -/
noncomputable def EgoodSchedule
    (_s : BalancedRationalSchedule) (n : ℕ) (hN : 3 ≤ n) : HardEpochData n :=
  Egood n hN

/-- **Wave-18 paper endpoint.**  Given, for every balanced-schedule ceiling
`D`, the named residual inputs of `PaperResidualInputs D`, there is one
universal serialized factoring algorithm such that, on the standard one-point
epoch family,

* the kernel-checked driver always outputs a permutation of
  `n.primeFactorsList`;
* the expected serialized bit cost is eventually at most
  `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
  `balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof composes `PaperResidualInputs.nonempty_wave17Inputs` with the
wave-17 endpoint. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave18Inputs
    (R : ∀ D : ℝ, PaperResidualInputs D) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (EgoodSchedule s))
            (fun s => epochAttempt (EgoodSchedule s))) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (EgoodSchedule s))
            (fun s => epochAttempt (EgoodSchedule s))) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ :=
    serialized_assembled_balancedEnvelopeInfimum_from_wave17Inputs (R 0).line
  refine ⟨k, sound, ?_⟩
  have hprovider : ∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
      Wave17Inputs (EgoodSchedule s) D := by
    intro s D _hvalid
    exact Classical.choice (PaperResidualInputs.nonempty_wave17Inputs (R D))
  have h := hmain EgoodSchedule hprovider
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## Axiom audit -/

#print axioms PaperResidualInputs.toL21_2
#print axioms PaperResidualInputs.l21_zeroFree_of_zetaRH
#print axioms PaperResidualInputs.l30_globalUpper
#print axioms PaperResidualInputs.l30_sharpCentral
#print axioms PaperResidualInputs.toL30
#print axioms PaperResidualInputs.toL27Finish
#print axioms PaperResidualInputs.toL34
#print axioms PaperResidualInputs.toWave17Remaining
#print axioms PaperResidualInputs.nonempty_wave17Inputs
#print axioms PaperResidualInputs.toWave17Inputs
#print axioms PaperResidualInputs.toL21_2_data
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave18Inputs

end Cogentic.RandomizedPaperEndpointWave18
