import Cogentic.RandomizedPaperEndpointWave18
import Cogentic.RandomizedL21_2ConcreteLeaf
import Cogentic.RandomizedWave18Audit

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 21: the L21.2 block of the paper endpoint from the concrete leaf

`Cogentic.RandomizedPaperEndpointWave18.PaperResidualInputs` carries the L21.2
analytic content as an explicit **24-field block** (`zetaRH` together with the
23 `l21*` fields), preceded by the global Dirichlet-GRH field `line`.  Every
one of the 24 L21.2 fields is an independent hypothesis:

* the concrete tent profile `l21Profile`, the constants `l21c`, `l21Cper`,
  `l21Ktail`, the centre `l21p` and their structural bounds;
* `l21ZeroFree`, `l21ClassicalLine` and `l21VerticalTail`;
* the literal central count `l21CentralCount`;
* the two paper parameter relations `l21b_le_B`, `l21a_ge_log_two`;
* the three Fourier bounds and the two two-scale relations.

`Cogentic.RandomizedL21_2ConcreteLeaf` proves all of them *except* the zeta-side
input and the literal count, and packages those two remaining pieces as the
two-field structure `ConcreteLeafResidual` (a `ZetaSide` together with a
`ShortIntervalSmoothCountLower`).  Its assembled record is
`wave17InputsOfResidual : ConcreteLeafResidual → Wave17L21_2Inputs`.

This file defines the variant

```
structure PaperResidualInputsL21 (D : ℝ) where
  line : DirichletLZerosOnLine
  l21  : ConcreteLeafResidual
  -- the L30, L27, L34, L18.4, L19, L20, P1 and C1–C4 fields, unchanged
```

and proves `PaperResidualInputsL21 D → PaperResidualInputs D` by *using*
`wave17InputsOfResidual` for the concrete L21.2 data.  Concretely:

* `R.toL21_2 := wave17InputsOfResidual R.l21` is the wave-17 record produced by
  the residual;
* `R.toPaperResidualInputs` transports every L21.2 field from `R.toL21_2`;
* the only two fields of `PaperResidualInputs` that the wave-17 record does not
  contain are `l21ZeroFree` (taken from the `ZetaSide`) and
  `l21ClassicalLine`, which is *derived* from the same `ZetaSide` by
  `classicalLogDerivLineBoundOn_of_zetaSide` (the two-sided estimate plus the
  eventual `B / b` ratio bound give the range-local `O (log²)` statement).

Nothing is copied: the 24 concrete L21.2 fields disappear as hypotheses and are
replaced by the two components of `ConcreteLeafResidual`.

## Field count

`PaperResidualInputs` has 73 fields.  Its first 25 fields are the pre-L30 block
`line`, `zetaRH`, and the 23 `l21*` fields.  Of these, the 24 L21.2-specific
fields `zetaRH` plus the 23 `l21*` fields are replaced by the single field
`l21 : ConcreteLeafResidual`.  The Dirichlet-GRH field `line` is not part of
`ConcreteLeafResidual` (which only contains zeta-side data) and is consumed
outside L21.2 by `PaperResidualInputs.toL30` and by the endpoint, so it remains
an explicit field.  Hence

```
PaperResidualInputsL21 : 1 (line) + 1 (l21) + 48 (unchanged) = 50 fields.
```

## Data equality versus the exact adapter

The `Wave17L21_2Inputs` produced by the residual is **not** definitionally the
one produced by `PaperResidualInputs.toL21_2` on the transported record: the
latter derives the line constant by `Classical.choose` from the classical
`O (log²)` bound, whereas the residual route uses the zeta-side
`ZetaLineEstimate` directly with constant `ZetaSide.KlineRaw`.  The records do
agree definitionally on all loss/structural data (`profile`, `c`, `Cper`,
`Ktail`, `p`).  `toPaperResidualInputs_toL21_2_adapter` states this exact
adapter; `toPaperResidualInputs_toL21_2_data` records the definitional part.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count or
probability is replaced by zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave21

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
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2LineMinimal
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2TailBound
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
open Cogentic.RandomizedPaperEndpointWave18
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit
open Cogentic.RandomizedWave18Audit
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver

universe u

/-! ## The variant with the L21.2 block collapsed to `ConcreteLeafResidual` -/

/-- **The Wave-21 residual inputs: the concrete leaf replaces the whole L21.2
block.**

The 24 L21.2-specific fields of
`Cogentic.RandomizedPaperEndpointWave18.PaperResidualInputs` (`zetaRH` and the
23 `l21*` fields: concrete profile, `c`, `Cper`, `Ktail`, `p`, the structural
bounds, `ZeroFree`, `ClassicalLine`, the vertical tail, the central count, the
`b`/`a` relations, the three Fourier bounds and the two two-scale relations)
are replaced by the single two-component residual
`l21 : ConcreteLeafResidual` of `RandomizedL21_2ConcreteLeaf`.

The Dirichlet-GRH field `line` is retained: it is a global hypothesis consumed
by the L30 reduction and by the endpoint, and it is not contained in the
zeta-side `ConcreteLeafResidual`.  Every field after the L21.2 block is copied
verbatim from `PaperResidualInputs`. -/
structure PaperResidualInputsL21 (D : ℝ) where
  /-- **GRH for Dirichlet `L`-functions.** -/
  line : DirichletLZerosOnLine
  /-- **The whole L21.2 analytic input**: the zeta side (RH, zero-freeness on
  `Re s = 2/3`, and the two-sided line estimate with a raw constant) together
  with the literal central short-interval smooth count.  Everything else in the
  former L21.2 block is proved from these two components by
  `wave17InputsOfResidual`. -/
  l21 : ConcreteLeafResidual

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

namespace PaperResidualInputsL21

variable {D : ℝ}

/-! ## The wave-17 L21.2 record from the residual -/

/-- **The L21.2 leaf produced by the residual.**  This is exactly
`wave17InputsOfResidual R.l21`: every numerical, structural and two-scale field
is a theorem of `RandomizedL21_2ConcreteLeaf`, and the line/tail constants are
the ones supplied by `ConcreteLeafResidual`. -/
noncomputable abbrev toL21_2 (R : PaperResidualInputsL21 D) : Wave17L21_2Inputs :=
  wave17InputsOfResidual R.l21

/-- The leaf keeps the concrete elementary profile. -/
theorem toL21_2_profile (R : PaperResidualInputsL21 D) :
    R.toL21_2.profile = elementaryProfile :=
  wave17InputsOfResidual_profile R.l21

/-- The leaf keeps the elementary stage-one constant. -/
theorem toL21_2_c (R : PaperResidualInputsL21 D) :
    R.toL21_2.c = elementaryC := by
  simpa only [toL21_2] using wave17InputsOfResidual_c R.l21

/-- The leaf keeps the elementary Perron exponent. -/
theorem toL21_2_Cper (R : PaperResidualInputsL21 D) :
    R.toL21_2.Cper = elementaryCper := by
  simpa only [toL21_2] using wave17InputsOfResidual_Cper R.l21

/-- The leaf keeps the elementary centre sequence `p = X`. -/
theorem toL21_2_p (R : PaperResidualInputsL21 D) :
    R.toL21_2.p = elementaryX := by
  simpa only [toL21_2] using wave17InputsOfResidual_p R.l21

/-- The stored vertical-tail constant of the leaf. -/
theorem toL21_2_Ktail (R : PaperResidualInputsL21 D) :
    R.toL21_2.Ktail = tailK / Real.pi := by
  simpa only [toL21_2] using wave17InputsOfResidual_Ktail R.l21

/-- The wave-17 record is inhabited, via `residualProp_to_wave17Inputs`. -/
theorem nonempty_toL21_2 (R : PaperResidualInputsL21 D) :
    Nonempty Wave17L21_2Inputs :=
  residual_to_wave17Inputs R.l21

/-! ## Transport to the Wave-18 residual record -/

/-- **`PaperResidualInputsL21 → PaperResidualInputs`.**

Every L21.2 field is transported from `R.toL21_2 = wave17InputsOfResidual
R.l21`.  The two fields absent from the wave-17 record are supplied by the
same residual: `l21ZeroFree` is the `ZetaSide` zero-freeness, and
`l21ClassicalLine` is derived from the two-sided estimate and the `B / b` ratio
bound by `classicalLogDerivLineBoundOn_of_zetaSide`.  All non-L21 fields are
copied verbatim. -/
noncomputable def toPaperResidualInputs (R : PaperResidualInputsL21 D) :
    PaperResidualInputs D :=
  let W := R.toL21_2
  { line := R.line
    zetaRH := W.hRH
    l21Profile := W.profile
    l21c := W.c
    l21Cper := W.Cper
    l21Ktail := W.Ktail
    l21p := W.p
    l21X_gt_one := W.X_gt_one
    l21c_pos := W.c_pos
    l21c_le_one := W.c_le_one
    l21U_ge_three := W.U_ge_three
    l21Cper_ge_three := W.Cper_ge_three
    l21Ktail_nonneg := W.Ktail_nonneg
    l21ZeroFree := R.l21.zeta.zeroFree
    l21ClassicalLine := classicalLogDerivLineBoundOn_of_zetaSide R.l21.zeta
    l21VerticalTail := W.verticalTail
    l21p_gt_one := W.p_gt_one
    l21CentralCount := W.localCount
    l21b_le_B := W.b_le_B
    l21a_ge_log_two := W.a_ge_log_two
    l21FourierLow := W.fourierLow
    l21FourierMiddle := W.fourierMiddle
    l21FourierTail := W.fourierTail
    l21U_dominates := W.U_dominates
    l21U_le_exp := W.U_le_exp
    l30p := R.l30p
    l30Growth := R.l30Growth
    l30ε := R.l30ε
    l30ε_pos := R.l30ε_pos
    l30A := R.l30A
    l30B := R.l30B
    l30B_pos := R.l30B_pos
    l30B_le_eighth := R.l30B_le_eighth
    l30AB_ge_four := R.l30AB_ge_four
    l30c := R.l30c
    l30C := R.l30C
    l30A_pos := R.l30A_pos
    l30A_ge_32 := R.l30A_ge_32
    l30AC_le := R.l30AC_le
    l30C_pos := R.l30C_pos
    l30SharpUpper := R.l30SharpUpper
    l30SharpCentral := R.l30SharpCentral
    l30Binomial := R.l30Binomial
    l30Cantor := R.l30Cantor
    l30Failure := R.l30Failure
    l27Data := R.l27Data
    l27L1 := R.l27L1
    l27Siegel := R.l27Siegel
    l27Hurwitz := R.l27Hurwitz
    l27ClassNumber := R.l27ClassNumber
    l27θ := R.l27θ
    l27θ_pos := R.l27θ_pos
    l27KappaLe := R.l27KappaLe
    l27CentralTrace := R.l27CentralTrace
    l27Prime := R.l27Prime
    l27WeightedModel := R.l27WeightedModel
    l27OrderDominates := R.l27OrderDominates
    l27Fiber := R.l27Fiber
    l27PGeFour := R.l27PGeFour
    l27KillLaw := R.l27KillLaw
    l27Hasse := R.l27Hasse
    l27CurveBudget := R.l27CurveBudget
    l27LogFactor := R.l27LogFactor
    l34 := R.l34
    l18_4 := R.l18_4
    l19 := R.l19
    l20_2 := R.l20_2
    l20_4 := R.l20_4
    p1 := R.p1
    c1 := R.c1
    c2 := R.c2
    c3 := R.c3
    c4 := R.c4 }

/-- The transported record keeps the Dirichlet-GRH field. -/
theorem toPaperResidualInputs_line (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.line = R.line := rfl

/-- The transported record's zeta GRH is the residual's zeta-side RH. -/
theorem toPaperResidualInputs_zetaRH (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.zetaRH = R.l21.zeta.rh := rfl

/-- The transported concrete profile is the elementary profile. -/
theorem toPaperResidualInputs_l21Profile (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.l21Profile = elementaryProfile := rfl

/-- The transported stage-one constant is the elementary constant. -/
theorem toPaperResidualInputs_l21c (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.l21c = elementaryC := by
  simp only [toPaperResidualInputs]
  simpa only [toL21_2] using wave17InputsOfResidual_c R.l21

/-- The transported Perron exponent is the elementary exponent. -/
theorem toPaperResidualInputs_l21Cper (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.l21Cper = elementaryCper := by
  simp only [toPaperResidualInputs]
  simpa only [toL21_2] using wave17InputsOfResidual_Cper R.l21

/-- The transported centre sequence is `X`. -/
theorem toPaperResidualInputs_l21p (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.l21p = elementaryX := by
  simp only [toPaperResidualInputs]
  simpa only [toL21_2] using wave17InputsOfResidual_p R.l21

/-- The transported central count is the residual's literal count. -/
theorem toPaperResidualInputs_l21CentralCount (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.l21CentralCount = R.l21.localCount := rfl

/-- The transported zero-free field is the residual's zero-free field. -/
theorem toPaperResidualInputs_l21ZeroFree (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.l21ZeroFree = R.l21.zeta.zeroFree := rfl

/-- The transported classical line bound is the one derived from the residual's
zeta side. -/
theorem toPaperResidualInputs_l21ClassicalLine (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.l21ClassicalLine =
      classicalLogDerivLineBoundOn_of_zetaSide R.l21.zeta := rfl

/-- **Every non-L21 field is transported verbatim.**  This records that the
L30, L27, L34, L18.4, L19, L20, P1 and C1–C4 components are unchanged. -/
theorem toPaperResidualInputs_data (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.line = R.line ∧
      R.toPaperResidualInputs.l30p = R.l30p ∧
      R.toPaperResidualInputs.l30Growth = R.l30Growth ∧
      R.toPaperResidualInputs.l30ε = R.l30ε ∧
      R.toPaperResidualInputs.l30A = R.l30A ∧
      R.toPaperResidualInputs.l30B = R.l30B ∧
      R.toPaperResidualInputs.l30c = R.l30c ∧
      R.toPaperResidualInputs.l30C = R.l30C ∧
      R.toPaperResidualInputs.l27Data = R.l27Data ∧
      R.toPaperResidualInputs.l27L1 = R.l27L1 ∧
      R.toPaperResidualInputs.l27θ = R.l27θ ∧
      R.toPaperResidualInputs.l34 = R.l34 ∧
      R.toPaperResidualInputs.l18_4 = R.l18_4 ∧
      R.toPaperResidualInputs.l19 = R.l19 ∧
      R.toPaperResidualInputs.l20_2 = R.l20_2 ∧
      R.toPaperResidualInputs.l20_4 = R.l20_4 ∧
      R.toPaperResidualInputs.p1 = R.p1 ∧
      R.toPaperResidualInputs.c1 = R.c1 ∧
      R.toPaperResidualInputs.c2 = R.c2 ∧
      R.toPaperResidualInputs.c3 = R.c3 ∧
      R.toPaperResidualInputs.c4 = R.c4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The definitional data equality.**  The record obtained by applying the
Wave-18 `toL21_2` to the transported residual agrees definitionally with the
residual's own `wave17InputsOfResidual` on all loss/structural data. -/
theorem toPaperResidualInputs_toL21_2_data (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.toL21_2.profile = R.toL21_2.profile ∧
      R.toPaperResidualInputs.toL21_2.c = R.toL21_2.c ∧
      R.toPaperResidualInputs.toL21_2.Cper = R.toL21_2.Cper ∧
      R.toPaperResidualInputs.toL21_2.Ktail = R.toL21_2.Ktail ∧
      R.toPaperResidualInputs.toL21_2.p = R.toL21_2.p :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The exact adapter.**

The two records are *not* definitionally equal: `PaperResidualInputs.toL21_2`
produces its line constant by `Classical.choose` from the classical `O (log²)`
bound (`l21ClassicalLine`), whereas the residual route uses the zeta-side
`ZetaLineEstimate` directly with constant `ZetaSide.KlineRaw`.  Both line bounds
are genuine:

* `R.toL21_2.lineBound` is `VerticalLineBound` at `R.l21.zeta.KlineRaw`,
  produced by `verticalLineBound_of_zetaLineEstimate_exponent`;
* `R.toPaperResidualInputs.toL21_2.lineBound` is `VerticalLineBound` at its own
  `Classical.choose` constant, produced by
  `verticalLineBound_of_classicalLogDerivOn_exponent`.

The adapter records the loss/structural equality and the residual's own line
bound.  It is the precise sense in which the residual's wave-17 record can be
used in the Wave-18 slot: the line proofs are interchangeable, but the chosen
constants need not coincide. -/
theorem toPaperResidualInputs_toL21_2_adapter (R : PaperResidualInputsL21 D) :
    R.toPaperResidualInputs.toL21_2.profile = R.toL21_2.profile ∧
      R.toPaperResidualInputs.toL21_2.c = R.toL21_2.c ∧
      R.toPaperResidualInputs.toL21_2.Cper = R.toL21_2.Cper ∧
      R.toPaperResidualInputs.toL21_2.Ktail = R.toL21_2.Ktail ∧
      R.toPaperResidualInputs.toL21_2.p = R.toL21_2.p ∧
      R.toL21_2.KlineRaw = R.l21.zeta.KlineRaw ∧
      VerticalLineBound R.toL21_2.profile.X
        (fun _ => R.toL21_2.KlineRaw) (R.toL21_2.Cper - 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, R.toL21_2.lineBound⟩

/-- **The transported record is inhabited from the L21 residual.** -/
theorem nonempty_paperResidualInputs (R : PaperResidualInputsL21 D) :
    Nonempty (PaperResidualInputs D) :=
  ⟨R.toPaperResidualInputs⟩

/-- **The wave-17 inputs are inhabited through the transported record.** -/
theorem nonempty_wave17Inputs (R : PaperResidualInputsL21 D) :
    Nonempty (Wave17Inputs Egood D) :=
  PaperResidualInputs.nonempty_wave17Inputs R.toPaperResidualInputs

end PaperResidualInputsL21

/-! ## The endpoint -/

/-- The standard one-point epoch family packaged as a schedule-indexed family. -/
noncomputable def EgoodSchedule
    (_s : BalancedRationalSchedule) (n : ℕ) (hN : 3 ≤ n) : HardEpochData n :=
  Cogentic.RandomizedPaperEndpointWave18.EgoodSchedule _s n hN

/-- **Wave-21 paper endpoint.**  Given, for every balanced-schedule ceiling `D`,
the residual inputs in which the entire L21.2 block is the concrete-leaf
residual, there is one universal serialized factoring algorithm such that, on
the standard one-point epoch family,

* the kernel-checked driver always outputs a permutation of
  `n.primeFactorsList`;
* the expected serialized bit cost is eventually at most
  `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
  `balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof transports each residual record to `PaperResidualInputs` via
`PaperResidualInputsL21.toPaperResidualInputs`, whose L21.2 leaf is
`wave17InputsOfResidual`, and then invokes the Wave-18 endpoint. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave21Inputs
    (R : ∀ D : ℝ, PaperResidualInputsL21 D) :
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
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) :=
  Cogentic.RandomizedPaperEndpointWave18.serialized_assembled_balancedEnvelopeInfimum_from_wave18Inputs
    (fun D => (R D).toPaperResidualInputs)

/-! ## Axiom audit -/

#print axioms PaperResidualInputsL21.toL21_2
#print axioms PaperResidualInputsL21.toL21_2_profile
#print axioms PaperResidualInputsL21.toL21_2_c
#print axioms PaperResidualInputsL21.toL21_2_Cper
#print axioms PaperResidualInputsL21.toL21_2_p
#print axioms PaperResidualInputsL21.toL21_2_Ktail
#print axioms PaperResidualInputsL21.nonempty_toL21_2
#print axioms PaperResidualInputsL21.toPaperResidualInputs
#print axioms PaperResidualInputsL21.toPaperResidualInputs_line
#print axioms PaperResidualInputsL21.toPaperResidualInputs_zetaRH
#print axioms PaperResidualInputsL21.toPaperResidualInputs_l21Profile
#print axioms PaperResidualInputsL21.toPaperResidualInputs_l21c
#print axioms PaperResidualInputsL21.toPaperResidualInputs_l21Cper
#print axioms PaperResidualInputsL21.toPaperResidualInputs_l21p
#print axioms PaperResidualInputsL21.toPaperResidualInputs_l21CentralCount
#print axioms PaperResidualInputsL21.toPaperResidualInputs_l21ZeroFree
#print axioms PaperResidualInputsL21.toPaperResidualInputs_l21ClassicalLine
#print axioms PaperResidualInputsL21.toPaperResidualInputs_data
#print axioms PaperResidualInputsL21.toPaperResidualInputs_toL21_2_data
#print axioms PaperResidualInputsL21.toPaperResidualInputs_toL21_2_adapter
#print axioms PaperResidualInputsL21.nonempty_paperResidualInputs
#print axioms PaperResidualInputsL21.nonempty_wave17Inputs
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave21Inputs

end Cogentic.RandomizedPaperEndpointWave21
