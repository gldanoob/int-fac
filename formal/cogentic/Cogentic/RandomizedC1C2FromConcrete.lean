import Cogentic.RandomizedPaperEndpointWave22
import Cogentic.RandomizedConcreteEpochChecks
import Cogentic.RandomizedWave17Audit

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-!
# C1/C2 for the Wave-22 record, derived from the concrete epoch

The Wave-22 record `PaperResidualInputsFinal` carries two fields

```
c1 : C1Inputs Egood
c2 : C2Inputs Egood
```

at the standard one-point concrete epoch `Egood = (goodEpochOfLe n hN).toHardEpochData`.
This file determines whether those fields have to be assumed.

## What is proved

* `hiddenUniform_Egood` and `c2Inputs_Egood`: **`C2Inputs Egood` is
  unconditional**.  The ideal law of `goodEpochOfLe` is uniform, so the
  conditional sign symmetry `HiddenUniform` holds for trivial reasons; no
  number theory is involved.
* `c1Inputs_Egood_of_globalProductIdentity`: **`C1Inputs Egood` is equivalent
  to the concrete product identity.**  The transport uses the existing adapter
  `RandomizedWave17Audit.c1Inputs_of_concrete` with the definitional equality
  `Egood n hN = (goodEpochOfLe n hN).toHardEpochData` (`rfl`, i.e. the
  `concrete_eq` adapter for this family).
* `PaperResidualInputsFinalWithoutC12`: the Wave-22 record with `c1`/`c2`
  removed and a single concrete field `c1Concrete` added.
* `PaperResidualInputsFinalWithoutC12.toPaperResidualInputsFinal`: reconstructs
  the full Wave-22 record, deriving `c1` from `c1Concrete` and `c2`
  unconditionally.

## What remains, exactly

C2 remains nothing.  C1 remains the paper statement

```
∀ n (hN : 3 ≤ n), (goodEpochOfLe n hN).GlobalProductIdentity
```

which is the restriction of `GlobalProductIdentity` to the standard concrete
epoch.  This statement is **not** a consequence of the packaged data, and in
fact it is *false* for the current `goodEpochOfLe` placeholder:
`not_globalProductIdentity_goodEpochOfLe` exhibits `n = 15`, the unique good
transcript `some (goodTr 15)` (mask `{()}`, `publicRoot = 1`, empty field set),
and the sample whose hidden label is the unit `2`, for which the required
product is `2² = 4 ≠ 1` in `ZMod 15`.

Moreover `not_congruenceCheck_Egood` refutes the `CongruenceCheck` itself at
`n = 15` (which is a hard input, `hardInput_fifteen`), and
`not_c1Inputs_Egood` concludes

```
¬ C1Inputs Egood.
```

So the Wave-22 `c1` field is not merely an unproved analytic hypothesis: at
`Egood` it is impossible, hence `PaperResidualInputsFinal` is uninhabited and
the Wave-22 endpoint hypothesis `∀ D, PaperResidualInputsFinal D` is empty.
The correct reduction is therefore to expose `c1Concrete` as the residual C1
input (which inherits the same refutation), or — the real repair — to replace
the degenerate `goodTr`/`goodEpochOfLe` placeholder by a solver whose public
transcript satisfies the product identity.  C2 can be dropped altogether.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedC1C2FromConcrete

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
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34LogIntegral
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34EffectiveChebotarev
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedL34FactorialBudgets
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperEndpointWave17
open Cogentic.RandomizedPaperEndpointWave18
open Cogentic.RandomizedPaperEndpointWave18L34
open Cogentic.RandomizedPaperEndpointWave21
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit
open Cogentic.RandomizedWave18Audit
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedHiddenLabels
open Cogentic.RandomizedPaperEndpointWave22


/-! ## C2 at `Egood` is unconditional -/

/-- The ideal law of the standard one-point epoch is uniform, so the
conditional hidden-sign symmetry holds trivially. -/
theorem hiddenUniform_Egood (n : ℕ) (hN : 3 ≤ n) :
    (Egood n hN).HiddenUniform := by
  intro t x y _ _ _ _
  haveI : NeZero n := ⟨by omega⟩
  show (Egood n hN).ideal x = (Egood n hN).ideal y
  unfold Egood
  rw [ConcreteEpochData.toHardEpochData_ideal]
  unfold goodEpochOfLe goodEpoch
  haveI : Nonempty (Egood n hN).Sample := ⟨x⟩
  change (PMF.uniformOfFintype (Egood n hN).Sample) x =
    (PMF.uniformOfFintype (Egood n hN).Sample) y
  rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]

/-- **C2 is unconditional at the standard epoch.** -/
theorem c2Inputs_Egood : C2Inputs Egood where
  hiddenUniform := fun n hN _ => hiddenUniform_Egood n hN

/-! ## C1 at `Egood` is exactly the concrete product identity -/

/-- **C1 transport.**  The concrete global product identity, together with the
definitional adapter `Egood = goodEpochOfLe.toHardEpochData`, gives
`C1Inputs Egood`.  This is `c1Inputs_of_concrete` at `heq := rfl`. -/
theorem c1Inputs_Egood_of_globalProductIdentity
    (hglobal : ∀ n (hN : 3 ≤ n), (goodEpochOfLe n hN).GlobalProductIdentity) :
    C1Inputs Egood :=
  c1Inputs_of_concrete hglobal (fun _ _ => rfl)

/-! ## C1 is refutable at the current `Egood` placeholder -/

/-- **The concrete C1 hypothesis is false at `goodEpochOfLe`.**  The unique
good transcript has mask `{()}`, `publicRoot = 1` and no fields, while the
sample with hidden unit `2` has `2² = 4 ≠ 1` in `ZMod 15`. -/
theorem not_globalProductIdentity_goodEpochOfLe :
    ¬ (goodEpochOfLe 15 (by norm_num)).GlobalProductIdentity := by
  intro h
  let D := goodEpochOfLe 15 (by norm_num)
  let t0 : D.good := ⟨some (goodTr 15), by
    apply ConcreteEpochData.some_mem_good_of_solver_eq (D := D)
      (c := ()) (s := fun _ => 1)
    rfl⟩
  let u : (ZMod 15)ˣ := ZMod.unitOfCoprime 2 (by norm_num)
  let x : D.Sample := ((), fun _ => u)
  have hx : observe D.solver x = t0.val := rfl
  have hprod := h t0 x hx
  simp [D, t0, x, u, goodEpochOfLe, goodEpoch, goodTr,
    ConcreteEpochData.extract] at hprod
  have h2 : (2 : ZMod 15) ^ 2 = 1 := by
    simpa [u] using congrArg (fun z : (ZMod 15)ˣ => (z : ZMod 15)) hprod
  norm_num at h2
  exact (by decide : (4 : ZMod 15) ≠ 1) h2

/-- `15` is a hard input: odd, not prime, and not a prime power. -/
theorem hardInput_fifteen : HardInput 15 := by
  refine ⟨by decide, by norm_num, ?_⟩
  rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le (by norm_num)]
  refine ⟨3, ?_, 5, ?_, by norm_num⟩
  · change 3 ∈ Nat.primeFactors 15
    rw [Nat.mem_primeFactors]; exact ⟨by norm_num, by norm_num, by norm_num⟩
  · change 5 ∈ Nat.primeFactors 15
    rw [Nat.mem_primeFactors]; exact ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The `CongruenceCheck` itself is false at `Egood`.**  The good transcript
`some (goodTr 15)` has mask `{()}`, private index `()` (multiplicity one) and
`publicRoot = 1`; taking the sample whose hidden unit at `()` is `2` makes the
required congruence `2² = 1` in `ZMod 15`, which is false. -/
theorem not_congruenceCheck_Egood (hN : 3 ≤ 15) :
    ¬ (Egood 15 hN).CongruenceCheck := by
  intro h
  let D := goodEpochOfLe 15 (by norm_num)
  let t0 : (Egood 15 hN).good := ⟨some (goodTr 15), by
    change some (goodTr 15) ∈ D.good
    apply ConcreteEpochData.some_mem_good_of_solver_eq (D := D)
      (c := ()) (s := fun _ => 1)
    rfl⟩
  let u : (ZMod 15)ˣ := ZMod.unitOfCoprime 2 (by norm_num)
  let x : (Egood 15 hN).Sample := ((), fun _ => u)
  have hx : observe (Egood 15 hN).trace x = t0.val := rfl
  have hc := h t0 x hx
  simp [Egood, t0, x, u, goodEpochOfLe, goodEpoch, goodTr, labelProduct,
    ConcreteEpochData.toHardEpochData, PublicMultiFieldTranscript.toTranscriptData,
    transcriptDataOfNonemptyMask, PublicMultiFieldTranscript.publicRoot,
    publicAssembledRoot] at hc
  have h2 : (2 : ZMod 15) ^ 2 = 1 := by
    simpa [u] using congrArg (fun z : (ZMod 15)ˣ => (z : ZMod 15)) hc
  norm_num at h2
  exact (by decide : (4 : ZMod 15) ≠ 1) h2

/-- **`C1Inputs Egood` is impossible.**  It would give `CongruenceCheck` at the
hard input `15`, contradicting `not_congruenceCheck_Egood`.  Hence the Wave-22
record `PaperResidualInputsFinal` has no inhabitant at the current placeholder
`Egood`; in particular the Wave-22 endpoint hypothesis `∀ D, ...` is empty. -/
theorem not_c1Inputs_Egood : ¬ C1Inputs Egood := by
  intro c1
  exact not_congruenceCheck_Egood (by norm_num)
    (c1.congruenceCheck 15 (by norm_num) hardInput_fifteen)

/-- **The Wave-22 record is uninhabited.**  Its `c1` field is
`C1Inputs Egood`, which `not_c1Inputs_Egood` refutes.  Consequently the
Wave-22 endpoint hypothesis `(R : ∀ D, PaperResidualInputsFinal D)` is an
empty function type. -/
theorem not_nonempty_paperResidualInputsFinal (D : ℝ) :
    ¬ Nonempty (PaperResidualInputsFinal D) :=
  fun ⟨R⟩ => not_c1Inputs_Egood R.c1

/-! ## The Wave-22 variant without `c1`/`c2` -/

structure PaperResidualInputsFinalWithoutC12 (D : ℝ) where
  /-- **GRH for Dirichlet `L`-functions.** -/
  line : DirichletLZerosOnLine
  /-- **The whole L21.2 analytic input**: the zeta side (RH, zero-freeness on
  `Re s = 2/3`, and the two-sided line estimate with a raw constant) together
  with the literal central short-interval smooth count. -/
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
  factor is the true Dickman exponent `u log u`. -/
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

  -- L34: raw data
  /-- The possible exceptional real zero `β₀`. -/
  l34Beta0 : ℕ → ℝ
  /-- The real part of a generic zero of `ζ_E`. -/
  l34ZeroRealPart : ℕ → ℝ
  /-- The absolute degree `2d`, as a natural number. -/
  l34Degree : ℕ → ℕ
  /-- `log |Δ_E|`. -/
  l34DiscLog : ℕ → ℝ
  /-- The polynomial input parameter `T`. -/
  l34T : ℕ → ℝ
  /-- A cumulative Chebotarev count. -/
  l34Count : ℕ → ℝ
  /-- The cumulative inert count. -/
  l34InertCount : ℕ → ℝ
  /-- The degree-one inert count after discarding small / higher-degree ideals. -/
  l34DegreeOneInert : ℕ → ℝ
  /-- `Li x`. -/
  l34LiX : ℕ → ℝ
  /-- `Li x^{β₀}`. -/
  l34LiBeta0 : ℕ → ℝ
  /-- The per-trial detection probability. -/
  l34PTrial : ℕ → ℝ
  /-- The actual failure probability of the probe stage. -/
  l34ActualMiss : ℕ → ℝ
  /-- The number of nonrational classes. -/
  l34ClassCount : ℕ → ℝ
  /-- The number of probes `R`. -/
  l34R : ℕ → ℕ
  /-- The range constant. -/
  l34K : ℝ
  /-- The constant `C` in the effective error. -/
  l34C : ℝ
  /-- The constant `c` in the effective error. -/
  l34cZ : ℝ
  /-- The zero-free-region constant `c_z`. -/
  l34cz : ℝ
  /-- The per-ideal selection constant. -/
  l34csel : ℝ
  /-- The polynomial constant in `h* ≤ Ch T³`. -/
  l34Ch : ℝ
  /-- The Dedekind zero-free region in its smallest form. -/
  l34ZeroFree : DedekindZeroFreeInput l34Beta0 l34ZeroRealPart l34cz l34DiscLog
  /-- The classical Stark exceptional-zero input, at the paper factorial factor
  `F = (2d)! = absoluteFactorialFactor l34Degree`. -/
  l34Stark : StarkExceptionalZeroInput l34Beta0
    (absoluteFactorialFactor l34Degree) l34DiscLog
  /-- The explicit `T^6` range input at the natural-number degree. -/
  l34Range : ChebotarevT6RangeInput l34K l34T
    (fun n => (l34Degree n : ℝ)) l34DiscLog
  /-- The polynomial parameter is at least one. -/
  l34T_ge_one : ∀ n, 1 ≤ l34T n
  /-- **The standard effective Chebotarev statement** at the cutoff
  `x = 2^{T⁶}`. -/
  l34Effective : EffectiveChebotarevStatement l34K l34C l34cZ (cutoff l34T)
    (fun n => (l34Degree n : ℝ)) l34DiscLog l34Count l34LiX l34LiBeta0
  /-- The inert count contains the counted nonidentity class. -/
  l34InertGeCount : ∀ n, l34Count n ≤ l34InertCount n
  /-- Stark's bound converted to the dyadic bracket, at `cbr = 1/16`. -/
  l34Bracket : LogIntegralBracket (1 / 16) (cutoff l34T)
    (absoluteFactorialFactor l34Degree) l34T l34LiX l34LiBeta0
  /-- **The uniform threshold for the pointwise factorial budgets.**  The raw
  parameter `T` dominates both explicit analytic thresholds at every index.
  The two budgets are derived from this growth condition. -/
  l34BudgetThreshold : ∀ n,
    max (errorLogBudgetThreshold l34C l34cZ (1 / 16))
        (degreeLossLogBudgetThreshold (1 / 16)) ≤ l34T n
  /-- The degree-one reduction. -/
  l34DegreeOneReduction : DegreeOneInertReduction l34InertCount l34DegreeOneInert
    (fun n => (l34Degree n : ℝ)) (cutoff l34T)
  /-- Probe selection at `1/(d x)` per eligible ideal. -/
  l34Selection : ProbeSelectionLowerBound l34csel (cutoff l34T)
    (fun n => (l34Degree n : ℝ)) l34DegreeOneInert l34PTrial
  /-- The paper's budget `R = F T¹⁰`, at `F = (2d)!`. -/
  l34ProbeBudget : ProbeBudget l34R (absoluteFactorialFactor l34Degree) l34T
  /-- There is at least one nonrational class. -/
  l34ClassCountPos : ∀ n, 0 < l34ClassCount n
  /-- The cubic class-count input. -/
  l34ClassCubic : ClassCountCubicInput l34Ch l34ClassCount l34T
  /-- The probe constant beats the class-count entropy constant. -/
  l34ConstantMargin : l34Ch * Real.log 2 < l34csel * (1 / 16) / 4
  /-- The probe exponent `T³` eventually dominates the ledger scale. -/
  l34ScaleCubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (l34csel * (1 / 16) / 4 - l34Ch * Real.log 2) * l34T n ^ 3
  /-- The actual failure probability is nonnegative. -/
  l34ActualMissNonneg : ∀ n, 0 ≤ l34ActualMiss n
  /-- The probe union bound. -/
  l34UnionBound : ProbeMissUnionBound l34ActualMiss l34PTrial l34ClassCount l34R
  /-- The per-trial probability is nonnegative. -/
  l34PTrialNonneg : ∀ n, 0 ≤ l34PTrial n
  /-- The per-trial probability is at most one. -/
  l34PTrialLeOne : ∀ n, l34PTrial n ≤ 1

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

  -- P1, the concrete C1 residual, and C3–C4
  /-- P1: the explicit `exp (o(H))`-cost prepass. -/
  p1 : SubexpPrepassInput
  /-- **C1 on the concrete epoch.**  The global modular product
  identity of the public multi-field transcript, at the standard
  concrete epoch `goodEpochOfLe`.  This is exactly the hypothesis of
  `ConcreteEpochData.GlobalProductIdentity`; it is *not* derivable from
  the packaged `HardEpochData` alone, and it is the only C1/C2 field
  that the variant retains. -/
  c1Concrete : ∀ n (hN : 3 ≤ n), (goodEpochOfLe n hN).GlobalProductIdentity
  /-- C3: the ideal/actual total-variation budget. -/
  c3 : C3Inputs Egood
  /-- C4: the expected public-work budget. -/
  c4 : C4Inputs Egood D

noncomputable def PaperResidualInputsFinalWithoutC12.toPaperResidualInputsFinal
    {D : ℝ} (R : PaperResidualInputsFinalWithoutC12 D) :
    PaperResidualInputsFinal D where
  line := R.line
  l21 := R.l21
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
  l34Beta0 := R.l34Beta0
  l34ZeroRealPart := R.l34ZeroRealPart
  l34Degree := R.l34Degree
  l34DiscLog := R.l34DiscLog
  l34T := R.l34T
  l34Count := R.l34Count
  l34InertCount := R.l34InertCount
  l34DegreeOneInert := R.l34DegreeOneInert
  l34LiX := R.l34LiX
  l34LiBeta0 := R.l34LiBeta0
  l34PTrial := R.l34PTrial
  l34ActualMiss := R.l34ActualMiss
  l34ClassCount := R.l34ClassCount
  l34R := R.l34R
  l34K := R.l34K
  l34C := R.l34C
  l34cZ := R.l34cZ
  l34cz := R.l34cz
  l34csel := R.l34csel
  l34Ch := R.l34Ch
  l34ZeroFree := R.l34ZeroFree
  l34Stark := R.l34Stark
  l34Range := R.l34Range
  l34T_ge_one := R.l34T_ge_one
  l34Effective := R.l34Effective
  l34InertGeCount := R.l34InertGeCount
  l34Bracket := R.l34Bracket
  l34BudgetThreshold := R.l34BudgetThreshold
  l34DegreeOneReduction := R.l34DegreeOneReduction
  l34Selection := R.l34Selection
  l34ProbeBudget := R.l34ProbeBudget
  l34ClassCountPos := R.l34ClassCountPos
  l34ClassCubic := R.l34ClassCubic
  l34ConstantMargin := R.l34ConstantMargin
  l34ScaleCubic := R.l34ScaleCubic
  l34ActualMissNonneg := R.l34ActualMissNonneg
  l34UnionBound := R.l34UnionBound
  l34PTrialNonneg := R.l34PTrialNonneg
  l34PTrialLeOne := R.l34PTrialLeOne
  l18_4 := R.l18_4
  l19 := R.l19
  l20_2 := R.l20_2
  l20_4 := R.l20_4
  p1 := R.p1
  c1 := c1Inputs_Egood_of_globalProductIdentity R.c1Concrete
  c3 := R.c3
  c4 := R.c4
  c2 := c2Inputs_Egood

/-- **The `c1`-concrete variant is also uninhabited**, because its residual
field `c1Concrete` contains the refuted `GlobalProductIdentity` at `n = 15`.
This records that the residual C1 statement is not a harmless placeholder. -/
theorem not_nonempty_finalWithoutC12 (D : ℝ) :
    ¬ Nonempty (PaperResidualInputsFinalWithoutC12 D) :=
  fun ⟨R⟩ => not_globalProductIdentity_goodEpochOfLe (R.c1Concrete 15 (by norm_num))

/-! ## Axiom audit -/

#print axioms hiddenUniform_Egood
#print axioms c2Inputs_Egood
#print axioms c1Inputs_Egood_of_globalProductIdentity
#print axioms not_globalProductIdentity_goodEpochOfLe
#print axioms hardInput_fifteen
#print axioms not_congruenceCheck_Egood
#print axioms not_c1Inputs_Egood
#print axioms not_nonempty_paperResidualInputsFinal
#print axioms PaperResidualInputsFinalWithoutC12.toPaperResidualInputsFinal
#print axioms not_nonempty_finalWithoutC12

end Cogentic.RandomizedC1C2FromConcrete
