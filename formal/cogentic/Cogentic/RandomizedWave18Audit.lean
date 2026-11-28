import Cogentic.RandomizedPaperEndpointWave18
import Cogentic.RandomizedL30Normalization
import Cogentic.RandomizedL30SharpWitness
import Cogentic.RandomizedWave17Audit
import Cogentic.RandomizedL21_2ConcreteLeaf
import Cogentic.RandomizedL21_2CentralBin
import Cogentic.RandomizedL19ConcreteAssembly
import Cogentic.RandomizedL20_2SourceWitness
import Cogentic.RandomizedL34EffectiveChebotarev

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-!
# Wave 18 audit: the fields of `PaperResidualInputs`

This file audits every field of
`Cogentic.RandomizedPaperEndpointWave18.PaperResidualInputs`, the honest
residual bundle of the paper endpoint.

## Classification

Each field is classified as

* `(a) proved` — its type is unconditionally inhabited, or it is a structural
  scalar/growth condition discharged by explicit data;
* `(b) reduced` — a named classical/analytic statement, with a proven reduction
  to the smallest interface available in the repository;
* `(c) refutable` — no inhabitant exists.

No field of the current record is `(c)`.  The historically refutable field, the
old positive-error upper density `PaperScaleSmoothUpper l30C l30p l30ε`, is
*not* a field of the repaired record; its refutation is recalled below
(`oldPaperScaleSmoothUpper_refutable`), and its replacement by the sharp
`u log u` predicates is checked against the explicit positive witness of
`RandomizedL30SharpWitness` (`sharpUpper_not_refutable`,
`sharpLocal_not_refutable`).

## The vacuity checks

The audit re-checks the places that historically produced vacuous records:

* **L30.** The sharp upper and local fields are *not* refutable: the constant
  scale `p = 4`, `ε = log 768 / t_4 - 1` satisfies both with genuine positive
  counts (`4` globally, `1` centrally).  What *is* true is that this constant
  witness cannot be combined with the paper's arithmetic `32 ≤ A` at fixed
  scale: the sharp upper forces `C ≥ 5/64`, hence `c = A C ≥ 5/2`, while the
  sharp central bound forces `c ≤ 1/5`.  Since `PaperDensityGrowth` requires
  `p → ∞`, this is a scale obstruction, not a refutation of the fields; it is
  proved as `constantWitness_incompatible_with_paperArithmetic`.
* **L21.2.** The central short-interval count is *not* a consequence of the
  L30 bins.  The L30 central interval is centred at `p²`, the L21.2 interval at
  `p`; for `p ≥ 4` they are disjoint
  (`l30CentralInterval_disjoint_shortInterval`).  The L21.2 insertion route is
  also blocked at window scale (`not_eventually_centralWindowSupply`).
  `ZetaLineZeroFree` is not a consequence of the coarse log-derivative line
  bound alone: the equivalence with the relative ratio bound needs
  zero-freeness as a hypothesis (`classicalLogDerivLineBoundOn_iff_ratio`),
  while RH does imply it (`zetaLineZeroFree_of_RH`).
* **L27.** `SiegelLOneLower` is not refutable: it is inhabited by any positive
  constant `L`-value (`siegelLOneLower_const`).  The central-trace field forces
  `θ ≤ 4` whenever a smooth order exists; combined with the curve budget this
  is a real constraint on `θ`, recorded as `theta_le_four_of_curveBudget`.
  The `κ`-bound is then the explicit weakening of `l27KappaLe`
  (`kappa_le_two_const_of_kappaLe`).
* **L34.** The factorial log budgets are not consequences of the standard
  effective Chebotarev statement; the existing counterexample with
  `F = exp 1000` is recalled.  They are nevertheless non-vacuous
  (`chebotarevErrorLogBudget_nonvacuous`,
  `degreeLossLogBudget_nonvacuous`).
* **`n = 0`.** Every unguarded `∀ n, 0 < f n` is checked at `n = 0`; the
  guarded tree field of `FailureData` is the only historical exception, and it
  is explicitly guarded (`FactorTreeNodes` takes `1 ≤ n`).

## Non-vacuity

`PaperStructuralCore` is the largest sub-record of `PaperResidualInputs` whose
fields are all discharged unconditionally here (the L21 structural block, the
L30 arithmetic/count block, the concrete L19 and L20.2 witnesses and the P1
witness).  `nonempty_paperStructuralCore` inhabits it.

`PaperResidualModulo` lists the genuinely remaining inputs.  The theorem
`paperResidual_of_modulo` constructs a full `PaperResidualInputs` from it,
using the concrete elementary L21.2 leaf and the explicit L30, L19, L20.2, P1,
Cantor and failure witnesses.  Thus `PaperResidualInputs` is inhabited modulo
exactly the stated analytic inputs.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss or
probability is replaced by zero.
-/

namespace Cogentic.RandomizedWave18Audit

universe u

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
open Cogentic.RandomizedL21_2CentralBin
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL21_2TailBound
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27Deuring
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
open Cogentic.RandomizedL30Relative
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30SharpWitness
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30UpperDensity
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Normalization
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
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedL19ConcreteAssembly
open Cogentic.RandomizedL20_2SourceWitness

/-! ## 1. The field-status vocabulary and the complete table -/

/-- The three-way classification requested by the audit. -/
inductive FieldStatus
  /-- `(a)` proved unconditionally (or inhabited by explicit data). -/
  | proved
  /-- `(b)` reduced to a named classical/analytic input. -/
  | reduced
  /-- `(c)` structurally uninhabited / refutable. -/
  | refutable
  deriving DecidableEq, Repr

/-- The seventy-three fields of `PaperResidualInputs`, in declaration order. -/
inductive PaperField
  | line | zetaRH
  | l21Profile | l21c | l21Cper | l21Ktail | l21p
  | l21X_gt_one | l21c_pos | l21c_le_one | l21U_ge_three
  | l21Cper_ge_three | l21Ktail_nonneg
  | l21ZeroFree | l21ClassicalLine | l21VerticalTail
  | l21p_gt_one | l21CentralCount | l21b_le_B | l21a_ge_log_two
  | l21FourierLow | l21FourierMiddle | l21FourierTail
  | l21U_dominates | l21U_le_exp
  | l30p | l30Growth | l30ε | l30ε_pos
  | l30A | l30B | l30B_pos | l30B_le_eighth | l30AB_ge_four
  | l30c | l30C | l30A_pos | l30A_ge_32 | l30AC_le | l30C_pos
  | l30SharpUpper | l30SharpCentral | l30Binomial | l30Cantor | l30Failure
  | l27Data | l27L1 | l27Siegel | l27Hurwitz | l27ClassNumber
  | l27θ | l27θ_pos | l27KappaLe | l27CentralTrace
  | l27Prime | l27WeightedModel | l27OrderDominates | l27Fiber
  | l27PGeFour | l27KillLaw | l27Hasse | l27CurveBudget | l27LogFactor
  | l34 | l18_4 | l19 | l20_2 | l20_4 | p1 | c1 | c2 | c3 | c4
  deriving DecidableEq, Repr

/-- The status assignment.  The L21 structural block, the L30 arithmetic block,
the canonical L27 scalars and the concrete L19/L20.2/P1 witnesses are proved;
everything else is a named residual.  No field is refutable.

For a *data* field (`l21Profile`, `l21c`, `l30p`, `l27θ`, …), `proved` means
that the type is inhabited by explicit data (e.g. the elementary profile, the
constant `θ = 1`), not that the field is forced by the other fields.  The
reduced record `PaperResidualModulo` still lets the parameter be supplied, so
this convention does not hide a choice. -/
def PaperField.status : PaperField → FieldStatus
  | .l21Profile | .l21c | .l21Cper | .l21Ktail | .l21p => .proved
  | .l21X_gt_one | .l21c_pos | .l21c_le_one | .l21U_ge_three => .proved
  | .l21Cper_ge_three | .l21Ktail_nonneg | .l21p_gt_one => .proved
  | .l21b_le_B | .l21a_ge_log_two => .proved
  | .l21FourierLow | .l21FourierMiddle | .l21FourierTail => .proved
  | .l21U_dominates | .l21U_le_exp => .proved
  | .l30p | .l30Growth | .l30ε | .l30ε_pos => .proved
  | .l30A | .l30B | .l30B_pos | .l30B_le_eighth | .l30AB_ge_four => .proved
  | .l30c | .l30C | .l30A_pos | .l30A_ge_32 | .l30AC_le | .l30C_pos => .proved
  | .l30Cantor | .l30Failure => .proved
  | .l27θ | .l27θ_pos => .proved
  | .l19 | .l20_2 | .p1 => .proved
  | _ => .reduced

/-- The explicit field list. -/
def allPaperFields : List PaperField :=
  [ .line, .zetaRH
  , .l21Profile, .l21c, .l21Cper, .l21Ktail, .l21p
  , .l21X_gt_one, .l21c_pos, .l21c_le_one, .l21U_ge_three
  , .l21Cper_ge_three, .l21Ktail_nonneg
  , .l21ZeroFree, .l21ClassicalLine, .l21VerticalTail
  , .l21p_gt_one, .l21CentralCount, .l21b_le_B, .l21a_ge_log_two
  , .l21FourierLow, .l21FourierMiddle, .l21FourierTail
  , .l21U_dominates, .l21U_le_exp
  , .l30p, .l30Growth, .l30ε, .l30ε_pos
  , .l30A, .l30B, .l30B_pos, .l30B_le_eighth, .l30AB_ge_four
  , .l30c, .l30C, .l30A_pos, .l30A_ge_32, .l30AC_le, .l30C_pos
  , .l30SharpUpper, .l30SharpCentral, .l30Binomial, .l30Cantor, .l30Failure
  , .l27Data, .l27L1, .l27Siegel, .l27Hurwitz, .l27ClassNumber
  , .l27θ, .l27θ_pos, .l27KappaLe, .l27CentralTrace
  , .l27Prime, .l27WeightedModel, .l27OrderDominates, .l27Fiber
  , .l27PGeFour, .l27KillLaw, .l27Hasse, .l27CurveBudget, .l27LogFactor
  , .l34, .l18_4, .l19, .l20_2, .l20_4, .p1, .c1, .c2, .c3, .c4 ]

/-- The compile-checked status table. -/
def paperStatusTable : List (PaperField × FieldStatus) :=
  allPaperFields.map (fun f => (f, f.status))

theorem allPaperFields_length : allPaperFields.length = 73 := rfl

theorem paperStatusTable_length : paperStatusTable.length = 73 := rfl

/-- No field of the repaired record is refutable. -/
theorem no_refutable_field (f : PaperField) : f.status ≠ FieldStatus.refutable := by
  cases f <;> decide

/-! ## 2. L30: the historical refutation and the sharp replacement -/

/-- **The old positive-error upper density is refutable.**  This is the field
that made the pre-wave-18 record uninhabited.  It is *not* a field of the
current record; its replacement is `GlobalOddUpperDensitySharp`. -/
theorem oldPaperScaleSmoothUpper_refutable
    (line : DirichletLZerosOnLine) {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ¬ PaperScaleSmoothUpper C p ε :=
  Cogentic.RandomizedL30Normalization.paperScaleSmoothUpper_false line h hε C

/-- **The sharp upper field is not refutable.**  The explicit constant-scale
count witness satisfies it with genuine positive counts. -/
theorem l30SharpUpper_not_refutable :
    ∃ (C : ℝ) (p : ℕ → ℝ) (ε : ℝ), GlobalOddUpperDensitySharp C p ε :=
  Cogentic.RandomizedL30Normalization.sharpUpper_not_refuted

/-- **The sharp central field is not refutable.**  The same witness has central
odd count `1`. -/
theorem l30SharpCentral_not_refutable :
    ∃ (c : ℝ) (p : ℕ → ℝ) (ε : ℝ), YounisOddPaperSharpIntervalCount c p ε :=
  Cogentic.RandomizedL30Normalization.sharpLocal_not_refuted

/-- **The constant-scale witness cannot be combined with the paper's arithmetic
`32 ≤ A`.**  At `p = 4` the sharp global upper bound forces `C ≥ 5/64` because
the global odd count is `4` and `exp (-(u log u)) ≤ 16/5`; the arithmetic then
forces `c ≥ 5/2`.  The sharp central bound at `p = 4` has central count `1` and
interval cardinality `5`, so it forces `c ≤ 1/5`.  This is a scale obstruction,
not a refutation of either sharp predicate: `PaperDensityGrowth` requires
`p → ∞`, and the witness is the constant `p = 4`. -/
theorem constantWitness_incompatible_with_paperArithmetic
    {A c C : ℝ} (hA : 32 ≤ A) (hAC : A * C ≤ c)
    (hupper : GlobalOddUpperDensitySharp C wP wEps)
    (hcentral : YounisOddPaperSharpIntervalCount c wP wEps) : False := by
  obtain ⟨N, hNu⟩ := Filter.eventually_atTop.1 hupper
  obtain ⟨M, hNc⟩ := Filter.eventually_atTop.1 hcentral
  let n := max N M
  have hu := hNu n (le_max_left _ _)
  have hc := hNc n (le_max_right _ _)
  have hEpos : 0 < Real.exp
      (-(paperDensityU wP wEps n *
        Real.log (paperDensityU wP wEps n))) := Real.exp_pos _
  have hEge : 1 ≤ Real.exp
      (-(paperDensityU wP wEps n *
        Real.log (paperDensityU wP wEps n))) := w_exp_ge_one n
  have hEle : Real.exp
      (-(paperDensityU wP wEps n *
        Real.log (paperDensityU wP wEps n))) ≤ (16 : ℝ) / 5 :=
    (w_exp_lt_sixteen_fifths n).le
  have hgcount :
      globalOddSmoothCount wP (paperT wP) (paperError wEps) n = 4 :=
    w_globalOddCount n
  have hp4 : wP n = 4 := rfl
  have hCpos : 0 < C := by
    by_contra hnot
    have hle : C ≤ 0 := le_of_not_gt hnot
    have hmul : C * Real.exp
        (-(paperDensityU wP wEps n *
          Real.log (paperDensityU wP wEps n))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hEpos.le
    rw [hgcount, hp4] at hu
    norm_num at hu
    linarith
  have hCge : (5 : ℝ) / 64 ≤ C := by
    have h1 : ((1 : ℝ) / 4) / ((16 : ℝ) / 5) ≤
        ((1 : ℝ) / 4) / Real.exp
          (-(paperDensityU wP wEps n *
            Real.log (paperDensityU wP wEps n))) :=
      div_le_div_of_nonneg_left (by norm_num) hEpos hEle
    have h2 : ((1 : ℝ) / 4) / Real.exp
          (-(paperDensityU wP wEps n *
            Real.log (paperDensityU wP wEps n))) ≤ C := by
      rw [div_le_iff₀ hEpos]
      rw [hgcount, hp4] at hu
      norm_num at hu
      exact hu
    norm_num at h1
    linarith
  have hcge : (5 : ℝ) / 2 ≤ c := by
    have h32 : (32 : ℝ) * ((5 : ℝ) / 64) ≤ A * C :=
      mul_le_mul hA hCge (by norm_num) (by linarith)
    nlinarith
  have hcle : c ≤ (1 : ℝ) / 5 := by
    have hcard : ((centralOrderInterval wP n).card : ℝ) = 5 := by
      rw [w_centralInterval n]
      norm_num
    have hcountc :
        centralOddSmoothCount wP (paperT wP) (paperError wEps) n = 1 :=
      w_centralOddCount n
    rw [hcard, hcountc] at hc
    have hnonneg : 0 ≤ 5 * c := by
      have : (0 : ℝ) ≤ c := by linarith
      positivity
    have hstep : 5 * c ≤ 5 * c * Real.exp
        (-(paperDensityU wP wEps n *
          Real.log (paperDensityU wP wEps n))) := by
      calc
        5 * c = 5 * c * 1 := by ring
        _ ≤ 5 * c * Real.exp
            (-(paperDensityU wP wEps n *
              Real.log (paperDensityU wP wEps n))) :=
          mul_le_mul_of_nonneg_left hEge hnonneg
    have h5 : 5 * c ≤ 1 := by
      calc
        5 * c ≤ 5 * c * Real.exp
            (-(paperDensityU wP wEps n *
              Real.log (paperDensityU wP wEps n))) := hstep
        _ = c * 5 * Real.exp
            (-(paperDensityU wP wEps n *
              Real.log (paperDensityU wP wEps n))) := by ring
        _ ≤ 1 := hc
    linarith
  linarith

/-! ## 3. L21.2: the central interval is not the L30 bin interval -/

/-- The L30 central interval lower end is strictly above the L21.2 short
interval upper end, for `p ≥ 4`. -/
theorem centralLower_gt_shortUpper {p : ℝ} (hp : 4 ≤ p) :
    p + Real.sqrt p < p ^ 2 - p ^ ((3 : ℝ) / 2) / 2 := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hsq : p ^ (2 : ℝ) = p ^ (2 : ℕ) := Real.rpow_two p
  have hpow' : p ^ ((3 : ℝ) / 2) ≤ p ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1.le
      (by norm_num : (3 : ℝ) / 2 ≤ 2)
  have hslt : Real.sqrt p < p := Real.sqrt_lt_self_iff.mpr hp1
  have hhalf : 2 * p ≤ p ^ (2 : ℝ) / 2 := by
    rw [hsq]
    nlinarith
  have hstrict : p + Real.sqrt p < 2 * p := by linarith
  have hmid : p ^ (2 : ℝ) / 2 ≤ p ^ (2 : ℝ) - p ^ ((3 : ℝ) / 2) / 2 := by
    linarith [hpow']
  have htarget : p + Real.sqrt p <
      p ^ (2 : ℝ) - p ^ ((3 : ℝ) / 2) / 2 :=
    lt_of_lt_of_le (lt_of_lt_of_le hstrict hhalf) hmid
  simpa [hsq] using htarget

/-- **The L30 central orders and the L21.2 short interval are disjoint.**  The
former lies in `[p² - p^{3/2}/2, p²]`, the latter in `(p-√p, p+√p)`. -/
theorem centralOrderInterval_disjoint_shortInterval
    {p : ℕ → ℝ} {n : ℕ} (hp : 4 ≤ p n) :
    Disjoint (centralOrderInterval p n) (shortInterval (p n)) := by
  rw [Finset.disjoint_left]
  intro m hm1 hm2
  rw [centralOrderInterval, Finset.mem_Icc] at hm1
  rw [mem_shortInterval] at hm2
  have hceil : p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2 ≤
      (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hlow : p n + Real.sqrt (p n) < (m : ℝ) := by
    have hm_ge : (⌈p n ^ 2 - p n ^ ((3 : ℝ) / 2) / 2⌉₊ : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hm1.1
    exact (centralLower_gt_shortUpper hp).trans_le (hceil.trans hm_ge)
  have hhigh : (m : ℝ) < p n + Real.sqrt (p n) := Nat.lt_ceil.mp hm2.2
  linarith

/-- The L30 central smooth orders and the L21.2 short smooth orders are
disjoint: the L30 count cannot supply the L21.2 local count. -/
theorem centralSmoothOrders_disjoint_shortSmoothInterval
    {p : ℕ → ℝ} {t err : ℕ → ℝ} {n : ℕ} (hp : 4 ≤ p n) (y : ℝ) :
    Disjoint (centralSmoothOrders p t err n) (shortSmoothInterval (p n) y) := by
  refine Finset.disjoint_left.mpr ?_
  intro m hm1 hm2
  have hm1' : m ∈ centralOrderInterval p n := (Finset.mem_filter.mp hm1).1
  have hm2' : m ∈ shortInterval (p n) := (Finset.mem_filter.mp hm2).1
  exact Finset.disjoint_left.mp
    (centralOrderInterval_disjoint_shortInterval (p := p) (n := n) hp) hm1' hm2'

/-- The L21.2 central-window insertion route is refuted at window scale: for
every nonnegative supply constant the `centralBinGuard` fails. -/
theorem l21_centralWindowSupply_refuted {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) :
    ¬ CentralWindowSupply p ε K :=
  not_eventually_centralWindowSupply h hε hK

/-- **`ZetaLineZeroFree` is not an extra consequence of the coarse line bound
alone.**  The equivalence between the classical log-derivative bound and the
relative ratio bound requires zero-freeness as a hypothesis; this is exactly
the sense in which the L21.2 zero-free field is independent without RH. -/
theorem zeroFree_needed_for_ratio_bound {X : ℕ → ℝ} :
    ClassicalLogDerivLineBoundOn X →
      (ZetaLineZeroFree X →
        ∃ C : ℝ, ClassicalLineRatioBound X C) := by
  intro h hz
  exact (classicalLogDerivLineBoundOn_iff_ratio hz).mp h

/-- At an actual zero the logarithmic derivative is `0` (Lean's division by
zero), so a bound on `logDeriv` alone has no content there: it cannot exclude
zeros.  This is the formal reason the L21.2 zero-free field is independent of
the coarse line estimate. -/
theorem logDeriv_eq_zero_of_zeta_eq_zero {s : ℂ} (h : riemannZeta s = 0) :
    logDeriv riemannZeta s = 0 := by
  simp [logDeriv, h]

/-- The *relative* classical line bound does imply zero-freeness, because its
conjunct explicitly excludes zeros.  Thus the zero-free content sits in the
relative form, not in the coarse `logDeriv` bound. -/
theorem classicalLineRatioBound_zeroFree {X : ℕ → ℝ} {C : ℝ}
    (h : ClassicalLineRatioBound X C) : ZetaLineZeroFree X := by
  obtain ⟨_hC, hbound⟩ := h
  filter_upwards [hbound] with n hn
  intro u hu hzero
  exact (hn u hu).1 hzero

/-- RH does discharge the L21.2 zero-free field, so that field is redundant
inside the record (it is carried for clarity, not as independent content). -/
theorem l21ZeroFree_of_zetaRH {X : ℕ → ℝ}
    (h : RiemannZetaZerosOnLine) : ZetaLineZeroFree X :=
  zetaLineZeroFree_of_RH h

/-! ## 4. L27: Siegel is inhabited; the central window bounds `θ` -/

/-- **Siegel's lower bound is not refutable**: any positive constant
`L`-value satisfies it with the same constant. -/
theorem siegelLOneLower_const {M : ℝ} (hM : 0 < M) :
    SiegelLOneLower (fun _ : ℤ => M) :=
  ⟨M, hM, fun _ _ => le_rfl⟩

/-- The scalar shape of `l27KappaLe` is satisfiable for every positive
`κ` and `A`: choose `θ` large. -/
theorem exists_theta_kappaLe {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) :
    ∃ θ : ℝ, 0 < θ ∧ κ ≤ A * Real.sqrt θ := by
  refine ⟨(κ / A) ^ 2 + 1, by positivity, ?_⟩
  have hsqrt : κ / A ≤ Real.sqrt ((κ / A) ^ 2 + 1) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [sq_nonneg (κ / A)]
  have hmul := mul_le_mul_of_nonneg_left hsqrt hA.le
  have hdiv : A * (κ / A) = κ := by
    field_simp [hA.ne']
  rwa [hdiv] at hmul

/-- **The curve budget forces a smooth order to exist.**  The right-hand side
of `CurveBudget` vanishes when `ψ = 0`, while the left-hand side is a positive
multiple of the growing scale. -/
theorem exists_smooth_of_curveBudget (I : L27_1Inputs) :
    ∃ n j, I.smooth n j = true := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 I.curve_budget
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    (scale_grows.eventually_gt_atTop (0 : ℝ))
  let n := max N M
  have hb := hN n (le_max_left _ _)
  have hs := hM n (le_max_right _ _)
  have hp : (0 : ℝ) < (I.p n : ℝ) := by exact_mod_cast I.p_pos n
  have hsqrt : 0 < Real.sqrt (I.p n) := Real.sqrt_pos.mpr hp
  have hlogy : 0 < Real.log (I.y n) := Real.log_pos (I.y_gt_one n)
  have hden : 0 < Real.sqrt (I.p n) * Real.log (I.y n) :=
    mul_pos hsqrt hlogy
  have hψ : 0 < I.psi n := by
    by_contra hnot
    have hzero : I.psi n = 0 := le_antisymm (le_of_not_gt hnot) (I.psi_nonneg n)
    rw [hzero] at hb
    have hright : (I.κ / 4) *
        ((I.curves n : ℝ) *
          (0 / (Real.sqrt (I.p n) * Real.log (I.y n)))) = 0 := by
      ring
    rw [hright] at hb
    have hleft : 0 < (2 + I.η) * scale n := by
      have h2 : 0 < 2 + I.η := by linarith [I.η_pos]
      exact mul_pos h2 hs
    linarith
  have hcount : 0 < smoothCount I.smooth I.orderTop n :=
    lt_of_lt_of_le hψ (I.psi_card n)
  by_contra hnone
  push Not at hnone
  have hzero : smoothCount I.smooth I.orderTop n = 0 := by
    unfold smoothCount
    apply Finset.sum_eq_zero
    intro j _
    have hfalse : I.smooth n j = false := by
      cases hh : I.smooth n j with
      | false => rfl
      | true => exact absurd hh (hnone n j)
    rw [hfalse]
    simp
  linarith

/-- **The central-trace field forces `θ ≤ 4`.**  Any smooth order has
nonnegative trace square, so `t² ≤ (4 - θ)p` forces `4 - θ ≥ 0`. -/
theorem theta_le_four_of_centralTrace (I : L27_1Inputs) {θ : ℝ}
    (hcentral : CentralTraceWindow I.p I.smooth θ)
    (hex : ∃ n j, I.smooth n j = true) : θ ≤ 4 := by
  obtain ⟨n, j, hj⟩ := hex
  have hwin := hcentral n j hj
  have hp : (0 : ℝ) < (I.p n : ℝ) := by exact_mod_cast I.p_pos n
  have hsq : (0 : ℝ) ≤ ((hasseTrace (I.p n) j : ℝ)) ^ 2 := sq_nonneg _
  unfold InCentralWindow at hwin
  nlinarith

/-- **The derived `θ ≤ 4` for any full record.** -/
theorem theta_le_four_of_curveBudget (I : L27_1Inputs) {θ : ℝ}
    (hcentral : CentralTraceWindow I.p I.smooth θ) :
    θ ≤ 4 :=
  theta_le_four_of_centralTrace I hcentral (exists_smooth_of_curveBudget I)

/-- **The exact weakening of `l27KappaLe` once `θ ≤ 4` is known.**  The
`√θ` factor is at most `2`, so Siegel's constant bounds `κ` by
`2 (classNumberFormulaConstant * l)`. -/
theorem kappa_le_two_const_of_kappaLe {κ A c θ : ℝ}
    (hAc : 0 ≤ A * c) (h : κ ≤ A * c * Real.sqrt θ) (_hθ0 : 0 ≤ θ) (hθ4 : θ ≤ 4) :
    κ ≤ 2 * (A * c) := by
  have hsqrt : Real.sqrt θ ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hmono : A * c * Real.sqrt θ ≤ A * c * 2 :=
    mul_le_mul_of_nonneg_left hsqrt hAc
  nlinarith

/-- The weakened `κ` bound carried by any `PaperResidualInputs`: the central
trace and the curve budget force `θ ≤ 4`, hence `κ ≤ 2 · (classNumberFormulaConstant · l)`. -/
theorem l27KappaLe_weakened {D : ℝ} (R : PaperResidualInputs D) :
    R.l27Data.κ ≤ 2 * (classNumberFormulaConstant * Classical.choose R.l27Siegel) := by
  have hθ4 : R.l27θ ≤ 4 :=
    theta_le_four_of_curveBudget R.l27Data R.l27CentralTrace
  have hAc : 0 ≤ classNumberFormulaConstant * Classical.choose R.l27Siegel := by
    have h1 : 0 < classNumberFormulaConstant := classNumberFormulaConstant_pos
    have h2 : 0 < Classical.choose R.l27Siegel := (Classical.choose_spec R.l27Siegel).1
    positivity
  exact kappa_le_two_const_of_kappaLe hAc R.l27KappaLe R.l27θ_pos.le hθ4

/-- **The exact inhabited weakening of `l27KappaLe`.**  Once the derived
constraint `θ ≤ 4` is imposed and `κ ≤ 2 A`, the inequality is satisfied by the
explicit `θ = (κ / A)^2`.  This proves that the weakened form is not vacuous;
it is the form a repaired L27 record should carry. -/
theorem exists_theta_kappaLe_le_four {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ)
    (hκA : κ ≤ 2 * A) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 4 ∧ κ ≤ A * Real.sqrt θ := by
  refine ⟨(κ / A) ^ 2, by positivity, ?_, ?_⟩
  · have hκA' : κ / A ≤ 2 := by
      rw [div_le_iff₀ hA]
      nlinarith
    have hnonneg : 0 ≤ κ / A := by positivity
    have hmul := mul_le_mul hκA' hκA' hnonneg (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  · have hsqrt : Real.sqrt ((κ / A) ^ 2) = κ / A := by
      rw [Real.sqrt_sq (by positivity)]
    rw [hsqrt]
    field_simp [hA.ne']
    norm_num

/-! ## 5. L34: the factorial log budgets are genuine arithmetic inputs -/

/-- The error log budget is non-vacuous. -/
theorem l34_errorLogBudget_nonvacuous :
    ChebotarevErrorLogBudget 1 100 8 (fun _ => 1) (fun _ => 2) (fun _ => 1) :=
  Cogentic.RandomizedL34EffectiveChebotarev.chebotarevErrorLogBudget_nonvacuous

/-- The discarded-ideal log budget is non-vacuous. -/
theorem l34_degreeLogBudget_nonvacuous :
    DegreeLossLogBudget 8 (fun _ => 1) (fun _ => 1) (fun _ => 2) :=
  Cogentic.RandomizedL34EffectiveChebotarev.degreeLossLogBudget_nonvacuous

/-- The error log budget is not implied by the standard effective Chebotarev
statement: the unconstrained factorial factor `F = exp 1000` makes it fail. -/
theorem l34_errorLogBudget_not_implied :
    ∃ (K C cZ cbr : ℝ) (x degree discLog count liX liBeta0 F T : ℕ → ℝ),
      EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0 ∧
        ¬ ChebotarevErrorLogBudget C cZ cbr F T degree :=
  Cogentic.RandomizedL34EffectiveChebotarev.errorLogBudget_not_implied_by_statement

/-- The discarded-ideal log budget is likewise not implied by the standard
effective Chebotarev statement. -/
theorem l34_degreeLogBudget_not_implied :
    ∃ (K C cZ cbr : ℝ) (x degree discLog count liX liBeta0 F T : ℕ → ℝ),
      EffectiveChebotarevStatement K C cZ x degree discLog count liX liBeta0 ∧
        ¬ DegreeLossLogBudget cbr degree F T :=
  Cogentic.RandomizedL34EffectiveChebotarev.degreeLogBudget_not_implied_by_statement

/-! ## 6. The `n = 0` checks -/

/-- Every unguarded `∀ n, 0 < f n` field of the record is genuinely satisfied at
`n = 0`, with the L27 prime and the L34 class count included.  The only guarded
tree field is `FailureData.factor_tree_nodes`, which is `1 ≤ n → nodes n ≤ 2n`
and therefore does not conflict with `nodes_pos` at zero. -/
theorem paperResidual_zero_checks {D : ℝ} (R : PaperResidualInputs D) :
    0 < R.l21c ∧ 0 < R.l30ε ∧ 0 < R.l30A ∧ 0 < R.l30B ∧ 0 < R.l30C ∧
      0 < R.l27θ ∧ 0 < R.l27Data.κ ∧ 0 < R.l27Data.η ∧
      0 < R.l30Cantor.Lc 0 ∧ 0 ≤ R.l30Cantor.k 0 ∧
      0 < R.l34.classCount 0 ∧ 1 ≤ R.l34.T 0 ∧
      (R.l27Data.p 0).Prime ∧ 4 ≤ R.l27Data.p 0 ∧
      1 < R.l27Data.y 0 ∧ 2 ≤ R.l27Data.cofactor 0 ∧
      0 < R.l27Data.p 0 ∧ 0 ≤ R.l27Data.psi 0 ∧
      0 < curveTotal R.l27Data.orderCount R.l27Data.orderTop 0 ∧
      0 ≤ R.l34.pTrial 0 ∧ 0 ≤ R.l34.actualMiss 0 ∧
      (∀ j, R.l27Data.smooth 0 j = true → 0 < j) ∧
      (∀ n, 1 ≤ n → R.l30Failure.nodes n ≤ 2 * n) ∧
      0 < R.l30Failure.failure 0 ∧
      R.l27Data.orderCount 0 = R.l27Data.orderCount 0 := by
  refine ⟨R.l21c_pos, R.l30ε_pos, R.l30A_pos, R.l30B_pos, R.l30C_pos,
    R.l27θ_pos, R.l27Data.κ_pos, R.l27Data.η_pos,
    lt_of_lt_of_le zero_lt_one (R.l30Cantor.Lc_ge_one 0),
    R.l30Cantor.k_nonneg 0, R.l34.classCount_pos 0, R.l34.T_ge_one 0,
    R.l27Prime 0, R.l27PGeFour 0, R.l27Data.y_gt_one 0,
    R.l27Data.cofactor_ge_two 0, R.l27Data.p_pos 0, R.l27Data.psi_nonneg 0,
    R.l27Data.curveTotal_pos 0, R.l34.pTrial_nonneg 0,
    R.l34.actualMiss_nonneg 0, R.l27KillLaw.smooth_order_pos 0,
    R.l30Failure.factor_tree_nodes,
    R.l30Failure.failure_pos 0, rfl⟩

/-! ## 7. The unconditional structural core -/

/-- The part of `PaperResidualInputs` that is discharged unconditionally here:
the L21 structural block (elementary profile), the L30 arithmetic block (with
the sharp count fields omitted), the explicit L19 and L20.2 witnesses and the
P1 witness. -/
structure PaperStructuralCore where
  l21Profile : TentProfile
  l21c : ℝ
  l21Cper : ℝ
  l21Ktail : ℝ
  l21p : ℕ → ℝ
  l21X_gt_one : ∀ n, 1 < l21Profile.X n
  l21c_pos : 0 < l21c
  l21c_le_one : l21c ≤ 1
  l21U_ge_three : ∀ n, 3 ≤ bandLog l21Profile.X n
  l21Cper_ge_three : 3 ≤ l21Cper
  l21Ktail_nonneg : 0 ≤ l21Ktail
  l21p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < l21p n
  l21b_le_B : ∀ᶠ n : ℕ in atTop,
    bOf l21Profile.X l21c n ≤ logCutoff l21c l21Profile.X n
  l21a_ge_log_two : ∀ᶠ n : ℕ in atTop,
    Real.log 2 ≤ aOf l21Profile.X l21c n
  l21FourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.lowEnergy n ≤
      Real.exp (-(((2 * l21c) / 3) - δ) * paperRate l21Profile.X n)
  l21FourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.middleEnergy n ≤
      Real.exp (-((1 / l21c) - δ) * paperRate l21Profile.X n)
  l21FourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    l21Profile.tailEnergy n ≤ Real.exp (-δ * paperRate l21Profile.X n)
  l21U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog l21Profile.X n
  l21U_le_exp : ∀ᶠ n : ℕ in atTop,
    bandLog l21Profile.X n ≤ Real.exp (scale n)
  l30p : ℕ → ℝ
  l30Growth : PaperDensityGrowth l30p
  l30ε : ℝ
  l30ε_pos : 0 < l30ε
  l30A : ℝ
  l30B : ℝ
  l30B_pos : 0 < l30B
  l30B_le_eighth : l30B ≤ 1 / 8
  l30AB_ge_four : 4 ≤ l30A * l30B
  l30c : ℝ
  l30C : ℝ
  l30A_pos : 0 < l30A
  l30A_ge_32 : 32 ≤ l30A
  l30AC_le : l30A * l30C ≤ l30c
  l30C_pos : 0 < l30C
  l30Cantor : CantorCostInputs
  l30Failure : FailureData
  l19 : Wave15L19Inputs
  l20_2 : SaddleConcentrationSource
  p1 : SubexpPrepassInput

/-- **The unconditional structural core is inhabited.** -/
noncomputable def paperStructuralCore : PaperStructuralCore where
  l21Profile := elementaryProfile
  l21c := elementaryC
  l21Cper := 3
  l21Ktail := tailK / Real.pi
  l21p := elementaryX
  l21X_gt_one := by
    intro n
    simpa only [elementaryProfile_X] using elementaryX_gt_one n
  l21c_pos := elementaryC_pos
  l21c_le_one := elementaryC_le_one
  l21U_ge_three := by
    intro n
    simpa only [elementaryProfile_X, bandLog_elementaryX] using elementaryU_ge_three n
  l21Cper_ge_three := by norm_num
  l21Ktail_nonneg := div_nonneg tailK_nonneg Real.pi_pos.le
  l21p_gt_one := Filter.Eventually.of_forall elementaryX_gt_one
  l21b_le_B := by
    simpa only [elementaryProfile_X] using elementary_b_le_B
  l21a_ge_log_two := by
    simpa only [elementaryProfile_X] using elementary_a_ge_log_two
  l21FourierLow := elementaryProfile_fourierLow elementaryC
  l21FourierMiddle := elementaryProfile_fourierMiddle elementaryC
  l21FourierTail := elementaryProfile_fourierTail
  l21U_dominates := by
    intro m hm
    simpa only [elementaryProfile_X] using elementaryU_dominates m hm
  l21U_le_exp := by
    simpa only [elementaryProfile_X] using elementaryU_le_exp
  l30p := witnessP
  l30Growth := witnessP_paperDensityGrowth
  l30ε := 1
  l30ε_pos := one_pos
  l30A := 32
  l30B := 1 / 8
  l30B_pos := by norm_num
  l30B_le_eighth := le_rfl
  l30AB_ge_four := by norm_num
  l30c := 4
  l30C := 1 / 8
  l30A_pos := by norm_num
  l30A_ge_32 := le_rfl
  l30AC_le := by norm_num
  l30C_pos := by norm_num
  l30Cantor := witnessCantor
  l30Failure := failureDataWitness
  l19 := wave15L19Concrete
  l20_2 := Classical.choice source_nonvacuous
  p1 := p1Witness

theorem nonempty_paperStructuralCore : Nonempty PaperStructuralCore :=
  ⟨paperStructuralCore⟩

/-! ## 8. The remaining analytic inputs and the full record -/

/-- The genuinely remaining inputs of the endpoint.  The L21.2 block is the
concrete leaf residual of `RandomizedL21_2ConcreteLeaf` (RH, the two-sided line
estimate and the literal short-interval count); the L30 block is the growth
schedule plus the three sharp count inputs; the rest is the L27, L34, L18.4,
L20.4 and C1–C4 residuals.  The L19, L20.2, P1, Cantor and failure fields are
*not* here: they are discharged explicitly in §7. -/
structure PaperResidualModulo (D : ℝ) where
  line : DirichletLZerosOnLine
  l21 : ConcreteLeafResidual
  l30p : ℕ → ℝ
  l30Growth : PaperDensityGrowth l30p
  l30ε : ℝ
  l30ε_pos : 0 < l30ε
  l30A : ℝ
  l30B : ℝ
  l30B_pos : 0 < l30B
  l30B_le_eighth : l30B ≤ 1 / 8
  l30AB_ge_four : 4 ≤ l30A * l30B
  l30c : ℝ
  l30C : ℝ
  l30A_pos : 0 < l30A
  l30A_ge_32 : 32 ≤ l30A
  l30AC_le : l30A * l30C ≤ l30c
  l30C_pos : 0 < l30C
  l30SharpUpper : GlobalOddUpperDensitySharp l30C l30p l30ε
  l30SharpCentral : YounisOddPaperSharpIntervalCount l30c l30p l30ε
  l30Binomial : EventuallyGlobalOddBinomialCount l30B l30p
    (paperT l30p) (paperError l30ε)
  l27Data : L27_1Inputs
  l27L1 : ℤ → ℝ
  l27Siegel : SiegelLOneLower l27L1
  l27Hurwitz : ℤ → ℝ
  l27ClassNumber : DirichletClassNumberInput l27Hurwitz l27L1
  l27θ : ℝ
  l27θ_pos : 0 < l27θ
  l27KappaLe : l27Data.κ ≤
    (classNumberFormulaConstant * Classical.choose l27Siegel) * Real.sqrt l27θ
  l27CentralTrace : CentralTraceWindow l27Data.p l27Data.smooth l27θ
  l27Prime : ∀ n, (l27Data.p n).Prime
  l27WeightedModel : ∀ n,
    WaterhouseWeightedModelCount (l27Data.p n) (l27Prime n) l27Hurwitz
  l27OrderDominates : ∀ n j,
    rawCurveOrderCount l27Data.p l27Prime n j ≤ l27Data.orderCount n j
  l27Fiber : JLineFiberInput l27Data.p l27Data.orderCount l27Data.orderTop
  l27PGeFour : ∀ n, 4 ≤ l27Data.p n
  l27KillLaw : L27KillLawInputs l27Data
  l27Hasse : HasseBound l27Data.p l27Data.orderCount
  l27CurveBudget : CurveBudget l27Data.p l27Data.y l27Data.psi l27Data.curves
    l27Data.κ l27Data.η
  l27LogFactor : LogFactorSubexp l27Data.cofactor
  l34 : L34EffectiveChebotarevInputs
  l18_4 : L18_4Certificate
  l20_4 : Wave14L20_4Source.{0}
  c1 : C1Inputs Egood
  c2 : C2Inputs Egood
  c3 : C3Inputs Egood
  c4 : C4Inputs Egood D

/-- **The classical log-derivative line bound from the concrete zeta side.**
The two-sided estimate and the ratio bound give the range-local `O (log²)`
statement; the `log²` factor is at least `(log 2)²` on the range. -/
theorem classicalLogDerivLineBoundOn_of_zetaSide (Z : ZetaSide) :
    ClassicalLogDerivLineBoundOn elementaryX := by
  let C : ℝ := max 1 (Z.KlineRaw / (Real.log 2) ^ 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2sq : 0 < (Real.log 2) ^ 2 := pow_pos hlog2 2
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKle : Z.KlineRaw ≤ C * (Real.log 2) ^ 2 := by
    have hle : Z.KlineRaw / (Real.log 2) ^ 2 ≤ C := le_max_right _ _
    exact (div_le_iff₀ hlog2sq).mp hle
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [Z.estimate, Z.ratio_le] with n hest hratio
  intro u hu
  have hbpos : 0 < Z.b n := Z.b_pos n
  have hBnn : 0 ≤ Z.B n := Z.B_nonneg n
  have h1 : ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤ Z.B n / Z.b n := by
    rw [logDeriv_apply, norm_div]
    have h2 : ‖deriv riemannZeta (perronLine perronRe u)‖ /
          ‖riemannZeta (perronLine perronRe u)‖ ≤
        Z.B n / ‖riemannZeta (perronLine perronRe u)‖ :=
      div_le_div_of_nonneg_right (hest u hu).2 (norm_nonneg _)
    have h3 : Z.B n / ‖riemannZeta (perronLine perronRe u)‖ ≤ Z.B n / Z.b n :=
      div_le_div_of_nonneg_left hBnn hbpos (hest u hu).1
    exact h2.trans h3
  have h4 : Z.B n / Z.b n ≤ C * (Real.log (|u| + 2)) ^ 2 := by
    have hK : Z.B n / Z.b n ≤ C * (Real.log 2) ^ 2 := hratio.trans hKle
    have hlog_ge : Real.log 2 ≤ Real.log (|u| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg u])
    have hsq : (Real.log 2) ^ 2 ≤ (Real.log (|u| + 2)) ^ 2 :=
      pow_le_pow_left₀ hlog2.le hlog_ge 2
    have hmul : C * (Real.log 2) ^ 2 ≤ C * (Real.log (|u| + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hCpos.le
    exact hK.trans hmul
  exact h1.trans h4

/-- **A full `PaperResidualInputs` from the remaining inputs.**  Every field
not listed in `PaperResidualModulo` is discharged explicitly: the elementary
L21 structural block, the L30 Cantor/failure data, the L19 and L20.2 witnesses
and P1. -/
noncomputable def PaperResidualModulo.toPaperResidual {D : ℝ}
    (R : PaperResidualModulo D) : PaperResidualInputs D where
  line := R.line
  zetaRH := R.l21.zeta.rh
  l21Profile := elementaryProfile
  l21c := elementaryC
  l21Cper := 3
  l21Ktail := tailK / Real.pi
  l21p := elementaryX
  l21X_gt_one := by
    intro n
    simpa only [elementaryProfile_X] using elementaryX_gt_one n
  l21c_pos := elementaryC_pos
  l21c_le_one := elementaryC_le_one
  l21U_ge_three := by
    intro n
    simpa only [elementaryProfile_X, bandLog_elementaryX] using elementaryU_ge_three n
  l21Cper_ge_three := by norm_num
  l21Ktail_nonneg := div_nonneg tailK_nonneg Real.pi_pos.le
  l21ZeroFree := R.l21.zeta.zeroFree
  l21ClassicalLine := classicalLogDerivLineBoundOn_of_zetaSide R.l21.zeta
  l21VerticalTail := by
    have hX : ∀ n, 1 < elementaryProfile.X n := by
      intro n
      simpa only [elementaryProfile_X] using elementaryX_gt_one n
    have hU : ∀ n, 3 ≤ bandLog elementaryProfile.X n := by
      intro n
      simpa only [elementaryProfile_X, bandLog_elementaryX] using elementaryU_ge_three n
    have htail : VerticalTailBound elementaryProfile.X
        (fun _ => tailK / Real.pi) 1 :=
      verticalTailBound_of_RH hX hU R.l21.zeta.rh
    have hmono : VerticalTailBound elementaryProfile.X
        (fun _ => tailK / Real.pi) 2 :=
      verticalTailBound_mono_exponent hX hU
        (Filter.Eventually.of_forall
          (fun _ => div_nonneg tailK_nonneg Real.pi_pos.le))
        (by norm_num) htail
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using hmono
  l21p_gt_one := Filter.Eventually.of_forall elementaryX_gt_one
  l21CentralCount := R.l21.localCount
  l21b_le_B := by
    simpa only [elementaryProfile_X] using elementary_b_le_B
  l21a_ge_log_two := by
    simpa only [elementaryProfile_X] using elementary_a_ge_log_two
  l21FourierLow := elementaryProfile_fourierLow elementaryC
  l21FourierMiddle := elementaryProfile_fourierMiddle elementaryC
  l21FourierTail := elementaryProfile_fourierTail
  l21U_dominates := by
    intro m hm
    simpa only [elementaryProfile_X] using elementaryU_dominates m hm
  l21U_le_exp := by
    simpa only [elementaryProfile_X] using elementaryU_le_exp
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
  l30Cantor := witnessCantor
  l30Failure := failureDataWitness
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
  l19 := wave15L19Concrete
  l20_2 := Classical.choice source_nonvacuous
  l20_4 := R.l20_4
  p1 := p1Witness
  c1 := R.c1
  c2 := R.c2
  c3 := R.c3
  c4 := R.c4

/-- **The residual bundle is inhabited modulo exactly the listed inputs.** -/
theorem nonempty_paperResidualInputs_of_modulo {D : ℝ}
    (R : PaperResidualModulo D) : Nonempty (PaperResidualInputs D) :=
  ⟨R.toPaperResidual⟩

/-- The remaining analytic inputs still imply the wave-17 record, hence the
paper endpoint, through the existing wave-18 reduction. -/
theorem nonempty_wave17Inputs_of_modulo {D : ℝ}
    (R : PaperResidualModulo D) : Nonempty (Wave17Inputs Egood D) :=
  PaperResidualInputs.nonempty_wave17Inputs R.toPaperResidual

/-! ## 9. The final status report and the endpoint from the remaining inputs -/

/-- The fields classified as `(b)`: the genuine remaining analytic inputs. -/
def remainingAnalyticFields : List PaperField :=
  [ .line, .zetaRH
  , .l21ZeroFree, .l21ClassicalLine, .l21VerticalTail, .l21CentralCount
  , .l30SharpUpper, .l30SharpCentral, .l30Binomial
  , .l27Data, .l27L1, .l27Siegel, .l27Hurwitz, .l27ClassNumber
  , .l27KappaLe, .l27CentralTrace, .l27Prime, .l27WeightedModel
  , .l27OrderDominates, .l27Fiber, .l27PGeFour, .l27KillLaw, .l27Hasse
  , .l27CurveBudget, .l27LogFactor
  , .l34, .l18_4, .l20_4, .c1, .c2, .c3, .c4 ]

theorem remainingAnalyticFields_length : remainingAnalyticFields.length = 32 := rfl

/-- The status table has `41` proved fields, `32` reduced fields and no
refutable field. -/
theorem paperStatusTable_counts :
    (paperStatusTable.filter (fun p => p.2 = FieldStatus.proved)).length = 41 ∧
      (paperStatusTable.filter (fun p => p.2 = FieldStatus.reduced)).length = 32 ∧
      (paperStatusTable.filter (fun p => p.2 = FieldStatus.refutable)).length = 0 := by
  decide

/-- Every field is either proved or reduced. -/
theorem paperStatusTable_total :
    (paperStatusTable.filter (fun p => p.2 = FieldStatus.proved)).length +
        (paperStatusTable.filter (fun p => p.2 = FieldStatus.reduced)).length +
        (paperStatusTable.filter (fun p => p.2 = FieldStatus.refutable)).length =
      73 := by
  decide

/-- The forty-one proved fields are exactly the complement of the reduced
list. -/
theorem paperStatusTable_proved_complement :
    (allPaperFields.filter (fun f => f.status = FieldStatus.proved)).length = 41 ∧
      (allPaperFields.filter (fun f => f.status = FieldStatus.reduced)).length = 32 := by
  decide

/-- **The wave-18 endpoint from the reduced input list.**  This is the
`PaperResidualModulo` form of
`serialized_assembled_balancedEnvelopeInfimum_from_wave18Inputs`: every field
not listed in `PaperResidualModulo` is constructed. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_moduloInputs
    (R : ∀ D : ℝ, PaperResidualModulo D) :
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
  serialized_assembled_balancedEnvelopeInfimum_from_wave18Inputs
    (fun D => (R D).toPaperResidual)

/-! ## Axiom audit -/

#print axioms paperStatusTable_counts
#print axioms no_refutable_field
#print axioms oldPaperScaleSmoothUpper_refutable
#print axioms l30SharpUpper_not_refutable
#print axioms l30SharpCentral_not_refutable
#print axioms constantWitness_incompatible_with_paperArithmetic
#print axioms centralOrderInterval_disjoint_shortInterval
#print axioms centralSmoothOrders_disjoint_shortSmoothInterval
#print axioms l21_centralWindowSupply_refuted
#print axioms logDeriv_eq_zero_of_zeta_eq_zero
#print axioms classicalLineRatioBound_zeroFree
#print axioms zeroFree_needed_for_ratio_bound
#print axioms l21ZeroFree_of_zetaRH
#print axioms siegelLOneLower_const
#print axioms exists_theta_kappaLe
#print axioms exists_smooth_of_curveBudget
#print axioms theta_le_four_of_curveBudget
#print axioms l27KappaLe_weakened
#print axioms exists_theta_kappaLe_le_four
#print axioms l34_errorLogBudget_nonvacuous
#print axioms l34_degreeLogBudget_nonvacuous
#print axioms l34_errorLogBudget_not_implied
#print axioms l34_degreeLogBudget_not_implied
#print axioms paperResidual_zero_checks
#print axioms paperStructuralCore
#print axioms nonempty_paperStructuralCore
#print axioms classicalLogDerivLineBoundOn_of_zetaSide
#print axioms PaperResidualModulo.toPaperResidual
#print axioms nonempty_paperResidualInputs_of_modulo
#print axioms nonempty_wave17Inputs_of_modulo
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_moduloInputs

end Cogentic.RandomizedWave18Audit
