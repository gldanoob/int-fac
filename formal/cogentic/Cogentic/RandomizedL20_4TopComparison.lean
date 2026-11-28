import Cogentic.RandomizedL20_4LeafAssembly

/-!
# L20.4 top comparison: `PaperTopComparison` from the factored G.12 input

`Cogentic.RandomizedL20_4LeafAssembly` defines the paper top comparison as the
depth form

`PaperTopComparison S` :
`S.top ≤ S.Ctop √(step^L (δ_L + L(η + ε_rat))) + S.Ctop √(ε_in) + S.Ctop η`

and records in `paperTopComparison_of_comparison` that the *factored* G.12
comparison

`TopG12Comparison S.top S.Ctop S.interior ε_in η` :
`S.top ≤ S.Ctop (√(δ_0) + √(ε_in) + η)`

implies it through the G.11 recurrence.  That field, however, is stored inside
`SourcedTopData`, so the leaf assembly can only be instantiated by *assuming*
the depth form.

This file removes that circularity.  The recurrence data (depth `L`, interior
masses `δ_i`, step multiplier, nonnegativity, depth bound, `D^{O(1)}` constant,
and the base/eta/rational/incoming sources packaged by
`PaperExceptionSources`) are collected in `TopRecurrenceData` **without** any
top comparison.  The single remaining analytic input is then isolated as the
explicit `Prop`

`TopComparisonInput S` := `TopG12Comparison S.top S.Ctop S.interior ε_in η`.

The reduction chain is

* `TopComparisonInput S` (factored G.12, the paper's KeyBreak estimate);
* `additiveDepth_of_input` : the G.11 recurrence turns it into
  `TopG12AdditiveDepthComparison` at the explicit majorant
  `step^L (δ_L + L(η + ε_rat))`, with `Ctop`, `η`, `ε_in` unchanged;
* `toSourcedTopData` / `paperTopComparison` : the resulting `SourcedTopData`
  satisfies `PaperTopComparison`;
* `subexpLoss` : hence `SubexpLoss S.top`.

Two finer inputs are also reduced, keeping the constants separate:

* `topComparisonInput_of_g54g55` derives the input from the componentwise
  G.54--G.55 comparison at `δ_0` once `Cint, Cin, Cell ≤ Ctop`;
* `paperTopComparison_of_componentwiseDepth` derives `PaperTopComparison`
  directly from the componentwise depth comparison
  `G54G55ThreeTermDepthComparison`, merging the three constants into `Ctop`
  only in the final step.

No `sorry`, `admit`, `axiom`, `native_decide`, and no loss is set to zero.
-/

namespace Cogentic.RandomizedL20_4TopComparison

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4Top
open Cogentic.RandomizedL20_4Additive
open Cogentic.RandomizedL20_4InteriorBase
open Cogentic.RandomizedL20_4EtaSource
open Cogentic.RandomizedL20_4LeafAssembly

/-! ## 1. The recurrence data, with no comparison baked in -/

/-- The G.11/G.12 recurrence data and the paper's base/eta/rational/incoming
sources, **without** the top comparison.  It is `SourcedTopData` with the
`additive_comparison` field removed: the only missing analytic ingredient is
supplied separately as `TopComparisonInput` (or one of its finer forms). -/
structure TopRecurrenceData where
  /-- Depth of the internal G.11 recurrence. -/
  L : ℕ
  /-- Internal normalized bad-child masses `δ_i`, `i = 0 … L`. -/
  interior : ℕ → ℕ → ℝ
  /-- G.11 step multiplier. -/
  step : ℕ → ℝ
  /-- Elliptic deletion fraction `η` (L21.2). -/
  eta : ℕ → ℝ
  /-- The paper sources: base, rational, elliptic and incoming. -/
  exceptions : PaperExceptionSources interior L eta
  /-- Resulting top bad-child mass `δ_top`. -/
  top : ℕ → ℝ
  /-- The G.12 top constant. -/
  Ctop : ℕ → ℝ
  /-- Exponent of the top constant. -/
  cTop : ℝ
  /-- Exponent of the depth factor. -/
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  /-- The G.11 linear recurrence. -/
  recurrence : G11InteriorRecurrence interior L step eta
    (fun n => paperEpsRat exceptions.rational n)
  /-- The step multiplier is at least one. -/
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  /-- The G.11 error is nonnegative. -/
  alpha_nonneg : ∀ᶠ n : ℕ in atTop,
    0 ≤ eta n + paperEpsRat exceptions.rational n
  /-- The depth factor is `D^{O(1)}`. -/
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  /-- The top constant is `D^{O(1)}`. -/
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)

/-! ## 2. The smallest remaining analytic input -/

/-- **The single remaining analytic input.**  It is literally the factored G.12
KeyBreak comparison `TopG12Comparison`, evaluated at the paper's incoming
exception.  The rational exception enters separately through the recurrence,
and `η` is the L21.2 elliptic fraction from `PaperExceptionSources`. -/
def TopComparisonInput (S : TopRecurrenceData) : Prop :=
  TopG12Comparison S.top S.Ctop S.interior
    (fun n => paperEpsIn S.exceptions.incoming n) S.eta

/-- The input is exactly the factored G.12 comparison: no new predicate is
introduced, so assuming it is not a strengthening of the paper's estimate. -/
theorem topComparisonInput_iff (S : TopRecurrenceData) :
    TopComparisonInput S ↔
      TopG12Comparison S.top S.Ctop S.interior
        (fun n => paperEpsIn S.exceptions.incoming n) S.eta :=
  Iff.rfl

/-! ## 3. Explicit recurrence and the depth majorant -/

/-- **The G.11 recurrence, made explicit.**  At every sufficiently large scale
the derived level `δ_0` is bounded by
`step^L (δ_L + L(η + ε_rat))`.  This is the only use of the recurrence in the
top step, and it keeps the step multiplier, the depth `L` and both error
fractions. -/
theorem eventually_interior_zero_le_depthMajorant (S : TopRecurrenceData) :
    ∀ᶠ n : ℕ in atTop,
      S.interior n 0 ≤
        S.step n ^ S.L *
          (S.interior n S.L +
            (S.L : ℝ) * (S.eta n + paperEpsRat S.exceptions.rational n)) := by
  filter_upwards [S.recurrence, S.step_ge_one, S.alpha_nonneg] with n hrec hstep hα
  exact internal_linear_recurrence_bound (S.interior n) S.L hstep hα hrec

/-- **The input at `δ_0` becomes the depth form at the explicit majorant.**
The G.11 recurrence replaces `√(δ_0)` by the larger
`√(step^L (δ_L + L(η + ε_rat)))`, so the right-hand side only contains base
data.  The constants `Ctop`, `η` and `ε_in` are untouched. -/
theorem additiveDepth_of_input (S : TopRecurrenceData) (h : TopComparisonInput S) :
    TopG12AdditiveDepthComparison S.top S.Ctop S.interior S.step S.eta
      (fun n => paperEpsRat S.exceptions.rational n)
      (fun n => paperEpsIn S.exceptions.incoming n) S.L :=
  topG12AdditiveDepth_of_comparison h S.recurrence S.step_ge_one S.alpha_nonneg
    (Eventually.of_forall S.Ctop_nonneg)

/-- The depth form is `PaperTopComparison` after the `SourcedTopData` wrapper is
stripped: the exact inequality proved by the reduction, with every constant
still explicit. -/
theorem additiveDepth_of_input_unfolded (S : TopRecurrenceData)
    (h : TopComparisonInput S) :
    ∀ᶠ n : ℕ in atTop,
      S.top n ≤
        S.Ctop n *
            Real.sqrt (S.step n ^ S.L *
              (S.interior n S.L +
                (S.L : ℝ) * (S.eta n + paperEpsRat S.exceptions.rational n))) +
          S.Ctop n * Real.sqrt (paperEpsIn S.exceptions.incoming n) +
          S.Ctop n * S.eta n :=
  additiveDepth_of_input S h

/-! ## 4. Realizing `SourcedTopData` and `PaperTopComparison` -/

/-- Build the `SourcedTopData` bundle from the recurrence data and *any*
explicit depth comparison.  This constructor is shared by the factored input
and by the componentwise depth input below. -/
noncomputable def toSourcedTopDataOfDepth (S : TopRecurrenceData)
    (h : TopG12AdditiveDepthComparison S.top S.Ctop S.interior S.step S.eta
      (fun n => paperEpsRat S.exceptions.rational n)
      (fun n => paperEpsIn S.exceptions.incoming n) S.L) : SourcedTopData where
  L := S.L
  interior := S.interior
  step := S.step
  eta := S.eta
  exceptions := S.exceptions
  top := S.top
  Ctop := S.Ctop
  cTop := S.cTop
  cInt := S.cInt
  interior_nonneg := S.interior_nonneg
  eta_nonneg := S.eta_nonneg
  top_nonneg := S.top_nonneg
  Ctop_nonneg := S.Ctop_nonneg
  cTop_nonneg := S.cTop_nonneg
  recurrence := S.recurrence
  step_ge_one := S.step_ge_one
  alpha_nonneg := S.alpha_nonneg
  depth_bound := S.depth_bound
  additive_comparison := h
  Ctop_le := S.Ctop_le

/-- Build the `SourcedTopData` from the factored G.12 input, the recurrence and
the paper's base/rational/eta sources. -/
noncomputable def toSourcedTopData (S : TopRecurrenceData)
    (h : TopComparisonInput S) : SourcedTopData :=
  toSourcedTopDataOfDepth S (additiveDepth_of_input S h)

/-- **`PaperTopComparison` from the explicit depth comparison.** -/
theorem paperTopComparison_of_depth (S : TopRecurrenceData)
    (h : TopG12AdditiveDepthComparison S.top S.Ctop S.interior S.step S.eta
      (fun n => paperEpsRat S.exceptions.rational n)
      (fun n => paperEpsIn S.exceptions.incoming n) S.L) :
    PaperTopComparison (toSourcedTopDataOfDepth S h) :=
  (toSourcedTopDataOfDepth S h).additive_comparison

/-- **`PaperTopComparison` from the factored G.12 input.**  This is the target
statement of the reduction: the only analytic hypothesis is `TopComparisonInput`
(`TopG12Comparison`); the recurrence and all sources come from `S`. -/
theorem paperTopComparison (S : TopRecurrenceData) (h : TopComparisonInput S) :
    PaperTopComparison (toSourcedTopData S h) :=
  paperTopComparison_of_depth S (additiveDepth_of_input S h)

/-! ## 5. The reduction chain to `SubexpLoss` -/

/-- **`SubexpLoss` from `PaperTopComparison`.**  Unlike the wrapper in
`RandomizedL20_4LeafAssembly`, this proof *consumes* the comparison: it feeds
the depth inequality to `top_subexp_of_additiveDepth` together with the four
`SubexpLoss` fields produced by the base/rational/eta sources. -/
theorem subexpLoss_of_paperTopComparison (S : SourcedTopData)
    (h : PaperTopComparison S) : SubexpLoss S.top := by
  have hsub := S.exceptions.subProps
  exact top_subexp_of_additiveDepth S.interior S.step S.eta
    (fun n => paperEpsRat S.exceptions.rational n)
    (fun n => paperEpsIn S.exceptions.incoming n)
    S.top S.Ctop S.cTop S.cInt
    S.interior_nonneg S.eta_nonneg (paperEpsRat_nonneg S.exceptions.rational)
    (paperEpsIn_nonneg S.exceptions.incoming) S.top_nonneg S.Ctop_nonneg
    S.cTop_nonneg S.recurrence S.step_ge_one S.alpha_nonneg S.depth_bound
    h S.Ctop_le hsub.base_subexp hsub.eta_subexp hsub.epsRat_subexp
    hsub.epsIn_subexp

/-- **The full chain `input → PaperTopComparison → SubexpLoss`.** -/
theorem subexpLoss_via_paperTopComparison (S : TopRecurrenceData)
    (h : TopComparisonInput S) : SubexpLoss S.top :=
  subexpLoss_of_paperTopComparison (toSourcedTopData S h) (paperTopComparison S h)

/-- **`SubexpLoss S.top` from the recurrence data and the factored input.** -/
theorem subexpLoss (S : TopRecurrenceData) (h : TopComparisonInput S) :
    SubexpLoss S.top :=
  (toSourcedTopData S h).top_subexp

/-! ## 6. Finer inputs keeping the three constants separate -/

/-- **The factored input from the componentwise G.54--G.55 comparison.**  The
three constants `Cint`, `Cin`, `Cell` are merged into `Ctop` only at this last
step; the componentwise estimates at `δ_0` are the finer analytic statement. -/
theorem topComparisonInput_of_g54g55 (S : TopRecurrenceData)
    {Cint Cin Cell : ℕ → ℝ}
    (h : G54G55ThreeTermComparison S.top Cint Cin Cell S.interior
      (fun n => paperEpsIn S.exceptions.incoming n) S.eta)
    (hInt : ∀ᶠ n : ℕ in atTop, Cint n ≤ S.Ctop n)
    (hIn : ∀ᶠ n : ℕ in atTop, Cin n ≤ S.Ctop n)
    (hEll : ∀ᶠ n : ℕ in atTop, Cell n ≤ S.Ctop n) :
    TopComparisonInput S :=
  topG12Comparison_of_g54g55 h hInt hIn hEll (Eventually.of_forall S.eta_nonneg)

/-- **The depth comparison from the componentwise depth form.**  This is the
version in which the G.11 recurrence has already been applied inside each
component; the three constants are merged into `Ctop` at the end. -/
theorem additiveDepth_of_componentwiseDepth (S : TopRecurrenceData)
    {Cint Cin Cell : ℕ → ℝ}
    (h : G54G55ThreeTermDepthComparison S.top Cint Cin Cell S.interior S.step S.eta
      (fun n => paperEpsRat S.exceptions.rational n)
      (fun n => paperEpsIn S.exceptions.incoming n) S.L)
    (hInt : ∀ᶠ n : ℕ in atTop, Cint n ≤ S.Ctop n)
    (hIn : ∀ᶠ n : ℕ in atTop, Cin n ≤ S.Ctop n)
    (hEll : ∀ᶠ n : ℕ in atTop, Cell n ≤ S.Ctop n) :
    TopG12AdditiveDepthComparison S.top S.Ctop S.interior S.step S.eta
      (fun n => paperEpsRat S.exceptions.rational n)
      (fun n => paperEpsIn S.exceptions.incoming n) S.L :=
  additiveDepth_of_g54g55Depth h hInt hIn hEll (Eventually.of_forall S.eta_nonneg)

/-- **`PaperTopComparison` from the componentwise depth input**, with the three
G.54--G.55 constants kept separate until the final merge into `Ctop`. -/
theorem paperTopComparison_of_componentwiseDepth (S : TopRecurrenceData)
    {Cint Cin Cell : ℕ → ℝ}
    (h : G54G55ThreeTermDepthComparison S.top Cint Cin Cell S.interior S.step S.eta
      (fun n => paperEpsRat S.exceptions.rational n)
      (fun n => paperEpsIn S.exceptions.incoming n) S.L)
    (hInt : ∀ᶠ n : ℕ in atTop, Cint n ≤ S.Ctop n)
    (hIn : ∀ᶠ n : ℕ in atTop, Cin n ≤ S.Ctop n)
    (hEll : ∀ᶠ n : ℕ in atTop, Cell n ≤ S.Ctop n) :
    PaperTopComparison
      (toSourcedTopDataOfDepth S
        (additiveDepth_of_componentwiseDepth S h hInt hIn hEll)) :=
  paperTopComparison_of_depth S
    (additiveDepth_of_componentwiseDepth S h hInt hIn hEll)

/-- **`SubexpLoss` from the componentwise depth input.** -/
theorem subexpLoss_of_componentwiseDepth (S : TopRecurrenceData)
    {Cint Cin Cell : ℕ → ℝ}
    (h : G54G55ThreeTermDepthComparison S.top Cint Cin Cell S.interior S.step S.eta
      (fun n => paperEpsRat S.exceptions.rational n)
      (fun n => paperEpsIn S.exceptions.incoming n) S.L)
    (hInt : ∀ᶠ n : ℕ in atTop, Cint n ≤ S.Ctop n)
    (hIn : ∀ᶠ n : ℕ in atTop, Cin n ≤ S.Ctop n)
    (hEll : ∀ᶠ n : ℕ in atTop, Cell n ≤ S.Ctop n) :
    SubexpLoss S.top :=
  (toSourcedTopDataOfDepth S
    (additiveDepth_of_componentwiseDepth S h hInt hIn hEll)).top_subexp

/-! ## Axiom audit -/

#print axioms topComparisonInput_iff
#print axioms eventually_interior_zero_le_depthMajorant
#print axioms additiveDepth_of_input
#print axioms additiveDepth_of_input_unfolded
#print axioms toSourcedTopDataOfDepth
#print axioms toSourcedTopData
#print axioms paperTopComparison_of_depth
#print axioms paperTopComparison
#print axioms subexpLoss_of_paperTopComparison
#print axioms subexpLoss_via_paperTopComparison
#print axioms subexpLoss
#print axioms topComparisonInput_of_g54g55
#print axioms additiveDepth_of_componentwiseDepth
#print axioms paperTopComparison_of_componentwiseDepth
#print axioms subexpLoss_of_componentwiseDepth

end Cogentic.RandomizedL20_4TopComparison
