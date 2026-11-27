import Cogentic.RandomizedL20_4Top

/-!
# L20.4 additive: the G.54--G.55 three-term comparison and its three constants

`Cogentic.RandomizedL20_4Top` states the G.54--G.55 Cauchy--Schwarz output as
the single additive inequality

`TopG12AdditiveThreeComparison top Cint Cin Cell interior epsIn eta` :
`top ≤ Cint √(interior 0) + Cin √(epsIn) + Cell η`,

and proves `TopG12Comparison` from it once the three constants are dominated by
`Ctop`.  The present file supplies the missing *upstream* step: the individual
G.54 reordering and G.55/Cauchy--Schwarz estimates from which that aggregate
inequality is obtained.

## 1. The G.54--G.55 component comparison

The paper's G.54 step reorders the top bad-child count into its formal
incidences.  In the private-dyad normalization it splits the normalized top
mass into three nonnegative contributions:

* the recursive internal child-bad contribution (the G.11 mass propagated to
  the top), bounded by `Cint √(interior 0)` after Cauchy--Schwarz;
* the incoming-rational exceptional contribution (G.55 together with the
  `O(1/q)` root probability and the rational second moment), bounded by
  `Cin √(epsIn)`;
* the elliptic deletion fraction (G.51/(G.55) applied to exceptional numerical
  child primes), bounded by `Cell η`.

`G54G55ThreeTermComparison` records exactly these three component estimates
plus the G.54 additive reordering.  It is *strictly finer* than
`TopG12AdditiveThreeComparison`: it bounds each contribution separately,
whereas the target only bounds their sum.  Consequently
`topG12AdditiveThreeComparison_of_g54g55` proves the target from the three
paper-level component estimates, and `topG12Comparison_of_g54g55` composes
with the existing G.12 constant reduction.

The component form is the smallest explicit three-constant inequality of this
shape: no term is dropped, no constant is set to one, and the three constants
remain independent.  `g54g55_of_comparison` shows that the one-constant G.12
display of the paper is the special case `Cint = Cin = Cell = C`, while
`topG12Comparison_iff_additiveThree` (from the parent file) shows that with a
common constant the aggregate form is literally `TopG12Comparison`.

## 2. The G.11 depth reduction

The internal term still refers to the derived level `interior 0`.  The G.11
linear recurrence bounds it by

`step^L * (interior L + L (η + ε_rat))`.

`G54G55ThreeTermDepthComparison` is the component comparison evaluated at this
explicit majorant.  The existing G.11 theorem
`internal_linear_recurrence_bound` gives it from the `δ₀` comparison
(`g54g55Depth_of_additiveThree`), with no loss of any constant:
`Cint` multiplies the larger square root.  The G.12 reduction
`topG12LinearComparison_of_additiveDepth` then gives the linear-majorant form
consumed by `G12TopInputs`.

## 3. Consumers

`G54G55ThreeTermData` packages the depth form with the same nonnegativity,
subexponential and depth-field data as `TopG12AdditiveData`; its
`toTopG12AdditiveData` realizes the existing bundle, so `top_subexp` follows
from `top_subexp_of_additiveDepth`.  The `δ₀` bundle
`G54G55ThreeTermComparisonData` instead realizes `TopG12ThreeData` (hence
`G12TopInputs`), so the derived `TopG12Comparison` is the same one used by the
existing top-end reduction.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero loss: the two exception
masses, the elliptic fraction and the internal mass all remain explicit, and
the three constants are never identified with one another.
-/

namespace Cogentic.RandomizedL20_4Additive

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4Top

/-! ## 1. The G.54 reordering and the three G.55 component estimates -/

/-- **G.54: the top bad-child count is dominated by the sum of its formal
incidences.**  The three terms are the recursive internal contribution, the
incoming-rational exceptional contribution and the elliptic deletion
contribution.  All three are retained; this is the exact reordering step,
written as a domination so that the subsequent count only has to be an upper
bound. -/
def G54G55TopDecomposition (top topInternal topIncoming topElliptic : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    top n ≤ topInternal n + topIncoming n + topElliptic n

/-- **G.11/Cauchy--Schwarz internal component.**  After the G.11 propagation,
the internal child-bad contribution is at most `Cint √(interior 0)`. -/
def G54G55InternalBound (topInternal Cint : ℕ → ℝ)
    (interior : ℕ → ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    topInternal n ≤ Cint n * Real.sqrt (interior n 0)

/-- **G.55 incoming-rational component.**  The incoming exceptional
contribution is at most `Cin √(epsIn)`, the Cauchy--Schwarz form of the G.55
one-point upper bound, the `O(1/q)` root probability and the rational second
moment. -/
def G54G55IncomingBound (topIncoming Cin epsIn : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    topIncoming n ≤ Cin n * Real.sqrt (epsIn n)

/-- **Elliptic deletion component.**  The elliptic exceptional fraction costs at
most `Cell η` in the normalized incidence count. -/
def G54G55EllipticBound (topElliptic Cell eta : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    topElliptic n ≤ Cell n * eta n

/-- **The G.54--G.55 three-term comparison, componentwise.**  This is the
smallest explicit three-constant inequality of the paper's shape: the G.54
reordering plus the three separate component estimates, with constants
`Cint`, `Cin`, `Cell`.  It is strictly finer than the aggregate
`TopG12AdditiveThreeComparison`, which only bounds the sum. -/
def G54G55ThreeTermComparison (top Cint Cin Cell : ℕ → ℝ)
    (interior : ℕ → ℕ → ℝ) (epsIn eta : ℕ → ℝ) : Prop :=
  ∃ topInternal topIncoming topElliptic : ℕ → ℝ,
    G54G55TopDecomposition top topInternal topIncoming topElliptic ∧
      G54G55InternalBound topInternal Cint interior ∧
      G54G55IncomingBound topIncoming Cin epsIn ∧
      G54G55EllipticBound topElliptic Cell eta

/-- **`TopG12AdditiveThreeComparison` from the componentwise G.54--G.55
comparison.**  The three component estimates are added and the G.54 reordering
is applied.  No term is dropped and the three constants stay independent. -/
theorem topG12AdditiveThreeComparison_of_g54g55
    {top Cint Cin Cell : ℕ → ℝ} {interior : ℕ → ℕ → ℝ} {epsIn eta : ℕ → ℝ}
    (h : G54G55ThreeTermComparison top Cint Cin Cell interior epsIn eta) :
    TopG12AdditiveThreeComparison top Cint Cin Cell interior epsIn eta := by
  obtain ⟨topInternal, topIncoming, topElliptic, hdec, hint, hin, hell⟩ := h
  filter_upwards [hdec, hint, hin, hell] with n hdec' hint' hin' hell'
  calc
    top n ≤ topInternal n + topIncoming n + topElliptic n := hdec'
    _ ≤ Cint n * Real.sqrt (interior n 0) + Cin n * Real.sqrt (epsIn n) +
        Cell n * eta n := add_le_add (add_le_add hint' hin') hell'

/-- **The one-constant G.12 display is the special case of equal constants.**
Taking `Cint = Cin = Cell = C` in the componentwise comparison reproduces the
paper's single-constant G.54--G.55 display, with the components exactly the
three summands.  This records that the three-constant form is the finer object,
not a weakening. -/
theorem g54g55_of_comparison
    {top C : ℕ → ℝ} {interior : ℕ → ℕ → ℝ} {epsIn eta : ℕ → ℝ}
    (h : TopG12Comparison top C interior epsIn eta) :
    G54G55ThreeTermComparison top C C C interior epsIn eta := by
  refine ⟨fun n => C n * Real.sqrt (interior n 0),
    fun n => C n * Real.sqrt (epsIn n), fun n => C n * eta n, ?_, ?_, ?_, ?_⟩
  · filter_upwards [h] with n hn
    calc
      top n ≤ C n * (Real.sqrt (interior n 0) + Real.sqrt (epsIn n) + eta n) := hn
      _ = C n * Real.sqrt (interior n 0) + C n * Real.sqrt (epsIn n) + C n * eta n := by
        ring
  · filter_upwards with n
    exact le_rfl
  · filter_upwards with n
    exact le_rfl
  · filter_upwards with n
    exact le_rfl

/-- **The aggregate three-constant form from the factored G.12 comparison.**
This is the equal-constant special case: the one-constant display is exactly the
componentwise G.54--G.55 estimate with `Cint = Cin = Cell = C`, followed by the
componentwise-to-aggregate reduction. -/
theorem topG12AdditiveThreeComparison_of_comparison
    {top C : ℕ → ℝ} {interior : ℕ → ℕ → ℝ} {epsIn eta : ℕ → ℝ}
    (h : TopG12Comparison top C interior epsIn eta) :
    TopG12AdditiveThreeComparison top C C C interior epsIn eta :=
  topG12AdditiveThreeComparison_of_g54g55 (g54g55_of_comparison h)

/-- **`TopG12Comparison` from the componentwise G.54--G.55 comparison.**  This
composes the target reduction with the existing G.12 domination step: if each
of the three constants is eventually at most `Ctop` and the elliptic fraction
is nonnegative, the top mass obeys the factored G.12 comparison. -/
theorem topG12Comparison_of_g54g55
    {top Ctop Cint Cin Cell : ℕ → ℝ} {interior : ℕ → ℕ → ℝ}
    {epsIn eta : ℕ → ℝ}
    (h : G54G55ThreeTermComparison top Cint Cin Cell interior epsIn eta)
    (hInt : ∀ᶠ n : ℕ in atTop, Cint n ≤ Ctop n)
    (hIn : ∀ᶠ n : ℕ in atTop, Cin n ≤ Ctop n)
    (hEll : ∀ᶠ n : ℕ in atTop, Cell n ≤ Ctop n)
    (hη : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n) :
    TopG12Comparison top Ctop interior epsIn eta :=
  topG12Comparison_of_additiveThree
    (topG12AdditiveThreeComparison_of_g54g55 h) hInt hIn hEll hη

/-- **The aggregate three-constant form is exactly the factored comparison once
the three constants coincide.**  This is the parent file's equivalence, recorded
here to identify the smallest three-constant object with `TopG12Comparison` in
the common-constant case. -/
theorem additiveThree_iff_comparison {top Ctop : ℕ → ℝ}
    {interior : ℕ → ℕ → ℝ} {epsIn eta : ℕ → ℝ} :
    TopG12AdditiveThreeComparison top Ctop Ctop Ctop interior epsIn eta ↔
      TopG12Comparison top Ctop interior epsIn eta :=
  topG12Comparison_iff_additiveThree

/-! ## 2. The G.11 depth form with three constants -/

/-- The G.54--G.55 component comparison evaluated at the explicit G.11 majorant
`step^L * (interior L + L (η + ε_rat))` instead of the derived level
`interior 0`.  The three constants remain separate. -/
def G54G55ThreeTermDepthComparison (top Cint Cin Cell : ℕ → ℝ)
    (interior : ℕ → ℕ → ℝ) (step eta epsRat epsIn : ℕ → ℝ) (L : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    top n ≤
      Cint n *
          Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) +
        Cin n * Real.sqrt (epsIn n) + Cell n * eta n

/-- **The depth form from the `δ₀` three-constant form.**  The G.11 linear
recurrence bounds `interior 0` by `step^L (interior L + L(η+ε_rat))`; monotonicity
of the square root and nonnegativity of `Cint` transfer the internal term.  The
incoming and elliptic terms are unchanged. -/
theorem g54g55Depth_of_additiveThree
    {top Cint Cin Cell : ℕ → ℝ} {interior : ℕ → ℕ → ℝ}
    {step eta epsRat epsIn : ℕ → ℝ} {L : ℕ}
    (h : TopG12AdditiveThreeComparison top Cint Cin Cell interior epsIn eta)
    (hrec : G11InteriorRecurrence interior L step eta epsRat)
    (hstep : ∀ᶠ n : ℕ in atTop, 1 ≤ step n)
    (hα : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n)
    (hCint : ∀ᶠ n : ℕ in atTop, 0 ≤ Cint n) :
    G54G55ThreeTermDepthComparison top Cint Cin Cell interior step eta epsRat epsIn L := by
  filter_upwards [h, hrec, hstep, hα, hCint] with n htop hrec' hstep' hα' hCint'
  have hmaj : interior n 0 ≤
      step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n)) :=
    internal_linear_recurrence_bound (interior n) L hstep' hα' hrec'
  have hsqrt : Real.sqrt (interior n 0) ≤
      Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) :=
    Real.sqrt_le_sqrt hmaj
  have hkey : Cint n * Real.sqrt (interior n 0) ≤
      Cint n * Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) :=
    mul_le_mul_of_nonneg_left hsqrt hCint'
  exact htop.trans (add_le_add (add_le_add hkey le_rfl) le_rfl)

/-- **The depth form directly from the factored G.12 comparison.**  The
one-constant comparison is the equal-constant componentwise estimate; the G.11
recurrence then gives the three-constant depth form with all constants `C`.
This is the shortest path from the paper's single-constant G.12 display to the
explicit base-level data. -/
theorem g54g55Depth_of_comparison
    {top C : ℕ → ℝ} {interior : ℕ → ℕ → ℝ}
    {step eta epsRat epsIn : ℕ → ℝ} {L : ℕ}
    (h : TopG12Comparison top C interior epsIn eta)
    (hrec : G11InteriorRecurrence interior L step eta epsRat)
    (hstep : ∀ᶠ n : ℕ in atTop, 1 ≤ step n)
    (hα : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n)
    (hC : ∀ᶠ n : ℕ in atTop, 0 ≤ C n) :
    G54G55ThreeTermDepthComparison top C C C interior step eta epsRat epsIn L :=
  g54g55Depth_of_additiveThree (topG12AdditiveThreeComparison_of_comparison h)
    hrec hstep hα hC

/-- **Merging the three depth constants into `Ctop`.**  Once each constant is
eventually dominated by `Ctop` and the elliptic fraction is nonnegative, the
three-constant depth form is the common-constant `TopG12AdditiveDepthComparison`
of the parent file.  This is the exact shape consumed by
`topG12LinearComparison_of_additiveDepth`. -/
theorem additiveDepth_of_g54g55Depth
    {top Ctop Cint Cin Cell : ℕ → ℝ} {interior : ℕ → ℕ → ℝ}
    {step eta epsRat epsIn : ℕ → ℝ} {L : ℕ}
    (h : G54G55ThreeTermDepthComparison top Cint Cin Cell interior step eta epsRat epsIn L)
    (hInt : ∀ᶠ n : ℕ in atTop, Cint n ≤ Ctop n)
    (hIn : ∀ᶠ n : ℕ in atTop, Cin n ≤ Ctop n)
    (hEll : ∀ᶠ n : ℕ in atTop, Cell n ≤ Ctop n)
    (hη : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n) :
    TopG12AdditiveDepthComparison top Ctop interior step eta epsRat epsIn L := by
  filter_upwards [h, hInt, hIn, hEll, hη] with n hn hInt' hIn' hEll' hη'
  have h1 : Cint n *
        Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) ≤
      Ctop n *
        Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) :=
    mul_le_mul_of_nonneg_right hInt' (Real.sqrt_nonneg _)
  have h2 : Cin n * Real.sqrt (epsIn n) ≤ Ctop n * Real.sqrt (epsIn n) :=
    mul_le_mul_of_nonneg_right hIn' (Real.sqrt_nonneg _)
  have h3 : Cell n * eta n ≤ Ctop n * eta n :=
    mul_le_mul_of_nonneg_right hEll' hη'
  exact hn.trans (add_le_add (add_le_add h1 h2) h3)

/-- **The G.12 linear-majorant form from the three-constant depth comparison.**
This is the parent file's `topG12LinearComparison_of_additiveDepth` applied
after merging the three constants. -/
theorem topG12LinearComparison_of_g54g55Depth
    {top Ctop Cint Cin Cell : ℕ → ℝ} {interior : ℕ → ℕ → ℝ}
    {step eta epsRat epsIn : ℕ → ℝ} {L : ℕ}
    (h : G54G55ThreeTermDepthComparison top Cint Cin Cell interior step eta epsRat epsIn L)
    (hInt : ∀ᶠ n : ℕ in atTop, Cint n ≤ Ctop n)
    (hIn : ∀ᶠ n : ℕ in atTop, Cin n ≤ Ctop n)
    (hEll : ∀ᶠ n : ℕ in atTop, Cell n ≤ Ctop n)
    (hη : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n) :
    TopG12LinearComparison top Ctop interior step eta epsRat epsIn L :=
  topG12LinearComparison_of_additiveDepth
    (additiveDepth_of_g54g55Depth h hInt hIn hEll hη)

/-! ## 3. The `δ₀` bundle realizing `TopG12ThreeData` -/

/-- The top data with the aggregate additive comparison replaced by the
componentwise G.54--G.55 estimate.  The three constants are kept separate and
are only merged into `Ctop` when `TopG12ThreeData` is constructed. -/
structure G54G55ThreeTermComparisonData where
  /-- Depth of the internal G.11 recurrence. -/
  L : ℕ
  /-- Internal normalized bad-child masses `δ_i`. -/
  interior : ℕ → ℕ → ℝ
  /-- G.11 step multiplier. -/
  step : ℕ → ℝ
  /-- Elliptic deletion fraction `η`. -/
  eta : ℕ → ℝ
  /-- G.11 rational error `ε_rat`. -/
  epsRat : ℕ → ℝ
  /-- Incoming exceptional mass. -/
  epsIn : ℕ → ℝ
  /-- Resulting top bad-child mass `δ_top`. -/
  top : ℕ → ℝ
  /-- Internal G.54--G.55 constant. -/
  Cint : ℕ → ℝ
  /-- Incoming G.54--G.55 constant. -/
  Cin : ℕ → ℝ
  /-- Elliptic G.54--G.55 constant. -/
  Cell : ℕ → ℝ
  /-- The common G.12 top constant used by the consumer. -/
  Ctop : ℕ → ℝ
  /-- Exponent of the top constant. -/
  cTop : ℝ
  /-- Exponent of the depth factor. -/
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  epsRat_nonneg : ∀ n, 0 ≤ epsRat n
  epsIn_nonneg : ∀ n, 0 ≤ epsIn n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  /-- The three G.54--G.55 constants are nonnegative. -/
  Cint_nonneg : ∀ n, 0 ≤ Cint n
  Cin_nonneg : ∀ n, 0 ≤ Cin n
  Cell_nonneg : ∀ n, 0 ≤ Cell n
  recurrence : G11InteriorRecurrence interior L step eta epsRat
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  /-- The componentwise G.54--G.55 comparison at `δ₀`. -/
  component_comparison : G54G55ThreeTermComparison top Cint Cin Cell interior epsIn eta
  Cint_le_Ctop : ∀ᶠ n : ℕ in atTop, Cint n ≤ Ctop n
  Cin_le_Ctop : ∀ᶠ n : ℕ in atTop, Cin n ≤ Ctop n
  Cell_le_Ctop : ∀ᶠ n : ℕ in atTop, Cell n ≤ Ctop n
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)
  base_subexp : SubexpLoss fun n => interior n L
  eta_subexp : SubexpLoss eta
  epsRat_subexp : SubexpLoss epsRat
  epsIn_subexp : SubexpLoss epsIn

namespace G54G55ThreeTermComparisonData

/-- The aggregate three-constant comparison at `δ₀`, proved from the
componentwise estimates. -/
theorem additiveThree (S : G54G55ThreeTermComparisonData) :
    TopG12AdditiveThreeComparison S.top S.Cint S.Cin S.Cell S.interior S.epsIn S.eta :=
  topG12AdditiveThreeComparison_of_g54g55 S.component_comparison

/-- The aggregate comparison at the common constant `Ctop`, obtained by merging
the three constants.  This is the `additive_comparison` field of
`TopG12ThreeData`. -/
theorem additiveThreeCommon (S : G54G55ThreeTermComparisonData) :
    TopG12AdditiveThreeComparison S.top S.Ctop S.Ctop S.Ctop S.interior S.epsIn S.eta := by
  filter_upwards [S.additiveThree, S.Cint_le_Ctop, S.Cin_le_Ctop, S.Cell_le_Ctop,
    Eventually.of_forall S.eta_nonneg] with n hn hInt hIn hEll hη
  have h1 : S.Cint n * Real.sqrt (S.interior n 0) ≤
      S.Ctop n * Real.sqrt (S.interior n 0) :=
    mul_le_mul_of_nonneg_right hInt (Real.sqrt_nonneg _)
  have h2 : S.Cin n * Real.sqrt (S.epsIn n) ≤
      S.Ctop n * Real.sqrt (S.epsIn n) :=
    mul_le_mul_of_nonneg_right hIn (Real.sqrt_nonneg _)
  have h3 : S.Cell n * S.eta n ≤ S.Ctop n * S.eta n :=
    mul_le_mul_of_nonneg_right hEll hη
  exact hn.trans (add_le_add (add_le_add h1 h2) h3)

/-- The derived `TopG12Comparison` at the common constant. -/
theorem comparison (S : G54G55ThreeTermComparisonData) :
    TopG12Comparison S.top S.Ctop S.interior S.epsIn S.eta :=
  topG12Comparison_of_additiveThree S.additiveThreeCommon
    (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall S.eta_nonneg)

/-- The bundle realizes `TopG12ThreeData` with the derived common-constant
comparison.  Its `G12TopInputs` realization is therefore available. -/
noncomputable def toTopG12ThreeData (S : G54G55ThreeTermComparisonData) :
    TopG12ThreeData where
  L := S.L
  interior := S.interior
  step := S.step
  eta := S.eta
  epsRat := S.epsRat
  epsIn := S.epsIn
  top := S.top
  Ctop := S.Ctop
  cTop := S.cTop
  cInt := S.cInt
  interior_nonneg := S.interior_nonneg
  eta_nonneg := S.eta_nonneg
  epsRat_nonneg := S.epsRat_nonneg
  epsIn_nonneg := S.epsIn_nonneg
  top_nonneg := S.top_nonneg
  Ctop_nonneg := S.Ctop_nonneg
  cTop_nonneg := S.cTop_nonneg
  recurrence := S.recurrence
  step_ge_one := S.step_ge_one
  alpha_nonneg := S.alpha_nonneg
  depth_bound := S.depth_bound
  additive_comparison := S.additiveThreeCommon
  Ctop_le := S.Ctop_le
  base_subexp := S.base_subexp
  eta_subexp := S.eta_subexp
  epsRat_subexp := S.epsRat_subexp
  epsIn_subexp := S.epsIn_subexp

/-- The bundle realizes `G12TopInputs` through `TopG12ThreeData`. -/
noncomputable def toG12TopInputs (S : G54G55ThreeTermComparisonData) :
    G12TopInputs :=
  S.toTopG12ThreeData.toG12TopInputs

/-- The G.12 top mass is subexponential. -/
theorem top_subexp (S : G54G55ThreeTermComparisonData) : SubexpLoss S.top :=
  S.toTopG12ThreeData.top_subexp

end G54G55ThreeTermComparisonData

/-! ## 4. The depth bundle realizing `TopG12AdditiveData` -/

/-- The depth form of the G.54--G.55 data.  It differs from
`G54G55ThreeTermComparisonData` only in carrying the explicit G.11 majorant
comparison instead of the `δ₀` comparison, so it feeds
`TopG12AdditiveData` directly. -/
structure G54G55ThreeTermDepthData where
  L : ℕ
  interior : ℕ → ℕ → ℝ
  step : ℕ → ℝ
  eta : ℕ → ℝ
  epsRat : ℕ → ℝ
  epsIn : ℕ → ℝ
  top : ℕ → ℝ
  Cint : ℕ → ℝ
  Cin : ℕ → ℝ
  Cell : ℕ → ℝ
  Ctop : ℕ → ℝ
  cTop : ℝ
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  epsRat_nonneg : ∀ n, 0 ≤ epsRat n
  epsIn_nonneg : ∀ n, 0 ≤ epsIn n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  Cint_nonneg : ∀ n, 0 ≤ Cint n
  Cin_nonneg : ∀ n, 0 ≤ Cin n
  Cell_nonneg : ∀ n, 0 ≤ Cell n
  recurrence : G11InteriorRecurrence interior L step eta epsRat
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  /-- The componentwise G.54--G.55 comparison at the G.11 majorant. -/
  depth_comparison : G54G55ThreeTermDepthComparison top Cint Cin Cell interior step eta epsRat epsIn L
  Cint_le_Ctop : ∀ᶠ n : ℕ in atTop, Cint n ≤ Ctop n
  Cin_le_Ctop : ∀ᶠ n : ℕ in atTop, Cin n ≤ Ctop n
  Cell_le_Ctop : ∀ᶠ n : ℕ in atTop, Cell n ≤ Ctop n
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)
  base_subexp : SubexpLoss fun n => interior n L
  eta_subexp : SubexpLoss eta
  epsRat_subexp : SubexpLoss epsRat
  epsIn_subexp : SubexpLoss epsIn

namespace G54G55ThreeTermDepthData

/-- The common-constant additive depth comparison of the parent file. -/
theorem additiveDepth (S : G54G55ThreeTermDepthData) :
    TopG12AdditiveDepthComparison S.top S.Ctop S.interior S.step S.eta S.epsRat S.epsIn S.L :=
  additiveDepth_of_g54g55Depth S.depth_comparison S.Cint_le_Ctop S.Cin_le_Ctop
    S.Cell_le_Ctop (Eventually.of_forall S.eta_nonneg)

/-- The G.12 linear-majorant form consumed by `G12TopInputs`. -/
theorem linearComparison (S : G54G55ThreeTermDepthData) :
    TopG12LinearComparison S.top S.Ctop S.interior S.step S.eta S.epsRat S.epsIn S.L :=
  topG12LinearComparison_of_additiveDepth S.additiveDepth

/-- The four explicit interior fields assemble `InteriorSubProps`. -/
theorem interiorConcentration (S : G54G55ThreeTermDepthData) :
    InteriorSubProps S.interior S.L S.eta S.epsRat S.epsIn where
  base_subexp := S.base_subexp
  eta_subexp := S.eta_subexp
  epsRat_subexp := S.epsRat_subexp
  epsIn_subexp := S.epsIn_subexp

/-- The depth bundle realizes the existing `TopG12AdditiveData`. -/
noncomputable def toTopG12AdditiveData (S : G54G55ThreeTermDepthData) :
    TopG12AdditiveData where
  L := S.L
  interior := S.interior
  step := S.step
  eta := S.eta
  epsRat := S.epsRat
  epsIn := S.epsIn
  top := S.top
  Ctop := S.Ctop
  cTop := S.cTop
  cInt := S.cInt
  interior_nonneg := S.interior_nonneg
  eta_nonneg := S.eta_nonneg
  epsRat_nonneg := S.epsRat_nonneg
  epsIn_nonneg := S.epsIn_nonneg
  top_nonneg := S.top_nonneg
  Ctop_nonneg := S.Ctop_nonneg
  cTop_nonneg := S.cTop_nonneg
  recurrence := S.recurrence
  step_ge_one := S.step_ge_one
  alpha_nonneg := S.alpha_nonneg
  depth_bound := S.depth_bound
  additive_comparison := S.additiveDepth
  Ctop_le := S.Ctop_le
  base_subexp := S.base_subexp
  eta_subexp := S.eta_subexp
  epsRat_subexp := S.epsRat_subexp
  epsIn_subexp := S.epsIn_subexp

/-- The G.12 top mass is subexponential. -/
theorem top_subexp (S : G54G55ThreeTermDepthData) : SubexpLoss S.top :=
  S.toTopG12AdditiveData.top_subexp

end G54G55ThreeTermDepthData

/-! ## Axiom audit -/

#print axioms topG12AdditiveThreeComparison_of_g54g55
#print axioms g54g55_of_comparison
#print axioms topG12AdditiveThreeComparison_of_comparison
#print axioms topG12Comparison_of_g54g55
#print axioms additiveThree_iff_comparison
#print axioms g54g55Depth_of_additiveThree
#print axioms g54g55Depth_of_comparison
#print axioms additiveDepth_of_g54g55Depth
#print axioms topG12LinearComparison_of_g54g55Depth
#print axioms G54G55ThreeTermComparisonData.additiveThree
#print axioms G54G55ThreeTermComparisonData.additiveThreeCommon
#print axioms G54G55ThreeTermComparisonData.comparison
#print axioms G54G55ThreeTermComparisonData.toTopG12ThreeData
#print axioms G54G55ThreeTermComparisonData.toG12TopInputs
#print axioms G54G55ThreeTermComparisonData.top_subexp
#print axioms G54G55ThreeTermDepthData.additiveDepth
#print axioms G54G55ThreeTermDepthData.linearComparison
#print axioms G54G55ThreeTermDepthData.toTopG12AdditiveData
#print axioms G54G55ThreeTermDepthData.top_subexp

end Cogentic.RandomizedL20_4Additive
