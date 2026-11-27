import Cogentic.RandomizedL20_4InteriorBase
import Cogentic.RandomizedL20_2Sub
import Cogentic.RandomizedL20_2Saddle

set_option linter.style.haveILetI false

/-!
# L20.4 base source: the paper's G.11 base mass

`Cogentic.RandomizedL20_4InteriorBase.BaseConcentrationSource` isolates the
base field of the G.11 interior step as the eventual identification

`interior n L = I.loss n`.

This file makes the paper's G.11 base mass explicit and proves that source for
it.  The base mass is the normalized mean discrepancy of the L20.2 interior
cell, i.e. exactly the quantity `I.loss`:

```
paperG11BaseMass I n L
  = |mean (cell n).f - mean (cell n).proxy| / μ n
  = I.loss n .
```

The first equality is the definition; the second is the L20.2 definition of
`loss`.  Thus `BaseConcentrationSource` is not an extra analytic estimate: it is
the identification of the paper's base mass with the existing L20.2
concentration discrepancy.  The same identification is recorded for the reduced
bundles `L20_2SubInputs` and `L20_2SaddleInputs`, whose `toInputs_loss_eq`
theorems expose the cell-level discrepancy directly.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss.
-/

namespace Cogentic.RandomizedL20_4BaseSource

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Saddle
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4Interior
open Cogentic.RandomizedL20_4InteriorBase

noncomputable section

/-! ## 1. The explicit G.11 base mass -/

/-- The paper's G.11 base mass on the L20.2 interior cell: the absolute
normalized discrepancy between the actual mean and the proxy mean.  The extra
depth argument is the internal G.11 level; the concentration estimate is
uniform in it, so the mass itself does not depend on it. -/
def paperG11BaseMass (I : L20_2Inputs) : ℕ → ℕ → ℝ :=
  fun n _ =>
    |(I.cell n).mean (I.cell n).f - (I.cell n).mean (I.cell n).proxy| / I.μ n

/-- The base mass is definitionally the normalized cell discrepancy. -/
theorem paperG11BaseMass_apply (I : L20_2Inputs) (n L : ℕ) :
    paperG11BaseMass I n L =
      |(I.cell n).mean (I.cell n).f - (I.cell n).mean (I.cell n).proxy| / I.μ n :=
  rfl

/-- **The paper's G.11 base mass is the L20.2 concentration loss.** -/
theorem paperG11BaseMass_eq_loss (I : L20_2Inputs) (n L : ℕ) :
    paperG11BaseMass I n L = I.loss n :=
  rfl

/-- The base mass is nonnegative: it is an absolute value divided by the
positive ideal mean.  The loss is never replaced by zero. -/
theorem paperG11BaseMass_nonneg (I : L20_2Inputs) (n L : ℕ) :
    0 ≤ paperG11BaseMass I n L :=
  div_nonneg (abs_nonneg _) (I.μ_pos n).le

/-- The base mass vanishes exactly when the actual and proxy means agree.  This
records that the mass is the genuine cell discrepancy, not a zero placeholder. -/
theorem paperG11BaseMass_eq_zero_iff (I : L20_2Inputs) (n L : ℕ) :
    paperG11BaseMass I n L = 0 ↔
      (I.cell n).mean (I.cell n).f = (I.cell n).mean (I.cell n).proxy := by
  rw [paperG11BaseMass_apply, div_eq_zero_iff, abs_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (I.μ_pos n).ne'
  · exact Or.inl

/-- **`BaseConcentrationSource` for the paper's G.11 base mass.**  This is the
smallest explicit source: the base mass *is* the L20.2 normalized interior
discrepancy, so the source holds by reflexivity. -/
theorem baseConcentrationSource_paperG11BaseMass (I : L20_2Inputs) (L : ℕ) :
    BaseConcentrationSource (paperG11BaseMass I) L I :=
  Eventually.of_forall fun n => paperG11BaseMass_eq_loss I n L

/-- The explicit base mass is the existing canonical sequence
`concentrationBase` of `RandomizedL20_4InteriorBase`. -/
theorem paperG11BaseMass_eq_concentrationBase (I : L20_2Inputs) :
    paperG11BaseMass I = concentrationBase I := by
  funext n L
  exact paperG11BaseMass_eq_loss I n L

/-! ## 2. The smallest explicit equality -/

/-- The source form with `I.loss` unfolded into the actual cell means and the
ideal mean.  This is the smallest explicit equality: it mentions no derived
abbreviation. -/
def BaseDiscrepancySource (interior : ℕ → ℕ → ℝ) (L : ℕ) (I : L20_2Inputs) :
    Prop :=
  ∀ᶠ n : ℕ in atTop,
    interior n L =
      |(I.cell n).mean (I.cell n).f - (I.cell n).mean (I.cell n).proxy| / I.μ n

/-- The explicit discrepancy source is exactly `BaseConcentrationSource`; the
only difference is that `I.loss` has been unfolded. -/
theorem baseDiscrepancySource_iff_baseConcentrationSource
    {interior : ℕ → ℕ → ℝ} {L : ℕ} {I : L20_2Inputs} :
    BaseDiscrepancySource interior L I ↔ BaseConcentrationSource interior L I := by
  constructor
  · intro h
    filter_upwards [h] with n hn
    rw [hn]
    rfl
  · intro h
    filter_upwards [h] with n hn
    rw [hn]
    rfl

/-- The smallest explicit equality directly implies the parent inequality
`BaseFromConcentration`. -/
theorem baseFromConcentration_of_discrepancySource
    {interior : ℕ → ℕ → ℝ} {L : ℕ} {I : L20_2Inputs}
    (h : BaseDiscrepancySource interior L I) :
    BaseFromConcentration interior L I :=
  baseFromConcentration_of_source
    ((baseDiscrepancySource_iff_baseConcentrationSource).mp h)

/-- The paper's G.11 base mass satisfies the smallest explicit equality. -/
theorem baseDiscrepancySource_paperG11BaseMass (I : L20_2Inputs) (L : ℕ) :
    BaseDiscrepancySource (paperG11BaseMass I) L I :=
  (baseDiscrepancySource_iff_baseConcentrationSource).mpr
    (baseConcentrationSource_paperG11BaseMass I L)

/-! ## 3. The inherited L20.2 estimates -/

/-- The base mass inherits the L20.2 `D^{-2A}` concentration budget. -/
theorem paperG11BaseMass_le_paper (I : L20_2Inputs) (L : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      paperG11BaseMass I n L ≤ exp (-2 * I.A n * scale n) :=
  baseSource_le_paper (baseConcentrationSource_paperG11BaseMass I L)

/-- The base mass is a `SubexpLoss`, inherited from the L20.2 concentration
estimate. -/
theorem paperG11BaseMass_subexp (I : L20_2Inputs) (L : ℕ) :
    SubexpLoss fun n => paperG11BaseMass I n L :=
  baseSource_subexp (baseConcentrationSource_paperG11BaseMass I L)

/-- `BaseFromConcentration` for the paper's G.11 base mass. -/
theorem baseFromConcentration_paperG11BaseMass (I : L20_2Inputs) (L : ℕ) :
    BaseFromConcentration (paperG11BaseMass I) L I :=
  baseFromConcentration_of_source (baseConcentrationSource_paperG11BaseMass I L)

/-- The base mass occupies the `B = 2` ledger slot: it is at most
`exp (-2 log D)`.  This is the L20.2 `slot_le` under the identification, so the
mass is a genuine `D^{-B}` quantity rather than zero by fiat. -/
theorem paperG11BaseMass_slot_le (I : L20_2Inputs) (L : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      paperG11BaseMass I n L ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [I.slot_le] with n hn
  rwa [paperG11BaseMass_eq_loss]

/-! ## 4. The reduced L20.2 bundles -/

/-- The paper's G.11 base mass attached to the reduced `L20_2SubInputs` bundle.
It is written on the actual cell and mass carried by the bundle. -/
def paperG11BaseMassOfSub (S : L20_2SubInputs) : ℕ → ℕ → ℝ :=
  fun n _ =>
    |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| / S.μ n

/-- The reduced-bundle base mass is the normalized cell discrepancy. -/
theorem paperG11BaseMassOfSub_apply (S : L20_2SubInputs) (n L : ℕ) :
    paperG11BaseMassOfSub S n L =
      |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| / S.μ n :=
  rfl

/-- The reduced-bundle base mass is the reduced bundle's L20.2 loss. -/
theorem paperG11BaseMassOfSub_eq_loss (S : L20_2SubInputs) (n L : ℕ) :
    paperG11BaseMassOfSub S n L = S.toInputs.loss n :=
  (S.toInputs_loss_eq n).symm

/-- **`BaseConcentrationSource` for the reduced L20.2 bundle.** -/
theorem baseConcentrationSource_paperG11BaseMassOfSub
    (S : L20_2SubInputs) (L : ℕ) :
    BaseConcentrationSource (paperG11BaseMassOfSub S) L S.toInputs :=
  Eventually.of_forall fun n => paperG11BaseMassOfSub_eq_loss S n L

/-- The reduced-bundle base mass satisfies the smallest explicit equality. -/
theorem baseDiscrepancySource_paperG11BaseMassOfSub
    (S : L20_2SubInputs) (L : ℕ) :
    BaseDiscrepancySource (paperG11BaseMassOfSub S) L S.toInputs :=
  (baseDiscrepancySource_iff_baseConcentrationSource).mpr
    (baseConcentrationSource_paperG11BaseMassOfSub S L)

/-- The reduced-bundle base mass is a `SubexpLoss`. -/
theorem paperG11BaseMassOfSub_subexp (S : L20_2SubInputs) (L : ℕ) :
    SubexpLoss fun n => paperG11BaseMassOfSub S n L :=
  baseSource_subexp (baseConcentrationSource_paperG11BaseMassOfSub S L)

/-- The reduced-bundle base mass is in the `B = 2` ledger slot. -/
theorem paperG11BaseMassOfSub_slot_le (S : L20_2SubInputs) (L : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      paperG11BaseMassOfSub S n L ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [S.slot_le] with n hn
  rwa [paperG11BaseMassOfSub_eq_loss]

/-- The paper's G.11 base mass attached to the fully reduced saddle bundle. -/
def paperG11BaseMassOfSaddle (S : L20_2SaddleInputs) : ℕ → ℕ → ℝ :=
  fun n _ =>
    |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| / S.μ n

/-- The saddle-bundle base mass is the normalized cell discrepancy. -/
theorem paperG11BaseMassOfSaddle_apply (S : L20_2SaddleInputs) (n L : ℕ) :
    paperG11BaseMassOfSaddle S n L =
      |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| / S.μ n :=
  rfl

/-- The saddle-bundle base mass is the saddle bundle's L20.2 loss. -/
theorem paperG11BaseMassOfSaddle_eq_loss (S : L20_2SaddleInputs) (n L : ℕ) :
    paperG11BaseMassOfSaddle S n L = S.toInputs.loss n :=
  (S.toInputs_loss_eq n).symm

/-- **`BaseConcentrationSource` for the fully reduced saddle bundle.** -/
theorem baseConcentrationSource_paperG11BaseMassOfSaddle
    (S : L20_2SaddleInputs) (L : ℕ) :
    BaseConcentrationSource (paperG11BaseMassOfSaddle S) L S.toInputs :=
  Eventually.of_forall fun n => paperG11BaseMassOfSaddle_eq_loss S n L

/-- The saddle-bundle base mass satisfies the smallest explicit equality. -/
theorem baseDiscrepancySource_paperG11BaseMassOfSaddle
    (S : L20_2SaddleInputs) (L : ℕ) :
    BaseDiscrepancySource (paperG11BaseMassOfSaddle S) L S.toInputs :=
  (baseDiscrepancySource_iff_baseConcentrationSource).mpr
    (baseConcentrationSource_paperG11BaseMassOfSaddle S L)

/-- The saddle-bundle base mass is a `SubexpLoss`. -/
theorem paperG11BaseMassOfSaddle_subexp (S : L20_2SaddleInputs) (L : ℕ) :
    SubexpLoss fun n => paperG11BaseMassOfSaddle S n L :=
  baseSource_subexp (baseConcentrationSource_paperG11BaseMassOfSaddle S L)

/-- The saddle-bundle base mass is in the `B = 2` ledger slot. -/
theorem paperG11BaseMassOfSaddle_slot_le (S : L20_2SaddleInputs) (L : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      paperG11BaseMassOfSaddle S n L ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [S.slot_le] with n hn
  rwa [paperG11BaseMassOfSaddle_eq_loss]

/-! ## 5. The base-source bundle -/

/-- A base source for the G.11 interior step: an L20.2 input together with the
identification of the paper's base mass with its normalized discrepancy.  This
is the base-field part of `InteriorBaseSources`, with the identification kept as
an explicit equality rather than hidden in a `≤`. -/
structure G11BaseSource (interior : ℕ → ℕ → ℝ) (L : ℕ) where
  /-- The L20.2 concentration input. -/
  base : L20_2Inputs
  /-- The G.11 base mass is the L20.2 normalized discrepancy. -/
  source : BaseConcentrationSource interior L base

namespace G11BaseSource

variable {interior : ℕ → ℕ → ℝ} {L : ℕ}

/-- The parent base inequality. -/
theorem baseFrom (S : G11BaseSource interior L) :
    BaseFromConcentration interior L S.base :=
  baseFromConcentration_of_source S.source

/-- The base mass is a `SubexpLoss`. -/
theorem base_subexp (S : G11BaseSource interior L) :
    SubexpLoss fun n => interior n L :=
  baseSource_subexp S.source

/-- The base mass inherits the L20.2 paper budget. -/
theorem le_paper (S : G11BaseSource interior L) :
    ∀ᶠ n : ℕ in atTop,
      interior n L ≤ exp (-2 * S.base.A n * scale n) :=
  baseSource_le_paper S.source

end G11BaseSource

/-- The canonical base source of the paper: the base mass is the L20.2
normalized discrepancy of `I`. -/
def paperG11BaseSource (I : L20_2Inputs) (L : ℕ) :
    G11BaseSource (paperG11BaseMass I) L where
  base := I
  source := baseConcentrationSource_paperG11BaseMass I L

/-- The reduced-bundle base source. -/
def paperG11BaseSourceOfSub (S : L20_2SubInputs) (L : ℕ) :
    G11BaseSource (paperG11BaseMassOfSub S) L where
  base := S.toInputs
  source := baseConcentrationSource_paperG11BaseMassOfSub S L

/-- The saddle-bundle base source. -/
def paperG11BaseSourceOfSaddle (S : L20_2SaddleInputs) (L : ℕ) :
    G11BaseSource (paperG11BaseMassOfSaddle S) L where
  base := S.toInputs
  source := baseConcentrationSource_paperG11BaseMassOfSaddle S L

/-! ## 6. Feeding `InteriorSourceData` -/

/-- **The G.11 interior data with the base field sourced concretely.**  The base
mass is the paper's normalized L20.2 discrepancy; the other three fields are the
rational source, the L21.2 elliptic source and an explicit incoming
`SubexpLoss`.  This is `interiorSourceData_of_sources` specialized to the
paper's base mass. -/
noncomputable def interiorSourceData_of_base_source {L : ℕ} {eta epsRat epsIn : ℕ → ℝ}
    (I : L20_2Inputs)
    (rational : L20_2Inputs) (hrat : RationalExceptionSource epsRat rational)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs)
    (hell : EllipticFromL21_2 eta elliptic)
    (hin : SubexpLoss epsIn) :
    InteriorSourceData (paperG11BaseMass I) L eta epsRat epsIn :=
  interiorSourceData_of_sources I (baseConcentrationSource_paperG11BaseMass I L)
    rational hrat elliptic hell hin

/-- The sourced interior data realize the four interior `SubexpLoss` fields. -/
theorem interiorSubProps_of_base_source {L : ℕ} {eta epsRat epsIn : ℕ → ℝ}
    (I : L20_2Inputs)
    (rational : L20_2Inputs) (hrat : RationalExceptionSource epsRat rational)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs)
    (hell : EllipticFromL21_2 eta elliptic)
    (hin : SubexpLoss epsIn) :
    InteriorSubProps (paperG11BaseMass I) L eta epsRat epsIn :=
  (interiorSourceData_of_base_source I rational hrat elliptic hell hin).subProps

/-- The same reduction with the base field supplied by a reduced
`L20_2SaddleInputs` bundle. -/
noncomputable def interiorSourceData_of_saddle_base {L : ℕ} {eta epsRat epsIn : ℕ → ℝ}
    (S : L20_2SaddleInputs)
    (rational : L20_2Inputs) (hrat : RationalExceptionSource epsRat rational)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs)
    (hell : EllipticFromL21_2 eta elliptic)
    (hin : SubexpLoss epsIn) :
    InteriorSourceData (paperG11BaseMassOfSaddle S) L eta epsRat epsIn :=
  interiorSourceData_of_sources S.toInputs
    (baseConcentrationSource_paperG11BaseMassOfSaddle S L)
    rational hrat elliptic hell hin

/-- The saddle-based base source realizes the four interior `SubexpLoss` fields. -/
theorem interiorSubProps_of_saddle_base {L : ℕ} {eta epsRat epsIn : ℕ → ℝ}
    (S : L20_2SaddleInputs)
    (rational : L20_2Inputs) (hrat : RationalExceptionSource epsRat rational)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs)
    (hell : EllipticFromL21_2 eta elliptic)
    (hin : SubexpLoss epsIn) :
    InteriorSubProps (paperG11BaseMassOfSaddle S) L eta epsRat epsIn :=
  (interiorSourceData_of_saddle_base S rational hrat elliptic hell hin).subProps

/-! ## Axiom audit -/

#print axioms paperG11BaseMass_apply
#print axioms paperG11BaseMass_eq_loss
#print axioms paperG11BaseMass_nonneg
#print axioms paperG11BaseMass_eq_zero_iff
#print axioms baseConcentrationSource_paperG11BaseMass
#print axioms paperG11BaseMass_eq_concentrationBase
#print axioms baseDiscrepancySource_iff_baseConcentrationSource
#print axioms baseFromConcentration_of_discrepancySource
#print axioms baseDiscrepancySource_paperG11BaseMass
#print axioms paperG11BaseMass_le_paper
#print axioms paperG11BaseMass_subexp
#print axioms baseFromConcentration_paperG11BaseMass
#print axioms paperG11BaseMass_slot_le
#print axioms paperG11BaseMassOfSub_apply
#print axioms paperG11BaseMassOfSub_eq_loss
#print axioms baseConcentrationSource_paperG11BaseMassOfSub
#print axioms baseDiscrepancySource_paperG11BaseMassOfSub
#print axioms paperG11BaseMassOfSub_subexp
#print axioms paperG11BaseMassOfSub_slot_le
#print axioms paperG11BaseMassOfSaddle_apply
#print axioms paperG11BaseMassOfSaddle_eq_loss
#print axioms baseConcentrationSource_paperG11BaseMassOfSaddle
#print axioms baseDiscrepancySource_paperG11BaseMassOfSaddle
#print axioms paperG11BaseMassOfSaddle_subexp
#print axioms paperG11BaseMassOfSaddle_slot_le
#print axioms G11BaseSource.baseFrom
#print axioms G11BaseSource.base_subexp
#print axioms G11BaseSource.le_paper
#print axioms paperG11BaseSource
#print axioms paperG11BaseSourceOfSub
#print axioms paperG11BaseSourceOfSaddle
#print axioms interiorSourceData_of_base_source
#print axioms interiorSubProps_of_base_source
#print axioms interiorSourceData_of_saddle_base
#print axioms interiorSubProps_of_saddle_base

end

end Cogentic.RandomizedL20_4BaseSource
