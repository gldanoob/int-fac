import Cogentic.RandomizedL20_4Interior
import Cogentic.RandomizedL20_2Sub
import Cogentic.RandomizedL20_2Saddle

set_option linter.style.haveILetI false

/-!
# L20.4 interior: explicit sources for the base and rational fields

`Cogentic.RandomizedL20_4Interior` isolates three source inequalities for the
interior step:

* `BaseFromConcentration interior L I` : `interior n L ≤ I.loss n`;
* `RationalFromExceptions epsRat I` : `epsRat n ≤ I.ρ n`;
* `IncomingFromExceptions epsIn I` : `epsIn n ≤ I.ρ n`
  (with the elliptic field already discharged from L21.2).

The first two are stated against the L20.2 normalized concentration discrepancy
`I.loss` and the L20.2 CRT plus smooth-character budget
`I.ρ = I.crtError + I.charError`.  They cannot be derived from the L20.2
*paper bounds* alone for an arbitrary sequence: `I.loss` and `I.ρ` have only
upper bounds (`loss_le_paper`, `eventually_rho_le`), and an arbitrary
`interior`/`epsRat` has no relation to them.  For example `interior = 1` is
compatible with every L20.2 budget but not with `interior n L ≤ I.loss n`.

The correct smallest explicit sources are therefore *identifications* of the
G.11/G.12 objects with the existing L20.2 objects, not new estimates:

* `BaseConcentrationSource interior L I` : `interior n L = I.loss n`;
* `RationalExceptionSource epsRat I` : `epsRat n = I.ρ n`;
* `IncomingExceptionSource epsIn I` : `epsIn n = I.ρ n`.

Each is the exact statement that the G.11 base mass, the G.11 rational error and
the G.12 incoming exception are the L20.2 concentration and character quantities.
They imply the parent inequalities by `le_of_eq`, and they inherit the L20.2
`D^{-B}` bounds through the already-proved estimates
`loss_subexp_of_L20_2` and `rho_subexp_of_L20_2`.  No inequality is weakened to
equality of estimates and no loss is set to zero: the identified sequences are
the actual normalized discrepancies.

The file also records the canonical concrete instance: choosing
`interior n L = I.loss n` and `epsRat = I.ρ` makes both source `Prop`s
definitional, so an `InteriorSourceData` is obtained from three L20.2 inputs
(base, rational and incoming) plus one L21.2 input, with no extra analytic
hypothesis.  This is the reduction to `InteriorSourceData`, hence to
`InteriorSubProps` and the top-conditioned data of `RandomizedL20_4Interior`.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss.
-/

namespace Cogentic.RandomizedL20_4InteriorBase

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4Interior
open Cogentic.RandomizedL19SecondMoment

/-! ## 1. The explicit source `Prop`s -/

/-- The G.11 internal base mass is the L20.2 normalized interior concentration
discrepancy.  This is the smallest explicit source for the base field: it
identifies the object, and `BaseFromConcentration` follows by `le_of_eq`. -/
def BaseConcentrationSource (interior : ℕ → ℕ → ℝ) (L : ℕ)
    (I : L20_2Inputs) : Prop :=
  ∀ᶠ n : ℕ in atTop, interior n L = I.loss n

/-- The G.11 rational error is the L20.2 CRT plus smooth-character budget
`ρ = crtError + charError`.  This is the smallest explicit source for the
rational field. -/
def RationalExceptionSource (epsRat : ℕ → ℝ) (I : L20_2Inputs) : Prop :=
  ∀ᶠ n : ℕ in atTop, epsRat n = I.ρ n

/-- The G.12 incoming exceptional mass is the same L20.2 CRT plus
smooth-character budget.  This is the source form of `IncomingFromExceptions`. -/
def IncomingExceptionSource (epsIn : ℕ → ℝ) (I : L20_2Inputs) : Prop :=
  ∀ᶠ n : ℕ in atTop, epsIn n = I.ρ n

/-! ## 2. The parent inequalities -/

/-- `BaseFromConcentration` from the explicit identification with `I.loss`. -/
theorem baseFromConcentration_of_source {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {I : L20_2Inputs} (h : BaseConcentrationSource interior L I) :
    BaseFromConcentration interior L I := by
  filter_upwards [h] with n hn
  exact le_of_eq hn

/-- `RationalFromExceptions` from the explicit identification with `I.ρ`. -/
theorem rationalFromExceptions_of_source {epsRat : ℕ → ℝ} {I : L20_2Inputs}
    (h : RationalExceptionSource epsRat I) :
    RationalFromExceptions epsRat I := by
  filter_upwards [h] with n hn
  exact le_of_eq hn

/-- `IncomingFromExceptions` from the explicit identification with `I.ρ`. -/
theorem incomingFromExceptions_of_source {epsIn : ℕ → ℝ} {I : L20_2Inputs}
    (h : IncomingExceptionSource epsIn I) :
    IncomingFromExceptions epsIn I := by
  filter_upwards [h] with n hn
  exact le_of_eq hn

/-! ## 3. The L20.2 budgets inherited by the sources -/

/-- The sourced base mass inherits the L20.2 `D^{-2A}` concentration budget
`exp (-2 * A * log D)`. -/
theorem baseSource_le_paper {interior : ℕ → ℕ → ℝ} {L : ℕ} {I : L20_2Inputs}
    (h : BaseConcentrationSource interior L I) :
    ∀ᶠ n : ℕ in atTop, interior n L ≤ exp (-2 * I.A n * scale n) := by
  filter_upwards [h, I.loss_le_paper] with n he hle
  rwa [he]

/-- The sourced rational error inherits the L20.2 CRT plus smooth-character
budget `ρ ≤ (1/2) exp (-4 * A * log D)`. -/
theorem rationalSource_le_paper {epsRat : ℕ → ℝ} {I : L20_2Inputs}
    (h : RationalExceptionSource epsRat I) :
    ∀ᶠ n : ℕ in atTop,
      epsRat n ≤ (1 / 2) * exp (-4 * I.A n * scale n) := by
  filter_upwards [h, I.eventually_rho_le] with n he hle
  rwa [he]

/-- The sourced incoming exception inherits the same CRT plus smooth-character
budget. -/
theorem incomingSource_le_paper {epsIn : ℕ → ℝ} {I : L20_2Inputs}
    (h : IncomingExceptionSource epsIn I) :
    ∀ᶠ n : ℕ in atTop,
      epsIn n ≤ (1 / 2) * exp (-4 * I.A n * scale n) := by
  filter_upwards [h, I.eventually_rho_le] with n he hle
  rwa [he]

/-- The sourced base mass is a `SubexpLoss`: the L20.2 normalized discrepancy is
subexponential (`loss_subexp_of_L20_2`), and the source identifies the base
with it. -/
theorem baseSource_subexp {interior : ℕ → ℕ → ℝ} {L : ℕ} {I : L20_2Inputs}
    (h : BaseConcentrationSource interior L I) :
    SubexpLoss fun n => interior n L := by
  refine subexpLoss_of_eventually_le ?_ (loss_subexp_of_L20_2 I)
  filter_upwards [h] with n he
  exact le_of_eq he

/-- The sourced rational error is a `SubexpLoss` (the L20.2 CRT plus
smooth-character budget is subexponential). -/
theorem rationalSource_subexp {epsRat : ℕ → ℝ} {I : L20_2Inputs}
    (h : RationalExceptionSource epsRat I) :
    SubexpLoss epsRat := by
  refine subexpLoss_of_eventually_le ?_ (rho_subexp_of_L20_2 I)
  filter_upwards [h] with n he
  exact le_of_eq he

/-- The sourced incoming exception is a `SubexpLoss`. -/
theorem incomingSource_subexp {epsIn : ℕ → ℝ} {I : L20_2Inputs}
    (h : IncomingExceptionSource epsIn I) :
    SubexpLoss epsIn := by
  refine subexpLoss_of_eventually_le ?_ (rho_subexp_of_L20_2 I)
  filter_upwards [h] with n he
  exact le_of_eq he

/-! ## 4. Reduction to `InteriorSourceData` -/

/-- The source data for all four interior fields: the G.11 base, the G.11
rational error, the L21.2 elliptic fraction and the G.12 incoming exception.
The base and rational fields are identified with the existing L20.2 objects; the
elliptic field with L21.2; the incoming exception with a second L20.2 budget. -/
structure InteriorBaseSources (interior : ℕ → ℕ → ℝ) (L : ℕ)
    (eta epsRat epsIn : ℕ → ℝ) where
  /-- The L20.2 input controlling the base mass. -/
  base : L20_2Inputs
  /-- The G.11 base mass is the L20.2 normalized discrepancy. -/
  base_source : BaseConcentrationSource interior L base
  /-- The L20.2 input controlling the rational and incoming errors. -/
  rational : L20_2Inputs
  /-- The G.11 rational error is the L20.2 CRT plus character budget. -/
  rational_source : RationalExceptionSource epsRat rational
  /-- The L21.2 elliptic input. -/
  elliptic : Cogentic.RandomizedL21_2.L21_2Inputs
  /-- The elliptic fraction is the L21.2 exceptional fraction. -/
  elliptic_source : EllipticFromL21_2 eta elliptic
  /-- The second L20.2 input controlling the incoming exception. -/
  incoming : L20_2Inputs
  /-- The G.12 incoming exception is the L20.2 CRT plus character budget. -/
  incoming_source : IncomingExceptionSource epsIn incoming

namespace InteriorBaseSources

variable {interior : ℕ → ℕ → ℝ} {L : ℕ} {eta epsRat epsIn : ℕ → ℝ}

/-- The base field of `InteriorSourceData`. -/
theorem baseFrom (S : InteriorBaseSources interior L eta epsRat epsIn) :
    BaseFromConcentration interior L S.base :=
  baseFromConcentration_of_source S.base_source

/-- The rational field of `InteriorSourceData`. -/
theorem rationalFrom (S : InteriorBaseSources interior L eta epsRat epsIn) :
    RationalFromExceptions epsRat S.rational :=
  rationalFromExceptions_of_source S.rational_source

/-- The incoming field, in the `IncomingFromExceptions` form. -/
theorem incomingFrom (S : InteriorBaseSources interior L eta epsRat epsIn) :
    IncomingFromExceptions epsIn S.incoming :=
  incomingFromExceptions_of_source S.incoming_source

/-- The base mass is a `SubexpLoss`. -/
theorem base_subexp (S : InteriorBaseSources interior L eta epsRat epsIn) :
    SubexpLoss fun n => interior n L :=
  baseSource_subexp S.base_source

/-- The rational error is a `SubexpLoss`. -/
theorem epsRat_subexp (S : InteriorBaseSources interior L eta epsRat epsIn) :
    SubexpLoss epsRat :=
  rationalSource_subexp S.rational_source

/-- The incoming exception is a `SubexpLoss`. -/
theorem epsIn_subexp (S : InteriorBaseSources interior L eta epsRat epsIn) :
    SubexpLoss epsIn :=
  incomingSource_subexp S.incoming_source

/-- **The reduction to `InteriorSourceData`.**  Each source identification fills
the corresponding field of `InteriorSourceData`; the L20.2 `SubexpLoss` fields
are then obtained from the existing concentration and character estimates, and
the elliptic field from L21.2. -/
def toInteriorSourceData (S : InteriorBaseSources interior L eta epsRat epsIn) :
    InteriorSourceData interior L eta epsRat epsIn where
  base := S.base
  base_from := S.baseFrom
  rational := S.rational
  rational_from := S.rationalFrom
  elliptic := S.elliptic
  elliptic_from := S.elliptic_source
  epsIn_subexp := S.epsIn_subexp

/-- The sourced data realize the four `InteriorSubProps` fields. -/
theorem subProps (S : InteriorBaseSources interior L eta epsRat epsIn) :
    InteriorSubProps interior L eta epsRat epsIn :=
  S.toInteriorSourceData.subProps

/-- The four interior fields with the incoming exception sourced from a possibly
different L20.2 CRT plus smooth-character budget.  This mirrors
`InteriorSourceData.subProps_of_incoming`: the base and rational fields are
unchanged, and only the incoming `SubexpLoss` is re-sourced. -/
theorem subProps_of_incoming
    (S : InteriorBaseSources interior L eta epsRat epsIn)
    (incoming : L20_2Inputs) (hin : IncomingFromExceptions epsIn incoming) :
    InteriorSubProps interior L eta epsRat epsIn where
  base_subexp := S.base_subexp
  eta_subexp := S.toInteriorSourceData.eta_subexp
  epsRat_subexp := S.epsRat_subexp
  epsIn_subexp := subexpLoss_of_eventually_le hin (rho_subexp_of_L20_2 incoming)

end InteriorBaseSources

/-- **Direct reduction from the explicit sources.**  Only the base and rational
fields need source `Prop`s; the elliptic field is the existing L21.2 input and
the incoming exception is any explicit `SubexpLoss`. -/
def interiorSourceData_of_sources {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {eta epsRat epsIn : ℕ → ℝ}
    (base : L20_2Inputs) (hbase : BaseConcentrationSource interior L base)
    (rational : L20_2Inputs) (hrat : RationalExceptionSource epsRat rational)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs)
    (hell : EllipticFromL21_2 eta elliptic)
    (hin : SubexpLoss epsIn) :
    InteriorSourceData interior L eta epsRat epsIn where
  base := base
  base_from := baseFromConcentration_of_source hbase
  rational := rational
  rational_from := rationalFromExceptions_of_source hrat
  elliptic := elliptic
  elliptic_from := hell
  epsIn_subexp := hin

/-- The direct reduction, with the incoming exception also sourced from an
L20.2 CRT plus smooth-character budget. -/
def interiorSourceData_of_sources_of_incoming {interior : ℕ → ℕ → ℝ}
    {L : ℕ} {eta epsRat epsIn : ℕ → ℝ}
    (base : L20_2Inputs) (hbase : BaseConcentrationSource interior L base)
    (rational : L20_2Inputs) (hrat : RationalExceptionSource epsRat rational)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs)
    (hell : EllipticFromL21_2 eta elliptic)
    (incoming : L20_2Inputs) (hin : IncomingExceptionSource epsIn incoming) :
    InteriorSourceData interior L eta epsRat epsIn :=
  interiorSourceData_of_sources base hbase rational hrat elliptic hell
    (incomingSource_subexp hin)

/-! ## 5. The canonical concrete instance -/

/-- The canonical base sequence: at depth `L` it is the L20.2 normalized
concentration discrepancy of `I`. -/
noncomputable def concentrationBase (I : L20_2Inputs) : ℕ → ℕ → ℝ :=
  fun n _ => I.loss n

/-- The canonical rational sequence: the L20.2 CRT plus smooth-character
budget of `I`. -/
noncomputable def rationalException (I : L20_2Inputs) : ℕ → ℝ :=
  fun n => I.ρ n

/-- The canonical base is a source by reflexivity. -/
theorem baseConcentrationSource_concrete (I : L20_2Inputs) (L : ℕ) :
    BaseConcentrationSource (concentrationBase I) L I :=
  Eventually.of_forall fun _ => rfl

/-- The canonical rational error is a source by reflexivity. -/
theorem rationalExceptionSource_concrete (I : L20_2Inputs) :
    RationalExceptionSource (rationalException I) I :=
  Eventually.of_forall fun _ => rfl

/-- `BaseFromConcentration` holds for the canonical L20.2 concentration
sequence. -/
theorem baseFromConcentration_concrete (I : L20_2Inputs) (L : ℕ) :
    BaseFromConcentration (concentrationBase I) L I :=
  baseFromConcentration_of_source (baseConcentrationSource_concrete I L)

/-- `RationalFromExceptions` holds for the canonical L20.2 CRT plus
smooth-character budget. -/
theorem rationalFromExceptions_concrete (I : L20_2Inputs) :
    RationalFromExceptions (rationalException I) I :=
  rationalFromExceptions_of_source (rationalExceptionSource_concrete I)

/-- **A concrete `InteriorSourceData`.**  The base and rational sequences are
the actual L20.2 loss and `ρ` sequences, the elliptic sequence is the actual
L21.2 loss, and the incoming exception is any explicit `SubexpLoss`.  Only the
three existing analytic inputs (two L20.2, one L21.2) and the incoming loss are
required. -/
def concreteInteriorSourceData (base rational : L20_2Inputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ)
    (epsIn : ℕ → ℝ) (hin : SubexpLoss epsIn) :
    InteriorSourceData (concentrationBase base) L
      (fun n => elliptic.loss n) (rationalException rational) epsIn where
  base := base
  base_from := baseFromConcentration_concrete base L
  rational := rational
  rational_from := rationalFromExceptions_concrete rational
  elliptic := elliptic
  elliptic_from := fun _ => rfl
  epsIn_subexp := hin

/-- The concrete source data realize the four interior `SubexpLoss` fields. -/
theorem concreteSubProps (base rational : L20_2Inputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ)
    (epsIn : ℕ → ℝ) (hin : SubexpLoss epsIn) :
    InteriorSubProps (concentrationBase base) L
      (fun n => elliptic.loss n) (rationalException rational) epsIn :=
  (concreteInteriorSourceData base rational elliptic L epsIn hin).subProps

/-- **The fully L20.2/L21.2-sourced `InteriorSourceData`.**  The incoming
exception is also the CRT plus smooth-character budget of an L20.2 input, so no
explicit `SubexpLoss` hypothesis remains. -/
noncomputable def concreteInteriorSourceDataOfIncoming
    (base rational incoming : L20_2Inputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ) :
    InteriorSourceData (concentrationBase base) L
      (fun n => elliptic.loss n) (rationalException rational)
      (rationalException incoming) :=
  concreteInteriorSourceData base rational elliptic L (rationalException incoming)
    (by
      show SubexpLoss (fun n => incoming.ρ n)
      exact rho_subexp_of_L20_2 incoming)

/-- The fully sourced data realize the four interior `SubexpLoss` fields. -/
theorem concreteSubPropsOfIncoming (base rational incoming : L20_2Inputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ) :
    InteriorSubProps (concentrationBase base) L
      (fun n => elliptic.loss n) (rationalException rational)
      (rationalException incoming) :=
  (concreteInteriorSourceDataOfIncoming base rational incoming elliptic L).subProps

/-! ## Axiom audit -/

#print axioms baseFromConcentration_of_source
#print axioms rationalFromExceptions_of_source
#print axioms incomingFromExceptions_of_source
#print axioms baseSource_le_paper
#print axioms rationalSource_le_paper
#print axioms incomingSource_le_paper
#print axioms baseSource_subexp
#print axioms rationalSource_subexp
#print axioms incomingSource_subexp
#print axioms InteriorBaseSources.baseFrom
#print axioms InteriorBaseSources.rationalFrom
#print axioms InteriorBaseSources.incomingFrom
#print axioms InteriorBaseSources.base_subexp
#print axioms InteriorBaseSources.epsRat_subexp
#print axioms InteriorBaseSources.epsIn_subexp
#print axioms InteriorBaseSources.toInteriorSourceData
#print axioms InteriorBaseSources.subProps
#print axioms InteriorBaseSources.subProps_of_incoming
#print axioms interiorSourceData_of_sources
#print axioms interiorSourceData_of_sources_of_incoming
#print axioms baseConcentrationSource_concrete
#print axioms rationalExceptionSource_concrete
#print axioms baseFromConcentration_concrete
#print axioms rationalFromExceptions_concrete
#print axioms concreteInteriorSourceData
#print axioms concreteSubProps
#print axioms concreteInteriorSourceDataOfIncoming
#print axioms concreteSubPropsOfIncoming

end Cogentic.RandomizedL20_4InteriorBase
