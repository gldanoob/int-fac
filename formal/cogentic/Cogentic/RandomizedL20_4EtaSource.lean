import Cogentic.RandomizedL20_4InteriorBase
import Cogentic.RandomizedL20_2Char

set_option linter.style.haveILetI false

/-!
# L20.4: the paper's rational and incoming exception sources

`Cogentic.RandomizedL20_4InteriorBase` isolates the two exception source
`Prop`s of the G.11/G.12 interior step:

* `RationalExceptionSource epsRat I : ∀ᶠ n, epsRat n = I.ρ n`;
* `IncomingExceptionSource epsIn I : ∀ᶠ n, epsIn n = I.ρ n`.

The paper does not treat `ε_rat` and `ε_in` as new analytic objects: both are
the *same* exception budget produced by the truncated geometric CRT step and
the GRH smooth-character step of L20.2.  In the formal development that budget
is

`I.ρ n = I.crtError n + I.charError n`.

This file makes the paper's choices explicit:

* `paperEpsRat I` and `paperEpsIn I` are both `fun n => I.crtError n + I.charError n`;
* `paperEpsRat_eq_rho` and `paperEpsIn_eq_rho` identify them definitionally
  with the L20.2 `ρ`;
* `rationalExceptionSource_paper` and `incomingExceptionSource_paper` prove the
  two source `Prop`s, so no extra analytic hypothesis is introduced.

The general `..._of_crt_add_char` lemmas record the smallest explicit equality
form: any sequence eventually equal to `I.crtError + I.charError` is a source.
The `L20_2CharInputs` specialization shows the budget in terms of the *actual*
concrete objects `geometricCRTError` and `smoothCharacterError`.

Finally `PaperExceptionSources` packages the three L20.2 inputs and the L21.2
input needed by the interior step.  Its `subProps` theorem produces
`InteriorSubProps` with the paper's `ε_rat` and `ε_in` already sourced, hence
the G.11/G.12 concentration fields without any new hypothesis.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss: the sequences are
the genuine CRT plus character budgets, not placeholders.
-/

namespace Cogentic.RandomizedL20_4EtaSource

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Char
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4Interior
open Cogentic.RandomizedL20_4InteriorBase

/-! ## 1. The paper's choices -/

/-- The paper's G.11 rational exception `ε_rat`: the L20.2 CRT plus
smooth-character budget.  This is written as the explicit sum so that the
identification with `ρ` is a definitional equality, not a new estimate. -/
noncomputable def paperEpsRat (I : L20_2Inputs) : ℕ → ℝ :=
  fun n => I.crtError n + I.charError n

/-- The paper's G.12 incoming exception `ε_in`: the same L20.2 CRT plus
smooth-character budget. -/
noncomputable def paperEpsIn (I : L20_2Inputs) : ℕ → ℝ :=
  fun n => I.crtError n + I.charError n

/-- The paper's rational exception is exactly the L20.2 `ρ`. -/
theorem paperEpsRat_eq_rho (I : L20_2Inputs) :
    paperEpsRat I = fun n => I.ρ n :=
  rfl

/-- The paper's incoming exception is exactly the L20.2 `ρ`. -/
theorem paperEpsIn_eq_rho (I : L20_2Inputs) :
    paperEpsIn I = fun n => I.ρ n :=
  rfl

/-- Pointwise identification with `ρ`. -/
theorem paperEpsRat_apply_eq_rho (I : L20_2Inputs) (n : ℕ) :
    paperEpsRat I n = I.ρ n :=
  rfl

/-- Pointwise identification with `ρ`. -/
theorem paperEpsIn_apply_eq_rho (I : L20_2Inputs) (n : ℕ) :
    paperEpsIn I n = I.ρ n :=
  rfl

/-! ## 2. The source `Prop`s for the paper's choices -/

/-- **The G.11 rational exception source.**  The paper's `ε_rat` is the L20.2
CRT plus smooth-character budget, so `RationalExceptionSource` holds with the
same `I`. -/
theorem rationalExceptionSource_paper (I : L20_2Inputs) :
    RationalExceptionSource (paperEpsRat I) I :=
  Eventually.of_forall fun n => paperEpsRat_apply_eq_rho I n

/-- **The G.12 incoming exception source.**  The paper's `ε_in` is the same
L20.2 CRT plus smooth-character budget. -/
theorem incomingExceptionSource_paper (I : L20_2Inputs) :
    IncomingExceptionSource (paperEpsIn I) I :=
  Eventually.of_forall fun n => paperEpsIn_apply_eq_rho I n

/-- Alias for the rational source with a descriptive name. -/
theorem paperRationalExceptionSource (I : L20_2Inputs) :
    RationalExceptionSource (paperEpsRat I) I :=
  rationalExceptionSource_paper I

/-- Alias for the incoming source with a descriptive name. -/
theorem paperIncomingExceptionSource (I : L20_2Inputs) :
    IncomingExceptionSource (paperEpsIn I) I :=
  incomingExceptionSource_paper I

/-- The source property is exactly eventual equality with `ρ`. -/
theorem rationalExceptionSource_iff_eventuallyEq (eps : ℕ → ℝ) (I : L20_2Inputs) :
    RationalExceptionSource eps I ↔
      ∀ᶠ n : ℕ in atTop, eps n = paperEpsRat I n :=
  Iff.rfl

/-- The source property is exactly eventual equality with `ρ`. -/
theorem incomingExceptionSource_iff_eventuallyEq (eps : ℕ → ℝ) (I : L20_2Inputs) :
    IncomingExceptionSource eps I ↔
      ∀ᶠ n : ℕ in atTop, eps n = paperEpsIn I n :=
  Iff.rfl

/-- Any sequence eventually equal to the paper's rational choice is a source. -/
theorem rationalExceptionSource_of_eventuallyEq_paper {eps : ℕ → ℝ}
    {I : L20_2Inputs}
    (h : ∀ᶠ n : ℕ in atTop, eps n = paperEpsRat I n) :
    RationalExceptionSource eps I :=
  (rationalExceptionSource_iff_eventuallyEq eps I).mpr h

/-- Any sequence eventually equal to the paper's incoming choice is a source. -/
theorem incomingExceptionSource_of_eventuallyEq_paper {eps : ℕ → ℝ}
    {I : L20_2Inputs}
    (h : ∀ᶠ n : ℕ in atTop, eps n = paperEpsIn I n) :
    IncomingExceptionSource eps I :=
  (incomingExceptionSource_iff_eventuallyEq eps I).mpr h

/-- Conversely, a rational source is eventually equal to the paper's choice. -/
theorem eventuallyEq_paper_of_rationalExceptionSource {eps : ℕ → ℝ}
    {I : L20_2Inputs} (h : RationalExceptionSource eps I) :
    ∀ᶠ n : ℕ in atTop, eps n = paperEpsRat I n :=
  (rationalExceptionSource_iff_eventuallyEq eps I).mp h

/-- Conversely, an incoming source is eventually equal to the paper's choice. -/
theorem eventuallyEq_paper_of_incomingExceptionSource {eps : ℕ → ℝ}
    {I : L20_2Inputs} (h : IncomingExceptionSource eps I) :
    ∀ᶠ n : ℕ in atTop, eps n = paperEpsIn I n :=
  (incomingExceptionSource_iff_eventuallyEq eps I).mp h

/-! ## 3. The smallest explicit equality form

The paper's choice need not be written as `ρ`; it is enough that it is the
explicit CRT plus smooth-character sum.  These are the smallest equality
statements from which the sources follow. -/

/-- A rational exception given by the CRT plus smooth-character sum is a
source. -/
theorem rationalExceptionSource_of_crt_add_char {eps : ℕ → ℝ}
    {I : L20_2Inputs}
    (h : ∀ᶠ n : ℕ in atTop, eps n = I.crtError n + I.charError n) :
    RationalExceptionSource eps I := by
  simpa only [RationalExceptionSource, paperEpsRat, L20_2Inputs.ρ] using h

/-- An incoming exception given by the CRT plus smooth-character sum is a
source. -/
theorem incomingExceptionSource_of_crt_add_char {eps : ℕ → ℝ}
    {I : L20_2Inputs}
    (h : ∀ᶠ n : ℕ in atTop, eps n = I.crtError n + I.charError n) :
    IncomingExceptionSource eps I := by
  simpa only [IncomingExceptionSource, paperEpsIn, L20_2Inputs.ρ] using h

/-- Pointwise version of the rational equality form. -/
theorem rationalExceptionSource_of_crt_add_char_pointwise {eps : ℕ → ℝ}
    {I : L20_2Inputs}
    (h : ∀ n : ℕ, eps n = I.crtError n + I.charError n) :
    RationalExceptionSource eps I :=
  rationalExceptionSource_of_crt_add_char (Eventually.of_forall h)

/-- Pointwise version of the incoming equality form. -/
theorem incomingExceptionSource_of_crt_add_char_pointwise {eps : ℕ → ℝ}
    {I : L20_2Inputs}
    (h : ∀ n : ℕ, eps n = I.crtError n + I.charError n) :
    IncomingExceptionSource eps I :=
  incomingExceptionSource_of_crt_add_char (Eventually.of_forall h)

/-! ## 4. Consequences inherited from the L20.2 budget -/

/-- The paper's rational exception is nonnegative. -/
theorem paperEpsRat_nonneg (I : L20_2Inputs) (n : ℕ) :
    0 ≤ paperEpsRat I n := by
  rw [paperEpsRat_apply_eq_rho]
  exact I.ρ_nonneg n

/-- The paper's incoming exception is nonnegative. -/
theorem paperEpsIn_nonneg (I : L20_2Inputs) (n : ℕ) :
    0 ≤ paperEpsIn I n := by
  rw [paperEpsIn_apply_eq_rho]
  exact I.ρ_nonneg n

/-- The paper's rational exception inherits the L20.2
`(1/2) exp (-4 A log D)` budget. -/
theorem paperEpsRat_le_paper (I : L20_2Inputs) :
    ∀ᶠ n : ℕ in atTop,
      paperEpsRat I n ≤ (1 / 2) * exp (-4 * I.A n * scale n) :=
  rationalSource_le_paper (rationalExceptionSource_paper I)

/-- The paper's incoming exception inherits the same budget. -/
theorem paperEpsIn_le_paper (I : L20_2Inputs) :
    ∀ᶠ n : ℕ in atTop,
      paperEpsIn I n ≤ (1 / 2) * exp (-4 * I.A n * scale n) :=
  incomingSource_le_paper (incomingExceptionSource_paper I)

/-- The paper's rational exception is a `SubexpLoss`. -/
theorem paperEpsRat_subexp (I : L20_2Inputs) :
    SubexpLoss (paperEpsRat I) :=
  rationalSource_subexp (rationalExceptionSource_paper I)

/-- The paper's incoming exception is a `SubexpLoss`. -/
theorem paperEpsIn_subexp (I : L20_2Inputs) :
    SubexpLoss (paperEpsIn I) :=
  incomingSource_subexp (incomingExceptionSource_paper I)

/-- The `RationalFromExceptions` form of the paper's choice. -/
theorem paperRationalFromExceptions (I : L20_2Inputs) :
    RationalFromExceptions (paperEpsRat I) I :=
  rationalFromExceptions_of_source (rationalExceptionSource_paper I)

/-- The `IncomingFromExceptions` form of the paper's choice. -/
theorem paperIncomingFromExceptions (I : L20_2Inputs) :
    IncomingFromExceptions (paperEpsIn I) I :=
  incomingFromExceptions_of_source (incomingExceptionSource_paper I)

/-! ## 4b. The elliptic `η` source

The same file records the paper's elliptic deletion fraction `η`: it is the
L21.2 exceptional fraction, so `EllipticFromL21_2` holds by reflexivity and the
`SubexpLoss` field is the already-proved L21.2 estimate. -/

/-- The paper's elliptic deletion fraction `η`: the L21.2 exceptional fraction. -/
noncomputable def paperEta (I : Cogentic.RandomizedL21_2.L21_2Inputs) : ℕ → ℝ :=
  fun n => I.loss n

/-- Pointwise identification with the L21.2 loss. -/
theorem paperEta_apply (I : Cogentic.RandomizedL21_2.L21_2Inputs) (n : ℕ) :
    paperEta I n = I.loss n :=
  rfl

/-- **The paper's `η` is the L21.2 exceptional fraction.** -/
theorem ellipticFromL21_2_paperEta
    (I : Cogentic.RandomizedL21_2.L21_2Inputs) :
    EllipticFromL21_2 (paperEta I) I :=
  fun _ => rfl

/-- The paper's `η` is nonnegative. -/
theorem paperEta_nonneg (I : Cogentic.RandomizedL21_2.L21_2Inputs) (n : ℕ) :
    0 ≤ paperEta I n :=
  I.loss_nonneg n

/-- The paper's `η` is a `SubexpLoss`, inherited from L21.2. -/
theorem paperEta_subexp (I : Cogentic.RandomizedL21_2.L21_2Inputs) :
    SubexpLoss (paperEta I) :=
  subexpLoss_of_L21_2 I

/-! ## 5. Concrete smooth-character specialization

`L20_2CharInputs` builds an `L20_2Inputs` whose `crtError` is the actual
truncated geometric tail `geometricCRTError` and whose `charError` is the actual
normalized smooth-character error `smoothCharacterError`.  The paper's budget
therefore has the concrete form below. -/

/-- The paper's rational budget on the concrete L20.2 character inputs. -/
noncomputable def paperEpsRatOfChar (S : L20_2CharInputs) : ℕ → ℝ :=
  paperEpsRat S.toInputs

/-- The paper's incoming budget on the concrete L20.2 character inputs. -/
noncomputable def paperEpsInOfChar (S : L20_2CharInputs) : ℕ → ℝ :=
  paperEpsIn S.toInputs

/-- The concrete rational budget is the geometric CRT tail plus the actual
smooth-character error. -/
theorem paperEpsRatOfChar_apply (S : L20_2CharInputs) (n : ℕ) :
    paperEpsRatOfChar S n =
      geometricCRTError n + smoothCharacterError (S.charData n) := by
  simp only [paperEpsRatOfChar, paperEpsRat, L20_2CharInputs.toInputs,
    L20_2CharInputs.toSubInputs, L20_2SubInputs.toInputs, L20_2CharInputs.charError]

/-- The concrete incoming budget is the geometric CRT tail plus the actual
smooth-character error. -/
theorem paperEpsInOfChar_apply (S : L20_2CharInputs) (n : ℕ) :
    paperEpsInOfChar S n =
      geometricCRTError n + smoothCharacterError (S.charData n) := by
  simp only [paperEpsInOfChar, paperEpsIn, L20_2CharInputs.toInputs,
    L20_2CharInputs.toSubInputs, L20_2SubInputs.toInputs, L20_2CharInputs.charError]

/-- The concrete rational budget is exactly the rule of `S.toInputs`. -/
theorem paperEpsRatOfChar_eq_rho (S : L20_2CharInputs) :
    paperEpsRatOfChar S = fun n => S.toInputs.ρ n :=
  paperEpsRat_eq_rho S.toInputs

/-- The concrete incoming budget is exactly the rule of `S.toInputs`. -/
theorem paperEpsInOfChar_eq_rho (S : L20_2CharInputs) :
    paperEpsInOfChar S = fun n => S.toInputs.ρ n :=
  paperEpsIn_eq_rho S.toInputs

/-- The paper's rational source, for the concrete character bundle. -/
theorem rationalExceptionSource_paperOfChar (S : L20_2CharInputs) :
    RationalExceptionSource (paperEpsRatOfChar S) S.toInputs :=
  rationalExceptionSource_paper S.toInputs

/-- The paper's incoming source, for the concrete character bundle. -/
theorem incomingExceptionSource_paperOfChar (S : L20_2CharInputs) :
    IncomingExceptionSource (paperEpsInOfChar S) S.toInputs :=
  incomingExceptionSource_paper S.toInputs

/-- The concrete rational budget is a `SubexpLoss`. -/
theorem paperEpsRatOfChar_subexp (S : L20_2CharInputs) :
    SubexpLoss (paperEpsRatOfChar S) :=
  paperEpsRat_subexp S.toInputs

/-- The concrete incoming budget is a `SubexpLoss`. -/
theorem paperEpsInOfChar_subexp (S : L20_2CharInputs) :
    SubexpLoss (paperEpsInOfChar S) :=
  paperEpsIn_subexp S.toInputs

/-! ## 6. Assembling the interior source data

The paper's choices only need the base concentration input, the elliptic L21.2
input, and the L20.2 budgets that supply `ρ` for the rational and incoming
exceptions. -/

/-- The data needed when `ε_rat` and `ε_in` are the paper's `ρ` choices: a base
concentration input, an elliptic L21.2 input, and one L20.2 budget for each
exception. -/
structure PaperExceptionSources (interior : ℕ → ℕ → ℝ) (L : ℕ)
    (eta : ℕ → ℝ) where
  /-- The L20.2 input controlling the base mass. -/
  base : L20_2Inputs
  /-- The base mass is the L20.2 normalized concentration discrepancy. -/
  base_source : BaseConcentrationSource interior L base
  /-- The L20.2 input supplying the paper's rational exception budget. -/
  rational : L20_2Inputs
  /-- The L21.2 elliptic input. -/
  elliptic : Cogentic.RandomizedL21_2.L21_2Inputs
  /-- The elliptic fraction is the L21.2 exceptional fraction. -/
  elliptic_source : EllipticFromL21_2 eta elliptic
  /-- The L20.2 input supplying the paper's incoming exception budget. -/
  incoming : L20_2Inputs

namespace PaperExceptionSources

variable {interior : ℕ → ℕ → ℝ} {L : ℕ} {eta : ℕ → ℝ}

/-- The paper's choice fills `InteriorBaseSources` with no additional source
hypothesis for `ε_rat` or `ε_in`. -/
def toInteriorBaseSources (S : PaperExceptionSources interior L eta) :
    InteriorBaseSources interior L eta
      (paperEpsRat S.rational) (paperEpsIn S.incoming) where
  base := S.base
  base_source := S.base_source
  rational := S.rational
  rational_source := rationalExceptionSource_paper S.rational
  elliptic := S.elliptic
  elliptic_source := S.elliptic_source
  incoming := S.incoming
  incoming_source := incomingExceptionSource_paper S.incoming

/-- The resulting `InteriorSourceData`. -/
noncomputable def toInteriorSourceData (S : PaperExceptionSources interior L eta) :
    InteriorSourceData interior L eta
      (paperEpsRat S.rational) (paperEpsIn S.incoming) :=
  S.toInteriorBaseSources.toInteriorSourceData

/-- **The four interior concentration fields, with the paper's `ε_rat` and
`ε_in` choices.** -/
theorem subProps (S : PaperExceptionSources interior L eta) :
    InteriorSubProps interior L eta
      (paperEpsRat S.rational) (paperEpsIn S.incoming) :=
  S.toInteriorBaseSources.subProps

end PaperExceptionSources

/-- **The canonical concrete instance.**  The base mass is the L20.2
concentration loss, the elliptic fraction is the L21.2 loss, and both exception
sequences are the paper's CRT plus character budget. -/
noncomputable def paperExceptionSources
    (base rational incoming : L20_2Inputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ) :
    PaperExceptionSources (concentrationBase base) L (fun n => elliptic.loss n) where
  base := base
  base_source := baseConcentrationSource_concrete base L
  rational := rational
  elliptic := elliptic
  elliptic_source := fun _ => rfl
  incoming := incoming

/-- The canonical concrete instance realizes `InteriorSourceData`. -/
noncomputable def paperInteriorSourceData
    (base rational incoming : L20_2Inputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ) :
    InteriorSourceData (concentrationBase base) L (fun n => elliptic.loss n)
      (paperEpsRat rational) (paperEpsIn incoming) :=
  (paperExceptionSources base rational incoming elliptic L).toInteriorSourceData

/-- **The canonical concrete instance realizes all four interior fields.** -/
theorem paperSubProps
    (base rational incoming : L20_2Inputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ) :
    InteriorSubProps (concentrationBase base) L (fun n => elliptic.loss n)
      (paperEpsRat rational) (paperEpsIn incoming) :=
  (paperExceptionSources base rational incoming elliptic L).subProps

/-- The canonical concrete instance with the exception budgets taken from the
concrete L20.2 character bundles. -/
noncomputable def charPaperExceptionSources
    (base : L20_2Inputs) (rational incoming : L20_2CharInputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ) :
    PaperExceptionSources (concentrationBase base) L (fun n => elliptic.loss n) where
  base := base
  base_source := baseConcentrationSource_concrete base L
  rational := rational.toInputs
  elliptic := elliptic
  elliptic_source := fun _ => rfl
  incoming := incoming.toInputs

/-- The concrete character instance realizes all four interior fields with the
paper's exceptions written as `geometricCRTError + smoothCharacterError`. -/
theorem charPaperSubProps
    (base : L20_2Inputs) (rational incoming : L20_2CharInputs)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs) (L : ℕ) :
    InteriorSubProps (concentrationBase base) L (fun n => elliptic.loss n)
      (paperEpsRatOfChar rational) (paperEpsInOfChar incoming) :=
  (charPaperExceptionSources base rational incoming elliptic L).subProps

/-! ## Axiom audit -/

#print axioms paperEpsRat_eq_rho
#print axioms paperEpsIn_eq_rho
#print axioms rationalExceptionSource_paper
#print axioms incomingExceptionSource_paper
#print axioms paperRationalExceptionSource
#print axioms paperIncomingExceptionSource
#print axioms rationalExceptionSource_iff_eventuallyEq
#print axioms incomingExceptionSource_iff_eventuallyEq
#print axioms rationalExceptionSource_of_eventuallyEq_paper
#print axioms incomingExceptionSource_of_eventuallyEq_paper
#print axioms eventuallyEq_paper_of_rationalExceptionSource
#print axioms eventuallyEq_paper_of_incomingExceptionSource
#print axioms rationalExceptionSource_of_crt_add_char
#print axioms incomingExceptionSource_of_crt_add_char
#print axioms rationalExceptionSource_of_crt_add_char_pointwise
#print axioms incomingExceptionSource_of_crt_add_char_pointwise
#print axioms paperEpsRat_nonneg
#print axioms paperEpsIn_nonneg
#print axioms paperEpsRat_le_paper
#print axioms paperEpsIn_le_paper
#print axioms paperEpsRat_subexp
#print axioms paperEpsIn_subexp
#print axioms paperRationalFromExceptions
#print axioms paperIncomingFromExceptions
#print axioms paperEta_apply
#print axioms ellipticFromL21_2_paperEta
#print axioms paperEta_nonneg
#print axioms paperEta_subexp
#print axioms paperEpsRatOfChar_apply
#print axioms paperEpsInOfChar_apply
#print axioms rationalExceptionSource_paperOfChar
#print axioms incomingExceptionSource_paperOfChar
#print axioms paperEpsRatOfChar_subexp
#print axioms paperEpsInOfChar_subexp
#print axioms PaperExceptionSources.toInteriorBaseSources
#print axioms PaperExceptionSources.toInteriorSourceData
#print axioms PaperExceptionSources.subProps
#print axioms paperExceptionSources
#print axioms paperInteriorSourceData
#print axioms paperSubProps
#print axioms charPaperExceptionSources
#print axioms charPaperSubProps

end Cogentic.RandomizedL20_4EtaSource
