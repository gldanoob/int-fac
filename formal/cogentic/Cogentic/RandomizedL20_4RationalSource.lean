import Cogentic.RandomizedL20_4InteriorBase
import Cogentic.RandomizedL20_2Char

set_option linter.style.haveILetI false

/-!
# L20.4 rational source: the paper's `ε_rat` is the L20.2 `ρ`

`Cogentic.RandomizedL20_4InteriorBase` isolates the G.11 rational source as the
identification

`RationalExceptionSource epsRat I` : `epsRat n = I.ρ n` eventually,

where `I.ρ = I.crtError + I.charError` is the L20.2 CRT plus smooth-character
budget.  This file makes the identification explicit in both directions:

* the **paper's `ε_rat`** is the sum of the two exception budgets,
  `paperEpsRat crtError charError n = crtError n + charError n`
  (`paperEpsRat`);
* `paperEpsRat I.crtError I.charError` is *definitionally* `I.ρ`
  (`paperEpsRat_eq_rho`), hence satisfies `RationalExceptionSource`
  (`rationalExceptionSource_paper`);
* the source statement is equivalent to the smallest explicit equality
  `epsRat n = I.crtError n + I.charError n`, with no reference to the name `ρ`
  (`rationalExceptionSource_iff_crt_add_char`), and the parent inequality is
  equivalent to the corresponding `≤` statement
  (`rationalFromExceptions_iff_crt_add_char`);
* the same identification is made for the two reduced L20.2 bundles:
  `L20_2SubInputs` (whose CRT budget is the *proved* truncated geometric tail
  `geometricCRTError`) and `L20_2CharInputs` (whose character budget is the
  *actual* normalized smooth-character error `smoothCharacterError`).
  For the latter the paper sequence is
  `paperCharEpsRat S n = geometricCRTError n + smoothCharacterError (S.charData n)`,
  and it satisfies `RationalExceptionSource` for `S.toInputs`
  (`rationalExceptionSource_char`).

No term is dropped and no loss is set to zero: `paperEpsRat` is the literal sum
of the two nonnegative deficits, and `paperCharEpsRat` uses the proved geometric
CRT tail and the concrete character error rather than an abstract budget.
The inherited `D^{-B}` and `(1/2) D^{-4A}` bounds are the existing L20.2
estimates transported across the identification.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL20_4RationalSource

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Char
open Cogentic.RandomizedL20_4Interior
open Cogentic.RandomizedL20_4InteriorBase
open Cogentic.RandomizedL19SecondMoment

/-! ## 1. The paper's rational error as a CRT plus character sum -/

/-- The paper's G.11 rational error `ε_rat`: the sum of the truncated-geometric
CRT defect and the smooth-character error.  This is the object the manuscript
denotes by `ε_rat`; the two summands are exactly the L20.2 budgets. -/
def paperEpsRat (crtError charError : ℕ → ℝ) : ℕ → ℝ :=
  fun n => crtError n + charError n

/-- The unfolded value of the paper rational error. -/
theorem paperEpsRat_apply (crtError charError : ℕ → ℝ) (n : ℕ) :
    paperEpsRat crtError charError n = crtError n + charError n := rfl

/-- **The paper's `ε_rat` is the L20.2 `ρ`.**  The L20.2 budget is defined as
`ρ = crtError + charError`, so the identification is definitional; no estimate
is introduced and no term is lost. -/
theorem paperEpsRat_eq_rho (I : L20_2Inputs) :
    paperEpsRat I.crtError I.charError = I.ρ := rfl

/-- The pointwise form of `paperEpsRat_eq_rho`. -/
theorem paperEpsRat_eq_rho_apply (I : L20_2Inputs) (n : ℕ) :
    paperEpsRat I.crtError I.charError n = I.ρ n := rfl

/-! ## 2. The smallest explicit equality -/

/-- The smallest explicit source: the paper error equals the literal CRT plus
smooth-character sum, with the derived abbreviation `ρ` unfolded. -/
def RationalCRTCharSource (epsRat : ℕ → ℝ) (I : L20_2Inputs) : Prop :=
  ∀ᶠ n : ℕ in atTop, epsRat n = I.crtError n + I.charError n

/-- **The source is the explicit CRT-plus-character equality.**  This is the
smallest form of `RationalExceptionSource`: it mentions the two paper budgets
directly and never the derived name `ρ`. -/
theorem rationalExceptionSource_iff_crt_add_char {epsRat : ℕ → ℝ}
    {I : L20_2Inputs} :
    RationalExceptionSource epsRat I ↔ RationalCRTCharSource epsRat I := by
  simp only [RationalExceptionSource, RationalCRTCharSource, L20_2Inputs.ρ]

/-- The parent inequality in the same explicit CRT-plus-character form.  This is
the weakest source that the G.11 recurrence consumes. -/
theorem rationalFromExceptions_iff_crt_add_char {epsRat : ℕ → ℝ}
    {I : L20_2Inputs} :
    RationalFromExceptions epsRat I ↔
      ∀ᶠ n : ℕ in atTop, epsRat n ≤ I.crtError n + I.charError n := by
  simp only [RationalFromExceptions, L20_2Inputs.ρ]

/-- The smallest explicit equality directly implies the source. -/
theorem rationalExceptionSource_of_crt_add_char {epsRat : ℕ → ℝ}
    {I : L20_2Inputs} (h : RationalCRTCharSource epsRat I) :
    RationalExceptionSource epsRat I :=
  rationalExceptionSource_iff_crt_add_char.mpr h

/-- The equality form against `ρ` is the source statement itself. -/
theorem rationalExceptionSource_of_eq_rho {epsRat : ℕ → ℝ} {I : L20_2Inputs}
    (h : ∀ᶠ n : ℕ in atTop, epsRat n = I.ρ n) :
    RationalExceptionSource epsRat I :=
  h

/-- The smallest explicit `≤` statement directly implies the parent inequality. -/
theorem rationalFromExceptions_of_crt_add_char_le {epsRat : ℕ → ℝ}
    {I : L20_2Inputs}
    (h : ∀ᶠ n : ℕ in atTop, epsRat n ≤ I.crtError n + I.charError n) :
    RationalFromExceptions epsRat I :=
  rationalFromExceptions_iff_crt_add_char.mpr h

/-- **`RationalExceptionSource` for the paper's `ε_rat`.**  The sequence
`paperEpsRat I.crtError I.charError` is the L20.2 budget `I.ρ` by definition. -/
theorem rationalExceptionSource_paper (I : L20_2Inputs) :
    RationalExceptionSource (paperEpsRat I.crtError I.charError) I :=
  Eventually.of_forall fun _ => rfl

/-- The paper sequence satisfies the smallest explicit equality itself. -/
theorem rationalCRTCharSource_paper (I : L20_2Inputs) :
    RationalCRTCharSource (paperEpsRat I.crtError I.charError) I :=
  Eventually.of_forall fun _ => rfl

/-- The paper rational error realizes the parent `RationalFromExceptions`
inequality. -/
theorem rationalFromExceptions_paper (I : L20_2Inputs) :
    RationalFromExceptions (paperEpsRat I.crtError I.charError) I :=
  rationalFromExceptions_of_source (rationalExceptionSource_paper I)

/-- The paper rational error is nonnegative: both summands are nonnegative
budgets. -/
theorem paperEpsRat_nonneg (I : L20_2Inputs) (n : ℕ) :
    0 ≤ paperEpsRat I.crtError I.charError n := by
  rw [paperEpsRat_apply]
  exact add_nonneg (I.crt_law.2 n).1 (I.char_sum.2 n).1

/-! ## 3. The L20.2 estimates inherited by the paper source -/

/-- The paper rational error inherits the L20.2 CRT plus smooth-character bound
`ρ ≤ (1/2) exp (-4 A log D)`. -/
theorem paperEpsRat_le_paper (I : L20_2Inputs) :
    ∀ᶠ n : ℕ in atTop,
      paperEpsRat I.crtError I.charError n ≤
        (1 / 2) * exp (-4 * I.A n * scale n) :=
  rationalSource_le_paper (rationalExceptionSource_paper I)

/-- The paper rational error is a `SubexpLoss`: the sum of the two L20.2
exception budgets is `D^{-B}` for every `B`. -/
theorem paperEpsRat_subexp (I : L20_2Inputs) :
    SubexpLoss (paperEpsRat I.crtError I.charError) :=
  rationalSource_subexp (rationalExceptionSource_paper I)

/-! ## 4. The reduced L20.2 sub-bundle: proved CRT tail plus character budget -/

/-- For an `L20_2SubInputs` bundle the CRT budget is the proved truncated
geometric tail and the character budget is the bundle's `charError`.  The
resulting `ρ` is the paper rational error for those two explicit sequences. -/
theorem subInputs_rho_eq (S : L20_2SubInputs) :
    S.toInputs.ρ = paperEpsRat geometricCRTError S.charError := rfl

/-- **`RationalExceptionSource` for the reduced L20.2 sub-bundle.**  The paper
rational error built from the proved geometric CRT tail and the character budget
is the `ρ` of `S.toInputs`. -/
theorem rationalExceptionSource_subInputs (S : L20_2SubInputs) :
    RationalExceptionSource (paperEpsRat geometricCRTError S.charError) S.toInputs :=
  Eventually.of_forall fun _ => rfl

/-- The reduced sub-bundle's rational error is subexponential. -/
theorem paperEpsRat_subInputs_subexp (S : L20_2SubInputs) :
    SubexpLoss (paperEpsRat geometricCRTError S.charError) :=
  rationalSource_subexp (rationalExceptionSource_subInputs S)

/-! ## 5. The concrete character bundle: actual CRT tail and actual character error -/

/-- The paper rational error for the concrete `L20_2CharInputs` bundle: the
proved geometric CRT remainder plus the actual normalized smooth-character
error of the bundle's data. -/
noncomputable def paperCharEpsRat (S : L20_2CharInputs) : ℕ → ℝ :=
  paperEpsRat geometricCRTError (fun n => smoothCharacterError (S.charData n))

/-- The concrete paper rational error is the `ρ` of the bundle's L20.2 inputs. -/
theorem charInputs_rho_eq (S : L20_2CharInputs) :
    S.toInputs.ρ = paperCharEpsRat S := rfl

/-- **The concrete `RationalExceptionSource`.**  The paper rational error built
from the proved geometric CRT tail and the actual smooth-character error is the
L20.2 `ρ` of `S.toInputs`. -/
theorem rationalExceptionSource_char (S : L20_2CharInputs) :
    RationalExceptionSource (paperCharEpsRat S) S.toInputs :=
  Eventually.of_forall fun _ => rfl

/-- The concrete paper rational error is the parent `RationalFromExceptions`
budget. -/
theorem rationalFromExceptions_char (S : L20_2CharInputs) :
    RationalFromExceptions (paperCharEpsRat S) S.toInputs :=
  rationalFromExceptions_of_source (rationalExceptionSource_char S)

/-- The concrete paper rational error is nonnegative. -/
theorem paperCharEpsRat_nonneg (S : L20_2CharInputs) (n : ℕ) :
    0 ≤ paperCharEpsRat S n := by
  unfold paperCharEpsRat paperEpsRat
  exact add_nonneg (geometricCRTError_nonneg n) (smoothCharacterError_nonneg (S.charData n))

/-- The concrete paper rational error inherits the L20.2 `(1/2) D^{-4A}` bound. -/
theorem paperCharEpsRat_le_paper (S : L20_2CharInputs) :
    ∀ᶠ n : ℕ in atTop,
      paperCharEpsRat S n ≤
        (1 / 2) * exp (-4 * S.toInputs.A n * scale n) :=
  rationalSource_le_paper (rationalExceptionSource_char S)

/-- The concrete paper rational error is a `SubexpLoss`. -/
theorem paperCharEpsRat_subexp (S : L20_2CharInputs) :
    SubexpLoss (paperCharEpsRat S) :=
  rationalSource_subexp (rationalExceptionSource_char S)

/-- **The concrete budgets at their own rate.**  The proved geometric CRT tail
is at most `exp (-2 D log D)` and the actual character error is at most
`exp (-cChar D log D)`, so their sum is at most
`2 exp (-min 2 cChar · D log D)`.  This records that `paperCharEpsRat` is a
genuine sum of the two nonnegative deficits, not a renamed hypothesis. -/
theorem paperCharEpsRat_le_two_exp (S : L20_2CharInputs) :
    ∀ᶠ n : ℕ in atTop,
      paperCharEpsRat S n ≤
        2 * exp (-(min 2 S.cChar) * paperD n * scale n) := by
  filter_upwards [scale_grows.eventually_ge_atTop 0] with n hs
  have hX : 0 ≤ paperD n * scale n := mul_nonneg (paperD_pos n).le hs
  have hcrt : geometricCRTError n ≤
      exp (-(min 2 S.cChar) * (paperD n * scale n)) := by
    refine (geometricCRTError_le n).trans ?_
    apply exp_le_exp.mpr
    have hle : min 2 S.cChar ≤ 2 := min_le_left _ _
    nlinarith only [hle, hX]
  have hchar : smoothCharacterError (S.charData n) ≤
      exp (-(min 2 S.cChar) * (paperD n * scale n)) := by
    refine (smoothCharacterError_le (S.charData n) (exp_pos _).le
      (fun χ hχ => S.char_concrete n χ hχ)).trans ?_
    apply exp_le_exp.mpr
    have hle : min 2 S.cChar ≤ S.cChar := min_le_right _ _
    nlinarith only [hle, hX]
  unfold paperCharEpsRat paperEpsRat
  calc
    geometricCRTError n + smoothCharacterError (S.charData n)
        ≤ exp (-(min 2 S.cChar) * (paperD n * scale n)) +
            exp (-(min 2 S.cChar) * (paperD n * scale n)) := add_le_add hcrt hchar
    _ = 2 * exp (-(min 2 S.cChar) * paperD n * scale n) := by
        rw [show -(min 2 S.cChar) * (paperD n * scale n) =
          -(min 2 S.cChar) * paperD n * scale n by ring]
        ring

/-- The same subexponential conclusion, but derived directly from the concrete
CRT and character rates rather than from the `ρ` of the rebuilt L20.2 inputs. -/
theorem paperCharEpsRat_subexp_direct (S : L20_2CharInputs) :
    SubexpLoss (paperCharEpsRat S) := by
  have hmin : 0 < min 2 S.cChar := lt_min (by norm_num) S.cChar_pos
  refine subexpLoss_of_eventually_le (paperCharEpsRat_le_two_exp S) ?_
  exact subexpLoss_two_mul (subexpLoss_exp_neg_paperD hmin)

/-! ## 6. The rational-source bundle -/

/-- A rational source for the G.11 interior step: an L20.2 input together with
the identification of the paper's `ε_rat` with its CRT plus smooth-character
budget.  This is the rational-field part of `InteriorBaseSources`, with the
identification kept as an explicit equality rather than hidden in a `≤`. -/
structure G11RationalSource (epsRat : ℕ → ℝ) where
  /-- The L20.2 CRT plus smooth-character input. -/
  rational : L20_2Inputs
  /-- The paper rational error is the L20.2 CRT plus character budget. -/
  source : RationalExceptionSource epsRat rational

namespace G11RationalSource

variable {epsRat : ℕ → ℝ}

/-- The parent `RationalFromExceptions` inequality. -/
theorem rationalFrom (S : G11RationalSource epsRat) :
    RationalFromExceptions epsRat S.rational :=
  rationalFromExceptions_of_source S.source

/-- The rational error is a `SubexpLoss`. -/
theorem epsRat_subexp (S : G11RationalSource epsRat) : SubexpLoss epsRat :=
  rationalSource_subexp S.source

/-- The rational error inherits the L20.2 `(1/2) D^{-4A}` paper budget. -/
theorem le_paper (S : G11RationalSource epsRat) :
    ∀ᶠ n : ℕ in atTop,
      epsRat n ≤ (1 / 2) * exp (-4 * S.rational.A n * scale n) :=
  rationalSource_le_paper S.source

end G11RationalSource

/-- The canonical rational source of the paper: `ε_rat` is the L20.2 `ρ` of
`I`. -/
def paperG11RationalSource (I : L20_2Inputs) :
    G11RationalSource (paperEpsRat I.crtError I.charError) where
  rational := I
  source := rationalExceptionSource_paper I

/-- The reduced-bundle rational source: the CRT budget is the proved geometric
tail `geometricCRTError` and the character budget is `S.charError`. -/
noncomputable def paperG11RationalSourceOfSub (S : L20_2SubInputs) :
    G11RationalSource (paperEpsRat geometricCRTError S.charError) where
  rational := S.toInputs
  source := rationalExceptionSource_subInputs S

/-- The concrete character-bundle rational source: the CRT budget is the proved
geometric tail and the character budget is the actual normalized
smooth-character error. -/
noncomputable def paperG11RationalSourceOfChar (S : L20_2CharInputs) :
    G11RationalSource (paperCharEpsRat S) where
  rational := S.toInputs
  source := rationalExceptionSource_char S

/-! ## 7. Feeding `InteriorSourceData` -/

/-- **The G.11 interior data with the rational field sourced concretely.**
The base field remains the L20.2 concentration source, the elliptic field is
L21.2, the incoming exception is an explicit `SubexpLoss`, and the rational
field is the concrete paper sequence `paperCharEpsRat S`. -/
noncomputable def interiorSourceData_of_char_source {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {eta epsIn : ℕ → ℝ}
    (S : L20_2CharInputs)
    (base : L20_2Inputs) (hbase : BaseConcentrationSource interior L base)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs)
    (hell : EllipticFromL21_2 eta elliptic)
    (hin : SubexpLoss epsIn) :
    Cogentic.RandomizedL20_4Interior.InteriorSourceData interior L eta
      (paperCharEpsRat S) epsIn :=
  interiorSourceData_of_sources base hbase S.toInputs (rationalExceptionSource_char S)
    elliptic hell hin

/-- The sourced interior data realize the four interior `SubexpLoss` fields. -/
theorem interiorSubProps_of_char_source {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {eta epsIn : ℕ → ℝ}
    (S : L20_2CharInputs)
    (base : L20_2Inputs) (hbase : BaseConcentrationSource interior L base)
    (elliptic : Cogentic.RandomizedL21_2.L21_2Inputs)
    (hell : EllipticFromL21_2 eta elliptic)
    (hin : SubexpLoss epsIn) :
    Cogentic.RandomizedL20_4Conditioned.InteriorSubProps interior L eta
      (paperCharEpsRat S) epsIn :=
  (interiorSourceData_of_char_source S base hbase elliptic hell hin).subProps

/-! ## Axiom audit -/

#print axioms paperEpsRat_apply
#print axioms paperEpsRat_eq_rho
#print axioms paperEpsRat_eq_rho_apply
#print axioms rationalExceptionSource_iff_crt_add_char
#print axioms rationalFromExceptions_iff_crt_add_char
#print axioms rationalExceptionSource_of_crt_add_char
#print axioms rationalExceptionSource_of_eq_rho
#print axioms rationalFromExceptions_of_crt_add_char_le
#print axioms rationalCRTCharSource_paper
#print axioms rationalExceptionSource_paper
#print axioms rationalFromExceptions_paper
#print axioms paperEpsRat_nonneg
#print axioms paperEpsRat_le_paper
#print axioms paperEpsRat_subexp
#print axioms subInputs_rho_eq
#print axioms rationalExceptionSource_subInputs
#print axioms paperEpsRat_subInputs_subexp
#print axioms charInputs_rho_eq
#print axioms rationalExceptionSource_char
#print axioms rationalFromExceptions_char
#print axioms paperCharEpsRat_nonneg
#print axioms paperCharEpsRat_le_paper
#print axioms paperCharEpsRat_subexp
#print axioms paperCharEpsRat_le_two_exp
#print axioms paperCharEpsRat_subexp_direct
#print axioms G11RationalSource.rationalFrom
#print axioms G11RationalSource.epsRat_subexp
#print axioms G11RationalSource.le_paper
#print axioms paperG11RationalSource
#print axioms paperG11RationalSourceOfSub
#print axioms paperG11RationalSourceOfChar
#print axioms interiorSourceData_of_char_source
#print axioms interiorSubProps_of_char_source

end Cogentic.RandomizedL20_4RationalSource
