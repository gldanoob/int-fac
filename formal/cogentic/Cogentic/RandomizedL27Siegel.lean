import Cogentic.RandomizedL27TraceClass

/-!
# L27 Siegel: the smallest explicit Hurwitz/class-number input

`Cogentic.RandomizedL27Hurwitz` isolates the analytic leaf
`HurwitzSiegelLowerTrace`: for every Frobenius trace `t` with positive
discriminant `D = 4p - t²`, the Hurwitz class number satisfies
`H(-D) ≥ c√D`.  `Cogentic.RandomizedL27TraceClass` removes the two trace-class
`Prop`s, but still keeps that Siegel leaf as an abstract field.

This file reduces the leaf further, to two explicitly named arithmetic inputs.

## The two inputs

For an imaginary quadratic order of discriminant `-D`, the lower half of the
order class-number formula is

`H(-D) ≥ (1/(2π)) · L(1, χ_D) · √D`.

The order formula's Euler product over the conductor is at least one, so this
inequality is the part of the formula that is used below.  It is recorded as
`HurwitzClassNumberFormulaLower`.  The remaining analytic input is a uniform
positive lower bound for the quadratic `L`-value,

`0 < l ≤ L(1, χ_D)` on Frobenius discriminants.

The constant `1/(2π)` is named `classNumberFormulaConstant`.  Composing the two
inputs gives the Siegel leaf with constant `classNumberFormulaConstant * l`;
this is `hurwitzSiegelLowerFrob_of_formula_and_LOne` and its trace form
`hurwitzSiegelLowerTrace_of_formula_and_LOne`.

## Why this is the smallest honest form

`HurwitzSiegelLower` quantifies over all positive integers `D`, but a Hurwitz
class number is only defined on discriminants.  The honest support is
`IsFrobeniusDiscriminant D`, i.e. `D = 4p - t² > 0` for some `p > 0`.  On that
support the normalized form

`c ≤ H(-D) / √D`

is exactly `HurwitzSiegelLowerFrob`; it is equivalent to the constant form and
to the trace form for any positive prime sequence.  The global
`HurwitzSiegelLower` is the conjunction of this honest support statement and an
unsupported off-discriminant statement.  The latter is never used by L27, so the
support form is the smallest statement with the same downstream content.

The classical effective Brauer–Siegel bound has a logarithmic loss,
`c√D/log(D+2)`.  `BrauerSiegelLower` records that shape, and
`brauerSiegelLowerOn_bounded` proves exactly what it gives on a bounded
discriminant range: a constant `c/log(X+2)` on `D ≤ X`.  It therefore does not
imply the paper's constant-`κ` leaf on an unbounded range; that leaf needs the
constant lower bound on `L(1, χ_D)` above.  The file states this gap explicitly
instead of hiding a logarithm.

Mathlib's class-number API supplies `NumberField.classNumber_pos` (positivity)
but no Brauer–Siegel lower bound.  The order formula inequality and the
constant `L`-bound are therefore kept as the two named arithmetic inputs, not
silently replaced by a zero count or by an unproved analytic lemma.

## Bundles

`L27SiegelInputs I` replaces the `siegel_lower` field of
`L27TraceClassInputs` by the two inputs `formula_lower` and `l_one_lower`.  Its
`toTraceClassInputs` derives the Siegel leaf and reassembles the old bundle, so
every L27.1 conclusion (`deuringLenstraCounts`, `reduced_ledger`,
`reduced_paper`, `toRatedLeaf`, `slot`) is re-exported without change.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No class number,
curve count, or loss is set to zero.
-/

namespace Cogentic.RandomizedL27Siegel

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27TraceClass
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The explicit constants and inputs -/

/-- The explicit constant in the lower half of the imaginary quadratic order
class-number formula: `1 / (2π)`. -/
def classNumberFormulaConstant : ℝ := 1 / (2 * Real.pi)

/-- The class-number-formula constant is positive. -/
theorem classNumberFormulaConstant_pos : 0 < classNumberFormulaConstant := by
  unfold classNumberFormulaConstant
  positivity

/-- The class-number-formula constant is nonnegative. -/
theorem classNumberFormulaConstant_nonneg : 0 ≤ classNumberFormulaConstant :=
  classNumberFormulaConstant_pos.le

/-- **Frobenius discriminants.**  The positive integers that occur as
`4p - t²` for a positive `p` and an integral trace `t`.  These are exactly the
`D ≡ 0, 3 (mod 4)` on which the Hurwitz class number is evaluated. -/
def IsFrobeniusDiscriminant (D : ℤ) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∃ t : ℤ, 0 < traceDisc p t ∧ D = traceDisc p t

/-- A Frobenius discriminant is positive. -/
theorem isFrobeniusDiscriminant_pos {D : ℤ}
    (h : IsFrobeniusDiscriminant D) : 0 < D := by
  obtain ⟨p, _hp, t, ht, rfl⟩ := h
  exact ht

/-- **The lower half of the order class-number formula.**  On every Frobenius
discriminant, `H(-D) ≥ c · L(1, χ_D) · √D`.  The canonical constant is
`classNumberFormulaConstant = 1/(2π)`; the definition keeps `c` explicit so
that a weaker literature normalization can be compared without changing the
reduction. -/
def HurwitzClassNumberFormulaLower (hurwitz L1 : ℤ → ℝ) (c : ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D →
    c * L1 D * Real.sqrt (D : ℝ) ≤ hurwitz D

/-- The class-number formula with the canonical constant `1/(2π)`. -/
def HurwitzClassNumberFormula (hurwitz L1 : ℤ → ℝ) : Prop :=
  HurwitzClassNumberFormulaLower hurwitz L1 classNumberFormulaConstant

/-- **A uniform lower bound for the quadratic `L`-value.**  On every Frobenius
discriminant, `l ≤ L(1, χ_D)`, with `l > 0`.  This is the constant-`L` input
that rules out a Siegel zero on the discriminants used by L27. -/
def DirichletLOneLower (L1 : ℤ → ℝ) (l : ℝ) : Prop :=
  0 < l ∧ ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D

/-- **Honest support form of the Siegel lower bound.**  The Hurwitz class
number is at least `c√D` on Frobenius discriminants.  This is the smallest
form of `HurwitzSiegelLower`: the global statement additionally quantifies over
non-discriminants, where no Hurwitz class number is being counted. -/
def HurwitzSiegelLowerFrob (hurwitz : ℤ → ℝ) (c : ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D →
    c * Real.sqrt (D : ℝ) ≤ hurwitz D

/-- The support form implies the trace leaf for any positive prime sequence. -/
theorem hurwitzSiegelLowerTrace_of_frob {p : ℕ → ℕ} {hurwitz : ℤ → ℝ}
    {c : ℝ} (hp : ∀ n, 0 < p n) (h : HurwitzSiegelLowerFrob hurwitz c) :
    HurwitzSiegelLowerTrace p hurwitz c := by
  intro n t ht
  exact h (traceDisc (p n) t) ⟨p n, hp n, t, ht, rfl⟩

/-- **Normalized form of the Siegel lower bound.**  `c ≤ H(-D)/√D` on
Frobenius discriminants.  This is the same inequality as
`HurwitzSiegelLowerFrob`; it exposes the ratio whose uniform positivity is the
actual Brauer–Siegel input. -/
def HurwitzSiegelRatioLower (hurwitz : ℤ → ℝ) (c : ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D →
    c ≤ hurwitz D / Real.sqrt (D : ℝ)

/-- **The classical effective Brauer–Siegel shape.**  A logarithmic loss is
kept: `c√D/log(D+2) ≤ H(-D)` on Frobenius discriminants. -/
def BrauerSiegelLower (hurwitz : ℤ → ℝ) (c : ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D →
    c * Real.sqrt (D : ℝ) / Real.log ((D : ℝ) + 2) ≤ hurwitz D

/-- **Brauer–Siegel on a bounded discriminant range.**  The same logarithmic
bound restricted to `D ≤ X`. -/
def BrauerSiegelLowerOn (hurwitz : ℤ → ℝ) (c X : ℝ) : Prop :=
  ∀ D : ℤ, IsFrobeniusDiscriminant D → (D : ℝ) ≤ X →
    c * Real.sqrt (D : ℝ) / Real.log ((D : ℝ) + 2) ≤ hurwitz D

/-! ## 2. The formula and `L`-value inputs imply Siegel -/

/-- **The class-number formula plus a constant `L`-lower bound gives the
Siegel leaf.**  If `H(-D) ≥ c · L(1, χ_D) · √D` and `l ≤ L(1, χ_D)`, then
`H(-D) ≥ (c l)√D` on Frobenius discriminants. -/
theorem hurwitzSiegelLowerFrob_of_formula_and_LOne
    {hurwitz L1 : ℤ → ℝ} {c l : ℝ}
    (hc : 0 ≤ c) (_hl : 0 < l)
    (hformula : HurwitzClassNumberFormulaLower hurwitz L1 c)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D) :
    HurwitzSiegelLowerFrob hurwitz (c * l) := by
  intro D hD
  have hsqrt : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hle : c * l ≤ c * L1 D :=
    mul_le_mul_of_nonneg_left (hL D hD) hc
  calc
    (c * l) * Real.sqrt (D : ℝ) ≤ (c * L1 D) * Real.sqrt (D : ℝ) :=
      mul_le_mul_of_nonneg_right hle hsqrt
    _ = c * L1 D * Real.sqrt (D : ℝ) := by ring
    _ ≤ hurwitz D := hformula D hD

/-- **The canonical formula input plus a constant `L`-lower bound.** -/
theorem hurwitzSiegelLowerFrob_of_formula
    {hurwitz L1 : ℤ → ℝ} {l : ℝ}
    (hl : 0 < l)
    (hformula : HurwitzClassNumberFormula hurwitz L1)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D) :
    HurwitzSiegelLowerFrob hurwitz (classNumberFormulaConstant * l) :=
  hurwitzSiegelLowerFrob_of_formula_and_LOne
    classNumberFormulaConstant_nonneg hl hformula hL

/-- **The trace form of the reduction.**  For any positive prime sequence
`p`, the two inputs give `HurwitzSiegelLowerTrace p hurwitz (c l)`.  This is the
leaf consumed by `L27HurwitzInputs`. -/
theorem hurwitzSiegelLowerTrace_of_formula_and_LOne
    {p : ℕ → ℕ} {hurwitz L1 : ℤ → ℝ} {c l : ℝ}
    (hp : ∀ n, 0 < p n)
    (hc : 0 ≤ c) (hl : 0 < l)
    (hformula : HurwitzClassNumberFormulaLower hurwitz L1 c)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D) :
    HurwitzSiegelLowerTrace p hurwitz (c * l) :=
  hurwitzSiegelLowerTrace_of_frob hp
    (hurwitzSiegelLowerFrob_of_formula_and_LOne hc hl hformula hL)

/-- **The trace form with the canonical class-number constant.** -/
theorem hurwitzSiegelLowerTrace_of_formula
    {p : ℕ → ℕ} {hurwitz L1 : ℤ → ℝ} {l : ℝ}
    (hp : ∀ n, 0 < p n)
    (hl : 0 < l)
    (hformula : HurwitzClassNumberFormula hurwitz L1)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D) :
    HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) :=
  hurwitzSiegelLowerTrace_of_frob hp
    (hurwitzSiegelLowerFrob_of_formula hl hformula hL)

/-- **The global form of the reduction.**  If the class-number formula and the
constant `L`-lower bound are available on every positive integer, the original
global `HurwitzSiegelLower` follows.  The support version above is the honest
smallest form: the extra quantifier over non-discriminants is not used by L27,
but this theorem records that the global leaf also reduces to the same two
arithmetic inputs. -/
theorem hurwitzSiegelLower_of_formula_and_LOneGlobal
    {hurwitz L1 : ℤ → ℝ} {c l : ℝ}
    (hc : 0 ≤ c) (_hl : 0 < l)
    (hformula : ∀ D : ℤ, 0 < D →
      c * L1 D * Real.sqrt (D : ℝ) ≤ hurwitz D)
    (hL : ∀ D : ℤ, 0 < D → l ≤ L1 D) :
    HurwitzSiegelLower hurwitz (c * l) := by
  intro D hD
  have hsqrt : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hle : c * l ≤ c * L1 D :=
    mul_le_mul_of_nonneg_left (hL D hD) hc
  calc
    (c * l) * Real.sqrt (D : ℝ) ≤ (c * L1 D) * Real.sqrt (D : ℝ) :=
      mul_le_mul_of_nonneg_right hle hsqrt
    _ = c * L1 D * Real.sqrt (D : ℝ) := by ring
    _ ≤ hurwitz D := hformula D hD

/-- The global form with the canonical class-number constant. -/
theorem hurwitzSiegelLower_of_formulaGlobal
    {hurwitz L1 : ℤ → ℝ} {l : ℝ}
    (hl : 0 < l)
    (hformula : ∀ D : ℤ, 0 < D →
      classNumberFormulaConstant * L1 D * Real.sqrt (D : ℝ) ≤ hurwitz D)
    (hL : ∀ D : ℤ, 0 < D → l ≤ L1 D) :
    HurwitzSiegelLower hurwitz (classNumberFormulaConstant * l) :=
  hurwitzSiegelLower_of_formula_and_LOneGlobal
    classNumberFormulaConstant_nonneg hl hformula hL

/-- The global Siegel bound restricts to the honest Frobenius support. -/
theorem hurwitzSiegelLowerFrob_of_global {hurwitz : ℤ → ℝ} {c : ℝ}
    (h : HurwitzSiegelLower hurwitz c) : HurwitzSiegelLowerFrob hurwitz c :=
  fun D hD => h D (isFrobeniusDiscriminant_pos hD)

/-- The global statement is exactly its honest support part together with the
off-discriminant part.  This records that L27 only uses the left conjunct. -/
theorem hurwitzSiegelLower_iff_frob_and_off {hurwitz : ℤ → ℝ} {c : ℝ} :
    HurwitzSiegelLower hurwitz c ↔
      HurwitzSiegelLowerFrob hurwitz c ∧
        ∀ D : ℤ, 0 < D → ¬ IsFrobeniusDiscriminant D →
          c * Real.sqrt (D : ℝ) ≤ hurwitz D := by
  classical
  constructor
  · intro h
    refine ⟨hurwitzSiegelLowerFrob_of_global h, ?_⟩
    intro D hD _
    exact h D hD
  · rintro ⟨hfrob, hoff⟩ D hD
    by_cases hdisc : IsFrobeniusDiscriminant D
    · exact hfrob D hdisc
    · exact hoff D hD hdisc

/-! ## 3. The normalized and global forms -/

/-- The support form is equivalent to the normalized ratio form. -/
theorem hurwitzSiegelLowerFrob_iff_ratioLower {hurwitz : ℤ → ℝ} {c : ℝ} :
    HurwitzSiegelLowerFrob hurwitz c ↔ HurwitzSiegelRatioLower hurwitz c := by
  constructor
  · intro h D hD
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast isFrobeniusDiscriminant_pos hD
    have hsqrt : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hDpos
    exact (le_div_iff₀ hsqrt).mpr (h D hD)
  · intro h D hD
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast isFrobeniusDiscriminant_pos hD
    have hsqrt : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hDpos
    exact (le_div_iff₀ hsqrt).mp (h D hD)

/-- **The global normalized form.**  `c ≤ H(-D)/√D` for every positive `D`.
This is the global `HurwitzSiegelLower` after dividing by `√D`. -/
def HurwitzSiegelRatioLowerGlobal (hurwitz : ℤ → ℝ) (c : ℝ) : Prop :=
  ∀ D : ℤ, 0 < D → c ≤ hurwitz D / Real.sqrt (D : ℝ)

/-- The global Siegel bound is equivalent to its global normalized form. -/
theorem hurwitzSiegelLower_iff_ratioLowerGlobal {hurwitz : ℤ → ℝ} {c : ℝ} :
    HurwitzSiegelLower hurwitz c ↔ HurwitzSiegelRatioLowerGlobal hurwitz c := by
  constructor
  · intro h D hD
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hsqrt : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hDpos
    exact (le_div_iff₀ hsqrt).mpr (h D hD)
  · intro h D hD
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hsqrt : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hDpos
    exact (le_div_iff₀ hsqrt).mp (h D hD)

/-- **The smallest explicit Siegel input.**  A positive constant together with
the normalized lower bound on the honest Frobenius support. -/
structure SiegelHurwitzInput (hurwitz : ℤ → ℝ) (c : ℝ) : Prop where
  /-- The Siegel constant is positive. -/
  c_pos : 0 < c
  /-- The normalized Hurwitz lower bound. -/
  ratio_lower : HurwitzSiegelRatioLower hurwitz c

/-- The smallest input gives the support form of the Siegel leaf. -/
theorem SiegelHurwitzInput.toSiegelLower {hurwitz : ℤ → ℝ} {c : ℝ}
    (S : SiegelHurwitzInput hurwitz c) : HurwitzSiegelLowerFrob hurwitz c :=
  (hurwitzSiegelLowerFrob_iff_ratioLower).mpr S.ratio_lower

/-- The support form gives the smallest input once the constant is positive. -/
theorem siegelHurwitzInput_of_siegelLower {hurwitz : ℤ → ℝ} {c : ℝ}
    (hc : 0 < c) (h : HurwitzSiegelLowerFrob hurwitz c) :
    SiegelHurwitzInput hurwitz c where
  c_pos := hc
  ratio_lower := (hurwitzSiegelLowerFrob_iff_ratioLower).mp h

/-- The smallest input is exactly the support form of the Siegel leaf. -/
theorem siegelHurwitzInput_iff_siegelLower {hurwitz : ℤ → ℝ} {c : ℝ}
    (hc : 0 < c) :
    SiegelHurwitzInput hurwitz c ↔ HurwitzSiegelLowerFrob hurwitz c :=
  ⟨SiegelHurwitzInput.toSiegelLower, siegelHurwitzInput_of_siegelLower hc⟩

/-- **The smallest explicit input at the L27 scale.**  There is a positive
constant `c` compatible with `κ` and `θ` for which the normalized Hurwitz lower
bound holds on Frobenius discriminants.  This is the bare statement that the
downstream `HurwitzClassLower` needs. -/
def HasSiegelHurwitzAtScale (hurwitz : ℤ → ℝ) (κ θ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ κ ≤ c * Real.sqrt θ ∧
    HurwitzSiegelLowerFrob hurwitz c

/-- The scale-level input gives `HurwitzClassLower` directly. -/
theorem hurwitzClassLower_of_hasSiegelAtScale
    {p : ℕ → ℕ} {smooth : ℕ → ℕ → Bool} {hurwitz : ℤ → ℝ} {κ θ : ℝ}
    (hp : ∀ n, 0 < p n) (hθ : 0 < θ)
    (h : HasSiegelHurwitzAtScale hurwitz κ θ)
    (hscale : HurwitzDiscriminantScale p smooth θ) :
    HurwitzClassLower p smooth hurwitz κ := by
  obtain ⟨c, hc, hκ, hsiegel⟩ := h
  exact hurwitzClassLower_of_siegel_trace_scale hp hθ hc.le hκ
    (hurwitzSiegelLowerTrace_of_frob hp hsiegel) hscale

/-- The formula and `L`-value inputs imply the scale-level input. -/
theorem hasSiegelHurwitzAtScale_of_formula_and_LOne
    {hurwitz L1 : ℤ → ℝ} {c l κ θ : ℝ}
    (hc : 0 < c) (hl : 0 < l)
    (hκ : κ ≤ (c * l) * Real.sqrt θ)
    (hformula : HurwitzClassNumberFormulaLower hurwitz L1 c)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D) :
    HasSiegelHurwitzAtScale hurwitz κ θ :=
  ⟨c * l, mul_pos hc hl, hκ,
    hurwitzSiegelLowerFrob_of_formula_and_LOne hc.le hl hformula hL⟩

/-- The canonical formula and `L`-value inputs imply the scale-level input. -/
theorem hasSiegelHurwitzAtScale_of_formula
    {hurwitz L1 : ℤ → ℝ} {l κ θ : ℝ}
    (hl : 0 < l)
    (hκ : κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ)
    (hformula : HurwitzClassNumberFormula hurwitz L1)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D) :
    HasSiegelHurwitzAtScale hurwitz κ θ :=
  ⟨classNumberFormulaConstant * l,
    mul_pos classNumberFormulaConstant_pos hl, hκ,
    hurwitzSiegelLowerFrob_of_formula hl hformula hL⟩

/-! ## 4. The logarithmic Brauer–Siegel form -/

/-- The formula plus a logarithmic `L`-lower bound gives the classical
Brauer–Siegel shape with a log loss. -/
theorem brauerSiegelLower_of_formula_and_LOneLog
    {hurwitz L1 : ℤ → ℝ} {c l : ℝ}
    (hc : 0 ≤ c) (hl : 0 < l)
    (hformula : HurwitzClassNumberFormulaLower hurwitz L1 c)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D →
      l / Real.log ((D : ℝ) + 2) ≤ L1 D) :
    BrauerSiegelLower hurwitz (c * l) := by
  intro D hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast isFrobeniusDiscriminant_pos hD
  have hlog : 0 < Real.log ((D : ℝ) + 2) :=
    Real.log_pos (by linarith)
  have hsqrt : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hstep : c * (l / Real.log ((D : ℝ) + 2)) ≤ c * L1 D :=
    mul_le_mul_of_nonneg_left (hL D hD) hc
  calc
    (c * l) * Real.sqrt (D : ℝ) / Real.log ((D : ℝ) + 2) =
        c * (l / Real.log ((D : ℝ) + 2)) * Real.sqrt (D : ℝ) := by
      field_simp [ne_of_gt hlog]
    _ ≤ c * L1 D * Real.sqrt (D : ℝ) := by
      exact mul_le_mul_of_nonneg_right hstep hsqrt
    _ ≤ hurwitz D := hformula D hD

/-- The global Brauer–Siegel bound restricts to a bounded range. -/
theorem brauerSiegelLowerOn_of_brauerSiegelLower {hurwitz : ℤ → ℝ}
    {c X : ℝ} (h : BrauerSiegelLower hurwitz c) :
    BrauerSiegelLowerOn hurwitz c X :=
  fun D hD _ => h D hD

/-- **What the logarithmic Brauer–Siegel bound gives on a bounded range.**
On `D ≤ X` the log loss is at most `log(X+2)`, so one obtains the constant
`c/log(X+2)` there.  This is the exact bounded-range consequence; no
unbounded constant-`c` statement is asserted. -/
theorem brauerSiegelLowerOn_bounded {hurwitz : ℤ → ℝ} {c X : ℝ}
    (hc : 0 ≤ c) (hX : 0 < X)
    (h : BrauerSiegelLowerOn hurwitz c X) :
    ∀ D : ℤ, IsFrobeniusDiscriminant D → (D : ℝ) ≤ X →
      (c / Real.log (X + 2)) * Real.sqrt (D : ℝ) ≤ hurwitz D := by
  intro D hD hDX
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast isFrobeniusDiscriminant_pos hD
  have hlogD : 0 < Real.log ((D : ℝ) + 2) :=
    Real.log_pos (by linarith)
  have hlogX : 0 < Real.log (X + 2) :=
    Real.log_pos (by linarith)
  have hlog_le : Real.log ((D : ℝ) + 2) ≤ Real.log (X + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hinv : 1 / Real.log (X + 2) ≤ 1 / Real.log ((D : ℝ) + 2) :=
    one_div_le_one_div_of_le hlogD hlog_le
  have hsqrt : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  calc
    (c / Real.log (X + 2)) * Real.sqrt (D : ℝ) =
        (c * Real.sqrt (D : ℝ)) * (1 / Real.log (X + 2)) := by ring
    _ ≤ (c * Real.sqrt (D : ℝ)) * (1 / Real.log ((D : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hinv (mul_nonneg hc hsqrt)
    _ = c * Real.sqrt (D : ℝ) / Real.log ((D : ℝ) + 2) := by ring
    _ ≤ hurwitz D := h D hD hDX

/-- The bounded-range form of the global Brauer–Siegel bound. -/
theorem brauerSiegelLower_bounded_of_global {hurwitz : ℤ → ℝ} {c X : ℝ}
    (hc : 0 ≤ c) (hX : 0 < X) (h : BrauerSiegelLower hurwitz c) :
    ∀ D : ℤ, IsFrobeniusDiscriminant D → (D : ℝ) ≤ X →
      (c / Real.log (X + 2)) * Real.sqrt (D : ℝ) ≤ hurwitz D :=
  brauerSiegelLowerOn_bounded hc hX
    (brauerSiegelLowerOn_of_brauerSiegelLower h)

/-! ## 5. The bundle with the Siegel leaf removed -/

/-- **The L27 Hurwitz/Deuring inputs without the Siegel leaf.**

Compared with `L27TraceClassInputs`, the field `siegel_lower` is gone.  It is
replaced by the two arithmetic inputs

* `formula_lower : H(-D) ≥ (1/(2π)) L(1, χ_D) √D` on Frobenius discriminants;
* `l_one_lower : l ≤ L(1, χ_D)` with `l > 0` on the same support.

The nondegeneracy fraction `θ`, the one-sided Deuring count on the order model,
the `j`-line stratification, and the small-prime prepass are unchanged.  No
field sets a class number, curve count, or probability to zero. -/
structure L27SiegelInputs (I : L27_1Inputs) where
  /-- The Hurwitz class number `H(-D)`. -/
  hurwitz : ℤ → ℝ
  /-- The quadratic `L`-value `L(1, χ_D)`. -/
  L1 : ℤ → ℝ
  /-- The uniform lower bound for `L(1, χ_D)`. -/
  l : ℝ
  /-- Nondegeneracy fraction `D(p,j) ≥ θp` on smooth orders. -/
  θ : ℝ
  /-- The `L`-lower bound is positive. -/
  l_pos : 0 < l
  /-- The nondegeneracy fraction is positive. -/
  θ_pos : 0 < θ
  /-- The Hasse-scale constant is below the Siegel constant `(1/(2π))l`. -/
  kappa_le : I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ
  /-- The lower half of the order class-number formula. -/
  formula_lower : HurwitzClassNumberFormula hurwitz L1
  /-- A uniform positive lower bound for the quadratic `L`-value. -/
  l_one_lower : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D
  /-- Smooth Frobenius discriminants retain a `θ`-fraction of the Hasse width. -/
  disc_scale : HurwitzDiscriminantScale I.p I.smooth θ
  /-- The one-sided Deuring/Waterhouse count on the order model. -/
  trace_count_lower : DeuringTraceCountLower I.p I.orderCount hurwitz
  /-- The `j`-line stratification of the curves. -/
  j_invariant_strata : JInvariantStratification I.p I.orderCount I.orderTop
  /-- The target prime exceeds the two removed small primes. -/
  p_ge_four : ∀ n, 4 ≤ I.p n

namespace L27SiegelInputs

variable {I : L27_1Inputs}

/-- The support form of the Siegel leaf derived from the two arithmetic inputs. -/
theorem siegelLower (D : L27SiegelInputs I) :
    HurwitzSiegelLowerFrob D.hurwitz (classNumberFormulaConstant * D.l) :=
  hurwitzSiegelLowerFrob_of_formula D.l_pos D.formula_lower D.l_one_lower

/-- The trace form of the Siegel leaf consumed by `L27TraceClassInputs`. -/
theorem siegelLowerTrace (D : L27SiegelInputs I) :
    HurwitzSiegelLowerTrace I.p D.hurwitz (classNumberFormulaConstant * D.l) :=
  hurwitzSiegelLowerTrace_of_frob (fun n => I.p_pos n) D.siegelLower

/-- The Siegel constant is positive. -/
theorem siegelConstant_pos (D : L27SiegelInputs I) :
    0 < classNumberFormulaConstant * D.l :=
  mul_pos classNumberFormulaConstant_pos D.l_pos

/-- Reassemble the trace-class bundle, with the Siegel field derived rather
than assumed. -/
def toTraceClassInputs (D : L27SiegelInputs I) : L27TraceClassInputs I where
  hurwitz := D.hurwitz
  c := classNumberFormulaConstant * D.l
  θ := D.θ
  c_pos := D.siegelConstant_pos
  θ_pos := D.θ_pos
  kappa_le := D.kappa_le
  siegel_lower := D.siegelLowerTrace
  disc_scale := D.disc_scale
  trace_count_lower := D.trace_count_lower
  j_invariant_strata := D.j_invariant_strata
  p_ge_four := D.p_ge_four

/-- Reassemble `L27HurwitzInputs`. -/
def toHurwitzInputs (D : L27SiegelInputs I) : L27HurwitzInputs I :=
  D.toTraceClassInputs.toHurwitzInputs

/-- Reassemble `L27DeuringInputs`. -/
def toDeuringInputs (D : L27SiegelInputs I) : L27DeuringInputs I :=
  D.toTraceClassInputs.toDeuringInputs

/-- The Hurwitz class-number lower bound from the two arithmetic inputs. -/
theorem hurwitzClassLower (D : L27SiegelInputs I) :
    HurwitzClassLower I.p I.smooth D.hurwitz I.κ :=
  D.toTraceClassInputs.hurwitzClassLower

/-- The one-sided Deuring trace formula. -/
theorem deuringTraceFormula (D : L27SiegelInputs I) :
    DeuringTraceFormula I.p I.smooth I.orderCount D.hurwitz :=
  D.toTraceClassInputs.deuringTraceFormula

/-- The per-order Deuring/Lenstra bound. -/
theorem deuringSmoothOrderCount (D : L27SiegelInputs I) :
    DeuringSmoothOrderCount I.p I.smooth I.orderCount I.κ :=
  D.toTraceClassInputs.deuringSmoothOrderCount

/-- The sharp `2p + 8` total. -/
theorem jInvariantCurveTotal (D : L27SiegelInputs I) :
    JInvariantCurveTotal I.p I.orderCount I.orderTop :=
  D.toTraceClassInputs.jInvariantCurveTotal

/-- The paper's `≤ 4p` total. -/
theorem hasseWindowCurveTotal (D : L27SiegelInputs I) :
    HasseWindowCurveTotal I.p I.orderCount I.orderTop :=
  D.toTraceClassInputs.hasseWindowCurveTotal

/-- The bundled `DeuringLenstraCounts` hypothesis of `L27_1Sub`. -/
theorem deuringLenstraCounts (D : L27SiegelInputs I) :
    DeuringLenstraCounts I :=
  D.toTraceClassInputs.deuringLenstraCounts

/-- Reassemble `L27PaperInputs` from the two arithmetic inputs and the five
remaining LP §7 inputs. -/
theorem toPaperInputs (D : L27SiegelInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success) :
    L27PaperInputs I :=
  D.toTraceClassInputs.toPaperInputs hhasse h0 h1 h2 hstage

/-- The L27.1 ledger from the two arithmetic inputs. -/
theorem reduced_ledger (D : L27SiegelInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  D.toTraceClassInputs.reduced_ledger hhasse h0 h1 h2 hstage hbudget hlog

/-- The manuscript-rate deficit bound from the two arithmetic inputs. -/
theorem reduced_paper (D : L27SiegelInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n)) :=
  D.toTraceClassInputs.reduced_paper hhasse h0 h1 h2 hstage hbudget hlog

/-- The L27.1 `RatedLeaf` from the two arithmetic inputs. -/
def toRatedLeaf (D : L27SiegelInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) : RatedLeaf :=
  D.toTraceClassInputs.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog

/-- The `C5` slot `exp (-2H)` for the assembled leaf. -/
theorem slot (D : L27SiegelInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    ∀ᶠ n : ℕ in atTop,
      (D.toRatedLeaf hhasse h0 h1 h2 hstage hbudget hlog).loss n ≤
        Real.exp (-(2 : ℝ) * scale n) :=
  D.toTraceClassInputs.slot hhasse h0 h1 h2 hstage hbudget hlog

end L27SiegelInputs

/-- **Direct construction from the two arithmetic inputs.** -/
def toSiegelInputs {I : L27_1Inputs}
    (hurwitz L1 : ℤ → ℝ) {l θ : ℝ}
    (l_pos : 0 < l) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ)
    (formula_lower : HurwitzClassNumberFormula hurwitz L1)
    (l_one_lower : ∀ D : ℤ, IsFrobeniusDiscriminant D → l ≤ L1 D)
    (scale : HurwitzDiscriminantScale I.p I.smooth θ)
    (trace : DeuringTraceCountLower I.p I.orderCount hurwitz)
    (strata : JInvariantStratification I.p I.orderCount I.orderTop)
    (hp4 : ∀ n, 4 ≤ I.p n) : L27SiegelInputs I where
  hurwitz := hurwitz
  L1 := L1
  l := l
  θ := θ
  l_pos := l_pos
  θ_pos := θ_pos
  kappa_le := kappa_le
  formula_lower := formula_lower
  l_one_lower := l_one_lower
  disc_scale := scale
  trace_count_lower := trace
  j_invariant_strata := strata
  p_ge_four := hp4

/-! ## 6. Capstone reduction -/

/-- **The full reduction from the two arithmetic inputs.**  The class-number
formula's lower half, the constant `L`-value bound, the discriminant scale, the
one-sided Deuring count, the `j`-line stratification, Hasse, the three gcd-exit
facts, stage-one success, the curve budget, and the `log₂` multiplier imply
both bundled `L27_1Sub` hypotheses and both deficit conclusions. -/
theorem reduction_of_siegel {I : L27_1Inputs} (D : L27SiegelInputs I)
    (hhasse : HasseBound I.p I.orderCount)
    (h0 : GCDExitNonneg I.gcdFail)
    (h1 : GCDExitLeInv I.p I.gcdFail)
    (h2 : GCDExitLeFailure I.gcdFail (fun n => 1 - I.success n))
    (hstage : StageOneSuccess
      (smoothFraction I.smooth I.orderCount I.orderTop) I.y I.success)
    (hbudget : CurveBudget I.p I.y I.psi I.curves I.κ I.η)
    (hlog : LogFactorSubexp I.cofactor) :
    DeuringLenstraCounts I ∧ EllipticCurveGroupLaw I ∧
      (∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.loss n ≤ Real.exp (-((I.cRate / 2) * I.rate n))) :=
  reduction_of_traceClass D.toTraceClassInputs hhasse h0 h1 h2 hstage hbudget hlog

/-- The Deuring half of the capstone from the two arithmetic inputs. -/
theorem deuringLenstraCounts_of_siegel {I : L27_1Inputs}
    (D : L27SiegelInputs I) : DeuringLenstraCounts I :=
  D.deuringLenstraCounts

/-- **No-loss check.**  The derived Siegel leaf is exactly the field consumed
by `L27TraceClassInputs`; the two arithmetic inputs have not changed the
support or the constant. -/
theorem L27SiegelInputs.siegelLowerTrace_eq
    {I : L27_1Inputs} (D : L27SiegelInputs I) :
    D.toTraceClassInputs.siegel_lower = D.siegelLowerTrace :=
  rfl

/-! ## Axiom audit -/

#print axioms classNumberFormulaConstant_pos
#print axioms classNumberFormulaConstant_nonneg
#print axioms isFrobeniusDiscriminant_pos
#print axioms hurwitzSiegelLowerFrob_of_formula_and_LOne
#print axioms hurwitzSiegelLowerFrob_of_formula
#print axioms hurwitzSiegelLowerTrace_of_formula_and_LOne
#print axioms hurwitzSiegelLowerTrace_of_formula
#print axioms hurwitzSiegelLowerTrace_of_frob
#print axioms hurwitzSiegelLower_of_formula_and_LOneGlobal
#print axioms hurwitzSiegelLower_of_formulaGlobal
#print axioms hurwitzSiegelLowerFrob_of_global
#print axioms hurwitzSiegelLower_iff_frob_and_off
#print axioms hurwitzSiegelLowerFrob_iff_ratioLower
#print axioms hurwitzSiegelLower_iff_ratioLowerGlobal
#print axioms SiegelHurwitzInput.toSiegelLower
#print axioms siegelHurwitzInput_of_siegelLower
#print axioms siegelHurwitzInput_iff_siegelLower
#print axioms hurwitzClassLower_of_hasSiegelAtScale
#print axioms hasSiegelHurwitzAtScale_of_formula_and_LOne
#print axioms hasSiegelHurwitzAtScale_of_formula
#print axioms brauerSiegelLower_of_formula_and_LOneLog
#print axioms brauerSiegelLowerOn_of_brauerSiegelLower
#print axioms brauerSiegelLowerOn_bounded
#print axioms brauerSiegelLower_bounded_of_global
#print axioms L27SiegelInputs.siegelLower
#print axioms L27SiegelInputs.siegelLowerTrace
#print axioms L27SiegelInputs.siegelConstant_pos
#print axioms L27SiegelInputs.toTraceClassInputs
#print axioms L27SiegelInputs.toHurwitzInputs
#print axioms L27SiegelInputs.toDeuringInputs
#print axioms L27SiegelInputs.hurwitzClassLower
#print axioms L27SiegelInputs.deuringTraceFormula
#print axioms L27SiegelInputs.deuringSmoothOrderCount
#print axioms L27SiegelInputs.jInvariantCurveTotal
#print axioms L27SiegelInputs.hasseWindowCurveTotal
#print axioms L27SiegelInputs.deuringLenstraCounts
#print axioms L27SiegelInputs.toPaperInputs
#print axioms L27SiegelInputs.reduced_ledger
#print axioms L27SiegelInputs.reduced_paper
#print axioms L27SiegelInputs.toRatedLeaf
#print axioms L27SiegelInputs.slot
#print axioms toSiegelInputs
#print axioms reduction_of_siegel
#print axioms deuringLenstraCounts_of_siegel
#print axioms L27SiegelInputs.siegelLowerTrace_eq

end

end Cogentic.RandomizedL27Siegel
