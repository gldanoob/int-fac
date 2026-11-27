import Cogentic.RandomizedL34HalfPlane

/-!
# L34: the explicit strip input below the half-plane

`Cogentic.RandomizedL34HalfPlane` reduced the paper's zero-free input
`DedekindZeroFreeAboveBeta` to the residual strip statement
`DedekindZeroFreeAboveBetaBelowOne`:

`β₀ < Re ρ → Re ρ < 1 → Re ρ ≤ 1 - cz / log |Δ_E|`.

This file performs the last lossless rewrite of that residual statement and
isolates the exact analytic inequality that is missing for `ζ_E`.

## What is reduced

1. **Division-free form.**  On the open strip the denominator
   `log |Δ_E|` is positive, so the inequality is equivalent to

   `cz ≤ (1 - Re ρ) * log |Δ_E|`.

   This is `DedekindZeroFreeStripDistance`, and
   `dedekindZeroFreeAboveBetaBelowOne_iff_stripDistance` proves the exact
   equivalence.  The form has no division and no separate positivity
   conjunct; only the two strip inequalities `β₀ < Re ρ` and `Re ρ < 1` are
   carried.

2. **Zero-sequence form.**  The real-part sequence of a `ZetaZeroSequence` is
   definitionally the real part of its zero sequence.  Replacing
   `Z.realPart n` by `(Z.zero n).re` removes the last piece of bookkeeping and
   gives `DedekindZeroFreeStripZeros`, equivalent to the division-free form by
   `dedekindZeroFreeStripZeros_iff_stripDistance`.

3. **Half-plane plus strip.**  The half-plane result at `1` supplies
   `Re ρ < 1` for every genuine zero.  Consequently a strip input alone gives
   the paper's `DedekindZeroFreeAboveBeta`
   (`dedekindZeroFreeAboveBeta_of_stripZeros_of_halfPlane`).  Instances are
   provided for Riemann `ζ`, for nontrivial Dirichlet `L`-functions, for the
   unique character modulo `1`, and for the Dedekind zeta function under its
   missing half-plane hypothesis.

4. **The smallest division-free input.**  Under the half-plane, the residual
   strip statement is *exactly* `DedekindZeroFreeDistance` from
   `Cogentic.RandomizedL34ZeroFree`, the existing division-free input with no
   `Re ρ < 1` conjunct
   (`dedekindZeroFreeAboveBetaBelowOne_iff_distance_of_halfPlane`).  Thus the
   half-plane lets the strip condition be dropped rather than assumed twice.

## What is not formalized

Mathlib proves only the closed half-plane statements at `Re s = 1`:

* `riemannZeta_ne_zero_of_one_le_re`;
* `DirichletCharacter.LFunction_ne_zero_of_one_le_re`.

Neither has an effective `1 - c / log` region, and Mathlib contains no
half-plane or strip statement for `NumberField.dedekindZeta`.  The repository
does not contain a formal classical zero-free region for Riemann or Dirichlet
zeta either, so there is nothing stronger to invoke than the half-plane.

Accordingly the exact missing Dedekind statement is *defined*, never asserted:
`DedekindZetaStripInput` (sequence-indexed, matching the paper's family) and
`DedekindZetaStripInequality` (the scalar form for one field).  Together with
the missing half-plane `DedekindZetaHalfPlane` they imply the paper's input
(`dedekindZeroFreeAboveBeta_of_zetaStripInput_of_halfPlane`); no zero-free
region is claimed.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL34BelowOne

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane

noncomputable section

/-! ## 1. The division-free strip input -/

/-- **The strip input, division-free.**  On the open strip
`β₀ < Re ρ < 1`, the zero-free inequality
`Re ρ ≤ 1 - cz / log |Δ_E|` is equivalently
`cz ≤ (1 - Re ρ) * log |Δ_E|`.

This form carries no division and no positivity conjunct: the two strip
inequalities are the only hypotheses.  It is the smallest explicit strip
statement equivalent to `DedekindZeroFreeAboveBetaBelowOne` once
`log |Δ_E| > 0` is known. -/
def DedekindZeroFreeStripDistance (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n < zeroRealPart n → zeroRealPart n < 1 →
    cz ≤ (1 - zeroRealPart n) * discLog n

/-- **The division-free strip form is exactly the paper's residual strip
statement.**  The only side condition is positivity of `log |Δ_E|`; no
positivity of `cz` is needed, and no zero-free content is added or removed. -/
theorem dedekindZeroFreeAboveBetaBelowOne_iff_stripDistance
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeAboveBetaBelowOne beta0 zeroRealPart cz discLog ↔
      DedekindZeroFreeStripDistance beta0 zeroRealPart cz discLog := by
  constructor
  · intro h n hb hlt
    have hdiv : cz / discLog n ≤ 1 - zeroRealPart n := by
      have := h n hb hlt
      linarith
    exact (div_le_iff₀ (hd n)).mp hdiv
  · intro h n hb hlt
    have hineq : cz ≤ (1 - zeroRealPart n) * discLog n := h n hb hlt
    have hdiv : cz / discLog n ≤ 1 - zeroRealPart n :=
      (div_le_iff₀ (hd n)).mpr hineq
    linarith

/-- The division-free strip input gives the paper's residual strip statement. -/
theorem dedekindZeroFreeAboveBetaBelowOne_of_stripDistance
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeStripDistance beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeAboveBetaBelowOne beta0 zeroRealPart cz discLog :=
  (dedekindZeroFreeAboveBetaBelowOne_iff_stripDistance hd).mpr h

/-- The paper's residual strip statement gives the division-free strip input. -/
theorem dedekindZeroFreeStripDistance_of_aboveBetaBelowOne
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeAboveBetaBelowOne beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeStripDistance beta0 zeroRealPart cz discLog :=
  (dedekindZeroFreeAboveBetaBelowOne_iff_stripDistance hd).mp h

/-! ## 2. The strip input on a zero sequence -/

/-- **The strip input on the actual complex zeros.**  The real-part sequence of
`ZetaZeroSequence` is only a projection; writing the inequality directly on
`Z.zero n` makes the statement about the zeros themselves and removes the
projection from the hypotheses. -/
def DedekindZeroFreeStripZeros {f : ℂ → ℂ} (Z : ZetaZeroSequence f)
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n < (Z.zero n).re → (Z.zero n).re < 1 →
    cz ≤ (1 - (Z.zero n).re) * discLog n

/-- The zero-sequence strip input is exactly the division-free form. -/
theorem dedekindZeroFreeStripZeros_iff_stripDistance
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} :
    DedekindZeroFreeStripZeros Z beta0 cz discLog ↔
      DedekindZeroFreeStripDistance beta0 Z.realPart cz discLog := by
  constructor
  · intro h n hb hlt
    have hb' : beta0 n < (Z.zero n).re := by
      simpa only [Z.realPart_eq n] using hb
    have hlt' : (Z.zero n).re < 1 := by
      simpa only [Z.realPart_eq n] using hlt
    simpa only [Z.realPart_eq n] using h n hb' hlt'
  · intro h n hb hlt
    have hb' : beta0 n < Z.realPart n := by
      simpa only [Z.realPart_eq n] using hb
    have hlt' : Z.realPart n < 1 := by
      simpa only [Z.realPart_eq n] using hlt
    have hres : cz ≤ (1 - Z.realPart n) * discLog n := h n hb' hlt'
    simpa only [Z.realPart_eq n] using hres

/-- **The zero-sequence strip input is exactly `DedekindZeroFreeAboveBetaBelowOne`.**
This is the final rewrite of the residual statement: only the zeros and the
strict strip conditions remain. -/
theorem dedekindZeroFreeAboveBetaBelowOne_iff_stripZeros
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog ↔
      DedekindZeroFreeStripZeros Z beta0 cz discLog :=
  (dedekindZeroFreeAboveBetaBelowOne_iff_stripDistance hd).trans
    (dedekindZeroFreeStripZeros_iff_stripDistance Z).symm

/-! ## 3. Half-plane plus the strip input -/

/-- **A half-plane at `1` and the explicit strip input give the paper's
zero-free region.**  The half-plane removes every zero with `Re ρ ≥ 1`, leaving
exactly the strip `β₀ < Re ρ < 1`, where the division-free input applies. -/
theorem dedekindZeroFreeAboveBeta_of_stripZeros_of_halfPlane
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeStripZeros Z beta0 cz discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_belowOne_of_halfPlane Z hf
    ((dedekindZeroFreeAboveBetaBelowOne_iff_stripZeros Z hd).mpr h)

/-- The division-free strip input plus a half-plane at `1`. -/
theorem dedekindZeroFreeAboveBeta_of_stripDistance_of_halfPlane
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeStripDistance beta0 Z.realPart cz discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_belowOne_of_halfPlane Z hf
    ((dedekindZeroFreeAboveBetaBelowOne_iff_stripDistance hd).mpr h)

/-- The strip input plus a half-plane at `1` gives the smallest zero-free
bundle `DedekindZeroFreeInput`. -/
theorem dedekindZeroFreeInput_of_stripZeros_of_halfPlane
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hcz : 0 < cz) (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeStripZeros Z beta0 cz discLog) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog where
  cz_pos := hcz
  above_beta :=
    dedekindZeroFreeAboveBeta_of_stripZeros_of_halfPlane Z hf hd h

/-- **Under the half-plane, the residual strip statement is equivalent to the
plain division-free distance input.**  `DedekindZeroFreeDistance` carries no
`Re ρ < 1` conjunct; the half-plane supplies it automatically for every genuine
zero.  This exhibits `DedekindZeroFreeAboveBetaBelowOne` as exactly the existing
smallest division-free zero-free input restricted by the half-plane. -/
theorem dedekindZeroFreeAboveBetaBelowOne_iff_distance_of_halfPlane
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog ↔
      DedekindZeroFreeDistance beta0 Z.realPart cz discLog :=
  (dedekindZeroFreeAboveBeta_iff_belowOne_of_halfPlane Z hf).symm.trans
    (dedekindZeroFreeAboveBeta_iff_distance hd)

/-- The Riemann-zeta instance. -/
theorem riemannZeta_dedekindZeroFreeAboveBeta_of_strip
    (Z : ZetaZeroSequence riemannZeta) {beta0 : ℕ → ℝ} {cz : ℝ}
    {discLog : ℕ → ℝ} (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeStripZeros Z beta0 cz discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_stripZeros_of_halfPlane Z
    riemannZeta_closedHalfPlane hd h

/-- The nontrivial-Dirichlet-character instance. -/
theorem dirichletL_dedekindZeroFreeAboveBeta_of_strip {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeStripZeros Z beta0 cz discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_stripZeros_of_halfPlane Z
    (dirichletL_closedHalfPlane hχ) hd h

/-- The character-modulo-`1` instance, where no trivial-character exception is
needed. -/
theorem dirichletL_modOne_dedekindZeroFreeAboveBeta_of_strip
    (χ : DirichletCharacter ℂ 1)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeStripZeros Z beta0 cz discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_stripZeros_of_halfPlane Z
    (dirichletL_modOne_closedHalfPlane χ) hd h

/-- The Dedekind-zeta instance, conditional on the half-plane hypothesis that
Mathlib does not prove. -/
theorem dedekindZeta_dedekindZeroFreeAboveBeta_of_strip
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZeroFreeStripZeros Z beta0 cz discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_stripZeros_of_halfPlane Z hK hd h

/-! ## 4. The exact missing Dedekind-zeta strip inequality -/

/-- **The exact missing strip inequality for `ζ_E`, in the paper's
sequence-indexed form.**  For every index `n` and every genuine zero `z` of
`NumberField.dedekindZeta K` with

`β₀ n < Re z < 1`,

the zero-free bound `Re z ≤ 1 - cz / log |Δ_E|` must hold.

This is the precise analytic statement that Mathlib and this repository do not
prove.  It is a `def`, not a theorem: no zero-free claim is made. -/
def DedekindZetaStripInput (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  ∀ n, ∀ z : ℂ, NumberField.dedekindZeta K z = 0 →
    beta0 n < z.re → z.re < 1 → z.re ≤ 1 - cz / discLog n

/-- **The exact missing strip inequality for one field**, with scalar `β₀`,
`cz` and `log |Δ_E|`.  This is the specialization of `DedekindZetaStripInput`
to a single number field. -/
def DedekindZetaStripInequality (K : Type*) [Field K] [NumberField K]
    (beta0 cz discLog : ℝ) : Prop :=
  ∀ z : ℂ, NumberField.dedekindZeta K z = 0 →
    beta0 < z.re → z.re < 1 → z.re ≤ 1 - cz / discLog

/-- The scalar exact strip inequality gives the sequence-indexed missing input
when the parameters are constant. -/
theorem dedekindZetaStripInput_of_inequality
    (K : Type*) [Field K] [NumberField K]
    {beta0 cz discLog : ℝ} {beta0Seq discLogSeq : ℕ → ℝ}
    (hβ : ∀ n, beta0Seq n = beta0) (hL : ∀ n, discLogSeq n = discLog)
    (h : DedekindZetaStripInequality K beta0 cz discLog) :
    DedekindZetaStripInput K beta0Seq cz discLogSeq := by
  intro n z hz hb hlt
  have hb' : beta0 < z.re := by
    simpa only [hβ n] using hb
  have hres : z.re ≤ 1 - cz / discLog := h z hz hb' hlt
  simpa only [hL n] using hres

/-- **The exact missing Dedekind strip input gives the paper's residual strip
statement** for any zero sequence.  No half-plane is used here: this is the
purely strip part of the reduction. -/
theorem dedekindZeroFreeAboveBetaBelowOne_of_zetaStripInput
    (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZetaStripInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog := by
  intro n hb hlt
  have hb' : beta0 n < (Z.zero n).re := by
    simpa only [Z.realPart_eq n] using hb
  have hlt' : (Z.zero n).re < 1 := by
    simpa only [Z.realPart_eq n] using hlt
  have hres : (Z.zero n).re ≤ 1 - cz / discLog n :=
    h n (Z.zero n) (Z.isZero n) hb' hlt'
  simpa only [Z.realPart_eq n] using hres

/-- **The two missing Dedekind inputs together give the paper's zero-free
region.**  `DedekindZetaHalfPlane` removes the closed half-plane `Re ρ ≥ 1` and
`DedekindZetaStripInput` is the exact remaining inequality on the open strip.
Both are hypotheses; neither is proved here. -/
theorem dedekindZeroFreeAboveBeta_of_zetaStripInput_of_halfPlane
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZetaStripInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_belowOne_of_halfPlane Z hK
    (dedekindZeroFreeAboveBetaBelowOne_of_zetaStripInput K h Z)

/-- The same assembly in the smallest zero-free bundle, with positivity of the
constant made explicit. -/
theorem dedekindZeroFreeInput_of_zetaStripInput_of_halfPlane
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} (hcz : 0 < cz)
    (h : DedekindZetaStripInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog where
  cz_pos := hcz
  above_beta :=
    dedekindZeroFreeAboveBeta_of_zetaStripInput_of_halfPlane K hK h Z

/-! ## Axiom audit -/

#print axioms dedekindZeroFreeAboveBetaBelowOne_iff_stripDistance
#print axioms dedekindZeroFreeAboveBetaBelowOne_of_stripDistance
#print axioms dedekindZeroFreeStripDistance_of_aboveBetaBelowOne
#print axioms dedekindZeroFreeStripZeros_iff_stripDistance
#print axioms dedekindZeroFreeAboveBetaBelowOne_iff_stripZeros
#print axioms dedekindZeroFreeAboveBeta_of_stripZeros_of_halfPlane
#print axioms dedekindZeroFreeAboveBeta_of_stripDistance_of_halfPlane
#print axioms dedekindZeroFreeInput_of_stripZeros_of_halfPlane
#print axioms dedekindZeroFreeAboveBetaBelowOne_iff_distance_of_halfPlane
#print axioms riemannZeta_dedekindZeroFreeAboveBeta_of_strip
#print axioms dirichletL_dedekindZeroFreeAboveBeta_of_strip
#print axioms dirichletL_modOne_dedekindZeroFreeAboveBeta_of_strip
#print axioms dedekindZeta_dedekindZeroFreeAboveBeta_of_strip
#print axioms dedekindZetaStripInput_of_inequality
#print axioms dedekindZeroFreeAboveBetaBelowOne_of_zetaStripInput
#print axioms dedekindZeroFreeAboveBeta_of_zetaStripInput_of_halfPlane
#print axioms dedekindZeroFreeInput_of_zetaStripInput_of_halfPlane

end

end Cogentic.RandomizedL34BelowOne
