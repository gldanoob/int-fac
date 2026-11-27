import Cogentic.RandomizedL34ZeroFree
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# L34: the strongest half-plane zero-free content available in Mathlib

`Cogentic.RandomizedL34ZeroFree` records the Riemann-zeta half-plane estimate
`riemannZeta_ne_zero_of_one_le_re` and the vacuous deduction
`dedekindZeroFreeAboveBeta_of_halfPlane_one` for `β₀ ≥ 1`.  This file completes
that picture with the Dirichlet `L`-function half-plane estimate and with the
exact residual region left for `β₀ < 1`.

The strongest zero-free statements that Mathlib actually proves are the closed
half-plane statements

* `riemannZeta_ne_zero_of_one_le_re` — `riemannZeta s ≠ 0` for `1 ≤ s.re`;
* `DirichletCharacter.LFunction_ne_zero_of_one_le_re` — for a Dirichlet
  character `χ`, `LFunction χ s ≠ 0` for `1 ≤ s.re`, except at the trivial
  character and `s = 1`.

Both include the boundary line `re s = 1`; neither is effective (there is no
`1 - c / log` region) and neither says anything about the open strip
`0 < re s < 1`.  In particular, Mathlib contains no half-plane statement for
`NumberField.dedekindZeta`.  That statement is therefore *isolated as a
hypothesis* in `DedekindZetaHalfPlane` below; it is not proved here.

The only consequence for the paper's `DedekindZeroFreeAboveBeta` that follows
from a half-plane at `1` is the vacuous one: when `β₀ ≥ 1`, no zero can lie
above `β₀`, so the implication holds for every constant `cz`.  For `β₀ < 1`,
the half-plane at `1` reduces `DedekindZeroFreeAboveBeta` to the *exact* strip
statement

`β₀ < Re ρ → Re ρ < 1 → Re ρ ≤ 1 - cz / log |Δ_E|`,

which is `DedekindZeroFreeAboveBetaBelowOne`.  This is the smallest explicit
remaining region input: it is vacuous for `β₀ ≥ 1`, and on the strip it is
literally the assertion that remains once the half-plane has removed all zeros
with `Re ρ ≥ 1`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no zero-free
region is asserted for `ζ_E`.
-/

namespace Cogentic.RandomizedL34HalfPlane

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree

noncomputable section

/-! ## 1. Riemann zeta and Dirichlet characters: the precise Mathlib content -/

/-- **Riemann zeta half-plane.**  Mathlib's `riemannZeta_ne_zero_of_one_le_re`,
re-exported as a `ZeroFreeHalfPlane` at `1`.  The closed half-plane includes the
line `re s = 1`. -/
theorem riemannZeta_closedHalfPlane : ZeroFreeHalfPlane riemannZeta 1 :=
  riemannZeta_zeroFreeHalfPlane

/-- **Nontrivial Dirichlet characters.**  For `χ ≠ 1`, Mathlib's
`LFunction_ne_zero_of_one_le_re` gives the full closed half-plane, including
`s = 1`. -/
theorem dirichletL_closedHalfPlane {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ZeroFreeHalfPlane (DirichletCharacter.LFunction χ) 1 :=
  fun _s hs => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

/-- **The unique character modulo `1`.**  Its `L`-function is `riemannZeta`, so
the Riemann half-plane applies without the trivial-character exception. -/
theorem dirichletL_modOne_closedHalfPlane (χ : DirichletCharacter ℂ 1) :
    ZeroFreeHalfPlane (DirichletCharacter.LFunction χ) 1 := by
  simpa using riemannZeta_zeroFreeHalfPlane

/-- **The literal zero-set statement for all Dirichlet characters.**  Any zero
in the closed half-plane `re s ≥ 1` must be the exceptional trivial-character
point `s = 1`.  This is exactly the content of
`LFunction_ne_zero_of_one_le_re`, with the disjunction
`χ ≠ 1 ∨ s ≠ 1` converted into a zero-set inclusion. -/
theorem dirichletL_zero_mem_trivial_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 ≤ s.re)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    χ = 1 ∧ s = 1 := by
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
    (not_and_or.mp h) hs hz

/-! ## 2. The Dedekind half-plane hypothesis that Mathlib does not supply -/

/-- **The Dedekind zeta half-plane, isolated as an assumption.**  This is the
exact analogue of the Riemann/Dirichlet half-plane results for
`NumberField.dedekindZeta K`.  No proof of this proposition exists in Mathlib
or elsewhere in this repository; it is used below only as a hypothesis, never
asserted. -/
def DedekindZetaHalfPlane (K : Type*) [Field K] [NumberField K] : Prop :=
  ZeroFreeHalfPlane (NumberField.dedekindZeta K) 1

/-! ## 3. The vacuous case `β₀ ≥ 1` -/

/-- **Any half-plane at `1` plus `β₀ ≥ 1` gives the paper's zero-free input.**
This is the general form of the only deduction supplied by Mathlib's
half-plane estimates: the region above `β₀` is empty, for every `cz` and every
`log |Δ_E|`. -/
theorem dedekindZeroFreeAboveBeta_of_halfPlane_of_one_le_beta0
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 ≤ beta0 n) (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_halfPlane_one Z hf hβ cz discLog

/-- The Riemann-zeta instance of `dedekindZeroFreeAboveBeta_of_halfPlane_of_one_le_beta0`. -/
theorem riemannZeta_dedekindZeroFreeAboveBeta
    (Z : ZetaZeroSequence riemannZeta) {beta0 : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_halfPlane_of_one_le_beta0 Z
    riemannZeta_closedHalfPlane hβ cz discLog

/-- The nontrivial-Dirichlet-character instance. -/
theorem dirichletL_dedekindZeroFreeAboveBeta {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 ≤ beta0 n) (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_halfPlane_of_one_le_beta0 Z
    (dirichletL_closedHalfPlane hχ) hβ cz discLog

/-- The character-modulo-`1` instance, where no trivial-character exception is
needed. -/
theorem dirichletL_modOne_dedekindZeroFreeAboveBeta
    (χ : DirichletCharacter ℂ 1)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 ≤ beta0 n) (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_halfPlane_of_one_le_beta0 Z
    (dirichletL_modOne_closedHalfPlane χ) hβ cz discLog

/-- The Dedekind-zeta instance, conditional on the half-plane hypothesis that
Mathlib does not prove. -/
theorem dedekindZeta_dedekindZeroFreeAboveBeta
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 ≤ beta0 n) (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_halfPlane_of_one_le_beta0 Z hK hβ cz discLog

/-! ## 4. The smallest remaining input for `β₀ < 1` -/

/-- **The exact residual zero-free region below the Mathlib half-plane.**  Once
the half-plane at `1` has removed every zero with `Re ρ ≥ 1`, the paper's
`DedekindZeroFreeAboveBeta` is equivalent to this statement, which quantifies
only over the open strip `β₀ < Re ρ < 1`.

For `β₀ ≥ 1` the strip is empty and the statement is vacuous; for `β₀ < 1` it
is the smallest explicit region input that remains. -/
def DedekindZeroFreeAboveBetaBelowOne (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n < zeroRealPart n → zeroRealPart n < 1 →
    zeroRealPart n ≤ 1 - cz / discLog n

/-- The paper's zero-free input restricts to the strip. -/
theorem dedekindZeroFreeAboveBetaBelowOne_of_aboveBeta
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeAboveBetaBelowOne beta0 zeroRealPart cz discLog :=
  fun n hb _ => h n hb

/-- **The strip input plus a half-plane at `1` gives the paper's zero-free
input.**  The half-plane supplies `Re ρ < 1` for every genuine zero, and the
strip hypothesis supplies the only remaining inequality. -/
theorem dedekindZeroFreeAboveBeta_of_belowOne_of_halfPlane
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog := by
  intro n hb
  by_cases hlt : Z.realPart n < 1
  · exact h n hb hlt
  · exfalso
    have h1 : 1 ≤ Z.realPart n := le_of_not_gt hlt
    rw [Z.realPart_eq n] at h1
    exact hf (Z.zero n) h1 (Z.isZero n)

/-- **The strip statement is exactly the residual content.**  Given any
half-plane at `1`, `DedekindZeroFreeAboveBeta` and
`DedekindZeroFreeAboveBetaBelowOne` are equivalent.  This is the lossless
statement of what is left for `β₀ < 1`. -/
theorem dedekindZeroFreeAboveBeta_iff_belowOne_of_halfPlane
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog ↔
      DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog :=
  ⟨dedekindZeroFreeAboveBetaBelowOne_of_aboveBeta,
    dedekindZeroFreeAboveBeta_of_belowOne_of_halfPlane Z hf⟩

/-- For `β₀ ≥ 1` the residual strip statement is vacuous. -/
theorem dedekindZeroFreeAboveBetaBelowOne_of_one_le_beta0
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    DedekindZeroFreeAboveBetaBelowOne beta0 zeroRealPart cz discLog := by
  intro n hb hlt
  linarith [hβ n, hb, hlt]

/-! ## 5. The residual input in the smallest zero-free bundle -/

/-- **Assembling the paper's smallest zero-free input.**  A half-plane at `1`,
positivity of `cz`, and the strip input give `DedekindZeroFreeInput`, the
zero-free component of `DedekindAnalyticInputs`. -/
theorem dedekindZeroFreeInput_of_halfPlane_of_belowOne
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} (hcz : 0 < cz)
    (h : DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog where
  cz_pos := hcz
  above_beta := dedekindZeroFreeAboveBeta_of_belowOne_of_halfPlane Z hf h

/-- The Riemann-zeta residual input. -/
theorem riemannZeta_zeroFreeInput_of_belowOne
    (Z : ZetaZeroSequence riemannZeta) {beta0 : ℕ → ℝ} {cz : ℝ}
    {discLog : ℕ → ℝ} (hcz : 0 < cz)
    (h : DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog :=
  dedekindZeroFreeInput_of_halfPlane_of_belowOne Z
    riemannZeta_closedHalfPlane hcz h

/-- The nontrivial-Dirichlet-character residual input. -/
theorem dirichletL_zeroFreeInput_of_belowOne {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} (hcz : 0 < cz)
    (h : DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog :=
  dedekindZeroFreeInput_of_halfPlane_of_belowOne Z
    (dirichletL_closedHalfPlane hχ) hcz h

/-- The character-modulo-`1` residual input. -/
theorem dirichletL_modOne_zeroFreeInput_of_belowOne
    (χ : DirichletCharacter ℂ 1)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} (hcz : 0 < cz)
    (h : DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog :=
  dedekindZeroFreeInput_of_halfPlane_of_belowOne Z
    (dirichletL_modOne_closedHalfPlane χ) hcz h

/-- The Dedekind-zeta residual input, conditional on the half-plane hypothesis
that Mathlib does not supply. -/
theorem dedekindZeta_zeroFreeInput_of_belowOne
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} (hcz : 0 < cz)
    (h : DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog :=
  dedekindZeroFreeInput_of_halfPlane_of_belowOne Z hK hcz h

/-! ## Axiom audit -/

#print axioms riemannZeta_closedHalfPlane
#print axioms dirichletL_closedHalfPlane
#print axioms dirichletL_modOne_closedHalfPlane
#print axioms dirichletL_zero_mem_trivial_one
#print axioms dedekindZeroFreeAboveBeta_of_halfPlane_of_one_le_beta0
#print axioms riemannZeta_dedekindZeroFreeAboveBeta
#print axioms dirichletL_dedekindZeroFreeAboveBeta
#print axioms dirichletL_modOne_dedekindZeroFreeAboveBeta
#print axioms dedekindZeta_dedekindZeroFreeAboveBeta
#print axioms dedekindZeroFreeAboveBetaBelowOne_of_aboveBeta
#print axioms dedekindZeroFreeAboveBeta_of_belowOne_of_halfPlane
#print axioms dedekindZeroFreeAboveBeta_iff_belowOne_of_halfPlane
#print axioms dedekindZeroFreeAboveBetaBelowOne_of_one_le_beta0
#print axioms dedekindZeroFreeInput_of_halfPlane_of_belowOne
#print axioms riemannZeta_zeroFreeInput_of_belowOne
#print axioms dirichletL_zeroFreeInput_of_belowOne
#print axioms dirichletL_modOne_zeroFreeInput_of_belowOne
#print axioms dedekindZeta_zeroFreeInput_of_belowOne

end

end Cogentic.RandomizedL34HalfPlane
