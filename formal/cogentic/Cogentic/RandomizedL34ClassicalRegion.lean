import Cogentic.RandomizedL34BelowOne

/-!
# L34: the classical de la Vallée Poussin region and its reduction

`Cogentic.RandomizedL34BelowOne` isolated the paper's residual strip input
`DedekindZetaStripInput` and the division-free distance form
`DedekindZeroFreeStripDistance`.  This file records the *classical analytic
region* that is supposed to supply such a strip, and proves the exact
reduction from it to the Dedekind strip and zero-free `Prop`s.

## The classical region

The classical de la Vallée Poussin zero-free region is height dependent:

`ζ(s) ≠ 0` for `Re s > 1 - c / log(|Im s| + 2)`,

with the analogous statement for Dirichlet `L`-functions, where the conductor
is inserted into the logarithm (in the no-exceptional-zero form).
`ClassicalZeroFreeRegion f c` is this
statement for a general `f : ℂ → ℂ`; `RiemannClassicalRegion c` and
`DirichletClassicalRegion χ c` are its Riemann-zeta and Dirichlet instances.

Mathlib proves only the closed half-plane at `Re s = 1`.  The file records
that boundary honestly:

* `classicalZeroFreeRegion_halfPlane` — any classical region with `c > 0`
  implies `ZeroFreeHalfPlane f 1`;
* `classicalZeroFreeRegion_of_halfPlane_of_nonpos` — conversely, for `c ≤ 0`
  the classical region is a consequence of Mathlib's half-plane.  Thus the
  only content Mathlib currently supplies is the degenerate `c ≤ 0` case.

Nothing here asserts that `ClassicalZeroFreeRegion riemannZeta c` holds for
any `c > 0`; it is a `def`, used only as a hypothesis.

## The height bridge

The paper's zero-free input is *uniform in height*: it uses the fixed
denominator `log |Δ_E|` rather than `log(|Im ρ| + 2)`.  The classical region
alone does not give this: at a zero `ρ` one gets

`Re ρ ≤ 1 - c / log(|Im ρ| + 2)`,

and to replace the denominator by `log |Δ_E|` one needs

`log(|Im ρ| + 2) ≤ log |Δ_E|`.

This is the explicit elementary input `ZeroHeightBoundAt Z discLog`
(equivalently `|Im ρ| + 2 ≤ |Δ_E|` when `discLog = log |Δ_E|`).  The file
does not hide it: the theorem `classicalZeroFreeRegion_uniformSequence` proves
that the classical region together with exactly this height bound yields the
paper's uniform strip `ZeroSequenceUniformRegion`.

## The reduction

The uniform strip is the *smallest* explicit region input: it has no
exceptional-zero slot and no separate half-plane conjunct.

* `ZeroSequenceUniformRegion.toAboveBeta` — it gives
  `DedekindZeroFreeAboveBeta` directly;
* `ZeroSequenceUniformRegion.toStripZeros` — it gives
  `DedekindZeroFreeStripZeros` and hence `DedekindZeroFreeStripDistance`;
* `ZeroSequenceUniformRegion.toZeroFreeInput` — it gives
  `DedekindZeroFreeInput`.

The packaged input `ClassicalRegionInput` bundles `c > 0`, the classical
region, and the height bound, and reduces to all of the above.  The Dedekind
zeta specializations `dedekindClassicalRegion_stripInequality`,
`dedekindClassicalRegion_stripInput`, `dedekindClassicalRegion_aboveBeta` and
`dedekindClassicalRegion_zeroFreeInput` land exactly on the `Prop`s of
`Cogentic.RandomizedL34BelowOne`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no zero-free
region is claimed.
-/

namespace Cogentic.RandomizedL34ClassicalRegion

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34BelowOne

noncomputable section

/-! ## 1. The height-dependent classical region -/

/-- **The classical de la Vallée Poussin zero-free region.**  The function `f`
has no zero with `Re s > 1 - c / log(|Im s| + 2)`.  This is the standard
height-dependent form of the classical theorem; `c` is its explicit constant.

The statement is a `def`, not a theorem: for `f = riemannZeta` or a Dirichlet
`L`-function no effective value of `c > 0` is proved in Mathlib or in this
repository. -/
def ClassicalZeroFreeRegion (f : ℂ → ℂ) (c : ℝ) : Prop :=
  ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) < s.re → f s ≠ 0

/-- **Existence form of the classical region.**  There is an effective
constant `c > 0` for which the classical region holds.  This is the shape in
which the classical theorem is usually quoted.  It is again a `def`. -/
def ClassicalZeroFreeRegionExists (f : ℂ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ClassicalZeroFreeRegion f c

/-- **A classical region with `c > 0` implies the closed half-plane.**  On
`Re s ≥ 1` the classical line `1 - c / log(|Im s| + 2)` is strictly below
`1`, so the classical region applies.  This shows that the classical input is
at least as strong as the half-plane estimates that Mathlib actually proves. -/
theorem classicalZeroFreeRegion_halfPlane {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (h : ClassicalZeroFreeRegion f c) : ZeroFreeHalfPlane f 1 := by
  intro s hs
  apply h s
  have hlog : 0 < Real.log (|s.im| + 2) := by
    apply Real.log_pos
    have := abs_nonneg s.im
    linarith
  have hpos : 0 < c / Real.log (|s.im| + 2) := div_pos hc hlog
  linarith

/-- The existence form `∃ c > 0` also gives the half-plane. -/
theorem ClassicalZeroFreeRegionExists.halfPlane {f : ℂ → ℂ}
    (h : ClassicalZeroFreeRegionExists f) : ZeroFreeHalfPlane f 1 := by
  rcases h with ⟨_c, hc, hreg⟩
  exact classicalZeroFreeRegion_halfPlane hc hreg

/-- In particular every zero in the sequence has real part below `1`. -/
theorem classicalZeroFreeRegion_re_lt_one {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (h : ClassicalZeroFreeRegion f c) : ∀ s : ℂ, f s = 0 → s.re < 1 := by
  intro s hz
  by_contra hnot
  exact (classicalZeroFreeRegion_halfPlane hc h s (le_of_not_gt hnot)) hz

/-- **Mathlib's half-plane is the degenerate `c = 0` classical region.**  When
`c = 0` the classical line is `1`, so the strict region is exactly the open
half-plane `Re s > 1`; this is contained in Mathlib's closed half-plane. -/
theorem classicalZeroFreeRegion_zero_of_halfPlane {f : ℂ → ℂ}
    (h : ZeroFreeHalfPlane f 1) : ClassicalZeroFreeRegion f 0 := by
  intro s hs
  apply h s
  have : (1 : ℝ) < s.re := by simpa using hs
  linarith

/-- **The only classical regions Mathlib supplies are those with `c ≤ 0`.**
For `c ≤ 0` the line `1 - c / log(|Im s| + 2)` is at least `1`, so the
classical region is weaker than the closed half-plane.  This is the precise
sense in which the positive-constant region is missing. -/
theorem classicalZeroFreeRegion_of_halfPlane_of_nonpos {f : ℂ → ℂ} {c : ℝ}
    (hc : c ≤ 0) (h : ZeroFreeHalfPlane f 1) :
    ClassicalZeroFreeRegion f c := by
  intro s hs
  apply h s
  have hlog : 0 < Real.log (|s.im| + 2) := by
    apply Real.log_pos
    have := abs_nonneg s.im
    linarith
  have hquot : c / Real.log (|s.im| + 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hc (le_of_lt hlog)
  linarith

/-- **Monotonicity in the classical constant.**  A region with constant
`c'` is stronger than one with `c ≤ c'`, because the line
`1 - c' / log` is to the left of `1 - c / log`.  This is how a literature
estimate with a larger explicit constant is consumed. -/
theorem classicalZeroFreeRegion_of_le {f : ℂ → ℂ} {c c' : ℝ} (hcc' : c ≤ c')
    (h : ClassicalZeroFreeRegion f c') : ClassicalZeroFreeRegion f c := by
  intro s hs
  apply h s
  have hlog : 0 < Real.log (|s.im| + 2) := by
    apply Real.log_pos
    have := abs_nonneg s.im
    linarith
  have hquot : c / Real.log (|s.im| + 2) ≤ c' / Real.log (|s.im| + 2) :=
    div_le_div_of_nonneg_right hcc' (le_of_lt hlog)
  linarith

/-- **The uniform strip input on a zero sequence.**  Every zero lies on the
zero-free side of the fixed line `1 - c / discLog n`.  There is no
exceptional-zero slot and no half-plane conjunct: this is the smallest
explicit region input used by the file. -/
def ZeroSequenceUniformRegion {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (c : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, Z.realPart n ≤ 1 - c / discLog n

namespace ZeroSequenceUniformRegion

/-- The uniform strip gives the paper's "above `β₀`" region directly; no
half-plane and no `Re ρ < 1` conjunct are needed. -/
theorem toAboveBeta {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {c : ℝ}
    {discLog : ℕ → ℝ} {beta0 : ℕ → ℝ}
    (h : ZeroSequenceUniformRegion Z c discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart c discLog :=
  fun n _ => h n

/-- The uniform strip gives the residual strip statement. -/
theorem toBelowOne {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {c : ℝ}
    {discLog : ℕ → ℝ} {beta0 : ℕ → ℝ}
    (h : ZeroSequenceUniformRegion Z c discLog) :
    DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart c discLog :=
  fun n _ _ => h n

/-- The uniform strip gives the division-free strip distance. -/
theorem toStripDistance {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {c : ℝ}
    {discLog : ℕ → ℝ} {beta0 : ℕ → ℝ}
    (h : ZeroSequenceUniformRegion Z c discLog)
    (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeStripDistance beta0 Z.realPart c discLog := by
  intro n _ hlt
  have hline : Z.realPart n ≤ 1 - c / discLog n := h n
  have hquot : c / discLog n ≤ 1 - Z.realPart n := by linarith
  exact (div_le_iff₀ (hd n)).mp hquot

/-- The uniform strip gives `DedekindZeroFreeStripZeros`. -/
theorem toStripZeros {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {c : ℝ}
    {discLog : ℕ → ℝ} {beta0 : ℕ → ℝ}
    (h : ZeroSequenceUniformRegion Z c discLog)
    (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeStripZeros Z beta0 c discLog :=
  (dedekindZeroFreeStripZeros_iff_stripDistance Z).mpr
    (ZeroSequenceUniformRegion.toStripDistance h hd)

/-- The uniform strip gives the smallest zero-free bundle. -/
theorem toZeroFreeInput {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {c : ℝ}
    {discLog : ℕ → ℝ} {beta0 : ℕ → ℝ}
    (h : ZeroSequenceUniformRegion Z c discLog) (hc : 0 < c) :
    DedekindZeroFreeInput beta0 Z.realPart c discLog where
  cz_pos := hc
  above_beta := ZeroSequenceUniformRegion.toAboveBeta h

end ZeroSequenceUniformRegion

/-! ## 2. Riemann-zeta and Dirichlet instances -/

/-- **The classical region for the Riemann zeta function.** -/
def RiemannClassicalRegion (c : ℝ) : Prop :=
  ClassicalZeroFreeRegion riemannZeta c

/-- The Riemann instance implies the half-plane at `1`. -/
theorem riemannClassicalRegion_halfPlane {c : ℝ} (hc : 0 < c)
    (h : RiemannClassicalRegion c) : ZeroFreeHalfPlane riemannZeta 1 :=
  classicalZeroFreeRegion_halfPlane hc h

/-- **The range of the Riemann classical region that Mathlib proves.**  For
`c ≤ 0` the classical line is at least `1`, so the region follows from
`riemannZeta_ne_zero_of_one_le_re`.  This is exactly the degenerate range of
constants available without a new zero-free theorem. -/
theorem riemannZeta_classicalRegion_of_nonpos {c : ℝ} (hc : c ≤ 0) :
    RiemannClassicalRegion c :=
  classicalZeroFreeRegion_of_halfPlane_of_nonpos hc riemannZeta_closedHalfPlane

/-- **The classical region for a Dirichlet `L`-function**, with the conductor
`N` inserted into the logarithm:
`L(s, χ) ≠ 0` for `Re s > 1 - c / log(N (|Im s| + 2))`.  This is the
no-exceptional-zero form of the classical Dirichlet statement; the possible
real exceptional zero of a real character is not modelled by this `def`.
The paper's `β₀` slot in `DedekindZeroFreeAboveBeta` is the separate mechanism
for such an exception, and the reductions below are for the no-exception
case. -/
def DirichletClassicalRegion {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (c : ℝ) : Prop :=
  ∀ s : ℂ, 1 - c / Real.log ((N : ℝ) * (|s.im| + 2)) < s.re →
    DirichletCharacter.LFunction χ s ≠ 0

/-- The conductor factor makes the logarithm at least `log 2`, so the
Dirichlet region only ever divides by a positive number. -/
theorem dirichlet_conductor_log_pos {N : ℕ} [NeZero N] (s : ℂ) :
    0 < Real.log ((N : ℝ) * (|s.im| + 2)) := by
  apply Real.log_pos
  have hN : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hX : (1 : ℝ) < |s.im| + 2 := by
    have := abs_nonneg s.im
    linarith
  have hNX : |s.im| + 2 ≤ (N : ℝ) * (|s.im| + 2) := by
    calc
      |s.im| + 2 = 1 * (|s.im| + 2) := by ring
      _ ≤ (N : ℝ) * (|s.im| + 2) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
  linarith

/-- The conductor-form Dirichlet region implies the half-plane at `1`. -/
theorem dirichletClassicalRegion_halfPlane {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {c : ℝ} (hc : 0 < c)
    (h : DirichletClassicalRegion χ c) :
    ZeroFreeHalfPlane (DirichletCharacter.LFunction χ) 1 := by
  intro s hs
  apply h s
  have hpos : 0 < c / Real.log ((N : ℝ) * (|s.im| + 2)) :=
    div_pos hc (dirichlet_conductor_log_pos s)
  linarith

/-- **The range of the nontrivial Dirichlet classical region that Mathlib
proves.**  For `c ≤ 0` the conductor line is at least `1`, so
`LFunction_ne_zero_of_one_le_re` gives the region. -/
theorem dirichlet_classicalRegion_of_nonpos {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {c : ℝ} (hc : c ≤ 0) :
    DirichletClassicalRegion χ c := by
  intro s hs
  apply dirichletL_closedHalfPlane (N := N) hχ s
  have hlog := dirichlet_conductor_log_pos (N := N) s
  have hquot : c / Real.log ((N : ℝ) * (|s.im| + 2)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hc (le_of_lt hlog)
  linarith

/-- The character-modulo-`1` case, where the `L`-function is `riemannZeta`. -/
theorem dirichlet_modOne_classicalRegion_of_nonpos (χ : DirichletCharacter ℂ 1)
    {c : ℝ} (hc : c ≤ 0) : DirichletClassicalRegion χ c := by
  intro s hs
  apply dirichletL_modOne_closedHalfPlane χ s
  have hlog : 0 < Real.log ((1 : ℝ) * (|s.im| + 2)) := by
    simpa only [Nat.cast_one] using dirichlet_conductor_log_pos (N := 1) s
  have hquot : c / Real.log ((1 : ℝ) * (|s.im| + 2)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hc (le_of_lt hlog)
  linarith

/-- **The conductor-form classical region plus its height bound gives the
uniform strip.**  At each zero the conductor height bound
`log(N (|Im ρ| + 2)) ≤ discLog n` moves the classical line
`1 - c / log(N (|Im ρ| + 2))` to the paper's line `1 - c / discLog n`. -/
theorem dirichletClassicalRegion_uniformSequence {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {c : ℝ} (hc : 0 < c)
    (h : DirichletClassicalRegion χ c)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {discLog : ℕ → ℝ}
    (hh : ∀ n, Real.log ((N : ℝ) * (|(Z.zero n).im| + 2)) ≤ discLog n) :
    ZeroSequenceUniformRegion Z c discLog := by
  intro n
  by_contra hnot
  have hlt : 1 - c / discLog n < Z.realPart n := lt_of_not_ge hnot
  have hlogpos : 0 < Real.log ((N : ℝ) * (|(Z.zero n).im| + 2)) :=
    dirichlet_conductor_log_pos (Z.zero n)
  have hdiv : c / discLog n ≤
      c / Real.log ((N : ℝ) * (|(Z.zero n).im| + 2)) :=
    div_le_div_of_nonneg_left (le_of_lt hc) hlogpos (hh n)
  have hregion' :
      1 - c / Real.log ((N : ℝ) * (|(Z.zero n).im| + 2)) < Z.realPart n := by
    linarith
  have hregion :
      1 - c / Real.log ((N : ℝ) * (|(Z.zero n).im| + 2)) < (Z.zero n).re := by
    simpa only [Z.realPart_eq n] using hregion'
  exact h (Z.zero n) hregion (Z.isZero n)

/-! ## 3. The uniform-in-height region -/

/-- **The paper's uniform-in-height zero-free region.**  For a fixed
denominator `L`, the function has no zero with `Re s > 1 - c / L`.  When
`L = log |Δ_E|` this is the constant-width strip of the paper. -/
def UniformZeroFreeRegion (f : ℂ → ℂ) (c L : ℝ) : Prop :=
  ∀ s : ℂ, 1 - c / L < s.re → f s ≠ 0

/-- A uniform region with `c > 0` and `L > 0` implies the closed half-plane. -/
theorem UniformZeroFreeRegion.halfPlane {f : ℂ → ℂ} {c L : ℝ}
    (hc : 0 < c) (hL : 0 < L) (h : UniformZeroFreeRegion f c L) :
    ZeroFreeHalfPlane f 1 := by
  intro s hs
  apply h s
  have hpos : 0 < c / L := div_pos hc hL
  linarith

/-- **The uniform region in gap form.**  At a zero, the uniform region is
exactly the division-free inequality `c ≤ (1 - Re s) * L`. -/
theorem uniformZeroFreeRegion_gap {f : ℂ → ℂ} {c L : ℝ} (hL : 0 < L)
    (h : UniformZeroFreeRegion f c L) {s : ℂ} (hz : f s = 0) :
    c ≤ (1 - s.re) * L := by
  by_contra hnot
  have hprod : (1 - s.re) * L < c := lt_of_not_ge hnot
  have hquot : 1 - s.re < c / L := (lt_div_iff₀ hL).mpr hprod
  exact h s (by linarith) hz

/-! ## 4. The height bound and the uniform strip on a zero sequence -/

/-- **The explicit height input.**  Every zero in the sequence has
`log(|Im ρ| + 2) ≤ discLog n`.  For the paper's choice
`discLog n = log |Δ_E|` this says that the zeros occur at height at most the
discriminant, equivalently `|Im ρ| + 2 ≤ |Δ_E|`.

This is the only extra input needed to pass from the height-dependent
classical region to the paper's fixed-denominator strip. -/
def ZeroHeightBoundAt {f : ℂ → ℂ} (Z : ZetaZeroSequence f)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, Real.log (|(Z.zero n).im| + 2) ≤ discLog n

/-- The scalar (whole-function) form of the height input. -/
def ZeroHeightBound (f : ℂ → ℂ) (L : ℝ) : Prop :=
  ∀ s : ℂ, f s = 0 → Real.log (|s.im| + 2) ≤ L

/-- A scalar height bound gives the sequence form with constant `discLog`. -/
theorem ZeroHeightBound.toAt {f : ℂ → ℂ} {L : ℝ} (h : ZeroHeightBound f L)
    (Z : ZetaZeroSequence f) : ZeroHeightBoundAt Z (fun _ => L) :=
  fun n => h (Z.zero n) (Z.isZero n)

/-- The height bound makes `discLog` positive wherever it is used, because
`log(|Im ρ| + 2) ≥ log 2 > 0`.  No separate positivity hypothesis on
`discLog` is required. -/
theorem zeroHeightBoundAt_discLog_pos {f : ℂ → ℂ} (Z : ZetaZeroSequence f)
    {discLog : ℕ → ℝ} (hh : ZeroHeightBoundAt Z discLog) :
    ∀ n, 0 < discLog n := by
  intro n
  have h2 : 0 < Real.log (|(Z.zero n).im| + 2) := by
    apply Real.log_pos
    have := abs_nonneg (Z.zero n).im
    linarith
  exact lt_of_lt_of_le h2 (hh n)

/-- **The whole-function height bridge.**  The height-dependent classical
region and a global height bound give the fixed-denominator uniform region. -/
theorem classicalZeroFreeRegion_toUniform {f : ℂ → ℂ} {c L : ℝ}
    (hc : 0 < c) (h : ClassicalZeroFreeRegion f c)
    (hh : ZeroHeightBound f L) : UniformZeroFreeRegion f c L := by
  intro s hs hz
  have hlogpos : 0 < Real.log (|s.im| + 2) := by
    apply Real.log_pos
    have := abs_nonneg s.im
    linarith
  have hdiv : c / L ≤ c / Real.log (|s.im| + 2) :=
    div_le_div_of_nonneg_left (le_of_lt hc) hlogpos (hh s hz)
  have hregion : 1 - c / Real.log (|s.im| + 2) < s.re := by linarith
  exact h s hregion hz

/-- **The classical region plus the height bound gives the uniform strip.**
At index `n`, the classical region bounds `Re ρ` by
`1 - c / log(|Im ρ| + 2)`; the height bound says
`log(|Im ρ| + 2) ≤ discLog n`, and monotonicity of `t ↦ 1 - c / t` moves the
line to `1 - c / discLog n`. -/
theorem classicalZeroFreeRegion_uniformSequence {f : ℂ → ℂ} {c : ℝ}
    (hc : 0 < c) (h : ClassicalZeroFreeRegion f c)
    (Z : ZetaZeroSequence f) {discLog : ℕ → ℝ}
    (hh : ZeroHeightBoundAt Z discLog) :
    ZeroSequenceUniformRegion Z c discLog := by
  intro n
  by_contra hnot
  have hlt : 1 - c / discLog n < Z.realPart n := lt_of_not_ge hnot
  have hlogpos : 0 < Real.log (|(Z.zero n).im| + 2) := by
    apply Real.log_pos
    have := abs_nonneg (Z.zero n).im
    linarith
  have hdiv : c / discLog n ≤ c / Real.log (|(Z.zero n).im| + 2) :=
    div_le_div_of_nonneg_left (le_of_lt hc) hlogpos (hh n)
  have hregion' : 1 - c / Real.log (|(Z.zero n).im| + 2) < Z.realPart n := by
    linarith
  have hregion : 1 - c / Real.log (|(Z.zero n).im| + 2) < (Z.zero n).re := by
    simpa only [Z.realPart_eq n] using hregion'
  exact h (Z.zero n) hregion (Z.isZero n)

/-- The classical region plus the height bound gives `DedekindZeroFreeStripZeros`. -/
theorem classicalZeroFreeRegion_stripZeros {f : ℂ → ℂ} {c : ℝ}
    (hc : 0 < c) (h : ClassicalZeroFreeRegion f c)
    {beta0 : ℕ → ℝ} (Z : ZetaZeroSequence f) {discLog : ℕ → ℝ}
    (hh : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeStripZeros Z beta0 c discLog :=
  ZeroSequenceUniformRegion.toStripZeros
    (classicalZeroFreeRegion_uniformSequence hc h Z hh)
    (zeroHeightBoundAt_discLog_pos Z hh)

/-- The classical region plus the height bound gives the division-free strip
distance. -/
theorem classicalZeroFreeRegion_stripDistance {f : ℂ → ℂ} {c : ℝ}
    (hc : 0 < c) (h : ClassicalZeroFreeRegion f c)
    {beta0 : ℕ → ℝ} (Z : ZetaZeroSequence f) {discLog : ℕ → ℝ}
    (hh : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeStripDistance beta0 Z.realPart c discLog :=
  ZeroSequenceUniformRegion.toStripDistance
    (classicalZeroFreeRegion_uniformSequence hc h Z hh)
    (zeroHeightBoundAt_discLog_pos Z hh)

/-- The classical region plus the height bound gives the paper's
`DedekindZeroFreeAboveBeta`. -/
theorem classicalZeroFreeRegion_aboveBeta {f : ℂ → ℂ} {c : ℝ}
    (hc : 0 < c) (h : ClassicalZeroFreeRegion f c)
    {beta0 : ℕ → ℝ} (Z : ZetaZeroSequence f) {discLog : ℕ → ℝ}
    (hh : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart c discLog :=
  ZeroSequenceUniformRegion.toAboveBeta
    (classicalZeroFreeRegion_uniformSequence hc h Z hh)

/-- The classical region plus the height bound gives `DedekindZeroFreeInput`. -/
theorem classicalZeroFreeRegion_zeroFreeInput {f : ℂ → ℂ} {c : ℝ}
    (hc : 0 < c) (h : ClassicalZeroFreeRegion f c)
    {beta0 : ℕ → ℝ} (Z : ZetaZeroSequence f) {discLog : ℕ → ℝ}
    (hh : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeInput beta0 Z.realPart c discLog :=
  ZeroSequenceUniformRegion.toZeroFreeInput
    (classicalZeroFreeRegion_uniformSequence hc h Z hh) hc

/-! ## 5. The packaged classical input -/

/-- **The smallest explicit classical region input.**  It bundles the
positive classical constant, the height-dependent de la Vallée Poussin region,
and the height bridge.  Each field is an explicit analytic or arithmetic
hypothesis; the structure does not assert any of them. -/
structure ClassicalRegionInput (f : ℂ → ℂ) (beta0 : ℕ → ℝ) (c : ℝ)
    (discLog : ℕ → ℝ) (Z : ZetaZeroSequence f) : Prop where
  /-- The classical zero-free constant is positive. -/
  c_pos : 0 < c
  /-- The height-dependent classical de la Vallée Poussin region. -/
  region : ClassicalZeroFreeRegion f c
  /-- The height bridge to the paper's fixed denominator. -/
  height : ZeroHeightBoundAt Z discLog

namespace ClassicalRegionInput

/-- The packaged input gives the uniform strip. -/
theorem toUniform {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {c : ℝ}
    {discLog : ℕ → ℝ} {Z : ZetaZeroSequence f}
    (A : ClassicalRegionInput f beta0 c discLog Z) :
    ZeroSequenceUniformRegion Z c discLog :=
  classicalZeroFreeRegion_uniformSequence A.c_pos A.region Z A.height

/-- The packaged input gives the paper's zero-free region. -/
theorem toAboveBeta {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {c : ℝ}
    {discLog : ℕ → ℝ} {Z : ZetaZeroSequence f}
    (A : ClassicalRegionInput f beta0 c discLog Z) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart c discLog :=
  ZeroSequenceUniformRegion.toAboveBeta A.toUniform

/-- The packaged input gives the residual strip statement. -/
theorem toBelowOne {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {c : ℝ}
    {discLog : ℕ → ℝ} {Z : ZetaZeroSequence f}
    (A : ClassicalRegionInput f beta0 c discLog Z) :
    DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart c discLog :=
  ZeroSequenceUniformRegion.toBelowOne A.toUniform

/-- The packaged input gives `DedekindZeroFreeStripZeros`. -/
theorem toStripZeros {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {c : ℝ}
    {discLog : ℕ → ℝ} {Z : ZetaZeroSequence f}
    (A : ClassicalRegionInput f beta0 c discLog Z) :
    DedekindZeroFreeStripZeros Z beta0 c discLog :=
  ZeroSequenceUniformRegion.toStripZeros A.toUniform
    (zeroHeightBoundAt_discLog_pos Z A.height)

/-- The packaged input gives `DedekindZeroFreeInput`. -/
theorem toZeroFreeInput {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {c : ℝ}
    {discLog : ℕ → ℝ} {Z : ZetaZeroSequence f}
    (A : ClassicalRegionInput f beta0 c discLog Z) :
    DedekindZeroFreeInput beta0 Z.realPart c discLog :=
  ZeroSequenceUniformRegion.toZeroFreeInput A.toUniform A.c_pos

end ClassicalRegionInput

/-! ## 6. Riemann-zeta and Dirichlet instantiations -/

/-- The Riemann-zeta instance of the packaged classical input. -/
theorem riemannZeta_classicalRegion_aboveBeta
    (Z : ZetaZeroSequence riemannZeta) {beta0 : ℕ → ℝ} {c : ℝ}
    {discLog : ℕ → ℝ} (hc : 0 < c) (h : RiemannClassicalRegion c)
    (hh : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart c discLog :=
  classicalZeroFreeRegion_aboveBeta hc h Z hh

/-- The Riemann-zeta instance of the packaged input. -/
theorem riemannZetaClassicalInput (Z : ZetaZeroSequence riemannZeta)
    (beta0 : ℕ → ℝ) (c : ℝ) (discLog : ℕ → ℝ)
    (hc : 0 < c) (h : RiemannClassicalRegion c)
    (hh : ZeroHeightBoundAt Z discLog) :
    ClassicalRegionInput riemannZeta beta0 c discLog Z :=
  { c_pos := hc, region := h, height := hh }

/-- **The Dirichlet instance gives the paper's zero-free region.**  The height
bound is the conductor-form bound `log(N (|Im ρ| + 2)) ≤ discLog n`. -/
theorem dirichlet_classicalRegion_aboveBeta {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {beta0 : ℕ → ℝ} {c : ℝ} {discLog : ℕ → ℝ}
    (hc : 0 < c) (h : DirichletClassicalRegion χ c)
    (hh : ∀ n, Real.log ((N : ℝ) * (|(Z.zero n).im| + 2)) ≤ discLog n) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart c discLog :=
  ZeroSequenceUniformRegion.toAboveBeta
    (dirichletClassicalRegion_uniformSequence χ hc h Z hh)

/-- The Dirichlet instance gives `DedekindZeroFreeInput`. -/
theorem dirichlet_classicalRegion_zeroFreeInput {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (Z : ZetaZeroSequence (DirichletCharacter.LFunction χ))
    {beta0 : ℕ → ℝ} {c : ℝ} {discLog : ℕ → ℝ}
    (hc : 0 < c) (h : DirichletClassicalRegion χ c)
    (hh : ∀ n, Real.log ((N : ℝ) * (|(Z.zero n).im| + 2)) ≤ discLog n) :
    DedekindZeroFreeInput beta0 Z.realPart c discLog where
  cz_pos := hc
  above_beta := dirichlet_classicalRegion_aboveBeta χ Z hc h hh

/-! ## 7. The Dedekind zeta function -/

/-- **The classical region for a Dedekind zeta function.** -/
def DedekindClassicalRegion (K : Type*) [Field K] [NumberField K]
    (c : ℝ) : Prop :=
  ClassicalZeroFreeRegion (NumberField.dedekindZeta K) c

/-- The classical Dedekind region supplies the half-plane hypothesis that
Mathlib does not prove: `DedekindZetaHalfPlane K`. -/
theorem dedekindClassicalRegion_halfPlane (K : Type*) [Field K] [NumberField K]
    {c : ℝ} (hc : 0 < c) (h : DedekindClassicalRegion K c) :
    DedekindZetaHalfPlane K :=
  classicalZeroFreeRegion_halfPlane hc h

/-- **The scalar height input for the Dedekind zeta function on the strip.**
For strip zeros `β₀ < Re z < 1` one has `log(|Im z| + 2) ≤ discLog`.  The
restriction to the strip is harmless: only strip zeros enter
`DedekindZetaStripInequality`. -/
def DedekindStripHeightBound (K : Type*) [Field K] [NumberField K]
    (beta0 discLog : ℝ) : Prop :=
  ∀ z : ℂ, NumberField.dedekindZeta K z = 0 → beta0 < z.re → z.re < 1 →
    Real.log (|z.im| + 2) ≤ discLog

/-- **The classical region plus the strip height bound give the exact
Dedekind strip inequality.**  This is the scalar bridge from the classical
de la Vallée Poussin statement to `DedekindZetaStripInequality`. -/
theorem dedekindClassicalRegion_stripInequality (K : Type*) [Field K]
    [NumberField K] {beta0 c discLog : ℝ}
    (h : DedekindClassicalRegion K c)
    (hh : DedekindStripHeightBound K beta0 discLog) :
    DedekindZetaStripInequality K beta0 c discLog := by
  intro z hz hb hlt
  have hLpos : 0 < Real.log (|z.im| + 2) := by
    apply Real.log_pos
    have := abs_nonneg z.im
    linarith
  have hLle : Real.log (|z.im| + 2) ≤ discLog := hh z hz hb hlt
  have hdisc : 0 < discLog := lt_of_lt_of_le hLpos hLle
  have hreg : z.re ≤ 1 - c / Real.log (|z.im| + 2) := by
    by_contra hnot
    exact h z (lt_of_not_ge hnot) hz
  have hc_le : c ≤ (1 - z.re) * Real.log (|z.im| + 2) := by
    have hquot : c / Real.log (|z.im| + 2) ≤ 1 - z.re := by linarith
    exact (div_le_iff₀ hLpos).mp hquot
  have hmul : (1 - z.re) * Real.log (|z.im| + 2) ≤ (1 - z.re) * discLog :=
    mul_le_mul_of_nonneg_left hLle (by linarith)
  have hdist : c ≤ (1 - z.re) * discLog := le_trans hc_le hmul
  have hquot : c / discLog ≤ 1 - z.re := (div_le_iff₀ hdisc).mpr hdist
  linarith

/-- **The classical region and the height bound give the paper's missing
Dedekind strip input** `DedekindZetaStripInput`, with constant parameters. -/
theorem dedekindClassicalRegion_stripInput (K : Type*) [Field K]
    [NumberField K] {beta0 c discLog : ℝ}
    (h : DedekindClassicalRegion K c)
    (hh : DedekindStripHeightBound K beta0 discLog) :
    DedekindZetaStripInput K (fun _ => beta0) c (fun _ => discLog) :=
  dedekindZetaStripInput_of_inequality K (fun _ => rfl) (fun _ => rfl)
    (dedekindClassicalRegion_stripInequality K h hh)

/-- **The classical region gives the residual strip statement.** -/
theorem dedekindClassicalRegion_belowOne (K : Type*) [Field K] [NumberField K]
    {beta0 c discLog : ℝ}
    (h : DedekindClassicalRegion K c)
    (hh : DedekindStripHeightBound K beta0 discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBetaBelowOne (fun _ => beta0) Z.realPart c
      (fun _ => discLog) :=
  dedekindZeroFreeAboveBetaBelowOne_of_zetaStripInput K
    (dedekindClassicalRegion_stripInput K h hh) Z

/-- **The classical region gives the paper's Dedekind zero-free region.**
The half-plane part is supplied by `classicalZeroFreeRegion_halfPlane`, so no
separate `DedekindZetaHalfPlane` hypothesis remains. -/
theorem dedekindClassicalRegion_aboveBeta (K : Type*) [Field K] [NumberField K]
    {beta0 c discLog : ℝ} (hc : 0 < c)
    (h : DedekindClassicalRegion K c)
    (hh : DedekindStripHeightBound K beta0 discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBeta (fun _ => beta0) Z.realPart c
      (fun _ => discLog) :=
  dedekindZeroFreeAboveBeta_of_zetaStripInput_of_halfPlane K
    (dedekindClassicalRegion_halfPlane K hc h)
    (dedekindClassicalRegion_stripInput K h hh) Z

/-- **The classical region gives the smallest Dedekind zero-free bundle.** -/
theorem dedekindClassicalRegion_zeroFreeInput (K : Type*) [Field K]
    [NumberField K] {beta0 c discLog : ℝ} (hc : 0 < c)
    (h : DedekindClassicalRegion K c)
    (hh : DedekindStripHeightBound K beta0 discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput (fun _ => beta0) Z.realPart c (fun _ => discLog) where
  cz_pos := hc
  above_beta := dedekindClassicalRegion_aboveBeta K hc h hh Z

/-! ## Axiom audit -/

#print axioms classicalZeroFreeRegion_halfPlane
#print axioms ClassicalZeroFreeRegionExists.halfPlane
#print axioms classicalZeroFreeRegion_re_lt_one
#print axioms classicalZeroFreeRegion_zero_of_halfPlane
#print axioms classicalZeroFreeRegion_of_halfPlane_of_nonpos
#print axioms classicalZeroFreeRegion_of_le
#print axioms riemannClassicalRegion_halfPlane
#print axioms riemannZeta_classicalRegion_of_nonpos
#print axioms dirichlet_conductor_log_pos
#print axioms dirichlet_classicalRegion_of_nonpos
#print axioms dirichlet_modOne_classicalRegion_of_nonpos
#print axioms dirichletClassicalRegion_halfPlane
#print axioms dirichletClassicalRegion_uniformSequence
#print axioms UniformZeroFreeRegion.halfPlane
#print axioms classicalZeroFreeRegion_toUniform
#print axioms uniformZeroFreeRegion_gap
#print axioms ZeroHeightBound.toAt
#print axioms zeroHeightBoundAt_discLog_pos
#print axioms classicalZeroFreeRegion_uniformSequence
#print axioms classicalZeroFreeRegion_stripZeros
#print axioms classicalZeroFreeRegion_stripDistance
#print axioms classicalZeroFreeRegion_aboveBeta
#print axioms classicalZeroFreeRegion_zeroFreeInput
#print axioms ZeroSequenceUniformRegion.toAboveBeta
#print axioms ZeroSequenceUniformRegion.toBelowOne
#print axioms ZeroSequenceUniformRegion.toStripDistance
#print axioms ZeroSequenceUniformRegion.toStripZeros
#print axioms ZeroSequenceUniformRegion.toZeroFreeInput
#print axioms ClassicalRegionInput.toUniform
#print axioms ClassicalRegionInput.toAboveBeta
#print axioms ClassicalRegionInput.toBelowOne
#print axioms ClassicalRegionInput.toStripZeros
#print axioms ClassicalRegionInput.toZeroFreeInput
#print axioms riemannZeta_classicalRegion_aboveBeta
#print axioms riemannZetaClassicalInput
#print axioms dirichlet_classicalRegion_aboveBeta
#print axioms dirichlet_classicalRegion_zeroFreeInput
#print axioms dedekindClassicalRegion_halfPlane
#print axioms dedekindClassicalRegion_stripInequality
#print axioms dedekindClassicalRegion_stripInput
#print axioms dedekindClassicalRegion_belowOne
#print axioms dedekindClassicalRegion_aboveBeta
#print axioms dedekindClassicalRegion_zeroFreeInput

end

end Cogentic.RandomizedL34ClassicalRegion
