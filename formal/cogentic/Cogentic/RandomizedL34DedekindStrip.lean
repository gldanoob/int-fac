import Cogentic.RandomizedL34BelowOne

/-!
# L34: the Dedekind strip input from the classical zero-free region

`Cogentic.RandomizedL34BelowOne` reduced the paper's zero-free input to the
exact residual strip statement

`β₀ < Re ρ → Re ρ < 1 → Re ρ ≤ 1 - cz / log |Δ_E|`

and isolated it as `DedekindZetaStripInput`, a `def` and never a theorem.  The
present file closes the interface around that definition: it states the
*classical* Dedekind zero-free region, proves that the classical region implies
the strip input, and identifies the smallest explicit strip inequality that is
equivalent to `DedekindZetaStripInput`.

## What is proved

1. **Classical region implies the strip input.**  The classical Dedekind region
   `DedekindZetaClassicalRegion K β₀ cz D` says that every zero of `ζ_K` above
   `β₀` lies on the zero-free side of `1 - cz / D`.  Restricting to `Re ρ < 1`
   gives `DedekindZetaStripInput K β₀ cz D`
   (`DedekindZetaStripInput_of_classicalRegion`).

2. **The converse needs only the half-plane at `1`.**  If every zero with
   `Re ρ ≥ 1` is excluded (`DedekindZetaHalfPlane K`), then the strip input is
   *exactly* the classical region
   (`DedekindZetaClassicalRegion_iff_stripInput_of_halfPlane`).  Hence, under the
   half-plane, the strip input loses no information: it is the classical region
   with the already-excluded half-plane removed.

3. **The smallest explicit strip inequality.**  On the open strip the
   denominator `log |Δ_E|` is positive, so the division-free statement

   `cz ≤ (1 - Re ρ) * log |Δ_E|`

   is equivalent to `DedekindZetaStripInput`
   (`DedekindZetaStripInput_iff_stripDistance`,
   `DedekindZetaStripDistanceInput`).  The scalar form
   `DedekindZetaStripInequalityDistance` is the same statement for one field.

4. **The paper's zero-free input.**  The classical region gives the paper's
   `DedekindZeroFreeAboveBeta` for every zero sequence, with no half-plane
   hypothesis (`DedekindZetaClassicalInput.toAboveBeta`), and the strip distance
   input gives it under the half-plane
   (`DedekindZetaStripDistanceInput.toAboveBeta`).  Both compose with the
   existing `dedekindAnalyticInputs_of_zeroFree`.

5. **Riemann and Dirichlet.**  The same classical-region/strip-region interface
   is instantiated for `riemannZeta` and for Dirichlet `L`-functions
   (`RiemannZetaClassicalRegion`, `DirichletLClassicalRegion`).  For `β₀ ≥ 1`
   Mathlib's half-plane results really do give these classical regions
   (`riemannZetaClassicalRegion_of_one_le_beta0`,
   `dirichletLClassicalRegion_of_one_le_beta0`); for `β₀ < 1` no effective
   `1 - c / log` region is available in Mathlib, so the region remains a
   hypothesis.

6. **Factorization.**  If `ζ_K` is a product of factors and each factor has the
   strip region (or half-plane), then `ζ_K` has it too
   (`stripRegion_of_prod`, `classicalRegion_of_factorization`).  This is the
   precise form in which the Riemann/Dirichlet classical regions feed into a
   Dedekind statement; the factorization itself is a hypothesis.

## What is not claimed

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  The classical
zero-free region for `ζ_K` is never asserted: it is a `def` / `structure`
hypothesis.  The `β₀ ≥ 1` instances are genuine Mathlib consequences of the
half-plane estimates, and they are vacuous on the open strip, so they do not
claim an effective zero-free region either.
-/

namespace Cogentic.RandomizedL34DedekindStrip

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34BelowOne

noncomputable section

/-! ## 1. The classical region and its strip restriction -/

/-- **The classical zero-free region for a zeta-type function.**  Above `β₀`,
every zero lies on the zero-free side of the line `1 - cz / log |Δ|`.  This is
the form in which a classical Dedekind (or Riemann/Dirichlet) zero-free region
is quoted; it is a hypothesis, never proved here. -/
def ZetaClassicalRegion (f : ℂ → ℂ) (beta0 : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (z : ℂ), f z = 0 → beta0 n < z.re → z.re ≤ 1 - cz / discLog n

/-- **The division-free classical region.**  Above `β₀`, the distance
`1 - Re ρ` to the line `1` is at least `cz / log |Δ|`. -/
def ZetaClassicalDistance (f : ℂ → ℂ) (beta0 : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (z : ℂ), f z = 0 → beta0 n < z.re → cz ≤ (1 - z.re) * discLog n

/-- **The strip region for a zeta-type function.**  The classical region with
the half-plane `Re ρ ≥ 1` removed from the hypotheses. -/
def ZetaStripRegion (f : ℂ → ℂ) (beta0 : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (z : ℂ), f z = 0 → beta0 n < z.re → z.re < 1 →
    z.re ≤ 1 - cz / discLog n

/-- **The division-free strip region.**  The smallest explicit strip inequality
for one zero: `cz ≤ (1 - Re ρ) log |Δ|` on `β₀ < Re ρ < 1`. -/
def ZetaStripDistance (f : ℂ → ℂ) (beta0 : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (z : ℂ), f z = 0 → beta0 n < z.re → z.re < 1 →
    cz ≤ (1 - z.re) * discLog n

/-- The division-free classical region is the classical region when
`log |Δ| > 0`. -/
theorem classicalRegion_iff_distance {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ}
    {discLog : ℕ → ℝ} (hd : ∀ n, 0 < discLog n) :
    ZetaClassicalRegion f beta0 cz discLog ↔
      ZetaClassicalDistance f beta0 cz discLog := by
  constructor
  · intro h n z hz hb
    have hle : z.re ≤ 1 - cz / discLog n := h n z hz hb
    have hdiv : cz / discLog n ≤ 1 - z.re := by linarith
    exact (div_le_iff₀ (hd n)).mp hdiv
  · intro h n z hz hb
    have hineq : cz ≤ (1 - z.re) * discLog n := h n z hz hb
    have hdiv : cz / discLog n ≤ 1 - z.re := (div_le_iff₀ (hd n)).mpr hineq
    linarith

/-- The division-free strip region is the strip region when `log |Δ| > 0`. -/
theorem stripRegion_iff_distance {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ}
    {discLog : ℕ → ℝ} (hd : ∀ n, 0 < discLog n) :
    ZetaStripRegion f beta0 cz discLog ↔
      ZetaStripDistance f beta0 cz discLog := by
  constructor
  · intro h n z hz hb hlt
    have hle : z.re ≤ 1 - cz / discLog n := h n z hz hb hlt
    have hdiv : cz / discLog n ≤ 1 - z.re := by linarith
    exact (div_le_iff₀ (hd n)).mp hdiv
  · intro h n z hz hb hlt
    have hineq : cz ≤ (1 - z.re) * discLog n := h n z hz hb hlt
    have hdiv : cz / discLog n ≤ 1 - z.re := (div_le_iff₀ (hd n)).mpr hineq
    linarith

/-- **The classical region restricts to the strip.**  No hypothesis is needed:
the strip is a subset of the region above `β₀`. -/
theorem stripRegion_of_classicalRegion {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ}
    {discLog : ℕ → ℝ} (h : ZetaClassicalRegion f beta0 cz discLog) :
    ZetaStripRegion f beta0 cz discLog :=
  fun n z hz hb _ => h n z hz hb

/-- **The strip region plus a half-plane at `1` is the classical region.**  The
half-plane removes every zero with `Re ρ ≥ 1`, and the strip region supplies the
inequality on the remaining zeros. -/
theorem classicalRegion_of_stripRegion_of_halfPlane {f : ℂ → ℂ}
    (hf : ZeroFreeHalfPlane f 1) {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : ZetaStripRegion f beta0 cz discLog) :
    ZetaClassicalRegion f beta0 cz discLog := by
  intro n z hz hb
  by_cases hlt : z.re < 1
  · exact h n z hz hb hlt
  · exact absurd hz (hf z (le_of_not_gt hlt))

/-- **Under the half-plane at `1`, the strip region is exactly the classical
region.**  The strip condition `Re ρ < 1` is not an extra hypothesis: it is a
consequence of the half-plane for every zero. -/
theorem classicalRegion_iff_stripRegion_of_halfPlane {f : ℂ → ℂ}
    (hf : ZeroFreeHalfPlane f 1) {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} :
    ZetaClassicalRegion f beta0 cz discLog ↔
      ZetaStripRegion f beta0 cz discLog :=
  ⟨stripRegion_of_classicalRegion,
    classicalRegion_of_stripRegion_of_halfPlane hf⟩

/-! ## 2. Monotonicity in the zero-free constant -/

/-- A classical region with a larger constant gives the region with any smaller
positive constant. -/
theorem classicalRegion_of_le {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz cz' : ℝ}
    {discLog : ℕ → ℝ} (hcz : cz ≤ cz') (hd : ∀ n, 0 < discLog n)
    (h : ZetaClassicalRegion f beta0 cz' discLog) :
    ZetaClassicalRegion f beta0 cz discLog := by
  intro n z hz hb
  have hle : z.re ≤ 1 - cz' / discLog n := h n z hz hb
  have hdiv : cz / discLog n ≤ cz' / discLog n :=
    div_le_div_of_nonneg_right hcz (le_of_lt (hd n))
  linarith

/-- The division-free version of the constant comparison needs no positivity:
`cz ≤ cz'` is simply composed with the stronger inequality. -/
theorem classicalDistance_of_le {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz cz' : ℝ}
    {discLog : ℕ → ℝ} (hcz : cz ≤ cz')
    (h : ZetaClassicalDistance f beta0 cz' discLog) :
    ZetaClassicalDistance f beta0 cz discLog :=
  fun n z hz hb => le_trans hcz (h n z hz hb)

/-- A strip region with a larger constant gives the strip region with any
smaller constant. -/
theorem stripRegion_of_le {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz cz' : ℝ}
    {discLog : ℕ → ℝ} (hcz : cz ≤ cz') (hd : ∀ n, 0 < discLog n)
    (h : ZetaStripRegion f beta0 cz' discLog) :
    ZetaStripRegion f beta0 cz discLog := by
  intro n z hz hb hlt
  have hle : z.re ≤ 1 - cz' / discLog n := h n z hz hb hlt
  have hdiv : cz / discLog n ≤ cz' / discLog n :=
    div_le_div_of_nonneg_right hcz (le_of_lt (hd n))
  linarith

/-- The division-free strip constant comparison. -/
theorem stripDistance_of_le {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz cz' : ℝ}
    {discLog : ℕ → ℝ} (hcz : cz ≤ cz')
    (h : ZetaStripDistance f beta0 cz' discLog) :
    ZetaStripDistance f beta0 cz discLog :=
  fun n z hz hb hlt => le_trans hcz (h n z hz hb hlt)

/-! ## 3. Reduction through a product factorization -/

/-- **A product of strip regions is a strip region.**  If `f` is the product of
factors `g i` and every factor satisfies the same strip region, then `f` does.
This is the exact step by which Riemann/Dirichlet regions feed into a Dedekind
statement, once the product decomposition of `ζ_K` is supplied. -/
theorem stripRegion_of_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℂ → ℂ} {g : ι → ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hfac : ∀ s : ℂ, f s = ∏ i, g i s)
    (hg : ∀ i, ZetaStripRegion (g i) beta0 cz discLog) :
    ZetaStripRegion f beta0 cz discLog := by
  intro n z hz hb hlt
  have hprod : (∏ i, g i z) = 0 := by rw [← hfac z]; exact hz
  have hmem : ∃ i : ι, g i z = 0 := by
    simpa using (Finset.prod_eq_zero_iff (s := (Finset.univ : Finset ι))
      (f := fun i => g i z)).mp hprod
  obtain ⟨i, hi⟩ := hmem
  exact hg i n z hi hb hlt

/-- **A product of classical regions is a classical region.** -/
theorem classicalRegion_of_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℂ → ℂ} {g : ι → ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hfac : ∀ s : ℂ, f s = ∏ i, g i s)
    (hg : ∀ i, ZetaClassicalRegion (g i) beta0 cz discLog) :
    ZetaClassicalRegion f beta0 cz discLog := by
  intro n z hz hb
  have hprod : (∏ i, g i z) = 0 := by rw [← hfac z]; exact hz
  have hmem : ∃ i : ι, g i z = 0 := by
    simpa using (Finset.prod_eq_zero_iff (s := (Finset.univ : Finset ι))
      (f := fun i => g i z)).mp hprod
  obtain ⟨i, hi⟩ := hmem
  exact hg i n z hi hb

/-- **A product of half-planes at `1` is a half-plane at `1`.** -/
theorem halfPlane_of_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℂ → ℂ} {g : ι → ℂ → ℂ}
    (hfac : ∀ s : ℂ, f s = ∏ i, g i s)
    (hg : ∀ i, ZeroFreeHalfPlane (g i) 1) :
    ZeroFreeHalfPlane f 1 := by
  intro z hz hzero
  have hprod : (∏ i, g i z) = 0 := by rw [← hfac z]; exact hzero
  have hmem : ∃ i : ι, g i z = 0 := by
    simpa using (Finset.prod_eq_zero_iff (s := (Finset.univ : Finset ι))
      (f := fun i => g i z)).mp hprod
  obtain ⟨i, hi⟩ := hmem
  exact hg i z hz hi

/-- **A product factorization and the factors' half-planes give the classical
region for `β₀ ≥ 1`.**  The region is vacuous, but this records the exact
Mathlib input (the half-plane at `1`) that produces it. -/
theorem classicalRegion_of_prod_halfPlane_of_one_le_beta0 {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : ℂ → ℂ} {g : ι → ℂ → ℂ}
    (hfac : ∀ s : ℂ, f s = ∏ i, g i s)
    (hg : ∀ i, ZeroFreeHalfPlane (g i) 1)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 ≤ beta0 n) (cz : ℝ) (discLog : ℕ → ℝ) :
    ZetaClassicalRegion f beta0 cz discLog := by
  intro n z hz hb
  exact absurd hz (halfPlane_of_prod hfac hg z (le_trans (hβ n) (le_of_lt hb)))

/-! ## 4. The Dedekind-zeta specializations -/

/-- The classical zero-free region for the Dedekind zeta function of `K`. -/
def DedekindZetaClassicalRegion (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  ZetaClassicalRegion (NumberField.dedekindZeta K) beta0 cz discLog

/-- The division-free Dedekind classical region. -/
def DedekindZetaClassicalDistance (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  ZetaClassicalDistance (NumberField.dedekindZeta K) beta0 cz discLog

/-- The division-free Dedekind strip region. -/
def DedekindZetaStripDistance (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  ZetaStripDistance (NumberField.dedekindZeta K) beta0 cz discLog

/-- `DedekindZetaStripInput` is the generic strip region for `ζ_K`; the two
definitions have the same body. -/
theorem dedekindZetaStripInput_iff_stripRegion (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZetaStripInput K beta0 cz discLog ↔
      ZetaStripRegion (NumberField.dedekindZeta K) beta0 cz discLog :=
  Iff.rfl

/-- **The classical Dedekind region implies `DedekindZetaStripInput`.**  This is
the requested reduction: the strip statement is the classical zero-free region
with the half-plane `Re ρ < 1` added to the hypotheses. -/
theorem DedekindZetaStripInput_of_classicalRegion (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZetaClassicalRegion K beta0 cz discLog) :
    DedekindZetaStripInput K beta0 cz discLog :=
  stripRegion_of_classicalRegion h

/-- The classical region in division-free form gives the strip input. -/
theorem DedekindZetaStripInput_of_classicalDistance (K : Type*) [Field K]
    [NumberField K] {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n)
    (h : DedekindZetaClassicalDistance K beta0 cz discLog) :
    DedekindZetaStripInput K beta0 cz discLog :=
  DedekindZetaStripInput_of_classicalRegion K
    ((classicalRegion_iff_distance hd).mpr h)

/-- **Under the half-plane, the classical Dedekind region is exactly the strip
input.** -/
theorem DedekindZetaClassicalRegion_iff_stripInput_of_halfPlane
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} :
    DedekindZetaClassicalRegion K beta0 cz discLog ↔
      DedekindZetaStripInput K beta0 cz discLog :=
  (classicalRegion_iff_stripRegion_of_halfPlane hK).trans
    (dedekindZetaStripInput_iff_stripRegion K beta0 cz discLog).symm

/-- The strip input and the half-plane give the classical region. -/
theorem DedekindZetaClassicalRegion_of_stripInput_of_halfPlane
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZetaStripInput K beta0 cz discLog) :
    DedekindZetaClassicalRegion K beta0 cz discLog :=
  (DedekindZetaClassicalRegion_iff_stripInput_of_halfPlane K hK).mpr h

/-- **The division-free form of `DedekindZetaStripInput`.** -/
theorem dedekindZetaStripInput_iff_stripDistance (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n) :
    DedekindZetaStripInput K beta0 cz discLog ↔
      DedekindZetaStripDistance K beta0 cz discLog :=
  (dedekindZetaStripInput_iff_stripRegion K beta0 cz discLog).trans
    (stripRegion_iff_distance hd)

/-! ## 5. The smallest explicit inputs -/

/-- **The classical Dedekind region as an input**, with the positivity data that
the paper's constants already carry. -/
structure DedekindZetaClassicalInput (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop where
  /-- The zero-free constant is positive. -/
  cz_pos : 0 < cz
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The classical zero-free region. -/
  region : DedekindZetaClassicalRegion K beta0 cz discLog

/-- **The smallest explicit strip input.**  Positivity of `cz` and `log |Δ_E|`
together with the division-free strip inequality. -/
structure DedekindZetaStripDistanceInput (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop where
  /-- The zero-free constant is positive. -/
  cz_pos : 0 < cz
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The division-free strip inequality. -/
  distance : DedekindZetaStripDistance K beta0 cz discLog

namespace DedekindZetaClassicalInput

/-- The classical region gives the paper's "above `β₀`" statement on any zero
sequence, with no half-plane hypothesis. -/
theorem toAboveBeta (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZetaClassicalInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog := by
  intro n hb
  have hb' : beta0 n < (Z.zero n).re := by
    simpa only [Z.realPart_eq n] using hb
  have h := C.region n (Z.zero n) (Z.isZero n) hb'
  simpa only [Z.realPart_eq n] using h

/-- The classical input gives the paper's smallest zero-free bundle. -/
theorem toDedekindZeroFreeInput (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZetaClassicalInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog where
  cz_pos := C.cz_pos
  above_beta := C.toAboveBeta K Z

/-- The classical input gives the strip input. -/
theorem toStripInput (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZetaClassicalInput K beta0 cz discLog) :
    DedekindZetaStripInput K beta0 cz discLog :=
  DedekindZetaStripInput_of_classicalRegion K C.region

/-- The classical input gives the smallest explicit strip input. -/
theorem toStripDistanceInput (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZetaClassicalInput K beta0 cz discLog) :
    DedekindZetaStripDistanceInput K beta0 cz discLog where
  cz_pos := C.cz_pos
  discLog_pos := C.discLog_pos
  distance := by
    intro n z hz hb _
    have hle : z.re ≤ 1 - cz / discLog n := C.region n z hz hb
    have hdiv : cz / discLog n ≤ 1 - z.re := by linarith
    exact (div_le_iff₀ (C.discLog_pos n)).mp hdiv

/-- A literature region with a larger constant gives the paper's constant. -/
theorem of_constant_le (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz cz' : ℝ} {discLog : ℕ → ℝ}
    (hcz_pos : 0 < cz) (hcz : cz ≤ cz')
    (C : DedekindZetaClassicalInput K beta0 cz' discLog) :
    DedekindZetaClassicalInput K beta0 cz discLog where
  cz_pos := hcz_pos
  discLog_pos := C.discLog_pos
  region := classicalRegion_of_le hcz C.discLog_pos C.region

end DedekindZetaClassicalInput

namespace DedekindZetaStripDistanceInput

/-- The smallest explicit strip input gives `DedekindZetaStripInput`. -/
theorem toStripInput (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (D : DedekindZetaStripDistanceInput K beta0 cz discLog) :
    DedekindZetaStripInput K beta0 cz discLog := by
  intro n z hz hb hlt
  have h := D.distance n z hz hb hlt
  have hdiv : cz / discLog n ≤ 1 - z.re := (div_le_iff₀ (D.discLog_pos n)).mpr h
  linarith

/-- The smallest explicit strip input gives the paper's residual strip
statement for any zero sequence. -/
theorem toAboveBetaBelowOne (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (D : DedekindZetaStripDistanceInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog := by
  intro n hb hlt
  have hb' : beta0 n < (Z.zero n).re := by
    simpa only [Z.realPart_eq n] using hb
  have hlt' : (Z.zero n).re < 1 := by
    simpa only [Z.realPart_eq n] using hlt
  have hdist := D.distance n (Z.zero n) (Z.isZero n) hb' hlt'
  have hdiv : cz / discLog n ≤ 1 - (Z.zero n).re :=
    (div_le_iff₀ (D.discLog_pos n)).mpr hdist
  have hres : (Z.zero n).re ≤ 1 - cz / discLog n := by linarith
  simpa only [Z.realPart_eq n] using hres

/-- The smallest explicit strip input plus the half-plane gives the paper's
zero-free region. -/
theorem toAboveBeta (K : Type*) [Field K] [NumberField K]
    (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (D : DedekindZetaStripDistanceInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_zetaStripInput_of_halfPlane K hK
    (D.toStripInput K) Z

/-- The smallest explicit strip input plus the half-plane gives the paper's
smallest zero-free bundle. -/
theorem toDedekindZeroFreeInput (K : Type*) [Field K] [NumberField K]
    (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (D : DedekindZetaStripDistanceInput K beta0 cz discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog where
  cz_pos := D.cz_pos
  above_beta := D.toAboveBeta K hK Z

/-- A literature strip estimate with a larger constant gives the paper's
constant. -/
theorem of_constant_le (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz cz' : ℝ} {discLog : ℕ → ℝ}
    (hcz_pos : 0 < cz) (hcz : cz ≤ cz')
    (D : DedekindZetaStripDistanceInput K beta0 cz' discLog) :
    DedekindZetaStripDistanceInput K beta0 cz discLog where
  cz_pos := hcz_pos
  discLog_pos := D.discLog_pos
  distance := stripDistance_of_le hcz D.distance

/-- Conversely, `DedekindZetaStripInput` with the positivity data gives the
smallest explicit strip input. -/
theorem ofStripInput (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hcz : 0 < cz) (hd : ∀ n, 0 < discLog n)
    (h : DedekindZetaStripInput K beta0 cz discLog) :
    DedekindZetaStripDistanceInput K beta0 cz discLog where
  cz_pos := hcz
  discLog_pos := hd
  distance := by
    intro n z hz hb hlt
    have hle : z.re ≤ 1 - cz / discLog n := h n z hz hb hlt
    have hdiv : cz / discLog n ≤ 1 - z.re := by linarith
    exact (div_le_iff₀ (hd n)).mp hdiv

end DedekindZetaStripDistanceInput

/-- **The smallest explicit strip input is exactly
`DedekindZetaStripInput`.**  The only additional data are the positivity
conditions that the paper-level statements already carry. -/
theorem dedekindZetaStripInput_iff_stripDistanceInput
    (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hcz : 0 < cz) (hd : ∀ n, 0 < discLog n) :
    DedekindZetaStripInput K beta0 cz discLog ↔
      DedekindZetaStripDistanceInput K beta0 cz discLog :=
  ⟨DedekindZetaStripDistanceInput.ofStripInput K hcz hd,
    fun D => D.toStripInput K⟩

/-- Under the half-plane, the classical input and the smallest explicit strip
input are equivalent. -/
theorem dedekindZetaClassicalInput_iff_stripDistanceInput_of_halfPlane
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} :
    DedekindZetaClassicalInput K beta0 cz discLog ↔
      DedekindZetaStripDistanceInput K beta0 cz discLog := by
  constructor
  · intro C
    exact C.toStripDistanceInput K
  · intro D
    exact
      { cz_pos := D.cz_pos
        discLog_pos := D.discLog_pos
        region := DedekindZetaClassicalRegion_of_stripInput_of_halfPlane K hK
          (D.toStripInput K) }

/-! ## 6. The scalar exact strip inequality -/

/-- **The division-free scalar strip inequality for one field.**  This is the
smallest explicit form of `DedekindZetaStripInequality`: no division and no
positivity conjunct beyond `log |Δ| > 0` when it is read as an inequality in
`ℝ`. -/
def DedekindZetaStripInequalityDistance (K : Type*) [Field K] [NumberField K]
    (beta0 cz discLog : ℝ) : Prop :=
  ∀ z : ℂ, NumberField.dedekindZeta K z = 0 →
    beta0 < z.re → z.re < 1 → cz ≤ (1 - z.re) * discLog

/-- The scalar strip inequality is exactly its division-free form. -/
theorem dedekindZetaStripInequality_iff_distance
    (K : Type*) [Field K] [NumberField K]
    {beta0 cz discLog : ℝ} (hd : 0 < discLog) :
    DedekindZetaStripInequality K beta0 cz discLog ↔
      DedekindZetaStripInequalityDistance K beta0 cz discLog := by
  constructor
  · intro h z hz hb hlt
    have hle : z.re ≤ 1 - cz / discLog := h z hz hb hlt
    have hdiv : cz / discLog ≤ 1 - z.re := by linarith
    exact (div_le_iff₀ hd).mp hdiv
  · intro h z hz hb hlt
    have hineq : cz ≤ (1 - z.re) * discLog := h z hz hb hlt
    have hdiv : cz / discLog ≤ 1 - z.re := (div_le_iff₀ hd).mpr hineq
    linarith

/-- The scalar classical region gives the scalar strip inequality. -/
theorem dedekindZetaStripInequality_of_classicalRegion
    (K : Type*) [Field K] [NumberField K]
    {beta0 cz discLog : ℝ}
    (h : ∀ z : ℂ, NumberField.dedekindZeta K z = 0 →
      beta0 < z.re → z.re ≤ 1 - cz / discLog) :
    DedekindZetaStripInequality K beta0 cz discLog :=
  fun z hz hb _ => h z hz hb

/-- **The scalar division-free inequality reduces to
`DedekindZetaStripInput`** when the parameters are constant sequences. -/
theorem dedekindZetaStripInput_of_inequalityDistance
    (K : Type*) [Field K] [NumberField K]
    {beta0 cz discLog : ℝ} {beta0Seq discLogSeq : ℕ → ℝ}
    (hβ : ∀ n, beta0Seq n = beta0) (hL : ∀ n, discLogSeq n = discLog)
    (hd : 0 < discLog)
    (h : DedekindZetaStripInequalityDistance K beta0 cz discLog) :
    DedekindZetaStripInput K beta0Seq cz discLogSeq :=
  dedekindZetaStripInput_of_inequality K hβ hL
    ((dedekindZetaStripInequality_iff_distance K hd).mpr h)

/-! ## 7. Riemann and Dirichlet instances -/

/-- The classical zero-free region for `riemannZeta`. -/
def RiemannZetaClassicalRegion (beta0 : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ZetaClassicalRegion riemannZeta beta0 cz discLog

/-- The strip region for `riemannZeta`. -/
def RiemannZetaStripRegion (beta0 : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ZetaStripRegion riemannZeta beta0 cz discLog

/-- The classical zero-free region for a Dirichlet `L`-function. -/
def DirichletLClassicalRegion {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  ZetaClassicalRegion (DirichletCharacter.LFunction χ) beta0 cz discLog

/-- The strip region for a Dirichlet `L`-function. -/
def DirichletLStripRegion {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  ZetaStripRegion (DirichletCharacter.LFunction χ) beta0 cz discLog

/-- The Riemann classical region gives the Riemann strip region. -/
theorem riemannZetaStripRegion_of_classicalRegion
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : RiemannZetaClassicalRegion beta0 cz discLog) :
    RiemannZetaStripRegion beta0 cz discLog :=
  stripRegion_of_classicalRegion h

/-- The Dirichlet classical region gives the Dirichlet strip region. -/
theorem dirichletLStripRegion_of_classicalRegion {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DirichletLClassicalRegion χ beta0 cz discLog) :
    DirichletLStripRegion χ beta0 cz discLog :=
  stripRegion_of_classicalRegion h

/-- **The Riemann classical region is vacuous for `β₀ ≥ 1`.**  Mathlib's
half-plane `riemannZeta_ne_zero_of_one_le_re` supplies it directly. -/
theorem riemannZetaClassicalRegion_of_one_le_beta0
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    RiemannZetaClassicalRegion beta0 cz discLog := by
  intro n z hz hb
  exact (riemannZeta_ne_zero_of_one_le_re (le_trans (hβ n) (le_of_lt hb)) hz).elim

/-- **The Dirichlet classical region is vacuous for `β₀ ≥ 1`** for every
nontrivial character, by Mathlib's half-plane
`DirichletCharacter.LFunction_ne_zero_of_one_le_re`. -/
theorem dirichletLClassicalRegion_of_one_le_beta0 {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    DirichletLClassicalRegion χ beta0 cz discLog := by
  intro n z hz hb
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ)
    (le_trans (hβ n) (le_of_lt hb)) hz).elim

/-- The character-modulo-`1` instance, where no trivial-character exception is
needed. -/
theorem dirichletL_modOneClassicalRegion_of_one_le_beta0
    (χ : DirichletCharacter ℂ 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    DirichletLClassicalRegion χ beta0 cz discLog := by
  intro n z hz hb
  exact (dirichletL_modOne_closedHalfPlane χ z
    (le_trans (hβ n) (le_of_lt hb)) hz).elim

/-- The Riemann strip region at `β₀ ≥ 1`, with no analytic input. -/
theorem riemannZetaStripRegion_of_one_le_beta0
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    RiemannZetaStripRegion beta0 cz discLog :=
  riemannZetaStripRegion_of_classicalRegion
    (riemannZetaClassicalRegion_of_one_le_beta0 hβ)

/-- The Dirichlet strip region at `β₀ ≥ 1`, with no analytic input. -/
theorem dirichletLStripRegion_of_one_le_beta0 {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    DirichletLStripRegion χ beta0 cz discLog :=
  dirichletLStripRegion_of_classicalRegion
    (dirichletLClassicalRegion_of_one_le_beta0 hχ hβ)

/-- The character-modulo-`1` strip region at `β₀ ≥ 1`. -/
theorem dirichletL_modOneStripRegion_of_one_le_beta0
    (χ : DirichletCharacter ℂ 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    DirichletLStripRegion χ beta0 cz discLog :=
  dirichletLStripRegion_of_classicalRegion
    (dirichletL_modOneClassicalRegion_of_one_le_beta0 χ hβ)

/-- **The Dedekind classical region is vacuous for `β₀ ≥ 1`** under the
half-plane hypothesis. -/
theorem dedekindZetaClassicalRegion_of_one_le_beta0
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    DedekindZetaClassicalRegion K beta0 cz discLog := by
  intro n z hz hb
  exact absurd hz (hK z (le_trans (hβ n) (le_of_lt hb)))

/-- `DedekindZetaStripInput` is vacuous for `β₀ ≥ 1` with no analytic input:
the open strip `β₀ < Re ρ < 1` is empty. -/
theorem dedekindZetaStripInput_of_one_le_beta0
    (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    DedekindZetaStripInput K beta0 cz discLog := by
  intro n z _ hb hlt
  linarith [hβ n, hb, hlt]

/-! ## 8. Factorization reductions for the Dedekind zeta function -/

/-- If `ζ_K` is a product of factors satisfying the strip region, then
`DedekindZetaStripInput` holds. -/
theorem DedekindZetaStripInput_of_factorization
    (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : ι → ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hfac : ∀ s : ℂ, NumberField.dedekindZeta K s = ∏ i, g i s)
    (hg : ∀ i, ZetaStripRegion (g i) beta0 cz discLog) :
    DedekindZetaStripInput K beta0 cz discLog :=
  stripRegion_of_prod hfac hg

/-- If `ζ_K` is a product of factors satisfying the classical region, then the
classical Dedekind region holds. -/
theorem DedekindZetaClassicalRegion_of_factorization
    (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : ι → ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hfac : ∀ s : ℂ, NumberField.dedekindZeta K s = ∏ i, g i s)
    (hg : ∀ i, ZetaClassicalRegion (g i) beta0 cz discLog) :
    DedekindZetaClassicalRegion K beta0 cz discLog :=
  classicalRegion_of_prod hfac hg

/-- If `ζ_K` is a product of factors with half-planes at `1`, then `ζ_K` has the
classical region for every `β₀ ≥ 1`.  This is the concrete form of the
Riemann/Dirichlet input that Mathlib actually provides. -/
theorem DedekindZetaClassicalRegion_of_factorization_of_one_le_beta0
    (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : ι → ℂ → ℂ}
    (hfac : ∀ s : ℂ, NumberField.dedekindZeta K s = ∏ i, g i s)
    (hg : ∀ i, ZeroFreeHalfPlane (g i) 1)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hβ : ∀ n, 1 ≤ beta0 n) :
    DedekindZetaClassicalRegion K beta0 cz discLog :=
  classicalRegion_of_prod_halfPlane_of_one_le_beta0 hfac hg hβ cz discLog

/-! ## 9. Composition with the paper-level analytic bundle -/

/-- **The classical Dedekind region plugs directly into
`DedekindAnalyticInputs`.**  The zero-free field is supplied by the classical
region, with no half-plane hypothesis; Stark, range and the Chebotarev count are
passed separately. -/
theorem dedekindAnalyticInputs_of_classicalDedekind
    (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {Kc C cZ : ℝ}
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (Cd : DedekindZetaClassicalInput K beta0 cz discLog)
    (hs : StarkBetaUpper beta0 F discLog)
    (hK : 0 < Kc)
    (hr : ChebotarevRangeThreshold Kc x degree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 Z.realPart cz discLog F Kc x degree C cZ count
      liX liBeta0 :=
  dedekindAnalyticInputs_of_zeroFree Cd.cz_pos (Cd.toAboveBeta K Z)
    hs hK hr hx hC hcZ hcheb

/-- **The smallest explicit strip input plugs into `DedekindAnalyticInputs`**
under the half-plane hypothesis. -/
theorem dedekindAnalyticInputs_of_stripDistanceDedekind
    (K : Type*) [Field K] [NumberField K] (hK : DedekindZetaHalfPlane K)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog F x degree count liX liBeta0 : ℕ → ℝ}
    {Kc C cZ : ℝ}
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (D : DedekindZetaStripDistanceInput K beta0 cz discLog)
    (hs : StarkBetaUpper beta0 F discLog)
    (hKc : 0 < Kc)
    (hr : ChebotarevRangeThreshold Kc x degree discLog)
    (hx : ∀ n, 0 < x n)
    (hC : 0 < C) (hcZ : 0 < cZ)
    (hcheb : ChebotarevSides count (mainOf liX liBeta0)
      (lagariasOdlyzkoError C cZ x degree)) :
    DedekindAnalyticInputs beta0 Z.realPart cz discLog F Kc x degree C cZ count
      liX liBeta0 :=
  dedekindAnalyticInputs_of_zeroFree D.cz_pos (D.toAboveBeta K hK Z)
    hs hKc hr hx hC hcZ hcheb

/-! ## Axiom audit -/

#print axioms classicalRegion_iff_distance
#print axioms stripRegion_iff_distance
#print axioms stripRegion_of_classicalRegion
#print axioms classicalRegion_of_stripRegion_of_halfPlane
#print axioms classicalRegion_iff_stripRegion_of_halfPlane
#print axioms classicalRegion_of_le
#print axioms classicalDistance_of_le
#print axioms stripRegion_of_le
#print axioms stripDistance_of_le
#print axioms stripRegion_of_prod
#print axioms classicalRegion_of_prod
#print axioms halfPlane_of_prod
#print axioms classicalRegion_of_prod_halfPlane_of_one_le_beta0
#print axioms DedekindZetaStripInput_of_classicalRegion
#print axioms DedekindZetaStripInput_of_classicalDistance
#print axioms DedekindZetaClassicalRegion_iff_stripInput_of_halfPlane
#print axioms DedekindZetaClassicalRegion_of_stripInput_of_halfPlane
#print axioms dedekindZetaStripInput_iff_stripDistance
#print axioms DedekindZetaClassicalInput.toAboveBeta
#print axioms DedekindZetaClassicalInput.toDedekindZeroFreeInput
#print axioms DedekindZetaClassicalInput.toStripInput
#print axioms DedekindZetaClassicalInput.toStripDistanceInput
#print axioms DedekindZetaClassicalInput.of_constant_le
#print axioms DedekindZetaStripDistanceInput.toStripInput
#print axioms DedekindZetaStripDistanceInput.toAboveBetaBelowOne
#print axioms DedekindZetaStripDistanceInput.toAboveBeta
#print axioms DedekindZetaStripDistanceInput.toDedekindZeroFreeInput
#print axioms DedekindZetaStripDistanceInput.of_constant_le
#print axioms DedekindZetaStripDistanceInput.ofStripInput
#print axioms dedekindZetaStripInput_iff_stripDistanceInput
#print axioms dedekindZetaClassicalInput_iff_stripDistanceInput_of_halfPlane
#print axioms dedekindZetaStripInequality_iff_distance
#print axioms dedekindZetaStripInequality_of_classicalRegion
#print axioms dedekindZetaStripInput_of_inequalityDistance
#print axioms riemannZetaStripRegion_of_classicalRegion
#print axioms dirichletLStripRegion_of_classicalRegion
#print axioms riemannZetaClassicalRegion_of_one_le_beta0
#print axioms dirichletLClassicalRegion_of_one_le_beta0
#print axioms dirichletL_modOneClassicalRegion_of_one_le_beta0
#print axioms riemannZetaStripRegion_of_one_le_beta0
#print axioms dirichletLStripRegion_of_one_le_beta0
#print axioms dirichletL_modOneStripRegion_of_one_le_beta0
#print axioms dedekindZetaClassicalRegion_of_one_le_beta0
#print axioms dedekindZetaStripInput_of_one_le_beta0
#print axioms DedekindZetaStripInput_of_factorization
#print axioms DedekindZetaClassicalRegion_of_factorization
#print axioms DedekindZetaClassicalRegion_of_factorization_of_one_le_beta0
#print axioms dedekindAnalyticInputs_of_classicalDedekind
#print axioms dedekindAnalyticInputs_of_stripDistanceDedekind

end

end Cogentic.RandomizedL34DedekindStrip
