import Cogentic.RandomizedL34DedekindStrip
import Cogentic.RandomizedL34ZeroFreeArithmetic
import Statements

/-!
# L34: the Dedekind zero-free input from GRH for Dirichlet `L`-functions

`Cogentic.RandomizedL34DedekindStrip` reduced the paper's Dedekind zero-free
input to the strip statement `DedekindZetaStripInput`, and proved that a
*product factorization* of `ζ_K` into factors with their own zero-free regions
transfers the region to `ζ_K`.  The factorization itself was left as a
hypothesis and no GRH-style input was connected to it.

This file supplies the missing connection.  The tree package states GRH for all
Dirichlet `L`-functions as `DirichletLZerosOnLine`:

```
∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
  0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2
```

and GRH for `ζ` as `RiemannZetaZerosOnLine`:

```
∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
  s ≠ 1 → s.re = 1 / 2
```

The two statements are *not* equivalent.  `DirichletLZerosOnLine` quantifies
over every Dirichlet character, including the principal one, and therefore
contains the Riemann zeta function through the unique character modulo `1`
(`DirichletCharacter.LFunction_modOne_eq`).  But it only speaks about zeros in
the **open critical strip**.  `RiemannZetaZerosOnLine` excludes the trivial
zeros and the (junk) point `1`, and then asks for `re = 1/2` for *every*
remaining zero, including zeros outside the critical strip.

## What this file proves

1. **The critical-strip half of `RiemannZetaZerosOnLine`.**  From
   `DirichletLZerosOnLine` one gets, with no extra input,

   * `riemannZeta_ne_zero_of_half_lt_re`: `ζ` has no zero with
     `1/2 < re s < 1`;
   * `riemannZeta_zeros_on_line_in_strip`: every zero of `ζ` with
     `0 < re s < 1` has `re s = 1/2`.

2. **The exact missing ingredient for `RiemannZetaZerosOnLine`.**  The only
   information `DirichletLZerosOnLine` lacks about `RiemannZetaZerosOnLine` is
   that every nontrivial zero of `ζ` has positive real part.  We isolate this
   as `RiemannNontrivialZerosPositiveRe` and prove the equivalence
   (`RiemannZetaZerosOnLine_iff_nontrivial_zeros_positiveRe`)

   `RiemannZetaZerosOnLine ↔ RiemannNontrivialZerosPositiveRe`

   *given* `DirichletLZerosOnLine`.  The forward implication is immediate
   (`re = 1/2 > 0`); the backward implication combines the strip statement with
   Mathlib's half-plane `riemannZeta_ne_zero_of_one_le_re`.  Thus the reduction
   from Dirichlet GRH to Riemann GRH is complete up to the classical fact that
   the nontrivial zeros of `ζ` lie in the critical strip.  That fact is not in
   Mathlib: proving it needs the functional equation together with
   `ζ(-(2k+1)) ≠ 0`, i.e. nonvanishing of the even Bernoulli numbers
   (`riemannZeta_neg_nat_eq_bernoulli`), which Mathlib does not currently
   provide.  We therefore state it as the explicit hypothesis
   `RiemannNontrivialZerosPositiveRe`, never as an axiom.

3. **The abelian factorization hypothesis.**  Mathlib has no Artin
   `L`-functions and no class-field-theoretic factorization of `ζ_K`.  The
   smallest hypothesis that the GRH route actually uses is
   `DedekindZetaFactorsIntoDirichletOffPole`: an explicit finite family of
   Dirichlet characters `χ i` modulo `N i` with

   `ζ_K s = ∏ i, L(s, χ i)`   for every `s ≠ 1`.

   Restricting to `s ≠ 1` is deliberate.  It is exactly the range in which the
   factorization is a statement about analytic functions rather than about the
   pole, and the strip `1/2 < re s < 1` is contained in it.  The full-strength
   version `DedekindZetaFactorsIntoDirichlet` (all `s`) is also provided, but
   the theorems only require the off-pole version.

4. **`DedekindZetaHalfPlane`.**  Off the point `1`, the half-plane follows from
   Mathlib's Dirichlet half-plane and the factorization alone (GRH is not
   needed): `DedekindZetaHalfPlaneOffOne_of_factorization`.  At `s = 1` the
   statement is not a theorem about zeros: `NumberField.dedekindZeta` is an
   `LSeries`, and `LSeries` assigns `0` to a defining series that is not
   summable (`dedekindZeta_one_eq_zero_of_not_LSeriesSummable`).  The value at
   `1` is therefore a junk value at the pole unless the defining series happens
   to be summable, and `not_DedekindZetaHalfPlane_of_dedekindZeta_one_eq_zero`
   records that the unpunctured half-plane fails whenever that value is `0`.
   We prove the exact decomposition

   `DedekindZetaHalfPlane K ↔
      DedekindZetaHalfPlaneOffOne K ∧ ζ_K 1 ≠ 0`

   (`DedekindZetaHalfPlane_iff_offOne_and_one_ne_zero`) and isolate the single
   extra hypothesis `ζ_K 1 ≠ 0` in
   `DedekindZetaHalfPlane_of_factorization_of_one_ne_zero`.  This is *not*
   derivable from GRH, which says nothing at `s = 1`.

   The full factorization at `s = 1` cannot repair this: both `ζ_K` and the
   product have a pole there, and the identity of meromorphic functions does
   not become a statement about the junk values that `LSeries` assigns at the
   pole.  This is why the factorization below is stated off the pole and the
   value at `1` is a separate hypothesis.

5. **`DedekindZetaStripInput`.**  GRH puts every zero in the open strip on
   `re = 1/2`, so once `β₀ ≥ 1/2` the strip `β₀ < re z < 1` is empty.  Hence

   * `DedekindZetaStripInput_of_GRH_of_factorization`:
     `DedekindZetaStripInput K β₀ cz discLog` for **every** `cz` and every
     `discLog`, provided `∀ n, 1/2 ≤ β₀ n`;
   * `DedekindZetaStripDistance_of_GRH_of_factorization` and
     `DedekindZetaStripInequalityDistance_of_GRH_of_factorization`: the same in
     the division-free scalar forms;
   * `DedekindZetaStripDistanceInput_of_GRH_of_factorization`: the packaged
     positivity-carrying input.

   No height bound and no positivity of `discLog` is required for the strip
   itself: the GRH route removes the height bookkeeping entirely.

6. **The paper's explicit `β₀`.**  `paperBeta0 F discLog n = 1 - 1/(4 F n log|Δ| n)`
   is at least `1/2` as soon as `4 F n log|Δ| n ≥ 2`.  We prove this pointwise
   (`half_le_paperBeta0_of_two_le`), the eventual version
   (`eventually_half_le_paperBeta0`) for a divergent product `F n * discLog n`,
   and the two paper-scale cases `log|Δ| = 0` and `log|Δ| ≥ log 2` with
   `F n ≥ 1` (`half_le_paperBeta0_of_discLog_eq_zero`,
   `half_le_paperBeta0_of_one_le_of_log_two_le`).  The strip input for
   `paperBeta0` is then
   `DedekindZetaStripInput_paperBeta0_of_GRH_of_factorization`, with the
   paper-scale variant
   `DedekindZetaStripInput_paperBeta0_of_GRH_of_factorization_of_one_le`.

   Because the paper's `β₀` only reaches `1/2` eventually, we also isolate the
   tail form `DedekindZetaStripInputFrom` and prove
   `exists_DedekindZetaStripInputFrom_paperBeta0_of_GRH_of_factorization`:
   if `4 F log|Δ|` diverges then GRH gives the strip input for all sufficiently
   large indices.  The finitely many initial indices are not covered by GRH at
   `1/2` and must come from a separate (classical) region;
   `DedekindZetaStripInput_of_from` records that a tail input plus the initial
   segment is exactly the full input.

7. **Zero sequences and the paper's `DedekindZeroFreeAboveBeta`.**
   `DedekindZetaStripInput` gives `DedekindZeroFreeAboveBetaBelowOne` for every
   zero sequence, with no half-plane and no height bound
   (`dedekindZeroFreeAboveBetaBelowOne_of_GRH_of_factorization`).  The
   unpunctured `DedekindZeroFreeAboveBeta` additionally needs the sequence to
   avoid the junk zero `1`; we prove it under `∀ n, Z.zero n ≠ 1`, and we show
   in `not_dedekindZeroFreeAboveBeta_of_zero_eq_one` that this avoidance is not
   removable when `cz > 0`.

## What a Mathlib factorization theorem would need

A theorem producing `DedekindZetaFactorsIntoDirichletOffPole K` from the
hypothesis that `K` is abelian over `ℚ` would need:

* a definition of the abelian Galois group `Gal(K/ℚ)` and of its character
  group `Ĝ` (Mathlib has `K ≃ₐ[ℚ] K` and `DirichletCharacter`, but not the
  character group of a number field);
* Kronecker–Weber / class field theory identifying each `χ : Ĝ` with a
  primitive Dirichlet character of conductor dividing the conductor of `K`,
  including the trivial character;
* the Euler-product identity `ζ_K(s) = ∏_{χ ∈ Ĝ} L(s, χ)` for `re s > 1`,
  extended meromorphically to `s ≠ 1`;
* the matching of the local factors at the ramified primes.

None of these are available in the current Mathlib or in this repository, so
the factorization remains an explicit hypothesis.  The reductions below are
conditional on it and do not assert it.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  GRH is never
asserted: `DirichletLZerosOnLine` is always a hypothesis, and the statements
that cannot be derived from it are isolated as `Prop`-valued definitions.
-/

namespace Cogentic.RandomizedL34DedekindGRH

open Filter Real
open NumberField
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34BelowOne
open Cogentic.RandomizedL34ClassicalRegion
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34ZeroFreeArithmetic

noncomputable section

/-! ## 1. Reading the two tree-package statements -/

/-- The exact fields of `DirichletLZerosOnLine`, exposed as an application
lemma.  Every Dirichlet character is allowed, including the principal one, and
the zero is an arbitrary point of the open critical strip. -/
theorem dirichletLZerosOnLine_apply (h : DirichletLZerosOnLine)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) : s.re = 1 / 2 :=
  h N χ s h0 h1 hz

/-- The exact fields of `RiemannZetaZerosOnLine`, exposed as an application
lemma.  The trivial zeros `-2(n+1)` and the junk point `1` are excluded; every
other zero is required to lie on `re = 1/2`. -/
theorem riemannZetaZerosOnLine_apply (h : RiemannZetaZerosOnLine) {s : ℂ}
    (hz : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (h1 : s ≠ 1) : s.re = 1 / 2 :=
  h s hz htriv h1

/-- The unique Dirichlet character modulo `1` is the principal character and
its `L`-function is `riemannZeta`. -/
theorem lFunction_one_eq_riemannZeta (s : ℂ) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s := by
  simp

/-! ## 2. From Dirichlet GRH to zeta on the critical line -/

/-- **GRH excludes zeros of a Dirichlet `L`-function in `1/2 < re s < 1`.** -/
theorem dirichletL_ne_zero_of_half_lt_re (hGRH : DirichletLZerosOnLine)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h1 : 1 / 2 < s.re) (h2 : s.re < 1) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hz
  have hline := hGRH N χ s (by linarith) h2 hz
  linarith

/-- **GRH excludes zeros of `ζ` in `1/2 < re s < 1`.**  This is the modulo-`1`
instance of the preceding lemma. -/
theorem riemannZeta_ne_zero_of_half_lt_re (hGRH : DirichletLZerosOnLine)
    {s : ℂ} (h1 : 1 / 2 < s.re) (h2 : s.re < 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hz' :
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
    simpa using hz
  exact dirichletL_ne_zero_of_half_lt_re hGRH (1 : DirichletCharacter ℂ 1) h1 h2 hz'

/-- **GRH for `ζ` inside the critical strip.**  Every zero of `ζ` with
`0 < re s < 1` has real part `1/2`. -/
theorem riemannZeta_zeros_on_line_in_strip (hGRH : DirichletLZerosOnLine)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    s.re = 1 / 2 := by
  have hz' :
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
    simpa using hz
  exact dirichletLZerosOnLine_apply hGRH (1 : DirichletCharacter ℂ 1) h0 h1 hz'

/-- **The one statement that `DirichletLZerosOnLine` does not supply about
`RiemannZetaZerosOnLine`:** every nontrivial zero of `ζ` has positive real
part.

This is the standard fact that all zeros outside the critical strip are the
trivial zeros `-2(n+1)`.  In Mathlib it is not available: the functional
equation `riemannZeta_one_sub` gives it immediately for zeros that are not
nonpositive integers, but at the negative odd integers one additionally needs
`ζ(-(2k+1)) ≠ 0`, i.e. nonvanishing of the even Bernoulli numbers via
`riemannZeta_neg_nat_eq_bernoulli`.  We keep it as an explicit `def`, never an
axiom. -/
def RiemannNontrivialZerosPositiveRe : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 →
    (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → 0 < s.re

/-- Under `DirichletLZerosOnLine`, the whole of `RiemannZetaZerosOnLine` is
equivalent to the single missing fact `RiemannNontrivialZerosPositiveRe`. -/
theorem RiemannZetaZerosOnLine_iff_nontrivial_zeros_positiveRe
    (hGRH : DirichletLZerosOnLine) :
    RiemannZetaZerosOnLine ↔ RiemannNontrivialZerosPositiveRe := by
  constructor
  · intro hRH s hz htriv hs1
    rw [hRH s hz htriv hs1]
    norm_num
  · intro hpos s hz htriv hs1
    have hpos' : 0 < s.re := hpos s hz htriv hs1
    by_cases hlt : s.re < 1
    · exact riemannZeta_zeros_on_line_in_strip hGRH hpos' hlt hz
    · have hge : 1 ≤ s.re := le_of_not_gt hlt
      exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge)

/-- **`DirichletLZerosOnLine` implies `RiemannZetaZerosOnLine`, provided the
nontrivial zeros of `ζ` are known to have positive real part.**  This is the
full reduction permitted by the definitions; see
`RiemannZetaZerosOnLine_iff_nontrivial_zeros_positiveRe` for the exactness of
the extra hypothesis. -/
theorem RiemannZetaZerosOnLine_of_DirichletLZerosOnLine
    (hGRH : DirichletLZerosOnLine) (hpos : RiemannNontrivialZerosPositiveRe) :
    RiemannZetaZerosOnLine :=
  (RiemannZetaZerosOnLine_iff_nontrivial_zeros_positiveRe hGRH).mpr hpos

/-! ## 3. The abelian factorization of the Dedekind zeta function -/

/-- **The smallest factorization hypothesis used by the GRH route.**

`K` has a finite family of Dirichlet characters `χ i` modulo `N i` such that,
away from the pole `s = 1`,

`ζ_K s = ∏ i, L(s, χ i)`.

For an abelian number field this is the standard factorization of `ζ_K` into
the Dirichlet `L`-functions of the characters of `Gal(K/ℚ)`.  The index type,
the moduli and the characters are explicit parameters, so the statement does
not rely on any nonexistent Mathlib class-field-theory API.  Restricting to
`s ≠ 1` is exactly the range needed by GRH; the critical strip is contained in
it. -/
def DedekindZetaFactorsIntoDirichletOffPole
    (K : Type*) [Field K] [NumberField K]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) : Prop :=
  ∀ s : ℂ, s ≠ 1 →
    NumberField.dedekindZeta K s = ∏ i, DirichletCharacter.LFunction (χ i) s

/-- **The full-strength factorization**, including the value at `s = 1`.

The theorems below only need the off-pole version.  The full version is
recorded for completeness and reduces to the off-pole one by
`DedekindZetaFactorsIntoDirichlet.toOffPole`. -/
def DedekindZetaFactorsIntoDirichlet
    (K : Type*) [Field K] [NumberField K]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) : Prop :=
  ∀ s : ℂ,
    NumberField.dedekindZeta K s = ∏ i, DirichletCharacter.LFunction (χ i) s

/-- The full factorization implies the off-pole factorization. -/
theorem DedekindZetaFactorsIntoDirichlet.toOffPole
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (h : DedekindZetaFactorsIntoDirichlet K ι N χ) :
    DedekindZetaFactorsIntoDirichletOffPole K ι N χ :=
  fun s _ => h s

/-- **A zero of `ζ_K` is a zero of at least one factor**, away from the pole. -/
theorem dedekindZeta_eq_zero_iff_exists_LFunction_eq_zero
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {s : ℂ} (hs1 : s ≠ 1) :
    NumberField.dedekindZeta K s = 0 ↔
      ∃ i, DirichletCharacter.LFunction (χ i) s = 0 := by
  rw [hfac s hs1]
  simpa using
    (Finset.prod_eq_zero_iff (s := (Finset.univ : Finset ι))
      (f := fun i => DirichletCharacter.LFunction (χ i) s))

/-- If no factor vanishes at `s`, then `ζ_K` does not vanish at `s`. -/
theorem dedekindZeta_ne_zero_of_factor_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {s : ℂ} (hs1 : s ≠ 1)
    (h : ∀ i, DirichletCharacter.LFunction (χ i) s ≠ 0) :
    NumberField.dedekindZeta K s ≠ 0 := by
  intro hz
  rw [hfac s hs1] at hz
  obtain ⟨i, -, hi⟩ :=
    (Finset.prod_eq_zero_iff (s := (Finset.univ : Finset ι))
      (f := fun i => DirichletCharacter.LFunction (χ i) s)).mp hz
  exact h i hi

/-! ## 4. GRH consequences for the Dedekind zeta function -/

/-- **GRH puts the strip zeros of `ζ_K` on `re = 1/2`.**  Equivalently, `ζ_K`
has no zero with `1/2 < re z < 1`, once `ζ_K` is a product of Dirichlet
`L`-functions. -/
theorem dedekindZeta_ne_zero_of_half_lt_re_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {s : ℂ} (hs1 : s ≠ 1) (h1 : 1 / 2 < s.re) (h2 : s.re < 1) :
    NumberField.dedekindZeta K s ≠ 0 :=
  dedekindZeta_ne_zero_of_factor_ne_zero hfac hs1 fun i =>
    dirichletL_ne_zero_of_half_lt_re hGRH (χ i) h1 h2

/-- **The half-plane at `1`, punctured at the pole.**  This part does not need
GRH: Mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re` and the
factorization suffice, because the only exceptional factor value is the
trivial character at `s = 1`, which is excluded. -/
theorem dedekindZeta_ne_zero_of_one_le_re_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {s : ℂ} (hs1 : s ≠ 1) (h1 : 1 ≤ s.re) :
    NumberField.dedekindZeta K s ≠ 0 :=
  dedekindZeta_ne_zero_of_factor_ne_zero hfac hs1 fun i =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ i) (Or.inr hs1) h1

/-- **The junk mechanism at the pole, exposed.**  `NumberField.dedekindZeta`
is defined as an `LSeries`; if its defining coefficient series is not summable
at `1` (the expected case, since the Dedekind zeta has a simple pole there),
then `LSeries` assigns the junk value `0`. -/
theorem dedekindZeta_one_eq_zero_of_not_LSeriesSummable
    (K : Type*) [Field K] [NumberField K]
    (h : ¬ LSeriesSummable
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 1) :
    NumberField.dedekindZeta K 1 = 0 :=
  LSeries.eq_zero_of_not_LSeriesSummable _ _ h

/-- **Consequently the unpunctured half-plane fails at the junk point.**  Any
proof of `DedekindZetaHalfPlane K` must establish `ζ_K 1 ≠ 0`; this is not a
zero-free statement and is not supplied by GRH. -/
theorem not_DedekindZetaHalfPlane_of_dedekindZeta_one_eq_zero
    (K : Type*) [Field K] [NumberField K]
    (h : NumberField.dedekindZeta K 1 = 0) : ¬ DedekindZetaHalfPlane K :=
  fun hH => hH 1 le_rfl h

/-- **The Dedekind half-plane with the pole at `1` removed.** -/
def DedekindZetaHalfPlaneOffOne (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ s : ℂ, 1 ≤ s.re → s ≠ 1 → NumberField.dedekindZeta K s ≠ 0

/-- **The punctured Dedekind half-plane follows from the factorization alone.** -/
theorem DedekindZetaHalfPlaneOffOne_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ) :
    DedekindZetaHalfPlaneOffOne K :=
  fun _s hs hs1 => dedekindZeta_ne_zero_of_one_le_re_of_factorization hfac hs1 hs

/-- **The exact content of the unpunctured Dedekind half-plane.**  It is the
punctured half-plane together with nonvanishing at the junk point `1`. -/
theorem DedekindZetaHalfPlane_iff_offOne_and_one_ne_zero
    (K : Type*) [Field K] [NumberField K] :
    DedekindZetaHalfPlane K ↔
      DedekindZetaHalfPlaneOffOne K ∧ NumberField.dedekindZeta K 1 ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun s hs _ => h s hs, h 1 le_rfl⟩
  · rintro ⟨h, h1⟩ s hs
    by_cases hs1 : s = 1
    · subst hs1
      exact h1
    · exact h s hs hs1

/-- **`DedekindZetaHalfPlane` from the factorization, with the single extra
hypothesis `ζ_K 1 ≠ 0`.**

The extra hypothesis is unavoidable in the available formal model:
`NumberField.dedekindZeta` is an `LSeries`, and if its defining series is not
summable at `1` (the expected case at the pole) then `LSeries` gives the junk
value `0`.  GRH says nothing about `s = 1`, so the unpunctured half-plane can
only be obtained from this extra nonvanishing. -/
theorem DedekindZetaHalfPlane_of_factorization_of_one_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0) :
    DedekindZetaHalfPlane K :=
  (DedekindZetaHalfPlane_iff_offOne_and_one_ne_zero K).mpr
    ⟨DedekindZetaHalfPlaneOffOne_of_factorization hfac, h1⟩

/-- The same statement with `DirichletLZerosOnLine` in the hypothesis list, to
record that GRH is not what supplies the unpunctured half-plane. -/
theorem DedekindZetaHalfPlane_of_GRH_of_factorization_of_one_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (_hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0) :
    DedekindZetaHalfPlane K :=
  DedekindZetaHalfPlane_of_factorization_of_one_ne_zero hfac h1

/-! ## 5. The strip input from GRH -/

/-- **GRH implies the Dedekind strip input whenever `β₀ ≥ 1/2`.**

For every `cz` and every `discLog`, the open strip
`β₀ n < Re z < 1` contains no zero of `ζ_K`, so the inequality
`Re z ≤ 1 - cz / discLog n` is vacuous.  No height bound and no positivity of
`discLog` is needed. -/
theorem DedekindZetaStripInput_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZetaStripInput K beta0 cz discLog := by
  intro n z hz hb hlt
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hlt
    norm_num at hlt
  have hhalf : 1 / 2 < z.re := lt_of_le_of_lt (hβ n) hb
  exact absurd hz
    (dedekindZeta_ne_zero_of_half_lt_re_of_factorization hGRH hfac hz1 hhalf hlt)

/-- **The division-free strip input from GRH**, again with no height or
positivity hypotheses. -/
theorem DedekindZetaStripDistance_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZetaStripDistance K beta0 cz discLog := by
  intro n z hz hb hlt
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hlt
    norm_num at hlt
  have hhalf : 1 / 2 < z.re := lt_of_le_of_lt (hβ n) hb
  exact absurd hz
    (dedekindZeta_ne_zero_of_half_lt_re_of_factorization hGRH hfac hz1 hhalf hlt)

/-- **The scalar division-free strip inequality from GRH.** -/
theorem DedekindZetaStripInequalityDistance_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 cz discLog : ℝ} (hβ : 1 / 2 ≤ beta0) :
    DedekindZetaStripInequalityDistance K beta0 cz discLog := by
  intro z hz hb hlt
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hlt
    norm_num at hlt
  have hhalf : 1 / 2 < z.re := lt_of_le_of_lt hβ hb
  exact absurd hz
    (dedekindZeta_ne_zero_of_half_lt_re_of_factorization hGRH hfac hz1 hhalf hlt)

/-- **The scalar strip inequality from GRH**, in the division form. -/
theorem DedekindZetaStripInequality_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 cz discLog : ℝ} (hβ : 1 / 2 ≤ beta0) (hd : 0 < discLog) :
    DedekindZetaStripInequality K beta0 cz discLog :=
  (dedekindZetaStripInequality_iff_distance K hd).mpr
    (DedekindZetaStripInequalityDistance_of_GRH_of_factorization hGRH hfac hβ)

/-- **The packaged strip-distance input from GRH.**  Positivity of `cz` and of
`discLog` is supplied separately; the analytic distance inequality is vacuous. -/
theorem DedekindZetaStripDistanceInput_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} (hcz : 0 < cz) {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n) :
    DedekindZetaStripDistanceInput K beta0 cz discLog :=
  DedekindZetaStripDistanceInput.ofStripInput K hcz hd
    (DedekindZetaStripInput_of_GRH_of_factorization hGRH hfac hβ cz discLog)

/-- **The strip input restricted to a tail of indices.**  This is the form in
which the eventual arithmetic of `paperBeta0` can be consumed: GRH controls
every index `n ≥ N₀` once `β₀ n ≥ 1/2` there. -/
def DedekindZetaStripInputFrom (K : Type*) [Field K] [NumberField K]
    (N₀ : ℕ) (beta0 : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ) : Prop :=
  ∀ n, N₀ ≤ n → ∀ z : ℂ, NumberField.dedekindZeta K z = 0 →
    beta0 n < z.re → z.re < 1 → z.re ≤ 1 - cz / discLog n

/-- **GRH gives the tail strip input** when `β₀ ≥ 1/2` on the tail. -/
theorem DedekindZetaStripInputFrom_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {N₀ : ℕ} {beta0 : ℕ → ℝ} (hβ : ∀ n, N₀ ≤ n → 1 / 2 ≤ beta0 n)
    (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZetaStripInputFrom K N₀ beta0 cz discLog := by
  intro n hn z hz hb hlt
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hlt
    norm_num at hlt
  have hhalf : 1 / 2 < z.re := lt_of_le_of_lt (hβ n hn) hb
  exact absurd hz
    (dedekindZeta_ne_zero_of_half_lt_re_of_factorization hGRH hfac hz1 hhalf hlt)

/-- **A tail strip input plus the finitely many initial indices gives the full
strip input.** -/
theorem DedekindZetaStripInput_of_from
    {K : Type*} [Field K] [NumberField K]
    {N₀ : ℕ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hfrom : DedekindZetaStripInputFrom K N₀ beta0 cz discLog)
    (hbefore : ∀ n, n < N₀ → ∀ z : ℂ, NumberField.dedekindZeta K z = 0 →
      beta0 n < z.re → z.re < 1 → z.re ≤ 1 - cz / discLog n) :
    DedekindZetaStripInput K beta0 cz discLog := by
  intro n z hz hb hlt
  by_cases hn : n < N₀
  · exact hbefore n hn z hz hb hlt
  · exact hfrom n (le_of_not_gt hn) z hz hb hlt

/-! ## 6. The classical region, and the point `s = 1` -/

/-- **GRH gives the classical Dedekind region for `β₀ ≥ 1/2`**, provided the
junk point `1` is not a zero.  Above `β₀` there are no zeros at all: the strip
is empty by GRH and the half-plane is Mathlib's Dirichlet estimate. -/
theorem DedekindZetaClassicalRegion_of_GRH_of_factorization_of_one_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    (cz : ℝ) (discLog : ℕ → ℝ) :
    DedekindZetaClassicalRegion K beta0 cz discLog := by
  intro n z hz hb
  exfalso
  by_cases hz1 : z = 1
  · exact h1 (by simpa [hz1] using hz)
  · by_cases hlt : z.re < 1
    · have hhalf : 1 / 2 < z.re := lt_of_le_of_lt (hβ n) hb
      exact dedekindZeta_ne_zero_of_half_lt_re_of_factorization hGRH hfac hz1 hhalf
        hlt hz
    · have hge : 1 ≤ z.re := le_of_not_gt hlt
      exact dedekindZeta_ne_zero_of_one_le_re_of_factorization hfac hz1 hge hz

/-- **The packaged classical input from GRH.** -/
theorem DedekindZetaClassicalInput_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} (hcz : 0 < cz) {discLog : ℕ → ℝ}
    (hd : ∀ n, 0 < discLog n) :
    DedekindZetaClassicalInput K beta0 cz discLog where
  cz_pos := hcz
  discLog_pos := hd
  region :=
    DedekindZetaClassicalRegion_of_GRH_of_factorization_of_one_ne_zero hGRH hfac h1
      hβ cz discLog

/-! ## 7. The explicit `paperBeta0` arithmetic -/

/-- **`paperBeta0` is at least `1/2` once `4 F log|Δ| ≥ 2`.** -/
theorem half_le_paperBeta0_of_two_le {F discLog : ℕ → ℝ} {n : ℕ}
    (h : 2 ≤ 4 * F n * discLog n) :
    1 / 2 ≤ paperBeta0 F discLog n := by
  have hden : 0 < 4 * F n * discLog n := lt_of_lt_of_le (by norm_num) h
  have hq : 1 / (4 * F n * discLog n) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  unfold paperBeta0
  linarith

/-- **`paperBeta0 = 1` when `log|Δ| = 0`.**  This covers the rational field,
where the discriminant is `1`; the Lean value `1 / 0 = 0` makes `paperBeta0`
equal to `1`, which is certainly at least `1/2`. -/
theorem half_le_paperBeta0_of_discLog_eq_zero {F discLog : ℕ → ℝ} {n : ℕ}
    (h : discLog n = 0) : 1 / 2 ≤ paperBeta0 F discLog n := by
  unfold paperBeta0
  rw [h]
  norm_num

/-- **`paperBeta0 ≥ 1/2` from the paper's factorial scale.**  If `F n ≥ 1`
and `log|Δ| n ≥ log 2`, then `4 F n log|Δ| n ≥ 4 log 2 > 2`.  Together with
`half_le_paperBeta0_of_discLog_eq_zero`, this covers the two cases
`log|Δ| = 0` and `log|Δ| ≥ log 2` of an integer discriminant. -/
theorem half_le_paperBeta0_of_one_le_of_log_two_le {F discLog : ℕ → ℝ} {n : ℕ}
    (hF : 1 ≤ F n) (hD : Real.log 2 ≤ discLog n) :
    1 / 2 ≤ paperBeta0 F discLog n := by
  apply half_le_paperBeta0_of_two_le
  have hlog2 : (2 : ℝ) ≤ 4 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hprod : Real.log 2 ≤ F n * discLog n := by
    calc Real.log 2 = 1 * Real.log 2 := by ring
      _ ≤ F n * discLog n :=
        mul_le_mul hF hD (le_of_lt hlog2pos) (by linarith)
  nlinarith

/-- **Eventually `paperBeta0 ≥ 1/2`** whenever `4 F log|Δ|` diverges. -/
theorem eventually_half_le_paperBeta0 {F discLog : ℕ → ℝ}
    (h : Tendsto (fun n => 4 * F n * discLog n) atTop atTop) :
    ∀ᶠ n in atTop, 1 / 2 ≤ paperBeta0 F discLog n := by
  filter_upwards [h.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
  exact half_le_paperBeta0_of_two_le hn

/-- **The `paperBeta0` tail input from GRH and the eventual lower bound.**
If `4 F log|Δ|` diverges, then `paperBeta0 ≥ 1/2` eventually, and GRH gives the
strip input from some index on.  This is the exact way in which the paper's
`β₀` "exceeds `1/2` eventually". -/
theorem exists_DedekindZetaStripInputFrom_paperBeta0_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {F discLog : ℕ → ℝ}
    (hdiv : Tendsto (fun n => 4 * F n * discLog n) atTop atTop)
    (cz : ℝ) :
    ∃ N₀, DedekindZetaStripInputFrom K N₀ (paperBeta0 F discLog) cz discLog := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.mp (eventually_half_le_paperBeta0 hdiv)
  exact
    ⟨N₀,
      DedekindZetaStripInputFrom_of_GRH_of_factorization hGRH hfac hN₀ cz discLog⟩

/-- **The strip input for the paper's `β₀` from GRH.**  The condition is the
pointwise form `4 F n log|Δ| n ≥ 2`, exactly the arithmetic needed for
`paperBeta0 n ≥ 1/2`. -/
theorem DedekindZetaStripInput_paperBeta0_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {F discLog : ℕ → ℝ}
    (hβ : ∀ n, 2 ≤ 4 * F n * discLog n)
    (cz : ℝ) :
    DedekindZetaStripInput K (paperBeta0 F discLog) cz discLog :=
  DedekindZetaStripInput_of_GRH_of_factorization hGRH hfac
    (fun n => half_le_paperBeta0_of_two_le (hβ n)) cz discLog

/-- **The strip input for `paperBeta0` at the paper's factorial scale.**

`F n ≥ 1` (a factorial) and `log|Δ| n` is either `0` (the field `ℚ`) or at
least `log 2` (an integer discriminant of absolute value at least `2`).  Then
`paperBeta0 n ≥ 1/2` for every `n`, so GRH gives the full strip input. -/
theorem DedekindZetaStripInput_paperBeta0_of_GRH_of_factorization_of_one_le
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {F discLog : ℕ → ℝ}
    (hF : ∀ n, 1 ≤ F n)
    (hD : ∀ n, discLog n = 0 ∨ Real.log 2 ≤ discLog n)
    (cz : ℝ) :
    DedekindZetaStripInput K (paperBeta0 F discLog) cz discLog :=
  DedekindZetaStripInput_of_GRH_of_factorization hGRH hfac
    (fun n =>
      (hD n).elim
        (fun h => half_le_paperBeta0_of_discLog_eq_zero
          (F := F) (discLog := discLog) h)
        (fun h => half_le_paperBeta0_of_one_le_of_log_two_le
          (F := F) (discLog := discLog) (hF n) h))
    cz discLog

/-- **The division-free strip-distance input for `paperBeta0` from GRH.** -/
theorem DedekindZetaStripDistanceInput_paperBeta0_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {F discLog : ℕ → ℝ}
    (hβ : ∀ n, 2 ≤ 4 * F n * discLog n)
    {cz : ℝ} (hcz : 0 < cz) (hd : ∀ n, 0 < discLog n) :
    DedekindZetaStripDistanceInput K (paperBeta0 F discLog) cz discLog :=
  DedekindZetaStripDistanceInput_of_GRH_of_factorization hGRH hfac
    (fun n => half_le_paperBeta0_of_two_le (hβ n)) hcz hd

/-- **The classical input for `paperBeta0` from GRH**, still conditional on the
nonvanishing at the pole `ζ_K 1 ≠ 0`. -/
theorem DedekindZetaClassicalInput_paperBeta0_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {F discLog : ℕ → ℝ}
    (hβ : ∀ n, 2 ≤ 4 * F n * discLog n)
    {cz : ℝ} (hcz : 0 < cz) (hd : ∀ n, 0 < discLog n) :
    DedekindZetaClassicalInput K (paperBeta0 F discLog) cz discLog :=
  DedekindZetaClassicalInput_of_GRH_of_factorization hGRH hfac h1
    (fun n => half_le_paperBeta0_of_two_le (hβ n)) hcz hd

/-! ## 8. Zero sequence bookkeeping -/

/-- **The residual strip statement for any zero sequence, with no half-plane
and no height bound.**  This is the zero-sequence form of
`DedekindZetaStripInput`. -/
theorem dedekindZeroFreeAboveBetaBelowOne_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBetaBelowOne beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBetaBelowOne_of_zetaStripInput K
    (DedekindZetaStripInput_of_GRH_of_factorization hGRH hfac hβ cz discLog) Z

/-- **The unpunctured zero sequence statement**, under the necessary avoidance
of the junk zero `1`.  The half-plane is supplied by the factorization alone. -/
theorem dedekindZeroFreeAboveBeta_of_GRH_of_factorization_of_ne_one
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (hZ1 : ∀ n, Z.zero n ≠ 1) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog := by
  intro n hb
  by_cases hlt : Z.realPart n < 1
  · exact
      dedekindZeroFreeAboveBetaBelowOne_of_GRH_of_factorization hGRH hfac hβ Z n hb
        hlt
  · have hge : 1 ≤ Z.realPart n := le_of_not_gt hlt
    rw [Z.realPart_eq n] at hge
    exact absurd (Z.isZero n)
      (dedekindZeta_ne_zero_of_one_le_re_of_factorization hfac (hZ1 n) hge)

/-- **The paper's smallest zero-free bundle from GRH**, for a zero sequence
avoiding the junk zero `1`. -/
theorem dedekindZeroFreeInput_of_GRH_of_factorization_of_ne_one
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} (hcz : 0 < cz) {discLog : ℕ → ℝ}
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (hZ1 : ∀ n, Z.zero n ≠ 1) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog where
  cz_pos := hcz
  above_beta :=
    dedekindZeroFreeAboveBeta_of_GRH_of_factorization_of_ne_one hGRH hfac hβ Z hZ1

/-- **The paper's `paperBeta0` zero-free region from GRH**, for a zero sequence
avoiding `1`. -/
theorem dedekindZeroFreeAboveBeta_paperBeta0_of_GRH_of_factorization_of_ne_one
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {F discLog : ℕ → ℝ}
    (hβ : ∀ n, 2 ≤ 4 * F n * discLog n)
    {cz : ℝ} (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (hZ1 : ∀ n, Z.zero n ≠ 1) :
    DedekindZeroFreeAboveBeta (paperBeta0 F discLog) Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_GRH_of_factorization_of_ne_one hGRH hfac
    (fun n => half_le_paperBeta0_of_two_le (hβ n)) Z hZ1

/-- **The paper's `paperBeta0` zero-free bundle from GRH**, for a zero sequence
avoiding `1`. -/
theorem dedekindZeroFreeInput_paperBeta0_of_GRH_of_factorization_of_ne_one
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {F discLog : ℕ → ℝ}
    (hβ : ∀ n, 2 ≤ 4 * F n * discLog n)
    {cz : ℝ} (hcz : 0 < cz)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K))
    (hZ1 : ∀ n, Z.zero n ≠ 1) :
    DedekindZeroFreeInput (paperBeta0 F discLog) Z.realPart cz discLog where
  cz_pos := hcz
  above_beta :=
    dedekindZeroFreeAboveBeta_paperBeta0_of_GRH_of_factorization_of_ne_one
      hGRH hfac hβ Z hZ1

/-- **The paper-level zero-free statement for every zero sequence**, under the
extra nonvanishing `ζ_K 1 ≠ 0` that makes the unpunctured half-plane available.
No avoidance hypothesis on the sequence is needed. -/
theorem dedekindZeroFreeAboveBeta_of_GRH_of_factorization_of_one_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_zetaStripInput_of_halfPlane K
    (DedekindZetaHalfPlane_of_factorization_of_one_ne_zero hfac h1)
    (DedekindZetaStripInput_of_GRH_of_factorization hGRH hfac hβ cz discLog) Z

/-- **The paper's `paperBeta0` zero-free statement for every zero sequence**,
under `ζ_K 1 ≠ 0`. -/
theorem dedekindZeroFreeAboveBeta_paperBeta0_of_GRH_of_factorization_of_one_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {F discLog : ℕ → ℝ}
    (hβ : ∀ n, 2 ≤ 4 * F n * discLog n)
    {cz : ℝ} (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBeta (paperBeta0 F discLog) Z.realPart cz discLog :=
  dedekindZeroFreeAboveBeta_of_GRH_of_factorization_of_one_ne_zero hGRH hfac h1
    (fun n => half_le_paperBeta0_of_two_le (hβ n)) Z

/-- **The paper's `paperBeta0` zero-free bundle for every zero sequence**,
under `ζ_K 1 ≠ 0`. -/
theorem dedekindZeroFreeInput_paperBeta0_of_GRH_of_factorization_of_one_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {F discLog : ℕ → ℝ}
    (hβ : ∀ n, 2 ≤ 4 * F n * discLog n)
    {cz : ℝ} (hcz : 0 < cz)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput (paperBeta0 F discLog) Z.realPart cz discLog where
  cz_pos := hcz
  above_beta :=
    dedekindZeroFreeAboveBeta_paperBeta0_of_GRH_of_factorization_of_one_ne_zero
      hGRH hfac h1 hβ Z

/-- **The avoidance of `1` is not removable** when `cz > 0`: a zero sequence
containing the junk zero `1`, with `β₀ n < 1`, violates the paper's zero-free
statement at that index.  This is why the unpunctured statements above carry
either `ζ_K 1 ≠ 0` or `∀ n, Z.zero n ≠ 1`. -/
theorem not_dedekindZeroFreeAboveBeta_of_zero_eq_one
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} {n : ℕ}
    (h1 : Z.zero n = 1) (hβ : beta0 n < 1) (hcz : 0 < cz) (hd : 0 < discLog n) :
    ¬ DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog := by
  intro h
  have hb : beta0 n < Z.realPart n := by
    rw [Z.realPart_eq n, h1]
    simpa using hβ
  have hle := h n hb
  rw [Z.realPart_eq n, h1] at hle
  have hle' : (1 : ℝ) ≤ 1 - cz / discLog n := by simpa using hle
  have hgt : 1 - cz / discLog n < 1 := by
    have : 0 < cz / discLog n := div_pos hcz hd
    linarith
  linarith

/-! ## Axiom audit -/

#print axioms dirichletLZerosOnLine_apply
#print axioms riemannZetaZerosOnLine_apply
#print axioms lFunction_one_eq_riemannZeta
#print axioms dirichletL_ne_zero_of_half_lt_re
#print axioms riemannZeta_ne_zero_of_half_lt_re
#print axioms riemannZeta_zeros_on_line_in_strip
#print axioms RiemannZetaZerosOnLine_iff_nontrivial_zeros_positiveRe
#print axioms RiemannZetaZerosOnLine_of_DirichletLZerosOnLine
#print axioms DedekindZetaFactorsIntoDirichlet.toOffPole
#print axioms dedekindZeta_eq_zero_iff_exists_LFunction_eq_zero
#print axioms dedekindZeta_ne_zero_of_factor_ne_zero
#print axioms dedekindZeta_ne_zero_of_half_lt_re_of_factorization
#print axioms dedekindZeta_ne_zero_of_one_le_re_of_factorization
#print axioms dedekindZeta_one_eq_zero_of_not_LSeriesSummable
#print axioms not_DedekindZetaHalfPlane_of_dedekindZeta_one_eq_zero
#print axioms DedekindZetaHalfPlaneOffOne_of_factorization
#print axioms DedekindZetaHalfPlane_iff_offOne_and_one_ne_zero
#print axioms DedekindZetaHalfPlane_of_factorization_of_one_ne_zero
#print axioms DedekindZetaHalfPlane_of_GRH_of_factorization_of_one_ne_zero
#print axioms DedekindZetaStripInput_of_GRH_of_factorization
#print axioms DedekindZetaStripDistance_of_GRH_of_factorization
#print axioms DedekindZetaStripInequalityDistance_of_GRH_of_factorization
#print axioms DedekindZetaStripInequality_of_GRH_of_factorization
#print axioms DedekindZetaStripDistanceInput_of_GRH_of_factorization
#print axioms DedekindZetaStripInputFrom_of_GRH_of_factorization
#print axioms DedekindZetaStripInput_of_from
#print axioms exists_DedekindZetaStripInputFrom_paperBeta0_of_GRH_of_factorization
#print axioms DedekindZetaClassicalRegion_of_GRH_of_factorization_of_one_ne_zero
#print axioms DedekindZetaClassicalInput_of_GRH_of_factorization
#print axioms half_le_paperBeta0_of_two_le
#print axioms half_le_paperBeta0_of_discLog_eq_zero
#print axioms half_le_paperBeta0_of_one_le_of_log_two_le
#print axioms eventually_half_le_paperBeta0
#print axioms DedekindZetaStripInput_paperBeta0_of_GRH_of_factorization
#print axioms DedekindZetaStripInput_paperBeta0_of_GRH_of_factorization_of_one_le
#print axioms DedekindZetaStripDistanceInput_paperBeta0_of_GRH_of_factorization
#print axioms DedekindZetaClassicalInput_paperBeta0_of_GRH_of_factorization
#print axioms dedekindZeroFreeAboveBetaBelowOne_of_GRH_of_factorization
#print axioms dedekindZeroFreeAboveBeta_of_GRH_of_factorization_of_ne_one
#print axioms dedekindZeroFreeInput_of_GRH_of_factorization_of_ne_one
#print axioms dedekindZeroFreeAboveBeta_paperBeta0_of_GRH_of_factorization_of_ne_one
#print axioms dedekindZeroFreeInput_paperBeta0_of_GRH_of_factorization_of_ne_one
#print axioms dedekindZeroFreeAboveBeta_of_GRH_of_factorization_of_one_ne_zero
#print axioms dedekindZeroFreeAboveBeta_paperBeta0_of_GRH_of_factorization_of_one_ne_zero
#print axioms dedekindZeroFreeInput_paperBeta0_of_GRH_of_factorization_of_one_ne_zero
#print axioms not_dedekindZeroFreeAboveBeta_of_zero_eq_one

end

end Cogentic.RandomizedL34DedekindGRH
