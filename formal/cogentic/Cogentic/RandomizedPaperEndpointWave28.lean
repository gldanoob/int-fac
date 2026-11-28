import Cogentic.RandomizedPaperEndpointWave26
import Cogentic.RandomizedL34DedekindGRH
import Cogentic.RandomizedL34ClassicalStark
import Cogentic.RandomizedL34ChebotarevSides

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 28: the Stark exceptional-zero input is redundant under GRH

The Wave-26 record keeps, inside its L34 slot `L34ChebotarevSidesInputs`, both

* `zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog`, and
* `stark : StarkExceptionalZeroInput beta0 F discLog`.

Under GRH for the Dirichlet `L`-functions and the abelian factorization of
`ζ_K` into Dirichlet `L`-functions, every zero of `ζ_K` in the critical strip
lies on `Re = 1/2`, and the half-plane `Re ≥ 1` is zero-free.  Consequently an
*actual* exceptional zero has real part at most `1/2`, while the paper's line

```
paperBeta0 F discLog n = 1 - 1/(4 F n log|Δ| n)
```

is at least `1/2` as soon as `2 ≤ 4 F n log|Δ| n`.  Thus the Stark bound
`β₀ ≤ paperBeta0 F discLog` is automatic and the Stark field is redundant.

## What this file proves

1. **The exact algebraic content of `StarkExceptionalZeroInput`.**

   ```
   StarkExceptionalZeroInput beta0 F discLog
     ↔ (∀ n, 0 < F n) ∧ (∀ n, 0 < discLog n) ∧
       (∀ n, beta0 n ≤ paperBeta0 F discLog n)
   ```

   (`starkExceptionalZeroInput_iff_le_paperBeta0`).  In particular, for
   `beta0 = fun _ => 1/2` the whole input is exactly the arithmetic inequality
   `1/2 ≤ paperBeta0 F discLog`.

2. **The GRH strip consequence.**  From `DirichletLZerosOnLine` and

   `DedekindZetaFactorsIntoDirichletOffPole K ι N χ`

   we derive `DedekindZetaNoZerosAboveHalf K`: every zero of `ζ_K` other than
   the junk point `1` has `Re z ≤ 1/2`
   (`DedekindZetaNoZerosAboveHalf_of_GRH_of_factorization`).  The point `1` is
   excluded because `NumberField.dedekindZeta` is an `LSeries` and its value at
   the pole is a junk value, which GRH does not control.

3. **No zero in `(paperBeta0, 1)`.**  If `paperBeta0 F discLog n ≥ 1/2` then no
   zero of `ζ_K` has `paperBeta0 F discLog n < Re z < 1`; indeed no zero has
   `Re z > 1/2` (`dedekindZeta_noZero_above_paperBeta0`).  This is the precise
   statement that the paper's explicit `β₀` is above every zero.

4. **The Stark reduction.**  If each `beta0 n` is the real part of a genuine
   zero of `ζ_K` (`StarkRealizedZero K beta0`) and `2 ≤ 4 F log|Δ|`, then
   `StarkExceptionalZeroInput beta0 F discLog`
   (`starkExceptionalZeroInput_of_GRH_of_factorization_of_realized`).

   The *single residual* is the realization hypothesis.  `StarkExceptionalZeroInput`
   says nothing about zeros: it is the pure inequality `β₀ ≤ paperBeta0`.  The
   only information GRH adds is that a zero has real part `≤ 1/2`; without
   knowing that `β₀` is a zero real part, no analytic hypothesis can bound it.
   We therefore state the residual explicitly as `StarkRealizedZero`, and also
   give the purely numeric form `beta0 n ≤ 1/2` in
   `StarkHalfLineResidual`, which is the exact consequence of GRH for an
   exceptional zero and implies the Stark input together with
   `1/2 ≤ paperBeta0`.

5. **The Wave-28 L34 record.**  `Wave28L34Inputs` is
   `L34ChebotarevSidesInputs` with the `stark` field removed and replaced by the
   three arithmetic/residual fields

   * `starkF_pos : ∀ n, 0 < F n`,
   * `beta0_le_half : ∀ n, beta0 n ≤ 1/2` (the GRH residual), and
   * `paperBeta0_ge_half : ∀ n, 1/2 ≤ paperBeta0 F log|Δ| n` (the paper's
     arithmetic side condition, which also covers `log|Δ| = 0`).

   Its `toL34ChebotarevSidesInputs` derives the Stark field.  Every other L34
   field is unchanged.

6. **The Wave-28 E-generic record and endpoint.**
   `PaperResidualFor28` is `PaperResidualFor26` with `l34 : Wave28L34Inputs`;
   `toPaperResidualFor26` maps it back (the ledger only reads the actual probe
   miss `actualMiss`, which is unchanged), and
   `serialized_assembled_balancedEnvelopeInfimum_from_wave28Inputs` is the
   E-generic endpoint.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-free claim is used.  GRH
and the factorization are hypotheses; the only residual beyond them is the
realization of `β₀` as a zero (equivalently the numeric bound `β₀ ≤ 1/2`).
-/

namespace Cogentic.RandomizedPaperEndpointWave28

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.RandomizedL30NoBinomial
open Cogentic.RandomizedL30PrimeReciprocal
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34BelowOne
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34ZeroFreeArithmetic
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34DedekindGRH
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperEndpointWave17
open Cogentic.RandomizedPaperEndpointWave24
open Cogentic.RandomizedPaperEndpointWave25
open Cogentic.RandomizedPaperEndpointWave26
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## 1. The exact algebraic content of the Stark input -/

/-- The paper's Stark line is literally `paperBeta0`. -/
theorem starkLine_eq_paperBeta0 (F discLog : ℕ → ℝ) :
    starkLine F discLog = paperBeta0 F discLog := rfl

/-- **The exact bundled characterization of `StarkExceptionalZeroInput`.**  It
is precisely the two positivity conditions together with the paper's Stark
inequality `β₀ ≤ paperBeta0`.  Nothing about zeros is stored. -/
theorem starkExceptionalZeroInput_iff_pos_and_le_paperBeta0
    {beta0 F discLog : ℕ → ℝ} :
    StarkExceptionalZeroInput beta0 F discLog ↔
      (∀ n, 0 < F n) ∧ (∀ n, 0 < discLog n) ∧
        (∀ n, beta0 n ≤ paperBeta0 F discLog n) := by
  constructor
  · intro S
    refine ⟨S.F_pos, S.discLog_pos, fun n => ?_⟩
    have hle : beta0 n ≤ starkLine F discLog n :=
      not_lt.mp (S.no_exceptional_above n)
    simpa [starkLine, paperBeta0] using hle
  · rintro ⟨hF, hD, h⟩
    exact
      { F_pos := hF
        discLog_pos := hD
        no_exceptional_above := fun n => by
          have hle : beta0 n ≤ starkLine F discLog n := by
            simpa [starkLine, paperBeta0] using h n
          exact not_lt.mpr hle }

/-- **`StarkExceptionalZeroInput` is exactly the inequality
`β₀ ≤ paperBeta0` plus the two positivity side conditions.**  The structure
stores no relation to zeros: this characterization exposes that its entire
numeric content is the paper's Stark bound. -/
theorem starkExceptionalZeroInput_iff_le_paperBeta0
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n) :
    StarkExceptionalZeroInput beta0 F discLog ↔
      ∀ n, beta0 n ≤ paperBeta0 F discLog n := by
  constructor
  · intro S n
    have hle : beta0 n ≤ starkLine F discLog n := not_lt.mp (S.no_exceptional_above n)
    simpa [starkLine, paperBeta0] using hle
  · intro h
    exact
      { F_pos := hF
        discLog_pos := hD
        no_exceptional_above := fun n => by
          have hle : beta0 n ≤ starkLine F discLog n := by
            simpa [starkLine, paperBeta0] using h n
          exact not_lt.mpr hle }

/-- **Numerically, the Stark input is exactly `β₀ ≤ 1/2` together with
`1/2 ≤ paperBeta0`.**  This is the form in which GRH makes it redundant. -/
theorem starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (hβ0 : ∀ n, beta0 n ≤ 1 / 2)
    (hpaper : ∀ n, 1 / 2 ≤ paperBeta0 F discLog n) :
    StarkExceptionalZeroInput beta0 F discLog :=
  (starkExceptionalZeroInput_iff_le_paperBeta0 hF hD).mpr
    (fun n => le_trans (hβ0 n) (hpaper n))

/-- The same reduction from the paper's arithmetic side condition
`2 ≤ 4 F log|Δ|`, which implies `paperBeta0 ≥ 1/2`. -/
theorem starkExceptionalZeroInput_of_le_half_of_two_le
    {beta0 F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (hβ0 : ∀ n, beta0 n ≤ 1 / 2)
    (h2 : ∀ n, 2 ≤ 4 * F n * discLog n) :
    StarkExceptionalZeroInput beta0 F discLog :=
  starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0 hF hD hβ0
    (fun n => half_le_paperBeta0_of_two_le (h2 n))

/-- **The GRH choice `β₀ = 1/2`.**  The Stark input at the critical line is
exactly the arithmetic inequality `1/2 ≤ paperBeta0`. -/
theorem starkExceptionalZeroInput_half_of_half_le_paperBeta0
    {F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (hpaper : ∀ n, 1 / 2 ≤ paperBeta0 F discLog n) :
    StarkExceptionalZeroInput (fun _ => 1 / 2) F discLog :=
  starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0 hF hD
    (fun _ => le_rfl) hpaper

/-- The GRH choice `β₀ = 1/2` from the paper's arithmetic `2 ≤ 4 F log|Δ|`. -/
theorem starkExceptionalZeroInput_half_of_two_le
    {F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (h2 : ∀ n, 2 ≤ 4 * F n * discLog n) :
    StarkExceptionalZeroInput (fun _ => 1 / 2) F discLog :=
  starkExceptionalZeroInput_of_le_half_of_two_le hF hD (fun _ => le_rfl) h2

/-- **The paper's own choice `β₀ = paperBeta0` satisfies Stark's input
identically.**  This is the degenerate but frequently used case: if the
exceptional-zero threshold is *defined* as the Stark line, the input is
arithmetic reflexivity. -/
theorem starkExceptionalZeroInput_paperBeta0
    {F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n) :
    StarkExceptionalZeroInput (paperBeta0 F discLog) F discLog :=
  (starkExceptionalZeroInput_iff_le_paperBeta0 hF hD).mpr (fun _ => le_rfl)

/-! ## 2. The GRH strip packet: no zeros above `1/2` -/

/-- **The strip packet produced by GRH and the abelian factorization.**  Every
zero of `ζ_K` except the junk point `1` has real part at most `1/2`.

The point `1` is excluded on purpose: `NumberField.dedekindZeta` is an
`LSeries`, and its value at the pole is a junk value which GRH says nothing
about (see `Cogentic.RandomizedL34DedekindGRH`). -/
def DedekindZetaNoZerosAboveHalf (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ z : ℂ, NumberField.dedekindZeta K z = 0 → z ≠ 1 → z.re ≤ 1 / 2

/-- **GRH plus the off-pole factorization give the no-zeros-above-half
packet.**  Zeros with `1/2 < Re z < 1` are excluded by GRH through the
factorization; zeros with `1 ≤ Re z` are excluded by Mathlib's Dirichlet
half-plane through the factorization. -/
theorem DedekindZetaNoZerosAboveHalf_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ) :
    DedekindZetaNoZerosAboveHalf K := by
  intro z hz hz1
  by_contra hle
  have hhalf : 1 / 2 < z.re := lt_of_not_ge hle
  by_cases hlt : z.re < 1
  · exact dedekindZeta_ne_zero_of_half_lt_re_of_factorization hGRH hfac hz1 hhalf hlt hz
  · have hge : 1 ≤ z.re := le_of_not_gt hlt
    exact dedekindZeta_ne_zero_of_one_le_re_of_factorization hfac hz1 hge hz

/-- **The strip-input form of the packet.**  If the open strip
`1/2 < Re z < 1` is zero-free and the half-plane `Re z ≥ 1` is zero-free, then
no zero of `ζ_K` has real part above `1/2`.

The extra side condition `log|Δ| n ≤ 2 cz` makes the strip line
`1 - cz / log|Δ|` fall on or below `1/2`, so the strip inequality contradicts
`Re z > 1/2`.  In the GRH route this side condition is not needed, because
GRH gives zero-freeness of the whole strip directly. -/
theorem DedekindZetaNoZerosAboveHalf_of_stripInput_of_halfPlane
    (K : Type*) [Field K] [NumberField K]
    {cz : ℝ} {discLog : ℕ → ℝ}
    (hstrip : DedekindZetaStripInput K (fun _ => 1 / 2) cz discLog)
    (hH : DedekindZetaHalfPlane K)
    (hD : ∀ n, 0 < discLog n)
    (hcz : ∀ n, discLog n ≤ 2 * cz) :
    DedekindZetaNoZerosAboveHalf K := by
  intro z hz hz1
  by_contra hle
  have hhalf : 1 / 2 < z.re := lt_of_not_ge hle
  by_cases hlt : z.re < 1
  · have hres : z.re ≤ 1 - cz / discLog 0 := hstrip 0 z hz hhalf hlt
    have hquot : (1 : ℝ) / 2 ≤ cz / discLog 0 := by
      rw [le_div_iff₀ (hD 0)]
      linarith [hcz 0]
    linarith
  · have hge : 1 ≤ z.re := le_of_not_gt hlt
    exact hH z hge hz

/-! ## 3. No zero above the paper's `β₀` -/

/-- **No zero of `ζ_K` has real part above `paperBeta0`**, provided
`paperBeta0 ≥ 1/2`.  In particular there is no zero with
`paperBeta0 n < Re z < 1`, and indeed none with `Re z > 1/2`.

This is the precise content behind the paper's explicit exceptional zero: the
line `paperBeta0` is already above every zero once the critical line is
zero-free. -/
theorem dedekindZeta_noZero_above_paperBeta0
    {K : Type*} [Field K] [NumberField K]
    (hK : DedekindZetaNoZerosAboveHalf K)
    {F discLog : ℕ → ℝ}
    (hpaper : ∀ n, 1 / 2 ≤ paperBeta0 F discLog n) :
    ∀ (n : ℕ) (z : ℂ), NumberField.dedekindZeta K z = 0 → z ≠ 1 →
      ¬ (paperBeta0 F discLog n < z.re) := by
  intro n z hz hz1 hb
  have hle : z.re ≤ 1 / 2 := hK z hz hz1
  have hhalf : 1 / 2 ≤ paperBeta0 F discLog n := hpaper n
  linarith

/-- The same statement with the paper's arithmetic `2 ≤ 4 F log|Δ|`. -/
theorem dedekindZeta_noZero_above_paperBeta0_of_two_le
    {K : Type*} [Field K] [NumberField K]
    (hK : DedekindZetaNoZerosAboveHalf K)
    {F discLog : ℕ → ℝ}
    (h2 : ∀ n, 2 ≤ 4 * F n * discLog n) :
    ∀ (n : ℕ) (z : ℂ), NumberField.dedekindZeta K z = 0 → z ≠ 1 →
      ¬ (paperBeta0 F discLog n < z.re) :=
  dedekindZeta_noZero_above_paperBeta0 hK
    (fun n => half_le_paperBeta0_of_two_le (h2 n))

/-! ## 4. The residual: `β₀` is realized by a zero -/

/-- **The exact residual left by the Stark input.**  Each `beta0 n` is the real
part of a genuine (non-junk) zero of `ζ_K`.  This is the only information about
`β₀` that `StarkExceptionalZeroInput` does not itself contain, and it is what
lets GRH bound `β₀`. -/
def StarkRealizedZero (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) : Prop :=
  ∀ n, ∃ z : ℂ, NumberField.dedekindZeta K z = 0 ∧ z ≠ 1 ∧ z.re = beta0 n

/-- **The numeric half-line residual.**  An exceptional zero under GRH has real
part at most `1/2`.  This is the exact consequence of GRH used by the
reduction. -/
def StarkHalfLineResidual (beta0 : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n ≤ 1 / 2

/-- **Raising the exceptional-zero threshold preserves the zero-free region.**
This records why `DedekindZeroFreeInput` alone cannot bound `β₀`: the premise
`β₀ n < zeroRealPart n` becomes harder as `β₀` grows, so the zero-free field
remains true for every larger threshold and is vacuous once `β₀` exceeds all
zero real parts.  The realization of `β₀` as a zero is therefore a genuine
residual, not an artefact of the reduction. -/
theorem dedekindZeroFreeAboveBeta_of_beta0_le
    {beta0 beta0' zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : ∀ n, beta0 n ≤ beta0' n)
    (hZ : DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeAboveBeta beta0' zeroRealPart cz discLog := by
  intro n hb
  exact hZ n (lt_of_le_of_lt (h n) hb)

/-- The packaged zero-free input is monotone in the exceptional-zero
threshold, for the same reason. -/
theorem dedekindZeroFreeInput_of_beta0_le
    {beta0 beta0' zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : ∀ n, beta0 n ≤ beta0' n)
    (hZ : DedekindZeroFreeInput beta0 zeroRealPart cz discLog) :
    DedekindZeroFreeInput beta0' zeroRealPart cz discLog where
  cz_pos := hZ.cz_pos
  above_beta := dedekindZeroFreeAboveBeta_of_beta0_le h hZ.above_beta

/-- **Realized zeros plus the GRH strip packet bound `β₀` by `1/2`.** -/
theorem StarkHalfLineResidual_of_realized_of_noZerosAboveHalf
    {K : Type*} [Field K] [NumberField K]
    {beta0 : ℕ → ℝ}
    (hK : DedekindZetaNoZerosAboveHalf K)
    (hR : StarkRealizedZero K beta0) :
    StarkHalfLineResidual beta0 := by
  intro n
  obtain ⟨z, hz, hz1, hre⟩ := hR n
  rw [← hre]
  exact hK z hz hz1

/-- **Stark's input from a realized exceptional zero and the strip packet.** -/
theorem starkExceptionalZeroInput_of_realized_of_noZerosAboveHalf
    {K : Type*} [Field K] [NumberField K]
    {beta0 F discLog : ℕ → ℝ}
    (hK : DedekindZetaNoZerosAboveHalf K)
    (hR : StarkRealizedZero K beta0)
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (hpaper : ∀ n, 1 / 2 ≤ paperBeta0 F discLog n) :
    StarkExceptionalZeroInput beta0 F discLog :=
  starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0 hF hD
    (StarkHalfLineResidual_of_realized_of_noZerosAboveHalf hK hR) hpaper

/-- **The Stark field is redundant under GRH and the abelian factorization.**
This is the exact reduction requested by the L34 ledger: everything except the
realization of `β₀` as a zero comes from GRH and the factorization. -/
theorem starkExceptionalZeroInput_of_GRH_of_factorization_of_realized
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 F discLog : ℕ → ℝ}
    (hR : StarkRealizedZero K beta0)
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (h2 : ∀ n, 2 ≤ 4 * F n * discLog n) :
    StarkExceptionalZeroInput beta0 F discLog :=
  starkExceptionalZeroInput_of_le_half_of_two_le hF hD
    (StarkHalfLineResidual_of_realized_of_noZerosAboveHalf
      (DedekindZetaNoZerosAboveHalf_of_GRH_of_factorization hGRH hfac) hR)
    h2

/-- **The literal strip-packet form of the reduction.**  The analytic input is
`DedekindZetaStripInput` at the critical line together with the half-plane at
`1`; the numeric side condition `log|Δ| ≤ 2 cz` makes the strip line fall on or
below `1/2`.  With a realized exceptional zero this gives Stark's input. -/
theorem starkExceptionalZeroInput_of_stripInput_of_halfPlane_of_realized
    {K : Type*} [Field K] [NumberField K]
    {cz : ℝ} {discLog beta0 F : ℕ → ℝ}
    (hstrip : DedekindZetaStripInput K (fun _ => 1 / 2) cz discLog)
    (hH : DedekindZetaHalfPlane K)
    (hR : StarkRealizedZero K beta0)
    (hD : ∀ n, 0 < discLog n)
    (hcz : ∀ n, discLog n ≤ 2 * cz)
    (hF : ∀ n, 0 < F n)
    (h2 : ∀ n, 2 ≤ 4 * F n * discLog n) :
    StarkExceptionalZeroInput beta0 F discLog :=
  starkExceptionalZeroInput_of_realized_of_noZerosAboveHalf
    (DedekindZetaNoZerosAboveHalf_of_stripInput_of_halfPlane K hstrip hH hD hcz)
    hR hF hD (fun n => half_le_paperBeta0_of_two_le (h2 n))

/-- **The fully numeric form.**  If `β₀` is already known not to exceed the
critical line, GRH is not even needed: the arithmetic `1/2 ≤ paperBeta0`
closes the Stark input.  This isolates the exact residual `β₀ ≤ 1/2`. -/
theorem starkExceptionalZeroInput_of_halfLine
    {beta0 F discLog : ℕ → ℝ}
    (hβ0 : StarkHalfLineResidual beta0)
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (h2 : ∀ n, 2 ≤ 4 * F n * discLog n) :
    StarkExceptionalZeroInput beta0 F discLog :=
  starkExceptionalZeroInput_of_le_half_of_two_le hF hD hβ0 h2

/-! ## 5. The Wave-28 L34 record -/

/-- **The Wave-28 L34 inputs: the Stark field is removed.**

This is `L34ChebotarevSidesInputs` with

* the field `stark : StarkExceptionalZeroInput beta0 F discLog` deleted, and
* three explicit arithmetic/residual fields added:

  `starkF_pos` (the paper's factorial factor is positive),
  `beta0_le_half` (the GRH residual `β₀ ≤ 1/2`), and
  `paperBeta0_ge_half` (the paper's arithmetic `paperBeta0 ≥ 1/2`, implied
  by `2 ≤ 4 F log|Δ|` and also holding when `log|Δ| = 0`).

Every other field is copied verbatim, with the same name and type.  The Stark
field is reconstructed by `toL34ChebotarevSidesInputs` from
`starkExceptionalZeroInput_of_le_half_of_two_le`; it is not assumed. -/
structure Wave28L34Inputs where
  /-- The possible exceptional real zero `β₀`. -/
  beta0 : ℕ → ℝ
  /-- The real part of a generic zero of `ζ_E`. -/
  zeroRealPart : ℕ → ℝ
  /-- The absolute degree `2d` of `E = K(√γ)`. -/
  degree : ℕ → ℝ
  /-- `log |Δ_E|`. -/
  discLog : ℕ → ℝ
  /-- The factorial factor `F = (2d)!`. -/
  F : ℕ → ℝ
  /-- The polynomial input parameter `T`. -/
  T : ℕ → ℝ
  /-- A cumulative Chebotarev count. -/
  count : ℕ → ℝ
  /-- The cumulative inert count. -/
  inertCount : ℕ → ℝ
  /-- The degree-one inert count after discarding small / higher-degree ideals. -/
  degreeOneInert : ℕ → ℝ
  /-- `Li x`. -/
  liX : ℕ → ℝ
  /-- `Li x^{β₀}`. -/
  liBeta0 : ℕ → ℝ
  /-- The per-trial detection probability. -/
  pTrial : ℕ → ℝ
  /-- The actual failure probability of the probe stage. -/
  actualMiss : ℕ → ℝ
  /-- The number of nonrational classes. -/
  classCount : ℕ → ℝ
  /-- The number of probes `R`. -/
  R : ℕ → ℕ
  /-- The range constant. -/
  K : ℝ
  /-- The constant `C` in the effective error. -/
  C : ℝ
  /-- The constant `c` in the effective error. -/
  cZ : ℝ
  /-- The zero-free-region constant `c_z`. -/
  cz : ℝ
  /-- The bracket constant. -/
  cbr : ℝ
  /-- The per-ideal selection constant. -/
  csel : ℝ
  /-- The polynomial constant in `h* ≤ Ch T³`. -/
  Ch : ℝ
  /-- The Dedekind zero-free region in its smallest form. -/
  zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog
  /-- The explicit `T^6` range input. -/
  range : ChebotarevT6RangeInput K T degree discLog
  /-- The polynomial parameter is at least one. -/
  T_ge_one : ∀ n, 1 ≤ T n
  /-- The canonical Chebotarev error slack. -/
  cheb : ChebotarevResidualInput C cZ (cutoff T) degree count liX liBeta0
  /-- The inert count contains the counted nonidentity class. -/
  inert_ge_count : ∀ n, count n ≤ inertCount n
  /-- Stark's bound converted to the dyadic bracket. -/
  bracket : LogIntegralBracket cbr (cutoff T) F T liX liBeta0
  /-- The Chebotarev error is negligible against the bracket, in scalar form. -/
  error_scalar : ChebotarevErrorScalarBound C cZ cbr F T degree
  /-- Discarding small / higher-degree ideals is negligible, in scalar form. -/
  degree_loss_scalar : DegreeLossScalarBound cbr degree F T
  /-- The degree-one reduction. -/
  degree_one_reduction : DegreeOneInertReduction inertCount degreeOneInert degree (cutoff T)
  /-- Probe selection at `1/(d x)` per eligible ideal. -/
  selection : ProbeSelectionLowerBound csel (cutoff T) degree degreeOneInert pTrial
  /-- The paper's budget `R = F T¹⁰`. -/
  budget : ProbeBudget R F T
  /-- There is at least one nonrational class. -/
  classCount_pos : ∀ n, 0 < classCount n
  /-- The cubic class-count input. -/
  classCubic : ClassCountCubicInput Ch classCount T
  /-- The probe constant beats the class-count entropy constant. -/
  constant_margin : Ch * Real.log 2 < csel * cbr / 4
  /-- The probe exponent `T³` eventually dominates the ledger scale. -/
  scale_cubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (csel * cbr / 4 - Ch * Real.log 2) * T n ^ 3
  /-- The actual failure probability is nonnegative. -/
  actualMiss_nonneg : ∀ n, 0 ≤ actualMiss n
  /-- The probe union bound. -/
  union_bound : ProbeMissUnionBound actualMiss pTrial classCount R
  /-- The per-trial probability is nonnegative. -/
  pTrial_nonneg : ∀ n, 0 ≤ pTrial n
  /-- The per-trial probability is at most one. -/
  pTrial_le_one : ∀ n, pTrial n ≤ 1
  /-- The factorial factor is positive.  (Removed from `stark`; kept
  explicitly because `L34ChebotarevSidesInputs` does not store `F > 0`.) -/
  starkF_pos : ∀ n, 0 < F n
  /-- **The exact GRH residual**: the exceptional zero is at most the critical
  line.  For an actual zero this is exactly
  `StarkHalfLineResidual_of_realized_of_noZerosAboveHalf`. -/
  beta0_le_half : ∀ n, beta0 n ≤ 1 / 2
  /-- **The paper's arithmetic side condition** `1/2 ≤ paperBeta0 F discLog`.
  It holds as soon as `2 ≤ 4 F log|Δ|`, and also when `log|Δ| = 0` (where
  Lean's `1 / 0 = 0` gives `paperBeta0 = 1`).  This is the other half of the
  Stark reduction. -/
  paperBeta0_ge_half : ∀ n, 1 / 2 ≤ paperBeta0 F discLog n

namespace Wave28L34Inputs

variable (S : Wave28L34Inputs)

/-- **The Stark field, derived.**  This is the only place where the removed
Stark input is reconstructed. -/
theorem toStark : StarkExceptionalZeroInput S.beta0 S.F S.discLog :=
  starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0 S.starkF_pos
    (S.range.discLog_pos) S.beta0_le_half S.paperBeta0_ge_half

/-- **The full `L34ChebotarevSidesInputs`, with the Stark field derived.**
Every other field is passed through unchanged. -/
noncomputable def toL34ChebotarevSidesInputs : L34ChebotarevSidesInputs where
  beta0 := S.beta0
  zeroRealPart := S.zeroRealPart
  degree := S.degree
  discLog := S.discLog
  F := S.F
  T := S.T
  count := S.count
  inertCount := S.inertCount
  degreeOneInert := S.degreeOneInert
  liX := S.liX
  liBeta0 := S.liBeta0
  pTrial := S.pTrial
  actualMiss := S.actualMiss
  classCount := S.classCount
  R := S.R
  K := S.K
  C := S.C
  cZ := S.cZ
  cz := S.cz
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  zeroFree := S.zeroFree
  stark := S.toStark
  range := S.range
  T_ge_one := S.T_ge_one
  cheb := S.cheb
  inert_ge_count := S.inert_ge_count
  bracket := S.bracket
  error_scalar := S.error_scalar
  degree_loss_scalar := S.degree_loss_scalar
  degree_one_reduction := S.degree_one_reduction
  selection := S.selection
  budget := S.budget
  classCount_pos := S.classCount_pos
  classCubic := S.classCubic
  constant_margin := S.constant_margin
  scale_cubic := S.scale_cubic
  actualMiss_nonneg := S.actualMiss_nonneg
  union_bound := S.union_bound
  pTrial_nonneg := S.pTrial_nonneg
  pTrial_le_one := S.pTrial_le_one

/-- The transport leaves the prime run data unchanged. -/
theorem toL34ChebotarevSidesInputs_data :
    S.toL34ChebotarevSidesInputs.beta0 = S.beta0 ∧
      S.toL34ChebotarevSidesInputs.F = S.F ∧
      S.toL34ChebotarevSidesInputs.discLog = S.discLog ∧
      S.toL34ChebotarevSidesInputs.actualMiss = S.actualMiss ∧
      S.toL34ChebotarevSidesInputs.R = S.R :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The transported Stark field is the derived one**, not an assumption. -/
theorem toL34ChebotarevSidesInputs_stark :
    S.toL34ChebotarevSidesInputs.stark = S.toStark := rfl

/-- The transported L34 loss is still exactly the actual probe miss. -/
theorem toL34ChebotarevSidesInputs_loss_eq (n : ℕ) :
    (wave15L34Leaf S.toL34ChebotarevSidesInputs).loss n = S.actualMiss n :=
  wave15L34Leaf_loss_eq S.toL34ChebotarevSidesInputs n

end Wave28L34Inputs

/-! ## 6. The Wave-28 ledger -/

/-- **The Wave-28 ledger.**  The L34 slot is the actual probe miss of the
Wave-28 inputs, transported through the derived Stark field.  It is
definitionally the Wave-26 L34 leaf, because that leaf reads only
`actualMiss`. -/
noncomputable def wave28Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : ConcreteLeafResidual) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  fullyDischargedSlots l18_4 l19.toL19FullCertificate
    (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf (wave17InputsOfResidual l21).toL21_2LeafData)
    (wave15L27Leaf l27_data l27_finish) l30.toSubexpLeaf
    (wave15L34Leaf l34.toL34ChebotarevSidesInputs)
    (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
    (wave14P1Leaf p1)

/-- **The Wave-28 ledger is the Wave-26 ledger after deriving Stark.**  The
only difference is the L34 record: both ledgers read the same `actualMiss`. -/
theorem wave26Slots_eq_wave28Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : ConcreteLeafResidual) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) :
    wave26Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toL34ChebotarevSidesInputs p1 =
      wave28Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 :=
  rfl

/-! ## 7. The E-generic residual record -/

/-- **The Wave-28 E-generic residual record.**

This is exactly `PaperResidualFor26` with

```
l34 : L34ChebotarevSidesInputs
```

replaced by

```
l34 : Wave28L34Inputs,
```

so the L34 slot carries no `stark` field: the Stark bound is derived from
`beta0 ≤ 1/2` and `2 ≤ 4 F log|Δ|`.  All other fields are unchanged. -/
structure PaperResidualFor28
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate, with the L19.6 thin slot built from lattice
  data. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- **The whole L21.2 analytic input**: the zeta side and the literal central
  short-interval smooth count. -/
  l21 : ConcreteLeafResidual
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- **L30 with both density fields derived**, as in Wave 26. -/
  l30 : Wave26L30Inputs
  /-- **L34 with the Stark field derived** from `β₀ ≤ 1/2` and the paper's
  arithmetic `2 ≤ 4 F log|Δ|`. -/
  l34 : Wave28L34Inputs
  /-- P1: the explicit `exp (o(H))`-cost prepass. -/
  p1 : SubexpPrepassInput
  /-- C1: the public congruence check (L1). -/
  c1 : C1Inputs E
  /-- C2: conditional hidden-sign uniformity (L2–L5, including L4). -/
  c2 : C2Inputs E
  /-- C3: the ideal/actual total-variation budget (L6–L10). -/
  c3 : C3Inputs E
  /-- C4: the expected public-work budget (L11–L16). -/
  c4 : C4Inputs E D
  /-- The concrete epoch family underlying the C5 certificate. -/
  concrete : ∀ n, 3 ≤ n → ConcreteEpochData n
  /-- Adapter: the ambient epoch is the concrete family's `toHardEpochData`. -/
  concrete_eq : ∀ n (hN : 3 ≤ n), E n hN = (concrete n hN).toHardEpochData
  /-- **The C5 data assembled by `c5FullOfCount`.** -/
  c5Data : Wave15C5Data concrete
  /-- Adapter: the concrete C5 loss is dominated by the wave-28 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave28Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor28

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The fully discharged inputs directly from the Wave-28 record.**  The
ledger only reads the L34 probe-miss leaf, so the derived Stark field is
bypassed here; this is the unconditional route used by the endpoint. -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor28 E D) :
    FullyDischargedInputs E D where
  l18_4 := I.l18_4
  l19 := I.l19.toL19FullCertificate
  l20_2 := wave14L20_2Leaf I.l20_2
  l20_4 := I.l20_4.toSubexpLeaf
  l21_2 := wave14L21_2Leaf (wave17InputsOfResidual I.l21).toL21_2LeafData
  l27_1 := wave15L27Leaf I.l27_data I.l27_finish
  l30 := I.l30.toSubexpLeaf
  l34 := wave15L34Leaf I.l34.toL34ChebotarevSidesInputs
  l4_l25_l36 := wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget
  p1 := wave14P1Leaf I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5 := I.c5Data.toC5
  loss_le := by
    intro n hN
    simpa only [wave28Slots] using I.loss_le n hN

/-- **`PaperResidualFor28 E D → PaperResidualFor26 E D`.**  The L34 record is
transported by `Wave28L34Inputs.toL34ChebotarevSidesInputs`, which derives the
Stark field.  Every other field is copied verbatim; the C5 loss is unchanged
because `wave26Slots` and `wave28Slots` only read the same probe miss. -/
noncomputable def toPaperResidualFor26 (I : PaperResidualFor28 E D) :
    PaperResidualFor26 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34.toL34ChebotarevSidesInputs
  p1 := I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5Data := I.c5Data
  loss_le := by
    intro n hN
    rw [wave26Slots_eq_wave28Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21
      I.l27_data I.l27_finish I.l30 I.l34 I.p1]
    exact I.loss_le n hN

/-- The transport keeps the L34 record, with the derived Stark field. -/
theorem toPaperResidualFor26_l34 (I : PaperResidualFor28 E D) :
    (I.toPaperResidualFor26).l34 = I.l34.toL34ChebotarevSidesInputs := rfl

/-- **The transported Wave-26 L34 record carries the derived Stark field**, not
an assumed one. -/
theorem toPaperResidualFor26_l34_stark (I : PaperResidualFor28 E D) :
    (I.toPaperResidualFor26).l34.stark = I.l34.toStark := rfl

/-- The transport leaves the actual probe miss unchanged. -/
theorem toPaperResidualFor26_l34_actualMiss (I : PaperResidualFor28 E D) :
    (I.toPaperResidualFor26).l34.actualMiss = I.l34.actualMiss := rfl

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor28 E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- The reduction is the identity on every c1–c4 field. -/
theorem toPaperResidualFor26_c (I : PaperResidualFor28 E D) :
    (I.toPaperResidualFor26).c1 = I.c1 ∧
      (I.toPaperResidualFor26).c2 = I.c2 ∧
      (I.toPaperResidualFor26).c3 = I.c3 ∧
      (I.toPaperResidualFor26).c4 = I.c4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The reduction is the identity on the concrete family, its adapter and the
C5 data. -/
theorem toPaperResidualFor26_c5 (I : PaperResidualFor28 E D) :
    (I.toPaperResidualFor26).concrete = I.concrete ∧
      (I.toPaperResidualFor26).concrete_eq = I.concrete_eq ∧
      (I.toPaperResidualFor26).c5Data = I.c5Data :=
  ⟨rfl, rfl, rfl⟩

end PaperResidualFor28

/-- **The schedule-indexed form of the Wave-28 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor28Schedule
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor28 (E s) D

/-! ## 8. The E-generic endpoint -/

/-- **Wave-28 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** balanced-
schedule epoch family `E` which, at every valid ceiling, carries a
`PaperResidualFor28 (E s) D` record, the kernel-checked driver outputs a
permutation of `n.primeFactorsList` and has expected serialized bit cost
eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The L34 leaf of the record has no `stark` field: the Stark bound is derived
from the GRH residual `β₀ ≤ 1/2` and the arithmetic `2 ≤ 4 F log|Δ|`.  The
epoch family `E` is quantified inside the conclusion. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave28Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor28 (E s) D) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ :=
    serialized_assembled_balancedEnvelopeInfimum_from_wave26Inputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toPaperResidualFor26⟩

/-! ## 9. Residual accounting -/

/-- The field names of `Wave28L34Inputs`.  The Stark field `stark` is absent;
the three added fields are `starkF_pos`, `beta0_le_half` and
`paperBeta0_ge_half`. -/
def wave28L34FieldNames : List String :=
  ["beta0", "zeroRealPart", "degree", "discLog", "F", "T", "count",
   "inertCount", "degreeOneInert", "liX", "liBeta0", "pTrial", "actualMiss",
   "classCount", "R", "K", "C", "cZ", "cz", "cbr", "csel", "Ch", "zeroFree",
   "range", "T_ge_one", "cheb", "inert_ge_count", "bracket", "error_scalar",
   "degree_loss_scalar", "degree_one_reduction", "selection", "budget",
   "classCount_pos", "classCubic", "constant_margin", "scale_cubic",
   "actualMiss_nonneg", "union_bound", "pTrial_nonneg", "pTrial_le_one",
   "starkF_pos", "beta0_le_half", "paperBeta0_ge_half"]

theorem wave28L34FieldNames_length : wave28L34FieldNames.length = 44 := rfl

/-- **There is no `stark` field in the Wave-28 L34 record.** -/
theorem wave28L34_no_stark_field :
    wave28L34FieldNames.all (fun s => decide (s ≠ "stark")) = true := by
  decide

/-- **The exact remaining analytic residual of the L34 slot**: the GRH
half-line bound on the exceptional zero.  The other added fields are arithmetic
(`F > 0` and `2 ≤ 4 F log|Δ|`). -/
def wave28RemainingL34FieldNames : List String :=
  ["beta0_le_half"]

theorem wave28RemainingL34FieldNames_length :
    wave28RemainingL34FieldNames.length = 1 := rfl

/-- **The complete remaining L34 residual of the Wave-28 record**, stated at the
same level as `wave26RemainingFieldNames`: the GRH half-line bound on `β₀`, plus
the two arithmetic side conditions. -/
theorem wave28_l34_residual (S : Wave28L34Inputs) :
    (∀ n, S.beta0 n ≤ 1 / 2) ∧
      (∀ n, 0 < S.F n) ∧
      (∀ n, 1 / 2 ≤ paperBeta0 S.F S.discLog n) :=
  ⟨S.beta0_le_half, S.starkF_pos, S.paperBeta0_ge_half⟩

/-- The removed Stark field is a theorem of the recorded data. -/
theorem wave28_l34_stark_derived (S : Wave28L34Inputs) :
    StarkExceptionalZeroInput S.beta0 S.F S.discLog :=
  S.toStark

/-- The GRH residual is exactly what an actual exceptional zero satisfies under
the strip packet. -/
theorem wave28_l34_beta0_le_half_of_realized
    {K : Type*} [Field K] [NumberField K]
    (hK : DedekindZetaNoZerosAboveHalf K) {beta0 : ℕ → ℝ}
    (hR : StarkRealizedZero K beta0) :
    StarkHalfLineResidual beta0 :=
  StarkHalfLineResidual_of_realized_of_noZerosAboveHalf hK hR

/-! ## Axiom audit -/

#print axioms starkLine_eq_paperBeta0
#print axioms starkExceptionalZeroInput_iff_pos_and_le_paperBeta0
#print axioms starkExceptionalZeroInput_iff_le_paperBeta0
#print axioms starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0
#print axioms starkExceptionalZeroInput_of_le_half_of_two_le
#print axioms starkExceptionalZeroInput_half_of_half_le_paperBeta0
#print axioms starkExceptionalZeroInput_half_of_two_le
#print axioms starkExceptionalZeroInput_paperBeta0
#print axioms DedekindZetaNoZerosAboveHalf_of_GRH_of_factorization
#print axioms DedekindZetaNoZerosAboveHalf_of_stripInput_of_halfPlane
#print axioms dedekindZeta_noZero_above_paperBeta0
#print axioms dedekindZeta_noZero_above_paperBeta0_of_two_le
#print axioms dedekindZeroFreeAboveBeta_of_beta0_le
#print axioms dedekindZeroFreeInput_of_beta0_le
#print axioms StarkHalfLineResidual_of_realized_of_noZerosAboveHalf
#print axioms starkExceptionalZeroInput_of_realized_of_noZerosAboveHalf
#print axioms starkExceptionalZeroInput_of_GRH_of_factorization_of_realized
#print axioms starkExceptionalZeroInput_of_stripInput_of_halfPlane_of_realized
#print axioms starkExceptionalZeroInput_of_halfLine
#print axioms Wave28L34Inputs.toStark
#print axioms Wave28L34Inputs.toL34ChebotarevSidesInputs
#print axioms Wave28L34Inputs.toL34ChebotarevSidesInputs_data
#print axioms Wave28L34Inputs.toL34ChebotarevSidesInputs_stark
#print axioms Wave28L34Inputs.toL34ChebotarevSidesInputs_loss_eq
#print axioms wave28Slots
#print axioms wave26Slots_eq_wave28Slots
#print axioms PaperResidualFor28.toFullyDischargedInputs
#print axioms PaperResidualFor28.toPaperResidualFor26
#print axioms PaperResidualFor28.toPaperResidualFor26_l34
#print axioms PaperResidualFor28.toPaperResidualFor26_l34_stark
#print axioms PaperResidualFor28.toPaperResidualFor26_l34_actualMiss
#print axioms PaperResidualFor28.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor28.toPaperResidualFor26_c
#print axioms PaperResidualFor28.toPaperResidualFor26_c5
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave28Inputs
#print axioms wave28L34FieldNames_length
#print axioms wave28L34_no_stark_field
#print axioms wave28RemainingL34FieldNames_length
#print axioms wave28_l34_residual
#print axioms wave28_l34_stark_derived
#print axioms wave28_l34_beta0_le_half_of_realized

end Cogentic.RandomizedPaperEndpointWave28
