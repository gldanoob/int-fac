import Cogentic.RandomizedL34ZeroFree
import Cogentic.RandomizedL34DedekindGRH

/-!
# L34: the sequence-indexed zero-free input is vacuous, and its faithful repair

`Cogentic.RandomizedL34ZeroFree.ZetaZeroSequence` requires only that the sequence
consists of zeros:

```
structure ZetaZeroSequence (f : ℂ → ℂ) where
  zero : ℕ → ℂ
  isZero : ∀ n, f (zero n) = 0
  realPart : ℕ → ℝ
  realPart_eq : ∀ n, realPart n = (zero n).re
```

It has **no completeness field**.  Consequently
`DedekindZeroFreeInput beta0 Z.realPart cz discLog` speaks only about the
particular sequence `Z`, not about all zeros of `f`.  A proof of that input can
therefore omit every inconvenient zero and keep only zeros whose real part lies
below `beta0`.  This file makes that failure explicit and then supplies the
faithful interfaces.

## 1. The vacuity, concretely

* `zeroFunction` is `f = fun _ => 0`; every complex number is a zero.
* `halfZeroSequence` is the constant sequence at `1/2`.  For it,
  `DedekindZeroFreeInput (fun _ => 3/4) halfZeroSequence.realPart cz discLog`
  holds for every `cz > 0`, because `3/4 < 1/2` is false, so the implication is
  vacuous (`halfZeroSequence_zeroFreeInput`).
* More generally, any zero `s₀` of `f` with `s₀.re ≤ beta0 n` for all `n` gives
  such an input (`dedekindZeroFreeInput_of_zero_re_le_beta0`).  This is the
  precise "choose a zero below every exceptional zero" mechanism.
* A function with no zeros admits no `ZetaZeroSequence` at all
  (`not_nonempty_zetaZeroSequence_of_no_zeros`), so the vacuity is not from an
  empty sequence: it is from an *incomplete* one.

## 2. The faithful interfaces

* `CompleteZetaZeroSequence f` adds
  `complete : ∀ s, f s = 0 → ∃ n, zero n = s`.
* `DedekindZeroFreeAboveBetaStrip beta0 zeroRealPart cz discLog` is the
  sequence-indexed strip statement `beta0 n < r n → r n < 1 → r n ≤ 1 - cz/log n`.
  It coincides definitionally with the existing
  `DedekindZeroFreeAboveBetaBelowOne`.
* `DedekindZeroFreeInputComplete f beta0 cz discLog` is the honest all-zeros
  packet: `cz > 0` and
  `∀ n s, f s = 0 → beta0 n < s.re → s.re < 1 → s.re ≤ 1 - cz / discLog n`.
  This is exactly `DedekindZetaStripInput K beta0 cz discLog` for
  `f = NumberField.dedekindZeta K`, plus `cz_pos`
  (`dedekindZeroFreeInputComplete_iff_dedekindZetaStripInput`).
* `DedekindZeroFreeMaxAllZeros` is the optional max-form
  `s.re ≤ max (beta0 n) (1 - cz/log n)`, derived from the packet under a
  half-plane at `1` (`DedekindZeroFreeInputComplete.toMaxAllZeros`).

## 3. The implication and the counterexample

* `DedekindZeroFreeInputComplete.toDedekindZeroFreeInput`: the faithful packet,
  together with a half-plane at `1`, implies the current sequence-indexed
  `DedekindZeroFreeInput` for every zero sequence.  The hypothesis "all zeros
  above `β₀` have real part `< 1`" is exposed separately in
  `DedekindZeroFreeInputComplete.toDedekindZeroFreeInput_of_complete`.
* `dedekindZeroFreeInput_not_imp_complete`: the current input does **not** imply
  the faithful packet.  The counterexample is exactly the constant sequence at
  `1/2` for `f = 0` with `β₀ = 3/4`, `cz = 1`, `log|Δ| = 1`: the sequence input
  is vacuous, but the all-zeros packet fails at the genuine zero `7/8`.

## 4. The Dedekind zeta function and the junk zero at `1`

`NumberField.dedekindZeta` is an `LSeries`.  When its defining series is not
summable at `1`, `LSeries` assigns the junk value `0`:

```
dedekindZeta_one_eq_zero_of_not_LSeriesSummable :
  (¬ LSeriesSummable (fun n => Nat.card {I // absNorm I = n}) 1) →
  NumberField.dedekindZeta K 1 = 0
```

Hence a **complete** sequence for `ζ_K` must contain `1`
(`complete_dedekindZeta_contains_one_of_not_LSeriesSummable`).  If the packet
were not restricted to `Re < 1`, the junk zero at `1` would violate it whenever
`beta0 n < 1` and `cz/log n > 0`
(`not_unrestricted_strip_of_junk_one`).  The `Re < 1` restriction is therefore
not cosmetic: it is exactly what removes the junk pole value.

## The exact repair

Replace

```
DedekindZeroFreeInput beta0 zeroRealPart cz discLog
```

by the all-zeros packet

```
DedekindZeroFreeInputComplete f beta0 cz discLog
```

(or, for the Dedekind zeta function, by `DedekindZetaStripInput K beta0 cz
discLog` together with `0 < cz`).  If a sequence interface is retained, it must
be `CompleteZetaZeroSequence`, the statement must use
`DedekindZeroFreeAboveBetaStrip` and never `DedekindZeroFreeAboveBeta`, and the
packet must still be applied at the same index as the parameter sequences; the
all-zeros packet above avoids that bookkeeping entirely.

The Wave-23 derivation still goes through.  Its `toZeroFree` step is exactly
the record-independent theorem
`dedekindZeroFreeInput_of_GRH_of_factorization_of_one_ne_zero_faithful` with
`K = R.l34NumField`, `hGRH = R.line`, `hfac = R.l34Factorization`,
`h1 = R.l34ZetaOneNeZero`, `hβ = R.l34Beta0Half`, `hcz = R.l34cz_pos` and
`Z = R.l34ZeroSeq`, followed by the record's consistency field
`R.l34ZeroSeq_realPart`.  On the strip `Re ∈ (1/2, 1)` GRH excludes every
zero; at `Re = 1` the faithful packet's `Re < 1` hypothesis removes the point,
and the half-plane supplied by `l34ZetaOneNeZero` handles the rest.  Thus the
Wave-23 record does not need a new analytic input: it only needs its zero-free
field to be the faithful all-zeros packet, or (if it keeps a sequence) that
sequence to be complete together with the matching-index discipline above.  The
source `RandomizedPaperEndpointWave23.lean` is not present in the tracked tree
of this checkout, so the bridge is stated here in record-independent form
rather than by importing that module.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  Nothing is committed;
the existing files are untouched.
-/

namespace Cogentic.RandomizedL34ZeroFaithful

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open Filter Real
open NumberField
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34BelowOne
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34DedekindGRH
open Cogentic.RandomizedL34ZeroFreeArithmetic

noncomputable section

/-! ## 1. The vacuity of the sequence-indexed input -/

/-- The identically-zero function.  Every complex number is a zero of it. -/
def zeroFunction : ℂ → ℂ := fun _ => 0

/-- The constant zero sequence at `1/2` for the identically-zero function.  It
is a perfectly good `ZetaZeroSequence`, but it is not complete: it misses the
genuine zero `0` (and every other point). -/
def halfZeroSequence : ZetaZeroSequence zeroFunction where
  zero := fun _ => (1 / 2 : ℂ)
  isZero := fun _ => rfl
  realPart := fun _ => 1 / 2
  realPart_eq := fun _ => by norm_num

/-- Every constant sequence at a genuine zero is a `ZetaZeroSequence`. -/
def constantZeroSequence (f : ℂ → ℂ) (s₀ : ℂ) (hs₀ : f s₀ = 0) :
    ZetaZeroSequence f where
  zero := fun _ => s₀
  isZero := fun _ => hs₀
  realPart := fun _ => s₀.re
  realPart_eq := fun _ => rfl

/-- **A zero with real part at most every `beta0 n` makes the current input
vacuous.**  The constant sequence at `s₀` satisfies `DedekindZeroFreeInput` for
every positive `cz`, because the antecedent `beta0 n < s₀.re` is never true. -/
theorem dedekindZeroFreeInput_of_zero_re_le_beta0
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (s₀ : ℂ) (_hs₀ : f s₀ = 0) (hle : ∀ n, s₀.re ≤ beta0 n) (hcz : 0 < cz) :
    DedekindZeroFreeInput beta0 (fun _ => s₀.re) cz discLog where
  cz_pos := hcz
  above_beta := by
    intro n hb
    exact absurd hb (not_lt.mpr (hle n))

/-- The strict form requested when the zero lies strictly below every `beta0 n`. -/
theorem dedekindZeroFreeInput_of_zero_re_lt_beta0
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (s₀ : ℂ) (hs₀ : f s₀ = 0) (hlt : ∀ n, s₀.re < beta0 n) (hcz : 0 < cz) :
    DedekindZeroFreeInput beta0 (fun _ => s₀.re) cz discLog :=
  dedekindZeroFreeInput_of_zero_re_le_beta0 s₀ hs₀
    (fun n => le_of_lt (hlt n)) hcz

/-- The same triviality with the sequence made explicit. -/
theorem constantZeroSequence_zeroFreeInput
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (s₀ : ℂ) (hs₀ : f s₀ = 0) (hle : ∀ n, s₀.re ≤ beta0 n) (hcz : 0 < cz) :
    DedekindZeroFreeInput beta0 (constantZeroSequence f s₀ hs₀).realPart cz discLog := by
  simpa only [constantZeroSequence] using
    dedekindZeroFreeInput_of_zero_re_le_beta0 (f := f) (beta0 := beta0)
      (cz := cz) (discLog := discLog) s₀ hs₀ hle hcz

/-- **The concrete `f = 0`, `Re = 1/2`, `β₀ = 3/4` instance.**  The current
zero-free input holds for every positive `cz`, although `f` is identically zero
and `1/2` is not a faithful description of its zero set. -/
theorem zeroFunction_zeroFreeInput_of_half
    (cz : ℝ) (hcz : 0 < cz) (discLog : ℕ → ℝ) :
    DedekindZeroFreeInput (fun _ => (3 / 4 : ℝ)) (fun _ => (1 / 2 : ℝ)) cz discLog where
  cz_pos := hcz
  above_beta := by
    intro n hb
    norm_num at hb

/-- The same instance stated with `halfZeroSequence.realPart`. -/
theorem halfZeroSequence_zeroFreeInput
    (cz : ℝ) (hcz : 0 < cz) (discLog : ℕ → ℝ) :
    DedekindZeroFreeInput (fun _ => (3 / 4 : ℝ)) halfZeroSequence.realPart cz discLog where
  cz_pos := hcz
  above_beta := by
    intro n hb
    simp only [halfZeroSequence] at hb
    norm_num at hb

/-- The chosen constant sequence is genuinely incomplete: `0` is a zero of
`zeroFunction` that does not occur in it. -/
theorem halfZeroSequence_misses_zero :
    ∃ s : ℂ, zeroFunction s = 0 ∧ ¬ ∃ n, halfZeroSequence.zero n = s := by
  refine ⟨(0 : ℂ), rfl, ?_⟩
  rintro ⟨n, hn⟩
  have h : (1 / 2 : ℂ) = 0 := by simpa only [halfZeroSequence] using hn
  norm_num at h

/-- **No zero sequence can be fabricated for a zero-free function.**  The
degeneracy above is therefore not an empty-sequence artefact: the sequence must
really consist of zeros, and the only freedom is to omit the inconvenient
ones. -/
theorem not_nonempty_zetaZeroSequence_of_no_zeros {f : ℂ → ℂ}
    (hf : ∀ s : ℂ, f s ≠ 0) : ¬ Nonempty (ZetaZeroSequence f) := by
  rintro ⟨Z⟩
  exact hf (Z.zero 0) (Z.isZero 0)

/-! ## 2. The faithful interfaces -/

/-- **A zero sequence that enumerates every zero.**  This is the missing
condition in `ZetaZeroSequence`. -/
structure CompleteZetaZeroSequence (f : ℂ → ℂ) extends ZetaZeroSequence f where
  /-- Every zero of `f` occurs in the sequence. -/
  complete : ∀ s : ℂ, f s = 0 → ∃ n : ℕ, zero n = s

/-- **The strip form of the zero-free statement.**  The current
`DedekindZeroFreeAboveBeta` with the extra hypothesis `Re ρ < 1`.  It is
definitionally the existing `DedekindZeroFreeAboveBetaBelowOne`. -/
def DedekindZeroFreeAboveBetaStrip (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n, beta0 n < zeroRealPart n → zeroRealPart n < 1 →
    zeroRealPart n ≤ 1 - cz / discLog n

/-- The new strip definition is the existing residual strip definition. -/
theorem dedekindZeroFreeAboveBetaStrip_iff_belowOne
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} :
    DedekindZeroFreeAboveBetaStrip beta0 zeroRealPart cz discLog ↔
      DedekindZeroFreeAboveBetaBelowOne beta0 zeroRealPart cz discLog :=
  Iff.rfl

/-- **The faithful zero-free packet, quantified over all zeros of `f`.**  Unlike
`DedekindZeroFreeInput`, this cannot be satisfied by choosing a favourable
sequence: every zero above `β₀` with real part `< 1` must satisfy the bound. -/
structure DedekindZeroFreeInputComplete (f : ℂ → ℂ) (beta0 : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop where
  /-- The zero-free-region constant is positive. -/
  cz_pos : 0 < cz
  /-- Every zero of `f` above `β₀` and below `1` is on the zero-free side. -/
  strip : ∀ n (s : ℂ), f s = 0 → beta0 n < s.re → s.re < 1 →
    s.re ≤ 1 - cz / discLog n

/-- **The optional max-modulus form, quantified over all zeros.**  It says that
every zero is at most the larger of `β₀` and the zero-free line. -/
def DedekindZeroFreeMaxAllZeros (f : ℂ → ℂ) (beta0 : ℕ → ℝ) (cz : ℝ)
    (discLog : ℕ → ℝ) : Prop :=
  ∀ n (s : ℂ), f s = 0 → s.re ≤ max (beta0 n) (1 - cz / discLog n)

/-- The faithful packet gives the sequence-indexed strip statement for every
zero sequence. -/
theorem DedekindZeroFreeInputComplete.toAboveBetaStrip
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZeroFreeInputComplete f beta0 cz discLog)
    (Z : ZetaZeroSequence f) :
    DedekindZeroFreeAboveBetaStrip beta0 Z.realPart cz discLog := by
  intro n hb hlt
  have hb' : beta0 n < (Z.zero n).re := by simpa only [Z.realPart_eq n] using hb
  have hlt' : (Z.zero n).re < 1 := by simpa only [Z.realPart_eq n] using hlt
  have h := C.strip n (Z.zero n) (Z.isZero n) hb' hlt'
  simpa only [Z.realPart_eq n] using h

/-- The faithful packet gives the optional max-modulus form under a half-plane
at `1`.  This is the form in which a `max`-based case split consumes it. -/
theorem DedekindZeroFreeInputComplete.toMaxAllZeros
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZeroFreeInputComplete f beta0 cz discLog)
    (hf : ZeroFreeHalfPlane f 1) :
    DedekindZeroFreeMaxAllZeros f beta0 cz discLog := by
  intro n s hs
  by_cases hb : beta0 n < s.re
  · by_cases hlt : s.re < 1
    · exact le_trans (C.strip n s hs hb hlt) (le_max_right _ _)
    · exact absurd hs (hf s (le_of_not_gt hlt))
  · exact le_trans (le_of_not_gt hb) (le_max_left _ _)

/-- The faithful packet gives the sequence-indexed max form. -/
theorem DedekindZeroFreeInputComplete.toMax
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZeroFreeInputComplete f beta0 cz discLog)
    (hf : ZeroFreeHalfPlane f 1) (Z : ZetaZeroSequence f) :
    DedekindZeroFreeMax beta0 Z.realPart cz discLog := by
  intro n
  have h := C.toMaxAllZeros hf n (Z.zero n) (Z.isZero n)
  simpa only [Z.realPart_eq n] using h

/-- **The faithful packet is exactly the existing all-zeros Dedekind strip
input, plus positivity.**  This is the exact repair: no new analytic statement
is needed, only the replacement of the sequence-indexed form by
`DedekindZetaStripInput`/`DedekindZetaStripDistanceInput`. -/
theorem dedekindZeroFreeInputComplete_iff_dedekindZetaStripInput
    (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} (hcz : 0 < cz) :
    DedekindZeroFreeInputComplete (NumberField.dedekindZeta K) beta0 cz discLog ↔
      DedekindZetaStripInput K beta0 cz discLog := by
  constructor
  · intro C n z hz hb hlt
    exact C.strip n z hz hb hlt
  · intro h
    refine ⟨hcz, ?_⟩
    intro n z hz hb hlt
    exact h n z hz hb hlt

/-- The faithful packet is exactly the existing *smallest* Dedekind strip input
`DedekindZetaStripDistanceInput`, plus positivity.  This is the most explicit
form of the repair. -/
theorem dedekindZeroFreeInputComplete_iff_dedekindZetaStripDistanceInput
    (K : Type*) [Field K] [NumberField K]
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (hcz : 0 < cz) (hd : ∀ n, 0 < discLog n) :
    DedekindZeroFreeInputComplete (NumberField.dedekindZeta K) beta0 cz discLog ↔
      DedekindZetaStripDistanceInput K beta0 cz discLog :=
  (dedekindZeroFreeInputComplete_iff_dedekindZetaStripInput K hcz).trans
    (dedekindZetaStripInput_iff_stripDistanceInput K hcz hd)

/-! ## 3. The implication and the counterexample -/

/-- The sequence-indexed strip statement plus "zeros above `β₀` have real part
`< 1`" is exactly the current `DedekindZeroFreeAboveBeta`. -/
theorem DedekindZeroFreeAboveBetaStrip.toAboveBeta
    {beta0 zeroRealPart : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (h : DedekindZeroFreeAboveBetaStrip beta0 zeroRealPart cz discLog)
    (hlt : ∀ n, beta0 n < zeroRealPart n → zeroRealPart n < 1) :
    DedekindZeroFreeAboveBeta beta0 zeroRealPart cz discLog := by
  intro n hb
  exact h n hb (hlt n hb)

/-- **Faithful implies current.**  A half-plane at `1` supplies the `Re < 1`
hypothesis for every zero above `β₀`, and the faithful strip statement supplies
the inequality. -/
theorem DedekindZeroFreeInputComplete.toDedekindZeroFreeInput
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (C : DedekindZeroFreeInputComplete f beta0 cz discLog)
    (hf : ZeroFreeHalfPlane f 1) (Z : ZetaZeroSequence f) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog where
  cz_pos := C.cz_pos
  above_beta := by
    refine DedekindZeroFreeAboveBetaStrip.toAboveBeta (C.toAboveBetaStrip Z) ?_
    intro n hb
    by_contra hnot
    have hge : 1 ≤ Z.realPart n := le_of_not_gt hnot
    rw [Z.realPart_eq n] at hge
    exact hf (Z.zero n) hge (Z.isZero n)

/-- **Faithful implies current, with the half-plane hypothesis stated on the
zeros rather than as a global half-plane.**  This is the form matching "a
complete sequence where all zeros above `β₀` have real part `< 1`". -/
theorem DedekindZeroFreeInputComplete.toDedekindZeroFreeInput_of_complete
    {f : ℂ → ℂ} {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ}
    (Z : CompleteZetaZeroSequence f)
    (C : DedekindZeroFreeInputComplete f beta0 cz discLog)
    (habove : ∀ s : ℂ, f s = 0 → ∀ n : ℕ, beta0 n < s.re → s.re < 1) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog where
  cz_pos := C.cz_pos
  above_beta := by
    intro n hb
    have hb' : beta0 n < (Z.zero n).re := by simpa only [Z.realPart_eq n] using hb
    have hlt' : (Z.zero n).re < 1 :=
      habove (Z.zero n) (Z.isZero n) n hb'
    have h := C.strip n (Z.zero n) (Z.isZero n) hb' hlt'
    simpa only [Z.realPart_eq n] using h

/-- **The concrete faithful packet fails at the zero `7/8`.**  For
`f = 0`, `β₀ = 3/4`, `cz = 1` and `log|Δ| = 1`, the point `7/8` is a zero in
the strip `(3/4, 1)`, and the required inequality is `7/8 ≤ 0`. -/
theorem zeroFunction_not_faithful :
    ¬ DedekindZeroFreeInputComplete zeroFunction (fun _ => (3 / 4 : ℝ)) 1
      (fun _ => (1 : ℝ)) := by
  intro C
  have h := C.strip 0 (7 / 8 : ℂ) rfl (by norm_num) (by norm_num)
  norm_num at h

/-- The current input for the concrete model. -/
theorem zeroFunction_current_vacuous :
    DedekindZeroFreeInput (fun _ => (3 / 4 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1
      (fun _ => (1 : ℝ)) :=
  zeroFunction_zeroFreeInput_of_half 1 (by norm_num) (fun _ => 1)

/-- **Current input does not imply the faithful packet.**  The model above has
the sequence-indexed input but fails the all-zeros packet. -/
theorem zeroFunction_current_not_faithful :
    DedekindZeroFreeInput (fun _ => (3 / 4 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1
        (fun _ => (1 : ℝ)) ∧
      ¬ DedekindZeroFreeInputComplete zeroFunction (fun _ => (3 / 4 : ℝ)) 1
        (fun _ => (1 : ℝ)) :=
  ⟨zeroFunction_current_vacuous, zeroFunction_not_faithful⟩

/-- **The general non-implication.**  No choice of a single zero sequence can
turn the sequence-indexed input into the all-zeros packet. -/
theorem dedekindZeroFreeInput_not_imp_complete :
    ¬ ∀ (f : ℂ → ℂ) (beta0 zeroRealPart : ℕ → ℝ) (cz : ℝ) (discLog : ℕ → ℝ),
        DedekindZeroFreeInput beta0 zeroRealPart cz discLog →
        DedekindZeroFreeInputComplete f beta0 cz discLog := by
  intro h
  exact zeroFunction_not_faithful
    (h zeroFunction (fun _ => (3 / 4 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1
      (fun _ => (1 : ℝ)) zeroFunction_current_vacuous)

/-- The concrete vacuous sequence cannot be completed to a complete sequence
with the same real-part function.  This isolates the failure as incompleteness,
not as a bad choice of `cz` or `log|Δ|`. -/
theorem halfZeroSequence_not_completable :
    ¬ ∃ Z : CompleteZetaZeroSequence zeroFunction,
        Z.realPart = fun _ => (1 / 2 : ℝ) := by
  rintro ⟨Z, hZ⟩
  obtain ⟨n, hn⟩ := Z.complete (0 : ℂ) rfl
  have hzero : Z.realPart n = 0 := by
    rw [Z.realPart_eq n, hn]
    rfl
  have hhalf : Z.realPart n = (1 / 2 : ℝ) := by
    simp only [hZ]
  rw [hzero] at hhalf
  norm_num at hhalf

/-! ## 4. The Dedekind zeta function and the junk zero at `1` -/

/-- A complete sequence for `ζ_K` contains the junk value `1` whenever
`ζ_K 1 = 0`. -/
theorem complete_dedekindZeta_contains_one
    (K : Type*) [Field K] [NumberField K]
    (h1 : NumberField.dedekindZeta K 1 = 0)
    (Z : CompleteZetaZeroSequence (NumberField.dedekindZeta K)) :
    ∃ n, Z.zero n = 1 :=
  Z.complete 1 h1

/-- **The junk-zero fact, fed through completeness.**  If the defining
`LSeries` of `ζ_K` is not summable at `1`, then `ζ_K 1 = 0`, so every complete
zero sequence contains `1`. -/
theorem complete_dedekindZeta_contains_one_of_not_LSeriesSummable
    (K : Type*) [Field K] [NumberField K]
    (h : ¬ LSeriesSummable
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 1)
    (Z : CompleteZetaZeroSequence (NumberField.dedekindZeta K)) :
    ∃ n, Z.zero n = 1 :=
  complete_dedekindZeta_contains_one K
    (dedekindZeta_one_eq_zero_of_not_LSeriesSummable K h) Z

/-- **The `Re < 1` restriction is forced by the junk zero.**  Without it, the
all-zeros packet would demand `1 ≤ 1 - cz/log|Δ|` at the genuine (junk) zero
`s = 1`, which is false as soon as `cz > 0` and `log|Δ| > 0`. -/
theorem not_unrestricted_strip_of_junk_one
    (K : Type*) [Field K] [NumberField K]
    (h1 : NumberField.dedekindZeta K 1 = 0)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} {n : ℕ}
    (hβ : beta0 n < 1) (hcz : 0 < cz) (hd : 0 < discLog n) :
    ¬ (∀ (m : ℕ) (s : ℂ), NumberField.dedekindZeta K s = 0 →
        beta0 m < s.re → s.re ≤ 1 - cz / discLog m) := by
  intro h
  have hm : (1 : ℝ) ≤ 1 - cz / discLog n := by
    have := h n 1 h1 (by simpa using hβ)
    simpa using this
  have hlt : 1 - cz / discLog n < 1 := by
    have hpos : 0 < cz / discLog n := div_pos hcz hd
    linarith
  linarith

/-- The sequence-indexed form of the same failure: a zero sequence containing
`1` cannot satisfy the unpunctured `DedekindZeroFreeAboveBeta` when `β₀ < 1`
and `cz > 0`.  This is the existing GRH-file lemma, restated here to keep the
junk-zero argument self-contained. -/
theorem not_dedekindZeroFreeAboveBeta_of_junk_one
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f)
    {beta0 : ℕ → ℝ} {cz : ℝ} {discLog : ℕ → ℝ} {n : ℕ}
    (h1 : Z.zero n = 1) (hβ : beta0 n < 1) (hcz : 0 < cz) (hd : 0 < discLog n) :
    ¬ DedekindZeroFreeAboveBeta beta0 Z.realPart cz discLog :=
  Cogentic.RandomizedL34DedekindGRH.not_dedekindZeroFreeAboveBeta_of_zero_eq_one
    Z h1 hβ hcz hd

/-! ## 5. The faithful GRH/Wave-23 derivation -/

/-- **The faithful packet follows from the same GRH data as the old one.**
`DedekindZetaStripInput_of_GRH_of_factorization` is exactly the all-zeros strip
statement, so `cz_pos` is the only additional field. -/
theorem dedekindZeroFreeInputComplete_of_GRH_of_factorization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} (hcz : 0 < cz) (discLog : ℕ → ℝ) :
    DedekindZeroFreeInputComplete (NumberField.dedekindZeta K) beta0 cz discLog where
  cz_pos := hcz
  strip := by
    intro n s hs hb hlt
    exact DedekindZetaStripInput_of_GRH_of_factorization hGRH hfac hβ cz discLog
      n s hs hb hlt

/-- **The faithful form of the Wave-23 bridge.**  The same hypotheses as
`dedekindZeroFreeInput_of_GRH_of_factorization_of_one_ne_zero`, but routed
through the faithful packet.  The `Re = 1` point is excluded by the packet's
`Re < 1`; the half-plane from `ζ_K 1 ≠ 0` covers the remaining zeros. -/
theorem dedekindZeroFreeInput_of_GRH_of_factorization_of_one_ne_zero_faithful
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} (hcz : 0 < cz) {discLog : ℕ → ℝ}
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog := by
  have hC :=
    dedekindZeroFreeInputComplete_of_GRH_of_factorization
      (K := K) (ι := ι) (N := N) (χ := χ) hGRH hfac hβ hcz discLog
  have hhalf : DedekindZetaHalfPlane K :=
    DedekindZetaHalfPlane_of_factorization_of_one_ne_zero hfac h1
  exact DedekindZeroFreeInputComplete.toDedekindZeroFreeInput hC hhalf Z

/-- **Record-independent form of the Wave-23 faithful zero-free packet.**  The
Wave-23 record's `l34Beta0Half`, `line`, `l34Factorization` and `l34cz_pos`
are exactly the hypotheses below; the sequence field is not used. -/
theorem wave23_toZeroFreeFaithful
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} (hcz : 0 < cz) (discLog : ℕ → ℝ) :
    DedekindZeroFreeInputComplete (NumberField.dedekindZeta K) beta0 cz discLog :=
  dedekindZeroFreeInputComplete_of_GRH_of_factorization hGRH hfac hβ hcz discLog

/-- **Record-independent form of the Wave-23 `toZeroFree` step.**  This is the
exact theorem that replaces `PaperResidualInputsWave23.toZeroFree` when
`l34ZeroFree` is replaced by the faithful packet. -/
theorem wave23_toZeroFree_of_faithful
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {beta0 : ℕ → ℝ} (hβ : ∀ n, 1 / 2 ≤ beta0 n)
    {cz : ℝ} (hcz : 0 < cz) {discLog : ℕ → ℝ}
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput beta0 Z.realPart cz discLog :=
  dedekindZeroFreeInput_of_GRH_of_factorization_of_one_ne_zero_faithful
    hGRH hfac h1 hβ hcz Z

/-- The `paperBeta0` instance of the faithful bridge. -/
theorem dedekindZeroFreeInput_paperBeta0_of_GRH_of_factorization_of_one_ne_zero_faithful
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → ℕ} [∀ i, NeZero (N i)]
    {χ : ∀ i, DirichletCharacter ℂ (N i)}
    (hGRH : DirichletLZerosOnLine)
    (hfac : DedekindZetaFactorsIntoDirichletOffPole K ι N χ)
    (h1 : NumberField.dedekindZeta K 1 ≠ 0)
    {F discLog : ℕ → ℝ} (hβ : ∀ n, 2 ≤ 4 * F n * discLog n)
    {cz : ℝ} (hcz : 0 < cz)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput (paperBeta0 F discLog) Z.realPart cz discLog :=
  dedekindZeroFreeInput_of_GRH_of_factorization_of_one_ne_zero_faithful
    hGRH hfac h1 (fun n => half_le_paperBeta0_of_two_le (hβ n)) hcz Z

/-! ## Axiom audit -/

#print axioms zeroFunction_zeroFreeInput_of_half
#print axioms halfZeroSequence_zeroFreeInput
#print axioms halfZeroSequence_misses_zero
#print axioms not_nonempty_zetaZeroSequence_of_no_zeros
#print axioms dedekindZeroFreeInput_of_zero_re_le_beta0
#print axioms dedekindZeroFreeInput_of_zero_re_lt_beta0
#print axioms constantZeroSequence_zeroFreeInput
#print axioms dedekindZeroFreeAboveBetaStrip_iff_belowOne
#print axioms DedekindZeroFreeInputComplete.toAboveBetaStrip
#print axioms DedekindZeroFreeInputComplete.toMaxAllZeros
#print axioms DedekindZeroFreeInputComplete.toMax
#print axioms dedekindZeroFreeInputComplete_iff_dedekindZetaStripInput
#print axioms dedekindZeroFreeInputComplete_iff_dedekindZetaStripDistanceInput
#print axioms DedekindZeroFreeAboveBetaStrip.toAboveBeta
#print axioms DedekindZeroFreeInputComplete.toDedekindZeroFreeInput
#print axioms DedekindZeroFreeInputComplete.toDedekindZeroFreeInput_of_complete
#print axioms zeroFunction_not_faithful
#print axioms zeroFunction_current_vacuous
#print axioms zeroFunction_current_not_faithful
#print axioms dedekindZeroFreeInput_not_imp_complete
#print axioms halfZeroSequence_not_completable
#print axioms complete_dedekindZeta_contains_one
#print axioms complete_dedekindZeta_contains_one_of_not_LSeriesSummable
#print axioms not_unrestricted_strip_of_junk_one
#print axioms not_dedekindZeroFreeAboveBeta_of_junk_one
#print axioms dedekindZeroFreeInputComplete_of_GRH_of_factorization
#print axioms dedekindZeroFreeInput_of_GRH_of_factorization_of_one_ne_zero_faithful
#print axioms wave23_toZeroFreeFaithful
#print axioms wave23_toZeroFree_of_faithful
#print axioms dedekindZeroFreeInput_paperBeta0_of_GRH_of_factorization_of_one_ne_zero_faithful

end

end Cogentic.RandomizedL34ZeroFaithful
