import Cogentic.RandomizedPaperEndpointWave31
import Cogentic.RandomizedPaperEndpointWave30

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 32: the combined residual record

This file combines the three independent reductions of the L30, L34 and L21.2
blocks into one E-generic (and number-field-generic) residual record.

* **L30** is `Wave31L30Inputs` from Wave 31: the sharp central short-interval
  count is *derived* from the large-prime Buchstab estimate `hbuchstab` and the
  odd-half parity fraction `hparity`, so the residual fields are exactly those
  two analytic inputs (plus the effective constant `θ * c`).
* **L34** is `Wave30L34Inputs K` from Wave 30: the vacuous sequence-indexed
  `zeroFree` field is replaced by the faithful all-zeros strip packet
  `zeroStrip`, a genuine zero sequence `zeroSeq` of `ζ_K`, and the
  nontriviality condition `zeroSeq_lt_one` (`Re < 1`, excluding the junk zero at
  `1`).  The old `zeroFree` field is a theorem (`toZeroFree`).
* **L21.2** is `Wave27L21Inputs` from Wave 27: only `zetaRH` (the Riemann
  hypothesis for `ζ`) and the literal central smooth count `localCount`.
* **L18.4** is the current guarded `L18_4Certificate`, whose pointwise
  `D^{O(1)}` and growth bounds are stated only on the paper regime `3 ≤ n`
  (the guard is necessary because `scale 0 = scale 1 = 0` and `scale 2 < 0`).

All remaining fields — `l19`, `l20_2`, `l20_4`, `l27_data`, `l27_finish`, `p1`,
`c1`–`c4`, `concrete`, `concrete_eq`, `c5Data` and `loss_le` — are unchanged
from the Wave-29/30/31 records.  The combined ledger `wave32Slots` is
definitionally the Wave-27 fully discharged ledger at the decoded L34 record and
the derived L30 leaf, so every slot total is preserved.

## What is proved

* `wave32Slots` and its definitional equalities with `wave31Slots`,
  `wave30Slots`, `wave29Slots` and `wave27Slots`, together with the full total
  equalities (`wave32Slots_total_eq_wave31Slots_total`, etc.).
* `PaperResidualFor32.toFullyDischargedInputs` — the direct
  `PaperResidualFor32 K E D → FullyDischargedInputs E D` transport.
* `PaperResidualFor32.toPaperResidualFor31` and
  `PaperResidualFor32.toPaperResidualFor30` — the two-block adapters.
* `serialized_assembled_balancedEnvelopeInfimum_from_wave32Inputs` — the
  E-generic (and `K`-generic) endpoint, with `E` quantified inside the
  conclusion.

## The exact residual list

The list has 26 entries and contains **no** `zeroFree` and **no** generic
`short_interval`:

```
[zetaRH, localCount, hbuchstab, hparity,
 hurwitzClassNumber, siegelLower, hasse, waterhouseTrace, killMass, curveBudget,
 zeroStrip, zeroSeq, zeroSeq_lt_one, cheb, range, beta0_le_half,
 l18_4, l19, l20_2, l20_4, c1, c2, c3, c4, concrete, p1]
```

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss,
probability or error is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave32

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
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2LineMinimal
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2StripBound
open Cogentic.RandomizedL21_2TailBound
open Cogentic.RandomizedL21_2TentWitness
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30Dickman
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
open Cogentic.RandomizedL34ZeroFaithful
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
open Cogentic.RandomizedPaperEndpointWave27
open Cogentic.RandomizedPaperEndpointWave28
open Cogentic.RandomizedPaperEndpointWave29
open Cogentic.RandomizedPaperEndpointWave30
open Cogentic.RandomizedPaperEndpointWave31
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## 1. The combined ledger -/

/-- **The Wave-32 ledger.**

It is the Wave-31 ledger (Wave-29 at `l30.toWave26L30Inputs`) at the L34
record decoded by `Wave30L34Inputs.toWave28L34Inputs`.  The L30 leaf reads only
the H.3 failure probability and the L34 leaf only the actual probe miss, so the
two block replacements do not change any slot. -/
noncomputable def wave32Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave31Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
    l34.toWave28L34Inputs p1

/-- The Wave-32 ledger is definitionally the Wave-31 ledger at the decoded
faithful L34 packet. -/
theorem wave32Slots_eq_wave31Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave31Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave28L34Inputs p1 := rfl

/-- The Wave-32 ledger is definitionally the Wave-30 ledger at the L30 record
obtained by deriving the sharp central count. -/
theorem wave32Slots_eq_wave30Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave30Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30.toWave26L30Inputs l34 p1 := rfl

/-- **The combined ledger is definitionally the Wave-29 ledger** at the derived
L30 record and the decoded L34 record. -/
theorem wave32Slots_eq_wave29Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30.toWave26L30Inputs l34.toWave28L34Inputs p1 := rfl

/-- **The combined ledger is definitionally the Wave-27 ledger** at the decoded
L34 sides input. -/
theorem wave32Slots_eq_wave27Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave27Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30.toWave26L30Inputs
        l34.toWave28L34Inputs.toL34ChebotarevSidesInputs p1 := rfl

/-- **The full Wave-31 slot total is preserved.** -/
theorem wave32Slots_total_eq_wave31Slots_total
    {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) :
    (wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total =
      (wave31Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave28L34Inputs p1).total := rfl

/-- **The full Wave-30 slot total is preserved.** -/
theorem wave32Slots_total_eq_wave30Slots_total
    {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) :
    (wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total =
      (wave30Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30.toWave26L30Inputs l34 p1).total := rfl

/-- **The full Wave-29 slot total is preserved.** -/
theorem wave32Slots_total_eq_wave29Slots_total
    {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave30L34Inputs K)
    (p1 : SubexpPrepassInput) :
    (wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total =
      (wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30.toWave26L30Inputs l34.toWave28L34Inputs p1).total := rfl

/-! ## 2. The combined E-generic residual record -/

/-- **The Wave-32 combined E-generic residual record.**

It combines the three reductions:

* `l30 : Wave31L30Inputs` — the sharp central count is derived from the
  Buchstab large-prime estimate and the parity fraction;
* `l34 : Wave30L34Inputs K` — the faithful strip packet, a genuine zero
  sequence of `ζ_K`, and `Re < 1` on the sequence (no vacuous `zeroFree`);
* `l21 : Wave27L21Inputs` — only `zetaRH` and the literal central count;
* `l18_4 : L18_4Certificate` — the current guarded L18.4 certificate.

All other fields are copied verbatim, and the ledger is `wave32Slots`, which is
definitionally the Wave-27 fully discharged ledger at the derived/decoded
blocks.  No loss is set to zero. -/
structure PaperResidualFor32 (K : Type u) [Field K] [NumberField K]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full guarded L18.4 certificate (`3 ≤ n` regime). -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate, with the L19.6 thin slot built from lattice
  data. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- **The L21.2 analytic input**: the Riemann hypothesis and the literal
  central short-interval smooth count. -/
  l21 : Wave27L21Inputs
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- **L30 with the sharp count derived** from the Buchstab estimate and the
  parity fraction, leaving the H.3 failure data. -/
  l30 : Wave31L30Inputs
  /-- **L34 with the faithful zero-free strip packet**, the genuine zero
  sequence and the nontriviality condition `Re < 1`. -/
  l34 : Wave30L34Inputs K
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
  /-- Adapter: the concrete C5 loss is dominated by the Wave-32 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor32

variable {K : Type u} [Field K] [NumberField K]
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor32 K E D → FullyDischargedInputs E D` directly.**

The L21.2 leaf is the Wave-27 `{ zetaRH, localCount }` leaf, the L30 leaf is the
actual H.3 failure leaf, and the L34 leaf is the Wave-28 sides input decoded from
the faithful Wave-30 packet.  The ledger domination transfers because
`wave32Slots` unfolds to the fully discharged ledger `wave27Slots`. -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor32 K E D) :
    FullyDischargedInputs E D where
  l18_4 := I.l18_4
  l19 := I.l19.toL19FullCertificate
  l20_2 := wave14L20_2Leaf I.l20_2
  l20_4 := I.l20_4.toSubexpLeaf
  l21_2 := wave14L21_2Leaf I.l21.toL21_2LeafData
  l27_1 := wave15L27Leaf I.l27_data I.l27_finish
  l30 := I.l30.toWave26L30Inputs.toSubexpLeaf
  l34 := wave15L34Leaf I.l34.toWave28L34Inputs.toL34ChebotarevSidesInputs
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
    simpa only [wave32Slots, wave31Slots, wave29Slots, wave27Slots] using
      I.loss_le n hN

/-- **`PaperResidualFor32 K E D → PaperResidualFor31 E D`.**  Only the L34 block
changes: the faithful packet is decoded by `toWave28L34Inputs`, and the ledger is
definitionally the Wave-31 ledger. -/
noncomputable def toPaperResidualFor31 (I : PaperResidualFor32 K E D) :
    PaperResidualFor31 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34.toWave28L34Inputs
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
    simpa only [wave32Slots, wave31Slots] using I.loss_le n hN

/-- **`PaperResidualFor32 K E D → PaperResidualFor30 K E D`.**  Only the L30 block
changes: the sharp count is derived by `toWave26L30Inputs`, and the ledger is
definitionally the Wave-30 ledger. -/
noncomputable def toPaperResidualFor30 (I : PaperResidualFor32 K E D) :
    PaperResidualFor30 K E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30.toWave26L30Inputs
  l34 := I.l34
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
    simpa only [wave32Slots, wave31Slots, wave30Slots] using I.loss_le n hN

/-- **`PaperResidualFor32 K E D → PaperResidualFor29 E D`.**  Both blocks are
decoded, and the ledger is definitionally the Wave-29 ledger. -/
noncomputable def toPaperResidualFor29 (I : PaperResidualFor32 K E D) :
    PaperResidualFor29 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30.toWave26L30Inputs
  l34 := I.l34.toWave28L34Inputs
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
    simpa only [wave32Slots, wave31Slots, wave29Slots] using I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor32 K E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- The transport to Wave 31 changes only the L34 block. -/
theorem toPaperResidualFor31_l34 (I : PaperResidualFor32 K E D) :
    (I.toPaperResidualFor31).l34 = I.l34.toWave28L34Inputs := rfl

/-- The transported Wave-31 `zeroFree` field is derived from the faithful
packet, not assumed. -/
theorem toPaperResidualFor31_l34_zeroFree (I : PaperResidualFor32 K E D) :
    (I.toPaperResidualFor31).l34.zeroFree = I.l34.toZeroFree := rfl

/-- The transport to Wave 30 changes only the L30 block. -/
theorem toPaperResidualFor30_l30 (I : PaperResidualFor32 K E D) :
    (I.toPaperResidualFor30).l30 = I.l30.toWave26L30Inputs := rfl

/-- The transported L30 `short_interval` is the derived theorem, not an assumed
field. -/
theorem toPaperResidualFor30_l30_short_interval (I : PaperResidualFor32 K E D) :
    (I.toPaperResidualFor30).l30.counts.short_interval =
      I.l30.counts.short_interval := rfl

/-- The transports keep the L21 block and the H.3 failure probability. -/
theorem toPaperResidualFor29_l21_l30_loss (I : PaperResidualFor32 K E D) (n : ℕ) :
    (I.toPaperResidualFor29).l21 = I.l21 ∧
      (I.toPaperResidualFor29).l30.toSubexpLeaf.loss n =
        I.l30.failure.failure n :=
  ⟨rfl, rfl⟩

end PaperResidualFor32

/-- **The schedule-indexed form of the Wave-32 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor32Schedule (K : Type u) [Field K] [NumberField K]
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor32 K (E s) D

/-! ## 3. The E-generic endpoint -/

/-- **Wave-32 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K` and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor32 K (E s) D` record, the kernel-checked driver
outputs a permutation of `n.primeFactorsList` and has expected serialized bit
cost eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The record combines the Wave-31 L30 block (Buchstab + parity, with the sharp
count derived), the Wave-30 L34 block (faithful strip packet and genuine zero
sequence, with `zeroFree` derived), the Wave-27 L21.2 block (`zetaRH` and the
central count) and the current guarded L18.4 certificate.  The epoch family `E`
is quantified inside the conclusion. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave32Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor32 K (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave31Inputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF E hI
  exact hmain E fun s D hvalid => (hI s D hvalid).toPaperResidualFor31

/-! ## 4. Residual accounting -/

/-- The field names of `PaperResidualFor32`.  The combined record has the same
18 structural fields as the Wave-30/31 records; the replacements are inside
`l30` and `l34`. -/
def wave32FieldNames : List String :=
  ["l18_4", "l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave32FieldNames_length : wave32FieldNames.length = 18 := rfl

/-- **The exact combined residual list (analytic fields only).**

The Wave-31 L30 entry `short_interval` is replaced by `hbuchstab` and `hparity`,
and the Wave-30 L34 entry `zeroFree` is replaced by `zeroStrip`, `zeroSeq` and
`zeroSeq_lt_one`.  The first line is `RiemannZetaZerosOnLine` and the two
L21/L30 analytic blocks; the second the L27 class-number/Siegel/Hasse/
Waterhouse/kill-law/budget block; the third the L34 faithful-strip/
effective-Chebotarev/range block; the fourth the L18.4/L19/L20 certificates,
C1–C4/concrete and P1.

Note that `cz_pos` and `p_ge_two` are arithmetic side data (as in Wave 30/31),
not analytic residuals, and the number field `K` is a parameter of the record. -/
def wave32RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "zeroStrip", "zeroSeq", "zeroSeq_lt_one", "cheb", "range", "beta0_le_half",
   "l18_4", "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

theorem wave32RemainingFieldNames_length :
    wave32RemainingFieldNames.length = 26 := rfl

/-- **The residual list does not contain the vacuous sequence-indexed
`zeroFree` field.** -/
theorem wave32_no_zeroFree_residual :
    wave32RemainingFieldNames.all (fun s => decide (s ≠ "zeroFree")) = true := by
  decide

/-- **The residual list does not contain the generic sharp central
`short_interval` field.** -/
theorem wave32_no_shortInterval_residual :
    wave32RemainingFieldNames.all (fun s => decide (s ≠ "short_interval")) = true := by
  decide

/-- The residual list contains the explicit Buchstab/parity and faithful-strip
entries. -/
theorem wave32_residual_blocks :
    wave32RemainingFieldNames.contains "hbuchstab" = true ∧
      wave32RemainingFieldNames.contains "hparity" = true ∧
      wave32RemainingFieldNames.contains "zeroStrip" = true ∧
      wave32RemainingFieldNames.contains "zeroSeq" = true ∧
      wave32RemainingFieldNames.contains "zeroSeq_lt_one" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

variable {K : Type u} [Field K] [NumberField K]
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The complete remaining L30 analytic input** is the Buchstab large-prime
estimate together with the odd-half parity fraction; the sharp count is a
theorem of the record. -/
theorem wave32_l30_remaining (I : PaperResidualFor32 K E D) :
    BuchstabLargePrimeShortIntervalLower I.l30.counts.c I.l30.counts.p
        I.l30.counts.ε ∧
      CentralOddHalfParity I.l30.counts.θ I.l30.counts.p I.l30.counts.ε :=
  ⟨I.l30.counts.hbuchstab, I.l30.counts.hparity⟩

/-- **The sharp central count is derived** with the effective constant
`θ * c`. -/
theorem wave32_l30_short_interval_derived (I : PaperResidualFor32 K E D) :
    YounisOddPaperSharpIntervalCount
      (I.l30.counts.θ * I.l30.counts.c) I.l30.counts.p I.l30.counts.ε :=
  I.l30.counts.short_interval

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave32_l21_remaining (I : PaperResidualFor32 K E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L34 analytic input is the faithful packet**, not
the vacuous sequence-indexed field. -/
theorem wave32_l34_remaining (I : PaperResidualFor32 K E D) :
    DedekindZetaStripInput K I.l34.beta0 I.l34.cz I.l34.discLog ∧
      0 < I.l34.cz ∧
      (∀ n, I.l34.zeroRealPart n < 1) ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog ∧
      (∀ n, I.l34.beta0 n ≤ 1 / 2) :=
  ⟨I.l34.zeroStrip, I.l34.cz_pos, I.l34.zeroSeq_lt_one, I.l34.cheb,
    I.l34.range, I.l34.beta0_le_half⟩

/-- The sequence carries genuine zeros of `ζ_K` with the recorded real parts. -/
theorem wave32_l34_zeroSeq (I : PaperResidualFor32 K E D) :
    (∀ n, NumberField.dedekindZeta K (I.l34.zeroSeq.zero n) = 0) ∧
      I.l34.zeroSeq.realPart = I.l34.zeroRealPart :=
  ⟨I.l34.zeroSeq.isZero, I.l34.zeroSeq_realPart⟩

/-- **The old zero-free field is derived from the faithful packet**, not
assumed. -/
theorem wave32_l34_zeroFree_derived (I : PaperResidualFor32 K E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz I.l34.discLog :=
  I.l34.toZeroFree

/-- The L30 loss is exactly the H.3 failure probability and the L34 loss is
exactly the actual probe miss: the combination changes no loss. -/
theorem wave32_losses (I : PaperResidualFor32 K E D) (n : ℕ) :
    (wave15L34Leaf I.l34.toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
        I.l34.actualMiss n ∧
      I.l30.toSubexpLeaf.loss n = I.l30.failure.failure n :=
  ⟨I.l34.toWave28L34Inputs_loss_eq n, Wave31L30Inputs.loss_eq I.l30 n⟩

/-! ## Axiom audit -/

#print axioms wave32Slots
#print axioms wave32Slots_eq_wave31Slots
#print axioms wave32Slots_eq_wave30Slots
#print axioms wave32Slots_eq_wave29Slots
#print axioms wave32Slots_eq_wave27Slots
#print axioms wave32Slots_total_eq_wave31Slots_total
#print axioms wave32Slots_total_eq_wave30Slots_total
#print axioms wave32Slots_total_eq_wave29Slots_total
#print axioms PaperResidualFor32.toFullyDischargedInputs
#print axioms PaperResidualFor32.toPaperResidualFor31
#print axioms PaperResidualFor32.toPaperResidualFor30
#print axioms PaperResidualFor32.toPaperResidualFor29
#print axioms PaperResidualFor32.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor32.toPaperResidualFor31_l34
#print axioms PaperResidualFor32.toPaperResidualFor31_l34_zeroFree
#print axioms PaperResidualFor32.toPaperResidualFor30_l30
#print axioms PaperResidualFor32.toPaperResidualFor30_l30_short_interval
#print axioms PaperResidualFor32.toPaperResidualFor29_l21_l30_loss
#print axioms PaperResidualFor32Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave32Inputs
#print axioms wave32FieldNames_length
#print axioms wave32RemainingFieldNames_length
#print axioms wave32_no_zeroFree_residual
#print axioms wave32_no_shortInterval_residual
#print axioms wave32_residual_blocks
#print axioms wave32_l30_remaining
#print axioms wave32_l30_short_interval_derived
#print axioms wave32_l21_remaining
#print axioms wave32_l34_remaining
#print axioms wave32_l34_zeroSeq
#print axioms wave32_l34_zeroFree_derived
#print axioms wave32_losses

end Cogentic.RandomizedPaperEndpointWave32
