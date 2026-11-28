import Cogentic.RandomizedPaperEndpointWave32
import Cogentic.RandomizedPaperEndpointWave30
import Cogentic.RandomizedPaperEndpointWave28

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 33: the faithful L34 block with the Wave-28 Stark arithmetic replacement

Wave 32 combined three reductions into `PaperResidualFor32 K E D`:

* the Buchstab/parity L30 leaf `Wave31L30Inputs`,
* the faithful L34 strip packet `Wave30L34Inputs K`, and
* the `{ zetaRH, localCount }` L21.2 leaf `Wave27L21Inputs`.

The Wave-30 L34 packet already replaced the vacuous sequence-indexed
`zeroFree` field by the all-zeros strip packet
`zeroStrip : DedekindZetaStripInput K beta0 cz discLog`, a genuine zero
sequence `zeroSeq` of `ζ_K`, and the nontriviality condition `Re < 1`.  It also
inherited, from the Wave-28 reduction, the arithmetic fields

```
starkF_pos       : ∀ n, 0 < F n,
beta0_le_half    : ∀ n, beta0 n ≤ 1/2,
paperBeta0_ge_half : ∀ n, 1/2 ≤ paperBeta0 F discLog n,
```

which replace the Stark exceptional-zero input.  The **Wave-28 Stark
replacement** is exactly the derivation

```
StarkExceptionalZeroInput beta0 F discLog
  := starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0
       starkF_pos discLog_pos beta0_le_half paperBeta0_ge_half,
```

so `stark` is a theorem of the L34 block, never a field.

This file names that combination explicitly as `Wave33L34Inputs K` (a
faithful-strip L34 block with **no `stark` and no `zeroFree` field**) and
packages it in the combined record `PaperResidualFor33 K E D`.  Its L30 block is
the Wave-31 `Wave31L30Inputs` (sharp count derived from `hbuchstab`/`hparity`),
its L21 block is the Wave-27 `Wave27L21Inputs` (`zetaRH` + `localCount`), its
L18.4 block is the guarded `L18_4Certificate`, and all remaining fields are the
Wave-32 ones.

## What is proved

* `Wave33L34Inputs` has no `stark` field; `Wave33L34Inputs.toStark` derives it
  from the faithful strip block's arithmetic data, and
  `Wave33L34Inputs.toZeroFree` derives the old sequence-indexed field from the
  strip packet.
* `wave33Slots` is definitionally the Wave-32 ledger at the decoded L34 block;
  the Wave-32 and Wave-27 totals are preserved.
* `PaperResidualFor33.toPaperResidualFor32` and
  `PaperResidualFor33.toFullyDischargedInputs`.
* `serialized_assembled_balancedEnvelopeInfimum_from_wave33Inputs` — the
  `K`-generic and `E`-generic endpoint, with `E` quantified inside the
  conclusion.

## The exact residual list

The list has 26 entries and contains **neither** `zeroFree` **nor** `stark`:

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

namespace Cogentic.RandomizedPaperEndpointWave33

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
open Cogentic.RandomizedPaperEndpointWave32
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## 1. The Wave-33 L34 block -/

/-- **The Wave-33 L34 block: the faithful strip packet with the Wave-28 Stark
arithmetic replacement and no `stark` field.**

It extends the Wave-30 faithful packet, so it carries

* the all-zeros strip `DedekindZetaStripInput K beta0 cz discLog` (and
  `cz_pos`),
* a genuine zero sequence of `ζ_K` with the recorded real parts and
  `Re < 1` (excluding the junk zero at `1`),
* the Wave-28 arithmetic fields `starkF_pos`, `beta0_le_half` and
  `paperBeta0_ge_half`,

and it has **no `zeroFree` field and no `stark` field**.  Both are theorems:
`toZeroFree` reconstructs the old sequence-indexed field from the strip, and
`toStark` reconstructs Stark's exceptional-zero input from `β₀ ≤ 1/2` and
`1/2 ≤ paperBeta0`. -/
structure Wave33L34Inputs (K : Type u) [Field K] [NumberField K]
    extends Wave30L34Inputs K

namespace Wave33L34Inputs

variable {K : Type u} [Field K] [NumberField K]

/-- The Wave-30 faithful L34 block underlying the Wave-33 block. -/
abbrev toWave30 (S : Wave33L34Inputs K) : Wave30L34Inputs K :=
  S.toWave30L34Inputs

/-- The Wave-28 L34 block, with the faithful packet decoded.  Every data field
is passed through; only `zeroFree` is reconstructed. -/
abbrev toWave28L34Inputs (S : Wave33L34Inputs K) : Wave28L34Inputs :=
  S.toWave30L34Inputs.toWave28L34Inputs

/-- **The Wave-28 Stark input is derived**, never assumed as a field.  This is
the arithmetic replacement: `β₀ ≤ 1/2` (the strip/GRH half-line content) plus
`1/2 ≤ paperBeta0` gives `β₀ ≤ paperBeta0`, and `F > 0` is the paper's
factorial side condition. -/
theorem toStark (S : Wave33L34Inputs K) :
    StarkExceptionalZeroInput S.beta0 S.F S.discLog :=
  starkExceptionalZeroInput_of_le_half_of_half_le_paperBeta0
    S.starkF_pos S.range.discLog_pos S.beta0_le_half S.paperBeta0_ge_half

/-- The derived Stark field agrees with the one decoded through the Wave-28
block. -/
theorem toStark_eq_via_wave28 (S : Wave33L34Inputs K) :
    S.toStark = S.toWave28L34Inputs.toStark := rfl

/-- **The old sequence-indexed zero-free field is derived from the faithful
strip packet**, using the genuine zero sequence and `Re < 1`. -/
theorem toZeroFree (S : Wave33L34Inputs K) :
    DedekindZeroFreeInput S.beta0 S.zeroRealPart S.cz S.discLog :=
  S.toWave30L34Inputs.toZeroFree

/-- The derived `zeroFree` field is the decoded Wave-28 one. -/
theorem toZeroFree_eq_via_wave28 (S : Wave33L34Inputs K) :
    S.toZeroFree = S.toWave28L34Inputs.zeroFree := rfl

/-- The transport to the Wave-30 faithful block changes nothing; it is the
identity on the underlying data. -/
theorem toWave30_data (S : Wave33L34Inputs K) :
    S.toWave30.beta0 = S.beta0 ∧
      S.toWave30.zeroRealPart = S.zeroRealPart ∧
      S.toWave30.cz = S.cz ∧
      S.toWave30.actualMiss = S.actualMiss :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The L34 loss is still exactly the actual probe miss. -/
theorem toWave28L34Inputs_loss_eq (S : Wave33L34Inputs K) (n : ℕ) :
    (wave15L34Leaf S.toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
      S.actualMiss n :=
  S.toWave28L34Inputs.toL34ChebotarevSidesInputs_loss_eq n

end Wave33L34Inputs

/-! ## 2. The Wave-33 ledger -/

/-- **The Wave-33 ledger.**  It is the Wave-32 ledger at the Wave-30 faithful
block underlying the Wave-33 L34 block.  The L34 leaf reads only the actual
probe miss, which is unchanged, so no slot moves. -/
noncomputable def wave33Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
    l34.toWave30L34Inputs p1

/-- The Wave-33 ledger is definitionally the Wave-32 ledger at the decoded
faithful L34 block. -/
theorem wave33Slots_eq_wave32Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave33Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave30L34Inputs p1 := rfl

/-- **The Wave-33 ledger is definitionally the Wave-31 ledger** at the decoded
L34 block and the derived L30 record. -/
theorem wave33Slots_eq_wave31Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave33Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave31Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave28L34Inputs p1 := rfl

/-- **The Wave-33 ledger is definitionally the Wave-27 ledger** at the decoded
L34 sides input and the derived L30 record. -/
theorem wave33Slots_eq_wave27Slots {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave33Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave27Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30.toWave26L30Inputs
        l34.toWave28L34Inputs.toL34ChebotarevSidesInputs p1 := rfl

/-- **The full Wave-32 slot total is preserved.** -/
theorem wave33Slots_total_eq_wave32Slots_total
    {K : Type u} [Field K] [NumberField K]
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) :
    (wave33Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total =
      (wave32Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toWave30L34Inputs p1).total := rfl

/-- The L34 loss of the Wave-33 ledger is exactly the actual probe miss. -/
theorem wave33Slots_l34_loss_eq {K : Type u} [Field K] [NumberField K]
    (l34 : Wave33L34Inputs K) (n : ℕ) :
    (wave15L34Leaf l34.toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
      l34.actualMiss n :=
  l34.toWave28L34Inputs_loss_eq n

/-! ## 3. The combined E-generic residual record -/

/-- **The Wave-33 combined E-generic residual record.**

It combines the Wave-32 record with the Wave-28 Stark arithmetic replacement:

* `l30 : Wave31L30Inputs` — the Wave-31 L30 leaf: the sharp central count is
  derived from the Buchstab large-prime estimate `hbuchstab` and the parity
  fraction `hparity`;
* `l34 : Wave33L34Inputs K` — the faithful all-zeros strip packet and a genuine
  zero sequence with `Re < 1`, plus the Wave-28 arithmetic fields
  (`starkF_pos`, `beta0_le_half`, `paperBeta0_ge_half`).  There is **no `stark`
  field and no `zeroFree` field**: both are theorems of the block
  (`Wave33L34Inputs.toStark`, `Wave33L34Inputs.toZeroFree`);
* `l21 : Wave27L21Inputs` — only `zetaRH` and the literal central count;
* `l18_4 : L18_4Certificate` — the current guarded L18.4 certificate.

All other fields are copied verbatim from the Wave-32 record, and the ledger is
`wave33Slots`, which is definitionally the Wave-27 fully discharged ledger at the
derived/decoded blocks.  No loss is set to zero. -/
structure PaperResidualFor33 (K : Type u) [Field K] [NumberField K]
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
  parity fraction. -/
  l30 : Wave31L30Inputs
  /-- **L34 with the faithful strip packet and the Wave-28 Stark arithmetic
  replacement** — no `zeroFree` and no `stark` field. -/
  l34 : Wave33L34Inputs K
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
  /-- Adapter: the concrete C5 loss is dominated by the Wave-33 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave33Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor33

variable {K : Type u} [Field K] [NumberField K]
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor33 K E D → PaperResidualFor32 K E D`.**  Only the L34
block changes: the Wave-33 faithful packet is passed to the Wave-30 block.  The
ledger is definitionally the Wave-32 ledger, so the C5 loss adapter transfers
unchanged. -/
noncomputable def toPaperResidualFor32 (I : PaperResidualFor33 K E D) :
    PaperResidualFor32 K E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34.toWave30L34Inputs
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
    simpa only [wave33Slots, wave32Slots] using I.loss_le n hN

/-- **`PaperResidualFor33 K E D → FullyDischargedInputs E D` directly.**  The
L30 leaf is the actual H.3 failure, the L34 leaf is decoded from the faithful
packet through the Wave-28 block (Stark derived, zero-free derived), and the
ledger unfolds to the fully discharged Wave-27 ledger. -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor33 K E D) :
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
    simpa only [wave33Slots, wave32Slots, wave31Slots, wave29Slots,
      wave27Slots] using I.loss_le n hN

/-- **`PaperResidualFor33 K E D → PaperResidualFor31 E D`.**  The L34 block is
decoded by `toWave28L34Inputs`; the ledger is definitionally the Wave-31
ledger. -/
noncomputable def toPaperResidualFor31 (I : PaperResidualFor33 K E D) :
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
    simpa only [wave33Slots, wave32Slots, wave31Slots] using I.loss_le n hN

/-- **`PaperResidualFor33 K E D → PaperResidualFor30 K E D`.**  The L30 block
derives its sharp count and the L34 block is decoded; the ledger is
definitionally the Wave-30 ledger. -/
noncomputable def toPaperResidualFor30 (I : PaperResidualFor33 K E D) :
    PaperResidualFor30 K E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30.toWave26L30Inputs
  l34 := I.l34.toWave30L34Inputs
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
    simpa only [wave33Slots, wave32Slots, wave31Slots, wave30Slots] using
      I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor33 K E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- The transport to Wave 32 changes only the L34 block. -/
theorem toPaperResidualFor32_l34 (I : PaperResidualFor33 K E D) :
    (I.toPaperResidualFor32).l34 = I.l34.toWave30L34Inputs := rfl

/-- The transport to Wave 31 changes only the L34 block. -/
theorem toPaperResidualFor31_l34 (I : PaperResidualFor33 K E D) :
    (I.toPaperResidualFor31).l34 = I.l34.toWave28L34Inputs := rfl

/-- **The Stark field is derived from the Wave-33 L34 block**, not stored. -/
theorem stark_derived (I : PaperResidualFor33 K E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  Wave33L34Inputs.toStark I.l34

/-- **The wave-32 `zeroFree` field is derived from the faithful strip packet**,
not stored. -/
theorem zeroFree_derived (I : PaperResidualFor33 K E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz
      I.l34.discLog :=
  Wave33L34Inputs.toZeroFree I.l34

/-- The L30 loss is exactly the H.3 failure probability and the L34 loss is
exactly the actual probe miss. -/
theorem losses (I : PaperResidualFor33 K E D) (n : ℕ) :
    (wave15L34Leaf I.l34.toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
        I.l34.actualMiss n ∧
      I.l30.toSubexpLeaf.loss n = I.l30.failure.failure n :=
  ⟨I.l34.toWave28L34Inputs_loss_eq n, Wave31L30Inputs.loss_eq I.l30 n⟩

end PaperResidualFor33

/-- **The schedule-indexed form of the Wave-33 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor33Schedule (K : Type u) [Field K] [NumberField K]
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor33 K (E s) D

/-! ## 4. The E-generic endpoint -/

/-- **Wave-33 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K` and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor33 K (E s) D` record, the kernel-checked driver
outputs a permutation of `n.primeFactorsList` and has expected serialized bit
cost eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The record combines the Wave-31 L30 leaf (Buchstab + parity, sharp count
derived), the Wave-33 L34 block (faithful strip packet, Stark derived from
`β₀ ≤ 1/2` and `1/2 ≤ paperBeta0`, old `zeroFree` derived from the strip), the
Wave-27 L21.2 leaf (`zetaRH` + central count) and the guarded L18.4 certificate.
The epoch family `E` is quantified inside the conclusion. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave33Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor33 K (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave32Inputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF E hI
  exact hmain (K := K) E fun s D hvalid => (hI s D hvalid).toPaperResidualFor32

/-! ## 5. Residual accounting -/

/-- The field names of `PaperResidualFor33`.  It has the same 18 structural
fields as the Wave-30/31/32 records; the replacements are inside `l30` and
`l34`. -/
def wave33FieldNames : List String :=
  ["l18_4", "l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave33FieldNames_length : wave33FieldNames.length = 18 := rfl

/-- The field names of the Wave-33 L34 block.  It is the parent Wave-30 faithful
packet plus the single extension field; there is no `stark` and no `zeroFree`
entry. -/
def wave33L34FieldNames : List String :=
  "toWave30L34Inputs" :: wave30L34FieldNames

theorem wave33L34FieldNames_length : wave33L34FieldNames.length = 49 := rfl

/-- **There is no `stark` field in the Wave-33 L34 block.** -/
theorem wave33L34_no_stark_field :
    wave33L34FieldNames.all (fun s => decide (s ≠ "stark")) = true := by
  decide

/-- **There is no vacuous `zeroFree` field in the Wave-33 L34 block.** -/
theorem wave33L34_no_zeroFree_field :
    wave33L34FieldNames.all (fun s => decide (s ≠ "zeroFree")) = true := by
  decide

/-- **The exact combined residual list (analytic fields only).**

The Wave-31 L30 entry `short_interval` is replaced by `hbuchstab` and `hparity`;
the Wave-30 L34 entry `zeroFree` is replaced by `zeroStrip`, `zeroSeq` and
`zeroSeq_lt_one`; and the Wave-28 `stark` entry is replaced by its arithmetic
content `starkF_pos`/`beta0_le_half`/`paperBeta0_ge_half` (listed here as
`beta0_le_half`; the two remaining ones are arithmetic side data of the same
block).  The first line is the Riemann hypothesis and the L21/L30 analytic
blocks; the second the L27 class-number/Siegel/Hasse/Waterhouse/kill-law/budget
block; the third the L34 faithful-strip/effective-Chebotarev/range block; the
fourth the L18.4/L19/L20 certificates, C1–C4/concrete and P1.

Note that `cz_pos`, `p_ge_two`, `starkF_pos` and `paperBeta0_ge_half` are
arithmetic side data, not analytic residuals, and the number field `K` is a
parameter of the record. -/
def wave33RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "zeroStrip", "zeroSeq", "zeroSeq_lt_one", "cheb", "range", "beta0_le_half",
   "l18_4", "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

theorem wave33RemainingFieldNames_length :
    wave33RemainingFieldNames.length = 26 := rfl

/-- **The Wave-33 residual list is exactly the Wave-32 list**: the Wave-28 Stark
replacement removes `stark` without changing any other analytic entry. -/
theorem wave33RemainingFieldNames_eq_wave32 :
    wave33RemainingFieldNames = wave32RemainingFieldNames := rfl

/-- **The residual list does not contain the vacuous sequence-indexed
`zeroFree` field.** -/
theorem wave33_no_zeroFree_residual :
    wave33RemainingFieldNames.all (fun s => decide (s ≠ "zeroFree")) = true := by
  decide

/-- **The residual list does not contain the Stark exceptional-zero field**: it
is derived from `β₀ ≤ 1/2` and `1/2 ≤ paperBeta0`. -/
theorem wave33_no_stark_residual :
    wave33RemainingFieldNames.all (fun s => decide (s ≠ "stark")) = true := by
  decide

/-- **The residual list does not contain the generic sharp central
`short_interval` field.** -/
theorem wave33_no_shortInterval_residual :
    wave33RemainingFieldNames.all (fun s => decide (s ≠ "short_interval")) = true := by
  decide

/-- The residual list contains the explicit Buchstab/parity, faithful-strip and
Stark-replacement entries. -/
theorem wave33_residual_blocks :
    wave33RemainingFieldNames.contains "hbuchstab" = true ∧
      wave33RemainingFieldNames.contains "hparity" = true ∧
      wave33RemainingFieldNames.contains "zeroStrip" = true ∧
      wave33RemainingFieldNames.contains "zeroSeq" = true ∧
      wave33RemainingFieldNames.contains "zeroSeq_lt_one" = true ∧
      wave33RemainingFieldNames.contains "beta0_le_half" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

variable {K : Type u} [Field K] [NumberField K]
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The complete remaining L30 analytic input** is the Buchstab large-prime
estimate together with the odd-half parity fraction; the sharp count is a
theorem of the record. -/
theorem wave33_l30_remaining (I : PaperResidualFor33 K E D) :
    BuchstabLargePrimeShortIntervalLower I.l30.counts.c I.l30.counts.p
        I.l30.counts.ε ∧
      CentralOddHalfParity I.l30.counts.θ I.l30.counts.p I.l30.counts.ε :=
  ⟨I.l30.counts.hbuchstab, I.l30.counts.hparity⟩

/-- **The sharp central count is derived** with the effective constant
`θ * c`. -/
theorem wave33_l30_short_interval_derived (I : PaperResidualFor33 K E D) :
    YounisOddPaperSharpIntervalCount
      (I.l30.counts.θ * I.l30.counts.c) I.l30.counts.p I.l30.counts.ε :=
  I.l30.counts.short_interval

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave33_l21_remaining (I : PaperResidualFor33 K E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L34 analytic input is the faithful packet**, not
the vacuous sequence-indexed field; there is no `stark` field. -/
theorem wave33_l34_remaining (I : PaperResidualFor33 K E D) :
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
theorem wave33_l34_zeroSeq (I : PaperResidualFor33 K E D) :
    (∀ n, NumberField.dedekindZeta K (I.l34.zeroSeq.zero n) = 0) ∧
      I.l34.zeroSeq.realPart = I.l34.zeroRealPart :=
  ⟨I.l34.zeroSeq.isZero, I.l34.zeroSeq_realPart⟩

/-- **The Stark input is the derived Wave-28 arithmetic replacement**, not a
field of the record. -/
theorem wave33_l34_stark_derived (I : PaperResidualFor33 K E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  I.stark_derived

/-- **The old zero-free field is derived from the faithful packet**, not
assumed. -/
theorem wave33_l34_zeroFree_derived (I : PaperResidualFor33 K E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz I.l34.discLog :=
  I.zeroFree_derived

/-! ## Axiom audit -/

#print axioms Wave33L34Inputs.toWave28L34Inputs
#print axioms Wave33L34Inputs.toStark
#print axioms Wave33L34Inputs.toStark_eq_via_wave28
#print axioms Wave33L34Inputs.toZeroFree
#print axioms Wave33L34Inputs.toZeroFree_eq_via_wave28
#print axioms Wave33L34Inputs.toWave30_data
#print axioms Wave33L34Inputs.toWave28L34Inputs_loss_eq
#print axioms wave33Slots
#print axioms wave33Slots_eq_wave32Slots
#print axioms wave33Slots_eq_wave31Slots
#print axioms wave33Slots_eq_wave27Slots
#print axioms wave33Slots_total_eq_wave32Slots_total
#print axioms wave33Slots_l34_loss_eq
#print axioms PaperResidualFor33.toPaperResidualFor32
#print axioms PaperResidualFor33.toFullyDischargedInputs
#print axioms PaperResidualFor33.toPaperResidualFor31
#print axioms PaperResidualFor33.toPaperResidualFor30
#print axioms PaperResidualFor33.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor33.toPaperResidualFor32_l34
#print axioms PaperResidualFor33.toPaperResidualFor31_l34
#print axioms PaperResidualFor33.stark_derived
#print axioms PaperResidualFor33.zeroFree_derived
#print axioms PaperResidualFor33.losses
#print axioms PaperResidualFor33Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave33Inputs
#print axioms wave33FieldNames_length
#print axioms wave33L34FieldNames_length
#print axioms wave33L34_no_stark_field
#print axioms wave33L34_no_zeroFree_field
#print axioms wave33RemainingFieldNames_length
#print axioms wave33RemainingFieldNames_eq_wave32
#print axioms wave33_no_zeroFree_residual
#print axioms wave33_no_stark_residual
#print axioms wave33_no_shortInterval_residual
#print axioms wave33_residual_blocks
#print axioms wave33_l30_remaining
#print axioms wave33_l30_short_interval_derived
#print axioms wave33_l21_remaining
#print axioms wave33_l34_remaining
#print axioms wave33_l34_zeroSeq
#print axioms wave33_l34_stark_derived
#print axioms wave33_l34_zeroFree_derived

end Cogentic.RandomizedPaperEndpointWave33
