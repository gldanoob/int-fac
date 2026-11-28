import Cogentic.RandomizedPaperEndpointWave27
import Cogentic.RandomizedPaperEndpointWave28

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 29: the three reductions combined into one E-generic record

Waves 26, 27 and 28 successively cut three leaves of the paper endpoint:

* Wave 26 (`Wave26L30Inputs`) removes the upper-density, binomial and global
  lower fields of L30, leaving the sharp central count `short_interval` (plus
  the density growth and the arithmetic constants);
* Wave 27 (`Wave27L21Inputs`) removes the whole `ZetaSide` package, leaving
  exactly `zetaRH` and the literal central short-interval smooth count
  `localCount`;
* Wave 28 (`Wave28L34Inputs`) removes the `stark` field of L34, replacing it by
  its arithmetic content: `F > 0`, the GRH residual `β₀ ≤ 1/2`, and the paper's
  `1/2 ≤ paperBeta0`.

This file puts the three reductions in **one** E-generic record,
`PaperResidualFor29 (E) (D)`:

```
l21 : Wave27L21Inputs,   l30 : Wave26L30Inputs,   l34 : Wave28L34Inputs,
```

with every other field copied verbatim from the Wave-26/28 records (L18.4, L19,
L20.2, L20.4, L27, P1, C1–C4, the concrete epoch family, `concrete_eq`, the C5
data and the ledger domination `loss_le`).

The ledger `wave29Slots` is definitionally the Wave-27 ledger at the L34 record
transported by `Wave28L34Inputs.toL34ChebotarevSidesInputs`; the two transports
are proved as slot equalities:

* `wave29Slots_eq_wave27Slots` — the L34 slot;
* `wave29Slots_total_eq_wave28Slots_total` — the full total against Wave 28 at
  the same `ZetaSide` and central count (the L21 slot is the same bad-centre
  fraction, the L30 slot is the same H.3 failure leaf).

The direct transport `PaperResidualFor29.toFullyDischargedInputs` bypasses the
intermediate records; the E-generic endpoint is

`serialized_assembled_balancedEnvelopeInfimum_from_wave29Inputs`,

with the epoch family `E` quantified inside the conclusion.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss is used anywhere.

## Residual accounting

The combined analytic residual list is, with its 23 entries,

```
[zetaRH, localCount, short_interval,
 hurwitzClassNumber, siegelLower, hasse, waterhouseTrace, killMass, curveBudget,
 zeroFree, cheb, range, beta0_le_half,
 l18_4, l19, l20_2, l20_4, c1, c2, c3, c4, concrete, p1]
```

(the first line is `RiemannZetaZerosOnLine` and the two central counts, the
second the L27 class-number/Siegel/Hasse/Waterhouse/kill-law/budget block, the
third the L34 zero-free/effective-Chebotarev/range block, and the last the
L18.4/L19/L20 certificates, C1–C4/concrete and P1).
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave29

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
open Cogentic.RandomizedPaperEndpointWave27
open Cogentic.RandomizedPaperEndpointWave28
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## The combined ledger -/

/-- **The Wave-29 ledger.**  The L21 slot is the Wave-27
`{ zetaRH, localCount }` leaf, the L30 slot is the Wave-26 H.3 failure leaf,
and the L34 slot is the Wave-28 record with the Stark field derived by
`Wave28L34Inputs.toL34ChebotarevSidesInputs`.  It is definitionally the
Wave-27 ledger at the transported L34 record. -/
noncomputable def wave29Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave27Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
    l34.toL34ChebotarevSidesInputs p1

/-- **The L34 slot equality.**  The Wave-29 ledger is the Wave-27 ledger with
the Wave-28 L34 record transported through the derived Stark field. -/
theorem wave29Slots_eq_wave27Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) :
    wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave27Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30
        l34.toL34ChebotarevSidesInputs p1 := rfl

/-- The L34 loss of the combined ledger is still exactly the actual probe miss
of the Wave-28 record. -/
theorem wave29Slots_l34_loss_eq (l34 : Wave28L34Inputs) (n : ℕ) :
    (wave15L34Leaf l34.toL34ChebotarevSidesInputs).loss n = l34.actualMiss n :=
  wave15L34Leaf_loss_eq l34.toL34ChebotarevSidesInputs n

/-- **The full total equality with the Wave-28 ledger**, at the same `ZetaSide`
and central count.  The L21.2 slot is the same bad-centre fraction (Wave 27),
the L34 slot is the same actual probe miss (Wave 28), and the L30 slot is the
same H.3 failure leaf. -/
theorem wave29Slots_total_eq_wave28Slots_total
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (z : ZetaSide)
    (hcount : ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX)
    (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) :
    (wave29Slots l18_4 l19 l20_2 l20_4
        (Wave27L21Inputs.mk (zetaRH := z.rh) (localCount := hcount))
        l27_data l27_finish l30 l34 p1).total =
      (wave28Slots l18_4 l19 l20_2 l20_4
        ({ zeta := z, localCount := hcount } : ConcreteLeafResidual)
        l27_data l27_finish l30 l34 p1).total := by
  unfold wave29Slots
  rw [Cogentic.RandomizedPaperEndpointWave27.PaperResidualFor27.wave27Slots_total_eq_wave26Slots_total
      l18_4 l19 l20_2 l20_4 z hcount l27_data l27_finish l30
      l34.toL34ChebotarevSidesInputs p1]
  exact congrArg C5LossSlots.total
    (wave26Slots_eq_wave28Slots l18_4 l19 l20_2 l20_4
      ({ zeta := z, localCount := hcount } : ConcreteLeafResidual)
      l27_data l27_finish l30 l34 p1)

/-! ## The E-generic residual record -/

/-- **The Wave-29 E-generic residual record.**

It combines the three reductions:

* `l21 : Wave27L21Inputs` — only `zetaRH` and the central short count;
* `l30 : Wave26L30Inputs` — only the sharp central count `short_interval`;
* `l34 : Wave28L34Inputs` — the Stark field replaced by `β₀ ≤ 1/2`, `F > 0`
  and `1/2 ≤ paperBeta0`.

All other fields are copied from the Wave-26/28 records, and the ledger is
`wave29Slots`.  No loss is set to zero: the ledger simply reads the same three
losses as the three source records. -/
structure PaperResidualFor29
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
  /-- **The L21.2 analytic input**: the Riemann hypothesis and the literal
  central short-interval smooth count. -/
  l21 : Wave27L21Inputs
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- **L30 with both density fields derived**, leaving the sharp central
  count, the GRH lower bound, the density growth and the H.3 failure data. -/
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
  /-- Adapter: the concrete C5 loss is dominated by the wave-29 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor29

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The fully discharged inputs directly from the Wave-29 record.**

The three leaves are the Wave-27 L21.2 leaf, the Wave-26 L30 leaf and the
Wave-28 L34 leaf with derived Stark field.  The ledger domination transfers
because `wave29Slots` unfolds to the fully discharged ledger. -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor29 E D) :
    FullyDischargedInputs E D where
  l18_4 := I.l18_4
  l19 := I.l19.toL19FullCertificate
  l20_2 := wave14L20_2Leaf I.l20_2
  l20_4 := I.l20_4.toSubexpLeaf
  l21_2 := wave14L21_2Leaf I.l21.toL21_2LeafData
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
    simpa only [wave29Slots, wave27Slots] using I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor29 E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-! ## Transport to the Wave-27 record -/

/-- **`PaperResidualFor29 E D → PaperResidualFor27 E D`.**  Only the L34 record
changes: it is transported through `Wave28L34Inputs.toL34ChebotarevSidesInputs`,
which derives the Stark field.  The ledger is definitionally the same
(`wave29Slots_eq_wave27Slots`). -/
noncomputable def toPaperResidualFor27 (I : PaperResidualFor29 E D) :
    PaperResidualFor27 E D where
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
    simpa only [wave29Slots] using I.loss_le n hN

/-- The transport keeps the L21 block. -/
theorem toPaperResidualFor27_l21 (I : PaperResidualFor29 E D) :
    (I.toPaperResidualFor27).l21 = I.l21 := rfl

/-- The transport keeps the L30 block. -/
theorem toPaperResidualFor27_l30 (I : PaperResidualFor29 E D) :
    (I.toPaperResidualFor27).l30 = I.l30 := rfl

/-- The transported L34 record carries the derived Stark field, not an assumed
one. -/
theorem toPaperResidualFor27_l34_stark (I : PaperResidualFor29 E D) :
    (I.toPaperResidualFor27).l34.stark = I.l34.toStark := rfl

/-- The transport leaves the actual probe miss unchanged. -/
theorem toPaperResidualFor27_l34_actualMiss (I : PaperResidualFor29 E D) :
    (I.toPaperResidualFor27).l34.actualMiss = I.l34.actualMiss := rfl

/-! ## Transport to the Wave-28 record -/

/-- **`PaperResidualFor29 E D → PaperResidualFor28 E D`** once a `ZetaSide` is
supplied.  The L21 block becomes the `{ zeta, localCount }` residual; the L30
and L34 blocks are unchanged.  The totals agree by
`wave29Slots_total_eq_wave28Slots_total`, so the loss adapter transfers. -/
noncomputable def toPaperResidualFor28 (I : PaperResidualFor29 E D)
    (z : ZetaSide) : PaperResidualFor28 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := { zeta := z, localCount := I.l21.localCount }
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
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
    rw [← wave29Slots_total_eq_wave28Slots_total I.l18_4 I.l19 I.l20_2 I.l20_4
      z I.l21.localCount I.l27_data I.l27_finish I.l30 I.l34 I.p1]
    exact I.loss_le n hN

/-- The transport replaces only the L21 block. -/
theorem toPaperResidualFor28_l21 (I : PaperResidualFor29 E D) (z : ZetaSide) :
    (I.toPaperResidualFor28 z).l21 =
      ({ zeta := z, localCount := I.l21.localCount } : ConcreteLeafResidual) := rfl

/-- The transport keeps the L30 and L34 blocks. -/
theorem toPaperResidualFor28_l30_l34 (I : PaperResidualFor29 E D) (z : ZetaSide) :
    (I.toPaperResidualFor28 z).l30 = I.l30 ∧
      (I.toPaperResidualFor28 z).l34 = I.l34 :=
  ⟨rfl, rfl⟩

/-! ## The combined constructor -/

/-- **`PaperResidualFor28 E D → PaperResidualFor29 E D`.**  This is the
unconditional direction of the combined reduction: the Wave-29 record keeps
only `zetaRH` from the Wave-28 `ZetaSide`, and keeps the Wave-26 L30 and the
Wave-28 L34 records.  The L21.2 loss of the extracted `zetaRH` is the same
bad-centre fraction, so the ledger total is unchanged. -/
noncomputable def ofPaperResidualFor28 (I : PaperResidualFor28 E D) :
    PaperResidualFor29 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 :=
    { zetaRH := I.l21.zeta.rh
      localCount := I.l21.localCount }
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
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
    rw [wave29Slots_total_eq_wave28Slots_total I.l18_4 I.l19 I.l20_2 I.l20_4
      I.l21.zeta I.l21.localCount I.l27_data I.l27_finish I.l30 I.l34 I.p1]
    exact I.loss_le n hN

/-- The unconditional reduction replaces only the L21 block. -/
theorem ofPaperResidualFor28_l21 (I : PaperResidualFor28 E D) :
    (PaperResidualFor29.ofPaperResidualFor28 I).l21 =
      ({ zetaRH := I.l21.zeta.rh
         localCount := I.l21.localCount } : Wave27L21Inputs) := rfl

/-- The unconditional reduction keeps the L30 and L34 blocks. -/
theorem ofPaperResidualFor28_l30_l34 (I : PaperResidualFor28 E D) :
    (PaperResidualFor29.ofPaperResidualFor28 I).l30 = I.l30 ∧
      (PaperResidualFor29.ofPaperResidualFor28 I).l34 = I.l34 :=
  ⟨rfl, rfl⟩

end PaperResidualFor29

/-- **The schedule-indexed form of the Wave-29 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor29Schedule
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor29 (E s) D

/-! ## The E-generic endpoint -/

/-- **Wave-29 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** balanced
schedule epoch family `E` which, at every valid ceiling, carries a
`PaperResidualFor29 (E s) D` record, the kernel-checked driver outputs a
permutation of `n.primeFactorsList` and has expected serialized bit cost
eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The record combines the three reductions: L21.2 is only `{ zetaRH, localCount }`,
L30 only the sharp central count, and L34 has the Stark field derived.  The
epoch family `E` is quantified inside the conclusion.  The proof transports each
record to `PaperResidualFor27` and applies the Wave-27 endpoint. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave29Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor29 (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave27Inputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toPaperResidualFor27⟩

/-! ## Residual accounting -/

/-- The field names of `PaperResidualFor29`. -/
def wave29FieldNames : List String :=
  ["l18_4", "l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave29FieldNames_length : wave29FieldNames.length = 18 := rfl

/-- **The exact combined residual list (analytic fields only).**

The first line is `RiemannZetaZerosOnLine` and the two central counts; the
second is the L27 class-number/Siegel/Hasse/Waterhouse/kill-law/budget block;
the third is the L34 zero-free/effective-Chebotarev/range block; the fourth is
the L18.4/L19/L20 certificates, C1–C4/concrete and P1. -/
def wave29RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "short_interval",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "zeroFree", "cheb", "range", "beta0_le_half",
   "l18_4", "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

theorem wave29RemainingFieldNames_length :
    wave29RemainingFieldNames.length = 23 := rfl

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave29_l21_remaining (I : PaperResidualFor29 E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L30 analytic input** is the sharp central count. -/
theorem wave29_l30_remaining (I : PaperResidualFor29 E D) :
    YounisOddPaperSharpIntervalCount I.l30.counts.c I.l30.counts.p
      I.l30.counts.ε :=
  I.l30.counts.short_interval

/-- **The complete remaining L34 analytic input** is the zero-free region, the
effective Chebotarev error and the `T^6` range, plus the GRH half-line bound on
the exceptional zero.  The Stark field is derived. -/
theorem wave29_l34_remaining (I : PaperResidualFor29 E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz
        I.l34.discLog ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog ∧
      (∀ n, I.l34.beta0 n ≤ 1 / 2) :=
  ⟨I.l34.zeroFree, I.l34.cheb, I.l34.range, I.l34.beta0_le_half⟩

/-- The Stark field of the L34 block is a theorem of the recorded data. -/
theorem wave29_l34_stark_derived (I : PaperResidualFor29 E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  I.l34.toStark

/-- **The L27 block** carries the class-number Hurwitz/Siegel/Waterhouse data,
Hasse's theorem, the kill-law data and the paper's curve budget. -/
theorem wave29_l27_remaining (I : PaperResidualFor29 E D) :
    Nonempty (L27HurwitzInputs I.l27_data) ∧
      Nonempty (L27KillLawInputs I.l27_data) ∧
      HasseBound I.l27_data.p I.l27_data.orderCount ∧
      CurveBudget I.l27_data.p I.l27_data.y I.l27_data.psi
        I.l27_data.curves I.l27_data.κ I.l27_data.η ∧
      LogFactorSubexp I.l27_data.cofactor :=
  ⟨⟨I.l27_finish.hurwitz⟩, ⟨I.l27_finish.killLaw⟩, I.l27_finish.hasse,
    I.l27_finish.curve_budget, I.l27_finish.log_factor_subexp⟩

/-- The L34 loss of the record is exactly the actual probe miss, and the L30
loss exactly the H.3 failure probability: the ledger does not read any of the
reduced counting fields. -/
theorem wave29_losses (I : PaperResidualFor29 E D) (n : ℕ) :
    (wave15L34Leaf I.l34.toL34ChebotarevSidesInputs).loss n = I.l34.actualMiss n ∧
      I.l30.toSubexpLeaf.loss n = I.l30.failure.failure n :=
  ⟨wave29Slots_l34_loss_eq I.l34 n, Wave26L30Inputs.loss_eq I.l30 n⟩

/-! ## Axiom audit -/

#print axioms wave29Slots
#print axioms wave29Slots_eq_wave27Slots
#print axioms wave29Slots_l34_loss_eq
#print axioms wave29Slots_total_eq_wave28Slots_total
#print axioms PaperResidualFor29.toFullyDischargedInputs
#print axioms PaperResidualFor29.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor29.toPaperResidualFor27
#print axioms PaperResidualFor29.toPaperResidualFor27_l21
#print axioms PaperResidualFor29.toPaperResidualFor27_l30
#print axioms PaperResidualFor29.toPaperResidualFor27_l34_stark
#print axioms PaperResidualFor29.toPaperResidualFor27_l34_actualMiss
#print axioms PaperResidualFor29.toPaperResidualFor28
#print axioms PaperResidualFor29.toPaperResidualFor28_l21
#print axioms PaperResidualFor29.toPaperResidualFor28_l30_l34
#print axioms PaperResidualFor29.ofPaperResidualFor28
#print axioms PaperResidualFor29.ofPaperResidualFor28_l21
#print axioms PaperResidualFor29.ofPaperResidualFor28_l30_l34
#print axioms PaperResidualFor29Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave29Inputs
#print axioms wave29FieldNames_length
#print axioms wave29RemainingFieldNames_length
#print axioms wave29_l21_remaining
#print axioms wave29_l30_remaining
#print axioms wave29_l34_remaining
#print axioms wave29_l34_stark_derived
#print axioms wave29_l27_remaining
#print axioms wave29_losses

end Cogentic.RandomizedPaperEndpointWave29
