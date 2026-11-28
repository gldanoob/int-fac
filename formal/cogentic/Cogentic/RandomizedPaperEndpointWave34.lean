import Cogentic.RandomizedPaperEndpointWave33
import Cogentic.RandomizedL18_4CertificateGRH

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 34: the Wave-33 residual record with the GRH-constructed L18.4 certificate

Wave 33 combined the three analytic reductions into `PaperResidualFor33 K E D`:

* the Buchstab/parity L30 leaf `Wave31L30Inputs`,
* the faithful/stark-derived L34 block `Wave33L34Inputs K`,
* the RH-only L21.2 leaf `Wave27L21Inputs`,

but it still carried an opaque `l18_4 : L18_4Certificate` field.  The file
`RandomizedL18_4CertificateGRH` constructs that certificate from the critical
line: `paperCertificate line : L18_4Certificate`.  This file removes the field
entirely.

`PaperResidualFor34 line K E D` is the Wave-33 record with `l18_4` deleted; its
ledger is `wave34Slots line … = wave33Slots (paperCertificate line) …`, i.e. the
Wave-33 ledger at the constructed certificate.  The certificate's thin
fraction is `paperThin line n = 1 / paperR line n`, which is strictly positive
(`paperCertificate_loss_pos`), so the L18.4 slot of the ledger is genuinely
positive and nothing is set to zero.

## What is proved

* `wave34Slots` and its definitional equalities with `wave33Slots` at
  `paperCertificate line` and with the fully discharged `wave27Slots`.
* `PaperResidualFor34.toPaperResidualFor33` — filling
  `l18_4 := paperCertificate line`.
* `PaperResidualFor34.toFullyDischargedInputs`.
* `serialized_assembled_balancedEnvelopeInfimum_from_wave34Inputs` — the
  `K`-generic and `E`-generic endpoint, with `E` quantified inside the
  conclusion and the same interval for `balancedEnvelopeInfimum`.
* `wave34Slots_l18_4_slot` and `wave34_l18_4_loss_pos` — the constructed
  certificate still contributes its positive `1/R` loss.

## The exact residual list

The list is the Wave-33 list (26 entries) minus `l18_4`, hence 25 entries:

```
[zetaRH, localCount, hbuchstab, hparity,
 hurwitzClassNumber, siegelLower, hasse, waterhouseTrace, killMass, curveBudget,
 zeroStrip, zeroSeq, zeroSeq_lt_one, cheb, range, beta0_le_half,
 l19, l20_2, l20_4, c1, c2, c3, c4, concrete, p1]
```

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss,
probability or error is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave34

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
open Cogentic.RandomizedPaperEndpointWave33
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## 1. The Wave-34 ledger -/

/-- **The Wave-34 ledger.**  It is the Wave-33 ledger at the L18.4 certificate
constructed from the critical line, `paperCertificate line`.  The L34, L30 and
L21 blocks are the Wave-33 ones. -/
noncomputable def wave34Slots {K : Type u} [Field K] [NumberField K]
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave33Slots (paperCertificate line) l19 l20_2 l20_4 l21 l27_data l27_finish
    l30 l34 p1

/-- The Wave-34 ledger is definitionally the Wave-33 ledger at the constructed
certificate. -/
theorem wave34Slots_eq_wave33Slots {K : Type u} [Field K] [NumberField K]
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave34Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave33Slots (paperCertificate line) l19 l20_2 l20_4 l21 l27_data
        l27_finish l30 l34 p1 := rfl

/-- **The Wave-34 ledger is definitionally the fully discharged Wave-27
ledger** at the decoded blocks and the constructed certificate. -/
theorem wave34Slots_eq_wave27Slots {K : Type u} [Field K] [NumberField K]
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave34Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave27Slots (paperCertificate line) l19 l20_2 l20_4 l21 l27_data
        l27_finish l30.toWave26L30Inputs
        l34.toWave28L34Inputs.toL34ChebotarevSidesInputs p1 := rfl

/-- **The L18.4 slot of the Wave-34 ledger is the constructed certificate's
loss**, not zero: it is the thin fraction `1/R` plus the cell deficit. -/
theorem wave34Slots_l18_4_slot {K : Type u} [Field K] [NumberField K]
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) :
    wave34Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1
        C5Leaf.rationalGoodEnvironments =
      (paperCertificate line).toInputs.loss := rfl

/-- **The constructed L18.4 slot is genuinely positive.**  The certificate loss
contains the thin fraction `1/R`, which is strictly positive; this is the same
positive loss recorded for the Wave-33 certificate, not a zero placeholder. -/
theorem wave34_l18_4_loss_pos {K : Type u} [Field K] [NumberField K]
    (line : DirichletLZerosOnLine) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave33L34Inputs K)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    0 < wave34Slots line l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1
      C5Leaf.rationalGoodEnvironments n := by
  rw [wave34Slots_l18_4_slot]
  exact paperCertificate_loss_pos line n

/-- The constructed certificate's thin fraction is still `1/R`. -/
theorem wave34_l18_4_thin_eq (line : DirichletLZerosOnLine) (n : ℕ) :
    (paperCertificate line).toInputs.thin n = 1 / (paperR line n : ℝ) := rfl

/-- The thin fraction is strictly positive: `1/R > 0`. -/
theorem wave34_l18_4_thin_pos (line : DirichletLZerosOnLine) (n : ℕ) :
    0 < (paperCertificate line).toInputs.thin n := by
  rw [wave34_l18_4_thin_eq]
  exact paperThin_pos line n

/-! ## 2. The combined residual record without `l18_4` -/

/-- **The Wave-34 combined residual record.**

It is the Wave-33 record with the `l18_4` field removed:

* `l30 : Wave31L30Inputs` — the Buchstab/parity L30 leaf;
* `l34 : Wave33L34Inputs K` — the faithful strip packet with the Stark
  arithmetic replacement (no `stark` and no `zeroFree` field);
* `l21 : Wave27L21Inputs` — only `zetaRH` and the literal central count;
* the L18.4 certificate is **not a field**: it is the constructed
  `paperCertificate line`, used in the ledger.

All other fields are copied verbatim from the Wave-33 record.  The ledger is
`wave34Slots line …`, which is definitionally the Wave-33 ledger at the
constructed certificate.  The certificate loss is the genuine positive
`1/R` thin fraction, so no loss is set to zero. -/
structure PaperResidualFor34 (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
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
  /-- Adapter: the concrete C5 loss is dominated by the Wave-34 ledger at the
  constructed L18.4 certificate. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave34Slots line l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor34

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor34 line K E D → PaperResidualFor33 K E D`.**  The only
change is `l18_4`, filled with the constructed `paperCertificate line`; the C5
adapter is unchanged because `wave34Slots` is definitionally `wave33Slots` at
that certificate. -/
noncomputable def toPaperResidualFor33 (I : PaperResidualFor34 line K E D) :
    PaperResidualFor33 K E D where
  l18_4 := paperCertificate line
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
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
    simpa only [wave34Slots] using I.loss_le n hN

/-- The transported certificate is the constructed one. -/
theorem toPaperResidualFor33_l18_4 (I : PaperResidualFor34 line K E D) :
    (I.toPaperResidualFor33).l18_4 = paperCertificate line := rfl

/-- The transport leaves the C5 loss adapter unchanged, at the constructed
certificate. -/
theorem toPaperResidualFor33_loss_le (I : PaperResidualFor34 line K E D)
    (n : ℕ) (hN : 3 ≤ n) :
    c5TotalLoss hN (I.concrete n hN) (I.c5Data.toC5 n hN) ≤
      (wave33Slots (paperCertificate line) I.l19 I.l20_2 I.l20_4 I.l21
        I.l27_data I.l27_finish I.l30 I.l34 I.p1).total n :=
  I.loss_le n hN

/-- **`PaperResidualFor34 line K E D → FullyDischargedInputs E D` directly.**
The L18.4 certificate is the constructed one, the L30 leaf is the actual H.3
failure, the L34 leaf is decoded from the faithful packet, and the ledger
unfolds to the fully discharged Wave-27 ledger. -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor34 line K E D) :
    FullyDischargedInputs E D where
  l18_4 := paperCertificate line
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
    simpa only [wave34Slots, wave33Slots, wave32Slots, wave31Slots, wave29Slots,
      wave27Slots] using I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor34 line K E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- **The Stark field remains derived** from the Wave-33 L34 block, not stored. -/
theorem stark_derived (I : PaperResidualFor34 line K E D) :
    StarkExceptionalZeroInput I.l34.beta0 I.l34.F I.l34.discLog :=
  Wave33L34Inputs.toStark I.l34

/-- **The old `zeroFree` field remains derived** from the faithful strip
packet, not stored. -/
theorem zeroFree_derived (I : PaperResidualFor34 line K E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz
      I.l34.discLog :=
  Wave33L34Inputs.toZeroFree I.l34

/-- The L30 loss is exactly the H.3 failure probability and the L34 loss is
exactly the actual probe miss. -/
theorem losses (I : PaperResidualFor34 line K E D) (n : ℕ) :
    (wave15L34Leaf I.l34.toWave28L34Inputs.toL34ChebotarevSidesInputs).loss n =
        I.l34.actualMiss n ∧
      I.l30.toSubexpLeaf.loss n = I.l30.failure.failure n :=
  ⟨I.l34.toWave28L34Inputs_loss_eq n, Wave31L30Inputs.loss_eq I.l30 n⟩

end PaperResidualFor34

/-- **The schedule-indexed form of the Wave-34 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor34Schedule (line : DirichletLZerosOnLine)
    (K : Type u) [Field K] [NumberField K]
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor34 line K (E s) D

/-! ## 3. The E-generic endpoint -/

/-- **Wave-34 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** number field
`K` and every balanced-schedule epoch family `E` which, at every valid ceiling,
carries a `PaperResidualFor34 line K (E s) D` record, the kernel-checked driver
outputs a permutation of `n.primeFactorsList` and has expected serialized bit
cost eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The record carries **no L18.4 hypothesis**: the certificate is the constructed
`paperCertificate line`.  The remaining blocks are the Wave-31 L30 leaf, the
Wave-33 faithful/stark-derived L34 block and the Wave-27 RH-only L21.2 leaf.
The epoch family `E` is quantified inside the conclusion. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave34Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (K : Type u) [Field K] [NumberField K],
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor34 line K (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave33Inputs line
  refine ⟨k, sound, ?_⟩
  intro K instK instNF E hI
  exact hmain (K := K) E fun s D hvalid => (hI s D hvalid).toPaperResidualFor33

/-! ## 4. Residual accounting -/

/-- The field names of `PaperResidualFor34`; there is no `l18_4` field. -/
def wave34FieldNames : List String :=
  ["l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave34FieldNames_length : wave34FieldNames.length = 17 := rfl

/-- **The record no longer carries an L18.4 hypothesis.** -/
theorem wave34_no_l18_4 :
    wave34FieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- **The exact Wave-34 residual list** is the Wave-33 list minus `l18_4`. -/
def wave34RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "zeroStrip", "zeroSeq", "zeroSeq_lt_one", "cheb", "range", "beta0_le_half",
   "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

theorem wave34RemainingFieldNames_length :
    wave34RemainingFieldNames.length = 25 := rfl

/-- **The Wave-34 residual list is exactly the Wave-33 list with `l18_4`
filtered out.** -/
theorem wave34RemainingFieldNames_eq_wave33_filter :
    wave34RemainingFieldNames =
      wave33RemainingFieldNames.filter (fun s => s ≠ "l18_4") := by
  decide

/-- **The residual list does not contain the L18.4 certificate entry.** -/
theorem wave34_no_l18_4_residual :
    wave34RemainingFieldNames.all (fun s => decide (s ≠ "l18_4")) = true := by
  decide

/-- The residual list still does not contain the vacuous sequence-indexed
`zeroFree` field nor the Stark exceptional-zero field. -/
theorem wave34_no_zeroFree_no_stark_residual :
    wave34RemainingFieldNames.all (fun s => decide (s ≠ "zeroFree")) = true ∧
      wave34RemainingFieldNames.all (fun s => decide (s ≠ "stark")) = true :=
  ⟨by decide, by decide⟩

/-- The residual list contains the explicit Buchstab/parity, faithful-strip,
Stark-replacement and remaining certificate entries. -/
theorem wave34_residual_blocks :
    wave34RemainingFieldNames.contains "hbuchstab" = true ∧
      wave34RemainingFieldNames.contains "hparity" = true ∧
      wave34RemainingFieldNames.contains "zeroStrip" = true ∧
      wave34RemainingFieldNames.contains "zeroSeq" = true ∧
      wave34RemainingFieldNames.contains "zeroSeq_lt_one" = true ∧
      wave34RemainingFieldNames.contains "beta0_le_half" = true ∧
      wave34RemainingFieldNames.contains "l19" = true ∧
      wave34RemainingFieldNames.contains "l20_2" = true ∧
      wave34RemainingFieldNames.contains "l20_4" = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

variable {line : DirichletLZerosOnLine}
variable {K : Type u} [Field K] [NumberField K]
variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The L18.4 certificate is supplied, not assumed**: its two former residuals
(`W_dominates` and `cellSupply`) are theorems of the constructed certificate. -/
theorem wave34_l18_4_residuals_discharged :
    (∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, c * scale n ≤ (paperCertificate line).W n) ∧
      PrimeBinCellSupply (paperCertificate line).cellK0 :=
  paperCertificate_residuals_discharged line

/-- **The complete remaining L30 analytic input** is the Buchstab large-prime
estimate together with the odd-half parity fraction. -/
theorem wave34_l30_remaining (I : PaperResidualFor34 line K E D) :
    BuchstabLargePrimeShortIntervalLower I.l30.counts.c I.l30.counts.p
        I.l30.counts.ε ∧
      CentralOddHalfParity I.l30.counts.θ I.l30.counts.p I.l30.counts.ε :=
  ⟨I.l30.counts.hbuchstab, I.l30.counts.hparity⟩

/-- **The sharp central count is derived** with the effective constant
`θ * c`. -/
theorem wave34_l30_short_interval_derived (I : PaperResidualFor34 line K E D) :
    YounisOddPaperSharpIntervalCount
      (I.l30.counts.θ * I.l30.counts.c) I.l30.counts.p I.l30.counts.ε :=
  I.l30.counts.short_interval

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave34_l21_remaining (I : PaperResidualFor34 line K E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L34 analytic input is the faithful packet**, not
the vacuous sequence-indexed field; there is no `stark` field. -/
theorem wave34_l34_remaining (I : PaperResidualFor34 line K E D) :
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
theorem wave34_l34_zeroSeq (I : PaperResidualFor34 line K E D) :
    (∀ n, NumberField.dedekindZeta K (I.l34.zeroSeq.zero n) = 0) ∧
      I.l34.zeroSeq.realPart = I.l34.zeroRealPart :=
  ⟨I.l34.zeroSeq.isZero, I.l34.zeroSeq_realPart⟩

/-! ## Axiom audit -/

#print axioms wave34Slots
#print axioms wave34Slots_eq_wave33Slots
#print axioms wave34Slots_eq_wave27Slots
#print axioms wave34Slots_l18_4_slot
#print axioms wave34_l18_4_loss_pos
#print axioms wave34_l18_4_thin_eq
#print axioms wave34_l18_4_thin_pos
#print axioms PaperResidualFor34.toPaperResidualFor33
#print axioms PaperResidualFor34.toPaperResidualFor33_l18_4
#print axioms PaperResidualFor34.toPaperResidualFor33_loss_le
#print axioms PaperResidualFor34.toFullyDischargedInputs
#print axioms PaperResidualFor34.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor34.stark_derived
#print axioms PaperResidualFor34.zeroFree_derived
#print axioms PaperResidualFor34.losses
#print axioms PaperResidualFor34Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave34Inputs
#print axioms wave34FieldNames_length
#print axioms wave34_no_l18_4
#print axioms wave34RemainingFieldNames_length
#print axioms wave34RemainingFieldNames_eq_wave33_filter
#print axioms wave34_no_l18_4_residual
#print axioms wave34_no_zeroFree_no_stark_residual
#print axioms wave34_residual_blocks
#print axioms wave34_l18_4_residuals_discharged
#print axioms wave34_l30_remaining
#print axioms wave34_l30_short_interval_derived
#print axioms wave34_l21_remaining
#print axioms wave34_l34_remaining
#print axioms wave34_l34_zeroSeq

end Cogentic.RandomizedPaperEndpointWave34
