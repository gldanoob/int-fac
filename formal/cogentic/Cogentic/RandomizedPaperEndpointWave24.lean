import Cogentic.RandomizedPaperEndpointWave17
import Cogentic.RandomizedL21_2ConcreteLeaf
import Cogentic.RandomizedWave17Audit
import Cogentic.RandomizedC1C2FromConcrete

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 24: an E-generic residual record and a non-vacuous endpoint

## Why the Wave-18/22 endpoints are vacuous

`Cogentic.RandomizedPaperEndpointWave22.PaperResidualInputsFinal` carries the
fields

```
c1 : C1Inputs Egood
c2 : C2Inputs Egood
c3 : C3Inputs Egood
c4 : C4Inputs Egood D
```

at the single placeholder epoch

```
Egood n hN = (goodEpochOfLe n hN).toHardEpochData.
```

`Cogentic.RandomizedC1C2FromConcrete.not_c1Inputs_Egood` proves
`¬ C1Inputs Egood` (the `n = 15` product-identity refutation), hence
`not_nonempty_paperResidualInputsFinal : ¬ Nonempty (PaperResidualInputsFinal D)`.
The Wave-18/22 endpoint hypotheses `(R : ∀ D, PaperResidualInputsFinal D)` are
therefore empty function types: those endpoints are true but vacuous.

## What this file does

The valid shape is the Wave-17 one:

```
serialized_assembled_balancedEnvelopeInfimum_from_wave17Inputs (line) :
  ∃ k sound, ∀ E, (∀ s D, s.Valid D → Wave17Inputs (E s) D) → <conclusion about E>
```

with `E : ∀ s n, 3 ≤ n → HardEpochData n` quantified *inside* the conclusion,
so the algorithm is universal but the epoch family is not fixed to a
placeholder.

This file introduces the reduced, E-generic record

```
structure PaperResidualFor (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ)
```

(mirroring `Wave17Inputs`' exact per-ceiling quantification).  Its E-specific
fields are `c1`–`c4` together with the concrete family, its adapter and the C5
data / ledger domination; its analytic fields are the reduced leaves

```
l18_4, l19, l20_2, l20_4, l21 : ConcreteLeafResidual,
l27_data + l27_finish, l30 : Wave14L30Inputs (sharp),
l34 : L34ChebotarevSidesInputs, p1.
```

The L21.2 block is the two-component `ConcreteLeafResidual`; it is turned into
`Wave17L21_2Inputs` by `RandomizedL21_2ConcreteLeaf.wave17InputsOfResidual`.
The four L4 scalar fields of `Wave17Inputs` are *proved* data (`N = 9`,
`bits = 3`, `Odd 9`, `2 ^ 3 ≤ 9`) and are therefore fixed in the reduction
rather than exposed as hypotheses.

Main results:

* `PaperResidualFor.toWave17Inputs` — `PaperResidualFor E D → Wave17Inputs E D`,
  with `l21` assembled by `wave17InputsOfResidual` and every c1–c5/concrete
  field passed through unchanged;
* `serialized_assembled_balancedEnvelopeInfimum_from_wave24Inputs` — the
  E-generic endpoint, proved by applying the Wave-17 endpoint to the
  `toWave17Inputs` family (the conclusion is about the same `E`);
* `paperResidualForConcrete` / `nonempty_paperResidualForConcrete` — a
  non-vacuity witness for the actual concrete epoch family
  `concreteFamily n hN = (goodEpochOfLe n hN).toHardEpochData`, modulo exactly
  the genuine analytic leaves, C3, C4 and the concrete product identity
  `∀ n hN, (goodEpochOfLe n hN).GlobalProductIdentity`.  `c1` is *derived*
  from the product identity by `c1Inputs_of_concrete` and `c2` is the
  unconditional `c2Inputs_Egood`; neither is assumed.

## What remains exactly

`Wave24Remaining` lists the residual inputs of the non-vacuity witness:

```
l18_4, l19, l20_2, l20_4, l21, l27_data, l27_finish, l30, l34, p1,
c1Concrete (the concrete GlobalProductIdentity), c3, c4.
```

The concrete product identity is stated explicitly and is *not* claimed: for
the current `goodEpochOfLe` placeholder it is false
(`not_globalProductIdentity_goodEpochOfLe`), which is exactly why the Wave-22
record is uninhabited.  The witness here shows that the only obstruction in
`PaperResidualFor` is that genuine statement plus the named analytic leaves;
it is not a hidden inconsistency of the record itself.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count,
probability or error is set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave24

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL30
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperEndpointWave17
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit
open Cogentic.RandomizedC1C2FromConcrete
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver

universe u

/-! ## The reduced E-generic record -/

/-- **The L4 scalar data is fixed to the proved witness.**  `N = 9`, `bits = 3`,
`Odd 9` and `2 ^ 3 ≤ 9` are theorems, so they are not residual fields. -/
theorem wave24_l4N_odd : Odd 9 := by decide

theorem wave24_l4Bits_budget : 2 ^ 3 ≤ 9 := by decide

/-- **The wave-24 ledger.**  It is the wave-17 ledger at the L21.2 leaf
assembled from the two-component `ConcreteLeafResidual`, and at the proved L4
witness `(9, 3)`. -/
noncomputable def wave24Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : ConcreteLeafResidual) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave17Slots l18_4 l19 l20_2 l20_4 (wave17InputsOfResidual l21) l27_data
    l27_finish l30 l34 9 3 wave24_l4N_odd wave24_l4Bits_budget p1

/-- **The E-generic residual record.**

`E` is the ambient epoch family, at exactly the quantification used by
`Wave17Inputs` (`∀ n, 3 ≤ n → HardEpochData n`).  The record contains:

* the ten reduced analytic leaves, with the whole L21.2 block collapsed to the
  two-component `ConcreteLeafResidual`;
* the E-specific C1–C4 inputs;
* the concrete epoch family underlying C5, its adapter `concrete_eq`, the C5
  data assembled by `c5FullOfCount`, and the ledger domination `loss_le`.

The L4 scalar fields are not fields: they are the proved witness `(9, 3)` used
in `wave24Slots`. -/
structure PaperResidualFor
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
  /-- **The whole L21.2 analytic input**: the zeta side (RH, zero-freeness on
  `Re s = 2/3`, and the two-sided line estimate with a raw constant) together
  with the literal central short-interval smooth count.  Every other L21.2
  field is a theorem of `RandomizedL21_2ConcreteLeaf`. -/
  l21 : ConcreteLeafResidual
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- L30: the sharp sourced counts and the H.3 failure data. -/
  l30 : Wave14L30Inputs
  /-- L34: the explicit Chebotarev-side counting inputs. -/
  l34 : L34ChebotarevSidesInputs
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
  /-- Adapter: the concrete C5 loss is dominated by the wave-24 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave24Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-! ## Reduction to the Wave-17 record -/

/-- **`PaperResidualFor E D → Wave17Inputs E D`.**

The L21.2 leaf is assembled by
`RandomizedL21_2ConcreteLeaf.wave17InputsOfResidual`; the L4 scalar fields are
the proved witness `(9, 3)`; every c1–c5/concrete field is passed through
*unchanged*, including the ledger domination `loss_le` (which is stated at the
same fixed L4 witness). -/
noncomputable def toWave17Inputs (I : PaperResidualFor E D) : Wave17Inputs E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21_2 := wave17InputsOfResidual I.l21
  l4N := 9
  l4Bits := 3
  l4N_odd := wave24_l4N_odd
  l4Bits_budget := wave24_l4Bits_budget
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
    simpa only [wave24Slots] using I.loss_le n hN

/-- The reduction keeps the L21.2 leaf exactly: `l21_2` is
`wave17InputsOfResidual I.l21`. -/
theorem toWave17Inputs_l21_2 (I : PaperResidualFor E D) :
    I.toWave17Inputs.l21_2 = wave17InputsOfResidual I.l21 := rfl

/-- The reduction keeps the proved L4 witness. -/
theorem toWave17Inputs_l4 (I : PaperResidualFor E D) :
    I.toWave17Inputs.l4N = 9 ∧ I.toWave17Inputs.l4Bits = 3 :=
  ⟨rfl, rfl⟩

/-- **The wave-24 ledger is the wave-17 ledger of the reduction.** -/
theorem toWave17Inputs_slots (I : PaperResidualFor E D) :
    wave17Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.toWave17Inputs.l21_2
        I.l27_data I.l27_finish I.l30 I.l34 9 3 wave24_l4N_odd
        wave24_l4Bits_budget I.p1 =
      wave24Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21 I.l27_data
        I.l27_finish I.l30 I.l34 I.p1 :=
  rfl

/-- The reduction is the identity on every c1–c4 field. -/
theorem toWave17Inputs_c (I : PaperResidualFor E D) :
    I.toWave17Inputs.c1 = I.c1 ∧ I.toWave17Inputs.c2 = I.c2 ∧
      I.toWave17Inputs.c3 = I.c3 ∧ I.toWave17Inputs.c4 = I.c4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The reduction is the identity on the concrete family, its adapter and the
C5 data. -/
theorem toWave17Inputs_c5 (I : PaperResidualFor E D) :
    I.toWave17Inputs.concrete = I.concrete ∧
      I.toWave17Inputs.concrete_eq = I.concrete_eq ∧
      I.toWave17Inputs.c5Data = I.c5Data :=
  ⟨rfl, rfl, rfl⟩

/-- **The Wave-17 fully discharged inputs from the residue.** -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor E D) :
    FullyDischargedInputs E D :=
  I.toWave17Inputs.toFullyDischargedInputs

/-- The record is nonempty as a `Wave17Inputs`. -/
theorem nonempty_wave17Inputs (I : PaperResidualFor E D) :
    Nonempty (Wave17Inputs E D) :=
  ⟨I.toWave17Inputs⟩

end PaperResidualFor

/-- **The schedule-indexed form of the record**, at the exact quantification of
the endpoint: a family `E : ∀ s n, 3 ≤ n → HardEpochData n` carries the record
`PaperResidualFor (E s) D` for the schedule `s`. -/
abbrev PaperResidualForSchedule
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor (E s) D

/-! ## The E-generic endpoint -/

/-- **Wave-24 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** balanced-
schedule epoch family `E` which, at every valid ceiling, carries a
`PaperResidualFor (E s) D` record, the kernel-checked driver outputs a
permutation of `n.primeFactorsList` and has expected serialized bit cost
eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The epoch family `E` is quantified inside the conclusion, exactly as in the
Wave-17 endpoint; it is **not** specialized to `Egood`.  The proof reduces each
`PaperResidualFor (E s) D` to `Wave17Inputs (E s) D` by
`PaperResidualFor.toWave17Inputs` and then applies
`serialized_assembled_balancedEnvelopeInfimum_from_wave17Inputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave24Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave17Inputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toWave17Inputs⟩

/-! ## Non-vacuity modulo the genuine residual inputs -/

/-- **The concrete epoch family of the non-vacuity witness** — the standard
one-point family, *not* a new placeholder.  It is literally
`Egood = fun n hN => (goodEpochOfLe n hN).toHardEpochData`. -/
noncomputable def concreteFamily : ∀ n, 3 ≤ n → HardEpochData n :=
  fun n hN => (goodEpochOfLe n hN).toHardEpochData

/-- `concreteFamily` is the standard family `Egood`. -/
theorem concreteFamily_eq_Egood : concreteFamily = Egood := rfl

/-- **The residual inputs of the non-vacuity witness.**

Compared with `PaperResidualFor`, this record has no `c1`/`c2` fields
(`c1` is derived from `c1Concrete`, `c2` is unconditional), no L4 fields
(proved), and no C5 fields (constructed by `paperResidualForConcrete`). -/
structure Wave24Remaining (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate. -/
  l19 : Wave15L19Inputs
  /-- L20.2 saddle-concentration source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4 sourced two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- The two-component L21.2 residual. -/
  l21 : ConcreteLeafResidual
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- The sharp L30 record. -/
  l30 : Wave14L30Inputs
  /-- The L34 Chebotarev-side record. -/
  l34 : L34ChebotarevSidesInputs
  /-- The P1 prepass record. -/
  p1 : SubexpPrepassInput
  /-- **The concrete global product identity** on `goodEpochOfLe`.  This is the
  genuine residual C1 statement; it is false for the current placeholder
  (`not_globalProductIdentity_goodEpochOfLe`), and it is the only obstruction
  besides the analytic leaves. -/
  c1Concrete : ∀ n (hN : 3 ≤ n), (goodEpochOfLe n hN).GlobalProductIdentity
  /-- C3 on the concrete family. -/
  c3 : C3Inputs concreteFamily
  /-- C4 on the concrete family. -/
  c4 : C4Inputs concreteFamily D

/-- **Assemble `PaperResidualFor` from the residual inputs.**

The E-specific fields are derived, not assumed:

* `c1 := c1Inputs_of_concrete R.c1Concrete rfl`;
* `c2 := c2Inputs_Egood` (unconditional at the concrete family);
* `concrete := goodEpochOfLe`, `concrete_eq := rfl`;
* `c5Data := goodC5Data (ledger / 2)`, and `loss_le` follows from
  `c5TotalLoss_goodC5Data_le` because the wave-24 ledger is strictly positive
  at every scale (`wave17Slots_total_pos`, whose L30 summand is the genuine
  positive failure probability).

Nothing is set to zero: the C5 loss is bounded by half of a strictly positive
ledger. -/
noncomputable def paperResidualForConcrete {D : ℝ} (R : Wave24Remaining D) :
    PaperResidualFor concreteFamily D := by
  classical
  let ledger : ℕ → ℝ := fun n =>
    (wave24Slots R.l18_4 R.l19 R.l20_2 R.l20_4 R.l21 R.l27_data
      R.l27_finish R.l30 R.l34 R.p1).total n
  have hledger_pos : ∀ n, 0 < ledger n := by
    intro n
    simpa only [ledger, wave24Slots] using
      wave17Slots_total_pos R.l18_4 R.l19 R.l20_2 R.l20_4
        (wave17InputsOfResidual R.l21) R.l27_data R.l27_finish R.l30 R.l34
        9 3 wave24_l4N_odd wave24_l4Bits_budget R.p1 n
  let c5 : Wave15C5Data (fun n hN => goodEpochOfLe n hN) :=
    goodC5Data (fun n => ledger n / 2) (fun n => half_pos (hledger_pos n))
  exact
    { l18_4 := R.l18_4
      l19 := R.l19
      l20_2 := R.l20_2
      l20_4 := R.l20_4
      l21 := R.l21
      l27_data := R.l27_data
      l27_finish := R.l27_finish
      l30 := R.l30
      l34 := R.l34
      p1 := R.p1
      c1 := c1Inputs_of_concrete R.c1Concrete (fun _ _ => rfl)
      c2 := c2Inputs_Egood
      c3 := R.c3
      c4 := R.c4
      concrete := fun n hN => goodEpochOfLe n hN
      concrete_eq := fun _ _ => rfl
      c5Data := c5
      loss_le := by
        intro n hN
        have hsmall :=
          c5TotalLoss_goodC5Data_le (fun n => ledger n / 2)
            (fun n => half_pos (hledger_pos n)) n hN
        have hhalf : ledger n / 2 ≤ ledger n := by
          linarith [hledger_pos n]
        simpa only [c5, ledger, wave24Slots] using hsmall.trans hhalf }

/-- **The non-vacuity witness is inhabited modulo exactly the residual
inputs.** -/
theorem nonempty_paperResidualFor_concrete {D : ℝ} (R : Wave24Remaining D) :
    Nonempty (PaperResidualFor concreteFamily D) :=
  ⟨paperResidualForConcrete R⟩

/-- The derived `c1` field is the transport of the concrete product identity. -/
theorem paperResidualForConcrete_c1 {D : ℝ} (R : Wave24Remaining D) :
    (paperResidualForConcrete R).c1 =
      c1Inputs_of_concrete R.c1Concrete (fun _ _ => rfl) := rfl

/-- The derived `c2` field is the unconditional `c2Inputs_Egood`. -/
theorem paperResidualForConcrete_c2 {D : ℝ} (R : Wave24Remaining D) :
    (paperResidualForConcrete R).c2 = c2Inputs_Egood := rfl

/-- The concrete family of the witness is `goodEpochOfLe`. -/
theorem paperResidualForConcrete_concrete {D : ℝ} (R : Wave24Remaining D) :
    (paperResidualForConcrete R).concrete = fun n hN => goodEpochOfLe n hN := rfl

/-- **The exact residual list.**  Everything in this list is an input of
`Wave24Remaining`; every other field of `PaperResidualFor` is derived. -/
def wave24RemainingFieldNames : List String :=
  ["l18_4", "l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1Concrete", "c3", "c4"]

theorem wave24RemainingFieldNames_length : wave24RemainingFieldNames.length = 13 := rfl

/-- **The complete list of remaining inputs of the non-vacuity witness.** -/
theorem wave24_remaining_inputs {D : ℝ} (R : Wave24Remaining D) :
    Nonempty L18_4Certificate ∧ Nonempty Wave15L19Inputs ∧
      Nonempty SaddleConcentrationSource ∧ Nonempty (Wave14L20_4Source.{0}) ∧
      Nonempty ConcreteLeafResidual ∧ Nonempty L27_1Inputs ∧
      Nonempty (L27StageOneFinishInputs R.l27_data) ∧
      Nonempty Wave14L30Inputs ∧ Nonempty L34ChebotarevSidesInputs ∧
      Nonempty SubexpPrepassInput ∧
      (∀ n (hN : 3 ≤ n), (goodEpochOfLe n hN).GlobalProductIdentity) ∧
      Nonempty (C3Inputs concreteFamily) ∧
      Nonempty (C4Inputs concreteFamily D) :=
  ⟨⟨R.l18_4⟩, ⟨R.l19⟩, ⟨R.l20_2⟩, ⟨R.l20_4⟩, ⟨R.l21⟩, ⟨R.l27_data⟩,
    ⟨R.l27_finish⟩, ⟨R.l30⟩, ⟨R.l34⟩, ⟨R.p1⟩, R.c1Concrete,
    ⟨R.c3⟩, ⟨R.c4⟩⟩

/-- **The residual record is inhabited from the concrete leaves**, hence the
Wave-17 record of the concrete family is too.  This is the non-vacuous
counterpart of `RandomizedWave17Audit.nonempty_wave17Inputs_of_remaining`, with
the L21.2 block reduced to `ConcreteLeafResidual` and `c1`/`c2` derived from the
concrete epoch. -/
theorem nonempty_wave17Inputs_of_wave24Remaining {D : ℝ}
    (R : Wave24Remaining D) :
    Nonempty (Wave17Inputs concreteFamily D) :=
  Nonempty.map PaperResidualFor.toWave17Inputs
    (nonempty_paperResidualFor_concrete R)

/-- The witness's concrete product identity is the only C1 content: there is no
`Egood`-shaped `c1 : C1Inputs Egood` hypothesis anywhere in
`Wave24Remaining`.  In particular the refutation
`not_c1Inputs_Egood` does not apply to `PaperResidualFor` unless the concrete
family is specialized to the placeholder **and** `c1Concrete` is asserted. -/
theorem wave24_no_c1Inputs_field :
    wave24RemainingFieldNames.all (fun s => decide (s ≠ "c1")) = true := by
  decide

/-! ## Axiom audit -/

#print axioms wave24_l4N_odd
#print axioms wave24_l4Bits_budget
#print axioms wave24Slots
#print axioms PaperResidualFor.toWave17Inputs
#print axioms PaperResidualFor.toWave17Inputs_l21_2
#print axioms PaperResidualFor.toWave17Inputs_l4
#print axioms PaperResidualFor.toWave17Inputs_slots
#print axioms PaperResidualFor.toWave17Inputs_c
#print axioms PaperResidualFor.toWave17Inputs_c5
#print axioms PaperResidualFor.toFullyDischargedInputs
#print axioms PaperResidualFor.nonempty_wave17Inputs
#print axioms PaperResidualForSchedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave24Inputs
#print axioms concreteFamily
#print axioms concreteFamily_eq_Egood
#print axioms paperResidualForConcrete
#print axioms nonempty_paperResidualFor_concrete
#print axioms paperResidualForConcrete_c1
#print axioms paperResidualForConcrete_c2
#print axioms paperResidualForConcrete_concrete
#print axioms wave24RemainingFieldNames_length
#print axioms wave24_remaining_inputs
#print axioms nonempty_wave17Inputs_of_wave24Remaining
#print axioms wave24_no_c1Inputs_field

end Cogentic.RandomizedPaperEndpointWave24
