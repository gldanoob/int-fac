import Cogentic.RandomizedPaperEndpoint
import Cogentic.RandomizedPaperL18_4
import Cogentic.RandomizedL19SecondMoment
import Cogentic.RandomizedC5Full

/-!
# Wave 7 capstone: the discharged paper endpoint

`Cogentic.RandomizedPaperEndpoint.PaperEndpointInputs` bundles the twelve
manuscript leaves of `PaperAnalyticAssumptions`, the C1–C4 interfaces, and the
opaque C5 `hitMass` bridge.  Wave 7 has replaced several of those opaque fields
by smaller certificates:

* **L18.4** — `RandomizedL18_4.L18_4Inputs` (large sieve, RH cell counts, and the
  thin-pair fraction) proves the `SubexpLeaf`.
* **L19.4–L19.6** — `RandomizedL19SecondMoment.L19Inputs` (Poisson quotient,
  ideal zero mode, thin/small-determinant pairs) proves the three `SubexpLeaf`s.
* **C5** — `RandomizedC5Full.C5FullInputs` contains the W45 certificate: the
  C5.a–c counting reduction, the C5.b/c survivor/descent budgets, and the
  **W31** `RandomizedC5Algebra.C5AlgebraInputs` and **W32**
  `RandomizedC5Coupling.CouplingInputs` for C5.d/C5.e.  It proves the `hitMass`
  bridge with the algebra and coupling stages literally
  `C5AlgebraInputs.stageBudget` and `CouplingInputs.stageBudget`.

`DischargedPaperEndpointInputs` assembles the remaining eight paper leaves
(L20.2, L20.4, L21.2, L27.1, L30, L34, L4/L25/L36, P1) with those three
certificates and C1–C4.  It has **no** `hitMass` field.  The file proves

* `DischargedPaperEndpointInputs.toPaperAnalyticAssumptions` : the twelve-leaf
  `PaperAnalyticAssumptions` record, with L18.4 and L19.4–L19.6 replaced;
* `DischargedPaperEndpointInputs.toPaperAnalyticAssumptions_slots` : its C5
  ledger is the ledger of the discharged leaves;
* `DischargedPaperEndpointInputs.toPaperEndpointInputs` : the full
  `PaperEndpointInputs`, with `hitMass` proved from the W45 certificate;
* `serialized_assembled_balancedEnvelopeInfimum_from_dischargedInputs` : the
  final endpoint, obtained by composing with
  `RandomizedPaperEndpoint.serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions`.

The remaining adapters, stated explicitly, are

1. `concrete` / `concrete_eq`: the ambient `HardEpochData` family must be a
   concrete epoch family (the C5 certificates live on `ConcreteEpochData`);
2. `loss_le`: the concrete C5.a–e total loss must be dominated by the assembled
   paper ledger `slots.total`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no loss, mass, or
error is set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointDischarged

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
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperL18_4
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real
open scoped BigOperators ENNReal

set_option warn.classDefReducibility false

/-- The sample type of a concrete epoch on `n ≥ 3` is finite: `3 ≤ n` gives
`NeZero n`, which is what `ZMod n`'s `Fintype` instance needs.  The C5
certificates are stated at this instance. -/
noncomputable def sampleFintype {n : ℕ} (hN : 3 ≤ n) (C : ConcreteEpochData n) :
    Fintype C.Sample := by
  haveI : NeZero n := ⟨by omega⟩
  exact inferInstanceAs (Fintype (C.Coins × (C.Label → (ZMod n)ˣ)))

/-- The explicit C5.a–e total loss at the `3 ≤ n` sample instance. -/
noncomputable def c5TotalLoss {n : ℕ} (hN : 3 ≤ n) (C : ConcreteEpochData n)
    (I : @C5FullInputs n C (sampleFintype hN C)) : ℝ :=
  @C5FullInputs.totalLoss n C (sampleFintype hN C) I

/-! ## The discharged leaf ledger -/

/-- The C5 loss ledger induced by the eight remaining paper leaves, the
decomposed L18.4 inputs, and the decomposed L19.4–L19.6 inputs.

This is `PaperAnalyticAssumptions.slots` with the three replaced groups unfolded:
the L18.4 branch is `L18_4Inputs.loss`, the three L19 branches are the
`L19Inputs` losses, and the other eight branches are the paper-leaf losses. -/
noncomputable def dischargedSlots
    (l18_4 : L18_4Inputs) (l19 : L19Inputs)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf) :
    C5LossSlots
  | .rationalGoodEnvironments => l18_4.loss
  | .poissonQuotient => l19.poisson.loss
  | .idealZeroMode => l19.zeroMode.loss
  | .thinPairs => l19.thin.loss
  | .interiorConcentration => l20_2.loss
  | .topChildLaw => l20_4.loss
  | .ellipticExceptional => l21_2.loss
  | .ecmRecognition => l27_1.loss
  | .genusTwoPartialFactorer => l30.loss
  | .characterSeparation => l34.loss
  | .classGroupGenus => l4_l25_l36.loss
  | .prepass => p1.loss

/-- **The discharged paper-endpoint inputs.**

Compared with `PaperEndpointInputs`, the opaque `paper.l18_4` leaf is replaced by
`L18_4Inputs`, the three opaque L19 leaves by `L19Inputs`, and the opaque
`hitMass` bridge by the W45 `C5FullInputs` certificate (which itself carries the
W31 C5.d algebra and W32 C5.e coupling decompositions).  The remaining eight
paper leaves, C1–C4, and the concrete-family/ledger adapters stay explicit. -/
structure DischargedPaperEndpointInputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- L18.4 replaced by its explicit large-sieve / cell-count / thin-pair inputs. -/
  l18_4 : L18_4Inputs
  /-- L19.4–L19.6 replaced by the three explicit second-moment inputs. -/
  l19 : L19Inputs
  /-- L20.2: interior concentration (still a paper leaf). -/
  l20_2 : ConcentrationLeaf
  /-- L20.4: child-root-conditioned two-point bound (still a paper leaf). -/
  l20_4 : SubexpLeaf
  /-- L21.2: RH smooth numbers near integer centres (still a paper leaf). -/
  l21_2 : RatedLeaf
  /-- L27.1: Lenstra–Pomerance ECM (still a paper leaf). -/
  l27_1 : RatedLeaf
  /-- L30: genus-two partial factorer (still a paper leaf). -/
  l30 : SubexpLeaf
  /-- L34: effective Chebotarev character separation (still a paper leaf). -/
  l34 : RatedLeaf
  /-- L4/L25/L36: form composition / principal genus / even valuations. -/
  l4_l25_l36 : AlgebraicLeaf
  /-- P1: the `exp (o(H))`-cost prepass (still a paper leaf). -/
  p1 : P1Leaf
  /-- C1: the public congruence check (L1). -/
  c1 : C1Inputs E
  /-- C2: conditional hidden-sign uniformity (L2–L5, including L4). -/
  c2 : C2Inputs E
  /-- C3: the ideal/actual total-variation budget (L6–L10). -/
  c3 : C3Inputs E
  /-- C4: the expected public-work budget (L11–L16). -/
  c4 : C4Inputs E D
  /-- The concrete epoch family underlying the C5 certificates. -/
  concrete : ∀ n, 3 ≤ n → ConcreteEpochData n
  /-- Adapter: the ambient epoch family is the concrete family's
  `toHardEpochData`.  For the canonical `E = concreteFamily concrete` this is
  `fun _ _ => rfl`. -/
  concrete_eq : ∀ n hN, E n hN = (concrete n hN).toHardEpochData
  /-- The W45 C5 certificate, carrying the W31/W32 C5.d/C5.e stages. -/
  c5 : ∀ n hN, @C5FullInputs n (concrete n hN) (sampleFintype hN (concrete n hN))
  /-- Adapter: the concrete C5.a–e total loss is dominated by the paper ledger.
  This is the numerical bridge between the concrete pool/recognizer budgets and
  the twelve leaf losses; no term is set to zero. -/
  loss_le : ∀ n hN,
    c5TotalLoss hN (concrete n hN) (c5 n hN) ≤
      (dischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
        l4_l25_l36 p1).total n

namespace DischargedPaperEndpointInputs

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- Reassemble the twelve-field `PaperAnalyticAssumptions` record.

The eleven-field structure of `RandomizedPaperL18_4` is filled with the eight
remaining leaves plus the three `L19Inputs.leaves`, and then the L18.4 leaf is
supplied as `L18_4Inputs.toSubexpLeaf`. -/
noncomputable def toPaperAnalyticAssumptions
    (I : DischargedPaperEndpointInputs E D) : PaperAnalyticAssumptions E D :=
  paperAssumptions_of_L18_4Inputs
    { l19_4 := I.l19.leaves.l19_4
      l19_5 := I.l19.leaves.l19_5
      l19_6 := I.l19.leaves.l19_6
      l20_2 := I.l20_2
      l20_4 := I.l20_4
      l21_2 := I.l21_2
      l27_1 := I.l27_1
      l30 := I.l30
      l34 := I.l34
      l4_l25_l36 := I.l4_l25_l36
      p1 := I.p1 }
    I.l18_4

/-- **The discharged ledger is the paper ledger.**  Unfolding the three replaced
groups in `PaperAnalyticAssumptions.slots` gives `dischargedSlots`. -/
theorem toPaperAnalyticAssumptions_slots
    (I : DischargedPaperEndpointInputs E D) :
    I.toPaperAnalyticAssumptions.slots =
      dischargedSlots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_1
        I.l30 I.l34 I.l4_l25_l36 I.p1 := by
  funext k n
  cases k <;> rfl

/-- **The `hitMass` bridge, proved from the W45 certificate.**  The concrete C5
lower bound and the ledger adapter `loss_le` give the exact field type consumed
by `PaperEndpointInputs` at every hard input. -/
theorem hitMass_of_inputs
    (I : DischargedPaperEndpointInputs E D) :
    ∀ n (hN : 3 ≤ n), HardInput n →
      (1 / 4 : ℝ) - I.toPaperAnalyticAssumptions.slots.total n ≤
        ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal := by
  intro n hN _
  have hledger :
      c5TotalLoss hN (I.concrete n hN) (I.c5 n hN) ≤
        I.toPaperAnalyticAssumptions.slots.total n := by
    rw [I.toPaperAnalyticAssumptions_slots]
    exact I.loss_le n hN
  have hquarter : (1 / 4 : ℝ) - I.toPaperAnalyticAssumptions.slots.total n ≤
      (1 / 4 : ℝ) - c5TotalLoss hN (I.concrete n hN) (I.c5 n hN) := by
    linarith only [hledger]
  have hc5 := @C5FullInputs.hitMass_of_inputs n (I.concrete n hN)
    (sampleFintype hN (I.concrete n hN)) (I.c5 n hN)
  rw [I.concrete_eq n hN]
  exact hquarter.trans hc5

/-- **`PaperEndpointInputs` from the discharged inputs.**  The C5 field is the
proved `hitMass_of_inputs`; no opaque `hitMass` hypothesis remains. -/
noncomputable def toPaperEndpointInputs
    (I : DischargedPaperEndpointInputs E D) : PaperEndpointInputs E D where
  paper := I.toPaperAnalyticAssumptions
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  hitMass := I.hitMass_of_inputs

/-- The paper record produced by the discharged inputs has the same ledger as
`dischargedSlots`. -/
theorem toPaperEndpointInputs_paper_slots
    (I : DischargedPaperEndpointInputs E D) :
    I.toPaperEndpointInputs.paper.slots =
      dischargedSlots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_1
        I.l30 I.l34 I.l4_l25_l36 I.p1 :=
  I.toPaperAnalyticAssumptions_slots

end DischargedPaperEndpointInputs

/-! ## The endpoint -/

/-- **Wave 7 discharged paper endpoint.**  Under the critical-line hypothesis for
Dirichlet L-functions, there is one universal serialized factoring algorithm
such that, for every balanced-schedule epoch family which, at every valid
ceiling, carries

* the decomposed L18.4 inputs,
* the decomposed L19.4–L19.6 inputs,
* the eight remaining paper leaves,
* C1–C4, and
* the W45 C5 certificate (with the W31 C5.d and W32 C5.e stages),

the kernel-checked driver always outputs a permutation of `n.primeFactorsList`
and has expected serialized bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`, where
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof is `RandomizedPaperEndpoint
.serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions` applied to
`DischargedPaperEndpointInputs.toPaperEndpointInputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_dischargedInputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        DischargedPaperEndpointInputs (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toPaperEndpointInputs⟩

/-! ## Axiom audit -/

#print axioms sampleFintype
#print axioms c5TotalLoss
#print axioms dischargedSlots
#print axioms DischargedPaperEndpointInputs.toPaperAnalyticAssumptions
#print axioms DischargedPaperEndpointInputs.toPaperAnalyticAssumptions_slots
#print axioms DischargedPaperEndpointInputs.hitMass_of_inputs
#print axioms DischargedPaperEndpointInputs.toPaperEndpointInputs
#print axioms DischargedPaperEndpointInputs.toPaperEndpointInputs_paper_slots
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_dischargedInputs

end Cogentic.RandomizedPaperEndpointDischarged
