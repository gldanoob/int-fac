import Cogentic.RandomizedPaperEndpointDischarged
import Cogentic.RandomizedDischargedAdapters
import Cogentic.RandomizedL18_4Full
import Cogentic.RandomizedL19Full
import Cogentic.RandomizedC5Full

/-!
# The fully discharged paper endpoint

`Cogentic.RandomizedPaperEndpointDischarged.DischargedPaperEndpointInputs` still
takes the decomposed *inputs* `L18_4Inputs` and `L19Inputs`.  Wave 7 has since
proved that those inputs follow from the full certificates
`RandomizedL18_4.L18_4Certificate` and
`RandomizedL19Full.L19FullCertificate`.  This file replaces the two input
records by the certificates, so that the endpoint's remaining assumptions are
exactly

* the eight paper leaves `L20.2`, `L20.4`, `L21.2`, `L27.1`, `L30`, `L34`,
  `L4/L25/L36`, and `P1`;
* C1–C4;
* the full L18.4 certificate `L18_4Certificate`;
* the full L19 certificate `L19FullCertificate`;
* the W45 C5 certificate `C5FullInputs` (the C5 field of the discharged inputs,
  carrying the W31 C5.d and W32 C5.e stages);
* the adapters `concrete`, `concrete_eq`, and `loss_le`.

The ledger `fullyDischargedSlots` is `dischargedSlots` evaluated at
`L18_4Certificate.toInputs` and `L19FullCertificate.toL19Inputs`; its term-by-term
form is `fullyDischargedSlots_total_eq`.  The only numerical adapter is `loss_le`,
which is kept in exactly the same shape as in the discharged file, only with the
certificate-produced inputs.  No loss, mass, or error is set to zero.

The reduction is

* `FullyDischargedInputs.toDischargedInputs` : the discharged endpoint inputs;
* `FullyDischargedInputs.toPaperAnalyticAssumptions` and
  `FullyDischargedInputs.toPaperAnalyticAssumptions_slots` : the twelve-leaf
  record and its ledger;
* `FullyDischargedInputs.toPaperEndpointInputs` : the full paper endpoint inputs;
* `serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs` : the
  endpoint, obtained by composing with
  `RandomizedPaperEndpointDischarged
  .serialized_assembled_balancedEnvelopeInfimum_from_dischargedInputs`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedPaperEndpointFullyDischarged

open Cogentic.Randomized
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedDischargedAdapters
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperL18_4
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real
open scoped BigOperators ENNReal

set_option warn.classDefReducibility false

/-! ## The fully discharged ledger -/

/-- The C5 loss ledger of the fully discharged inputs.  This is the paper ledger
`dischargedSlots` with the L18.4 group read from the full L18.4 certificate and
the L19.4–L19.6 groups read from the full L19 certificate. -/
noncomputable def fullyDischargedSlots
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf) :
    C5LossSlots :=
  dischargedSlots l18_4.toInputs l19.toL19Inputs l20_2 l20_4 l21_2 l27_1
    l30 l34 l4_l25_l36 p1

/-- **Definitional adapter.**  The fully discharged ledger is the discharged
ledger at the certificate-produced inputs. -/
theorem fullyDischargedSlots_eq
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf) :
    fullyDischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
        l4_l25_l36 p1 =
      dischargedSlots l18_4.toInputs l19.toL19Inputs l20_2 l20_4 l21_2
        l27_1 l30 l34 l4_l25_l36 p1 :=
  rfl

/-- **The ledger, term by term.**  The fully discharged C5 ledger total is the
L18.4 certificate loss, the three L19 certificate losses, and the eight
remaining paper-leaf losses.  This makes explicit that no slot is dropped or set
to zero. -/
theorem fullyDischargedSlots_total_eq
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_1 : RatedLeaf) (l30 : SubexpLeaf)
    (l34 : RatedLeaf) (l4_l25_l36 : AlgebraicLeaf) (p1 : P1Leaf) (n : ℕ) :
    (fullyDischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
        l4_l25_l36 p1).total n =
      l18_4.toInputs.loss n + l19.toL19Inputs.poisson.loss n +
        l19.toL19Inputs.zeroMode.loss n + l19.toL19Inputs.thin.loss n +
        l20_2.loss n + l20_4.loss n + l21_2.loss n + l27_1.loss n +
        l30.loss n + l34.loss n + l4_l25_l36.loss n + p1.loss n := by
  simpa only [fullyDischargedSlots] using
    dischargedSlots_total_eq l18_4.toInputs l19.toL19Inputs l20_2 l20_4
      l21_2 l27_1 l30 l34 l4_l25_l36 p1 n

/-! ## The fully discharged inputs -/

/-- **The fully discharged paper-endpoint inputs.**

Compared with `DischargedPaperEndpointInputs`, the decomposed `l18_4` inputs are
replaced by the full `L18_4Certificate` and the decomposed `l19` inputs by the
full `L19FullCertificate`.  The C5 field remains the W45 `C5FullInputs`
certificate (with the W31 C5.d and W32 C5.e stages).  The eight remaining paper
leaves, C1–C4, and the concrete-family/ledger adapters stay explicit. -/
structure FullyDischargedInputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate (large sieve, RH cell counts, numerator count,
  and thin-pair aggregate). -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate (Poisson quotient, zero mode, and thin pairs). -/
  l19 : L19FullCertificate
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
  /-- The concrete epoch family underlying the C5 certificate. -/
  concrete : ∀ n, 3 ≤ n → ConcreteEpochData n
  /-- Adapter: the ambient epoch family is the concrete family's
  `toHardEpochData`. -/
  concrete_eq : ∀ n hN, E n hN = (concrete n hN).toHardEpochData
  /-- The W45 C5 certificate, carrying the W31/W32 C5.d/C5.e stages. -/
  c5 : ∀ n hN, @C5FullInputs n (concrete n hN) (sampleFintype hN (concrete n hN))
  /-- Adapter: the concrete C5.a–e total loss is dominated by the fully
  discharged paper ledger.  This is the numerical bridge between the concrete
  pool/recognizer budgets and the certificate-plus-leaf losses; no term is set
  to zero. -/
  loss_le : ∀ n hN,
    c5TotalLoss hN (concrete n hN) (c5 n hN) ≤
      (fullyDischargedSlots l18_4 l19 l20_2 l20_4 l21_2 l27_1 l30 l34
        l4_l25_l36 p1).total n

namespace FullyDischargedInputs

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The discharged inputs.**  Replace the two certificates by the literal
inputs they prove, and keep every other field (including the C5 certificate and
the loss adapter) unchanged.  The `loss_le` field transfers definitionally
because `fullyDischargedSlots` is `dischargedSlots` at the certificate outputs. -/
noncomputable def toDischargedInputs (I : FullyDischargedInputs E D) :
    DischargedPaperEndpointInputs E D where
  l18_4 := I.l18_4.toInputs
  l19 := I.l19.toL19Inputs
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21_2 := I.l21_2
  l27_1 := I.l27_1
  l30 := I.l30
  l34 := I.l34
  l4_l25_l36 := I.l4_l25_l36
  p1 := I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5 := I.c5
  loss_le := I.loss_le

/-- The L18.4 input of the reduction is the certificate's `toInputs`. -/
theorem toDischargedInputs_l18_4 (I : FullyDischargedInputs E D) :
    I.toDischargedInputs.l18_4 = I.l18_4.toInputs := rfl

/-- The L19 input of the reduction is the certificate's `toL19Inputs`. -/
theorem toDischargedInputs_l19 (I : FullyDischargedInputs E D) :
    I.toDischargedInputs.l19 = I.l19.toL19Inputs := rfl

/-- Reassemble the twelve-field `PaperAnalyticAssumptions` record from the
certificate-produced inputs. -/
noncomputable def toPaperAnalyticAssumptions
    (I : FullyDischargedInputs E D) : PaperAnalyticAssumptions E D :=
  I.toDischargedInputs.toPaperAnalyticAssumptions

/-- **The fully discharged ledger is the paper ledger.**  This is the discharged
slots identity with the two certificates unfolded to their inputs. -/
theorem toPaperAnalyticAssumptions_slots
    (I : FullyDischargedInputs E D) :
    I.toPaperAnalyticAssumptions.slots =
      fullyDischargedSlots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_1
        I.l30 I.l34 I.l4_l25_l36 I.p1 := by
  exact I.toDischargedInputs.toPaperAnalyticAssumptions_slots

/-- The `hitMass` bridge, inherited from the discharged reduction. -/
theorem hitMass_of_inputs (I : FullyDischargedInputs E D) :
    ∀ n (hN : 3 ≤ n), HardInput n →
      (1 / 4 : ℝ) - I.toPaperAnalyticAssumptions.slots.total n ≤
        ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal :=
  I.toDischargedInputs.hitMass_of_inputs

/-- **`PaperEndpointInputs` from the fully discharged inputs.** -/
noncomputable def toPaperEndpointInputs
    (I : FullyDischargedInputs E D) : PaperEndpointInputs E D :=
  I.toDischargedInputs.toPaperEndpointInputs

/-- The paper record produced by the fully discharged inputs has the fully
discharged ledger. -/
theorem toPaperEndpointInputs_paper_slots
    (I : FullyDischargedInputs E D) :
    I.toPaperEndpointInputs.paper.slots =
      fullyDischargedSlots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_1
        I.l30 I.l34 I.l4_l25_l36 I.p1 :=
  I.toPaperAnalyticAssumptions_slots

end FullyDischargedInputs

/-! ## The endpoint -/

/-- **Fully discharged paper endpoint.**  Under the critical-line hypothesis for
Dirichlet L-functions, there is one universal serialized factoring algorithm
such that, for every balanced-schedule epoch family which, at every valid
ceiling, carries

* the full L18.4 certificate,
* the full L19 certificate,
* the eight remaining paper leaves,
* C1–C4, and
* the W45 C5 certificate (with the W31 C5.d and W32 C5.e stages),

the kernel-checked driver always outputs a permutation of `n.primeFactorsList`
and has expected serialized bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`, where
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof is
`RandomizedPaperEndpointDischarged
.serialized_assembled_balancedEnvelopeInfimum_from_dischargedInputs` applied to
`FullyDischargedInputs.toDischargedInputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        FullyDischargedInputs (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_dischargedInputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toDischargedInputs⟩

/-! ## Axiom audit -/

#print axioms fullyDischargedSlots
#print axioms fullyDischargedSlots_eq
#print axioms fullyDischargedSlots_total_eq
#print axioms FullyDischargedInputs.toDischargedInputs
#print axioms FullyDischargedInputs.toDischargedInputs_l18_4
#print axioms FullyDischargedInputs.toDischargedInputs_l19
#print axioms FullyDischargedInputs.toPaperAnalyticAssumptions
#print axioms FullyDischargedInputs.toPaperAnalyticAssumptions_slots
#print axioms FullyDischargedInputs.hitMass_of_inputs
#print axioms FullyDischargedInputs.toPaperEndpointInputs
#print axioms FullyDischargedInputs.toPaperEndpointInputs_paper_slots
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs

end Cogentic.RandomizedPaperEndpointFullyDischarged
