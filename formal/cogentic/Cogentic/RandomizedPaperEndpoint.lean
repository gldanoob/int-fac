import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedEndToEnd

/-!
# Paper-assumption endpoint for the randomized factoring algorithm

`Cogentic.RandomizedPaperLeafStatements` reduces the twelve manuscript leaf
statements to the auditable `EpochAnalyticInputs` ledger, and
`Cogentic.RandomizedEndToEnd` composes that ledger with the serialized driver.
This file performs the final composition: the balanced universal-schedule
endpoint, stated directly in terms of the paper-level leaf assumptions.

The only non-paper inputs are C1-C4 and the C5 `hitMass` assembly bridge; they
are bundled in `PaperEndpointInputs`.  In particular, the endpoint no longer
mentions the opaque `HardEpochAsymptoticBound`, and no new axiom is introduced:
the proof is the wave-1 `HardEpochAsymptoticBound` reduction applied to
`epochAnalyticInputs_of_paperAssumptions`.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedPaperEndpoint

open Cogentic.Randomized
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real
open scoped BigOperators ENNReal

/-- The inputs of the paper-level endpoint that are not manuscript leaf
statements.

* `paper` is the twelve-field `PaperAnalyticAssumptions` record (L18.4,
  L19.4-L19.6, L20.2, L20.4, L21.2, L27.1, L30, L34, L4/L25/L36, P1).
* `c1`-`c4` are the blueprint's C1-C4 interfaces (public congruence check,
  conditional hidden-sign uniformity, ideal/actual total variation, and the
  expected public-work budget).  For the concrete `ofMultiField` epoch, C1 and
  C2 are discharged in `RandomizedEpochAnalyticInputs`.
* `hitMass` is the C5.a-e assembly bridge: the ideal law's good-transcript mass
  is at least `1/4` minus the total paper ledger.  It concerns the concrete field
  pool and recognizer events, so it is not one of the manuscript's twelve leaves
  and is recorded separately.

This is exactly the interface consumed by
`epochAnalyticInputs_of_paperAssumptions`. -/
structure PaperEndpointInputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The twelve paper-level analytic leaf statements. -/
  paper : PaperAnalyticAssumptions E D
  /-- C1: the public congruence check (L1). -/
  c1 : C1Inputs E
  /-- C2: conditional hidden-sign uniformity (L2-L5, including L4). -/
  c2 : C2Inputs E
  /-- C3: the ideal/actual total-variation budget (L6-L10). -/
  c3 : C3Inputs E
  /-- C4: the expected public-work budget (L11-L16). -/
  c4 : C4Inputs E D
  /-- The C5.a-e assembly bridge (paper glue L17/L28/L38). -/
  hitMass : ∀ n (hN : 3 ≤ n), HardInput n →
    (1 / 4 : ℝ) - paper.slots.total n ≤
      ((E n hN).ideal.toOuterMeasure
        {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal

/-- Forget the paper-level presentation and recover the auditable analytic
ledger, using the twelve `B = 2` specializations and the C5 assembly bridge. -/
def PaperEndpointInputs.toEpochAnalyticInputs
    {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}
    (I : PaperEndpointInputs E D) : EpochAnalyticInputs E D :=
  epochAnalyticInputs_of_paperAssumptions E D I.paper I.c1 I.c2 I.c3 I.c4 I.hitMass

/-- **Paper-assumption endpoint.**  Under the critical-line hypothesis for
Dirichlet L-functions, there is one universal serialized factoring algorithm
such that, for every balanced-schedule epoch family equipped with the twelve
paper-level leaf statements, the C1-C4 interfaces, and the C5 `hitMass` bridge at
every valid schedule ceiling, the kernel-checked universal driver

* always outputs a permutation of `n.primeFactorsList`, and
* has expected serialized bit cost eventually at most
  `exp ((balancedEnvelopeInfimum + ε) * scale n)` for every `ε > 0`,

where `balancedEnvelopeInfimum ∈ (1.9839824118071388228,
1.9839824118071388230)`.

The manuscript's analytic leaves remain hypotheses (the fields of
`PaperAnalyticAssumptions`); the proof only composes them through
`epochAnalyticInputs_of_paperAssumptions` and
`RandomizedEndToEnd.serialized_assembled_balancedEnvelopeInfimum_from_analyticInputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperEndpointInputs (E s) D) →
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
    RandomizedEndToEnd.serialized_assembled_balancedEnvelopeInfimum_from_analyticInputs
      line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toEpochAnalyticInputs⟩

/-! ## Axiom audit -/

#print axioms PaperEndpointInputs.toEpochAnalyticInputs
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions

end Cogentic.RandomizedPaperEndpoint
