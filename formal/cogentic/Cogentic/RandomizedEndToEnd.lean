import Cogentic.RandomizedConcreteEpoch
import Cogentic.RandomizedConcreteEpochChecks
import Cogentic.RandomizedConcreteEpochCost
import Cogentic.RandomizedConcreteStageCost
import Cogentic.RandomizedConcreteStageCostS1S2
import Cogentic.RandomizedConcreteStageCostS3
import Cogentic.RandomizedConcreteStageCostS469
import Cogentic.RandomizedConcreteStageCostS5
import Cogentic.RandomizedConcreteStageCostS8
import Cogentic.RandomizedC5Algebra
import Cogentic.RandomizedC5Coupling
import Cogentic.RandomizedL19Poisson
import Cogentic.RandomizedL19Energy
import Cogentic.RandomizedL19EnergyMass
import Cogentic.RandomizedL19ZeroMode
import Cogentic.RandomizedL19ZeroModeFinite
import Cogentic.RandomizedL19Thin
import Cogentic.RandomizedL19ThinFinite
import Cogentic.RandomizedL19Full
import Cogentic.RandomizedL20_2
import Cogentic.RandomizedL20_2Sub
import Cogentic.RandomizedL20_4
import Cogentic.RandomizedL20_4Sub
import Cogentic.RandomizedL34
import Cogentic.RandomizedL34Sub
import Cogentic.RandomizedC5Full
import Cogentic.RandomizedL21_2
import Cogentic.RandomizedL21_2Sub
import Cogentic.RandomizedL27_1
import Cogentic.RandomizedL27_1Sub
import Cogentic.RandomizedL30
import Cogentic.RandomizedL30Sub
import Cogentic.RandomizedL4
import Cogentic.RandomizedL4Sub
import Cogentic.RandomizedConcreteFormSpec
import Cogentic.RandomizedP1
import Cogentic.RandomizedP1Sub
import Cogentic.RandomizedConcreteTV
import Cogentic.RandomizedConcreteHitMass
import Cogentic.RandomizedConcreteHitMassCount
import Cogentic.RandomizedC5HalfMass
import Cogentic.RandomizedL18_4
import Cogentic.RandomizedL18_4CellCount
import Cogentic.RandomizedL18_4CellData
import Cogentic.RandomizedL18_4Numerator
import Cogentic.RandomizedL18_4Mass
import Cogentic.RandomizedL18_4Thin
import Cogentic.RandomizedL18_4ThinAggregate
import Cogentic.RandomizedL18_4Full
import Cogentic.RandomizedL18_4LargeSieve
import Cogentic.RandomizedL18_4LargeSieveInputs
import Cogentic.RandomizedL18_4LargeSieveResidual
import Cogentic.RandomizedL18_4LatticeCount
import Cogentic.RandomizedL19SecondMoment
import Cogentic.RandomizedL19Muq
import Cogentic.RandomizedPaperL18_4
import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedEpochAnalyticInputs
import Cogentic.RandomizedEpochWork
import Cogentic.RandomizedEpochPool
import Cogentic.RandomizedEpochAlgebra
import Cogentic.RandomizedEpochTV
import Cogentic.RandomizedEpochPrivate
import Cogentic.RandomizedRoughEndpoint
import Cogentic.RandomizedTrialEndpoint

/-!
# Randomized factoring: end-to-end composition with auditable analytic inputs

This file is the integration point for the randomized branch.  The existing
`RandomizedEpochAssembly` theorems are conditional on the opaque
`HardEpochAsymptoticBound`.  `RandomizedEpochAnalyticInputs` replaces that
hypothesis by an explicit ledger of named analytic leaves.  Here we compose the
two, so the only unproved inputs are the fields of `EpochAnalyticInputs`:

* C1: the public congruence check;
* C2: conditional hidden-sign uniformity;
* C3: the ideal/actual total-variation budget;
* C4: the expected public-work budget;
* C5: the good-transcript mass and the leaf ledger L18.4, L19.4-L19.6,
  L20.2, L20.4, L21.2, L27.1, L30, L34, L4/L25/L36, P1, plus the C5 assembly
  bridge.

Nothing in this file proves those analytic leaves.  What it does prove is that
the kernel-checked assembly, the numerical C5 combination, and the serialized
driver go through once the leaves are supplied.  The still-open lower-level
statements are listed in `research/randomized-gap-audit.md`.

Two endpoints are provided:

* `serialized_assembled_epoch_from_analyticInputs` for a fixed epoch and
  ceiling `C`;
* `serialized_assembled_balancedEnvelopeInfimum_from_analyticInputs` for the
  universal balanced schedule, with the explicit interval for
  `balancedEnvelopeInfimum`.
-/

namespace Cogentic.RandomizedEndToEnd

open Cogentic.Randomized
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real
open scoped BigOperators ENNReal

/-- Fixed-schedule endpoint: if a concrete hard-input epoch family has the
auditable analytic inputs at ceiling `C`, then the serialized factor driver
returns the complete prime factorization with expected bit cost eventually at
most `exp ((C + ε) * scale n)`. -/
theorem serialized_assembled_epoch_from_analyticInputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ}, 0 ≤ C →
      EpochAnalyticInputs E C →
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound (epochHard (epochLaw E) (epochAttempt E)) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound (epochHard (epochLaw E) (epochAttempt E)) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤ ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ := serialized_assembled_epoch_from_critical_line line
  refine ⟨k, sound, fun E C hC I => ?_⟩
  exact hmain E hC (hardEpochAsymptoticBound_of_analyticInputs E C I)

/-- Universal-schedule endpoint: one algorithm works for the whole balanced
schedule family.  The only inputs are the analytic ledgers at each valid
schedule ceiling.  The limiting coefficient is the kernel-checked
`balancedEnvelopeInfimum`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_analyticInputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        EpochAnalyticInputs (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_critical_line line
  refine ⟨k, sound, fun E hI => ?_⟩
  exact hmain E fun s D hvalid =>
    hardEpochAsymptoticBound_of_analyticInputs (E s) D (hI s D hvalid)

#print axioms serialized_assembled_epoch_from_analyticInputs
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_analyticInputs
#print axioms Cogentic.RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilon
#print axioms Cogentic.RandomizedEpochTV.assembledAttempt_hit_prob_ge_of_directSampler
#print axioms Cogentic.RandomizedEpochPrivate.PrivateSupplyInputs.privateSlotProbability_lower
#print axioms Cogentic.RandomizedEpochPrivate.PrivateSupplyInputs.goodLeading_card_le_rankin
#print axioms Cogentic.RandomizedConcreteEpoch.ConcreteEpochData.pubWork_eq_zero_iff
#print axioms Cogentic.RandomizedPaperLeafStatements.epochAnalyticInputs_of_paperAssumptions
#print axioms Cogentic.RandomizedPaperLeafStatements.hardEpochAsymptoticBound_of_paperAssumptions
#print axioms Cogentic.RandomizedConcreteEpoch.ConcreteEpochChecks.c1_and_c2_inputs_concreteEpoch
#print axioms Cogentic.RandomizedConcreteEpochCost.c3_and_c4_inputs_concreteEpoch
#print axioms Cogentic.RandomizedConcreteEpochCost.hardEpochAsymptoticBound_of_concreteCost
#print axioms Cogentic.RandomizedConcreteTV.toy_tv_eq_zero
#print axioms Cogentic.RandomizedConcreteTV.toyC3Inputs
#print axioms Cogentic.RandomizedConcreteTV.bigConcreteC3
#print axioms Cogentic.RandomizedConcreteTV.bigC3Inputs
#print axioms Cogentic.RandomizedConcreteStageCost.s0Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCost.s7Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCost.ConcreteC4Hypotheses.ofS0S7
#print axioms Cogentic.RandomizedConcreteStageCostS1S2.s1Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCostS1S2.s2Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCostS1S2.ConcreteC4Hypotheses.withS1S2
#print axioms Cogentic.RandomizedConcreteStageCostS469.s4Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCostS469.s6Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCostS469.s9Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCostS469.ConcreteC4Hypotheses.withS4S6S9
#print axioms Cogentic.RandomizedC5Algebra.C5AlgebraInputs.stageBudget
#print axioms Cogentic.RandomizedL19Poisson.CoupledNumeratorData.numerator_energy
#print axioms Cogentic.RandomizedL19Poisson.PoissonDenominatorData.A_bound
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceMarginalBounds
#print axioms Cogentic.RandomizedL19ZeroMode.ZeroModeCertificate.toIdealZeroModeInputs
#print axioms Cogentic.RandomizedL19ZeroModeFinite.FiniteZeroModeCertificate.toZeroModeCertificate
#print axioms Cogentic.RandomizedL19EnergyMass.mellinEnvelope_le_exp_of_growth
#print axioms Cogentic.RandomizedL19EnergyMass.gridPrefixEnvelope_le_exp_of_growth
#print axioms Cogentic.RandomizedL19Thin.LatticeThinInputs.slot_le
#print axioms Cogentic.RandomizedL19ThinFinite.LatticePaperThinFiniteInputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL19ThinFinite.LatticePaperThinFiniteInputs.slot_le
#print axioms Cogentic.RandomizedConcreteStageCostS5.s5Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCostS5.ConcreteC4Hypotheses.withS5
#print axioms Cogentic.RandomizedC5Coupling.CouplingInputs.stageBudget
#print axioms Cogentic.RandomizedC5Coupling.goodMass_lower_withCoupling
#print axioms Cogentic.RandomizedL18_4.eventually_shrunk_field_count
#print axioms Cogentic.RandomizedL27_1.L27_1Inputs.toRatedLeaf
#print axioms Cogentic.RandomizedL27_1.L27_1Inputs.slot_le
#print axioms Cogentic.RandomizedL30.L30Inputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL30.L30Inputs.slot_le
#print axioms Cogentic.RandomizedL30Sub.FailureData.subexpLoss
#print axioms Cogentic.RandomizedL30Sub.PaperInputs.modelCount_lower
#print axioms Cogentic.RandomizedP1.P1Inputs.toP1Leaf
#print axioms Cogentic.RandomizedP1.trialDivisionGap
#print axioms Cogentic.RandomizedL21_2.L21_2Inputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2.L21_2Inputs.slot_le
#print axioms Cogentic.RandomizedL20_4.L20_4Inputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL20_4.L20_4Inputs.slot_le
#print axioms Cogentic.RandomizedL20_4Sub.L20_4SubInputs.subexpLoss
#print axioms Cogentic.RandomizedL20_4Sub.L20_4SubInputs.slot_le
#print axioms Cogentic.RandomizedL4.L4Inputs.toAlgebraicLeaf
#print axioms Cogentic.RandomizedL20_2.L20_2Inputs.toConcentrationLeaf
#print axioms Cogentic.RandomizedL20_2.L20_2Inputs.slot_le
#print axioms Cogentic.RandomizedL34.EffectiveChebotarevInputs.ratedLeaf
#print axioms Cogentic.RandomizedL19Full.L19FullCertificate.toL19Inputs
#print axioms Cogentic.RandomizedL19Full.L19FullCertificate.slots_bounds
#print axioms Cogentic.RandomizedC5Full.C5FullInputs.toHitMassInputs
#print axioms Cogentic.RandomizedC5Full.C5FullInputs.hitMass_of_inputs
#print axioms Cogentic.RandomizedL34Sub.probeMiss_le_exp_of_estimates
#print axioms Cogentic.RandomizedL30Sub.FailureData.subexpLoss
#print axioms Cogentic.RandomizedL18_4.L18_4Inputs.replaceLargeSieveResidualData
#print axioms Cogentic.RandomizedL20_2Sub.L20_2SubInputs.toInputs
#print axioms Cogentic.RandomizedL27_1Sub.toRatedLeaf
#print axioms Cogentic.RandomizedL4Sub.L4SubInputs.toL4Inputs
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.slot_le
#print axioms Cogentic.RandomizedP1Sub.P1SubInputs.toP1Leaf
#print axioms Cogentic.RandomizedP1Sub.p1Sub_reduction
#print axioms Cogentic.RandomizedConcreteFormSpec.concreteFormSpec
#print axioms Cogentic.RandomizedL19EnergyMass.mellinEnergyScaleOfGrowth
#print axioms Cogentic.RandomizedConcreteStageCostS3.s3Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCostS3.ConcreteC4Hypotheses.ofS0S7_withS3
#print axioms Cogentic.RandomizedConcreteStageCostS8.s8Cost_le_poly
#print axioms Cogentic.RandomizedConcreteStageCostS8.ConcreteC4Hypotheses.withS8
#print axioms Cogentic.RandomizedL18_4.cell_prime_count_of_cellData
#print axioms Cogentic.RandomizedL18_4.cell_prime_count_from_critical_line
#print axioms Cogentic.RandomizedL18_4.L18_4Inputs.replaceCellNumeratorCount
#print axioms Cogentic.RandomizedL18_4.MassErrorInputs.mass_lower
#print axioms Cogentic.RandomizedL18_4.MassErrorInputs.error_le
#print axioms Cogentic.RandomizedL18_4.L18_4Inputs.replaceCellNumeratorCountOfMass
#print axioms Cogentic.RandomizedL18_4.ThinPairInputs.thin_pair_fraction
#print axioms Cogentic.RandomizedL19SecondMoment.L19Inputs.leaves
#print axioms Cogentic.RandomizedL19SecondMoment.L19Inputs.slots_bounds
#print axioms Cogentic.RandomizedL19Muq.DividedStripRatioInputs.muq_le
#print axioms Cogentic.RandomizedL18_4.L18_4Inputs.replaceThinPairFraction
#print axioms Cogentic.RandomizedL18_4.ThinAggregate.strip_count
#print axioms Cogentic.RandomizedL18_4.ThinAggregate.replaceThinPairFraction
#print axioms Cogentic.RandomizedL18_4.L18_4Certificate.toInputs
#print axioms Cogentic.RandomizedL18_4.L18_4Certificate.toSubexpLeaf
#print axioms Cogentic.RandomizedL18_4.L18_4Certificate.slot_le
#print axioms Cogentic.RandomizedL18_4.zmod_parseval
#print axioms Cogentic.RandomizedL18_4.L18_4Inputs.replaceLargeSieve
#print axioms Cogentic.RandomizedL18_4.L18_4Inputs.replaceLargeSieveCertificate
#print axioms Cogentic.RandomizedL18_4.LargeSieveCertificateData.toLargeSieveCertificate
#print axioms Cogentic.RandomizedL18_4.L18_4Inputs.replaceLargeSieveCertificateData
#print axioms Cogentic.RandomizedPaperL18_4.paperAssumptions_of_L18_4Inputs
#print axioms Cogentic.RandomizedConcreteHitMassCount.C5abcInputs.compl_le
#print axioms Cogentic.RandomizedConcreteHitMassCount.C5abcInputs.toHitMassInputs
#print axioms Cogentic.RandomizedC5HalfMass.HalfMassInputs.half_mass
#print axioms Cogentic.RandomizedC5HalfMass.half_mass_epochAccepted
#print axioms Cogentic.RandomizedL18_4.L18_4Inputs.toSubexpLeaf
#print axioms Cogentic.RandomizedConcreteHitMass.HitMassInputs.hitMass_of_inputs
#print axioms Cogentic.RandomizedConcreteHitMass.toC5Inputs_of_hitMassInputs

end Cogentic.RandomizedEndToEnd
