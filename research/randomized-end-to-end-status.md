# Randomized factoring: end-to-end Lean status

Branch `explore/randomized-one-third`, base commit `0bcb1db`, Lean
`leanprover/lean4:v4.33.1`. This note records what the end-to-end pass actually
proved. The short version: the conditional assembly is kernel-checked and is now
composed with an explicit analytic-input ledger and a paper-assumption endpoint,
but the manuscript bound itself is **not** proved. The current
`HardEpochAsymptoticBound` interface is vacuous as stated; wave 2 supplies a
construction-level concrete S0–S9 epoch and restates the endpoint directly in
terms of the paper's twelve analytic leaves, but those leaves, the concrete
C3/C4 estimates, and the manuscript bound remain unproved.

## Reproduction

```sh
cd /home/gldanoob/dev/int-fac-randomized
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
flock /tmp/intfac-lean.lock -c 'make check-randomized-end-to-end'
```

The target builds:

```text
Cogentic.RandomizedEndToEnd
Cogentic.RandomizedEpochVacuity
Cogentic.RandomizedCostedEpoch
Cogentic.RandomizedConcreteEpoch
Cogentic.RandomizedConcreteEpochChecks
Cogentic.RandomizedConcreteEpochCost
Cogentic.RandomizedPaperLeafStatements
Cogentic.RandomizedPaperEndpoint
```

All printed axioms are `[propext, Classical.choice, Quot.sound]`. The target
does not build the whole randomized tree; `make check-randomized-lean` does
that.

## What is kernel-checked

### 1. The interface is vacuous as stated

`Cogentic/RandomizedEpochVacuity.lean`:

- `oracleEpoch` is a zero-work epoch with a uniform hidden-label law and
  `publicRoot := Classical.choose (...)`.
- `oracleEpoch_bound : HardEpochAsymptoticBound oracleEpoch 0`.
- `oracle_end_to_end` applies the conditional theorem at `C = 0` and obtains an
  `exp(ε · scale n)` expected-cost claim for every `ε > 0`.

This is the regression test for the interface. It is not a factoring algorithm:
the hidden square root is supplied for free and no work is charged for it.

### 2. A costed interface that charges sampler and extractor

`Cogentic/RandomizedCostedEpoch.lean`:

- `Program` is a finite decision tree; `Program.cost` counts Boolean queries.
- `CostedRealization E` requires
  - a seed law and a `samplerProgram` generating the hidden labels,
  - `E.actual = seedLaw.map (...)` (the hidden sample is a pushforward, not a
    free coordinate),
  - a `program` computing `E.data` from the public transcript,
  - `E.pubWork` equal to sampler cost plus data-program cost plus explicit
    helper work.
- `serialized_costed_assembled_epoch_from_critical_line` reuses the existing
  assembly for the underlying bare epoch.
- `oracleEpoch_not_costed` and `oracleEpoch_no_zero_cost_sampler` reject the
  zero-work oracle unconditionally.
- `OracleRootExtractionLowerBound` is the explicit missing asymptotic lower
  bound; `not_costedHardEpochAsymptoticBound_zero_of_oracle` shows it is exactly
  what is needed to exclude an oracle that declares small positive work.

The model is a soundness device, not a complexity lower bound. A modified
oracle declaring `O(log n)` work is not rejected by the model; that requires the
residual `OracleRootExtractionLowerBound`.

### 3. The end-to-end composition with an explicit ledger

`Cogentic/RandomizedEndToEnd.lean`:

```lean
theorem serialized_assembled_epoch_from_analyticInputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, ...),
    ∀ (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ}, 0 ≤ C →
      EpochAnalyticInputs E C →
      (correctness of outputBits) ∧
      ∀ ε > 0, ∀ᶠ n, ∀ hn : 2 ≤ n,
        mean (serializedFactor ...) ... ≤ ofReal (exp ((C + ε) * scale n))

theorem serialized_assembled_balancedEnvelopeInfimum_from_analyticInputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ...),
    ∀ (E : ∀ s n, 3 ≤ n → HardEpochData n),
      (∀ s D, s.Valid D → EpochAnalyticInputs (E s) D) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (correctness of outputBits) ∧
      ∀ ε > 0, ∀ᶠ n, ∀ hn : 2 ≤ n,
        mean (serializedFactor ...) ... ≤
          ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n))
```

`EpochAnalyticInputs` (`Cogentic/RandomizedEpochAnalyticInputs.lean`) groups:

| Field | Content | Status |
|---|---|---|
| C1 | `CongruenceCheck` | discharged for `HardEpochData.ofMultiField` |
| C2 | `HiddenUniform` | discharged for `HardEpochData.ofMultiField` |
| C3 | total-variation budget `ε` | explicit field |
| C4 | expected public work | explicit field |
| C5 | good-transcript mass and leaf ledger | explicit fields |

The C5 ledger has one loss slot per blueprint leaf: L18.4, L19.4, L19.5, L19.6,
L20.2, L20.4, L21.2, L27.1, L30, L34, L4/L25/L36, and P1. Each slot is a
**weakened Lean-facing eventuality** `≤ exp(-2 · scale n)`, not the full
manuscript statement, because `HardEpochData` does not expose the field pool,
moment functionals, or recognizer events. The C5 `hitMass` field is the
remaining a–e assembly bridge. These are the unproved inputs of the endpoint.

### 4. Supporting glue

| Module | Content |
|---|---|
| `RandomizedEpochWork.lean` | stage decomposition and finite-sum public-work bound; `hardEpochAsymptoticBound_of_stagewise`, `serialized_assembled_epoch_stagewise_from_critical_line` |
| `RandomizedEpochTV.lean` | explicit direct-sampler TV budget, `pmfTotalVariation_le_directSamplerEpsilon`, and the epoch bridge `assembledAttempt_hit_prob_ge_of_directSampler` |
| `RandomizedEpochPool.lean` | C5.a pool coverage from Paley–Zygmund, upper-cut, bad-child, dyadic trimming and the union bound |
| `RandomizedEpochPrivate.lean` | private-slot probability lower bound, Rankin upper bound, and `privateSlotProbability_isExpLowerBound` (band/genus and slot-loss forms), with the form-composition bridge `realized` explicit |
| `RandomizedEpochAlgebra.lean` | `γ/2 - ε` split assembly and the `hardEpochAsymptoticBound_of_const_hit` bridge |
| `RandomizedRoughEndpoint.lean` | hard-epoch hypothesis restricted to `IsRough (roughThreshold n) n`; prepass splitting discharged; prepass cost at `exp((log n)^{2/3})` kept explicit (P1) |
| `RandomizedTrialEndpoint.lean` | unconditional `O(√N)` randomized endpoint; sanity check that the framework can prove a real theorem with no epoch hypothesis |

### 5. Build repair

`RandomizedDirectClassSampler.lean` had two failing proof terms in
`gcdExitProb_toReal_le_scaled`:

- `by ring` → `by field_simp`;
- `by omega` → `Nat.lt_one_iff.mp (Nat.lt_of_not_le hUp)`.

After the repair the module elaborates and `gcdExitProb_toReal_le` /
`gcdExitProb_toReal_le_scaled` no longer depend on `sorryAx`. This removes the
pre-existing `sorryAx` blocker for the TV workstream.

## Wave 2: concrete epoch, cost bridge, and paper endpoint

Wave 2 (W11–W15) adds five modules. All five compile and are listed in
`check-randomized-end-to-end`. The final run reported exit 0,
`Build completed successfully (9209 jobs)`, no `sorryAx`, and no axiom outside
`[propext, Classical.choice, Quot.sound]`.

| Module | Workstream | Content |
|---|---|---|
| `RandomizedConcreteEpoch.lean` | W11 | Concrete S0–S9 epoch from an explicit solver |
| `RandomizedConcreteEpochChecks.lean` | W12 | C1/C2 reduced to two explicit paper hypotheses |
| `RandomizedConcreteEpochCost.lean` | W13 | C3/C4 bridge from explicit TV/work hypotheses |
| `RandomizedPaperLeafStatements.lean` | W14 | Twelve paper-level leaf statements |
| `RandomizedPaperEndpoint.lean` | W15 | Paper-assumption endpoint theorem |

### W11 — construction-level concrete epoch

`RandomizedConcreteEpoch.ConcreteEpochData N` carries public coins, hidden
labels, field identities, the ideal and actual laws, an explicit
`solver : Coins → (Label → (ZMod N)ˣ) → Option (PublicMultiFieldTranscript …)`,
an explicit finite `publicCandidates` universe, and the ten stage-cost fields
`StageCosts.s0 … s9`. Its `toHardEpochData` sets

- `trace := solver` (the solver output, not a chosen transcript),
- `good := publicCandidates.filter (·.isSome)` (exactly the successful solver
  outputs, with `mem_good_iff_solver` proving both directions),
- `data := (Option.get t.val (good_isSome t.2)).toTranscriptData`,
- `pubWork := StageCosts.total`, the explicit sum of `S0`–`S9`.

The file proves `pubWork_eq_sum`, `stageCost_le_pubWork`, `pubWork_eq_zero_iff`
(a zero-work epoch must have every named stage zero), the pointwise
`stageDecomposition`, and that the public root comes from the solver output
rather than `Classical.choose`. The only `choose` in the data path is the
pre-existing mask-representative selection inside `toTranscriptData`. No
analytic estimate is asserted here.

### W12 — C1 and C2

Two `Prop`-valued hypotheses are stated with manuscript citations:

- `GlobalProductIdentity D`: the global modular product identity of the public
  multi-field transcript (blueprint C1 / leaf L1).
- `HiddenSignSymmetry D`: coordinatewise hidden-sign symmetry of the ideal law
  on the mask (blueprint C2 / leaves L2–L5).

The file proves `congruenceCheck` from `GlobalProductIdentity` via
`HardEpochData.ofMultiField_congruenceCheck`, and `hiddenUniform` from
`HiddenSignSymmetry` via `HardEpochData.ofMultiField_hiddenUniform`. It then
bundles `C1Inputs` and `C2Inputs` for a concrete epoch family
(`c1Inputs_concreteEpoch`, `c2Inputs_concreteEpoch`,
`c1_and_c2_inputs_concreteEpoch`). Thus C1/C2 are no longer part of the
analytic gap: they follow from those two explicit statements.

### W13 — C3 and C4

- `ConcreteC3Hypotheses D` collects the `DirectFormSpec`, retry parameters
  `J`/`J₀`, root-count majorant `R` and its side conditions, the ideal-to-uniform
  error `eta`, the gcd-exit budget `gcdMass`, `hideal`, `hgcd`, the exact-law
  hypothesis `hactual`, and the small-budget condition
  `directSamplerEpsilon ≤ 1/32`. From these it proves `tv_le` (the direct-sampler
  TV bound), `hit_prob_ge` (the epoch-level hit-probability bridge), and
  `c3Inputs`.
- `ConcreteC4Hypotheses D C` supplies per-stage weights `stageWeight`, exponents
  `stageExponent`, `exponent_lt`, and the eventual `mean_le`/`weight_le` bounds.
  From these it proves `mean_pubWork_le_exp_of_concreteStages` and `c4Inputs`,
  using the actual `S0`–`S9` decomposition, not an assumed one.

`concreteCostInputs` and `hardEpochAsymptoticBound_of_concreteCost` assemble the
pair. Every numeric TV and work estimate is an explicit structure field; the
file proves only the bridge and the pointwise `S0`–`S9` decomposition. Because
`DirectFormSpec` requires `DecidableEq` on the sample type, the module installs
a noncomputable `Classical.decEq` instance on the concrete sample space. This is
a decidability instance, not a choice of epoch data or of a public root, but it
is why `Classical.choice` appears in the `tv_le`/`c3Inputs` axiom lists.

### W14 — the twelve paper leaves

`PaperAnalyticAssumptions E C` has exactly twelve fields, one per manuscript
leaf: `l18_4`, `l19_4`, `l19_5`, `l19_6`, `l20_2`, `l20_4`, `l21_2`, `l27_1`,
`l30`, `l34`, `l4_l25_l36`, `p1`. The leaf shapes are:

- `SubexpLeaf` — the paper's `D^{-B}` for every `B`; the ledger slot is `B = 2`.
- `RatedLeaf` — the paper's quoted rate plus an explicit extra `ledger` estimate.
  L21.2, L27.1 and L34 use this shape because their quoted rates
  (`exp(-c H / log H)`, the ECM curve-count rate, and the effective-Chebotarev
  error) do not by themselves imply `exp(-2H)`.
- `ConcentrationLeaf` — L20.2's `D^{-2A}` with `A = D^{1/48}`.
- `AlgebraicLeaf` — L4/L25/L36, exact identifications with zero loss.
- `P1Leaf` — the prepass success probability plus its `costExponent` and
  `cost_sublinear`; the C5 ledger consumes only the success side (C4 charges
  the work).

The module proves `slot_le`, `toC5Inputs`, `paper_total_le_exp_neg_scale`, and
the reduction `epochAnalyticInputs_of_paperAssumptions` /
`hardEpochAsymptoticBound_of_paperAssumptions`. No paper lemma is proved.

### W15 — the paper-assumption endpoint

`PaperEndpointInputs E D` bundles the twelve `PaperAnalyticAssumptions` fields,
`C1Inputs`–`C4Inputs`, and the C5 `hitMass` bridge. The main theorem is

```lean
theorem serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, ...),
    ∀ (E : ∀ s n, 3 ≤ n → HardEpochData n),
      (∀ s D, s.Valid D → PaperEndpointInputs (E s) D) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      [correctness] ∧
      ∀ ε > 0, ∀ᶠ n, ∀ hn : 2 ≤ n,
        mean (serializedFactor ...) ... ≤
          ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n))
```

The statement no longer mentions `HardEpochAsymptoticBound`, and the proof
introduces no new axiom; it composes W14 with the wave-1 endpoint. **It remains
conditional on the paper leaves, C1–C4, and `hitMass`.**

### Build history

The first full `make check-randomized-end-to-end` run exited 2 and failed in W13
(`RandomizedConcreteEpochCost.lean`) because `DirectFormSpec` needs `DecidableEq`
on the sample type while `ConcreteEpochData` only supplied `DecidableEq Label`.
The exact leading errors were:

```text
error: Cogentic/RandomizedConcreteEpochCost.lean:107:14: failed to synthesize instance of type class
  DecidableEq (D n).Sample
error: Cogentic/RandomizedConcreteEpochCost.lean:162:19: failed to synthesize instance of type class
  DecidableEq ((D n).Coins × ((D n).Label → (ZMod n)ˣ))
```

The subsequent `sorryAx` entries in that module's `#print axioms` output were a
symptom of elaboration failure, not source `sorry`s. After W13 added local
`Classical.decEq` instances it built with exit 0 and zero `sorryAx`. A transient
`RandomizedEndToEnd ↔ RandomizedPaperEndpoint` import cycle from a concurrent
edit was then removed; the final full target run is clean.

### Exact remaining paper assumptions

The paper-level endpoint assumes, for the epoch family and schedule:

1. the twelve leaves of `PaperAnalyticAssumptions`: L18.4 (large sieve / G.3),
   L19.4–L19.6 (narrow-width second moment), L20.2 (interior concentration),
   L20.4 (child-root-conditioned two-point bound), L21.2 (RH smooth numbers near
   integer centres), L27.1 (Lenstra–Pomerance ECM), L30 (genus-two partial
   factorer), L34 (effective Chebotarev), L4/L25/L36 (form composition), P1
   (prepass);
2. C1 `GlobalProductIdentity` and C2 `HiddenSignSymmetry` (or the already
   discharged `C1Inputs`/`C2Inputs` for `ofMultiField`);
3. the C3 fields of `ConcreteC3Hypotheses` (direct-sampler TV estimate, exact
   actual law, `≤ 1/32` budget);
4. the C4 fields of `ConcreteC4Hypotheses` (per-stage mean and weight bounds
   below the ceiling `C`);
5. the C5 `hitMass` bridge (`1/4 - total loss ≤` ideal good-transcript mass).

No item on this list is proved in Lean.

## Wave 3: discharging sub-lemmas

Wave 3 attacks the first concrete sub-lemmas behind `PaperEndpointInputs`. It
does **not** prove the twelve leaves; it replaces several opaque leaves or
bridges by smaller explicit inputs and proves the reductions.

| Module | Content |
|---|---|
| `RandomizedL18_4.lean` | L18.4 split into `large_sieve`, `cell_prime_count`, `cell_numerator_count`, `thin_pair_fraction`; the numeric `SubexpLoss`/`SubexpLeaf` chain is proved |
| `RandomizedL18_4LargeSieve.lean` | single-modulus Parseval/Bessel lemmas; `large_sieve` reduced to `multiModulusSum` + `rationalCellPartition` |
| `RandomizedL18_4CellCount.lean` | `cell_prime_count` from integer `CellData` + the existing critical-line prime-bin supply; real-to-integer rounding proved |
| `RandomizedL18_4Numerator.lean` | `cell_numerator_count` from an actual root-progression count and the existing `PrimePatternProgressionBound`; two numeric residuals isolated |
| `RandomizedL18_4Thin.lean` | determinant-level lattice count and `thin_pair_fraction` from `ThinPairInputs`; `loss` unchanged |
| `RandomizedPaperL18_4.lean` | reassembles `PaperAnalyticAssumptions` from the eleven remaining leaves plus `L18_4Inputs` |
| `RandomizedConcreteStageCost.lean` | concrete S0 and S7 costs, with `≤ 4·(log₂N+1)²` and `≤ 12·(log₂N+1)⁴`; `ConcreteC4Hypotheses.ofS0S7` |
| `RandomizedConcreteTV.lean` | explicit `DirectFormSpec`, exact-zero toy TV instance, and a full `ConcreteC3Hypotheses` instance `bigConcreteC3` with `heps_le` proved |
| `RandomizedConcreteHitMass.lean` | C5 `hitMass` decomposed into pool coverage, survivor recurrence, descent tree, algebra, and coupling |
| `RandomizedConcreteHitMassCount.lean` | `c5abc_compl_le` proved from `C5abcInputs`; the remaining H.8 counting field is `half_mass` |

### L18.4 status

The L18.4 leaf is no longer opaque. `L18_4Inputs` defines the scales and the
deficit, and the file proves

```lean
theorem L18_4Inputs.subexpLoss : SubexpLoss I.loss
theorem L18_4Inputs.slot_le : ∀ᶠ n, slots .rationalGoodEnvironments n ≤ exp (-(2:ℝ) * scale n)
```

from four inputs. Each input now has a separate reduction:

- `large_sieve` ← `LargeSieveInputs.multiModulusSum` and
  `rationalCellPartition`; the single-modulus Parseval and Bessel lemmas are
  proved (`zmod_parseval`, `zmod_unit_bessel`, `multiModulus_residueEnergy_le`).
- `cell_prime_count` ← `CellData` plus the existing
  `cell_card_lower_from_critical_line`; the real-to-integer cell rounding and
  the supply/width compatibility are proved.
- `cell_numerator_count` ← `NumeratorCountInputs`, tied to an actual
  `progressionCount` and the existing `PrimePatternProgressionBound`; the
  remaining residuals are `mass_lower` and `error_le`.
- `thin_pair_fraction` ← `ThinPairInputs`; the per-level determinant lattice
  count (`card_modEq_le`, `det_level_card_le`) is proved, and the aggregated
  strip sum is the remaining input.

The only factor-level caveat is recorded in `RandomizedL18_4CellCount`: the
paper's equal subdivision gives width `2V/(3dK)`, while the literal field asks
for `V/(2dK(1+W))`. The module isolates this in `CellData.width` and
`cell_prime_count_of_paper_cell_width`.

### C5 hitMass status

`HitMassInputs` decomposes the good-event mass:

```text
totalLoss = preLoss + algebra.loss + coupling.loss
preLoss   = pool.loss + survivor.loss + descent.loss
```

and proves `HitMassInputs.hitMass_of_inputs` and
`toC5Inputs_of_hitMassInputs`. The C5.a pool coverage is the actual L17
`PoolCoverageBudget`; C5.b/C5.c are the existing survivor/descent recurrences.
`RandomizedConcreteHitMassCount` proves `c5abc_compl_le` from `C5abcInputs`,
leaving the single H.8 counting field `half_mass` (the paper's "at least half
the ideal mass reaches an immediate factor or an accepted dense field").

### C3 and C4 status

`RandomizedConcreteTV.bigConcreteC3` is a genuine full
`ConcreteC3Hypotheses` instance: the structural `DirectFormSpec` fields are
explicit, the sample type's `DecidableEq` obstruction is resolved with a
one-point `BigCoins` type, and `heps_le` is proved as the numeric inequality
`big_heps_le` (not assumed). The modulus is a huge opaque prime, not the paper's
class group, so this is a concrete instance of the interface rather than the
paper's sampler.

For C4, `s0Cost ≤ 4·(log₂N+1)²` and `s7Cost ≤ 12·(log₂N+1)⁴` are proved, and
`ConcreteC4Hypotheses.ofS0S7` discharges those two stages. The other eight stage
costs remain explicit.

## Waves 4-7: sub-lemma discharge and the discharged endpoint

Waves 4-7 replace most of the opaque `PaperEndpointInputs` fields by smaller
explicit certificates and compose them.

| Module group | Content |
|---|---|
| `RandomizedL18_4{CellData,CellCount,Numerator,Mass,Thin,ThinAggregate,LargeSieve,LargeSieveInputs,LatticeCount,Full}.lean` | L18.4 fully decomposed and recomposed: large sieve, RH cell counts, numerator count, mass/error, thin-pair lattice aggregation, canonical cell data, rational-cell lattice count, and the full `L18_4Certificate` |
| `RandomizedL19{SecondMoment,Energy,Poisson,ZeroMode,Thin,ThinFinite,Muq,Full}.lean` | L19.4-L19.6 decomposed into energy/denominator/zero-mode/thin certificates and recomposed in `L19FullCertificate` |
| `RandomizedC5{Algebra,Coupling,HalfMass,Full}.lean` | C5.a-e decomposed into pool coverage, H.8 half-mass, algebra (L34-L37), adaptive coupling, and recomposed in `C5FullInputs` |
| `RandomizedConcreteStageCost{S1S2,S3,S469,S5,S8}.lean` | Concrete S0-S9 costs; all ten stages have polynomial bounds and `ConcreteC4Hypotheses` compatibility |
| `RandomizedL{20_2,20_4,21_2,27_1,30,34,4,P1}.lean` | The remaining paper leaves decomposed into explicit paper-level inputs |
| `RandomizedPaperEndpointDischarged.lean` | Composes L18.4Full, L19Full and C5Full into `DischargedPaperEndpointInputs`; no `hitMass` field remains |

The capstone theorem is

```lean
theorem serialized_assembled_balancedEnvelopeInfimum_from_dischargedInputs
    (line : DirichletLZerosOnLine) :
  ∃ (k : ℕ) (sound : ∀ n ≥ 2, ...),
  ∀ (E : ∀ s n, 3 ≤ n → HardEpochData n),
    (∀ s D, s.Valid D → DischargedPaperEndpointInputs (E s) D) →
    1.9839824118071388228 < balancedEnvelopeInfimum ∧
    balancedEnvelopeInfimum < 1.9839824118071388230 ∧
    (decoder permutation correctness) ∧
    ∀ ε > 0, ∀ᶠ n, ∀ hn : 2 ≤ n,
      mean (serializedFactor ...) ... ≤
        ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n))
```

`DischargedPaperEndpointInputs` contains the eleven paper leaves not reduced
here, the C1-C4 inputs, and the C5Full certificate. The old opaque L18.4 leaf,
L19.4-L19.6 leaves and `hitMass` bridge are gone. The remaining adapters are
`concrete`/`concrete_eq` (the ambient epoch family is the concrete one) and
`loss_le` (the concrete C5 total loss is dominated by the paper ledger).

### Wave 8: the real reduced-form spec and the sub-lemma layer

`RandomizedConcreteFormSpec.lean` constructs the actual `DirectFormSpec` over
`ReducedForms N` for discriminant `-8N`:

- `Form = ℕ × ℤ × ℕ` (`[A, 2b, C]`), `U = sqrt (8N/3)`;
- `roots N A` is the explicit balanced-root image of `x² = -2N` under
  `ZMod.valMinAbs`;
- `buildForm` computes `C = (b² + 2N)/A` and accepts exactly the reduced forms;
- `concreteFormSpec N hN` proves all seven `DirectFormSpec` fields.

This replaces the toy prime modulus in `bigConcreteC3` as the C3 interface.

`RandomizedDischargedAdapters.lean` reduces the three discharged-endpoint
adapters:

- `concrete`/`concrete_eq` are definitional for `concreteHardFamily` and
  `concreteCostFamily`;
- `loss_le` is equivalent to the explicit inequality between the eight-term
  concrete C5 loss and the twelve-term paper ledger
  (`loss_le_iff_explicit`);
- `dischargedInputsOfConcrete` and `dischargedInputsOfConcreteCost` build
  `DischargedPaperEndpointInputs` from concrete C1–C4/C5 inputs.

The remaining sub-lemma modules are:

| Module | Reduced content |
|---|---|
| `RandomizedL18_4LargeSieveResidual` | `perCell_ge_one` and `energy_le` from the spectral energy identity; residual `MellinConvolutionEnergyBudget` |
| `RandomizedL19EnergyMass`, `RandomizedL19ZeroModeFinite`, `RandomizedL19ThinFinite` | envelope growth, marginal mass, and the finite initial segments |
| `RandomizedL20_2Sub`, `RandomizedL20_4Sub` | saddle/CRT arithmetic, conditioned Paley–Zygmund, pool/dyad/G.11–G.12 reductions |
| `RandomizedL27_1Sub`, `RandomizedL30Sub`, `RandomizedL34Sub` | Hasse/Deuring arithmetic, curve-budget/union bounds, probe/class-count/mask arithmetic |
| `RandomizedL4Sub` | local splitting/CRT, principal-genus bridge, small-band product, reduced-form construction |

These files keep the genuinely paper-level estimates as explicit `Prop`s; no
loss, mass, count, or error is set to zero.

### Wave 9: real-form C3, good-event composition, and the fully discharged endpoint

- `RandomizedConcreteC3Real.lean` instantiates the C3 interface with the real
  `concreteFormSpec` over `ReducedForms N` (discriminant `-8N`). Its
  `ConcreteC3RealInputs` reduces the TV hypotheses to explicit `eta`/`gcdMass`/
  `hideal`/`hgcd`/`hactual`/`heps_le` fields; `c3Inputs` and `hit_prob_ge` are
  proved. This replaces the toy prime modulus of `bigConcreteC3`.
- `RandomizedC5GoodIff.lean` removes the structural `good_iff` hypothesis for
  the concrete epoch: `ConcreteEpochData.good` is definitionally the solver
  success set, and the C5 events are defined as its projections. It also
  provides a concrete `C5FullInputs` instance (`ofToyEpoch`) with positive loss.
- `RandomizedPaperEndpointFullyDischarged.lean` replaces the remaining
  `L18_4Inputs`/`L19Inputs` fields by `L18_4Certificate`/`L19FullCertificate`
  and composes the full C5 certificate. The endpoint
  `serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs` has
  only the eight unreduced paper leaves, C1-C4, the full certificates, and the
  concrete adapters left.

### Wave 10: the real C3 budget and its exact obstruction

`RandomizedConcreteC3Budget.lean` discharges the definitional C3 fields for
`realEpoch`:

- `eta = 0`, `hideal` by reflexivity (`ideal` is the uniform law itself);
- `hactual` by reflexivity (`actual` is the direct retry law);
- `gcdMass = (gcdExitProb (realSpec N hN) (realJ N)).toReal`, `hgcd` by
  `le_rfl`.

It reduces `heps_le` to the single explicit inequality

```text
2·L·(1+log L)·(∑_{p|N} 4/(p−1))·(log 2N)^80 / #(ReducedForms N)
  + ∑_{p|N} 1/p  ≤  1/32,        L = sqrt(8N/3).
```

**This inequality is false for every sufficiently large `N` divisible by 3**
under the current crude `directMissingRootMass` bound: the numerator carries
`(log 2N)^80`, while the GRH class-number lower bound is only `√N/log N`, and
`∑_{p|N} 1/p ≥ 2` for `3 ∣ N`. The budget therefore grows like
`(log N)^82`, not decays. The file proves this and does not assert an
eventual-for-all-`N` statement.

For **prime** `N` the reciprocal sum is `4/(N−1)` and the budget is
`O((log N)^82 / N)`, so `heps_le` does hold eventually under
`DirichletLZerosOnLine`:

```lean
eventually_heps_le_of_prime (line : DirichletLZerosOnLine) :
  ∃ N₀, ∀ N ≥ N₀, ∀ hN h2, Nat.Prime N →
    directSamplerEpsilon (realSpec N hN) realEta (realGcdMass N hN) ≤ 1/32

exists_concreteC3RealInputs_of_prime (line) :
  ∃ N₀, ∀ N ≥ N₀, ∀ hN h2, Nat.Prime N →
    Nonempty (ConcreteC3RealInputs N hN h2)
```

**Wave 11 closes the rough branch.** `RandomizedConcreteC3Rough.lean` proves
that for `IsRough (roughThreshold n) n` the `1/B` saving dominates the
polylogarithmic numerator:

```lean
theorem eventually_heps_le_of_rough (line : DirichletLZerosOnLine) :
  ∀ᶠ n, ∀ (hN : Odd n), 3 ≤ n → IsRough (roughThreshold n) n →
    directSamplerEpsilon (realSpec n hN) realEta (realGcdMass n hN) ≤ 1/32

theorem eventually_concreteC3RealInputs_of_rough (line) :
  ∀ᶠ n, ∀ hN, 3 ≤ n → IsRough (roughThreshold n) n →
    Nonempty (ConcreteC3RealInputs n hN ...)
```

The proof uses `∑_{p|N} 1/p ≤ ω(N)/B`, `ω(N) ≤ log N/log B`, and
`B = exp((log n)^{2/3})` beating `(log N)^83`. So the real C3 budget is
discharged on exactly the rough branch the randomized endpoint uses; the false
general-`N` statement is only the small-prime branch, which the prepass handles.

### Wave 11: the last sub-lemma reductions

| Module | Reduction |
|---|---|
| `RandomizedL20_2Saddle` | saddle scale/mean to explicit smooth-number count/mass; character sums to `PrimeBinProductBound`/Mellin envelope |
| `RandomizedL20_4Conditioned` | conditioned two-point/mean to unconditioned second moment + event/complement mass; interior concentration split into base/rational/elliptic |
| `RandomizedL21_2Perron` | Plancherel split eliminated; tent smoothing reduced to Chebyshev + polynomial absorption; Perron/Fourier/density remain minimal |
| `RandomizedL27Deuring` | Deuring counts to Frobenius discriminant + Hurwitz lower bound; curve total to the `j`-line stratification |
| `RandomizedL30Younis` | Younis count to odd relative short-interval + global lower; LPP to raw model count + normalization |
| `RandomizedL34Dedekind` | zero-free/Stark/range/Chebotarev to smallest equivalent one-sided forms; slack error form |
| `RandomizedL4Faithful` | coprime composition proved by CRT; non-coprime Cox correction and squaring primitive selection isolated; `FaithfulFormComposition` shown false for odd `N` |
| `RandomizedP1Analytic` | genus-two/ECM success and cost interfaces; trial-division cost obstruction formalized |
| `RandomizedConcreteC3Rough` | rough-branch C3 budget discharged under GRH |

The remaining explicit `Prop`s are the genuinely analytic inputs of those
modules (smooth-number saddle/concentration, Perron/Fourier/tent estimates,
Hurwitz/Deuring curve counts, Younis/LPP short-interval counts, Dedekind
zero-free/Stark/Chebotarev, Cox correction, prepass success/cost).

## What is not proved

1. **The concrete epoch's analytic content.** Waves 2-5 supply the
   construction-level S0–S9 epoch (`ConcreteEpochData`), a full concrete
   `ConcreteC3Hypotheses` instance (`bigConcreteC3`), concrete S0–S9 stage costs,
   and the C5 `HitMassInputs`/`C5FullInputs` decomposition. Wave 9 supplies the
   real reduced-form `DirectFormSpec`, and wave 10 reduces its C3 budget to the
   explicit `RealC3BudgetInputs`. That budget is **discharged on the rough
   branch** by wave 11 (`eventually_concreteC3RealInputs_of_rough`), which is
   exactly the branch the randomized endpoint uses. The literal budget is false
   for large `N` divisible by 3 under the crude missing-root bound, but those
   inputs go through the small-prime prepass.
2. **The analytic leaves.** L18.4 and L19.4–L19.6 are now decomposed into
   explicit certificates and recomposed (`L18_4Full`, `L19Full`). The remaining
   paper-level leaves are L20.2, L20.4, L21.2, L27.1, L30, L34, L4/L25/L36, and
   P1, each with its own explicit sub-input structure. Their genuinely
   paper-level sub-lemmas are not proved.
3. **P1.** Trial division to `roughThreshold n = exp((log n)^{2/3})` has the
   correct splitting behaviour but cost `exp((log n)^{2/3})`, not
   `exp(o(scale n))`. The rough endpoint keeps this as an explicit hypothesis.
   This is the same gap as the blueprint's genus-two/ECM prepass.
4. **The residual lower bound.** `OracleRootExtractionLowerBound` is stated but
   not proved and not shown inhabited. It is the honest missing assumption
   behind a non-vacuous costed endpoint.
5. **The full manuscript bound.** Consequently, the numerical
   `L_N[1/3, 1.9839824…]` claim is not a theorem of this branch. What is a
   theorem is the reduction from the named ledger to the serialized driver, the
   wave-2 paper-assumption endpoint, the wave-7 discharged endpoint, and the
   wave-9 fully discharged endpoint
   `serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs`,
   whose remaining inputs are the eight unreduced paper leaves, C1–C4, the full
   L18.4/L19/C5 certificates, and the concrete adapters. The real C3 budget is
   certified for prime moduli; composite `N` needs a sharper TV accounting.

## Reading order

1. `research/randomized-epoch-blueprint.md` — original dependency tree and gap
   estimates.
2. `research/randomized-gap-audit.md` — independent audit of the five serious
   gaps, with exact Lean anchors.
3. `Cogentic/RandomizedEpochVacuity.lean` — the counterexample.
4. `Cogentic/RandomizedCostedEpoch.lean` — the soundness repair and its residual
   lower bound.
5. `Cogentic/RandomizedEpochAnalyticInputs.lean` — the explicit ledger.
6. `Cogentic/RandomizedEndToEnd.lean` — the conditional end-to-end theorem.
7. `Cogentic/RandomizedConcreteEpoch.lean` — the concrete S0–S9 epoch.
8. `Cogentic/RandomizedConcreteEpochChecks.lean` — C1/C2 for the concrete epoch.
9. `Cogentic/RandomizedConcreteEpochCost.lean` — C3/C4 bridge.
10. `Cogentic/RandomizedPaperLeafStatements.lean` — the twelve paper leaves.
11. `Cogentic/RandomizedPaperEndpoint.lean` — the paper-assumption endpoint.
12. `Cogentic/RandomizedL18_4.lean` — the L18.4 decomposition and the
    `SubexpLeaf` numeric chain.
13. `Cogentic/RandomizedL18_4{CellCount,Numerator,Thin,LargeSieve}.lean` — the
    four L18.4 sub-lemma reductions.
14. `Cogentic/RandomizedConcreteHitMass{,Count}.lean` — the C5 `hitMass`
    decomposition and the C5.a–c counting reduction.
15. `Cogentic/RandomizedConcreteTV.lean` and
    `Cogentic/RandomizedConcreteStageCost*.lean` — the full concrete C3 instance
    and the concrete S0-S9 cost bounds.
16. `Cogentic/RandomizedL18_4Full.lean` — the recomposed L18.4 certificate.
17. `Cogentic/RandomizedL19Full.lean` — the recomposed L19.4-L19.6 certificate.
18. `Cogentic/RandomizedC5Full.lean` — the recomposed C5.a-e hit-mass
    certificate.
19. `Cogentic/RandomizedPaperEndpointDischarged.lean` — the discharged endpoint
    with no opaque L18.4/L19/`hitMass` fields.
