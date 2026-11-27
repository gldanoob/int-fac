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

## What is not proved

1. **The concrete epoch's analytic content.** Wave 2 supplies the
   construction-level S0–S9 epoch (`ConcreteEpochData`) and a C3/C4 bridge, but
   `HardEpochData` still exposes no field-pool object, moment functionals, or
   recognizer events. The concrete stage cost functions, the C3 TV estimate, the
   C4 per-stage mean bounds, and the C5 `hitMass` bridge remain explicit
   hypotheses rather than instances.
2. **The analytic leaves.** L19.4–L19.6 (narrow-width second moment), L20.2
   (interior concentration), L20.4 (child-root-conditioned two-point bound),
   L21.2 (RH smooth numbers near integer centres), L27.1 (Lenstra–Pomerance
   ECM), L30 (genus-two partial factorer), L34 (effective Chebotarev), L18.4
   (large sieve / G.3), and L4/L25/L36 (non-maximal-order form composition)
   remain paper-level.
3. **P1.** Trial division to `roughThreshold n = exp((log n)^{2/3})` has the
   correct splitting behaviour but cost `exp((log n)^{2/3})`, not
   `exp(o(scale n))`. The rough endpoint keeps this as an explicit hypothesis.
   This is the same gap as the blueprint's genus-two/ECM prepass.
4. **The residual lower bound.** `OracleRootExtractionLowerBound` is stated but
   not proved and not shown inhabited. It is the honest missing assumption
   behind a non-vacuous costed endpoint.
5. **The full manuscript bound.** Consequently, the numerical
   `L_N[1/3, 1.9839824…]` claim is not a theorem of this branch. What is a
   theorem is the reduction from the named ledger to the serialized driver, and
   (wave 2) the reduction from the twelve paper leaves plus C1–C4 and the C5
   `hitMass` bridge to that same driver.

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
