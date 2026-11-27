# Randomized factoring: end-to-end Lean status

Branch `explore/randomized-one-third`, base commit `0bcb1db`, Lean
`leanprover/lean4:v4.33.1`. This note records what the end-to-end pass actually
proved. The short version: the conditional assembly is kernel-checked and is now
composed with an explicit analytic-input ledger, but the manuscript bound
itself is **not** proved. The current `HardEpochAsymptoticBound` interface is
vacuous as stated, and the concrete KeyBreak epoch is still missing.

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

## What is not proved

1. **The concrete S0–S9 epoch.** `HardEpochData` still has no field-pool object,
   moment functionals, recognizer events, or concrete cost functions. C4's
   `work_le` and C5's `hitMass` cannot be instantiated until that epoch is
   defined.
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
   theorem is the reduction from the named ledger to the serialized driver.

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
