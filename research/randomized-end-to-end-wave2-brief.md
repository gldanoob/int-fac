# Randomized factoring end-to-end: wave 2

Base: branch `explore/randomized-one-third`, commit `0bcb1db` plus the wave-1
work in the worktree `/home/gldanoob/dev/int-fac-randomized`.

Read `research/randomized-end-to-end-status.md` and
`research/randomized-gap-audit.md` first. The wave-1 modules are:

- `Cogentic/RandomizedEpochVacuity.lean`
- `Cogentic/RandomizedCostedEpoch.lean`
- `Cogentic/RandomizedEpochAnalyticInputs.lean`
- `Cogentic/RandomizedEpochWork.lean`
- `Cogentic/RandomizedEpochTV.lean`
- `Cogentic/RandomizedEpochPool.lean`
- `Cogentic/RandomizedEpochPrivate.lean`
- `Cogentic/RandomizedEpochAlgebra.lean`
- `Cogentic/RandomizedRoughEndpoint.lean`
- `Cogentic/RandomizedTrialEndpoint.lean`
- `Cogentic/RandomizedEndToEnd.lean`

The remaining gap is the concrete S0-S9 epoch and the 12 analytic leaves. Do
not pretend an unproved paper lemma is proved. The goal of this wave is to
make the epoch and the paper assumptions explicit and to wire them into the
kernel-checked endpoint.

## Constraints

Same as `research/randomized-end-to-end-agent-brief.md`:

- `cd formal/cogentic`, `export PATH="$HOME/.elan/bin:$PATH"`,
  `export LEAN_NUM_THREADS=1`.
- Build with `flock /tmp/intfac-lean.lock -c 'lake env lean Cogentic/YourFile.lean'`
  or `lake build Cogentic.YourFile`.
- No `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose` to hide a
  missing construction.
- Only create your own new file. Do not edit shared files. If a shared change
  is required, report it.
- Do not commit.

## Workstreams

### W11. Concrete epoch skeleton

File `Cogentic/RandomizedConcreteEpoch.lean`.

Define a record of the S0-S9 epoch data and a concrete `HardEpochData` from it:

- public/private type parameters, `ideal`/`actual` laws;
- a public solver `solver : Coins → (Label → (ZMod n)ˣ) → Option (PublicMultiFieldTranscript Label FieldId n)`
  (or an equivalent `Public` transcript type);
- `trace` exposing the solver output;
- `good` the set of successful solver outputs;
- `data` from `PublicMultiFieldTranscript.toTranscriptData`;
- `pubWork` as an explicit sum of named stage costs S0-S9, with a
  `StageDecomposition`-style pointwise identity.

Prove the `HardEpochData` fields and the pointwise work decomposition. Do not
claim any analytic estimate. The goal is a non-`Classical.choose` epoch whose
data is computed by the solver, so the vacuity loophole is structurally closed
at the epoch-construction level. State any missing solver/cost fields as
explicit structure fields with docstrings.

### W12. Concrete epoch C1/C2

File `Cogentic/RandomizedConcreteEpochChecks.lean`.

Import W11 and `RandomizedFieldExtraction`. Prove `CongruenceCheck` and
`HiddenUniform` for the concrete epoch from:

- the global product identity for `PublicMultiFieldTranscript`;
- the coordinatewise hidden-sign symmetry of the ideal law on the mask.

Use `HardEpochData.ofMultiField_congruenceCheck` and
`ofMultiField_hiddenUniform` where possible. State the two remaining hypotheses
(global product, hidden-sign symmetry) explicitly with docstrings pointing to
the manuscript. No `Classical.choose`.

### W13. Concrete epoch C3/C4

File `Cogentic/RandomizedConcreteEpochCost.lean`.

Import W11, `RandomizedEpochTV` and `RandomizedEpochWork`. Build the C3 and C4
inputs for the concrete epoch:

- C3: a `DirectFormSpec`-based TV bound via
  `RandomizedEpochTV.pmfTotalVariation_le_directSamplerEpsilon` and the epoch
  bridge `assembledAttempt_hit_prob_ge_of_directSampler`;
- C4: a `StageDecomposition` over the S0-S9 stage list and
  `RandomizedEpochWork.hardEpochAsymptoticBound_of_stagewise` /
  `eventually_mean_pubWork_le_exp_of_blueprintStages`.

Leave the concrete TV/work estimates as explicit hypotheses if the stage
implementations are not defined. The deliverable is a compiling bridge from the
concrete epoch's stage data to `C3Inputs`/`C4Inputs`.

### W14. Paper-level leaf statements

File `Cogentic/RandomizedPaperLeafStatements.lean`.

`RandomizedEpochAnalyticInputs.C5Inputs` currently uses weakened loss slots
`≤ exp(-2 * scale n)`. Define a structure `PaperAnalyticAssumptions E C` whose
fields are the *paper-level* statements for the 12 leaves, with docstrings
citing the blueprint section and the KeyBreak/manuscript lemma:

- L18.4 large sieve / G.3
- L19.4, L19.5, L19.6 narrow-width second moment
- L20.2 interior concentration
- L20.4 child-root-conditioned two-point bound
- L21.2 RH smooth numbers near integer centres
- L27.1 Lenstra-Pomerance ECM
- L30 genus-two partial factorer
- L34 effective Chebotarev
- L4/L25/L36 form composition
- P1 prepass

Then prove `EpochAnalyticInputs E C` from `PaperAnalyticAssumptions E C` plus
the C1-C4 inputs and the C5 `hitMass` bridge. If a paper statement does not
imply the loss slot without an extra estimate, add that estimate as an explicit
field, not as an axiom.

### W15. Paper-assumption endpoint

File `Cogentic/RandomizedPaperEndpoint.lean`.

Compose W14 with `Cogentic.RandomizedEndToEnd`:

```lean
theorem serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ...),
    ∀ (E : ∀ s n, 3 ≤ n → HardEpochData n),
      (∀ s D, s.Valid D → PaperAnalyticAssumptions (E s) D) →
      [correctness] ∧
      ∀ ε > 0, ∀ᶠ n, ∀ hn : 2 ≤ n,
        mean (serializedFactor ...) ... ≤
          ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n))
```

This is the honest paper-level endpoint: the only unproved inputs are the
paper's stated analytic lemmas, not an opaque `HardEpochAsymptoticBound`.
Print the axiom list.

### W16. Integration and audit

Files: `Makefile`, `README.md`, `research/randomized-end-to-end-status.md`.

Add the wave-2 modules to the `check-randomized-end-to-end` target once they
compile. Run the target with `flock` and `LEAN_NUM_THREADS=1`, check for
`sorryAx`, and update the status table with the new modules and the exact
remaining paper assumptions. Do not edit Lean proofs.

## Definition of done

1. The new file compiles with no `sorry`/`admit`/`axiom`/`native_decide`.
2. `#print axioms` depends only on `[propext, Classical.choice, Quot.sound]`.
3. The report states the theorem signatures, the remaining hypotheses, and
   whether any conclusion had to be weakened to an explicit `Prop`.
