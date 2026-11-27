# Randomized factoring end-to-end: wave 3

Base: branch `explore/randomized-one-third`, current HEAD includes waves 1-2.
Read `research/randomized-end-to-end-status.md`,
`research/randomized-gap-audit.md`, and
`research/randomized-end-to-end-wave2-brief.md` first.

The paper-level endpoint

```lean
Cogentic.RandomizedPaperEndpoint.serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions
```

is kernel-checked but conditional on `PaperEndpointInputs`: the twelve paper
leaves, C1-C4, and the `hitMass` bridge. Wave 3 attacks the first requested
pieces directly:

- L18.4 (rational-good environments / large sieve);
- concrete per-stage work for the S0-S9 epoch;
- concrete TV estimates for a `DirectFormSpec`.

No agent may fake a paper lemma with `sorry`, `axiom`, or a zero loss. If a
paper estimate cannot be proved, decompose it into smaller explicit hypotheses
and prove the reduction. State the remaining sub-lemmas precisely.

## Constraints

Same as before: `flock /tmp/intfac-lean.lock`, `LEAN_NUM_THREADS=1`,
`PATH="$HOME/.elan/bin:$PATH"`, new file only, no shared edits, no commit.

## W17. L18.4 decomposition

File `Cogentic/RandomizedL18_4.lean`.

Target: a theorem producing the L18.4 `SubexpLeaf` (or the `C5Inputs.l18_4`
field) from smaller, explicitly named estimates:

- a large-sieve / second-moment inequality for the relevant rational cells;
- RH prime counts in the denominator cells;
- the rational-good cell partition and its multiplicity/energy loss.

Use the existing `RandomizedEpochPool`/`RandomizedPrimeBin*` lemmas where they
apply. If the full leaf needs definitions not present, define a local
`L18_4Inputs` structure carrying those estimates and prove the leaf from it.
The deliverable is a compiling reduction, not a fake proof. Document exactly
which sub-lemma is still paper-level.

## W18. Concrete S0/S7 stage work

File `Cogentic/RandomizedConcreteStageCost.lean`.

Target: instantiate two named stages of `RandomizedConcreteEpoch` with concrete
cost functions and prove their `ConcreteC4Hypotheses`-style per-stage bounds:

- S0: deterministic integer parameter computation from the input bit length.
  Define the parameters and a polynomial bit-cost bound (e.g. `O(n^2)` or
  `O(n^3)`), with a proof.
- S7: sparse `F₂` dependency. Use `RandomizedPadeCost`/`RandomizedSparseProducts`
  if they provide a concrete cost; otherwise define the cost from the existing
  Padé/Krylov stage and prove a polynomial bound in the matrix dimensions.

Do not claim the other stages. The deliverable is two concrete stage-cost
functions and their bounds, plus the `StageDecomposition` compatibility with
`RandomizedConcreteEpoch`.

## W19. Concrete TV instance

File `Cogentic/RandomizedConcreteTV.lean`.

Target: a concrete `DirectFormSpec` instance (a simple form type and explicit
roots/buildForm data) and a proof of the `ConcreteC3Hypotheses` structural
fields for an epoch whose `actual` is `directRetryConditionalPMF` and whose
`ideal` is `uniformOfFinset` (or the closest existing concrete pair). The
deliverable is a concrete `C3Inputs`/`ConcreteC3Hypotheses`, not the full paper
class-group sampler. If the `DirectFormSpec` fields are too large, prove the
reduction from a smaller `ConcreteSpecInputs` structure and state the remaining
field proofs.

## Definition of done

1. The new file compiles with no `sorry`/`admit`/`axiom`/`native_decide`.
2. `#print axioms` is `[propext, Classical.choice, Quot.sound]`.
3. The report states the theorem signatures, the decomposition, and the exact
   remaining paper-level sub-lemmas.
