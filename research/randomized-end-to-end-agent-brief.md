# Randomized factoring end-to-end Lean workstreams

Common base: branch `explore/randomized-one-third`, commit `0bcb1db`, worktree
`/home/gldanoob/dev/int-fac-randomized`.

Read first:

- `research/randomized-epoch-blueprint.md` (the previous agent's gap analysis).
- `formal/cogentic/Cogentic/RandomizedEpochAssembly.lean` (`HardEpochData`,
  `HardEpochAsymptoticBound`, `serialized_assembled_epoch_from_critical_line`).
- `formal/cogentic/Cogentic/RandomizedEpochVacuity.lean` (the oracle epoch showing the
  current `HardEpochAsymptoticBound` interface is vacuous).
- `formal/cogentic/RandomizedFactoring.lean` (the current audit target).

The existing end-to-end theorem is conditional on `HardEpochAsymptoticBound E C`.
The previous agent proved that this hypothesis can be met by a zero-work oracle epoch.
The goal of these workstreams is to make the endpoint non-vacuous and to replace the
single opaque hypothesis with explicit, auditable analytic leaves. Do not claim the
manuscript's numerical bound is proved unless the concrete epoch and all leaves are
discharged.

## Hard constraints

- Lean toolchain: `/home/gldanoob/dev/int-fac-randomized/formal/cogentic/lean-toolchain`.
- Before any Lean command:
  ```sh
  cd /home/gldanoob/dev/int-fac-randomized/formal/cogentic
  export PATH="$HOME/.elan/bin:$PATH"
  export LEAN_NUM_THREADS=1
  ```
- Serialize Lean invocations with `flock /tmp/intfac-lean.lock -c '...'`. The host has
  about 7.6 GiB RAM; at most one heavy Lean process at a time.
- Compile only your own file with `lake env lean Cogentic/YourFile.lean`. Do not run
  `lake build`, `make`, or a whole-tree build.
- Do not use `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choice` to hide a
  missing construction beyond what the surrounding code already uses.
- Do not modify existing shared files. Add imports inside your own new file. If a shared
  change is genuinely required, report it instead of making it.
- Do not commit. Leave the file in the worktree and report the exact compile command and
  printed axioms.
- If a requested theorem is not provable from the current interfaces, produce the
  strongest compiling theorem with the missing statement exposed as an explicit `Prop`
  hypothesis. Report the exact blocker. A compiling reduction is useful; a fake proof is
  not.

## Workstreams

| File | Deliverable |
|---|---|
| `Cogentic/RandomizedCostedEpoch.lean` | A costed epoch interface whose `pubWork` is the cost of a program that computes the transcript data; the assembly theorem for it; a formal statement that the zero-work oracle epoch is not an instance under a zero-cost/constant-program condition. |
| `Cogentic/RandomizedRoughEndpoint.lean` | The end-to-end theorem with `HardEpochAsymptoticBound` required only on `IsRough (roughThreshold n) n`, using `RandomizedSmallPrimePrepass.factor_expected_from_prepass_and_rough_epoch` and the trial prepass. |
| `Cogentic/RandomizedEpochAnalyticInputs.lean` | A structure collecting the named analytic leaves from the blueprint, plus `hardEpochAsymptoticBound_of_analyticInputs` reducing the bound to those fields via the existing glue. C1/C2 should be discharged where the current `ofMultiField` lemmas allow. |
| `Cogentic/RandomizedEpochTV.lean` | An explicit total-variation bound `pmfTotalVariation ideal actual ≤ ε` for an epoch built from the direct class sampler, using `RandomizedDirectClassSampler` lemmas. |
| `Cogentic/RandomizedEpochWork.lean` | A public-work bound `mean E.actual pubWork ≤ exp((C+δ/2) scale n)` for an epoch whose `pubWork` is a sum of named stage costs satisfying the existing schedule hypotheses. |
| `Cogentic/RandomizedEpochPool.lean` | A single field-pool coverage theorem assembled from `RandomizedFieldPoolDescent` (blueprint L17), with the moment/trimming hypotheses explicit. |
| `Cogentic/RandomizedEpochAlgebra.lean` | The final `γ/2 - ε ≥ c` split-probability assembly from `RandomizedFieldExtraction` and `RandomizedEpochSuccess`, given C1/C2/TV inputs. |
| `Cogentic/RandomizedTrialEndpoint.lean` | A fully unconditional randomized runtime theorem for a simple trial-division algorithm, as a cost-model sanity check. It may use a weak exponent, but it must be a real end-to-end theorem with no epoch hypothesis. |
| `Makefile`, `README.md`, `research/randomized-epoch-blueprint.md` | Integration: add a randomized end-to-end check target, record exact build status, and update the formal-status table. No Lean proof edits. |
| `research/randomized-gap-audit.md` | Independent audit of the blueprint's five serious gaps against the current Lean statements, with file:line references and a prioritized remaining-work list. No Lean edits. |

## Definition of done for a Lean workstream

1. The new file compiles with `lake env lean Cogentic/YourFile.lean`.
2. The key theorem is printed with `#print axioms` and depends only on
   `[propext, Classical.choice, Quot.sound]` (or reports the exact extra axioms).
3. The report states the theorem signature, the remaining hypotheses, and whether any
   requested conclusion had to be weakened to an explicit hypothesis.
