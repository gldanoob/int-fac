# Deterministic factoring Lean handoff, 26 November 2026

After this handoff the local proof reached the [two-thirds factoring theorem](../formal/cogentic/Cogentic/TwoThirdsFactorization.lean). The [verification report](cogentic-worst-case-verification.md) gives its hypotheses, running time and reproduction commands. The checkpoints below describe the earlier paused session.

The main goal is paused at the user's request. Resume the proof of the deterministic worst-case two-thirds factoring bound, allowing the pinned results of Cogentic as inputs. The open local assertion is that sufficiently many dyadic targets on every sufficiently large input surviving the preliminary tests have a successful tuple in the four-coordinate box. The existing conditional endpoint still takes that assertion as a hypothesis. The concrete binary cost proof also needs its final modules built and audited. The separate one-third branch is exploratory.

## Checkpoints and worktrees

| Worktree | Local branch and checkpoint | Contents |
|---|---|---|
| `/home/gldanoob/dev/int-fac` | `main`, proof checkpoint `67a267613535` | All 43 in-progress Lean source changes, including unverified drafts. Earlier commits `c30a5ca` and `7fb093e` cover the early-return search, binary schedule, leading coefficient, and sharp outer-count conversion. The existing untracked `yay/` directory is outside this work. |
| `/home/gldanoob/dev/int-fac-one-third` | `explore/deterministic-one-third`, `61fa484` | Manuscript reduction to a scalar counting problem, plus a finite replay. This worktree starts from `7fb093e`. |

Both project branches are local. The [previous verification report](cogentic-worst-case-verification.md) and [fixed-schedule manuscript](cogentic-deterministic-two-thirds.md) give the definitions and source ledger. The pinned paper's Lemma 7.5 supplies a uniform polynomial-time extractor under its listed conditions. Proposition 10.1 specializes to the paper's original schedule. Its conclusion on the modified schedule is the local mathematical obligation.

## Where to resume the rank proof

1. **Center the empirical observables.** In `EmpiricalBranchObservable.lean`, apply `mesh_numerator_center_error` and `ordinary_branch_normalizer` to the small-mean premise of `physical_pair_centered_observable`. The proposed center averages the independent Chinese-remainder and saddle numerator over every raw mesh position. There is an unchecked draft of `canonical_mesh_saddle_range` in `~/.cache/intfac-handoff-20261126/intfac-rank-numerator.inc`. [Empirical moments](../formal/cogentic/Cogentic/EmpiricalBranchObservable.lean) · [Normalizer](../formal/cogentic/Cogentic/OrdinaryBranchNormalizer.lean)
2. **Control all row pairs on the same draw.** Use `ordinary_pair_hit_reference` divided by the square root of the two row masses with `admitted_physical_gram_budget`. Include same-prime, singleton, target and finite–log entries. The log associated with the matching root can vary by as much as log 2 within one cell. Carry its mesh-position variation through the second moment. Account for rejected marks and deleted rows on the same tuple. [Admitted-mass estimate](../formal/cogentic/Cogentic/OrdinaryMass.lean) · [Pair reference](../formal/cogentic/Cogentic/PairHitReference.lean) · [Log profiles](../formal/cogentic/Cogentic/RawLogProfiles.lean)
3. **Transfer the lower bound and finish coverage.** The candidate reference estimates are `raw_grid_model_margin` and `raw_grid_average_energy`. The former gives $(g+m)^2+13F/16\le Q$ and $m^2\le120000dF$ under its admitted-mass condition. Transfer these estimates to the retained empirical quadratic form, invoke `positiveMarkCore_of_perpendicular`, and produce a boxed witness. The driver needs a set of distinct successful targets with $3\beta |S|\ge2^\beta$. `dense_of_all_hits` is available if coverage holds for every target. [Raw model](../formal/cogentic/Cogentic/RawGridModel.lean) · [Mesh energy](../formal/cogentic/Cogentic/RawGridEnergy.lean) · [Positive core](../formal/cogentic/Cogentic/SurvivingGram.lean) · [Target threshold](../formal/cogentic/Cogentic/CompanionReduction.lean)

**Verification status.** `MarkTilts` built against the real imports. A direct Lean check of `TargetBranchEnergy` passed its printed axiom checks. The rank worker checked `OrdinaryMass`, `OrdinaryPairRemainder`, `PhysicalProfileVariance`, `PhysicalBranchVariance`, `BranchInsertionProfiles` and `EmpiricalBranchObservable` in an isolated file with copied dependency signatures. The coverage worker used similar probes for `DividedMarkTilts`, `OrdinaryBranchMasks`, `OrdinaryBranchNormalizer`, `OrdinaryModelBlocks`, `RawGridModel` and `RawGridEnergy`. Those checks still need real package builds. `ordinary_single_hit_reference` and `AuxiliaryBranchPrime` are unchecked. The first known error in `RawLogProfiles.lean` is the multiline `exact` following `simp only [abs_mul]` at line 81. Recheck the following sum after fixing the parse error.

## Where to resume the bit-cost proof

The draft `Companion.factor_words_of_dense_hits` in `BinaryFactorization.lean` gives binary output, multiplicities and a runtime conclusion conditional on coverage and the upstream contracts. It has not passed a real build. The earlier `factor_tree_of_local_bounds` additionally parameterizes residual work. The new files aim to replace that parameter with the actual search, driver and output charges. [Binary endpoint](../formal/cogentic/Cogentic/BinaryFactorization.lean) · [Driver cost](../formal/cogentic/Cogentic/DriverBitCost.lean) · [Metered search](../formal/cogentic/Cogentic/SearchTraceCost.lean)

The metered search loop, schedule words, leading coefficient, driver setup, axis lists, precision words, observation arithmetic, exhaustive mark cost, canonical quotient/output traversal, finite fallback, back substitution and integer-family conversion have passed real Lean checks. Rebuild the sources from the checkpoint. The observations and generator-list files have small edits newer than their last direct checks. `ExhaustiveMarkCost.olean` and the direct run's axiom output exist after the fixed box-sum rewrite. The earlier monolithic Lake job logged a leading-coefficient timeout before that source was fixed and checked separately. Its process and the solver retry are gone. There is no verified complete package build for this checkpoint.

Start the real dependency chain here. On this host, the user has installed Sage and the per-user Elan installation already resolves the pinned Lean 4.33.1 toolchain in the Lake package.

```bash
cd /home/gldanoob/dev/int-fac/formal/cogentic
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
lake build Cogentic.SolverArithmeticCost
lake build Cogentic.SolverBoxCost Cogentic.SearchTraceCost
lake build Cogentic.DriverBitCost Cogentic.BinaryFactorization
```

The last solver error was in `integerWork_eq` at the summand using `Vector.ofFn`. The checkpoint contains a `simp only [Vector.getElem_ofFn]` fix. Its retry produced no completion log or `.olean`. The worker's suggested fallback is to simplify both `Vector.get_eq_getElem` and `Vector.getElem_ofFn` when applying `congrArg (fun x => (integerizeWords x).2) (funext (d j))`. The box proof passed a signature probe. The later driver and binary output proofs require checking against the real imports. Review each counted stage against the reachable executable path before claiming a bound on total bit operations.

Once the rank proof is complete, connect it to the binary endpoint, add the final imports and names to the axiom audit in `formal/cogentic/Cogentic.lean`, and rebuild. The manuscript's leading coefficient 400000 refers to the polynomial-time extractor. `search_work_leading` proves the sharp outer-count conversion with a per-call bound of $2^{O(h)}$. The concrete exhaustive-minor implementation currently targets a larger constant in the two-thirds exponent.

## Checks and resources

- The seven standalone Lean checks, PARI/GP suite and all five two-thirds replays (including the two Sage runs) passed earlier. After integration, run `make check check-two-thirds` from the repository root with `PATH="$HOME/.elan/bin:$PATH"`, `LEAN="$HOME/.cache/intfac-toolchain/lean-4.33.1-linux/bin/lean"` and `DOT_SAGE=/tmp/rsa-sage-check`.
- The pinned mathlib cache and 331 SHA-verified transitive upstream artifacts for the default build are present in `formal/cogentic/.lake`. The default theorem takes the archive's exact critical-line proposition as an input. The optional `CogenticWithGRH` target links the full frozen archive. That optional build was not run here. See the [verification report](cogentic-worst-case-verification.md) for its prerequisites.
- Scratch source, the unintegrated numerator lemma, selected logs and helpers are saved locally in `~/.cache/intfac-handoff-20261126/`. The helper `intfac-lean-check` serializes direct Lean checks. `intfac-resume-leanpath` records this worktree's import path. Some probe scripts manufacture temporary declarations. Only production imports and the package axiom audit count as final verification. This host has about 7.6 GiB RAM. Limit simultaneous Lean compiler jobs even if additional worker slots are available.
- On the one-third branch, read `research/cogentic-scalar-divisor-count.md` and rerun `python3 -B experiments/cogentic-scalar-divisor-count.py`. The handoff reran 144 exact projected counts, 288 interval brackets, 144 counting bounds and 24 prescribed-accuracy checks. The open step is a uniform deterministic scalar divisor count at large moduli with the stated additive error and runtime. The branch does not establish worst-case one-third factoring.
