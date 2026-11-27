# Randomized factoring end-to-end: wave 7 capstones

Base: `explore/randomized-one-third` at `b5fff17`. Read
`research/randomized-end-to-end-status.md` and the wave-3/4/5/6 briefs.

Wave 7 composes the sub-lemma reductions into larger certificates. Same
constraints: new file only, no shared edits, no commit, no
`sorry`/`admit`/`axiom`/`native_decide`, `flock /tmp/intfac-lean.lock`,
`LEAN_NUM_THREADS=1`, `PATH="$HOME/.elan/bin:$PATH"`. Do not fake a paper
estimate or set a loss to zero.

## W43. L18.4 full certificate

File `Cogentic/RandomizedL18_4Full.lean`. Compose `LargeSieveCertificate`,
`CellData`, `MassErrorInputs`, and `ThinAggregate` into a single
`L18_4Certificate` that yields an `L18_4Inputs` with all four analytic fields
discharged (the ambient scales/upper bounds remain explicit). Prove
`toSubexpLeaf`, `subexpLoss`, and `slot_le`.

## W44. L19 full certificate

File `Cogentic/RandomizedL19Full.lean`. Compose the L19.4 energy/denominator
replacements (`RandomizedL19Energy`, `RandomizedL19Poisson`), the L19.5
`ZeroModeCertificate`, and the L19.6 `LatticeThinInputs` into an `L19Inputs`
and prove `L19Inputs.leaves` / `slots_bounds`.

## W45. C5 hitMass full certificate

File `Cogentic/RandomizedC5Full.lean`. Compose `C5abcInputs` /
`HalfMassInputs`, `HitMassInputs`, `C5AlgebraInputs`, and `CouplingInputs`
into a single `HitMassInputs` whose `algebra`/`coupling` stages are the
decomposed ones. Prove `hitMass_of_inputs`, `goodMass_lower`, and the assembled
attempt bound.

## W46. Discharged paper endpoint

File `Cogentic/RandomizedPaperEndpointDischarged.lean`. Define
`DischargedPaperEndpointInputs` that replaces the L18.4 leaf by
`L18_4Inputs`, the L19.4–L19.6 leaves by `L19Inputs`, the C5 `hitMass` bridge by
the W45 certificate, and the C5.d/e stages by the W31/W32 certificates, while
keeping the remaining paper leaves explicit. Prove
`PaperEndpointInputs` from it and compose with
`RandomizedPaperEndpoint.serialized_assembled_balancedEnvelopeInfimum_from_paperAssumptions`.

This is the capstone: the endpoint should no longer mention the replaced
opaque fields. The remaining paper leaves are the ones not yet reduced.
