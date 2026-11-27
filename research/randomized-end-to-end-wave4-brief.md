# Randomized factoring end-to-end: wave 4

Base: `explore/randomized-one-third` at `0f3799f`. Read
`research/randomized-end-to-end-status.md`, the wave-3 brief, and the files
named in each task.

Wave 4 discharges the smallest remaining explicit fields:

1. L19.4 `PoissonQuotientInputs.E₁_bound`/`E₂_bound` from the existing
   `RandomizedPrimeProductPlancherel` / `RandomizedPrimeGridPrefixEnergy`
   theorems.
2. L19.5 `IdealZeroModeInputs.muq_le` from
   `RandomizedTopStripMoments.primeBinPatternProducts_dividedStrip_ratio_le`.
3. L18.4 `NumeratorCountInputs.mass_lower`/`error_le`.
4. C5 `C5abcInputs.half_mass`.

Same constraints: new file only, no shared edits, no commit, no
`sorry`/`admit`/`axiom`/`native_decide`, `flock /tmp/intfac-lean.lock`,
`LEAN_NUM_THREADS=1`, `PATH="$HOME/.elan/bin:$PATH"`. If a paper estimate cannot
be proved, reduce it to the smallest explicit `Prop` and prove the reduction.

## Tasks

### W21. L19.4 marginal energies

File `Cogentic/RandomizedL19Energy.lean`.

Define the marginal energies used by `PoissonQuotientInputs` (the Mellin
residue energy and the sharp-prefix energy) from
`primeBinProducts_mellin_energy_from_critical_line` and
`primeBinProducts_gridPrefix_from_critical_line`. Prove the `E₁_bound`/`E₂_bound`
shape `E_i ≤ exp(c_i * scale n) * exp(-η_i * W n)` under explicit scale
identifications, or reduce to the smallest explicit `EnergyScaleInputs`. Do not
set the energies to zero.

### W22. L19.5 divided-strip ratio

File `Cogentic/RandomizedL19Muq.lean`.

Instantiate `mu`/`muq` with `stripDensity S X` and
`stripDensity (dividedStrip S q) (X/q)`. Use
`primeBinPatternProducts_dividedStrip_ratio_le` to prove
`muq n ≤ exp(cq * scale n) * mu n` for a suitable `cq`, with the arithmetic
`(d * log y)/c ≤ exp(cq * scale n)` proved. Leave only the explicit population
and scale hypotheses.

### W23. L18.4 numerator mass/error

File `Cogentic/RandomizedL18_4Mass.lean`.

Prove `NumeratorCountInputs.mass_lower` and `error_le` from the actual pool and
the existing `PrimePatternProgressionBound`, or reduce them to the smallest
explicit counting lemmas. `mass_lower` is `V ρ ≤ #pool`; `error_le` is the RH
progression deviation at most half the reference count. Do not set the pool or
error to zero.

### W24. C5 H.8 half-mass

File `Cogentic/RandomizedC5HalfMass.lean`.

Prove `C5abcInputs.half_mass` from the existing C5.a/H.8 counting machinery
(`RandomizedEpochPool`, `RandomizedFieldPoolDescent`, `RandomizedEpochSuccess`,
`RandomizedConcreteHitMassCount`), or reduce it to the smallest explicit
counting `Prop`. The target is

  `1/2 ≤ pmfProb D.ideal (immediateFactor ∨ acceptedDense)`.

If the exact events are not defined concretely, define a local structure and
prove the counting reduction. Do not set the probability to 1 by fiat.

## Definition of done

Compile, no `sorry`/`axiom`, `[propext, Classical.choice, Quot.sound]`, and a
report with exact signatures and remaining hypotheses.
