# Randomized factoring end-to-end: wave 5

Base: `explore/randomized-one-third` at `94a2dee`. Read
`research/randomized-end-to-end-status.md`, the wave-3/4 briefs, and the files
named in each task.

Wave 5 continues the sub-lemma discharge. Same constraints: new file only, no
shared edits, no commit, no `sorry`/`admit`/`axiom`/`native_decide`,
`flock /tmp/intfac-lean.lock`, `LEAN_NUM_THREADS=1`,
`PATH="$HOME/.elan/bin:$PATH"`. If a paper estimate cannot be proved, reduce it
to the smallest explicit `Prop` and prove the reduction. Do not set a loss,
mass, count, or error to zero by fiat.

## W25. L18.4 large-sieve R1/R2

File `Cogentic/RandomizedL18_4LargeSieveInputs.lean`. Prove or reduce
`LargeSieveInputs.multiModulusSum` and `rationalCellPartition` from the existing
Mellin/Plancherel and prefix-energy estimates plus the rational-cell lattice
count. Smallest explicit `Prop` otherwise.

## W26. L18.4 cell data construction

File `Cogentic/RandomizedL18_4CellData.lean`. Construct `CellData` for the
canonical shrunken denominator interval, prove the supply-fit condition
`2 d K0 (1+log3+W)^2 ≤ K`, and resolve the paper's `2V/(3dK)` vs the field's
`V/(2dK(1+W))` factor.

## W27. L18.4 thin-pair aggregate

File `Cogentic/RandomizedL18_4ThinAggregate.lean`. Prove or reduce
`ThinPairInputs.strip_count`, `mark_count`, and `cutoff_in_range` from the
proved determinant-level lattice counts and the rational-good denominator count.

## W28. L19.4 Poisson numerator/denominator

File `Cogentic/RandomizedL19Poisson.lean`. Prove or reduce
`PoissonQuotientInputs.numerator_energy` from
`coupled_mode_cauchy_schwarz`, and `A_bound` from the existing denominator
estimate / `keybreak-mixed-strip-moment.md`. Keep the Poisson identity explicit.

## W29. L19.5 zero mode and residual

File `Cogentic/RandomizedL19ZeroMode.lean`. Prove or reduce
`IdealZeroModeInputs.zero_mode_bound` and `rho_bound` from the existing
ellipse-covering/layer-cake and period-prime estimates.

## W30. L19.6 thin and small-determinant fractions

File `Cogentic/RandomizedL19Thin.lean`. Prove or reduce
`ThinPairInputs.thin_bound` and `smallDet_bound` from the determinant-level
lattice counts and the paper's `O(1/K)`/`V^{-c}` estimates.

## W31. C5.d algebra stage

File `Cogentic/RandomizedC5Algebra.lean`. Decompose the C5.d `StageBudget`
(Chebotarev L34, odd-degree L35, valuation L36, Hensel L37) into explicit
sub-lemmas and prove the `StageBudget` reduction.

## W32. C5.e coupling stage

File `Cogentic/RandomizedC5Coupling.lean`. Decompose the C5.e recognizer coupling
into explicit sub-lemmas and prove the `StageBudget` reduction.

## W33. C4 stages S1/S2

File `Cogentic/RandomizedConcreteStageCostS1S2.lean`. Concrete S1 (field pool)
and S2 (character probes) costs and polynomial bounds, following the S0/S7
pattern.

## W34. C4 stages S4/S6/S9

File `Cogentic/RandomizedConcreteStageCostS469.lean`. Concrete S4 (screening),
S6 (row records), and S9 (final gcd) costs and polynomial bounds, following the
S0/S7 pattern.
