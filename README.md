# Deterministic integer factoring

This repository investigates algorithms that return the smallest prime factor of every integer $N\ge2$. For a $b$-bit input, the benchmark is $2^{O(b/\sqrt{\log b})}$ deterministic bit operations. The reports give partial algorithms, counterexamples and open proof obligations. A better all-input bound remains open here. [Leaderboard](https://bigospeedrun.com/integer-factoring) · [Upstream factoring project](https://github.com/1337isnot1337/integer-factoring)

## Research

The [November 25 continuation](research/2026-11-25-continuation.md) records results obtained after the morning work.

The [November 25 morning handoff](research/2026-11-25-handoff/README.md) collects the average-time reductions, the exact height-five counterexample, the complete height-six search data and the remaining proof obligations.

Start with the [known-results index](research/known-results.md), including the [discussion board leads](research/known-results.md#discussion-board-leads-checked-on-november-24), and the [order-oracle and CRT reductions](research/order-and-crt-reductions.md). Before deriving a lemma or running a new sweep, check the published theorem and the latest upstream correction for that question. Record the exact input, assumptions, guarantee and source next to any remaining gap.

| Report | Starting points |
| --- | --- |
| [An unpadded magnitude threshold](research/unpadded-magnitude-threshold.md) | Complete factoring from threshold-one bits at the original modulus, in expected polynomial time for all inputs and deterministic polynomial time for limited prime support |
| [A fixed Kloosterman threshold](research/kloosterman-threshold.md) | Complete factoring from nonadaptive gap-comparison bits at one square modulus, with sublinear padding in the input bit length |
| [Divisor sums on powers of the input](research/divisor-sums-on-powers.md) | Exact totient from leading bits of one $\sigma(N^j)$, and complete factoring from a short block of ordinary divisor sums without analytic input |
| [Factoring from simultaneous divisibilities](research/hidden-divisor-lattices.md) | Unconditional recovery from bounded cubic multiples on balanced inputs, large prime powers from one divisor sum, and complete factoring from ordinary divisor sums on powers of the input |
| [One divisor sum for general inputs](research/single-divisor-sum.md) | Complete deterministic factoring from a supplied divisor sum in $\exp(O(b^{1/3}(\log b)^{2/3}))$ time under a uniform Dedekind zero-free strip, and polynomial time for bounded prime support |
| [Cyclotomic multiples computed from the input](research/cyclotomic-supply.md) | An infinite family covered by $N^2+N+1$, and density-one residual bounds for exponent lists using polynomials and integer square roots of the input |
| [Cyclotomic multiples at any fixed index](research/cyclotomic-order-multiples.md) | A deterministic split from one hidden prime’s cyclotomic multiple, and complete factoring from one divisor sum for bounded prime multiplicities |
| [Quadratic resolvents of cubic probes](research/cubic-resolvent-profiles.md) | Exact degree for one norm field, and which cubic conditions several Galois fields can impose, with height-five minima |
| [Cubic order multiples](research/cubic-order-multiples.md) | A deterministic split from an unfactored multiple of $p^2+p+1$ in specified congruence classes |
| [Known multiples of one hidden prime’s p+1](research/p-plus-one-multiples.md) | Complete factoring of Lucas–Carmichael numbers, one divisor sum on squarefree inputs, and a square-root search for a missing multiplier |
| [Polynomial overhead for three-square queries](research/hurwitz-polynomial-reductions.md) | Complete factoring from quarter-bit counts on small composite twists or the parity of remainders modulo small odd primes on prime twists |
| [Counting square roots in a quarter interval](research/centered-count-complexity.md) | A two-list exact evaluator given the factors, and parity completeness for variable centers |
| [Kloosterman values and signs](research/kloosterman-localization.md) | Factoring from exact signs at the original square modulus in $2^{O(\sqrt b)}$ work and queries, and polynomial time for logarithmically many prime factors |
| [Salié sums and quarter parity](research/salie-and-quarter-parity.md) | Direct centered-bit comparison at the input modulus, a low-frequency sign evaluator and the exact first negative unit frequency for two prime types |
| [Quadratic floor-sum and discrete-log parity](research/floor-sum-and-log-parity.md) | Factoring from one floor-sum bit per bisection step, fixed-length nonadaptive queries for two prime divisors, or canonical discrete-log parities |
| [Parity of clipped counts](research/box-count-parity.md) | A split from one-bit counts in planar disks in the fixed quadrant, three-square boxes, or slices of reduced forms |
| [Low bits of Hurwitz class numbers](research/hurwitz-residues.md#one-large-index-and-quarter-bit-precision-suffice) | All-input reduction to the low bits of a positive three-square count, including repeated prime factors |
| [Twisted represented squares](research/twisted-square-witnesses.md) | Sharp count of inputs covered by small coefficients, roots pooled across multipliers, and a CFRAC failure family |
| [Prime-form powers and second witnesses](research/prime-power-witnesses.md) | A guaranteed large leading coefficient, a short witness and the gcd detected by each secant |
| [Represented squares and their height](research/represented-square-height.md) | A 120-input experiment and an infinite family missed by the bounded first-square search |
| [Factoring from quadratic-order class numbers](research/quadratic-order-reduction.md) | All-input reduction, unknown conductors, and primitive-form counting certificates |
| [Class-group walks and finite tape covers](research/class-group-walks.md) | Lenstra–Pomerance derandomization, smooth relations, and equal-square witnesses |
| [First parallel search](research/round-1.md) | Discrete logs and multiplicative orders, divisor moments, and the clique evaluator |
| [Second parallel search](research/round-2.md) | Elliptic-curve splits, coefficient rank, bounded products, and order searches |
| [Applications of upstream lemmas](research/round-2.md#further-tests-against-upstream-results) | Deep roots, normalized coefficients, and deterministic probes on two archived cycles |
| [Third parallel search](research/round-3.md) | Bounded CRT joins, Lenstra–Pomerance relation lifts, class-number windows, and global order multiples |

## Open problems by topic

| Direction | What the current result still needs |
| --- | --- |
| [Lenstra–Pomerance derandomization](research/round-3.md#why-endpoint-mixing-alone-does-not-derandomize-lenstrapomerance) | An efficient exponent schedule covering useful lifts within a fixed class and parity |
| [Three-square counts](research/hurwitz-polynomial-reductions.md) | A faster evaluator for small-prime residues or for the lowest $\lceil b/4\rceil+1$ bits of the count at the chosen square multiples. |
| [Genus characters](research/quadratic-order-reduction.md#small-split-primes-for-every-negative-order-discriminant) | Small split prime forms cover the two-primary subgroup for every negative order discriminant. The remaining cost is computing their projections. |
| [Class-group relations](research/round-3.md#mixed-relations-can-recover-several-deep-roots-at-once) | A uniform way to find short relations of sufficient rank |
| [Multiplicative orders](research/round-3.md#splitting-from-an-unfactored-global-order-multiple) | An affordable global relation with a small residual exponent |
| [Divisor coefficients](research/round-3.md#two-upstream-field-evaluations-per-level-suffice-for-triprimes) | A fast way to evaluate the supplied character sums on the original composite input |
| [Multiplication networks](research/round-3.md#explicit-crt-joins-remain-large-inside-balanced-operand-boxes) | A symbolic join or cross-subtree pruning rule with a bound on intermediate work |

## Reproduce the results

Run from the repository root with Lean 4 and PARI/GP installed. The checked versions are Lean 4.36.0 and PARI/GP 2.19.1 (development build).

~~~sh
make check
~~~

The check uses the installed elan stable binary when available and otherwise uses Lean on the search path. To use a specific Lean executable, pass its path as the make variable `LEAN`. The [formal proofs](formal/) establish the finite tape-cover, raw clique-cost and order-query counting statements, together with existence and uniqueness of primitive-form certificates, the three conic secant identities, and the clipped three-square shell equivalence. The [PARI/GP experiments](experiments/) check the finite examples and sweeps. Each report includes commands for running its checks individually.
