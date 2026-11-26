# Deterministic integer factoring

This repository investigates algorithms that return the smallest prime factor of every integer $N\ge2$. For a $b$-bit input, the public kernel-checked leaderboard bound is $2^{O(b/\sqrt{\log b})}$ deterministic bit operations. A November 25 Cogentic manuscript claims the stronger deterministic worst-case bound $2^{O(b^{3/4})}$. Its companion claims complete factorization in per-input expected time $L_N[1/3,105]$ using random bits. Both authors' release statements announce Lean proof sources separately. [Pinned manuscripts, models and verification status](research/cogentic-factoring-papers.md) · [Leaderboard](https://bigospeedrun.com/integer-factoring) · [Upstream factoring project](https://github.com/1337isnot1337/integer-factoring)

The randomized branch gives a manuscript-level expected-time coefficient of 2.620741394… at the one-third scale, using averaged projective residues and exact transposed extraction under the local moment hypotheses. Earlier versions give 3.845998854… with entrywise bounds and 2.935046443… with the original trace analysis. KeyBreak states 2.97 under Dirichlet GRH. [Source comparison and checks](research/keybreak-randomized-factoring.md) · [Averaged trace proof](research/cogentic-averaged-projective-trace.md)

Lean checks a deterministic factoring algorithm with worst-case bit cost $L_N[2/3,O(1)]$ in a combined build with the readable Dirichlet GRH proof. The local splitter constructs a bounded list of generators, runs modular powering and GCDs, and returns a verified divisor. Lean accounts for constructing the list and running the splitter. One fixed algorithm returns all prime factors with multiplicity for every $N\ge2$. For each sufficiently large input that reaches the search, the proof finds a successful coefficient tuple for every dyadic target and bounds the bit cost of the same recursion that emits the factors. The concrete implementation enumerates minors. The paper’s smaller leading coefficient of $400000$ uses its polynomial-time extraction routine. [Parameter-free Lean endpoint](formal/cogentic/CogenticWithGRH.lean) · [Verification and reproduction](research/cogentic-worst-case-verification.md) · [Derivation](research/cogentic-deterministic-two-thirds.md)


## Research

A separate deterministic construction now gives $L_X[1/3,O(1)]$ arithmetic mean time on $X<N\le2X$, including every exceptional input. Its fast path covers all but $\exp(O(b^{2/3}(\log b)^{1/3}))$ of the $b$-bit inputs and retains the original bit string across recursive splits. A reusable small list can also be prepared uniformly for worst-case batches. [Sampling proof, preprocessing and finite checks](research/cogentic-universal-score-sampler.md)

The earlier elliptic algorithm for integers $X<N\le2X$ completely factors $N$ in arithmetic mean time $\exp((1+o(1))\sqrt{\ln X\,\ln\ln X})$. This paper bound includes exceptional inputs and the full recursion. Alpöge’s proved ordinary RH supplies the needed prime estimate. His Dirichlet GRH theorem supplies pointwise character witnesses. Sutherland independently verified both statements, including all Dirichlet characters and moduli. Older classical estimates alone give a mean of $\exp(O(b^{2/3}\log\log b/(\log b)^{2/3}))$. [Sharp mean-time proof and checks](research/sharp-elliptic-mean.md) · [Kernel verification of the zeta statements](https://math.mit.edu/~drew/grh/) · [Classical mean proof](research/smooth-integer-slot-hasse.md)

For every fixed prime $p$, the square-root exponent in $\log p$ holds when averaging splits of $pm$ over partner intervals starting at $p^3$ or higher whose length equals their starting point. The same scale covers complete inputs sharing a hidden divisor whose prime factors are at most the cube root of the partner scale. Working over quadratic extensions lowers the cubic threshold to a square for all but a subexponential number of primes per dyadic interval. In the unrestricted worst-case search, the Euclidean tensor-price theorem rules out the proposed exact antipodal crossing improvement in every fixed number of axes. [November 25 continuation](research/2026-11-25-continuation.md) · [Individual-prime proof](research/three-parameter-genus-two.md) · [Common divisors](research/common-divisor-partners.md) · [Quadratic extension and replay](research/quadratic-elliptic-partners.md) · [All-axis inequality](research/multiaxis-crossing-barrier.md)

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

Run from the repository root with elan, Lake and PARI/GP installed. The factoring project pins Lean 4.33.1 and Mathlib. The other standalone checks use Lean 4.36.0 and PARI/GP 2.19.1 (development build).

~~~sh
make check
~~~

The standalone checks use the installed elan stable binary when available and otherwise use Lean on the search path. Run `make check-two-thirds-lean` for the pinned factoring project alone. To use a specific Lean executable, pass its path as the make variable `LEAN`. The [formal proofs](formal/) establish the finite tape-cover, raw clique-cost and order-query counting statements, together with existence and uniqueness of primitive-form certificates, the three conic secant identities, and the clipped three-square shell equivalence. The [PARI/GP experiments](experiments/) check the finite examples and sweeps. Each report includes commands for running its checks individually.

With the pinned GRH artifacts installed, `make check-two-thirds-cached-grh` compiles the parameter-free factoring theorem and prints its axioms. [Cache setup](research/cogentic-worst-case-verification.md#reproduction-and-scope)

Run `make check-two-thirds-short-grh` to build the same parameter-free theorem with the 803-module readable GRH proof on Lean 4.35.0. This target needs elan, Git, Python 3.11 or newer, curl and `patch`. It fetches the pinned sources and caches, then builds `Cogentic.binary_factorization_two_thirds` and checks its axioms. [Combined build](research/cogentic-worst-case-verification.md#combined-build-with-the-readable-grh-proof)
