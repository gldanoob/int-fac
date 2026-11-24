# Deterministic integer factoring

This repository investigates algorithms that return the smallest prime factor of every integer $N\ge2$. For a $b$-bit input, the benchmark is $2^{O(b/\sqrt{\log b})}$ deterministic bit operations. The reports give partial algorithms, counterexamples and open proof obligations. A better all-input bound remains open here. [Leaderboard](https://bigospeedrun.com/integer-factoring) · [Upstream factoring project](https://github.com/1337isnot1337/integer-factoring)

## Research

Start with the [known-results index](research/known-results.md), including the [discussion board leads](research/known-results.md#discussion-board-leads-checked-on-november-24), and the [order-oracle and CRT reductions](research/order-and-crt-reductions.md). Before deriving a lemma or running a new sweep, check the published theorem and the latest upstream correction for that question. Record the exact input, assumptions, guarantee and source next to any remaining gap.

| Report | Starting points |
| --- | --- |
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

The check uses the installed elan stable binary when available and otherwise uses Lean on the search path. To use a specific Lean executable, pass its path as the make variable `LEAN`. The [formal proofs](formal/) establish the finite tape-cover, raw clique-cost and order-query counting statements, together with existence and uniqueness of primitive-form certificates. The [PARI/GP experiments](experiments/) check the finite examples and sweeps. Each report includes commands for running its checks individually.
