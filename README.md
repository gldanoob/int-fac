# Deterministic integer factoring

This repository investigates algorithms that return the smallest prime factor of every integer $N\ge2$. For a $b$-bit input, the benchmark is $2^{O(b/\sqrt{\log b})}$ deterministic bit operations. The reports give partial algorithms, counterexamples and open proof obligations. A better all-input bound remains open here. [Leaderboard](https://bigospeedrun.com/integer-factoring) · [Upstream factoring project](https://github.com/1337isnot1337/integer-factoring)

## Research

| Report | Starting points |
| --- | --- |
| [Class-group walks and finite tape covers](research/class-group-walks.md) | Lenstra–Pomerance derandomization, smooth relations, and equal-square witnesses |
| [First parallel search](research/round-1.md) | Discrete logs and multiplicative orders, divisor moments, and the clique evaluator |
| [Second parallel search](research/round-2.md) | Elliptic-curve splits, coefficient rank, bounded products, and order searches |
| [Applications of upstream lemmas](research/round-2.md#further-tests-against-upstream-results) | Deep roots, normalized coefficients, and deterministic probes on two archived cycles |

The [open computations](research/round-2.md#open-computations) identify the outstanding algorithmic steps and the hypotheses each would need.

## Reproduce the results

Run from the repository root with Lean 4 and PARI/GP installed. The checked versions are Lean 4.36.0 and PARI/GP 2.19.1 (development build).

~~~sh
make check
~~~

The check uses the installed elan stable binary when available and otherwise uses Lean on the search path. To use a specific Lean executable, pass its path as the make variable `LEAN`. The [formal proofs](formal/) establish the finite tape-cover and raw clique-cost statements. The [PARI/GP experiments](experiments/) check the finite examples and sweeps. Each report includes commands for running its checks individually.
