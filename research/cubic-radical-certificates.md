# Exact cubic character dependencies in coefficient boxes

The height-six handoff determined dependencies between cubic fields by explicit field inclusions. A single calculation now certifies those dependencies for any finite family of rational irreducible cubics. Through height 20 it finds 380 independent relations among 13,845 fields. Within a fixed quadratic resolvent it recovers the entire ternary space, including the individual coordinates needed to count irreducibility patterns. The Galois-theoretic ingredients are classical. The results here are the reproducible certificates, larger-box computations and optimization over quadratic profiles. [Earlier height-six proof](2026-11-25-handoff/height-six/proof.md) · [Cohen and Morra on cubic fields with fixed quadratic resolvent](https://arxiv.org/abs/1003.1869)

## Two complementary certificates

For a monic cubic $f=x^3+a x^2+b x+c$, write $P=a^2-3b$, $Q=2a^3-9ab+27c$ and $\Delta=\operatorname{disc}(f)$. If $D$ is the fundamental discriminant of its resolvent, with $D=1$ in the cyclic case, set $e=\operatorname{core}(-3D)$ and $E=\mathbb Q(\sqrt e)$. Here core removes square factors. The identity $Q^2-4P^3=-27\Delta$ puts a nonzero choice
$$
 z=(-Q\pm\sqrt{-27\Delta})/2
$$
in $E$. If $P\ne0$, the other choice is $P^3/z$. The root formula $3x+a=\alpha+P/\alpha$, $\alpha^3=z$, shows that over $L=E(\zeta_3)$ the splitting field is $L(\sqrt[3]{z})$. Indeed $L$ already contains the square root of the discriminant, and irreducibility persists under the extension from $\mathbb Q$ to the two-power-degree field $L$ because a cubic root generates a degree-three subfield. The displayed formula then identifies two cubic extensions. The norm map shows $E^\times/E^{\times3}\to L^\times/L^{\times3}$ is injective because $[L:E]$ is prime to three. Kummer theory identifies the degree of the joint splitting field over $L$ with $3^{\dim\langle z_i\rangle}$. Enlarging the quadratic resolvent to $L$ preserves its cubic kernel. [Cardano's formula and Kummer theory for cubics](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/1AAF4F4C89D37E5D1D5B5400CAE24ED8/S0008414X00005186a.pdf)

1. At good primes $l\equiv1\bmod3$ splitting in $E$, choose one root of $e$ and compute each $z_i^{(l-1)/3}$ in the residue field. Express these roots of unity as exponents in $\mathbb F_3$. Independent rows certify a lower bound for the dimension. The replay independently counts all modular roots of every cubic at each retained row.
2. For each basis vector $v$ of the nullspace of the current residue matrix, compute $\prod_i z_i^{v_i}$ exactly in $E$. Obtain a cube root with PARI and verify its cube equals the product. The rational mirror uses ordinary rational cube roots. If every vector passes, the row space gives the full cubic kernel, including its coordinate maps. Otherwise continue with another independent prime.

Each true multiplicative relation is invisible to every residue row. Conversely Chebotarev over $L$ supplies every cubic character via primes splitting in $L$ over the rationals, up to the simultaneous sign of a row. Changing the chosen square root in a nontrivial mirror inverts all classes since $z_i\overline z_i=P_i^3$. The zero-$P_i$ case has rational mirror and uses its nonzero radical. Thus the calculation terminates. No bound for the smallest witness prime is needed. Distinct nontrivial resolvents act through distinct sign characters on their cubic kernels. Projection onto the eigenspaces over $\mathbb F_3$ makes the blocks independent after fixing the quadratic data. The cyclic block is the trivial eigenspace and may be fixed by rational congruences. [Independent eigenspaces and Frobenius distributions](2026-11-25-handoff/height-six/proof.md)

| Monic coefficient height | Cubic fields | Resolvent blocks including cyclic | Cyclic rank | Total ternary rank | Relations | Largest witness prime |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 6 | 369 | 330 | 4 | 360 | 9 | 139 |
| 7 | 584 | 530 | 5 | 573 | 11 | 139 |
| 8 | 848 | 769 | 7 | 831 | 17 | 157 |
| 9 | 1,175 | 1,047 | 7 | 1,142 | 33 | 157 |
| 10 | 1,644 | 1,478 | 9 | 1,598 | 46 | 193 |
| 11 | 2,230 | 2,016 | 10 | 2,171 | 59 | 229 |
| 12 | 2,877 | 2,546 | 10 | 2,782 | 95 | 229 |
| 14 | 4,687 | 4,193 | 14 | 4,553 | 134 | 277 |
| 20 | 13,845 | 12,363 | 20 | 13,465 | 380 | 457 |

## Largest collision probability

Fix the quadratic signs and cyclic characters, and take two primes independently in a dyadic interval with the given character values. Send the prime range to infinity at fixed height. An inactive resolvent gives the same bit at both primes. For an active block with row matrix $R$, enumerate its $3^r$ row combinations. If $n_w$ combinations have the same zero-versus-nonzero mask $w$, the collision probability in the block is $C_D=\sum_w n_w^2/9^r$. For a full-rank block with $m$ fields this simplifies to $(5/9)^m$. The total probability is the product over the active blocks. Cauchy–Schwarz on two mask distributions bounds the collision probability for distinct fixed profiles by the larger self-collision optimum.

The replay eliminates quadratic character variables from the exact product by maximizing integer numerators over each binary choice. Backtracking gives an attaining profile and rechecks its original product. These are the negative base-two logarithms of the largest probabilities, rounded after the exact rational calculation.

| Height | $p\equiv1\pmod3$ | $p\equiv2\pmod3$ |
| ---: | ---: | ---: |
| 6 | 56.73037520 | 59.35978346 |
| 7 | 91.20664481 | 98.36764116 |
| 8 | 139.81419759 | 157.72742462 |
| 9 | 194.05918585 | 224.42757668 |
| 10 | 261.94608427 | 334.37557097 |

One can also require splitting in a multiquadratic base whose squareclasses span a binary space $U$ of dimension at most $d$, and impose abelian Artin conditions over that base. Every represented $D\in U$ splits and its cubic coordinates can be fixed. Every $D\notin U$ retains its full cubic kernel. Indeed an element fixing the base inverts that block, and its commutators with the individual cubic kernel give the whole block while fixing every abelian prescription. For each $U$ maximize the product above subject to a positive sign at its represented classes, omitting their factors. Every feasible quadratic profile and fixed covered cubic pattern can attain the stated remaining distribution, for example by prescribing the covered cubic identities. This statement concerns prime samples from the Artin and congruence conditions. Distributions of primes among the values of a particular norm polynomial would require additional results. [Norm fields and the commutator argument](cubic-resolvent-profiles.md)

It suffices to enumerate spans generated by represented classes since taking the span of the represented part drops only extra base constraints. For each span, dividing the unconditioned optimum by the product of all covered $C_D$ bounds its possible gain. Branch-and-bound uses rigorous integer upper bounds for base-two logarithms and tests the exact rational upper bound before reoptimizing signs. On the height-six $p\equiv1$ branch the optima over **all** profiles at base dimensions one through four agree with the earlier single-profile results. One sequence of attaining basis discriminants is $-3,-19,-228,-152$, taken in that order. Solving $m(m-1)P/2\ge1$ and rounding up gives respectively 51,192,666, 11,037,550, 2,539,169 and 584,132 samples for one expected unordered colliding pair. This calculation does not exhibit a colliding pair. [Archived one-profile enumeration](2026-11-25-handoff/height-six/norm-bases.txt)

Run `python3 -B experiments/cubic-radical-profile.py 6` for both exact height-six probabilities, also checked against the independent archives. A second argument sets the maximum base dimension. For just the ranks, from the repository root start `gp -fq`, then enter `read("experiments/cubic-radical-ranks.gp")` and `cubicRadicalBox(20)`. The last entry lists each deficient block and its dimensions. [Exact field arithmetic](../experiments/cubic-radical-ranks.gp) · [Profile and base optimization](../experiments/cubic-radical-profile.py)
