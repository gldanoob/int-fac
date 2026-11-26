# A finite all-prime reference for monic ideal parity

The bounded reference checks the complete joint ideal-parity kernel on fixed primitive grids, including singular primes and primes dividing the power-order index. It uses PARI maximal orders and complete integer norm factorizations. Its small-prime labels and private decisions provide a reference for the [singular-prime algorithm](cogentic-monic-singular-ideals.md). The replay checks the quadratic ramification criterion directly on prescribed examples. It makes no complexity claim for PARI or for computing its maximal orders. [Replay](../experiments/cogentic-all-ideal-reference.py)

## Exact finite collector

For a grid $|a|\le A$, $1\le b\le A$, take every primitive mark with $\gcd(a-bm,N)=1$ and put $Y=2A^2$. For each field and each rational prime $p\le Y$, precompute the prime ideal decomposition in the maximal order. A row label consists of a field number, $p$, and the position of the prime ideal in that precomputed decomposition. In addition, record the contraction root when $\alpha$ has image in $\mathbb F_p$. Distinct prime ideals at singular roots can have the same contraction root, so the precomputed labels retain their different positions.

For a mark $z=a-b\alpha$, compute and completely factor the absolute rational norm. For each rational prime in that factorization, evaluate $v_{\mathfrak p}(z)$ at every prime ideal above it, using the precomputed decompositions below the cutoff. Check that the sum of residue degrees times valuations is the rational norm exponent. Record the odd valuations at $p\le Y$. Above $Y$, keep only whether every valuation in each field is even. An odd valuation at any such prime ideal forces this column to have coefficient zero in every dependency. If the ideal divided another primitive mark, its rational prime would divide the nonzero integer $ab'-a'b$ of absolute value at most $2A^2$. This uses only divisibility in the maximal order and applies to singular ideals as well.

Delete the columns with an odd private valuation and compute the binary kernel in the remaining small-prime rows. The replay also computes the kernel with one independent row per deleted column and checks exact equality of the embedded bases. Every column admitted by the [mark-local collector](cogentic-monic-local-roots.md) must appear in the reference with identical parity after its root labels are translated to maximal-order labels.

## Grid comparisons

Run `python3 -B experiments/cogentic-all-ideal-reference.py`. It uses grid heights at most 32 and gives each PARI reference call a 30-second timeout. Both collectors admit the known dyadic row. The last column counts newly recovered marks that participate in at least one exact ideal-parity dependency.

| Input | Pair | Height | Mark-local columns | Mark-local nullity | Reference columns | Reference nullity | Active recovered marks |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 143 | Raw cubic and quartic | 16 | 73 | 0 | 73 | 0 | 0 |
| 247 | Raw cubic and quartic | 32 | 248 | 1 | 248 | 1 | 0 |
| 323 | Raw cubic and quartic | 16 | 73 | 2 | 73 | 2 | 0 |
| 895 | Raw quadratic and cubic | 20 | 63 | 0 | 151 | 7 | 36 |
| 145 | Repaired quadratic and cubic | 16 | 76 | 0 | 76 | 0 | 0 |
| 67 | Repaired quadratic and cubic | 20 | 129 | 2 | 184 | 27 | 29 |
| 85 | Planted | 16 | 9 | 1 | 9 | 1 | 0 |
| 631 | Planted | 16 | 16 | 1 | 16 | 1 | 0 |
| 15629 | Planted | 16 | 7 | 2 | 7 | 2 | 0 |

The original $247$ subset still contains the known two-mark dependency with sign $-1$, residues $149,111$, and gcd $19$. At $N=895$, the reference has a 15-mark dependency with sign $-1$ and exact square roots in both fields. The derivative-cleared residues are $572$ and $502$ with common square $509$ and difference gcd $5$. The replay verifies the listed support belongs to the reference kernel and recomputes the two roots. One support mark is $(-3,1)$. Its cubic norm is $-225$. The two prime ideals above $5$ that divide this mark have the same contraction root $2$ but each has exponent one, so it takes two distinct rows to record their parity. The mark-local matrix has nullity zero at this height.

## Private residual controls

The replay recomputes the original $\mathbb Q(i)$ example of the [singular-prime note](cogentic-monic-singular-ideals.md), with $q=(11\cdot19^2)^{2^j}$ for $j=0,1,2$ and the mark $(0,1)$ in the power order of $X^2+q^2$. For the quadratic extension defined by its square root, PARI computes the weighted sums $S_E(p)$ and $2S_K(p)$ from the prime decompositions at 11 and 19. The test fails at 11 for $j=0$ and passes at both primes for $j=1,2$, in agreement with direct maximal-order valuations.

The two-field control uses $s=(13\cdot19^2)^t$, $m=3$, and

$$F=X^3+2X^2+2sX+2s^2,\qquad G=F+(X-3)X^3.$$

Take $A=2$, so $Y=8$ and both 13 and 19 are private. The mark $(0,1)$ has norm $2s^2$ in each field. At each private prime there are two degree-one branches above the contracted root zero. Their individual valuations are $t,t$ at 13 and $2t,2t$ at 19. In fact substitution $X=sZ$ followed by division by $s^2$ gives the reduction $2(Z^2+Z+1)$ at both primes, with two distinct nonzero roots, so Hensel's lemma yields the two branches. PARI independently verifies these exponents and the quadratic weighted sums. At $t=1$, the sum upstairs at 13 is smaller than the doubled base sum by two in both fields, while equality holds at 19. At $t=2$, equality holds at both primes and the exact reference admits the mark. The mark-local collector rejects both controls because the square tail shares a factor with the homogenized derivative.

These controls compare exact individual valuations with the pointwise ramification criterion at named primes. They leave the composite tame-overorder and Smith-invariant implementation outside the replay.
