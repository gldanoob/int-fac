# Optimizing the variable-multiple factoring schedule

The infimum of the randomized cost ledger is $2(8/3)^{2/3}=3.845998854153089\ldots$. A strict rational schedule has leading coefficient $3.8459988542$, with the sieve term strictly larger than the other two terms. This calculation uses the moment and extractor hypotheses of the variable-multiple construction. [Variable-multiple lattice and moment estimates](cogentic-variable-multiple-lattice.md)

## The strict constraints and three costs

Keep $H=(\log N)^{1/3}(\log\log N)^{2/3}$, $S=xc+1/x$, $\log A\sim cH$ and $\log B\sim bH$. The parameters are positive and obey
\[
 c>2b,\qquad c>b+\frac{S}{3b},\qquad s>2c+2b.
\]
The first gives a strict margin for the weighted cell estimate with $Q\le B^2$. The second makes the diagonal Gram error exponentially small on the $H$ scale. The third makes $W/(Q(2A)^2m\operatorname{poly}(d))$ exponentially large for the two-mark lattice Gaussian. It leaves $S$ unchanged because $\log(W/m)\sim sH=o(V)$.

The coefficient of $H$ in the time bound is
\[
 \kappa(x,b,c)=\max\left(2c,\ 4b,\ 2c+2b-\frac{2S}{3b}\right).
\]
For the sieve, each root of either field modulo $p$ gives one residue class of numerators at each eligible denominator. There are at most $d$ roots per prime and field. Across at most $A$ denominators, their streams have length $O(d(A^2\sum_{p\le B}1/p+AB))$, with a polynomial factor in $\log N$ for the interval lists. Computing the roots and sorting the streams costs $(A^2+AB+B^2)\exp(o(H))$. The inequality $c>2b$ makes the leading term $A^2$.

The exact lifting and dense adjugate updates cost $B^{4+o(1)}$. With $M$ retained columns, the modular pivot scans, nullspace lifts and archimedean processing cost $MB^{2+o(1)}$. The two field samples are independent, so the stated one-mark smoothness estimate yields $\mathbf E M\le\exp((2c-2S/(3b)+o(1))H)$. Multiplying by the per-column cost gives the third coefficient. The Gaussian sampling and integer setup use polynomial-bit data, and the extraction proof charges independent retries at constant expected multiplicative cost. [Projective sieve ledger](cogentic-homogeneous-marks.md) · [Exact extraction and retries](cogentic-randomized-relation-time.md#bit-cost-of-one-extraction)

For a strict target coefficient $\kappa_*$, the three entries are below it precisely when $c<\kappa_*/2$, $b<\kappa_*/4$ and $S>3b(c+b-\kappa_*/2)$. Feasibility imposes the separate upper bound $S<3b(c-b)$.

## Exact infimum

The strict conditions imply
\[
 2\sqrt c\le xc+\frac1x=S<3b(c-b)<\frac{3c^2}{4}.
\]
The first inequality is arithmetic–geometric mean. The last follows from $b(c-b)=c^2/4-(b-c/2)^2$ and $b<c/2$. Consequently every feasible schedule has $c>c_0=(8/3)^{2/3}$ and every displayed cost bound has $\kappa\ge2c>2c_0$.

For any rational $c>c_0$, first set $x_*=1/\sqrt c$, $S_*=2\sqrt c$ and $b_*=\sqrt{S_*/3}$. Then $S_*/(3b_*)=b_*$ and $2b_*<c$. Decrease $b_*$ slightly while keeping $x_*$ fixed. By continuity the strict feasibility conditions on $b,c$ persist, and now $S_*>3b^2$. The latter makes the third cost term strictly less than $2c$. These are all open conditions, so nearby rational $x,b$ satisfy them. Choose a rational $s>2c+2b$. Both subsidiary cost terms are strictly below $2c$, and the ledger attains $2c$ for that $c$. Taking rational $c$ down to $c_0$ proves that the infimum is $2c_0$, whose cube is $512/9$.

## A rational schedule with explicit margins

Use the following terminating decimals as exact rationals.

| Parameter | Value |
| --- | ---: |
| $x$ | $0.7211248$ |
| $b$ | $0.9614997$ |
| $c$ | $1.9229994271$ |
| $s$ | $6$ |

The cell gap $c-2b$ is exactly $2.71\times10^{-8}$. The diagonal gap $c-b-S/(3b)$ exceeds $1.75\times10^{-11}$, and the Gaussian width gap $s-2c-2b$ exceeds $0.23$. The three cost coefficients are $3.8459988542$, $3.8459988$ and a rational in $(3.84599880003,3.84599880004)$, respectively. In particular all three are strictly below $3.84599885421$. The largest coefficient is less than $5\times10^{-11}$ above the algebraic infimum. [Exact rational checks](../experiments/cogentic-variable-multiple-costs.py)
