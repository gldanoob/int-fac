# Exact norm squareclasses on centered quadratic grids

The signed rational norm kernel of a centered quadratic grid can be computed by stripping only bounded primes. A large prime common to two distinct primitive marks forces the marks to be conjugate, so their integer norms and stripped residuals coincide. Grouping equal nonsquare residuals therefore computes the first squareclass kernel exactly. [Implementation and benchmark](../experiments/cogentic-quadratic-grid-norms.py) · [Quadratic square descent](cogentic-quadratic-square-kernel.md)

## The prime cutoff

Let the polynomial be $P=X^2+uX+v$ and a primitive mark $(a,b)$ satisfy $|a|\le H$ and $1\le b\le H$. Its norm is $a^2+uab+vb^2$. A prime $p$ dividing the norm has $p\nmid b$ by monicity and primitivity, so $a/b$ is a root of $P$ over $\mathbf F_p$.

Suppose $p>(2+|u|)H^2$ divides the norms of two marks $(a,b)$ and $(c,d)$. If their roots coincide, $p$ divides $ad-cb$, whose absolute value is at most $2H^2$. This forces equality of the rational slopes and hence of the primitive marks with positive denominator. If the roots differ, their sum is $-u$. Consequently $p$ divides $ad+cb+ubd$, whose absolute value is at most $(2+|u|)H^2$, and this expression must vanish. The rational slope of $(c,d)$ equals that of $(-a-ub,b)$. The latter mark is also primitive with positive denominator, so $(c,d)$ is exactly that conjugate. Substitution shows their signed integer norms coincide. The bound applies even though the conjugation of an arbitrary mark can leave the box.

The cutoff accounts for the linear coefficient. At height 3 with $P=X^2-2X+66$, the marks $(-3,2)$ and $(1,3)$ have norms $285$ and $589$. After removing primes through $2H^2=18$, their tails are 19 and 589. These tails overlap at 19 despite the distinct norms. The cutoff $(2+|u|)H^2=36$ covers that overlap.

## Exact rational parity

For each nonzero integer norm, retain its sign and the parity of its valuations at primes through $(2+|u|)H^2$. Reuse the result for repeated integer norms. After division, any two distinct residuals above one are coprime unless they are equal, by the cutoff proof. Assign a row to each distinct nonsquare residual and omit square residuals. A nonsquare residual contains an odd prime exponent, and every other residual and every retained bounded prime row has zero exponent at that large prime. Its row therefore represents an independent rational squareclass. This proves equivalence to the full rational squareclass matrix without factoring the residual. The optional signed field relation has a final column for the element $-1$, whose quadratic norm is $+1$ and whose norm column is zero.

The implementation trial-divides one copy of each distinct norm through the cutoff and uses exact square tests. For $u\in\{0,-1,-2\}$ it uses at most $O(H^4)$ small-prime probes, each with bit work polynomial in the norm length, followed by the same packed binary elimination as the gcd-free baseline. The division loop can stop as soon as the next prime exceeds the square root of the residual, in which case any surviving residue is prime. The proof also shows exactly why one can group residuals by equality on the grid and why the grouped row is rational rather than an individual prime-ideal label.

## First-stage comparison

Run `python experiments/cogentic-quadratic-grid-norms.py` to compare the scheduled centered fields on the ten frozen public inputs at heights 12 and 24. The comparison uses the same primitive modular unit marks in both paths. It checks the complete ordered basis masks, including the norm-one column, for both fields of every input. It also checks signed norms, slope $-2$, a shared large nonsquare residual, and a large square residual. The reference computes the same integer norms directly and applies the existing gcd-free squareclass routine. The table sums both fields and all ten inputs at each height. [Frozen inputs](cogentic-monic-blind-grid.md) · [Centered field construction](../experiments/cogentic-selected-polynomial-recenter.py)

| Height | Unit marks per input | Summed norm rank | Gcd-free seconds | Bounded seconds | Speedup |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 12 | 183 | 2,067 | 0.223738 | 0.011800 | 18.96× |
| 24 | 719 | 7,881 | 6.374174 | 0.083075 | 76.73× |

## Second-stage bottleneck

The norm kernel is only the first condition for a field square. For each norm-kernel mask the next stage forms the field product $\beta$ and uses the rational descent scalar $\operatorname{Tr}(\beta)+2t$ with $t^2=N(\beta)$. These are scalars of products, so the primitive-box determinant argument does not apply to their common divisors. The second gcd-free pass on the scalars and the discriminant still computes the field square kernel.

At height 24 on the first frozen input, 341,854,927, the quadratic fields of slopes 0 and $-1$ had signed norm nullities 366 and 270, and exact square nullities 9 and 0. Their combined first-stage time was about 0.008 seconds. Forming the descent products took 0.018 seconds and the second gcd-free reduction took 0.368 seconds. The first-stage speedup therefore leaves a larger cost in the complete field-square decision on this input.
