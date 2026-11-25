# Recovering a prime from simultaneous divisibilities

Let $N$ have $b$ bits. There are three unconditional deterministic polynomial-time consequences of the same univariate lattice construction.

- From one multiple $M$ of $\Phi_k(p)$ for an unknown prime divisor $p$, recover $p$ when $p\ge\sqrt N/b^C$ and $M\le N^{\varphi(k)} b^C$, for fixed $k\ge2$ and $C$. In particular a multiple of $p^2+p+1$ up to $N^2 b^C$ suffices for balanced semiprimes. The public inputs may share prime factors. The [cyclotomic field search](cyclotomic-order-multiples.md) covers arbitrary positive multiples under its stated zero-free strip.
- From the single integer $\sigma(N)$, recover every full prime power $p^e\parallel N$ of size at least $\sqrt N/b^C$, for fixed $C$. A remaining cofactor may contain arbitrarily many distinct primes. The [single-value report](single-divisor-sum.md) gives bounds for other multiplicity patterns.
- The list of ordinary divisor sums $\sigma(N^j)$ for $1\le j\le3b$ suffices for **complete factorization of every $N$**. The query powers are fixed before seeing any answers. Each queried integer and each answer has $O(b^2)$ bits. This gives a deterministic polynomial-time oracle reduction. Computing the answers from $N$ is an additional cost.

## A lattice for overlapping public moduli

Let $f_i\in\mathbb Z[X]$ be monic of positive degree $d_i$, and let $M_i\ge2$ and $1\le A_i\le M_i$ be supplied integers. Seek an integer $w$ such that, for each $i$, some $D_i\ge A_i$ divides both $M_i$ and $f_i(w)$. Assume these **hidden** divisors can be chosen pairwise coprime. The $M_i$ may overlap or even coincide. On any interval $[c-R,c+R]$, the procedure lists candidates containing every qualifying $w$ if

$$
1\le R\le\tfrac18\exp\!\left(\sum_i\frac{(\log A_i)^2}{d_i\log M_i}\right).
$$

All logarithms in this bound are natural. Runtime is polynomial in the number of constraints, dense input sizes and binary lengths. The applications below verify each proposed prime by primality testing and division.

Translate $f_i$ by $c$ so the target has $|w-c|\le R$. Write $a_i=\log A_i$, $b_i=\log M_i$. Set $m=2+2\sum_i\lceil\log_2 M_i\rceil$ and put $t_i=\lfloor m a_i/(d_i b_i)\rfloor$. Integer comparisons $M_i^{d_i t}\le A_i^m$ compute $t_i$ exactly. Form the full-rank lattice in the $m$ coefficients of degree less than $m$ with the following local basis, one polynomial for every $0\le j<m$.

$$
s=\min(t_i,\lfloor j/d_i\rfloor),\qquad M_i^{t_i-s} f_i(c+X)^sX^{j-d_i s}.
$$

Every evaluation at $w-c$ is divisible by $D_i^{t_i}$. The leading coefficients give a triangular basis with index $M_i^{d_i t_i(t_i+1)/2}$, since $d_i t_i\le m$. Intersect the local lattices. The quotient by their intersection embeds into the product of the local quotients, so the index of the intersection is at most the product of the indices. An integral kernel of the block matrix $[U,-V]$, projected through its first block and $U$, computes the intersection of two column lattices. Hermite normal form keeps the intermediate bases at polynomial bit size since their indices have polynomial bit length. [Kannan–Bachem, polynomial-time integer normal forms](https://doi.org/10.1137/0208040)

Scale coefficient $j$ by $R^j$, multiplying the determinant by $R^{m(m-1)/2}$. LLL supplies a nonzero polynomial whose absolute evaluation at any $|X|\le R$ is at most $\sqrt m\,2^{(m-1)/4}$ times the $m$th root of the scaled determinant. To see the rounding cost, put $z_i=m a_i/(d_i b_i)$. Since $(t_i-z_i)^2+t_i\le2z_i$,

$$
2t_i a_i-\frac{d_i b_i}{m}t_i(t_i+1)\ge \frac{m a_i^2}{d_i b_i}-2a_i.
$$

After dividing the log bound by $(m-1)/2$, the total loss from rounding, LLL and evaluation is at most $2\sum_i a_i/(m-1)+(\log2)/2+(\log m)/(m-1)<\log8$. Thus the absolute evaluation is strictly less than $\prod_i A_i^{t_i}$ in the claimed range. It is divisible by $\prod_i D_i^{t_i}$ by coprimality, so it vanishes in $\mathbb Z$. Deterministic factorization of the short polynomial over $\mathbb Q$ lists its integer roots. Polynomial coefficients, lattice entries and translations have polynomial bit length throughout. [Lenstra–Lenstra–Lovász](https://doi.org/10.1007/BF01457454)

The individual large-gcd construction occurs in Boneh's small-root work. Guruswami, Sahai and Sudan use weighted lattice intersections for CRT list decoding. May and Ritzenhofen treat several monic congruences with known coprime moduli. The index argument above permits overlapping public moduli and distinct lower bounds on coprime hidden divisors. Publication priority for these factoring consequences has not been established. [Boneh, Theorem 4.1](https://core.ac.uk/download/pdf/82341411.pdf) · [Guruswami–Sahai–Sudan, §3.2](https://web.cs.ucla.edu/~sahai/work/web/2000%20Publications/GSS00.pdf) · [May–Ritzenhofen, Theorem 3](https://www.cits.ruhr-uni-bochum.de/imperia/md/content/may/paper/pkc2008.pdf)

## One cyclotomic multiple or one divisor sum

For the first application let $d=\varphi(k)$, and try dyadic bins $P\le p<2P$. Use $(f_1,M_1)=(X,N)$ and $(f_2,M_2)=(\Phi_k,M)$. The divisors $p,\Phi_k(p)$ are coprime since $\Phi_k(0)=1$. Use $A_1=P$, $A_2=(P-1)^d$ from the distances to the complex roots of unity. Discard candidates with a proposed lower bound exceeding its public modulus. For a qualifying bin, write $L=\log N$ and $u=\log P\ge L/2-O_C(\log b)$. The sum in the radius bound is at least

$$
\frac{u^2}{L}+\frac{d(u-O(1))^2}{dL+C\log b}\ge u-O_{k,C}(\log b).
$$

Small $P$ can be handled by trial division. Subdividing the bin into polynomially many intervals of radius $P/b^{O_{k,C}(1)}$ and verifying the returned candidates finds the prime.

For the second application guess $1\le e\le b$ and a dyadic bin $B\le p^e<2B$. Use $f_1=X^e$ at $N$, and $f_2=1+X+\cdots+X^e$ at $M=\sigma(N)$. The true divisors $p^e,\sigma(p^e)$ are coprime and each is at least $B$. Multiplicativity gives $\sigma(p^e)\mid M$ because $e$ is the original valuation. Now $M\le N(1+\log N)$ by the harmonic sum. With $v=\log B\ge L/2-O_C(\log b)$, the sum in the radius bound is at least

$$
\frac{v^2}{e}\left(\frac1L+\frac1{L+\log(1+L)}\right)\ge\frac ve-O_C(\log b).
$$

Polynomially many intervals cover $[B^{1/e},(2B)^{1/e}]$. Integer roots give the endpoints up to one unit. Small intervals may be checked directly. Once a prime is found, division recovers its full valuation. Morain, Renault and Smith prove a related single-divisor-sum result for a large prime on a squarefree input. [Theorem 5.4](https://arxiv.org/pdf/1802.08444v2#page=13)

## Ordinary divisor sums on powers of the original input

Take all $M_j=\sigma(N^j)$, $1\le j\le3b$. Trial-divide $N$ through $b^2$. For each remaining prime $p$ we prove recovery on one of the dyadic bins $P\le p<2P$ and one of the guesses $1\le e\le b$ for $v_p(N)$. All lattice inputs below use the original $N$ and its supplied power sums.

For every prime $b<r\le3b$, take $1\le j_r<r$ congruent to $-e^{-1}\bmod r$. The inverse exists since $r>b\ge e$. At the correct exponent, $r\mid e j_r+1$ gives

$$
D_r=\Phi_r(p)=1+p+\cdots+p^{r-1}\ \mid\ \sigma(p^{e j_r})\ \mid\ M_{j_r}.
$$

The $D_r$ are pairwise coprime. For distinct primes $r,s$ the identity $\gcd(p^r-1,p^s-1)=p-1$ gives $\gcd(\Phi_r(p),\Phi_s(p))=1$ after division by $p-1$. Use the corresponding polynomial $\Phi_r$ of degree $r-1$, and lower bound $A_r=P^{r-1}$. Since $\log M_j\le jL+\log(1+jL)\le2jL$ and $j_r\le r-1$, each term in the radius sum is at least $(\log P)^2/(2L)$.

By the prime number theorem, for all sufficiently large $b$ the interval $(b,3b]$ has at least $b/\log b$ primes. Our bins satisfy $\log P\ge2\log b-\log2$ and $L\le b\log2$. Hence the total radius exponent divided by $\log P$ is at least $(1-o(1))/\log2>1$. For sufficiently large $b$, the guaranteed radius exceeds $P$. A single interval of radius $P$ covers each bin. One may always run these finite searches, verify the resulting prime powers, and use trial division of any residual after all searches finish. The latter fallback is needed only for finitely many bit lengths. The algorithm uses ordinary divisor sums of the powers of $N$. The linear number of polynomial-size exact answers is part of its input. Bach, Miller and Shallit obtain a randomized polynomial-time reduction with the different input consisting of the single original value $\sigma(N)$. [Bach–Miller–Shallit, Theorem 2](https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf)

## Exact arithmetic replay

The GP fixture intersects two integer lattices at public moduli with a common factor. The true divisors there are 1,001 and 1,003, which are coprime. A second fixture uses $N=1031^2\cdot659\cdot1613$ and its exact divisor sum to recover the prime 1,031 in an interval with 129 offsets. Its cubic fixture uses $N=3{,}067{,}526{,}838{,}329$ and a supplied multiple $M=1{,}042{,}291{,}580{,}848{,}973{,}061$. With 160,001 offsets the combined first LLL vector gives the prime $1{,}004{,}323$. Its scaled coefficient sum is below the forced divisor bound, certifying vanishing over the entire interval for qualifying roots. Each local first vector by itself misses. With four ordinary divisor sums on powers of a three-prime integer, the final fixture recovers 1,013 and checks the shortness inequality again. It uses the sum of dual lattices to compute the intersection exactly. The fixture uses small lattice parameters for speed. The dimension in the general theorem is larger. [GP replay](../experiments/hidden-divisor-lattice.gp)
