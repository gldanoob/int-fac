# Polynomial-time factoring reduction to the middle three-square digit

Complete integer factoring has an **unconditional deterministic polynomial-time Turing reduction** to the bit at position $\lfloor(\log_2 M)/2\rfloor$ of the ordered positive three-square count $C(M)$, on indices $M\equiv3\pmod8$. A prime-index construction uses $O(b^2)$-bit indices for a $b$-bit input. Grouping primitive parts of composite cyclotomic orders lowers this to **$O(b^2/\log b)$ bits**. The [linear-bit reduction](middle-three-square-bit.md) has $2^{O(b/\log(2b))}$ arithmetic overhead.

## Count schedule and divisibility

Strip primes through the square of the original bit length by trial division, recording full multiplicities. This includes every prime needed for the [small twist library](middle-three-square-bit.md#an-unconditional-family-of-logarithmically-many-twists) at all sufficiently large bit lengths. Handle bounded inputs by direct division. At any remaining cofactor $n$ write $b=\lfloor\log_2n\rfloor+1$. Every remaining prime is greater than $b^2$. Take roots of squares, carrying multiplicities, and finish primes by deterministic primality testing. A nonsquare has a prime $p$ of odd valuation $e$. Put $h=(e-1)/2$.

Choose a squarefree $a$ coprime to $n$ with $an\equiv3\pmod8$ and $a\le n$. For an exact-count oracle one may take $a=3n\bmod8$ in $\{1,3,5,7\}$. Use the indices

$$
m_j=a n^{2j+1},\qquad 1\le j<8b.
$$

In the fundamental part of $m_j$ the prime $p$ is ramified. The Hurwitz local factor in $M_j=C(m_j)$ is exactly $1+p+\cdots+p^{h+ej}$. The positive integer $M_j$ contains it as a divisor, with the exceptional weight at fundamental discriminant $-3$ already absorbed in $C(3)=1$. For each prime $b<r\le8b$ the integer $e$ is a unit modulo $r$. Let $1\le j_r<r$ solve $ej_r\equiv-h-1\pmod r$. It exists in the specified range since $1\le h+1<r$. Then

$$
D_r=\Phi_r(p)\mid M_{j_r}.
$$

For distinct primes $r,s$, the identity $\gcd(p^r-1,p^s-1)=p-1$ implies $\gcd(D_r,D_s)=1$. This is a condition on hidden divisors. The public counts can share prime factors, and even equal public moduli are allowed. All small-factor removal occurs **before** the query at the current cofactor. No update divides an old count by a factor that would require an unknown character. [Hurwitz local factors](https://arxiv.org/pdf/2010.14315#page=5)

## Radius and polynomial cost

Try every odd $1\le e\le b$ and every eligible dyadic bin $P\le p<2P$. On row $r$ use the monic polynomial $\Phi_r(X)$, of degree $d_r=r-1$, the public modulus $M_{j_r}$ and the integer lower bound $A_r=P^{r-1}$. Skip a guess if any $A_r>M_{j_r}$. For the true guess one has $D_r\ge A_r$. The [intersection-lattice theorem](hidden-divisor-lattices.md#a-lattice-for-overlapping-public-moduli) gives a certified search radius $\exp(S)/8$ where, with natural logarithms,

$$
S=\sum_{b<r\le8b\,/\,r\ \mathrm{prime}}
   \frac{(\log A_r)^2}{d_r\log M_{j_r}}.
$$

The elementary bound $C(m)\le m$ follows by enumerating the first two coordinates. Since $a\le n$ and $j_r\le r-1$,

$$
\log M_{j_r}\le (2j_r+2)\log n\le2r\log n.
$$

Each row therefore contributes at least $(\log P)^2/(4\log n)$, including rows where $j_r$ is close to $r-1$. By the prime number theorem there are at least $4b/\log b$ primes in $(b,8b]$ for all sufficiently large $b$. Also $\log n<b\log 2$ and $P> b^2/2$ for the true bin. Hence

$$
\frac{S}{\log P}\ge\frac{\log P}{(\log2)\log b}\ge\frac{3}{2\log2}>2
$$

for large $b$. This bound covers primes immediately beyond the trial cutoff. With $P>8$ it gives $\exp(S)/8>P$. Use one interval of radius $P$ centered at $P$ to cover the whole bin. Verify every candidate by divisibility and primality. If no candidate is found after all guesses, direct trial division suffices for the finitely many small bit lengths outside the estimates.

There are $O(b)$ rows with degrees $O(b)$ and moduli of $O(b^2)$ bits. The cited theorem's integer lattice dimension $2+2\sum_r\lceil\log_2 M_{j_r}\rceil$ is $O(b^3)$. Translation by the bin center, coefficient scaling, Hermite normal form intersections, LLL and exact univariate integer-root extraction all take polynomial bit time by that theorem. The coprime $D_r$ give divisibility by the product of all forced powers throughout the intersection. Bounding each modulus separately without forming the intersection would only give the individual radii.

The guesses cover every odd-valuation prime. Strip the full multiplicities of the verified primes. Any additional even-valuation prime that passes verification can be stripped too. The quotient is a square. Take its square root and double the multiplicity weight for the next call. This requires $O(\log(2b))$ rounds. The largest exact-count index has $O(b^2)$ bits.

## Shorter powers from composite cyclotomic orders

On a guessed dyadic bin $P=2^k$ and odd valuation $e$, discard $P^e>n$. Use an absolute constant $J_0$ specified by the estimates below and put

$$
J=\max(J_0,\lceil 256b/(ek)\rceil),\quad
\lceil J/2\rceil\le j\le J,\quad r_j=ej+(e+1)/2.
$$

Thus $J=O(1+\log n/\log(p^e))$ on the true bin. A block $p^e\ge n^\delta$ for fixed $\delta>0$ can be found with linear-bit indices by trying the bins and exponents with $P^e\ge n^{\delta/2}$, handling bounded inputs directly. The upper bound over every retained guess is $J=O(b/\log b)$ because $P>b^2/2$. The largest count and padded digit indices then have $O(b^2/\log b)$ bits. One can request all powers to the largest required $J$ once per cofactor.

Assign every integer $v\ge3$ dividing at least one $r_j$ to the first such row $j$, and denote its set by $I_j$. It contains $r_j$ since the indices increase strictly. Use

$$
 f_j=\prod_{v\in I_j}\Phi_v,\quad d_j=\deg f_j,\quad
 A_j=\left\lceil\frac{P^{d_j}}{\prod_{v\in I_j}(4v)}\right\rceil.
$$

The hidden divisor $D_j=\prod_{v\in I_j}\Phi_v^*(p)$ uses only prime divisors whose multiplicative order on $p$ is exactly $v$, with the order understood as the order of $p$ modulo that prime. These divisors are pairwise coprime across rows. Their product within each row divides $f_j(p)$, which in turn divides $(p^{r_j}-1)/(p-1)$ and hence $M_j$. For $v\ge3$, $\Phi_v^*(p)=\Phi_v(p)/\gcd(\Phi_v(p),v)$ and $\Phi_v(p)>p^{\varphi(v)}/4$. This gives $D_j\ge A_j$. The algorithm uses the public polynomial $f_j$ and never computes the hidden primitive parts. [Glasby, Lübeck, Niemeyer and Praeger, Lemmas 5(f), 7 and Remark 8](https://arxiv.org/pdf/1504.02598#page=4)

Uniformly over the retained guesses $r_J=O(b/k)$ since $ek\le b$. Thus $4r_J\le P$ for sufficiently large $b$. Every assigned order has $\varphi(v)\ge2$, so $|I_j|\le d_j/2$ and $\log A_j\ge(d_j/2)\log P$.

To bound the total degree, first suppose $e<J$. For a prime $\ell\mid e$, no $r_j$ is divisible by $\ell$. Each other prime divides at most $m/\ell+1$ of the $m=J-\lceil J/2\rceil+1$ indices. Since $r_J\le2J^2$ and $1-\varphi(r)/r\le\sum_{\ell\mid r,\ \ell\text{ prime}}1/\ell$, it follows that

$$
\sum_j \frac{\varphi(r_j)}{r_j}
\ge m\left(1-\sum_{\ell\text{ prime}}\ell^{-2}\right)
       -\sum_{\ell\le2J^2,\ \ell\text{ prime}}\ell^{-1}
\ge m/4.
$$

The last bound holds for all $J\ge J_0$ by $\sum_{n\ge2}n^{-2}<2/3$ and the elementary harmonic bound $O(\log J)$ for the second sum. Since $d_j\ge\varphi(r_j)$ and $r_j\ge ej$, this gives $\sum_j d_j/j\ge eJ/8$.

For $e\ge J$, an order assigned to an earlier $i$ and dividing $r_j$ divides $\gcd(r_i,r_j)$, itself a divisor of $j-i$ since $\gcd(e,r_i)=1$. The sum of the degrees of all cyclotomic polynomials indexed by divisors of $\gcd(r_i,r_j)$ is $\gcd(r_i,r_j)$. Orders 1 and 2 cost at most two more degrees. Hence

$$
 d_j\ge r_j-2-\sum_{\lceil J/2\rceil\le i<j}(j-i)\ge r_j/2
$$

for $J_0\ge16$, since $r_j\ge J^2/2$. This again gives $\sum_j d_j/j\ge eJ/8$, including cases with arbitrarily large valuation and bounded $J$.

Using $\log M_j\le(2j+2)\log n\le3j\log n$ now gives

$$
 \frac{S}{\log P}\ge
 \frac{\log P}{12\log n}\sum_j\frac{d_j}{j}
 \ge\frac{eJ\log P}{96\log n}>2.
$$

The radius covers every eligible bin, including the first one after trial division. The orders are $O(b/\log b)$, the degrees are at most $r_j$, and all cyclotomic products have polynomial dense bit size. For example the coefficient magnitudes of each monic product of roots of unity are bounded by $2^{d_j}$. The same lattice, prime verification, exact-count reconstruction and square-root recursion apply. For small blocks the sufficient count power grows with $\log n/\log(p^e)$. Changing the squarefree twist at a fixed power cannot increase this particular source of local divisibilities, since the ramified local sum at $p$ is identical for every allowed twist.

## Replacing the exact counts by one digit

Use the middle-bit twist library at scale $b$ before requesting the power counts. It contains $O(\log b)$ squarefree values $a$ and uses $F=\prod_{3\le p\le b}p$ over odd primes. For at least one twist the middle-bit sweep recovers the amplified count at $anF^2$ from a transition in its dyadic interval. This already guarantees transitions at *every* $m_jF^2$ for the accepted twist. All these indices share the same fundamental character, and the normalized local factors $g_h(p)=1+(1-\chi(p))\sum_{i=1}^h p^{-i}$ are nondecreasing as the conductor exponent grows. Test the base, then recover the count at each power by the middle-bit sweep and divide by its computable amplification ratio. The field character does not have to be constructed. The work is polynomial in the largest query bit length, which remains $O(b^2)$. [Unconditional twist estimate and exact midpoint decoder](middle-three-square-bit.md)

## Evidence

Run `gp -fq experiments/ramified-power-lattice.gp`. At $n=10007^3\cdot5003^2$ both primes exceed the trial cutoff $65^2$. On all 79 prescribed prime rows the program verifies divisibility into independently computed positive counts, pairwise coprimality and the public-modulus size bound. Using actual integer bit lengths to round denominators upward gives $\lfloor S/\log2\rfloor\ge470$ in a bin starting at $2^{13}$.

A second replay uses four smaller indices in a 14-dimensional lattice. A short polynomial recovers the prime $10007$ from the 33-integer interval centered at $10000$. The scaled coefficient sum has 359 bits and is strictly below the 386-bit forced-divisibility bound. This finite lattice uses reduced parameters. The asymptotic $O(b^3)$-dimensional construction and its runtime are justified by the written radius calculation and the linked intersection theorem.

On 26 consecutive composite-order rows, 17 collect several orders and two full polynomial values share factors with earlier rows. Their primitive parts pass the pairwise-coprimality test and divide the independent counts. The exact rounded lower bound gives $\lfloor S/\log2\rfloor\ge188$ in the same bin, using count indices through 6,512 bits. A further 128 exponent and interval pairs exercise both cases of the summed-degree estimate. [PARI/GP replay](../experiments/ramified-power-lattice.gp) · [Related ordinary divisor-sum lattice](hidden-divisor-lattices.md#ordinary-divisor-sums-on-powers-of-the-original-input)
