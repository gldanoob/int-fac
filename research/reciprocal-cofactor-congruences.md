# Factoring with congruences in both directions

Let $N=xy$, $x,y>1$, and let $F,G\in\mathbb Z[X]$ have positive degrees $d,e$. Suppose $\gcd(F(0)\operatorname{lc}(G),N)=1$. Fix positive integers $r,s$ and assume

$$
 x^r\mid F(y),\qquad y^s\mid G(x).
$$

Given $N$ and the polynomials, a deterministic algorithm finds a proper divisor in

$$
 N^{\,\max\{0,\, (1-4rs/(de))/(4(1+r/d+s/e))\}}
 \operatorname{poly}(b,d,e,r,s,\mathrm{bits}(F),\mathrm{bits}(G))
$$

bit operations, where $b=\mathrm{bits}(N)$. For fixed polynomials and exponents the algorithm receives only $N$. **If $4rs\ge de$, including equality, it splits all such products in polynomial time.** The factors may be very different sizes and may themselves be composite. On semiprimes the split is the complete factorization.

For example, the reciprocal divisibilities $x\mid y^2+y+13$ and $y\mid x^2+x+5$ suffice. So does any ordered pair of the cyclotomic polynomials $\Phi_3,\Phi_4,\Phi_6$ in the two directions. With two quartics and $r=s=1$ the bound is $N^{1/8}$ times polynomial overhead. A quadratic and a quartic give $N^{1/14}$. These exponents describe a direct arithmetic search on the stated families. The general all-input subexponential factoring bound still applies independently. [Single complementary-factor congruence](hidden-divisor-lattices.md#a-congruence-on-the-complementary-factor) · [All-input benchmark](known-results.md)

## Two hidden coprime divisors

The factors are automatically coprime under the exact hypotheses. A prime dividing both would divide $F(y)$ and $y$, hence $F(0)$, contrary to its being a unit modulo $N$. Form

$$
 M_1=N^{d+r},\qquad H(X)=X^d F(N/X),\qquad M_2=N^s.
$$

$H$ is an integral polynomial with leading coefficient $F(0)$. Multiply by its inverse modulo $M_1$ and lift the other coefficients to obtain a monic integral polynomial $f_1$ of degree $d$. Likewise normalize $G$ by its leading coefficient modulo $M_2$ to get a monic $f_2$ of degree $e$. On the hidden integer $x$, $H(x)=x^d F(y)$ is divisible by $x^{d+r}$ and $G(x)$ is divisible by $y^s$. Thus the two rows at moduli $M_1,M_2$ have coprime hidden divisors $x^{d+r},y^s$, even though the public moduli are powers of the *same* integer. Reducing individual coefficients to least nonnegative residues and setting the leading coefficient exactly to one preserves these divisibilities.

Use the [intersection lattice for overlapping moduli](hidden-divisor-lattices.md#a-lattice-for-overlapping-public-moduli). Its radius is $\exp(S)/8$ where $S=\sum_i(\log A_i)^2/(\deg(f_i)\log M_i)$ and each $A_i$ is a public lower bound on the corresponding hidden divisor. No modulus needs to be factored. The construction uses exact integer linear algebra, LLL and polynomial factorization over the rationals. [Lenstra, Lenstra and Lovász](https://doi.org/10.1007/BF01457454)

## Charging every interval, including the equality case

Write $\mu=r/d,\ \nu=s/e,\ L=\log N$. For exact $x$ and $y$ and $\alpha=\log(x)/L$, the radius exponent with the hidden divisors as lower bounds would be

$$
 S/L=(1+\mu)\alpha^2+\nu(1-\alpha)^2.
$$

To obtain the useful bounds without knowing $\alpha$, take an integer $T\ge 2+2s$. Trial-divide through $T$; one may take $T=2+2s$. For the remaining $x$-values use consecutive integer bins $[P,U]$, starting at $T+1$, with $U=\min(N-1,P+\lfloor P/T\rfloor)$ and the next $P=U+1$. There are $O(T\log N)$ bins. Put

$$
 Q=\lceil N/U\rceil,\quad A_1=P^{d+r},\quad A_2=Q^s .
$$

Any genuine solution in the bin has $x\ge P$ and $y\ge Q$. Now define $\alpha=\log P/L$ for this **known** bin. Since $\log Q\ge(1-\alpha)L-1/T$, the radius exponent obeys

$$
 S\ge L\big((1+\mu)\alpha^2+\nu(1-\alpha)^2\big)-2\nu/T.
$$

The inequality also holds when $(1-\alpha)L<1/T$, by nonnegativity of the squared term. The additive loss is bounded by one even if $s$ varies. A bin needs $O(1+P\exp(-S))$ lattice windows, allowing an absolute constant for the factor eight and integer rounding. If the guaranteed radius is below one, try individual integers there. For explicit window sizes one can approximate the logarithms by certified rational intervals to absolute error less than $1/4$ in $S/\log 2$, and use a lower binary power divided by 16. Their required bit precisions are polynomial in the listed inputs. The bin center, both degrees, the public moduli and every lattice basis entry have polynomial bit length.

The maximum loss over all bins follows by completing the square:

$$
 \alpha-(1+\mu)\alpha^2-\nu(1-\alpha)^2
 =\frac{1-4\mu\nu}{4(1+\mu+\nu)}
 -(1+\mu+\nu)\left(\alpha-\frac{1+2\nu}{2(1+\mu+\nu)}\right)^2.
$$

In particular at $4\mu\nu=1$, even a bin containing the maximum needs only a bounded number of windows. This includes unequal degrees, positive exponents larger than one and factors near the endpoints of the range. Integer roots of each short polynomial are checked by division into $N$. If the congruence pair is requested as a certificate, test it by direct polynomial evaluation on the recovered factors.

## Partial divisibility and coefficient endpoints

The same argument handles known defect bounds $A,B\ge1$ on coprime factors, meaning

$$
 \frac{x^r}{\gcd(x^r,F(y))}\le A,\qquad
 \frac{y^s}{\gcd(y^s,G(x))}\le B.
$$

The true hidden divisors become $x^d\gcd(x^r,F(y))$ and $\gcd(y^s,G(x))$. Use the ceilings of $P^{d+r}/A$ and $Q^s/B$ for the two lower bounds. For $u,v\ge0$, $\max(0,u-v)^2\ge u^2-2uv$. It follows that the additional radius loss is at most $2\log A/d+2\log B/e$, because both $P$ and $Q$ are at most $N$. This multiplies the search bound by at most $A^{2/d}B^{2/e}$ up to absolute constants. In particular polynomially bounded defects preserve polynomial recovery when $4rs\ge de$. If only an allowed defect is known, accept candidates by the two gcd inequalities.

For a specified coprime factorization, exact powers of $X$ in either polynomial can first be removed since evaluation at the complementary factor multiplies by a unit. If a needed coefficient has a proper gcd with $N$, that gcd already splits $N$. If the gcd equals $N$, it supplies no inverse. One can also try interchanging the ordered factors and polynomials if the opposite normalization uses units. For fixed nonzero endpoint coefficients, divisibility of an entire $N$ into an endpoint occurs only for finitely many $N$. A nonzero constant polynomial whose value is a unit makes its positive-exponent divisibility impossible. A zero polynomial gives a vacuous condition and leaves the [one-sided problem](hidden-divisor-lattices.md#a-congruence-on-the-complementary-factor) on the other side. The two-row degree formula assumes two nonconstant polynomials and the stated unit coefficients.

## How many rough, unbalanced products occur?

Fix $F=X^2-2X+4$ and $G=(X-1)(X-2)$. For each odd $t>1$, put

$$
 x=t^2+t+1,\qquad y=t(t^2+t-1),\qquad N=xy .
$$

Then $\gcd(x,t)=1$ and $\gcd(x,t^2+t-1)=1$ since both quadratics are odd and differ by two. The congruence $y\equiv-2t\bmod x$ gives $F(y)\equiv4(t^2+t+1)\equiv0\bmod x$, and $G(x)=(t+1)y$. The complementary factors are of sizes $N^{2/5+o(1)}$ and $N^{3/5+o(1)}$. The family also has a simpler direct splitter: $N=t^5+2t^4+t^3-t$ lies strictly between $t^5$ and $(t+1)^5$, so its integer fifth root recovers $t$. These parametrized products provide a lower bound on the size of the congruence class.

There is an absolute $\eta>0$ such that for all sufficiently large $X$, at least $\gg X^{1/5}/(\log X)^3$ **distinct** products in $[X,2X]$ from this family have every prime factor larger than $X^\eta$. To see this, let $T=X^{1/5}$ and take $T\le t\le 1.1T$, so the products lie in the dyad for large $X$. At a prime $\ell>5$ the three factors of $t(t^2+t+1)(t^2+t-1)$ have disjoint zero sets. Their total number of roots is

$$
 \rho(\ell)=3+(-3/\ell)+(5/\ell).
$$

The primes $2,3,5$ have admissible residues, as seen from $t=1,2,1$ respectively. The prime harmonic sums of the two fixed nonprincipal characters converge by the prime number theorem in fixed progressions and partial summation with its classical error bound. Hence the local product through $z$ is $\asymp(\log z)^{-3}$ and the required upper sieve dimension is 3. For squarefree $d$, CRT and interval endpoints give an error $O(\rho(d))$, where $\rho(d)\le5^{\omega(d)}$. Through level $T^{1/2}$ the sum of these errors is $T^{1/2+o(1)}$ by the elementary divisor bound. Take $z=T^\epsilon$ with a sufficiently small fixed positive $\epsilon$. The lower bound in the fundamental lemma of the sieve leaves $\gg T/(\log T)^3$ survivors, all odd. Distinct $t$ give distinct $N$ by the fifth-root identity, and any $\eta<\epsilon/5$ works. The population statement counts proper splits into coprime blocks. Primality of the displayed blocks is not needed. [Fundamental lemma of the sieve, Theorem 2.2](https://kurlberg.github.io/eprints/2dscar.pdf#page=9)

For fixed nonzero $F,G$ of bounded degree, pairs with $F(y)G(x)\ne0$ give at most $X^{1/2+o(1)}$ such integers in $[X,2X]$. Iterate their smaller factor $m\le\sqrt{2X}$. The larger factor divides a nonzero member of $\{F(m),G(m)\}$ of size $X^{O(1)}$. Each such value has at most $X^{o(1)}$ divisors. This upper bound also permits $X^{o(1)}$ choices of the polynomial pair with bounded degrees and coefficient sizes $X^{O(1)}$. A zero evaluation gives a factor among the positive integer roots of a public polynomial. [Maximal order of the divisor function](https://terrytao.wordpress.com/2014/11/23/254a-notes-1-elementary-multiplicative-number-theory/)

## Evidence and related results

The [PARI/GP fixture](../experiments/reciprocal-cofactor-congruences.gp) searches the public bins from $2^8$ upward using finite, reduced 18-dimensional lattice parameters. For $N=250112689$, the two different-constant irreducible quadratics $F=X^2+X+13$, $G=X^2+X+5$ recover $2207$ and $113327$, a ratio over 51. The seventh window is centered at 2560 with radius 512. Its scaled short-vector coefficient sum is strictly smaller than the integer product of the public lower bounds to their forced powers, certifying integer vanishing on the entire 1,025-integer window for all qualifying roots. The script checks the reversed-polynomial identities also on 10 exact and 8,342 deficient finite examples, including nonmonic second polynomials with negative coefficients.

The special pair $\Phi_3,\Phi_3$ has an elementary Vieta-jumping solution that predates this calculation. If $x,y$ are coprime and mutually divide $z^2+z+1$ evaluated on the other factor, then $x^2+y^2+x+y+1=5xy$. Hence $(x+y)^2+(x+y)+1=7N$. That identity uses the same polynomial in both directions. The lattice proof permits arbitrary unit-endpoint polynomials of the indicated degrees and proves its bound only on the promised inputs. [Huy Nguyen and Tam Nguyen, Example 1.3](https://www.cs.cmu.edu/~hn1/documents/cyclic-number-theory/cyclic-number-theory.pdf)

The replay checks the two congruences, coprimality and fifth-root decoding on all 4,500 odd parameters from 1,001 to 9,999. Of the resulting products, 77 have no prime factor through 101. It also checks the local root counts at all 26 primes through 101.
