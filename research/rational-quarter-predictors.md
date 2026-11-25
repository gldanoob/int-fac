# Recovering a divisor from the formulas of a quarter-bit predictor

Let $n=P_1^{a_1}P_2^{a_2}$ for distinct odd primes. Write $r$ for either mixed root of one, with opposite signs at the two prime powers. At a unit center $t$ the informative part of the centered floor-sum parity is $H(rt/n)$, where $H(x)=\operatorname{sgn}\cos(2\pi x)$. The other root pair has a publicly computable contribution. Here the input $n$ is fixed and the center is uniformly distributed over its units. [Centered identity and mixed bit](floor-sum-and-log-parity.md#nonadaptive-queries-for-two-distinct-prime-divisors)

Consider an input-only prediction method using $d$ tests of whether a rational modular expression in $t$ belongs to an interval, and $s$ Jacobi symbols of rational expressions in $t$. The formulas, interval endpoints and final Boolean function can depend on all bits of $n$ and must be fixed before $t$ is chosen. Rational functions are given by numerator and denominator polynomials of degrees at most $D$, with coefficients modulo $n$. At zero Jacobi symbols and noninvertible denominators the predictor may answer arbitrarily. A zero or constant formula conveying only a fixed answer can be removed. In particular the model makes no special provision for an identically zero denominator used to encode extra input-dependent information.

Suppose its success probability is at least $1/2+\delta$, $0<\delta\le1/2$. One can find a proper divisor of $n$ deterministically using only the rational formulas. This completely factors a squarefree two-prime input. A uniform predictor available at every residual cofactor gives complete factoring, including multiplicities, by recursion with primality and perfect-power tests. No labels or evaluations of the predictor are needed. For fixed $d$, $s=O(\log b)$, $D,1/\delta=\operatorname{poly}(b)$ and $b=\lceil\log_2(2n)\rceil$, the cost is polynomial in $b$. This isolates which public coefficients could certify an advantage. Constructing such formulas from a general $n$ remains open.

## Small combinations to try

For an interval formula $Q_i(X)=U_i(X)/V_i(X)$ compute $a_i=[X]Q_i$ in its **Laurent expansion at zero** modulo $n$. A pole at zero is allowed. Remove the initial power of $X$ from $V_i$, then invert the resulting series to the $O(D)$ coefficients needed. A proper gcd with $n$ during inversion immediately splits $n$. For preprocessing, reduce coefficients modulo $n$ and take gcds of nonzero coefficients with $n$. Check the minors of each numerator and denominator coefficient pair as well. A proper gcd suffices. Otherwise a rational expression is constant at both residue primes, with the same public formula for its value, or is nonconstant at both. Indeed, using a unit denominator coefficient as pivot gives proportional coefficient vectors exactly when all its minors vanish. This criterion holds modulo $n$ and modulo either prime after the coefficient and minor checks. Ignore the poles of a constant expression in the probability estimate below. A polynomial identified with zero has its known constant symbol handled before the argument.

Choose a sufficiently large effective absolute constant $C$. Put
$$
 K=\left\lceil(C(d+1)(D+1)^2/\delta)^2\right\rceil,\quad
 W=2^{(s+d)/2}[C\log(2K)]^{d+1},\quad
 B=\left\lceil K+\big(C(1+s+d)(1+D)W/\delta\big)^2\right\rceil.
$$
Trial divide through $B$, stopping at $\sqrt n$ if reached. For all $|m_i|\le K$ and $1\le k\le K$, form $A=\sum_i m_i a_i\bmod n$ and test $\gcd(A-k,n)$ and $\gcd(A+k,n)$. For a squarefree two-prime input any proper gcd is already a prime. For repeated factors a preprocessing gcd can be a mixed proper divisor, which is why the complete recursive version assumes access to formulas on each cofactor. The enumeration and trial division cost $[B+K(2K+1)^d]\operatorname{poly}(b,s,d,D)$ with normalized coefficient encoding. The Boolean table and interval endpoints are unnecessary to this search.

## Why an advantage forces a gcd

Assume the search finds no proper gcd and put $P=\min(P_1,P_2)>B$. Work on the full $n$-grid. Passing from units to all centers costs $O(1/P)$ in expected sign correlation. Ignoring all poles, character zeros and critical points of nonconstant interval maps costs $O((1+d+s)(1+D)/P)$. For this estimate the derivative of a nonconstant rational function of degree $D<P$ is nonzero over either prime field. Count the $O(D)$ exceptional residues by its derivative numerator and by its original numerator or denominator as appropriate. On the remaining centers a value of an interval map has at most $D^2$ preimages modulo $n$. Each prime residue solves a nonzero polynomial of degree at most $D$, with unit derivative, and Hensel lifting gives at most one extension per solution and prime power.

Replace each interval sign and the mixed-root sign by its circle Fejér mean of degree $K$. An interval crossing costs at most the kernel tail $O(1/(Kz))$ at distance $z$ from its endpoints and at most two everywhere. On a uniform $n$-grid the mean absolute error is $O(\log(2K)/K+1/n)$ by grouping distances from the two endpoints. This includes hits at an endpoint. For a nonconstant rational interval map the good-grid mean error is at most $D^2$ times this bound by the preimage count. The target $r t$ is a unit multiplier and preserves the grid. The Fejér means lie in $[-1,1]$. Extend the Boolean combining function to this cube by its multilinear polynomial. It equals the expected sign for independent input signs of given means, so changing any input costs at most its absolute change. Thus total expected replacement error is $O((d+1)(D+1)^2\log(2K)/K)$ apart from the exceptions above. The smoothed target has zero constant coefficient since $H$ has mean zero.

The sum of the absolute Walsh coefficients of a Boolean function of $s+d$ signs is at most $2^{(s+d)/2}$ by Parseval. The Fourier absolute sum of a smoothed interval sign is $O(\log(2K))$, from the geometric interval coefficient bound. Expanding the smoothed product, including its target, gives absolute coefficient sum at most $W$. Each term on units away from poles and zeros is a product of Jacobi symbols times
$$
 e_n(F(t)),\qquad F(X)=\sum_{i=1}^d m_i Q_i(X)-k r X,\qquad 0<|k|\le K.
$$
Changing all $m_i,k$ signs when appropriate reduces the gcd tests to positive $k$. For each term, at least one residue prime $p$ has $[X]F=A-kr\ne0\pmod p$. Otherwise $A-k$ and $A+k$ vanish at opposite primes. Each is a unit at the prime where the other vanishes since $2k$ is a unit. The gcd search would have split $n$. Laurent coefficient extraction commutes with reduction at each prime because the stripped denominator constant is a unit.

At the selected block the additive rational phase is nonconstant and has degree at most $dD+1<p$. Over the prime field a pole of a nonconstant rational function of this degree has order strictly below $p$, precluding an Artin–Schreier phase. The mixed additive–multiplicative Weil bound gives normalized magnitude $O((1+s+d)(1+D)/\sqrt p)$, including the case of a trivial multiplicative factor. Excluding the finitely many discarded residues, including critical points, costs the same or less. The nonzero CRT multiplier of $F$ preserves nonconstancy. [Cochrane–Pinner, Theorem 1.1](https://www.math.ksu.edu/~cochrane/research/stepmix.pdf)

At a higher prime power $p^a$, sum first over the $p$ lifts $t=t_0+jp^{a-1}$. All Jacobi factors and discarded-residue tests are constant on these lifts. On invertible denominators $F(t)\equiv F(t_0)+jp^{a-1}F'(t_0)\pmod{p^a}$. Their additive phases cancel unless $F'(t_0)=0\bmod p$. Its nonzero derivative numerator has degree $O(1+dD)$, giving the stronger bound $O((1+dD)/p)$ here. CRT factorizes the complete term, and the other block contributes absolute mean at most one. Consequently the entire absolute correlation is at most the smoothing and exceptional-set errors plus $O(W(1+s+d)(1+D)/\sqrt P)$. Increasing the absolute constant in the choices of $K,B$ makes this smaller than $2\delta$, contrary to the assumed prediction advantage.

In particular interval formulas with zero Laurent linear coefficient, such as $X^2$, $1/X$, or any publicly shifted threshold on their values, together with Jacobi symbols cannot supply this advantage at primes exceeding $B$. The statement uses chosen centers at a single modulus. The earlier input-probe result averages over an unknown prime and limits bits read from the modulus. [Earlier input-probe model](centered-bit-probes.md#rational-functions-and-quadratic-character-probes)

## A sharper direct test for one quadratic

For every odd $n$, any unit $r$, and any $Q(X)=aX^2+bX+c$ with $a$ a unit, an interval sign of $Q(t)\bmod n$ has absolute correlation with $H(rt/n)$ at most $O((1+\log n)^2/\sqrt n)$ on the full grid, uniformly over all intervals and coefficients. This includes prime powers and moduli with many distinct primes. Restricting to units changes the bound by $O(1-\varphi(n)/n)$ when the unit proportion is bounded below.

Indeed the normalized quadratic sum with input and target Fourier indices $m,k$ vanishes unless $g=\gcd(m,n)$ divides $k$. When it does, the magnitude is $\sqrt{g/n}$ by reduction and the complete odd-modulus quadratic Gauss sum. Equivalently its squared magnitude follows by differencing the sum and using orthogonality of the resulting linear phase. The target's zero coefficient contributes at most $1/n$, since odd-grid quarter signs have signed sum $\pm1$. The constant input term has no other contribution. For fixed $g$ the absolute sums of the nonzero interval coefficients at multiples of $g$ are $O((1+\log n)/g)$ for each of the input and target. Summing the product with $\sqrt{g/n}$ uses $\sum_{g\mid n}g^{-3/2}\le\zeta(3/2)$. This supplies the stated saving without a small-prime cutoff.

## Finite checks

Run `python3 experiments/rational-quarter.py`. The check verifies the complete Gauss-sum magnitude at 3,653 frequency pairs numerically. Exact enumeration of 29,760 unit-leading quadratics on six grids gives the largest signed correlation with **any** interval as $9/15,19/35,21/45,33/77,37/99,49/143$ at $n=15,35,45,77,99,143$, respectively. Constant terms are included by translating intervals. [Replay](../experiments/rational-quarter.py)

The public menu uses quarter tests on $t,t^2+t,t^{-1},\lfloor\sqrt n\rfloor t$, plus the Jacobi symbols of $t+3,t^2+1$. The table grants the classifier the empirical majority for every complete tuple of answers, including zeros. Two additional planted predictors at each modulus make one small difference of slopes equal $r$, first with a common quadratic term and then with a common reciprocal term. The gcd search with coefficients bounded by one split all four planted examples.

| Modulus | Unit centers | Best public menu | Public slope gcd at bound two | Planted quadratic agreement | Planted reciprocal agreement |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 10,403 | 10,200 | 7,669 | 103 | 7,722 | 7,592 |
| 15,049 | 14,800 | 8,047 | none | 10,990 | 11,110 |
| 1,050,703 | 1,030,200 | 588,508 | none | 772,594 | 772,200 |
| 507,527 | 506,016 | 256,618 | none | 379,507 | 379,198 |

The bound-two public search in the table is a finite diagnostic. The proof chooses its bounds from the promised advantage, degree and number of probes. Across the planted tests the slopes include information derived from the factors. They exercise the extraction implication.
