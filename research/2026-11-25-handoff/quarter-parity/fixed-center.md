# Factoring two prime powers through a fixed-center parity oracle

For odd $N$, put
$$
 B(N)=\#\{1\le x\le\lfloor N/4\rfloor:x^2\equiv1\pmod N\}\bmod2.
$$
A zero-error randomized polynomial-time reduction factors any odd $n$ with exactly two distinct prime divisors using $B(n\ell)$, where each queried $\ell>n$ is a certified prime supplied openly to the oracle. The two input prime powers may have arbitrary exponents. The centered identity also gives the reduction to the corresponding quadratic floor-sum parity at fixed auxiliary center $c=1$.

## The exact lift

Let $r\in[2,n/2]$ be a mixed root of one, so the roots modulo $n$ are $\pm1,\pm r$. Write $H(u)=\operatorname{sgn}\cos(2\pi u)$, with period one. For prime $\ell\ge5$ coprime to $n$, put $A=\ell^{-1}\pmod n$. Each pair of roots modulo $n\ell$ related by negation has one representative $z\equiv1\pmod\ell$. For the root $x\bmod n$ that representative satisfies
$$
 \frac z{n\ell}\equiv\frac{A(x-1)}n+\frac1{n\ell}\pmod1 .
$$
The pair contributes one precisely when the representative lies in the outer quarters. A point of the $1/n$ grid is at least $1/(4n)$ from either quarter boundary, and $1/(n\ell)<1/(4n)$. Thus the quarter sign agrees before and after the shift. The argument includes grid points at zero. The identity also holds for $\ell=3$ on the stated two-block inputs coprime to $3$. A forward crossing in that case can occur only on a quarter boundary whose scaled left grid endpoint has numerator $(n-1)/4$ or $(3n-1)/4$. The corresponding lift has $x\equiv 4^{-1}\pmod n$. The root condition forces $n\mid15$, and $n=5$ is the only such nontrivial modulus coprime to $3$. It has a crossing but only one block.

Let $h_0(A)=\mathbf1_{H(2A/n)=+1}$. The lifts of $x=1,-1$ contribute $1+h_0(A)$. The two mixed lifts give
$$
 G(A):=(-1)^{B(n\ell)-1-h_0(A)}
     =H\!\left(\frac{A(r-1)}n\right)H\!\left(\frac{A(r+1)}n\right).
 \tag{1}
$$
Only the inverse class $A$ matters. Either mixed root sign gives the same product.

## The hidden Fourier coefficient

Write $n=d_1d_2$ for the prime powers, with underlying primes $p_1,p_2$. The additive orders of $r-1,r+1\bmod n$ are exactly $d_1,d_2$, in some order. Thus under uniform $A\bmod n$ the two arguments in (1) are independent and uniform on their two grids. Units restrict each to unit numerators. At frequency $2r$, the Fourier character is the product of the first harmonics since $(r-1)+(r+1)=2r$. Fourier transforms are normalized.

For odd $d$, write $H_d(u)=H(u/d)$. Summing geometrically over $-\lfloor d/4\rfloor,\ldots,\lfloor d/4\rfloor$ gives
$$
 \widehat H_d(1)=\frac{1}{d\sin(\pi/(2d))}\ge\frac2\pi,\quad
 |\widehat H_d(0)|=\frac1d,\quad
 |\widehat H_d(j)|\le\frac1{\min(j,d-j)}\quad(0<j<d).
$$
Consequently $G^\times=\mathbf1_{(A,n)=1}G$ satisfies
$$
 \widehat {G^\times}(2r)
 \ge \left(\frac2\pi-\frac1{p_1}\right)
      \left(\frac2\pi-\frac1{p_2}\right).
 \tag{2}
$$
The two restricted coefficients are real by evenness. Omitting nonunits changes each by at most $1/p_i$.

For a nonprincipal real character $\psi\bmod n$, at least one local factor, say at $d=p^a$, lifts the nontrivial quadratic character modulo $p$. Reparameterizing the coordinate changes its values by a constant sign factor. Its normalized additive Fourier transform is supported on multiples of $d/p$, with at most $p$ entries of magnitude $p^{-1/2}$, by the prime Gauss sum. Convolving with $\widehat H_d$ bounds the absolute first coefficient by $(3+2\log p)/\sqrt p$, since the $p$ largest bounds in the display sum to at most $3+2\log p$. The other local first coefficient has magnitude at most one. Thus
$$
  |\widehat{\psi G^\times}(2r)|\le (3+2\log p)/\sqrt p.
 \tag{3}
$$
A fixed preliminary small-factor search makes (3) as small as needed. A factor found there determines its full prime-power block by exact division.

## One prime candidate per call

Choose a sufficiently large effective absolute integer $C\ge12$, and let $X=n^C$. Given $A$, compute $\gcd(A,n)$. A proper gcd splits $n$. For nonunit $A$ the conceptual experiment returns zero. For a unit, sample one uniform integer $\ell\in(n,X]$ in the class $A^{-1}\bmod n$. Return zero if $\ell$ is composite. For a prime, certified by deterministic polynomial-time primality testing, return $G(A)$ from (1) using the supplied oracle. All arguments and candidates have $O(\log n)$ bits.

Thorner–Zaman give
$$
 \sum_{\substack{\ell\le X\ {\rm prime}\\\ell\equiv A^{-1}\bmod n}}\log\ell
 =\frac{X}{\varphi(n)}[1-\gamma\psi(A)]\,[1+O(\eta)].
$$
Here $\eta$ can be any sufficiently small absolute constant by increasing $C$. The secondary term is absent without an exceptional zero. Otherwise $\psi$ is a nonprincipal real character and $\gamma=X^{\beta-1}/\beta<1$. The inverse class has the same character value. The uniform relative bound and the lower cutoff for $n$ are effective. [Thorner–Zaman, Corollary 1.4 and Remark 1.5](https://arxiv.org/pdf/2108.10878#page=3)

For $Y=X/(\log X)^3$, the fraction of progression candidates at most $Y$ is $O((\log X)^{-3}+n/X)$. Above $Y$, the weights $\log\ell/\log X$ equal $1+O(\log\log X/\log X)$. The weighted and unweighted success rates therefore differ by $o(1/\log X)$, uniformly in the class, since the weighted rate is $O(1/\log X)$. This includes omission of primes $\ell\le n$. The candidate count is $X/n+O(1)$, so the trial's success probability has the form
$$
 P(A)=\frac{n}{\varphi(n)\log X}
       [1-\gamma\psi(A)+E(A)],\qquad |E(A)|\le 3\eta
 \tag{4}
$$
after increasing the effective cutoff for $n$. Averaging (4) over units gives $n[1+O(\eta)]/(\varphi(n)\log X)$ because the nonprincipal character averages to zero.

The mean output function on the full additive group is $F(A)=P(A)G^\times(A)$. Equations (2)–(4), preliminary removal of bounded primes, and sufficiently small $\eta$ give
$$
 |\widehat F(2r)|\ge \frac{1}{4\log X}.
$$
Apply the significant Fourier transform on $\mathbb Z/n\mathbb Z$ at threshold $1/(8\log X)$. Its sampling estimates consist of linear averages and products evaluated at chosen arguments. For the products use independent trials at the two arguments. This yields the same expected products of mean values and the same absolute bounds, so the concentration argument retains polynomial query and bit costs. Alternatively, repeated trials estimate each chosen mean to inverse-polynomial accuracy with polynomial work. [Akavia–Goldwasser–Safra, FOCS 2003](https://doi.org/10.1109/SFCS.2003.1238189) · [Galbraith–Laity–Shani, Theorem 3.4 and Appendix A](https://arxiv.org/abs/1607.01842)

With probability bounded below by an absolute positive constant per run, the list contains $2r\bmod n$. For every listed $f$, set $s=f/2\bmod n$, check $s^2\equiv1\pmod n$, and test $\gcd(s-1,n)$. Repeat until a proper divisor is verified. Integer roots and primality tests recover the two bases and exponents. Bounded trial division handles $n$ below the effective cutoffs. This gives zero error and polynomial expected time. The oracle restricted to inputs with only two distinct prime divisors is a separate problem.

## Fixed prime powers as auxiliaries

The exact lift also works with $\ell=L^e\ge3$ for a known odd prime $L$, since the two roots modulo $L^e$ are $\pm1$. To use the same chosen-input Fourier transform, this would require realizations of arbitrary classes $A$ by short powers of $L$. Exponent $e$ costs $\Theta(e\log L)$ input bits, and a fixed $L$ reaches only polynomially many residues at polynomial bit length. An algorithm using only this particular deterministic schedule would need a decoding argument for its restricted evaluations.

## Draft extension to a bounded number of prime-power blocks

The replay above covers the two-block lift and its local Fourier estimates. The following argument for growing support awaits independent review, including uniformity in the progression estimate.

The same reduction works for every promised bound $R\ge2$ on the number of blocks, with $e^{O(R^2\log(2R))}\operatorname{poly}(\log n)$ expected bit cost and oracle queries. An oracle call adds one known prime. For each cofactor, strip small primes and recognize primes and prime powers first. In the proof write $h$ for the remaining number of blocks and assume $2\le h\le R$.

Let $e_i$ be the CRT idempotent for the $i$-th block and $x_i=2Ae_i/n\bmod1$. All roots of one are $w=1-2\sum_{i\in S}e_i\bmod n$. The same lift argument and the removal of the known roots $w=\pm1$ give the product
$$
 \mathcal G_h(x)=\prod_{\varnothing\ne S\subsetneq[h]}
          H\!\left(\sum_{i\in S}x_i\right).
 \tag{5}
$$
On the continuous $h$-torus, this function has a coefficient away from the diagonal $k_1=\cdots=k_h$. For a quantitative bound put $e=1/(32h)$, $y=1/4+e$, and $\delta=e/(8h)$. Compare the point with all coordinates $y/h$ to the point with first coordinate $e/2$ and all remaining coordinates $(y-e/2)/(h-1)$. At the first point all proper subset sums are strictly below $1/4$. At the second point exactly one proper subset sum is above $1/4$, namely the subset omitting coordinate one. Each conclusion persists in the coordinate boxes of radius $\delta$. The translation $v$ between the centers has total coordinate sum zero, and
$$
 \|\mathcal G_h-\mathcal G_h(\cdot+v)\|_2^2\ge4(2\delta)^h.
$$
All diagonal frequencies are killed by this difference. Parseval implies that the non-diagonal Fourier energy of $\mathcal G_h$ is at least $\mu=(2\delta)^h$.

Translating one coordinate by $u\in[0,1/K]$ changes (5) only when an affected subset sum is within $u$ of a quarter boundary. Each subset sum is uniform on the circle, so its contribution to the squared difference is at most $16u$. On the Fourier side the average of $|e^{2\pi i k_j u}-1|^2$ over this interval is at least one if $|k_j|>K$. Summing over coordinates bounds the energy outside the box $[-K,K]^h$ by $16h2^h/K$. With $K=\lceil 32h2^h/\mu\rceil$ some non-diagonal mode in the box thus has magnitude at least
$$
 \zeta=\sqrt{\mu/(2(2K+1)^h)}=e^{-O(h^2\log(2h))}.
$$
Use bounds computed with $R$ in place of $h$ if the number of blocks is unknown.

The pullback of the chosen mode to $A\bmod n$ has additive frequency $f=2\sum_i k_i e_i\bmod n$. Couple the continuous coordinates to the independent finite grids of orders $d_i$ by rounding down. If the smallest prime divisor of $n$ is $p_{\min}$, the total phase error is at most $2\pi hK/p_{\min}$. The probability that any subset sum crosses a boundary is at most $4h2^h/p_{\min}$, since each continuous subset sum is uniform. Removing nonunits costs at most $h/p_{\min}$. Thus the finite coefficient has magnitude at least $\zeta-O(h(K+2^h)/p_{\min})$.

For an exceptional character with a nonprincipal factor at $p^a$, fix all other coordinates and sum over the coordinate of $p^a$. The sliced function (5) is a step function with at most $2^h$ jump points on the circle. The geometric-sum bound for each interval's Fourier coefficients, and the same top-$p$ estimate as in (3), bound the twisted sliced coefficient by $O(2^h(1+\log p)/\sqrt p)$. This holds uniformly in the other coordinates and at all frequencies, including the mode above. Averaging preserves the bound. A trial cutoff $[C_0 R(2^R+K)/\zeta]^4$ with sufficiently large absolute $C_0$ makes both the discretization and twisting errors smaller than $\zeta/8$, and ensures $p_{\min}>4K$. It has size $e^{O(R^2\log(2R))}$. Use $R$ for $\zeta,K$ and this cutoff throughout.

In the prime sampler, multiply the success indicator at a certified prime by an independent acceptance indicator of probability $\log\ell/\log X$, to within absolute error $\zeta/(10^3\log X)$. Elementary logarithm approximations by a convergent power series give the required rational probability with polynomial bit cost. The weighted success probability is then given directly by the Thorner–Zaman estimate. Choose the integer exponent in $X=n^C$ to be a sufficiently large absolute multiple of $(1+\log(1/\zeta))^2$. Both effective error terms are $O(\zeta)$ with arbitrarily small implied constant. Dropping primes at most $n$ costs at most $n\log n$ in the progression weight, negligible relative to $\zeta X/\varphi(n)$. The rounding of the progression size and of the acceptance probability are also within $O(\zeta)n/(\varphi(n)\log X)$. This avoids an error from replacing logarithmic weights by prime counts when $R$ grows. The mean oracle now has a coefficient of magnitude at least $\zeta/(2\log X)$ at $f$.

List the coefficients above that threshold with constant probability. For every listed $f$ and $j\in[-K,K]$, test $\gcd(f-2j,n)$. At the desired mode, taking $j=k_i$ keeps the prime-power blocks whose coordinate equals $j$. Because $p_{\min}>4K$, every different coordinate is unequal even modulo its underlying prime. A non-diagonal mode therefore yields a proper divisor from the list. Verification and repetition give zero error. Recursion reduces the number of distinct blocks at every step. The costs are polynomial in $K,1/\zeta$, the trial cutoff and $\log n$, giving the stated bound. In particular, the reduction is expected polynomial time for $R=O(\sqrt{\log\log n/\log\log\log n})$.
