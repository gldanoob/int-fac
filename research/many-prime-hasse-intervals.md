# More odd smooth orders in central Hasse intervals

For each fixed $2/3<\alpha<1$, set $L=\log X$, $Y=\exp(L^\alpha)$ and $V=\exp(1000 L\log L/\log Y)$. For all but $O(X/V^4)$ primes $X<p\le2X$ the interval $|n-(p+1)|\le\sqrt p$ contains at least $\sqrt X/V$ integers $n=4m$ with $m$ odd and $Y$-smooth. This uses the classical Vinogradov–Korobov zero-free region. In the moving Legendre-curve algorithm it gives deterministic $\exp(O_\alpha(b^\alpha))$ time on a density-one set of balanced semiprimes of bit length $b$. The stronger square-root-exponent conclusion in the other proof uses a fixed zero-free half-plane. [Factoring algorithm](legendre-average-factoring.md) · [Single-prime interval argument](odd-smooth-hasse.md) · [Ford on the classical zero-free region](https://arxiv.org/abs/1910.08205)

Jain's Theorem 1.1 obtains a smooth number in almost all much shorter unconditioned intervals at this smoothness scale, with sharper dependence on the Dickman function. His argument uses several prime factors of comparable size to strengthen a Dirichlet-polynomial estimate. Here the required interval length is proportional to $\sqrt X$. This permits a direct many-prime convolution, forces the exact 2-adic valuation of the order, and bounds the exceptional prime count. Friedlander–Lagarias and Lenstra–Pomerance studied smoothness in Hasse intervals for randomized ECM. [Jain, Theorem 1.1 and equations (4.7)–(4.9)](https://arxiv.org/pdf/2502.10530) · [Friedlander and Lagarias](https://websites.umich.edu/~lagarias/doc/short.pdf) · [Lenstra and Pomerance, §7](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/rigorous.pdf#page=22)

## Short convolution and its long average

Put $T=X/4$, $J=\lfloor L/(5\log Y)\rfloor$ and $z_0=Y/2$. We consider large $X$ so $J\ge2$. Let $Z=3T/(Yz_0^{J-1})=X^{4/5+o(1)}$. There is a set $\mathcal M$ of distinct odd $Y$-smooth numbers in $[Z,1.11Z]$ with
$$
                         V^{-1/50}\le \sum_{m\in\mathcal M}1/m\ll 1 .
$$
Indeed take $k=\lceil\log Z/\log(Y/2)\rceil$, $z=Z^{1/k}$, and choose $k$ distinct primes of $(z,z(1+1/(10k))]$. Here $Y^{1/2}<z\le Y/2$ eventually and $k\le2L/\log Y$. The prime number theorem with its classical error gives at least $z/(30k\log z)$ choices per slot before requiring distinctness. Different unordered subsets give different products. The binomial lower bound $(z/(30k^2\log z))^k$ has logarithm at least $\log Z-8 L\log L/\log Y$. Each product is at most $Z e^{1/10}<1.11Z$, which proves the claim for large $X$.

Choose a fixed smooth $0\le W\le1$ supported in $(1/6,5/6)$ and equal to one on $[1/4,7/10]$. Give each $m\in\mathcal M$ and ordered $J$-tuple of primes $r_i$ weight
$$
  m^{-1}\prod_{i=1}^J (\log r_i)W(r_i/Y)/r_i
$$
at the logarithm of $s=m\prod_i r_i$, forming a positive measure $\mu$. Its Fourier transform is $D(t)P(t)^J$ with $D(t)=\sum_{m\in\mathcal M}m^{-1-it}$ and $P(t)=\sum_{r\,\mathrm{prime}}(\log r) W(r/Y)r^{-1-it}$. All supported $s$ are odd and $Y$-smooth. The total mass is at most $O(1)^{J+1}=V^{o(1)}$ by partial summation.

Take a fixed smooth nonnegative integral-one kernel supported in $[-1,1]$ and positive on $[-1/2,1/2]$. Write $K_w(z)=K(z/w)/w$, $\eta=V^{-16}$ and $h=1/(100\sqrt X)$. Uniformly at $x\in[T,2T]$ we have
$$
                         (\mu*K_\eta)(\log x)\ge V^{-1/10}.
$$
Restrict any $J-1$ of the primes to $[z_0,z_0(1+1/(10J))]$, with repetitions allowed. Their total single-slot weight is $\gg1/J$. For each such tuple and allowed $m$, the remaining prime is centered at $y'=x/(m\prod_{i<J}r_i)$. Its range is contained in $[(3\,1.11 e^{1/10})^{-1}Y,2Y/3]$, in the interior of the range where $W=1$. A relative window of width $\eta/4$ there has prime weight $\gg\eta$. Indeed the classical prime number theorem error $O(Y\exp(-c\sqrt{\log Y}))$ is $o(\eta Y)$ when $\alpha>2/3$. The kernel contributes $\gg1/\eta$ on that window. The losses from $(c/J)^{J-1}$ and the cofactor mass together are smaller than the chosen exponent $1/10$ in $V$.

## Why repeating the prime factor helps

For $V^4\le |t|\le X^2$, the smoothed explicit formula and the Vinogradov–Korobov region give, for a constant $c>0$ and any fixed $a\ge2$,
$$
 |P(t)|\ll_a |t|^{-a}
   +L\exp\!\left(-\frac{c\log Y}{L^{2/3}(\log L)^{1/3}}\right)
   +Y^{-1/2}\log^2Y .
$$
The first term is the pole term. The transform of $W$ has arbitrarily fast power decay in $|\operatorname{Im}\rho-t|$ for each nontrivial zero $\rho$, and unit zero-counting intervals contain $O(\log(2+|\operatorname{Im}\rho|))$ zeros. The zeros beyond height $2X^2+1$ contribute a negligible inverse power of $X$. The final term bounds the replacement of prime powers by primes. This is the same explicit formula used in the single-prime estimate. [Smoothed explicit formula, chapter 7](https://people.maths.ox.ac.uk/greenbj/papers/primenumbers.pdf) · [Vinogradov–Korobov region](https://arxiv.org/abs/1910.08205)

In the middle term the magnitude of the negative exponent dominates $\log L$ because $\alpha>2/3$. Multiplying that exponent by $J$ gives a saving $\gg L^{1/3}/(\log L)^{1/3}$, which dominates $\log V=1000 L^{1-\alpha}\log L$. The first and last terms raised to the $J$th power also save more than $V^{-8}$, including the fixed implied constants. Hence $|P(t)|^J\ll V^{-8}$ throughout the indicated range.

By Plancherel,
$$
  \int_{\mathbb R}|\mu*K_h-\mu*K_\eta|^2\ll V^{-12}.
$$
For $|t|\le V^4$ the kernel-transform difference is $O(\eta |t|)$. Integrating and using the total mass costs at most $V^{o(1)}\eta^2 V^{12}$. For $V^4\le |t|\le Z$ use $|P(t)|^J\ll V^{-8}$ and the mean-value theorem $\int_{-Z}^Z|D(t)|^2dt\ll Z\sum_{m\in\mathcal M}m^{-2}\ll1$. For $|t|>Z$ smooth-transform decay bounds the tail by $V^{o(1)} h^{-8}Z^{-7}=X^{-8/5+o(1)}$. [Montgomery–Vaughan mean value theorem](https://doi.org/10.1112/jlms/s2-8.1.73)

Outside logarithmic measure $O(V^{-11})$, the short convolution is therefore at least $V^{-1/10}/2$. For $s\asymp X$ the number of choices for a prime $r_i\in(Y/6,5Y/6)$ dividing $s$ is $O(L/\log Y)$. Each ordered choice of $J$ such primes determines the unique residual $m$. The total weight at any single $s$ is at most $X^{-1}(C L)^J\le X^{-1}V^{1/100}$ for large $X$. A good center thus contains more than $\sqrt X/V$ distinct products in its logarithmic $h$-window. For each prime $p$ consider $|(p+1)/4-x|\le1/16$, ignoring $O(1)$ endpoints. These real intervals are disjoint and each has logarithmic measure $\gg1/X$. Any good center within it puts all its products $s$ inside $|4s-(p+1)|\le\sqrt p$. The number of primes without a good center is $O(XV^{-11})$, stronger than claimed.

The same argument allows $\log Y=C L^{2/3}(\log L)^{4/3}$ for a sufficiently large absolute $C$. Indeed the one-prime zero-free saving then has magnitude $cC\log L$ before the factor $L$. After $J$ repetitions it saves $\gg L^{1/3}/(\log L)^{1/3}$, whereas $\log V=(1000/C)L^{1/3}/(\log L)^{1/3}$. A sufficiently large $C$ also ensures the long-window prime estimate. All these bounds are asymptotic.

For a finite check of the repeated-prime measure, the replay enumerates both ordered tuples and their successive product convolutions, verifies each atom's multiplicity bound, and compares 528 exact central-window counts against literal integer squares. [Prime-slot replay](../experiments/mean-time-ecm.py)
