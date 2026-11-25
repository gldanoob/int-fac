# Odd smooth numbers in almost all central Hasse intervals

Let $X\to\infty$, $L=\log X$ and let $Y$ be one of the two cutoffs below. For all but $o(X/\log X)$ primes $p\in(X,2X]$, the interval $|n-(p+1)|\le\sqrt p$ contains at least $\sqrt X/V^2$ distinct integers $n=4m$ with $m$ odd and $Y$-smooth, where

$$V=\exp(16L\log L/\log Y).$$

1. For fixed $0<\epsilon<1/6$, one can take $Y=\exp(L^{5/6+\epsilon})$ using the classical Vinogradov–Korobov zero-free region.
2. If $\zeta(s)$ has no nontrivial zeros in $\Re s>1-\delta$ for some fixed $\delta>0$, one can take $Y=\exp(C_\delta\sqrt{L\log L})$ with a sufficiently large constant. Ordinary RH supplies $\delta=1/2$. A fixed zero-free strip for $\zeta$ alone suffices for this statement. [Ford, explicit Vinogradov–Korobov region](https://arxiv.org/abs/1910.08205) · [Recent Dedekind strip, Theorem 1.1](https://hexagonmath.org/pdf/2610.00200v2#page=3) · [Alpöge, November 20 statement](https://alpo.ge/remark.pdf) · [Sutherland, exact statements independently checked](https://math.mit.edu/~drew/grh/)

Friedlander–Lagarias and Lenstra–Pomerance use a density-one smoothness property of central Hasse intervals in their analysis of randomized ECM. The proof below specifies the $2$-adic valuation of the candidate orders. In particular every candidate has valuation exactly two. [Lenstra–Pomerance, §7](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/rigorous.pdf#page=19)

## A convolution of odd primes and smooth cofactors

Set $T=X/4$. Construct distinct odd smooth integers $m$ in $[3T/Y,4T/Y]$ with total reciprocal mass at least $V^{-1/2}$ up to an absolute factor. Let $k=\lceil\log(3T/Y)/\log(Y/2)\rceil$ and $z=(3T/Y)^{1/k}$. For large $X$ we have $Y^{1/2}<z\le Y/2$ and $k\le2L/\log Y$. The interval $(z,z(1+1/(10k))]$ contains at least $z/(30k\log z)$ primes by the prime number theorem with its classical error term. Every product of $k$ distinct such primes lies in $[3T/Y,4T/Y]$. If $P$ is the number of available primes then

$$\binom Pk\ge (P/k)^k\ge (3T/Y)(30k^2\log z)^{-k}\ge(3T/Y)V^{-1/2}.$$

The last inequality uses $\log(30k^2\log z)\le4\log L$. Denote this set of products by $\mathcal M$. It supplies the required lower mass and its reciprocal mass is also $O(1)$.

Choose a fixed smooth, nonnegative function $W$ compactly supported in $(1/5,4/5)$ and equal to one on a neighborhood of $[1/4,2/3]$. Define a positive measure on the real line of logarithms by

$$\mu=\sum_{m\in\mathcal M}\sum_{r\ {\rm prime}}\frac{(\log r)W(r/Y)}{rm}\,\delta_{\log(rm)}.$$

All products $rm$ are odd and $Y$-smooth. Its Fourier transform, with the phase $e^{-itx}$, factors as $P(t)D(t)$, where $P(t)=\sum_r(\log r)W(r/Y)r^{-1-it}$ and $D(t)=\sum_{m\in\mathcal M}m^{-1-it}$. Both are bounded by an absolute constant. We use

$$|P(t)|\ll V^{-6}\quad\text{for}\quad V^4\le |t|\le X^2.$$

Apply the smoothed prime explicit formula first to the von Mangoldt sum. Its pole term is $Y^{-it}\widehat W(-it)$, with $\widehat W(s)=\int W(u)u^{s-1}\,du$. The terms from nontrivial zeros $\rho=\beta+i\gamma$ have absolute value $\ll_j Y^{\beta-1}(1+|\gamma-t|)^{-j}$ for any fixed $j$. The trivial zeros contribute $O(1/Y)$, and replacing prime powers by primes costs $O(Y^{-1/2}\log^2Y)$. Zeros in each interval $[w,w+1]$ number $O(\log(2+|w|))$. The zeros with $|\gamma|>2X^2+1$ have negligible total contribution by the decay, taking $j$ sufficiently large. Under a fixed strip the remaining zero terms give $O(L Y^{-\delta})$. Choose $C_\delta$ sufficiently large that this and the prime-power error are $O(V^{-7})$. In the classical case they give $O(L\exp(-c\log Y/(L^{2/3}(\log L)^{1/3})))$, which is $O(V^{-7})$ since $5/6+\epsilon>5/6$. The pole term is $O(V^{-8})$ in the indicated range. [Smoothed explicit formula, Chapter 7](https://people.maths.ox.ac.uk/greenbj/papers/primenumbers.pdf) · [Ford's zero-free region](https://arxiv.org/abs/1910.08205)

## Passing from a long average to the central interval

Let $K$ be a smooth nonnegative bump of integral one supported in $[-1,1]$ and positive on $[-1/2,1/2]$. Write $K_w(v)=K(v/w)/w$. Take $\eta=V^{-12}$ and $h=1/(100\sqrt X)$. Uniformly for $x\in[T,2T]$,

$$(\mu*K_\eta)(\log x)\gg V^{-1/2}.$$

Indeed for each $m$ the prime interval centered on $x/m$ of relative width $\eta/4$ lies where $W=1$ and contains weighted prime mass $\gg\eta$. With the fixed strip use $\vartheta(w)=w+O_\delta(w^{1-\delta/2}\log^2(2w))$, which follows from the truncated prime explicit formula. Increasing $C_\delta$ makes this error $o(Y\eta)$ at $w\asymp Y$. With the classical cutoff even the de la Vallée Poussin error $O(Y\exp(-c\sqrt{\log Y}))$ is $o(Y\eta)$. Summing the resulting lower bound over the cofactors proves the assertion. The same proof works if $x$ differs from either endpoint by at most one, by the chosen neighborhood for $W$.

Plancherel gives

$$\int_{\mathbb R}|\mu*K_h-\mu*K_\eta|^2\ll V^{-12}+X^{-2}.$$

For $|t|\le V^4$ we have $|\widehat K(ht)-\widehat K(\eta t)|\ll\eta |t|$. The integral over this range is $O(\eta^2 V^{12})=O(V^{-12})$. From $V^4$ to $T/Y$, the prime bound gives $|P|^2\ll V^{-12}$ and the Dirichlet-polynomial mean value theorem gives

$$\int_{-T/Y}^{T/Y}|D(t)|^2\,dt\ll(T/Y)\sum_{m\in\mathcal M}m^{-2}\ll1.$$

Above $T/Y$ bound $P,D$ trivially and use $|\widehat K(ht)|+|\widehat K(\eta t)|\ll(h|t|)^{-4}$. This tail contributes $O(h^{-8}(T/Y)^{-7})=X^{-3+o(1)}$. Both cutoffs satisfy $Y=X^{o(1)}$. [Montgomery–Vaughan mean-value theorem](https://doi.org/10.1112/jlms/s2-8.1.73)

It follows that outside a subset of logarithmic measure $O(V^{-11})$ in $[\log T,\log(2T)]$ the short convolution is $\gg V^{-1/2}$. One product $s=rm$ has at most $O(L/\log Y)$ representations in the measure because the prime $r\asymp Y$ divides $s$. Thus its coefficient is $O(L/X)$. Since $\|K_h\|_\infty\ll1/h$, a good center contains $\gg\sqrt X/(V^{1/2} L)$ different products in $|\log(s/x)|\le h$.

To pass to primes, use the real interval $|x-(p+1)/4|\le1/16$ for each $X<p\le2X$, discarding $O(1)$ boundary cases. These intervals are disjoint and have logarithmic measure $\gg1/X$ apiece. Any one good center in such an interval gives the displayed candidate count with $n=4s$ and $|n-(p+1)|\le\sqrt p$. Since $V$ grows faster than every power of $L$, this exceeds $\sqrt X/V^2$ for large $X$. The number of primes with no such center is $O(XV^{-11})=o(X/\log X)$. This proves the stated prime exception bound without a short-interval prime theorem at the scale of the Hasse interval.
