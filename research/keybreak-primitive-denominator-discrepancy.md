# Primitive-denominator discrepancy on short squares

Let $N$ be odd, $X=\lfloor N^\alpha\rfloor$, and $T=\lfloor N^\sigma\rfloor$, where

\[
 \frac34<\alpha<1,\qquad 1-\alpha<\sigma<\frac\alpha2.
\]

Take $I=[X/8,X/4]\cap\mathbb Z$, and let $\mathcal Z$ consist of the units $z$ modulo $N$ whose least nonnegative square residues belong to $[1,X]$. For $z\in\mathcal Z$, let $A(z)$ count pairs $(h,t)$ with $h\in I$, $T\le t<2T$, $t$ odd, $(t,N)=1$, $(h,t)=1$, and $h\equiv zt\pmod N$. Define

\[
 \lambda=\frac{|I|T}{2N}\frac{\varphi(N)}N
   \prod_{p\nmid 2N}(1-p^{-2}),\qquad
 \nu=\min\left\{\frac{\sigma+\alpha-1}2,2\alpha-\frac32\right\}>0.
\]

Then

\[
 \sum_{z\in\mathcal Z}|A(z)-\lambda|
 \ll\frac{TX^2}{N}N^{-\nu+o(1)}.
\]

Also $|\mathcal Z|=X\varphi(N)/N+O(N^{1/2+o(1)})$. Since $\varphi(N)/N=N^{-o(1)}$, choosing uniformly from the counted pairs and taking $z=h/t\pmod N$ gives total variation distance at most $N^{-\nu+o(1)}$ from the uniform law on $\mathcal Z$. The statement concerns multiplicities and does not give a fast procedure for drawing the pairs.

## Quadratic completion on a linear slab

Write $e_q(x)=\exp(2\pi i x/q)$. For odd $q$, the complete sum

\[
 G_q(a,b)=\sum_{z\bmod q} e_q(az^2+bz)
\]

has magnitude at most $\sqrt{q(a,q)}$. Squaring its magnitude and changing variables to the difference between the two summation arguments leaves an inner linear sum that vanishes unless $2a$ times the difference is divisible by $q$. Exactly $(a,q)$ differences can contribute. For an interval indicator $J$ modulo $q$, use the unnormalized Fourier transform $\widehat J(k)$ and centered magnitude $|k|_q$. Then $|\widehat J(k)|\ll q/|k|_q$ for $k\ne0$, and $\sum_k|\widehat J(k)|\ll q\log(2q)$. For $0\le\theta\le1$ the divisor bound gives

\[
 \sum_{k\ne0}\frac{(k,q)^\theta}{|k|_q}
 \ll \log(2q)\sum_{d\mid q}d^{\theta-1}\le q^{o(1)}.
\]

Indeed, replace $(k,q)^\theta$ by the sum of $d^\theta$ over common divisors and sum the reciprocal multiples of $d$.

Let $\mathcal Z_0$ be the same short-square set as $\mathcal Z$ without the unit restriction. For any integer $m$ and $U\ge1$, put $g=(m,N)$ and $r=N/g$. The condition $\|mz/N\|\le1/U$ is an interval on the cyclic group of order $r$ pulled back by the unit $m/g$ when $r>1$. Its interval has at most $O(r/U+1)$ elements. Expand this interval modulo $r$ and the quadratic interval $[1,X]$ modulo $N$. The zero quadratic frequency gives $O(X/U+Xg/N)$, since the remaining condition is periodic modulo $r$. The nonzero frequencies have total absolute contribution $N^{1/2+o(1)}$. To see this, the linear interval has normalized Fourier $\ell^1$ norm $O(\log(2r))$, the complete quadratic bound is uniform in the resulting linear phase, and the quadratic frequency sum is bounded by the preceding divisor estimate with $\theta=1/2$. If $r=1$ only the zero linear frequency is used. Thus

\[
 \#\{z\in\mathcal Z_0:\|mz/N\|\le1/U\}
 \ll X\left(\frac1U+\frac gN\right)+N^{1/2+o(1)}.
\]

For the length-$K$ geometric sum $D_K(w)=\sum_{0\le k<K}e^{2\pi i k w}$, split its elementary bound $|D_K(w)|\ll\min(K,\|w\|^{-1})$ into dyadic layers. The preceding estimate yields

\[
 \sum_{z\in\mathcal Z}|D_K(mz/N)|
 \ll X\log(2K)+\frac{XK(m,N)}N+K N^{1/2+o(1)}
 \qquad(K\ge1).
\]

The first term accumulates one contribution $O(X)$ per layer. The other two terms are geometric sums ending at scale $K$. Restricting to $\mathcal Z$ only decreases this upper bound.

## Small divisors in the primitivity sieve

For $d$ prime to $2N$, write $I_d=\{h':dh'\in I\}$ and let $T_d$ be the odd units $t'$ in $[T/d,2T/d)$. A pair counted with $d\mid(h,t)$ corresponds to $h'\in I_d$, $t'\in T_d$, and $h'\equiv zt'\pmod N$. Let its number be $A_d(z)$. The zero Fourier coefficient contributes $|I_d||T_d|/N$.

To bound the other coefficients, expand the unit restriction on $t'$ over $e\mid N$ with coefficient $\mu(e)$. As $N$ and $e$ are odd, each progression of odd multiples of $e$ has step $2e$. If it is nonempty its length $K_e$ is $O(T/(de))$, since then $e\le 2T/d$. A Fourier frequency $k$ gives a geometric sum at $2ke z/N$, up to a unit-modulus phase. Its gcd factor in the preceding bound is $(2ke,N)=e(k,N/e)$. Insert that bound and sum against $|\widehat I_d(k)|/N\ll 1/|k|_N$. The $X\log(2K_e)$ term contributes $XN^{o(1)}$. For the gcd term, the divisor estimate with $\theta=1$ gives a contribution at most $(XT/(dN))N^{o(1)}$ after summing over $e$. The remaining term is $(T/d)N^{1/2+o(1)}$. Therefore

\[
 \sum_{z\in\mathcal Z}\left|A_d(z)-\frac{|I_d||T_d|}N\right|
 \ll \left(X+\frac Td\sqrt N\right)N^{o(1)}.
\]

For $d\le D_0$ the summed error is $O((D_0X+T\sqrt N)N^{o(1)})$.

The main coefficient of the truncated Möbius sum is close to $\lambda$. Indeed $|I_d|=|I|/d+O(1)$ and $|T_d|=(T/2d)\varphi(N)/N+O(\tau(N))$. Thus

\[
 \sum_{\substack{d\le D_0\\(d,2N)=1}}\frac{\mu(d)|I_d||T_d|}N
 =\lambda+O\left(\frac1N\left[\frac{|I|T}{D_0}+
 (T+|I|\tau(N))\log(2D_0)+D_0\tau(N)\right]\right).
\]

The first error uses the absolute tail of the $d^{-2}$ series. The Euler product in $\lambda$ is bounded above and below by absolute positive constants.

## Large divisors and the unit population

Fix an odd unit $t'\in[T/d,2T/d)$. Count $h'\in I_d$ for which $(h'/t')^2\pmod N$ is in $[1,X]$, dropping the extra condition that $h'$ is a unit. Expand the quadratic interval modulo $N$ and complete the sum over $h'$ by linear Fourier expansion of $I_d$. The quadratic bound and the divisor estimate above give

\[
 \#\{h'\in I_d:(h'/t')^2\bmod N\in[1,X]\}
 \ll\frac{X^2}{dN}+N^{1/2+o(1)}
 \qquad(d\le2T).
\]

For the main term use $|I_d|\ll X/d$, valid here since $T=o(X)$. This bound is uniform in $t'$ because $(k(t')^{-2},N)=(k,N)$. There are $O(T/d)$ choices for $t'$ for each contributing $d$. Summing from $d>D_0$ through $2T$ proves

\[
 \sum_{d>D_0}\sum_{z\in\mathcal Z} A_d(z)
 \ll\frac{TX^2}{ND_0}+T N^{1/2+o(1)}.
\]

Finally expand the unit restriction on $z$ over $e\mid N$. The quadratic phase on $z=es$ becomes $e_{N/e}(kes^2)$ for $s$ modulo $N/e$. Its complete magnitude for nonzero $k$ is bounded by $\sqrt{(N/e)(ke,N/e)}\le\sqrt{N(k,N)}$. The zero frequency in the resulting count is $X\varphi(N)/N$. The other frequencies contribute $O(N^{1/2+o(1)})$ by the same harmonic divisor estimate. This proves the stated unit population estimate.

Möbius inversion gives $A(z)=\sum_{(d,2N)=1}\mu(d)A_d(z)$. Choose $D_0=\lfloor N^{(\sigma+\alpha-1)/2}\rfloor$. Relative to $TX^2/N$, the small divisor error $D_0X$ and the absolute tail main term have power saving $(\sigma+\alpha-1)/2$. The Gauss-sum error $T\sqrt N$ has saving $2\alpha-3/2$. The zero-frequency remainder summed over $\mathcal Z$ fits the same bound, since $D_0<T$ and $|\mathcal Z|\ll X$. This proves the claimed discrepancy on the entire unit short-square population.
