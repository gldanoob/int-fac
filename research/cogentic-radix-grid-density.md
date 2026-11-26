# Private prime ideals on the automatic growing-degree grid

Fix a balance ratio $R>1$. Let $L=\log X$, $W=L^{1/3}(\log L)^{2/3}$ and $H=\lfloor\exp(cW)\rfloor$. For **every fixed $0<c\le1/3$**, a proportion tending to one of the balanced semiprimes $N=pq\in[X,2X]$, $p<q\le Rp$, has the following property. On the actual scheduled [raw monic pair](cogentic-monic-pair.md), **each primitive mark in each field** has odd valuation at a prime ideal private to that direction. This is simultaneous over $|a|,b\le H$, $b>0$, including $(0,1)$. All mark values and both derivatives are units modulo $N$. Consequently the entire ordinary two-field square search gives only global signs. The same statements hold for each pair on any fixed bounded-size menu of the perturbations below.

For $c<1/3$ the exceptional proportion is $\exp(-\Omega_c(W))$. At the endpoint it is $\exp(-\Omega(d\log\log L))$, where $d\sim (L/\log L)^{1/3}$. For every fixed $c>1/3$ and $\epsilon>0$, outside a proportion tending to zero the number of directions in each field lacking a private odd norm prime above $2H^2$ is at most
\[
 \exp\!\left(\left[2c-\frac{1+c}{6c}+\epsilon\right]W\right).
\]
At these larger constants a small group of surviving columns could still supply a productive relation. The estimates concern this specific field construction. [Sparse special-input obstruction](cogentic-private-grid-density.md) · [Centered quadratic result](cogentic-centered-quadratic-density.md)

## Counting all inputs in radix boxes

On each input-bit-length band, let $d$ be the scheduled degree and $m$ the largest odd integer at most $N^{1/d}$. The executable carry writes
\[
 N=m^d+2\sum_{i=0}^{d-1}c_i m^i,\qquad
 F(Z)=Z^d+2\sum_{i=0}^{d-1}c_i Z^i,\quad G(Z)=F(Z)+(Z-m)Z^d .
\]
Put $k=d-2$. The odd constant digit runs through $-m,-m+2,\ldots,m-2$. The digits $c_1,\ldots,c_k$ are in $[0,m)$, and $0\le c_{d-1}=O(d)$ follows from $m^d\le N<(m+2)^d$, since $d/m=o(1)$. For an upper bound fill the entire box of $m^{k+1}$ independent low-digit tuples for each allowed top digit, including at the clipped endpoints. The map from actual inputs to tuples is injective. For one bit-length band there are $O((2X)^{1/d}/d)$ possible odd bases, each at most $(2X)^{1/d}$. Summing the padded cardinalities costs $O(X)$; there are at most two bit-length bands. This absolute estimate preserves exponentially small exceptional fractions, including on comparison to the $\gg_R X/(\log X)^2$ balanced semiprimes given by the prime number theorem.

One may replace $F,G$ by $F+4(Z-m)P,G+4(Z-m)P$ with $\deg P\le d-2$ and $\|P\|_\infty\le\exp(CW)$ for fixed $C$. The menu may depend on the base, degree and top digit, and must be fixed independently of the low digits within each box. The pairs remain monic Eisenstein at two and evaluate to $N$ at $m$. All ensuing estimates are uniform over this choice.

## Concentration from all low digits

Fix a primitive mark $(a,b)$, set $h=\max(|a|,b)$ and $K=m h^k$. Conditional on $m$ and the top digit, the signed homogeneous norm in each field is of the form
\[
 B+2b^j T,\quad T=\sum_{i=0}^k c_i a^i b^{k-i},\qquad
 j=2\ \text{for }F,\quad j=3\ \text{for }G .
\]
Here $B$ absorbs the fixed perturbation. The interval containing $T$ has length $O(dK)$. **Each integer value of $T$ has probability $O(1/K)$.** For $h=b>1$, reduce modulo $b$ to specify the residue of $c_k$, using $\gcd(a,b)=1$. Choose that digit, subtract and divide by $b$, and repeat down to $c_1$. The remaining $c_0$ is uniquely determined. If $h=|a|>1$, start with $c_0$ modulo $|a|$ and proceed in the other direction. Counting the entire interval $[-m,m)$ for this one digit costs a factor at most $2+o(1)$. The multiplicity is at most $2(m/h+1)^k$, up to an absolute constant; $dh/m=o(1)$ uniformly. At $h=1$ one coefficient is determined by all the others, including at $a=0,b=1$ where $T=c_0$.

Let $g$ be the absolute norm with its factor of two removed. Its dyadic valuation before removal is zero for $a$ odd and exactly one for $a$ even. If an odd divisor $u$ has a common prime with $b$, divisibility is impossible by monicity and primitivity. Otherwise $u\mid g$ specifies one residue class of $T$, hence
\[
 \Pr(u\mid g)\ll d(1/u+1/K).
\]
Also $|g|\le K\exp(O_{c,C}(W))$ from the coefficient bounds, since the extra powers $h^2,h^3$ and the factor from the perturbation have this size. Small magnitudes satisfy $\Pr(g\le K e^{-MW})\ll e^{-MW}+1/K$ for any fixed $M>0$, by the atom bound and the nonzero integral slope in $T$.

## Odd valuations beyond the determinant bound

Put $y=2H^2$, take a sufficiently large fixed $M$ depending on $c$, and discard the small-magnitude event above. If $g$ has no odd valuation beyond $y$, write $g=u s^2$ with $u$ its entire $y$-smooth part. Take $D=K e^{-3MW}$. When $u<D$ we have $s>e^{MW}$ and $s\le K^{1/2}e^{O(W)}$. Summing the divisibility estimate for the odd $s^2$ costs $O(d)(e^{-MW}+K^{-1/2}e^{O(W)})$. When $u\ge D$ there is an odd smooth divisor in $[D/y,D]$, by taking prime factors with multiplicity. Summing over such divisors, the probability in this case is at most
\[
 O(d)\left[(D/y)^{-\lambda}\prod_{p\le y}(1-p^{-1+\lambda})^{-1}+D/K\right],
 \qquad \lambda=\frac{\log d+\tfrac12\log\log d}{\log y}.
\]
For completeness, Chebyshev's $\pi(t)\ll t/\log t$ and partial summation bound the logarithm of the product by $O(\log\log y+y^\lambda/(\lambda\log y))=O(\log\log y+d/\sqrt{\log d})$. Indeed the integral becomes $\int_{\log2}^{\log y} e^{\lambda v}\,dv/v$. Integrate up to $1/\lambda$ directly, then use $\int_1^A e^t\,dt/t\ll e^A/A$ for $A\ge2$.

The implemented degree is the integer cube root of $\lfloor b_0/\operatorname{bitlength}(b_0)\rfloor$ with $b_0=\operatorname{bitlength}(N)$, eventually above its floor of two. Thus $d=(L/\log L)^{1/3}(1+O(1/\log L))$, $W=d(\log L+O(1))$, and $\log m=dW(1+O(1/\log L))$. Uniformly for $t=\log h/W\in[0,c]$,
\[
 \lambda\log(D/y)
 =\frac{1+t}{6c}W+\frac{1+t}{12c}d\log\log L+O_c(d).
\]
This uses $\log d=(\log L-\log\log L)/3+O(1/\log L)$ and $\log K=dW(1+t+O(1/\log L))$. Subtracting $3MW+\log y$ from $\log K$ costs only $O_{c,M}(\log d)$ in the exponent.

Bin $\log h$ into intervals of length one; there are $O(W)$ such bins and at most $O(e^{2tW})$ marks per bin when $tW$ is its upper endpoint. The leading log of the expected number of exceptional directions is bounded by $W\max_{0\le t\le c}(2t-(1+t)/(6c))$. This affine function is strictly negative throughout for $c<1/3$. For $c=1/3$ it vanishes only at $t=c$ and the retained second term saves $\Omega(d\log\log L)$ uniformly. The discard terms are negligible upon choosing $M>2c+1+1/c$. This proves the asserted union bound. For $c>1/3$ the maximum occurs at $c$, and Markov's inequality gives the stated count after an arbitrarily small exponent allowance. In each argument summing the box weights and dividing by the semiprime lower bound only costs $O(\log L)$ in the log estimate.

## Unit tests and the square search

For a balanced semiprime, $0<|a-bm|\le H(m+1)=o(\sqrt X)$, so its mark gcd is one. Both derivatives at $m$ are independent of $c_0$. For the true digits $F'(m)\ge d m^{d-1}$, and $G'(m)=F'(m)+m^d$. The perturbation adds $4P(m)=o(m^{d-1})$. The derivatives are positive and have $O(\log X)$ bits. Freeze all the digits except $c_0$. Each derivative has $O_R(1)$ divisors that are primes of size comparable to $\sqrt X$. Each such prime divides $N$ for at most one of the $m$ constant digits, by the step-four progression. This costs $O_R(1/m)$ of the padded box.

An odd valuation of the norm at a prime $p>2H^2$ gives odd valuation at some prime ideal above $p$ in the maximal order. Its presence at two different primitive marks would imply $p\mid ab'-a'b$, whose nonzero magnitude is at most $2H^2$. This supplies a separate row for each direction, including when the prime is singular. Rational contents from nonprimitive marks of height $H$ are units at these private primes. In any tested pair, all primitive exponents in a simultaneous square are therefore even. After taking out the even powers only a common signed rational scalar remains. Squareness in the odd-degree field forces that scalar to be a rational square, by taking its norm; both field roots then reduce to the same half-product up to global sign. For arbitrary mixed libraries the private rows still force all primitive direction bits to zero field by field. Additional independent rational scalar classes in such libraries would require their own analysis.

The [finite replay](../experiments/cogentic-radix-grid-density.py) checks the exact digit fibers, both norm expansions, the multiplicity bound and admissible divisor progressions in whole small boxes. The asymptotic estimates above give the density statement.
