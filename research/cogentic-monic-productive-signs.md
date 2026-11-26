# A growing-grid obstruction to productive signs

There are infinitely many odd composite inputs for which the scheduled monic pair has unit derivatives at its common root and every simultaneous square of ordinary marks in a growing grid has a trivial sign class. Each input has at least three distinct prime factors, two of which occur to exponent one. For scheduled degree $d$, the grid includes all nonzero integer pairs $(a,b)$ with $|a|,|b|\le A=\lfloor\sqrt d/4\rfloor$. Every mark reduces to a unit modulo $N$. The conclusion allows signed products, negative exponents and nonprimitive marks.

The inputs can be chosen to have no prime divisor at most $Z=2^{\lfloor d^2/1000\rfloor}$.

## Norm valuations on primitive directions

Take arbitrarily large odd prime $d$ and plan to set $N=m^d+2$ for an odd integer $m$. Once the schedule selects $d$, the [monic construction](cogentic-monic-pair.md) gives
$$
F(X)=X^d+2,\qquad G(X)=X^d(1+X-m)+2.
$$
Indeed, $m^d\le N<(m+2)^d$ and the carry starts with the odd digit one and zero quotient. Write $\alpha,\beta$ for the respective roots.

Normalize each direction with $b\ne0$ to coprime $(a,b)$ with $b>0$. The direction $b=0$ contributes only rational scalars. For a nonzero slope $x=a/b$ the homogeneous norms are
$$
F_{\mathrm{hom}}(a,b)=a^d+2b^d,\qquad
G_{\mathrm{hom}}(a,b)=B_x-mC_x,
\quad B_x=a^d(a+b)+2b^{d+1},\quad C_x=ba^d.
$$
The unique root of the latter affine function of $m$ is
$$
M_d(x)=B_x/C_x=1+x+2x^{-d}.
$$

These roots are distinct on the nonzero grid slopes for large $d$. For $0<|x|<1$, the grid gives $|x|\le1-1/A$, so the reciprocal term puts $M_d(x)$ outside $[-A-4,A+4]$. Its sign separates the positive slopes from the negative ones. On each of these two intervals the derivative $1-2d x^{-d-1}$ is negative because $d$ is odd. For $|x|>1$, the grid gives $|x|\ge1+1/A$. Thus $M_d(x)$ is within $2(1+1/A)^{-d}$ of $1+x$. Distinct rational slopes differ by at least $1/A^2$, and $4(1+1/A)^{-d}<1/A^2$ for large $d$. At $x=1,-1$ the values are $4,-2$. A slope with $|x|>1$ either has its $1+x$ at distance at least $1/A$ from each of these values or has $x=3$ or $x=-3$. In the latter cases the reciprocal term is nonzero and prevents equality with the coinciding value of $1+x$.

Give each nonzero grid slope $x$ a separate odd prime $\lambda_x>d$. Choose the primes to avoid all nonzero cross differences $B_xC_y-B_yC_x$. Since $\lambda_x$ exceeds the grid height, it divides none of the $C_y$. Impose
$$
m\equiv B_x C_x^{-1}\pmod{\lambda_x},\qquad
B_x-mC_x\not\equiv0\pmod{\lambda_x^2}.
$$
All but one of the $\lambda_x$ lifts satisfy the second condition. Then $\lambda_x$ has rational valuation one in the $G$ norm for $x$ and zero for every other direction, including $x=0$ whose norm is $2$. The primes exceed the grid height, so they also miss the content of each mark.

Consider a relation with arbitrary integer exponents in the grid, with an optional shared sign. Factor out the rational content of each column to write the two products as $c\prod_x(a_x-b_x\alpha_i)^{n_x}$ with the same rational $c$ and exponents, where $\alpha_i=\alpha,\beta$ and the product includes $x=0$. If the second product is a field square, its rational norm is a square. The valuations at $\lambda_x$ force $n_x$ even for every nonzero slope. The valuation at two now forces $n_0$ even, since the zero slope has $G$ norm $2$ and a rational scalar contributes $(d+1)v_2(c)$, which is even.

Write $n_x=2k_x$. Squareness in the odd-degree field of $F$ forces $c$ to be a rational square. The norm of $c$ is $c^d$, which can be a rational square only if $c$ itself is a rational square. Consequently, for a rational $s$ with $s^2=c$, all roots of the two products are
$$
\pm s\prod_x(a_x-b_x\alpha_i)^{k_x}.
$$
When the marks reduce to units, the rational $s$ and any factors with negative exponents in these expressions also have unit reductions. The expressions evaluate to the same modular value up to a single global sign. The square kernel can contain relations from mark content or repeated directions, but its [sign map](cogentic-square-kernel-splitting.md) is zero.

## Fitting the congruences into the degree schedule

Let $U$ be the odd part of the integer
$$
d!\,(d^d-2)\prod_{x\ne0}|a_x^d+2b_x^d|,
$$
where the product runs through the normalized grid slopes. This is nonzero since $X^d+2$ has no rational roots. Impose $m\equiv0\pmod U$ and $m\equiv1\pmod2$. Any odd prime dividing $U$ is now coprime to $N$, since $N\equiv2$ there. In particular no prime at most $d$ divides $N$.

All nonzero grid marks have unit reductions. In fact, for a prime $p\mid N$ the content of a mark is a unit since $p>d$. For a primitive mark with $b>0$, the condition $a-bm\equiv0\pmod p$ would imply $p\mid a^d+2b^d$. All odd prime divisors of this norm belong to $U$ for nonzero $a$, and for $a=0$ the norm is $2$. The pure rational marks have no prime divisors larger than the grid height. Also $m$ is a unit modulo $N$. The derivatives at $m$ are $dm^{d-1}$ and $m^{d-1}(d+m)$. The first is a unit since $d\mid U$. If a prime divisor of $N$ divided $d+m$, it would divide $(-d)^d+2$ and therefore $U$. Both derivative gcds are one, so the [simple-root evaluation](cogentic-monic-index.md) applies to the unperturbed pair.

Select the $\lambda_x$ among primes at most $d^5$ that exceed $d$ and avoid $U$, all cross differences, and all integers $B_x^d+2C_x^d$. This last exclusion ensures $N\not\equiv0\pmod{\lambda_x}$ for the prescribed class of $m$. The integers are nonzero since $X^d+2$ has no rational root. There are at most $2A^2$ nonzero slopes. The product of the absolute exclusions has $O((dA^4+d^2A^2)\log A+d^2\log d)=O(d^3\log d)$ bits, so it rules out at most that many primes. The prime number theorem supplies enough remaining primes.

Select two further primes $p,q$ in $(Z,2Z)$ that avoid $U$ and are not $1$ modulo $d$. The interval contains asymptotically $Z/\log Z$ primes, at most $2Z/((d-1)\log(Z/d))$ of which are $1$ modulo $d$ by Brun–Titchmarsh. At most $\log_2 U$ primes divide $U$. This leaves enough choices, distinct from all $\lambda_x$ since $Z>d^5$ for large $d$. [Montgomery and Vaughan, *The large sieve*, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf)

Since $d$ is prime and $d\nmid p-1$, the map $m\mapsto m^d$ is bijective on $\mathbb F_p^\times$. Choose the residue $m^d=-2$ there and lift it modulo $p^2$ so $v_p(N)=1$. This is possible since $dm^{d-1}$ is a unit there. Do the same at $q$. These exact valuations rule out perfect powers.

The congruences specify a single class modulo
$$
T=2U p^2q^2\prod_{x\ne0}\lambda_x^2.
$$
Since $|a^d+2b^d|\le3A^d$ and $A\le\sqrt d/4$, the estimate is
$$
\log_2 T
\le2d\log_2 d+2A^2\log_2(3A^d)+O(A^2\log d+d^2)
\le(1/16+o(1))d^2\log_2 d.
$$

Let $j$ be the smallest positive integer with $d^3<2^j/j$ and set $\ell=d^3j$. Minimality gives $2^{j-1}\le\ell<2^j$, so $j$ is the bit length of $\ell$. Put $D=2^{d^2j}$. The interval
$$
\left[\left(1-\frac1{4d}\right)D,\ \left(1-\frac1{8d}\right)D\right]
$$
has length $D/(8d)>T$ for large $d$, hence contains integers $m$ in the specified class. Bernoulli's inequality gives $m^d\ge(3/4)D^d$. The upper endpoint gives $m^d\le(1-1/(8d))D^d$, so $m^d+2$ has bit length $\ell$. Its scheduled degree $\lfloor(\ell/j)^{1/3}\rfloor$ is exactly $d$. Also $N>pq$ for large $d$ since $pq<4Z^2$, so the cofactor supplies at least one more distinct prime.

## Excluding the remaining small prime factors

The progression $m=m_0+Tt$ in this interval has $K\ge\exp(2d^2\log d)$ consecutive indices for large $d$. Indeed, $j>3\log_2 d$, while $\log_2 T\le(1/16+o(1))d^2\log_2 d$. The congruences already exclude from $N$ every prime at most $Z$ dividing $T$. For a prime $r\le Z$ coprime to $T$, there are $h_r$ forbidden classes of $t$ modulo $r$, corresponding to the solutions of $m^d=-2$ modulo $r$. Since $r>d$, there is at most one such class unless $r\equiv1\pmod d$, in which case there are at most $d$. In the latter case $r\ge2d+1$ since it is odd. Thus each density $e_r=h_r/r$ is at most $1/2$.

Write $S=\sum_r e_r$. The ordinary reciprocal prime sum through $Z$ is at most $2\log\log Z+O(1)$ by partial summation and the prime number theorem. The additional contribution from primes $r\equiv1\pmod d$ with $r\le d^2$ is at most $d\sum_{k=1}^d 1/(kd+1)\le1+\log d$. For $t\ge d^2$, Brun–Titchmarsh gives $d\pi(t;d,1)\le6t/\log t$. Partial summation then bounds the additional contribution from $d^2<r\le Z$ by $6\log\log Z+O(1)$. Since $\log\log Z\le2\log d$ for large $d$, these estimates give $S\le20\log d$.

For any set of these primes, the number of indices forbidden at every prime in the set is $K$ times the product of their densities, with error at most the product of the corresponding $h_r$. This follows by counting each CRT class in a consecutive interval. Apply inclusion-exclusion through the smallest odd integer $J\ge20(S+1)$, which gives a lower bound on the count avoiding every forbidden class. For sufficiently large $d$, $J\le410\log d$. The total rounding error through order $J$ is at most
\[
\sum_{k\le J}(dZ)^k\ <\ \exp\bigl(\tfrac12 d^2\log d\bigr),
\]
using $\log Z\le(d^2/1000)\log 2$. The full density product is at least $\exp(-2S)$ because $e_r\le1/2$. The discarded density terms have absolute sum at most $\sum_{k>J}S^k/k!$. For $k>J$, the factorial bound $k!\ge(k/e)^k$ gives $S^k/k!\le(e/20)^k$, so the tail is less than $\tfrac12\exp(-2S)$. The count of indices avoiding every small prime is therefore at least
\[
\tfrac12 K\exp(-2S)-\exp\bigl(\tfrac12 d^2\log d\bigr)>0
\]
for large $d$. Choosing one of these indices completes the construction for arbitrarily large odd prime $d$.

## Scope and replay

The argument applies to all subsets of this grid, including pools filtered by smoothness, admissible roots or discriminant coprimality. It uses no assertions about the distribution of simultaneous smooth norms. Local tests that a common value is a square at primes dividing $N$ do not determine which of the two local roots a given global field root reduces to. Here the exact field-square identities force those choices to agree everywhere up to a global sign.

The construction prescribes two divisors between $Z$ and $2Z$ and proves existence within the final progression by counting. Since $W\asymp d\log d$, it even excludes trial divisors through $\exp(cW)$ for every fixed $c>0$ and sufficiently large $d$. The grid, however, has $\log A=O(\log d)$, far below $\log A=cW$. The method assigns a distinct prime greater than $A$ to each of $\Theta(A^2)$ slopes. Those prime powers alone give a modulus of bit length $\Omega(A^2\log A)$, while the interval for $m$ has bit length $O(d^2\log d)$. The interval-length guarantee cannot reach the one-third height. The obstruction applies to ordinary marks, so added unit corrections require separate analysis.

Run `python3 -B experiments/cogentic-monic-productive-signs.py` to verify a finite instance with scheduled degree five and grid height two. The replay verifies the exact pair, each isolated norm valuation, all bounded mark residues, both derivative residues, two exact prime valuations of $N$, absence of prime divisors through the fixture cutoff of 80, and a three-column square relation whose roots give only trivial gcds. [Replay](../experiments/cogentic-monic-productive-signs.py)
