# The middle binary digit of a three-square count

For $m\equiv3\pmod8$, let $C(m)$ be the number of ordered positive representations of $m$ by three squares. Define the bit oracle

$$
B(m)=\left\lfloor C(m)/2^{\lfloor(\log_2m)/2\rfloor}\right\rfloor\bmod2.
$$

Complete factoring reduces deterministically to this bit on indices of $O(b)$ bits for a $b$-bit input. Unconditionally the arithmetic outside evaluations costs $2^{O(b/\log(2b))}$ and the query count is $\exp(O(\log^2(2b)))$. With $O(b^2)$-bit indices the [power-count lattice](ramified-power-lattice.md) gives unconditional polynomial overhead. The verified Dirichlet GRH gives polynomial overhead. Polynomially many middle-bit queries recover the entire count $C(m)$ at every input. For every fixed $\alpha>1/2$, the digit in position $\lfloor\alpha\log_2m\rfloor$ is eventually zero by the unconditional bound $C(m)/\sqrt m\ll(1+\log m)^3$ below. The [earlier reduction](ramified-three-squares.md) covers each fixed position fraction strictly below $1/2$.

## Locating a change of the digit

Write $b=\lfloor\log_2m\rfloor+1$, $C=C(m)$ and $R=C/\sqrt m$. First suppose $R>1/2$. The quantities $R$ and $2R$ are irrational because $m\equiv3\pmod8$ and $C\ge1$. Choose $K=8b+16$. For $j\ge0$ set $s_j=1+4mj^2$. Every prime divisor of $s_j$ splits for the fundamental discriminant associated to $-m$, as $-m$ is the square of $(2j)^{-1}$ modulo that prime. The Hurwitz product gives $C(ms_j^2)=s_j C$. On the indices for which $2^K\le s_j\sqrt m<2^{K+1}$ the answer is the parity of $\lfloor t_j\rfloor$, where $t_j=Cs_j/2^K$. The endpoints $j_0,j_1$ of this range can be found by integer square roots. [Hurwitz product and the norm multiplier](ramified-three-squares.md#counts-under-multiplication-by-split-primes)

The unrounded endpoints of the $t$-range are $R,2R$. On the chosen mesh $s_{j+1}-s_j\le8\,2^{K/2}m^{1/4}$ for $j\le j_1$, including the endpoint steps. Hence rounding a real endpoint to the first or last permitted $j$ changes $t$ by at most $8C m^{1/4}2^{-K/2}<1/(5m^2)$. For $v=1,2$ and an integer $z$ nearest to $vR$, the nonzero integer $(vC)^2-mz^2$ gives $|vR-z|\ge1/(m(vR+z))\ge1/(5m^2)$ since $C\le m$. Therefore the endpoint floors are exactly $\lfloor R\rfloor$ and $\lfloor 2R\rfloor$.

Use the polynomial-size upper bound $U\ge R$ derived below. Interpolate $8U+1$ equal steps in $j$ between $j_0$ and $j_1$, rounding down. A jump in the coarse mesh spans at most $j_1/(8U+1)+1$ integer steps. Since $4mj_1^2<2^{K+1}/\sqrt m$, the change of $t$ is at most $4R/(8U+1)+8C m^{1/4}2^{-K/2}<1$. Thus the number $D$ of bit transitions is exactly $\lfloor2R\rfloor-\lfloor R\rfloor$. It is positive for $R>1/2$. The only two possibilities for $\lfloor R\rfloor$ are $D,D-1$, and the first bit gives its parity. Put $J=1+\lfloor R\rfloor$.

Bisect the first coarse interval where the bit changes to find adjacent indices $j,j+1$ straddling the threshold $J$. This is a monotone binary search on that interval. Then

$$
\frac{J2^K}{s_{j+1}}\le C <\frac{J2^K}{s_j}.
$$

The width is at most $C(s_{j+1}-s_j)/s_j\le8Cm^{3/4}2^{-K/2}<1$. Taking the ceiling of the lower endpoint gives $C$ exactly. If the sweep had zero transitions, it certifies $R<1/2$. Every query has at most $2K+2$ bits. The distinguishing thresholds can be exponentially close in relative terms when determining the exact integer.

## Raising the normalized count on demand

Write $m=df^2$ with $d$ squarefree and let $\chi$ be the primitive character of $-d$. For a prime $p$ put $h=v_p(f)$ and

$$
g_h(p)=1+(1-\chi(p))\sum_{i=1}^{h}p^{-i},\qquad
R=\frac3\pi L(1,\chi)\prod_{p\mid f}g_h(p).
$$

The weighted formula includes $d=3$. The elementary bound $L(1,\chi)\le 2+\log d$ follows by summing the Dirichlet series through $d$, then by partial summation with period $d$ and zero mean. Moreover $g_h(p)\le(1-p^{-1})^{-2}$ and $\prod_{p\mid f}(1-p^{-1})^{-1}\le \zeta(2)\sigma(f)/f\le2(1+\log f)$. Thus $R\ll b^3$. A smaller explicit upper bound for the grid is

$$
U=\left\lceil 2(b+2)\prod_{p\le4b,\;p^2\mid m}g_h(p)\right\rceil.
$$

The omitted local factors have total logarithm at most $2b/(4b-1)<\log2$ for $b\ge2$. Each $h$ and $\chi(p)$ at the retained odd primes can be obtained from $m$ alone as $h=\lfloor v_p(m)/2\rfloor$ and $\chi(p)=(-m/p^{2h}\mid p)$ in Legendre notation. [Class-number formula and primitive Dirichlet character](https://reneschoof.github.io/mcpaper.pdf) · [Hurwitz local factors](https://arxiv.org/pdf/2010.14315#page=5)

For a cutoff $P$ put $F=\prod_{3\le p\le P}p$ over the odd primes. The exact rational ratio $C(mF^2)/C(m)$ is computable without factoring $m$. For each $p$ in the product use the local $h,\chi(p)$ above and multiply by $p\,g_{h+1}(p)/g_h(p)$. This also treats primes already dividing $m$, including ramified primes. Chebyshev's estimate gives $\log F=O(P)$.

At each odd $p\le P$ the normalized count at $mF^2$ includes

$$
\frac{g_{h+1}(p)}{1-\chi(p)/p}\ \ge\ \frac{1-2/p^2}{1-1/p}.
$$

For $\chi=1$ the denominator already gives the full right Euler factor before its $1-2/p^2$ correction. For $\chi=0$ use $g_{h+1}\ge1+1/p$, and for $\chi=-1$ use $g_{h+1}\ge1+2/p$. At 2 the fixed factor is $2/3$. The product of $1-2/p^2$ over odd primes is positive, and $\prod_{p\le P}(1-1/p)^{-1}\ge\sum_{j\le P}1/j$. Therefore the contribution through $P$ is at least a positive absolute constant times $\log P$. The remaining conductor factors are all at least one.

By the proved Dirichlet GRH the Euler product for $L(1,\chi)$ through $b^4$ approximates it to relative error $o(1)$ uniformly in $d\le m$. The reciprocal product over $b<p\le b^4$ is bounded below by an absolute positive constant by Mertens' estimate for the prime harmonic sum. Taking $P=b$ therefore gives $C(mF^2)/\sqrt{mF^2}\gg\log b>1/2$ for sufficiently large $b$. The sweep followed by division by the rational ratio recovers $C(m)$ with polynomial overhead on indices of $O(b)$ bits. For small inputs one may first try the original $m$, then double $P$ from $b$ until a sweep succeeds. For each fixed character its Euler product at 1 converges and the lower bound from primes through $P$ tends to infinity, so this covers every finite exception. Composing with the [two-count odd-valuation reduction](ramified-three-squares.md#polynomial-overhead-from-the-verified-dirichlet-grh) proves the polynomial factoring bound under the same hypothesis. [Schoof, Theorem 6.3](https://reneschoof.github.io/mcpaper.pdf#page=33) · [Mertens product estimates](https://arxiv.org/pdf/math/0206031#page=7)

## An unconditional family of logarithmically many twists

The [ramified factoring recursion](ramified-three-squares.md#extracting-repeated-prime-factors) permits the same squarefree twist $a$ on $an$ and $an^3$. We give a polynomial procedure that obtains both counts from the middle digit on every such cofactor, with no zero-free hypothesis. Put $b=\lfloor\log_2n\rfloor+1$. Choose the least $t$ with $H=2^t\ge 1+\log b$ and the first $t$ primes $r_i\equiv1\pmod8$. At each recursive node strip these small primes to full multiplicity together with $2,3,5,7$ before proceeding, retaining each factor. One may use the bit length before stripping for the preliminary prime list, then recompute the bit length of the remaining cofactor for the twist family. By the prime number theorem for this fixed progression, $r_t=O(t\log(2t))$ and $W=\prod_i r_i=\exp(O(t\log(2t)))=b^{o(1)}$. In particular $W<\sqrt b$ for sufficiently large $b$.

With $a_0$ the representative of $3n\bmod8$ in $\{1,3,5,7\}$, try every $a_S=a_0\prod_{i\in S} r_i$. Each twist is squarefree, coprime to $n$ and satisfies $a_Sn\equiv3\pmod8$. Put $d_S=a_S\,\mathrm{core}(n)$, where $\mathrm{core}(n)$ is the squarefree kernel. The primitive character $\chi_S$ of $-d_S$ is nonprincipal and has conductor $d_S\le n^2$ for large $n$. Both indices $a_Sn$ and $a_Sn^3$ have this same fundamental part. The factors being sought enter only in the proof.

Take $s=1+b^{-4}$, and write $g_1(p,\chi)=1+(1-\chi(p))/p$. We show that some $S$ satisfies

$$
L(1,\chi_S)\prod_{3\le p\le b}g_1(p,\chi_S)\gg\log b,
$$

with the product over primes. At $s$ instead of $1$, the local lower bound in the previous section through $b$ still gives a constant times $\log b$. Changing $p^{-1}$ to $p^{-s}$ in those Euler denominators changes their log-product by $O((s-1)\sum_{p\le b}\log(p)/(p-1))=o(1)$. For $p>b$, average the first log-Euler coefficient over all $S$. Quadratic reciprocity gives

$$
H^{-1}\sum_S\chi_S(p)=\chi_\varnothing(p)\prod_{i=1}^t\frac{1+(p/r_i)}{2}.
$$

It vanishes except on $\varphi(W)/H$ reduced classes modulo $W$. For $x\ge b$, Brun–Titchmarsh summed over those classes bounds the number of such primes up to $x$ by $O(x/(H\log x))$, using $W<\sqrt b$. Partial summation bounds their total $p^{-s}$ weight above $b$ by $O((1+\log(1/(s-1)))/H)=O(1)$. Indeed the integral reduces to $\int_{\log b}^\infty e^{-(s-1)v}dv/v$. All powers $p^{-ks}$ with $k\ge2$ have bounded total absolute weight. Thus the mean of the logarithms of the displayed products with $s$ in place of 1 is at least $\log\log b-O(1)$. Some $S$ meets the claimed lower bound at $s$. [Montgomery–Vaughan, Brun–Titchmarsh inequality](https://doi.org/10.1112/S0025579300004708)

The transfer to $1$ is elementary and uniform. For a nonprincipal character of conductor $d\le n^2$, sum through $d$ and use partial summation beyond $d$ with partial sums bounded by $d$. This gives $|L'(u,\chi)|\ll (1+\log d)^2$ for real $1\le u\le2$. The mean-value estimate for $L(1,\chi)-L(s,\chi)$ is therefore $O(b^{-2})$ in absolute value. Mertens' product bound gives $\prod_{3\le p\le b}g_1(p,\chi)\ll(\log b)^2$ uniformly. The absolute transfer error in the displayed product tends to zero, proving the lower bound. [Mertens product estimates](https://arxiv.org/pdf/math/0206031#page=7)

For this $S$, amplification by $F=\prod_{3\le p\le b}p$ makes the normalized counts at *both* indices at least a constant times $\log b$, since every such local conductor exponent is now at least one. Try the $H=O(\log b)$ candidates with the middle-bit sweep, accepting the pair when both crossings succeed. Each count is exact and the rational scaling is computable by small-prime valuations. For all sufficiently large cofactors a pair succeeds. If every candidate fails, direct trial division finishes one of the finitely many remaining inputs. All prime factors removed in preparing the library are retained in the output. The accepted $C(a_Sn)$ is $n^{1/2+o(1)}$, so the shrinking recursion from the original proof gives $\exp(O(\log^2(2b)))$ middle-bit queries total and $2^{O(b/\log(2b))}$ arithmetic overhead on all inputs. Divisor enumeration accounts for the larger arithmetic bound. All indices have $O(b)$ bits.

There is also **unconditional polynomial average bit cost** from the middle digit. Use just the accepted cubic-index count as the supplied multiple in the [average factoring reduction](ramified-three-squares.md#average-cost-with-a-single-exact-count). It is divisible by $p+1$ for every remaining original multiplicity-one prime $p$. The preparatory trial divisions and all middle-bit queries for selecting the twist have polynomial cost independent of these factors. The average splitting theorem bounds its exceptional sets uniformly in the supplied multiple, so this choice leaves the polynomial mean bound valid over uniform integers of each bit length.

This result transfers any faster all-index algorithm for $B(m)$ to deterministic factoring at the corresponding bound, up to the stated overhead. Evaluating the middle bit at the specially chosen indices of the bisection remains open here. A short Euler product alone comes with relative error, while the last threshold comparisons determine a single integer.

## Reproduction

Run `gp -fq experiments/middle-three-square-bit.gp`. The replay verifies 190 rational amplification ratios, exercising all three character values at primes already in the conductor. It recovers six exact counts from 1,916 middle-bit answers on inputs through 354 bits. The callback receives only the queried index, factors it independently, and evaluates the Hurwitz formula from the fundamental class number and local factors. On a separate semiprime test the four-member character library satisfies 290 primewise cancellation identities. For $143$ the selected twist is five and the two decoded counts are 12 and 2016, giving $11+13=24$. That integration test supplies 3,162 bits via the verified norm identity and known base counts. The asymptotic twist estimate is a paper argument. [Decoder and checks](../experiments/middle-three-square-bit.gp)
