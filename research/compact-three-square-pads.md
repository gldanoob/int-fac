# Shorter inputs for exact middle-bit inversion

Let $m\equiv3\bmod8$ have $b$ bits, let $C(m)$ count the ordered positive three-square representations, and put $R=C(m)/\sqrt m$. When $R>1/2$, a deterministic polynomial-time decoder recovers $C(m)$ using middle digits on indices with **at most $3b+O(\log b)$ bits**. At every $m$, including arbitrarily small normalized counts, the corresponding bound is

$$
                        3b+\exp(O(\sqrt{\log(2b)})).
$$

These lengths include the conductor multiplier used to expose a small count. There are infinitely many inputs which require an added $\exp(\Omega(\sqrt{\log b}))$ bits in the procedure that first raises $R$ above $1/2$ by a conductor multiplier and then uses the primitive norms below. The results on arbitrary bases and small inert markers use Alpöge’s Dirichlet GRH theorem for characters over $\mathbb Q$. [Theorem announcement](https://alpo.ge/remark.pdf) · [Sutherland’s independently checked statements](https://math.mit.edu/~drew/grh/)

## Primitive norms and two consecutive crossings

Put

$$
 K=\lceil3b/2\rceil+2\,\mathrm{bits}((b+2)^{12})+8,\quad
 s(x)=x^2+4m,\quad
 2^K\le s(x)\sqrt m<2^{K+1},\quad x>0,\quad (x,2m)=1 .
$$

Every prime $r\mid s(x)$ is odd, coprime to $m$, and satisfies $-m\equiv (x/2)^2\bmod r$. Thus $C(ms(x)^2)=s(x)C(m)$ exactly. The middle digit at this index is the parity of the floor of $t(x)=C(m)s(x)/2^K$. All indices have at most $2K+2=3b+O(\log b)$ bits. On the real interval before the coprimality filter, $x$ and the length of its interval are both comparable to $L_0=\sqrt m\,(b+2)^{12}$. Consecutive integers coprime to $2m$ have gaps at most $G\ll b^2\log^2(2b)$ by Iwaniec’s bound for arbitrary prime divisors. The first and last allowed $x$ and a nearest allowed integer to any interior position can be found by square roots and $O(G)$ gcd checks. [Hurwitz product](ramified-three-squares.md#counts-under-multiplication-by-split-primes) · [Iwaniec, *On the problem of Jacobsthal*](https://doi.org/10.1515/DEMA-1978-0121)

Use the explicit polynomial upper bound $U\ge R$ of the [original decoder](middle-three-square-bit.md#raising-the-normalized-count-on-demand), with $U=O(b^3)$. On $16U+1$ equally spaced intervals in $x$, round an interior endpoint to the next allowed integer, clipped to the last permitted value. Each resulting increment of $t$ is less than one for large $b$, by $s'(x)=2x$, $x_{\max}^2\le2^{K+1}/\sqrt m$, and $G/L_0=o(1/U)$. Thus every observed parity change represents one integer crossing, in order. Bisect a changing interval by the nearest allowed integers to bracket the crossing between adjacent allowed norms. The final bracket width in the norm coordinate is $O(G L_0)$. All searches and queries cost polynomial overhead. For any bounded initial range of $b$ one may count triples directly.

If two consecutive crossings have norm brackets $[s_1^-,s_1^+]$ and $[s_2^-,s_2^+]$, their true norm coordinates differ by $2^K/C(m)$. The integer $C(m)$ therefore lies between $2^K/(s_2^+-s_1^-)$ and $2^K/(s_2^--s_1^+)$. This interval has width

$$
 O\!\left(\frac{C(m)^2 G L_0}{2^K}\right)
 =O\!\left(\frac{U^2G}{(b+2)^{12}}\right)<1
$$

for large $b$. In particular $R\ge3$ guarantees two observed crossings since endpoint rounding changes $t$ by at most $\delta=O(UG/L_0)$. No label for the first crossing is needed.

## Counts just above one half

A real endpoint $R$ or $2R$ can be exceptionally close to an integer. If both endpoint distances exceed $\delta$, the endpoint floors equal $\lfloor R\rfloor$ and $\lfloor2R\rfloor$. For $R>1/2$ there is then a crossing. If there is just one, $\lfloor R\rfloor$ is zero or one and its parity is the initial bit. Thus the crossing label $J$ equals one or two respectively. The bracketing formula $J2^K/s^+\le C(m)<J2^K/s^-$ has width $O(UG/(b+2)^{12})<1$. In a one-crossing scan use this candidate when integral rounding is unique. A scan with no crossings abstains.

For three distinct endpoint placements, use $m$ and $mp_i^2$ for two distinct primes $p_1,p_2\in[b^8,2b^8]$ with $(-m/p_i)=-1$. Trial the primes directly. The quadratic prime sum at this length has error $O(\sqrt{b^8}\log^2(2mb^8))=o(b^8)$ by the Dirichlet GRH explicit formula. Removing primes dividing $m$ costs $O(b)$ in logarithmic weight. Hence two suitable primes exist for all sufficiently large $b$. Their exact count multipliers are $p_i+2$, and the normalized multipliers are $\kappa_i=1+2/p_i$. Set $\kappa_0=1$. [Quadratic local factor](ramified-three-squares.md) · [Smoothed explicit formula](https://people.maths.ox.ac.uk/greenbj/papers/primenumbers.pdf)

If an endpoint is within its mesh error of an integer, $2\kappa_iR$ is within twice that error of an integer. The three values $2\kappa_iR$ lie in an interval of width $O(U/b^8)<1/4$. For $R\ge1/4$ they have pairwise spacing $\gg b^{-16}$, while all three endpoint errors are $O(\operatorname{poly}(b)/\sqrt m)$. Consequently at most one scan has an endpoint problem. Divide each returned count by its known multiplier and accept a positive integer only if it occurs twice. For $R>1/2$ at least two scans give the true integer. Below this promise a good scan either abstains or gives the true integer, and for $R<1/4$ all scans abstain at large $b$. The two additional prime squares add only $O(\log b)$ to the lengths.

## The cost of raising a small count

Write $m=df^2$ with $d$ squarefree. Take $F=\prod_{3\le p\le P}p$ over primes and evaluate the count at $u=mF^2$. The exact ratio $C(u)/C(m)$ is calculated using small prime valuations, including $p\mid f$ and $p\mid d$. The original local calculation shows that all Euler and conductor factors through $P$ in $C(u)/\sqrt u$ contribute $\gg\log P$. Dirichlet GRH approximates the primitive $L(1,\chi_{-d})$ by its Euler product through $b^4$ with uniform relative error $o(1)$. Every remaining conductor factor is at least one. The Euler factors from $P$ to $b^4$ contribute at least $\prod_{P<p\le b^4}(1+1/p)^{-1}\gg\log P/\log b$ for $2\le P\le b^4$. Hence

$$
                     \frac{C(u)}{\sqrt u}\gg\frac{(\log P)^2}{\log b}.
$$

Choosing $P=\lceil\exp(A\sqrt{\log(2b)})\rceil$ with a sufficiently large absolute $A$ ensures $C(u)/\sqrt u\ge3$ for all large $b$. Now $\log F=O(P)$, so the two-crossing scan at $u$ proves the all-base length bound. Its bit overhead, including generating $F$, remains polynomial in $b$. A finite initial range can again use direct counting. [Exact amplification formula and single-character estimate](middle-three-square-bit.md#raising-the-normalized-count-on-demand) · [Mertens products](https://arxiv.org/pdf/math/0206031#page=7)

For a converse let $y$ grow, set $Q=8\prod_{3\le p\le y}p$ over primes, and choose by CRT a reduced class $a\bmod Q$ with $a\equiv3\bmod8$ and $(-a/p)=-1$ at all the odd primes in the product. There is a squarefree $d=a+kQ$ with $Q^3/2<k\le Q^3$. If the number of $k$ is $H$, at most $H\sum_{r\ge2}r^{-2}+O(Q^2)$ of these terms can be divisible by a prime square. Primes dividing $Q$ divide no term, and a prime whose square divides a term has size $O(Q^2)$. Since the series is less than one, such a $d$ exists for large $y$. Its bit length $b\asymp y$. The short Euler product for this character is $O(1/\log b)$ since all odd primes through $y$ are inert and the remaining range through $b^4$ contributes $O(1)$. Thus $C(d)/\sqrt d\ll1/\log b$.

For an arbitrary integer conductor multiplier $F$ yielding a supported odd input, the normalized local gain is at most $\prod_{p\mid F}(1-1/p)^{-2}\ll(1+\log\log(3F))^2$. This follows by Mertens through $\log(3F)$ and bounding the remaining prime harmonic sum by an absolute constant. Therefore reaching $1/2$ on these $d$ requires $\log F\ge\exp(c\sqrt{\log b})$ for some absolute $c>0$. Since $s(x)\ge4dF^2$ in the primitive-norm sweep, its index length is at least $3b+6\log_2 F-O(1)$. This lower bound concerns amplification by conductor squares followed by these primitive norms.

## Direct evaluation on full compact pad intervals

At $u=dn^2$ with squarefree $d\le b^D$, choose $x$ uniformly over the allowed integers in the compact dyad. The [exact direct evaluator](fixed-discriminant-middle-digits.md) still has root-mean-square cost $2^{t/2}\operatorname{poly}(b)$ for the quotient $t$ positions below the middle. Its input is $M=us(x)^2$, $d$ and $t$. The raw interval has $\asymp L_0$ integer positions, and its allowed subset has size $\gg L_0/G$. An obstruction interval of normalized width $O(b/Y)$ at extraction cutoff $Y$ therefore contains proportion $O(G(b/Y+1/L_0))$ of allowed points. Multiply by the $O(2^tR+1)$ possible thresholds. At an eligible $k$, invert the strictly increasing public function $K(b_0)$ to recover the candidate outer bit length $b_0$. Strip primes through $H=\lfloor\sqrt{(2^{b_0}-1)/d}\rfloor$ and try divisors $n'$ of the known part. The witness $M=df^2$, $f/n'=x^2+4d(n')^2$, $\gcd(x,2d(n')^2)=1$ and $\mathrm{bits}(d(n')^2)=b_0$ certifies the exact count from the known local factors of $n'$. Every actual compact pad has such a witness, with $H<\sqrt2\,n$. The trial-and-certify proof charges the final grid endpoint term by $2^t\operatorname{poly}(b)H/L_0$, which is covered since $H\le\sqrt u$. On other eligible ordinary inputs the extra candidate search costs $\tau(f)\operatorname{poly}(b)\ll\sqrt H\operatorname{poly}(b)$ because $H=f^{1/3+o(1)}$. This mean bound covers the full allowed interval at each fixed $n$.

The middle-bit replay independently factors the indices for 1,292 digit answers on five bases, with peak length 184 bits. It also checks the two-crossing recovery on a 230-bit amplified index and five endpoint stress tests on artificial integer counts at $m=(9(2^{169}+1))^2+2$. The three-scan procedure corrected two failures of the unperturbed scan. The amplified and synthetic tests used 190,344 exact norm-transfer answers through 1,886 bits. Seven prescribed-character progressions and 28 inert local gains independently checked the small-prime construction. The independent direct evaluator checked all 384 further compact-pad quotients through 328 bits, including 128 full counts and 204 successful concealed-conductor certificates. [Inversion replay](../experiments/middle-three-square-bit.gp) · [Direct evaluator replay](../experiments/fixed-discriminant-middle-digits.gp)
