# Polynomial overhead for three-square count queries

Let $C(d,n)$ count the ordered positive triples with $x^2+y^2+z^2=dn^2$, for odd $n$ and squarefree $d\equiv3\bmod8$ coprime to $n$. For a $b$-bit input, complete deterministic factorization reduces to the following two counting problems. The bounds use Dirichlet GRH for primes in specified cosets. [GRH verification](https://math.mit.edu/~drew/grh/) · [Lamzouri–Li–Soundararajan, Theorem 1.4](https://arxiv.org/pdf/1309.3595#page=3)

| Oracle returns | Twists on a cofactor $n$ | Total bit cost for input $N$ |
| --- | --- | --- |
| Lowest $\lceil b_n/4\rceil+1$ bits of $C(d,n)$, $b_n$ the cofactor bit length | Prime twists, or $3$ times at most four distinct primes $1\bmod8$, each $O(b_n^2)$ | $\operatorname{poly}(b)(1+Q)$ |
| $C(\ell,n)\bmod r$ for a requested odd prime $r=O(b_n)$ | Prime $\ell\equiv3\bmod8$, $\ell=O(b_n^2)$ | $\operatorname{poly}(b)(1+Q)$ |

Here $Q$ bounds a single requested evaluation. Both rows have largest index of bit length $2b+O(\log b)$. The first row takes $O(b_n^2/\log(2b_n))$ large count queries per cofactor by the walk construction below. The second uses $O(\log b)$ bits per answer and varies the output modulus. On these promised prime twists, a factorization of $n$ also evaluates the count in polynomial time by the product below. The [earlier prime-only quarter-bit reduction](hurwitz-residues.md#one-large-index-and-quarter-bit-precision-suffice) had $2^{O(\sqrt b)}$ overhead on unrestricted inputs. Computing the requested residues fast enough to improve the factoring record remains open.

## A gcd for every mixed twist

Strip primes through $8b$ by trial division. On each remaining cofactor test primality and replace a perfect power by its base, carrying the multiplicity. Thus a cofactor that still needs a split has at least two distinct odd prime divisors. The count is $C(d,n)=3H(dn^2)$, and $B_d=C(d,1)$ is computable in polynomial time by enumerating reduced forms at our polynomial-size $d$. For every $p^e\parallel n$ put
$$
w_p=1+2\sum_{j=1}^e p^{-j}
=1+\frac{2(1-p^{-e})}{p-1}.
$$
Writing $R_d=C(d,n)/B_d$, the Hurwitz formula makes $R_d$ an odd integer and gives
$$
R_d/n=\prod_{p\mid n,\;(-d/p)=-1} w_p.
$$
Every subproduct of the $w_p$ is less than $\exp(2\omega(n)/(8b))\le e^{1/4}<2$. Every nonempty subproduct exceeds one. Thus any twist with an inert prime has $n<R_d<2n$. Every split prime power divides $R_d$. A twist with both signs consequently gives $1<\gcd(R_d,n)<n$, including when some inert local factors are divisible by other primes of $n$. For instance, $n=257\cdot509\cdot263$ at $\ell=19$ gives gcd $263$, although $R_d$ and $n$ agree modulo $256$. [Chen–Garvan, Eq. (2.1) and the three-square identity](https://arxiv.org/pdf/2010.14315#page=6)

For any two distinct prime divisors $p,q$, demand $\ell\equiv3\bmod8$ and $(-\ell/p)(-\ell/q)=-1$. This prescribes a coset of index eight in the units modulo $8n$. Enumerating eligible primes $\ell$ up to $O(b_n^2)$ therefore finds a mixed twist. One can also enumerate until a proper gcd appears. Across recursion there are at most $O(b)$ splittings and perfect-power reductions with multiplicities tracked. [Least prime in a coset](https://arxiv.org/pdf/1309.3595#page=3)

For the small-prime output interface, skip $r\mid 2B_\ell$. Each remaining answer gives $R_\ell-n\bmod r$ by division by $B_\ell$. CRT reconstructs the unique integer in $[0,n)$ once the product of retained primes reaches $n$. Such a product is reached with $r=O(b_n)$ and $O(b_n/\log(2b_n))$ queries per twist. Indeed $\sum_{p\le x}\log p\sim x$, while the skipped primes contribute at most $\log(2B_\ell)=O(\log b_n)$. This also works for an all-split twist, when the difference is zero. [Chebyshev-function estimates, Rosser–Schoenfeld](https://doi.org/10.1090/S0025-5718-1975-0457373-7)

## Quarter-bit counts with polynomial overhead

When $\omega(n)\le8$, the prime-only algorithm already has polynomial overhead. The coset specifying all signs has index at most $4\cdot2^8$, so its isolating prime is $O(b_n^2)$. The low-bit decoder applies to any nonsquare cofactor by targeting a prime of odd multiplicity. Run that search alongside the following one, or enumerate both finite lists using the explicit least-prime bound. The factorization algorithm never needs $\omega(n)$. [Prime-only decoder and divisor listing](hurwitz-residues.md#one-large-index-and-quarter-bit-precision-suffice)

If $\omega(n)\ge9$, mark any nine distinct prime divisors in the **existence proof**. Assign them nine distinct nonzero four-bit labels. For each of the four coordinates the signs $(s_i/p)$ at the nine marked primes and $s_i\equiv1\bmod8$ specify a coset of fixed index $4\cdot2^9$ modulo $8n$. Choose four distinct nonzero columns of signs, for example using the binary encodings of the integers 1 through 9 as rows. Each coordinate then has a prime $s_i=O(b_n^2)$ and the columns ensure that these four primes are distinct. The algorithm tries all four-element sets in that polynomial range. The order of their coordinates only permutes the labels. For the successful set, the actual factors fall into at least nine nonempty nonzero classes. Writing $e_p$ for the multiplicity of $p$, at least one such class $v$ has prime-power product $P=\prod_{p\in v}p^{e_p}\le n^{1/9}$.

For $a\in\{0,1\}^4$, set $d_a=3\prod_{i:a_i=1}s_i$ and $F_a=C(d_a,n)/(B_{d_a}n)$. Let $v_p$ denote the **label** of $p$, with bit $i$ set when $(s_i/p)=-1$, and put $\sigma_p=(-3/p)$. The local exponent of $w_p$ in $F_a$ is $(1-\sigma_p(-1)^{a\cdot v_p})/2$. For any nonzero $v$, summing those exponents against $(-1)^{a\cdot v}$ gives
$$
\prod_a F_a^{(-1)^{a\cdot v}}=U_v^8,\qquad
U_v=\prod_{p:v_p=v}w_p^{-\sigma_p}.
$$
This follows by pairing opposite signs in the sum of every nontrivial character on $\{0,1\}^4$. The constant term cancels because $v\ne0$. Every $F_a$ is a ratio of odd integers.

Let $K=\lceil b_n/4\rceil+1$ and $L=K-\max_a v_2(B_{d_a})$. Since $d_a=O(b_n^8)$ and $B_{d_a}$ is polynomially bounded in $d_a$, the loss is $O(\log b_n)$. From a count modulo $2^K$, divide by the known power of two in $B_{d_a}$ before inverting the remaining odd factors. Compute the product modulo $2^L$. Enumerate all odd eighth roots by lifting one bit at a time. There are at most 16 at any precision, by the structure of the units modulo a power of two. Finitely many small inputs can be handled by trial division.

Write $U_v=u/v'$ in lowest positive terms. Before cancellation, its numerator and denominator are each $P$ times a subproduct of the $w_p$, hence both are below $2P$. For the chosen small cell this gives $u,v'<2n^{1/9}$ and $2uv'<8n^{2/9}<2^L$ for sufficiently large $b_n$. Use the uniform bound $H=2\lfloor n^{1/9}\rfloor$ on each coordinate, so $2H^2<2^L$. Rational reconstruction by the Euclidean algorithm on each eighth root lists the correct fraction. The modulus is coprime to its odd denominator. [Wang–Guy–Davenport, rational reconstruction](https://www.cecm.sfu.ca/~monaganm/teaching/TopicsinCA13/GuyDavenWang.pdf)

At least one of $\gcd(u,n),\gcd(v',n)$ is a proper divisor. To see why cancellation is harmless, take a nonempty sign side of the cell, with prime-power product $Q$. Its unsigned product of $w_p$ has the form $A/Q$ with $Q<A<2Q$, so some $p\mid Q$ has $v_p(A)<v_p(Q)$. The other side has product $A'/Q'$ with $(Q,Q')=1$. In $(A/Q)(Q'/A')$ this $p$ survives in the denominator. If the nonempty side is inverted, it survives in the numerator instead. Both coordinates of the reduced fraction are smaller than $n$. Test both gcds for every candidate and accept only proper divisors.

There are $O(b_n^8)$ four-tuples, sixteen subset counts per tuple, and fifteen nonzero classes to try. A tuple's exact bases and all arithmetic outside the large queries take polynomial bit time. Recursing on verified splits proves the first row. For any fixed $c>0$, a further $\lfloor c\log_2 b_n\rfloor$ bits can be omitted. In the prime-only branch enumerate the polynomially many completions of each individual large answer before its decoder. In the composite branch the slack $b_n/4-2b_n/9$ already covers the lost bits for sufficiently large $b_n$. For a fixed $\eta>0$, the same small-cell argument with any fixed integer $m>2/\eta$ and $\lceil\log_2(m+1)\rceil$ coordinates suffices at precision $\lceil\eta b_n\rceil+1$ **on a split with at least $m$ distinct prime divisors**. For instance, four coordinates can mark 15 primes and split such a cofactor at $2b_n/15+O(\log b_n)$ bits: complete the normalized residues by $O(\log b_n)$ bits at the rational-reconstruction endpoint. A recursive run can still encounter cofactors with fewer distinct primes.

## Fewer large count queries per cofactor

The number of quarter-bit queries per cofactor can be reduced to $O(b_n^2/\log(2b_n))$ while retaining the same precision and index bound. This sharpens the enumeration of four-tuples above. Constants in the construction depend on marking nine primes and can be large.

Write $q=8n$, $h=4\cdot2^9$ and $X=C b_n^2$ with a sufficiently large absolute $C$. Each specified column of nine signs with $s\equiv1\bmod8$ is a coset on the units modulo $q$. There are $\gg_h X/\log X$ primes in that coset in $[X/4,X]$, uniformly in $n$ and the marked factors. To see the short-range uniformity, use the weighted character sum $S(x,\chi)=\sum_{j\le x}\Lambda(j)\chi(j)\log(x/j)$. For $x$ within a constant factor of $X$, the nonprincipal bound in Lamzouri–Li–Soundararajan (4.8), with the inner sum bounded in absolute value by $O(\log x)$, gives
$$
O\big(\sqrt x(\log q+\log x)+\log^2 x+\log x\log(qx)\big).
$$
For the principal character the main term is $x$, with the imprimitive omissions bounded by $O(\omega(q)\log^2 x)$ in addition to the zeta-function error. Apply character orthogonality to $S(X)-2S(X/2)+S(X/4)$. The weight on each von Mangoldt term is nonnegative, supported on $[X/4,X]$ and at most $\log2$. The principal main term after division by $h$ is $X/(4h)$. Higher prime powers contribute $O(\sqrt X\log^2 X)$. Increasing $C$ makes the total error less than half the main term for large $b_n$. Each prime contributes at most $(\log X)\log2$, giving the claimed lower bound. In the list of eligible primes in this interval, of size $M\ll X/\log X$, each of the four target columns consequently occupies a fixed positive fraction. [Lamzouri–Li–Soundararajan, §4.1, especially (4.3)–(4.8)](https://arxiv.org/pdf/1309.3595#page=13)

Set $m=\lfloor\sqrt M\rfloor$ and retain the first $m^2$ primes. Dropping $O(\sqrt M)$ entries preserves a common positive density $\delta$ for each column. Index these primes by the vertices of the constant-degree Margulis–Gabber–Galil graph on $(\mathbb Z/m\mathbb Z)^2$. Its normalized transition matrix $P$ has $\|P-J\|\le\lambda<1$, where $J$ averages over all vertices. Choose a fixed $k$ with $3\lambda^k<\delta^4$. For the four target sets let $D_i$ be their diagonal indicator matrices. In the uniform inner product the fraction of walks meeting the four sets at times $0,k,2k,3k$ is
$$
\langle 1,D_1P^kD_2P^kD_3P^kD_4 1\rangle .
$$
Replacing the three transitions by $J$ gives the product of the densities, at least $\delta^4$. Telescoping the three replacements changes the expression by at most $3\lambda^k$, since the remaining operators are contractions. Thus some walk meets the required four columns. Their distinct sign patterns force four distinct primes. [Explicit graph and spectral bound](https://isa-afp.org/browser_info/current/AFP/Expander_Graphs/Expander_Graphs_Strongly_Explicit.html)

Enumerate all starts and all walks of length $3k$, using the four checkpoint primes when they are distinct. This gives $O(M)$ tuples at constant cost in large queries per tuple. The algorithm constructs this list without the prime factors or the marked sets. The branch for at most eight prime factors already scans $O(b_n^2/\log(2b_n))$ prime twists. The bound counts expensive oracle calls. Computing small class numbers and rational reconstructions still takes polynomial bit time. This search bound and its constants are analytic results.

## A tradeoff with three coordinate primes

Eight large subset counts and one fixed character per tuple also suffice if a larger polynomial search range is acceptable. For $\omega(n)\ge8$ mark eight primes, assign them all three-bit labels, and assign the lightest marked prime (weight $e_p\log_2p$) to a fixed nonzero label $S$. For each of the three columns draw an eligible prime independently from the required sign coset with weight $(\log s)\log(X/s)$ up to $X=b_n^8$. Given one unmarked prime $q'$, its two possible additional signs have equal main terms by CRT. The same weighted sums, even with the coarser error $O(\sqrt X\log^2(8nX))$ after removing prime powers, give each conditional sign probability $1/2+O(b_n^{-2})$. The expected weight of the cell at $S$ is at most one eighth of the total marked weight plus $(1/8+O(b_n^{-2}))$ times the unmarked weight. Some tuple therefore gives $P_S=O(n^{1/8})$, and that cell contains the designated marked prime. [Smoothed character estimates](https://arxiv.org/pdf/1309.3595#page=13)

Try the tuples deterministically. The Walsh product is now a fourth power. Enumerate its at most eight odd roots and complete each residue by $O(\log b_n)$ additional bits so that the reconstruction modulus exceeds a fixed constant times $n^{1/4}$. These polynomially many lifts cover the true fraction, whose numerator and denominator are $O(n^{1/8})$. The preceding gcd argument gives a verified split. The four-coordinate proof permits a smaller prime search range, and the three-coordinate proof uses fewer counts and fewer characters for an individual tuple.

## Reproduction

The callable GP routine `factorHurwitzModPrimes(N, countResidue)` returns sorted prime factors with multiplicity. Its callback receives $(\ell,n,r)$ and returns $C(\ell,n)\bmod r$. The sample implementation uses PARI’s primality test, while the polynomial-time reduction can use deterministic polynomial-time primality testing. To run it from the repository root with PARI supplying the modular counts, use

~~~gp
read("experiments/hurwitz-mixed.gp");
factorHurwitzModPrimes(1019*1021*1031,(ell,n,r)->(3*qfbhclassno(ell*n^2))%r)
~~~

The [mixed-twist regression](../experiments/hurwitz-mixed.gp) compares CRT reconstruction with exact PARI counts on 60 twists. It includes 40 mixed twists and one case where the gcd contains an inert prime. The regression passes only the residues to the CRT decoder.

The [Walsh regression](../experiments/hurwitz-walsh.gp) checks 18 exact and 180 truncated products. One 90-bit fixture recovers the signed fraction $91/99$ and the divisors 7 and 11 from 23-bit counts. In a separate 174-bit cofactor all twelve distinct prime divisors survive the stated trial bound, and one occurs twice. From 45 bits per count the decoder obtains proper gcds in eleven cells, including 10039. PARI supplies the large counts to the regression. Selecting the tuple on arbitrary inputs and the asymptotic bounds are paper arguments.
