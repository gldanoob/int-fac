# Dickman-scale Hasse counts and the leading constant in deterministic mean time

Let $P\to\infty$, $L=\log P$, $s=\log Y$, $u=L/s\to\infty$, and suppose $s\ge c\sqrt{L\log L}$ for a fixed $c>0$. For all but $P^{4/5+o(1)}$ primes $p\in(P,2P]$, the central Hasse interval contains
$$
       \sqrt P\,\exp(-(1+o(1))u\log u)
$$
distinct integers $n=4m$ with $m$ odd and $Y$-smooth, where the display is a lower bound. The ordinary Riemann hypothesis used in the prime explicit formula was proved by Alpöge and checked independently by Sutherland. Hildebrand's long-interval distribution applies classically throughout this range. The proof permits the **fixed value** $c=1/\sqrt2$. [Ordinary RH verification](https://math.mit.edu/~drew/grh/) · [Hildebrand](https://doi.org/10.1016/0022-314X(86)90013-2) · [Hildebrand–Tenenbaum, Theorem 1.1 and Corollary 2.4](https://tenenb.perso.math.cnrs.fr/PPP/Survey_friables.pdf)

Taking $s=\sqrt{L\log L/2}$ gives the following bound for a uniform deterministic algorithm which completely factors every integer. Its mean bit cost over all integers $X<N\le2X$, and separately over balanced products of distinct primes $P<p,q\le2P$, is
$$
     \exp\big((1+o(1))\sqrt{\log X\,\log\log X}\big),
$$
where $X=P^2$ in the balanced family. For $b$-bit integers the leading expression in natural logarithms is $\sqrt{(b\log 2)\log(b\log 2)}$. The prime-local contribution has coefficient $\sqrt2$ at $\sqrt{\log p\log\log p}$. The algorithm retains the existing worst-case bound by interleaving. The result concerns deterministic average time over inputs. Lenstra–Pomerance previously obtained this leading constant in per-input randomized expected time by a class-group algorithm and discussed a density-one randomized ECM analysis in §7. [Lenstra–Pomerance, theorem and §7](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/rigorous.pdf#page=19) · [Earlier deterministic mean bound](mean-time-elliptic-factoring.md)

Hildebrand–Tenenbaum's Theorem 5.7 gives an almost-all Dickman asymptotic at larger smoothness cutoffs. Their accompanying discussion reports a 1993 unpublished preprint of Hafner giving an ordinary-RH lower bound already at $Y\ge\exp(\sqrt{L\log L})$ in much shorter intervals. Matomäki–Radziwiłł also identify that result as unpublished. The present argument allows every fixed positive coefficient in front of $\sqrt{L\log L}$, enforces the odd cofactor, and bounds the number of exceptional prime centers by $P^{4/5+o(1)}$. Hafner–McCurley studied the input distribution of running times for factoring methods governed by the second largest prime factor, with an application to complete randomized factoring. [Hildebrand–Tenenbaum, §5, Theorems 5.6–5.7](https://tenenb.perso.math.cnrs.fr/PPP/Survey_friables.pdf) · [Matomäki–Radziwiłł, Corollary 6 and reference 13](https://arxiv.org/pdf/1501.04585#page=5) · [Hafner–McCurley](https://doi.org/10.1016/0196-6774(89)90004-7)

## Prime factors with distinct size bins

Put $T=P/4$, $J=\lfloor u/5\rfloor$, $M=\lfloor s/(10\log(2u))\rfloor$ and $z_i=Y\,2^{-i-1}$ for $0\le i<M$. Both $J,M$ tend to infinity. Each $z_i=Y^{1-O(1/\log(2u))}$. Fix a nonnegative smooth function $W(v)$ supported on $|v|<1/5$ and equal to one on $|v|\le1/10$. The prime bins $W(\log(r/z_i))\ne0$ are disjoint, and all their primes are odd and at most $Y$ for sufficiently large $P$.

Average over ordered bin vectors $\mathbf i=(i_1,\ldots,i_J)$ with the uniform weight $M^{-J}$. For one vector let $A_\mathbf i=\prod_j z_{i_j}$, $Z_\mathbf i=T/A_\mathbf i$ and $\mathcal M_\mathbf i$ be all odd $Y$-smooth integers in $[Z_\mathbf i,1.01Z_\mathbf i]$. Uniformly in the vector,
$$
 \log A_\mathbf i=(1/5+o(1))L,\qquad
 \log Z_\mathbf i=(4/5+o(1))L,\qquad
 d_\mathbf i=\sum_{m\in\mathcal M_\mathbf i}1/m
       =\exp(-(4/5+o(1))u\log u).
$$
For the last assertion the four cumulative smooth counts at $Z$, $1.01Z$, $Z/2$, $1.01Z/2$ give $(0.005+o(1))Z\rho(\log Z/s)$ odd integers by Hildebrand's estimate. Changing any one endpoint by a fixed factor changes its Dickman value by $1+O(\log(2u)/s)=1+o(1)$. The logarithmic Dickman estimate is $\log\rho(v)=-(1+o(1))v\log v$ as $v\to\infty$. The bin vector only occurs in the analysis. The algorithm does not enumerate these vectors or smooth cofactors.

Put positive mass at each $\log(m\prod_j r_j)$ with value $m^{-1}\prod_j (\log r_j)W(\log(r_j/z_{i_j}))/r_j$, summed over these $m$ and primes $r_j$, and average the measures over the bin vectors to obtain $\mu$. Write $\nu$ for the corresponding average in which the prime measures are replaced by $W(\log(r/z_i))\,dr/r$. Let $K$ be a fixed smooth nonnegative kernel supported in $[-1,1]$, of integral one and positive on $[-1/2,1/2]$. Put $h=1/(100\sqrt P)$ and $K_h(x)=K(x/h)/h$. For all $x\in[T-1,2T+1]$,
$$
   (\nu*K_h)(\log x)\ \ge c_0^J\,\mathbb E_\mathbf i d_\mathbf i
$$
with an absolute $0<c_0<1$. For fixed $\mathbf i,m$ write $v_j=\log(r_j/z_{i_j})$, $a=\log(x/(A_\mathbf i m))$, so $|a|<1$ for large $P$. Restrict each successive partial sum through step $j<J$ to the interval of radius $1/100$ about $ja/J$. At each step the permissible $v_j$ interval has length $1/50$ and lies in $[-1/10,1/10]$ for large $J$. The final $v_J$ can be chosen from an interval of length $h/2$ where the actual kernel has value $\gg 1/h$. Thus the lower bound costs $\exp(O(J))$ uniformly. In particular it incurs no $J^{-J}$ penalty.

## The high-frequency exceptional set

For a bin $i$, denote the two Fourier transforms by
$$
 P_i(t)=\sum_{r\ \mathrm{prime}}\frac{(\log r)W(\log(r/z_i))}{r^{1+it}},
 \qquad P_i^0(t)=z_i^{-it}\!\int W(v)e^{-itv}\,dv .
$$
Each is $O(1)$ uniformly. For $|t|\le P^2$ the prime explicit formula on ordinary RH gives $|P_i(t)-P_i^0(t)|\ll z_i^{-1/2}L^3$. Indeed the nontrivial zeros contribute $O(z_i^{-1/2}\log(2+|t|))$ by the unit-interval zero count and the rapid decay of the transform of $W$. Removing higher prime powers costs $O(z_i^{-1/2}L^2)$ and the trivial-zero terms are smaller. The explicit formula is needed only on these smooth fixed-relative-width bins. [Explicit formula for the prime measure](odd-smooth-hasse.md#a-convolution-of-odd-primes-and-smooth-cofactors)

Let $T_0=Y^{1/10}$. On $|t|\le T_0$ telescope the difference of products of $J$ prime transforms. Its inverse Fourier integral after multiplying by the cofactor transform $D_\mathbf i(t)=\sum_{m\in\mathcal M_\mathbf i}m^{-1-it}$ and the kernel has magnitude
$$
 \ll d_\mathbf i\, T_0 J C_1^J\,Y^{-1/2+o(1)}L^3 .
$$
Because $J=o(s)$, this is $o(c_0^J d_\mathbf i)$ for every fixed $c>0$ in the hypothesis $s\ge c\sqrt{L\log L}$. Thus the low-frequency error after averaging is negligible relative to the continuous lower bound **at each center**, even for $c=1/\sqrt2$. No dyadic interval of the cofactor has been given unit mass in this comparison.

On $T_0\le|t|\le P^2$, integrating $P_i^0$ by parts a fixed number of times, for instance twelve, gives $P_i^0(t)\ll Y^{-1}$. For the continuous or discrete product one therefore has
$$
        \left|\prod_{j=1}^J P_{i_j}^{(*)}(t)\right|^2
        \le A_\mathbf i^{-1}L^{O(J)}=P^{-1/5+o(1)}.
$$
Here $J\log L=o(L)$. The cofactor mean value theorem gives $\int_{\mathbb R}|D_\mathbf i(t)\widehat K(ht)|^2dt\ll1$. In detail its unweighted integral to height $B$ is $O((B+Z_\mathbf i)d_\mathbf i/Z_\mathbf i)$, by the Dirichlet-polynomial mean value theorem. Sum dyadic heights using rapid decay of $\widehat K$ and $hZ_\mathbf i\gg1$. For $|t|>P^2$ the prime transforms and the cofactor are bounded trivially and $\widehat K(ht)$ saves any fixed power of $P$. Consequently the squared $L^2$ norm of the high-frequency part of $(\mu-\nu)*K_h$ is $\ll P^{-1/5+o(1)}$: Jensen's inequality for the probability average retains the uniform estimate for each bin vector. [Montgomery–Vaughan mean value theorem](https://doi.org/10.1112/jlms/s2-8.1.73)

The continuous lower bound is $P^{-o(1)}$. Chebyshev and Plancherel give $(\mu*K_h)(\log x)\ge c_0^J\mathbb E_\mathbf i d_\mathbf i/2$ outside a set of **logarithmic measure** at most $P^{-1/5+o(1)}$. To count distinct smooth integers near each retained center, take a supported product $v\asymp P$. Its ordered prime factors $r_j$ can be chosen in at most $(C_2u)^J$ ways, because each such factor exceeds $Y^{1-o(1)}$. The primes determine their unique bin indices by disjointness, and their product determines the residual cofactor. Thus the averaged mass at this single atom is at most
$$
        \frac1v\left(\frac{C_2u\,\log Y}{M}\right)^J
             \le P^{-1}\exp((1/5+o(1))u\log u).
$$
The $M^{-J}$ probability is essential here. Since $\|K_h\|_\infty\ll\sqrt P$, the retained center contains at least $\sqrt P\exp(-(1+o(1))u\log u)$ distinct odd $Y$-smooth $v$ in $|\log(v/x)|\le h$. For each prime $p$ take the disjoint real intervals $|x-(p+1)/4|\le1/16$ of logarithmic measure $\gg1/P$. A single retained center there puts every corresponding $4v$ inside $|4v-(p+1)|\le\sqrt p$. Hence at most $P^{4/5+o(1)}$ primes fail the stated count. Removing $4v=p+1$ costs at most one order at any prime.

## Charging the deterministic selection and full recursion

For a good prime in this dyad, the set of eligible ordinary traces has relative size $\delta\ge\exp(-(1+o(1))u\log u)$ among the central traces with order $4\bmod8$. The [least Legendre mass estimate](vertical-trace-subsets.md) gives untwisted parameter density at least a constant times $\delta/\log(2+\log(1/\delta))=\exp(-(1+o(1))u\log u)$; its classical version suffices since the number of traces is $p^{1/2-o(1)}$. For any small public conic with the required signs at $p$ and another prime factor $q$, the [quadratic character bound](vertical-trace-subsets.md#both-quadratic-signs-from-a-logarithmic-mark-prefix) shows that $O(\log p)$ distinct conic marks retain at least half of these parameters. For example $H=\lceil2\log_2(2P)\rceil$ is a uniform prefix. The mark heights are polynomial in the modulus bit length and $H$, so the small-prime preprocessing cutoff and the number of point tests per parameter are polynomial. The good marked parameter density on the public binary cube is $\gamma\ge\exp(-(1+o(1))u\log u)$.

Use the [one-conic algorithm](untwisted-legendre-partners.md), the explicit small-bias XOR shifts and its whole-partner estimate with $r=1$. At each tested parameter the odd scalar is applied as a succession of maximal odd prime powers with bases at most $Y$ and powers at most $4P$. Sieving, scalar multiplication and the conic list cost $Y\,\mathrm{poly}(\log N)$ bit operations per parameter. From stage $a$ onward at most a $\mathrm{poly}(\log N)/(4^a\gamma)$ fraction of integer starts are missed, while the stage has $4^a$ shifts. The average cost of finding one split at fixed $p$, with the whole integer cofactor in a dyadic interval of length comparable to or larger than $p$, is therefore
$$
    Y\,\gamma^{-1}\,\mathrm{poly}(\log N)
       \le\exp\big(s+(1+o(1))u\log u\big)\,\mathrm{poly}(\log N).
$$
On the proved Dirichlet GRH the polynomial-size conic list is pointwise for all pairs of primes. Alternatively the classical small exceptional-partner estimate and the factorial fallback in the one-conic proof give the same bound. A single deterministic algorithm interleaves all dyadic size/shift guesses, the scalar track below and its all-prime backup. It tests for exact powers and certifies prime factors. The number of tracks is polynomial in the input bit length. [Local parity split and conic construction](untwisted-legendre-partners.md) · [Mean-time sampler and recursion](mean-time-elliptic-factoring.md)

Set $s=\sqrt{L\log L/2}$, rounding $Y=e^s$ to an integer, with bounded dyads done directly. Then $u\log u=(1/\sqrt2+o(1))\sqrt{L\log L}$, so the good-prime charge is $\exp((\sqrt2+o(1))\sqrt{L\log L})$ up to the indicated bit polynomial. On every exceptional prime use the established classical backup with fixed $\theta=31/200$: the cost averaged over integer partners is $p^\theta\mathrm{poly}(\log N)$ when the interval length is comparable to or larger than $p$. If a partner interval at the balanced boundary starts between $p/2$ and $p$, the proof by counting all integer starts still has the same bounded fiber factor $1+p/Z$, and the number of eligible inputs is upper bounded by the count on that whole interval. Exact powers are recognized directly. [Every-prime mean backup](untwisted-legendre-partners.md#whole-integer-partners-and-rare-failure-of-the-conic-list)

For a wholly integral choice on a dyad $P=2^k$, set $v=\lceil\log_2(2k)\rceil$ by a bit-length test, $h_0=\lceil\sqrt{\lceil kv/2\rceil}\rceil$ by integer square root and $Y=2^{h_0}$. Then $\log Y\ge\sqrt{L\log L/2}$, since $v\ge\log_2(k\log 2)$, and $\log Y=\sqrt{L\log L/2}(1+O(1/\log k))$. This yields the same leading coefficient in both $s$ and $u\log u$. Computing the cutoff takes polynomially many bit operations in the input length.

In $X<N\le2X$ each composite has a least prime $p\le\sqrt{2X}$. Its possible partners lie in $(X/p,2X/p]$ of length at least $p/2$. On a bad-prime dyad $(P,2P]$ the normalized contribution is $\mathrm{poly}(\log X)P^{4/5+\theta-1+o(1)}$, summable over large dyads since $4/5+\theta<1$. For good primes the factors $1/p$ in the normalized mean sum to only a polynomial in $\log X$. Substituting $p\le\sqrt{2X}$ in the good-prime charge converts $\sqrt2$ to $1$. Uniform $o(1)$ on large dyads suffices, since finitely many small dyads cost polynomial time.

For complete recursion over integer inputs, charge each visited cofactor to its numerical divisor of the original integer with at most $O(\log X)$ repetitions. A number $d\le2X$ divides at most $3X/d$ numbers in the dyad, so the mean complete cost is at most a polynomial times the sum of the one-split costs weighted by $1/d$. Summing the one-split estimates dyadically preserves their leading coefficient. On balanced prime pairs a single successful split leaves primes, and passing from whole integer partners or the ambient dyad to prime pairs costs only a polynomial in $\log X$. This proves the stated mean bounds with the fixed smoothness cutoff.

The replay reconstructed the aggregated weights of all 1,953 distinct atoms from 10,175 assignments to 27 ordered bin vectors. It proved 17,928 finite instances of the one-sign bound with separately chosen signs by exact integer comparisons. The estimates on the prime sums, class numbers and exceptional primes are analytic. [Finite bin and sign replay](../experiments/sharp-elliptic-mean.py)
