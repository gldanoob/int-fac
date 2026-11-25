# Counting rough inputs factored in polynomial time from the integer alone

Take the bit length $b$ of $N$ as the smoothness bound in Źrałek's deterministic $p-1$ algorithm. This gives **one fixed algorithm** that completely factors each of the following input sets in $O(b^7)$ time. Both counts hold at **every sufficiently large bit length**. They use the fixed-parameter Poisson–Dirichlet theorem for prime predecessors. [Źrałek, Corollary 4.6](https://arxiv.org/pdf/0707.4102#page=7) · [OpenAI, Theorem 1.1 and equation (1.3)](https://github.com/openai/math/blob/main/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf) · [Lichtman, Theorem 1.3](https://arxiv.org/pdf/2611.28392#page=2)

- For fixed $A>1$, among $b$-bit semiprimes $N=pq$ with $b^A<p\le b^{2A}$ and $q>p$, a proportion tending to $\int_A^{2A}\rho(u)\,du/(u\log 2)>0$ has a $b$-smooth predecessor $p-1$. Here $\rho$ is the Dickman function. These inputs can have an arbitrary prime as their larger factor.
- For fixed $A>1$, among squarefree $b$-bit integers with **all** prime factors in $(b^A,2b^A]$, at least $2^{(1-1/A)b-O_A(b/\log b)}$ have $p-1$ $b$-smooth at every factor. The whole set, before imposing any smoothness, has size at most $2^{(1-1/A)b+O_A(b/\log b)}$.

In particular, let $h(b)\to\infty$ arbitrarily slowly. There exist $A(b)\to\infty$ and, at every sufficiently large $b$, at least $2^b/(b h(b))$ semiprimes in the first class and $2^{(1-o(1))b}$ squarefree integers in the second. Every prime factor of these inputs exceeds every fixed power of $b$ eventually. The semiprimes have very different factor sizes. The squarefree inputs have a growing number of comparable prime factors. Both classes are defined without prescribing a residue class for $N$.

## The input-only algorithm and analytic ingredient

Źrałek's Corollary 4.6(ii) gives complete deterministic factorization in $O(B(\log N)^6)$ for $B\ge\log N$ when at most one prime divisor of $N$ has a predecessor that is not $B$-smooth and some prime divisor has a $B$-smooth predecessor. Use $B=b$ and retain this bound during recursion. The algorithm's factored scalar is computed from $N$ and $b$ by sieving primes $\ell\le b$ and taking each to the largest power at most $N$. This takes polynomial bit cost, and every $b$-smooth $p-1$ divides the scalar. The group computations and deterministic primality tests establishing the complete factorization and running time are in the published algorithm. A time cap can return an inconclusive result on other inputs. [Źrałek, proof of Corollary 4.6](https://arxiv.org/pdf/0707.4102#page=7)

The counting input is that, for fixed $v\ge1$, primes with $P^+(p-1)\le p^{1/v}$ have relative density $\rho(v)$ among all primes. Here $P^+$ denotes largest prime factor. The stated Poisson–Dirichlet limit normalizes by $\log(p-1)$, and replacing this by $\log p$ follows by squeezing at adjacent fixed parameters and using continuity of $\rho$. Thus each fixed positive-length interval $(cX,dX]$ contains $(\rho(v)+o(1))(d-c)X/\log X$ such primes for $0<c<d$. In particular if $X=b^A$ and $c,d$ are fixed, choosing $v=2A$ ensures at least $c_{A,c,d}X/\log X$ primes there with $b$-smooth predecessor for all large $b$. Only fixed-parameter convergence is used at this step. [Original fixed-parameter theorem](https://github.com/openai/math/blob/main/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf) · [November 2026 quantitative fixed-$v$ refinement](https://arxiv.org/pdf/2611.28392#page=2)

## Semiprimes with least factor beyond trial division through a polynomial

Uniformly over $b^A<p\le b^{2A}$, the prime number theorem gives

$$\#\{q\text{ prime}:2^{b-1}\le pq<2^b\}\sim \frac{2^{b-1}}{b\log 2}\frac1p.$$

All such $q$ exceed $p$ for large $b$. The sum of $1/p$ over the full band tends to $\log 2$. Over the primes with $b$-smooth predecessor the sum tends to

$$I_A=\int_A^{2A}\rho(u)\,\frac{du}{u}.$$

To prove the second estimate, partition $[A,2A]$ into fixed intervals $[s,t]$. On $b^s<p\le b^t$, the indicator of $P^+(p-1)\le b$ lies between the indicators for $p^{1/t}$ and $p^{1/s}$. For each fixed $v$, partial summation of the prime density at $v$ shows that its harmonic sum in this interval tends to $\rho(v)\log(t/s)$. Refine the partition and use continuity. Consequently the number of inputs with the promised smooth predecessor is asymptotic to $2^{b-1}I_A/(b\log 2)$. The algorithm can also succeed on other inputs.

## Filling one exact binary length with comparable prime factors

Put $X=b^A$, and use three disjoint intervals for the prime factors. Take two pools $(X,1.1X]$ and $(1.3X,1.4X]$, and the interval $(1.6X,1.9X]$ for the factors of an initial product. Each interval contains $\gg_A X/\log X$ primes with $b$-smooth predecessor. Write $L=\log_2 X$, and take

$$r=\left\lfloor\frac{b-1-b/L}{\log_2(1.9X)}\right\rfloor.$$

Every choice of $r$ distinct primes in the last interval gives a product $C$ with remaining length $D=b-1-\log_2 C=\Theta_A(b/L)$. Its lower bound follows from the definition of $r$. For the upper bound, the variation of each prime logarithm across the last interval is bounded by an absolute constant, and $r=O(b/L)$. The number of choices, with $P\gg_A X/\log X$ available primes, satisfies

$$\log_2\binom{P}{r}\ \ge\ r\log_2(P/r)\ \ge\ (1-1/A)b-O_A(b/\log b).$$

Here $r=b/L+O_A(b/L^2)$ and $\log_2(P/r)\ge(A-1)\log_2 b-O_A(1)$.

Order the primes in each pool arbitrarily. Take the least $m$ such that the product of the first $m$ primes in the higher pool reaches $2^D$. The product is below $1.4X\,2^D$, and $m=\Theta_A(b/L^2)$. The two pools contain more than $m$ primes. Replacing all $m$ high primes by the corresponding low primes multiplies the product by at most $(1.1/1.3)^m<1/(1.4X)$ for large $b$. Thus the two endpoints bracket $2^D$. Replace the primes one at a time. Each replacement decreases the product by a factor at most $1.4<2$. The last product still at least $2^D$ is consequently below $2^{D+1}$. Multiply it by $C$ to get exactly $b$ bits. The initial primes can be recovered uniquely from the final factorization by their interval, so this map is injective.

For the matching upper bound, the entire interval $(X,2X]$ contains $P'\ll_A X/\log X$ primes. Any eligible product has at most $k=\lfloor b/L\rfloor$ prime factors. Since $A>1$, eventually $k<P'/2$. The number of subsets is at most $(k+1)(eP'/k)^k$, whose base-two logarithm is at most $(1-1/A)b+O_A(b/\log b)$. This matches the leading exponent of the factorable class.

## Letting the least factor grow

For integer $j\ge2$ apply both results with $A=j$. Choose increasing thresholds $b_j$ so both estimates hold for all $b\ge b_j$, the lower exponent in the second result exceeds $1-2/j$, and $h(b)\ge 4\log 2/I_j$ for all $b\ge b_j$. Set $A(b)=j$ for $b_j\le b<b_{j+1}$. This establishes both diagonal statements. The algorithm always uses the cutoff $b$ and does not need $A(b)$, these thresholds or a convergence rate. The proof gives no explicit growth rate for $A(b)$. At any fixed number of comparable factors and polynomial cost, using smooth predecessors this way would require a quantitative supply of primes at a shrinking smoothness exponent. The cited fixed-$v$ statements do not give such a supply for a specified $v=v(X)$.

## Arithmetic replay

`python -B experiments/smooth-predecessor-products.py` checks 384 products at 32 consecutive bit lengths. The initial primes occupy their own interval, individual high-to-low replacements preserve squarefreeness, and exact products certify the bit-length crossings. The first has 8,160 bits and 491 prime factors between 65,537 and 110,083. The replay also counts all semiprime pairs in the band $b^{4/3}<p\le b^{8/3}$ at 27 and 28 bits. At 28 bits the band contains 7,133,381 pairs, of which 3,355,647 have a 28-smooth smaller-prime predecessor. The counts test finite membership only. Three smaller examples check complete recovery by actual modular exponentiation, gcds and a fixed base list from the input. The general polynomial bound uses Źrałek's published algorithm. [Exact replay](../experiments/smooth-predecessor-products.py)
