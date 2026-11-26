# Sparse signed order relations

Fix an odd modulus $N>1$, an ordered list of $t$ unit residues $h_1,\ldots,h_t$, a positive scalar $s$, and a support limit $0\le k\le t$. Search words $v\in\{-1,0,1\}^t$ with at most $k$ nonzero coordinates for a proper $\gcd((h^v)^s-1,N)$. If none occurs, the same search counts all global relations and computes their rational span. The method lists at most halves of sparse words. Unlike a coordinate cut fixed before the search, the cut follows the median of each word's support.

## Median split and unique routing

Handle support zero directly and support one by separate gcd tests. For each exact support size $j\in[2,k]$, let $a=\lfloor j/2\rfloor$ and $b=\lceil j/2\rceil$. List signed words of exact support $a$ as prefixes and of exact support $b$ as suffixes. A prefix and suffix form a word of size $j$ precisely when the largest prefix index precedes the smallest suffix index. This is the unique median decomposition of the resulting word.

Build a balanced binary tree whose leaves are the indices $1,\ldots,t$ in order. Insert a prefix into the list at each ancestor of its largest index at which that index lies in the left child. Insert a suffix into the list at each ancestor of its smallest index at which that index lies in the right child. The two lists at any shared node have ordered, disjoint supports. The shared node is unique because it is the lowest common ancestor of the two extremal indices. Conversely, for any ordered pair the lowest common ancestor separates those indices in the required left-to-right order, so the routing includes the pair. Only the extremal index is constrained by a node. Other indices of either word may lie outside that node's subtree.

At each node bucket prefix words $u$ by $h^{su}$ and suffix words $w$ by $h^{-sw}$. The product-tree and derivative collision test from the boxed search detects a proper gcd between nonidentical residues, giving the word $u+w$. For a globally equal residue bucket with $A$ prefixes and $C$ suffixes, add $|A||C|$ to the relation count. The star sums based at one fixed prefix and suffix span all sums in that bucket, using $|A|+|C|-1$ candidates for exact rational elimination. Unique routing ensures that the count has no duplicates across nodes or support sizes. A relation modulo one prime is global whenever the search completes without a proper local gcd. The recovered span can be saturated and pooled exactly as for boxes. [Boxed relation search](cogentic-boxed-order-relations.md)

## List size versus the sparse ball

Write
\[
 S(t,j)=\sum_{i=0}^{j} 2^i\binom{t}{i},\qquad
 A=\lceil k/2\rceil,\qquad C=\lfloor k/2\rfloor .
\]
Each half-word is copied at most $\lceil\log_2t\rceil$ times for each size where it is used, and can appear as a given side for at most two sizes. For $k\ge2$ the aggregate number of list entries is $O(S(t,A)\log t)$. The proper-gcd tests for singleton words take $O(t)$ entries, absorbed by this quantity. With fast monic polynomial arithmetic, the search time is at most $S(t,A)$ times a polynomial in $t,\log N,\log s$, with the corresponding storage bound. For example, deterministic comparison sorting can build each residue bucket. Exact rank calculations use signed vectors of length $t$ and retain at most $t$ independent vectors. The cases $k=0,1$ need only the direct checks.

For an explicit comparison with $\sqrt{S(t,k)}$, the summands increase through index $A$, so $S(t,A)\le (A+1)2^A\binom tA$. Also
\[
 \binom tA\binom{t-A}C=\binom tk\binom kA,\qquad
 \frac{\binom tC}{\binom{t-A}C}\le\binom kC.
\]
The ratio inequality follows from the product of the $C$ factors $(t-i)/(t-A-i)$, each decreasing with $t$ for $0\le i<C$, so its maximum occurs at $t=k$. For even $k$, $\binom tA/\binom tC=1$. For odd $k$, it equals $(t-C)/(C+1)\le t$. Therefore for $k\ge1$,
\[
 S(t,A)\le (A+1)\sqrt{2t}\binom kA\,\sqrt{S(t,k)}.
\]
For even $k$ the factor $\sqrt{2t}$ can be omitted. This gives an explicit $\exp(O(k))\operatorname{poly}(t)$ overhead above the square root of the sparse ball volume. In particular, the estimate accounts for the larger half in an odd-support search.

## A one-third cost regime and its supply condition

Set $L=\log N$ and $H=L^{1/3}(\log L)^{2/3}$. If $t=\operatorname{poly}(L)$ and $k=O(H/\log L)$, then $\log S(t,\lceil k/2\rceil)=O(H)$, by bounding each summand by $(2t)^i$. For $\log s=\operatorname{poly}(L)$, the lists, arithmetic and rational elimination thus fit $\exp(O(H))$ time. The search gives a factor when a sparse word has a proper local gcd or the resulting order certificates expose a mixed sign. The time estimate itself supplies neither kind of witness.

One sufficient condition uses a polynomial-size menu of distinct primes $h_i\le L^{O(1)}$. Take $\ell=\lfloor k/2\rfloor$ and the products of exactly $\ell$ menu primes. For $s=1$ and sufficiently large $N$, their size bound is $\exp(O(H))<N$, so unique factorization makes them distinct globally. If for some $p\mid N$ the generated group modulo $p$ has size smaller than $\binom t\ell$, two products coincide locally and their quotient has signed support at most $2\ell$. It has a proper gcd because the products differ globally. For example, with $t=L^{D+o(1)}$ for fixed $D>1/3$ and $\ell\sim cH/\log L$, the binomial has logarithm $(c(D-1/3)+o(1))H$. This gives a one-third search with guaranteed supply under a quantitative small-local-order hypothesis.

For arbitrary $s$, the same argument requires that the powers of the products attain more **distinct global residues** than the size of the generated local group of powered bases. Select one product per distinct global residue and apply the same pigeonhole argument. Raising to $s$ can shrink both images, so a small local group alone does not imply a proper factor in the powered case.

For comparison, the unconditional product argument at the polynomial prime cutoff supplies words of support $O(L/\log L)$, using a product family larger than $\sqrt N$. At its larger support scale, the list bound above gives an exponential-in-$L$ search bound and does not yield one-third cost. The stronger rank result for a one-third-size prime cutoff uses many more generators and a different support scale. [Determinant and sparse supply bounds](cogentic-short-order-lattice-determinants.md)

As an exact example, take $N=899=29\cdot31$, $s=1$, and the primes through $23$. The products $6=2\cdot3$ and $35=5\cdot7$ agree modulo $29$ and differ modulo $31$. The word with coefficients $+1$ at $2,3$ and $-1$ at $5,7$ has support four. Its median decomposition uses these two disjoint pairs. The gcd of their difference is $29$.

The finite replay compares the tree partition with exhaustive enumeration at every support limit in dimensions zero through eight. Across the 45 partitions it recovers all 34,445 signed words exactly once. [Combinatorial replay](../experiments/cogentic-sparse-support-partition.py)

## How short can a productive word be?

Write an unpowered word on distinct positive primes at most $B$ as the reduced ratio $U/V$. A nonempty signed support of size $k$ gives $U\ne V$ and $UV\le B^k$. If it is one modulo a prime $p$ dividing $N$, then $|U-V|\ge p$, so one sign side alone contains at least $\log(p+1)/\log B$ letters. On every balanced semiprime the least possible support for a proper gcd at cutoff $B=C(\log N)^2$, $C>e^{-2}$, is therefore $\Theta(\log N/\log\log N)$ for sufficiently large $N$. The upper bound is the local pigeonhole construction above. This rules out a uniform reduction of the unpowered support to the one-third enumeration range. A small local subgroup in the preceding unpowered sufficient condition can only help when the relevant prime is below the product-height bound.

Public powering changes the necessary height. For any distinct positive $U,V$ coprime to $p$ and positive scalar $s$, suppose $(U/V)^s=1\bmod p$. With $d$ the order of $U/V\bmod p$ and $g_p=\gcd(s,p-1)$, one has
\[
       p\le |\Phi_d(U,V)|\le (U+V)^{\varphi(d)}
          \le (U+V)^{\varphi(g_p)} .
\]
Here $\Phi_d$ is the homogenized cyclotomic polynomial. Of the factors of $U^d-V^d$, none indexed by a proper divisor of $d$ can vanish modulo $p$, by minimality of the order. Each complex linear factor of $\Phi_d$ has absolute value at most $U+V$, and $\varphi(d)\mid\varphi(g_p)$ since $d\mid g_p$. This necessary bound applies simultaneously to all such rational representatives for a given $p,s$.

In particular, on almost all pairs of distinct primes $p,q\in[Y,2Y]$, **no** positive rational with distinct numerator and denominator at most $\exp(h)$ gives a local relation at either prime after the default powering, for any $h=o(\log Y)$. This holds simultaneously for every positive scalar whose odd part divides $N-1$, $N=pq$. The assertion includes signed equalities by doubling the scalar. For the proof set $X=\log Y/(2(h+\log 2))$, which tends to infinity. At $p$ the gcd of any allowed scalar with $p-1$ divides $a g_0$, where $a$ is the full power of two in $p-1$ and $g_0$ is the odd part of $\gcd(p-1,q-1)$. Indeed $N-1\equiv q-1\bmod(p-1)$. If $ag_0<X$, the displayed cyclotomic bound would give $p\le\sqrt Y$. The same argument works at $q$.

For completeness the proportion where $a g_0\ge X$ at either prime is
\[
 O\!\left(\frac{\log(2X)}X+\frac{\log(2X)(\log Y)^2}{\sqrt Y}\right).
\]
The event $a>X$ is bounded by $O(1/X)$ by counting primes in one class modulo the first power of two above $X$. For each dyadic $a\le X$, sum over odd $d\ge X/a$ dividing both predecessors, including $d=g_0$. When $ad\le\sqrt Y$, Brun–Titchmarsh in the classes $p=1\bmod ad$, $q=1\bmod d$, normalized by the dyadic prime count, gives a total proportion $O(a^{-1}\sum_{d\ge X/a}\varphi(d)^{-2})=O(1/X)$. The tail estimate follows from $\sum_{n\le x}(n/\varphi(n))^2=O(x)$ by dyadic summation. For this mean bound expand $(n/\varphi(n))^2=\prod_{\ell\mid n}(1+c_\ell)$ with $c_\ell=(1-1/\ell)^{-2}-1=O(1/\ell)$, then bound the mean by $\prod_\ell(1+c_\ell/\ell)<\infty$. For $ad>\sqrt Y$, counting integer multiples in the two predecessors gives total proportion $O((\log Y)^2 a^{-1}\sum_{d>\sqrt Y/a}d^{-2})=O((\log Y)^2/\sqrt Y)$. Only moduli $ad\le2Y$ can occur. Sum over the $O(\log(2X))$ powers of two and interchange $p,q$. For the single scalar $s=N-1$ both local gcds equal $\gcd(p-1,q-1)$, so the same count with the common divisor alone omits the $\log(2X)$ factor. [Montgomery and Vaughan, The large sieve](https://doi.org/10.1112/S0025579300004708)

For a polynomial-size menu of primes bounded by a power of $\log N$, any signed support $o(\log N/\log\log N)$ has logarithmic height $o(\log N)$. Thus on almost all balanced semiprimes the default scalar still gives zero nontrivial relations on the entire union of these short candidates, regardless of the search order. Other scalars and bases of greater rational height can change this conclusion. An exact finite check tested the displayed cyclotomic implication in 149,940 combinations of two primes, a scalar, a local prime and a reduced ratio, including 10,170 local equalities.
