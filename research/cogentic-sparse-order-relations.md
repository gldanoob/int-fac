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
