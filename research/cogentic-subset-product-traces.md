# Trace invariants and canonical subset-product collisions

An exterior-power trace computes a complete power sum of the subset-product set cheaply. Its associated full recurrence measures the support of modular product residues with nonzero fiber weights. On the balanced one-third-size prime menu, reconstructing that recurrence requires nearly $\sqrt N$ degrees even though each trace is cheap. Short traces can still split particular inputs. A separate capped subset computation recovers a canonical collision when the local image is small, including when many global products repeat. [Sparse local words and determinant bounds](cogentic-short-order-lattice-determinants.md) · [Batched local gcd search](cogentic-unit-collision-search.md)

## What one low-degree trace computes

Take unit generators $a_1,\ldots,a_m$ modulo $N$ and fix $k$. Write $u_I=\prod_{i\in I}a_i$ for $|I|=k$ and $M=\binom mk$. In the $k$th exterior power of the diagonal generator matrix the eigenvalues are exactly the $u_I$. Thus
\[
S_j=\sum_{|I|=k}u_I^j=e_k(a_1^j,\ldots,a_m^j).
\]
Multiply the factors $1+a_i^j Z$ successively, retaining only degrees through $k$, and take the coefficient of $Z^k$. This uses $O(mk)$ operations in the residue ring per $j$ after computing the powers, with no division. Consecutive powers can be updated by one multiplication per generator. A list $S_0,\ldots,S_D$ supplies every aggregate $\sum_I Q(u_I)$ for $\deg Q\le D$. It also supplies the paired power aggregates
\[
\sum_{I,J}(u_I-u_J)^d=\sum_{j=0}^d(-1)^j\binom dj S_{d-j}S_j
\qquad (0\le d\le D).
\]
Assigning a public multiplicative tag $z_i$ to each generator changes the same recursion to $e_k(z_i a_i^j)$. A tag keeps the total weight of a fiber, while the identities of the individual supports need additional information.

At a prime $p\mid N$, a polynomial of a difference alone that equals one at zero and vanishes at all other residues has degree at least $p-1$. The smallest such polynomial is $1-X^{p-1}$. Thus an exact collision count over all residues modulo $p$, made by inserting this indicator into the paired trace formula, reaches degree $p-1$ and gives a count modulo $p$.

## Full recurrence degree and short-prefix ambiguity

At a prime divisor $p$, write $w_p(x)=\#\{I:u_I\equiv x\pmod p\}$. The power sequence modulo $p$ is $S_j=\sum_x w_p(x)x^j$. Let $d_p$ count the residues for which $w_p(x)\ne0\pmod p$. A polynomial $Q$ annihilates the sequence if and only if $Q(x)=0$ on these residues. To see the converse direction, for shifts $j=0,\ldots,d_p-1$ the recurrence equations form a Vandermonde system on the unknowns $w_p(x)Q(x)$. The minimal monic recurrence is therefore the product of $X-x$ over the retained residues.

The leading $d_p$ by $d_p$ Hankel matrix is invertible over $\mathbb F_p$, by its Vandermonde factorization with the diagonal weights $w_p(x)$. Every Hankel block with at least $d_p$ rows and columns has rank $d_p$ when indexed from zero. Smaller blocks can be singular even below the recurrence degree. For a semiprime, if both actual recurrence degrees are at most $T$ and are unequal, then the $T$ by $T$ Hankel block detects a factor using $2T-1$ traces. Run complete-pivot elimination over $\mathbb Z/N\mathbb Z$, checking every nonzero candidate pivot by gcd. In the absence of a proper gcd every pivot is a unit, and the eliminations preserve matching ranks at both primes. Thus unequal ranks necessarily expose a nonunit. The cost is $O(mkT+T^3)$ ring operations for this elementary implementation. A short prefix alone cannot certify the degree promise.

For the small prime fixture at $N=899$, take pair products from $2,3,5,7,11,13,17,19,23$. The first eleven traces, computed directly by the elementary symmetric recursion, are
\[
36,626,210,699,161,750,1,17,762,531,441\pmod {899}.
\]
The determinant of the leading $6$ by $6$ Hankel block is $435\bmod899$, with gcd 29. Its ranks at 29 and 31 are five and six, even though both full recurrence degrees are 22. This is a proper gcd from a short trace without forming any of the 36 pair products.

There is a general ambiguity for unweighted moment-only tests. Choose distinct primes $p,q$ with $q>2h$ and a subgroup $H\le\mathbb F_p^\times$ of order $h$ and index at least two. Use $k=1$. Give the $p$ coordinates of the first menu as $H$ and one disjoint coset, each listed once. Give the $p$ coordinates of the second menu as two copies of $H$. Give both menus the same $2h$ distinct nonzero $q$ coordinates in the same order, joining by CRT. All global residues in either menu are distinct. The first menu has no proper difference gcd, and the second has a local coincidence modulo $p$ between the two copies. Both menus have the same moments $S_0,\ldots,S_{h-1}$ modulo $N$, since the nonconstant moments vanish modulo $p$ on each coset and the $q$ coordinates agree. At $p=29,q=31,h=7$, use $H=\langle16\rangle$ and the coset $2H$ with $q$ coordinates $1,\ldots,14$. The shared trace prefix is $14,725,116,609,29,551,232$. The values 1 and 349 in the second menu give gcd 29. This ambiguity concerns arbitrary unit menus and unweighted prefixes. It leaves open tests using small-prime structure or adaptively chosen tags.

## Why the near-square-root product cloud has large recurrence degree

Let $N=pq$ be balanced, put $L=\log N$, $W=L^{1/3}(\log L)^{2/3}$ and $V=L^{2/3}(\log L)^{1/3}$. Use all primes through $B=\lfloor e^{cW}\rfloor$ for fixed $c>0$. Fix $\eta>1/(2c)$, set $U=\exp(L/2+\eta V)$ and take the maximal $k$ with $B^k<U$. The subset-count calculation gives
\[
\log M=\tfrac12 L+(\eta-1/(2c)+o(1))V.
\]
All the products are distinct integers below $U<N$. As $M>\max(p,q)$ eventually, local coincidences are forced at both primes.

At either prime $r\in\{p,q\}$, the multiplicity of any residue is at most $\lceil U/r\rceil=\exp((\eta+o(1))V)<r$. None of the occupied residues disappears from the power sequence modulo $r$. Hence
\[
d_r\ge M/\lceil U/r\rceil
\ge\exp\bigl(L/2-(1/(2c)+o(1))V\bigr).
\]
This is a support bound for the actual product cloud, beyond the determinant bound for the full generated group. An explicit full recurrence has that many degrees, outside one-third size. It does not exclude a low-degree factor test that bypasses recurrence reconstruction.

## A canonical witness with small modular support

Fix a cap $T\ge2$ and order the $k$-subsets lexicographically by their increasing generator indices. Keep the first $T$ **distinct global residues** with the earliest support representing each one. This list can be computed without following a long run of repeated products.

Process generator suffixes from right to left. At each suffix and size $j\le k$, form the ordered union of the include-current branch and the exclude-current branch. The include branch comes first, and its residues are the previous suffix's $(j-1)$-subset products multiplied by the current unit. Keep only first occurrences and truncate at $T$. Multiplication by a unit preserves distinctness within a branch. A saturated include branch fills the result by itself. Otherwise it has $r<T$ entries, and at most $r$ of the first $T$ exclude-branch residues can be repeats from the include branch. This proves that keeping the first $T$ distinct representatives at each state gives the exact first $T$ for the next state. The procedure takes $O(mkT)$ representative visits. A balanced lookup structure gives a deterministic logarithmic membership cost. Support lists add at most a factor polynomial in $k$ to time and storage.

If the global support contains fewer than $T$ residues, this gives the full support. If it contains at least $T$ and one local support has size less than $T$, those $T$ representatives force a proper gcd. One may apply the monic collision detector to two copies of the representative prefix. Its derivative step removes each exact self-match. Existence of a proper gcd is monotone as the prefix length increases. Binary search therefore gives the smallest later representative index in any colliding pair, then one linear scan finds the earliest preceding partner. This recovers the canonical word in that ordering under the small-support promise, with a softly linear collision cost in $T$ using fast polynomial arithmetic. The searched prefix can also be used without the promise, with exhaustion confined to that prefix.

For example, at $N=899$ use an ordered list with first generator 32 and 79 copies of 3, and choose $k=20$. All $\binom{79}{19}$ supports containing the first generator precede all supports excluding it, and give just one residue. The cap-two recursion keeps the supports $\{0,\ldots,19\}$ and $\{1,\ldots,20\}$ without traversing that run. Their products agree modulo 29 and differ modulo 31. For the distinct pair-product fixture above, the same canonical order first gives $46=2\cdot23$ and $15=3\cdot5$, with gcd 31. This is separate from the gcd 29 found by the short Hankel determinant.

The cap preserves ordering through repetitions. In the natural injective cloud below $N$, its first $T$ representatives are already the first $T$ subsets. The local support lower bound in that cloud is too large for the promise at one-third size. An exact check on 800 small lists verified both the capped representatives and the trace recursion against direct enumeration. The remaining selection problem is to exploit the large supply of sparse relations on that cloud within the one-third budget.
