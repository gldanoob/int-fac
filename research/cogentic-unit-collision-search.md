# Bounded local collision search for unit-corrected roots

The explicit unit chart gives two modular root progressions on any eligible odd $N$. A bounded search can find a proper cross-difference gcd even if no corrected squares agree modulo all of $N$. The detector is exhaustive on its two finite lists, including over prime powers. [Sage/NTL replay](../experiments/cogentic-unit-collision-search.py) · [Unit chart](../experiments/cogentic-unit-corrected-family.gp)

## Unit chart and the two tests

For the integer parameter $t$, test $t,t-1,t+1,t^2+1$ for coprimality with $N$. A proper gcd is a direct parameter certificate. If any fails with gcd $N$ and there is no proper parameter gcd, skip that parameter. For eligible $t$, use
\[
A=\frac{t(t-1)}{t+1},\qquad B=\frac{t-1}{t(t+1)},\qquad
x_i=\frac{A+1}{2}A^i,\qquad y_j=\frac{B-1}{2}B^j
\pmod N.
\]
The two starting roots and the two multipliers are units by the eligibility tests. For example, $(A+1)/2=(t^2+1)/(2(t+1))$ and $(B-1)/2=-(t^2+1)/(2t(t+1))$. Build each list by multiplication from exponent zero through one less than its supplied length.

The local search asks whether $1<\gcd(x_i-\epsilon y_j,N)<N$ for some $\epsilon\in\{1,-1\}$. That gcd itself is a factor certificate. A full corrected-square agreement additionally requires $x_i^2\equiv y_j^2\pmod N$. The two conditions are recorded independently. In particular, a full square agreement can have a productive mixed sign even when no signed root equality holds modulo $N$.

## Exact product buckets with global hits removed

For a generic bipartite search, reduce both lists modulo $N$ and keep one index per distinct residue. For the unit test, the right list has both signed residues for every $y_j$. Let $Y$ be the deduplicated right set and form the polynomial
\[
P(X)=\prod_{y\in Y}(X-y)
\]
over $\mathbb Z/N\mathbb Z$. Evaluate $P$ and $P'$ at every distinct left residue using a balanced monic product tree of $X-x_i$ and downward remainders. The only polynomial divisors are monic, so zero divisors in the coefficient ring cause no inversion. The replay uses Sage's dense NTL backend over the residue ring, including past 64 bits.

If $x\notin Y$, use the bucket $P(x)$. When $x\in Y$, its exact factor would make this product identically zero. Instead use
\[
P'(x)=\prod_{y\in Y\setminus\{x\}}(x-y).
\]
Deduplication is essential for this identity to remove every exact residue from the bucket. Candidate gcds of a bucket and $N$ detect whether at least one of the remaining differences is divisible by a prime of $N$. In the first bucket with nonunit gcd, scan the distinct right residues except $x$ and return the first proper gcd of a difference. This scan succeeds even when the bucket gcd equals $N$. A prime divides some factor of the product, and each scanned factor is nonzero modulo $N$. The same argument handles repeated prime factors of $N$. At most one row is scanned, regardless of how many buckets would saturate.

With fast polynomial multiplication and monic remainder, the tree work for left and right lengths $L,R$ takes softly linear polynomial work in $L+R$ over ring elements. Each product-tree level has total degree at most $L+R$. Fast monic remainders can use reversal and Newton inversion of the reversed divisor, whose constant coefficient is one. The remaining work uses $O(L+R)$ modular multiplications and gcds or hash-table operations in the implementation. The worst extra scan takes $O(R)$ gcds. These are bounds in the supplied box sizes. They give no bound on a box that has a hit for an arbitrary input. [Earlier monic collision search](round-2.md#rational-power-collision-search) · [Sage implementation](../experiments/cogentic-unit-collision-search.py)

## Global square agreement in parallel

Hash the right residues by their squared values and, within each bucket, retain representatives of at most two distinct classes up to global sign. For each left square, a nonempty bucket proves full agreement. If it contains two sign classes, at least one differs from the left root up to sign. Both corresponding signed differences are then nonzero modulo $N$, while their product is zero, so at least one gives a proper gcd. If the bucket has one sign class, testing a representative in both signs is sufficient. This also detects proper gcds from opposite signs of globally identical nonunit roots in the generic alignment check. The hash pass records full alignment and a productive fully aligned pair separately from the product-tree witness.

Run `python experiments/cogentic-unit-collision-search.py` for 4,106 comparisons with brute force and the explicit controls. With `341 --t 2 --left 3 --right 3`, the first local witness is $(i,j,\epsilon)=(0,1,-1)$ and gives 11 even though those two squares differ modulo 341. The same box has a globally aligned split at $(2,2)$. With $N=77$ and the same settings, the local gcd is 11 and no pair has full corrected-square agreement. These are fixed examples. The replay also checks exact residue duplicates, derivative saturation, prime-power saturation, and an empty box.
