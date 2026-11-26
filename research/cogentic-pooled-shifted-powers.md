# Pooling the shifted powers of the input

Let $N=pq$ and take the odd part of every $N^k-1$ and $N^k+1$ for $1\le k\le R$ into one exponent. On a density-one set of balanced prime pairs the resulting residual orders remain at least $X^{1/2-o(1)}$ at both factors, even with a subpolynomial smoothness scalar and an entire subpolynomial base list. An unbalanced family shows that $N+1$ can nevertheless split inputs where the older $N-1$ scalar and bounded residual searches fail. [Partial odd-order searches and the shared factor $N-1$](cogentic-partial-odd-orders.md)

## A bound for all the shifted powers at once

For $X<p<q\le2X$ choose $A,Y\ge2$ and $R\ge1$ with $A,Y,R=X^{o(1)}$. Let $S_Y$ be the odd product of the largest powers at most $N$ of the primes through $Y$. Use the scalar
\[
E=S_Y\operatorname{odd}\!\left(\prod_{k=1}^R(N^{2k}-1)\right).
\]
This equals the pooled signed product after removing powers of two. Its bit length is $O((R^2+Y)\log N)$, and it is computable within a polylogarithmic factor of that bound by a sieve, successive powers and a product tree using fast integer arithmetic. At one-third cutoffs, the setup cost is $\exp(O(W))$ for $W=(\log N)^{1/3}(\log\log N)^{2/3}$. The estimates below also allow choosing smaller cutoffs or a subproduct after seeing $N$.

Set $T=\lceil\max(Y,R^2,\log X)\rceil$. Suppose a prime $\ell>T$ divides $p-1$ and a tested $N^k\pm1$. As $N\equiv q\pmod\ell$, its $q$ coordinate is a root of $x^{2k}-1$ over $\mathbb F_\ell$. For the whole test list there are at most $\sum_{k\le R}2k=R(R+1)$ possible $q$ classes, all units. The exact count is
\[
 \sum_{d\mid\ell-1,\ d/\gcd(d,2)\le R}\varphi(d),
\]
because a unit of order $d$ occurs precisely when $d$ divides some $2k$ with $k\le R$.

For $T<\ell\le\sqrt X$, Brun–Titchmarsh bounds the proportion of dyadic primes in any one unit class by $O(1/\ell)$, uniformly up to the endpoint $\sqrt X$. Apply this on both coordinates, one of which has the fixed class $1\bmod\ell$. The total exceptional proportion is at most $O(R^2\sum_{\ell>T}1/\ell^2)=O(R^2/(T\log T))$, by the ordinary prime counting upper bound. For $\sqrt X<\ell\le2X$, a unit class has at most $1+X/\ell\le3X/\ell$ integers in the interval. Counting integers for both coordinates then gives $O(R^2(\log X)^2/\sqrt X)$ after summing over all integer moduli in this range and dividing by the number of prime pairs. Both bounds also apply with the roles of $p,q$ reversed. Thus
\[
 \Pr[\exists\,\ell>T\text{ removed from either predecessor}]
 \ll \frac{R^2}{T\log T}+\frac{R^2(\log X)^2}{\sqrt X}=o(1).
\]
The union bound treats the full product. The increase from $Y$ to $T$ takes place in the estimate for the removed part. When $Y<R^2$, it allows every factor between $Y$ and $R^2$ to contribute to that part. [Montgomery–Vaughan, Brun–Titchmarsh](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf)

On every remaining pair the common divisor of $2^{\operatorname{bitlength}(N)}E$ and each predecessor is bounded by that predecessor's full $T$-smooth part. This also controls the contribution of arbitrarily high powers of the primes at most $T$. Set $\eta=\sqrt{(\log(2A)+\log(2T)+\log\log X)/\log X}$. Outside a further exceptional set of proportion $o(1)$, the [prior estimates](cogentic-partial-odd-orders.md#density-of-failure-for-short-integer-bases-and-the-shared-factor-scalar) bound both $T$-smooth parts by $X^\eta$ and every local order of the integers $2\le a\le A$ exceeds $X^{1/2-\eta}$. Hence every pooled residual order is at least $X^{1/2-2\eta}$ at both factors. All repeated squares have the same odd orders as their starting bases. The same conclusion holds for catalogues of $M$ nonidentity rational words of log height at most $H_0$ when $M H_0=X^{o(1)}$, by the rational difference product in the prior estimate. Use $\log(2+MH_0)$ in place of $\log(2A)$ in $\eta$.

## A family where the positive shift adds a split

For all large $P$, there are unconditionally $\gg P^3/(\log P)^2$ distinct products with primes
\[
 P<p\le2P,\qquad P^3<q\le2P^3,\qquad q\equiv-1\pmod{p-1}.
\]
For each prescribed $A,Y=P^{o(1)}$ with $A,Y\ge2$, at least this many products have the following extra property. The old exponent $\operatorname{odd}(N-1)S_Y$ leaves odd residual orders exceeding $P^{1/4}$ at both factors for every base $2\le a\le A$. The exponent $N+1$, used directly, splits every product in the displayed family in polynomial bit time. Since $p-1\mid N+1$, each unit base of the power map gives the identity modulo $p$. Modulo $q$, its kernel has order $\gcd(q-1,N+1)=\gcd(q-1,p+1)\le p+1$.

To find a base outside that kernel unconditionally, take $B=\operatorname{bitlength}(N)^2$. Set $J=\lfloor\log(q-1)/\log B\rfloor$ for the counting argument. The products of $J$ distinct primes at most $B$ are distinct integers below $q$. There are at least $(\pi(B)/J)^J=q^{1/2+o(1)}$ such products, whereas $p+1=q^{1/3+o(1)}$. If all primes through $B$ belonged to the kernel their products would as well. At least one of those primes therefore gives $\gcd(a^{N+1}-1,N)=p$. The algorithm tests all integers through $B$ and needs only $N$.

To count the products with the older scalar's failure, first use the low-order product with $K=\lfloor P^{1/3}\rfloor$. Among primes in either dyad, at most $P^{2/3+o(1)}/\log P$ have any listed base of order at most $K$. In the first dyad also discard primes with $Y$-smooth part of $p-1$ above $P^{1/12}$ by the earlier smooth-part estimate. This leaves $\gg P/\log P$ choices of $p$.

At $X=P^3$, Bombieri–Vinogradov bounds the sum of the absolute prime-sum errors on $(X,2X]$ over moduli $m\le2P$ by $O(X/(\log X)^3)$. Thus at most $O(P/(\log P)^3)$ moduli have error above $X/(4P)$ in the class $-1\bmod m$. After discarding the corresponding choices of $p$, each remaining $m=p-1$ has a main term $X/\varphi(m)\ge X/(2P)$. Removing prime powers costs $O(\sqrt X\log^2 X)$ in von Mangoldt weight, leaving $\gg P^3/(\varphi(m)\log P)$ primes in the progression. The exceptional low-order primes are negligible even relative to this restricted count. [Bombieri–Vinogradov](https://doi.org/10.1112/S0025579300005313)

Within this progression, $q\equiv1\bmod\ell^j$ for odd $\ell\mid m$ is impossible. In every compatible case the joint class modulo $\operatorname{lcm}(m,\ell^j)$ is a unit class, and the ratio of totients $\varphi(m)/\varphi(\operatorname{lcm}(m,\ell^j))$ is at most $2/\varphi(\ell^j)$. When $\ell\nmid m$ this follows by coprimality. When $\ell=2$ divides $m$, either $4\mid m$ and $j\ge2$ is incompatible, or the overlap has totient one. If $\ell^j\le P^{1/4}$, the joint modulus is below $\sqrt X$, and Brun–Titchmarsh divided by the progression's lower bound gives probability $O(1/\varphi(\ell^j))$. For each $\ell\le Y$ the first power above $P^{1/4}$ is at most $YP^{1/4}$, and its joint modulus is still below $\sqrt X$. The probability of any such power is $O(Y P^{-1/4})=o(1)$. The expected log contribution from the smaller powers is $O(\log(2Y))$, so a proportion $1-o(1)$ of the progression also has $Y$-smooth part at most $P^{1/12}$. All these estimates are uniform in the fixed first prime. [Montgomery–Vaughan, Brun–Titchmarsh](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf)

For every retained pair, $q-1\equiv-2\bmod(p-1)$ implies $\gcd(p-1,q-1)=2$. Thus the odd part of $N-1$ removes no odd factor of either predecessor, and the powers of two and the smooth scalar together remove at most $P^{1/12}$. Dividing the two raw order bounds by this gives the claimed residuals. The prime intervals are disjoint so distinct pairs give distinct inputs. The splitting procedure takes $N$ alone.

For example, $N=4{,}881{,}749=47\cdot103{,}867$ splits at base two using $N+1$. At $Y=5$, the old odd shift plus smooth scalar leaves local orders $23,17311$ after removing the 2-parts.

The finite check compared 1,664 cyclic root counts and 2,320 local predecessor supports with the signed-power tests and verified the displayed split.
