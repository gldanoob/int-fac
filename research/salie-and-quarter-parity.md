# A Salié sum for the centered parity bit

For an odd modulus $n$ write $e_n(x)=\exp(2\pi i x/n)$, $\epsilon_n=1$ if $n\equiv1\pmod4$ and $i$ otherwise. For a unit $t$ define the real normalized Salié sum
$$
W_n(t)=\frac{(t/n)}{\epsilon_n\sqrt n}
\sum_{u\bmod n}^{*}\left(\frac{u}{n}\right)e_n(t(u+u^{-1})),
$$
where the symbols are Jacobi symbols. The summand and the normalization are computable from $n,t,u$. The classical Salié evaluation gives exactly
$$
W_n(t)=\sum_{w^2=1\bmod n} e_n(2tw).
$$
Here the modulus of the character sum is the original integer $n$. For inputs with two distinct odd prime divisors, including repeated factors, one such real number evaluates each centered quadratic floor-sum parity bit. The direct sum still has $\varphi(n)$ terms.

For a proof of the classical formula, hold $b$ coprime to $n$ fixed. The Fourier transform in $a$ of $\sum_{y^2=4ab\bmod n}e_n(y)$, with kernel $e_n(-au)$, is $\sum_y e_n(y-u(4b)^{-1}y^2)$. It vanishes at nonunits $u$ because the linear coefficient is one. At a unit, completing the square gives $e_n(bu^{-1})(-bu/n)G_n$, where $G_n=\epsilon_n\sqrt n$ is the ordinary quadratic Gauss sum. Inverting and using $G_n^2=(-1/n)n$ gives the Salié identity at $a=b=t$. This proof works for odd composite moduli and imprimitive Jacobi symbols as well. [Williams, Salié's prime-modulus formula](https://people.math.carleton.ca/~williams/papers/pdf/044.pdf) · [Chen and Wang, equations (2.1)–(2.3) and the Gauss-sum lemma](https://dml.cz/bitstream/handle/10338.dmlcz/151785/CzechMathJ_73-2023-3_19.pdf#page=5)

## The shifted comparison at one dyadic center

Suppose $n$ has exactly two distinct prime divisors. Let $r$ denote either of its two mixed roots of one, and take $2t\equiv c\pmod n$ at the desired dyadic center. The rational roots contribute explicitly:
$$
W_n(t)-2\cos(2\pi c/n)=2\cos(2\pi cr/n).
$$
The right side is positive exactly when one of $\pm cr$ contributes to the first quarter. XOR this comparison with the known contribution of $\pm c$ to obtain the centered floor-sum parity after removing the midpoint. This is a direct formula for the bit at the requested center. [Centered floor identity and digit convention](floor-sum-and-log-parity.md#nonadaptive-queries-for-two-distinct-prime-divisors)

When $16c^2<n$, the absolute margin in this comparison is at least $2/\sqrt n$. Let $z=4cr-(2j+1)n$ have smallest possible absolute value. Then $z$ is odd and $z^2\equiv16c^2\pmod n$. Its square differs from the even square $16c^2$ and cannot lie below it, since $16c^2<n$. Therefore $|z|\ge\sqrt{n+16c^2}$. The distance of $cr/n$ from the nearest quarter boundary is $|z|/(4n)$, and $\sin y\ge2y/\pi$ on $[0,\pi/2]$ gives the margin. **Absolute error less than one in the unnormalized Salié sum** therefore suffices to recover each of these bits with room for rounding the public threshold. These centers give all but a constant number of the digits needed for a split. Indeed the largest admissible dyadic $c$ is within a constant factor of $\sqrt n$, so the resulting digit interval has length $O(\sqrt n)$. A constant number of translated short-root searches finish the two-prime factorization. [Coppersmith, Corollary 1](https://www.di.ens.fr/~fouque/ens-rennes/coppersmith.pdf#page=11)

For arbitrary odd inputs, the original-modulus sign decoder transfers to $W_n(t)$ verbatim with cyclic order $n$ in place of $n^2$. Its local orders are now the prime powers $p^e$ themselves. CRT still gives two local signs and a cosine at each block; all estimates on the rough residual use odd orders and large least prime only. To transfer a unit query across removed factors, set its local phase at a known block $D$ to one. The sign there is known, so multiply it out. This gives the same $2^{O(R)}\operatorname{poly}(\log n)$ nonadaptive work and queries for $R$ distinct primes, or $2^{O(\sqrt{\log n})}$ on arbitrary inputs, with every sign queried at $n$. [Original-modulus sign decoder and approximation proof](kloosterman-localization.md#sign-decoding-with-logarithmically-many-prime-factors)

The polynomial-time magnitude-threshold reduction transfers to one modulus $m=nH$ with $\log H=O(b^{2/3}\log b)$, $b=\lceil\log_2(2n)\rceil$. Use local orders $p^e$ throughout and scale a residual frequency by $m/n_{\rm residual}$ in the CRT transfer. At each removed known block choose a unit within two of $D/6$; the total known log magnitude is now $O(\log b)$ since the distinct block sizes have reciprocal sum $O(\log b)$. This is absorbed in the $O(b^{2/3})$ gain range. Each fresh padding prime in $[b^2,2b^2]$ contributes an $O(b^{-2})$ log gain error and all such errors sum to $o(1)$. The Fourier frequencies of single local logarithms have additive orders equal to the full blocks themselves. All remaining isolation, gap and verification estimates follow as before. Thus the twisted-sum modulus has $b+o(b)$ bits. A fast unrestricted evaluator remains open. [Gap comparison and CRT proof](kloosterman-threshold.md)

## Evaluating the unshifted sign at low frequencies

There is an unconditional, oracle-free evaluation on a restricted range. Let $Q$ have exactly two distinct odd prime factors, with prime-power blocks $U,V$. Use the root sum $W_Q(t)$ above. If $Q=n^2$, it is also the classical untwisted Kloosterman sum at $n^2$ divided by $n$. For a unit $t$ let $a$ be the least absolute representative of $2t\bmod Q$ and put $B=2|a|$. Then $W_Q(t)$ is negative if and only if there is a nonnegative odd integer $z<B$ such that
$$
                   z^2=B^2-kQ,\quad k\ge1,\qquad z\not\equiv\pm B\pmod Q.
$$
Indeed the two cosine pairs give a negative sum exactly when $ar/Q$ is closer to a half-integer than $a/Q$ is to an integer. Clearing denominators gives an odd $z$ with $|z|<B$ and $z\equiv2ar\pmod Q$. Conversely any listed square reconstructs a mixed root by division by $2a$; oddness ensures the subtracted multiple of $Q$ is odd. Changing the sign of $z$ preserves all tests. None of the local cosine factors vanishes on an odd grid.

Testing $k\le B^2/Q$ by integer square roots takes $O(1+B^2/Q)\operatorname{poly}(\log Q)$ deterministic bit operations from the modulus and frequency alone. Only $k\equiv(B^2-1)Q^{-1}\pmod8$ need be tested. In particular all queries with $|a|\le\sqrt Q\operatorname{poly}(\log Q)$ have a polynomial-time evaluator, and $B^2<Q$ gives a positive sign immediately. The shifted comparison in the preceding section uses a different threshold.

For larger $B$, cover $[0,B)$ by $O(1+B/\sqrt Q)$ intervals of radius at most $\lfloor\sqrt Q\rfloor$. In each, translate the monic quadratic $Z^2-B^2$ and list its small roots modulo $Q$. Keep odd representatives in the interval and discard the two trivial residues. This reduces the deterministic evaluation cost to $O(1+B/\sqrt Q)\operatorname{poly}(\log Q)$. [Coppersmith, §6, Corollary 1](https://www.di.ens.fr/~fouque/ens-rennes/coppersmith.pdf#page=11)

There is also an exact formula for the **first negative unit frequency** of the ordinary Kloosterman sum at $n^2$. Suppose $n$ has two odd prime-power blocks, $7\nmid n$, and write their squares as $U<V$, so $Q=UV$. Then this first frequency is
$$
                          t_*=\frac{7U+V}{8}.
$$
In fact $8t_*<Q$ since $U\ge9$, $V\ge25$, and $t_*$ is a unit by coprimality and $7\nmid n$. For a unit $t<Q/8$ we have $B=4t$; the two positive odd integers $B-z,B+z$ have sum $8t<Q$ and product divisible by $Q$. They share no prime divisor of $Q$ since $\gcd(2B,Q)=1$. Hence they must be $uU$ and $vV$ in some order for positive odd $u,v$. Conversely such a pair gives an odd $z$ by taking half the absolute difference, and it gives the mixed root because each summand is below $Q$. Both square blocks are one modulo eight. Therefore $u+v\equiv0\pmod8$, and the smallest possible weighted sum is $7U+V$, obtained by putting as much weight as possible on the smaller block. This proves the formula. From a supplied $t_*$ the quadratic $7U^2-8t_*U+Q=0$ recovers the blocks. If $7\mid n$, ordinary division already identifies one of the two prime types. Finding the first sign change efficiently from $n$ is a separate problem.

The finite replay compares 6,746 literal twisted sums at odd moduli through 181 against exact root enumeration. It compares the integer sign test at all 2,708 two-prime unit inputs in that sweep and checks 106 centered floor sums by direct integer summation. Nine square-modulus fixtures verify the first negative frequency, including inputs with repeated prime factors. Run `python3 -B experiments/salie-quarter.py`. [Independent finite checks](../experiments/salie-quarter.py)

## A comparison that works without the factors

Write $c=2t\bmod Q$ in $[0,Q)$ and $s(y)=\operatorname{sgn}\cos(2\pi y)$. The elementary comparison $s(c/Q)$ uses just $c,Q$. For two large prime-power blocks it predicts the sign of $W_Q(t)$ on a proportion tending to $3/4$ of unit frequencies. Its agreement with the mixed-root bit at the same frequencies tends to $1/2$. These proportions concern uniform unit frequencies. The prescribed dyadic centers are a different sampling problem.

**The exact exceptions for two blocks.** Let $Q=UV$ with distinct odd prime-power blocks, and let $k$ be the absolute least residue of $2c$ modulo $Q$. Then
$$
 \operatorname{sgn} W_Q(t)\ne s(c/Q)
 \quad\Longleftrightarrow\quad
 k=\frac{U+V}{2}+iU+jV\quad\text{for integers }i,j\ge0.
$$
Consequently the first disagreement in this ordering occurs at $k_*=(U+V)/2$. It is a unit and is attained for either sign of the centered residue. Thus every frequency with $k<\sqrt Q$ has an exact comparison from the input alone. A supplied first disagreement determines the two prime powers by the quadratic $Z^2-2k_*Z+Q=0$. This holds at the original twisted modulus and at the ordinary square modulus.

To see the criterion, let $x=(cV^{-1}\bmod U)/U$ and $y=(cU^{-1}\bmod V)/V$. The root sum factors as $4\cos(2\pi x)\cos(2\pi y)$ and $x+y\equiv c/Q\bmod1$. Let $h/U$ and $l/V$ be the centered representatives of $2x$ and $2y$ modulo one. Writing $2x$ as its nearest integer plus its centered part shows that $s(x)s(y)s(x+y)$ is negative precisely when $|h/U+l/V|>1/2$. In that case $h,l$ have the same sign and
$$
              2k=(U-2|h|)V+(V-2|l|)U.
$$
Conversely, if $2k=aV+bU$ for positive odd $a,b$, the bound $2k<Q$ gives $a<U,b<V$. The centered numerators $(U-a)/2,(V-b)/2$ give the sum $1-k/Q$ and its negative gives the opposite residue. These are exactly the two frequencies with this $k$. The first disagreement follows by taking $a=b=1$.

The same proof gives an input-only evaluator beyond the guaranteed range. Disagreement holds precisely when $k^2-jQ=z^2$ for a **positive odd** $j$ and integer $0\le z<k$. In one direction take $z=|aV-bU|/2$ and $j=ab$. In the other, $k-z,k+z$ are positive odd integers below $Q$ whose product is divisible by $Q$. Since $k$ is a unit, the two prime-power blocks divide opposite factors. Enumerating the odd multiples costs $O(1+k^2/Q)\operatorname{poly}(\log Q)$. Alternatively use the translated quadratic small-root searches above on $[0,k)$ and retain the opposite parity to $k$. This costs $O(1+k/\sqrt Q)\operatorname{poly}(\log Q)$. Both bounds apply near the half-integer as well as near the integer.

There is an exact count of the errors. Define $T(u,v)$ to count positive odd pairs $a,b$ with $a/u+b/v<1$. If $p\mid U$ and $q\mid V$ are the base primes, there are
$$
  2\big[T(U,V)-T(U/p,V)-T(U,V/q)+T(U/p,V/q)\big]
$$
wrong unit frequencies. The same-sign centered choices give the factor two. Removing the requirements $p\nmid a$, $q\nmid b$ gives the four terms. Each $T$ is an ordinary linear floor sum and can be evaluated by the Euclidean algorithm from the supplied orders. For the mixed-root bit $s(x-y)$, agreement with $s(x+y)$ is equivalent to $\cos(4\pi x)+\cos(4\pi y)>0$, or $|h|/U+|l|/V<1/2$. Reflection independently in each local grid shows that exactly twice as many unit frequencies fail this second comparison as fail the unshifted one.

**More than two prime factors.** Let $Q=\prod_iD_i$ have $r$ odd prime-power blocks. Its sign is $\prod_i s(x_i)$ for $x_i=(c(Q/D_i)^{-1}\bmod D_i)/D_i$, and $\sum x_i\equiv c/Q\bmod1$. For independent continuous uniform $X_i$ on the circle, the conditional mean of the sign product given $Y=\sum X_i\bmod1$ is the $r$-fold convolution $C_r=s^{*r}$. Its sign is $s(Y)$ away from the quarter boundaries. Indeed all $C_r$ are even and change sign under a half-turn. For $0<y<1/2$, integrating over the central half gives $C_r'(y)=-4C_{r-1}(y-1/4)$ almost everywhere, proving the sign by induction. The optimal accuracy given the sum is
$$
 P_r=\frac12+\left(\frac2\pi\right)^{r+1}
       \sum_{j>0\text{ odd}}\frac{(-1)^{(r+1)(j-1)/2}}{j^{r+1}} .
$$
The series follows by integrating $sC_r$ using the Fourier coefficients of $s$. For two blocks, $C_2(y)=1-4\|y\|$ and $P_2=3/4$. For three, $\int s C_3=\int C_2^2=1/3$, giving $P_3=2/3$. For two blocks the map $(X_1,X_2)\mapsto(X_1+X_2,X_1-X_2)$ preserves uniform measure on the torus, giving accuracy $1/2$ for predicting the mixed bit from the sum.

These continuous bounds persist for finite public comparisons. Allow a predictor to see $c\bmod m$ with $(m,Q)=1$ and to use up to $K$ interval boundaries in $c/Q$ for each residue. Its accuracy is at most $P_r+O((K+1)m\sum_iD_i^{-1})$. The two-block mixed bit has upper bound $1/2$ with the same error. For $s(c/Q)$ itself use $m=1,K=2$ for an absolute error bound in either direction. For two blocks, restricting this public prediction to $\operatorname{dist}(c/Q,\tfrac12\mathbb Z)\le\delta\le1/4$ gives coverage $4\delta+O(\sum_i D_i^{-1})$ and joint error probability $4\delta^2+O(\sum_iD_i^{-1})$. This follows by integrating the conditional error $2\operatorname{dist}(y,\tfrac12\mathbb Z)$ on those intervals.

For the discrete approximation, the local numerators $a_i=D_i x_i$ are independent and uniform over their unit grids by CRT. In any given class modulo $m$, the number of units in an interval of length $L$ is $(1-1/p_i)L/m+O(1)$ by subtracting the multiples of $p_i$. Couple $a_i\bmod m$ to an independent uniform label $Z_i$ with failure $O(m/D_i)$. Given the labels, couple $x_i$ to an independent uniform $X_i$ by matching quantiles, with distance $O(m/D_i)$ when the labels agree. The estimate is trivial if the error bound is of constant size. Otherwise $\lfloor\sum x_i\rfloor$ agrees with $\lfloor\sum X_i\rfloor$ except with probability $O(m\sum_iD_i^{-1})$, since the continuous sum modulo one is uniform. The continuous label $\sum_i (Q/D_i)Z_i-Q\lfloor\sum X_i\rfloor\bmod m$ is uniform independently of all $X_i$ and agrees with the actual label outside these exceptions. Crossing a local sign boundary or a predictor boundary costs at most the stated additional error. This comparison concerns a fixed modulus and varying diagonal unit frequencies. Related distribution results for short sums at varying prime powers use a different family. [Ricotta, Royer and Shparlinski](https://ambp.centre-mersenne.org/articles/10.5802/ambp.385/)

**Counting all negative unit frequencies.** For any odd $Q$, let $A_Q$ count the negative signs among unit frequencies and let $\chi_4$ be the nontrivial character modulo four. Then
$$
 \varphi(Q)-2A_Q=\prod_{p^e\parallel Q}\big(\chi_4(p^e)-\chi_4(p^{e-1})\big).
$$
On the full odd grid of size $D$ the signed count is $4\lfloor D/4\rfloor+2-D=\chi_4(D)$. Subtract the nonunits, then multiply the local signed counts by CRT. At $Q=n^2$, the right side is $\prod_{p\mid n}(1-\chi_4(p))$, between zero and $2^{\omega(n)}<n$ for $n>1$. Hence **$\varphi(n)=\lceil2A_{n^2}/n\rceil$**. For odd $n\ge5$ the totient is even and $2^{\omega(n)}/n\le2/5$ (for two or more distinct primes use $4/15$). An additive error below $n/4$ in the count still gives the totient by rounding $2A_{n^2}/n$ to the nearest even integer. Computing that aggregate at the required precision from unrestricted $n$ remains open.

For blocks 101 and 103 the public comparison matches 7,600 of 10,200 unshifted signs and 5,000 mixed bits. The replay checks the count and the two-block triangle formula against individual unit frequencies. It includes primes, repeated prime powers, and inputs with three and four distinct primes. [Finite sign and count checks](../experiments/salie-quarter.py)

## Searching for a disagreeing frequency near a square root

For balanced two-block inputs, finding a single unit frequency where the public comparison is wrong and $k=O(\sqrt Q\,\operatorname{poly}(\log Q))$ would suffice to split the modulus in polynomial time. The odd-square test above then recovers $k-z$ and $k+z$, each divisible by one of the two blocks. Conversely, the blocks give a frequency at $k=(U+V)/2=O(\sqrt Q)$ whenever their ratio is bounded.

There is a density bound for schedules that search around public multiples of $\sqrt Q$. Fix an integer $e\ge1$ and let $Q=(pq)^e$ for ordered distinct primes $p,q\in[X,2X]$. Choose up to $m$ real coefficients $a_j\in[0,A]$, independently of the pair. They may vary with $X$. Allow every integer in every window $|k-a_j\sqrt Q|\le E$, with $E\ge1$. The fraction of prime pairs for which any such window contains a valid disagreement is
$$
 \ll_e \frac{m\log X}{X}(1+A+E/X^e)^2
                (1+X^{1-e/2}\sqrt E).
$$
For $m,A=X^{o(1)}$ and bounded $E$, this is at most $X^{-1/2+o(1)}$ at the input modulus and $X^{-1+o(1)}$ at its square. The result permits arbitrary choices of frequencies inside the windows.

Indeed each disagreement has $2k=u q^e+v p^e$ with $u,v$ positive odd and $u,v\ll_e 1+A+E/X^e$. Fix $p,u,v,j$ and set $z=q^{e/2}$. Then
$$
        |u z^2-2a_j p^{e/2}z+v p^e|\le2E.
$$
Completing the square shows that admissible real $z$ lie in at most two intervals of total length $O(\sqrt{E/u})$. On $[X,2X]$ the derivative of $q^{e/2}$ is bounded below by a constant times $X^{e/2-1}$. Hence there are $O_e(1+X^{1-e/2}\sqrt E)$ possible integers $q$. Summing over the coefficients and the first prime, and using the prime number theorem for the denominator, gives the claim.

At $e=1$ the exponent is attained by $k=\lceil\sqrt{pq}\rceil$. In fact this choice yields a unit disagreement exactly when $k=(p+q)/2$, the first square test in Fermat's method. The next semigroup element is at least $(p+q)/2+\min(p,q)>\lceil\sqrt{pq}\rceil$. For $p<q$ the exact criterion is $q<p+2+\sqrt{8p}$. Consequently the fraction among balanced prime pairs is $\Theta(X^{-1/2})$. The upper bound follows by Brun–Titchmarsh in intervals of length $O(\sqrt X)$. For the lower bound divide $[X,2X]$ into $O(\sqrt X)$ intervals of length at most $\sqrt X$. Every distinct pair in one interval passes. Cauchy–Schwarz applied to the prime counts in the intervals gives $\gg X^{3/2}/(\log X)^2$ such ordered pairs. [Montgomery and Vaughan, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf)

Across the primes in $[101,200]$, the integer square test and direct CRT signs agree on 4,173 unit frequencies in four square-root windows at exponents one and two. Of these, 198 disagree with the public prediction, including 105 first Fermat successes at exponent one. [Integer replay](../experiments/salie-quarter.py)
