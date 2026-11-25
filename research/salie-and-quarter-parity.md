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
