# Reducing diagonal Salié queries to frequency one

For odd $n$ and a unit $t$ let $W_n(t)=\sum_{r^2=1\bmod n}e_n(2tr)$ be the real normalized Salié sum. Each sign $\operatorname{sgn}W_n(t)$ is computable from $O(\log n)$ **nonadaptive sign queries at frequency one** on odd moduli at most $n^3$, with deterministic polynomial additional work. The same reduction expresses $\log|W_n(t)|$ as an alternating sum of frequency-one log magnitudes and explicitly known terms. Thus an inverse-polylogarithmic approximation to a single real number per odd modulus, $\log|W_m(1)|$, is polynomial-time equivalent to complete integer factoring. These are reductions to an evaluator. The cost of computing the fixed-frequency sum directly on an unfactored modulus remains open.

### A descent with a known power of three

The two roots at each odd prime power $D$ give the local factor $2\cos(4\pi t/D)$, which is nonzero on the odd unit grid. For odd coprime $a,b$, CRT gives
$$
 W_{ab}(1)=W_a(b^{-1}\bmod a) W_b(a^{-1}\bmod b).
$$
The trace is even in its frequency. Set $W_1=1$. Ordinary twisted multiplicativity and the Salié root evaluation are classical. The fixed-frequency sign of an ordinary untwisted Kloosterman sum on squarefree moduli has also been studied as a distribution problem. [Salié formula and normalization](salie-and-quarter-parity.md) · [Jones, twisted multiplicativity of Salié sums](https://link.springer.com/article/10.1007/s40687-025-00544-4) · [Fouvry–Michel, ordinary Kloosterman sign changes](https://doi.org/10.4007/annals.2007.165.675)

Remove the power of three from $n$ first. If $n=3^h n_0$ with $3\nmid n_0$, the known $3^h$ factor is evaluated at $t n_0^{-1}$ and the residual frequency at $n_0$ is $t(3^h)^{-1}$. Stop at residual modulus one. At a remaining step write the current modulus as $n$, coprime to six. Let $m$ be the unique positive odd representative below $n$ of $\pm t^{-1}\bmod n$. If $m\le3n/4$, set $B=1$. Otherwise put $d=n-m$, $s=v_3(d)$, $B=3^{s+1}$, and replace $m$ by the positive odd representative of $\pm(Bt)^{-1}\bmod n$. Now
$$
                         m\le 3n/4.
$$
In fact $3m=jn\pm d/3^s$ for an integer $j$. Since $d/3^s$ is prime to three and is smaller than $n/4$, the only possibilities are $j=1,2$. Hence $m\le(2n+d/3^s)/3<3n/4$. Also $B\le3d<3n/4$. Move any further factor of three from $m$ into $B$, preserving $Bm$. The integers $n,B,m$ are now pairwise coprime.

One query at the odd modulus $v=nBm\le n^3$ gives the product identity
$$
 W_v(1)=W_n(t)\,W_B((nm)^{-1})\,W_m((nB)^{-1}).
$$
The $B$ factor is known because $B$ is a power of three. The last term is another instance with modulus at most $3n/4$. Recursion terminates in $O(\log n)$ steps. Every modulus and known phase is computed by integer arithmetic on the original input, so the queries may all be issued together. Taking signs gives a product of signs. Taking log magnitudes gives an alternating sum, with coefficients of absolute value one. At odd prime-power blocks the sign of the known cosine is computed by integer comparison with the two quarter boundaries.

### Consequences for the evaluator

* **Exact signs.** The original-modulus sign decoder for inputs with $R$ distinct odd primes now needs only frequency-one sign queries on varying odd moduli. Its work and query bounds remain $2^{O(R)}\operatorname{poly}(b)$ or $2^{O(\sqrt b)}$ for arbitrary $b$-bit inputs. In particular these fixed-frequency signs suffice in deterministic polynomial time for two-prime inputs, where the complete factors also yield every individual centered floor-sum parity bit. The auxiliary moduli in the descent may have more prime divisors than the input. [Original-modulus decoder](kloosterman-localization.md#sign-decoding-with-logarithmically-many-prime-factors) · [Transfer to Salié sums](salie-and-quarter-parity.md)
* **Log magnitudes.** Suppose the answer at $m$ approximates $\log|W_m(1)|$ to absolute error at most $2^{-20}/(1+\log_2 m)^2$. The descent reconstructs the variable-frequency log magnitude to absolute error less than $2^{-14}$. Each dyadic size range contains at most three current moduli since $(3/4)^3<1/2$, and each queried modulus is at least the corresponding current modulus. Summing the promised errors over these ranges is bounded by $3\cdot2^{-20}\sum_{j\ge0}(1+j)^{-2}$. Compute the known cosine logs to the same per-stage accuracy. The extra initial power of three contributes at most one additional term. All this fits inside the stated error. Comparing the reconstructed value with zero gives a valid answer to the fixed magnitude-gap problem, since the permitted band is $1\pm2^{-12}$ in magnitude. Combining with the earlier threshold reduction therefore gives complete deterministic polynomial-time factoring on arbitrary integers. Conversely, given the factors of $m$, multiply or sum the local cosine magnitudes in polynomial time. Each local magnitude is at least $2/D$ on a block of size $D$, so polynomial working precision suffices. The promised approximation has an encoding of $O(\log\log(3m))$ bits since $|\log|W_m(1)||\le\log m$. The sign of $W_m(1)$ is unnecessary for this magnitude reduction. [Variable-frequency gap reduction](kloosterman-threshold.md) · [Original twisted-modulus transfer](salie-and-quarter-parity.md#the-shifted-comparison-at-one-dyadic-center)

The replay tested all units at odd moduli through 259 and twenty further cases with deliberately large powers of three in $n-m$. All 13,722 transfers agreed in exact integer sign and to numerical tolerance in log magnitude. An independent enumeration of roots checked 195 of the frequency-one values directly. The longest list in this finite sample contained nine queries. [Replay](../experiments/salie-fixed-frequency.py)
