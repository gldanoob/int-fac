# A divisor-moment bound for intermediate scalar progressions

Some intermediate scalar progression counts admit a deterministic zero approximation in polynomial time in the prime cutoff and binary input length. The certificate bounds the fraction of squarefree band products in the progression. It can apply when the step is too large for a residue table, the progression is shorter than the square-root threshold for character estimates, and both the ordinary and complementary progressions are long. [Scalar counting regimes](cogentic-scalar-divisor-count.md) · [Complementary divisor windows](cogentic-coefficient-selection.md#exact-counts-by-complementary-divisor-windows)

## Exact upper bound

First handle a constant progression by one divisor test. Otherwise write the progression as $c+dj$ for $0\le j<T$, and set $g=\gcd(c,d)>0$. The eligible band product is squarefree. If $g$ does not divide it, the count is zero. Otherwise divide all values and the step by $g$. Delete every eligible prime dividing $g$ or the reduced step from the band. The first deletion enforces squarefreeness of the original value. The second is valid because the reduced start and step are coprime. Split at zero and turn each negative piece into a positive progression by taking absolute values and reversing the order if needed. Clip to $[1,P]$ where $P=\prod_{p\in J}p$ is the product of the remaining eligible primes. Each piece is now a positive progression in a unit class modulo the reduced step. Its clipped length is $t$, and all values are at least its first member $l$. Empty pieces contribute zero. [Unit-class reduction](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli)

Let $n=|J|$ and let $k$ be the least number of the largest primes of $J$ whose product reaches $l$. The empty product is allowed. Every divisor of $P$ at least $l$ contains at least $k$ distinct primes. For $0\le m\le k$ write
\[
 e_m=\sum_{\substack{S\subseteq J\\|S|=m}}\prod_{p\in S}\frac1p.
\]
If $C$ is the exact count on the clipped piece, then
\[
 \frac{C}{t}\le U=\min\left(1,\min_{1\le m\le k}
       \frac{e_m+\binom{n}{m}/t}{\binom{k}{m}}\right).
 \tag{1}
\]
For $k=0$ use $U=1$. To prove (1), count incidences between progression members and products of $m$ distinct eligible primes dividing those members. Every accepted member contributes at least $\binom{k}{m}$ incidences by squarefreeness. For a fixed subset $S$, all its primes are coprime to the step, so the indices divisible by $d_S=\prod_{p\in S}p$ form a single residue class modulo $d_S$. At most $t/d_S+1$ indices lie in that class. Summing these upper bounds gives (1). This counts auxiliary incidences even on rejected members. It uses the squarefree smooth-value indicators in the actual conditional score and the squarefree-divisor test after projection. [Score expansion](cogentic-conditional-score.md#fixing-the-two-fields) · [Scalar mark tests](cogentic-scalar-divisor-count.md#rectangles-for-a-pair-of-marked-values)

Compute $P e_m=[z^m]\prod_{p\in J}(p+z)$ by multiplying the linear factors up to degree $k$. The integer coefficients have $O(n\log(2B))$ bits, and $k\le 1+\log_2 l$. The sieve, clipping, recurrence, binomials and rational comparisons therefore take $\operatorname{poly}(B,w)$ bit operations for $w$ an input bit-length envelope, with no scan in $t$ or the step. For signed input, sum the bounds $tU$ over the two pieces and divide by the original $T$. If the result is at most the requested additive tolerance, return zero as an approximation. Taking $\lfloor tU\rfloor$ also gives a certified integer upper bound per piece.

## Precision on the one-third scale

Use $L=\log N$, $H=L^{1/3}(\log L)^{2/3}$ and $V=L^{2/3}(\log L)^{1/3}$. Consider a clipped positive unit class with $\log B=(\beta+o(1))H$, $\log t=(\tau+o(1))V$, and $\log l=(\lambda+o(1))V$, where $\beta>0$ and $0<\tau<\lambda$. Set $m=\lfloor\log t/\log B\rfloor$. Then $m\le k$ eventually, since $k\ge\log l/\log B$. For integers $B\ge2$,
\[
 \sum_{\sqrt B<p\le B}\frac1p
 \le \frac{2}{\log B}\sum_{p\le B}\frac{\log p}{p}
 \le \frac{4\log(B!)}{B\log B}\le 4.
\]
The middle inequality follows from $\lfloor B/p\rfloor\ge B/(2p)$ and $\prod_{p\le B}p^{\lfloor B/p\rfloor}\mid B!$. Consequently $m!e_m\le4^m$, $m!\binom{n}{m}/t\le B^m/t\le1$, and $m!\binom{k}{m}\ge(k-m+1)^m$. Substituting in (1) gives
\[
 U\le\frac{4^m+1}{(k-m+1)^m}
 \le \exp\left(-\left(\frac{\tau}{3\beta}+o(1)\right)H\right).
\]
Here $m=(\tau/\beta+o(1))V/H$, $k-m\gg V/H$, and $(V/H)\log L=H$. For any fixed $0<\gamma<\tau/(3\beta)$, this certifies additive error $e^{-\gamma H}$ in time $\exp(O(H))$, independently of the modulus or relative width. If $\log l$ and $\log h$ both have leading term $\lambda V$ for $h$ the largest member, the conclusion includes the intermediate range $0<\tau<\lambda/2$.

This level of precision depends on the progression length. The coefficient selector asks for $e^{-C H}$ with $C$ large enough to absorb its signed score weights and bisection errors. The divisor-moment estimate supplies no general comparison with that $C$, and it applies only when its computed upper bound meets the available error budget. [Precision required for bisection](cogentic-scalar-divisor-count.md#fixing-the-four-coefficient-words)

## Finite replay

Run `python3 experiments/cogentic-intermediate-count.py`. The replay compares exact rational bounds with direct divisor tests on signed, nonunit, constant and omitted-prime cases. It also constructs a unit class modulo $2^{240}$ with $2^{160}$ members, ending at the product of the 60 largest eligible primes for $B=997$. This endpoint gives a known hit. The largest member has 577 bits, the complementary progression has 349-bit length, and $h/(qt)$ has 177 bits in its integer part. The prime 37 alone generates $2^{238}$ residues modulo the step. Formula (1) certifies a fraction below $2^{-128}$, using $m=20$, without visiting any of the progression members.
