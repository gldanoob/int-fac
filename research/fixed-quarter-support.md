# A constant Fourier energy bound for fixed-quarter parity

For $B(v)=\#\{1\le z\le v/4:z^2\equiv1\pmod v\}\bmod2$, complete factoring of an odd $b$-bit integer $n$ with at most $R$ distinct primes takes $\exp(O(R^2))\operatorname{poly}(b)$ expected bit operations and queries to $B$. Each query appends one certified auxiliary prime to the current cofactor. The algorithm is Las Vegas. This gives expected polynomial time for $R=O(\sqrt{\log b})$, and $\exp(O(b^{2/3}))$ expected time and queries for arbitrary support. The evaluator for $B$ remains an assumption. [Exact lift, progression sampler and earlier bounded-support argument](2026-11-25-handoff/quarter-parity/fixed-center.md)

## Detecting non-diagonal frequencies

Write $H(x)=\operatorname{sgn}\cos(2\pi x)$ and take $h\ge2$ independent uniform circle coordinates. After removing the known root pair, the corrected sign from the prime lift has the continuous model
$$
 G(x)=\prod_{\varnothing\ne S\subsetneq[h]} H\left(\sum_{i\in S}x_i\right).
$$
Translate by $v=u(e_1-e_2)$, $u=2^{-h-1}$. Exactly $m=2^{h-1}$ factors have their argument changed by $+u$ or $-u$, one for every proper subset containing exactly one of indices 1, 2. Each affected factor changes sign with probability $2u$. The changes for two distinct subsets are pairwise independent. Indeed their distinct nonzero binary incidence vectors are linearly independent over the rationals, so the corresponding map from the torus onto the two-torus is surjective and sends Haar measure to Haar measure. This assertion requires only pairwise independence.

Let $J$ be the number of sign changes. Then $\mathbb EJ=1/2$ and $\mathbb E[J(J-1)]=m(m-1)(2u)^2\le1/4$. The pointwise inequality $\mathbf1_{J=1}\ge J-J(J-1)$ gives $\Pr(J=1)\ge1/4$. Thus $\|G(\cdot+v)-G\|_2^2=4\Pr(J\text{ odd})\ge1$. Every diagonal frequency has translation multiplier one, while the squared difference multiplier is at most four at every frequency. Parseval gives non-diagonal Fourier energy at least $1/4$.

For a coordinate shift of size $t$ in $[0,1/K]$, the union bound over the affected subsets gives mean squared difference at most $8\cdot 2^h t$ for $K\ge2$. On averaging in $t$, each frequency with $|k_i|>K$ has squared difference multiplier at least one. The total energy outside $[-K,K]^h$ is at most $8h2^h/K$. With $K=\lceil128h2^h\rceil$, some non-diagonal mode in that box has magnitude at least $\zeta=[8(2K+1)^h]^{-1/2}=\exp(-O(h^2))$. Larger values of $K$ and smaller $\zeta$ computed using a public $R\ge h$ also work.

## Uniformity of the reduction

For residual blocks $d_i=p_i^{a_i}$ let $e_i$ be their CRT idempotents. On input $A\bmod n$, the grid angles are $x_i=2Ae_i/n\bmod1$, and the selected mode has additive frequency $f=2\sum k_i e_i\bmod n$. With $P=\min p_i$ the coupling obtained by rounding each continuous coordinate down to its grid changes the Fourier phase by at most $2\pi hK/P$. A subset sum crosses a quarter boundary with probability at most $4h/P$. The probability that any factor changes is at most $4h2^h/P$, and removing all nonunits costs at most $h/P$. This gives discretization error $O(h(K+2^h)/P)$, uniformly in the chosen mode.

For any nonprincipal real Dirichlet character, take a block $p^a$ where it is the lift of the quadratic character modulo $p$. Holding the other coordinates fixed gives a step function in this angle with $O(2^h)$ intervals, each with normalized Fourier coefficients bounded by $O(1/\min(j,d-j))$ for $0<j<d=p^a$ and by one for $j=0$. The quadratic Gauss transform has $p-1$ values of absolute size $p^{-1/2}$. Bounding an arbitrary translate of its convolution by the largest $p$ coefficient bounds gives $O(2^h(1+\log p)/\sqrt p)$ at each frequency. Restriction to units in the other coordinates only decreases this bound after averaging. The distinguished character already vanishes on nonunits of its own block. This proves the required twisting estimate uniformly in $h,p,a,k$.

Strip prime factors by trial division up to
$$
 D=\big\lceil[C_0R(2^R+K)/\zeta]^4\big\rceil
$$
for a large absolute $C_0$, and recognize zero or one residual block by prime and perfect-power tests. Now both errors above are smaller than $\zeta/8$ and $P>4K$ on each remaining cofactor. The cutoff costs $\exp(O(R^2))\operatorname{poly}(b)$.

For a unit $A$ sample one integer $\ell\in(n,X]$ uniformly in the class $A^{-1}\bmod n$, where $X=n^C$. Use the corrected $B(n\ell)$ only if a primality test passes. Further accept with probability $\log\ell/\log X$ rounded within $\zeta/(10^3\log X)$, outputting zero for rejection or nonunits. One can implement the rounded probability with a dyadic rational and independent fair bits. Thorner–Zaman's Corollary 1.4 has relative error
$$
 O\left(e^{-cC}+\exp[-c(\log X)^{3/5}/(\log\log X)^{1/5}]\right)
$$
with effective absolute constants for $C\ge12$. Set $C=\lceil C_1(1+\log(1/\zeta))^2\rceil$ for a large absolute $C_1$. For $n\ge3$ the second exponent grows at least as fast as a constant multiple of $C^{3/5}/(\log(2C))^{1/5}$. Both terms are then less than any fixed small multiple of $\zeta$. The relative main term has the form $1-\gamma\psi(A)$, where $0\le\gamma\le1$ and a nonzero secondary term uses a nonprincipal real character. Positivity of the main term in each reduced class and Remark 1.5 give this bound on $\gamma$. [Thorner–Zaman, Corollary 1.4 and Remark 1.5](https://arxiv.org/pdf/2108.10878#page=3)

Omitting primes at most $n$ costs at most $n\log n$ in prime weight against $X/\varphi(n)$. The candidate count is $X/n+O(1)$, so after the same choice of $C_1$ both corrections are smaller than $.001\zeta$ on the scale of the main term. Thus the sampled sign has mean function with coefficient of magnitude at least $\zeta/(2\log X)$ at $f$, by the discrete untwisted and twisted bounds above. One can take $K,\zeta,D,C$ from $R$ at all recursive calls. List significant Fourier coefficients with a randomized additive-group algorithm at threshold $\zeta/(4\log X)$, using independent trials at repeated evaluations to estimate their means. This has polynomial cost in $\log n$, $\log X$ and $1/\zeta$. For each output $g$ try $\gcd(g-2j,n)$ for $-K\le j\le K$. At $g=f$, choosing $j=k_i$ includes block $d_i$ and excludes every block with a different coordinate because $P>4K$. Verification, repetition and recursion give the stated zero-error bound. For unrestricted support use $R=\lceil b^{1/3}\rceil$ and include $2^{R^2}$ in the trial cutoff. At most $R$ distinct primes survive. [Significant Fourier transform for finite cyclic groups, Theorem 3.4](https://arxiv.org/abs/1607.01842) · [Fixed-center decoding details](2026-11-25-handoff/quarter-parity/fixed-center.md)

## Exact replay

Run `python3 experiments/quarter-support.py`. The script checks the first two crossing moments, counts odd crossings, and projects onto functions of the coordinate sum to compute all diagonal Fourier energy in rational arithmetic. It uses grids of order $2^{h+1}$ and offsets each coordinate by $1/((h+1)2^{h+1})$, which keeps every proper nonempty subset sum away from a quarter boundary. A separate enumeration counts roots in the quarter interval directly at 35 prime lifts of moduli with two through six prime-power blocks. [Replay](../experiments/quarter-support.py)

| Coordinates | Grid points | Probability of one crossing | Probability of an odd number | Non-diagonal energy |
| --- | ---: | ---: | ---: | ---: |
| 2 | 64 | 3/8 | 3/8 | 5/8 |
| 3 | 4,096 | 21/64 | 21/64 | 405/512 |
| 4 | 1,048,576 | 1267/4096 | 637/2048 | 904931/1048576 |
