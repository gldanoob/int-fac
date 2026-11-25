# Exact mean-time evaluation of three-square digits at a small fundamental discriminant

Fix squarefree $d\equiv3\bmod8$. Given $M=df^2$ for odd $f$, the method below always returns the exact quotient of the ordered positive three-square count $C(M)$ at binary position $k-t$, where $k=\lfloor(\log_2M)/2\rfloor$ and $0\le t\le k$. It uses deterministic $2^t\operatorname{poly}(b)$ **mean** bit time in either of the following settings.

- Take $f$ uniform over odd integers in $[X,2X]$ with $b=\lceil\log_2(2X)\rceil$.
- Fix **any** odd $n$, put $u=dn^2$ and $b=\mathrm{bits}(u)$, and take $f=n(1+4uj^2)$ over the full standard dyadic range of the [middle-bit reduction](middle-three-square-bit.md). The mean is over $j$ separately at that single $n$.

Both bounds are uniform for squarefree $d\le b^D$ with fixed $D$. The second algorithm receives the padded integer and $d$; the fixed outer conductor $n$ and multiplier $j$ remain unknown to it. If only a polynomial bound on the squarefree part is supplied, one can find the unique $d$ by trying the small squarefree candidates and testing for a square quotient. No zero-free hypothesis or estimate of an unknown class number enters the calculation. In particular $t=O(\log b)$ gives exact polynomial mean time.

## A pointwise integer enclosure

Compute $B_d=C(d)$ by enumerating positive triples for the small $d$. For $p^e\parallel f$ the Hurwitz product gives

$$
 C(df^2)=B_d f\prod_{p^e\parallel f}g_e(p),\qquad
 g_e(p)=1+(1-\chi_d(p))\frac{1-p^{-e}}{p-1},\qquad
 \chi_d(p)=(-d/p).
$$

This includes $B_3=1$ and primes ramified in $d$. After trial division through $Y\ge2$, write $f=ar$ with every prime of $a$ removed to its full exponent and every prime of $r$ exceeding $Y$. Set $J=B_d f\prod_{p^e\parallel a}g_e(p)$. This is an integer since the only denominators divide $a$. If $r=1$, the count is $J$. If $1<r<(Y+1)^2$, the residual must be prime and its remaining factor is explicit. Otherwise the count lies in the closed integer interval

$$
 \left[J,\ \left\lfloor J(1+2/Y)^{\lfloor\log_{Y+1}r\rfloor}\right\rfloor\right].
$$

Every missing factor is in $[1,1+2/Y]$, and the number of missing primes is at most the exponent shown. Return as soon as both endpoint quotients agree. The log of the interval's upper-to-lower ratio is $O(\mathrm{bits}(f)/Y)$. Computing the endpoints, even as exact rational powers, costs polynomial bit time per trial candidate. [Chen and Garvan, Hurwitz product](https://arxiv.org/pdf/2010.14315#page=5)

Double $Y$ from 8, keeping the factors already removed. Cap the last cutoff at $\lceil f^{1/3}\rceil+1$. If the interval still straddles a threshold, factor the residual deterministically by Lehman's cubic-root algorithm and complete the local product exactly. This last stage costs $O(f^{1/3}\operatorname{poly}(\log(2f)))$ bit operations, comparable up to a polynomial to the cost of reaching it. The implementation searches a safe integer superset of Lehman's square intervals and recurses on any proper split. [Lehman, Theorem 1](https://doi.org/10.1090/S0025-5718-1974-0340163-2)

## Mean over ordinary conductors

Fix a cutoff $Y$ on the doubling schedule. For $Y=O(b)$ the bound $O(2^t\operatorname{poly}(b)/Y)$ on the continuation probability is immediate. For larger $Y$ the enclosure has relative width $O(b/Y)$. At fixed $a$ write $J=W_a f$, where $W_a=B_d\prod_{p^e\parallel a}g_e(p)$. If a threshold lies in the interval, $f$ is in a range of length $O(Xb/Y)$ about $j2^{k-t}/W_a$. There are at most two choices of $k$ in $[X,2X]$ and $O(2^t\operatorname{poly}(b))$ choices of $j$. For instance, the count divided by $\sqrt{df^2}$ is $O((1+\log(df^2))^3)$ by the elementary Hurwitz bound. The enclosure width only changes this bound by a constant factor at these cutoffs. [Elementary normalized count bound](middle-three-square-bit.md#raising-the-normalized-count-on-demand)

Each such interval contains $O(1+Xb/(aY))$ multiples of $a$. A still unresolved input has $r>Y$, hence $a\le2X/Y$. Summing the unit term over these $a$ costs $O(X/Y)$, and $\sum_{a\le2X/Y}1/a=O(b)$. Thus the fraction still unresolved after cutoff $Y$ is $O(2^t\operatorname{poly}(b)/Y)$. The probability of reaching the next doubled stage times its cost is $O(2^t\operatorname{poly}(b))$. There are $O(b)$ stages. The varying final cap is within a fixed factor of $X^{1/3}$ throughout this dyad, so charging its predecessor at the corresponding scale covers the exact fallback as well.

## Mean at every fixed base across its norm pads

Let $K=8b+16$, $s_j=1+4uj^2$ and $2^K\le s_j\sqrt u<2^{K+1}$. Every prime dividing $s_j$ splits for $-d$, and the exact count at $M=us_j^2$ is $s_jC(u)$. Put $R=C(u)/\sqrt u$. The scaled value before flooring is $2^tR\,s_j\sqrt u/2^K$. The normalized abscissas lie in $[1,2)$ on a grid with upper and lower spacing of order $1/L$, where

$$
 L\asymp 2^{K/2}u^{-3/4}\asymp u^{13/4}
$$

is the number of eligible multipliers. This follows directly from the endpoints and derivative of $1+4uj^2$. At large cutoffs the relative width of the pointwise valid interval is $O(b/Y)$ since $\mathrm{bits}(f)=O(b)$. Each of $O(2^tR+1)$ thresholds can obstruct certification on a range in the normalized abscissa of length $O(b/Y)$. For each individual $n$ the continuation fraction is therefore at most

$$
 O\big((2^tR+1)(b/Y+1/L)\big).
$$

Since $R=\operatorname{poly}(b)$, the first term again pays for every doubled stage. The accumulated contribution of the grid endpoint terms is at most $2^t\operatorname{poly}(b)\max f^{1/3}/L$. Here $f=ns_j<2^{K+1}/\sqrt d=O(u^8)$, so $f^{1/3}/L=O(u^{8/3-13/4})$. The rare fallback is covered even though the evaluator has to work with the much larger padded conductor. The identity of the outer $n$ is used only to prove the mean bound. [Norm padding and grid estimate](middle-three-square-bit.md#locating-a-change-of-the-digit)

The arithmetic average concerns the full interval of $j$. The exact-count reduction selects the few locations bracketing a transition, where its output can distinguish neighboring integer counts. [Sparsity at the final comparisons](twisted-three-square-digits.md#what-survives-at-the-last-comparisons)

## Unpadded semiprimes and the baseline value

For comparable primes $p,z$ and $n=pz\in[X,2X]$, the simple baseline $B_d n$ differs from the true count by relative $O(X^{-1/2})$, uniformly in $d$. For fixed $d\le(\log X)^D$ the unpadded quotient can consequently differ from that of $B_d n$ at only $O(2^t\sqrt X\,\operatorname{poly}(\log X))$ such integers. At each possible quotient threshold $j2^{k-t}$, the allowed $n$ lie in a real interval of length $O(\sqrt X)$ about $j2^{k-t}/B_d$. There are $O(2^t\operatorname{poly}(\log X))$ thresholds in the dyad. This applies to the union of polynomially many such discriminants as well. It quantifies how seldom unpadded middle quotients distinguish the remaining local factors on balanced semiprimes.

For $d=3$, suppose $p\equiv2\bmod3,\ z\equiv1\bmod3$, and $c^{-1}\sqrt n\le p,z\le c\sqrt n$ for fixed $c$. Then $C(3n^2)=n+2z$. The standard padded midpoint can implement an exact comparison with any integer $w$ in that initial range. Choose the first $s_j=1+4(3n^2)j^2$ with $s_j(n+2w)\ge2^K$. Its step is small enough that $s_j(n+2w-2)<2^K$ for large $n$: the corresponding change in $2^K/s_j$ is $O(n/L)=o(1)$. Also $s_j\sqrt{3n^2}/2^K=\sqrt3+O_c(1/\sqrt n)$, so this pad belongs to the allowed dyad and the quotient is zero or one. Its digit equals $[z\ge w]$.

Only $\tfrac14\log_2 n+O_c(1)$ such comparison bits need an external evaluator. Bisect the initial range, of width $O_c(\sqrt n)$, until it has width $O_c(n^{1/4})$. The degree-one unknown-divisor lattice at modulus $n$, with the lower bound $z\ge\sqrt n/c$, certifies radius at least $n^{1/4}/(8c)$ from its explicit formula. Cover the remaining interval by a constant number of windows and verify each candidate by division. More generally this directly evaluates a threshold whenever $w$ is within $O_c(n^{1/4})$ of $z$, even if the comparison itself is exceptionally close. The polynomial mean-time theorem for uniformly chosen pads gives no expectation bound for the earlier comparisons deliberately placed inside the factor range. [Unknown-divisor search radius](hidden-divisor-lattices.md#a-lattice-for-overlapping-public-moduli)

The ordinary-conductor argument also gives unconditional deterministic $2^t\operatorname{poly}(b)$ mean time for the exact quotients of $\sigma(f)$ and $\varphi(f)$ at position $\lfloor\log_2 f\rfloor-t$. Their normalized local factors at $p^e$ are $(1-p^{-e-1})/(1-p^{-1})$ and $1-p^{-1}$ respectively. After the smooth part has been removed, the true products are again within relative $O(b/Y)$ of the known multiplier times $f$, and exact factorization supplies the same fallback. This assertion concerns leading quotients on ordinary integers.

## Finite check

The [PARI/GP replay](../experiments/fixed-discriminant-middle-digits.gp) verifies Lehman's split or prime result on all 4,999 integers from 2 through 5,000. It compares 5,120 exact ordinary quotients with independent factorizations, including 2,562 that reach the fallback. The mean last trial cutoff is $57317/5120$. A further 256 standard-pad queries through 450 bits run the evaluator on the padded integer with the fixed discriminant. They all return the exact reference quotient; the largest trial cutoff is 65,536. The finite pad sample uses 32 equally spaced interior probes at each base and two precisions. The mean-time guarantees above cover the full pad intervals.

For $170229077=10007\cdot17011$, seven supplied norm-transfer bits leave the interval $[16921,17073]$ for the split prime. The terminal degree-one lattice returns 17,011. This last replay checks the comparison reduction and its direct local finish.
