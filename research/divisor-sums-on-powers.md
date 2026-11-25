# Complete factorization from a short block of divisor sums

Let $N\ge2$ have $b$ binary digits. A deterministic algorithm recovers its complete prime factorization in polynomial bit time from **$O(b/\log b)$ consecutive ordinary divisor sums $\sigma(N^j)$**. The exponents $j$ are $O(b/\log b)$ and are chosen from $N$ before any answers arrive. Each queried integer and each answer has $O(b^2/\log b)$ bits. The proof uses integer and rational arithmetic and has no zero-free hypothesis. One compressed answer at a single public power also recovers the exact totient and gives complete factoring via Miller’s Dirichlet-based reduction. Producing these divisor sums on unrestricted inputs remains open here.

For comparison, Bach, Miller and Shallit give a randomized polynomial-time algorithm with a single original value $\sigma(N)$. Morain, Renault and Smith obtain deterministic results under size conditions for one original divisor sum. The [intersection-lattice reduction](hidden-divisor-lattices.md) gives an independent unconditional algorithm with all powers through $3b$. The shifted moment matrices below are related to the matrix pencil used in Prony methods for exponential sums. Here there can be exponentially many subset terms. The proof bounds the signed terms we omit, chooses the binary precision and certifies the recovered integer. [Bach–Miller–Shallit, Theorem 2](https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf) · [Morain–Renault–Smith, Theorem 5.4](https://arxiv.org/pdf/1802.08444v2#page=13) · [Fischer et al., generalized eigenvalue methods](https://arxiv.org/abs/2004.10472)

## One compressed divisor sum recovers the totient

For every $b$-bit $N\ge2$, choose $L=\max(16,b^2)$ and the least integer $J\ge1$ with $(L+1)^{J+1}\ge8bN$. Thus $J=O(b/\log b)$. The **single integer**
$$
C=\left\lfloor\frac{N^{J+1}}{\sigma(N^J)}\right\rfloor
$$
has at most $b$ bits and suffices to determine $\varphi(N)$ exactly in deterministic polynomial time. Alternatively, supply the bit length and the first $b+4$ significant bits of $\sigma(N^J)$, using all its bits if it is shorter. This also suffices and costs $b+O(\log b)$ bits in total. Treating the supplied arithmetic data as an oracle answer, complete deterministic factoring then follows by Miller's reduction. Its small-base bound uses the Dirichlet L-function zero-free statement in the cited independent verification. Computing the totient from the response uses only elementary arithmetic. [Miller, Lemma 5 and Theorem 4](https://www.cs.cmu.edu/~glmiller/Publications/Papers/Mi76.pdf#page=11) · [Dirichlet verification, statement 3](https://math.mit.edu/~drew/grh/) · [Order-multiple reduction](order-and-crt-reductions.md#a-linear-number-of-queries-on-one-cofactor)

Write $N=tm$ by trial-dividing through $L$, with all small prime powers in $t$. Compute $\varphi(t)$ and $R_t=t^{J+1}/\sigma(t^J)$ directly. For $u\ge1$ let $R_u=u^{J+1}/\sigma(u^J)$ and $E_u=1-\varphi(u)/R_u$. Multiplicativity gives $R_N=R_tR_m$. The geometric-series identity gives $R_u\ge\varphi(u)\ge1$ and $R_u\le u$. For the residual, a union bound on the factors of the product gives
$$
0\le E_m=1-\prod_{p^e\parallel m}(1-p^{-1-eJ})
\le b/(L+1)^{J+1}\le1/(8N).
$$
Consequently $0\le R_m-\varphi(m)=R_m E_m\le1/8$. If $m=1$, the answer is already $\varphi(t)$. Otherwise $m$ is odd and $\varphi(m)$ is even.

In fact the decoding works for $C=\lfloor\widetilde R_N\rfloor$ whenever $|\widetilde R_N-R_N|<1/4$. The even integer $\varphi(m)$ belongs to
$$
\left[\frac{C-1/4}{R_t}-\frac18,\ \frac{C+5/4}{R_t}\right).
$$
Its width is at most $13/8<2$, so there is a unique even candidate. Multiply that integer by $\varphi(t)$. For the leading-bit protocol, truncation gives $\widetilde S$ with $|\widetilde S/\sigma(N^J)-1|\le1/(8N)$. Hence $|N^{J+1}/\widetilde S-R_N|\le N/(8N-1)<1/4$, proving the claim for that protocol as well. There are $O(\log b)$ bits of length information because $\sigma(N^J)\le N^J(1+J\log N)$.

With $J=b$ there is a still simpler identity $C=\varphi(N)$ without trial division. Indeed $E_N\le\sum_{n\ge2}n^{-(b+1)}\le2^{-b-1}(1+2/b)\le2^{-b}$ by integral comparison for $b\ge2$. It follows that $0\le R_N-\varphi(N)\le N2^{-b}<1$. The shorter public exponent above uses the small factors to obtain the same information.

The full decoder recovered the totient and factors of all 1,999 inputs from 2 to 2,000 and 64 larger inputs with three primes beyond the trial bound. For example, at $N=43912157131979933002905882398568$ it used $J=8$ and $C=14637732739448786428993195606914$ to recover $\varphi(N)=14636988629364742811360062153344$. The larger checks also used truncated leading bits and perturbations of both signs near the stated limits. [GP reciprocal decoder and fixture](../experiments/sigma-tail.gp)

## Which integers to request

Put $L=\max(16,b^2)$, let $h_0$ be the largest positive integer with $h_0!\le N$, and take

$$
h=\max(1,\min(h_0,\lfloor\log_{L+1} N\rfloor)),\qquad
J=32+\left\lceil\frac{32b}{\lfloor\log_2 b\rfloor}\right\rceil.
$$

Request $S_j=\sigma(N^j)$ for $J\le j<J+2h$. Trial-divide through $L$. Whenever a full prime power $B_i=p_i^{e_i}$ is removed, divide each $S_j$ by $(p_i B_i^j-1)/(p_i-1)$. The new values are exactly $\sigma(m^j)$ for the new residual $m$. The number of residual primes is at most $h$ because each exceeds $L$ and their product is at least their count factorial. This update also applies to every prime recovered below. The estimate $\sigma(N^j)\le N^j(1+j\log N)$ gives the claimed answer sizes.

## Isolating the smallest remaining prime power

For the current $m>1$ write $B=\min_i B_i$. Different prime bases give distinct block sizes. Define the positive error

$$
E_j=1-\frac{\varphi(m)\sigma(m^j)}{m^{j+1}}
   =1-\prod_i\left(1-\frac{1}{p_i B_i^j}\right).
$$

If $p_1$ is the base of $B$, then $B^{-J}/p_1\le E_J\le hB^{-J}$. Since $B>b^2$, $B^J>2^{64b}$. Thus $m^{J+1}/\sigma(m^J)=\varphi(m)/(1-E_J)$ is within one above $\varphi(m)$, so taking its floor computes the totient and hence every $E_j$ used below.

Let $T=\max(8,\lfloor(NE_J)^{-1/J}\rfloor)$. It is computed by integer comparisons. The two preceding bounds give $T\le B$ and $z_1=T/B\ge1/(2b^{1/16})$. Indeed $(Nh)^{1/J}\le2^{2b/J}\le b^{1/16}$, and rounding down costs at most a factor of two in this range. Put $Y_k=T^k E_{J+k}/E_J$ for $0\le k<2h$. For a nonempty subset $S$ of prime blocks put $B_S=\prod_{i\in S}B_i$ and $p_S=\prod_{i\in S}p_i$. Expansion gives

$$
Y_k=\sum_{S\ne\varnothing} a_S z_S^k,\qquad
z_S=T/B_S,\qquad a_S=\frac{(-1)^{|S|+1}B_S^{-J}}{p_S E_J}.
$$

Every node $z_S$ is in $(0,1]$. The singleton weights are positive and the weight of the largest node $z_1$ is at least $1/(Nh)$. The sum of the absolute weights of all nonsingletons is at most $2^b N B^{-J}$, since $B_S\ge B^2$ and $E_J\ge B^{-J}/N$.

## An exact test at each bisection point

Take $Q=2^{16b+16}$ and $y_k=\lfloor QY_k\rfloor$. For a dyadic $0\le u\le1$ test whether the real symmetric matrix

$$
A_u=(y_{i+k+1}-u y_{i+k})_{0\le i,k<h}-3h I
$$

has a positive eigenvalue. Multiplying by the positive denominator of $u$ leaves an integer signature test. For example, the characteristic polynomial has all coefficients nonnegative exactly when every eigenvalue is nonpositive. The matrix entries have polynomial bit size, since $Y_k\le hN$ and bisection uses $O(b)$ bits.

For a coefficient vector $v$ write $P(z)=\sum_{i=0}^{h-1}v_i z^i$. The exact unrounded moment form before the diagonal correction equals $\sum_S a_S(z_S-u)P(z_S)^2$. On $[0,1]$, $|P(z)|^2\le h\|v\|_2^2$. The nonsingletons therefore contribute at most $(h/Q)\|v\|_2^2$ in absolute value. Rounding costs at most another $(2h/Q)\|v\|_2^2$. If $u\ge z_1$, every singleton contributes a nonpositive term and the test returns false.

For $u\le z_1-\delta$, with $\delta=1/(64N^2)$, use the polynomial $P(z)=\prod_{i:B_i>B}(z-T/B_i)$. Its degree is less than $h$ and $\|v\|_2^2\le4^b$. At the largest node each difference is at least $z_1/B_i$. The actual number of remaining blocks is at most $b/(2\log_2 b)$, so the product of these factors of $z_1$ is at least $2^{-b}$. The product of the $B_i$ is at most $N$, giving $|P(z_1)|\ge2^{-b}/N$. Only the largest singleton contributes. Its positive contribution is at least

$$
\frac{2^{-2b}}{64hN^5}>\frac{6h\,4^b}{Q}.
$$

This exceeds the nonsingletons, rounding error and diagonal correction together. The test returns true. The polynomial $P$ is used to prove the test and is never constructed from unknown factors.

Bisect $[0,1]$, moving the lower endpoint to $u$ on true and the upper endpoint to $u$ on false. The invariants are $\mathrm{lo}\le z_1$ and $z_1\le\mathrm{hi}+\delta$. Both hold even if the test gives either answer in the intervening strip. When $\mathrm{hi}-\mathrm{lo}\le\delta$, $z_1-\mathrm{lo}\le2\delta$, and $\mathrm{lo}\ge z_1/2$. Hence $|T/\mathrm{lo}-B|\le8N b^{1/16}\delta<1/2$. Rounding recovers the exact block. Trying integer roots in decreasing exponent order gives its prime and valuation. Remove that block, update all answers and repeat. There are at most $b$ rounds. Exact integer roots, integer determinants and the other operations all cost polynomial bit time.

## Recovering several blocks from the same moments

The implementation first tries to recover several blocks at once. From the rounded moments $y_k$, solve the exact rational equations $\sum_{j=0}^{h-1}c_jy_{i+j}=-y_{i+h}$ for $0\le i<h$. For an exact mixture of $h$ distinct singleton nodes with positive weights, the resulting monic polynomial $P(z)=z^h+\sum_{j<h}c_j z^j$ vanishes at every node. Indeed the vector of weighted $P(z_i)$ values lies in the kernel of an invertible Vandermonde matrix. This is the classical Prony recurrence. [Potts–Tasche, *Parameter estimation for exponential sums by approximate Prony method*](https://doi.org/10.1016/j.sigpro.2009.11.012)

The actual moments have signed subset terms and rounding error. Round the recurrence coefficients to $8b+64$ fractional bits before isolating its real roots. For each resulting root $z$ in $[T/m,1]$, round $T/z$ to a candidate $B$. Accept a candidate only if it is a prime power dividing the residual and $\gcd(B,m/B)=1$. These integer checks certify a complete prime-power block independently of the root accuracy. Remove all accepted blocks and divide each supplied sum by its exact contribution. A singular system or an empty verified list invokes the signature algorithm above. Final exact divisions verify every supplied answer.

## Arithmetic replay

The short-block fixture factors an 86-bit integer from 12 consecutive divisor sums starting at $j=491$. The answers total 508,507 bits. After trial division the three full blocks are $100{,}140{,}043$, $10007^2=100{,}140{,}049$, and $100{,}140{,}059$. The reconstruction uses only $N$ and the supplied answers. Other fixtures cover prime powers and inputs with many small primes. The GP program also supports a simpler schedule $J=32b+32$ after trial division through 16. It uses the same bisection test. [GP decoder and fixtures](../experiments/sigma-power-moments.gp)


A larger replay used the first $k$ primes strictly above $2^d$ as the factors, with $(d,k)=(15,8),(18,14),(20,19),(20,25),(21,36),(21,48)$. Every factor exceeded the trial limit. All six complete factorizations matched the independently constructed inputs. On one machine the 253-bit, 14-prime case took 1.668 seconds with the recurrence and 923.810 seconds in an earlier run of the signature-only decoder. The largest case used 100 answers totaling 369,890,026 bits to recover 48 close primes in a 1,009-bit input. Its decoding time was 213.168 seconds, excluding answer generation. These are local timings for structured inputs with supplied divisor sums.
