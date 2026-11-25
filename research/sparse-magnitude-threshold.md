# Deterministic decoding of the original-modulus magnitude bit

Let $N$ be odd with at most $R$ distinct prime divisors and bit length $b$. Write $W_N(t)=\sum_{x^2=1\bmod N}e^{4\pi i tx/N}$. Given the bit $|W_N(t)|>1$ at chosen units $t$ of the original modulus, complete deterministic factoring takes $2^{O(R)}\operatorname{poly}(b)$ bit operations and queries. Each reply may be chosen adversarially when $1-2^{-12}\le |W_N(t)|\le1+2^{-12}$. The same bound holds for the normalized ordinary diagonal Kloosterman sum at the original square modulus. In particular the reduction is polynomial for $R=O(\log b)$ and costs $2^{O(\sqrt b)}$ on all inputs. The cost of producing the comparison from $N$ is open. [Earlier decoder and oracle definition](unpadded-magnitude-threshold.md) · [Square-modulus identity](kloosterman-localization.md#stationary-phase-at-a-square-modulus)

The earlier original-modulus magnitude proof gives $\exp(O(R\log\log(3R)))\operatorname{poly}(b)$. The exact-sign argument in the same repository already uses a sum of dyadic levels to obtain $2^{O(R)}$ for its oracle. Here the obstacle is to approximate a **threshold on the sum of singular logarithms** while retaining a separable representation with uniformly bounded scalar frequencies. One-sided interval approximants address this point. The sparse products and the deterministic frequency decoder use established methods. [Vaaler, *Some extremal functions in Fourier analysis*](https://doi.org/10.1090/S0273-0979-1985-15349-2) · [Smolyak, product quadrature](https://www.mathnet.ru/eng/dan27586) · [Akavia, deterministic sparse Fourier approximation](https://people.csail.mit.edu/akavia/akaviaCOLT10.pdf) · [Earlier sparse sign argument](kloosterman-localization.md#sign-decoding-with-logarithmically-many-prime-factors)

## Uniform density and the scalar approximants

Use the original decoder's trial division, prime-power tests and freezing of the known CRT phases. With $2\le r\le R$ remaining blocks, the oracle signal at the unknown coordinates $x_i$ compares $S=\sum_i Y(x_i)$ with a known $q\in[-2,0]$, where $Y(x)=\log|2\cos(2\pi x)|$. On the uniform continuous torus let $f_r$ be the density of $S$ and $a_r$ the coefficient of $\mathbf1_{S>q}$ at any axial frequency $(2,0,\ldots,0)$. The previous density proof gives an effective $c>0$ with $a_r\ge c/\sqrt r$, and $\Pr(|S-q|\le .001)<.051a_r$. [Density and axial coefficient](unpadded-magnitude-threshold.md#size-of-the-coefficient-and-the-ambiguous-band)

We also need $\sup_s f_r(s)\le C/\sqrt r$ for an effective absolute $C$. The beta integral and gamma reflection formula give the exact characteristic function magnitude
$$
 |\mathbb E e^{itY}|^2=\frac{2}{\pi |t|}\tanh(\pi |t|/2).
$$
Indeed the characteristic function itself is $2^{it}\Gamma((1+it)/2)/(\sqrt\pi\,\Gamma(1+it/2))$. On $|t|\le1$ the magnitude is at most $e^{-c_0t^2}$ for an effective $c_0>0$, by Taylor expansion at zero and compactness. On $|t|\ge1$ use $(2/(\pi |t|))^{1/2}$. For $r\ge3$, Fourier inversion now bounds the density by $O(r^{-1/2})$. For $r=2$, the density of $\log2-Y$ is bounded by $C_1e^{-z}(1+z^{-1/2})$ on $z>0$. Its self-convolution is bounded since $\int_0^w z^{-1/2}(w-z)^{-1/2}\,dz=\pi$.

Choose a large absolute integer $A$ below, put $U=AR$, and use period $P=16(U+R+1)$. Let $T$ be a large effective absolute constant and $m=\lceil TP\rceil$. On the circle of length $P$ form the degree-$m$ Selberg majorant $V$ of the arc $[q-.001,P/2]$ and the degree-$m$ minorant $L$ of $[q+.001,P/2]$. They have one-sided integrated excess and deficit $P/(m+1)$ each with respect to ordinary length. These polynomials bracket their interval indicators off the endpoints. The majorant bounds either endpoint convention from above and the minorant from below by continuity of the polynomials. Put $p=(V+L)/2$, $d=(V-L)/2$. Then $d\ge0$. Any allowed reply $O$ satisfies $|O-p(S)|\le d(S)$ when $|S|<P/2$ since $|\log(1\pm2^{-12})|<.001$. The exact indicator of $S>q$ obeys the same bound. Only scalar frequencies $|2\pi j/P|\le 2\pi(T+1)$ occur. Their coefficient absolute sum for $p,d$ is $O(m)$ since each coefficient is bounded by the normalized $L^1$ norm, at most $1+O(1/m)$ for either one-sided approximant. [Vaaler’s periodic approximation](https://doi.org/10.1090/S0273-0979-1985-15349-2) · [Murty–Sinha, explicit interval polynomials and integrals, §3](https://www.iiserkol.ac.in/~kaneenika/Effective-Equidistribution.pdf)

Integrating on $-P/2<S<P/2$ gives
$$
 \mathbb E[d(S)\mathbf1_{|S|<P/2}]
 \le \tfrac12\Pr(|S-q|\le.001)+\frac{CP}{(m+1)\sqrt r}<.027a_r
$$
for sufficiently large absolute $T$. Large scalar bandwidth enters the constants only. Uniform approximation of the discontinuous comparison to error $1/\sqrt R$ at every scalar point would instead require growing bandwidth.

## Sparse products of the local complex powers

For each scalar frequency $|t|\le2\pi(T+1)$ write $g_t(x)=e^{itY(x)}$, assigning any value of magnitude at most one at the two cosine zeros. Let $g_j$ be its Fejér mean with multiplier $(1-|k|/2^j)_+$, $\Delta_0=g_0$ and $\Delta_j=g_j-g_{j-1}$ for $j\ge1$. For $d_x$ the distance to the nearer zero, constants depending only on $T$ give
$$
 \|\widehat{\Delta_j}\|_1\le C_T,\qquad
 |\Delta_j(x)|\le C_T 2^{-j}/d_x\quad(d_x>0).
$$
For the first inequality, $|\widehat g_t(k)|\ll_T1/|k|$ for $k\ne0$. To see this remove arcs of radius $1/|k|$ around the two zeros. Their integrals are $O(1/|k|)$. Off those arcs integrate twice by parts, using $|g_t'|\ll_T1/d_x$ and $|g_t''|\ll_T1/d_x^2$. The boundary terms and integral are $O_T(1/|k|)$. Small $k$ obey the bound by $|g_t|=1$ almost everywhere. The difference of the multipliers up to $2^{j-1}$ is $|k|/2^j$, and the remaining terms span a single dyadic interval. For the pointwise bound the symmetric Fejér kernel of scale $n=2^j$ has mass $O(1/(nd_x))$ outside $|u|<d_x/2$. Inside, use the second difference $O_T(u^2/d_x^2)$ and the kernel bound $O(1/(nu^2))$. This bounds $|g_t-g_j|$ by $O_T(1/(nd_x))$ and gives the displayed difference estimate, including $j=0$ after adjusting the constant.

In each scalar summand replace $e^{itS}=\prod_i g_t(x_i)$ by
$$
 \sum_{j_i\ge0,\ \sum j_i\le4U}\prod_i \Delta_{j_i}(x_i).
$$
Denote the resulting real polynomials by $p_*,d_*$. Their coordinate degrees are less than $2^{4U}$ and their Fourier absolute sums are at most $H=C_T m C_T^R\binom{4U+R}{R}$. Thus $\log_2 H=O_T((1+\log A)R)$. They exist for the proof and need no construction by the decoder.

Call a point good when $\sum_i u_i\le U$ with $u_i=\lfloor\log_2(1/d_{x_i})\rfloor$, taking $u_i=+\infty$ at a zero. On good points $2|\cos(2\pi x_i)|=2\sin(2\pi d_{x_i})\ge8d_{x_i}$, so $|S|<P/2$. Absolute convergence of the dyadic telescoping there and the difference bound give a truncation error for each scalar product of at most
$$
 (2C_T)^r 2^U\sum_{k>4U}\binom{k+r-1}{r-1}2^{-k}
 \le (2C_T)^r(1-2^{-1/2})^{-r}2^{-U}.
$$
Both polynomial approximations therefore have good-set error at most $E=O_T(m)C_2^R2^{-U}$.

## A majorant on the finite grids

The bad set lies in the union of the rectangles $d_{x_i}\le 2^{-v_i}$ with $v_i\ge0$, $\sum_i v_i=U$. For each radius $\rho=2^{-v_i}$ majorize the event by the constant one for $\rho\ge1/8$, and otherwise by the sum of two tents of radius $2\rho$ and height two at the cosine zeros. On any odd grid of order $D_i$, use zero when $\rho<1/(4D_i)$ since the event is empty. Each local majorant has Fourier absolute sum at most four, as a height-one centered tent is a normalized interval self-convolution with nonnegative coefficients summing to one. Its uniform continuous or grid mean is at most $C_3\rho$, by the count of grid points in an interval and $1/D_i\le4\rho$ when the event can be nonempty. Independent axes under Haar measure or uniform CRT averaging give the sum $B$ of the product majorants the bounds
$$
 B\ge\mathbf1_{\rm bad},\qquad
 \mathbb EB\le J C_3^R2^{-U},\qquad
 \|\widehat B\|_1\le J4^R,\qquad J=\binom{U+R}{R}.
$$
At a continuous zero the same union covers the point. The grid-specific zero majorants are used only for grid estimates.

Choose $A$ after fixing $T$ so that $E$ and $(10+10H)JC_3^R2^{-U}$ are each below $.0001c/\sqrt R$ for $R\ge2$. This is possible since the positive prefactors have logarithms $O_T((1+\log A)R)$. Against continuous measure, the scalar estimate on the good set and the bad-set bounds imply
$$
 \widehat d_*(0)<.029a_r,\qquad
 |\widehat p_*(2,0,\ldots,0)-a_r|<.029a_r.
$$
Indeed the mean error of $p_*$ relative to the exact indicator is bounded by $\mathbb E[d(S)\mathbf1_{|S|<P/2}]+E+(1+H)\Pr(\text{bad})$. The upper bound for the mean of $d_*$ follows in the same way.

Trial-divide beyond $2^{4U+2}$ so neither the mean nor the axial coefficient of the sparse polynomials aliases on the CRT grid. For its possibly adversarial oracle replies take the finite majorant
$$
 C_*=d_*+2E+(1+2H)B.
$$
On good points $|O-p_*|\le C_*$ by the one-sided scalar bounds. On bad points the bound follows from $|O|\le1$, $|p_*|,|d_*|\le H$, $B\ge1$. Thus every unit reply obeys the same pointwise majorant and $\widehat C_*(0)<.030a_r$. Both $C_*$ and $p_*$ have grid Fourier absolute sum $2^{O(R)}$, including the aliased tent tails. The coefficient of $p_*$ at every required CRT axis is at least $.971a_r$ in real part.

The original decoder now applies with this pair. For clarity, if $T_0$ bounds the two Fourier absolute sums and $\nu=c/\sqrt R$, choose Fejér half-window $L_0\gg T_0/\nu$ and enumerate a dilation set of bias much less than $\nu/T_0$. Raise the trial cutoff beyond $R(2L_0+1)(2b+4)$ as well. For any nonzero residual frequency difference the random-dilation mean of its nonnegative Fejér multiplier is at most $1/(L_0+1)$ plus the bias. Weighted by the Fourier magnitudes of both polynomials, this supplies an enumerated dilation with total unwanted contribution less than $\nu/200$ at any designated axial frequency and at zero for $C_*$. The same bound holds on all translated rows. A translation making all queried frequencies units exists by the finite exclusion count in the original proof. On each row the majorant error is at most $.030a_r+\nu/200$. The anchor, mesh and dyadic shifts of that proof recover the axial frequency, whose additive order yields one whole prime-power block. Exhaustive search of the same mesh and dilations recovers every block. Enumerating the trial factors, shifts and small-bias support costs $2^{O(R)}\operatorname{poly}(b)$. For unrestricted inputs take $R=\lceil\sqrt b\rceil$ and include $2^R$ in the cutoff. More than $R$ remaining primes would then have product exceeding $2^b$. [Deterministic dilation, translation and phase recovery](unpadded-magnitude-threshold.md#randomized-and-deterministic-decoding)

## Finite replay

Run `gp -fq experiments/sparse-magnitude.gp`. At all residues of $35,77,143,385,819$, the check compares literal root sums with the local product, evaluates the degree-1,535 one-sided polynomials, brackets all 4,405 admissible replies at three thresholds, and measures the error on each CRT axis. The 28 ambiguous grid points test both replies. The largest ratio of the mean half-width to an axial coefficient at the two fixed thresholds was 0.239, on modulus 77. Small grids can thus require more resolution than the displayed finite parameters. The proof's no-aliasing cutoff is much larger.

On all 315 points of the grid with orders 5, 7 and 9, the mean errors in the sparse complex-power products at total levels 4, 8 and 12 were respectively $(.17264,.03075,.00408)$ for $t=1/2$, $(.87585,.51797,.16671)$ for $t=2$ and $(.98671,.86734,.56469)$ for $t=6$. The script obtains the even Fourier coefficients from the beta integral recurrence and compares the sparse sum with direct complex exponentiation. These are 38-digit PARI numerical checks. The uniform estimates are paper proofs. [Replay](../experiments/sparse-magnitude.gp)
