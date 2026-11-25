# Factoring from a fixed magnitude threshold at the input modulus

Let $N$ be odd and let $W_Q(t)=\sum_{r^2=1\bmod Q}e_Q(2tr)$ for unit frequencies. Complete factoring of arbitrary $N$ admits a **Las Vegas polynomial-time reduction** to the single bit $|W_N(t)|>1$, with *every* query at the original modulus $N$. Either answer is allowed independently in $[1-2^{-12},1+2^{-12}]$. The same result holds with every query to the original normalized Kloosterman sum at $Q=N^2$. Randomness selects arithmetic progressions of frequencies; it uses no auxiliary primes. The calculation of the bit directly from an unfactored input remains open.

With a public bound $h$ on the number of distinct primes, a deterministic reduction uses $\exp(O(h\log\log(3h)))\,\mathrm{poly}(b)$ time and unit queries, where $b=\lceil\log_2(2N)\rceil$. This is polynomial for $h=O(\log b/\log\log\log(16b))$. For arbitrary inputs it gives $\exp(O(\sqrt{b\log\log(3b)}))$ deterministic time and queries. A different deterministic polynomial reduction can use one larger padded modulus. [Padded deterministic threshold](kloosterman-threshold.md) · [Salié and stationary-phase identities](salie-and-quarter-parity.md)

## Size of the coefficient and the ambiguous band

Take independent uniform circle coordinates $x_i$ and let $S_r=\sum_{i=1}^r\log|2\cos(2\pi x_i)|$. For $r\ge2$ and any $q\in[-2,0]$, let $f_r$ be its density and $a_r$ the Fourier coefficient of $\mathbf 1_{S_r>q}$ at $(2,0,\ldots,0)$. Each axis gives the same real positive coefficient. For an effective absolute constant $c>0$,
$$
 a_r>.04 f_r(q)\ge c/\sqrt r,\qquad
 \Pr(|S_r-q|\le .001)<.051a_r .
$$
Here is a proof with constants for the relative error. The deficit $Z=-\log|\cos(2\pi x)|$ has density $g(z)=(2/\pi)e^{-z}\psi(z)$ on $z>0$, where $\psi(z)=(1-e^{-2z})^{-1/2}$. Write $C_k=\psi^{*k}$. Scaling the convolution simplex from $v$ to $u$, for $0<u\le v$, gives
$$
 (u/v)^{k-1}\le C_k(u)/C_k(v)\le (u/v)^{k/2-1}.
$$
Indeed $\psi$ decreases and $\sqrt z\,\psi(z)$ increases. At $w=r\log2-s$ we have $f_r(s)=(2/\pi)^r e^{-w}C_r(w)$. In $|s-q|\le.001$, the two bounding logarithmic slopes $-1+(r/2-1)/w$ and $-1+(r-1)/w$ lie in $[-1,1]$. Thus the band has mass at most $.002e^{.001}f_r(q)$.

At $w=r\log2-q$, conditioning on the other deficits makes the single-axis Fourier integral at remaining deficit $z>0$ equal to $\sin(2\arccos(e^{-z}))/\pi=g(z)(1-e^{-2z})$. Hence
$$
 a_r=f_r(q)\, \mathbb E[1-e^{-2Z_1}\mid \textstyle\sum_i Z_i=w].
$$
For $r\ge3$, the conditional density is proportional to $\psi(z)C_{r-1}(w-z)$. Its unnormalized mass below $1/4$ is at most $C_{r-1}(w)$ since $\int_0^{1/4}\psi(z)\,dz\le1$. On $[1/4,1/2]$ the second factor is at least $(1-1/(2w))^{r-2}C_{r-1}(w)>.48C_{r-1}(w)$ by the scaling inequality and $w\ge r\log 2$. Thus the conditional expectation exceeds $(1-e^{-1/2})(.12/1.12)>.04$. For $r=2$, exchangeability gives at least $(1-e^{-w})/2\ge3/8$.

Finally $Y=\log|2\cos(2\pi x)|$ has mean zero by the integral of $\log\cos$ and angle doubling, positive variance, and finite third absolute moment by the displayed deficit density. Berry–Esseen gives an effective constant $M$ with $\Pr(|S_r|\le M)\ge1/\sqrt r$ for sufficiently large $r$: choose $M$ so that the centered Gaussian window exceeds the two endpoint errors by $1/\sqrt r$. The scaling inequality bounds the log-density variation on this fixed window by $4M$ when $r\log2\ge2M$, so $f_r(0)\gg1/\sqrt r$. The finitely many smaller $r$ have an effective positive bound from $C_r(w)\ge w^{r-1}/(r-1)!$. The same log-slope estimate on $[-2,0]$ gives $f_r(q)\ge e^{-2}f_r(0)$. [Shevtsova, iid Berry–Esseen bound](https://arxiv.org/abs/1111.6554)

## Keeping every query at the original modulus

Remove powers of two first. Trial-divide the odd input to the cutoffs specified below. For the Salié version take $Q=N$, and for the square-modulus Kloosterman version take $Q=N^2$. Write $Q=KM$ with $K$ the product of the known prime-power blocks and $M$ the product of the remaining ones. Prime and perfect-power tests settle zero or one remaining prime. Each remaining block $D$ contributes $2\cos(2\pi x_D)$ with $x_D=2(M/D)^{-1}t/D$. CRT chooses the phase on each known block independently. Specifically, use $T\equiv Kt\bmod M$ and choose $T\bmod K$ to give the desired known local phases. Then $|W_Q(T)|=e^A |W_M(t)|$ with known log gain $A$.

Arrange $0\le A\le2$. The block 3 contributes zero log gain. At $D\ge5$, the unit numerator $(D-1)/2$ gives positive log gain below $\log2$. A unit phase in $[1/6,2/9]$ or $[5/18,1/3]$ gives negative log gain above $-\log3$. For $D\ge37$ the first interval has two consecutive numerators. For $D=5,7,9,11,13,17,19,23,25,27,29,31$ suitable numerators are $1,2,2,2,4,3,4,4,7,5,5,6$. Use the positive phase if the current log gain estimated to $.01$ is at most $1.2$, and the negative phase otherwise. These operations preserve $[0,2]$ and require polynomial precision. The unknown part now has threshold $q=-A$.

## Finite Fourier approximants

Use a public $h\ge r$, and decrease $c$ if necessary so $c\le1$. Set $\nu=c/\sqrt h$, $\eta=\nu/(10^4h)$, and choose a circle shift scale $\rho=\eta\,2^{-18}/h$. Let $F=\mathbf 1_{S_r>q}$. Define $B$ to be the union of $|S_r-q|\le .001$ and the sets $|\cos(2\pi x_i)|\le2\eta$. Its measure is at most $.051a_r+2h\eta$, since $\Pr(|\cos(2\pi x)|\le u)=2\arcsin(u)/\pi\le u$ for $0\le u\le1$.

Convolve $F$ and $B$'s indicator with a product of $r$ normalized continuous Fejér kernels of degree $m$. Let the resulting trigonometric polynomials be $P$ and $C_0$. Choose $m=\mathrm{poly}(h)$ large enough that $2/(m+1)\le .001$ and the kernel probability of a shift larger than $\rho$ in any coordinate is at most $\nu/1000$. This follows from the one-dimensional Fejér tail $O(1/(m\rho))$ and a union bound. Put $C=C_0+\nu/1000$. For every valid Boolean reply at a unit grid point,
$$
 |O-P|\le C,\qquad
 \widehat C(0)<.053a_r,\qquad
 \widehat P(2,0,\ldots,0)\ge.999a_r.
$$
For the pointwise assertion, consider a shift with all coordinates at most $\rho$. If its shifted point is outside $B$, the cosines there exceed $2\eta$ in absolute value. Along the shift they exceed $\eta$, and the total log change is at most $2\pi h\rho/\eta$. This is smaller than the difference between $.001$ and the log width of the allowed oracle band. The shifted exact bit and the original reply therefore agree. Integration gives the asserted majorant, including arbitrary choices inside the band. The axis coefficient uses the Fejér multiplier $1-2/(m+1)$.

For residual prime powers $D>2m+4$, the pullback to $\mathbb Z/M$ preserves both means and the specified coefficients exactly by CRT and absence of local frequency aliasing. Write $c_D=(M/D)^{-1}\bmod D$. The resulting target $f=4c_D(M/D)\bmod M$ has additive order $D$. Both polynomials have pointwise magnitude at most two, hence normalized squared Fourier mass at most four. Their Fourier absolute sums are at most $T_0=2(2m+1)^{h/2}$ by Cauchy–Schwarz. They are used only to prove the decoder's guarantees.

## Randomized and deterministic decoding

For $|k|\le L$ let $w_k=(L+1-|k|)/(L+1)^2$. Use rows at shifts $u=0,1,2,4,\ldots,2^J$ with $J=\lceil\log_2 M\rceil$. At mesh tag $x$ a row is $\sum_k w_k O(s+ka+u)e^{-2\pi ikx}$. Choose mesh spacing at most $\nu/(10^4 L)$, and use numerical errors below $\nu/1000$. The same queries serve every tag. For each candidate tag divide its shifted rows by its nonzero anchor at $u=0$, retaining anchors of magnitude at least $\nu/2$. At a tag where all rows approximate $\widehat P(f)e_M((s+u)f)$ to error at most $.07a_r$, each quotient lies within $.16$ of $e_M(uf)$. Rounding to the nearest of 32 directions gives circular error below $1/16$. Starting at the last dyadic shift, choose each successive modular half nearest the preceding direction. The distance to the correct predecessor stays below $1/4$, and at $u=1$ the error is less than $1/(2M)$. Nearest integer rounding recovers $f$. Test additive orders by division and prime-power recognition. An order $D$ yields its entire prime-power block, by an integer square root in the square-modulus version. Accept only verified blocks and finish when their product accounts for the input. [Phase recovery and public meshes](kloosterman-localization.md#keeping-the-error-bounded-through-doubling)

For the **randomized algorithm**, use $h=b$, and draw $a,s$ independently uniformly modulo $M$. Choose $L$ an integer larger than $10^9 h(J+2)/\nu^2$ using the public bound $J\le2b+1$ when choosing the trial cutoff. Trial-divide beyond $2m+4$, $2L+1$, and $100h(2L+1)(2b+4)$. With probability at least $.99$ every residual sample is a unit, by a union bound. At the true tag $af/M$, the mean squared interference of the $P$ row is at most $4/(L+1)$. Indeed the random translation cancels cross terms between different Fourier modes. For any $g\ne f$, averaging $\left|\sum_k w_k e_M(ka(g-f))\right|^2$ over the dilation leaves only the diagonal terms $\sum w_k^2\le1/(L+1)$, since every nonzero difference frequency has additive order exceeding $2L$. The same bound controls interference of a $C$ row at tag zero around $\widehat C(0)$. Equivalently, distinct sampled locations are pairwise independent when their spacing is coprime to $M$.

Chebyshev and a union bound over at most $h(J+2)$ target rows and $J+2$ majorant rows make every interference smaller than $\nu/200$ together with probability greater than $.9$. On this event the sum of the two interferences, $\widehat C(0)$, mesh error and numerical error is below $.07a_r$. The majorant controls all allowed answers separately at each query. This reasoning permits replies chosen after seeing the sampled frequencies. Every desired tag is tried, and all remaining blocks are then recovered in that trial. Reject a trial containing a nonunit or incomplete verified output and repeat. This gives expected polynomial bit cost. General randomized significant-Fourier algorithms are also known for fixed bounded signals. [Akavia–Goldwasser–Safra, heavy Fourier learning](https://www.cs.tau.ac.il/~safra/PapersAndTalks/hardcore.pdf)

For the **deterministic algorithm**, choose $L\gg T_0/\nu$ and a public $\epsilon$-biased dilation support with $\epsilon\ll\nu/T_0$. Enlarge the trial cutoff beyond $2m+4$, $2L+1$ and $h(2L+1)(2b+4)$. The Fejér kernel $K_L(v)=\sum w_ke^{2\pi ikv}$ is nonnegative and has mean at most $1/(L+1)+\epsilon$ over this support at any nonzero difference frequency. For each desired $f$ some enumerated $a$ makes
$$
 \sum_{g\ne f}|\widehat P(g)|K_L(a(g-f)/M)
       +\sum_{g\ne0}|\widehat C(g)|K_L(ag/M)<\nu/200
$$
by averaging. This single bound controls every translation and every dyadic row for that target. The second sum suppresses the possible gap errors uniformly in all those rows. Choose a translation from $0$ through $h(2L+1)(J+2)$ making every sample a unit, by gcd checks. Each residual prime exceeds this range and excludes at most $(2L+1)(J+2)$ candidates. The mesh and phase decoder give $\mathrm{poly}(T_0,h,b)$ cost including trial division. [Explicit small-bias support and Fejér isolation](kloosterman-threshold.md)

## Reducing the deterministic Fourier absolute sum

For the sharper bound in the introduction it suffices to replace the two proof polynomials by ones of Fourier absolute sum $\exp(O(h\log\log(3h)))$. Keep $\eta,\rho,m$ as above. Clip each logarithm to $Y^*(x)=\log(2\max(\eta,|\cos(2\pi x)|))$ and put $S^*=\sum Y^*(x_i)$. This differs from $S_r$ on a set of measure at most $h\eta$. Each $Y^*$ has total variation $O(\log(2h))$.

Use an integer period $P_0>4h(|\log(2\eta)|+4)$ of order $O(h\log(2h))$ for the real variable $S^*$. On this interval construct two scalar trigonometric polynomials $p(z),d(z)$ taking values in $[0,1]$. The first agrees to error $\epsilon=\nu/10^5$ with the indicator of $z>q$ at distance greater than $.0001$ from $q$ throughout the attained range. The second is at least $1-\epsilon$ when $|z-q|\le .0004$ and at most $\epsilon$ when $|z-q|>.0006$. Their physical frequencies $2\pi j/P_0$ have magnitude $O(\log(2h))$. For the construction convolve the two interval indicators $[q,P_0/2]$ and $[q-.0005,q+.0005]$, periodically, with a nonnegative Fejér kernel of degree $O(P_0)$ with sufficiently large absolute multiplier. The mass past distance $.0001$ is below $1/16$. Compose each result with the polynomial $\Pr[\mathrm{Binomial}(k,v)>k/2]$ for an odd $k=O(\log(2/\epsilon))$. The binomial tail bound gives the required accuracy, degree $O(P_0k)$ and range. Each scalar Fourier absolute sum is polynomial in $h$ by Cauchy–Schwarz.

Now convolve $p(S^*)$ with the original product of angular Fejér kernels. For the majorant convolve $d(S^*)+\sum_i\mathbf 1_{\{|\cos(2\pi x_i)|\le2\eta\}}$ with the same kernel and add $2\epsilon+\nu/1000$. For a shift of size at most $\rho$ in each coordinate, any near-zero shifted cosine is covered by the sum of indicators. Otherwise $S^*$ equals the shifted true log and the change in log magnitude is at most $2\pi h\rho/\eta$. If $|S^*-q|\le .0004$ the window polynomial covers an arbitrary reply. Outside that range the reply and the scalar comparison agree up to $\epsilon$. The kernel tail costs at most $\nu/1000$. Thus the new majorant still dominates the absolute row error pointwise.

Before angular convolution, the new signal differs in mean absolute value from the exact bit by at most $\epsilon+h\eta+\Pr(|S_r-q|\le .0001)$. The majorant's mean after convolution is at most $3\epsilon+3h\eta+\nu/1000+\Pr(|S_r-q|\le .0006)$. The density-slope inequality above bounds these two window probabilities by $2v e^v f_r(q)$ at radius $v$. Including the axial Fejér multiplier, the new signal coefficient exceeds $.99a_r$ and the majorant's mean is below $.033a_r$. This leaves the same slack for decoding.

For a scalar frequency $\tau$ each separated factor $e^{i\tau Y^*(x)}$ has variation $O(|\tau|\log(2h))$. Its $j$th nonconstant Fourier coefficient is bounded by the variation divided by $2\pi|j|$, by integration by parts. The angular convolution cuts off at degree $m=\mathrm{poly}(h)$. Thus each local Fourier absolute sum is at most $1+O(|\tau|\log(2h)\log(2m))=O((\log(3h))^3)$. Multiplying the $r$ sums and the polynomial scalar-mode cost gives the stated bound. Each one-axis indicator in the majorant adds only $O(\log(2m))$. All polynomials have angular degree at most $m$, so the original no-aliasing argument applies.

Substituting this absolute sum for $T_0$ proves the deterministic bound. On unrestricted inputs take $h$ a sufficiently large absolute multiple of $\sqrt{b/\log\log(3b)}$ and include $\exp(h\log\log(3h))$ in the trial cutoff. More than $h$ remaining primes would have product exceeding $N$. Large constants in the Fourier approximations make the asymptotic schedules unsuitable as numerical parameters for the replay.

## Numerical checks

A finite decoder with a Fejér half-window of 2,048 recovered every residual prime-power block in the first sampled progression for each fixture below. Its only signal input was a Boolean oracle on unit frequencies at the original integer. The two oracle policies flipped every comparison in the interior of the allowed band or alternated the in-band answers. Nonunits received dummy zeros in these numerical runs. The asymptotic proof above rejects progressions containing nonunits and uses a larger exhaustive tag mesh.

| Distinct blocks | Known blocks fixed before sampling | Unit queries per policy | In-band replies per policy |
|---:|---|---:|---:|
| 3 | none | 229,365 | 26 |
| 5 | none | 335,760 | 32 |
| 8 | none | 499,441 | 49 |
| 8 | 9, 25, 7 | 335,799 | 23 |
| 12 | none | 662,936 | 46 |

The frozen log gain was $0.506588437$ and the remaining five blocks were recovered from phase measurements. Literal CRT root sums independently check the synthetic oracle on each fixture. A separate numerical convolution checked 323 pairs of block count and shifted threshold for $2\le r\le20$. At mesh width $2^{-17}$ the minimum scaled coefficient lower bound was $0.073131887$ and the maximum ratio of band upper bound to coefficient lower bound was $0.001258458$ after upward rounding. The grid brackets the discretization error. Floating-point roundoff is outside those brackets. Run the NumPy replay with no arguments for the factoring fixtures, or with the density option and grid precision 17 for the convolution. [Decoder, synthetic oracle and convolution replay](../experiments/unpadded-magnitude.py)

## Short frequencies for a two-block input

Suppose $n$ has exactly two distinct odd prime divisors, including arbitrary positive multiplicities. One can deterministically factor $n$ using only $O(\log^2(2T))$ fixed-gap comparisons on the **original modulus**, at unit frequencies $1\le |t|\le T$, with additional bit cost
$$
 (1+\sqrt n/T)\,\mathrm{poly}(\log n),\qquad 1\le T\le\sqrt n/12 .
$$
Thus $T=\lfloor\sqrt n/12\rfloor$, or $\sqrt n$ divided by a fixed power of $\log n$, suffices in deterministic polynomial time. The tolerated gap remains the constant $2^{-12}$ at threshold one. The decoder uses a one-dimensional Fourier coefficient and an elementary alternative when the dyadic dilations stay close to small rational numbers.

Let $r$ be a mixed root of $r^2=1\bmod n$ and $\alpha=2r/n\bmod1$. At these frequencies, $W_n(t)=2\cos(4\pi t/n)+2\cos(2\pi t\alpha)$. The magnitude differs from $2+2\cos(2\pi t\alpha)$ by at most $16\pi^2 T^2/n^2$. For sufficiently large $n$, every permissible bit agrees with $F(t\alpha)$, $F(x)=\mathbf 1_{\{\|x\|<1/3\}}$, unless the circle point lies within $.001$ of $1/3$ or $2/3$. This follows directly from the cosine slope at both boundaries and the fixed gap.

Choose $D=10^8$ and convolve $F$ with the normalized circle Fejér kernel of degree $D$ to obtain $P$. Convolve the indicator of the $.002$-neighborhoods of the same two endpoints with the kernel and add $.0001$ to obtain $C$. The kernel mass past $.0005$ is at most $1/(2(D+1)\cdot .0005)$. Hence $|O(t)-P(t\alpha)|\le C(t\alpha)$ at every allowed query. The mean of $C$ is below $.009$, and $\widehat P(1)=(1-1/(D+1))\sqrt3/(2\pi)>.27$. Let $d_0=D+1$, $\epsilon=1/(8d_0^2)$ and choose a fixed integer $L\ge 10^4(2D+1)/\epsilon$. Call $a$ good when $\|ja\alpha\|\ge\epsilon$ for all $1\le j\le d_0$. At a good dilation each unwanted Fejér multiplier is at most $1/(4(L+1)^2\epsilon^2)$. Both coefficient absolute sums are at most $2(2D+1)$, so the total unwanted contribution from $P$ at tag $a\alpha$ and $C$ at tag zero is below $.001$, uniformly in every translation.

Try all $a=1,2,4,\ldots\le T/(4L)$ and all shifts $u=0,1,2,4,\ldots,2^J\le T/4$, with $J$ maximal. Put $U=(2L+1)(J+2)$. If trial division through $2U$ finds a prime, its full power can be removed and the other block recognized. Otherwise choose $s\in[0,2U]$ making each $s+ka+u$ a unit by the same two-prime exclusion count as above. For $T$ greater than a sufficiently large fixed multiple of $\log(2n)$ these frequencies have absolute value at most $T$. Smaller $T$ requires no query at all for the asserted tradeoff: cover the possible roots by $O(\sqrt n)$ translated small-root intervals, absorbing $T$ into the polynomial factor.

For each dilation try every tag on a mesh of spacing at most $10^{-4}/L$. At a good dilation the preceding row estimates, including the nonnegative majorant, give error below $.012$ at the nearest tag, allowing $.001$ for arithmetic error. Dyadic phase recovery therefore estimates $\alpha$ within $1/(16\cdot 2^J)$ on the circle. Each candidate gives two possible mixed-root centers $n(\widetilde\alpha+j)/2$, $j=0,1$, with error $O(n/T)$.

If every dilation tried is bad, write $\rho_j$ for a rational of denominator at most $d_0$ within $\epsilon$ of $2^j\alpha$ on the circle. Distinct reduced rationals of these denominators are separated by at least $1/d_0^2$. Since $3\epsilon<1/d_0^2$, one has $\rho_{j+1}=2\rho_j\bmod1$. The signed errors double exactly at each step, so initially $\alpha$ is within $\epsilon/2^{j_{\max}}=O(L/T)$ of $\rho_0$. The decoder always tries the two centers for every such rational as well. It never needs to determine whether a hidden dilation was good.

Split each candidate interval into $O(1+\sqrt n/T)$ intervals of radius at most $\lfloor\sqrt n\rfloor$. Translating the monic quadratic $X^2-1$ and using Coppersmith's inclusive small-root corollary lists all roots there in polynomial bit time per interval. A mixed root gives the two full blocks by gcd with $r-1$ and $r+1$. Endpoint rounding and wraparound change the number of intervals by an absolute constant. [Coppersmith, Corollary 1](https://www.di.ens.fr/~fouque/ens-rennes/coppersmith.pdf#page=11)

The individual one-third tests also have a sharp arithmetic margin. For $n\ge145$, a unit $0<|t|\le\sqrt n/12$ and $v_3(n)\ne1$, let $A=\min(2tr\bmod n,-2tr\bmod n)$ and $k=3A-n$. Then $k^2\equiv36t^2\bmod n$. Since $36t^2<n$, either $k^2=36t^2$ or $k^2\ge n+36t^2$. The equality would force $n\mid3(r-1)$ or $n\mid3(r+1)$. When $9\mid n$, the signs of a root are already fixed modulo $n/3$, and when $3\nmid n$ this directly forces a rational root. Thus the mixed root is at distance at least $1/(3\sqrt n)$ from the one-third boundary in phase. On $[1/4,5/12]$ the slope magnitude of $2\cos(2\pi x)$ is at least $2\pi$. Outside this interval the cosine comparison already has a constant margin. Subtracting the public cosine error gives $\big||W_n(t)|-1\big|\ge1/\sqrt n$, and the exact upper outcome equals $3A<n$. When $3\parallel n$, the other block forces $A/n=1/3\pm2|t|/n$. Writing $y=4\pi|t|/n$ gives $W_n(t)=\cos y\pm\sqrt3\sin y$ and $y\le\big||W_n(t)|-1\big|\le2y$. The gap at $t=1$ on this family is of order $1/n$.

The replay checks 287,062 ordinary short-frequency gaps and 40,534 cases with $3\parallel n$. It also generates intervals and passes them to PARI's translated modular small-root solver. On $n=1000036000099$ the phase decoder used 4,700 unit queries, including 22 ambiguous replies, and recovered the factor 1,000,033. The largest queried frequency was 65,536, below the limit 83,334. A separate adjacent-prime fixture exercises the small-rational case. Both in-band reply policies were checked. [End-to-end short-frequency and lattice replay](../experiments/short-magnitude.py)
