# Divisor-moment error budgets for the fixed conditional score

On the conservative fixed schedule, divisor-moment bounds can discard the close-pair contribution to the quadratic normalized-mass term in part of the intermediate-length range. The same bounds are too large to replace the linear normalized-mass term by zero. This gap persists in actual dyadic subboxes of the first field with the second field still unrestricted, even if its average is supplied exactly. [Divisor-moment certificate](cogentic-intermediate-count.md) · [Fixed conditional score](cogentic-conditional-score.md)

## The size of the computed bound

Use $L=\log N$, $D=(L/\log L)^{1/3}$, $H=D\log L$ and $V=DH$. The conservative schedule has $\log B=(1000+o(1))H$, $\log A=(10000+o(1))H$, $\log U=(100000+o(1))V$ and marked values of height $\exp((\lambda+o(1))V)$ with $\lambda=100001$. Let $\rho=\lambda/3000$. For a unit progression of length $t$ with $\log t=(\tau+o(1))V$, $0<\tau<\lambda$, whose endpoints both have this height, the divisor-moment upper bound $U_{\rm mom}$ itself satisfies
\[
               U_{\rm mom}=\exp\bigl((-\tau/3000+o(1))H\bigr) .           \tag{1}
\]
Here the band may omit polynomially many primes in $L$. The known upper bound follows by taking $m=\lfloor\log t/\log B\rfloor$. For the lower bound on the certificate, let $n$ be the number of eligible primes, and $k$ the minimum prime count used in its formula. Uniformly, $n\gg B/\log B$, $k=\Theta(D)$, and the sum of the reciprocals of the eligible band primes exceeds a positive constant. For the latter bound, apply the prime number theorem on dyadic pieces of $(\sqrt B,B]$ and subtract the negligible reciprocal weight of the omissions. In an ordered draw of $m\le k$ different primes, previously drawn primes remove reciprocal mass at most $k/\sqrt B=o(1)$. Thus $m!e_m\ge c^m$ for a fixed $c>0$. The two terms of the certificate obey
\[
 \frac{e_m}{\binom{k}{m}}\ge(c/k)^m,
 \qquad
 \frac{\binom{n}{m}}{t\binom{k}{m}}\ge \frac{(n/k)^m}{t}.
\]
If $m\ge\log t/\log(n/k)$, the second term is at least one. For smaller $m$ the first is at least $\exp(( -\tau/3000+o(1))H)$ because $\log(n/k)=(1000+o(1))H$, $\log k=(1/3+o(1))\log L$ and $D\log L=H$. This proves (1) for the minimum over all orders, including integer rounding. [Schedule and marked-height bounds](cogentic-deterministic-two-thirds.md#fixed-parameters)

## Dyadic subboxes and the linear mass term

Consider the bisection that finishes the first field before starting the second. After the first-field sides have equal lengths, every second decision again produces equal sides. At any fixed $0<\tau<50000.5$, take the attainable side length $X=2^{\lfloor\tau V/\log 2\rfloor}$. The following bounds hold for every aligned first-field square of that size. For a grid mark $a$ retained by the score, the original real-grid estimate and perturbation bound imply
\[
 \log |f_i(a)|=(\lambda+o(1))V,
 \qquad \log q_a=(1+o(1))V,\qquad q_a=P_0\ell|a-m| .
\]
The sign is fixed on the original coefficient box. The marked residue is coprime to $q_a$ outside the at most $d$ target-root classes of the first field modulo $\ell$. Indeed the residue modulo $a-m$ is $k_iN$ and the grid has excluded its nonunits. The reductions modulo $P_0$ are nonvanishing and the second field has no target roots. Let $\mathcal U$ denote the remaining marks. The excluded marks carry grid weight $\exp((-997+o(1))H)$ or less, by the point mass bound $\pi_{\max}\le\exp((-9997+o(1))H)$ and the number of integers in at most $d$ classes modulo $\ell$. Primes dividing the scalar moduli or the cofactor multipliers remove only polynomially many eligible primes in $L$. [Fixed residue checks](cogentic-intercept-sampling.md#realizing-the-obstruction-in-dyadic-subboxes-of-a-fixed-cogentic-score) · [Grid point mass](cogentic-fixed-rank-audit.md#interval-counts-and-signed-centering)

For every $a\in\mathcal U$, fix the slope and vary the intercept in a first-field subbox. This gives $X$ progression members. The normalized window width satisfies
\[
                  \log\frac{|f_i(a)|}{q_a X}=(100000-\tau+o(1))V .       \tag{2}
\]
The progression has intermediate length. A direct scan costs $\exp((\tau+o(1))V)$ and $\tau<\lambda/2$ is below the individual square-root threshold. The small-modulus logarithmic bins also have the large width ratio (2). The eligible residue semigroup modulo $q_a$ already contains $\exp((1/2+o(1))V)$ elements by taking distinct subsets of $\lfloor\log q_a/(2\log B)\rfloor$ primes, whose products are distinct positive integers below $q_a$. The complementary divisor interval has $\asymp P X/|f_i(a)|^2$ members in its prescribed residue class, where $P$ is the eligible band product, since $\log P\gg B$ and rounding contributes at most two to the endpoint count. [Other scalar counting regimes](cogentic-scalar-divisor-count.md) · [Complementary divisor reduction](cogentic-coefficient-selection.md#exact-counts-by-complementary-divisor-windows)

The normalized mass in the sufficient score is
\[
 \widehat C=\sum_a \frac{\pi_0(a)}{Z_1^{(0)}(a)Z_2^{(0)}(a)}I_1(a)I_2(a).
\]
The reference factors are $Z_i^{(0)}(a)=\exp(( -\rho+o(1))H)$ uniformly. This uses $(1-\alpha)\log B=(1/3+o(1))\log L$, $\log F(\alpha)=O(D)$ and the polylogarithmic residue density correction. Let $p_2(a)$ be the exact uniform expectation on the full second-field box. Then $p_2(a)\ge\exp(( -\rho+o(1))H)$ on $\mathcal U$. For instance, in every horizontal slice of this box place a Gaussian at the midpoint with width $q_a(4UA)/(10L_0)$. The width ratio is $\exp(O(H))$ and the Gaussian progression estimate has absolute error $\exp(-\Omega(V))$. Its mass outside the intercept interval is negligible and its normalized point weights are bounded by $10L_0/(4UA)$. The saddle main term is $\exp(( -\rho+o(1))H)$, and losing a polynomial factor in $L$ gives the stated lower bound. [Saddle normalization](cogentic-fixed-window-audit.md#divided-classes-and-numerical-margin) · [Gaussian comparison on a horizontal slice](cogentic-intercept-sampling.md#realizing-the-obstruction-in-dyadic-subboxes-of-a-fixed-cogentic-score)

Now use the returned intervals $[0,U_{\rm mom}]$ for the first-field scalar means. Weighted averaging over slopes preserves the lower bound on their widths from (1). Giving the evaluator the exact $p_2(a)$, the absolute interval width contributed by the linear term $-128\widehat C$ is bounded below by
\[
       128\sum_{a\in\mathcal U}\pi_0(a)
           \frac{p_2(a)}{Z_2^{(0)}(a)}\frac{\exp(( -\tau/3000+o(1))H)}{Z_1^{(0)}(a)}
       \ \ge\ \exp\bigl(((100001-\tau)/3000+o(1))H\bigr)                 \tag{3}
\]
The exponent is at least $100001/6000>16.66$ throughout the open intermediate range. The linear term has one sign across all marks. Its absolute error budget for termwise conditional expectations is $O(1/V)$ before accounting for the other terms. Even the midpoint of the interval has a worst-case interval error of half this width. This conclusion uses the linear term alone.

The same limitation holds for a partition of the one-mark projection into $\exp(O(H))$ disjoint scalar progressions of length at most $X\exp(O(H))$, when it accounts for the full projected law and imposes no extra restrictions. The point mass of $x+ay$ is at most $1/X$, since each fixed slope $y$ gives at most one intercept for a projected value. Thus all pieces with length at most $\exp(O(H))$ have combined weight $\exp(-\tau V+O(H))$. Those pieces can be evaluated exactly with negligible influence on (3). The proof of the lower bound for $U_{\rm mom}$ uses only an upper bound on $t$, so shortening the remaining progressions cannot improve the exponent in (3).

## A weighted discard for close pairs

Keep the second field full and take $30000\le\tau\le50000$. In the term $64\widehat C^2$, discard ordered pairs with $0<|a-a'|\le AK_1^{-1/2}$, where $\log K_1=(100+o(1))H$. Their pair grid weight is at most
\[
             (2 AK_1^{-1/2}+1)\pi_{\max}=\exp((-47+o(1))H).
\]
Pairs including a mark outside $\mathcal U$ and the repeated-mark diagonal can also be discarded at exponential precision in $H$ by using probabilities at most one and respectively the grid weights $\exp((-997+o(1))H)$ and $\exp((-9997+o(1))H)$. The four reciprocal reference factors cost $\exp((4\rho+o(1))H)$.

For the remaining distinct pairs, apply the two-mark rectangle construction to the first-field square with geometric tolerance $e^{-100H}$. There are $\exp(O(H))$ rectangles after splitting by the lattice residues, and each scalar length is at most $X\exp(O(H))$. Drop rectangles with a scalar length below $Xe^{-M H}$ from this upper estimate by charging their whole mass. The per-rectangle mass is at most the product of the two progression lengths divided by $X^2$. A sufficiently large fixed $M$ makes the aggregate charge at most $e^{-100H}$. The geometric tolerance is charged in the same direction. The remaining scalar lengths all have leading logarithm $\tau V$. For either mark the step is its $q_a$ times the lattice residue period $|a-a'|\le A$. The unit mark condition means that a nonempty gcd reduction removes a factor of size at most $|a-a'|$. The reduced heights still have leading logarithm $\lambda V$ and the number of omitted primes stays polynomial in $L$. Thus (1) gives $\exp(( -\tau/3000+o(1))H)$ for each scalar fraction, uniformly. The two fractions multiply on disjoint rectangles whose normalized masses sum to at most one. The first-field pair probability is therefore at most $\exp(( -2\tau/3000+o(1))H)$. [Rectangle construction and error accounting](cogentic-scalar-divisor-count.md#rectangles-for-a-pair-of-marked-values)

In the full second field, uniform-box point weights are bounded by a constant times the original Gaussian weights. The available rough two-point estimate, including close pairs, is $\exp((-2\rho+0.02+o(1))H)$. The normalization and local factors beyond $e^{0.02H}$ have size $e^{o(H)}$. Multiplying the preceding bounds gives the weighted cost of discarding these positive terms as at most
\[
            \exp\bigl((2\rho+0.02-47-2\tau/3000+o(1))H\bigr)
            \ \le\ e^{-0.30H}.
\]
Even at $\tau=30000$ the limiting exponent is $-0.312\ldots$. The same proof discards any family of distinct unit pairs of total grid weight at most $e^{-bH}$ when $b>2\rho+0.02-2\tau/3000$. This covers all close pairs of the mass quadratic at these dyadic depths, uniformly in the chosen subbox. The weighted loss summed over $O(V)$ decisions is still exponentially small in $H$. [Rough two-point estimate](cogentic-deterministic-two-thirds.md#all-required-progression-estimates) · [Centered grid estimates](cogentic-fixed-rank-audit.md)

## What positivity gives at a dyadic split

If a parent has certified mean score at most $u$, nonnegativity alone bounds each child by $2u$. Iterating gives a bound of $2^j u$ after $j$ unresolved binary decisions. This inheritance is sharp using only the parent bound and nonnegativity, as a score supported on one descendant can put all the parent mass there. Even a certified bound $c/d$ with fixed $c>0$ at the start of the intermediate range would guarantee only $O(\log d)$ arbitrary binary decisions this way. Reaching $\exp(O(H))$ side length from there costs $\Theta(V)$ decisions. Splitting into several refinements at once changes the same bound by the reciprocal descendant mass. The estimates above leave open an adaptive strategy that uses correlations among the signed terms, nontrivial certified lower bounds for relation mass, or an independently verified smaller box. [Quantitative initial score bound](cogentic-intercept-sampling.md#one-low-intercept-word-for-all-generator-primes)
