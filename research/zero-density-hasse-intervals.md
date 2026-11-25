# Power saving for exceptional smooth Hasse intervals from classical zero density

For any fixed $5/6<\sigma<1$ there is an absolute constant $C=C(\sigma)$ with the following property. For $P$ a large power of two, put $L=\log P$, $\log Y=C L^{2/3}(\log L)^{4/3}$ and $V=\exp(1000 L\log L/\log Y)$. At most $P^{\sigma+o(1)}$ primes $P<p\le2P$ have fewer than $\sqrt P/V$ different integers $n=4m$ with $m$ odd and $Y$-smooth in $|n-(p+1)|\le\sqrt p$. The only zeta inputs are the classical Vinogradov–Korobov region, the explicit formula, and Huxley's zero-density estimate. [Huxley, equation (1.9), pp. 164–165](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0015/PPN356556735_0015.pdf#page=168) · [Ford, explicit zero-free regions](https://arxiv.org/abs/1910.08205) · [Explicit formula and zero counts](https://people.maths.ox.ac.uk/greenbj/papers/primenumbers.pdf)

## The logarithmic product measure

Choose a fixed $g$ with $3/(2(3\sigma-1))<g<1$. In the [odd smooth product construction](many-prime-hasse-intervals.md) use $J=\lfloor gL/\log Y\rfloor$, $T=P/4$, $z_0=Y/2$ and $Z=3T/(Y z_0^{J-1})=P^{1-g+o(1)}$. The same distinct-prime subset construction supplies a set of odd smooth cofactors in $[Z,1.11Z]$ whose reciprocal mass is between $V^{-1/50}$ and $O(1)$. This remains valid for $g$ arbitrarily close to one and fixed because $\log Z/\log Y$ tends to infinity. Use $D(t)=\sum_{m\in\mathcal M}m^{-1-it}$ and
$$
 P_1(t)=\sum_{r\ \mathrm{prime}}\frac{\log r}{r}W(r/Y)r^{-it},
 \qquad P_0(t)=\int W(r/Y)r^{-it}\frac{dr}{r}.
$$
The measures with transforms $DP_1^J$ and $DP_0^J$ are discrete and continuous in their prime slots respectively. Smooth them on the log scale with a positive kernel $K_h$ supported on $[-h,h]$, $h=1/(100\sqrt P)$, normalized to integral one. Require $K$ bounded below on $[-1/4,1/4]$ and $W=1$ on $[1/4,7/10]$ with support in $(1/6,5/6)$. The continuous short convolution is uniformly at least $V^{-1/10}$ on $[\log T,\log(2T)]$. Indeed $J-1$ prime variables in $[z_0,z_0(1+1/(10J))]$ cost $(c/J)^{J-1}$. For each such choice and each cofactor the last variable ranges across a relative $h/4$ window on the plateau, cancelling the $1/h$ normalization. These estimates and the atom bound below use $J\log(C_1 L)\le (1/100)\log V$ for fixed $C_1$ and all sufficiently large $P$.

Take both cutoffs of Gevrey class two, in the logarithmic variable for $W$. For example, form smooth transitions by integrating and normalizing the product of $e^{-1/u}$ and $e^{-1/(1-u)}$ on $0<u<1$, setting it zero outside, then rescale and multiply the desired transitions. Its derivatives of order $j$ are bounded by $A^{j+1}(j!)^2$. For $e^{-1/u}$ Cauchy's estimate on a complex circle of radius $u/2$ gives $j!(2/u)^j e^{-c/u}$, with maximum $\le A^{j+1}(j!)^2$. The product rule preserves the bound, uniformly also after multiplication by $e^{(\beta-1)v}$ on the fixed log support, $0\le\beta\le1$. Integrating by parts $j\asymp\sqrt{|t|}$ times gives transform decay $O(\exp(-c\sqrt{|t|}))$. This construction is needed only for the proof.

## Small frequencies and the contribution near exceptional zeros

Write $T_0=V^4$, $T_1=\sqrt P L^4$ and $H=L^4$. For $|t|\le T_1$ the explicit formula for $P_1(t)-P_0(t)$ is a sum over nontrivial zeros $\rho=\beta+i\gamma$. A zero contributes $O(Y^{\beta-1}e^{-c\sqrt{|t-\gamma|}})$. Discarding $|t-\gamma|>H$ costs $O(P^{-100})$ by the unit-height zero count, for sufficiently large $P$. Replacing prime powers by primes costs $O(Y^{-1/2}L^2)$, and the trivial zeros and endpoint terms fit this bound by a fixed contour shift. The pole is precisely $P_0(t)$. Beyond $T_1$ the integral of either transform against $\widehat K(ht)$ is $O(P^{-100})$ by the cutoff decay and the trivial total masses $O(1)^{J+1}$.

For $|t|\le T_0$ every retained zero is at height at most $T_0+H$. Vinogradov–Korobov bounds the difference of the prime transforms by
$$
 O\!\left(L^{C_2}\exp\left[-\frac{c\log Y}{(\log(3+T_0+H))^{2/3}(\log\log(4+T_0+H))^{1/3}}\right]+Y^{-1/2}L^2+P^{-100}\right).
$$
The saving in the first exponential dominates $\log V$ by a growing factor. Multiplying by $O(T_0 J C_3^J)$ therefore makes the low-frequency difference of the two smoothed convolutions $o(V^{-1/10})$ uniformly at every center.

For $T_0\le |t|\le T_1$ the pole is $O(P^{-100})$. Call a frequency exceptional if a zero of real part greater than $\sigma$ has $|t-\gamma|\le H$. Classify such frequencies by the largest real part among these zeros, in bins $[\beta,\beta+1/L]$ starting at $\sigma$. Put $\delta=1-\beta$. The measure of a bin's frequency set is at most
$$
  2H N(\beta,T_1+H)\ll L^{C_4}(T_1+H)^{3\delta/(3\beta-1)}
   \le L^{C_5}\exp\!\left(\frac{3\delta L}{2(3\sigma-1)}\right).
$$
On it $|P_1(t)|\le L^{C_6}Y^{-\delta+1/L}$ by the explicit formula. Here the real part of every zero in the window is at most $\beta+1/L$. The bound also absorbs the prime powers and the pole. Since $|D|,|\widehat K|=O(1)$, summing the absolute integrals over all $O(L)$ bins gives
$$
  \int_{\rm exceptional}|D P_1^J\widehat K(ht)|\,dt
  \ll \max_{\delta}\exp\!\left[-\left(g-\frac3{2(3\sigma-1)}\right)\delta L
              +O(\delta\log Y+J\log L+\log L)\right].
$$
The bin width costs $O(1)$ in the exponent. For every occupied bin, $\delta L\gg L^{1/3}/(\log L)^{1/3}$ by Vinogradov–Korobov through height $T_1+H$. The rounding term $\delta\log Y=o(\delta L)$. Both $J\log L$ and $\log V$ are at most a constant times $C^{-1}L^{1/3}/(\log L)^{1/3}$. Choosing $C$ sufficiently large makes this integral $o(V^{-1/10})$. Thus even though these frequencies may have large prime sums, their whole contribution is uniformly small in physical space.

## Mean square on the remaining frequencies

For the remaining $T_0\le|t|\le T_1$, the explicit formula gives $|P_1(t)|\le L^{C_6}Y^{-(1-\sigma)}$. Separate $J_1=\lfloor L/(2\log Y)\rfloor$ prime slots. On this region
$$
                   |P_1(t)|^{2J_1}\le P^{-(1-\sigma)+o(1)}.
$$
The other slots form $D'(t)=D(t)P_1(t)^{J-J_1}=\sum a_u u^{-it}$. Its support lies between $P^{1/2-o(1)}$ and $P^{1/2+o(1)}$ since all primes lie in $(Y/6,5Y/6)$ and the $m$ lie in $[Z,1.11Z]$. For each $u$ the ordered prime choices successively divide $u$ and determine $m$. This gives $0\le a_u\le u^{-1}(C_7 L\log Y)^J=u^{-1}P^{o(1)}$, and hence $\sum |a_u|^2\le P^{-1/2+o(1)}$. The Dirichlet-polynomial mean value theorem through $T_1$ yields $\int_{-T_1}^{T_1}|D'(t)|^2dt\le P^{o(1)}$. The continuous prime transform is negligible on this frequency range by Gevrey decay. Plancherel therefore bounds the squared integral of the remaining physical-space error by $P^{-(1-\sigma)+o(1)}$. [Montgomery–Vaughan mean value estimate](https://doi.org/10.1112/jlms/s2-8.1.73)

Chebyshev's inequality and the uniform estimates leave logarithmic exceptional measure $P^{-(1-\sigma)+o(1)}$. At every other center $x\in[T,2T]$ the short discrete convolution exceeds a constant times $V^{-1/10}$. Each atom there has weight at most $P^{-1}(C_8 L)^J$ since at most $O(L/\log Y)$ possible prime divisors occur in each slot, and each slot numerator is at most $\log Y$. The kernel height is $O(\sqrt P)$, so more than $\sqrt P/V$ distinct odd products occur. The disjoint intervals $|x-(p+1)/4|\le1/16$ have log measure $\gg1/P$. Any good center in one supplies the required smooth orders, since multiplication by four takes the kernel window inside the central Hasse interval. The $O(1)$ endpoint primes can be included amongst the exceptions. This proves the stated count. As in the [square-root exceptional estimate](mean-time-elliptic-factoring.md), the bad primes also admit a cover by $P^{\sigma-1/2+o(1)}$ intervals of length $O(\sqrt P)$.

The finite coefficient replay expands 23,400 ordered tuples and checks 3,310 exact rational product coefficients over ten splits of the repeated slots. It also checks the constant inequalities for the zero-density estimate. The earlier prime-window replay tests the distinct-product counting step. Neither calculation samples zeta zeros to infer an asymptotic exponent. [Coefficient replay](../experiments/zero-density-hasse.py) · [Prime-centered windows](../experiments/mean-time-ecm.py)

## Complete deterministic factoring in classical mean time

A deterministic algorithm factors every input $N\ge2$ and has arithmetic mean bit cost
$$
                 \exp\!\big(O(b^{2/3}(\log(2b))^{4/3})\big)
$$
over all $b$-bit integers and over balanced semiprimes $N=pq$ with $P<p,q\le2P$. This deduction only uses classical unconditional theorems. Under ordinary RH the [stronger square-root-exponent mean bound](mean-time-elliptic-factoring.md) applies.

Set $\sigma=167/200$, $g=999/1000$, $\theta=31/200$. Then $g-3/(2(3\sigma-1))=699/301000>0$ and $1-\sigma-\theta=1/100$. Let $T_b$ denote an upper bound of the displayed subexponential order with a sufficiently large absolute constant. Use the [classical large-sieve conic list](average-conic-signs.md). Its construction, small-factor preprocessing, all conic/mark enumeration overhead and all union factors from pairs of conics fit $T_b$. As in that proof, character exceptions cost at most $T_b$ in the arithmetic mean when using the unconditional factorial fallback.

After preprocessing, interleave three computations, allocating elementary bit steps in round-robin order. The first is the factorial search, which produces a proper divisor within $\sqrt p\,\mathrm{poly}(b)$ for the least prime $p$. The second is the small-bias elliptic search with smooth bound $Y$ at the input size. The third consists of at most $O(b)$ auxiliary elliptic searches, one per guess of the least-prime dyad $P<p\le2P$, using smooth cutoff $\lceil(2P)^\theta\rceil$. Even scalar construction in each search is interleaved. Thus on each particular input the total work is at most a polynomial in $b$ times the cost of its fastest successful route.

For every prime $p$ with enough $Y$-smooth central orders, the first elliptic search has target density at least $1/(2V(\log P)^4)$ on the binary cube of size $2P$. Each stage $a$ costs $4^a T_b$. Fixing $p$, the dyad $(U,2U]$ of another prime $q$, and the remaining factor $A$ as in the [mean-time charging argument](mean-time-elliptic-factoring.md#charging-the-entire-running-time), the number of partners reaching stage $a+1$ is $O(U T_b/4^a)$. Here the count fixes the dyad and lets $q$ vary, without requiring that every integer partner be prime. Summing the capped stage costs gives $U T_b$ with a larger constant in $T_b$.

For **every** sufficiently large prime $p$, the odd version of Harman's pointwise theorem supplies $\gg\sqrt p$ central orders $4m$ with $m$ odd and $p^\theta$-smooth. Discarding trace zero loses at most one. Lenstra's mass bound gives $\gg p/\log p$ Legendre parameters having a good twist. For each applicable pair of conics take $H=\lceil(\log(2P))^3\rceil$ marks per sign. At most $O(p/H)$ parameters miss a specified sign, so the successful cube density is $\gg1/\log p$. These marks have height within the preprocessing threshold. The matching auxiliary run for this prime costs $4^a P^\theta T_b$ per stage. Its missed partners again number $O(UT_b/4^a)$ and its total work on them is at most $U P^\theta T_b$. This accounts for its actual cost even on the last sampler stages. [Pointwise odd smoothness and Harman's primary theorem](pointwise-odd-smooth-hasse.md) · [Marked Legendre mass and parity](legendre-average-factoring.md)

Use the auxiliary charge only when $p$ belongs to the $Y$-smooth exceptional set for its dyad, the main charge for all other admissible pairs, and the factorial charge if the conic supply fails. On $X<d\le2X$ there are at most $2X/(pU)$ choices of $A$ and $O(b)$ dyads for $q$. Thus the extra normalized cost of the auxiliary runs at exceptional $p$ is at most
$$
        T_b\sum_{P\le\sqrt{2X}}
              \sum_{\substack{P<p\le2P\\p\text{ exceptional}}}p^{\theta-1}
       \ \ll\ T_b\sum_{P\le\sqrt{2X}} P^{\sigma+\theta-1+o(1)}
       \ \ll\ T_b .
$$
Both outer sums are over powers of two. The strict margin $1/100$ makes the dyadic tail summable. On good primes the total normalized cost is $\le T_b\sum_{p\le2X}1/p$ and a polynomial factor absorbs this sum. Prime powers and primes are recognized in polynomial time. Charging every recursive cofactor $d\mid N$ to its multiples costs at most a further polynomial in $b$, by dyadic summation of $t(d)/d$ as in the complete factoring proof. Dividing by the count of balanced semiprimes changes a dyadic mean by at most $O((\log X)^2)$. No empirical success assumption enters these charges.

## A weaker zero-free hypothesis for the square-root-exponent mean

Separately suppose the ordinary zeta function has
$$
   1-\Re\rho\ \ge\ c\sqrt{\frac{\log\log(3+|\Im\rho|)}{\log(3+|\Im\rho|)}}
$$
at all sufficiently large zero heights, for some fixed $c>0$. Any fixed zero-free strip implies this hypothesis. The full mean-time bound improves to $\exp(O(\sqrt{b\log b}))$. The proof here also uses Huxley and the pointwise odd-smooth fallback. It requires neither ordinary RH nor a statement about zeros of Dirichlet $L$-functions. [Fixed-strip theorem for Dedekind zeta functions, including $\mathbb Q$](https://hexagonmath.org/pdf/2610.00200v2#page=3)

Use $\log Y=C\sqrt{L\log L}$ with $C$ sufficiently large. Compare the *discrete* convolution at scales $h$ and $\eta=V^{-10}$. In the product construction the first $J-1$ slots each have prime weight $\gg1/J$ within a relative $1/(10J)$ of $z_0$, by the ordinary prime number theorem. In the last slot the centered interval of relative length $\eta/4$ lies on the plateau and has prime weight $\gg\eta$. Indeed $\log(1/\eta)/\log Y=10000/C^2$, so even at this smaller choice of $Y$ the last interval has length at least $Y^{3/4}$ on increasing $C$. The classical prime number theorem in short intervals applies uniformly at this scale. Consequently the long *discrete* convolution is at least $V^{-1/10}$ at every center. [Guth–Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552#page=4)

Up to $T_0=V^4$ use $|\widehat K(ht)-\widehat K(\eta t)|\ll\eta |t|$ and $|DP_1^J|\le O(1)^{J+1}$. The absolute integral is $O(C_1^J\eta T_0^2)=o(V^{-1/10})$. Above $T_0$ both kernels are bounded, and above $T_1$ their Gevrey tails give the same negligible integral as before. In each occupied exceptional bin the weaker zero-free hypothesis now gives $\delta L\gg c\sqrt{L\log L}$, while $J\log L$ and $\log V$ are at most fixed multiples of $C^{-1}\sqrt{L\log L}$. Thus the exceptional-bin absolute integral is still $o(V^{-1/10})$. The remaining Plancherel argument and the two elliptic searches apply without change. The resulting bad-prime estimate $P^{\sigma+o(1)}$ is weaker than the square-root exceptional count obtained with ordinary RH, but the pointwise backup fully pays for it.

The cited prime-interval corollary has an upper endpoint for its interval length as well. More explicitly, for a last-slot center of size comparable to \(Y\), tile the required interval of length \(\gg Y^{3/4}\) by intervals of length \(\lfloor Y^{2/3}\rfloor\), discarding the final piece. The full pieces occupy at least half its length for large \(Y\), and their lengths are between the corollary's lower and upper endpoints at each starting point. The asserted prime mass \(\gg\eta\) follows by adding their lower bounds. [Guth–Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552#page=2)

The finite two-search replay completed 378 example factorizations. With intentionally short menus it found 265 splits at smooth cutoff 3, another 103 at cutoff 13, and the final 13 by ordinary trial division. Each prime product was checked. These finite parameters exercise all three routes.

## A smaller classical exceptional exponent

Both exceptional-prime estimates in this note hold for **every fixed \(25/32<\sigma<1\)** at their respective choices of \(Y\). Write \(A(\beta)\) for an exponent such that \(N(\beta,t)\ll_{\epsilon,\beta}t^{A(\beta)(1-\beta)+\epsilon}\) for each fixed \(\epsilon>0\). The following estimates give a fixed upper bound strictly below two throughout \([\sigma,1]\).

| Range, intersected with \([\sigma,1]\) | Upper bound for \(A(\beta)\) |
| --- | --- |
| \([\sigma,4/5]\) | \(9/[8(2\beta-1)]\), since \(25/32>38/49\). [Tao–Trudgian–Yang, Theorem 51](https://arxiv.org/pdf/2501.16779#page=29) |
| \([4/5,9/10]\) | \(3/(2\beta)\). [Ivić, Theorem 9.3, (9.63)](https://bibliotheque.imo.universite-paris-saclay.fr/media/filer_public/86/6d/866d1cf0-a942-4f8a-9d30-7cb3b03e1b1c/i_ivic-66.pdf) |
| \([9/10,1]\) | \(3/(3\beta-1)\), with the uniform loss \((\log t)^{44}\). [Huxley, (1.9)](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0015/PPN356556735_0015.pdf#page=168) |

Choose fixed \(g<1\) so twice \(g\) exceeds the supremum of these three bounds, ignoring empty ranges. In the exceptional-frequency argument this gives \(g-A(\beta)/2>0\) with a fixed margin. On \([\sigma,9/10]\) the fixed-height exponents can be used uniformly as follows. Include \(4/5\) and \(9/10\) as boundaries and fix a mesh of width at most \(d\) in each relevant piece. At \(\beta\) use its lower mesh endpoint \(v\), so \(N(\beta,t)\le N(v,t)\). If \(A_*<2g\) is the common upper bound, then
\[
 A(v)(1-v)+\epsilon\le A_*(1-\beta)+A_*d+\epsilon.
\]
Since \(1-\beta\ge1/10\), choose fixed \(d,\epsilon>0\) with \(A_*d+\epsilon<(2g-A_*)/20\). This retains a fixed positive margin in the frequency integral after using \(t=T_1+H=P^{1/2+o(1)}\). There are finitely many mesh endpoints, so the largest of their implied constants suffices. For \(\beta\ge9/10\), Huxley's uniform logarithmic loss allows the original mesh of width \(1/L\) all the way to the shrinking zero-free boundary. The Gevrey estimates, prime-slot split and distinct-order count now give \(P^{\sigma+o(1)}\) exceptional primes as before.

For example \(\sigma=79/100\) and \(g=49/50\) leave a positive margin on all three ranges; the smallest before the fixed-mesh loss is \(49/50-225/232\). The choice \(d=1/10000\), \(\epsilon=1/100000\) meets the displayed mesh inequality. The [exact rational check](../experiments/zero-density-hasse.py) also verifies the strict threshold at \(25/32\) and the original factoring-cost margin.
