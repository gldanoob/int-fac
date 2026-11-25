# Trading deterministic time for smaller space in the two-field extractor

Put $L=\log N$, $z=\log L$. Fix $0<\theta<1/3$ and define
$$
 h=L^\theta z^{1-\theta},\qquad s=L^{1-\theta}z^\theta,
 \qquad j=sz/h=L^{1-2\theta}z^{2\theta},\qquad \kappa=1-2\theta .
$$
For each fixed space coefficient $\beta>0$, the two-field method gives the following manuscript-level bounds for full deterministic factorization:
$$
 \log S\le (\beta+o(1))h,\qquad
 \log T\le \left(\frac{4(1-2\theta)}{\beta}+o(1)\right)s.
$$
The statement is in the usual infimum sense for real coefficients, with a single limiting algorithm for efficiently computable parameters as in the [workspace proof](cogentic-extractor-space.md). The fixed positive exponent on the space bound can be arbitrarily small. The analytic input is the individually uniform squarefree progression estimate based on proved ordinary and Dirichlet RH. The endpoint $\theta=1/3$ has a separate coefficient because $h$ then equals $j$. [Two-thirds schedule](cogentic-deterministic-two-thirds.md) · [Window estimate](cogentic-dirichlet-smooth-windows.md) · [Cogentic, Lemmas 9.4–9.5 and Proposition 10.1](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=47)

## A two-point upper bound that permits large determinants

Use two distinct integer marks $a,a'$ in one field from the source, $\Delta=|a-a'|$. There are at most two prescribed ordinary rows and one special target prime $\ell$. Write $P$ for the product of their distinct primes. Thus $P\le B^3$. Condition on their root rows and the central cutoff on the first affine scalar. The event at the first mark requires the reduced norm $n_1=|f(a)|/Q_{\rm pre}(a)$ to be squarefree and supported on the prime band $(\sqrt B,B]$ after the source deletions. Write $D_0$ for the product of eligible primes dividing $\Delta$ and coprime to $P$. Its logarithm is at most $\log A$. If the corresponding event at the second mark is possible, the forced common divisor $G$ of its reduced norm with its conditional progression modulus is squarefree. Every prime of $G$ lies in $P$ or divides $D_0$ and $n_1$. Indeed primes dividing $P_0|a'-m|$ cannot force a zero by the original coprimality sieve. All other primes outside $P$ in that modulus divide $\Delta$, and $f(a')\equiv f(a)\pmod p$. Consequently $G\mid P\gcd(D_0,n_1)$. This also covers repeated prime powers in $\Delta$, since successful reduced norms are squarefree.

Suppose the hypotheses of the [smooth-window formula (2)](cogentic-dirichlet-smooth-windows.md) hold, with an exponential-in-$s$ margin in the two absolute errors, even after imposing moduli of size $A B^{O(1)}$ or dividing centers by this quantity. The parameter verification below gives that margin. All the resulting centers have logarithm $(v+1/x+o(1))s$, so their saddles satisfy $1-\alpha_Y\le\xi=Cz/h$ with a fixed $C$. Write $I(Y)$ for the principal saddle density, allowing the given deleted primes. Uniformly for $1\le t\le A B^{O(1)}$,
$$
 I(Y/t)\ll I(Y)t^\xi.
$$
Indeed the logarithmic derivative of $\log(Y^{\alpha_Y-1}F(\alpha_Y))$ with respect to $\log Y$ equals $\alpha_Y-1$ by the saddle equation. The two square-root saddle prefactors are comparable since the logarithms of the centers have ratio $1+o(1)$. Deleting any additional $L^{O(1)}$ primes of size at least $\sqrt B$ changes the saddle envelope and width by a relative $o(1)$, from the Euler factors or the saddle variance. The progression normalizers $q/\phi(q)$ are bounded by a polynomial in $L$. All geometric, normalization and prescribed-prime factors in $Z_i^{(0)}\Phi_i$ are retained as in the source. In particular $P^\xi\le L^{O(1)}$.

For a divisor $g\mid D_0$, the unconditional one-point bound for the first smooth event with $g\mid n_1$ is at most $L^{O(1)}Z_1 g^{-1+\xi}$, where $Z_1=Z_i^{(0)}(a)\Phi_i(a;R_i)$. If $g$ meets the reduced one-point modulus this event is impossible because its class is coprime. Otherwise substitute $n_1=g n$. The normalized progression has its original modulus, width divided by $g$, and an additional overall factor $1/g$. The saddle ratio proves the bound. The relative error is uniform because $\log g=O(j)=o(s)$ and both absolute contour errors have $\exp(-\Omega(s))$ slack. The same argument applies after imposing one further congruence at a prime $p\mid P$ not already fixed: for a unit residue the extra factor is $O(L^{O(1)}/p)$, and for a zero residue it is $O(L^{O(1)}p^{-1+\xi})$ on dividing out $p$. Here $g$ is coprime to $P$. These factors come from the one-point normalization before the further congruence is imposed.

At the second mark, divide its class and width by the forced common divisor $G$. The normalizing prefactor is exactly $(q/G)/(S_2/G)$, so the conditional probability is at most $L^{O(1)} Z_2 G^\xi$, with $Z_2=Z_i^{(0)}(a')\Phi_i(a';R_i)$. Sum this against the first event, using $\gcd(D_0,n_1)^\xi\le\sum_{g\mid D_0,\ g\mid n_1}g^\xi$. This yields
$$
 \Pr(E_i(a)\cap E_i(a')\mid E_{R_i})
 \ll L^{O(1)}Z_1 Z_2
 \prod_{p\mid D_0}(1+p^{-1+2\xi})
 \ll L^{O(1)}Z_1 Z_2 .
$$
There are only $L^{O(1)}$ factors and every one has $p>\sqrt B$. The omitted Gaussian tails are $\exp(-\Omega(L^6))$ and may be discarded before the divisor sum. This averaging is important when $\log\Delta\gg\log B$: simply maximizing $G^\xi$ can cost more than the band-prime saving.

For the clean two-point formula the error from a shared eligible divisor of $\Delta$ has the same bound with an extra $O(L^{O(1)} B^{-1/2+o(1)})$. To see this, write $d_1=\gcd(D_0,n_1)$. On $d_1>1$,
$d_1^\xi\le\sum_{g\mid d_1,\, g>1}g^\xi$; the product in the last display is replaced by that product minus one. The bad residue at a prescribed or special prime is treated by the one-additional-congruence estimate above, with exponent $-1+\xi$ in place of $-1$. For the special prime hit at both marks the source's forbidden class removes the second event and costs only its first-mark mass. These are exactly the four local cases of its Lemma 9.5. On the remaining first scalars, its coprime conditional calculation applies with relative error $O(e^{-50z^2})$. The product over the small primes dividing $\Delta$ is the source's $\gamma(a,a')$, and large primes dividing $\Delta$ outside the band contribute at most $1+O(L^{O(1)}B^{-1/2})$. The two fields are independent after their respective prescriptions.

## Parameter transfer

Choose positive $x,v,c$ with
$$
 v>1/x,\qquad v>xc,\qquad c>2\kappa(v+1/x)/\beta .
$$
Take $d\sim xh/z$, $\log B\sim\beta h$, $\log U\sim vs$, $\log A\sim cj$, $\log K_1\sim h$, and $\log(1/w)\sim d\sqrt z$. Since $h=o(j)$ and $j=o(s)$, the base $m=\lceil N^{1/d}\rceil$ has $\log m=(1/x+o(1))s$, while $d\log A=(xc+o(1))s<\log U$. Source rounding and the definition of the leading coefficient give $\log X_{\rm sc}=(v+1/x+o(1))s=o(L)$. The real-root products on each interval have logarithmic loss $O(\log(1/w)+d)=o(h)$ by factorial spacing; all nominal means differ from $X_{\rm sc}$ by $O(\log B)$ on the logarithmic scale. For all marks, including nearest neighbors, $\log R=O(j)$, $\log R\gg h$, and conditional mean displacements are exponentially small in $h$ on the source cutoff. The high-frequency and nonprincipal absolute errors in (2) are $\exp(-\Omega(s))$ since $\log q\le(1/x+o(1))s$ and $v>1/x$. This remains true after imposing or dividing by $A B^{O(1)}$, because $j=o(s)$. The saddle has $u\sim (v+1/x)s/(\beta h)$ and $\lambda\sim\kappa z$, hence
$$
 \log(1/I(Y))=(\kappa(v+1/x)/\beta+o(1))j .
$$
Thus the absolute errors above are negligible relative to every required mass and congruence. The saddle expansion and two-prime covariance use $|\log(\mu_i/X_{\rm sc})|=O(\log B)$ as before.

There are $O(s/\log d)$ prime divisors of $k_0 k'_0$, all larger than $d$. Mertens' theorem bounds their reciprocal sum by $\log((1-\theta)/\theta)+O(1)$, by taking the smallest possible such primes. The density of survivors in the grid is therefore bounded below by a positive constant depending only on $\theta$. The Brun inclusion–exclusion error in the earlier argument is unchanged: $Aw/B^4=\exp((c+o(1))j)$ absorbs $\exp(O(z^3))$, and all prime counts are polynomial in $L$. This gives $\gg_\theta Aw$ survivors in each interval. The squared-ordinary-prime and close-mark losses are $L^{O(1)}(B^{-1/2}+B^3/(Aw)+w^{-1}K_1^{-1/2})$, using the averaged rough bound. The shortest-prefix tail and main centered divisors use the same progression sieve up to $B^4$. The diagonal cost in Proposition 10.1 is
$$
 L^{O(1)}\frac{B^2}{Aw}\exp\big((2\kappa(v+1/x)/\beta+o(1))j\big).
$$
It is $\exp(-\Omega(j))$ by the third strict inequality. All these errors are $o(e^{-7z^2})$. The polynomial losses in the archimedean covariance and its peeling are absorbed by the same thresholds as in the two-thirds proof. The interval log-root matrix has off-diagonal row and column sums $O(d)$ and diagonal magnitude $\log(1/w)\gg d$. This proves the required success probability at each target.

The [one-intercept construction](cogentic-one-intercept.md) can now enumerate its complete support. The numbers of coordinates in each expanded moment sum, the sup norm of each weight, the reciprocal smooth density and the moment normalizers are at most $\exp(O(j))$. Use bias $\exp(-C'j)$ for a sufficiently large fixed $C'$. The auxiliary supports and mark processing then cost $\exp(O(j))$, and the principal cyclic intercept has $\log$-size $\log U+O(j)$. The [streamed implementation](cogentic-extractor-space.md) uses $B\,\mathrm{poly}(L)$ bits while its per-candidate time is $\mathrm{poly}(A,B,L)$. Its prime and mark counters have polynomial bit length in $L$. Directly checking a candidate divisor and then recursing uses only polynomial additional space. With primality recognition, perfect-power checks and fallback for finitely many small sizes, this proves $\log T\le(v+o(1))s$ and $\log S\le(\beta+o(1))h$.

Finally choose $x$ just above $1/v$. A $c$ exists precisely when $v>2\kappa(xv+1)/\beta$ for such an $x$, which is possible for every $v>4\kappa/\beta$. Strict rational schedules approaching this boundary can be interleaved under the common workspace cap described in the workspace proof. This analysis keeps $\theta$ fixed, so it supplies no polynomial-space guarantee by setting $\theta=0$.

## Quasipolynomial space

There is also an endpoint family for fixed $k>2$:
$$
 \log S\le (\beta+o(1))z^k,\qquad
 \log T\le (4/\beta+o(1))L/z^{k-1}.
$$
Set $h=z^k$, $s=Lz/h$, $j=sz/h$, $d\sim xh/z$, and now $\kappa=1$. The relations $h=o(j)$ and $j=o(s)$ still hold, as do $u\sim(v+1/x)s/(\beta h)$ and $\lambda\sim z$. In this regime $\log B$ and the smallest $\log R$ are powers of $z$, below the polynomial-in-$L$ lower hypotheses stated in the window lemma. The following checks give the needed extension of its proof.

1. In the individual character bound choose $\delta=D_0 z/\log B=o(1)$. The explicit-formula proof gives $x^{-\delta/2}\le L^{-D_0/4}$ for the least endpoint $x=\sqrt B$. Every logarithm of a conductor, frequency, upper cutoff, or center is $L^{O(1)}$, and $1/\delta\le L^{O(1)}$. These are the only scale checks in the Perron shift; endpoint errors, deleted primes and the Euler logarithm's quadratic tail are all $O(L^{-10})$ with $D_0$ enlarged.
2. In the saddle estimate, the prime band of relative logarithmic thickness $1/\lambda$ at the top has ordinary prime-theorem errors negligible by RH, since $\log B/\lambda\asymp z^{k-1}\to\infty$ and $\sqrt B$ dominates every polynomial in $L$. The cumulant of order $j_0\le 6$ is $O(u(\log B)^{j_0})$, the variance is $\asymp u(\log B)^2$, and $u=L^{1-o(1)}$. The original small-frequency expansion and $e^{-c u/\lambda^2}$ decay up to $|t|=1$ therefore retain their errors. On the bent portion the quotient $e^\lambda/(u\log B)=O(\lambda/\log B)=o(1)$, giving the same $t^{-u}$ gain. On the far portion $T=B^4R^2$ has $\log T=O(j)$; it is absorbed in the strict square-root margin of size $\Omega(s)$. The Mellin and Gaussian tails remain negligible, since even the least $R$ grows as $\exp(\Omega(z^k))$ and dominates any fixed power of $L$. The retained relative error $O(R^{-2}+e^{-cu/\lambda^2})$ is $o(e^{-50z^2})$.
3. The reciprocal sum over the primes in $k_0 k'_0$ can now grow as $O(\log z)$, bounded by taking the first $O(s/\log d)$ primes beyond $d$. The product of surviving fractions is at least $z^{-O(1)}$. The same Brun truncation at $2\lceil z^2\rceil$ has tail $(O(\log z)/z^2)^{2z^2}$; its absolute error remains $o(e^{-4z^2})$ even after division by the survivor fraction. Every use of the grid interval count or reciprocal local density incurs at most another polynomial factor in $L$. Root brackets and angular separation have the same estimates since $d\to\infty$, $d\sqrt z=o(h)$ and $d\sqrt z\gg d$. The remaining losses $B^{-1/2+o(1)}$, $K_1^{-1/2}/w$ and $e^{-\Omega(j)}$ all beat $e^{-50z^2}$ for $k>2$.

The same moment, support and workspace argument now applies with $\kappa=1$. No limit uniform in $k$ is needed.

The [finite replay](../experiments/cogentic-averaged-gcd.py) checked the forced-divisor containment on 2,283 local systems, both full and exceptional divisor averages in 64 exact toy distributions, and 72 strict rational schedules. These test the new arithmetic steps independently of the asymptotic proof.
