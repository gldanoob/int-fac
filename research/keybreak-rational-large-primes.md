# Rational large primes at the terminal descent

Allowing one or two extra rational primes per cofactor gives no leading smoothness gain at any fixed $L_N[1/3]$ prime cap. Primes large enough to change that conclusion cannot match across distinct primitive marks in the same terminal box. Broadening the rational cutoff while paying for all its parity columns also leaves the current terminal cost floor in place. The remaining case allows order $D$ extra factors and needs a bound on the rank of their actual incidence matrix. [Terminal eligibility](keybreak-late-rational-eligibility.md) · [Public pivots](keybreak-public-pivot-budget.md) · [Sparse-dependency schedule](keybreak-sparse-dependency.md)

## Standalone density under a bound on the extra factors

Write $L=\log N$, $D=(L/\log L)^{1/3}$, $H=D\log L$, and $V=DH$. Let $X=\exp((\sigma+o(1))V)$ be the rational cofactor scale and $B_R=\exp((r+o(1))H)$ the smooth cutoff. For positive fixed $r,\sigma$, the ordinary smoothness loss is
\[
 \frac{\Psi(X,B_R)}{X}
 =\exp\!\left(-\left(\frac{\sigma}{3r}+o(1)\right)H\right).
\]
Here $\log D\sim(\log L)/3$, and the smooth argument is $(\sigma/r+o(1))D$. All counts below hold with the same leading coefficient on $[X/2,X]$. Multiplying any admitted smaller integer by a power of two puts it in the dyadic interval without changing its large factors, with at most $1+\log_2 X$ preimages. [KeyBreak, Proposition G.13 and its uniform smoothness estimate](https://crypto.sjtu.edu.cn/factoring.pdf#page=124)

For a cap $P=\exp((t+o(1))H)$, $t>r$, allow at most $k=(\kappa+o(1))D$ prime factors in $(B_R,P]$, counted with multiplicity. Require all other factors to be $B_R$-smooth. The exact leading density is $\exp(-(s_R+o(1))H)$, where
\[
 s_R=\begin{cases}
   (\sigma-\kappa t)/(3r)+\kappa/3, & \kappa t\le\sigma,\\
   \sigma/(3t), & \kappa t\ge\sigma .
 \end{cases}
\]
This includes $k=o(D)$, in particular the one- and two-large-prime cases, with identical leading loss to the original cutoff.

For the upper count, use the weights $\alpha=1-\theta\log D/H$ and $z=D^{-\mu}$, where $0<\theta\le1/r$ and $\mu=(t\theta-1)_+$. Rankin's inequality bounds the count by
\[
 X^\alpha z^{-k}
 \prod_{p\le B_R}(1-p^{-\alpha})^{-1}
 \prod_{B_R<p\le P}(1-zp^{-\alpha})^{-1}.
\]
At exact endpoints with $o(H)$ perturbations in the cutoffs, first decrease $\theta$ and increase $\mu$ by arbitrarily small fixed amounts. Partial summation gives $\sum_{p\le \exp(uH)}p^{-\alpha}\ll\log H+D^{u\theta}$ for each fixed $u>0$. Thus each product has log $o(H)$ after the indicated slack. The density loss is at least $(\theta\sigma-\kappa\mu)/3$. Maximizing at $\theta=1/r$ or $\theta=1/t$, then taking the slack to zero, gives the two branches.

For the lower count take $m=(\lambda+o(1))D$ distinct primes in $[\exp((t-\epsilon)H),\exp(tH)]$, with $\lambda<\kappa$ and $\lambda t<\sigma$. An arbitrarily small reduction of the upper endpoint absorbs perturbations of the allowed cap. The harmonic sum in the strip is bounded below by a positive constant. Its ordered $m$-fold products with repeated primes discarded retain $1-o(1)$ of the unrestricted harmonic mass, by the bound on the largest single weight. Dividing by $m!$ costs $\exp(-(\lambda/3+o(1))H)$. Each choice has its own disjoint set of smooth complements. Their uniform Dickman lower bound uses residual log height at most $(\sigma-\lambda(t-\epsilon)+o(1))V$, still bounded away from zero on the $V$ scale. Let $\epsilon$ tend to zero and $\lambda$ tend to $\min(\kappa,\sigma/t)$. The case $\kappa=0$ follows from the ordinary smooth subset.

These leading coefficients are unchanged if the bound counts only odd valuations of primes above $B_R$, and arbitrary square factors above $P$ are allowed. Factor the integer as a $B_R$-smooth part, an odd-valuation squarefree part in $(B_R,P]$, and a square with primes above $B_R$. The square part contributes at most $\prod_p(1-p^{-2\alpha})^{-1}=O(1)$ to the upper bound. The preceding distinct-prime construction supplies the lower bound.

A different answer holds at a cap $P=\exp((\tau+o(1))V)$ with fixed $\tau>0$ and $k\ge1$. The loss is $(\sigma-k\tau)_+/(3r)$. For the upper bound take the ordinary Rankin parameter and bound the contribution from at most $k$ extra primes by $\sum_{j\le k}(\sum_{p\le P}p^{-\alpha})^j$. Even replacing primes by integers leaves at most $\exp((k\tau/(3r)+o(1))H)$. For the lower count use $k$ primes in a dyadic band just below the cap. Their harmonic mass loses only $\exp(o(H))$. When $k\tau\ge\sigma$, take the band at scale $(\sigma-\epsilon)V/k$ instead, leaving a small positive smooth height, and let $\epsilon$ tend to zero. The absence of any cap permits a prime numerator and has zero leading loss already for $k=1$.

## Which large primes can cancel

In a fixed public field and rational environment, write $G(a,b')=Qa-r_0b'$. If a prime $p\nmid Q$ divides both $G(a,b')$ and $G(a',b'')$, then $p\mid ab''-a'b'$. Distinct positive primitive marks in a box of coordinate size $U=\exp((v+o(1))H)$ have nonzero determinant of magnitude at most $2U^2$. A rational prime exceeding $2U^2$ therefore belongs to at most one primitive mark of this box. If that prime occurs at odd valuation and has no support outside the terminal box, its row forces even use of that physical atom in every recombination. Repeating the same atom does not create a second source of the prime. In the late geometry $p=Q$ cannot occur because the denominator lies below $Q$ and $r_0$ is a unit modulo $Q$.

More quantitatively, the positive slopes $a/b'$ lie in a fixed bounded interval in the KeyBreak box. Distinct slopes at which $p$ occurs differ by at least $p/U^2$, giving occupancy $O(1+U^2/p)$. If both marks answer the same internal parent $(\ell,s)$, the determinant also has factor $\ell$. For $p\ne\ell$ the bound becomes $O(1+U^2/(p\ell))$. The internal root exclusion already makes $p=\ell$ impossible on the rational side. These bounds use the geometry alone. They do not require independence of accepted samples. [KeyBreak, (G.5) and Lemma H.2](https://crypto.sjtu.edu.cn/factoring.pdf#page=127)

Consequently a terminal-only recombination can use odd rational prime labels above the base only up to first-scale exponent $2v$. This excludes the radix-scale fixed-$k$ gain. By the standalone density formula, a fixed material gain with any fixed first-scale cap demands $\Omega(D)$ additional odd factors per cofactor, even if cancellation is free. At the geometry limit, even perfect cancellation cannot lower the standalone rational loss below $\sigma/(6v)$.

## Exact rank and paying for extra columns

For $m$ partial columns let $E$ have their large-prime parity vectors as columns. Before imposing any small-prime or character equations the recombined dimension is exactly $m-\operatorname{rank}E$. With one extra prime per partial column, the rank is the number of occupied prime labels. With at most two, the columns are graph edges, using one extra dummy vertex for singletons. The rank is the number of vertices minus the number of components. Deleting the dummy row preserves that rank. For larger supports the exact linear rank still applies. To guarantee a dependency by dimension after imposing $C$ remaining rows one needs $m-\operatorname{rank}E>C$.

For example a per-history upper bound $\mu$ on the probability of any particular accepted singleton label would give expected recombined dimension at most $\binom m2\mu$ among $m$ singleton columns. Each repeated label requires a matched pair, and conditioning on the earlier transcript proves the estimate without independent labels. The geometric occupancy bound controls raw point counts. It does not establish this cap for points selected after algebraic smoothness, rational smoothness and good-child screening.

An asymmetry in the cutoffs alone does not improve the current paid-column ledger. Keep the same terminal geometry and field height, let $b_A$ be the algebraic cutoff exponent, let $r$ be the usable rational cutoff exponent and let $c\ge\max(b_A,r)$ be the exponent charged for the final retained population. Write $\delta=d/D$ and $K_A=(1+\alpha/\kappa_0)/\delta$ for the height contribution other than the algebraic mark. Here $\kappa_0$ is the existing box schedule parameter. The necessary terminal conditions of this ledger are
\[
 S\ge\frac{K_A+\delta v}{3b_A}+\frac{1}{3\delta r},
 \qquad 2v\ge b_A+S,\qquad C_{\rm work}\ge c+S .
\]
For $3b_A>\delta/2$, elimination gives
\[
 S\ge\frac{K_A+b_A(\delta/2+1/(\delta r))}{3b_A-\delta/2}.
\]
Replacing $r$ by $c$ decreases this lower bound. The resulting function strictly decreases with $b_A$, so replacing $b_A$ by $c$ decreases it again. The result is the symmetric necessary terminal inequality at $c$. The private population still pays $c$ in this ledger. A different rank theorem allowing rational cap above the charged column exponent, or a different geometry or population law, could change the comparison. [Existing terminal floor](keybreak-sparse-dependency.md#exact-limiting-coefficient)

## An analytic input for a larger incidence calculation

KeyBreak's GRH smooth-character estimate can be extended to the capped numerator set when $\kappa t<\sigma$. For a nonprincipal character modulo $Q_0=\exp(O(H))$, expand over the large part $d\le P^k$ and apply (G.7) to the remaining smooth sum. Bounding the large-part sum by all integers gives error
\[
 O_\epsilon\!\left(X^{1/2+\epsilon}P^{k(1/2-\epsilon)} Q_0^\epsilon\right),
\]
which saves a fixed power of $X$ for sufficiently small fixed $\epsilon>0$. This gives a short-progression error at the first-scale moduli by the same character orthogonality, with principal term remaining the admitted coprime count. In the numerator–prime-denominator convolution of (G.16), permitting some denominator primes in the numerator no longer gives uniqueness. The multiplicity is still at most the number of distinct prime factors of the product, which is polynomial in $\log N$. Neither observation controls the conditional incidence rank among retained partial columns. The one-field schedule still lacks a weighted abundance and matching estimate for those columns. [KeyBreak, Lemmas G.2–G.3](https://crypto.sjtu.edu.cn/factoring.pdf#page=106)
