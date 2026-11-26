# Gaussian width for skewed top boxes

In the KeyBreak single-input schedule, a common Gaussian coefficient law is used for the large top boxes and the late descent. The existing uniform shifted-fiber argument forces a large coefficient width even when the covariance is arbitrary. A separate entropy bound gives the same leading obstruction for pointwise Gaussian comparison on the actual two-value image, provided the smallest covariance eigenvalue has logarithm $-o(d\log M)$ or larger. With the ordinary late boxes and the same height-based smoothness ledger, neither change lowers the terminal constraint. [KeyBreak, (G.4) and Lemmas G.4–G.6](https://crypto.sjtu.edu.cn/factoring.pdf#page=109) · [Single-input cost model](keybreak-private-elliptic-schedule.md#limits-of-retuning-the-preceding-schedule)

## The coefficient law

Write the random part of the binary form as $2G R$, where $G=QX-rY$, $R$ has degree $d-1$, and its coefficient vector $c\in\mathbb Z^d$ has mass proportional to $\exp(-\pi c^{\mathsf T}S^{-1}c)$ for an arbitrary positive definite $S$. Let $E$ evaluate $R$ at distinct primitive points $P_i=(a_i,b_i)$ with $b_i>0$ and $\Delta=|a_1b_2-a_2b_1|>0$. The factors $2G(P_i)$ and the fixed centers do not affect the coefficient kernel. Gauss's lemma identifies its full integral lattice $L$ with the coefficient vectors of

\[
 (b_1X-a_1Y)(b_2X-a_2Y)U(X,Y),\qquad U\in\mathbb Z[X,Y]_{d-3}.
\]

The coefficient of $X^{d-1}$ on $L$ runs through $b_1b_2\mathbb Z$. If $a_1a_2\ne0$, that of $Y^{d-1}$ runs through $a_1a_2\mathbb Z$.

For $K=L\otimes\mathbb R$, the shifted-fiber mass is $\sum_{x\in L+h}\exp(-\pi x^{\mathsf T}S^{-1}x)$, $h\in K$. Relative to its torus mean, its Fourier coefficient at a dual functional $u$ is $\exp(-\pi\|u\|_*^2)$ where

\[
 \|u\|_*^2=\sup_{x\in K\setminus\{0\}}\frac{|u(x)|^2}{x^{\mathsf T}S^{-1}x}.
\]

If every shift gives relative error at most $\varepsilon<1$, each nonzero Fourier coefficient is at most $\varepsilon$. For the leading coefficient functional divided by $b_1b_2$, the supremum is at most $S_{d-1,d-1}/(b_1b_2)^2$, by taking the supremum on the full coefficient space instead. Thus the square root of the leading diagonal entry is at least $b_1b_2\sqrt{\log(1/\varepsilon)/\pi}$. The constant coefficient has the corresponding bound with $|a_1a_2|$. This is a necessary bound for the all-shift Poisson argument of G.4. It uses the coefficient lattice itself and is independent of the size of the nonzero determinant $\Delta$.

### Pointwise comparison on the actual image

The evaluation lattice $\Gamma=E\mathbb Z^d$ has covolume $\Delta$ by G.5. Suppose the actual law of $Ec$ is pointwise bounded above by $(1+\varepsilon)$ times the normalized centered Gaussian of parameter matrix $ESE^{\mathsf T}$ on $\Gamma$. Its entropy is at least the negative logarithm of its largest point mass. Poisson summation at shift zero bounds the reference normalizer below by $\sqrt{\det(ESE^{\mathsf T})}/\Delta$. Writing $\nu$ for the smallest eigenvalue of $S$, the two adjacent monomials at either end give a $2\times 2$ minor of $E$ with determinant of magnitude $\Delta(b_1b_2)^{d-2}$ or $\Delta|a_1a_2|^{d-2}$. Thus

\[
 \operatorname{Ent}(Ec)\ge (d-2)\log J+\log\nu-\log(1+\varepsilon),\qquad
 J=\max\{b_1b_2,|a_1a_2|\}.
\]

The centered lattice Gaussian satisfies $\mathbb E e^{tc_j}\le \exp(t^2 S_{jj}/(4\pi))$. Completing the square gives the stated continuous factor times a shifted lattice-mass ratio at most one by positivity of the Poisson coefficients. In particular $\operatorname{Var}(c_j)\le S_{jj}/(2\pi)$, and $\operatorname{Ent}(c)\le\sum_j\log(1+\sqrt{S_{jj}})+O(d)$. The coordinate entropy bound follows by adding independent uniform noise of length one and bounding the resulting differential entropy by that of a Gaussian of the same variance. Since $Ec$ is a function of $c$, the right side also bounds its entropy. These statements only use the actual integral support. In fact, for one fixed pair an integral complement of $L$ in $\mathbb Z^d$ gives exact pointwise Gaussian comparison when the coefficient law is a product along that complement and $L$, with arbitrarily narrow directions along $L$. This follows because the evaluation on the complement is bijective onto $\Gamma$. The complement construction is specific to that pair.

## Width at the bottom and the cost coefficient

In an ordinary late box, let $W$ bound the Gaussian parameter of $R(s,1)$ over the relevant slope interval, which contains a fixed positive-length interval of slopes in a compact subset of $(0,1)$. The parameter is the Euclidean norm of $S^{1/2}(s^j)_{j=0}^{d-1}$. At $d$ points in this interval separated by $\gg1/d$, Lagrange interpolation expresses each coefficient as a linear combination of the values whose absolute weights sum to at most $(Cd)^d$. This follows by bounding the coefficient absolute sum of each numerator by $C^d$ and its denominator below by $(c/d)^{d-1}$. Consequently every $\sqrt{S_{jj}}$ is at most $(Cd)^d W$. Applying either the all-shift bound or the entropy bound gives

\[
 \log W\ge \log J-o(\log M),
\]

where the entropy version assumes $\log\nu\ge-o(d\log M)$ and bounded relative error. Here $d\log d=o(\log M)$, and $\log J=O(\log M)$. A fixed positive saving in $\log W/\log M$ under the entropy comparison would require an eigenvalue $\exp(-\Omega(d\log M))$ or smaller.

One can also see the all-shift obstruction on most eligible points in a rational-good late box. Contract the vector polynomial $S^{1/2}(s^j)_j$ against the unit vector in the direction of the coefficient with large diagonal entry. If that coefficient is leading, the resulting scalar polynomial has leading coefficient $\sqrt{S_{d-1,d-1}}$. Outside intervals of width $2/d^2$ around the real parts of its roots, its absolute value is at least $\sqrt{S_{d-1,d-1}}d^{-2(d-1)}$. For the constant coefficient apply the argument to the reversed polynomial and use that $s$ is bounded away from zero. The cell upper bound from G.3 charges each slope interval of width $O(d^{-2})$ a fraction $O(d^{-2}+K_{
m mesh}^{-1})$ of a rational-good population. Such a slope strip meets $O(K_{
m mesh}+K_{
m mesh}^2d^{-2})$ cells in the two rational coordinates, since the slope is $r/Q-w/(Qb)$. The excluded fraction is $o(1)$ since $K_{
m mesh}\gg d$. A uniform height bound on the ordinary eligible population therefore cannot use a cancellation confined to a small number of slopes. [KeyBreak, Lemma G.3](https://crypto.sjtu.edu.cn/factoring.pdf#page=107)

An axis-aligned top rectangle with coordinate scales $U,V$ has expected $O(UV/p)$ raw points for a top parent $p$ at the current scales. For each fixed point with denominator prime smaller than $p$, the parent congruence gives one residue class for $r\bmod p$. The public interval for $r$ has length $\asymp M\gg p$. If the large numerators and denominators are of respective sizes $U,V$ at the pairs being compared, $J\asymp\max(U,V)^2$. A tilted strip can instead take $b\asymp V$ and $w=rb-Qa\asymp MU$, with $U\le V$ and $V\le M^{1-\eta}$ for some fixed $\eta>0$. Conditional on $Q$, each denominator and each of the $O(MU/p+1)$ possible $w$ divisible by $p$ determine at most one $r$ via $rb\equiv w\bmod Q$. Its expected raw population is $O(UV/p+V/M)$, while $J\gg V^2$. In both cases the mean can vanish by a fixed power of $M$ if $UV$ is below $p$ by such a power. The source needs positive typical supply before imposing either smoothness predicate. Both shapes thus require $\log W\ge\log p-o(\log M)$ with the stated fiber comparisons. [KeyBreak, (G.5)–(G.6)](https://crypto.sjtu.edu.cn/factoring.pdf#page=105)

To translate this to the existing ledger, write $d\sim\delta D$, $H=D\log\log N$, $\log M\sim DH/\delta$, and $\log B\sim bH$. Put $\ell=\log W/\log M$. In the largest top band, $\log p/\log M\to1/(2\kappa)$, so $\ell\ge1/(2\kappa)-o(1)$. In a late box with coordinate size $e^{vH}$, the original height-based estimate budgets combined rational and algebraic smoothness loss at least

\[
 s=\frac{(2+\ell)/\delta+\delta v}{3b}.
\]

The rational modulus contributes $1/\delta$ on the $DH$ scale. The algebraic value contributes $(1+\ell)/\delta$ from $G$ and the coefficient width, plus $\delta v$ from the degree. The terminal mean comparison uses $2v-b\ge s$ even if its positive mean slack is dropped. Eliminating $v$ gives the leading lower ledger

\[
 C\ge b+s\ge \frac{6b^2+(4+2\ell)/\delta}{6b-\delta}
 \ge \frac{6b^2+4/\delta+1/(\kappa\delta)}{6b-\delta}.
\]

Feasibility already requires $6b>\delta$. At fixed top volume a tilted strip with $\log V/\log M$ increased by $\xi$ and $\log U/\log M$ reduced by $\xi$ saves $\xi/(3\delta b)$ in the top rational loss for that band. It increases the terminal lower ledger by at least $4\xi/[\delta(6b-\delta)]$ relative to the minimal balanced width. This comparison uses a single coefficient law throughout and the original terminal height and mean estimates. A different pairwise comparison that avoids uniform shifted fibers and permits much narrower directions, or an analysis that changes the late relation population, would need its own density and incidence bounds.
