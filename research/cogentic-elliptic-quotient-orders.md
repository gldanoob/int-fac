# Quotient-order collisions on the separating elliptic quartic

For a fixed seed on the four-mark quartic, a comparison of unit values at distinct multiples is an order test on a two-isogenous curve. With $B$ points on each side and a product tree, the public search covers quotient orders through $B^2$. A common annihilator gives a split if exact quotient orders or torsion labels differ at two primes. The existing residual odd-order stage also gives this guarantee after refining a common annihilator. [Separating units](cogentic-separating-power-order-units.md) · [Bounded elliptic orders](cogentic-elliptic-residual-order.md)

## The map behind equal ratios

Write $A(t)=(t-1)(t-2)$, $C(t)=(t-13)(t-14)$, and use $\delta y^2=A(t)C(t)$ with origin at the branch point $t=1$. The other zero of $A$ is the rational two-torsion point $T=(2,0)$. Put $\lambda=-156\delta$ and use Weierstrass coordinates
$$
 X=\frac{\lambda}{t-1},\qquad Y=\frac{\delta\lambda y}{(t-1)^2}.
$$
The roots are $e=\lambda,e_2=\lambda/12,e_3=\lambda/13$. With $u=X-e$, put $a=2e-e_2-e_3$, $b=(e-e_2)(e-e_3)$. The equation is $Y^2=u(u^2+au+b)$, with $T=(0,0)$. The degree-two map with kernel $\{O,T\}$ is
$$
 \phi(u,Y)=\left(u+a+\frac{b}{u},\ Y\left(1-\frac{b}{u^2}\right)\right)
$$
to $Y'^2=X'(X'^2-2aX'+a^2-4b)$. Its abscissa is $(Y/u)^2=\delta C(t)/A(t)$.

Translation by $T$ sends $u$ to $b/u$ and $Y$ to $-bY/u^2$. On the quartic parameter this gives the involution $g(t)=(15t-41)/(2t-15)$. Equality of ratios can also be seen by cross multiplication:
$$
 A(t)C(z)-A(z)C(t)=-12(t-z)\bigl(2tz-15(t+z)+41\bigr).
$$
Over a good odd reduction, equality of the projective quotients means $Q=\pm R+\eta T$ for some $\eta\in\{0,1\}$. Compare abscissas on the quotient curve and lift through the kernel. This includes poles and branch points where the affine ratio is ineligible as a modular unit.

## A public search at distinct multiples

For a fixed seed $P$ and a good prime $p$, set
$$
 d_p=\operatorname{ord}(\phi(P)\bmod p),\qquad [d_p]P=\epsilon_p T\pmod p.
$$
The relation $[k]P=\eta T$ holds locally exactly when $d_p\mid k$ and $\eta\equiv\epsilon_p k/d_p\bmod2$. The labelled comparisons at indices $n,m$ test this condition at $k=n-m,n+m$.

Suppose the odd input $N$ has good reduction at every prime factor and the seed and its image can be computed by guarded modular arithmetic. If $d_p\le B^2$ at some prime factor and two primes have different profiles $(d_p,\epsilon_p)$, there is a deterministic split in $\widetilde O(B)$ work up to factors polynomial in $\log N$.

Compute the baby indices $0,\ldots,B-1$ and giant indices $B,2B,\ldots,B^2$ on the quotient. They cover a local cancellation since $d_p=jB-i$ for some pair. Infinity at only some primes or a proper gcd of abscissa differences gives a factor. The existing monic product-tree search finds a gcd or a global annihilator $g\le B^2+B-1$. For a full abscissa match it checks both ordinate signs.

Sieve the primes through $\sqrt g$, include any remaining prime factor of $g$, and test $[g/\ell]\phi(P)$ for each factor $\ell$, repeating a successful global division. Checked modular addition gives a proper gcd if the tested point is the identity at some primes and finite at others. Otherwise the final order $d$ is exact at every prime. Compute $[d]P$ on the source. Different labels $O,T$ also give a mixed identity. The sieve, binary scalar multiplications and product tree all use modular data. The rational coordinates of the large multiples are unnecessary.

When the profiles agree at every prime, every labelled relation agrees for every pair of indices. For example, the seed $t=3$, $\delta=220$, has profile $(78,0)$ at both 4391 and 1879. The two quadratic characters of $\delta$ are opposite, and both primes have $v_2(p-1)=1$. Thus even a seed satisfying the separating-unit character condition can miss every comparison of this type.

## Comparison with the existing odd-order stage

The quotient order equals the full seed order unless the seed subgroup contains $T$, in which case it is half the full order. Both orders have the same odd part. If two quotient profiles differ, then the source points differ in odd order, two-primary height, or final nonidentity torsion point. The existing search on the source after a large power of two therefore covers at least the same order range. Refine a common annihilator by prime-factor tests on that odd-order point. Different odd orders split during refinement. Different two-primary data split during the existing continuation, which can also distinguish two different final torsion points when neither is $T$.

For the seed $t=3$, at primes 263 and 269 the full orders are both 34. The quotient profiles are $(34,0)$ and $(17,1)$. With $B=5$, the ordinary search before removing the two-part misses, while quotient abscissas give 269. The existing odd-order search finds the common annihilator 17 and the continuation returns 269 by comparing the final torsion points.

The same seed at primes 1861 and 1693 has odd orders 21 and 105, both with two-primary height one and final torsion point at the mark 13. With bound 225 the product-tree routine returns the global multiple 105, and the torsion continuation alone misses. Refinement tests its proper divisors and returns 1861. The stage-two replay checks both outcomes. [Modular implementation and replay](../experiments/cogentic-moving-elliptic-separation.py)
