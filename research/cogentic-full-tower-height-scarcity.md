# Small-height quadratic towers cover few digit inputs

Let $X\le N<2X$, $L=\log X$, $D=(L/\log L)^{1/3}$ and $V=D^2\log L$. Consider a primitive irreducible $P\in\mathbb Z[T]$ of degree $d=O(D)$ whose field admits a complete tower of quadratic extensions from $\mathbb Q$. The polynomial can be nonmonic and need have no composition structure. Allow an input-dependent reduced rational radix $m=u/v$, with $0<v$ and $|u|,v\le \exp(O(V))$. If $P$ has coefficient height $\exp(O(V))$, at most $X^{o(1)}$ integers in the dyad divide a nonzero value $v^dP(u/v)$ from this model. In particular, the model cannot supply small-height fields for all inputs, even when the evaluated multiples and the towers vary. [Earlier obstructions for compositions](cogentic-quadratic-tower-construction-limits.md) · [Square kernels for supplied towers](cogentic-quadratic-tower-square-kernel.md)

## Denominators and height at one quadratic step

Write $M(P)$ for the Mahler measure, and normalize the leading coefficient $l$ to be positive. Let $\alpha$ be a root of $P$. The penultimate field $E\subset\mathbb Q(\alpha)$ has degree $e=d/2$, and the monic relative minimal polynomial of $\alpha$ is $G=T^2+aT+b$ over $E$. Its conjugate factors satisfy
$$
 \prod_{\sigma:E\hookrightarrow\mathbb C}\sigma G=P/l,\qquad
 \prod_\sigma M(\sigma G)=M(P)/l.
$$
The two coefficients $a,b$ generate $E$. Otherwise the field $F=\mathbb Q(a,b)$ has degree less than $e$, while $[\mathbb Q(\alpha):\mathbb Q]\le [F(\alpha):\mathbb Q]\le2[F:\mathbb Q]<d$.

Define the integral denominator ideal $\mathfrak d$ by $\mathfrak d^{-1}=\mathcal O_E+\mathcal O_Ea+\mathcal O_Eb$. Then $\operatorname{Nm}\mathfrak d=l$. To see this, fix a rational prime $p$ and apply multiplicativity of the nonarchimedean Gauss norm to the product of the relative factors over $\overline{\mathbb Q}_p$. Primitivity gives the minimum coefficient valuation of $P/l$ as $-v_p(l)$. For each prime $\mathfrak p\mid p$, its $e_{\mathfrak p}f_{\mathfrak p}$ embeddings contribute the common minimum of $0,v_{\mathfrak p}(a),v_{\mathfrak p}(b)$ divided by $e_{\mathfrak p}$ at each embedding. This yields $v_p(l)=\sum_{\mathfrak p\mid p}f_{\mathfrak p}v_{\mathfrak p}(\mathfrak d)$. In the same way, if $\beta$ generates $E$, the leading coefficient of its primitive integer minimal polynomial is the norm of the denominator ideal of $\beta$.

Choose $t\in[0,\binom e2]\cap\mathbb Z$ so that $\beta=a+tb$ generates $E$. Each pair of distinct embeddings can forbid at most one $t$ because $a,b$ jointly generate. The denominator ideal of $\beta$ divides $\mathfrak d$. Both relative coefficients at $\sigma$ have magnitude at most $2M(\sigma G)$ by the coefficient bound for a monic quadratic. The primitive minimal polynomial $Q$ of $\beta$ therefore satisfies
$$
 M(Q)\le l\prod_\sigma\max(1,|\sigma\beta|)
      \le \exp(O(e\log(2+e)))\,M(P).
$$
This gives a smaller tower field and preserves the Mahler budget up to the displayed factor. The leading coefficient at the smaller field is accounted for by the denominator ideal, including when $P$ and $Q$ are both nonmonic.

## Count the possible extensions and generators

Put $U=\log M_*$ for an upper bound $M_*\ge1$ on $M(P)$. Fix an isomorphism class of $E$. There are at most
$$
 M_*(1+\log M_*)^{e-1}
$$
integral ideals $\mathfrak d$ with $\operatorname{Nm}\mathfrak d\le M_*$. Indeed the number of ideals of norm $n$ is bounded by the ordered $e$-fold divisor function $\tau_e(n)$. At each rational prime this follows by padding the tuple of prime-ideal exponents weighted by their residue degrees to length $e$. The sum of $\tau_e(n)$ through $M_*$ is bounded by choosing the first $e-1$ factors and summing $M_*$ divided by their product.

For a fixed $\mathfrak d$ of norm $l$, round each $M(\sigma G)$ up to a dyadic power, and use twice those rounded bounds as the coefficient radii $A_\sigma$. Each $A_\sigma\ge1$, conjugate complex embeddings have equal radii, and $\prod_\sigma A_\sigma\le4^e M_*/l$. There are $\exp(O(e\log(2+U+e)))$ possible tuples of dyadic exponents, since their sum is $O(U+e)$.

For either coefficient, scale each archimedean coordinate by $A_\sigma$, using the same scale for the real and imaginary parts of a complex place. The coefficient then lies in the real box $[-1,1]^e$. If $z$ is a nonzero difference of two coefficients in $\mathfrak d^{-1}$, the ideal $(z)\mathfrak d$ is integral and $|\operatorname{Nm}_{E/\mathbb Q}z|\ge 1/l$. Thus the scaled difference has maximum coordinate at least $[2(l\prod_\sigma A_\sigma)^{1/e}]^{-1}$. Partitioning the scaled box at half this spacing bounds the number of possible coefficients by $C^e l\prod_\sigma A_\sigma$ for an absolute constant $C$. This is at most $M_*\exp(O(e))$, even when the individual radii are very unequal. The norm of the ideal gives the leading coefficient $l$, and $l\prod_\sigma\sigma G$ determines $P$.

Combining the two coefficients, the ideals and the dyadic radii shows that a fixed $E$ supplies at most $\exp(3U+O(e\log(2+U+e)))$ possible $P$. Every such $E$ has a smaller tower polynomial $Q$ with log Mahler measure at most $U+O(e\log(2+e))$. Iterate down the tower, fixing a field model for each possible $Q$ and counting repetitions as separate choices. The log budgets along the recursion differ from $U$ by $O(d\log(2+d))$, since the degrees halve. The degree-one count is at most $\exp(2U+O(1))$. For the total count $\mathcal T_d(U)$ of primitive normalized degree-$d$ tower polynomials this gives
$$
 \log \mathcal T_d(U)
 \le (3\log_2 d+2)U+
 O\!\left(d\log^2(2+d)+d\log(2+U+d\log(2+d))\right).
$$
For monic top polynomials the denominator ideal is the unit ideal throughout the tower. The smaller generators are integral, and the degree-one monic count is at most $\exp(U+O(1))$. The same error term then holds with $2\log_2 d+1$ in place of $3\log_2 d+2$.

## Count the represented inputs

By Jensen's formula and Parseval, $M(P)\le\|P\|_2\le\sqrt{d+1}\|P\|_\infty$, where $\|P\|_\infty$ is the coefficient height. At the stated height and degree this gives $U=O(V)$ and $\log\mathcal T_d(U)=o(L)$. There are $\exp(O(V))$ rational radix pairs. Every nonzero homogeneous evaluated integer has size $\exp(O(L))$, since $dV=O(L)$ and its coefficients have size $\exp(O(V))$. The divisor bound gives $\exp(o(L))$ divisors of any such value. Summing over degrees, polynomials and radix pairs proves the stated count. If the evaluated multiplier $|v^dP(u/v)/N|$ is at most $\exp(O(V))$, counting the possible multipliers directly improves the count to $\exp(O(V\log L))$. If $\gcd(v,N)=1$, reduction modulo $N$ at the radix is equivalent to reduction of the homogeneous value. The nonzero value requirement excludes a degree-one polynomial vanishing at the chosen rational radix.

More quantitatively, with maximum degree $d_{\max}=O(D)$ and the same radix bounds, covering a set of $X^{1-o(1)}$ inputs requires a log Mahler budget at least $(1-o(1))L/(3\log_2 d_{\max}+2)$, or $(1-o(1))L/(2\log_2 d_{\max}+1)$ for monic polynomials. Balanced semiprimes already give an input set of the required size. For the deduction it suffices to consider budgets $U\le L$, so homogeneous evaluated values still have $\exp(O(L))$ size. This lower bound also applies to log coefficient height up to $O(\log d_{\max})$. For a full projective mark box, height of this size prevents a uniform $\exp(O(V))$ norm bound. Fix a denominator $B_0$ large compared to $d$ and interpolate from $d+1$ numerator ratios spaced by $\gg1/d$ in a fixed subinterval of $[0,1]$. The coefficient height is at most $(Cd)^{O(d)}$ times the largest absolute value at those ratios. The corresponding homogeneous maximum is at least $B_0^d\|P\|_\infty/(Cd)^{O(d)}$. This implication concerns the full box and leaves smaller selected mark sets open.

## Towers over an arbitrary base field

Allow the tower to start at an arbitrary degree-$e_0$ field and take $r$ quadratic steps, so $d=2^r e_0$. The earlier recursion stops at $e_0$. At that degree the unrestricted polynomial count is $\exp((e_0+1)U+O(e_0^2))$ for log Mahler budget $U$, by the coefficient bound $2^{e_0}\exp(U)$. Including the growth of the budget at the higher levels bounds the log count at the top by
$$
 (e_0+1+3r)U+O\!\left(d^2\log(2+d)+d\log(2+U+d\log(2+d))\right).
$$
For $d=O(D)$ and $U=O(V)$, the same evaluated-value argument bounds the log count of represented inputs by $(e_0+1)U+o(L)$. Thus $e_0=o(D)$ still gives only $X^{o(1)}$ inputs. If $r$ is fixed and $e_0=\Theta(D)$, a digit-height bound $U\le(\kappa+o(1))L/d$ gives at most $X^{\kappa/2^r+o(1)}$ inputs. This implies scarcity when $\kappa<2^r$. A generic $O(V)$ budget in this fixed-step regime can make the bound vacuous.

The count applies when the primitive irreducible polynomial defines the stated field tower. A norm formula is covered when its factors arise from the relative minimal polynomial in that tower. Reducible norm forms or word alignments that only give a divisibility condition on a product of factors fall outside this scope. A separate argument would have to track which factors carry the prime divisors of $N$.

An exact arithmetic check compared the denominator-ideal norms, defined by lattice index, with both primitive leading coefficients on 320 real and imaginary quadratic fixtures. Of these, 319 gave irreducible quartic norm polynomials.
