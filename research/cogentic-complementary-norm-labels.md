# Order relations from exact dependencies of complementary norm values

Smooth chart norms can be combined through rational multiplicative dependencies of their complementary polynomial values. The extraction uses gcd refinement, integer linear algebra and modular verification. It needs neither unit logarithms nor a number-field factorization. The rank condition below applies to an explicit pool of charts and marks. A uniform supply at one-third cost remains open. [Chart torsion projection](cogentic-projected-order-rank.md) · [Rational evaluation labels](cogentic-rational-label-order-rank.md)

## Rational norms on the ideal-valuation kernel

For a chart field $K_i$ of degree $d_i$, the finite valuation of a norm at a rational prime $p$ is the sum of the chart's prime-ideal valuations over $p$ weighted by residue degrees. In particular, on the complete finite-valuation kernel,
\[
 \sum_a c_{ia}\,v_p\bigl(\lvert N_{K_i/\mathbb Q}(a-\theta_i)\rvert\bigr)
 =-d_i b_{ip}
\]
when $c_{ia}$ are mark exponents and $b_{ip}$ is the exponent of the rational scalar $p$ in chart $i$. This uses $N_{K_i/\mathbb Q}(p)=p^{d_i}$. For a nonmonic defining polynomial, the balanced mark sum cancels the leading-coefficient factor in the mark norms. Thus any rational exponent projection built from aggregate chart norm valuations alone factors through the chart-indexed scalar exponents. Including the valuations of the scalar norms themselves makes the projection identically zero. Choosing the target prime set after the norm factorization cannot change this identity.

## Divided differences give a different source of certified relations

Let $F_i\in\mathbb Z[X]$ be monic, let $N\mid F_i(m_i)$, and let a mark $a$ have $x= a-m_i$ and $y=F_i(a)$ both units modulo $N$. Integer division by the monic $X-m_i$ gives the complementary polynomial
\[
 G_i(X)=\frac{F_i(X)-F_i(m_i)}{X-m_i}\in\mathbb Z[X].
\]
The integer $g=G_i(a)$ is a unit modulo $N$, and $y/x\equiv g\pmod N$. If $F_i'(m_i)$ is a unit, the factorization $F_i=(X-m_i)G_i\bmod N$ splits the monic residue algebra into the evaluation component and the complementary component by the Chinese remainder theorem. The contribution of the complementary component to the norm of $a-X$ is $G_i(a)$. The direct identity $y/x\equiv g$ works even without the derivative condition.

Index an explicit pool of such marks by $j$, across any number of charts. Given an integer coefficient vector $c$ with $\prod_j |g_j|^{c_j}=1$, the identity gives the verified relation
\[
 \left(\prod_j |y_j/x_j|^{c_j}\right)^2=1\pmod N.
\]
Exponent doubling accounts for all signs. The $g_j$ may be much larger than the admitted smooth $y_j$ and $x_j$. They need not be factored.

Use a gcd-free basis of the positive $|g_j|$ to form their integer valuation matrix $C$. Distinct atoms in this representation are pairwise coprime integers greater than one, hence multiplicatively independent. A separate gcd-free basis represents the absolute rational labels $|y_j/x_j|$ by an integer matrix. Include the desired public primes in this refinement. Let $T$ consist of the rows for the permitted target coordinates and let $W$ contain the remaining rows. For instance one can sieve all labels by the Bach generators first, placing the unfactored residual rows in $W$. Put $A=\binom CW$. The exact rank obtained from these rational cancellations on the chosen coordinates is
\[
 \operatorname{rank}_{\mathbb Q} T(\ker_{\mathbb Q} A)
 =\operatorname{rank}_{\mathbb Q}\binom AT-\operatorname{rank}_{\mathbb Q}A .
\]
The first equality condition is $Cc=0$, precisely complementary cancellation. The second is $Wc=0$, precisely restriction to the chosen public bases. For each basis vector of the projected space choose a lift in the rational kernel and clear denominators. Modular verification and saturation then give the product certificates at this rank. [Saturation and its cofactor bound](cogentic-saturated-product-certificates.md)

Gcd refinement and elimination have polynomial bit cost in the explicit pool. In particular a one-third-size chart and mark library with polynomial-bit integer values can be tested as a batch. This supplies an alternative criterion to ideal cancellation and unit logarithms. It requires exact rational cancellation of the computed $g_j$, a stronger condition than the modular cancellation needed for the same projected product to be an order relation.

## Why simple pairings on the fixed schedule give zero rank

Suppose $g_i=\pm g_j$ for two retained marks. Then $y_i x_j\equiv\pm y_j x_i\pmod N$. If $|y_i x_j|+|y_j x_i|<N$, it follows that $|y_i/x_i|=|y_j/x_j|$ in $\mathbb Q$. Thus the complementary dependency on those two columns projects to zero. The same conclusion holds when the complementary residue ratio is known to be a global sign. In the fixed Cogentic schedule $\log |y_j|$ and $\log |x_j|$ are $O(V)$ with $V=o(\log N)$, so every such pairing satisfies the height bound. More generally if
\[
  \sum_j |c_j|\bigl(\log|y_j|+\log|x_j|\bigr)<\log(N/2),
\]
then a congruence of the rational product to either global sign forces its absolute rational value to be one. Clear denominators and bound the sum of the two positive sides by $2\exp(\sum_j |c_j|(\log|y_j|+\log|x_j|))<N$. In particular a nonzero direction from this construction on the fixed schedule needs $\sum_j |c_j|=\Omega(\log N/V)$ on an integer lift. This bound does not exclude larger coefficients of small bit length.

There is also an exact one-chart support obstruction independent of coefficient magnitude. Write $M=F(m)$, assume $M\ne0$, and group the marks by their signed norm value $y$. Let $h_y=\sum_{j:y_j=y} c_j$. Since $g_j=(y_j-M)/x_j$, an exact complementary cancellation gives
\[
 \prod_y |y-M|^{h_y}=\prod_j |x_j|^{c_j} .
\]
If $y-M$ has a prime factor larger than every $|x_j|$ and every $|y-y'|$ for distinct used values, that prime divides no other $y'-M$ and no evaluation label. Its valuation forces $h_y=0$. If every used signed value has such a prime, the right side is one and $\prod_j |y_j|^{c_j}=\prod_y|y|^{h_y}=1$ as well. Then the entire projected direction is zero. This applies regardless of the smoothness or multiplicity of the $y_j$. The existence of these private factors is a hypothesis. The matrix criterion tests the actual dependencies without that hypothesis or a factorization of $y-M$.

## Finite productive relation

For $N=77$, use $F_1=X^2+85X-9$ at $m_1=1$ and $F_2=X^2+83X-1875$ at $m_2=3$. The discriminants $7261,14389$ are positive nonsquares. The defining values at the two evaluations are $77,-21\cdot77$ and the derivatives $87,89$ are units modulo $77$. Use mark $a=0$ in both charts. The absolute rational labels $|F_i(0)/(-m_i)|$ are $9,625$, and both complementary values equal $86$. Hence the complementary rank is one and its rational-label projection has rank one. The resulting direction is $(3/25)^2$, whose primitive word $3/25$ is a mixed square root of one modulo $77$. The gcd $\gcd(3-25,77)=11$ gives the factor. The marked norms and evaluation labels use only $3,5$ and all are units. This checks the extraction arithmetic above the pairing height cutoff. The example is constructed from a known productive congruence and gives no general method for finding one.
