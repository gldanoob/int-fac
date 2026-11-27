# Width floor for uniform reduced imaginary quadratic classes

A uniform square class of discriminant \(-4N\) has reduced leading coefficient at most \(N^\theta\), for fixed \(0<\theta<1/2\), with probability \(N^{\theta-1/2+o(1)}\) on the rough-input branch under Dirichlet GRH. The upper bound counts all classes that have *any* integral equivalent ideal below that norm. Neither changing the representative nor selecting a sign in a square fiber avoids the rarity. The bound concerns uniform class sampling, and certain quantitatively controlled approximations. It gives no limit on a sampler with a deliberately different class law. [Reduced-form supply at width \(\sqrt N\)](keybreak-reduced-form-smooth-supply.md) · [Relative signs in a square fiber](keybreak-reduced-form-root-signs.md)

## A reduced form minimizes the norm within its class

For a positive definite reduced form \([A,B,C]\), the inequalities \(|B|\le A\le C\) give
\[
 Ax^2+Bxy+Cy^2\ \ge\ A(x^2-|xy|+y^2)\ \ge\ A
\]
for any nonzero integer pair. The minimum is attained at \((1,0)\). Thus an equivalent form, which represents the same integers under a unimodular change of variables, cannot have smaller positive leading coefficient.

There is also a direct ideal formulation covering imprimitive ideals. Let \(I=[A,(-B+\sqrt\Delta)/2]\) be the integral invertible ideal of the reduced form, of norm \(A\). An equivalent integral invertible ideal is \(\alpha I\) for some nonzero \(\alpha\in I^{-1}=\overline I/A\). On the basis \(1,(-B-\sqrt\Delta)/(2A)\) of \(I^{-1}\), its norm \(A\,\mathrm N_{K/\mathbb Q}(\alpha)\) is the form \([A,-B,C]\) evaluated at the coordinates of \(\alpha\). The same inequality bounds it below by \(A\). This applies to the proper class group of a nonmaximal order, since the ideal–form correspondence and \(I\overline I=A\mathcal O\) hold for the primitive proper invertible ideal attached to the reduced form. It does not assume the other representative is primitive. [Ideal and form classes of quadratic orders](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf#page=137)

## Counting the rare classes

Write \(n\) for the integer in a discriminant \(\Delta=-4n\), so \(n=N\) in the ordinary case. Choose one canonical reduced form in each proper class. For a given leading coefficient \(A\), write its even middle coefficient as \(2b\). The congruence \(b^2\equiv-n\bmod A\) and reduction restrict the number of possible \(b\)'s by an absolute constant times \(2^{\omega(A)}\sqrt{\gcd(A,n)}\). At an odd prime power, dividing off a common even valuation leaves at most two unit roots; at a power of two there are at most four. When the modulus divides \(n\), the count is \(p^{\lfloor e/2\rfloor}\) at modulus \(p^e\). Reduction permits at most one representative per residue except for bounded edge conventions. Restricting to primitive forms only decreases this upper bound.

For \(X\ge1\), split this upper sum by the exact gcd \(g_0=\gcd(A,n)\). Writing \(A=g_0a\), use \(2^{\omega(A)}\le2^{\omega(g_0)}2^{\omega(a)}\) and \(\sum_{a\le U}2^{\omega(a)}\le U(1+\log U)\). Dropping the residual gcd restriction yields
\[
 \#\{\text{proper classes with } A\le X\}
 \ll X(1+\log X)\sum_{g_0\mid n}\frac{2^{\omega(g_0)}}{\sqrt{g_0}}
 \le X(1+\log X)\,O\!\left(
       \prod_{p\mid n}\left(1+\frac{2}{\sqrt p-1}\right)\right).
 \tag{1}
\]
The estimate allows all genera, nonunit leading coefficients and all prime multiplicities in \(n\).

Let \(h_n\) be the order class number and \(g_n\) its index of squares. The [class number and genus bounds](keybreak-reduced-form-smooth-supply.md#normalization-and-upper-count) give \(h_n\ge\sqrt n/\operatorname{poly}(\log(2n))\) under Dirichlet GRH and \(g_n\le 2^{\omega(n)+O(1)}\). A uniform square class is uniform on a set of size \(h_n/g_n\). Dividing (1) by this cardinality gives, for \(1\le X\le\sqrt n\),
\[
 \Pr(A\le X)\ \ll\ \frac{X}{\sqrt n}\operatorname{poly}(\log(2n))
       \prod_{p\mid n}\left[2\left(1+\frac{2}{\sqrt p-1}\right)\right].
 \tag{2}
\]
The same upper bound applies in any fixed coset of the square subgroup. On the rough branch for \(n=N\), the Euler factor without the \(2\)'s is \(1+o(1)\), and \(2^{\omega(N)}=\exp(o(H))\). Hence (2) is at most \(X/\sqrt N\) times \(\exp(o(H))\).

For a matching leading lower bound on that branch, take \(N^\varepsilon\le X\le\sqrt N/2\) with fixed \(\varepsilon>0\). Choose a prime \(A\in[X/2,X]\) splitting in the quadratic field and with trivial genus class. The [Dirichlet genus count](keybreak-reduced-form-smooth-supply.md#genus-as-a-finite-dirichlet-condition) gives \(\gg X/(g_N\log X)\) choices, since \(g_N=\exp(o(H))\) and the dyad is polynomial in \(N\). Each constructs a distinct strictly reduced form in the square subgroup. Dividing by \(h_N/g_N\) gives a lower probability \(\gg X/(\sqrt N\operatorname{poly}(\log N))\). This lower count does not impose smoothness or the field-good restrictions. The upper count applies with either restriction. In particular the mass of \(A\le\sqrt N\exp(-cH)\), for fixed \(c>0\), has exact leading exponent \(-cH\). If \(\log(\sqrt N/X)=\omega(H)\), uniform class rejection alone costs more than \(\exp(O(H))\) draws.

## Multipliers, rejection, and sign choices

Consider discriminants \(-4mN\) with positive integer \(m\le N^{O(1)}\) and the same norm bound \(X\). In (2), factor out the product for \(N\). The factor \(\sqrt m\) in the class-number denominator absorbs all the new primes up to an absolute constant, because
\[
 \frac1{\sqrt m}\prod_{\substack{p\mid m\\p\nmid N}}
    2\left(1+\frac{2}{\sqrt p-1}\right)
 \ \le\ \prod_{\substack{p\mid m\\p\nmid N}}
    \frac{2(1+2/(\sqrt p-1))}{\sqrt p}
 \ \ll\ 1 .
\]
Every factor on the right is at most one outside a fixed finite set of primes. The logarithmic factors in (2) are still polynomial in \(\log N\) for a fixed polynomial size range of multipliers. Consequently the same rough-input upper bound \(X/\sqrt N\cdot\exp(o(H))\) holds uniformly in those discriminants. A fixed or subpolynomial family searched with one uniform class per member cannot remove the polynomial deficit for fixed \(\theta<1/2\). A change that divides the norm by a growing, specially certified factor is a different event.

More generally, suppose each raw proposal is conditionally uniform in the square subgroup or in a fixed coset of its chosen multiplier, with the multiplier and coset chosen before the fresh draw. A union bound over the first \(q\) raw proposals gives probability at most \(q\) times the uniform upper bound from (2), even with adaptive choices or a preliminary pool. Thus attaining a constant chance of one such class needs at least the reciprocal number of proposals, up to a constant, also as a lower bound on expected proposals to first success. All preprocessing draws count, even if saved or rejected. Charging just one bit operation per proposal already rules out an \(\exp(O(H))\) budget for fixed \(\theta<1/2\) on this route.

Squaring maps uniform classes to uniform square classes with equal fiber sizes. Varying the two-torsion translate, reduction sign, or modular root within a fixed fiber does not change its squared class or minimum norm. Selecting amongst uniform candidate classes is bounded by the same union count. If a raw law is pointwise dominated by \(K_0\) times the uniform law, the bound simply gains \(K_0\), so \(K_0=N^{o(1)}\) still preserves a fixed polynomial deficit. A total variation approximation of error \(\varepsilon_0\) instead adds \(\varepsilon_0\) per proposal. An error only known to be small on a subexponential scale may be larger than the event being counted. No conclusion here treats such an error as relative or asserts that signed outputs remain uniform after selecting a rare fiber.
