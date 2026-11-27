# Rational pairs of quadratic marks

Use the scales of the quadratic rational first moment. The parent prime lies in \([P,2P]\), \(V=P^\alpha\) with fixed \(1/3<\alpha<1/2\), and \(M\) is the anchor scale. Put
\[
 X_R=M^2V/P,\qquad u_R=\frac{\log X_R}{\log B},\qquad H=d\log d.
\]
Here \(\log P\asymp\log M\asymp d^2\log d\), \(\log B\asymp H\), and the bands under consideration have \(M\gg P\). The marks are primitive positive definite integral quadratics, their coefficient height is at most \(V'=V(\log P)^{O(1)}\), and their discriminants are negative fundamental, congruent to one modulo eight and of absolute size \(\asymp V^2\). The raw pair count below only uses the height, primitivity and positive definiteness. [Rational first moment](keybreak-quadratic-rational-mean.md)

## Raw factorial moment for every parent

Let \(Z_t\) count the marks \(h\) with \(h(t,1)=0\) in \(\mathbb F_p\). For every parent \(p\),
\[
 \sum_{t\in\mathbb F_p} Z_t(Z_t-1)
 \ll \frac{(V')^6}{p}(\log P)^2.
 \tag{1}
\]
The following planar count applies both to coefficient planes and to anchor congruences. In the radius-\(R\) ball about zero, a rank-two lattice of covolume \(D\) contains \(O(1+R^2/D)\) ambient primitive integer vectors. Indeed, if the vectors in the ball span at most a line, at most two are primitive. Otherwise choose a shortest nonzero lattice vector of length \(\lambda\le R\). Its parallel lattice rows have spacing \(D/\lambda\le R\), since some vector in the ball lies off its row. Multiplying the row count by the maximum count per row gives \(O(R^2/D)\).

Distinct primitive positive definite forms \(h,g\) have linearly independent coefficient vectors. Their cross product has all components \(O((V')^2)<p\). Thus they remain independent modulo \(p\), and the integer primitive normal \(w=(x,y,z)\) obtained by dividing that cross product by its content is nonzero modulo \(p\). A common root forces \(w\) to be proportional to \((t^2,t,1)\) modulo \(p\). In particular \(z\) is a unit modulo \(p\) and \(t=y/z\) is uniquely determined by \(w\). The projective point at infinity is never a parent root because the positive leading coefficient is smaller than \(p\).

The normal satisfies \(xz-y^2=jp\) for a nonzero integer \(j\). If \(xz=y^2\), the equality \(w=z((y/z)^2,y/z,1)\) over the rationals would give a real root of \(h\), contradicting positive definiteness. For \(\|w\|_\infty\le U<p\) one has \(0<|j|\le 2U^2/p\) and \(x\ne0\), since \(x=0\) would force \(p\mid y\) and hence \(y=0\).

Write \(J=\lfloor2U^2/p\rfloor\). For fixed \(x,j\), the variable \(y\) satisfies \(y^2\equiv-jp\pmod{|x|}\), and then \(z\) is determined. The number of square roots of an integer \(k\) modulo \(m\) is at most \(2\cdot2^{\omega(m)}\sqrt{\gcd(m,k)}\). At a prime power \(q^e\), if \(q^e\mid k\) there are \(q^{\lfloor e/2\rfloor}\) roots. Otherwise the valuation of \(k\) must be even, say \(2s<e\), and dividing off \(q^{2s}\) reduces to unit roots, at most two for odd \(q\) and four at two, with a factor \(q^s\) for lifts. This proves the bound by CRT. As \(p\nmid x\), the normal count is therefore bounded by a constant times
\[
 \sum_{0<|j|\le J}
 \sum_{1\le m\le U}(U/m+1)2^{\omega(m)}\sqrt{\gcd(m,j)}
 \ll UJ(\log(2U))^2.
\]
For the last inequality, bound the square root by \(\sum_{a\mid m,\ a\mid j}\sqrt a\). The sum over multiples of \(a\) in \(m\) is at most \(O((U/a)2^{\omega(a)}(\log(2U))^2)\), by \(2^{\omega(ab)}\le2^{\omega(a)}2^{\omega(b)}\) and the elementary divisor sums \(\sum_{b\le T}2^{\omega(b)}\ll T\log(2T)\) and \(\sum_{b\le T}2^{\omega(b)}/b\ll(\log(2T))^2\). There are at most \(2J/a\) nonzero multiples of \(a\) in \(j\). The remaining series \(\sum_a 2^{\omega(a)}a^{-3/2}\) converges. Thus there are \(O(U^3(\log(2U))^2/p)\) possible normals in the box, including zero possibilities if \(J=0\).

For a primitive normal \(w\), the lattice \(w^\perp\cap\mathbb Z^3\) has covolume \(\|w\|_2\). To see this, extend a basis of the kernel of \(v\mapsto w\cdot v\) by a vector with dot product one. The resulting basis of \(\mathbb Z^3\) spans volume one and its height above the kernel plane is \(1/\|w\|_2\). For a dyadic range \(U/2<\|w\|_\infty\le U\) the planar count bounds the number of possible ordered marks by \(O((1+(V')^2/U)^2)\) per normal. The normal count times this bound is \(O((V')^4U(\log P)^2/p)\), since \(U\ll (V')^2\). Summing the dyadic ranges proves (1). Also \(\sum_t Z_t\ll (V')^3\), since each form has at most two parent roots.

## Exceptional roots have small total raw mass

For any set \(E\subset\mathbb F_p\) with \(|E|/p\le p^{-\eta}\), where \(\eta>0\) is fixed, Cauchy–Schwarz and (1) give
\[
 \sum_{t\in E} Z_t\le \sqrt{|E|\sum_t Z_t^2}
 \ll (V')^3p^{-\eta/2}\log P.
 \tag{2}
\]
Here \((V')^3/p\) grows as a positive power, so the diagonal is absorbed. In particular (2) applies to the exceptional dual roots at each parent. For the uniform primitive-anchor law of the first moment, the probability of any finite projective root \(t\) is \(O((\log P)^{O(1)}/p)\). The anchor region is contained in a ball of radius \(M'=M(\log P)^{O(1)}\) and contains \(\gg M^2\) primitive points with odd denominator, by the elementary primitive-point count in a fixed rectangle inside the cone. The latter count follows by Möbius inversion over odd common divisors, with a positive limiting density and error \(O(M\log M)\). The congruence \(r\equiv tQ\pmod p\) defines a lattice of index \(p\), so the planar bound gives \(O(1+(M')^2/p)\) possible primitive anchors. Since \(M\gg P\), (2) bounds the total raw first-moment mass of exceptional slopes by \((V^3/P)p^{-\eta/2}(\log P)^{O(1)}\) for every parent. The bound also controls any subcount on those slopes, including the smooth count. [Exceptional dual-root density](keybreak-quadratic-mark-geometry.md)

On the good dual roots the full coefficient population has the uniform upper bound \(O((V')^3/p)\). Apply the smooth Poisson estimate there to a fixed nonnegative smooth majorant of the coefficient cube, at scale \(V'\). The primitivity and discriminant restrictions can be dropped for this cap. Let \(Z\) count the smooth marks and \(Z_{mathrm{good}}\) count those on good dual roots. The lost expectation is at most the raw mass in (2), which is negligible relative to the smooth first-moment lower bound at the parents where that bound holds. Put \(\mu=\mathbb E Z\) there. For all sufficiently large inputs, \(\mathbb E Z_{\mathrm{good}}\ge3\mu/4\). With \(K\ll(V^3/P)(\log P)^{O(1)}\) the uniform cap on \(Z_{\mathrm{good}}\),
\[
 \frac{3\mu}{4}\le \mathbb E Z_{\mathrm{good}}
 \le \frac{\mu}{2}+K\Pr[Z_{\mathrm{good}}\ge\mu/2].
\]
Consequently \(\Pr[Z\ge\mu/2]\ge\exp(-u_R\log u_R+o(H))\). This cap and the trimmed first moment give a stronger probability bound for the rational count alone than the divisor-level second moment below, which controls actual joint divisibility.

## Two smoothly divisible values at projective lattice level

Fix distinct marks with a common finite parent root and write \(R_{hg}=|\operatorname{Res}(h,g)|/p\). The homogeneous Sylvester resultant is nonzero since two nonproportional positive definite quadratics cannot share a complex root, and its absolute value is \(O((V')^4)<p^2\). The parent root implies \(p\mid\operatorname{Res}(h,g)\), so \(R_{hg}\) is an integer coprime to \(p\).

Consider a primitive anchor with \(h(r,Q)=pn_1\), \(g(r,Q)=pn_2\). For divisors \(k_i\mid n_i\) supported on primes at most \(B<p\), necessarily
\[
 \gcd(k_1,k_2)\mid R_{hg}.
 \tag{3}
\]
At any prime power dividing both \(k_i\), use the affine chart of the primitive anchor in which one coordinate is a unit. The Sylvester Bézout identity in that chart implies that the prime power divides the resultant. Swapping the coordinates in both forms preserves its absolute value.

Each form has at most two primitive projective roots modulo every prime power. For odd unramified primes the projective roots are simple and lift uniquely. At an odd ramified prime a repeated root lies in a chart where the quadratic leading coefficient is a unit modulo the prime. Indeed, a primitive quadratic with discriminant zero modulo an odd prime is a nonzero scalar times a square of a linear form there, and one can choose the chart with a unit leading coefficient at its root. Completing the square shows that its discriminant of valuation one precludes a root modulo the square of the prime. At two, the discriminant condition gives two simple roots. These can also be read directly from the parity condition of the first-moment family. Thus for fixed \(k_1,k_2\) there are at most \(2^{\omega(k_1)+\omega(k_2)}\) possible projective classes modulo \(p[k_1,k_2]\), using the unique parent root. Each class imposes a linear congruence lattice of index \(p[k_1,k_2]\): it is the inverse image of the rank-one direct summand generated by a primitive projective representative, with the local congruences combined by CRT.

The represented cofactors satisfy \(n_i=X_R(\log P)^{O(1)}\), with upper and lower polylogarithmic factors, because the coefficient height and discriminant bound the two eigenvalues of each form between \(V/(\log P)^{O(1)}\) and \(V(\log P)^{O(1)}\). Take divisor thresholds \(T_i\) below the minimum cofactor size with \(pT_1T_2\le M^2\). If both cofactors are \(B\)-smooth, multiplying their prime factors up to the respective threshold supplies divisors \(k_i\in[T_i/B,T_i]\). Using the planar count and (3), the number of such anchors for this pair is at most a constant times
\[
 \frac{(M')^2}{p}
 \sum_{\substack{T_i/B\le k_i\le T_i,\; P^+(k_i)\le B\\
                 (k_1,k_2)\mid R_{hg}}}
    \frac{2^{\omega(k_1)+\omega(k_2)}}{[k_1,k_2]}.
 \tag{4}
\]
The index bound is where the pointwise lattice estimate supplies the volume factor. The \(+1\) term of that estimate can dominate above this level.

Set \(\gamma=\log d/\log B\). Insert \((k_1k_2)^\gamma\) into the sum in (4) and multiply by \((T_1T_2/B^2)^{-\gamma}\). Dropping the thresholds in the weighted sum gives an Euler product. At a prime \(q\nmid R_{hg}\), only one of the two valuations can be positive, giving local factor \(1+O(q^{-1+\gamma})\). At a prime \(q\mid R_{hg}\), allow both valuations without an upper bound. For the terms where both are positive, summing by the maximum exponent gives \(O(q^{-1+2\gamma})\), uniformly for \(\gamma\le1/4\). The total logarithm from the first factors is \(o(H)\). Indeed, Chebyshev's upper bound and partial summation give \(\sum_{q\le B}q^{-1+\gamma}\ll 1+\log(1/\gamma)+B^\gamma/(\gamma\log B)\). The additional logarithm from primes dividing \(R_{hg}\) is also \(o(H)\). Below \((\log P)^4\) use \(q^{2\gamma}=O(1)\) and the harmonic bound; above it there are \(O(\log P)\) primes dividing \(R_{hg}\) and each contribution is at most \(q^{-1/2}\). The factor \(B^{2\gamma}=d^2\) is of size \(\exp(o(H))\). Thus (4) is
\[
 \ll \frac{(M')^2}{p}\exp\bigl(-\gamma\log(T_1T_2)+o(H)\bigr)
 \tag{5}
\]
uniformly in the distinct marks and parent.

Choose \(T_1=T_2=M/\sqrt p\), which is below the minimum cofactor size on these bands. Sum (5) by (1) and normalize by the number of anchors. The resulting estimate for the smooth count \(Z\), uniform in \(p\), is
\[
 \mathbb E[Z(Z-1)]\ll
 \left(\frac{V^3}{P}\right)^2
 \exp\left(-\frac{\log(M^2/P)}{\log B}\log d+o(H)\right).
 \tag{6}
\]
The diagonal is bounded by the raw first moment \((V^3/P)(\log P)^{O(1)}\), which is negligible relative to the right side of (6) as an upper bound on \(\mathbb E Z^2\).

The lattice cutoff captures \(\log(M^2/P)\) of the two cofactor logs, whose sum is \(2\log X_R\) to leading order. The exponent still missing from the independent-pair scale is
\[
 \frac{2\log X_R-\log(M^2/P)}{\log B}\log d
 =\frac{\log(M^2/P)+2\log V}{\log B}\log d.
\]
At the parents covered by the first-moment lower bound, (6) and Cauchy–Schwarz applied to \(Z\) on \(\{Z\ge \mathbb E Z/2\}\) give a lower bound on the probability of that event of the form \(\exp(-[2\log X_R-\log(M^2/P)]\log d/\log B+o(H))\). The gap in this estimate comes from the absolute lattice level. The resultant primes and the raw factorial moment contribute only \(\exp(o(H))\) factors.
