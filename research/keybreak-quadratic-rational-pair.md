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

## What ratio averaging discards at a prime denominator

For an odd prime \(Q\asymp M\), consider two different marks having the same parent root. Write their coefficient pairs as \((a_i,b_i)\). The integer \(a_1b_2-a_2b_1\) is nonzero. If it vanished, the parent-root equations would imply \(p\mid a_1c_2-a_2c_1\), hence equality over the integers since the minors are \(O(V'^2)<p\). Primitivity and positive leading coefficients would then make the marks equal. The same strict height bound makes this nonzero minor a unit modulo \(Q\).

For a nonzero base residue \(r_0\) define the unit phases \(f_i(r)=p^{-1}(a_i r^2+b_i rQ)\bmod Q^2\). Their ratio is
\[
 u(r)=\frac{a_1}{a_2}\left(1+Q\left(\frac{b_1}{a_1}-\frac{b_2}{a_2}\right)r^{-1}\right)\pmod{Q^2}.
\]
It depends only on \(r\bmod Q\). As \(r=r_0+Qj\) ranges over all lifts, \(f_1(r)\) ranges bijectively over the first-digit fiber \(z\equiv f_1(r_0)\bmod Q\), since its increment is \(2p^{-1}a_1r_0 Qj\). For a cofactor indicator \(A\), the full lift average is therefore \(Q^{-1}\sum_z A(z)A(z/u(r_0))\) over that fiber. The physical numerator interval of length at most \(Q\) sees at most one specified summand for each \(r_0\). An upper bound on the fiber average by itself incurs a factor \(Q\) for this summand by nonnegativity. For arbitrary supports this loss can occur, for instance by restricting support to the selected pair when their first digits are distinct. The unrestricted ratio correlation further sums over all first digits.

There is a second obstruction to a direct bound from the total square-modulus character energy. For a common cofactor set of \(S\) units in an interval of length \(O(X_R)=o(Q^2)\), its occupancy on units modulo \(Q^2\) is zero or one. If \(S_x\) is its occupancy in a fixed first digit modulo \(Q\), then \(S_x\ll 1+X_R/Q\). Multiplicative Parseval shows that the total energy with the characters of conductor exactly \(Q^2\), normalized by \(\phi(Q^2)\), equals
\[
 S-\frac1Q\sum_{x\bmod Q}S_x^2=(1-o(1))S .
\]
This estimate holds at each such prime \(Q\). In particular an average of these individual total energies cannot itself certify cancellation on the physical one-lift graph. A joint estimate exploiting how the *same* cofactor set meets the selected traces at different denominators is a separate possibility.

## Averaging the parent and the numerator

Averaging the parent prime before determining the two constant coefficients makes its common multiplicative dilation explicit. The following calculation applies to a common zero-one cofactor set \(A\) of units of size \(S=\rho X\) on an interval of length \(O(X)\), \(X\asymp M^2V/P\), satisfying \(|\widehat A(\chi)|\le S X^{-1/2}M^{o(1)}\) at every nonprincipal character. This calculation concerns a common test. A shape test varying with the individual discriminants requires a separate comparison. Put \(K=\phi(Q^2)\), let \(I\) be the physical numerator interval with \(|I|\asymp M\) distinct unit residues modulo \(Q\), and freeze the two nonproportional pairs of leading coefficients. Write \(x_i(r)=a_i r^2+b_i rQ\), and \(u_r=x_1(r)/x_2(r)\bmod Q^2\). The ratios are distinct on \(I\).

Uniform dilation over all units has pair mean \(K^{-1}|I|^{-1}\sum_{r\in I}R_A(u_r)\), where \(R_A(u)=\sum_z A(z)A(z/u)\). The Fourier coefficients of this correlation are \(|\widehat A(\chi)|^2\). Parseval, the character bound and the injective ratios give relative mean-square error for \(R_A(u_r)\) around \(S^2/K\) at most
\[
 \frac{K^2}{|I| S X}M^{o(1)}
 \ll \frac{P^2}{M V^2\rho}M^{o(1)}.
\]
At the bands with \(M\) exceeding \(P^2/V^2\) by a fixed power and \(\rho=M^{-o(1)}\), uniform dilation gives the desired pair scale.

For actual primes \(p\asymp P\), the character-pair expansion for \(A(x_1/p)A(x_2/p)\) inserts \(B(\eta)=\mathbb E_p\eta(p)\) at \(\eta=\chi\psi\), up to conjugation. The part \(\eta=1\) is exactly the uniform-dilation contribution. For every other \(\eta\) Dirichlet GRH gives \(|B(\eta)|\ll P^{-1/2}(\log M)^{O(1)}\). The numerator average supplies \(D_\eta(\chi)=\mathbb E_{r\in I}\overline\chi(u_r)\overline\eta(x_2(r))\), with \(\sum_\chi|D_\eta(\chi)|^2=K/|I|\). Thus Cauchy and \(\sum_{\eta,\chi}|\widehat A(\chi)\widehat A(\eta\chi^{-1})|^2=(KS)^2\) bound the absolute off-diagonal by \(S(\log M)^{O(1)}/\sqrt{P|I|}\). Relative to \(S^2/K^2\) the resulting bound is of order \(M^{3/2}\sqrt P/(V\rho)\) up to logarithms. As a direct description of the missing information, for \(L\) distinct sampled primes the squared Euclidean distance between the joint physical and uniform-dilation probability vectors on pairs of residues equals \(|I|^{-1}(1/L-1/K)\). Each ratio is distinct and its conditional first-coordinate support has size \(L\). The diagonal calculation controls ratios, while these estimates leave the cancellation between cofactor phases on that conditional support open.

## A finite check of the common-anchor moment

At \(p=100003\) and height \(282\), sample 2,048 primitive anchors in each of two dyads, \(3p\le Q<6p\) and \(6p\le Q<12p\), at slopes in \([.57,.63]\) and with odd \(Q\). Enumerate primitive negative fundamental marks of the indicated split parity in a fixed coefficient box by solving for their constant coefficient modulo \(p\). For a dyadic cofactor-size bin estimate its smoothness rate from the observed marks. Conditional independent thinning at those rates gives a comparison at the same raw marks and cofactor sizes.

| Denominator range | Cutoff | Observed ordered smooth pairs | Comparison | Observed fraction of anchors with a hit | Comparison |
|---|---:|---:|---:|---:|---:|
| \([3p,6p)\) | 251 | 14 | 15.8 | .0840 | .0837 |
| \([6p,12p)\) | 251 | 2 | 3.1 | .0391 | .0388 |
| \([3p,6p)\) | 1009 | 232 | 246.9 | .2974 | .2952 |
| \([6p,12p)\) | 1009 | 100 | 93.7 | .1943 | .1968 |

The two dyads contain 11,233 and 11,240 raw marks. The enumeration agrees with exhaustive enumeration for every residue in a smaller case at \(p=31\). The strict cutoff 251 gives few actual pairs. The larger cutoff exceeds the mark height, the dyad scales are only constant multiples of the parent here, and the comparison rates are fitted to the same sample. These finite counts leave the uniform asymptotic moment open. Reproduce the two dyads and the intermediate cutoff 503 with `python3 experiments/keybreak-quadratic-rational-moments.py`. [Seeded arithmetic experiment](../experiments/keybreak-quadratic-rational-moments.py)

## Averaging the coefficient pairs as well as the numerator

Take an odd denominator \(Q\asymp M\), an interval of \(R\) distinct unit numerators modulo \(Q\), and a full coefficient box \(1\le a\le V'\), \(|b|\le V'\), with \((a,Q)=1\) and \(V'=V(\log M)^{O(1)}\). Here \(R\) denotes the number of units in the interval; in the physical dyads it is \(M/(\log M)^{O(1)}\) or larger up to the fixed scale factors. Put \(C_r=\{a r^2+brQ\bmod Q^2\}\). Distinct coefficient pairs give distinct residues, first by reducing modulo \(Q\), then by reading the coefficient of \(Q\). A cofactor in a fixed interval \(X\asymp M^2V/P\), with \(X=o(Q^2)\), determines at most one integer constant coefficient. Removing its height and discriminant tests gives a pair upper bound. By the unit-leading construction, restricting the lower test to these units retains the actual common cofactor density to polynomial factors. [Ordinary first moment](keybreak-quadratic-rational-mean.md#unit-leading-coefficients-at-rough-composite-denominators)

Let \(\pi(v_1,v_2)=R^{-1}\sum_r1_{v_1,v_2\in C_r}\). This is a counting measure, with total mass at most \(O((V')^4)\). Group its support by the ratio of its two base residues modulo \(Q\). Each ratio has a unique reduced positive representative \(u/v\) arising from coefficients in the box since \((V')^2<Q\). Write \(U=\max(u,v)\). There are at most \(V'/U\) compatible leading pairs \((ju,jv)\). For fixed absolute phases and fixed \(j\), the congruence \(r^2\equiv v_1/(ju)\pmod Q\) has at most \(2^{\omega(Q)}\) roots. At a given root both \(b_i\) are unique. Thus the maximum point mass on this ratio is at most \(2^{\omega(Q)}V'/(UR)\), while its total mass is \(O((V')^3/U)\). There are \(O(U)\) such reduced ratios of height exactly \(U\), giving
\[
 \sum_{v_1,v_2}\pi(v_1,v_2)^2
 \ll 2^{\omega(Q)}(V')^4\log(2V')/R.
\]
For prime denominators the diagonal terms from using the same numerator twice in this squared norm already contribute \(\asymp (V')^4/R\). On complete odd denominator dyads the factor \(2^{\omega(Q)}\) costs only a logarithm on average, by summing its squarefree divisor expansion. The same upper bounds apply if distinct admissible coefficient pairs are required.

Let \(S\) be the cardinality of the common balanced cofactor set, \(S=\rho X\), \(K=\phi(Q^2)\). Use its prime-product character bound \(S X^{-1/2} M^{o(1)}\) off the principal character. Restrict it to units modulo \(Q\), which removes only \(o(S)\) choices since each bin has exponentially many primes and \(Q\) has \(O(\log M)\) prime divisors. For uniform common dilation, Parseval at each fixed \(r\) gives mean square equal to its squared mean plus an error at most \(S^2 X^{-1} M^{o(1)} |C_r|/K\). Relative to the squared full-box scale \(((V')^2S/K)^2\) this error is at most \(P V^{-3}M^{o(1)}\), a power saving. For actual parent primes the nonprincipal dilation terms insert the GRH factor \(O(P^{-1/2}(\log M)^{O(1)})\). By Cauchy on the two independent character indices, the unnormalized Fourier norms of the product cofactor function and of \(\pi\) are at most \(KS\) and \(K\|\pi\|_2\), respectively. Excluding the prime divisors of \(Q\) preserves the prime estimate. The absolute residual is thus \(O(P^{-1/2} S\|\pi\|_2(\log M)^{O(1)})\). Averaging complete physical denominator dyads gives the relative upper bound
\[
 \frac{M^{3/2}\sqrt P}{\rho V^3}(\log M)^{O(1)}.
\]
This saves a factor \(V^2\) compared with summing the fixed-coefficient estimates. It still grows as a power on the intended bands; the absolute two-dimensional Fourier energy alone leaves the needed common-anchor estimate open.

## Root fractions at the spacing of the anchors

For a fixed eligible parent \(p\), take \(n\) in the common cofactor set and prime discriminants \(D\) in the designated dyad. Let \(\mathcal W_p\) consist of the records \((n,D,b\bmod 2pn)\) with \(b^2\equiv D\pmod{4pn}\), using both signs and both orientations at two. Restrict to \(p\nmid n\); this is automatic in the smooth range. For the ordinary balanced prime-bin set write \(W=|\mathcal W_p|\asymp S V^2/\log V\), by the reverse-order count, uniformly in \(p\). Each record supplies a fraction \(x=b/(2pn)\pmod 1\). An upper bound on clustering at the Farey scale,
\[
 \#\{(w,w')\in\mathcal W_p^2:\|x_w-x_{w'}\|_{\mathbb R/\mathbb Z}
                  \le (\log V)^{C_0}/M^2\}
 \ \ll (\log V)^{C_1}(W+W^2/M^2),                 \tag{8}
\]
suffices for the ordinary rational second moment on the tight coefficient box up to logarithmic factors. Here \(C_0\) must dominate the previously fixed height and anchor-range exponents. The ratio \(W/M^2\) is a positive power of \(P\) up to \(P^{o(1)}\) since \(V^3/P\) has a fixed power margin.

To see the transfer, write a mark as \(h=[a,b_h,c]\) and an anchor as \(R=(r,Q)\). Choose \(T=(u,v)\) with \(rv-Qu=1\). Its mixed coefficient \(B_h\) in this basis satisfies
\[
 \frac{B_h}{2pn}=\frac vQ-\frac{2ar+b_hQ}{2Qpn}.
\]
The correction is \(O((\log V)^{C}/M^2)\) and \(B_h^2\equiv D\pmod{4pn}\). For a given \(R\) the record determines the mark: its residue specifies the unique lift of \(B_h/(2pn)\) sufficiently close to this fixed \(v/Q\), and the remaining coefficient is fixed by the discriminant. Conversely a specified fraction \(x\) can be that close to only \((\log V)^{O(1)}\) different reduced centers \(v/Q\), by elementary Farey spacing for denominators \(\le M(\log V)^C\). Each center determines \(r\) uniquely in the physical slope interval from \(rv\equiv1\pmod Q\). This bounds the number of anchors contributing a given pair. Dividing (8) with this multiplicity by the anchor count proves the asserted upper moment; dyadic probabilities change it by at most polynomial logarithms. Well-spacing for roots of a *fixed* quadratic congruence is used in the classical binary-form large sieve. In (8) the discriminants and smooth cofactor moduli both vary. [Exact completion identity in Lean](../formal/cogentic/Cogentic/RandomizedQuadraticCompletion.lean) · [Balog, Blomer, Dartyge and Tenenbaum, §5.3](https://ems.press/content/serial-article-files/43293)

Two types of close pairs can be excluded exactly. Put \(g=(n_1,n_2)\), \(u_i=n_i/g\). Alter the lift of the first root by a multiple of \(2pn_1\) to take the short circular difference, set \(c_i=(b_i^2-D_i)/(4pn_i)\), and put
\[
 t=b_1u_2-b_2u_1,\qquad K=2pg(c_1u_2+c_2u_1)-b_1b_2.
\]
Direct expansion gives
\[
 t^2=D_1u_2^2+D_2u_1^2+2K u_1u_2,
 \qquad 4pg\mid K^2-D_1D_2.
\]
The divisibility follows by expanding \(K^2\) modulo \(4pg\) and using \(b_i^2\equiv D_i\pmod{4pg}\). At the distance in (8), \(|t|\ll V(\log V)^{C}\max(u_1,u_2)\) since \(pn_i\asymp M^2 V\). Their ratio is bounded and \(D_i<0\), so \(0<K\ll V^2(\log V)^{O(1)}<p/2\). If \(D_1=D_2\), then \(K\equiv\pm D_1\pmod p\), forcing \(K=|D_1|\). The identity becomes \(t^2=-|D_1|(u_1-u_2)^2\), hence \(n_1=n_2\) and the two fractions are identical. They give the same record. For distinct prime discriminants, \(D_1D_2\) is nonsquare. Moreover \(K\ge\sqrt{D_1D_2}\) by the first identity and AM–GM, so \(K^2-D_1D_2\) is a positive multiple of \(4pg\). It follows that every distinct close pair has
\[
 D_1\ne D_2,\qquad (n_1,n_2)\ll V^4(\log V)^{O(1)}/p.
\]
In particular the same-cofactor diagonal contributes exactly one record per record at this scale because \(pX_R\gg V^4(\log V)^{O(1)}\) in the intended bands. Pairs with different discriminants and a small common cofactor can still contribute to (8).

### Pairs with a shared bin prime are negligible at both tabulated budgets

In the actual anchor moment the two odd cofactor parts may be required to be coprime at a negligible cost. More generally, after the raw pair \(h,g\) and the parent have been fixed, prescribe any nonzero integer \(J=J_{h,g,p}\) with \(\log(2+|J|)\le(\log V)^C\). The contribution from pairs for which an **odd** bin prime of either cofactor divides \(J\) is at most
\[
 \left(\frac{V^3}{P}\right)^2
 \exp\!\left(-\log B-\frac{\log(M^2/P)}{\log B}\log d+o(H)\right),       \tag{9}
\]
where \(H=(\log N)^{1/3}(\log\log N)^{2/3}\) and the top scales are fixed. To get the coprimality conclusion take \(J=\operatorname{Res}(h,g)\), since at a primitive anchor a prime common to the values must divide the resultant. Multiplying \(J\) by any of the nonzero coefficients, minors, or discriminants of the fixed pair costs only polynomially many additional prime tests in the estimate.

For a specified parent root and a specified offending \(q\mid J\) of the first cofactor, \(q=B^{1-o(1)}\). The odd cofactor part is squarefree. Its remaining bin primes have product \(\asymp X_R/q\), larger than \(T=M^2/(pq)\) by order \(V\). Multiplying these other primes until the product first exceeds \(T/B\) gives \(T/B<k\le T\). Both \(q\) and the primes of \(k\) divide \(h(R)\); they are distinct and different from \(p\). There are at most \(2^{1+\omega(k)}\) projective root choices, since \(h\) is primitive. Together with the fixed parent root each determines a planar congruence lattice of index \(pqk\le M^2\), including projective infinity when it occurs at another prime. The primitive-point bound above gives \(O((M')^2/(pqk))\) anchors in each lattice.

To sum \(2^{\omega(k)}/k\), the bin support forces \(\omega(k)\ge \log(T/B)/\log B\). For \(j\) prime factors the sum is at most \((2\sum_{\ell\le B}1/\ell)^j/j!\), summing over primes \(\ell\). The tail beginning at \(j\asymp d\) is at most \(\exp(-\log(T)\log d/\log B+o(H))\) by the prime harmonic sum and the factorial estimate. There are only polynomially many \(q\mid J\). Summing the raw pairs by (1), dividing by the anchor count and exchanging the two forms gives (9). This uses only one cofactor after the offending prime has been identified and holds uniformly at each parent.

On a band put \(P=M^y, V=M^v\), so \(2v<y\). Write \(bH=\log B+o(H)\). The saving in (9) compared with the square of the balanced first-moment scale is at least
\[
 \left(b-\frac{2+2v-y}{3\delta b}\right)H+o(H)
 \ \ge\left(b-\frac{2}{3\delta b}\right)H+o(H).
\]
Indeed the actual bin density is \(\exp[-(\log X_R/\log B)\log d+o(H)]\). In the two finite tables, \(b=\delta\beta\) gives a margin exceeding \(.44H\) in the wider table and \(.45H\) in the narrower table at leading order. Thus odd prime overlap and pair-specific exceptional prime factors are negligible on the needed *smooth-pair* scale. The correlation of pairs with disjoint odd supports remains open. [Quadratic finite budgets](keybreak-quadratic-top-budget.md#finite-witnesses-and-limiting-arithmetic)

### A uniform conic upper bound for nearby fractions

In (8), set \(A_i=|D_i|\), \(\Delta=K^2-A_1A_2\). Distinct close records give distinct primes \(A_1,A_2\) and \(0<\Delta\ll V^4(\log V)^C\). For fixed \(p,g,A_1,A_2,K\), the primitive triple \((u_1,u_2,t)\) lies on the nonsingular conic with symmetric matrix
\[
 \begin{pmatrix}A_2&-K&0\\-K&A_1&0\\0&0&1\end{pmatrix}.
\]
Its determinant has absolute value \(\Delta\), and its two-by-two minors have gcd one because they include the distinct primes \(A_1,A_2\). In a box of sides \(O(U),O(U),O(VU(\log V)^C)\), \(U=X_R/g\), the uniform conic estimate gives at most \(O(\tau(\Delta)(1+UV^{1/3}(\log V)^C/\Delta^{1/3}))\) primitive triples. [Browning and Heath-Brown, Corollary 2](https://arxiv.org/pdf/math/0404456#page=4)

For each triple the linear equation in \(b_1,b_2\) leaves a common integer shift \((u_1j,u_2j)\) with \(j\bmod 2pg\). At every odd prime dividing \(pg\) one of the two slopes is a unit. Its square-root condition leaves at most two choices there. The factor at two is bounded since the bin cofactors have precisely one factor of two. Thus there are \(O(2^{\omega(g)})\) lifts. For a fixed \(\Delta<P^2\) there is at most one parent in the dyad dividing it. Each \(K\ll V^2(\log V)^C\) gives at most two ordered prime pairs by \(A_1A_2=K^2-\Delta\).

Dropping the smoothness constraint and averaging the count over parents gives \(O((\log V)^C M^2V^6/P^2)\) distinct close pairs, at the raw scale. In detail the additive one in the conic estimate contributes \(O((\log V)^C V^6/P)\) by \(\sum_{\Delta\le Y}\tau(\Delta)3^{\omega(\Delta)}\ll Y(\log Y)^5\). The volume part for \(g\ge G\) is at most
\[
 \frac{V^2 X_R V^{1/3}}{P}(\log V)^C
 \sum_{\Delta\le Y}\tau(\Delta)\Delta^{-1/3}
          \sum_{g\mid\Delta,\ g\ge G}\frac{2^{\omega(g)}}g
 \ \ll\ \frac{V^{7/3}X_R}{P}\,\frac{Y^{2/3}}G(\log V)^C .
\]
This follows by writing \(\Delta=gj\) and summing \(2^{\omega(g)}\tau(g)/g^2\) over the tail, using an ordinary fixed divisor-function bound. At \(Y=V^4(\log V)^C\) this proves the raw estimate. Restricting \(Y\) to \(V^{4-\epsilon}\) or imposing \(G\ge V^\epsilon\) gives a fixed power saving and hence negligibility even on the smooth scale for typical parents. The remaining conics have large determinant and require both coordinates to be smooth. [Verified integer identities](../formal/cogentic/Cogentic/RandomizedRootFractionIdentity.lean)

At longer denominator scales, an independent held-out check at \(p=257,V=232,B=229\) used 2,048 calibration anchors and 4,096 reporting anchors per range. For \(Q\asymp p^2\) there were 91,200 ordered smooth pairs, compared with 90,054.68 under conditional independent thinning. The difference per anchor was .280 with 95% interval [−.829,1.388]. For \(Q\asymp p^{5/2}\) there were 508 pairs compared with 434.23; the difference per anchor was .0180 with interval [−.0077,.0437]. The cutoff is below the mark height but this finite experiment takes \(V>\sqrt p\) to obtain enough pairs. Reproduce it with the earlier script and its `--long` option.

### A second smoothness saving after averaging the parent

Write \(n_i=2u_i\) with coprime odd parts, and \(U\asymp X_R\), \(u_i\asymp U\). The estimate below concerns the balanced squarefree bin set. Write \(\rho\) for its density at this scale, so \(\log\rho=-(\log U/\log B)\log d+o(H)\). Besides retaining the full smooth density of the first cofactor, the close-pair average gains
\[
             \exp\!\left(-\frac{\log V}{\log B}\log d+o(H)\right)
\]
from the second cofactor. All scales are on a fixed positive band as above. This gain holds at the original rational cutoff.

**Removing the parent from the spacing condition.** A physical close pair supplies coarse records \((u_i,A_i,r_i)\), where \(A_i=|D_i|\asymp V^2\) and \(r_i=b_i\bmod u_i\) satisfies \(r_i^2\equiv-A_i\pmod{u_i}\). The short lift of \(t=b_1u_2-b_2u_1\) gives
\[
 \left\|r_1/u_1-r_2/u_2\right\|\le (\log V)^{O(1)} V/U .
\]
Conversely a specified coarse pair arising from a physical pair fixes this \(t\): its residue modulo \(u_1u_2\) is known and the permitted length \(O(VU(\log V)^{O(1)})\) is smaller than \(u_1u_2/2\). The conic identity above fixes \(K\). For distinct prime discriminants, \(0<K^2-A_1A_2<P^2\) and the parent divides it, so there are \(O(1)\) possible dyadic parents. At each such parent the lift from \((t,u_1,u_2)\) back to the full root residues has bounded multiplicity by the linear-shift argument above with \(g=2\). Equal-discriminant close pairs are the diagonal. Thus the coarse count bounds the sum over parents, with fixed multiplicity.

**Counting coarse neighbours.** Fix the first record and put \(z_i=(r_i+i\sqrt{A_i})/u_i\), using an integer translate of \(z_2\) to realize the close difference. Each \(z_i\) is the upper root of the positive integral form \([u_i,-2r_i,(r_i^2+A_i)/u_i]\), of discriminant \(-4A_i\). Their imaginary parts are comparable to \(V/U\). The formula \(\cosh d(z_1,z_2)=1+|z_1-z_2|^2/(2\Im z_1\Im z_2)\) shows \(e^{d(z_1,z_2)}\le (\log V)^{O(1)}\). Choose one \(\gamma\in\mathrm{SL}_2(\mathbb Z)\) sending \(z_1\) into the standard fundamental domain, with image height \(h_0\ge\sqrt3/2\). Set \(m_0=V/h_0\); the transformed first leading coefficient is the positive integer \(\sqrt{A_1}/h_0\), so \(1\ll m_0\ll V\).

Hyperbolic invariance gives \(h_0/L\le\Im(\gamma z_2)\le L h_0\) and \(|\Re(\gamma z_2)|\le L h_0\), for \(L=(\log V)^{O(1)}\): use \(|\Re(\gamma z_1)|\le1/2\) and the same distance formula. The transformed second integral form \([m,b,c]\) therefore lies in
\[
       0<m\le m_0 L,\qquad |b|\le V L,\qquad
       0<c\le (V^2/m_0)L
\]
after increasing the fixed logarithmic power. Here \(m=\sqrt{A_2}/\Im(\gamma z_2)\), \(b=-2m\Re(\gamma z_2)\), \(c=m|\gamma z_2|^2\). The original leading coefficient is \(u_2=mj^2+bjk+ck^2\), where \((j,k)\) is the first column of \(\gamma\) and \((j,k)=1\). The chart is fixed by the first record; the transformed form determines the second record by the inverse change of variables.

Let \(T_0\asymp V^2/m_0\) with a fixed small constant, so \(T_0\gg V\) and \(T_0<U\) on these bands. If \(u_2\) is in the bin set, multiply its distinct primes until their product first exceeds \(T_0/B\); this gives a squarefree divisor \(T_0/B<t_0\le T_0\). Split it as \(t_0=st'\) between primes dividing \(k\) and primes coprime to \(k\). Necessarily \(s\mid m\), since \(s\mid k\) and \((s,j)=1\). There are at most \(m_0 L/s\) positive choices for \(m\). Given \(m,b\), the condition modulo \(t'\) fixes one residue class for \(c\). Its upper range is at least a fixed multiple of \(t'\); thus at most \(O((V^2/m_0)L/t')\) choices occur. The three-dimensional count is \(O(V^3 L^3/t_0)\), also when one factor of the divisor is one. This handles every prime dividing the chart denominator.

Summing \(1/t_0\) over squarefree bin divisors costs at most \(\exp[-(\log T_0/\log B)\log d+o(H)]\) by the prime harmonic factorial tail used in (9). This proves the stated uniform bound for the second record in the neighbourhood of *any* first record, with \(V^3\) as the raw local count. The number of first records is at most \(U\rho\, V^2\exp(o(H))\): each odd cofactor has \(O(d)\) prime factors and hence at most \(2^{O(d)}\) root orientations per discriminant. After summing over parents and dividing by their dyadic prime count, the distinct close pairs consequently number at most
\[
   \frac{UV^5}{P}\,\rho\,
   \exp\!\left(-\frac{\log V}{\log B}\log d+o(H)\right)
\]
on average. Splitting polylogarithmically larger cofactor and height ranges into dyads changes only the \(o(H)\) term. For two cofactor dyads with ratio bounded by a polylog, the same chart argument applies with adjusted \(L\).

In the physical anchor moment this is \((V^3/P)^2\rho\exp[-(\log V/\log B)\log d+o(H)]\) for typical parents, by the Farey transfer, Markov's inequality and \(U\asymp M^2V/P\). The shared-odd-prime pairs from (9) and the diagonal fit this upper bound on the two tabulated bands. Together with the typical-parent first moment it gives a probability of at least
\[
       \exp\!\left(-\frac{\log(M^2/P)}{\log B}\log d+o(H)\right)
\]
of reaching half that parent's smooth mean. The previous trimmed one-cofactor estimate had \(\log U\) in the numerator. This improves the leading probability exponent by \((\log V/\log B)\log d\); it still leaves an exponential gap to a polynomial relative second moment.

### Averaging the reduced charts raises the divisor level to nearly the box volume

Assume in addition \(U/V\gg V^3\) by a fixed power, as on the two tabulated bands. For every fixed \(0<\epsilon<1\) the preceding close-pair bound holds with \((3-\epsilon)\log V\) in place of \(\log V\) in the second smoothness saving. In particular the numerator in the heavy-anchor probability becomes \(\log(U/V^{3-\epsilon})\). The residual exponent is positive on both tabulated bands.

Put \(\delta=\epsilon/4\) and \(T_*=V^{3-4\delta}\). Reduce each first record as before, retaining its actual transformed leading coefficient \(m_1\asymp w\) in dyadic groups. Fix a tie convention on the boundary of the fundamental domain. There are \(O(wV^2)\) possible first reduced forms per group: \(m_1\asymp w\), \(|b_1|\le m_1\), and \(c_1\ll V^2/w\). The primitive vector \((j,k)\) representing \(u_1\asymp U\) lies in a rectangle
\[
 |j|\ll\sqrt{U/w},\qquad |k|\ll\sqrt{Uw}/V.
\]
This follows by completing the square in the reduced first form, with \(|b_1|\le m_1\) and \(w\ll V\). Its area is \(O(U/V)\). The two side lengths exceed one. A fixed reduced form and a fixed vector determine at most one first coarse record: unimodular completions differ by adding an integer multiple of the vector in their second column, changing the middle coefficient by a multiple of \(2u_1\). Thus for \(w<V^{1-\delta}\) there are in total \(O(UV^{2-\delta})\) first records, even without smoothness. Each has at most \(V^3(\log V)^{O(1)}\) coarse neighbours by the previous box. This contribution saves a fixed power of \(V\), negligible compared with both smooth densities.

For the other groups the widths of the enclosing centred box for the second form can be chosen as \(wL,VL,V^2L/w\), with a common \(L=(\log V)^{O(1)}\). Their product is \(V^3L^3\) and the smallest width is \(\gg V^{1-\delta}\). Majorize the indicator by a constant times the product of centred Gaussians at these widths. For any squarefree divisor \(t\in(T_*/B,T_*]\) of a second cofactor, impose
\[
       m j^2+bjk+c k^2\equiv0\pmod t .
\]
Additive orthogonality and one-dimensional Poisson summation in each coefficient give a principal term \(O(V^3L^3/t)\), uniformly in the chart. For a nonprincipal frequency reduce the multiplier to a unit modulo \(e=t/(h,t)>1\). Relative to the principal scale the dual Gaussian is negligible unless the least absolute residues of each of
\[
        h'(j^2,jk,k^2)\pmod e,\qquad (h',e)=1 ,
\]
are at most \(R=eV^{-1+\delta}(\log V)^2\), with a fixed constant if needed. Nonminimal lifts and larger coordinates have total relative error \(O(V^{-C})\) for any designated \(C\), even after summing polynomially many frequencies. If \(R<1\) there is no nonprincipal tuple in the truncated box.

To average the remaining positive error, a fixed unimodular residue triple determines at most one projective slope \((j:k)\bmod e\). At each prime dividing \(e\) the first or last coordinate is a unit; dividing the middle coordinate by it determines the other affine coordinate. CRT applies because \(e\) is squarefree. At any fixed primitive chart the triple also determines the unit multiplier uniquely. Each slope gives an index-\(e\) lattice. Scaling the above rectangle to a square preserves the elementary primitive-point estimate \(O(1+(U/V)/e)=O(U/(Ve))\): in rank one only the two primitive vectors on the line contribute; in rank two the row count is bounded by a constant times area over covolume. Equivalently, primitivity in the ambient integer lattice implies primitivity in the congruence lattice, enough for this upper bound.

Write the short signed lift as \((A_0,A_1,A_2)\). It satisfies \(A_0A_2=A_1^2+le\) with \(|l|\ll R^2/e\). For each \(A_1,l\) with nonzero right side the divisor bound gives \(V^{o(1)}\) possibilities for \(A_0,A_2\). If the right side vanishes then \(e\mid A_1^2\), hence \(A_1=0\) by squarefreeness and \(R<e\), and the axes give \(O(R)\) nonzero triples. The total for \(R\ge1\) is \(O((R+R^3/e)V^{o(1)})\). Dividing the chart error sum by \(U/V\), and summing over \(e\mid t\), bounds the average relative error by
\[
 V^{o(1)}\big(V^{-1+\delta}+tV^{-3+3\delta}\big)
       \ll V^{-\delta+o(1)} .
\]
This estimate treats slopes at infinity and both signs of the dual lifts. It needs only \(e\le T_*\le U/V\) for the chart count.

Use the principal term **with the actual first smooth records**. Its sum over \(t\) gives \(V^3\exp[-(\log T_*/\log B)\log d+o(H)]\) per first record, by the harmonic factorial bound. For the error one may use all first forms in the group, multiplying the chart sum by at most \(O(wV^2)\). Using the harmonic bound \(\sum_{t\le T_*}1/t=O(\log V)\) and summing dyadically in \(w\ll V\) leaves \(O(UV^5V^{-\delta+o(1)})\) error. The bin densities are \(V^{-o(1)}\), so this is negligible. The coarse-to-physical transfer and overlap estimate are exactly as in the preceding proof. The resulting probability lower bound improves the trimmed first-moment exponent by \((3-\epsilon)(\log V/\log B)\log d\) on each fixed band. Passing to a liminf of normalized exponents allows \(\epsilon\downarrow0\); the displayed bounds are for fixed \(\epsilon\).

### A variance bound up to the square root of the number of charts

Let \(D_0=U/V\) and \(T=D_0^{(1-\epsilon)/2}\) for fixed \(0<\epsilon<1\). On the two tabulated families the previous close-pair bound also holds with \(\log T\) as the second logarithmic saving. Consequently one may use the larger of the two divisor levels; the new limiting logarithmic deficit in the half-mean hit probability is at most \(\tfrac12\log(UV)\). This is a bound for the original smooth cofactor, with a positive deficit.

Keep the reduced-chart decomposition. Discard \(w<V^{1-\delta}\) at the raw power saving already proved, with fixed small \(\delta>0\). For one remaining group use a common rectangular set of primitive chart vectors with side scales \(J\asymp\sqrt{U/w}\), \(K\asymp\sqrt{Uw}/V\) and \(JK\asymp D_0\), enlarging fixed constants to contain the required vectors. Both sides are positive powers of \(U\) on each fixed band. Let \(\mathcal F\) be the forms in its enclosing coefficient box with the required discriminant \(-4A\) for a prime \(A\asymp V^2\). Retain positive definiteness. These forms are primitive at every odd prime since their discriminants have no odd square factor. The same box contains both first and second forms, after enlarging its fixed logarithmic factor. Write \(F_0=V^3(\log V)^{O(1)}\) for a common upper bound on its size.

For every squarefree bin product \(T/B<t\le T\), let \(N_t(j,k)\) count forms in \(\mathcal F\) whose value at \((j,k)\) is divisible by \(t\), and put \(N=\sum_t N_t\). Each smooth candidate is counted at least once. Define \(\mu_t\) to be the mean over the *uniform projective slope* modulo \(t\), and \(\mu=\sum_t\mu_t\). A nonzero homogeneous quadratic modulo a prime has at most two projective zeros, so \(\mu_t\le F_0 2^{\omega(t)}/t\). The factorial tail yields \(\mu\le F_0\rho_T\exp(o(H))\), where \(\rho_T=\exp[-(\log T/\log B)\log d]\). We compare this model with uniform probability over the primitive chart rectangle.

**Weighted equidistribution of slopes.** For \(m=t\) or \(m=[t,t']\) we have \(T/B<m\le D_0^{1-\epsilon}\). A projective slope corresponds to a lattice of determinant \(m\). Scale the axes by \(1/J,1/K\) and let \(\Delta=m/(JK)\) and \(\lambda\) be its covolume and shortest length. Choose a small fixed \(\kappa>0\). At slopes with \(\lambda\ge\Delta U^\kappa\) the count of primitive points of the *lattice* in the normalized rectangle equals
\[
 \frac{\text{rectangle area}}{\zeta(2)\Delta}
    + O\bigl(\lambda^{-1}\log(2+1/\lambda)+\lambda/\Delta\bigr).
\]
Indeed the lattice-point discrepancy in the rectangle scaled by \(1/d\) is \(O(1+1/(d\lambda))\) by counting rows along a shortest vector, uniformly in direction. Apply Möbius inversion to nonzero points up to \(d\ll1/\lambda\); the tail of the main sum costs \(O(\lambda/\Delta)\). Since \(\lambda\ll\sqrt\Delta\), the relative error saves a fixed power of \(U\). To get primitive points of the ambient integer lattice, delete those divisible by a prime \(q\mid m\); at all other primes the two notions of primitivity agree. The corresponding intersection with \(q\mathbb Z^2\) has index \(q\) in the slope lattice since \(m\) is squarefree and its image modulo \(q\) is a full line. A lattice-primitive vector remains primitive in the intersection, which contains at most \(O(1+1/(q\Delta))\) such points in the rectangle. Normalize by the total primitive chart count, asymptotic to the unscaled area over \(\zeta(2)\) with power-saving relative error by the same computation. Each good slope therefore has the uniform projective probability \(1/\prod_{q\mid m}(q+1)\) to relative error \(O(U^{-c}+B^{-1+o(1)})\) for some fixed \(c>0\), since all its primes exceed \(B^{1-o(1)}\) and there are \(O(d)\) of them.

For the other slopes one needs only the *weighted* error summed over the test moduli. Group \(m\asymp M_0\) dyadically. Each such slope has a nonzero integer witness \((j_0,k_0)\) in the rectangle with coordinate bounds \(O(J M_0 U^\kappa/D_0)\) and \(O(K M_0 U^\kappa/D_0)\). Fix this vector and two counted forms \(f,f'\). The positive integers \(f(j_0,k_0), f'(j_0,k_0)\) are bounded by a fixed power of \(U\), and divisibility by \(t,t'\), respectively, is necessary: membership in the slope lattice suffices even if the witness is imprimitive. The divisor bound leaves \(U^{o(1)}\) possible modulus pairs. For each pair, the forms' local root bounds give at most \(2^{\omega(m)}=U^{o(1)}\) admissible slopes. Both the uniform and physical probability per slope are \(O(1/m)\), the latter by the primitive rectangle bound and \(m<D_0\). Thus the sum of bad-slope contributions weighted by \(N_tN_{t'}\), in either model, is bounded in this dyad by
\[
 F_0^2 U^{o(1)}\left(M_0^{-1}
           +U^\kappa(1/J+1/K)+U^{2\kappa}M_0/D_0\right)
      \ll F_0^2 U^{-c'} .
\]
Choose \(\kappa\) sufficiently small in terms of the fixed scales and \(\epsilon\). The corresponding single-modulus argument with one form costs \(O(F_0 U^{-c'})\). The dyadic summation preserves a power saving. The use of nonzero positive form values is essential in this divisor switch.

**Variance.** When \((t,t')=1\), the uniform joint expectation of \(N_t N_{t'}\) is exactly \(\mu_t\mu_{t'}\) by CRT. For overlapping moduli choose one prime \(q\mid(t,t')\) and condition on its slope. The box bound for one congruence gives at most \(O(F_0/q)\) choices for each form: \(q\ll V^{o(1)}\) and at least one of the three coefficient multipliers is a unit. At the other primes of \([t,t']\) there are at most two possible slopes per prime for any fixed pair. Their uniform joint expectation is thus at most \(O(F_0^2 2^{\omega(t)+\omega(t')}/(q[t,t']))\). A squarefree least common multiple \(n\ge T/B\) has total weighted pattern count at most \(8^{\omega(n)}\), since a prime can occur on the first side, the second, or both with weights \(2,2,4\). The factorial harmonic tail and \(q\ge B^{1-o(1)}\) bound the complete overlap sum. Expanding the centered square and using both the single and paired slope comparisons gives
\[
 \mathbb E_{\rm chart}(N-\mu)^2
  \ll F_0^2\bigl(U^{-c''}+B^{-1+o(1)}\rho_T\exp(o(H))\bigr).
\]
In particular, the relative comparison errors on the coprime terms multiply \(\mu^2\), and are included in this bound.

At a fixed chart let \(A\) be the number of actual first records assigned to it, and bound second choices by the number \(C\) of smooth forms in the enclosing box. Both are at most \(N\). Pointwise \(AC\le 2\mu A+(N-\mu)^2\). Sum over the \(O(D_0)\) primitive vectors per group and then the dyadic groups. The first term retains the total actual smooth first-record mass. For the variance term, \(B^{-1+o(1)}\) is negligible against \(\rho\) on these bands: in the notation of (9), \(b>(2+v-y)/(3\delta_{\rm budget} b)\) with a fixed margin, since \(v<y\) and the earlier comparison already bounded \(2/(3\delta_{\rm budget} b)\). Cusp groups, the diagonal and shared odd cofactor factors fit as before. This proves the claimed replacement of the second smoothness saving. [Weighted finite comparison in Lean](../formal/cogentic/Cogentic/RandomizedWeightedIncidence.lean) · [Coefficient congruence in Lean](../formal/cogentic/Cogentic/RandomizedQuadraticCoefficientCongruence.lean)
