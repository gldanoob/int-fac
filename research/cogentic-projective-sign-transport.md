# Projective transport preserves the acquired CRT sign

Fix one odd input \(N\), and write \(D=(\log N/\log\log N)^{1/3}\), \(H=D\log\log N\), \(V=DH\). Lee–Venkatesan's square-congruence argument samples odd-degree fields and separately needs useful signs from certified dependencies. For a dependency with rational root \(R\) and product of evaluated field roots \(S\), write its sign as \([R/S]\) in the square roots of unity modulo \(N\), quotiented by the global signs. The argument below tests a candidate symmetry of the acquired rows. It applies to every odd \(N\) and does not use a special representation of the sign by a quadratic character. [Lee–Venkatesan, §7 and Remark 7.4](https://arxiv.org/pdf/1805.08873#page=38) · [Verified dependency sign map](cogentic-mnfs-sign-map.md)

## Transport of exact dependencies

Consider a projective coordinate change
\[
 T(X)=\frac{A X+B}{C X+E},\qquad
 \begin{pmatrix}A&B\\C&E\end{pmatrix}\in\mathrm{GL}_2(\mathbb Q).
\]
Make this matrix primitive integral by common scaling. Replace \(\theta\) by \(T(\theta)\), \(m\) by \(T(m)\), and each primitive mark \((a,b)\) by the primitive representative \((a',b')\) of the image slope. Assume the compared evaluations and the denominators of \(T\) at the radix are units modulo \(N\). Then
\[
 a'-b'T(X)=\lambda_{a,b}\frac{a-bX}{C X+E},
 \qquad
 \lambda_{a,b}=\pm\frac{AE-BC}{\gcd(Aa+Bb,Ca+Eb)} .
\]
The gcd in the denominator divides \(AE-BC\) by the adjugate identity and primitivity of \((a,b)\).

Suppose a chosen dependency is certified before and after the transport. For a field in which it selects \(j\) marks, let \(s=\prod\lambda_{a,b}\). Under the field isomorphism the new product equals the old product times \(s/(C\theta+E)^j\). Thus:

- For even \(j\), \(s\) is a square in the field. Since the field degree is odd, \(s\) is a rational square, by taking norms. A field root changes by \(\sqrt{s}/(C\theta+E)^{j/2}\), and the corresponding multiplier on the rational product is exactly the square of its value at \(m\).
- For odd \(j\) and \(C=0\), the multiplier \(s/E^j\) is rational and is a field square, hence again a rational square. The corresponding roots change by the same rational multiplier.
- For odd \(j\) and \(C\ne0\), \(s(C\theta+E)\) must be a field square. This follows by multiplying \(s/(C\theta+E)^j\) by the square \((C\theta+E)^{j+1}\).

These conclusions apply separately in each field, since the rational root condition concerns their combined product. If only the first two cases occur, the rational and evaluated algebraic roots change by the same multiplier, up to global signs. The original and transported dependencies have the same CRT sign.

Any projective move matching three distinct acquired slopes in the old and new height boxes has a primitive matrix of height \(O(U^6)\) when both mark heights are at most \(U\). The three homogeneous correspondence equations have coefficients \(O(U^2)\), and their rank is three because a projective map is determined by three distinct pairs. Their \(3\times3\) cofactors give the bound. For \(U=\exp(O(H))\) the nonzero determinant is \(N^{o(1)}\). If it is a nonunit, its gcd with \(N\) already gives a proper factor. The same holds for \(Cm+E\) when nonzero, since \(m=\exp(O(V))\). If the radices satisfy only \(m'(Cm+E)\equiv Am+B\pmod N\), the height bound and \(m'=\exp(O(V))\) force equality over the integers. Thus selecting another small integer representative of the projective image cannot modify the rational square comparison.

## Rational twists of short products are rare

The following strengthens the [short-support exclusion](cogentic-short-squares-interpolation.md) to arbitrary rational twists. Let
\[
 f(X)=f_0(X)+M(X)G(X)
\]
with primitive \(M\) of degree \(O(D)\) divisible by \(X-m\). Keep the constant through cubic coefficients of \(G\) independently uniform on intervals of lengths at least \(\exp(c_0 V)\) for a fixed \(c_0>0\). Other coefficients may be held fixed or sampled independently. This holds for the Lee–Venkatesan coefficient law at fixed positive coefficient slack. For any fixed mark height bound \(\exp(KH)\), except with probability \(\exp(-\Omega(V/\log V))\), either \(f\) is reducible or no nonempty product of at most \(cD/\log\log N\) distinct primitive marks is a square in \(\mathbb Q[X]/(f)\) after multiplication by any rational scalar \(s\ne0\). Here \(c>0\) is sufficiently small in terms of the height and width constants.

For fixed \(P(X)=\prod_i(a_i-b_iX)\), choose auxiliary primes \(p\asymp V\) in a sufficiently short fixed-scale interval as in the previous bound, with total product at most \(\exp(c_0 V/2)\). Exclude primes dividing the first denominator or its slope determinants with the other marks. The excluded primes remove only \(o(V/\log V)\) choices, and at the remaining primes \(P\bmod p\) has a simple zero. The quadratic character sum bound gives two sets \(T_+,T_-\), each of size at least \(p/3\) after removing zeros of \(M\), where \(P\) is a unit and has the indicated Legendre sign. For a single nonconstant linear factor the two signs have equal counts before removing these zeros. [Weil, *On Some Exponential Sums*](https://doi.org/10.1073/pnas.34.5.204)

For \(t\in T_+\), \(u\in T_-\), the four variables \(f(t),f'(t),f(u),f'(u)\) are jointly uniform modulo \(p\) under the uniform law for the four free coefficients. This follows from Hermite interpolation for \(G\) and invertibility of multiplication by \(M\) at \(t,u\). Let \(Z_p\) count ordered pairs \((t,u)\) of simple roots of \(f\bmod p\) in these sets. Its mean is
\[
 |T_+||T_-|p^{-2}(1-p^{-1})^2\gg1 .
\]
In its second moment, terms with \(r\) distinct root sites, \(2\le r\le4\), have probability at most \(p^{-r}\) by ordinary interpolation of the four coefficients. There are \(O(p^r)\) such terms, giving \(\mathbb E Z_p^2=O(1)\), hence \(\Pr[Z_p>0]\gg1\). For irreducible \(f\), each of these two simple roots lifts to an embedding of the same field into \(\mathbb Q_p\). If \(sP(\theta)\) were a field square, both its images would have to be squares. Since both images of \(P(\theta)\) are units, \(v_p(s)\) would have to be even. Removing this even valuation leaves one common unit scalar for the two images. It cannot make both residues squares because they have opposite Legendre signs. The pair of roots therefore excludes every rational \(s\) at once.

The CRT makes these local tests independent with uniform coefficients modulo the prime product. The integer box contributes total variation \(O(\exp(-c_0V/2))\). Taking the union over \(\exp(O(kH))\) supports up to length \(k\) and setting \(k\le cD/\log\log N\) proves the claim. The same exceptional probability scale holds across \(\exp(O(H))\) fresh single-input draws. Conditional acceptance on irreducibility of probability bounded below changes the bound by only a constant factor.

## Consequence for an involution on acquired rows

With this probability bound, every small nonconstant linear denominator \(C\theta+E\) is excluded up to all rational twists. A projective reparametrization preserving the chosen rows and their certification must therefore use even selected support in every nonaffinely changed field. A field with nonempty selected support already needs at least three distinct slopes outside the same exceptional event, so the height bound for its projective matrix follows from the dependency itself. Its CRT sign is preserved. This conclusion allows the projective moves to be chosen after seeing the field and acquired marks. It also applies after exact interpolation at prescribed marks when the four wide free coefficients remain available.

A finite replay illustrates an already productive dependency under such transport. Take \(N=77\), \(m=5\), \(P(X)=\prod_{a\in\{-3,0,10,13\}}(a-X)\), \(Q(X)=(X-5)^2-9(X-5)+26\), and \(f=P-Q^2\), an irreducible cubic. The four homogeneous algebraic norms have prime divisors only \(2,3\), their rational values are \(5\)-smooth, and all are units modulo \(77\). The rational root is \(40\), and \(Q(5)=26\) gives gcd \(7\). The nonaffine transport \(T(X)=1/(X-4)\) has transformed radix \(1\). The transformed cubic, four norms and square identity again certify gcd \(7\). The replay also enumerated finite-field paired simple-root moments.

This inhibits a coordinate symmetry of a certified dependency. It does not bound changes that replace the square dependencies with different ones, and gives no positive-rank bound for the long dependencies of the original collection process.
