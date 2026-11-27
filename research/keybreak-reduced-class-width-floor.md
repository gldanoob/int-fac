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

## Which quadratic discriminants permit the normalized root?

Allow any imaginary quadratic order with integral generator \(\xi\), trace \(T\), norm \(P\), and discriminant \(\Delta=T^2-4P\). An evaluation at a known root \(r\) of \(X^2-TX+P\bmod N\) sends the conjugate generator to \(s=T-r\). The normalized ideal-root construction needs a change of representative by a scalar \(\lambda\) of unit norm modulo \(N\) to multiply the root by at most a global sign. Its multiplier is
\[
 \rho(\lambda^2/\operatorname{Nm}(\lambda))
 =\rho(\lambda)/\rho(\bar\lambda).
\]
On the branch \(\gcd(N,6)=1\), this holds for every such scalar exactly when \(r=s\bmod N\). Indeed take \(\lambda=a+\xi\) and choose \(a\) so that \(a+r,a+s,2a+T\) are all units. There are at most three forbidden residues at each prime dividing \(N\), so CRT guarantees a choice simultaneously. For this scalar the quotient cannot be \(-1\) since its numerator and denominator have unit sum. Equality to \(+1\) forces \(r=s\). Conversely, when \(r=s\), evaluation commutes with conjugation on the whole localized order and the quotient always equals one. The argument also works prime power by prime power. It is enough to require representative independence just on the principal ideal class, since multiplying the unit ideal by this scalar is an allowed change there. [Lean calculation for normalized scalar evaluations](../formal/cogentic/Cogentic/RandomizedQuadraticRamification.lean)

In particular \(\gcd(2r-T,N)\) either gives a proper divisor, equals one, or equals \(N\). In the unit case the scalar above exhibits a failure of representative independence. In the last case \(N\mid\Delta\), since \(\Delta\equiv(r-s)^2\bmod N\). Thus choosing a smaller absolute discriminant cannot implement this normalization on a rough input. One can find the scalar without CRT data by sampling \(a\bmod N\) and testing the three units. The acceptance probability is at least \(\prod_{p\mid N}(1-3/p)\), inverse-polylogarithmic in \(N\) by the prime harmonic bound. A proper gcd encountered during this test is already useful.

The width count above extends from \(-4mN\) to all imaginary quadratic order discriminants divisible by \(N\) with \(|\Delta|\le N^{O(1)}\). For \([A,B,C]\), the middle coefficient satisfies \(B^2\equiv\Delta\bmod 4A\) and is restricted to an interval of length \(2A\). The number of admissible \(B\)'s is at most the number of roots modulo \(4A\), hence \(O(2^{\omega(A)}\sqrt{\gcd(A,|\Delta|)})\) by the same prime-power count, absorbing the extra dyadic factor into the absolute constant. Use the order class-number bound \(h(\Delta)\gg\sqrt{|\Delta|}/\operatorname{poly}(\log |\Delta|)\) and the genus-index bound \(2^{\omega(|\Delta|)+O(1)}\). Taking \(m=|\Delta|/N\) now gives (2) and the same multiplier absorption. These statements apply to uniform square classes and this specific norm-based, representative-independent root. A sampler that deliberately uses the representative in the public row has a different conditional sign question.

## Cutting off the seed ideals before squaring

There is a way to bias the class law without a long rejection loop: apply the direct factored proposal with an upper bound \(X\) on the canonical seed norm \(t\), before squaring. Its equal weights persist. The original hidden-sign proof needs uniform relative signs conditional on the *resulting square class*. On balanced squarefree semiprimes this property fails on almost all of the truncated seeds for any fixed polynomial improvement in \(X\).

More precisely, let \(N=pq\equiv1\bmod4\) for distinct odd primes with \(p\asymp q\), so the order of discriminant \(-4N\) is maximal. Let \(S_X\) be its canonical primitive ideals of norm at most \(X=N^\sigma\), coprime to \(N\), with fixed \(0<\sigma<1/2\). Call a seed conflicting if its reduced square has unit leading coefficient, and some other seed in \(S_X\) with the same square class has a different root modulo global sign. Under Dirichlet GRH the fraction of conflicting seeds in \(S_X\) is at most
\[
             (X/\sqrt N)N^{o(1)} .
\]
In particular it stays negligible after a public acceptance event of probability \(\exp(-O(H))\), provided that comparison still conditions on the full reduced square class. This is an upper bound on the *mass* of the conflicting fibers.

Indeed a conflicting pair \(I,I'\) supplies an integral ideal \(I\bar I'\) of norm at most \(X^2\) in one of just two classes: the class of \(J_p=(p,\pi)\) and its translate by the ramified dyadic class. The two possibilities follow from the kernel and sign computation for fundamental discriminants. Their integral norm forms, up to conjugation, are
\[
             p x^2+q y^2,\qquad
             \tfrac12\bigl(p(2x+y)^2+q y^2\bigr).
\]
For the second formula use the ideal \(J_p\mathfrak p_2=(2p,p+\pi)\) of norm \(2p\). Both forms have minimum \(\gg\sqrt N\), and both give at most \(O(1+X^2/\sqrt N)\) lattice points with norm at most \(X^2\), by bounding the two displayed integer coordinates. Every integral ideal in the given class occurs from a norm-form vector, including imprimitive ideals. For each resulting ideal of norm \(m\), the number of factorizations as an ordered pair of integral ideals is bounded by \(\tau(m)^2=N^{o(1)}\) by unique prime-ideal factorization. Conjugating the second factor recovers the original seed. There are no pairs below the minimum; above it the additive one is absorbed. Finally, the split primes in \([X/2,X]\) give \(\gg X/\log X\) canonical seeds by the Dirichlet GRH prime estimate. Their centered forms are strictly reduced since \(X^2<N\). Dividing the pair count by this seed count gives the assertion. [The two sign classes](keybreak-reduced-form-root-signs.md#fundamental-discriminant-and-the-global-sign)

The public descent actually reveals just \(A\), so this does not exclude using collisions between *different* reduced square forms with the same leading coefficient. This distinction already matters for \(N=101\cdot109=11009\), with seed norm cutoff 41. The seed forms \([23,\pm20,483]\) and \([25,\pm8,441]\) give leading coefficient 21. The first pair has root 3351 up to sign and the second pair has root 2644 up to sign. Each full reduced square form in this example admits just one relative sign among the truncated seeds. Directly, \(3351^2\equiv2644^2\equiv21\bmod11009\) and \(\gcd(3351-2644,11009)=101\). [Integer squaring and reduction](../experiments/keybreak-quadratic-class-roots.py)

A smaller range also constrains the law after revealing only \(A\). For the primitive square norm \(a=q_0^2\), the exact identity gives \(q_0^2 A=(q_0^2 x+b y)^2+Ny^2\). If \(y\ne0\) then \(q_0^2 A\ge N\). If \(y=0\) then the unimodular first column gives \(x=\pm1\); the output is \(A=q_0^2\) with global root \(\pm q_0\). Whenever \(q_0^4<N\) the centered initial square form is already reduced, since its trailing coefficient is strictly greater than \(q_0^2\). In particular, cutting every seed below \(N^{1/4}\) makes all the roots globally predictable from their leading coefficients. The intermediate range \(N^{1/4}<X<N^{1/2}\) still permits the coarse collisions illustrated above. [Lean norm and small-seed root bounds](../formal/cogentic/Cogentic/RandomizedReducedFormRoot.lean)
