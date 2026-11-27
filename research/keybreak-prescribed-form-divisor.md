# Prescribed split divisors in a binary quadratic form

Restricting a form to an index-\(M\) split sublattice and dividing its values by \(M\) translates the proper ideal class. A fixed translation preserves the uniform law on a coset of the square subgroup, so it preserves the half-width lower bound for uniform class sampling. An adaptive divisor can narrow the output. Conjugate cancellation gives a principal form, and removing the square part of a factored public leading coefficient preserves the private root signs. The latter has a sharp width-tail estimate and still gives polynomially rare outputs at any fixed exponent below one half. [Uniform reduced-class width bound](keybreak-reduced-class-width-floor.md) · [Conditional root signs](keybreak-reduced-form-root-signs.md)

## Which class is translated

Put \(\pi=\sqrt{-N}\) and \(\mathcal O=\mathbb Z[\pi]\). For the primitive positive form \(f=[A,2b,C]\) with \(AC-b^2=N\), use the oriented norm basis of the proper invertible ideal \(I=(A,b+\pi)\). Thus
\[
f(x,y)=\frac{\operatorname{Nm}(Ax+(b+\pi)y)}{A}.
\]
Let \(M\) be a factored positive integer prime to \(2N\) whose prime factors are split in the order. Choosing one orientation at every prime gives \(P=(M,\pi-r)\), where \(r^2\equiv-N\pmod M\) specifies the simple local roots at the full prime-power moduli. Its norm is \(M\). The lattice to restrict to is \(IP\subseteq I\), which has index \(M\) by multiplicativity of norms of invertible ideals. If \(S\) is an oriented integer basis matrix for this sublattice in the given basis of \(I\), the divided form is
\[
f_P(X,Y)=\frac{f(S(X,Y))}{M}=
\frac{\operatorname{Nm}(\beta_1 X+\beta_2 Y)}{\operatorname{Nm}(IP)},
\]
where \((\beta_1,\beta_2)\) is the resulting basis of \(IP\). Its discriminant is \(-4N\), since the basis change multiplies discriminant by \((\det S)^2=M^2\) and value division cancels that factor. It is primitive. Locally an invertible ideal has one generator, and the normalized norm in such a basis is a unit times the order's norm form. In the norm-basis convention here the new class label is \([I][P]\). The integral ideal of norm \(f_P(X,Y)\) associated to the vector is \((\beta_1 X+\beta_2 Y)(IP)^{-1}\), whose class is the inverse. This accounts for the sign difference if the form is indexed instead by the class of the ideals whose norms it represents. [Cox, Theorem 7.7 and norm multiplicativity for proper ideals](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf#page=137)

When \((A,M)=1\), the restriction can be computed by the scalar congruence \(Ax+(b+r)y\equiv0\pmod M\). For \(s\equiv-(b+r)A^{-1}\pmod M\), use \((x,y)=(MX+sY,Y)\) to get
\[
f_P=\left[AM,\ 2(As+b),\ \frac{As^2+2bs+C}{M}\right].
\]
For primes shared by \(A\) and \(M\), compute \(IP\) using the four basis products and integer Hermite normal form. The scalar congruence describes \(I\cap P\) in that case, whereas the required index and class use \(IP\). The product and Gauss reduction use polynomial bit work when the defining integers have polynomial bit length.

The index condition also classifies split restrictions with a noncyclic quotient. At \(p^e\Vert M\), identify the local ideal with \(\mathbb Z_p^2\) in split coordinates, where its normalized norm is a unit times \(xy\). Let \(\alpha,\beta\) be the minimum valuations in the two coordinate projections of the sublattice. After dividing the coordinates by those powers, their reductions span a subspace with both projections nonzero, so some lattice vector attains both minima. Hence divisibility by \(p^e\) throughout the sublattice implies \(\alpha+\beta\ge e\). Containment in \(p^\alpha\mathbb Z_p\times p^\beta\mathbb Z_p\) gives the opposite inequality from the index. Equality forces exactly this Cartesian lattice. Globally the sublattice is therefore \(IP\) with local divisors \(\mathfrak p^\alpha\overline{\mathfrak p}^{\,\beta}\), \(\alpha+\beta=e\). A cyclic quotient uses a single orientation per prime. If both are used, their overlap is a principal factor, since \(\mathfrak p\overline{\mathfrak p}=p\mathcal O\). [Split ideal factorizations away from the conductor, Cox Proposition 7.19](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf)

## Width under predetermined choices

Write \(G=\operatorname{Pic}(\mathcal O)\), and let \(\lambda(g)\) be the minimum positive value of a primitive form of class \(g\) in the convention above. The leading coefficient of the reduced representative equals \(\lambda(g)\). For \([I]\) uniform on \(G^2\), any fixed \([P]\) gives a uniform class on \([P]G^2\). On the rough branch under Dirichlet GRH, the width count in every such coset gives
\[
\Pr\bigl(\lambda([I][P])\le X\bigr)
\le \min\left(1,\frac{X}{\sqrt N}\exp(o(H))\right),\qquad 1\le X\le\sqrt N.
\]
Here the numerator counts all reduced forms of leading coefficient at most \(X\), including other genera. The denominator is \(h(-4N)/[G:G^2]\), and the rough branch makes the genus and ramified losses \(e^{o(H)}\). Choosing a translation after inspecting the input can multiply the bound by the size of a menu fixed before that input draw. For each fixed \(M\), the number of cyclic orientations is \(2^{\omega(M)}\). Even allowing noncyclic split lattices gives at most \(\tau(M)\) choices, which is \(N^{o(1)}\) uniformly for \(M\le N^{O(1)}\). Thus a subpolynomial menu of such moduli and orientations preserves the polynomial deficit for \(X=N^\theta\) with fixed \(\theta<1/2\). For a menu of size \(e^{o(H)}\), it also preserves the leading tail exponent at \(X=\sqrt N\,e^{-cH}\). The lower tail and the universal Gauss bound put the smallest output from such a subpolynomial menu at width \(N^{1/2-o(1)}\) in probability. A pointwise comparison with the uniform law contributes its domination factor. A total variation approximation of the input law adds its error once to the probability of the union over the menu. [Coset width bound and measure comparison](keybreak-reduced-class-width-floor.md)

There is a necessary bound even for a wholly adaptive choice with \(M\le Y\). A quotient at most \(X\) comes from an original represented value at most \(MX\), so the original class must have \(\lambda([I])\le YX\). In particular a constant success probability at width \(N^\theta\) requires \(Y\ge N^{1/2-\theta-o(1)}\) in the uniform square model. This bound concerns the magnitude of an adaptive divisor and does not require a bound on the number of its possible values.

## Adaptive cancellation and root transport

With an odd factored primitive \(I\) prime to \(2N\), take \(P=\overline I\), of norm \(M=A\). Then \(IP=A\mathcal O\). In coordinates, the restriction is \(y\equiv0\pmod A\), and \(f(X,AY)/A=(X+bY)^2+NY^2\). Thus adaptive cancellation reaches width one. When the original ideal is the square of a factored odd primitive seed \(J\), its unreduced norm is already factored and one can take \(P=\overline J^{,2}\) in the same construction. This cancels the private seed as well, since the translated seed is \(J\overline J\), principal for every original seed.

For a sign-preserving variant, suppose the reduced form \(f\) is public and \(z^2\equiv A\pmod N\) is its private unit root, uniform on its root fiber conditional on the form. If a public choice of \((M,x,y)\) yields \(f(x,y)=Mu\) and a public unit \(w\) satisfies \(w^2\equiv M\pmod N\), then
\[
z'=\frac{Ax+by}{zw}\pmod N,
\qquad (z')^2\equiv u\pmod N.
\]
This follows from \(Af(x,y)=(Ax+by)^2+Ny^2\). For unit \(u\), this map bijects the two root fibers, so the original uniform signs are preserved conditional on all these public choices. In full cancellation \(M=A\), using the private \(z\) as the divisor root instead gives a deterministic sign. An independently available public root of the same \(A\) would already provide the comparison of two roots. At the ideal level, a public square ideal \(P=W^2\) similarly takes each seed class to \([J][W]\), a bijection of the two-torsion fibers when \(W\) is fixed conditional on the original squared class. [Root signs conditional on the reduced class](keybreak-reduced-form-root-signs.md)

## Square stripping is adaptive and its gain is limited

Suppose the public reduced leading coefficient \(A\) is a unit modulo \(N\). For an odd square divisor \(d^2\mid A\) with known factorization, remove the corresponding oriented prime powers of the leading ideal by taking \(P\) to be their conjugate. Then \(I=d_I J'\) for that oriented divisor \(d_I\) of norm \(d^2\), and \(IP=(d^2)J'\). The normalized form has the class of \(J'\), of norm \(A/d^2\). For \(d>1\), the latter is below \(\sqrt N\). Since \(J'\) remains primitive, its centered norm form is already reduced, so this is the exact quotient width. The public divisor root is simply \(d\). This stripping requires only the chosen square divisor and its orientation, which is read from the public middle coefficient.

Write \(U=\lfloor2\sqrt{N/3}\rfloor\). The number of classes with unit \(A\le U\) for which stripping can give width at most \(X\) is bounded above by the count of \(A=d^2a\) with \(a\le X\), \(d\le\sqrt{U/a}\), and with at most \(2\cdot2^{\omega(A)}\) roots per norm. Using \(2^{\omega(d^2a)}\le2^{\omega(d)}2^{\omega(a)}\), the squarefree-divisor sum \(\sum_{m\le Y}2^{\omega(m)}\le Y(1+\log Y)\), and partial summation gives
\[
\#\{\text{eligible classes}\}
\ll \sqrt U(1+\log U)\sum_{a\le X}\frac{2^{\omega(a)}}{\sqrt a}
\ll \sqrt{UX}(1+\log U)^2.
\]
Dividing by the square subgroup size gives at most \(\sqrt{X/\sqrt N}\,e^{o(H)}\) in the rough-input model. This includes choosing among all eligible square divisors from the full factorization, and reducedness gives the same conclusion if the output is reduced again. [Unit leading-coefficient root count](keybreak-direct-reduced-class-sampler.md#the-missing-fraction)

The square-root improvement in this width tail is attained to subleading factors. For fixed \(0<\theta<1/2\) and \(X=N^\theta\), or for \(X=\sqrt N e^{-cH}\) with fixed \(c>0\), take split primes \(p\in[P,2P]\) with \(P=\sqrt{\sqrt N/(16X)}\), and principal-genus split primes \(q\in[X/2,X]\). With \(p\ne q\), the ideals of norm \(A=p^2q\le\sqrt N/4\) obtained by choosing one orientation at each prime are primitive and in the square subgroup. Their centered forms are reduced, and their distinct norms give distinct classes. Removing \(p^2\) gives width \(q\le X\). Dirichlet GRH gives \(\gg P/\log P\) choices for \(p\). The principal-genus count gives \(\gg X/([G:G^2]\log X)\) choices for \(q\), as the dyad for \(q\) is polynomial in \(N\). Even if the prime intervals overlap, omitting \(p=q\) removes a negligible fraction. Accounting for the class number gives probability at least \(\sqrt{X/\sqrt N}/(\log N)^{O(1)}\). [Dirichlet genus counting](keybreak-reduced-form-smooth-supply.md#genus-as-a-finite-dirichlet-condition)

At the \(H\)-scale target, \(p=e^{(c/2+o(1))H}\) is the least prime of \(A=p^2q\). The existing bounded elliptic recognition argument finds it with high probability in \(e^{o(H)}\) work per trial after discarding its negligible exceptional prime set. Its factorization is tested and the square-divisor identity is verified. The direct sampler's \(e^{-\omega(H)}\) error is negligible relative to the target probability at this scale. Thus repeated square samples with partial recognition realize width \(\sqrt N e^{-cH}\) in expected \(e^{(c/2+o(1))H}\) work and retain the root signs. Rejection on the original width has exponent \(c\). This adaptive gain changes the width by a factor on the \(H\) scale and leaves the leading height \((1/2)\log N\) in the smoothness ledger. At fixed \(\theta<1/2\), the matching probability for the exact uniform law is still polynomially small even with the divisor supplied. [Bounded recognition for eligible least primes](keybreak-private-elliptic-recognition.md#transfer-to-the-private-coordinate-procedure) · [Direct sampler](keybreak-direct-reduced-class-sampler.md)

Another public choice, available with factored odd \(A\), is \(P=I^{2k}\) with \(M=A^{2k}\). It sends \(g=[I]\) to \(g^{2k+1}\) and uses the known root \(A^k\). For a fixed odd exponent \(m=2k+1\), the output of a uniform square class is uniform on the image of the power map, so its short-width probability is at most the uniform bound times \(|\ker(m:G^2\to G^2)|\). This identifies a different possible source of narrowing through class-order information. Large adaptive power moduli and discovering an exponent with a large kernel would need their own computation and cost proof. [Class-order information and quadratic class walks](class-group-walks.md)

An exact check compared the product-ideal norm form with independent PARI/GP composition and reduction in 344 cases, including 72 cases where \(M\) and \(A\) overlap. The check included nonmaximal orders and split prime powers.
