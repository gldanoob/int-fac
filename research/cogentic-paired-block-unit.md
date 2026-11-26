# A unit from two blocks of smooth norms

For every sufficiently large odd composite \(N\), the construction below either returns a proper divisor or produces an irreducible monic number field with an explicit modular evaluation and an infinite-order unit. The unit is the quotient of two products of distinct marked elements. Every marked norm is explicitly factored into one-third-size primes. At every finite prime of the number field, including primes above the index of the defining order, the valuations of the two products agree. For blocks of length \(h\ge3\), this quotient generates **all** unit relations on the marks. The real embeddings also determine their full field-square kernel. [Construction and exact checks](../experiments/cogentic-paired-block-unit.py)

## Constructing the polynomial and its modular root

Choose a prime \(\ell=2h+1\ge5\). Put \(M=\operatorname{rad}(h!)\operatorname{lcm}(1,\ldots,h)\), and take \(D=M s\), where \(1\le s<\ell\) satisfies \(D\equiv h\bmod\ell\). Set
\[
 A(X)=\prod_{i=1}^h(X-i),\qquad C(X)=A(X-D),\qquad W=AC,\qquad
 F=WG-W'.
\]
Use \(G_0=X^{2h-1}\). The marks \(1,\ldots,h,D+1,\ldots,D+h\) give every nonzero residue modulo \(\ell\). Hence \(W\equiv X^{2h}-1\), \(W'\equiv-X^{2h-1}\) and \(WG_0-W'\equiv X^{4h-1}\pmod\ell\). If the constant coefficient is already divisible by \(\ell^2\), increase the constant of \(G_0\) by \(\ell\). Since \(W(0)\) is an \(\ell\)-unit, the new constant of \(F\) has valuation one.

Trial divide through \(\ell\). Take consecutive integers \(m>D+h\) starting at or above \(N^{1/(2h-1)}\). Take the gcd of each mark difference \(m-a\) with \(N\). A proper gcd ends the search. Within \(2h+1\) tries one obtains a factor or a unit value \(W(m)\), since any remaining prime divisor exceeds \(2h\) and \(W\) has at most \(2h\) roots there. Choose \(0\le r<N\) satisfying
\[
 \ell^2 W(m)r\equiv W'(m)-W(m)G_0(m)\pmod N.
\]
Write \(r=R(m)\) in base \(m\). There are at most \(2h-1\) digits. With \(G=G_0+\ell^2R\), \(F\) remains monic of degree \(4h-1\), Eisenstein at \(\ell\), and \(F(m)\equiv0\bmod N\).

Define \(K=\mathbb Q(\theta)\) for \(F(\theta)=0\). The norm of each \(\theta-a\) is \((-1)^{4h-1}F(a)\), of absolute value \(\prod_{b\ne a}|a-b|\). The factors are bounded by \(D+h\) and obtained from the within-block differences and the \(2h-1\) integers between \(D-h+1\) and \(D+h-1\). Thus enumerating or factoring the norms needs no factorization of large, unspecified algebraic norms.

## All finite valuations and the exact unit relation

The element under consideration is \(U=A(\theta)/C(\theta)\). At a prime ideal of the full ring of integers, \(G(\theta)\) is integral and satisfies
\[
                   G(\theta)=W'(\theta)/W(\theta)
                            =\sum_a 1/(\theta-a).
\]
If the maximum of the nonnegative valuations of \(\theta-a\) is positive, it must occur at least twice. Otherwise the sum would have negative valuation.

At a rational prime \(p\le h\), \(v_p(D)>v_p(i-j)\) for every distinct \(i,j\) in the first block. If \(\theta-i\) and \(\theta-D-i\) had unequal valuations, the larger would exceed the valuation of \(D\), while every other mark would be strictly farther away in the \(p\)-adic metric. This contradicts the maximum condition. Thus matched factors have equal valuations. For \(p>h\), each block is injective modulo \(p\). A given prime ideal can see at most one positive valuation in either block. The maximum condition again forces equality across the blocks. This proves \(U\in\mathcal O_K^\times\) for every \(G\) above. In particular the half-ideal of \(W(\theta)\) is the principal ideal \((A(\theta))\).

For the converse, fix \(i\ne j\). At the primes \(p\le h\), the positive cross difference \(D+j-i\) has the same valuations as \(j-i\). Since \(D+j-i>|j-i|\), some \(p>h\) divides the cross difference. The polynomial \(F\) has the root \(i\equiv D+j\bmod p\), since \(W\) has a double root there. A prime ideal of \(\mathcal O_K\) above \((p,\theta-i)\) exists by integrality. Only the two marks \(i,D+j\) contribute there and their positive valuations coincide. Every unit word with exponent lists \((c_i),(d_j)\) consequently satisfies \(c_i+d_j=0\) for every \(i\ne j\). For \(h\ge3\) these equations force all \(c_i\) equal and all \(d_j\) their negatives. The converse already follows from \(U\) being a unit.

There is also an exact distinction between the maximal order and the power order. For \(U\) to belong to \(\mathbb Z[\theta]\) one needs \(A\in(C,F)\) in \(\mathbb Z[X]\). Modulo \(C\), \(F\equiv-AC'\), so this is equivalent to \(C\mid A(1+Q C')\) for some integral \(Q\). The two block polynomials are relatively prime over \(\mathbb Q\) and \(C\) is monic. The condition is therefore exactly invertibility of \(C'\) in \(\mathbb Z[X]/C\), or \(|\operatorname{disc} C|=1\). The inverse unit has the corresponding test with \(A\). For \(h=2\) both discriminants are one. For \(h\ge3\) there are already two roots at even distance. Localizing the power order at the primes up to \(h-1\) suffices for \(U\) and its inverse, by Bézout with the respective discriminants.

## Signs, costs and what the unit yields modulo the input

At the ordered marks the signs of \(F(a)=-W'(a)\) alternate. The leftmost sign is positive and the rightmost is negative. The odd monic degree therefore gives real roots in both exterior intervals and between every consecutive pair of marks. Take a real embedding from each of those \(2h+1\) intervals. Between the rows from adjacent intervals exactly one marked linear factor changes sign. Consequently a word on the \(2h\) marks and \(-1\) can be a field square only when all its exponents are even. In particular \(U\) has both positive and negative real values, so it has infinite order and is a nonsquare. Its field norm is \((-1)^h\), by taking the ratio of the \(F(a)\) products at the two blocks and using reflection in their common midpoint.

The input receives the residue \(A(m)/C(m)\) through the localization of \(\mathbb Z[\theta]\) at \(C(\theta)\), which is allowed because \(C(m)\) is invertible. One can also require that this residue have order greater than a public \(J\) at every prime factor, unless a proper gcd is found. Trial divide through \(R_0=\max(\ell,\,2h+hJ(J+1)/2)\); for the remaining primes \(D\) is a unit since its prime divisors are at most \(2h\). At such a prime the rational function \(A/C\) is nonconstant: equality of the two monic polynomials would make the \(h\)-element root set translation-invariant under the nonzero shift \(D\). The zeros of \(W\) and of the nonzero polynomials \(A^k-C^k,\ 1\le k\le J\), exclude at most \(R_0\) residues per prime. Testing \(R_0+1\) consecutive \(m\) with gcds therefore gives a factor or one chart avoiding all these local orders. In this argument a zero at only some prime divisors already exposes a proper gcd.

Write \(L=\log N\), \(H=L^{1/3}(\log L)^{2/3}\), \(V=L^{2/3}(\log L)^{1/3}\). Choose \(h\asymp(L/\log L)^{1/3}\) by taking an odd prime of the corresponding size. The elementary Chebyshev bounds give \(\log D=O(h)\). With \(J\le\exp(O(H))\), the tests above take \(\exp(O(H))\) bit operations, \(\log m=O(L/h+h+\log(J+2))\), and the coefficient log height of \(F\) is \(O(h^2+L/h+\log(J+2))=O(V)\). All prime factors of the marked norms are at most \(\exp(O(h))\). The unit is explicit even for \(J=0\). On \(64507\) the degree-eleven fixture has unit residue \(28294\) and norm \(-1\). Sage checks integrality of both \(U\) and \(U^{-1}\) directly.

This gives a controllable algebraic unit and rules out further unit directions on these marks. The sign test shows why the construction alone supplies no odd-parity field-square relation. It also supplies no upper bound on the local order of the displayed residue that would split every input.
