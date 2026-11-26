# Exact relations on the four smooth marks

The four fixed marks in the [separating power-order construction](cogentic-separating-power-order-units.md) have an exact unit lattice of rank one in each field. Passing to the compositum preserves just the two separate unit directions, even if rational scalar factors are admitted. The common modular reduction identifies those two directions. Its resulting relation holds identically as a rational function of the common argument and supplies no order multiple for the surviving unit.

## The four-mark valuation lattice

Write \(E=\{1,2,13,14\}\), \(A(X)=(X-1)(X-2)\), \(C(X)=(X-13)(X-14)\), and \(W=AC\). Let \(F=WG-W'\) be one of the monic irreducible charts of odd degree, and let \(\theta\) be a root. In the order on \(E\) shown, the absolute norms of the four \(\theta-e\) are \(156,132,132,156\). Put \(\mathbf u=(1,1,-1,-1)\). The order identity for \(A(\theta)/C(\theta)\) already proves that \(\mathbf u\) gives a unit. [Power-order inverse identity](cogentic-quintic-unit-target-two.md#the-power-order-identity)

For the converse, take a prime of the maximal order above a root of the reduction of \(F\). Lying-over from the power order supplies such a prime also when the rational prime divides the power-order index. If exactly two marks reduce to this root, they both have positive valuation and all other marks are units there. The two positive valuations are equal. [Lying-over](https://stacks.math.columbia.edu/tag/00GQ)

Indeed
\[
                         G(\theta)=\sum_{e\in E}\frac{1}{\theta-e}
\]
is integral, so a unique largest positive valuation among the \(\theta-e\) would give a unique negative minimum in the sum.

At 11 the colliding pair is \((2,13)\), and at 13 it is \((1,14)\). In each case the collision residue is a simple root of \(\bar F\): locally \(W\) has a double zero and \(W'\) has a simple zero with nonzero leading coefficient. Also no other mark residue is a root of \(\bar F\), since its value there is the nonzero derivative term. The remaining positive-degree factor of \(\bar F\) therefore supplies a prime where all four marks are units. At 3 there are two collision roots with pairs \((1,13)\) and \((2,14)\).

In fact, suppose \(s\prod_{e\in E}(\theta-e)^{v_e}\) is a unit for some \(s\in\mathbb Q^\times\). The all-unit primes at 11 and 13 imply \(\nu_{11}(s)=\nu_{13}(s)=0\), where \(\nu_\ell\) is the rational valuation at \(\ell\). The collision primes at those two rational primes then give \(v_2+v_{13}=v_1+v_{14}=0\). At 3 the two collision primes have mark exponent sums \(v_1+v_{13}\) and \(v_2+v_{14}\), which now are opposites. A nonzero additive valuation of the same rational \(s\) has the same sign at both primes above 3. Since the common valuation of each colliding pair is positive, cancellation forces both exponent sums to vanish. Hence \(\mathbf v\in\mathbb Z\mathbf u\). The marked part is already a unit, so \(s=\pm1\). This proves the unit lattice with or without rational scalars.

Taking just the smooth rational norms loses the two prime ideals over 3. For instance \(((\theta-1)/(\theta-14))^2\) has rational norm one for every chart. Its valuations at the two collision primes over 3 have opposite signs, so it is not an algebraic unit. The absolute-norm kernel has rank two, while the exact unit lattice has rank one.

## Combining the two fields

Let \(K_1,K_2\) be the two chart fields with coprime odd degrees \(d_1,d_2\), and put \(L=K_1K_2\). They are linearly disjoint. If \(sxy\) is a unit of \(L\), with \(s\) rational and \(x,y\) marked words in \(K_1,K_2\), taking the norm to \(K_1\) gives the unit
\[
                         s^{d_2} x^{d_2}\operatorname{Nm}_{K_2/\mathbb Q}(y).
\]
The preceding rational-scalar result in \(K_1\) forces the exponent vector of \(x\) into \(\mathbb Z\mathbf u\), since it is integral and its \(d_2\)-multiple is in that lattice. The same reasoning applies to \(y\). Thus the mixed unit lattice is precisely the direct sum of the two individual lattices, and rational scalars still contribute only \(\pm1\).

The two units \(U_1,U_2\) are independent even modulo algebraic torsion. Each is nontorsion, and a putative relation \(U_1^iU_2^j\) equal to a root of unity would give \(U_1^{2i}U_2^{2j}=1\), since \(L\) has odd degree. Then \(U_1^{2i}=U_2^{-2j}\) lies in the rational intersection of the fields and is a rational unit. Thus \(i=j=0\).

For square relations, observe that \(F\) has a real root in each of the five intervals cut out by the four marks. Its signs alternate at the marks, and its odd monic degree gives the opposite signs at the two outer ends. In a marked word times a rational number, adjacent embeddings from those intervals differ in sign exactly when the intervening mark has odd exponent. Consequently a square requires every mark exponent even. In the compositum, take norms of a square \(sxy\) to each field. The odd relative degrees force this same evenness separately for \(x\) and \(y\). After removing those explicit squares, the only remaining condition is that \(s\) be a rational square, since \(L\) has odd degree. In particular, \(W(\theta_1)W(\theta_2)\) has a square modular image but cannot yield an exact compositum square relation.

## The zero projected relation

At the common modular argument \(m\), the two copies of each marked factor have exactly the same unit reduction. One can localize at the marks to make every inverse available. On exponent vectors the projection therefore adds the two copies coordinatewise. The known congruence \(U_1/U_2\equiv1\bmod N\) has vector \((\mathbf u,-\mathbf u)\), which becomes zero under that projection. More strongly, its equation is
\[
       \frac{A(T)}{C(T)}\frac{C(T)}{A(T)}=1
\]
in the rational function field, before choosing any input or reduction. Exact algebraic multiplicative identities among the marked words also give no nonzero projected vector, by their unit lattice and the independence just proved. The ideal and square calculations therefore supply no annihilating exponent for the common residue \(A(m)/C(m)\). An extra order certificate or a genuinely new relation using other elements is still required.

For a finite check, the public [argument generator](../experiments/cogentic-elliptic-unit-arguments.py) with \(N=323\), degree 7, minimum height 10 bits and a partner gives two charts of degrees 7 and 11 at \(m=-2837/23\). The common residue is \(123\), with orders 4 at 17 and 9 at 19. The quotient relation still contributes zero to the shared exponent space. Running the separate smooth-multiplier test exposes 19 using its local odd order.
