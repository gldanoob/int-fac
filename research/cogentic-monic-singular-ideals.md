# Exact ideal parity at singular primes in the monic grid

All singular ideal rows can be handled deterministically in the same `exp(O(W))` bound as the bounded-grid parity computation. Use a local maximal order at each bounded rational prime and a quadratic extension to test the private cofactors above the bound. The private test uses tame overorders, Smith normal forms, gcds and exact integer square roots. It takes polynomial time in the explicit inputs for each mark and avoids factoring its composite residual. [Monic grid and parity kernel](cogentic-monic-large-primes.md) · [Mark-local simple-root criterion](cogentic-monic-index.md)

## Known rational primes

Let \(P\in\mathbb Z[X]\) be monic irreducible of degree \(d\), \(K=\mathbb Q(\alpha)\) for \(P(\alpha)=0\), and \(R=\mathbb Z[\alpha]\). The marks are \(\gamma=a-b\alpha\ne0\) with \(\gcd(a,b)=1\), \(|a|\le A\) and \(1\le b\le A\). Choose
\[
Y=\max(2A^2,2d_F,2d_G)
\]
for the degrees \(d_F,d_G\) of the two fields. For each known prime \(p\le Y\) dividing an eligible norm, Buchmann–Lenstra Algorithm 6.1 computes in deterministic polynomial time the \(p\)-maximal overorder \(B\supset R\) of \(p\)-power index. Compute it once per field and prime. [Buchmann–Lenstra, Algorithm 6.1 and Proposition 6.2](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/buchlen/to.pdf)

Reduce the multiplication table of \(B\) modulo \(p\). The kernel of the \(\mathbb F_p\)-linear map \(x\mapsto x^{p^t}\) for \(p^t\ge d\) is the nilradical. Quotienting by this kernel gives a product of finite fields. In that product the kernel of \(x\mapsto x^p-x\) is \(\mathbb F_p^r\), where \(r\) is the number of prime ideals above \(p\). Split its coordinates using the projectors \(1-(x-c)^{p-1}\), scanning \(c\in\mathbb F_p\) for each basis element \(x\) of the kernel. Taking successive common refinements yields the singleton idempotents because the basis separates distinct coordinates. The zero projection to each singleton field lifts to a prime ideal \(\mathfrak q\) of \(B\) above \(p\). This costs polynomial work in \(p\), \(d\) and the input bit lengths.

A prime ideal \(\mathfrak q\) above \(p\) is invertible in \(B\) because \(B\) is maximal at \(p\), and it localizes to the unit ideal at every other maximal ideal of \(B\). Hence \(\gamma\in\mathfrak q^j\) is exactly the condition that the corresponding normalized valuation in \(K\) is at least \(j\). Compute the powers and membership by integer lattice arithmetic in \(B\). Every exponent is at most \(v_p(|\operatorname N_{K/\mathbb Q}\gamma|)\), so the number of tests and the lattice bit lengths are polynomial in explicit bit sizes. This gives the individual exponents even when several ideals above the same root divide a mark.

## Private ideals and quadratic ramification

For \(p>Y\), a prime ideal dividing \(a-b\alpha\) cannot also divide a distinct primitive mark \(a'-b'\alpha\). Indeed, it would contain the nonzero integer \(ab'-a'b\) whose absolute value is at most \(2A^2\). This argument works in the maximal order at every prime, including singular primes. A column belongs to the joint ideal-parity kernel only if it has even valuations at all such ideals. In each field let \(m\) be the positive residual of its absolute norm after removing the entire bounded-prime part. The private test concerns exactly the primes above the rational prime divisors of \(m\). Return true if \(m=1\).

Form \(E=K(\sqrt\gamma)\) if \(\gamma\) is nonsquare in \(K\). A rational polynomial for this test and for \(E\) is \(Q(T^2)\), where \(Q(T)=(-b)^dP((a-T)/b)\) is the minimal polynomial of \(\gamma\). The polynomial \(Q(T^2)\) is monic with integer coefficients and has degree \(2d\). It is irreducible exactly when \([E:K]=2\) since \(K=\mathbb Q(\gamma)\). Test irreducibility by deterministic rational factorization. In the reducible case \(\gamma\) is a square and all its ideal valuations are even. [Deterministic rational factorization and the field-square test](cogentic-monic-square-extraction.md)

At an odd prime ideal \(\mathfrak p\) of \(K\), the extension \(E/K\) ramifies if and only if \(v_{\mathfrak p}(\gamma)\) is odd. Locally, remove the largest even power of a uniformizer from \(\gamma\). With an odd valuation the remaining quadratic is Eisenstein. With an even valuation the remaining quadratic is that of a unit, with separable reduction, and the local algebra is unramified or split. Thus the task is to decide whether \(E/K\) is unramified everywhere above \(m\).

For \(F=K,E\) and a rational prime \(p\mid m\), define the weighted sum
\[
S_F(p)=\sum_{\mathfrak P\mid p}
    \frac{[F_{\mathfrak P}:\mathbb Q_p]}{2^{v_2(e(\mathfrak P/p))}}.
\]
For each base prime \(\mathfrak p\mid p\), the degrees of the completions above \(\mathfrak p\) sum to \(2[K_{\mathfrak p}:\mathbb Q_p]\). Every exponent of 2 in an absolute ramification index upstairs is at least the corresponding one downstairs, with strict inequality for a ramified quadratic completion. Consequently \(S_E(p)\le 2S_K(p)\), with equality exactly when every ideal above \(p\) is unramified in \(E/K\). Equality also implies equality of the two weighted distributions of the 2-adic exponents, using weights \([E_{\mathfrak P}:\mathbb Q_p]\) upstairs and \(2[K_{\mathfrak p}:\mathbb Q_p]\) downstairs. Each upstairs exponent then equals its downstairs exponent.

## Computing the weighted sums over composite inputs

For each \(F=K,E\), run Buchmann–Lenstra Algorithm 6.6 on its given power order with input \(m\). It produces an overorder \(B\) in \(F\) and a set of pairwise coprime divisors \(q>1\) of \(m\) at which \(B\) is tame in their sense. At a prime \(p\mid m\) outside those divisors, \(F\) is unramified. In fact \(p>[F:\mathbb Q]\), so the proof of Theorem 6.7 places it in a successful call of Algorithm 6.3 with output \(q'=1\), to which Proposition 6.4(b) applies. [Buchmann–Lenstra, Algorithm 6.6, Proposition 6.4 and Theorem 6.7](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/buchlen/to.pdf)

For each returned \(q\), compute the ideal
\[
J=\{x\in B:\operatorname{Tr}_{F/\mathbb Q}(xB)\subset q\mathbb Z\}
\]
from its trace matrix. For \(j=1,\ldots,[F:\mathbb Q]\), compute the Smith invariants of the finite additive quotient \(B/(J^j+qB)\), retaining unit invariants to give \([F:\mathbb Q]\) entries. For \(p\mid q\), the local tame presentation is a product of blocks \(T[X]/(X^h-uq)\), with \(T\) unramified of degree \(f\) over \(\mathbb Z_p\), \(u\in T^*\), and \(p\nmid h\). In each block \(J\) is generated by the image of \(X\). Thus the local additive quotient for power \(j\) is free over \(\mathbb Z_p/q\mathbb Z_p\) of rank \(f\min(j,h)\), using the first \(\min(j,h)\) powers of \(X\). The number \(r_j\) of Smith invariants divisible by \(p\) is therefore \(\sum f\min(j,h)\). Taking successive differences with \(r_0=0\) yields \(\sum_{h\ge j}f\) and then the total \(f\) of the blocks of each size \(h\). [Buchmann–Lenstra, Section 3, especially Proposition 3.3(c)](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/buchlen/to.pdf)

Compute a gcd-free basis of \(m\), the returned \(q\)'s in both fields, and all the nonunit Smith invariants. This gives pairwise coprime integers \(c>1\) with every input an explicit product of powers of the \(c\)'s. One can maintain exponent vectors and replace overlapping distinct bases \(x,y\) by \(x/g,y/g,g\) for \(g=\gcd(x,y)\), dropping units and merging equal bases. The sum of the logarithms of the distinct bases decreases by at least \(\log 2\) at each step. All prime divisors of one basis integer \(c\) now have the same rank profile \((r_j)_j\) in each field, since each Smith invariant is divisible by either every prime of \(c\) or none. A returned \(q\) covering \(c\) has a known positive exponent \(s\) in its gcd-free representation, so \(v_p(q)=s\,v_p(c)\) for \(p\mid c\).

In a tame block \(T[X]/(X^h-uq)\), each field factor in characteristic zero has absolute ramification index \(h/\gcd(h,v_p(q))\). To see this, extend the unramified fraction field so that it contains the \(h\)th roots of unity and an \(h\)th root of the unit part of \(uq\). Such an unramified extension exists by separability modulo \(p\). The remaining roots are multiples of \(p^{v_p(q)/h}\), and each generates an extension of ramification index equal to the reduced denominator of this exponent. This follows from its valuation and the Eisenstein polynomial for a root of \(p\) of that denominator. Unramified base change preserves the ramification indices. All factors from the block therefore share the same 2-adic exponent, and their degrees sum to \(hf\).

For a basis integer \(c\), write \(z=v_2(v_p(c))\). A block of size \(h\) contributes weight \(hf\) at exponent
\[
  \max(0,v_2(h)-v_2(s)-z).
\]
The computed rank profiles give all these weights, so the weighted sums are explicit functions of \(z\). If a field has no returned \(q\) covering \(c\), put its entire degree at exponent zero. It suffices to evaluate both functions at
\[
 z_0=\min_{p\mid c}v_2(v_p(c)).
\]
The value \(z_0\) is the number of successive exact integer square roots that can be taken from \(c\), because \(c\) is a \(2^z\)-th power exactly when all its prime exponents are divisible by \(2^z\). There is at least one actual prime attaining \(z_0\). If the sums there are unequal, that prime witnesses failure. If they are equal, the preceding ramification argument gives equal weighted exponent distributions there, with the downstairs weights doubled. For every larger \(z\), replace each exponent \(x\) in both distributions by \(\max(0,x-(z-z_0))\). Equality of the weighted distributions persists, so all primes dividing \(c\) pass. Test each basis integer in this way.

## Kernel and cost

For each field and mark, record the exact ideal parities for \(p\le Y\). Discard a column if either field fails the composite private test. Every discarded column has an odd private row, and every kept column has only even private rows. Binary elimination on the bounded rows, extended by zeros on the discarded columns, therefore gives the full joint ideal-parity kernel of the primitive unit grid. No discriminant-prime exclusion is needed.

For \(L=\log N\) and \(W=L^{1/3}(\log L)^{2/3}\), the degrees, explicit power orders, norm bit lengths, and auxiliary quadratic defining polynomial bit lengths are polynomial in \(L\) for the [growing-degree pair](cogentic-monic-pair.md) at \(A\le\exp(O(W))\). Buchmann–Lenstra bounds the overorder computation by a polynomial in the input size. Subsequent trace, integer lattice and Smith computations also have polynomial size and bit cost. In particular the lattices for \(J^j+qB\) lie between \(qB\) and \(B\) and can be reduced after each multiplication. Bounded prime enumeration, bounded row computations, and binary elimination cost polynomial work in \(Y\), the grid size and the bit lengths. The private computations take polynomial work per mark in the explicit bit lengths. The total deterministic bit cost is \(\exp(O(W))\). This bound recovers the ideal-parity kernel. The condition of being a square in both fields, and finding a square dependency that yields a proper modular gcd, require further arguments.

## Finite ramification check

Take \(K=\mathbb Q(i)\), \(q=(11\cdot19^2)^{2^j}\) and \(\gamma=qi\). This is the mark \((0,1)\) for a generator of \(T^2+q^2\) with the opposite sign. Its norm \(q^2\) is always a square. At both odd support primes, \(K\) is unramified of degree two, and adjoining \(\sqrt\gamma\) gives the tame model with block size two over \(\mathbb Z_p[i]\). The weighted sum upstairs is \(4/2^{\max(0,1-v_2(v_p(q)))}\). At \(j=0\), the valuation is one above 11 and two above 19, so the test rejects. For \(j=1,2\) the test accepts. The replay verifies the formula and parity decisions against PARI's prime ideal decompositions and valuations. It uses the explicit tame models for this family. [PARI replay](../experiments/cogentic-monic-singular-ideals.gp)
