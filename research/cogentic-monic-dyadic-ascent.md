# Dyadic digit ascent for square roots in Eisenstein fields

An explicit product of marks in a monic Eisenstein field can be tested and, when square, recovered by binary digit lifting and bounded coefficient reconstruction. The calculation uses polynomial bit complexity and requires no factorization of either the defining polynomial over a finite field or the square algebra over \(\mathbb Q\). For factoring \(N\), the resulting candidates need only pass the two modular square checks and a proper gcd test. The two even marks in the [Pell family](cogentic-parametric-square-split.md) also give an obstruction to using their dyadic classes alone.

## Exact digit rules

Let \(P\in\mathbb Z[X]\) be monic Eisenstein at two, of degree \(d\ge2\), and write \(\pi\) for its root in the completion at two. There is one prime above two, with \(v_\pi(2)=d\), \(v_\pi(\pi)=1\), and residue field \(\mathbb F_2\). These follow from the [ramified row calculation](cogentic-monic-ramified-two.md). For coefficients \(c_i\in\mathbb Q_2\), the nonzero terms in \(\sum_{i<d}c_i\pi^i\) have distinct valuations modulo \(d\), so
\[
 v_\pi\!\left(\sum_{i<d}c_i\pi^i\right)
   =\min_{i<d}\bigl(d\,v_2(c_i)+i\bigr).
\]
In particular the local maximal order is \(\mathbb Z_2[\pi]\), and valuations of rational power-basis polynomials can be computed directly.

Given a signed integral mark product \(S\ne0\) in the quotient by \(P\), reject an odd valuation. Otherwise write \(v_\pi(S)=2s\) and set \(T=S/\pi^{2s}\). This is a local unit. Its rational coefficients can be computed by monic reduction using
\[
 \pi^{-1}=-\bigl(\pi^{d-1}+P_{d-1}\pi^{d-2}+\cdots+P_1\bigr)/P_0 .
\]
In particular the coefficients of \(T\) in reduced form are 2-adic integers. For a mark product, \(2s\) simply counts the even numerators among its primitive marks.

Start a root candidate \(r=1\) modulo \(\pi\). At step \(k\ge1\), with \(r\) specified modulo \(\pi^k\), write \(E=T-r^2\) and use the following rule.

| Step | Required valuation of \(E\) | Digit multiplying \(\pi^k\) |
| --- | ---: | --- |
| \(k<d\) | at least \(2k\) | one exactly when \(v_\pi(E)=2k\) |
| \(k=d\) | at least \(2d+1\) | zero |
| \(k>d\) | at least \(k+d\) | one exactly when \(v_\pi(E)=k+d\) |

Each digit is added to \(r\). For \(k<d\), the increment in the square of \(r\) after adding a term of valuation \(k\) first occurs at \(2k\), from the square of that term. For \(k>d\), it first occurs at \(k+d\), from the cross term. The residue field has two elements, so matching that leading digit gives the rule. At \(k=d\), the two leading terms cancel in \(\mathbb F_2\) for any increment of valuation \(d\). A root must already satisfy the stronger residual requirement. The two signs of a root differ by \(2r\), of valuation \(d\), so if a root exists then one sign agrees with the choice of digit zero. If this step passes, the rule for \(k>d\) inductively produces a compatible sequence, since each correction raises the residual valuation to at least \(k+d+1\). Completeness gives a local square root. Thus the first \(d\) steps decide the local square test and the later steps lift the selected sign one digit at a time.

To obtain the selected square root of \(S\) modulo \(2^J\), take \(J\ge2\), lift \(T\) to \(\pi^{dJ}\), and multiply by \(\pi^s\). Congruence modulo \(\pi^{dJ}\) is coefficientwise modulo \(2^J\) in the power basis. Polynomial multiplication and valuation calculations suffice for every step. The rational coefficients have polynomial bit length in the explicit input size and \(J\). For example, the powers of \(\pi\) are obtained by \(O(dJ+s)\) multiplications by \(X\) followed by monic reduction, and computing \(T\) requires \(2s\) multiplications by the displayed inverse. After normalization all coefficients can be reduced modulo \(2^{J+1}\), since every residual threshold examined is below \(d(J+1)\).

## Recovering an integral numerator

If \(S\) is a square in the global field, write one root as \(\beta\). It is integral because \(S\) is integral. There is a degree-\(<d\) integer polynomial \(C\) with \(C(\pi)=P'(\pi)\beta\). In fact, for roots \(\pi_i\) of \(P\) and the corresponding conjugates \(\beta_i\),
\[
 C(X)=\sum_{i=1}^d \beta_i\prod_{j\ne i}(X-\pi_j).
\]
Each coefficient is an algebraic integer fixed by all automorphisms of the normal closure, hence is an ordinary integer. Set \(R=1+\|P\|_\infty\), write \(S=\sum_i S_i X^i\bmod P\), and take
\[
 B=d\max\!\left(1,\sum_i |S_i|R^i\right)(1+R)^{d-1}.
\]
The root bound \(|\pi_i|\le R\) gives \(|\beta_i|\le\max(1,\sum_i |S_i|R^i)\), and the coefficient 1-norm of each product in the interpolation formula is at most \((1+R)^{d-1}\). Thus all coefficients of \(C\) have magnitude at most \(B\).

With \(J\ge2\) and \(2^J>2B\), multiply the lifted dyadic root by \(P'\) in the quotient. Take the balanced integer representative in each coefficient. If a global root exists, its image in the completion is one of the two dyadic signs, so the reconstructed polynomial is exactly \(C\) or \(-C\). The test \(C^2\equiv(P')^2S\pmod P\) decides global squareness and verifies the recovered root. The precision \(J\) is polynomial in the bit lengths of \(P\) and the reduced \(S\). This is an alternative to the [square-algebra calculation](cogentic-monic-square-extraction.md) for the Eisenstein pair.

Suppose the two fields share the evaluation argument \(m\bmod N\) and their derivatives at \(m\) are units modulo the odd \(N\), as in the repaired or planted pair. For each reconstructed numerator evaluate \(z_i=C_i(m)/P_i'(m)\bmod N\). For a split alone, check directly that both \(z_i^2\) equal the same signed mark value \(S(m)\) and take \(\gcd(z_1-z_2,N)\). A proper gcd certifies a factor even if neither reconstruction was checked in the global field. Equivalently, the two verified roots give two linear factorizations of \(Y^2-S(m)\bmod N\). The method recovers both roots whenever a supplied product really is a square in both fields. To skip reconstructing the individual coefficients, increase the precision to \(2^J>2B\sum_{j<d}|m|^j\) and take the single balanced representative of the dyadic numerator evaluated at \(m\). This recovers the integer \(C(m)\) for the selected sign under the same square hypothesis, with only polynomial additional precision. A local square condition by itself supplies neither a global root nor a proper modular gcd.

## Two structured local false positives

In the Pell construction write \(m=1+c^2n^2\), \(w^2=1+2n^2\), and \(L=1+2n^2(X+1-m)\). The product of its two even marks is
\[
 A=(2cn-X)(-2cn-X)=X^2-4c^2n^2 .
\]
Over the quadratic field, \(A=(w\pi)^2\). Over the cubic field, \(A=\pi^2L(\pi)\) by the polynomial identity in the construction. Since \(n\) is even, \(L(\pi)\equiv1\pmod{8\mathbb Z_2[\pi]}\), and the digit test accepts it. Indeed its difference from one has valuation at least \(3d\), which passes all steps through \(k=d\) starting from \(r=1\). Yet the cubic has a root \(x_0\in(0,1)\), since \(G(0)=2c^2>0\) and \(G(1)=1-c^2(n^2-2)<0\). At this embedding \(L(x_0)<0\), so \(A\) is no global cubic square. The negative orientation is excluded in the quadratic since its square root would generate the real field \(\mathbb Q(\sqrt2)\). Multiplying by the third Pell factor with the prescribed sign gives the full global square identity.

The planted pair gives the same obstruction inside the full common ideal-parity kernel. Take at least nine cuts and the [derivative bump](cogentic-planted-unit-signatures.md), so the cuts 0 and 16 occur and their real signatures are separated. Put \(a_0=-\pi\) and \(a_{16}=16-\pi\). Both have norm 2 in either field, so their product has even ideal valuations. Locally
\[
 a_0a_{16}=a_0^2(1+16/a_0),\qquad
 v_\pi(16/a_0)=4d-1\ge3d .
\]
Therefore it is a dyadic square in each field. In the real embedding just to the right of cut 0 the two factors have opposite signs, so the positive signed product cannot be a field square. In the real embedding just to the right of cut 16 the product is positive, which also excludes the negative signed product. This obstruction holds on every surviving planted input with those cuts. It leaves open how to find productive candidates uniformly in the full-grid kernel.

A finite implementation of the digit rules recovered the two roots and proper gcds on three Pell fixtures, including the second Pell solution, and recovered the integral-square fixture with power-basis denominator 15. It matched complete modulo-eight enumeration on 200 quadratic and cubic unit cases. The cuts 0 and 16 passed the local test in degrees 27 and 28 at the planted composite \(14063084466772621680157\).
