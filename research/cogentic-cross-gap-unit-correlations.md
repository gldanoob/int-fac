# Cross-gap correlations of elliptic unit values

Take two elliptic twists built from translated consecutive pairs with distinct gaps. The relation that a positive power of one marked unit agrees with a positive power of the other has geometric components of genus at least five. For equality of the unpowered units, the two signed components both have genus exactly five. This rules out planting a varying exact comparison on a rational or elliptic parameter curve with fixed gaps and twists. A mixed-sign modular comparison can still split an input, as the degree-five and degree-seven charts at 221 show. [Consecutive-pair order units](cogentic-quintic-unit-target-two.md) · [Same-mark elliptic comparisons](cogentic-elliptic-unit-collisions.md)

## The signed root cover

For an integer gap \(d\ge2\) put
\[
 A(X)=X(X-1),\qquad C_d(X)=(X-d)(X-d-1),\qquad W_d=AC_d.
\]
For a nonzero rational \(\delta\), let \(E_{d,\delta}\) be the smooth projective curve of \(\delta y^2=W_d(x)\). At finite points away from the marks, set \(u_d=A/C_d\) and \(s_d=y/C_d\), so \(u_d=\delta s_d^2\). Over an algebraic closure choose \(r_d=\sqrt\delta\,s_d\). The equation for \(x\) over the \(r_d\)-line is
\[
 (1-r_d^2)x^2+\big((2d+1)r_d^2-1\big)x-d(d+1)r_d^2=0.
\]
Its discriminant is \(D_d(r_d^2)\), where
\[
                    D_d(z)=z^2+(4d^2-2)z+1 .
\]
The elliptic function field is obtained by adjoining \(\sqrt{D_d(r_d^2)}\) to the rational function field in \(r_d\), since \(y\) is recovered from \(x,r_d\). The discriminant of \(D_d\) is \(16d^2(d^2-1)\). Thus the root cover is quadratic with four simple branch values and no branching at zero or infinity. Two distinct positive gaps give disjoint branch sets because the difference of their \(D_d(z)\) is a nonzero multiple of \(z\) and neither polynomial vanishes at zero. All these statements about branch sets also hold in odd characteristic away from \(d_1d_2(d_1^2-1)(d_2^2-1)(d_1^2-d_2^2)\).

The unpowered relation \(u_{d_1}(P)=u_{d_2}(Q)\) separates geometrically into \(r_{d_1}(P)=\pm r_{d_2}(Q)\). Over the common root coordinate, each normalization is a degree-four cover with a biquadratic function field, since the two quadratic squareclasses have disjoint nonempty branch sets. Each of the eight branch values has two points of ramification index two. Riemann–Hurwitz gives \(2g-2=-8+16\), hence \(g=5\). The two affine signed curves can meet where both roots vanish, but the modular unit comparisons use nonzero roots. [Riemann–Hurwitz](https://stacks.math.columbia.edu/tag/0C1B)

## Comparisons of positive powers

Fix positive integers \(a,b\), set \(h=\gcd(a,b)\), and put \(m=a/h\), \(n=b/h\). Over \(\mathbb C\), the equation \(u_{d_1}(P)^a=u_{d_2}(Q)^b\) on the nonzero finite root coordinates reduces to
\[
 r_1^m=\zeta r_2^n,qquad \zeta^{2h}=1 .
\]
Choose a root of unity \(\alpha\) with \(\alpha^m=\zeta\). Since \(m,n\) are coprime, the root-coordinate curve is parametrized by \(r_1=\alpha t^n,\ r_2=t^m\). The two covers pulled back to this parameter have branch sets given by the roots of \(D_{d_1}(\alpha^2 t^{2n})\) and \(D_{d_2}(t^{2m})\), of sizes \(4n\) and \(4m\).

The roots of \(D_d\) are negative real reciprocals, with one of absolute value greater than one. In each pulled-back branch set, all points of modulus greater than one therefore lie over a single root of \(D_d\), and likewise for points of modulus less than one. At each of these two radii, common branch points satisfy simultaneous equations for \(t^{2n}\) and \(t^{2m}\) with nonzero right-hand sides. There are at most \(\gcd(2m,2n)=2\) solutions on each radius. If \(m\ne n\), the different sizes give independent quadratic squareclasses, and the union of the branch sets has size \(B\ge4m+4n-4\ge8\). If \(m=n=1\), the distinct gaps give distinct outer radii, since the greater absolute value is \((d+\sqrt{d^2-1})^2\), strictly increasing with \(d\). The branch sets are disjoint in this case even after multiplication by the root of unity.

The resulting function field is biquadratic on every root-coordinate component. At a common branch point the two local quadratic extensions coincide over an algebraically closed residue field, so the degree-four cover still has two points of ramification index two. Its genus is \(B-3\ge5\). A nonconstant rational map from a smooth parameter curve to a geometric component extends to the smooth projective models. Riemann–Hurwitz then forces the parameter curve to have genus at least five. For fixed rational gaps, twists and exponents there are also only finitely many exact rational pairs on the admissible locus by Faltings' theorem, after passing to a number field over which the finitely many components are defined. This argument concerns fixed charts and identities over characteristic zero. Congruences between input-dependent seeds are a separate supply question. [Faltings on the Mordell conjecture](https://doi.org/10.1007/BF01388432)

## Local frequency for independent seed pairs

At a good odd prime \(p\), consider the unpowered equality. If \(\delta_2/\delta_1\) is nonsquare, admissible points cannot satisfy it because \(u_{d_i}=\delta_i s_{d_i}^2\). If the ratio is square, use a local square root to compare \(s_{d_1}\) against the rescaled \(s_{d_2}\). Each sign gives a geometrically integral curve defined over \(\mathbb F_p\) of genus five. By Hasse–Weil it has \(p+O(\sqrt p)\) rational points on its smooth projective model. Restricting to both finite points away from all marks deletes only \(O(1)\) geometric points, because the two projections have degree two. Disjointness of the branch sets makes each signed fiber product smooth. Thus the probability of either specified sign for two independently uniform admissible points is
\[
                         p^{-1}+O(p^{-3/2}).
\]
The constant is uniform in the gaps and twists at the good primes. With the same twist over a semiprime \(pq\) and independent draws in the two reductions, the two mixed-sign patterns have total probability \((2+O(p^{-1/2}+q^{-1/2}))/(pq)\). This is a count for independent reductions, with no distribution assumption about rational or input-dependent menus. [Weil's point bound](https://e.lavoisier.fr/produit/479667/9782402625296/sur-les-courbes-algebriques-et-les-varietes-qui-s-en-deduisent)

## A mixed-sign comparison at 221

Use \(\delta=15\), \(d_1=4\), \(d_2=7\), \(P=(-1,2)\) and \(Q=(15,28)\). Both points satisfy their twist equations. Their signed roots are \(1/15\) and \(1/2\), whose difference is \(-13/30\) and sum is \(17/30\). Modulo \(221=13\cdot17\) both marked unit values are 59. The two root gcds split 221 into 13 and 17.

For the actual power-order units take \(F_i=W_{d_i}G_i-W_{d_i}'\) with
\[
                     G_1=X+1001,\qquad G_2=X^3+2X^2+90 .
\]
The reductions of the monic defining polynomials are irreducible modulo 7 and 5, respectively. In the finite check, each has no root in its test field and divides \(X^{\ell^k}-X\) for the corresponding test prime \(\ell\) and prime degree \(k\). Their roots at \(-1,15\) modulo 221 are simple, with derivatives 198 and 12. The power-order inverse identity for consecutive pairs applies to both fields. The two seed points are on different marked curves and the gcd calculation uses neither local group order.
