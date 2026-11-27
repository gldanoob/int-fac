# Width of an absolute Fourier estimate on the congruence lattice

Consider a degree-\(d\) integral binary form with one prescribed congruence at a primitive anchor \(R=(r,Q)\) modulo \(N\), and two exact values at distinct primitive marks \(P_i=(a_i,b_i)\) with positive \(b_i\). Write \(r_0=d-1\), assume \(d\ge2\), and suppose \(b_1b_2\asymp V^2\). If both determinants \(b_i r-a_i Q\) are units modulo \(N\), the Euclidean covolume of the difference lattice in the two-value fiber satisfies
\[
 \det\Lambda\ \ge\ N (b_1b_2)^{r_0}.
\]
This gives a width restriction for a proof that bounds *every* Fourier error by the same product of two square-root estimates and then sums all absolute mode weights. Signed sums, arithmetic estimates on individual modes, and a different sampled lattice can give different bounds. [Balanced top moment using phase averages](keybreak-mixed-strip-moment.md)

## Fiber determinant

A difference of two forms with the same exact values is divisible over the integers by \(K=(b_1X-a_1Y)(b_2X-a_2Y)\). Rational divisibility uses the two distinct projective roots, and the product of the primitive linear forms is primitive, so Gauss's lemma gives integral divisibility. The quotient \(W\) has degree \(d-2\), with \(r_0\) coefficient slots. The remaining condition is \(W(R)=0\bmod N\) since \(K(R)\) is a unit. Evaluation onto \(\mathbb Z/N\) is surjective: a Bezout linear form \(J\) with \(J(R)=1\) supplies \(J^{d-2}\), including degree zero. Thus the quotient coefficient lattice has index \(N\). Take any integer basis matrix \(U\) of it, with \(|\det U|=N\).

In ascending powers of \(X\) after dehomogenizing, the projection of \(KW\) onto degrees \(2,\ldots,d\) is triangular with diagonal \(b_1b_2\). The corresponding square minor of the full fiber basis has absolute determinant \(N(b_1b_2)^{r_0}\). Cauchy–Binet expresses the squared covolume as a sum of all squared maximal minors, which proves the bound. There is no restriction on the slopes other than the stated primitivity, distinctness and unit hypotheses. Lean verifies the convolution identity, the triangular determinant, and its product with an arbitrary square basis matrix. [Projected determinant](../formal/cogentic/Cogentic/RandomizedTopCoefficientDet.lean)

## What a uniform per-mode estimate can certify

For an isotropic coefficient Gaussian of width \(H_f\), Poisson summation on the span of the difference lattice gives
\[
 \sum_{w\in\Lambda^*}e^{-\pi H_f^2\|w\|^2}
 =\frac{\det\Lambda}{H_f^{r_0}}
   \sum_{v\in\Lambda}e^{-\pi\|v\|^2/H_f^2}
 \ge \frac{N(b_1b_2)^{r_0}}{H_f^{r_0}}.
\]
A translate inserts unit phases in the Fourier series and leaves the sum of absolute Gaussian weights unchanged. Suppose two value tests are treated solely by a common per-mode *relative* bound \((X_1X_2)^{-1/2}V^{o(1)}\), with value scales \(X_i\le H_f V^d e^{O(d+\log d)}\). For the upper bound obtained by multiplying this allowance by the full nonzero dual mass to be small, a necessary consistency check, in the growing-scale regime, is
\[
 H_f^d\ \ge\ N V^{d-2} e^{-O(d+\log d)}V^{-o(1)} .
\]
Indeed the mass includes the zero mode only once, so successful comparison requires \(\det\Lambda/H_f^{r_0}\le 1+(X_1X_2)^{1/2}V^{o(1)}\); substitute the determinant and value bounds. In particular when \(d\to\infty\), \(V\to\infty\) and \(\log N/d\asymp\log V\), such a comparison requires \(\log H_f\ge d^{-1}\log N+(1-o(1))\log V\). Enlarging the allowed target multiplier while changing the physical degree must use \(N^{1/d}\) at that actual degree when applying the check. The lower bound concerns this absolute majorant. An individual tested pair can have a much smaller error, and the fixed equality \(F(R)=kN\) has a different difference lattice from the congruence considered here.
