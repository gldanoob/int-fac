# Interior moment guards at Gaussian width \(V_0^{37/20}\)

The interior pair proof has two independent scale comparisons. The separate-period GRH error needs a lower bound on the *actual* algebraic endpoint. The Gaussian image comparison needs the coefficient width to exceed the square of the largest *interior* mark size. At the half-width schedules with top ratio \(1.63\), both comparisons hold with a fixed power margin when \(\sigma=V_0^{37/20}\) up to polynomial padding. The three-root coefficient congruence guard also holds, with a smaller margin. [KeyBreak, Lemma G.4 and Proposition G.13](https://crypto.sjtu.edu.cn/factoring.pdf#page=123)

## Separate coordinate periods

Use base-two logarithms for the leading sizes. Let \(n\) be the input bit length, \(m_b\) the bit length of \(n\), and \(t=dm_b\). Write \(A_0=\delta^{-3}\) for the limit of \(\log_2 M/(dt)\). In a box with exponent \(e\ge e_B\), put
\[
e_B=\beta t+O(1),\qquad v(e)=\alpha e+\gamma e_B+O(1),\qquad V=2^{v(e)},\qquad S=\alpha+\gamma.
\]
The largest top box has \(\log V_0/\log M\to v_0\). For \(\sigma=V_0^\chi n^{O(1)}\) with \(\chi=37/20\), the leading coefficient of \(\log_2(\sigma M)/(dt)\) is
\[
h_\chi=A_0(1+\chi v_0).
\]
The retained endpoint in the analytic estimates comes from the actual marginal width. From (G.25), it has size \(\sigma M V^d\) up to root and parent divisions, factors \(2^{O(d)}\), and the fixed near-zero or radius padding. In the interior, these factors cost \(O(e+e_B+d+\log n)\) in its logarithm. Thus a uniform conservative lower bound on each retained endpoint is
\[
\log_2 X_*\ge (h_\chi+o(1))dt+d(\alpha e+\gamma e_B)-O(e+e_B+d+\log n).
\]
An upper reference height \(T_H\) used to authorize the cutoffs in (G.57) supplies no lower bound for this estimate. In particular, keeping the old cutoff schedule does not preserve the old actual \(\log X_*\). [KeyBreak, (G.25)–(G.26) and (G.57)](https://crypto.sjtu.edu.cn/factoring.pdf#page=111)

For a nonzero determinant \(\Delta=|\det(P_1,P_2)|\) and root divisor \(q\), the two periods are \(m_i=2|G(P_i)|\Delta/q\). As \(|G(P_i)|\asymp MV\) and \(\Delta=O(V^2)\), each period is \(O(MV^3)\). The upper bound also holds for \(m_i\vartheta\) with \(\vartheta=b_1b_2/\Delta\), since \(m_i\vartheta=2|G(P_i)|b_1b_2/q\). For the same fixed marks, dividing both the width and the period by \(q\) leaves their ratio unchanged. There is no product of the two periods in the one-coordinate denominator. [KeyBreak, (G.21)–(G.24) and Lemma G.9](https://crypto.sjtu.edu.cn/factoring.pdf#page=110)

The first term in (G.38), after dividing by the cell length and the reference density, is bounded by a fixed constant times
\[
c_i^{-1}\eta^{-1}m_i^{1+\varepsilon}X_*^{-1/2+\varepsilon}\max(1,Y^{1/2-\varepsilon}).
\]
Here \(\log Y=O(e+e_B)\), inverse smoothness densities have logarithm \(O(t)\) by (G.26), and the interior grid factor has logarithm \(o(dt)\). The base-two logarithm of the error is at most
\[
\big[(1+\varepsilon)A_0-(1/2-\varepsilon)h_\chi+o(1)\big]dt
 -(1/2-\varepsilon)d(\alpha e+\gamma e_B)+O(e+e_B).
\]
The negative coefficient of \(e\) of order \(d\) dominates the positive lower-order coefficient of \(e\). Thus the worst leading exponent is at \(e=e_B\). A sufficient strict guard is
\[
\mathcal G_\varepsilon=(1/2-\varepsilon)(h_\chi+S\beta)-(1+\varepsilon)A_0>0.
\tag{1}
\]
For \(\varepsilon=1/32\), it is \(h_\chi+S\beta>(11/5)A_0\). This makes the normalized progression error exponentially small in \(dt\), including the one-point estimate with a prescribed parent. The same leading comparison applies in G.9, using \(m_i\vartheta=O(MV^3)\). The Gaussian grid endpoint condition from (G.23) retains the factor \(\sigma V^{d-3}/2^{d-2}\), whose logarithm still grows on the \(d\log V\) scale after the radius padding. [KeyBreak, (G.38) and the separate-period calculation in Proposition G.13](https://crypto.sjtu.edu.cn/factoring.pdf#page=125)

A reduction from \(\chi=2\) to \(37/20\) reduces the margin in (1) by exactly \((1/2-\varepsilon)(3/20)A_0v_0\) with the other parameters fixed. This can exhaust a small margin in an abstract schedule. If \(h_\chi+S\beta>2A_0\), a sufficiently small fixed \(\varepsilon>0\) still certifies decay. At or below \(2A_0\), this square-root progression estimate does not certify the required saving. This comparison is an upper-error test.

For (G.32), the additional factor \(4k\) with \(k=\Delta/q\) costs only \(O(e+e_B)\) in the logarithm. The endpoint margin uses \(h_\chi+S\beta>A_0\), already implied by (1). The factors \(U,B_\nu\), and the remaining interior grid and density factors have logarithms \(o(d(e+t))\) with the choices in (G.29). The Bonferroni truncation term \(E_\nu\) in (G.38) has no period multiplier. The original truncation choice can be kept because \(\log X_*\) remains comparable to \(d(e+t)\) and \(\log y\) to \(e+t\). These comparisons use the same positive bounded cutoff ratios as the half-width schedule. [KeyBreak, (G.29), (G.31)–(G.32), and (G.38)](https://crypto.sjtu.edu.cn/factoring.pdf#page=112)

## Gaussian image and coefficient congruences

For two distinct primitive marks in one box, the integer evaluation kernel has a basis of monomial multiples of \((b_1X-a_1Y)(b_2X-a_2Y)\) of norm at most \(3V^2\). A nonzero dual vector has norm at least \(1/(3V^2)\). The pointwise Gaussian comparison of G.4 follows when \(\sigma/(3V^2)\) dominates the required polynomial in \(n\). For example, \(\sigma/(3V^2)\ge n^6\) gives the advertised \(e^{-n^{10}}\) error in its dual bound for sufficiently large inputs. Interior boxes are bounded by \(V_1\) with \(\log V_1/\log M\to v_1\). A sufficient leading guard is therefore
\[
\chi v_0>2v_1.
\tag{2}
\]
A fixed root condition in an interior pair is determined by the evaluation image. The support is restricted before dividing the two evaluations by \(q\), so no extra \(q\) multiplies the kernel basis norms in this comparison. The one-mark kernel uses only \(O(V)\) basis norms, and its comparison also holds at top size for \(\chi>1\). At the maximal top pair size \(V=V_0\), (2) would require \(\chi>2\). The G.4 two-point argument thus needs separate treatment for the larger top boxes, even though (1) remains valid there. Smaller top boxes with \(\log V/\log V_0<\chi/2\) by a fixed gap satisfy this same kernel test. [KeyBreak, Lemma G.4](https://crypto.sjtu.edu.cn/factoring.pdf#page=109)

A different use of the Gaussian compares the coefficient residues modulo the product of at most three child primes. The upper product is \(Y_1^3\) because a private top parent does not condition the coefficients. The finite guard in Proposition G.13 is \(\log_2\sigma-3\log_2 Y_1\ge 20 A_{\rm tail}^2t\), with \(A_{\rm tail}=(j+10)^3\). Since \(j=O(\log D)\), the right side is \(o(dt)\). Thus a sufficient leading guard is
\[
\chi v_0>3y_1,\qquad y_1=\lim\frac{\log Y_1}{\log M}.
\tag{3}
\]
This is the guard for coefficient-root probabilities and finite-sampler conditioning, including events involving several primes. Equation (2) suffices for the single-root evaluation-image restriction in the interior moment proof. [KeyBreak, (G.20) and Proposition G.13](https://crypto.sjtu.edu.cn/factoring.pdf#page=123)

## Half-width margins

For the tiered half-width schedule, \(v_0=\alpha/(2\kappa)\), \(y_1=v_0/\lambda_T\), and \(v_1=\alpha y_1\). The local top ratio \(1+(\lambda_T-1)a\) gives the same maximum child at \(a=1\). With \(\lambda_T=1.63\) and \(\alpha=.500000000001\), the congruence margin divided by \(v_0\) is the exact positive number \(37/20-3/1.63=31/3260\). The interior two-mark margin divided by \(v_0\) is \(37/20-2\alpha/1.63>1.23\). The two comparisons do not depend on choosing a new terminal cutoff.

For the published 353- and 4096-stage parameter choices, (1) at \(\varepsilon=1/32\) gives respectively \(\mathcal G_\varepsilon>.18705\) and \(>.18700\) in \(dt\) units, keeping their existing terminal box coefficients. For comparison, rebuilding the same low fixed-point and mean formulas with height \(h_\chi+10^{-11}\) instead gives \(\mathcal G_\varepsilon>.18568\) and \(>.18563\). That substitution checks these moment guards alone. [Half-width parameters](keybreak-quadratic-class-integration.md) · [Explicit schedule formulas](../experiments/keybreak-quadratic-class-budget.py)

Even at the original Appendix G.13 parameters, the true new height is \(h_\chi=(64/27)(1+(37/20)(17/60))=7316/2025\), so the printed conservative lower coefficient \(3.7\) must be replaced. Using a new lower coefficient \(3.6\), the same period upper coefficient \(2.4\), and \(S\beta=(4/3)(19/15)\), the remaining \(\varepsilon=1/32\) margin is exactly \(1/240\). Using the true limiting height and period coefficients gives \(11/270\). [KeyBreak, (G.56) and Proposition G.13](https://crypto.sjtu.edu.cn/factoring.pdf#page=125)
