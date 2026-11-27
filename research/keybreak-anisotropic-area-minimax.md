# Coefficient widths and rectangle area in the homogeneous height bound

Let \(m=d-1\) and consider
\[
P(u,v)=\sum_{j=0}^{m}c_j u^jv^{m-j},
\qquad |u|\le U,\quad |v|\le V.
\]
Write \(r=\sqrt{UV}\) and let \(G=(\prod_{j=0}^{m}\sigma_j)^{1/(m+1)}\) be the geometric mean of the positive coefficient widths. The area is \(4UV\). In particular \(U=e^{(s-w)H}\), \(V=e^{sH}\) give \(\log r=(s-w/2)H\).

## Exact monomial minimax

The product of the \(m+1\) corner contributions \(\sigma_j U^jV^{m-j}\) is \((Gr^m)^{m+1}\). Hence the minimum possible maximum contribution is exactly \(Gr^m\), with the unique choice
\[
\sigma_j=G(U/V)^{m/2-j}.
\]
All contributions coincide there. The result holds with any lower bound on \(G\) by using equality in that bound. If a monotonicity restriction requires the widths to increase with \(j\), the stated optimizer already obeys it when \(U\le V\).

For the entire coefficient box \(|c_j|\le\sigma_j\), the exact supremum of \(|P|\) over coefficients and marks is \(\sum_j\sigma_jU^jV^{m-j}\), attained with the positive corner of both boxes. Minimizing it yields \((m+1)Gr^m\) by arithmetic–geometric mean, with the same width equality case. For independent centered coefficients with standard deviations \(\sigma_j\), the supremum of the pointwise standard deviation is \((\sum_j\sigma_j^2U^{2j}V^{2(m-j)})^{1/2}\) and its minimum is \(\sqrt{m+1}\,Gr^m\), again with the same widths. Thus the sharp maximum-term log bound is \(\log G+m(s-w/2)H\), independent of the rectangle's skew at fixed area.

For several rectangles in the same coordinates put \(M_j=\max_i U_i^jV_i^{m-j}\). The exact minimum of the maximum term across the union is \(G(\prod_j M_j)^{1/(m+1)}\), attained uniquely by widths inversely proportional to \(M_j\). This is at least the bound for the largest area. Equality requires that a largest-area rectangle maximize every monomial size. When \(m\ge1\), this is equivalent to that rectangle dominating both side lengths. Rectangles of equal area with distinct skew strictly increase this joint maximum when the widths are shared. Their exact worst support bound need not be the sum of these separate maxima, since different terms can peak on different rectangles.

## Arbitrary linear coefficient coordinates

The geometric-mean constraint must act on volume for a basis-independent assertion. For example, assume the coefficient covariance \(C\) in the monomial basis satisfies \((\det C)^{1/(2(m+1))}\ge G\). Equivalently a standard coefficient vector is mapped into this basis by a matrix \(A\) with \(|\det A|\ge G^{m+1}\). This includes arbitrary covariance and determinant-one coefficient basis changes. The same matrix condition applies if the standard coefficient vector ranges over the unit cube and \(A\) sends it to a parallelepiped.

Use the \(m+1\) points \((U i/m,V)\), \(0\le i\le m\), when \(m\ge1\). The matrix of their evaluation functionals on the transformed coefficients has absolute determinant
\[
|\det A|\,r^{m(m+1)}\!
\prod_{0\le i<j\le m}\frac{j-i}{m}.
\]
The product is at least \(e^{-O(m^2)}\), since its logarithm is \(\sum_{j=1}^m(\log(j!)-j\log m)\), and \(\log(j!)\ge j\log j-j\), \(j\log(m/j)\le m/e\). Hadamard bounds the determinant by the product of the row Euclidean norms. These norms are the pointwise standard deviations. For a coefficient parallelepiped the pointwise support is the row \(\ell^1\)-norm, which is at least its Euclidean norm. Consequently the largest pointwise standard deviation or support on the rectangle is at least \(Gr^m e^{-O(m)}\). Degree zero gives the same conclusion directly. The monomial construction gives the matching leading log bound up to \(O(m)\), so changing basis can change finite constants while preserving the coefficient of \(mH\) as \(H\to\infty\).

A determinant-one change in the mark plane also preserves the coefficient volume. For a linear substitution \(T\) its action in degree \(m\) has determinant \((\det T)^{m(m+1)/2}\), as follows by checking diagonal and elementary shear matrices. The area lower bound therefore applies separately in each oriented rectangle and hence to their union, even when their slopes vary. Independently retuning the widths on each rectangle gives the same bound on each one at its own area. This argument measures the area of individual rectangles; a union of many smaller pieces needs a separate estimate if only its total area is available.

These bounds concern unrestricted marks in each displayed rectangle, and either worst support over coefficients or a pointwise second moment. They do not bound below the value of a particular polynomial at a selected mark, or the norms conditional on smoothness. The determinant proof also works on any mark subset admitting \(m+1\) evaluations with the same determinant scale. A thin slope restriction, a primitive lattice condition, or arithmetic conditioning must supply that assertion separately; the ambient area's bound alone does not do so. Likewise, a Fourier argument that constrains only some linear combinations of coefficient widths needs its own translation to a determinant bound.
