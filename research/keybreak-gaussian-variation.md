# Mixed variation of a twisted Gaussian on a rectangular lattice

Let \(T_1,T_2>0\) be marginal scales, \(c\in\mathbb R^2\) a center, and
\[
D=\operatorname{diag}(T_1,T_2),\qquad
C=\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix},\qquad
\kappa=\sqrt{1-\rho^2}\ge K^{-1}>0.
\]
Use normalized coordinates \(u=D^{-1}(x-c)\), and Mahalanobis coordinates \(y=C^{-1/2}u\). Define the Gaussian \(g(x)=e^{-\pi\|y\|^2}\) and its affine twist \(w(x)=g(x)e^{2\pi i(\alpha+\beta^T u)}\). Suppose \(\|C^{1/2}\beta\|\le R\). The normalizing mass throughout is the mass of \(g\).

For a rectangular lattice of spacings \(h_1,h_2\), let
\[
\delta=\frac1{2\kappa}\left(\frac{h_1}{T_1}+\frac{h_2}{T_2}\right)\le\frac1{10}.
\]
For \(L\ge4\), truncate to the lattice rectangle \(B=\{|u_1|,|u_2|\le L\}\). If a complex array \(d\) on \(B\) has every rectangular prefix sum bounded in absolute value by \(E\), then
\[
\left|\frac{\sum_{x\in B}d(x)w(x)}{\sum_{x\in B}g(x)}\right|
\le 16\pi^2(1+R^2)K^2\frac{h_1h_2}{T_1T_2}E.
\tag{1}
\]
Here both sums are over lattice points. For a product \(d(x)=d_1(x_1)d_2(x_2)\), one can take \(E=E_1E_2\) using the two unweighted one-dimensional prefix bounds. With the full lattice normalizer the factor \(16\pi^2\) can be replaced by \(8\pi^2\). If \(|d(x)|\le M\) on the full lattice, the omitted weighted sum divided by the full mass is at most \(8M e^{-\pi L^2/8}\).

## Integrated variation

Write \(A=C^{-1}\). The Gaussian integral is \(Z=\int g=T_1T_2\kappa\). For \(i=1,2\), set \(z_i=-(Au)_i+i\beta_i\), where the multiplier of \(\beta_i\) is the imaginary unit. Differentiating gives
\[
\partial_i w=\frac{2\pi}{T_i}z_iw,\qquad
\partial_1\partial_2 w=\frac{4\pi^2 z_1z_2-2\pi A_{12}}{T_1T_2}w.
\]
Under the probability measure \(g(x)\,dx/Z\), the vector \(y\) has density \(e^{-\pi\|y\|^2}\) and covariance \((2\pi)^{-1}I\). The diagonal entries of \(A\) are \(\kappa^{-2}\), and \(|A_{12}|\le\kappa^{-2}\). Since \(Au=C^{-1/2}y\) and \(\beta=C^{-1/2}(C^{1/2}\beta)\),
\[
\mathbb E|z_i|^2=\frac{A_{ii}}{2\pi}+\beta_i^2\le\kappa^{-2}\left(\frac1{2\pi}+R^2\right).
\]
Cauchy–Schwarz now bounds the mixed variation by
\[
\frac1Z\int_{\mathbb R^2}|\partial_1\partial_2 w|\,dx
\le \frac{4\pi+4\pi^2R^2}{\kappa^2T_1T_2}.
\tag{2}
\]
The first derivative bound is \(Z^{-1}\int|\partial_i w|\le (2\pi/(\kappa T_i))\sqrt{(2\pi)^{-1}+R^2}\).

## Rectangular summation by parts

List the retained lattice coordinates in increasing order as \(s_i\) and \(t_j\). Write \(P_{ij}=\sum_{k\le i,\,\ell\le j} d(s_k,t_\ell)\), with sums starting at the lower endpoints of the rectangle. Subtract successive prefixes in each coordinate and telescope. The weighted sum equals
\[
\sum_{i,j}P_{ij}\bigl(w(s_i,t_j)-w(s_{i+1},t_j)-w(s_i,t_{j+1})+w(s_{i+1},t_{j+1})\bigr),
\]
where an index beyond the last retained one has weight zero. For this last bin, integrate the derivative to \(+\infty\) in its coordinate. The Gaussian and its derivatives tend to zero at infinity, so every displayed difference is the integral of \(\partial_1\partial_2 w\) over the corresponding cell, including the unbounded edge cells. These cells have disjoint interiors. The total absolute sum of the weight differences is at most \(\int|\partial_1\partial_2 w|\). This argument accounts for the truncation faces through the edge cells. A bound on the full retained rectangle alone cannot replace the prefix bounds in this step.

## Lattice mass and tails

Tile \(\mathbb R^2\) by raw rectangles centered at the lattice points, each of area \(h_1h_2\). In Mahalanobis coordinates every tile point is within \(\delta\) of the tile center, since \(\|C^{-1/2}e_i\|=1/\kappa\). If the tile point has radius \(r\), its center's Gaussian value is between \(e^{-\pi(r+\delta)^2}\) and \(e^{-\pi(r-\delta)_+^2}\). Radial integration in two dimensions shows that the full lattice mass \(Z_{\rm lat}=\sum g(x)\) satisfies, uniformly in the lattice translate,
\[
1-\pi\delta-\pi\delta^2\le \frac{h_1h_2 Z_{\rm lat}}{Z}
\le 1+\pi\delta+\pi\delta^2.
\]
For instance, the upper integral is \(1+\pi\delta+\pi\delta^2\) after splitting at radius \(\delta\). The lower integral is \(e^{-\pi\delta^2}-2\pi\delta\int_\delta^\infty e^{-\pi t^2}dt\). In particular \(Z_{\rm lat}\ge Z/(2h_1h_2)\).

A center omitted by \(B\) has Mahalanobis radius greater than \(L\), since each row of \(C^{1/2}\) has norm one. Its tile lies at radii at least \(L-\delta\). On this set \(r-\delta\ge r/2\), so the integrated upper bound for the omitted mass is at most \(4e^{-\pi(L-\delta)^2/4}\) in units of \(Z/(h_1h_2)\). Dividing by the lower bound on \(Z_{\rm lat}\) gives an omitted fraction at most \(8e^{-\pi L^2/8}\). For \(L\ge4\) this leaves at least half the full mass in \(B\). Combining the resulting mass lower bound with (2) and the prefix identity proves (1).

All estimates hold on each translated progression phase. If an affine image is a disjoint union of such phases with the same spacings and the prefix hypotheses are uniform, the phase bounds combine with their positive Gaussian masses as weights. The number of phases introduces no factor.
