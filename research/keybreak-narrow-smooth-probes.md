# Exact smooth-predicate probes for a narrow two-mark Gaussian

The actual conditional smoothness moment admits an exact expansion in dual-kernel modes. It can be analyzed without the pointwise Gaussian image comparison in (G.19). One obstruction mode does cancel against the smooth predicates on a family of top-scale marks under the pinned GRH estimate. This cancellation leaves open the aggregate estimate for a narrower field. [KeyBreak, (G.8) and Lemma G.4](https://crypto.sjtu.edu.cn/factoring.pdf#page=109) · [Two-mark width obstruction](keybreak-two-mark-gaussian-width.md)

## Exact conditional moment and tail

Let \(c\in\mathbb Z^d\) have Gaussian parameter \(\sigma\), with weights \(\exp(-\pi\|c\|^2/\sigma^2)\). Let \(E\) evaluate a binary form of degree \(d-1\) at two distinct primitive marks. Allow conditioning on a compatible affine sublattice \(c\in c_*+\mathcal L\), as occurs for a fixed system of coefficient root congruences. Write
\[
\mathcal K=\mathcal L\cap\ker E,\qquad \Gamma=E(c_*+\mathcal L).
\]
Here \(\mathcal L\) has finite index, and \(\mathcal K^*\) is the dual lattice in the real kernel. For \(z\in\Gamma\), choose any compatible integer lift \(c_z\), put \(x_z=E^{\mathsf T}(EE^{\mathsf T})^{-1}z\), and put \(s_z=c_z-x_z\). The lift \(x_z\) is orthogonal to the real kernel. The shift \(s_z\) is defined modulo \(\mathcal K\), so the phase \(\chi_w(z)=\exp(2\pi i\langle w,s_z\rangle)\) is well-defined for \(w\in\mathcal K^*\). It is a character on the difference lattice \(E\mathcal L\), times a constant phase on the affine image.

Define \(\nu\) as the normalized measure on \(\Gamma\) with weights \(\exp(-\pi\|x_z\|^2/\sigma^2)\). This is the ideal Gaussian image on the exact support, with its original center even after conditioning. For example, take \(f(z)=f_1(F_0(P_1)+2G(P_1)z_1)f_2(F_0(P_2)+2G(P_2)z_2)\), absorbing any known root divisions into the predicates. The actual conditional expectation is exactly
\[
 \mathbb E[f(Ec)\mid c\in c_*+\mathcal L]
 =
 \frac{\displaystyle\sum_{w\in\mathcal K^*}
          e^{-\pi\sigma^2\|w\|^2}\nu(f\chi_w)}
      {\displaystyle\sum_{w\in\mathcal K^*}
          e^{-\pi\sigma^2\|w\|^2}\nu(\chi_w)}. \tag{1}
\]
The weight at \(z\) factors into \(\exp(-\pi\|x_z\|^2/\sigma^2)\) times the mass of \(\mathcal K+s_z\). Poisson summation on the latter gives the displayed phase sum times \(\sigma^{d-2}/\det\mathcal K\), which cancels in the ratio. The denominator is strictly positive since it is a positive ratio of Gaussian normalizers. Formula (1) also gives an image-event conditioning by replacing \(f\) and \(1\) with \(f1_{\mathcal E}\) and \(1_{\mathcal E}\) respectively. All sums in (1) are absolutely convergent for bounded \(f\).

For the unconditioned kernel \(K=\mathbb Z^d\cap\ker E\), an integer basis matrix \(A\) consists of shifts of the product \((b_1X-a_1Y)(b_2X-a_2Y)\). If both marks have height \(O(V)\), convolution by this three-coefficient product gives \(\|A\|_{\mathrm{op}}\le C V^2\), with no factor depending on \(d\). Since \(A^{\mathsf T}:K^*\to\mathbb Z^{d-2}\) is bijective, and its operator norm is at most \(CV^2\),
\[
 \sum_{w\in K^*}e^{-\pi\sigma^2\|w\|^2}\le (1+CV^2/\sigma)^{d-2}.
\]
Use the same argument at \(\sigma/\sqrt2\) to bound the tail with \(\sigma\|w\|>R\) by \(e^{-\pi R^2/2}(1+C'V^2/\sigma)^{d-2}\). In particular, if \(J\mathbb Z^d\subseteq\mathcal L\) the same two bounds hold with \(V^2\) replaced by \(JV^2\), since \(\mathcal K^*\subseteq J^{-1}K^*\). These bounds are uniform in the phases, the shifts and the marks.

At \(\sigma=V^{2-\epsilon}\), the unconditioned mass allowance is \(\exp(\epsilon(d-2)\log V+O(d))\). To approximate a positive \(\nu(f)=\mu\) to relative accuracy \(O(e^{-\gamma H})\), a sufficient bound on the retained nonzero weighted numerator is \(\mu e^{-\gamma H}\), along with \(e^{-\gamma H}\) on the retained nonzero denominator. For \(0\le f\le1\), \(|\nu(f\chi_w)|\le\mu\), so a tail mass \(e^{-\gamma H}\) suffices for both. The tail estimate gives such a cutoff with \(R^2\) of order \(\epsilon(d-2)\log V+d+\gamma H\); conditioning as above adds \((d-2)\log J\) to this allowance. For an approach that bounds each coefficient uniformly and sums absolute values, the sufficient per-mode relative suppression is \(\exp(-\epsilon(d-2)\log V-O(d)-\gamma H)\), with the corresponding conditioning term if present. This is an upper bound on the weighted mode count and a sufficient decay criterion. It is not a lower bound on the cancellation needed after summing phases.

## A leading residue mode canceled by the smooth predicates

Consider the unconditioned law at top scale, with \(\log V\asymp\log M\) for the radix scale \(M\), \(d\to\infty\), and \(\sigma=V^{2-\epsilon}\) for fixed \(0<\epsilon<2\). Take marks of height \(O(V)\) with distinct odd prime denominators \(b_i\asymp V\), neither dividing \(Q\). Assume \(\Delta=a_1b_2-a_2b_1\ne0\) and \(G_i=G(P_i)\ne0\). Use the two predicates \(f_i=1_{\{0<|F(P_i)|\in S_{y_i}\}}\) with \(y_i<b_i\). For these marks \(b_i\nmid 2G_i\Delta\), since \(G_i\equiv Qa_i\bmod b_i\) and the opposite denominator is a unit there. The source coefficient and radix bounds give \(|G_i|\le V^{O(1)}\) and \(|F_0(P_i)|\le V^{d+O(1)}e^{O(d)}\).

Put \(B=b_1b_2\) and let \(w\) be the projection of \(e_0/B\) to the real kernel. As in the width obstruction, \(w\in K^*\setminus\{0\}\) and \(\|w\|\le1/B\), so its Poisson weight is near one. Its phase factors as
\[
 \chi_w(z)=\exp(2\pi i\,c_{z,0}/B)\,
           \exp(-2\pi i\,\langle e_0/B,x_z\rangle).
\]
The first factor is the product of a nontrivial additive character modulo \(b_1\) of the first raw value and one modulo \(b_2\) of the second, times a constant. Indeed \(z_i\equiv a_i^{d-1}c_{z,0}\bmod b_i\), and the separate affine transformations to the raw values have unit multipliers there. On an ideal Mahalanobis ball of radius \(R_0=\log N\), the second factor is \(1+O(R_0\sigma/B)\), by \(\|x_z\|\le R_0\sigma\).

For the periodic part, partition the raw affine image into cosets of the Cartesian period lattice with separate steps \(m_i=2|G_i\Delta|\). The product period is in the image by the Bézout evaluation construction for \(\Delta\mathbb Z^2\). In a single coset and coordinate interval \(I\), refine the progression by its residue modulo \(b_i\). The zero class contributes no smooth values. For each nonzero class the principal term in (G.8) is identical, because the gcd with the new modulus \(m_i b_i\) is independent of this nonzero residue. If this term is \(M_i(I)\), the ordinary count is \((b_i-1)M_i(I)+O(b_i\mathcal E_i)\), and the character-weighted count is \(-M_i(I)+O(b_i\mathcal E_i)\) up to constant phase. Here \(\mathcal E_i=O_\tau(X_*^{1/2+\tau}(m_ib_i)^\tau)\) for fixed \(\tau>0\), with \(X_*\) bounding the raw magnitudes. The same estimate applies across zero by reflection and the prefix estimate (G.7). Thus no auxiliary equidistribution of the actual Gaussian is assumed.

To insert the ideal Gaussian weight, cover its Mahalanobis ball by axis-aligned grid cells of side \(s_{\min}V^{-1}\), where \(s_{\min}\) is the smaller raw Gaussian semiaxis. Include full cells meeting the ball. The final two monomials give \(s_{\min}\ge V^{d-O(1)}e^{-O(d)}\), and the bounding endpoint has \(X_*\le V^{d+O(1)}e^{O(d)}\operatorname{poly}(\log N)\). Both use \(b_i\asymp V\), the determinant bound \(|\Delta|\ge1\), and the size estimates above. Within any included cell the Gaussian weight varies relatively by \(O(R_0/V)\). The ideal mass outside the covered ball is \(\exp(-\Omega(R_0^2))\): compare the tails to the Gaussian of parameter \(\sqrt2\,\sigma\) and use Poisson summation for the two ideal normalizers, whose image semiaxes dominate a full-rank period lattice. Each coordinate interval now contains \(\asymp |I|/m_i\) points of its progression. With \(\tau\) sufficiently small, \(b_i\mathcal E_i/(|I|/m_i)=\exp(-\Omega(d\log V))\) uniformly. Inside each cell the two coordinate counts multiply on each Cartesian coset. Summing the estimates against constant cell weights, then restoring the varying weight and the nonperiodic phase, gives
\[
 |\nu(f\chi_w)|
 \ll \left(\frac1{(b_1-1)(b_2-1)}+\frac{R_0}{V}
               +\frac{R_0\sigma}{B}\right)\nu(f)
       +\exp(-\Omega(d\log V)).
\]
The same holds for \(-w\) by conjugation. This verifies cancellation of the particular leading-residue obstruction under the pinned Dirichlet GRH estimate for these probes. It is a statement about the ideal weighted Fourier coefficient, which is exactly where that mode enters the true expectation in (1). Nothing here bounds the combined contribution of the other modes. In particular the relative saving of this pair of modes is on a \(\log V\) scale, below the \(d\log V\) allowance for naive absolute summation at this width.
