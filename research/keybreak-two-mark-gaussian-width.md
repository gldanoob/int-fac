# A two-mark lower bound on KeyBreak Gaussian width

The two-mark Gaussian image estimate used in KeyBreak needs coefficient width on the denominator-product scale. In the ordinary large-mark regime, shrinking the isotropic width from \(V^2\) to \(V^{2-\epsilon}\) makes the actual image and the ideal Gaussian in (G.19) nearly disjoint in total variation. The discrepancy is visible in a residue of the leading coefficient that survives projection onto the two evaluations. [KeyBreak, Lemma G.4 and (G.19), p. 109](https://crypto.sjtu.edu.cn/factoring.pdf#page=109) · [Other coefficient-width constraints](keybreak-skewed-top-box.md)

## The residue carried by the evaluation image

Let \(P_i=(a_i,b_i)\) be primitive and nonproportional, with \(b_i>0\). Let \(d\ge3\), and let \(E:\mathbb Z^d\to\mathbb Z^2\) evaluate a binary form of degree \(d-1\) at the two marks, using the source's descending order in \(X\). Put \(\Gamma=E\mathbb Z^d\), \(K=\ker(E:\mathbb Z^d\to\mathbb Z^2)\), \(B=b_1b_2\), and \(\Delta=a_1b_2-a_2b_1\).

As in the proof of G.4, an integer kernel form is divisible by the primitive product \((b_1X-a_1Y)(b_2X-a_2Y)\) with integral quotient. Therefore its leading coefficient \(c_0\) is divisible by \(B\). The residue \(c_0\bmod B\) defines a map \(\chi:\Gamma\to\mathbb Z/B\), independent of the integral lift. It is surjective by varying the coefficient of \(X^{d-1}\). This uses the full product \(B\) even when the denominators share primes.

The image contains \(\Delta\mathbb Z^2\). For instance, multiply the factor vanishing at \(P_2\) by a power of a Bézout linear form for \(P_1\), so the resulting degree-\((d-1)\) form evaluates to \((\Delta,0)\). Interchanging the points gives the other coordinate. In particular \(B\Delta\mathbb Z^2\subseteq B\Gamma\subseteq\ker\chi\), giving a full-rank sublattice in each residue comparison.

## Width and total variation

Take coefficient law \(D_{\mathbb Z^d,\sigma}\), with weights proportional to \(\exp(-\pi\|c\|^2/\sigma^2)\). Compare the law of \(Ec\) to the ideal Gaussian on \(\Gamma\) with parameter matrix \(\sigma^2 EE^{\mathsf T}\) and center zero. With nonzero multipliers \(G(P_i)\), the source's affine scaling to the raw values is a bijection of both measures, so this is exactly the comparison in (G.19) before imposing any other conditioning.

Write \(s_{\min}\) for the smaller semiaxis of the ideal Gaussian. The dual of \(\ker\chi\) is contained in \((B|\Delta|)^{-1}\mathbb Z^2\). Poisson summation on each of its cosets shows that their masses agree up to relative error
\[
\varepsilon_{\rm im}=O\!\left(\exp\!\left[-c\left(\frac{s_{\min}}{B|\Delta|}\right)^2\right]\right)
\]
when the ratio is at least one. Indeed, the nonzero dual contribution is bounded by a two-dimensional Gaussian sum on \((B|\Delta|)^{-1}\mathbb Z^2\), uniformly in the translate. Thus the ideal residue law is within \(O(\varepsilon_{\rm im})\) of uniform.

Suppose \(|a_i|\le V\) and \(c_1V\le b_i\le V\) for a fixed \(c_1>0\). The final two monomial columns of \(E\) have rows \(b_i^{d-1}(a_i/b_i,1)\). After extracting the row factors, their determinant has magnitude \(|\Delta|/B\), while their operator norm is bounded. Their smaller singular value therefore gives
\[
s_{\min}\gg \sigma\min_i(b_i)^{d-1}|\Delta|/V^2,
\qquad
\frac{s_{\min}}{B|\Delta|}\gg
\frac{\sigma(c_1V)^{d-1}}{V^4}.
\]
In particular the second ratio tends to infinity for \(d\ge6\), \(V\to\infty\), and \(\sigma\ge1\). The determinant cancels in this estimate, so near-parallel marks do not invalidate it.

In the actual image, the residue \(\chi\) is obtained by reducing one scalar discrete Gaussian of parameter \(\sigma\). For \(1\le\sigma=o(B)\), apply the scalar Gaussian tail at \(U=\sqrt{B\sigma}\). The residue set represented by integers in \([-U,U]\) has actual mass at least \(1-O(\exp(-c B/\sigma))\), while its ideal mass is \(O(\sqrt{\sigma/B}+1/B+\varepsilon_{\rm im})\). It follows that the image total variation distance is at least
\[
1-O\!\left(\sqrt{\sigma/B}+B^{-1}
             +e^{-cB/\sigma}+\varepsilon_{\rm im}\right).
\]
For \(\sigma\le V^{2-\epsilon}\) under the same assumptions this is \(1-o(1)\). The assumed spread of the ideal image matters: at extremely small \(\sigma\) both measures can instead concentrate at zero.

## Direct smoothing-parameter obstruction

For the lattice \(K\) in its real span, let \(w\) be the orthogonal projection of \(e_0/B\) onto that span. The divisibility of the leading coefficient implies \(w\in K^*\); it is nonzero because the kernel contains the coefficient vector of \((b_1X-a_1Y)(b_2X-a_2Y)X^{d-3}\), whose leading coefficient is \(B\). Also \(\|w\|\le B^{-1}\). Therefore the dual Gaussian sum in the standard smoothing parameter contains the two terms for \(w,-w\), and for \(0<\varepsilon<1\)
\[
\eta_\varepsilon(K)\ge B\sqrt{\log(2/\varepsilon)/\pi}.
\]
This lower bound does not require a wide image law or an angle condition. It gives a direct limit of the shifted-kernel Poisson comparison used in G.4. The total variation argument further shows that, in the stated large-mark regime, a different proof cannot supply (G.19) for the same narrow isotropic law. Neither argument prohibits changing the coefficient law or replacing the ideal two-value comparison.
