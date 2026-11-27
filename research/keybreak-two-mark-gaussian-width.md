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

## The transition width for a stable polynomial

Fix the degree \(r\). Let the primitive integral kernel polynomial \(H_n\), after division by its signed leading coefficient of magnitude \(B=B_n\to\infty\), converge coefficientwise to a monic polynomial \(h\) with all roots in a fixed disk of radius less than one. Let the number \(n\) of input coefficients tend to infinity. Set
\[
 e(h)=\min_{0\ne k\in\mathbb Z^{(\mathbb Z)}}\;
 \int_0^1 \frac{|\sum_j k_j e^{2\pi ijt}|^2}{|h(e^{2\pi it})|^2}\,dt,
 \qquad
 \sigma_* = B\sqrt{\frac{\log n}{2\pi e(h)}} .
\]
Here \(k\) has finite support. Compare the orthogonal image of \(D_{\mathbb Z^n,\sigma,c}\) under orthogonal projection off the real span of integral multiples of the polynomial with the discrete Gaussian of the same width on the projected lattice, centered at the projected \(c\). For every fixed \(0<\delta<1\), their total variation distance tends to one for \(1\le\sigma\le(1-\delta)\sigma_*\) and to zero for \(\sigma\ge(1+\delta)\sigma_*\). Both conclusions hold uniformly in \(c\). A fixed parity translate is covered by measuring the width in units of the coefficient spacing. These conclusions concern the entire exact evaluation vector. [Definition of the image laws and integral kernels](keybreak-quadratic-pair-reserve.md#a-necessary-width-for-the-full-two-value-gaussian-approximation)

Let \(M\) be the \(n\)-by-\((n-r)\) matrix with columns the coefficient vectors of the untruncated products \(X^jH_n\). Write \(K=M\mathbb Z^{n-r}\), and let \(P,\pi\) project onto its real span and orthogonal complement, respectively. Write \(L=\pi\mathbb Z^n\). A vector of \(K^*\) has the form \(w_k=M(M^tM)^{-1}k\). Its squared length is \(B^{-2}k^tG_nk\) where \(G_n=(M^tM/B^2)^{-1}\). Parseval bounds the eigenvalues of \(G_n\) in a fixed compact interval \([\beta,\beta^{-1}]\subset(0,\infty)\), since the normalized polynomial is uniformly bounded above and away from zero on the unit circle. The bilateral inverse Gram \(G\) is the Fourier multiplier \(1/|h|^2\), with the same coercivity bound after shrinking \(\beta\). The entries of both inverses decay exponentially off the diagonal, uniformly in \(n\). Indeed a scaled Neumann series for the inverse of the banded positive Gram has a geometrically small operator-norm tail, and its degree-\(d\) partial sum has bandwidth \(rd\). In particular \(e(h)\ge\beta\). It is attained: a minimizing sequence has bounded integer amplitudes and support cardinality. After translating and taking a subsequence, every gap between consecutive sites is fixed or tends to infinity. A diverging gap splits the limiting energy into at least two nonempty fixed blocks of energy at least \(e(h)\) each, by decay. This contradicts minimality.

**An averaged theta estimate.** For any lattice \(\Lambda\), write \(\Theta_\Lambda(t)=\sum_{z\in\Lambda}\exp(-\pi t^2\|z\|^2)\). For \(w\in K^*\), extend its integral linear functional on the saturated lattice \(K\) to \(\mathbb Z^n\). The representing \(z_w\in\mathbb Z^n\) satisfies \(Pz_w=w\). Put \(v_w=\pi z_w\), defined modulo \(L^*\). Fiber Poisson summation expresses the density relative to the target Gaussian \(Q\) as \(A/\mathbb E_Q A\), where \(A-1\) is a Fourier series on \(L\) with character frequencies \(v_w\) up to sign and coefficient magnitudes \(\exp(-\pi\sigma^2\|w\|^2)\), \(0\ne w\in K^*\). Orthogonal decomposition of \(\|x-c\|^2\) gives the common target weight before this fiber correction. The normalizing mass is positive.

Assume \(\sigma\to\infty\). Under \(Q\), the correlation for \(w,w'\) has absolute value at most
\[
 (1+O_r(e^{-c_0\sigma^2}))\sum_{u\in L^*}
 \exp(-\pi\sigma^2\|v_w-v_{w'}+u\|^2).
\]
This follows by Poisson summation in fixed rank, since \(L^*\subset\mathbb Z^n\) has minimum at least one. Grouping the squared error by the integral lift \(z\) with \(Pz=w-w'\) and \(\pi z=v_w-v_{w'}+u\) gives
\[
 \mathbb E_Q|A-1|^2 \le (1+O_r(e^{-c_0\sigma^2}))
 \left\{\Theta_{K^*}(\sqrt2\,\sigma)-1+
 \Theta_{K^*}(\sqrt2\,\sigma)
 [\Theta_{\mathbb Z^n}(\sigma/\sqrt2)-1]\right\}.
\]
Indeed \(z=0\) gives precisely the first theta tail in the majorant. For fixed \(z\ne0\), the sum over \(w\) has exponent given by
\(\|w\|^2+\|w-Pz\|^2+\|\pi z\|^2
=2\|w-Pz/2\|^2+\|Pz\|^2/2+\|\pi z\|^2\).
A shifted lattice Gaussian has total mass at most its unshifted mass, again by Poisson. This yields the second term. Vanishing of the bound implies \(d_{\rm TV}=o(1)\) by Cauchy–Schwarz and \(\mathbb E_Q A=1+o(1)\).

**Summing short dual vectors.** Above \((1+\delta)\sigma_*\), the ambient integer theta tail vanishes by the one-dimensional product formula and \(B\to\infty\). For the kernel theta tail choose a small fixed \(\epsilon>0\) with \((1+\delta)^2(1-\epsilon)>1\). Use a fixed polynomial approximation to the inverse with operator error as small as needed compared to \(\epsilon\beta\), hence fixed bandwidth \(D\), for both the finite Gram and the bilateral Gram. The finite normalized Gram is exactly a finite Toeplitz section, as no output coefficients are truncated. Away from its two boundaries the polynomial therefore agrees with its bilateral counterpart for \(H_n/B\) up to leading sign. Coefficientwise convergence gives an additional \(o(1)\) operator error on replacing the bilateral symbol by \(h\).

Group the nonzero entries of \(k\) into maximal clusters with successive gaps at most \(D\). The polynomial has no cross terms between clusters. A bulk cluster, lying more than \(D\) from both boundaries, has bilateral energy at least \(e(h)\). Every cluster, including ones meeting either boundary strip, has a positive quadratic energy floor by coercivity. Combining these facts and absorbing the polynomial approximation errors gives
\[
 k^tG_n k\ \ge\ (1-\epsilon)e(h)\,\#\{\text{bulk clusters}\}
                 + c_\epsilon\sum_j k_j^2
\]
for all large \(n\), with \(c_\epsilon>0\). A cluster with \(t\) sites has at most \(D^{t-1}\) gap patterns after its first site is fixed. There are at most \(n\) bulk anchors, and \(O(D)\) anchors for clusters touching a boundary, counting from the right for the rightmost boundary. The amplitude weight per site sums to \(\sum_{a\ne0} e^{-2\pi(\sigma/B)^2 c_\epsilon a^2}=o(1)\). Summing over \(t\) is geometric. The bulk anchor factor is absorbed by \(n\exp(-2\pi(\sigma/B)^2(1-\epsilon)e(h))=o(1)\). The total weight of all individual clusters thus tends to zero. Overcounting their possible collections by the exponential of that sum bounds \(\Theta_{K^*}(\sqrt2\,\sigma)-1=o(1)\).

**A test below the width.** Choose translates of one fixed minimizing integer pattern \(k\), spaced by \(C\log n\), all at least \(C\log n\) from the ends. The \(m\asymp n/\log n\) resulting dual vectors \(w_i\) satisfy \(\|B w_i\|^2=e(h)+o(1)\) uniformly by the same polynomial approximation. Their entries decay exponentially away from the translated support, with prefactor \(O(1/B)\), by the inverse Gram decay and the banded matrix \(M\). Consider the characters on \(L\) of frequencies \(v_i\), rotated by unit scalars so their pullbacks at an integer \(x\) are \(\exp(-2\pi i\langle w_i,x-c\rangle)\). Under the actual law their expectations have real part
\[
  e^{-\pi\sigma^2\|w_i\|^2}(1+o(1)).
\]
For \(\sigma\ge1\) the one-coordinate, centered characteristic function at \(|t|\le1/4\) is \(e^{-\pi\sigma^2t^2}(1+O(\sigma^2 |t|e^{-c_2\sigma^2}))\): in the Poisson sum subtract the untwisted series, use the mean value theorem on each nonzero dual term, and divide by the untwisted mass, uniformly bounded below after normalization. Multiplication over coordinates costs a relative \(o(1)\) since \(\|w_i\|_1=O(1/B)\). Therefore the real means are at least \(n^{-(1-\delta)^2/2+o(1)}\). For the actual law truncate each rotated character's coefficient vector to disjoint intervals around its support. Its expected change is at most \(O((\sigma/B)n^{-3})\) for large enough \(C\), using \(\mathbb E|x_j-c_j|\ll\sigma\). The truncated variables are independent and bounded by one, so their sum has variance \(O(m)\).

For the ideal law the complex sum of the \(m\) rotated characters has second moment \(O_r(m)\) for \(\sigma\) greater than a sufficiently large fixed constant. To see this, for fixed \(i\) the union of the cosets \(v_i-v_j+L^*\) is uniformly separated. For distinct \(j,j'\), the corresponding difference lifts to a nonzero integral vector with kernel component \(w_j-w_{j'}\) of norm \(O(1/B)\); its orthogonal component has norm at least \(\sqrt{1-O(B^{-2})}\). Distinct points of one coset are at least one apart. Packing this union in fixed rank in the correlation bound gives \(O_r(1)\) for each row. The sum of the actual real means exceeds \(\sqrt m\) by a factor tending to infinity, so Chebyshev and the ideal second moment give a separating event of probabilities \(1-o(1)\) and \(o(1)\). For the remaining bounded range \(1\le\sigma\le\sigma_0(r)\), the finite-support estimate in the pair note gives the same conclusion directly, taking \(R=B^{1/4}\).

For \(h=X^r\) the integral energy is \(\sum k_i^2\), giving \(e=1\). For example \(H_n=B X^r+1\) has the cutoff \(B\sqrt{\log n/(2\pi)}\). For \(h=X-a\), \(0\le a<1\), the Toeplitz entries are \(a^{|i-j|}/(1-a^2)\). The energy minimum is
\[
 e(X-a)=\min\{1/(1-a^2),\,2/(1+a)\}.
\]
One unit site and two adjacent sites with opposite signs realize the two candidates. If \(\sum k_i^2\ge4\), coercivity gives \(4/(1+a)^2\ge2/(1+a)\). At squared norm two the optimal separation is one. At squared norm three, write \(x,y\) for the powers of \(a\) across the successive gaps and \(u,v\in\{\pm1\}\) for adjacent sign products. The numerator of the energy is \(1+2(1+ux)(1+vy)\ge1\). In particular, for \(a>1/2\) the two-site pattern controls the transition. [Lean comparisons of the two-, three- and four-site energy bounds](../formal/cogentic/Cogentic/RandomizedStableEnergy.lean)

### Uniform relative error and the transition profile

For a stable limiting symbol as above, the threshold for the **maximum relative error of individual image masses**, uniformly over shifts, is
\[
               B\sqrt{\frac{\log n}{\pi e(h)}}.
\]
At a fixed factor above it, the short-vector cluster sum already proved gives \(\Theta_{K^*}(\sigma)-1=o(1)\). Fiber Poisson summation then gives \(A(y)=1+o(1)\) uniformly in every image point and shift. At a fixed factor below it, with \(\sigma\) equal to that factor times the displayed width, take zero shift and the zero image point. There all phases are one. The \(n-O(\log n)\) interior translates of an energy-minimizing pattern contribute in total \(\gg n\exp[-\pi(\sigma/B)^2(e(h)+o(1))]\), which diverges. The normalizing factor \(\mathbb E_Q A\) is \(1+o(1)\) here: the exact Gaussian mass ratio is the ratio of the shifted Poisson corrections for the ambient integer lattice and fixed-rank projected lattice, both \(1+o(1)\) at this width. The factor of \(\sqrt2\) relative to the total-variation threshold comes from taking the first power of the dual weights rather than their squares.

Uniform relative accuracy persists after restricting to any common nonempty event in the image, by dividing by its total mass under each law. In particular, for polynomial pairs with all roots in a fixed disk of radius \(s<1\) the upper width \(C_{r,s} B\sqrt{\log n}\) is uniform without passing to a limiting symbol: the singular-value bounds give a product of one-dimensional theta sums directly. For a full coefficient parity translate use \(\sigma/2\) as the width in this test. These estimates concern approximation of the full image and its image-constrained versions; they also give the corresponding sufficient width for the Gaussian comparison in the wide pair estimate.

For the family \(H_n=BX^r+1\) there is an explicit profile inside the narrower total-variation transition. Assume \(B/\log n\to\infty\) and
\[
        \pi(\sigma/B)^2=(\log n+c)/2,\qquad \lambda=e^{-c/2},
\]
with \(c\) fixed. Then, writing \(\Phi\) for the standard normal distribution function,
\[
          d_{\rm TV}\ \longrightarrow\ 2\Phi(\lambda/\sqrt2)-1
\]
uniformly in the center. Put \(t=\lambda/\sqrt n\), \(m=n-r\). Since \(G_n=I+O(1/B)\) in operator norm, replace the Fourier amplitudes \(\exp(-\pi(\sigma/B)^2 k^tG_n k)\) by \(t^{\|k\|^2}\), preserving their linear phases. The squared \(L^2(Q)\) error tends to zero. On the diagonal of the grouped second-moment argument, the squared weights have bounded mass and bounded fixed moments of \(\|k\|^2\): this follows by differentiating, or expanding, the product theta sums at parameter \((1-O(1/B))(\log n+c)\). The mean-value bound for the change of amplitude therefore costs \(O((\log n/B)^2)\). For the off-diagonal use \(e^{-a\|k\|^2}\) to dominate both amplitudes, \(a=(1-O(1/B))(\log n+c)/2\). At a difference \(d=M^tz\), summing the two majorants costs at most \(O(1)\exp(-a\|d\|^2/2)\) by completing the square. As \(\|Pz\|^2\asymp\|d\|^2/B^2\), combining this with the projected dual Gaussian leaves \(\sum_{0\ne z\in\mathbb Z^n}\exp(-c_0\sigma^2\|z\|^2)=o(1)\).

If \(\theta_j\) are the rotated phases of the dual basis characters under the ideal law, the substituted series factors as \(\prod_{j=1}^m(1+2t\cos\theta_j+O(t^4))\). Its logarithm is
\[
 2t\sum_{j=1}^m\cos\theta_j-2t^2\sum_{j=1}^m\cos^2\theta_j+o(1)
\]
with a uniform remainder. At each fixed moment order every noncanceling character has kernel component of norm \(O(1/B)\) and nonzero integer lift, so its projected frequency lies at distance at least \(1-O(B^{-2})\) from \(L^*\). Its expectation is \(O(\exp(-c_0\sigma^2))\), uniformly even after the rotations. The error summed over any fixed number of moment indices tends to zero. The normalized cosine sum therefore has the independent uniform-circle limit by the method of moments, and the mean cosine square tends in probability to \(1/2\). The logarithm converges in distribution to \(N(-\lambda^2,2\lambda^2)\). The original density has the same lognormal limit by the \(L^2\) comparison and the ambient normalization. Integrating the bounded positive part \((1-dP/dQ)_+\) gives the stated profile.

## How many narrow Gaussian shifts approximate the full image?

Let \(K,L,\pi\) be the stable fixed-degree lattices above, \(m=n-r\). All input centers now have the same projection onto \(L_{\mathbb R}\). Allow at most \(M\) such centers with arbitrary probability weights, and compare the resulting image mixture with the ideal Gaussian \(Q\) of width \(\sigma\) at the common projected center. Suppose
\[
 \sigma/\sqrt{\log n}\to\infty,\qquad B/(\sigma\sqrt{\log n})\to\infty.
\]
Write \(D_m=\log\det K-m\log\sigma-m/2\), using natural logarithms and Gaussian weight \(\exp(-\pi\|x\|^2/\sigma^2)\). For fixed real \(a\), if
\[
                    \log M=D_m+a\sqrt{m/2}+o(\sqrt m),
\]
the infimum total variation over the centers and weights tends to \(\Phi(-a)\). Independent uniform shifts on \(K_{\mathbb R}/K\), with equal weights, attain this limit in expectation. This quantifies the number of shifts for approximation of the full image.

For the lower bound, choose \(b_n\to\infty\) with \(b_n=o(\sqrt n)\) dominating the absolute remainder in \(\log M\). For each component retain the atoms of the ambient integer Gaussian with log mass at least
\[
            l_n=-n\log\sigma-n/2+a\sqrt{n/2}+b_n .
\]
This set has at most \(e^{-l_n}\) elements and asymptotic probability \(\Phi(-a)\) uniformly in its center. Indeed the coordinates are independent. One-dimensional Poisson summation and its first three scale derivatives give the continuous-Gaussian mean \(1/2\) and variance \(1/2\) for \(\pi(X_j-c_j)^2/\sigma^2\) up to \(O(e^{-c\sigma^2})\), and a bounded absolute third centered moment. The Berry–Esseen bound is uniform, and \(ne^{-c\sigma^2}=o(1)\). The exact ambient log normalizer is \(n\log\sigma+o(1)\). Meanwhile every \(Q\)-atom is at most \((1+o(1))/(\sigma^r\det K)\), by Poisson summation in fixed rank, since \(L^*\) is integral and \(\det L=1/\det K\). The union of the projected retained sets has \(Q\)-probability at most \(M e^{-l_n}(1+o(1))/(\sigma^r\det K)=o(1)\), and mixture probability at least \(\Phi(-a)-o(1)\). [Finite mixture bound for arbitrary weights in Lean](../formal/cogentic/Cogentic/RandomizedFiniteSupportTV.lean)

For the matching construction take independent shifts \(C_i\) uniform on the kernel torus with Haar probability. For an image point \(y\), the relative fiber mass before ambient normalization is
\[
 A_i(y)=\det K\,\sigma^{-m}\sum_{v\in K}
            \exp(-\pi\|\xi_y+v-C_i\|^2/\sigma^2),
\]
where \(\xi_y\) is the kernel offset of any lift relative to the fixed center. Tiling shows \(\mathbb E A_i(y)=1\) and the law in the random shift is independent of \(y\). The actual image density relative to \(Q\) differs from \(A_i\) by a factor \(1+o(1)\) uniformly in the shift, by the ambient and projected normalizers. Truncate each weight at the event \(A_i\le M e^{-b_n}\), setting it to zero otherwise. The variance of their truncated average is at most \(e^{-b_n}\), since the truncated second moment is at most \(M e^{-b_n}\mathbb E A_i\). The expected deficit of the averaged density below one is bounded by \(e^{-b_n/2}+\mathbb E[A_i\mathbf 1_{A_i>M e^{-b_n}}]+o(1)\), also after integration against \(Q\).

Size-biasing the uniform offset by \(A_i\) gives the continuous Gaussian \(Z\) on \(K_{\mathbb R}\) reduced modulo \(K\). At that offset the log weight equals
\[
        \log\det K-m\log\sigma-\pi\|Z\|^2/\sigma^2+o_{\mathbb P}(1).
\]
Indeed the expectation of the sum of the square roots of the other translates' density ratios to that of \(Z\) equals \(\sum_{v\ne0}\exp(-\pi\|v\|^2/(4\sigma^2))\). The least singular value of the kernel basis is \(\gg B\), so a product theta sum bounds this by \(o(1)\). The normalized squared length \(2\pi\|Z\|^2/\sigma^2\) is chi-squared with \(m\) degrees of freedom. Its central limit theorem gives missing mass \(\Phi(-a)+o(1)\), as required.

One may replace \(\log\det K\) here by \(m\log B+O_{r,s}(1)\) if all normalized roots have modulus at most a fixed \(s<1\). Divide the multiplication matrix by its signed leading coefficient and use the last \(m\) rows as a square triangular block \(T\) with unit diagonal. Its inverse is a truncated convolution by the coefficients of \(\prod_{j=1}^r(1-z_j t)^{-1}\), whose absolute sum is bounded by \((1-s)^{-r}\). The remaining \(r\) rows \(R\) have bounded operator norm. The determinant correction is \(\det(I_r+R(T^*T)^{-1}R^*)^{1/2}\), between one and a constant depending only on \(r,s\).

## Additive noise at different digit resolutions

Take \(H=B X^r+1\) with \(B\) a positive integer tending to infinity, \(r\) fixed, and \(n\to\infty\). Let the coefficients be independent integer Gaussian variables of width \(\sigma\) with arbitrary centers \(c_i\). In the convention used above a continuous Gaussian of width \(s\) has density proportional to \(\exp(-\pi\|x\|^2/s^2)\). In the orthogonal image add an independent continuous Gaussian of width \(\tau>0\). The comparison law is the continuous Gaussian centered at \(Pc\) of width \((\sigma^2+\tau^2)^{1/2}\), where \(P\) is orthogonal projection to the image.

The \(r\) image coordinates have disjoint chains. Indeed orthogonality to each multiplication column \(e_i+B e_{i+r}\) gives \(z_{i+r}=-z_i/B\). An orthonormal basis for the image therefore gives the \(j\)-th projected coordinate as
\[
 Y_j=a_j\sum_{\ell=0}^{L_j-1}(-B^{-1})^\ell Z_{j,\ell},
 \qquad a_j=\left(\sum_{\ell=0}^{L_j-1}B^{-2\ell}\right)^{-1/2},
\]
where \(L_j\) is the number of ambient coefficients in that chain and \(Z_{j,\ell}\) denotes the corresponding coefficient. The chain lengths differ by at most one and \(a_j=1+O(B^{-2})\). The spacing of the exact \(j\)-th image lattice is \(a_j B^{-(L_j-1)}\). All assertions below are uniform in the coefficient centers.

**Coarse noise.** Suppose \(\sigma\to\infty\) and \(B\tau\to\infty\). Then total variation tends to zero exactly when \(\tau^2+\sigma^2/B^2\to\infty\). If \(\tau^2+\sigma^2/B^2\to s_0^2\) with \(0<s_0<\infty\), the limit is
\[
 \frac12\int_{[0,1]^r}
 \left|\prod_{j=1}^r\Theta_{s_0}(x_j)-1\right|\,dx,\qquad
 \Theta_s(x)=\sum_{h\in\mathbb Z}e^{-\pi s^2 h^2} e^{2\pi i h x}.
\]
If \(s_0=0\), the limit is one.

Here is the coupling used both here and below. An integer Gaussian of width \(\sigma\ge1\) and the corresponding continuous Gaussian can be coupled with expected absolute distance \(O(1)\), uniformly in the center. Round the continuous Gaussian to the nearest integer. The centered first absolute moment of the difference between the rounded weights and the sampled Gaussian weights is \(O(1/\sigma)\): integrate the second-derivative Taylor remainder on each rounding cell and sum with weight \(1+|k-c|\). Indeed the normalized second derivative is bounded on each cell by \(O(\sigma^{-3}(1+((k-c)/\sigma)^2)e^{-c_0((k-c)/\sigma)^2})\) for a positive absolute \(c_0\). The sampled Gaussian normalization differs from the continuous one by an exponentially small relative error by Poisson summation. Transport unmatched weights through the common center and add the rounding cost. For a coupling in the fixed-dimensional image, convolution by width-\(\tau\) Gaussian noise converts expected distance \(d\) to total variation at most \(O(d/\tau)\), by integrating the gradient of the noise density along the translation.

In the coarse regime replace all digits with \(\ell\ge1\) by continuous Gaussians at total variation cost \(O((B\tau)^{-1})\). In coordinate \(j\) the resulting law is an integer Gaussian on spacing \(a_j\) convolved by a Gaussian of squared width \(b_j^2=\tau^2+\sigma^2 a_j^2\sum_{\ell\ge1}B^{-2\ell}\). Its continuous comparison is exactly the law stated above. Completing the square and using one-dimensional Poisson summation gives a density ratio equal to \(\Theta_{s_j}\) at an affine phase, divided by the sampled Gaussian normalizer relative to the continuous one, where
\[
 s_j^2=\frac{\sigma^2 b_j^2}{a_j^2\sigma^2+b_j^2}.
\]
The relative normalizer is \(1+o(1)\). If \(\tau^2+\sigma^2/B^2\to\infty\), also \(s_j\to\infty\), and the theta ratio converges uniformly to one. For a finite positive limit \(s_0\), \(s_j\to s_0\). In output units of \(a_j\) the phase slope is \(a_j^2\sigma^2/(a_j^2\sigma^2+b_j^2)\), which tends to one in this case. Under the broad continuous comparison, the phases modulo one converge jointly to independent uniform phases by the Gaussian Fourier formula, uniformly in their translations. This gives the integral. If \(s_0=0\), the replaced law concentrates in shrinking neighborhoods of the shifted lattice from its leading digits, while the broad continuous comparison assigns these neighborhoods vanishing mass. Every bounded subsequence of the squared widths has a further finite-limit subsequence, which proves the necessity in the coarse assertion.

**Growing digit resolution.** Put \(L=\min_j L_j\) and, for \(0<\tau<1\), put \(K=\min(L,\log_B(1/\tau))\). Suppose
\[
 K\longrightarrow\infty,\qquad
 B/\log K\longrightarrow\infty,\qquad
 \sigma/\sqrt{\log n}\longrightarrow\infty .
\]
For every fixed \(\epsilon>0\) the total variation tends to zero above the width \((1+\epsilon)B\sqrt{\log K/(2\pi)}\) if \(\tau B^{L-1}\to\infty\). It tends to one below \((1-\epsilon)B\sqrt{\log K/(2\pi)}\). The terminal condition is necessary for total variation to tend to zero at any width in these hypotheses. A chain of length \(L\) has an exact lattice character of frequency \(B^{L-1}/a_j\). Its expectation after adding noise has magnitude \(\exp(-\pi\tau^2 B^{2(L-1)}/a_j^2)\), whereas the continuous comparison expectation tends to zero. Any subsequence on which \(\tau B^{L-1}\) stays bounded therefore has a positive total variation lower bound.

For the upper bound keep the first \(\min(L_j,\lceil\log_B(1/\tau)\rceil+2)\) digits of each chain. Coupling replaces the rest by continuous Gaussians at total variation cost \(O(B^{-1})\) or less, by summing the discarded geometric coefficients and dividing by \(\tau\). The kept chain, rescaled to have a unit image vector, is the monomial-kernel law above with degree parameter one and chain length \(K+O(1)\). The no-noise total variation upper estimate puts it within \(o(1)\) of the ideal image-lattice Gaussian. Undoing the scalar normalization gives that Gaussian width \(\sigma\) times the norm of the kept coefficient list. Its spacing in the original output coordinate is \(a_j B^{-(\text{kept length}-1)}\). The added noise width divided by this spacing tends to infinity. For chains cut before their ends this follows from the two extra digits, and for chains kept in full it follows from the terminal condition. Completing the square as in the coarse calculation converts the ideal image-lattice Gaussian with this noise to its continuous comparison in \(o(1)\) total variation. The effective conditional width divided by the spacing tends to infinity since both the noise width and the kept Gaussian width do so after division by that spacing. The continuous widths of kept and discarded digits combine to \((\sigma^2+\tau^2)^{1/2}\) exactly since the chain coefficient list has norm one. There are only \(r\) chains.

For the lower bound it suffices to use one chain, with at least \(K-O(1)\) frequencies of the form \(B^i/a_j\) for integers \(0\le i\le \min(L_j-2,\lfloor\log_B(1/\tau)\rfloor-2)\). The first \(i+1\) digit coefficients in that character are integers and vanish from the phase of the discrete sum. The fractional coefficient vector \(f_i\) starts at the next digit and has first magnitude \(1/B\) followed by a finite geometric tail. Thus
\[
 \|f_i\|^2=B^{-2}(1+O(B^{-2})),\qquad
 |\langle f_i,f_{i'}\rangle|\ll B^{-3}\quad(i\ne i').
\]
Rotate each phase by the negative of its fractional center phase and take its real part \(T_i\). For any fractional frequency \(|f|\le1/4\), Poisson summation gives the expectation of the character of a single centered discrete digit as \(e^{-\pi\sigma^2 f^2}(1+O(e^{-c_1\sigma^2}))\), with a positive absolute \(c_1\), uniformly in the original center. The frequencies \(f_i\pm f_{i'}\) stay in that range for large \(B\). Multiplying the digit estimates has uniform relative error \(o(1)\) by \(\sigma/\sqrt{\log n}\to\infty\). For all the retained frequencies, \(\tau B^i/a_j\ll B^{-2}\), so the noise also multiplies both the one- and two-character expectations by \(1+o(1)\). Let \(t=e^{-\pi\sigma^2/B^2}\). Since \(\sigma^2/B^2=O(\log K)\) in the lower regime and \(B/\log K\to\infty\), these calculations give, uniformly in the retained indices,
\[
 \mathbb E T_i=t(1+o(1)),\qquad
 \mathbb E(T_iT_{i'})=t^2(1+o(1))\quad(i\ne i').
\]
The second identity uses the two signed combinations of the phases and the inner product estimate. The sum of \(K-O(1)\) real parts has mean \((1+o(1))Kt\) and variance \(O(K)+o(K^2t^2)\). For the continuous comparison the same character combinations have nonzero frequencies of magnitude at least a fixed constant. Their expectations are \(O(e^{-c_2\sigma^2})\) for a positive absolute \(c_2\). Thus under the continuous law the mean is \(o(1)\) and the variance is \(O(K)\). Below the claimed width \(Kt^2\to\infty\), so the test at threshold \(Kt/2\) distinguishes the two laws with both error probabilities tending to zero. This proves the lower bound. These growing-resolution assertions leave the window with bounded terminal smoothing and the critical-width profile open.
