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
