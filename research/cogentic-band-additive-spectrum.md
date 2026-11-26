# Additive cancellation for short windows of squarefree band products

Under RH for the Dirichlet \(L\)-functions, including the Riemann zeta function, actual squarefree band products give a two-mark estimate below a complete cofactor cycle even where the marginal counting norm gives no saving. On the fixed schedule take
\[
  49999.5<\tau<50000,\qquad \delta=\tau-49999.5,\qquad
  2-\delta<\kappa<2.
\]
The projected scalar windows have length \(\exp((\tau+o(1))V)\), and the cofactor average runs over \(\exp((\kappa+o(1))V)\) consecutive values. For one or two marks, replacing this average by a complete residue-cycle average after freezing the physical windows costs at most \(e^{-CH}\) for any fixed \(C\). The full-cycle estimator and finite score expansions then apply at these widths. [Original pooling and expansion](cogentic-cofactor-dispersion.md) · [Artificial-array obstruction](cogentic-cofactor-dispersion.md#a-correlation-missed-by-finitely-many-fourier-probes)

## Additive sums in a physical interval

Let \(X=\exp((100001+o(1))V)\) and \(W=\exp((1+\tau+o(1))V)\). Let \(J\) be the primes in \((\sqrt B,B]\) after polynomially many deletions in \(L=\log N\), and let \(\mathbf1_J(m)\) indicate a squarefree product of primes in \(J\). Fix a smooth cutoff \(0\le w\le1\) supported on \([X,X+W]\) and equal to one outside the two endpoint ramps of width \(W e^{-AH}\) within this interval. A fixed twice continuously differentiable transition extended by its constant endpoint values suffices, for example \(10t^3-15t^4+6t^5\) on \(0\le t\le1\) with extension by zero on the left and one on the right. Its derivatives in \((x-X)/W\) through order two are \(e^{O_A(H)}\).

Write \(e(t)=\exp(2\pi i t)\) and \(Q=\lfloor W/\sqrt X\rfloor=\exp((\delta+o(1))V)\). For a rational \(\alpha\) of reduced denominator \(Q<d\le\exp((1+o(1))V)\),
\[
   \frac1W\left|\sum_m \mathbf1_J(m)w(m)e(\alpha m)\right|
     \le \exp((-\delta/2+o(1))V).                       \tag{1}
\]
The bound is uniform in the numerator and window origin. It also holds with a restriction to any one class modulo \(s=e^{O(H)}\) if every shifted frequency \(\alpha+\ell/s\) has denominator larger than \(Q\). This follows from additive orthogonality, including for nonunit classes.

Choose a reduced approximation \(a/r\), \(1\le r\le Q\), with \(\beta=\alpha-a/r\) and \(|\beta|\le1/(rQ)\). Since \(d>Q\),
\[
   |\beta|\ge 1/(dr),\qquad
   |\beta|W\ge \exp((49999.5+o(1))V).                    \tag{2}
\]
For each \(b\mid\operatorname{rad}(r)\) composed of primes in \(J\), split off terms with \(\gcd(m,\operatorname{rad}(r))=b\). Write \(m=bm'\). Then \(m'\) is a squarefree band product with all prime factors of \(r\) deleted, hence a unit modulo \(r/b\). Expand \(e(am'/(r/b))\) in multiplicative characters on that group. The sum of the absolute coefficients is at most \(\sqrt{\varphi(r/b)}\le\sqrt r\) by Parseval. The number of \(b\)'s is \(e^{o(V)}\) by the divisor bound.

For each character the remaining weight is \(w(bx)e(b\beta x)\). Put \(X'=X/b\) and \(\rho=W/X\). Its Mellin transform \(M(s)=\int_0^\infty w(bx)e(b\beta x)x^{s-1}\,dx\) satisfies
\[
 M(\sigma+it)=(X')^{\sigma+it}e(\beta X)\rho
       \int G_\sigma(v)e^{i\rho(t+2\pi\beta X)v}\,dv,
 \qquad
 G_\sigma(v)= e^{\sigma\rho v} w(Xe^{\rho v})
           e\big(\beta X(e^{\rho v}-1-\rho v)\big),
\]
by \(x=X'\exp(\rho v)\). The support of \(G_\sigma\) has bounded length. For \(0\le j\le2\) and \(1/2\le\sigma\le2\), its \(j\)-th derivative norms in \(L^1\) and \(L^2\) are at most \(e^{O_A(H)}U^j\), where \(U=1+|\beta|W^2/X\). The residual phase and its first two derivatives are \(O(|\beta|X\rho^2)\) there. Cauchy–Schwarz with weight \(1+(\xi/U)^2\), then Plancherel for \(G_\sigma,G'_\sigma\), gives
\[
       \int_{\mathbb R}|M(\sigma+it)|\,dt
         \ll (X')^\sigma e^{O_A(H)}\sqrt U.              \tag{3}
\]
Integrating twice by parts bounds the pointwise transform by \((X')^\sigma\rho e^{O_A(H)}\min(1,(U/|\rho(t+2\pi\beta X)|)^2)\).

Use the squarefree Euler product \(F_\chi\) on \(\sigma_0=1/2+D_0\log L/\log B\), with the fixed constant \(D_0\) from the individual character estimate. For \(B\le |t|\le X^5\) and \(\sigma_0\le\sigma\le1\), the individual character estimate bounds every product. For the principal character, integrate its prime main term by parts to get \(O(B^{1-\sigma}/(|t|\log B))\) for the logarithm, up to the error in that estimate. For \(1\le\sigma\le2\), the elementary absolute bound is \(\log|F_\chi|\le\sum_{\sqrt B<n\le B}n^{-1}=O(\log B)\). All conductors and heights used in the individual estimate have logarithms \(O(V)\) and deleting the prime factors of \(r\) costs \(O(V)\) primes at most. [Individual character estimate](cogentic-dirichlet-smooth-windows.md#an-individual-character-estimate)

Start Mellin inversion on \(\sigma=2\) and truncate at \(|t|=X^5\). Shift to \(\sigma_0\) when \(B\le|t|\le X^5\), retaining \(\sigma=1\) for \(|t|\le B\) and connecting horizontally at \(\pm B\). Both factors are entire. The pointwise bound just proved gives the original tails and high horizontals error \(\exp(-\Omega(V))\) in absolute count units. For example the tail integral on \(\sigma=2\) costs at most \(O((X')^2 e^{O_A(H)}U^2/(\rho X^5))\). On the low vertical and low horizontals, \(|\rho(t+2\pi\beta X)|\gg|\beta|W\) by (2), and \((X')^\sigma\rho\le W\). Their integrals cost
\[
     W e^{O_A(H)}\big(1/(|\beta|W)+\rho\big)^2
           =\exp(-\Omega(V)).
\]
Here the factor \(B\) from the low vertical is included in \(e^{O_A(H)}\). Thus (3) bounds each twisted character sum by \((X')^{\sigma_0}e^{O_A(H)}\sqrt U\) up to an exponentially small absolute error. Finally
\[
 \sqrt{rU}\le\sqrt{r+(Q+1)^2/Q}\ll\sqrt Q,\qquad
 X^{\sigma_0}=X^{1/2} e^{O(H)}.
\]
Summing over \(b\) and dividing by \(W\) proves (1).

## Incomplete cofactor averages

Use the scalar residue splits and endpoint freezing of the existing whole-score reduction. After a projection, sign change or division by an eligible prescribed factor, the physical step is \(q=sn_a\), \(s=e^{O(H)}\), and the cofactor step is \(S=R_a s_0\), where \(|s_0|=e^{O(H)}\) and \(\gcd(R_a,n_a)=1\). Set \(v=\gcd(S,q)=e^{O(H)}\) and \(n=q/v\). The physical orbit is \(m\equiv c\bmod v\), with
\[
        (m-c)/v\equiv u k \pmod n,\qquad u=S/v\bmod n
\]
a unit. Here \(k\) is the consecutive index within the retained cofactor class, still of interval length \(K=\exp((\kappa+o(1))V)\). Prime deletions enforce the unit-mark constraint as before. The frozen physical interval is half-open and has length \(W=qT\), where \(T\) is the projected scalar length. Its pointwise endpoint replacement error is \(e^{-\Omega(V)}\) by the old comparison, since the original cofactor shifts are at most \(\exp((10003+o(1))V)\). [Projection and unit splits](cogentic-cofactor-dispersion.md#the-whole-score-below-a-cofactor-cycle)

Let \(f_i(k)\in[0,1]\) be the frozen, smoothed progression fraction. The smoothing costs \(e^{-CH}\) for both incomplete and full-cycle means, for \(A\) sufficiently large. Each physical integer is visited in at most one orbit class, of probability at most \(1/n+1/K\). There are \(O(W e^{-AH}/v+1)\) integers in the ramps in the reachable class, and the count is normalized by \(T=W/(vn)\). Telescoping preserves the error bound in a product of two fractions.

Write \(\widehat f_i(j)\) for the normalized Fourier coefficient on period \(n_i\), with either fixed sign convention. It is \(1/(n_iT_i)\) times an additive sum of (1) in the reachable class. The phase is \(e(\pm j u_i^{-1}(m-c_i)/(v_i n_i))\). After additive orthogonality shifts by \(\ell/v_i\), multiplying the frequency by \(v_i\) gives \(\pm j u_i^{-1}/n_i\bmod1\). Every shifted denominator is therefore at least the reduced denominator of \(j/n_i\), and at most \(v_i n_i\). Since \(W_i/(n_iT_i)=v_i=e^{O(H)}\), (1) gives
\[
     |\widehat f_i(j)|\le\exp((-\delta/2+o(1))V)
       \quad\text{if the denominator of }j/n_i\text{ exceeds }Q_i.       \tag{4}
\]
Parseval also gives \(\sum_j|\widehat f_i(j)|^2\le1\).

For two distinct marks define \(D_{j_1,j_2}\) to be zero when \(j_1/n_1+j_2/n_2\) is integral, and otherwise to be the interval mean of \(e(k(j_1/n_1+j_2/n_2))\). This equals the interval mean minus the full-cycle mean on the Fourier basis. Each row and column has absolute sum \(O(1)\). The other frequencies are spaced \(1/n_i\) apart, so the geometric bound, leaving the nearest term bounded by one, gives \(O(1+n_i\log(2n_i)/K)\). The total absolute sum is \(O(n_1n_2\log(2n_1n_2)/K)\), since each frequency on the joint cycle occurs \(\gcd(n_1,n_2)\) times and the nonzero frequency bound is \(O(1/(K\|\theta\|))\).

For pairs with at least one high frequency as in (4), apply Cauchy–Schwarz with weights \(|D|\), using the total absolute sum for the high factor and the row or column bound and Parseval for the other factor. The total contribution is at most
\[
       \exp\!\left(\left((2-\kappa-\delta)/2+o(1)\right)V\right).
\]
For the remaining pairs the nonzero sum frequency has distance at least \(1/(Q_1Q_2)\) from the integers. There are at most \(Q_i\) times the divisor count of \(n_i\) low frequencies per mark, or \(\exp((\delta+o(1))V)\). Parseval bounds the product of the two low-frequency coefficient absolute sums by \(\exp((\delta+o(1))V)\). Their total contribution is at most \(\exp((3\delta-\kappa+o(1))V)\). Both errors are \(e^{-\Omega(V)}\) in the stated range. For one mark, complete orbits plus the remainder give the interval comparison \(O(n/K)\) directly. A repeated mark uses one Boolean test with the combined omissions and prescribed divisibility conditions.

## Score and width limits

Apply the full cycle only to the frozen average on each retained projection panel and cofactor residue split. The small CRT classes used by the existing score expansions are imposed within the incomplete box before this replacement, with their exact weights. Conditional on such a class, the full-cycle pooled scalar intervals have physical length \(\exp((1+\tau+o(1))V)\) and modulus \(e^{O(H)}\), by the original pooling proof and \(\gcd(n_{a_1},n_{a_2})\le |a_1-a_2|\). Their sharp scalar estimator applies with a strict square-root margin. The auxiliary unit tests, cofactor-dependent omissions and reference coefficients use the finite expansions in the previous whole-score reduction. The omitted tails are bounded on the actual incomplete cofactor interval, and each retained term is covered by the Fourier comparison. The number of weighted terms, their absolute coefficient sum and all precision and residue splits cost \(e^{O(H)}\). Increasing the endpoint and scalar precision absorbs these losses.

The estimator brings a low-mean score box below a complete cofactor cycle at \(\tau<50000\). In this range \(\tau+\kappa>50001.5\), so the shorter widths give no improved support-by-intercept scan exponent or final one-third selector.

A direct bilinear split illustrates the need for the oscillatory Mellin estimate. Order primes increasingly, stop the first factor at its first crossing of \(\sqrt X\), and fix its last prime \(p\). The two factors have separate coefficient functions, since every prime of the complement exceeds \(p\). On a dyadic first-factor range \(U_1\le u<2U_1\), Cauchy–Schwarz in the complement only sees first-factor differences \(h\ll U_1W/X\). Intersecting complement intervals have length \(O(W/U_1)\), and the geometric bound at difference \(h\) is the minimum of this length bound and \(O(\|\alpha h\|^{-1})\). At \(\alpha=1/n\) with \(n=\exp((1+o(1))V)\), the product of the maximum difference and the complement length is \(O(W^2/X)\ll n\). The bound then permits the full intersection length at every difference. Also, varying two fixed prefix blocks with combined product bounded by \(e^{O(H)}\) gives at most one admissible integer product per fixed complement, since the prefix interval has length \(O(e^{O(H)}W/X)=o(1)\).
