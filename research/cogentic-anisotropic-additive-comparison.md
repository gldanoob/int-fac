# One-sided Fourier comparison for unequal scalar windows

The [additive estimate for squarefree band products](cogentic-band-additive-spectrum.md) only needs to be applied to the wider scalar window. A direct count of frequencies with a given small denominator bounds all pairs involving a low frequency on that side. A separate abstract example shows that pointwise additive estimates, even with the finer dependence on the rational approximant, cannot improve the equal-width leading exponent on their own.

## Compare only the wider window to its spectrum bound

Use two scalar arrays \(f_i\in[0,1]\) after the endpoint and residue splits in the additive-spectrum argument. Their periods \(n_i\) have logarithms \((1+o(1))V\), and the cofactor interval has length \(K=\exp((\kappa+o(1))V)\). Assume the first physical window has \(Q_1=W_1/\sqrt{X_1}=\exp((\delta_1+o(1))V)\) with \(0<\delta_1<1/2\). Only this window needs the pointwise bound \(|\widehat f_1(j)|\le\exp(({-\delta_1/2}+o(1))V)\) at reduced denominators above \(Q_1\). The other array may have any spectrum.

For frequencies \(j_i/n_i\), let \(D_{j_1,j_2}\) be their summed-frequency mean on the interval minus its complete-cycle mean. As in the additive-spectrum argument it has absolute row and column sums \(O(1)\) for \(\kappa>1\), and total absolute sum \(O(n_1n_2\log(2n_1n_2)/K)\). Cauchy–Schwarz and Parseval bound the contribution with first denominator above \(Q_1\) by \(\exp(((2-\kappa-\delta_1)/2+o(1))V)\).

For the rest, fix a reduced denominator \(d\mid n_1\), \(d\le Q_1\). Extend its numerator set to all residues modulo \(d\). The sums \(a/d+j_2/n_2\) run over the grid of denominator \(\operatorname{lcm}(d,n_2)\), each with multiplicity \(\gcd(d,n_2)\). Integral frequencies have zero discrepancy, and the geometric bound on the others gives
\[
 \sum_{a\bmod d}\sum_{j_2\bmod n_2}|D_{a n_1/d,j_2}|
       \ll \frac{d n_2\log(2dn_2)}K .
\]
Summing over \(d\mid n_1\) up to \(Q_1\) and using the divisor bound gives \(\exp((1+\delta_1-\kappa+o(1))V)\). Both Fourier coefficients have magnitude at most one. Hence the total discrepancy is exponentially small in \(V\) when \(\kappa>2-\delta_1\), since \(\delta_1<1/2\).

Choose the wider of two supplied scalar windows for the first side. If the narrower pooled physical interval also clears the sharp square-root threshold, the existing full-cycle estimator then applies to the product. This proves the scalar comparison after small-modulus splits by applying the same argument to each retained class.

An ordinary coefficient rectangle with one narrow axis does not give such unequal inner projection rectangles. For projections \(z_i=x+a_i y\) at distinct positive marks, one has \(z_2-z_1=(a_2-a_1)y\) and \(a_2z_1-a_1z_2=(a_2-a_1)x\). If either original axis is narrow, either strip bound limits both sides of an axis-aligned inner projection rectangle to the narrow leading width, up to \(\exp(O(H))\) factors. The new scalar comparison therefore does not give an anisotropic whole-score descent by the existing inner-rectangle decomposition.

## Limits of pointwise approximant bounds

Fix \(0<\delta<1/2\) and \(1<\kappa<2-\delta\). There are arbitrarily large prime periods \(n_1,n_2\) with the same bounded nonzero difference, by bounded prime gaps and pigeonholing that difference. Write \(n=n_1\), \(Q=n^\delta\), and choose a prime \(r\in[Q/2,Q]\). Use the affine unit orbit \(k\mapsto rk\pmod{n_i}\) in both periods. These slopes can come from a common unit by CRT. [Maynard, Small gaps between primes](https://annals.math.princeton.edu/2015/181-1/p07)

Choose \(u_i=r^{-1}\pmod{n_i}\) so \(ru_i=a_i n_i+1\), and put \(M=\lfloor r/4\rfloor\). The physical frequencies corresponding to cofactor frequencies \(j/n_i\), \(1\le |j|\le M\), lie within \(1/(4n_i)\) of \(ja_i/r\). The latter rational has exact denominator \(r\). Any different rational \(a'/r'\) of denominator at most \(Q\) has distance at least \(1/(rr')\) from it, so its distance from the physical frequency is at least \(1/(2rr')\) for large \(n\), since \(Q^2=o(n)\). Consequently the pointwise Mellin envelope
\[
 Q^{-1}\sqrt{r'(1+Q^2|\alpha-a'/r'|)}
\]
is at least a constant times \(Q^{-1/2}\) on this entire band, for every such approximant. If the approximant is the same rational, its denominator \(r\asymp Q\) gives that lower bound directly.

There are signs \(\epsilon_j\in\{-1,1\}\) for which
\[
 P(t)=\frac{1}{C\sqrt{M\log n}}\sum_{j=1}^M\epsilon_j\cos(2\pi j t)
]
has supremum at most one and satisfies
\[
 \left|\sum_{k\bmod n_i}P(k/n_i)\chi(rk)\right|\ll\sqrt n
]
for both periods and every nonprincipal character, extended by zero off the units. For existence choose independent random signs and use the exponential moment bound for a Rademacher sum. For supremum control use a grid of spacing \(n^{-2}\), followed by the elementary derivative bound from the coefficient sum. For each character the coefficient of one sign before normalization is a combination of two Gauss sums, of magnitude at most \(\sqrt{n_i}\). Apply the same exponential moment bound to its real and imaginary parts and take a union bound over the grid and the \(O(n)\) characters, with sufficiently large fixed \(C\).

Remove the nonunit position in each prime period. This changes each Fourier coefficient by \(O(1/n)\), below the envelope even off the original band. It also changes means on \([0,K)\) for \(K=\lfloor n^\kappa\rfloor\) by \(O(1/n+1/K)\). On that interval the two polynomial arrays differ by \(O(MK/n^2)=o(1/\log n)\) by the Bernstein inequality for trigonometric polynomials. Their mean product is therefore \((2C^2\log n)^{-1}+o(1/\log n)\). Indeed the mean square of either polynomial on a complete period equals its continuous mean square, and the period remainder costs \(O(n/K)\). In a complete joint cycle the arrays have product mean \(O(n^{-2})\), by CRT and the zero constant term before removing the nonunit positions.

To turn these into integer progression counts, center each polynomial over its unit positions, scale it by a fixed fraction of the baseline density \(p=\exp(-O(H))\), and round in count units while preserving the principal total as in the [abstract cofactor array construction](cogentic-cofactor-dispersion.md#a-correlation-missed-by-finitely-many-fourier-probes). A window with \(\log T=(49999.5+\delta+o(1))V\) absorbs the rounding errors. The character deviation \(O(pT\sqrt n+n)\) fits the marginal allowance because its quotient by \(T\) has leading exponent at most \(1/2\), below the allowance exponent \(1-\delta\). The covariance difference, compared to the unperturbed baseline, is of order \(p^2/\log n\). Linear terms cost only \(O(p^2(n/K+1/n))\) because the individual polynomial means vanish on full periods before masking.

These arrays obey the marginal bounds and the sharper pointwise envelope for the high physical frequencies. They are abstract integer count arrays. They do not rule out cancellation from a stronger estimate for actual smooth products, such as a bound on their energy across a whole approximation band.
