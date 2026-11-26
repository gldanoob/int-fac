# A limit on lower smoothness certificates from bounded prime tests

A polynomial in a bounded number of prime-divisibility tests per monomial cannot certify a useful lower mean for the smooth-event indicator on a broad marked progression. This holds for actual squarefree band products, with the existing Dirichlet RH input for their positive mean. The obstruction itself is an exact moment identity for the finite CRT product law. It applies to a pointwise lower certificate for the marked event, including a certificate justified by its logarithmic factor budget. [Scalar marked tests](cogentic-scalar-divisor-count.md#rectangles-for-a-pair-of-marked-values) · [Positive mean on the fixed grid](cogentic-intermediate-score-budget.md#dyadic-subboxes-and-the-linear-mass-term)

## An exact law supported on small hit sets

Let \(J\) be a finite set of primes, let \(\theta_p=1/p\), and suppose \(\sum_{p\in J}\theta_p<1\). Write \(\theta_A=\prod_{p\in A}\theta_p\). For any integer \(0\le m\le |J|\), define a weight on \(A\subseteq J\) by
\[
 \nu(A)=\theta_A
    \sum_{\substack{C\subseteq J\setminus A\\|C|\le m-|A|}}
                  (-1)^{|C|}\theta_C
 \quad (|A|\le m),
\]
with weight zero otherwise. Every weight is nonnegative. Indeed, if \(e_j\) is the \(j\)-th elementary symmetric sum in the \(\theta_p\) outside \(A\), then \((j+1)e_{j+1}\le e_j\sum_{p\notin A}\theta_p\). The terms \(e_j\) are decreasing, so pairing consecutive terms proves nonnegativity of each alternating truncation.

For any \(S\subseteq J\) of size at most \(m\), sum the displayed weights over \(A\supseteq S\) and group by \(U=(A\setminus S)\cup C\). For a fixed \(U\) the factor multiplying \(\theta_S\theta_U\) is \(\sum_{W\subseteq U}(-1)^{|U|-|W|}\). Only \(U=\varnothing\) remains. Thus
\[
                  \nu\{A\supseteq S\}=\theta_S .
\]
Taking \(S=\varnothing\) proves normalization. All moments involving at most \(m\) distinct prime flags agree exactly with independent Bernoulli variables of means \(\theta_p\), even as \(m\) grows. For squarefree tests, label each \(p\in A\) independently with a square hit of probability \(1/p\), and with an exact single hit otherwise. This gives the same joint moments of all products of tests \(p\mid n\) and \(p^2\mid n\) involving at most \(m\) distinct primes as independent uniform residues modulo the corresponding prime squares. The same follows for products using absence and exact-single-hit flags by linearity.

## Comparison with an actual progression

Let \(n_j=|c+qj|\) for \(0\le j<T\), with \(q\ne0\), and assume all \(n_j\ge X_->1\). Use primes \(J\subseteq(\sqrt B,B]\) coprime to \(q\). On a reduced scalar call, these are the remaining band primes after removing omissions and primes dividing the stride. Set
\[
 k=\left\lceil\frac{\log X_-}{\log B}\right\rceil.
\]
A squarefree \(J\)-smooth \(n_j\) must have at least \(k\) distinct hits, since a product of fewer than \(k\) eligible primes is below \(X_-\). Suppose \(m<k\) and, for the two-level flags, take
\[
 T\ge 8(B+1)B^{2m},\qquad \sum_{p\in J}1/p\le 3/4.
 \tag{1}
\]
For flags testing only \(p\mid n_j\), replace \(B^{2m}\) by \(B^m\).

Every flag configuration in the support of \(\nu\) occurs in this *same progression*. To prove it, force the designated single hits modulo \(p\), and square hits modulo \(p^2\). The index lies in a single CRT class modulo a product at most \(B^{2m}\) or \(B^m\) for binary flags. In its remaining \(R\) indices, exclude a hit at each supposedly absent prime. For each purported single hit, also exclude a second factor of that prime. Each exclusion removes at most \(R/p+1\) indices, since on the forced class the undesired congruence has one residue modulo \(p\). The exclusions are indexed by distinct primes. Altogether they remove at most \(3R/4+|J|\). By (1), \(R\ge 8(B+1)-1\), so some point remains.

Consider a polynomial \(F\) in these flags, with a fixed coefficient on each monomial and at most \(m\) distinct primes per monomial. Write it in monomials in the two divisibility flags and let \(W\) be the sum of the absolute coefficients in that expansion. Assume \(F\) is a lower certificate, meaning \(F(\mathrm{flags}(n_j))\le \mathbf 1_{\{n_j\text{ squarefree }J\text{-smooth}\}}\) for every \(j\) in this progression. All configurations of \(\nu\) occur at nonsmooth \(n_j\), so the \(\nu\)-mean of \(F\) is nonpositive. A divisibility monomial on the true interval counts a single CRT class, and its normalized discrepancy from the independent-prime moment is at most \(1/T\). As the latter moment equals the \(\nu\)-moment,
\[
                      \frac1T\sum_{j<T}F(\mathrm{flags}(n_j))\le W/T .
 \tag{2}
\]
The same argument permits soundness to be relaxed by an additive \(\epsilon\) at each point, at the cost of adding \(\epsilon\) to (2).

One can also permit slowly varying coefficients, as when an additional weight uses the actual logarithm of the marked value. Suppose the coefficient at each index has sum of absolute values at most \(W\), and the sum of their variations along the interval is \(K\). For \(\delta>0\), partition the consecutive indices into \(P=O(1+K/\delta)\) panels of internal total variation at most \(\delta\). This follows by greedily ending a panel before the next step would exceed \(\delta\), including when a single step exceeds \(\delta\). Freeze the coefficients at the first index of each panel. Within a long panel, the frozen certificate has upper error at most \(\delta\) on the actual indicator. Applying (2) there and unfreezing contributes at most \(2\delta+W/R\) to its mean, where \(R\) is the panel length. A panel shorter than \(T_{\min}=8(B+1)B^{2m}\) can instead be charged by its full weight, since the actual certificate is bounded above by one. Thus the overall upper bound is
\[
               2\delta+O\!\left((1+K/\delta)(W+T_{\min})/T\right).
 \tag{3}
\]
Use the binary version of \(T_{\min}\) when appropriate.

## Application to the fixed-schedule score

On a clean ordinary mark, fix a slope in one of the original broad affine boxes. Varying its intercept gives an actual unit progression at height \(\exp((100001+o(1))V)\), with \(T=\exp((100000+o(1))V)\) and \(\log B=(1000+o(1))H\). Mertens' prime reciprocal estimate gives \(\sum_{\sqrt B<p\le B}1/p=\log 2+o(1)<3/4\). In particular (1) applies to any fixed \(m\), and even to growing \(m\) with \(2m\log B\le (100000-\eta)V\) for any fixed positive margin \(\eta\). For binary flags use \(m\log B\) instead. These conditions also give \(m<k\). The same result holds on any actual lower-width unit slice that still meets (1) and \(m<k\). The argument requires no smooth-density estimate on such a shorter slice.

For the original broad slice the established Gaussian smooth-window estimate gives actual smooth fraction at least \(\exp(-O(H))\). Its Gaussian may be centered at the interval midpoint, with width \(|q|T/(10L_0)\) in physical units. The tail outside the slice is negligible, and the density comparison costs at most a polynomial in \(L\). But (2) is at most \(\exp(-(100000+o(1))V)\) for \(W=\exp(O(H))\). Under the fixed margin in (1), (3) also gives error below the actual smooth mass for \(W,K=\exp(O(H))\), by taking \(\delta=e^{-CH}\) for a sufficiently large fixed \(C\). This includes local estimates combined with a slowly changing logarithmic threshold whenever their flag-polynomial representation satisfies the stated norm and variation bounds. [Broad-slice density](cogentic-intermediate-score-budget.md#dyadic-subboxes-and-the-linear-mass-term) · [Individual smooth-window estimate](cogentic-dirichlet-smooth-windows.md#a-gaussian-distribution-in-progressions)

The linear term of the normalized mass in the true score needs positive lower control on the actual relation probability. A certificate built by lower-bounding each scalar smooth indicator by the local polynomials above loses the entire leading unconditioned mass even before a coefficient is fixed. The result concerns this entrywise construction. It leaves open a lower bound obtained jointly across different marks or fields, a certificate with additional arithmetic information about the projected values, and conditional estimators that need only upper-bound the full score without lower-bounding the scalar indicators.

An exact rational replay checked normalization, 632 subset moments and 7,494 labelled moments. An integer replay checked 75 realized patterns and the CRT count discrepancies across positive and negative strides.
