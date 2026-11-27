# Absolute summation of the two evaluation frequencies

Let \(X=V^d\), \(b_i\asymp V\) be distinct primes, and \(h=d-2\), with \(d\to\infty\) and \(\log\log X=o(\log V)\). Consider the two evaluation frequencies with the conductor and counting properties (1)–(2) of the discrete major-arc count. In a fixed top band suppose \(X_i=X^{1+o(1)}\), \(m_i=V^{O(1)}\), \(L_i=X_i/m_i\), \(L_i/b_i^h\ge V^{1-\epsilon-o(1)}\), and the digit count \(M=2S+1\le V^{\epsilon+o(1)}\). Here \(0<\epsilon<1/6\) is fixed. The endpoint \(X_i\) includes a polylogarithmic marginal tail cutoff. Densities, endpoint and multiplicity losses below are uniform in the band. [Frequency construction and exact counting bound](keybreak-dual-major-arc-count.md)

Let each test be either ordinary smoothness on the nonzero integers or the constant one. Assume the normalized single-progression estimates in the cited major- and minor-arc notes at these endpoints and smoothness cutoffs, on every translate of the period. Normalization here means division by \(L_i\). Only absolute estimates are needed when the reference probability of interest is at least \(V^{-o(1)}\). Then the combined nonzero Fourier contribution on **Cartesian progressions**, before insertion of the Gaussian, is at most
\[
 V^{-(1-3\epsilon+\epsilon^2)+o(1)}+O(X^{-c})
\]
for some fixed \(c>0\). More precisely this bounds the sum over short modes of the products of the two per-coordinate supremums over intervals in the capped box. Each Fourier weight is at most one. [Major-arc prefix bound](keybreak-smooth-major-arc-progressions.md) · [Minor-arc prefix bound](keybreak-smooth-minor-arc-probes.md)

## A uniform count down to the first occupied height

Write \(T_i(s)=\min_{(a,q)=1}q(1+L_i\|\beta_i(s)-a/q\|)\). For the moment suppress the index \(i\), put \(t=\log_b T\), and \(\ell=\log_b(L/b^h)\). In the valuation group \(v\) of the discrete count, the number of free digits is \(e=h-k_v+\min(v,k_v)\). If \(k_v=h\), then \(e\le v\le t\). If \(k_v<h\), maximality gives \(2T^2 b^{k_v+1}\ge L b^v\), including when \(k_v=0\). Thus
\[
 e\le h-k_v+v\le 2t-\ell+1+\log_b2.
\]
There are at most \(h+1=V^{o(1)}\) groups. Since \(\ell\ge 1-\epsilon-o(1)\), the one-coordinate count is at most
\[
 V^{\epsilon^2+o(1)} T^{2\epsilon+o(1)}.
\]
This holds uniformly in \(T\ge1\). The second little-oh term allows the base \(b\asymp V\) and the digit count \(M\le V^{\epsilon+o(1)}\) to vary. By the exact conductor lower bound every nonzero mode has \(T_i(s)\ge V^{1-\epsilon-o(1)}\) in both coordinates.

## Summation with one cutoff

Use the threshold \(X^{1/3}\). If one height reaches it, the minor-arc estimate in that coordinate gives \(X^{-1/6+o(1)}\), understood with an arbitrarily small fixed loss. Indeed any approximant to a shifted frequency \(\theta+j/m\) induces an approximant to \(\beta=m\theta\) of at most the same denominator. Its residual times \(L_i\) is at most the original residual times \(X_i\). This gives the height criterion for every shift in additive orthogonality. The other normalized interval sum is \(O(1)\). There are at most \(M^h=X^{\epsilon+o(1)}\) modes. For the constant test the geometric bound is even smaller, because \(1+L_i\|\beta_i\|\ge T_i\).

For both heights below \(X^{1/3}\), the major-arc prefix estimate at the minimizing approximant is, after normalization,
\[
 V^{o(1)}T_i^{-1/2+o(1)}
      + X^{-1/6+O(\tau)+o(1)} .
\]
Indeed \(\Psi(X_i/g,y)\le X_i/g\), and \(q^{-1}(1+D)^{-1/2}\le [q(1+D)]^{-1/2}\). The estimate permits any fixed \(\tau>0\). Apply it with an arbitrarily small amount of slack in the threshold exponent when \(X_i\ne X\). The aggregate error remains \(O(X^{-c})\) since \(\epsilon<1/6\). This argument also allows the constant test, by the interval bound \(O(\min(1,(T_i-1)^{-1}))\) after normalization.

Group by dyadic ranges \([T,2T)\) of the lesser height. Either coordinate can furnish the lesser height, so doubling the one-coordinate count suffices. In each bin the product of the two principal bounds is at most \(V^{o(1)}T^{-1+o(1)}\). The number of bins is \(O(\log X)=V^{o(1)}\). As \(2\epsilon-1<0\), the largest upper bound is at the first allowed scale, with exponent in base \(V\) at most
\[
 \epsilon^2-(1-\epsilon)(1-2\epsilon)
 =-(1-3\epsilon+\epsilon^2).
\]
At \(\epsilon=3/20\) the saving in this exponent is \(229/400\). The high-frequency power margin before arbitrary small losses is \(1/6-3/20=1/60\).

## Scope on Gaussian phases

For a Gaussian on each Cartesian support phase this interval estimate can be multiplied by the normalized two-dimensional variation of the Gaussian and the residual affine phase, by two-dimensional partial summation. A bound \(V^{a+o(1)}\) there permits any fixed \(a<1-3\epsilon+\epsilon^2\). The high-frequency \(X^{-c}\) term absorbs any such fixed power of \(V\). Uniform bounds per support phase combine with their positive ideal Gaussian masses. An image-event restriction allowing a common divisor retains the same counting estimate whenever division multiplies frequency by a unit modulo \(b_i^h\) and preserves the ratio \(X_i/m_i\). These two facts must be checked on the specified support before taking conditional expectations. [Image-event restriction](keybreak-thin-top-pairs.md#conditioning-on-the-public-root-and-dividing)

The twisted-Gaussian variation lemma gives this loss with \(a=2\zeta\) for angle sine \(\gg V^{-\zeta}\), marginal cutoff polylogarithmic in \(X\), and Mahalanobis frequency polylogarithmic in \(X\). Its explicit tail remains negligible after summing \(X^{\epsilon+o(1)}\) modes for a cutoff of at least \(\log X\). [Gaussian variation and lattice normalization](keybreak-gaussian-variation.md)

This estimate concerns ordinary two-coordinate tests. Applying it to a complexity theorem also requires the reference moment at the new field width, the geometric and one-point estimates, and the costs of any changed schedule.

