# Independent panels for a shared Cogentic intercept

After freezing a slope, averaging the existing cofactor coordinate still leaves the two marked values coupled by the same intercept. On the conservative schedule their normalized projection is a diagonal strip of transverse width at most \(\exp((10002+o(1))V)\), whereas the residual intercept at the additive-spectrum cutoff has length \(\exp((\tau+o(1))V)\) with \(\tau>49999.5\). This gives an exact limit on reusing independent full-cycle panels for the final intercept. [Cofactor perturbation](cogentic-cofactor-dispersion.md#a-coefficient-that-varies-the-residue-at-every-mark) · [Additive-spectrum cutoff](cogentic-band-additive-spectrum.md) · [Shared cyclic intercept](cogentic-one-intercept.md#a-cyclic-distribution-and-two-affine-evaluations)

## The strip at two actual marks

Keep a slope value \(y\) and two distinct marks \(0\le a_1<a_2\le A\). Write \(n_i=m-a_i\) and \(R_i=R(a_i)\) for the nonnegative base-\(m\) digit polynomial \(R\) for \(N\). Divide the marked values by their signed intercept coefficients \(-gn_i\). Including translations in \(c_i\), the two normalized coordinates are exactly
\[
    U_i=x+t_i k+c_i,\qquad t_i=-R_i/n_i .
\]
The sign of a marked value is fixed on the box. Undoing the normalization, changing that sign, or dividing out a prescribed prime simply rescales the corresponding axis and smoothness test. Translating \(k\) to start at zero and subtracting \(c_i\) gives
\[
    U_2-U_1=(t_2-t_1)k,\qquad
    |U_2-U_1|\le D_*:=|t_2-t_1|(K-1)
\]
on an intercept interval of \(T\) consecutive values and a cofactor interval of \(K\) consecutive values.

The ratio \(R(a)/(m-a)\) is strictly increasing for \(a\ge0\) in this range. The numerator is nondecreasing, the denominator decreases, and \(R(a_2)>0\) since \(a_2\ge1\) and \(N>0\). Thus distinct marks define distinct projection directions. The bound \(R(a)\le dm A^{d-1}\) gives
\[
   D_*+1\le \exp((10000+\kappa+o(1))V)
   \quad\text{when }K=\exp((\kappa+o(1))V).
\]
The existing cofactor enlargement has \(\log K\le (2+o(1))V\). Subsequent cofactor descent only narrows the strip. Small residue splits may be made first: rescale both axes by the common intercept stride and use the consecutive indices in the two refined classes. The corresponding strides are \(e^{O(H)}\), so all leading exponents in the bound survive. Different fixed slopes or different fixed shifts in the cyclic sampler change the axis translations. [Scheduled heights](cogentic-deterministic-two-thirds.md#fixed-parameters) · [Sizes in the cofactor perturbation](cogentic-cofactor-dispersion.md#a-coefficient-that-varies-the-residue-at-every-mark)

Any axis-parallel rectangle inside the continuous strip in this calculation has side lengths at most \(2D_*\) in normalized coordinates. More generally, an independent product law supported inside the strip has projected support spans at most \(2D_*\), by fixing one point of the other support. When mapped back to physical values these spans are at most \(\exp((10003+o(1))V)\), since the intercept coefficients have size at most \(\exp((1+o(1))V)\). The pooled scalar counter at physical height \(\exp((100001+o(1))V)\) requires physical width exceeding its square root at leading scale. These short spans fail its width condition even with the small full-cycle moduli. For a single mark the entire projection has physical span at most \(gn_i(T+|t_i|K)\). If \(\log T=(\tau+o(1))V\) with \(\tau<49999.5\), this span has leading exponent at most \(\max(1+\tau,10003)<50000.5\). Thus short cofactor averaging cannot recover the pooled width condition below that intercept threshold even for one mark. [Pooled scalar threshold](cogentic-cofactor-dispersion.md#one--and-two-mark-counts) · [Sharp scalar counter](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli)

The exact common-intercept resonance is visible on these same projections. Use the origins with \(U_2-U_1=(t_2-t_1)k\). For every integer \(0<|j|<T\), each marginal has zero mean at frequency \(j/T\), by summing over the \(T\) consecutive intercepts. Yet the paired mean is
\[
    \mathbb E\,e^{2\pi i j(U_1-U_2)/T}
       =\frac1K\sum_{0\le k<K}e^{-2\pi i j(t_2-t_1)k/T}.
\]
Its distance from one is at most \(2\pi|j|D_*/T\). Hence there are on the order of \(T/(1+D_*)\) nonzero intercept frequencies with an exact \(x\)-resonance and an unsuppressed cofactor factor, including when \(K\) is a complete cofactor cycle. Completing the cofactor period does not remove this diagonal in the shared-intercept Fourier pairing.

## A lower bound for overlapping independent pools

Let \(P\) be the actual two-mark law under independent uniform \(x,k\) in the box. Consider any replacement by a positive mixture \(Q\) of \(J\) independent product laws for the two normalized coordinates. Suppose its error is at most \(\epsilon\le1/128\) on every rectangle tested by a pair of unary indicators, including arbitrary unions of coordinate intervals. Then
\[
                J\ \gg\ \frac{T}{1+D_*}.                         \tag{1}
\]
This bound also allows overlapping supports and masses outside the strip.

Use aligned bins of width \(b=32(1+D_*)\) for both coordinates. For two fixed real numbers at distance at most \(D_*\), a uniformly shifted bin boundary separates them with probability at most \(D_*/b\). Choose a shift for which the binned law of \(P\) has same-bin probability at least \(31/32\). With \(k\) fixed, each bin has at most \(b+1\) possible intercepts, so the \(P\) first marginal has mass at most \((b+1)/T\) per bin.

For a random set \(E\) of bins, include each bin independently with probability \(1/2\). For any binned law, the expectation over \(E\) of its mass on \(E\times E\) is \(1/4\) plus one quarter of its same-bin probability. The stipulated rectangle error therefore implies same-bin probability at least \(31/32-4\epsilon\ge15/16\) under \(Q\). The components of \(Q\) whose same-bin probability is at least \(1/2\) together have weight at least \(7/8\). For such a component with independent marginals \(p,q\),
\(\sum_j p(j)q(j)\le\max_j p(j)\), so some first-coordinate bin has at least \(1/2\) of its mass. The union of one such bin for each of these components carries at least \(7/16\) of the first \(Q\) marginal. Testing this union against the full second coordinate transfers at least \(7/16-\epsilon\) to the \(P\) marginal. Its per-bin bound proves (1).

In particular the pooled comparison with \(\log K\le(2+o(1))V\) needs \(\exp((\tau-10002+o(1))V)\) independent components or more to obtain a guarantee for all unary tests. For an exact independent decomposition restricted to the strip, applying a direct projection scan to every component still visits at least the full intercept length in total, up to any small residue strides. Indeed, fix one cofactor row. Each coordinate is injective on its \(T\) intercepts. If a component covers \(j\) of these pairs, each of its projected supports has at least \(j\) points. The components cover all \(T\) pairs, so the sum of the smaller projected support sizes is at least \(T\). This is a barrier to using independent pools with the existing wide-window counter and a uniform projection-scan fallback. It leaves open estimators specific to the squarefree band tests, and estimators that retain the correlation while combining the short supports.
