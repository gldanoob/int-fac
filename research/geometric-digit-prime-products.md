# Geometric digits and complete prime products

Let \(B\) be prime, \(1\le a<B\), and set \(X=B^d\) with \(d\to\infty\) and \(d\log\log X=o(\log B)\). At position \(i\), \(0\le i<d\), allow a consecutive integer interval of width \(B^\chi\le W_i\le B\) for fixed \(3/4<\chi<1\). The integer origins are arbitrary. The image
\[
   \mathcal D_a=\left\{\sum_{i=0}^{d-1}v_i a^i B^{d-1-i}\bmod X:
                  v_i\text{ is an allowed digit}\right\}
\]
has \(\prod_i W_i\) elements. Reducing modulo \(B\) determines the last digit, and subtracting and dividing by \(B\) determines each successive digit. The conclusion with all widths \(B\) follows by taking any fixed smaller lower-width exponent.

Use the complete prime-product model of the [ordinary digit comparison](digital-prime-product-distribution.md). Its prime bins are disjoint, have lower endpoints \(P_i\in[B^{c_-},B^{c_+}]\) with fixed positive exponents, and have relative lengths \(\asymp1/d\) and \(\prod_i P_i\asymp X\). The prime \(B\) is omitted. Let \(\mathcal P\) be the product set and \(f\) the folded density from the independent real variables with normalized densities \(dx/\log x\) on the bins, scaled to have mean one on the circle of length \(X\). Under Dirichlet GRH, for every arc \(I\) on this circle, including the full circle,
\[
 \frac{\#\{n\in\mathcal P:n\bmod X\in\mathcal D_a\cap I\}}{|\mathcal P|}
   =\frac{|\mathcal D_a|}{X}
        \left(\frac1{|\mathcal D_a|}\sum_{x\in\mathcal D_a\cap I}f(x)
                       +O(B^{-\kappa})\right)                         \tag{1}
\]
for a fixed \(\kappa>0\). The error inside the parentheses is absolute and uniform in \(a\), the digit intervals, the arc endpoints and the bin data within their fixed bounds. The reference is evaluated at the actual geometric digit images. It can be zero if the image misses the folded product support. When the reference in parentheses is \(B^{-o(1)}\) or larger, (1) gives a relative estimate. For a sharp true-value interval, including a prefix that spans several residue periods, the same comparison uses the real product density restricted to that interval before folding, without renormalizing it.

## Digit lifts and resonances

Let \(\mu\) be the uniform measure on the digit image, write \(\xi=1-\chi\), and abbreviate the \(i\)-th coefficient by \(\lambda_i=a^iB^{d-1-i}\). The absolute Fourier transform is the product of geometric factors at \(\lambda_i\alpha\), each bounded by \(\min(1,C/(W_i\|\lambda_i\alpha\|))\). Such an envelope remains valid with a larger absolute \(C\) when its argument is moved by \(O(1/B)\), since \(W_i\le B\).

On the full grid \(\alpha=h/B^d\), summing over lifts of \(h\bmod B^{i}\) to \(h\bmod B^{i+1}\) permutes the phases of the \(i\)-th factor, because \(a^i\) is a unit modulo \(B\). Sum first over the highest lifts to keep all lower-index factors fixed. Each factor costs \(O((B/W_i)\log(2B))\), giving the full-grid absolute sum \(X^\xi B^{o(1)}\). The same lifting estimate applies to any consecutive block when expressed on its natural grid.

There can be prominent resonances. For \(a=B-1\) and \(\alpha=a/B\), every phase except the last is integral. The last phase is \(\pm1/B\bmod1\), so its geometric factor tends to one if \(W_{d-1}=B^{\chi+o(1)}\). At the exact rational \(\alpha=1/a\), again for \(a=B-1\), the first phase is \(1/a\bmod1\) and all later phases are integral. At the nearest grid frequency, phases change by \(O(1/B)\), so the product still tends to one since the sum of the squared scaled phase errors is \(O(d(W_{max}/B)^2)=o(1)\) when all widths are \(B^{\chi+o(1)}\). In the \(B\)-th harmonics the prime products have the unit-class principal coefficient \(-1/(B-1)\), since \(B\) is omitted. The arc estimates below allow resonant digital coefficients of size one. A pointwise small Fourier bound at all noninteger rationals would fail.

## The Farey-arc absolute sum

Take reduced rational centers \(u/r\bmod1\) with \(r\asymp Q\), \(Q\le X^{0.49}\). For each center take grid frequencies at distance \(O(Z/X)\), where \(Z\ge1\). Each can be written as the rounded grid center plus \(j/X\) for one of \(O(Z)\) common offsets \(j\). Counting with multiplicity is allowed. Uniformly also after a common grid shift, their digital absolute sum is
\[
                     O\bigl(ZB^{\xi+o(1)}Q^{2\xi}\bigr).               \tag{2}
\]

Here is the block selection for a fixed \(r\). With \(C_0\) a sufficiently large fixed constant, start at \(k_0=\lceil\log_B(C_0Q^2)\rceil\), and replace \(k\) by
\[
  \max\!\left(1,\left\lceil\log_B(C_0\max(1,Q/g(k))^2)\right\rceil\right),
  \qquad g(k)=\gcd(r,a^{d-k}).
\]
This map is nondecreasing in \(k\). Starting at \(k_0\) gives a decreasing sequence with a fixed integer endpoint \(1\le k\le k_0<d\) for all sufficiently large \(d\). Put \(i_0=d-k\), \(A=a^{i_0}\), and \(g=g(k)\). Group centers by this pair \(k,g\).

Fix an offset \(j\). Multiplying the grid frequency by \(A\) writes the last \(k\) factors as a length-\(k\) geometric block with coefficients \(a^sB^{k-1-s}\), \(0\le s<k\). The new frequency lies within \(O(A/X)\le O(B^{-k})\) of the rational center \(Au/r\bmod1\) shifted by the common \(Aj/X\). Its reduced denominator is \(r/g\asymp Q/g\). Distinct transformed centers therefore have spacing \(\gg\max(1,Q/g)^{-2}\). By the block choice, each cell of length \(B^{-k}\), even when enlarged by a fixed number of adjacent cells, contains only \(O(1)\) such centers. For the suffix, evaluate an enlarged envelope at a neighboring \(B^{-k}\) grid endpoint. The change of each phase is \(O(1/B)\). Summing these envelopes on the natural grid by digit lifting costs
\[
          B^{k\xi+o(1)}
             \le B^{\xi+o(1)}\max(1,Q/g)^{2\xi}.
\]
This bound counts each distinct transformed center once and is uniform over all its preimages.

The preimages of a fixed transformed center in a group with given \(g,k\) have common denominator \(r\) and lie in a step-\(1/g\) coset, where the denominator \(r/g\) of the transformed center determines \(r\). We may sum all \(g\) lifts, retaining the first \(i_0\) factors to control this multiplicity. Write \(g_i=g/\gcd(g,a^i)\) and \(t_i=g_i/g_{i+1}\) for \(0\le i<i_0\). The \(i\)-th phase on the lifts depends on the lift index modulo \(g_i\) through a unit multiplier. All later phases depend only on that index modulo \(g_{i+1}\). This uses \((B,g)=1\) and the definition of the gcd. Rounding the original centers changes the phases by at most \(1/B\); the grid offset is a fixed phase translate for each factor. Summing one layer at a time costs \(O(1+t_i\log(2B)/W_i)\) at level \(i\), by the sum of a geometric envelope on \(t_i\) equally spaced points. Since \(t_i\mid a\), for any fixed \(0<\zeta<\chi\) the normalized cost is at most
\[
   C t_i^{-\zeta}\bigl(1+B^{\zeta-\chi}\log(2B)\bigr).
\]
As \(\prod_i t_i=g\), the original lift sum is at most \(g^{1-\zeta}B^{o(1)}\). Its product with the suffix bound is \(B^{\xi+o(1)}Q^{2\xi}g^{1-\zeta-2\xi}\), allowing an absolute factor when \(g>Q\).

Choose \(2\chi-1<\zeta<\chi\), so \(\omega=\zeta+2\xi-1>0\). The dependence on \(a\) after summing the groups is bounded, up to \(d=B^{o(1)}\), by
\[
   \sum_{g\mid a^d} g^{-\omega}
    \le \prod_{p\mid a}(1-p^{-\omega})^{-1}
    \le \exp\bigl(O_\omega((\log(2a))^{1-\omega})\bigr)
    = B^{o(1)}.
\]
The middle inequality follows by ordering the distinct primes and bounding their reciprocal powers by the first \(O(\log(2a))\) integer reciprocal powers. The offset sum now gives (2). Without the complementary prefix the reduced denominators can coincide, so separation of the transformed rationals alone would not justify (2).

## Product comparison and sharp arc endpoints

Use the additive prime-product estimates proved in the [ordinary digit comparison](digital-prime-product-distribution.md#rational-and-residual-phases-for-the-complete-product). At \(\alpha=u/r+\beta\) from Dirichlet approximation, set \(D=X|\beta|\ll\sqrt X/r\). The nonprincipal part is \(X^{-1/4+o(1)}\), and the principal part is \(O(r^{-1+o(1)}B^{o(1)})\). For \(D\ge B^\eta\) it saves an additional \(D^{-A_1}\) for any fixed \(A_1\), plus an \(X^{-1/4+o(1)}\) remainder, by the smooth physical cutoff on the full product range. These estimates are on the product law and are independent of the type of digits. Fix \(0<\eta<\min(c_-/16,1/100)\). The full-grid digital bound absorbs the \(X^{-1/4+o(1)}\) terms because \(\xi<1/4\). For high \(D\) and \(r\le X^{0.49}\), (2) with dyads in \(D,r\) gives \(B^{\xi+o(1)}Q^{2\xi-1+o(1)}Z^{1-A_1}\), which saves a fixed power of \(B\) for large enough \(A_1\). At \(r>X^{0.49}\) use the full-grid bound and the trivial principal bound.

For low \(D<B^\eta\) and moderate \(r\ge B^{3/5}\), (2) gives a power saving \(B^{\eta+\xi+(3/5)(2\xi-1)+o(1)}\). For \(2\le r<B^{3/5}\), \(r\) is coprime to \(B\). If \(r\nmid a^d\), every exact rational phase is at least \(1/r\) from an integer. Perturbing by \(\beta\) costs at most \(D/B\) in each phase, so the product is \(O((Cr/B^\chi)^d)\). When \(r\mid a^d\), the first factor alone is \(O(r/B^\chi)\). Retain its \(1/4\)-power and apply the prefix lift calculation to the remaining \(3/4\)-power of each factor, this time with \(g=r\) and the entire digit range as the prefix. For these powered envelopes the normalized cost at a lift is \(O(1/t_i+W_i^{-3/4})\), by summing \(j^{-3/4}\) over evenly spaced points. Taking any fixed \(1/4<\zeta'<3\chi/4\), the summed weight after multiplication by the principal \(r^{-1+o(1)}B^{o(1)}\) is
\[
       O\left(B^{\eta-\chi/4+o(1)}
              \sum_{r\mid a^d} r^{1/4-\zeta'+o(1)}\right).
\]
The same reciprocal-divisor bound gives a power saving. This handles small denominators that divide powers of \(a\), even when most digit factors have integral phases. In the central arc \(r=1,\ D<B^\eta\), replace the complete product by its continuous counterpart exactly as in the ordinary comparison. The continuous Fourier tail is summable with a power saving, and Fourier inversion evaluates \(f\) on the actual geometric images.

For a sharp residue arc, sandwich its indicator by smooth upper and lower weights on the circle of length one, evaluated at \(x/X\). Convolve arcs enlarged and shrunk by \(O(\delta)\) with a positive compact bump, where \(\delta=B^{-0.30}\). The weights lie between zero and one and differ from the indicator only within \(O(\delta)\) of its endpoints. Their Fourier coefficient absolute sum is \(O(\log B)\); the tail beyond \(|\ell|>B^{0.32}\) is \(O_C(B^{-0.02C})\) for every fixed \(C\), by bump differentiation. Multiplying the digit measure by either weight replaces its transform by a linear combination of the transforms shifted by \(\ell/X\). Equation (2) and the full-grid bound are uniform in all those shifts, so the estimates outside the central and small-denominator arcs survive with the logarithmic loss. In the small-denominator argument retain \(|\ell|\le B^{0.32}\). The further phase perturbation is at most \(|\ell|/B\), and \(r(D+|\ell|)/B=o(1)\) for \(r<B^{3/5}\). For the omitted shifts on those small-denominator arcs only, use the crude \(O(B^{6/5+\eta})\) grid count and take \(C\) large. The central comparison needs only that the transform of the weighted digit measure is bounded by one. This proves the comparison for both smooth weights.

Fixing all digits except the first makes its images equally spaced by \(X/B\). A boundary interval of length \(O(\delta X)\) therefore contains a fraction \(O((\delta B+1)/W_0)\) of the digit mass. Since \(f\ll d\) and \(0.30>1-\chi\), the upper and lower reference masses differ by a power-small amount in (1). This proves the sharp residue comparison. The last digit controls divisibility by \(B\), so replacing \(f(x)\) by \(Bf(x){\bf1}_{B\nmid x}/(B-1)\) changes the normalized reference by only \(O(d(B^{-\chi}+B^{-1}))\). The relative precision in (1) is not intended to isolate a correction smaller than its error.


## Sharp true-value intervals across several periods

Split each real prime interval into a fixed number \(M\) of equal real subintervals, assigning integer endpoints consistently. Within a subbox, the sum of the logarithms of the upper-to-lower endpoint ratios is \(O(1/M)\). The upper product scale is \(O(X)\), so a sufficiently large fixed \(M\) makes the product range in every subbox shorter than \(X/2\). All subbins have relative widths \(\asymp 1/d\), with constants that can depend on \(M\), and the same fixed power bounds apply. The principal prime estimate gives positive subbin populations for large \(B\).

For each true-value interval \(J\), its intersection with a subbox product range projects injectively onto a residue arc, possibly wrapping at zero. Apply (1) to that arc within the subbox. The normalized error is uniform over subboxes and endpoints. Average over the subboxes using their exact prime-count probabilities. These are products of the individual bin probabilities and sum to one.

Now weight the subboxes by the continuous bin probabilities from \(dx/\log x\). In each prime bin, the discrete and continuous distributions over its \(M\) subbins have total variation distance \(B^{-c_-/2+o(1)}\) by the endpoint estimates and the lower bound for the full bin. Summing the distances over \(k\) independent slots preserves that bound. Each subbox's scaled folded density is \(O(Md)\) by the one-variable log-density bound. Thus the change in the normalized reference is \(B^{-c_-/2+o(1)}\). With the continuous weights, the subbox references sum to the real product density restricted to \(J\) and then folded modulo \(X\). Writing \(f_J\) for \(X\) times this unnormalized folded density gives
\[
 \frac{\#\{n\in\mathcal P:n\in J,\ n\bmod X\in\mathcal D_a\}}{|\mathcal P|}
 =\frac{|\mathcal D_a|}{X}
   \left(\frac{1}{|\mathcal D_a|}\sum_{x\in\mathcal D_a}f_J(x)
         +O(B^{-\kappa'})\right)
\]
for fixed \(\kappa'>0\). For half-open intervals, define the restricted density pointwise by multiplying the continuous density on the line by the indicator of that half-open interval before folding. This fixes its values at integer endpoints. The error is absolute on the original digit-density scale, including for intervals whose continuous reference is small.


## Independent unimodal digits

The interval comparison also applies to independent integer digits with arbitrary summable unimodal probability masses \(p_i\) such that
\[
             \max_i\sup_{n\in\mathbb Z}p_i(n)\ll B^{-\chi}
\]
for some fixed \(\chi>3/4\). Here unimodality means that each positive superlevel set is an integer interval. Write \(\Gamma(x)\) for the probability mass at the actual image \(x=\sum_i v_i a^iB^{d-1-i}\bmod X\). For every sharp true-value interval \(J\) in the prime-product model,
\[
 \frac{X}{|\mathcal P|}\sum_{n\in\mathcal P\cap J}\Gamma(n\bmod X)
    =\sum_{x\bmod X}\Gamma(x)f_J(x)+O(B^{-\kappa''}) ,
\]
for a fixed \(\kappa''>0\). This is an absolute error, uniform in the digit locations and in \(J\). It also applies to sharp residue arcs with the corresponding restricted reference. The comparison is relative when the reference is at least \(B^{-o(1)}\).

To see this, for \(t>0\) write \(I_i(t)=\{n:p_i(n)>t\}\). The identity \(p_i(n)=\int_0^\infty{\bf1}_{I_i(t)}(n)\,dt\) expresses the digit law as a mixture of uniform laws on the nonempty finite intervals \(I_i(t)\), with mixing mass \(|I_i(t)|\,dt\). This mass integrates to one. If a superlevel interval has length \(L>B\), split it into \(\lceil L/B\rceil\) consecutive intervals of lengths differing by at most one, weighted by their lengths divided by \(L\). Each length is between \(\lfloor B/2\rfloor\) and \(B\). The split is exact and also covers unbounded original digit support through the mixture.

Fix \(3/4<\chi'<\min(\chi,1)\) and put \(L_0=\lceil B^{\chi'}\rceil\). A digit's mixture mass on original intervals of length below \(L_0\) is at most \(L_0\sup_n p_i(n)\). The new subintervals from long intervals all have length at least \(L_0\) for large \(B\). Thus the total mass of independent boxes with any width below \(L_0\) is at most \(O(d B^{\chi'-\chi})=B^{-(\chi-\chi')+o(1)}\). In each other box the widths are between \(L_0\) and \(B\), and the modular image is injective. Translating its individual intervals to begin at zero adds a common translation to the image. This multiplies each Fourier value by a unit phase, and the reference and arc weight remain evaluated on the actual translated images. Hence the uniform interval estimate at exponent \(\chi'\) applies to each such box. Its normalization is the displayed comparison, since the image mass of each box is \(1/|\mathcal D_a|\) at each of its points.

For the omitted boxes, the normalized comparison costs at most their mixture mass times \(O(X/|\mathcal P|+\|f_J\|_\infty)\). Indeed the product range has length \(O(X)\), so at most \(O(1)\) distinct products lift any given residue, and \(f_J\ll d\). Also \(|\mathcal P|=X B^{o(1)}\), with \(X/|\mathcal P|=B^{o(1)}\). The prime count in a bin is \(\asymp P_j/(d\log P_j)\), and multiplying these populations uses \(\prod_jP_j\asymp X\) and \(d\log\log X=o(\log B)\). The omitted contribution therefore saves a fixed power of \(B\). The good-box errors average without a dependence on the number of boxes. Positivity and the same absolute bounds justify all the mixtures and integrations.

In particular, discrete Gaussian digits with masses proportional to \(\exp(-\pi(n-c_i)^2/\sigma_i^2)\) satisfy the hypotheses for \(\sigma_i\ge B^\chi\), uniformly in the real centers \(c_i\). The normalizing sum is \(\gg \sigma_i\) by the integers within distance \(\sigma_i\) of the center, and the masses are unimodal. The exact interval splitting permits arbitrarily large \(\sigma_i\) with no tail truncation.
