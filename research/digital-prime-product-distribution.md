# Consecutive digits and complete prime products

Assume Dirichlet GRH, including the zeta case. Let \(B\) tend to infinity through primes, let \(d\to\infty\), and put \(X=B^d\). Assume \(d\log\log X=o(\log B)\). Fix \(3/4<\chi\le1\). In each of the \(d\) base-\(B\) positions allow an arbitrary consecutive interval of digits in \(\{0,\ldots,B-1\}\) of length at least \(B^\chi\). Let \(\mathcal D\subset\mathbb Z/X\mathbb Z\) be the resulting set. The digit lengths can vary with position.

Let \(\mathcal P\) consist of all products obtained by taking one rational prime other than \(B\) from each of \(k\) disjoint sharp intervals \(I_i=[P_i,P_i(1+\epsilon_i)]\), with either endpoint convention. The fixed bounds on the intervals are
\[
 B^{c_-}\le P_i\le B^{c_+},\qquad
 \epsilon_i\asymp d^{-1},\qquad \prod_i P_i\asymp X ,
\]
where \(0<c_-\le c_+\) are fixed, and the comparison constants are fixed. These assumptions imply \(k\asymp d\), all products are in a fixed positive multiplicative range about \(X\), and unique factorization recovers each prime choice. The model includes bins of scale \(B^{c+o(1)}\) for any fixed \(c>0\).

Independently draw a real variable \(z_i\) in \(I_i\) with normalized density proportional to \(dz_i/\log z_i\). Let \(f\) be \(X\) times the density of \(\prod_i z_i\), folded onto the circle of length \(X\). Thus \(X^{-1}\int_0^X f=1\). There is a fixed \(\kappa>0\) such that
\[
 \frac{\#\{n\in\mathcal P:n\bmod X\in\mathcal D\}}{|\mathcal P|}
  =\frac{|\mathcal D|}{X}
     \left(\frac1{|\mathcal D|}\sum_{x\in\mathcal D} f(x)+O(B^{-\kappa})\right).       \tag{1}
\]
The error is absolute in the parentheses. The estimates are uniform in the digit origins and the prime-interval endpoints under the stated fixed bounds. The same conclusion holds for a finite disjoint union of such complete product sets with their exact cardinality weights, using the corresponding mixture of continuous densities.

In particular, when all the relevant digit positions lie in a fixed interior fraction of the continuous log-product support in one lift, the reference in (1) is at least \(B^{-o(1)}\), and the estimate is relative there. One can see the lower bound by choosing an interior target log norm, writing it as a common fractional displacement inside the log intervals, and restricting the first \(k-1\) log variables to within \(c_0/d^2\) of their assigned positions. The last log variable then has density \(\gg d\) at the required interior value. The resulting lower density is \(\exp(-O(d\log d))\). The upper bound \(f\ll d\) follows from the bounded density of any one log variable and the fixed folded range. If the top digit selects a region disjoint from the folded product support, the intersection can be empty. A complete product concentrated in \([X,1.1X]\) and a top digit interval near \(B/2\) give an example when all digit widths are \(B^{\chi+o(1)}\) with \(\chi<1\). The density being transferred is the actual density of the specified product family.

## Fourier bounds uniform in the base

Write \(e(t)=\exp(2\pi i t)\), let \(\nu\) be the uniform measure on \(\mathcal P\), and let \(\mu\) be the uniform digit measure. Put \(\xi=1-\chi\) and use the convention \(\widehat\mu(\alpha)=\mathbb E_\mu e(\alpha n)\). With digit lengths \(W_j\),
\[
 |\widehat\mu(\alpha)|
 \le \prod_{j=0}^{d-1}\min\bigl(1,C/(W_j\|B^j\alpha\|)\bigr).
\]
The bound ignores interval origins. For a \(1/Y\)-separated set on the unit circle with \(1\le Y\le X\), use the first \(m=\lceil\log_B(2Y)\rceil\) factors when \(m\le d\). Each cylinder of length \(B^{-m}\) contains at most one point. On such a cylinder the \(j\)-th factor is bounded by a function of the next digit \(a\) alone, using \(\|B^j\alpha\|\ge B^{-1}\min(a,B-1-a)\). The sum of the resulting one-digit bounds is \(O((B/W_j)\log(2B))\), including the two endpoint digits bounded by one. Thus the absolute sum on the separated set is at most
\[
 B^{\xi+o(1)}Y^\xi .
\]
On the full grid \(\alpha=h/X\bmod1\), use all \(d\) factors directly to get \(X^\xi B^{o(1)}\). The factors \((C\log(2B))^d\) are \(B^{o(1)}\) by the scale assumption. This is the elementary cylinder form of the digital Fourier argument. Maynard uses a hybrid estimate of this kind in the restricted-digit prime problem. [Maynard, *Primes and polynomials with restricted digits*, Lemmas 5.1–5.3](https://arxiv.org/pdf/1510.07711#page=7)

Choose a reduced Dirichlet approximant \(a/r\) to each grid frequency \(\alpha\), with \(r\le\sqrt X\), \(\beta=\alpha-a/r\), and \(D=X|\beta|\ll\sqrt X/r\). In a dyad \(r\asymp Q\le X^{0.49}\) and with \(D\ll Z\), \(Z\ge1\), group grid points by their integer offset from the grid point nearest to \(a/r\). There are \(O(Z)\) offsets. For each offset the rounded rational centers still have spacing \(\gg Q^{-2}\), since rounding changes any difference by at most \(1/X\). The digital absolute sum for this group is therefore
\[
 O\bigl(Z B^{\xi+o(1)}Q^{2\xi}\bigr).                                  \tag{2}
\]
The full-grid bound suffices for larger \(Q\) in the uses below.

## Rational and residual phases for the complete product

At each prime interval the GRH logarithmic-twist estimates, uniformly for polynomial-size conductors and \(|t|\le X^C\) for any fixed \(C\), give
\[
 \sum_{p\in I_i}\chi_1(p)p^{-it}
 ={\bf1}_{\chi_1\ {\rm principal}}\int_{I_i}\frac{x^{-it}\,dx}{\log x}
       +O\bigl(P_i^{1/2}(\log X)^{O(1)}\bigr).                         \tag{3}
\]
Here one may omit the primes dividing the modulus and \(B\). Apply truncated Perron to the logarithmic derivative \( -L'/L(s+it,\chi_1)\) at the two half-integer endpoints and shift to \(1/2+1/\log P_i\). Its bounds there follow from the GRH zero locations and the logarithmic zero count in each unit height interval. The principal pole supplies the displayed integral, with partial summation removing the Mangoldt weight. Prime powers and the deleted primes fit the same error. In particular the actual number of allowed primes is \(\asymp P_i/(d\log P_i)\). Multiplying the normalized nonprincipal errors across any set of free bins costs only \(B^{o(1)}\) in their prefactors, since \(k\log\log X=o(\log B)\). [Logarithmic-twist and sharp product-prefix estimates](keybreak-prime-product-grid-variance.md#character-bounds-with-value-cutoffs)

For the rational part \(a/r\), split the products by \(g=(n,r)\). A possible \(g\) is squarefree, fixes one prime in each of its selected bins, and has probability at most \(B^{o(1)}/g\) before the remaining coprimality restriction. Set \(n=gm\) and omit every prime of \(r\) from the remaining bins. The free product has scale \(X/g\gg X/r\) and hence a number \(\gg d\) of free slots. Expand \(e(am/(r/g))\) in characters on the units modulo \(r/g\). The coefficient absolute sum is at most \(\sqrt r\) by Parseval. The principal coefficient is \(\mu_{\rm Mob}(r/g)/\varphi(r/g)\), also when \(r/g=1\). Its absolute value is at most \((r/g)^{-1+o(1)}\). The reduction from units of a larger modulus to units of \(r/g\) preserves this mean. Deleting occupied or excluded primes changes neither the forced-prime bound nor (3).

Insert \(e(\beta n)\) using the log Mellin transform of \(w(n/X)e(\beta n)\), where a fixed compact smooth \(w\) supported inside \((0,\infty)\) equals one throughout the full product range. In the log variable \(z=\log(n/X)\) the amplitude has bounded support, bounded \(L^2\) norm, and first derivative norm \(O(1+D)\). Weighted Cauchy–Schwarz and Plancherel give Mellin \(L^1\) norm \(O(\sqrt{1+D})\). The integral above a sufficiently large polynomial height is negligible by repeated differentiation. A nonprincipal character then contributes at most \((X/g)^{-1/2}B^{o(1)}\sqrt{1+D}\) before the rational coefficients and the forced-bin probabilities. Summing \(g^{-1/2+o(1)}\) over \(g\mid r\) costs \(r^{o(1)}\), and \(r(1+D)\ll\sqrt X\). Hence the total nonprincipal bound is \(X^{-1/4+o(1)}\). A sharp product prefix can also be inserted in this nonprincipal estimate by an independent truncated Perron integral. Use a half-integer endpoint in the divided variable \(m\), height \(X^4\), and abscissa \(1/\log X\). The absolute Perron integral costs \(O(\log X)\), and (3) applies at the sum of the two polynomially bounded Mellin frequencies. The half-integer truncation error is negligible uniformly on the product range. This prefix observation is for the nonprincipal terms.

The principal term is at most \(r^{-1+o(1)}B^{o(1)}\) by the forced-bin bound and the divisor bound. If \(D\ge B^\eta\) for a fixed \(\eta>0\), then for every fixed \(A\) it is bounded by
\[
 O_A\bigl(r^{-1+o(1)}B^{o(1)}D^{-A}+X^{-1/4+o(1)}\bigr).                \tag{4}
\]
For \(|t|\le cD\), with \(c>0\) small in terms of the support of \(w\), the log Mellin phase has derivative \(\gg D\). Repeated integration by parts makes this part of each principal character integral \(O_A(D^{-A})\) before its rational coefficient is applied. For \(|t|\ge cD\), the normalized prime sum in each free bin is bounded by
\[
 \min(1,(1+|t|)^{-1}(\log X)^{O(1)})
       +P_i^{-1/2}(\log X)^{O(1)}.
\]
This follows by integrating the principal main term of (3) by parts. When \(B^\eta\le D\le B^{c_++1}\), the \(\gg d\) factors give an arbitrary fixed power saving in \(D\), even after the Mellin \(L^1\) cost. For \(D>B^{c_++1}\), the product is \((X/g)^{-1/2}B^{o(1)}\). After the principal coefficient and forced-bin probability, summing over \(g\) bounds this last contribution by \(X^{-1/2+o(1)}\sqrt{D/r}\le X^{-1/4+o(1)}\). These estimates use the full smooth Mellin cutoff on the product range.

## Summing the grid

Finite Fourier inversion gives \(\nu(\mathcal D)=(|\mathcal D|/X)\sum_{h\bmod X}\widehat\nu(h/X)\overline{\widehat\mu(h/X)}\). The \(X^{-1/4+o(1)}\) terms save a fixed power of \(X\) by the full-grid absolute sum and \(\xi<1/4\). For \(D\ge B^\eta\) and \(r\le X^{0.49}\), combine (2) and (4) in dyads \(D\asymp Z\), \(r\asymp Q\). This gives \(B^{\xi+o(1)}Q^{2\xi-1+o(1)}Z^{1-A}\). Choose \(A\) large in terms of \(\eta\), taking the divisor-bound exponent smaller than a fixed fraction of \(1-2\xi\). The sum saves a fixed power of \(B\). For \(r>X^{0.49}\) the trivial principal bound and the full-grid absolute sum already save a power of \(X\).

Fix \(0<\eta<\min(c_-/16,1/100)\). At \(D<B^\eta\) and \(B^{3/5}\le r\le X^{0.49}\), the trivial principal bound and (2) give at most \(B^{\eta+\xi+(3/5)(2\xi-1)+o(1)}\) after dyadic summation, a power saving for \(\xi<1/4\). If \(2\le r<B^{3/5}\), then \(B\) is coprime to \(r\) and every digit factor satisfies \(\|B^j\alpha\|\ge 1/(2r)\). Indeed \(|\beta|B^{d-1}\le B^{-1+\eta}\). The resulting \(|\widehat\mu(\alpha)|\le(Cr/B^\chi)^d\) absorbs the \(O(B^{6/5+\eta})\) possible frequencies. Denominators sharing \(B\) occur in the previous large-denominator groups. In particular the exact primitive \(B\)-th harmonics have the ordinary unit-class principal factor \( -1/(B-1)\), since the product excludes \(B\).

It remains to treat \(r=1\), \(D<B^\eta\), which is the central grid interval \(|h|<B^\eta\). Successive replacement of the prime variables by their independent continuous versions in \(e((h/X)\prod_i z_i)\) costs \(O(B^{-c_-/2+o(1)}(1+|h|))\) per frequency from (3) at \(t=0\) and partial summation on each prime interval. This includes the sum over \(k\) slots. Summing over the central frequencies gives a power saving. For comparison, the continuous Fourier coefficients have size \(O_A(d^{O(A)}(1+|h|)^{-A})\) for every fixed \(A\) and sufficiently large \(d\). In log coordinates the individual normalized interval densities have variation \(O(d)\). Differentiate their convolution by putting the fixed number of derivatives on different factors and use the variation bounds. Change back to the product variable on its fixed relative support and integrate by parts. Thus extending the continuous sum to all \(h\in\mathbb Z\) is harmless, and its evaluation on the digits is the average of the folded density \(f\) in (1).

For an explicit terminal unit reference one may replace \(f(x)\) in (1) by \(B f(x){\bf1}_{B\nmid x}/(B-1)\) with the same type of error. At most one permitted least-significant digit is zero, and \(f\ll d\), so this substitution costs \(O(d(B^{-\chi}+B^{-1}))\) in the normalized reference. The error bound in (1) need not resolve a correction of this smaller size.

## Sharp prefixes in the digit comparison

When the product interval formed from the real bin endpoints lies in a single period of length \(X\), (1) also holds with a further sharp true-value prefix or interval imposed on both sides. The same argument always applies to a prefix of the residues after folding. The error remains absolute relative to \(|\mathcal D|/X\), uniformly in the endpoint. Fix \(3/4<\chi'<\chi\) and \(L=\lceil B^{\chi'}\rceil\). A prefix of the digits consists of an interval of complete leading-digit slices and at most one incomplete boundary slice. If the complete leading-digit interval has length at least \(L\), it is another digit box and the full comparison applies with lower width exponent \(\chi'\). If it has length less than \(L\), enclose it in a leading-digit interval of length \(L\). The incomplete slice has the same type of enclosure, keeping the other digit intervals unchanged and using positivity. Each enclosure has size at most \(L/W_{d-1}\) times the original digit count. The full comparison and \(f\ll d\) bound both the actual and reference contributions from these enclosures by \(O((|\mathcal D|/X)d B^{\chi'-\chi})\), up to the smaller comparison error. Taking differences gives intervals. This treats very short leading-digit prefixes without assigning them a lower width they lack.

The separation of grid frequencies, the cylinder factors, and this sharp-prefix argument use the integer base-\(B\) place values. The proof gives no distribution statement for replacing them by geometric coefficients \(a^i b^{d-1-i}\).
