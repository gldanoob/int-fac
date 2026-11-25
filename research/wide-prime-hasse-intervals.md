# Prime products with a wider range of sizes in Hasse intervals

For a large dyadic \(P\) write \(L=\log P\), \(\ell=\log L\), and \(\ell_2=\log\ell\). Fix \(25/32<\sigma<1\). With a sufficiently large constant depending on \(\sigma\), set
\[
 u=C L^{2/3}\ell^{1/3}\ell_2,\qquad Y=e^u,\qquad
 V=\exp(1000L\ell/u).
\]
All but \(P^{\sigma+o(1)}\) primes \(P<p\le2P\) have at least \(\sqrt P/V\) distinct central orders \(n=4m\), \(m\) odd and \(Y\)-smooth, with \(|n-(p+1)|\le\sqrt p\). Consequently a deterministic algorithm completely factors every input with classical unconditional mean bit cost
\[
 \exp\!\left(O\!\left(b^{2/3}(\log(2b))^{1/3}
                    \log\log(4b)\right)\right)
\]
over ordinary \(b\)-bit integers and over balanced semiprimes. The deduction uses the same auxiliary elliptic search and cost accounting as the [classical mean-time proof](zero-density-hasse-intervals.md#complete-deterministic-factoring-in-classical-mean-time).

## A probability measure on prime logarithms

Choose \(25/32<\sigma_0<\sigma\). The [piecewise density estimates](zero-density-hasse-intervals.md#a-smaller-classical-exceptional-exponent) have an upper coefficient \(A_*<2\) on \([\sigma_0,1]\). Fix small \(\xi,e>0\) such that \(a=1-\xi-e>A_*/2\) and \(a(1-\sigma_0)-\xi>1-\sigma\). Set
\[
 x_0=P\sqrt 2/4,\qquad J=\left\lceil(1+\xi)L/u\right\rceil,
 \qquad s=\log(x_0)/J,\qquad w=\xi s.
\]
Thus \(s\asymp u\), \(Js=L+O(1)\), and \(s+w\le u\). Choose a fixed even Gevrey-class-two probability density \(W\) compactly supported in \((-1,1)\) and positive near zero. At real frequency \(t\) use the single prime slot and continuous slot
\[
 Q(t)=\sum_{r\ \mathrm{prime}}\frac{\log r}{rw}
       W\!\left(\frac{\log r-s}{w}\right)r^{-it},
 \qquad Q_0(t)=e^{-ist}\widehat W(wt).
\]
Their \(J\)-th powers are transforms of positive measures \(\mu\) and \(\nu\). All primes in \(\mu\) are odd and at most \(Y\). Chebyshev's bound for the weighted prime sum and partial summation give \(Q(0)=O(1)\), uniformly at large scales.

Convolve on logarithms with a nonnegative Gevrey-class-two probability kernel \(K_h\) supported in \([-h,h]\), for \(h=1/(100\sqrt P)\). For \(P/4\le x\le P/2\),
\[
 (\nu*K_h)(\log x)\gg (w\sqrt J)^{-1}\gg L^{-1}.
\]
Indeed \(\nu\) has density \(w^{-1}W^{*J}((v-Js)/w)\). Uniformly for \(|z|\le1\), \(\sqrt J W^{*J}(z)\) tends to \((2\pi\operatorname{Var}(W))^{-1/2}\). In the Fourier integral, substitute \(t=v/\sqrt J\) and use \(\widehat W(t)=1-\operatorname{Var}(W)t^2/2+O(t^4)\). Near zero the integrand is bounded by a Gaussian in \(v\). Away from zero \(|\widehat W|\) stays below a fixed number less than one and is integrable. The estimate holds throughout each kernel window, including both endpoints.

## Locating zeros within the resolution of a prime slot

Writing \(z=-d+i\Delta\), \(d\ge0\), define the Mellin weight
\[
 F(z)=e^{s z}\int_{-1}^1 W(v)e^{w z v}\,dv.
\]
For absolute constants depending on \(W\),
\[
 |F(-d+i\Delta)|\ll e^{-(s-w)d}\exp(-c\sqrt{w|\Delta|}).
\]
Factor out \(e^{(s-w)z}\), then integrate by parts against \(e^{wz(v+1)}\). Its absolute value is at most one. The derivative bound \(\|W^{(j)}\|_1\le A^{j+1}(j!)^2\) gives the claim on optimizing \(j\) in powers of \(|wz|^{-1}\). This keeps the constants independent of the growing width \(w\).

Put \(T_0=L^8\), \(T_1=\sqrt P L^4\) and \(H=L^4\). The prime explicit formula follows by integrating \(-\zeta'/\zeta(1+it+z)F(z)\) and shifting to \(\Re z=-3/2\). The pole gives \(Q_0(t)\) and a nontrivial zero \(\rho=1-d'+i\gamma\) gives \(-F(-d'+i(\gamma-t))\). On the final line the logarithmic derivative is \(O(\log(2+|t+\Im z|))\) by the functional equation. The contour remainder is \(O(L^{O(1)}e^{-3(s-w)/2})\) through \(T_1\). Prime powers contribute \(O(s^{O(1)}e^{-(s-w)/2})\) by summing \(r^{-k}\log r\) over \(k\ge2\) and \(r^k\ge e^{s-w}\). Discarding \(|t-\gamma|>H\) costs \(O(P^{-100})\) by the unit-height zero count and the Gevrey decay. Frequencies beyond \(T_1\) have absolutely negligible contribution after multiplication by \(\widehat K(ht)\), since \(\sqrt{h T_1}\asymp L^2\). [Prime explicit formula](https://people.maths.ox.ac.uk/greenbj/papers/primenumbers.pdf) · [Gevrey cutoff construction](zero-density-hasse-intervals.md#the-logarithmic-product-measure)

At \(|t|\le T_0\), Vinogradov–Korobov puts every retained zero at distance \(\gg\ell^{-2/3}(\log\ell)^{-1/3}\) from the line one. The sum of the absolute Mellin weights is therefore at most \(L^{O(1)}\exp[-c(s-w)\ell^{-2/3}(\log\ell)^{-1/3}]\). The same upper bound covers the prime-power remainder. It is \(o(1/L)\) even after multiplication by \(T_0 J C_0^J\) for any fixed \(C_0\). Thus the inverse transforms of the smoothed powers differ by \(o(1/L)\) from these frequencies, uniformly at every center. [Vinogradov–Korobov region](https://arxiv.org/pdf/1910.08205#page=2)

For \(T_0\le |t|\le T_1\), write \(d_*=c_0 L^{-2/3}\ell^{-1/3}\) with a fixed sufficiently small \(c_0>0\). Every retained zero satisfies \(d'\ge d_*\) by the same region. Let \(d_*\le d\le1-\sigma_0\) be any lower bound for the \(d'\) in the window. Then for sufficiently large \(C\),
\[
                         |Q(t)|\le e^{-a s d}.
\tag{1}
\]
To see this, first count zeros with \(d'\in[v,2v]\), \(v\ge d_*\). In a frequency interval of width \(1/w\le d_*\), and at any of the retained heights, their number is
\[
                        O(\ell+Lv^{3/2}).
\tag{2}
\]
For \(v\le1/12\) use Ford's local zero count with disk centered on the line one and radius \(3v\). Its hypotheses include \(R\le1/4\), height at least 100, and the Vinogradov–Korobov bound for \(|\zeta|\). Its logarithmic terms are \(O(\log(1/v)+\log\log T_1)=O(\ell)\). For \(v\ge1/12\) the unit-height zero count is \(O(L)\), which also gives (2). [Ford, Lemma 4.2](https://arxiv.org/pdf/1910.08205#page=9) · [Ford's bound in the critical strip](https://doi.org/10.1112/S0024611502013655)

Partition the frequency window into intervals of width \(1/w\). The Gevrey weights on them sum to \(O(\sum_{j\ge0}e^{-c\sqrt j})=O(1)\) after taking the supremum on each interval. Summing the resulting envelopes over \(v=2^j d\) bounds the zero terms by
\[
 O\!\left(\sum_{j\ge0}(\ell+L(2^j d)^{3/2})
               e^{-(1-\xi)s 2^j d}\right).
\]
Uniformly for \(v\ge d_*\), the logarithm of the coefficient is \(O(\log\ell+\log(v/d_*))\), since \(Ld_*^{3/2}=O(1)\). Taking \(C\) sufficiently large makes this at most \(e s v/3\): here \(s d_*\gg C\ell_2\) and \(\ell_2=\log\ell\). The dyadic sum, its absolute constant, the prime powers and \(Q_0(t)\) fit (1) after the remaining slack. The bound on the prime powers uses \(1-\sigma_0<1/2\).

## The exceptional-prime count and mean cost

On the high frequencies where some retained zero has \(\Re\rho>\sigma_0\), take bins \([\beta,\beta+1/L]\) for the largest such real part and set \(\delta=1-\beta\). In (1) take \(d=\max(d_*,\delta-1/L)\). A bin has measure at most \(2H N(\beta,T_1+H)\). The compact-mesh density argument on \([\sigma_0,9/10]\) and uniform Huxley bound above \(9/10\) give \(O(L^{O(1)}\exp(g\delta L))\), with fixed \(A_*/2<g<a\). This includes the powers of \(L\) in \(T_1\). Since \(Js=L+O(1)\), (1) implies the total absolute integral of \(Q(t)^J\widehat K(ht)\) over these bins is \(O(L^{O(1)}e^{-(a-g)d_* L})=o(1/L)\). Here the loss from each bin's width is bounded. [Uniform and fixed-real-part density estimates](zero-density-hasse-intervals.md#a-smaller-classical-exceptional-exponent)

On the other high frequencies use \(d=1-\sigma_0\) in (1). Reserve \(J_1=\lfloor J/2\rfloor\) slots. Then \(|Q|^{2J_1}\le P^{-a(1-\sigma_0)+o(1)}\). The remaining Dirichlet polynomial \(Q^{J-J_1}=\sum b_n n^{-it}\) is supported between \(P^{(1-\xi)/2+o(1)}\) and \(P^{(1+\xi)/2+o(1)}\). Its coefficients are at most \(n^{-1}(C_1 J)^J=n^{-1}P^{o(1)}\). Each ordered choice of a prime divisor has at most \(O(J)\) options and its slot numerator \(w^{-1}W\log r\) is bounded. Thus \(\sum |b_n|^2\le P^{-(1-\xi)/2+o(1)}\). The mean-value theorem up to \(T_1\) bounds the squared integral of this polynomial by \(P^{\xi+o(1)}\). The continuous transform is negligible on these frequencies. By Plancherel, the squared physical-space error from this part is bounded by \(P^{-a(1-\sigma_0)+\xi+o(1)}\). The strict choice of \(\xi,e\) makes this \(O(P^{-(1-\sigma)})\) with room to absorb powers of \(L\). [Montgomery–Vaughan mean-value estimate](https://doi.org/10.1112/jlms/s2-8.1.73)

Outside logarithmic measure \(O(P^{-(1-\sigma)})\) the short discrete convolution is \(\gg1/L\). Every atom at size \(m\asymp P\) has coefficient at most \(P^{-1}(C_1 J)^J\). Since \(J\log(C_1 J)\le(1/100)\log V\) eventually, the positive kernel of height \(O(\sqrt P)\) supplies more than \(\sqrt P/V\) distinct smooth integers. Disjoint center intervals of ordinary length \(1/8\) around \((p+1)/4\) yield the stated prime count, exactly as in the [central-window argument](zero-density-hasse-intervals.md#mean-square-on-the-remaining-frequencies).

For the factoring deduction one can use the concrete constants \(\sigma_0=4/5\), \(\sigma=167/200\), \(\xi=1/200\), \(e=1/100\). On the exceptional-frequency ranges above \(\sigma_0\), \(A_*/2\le15/16\), while \(a=197/200\) and \(a(1-\sigma_0)-\xi=24/125\). This exceeds \(1-\sigma=33/200\). The auxiliary pointwise elliptic search uses \(\theta=31/200\), leaving \(1-\theta-\sigma=1/100\) in its summable mean charge. All prime-slot estimates concern the mathematical analysis of that algorithm. Its integer implementation uses the smooth cutoff \(Y\), the mark bound \(V\), and the verified divisor searches already specified. [Integer search and recursive charge](zero-density-hasse-intervals.md#complete-deterministic-factoring-in-classical-mean-time) · [Finite coefficient and margin checks](../experiments/wide-prime-hasse.py)
