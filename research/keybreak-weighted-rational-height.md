# Counting smooth major arcs with their rational denominators

Retaining the rational denominator in the single-progression estimate bounds the ordinary two-coordinate Fourier sum for any fixed \(0<\epsilon<1/2\). Let \(V\) be the mark height, \(X=V^d\), \(h=d-2\), and \(M=2S+1\le V^{\epsilon+o(1)}\) the number of short digits. Assume \(d\to\infty\), \(\log\log X=o(\log V)\), and the exact difference-conductor property for the two primes \(b_i\asymp V\), with \(2S<\min_i b_i\). At the endpoints \(X_i=X^{1+o(1)}\), let \(L_i=X_i/m_i\) with \(m_i=V^{O(1)}\), and assume \(L_i/b_i^h\ge V^{1-\epsilon-o(1)}\). The smoothness cutoffs satisfy \(y_i=X^{o(1)}\) and \(\log y_i/\log\log X\to\infty\). These are the interval and counting hypotheses supplied by the band setup at width \(\sigma\ge V^{2-\epsilon-o(1)}\), with \(\sigma=V^{O(1)}\). For each mode normalize the two interval sums by \(L_i\), and take their absolute supremums over intervals in the respective capped box. The sum of their products over the nonzero short modes, with Fourier weights at most one, is
\[
 O(X^{-c})+V^{-(1-2\epsilon)+o(1)}
\]
for some \(c>0\), uniformly in both progression translates. At \(\epsilon=3/20\) the new saving is \(7/10\) in the \(V\)-exponent, compared with \(229/400\) from the unweighted height. The proof covers the ordinary smooth test and the constant test under the stated Dirichlet GRH smooth-sum estimate. [Basic conductor and valuation count](keybreak-dual-major-arc-count.md) · [Single-progression saving](keybreak-smooth-major-arc-progressions.md)

## Low heights

For each coordinate and each short mode fix one minimizing rational approximant \(a/q\) for the step height \(T=q(1+L\|\beta-a/q\|)\), \(L=X_i/m_i\). Such a minimizer exists with \(q\le b^h\) because the exact approximant is available and every candidate has height at least its denominator. Set \(W=qT\) using this fixed choice. Both \(T\) and \(W\) are at least \(V^{1-\epsilon-o(1)}\) for a nonzero mode. To count \(W\le U\), group by dyadic denominator \(Q\le q<2Q\) and valuation \(v=v_b(q)\). Then \(T\le U/Q\) and \(q\le\sqrt U\). For two modes in such a group the circular distance between their step-frequency difference and their rational difference is at most
\[
 (U/(QL))(1/q+1/q').
\]
Multiplication by \(\operatorname{lcm}(q,q')\) makes this at most \(4U/(Lb^v)\). The existing prefix argument therefore works for every \(k\le h=d-2\) with \(4U b^k<L b^v\). Choose the largest such \(k\), or zero if the set is empty. Within a fixed suffix of the short digit vector, differences of approximants which coincide with grid differences have denominator dividing \(b^v\). The number of modes is at most \(M^{e}\) in the group, \(M=2S+1\le V^{\epsilon+o(1)}\) and \(e=h-k+\min(v,k)\). If \(k=h\), \(e\le\log_b\sqrt U\). Otherwise \(4U b^{k+1}\ge Lb^v\), so
\[
 e\le \log_b U+1-\log_b(L/b^h)+\log_b 4
 \le \log_b U+\epsilon+o(1).
\]
The default \(k=0\) needs no separation argument, since fixing its suffix fixes the entire vector. The valuation and dyadic denominator groups number \(O((h+1)(1+\log U))=V^{o(1)}\) uniformly up to \(U=X^{O(1)}\). This proves the one-coordinate upper bound
\[
 \#\{s: W_i(s)\le U\}\le V^{\epsilon^2+o(1)}U^{\epsilon+o(1)}. \tag{1}
\]

Choose a fixed height threshold \(X^\gamma\) with \(0<\gamma<1/2-\epsilon\). In the region \(T_1,T_2\le X^\gamma\), use the major-arc bound, with fixed slack in its applicability threshold to account for \(X_i=X^{1+o(1)}\). Its normalized principal part in coordinate \(i\) is at most \(V^{o(1)}W_i^{-1/2+o(1)}\) for the smooth test, since \(q^{-1}(1+D)^{-1/2}=W_i^{-1/2}\) and \(\Psi(X_i/g_i,y_i)\le X_i/g_i\). For the constant test, \(T_i\le1+L_i\|\beta_i\|\) by taking denominator one. The normalized geometric sum is therefore \(O(1/(T_i-1))=O(W_i^{-1/2})\), using \(W_i\le T_i^2\) and the nonzero-mode lower bound \(T_i\to\infty\). The normalized error from the smooth test is \(X^{-1/2+\gamma+O(\tau)+o(1)}\). Each principal upper bound is \(O(1)\) on these nonzero modes, and each actual normalized interval sum is \(O(1)\) trivially. Thus terms containing an error contribute \(O(X^{-c})\) in total after choosing \(\tau>0\) sufficiently small, since the number of short modes is at most \(M^h\le X^{\epsilon+o(1)}\). For a constant test the corresponding error is zero.

In dyadic bins \(U\le\min(W_1,W_2)<2U\), the product principal contribution is bounded by \(V^{o(1)}U^{-1+o(1)}\) per mode. At least one coordinate has \(W_i<2U\), so twice the larger of the two one-coordinate bounds (1) controls the bin size. The factor \(O(\log X)\) for the bin count is \(V^{o(1)}\). At the smallest permissible \(U\ge V^{1-\epsilon-o(1)}/2\), the net exponent is at most
\[
 \epsilon^2-(1-\epsilon)^2=2\epsilon-1.
\]
Keeping \(q\) in both the counting argument and the single-progression estimate is needed for this exponent.

## Heights above the threshold

Use the step-height count \(\#\{T_i\le X^t\}\le X^{\epsilon\min(1,2t)+o(1)}\) at fixed \(t\). Choose a cap \(\eta\) with \(\epsilon<\eta<1/2\). The invariant minor-arc criterion on the step frequency gives normalized savings \(X^{-\min(t,\eta)/2+o(1)}\) in a coordinate of height at least \(X^t\), with arbitrarily small fixed slack. The constant test has at least this saving by the geometric sum. The trivial estimates cover a bin starting at zero.

Write \(s\le t\) for the two exponents, with \(t\ge\gamma\). If both lie below \(\eta\), the multiplicity bound from the lower-height coordinate is at most \(X^{2\epsilon s+o(1)}\), so the exponent of count minus saving is at most \((\epsilon-1/2)(s+t)\). If \(s\le\eta\le t\), it is at most \((2\epsilon-1/2)s-\eta/2\), whose maximum is at most \(\max(-\eta/2,(2\epsilon-1)\eta)\). If both exceed the cap it is at most \(\epsilon-\eta\). The negative of each bound is uniformly bounded below by
\[
\min\bigl\{(1/2-\epsilon)\gamma,\ \eta/2,\ (1-2\epsilon)\eta,\ \eta-\epsilon\bigr\}>0.
\]
The exponents lie in a bounded interval because \(T_i\le b_i^h\le X^{1+o(1)}\). Choose a fixed partition of that interval containing \(\gamma\) and \(\eta\), with mesh sufficiently small relative to the margin above. Using a lower bin endpoint for saving and an upper endpoint for multiplicity changes the exponent by \(O(\text{mesh})\), since the exponent functions are Lipschitz. Fixed analytic slack can also be smaller than the margin. This gives \(O(X^{-c})\) for the high-height modes after summing the finitely many bin pairs. [Progression minor arcs including short prefixes](keybreak-smooth-minor-arc-probes.md)

## Gaussian and moment

The same fiber and lattice calculation applies with cutoff \(\vartheta\le V^\zeta\) for any \(0<2\zeta<1-2\epsilon\). It gives an absolute error \(O(V^{-c'})\) for every nonthin, distinct-denominator pair, with any fixed \(c'<1-2\epsilon-2\zeta\). This includes the common-root image restriction. On a rational-good region the discarded fraction is still a fixed negative power of \(V\). In particular \(\epsilon=3/8\), \(\zeta=1/1000\) permit \(c'=1/5\) at width \(V^{13/8}\). The one-point, interior, and finite conditioning inequalities must be verified using the corresponding field width. [Mixed variation and normalization](keybreak-gaussian-variation.md) · [Ordinary pair transfer](keybreak-narrow-top-moment.md)
