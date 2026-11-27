# Smooth residue variance at the square-root digit width

At \(\epsilon=1/2\), Parseval turns the proposed mean-square replacement for absolute mode summation into a variance of smooth counts at a single prime-power modulus. The diagonal has a power saving on the relevant progression scale. An aggregate estimate for the off-diagonal smooth pairs is still required for two smooth predicates. With at least one constant predicate, the full sum already saves a power by geometric summation. [The weighted-height bound below the endpoint](keybreak-weighted-rational-height.md)

## Exact identity and the missing correlation

Index the points of one progression by \(n=r+mk\), where \(k\) lies in an integer interval \(I\) of \(K\) points. Let \(f(k)\) indicate a nonzero value with \(y\)-smooth absolute value, and set \(\mu=K^{-1}\sum_I f(k)\). For the step-frequency grid of denominator \(Q=b^h\), write

\[
\widehat f_0(a)=\frac1K\sum_{k\in I}(f(k)-\mu)e(ak/Q).
\]

For \(z\bmod Q\), let \(n_z=\#\{k\in I:k\equiv z\bmod Q\}\) and \(S_z=\sum_{k\in I,\ k\equiv z\bmod Q}f(k)\). Additive orthogonality gives

\[
\begin{aligned}
\mathcal E_Q(I)
  :=\sum_{a=1}^{Q-1}|\widehat f_0(a)|^2
  &=\frac{Q}{K^2}\sum_{z\bmod Q}(S_z-\mu n_z)^2\\
  &=\frac{Q}{K^2}\sum_{j\in\mathbb Z}
       \sum_{\substack{k\in I\\ k+jQ\in I}}
       (f(k)-\mu)(f(k+jQ)-\mu).
\end{aligned}
\]

The diagonal is \(\mu(1-\mu)Q/K\). The raw shift in the inner sum is \(mjQ\), with the same support phase in both factors. Writing \(R=K/Q\), for \(Q\mid K\) the off-diagonal statement can use uncentered counts:

\[
\mathcal E_Q(I)=\frac{\mu(1-\mu)}{R}
+\frac{Q}{K^2}\left(2\sum_{1\le j<R}
   \#\{k,k+jQ\in I:f(k)=f(k+jQ)=1\}
-\mu^2 K(R-1)\right).
\]

At the endpoint of interest \(Q/K\le V^{-1/2+o(1)}\) and \(\mu=V^{-o(1)}\) on the good phases under consideration. Thus a sufficient input for a relative saving is an upper bound \(O(\mu^2 K R\,V^{-c})\), for fixed \(c>0\), on the parenthesized discrepancy. It asks for the independent main term with a small additive error after averaging over the shifts. A pair upper bound with an uncontrolled multiplicative constant gives an error on the scale \(\mu^2KR\) or larger. With two coordinates, injectivity of each short-mode map into its own grid and Cauchy–Schwarz bound the sum of products of their centered coefficients by \(\sqrt{\mathcal E_{Q_1}(I_1)\mathcal E_{Q_2}(I_2)}\). This uses the sum of squared normalized Fourier coefficients without another division by \(Q_i\). A full-grid bound suffices; a bound on the smaller selected sets could suffice as well. [Injectivity of the native frequency maps](keybreak-dual-major-arc-count.md)

If endpoint maxima are needed, it is enough to bound a dyadic tree of intervals. For each block \(B\), use its own mean \(\mu_B\) in the exact variance, while keeping the normalization \(1/K\), and let the resulting energy be \(\mathcal E(B)\). An arbitrary subinterval is a union of \(O(\log K)\) blocks. Cauchy–Schwarz then bounds the sum over \(a\ne0\) of squared maximal centered sums by \(O(\log K)\sum_B\mathcal E(B)\). Restoring the block means adds \(O((Q/K)^2(\log K)^2)\) to this squared bound, by the geometric sum and \(\sup_B\mu_B\le1\). Indeed each restored coefficient is bounded by \(O(\log K)/(K\|a/Q\|)\). For blocks of length at most \(K V^{-\lambda}\) with fixed \(\lambda>0\), the trivial occupancy bound \(\max_z n_{B,z}\le |B|/Q+1\) gives a total energy at each level \(O(\mu(V^{-\lambda}+Q/K))\), using \(\sum_B\sum_{k\in B} f(k)=K\mu\) at that level. Powers of \(\log K\) are \(V^{o(1)}\). Thus only the long blocks need a new variance input for this approach.

## A power saving for a constant predicate

For the constant test, every interval coefficient at \(a\ne0\) is bounded by \(O(1/(K\|a/Q\|))\) uniformly in its endpoints. By injectivity, summing over just the short modes costs at most

\[
\sum_{a=1}^{Q-1}\frac{O(1)}{K\|a/Q\|}\ll \frac{Q}{K}\log(2Q).
\]

Multiply by a trivial \(O(1)\) normalized interval bound for the other predicate. With normalization by the full progression scale, this gives \(V^{-1/2+o(1)}\) unconditionally for any product with one constant test. In particular the denominator comparison has no smooth-pair variance requirement at this width. Independent uniform translation of the entire frequency grid also removes the variance issue for any predicate: integrating the grid's total squared coefficient over one cell with normalized Lebesgue measure gives exactly the diagonal \(QK^{-2}\sum_I|f-\mu|^2\). This averaging statement assumes the translation; the exact rational grid does not come with that randomness.

## What the available progression bounds imply

Consider the usual case \(y<b\) and \((m,b)=1\). Write \(n=gu\) with \(g=(r,m)\) smooth, \(m'=m/g\), and \(u\equiv r'\bmod m'\) a unit progression. The interval of \(u\)'s is bounded by \(U\asymp m' K\) in absolute value for a top-scale interval. Its \(y\)-smooth integers are units modulo \(Q=b^h\), and \(k\mapsto u=r'+m'k\bmod Q\) is a bijection. For a nonprincipal multiplicative character \(\chi\bmod Q\), orthogonality over \(m'\) writes the conditional character sum as an average of smooth sums twisted by the nonprincipal \(\chi\psi\bmod m'Q\). Thus the imprimitive-inclusive estimate (G.7), differenced at the interval endpoints, bounds each conditional sum by \(O_\tau(U^{1/2+\tau}(m'Q)^\tau)\). Multiplicative Parseval gives

\[
\sum_{a\in(\mathbb Z/Q)^\times}
  \left(S_a-\frac{K\mu}{\phi(Q)}\right)^2
\ll_\tau U^{1+2\tau}(m'Q)^{2\tau}.
\]

Here \(S_a\) indexes the unit residue of \(u\); the other residue counts are zero. Comparing this center to the additive one costs \(O(\mu^2/b+\mu^2(Q/K)^2)\) in normalized additive energy. Indeed the flat profile on the \(\phi(Q)\) unit classes has normalized squared distance \(\mu^2(Q/\phi(Q)-1)=\mu^2/(b-1)\) from the flat profile on all \(Q\) classes. Replacing the uniform class-size center by \(n_z\) incurs at most \(O(\mu^2(Q/K)^2)\), since \(|n_z-K/Q|\le1\). Therefore the input (G.7) used in this way yields

\[
\mathcal E_Q(I)\ll_\tau
  \frac{m'Q}{K}U^{2\tau}(m'Q)^{2\tau}
  + \frac{\mu^2}{b}+\mu^2(Q/K)^2.
\]

At a fixed power gap \(Q\le K^{1-c_0}\) with \(m'=K^{o(1)}\), suitable fixed \(\tau>0\) gives a power saving. At \(Q=K V^{-1/2+o(1)}\) even \(m'=1\) leaves the fixed-\(\tau\) loss larger than the desired saving when \(\log K/\log V\to\infty\). The theorem does not give constants allowing \(\tau\) to tend to zero with that ratio. An extra Parseval over all unit translates modulo \(m'\) improves the first term by \(1/\phi(m')\) at a common endpoint, while the loss from the large modulus persists and the resulting estimate averages over translates. [KeyBreak, (G.7)–(G.8)](https://crypto.sjtu.edu.cn/factoring.pdf#page=106)

The ordinary additive large sieve gives \(O(\mu)\) by the \(1/Q\) frequency separation, because \(Q<K\). This also follows by capping occupancies directly, and it is larger than the required \(\mu^2 V^{-c}\). The one-dimensional short-interval upper estimate controls one smooth count at a time, rather than the centered product. Similarly, peeling one smooth factor from each shifted value gives upper counts in simultaneous divisibility classes. Summing those positive bounds alone supplies no subtraction of the independent main term in the identity. [Harper’s one-dimensional short-interval upper bound](https://arxiv.org/pdf/1408.1662#page=13)

The variance theorem of Harper averages over ordinary moduli. Pascadi's fixed-residue distribution theorem also sums over moduli and has a fixed power gap below \(K\). The linear-forms theorem of Matthiesen–Wang for simultaneous smoothness has a larger smoothness cutoff than the fixed top bands here. These statements leave the required fixed large prime-power variance untreated. [Harper, Corollary 1](https://arxiv.org/pdf/2412.19644#page=9) · [Pascadi, Theorem 1.1](https://arxiv.org/pdf/2304.11696#page=2) · [Matthiesen–Wang, Theorem 1.3](https://msp.org/ant/2025/19-10/ant-v19-n10-s.pdf)

## A bounded-weight example separating the inputs

Take \(Q\mid K\) with \(Q=K^{1-o(1)}\), \(Q=b^h\), \(b\) an odd prime and \(h\ge2\). There is a unit \(a\bmod Q\) such that \(\|as/Q\|\ge1/(\sqrt K\log K)\) for \(1\le s\le\sqrt K\). For uniform \(a\bmod Q\), the excluded fraction at each \(s\) is at most \(2/(\sqrt K\log K)+O((s,Q)/Q)\). The sum of the gcd terms is \(O((h+1)\sqrt K/Q)=o(1)\), using \((s,Q)=\sum_{b^j\mid s,\ j\le h}\phi(b^j)\). Excluding nonunits still leaves a choice. On a dyad of \(K\) consecutive integers consider the bounded profile

\[
F(k)=\frac{\mu}{1-1/b}\,1_{b\nmid k}\bigl(1+\cos(2\pi ak/Q)\bigr),
\qquad 0<\mu\le(1-1/b)/2.
\]

Its one-dimensional counts are bounded by \(O(\mu)\) times the interval length in integer points. On every progression the oscillating part has sum \(O(\mu\sqrt K\log K)\) on subintervals of the dyad, by the geometric sums for steps at most \(\sqrt K\) and occupancy for larger steps. To handle the unit mask, subtract the progression restricted to \(b\mid k\), with step \(\operatorname{lcm}(b,s)\). The flat unit profile gives the same principal count up to \(O(\mu)\) in classes with the same gcd with \(s\). Thus even centering each class by its gcd-group average leaves only a square-root-sized progression discrepancy. Nevertheless the mean of \(F\) is \(\mu\) and its normalized additive coefficient at \(a\) has magnitude \(\mu/2\), since the unit Ramanujan sums at \(a\) and \(2a\) vanish for \(h\ge2\). This supplies energy \(\gg\mu^2\). The example concerns the information in progression-count and upper-bound inequalities for bounded weights. It makes no assertion about the full multiplicative input (G.7) or the smooth indicator.

## Why the all-typical-moduli GRH variance has a different scale

Klurman–Mangerel–Teräväinen’s Theorem 1.4 bounds the sum of squared discrepancies over the reduced classes modulo \(q\) by \(O(\varepsilon_0\phi(q)(x/q)^2)\). It requires \(q\le Q_0\le x/10\) and \(\varepsilon_0\ge(\log(x/Q_0))^{-1/200}\). GRH removes the exceptional-set condition for \((x/Q_0)^{\varepsilon_0^2}\)-typical moduli. Proposition 9.2 removes typicality too, with \(\varepsilon_0^{1-3\Delta(q,(x/Q_0)^{\varepsilon_0})}\) in place of \(\varepsilon_0\), where \(\Delta\) measures the maximum local density of prime factors. A prime power \(q=b^h\) with \(b\to\infty\) is typical, and its \(\Delta=o(1)\). For \(x/q=V^{\Theta(1)}\), normalization by \(q/x^2\) still gives only an absolute \(O(\varepsilon_0)\) bound, whose smallest parameter is of order \((\log V)^{-1/200}\). This is above the scale \(\rho^2=\exp(-\Theta(d\log d))\) in the fixed top bands. For a preselected unit phase modulo \(m'\), applying the result to \(q=m'b^h\) and discarding other phases can cost another factor \(m'\) in the normalized bound. [Klurman–Mangerel–Teräväinen, Theorem 1.4 and Proposition 9.2](https://doi.org/10.1112/plms.12546)

Theorem 1.3 is unconditional for typical \(q\) with \(P^+(q)\le q^{\exp(-\varepsilon_0^{-3})}\), and gives the same absolute right-hand side. For \(q=b^h\) this condition is exactly \(h\ge\exp(\varepsilon_0^{-3})\), so it forces \(\varepsilon_0\ge(\log h)^{-1/3}\) when the parameter tends to zero. Theorem 1.2 for multiplicative functions supported on \(x^\eta\)-smooth integers gives an absolute maximum deviation \(O(\varepsilon_0 x/q)\), with fixed \(\eta>0\) and \(q\le x^{1/2-100\eta}\), also under GRH for every modulus in that range. It does not reach the endpoint modulus. [Klurman–Mangerel–Teräväinen, Theorems 1.2 and 1.3](https://doi.org/10.1112/plms.12546)

The published large-modulus proof has a specific obstruction to substituting a smooth count into its generic error term. Its last prime interval starts at \(P_J=x^{\varepsilon_0^2}\). For \(P_J\le y\), the allowed lower bound on \(\varepsilon_0\) requires \(\log(x/Q_0)\ge(\log x/\log y)^{100}\). In the fixed top bands the left side is \(O(d^2\log d)\), while \((\log x/\log y)^{100}\asymp d^{100}\). Thus the hybrid well-factorable set in §9.3 misses the smooth support, and the last prime block for the remaining characters in §9.4 vanishes. Their geometric or generic sieve error still applies to that contribution. The auxiliary smooth-conductor prime-sum lemma also needs \(P>q^{1/(\log\log q)^{0.9}}\), larger than the smooth cutoff here. [Klurman–Mangerel–Teräväinen, §§9.3–9.4 and Lemma 10.2](https://doi.org/10.1112/plms.12546)

For the smooth indicator, the squared pretentious distance to \(\chi(n)n^{it}\) equals the harmonic prime sum over \(y<p\le x\) with \(p\nmid q\), plus \(\sum_{p\le y,\ p\nmid q}(1-\Re(\overline{\chi(p)}p^{-it}))/p\). The principal character at \(t=0\) attains the minimum exactly. At \(q=b^h\) the minimum is \(\log(\log x/\log y)+O(1)\), and all such distances squared are \(O(\log\log x)\). An exponential in this distance, as in Halász’s estimate, therefore operates on a logarithmic scale, and the theorem's variance error does not carry even that factor. The saddle-point tilt \(1_{P^+(n)\le y}n^{1-\alpha}\) is unbounded, outside the theorem; a \(1\)-bounded tilt on the same support has mean at most \(\rho\). The negative tilt \(n^{-(1-\alpha)}\) is admissible, but undoing it on a dyad multiplies squared-error bounds by a factor of order \(x^{2(1-\alpha)}\). These substitutions leave open an estimate using saddle-point analysis directly on the large-modulus mean square. [Klurman–Mangerel–Teräväinen, (4), Remark 1.1 and Lemma 7.4](https://doi.org/10.1112/plms.12546)
