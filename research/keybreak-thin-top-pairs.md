# Thin pairs in KeyBreak’s top boxes

In a fixed root lattice, primitive marks are spaced by the size of the mark along each determinant level. This gives a bound on close pairs from the whole-box rational count alone. In the top box it permits a power-scale determinant cutoff, even after normalizing by ordinary smoothness densities. The rational parent lattice and the algebraic divisor play different roles in an individual private-parent box. [KeyBreak, (G.5) and Lemma G.3](https://crypto.sjtu.edu.cn/factoring.pdf#page=105)

## Determinant levels and repeated denominators

Let \(\mathcal R\) be a set of primitive marks \(P=(a,b)\) in a box of diameter \(O(V)\), with \(b\asymp V\) and \(b>0\). Suppose every mark satisfies \(a\equiv sb\pmod q\) for one fixed \(q\ge 1\) and one residue \(s\). Let \(R=|\mathcal R|\) and let \(W_a\) be the diameter of its first-coordinate range. KeyBreak's eligible marks have \(W_a\le (2/3-1/8)V<V\).

Fix \(P\in\mathcal R\) and write \(P'=(a',b')\) for a second mark. The determinant \(\Delta=ab'-a'b\) belongs to \(q\mathbb Z\). Any two integer solutions to one determinant level differ by an integer multiple of \(P\), since \(\gcd(a,b)=1\). Their spacing is therefore \(\|P\|\asymp V\). There are at most \(L_0=1+\lfloor\operatorname{diam}(\mathrm{box})/\|P\|\rfloor=O(1)\) solutions inside the box on each level. A primitive mark on the zero level is \(P\) or \(-P\), and the positive denominator retains only \(P\). Thus the number of partners with \(|\Delta|\le V^2/K\), for \(K\ge1\), is at most
\[
1+2L_0\left\lfloor\frac{V^2}{qK}\right\rfloor .
\]
The off-diagonal contribution is zero if \(q>V^2/K\), even if the box has very few marks. Applying the same estimate to the maximum determinant in the box also gives \(R=O(1+V^2/q)\) when \(R>0\). In particular, if \(q\asymp V^2\) and the region is nonempty, the diagonal can have a fraction bounded away from zero.

If the denominators coincide, then \(a'-a\) is a multiple of \(q\). At most \(1+2\lfloor W_a/q\rfloor\) partners have the same denominator, including \(P\). For \(q>V\) in the source box, distinct marks necessarily have different denominators. For smaller \(q\) the estimate discards same-denominator pairs without any prime-distribution estimate. With distinct prime denominators and primitive marks, \(b_1b_2\) is coprime to \(\Delta\). Indeed, modulo \(b_i\) the determinant is, up to sign, the product of its own numerator and the opposite denominator.

## Normalization on a rational-good box

Suppose the whole count has \(R\ge cV^2e^{-A H}/q\) for fixed \(c>0\) and \(A\ge0\), where \(H=(\log N)^{1/3}(\log\log N)^{2/3}\). The fractions among the \(R^2\) ordered pairs satisfy
\[
\begin{aligned}
\text{distinct thin pairs}&\ll e^{AH}/K,\\
\text{distinct same-denominator pairs}&\ll e^{AH}/V,\\
\text{diagonal pairs}&=1/R\ll e^{AH}q/V^2.
\end{aligned}
\]
These are bounds with a separate diagonal term. At \(q\asymp V^2\) the first two counts can vanish while the diagonal remains substantial. If \(K=V^\zeta\), \(\zeta>0\) is fixed, and \(q/V^2\le V^{-c_0}\) for fixed \(c_0>0\), the combined fraction is \(O(e^{AH}V^{-\min(\zeta,1,c_0)})\). This is \(\exp(-\Omega(\log V))\) even after any fixed \(\exp(O(H))\) multiplier when \(H=o(\log V)\), as at top scale. In a late box with \(\log V=O(H)\), the stated fractions still apply and a normalized saving requires a comparison of the constants.

For example, let \(Z=\sum_{P\in\mathcal R} w_P f_P\) with \(0\le f_P\le1\), \(0\le w_P\le W\), and conditional mean \(\mu\ge WR\exp(-A'H)>0\). The absolute contribution of a discarded set of ordered pairs to \(\mathbb E[Z^2]/\mu^2\) is at most its pair fraction times \(\exp(2A'H)\). The same argument applies to bounded signed pair terms, allowing an extra \(\exp(O(H))\) in their bound. It uses the set and the mean in the *same* fixed environment and root. For top incoming weights (G.54), the weights within one complete parent band are comparable. The one-point density lower estimate on a rational-good box supplies the required mean-to-size ratio there. The diagonal can alternatively be bounded through \(f_P^2\le f_P\), giving a term at most \(W/\mu\) after normalization. [KeyBreak, (G.6), Lemma G.6, and (G.54)–(G.55)](https://crypto.sjtu.edu.cn/factoring.pdf#page=121)

The geometric \(K\) above specifies only the determinant cutoff. It is independent of the mesh size used to obtain rational-good events in (G.13)–(G.18). Remaining pairs obey \(\vartheta=b_1b_2/|\Delta|\ll K\). An algebraic estimate that uses the original smaller angle bound must still check its grid and progression errors if it is applied with this new cutoff. [KeyBreak, (G.15) and (G.38)](https://crypto.sjtu.edu.cn/factoring.pdf#page=117)

## Which top rational count applies

Write \(w(P)=rb-Qa\), \(x=MV_0/8\), and let \(J\subseteq(P_*,2P_*]\) be a complete band of private parents. The numerator sets entering the aggregate count are
\[
A_p=[x/(2p),x/p]\cap S_B,\qquad A_J=\bigsqcup_{p\in J}pA_p,
\qquad \rho_J=|A_J|/x\asymp\rho_{P_*}/\log P_*.
\]
The scale separation is \(B<b<Y_{\min}<p\) and \(B<q\le Y_1<Y_{\min}\) for an active incoming child, with \(q\ne b\) imposed on its marks. A numerator in \(A_J\) has one prime above \(B\), the parent \(p\), to the first power. In the product convolution \(w b\), the two primes above \(B\) have distinct roles by size. Hence both the parent label of each mark and the factorization of an allowed product into numerator and denominator are unique. For an admissible incoming root, \(v=r-Qs\) is a unit modulo \(Qq\), and the rational congruence is \(w\equiv vb\pmod{Qq}\). In particular the numerator is a unit at \(q\). One can apply the progression estimate for the aggregate numerator by summing the estimates for \(u\in A_p\) in the residues \(p^{-1}vb\pmod q\), using the shorter scale \(x/P_*\) and the normalized cell error (G.17). This is the rational source of \(R\asymp \rho_J V_0^2/(q\log V_0)\) on the incoming-good event. [KeyBreak, (G.11)–(G.17)](https://crypto.sjtu.edu.cn/factoring.pdf#page=107)

For a fixed private parent \(p\), the condition is \(p\mid w(P)\). Since \(p\ne Q\), it defines the geometric root lattice with modulus \(p\) and slope \(rQ^{-1}\pmod p\). The rational count uses the single-parent cofactor convolution modulo \(Q\) in (G.18), yielding \(R\asymp\rho_p V_0^2/(p\log V_0)\) on the parent-good event. Its coefficient law has no algebraic root event at \(p\). For the aggregate incoming count the geometric modulus is the child \(q\), and every counted point is tested under the same coefficient-root event at \(q\). The paired geometry does not convert an aggregate good count into a good count with both a particular parent and a child prescribed. Off the incoming-good event the aggregate root-average bound (G.14) and the weighted Cauchy–Schwarz step of (G.53) are still needed. [KeyBreak, (G.18) and (G.53)–(G.55)](https://crypto.sjtu.edu.cn/factoring.pdf#page=121)

Both geometric moduli have a fixed power margin below \(V_0^2\) in the source top ranges. For example, \(\log V_0/\log Y_0\to 51/100\) and \(\log Y_1/\log Y_0\to 51/430\), so the exponent of \(Y_0/V_0^2\) in base \(V_0\) tends to \(-2/51\), and that of \(Y_1/V_0^2\) tends to \(10/43-2\). These facts, along with \(\log\rho_p^{-1},\log\rho_J^{-1}=O(H)\), are the margins used in the normalized pair estimate. [Top band ratios and preserved margins](keybreak-private-band-stages.md)

## Conditioning on the public root and dividing

Fix two distinct incoming marks with \(a_i\equiv sb_i\pmod q\), \(q\nmid b_i\), and a nonexcluded child root. Homogeneity gives \(F(a_i,b_i)\equiv b_i^d F(s,1)\pmod q\). Thus the event \(R_{q,s}\) is determined by either evaluation coordinate modulo \(q\), and its restriction to the joint image is exactly that both coordinates are divisible by \(q\). Lemma G.4 preserves the relative Gaussian image comparison under this restriction. Its probability under the original coefficient law is comparable to \(1/q\) for admissible roots in the stated range. That probability is charged when averaging over roots, not again in a moment under the conditional law. The finite coefficient-sampler error can increase under conditioning, as in G.4. [KeyBreak, Lemma G.4 and (G.20)](https://crypto.sjtu.edu.cn/factoring.pdf#page=109)

Let \(G_i=G(P_i)\) and \(\Delta=|\det(P_1,P_2)|>0\). The original two-value separate periods are \(m_i^{\mathrm{raw}}=2|G_i|\Delta\). They are divisible by \(q\), so restricting to both raw values divisible by \(q\) retains the separate raw period. Upon division the shifted support has the separate periods of (G.21), \(m_i=2|G_i|\Delta/q\), and \(\Delta/q\) phase pairs. The center is \(F_0(P_i)/q\) and the marginal Gaussian parameter is \(T_i=T_i^{\mathrm{raw}}/q\), where \(T_i^{\mathrm{raw}}=2\sigma|G_i|\|v(P_i)\|\). The center need not be in the support. For the same fixed pair, an endpoint parameter such as \(X_i=8n^{11}T_i\) and a grid side proportional to \(T_i/\vartheta\) also scale by \(1/q\). Consequently
\[
\frac{X_i}{m_i}=\frac{X_i^{\mathrm{raw}}}{m_i^{\mathrm{raw}}},
\qquad
\frac{T_i}{\vartheta m_i}=\frac{T_i^{\mathrm{raw}}}{\vartheta m_i^{\mathrm{raw}}}.
\]
These identities compare widths and periods at the same pair. Smoothness densities and admissibility of a root remain separate inputs. For an individual top private parent the algebraic divisor in these formulas is one, even though \(p\mid\Delta\) from the rational geometry. [KeyBreak, (G.21)–(G.24) and Lemma G.9](https://crypto.sjtu.edu.cn/factoring.pdf#page=110)
