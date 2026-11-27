# Raw quadratic marks through a random root

For almost every residue modulo a prime, a coefficient box of side greater than the cube root of the prime contains the expected number of primitive quadratics vanishing there. The statement is unconditional and applies to a fixed smooth weight supported entirely on irreducible quadratics. It proves the raw population estimate in the quadratic-top cost comparison. The smoothness of the rational values and of the algebraic resultants remains a separate requirement. [Quadratic top budget](keybreak-quadratic-top-budget.md)

## Count for one prime

Write \(f(X,Y)=aX^2+bXY+cY^2\), fix \(0<\epsilon<1/3\), and let \(p^{1/3+\epsilon}\le V\). Take a smooth nonnegative compactly supported weight \(w\) on \(\mathbb R^3\) and a bounded family of translations \(v/V\). Suppose every translated support is disjoint from the origin and lies in \([-CV,CV]^3\), with fixed \(C\) and \(CV<p\). For all but an \(O(p^{-\epsilon/4+o(1)})\) fraction of \(t\bmod p\),
\[
 \sum_{\substack{f(t,1)=0\bmod p\\ \gcd(a,b,c)=1}}
 w(((a,b,c)-v)/V)
 =\frac{V^3}{p}\left(\frac{\int w}{\zeta(3)}+O(p^{-\epsilon/4+o(1)})\right).
\]
The exceptional set works for every such translate at the stated scale. Choosing support in a small box near \((1,0,1)\) gives primitive irreducible quadratics with positive leading coefficient, since their real discriminants are negative. An anchor \((r,Q)\) with \(p\nmid Q\) imposes this same congruence at \(t=r/Q\bmod p\). If \(r\) is uniform in an interval of length \(T\), a set of exceptional roots of density \(h\) has probability at most \(h(1+p/T)\). A restricted or weighted law for the anchor needs a corresponding comparison.

The congruence lattice \(\Lambda_t\) has index \(p\). Its dual modulo \(\mathbb Z^3\) consists of the \(p\) multiples of \((t^2,t,1)/p\), since these annihilate the lattice and already give \(p\) distinct classes. Put \(\rho=p^{-1/3-\epsilon/4}\), \(L=\lfloor p\rho\rfloor\). A nonzero dual vector of sup norm at most \(\rho\) yields centered integer numerators \((x,y,z)\) bounded by \(L\), with \(z\ne0\) and \(xz\equiv y^2\pmod p\). Conversely each such triple gives precisely one root \(t=y/z\pmod p\) and one dual vector in this short box. For each \(y\) there are \(O(1+L^2/p)\) possible integers \(j\) with \(xz=y^2+jp\). For a nonzero right side the number of signed factor pairs is \(p^{o(1)}\) by the elementary divisor bound. A zero right side requires \(y=x=0\) and gives at most \(2L\) further triples. The probability of any short vector is therefore
\[
 \ll p^{o(1)}(L^3/p^2+L/p)
 \ll p^{-3\epsilon/4+o(1)}+p^{-1/3-\epsilon/4+o(1)} .
\]

For every other root the dual vectors are mutually separated in sup norm by at least \(\rho\). Disjoint cubes bound the number of dual vectors of norm at most \(k\rho\) by \(O((1+k)^3)\). By Poisson summation and rapid decay of \(\widehat w\), for every fixed \(A>0\) and \(W\rho\ge1\) the sum of \(w((x-u)/W)\) on \(\Lambda_t\) equals
\[
 \frac{W^3}{p}\bigl(\textstyle\int w+O_{w,A}((W\rho)^{-A})\bigr).
\]
The estimate is uniform in the shift \(u\) because the shift contributes only phases. This also gives raw counts before any primitivity restriction.

For primitivity, take \(D=\lfloor p^{\epsilon/4}\rfloor\). For each divisor variable \(k\le D\), points with all coefficients divisible by \(k\) are counted at scale \(W=V/k\) and translate \(u=v/k\) in the same lattice. Here \(W\rho\ge p^{\epsilon/2}\). Inclusion-exclusion through \(D\) gives main term \((V^3/p)\int w\sum_{k\le D}\mu(k)/k^3\), with a power-saving relative error of arbitrarily large order on the good roots. For \(D<k\le CV<p\), there are \(O_C((V/k)^3)\) possible nonzero divided vectors anywhere in the containing cube. Each gives a nonzero polynomial over \(\mathbb F_p\) with at most two roots. The expectation of the absolute omitted tail, including all translates using the common enclosing cube, is \(O_{C,w}(V^3/(pD^2))\). By Markov it is at most \(V^3/(pD)\) outside a fraction \(O_{C,w}(D^{-1})\). The Euler-product tail for the main term is \(O(D^{-2})\). This proves the stated estimate and includes the cost in exceptional roots of removing large contents.

## How many quadratic fields a full box needs

Let \(\mathcal D\) contain \(K\) signed squarefree discriminant representatives. An irreducible form of height at most \(V\) in this family satisfies \(b^2-4ac=D s^2\ne0\), with \(1\le s\ll V/\sqrt{|D|}\). For each \((b,D,s)\), the nonzero product \(4ac=b^2-Ds^2\) determines at most \(V^{o(1)}\) choices of \((a,c)\). There are at most two signed representatives for each absolute value, so \(\sum_{D\in\mathcal D}|D|^{-1/2}=O(\sqrt K)\). The whole family contains at most \(V^{2+o(1)}\sqrt K\) marks. In particular a family of \(V^{3-o(1)}\) marks uses \(V^{2-o(1)}\) distinct fields. If the squarefree parts have size at most \(V^\gamma\), the bound is \(V^{2+\gamma/2+o(1)}\) for \(0\le\gamma\le2\). This quantifies the loss from restricting the fields available to an analytic count.

## Rectangular boxes and two root conditions

There is also a raw count when the three side lengths are different and independent roots are imposed at two distinct primes. More generally let \(P\) be squarefree and \(t\) uniform modulo \(P\), which is equivalent to independent uniform choices at its prime divisors. Let \(A,B,C\ge P^\beta\), \(ABC\ge P^{1+\eta}\), with fixed positive \(\beta,\eta\). Choose \(0<\delta<\min(\beta,\eta/3)\) and set \(R=P^\delta\). Outside a proportion \(O(P^{-c})\) of roots for some \(c>0\), every nonzero dual vector \(\xi\) has \(\|(A\xi_1,B\xi_2,C\xi_3)\|_\infty>R\). Consequently the smooth translated count is
\[
 (ABC/P)\bigl(\textstyle\int w+O_{w,K}(R^{-K})\bigr)
\]
for every fixed \(K>0\). This version counts all coefficient triples. For the pair of primes its congruence combines two prescribed root residues using CRT. The volume hypothesis concerns the product of the two primes. Coverage under separate one-prime volume hypotheses does not follow from it.

Integral dual vectors are excluded by the shortest side. A nonintegral class has exact denominator \(m\mid P\), \(m>1\). The centered numerators are bounded by \(L_A=Rm/A,L_B=Rm/B,L_C=Rm/C\), all less than \(m/2\). The numerator \(z\) is a unit modulo \(m\), and \(xz\equiv y^2\pmod m\) determines the slope \(t=y/z\bmod m\). There are no such vectors for \(L_C<1\). A zero coordinate \(x\) or \(y\) forces \(x=y=0\) because \(m\) is squarefree, giving only the slope zero modulo \(m\). Otherwise \(L_A,L_B,L_C\ge1\). For fixed \(y\), \(xz\) lies in an interval of length \(2L_A L_C\), so only \(O(1+L_A L_C/m)\) choices of its value are congruent to \(y^2\); each has \(P^{o(1)}\) signed factor pairs. Alternatively, each fixed \((x,z)\) permits at most \(2^{\omega(m)}\) residues for \(y\), by CRT and squarefreeness. Dividing the smaller of these counts by \(m\), the exceptional probability at this denominator is at most
\[
 \frac1m+P^{o(1)}
 \left(\frac{R^3m}{ABC}+
 \min\left(\frac RB,\frac{R^2m}{AC}\right)\right)
 \le \frac1m+P^{o(1)}\left(\frac{R^3m}{ABC}+\sqrt{\frac{R^3m}{ABC}}\right).
\]
Only \(m\ge C/R\) contribute. Summing over \(P^{o(1)}\) divisors gives a power saving by the chosen margins. The scaled dual packing and Poisson estimates then apply exactly as in the cubic box. A bare inequality \(ABC>P\) cannot imply uniform asymptotic density over all translates. At \(ABC=2P\), the scaled dual has determinant two. Minkowski supplies a nonzero vector of bounded sup norm; its Fourier coefficient for a fixed Gaussian is bounded away from zero. By orthogonality over the translation torus, the relative Gaussian count cannot converge uniformly to its mean.

## The remaining rational smoothness condition

For a physical anchor of size \(r,Q\asymp M\) with \(Q\) an odd prime, the rational cofactor \(n=f(r,Q)/p\) has scale \(X\asymp M^2 V/p\). For a fixed \(r\), its first two base-\(Q\) digits satisfy \(pn\equiv ar^2+brQ\pmod{Q^2}\). Even if a product set of size \(S\) has nonprincipal character bounds \(SX^{-1/2}V^{o(1)}\), a direct application of multiplicative Parseval to \(\asymp V^2\) distinct unit phases yields absolute error of order at most \(SV X^{-1/2}V^{o(1)}\). Relative to its main term \(SV^2/\phi(Q^2)\), the bound costs \(M\sqrt p/V^{3/2}\) up to subpower factors. This calculation uses a common interval cutoff, already a more favorable situation than varying the cofactor interval with each mark. It leaves a large error even just above the cube-root threshold. If \((a,Q)=1\), then \(ar^2+brQ\equiv a(r+bQ/(2a))^2\pmod{Q^2}\). Averaging over all unit lifts of \(r\bmod Q^2\) would reduce this congruence to a quadratic character modulo \(Q\). An interval of length at most \(Q\) supplies at most one representative of each base residue. Any proof using this reduction must control the unaveraged second digit in the physical anchor law. The raw coefficient count above imposes no predicate on that cofactor.
