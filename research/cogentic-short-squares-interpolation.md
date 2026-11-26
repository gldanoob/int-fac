# Short square products under randomized NFS interpolation

Let \(D=(\log N/\log\log N)^{1/3}\), \(H=D\log\log N\) and \(V=DH\). Fix one input \(N\), one radix \(m\), and an integer polynomial \(f_0\) with \(f_0(m)=N\). In Lee–Venkatesan's randomization \(f=f_0+(X-m)G\), the coefficients of \(G\) are independently uniform in integer intervals of width \(\exp(\Omega(V))\) when the coefficient slack \(\kappa-\delta^{-1}\) is fixed and positive. The statement below is uniform in \(m\) and \(f_0\). It also applies when the perturbation vanishes at prescribed marks. [Lee–Venkatesan, Algorithm 2, Definition 4.1 and §7](https://arxiv.org/pdf/1805.08873)

## Short products in the coefficient ensemble

Fix a constant \(C\), and allow primitive marks \((a,b)\) with \(b>0\) and \(\max(|a|,b)\le e^{CH}\), taking at most one copy of each slope in a field. Let \(M(X)\in\mathbb Z[X]\) be primitive of degree \(O(D)\) and divisible by \(X-m\). Sample
\[
 f(X)=f_0(X)+M(X)G(X),
\]
where the constant and linear coefficients of \(G\) are independently uniform on integer intervals of lengths at least \(e^{c_0V}\) for a fixed \(c_0>0\). The remaining coefficients can be held fixed, or sampled independently of these two. There exist \(c_1,c_2>0\) such that the probability that \(f\) is irreducible of degree at least two and a nonempty product of at most \(c_1D/\log\log N\) distinct marks is a square in \(\mathbb Q[X]/(f)\) is at most
\[
 \exp(-c_2 V/\log V).
\]
The constants can be chosen uniformly over the given mark box and coefficient intervals. If irreducibility and degree at least two are accepted with probability bounded below, the same estimate holds up to a constant factor in the accepted ensemble.

To prove this, fix a product polynomial \(P(X)=\prod_{i=1}^k(a_i-b_iX)\) and use the prime interval \([cV,2cV]\), where \(c>0\) is a sufficiently small constant depending on \(c_0\). By the prime number theorem the interval contains \(\gg V/\log V\) primes, and the product \(Q\) of these primes is at most \(e^{c_0V/2}\). Discard the primes dividing
\[
 b_1\prod_{i>1}(a_1b_i-a_ib_1).
\]
This product is nonzero and has absolute logarithm \(O(kH)\). The discarded subset has size \(O(kH/\log V)=o(V/\log V)\) in the claimed range. At every remaining \(p\), the first slope is a simple zero of \(P\bmod p\), so \(P\bmod p\) has a geometrically nonsquare factor. The quadratic character sum bound gives at least \(p/3+\deg M\) points of \(\mathbb F_p\) where \(P\) is a nonresidue, for all sufficiently large \(N\). Indeed, the character sum has absolute value at most \(k\sqrt p\) and there are at most \(k\) zeros. Here \(k=o(\sqrt p)\) and \(\deg M=o(p)\). The reduction of primitive \(M\) is nonzero. Discard its roots to obtain a set \(T_p\) with at least \(p/3\) points. [Weil, *On Some Exponential Sums*](https://doi.org/10.1073/pnas.34.5.204)

Modulo \(p\), use the uniform law for the two free coefficients of \(G\). At each \(t\in T_p\), the pair \((f(t),f'(t))\) is uniform because \((G(t),G'(t))\) is uniform and the transformation has determinant \(M(t)^2\ne0\). At distinct \(t,u\in T_p\), the values \((f(t),f(u))\) are uniform by linear interpolation. Let \(Z_p\) count simple roots of \(f\) in \(T_p\). Then
\[
 \mathbb E Z_p=|T_p|p^{-1}(1-p^{-1}),\qquad
 \mathbb E Z_p^2\le \mathbb E Z_p+|T_p|(|T_p|-1)p^{-2}\le2 .
\]
Consequently \(\Pr[Z_p>0]\) is bounded below by a positive constant. Such a simple root lifts to \(\mathbb Z_p\). For irreducible \(f\) it induces an embedding \(\mathbb Q[X]/(f)\to\mathbb Q_p\). Under this embedding \(P\) is a unit with nonsquare residue, so it cannot be a square.

For uniform coefficients modulo \(Q\), the tests at distinct primes are independent. Their joint failure probability is \(\exp(-\Omega(V/\log V))\). The law induced by the integer box differs in total variation by \(O(Qe^{-c_0V})\), which is exponentially smaller. There are at most \(\exp(O(kH))\) supports of length at most \(k\). Choosing \(c_1\) small enough makes the union bound retain the negative exponent, since \(V/(H\log V)\asymp D/\log\log N\).

One can also use a smaller shared width \(W\) by replacing \(V\) with \(\Lambda=\log W\) in the prime interval and CRT argument. For \(\Lambda=O(V)\) and \(\Lambda/(H\log\Lambda)\to\infty\), this excludes support up to \(c_1\Lambda/(H\log\Lambda)\) with failure probability \(\exp(-\Omega(\Lambda/\log\Lambda))\). In particular this still rules out bounded support at vanishing coefficient slack provided \(\Lambda/\log\Lambda\gg H\).

## Exact interpolation at fixed marks

For finitely many prescribed slopes \((u_i,v_i)\), use
\[
 M(X)=(X-m)\prod_i(v_i X-u_i)
\]
with each \((u_i,v_i)\) primitive. Every integer homogeneous value \(v_i^{\deg f}f(u_i/v_i)\) is fixed as \(G\) varies at a fixed degree. The multiplier is primitive and has degree \(O(D)\) as long as the number of prescribed marks does. If a bounded-degree interpolation plant retains the above two wide independent coefficients in \(G\), the short-square exclusion applies even when those fixed values are smooth. It also applies to any short product involving unplanted marks.

If a single-input algorithm makes \(\exp(O(H))\) fresh draws, the probability of encountering an accepted field with such a short square still has scale \(\exp(-\Omega(V/\log V))\), since \(V/\log V\gg H\). The conclusion holds for adaptive choices of \(m,f_0,M\) that obey the stated conditional coefficient law on each draw. A useful multi-field dependency of total support below the threshold would require a nonempty square product below the threshold in at least one field. Therefore this particular method for attaching a bounded-size useful dependency cannot preserve the wide independent coefficient law. The conclusion leaves long acquired dependencies and specialized field selection open. All draws and mark generation here concern the same input.

## An explicitly selected family with positive sign rank

Take \(m=7\cdot2^{44k}\) for \(k\ge1\), and set
\[
 A=m+1,\qquad B=9m^2-5m+1,\qquad N=AB .
\]
The two quadratic polynomials
\[
 f_+(X)=(2X-1)^2+9m^2X,\qquad
 f_-(X)=(4X-1)^2+(2-3m)^2X
\]
satisfy \(f_+(m)=f_-(m)=N\). Their discriminant squareclasses are represented by \(9m^2-8\) and \((3m-2)^2-16\). Both are positive nonsquares by comparison with consecutive squares. The first has odd \(2\)-adic valuation and the second even \(2\)-adic valuation, so the quadratic fields are distinct.

The numbers \(A,B\) are odd and coprime because \(B\bmod A=15\) and \(m\equiv1\bmod3,\ m\equiv2\bmod5\). Both leading coefficients, \(m\), and the square-root denominators \(3m\) and \(2-3m\) are units modulo \(N\). For the latter denominator, a common prime with \(A\) or \(B\) would divide \(5\). The two derivatives at \(m\) are also units. After dividing by the corresponding square-root denominator, their residues modulo \(A\) are \(1,-3\), and modulo \(B\) they are \(15m-4,21m-6\). A common prime of \(B\) and \(15m-4\) divides \(69\), and a common prime of \(B\) and \(21m-6\) divides \(15\). These are excluded because \(m\equiv7\bmod23\), \(m\equiv1\bmod3\) and \(m\equiv2\bmod5\).

In both fields, acquire the primitive mark \((0,1)\) using rational smoothness bound \(7\). Its rational norm is \(-m\), and the homogeneous algebraic norms are both \(1\). All field-element valuations away from \(2\) vanish, since the algebraic element is integral there and has norm \(1/4\) or \(1/16\). The exact square identities in the fields are
\[
 -\theta_+=\left(\frac{2\theta_+-1}{3m}\right)^2,\qquad
 -\theta_-=\left(\frac{4\theta_--1}{2-3m}\right)^2 .
\]
The product of the two rational marks has root \(m\). Modulo \(A\), the evaluated field roots are \(1,-1\); modulo \(B\), they are both \(3m-1\). Thus the algebraic root product is \(m\bmod A\) and \(-m\bmod B\). The gcd of its difference from \(m\) with \(N\) is exactly \(A\). The resulting two-column relation space has a one-dimensional certified dependency space with sign rank one. [Sign map on verified dependencies](cogentic-mnfs-sign-map.md)

The same formulas give a Blum semiprime example at \(m=130\), with \(A=131,\ B=151451\) prime, both \(3\bmod4\). At that point the rational mark is \(13\)-smooth, both field derivatives are units, and the discriminant squareclasses are \(47\cdot809\) and \(3\). This example and the infinite family use explicit fields and directly identifiable factors. The polynomials have different leading coefficients and hence belong to no single linear-shift fan. Their fixed degree, coefficient height, and chosen radix fall outside the asymptotic Lee–Venkatesan ensemble.

An exact replay checked the square identities, unit conditions and proper gcd for the first 100 family members and the Blum example. It also enumerated 140 finite-field interpolation tables to check the simple-root first and second moments.
