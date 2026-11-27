# Adapted rational-prime incidence in one KeyBreak terminal box

A common pool of selected rational primes can depend on the public rational environment and the sampled field. Under the source's Dirichlet GRH and smooth-number inputs, its total incidence among verified joint proposals in a terminal box still satisfies an upper bound. Applied near the stationary sparse schedule, the bound excludes an improvement by reconciling a single widened rational band with separate uniform pivots. [Asymmetric terminal budget](keybreak-asymmetric-terminal-budget.md) · [KeyBreak, Appendix G](https://crypto.sjtu.edu.cn/factoring.pdf#page=106)

## Box and incidence bound

Use the same comparison distribution on the rational environment \((Q,r)\) and the coefficients of \(F=F_0+2G R_c\). Set \(G(X,Y)=QX-rY\). Let \(H,D\) have their [previous meanings](keybreak-asymmetric-terminal-budget.md#the-charged-terminal-box). Take a single terminal-scale box with coordinate size \(V=\exp((v+o(1))H)\), denominator prime in \((V/2,3V/4]\), and numerator \(w=r b'-Qa'\) in the usual window \([MV/16,MV/8]\). Use only primitive pairs \((a',b')\) with \(\gcd(w,N)=1\). A pair counts as algebraically valid if the absolute raw norm has exactly one prime in a prescribed incoming band above the algebraic smoothness cutoff, to exponent one, and the remaining part is smooth at that cutoff. This aggregates the labels in the band. A verified pair contributes to at most one incoming label. There is no conditioning on an incoming algebraic root.

For a dyadic rational prime band \((P,2P]\), \(P=\exp((\xi+o(1))H)\), let \(T_p\) count valid pairs with largest rational prime precisely \(p\). Write \(s_R(\xi)=1/(3\delta\xi)\), with \(d\sim\delta D\), and let \(s_A\) be the algebraic Dickman loss in this box. Put
\[
J=2v-s_R(\xi)-s_A.
\]
Suppose the algebraic value scale \(X=\sigma MV^d\) satisfies \(\log X\ge(2+\epsilon_0)\log M\) for a fixed \(\epsilon_0>0\), as it does in the terminal box at the sparse stationary parameters. For any fixed \(\epsilon>0\) and \(L_0>0\), the expected maximum over **all** pools \(S\subseteq(P,2P]\) with \(|S|\le\exp((q+o(1))H)\) satisfies
\[
\mathbb E\max_S\sum_{p\in S}T_p
\le
\exp\big((q+(J-\xi)_++\epsilon+o(1))H\big)
+
\exp\big((\xi-s_A+o(1))H\big)
+
\exp(-L_0 H).
\tag{1}
\]
Here \(x_+=\max(x,0)\). The pool may depend on both the environment and the field. The single-box assertion also bounds the union over subexponentially many separately eligible boxes and dyadic bands from a fixed menu by summing their bounds.

## Rational incidence and truncation

For a prescribed \(p\), take the fixed numerator set \(A_p\) consisting of the integers in the window with largest prime \(p\). It has size at most \(\exp((-s_R(\xi)+o(1))H)MV/P\), by counting smooth integers after division by \(p\). Let \(R_p\) count rational pairs before the algebraic test and, for this upper count, before the primitive and unit filters. The ratio-convolution proof of G.3 with modulus \(Q\) alone applies to \(A_p\). The product convolution remains independent of \(Q\). Its multiplicity is at most the number of prime divisors of the product, hence polynomial in \(\log N\), even when a prime denominator can divide an allowed numerator. Including this factor in the large-sieve energy gives
\[
\mathbb E R_p\ll\mu\exp(o(H)),\qquad
\mathbb E |R_p-L_Q|^2\le\mu\exp(o(H)),\qquad
0\le L_Q\le\mu\exp(o(H)),
\quad
\mu=\exp((2v-s_R(\xi)-\xi)H).
\]
The first estimate follows separately by averaging over the interval of \(r\), since each numerator and denominator pair determines at most one \(r\) there. For the variance, the large-sieve length is \(O(MV^2)=o(M^2)\). The principal term counts only the numerator residues that are units at \(Q\). [KeyBreak, (G.11)–(G.16)](https://crypto.sjtu.edu.cn/factoring.pdf#page=108)

Fix \(\eta>0\) and truncate above \(U=\exp(\eta H)\max(1,\mu)\). On \(R_p>U\), eventually \(R_p\le4(R_p-L_Q)^2/U\). Thus \(\mathbb E[R_p1_{R_p>U}]\le\exp((-\eta+o(1))H)\). Conditional on the rational environment, the algebraic validity probability of a primitive unit pair is at most \(\exp((-s_A+o(1))H)\), as in the one-point case below. Summing over \(p\) gives the second term of (1), with an extra negative \(\eta\) that can be dropped.

## Fixed higher moments for the algebraic test

For any fixed integer \(h\ge1\) and any \(h\) distinct primitive unit pairs in this box, the probability that all pass the band test is at most \(\exp((-hs_A+o(1))H)\). Here is the extension of the source's Gaussian and progression upper bounds to fixed \(h\).

* The integer kernel of the joint evaluation map on coefficient vectors consists of multiples of the primitive polynomial \(\prod_i(b_i'X-a_i'Y)\). Its monomial multiples form a basis with norms \(O_h(V^h)\). The terminal box has \(\sigma/V^h\) growing on the radix scale, so the Poisson argument of G.4 gives a uniform relative Gaussian image estimate with negligible error. The finite Gaussian sampler has negligible total variation error.
* For \(\Delta_{ij}=a_i'b_j'-a_j'b_i'\), the image contains independent separate periods \(m_i=2|G(P_i)|\prod_{j\ne i}|\Delta_{ij}|\) in coordinate \(i\). To see this, multiply the other \(h-1\) primitive factors by a homogeneous polynomial taking value one at \(P_i\). The latter exists by taking a power of a Bézout linear form for \((a_i',b_i')\). Hence the affine image is a union of Cartesian progression cosets with these periods. The least Gaussian semiaxis is \(X\exp(-O_h(H))\) or larger. Indeed the first \(h\) monomial columns have determinant, up to sign, \(\prod_i (b_i')^{d-h}\prod_{i<j}\Delta_{ij}\). Its nonzero integer factors and the row norm upper bounds give the semiaxis claim after multiplication by \(2\sigma|G(P_i)|\). The largest semiaxis is at most \(X\exp(o(H))\).
* For radii between \(\exp(-cH)\) and a polynomial in \(\log N\), cover a Gaussian ellipsoid with axis-aligned cubes of side \(X\exp(-C_h H)\). Taking \(C_h\) large relative to \(c\) and the shortest-axis bound keeps the outer cover's volume within a constant of the ellipsoid's volume. In every progression coset the number of points in the ellipsoid is comparable to its volume divided by \(\prod_i m_i\), by tiling with period rectangles whose side lengths are negligible compared with the shortest axis. The same comparison applies to each cube. The radius range can omit Gaussian mass \(\exp(-c' H)\) for arbitrarily large fixed \(c'\).
* In any supported progression coset, the gcd of the residue with \(m_i\) is coprime to \(2G(P_i)\) because \(F\) is projectively root-free modulo two and \(F(P_i)\) is a unit at primes of \(G(P_i)\). Thus the gcd has \(O_h(H)\) bits. Apply (G.8) and the phase-wise principal upper bound (G.35) in each cube coordinate. The latter uses B.7 and B.29 and allows a length \(X\exp(-O_h(H))\). Removing the gcd or one prescribed band prime changes the logarithmic scale by \(O_h(H)\), so the saddle correction is \(\exp(o(H))\). With smooth gcd, the band main terms sum weights \(1/\ell\). With a gcd containing a band prime there is at most one permissible term. The normalized nonprincipal error is \(\exp(-\Omega(DH))\) since \(m_i=M\exp(O_h(H))\) and \(\log X\ge(2+\epsilon_0)\log M\); summing over the band charges only \(\exp(O(H))\). Therefore each coordinate has density at most \(\exp((-s_A+o(1))H)\), uniformly in the cube and coset.

The cube cosets are Cartesian products, so their joint upper densities multiply. Sum over the cover and integrate the ellipsoids by the same layer-cake formula as G.9. Choose the outside radius losses after \(h\) and \(s_A\). This yields the asserted upper bound without a joint friable lower bound. [KeyBreak, Lemmas G.4 and G.9](https://crypto.sjtu.edu.cn/factoring.pdf#page=115)

## From moments to a common adapted pool

On \(R_p\le U\), the conditional factorial moments of \(T_p\) through order \(h\) are bounded by the corresponding powers of \(R_p\exp((-s_A+o(1))H)\). Passing to ordinary moments and summing over primes gives
\[
\sum_{P<p\le 2P}\mathbb E[T_p^h1_{R_p\le U}]
\le \exp\big((J+(h-1)((J-\xi)_++\eta)+o(1))H\big).
\]
Truncate the resulting degrees at \(\exp(((J-\xi)_++\eta+\gamma)H)\) for fixed \(\gamma>0\). Their discarded expected sum costs at most \(\exp((J-(h-1)\gamma+o(1))H)\). Choose \(\eta+\gamma<\epsilon\) and then fix \(h\) sufficiently large for the final term of (1). The retained degrees contribute at most the pool size times the cap simultaneously for every pool. This order of choices uses growing degree only to exceed a fixed moment order.

## Local consequence for delayed reconciliation

Keep the algebraic cutoff \(b\), the single-input private charge, and the uniform-request raw charge \(C\ge b+s_A+s_R(\xi)\) for the widened rational band. Assume \(\xi>b\), \(\xi-s_A<b\), and that this band must supply \(\exp((b+o(1))H)\) joint marks with probability bounded below. Equation (1) forces pool exponent \(q\ge b-(J-\xi)_+\). In particular, at the stationary box with width fixed, \(J=b+s_R(b)-s_R(\xi)<\xi\), since \(b^2>1/(3\delta)\). In that box the pool needs exponent at least \(b\).

The check also allows some retuning of the box width. If \(C<C_*\), the symmetric charged terminal constraints imply
\[
J_0=(6b/\delta-1)(C-b)-2A/\delta-(6b/\delta)s_R(b)<b.
\]
For a feasible width with \(\delta<6b\), substitute its upper bound from the widened raw charge to get
\[
J-\xi\le J_0-\xi+(6b/\delta)(s_R(b)-s_R(\xi))
< (\xi-b)\big(2/(\delta^2\xi)-1\big).
\]
An ordinary pivot for a rational incoming prime at \(\xi\) with both outputs smooth at \(b\) has loss strictly greater than
\[
C-b+\frac{\delta(\xi-b)}{6b-\delta}.
\]
This is the symmetric loss at incoming scale \(b\), plus the increase required by the mean inequality for the larger index. When \(3\delta^2 b^2\ge6b-\delta\), it exceeds the largest possible saving \(b-q\). This condition holds with strict slack at the stationary parameters. Thus the adapted pool and separate pivot searches cannot improve the local budget in this range. The argument leaves pooled elimination with nontriangular rows and adaptive online search laws outside its scope.
