# A fixed linear factor in the KeyBreak coefficient perturbation

Consider the modified affine field law
\[
 F=F_0+2G L^mS,\qquad G=QX-rY,\quad L=X-\xi Y,\quad \deg S=d-1-m,
\]
with fixed integer \(\xi\), \(m/d\to\rho\), and ordinary isotropic coefficient width \(\sigma\) for \(S\). This preserves \(F(r,Q)=N\) and the mod-two irreducibility of \(F_0\). A terminal strip favors \(\rho>1/2\), whereas the pinned one-point progression comparison cannot reach \(\rho>1/2\) on ordinary top marks. This is an obstruction to that combination of field law, proposal geometry and analytic estimate. [KeyBreak, (G.8), Lemma G.4 and (G.28)](https://crypto.sjtu.edu.cn/factoring.pdf#page=106)

## Terminal strip budget

Write \(d\sim\delta D\), \(H=D\log\log N\), and take marks with \(|b|\) of order \(\exp(vH)\) and \(|L(a,b)|\) of order \(\exp(wH)\), \(0\le w\le v\). The raw box volume exponent is \(v+w\), since \((a,b)\mapsto(L(a,b),b)\) is unimodular. The random part of the algebraic value has coordinate-height charge on the \(DH\) scale
\[
 \delta\big[(1-\rho)v+\rho w\big]
    = \frac{\delta}{2}(v+w)+\delta(1/2-\rho)(v-w).
\]
The fixed part can require more height. With the ordinary Gaussian law the directional scale in this formula is also a lower leading height in probability, irrespective of the shift \(F_0(a,b)\). Condition on all coefficients of \(S\) except the coefficient of \(Y^{d-1-m}\). The resulting scalar discrete Gaussian progression has step \(2|G(a,b)L(a,b)^m b^{d-1-m}|\) and parameter \(\sigma\) in its integer coordinate. Any interval of scale \(\exp(-\epsilon DH)\) times its Gaussian width has probability \(O(\exp(-\epsilon DH)+1/\sigma)\). This applies where \(G,L,b\) are nonzero. It controls norm height, without making any assertion about the smooth subset.

Thus when \(\rho\le1/2\), the change does not lower the ordinary coordinate-height charge at a fixed proposal volume. This comparison keeps the coefficient-width charge and the other entries of the single-input ledger fixed. A smaller coefficient width, a different proposal law, or a different smoothness estimate is a separate change. A fixed integer \(\xi\) also does not lower the ordinary terminal rational scale: \(G=Q L+(\xi Q-r)b\), and the original environment has \(\log Q\sim DH/\delta\) while terminal coordinates have logarithms \(O(H)\). An exceptional cancellation between the two terms is not a general radix saving.

## What the pinned progression error permits at the top

For a primitive top mark \(P=(a,b)\) with \(L(P)\ne0\), evaluation of \(S\) is onto \(\mathbb Z\) by powering a Bézout form. Its raw affine progression has exact step
\[
 M_P=2|G(P)|\,|L(P)|^m.
\]
In a top region with \(|a|,|b|\ll V\), the random window, including the source's polynomial tail padding, has length at most
\[
 W_P=M_P\,\sigma (CV)^{d-1-m}\operatorname{poly}(\log N)
\]
for a fixed constant \(C\). Use the top scale \(\log V\asymp\log M\), where \(M\) is the source's radix scale, and \(\log\sigma=O(\log M)\). Then
\[
 \log(W_P/M_P)\le (1-\rho+o(1))d\log V.
\]
This ratio is unchanged by dividing the progression and window by a common divisor. It also does not get larger when the step increases under further coefficient root congruences.

The error in (G.8) on an interval with global magnitude \(X_*\) and modulus \(M_P\) is \(O_\epsilon(X_*^{1/2+\epsilon}M_P^\epsilon)\). The one-point proof of (G.28) needs this error small against the main count in a window, which is at most of order \(W_P/M_P\) up to endpoint effects and before the smoothness charge. The source's original center is small compared to its random width. In the modified law, the true endpoint must account for the fixed center even if the perturbation is much shorter. In particular, if
\[
 |F_0(P)|\ge V^{d-o(d)}
 \quad\text{and}\quad
 \log D_P=o(d\log V),\qquad D_P=\gcd(F_0(P),M_P),
\]
then the divided endpoint still has logarithm at least \((1-o(1))d\log V\). Removing one more prescribed top prime with logarithm \(O(\log V)\) does not affect this leading comparison. Even dropping the smoothness loss and the positive \(\epsilon\) factors, the square-root error allowance is too large for this proof when \(\rho>1/2\). At \(\rho=1/2\) the leading comparison alone gives no margin. The statement is about what the specific error bound can certify, not a lower bound for the actual error in a progression. [KeyBreak, (G.28) and the separate-period budget, pp. 112 and 125](https://crypto.sjtu.edu.cn/factoring.pdf#page=112)

## Center and content in a skewed top box

The center need not be postulated large only on ordinary, unskewed slopes. Let \(b\asymp V\) and let \(L(P)\) range over an interval of length and magnitude \(O(U)\), \(1\le U\le V\), in the strip around \(\xi\). Set \(f(t)=F_0(\xi+(U/V)t,1)\). The source's irreducible mod-two \(F_0\) has \(F_0(\xi,1)\) odd, so \(|f(0)|\ge1\). This rules out multiplying the fixed center by \(L^m\), even if the strip omits the slope \(\xi\) itself.

On a bounded \(t\)-interval, the sublevel set \(|f(t)|\le V^{-\epsilon d}\) has measure \(O(d V^{-\epsilon})\) for every fixed \(\epsilon>0\). In a set of measure \(\tau>0\), choose \(d+1\) points separated by \(\gg\tau/d\) and evaluate the Lagrange interpolation at zero. The upper bound on \(|f(0)|\) is \(V^{-\epsilon d}(C d/\tau)^d\) up to a harmless factor absorbed into \(C\). This gives the stated measure bound. Since a polynomial sublevel set has at most \(O(d)\) components, on the \(a\)-grid for fixed \(b\asymp V\) the exceptional fraction in an interval of length \(\asymp U\) is \(O(dV^{-\epsilon}+d/U)\). Thus when \(U\gg d\), almost all raw strip marks have fixed-center height at least \(V^{(1-\epsilon-o(1))d}\). The same conclusion holds for any retained population known to avoid concentration on these short slope intervals. The original source's ordinary slope range does not contain an integer \(\xi\), so using a new top box around such a slope would itself require a rational-side analysis.

There is also control of the progression content on the raw strip. On a primitive unit mark, \(F_0(P)\) is a unit at primes of \(2G(P)\): modulo two this follows from irreducibility, and at odd primes of \(G(P)\) the mark is proportional to \((r,Q)\), whose value is \(N\). If \(Q\) is prime as in the source and \(b<Q\), then \(Q\nmid G(P)\). For \(C_0=F_0(\xi,1)\ne0\), the polynomial identity \(F_0(a,b)\equiv b^d C_0\bmod L(P)\) and \(\gcd(b,L(P))=1\) give
\[
 D_P\le \gcd(L(P),C_0)^m .
\]
For integers \(L(P)\ne0\) uniformly in an interval of length \(\asymp U\), counting multiples of each prime power dividing \(C_0\) yields
\[
 \mathbb E\log\gcd(L(P),C_0)
 \ll \sum_{p\mid C_0}\frac{\log p}{p-1}+\frac{\log(2|C_0|)}{U}
 \ll \log\log(3|C_0|)+\frac{\log(2|C_0|)}{U}.
\]
The last bound splits primes at \((\log(3|C_0|))^2\) and uses the prime harmonic bound below that point. The source coefficient bound gives \(\log(2|C_0|)=O(\log M+d+\log d)\). The average is \(o(\log V)\) for \(U\to\infty\). At fixed prime denominators \(b\asymp V\), the primitive restriction removes only \(O(1)\) values of \(a\) per interval. Thus a large content is exceptional in the raw strip before the source's rational and algebraic filters. This does not give a content or center estimate after conditioning on those filters.

For \(\rho>1/2\), a surviving use of the same square-root-scale error would need a genuine change, such as concentrating on a usable set where the reduced center is smaller by \(V^{(2\rho-1-o(1))d}\), or giving the perturbation a longer coefficient window. Raising \(\sigma\) by that leading radix-order amount would itself cost logarithmic coefficient width \(\Theta(d\log V)\), outside the ordinary terminal field-height scale. A different analytic bound for the shifted progressions could also change the comparison. The raw-strip estimates above identify the exceptional strata a replacement supply theorem would have to address.
