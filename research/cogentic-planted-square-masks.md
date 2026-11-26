# Two guaranteed global square masks at a Pell center

For every odd input \(N\ge9\), polynomial-time arithmetic either finds a proper divisor or produces two distinct monic fields of scheduled degree scale with a common simple root modulo \(N\). In both fields the primitive marks \((0,1)\) and \((1,2)\) have norms 4 and 1, respectively. Each mark is a square with the common negative sign. The two signed masks are independent and span the square space on these two marks and the sign. They give identical canonical roots on reduction, so their difference gcds are trivial. [Exact replay](../experiments/cogentic-planted-square-masks.py) · [Planted norm-two construction](cogentic-planted-norm-two.md) · [Pell pairs with productive roots on promised inputs](cogentic-growing-pell-pair.md)

## A common argument with two known squares

Put \(L=\log N\), \(d\asymp(L/\log L)^{1/3}\) and \(V=L^{2/3}(\log L)^{1/3}\). Starting from \((Y,U)=(1,1)\), iterate
\[
 (Y,U)\longmapsto(3Y+4U,2Y+3U).
\]
The pairs satisfy \(Y^2-2U^2=-1\), with \(Y,U\) odd. Stop at a public threshold with logarithm comparable to \(L/(2d)\), and at least 2. Each step grows \(U\) by a factor between 3 and 6. The replay uses threshold \(2^{\max(1,\lfloor(\operatorname{bitlength}(N)-1)/(2d)\rfloor)}\). Thus \(\log U\asymp V\) asymptotically. All of \(U-1,U,U+1,Y\) lie strictly between 1 and \(N\) for this threshold and \(N\ge9\). Indeed, when \(N\) has four to six bits the stopping pair is \((7,5)\). For larger bit lengths \(B\), either this pair still suffices or \(Y<\sqrt2\,U<6\sqrt2\,2^{(B-1)/4}<N\) and \(U+1<N\). Check the four gcds with \(N\) and return any nonunit gcd as a divisor.

Use the common argument \(m=U^2\). Negative signs on the two marks give the evaluations \(U^2\) and \(2U^2-1=Y^2\), both units. The task is to make the same two identities hold inside each field while keeping both norms small.

## Two roots in each field

Fix an odd \(k\) with \(U^{k-4}\ge N\) and \(k\ge7\). Let \(R(X)=2X^2-1\). Pick an integer polynomial \(B(X)\) by writing the least nonnegative representative of
\[
 B(U)\equiv
 \frac{(Y-U^k)/Y^2+1}{2U(U-1)}\pmod N
\]
in base \(U\). Its degree is at most \(k-5\). For \(s=0,1,2,3\) set
\[
\begin{aligned}
 A_s(X)&=-1+2X(X-1)\bigl(B(X)+s(X-U)\bigr),\\
 Q_s(X)&=X^k+R(X)A_s(X),\qquad
 H_s(X)=Q_s(X)^2-R(X).
\end{aligned}
\]
The size condition on \(k\) makes \(Q_s\) monic of degree \(k\). It has \(Q_s(0)=1\), \(Q_s(1)=0\) and reduction \(X^k+1\) modulo 2. Thus \(H_s\) is monic Eisenstein at 2 with constant 2 and degree \(2k\). It has a real root between 0 and 1 because its value at 1 is \(-1\). Also \(Q_s(U)\equiv Y\) and \(H_s(U)\equiv0\pmod N\).

Let \(\beta\) be a root of \(H_s\) and set \(\alpha=\beta^2\). Write \(H_s(X)=E(X^2)+X O(X^2)\). The odd part is nonzero because the even part of \(Q_s\) contains its constant and the odd part contains its leading term. If \(O(\alpha)\) vanished, then \(-\beta\) would also satisfy \(H_s\). The monic irreducible polynomial \(H_s\) would equal \(H_s(-X)\), a contradiction. Therefore \(\beta=-E(\alpha)/O(\alpha)\), and the monic minimal polynomial of \(\alpha\) is
\[
 P_s(T)=E(T)^2-T O(T)^2.
\]
Indeed \(P_s(\alpha)=0\) and it has degree \(2k=[\mathbb Q(\beta):\mathbb Q]\). Choose two distinct permitted odd values of \(k\) to obtain the two fields.

The square identities are
\[
 -(-\alpha)=\beta^2,\qquad -(1-2\alpha)=Q_s(\beta)^2.
\]
The norm of the first unsigned mark is \(P_s(0)=4\). At \(x=\pm1/\sqrt2\) the value \(R(x)\) vanishes, so \(H_s(x)=x^{2k}\). Hence \(P_s(1/2)=2^{-2k}\) and the second unsigned mark has norm \(2^{2k}P_s(1/2)=1\). The signs of these norms agree with the unsigned norms because the field degree is even.

## Repairing the common residue branch

As \(s\) varies, each of \(Q_s(-U)-Y\) and \(Q_s(-U)+Y\) has increment \(-4U^2(U+1)Y^2\) modulo \(N\), and \(H_s'(U)\) has increment \(4U(U-1)Y^3\). All three increments are units by the initial gcd checks. For each of the four shifts test the three gcds. A proper gcd gives a divisor. Each affine expression can give the full gcd on at most one shift, since the four shifts are distinct modulo \(N\). Thus if no divisor has appeared, there is a shift with all three gcds one. Then \(H_s(-U)\) and \(H_s'(U)\) are units, and differentiating \(P_s(X^2)=H_s(X)H_s(-X)\) gives
\[
 2U P_s'(m)\equiv H_s'(U)H_s(-U)\pmod N.
\]
Consequently the common root of \(P_s\) at \(m\) is simple and extends to reduction of algebraic integers. The explicit roots also have unit power-basis denominators since \(H_s(-U)\equiv-2U O(m)\pmod N\). They reduce to \(U\) and \(Y\). [Integral reduction at a simple common root](cogentic-monic-index.md)

## Square dimension and limits

The sign vectors are \((1,0;1)\) and \((0,1;1)\) in the two mark coordinates and the negative-sign coordinate. Since each field has a real embedding, \(-1\) is nonsquare there. Thus these two vectors span the entire signed square space on the planted points. For a word with exponents \(e_0,e_1\), the canonical square root reduces to \(U^{e_0}Y^{e_1}\) in either field, including negative exponents at these unit marks. Any other root differs by the global sign, giving difference gcd 1 or \(N\) when the two words have the same exponents. In a mixed relation with even total incidence in each mark, the product of the canonical roots has value \(U^{2k_0}Y^{2k_1}\) when the total incidence is \((2k_0,2k_1)\). Normalizing by \((-U^2)^{k_0}(-Y^2)^{k_1}\) again gives a global sign.

There is a rank limit for schemes based on preassigning exact rational square values at an unbounded integer argument with a fixed finite list of distinct primitive marks. A three-dimensional subspace of supported mark masks contains a vector nonzero in at least three coordinates, by taking three pivot coordinates. Its signed product evaluates a squarefree polynomial of degree at least three. It can be an exact rational square at only finitely many integers, since it is integral there and Siegel's theorem applies to the corresponding hyperelliptic curve. There are finitely many signed words in the fixed list. Thus this method can guarantee at most two independent mark masks for all sufficiently large arguments on that list. The restriction concerns exact rational squares of fixed mark products. Congruence squares and changing mark lists are outside it. [Hyperelliptic integral-point finiteness](https://arxiv.org/abs/2109.14328)

Take the least allowed odd \(k\) and the next odd degree. They give \(2k=\Theta(d)\). The radix coefficients and shifts bound the height of \(Q_s\) by \(O(U)\), and squaring and forming \(P_s\) keeps logarithmic height \(O(V)\). For grid height \(A\le\exp(O(W))\), with \(W=L^{1/3}(\log L)^{2/3}\), the homogeneous norms are at most \(\exp(O(V))\), since \(dW=\Theta(V)\). The recurrence, radix lift, gcd tests and polynomial arithmetic take polynomial bit time. The replay verifies the unit derivatives, exact norms, and common roots for 85 constructed pairs and checks 114 direct gcd outcomes. Both fields are constructed on the 14,112-bit fixture, with degrees 50 and 54.
