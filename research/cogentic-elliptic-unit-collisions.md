# Equal unit residues at distinct elliptic arguments

Two power-order fields can evaluate their marked units to the same residue at distinct modular arguments. If the arguments come from one elliptic twist, they carry explicit square roots after division by the twist parameter. Opposite choices of local sign in that equality yield a proper gcd. For two short multiples of one seed, every such collision is already a bounded elliptic order event. [Separating power-order units](cogentic-separating-power-order-units.md)

## When two marked ratios agree

Put \(A(x)=(x-1)(x-2)\), \(C(x)=(x-13)(x-14)\), and \(W=AC\). On the smooth projective curve \(E_\delta\) defined by \(\delta y^2=W(x)\), take \(O=(1,0)\) as origin and \(T=(2,0)\). Call a point admissible when it is affine and avoids the four marks. Write
\[
  r(P)=\frac{y(P)}{C(x(P))},\qquad
  u(P)=\frac{A(x(P))}{C(x(P))}=\delta r(P)^2.
\]
These formulas apply over \(\mathbb Q\) and at good odd primes where \(\delta\) is a unit and the four marks are distinct. Over \(\mathbb Z/N\mathbb Z\) the evaluations require unit denominators and nonzero mark differences modulo every prime dividing \(N\).

The function \(r\) has simple poles at \((13,0)\) and \((14,0)\) and simple zeros at \(O\) and \(T\). Indeed, \(y\) vanishes to order one and \(x-e\) to order two at each branch mark \(e\). At infinity \(r\) has a finite nonzero value over the algebraic closure. The poles sum to \(T\) in the elliptic group, since the three nonzero two-torsion points sum to \(O\). The two points in any finite fiber of \(r\), counted with multiplicity, therefore sum to \(T\). This is the degree-two divisor description of the elliptic group law. The involution fixing \(r\) is \(P\mapsto T-P\). The quartic involution is negation, so \(r(-P)=-r(P)\). Consequently, at admissible points,
\[
\begin{aligned}
r(P)=r(Q)&\iff P-Q=O\ \text{or}\ P+Q=T,\\
r(P)=-r(Q)&\iff P+Q=O\ \text{or}\ P-Q=T,\\
u(P)=u(Q)&\iff P-Q\in\{O,T\}\ \text{or}\ P+Q\in\{O,T\}.
\end{aligned}
\]
In the last line, the characteristic is odd and \(r(P),r(Q)\) are nonzero, so the first two lines give mutually exclusive local signs. A difference or sum of the two rational roots can be tested with gcds after clearing unit denominators. In particular, when the unit values agree modulo \(N\) and the signs differ at two prime factors, both \(\gcd(r(P)-r(Q),N)\) and \(\gcd(r(P)+r(Q),N)\) are proper divisors. Here the arguments of the gcds denote any integer representatives of the modular values. Equality of the unit values over \(\mathbb Q\) forces a single rational sign and gives only the trivial gcds wherever both points are admissible.

There is also a projected form of the test. For \(s=2x-15\) put \(B(s)=s^2-24s+143\). Then \(4C(x)=B(s)\) and \(4A(x)=B(s)+48s\). With \(s_P=2x(P)-15\) and \(s_Q=2x(Q)-15\),
\[
  u(P)-u(Q)=\frac{48(s_Q-s_P)(s_Ps_Q-143)}{B(s_P)B(s_Q)}.
\]
At the good primes, an equal unit value thus forces equal arguments or companion arguments with \(s_Ps_Q=143\). Different projected branches can give a gcd directly. When both reductions lie on the companion branch, they can still give opposite signs for \(r\).

## What the short orbit can supply

Suppose \(P=[n]P_0\) and \(Q=[m]P_0\) for distinct positive integers \(n,m\). At every admissible prime where \(u(P)=u(Q)\), the order of the reduced seed divides \(2(n-m)\) or \(2(n+m)\). This follows by doubling one of the four group identities above. For the amplified menu with \(S\le n,m\le 8S\), the order at a collision prime is at most \(32S\). Checked modular elliptic arithmetic can test the exact identities using the sums and differences of the indices and the known point \(T\), without generating either defining field. Thus pairwise equality of units from one short orbit gives a bounded elliptic order criterion in the same twist. The group identities also apply to independently chosen points on that twist.

The same local squareclass for all these unit values leaves the algebraic squareclasses independent in pairwise coprime odd-degree charts. To see this, let \(K_i\) be their fields, \(d_i=[K_i:\mathbb Q]\), and \(U_i=A(\theta_i)/C(\theta_i)\) in each power order. Each unit has norm \(+1\): for odd degree, \(N_{K_i/\mathbb Q}(\theta_i-e)=W'(e)\) at a mark \(e\), and the product of derivatives in each block is the same. Each \(U_i\) takes both signs under real embeddings, since \(F=WG-W'\) changes sign between consecutive marks and the ratio has different signs on the first and second intervening intervals.

The degree of the compositum \(L\) is at most \(\prod_i d_i\) and is divisible by each \(d_i\). Pairwise coprimality forces equality, so the relative norm from \(L\) to \(K_i\) sends \(U_j\) to \(1\) for \(j\ne i\) and \(U_i\) to \(U_i^{[L:K_i]}\). If a nonempty product of distinct \(U_i\) were square in \(L\), taking this norm at an included index would make an odd power of \(U_i\) square in \(K_i\), contradicting its negative real value. This addresses joint square extraction for products of the marked units. The collision test instead compares explicit rational functions on a single twist.

## A finite example

Take \(N=3383=17\cdot199\), \(\delta=364\), \(P=(15,1)\), and \(Q=[8]P\). The following are reductions of the two rational points and their root functions.

| Prime | \(x(P)\) | \(r(P)\) | \(x(Q)\) | \(r(Q)\) |
|---:|---:|---:|---:|---:|
| 17 | 15 | 9 | 10 | 9 |
| 199 | 15 | 100 | 198 | 99 |

For direct computation, put \(c_0=-156\) and use \(X=\delta c_0/(x-1)\), \(Y=\delta^2c_0y/(x-1)^2\). This gives \(Y^2=(X-\delta c_0)(X+13\delta)(X+12\delta)\). Starting with \(X=\delta c_0/14,\ Y=\delta^2c_0/14^2\), three doublings give \(Q\) and the table follows by reversing the change of variables. The seed has order six at 17 and fourteen at 199. At 17, \([9]P=T\). At 199, \([7]P=T\). Thus \(r(P)\) and \(r(Q)\) agree at 17 and are negatives at 199.

The arguments modulo \(N\) are 15 and 1591, distinct even after reduction at either prime. Both pairs of arguments lie on the projected companion branch. Both unit values reduce to 91, and the two roots reduce to 1692 and 298. Their difference has gcd 17 with \(N\), and their sum has gcd 199.

To realize the example in coprime-degree power orders take \(F_i=WG_i-W'\) with
\[
  G_1=X^3+175X^2+75X+180,\qquad
  G_2=X^7+X^3+32330.
\]
Both defining polynomials are Eisenstein at 5. Their respective modular roots are 15 and 1591, and the derivatives there are 3056 and 1417 modulo \(N\), both units. Thus the two reductions to 91 are evaluations of actual marked units in distinct fields of degrees seven and eleven. The twist parameter is nonsquare at 17 and square at 199, and the common residue has orders 16 and 99 at those primes.
