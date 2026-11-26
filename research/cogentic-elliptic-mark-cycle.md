# An elliptic family for the fixed four-mark split

The fixed [four-mark square cycle](cogentic-square-mark-cycle.md) gives infinitely many distinct odd moduli after removal of the original seed factors. Each admits two coprime factors whose ratio approaches one. The moduli can avoid every prescribed finite set of primes. A deterministic input-only search finds the split in polynomial bit time on this family. The construction uses one fixed elliptic curve and does not assert a supply of certificates on arbitrary inputs.

## A point of infinite order

Put
\[
 A(X)=(X-51)(X-95),\qquad
 B(X)=(X-57)(X-85),\qquad
 F(X)=X+A(X)B(X)(A(X)-1).
\]
The fixed sextic is irreducible modulo 13. With \(S=1-2A\) one has \(A-BS^2=-4F\), so in the field of \(F\) the product \(AB\) is the square of \(BS\).

The quartic \(y^2=A(m)B(m)\) contains \((50,105)\). Set \(a=-8976=-44\cdot6\cdot34\). The change
\[
 X=\frac a{m-51},\qquad Y=\frac{ay}{(m-51)^2}
\]
gives
\[
 E\colon Y^2=X^3+1964X^2+753984X+80568576.
\]
Indeed the intermediate cubic in \(1/(m-51)\) is the product of the three factors with slopes \(-44,-6,-34\). The seed gives \(P=(8976,-942480)\), and the inverse chart is \(m=51+a/X\), \(y=aY/X^2\).

The model has good reduction at 23 and 29. Modulo 23, \(8P=(12,0)\) and \(16P=O\), so the reduced order is 16. Modulo 29, \(18P=O\). Reduction at a good prime is injective on torsion of order coprime to that prime. In particular the order of the 2-primary component of a rational torsion point would be the same in both reductions. These orders rule out torsion for \(P\).

## Recurrence at finitely many places

For any finite prime set, take the product of \(E(\mathbb R)\) and the groups \(E(\mathbb Q_p)\) over that set. These are compact topological groups, including at bad reduction, since the elliptic curve is projective. Choose an increasing sequence of multiples \(n_jP\) converging in this product. Then \((1+n_{2j}-n_j)P\) converges to \(P\) simultaneously at the chosen places, and the multipliers tend to infinity. The inverse chart is continuous near \(P\) at every place. Thus infinitely many distinct rational pairs \((m,y)\) on the quartic approach \((50,105)\) simultaneously. The coordinate \(m\) alone takes infinitely many values, since the quartic has at most two values of \(y\) over it.

Write \(m=u/b\) in lowest terms with \(b>0\), and put \(A_h=b^2 A(m)\), \(B_h=b^2 B(m)\), \(S_h=b^2-2A_h\), \(F_h=b^6F(m)\), and \(w=b^2y\). The integer \(A_hB_h\) is a rational square, so \(w\) is an integer. The sextic is monic, hence \(F_h\) is coprime to \(b\).

Include all primes dividing \(2\cdot3\cdot5\cdot17\cdot19\cdot31\cdot313\) among the recurrence places. For sufficiently close points, \(b\) is a unit at each chosen prime and the valuation of \(F_h\) there equals that of \(F(50)=485150=50\cdot31\cdot313\). Thus
\[
 N=F_h/485150
\]
is an integer coprime to all the chosen primes. Additional primes in any fixed finite set are covered by the same choice. In the real neighborhood \(F(m)>0\) and \(F(m)\to F(50)\), so \(N/b^6\to1\). Bounded real \(m\) and infinitely many distinct rationals force unbounded denominators. One can choose a diagonal sequence with \(N\) strictly increasing and smallest prime factor tending to infinity. This does not give a power-law lower bound on that smallest factor.

## The two balanced factors

Any prime common to \(A_h\) and \(B_h\) divides the fixed cross-resultant of \(A,B\), since a prime dividing \(b\) cannot divide either form. The possible primes are \(2,3,5,17,19\). At those primes the local valuations are those of \(A(50)=45\) and \(B(50)=245\). At every other prime their product is a square and they cannot both vanish. Therefore \(A_h=5v^2\), \(B_h=5z^2\) with positive integers \(v,z\), and \(w=5vz\) on the positive real branch. The exact identity is
\[
 D_+D_-=4F_h/5,qquad D_+=-zS_h+v b^2,qquad D_-=-zS_h-v b^2.
\]

At any selected prime, \(v/b\) is near one of \(3,-3\) and \(z/b\) is near one of \(7,-7\). This follows from their squared values tending to 9 and 49, respectively, with the neighborhoods of the two roots taken disjoint. Their product tends to \(y/5=21\), so the two local signs agree when the neighborhood is small enough. Hence the possible common sign reversal negates both expressions \(D_+/b^3,D_-/b^3\) and preserves their separate valuations. Those valuations are the valuations of the seed values 626 and 620, respectively. Since \(626\cdot620=4F(50)/5\), the two positive integers
\[
 P_+=D_+/626,\qquad P_-=D_-/620
\]
multiply to \(N\). In the real limit \(v/b\to3\), \(z/b\to7\), and \(S(m)\to-89\), giving \(P_+/b^3\to1\) and \(P_-/b^3\to1\).

If a prime dividing \(N\) also divides \(A_h\) or \(B_h\), the identity for \(F_h\) forces \(u\equiv0\) at that prime. It would then divide \(A(0)=B(0)=4845\), whose prime factors have already been excluded. Thus \(v,z,w\) are units modulo \(N\). A prime common to the two displayed factors would divide \(D_+-D_-=2v b^2\), also a unit. This proves coprimality and shows that the normalized square root
\[
 R=\frac{B_hS_h}{w b^2}\pmod N
\]
has sign \(+1\) on \(P_+\) and \(-1\) on \(P_-\): its two comparison numerators are \(-5zD_+\) and \(-5zD_-\). All denominators are units. The modular gcds recover the two factors, including their whole prime powers. The same factors are already explicit in the elliptic parameters.

## Recovering a parameter from the integer

Use the logarithmic coordinate height \(h(X)\) and normalize the Néron–Tate height \(\widehat h_x\) so that \(h(X(Q))=\widehat h_x(Q)+O_E(1)\). It satisfies \(\widehat h_x(nP)=n^2\widehat h_x(P)\) and \(\widehat h_x(P)>0\) for the nontorsion seed. A fixed invertible rational fractional-linear change alters coordinate height by at most a constant, so \(h(m(nP))=n^2\widehat h_x(P)+O(1)\). On the recurrence family \(m\) lies in a fixed bounded real interval and \(F(m)\) is bounded above and away from zero. Consequently
\[
 \log N=6\log b+O(1)=6n^2\widehat h_x(P)+O(1).
\]
This normalization of \(\widehat h_x\) is twice the convention that compares it to half the coordinate height. [Silverman, Canonical Heights, p. 69](https://www.math.brown.edu/johsilve/Wyoming/WyomingEllipticCurveJune7.pdf#page=80) · [Silverman, explicit bound on the height difference](https://doi.org/10.1090/S0025-5718-1990-1035944-5)

Given only a public integer \(N\), try successive \(nP\) up to the binary bit length of \(N\), skipping undefined charts. Check \(F_h=485150N\), the unit denominators, the square comparison and a proper gcd. If several trials succeed, keep the split with the closest factors. For all sufficiently large members of the recurrence family one of these indices works since \(n=O(\sqrt{\log N})\). During the full search coordinates have \(O((\log N)^2)\) bits by the same height bound, and the group law and all checks use polynomial bit time. The search can report no certificate on other inputs.

As a separate exact check, \(2P=(16120/9,-3134528/27)\) maps to \(m=92667/2015\), \(y=1318852656/4060225\). Its sextic numerator is \(1727544298509508124101286949\). Removing 51 gives \(33873417617833492629436999\), and the normalized ratio \(7774315739127991393880527\) gives the coprime factors \(5829071504407\) and \(5811117189457\). This particular point illustrates the field and modular identities without using the recurrence neighborhoods.
