# Small defining polynomials with a separating unit in the power order

Assume Dirichlet RH. For any two distinct odd prime factors \(p,q\) of an input \(N\), a deterministic public menu either finds a proper divisor or contains two monic irreducible polynomials with the following properties. They have coprime degrees of order \((\log N/\log\log N)^{1/3}\), coefficient logarithmic heights \(O(V)\) with \(V=(\log N)^{2/3}(\log\log N)^{1/3}\), and a common simple root modulo \(N\). In each power order one explicit infinite-order unit reduces to the same residue modulo \(N\). That residue has different two-primary order heights at \(p,q\). Both fields use the same four fixed linear marks. The menu can be constructed in polynomial bit time with a sufficiently large fixed exponent in the short-character estimate. The proof targets a chosen pair of primes; the algorithm enumerates the same menu for every input of a given size, apart from the modular arithmetic and gcd checks. [Fixed linear-forms estimate](cogentic-cm-linear-forms.md) · [Paired-block units](cogentic-paired-block-unit.md)

## Keeping the two signs as the rational argument grows

Use \(A=(X-1)(X-2)\), \(C=(X-13)(X-14)\), and \(W=AC\). Choose a nonsquare sign at the prime with larger \(v_2(r-1)\), breaking ties arbitrarily, and a square sign at the other. A nonsquare in \(\mathbb F_r^\times\) has maximal two-primary height, whereas a square has height at most \(v_2(r-1)-1\). The desired residue is \(A(x)/C(x)=W(x)/C(x)^2\). Thus it suffices to prescribe the signs of \(W(x)\).

Apply the short linear-forms estimate to \(v,u-v,u-2v,u-13v,u-14v\) in a fixed positive box with \(u>14v\) and all forms in \([1,T]\). The denominator \(v^4\) is a square. Prescribe the two signs of each form so their product has the desired signs at the primes. Trial division through a fixed multiple of \(T\) catches the small primes. The theorem gives \(\gg T^2\) integer pairs for these signs with \(T=(\log N)^{C_0}\) for some fixed \(C_0\). Among pairs \(1\le u,v\le T\), fractions of reduced height at most \(\sqrt T\) account for \(O(T^{3/2})\) pairs: at reduced height \(m\) there are \(O(m)\) fractions and each has at most \(T/m\) representatives. Hence one good seed \(t=u/v\) has \(\log H(t)\asymp\log T\), where \(H\) is the maximum of the absolute reduced numerator and denominator. [Uniformity and the two available cutoffs](cogentic-cm-linear-forms.md#uniform-colors-of-short-linear-forms)

Put \(\delta=W(t)\). On the smooth projective genus-one curve \(\delta y^2=W(x)\), use the branch point \((1,0)\) as origin and \(P=(t,1)\) as seed. For \(c_0=-156\) the change of variables
\[
 X=\frac{\delta c_0}{x-1},\qquad Y=\frac{\delta^2 c_0y}{(x-1)^2}
\]
gives the monic cubic with roots \(-\delta c_0/(1-e)\) for \(e=2,13,14\). Over \(\mathbb Q(\sqrt{\delta})\) the twist identifies with the single fixed cubic for \(\delta=1\); its fixed-cubic abscissa is \(c_0/(x-1)\). The height difference for this fixed elliptic curve and this fixed fractional linear change is bounded independently of the seed. Writing \(x_n=x([n]P)\) gives
\[
       \log H(t)=2\widehat h(P)+O(1),\qquad
       \log H(x_n)=2n^2\widehat h(P)+O(1).
\]
The growing-height seed above is nontorsion. For the three primes selected in successive dyadic intervals starting at \(\lceil\sqrt{V/\log H(t)}\rceil\), all three arguments have logarithmic height \(\asymp V\). The bounds suffice with any fixed base for logarithms. Exact rational scalar multiplication up to these indices uses polynomially many bits. [Silverman's canonical-height comparison](https://doi.org/10.1090/S0025-5718-1990-1035944-5)

At both hidden primes the seed is affine and away from the branch points. Its local order \(o\) exceeds two. Since the branch points are exactly the two-torsion, a prime index \(n\) hits a branch point only if \(o/\gcd(o,2)\mid n\). A given prime of reduction therefore excludes at most one of the three indices. At the place where \(\delta\) is nonsquare, the quartic has no rational point at infinity, since its leading coefficient is one. Thus a denominator nonunit for a remaining index gives a proper gcd, even if the other prime sees infinity. Gcd-test the denominator and each of the four mark differences separately. A mark obstruction at just some primes also yields a divisor. Otherwise a surviving index gives an admissible \(x_n=a/b\) with the desired opposite signs, because \(W(x_n)=\delta y_n^2\). Inputs below the fixed asymptotic threshold can be handled by direct division.

## Repairing two monic fields at the same argument

Take \(b>0,\ \gcd(a,b)=1\), and \(H_m=\max(|a|,b)\). Choose the least \(d\ge7,\ d\equiv3\bmod4\) with \(H_m^d\ge N\), and also use \(d+4\). For the good argument \(d\asymp \log N/V\). These two degrees are coprime, so the resulting fields are linearly disjoint over \(\mathbb Q\).

For each degree construct \(F=WG-W'\). Since \(W\bmod5=X^4-1\), take \(G_0=X^3+X^7+\cdots+X^{d-4}\), with a constant adjustment by 5 to give \(v_5(F_0(0))=1\). This yields \(F_0\equiv X^d\bmod5\). Write \(G=G_0+25R\) with \(k=\deg G_0=d-4\) and \(\deg R\le k-1\). For \(W_h=b^4W(a/b)\) and \(F_{0,h}=b^dF_0(a/b)\), solve
\[
   \sum_{i=0}^{k-1}r_i a^i b^{k-1-i}
                 \equiv -F_{0,h}(25bW_h)^{-1}\pmod N.
\]
All inverses exist after the gcd checks. To represent the least absolute residue on the right, peel a centered digit modulo \(|a|\) from the constant end when \(|a|\ge b\), or modulo \(b\) from the high end otherwise. At each step the coefficient of that digit is invertible modulo the larger base. Subtract its contribution and divide by the larger signed base. All peeled coefficients have magnitude at most \(H_m/2\), and the final one is bounded by \(N/(2H_m^{k-1})+(k-1)H_m/2\le (H_m^5+kH_m)/2\). This gives the required \(O(V)\) coefficient log height and \(F(a/b)\equiv0\bmod N\). If the root derivative has a proper gcd, return it. If the derivative is zero modulo \(N\), add \(25(bX-a)\) to \(G\); this leaves its value fixed and changes the derivative of \(F\) by the unit \(25bW(a/b)\). Eisenstein at 5 holds throughout. [Homogeneous digit construction](../experiments/cogentic-projective-unit-chart.py)

At \(\theta\), the relation \(ACG=A'C+AC'\) gives \((A/C)C'=AG-A'\). The identity \(C'^2-4C=1\) therefore gives \(A/C=C'(AG-A')-4A\) in \(\mathbb Z[\theta]\). Swapping \(A,C\) gives its inverse there too. Interlacing at the four fixed marks gives positive and negative real values of the unit, so it has infinite order. In both fields its reduction is the same \(A(a/b)/C(a/b)\) with the prescribed pair of local signs. [Explicit inverse identities](cogentic-quintic-unit-target-two.md)

Every mark has norm of absolute value \(|W'(e)|\), namely \(156,132,132,156\) in increasing order. Giving a suitable odd multiple of the order of the reduced unit at one prime now suffices to split using gcds along the doubling chain. These fields provide the separating unit and its inverse in the power order. They do not supply such an order multiple for every input. In particular, using only a smooth multiplier recovers the familiar smooth \(p-1\) condition on the multiplicative group.


## Executable menu

The generator doubles the seed until its argument reaches the requested bit height at index \(S\), then scans all indices from \(S\) through \(8S\). This interval contains primes in three successive dyadic intervals for large \(S\), and the canonical-height comparison gives the required height scale on the good seed. The option `--partner` constructs both field degrees. On the small fixture below the first smooth-order test misses and the second finds 83, a factor of 2573. [Generator and replay](../experiments/cogentic-elliptic-unit-arguments.py)

```sh
python3 -B experiments/cogentic-elliptic-unit-arguments.py 2573 --seed-height 15 --degree 7 --height-bits 10 --smooth-bound 3
```
