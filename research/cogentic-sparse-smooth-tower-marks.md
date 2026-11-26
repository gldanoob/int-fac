# Sparse smooth marks in high-height tower fields

For every large composite input, a polynomial-time construction either finds a proper gcd in its preliminary checks or gives a primitive irreducible polynomial with a simple root modulo the input. One version plants a growing number of linear marks with the same sizeable squarefree smooth resultant. Its field has quadratic steps below one relative extension of freely chosen degree. A second version has a complete quadratic tower and logarithmically many cyclotomic marks. The coefficients have log height on the scale of \(\log N\), even though the complex conjugates stay small. [Low-height tower obstruction](cogentic-full-tower-height-scarcity.md)

## Planting linear marks

Let \(N\) be odd, take \(e\ge1\), \(f=2^r\), and put \(d=ef\). Set \(Q(X)=\prod_{i=1}^e(X-i)\) and \(m=e+1\). Choose an odd smooth \(S>1\), with its prime factors supplied. Check that \(S,Q(m),Q'(m)\) are units modulo \(N\). For the intended \(d=O((\log N/\log\log N)^{1/3})\), both \(Q(m)\) and \(Q'(m)\) are positive and at most \(\exp(O(e\log(2+e)))<N\), so a nonunit yields a proper gcd. Each prime used to build \(S\) can be checked separately. For instance, take \(S\) squarefree from the primes in \((V/2,V]\), where \(V=(\log N)^{2/3}(\log\log N)^{1/3}\). Enumerating these primes takes polynomial bit time, and their product has \(\log S=\Theta(V)\).

Set \(A_S=\operatorname{rad}(S)\). By CRT take \(0<C\le4NA_S\) with
\[
 C\equiv-S Q(m)^{-f}\pmod N,\qquad C\equiv2\pmod4,\qquad C\equiv1\pmod{A_S}.
\]
Then \(P(X)=S+C Q(X)^f\) satisfies \(P(m)=kN>0\). Its reciprocal \(X^dP(1/X)\) is Eisenstein at \(2\) since \(S\) is odd, \(Q\) is monic, and \(v_2(C)=1\). Any content prime of \(P\) divides \(C\) and then divides \(S\), which contradicts the CRT condition. The root at \(m\) is simple modulo \(N\) because \(P'(m)=CfQ(m)^{f-1}Q'(m)\) is a unit. Each monic linear mark \(X-i\) has resultant \(P(i)=S\), and its value at the radix is a unit.

Write \(L=\log N\). If \(\log S=O(V)\), then \(\log k=O(V+d\log(2+e))\). The estimate \(C Q(m)^f\ge N-S\) also gives \(\log C\ge L-O(d\log(2+e))\). The coefficient height has logarithm \(L+O(V+d\log(2+e))\), using the coefficient 1-norm of \(Q^f\) for the upper bound. Since \(|S/C|<1\) for large \(N\), every complex root \(\alpha\) of \(P\) satisfies \(|Q(\alpha)|<1\), so \(|\alpha|\le e+1\). The construction uses only polynomial-bit integer operations. In particular it can take \(e\) growing and \(o((L/\log L)^{1/3})\), with \(f\) chosen to reach the stated degree scale. With \(f=1\) it also shows that \(d\) bounded-value linear marks can coexist with high coefficient height for a primitive nonmonic polynomial.

In \(K=\mathbb Q(\alpha)\), the element \(Q(\alpha)\) has minimal polynomial proportional to \(C X^f+S\), again irreducible by reciprocal Eisenstein. Its iterated squares give a tower of quadratic steps over \(\mathbb Q\). The remaining extension from \(\mathbb Q(Q(\alpha))\) to \(K\) has degree \(e\). A full quadratic example uses a fixed split \(Q\) of degree eight with roots \(\pm1,\pm4,\pm7,\pm8\). It is a composition of quadratics, as the equal square-pair sums give
\[
 Q(X)=\left(\left(X^2-\frac{65}{2}\right)^2-\frac{2529}{4}\right)^2-360^2 .
\]
Use \(m=9\) and the same CRT construction. The successive images of \(\alpha\) under the inner compositions give a full tower since the total degree is the product of the quadratic degrees.

## What the marked ratios supply

In the linear construction \(\left|\operatorname{Nm}_{K/\mathbb Q}(\alpha-i)\right|=S/C\). For each prime above a rational \(p\mid C\), the relation \(Q(\alpha)^f=-S/C\) gives negative valuation of \(Q(\alpha)\). It follows that \(\alpha\) has negative valuation, so every \(\alpha-i\) has the same valuation there. For \(p\nmid CS\), the monic equation for \(\alpha\) is integral at \(p\), and the displayed norm is a unit. Thus every ratio \((\alpha-i)/(\alpha-j)\) has support only above the known primes dividing \(S\), independently of the factorization of \(C\).

If a prime \(p\) larger than every mark difference occurs to odd exponent in \(S\), each \(\alpha-i\) has an odd valuation at some prime above \(p\). This follows from the norm valuation, which is the sum of these valuations weighted by the residue degrees. For exponent one, there is exactly one prime of positive valuation, its valuation is one and its residue degree is one. The positive supports are disjoint for distinct marks, since a common prime would divide \(i-j\). The ratios against one fixed mark therefore have independent ideal parity at these rows. In particular the squarefree band version has full square-class rank on the planted ratios.

### A collision that gives a factor on a particular input

When two marks coincide modulo a prime of $S$, they can yield an actual square. Take $Q=X(X-12)$ and $P=Q^2+27$. With $\gamma=Q(\alpha)$, one has $\gamma^2=-27$. Over $E=\mathbf Q(\gamma)$ the discriminant of $X^2-12X-\gamma$ is
$$
 144+4\gamma=\gamma(4-2\gamma/3)^2 .
$$
The norm of $\gamma$ is $27$, so $\gamma$ is nonsquare in $E$, the quadratic is irreducible over $E$, and $P$ is irreducible over $\mathbf Q$. Thus $(2\alpha-12)/(4-2\gamma/3)$ squares to the product $\alpha(\alpha-12)$ in the quartic field. The two marks coincide modulo three.

For $N=P(16)=4123$ the evaluation at $16$ gives $Q(16)=64$, with rational square root $8$. The quartic square root evaluates to $-15/29\equiv426\pmod{4123}$. The gcds with $426-8$ and $426+8$ are $19$ and $217$. All the displayed denominators are units modulo this input. This gives a productive dependency on a single integer with an exact, checkable certificate. The choice $N=P(16)$ is essential to the example. Constructing such a modular evaluation with a known rational-side square for arbitrary $N$ remains open.

## Cyclotomic marks in a full tower

Take \(d=2^r\) with \(2^d-1<N\), set \(m=2\), and take an odd smooth unit \(R\) modulo \(N\). A nonunit \(2^d-1\) gives a proper gcd. When its gcd is one, choose \(C\) with \(C\equiv-R/(2^d-1)\pmod N\), \(C\equiv2\pmod4\) and \(C\equiv1\pmod{\operatorname{rad}(R)}\), as above. The primitive polynomial
\[
 P(X)=CX^d+R-C
\]
has \(P(2)=R+C(2^d-1)\equiv0\pmod N\) and unit derivative \(Cd2^{d-1}\). Reciprocal Eisenstein again gives irreducibility, and the pure power equation gives a full quadratic tower. At the roots of \(g_i=\Phi_{2^i}(X)\), for \(0\le i\le r\), the marked value is \(R\). Thus \(\operatorname{Res}(g_i,P)=R^{\deg g_i}\). Up to a degree cutoff \(1\le s\le d/2\), this gives \(2+\lfloor\log_2 s\rfloor\) primitive irreducible marks with coefficients of magnitude at most one. Taking \(\log R\asymp V/s\) keeps the largest marked values on the \(\exp(\Theta(V))\) scale.

Exact examples include the degree-12 chart at \(N=35\) with \(C=27886\), \(S=429\), \(m=4\) and \(P(m)/N=1032591\), the degree-32 full quadratic chart at \(N=10403\) with \(C=107098\), \(S=177147\) and \(m=9\), and the cyclotomic-mark chart at \(N=77\) with \(d=16\), \(C=730\) and \(R=243\). Exact polynomial computations checked irreducibility, the marked resultants and the derivative gcds. A further 100 linear-chart attempts gave 98 charts satisfying the modular and marked-value checks. The other two encountered nonunit inputs in the preliminary gcd checks.
