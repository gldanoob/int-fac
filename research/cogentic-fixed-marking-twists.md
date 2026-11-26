# A fixed marking and short rational twist parameters

The norm-lift menu can mark the fourth coordinate throughout. For every pair of primes satisfying the existing Boolean separation conditions on \(b\), the rational choice \(c=1/b\) separates them or reveals a proper gcd. A conic through \(1/b\) gives a polynomial-height family with separation on every nondegenerate member. The twist sign can be prescribed at either prime by a longer progression estimate. The absolute Frobenius trace remains that of the fixed Legendre curve with parameter \(b\). [Moving norm-lift menu](cogentic-moving-elliptic-separation.md)

## One marking for all remaining difference colors

Use the four coordinates \((0,1,b,c)\) and always mark \(c\). At the two odd primes write \(L(s)\in\mathbb F_2^2\) for the pair of Legendre bits of a unit \(s\), and set
\[
 z=L(-1),\quad a=L(b),\quad h=L(b-1),\quad
 u=L(c),\quad v=L(c-1),\quad w=L(c-b),\quad \omega=u+v+w.
\]
The norms in the existing menu prescribe \(a,h\) with \(a\ne0\), \(a\ne h\), \(a\ne z\), and \(h\ne z\). These inequalities hold in every row of its robust table. Put \(D=c(c-1)(c-b)\). The curve and point for this marking are
\[
 E_c:\ Y^2=X(X-D)(X-Db),\qquad R_c=(Dc,D^2).
\]
In the stacked Kummer matrix with columns \(R_c,T_0,T_1\), combine corresponding rows at the two primes into pairs of bits. The three columns are
\[
 P=(\omega+u,\omega+v),\qquad
 J=(a,\omega+z),\qquad K=(\omega,h+z).
\]
The torsion columns are nonzero and distinct for every \(\omega\). Nonvanishing follows from \(a\ne0,h\ne z\), and equality would require \(a=h\). To test that \(P\) is outside their span it suffices to check four possibilities. The equalities \(P=0,P=J,P=K,P=J+K\) respectively require \(u=v\), \(v=z\), \(u=0\), and \((u,v)=(a,h)\).

At \(c=1/b\), one has \(u=a\) and \(v=z+h+a\). The four equalities would respectively violate \(h\ne z\), \(h\ne a\), \(a\ne0\), and \(a\ne z\). Thus this single marking works for every \(w\). If \(c=b\) at both primes then \(b=-1\) at both, since \(b=1\) has already been excluded. This violates \(a\ne z\). A collision at just one of the two primes therefore gives a proper gcd. The other differences are units at both. For \(b=B/A\) in lowest terms the public integral coordinates can be taken as \((0,AB,B^2,A^2)\), with the common scaling checked by gcd. [Kummer formula and input-only construction](cogentic-moving-elliptic-separation.md#four-choices-of-a-marked-coordinate)

## Consecutive conic parameters

Put \(C=1/b\) and \(D_0=C-1\). The conic \(CU^2-D_0V^2=1\) has base point \((1,1)\). Intersecting with \(V=1+t(U-1)\) gives
\[
 W=C-D_0t^2,\qquad U=\frac{-C+2D_0t-D_0t^2}{W},\qquad
 V=\frac{C-2Ct+D_0t^2}{W}.
\]
Take \(c(t)=CU^2\). Then \(c(t)-1=D_0V^2\), so the two needed colors are unchanged whenever \(U,V,W\) give units. Over either odd prime the two nonzero conic coefficients make the conic nonsingular. At most ten finite residues of \(t\) are excluded by the two quadratic numerators, the quadratic denominator and \(c(t)=b\), whose cleared numerator has degree at most four and is nonzero. Any consecutive interval of \(M\le\min(p,q)\) parameters therefore gives at least \(M-20\) usable entries. Each rational value occurs at most four times since the map has degree four. Each usable entry separates with the same marked index. Public gcd checks can also report a split on an excluded entry.

Writing the conic with common denominator \(B\) gives the height bound \(O(H(b)^3(1+|t|)^4)\), where \(H(b)=\max(|A|,|B|)\). The norm-lift menu already has polynomial bit length. A polynomial bound on numerical height is also available under the same Dirichlet RH hypothesis. Choose distinct primes \(\beta,\eta\equiv1\bmod8\) of size \(O((\log N)^2)\) with \(L(\beta)=a,L(\eta)=h\), and require \((\eta/\beta)=+1\) in the second prime choice. The fixed-index prime bound applies since the sign conditions at \(p,q,\beta\) and modulo 8 are independent. Then \((-\eta/\beta)=(\beta/\eta)=+1\), and Legendre's criterion and Holzer's bound give a nonzero integral solution of \(\beta x^2-\eta y^2=z_0^2\) with \(|x|\le\sqrt\eta\), \(|y|\le\sqrt\beta\), \(|z_0|\le\sqrt{\beta\eta}\). After trial division through the height of these coordinates they are units at the remaining primes. The rational \(b=\beta(x/z_0)^2>1\) has height at most \(\beta\eta\), and \(b-1=\eta(y/z_0)^2\). The rational box and the conic list can both be enumerated in polynomial time for \(M\) polynomial in \(\log N\), with trial division through \(M+20\) if needed. [Pointwise conic construction and height bounds](pointwise-conic-marks.md#small-positive-coefficients) · [Least-prime bound, Theorem 1.4](https://arxiv.org/pdf/1309.3595#page=3)

## What the twist can change

Set \(X=Dx\) and \(Y=Dy\) in \(E_c\). This gives \(y^2=D x(x-1)(x-b)\). Thus the trace at a good odd prime \(p\) is \(\chi_p(D)t_p(b)\), where \(t_p(b)\) is the trace of \(y^2=x(x-1)(x-b)\). For all \(c\), the rational invariant is
\[
 j(b)=256\frac{(b^2-b+1)^3}{b^2(b-1)^2}.
\]
If \(b=B/A>1\), integrality of \(j(b)\) forces \(A,B,B-A\) to be powers of two, since the numerator is coprime to each apart from the factor 256. These three positive integers are pairwise coprime, hence \(A=B-A=1,B=2\). A rational CM invariant must be integral. Therefore the only rational CM case here is \(b=2\), with \(j=1728\) and trace zero at primes \(p\equiv3\bmod4\), regardless of the twist. For these primes the trace vanishing also follows by shifting the Legendre roots to \(-1,0,1\) and pairing \(x\) with \(-x\) in the trace sum. [Integrality of CM invariants](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)

For a fixed pattern of \(\omega\) at \(p,q\), the pair \(u,v\) can vary freely in the Boolean table and uniquely determines \(w\). The point column \(P\) then takes each of the 16 stacked values once. Exactly four lie in the torsion span. At either prime each of the eight profiles of the three signs of \(c,c-1,c-b\) occurs \(p/8+O(\sqrt p)\) times by expanding the three indicators and applying Weil to products of distinct linear factors. Hence for \(c\) uniform modulo \(pq\) the conditional rank-three proportion for each prescribed pair of twist signs is \(3/4+O(p^{-1/2}+q^{-1/2})\). The statement is about trace signs when the corresponding traces are nonzero, and also applies when a trace is zero. [Weil's complete sums](https://pmc.ncbi.nlm.nih.gov/articles/PMC1079093/)

In the short conic list, separation is already certified independently of the twist. The only varying sign in the twist is that of \(c(t)-b\). The projection of the conic onto the \(c\)-line is a degree-four map, adjoining the two roots of \(c/C\) and \((c-1)/D_0\), whose branch values are \(0,1,\infty\). Since \(b\) is distinct from them, \(c(t)-b\) has four simple geometric zeros and square poles. It is therefore represented for the quadratic character by a nonsquare polynomial of degree at most four. Complete mixed Weil bounds and Fourier completion give, on an interval of length \(M\le p\), \(M/2+O(\sqrt p\log p)\) parameters realizing either chosen twist at \(p\), before the \(O(1)\) local exclusions. Exclusions at the other prime cost \(O(1+M/q)\) further entries. Thus a single desired twist at \(p\) can be imposed by this estimate once \(M\gg\sqrt p\log p\) and the good primes are sufficiently large. The polynomial-length list yields many separating curves. Its guarantees on their twist signs require the longer bound. In particular it supplies no new smooth local orders beyond the two orders \(p+1\pm t_p(b)\). [Mixed character sums](https://www.math.ksu.edu/~cochrane/research/stepmix.pdf)
