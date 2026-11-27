# Primitive completions from a majority of quadratic classes

Let \(K\) be an imaginary quadratic field with maximal order \(\mathcal O_K\), discriminant of absolute size \(\asymp V^2\), and class number \(h\gg V/(\log V)^D\) for a fixed \(D\). Set \(X=V^{1+\varepsilon}\) for fixed \(\varepsilon>0\), \(N=X/V\), and \(z\ge(\log V)^4\). Fix a set of forbidden rational primes. Suppose more than \(0.60h\) classes each contain \(\gg N\delta\) primitive integral ideals of norm at most \(X\), with every prime factor of the norm at most \(y\) and greater than \(z\), and with norm coprime to the forbidden primes. Assume \(\delta\gg(\log\log V)^{-D_1}\) for fixed \(D_1\), with uniform constants across the good classes.

Then every target class contains \(\gg X^2/[V(\log V)^{O(1)}]\) distinct primitive integral ideals of norm at most \(X^2\) obeying the same prime restrictions. Each is a product of two of the specified ideals with relatively prime rational norms, and the counted products have at most \((\log V)^{O(1)}\) ordered factorizations into integral ideals.

## Uniform counting at smaller cutoffs

In any fixed class the number of primitive integral ideals of norm at most \(U\) is \(O(1+U/V)\), uniformly in \(U\) and in the class. Take an integral ideal \(\mathfrak b\) in the inverse class. An integral ideal \(\mathfrak a\) in the given class has \(\mathfrak a\mathfrak b=(\gamma)\) for \(\gamma\in\mathfrak b\), and \(\mathrm N\mathfrak a=|\gamma|^2/\mathrm N\mathfrak b\). For any integer \(m\ge2\), one has \(\gamma\in m\mathfrak b\) exactly when \(\mathfrak a\subseteq m\mathcal O_K\), by invertibility of \(\mathfrak b\). Thus primitive ideals correspond, up to units, to primitive vectors in the lattice \(\mathfrak b/\sqrt{\mathrm N\mathfrak b}\), where the quotient denotes geometric scaling. This lattice has covolume \(\sqrt{|\operatorname{disc}K|}/2\asymp V\), and the norm bound gives a disk of radius \(\sqrt U\).

If the lattice vectors in the disk span at most a line, at most two of them are primitive. Otherwise a shortest lattice vector of length \(\lambda\le\sqrt U\) defines parallel lattice rows spaced by the covolume divided by \(\lambda\). This spacing is at most \(\sqrt U\) since there is a vector off the central row in the disk. Counting those rows and the points along each gives \(O(U/V)\). This proves the stated bound including small cutoffs.

## Pairs in a prescribed class

Write \(G\) for the class group and \(S\subset G\) for the good classes. For a target \(C\), the map \(c\mapsto Cc^{-1}\) is a bijection. More than \(0.20h\) classes belong both to \(S\) and to its inverse image under this map. For each such class, fix a first ideal \(\mathfrak a\) in its specified family. Its partner lies in the single good class \(C[\mathfrak a]^{-1}\).

Remove partners whose norm is divisible by any rational prime \(q\mid\mathrm N\mathfrak a\). For a primitive partner, such divisibility requires a prime ideal over \(q\) of norm \(q\). An inert prime cannot occur, as its sole prime ideal is \((q)\). At a split or ramified prime there are at most two candidate prime ideals. On dividing by one of them, the class is fixed, the ideal remains integral and primitive, and its norm is at most \(X/q\). The uniform cutoff count bounds the number of excluded partners for this \(q\) by \(O(1+N/q)\). All the primes of \(\mathrm N\mathfrak a\) exceed \(z\) and their number is at most \(\log X/\log 2\), so the number removed per first ideal is at most
\[
 O\bigl(\log X(1+N/z)\bigr)=o(N\delta).
\]
The first term is negligible because \(N=V^\varepsilon\), and the second because \(z\ge(\log V)^4\). Consequently there are \(\gg hN^2\delta^2\) ordered pairs in the target class with coprime rational norms. Each product is primitive. Indeed, a rational principal ideal \((q)\) for prime \(q\) dividing the product would have to divide one factor whenever \(q\) divides just one of the two norms, contradicting primitivity of that factor.

## Distinct products

For an integral ideal \(\mathfrak a\), let \(\tau_K(\mathfrak a)\) count its integral ideal divisors. Uniformly in the discriminant,
\[
 \sum_{\mathrm N\mathfrak a\le X}\tau_K(\mathfrak a)
 \ll X(1+\log X)^3.
\]
The norm coefficients of \(\zeta_K\) are bounded coefficientwise by those of \(\zeta^2\), as follows directly from the split, ramified and inert Euler factors. The displayed sum has Dirichlet series \(\zeta_K^2\) and is bounded by the summatory coefficients of \(\zeta^4\). The elementary bound for that sum follows by summing three of the factors with harmonic weights and counting the fourth by \(X\) divided by their product.

Set \(T=(\log V)^L\) and discard pairs with \(\tau_K>T\) on either side. There are \(O(X(1+\log X)^3/T)\) ideals of norm at most \(X\) above this divisor threshold, and each has \(O(N)\) possible primitive partners in its complementary class. For fixed \(L>D+5\) the number of discarded pairs is \(o(hN^2\delta^2)\). Each remaining product has divisor count at most \(T^2\), by unique ideal factorization and \(e+f+1\le(e+1)(f+1)\) at each prime ideal. Its divisor count bounds the number of ordered representations of the product. Dividing the surviving pair count by \(T^2\) proves the claimed lower bound.

The forbidden set can include the primes dividing \(2Z\) and the \(O(d)\) individual primes already selected from bins. The conclusion is uniform in these exclusions whenever the majority hypothesis is uniform. With \(y\le V^{0.9}\), all prime factors of the completion norm satisfy that same bound, including the factors introduced by class correction.

## A split prime extends the cutoff to every fixed exponent above \(e^{-2/3}\)

Let \(V=\sqrt{|D|}\) for a negative fundamental discriminant and let \(e^{-2/3}<c<1\) be fixed. Under Dirichlet GRH there is a fixed \(L=L(c)>0\) such that **every ideal class** contains \(\gg V^{L-1}/(\log V)^{O(1)}\) distinct primitive integral ideals of norm at most \(V^L\) whose norm is \(V^c\)-smooth and coprime to the given \(Z\). As above, \(\log Z\) may be any fixed power of \(\log V\). The constants are uniform in the class, discriminant and admitted modulus.

Choose \(s=1+\varepsilon\) just above one, with \(c>s/2\) and \(\lambda=\log(s/c)<2/3\). Put \(X=V^s\), include all primes up to \((\log V)^4\) in the excluded set, and choose a sufficiently small fixed \(\tau>0\) that \(1-\lambda/(1-\tau)>1/3\) by a fixed margin. The real-moment estimate and the count in balanced classes give a set \(A\) of density at least \(1/3+2\eta\) for some fixed \(\eta>0\), each containing at least \(\tau C_Z X/h\) admitted smooth primitive ideals. Here \(C_Z X/h\gg (X/V)(\log\log V)^{-O(1)}\). Remove classes in which more than half this supply has ideal divisor count greater than \((\log V)^B\). The global divisor-count sum proved above shows that only \(o(h)\) classes are removed if \(B\) is a sufficiently large fixed constant. Keep the remaining set with density \(\delta\ge1/3+\eta\). [Real-moment smoothness bound](keybreak-quadratic-smooth-majority.md)

Independently of this set, let \(\nu\) be the class distribution of uniformly sampled oriented split prime ideals with rational prime in \([V^\kappa,2V^\kappa]\) away from \(2DZ\), for any fixed \(0<\kappa<c\). Every nontrivial order-two class character is a genus character attached to a factorization \(D=D_1D_2\) into nontrivial fundamental discriminants. At a split prime either orientation gives the same sign. The sum over both orientations at each unramified rational prime \(q\) is \(\chi_{D_1}(q)+\chi_{D_2}(q)\), including zero at inert primes. The Dirichlet GRH prime estimate gives \(\sup_{\operatorname{ord}\chi=2}|\widehat\nu(\chi)|=o(1)\), since the number of oriented guards is \(\asymp V^\kappa/\log V\) and the polylogarithmic exclusion removes a negligible number. [Genus characters, §5](https://mast.queensu.ca/~murty/Annalen.pdf)

Write \(\mu\) for uniform probability on \(A\). In the image of any character of order \(m\ge3\), an arc of radius \(\pi/6\) around the argument of its mean contains at most \(\lfloor m/6\rfloor+1\le m/3\) of the \(m\) equally spaced roots. Its preimage contains at most \(h/3\) classes. Thus \(|\widehat\mu(\chi)|\le 1-(1-\sqrt3/2)\eta\). Parseval gives \(\sum_\chi|\widehat\mu(\chi)|^2=1/\delta\). Choose a fixed \(k\ge2\) large enough that \((1-(1-\sqrt3/2)\eta)^{k-2}/\delta<1/4\). Fourier inversion then gives
\[
   (\mu^{*k}*\nu)(t)\ge 1/(2h)
\]
for every target class \(t\) when \(V\) is large. Indeed all higher-order characters contribute in absolute sum at most \(1/4\) in relative units, and the order-two contribution is bounded by \(\sup |\widehat\nu|/\delta=o(1)\).

Count these class tuples and guards *before* making any tuple-dependent deletions. For each tuple, choose a bounded-divisor ideal in each indicated class in order, avoiding primes of the guard and all earlier chosen components. The per-class primitive cutoff bound above costs at most \(O_k(\log X(1+(X/V)/(\log V)^4))\) choices at each step. This is smaller than half the retained per-class supply. Hence each admissible class tuple and guard has \(\gg ((X/V)(\log\log V)^{-O(1)})^k\) coprime realizations. Their products are primitive and fully smooth. The number of ordered representations per product is polynomial in \(\log V\), since the divisor count of the product is at most twice the product of the fixed number of component divisor counts, and each factor is a divisor. Together with the class probability this gives \(\gg V^\kappa X^k/[V(\log V)^{O(1)}]\) distinct products of norm at most \(2V^\kappa X^k\), using \(h\gg V/(\log\log V)^{O(1)}\). To obtain the stated pure power cutoff \(L=\kappa+ks\), take the guard dyad \([V^\kappa/2,V^\kappa]\) instead, which has identical estimates. A real cutoff at the endpoint \(c=e^{-2/3}\) is outside this argument.

## Every class at arbitrary fixed smoothness for almost all discriminants

Let \(D<0\) be fundamental, \(T\le |D|\le2T\), \(V=\sqrt{|D|}\), and \(h=|\mathrm{Cl}(D)|\). Fix \(c,C,A>0\). Unconditionally, with \(O_{c,C,A}(T/(\log T)^A)\) exceptional discriminants, there is a constant \(b=b(c,C,A)\) such that every class contains
\[
  \gg \frac{V^2Y}{h(\log V)^{O_{c,C,A}(1)}} ,\qquad Y=(\log V)^b ,
\]
distinct primitive ideals of norm at most \(V^2Y\), all of whose rational primes are at most \(V^c\) and coprime to \(Z\). The exceptional set is independent of the class and of the integer \(Z\ge1\) with \(\log Z\le(\log V)^C\). For prime discriminants the exception count is \(O(T^{1/2})\). All but \(O(h/(\log V)^A)\) classes already have \(\gg VY/[h(\log V)^{O(1)}]\) such ideals of norm at most \(VY\). The constants, in particular the power of the logarithm in the norm bound, are asymptotic. These are statements about ideal counts.

**A prime distribution for non-genus characters.** For an ideal class character \(\chi\) of order greater than two, complex conjugation takes \(\chi\) to \(\chi^{-1}\ne\chi\). Its theta series is cuspidal of weight one and level \(|D|\), with nebentypus \(\chi_D\), since \(\chi\) is unramified and is trivial on rational principal ideals. Its standard \(L\)-function equals the ideal-character \(L\)-function. Thus its analytic conductor is \(O(T)\), with absolute implied constant. A representation exceptional for one discriminant cannot belong to another discriminant, since the central character determines \(D\). [Class group theta series](https://www2.math.ou.edu/~rschmidt/papers/yoshida-values.pdf)

Thorner and Zaman's Theorem 1.2 bounds the total number of zeros with real part at least \(1-\eta\) up to height \(T\), summed over the conductor-\(O(T)\) GL(2) family over the rationals, by \(O(T^{O(\eta)})\). Use the GL(1) case for the separate characters \(\chi_D\). Fix \(\eta>0\) sufficiently small that deleting every discriminant contributing even one such zero costs \(O(T^{1/2})\). For all retained fields the zero-free rectangles are simultaneous over their non-genus characters. [Thorner and Zaman, Theorem 1.2](https://arxiv.org/pdf/1906.07717#page=3)

Fix a nonnegative smooth weight \(W\) supported inside \((1/2,1)\) with positive integral. At scale \(y\), give each oriented split prime ideal over \(q\) weight \(W(q/y)\log q\). For any of the above cuspidal representations the smoothed explicit formula bounds its prime-power log-derivative sum by
\[
 O_{W,\eta}\big(y^{1-\eta}\log(2T)+yT^{-1}\log(2T)+\log(2T)\big).
\]
Indeed each zero below height \(T\) contributes at most \(y^{1-\eta}|\widehat W(\rho)|\) with Mellin transform rapidly decaying vertically; there are \(O(\log(2T(2+|t|)^2))\) zeros in each unit height interval. The same decay bounds the tail using \(\Re\rho\le1\), and the fixed-degree archimedean terms contribute \(O_W(\log(2T))\). The unramified prime trace equals the sum over both orientations at a split prime and vanishes at inert primes. Removing higher prime powers costs \(O(\sqrt y\log^2(2y))\) by the unitary finite-order local parameters. Deleting the primes dividing \(2DZ\) costs \(O((\log V)^{\max(C,1)}\log(2y))\). The same explicit formula for \(\chi_D\) and the ordinary prime number theorem show that total oriented weight is \(\asymp y\). Consequently at \(y=Y=(\log V)^b\) the normalized oriented distribution \(\nu\) satisfies \(\sup_{\chi^2\ne1}|\widehat\nu(\chi)|\ll(\log V)^{-H}\) for any prescribed fixed \(H\), by taking \(b\) sufficiently large. The prime number theorem is needed only for the total mass. Each individual orientation then has probability \(O(\log Y/Y)\).

**Genus characters at larger primes.** For a nontrivial order-two character corresponding to \(D=D_1D_2\), the sum of its two oriented values at split primes, extended by zero at inert primes, equals \(\chi_{D_1}(q)+\chi_{D_2}(q)\) for \(q\nmid D\). Both factors are nonprincipal. At scales \(y\asymp V^a\) with fixed \(a>0\), each normalized sum is \(O((\log V)^{-H})\) for any fixed \(H\), simultaneously for all the factor characters, after deleting \(O_{a,H,A}(T/(\log T)^A)\) discriminants. To see this, Lemke Oliver, Thorner and Zaman's Theorem 1.1 for the group of order two has \(O(U^{1/2})\) exceptional quadratic fields of discriminant in \([U,2U]\), by taking their family exponent \(1/2\). Every good field has prefix prime-character sum \(O(x\exp(-c_1\sqrt{\log x}))\) above a fixed power of \(\log(2U)\). Partial summation gives the weighted bound on each fixed subinterval of this polynomial-scale dyad. A bad fundamental factor of conductor \(\asymp U\) divides \(O(T/U)\) possible \(D\). Thus for \(U\ge(\log T)^J\) the dyadic sum of exclusions is \(O(T/(\log T)^{J/2})\). For smaller conductors the Siegel–Walfisz theorem applies at \(x\asymp V^a\). Furthermore \(2^{\omega(D)}\le(\log T)^{A+3}\) off \(O(T/(\log T)^A)\) discriminants by the summatory divisor bound. This bounds the number of genus characters. For a prime discriminant genus theory gives only the principal character, so this entire exceptional set is unnecessary. [Genus characters, §5](https://mast.queensu.ca/~murty/Annalen.pdf) · [Lemke Oliver, Thorner and Zaman, Theorem 1.1](https://lemkeoliver.github.io/papers/27-ApproximateArtin.pdf#page=2)

**Counting products.** Choose a fixed integer \(k>1/c\). Select \(2k\) disjoint closed subintervals of \((V^{1/k}/2,V^{1/k})\) with lengths fixed positive multiples of \(V^{1/k}\), and sample independently one oriented split prime per interval, away from \(2DZ\), using fixed rescaled smooth weights as above. The first and last \(k\) intervals give class distributions \(\mu_1,\mu_2\). Every selection in either group gives a distinct primitive ideal of norm at most \(V\) by unique factorization and disjointness. Each such ideal has probability \(O((\log V)^k/V)\). The primitive per-class bound \(O(1+U/V)\) at \(U=V\), proved above, gives the same bound for each class probability. In particular,
\[
   \sum_\chi |\widehat\mu_i(\chi)|^2=h\sum_g\mu_i(g)^2
       \ll (\log V)^{k+1},
\]
using the class number bound \(h\ll V\log V\). Nontrivial genus frequencies of either \(\mu_i\) are \(O((\log V)^{-H})\) by the preceding paragraph. All constants here are independent of \(b\).

The extra oriented prime of law \(\nu\) has its own disjoint interval. In Fourier inversion for \(h(\mu_1*\mu_2*\nu)(g)\), the principal term equals one. Cauchy–Schwarz bounds the non-genus error by \(O((\log V)^{k+1-H})\). The genus error is \(O((\log V)^{A+3-H})\). Take \(H\) sufficiently large in terms of \(A,k,C\), then choose \(b\). Every target consequently has probability \((1+o(1))/h\). For the one-group law \(\mu_1*\nu\), Parseval gives
\[
  \frac1h\sum_g |h(\mu_1*\nu)(g)-1|^2
     =\sum_{\chi\ne1}|\widehat\mu_1(\chi)\widehat\nu(\chi)|^2
     \ll (\log V)^{k+1-2H}+(\log V)^{A+3-2H}.
\]
Increasing \(H\) makes the fraction of targets below half the uniform probability \(O((\log V)^{-A})\). For either assertion all rational primes are distinct and appear in prescribed intervals, so each selected tuple gives a different primitive ideal even after the extra prime is included. Dividing the class probability by the maximum individual tuple probability proves the counts.

**A lower bound for the worst class.** The exponent two in the uniform norm bound is necessary even if the permitted smoothness cutoff is increased arbitrarily. Take any negative fundamental discriminant \(D\equiv1\pmod8\), let \(Z=2\), and use the ordinary class of the primitive positive form \([2,1,(1-D)/8]\). Primitive integral ideal norms in this class (or its inverse, which has the same norm values by conjugation) are the values at coprime integer coordinates. Along \(y=0\) the only primitive value is the excluded value two. For \(y\ne0\), completing the square gives
\[
 8\,f(x,y)=(4x+y)^2+|D|y^2\ \ge\ |D|.
\]
Thus the smallest admitted norm in this class is at least \(V^2/8\). This applies also to negative prime discriminants in this progression. The upper bound differs by a power of \(\log V\); the uniform lower bound is an exponent statement and gives no lower bound of that logarithmic size. Membership of a single class in the exceptional set at the smaller norm scale is consistent with the almost-all-classes estimate.

## How many classes require a large coprime representative?

The obstruction at the smallest reduced coefficient gives an asymptotic count across the entire class group. Let \(M_Z(g)\) be the least norm of a primitive integral ideal of class \(g\) coprime to \(Z\); impose no smoothness restriction for this count. Write \(P_Z=C_Z/C_1\) for the product of local coprimality densities among primitive ideals. Assume \(W/V\to\infty\), \(W\le V^{2-\epsilon}\) for fixed \(\epsilon>0\), and \(\operatorname{rad}(2Z)^2V/W\to0\). In particular \(Z\) may be any fixed positive integer. Outside the power-saving exceptional family in the total norm estimate, or for all fields under Dirichlet GRH,
\[
 \frac{\#\{g:M_Z(g)>W\}}{h}
   =\frac{\pi}{4\zeta(2)}\bigl(\gamma_Z(D)+o(1)\bigr)\frac VW,
 \qquad
 \gamma_Z(D)=
 \begin{cases}
  2-4P_Z,&2\mid Z,\quad D\equiv1\pmod8,\\
  1-P_Z,&\text{otherwise}.
 \end{cases}
\]
For example, if \(2\) splits and \(Z=2\), the fraction is \((1/\pi+o(1))V/W\). It is a lower bound for the fraction of classes that also lack a smooth representative at that norm. The two sides agree to additive \(o(V/W)\), including cases with zero local obstruction. [Total norm estimate on all polynomial scales](keybreak-quadratic-smooth-majority.md#total-and-smooth-counts-below-the-lattice-scale)

Take a reduced primitive form \([a,b,c_0]\) for the class, with \(|b|\le a\le c_0\) and \(a\le V/\sqrt3\). Its primitive values are precisely the primitive ideal norms in that class, after choosing the usual form–ideal convention. If \((a,Z)=1\), the minimum is \(a\le W\). Otherwise a permitted value requires \(y\ne0\). Let \(d=2\) if \(2\mid Z,\ D\equiv1\pmod8,\ a\) is odd; let \(d=1\) otherwise. In the special case \(b\) is odd and \(c_0\) is even, since \(4ac_0=b^2-D\equiv0\pmod8\). Odd \(y\) then forces an even value, hence \(|y|\ge d\). Completing the square gives the lower bound \(M_Z(g)\ge d^2V^2/(4a)\).

Conversely take \(y=d\). At every odd prime \(p\mid Z\), the polynomial in \(x\) is nonzero modulo \(p\) by primitivity and \(p\nmid d\); at most two residues are excluded. At two, when \(d=2\) choose \(x\) odd. When \(d=1\) and \(2\mid Z\), the value modulo two is \((a+b)x+c_0\). Its identical vanishing would force \(c_0\) even and \(a,b\) both odd by primitivity, precisely the case already assigned \(d=2\). CRT now allows a suitable \(x\) within \(O(\operatorname{rad}(2Z))\) of \(-bd/(2a)\), with \((x,d)=1\). The upper bound is \(M_Z(g)\le d^2V^2/(4a)+O(a\operatorname{rad}(2Z)^2)\). Thus the classes above threshold correspond to ineligible shortest norms \(a\) below \(d^2V^2/(4W)\), up to a band of relative width \(o(1)\), uniformly under the hypotheses. Powers in \(Z\) can be removed before applying the total norm estimate.

Each primitive ideal of norm in this short range is the unique shortest primitive ideal in its class. Indeed norms of two independent primitive vectors in the normalized ideal lattice have product at least \(V^2/4\) by the determinant, while collinear primitive vectors agree up to sign. Here all relevant cutoff norms are \(o(V)\). Equivalently the exact integral identity reads \(4f(x,y)f(u,v)=B_f((x,y),(u,v))^2+|D|(xv-yu)^2\), with \(B_f\) the integral polarization. Consequently the total ideal count on short intervals counts classes here as well. [Lean determinant identity and primitive uniqueness](../formal/cogentic/Cogentic/RandomizedPrimitiveQuadraticRoot.lean) · [Lean odd-value bounds](../formal/cogentic/Cogentic/RandomizedQuadraticNormBound.lean)

Put \(U=V^2/(4W)\). If \(d=1\) for every ineligible norm, the count is \(C_1 U(1-P_Z+o(1))\) from the total and coprime asymptotics. In the split-at-two case with \(2\mid Z\), primitive even norms have density \(2/3\) relative to \(C_1\) since the primitive Euler factor at two is three. Count them up to \(U\). The odd ineligible norms have density \(1/3-P_Z\) and are counted up to \(4U\). The transition bands contribute \(o(C_1 U)\) by the uniform total asymptotic at these fixed-power scales. Finally \(C_1=L(1,\chi_D)/\zeta(2)\) and \(h=V L(1,\chi_D)/\pi\) for \(D<-4\). This yields the stated constant.
