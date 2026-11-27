# Smooth primitive ideals in a majority of quadratic classes

Let \(D<0\) be fundamental, let \(V=\sqrt{|D|}\), and fix a constant \(C\). Put \(X=V^{101/100}\) and \(Y=V^{9/10}\). For every integer \(Z\ge1\) with \(\log Z\le (\log V)^C\), consider primitive integral ideals of norm at most \(X\) coprime to \(Z\). An ideal is primitive if no rational integer greater than one divides it as an ideal. Under Dirichlet GRH, more than sixty percent of all ideal classes contain at least one eighth of the predicted per-class total as such ideals with \(Y\)-smooth norms, uniformly for large \(V\). The same conclusion holds for every smoothness cutoff \(y\ge Y\).

## The global bad-ideal upper bound

Write \(a_Z(n)\) for the number of admitted primitive ideals of norm \(n\) and define

\[
 F_Z(s)=\sum_{n\ge1}a_Z(n)n^{-s}
  =\frac{\zeta(s)L(s,\chi_D)}{\zeta(2s)}\prod_{p\mid Z}F_p(s)^{-1}.
\]

The primitive Euler factors \(F_p\) are \((1+p^{-s})/(1-p^{-s})\) at a split prime, \(1+p^{-s}\) at a ramified prime, and \(1\) at an inert prime. At a split prime a primitive ideal can use either direction with arbitrary multiplicity. At a ramified prime the square of the prime ideal is \((p)\). Write

\[
 \mathcal D_Z=\frac{1}{\zeta(2)}\prod_{p\mid Z}F_p(1)^{-1},\qquad
 C_Z=L(1,\chi_D)\mathcal D_Z.
\]

Uniformly for real \(1\le s\le 1+O(1/\log V)\), one has \(L(s,\chi_D)/L(1,\chi_D)=1+o(1)\). Indeed, the Dirichlet GRH estimate \(\sum_{n\le t}\Lambda(n)\chi_D(n)\ll\sqrt t\log^2(|D|t)\) allows truncation of the series for \(-L'/L\) at \(U=(\log V)^8\). Partial summation bounds its tail by \(O(U^{-1/2}\log^2(|D|U))\), and Chebyshev's bound on the initial sum gives \(O(\log U)\) for the logarithmic derivative. Integrating over the displayed segment gives the claim. The series for \(\log L(1,\chi_D)\) with the same cutoff also has an \(o(1)\) tail and its initial absolute sum is \(O(\log\log U)\). In particular \(L(1,\chi_D)\ge(\log\log V)^{-O(1)}\). [Dirichlet GRH prime estimates](https://academic.oup.com/qjmath/article/74/4/1505/7240642)

Choose a fixed \(B_0>\max(C+3,4)\) and put \(U_0=(\log V)^{B_0}\). The local factors for \(p\mid Z\) have logarithmic derivatives bounded in total by \(O(\log U_0+\log Z/U_0)\) for real \(s\ge1\). This follows by summing \(O((\log p)/p)\) up to \(U_0\) and using \(\sum_{p\mid Z}\log p\le\log Z\) above it. Thus the local product also changes by a relative \(o(1)\) over the same segment. Mertens' estimate below \(U_0\) and the sum of \(1/p\) over \(p\mid Z\) above \(U_0\) give \(\mathcal D_Z\ge(\log\log V)^{-O(1)}\). In particular the residue \(C_Z\) is bounded below by an inverse fixed power of \(\log\log V\). Both conclusions allow the stipulated \(\log Z\) budget, for example a product of a polynomial number in \(\log V\) of core primes and all primes up to a fixed power of \(\log V\). The cutoff \(U_0\) in this proof can exceed that presieve threshold.

Put \(L_0=\log(X/Y)\). Rankin's inequality and the estimates near \(1\) yield

\[
 \sum_{m\le X/Y}\frac{a_Z(m)}m
 \le e F_Z(1+1/L_0)=(e+o(1))C_Z L_0.
\]

Since \(Y^2>X\), an admitted ideal with a prime \(p>Y\) in its norm has exactly one such factor of the norm, with exponent one. If it splits, its prime ideal is one of two choices. The prime number theorem and the Dirichlet GRH character estimate give \(2\pi_{\rm split}(t)\le(1+o(1))t/\log Y\) uniformly for \(Y\le t\le X\). Summing over the norm \(m\) of the cofactor and allowing all split primes up to \(X/m\) gives an upper bound. Ramified primes above \(Y\) divide \(D\), so there are \(O(1)\) of them. Their contribution is \(O((X/Y)\log X)=o(C_ZX)\), since \(a_Z(m)\le\tau(m)\) and \(\sum_{m\le t}\tau(m)\ll t\log(2t)\). Consequently the number of bad ideals is at most

\[
 \left(\frac{11e}{90}+o(1)\right)C_ZX,
\]

which is eventually less than \(0.34C_ZX\). [Prime counting under Dirichlet GRH](https://academic.oup.com/qjmath/article/74/4/1505/7240642)

## Uniform counts in balanced classes

Represent the inverse of a prescribed class by an integral ideal \(J\). The integral ideals in the prescribed class correspond to nonzero \(\alpha\in J\) modulo units, by \(\alpha\mapsto(\alpha)J^{-1}\). The normalized lattice \(J/\sqrt{NJ}\) has covolume \(V/2\), and \(N((\alpha)J^{-1})=|\alpha|^2/NJ\). Its squared shortest length is the leading coefficient \(A\) of its reduced positive definite form. Fix \(K\ge4\) and call the class balanced when \(A\ge V/(\log V)^K\). There are \(O(W(1+\log W))\) reduced forms with \(A\le W\) for this discriminant. For each such \(A\), count roots of \(b^2\equiv D\pmod{4A}\) with \(|b|\le A\). At an odd prime power there are at most two roots since a fundamental discriminant has odd-prime valuations at most one. The two-part also has a bounded root count since \(v_2(D)\in\{0,2,3\}\). Summing \(O(2^{\omega(A)})\) gives the claim. With \(W=V/(\log V)^K\), the number of unbalanced classes is \(o(h_D)\) by the class number formula and the lower bound for \(L(1,\chi_D)\). [Reduced forms and the discriminant root bound](keybreak-quadratic-class-correction.md#a-short-representative-avoiding-the-modulus)

For a given generator, primitivity forbids membership in \(pJ\) for every rational prime \(p\). If \(p\mid Z\), coprimality forbids membership in \(\mathfrak pJ\) for each prime ideal over \(p\). These conditions in \(J/pJ\) have allowed density \(1-p^{-2}\) if \(p\nmid Z\) or \(p\) is inert, \((1-p^{-1})^2\) if \(p\mid Z\) splits, and \(1-p^{-1}\) if \(p\mid Z\) ramifies. In the split case the two forbidden lines intersect only at zero. Their infinite product is exactly \(\mathcal D_Z\).

Let \(\lambda_1\) be the shortest length of the normalized lattice and take the disk of radius \(R=\sqrt X\). The count in any translate of \(eJ/\sqrt{NJ}\) differs from \(\pi X/(e^2 V/2)\) by \(O(R/(e\lambda_1)+1)\). In a basis reduced along a shortest vector, count rows and then points in each chord. The rounding error is at most the number of rows, and replacing the chord sum by the area integral costs \(O(R/(e\lambda_1))\) because the chord length has total variation \(O(R)\). The row count has this order plus one by the planar shortest-vector bound. The same argument for any sublattice with covolume \(\Delta'\) and shortest length \(\lambda'_1\) gives the upper bound \(O(X/\Delta'+R/\lambda'_1+1)\).

For primes \(p\le U_0\) truncate inclusion–exclusion at consecutive even and odd orders of size \(s_0\asymp\log\log V\). The forbidden local densities \(\alpha_p\) satisfy \(\sum_{p\le U_0}\alpha_p=O(\log\log U_0)\), so the omitted independent tail is bounded by \(\sum_{j\ge s_0}(\sum\alpha_p)^j/j!\), smaller than any fixed negative power of \(\log\log V\). The number of tested squarefree products and the number of CRT residues per product are each at most \(U_0^{O(s_0)}=V^{o(1)}\). The summed lattice error is therefore \(V^{o(1)}(R/\lambda_1+1)\), also allowing the removal of zero. Since \(R/\lambda_1\le V^{1/200}(\log V)^{K/2}\), this error is \(o((X/V)\mathcal D_Z)\).

For the remaining primitivity restrictions, a nonzero vector in \(pJ\) requires \(p\le R/\lambda_1\). Summing translated-lattice upper bounds for \(p>U_0\) costs

\[
 O\left(\frac{X}{VU_0}+\frac{R}{\lambda_1}\log X+\frac{R}{\lambda_1}\right)
   =o((X/V)\mathcal D_Z).
\]

For \(p>U_0\) dividing \(Z\), each lattice \(\mathfrak pJ/\sqrt{NJ}\) has covolume at least \(pV/2\) and shortest length at least \(\lambda_1\). The union costs \(O((X/V)(\log Z)/U_0+(R/\lambda_1+1)\log Z)\), again negligible. The omitted factors in the independent local product have relative error \(O(1/U_0+(\log Z)/U_0)=o(1)\). Thus, writing \(w_D\) for the number of units, the uniform balanced-class count is

\[
 (1+o(1))\frac{2\pi X}{w_DV}\mathcal D_Z
  =(1+o(1))\frac{C_ZX}{h_D}.
\]

The last identity is the imaginary quadratic class number formula. [Class number formula](https://arxiv.org/abs/1309.3595)

## The majority bound

Put \(\mu=C_ZX/h_D\). If a balanced class contains fewer than \(\mu/8\) smooth admitted ideals, its bad count is at least \((7/8-o(1))\mu\). The global bad-ideal bound therefore limits the fraction of all classes that are balanced and fail to \(\frac87\frac{11e}{90}+o(1)\). The fraction of unbalanced classes is \(o(1)\). Hence at least

\[
 1-\frac87\frac{11e}{90}-o(1)>0.60
\]

of all classes have at least \(\mu/8\) coprime primitive ideals with \(Y\)-smooth norms. Summing the balanced-class count also shows that the global bad fraction among all admitted ideals is at most \(11e/90+o(1)\).
