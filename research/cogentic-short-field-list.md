# A deterministic pair with private smooth valuation rows

For every sufficiently large odd input \(N\), and every \(1\le r\le\lfloor h/2\rfloor\) with \(h\sim(\log N/\log\log N)^{1/3}\), a deterministic construction either gives a proper divisor or gives one pair of monic irreducible polynomials of degrees \(h+r,h+r+1\). They have a simple common root modulo \(N\) and \(r\) specified primitive marks with unit residues. Both norms at every mark are positive, squarefree, and at most \(\exp(O(r\log h))\). On \(r\) specified odd-prime ideal rows, the joint valuation matrix of these marks is the identity over \(\mathbb Z\). The construction balances the ownership of these rows between the fields, giving \(\lceil r/2\rceil\) rows in the first and \(\lfloor r/2\rfloor\) in the second. Each selected prime has exactly one simple affine root in its assigned field and no root in the other.

The pair uses zero random coefficient bits and costs \(\exp(O(r\log h))\operatorname{poly}(\log N)\) bit operations. At \(r=\lfloor h/2\rfloor\), this is the one-third scale. The [planted norm-two construction](cogentic-planted-norm-two.md) instead puts all mark valuations on one prime above two in each field. The new rows distinguish the marks by their odd ideal support. They can be cleared from additional relation columns by explicit integer column operations.

## Constructing the two fields

Let \(m\) be the largest odd integer with \(m^h\le N\), let \(t_j=2j\) for \(0\le j<r\), and set \(P(X)=\prod_j(X-t_j)\). Take \(d_i=h+r+i-1\) for \(i=1,2\) and choose the first \(r\) primes \(p_j>2d_2+2\). These are \(O(h\log h)\) by the prime number theorem. Test the gcds of all \(m-t_j\) and \(p_j\) with \(N\). These integers lie in \((0,N)\) for large \(N\), so any nonunit gives a proper factor. Otherwise \(P(m)\) and \(K=\prod_jp_j\) are units modulo \(N\).

Assign \(p_j\) to field \(i_j=1+(j\bmod 2)\). For each prime choose a monic rootless quadratic and a monic rootless cubic in \(\mathbb F_{p_j}[X]\), by testing every coefficient tuple and every residue. Such quadratics and cubics exist by counting the union of the root conditions. For monic degree \(n=2,3\), fixing distinct \(k\le n\) roots leaves \(p_j^{n-k}\) polynomials, and fixing \(n+1\) leaves none. Inclusion-exclusion gives \(\binom{p_j}{2}\) rootless quadratics and \(p_j\binom{p_j}{2}-\binom{p_j}{3}\) rootless cubics. Their products give a monic rootless \(U_{j,n}\) of every degree \(n\ge2\). Prescribe reductions
\[
 R_{ij}(X)=
 \begin{cases}
   (X-t_j)U_{j,d_i-1}(X),&i=i_j,\\
   U_{j,d_i}(X),&i\ne i_j.
 \end{cases}
\]
The only zero among all \(R_{ij}(t_k)\) for this prime is at \((i,k)=(i_j,j)\), because the cuts are distinct modulo \(p_j\). At that cut the derivative equals the nonzero \(U_{j,d_i-1}(t_j)\).

Write \(M=2^{r-1}(r-1)!\) and \(T=4MK^2\). Then \(P'(t_k)=(-1)^{r-1-k}2^{r-1}k!(r-1-k)!\) divides \(M\), and \((4M,K)=1\). Choose an integer norm \(n_{ik}\equiv 2\pmod{4M}\) and prescribe it at each \(p_j^2\) as follows. Use the least positive representative of \(R_{ij}(t_k)\bmod p_j\) if it is nonzero, and use \(p_j\bmod p_j^2\) if it is zero. The Chinese remainder theorem gives one class \(a\bmod T\), represented by \(1\le a\le T\). The forced factor \(g\) of any member of this class is \(2p_k\) if \(i=i_k\) and \(2\) otherwise. With \(q=T/g\), the quotient progression \(a/g+qz\) has a unit residue modulo \(q\), and every prime of \(g\) divides \(q\).

There is a squarefree quotient among \(0\le z<32q\). Indeed the quotients are at most \(32q^2\), and primes dividing \(q\) divide none of them. A prime \(p\nmid q\) excludes at most \(32q/p^2+1\) indices by its square. Summing over \(p\le\sqrt{32}\,q\) excludes fewer than \(30q\) indices, since \(\sum_{n\ge2}n^{-2}\le 1/4+\int_2^\infty x^{-2}\,dx=3/4\). Choose the first squarefree quotient by trial division. The resulting \(n_{ik}\) is squarefree, positive, and at most \(32T^2\). This argument allows the remaining prime factors of the marked norms to vary with the mark.

Write \(n_{ik}=2+4Mz_{ik}\) and interpolate by the integral polynomial
\[
 C_i(X)=2+4\sum_k z_{ik}\frac{M}{P'(t_k)}\frac{P(X)}{X-t_k}.
\]
It has degree less than \(r\), satisfies \(C_i(t_k)=n_{ik}\), and reduces to the constant two modulo four. Each quotient \((R_{ij}-C_i)/P\bmod p_j\) exists by the vanishing at all distinct cuts, and is monic of degree \(h+i-1\). Let \(Q_i^0\) be the monic polynomial of that degree obtained by taking its lower coefficients from these quotients by CRT, also prescribing them even modulo two. Use representatives in \([0,2K)\).

Choose \(S_i\) by taking the least nonnegative residue of
\[
       -\frac{C_i(m)+P(m)Q_i^0(m)}{2KP(m)}\pmod N
\]
and expanding it in base \(m\), with the last quotient placed at degree \(h-1\). The denominator is a unit. Since \(m^h\le N<(m+2)^h\) and \(m\gg h\), the final quotient is \(O(m)\). For \(s=0,1,2\) use
\[
 F_{i,s}=C_i+P\bigl(Q_i^0+2KS_i+4Ks(X-m)\bigr).
\]
These polynomials preserve the marked norms and the reductions \(R_{ij}\), and their values at \(m\) are zero modulo \(N\). They are monic of degrees \(d_i\). Modulo two, \(P=X^r\) and the quotient multiplying it is \(X^{h+i-1}\). Their constant terms are \(2\bmod4\), since \(P(0)=0\) and \(C_i(0)=n_{i0}\). Thus they are Eisenstein at two and give fields of distinct degrees. The derivative at \(m\) changes by \(4KsP(m)\) from the \(s=0\) value. For each field, at most one shift gives zero modulo \(N\), because the differences of shifts and \(4KP(m)\) are units. A proper derivative gcd yields a factor. Otherwise some common shift has both derivatives units, giving the simple common root and the [integral reductions at that root](cogentic-monic-index.md).

Here \(\log T=O(r\log h)\) and the coefficient bounds from interpolation and the digit construction give \(\log\|F_{i,s}\|_\infty\le\log m+O(r\log h)\). Polynomial and CRT operations have polynomial bit cost, except for finding the squarefree representatives. Even testing each of the \(32q\) candidates by trial division through \(\sqrt{32}\,q\) costs only \(\exp(O(r\log h))\operatorname{poly}(\log N)\). Thus one can specify the simultaneous smoothness bound \(B=32T^2\). These are ordinary \(B\)-smooth norms, including the forced prime two. A sieve demanding primes strictly above \(\sqrt B\) would need a different construction.

## What the rows certify

Let \(\alpha_i\) be a root of the chosen \(F_{i,s}\). The monic norm identity gives \(\lvert\operatorname{Norm}(t_k-\alpha_i)\rvert=n_{ik}\). At \(p_j\) there is exactly one occurrence among these norms, with valuation one at \((i_j,j)\). In the maximal order, the ideal norm formula forces precisely one prime of residue degree one with valuation one in \((t_j-\alpha_{i_j})\). All other columns have zero valuation there. The prescribed simple root also identifies this row in the power-order root description. The selected joint rows therefore give the identity matrix over both \(\mathbb Z\) and \(\mathbb F_2\).

All \(t_j-\alpha_i\) have unit reduction modulo \(N\). For another unit-residue relation column with vector \(w\in\mathbb Z^r\) in the selected rows, multiply its element pair by the planted pairs to exponents \(-w_j\), in the localization at unit residues. This removes all selected coordinates while preserving equality of the two modular reductions. Other valuations can change. On the planted columns alone, a simultaneous square requires every mark exponent even, since each selected row reads one exponent. Their canonical half-products have equal reductions and yield no proper difference gcd. This finite block has rank \(r\), and the other prime and archimedean rows required for an order certificate remain to be supplied. [Rank requirements for order extraction](cogentic-two-thirds-extraction-audit.md)

## A support barrier for preserving the variable-multiple output law

In the [variable-multiple pair](cogentic-variable-multiple-lattice.md), put \(L=\log N\), \(D=(L/\log L)^{1/3}\), \(H=D\log L\), and \(V=DH\). Use its fixed strict schedule, so \(d\sim xD\), \(e=d-1\), \(\log A\sim cH\), \(\log W=(1/x+o(1))V\), and write \(S=1/x+xc\). At any retained Farey mark \((a,b_v)\), the lattice projection \(H_i\mapsto H_i(a,b_v)\) has image \(\mathbb Z\). Its Gaussian mass at any integer is at most \(O(1/(W b_v^e))\) by the one-mark Poisson estimate. The continuous evaluation row has norm at least \(b_v^e\), the image covolume is one, and the Poisson errors are uniform in the marked value. At that mark the two field outputs are independent under the original sampling law. The affine conversion to polynomial values preserves the bound, and taking absolute values costs at most a factor four for the pair. Hence the largest atom of the joint norm law is at most \(\exp((-2S+o(1))V)\), uniformly in the input and the admissible target prime.

A deterministic list of \(J\) candidate pairs, even with arbitrary weights and \(t\) additional fair coefficient bits per entry, induces a law supported on at most \(J2^t\) joint marked outputs. If its statistical distance from the original output law is at most a fixed \(\eta<1\), then
\[
   J2^t\exp((-2S+o(1))V)\ge 1-\eta.
\]
This follows by testing the support of the proposed law. The exponent is sharp for the one-mark output law. Both original perturbation evaluations lie within \(L^{O(1)} Wb_v^e\) of zero with probability \(1-o(1)\), by the coefficient tail bound and the bounded slopes. Restricting to this box gives a law on at most \(\exp((2S+o(1))V)\) atoms within \(o(1)\) statistical distance, with each retained pair of atoms realizable by a pair of lattice perturbations. This is a support statement and gives no efficient method to compute those weights and lifts. In particular a list of size \(\exp(O(H))\) with \(O(H)\) residual bits cannot preserve even this single-mark law. Preserving specific smoothness moments or obtaining a certified rank does not require statistical distance on all norm events. The planted pair guarantees its private rows directly.

The [exact replay](../experiments/cogentic-short-field-list.py) verifies five polynomial pairs, two preliminary divisor branches, and ten private rows. It checks the full affine root set at each selected prime and factors every planted norm by trial division.
