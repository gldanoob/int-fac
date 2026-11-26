# Private norm primes on raw radix grids

For each fixed \(0<c<(1+\sqrt{13})/6=0.76759\ldots\), there are infinitely many odd composite inputs \(N\) for which the automatic [raw monic pair](cogentic-monic-pair.md) gives only trivial signs from simultaneous squares of primitive marks of height at most \(\exp(cW)\), where \(W=(\log N)^{1/3}(\log\log N)^{2/3}\). The conclusion includes negative exponents and shared signs. For \(c<1/2\) it also includes nonprimitive marks. For any fixed \(C\), the inputs can be chosen with at least three distinct prime factors, two of exponent one, and with no prime factor at most \(\exp(CW)\). Both derivatives and all mark reductions are units modulo \(N\). The same grid obstruction holds on a proportion tending to one of balanced semiprimes.

The pair count alone gives \(c<1/2\). Counting an anchor and the distinct neighbors of several of its large primes gives the stated range. The argument concerns the raw pair and ordinary marks. Other fields and independent unit corrections may supply additional relations. [Earlier obstruction from an affine progression of bases](cogentic-private-grid-density.md)

## A product of radix digit intervals

Take an arbitrarily large odd prime \(d\). Let \(j\) be the least positive integer with \(2^j/j>d^3\), set \(M=2^{d^2j}\), \(L_0=d\log M\), and use \(W_0=L_0^{1/3}(\log L_0)^{2/3}\) and \(V_0=L_0^{2/3}(\log L_0)^{1/3}\). Put \(H=\lfloor e^{cW_0}\rfloor\). Use all primitive marks \(v=(a_v,b_v)\) with \(|a_v|\le H\) and \(1\le b_v\le H\). The height of \(v\) is \(h_v=\max(|a_v|,b_v)\), and its logarithmic height is \(x_v=\log h_v/W_0\).

Fix \(C_0>\max(C,2c)\), put \(Z=\lceil e^{C_0W_0}\rceil\), and take distinct primes \(p_1,p_2\in(Z,4Z)\), using Bertrand's postulate on successive dyadic intervals. Set \(P=p_1^2p_2^2\). Fix an odd integer
\[
 m\in[(1-1/(4d))M,(1-1/(8d))M]
\]
whose residue avoids all the mark slopes modulo each \(p_i\). Each prime exceeds \(2H^2+H+1\) for large \(d\), so an allowed residue exists, and the interval contains representatives by CRT. Consider independent uniform digits \(c_0,\ldots,c_{d-2}\) in their respective residue classes modulo \(2P\) in \([1,m-1]\). Choose the residues so
\[
 N=m^d+2\sum_{i=0}^{d-2}c_i m^i,\qquad
 F=X^d+2\sum_{i=0}^{d-2}c_i X^i,\qquad G=F+(X-m)X^d
\]
have \(c_0\) odd, \(v_{p_i}(N)=1\), and \(F'(m),G'(m)\) nonzero modulo both \(p_i\). First choose \(c_1\bmod p_i\) to avoid at most two residues for the derivatives. After fixing all residues other than \(c_0\), select \(c_0\bmod p_i^2\) by the unit coefficient 2 in \(N\). Every interval of free digit indices has length \(J=(1+o(1))m/(2P)\).

Since \(0<N-m^d<2m^{d-1}\), the raw base is \(m\), and the odd first digit makes these the raw digits with top digit zero. The base interval gives \(N\) bit length \(d^3j\) and \(\log N<L_0\), so the automatic degree is \(d\) and the grid contains the claimed height. Also \(\log m=(1+o(1))V_0\), \(dW_0\sim V_0\) and \(\log d\sim(\log L_0)/3\). Both fields are Eisenstein at two. [Degree schedule](cogentic-monic-productive-signs.md#fitting-the-congruences-into-the-degree-schedule)

Conditional on the other digits, excluding each odd prime \(\ell\le Z\) from \(N\) removes one class of the constant-digit index modulo \(\ell\). The reciprocal prime sum is \(O(\log\log Z)=O(\log d)\). Odd Bonferroni truncation at \(O(\log d)\), with one rounding error per CRT class and total error \(Z^{O(\log d)}=o(Jd^{-B})\) for each fixed \(B\), leaves a fraction \(d^{-O(1)}\) with no prime divisor through \(Z\). This follows by taking the truncation more than 20 times the reciprocal sum plus one. The tail of the density product is smaller than half that product by the factorial bound. Conditional on the other digits, the remaining candidates for a prime dividing \(N\) and a derivative or a mark reduction belong to
\[
 |F'(m)G'(m)|\prod_v |a_v-b_vm|.
\]
This is nonzero since the digits and \(m\) are positive and \(m>H\). Neither prescribed prime is a candidate by construction. There are at most \(\exp((2c+o(1))W_0)\) candidate primes, by the bit lengths of the factors. Each candidate above \(Z\) costs at most \(1/Z+1/J\) in probability over the constant digit. The resulting loss is \(\exp(-\Omega(W_0))\), leaving a fraction \(d^{-O(1)}\) of the box with the required roughness and units. The cofactor \(N/(p_1p_2)>1\) is coprime to \(p_1p_2\). [Bonferroni estimate](cogentic-monic-productive-signs.md#excluding-the-remaining-small-prime-factors)

## Independent perturbations at finitely many marks

Write \(n_v=b_v^{d+1}G(a_v/b_v)\). Take any distinct marks \(v_1,\ldots,v_k\), with \(k\) fixed. Homogenize the free digit polynomial to degree \(d-2\), and work in digit indices, so an increment of one in an index changes its digit by \(2P\). For each \(v_i\) add to the index polynomial the homogeneous perturbation
\[
 T_i(X,Y)\prod_{j\ne i}(b_{v_j}X-a_{v_j}Y),
\]
where \(T_i\) has degree \(s=d-1-k\) and independent coefficients uniform in \([0,R-1]\), with \(R=\lfloor J/(k d^2(2H)^{k-1})\rfloor\). Each coordinate of the sum of perturbations has magnitude at most \(J/d^2\), by the coefficient sum bound \((2H)^{k-1}\) for each product of linear forms. Sample the central indices uniformly from their original intervals padded by \(\lceil J/d^2\rceil\) on each side. For every fixed perturbation, the probability of any original tuple under the padded law is the reciprocal of its padded box size. Consequently the original probability of any event is at most \(e^{O(1/d)}\) times its probability in the padded and perturbed model, including events about simultaneous divisibility.

Conditional on the center, the resulting \(n_{v_i}\) are independent. At \(v=v_i\) the evaluation has the form
\[
 B+\delta T_i(a_v,b_v),\qquad
 \delta=4P b_v^3\prod_{j\ne i}(a_v b_{v_j}-a_{v_j}b_v)\ne0 .
\]
Here \(B\) is the central norm, and the power \(b_v^3\) converts the digit polynomial of degree \(d-2\) to the norm form of degree \(d+1\). Put \(g=\gcd(B,\delta)>0\) and \(K=R h_v^s\). The normalized integer \(n_v/g\) varies in an interval of length \(O(dK|\delta|/g)\), in a single class modulo \(|\delta|/g\), and has maximum absolute value
\[
 X\ll dm h_v^{d+1}=K\exp(O_k(W_0)).
\]
Every nonzero determinant used here is bounded by \(2H^2\). The same bound on \(X\) holds when the padded center lies outside the original digit intervals.

The probability of any one normalized integer is \(O(1/K)\). In fact, if \(h_v=b_v>1\), partition the coefficient ranges of the \(s\) monomials other than \(Y^s\) into blocks of length \(b_v\). Within a full block in each index, their combined evaluation runs once through every class modulo \(b_v^s\). Reduce successively modulo \(b_v,b_v^2,\ldots,b_v^s\), using invertibility of \(a_v\) modulo \(b_v\). Then the remaining coefficient of \(Y^s\) takes at most one value at a prescribed evaluation. Bounding the trailing blocks by full blocks gives an atom bound \(\lceil R/b_v\rceil^s/R^{s+1}=O(1/K)\), since \(sH/R=o(1)\). If \(h_v=|a_v|>1\), interchange the roles of \(X\) and \(Y\). If \(h_v=1\), a coefficient multiplying a unit monomial suffices. Also, a given divisor \(u>0\) of the normalized value must be coprime to \(\delta/g\), since the start \(B/g\) is coprime to the step. In that case the interval and atom bounds give
\[
 \Pr[u\mid n_v/g\mid\text{center}]\ll d/u+1/K.
\]

## Counting marks with few large odd valuations

Fix an integer \(r\ge1\) and a positive cutoff \(z\) bounded away from zero. Let \(B_r(z)\) be the marks with no prime of odd \(n_v\)-valuation above \(2H^2\) and with fewer than \(r\) such primes in \((Y,2H^2]\), where \(Y=e^{zW_0}\). Conditional on any center above, uniformly in the \(k\) fixed marks,
\[
 \Pr[v\in B_r(z)\mid\text{center}]
 \le \exp\left(-\left(\frac{1+x_v}{3z}+o(1)\right)W_0\right). \tag{1}
\]
To verify this, allow all prime factors of \(\delta\) as exceptions when passing from \(n_v\) to \(n_v/g\), since division by \(g\) can flip parity there. The normalized value then has the form \(u t^2\) in absolute value, where all prime factors of \(u\) are either at most \(Y\), among the fixed exceptions dividing \(\delta\), or among at most \(r-1\) further distinct primes in \((Y,2H^2]\). Each allowed prime is at most \(Q=\exp(O_k(W_0))\), using the fixed \(C_0\). This formulation allows prime powers at the additional primes.

For \(\kappa=d^{-1/2}\), the fraction of zero or normalized values of magnitude at most \(K^{1-\kappa/2}\) is \(O(K^{-\kappa/2})\) by the atom bound. For larger values with \(u<K^{1-\kappa}\), sum the divisor bound over \(K^{\kappa/4}<t\le\sqrt X\) with divisor \(t^2\). This costs \(O(dK^{-\kappa/4}+\sqrt X/K)\). Otherwise \(u\) has a divisor of the allowed shape in \([K^{1-\kappa}/Q,K^{1-\kappa}]\). The atom error \(1/K\) over all such integers costs at most \(K^{-\kappa}\).

For the reciprocal divisor sum, take \(\lambda=\log d/\log Y\). Rankin's inequality puts the factor \((K^{1-\kappa}/Q)^{-\lambda}\) in front of the Euler product for primes through \(Y\), the factors for fixed exceptions, and the sum over the extra primes. The elementary prime-counting upper bound \(\pi(t)\ll t/\log t\) and partial summation give
\[
 \log\prod_{p\le Y}(1-p^{-1+\lambda})^{-1}
 \ll\log\log Y+\frac{e^{\lambda\log Y}}{\lambda\log Y}=O(d).
\]
The \(O_k(1)\) fixed exceptions above \(Y\) contribute \(o(1)\) to the logarithm. The factor for the extra primes is at most
\[
 \left(1+\sum_{Y<p\le2H^2}(p^{1-\lambda}-1)^{-1}\right)^{r-1}
 =\exp(O_r(\log d)),
\]
since \(p^\lambda\le d^{O(1)}\) on this band. The remaining factors are subexponential on the \(W_0\) scale. Finally \(\log K=(1+x_v+o(1))V_0\) uniformly, so \(\lambda\log K=((1+x_v)/(3z)+o(1))W_0\). This proves (1).

## Excluding shared primes

An odd rational norm valuation at \(q\) gives an odd valuation at some prime ideal above \(q\). If the same prime ideal divides two primitive marks, it divides their nonzero integer determinant. Thus a prime ideal above \(q>2H^2\) can divide just one direction. Rational contents only have primes at most \(H\), so they cannot cancel this valuation. The direction support \(S\) of any simultaneous square, after taking primitive exponents modulo two, therefore satisfies \(S\subset B_r(z_0)\) for \(z_0=\log(2H^2)/W_0\).

Suppose \(S\subset B_r(z)\), and a mark in \(S\) has at least \(r\) distinct odd norm primes above \(e^{z'W_0}\), for \(0<z'<z\). Choose \(r\) such primes. For primitive products the shared sign has zero ideal valuations. For products with rational contents, require \(e^{z'W_0}\ge H\), so that none of the chosen primes can divide a content. In either case, an odd ideal valuation at each chosen prime must be shared by another mark in \(S\) at that same ideal. Assign a neighboring mark to each chosen prime, obtaining \(t\) distinct neighbors with \(1\le t\le r\). An assignment may use the same neighbor for several primes. For each neighbor, the number of its determinant's prime divisors above \(e^{z'W_0}\) is \(O(1)\) for fixed \(z'\) bounded away from zero. Hence there are \(O_r(1)\) choices of the primes and their assignments for a fixed anchor and list of \(t\) neighbors.

Apply the padded model to these \(t+1\) marks. At the anchor, every selected prime divides the norm perturbation step, since the step contains the determinant to its assigned neighbor. Divisibility by their product is thus a condition on the center alone. The product of the \(r\) distinct primes is at most \((2H^2)^r=o(J)\) and coprime to \(2P\). If a prime divides the anchor's denominator, the event is impossible by monicity. Otherwise each prime fixes exactly one class of the center's constant-digit index. Conditional on the other center digits, their product fixes one class by CRT. Its probability is at most \(O(1)\) divided by the product, hence \(O(e^{-rz'W_0})\). Conditional on any such center, all \(t+1\) events \(v_i\in B_r(z)\) are independent and obey (1). The bound uses just the anchor hit and the mark counts, so it also covers multiple roots, index primes and leaves having additional shared primes.

Summing (1) over the grid gives \(\exp((A(z)+o(1))W_0)\), as an upper bound, with
\[
 A(z)=\max_{0\le x\le c}\left(2x-\frac{1+x}{3z}\right).
\]
For example, group by integer height \(h\), use \(O(h)\) marks at that height, and sum \(h^{1-1/(3z)}\). When \(A(z)<0\), the one-mark union bound excludes every mark in \(B_r(z)\) with probability \(1-\exp(-\Omega(W_0))\). When \(A(z)\ge0\), the maximum in the definition of \(A(z)\) is at \(x=c\). Summing the anchored configurations for \(1\le t\le r\) costs at most
\[
 \exp\left(\big((r+1)A(z)-rz'+o(1)\big)W_0\right).
\]
Outside that exceptional event, \(S\subset B_r(z')\). For \(r=1\) this is the pair recurrence \(z'>4c-2(1+c)/(3z)\).

Set \(\theta=(r+1)/r\). If \(c^2<(1+c)/(3\theta)\), there is a positive constant gap between \(z\) and \(\theta(2c-(1+c)/(3z))\), uniformly for \(z>0\), by \(z+\theta(1+c)/(3z)\ge2\sqrt{\theta(1+c)/3}\). A constant decrement smaller than this gap moves down from \(z_0\) to a fixed positive \(z\) with \(A(z)<0\) in finitely many steps. The total exceptional probability is \(\exp(-\Omega(W_0))\), so the rough unit subset contains an input with \(S\) empty. At \(r=1\) the inequality gives \(c<1/2\), and in that range we may stop at \(z=c\), where \(A(c)<0\), allowing rational contents throughout. For each \(c<(1+\sqrt{13})/6\) a fixed finite \(r\) suffices for primitive products.

## From norm support to global signs

The argument uses rational norm parity to find an odd ideal valuation at the anchor. A common rational prime in two norms may arise from different roots. The square relation requires cancellation at the same ideal, which is what forces one of the determinants used in the count.

With all primitive exponents even, a simultaneous square is a common rational scalar times a square in each field. The scalar has square norm in the odd-degree field of \(F\), so is a rational square. Any field square root is the same signed half-product up to a single global sign. Each primitive mark and the rational content have unit evaluations modulo \(N\), and the square root of the common rational scalar is a unit there too. The two root residues therefore agree up to a single sign and give only trivial gcds. [Raw pair and residue maps](cogentic-monic-pair.md)

## Balanced semiprimes

Fix a balance ratio \(R_0>1\). On each bit-length band of \([X,2X]\), freeze the scheduled base \(m\), degree \(d\), and top radix digit \(c_{d-1}=O(d)\). Every actual input maps injectively into the full product of \(m\) choices for each lower digit, with \(c_0\) odd in \([-m,m-2]\) and the others in \([0,m)\). Split each full box into its digit parity classes. Inside each resulting box all coordinates are again spaced by two, with lengths comparable to \(m\). The padding and perturbation argument applies with \(P=1\) and \(J\) the shortest coordinate length. Padded lengths differ from the originals by a factor \(1+O(d^{-2})\) in each coordinate. The fixed top digit and sign of \(c_0\) affect only the central value \(B\), whose magnitude bound still holds. Use the even-degree member, which is \(G\) for odd \(d\) and \(F\) for even \(d\). For \(F\) the perturbation formula has \(b_v^2\) instead of \(b_v^3\), since the norm degree is \(d\), with the same monic and constant-digit congruence arguments. This gives a uniform exceptional fraction \(\exp(-\Omega(W_0))\) over the full boxes, with \(W_0\) computed from \(\log(2X)\), so their common grid covers the required height for each \(N\) in the band.

At fixed \(d\) there are \(O((2X)^{1/d}/d)\) bases and \(O(d)\) top digits, and each full low-digit box has \(m^{d-1}\) elements. The total cardinality is \(O(X)\). Parity splitting preserves this sum. The prime number theorem gives \(\gg_{R_0}X/(\log X)^2\) balanced semiprimes, so the fraction of balanced semiprimes excluded by the peeling estimate tends to zero. All their grid mark values are units since \(0<|a-bm|=o(\sqrt X)\) for a primitive mark with \(b>0\), and content primes are at most \(H\). If a derivative is a nonunit, one of the two prime factors of \(N\) divides it. With the other digits fixed, the nonzero derivatives each have \(O_{R_0}(1)\) candidate prime divisors of size comparable to \(\sqrt X\), and every such prime divides \(N\) for at most one constant digit. This loses only \(O_{R_0}(1/m)\) of each full box, which also tends to zero after comparison with the semiprime count. For even \(d\), the odd-degree field \(G\) plays the role of \(F\) in forcing the residual scalar to be a square. [Full radix box and derivative estimates](cogentic-radix-grid-density.md)
