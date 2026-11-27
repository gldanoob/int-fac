# Residue variance for bounded prime-product shapes

A bounded smoothness predicate can attain the usual leading smoothness density and have a square-root relative character bound on every value interval under Dirichlet GRH. For a large prime-power grid, this gives the desired mean-square saving when the base progression residue is averaged over a complete set of unit phases. For one prescribed residue, the resulting bound loses one more factor of the size of the base modulus. This construction controls a subset of the ordinary smooth numbers. [Fixed-modulus variance for the ordinary indicator](keybreak-endpoint-grid-variance.md)

## A disjoint union with ordinary leading density

Let \(x\) be the target product size, \(u=\log x/\log y\to\infty\), and \(y=V^{c+o(1)}\) for a fixed \(c>0\). In the top range \(\log x/\log V\asymp d\) and \(d\log\log x=o(\log V)\). Matching the leading smoothness density below also requires \(\log\log x=o(u\log u)\). In particular this holds when \(\log V=d^{O(1)}\). Put \(k=\lceil u(1+1/\log u)\rceil\), \(P=x^{1/k}\), \(H=\log(y/P)\asymp\log y/\log u\), and \(\delta=\log(1+\lambda)/(2k)\), where \(0<\lambda\le1\) and \(k\log(1/\lambda)=o(\log V)\). Take \(J=\lfloor H/(4\delta)\rfloor\) possible bin indices \(0,\ldots,J-1\). Some integer \(A\) is the sum of at least \(\binom Jk/(kJ)\) distinct \(k\)-subsets of indices. Set

\[
I_j=[P e^{\delta(j-A/k)},P e^{\delta(j+1-A/k)}),
\qquad 0\le j<J.
\]

Every bin is below \(y\) and its lower endpoint \(a_j\) is \(y^{1-o(1)}\). For each selected subset take one prime in each bin. The product of the lower endpoints is exactly \(x\) and the actual products lie in \([x,x\sqrt{1+\lambda}]\). The bins are disjoint, so each variable prime occurs once and prime factorization recovers the subset and every choice. The function recognizing the union of all such products \(\mathcal A\) is a \(0,1\) predicate. A fixed modulus \(M\le x^C\) can be excluded from the prime choices by omitting its prime divisors from each bin. The prime number theorem under RH gives \(\asymp\delta a_j/\log y\) available primes, uniformly after the exclusions. Each bin has length \(a_j V^{-o(1)}\) and contains at most \(O_C(d)\) prime divisors of \(M\).

Writing \(S=|\mathcal A|\), the number of patterns and the product of the prime counts give

\[
\frac{S}{\lambda x}\ \ge\ \frac{1}{\lambda kJ}\left(\frac{c_1}{k\log u}\right)^k
\ \gg\ \frac{1}{k^2H}\left(\frac{c_1}{k\log u}\right)^k
\ \ge\ \exp\bigl(-(1+o(1))u\log u\bigr)
\]

for a fixed \(c_1>0\). Here \(J\delta\asymp H\), \(\delta\asymp\lambda/k\), and \(J\gg k\). The last inequality uses \(\log(k^2H)=o(u\log u)\). A single pattern loses a leading prime-count factor, which the disjoint family of patterns recovers.

The ordinary smooth count gives the matching leading upper bound per unit of interval length. Harper's Smooth Numbers Result 3 with modulus 1 and interval length \(\lambda x\ge y\) bounds that density by \(\ll (\Psi(x,y)/x)\lambda^{-(1-\alpha)}\log x\). The saddle point satisfies \(1-\alpha\ll\log u/\log y\), so \((1-\alpha)\log(1/\lambda)=o(1)\). The extra factor \(\log x\) is \(\exp(o(u\log u))\) by the density hypothesis. Thus \(S=\lambda x\exp(-(1+o(1))u\log u)\) throughout the stated interval range. [Hildebrand's ordinary smooth density](https://www.sciencedirect.com/science/article/pii/0022314X86900132) · [Harper, §2.1](https://arxiv.org/pdf/1408.1662#page=13)

The growth condition accounts for the cost of retaining just one index sum. Every \((k-1)\)-subset extends to at most one \(k\)-subset of sum \(A\), and each valid \(k\)-subset has \(k\) deletions. Hence the number of patterns is at most \(\binom J{k-1}/k\le J^{k-1}/k!\). The upper prime-count bound in each bin then gives \(S/x\ll J^{-1}(C_1/\log u)^k/k!\) for a fixed \(C_1>0\). For example, take \(d=u\to\infty\), \(\log V=e^{u^2}\), \(y=V\), \(x=y^u\), and \(\lambda=1\). These scales satisfy \(d\log\log x=o(\log V)\) but give \(\log J=u^2+O(\log u)\). The shape density is at most \(\exp(-u^2-u\log u+O(u\log\log u))\), whereas the ordinary smooth density is \(\exp(-(1+o(1))u\log u)\). The character and variance bounds below are relative to the actual shape mass and need only \(d\log\log x=o(\log V)\) and the bound on \(\lambda\).

## Character bounds with value cutoffs

For any nonprincipal \(\chi\bmod M\), \(M\le x^C\), the Dirichlet GRH estimate

\[
\sum_{p\le z}\chi(p)p^{it}\ll \sqrt z\,(\log x)^{C_2}
\]

holds at the bin endpoints and throughout the bins for every \(|t|\le x^{C_3}\), with the modulus and height exponents fixed. To see the uniformity in \(t\), apply truncated Perron to \(-L'/L(s-it,\chi)\) first for the coefficients \(\Lambda(n)\chi(n)n^{it}\). Use half-integer endpoints, polynomial truncation height \(T_1>|t|+x^2\), and shift to \(\Re s=1/2+1/\log z\). The partial-fraction formula and the bound \(O(\log(M(2+|\Im s-t|)))\) for the number of nearby zeros give an \(O((\log x)^2)\) bound on the logarithmic derivative along the shifted contour, since the distance to every nontrivial zero is at least \(1/\log z\). A primitive nonprincipal character has no pole in the shifted region. The horizontal and truncation errors are \(O(z(\log x)^2/T_1)\). Prime powers cost \(O(\sqrt z(\log x)^2)\), and passing from an imprimitive character to its primitive inducer costs at most \(O(\omega(M)\log z)\) in the Mangoldt sum. Partial summation by \(1/\log p\) gives the claimed prime sum with the oscillatory weight already included. [Logarithmic derivative and zero counts](https://ndl.ethernet.edu.et/bitstream/123456789/23715/1/Hugh%20L.%20Montgomery.pdf) · [Truncated Dirichlet explicit formula](https://doi.org/10.1007/s00208-026-03383-y)

Consequently for \(s=1/\log x+it\), \(|t|\le x^3\), each pattern has

\[
\left|\prod_{j}\sum_{p\in I_j,\ p\nmid M}\chi(p)p^{-s}\right|
\le S_{\rm pattern}\,x^{-1/2}
      \exp\bigl(O(k\log\log x+k\log(1/\delta))\bigr).
\]

The real weight \(p^{-1/\log x}\) is inserted by partial summation with bounded variation. The factors \(a_j^{-1/2}\) from the normalized prime bounds multiply to \(x^{-1/2}\). The loss is \(V^{o(1)}\) under the hypotheses on \(d\) and \(\lambda\). Summing over the disjoint patterns replaces \(S_{\rm pattern}\) by \(S\). A second truncated Perron integral inserts a prefix cutoff on the product, with \(\int |ds/s|\ll\log x\). A half-integer endpoint and height \(x^3\) give truncation error \(O(Sx^{-2})\), since the active integer products are comparable to \(x\); endpoints outside the product interval give either an empty prefix or the full sum. Thus every interval character sum is \(O(Sx^{-1/2}V^{o(1)})\), with respect to the full shape mass even for a small interval.

## Averaged and prescribed progression phases

Write \(M=mB\) with \(B=b^h\) for a prime \(b\) coprime to \(m\). Count shape integers in unit classes \((r,a)\bmod (m,B)\) and let \(S_{r,a}(I)\) be the count in a value interval \(I\), with \(S_r(I)=\sum_a S_{r,a}(I)\). Orthogonality on the unit group of \(M\) gives

\[
\sum_{r,a}^{*}\left|S_{r,a}(I)-\frac{|\mathcal A\cap I|}{\phi(mB)}\right|^2
\ll S^2x^{-1}V^{o(1)}.
\]

Centering each row by \(S_r(I)/\phi(B)\) is an orthogonal projection and reduces the left side. The same estimate for the full value interval modulo \(m\), using the pointwise character bound or character orthogonality, gives \(S_r=S/\phi(m)+O(Sx^{-1/2}V^{o(1)})\) uniformly. Thus the full shape density is uniform on these unit phases at leading order for \(m=V^{O(1)}\).

Index phase \(r\bmod m\) by \(n=r+mv\). The map \(v\bmod B\mapsto n\bmod B\) is a bijection. The additive transform of the within-row-centered residue counts has squared norm \(B\) times their squared residue norm. This square bound holds even with a supremum over intervals inside each nonzero additive coefficient. To see this, apply the within-row projection and additive transform first to the Mellin-weighted residue vector. Its \(\ell^2(r,\text{frequency})\) norm is at most \(\sqrt B Sx^{-1/2}V^{o(1)}\) for every \(s\) on the product Perron contour. Take the prefix supremum inside \(\int |ds/s|\), then use Minkowski in \(\ell^2\). The error in entry \((r,a)\) before projection is at most \(O(x^{-2}S_{r,a})\) pointwise in the cutoff, with \(S_{r,a}\) counted over the full band. The row sum of absolute errors, including the centering, is \(O(x^{-2}S_r)\). This bound holds for each additive coefficient in the row and gives \(O(\sqrt B S x^{-2})\) in \(\ell^2\) after taking coordinatewise suprema. Differences recover all interval endpoints.

Put \(K=x/m\) and use the deterministic phase-density reference \(\rho_m=S/(\phi(m)K)\). After normalizing additive sums by \(K\), the mean over all \(\phi(m)\) unit phases of their centered squared Fourier sums, relative to \(\rho_m^2\), is therefore

\[
\ll \frac{\phi(m)B}{x} V^{o(1)}
\ \le\ \frac{mB}{x} V^{o(1)} .
\]

For a single prescribed \(r\), positivity gives the same upper bound multiplied by \(\phi(m)\). For a subset of \(A_0\) unit phases with uniform weights, it gives a loss \(\phi(m)/A_0\). The uniform estimate on \(S_r\) is a first-moment statement and does not remove those factors. The subtracted flat unit profile can be restored in the additive probe with relative squared cost \(O(1/b)\), also with the interval supremum: its coefficients are fixed Ramanujan sums up to a phase, and its total mass is at most \(S_r\). In particular, for \(mB/x\le V^{-(1-\epsilon)+o(1)}\), complete unit-phase averaging suffices at any fixed \(\epsilon<1\). A family of prescribed or correlated phases needs its own comparison with that average. For a localized shape in a much shorter band the same relative Fourier-energy bound uses its own mass as reference; an absolute normalization by the actual progression length of that band instead of \(x/m\) must use the corresponding phase density as well.

## Nonunit phases and repeated factors

For a predetermined residue \(r\bmod m\), put \(g=(r,m)\). A nonsmooth \(g\) excludes any ordinary smooth value. If \(g\) is smooth, one option is to use a shape on the cofactor \(n/g\), at size \(x/g\), with modulus \((m/g)B\) and a unit phase modulo \(m/g\). The preceding averaged bound on that gcd stratum has the same ratio \((m/g)B/(x/g)=mB/x\). Known prime powers in \(g\) are permitted and all variable primes are distinct. Taking these cofactor predicates on the disjoint strata gives a bounded predicate, though it depends on \(m\).

Alternatively, for the original modulus-independent squarefree prime-box predicate, a nonsquarefree forced \(g\) gives no mass. A contributing \(g\) has its prime factors in distinct occupied bins and therefore fixes those choices in any pattern. With \(m=V^{O(1)}\) and every bin at \(y^{1-o(1)}\), at most \(O(1)\) choices are fixed this way. The remaining tuples still satisfy the character and variance estimates relative to their surviving total mass, at size comparable to \(x/g\); the notes above make no density claim for every such stratum. For the unit stratum, removing primes dividing any individual \(M\le x^C\) loses a vanishing fraction of choices, so the modulus-independent predicate has the stated leading density there.
