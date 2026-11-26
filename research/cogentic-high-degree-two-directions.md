# Two wide mark directions with an exact small evaluation lattice

On the fixed Cogentic schedule, two translated high-degree coefficient directions give two-mark widths $\exp((50001+o(1))V)$. Three smaller correction boxes fill the evaluation lattice to total variation $e^{-CH}$ for any fixed $C$, including after prescribed small coefficient congruences. The comparable physical widths permit a deterministic two-mark count using scalar smooth-window estimates. The count keeps the correcting coordinates averaged. [Fixed schedule](cogentic-deterministic-two-thirds.md#fixed-parameters) · [Original wide-cofactor calculation](cogentic-wide-cofactor-determinant.md)

## The exact image of polynomial perturbations

Take $g=P_0\ell$, $m=\lceil N^{1/d}\rceil$ and the base-$m$ digit polynomial $R$ of $N$. For large inputs let $r=d-3\ge2$ and put
\[
 f(X)=f^{(0)}(X)+g\left[kR(X)+(m-X)\bigl(x+Xy+u(A+X)^r+v(A+X)^{r+1}\bigr)\right].
\]
For distinct integers $1\le a_1<a_2\le A$, set $\Delta=a_2-a_1$, $n_i=m-a_i$, $b_i=A+a_i$ and $R_i=R(a_i)$. Assume $\gcd(N,n_i)=1$. Remove the base values and the factor $g$ from the evaluation coordinates. Write $\mathbf R$, $\mathbf n$, and $\mathbf{an}$ for the columns with entries $R_i$, $n_i$, and $a_i n_i$. All integer-polynomial columns lie in
\[
 L=\{(z_1,z_2)\in\mathbb Z^2:z_2\equiv z_1\pmod\Delta\}.
\]
The first three columns generate $L$ exactly. In fact $J=n_1R_2-n_2R_1=\Delta B_0$, with
\[
 B_0=R_1+n_1\frac{R_2-R_1}{\Delta}=R_2+n_2\frac{R_2-R_1}{\Delta}.
\]
The quotients in these formulas are integers. Since $R_i\equiv N\pmod{n_i}$, one has $\gcd(B_0,n_1n_2)=1$. The minor on $\mathbf n,\mathbf{an}$ is $n_1n_2\Delta$. The gcd of these two minors is $\Delta$, and every minor is divisible by $\Delta$ since each column belongs to $L$. This proves the index and the exact image. The first Smith invariant is one because $R_1$ and $n_1$ are coprime. Thus the Smith invariants are $1,\Delta$. Restricting every coefficient to a fixed residue modulo $M$ replaces $L$ by an explicitly translated copy of $ML$.

## Width and geometry of the two large directions

Let $D$ be the two-column matrix with rows $n_i b_i^r(1,b_i)$. Its determinant is $n_1n_2 b_1^r b_2^r\Delta$. The translated powers ensure $A<b_i\le2A$ for every $a_i\in[1,A]$, including marks near zero. Also $m/2<n_i<m$. These bounds give
\[
 \log |\det D|=(20002+o(1))V,\qquad
 \sigma_{\min}(D),\sigma_{\max}(D)=mA^r\exp(O(H)).
\]
Here the latter notation bounds either singular value above and below by the same reference times $e^{\pm O(H)}$. For the lower bound divide the determinant by the upper bound $O(m(2A)^{r+1})$ on the larger singular value. Indeed $2^r=e^{O(H)}$ and $1\le\Delta\le A=e^{O(H)}$. Thus for high-coordinate lengths $T=\lceil e^{40000V}\rceil$, the two singular widths and every projected marginal width have leading logarithm $50001V$. The ratio of the singular widths is $e^{O(H)}$. Untranslated powers would give the same leading widths on the official $a_i/A\ge1/(4d)$ grid only, since lowering $a_i$ to 1 would lose the factor $A^r$. The translated directions use no deletion of grid marks. [Nominal grid, Cogentic §8.2](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=39)

## Uniform distribution on the full lattice in the parallelogram

Take independent uniform integer intervals of lengths $T,T$ for $u,v$, and lengths
\[
 K=\lceil m^2 e^{C_1H}\rceil,\qquad X_0=Y_0=\lceil(2A)^{r+2} e^{C_1H}\rceil
\]
for $k,x,y$. Choose $C_1$ sufficiently large for the requested precision and congruence moduli. Write $L_h=D\mathbb Z^2\subset L$. Every class of $L/L_h$ has a representative $k\mathbf R+x\mathbf n+y\mathbf{an}$ with
\[
 0\le k<n_1n_2,\qquad |x|,|y|=O((2A)^{r+2}).
\]
To see this, first use the exact image above. The vector $n_1n_2\mathbf R$ lies in $\langle\mathbf n,\mathbf{an}\rangle$: after dividing the $i$th entry by $n_i$, the entries are $n_2R_1,n_1R_2$ and their difference is divisible by $\Delta$. This permits reduction of $k$ modulo $n_1n_2$. Subtract the reduced $k\mathbf R$ and divide the remaining two entries by $n_i$. The resulting vector has integer entries congruent modulo $\Delta$. Reduce it by the high basis with rows $b_i^r(1,b_i)$, by flooring both real basis coordinates. The remaining integers are still congruent modulo $\Delta$ and have sizes at most $(2A)^r+(2A)^{r+1}$. Interpolating the remaining vector as $x+a_i y$ yields $|y|\le 4(2A)^{r+1}/\Delta$ and $|x|\le 6(2A)^{r+2}/\Delta$.

Translate the correction box by any one of these representatives in coefficient coordinates. Its total variation from the untranslated uniform box is at most $O(m^2/K+(2A)^{r+2}/X_0+(2A)^{r+2}/Y_0)$. Average this bound over all classes of $L/L_h$. Translating by a uniform class makes any law on the quotient exactly uniform. Thus the law of the correcting class is $O(e^{-C_1H})$ from uniform. This argument uses no iteration over the quotient, whose index $n_1n_2 b_1^r b_2^r$ has leading logarithm $20002V$.

Subtract translated interval origins first. Then every correction value vector $q=k\mathbf R+x\mathbf n+y\mathbf{an}$ has norm at most $\exp((10003+o(1))V)$, using $|R_i|\le dm A^{d-1}$. For each fixed $q$, consider the half-open parallelogram $P=D[0,T)^2$. It contains exactly $T^2$ points of the coset $q+L_h$, since their high coordinates have a fixed fractional part. The actual shifted high box has the same fractional parts, and its high-coordinate integer indices differ by a translation of size $O(1+\|D^{-1}\|\|q\|)$. The total variation between the two within-coset laws is at most $O((1+\|D^{-1}\|\|q\|)/T)=e^{-\Omega(V)}$. Combining with the class bound proves that the marked pair is within $O(e^{-C_1H})+e^{-\Omega(V)}$ of uniform on $L\cap P$, translated by the original mark values and interval origins and then scaled by $g$.

After any fixed coefficient class modulo $M=e^{O(H)}$, use the same proof with $MD$ and $ML$. The independent coefficient intervals have lengths divided by $M$ up to one. For unequal high lengths $T_1,T_2$, take $P=MD([0,T_1)\times[0,T_2))$, so each conditional lattice coset contributes exactly $T_1T_2$ points. The translated physical widths retain leading logarithm $50001V$. The correction quotient after scaling is the same abstract finite group, and the coupling error gains at most an $O(M)$ factor. Taking $C_1$ sufficiently large gives the claimed $e^{-CH}$ error in every class. The actual cofactor is $k_*(k)=k_0+gk$, with the uniform integer law on the given $k$ interval or its specified progression. The approximation concerns the marginal of the marked pair for that law. It does not preserve dependence on the full cofactor after replacing the marginal by a lattice law.

## Root, coefficient and residue checks

For these height bounds use the master boxes starting at zero, or shifts with endpoint magnitudes bounded by a constant times the respective master lengths and $k\ge0$. All added terms have degree at most $d-1$. They preserve the leading coefficient, the entire polynomial reduction modulo $g$, and $f(m)=N(k_0+gk)$. In the indicated cofactor box $k_*$ remains positive and coprime to $g$ with $\log k_*=O(V)$. The fixed leading coefficient has $\log c_d=(90001+o(1))V$, and the perturbation coefficient 1-norm is at most $\exp((50001+o(1))V)$. For the high terms use $(m+1)(A+1)^{r+1}$ as a bound on the unscaled coefficient 1-norm. On $|X|\le A$ use instead $(m+A)(2A)^{r+1}$. These bounds and the smaller corrections show that the entire perturbation on this interval is at most $\exp((50001+o(1))V)=o(X_{\rm sc}/K_1)$. The field polynomials stay primitive because every prime dividing $c_d$ divides $g$ and the reduction of $f^{(0)}$ there is unchanged. They retain their irreducibility test modulo 2 and their real-root brackets and fixed mark signs on the nominal grid. The mark-height leading logarithm remains $100001V$. [Root and coefficient margins](cogentic-deterministic-two-thirds.md#the-grid-its-sieve-and-its-real-roots)

The protected first-field roots and their nonzero derivatives modulo $\ell$ are unchanged. Their marked values can be divided by $\ell$ before testing the residual band, deleting $\ell$ to insist on valuation one. All moves in that coordinate are divisible by $\ell$, since $g$ is. The second field retains its absence of roots modulo $\ell$. The identity $f(a)\equiv k_*N\pmod{n_a}$ continues to hold. For a squarefree band norm at a unit mark, admitting only band primes coprime to $n_a$ is equivalent to the same smoothness condition together with $\gcd(k_*,n_a)=1$, including the protected division since $n_a$ is coprime to $\ell$ there. Fixed row congruences at a bounded number of band primes can be enforced by a union of coefficient classes modulo a common $M=e^{O(H)}$. For a known divisor on a class, divide the relevant scalar progression and its step by that divisor before deleting its primes. This preserves the progression length.

## Scalar panels and the residual search cost

In the normalized mark coordinates cover the approximate parallelogram by an axis-aligned square grid with side the largest multiple of $M\Delta$ below $e^{-C_2H}$ times its smaller singular width. The side has leading logarithm $50001V$ and the number of squares meeting the parallelogram is $e^{O(H)}$. Keep the squares entirely inside it. The boundary strip has relative area $O(e^{-C_2H})$, since the area divided by the perimeter is comparable to the smaller singular width. Each grid square contains the same number of points of the affine lattice: membership is determined by the pair of residues modulo $M\Delta$. Bounding the discarded lattice points by all those in squares meeting the boundary gives the same relative bound as the area argument. In a retained square, split into admissible residue pairs modulo $M\Delta$. Each part is a Cartesian product of two progressions with leading length $\exp((50001+o(1))V)$ and small physical moduli after reinstating $g$ and any prescribed divisions. Exact panel weights are obtained from grid point counts. A one-mark predicate can be counted by taking the second-mark predicate identically one, or by projecting the same panel law.

For a nonunit scalar residue, any prime dividing both the stride and the residue is forced. Factor the stride by trial division, possible in $e^{O(H)}$. An inadmissible forced prime or a forced square makes the count zero. Otherwise divide the entire progression by the forced product and omit its prime divisors from the band. This leaves a unit residue class and checks exact squarefreeness at those primes. Together with the protected division, all strides and forced products here are $e^{O(H)}$. The [sharp scalar window counter](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli) applies because the mark heights have leading logarithm $100001V$ and $50001>100001/2$. Thus, under Dirichlet RH, for fixed band omissions and a union of small coefficient congruence classes, the actual elementary two-mark averages are computable to $e^{-CH}$ in $e^{O(H)}$ bit operations. Use the exact probability of each coefficient class and choose the geometric, coupling and scalar precisions to absorb the requested error. General changing-cofactor score weights would require an additional transfer to such congruence terms.

Both high lengths must remain above the physical threshold for this estimator. At the stated widths the full residual coefficient tuple count is $KT^2X_0Y_0=\exp((100002+o(1))V)$ per field. The correction volume has leading logarithm $20002V$, matching the leading exponent of $[L:L_h]$. This avoids a leading exponential overcount relative to the image area, while enumeration still costs on the $V$ scale. The result evaluates elementary averages with these coordinates wide. It leaves the initial low-score argument for this distribution and the descent to a single coefficient tuple open.

An exact finite check enumerated all $441448$ quotient classes across 12 eligible mark pairs, using $(N,m,A,r)=(77,13,4,1),(91,11,3,1),(143,9,4,2)$. It checked the minor gcd, the determinant of the translated high basis, the full quotient size and the bounds and class of every reconstructed correction representative. The finite checks use integer determinants and floors and concern the lattice arithmetic.

The combined replay enumerates all 152,760 classes in six finite two-mark quotients. In each class it reconstructs the three bounded correction coefficients and checks both mark evaluations as exact integers. [Finite quotient replay](../experiments/cogentic-cofactor-dispersion.py)
