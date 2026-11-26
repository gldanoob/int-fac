# Short linear forms prescribe marked Gaussian twists

Assume Dirichlet RH. For every sufficiently large $N$ and every pair of distinct odd primes $p,q\mid N$ above a public cutoff, a polynomial-size menu of rational curves with $j=1728$ realizes either quadratic twist of $y^2=x^3-x$ at each prime. For each choice of the two twists the menu contains a rational point with different two-primary order heights at $p$ and $q$. If the odd part of the order of either twist at one prime is $B$-smooth, the menu and a public odd scalar give a proper divisor in $\widetilde O((B+1)\operatorname{poly}(\log N))$ bit operations. The two order candidates at a split Gaussian prime $p=a^2+b^2$, with $a$ odd, are $p+1\pm2a$. At an inert Gaussian prime the order is $p+1$ for both twists. [Fixed-mark Legendre construction](cogentic-fixed-marking-twists.md) · [Prescribed twists for fixed curves with full rational 2-torsion](cogentic-prescribed-elliptic-twists.md)

## Uniform colors of short linear forms

Write $L(n)\in\mathbb F_2^2$ for the two Legendre bits of an integer or rational number that is a unit at $p,q$. Fix a finite system of $k$ nonzero integer linear forms $\ell_i$ in $d_0$ variables, with pairwise nonproportional coefficient vectors. Fix a closed box $I\subset(0,1)^{d_0}$ of positive side lengths on which each $\ell_i$ takes values strictly between 0 and 1. The following choices give a public box $TI$ containing integer vectors with every prescribed pattern $(L(\ell_i(\mathbf n)))_{i=1}^k$, uniformly over distinct $p,q\mid N$ with $p,q>2T$.

- For some fixed $C$ depending only on the forms and $I$, take $T=\lceil(\log N)^C\rceil$. The proof uses a fixed small error and gives an unspecified exponent $C$.
- With the explicit $T=\lceil\exp((\log\log N)^2)\rceil$, the color averages below have error $o(1)$ for each fixed system and box. Both statements are asymptotic in $N$.

To prove the estimates, fix an accuracy $\epsilon>0$ and put $s=\max(2,k-1)$. Truncate a character $\chi\in\{\chi_p,\chi_q,\chi_p\chi_q\}$ to $[1,T]$ on $\mathbb Z/P\mathbb Z$, where $P$ is a prime between $10T$ and $20T$. Frantzikinakis–Host decompose the truncated character into a part of $U^s$ norm at most $\epsilon$ and a convolution with a kernel of mean one. The latter has at most $Q(2R+2)$ frequencies satisfying $\lvert\xi/P-r/Q\rvert\le R/P$, for constants $Q,R$ independent of the character and $T$ after the accuracy is fixed. Each Fourier coefficient of the kernel has modulus at most one. [Frantzikinakis–Host, Theorem 8.1 and the kernel in §3.3](https://arxiv.org/pdf/1403.0945#page=47)

For any residue $a\bmod Q$ and endpoint $x\le T$, set $g=\gcd(a,Q)$, write $n=gm$, and expand the remaining unit condition $m\equiv a/g\bmod Q/g$ in Dirichlet characters. This gives an average of sums of $\chi\psi$ up to $x/g$, multiplied by bounded constants. Each $\psi$ has modulus $Q/g$, and each product is nonprincipal because $p,q>2T>Q$ for large $N$. Its modulus $q_0$ lies between $2T$ and $QN$, so the full prefix range lies below $q_0$. Use $y=(\log N)^3$. For both proposed cutoffs and every $x\le T$,
\[
 y\ge (\log q_0)^2(\log(2x))^2(\log\log q_0)^{12}
\]
for sufficiently large $N$. The character sum is at most $(1+o(1))\Psi(T,y)$, by Theorem 2 and the bound $\lvert\Psi(x/g,y;\chi\psi)\rvert\le\Psi(T,y)$. This is uniform in the residue and endpoint. For the polynomial cutoff, $\Psi(T,y)/T=\rho(C/3)+o(1)$, and $\rho(C/3)$ can be made arbitrarily small by increasing the fixed $C$. For the explicit larger cutoff, this ratio tends to zero since $\log T/\log y\sim(\log\log N)/3$, still within the stated uniform Dickman range. [Granville–Soundararajan, Theorems 2 and 3.4](https://dms.umontreal.ca/~andrew/PDF/ChiSums.pdf#page=4)

Split the Fourier sum into the $Q$ progressions. On each, the phase at $r/Q$ is constant and the remaining phase has total variation $O(R)$. Summation by parts bounds each normalized Fourier coefficient of the truncated character on the kernel's support by $O_{Q,R}(\Psi(T,y)/T)$. Fourier inversion bounds the supremum norm of the structured part by the same expression, with a larger constant depending only on $Q,R$. The $U^s$ triangle inequality now gives a bound $2\epsilon$ on the full truncated character, after choosing $C$ sufficiently large or taking $N$ sufficiently large for the explicit bigger cutoff. This step uses the uniform decomposition for changing characters, including $\chi_p\chi_q$.

Choose a nonnegative product weight $W(\mathbf n)=\prod_{j=1}^{d_0}W_j(n_j)$ supported in the interior of $TI$. Take each $W_j$ to be a translated interval autocorrelation divided by the interval length, using interval lengths that are fixed positive fractions of $T$. Each weight has Fourier coefficient absolute sum one by Parseval, and $\mathbb E_{\mathbf n\bmod P}W(\mathbf n)$ is bounded below by a constant depending only on $I,d_0$. For prescribed bits $\gamma=(\gamma_p,\gamma_q)$, the exact indicator at each form on the support is
\[
 \mathbf 1_{L(n)=\gamma}
 =\tfrac14(1+(-1)^{\gamma_p}\chi_p(n))(1+(-1)^{\gamma_q}\chi_q(n)).
\]
The product of all constant terms contributes $4^{-k}\mathbb E W$. Each other term contains a nonprincipal character on at least one form. The bounded generalized von Neumann inequality bounds its unweighted torus average by the $U^s$ norm of that character. For a chosen form $\ell_i$, eliminate each other form by Cauchy–Schwarz in a direction in its kernel on which $\ell_i$ is nonzero. The resulting increments are uniform under $\ell_i$, giving the $U^{k-1}$ bound when $k\ge2$. The forms remain nonproportional modulo $P$ for large $T$. The inequality also bounds the weighted average by $2\epsilon$. To see this, expand the weights into additive phases of total coefficient absolute sum one. Each summand is a linear phase in $\mathbf n$. If its coefficient vector is in the span of the form vectors, absorb it as additive modulations of the univariate functions, which preserve their $U^s$ norms for $s\ge2$. Otherwise the torus average vanishes by averaging on the common kernel of the forms. The case $k=1$ uses the same argument with the mean bounded by $U^2$. Taking $2\epsilon<4^{-k}\mathbb E W$ gives a positive weighted count. With the explicit larger cutoff the same argument gives $4^{-k}\mathbb E W+o(1)$ uniformly for each pattern. [Green–Tao, the bounded case of Corollary B.4 and Appendix C](https://arxiv.org/pdf/math/0606088#page=55)

## Marked points on either quadratic twist

Apply the theorem to $u,v,u-v,u+v$, for example on a closed positive box with $u/T\in[1/2,5/8]$ and $v/T\in[1/8,1/4]$. Set $c=u/v$, $D=c(c-1)(c+1)$, and
\[
 E_D\colon y^2=x(x-D)(x+D),\qquad R=(Dc,D^2).
\]
Substitution gives $D^4$ on both sides. After the small-factor trial division, every prime divisor of $N$ sees $v,u,u-v,u+v$ as units and the three roots as distinct. The points and curves can be computed over $\mathbb Z/N\mathbb Z$ by public gcd checks. Trial division through $2T$ handles smaller prime factors, and exact perfect-power detection handles inputs with a single distinct prime factor.

Write $A=L(c)$, $B_-=L(c-1)$, $B_+=L(c+1)$ and $\omega=L(D)=A+B_-+B_+$. Prescribing $L(v)=0$ makes the other three form colors equal to $A,B_-,B_+$. The two square-class coordinates on $E_D$ are $x,x-D$, with the usual product of root differences at a zero. Their pair on $R$ is
\[
 (\omega+A,\ \omega+B_-).
\]
For any prescribed $\omega$ and any prescribed pair of stacked values of these coordinates, choose $A,B_-$ from the displayed equations and then set $B_+=\omega+A+B_-$. Thus both local twists and both local square-class vectors are simultaneously selectable.

At an odd prime $r$ with $D$ a unit, the two coordinates identify $E_D(\mathbb F_r)/2E_D(\mathbb F_r)$ with $\mathbb F_2^2$. The chord-and-tangent identity makes the square-class coordinates homomorphisms, and the kernel follows from the point-halving criterion. The two given squares imply the third by the curve equation, with the product-of-differences convention at torsion points. The quotient has size four because the full two-torsion is rational. For a fixed twist class, rescaling by a square does not change these coordinates, since every root and $x$ scale by that square. [Bekker–Zarhin, §2 and Theorem 2.1](https://arxiv.org/pdf/1702.02255#page=2)

Fix either twist sign at each prime and let $2^{e_p},2^{e_q}$ be the exponents of their respective two-primary subgroups. At a prime with the larger exponent, breaking a tie arbitrarily, prescribe the square-class vector of a point of maximal two-primary order. Every representative of that coset has the same maximal two-primary order, since multiplication by $2^{e_r-1}$ on the two-primary subgroup kills doubles. At the other prime prescribe the zero vector. If its subgroup has exponent $2^e$, that coset has heights at most $e-1$. The menu therefore contains a point with unequal two-primary order heights for every ordered pair of twist signs. The heights and cosets are used to prove existence. The search enumerates all menu points without knowing either prime, height or coset.

The stronger stacked rank-three condition on $R,(0,0),(D,0)$ can restrict a prescribed twist pair. Put $z=L(-1)$ and $w=L(2)$. Its torsion columns, grouped into pairs of prime bits, are $(z,z+\omega)$ and $(\omega,w)$. They must be nonzero and distinct. For example at $z=w=\omega=0$ both vanish, so no choice of the marked point gives rank three for those twists. The two-primary height argument above works for that pair as well. [Local generated-subgroup parity test](cogentic-elliptic-local-halves.md)

## Gaussian order candidates and extraction

At an odd prime $r\equiv3\pmod4$, the character sum for $y^2=x^3-D^2x$ cancels under $x\mapsto-x$, giving $r+1$ points. For $r\equiv1\pmod4$, choose a quartic character $\psi$ with square $\chi_r$, and extend both by zero at zero. Substitution $t=x^2$ in the character sum for $y^2=x^3-x$ gives
\[
 \sum_x\chi_r(x^3-x)
 =\sum_t \bigl(\psi(t)+\overline{\psi(t)}\bigr)\chi_r(1-t)
 =2\operatorname{Re} J(\psi,\chi_r).
\]
The Jacobi sum $J$ lies in $\mathbb Z[i]$ and has norm $r$, by $J(\psi,\chi_r)=G(\psi)G(\chi_r)/G(\psi\chi_r)$ and the magnitude $\sqrt r$ of each nonprincipal Gauss sum. The product identity follows by grouping the two Gauss indices by their sum. Since the curve has four rational two-torsion points, $r+1+2\operatorname{Re}J$ is divisible by four. Thus $\operatorname{Re}J$ is the signed odd coordinate $\pm a$ in $r=a^2+b^2$. Scaling $x=Dz$ multiplies the character sum by $\chi_r(D)$. This establishes the two candidates $r+1\pm2a$ and shows that the two quadratic twists exchange them. Both are covered even when only one has smooth odd part.

Enumerate the polynomial-height menu and use the odd scalar
\[
 U=\prod_{3\le\ell\le B,\ \ell\text{ prime}}\ell^{\lfloor\log_\ell(2N)\rfloor}.
\]
If the odd part of a candidate order is $B$-smooth at either prime, choose the corresponding twist in the existence argument. At that prime $[U]R$ is two-primary. If the odd component survives at the other prime, the doubling ladder reaches infinity on only the first side. If both components are killed, the differing two-primary heights still yield a one-sided infinity. Odd multiplication preserves both two-primary heights. Checked modular arithmetic through $\lceil\log_2(2N)\rceil$ doublings detects the one-sided identity or an earlier nonunit denominator by a proper gcd. The sieve, scalar and curve enumeration cost $\widetilde O((B+1)\operatorname{poly}(\log N))$ with the existential fixed polynomial cutoff. The explicit larger cutoff instead costs $\widetilde O((B+1)\exp(O((\log\log N)^2)))$; both fit the same one-third scale when $\log B=O((\log N)^{1/3}(\log\log N)^{2/3})$. The order candidates describe the smoothness promise. The search uses neither the factorization of $N$ nor a Gaussian representation of either unknown prime. [Checked elliptic arithmetic](cogentic-elliptic-batch-search.md#distinct-right-abscissas-and-exact-leaves)

A finite check enumerated the points and local markings at $101,103,107,109,113,127$. It verified the order candidates for both twists, all eight combinations of a twist sign and a marked square-class vector at each prime, and the strict height drop in the zero coset.
