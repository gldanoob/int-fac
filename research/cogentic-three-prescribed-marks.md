# Three prescribed smooth marks with a quadratic perturbation

An integer quadratic perturbation of the coefficient word gives three prescribed smooth marks in both Cogentic fields. The two cofactors can be fixed after the smooth products are constructed. On the conservative schedule this costs $e^{O(H)}$ bit operations under Dirichlet RH. It uses the full-width coefficient boxes and a cofactor interval of length $m^3e^{O(H)}$. The original two-coordinate perturbation instead has a three-mark compatibility modulus of size $e^{(10003+o(1))V}$. [One- and two-mark construction](cogentic-cofactor-point-construction.md) · [Fixed schedule](cogentic-deterministic-two-thirds.md#fixed-parameters)

## Integral interpolation at three marks

Use $g=P_0\ell$, $m=\lceil N^{1/d}\rceil$, and let $R(X)$ be the base-$m$ digit polynomial for $N$. Work in the two field families
\[
 f(X)=f^{(0)}(X)+gkR(X)+g(X-m)(x+Xy+X^2z),\qquad
 f(m)=N(k_0+gk).
\]
Allow independent $k,x,y,z$ in the two fields. Use the original intervals of sizes $UA$ and $U$ for $x,y$, and make $[0,K)$ a power-of-two interval with $K\ge A^3m^3(\log N)^{C_0}$ for a sufficiently large fixed $C_0$, rounding up within a factor two. The construction gives $|z|\le (U/A)e^{(-5+o(1))H}$. It preserves the leading coefficient and the coefficient residues modulo $g$, since $d>3$ for sufficiently large inputs.

Prescribe three marks $0<a_1<a_2<a_3\le A$ in the fixed grid. Here clean means that $\gcd(N,m-a_i)=1$ and $f^{(0)}(a_i)$ is coprime to $g(m-a_i)$ in each field. Require $a_j-a_i\ge AB^{-1/100}$ for every $i<j$. Write $n_i=m-a_i$, $R_i=R(a_i)$, $\Delta_{ij}=a_j-a_i$, and $D=\Delta_{12}\Delta_{13}\Delta_{23}$.

In each field fix $y_c$ at a midpoint of its coefficient interval and take $x_c$ within $D$ of the intercept midpoint such that all three values
\[
       M_i=f^{(0)}(a_i)-gn_i(x_c+a_i y_c)
\]
are units modulo $gD^2$. Primes of $g$ already see units by the clean conditions. For a prime $p\mid D$ outside $g$, the expression is constant and nonzero modulo $p$ if $p\mid n_i$. Otherwise varying $x_c$ excludes one residue for this mark. At most three residues are excluded, and $p>3$ because $P_0$ includes two and three. Choose allowed residues and combine them by CRT modulo the radical of $D$. Trial division of the differences through $A$ finds all the needed primes. This displacement is $o(UA)$.

Take $\eta=B^{-1/8}$. Construct squarefree band products $P_i$ near $|M_i|$ with $P_i=|M_i|(1+O(\eta))$ and
\[
       \operatorname{sgn}(M_i)P_i\equiv M_i\pmod{gD^2}.
\]
Omit every band prime dividing $gD n_1n_2n_3$. This is the same prime-strip construction as for two marks with one larger bound on the modulus. Namely $\log(gD^2)\le(61000+o(1))H$. Use 200 terminal strip pieces with one chosen prime in each and put the other, unvaried primes in the initial piece. The source prime-strip calculation gives an error at most $\exp((-325\cdot200+o(1))H)$ in the terminal residue probability, smaller than $1/\varphi(gD^2)$. Sieve through $B$ and enumerate the terminal tuples. There are at most $B^{200}$, and the discarded prime list is polynomial in $\log N$. This gives all six products with their exact factorizations. [Prime-strip construction](cogentic-cofactor-point-construction.md#constructing-a-squarefree-product-with-a-prescribed-unit-residue)

Set $w_i=(\operatorname{sgn}(M_i)P_i-M_i)/(gD)$, an integer divisible by $D$, and seek $k=Dk'$. The three congruences
\[
                     R_i k'\equiv w_i\pmod{n_i}
\]
have a common solution. Each $R_i$ is a unit modulo $n_i$ since $R_i\equiv N\bmod n_i$. A pair of their prescribed $k'$ classes agrees modulo $\gcd(n_i,n_j)$ because that gcd divides $\Delta_{ij}$ and hence $D$. The compatible CRT solution gives a $k$ class of period $D\,\operatorname{lcm}(n_1,n_2,n_3)\le A^3m^3$. For any representative in $[0,K)$ the desired shifts at the marks are
\[
                    e_i=\frac{R_i k-Dw_i}{n_i}\in D\mathbb Z.
\]
The quadratic polynomial interpolating these three $e_i$ has integral coefficients. In each Lagrange summand, the denominator $\prod_{j\ne i}(a_i-a_j)$ divides $D$ and the numerator polynomial has integer coefficients. Write the interpolant as $E(X)=e_0+e_1^*X+e_2^*X^2$ and take $(x,y,z)=(x_c+e_0,y_c+e_1^*,e_2^*)$. Substitution gives the prescribed marked values exactly.

The source bound $|M_i|/(gn_i UA)\le e^{(100+o(1))H}$ and $\log R_i\le(10001+o(1))V$ give
\[
 |e_i|\le R_iK/n_i+\frac{O(\eta)|M_i|}{gn_i}
                       \le UA e^{(-25+o(1))H}.
\]
The first summand has logarithm at most $(10003+o(1))V$, negligible compared with the right side. Every Lagrange denominator has magnitude at least $A^2 B^{-2/100}$. The coefficient of $X^r$ in its numerator polynomial has absolute value at most $2A^{2-r}$ for $r=0,1,2$. Consequently
\[
                 |[X^r]E|\le U A^{1-r}e^{(-5+o(1))H}.
\]
The shifts in $x,y$ fit inside the original coefficient intervals. Moreover the new quadratic-word direction contributes at most $g(m+A) U A e^{(-5+o(1))H}$ on $|X|\le A$. This is $o(X_{\rm sc}/K_1)$ on the fixed schedule. The cofactor addition on the same real interval has size at most $\exp((10004+o(1))V)$ and also fits the nominal perturbation bound.

Finally choose representatives of the two solved $k$ classes after all six smooth products are known. Let $s$ be the number of distinct primes used in them. The period is coprime to every such prime, as is $g$. In $s+1$ consecutive representatives of either solved class, a selected prime divides $k_0+gk$ for at most one representative, since $p>s+1$. This list fits by the condition on $K$. Choose a representative avoiding every selected prime in each field. The $P_i$ are also coprime to $n_i$, so $f(a_i)\equiv (k_0+gk)N\bmod n_i$ guarantees the actual cofactor grid eligibility. Therefore all three marks pass the true squarefree smoothness tests in both fields, with both cofactors fixed.

## The compatibility equation in the original family

In the original family impose $z=0$. Let $v_i=f(a_i)$ and keep the central values $M_i$ above. Put
\[
 W=(\Delta_{23}n_2n_3,\ -\Delta_{13}n_1n_3,\ \Delta_{12}n_1n_2),
 \qquad \mathcal D=W\cdot(R_1,R_2,R_3).
\]
The two vectors multiplying $x-x_c$ and $y-y_c$ are annihilated by $W$. Hence the three actual outputs satisfy the exact necessary identity
\[
                         W\cdot(v-M)=gk\mathcal D.                 \tag{1}
\]
In addition, the first two congruences modulo $n_1,n_2$ and the integral slope congruence are necessary. When the shifts at all three marks have already been made multiples of $D$ as above, (1) is exactly the condition that their interpolating coefficient of $X^2$ vanish.

For an arithmetic expression for $\mathcal D$, let $Q(X)=(R(X)-N)/(X-m)\in\mathbb Z[X]$. The bracket $[Q]_{a_1,a_2,a_3}$ denotes its second divided difference, an integer since this holds for every monomial. The second divided difference of $1/(m-X)$ is $1/(n_1n_2n_3)$. It follows that
\[
             \mathcal D=D\bigl(N-n_1n_2n_3[Q]_{a_1,a_2,a_3}\bigr)\ne0.
\]
Nonvanishing also follows from $\gcd(N,n_1n_2n_3)=1$. Its size on the stated grid satisfies
\[
                         \log|\mathcal D|=(10003+o(1))V .
\]
For the lower bound, the leading base-$m$ digit of $N$ is at least $m-d$. All coefficients of the power series of $R(X)/(m-X)$ for $0<X<m$ are nonnegative. Its contribution from degree $d-1$ to the second divided difference is at least $(1-d/m)\min_i(a_i)^{d-3}$. On the fixed grid $\min_i a_i\ge A/(4d)$, so this has leading logarithm $10000V$. Multiplying by $Dn_1n_2n_3$ adds $(3+o(1))V$. The upper bound follows directly from the definition of $W$ and $R_i\le dm A^{d-1}$. [Nominal grid, pp. 37 and 39](https://raw.githubusercontent.com/google-research/google-research/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=39)

Thus independent choices modulo $gD^2$ solve the displayed divisibility and interpolation conditions for the quadratic-word variant, while the original choices must also solve (1), including its large modulus and cofactor range. More concretely, fixing the first two values in the original family determines a $k$ class of period $L_k$ with $\operatorname{lcm}(n_1,n_2)\mid L_k\mid \Delta_{12}\operatorname{lcm}(n_1,n_2)$ whenever the class is nonempty. The lower divisibility comes from the two individual value congruences and the upper one follows from the slope congruence. Therefore $\log L_k=(2+o(1))V$. The remaining third values form an arithmetic progression with step $g\mathcal D L_k/W_3$, of magnitude $e^{(10003+o(1))V}$. At the original cofactor width $m^2e^{O(H)}$, the progression has only $e^{O(H)}$ candidates. They can be verified directly, but the independent prime-strip argument supplies no guarantee of a third smooth hit in this progression.

Even imposing a homogeneous shared-factor direction does not cancel the compatibility equation if all three multipliers are units at their marks. If $W\cdot C=0$ with $\gcd(C_i,n_i)=1$ for each $i$, reducing modulo $n_i$ gives $n_i\mid W_i$, since the other two terms already contain $n_i$. Yet $\gcd(n_i,W_i)\le A^3\ll n_i$, by the difference bound on each $\gcd(n_i,n_j)$ and on the one difference in $W_i$. This obstruction and (1) apply to the given two-coordinate parametrization. They leave open a correlated construction of three products in that family and do not transfer the conditional score to the added quadratic direction.

For a finite arithmetic check, use $m=30$, $N=361$, $g=5$, $R(X)=1+12X$, marks $10,14,18$, and base polynomials $361$ and $361+10(X-30)$. On these deliberately small inputs the three-mark CRT and integral interpolation recover the tuples $(k,x,y,z)=(2048,-292768,-14496,-52040)$ and $(2048,-292768,-14496,-35656)$. The first field gives $673\cdot840137$, $47\cdot67\cdot272269$, and the prime $1047101801$. The second gives $179\cdot2243419$, $43\cdot13964507$, and $73\cdot9980777$. Trial division verifies the factors and their coprimality to both cofactors, which equal $10241$ here. Substitution also verifies (1) for the same tuples with the quadratic coefficient deleted. This checks the finite compatibility and cofactor selection identities separately from the asymptotic prime-strip estimates.
