# Cofactor averaging for intermediate Cogentic windows

An extra coefficient that changes the multiple of $N$ at the common argument supplies the residues missing from the fixed-class counter. On the conservative schedule, keeping that coefficient averaged allows arbitrary translated one-mark and two-mark windows with lengths $\exp((\tau+o(1))V)$ for $49999.5<\tau<50000.5$. The calculation includes affine row predicates and omissions from the changing cofactors. It estimates elementary factors in an enlarged polynomial family. The fixed-cofactor score and the eventual selection of this extra coefficient require separate arguments. [Fixed schedule](cogentic-deterministic-two-thirds.md#fixed-parameters) · [Sharp scalar counter](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli) · [Residue averaging](cogentic-weighted-smooth-count.md)

## A coefficient that varies the residue at every mark

Use $g=P_0\ell$, $m=\lceil N^{1/d}\rceil$ and a fixed initial field polynomial $f^{(0)}$ with $f^{(0)}(m)=k_0N$. Perfect powers have already been removed. Let $R(X)$ be the degree-at-most-$d-1$ base-$m$ digit polynomial for $N$. Add
\[
       gk R(X)+g(X-m)(x+Xy),\qquad 0\le k<K,
\]
so $f(m)=k_*(k)N$ with $k_*(k)=k_0+gk$. The leading coefficient and all coefficient residues modulo $g$ stay fixed. At mark $a$ set $n_a=m-a>0$ and $R_a=R(a)$. Then
\[
       f(a)=f^{(0)}(a)+gR_a k-gn_a(x+ay),\qquad
       R_a\equiv N\pmod{n_a}.
\]
The original mark eligibility check $\gcd(N,n_a)=1$ makes $R_a$ a unit modulo $n_a$. Outside the target-root classes of the first field, the marked value is a unit modulo $g$ throughout the enlarged family. Restrict to these marks below. The leading size of the marked values is unchanged. Indeed $R_a\le dm A^{d-1}=\exp((10001+o(1))V)$ and we use $K=m^2\exp(O(H))$. The added contribution has size $\exp((10003+o(1))V)$, whereas all original marked magnitudes are $\exp((100001+o(1))V)$. The sign remains fixed, and the extra normalized perturbation on the real grid is exponentially smaller than the prescribed perturbation bound. [Grid and unit checks](cogentic-intermediate-score-budget.md#dyadic-subboxes-and-the-linear-mass-term)

A unit-mark check can be imposed exactly while averaging $k$. Since $f(a)\equiv k_*(k)N\bmod n_a$, the conjunction of squarefree band smoothness and $\gcd(k_*(k),n_a)=1$ is precisely squarefree smoothness after deleting the band primes dividing $n_a$. In two fields impose this condition independently in each field. Additional prescribed band omissions can be made from the outset.

## One- and two-mark counts

Consider a projected scalar progression at $a_i$ arising on a rectangle and projection residue as in the existing geometric reduction. Write $Q\le \exp(O(H))$ for its projection period and $T_i$ for the number of terms. Both projections in a given rectangle can use the same $Q$. After taking the fixed sign and reversing indices where needed, the positive marked values at this progression are of the form
\[
     c_i \mathbin{\pm} g R_{a_i} k + g d_i j,\qquad
     d_i=n_{a_i}Q,\qquad 0\le j<T_i.
\]
Suppose $\log T_i=(\tau+o(1))V$ with $49999.5<\tau<50000.5$. At fixed $k$, replace the shifted interval by $[c_i,c_i+g d_i T_i-1]$ and keep the shifted residue modulo $gd_i$. The fraction changes by at most
\[
       O\left(\frac{R_{a_i} K}{d_i T_i}+T_i^{-1}\right)
                        =e^{-\Omega(V)}.                     \tag{1}
\]
The endpoint comparison is a count of all progression members in the symmetric difference. It requires no estimate for smooth numbers. Changes of the $k$-interval origin within the specified range give the same bound.

For one mark, replace $k$ modulo $d_1$ by a uniform residue. An interval of length $K$ has total variation distance at most $d_1/K$ from uniform modulo $d_1$. The shifted residue is then uniform on a coset whose effective step is $g\gcd(R_{a_1},d_1)$, at most $gQ$. Pooling all its classes in the common interval gives exactly a single progression of length $T_1 d_1/\gcd(R_{a_1},d_1)$. In particular its leading logarithm is $(1+\tau)V$.

For distinct marks $a_1,a_2$ take $D_0=\gcd(d_1,d_2)$. This is at most $Q|a_1-a_2|$, since $n_{a_1}-n_{a_2}=a_2-a_1$. Uniform $k$ modulo $\operatorname{lcm}(d_1,d_2)$ first gives a uniform class modulo $D_0$. In that class the residues modulo $d_1,d_2$ are independent and uniform on their respective classes modulo $D_0$, by CRT. At either mark the image residue modulo $gd_i$ is then uniform on a coset with effective step $gA_i$, where
\[
       A_i=\gcd(R_{a_i}D_0,d_i)\le QD_0.
\]
Here $\gcd(R_{a_i},n_{a_i})=1$ gives $\gcd(R_{a_i},d_i)\le Q$. The pooled scalar length is $T_i d_i/A_i$. Thus for that common class the two averages multiply. Average the products over the $D_0$ classes. There are $\exp(O(H))$ classes, and the total variation error of replacing $k$ by the full joint cycle is at most $\operatorname{lcm}(d_1,d_2)/K\le m^2 Q/K$. Repeated marks give one Boolean test.

Each pooled progression has height $\exp((100001+o(1))V)$, modulus $\exp(O(H))$, and length $\exp((1+\tau+o(1))V)$. The sharp scalar count under Dirichlet RH therefore gives fraction error $e^{-CH}$ at cost $e^{O(H)}$ for any fixed $C$. The strict inequality $1+\tau>50000.5$ supplies the square-root margin. Choose the factor $\exp(O(H))$ in $K$ large enough to absorb every cycle loss, including any prescribed precision. Bound (1) is still exponentially smaller.

For full coefficient rectangles, use the existing projection panel construction with geometric error $e^{-C'H}$, for a sufficiently large fixed $C'$. In a box with side lengths $\exp((\tau+o(1))V)$ and ratio at most $2A$, write $T_{\min}$ for the smaller side. After the split into at most $\exp(O(H))$ projection panels and residue pairs, discard every piece for which a scalar length is less than $T_{\min}e^{-C''H}$. The total error is at most $e^{-C'H}$ for a sufficiently large fixed $C''$. Each such piece has at most $T_{\min}^2\exp(O(H)-C''H)$ points, and the box contains at least $T_{\min}^2$. All other pieces have the required scalar lengths and the errors average by their exact point counts. This works for arbitrary box origins inside the allowed perturbation box. [Two-mark projection and weights](cogentic-scalar-divisor-count.md#rectangles-for-a-pair-of-marked-values)

## Modular conditions and changing cofactor omissions

Affine row conditions at any bounded number of primes up to $B$ can be imposed by splitting $(k,x,y)$ into classes modulo a common $M_0=\exp(O(H))$. The $(x,y)$ classes are incorporated in $Q=|a_1-a_2|M_0$ for a two-mark rectangle. A class of $k$ gives $k=k_1+M_0k'$, with length $K/M_0+O(1)$. Then $R_{a_i}$ in the orbit calculation is replaced by $M_0R_{a_i}$, and the gcd gains at most a factor $M_0$. Taking $K\ge m^2 M_0Q e^{C'H}$ up to integer rounding maintains the cycle error. All genuine counts can be weighted by the exact probability of the residue restrictions. A prescribed prime product $e_i$ dividing a marked value can be imposed in the same class split, taking $M_0$ a multiple of $e_i$. To enforce squarefreeness at those primes, divide the whole marked progression by $e_i$ and omit its prime factors. The physical interval and its effective step both divide by $e_i$, leaving the length unchanged. All scale conclusions survive a division by $\exp(O(H))$.

The eligible band can also exclude every prime dividing either of the two changing cofactors $k_*^{(1)}(k)$, $k_*^{(2)}(k)$. Allow independent $k$ coordinates across the two fields. For a term with at most two marks per field, let $E_p$ be the event that $p$ divides at least one cofactor and at least one marked value. Only eligible band primes matter, and for each marked value that can contribute, $p$ is coprime to its original scalar step $gn_a$. This holds because the row is unit modulo $g$ and the mark test already removed primes dividing $n_a$. Terms with barred $p$ at that mark are absent from the union defining $E_p$. A cofactor condition imposes one $k$ residue and, given all $k,y$, a marked-value condition imposes one $x$ residue. For a set of $b$ distinct primes with product $e$, choose for each prime one cofactor witness and one marked-value witness. There are at most $8^b$ choices. For each fixed choice CRT bounds the density of the simultaneous restrictions by $16/e^2$, once all $k$ and $x$ intervals are longer than $B^b$. For example, a set of assigned primes with product $e'$ cuts the corresponding coordinate density to at most $1/e'+1/\text{length}\le2/e'$, and there are at most four such coordinates. Sum over choices to bound the probability of the intersection.

Use Bonferroni through a fixed order $b_0$ to enforce that none of the $E_p$ occurs. The error, even after multiplying by any other $0$-$1$ constraints, is at most
\[
      16\bigg(8\sum_{p>\sqrt B}p^{-2}\bigg)^{b_0+1}
                      =\exp((-500(b_0+1)+o(1))H).
\]
This bound uses the unrestricted box and so applies when the term also includes a row predicate. Each retained intersection with $b\le b_0$ is evaluated by splitting both fields into classes for these primes and any affine row conditions. In each class the cofactor and marked-value divisibility predicates are known, and the two field factors separate. Every modulus and the number of splits is $B^{O(b_0+1)}=\exp(O(H))$. Choose $b_0$ and the scalar precision to absorb the target error and every retained summand. Thus elementary separated terms of this form can be evaluated at precision $e^{-CH}$ throughout the stated intermediate range. A signed score with $\exp(O(H))$ such terms and fixed coefficient sum $\exp(O(H))$ inherits the same precision by increasing $C$.

The one-mark count can select a genuinely populated child. In the full coefficient box, the fraction of cofactors for which $k_*(k)$ is coprime to $n_a$ is at least $\varphi(n_a)/n_a-o(1/\log(2n_a))=e^{-o(H)}$, by the full residue cycles and because primes dividing both $n_a$ and $g$ already see a fixed unit. For each such cofactor the original full-width Gaussian estimate at a horizontal intercept slice applies. The added shift does not affect the leading height or width, and the cofactor removes only polynomially many primes in $L$. Comparing the Gaussian with the uniform interval gives a fraction at least $\exp((-100001/3000+o(1))H)$ before averaging over these cofactors. Fixing a slope is already enough for this assertion. Now bisect only the intercept interval while leaving $k$ averaged. The estimate (1) and the pooled sharp count work at every length from the original full interval down to a target length $\exp((\tau+o(1))V)$ in the stated intermediate range. Keeping the child with larger estimated fraction costs at most $2e^{-CH}$ per split. For $C>100001/3000+1$, the final dyadic child still has fraction at least $\exp((-100001/3000+o(1))H)$. This construction costs $e^{O(H)}$, and the required absolute precision excludes a zero estimate. [Full-width lower bound](cogentic-intermediate-score-budget.md#dyadic-subboxes-and-the-linear-mass-term)

This arithmetic construction changes the cofactor at $m$. The original conditional score uses a fixed cofactor and its cofactor-dependent grid and reference weights. The calculation above gives no equivalence of those scores across different cofactors. It also uses $K=\exp((2+o(1))V)$ for two marks. Fixing that coordinate would remove the full-cycle guarantee, and scanning it would cost more than the saving in the intercept exponent. The reduction shows how genuine scalar windows can use the residue-mixture bound while an extra polynomial coefficient stays averaged.

The [finite replay](../experiments/cogentic-cofactor-dispersion.py) checks three two-mark pools on a cycle of 240 cofactor residues, including two prior congruence restrictions. An independent enumeration of 539 smooth marked values checks the prime-omission congruences, division by their selected product and the Bonferroni brackets.
