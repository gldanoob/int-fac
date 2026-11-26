# Cofactor averaging for intermediate Cogentic windows

An extra coefficient that changes the multiple of $N$ at the common argument supplies the residues missing from the fixed-class counter. On the conservative schedule, keeping that coefficient averaged allows arbitrary translated one-mark and two-mark windows with lengths $\exp((\tau+o(1))V)$ for $49999.5<\tau<50000.5$. The calculation includes affine row predicates and omissions from the changing cofactors. It estimates elementary factors and the normalized mass penalty in an enlarged polynomial family. The Gram terms and the eventual selection of the new coefficient require separate arguments. [Fixed schedule](cogentic-deterministic-two-thirds.md#fixed-parameters) · [Sharp scalar counter](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli) · [Residue averaging](cogentic-weighted-smooth-count.md)

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

## The normalized mass penalty with changing cofactors

Let $K_*=\lvert k_*^{(1)} k_*^{(2)}\rvert$. For each raw grid cell $I$, write $D_I(K_*)$ for the fraction of its integers satisfying $\gcd(a-m,K_*)=1$, and put $D_*(K_*)=\prod_{p\mid K_*}(1-1/p)$. The raw cell size is $\exp((9997+o(1))H)$, and $\log K_*=O(V)$ uniformly. Then
\[
                  D_I(K_*)=D_*(K_*)+e^{(-1500+o(1))H}.        \tag{2}
\]
Here and below the exponential error notation denotes a bound in absolute value. To prove (2), take $Y_0=e^{3000H}$ and first ignore primes above $\sqrt{Y_0}$. In the cell and in the product this incurs at most $O(V)(Y_0^{-1/2}+|I|^{-1})$, by the progression bound for each ignored prime. For the remaining primes dividing $K_*$, expand the product of the factors $1-\mathbf1_{p\mid a-m}$ recursively in increasing prime order. Prune each branch immediately after its included-prime product exceeds $Y_0$. Its residual is the product of $\mathbf1_{d\mid a-m}$ with the remaining factors, up to sign, for a unique first-crossing product $Y_0<d\le Y_0^{3/2}$. The sum of the cell means of these residuals is bounded by
\[
  \sum_{\substack{d\mid\operatorname{rad}(K_*)\\d>Y_0}}\frac1d
       +\frac{Y_0^{3/2}}{|I|}
  \le Y_0^{-1/2}\prod_{p\mid K_*}(1+p^{-1/2})
       +\frac{Y_0^{3/2}}{|I|}.
\]
The logarithm of the product is $O(\sqrt V)=o(H)$, by ordering the distinct prime factors and using $p_j\ge j+1$. The retained divisibility means differ from their reciprocal products by at most $Y_0/|I|$ in total. The tail of the reciprocal-prime product has the same Rankin bound. This proves (2).

Since $D_*\ge1/(1+\omega(K_*))=e^{-o(H)}$, one may replace each cell denominator by $D_*$. The powers $D_*^{-r}$ for $r=1,2$ have a finite divisor expansion. The local coefficient at $p\mid K_*$ is $(1-1/p)^{-r}-1=O(1/p)$, with constant term one. Truncate to squarefree products $d\le Y_0$; the discarded part is at most $Y_0^{-1/2}\prod_{p\mid K_*}(1+O(p^{-1/2}))=e^{(-1500+o(1))H}$. Each retained factor $\mathbf1_{d\mid K_*}$ is a predicate modulo $d$ on the cofactor coordinates. Thus the one- and two-mark estimates compute expectations with the expanded weights by adding these congruences. The included divisors, all moduli and the sum of the absolute expansion weights are $e^{O(H)}$.

The Gaussian principal references $Z_i^{(0)}(a)$ for the normalized mass can also be made independent of the cofactor coordinates at the required precision. In the pinned definition their heights $\mu_i(a)$, widths $S^*_{1,i}(a)$, and the factor $q_a/\varphi(q_a)$ are fixed. Cofactor dependence comes from removing band primes that divide $K_*$. Keep the prescribed omissions for $\ell$ and for primes dividing $n_a$, and restore the other primes in the reference integral only. On the fixed unperturbed saddle $\alpha=1-o(1)$, the change in the Euler product is bounded pointwise by its positive value at $\alpha$ times $\sum_{p\mid K_*,\ p>\sqrt B}p^{-\alpha}=e^{(-500+o(1))H}$. The principal integral may use this same line for either product by Mellin inversion. The integral of the absolute Mellin transform on that line is $O(R \mu_i(a)^{\alpha-1})$, where $R=\mu_i(a)/S^*_{1,i}(a)\le e^{(110+o(1))H}$. The saddle lower bound divides out $\mu_i(a)^{\alpha-1}$ and the positive Euler value up to an $e^{o(H)}$ factor. Thus restoring these primes costs relative error $e^{(-390+o(1))H}$ in $Z_i^{(0)}$. The smoothness indicator itself still uses the true variable omissions. [Pinned definitions, pp. 43 and 50–52](https://raw.githubusercontent.com/google-research/google-research/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=50) · [Principal transform bounds](cogentic-fixed-window-audit.md)

Now expand $\widehat C$ and $\widehat C^2$ for the enlarged fields. For each mark its exact grid indicator is retained by the unit-mark condition, and its fixed cell size is normalized using the expansion of $D_*^{-1}$ or $D_*^{-2}$. The discarded target-root marks have mass at most $e^{(-997+o(1))H}$, even under the varying grid normalization by (2). The inverse reference at one field and mark costs $e^{(\rho+o(1))H}$, where $\rho=100001/3000$. For the square expansion at most four such references occur. The error in $64(\widehat C-1)^2$ from freezing them, replacing the density and removing target-root marks is bounded uniformly by $e^{(-390+4\rho+o(1))H}=O(e^{-250H})$. Evaluating the finite expansion to finer error retains $O(e^{-250H})$ accuracy for the conditional mean of the full mass penalty in $e^{O(H)}$ time. A distinct-mark term uses the two-mark reduction in each field and a repeated-mark term uses the corresponding one-mark reduction.

This transfers the actual grid normalization and mass penalty while the cofactor coordinates stay averaged. The centered Gram terms use other cofactor-dependent references, which are outside this calculation. The two-mark count also needs $K=\exp((2+o(1))V)$. Fixing the cofactor removes the full-cycle guarantee, and scanning it costs more than the saving in intercept length.

The [finite replay](../experiments/cogentic-cofactor-dispersion.py) checks three two-mark pools on a cycle of 240 cofactor residues, including two prior congruence restrictions. An independent enumeration of 539 smooth marked values checks the prime-omission congruences, division by their selected product and the Bonferroni brackets.

## Cofactor descent below a complete residue cycle

For horizontal scalar slices with fixed prime omissions one can replace the full-cycle argument by a counting-norm bound. This works for a product of two scalar fractions even when the two residues are correlated. Let $k$ range over an arbitrary interval of $K'$ consecutive integers, and for each mark write the step as $q_i=gn_{a_i}$, with progression length $T_i$. Keep the unit condition modulo $q_i$ and delete its prime divisors from that mark's band. Assume the marked class is a unit modulo $g$ throughout, as in the preceding calculation. All omitted primes are fixed in this argument and their number is polynomial in $L$, as required by the individual Dirichlet-RH character estimate.

Replace the shifted physical interval at each $k$ by the leftmost cofactor's integer interval of length $q_iT_i$, keeping the residue $r_i(k)$ modulo $q_i$. The error in the fraction is at most $O(R_{a_i}K'/(n_{a_i}T_i)+1/T_i)$ by the same endpoint count as (1). Additions and subtractions to the residue as $k$ changes give a single orbit of period $n_{a_i}$, because $r_i(k)$ changes by $\pm gR_{a_i}$ and $R_{a_i}$ is coprime to $n_{a_i}$. Hence each residue has probability at most $1/n_{a_i}+1/K'$.

Write $C_i(r)$ for the count at a unit class in the common interval, $M_i=\sum_r C_i(r)$ for its total, and $E_i=O(w h_i^{\sigma_0})$ for the nonprincipal character bound at height $h_i$. Parseval gives
\[
 \sum_{r\in(\mathbb Z/q_i\mathbb Z)^\times}
 \left|C_i(r)-M_i/\varphi(q_i)\right|^2\le E_i^2.
\]
Consequently the expectation over $k$, including only unit $r_i(k)$, of the absolute error after replacing $C_i(r_i(k))/T_i$ by $p_i=M_i/(\varphi(q_i)T_i)$ is at most
\[
 \frac{E_i}{T_i}\sqrt{\frac1{n_{a_i}}+\frac1{K'}}.
\]
Both fractions lie in $[0,1]$ because the common integer interval has exactly $T_i$ integers per residue. Set each to zero on nonunit residues. Telescoping a product of the two fractions shows that the expected product differs from
\[
 p_1p_2\Pr_k(r_1(k),r_2(k)\text{ both units})
\]
by at most the sum of their endpoint and counting-norm errors. No independence of the two residue maps is used. The one-mark version uses just its single unit probability. The sharp untwisted count and truncated totient estimate compute each $p_i$ to error $e^{-CH}$ in $e^{O(H)}$ time when $q_iT_i\ge h_i^{\sigma_0}e^{O_C(H)}$. Numerical approximations can be clipped to $[0,1]$. [Counting-norm and principal-term estimates](cogentic-weighted-smooth-count.md#weighted-scalar-estimate)

The joint unit probability can be computed to error $e^{-CH}$ without factoring $n_{a_1}n_{a_2}$. For each prime dividing this product and coprime to $g$, the unit conditions forbid at most two classes of $k$. Test divisibility by primes through $Y^{1/2}$, with $Y=e^{D H}$ for a sufficiently large constant $D$, and ignore the rest. The ignored probability is $O(\omega(n_{a_1}n_{a_2})(Y^{-1/2}+1/K'))$. Expand the remaining avoidance predicates by inclusion–exclusion, pruning on the first included-prime product above $Y$. Any retained intersection is a union of at most $2^{\omega(d)}$ CRT classes modulo its squarefree product $d$ and has an exact floor count. A first-crossing branch has product $Y<d\le Y^{3/2}$, and the ignored descendants form a remaining avoidance predicate bounded by one on that intersection. Thus its contribution is bounded by $2^{\omega(d)}(1/d+1/K')$. Summing these upper bounds costs at most
\[
 Y^{-1/2}\prod_{p\mid n_{a_1}n_{a_2}}(1+2p^{-1/2})+Y^3/K'.
\]
The product is $e^{o(H)}$ since the number of distinct prime factors is $O(V)$ and $p_i\ge i+1$ for the ordered primes. Retained CRT enumeration costs a polynomial in $Y$ and the input bit lengths. Thus the unit probability has the claimed precision when $K'$ has any fixed positive leading exponent on the $V$ scale.

On the fixed schedule let $\lambda=100001$ and $\log T_i=(\tau+o(1))V$ with $50000<\tau<50000.5$. For any fixed $\kappa$ with $\lambda-2\tau<\kappa<1$, the bound above evaluates both child averages during cofactor bisection down to length $\exp((\kappa+o(1))V)$. Indeed $h_i^{\sigma_0}=\exp((\lambda/2+o(1))V)$, $n_{a_i}=\exp((1+o(1))V)$, and $\kappa>\lambda-2\tau$ gives a strict margin in the counting-norm error. Even the original longest cofactor interval leaves the endpoint error exponentially small in $V$. The pooled physical interval also exceeds the untwisted threshold. Keeping the child with the larger computed fraction loses at most $2e^{-CH}$ per split. Starting with the populated one-mark child described above and choosing $C$ sufficiently large therefore preserves its positive exponential density. This reduces the cofactor width below a single residue cycle, even though the intercept is still below its individual square-root threshold.

The remaining cofactor exponent $\kappa$ is positive for any fixed $\tau<\lambda/2$. An exhaustive scan over its cofactors and intercepts would cost $\exp((\kappa+\tau+o(1))V)$, with $\kappa+\tau>\lambda-\tau>\lambda/2$. The estimate does not supply a final fixed cofactor at one-third cost. It applies to the indicated scalar factors rather than the full Gram or changing-cofactor score.

## The centered Gram expectations while full cycles remain

The cofactor-dependent part of the exact Gram references admits a finite congruence expansion to arbitrary fixed exponential precision. This gives estimates for the whole conditional score from the [four-coefficient construction](cogentic-conditional-score.md#a-computable-nonnegative-score), including the ordinary and protected diagonals, the generator cross block and the remaining Gram norm. Here each cofactor coordinate retains the full-cycle width $m^2e^{O(H)}$. The conclusion is an estimator for the score at that stage of the larger search.

### Exact generator-root marks

The protected roots of the first field modulo $\ell$ are fixed by the coefficient CRT conditions. If $a$ belongs to such a class, then its first-field value is divisible by $\ell$, and $n_a=m-a$ is coprime to $\ell$ because $f_1(m)=k_*^{(1)}N$ is a unit modulo $\ell$. Divide this marked value by $\ell$ and delete $\ell$ from its band. This tests exact valuation one and otherwise leaves the squarefree smoothness predicate unchanged. The scalar step and cofactor step divide by the same factor, so the periods $d_i=n_{a_i}Q$ used above are unchanged. The remaining value is a unit modulo $P_0$, and coprimality with $n_a$ is equivalent to the original mark condition at this field. The second field has no target root, and the cofactors are always units modulo $\ell$. Thus the joint-omission argument applies in the protected classes without discarding their marks or charging them against their row weights. [Protected rows and reference formulas, pp. 38 and 50–52](https://raw.githubusercontent.com/google-research/google-research/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=50)

### Finite differences for the saddle coefficients

Let $\mathcal S$ be any realized set of cofactor omissions from the band. It has $O(V)$ members. Temporarily introduce one complex variable $z_p$ for $p\in\mathcal S$, so the full-band Euler factor $1+p^{-s}$ is replaced by $1+(1-z_p)p^{-s}$. The variables $z_p=1$ give the actual omitted product. Predetermined omissions, such as a row prime in an insertion numerator or a prime dividing $n_a$ in a Gaussian reference, are applied independently of these variables.

Uniformly on $|z_p|\le e^{200H}$, each reference saddle is a holomorphic function of these variables. Here the real reference heights $Y$ include the nominal heights divided by at most two row primes, and have $\log Y=(100001+o(1))V$. Let $\alpha_0$ be the full-band saddle at $Y$, $u=\log Y/\log B$, and let $\varphi_0$ be the logarithm of the full-band product. On a complex disk of radius $c_0/\log B$ about $\alpha_0$, with $c_0$ a small absolute constant, the first three logarithmic derivatives of the perturbed product differ from the original derivatives by at most
\[
     e^{(-300+o(1))H}(\log B)^j \qquad(1\le j\le 3).
\]
This follows by writing each logarithmic change as $\log(1-z_p p^{-s}/(1+p^{-s}))$, whose argument perturbation is uniformly $e^{(-300+o(1))H}$. The number of variables and powers of $\log B$ are $e^{o(H)}$. The full-band derivative obeys $\varphi_0''(\alpha_0)\asymp u(\log B)^2$ and its third derivative on that disk is $O(u(\log B)^3)$, by termwise bounds on the Euler factors. On the circle the linear term in $\varphi_0'(s)+\log Y$ therefore dominates the Taylor remainder. Rouché first gives one simple full-band root there, then one root for the perturbed equation. Its displacement is at most $e^{(-300+o(1))H}/(u\log B)$ by the linear lower bound in the disk. The perturbed derivative $\varphi''$ is nonzero at that root, so the implicit function theorem and uniqueness give a single holomorphic saddle throughout the polydisc.

Each central integral $I_{\rm pure}(Y;S)$ in the exact Gram references uses this saddle and a fixed bounded frequency interval. Its integrand at the moved saddle differs from the original integrand by at most $e^{(-300+o(1))H}Y^{\alpha_0-1}F_0(\alpha_0)$ uniformly on that central interval. To see this, telescope the Euler factors, and bound the change in the integrand from moving $s$ by the saddle displacement times $O(\log Y+\sum_p p^{-\alpha_0}\log p)$ and the same positive Euler envelope. The original central integral is $\asymp Y^{\alpha_0-1}F_0(\alpha_0)/(\sqrt u\log B)$, allowing fixed row-prime insertions or polynomially many fixed deletions. It stays nonzero on the polydisc. Each full Gaussian reference can use the original saddle line independent of the variables, since the finite product is entire and its compact Mellin window has the prescribed decay. The same telescoping bound, with the Mellin $L^1$ cost at most $e^{(110+o(1))H}$ times the scale of the integrand, keeps its relative perturbation at most $e^{(-190+o(1))H}$. Thus its denominators also stay nonzero. The positive square roots of saddle variances have holomorphic branches, since those variances stay in a small relative disk about their positive original values. [Saddle and principal estimates](cogentic-fixed-window-audit.md) · [Exact central reference formulas, pp. 43–46 and 52](https://raw.githubusercontent.com/google-research/google-research/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=45)

In particular the following individual analytic coefficients have a bound $e^{C_0H}$ on the polydisc for an effective fixed $C_0$. They include $q^{\pm\alpha_s/2}$ and the $q^{-\alpha_s}$ row weights, the mass and variance reference sums over band primes, inverse Gaussian references, and the one- and two-prime ratios of central integrals defining the local exact Gram matrix $\widetilde U^{\rm ex}(a)$. A sum such as $\sum_{q\in J_*}q^{-\alpha_s}$ is interpolated by assigning multiplier $1-z_q$ to the supported deletion variables. Products of a bounded number of these coefficients and their reciprocals as used in the score obey the same kind of bound. For a fixed factor-base row, its actual membership in $J_*$ is enforced separately by the congruence condition $q\nmid K_*$. The power and ratio formulas can be evaluated for other variable values without imposing that membership.

Here is the finite expansion. For any such analytic coefficient $F$, and any subset $U$ of band primes, compute
\[
       b_U=\sum_{J\subseteq U}(-1)^{|U|-|J|}\,F(\mathbf1_J),
\]
where all unlisted primes are present. The value tested on an actual cofactor is approximated by
\[
        \sum_{|U|\le r} b_U\prod_{p\in U}\mathbf1_{p\mid K_*}.
                                                                    \tag{3}
\]
For proof fix its realized set $\mathcal S$. A Taylor monomial in the variables of $\mathcal S$ contributes to $b_U$ exactly when its support is $U$. All discarded monomials have total degree larger than $r$. Cauchy's estimate on the polydisc bounds their sum at the point with all variables one by
\[
         e^{C_0H}\sum_{n>r} (|\mathcal S|e^{-200H})^n.
\]
There are at most $|\mathcal S|^n$ monomials of total degree $n$ for nonempty $\mathcal S$, and the empty case is exact. Choosing a fixed $r$ sufficiently large gives any fixed absolute error $e^{-CH}$. The sum (3) has at most $B^{O(r+1)}$ summands, with absolute coefficient sum $e^{O(H)}$. Each coefficient uses only evaluations with explicitly supplied finite prime omissions, available from the [score coefficient evaluator](cogentic-conditional-score.md#computing-the-real-coefficients-without-a-smoothness-oracle). Each predicate is enforced by testing the two cofactor residues modulo $\prod_{p\in U}p$.

### Inverting grid cell densities to higher precision

Formula (2) already bounds $D_I-D_*$ uniformly. For any fixed $r$, the identity for $D_I^{-1}$ expanded in the small difference gives
\[
 D_I^{-1}=\sum_{j=0}^{r}(-1)^j(D_I-D_*)^j D_*^{-j-1}
                  + O(e^{(-1500(r+1)+o(1))H}).
\]
Expand the fixed power of the difference by the binomial theorem. Each resulting $D_I^k$ is the average of the product of $k$ grid eligibility indicators over $k$ independent auxiliary marks in $I$. Explicitly enumerate those marks in $e^{O(H)}$ time. They supply unit predicates only, without adding any smooth-value tests. Each fixed power of $D_*^{-1}$ has the divisor expansion used after (2), now truncated at $Y=e^{DH}$ for any sufficiently large fixed $D$. That expansion has arbitrary $e^{-CH}$ accuracy by the same Rankin argument. Products of bounded numbers of cell denominators can use products of these finite formulas.

For a fixed tuple of auxiliary marks, enforcing all unit conditions $\gcd(n_a,K_*)=1$ is an affine avoidance problem on the two cofactor coordinates. A prime dividing $g$ can be ignored since the corresponding cofactors are always units. Other primes of the product of the $n_a$ forbid one class in each relevant cofactor coordinate. On the original cofactor intervals, discard primes exceeding $Y^{1/2}$, with error at most $O(V)(Y^{-1/2}+1/K)$ by summing class counts. Expand the remaining prime avoidance conditions, pruning when the product first exceeds $Y$. The first-crossing products have size at most $Y^{3/2}$, and their summed probability is $e^{(-D/2+o(1))H}+O(Y^3/K)$ by the same Rankin and CRT argument as for the joint unit probability above. This can be done separately for each field. The bounds hold with other $0$-$1$ factors multiplied in, since the pruning error was bounded before inserting them. They can be taken smaller than any required score error by choosing $D$ large enough. All retained tests are finite affine residue predicates with $e^{O(H)}$ total description and enumeration cost. This avoids a fixed error floor from replacing the exact cell densities by $D_*$ alone.

### Separation of the score

Use the universal row list on the full band. Enforce inclusion of each ordinary row by $q\nmid K_*$ and $f_i(r)=0\bmod q$. Protected rows are fixed by CRT. Repeated-root and shared-root flags impose the additional derivative or other-field congruences. The coefficients of these tests, and the scalar baselines in the root-mass and variance terms, have the expansions (3). Thus the root-only part uses affine congruence counts without smooth tests.

For any centered Gram entry, write
\[
  A_{\alpha,\beta}
   =\sum_a w(a)\,I_1(a)I_2(a)
      \left(r_\alpha(a)r_\beta(a)-
        \sum_{b}\pi_0(b)\widetilde U^{\rm ex}_{\alpha,\beta}(b)\right).
\]
Its square has at most two actual smoothness marks per field. The inner reference sums introduce only auxiliary grid marks. A monomial uses at most four cell denominators before their finite expansions. The same description applies to the weighted sum of ordinary squares $D_A$, the protected squares $A_{l_j,l_j}^2$, the target cross block $\ell^{\alpha_s}F_\ell^2$, and the remaining block $F_A^2$. Omitted same-prime off-diagonal entries are absent from the score as in the fixed construction. All resulting congruences can be tested in the common residue splits of the one- and two-mark estimates. When an actual mark is a protected root, use the division by $\ell$ above. The true joint cofactor omissions in the smoothness indicators use the Bonferroni estimate, with its tail bounded before adding the residue tests.

For a prescribed final error $e^{-CH}$, first choose the grid and analytic truncation orders large enough to absorb the fixed exponential bound on the score expansion. Their finite lists have length and coefficient sum $e^{O(H)}$. Choose the auxiliary avoidance precision next, absorbing this list's coefficient sum. Then choose the actual smoothness and cofactor-omission precision to absorb all remaining finite terms. This sequence of choices uses fixed constants at each stage. The final elementary estimates stay in $e^{O(H)}$ time and give the true conditional score of the enlarged family to error $e^{-CH}$ whenever both cofactor coordinates stay averaged over the stipulated full-cycle width and the unfixed intercept and slope boxes have the stated intermediate lengths. The proof transfers the Gram references and the associated conditional expectations. It does not fix the cofactors, and it does not replace the separate low-mean and extractor hypotheses used to turn those expectations into a successful search.
