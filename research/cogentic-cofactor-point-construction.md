# Constructing one or two prescribed smooth marks in the cofactor family

The enlarged fixed-schedule family admits deterministic construction of actual coefficients at one prescribed clean mark, or at two well-separated prescribed clean marks, in $\exp(O(H))$ bit operations. This uses the original full-width intercept and slope boxes. It uses the Dirichlet-RH prime-sum estimate and gives explicit smooth norm factorizations, including the exclusions from the two resulting cofactors. It gives no small Gram score or selection inside the intermediate-width boxes. [Cofactor family and its scalar estimators](cogentic-cofactor-dispersion.md)

## Constructing a squarefree product with a prescribed unit residue

Keep the fixed parameters, with $\log B=(1000+o(1))H$ and $\log Y=(100001+o(1))V$. Take a target residue $r$ which is a unit modulo $q$. We need either $q\le P_0\ell$ or $q\le P_0\ell A^2$, and may omit polynomially many primes in $\log N$. Let $Z=\lfloor B^{9/10}\rfloor$ and take the smallest integer $t$ for which $Z^t\ge Y$. Let $P=\lfloor Y^{1/t}\rfloor$, $\eta=B^{-1/8}$, and choose an integer $J\asymp \eta P/(100t)$ by integer root computations. Then $t\asymp V/H$ and $\log P=(900+o(1))H$. All primes in $[P,P+J]$ are in $(\sqrt B,B]$, and the product of any $t$ of them is $Y(1+O(\eta/100))$. Indeed $P$ differs from $Y^{1/t}$ by at most one, and $t/P=o(\eta)$.

Partition this strip into $b+1$ disjoint consecutive pieces of comparable length, where $b=4$ for the smaller modulus bound and $b=70$ for the larger one. Take $t-b$ distinct eligible primes in the first piece and let $M_0$ be their product. In each of the remaining $b$ pieces we will select one prime to make the final product congruent to $r$. Delete primes dividing $q$ and the prescribed omission list from all pieces. Dirichlet RH gives, for each piece and nonprincipal $\chi\bmod q$, an unweighted prime sum $O(\sqrt P\operatorname{poly}(\log(Pq)))$. This follows by partial summation of the prime estimate, with the specified deletions changing either count by at most a polynomial in $\log N$. The principal number of primes is $\exp((775+o(1))H)$ because the piece length is $\eta P\exp(o(H))$ and is larger than the RH error. Thus the magnitude of every normalized nonprincipal character mean in a piece is at most $\exp((-325+o(1))H)$. This is uniform in the stated moduli. [Prime character estimate and deletions](cogentic-dirichlet-smooth-windows.md#an-individual-character-estimate)

By character orthogonality, the fraction of terminal tuples giving product $r/M_0$ modulo $q$ is at least
\[
     \frac{1}{\varphi(q)}-\exp((-325b+o(1))H)>0 .
\]
For $b=4$ use $\log q\le(1000+o(1))H$. For $b=70$ use $\log q\le(21000+o(1))H$. Disjoint pieces make the factors distinct. The primes and the terminal tuple can be found by sieving through $B$ and enumerating at most $B^b$ tuples. Exact integer powers suffice to set the strip. The cost is $\exp(O(H))$, and the chosen product comes with its squarefree factorization.

## From constructed products to genuine coefficients

Write $g=P_0\ell$ and use in each field
\[
 f(X)=f^{(0)}(X)+gkR(X)+g(X-m)(x+Xy),\qquad k_*(k)=k_0+gk.
\]
Here $R(X)$ is the base-$m$ digit polynomial for $N$. At a mark $a$ put $n_a=m-a$ and $R_a=R(a)$. We require a mark at which $f_i^{(0)}(a)$ is a unit modulo $gn_a$ in both fields, as for the clean marks of the fixed grid. In particular $R_a$ is invertible modulo $n_a$. We may choose the original cofactor width $K$ at least $A m^2$ times a sufficiently large fixed power of $\log N$, rounded up to a power of two. This still has $K=m^2\exp(O(H))$. The term $R_aK/n_a$ is at most $\exp((10002+o(1))V)$, negligible relative to $U$. These bounds also hold with $k$ restricted to any interval of comparable length inside the enlargement. [Original perturbation and marked heights](cogentic-cofactor-dispersion.md#a-coefficient-that-varies-the-residue-at-every-mark)

For one mark, prescribe the slope near the middle of its original box, and take $x_c$ at the midpoint of the original intercept interval. Set $M=f^{(0)}(a)-gn_a(x_c+ay)$, and construct a squarefree product $P_a$ near $|M|$ with $\operatorname{sgn}(M)P_a\equiv M\bmod g$. Exclude the band primes dividing $gn_a$. The equation
\[
 R_a k-n_a(x-x_c)=\frac{\operatorname{sgn}(M)P_a-M}{g}
\]
first fixes one residue class of $k\bmod n_a$ and then gives an integer $x$. The original height rule gives $|M|/(gn_a UA)\le\exp((100+o(1))H)$. Thus the product error divided by $gn_a$ is $o(UA)$ because $\eta=\exp((-125+o(1))H)$. The cofactor displacement is smaller still, so the constructed $x$ is in the original interval.

For two marks $a_1<a_2$, put $\Delta=a_2-a_1$, $n_i=m-a_i$ and $G=\gcd(n_1,n_2)$. Assume $\Delta\ge A B^{-1/100}$. Choose a central slope $y_c$ and move the central intercept by at most $\Delta$ in each field to ensure that both central marked values
\[
                 M_i=f^{(0)}(a_i)-gn_i(x_c+a_i y_c)
\]
are units modulo $q=g\Delta G$. Primes dividing $g$ or $G$ already see units by the clean-mark conditions. For any other prime dividing $\Delta$, the two marks coincide modulo the prime, so the two values give the same affine expression in $x_c$ with invertible slope. Prescribe its residue to be one and combine these choices by CRT. Trial division through $A$ suffices to find these primes.

Construct each $P_i$ near $|M_i|$ with $\operatorname{sgn}(M_i)P_i\equiv M_i\bmod q$. Omit all band primes dividing $gn_1n_2\Delta$, so future cofactor shifts are invertible at every chosen factor. Write $w_i=(\operatorname{sgn}(M_i)P_i-M_i)/(g\Delta)$, a multiple of $G$. Put $k=\Delta k'$. The pair of congruences
\[
                    R_{a_i} k'\equiv w_i\pmod{n_i}
\]
is solvable because the prescribed classes both vanish modulo $G$. Its solutions give a cofactor class modulo $P_{\rm step}=\Delta\operatorname{lcm}(n_1,n_2)\le A m^2$. The shifts requested at the two marks are
\[
                e_i=(R_{a_i} k-\Delta w_i)/n_i .
\]
They are integers divisible by $\Delta$. Hence $y-y_c=(e_2-e_1)/\Delta$ and $x-x_c=e_1-a_1(y-y_c)$ are integers. The product error gives
\[
    |e_i|\le R_{a_i}K/n_i+O\!\left(\eta|M_i|/(gn_i)\right)=o(U\Delta).
\]
For the second term use $|M_i|/(gn_i UA)\le\exp((100+o(1))H)$ and $A/\Delta\le B^{1/100}=\exp((10+o(1))H)$. The first term is negligible on the $V$ scale. Consequently $|y-y_c|=o(U)$ and $|x-x_c|=o(UA)$, so both coordinates remain in their original boxes. This construction does not cover arbitrarily close pairs.

Apply the construction separately in the two fields, postponing the choice of a particular cofactor within each solved cofactor class until all norm products are known. Let $s$ be the total number of distinct chosen rational primes. For either field, take $s+1$ consecutive representatives of its solved class in the allowed cofactor interval. Such a list fits because $s$ is polynomial in $\log N$ and the class period is at most $A m^2$. Every chosen prime is coprime to the product of $g$ and the cofactor period. Because each chosen prime exceeds $s+1$, it divides the cofactor $k_*(k)$ for at most one of these $s+1$ choices. At least one choice avoids every selected prime. Also, the constructed values are coprime to $n_a$ at each selected mark. The identity $f(a)\equiv k_*(k)N\bmod n_a$ then proves that each mark passes the changing cofactor eligibility test. Thus the true squarefree norm tests in both fields pass with both cofactors fixed.

A small exact check used $m=30$, $N=361$, $g=5$, $R(X)=1+12X$, marks $10,14$ and initial polynomials $361$ and $361+5(X-30)$. It used a deliberately small arithmetic fixture rather than the asymptotic prime strips. For the first field the solved $(k,x,y)=(128,-746,143)$ gives the norms $7\cdot17\cdot79$ and $11\cdot17\cdot43$. For the second, $(16,-166,17)$ gives $7\cdot29\cdot47$ and $11\cdot17\cdot43$. Both cofactor classes pass all chosen-prime omissions and the unit tests at the two marks.

## What the width estimates give when the axes are exchanged

For the fixed interval replacement and counting-norm argument, use exponents $\tau=\log T/V$ and $\kappa=\log K'/V$ for an intercept progression and the averaged cofactor interval. Write $\lambda=100001$ and $r=\log |R_a|/V$ when $R_a\ne0$. The latter is bounded above by $10001+o(1)$ on the conservative schedule. At leading-exponent precision, the sufficient inequalities for horizontal intercept counting are
\[
 r+\kappa<1+\tau,\qquad 1+\tau>\lambda/2,\qquad
 \tau+\tfrac12\min(1,\kappa)>\lambda/2 .
\]
The first controls endpoint freezing, the second the untwisted saddle count, and the third the counting norm of the cofactor orbit. Full-cycle pooling changes the third to a cycle-length requirement of up to exponent two for two marks and retains the untwisted threshold $\tau>\lambda/2-1$. In the counting-norm region with $\kappa>0$, direct scanning one remaining intercept and its cofactor costs at exponent $\tau+\kappa>\lambda/2+\kappa-\min(1,\kappa)/2$. Full two-mark cycles likewise have $\tau+\kappa>\lambda/2+1$ when using the complete-cycle width. The individual sharp counter allows fixing the cofactor before scanning when $\tau>\lambda/2$, so these bounds alone give no improvement to the leading exponent of a direct residual scan.

For a single mark, exchange the intercept and cofactor even in the favorable case where all relevant cofactor classes are units modulo the new scalar step $g|R_a|$. The cofactor progression now has length $K'$ and the averaged intercept orbit has period $|R_a|$, since $n_a$ is coprime to $R_a$. The swapped sufficient inequalities are
\[
      1+\tau<r+\kappa,\qquad r+\kappa>\lambda/2,\qquad
      \kappa+\tfrac12\min(r,\tau)>\lambda/2 .
\]
A complete cycle instead needs $\tau\ge r$ up to the chosen secondary margin, and still needs the middle inequality. Even with an enlarged cofactor range, both the norm and cycle regimes give $\tau+\kappa>\lambda/2$ for a direct residual scan. On the stipulated cofactor range $\kappa\le2+o(1)$ gives $r+\kappa\le10003+o(1)$, so the middle inequality already fails. Even dividing out any common marked divisor of exponent $\gamma\ge0$ makes the physical-width condition $r+\kappa-\gamma>(\lambda-\gamma)/2$, which is stronger.

Splitting into frozen-endpoint panels instead of freezing the whole current interval also has a quantitative cost. For the original horizontal direction one panel with endpoint loss at most $\epsilon T$ can cover at most $1+O(\epsilon n_a T/|R_a|)$ consecutive cofactor positions. If $r+\kappa>1+\tau$ with a fixed positive gap and $r<1+\tau$, the required number of such panels at $\epsilon=\exp(-O(H))$ has leading exponent $r+\kappa-1-\tau$ on the $V$ scale. In the swapped direction exchange the two physical widths in the same formula. These are bounds for the frozen-endpoint procedure. The direct product construction instead uses the full-width physical window at isolated marks and does not estimate the whole score.
