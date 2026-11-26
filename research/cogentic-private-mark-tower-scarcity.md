# Private small marks constrain the height of tower polynomials

Let $F\in\mathbb Z[x]$ be primitive and irreducible, of degree $d$ and positive leading coefficient. Suppose the field of a root has a subfield $E$ of degree $e\ge2$ and relative degree $q=d/e\ge2$. At distinct primitive marks $(a_i,b_i)$ with $|a_i|,b_i\le A$ and $b_i\ge1$, write $n_i=b_i^d F(a_i/b_i)$. Suppose $0<|n_i|\le T$. Either marking condition below forces
\[
 \log \|F\|_\infty=O(\log T+d\log(2A)),
\]
with an absolute implied constant.

- There are $d$ marks. Each has a prime of valuation one in its value and valuation zero in every other marked value.
- The polynomial is monic and there are $d-1$ marks. Each has a prime of valuation one in its value. A prime may recur across marks.

In particular, take $X\le N<2X$, $L=\log X$, $D=(L/\log L)^{1/3}$, $d=O(D)$, $A=\exp(O(D\log L))$ and $T=\exp(O(D^2\log L))$. If the field has a tower from $\mathbb Q$ with maximum step degree $o(D)$, either marking condition gives the small-height tower bound. For adaptive primitive radices $(u,v)$ of height $\exp(O(D^2\log L))$, only $X^{o(1)}$ integers in the dyad divide a nonzero homogeneous value $v^dF(u/v)$ from this model. No initial coefficient bound is needed. [Small-height tower count](cogentic-full-tower-height-scarcity.md) · [Construction with private valuation rows](cogentic-short-field-list.md)

## Isolating roots from the marks

Set $t_i=a_i/b_i$ and $P(x)=\prod_i(x-t_i)$. The $t_i$ have magnitude at most $A$ and separation at least $A^{-2}$. Let $R$ be the Lagrange interpolant of degree less than the number of marks, with $R(t_i)=n_i/b_i^d$. Its coefficient height and its supremum on $|z|\le A+1$ are at most $T(CA)^{Cd}$ for an absolute $C$. Each Lagrange denominator is a product of differences of magnitude at least $A^{-2}$, and the numerator products have factors of magnitude at most $2A+1$ on the disk. Expanding the same products bounds the coefficients.

In the $d$-mark case write $F=lP+R$, where $l>0$ is the leading coefficient. In the monic $d-1$-mark case write $F=P(x)(x-s)+R$. Let $B=l$ in the first case and $B=|s|$ in the second. There is a common $K=T(CA)^{Cd}\ge2$, by increasing the absolute $C$, such that whenever $B\ge K^4$ each mark has exactly one root of $F$ within $K/B$. On the circle of that radius the marked factor has magnitude $K/B$ and every other marked factor has magnitude at least $(2A^2)^{-1}$. The linear factor $z-s$ in the monic case has magnitude at least $B/2$. The leading term in either interpolation formula dominates $R$ there, and Rouché's theorem gives the root. It is real by conjugation. In the monic case the remaining root $\beta$ is also real and satisfies $|\beta-s|\le(d-1)K/B$ by the sum of roots. When $B<K^4$, the interpolation formulas already give the desired coefficient height.

## The $d$-mark case

Write $F=l\prod_{\sigma:E\hookrightarrow\mathbb C}\sigma G$, with $G$ the monic relative minimal polynomial of degree $q$. The relative factors partition the roots into groups of size $q$. The denominator ideal $\mathfrak d$, defined by $\mathfrak d^{-1}=\mathcal O_E+\sum_j\mathcal O_E G_j$ for the coefficients $G_j$ of $G$, has norm $l$. This uses primitivity and multiplicativity of the nonarchimedean Gauss norm. [Denominator ideal identity](cogentic-full-tower-height-scarcity.md#towers-with-varying-relative-degrees)

Choose two marks $i,j$ whose nearby roots belong to the same group. Put $c_k=b_k^q G(t_k)$ for $k=i,j$ and $y=c_i/c_j$. Then $l\operatorname{Nm}_{E/\mathbb Q}(c_k)=n_k$, and the denominator ideal of $y$ divides $(c_j)\mathfrak d$. Indeed $c_i\mathfrak d$ and $c_j\mathfrak d$ are integral ideals, so $y(c_j)\mathfrak d$ is integral. The denominator ideal thus has norm at most $|n_j|\le T$. At any embedding outside the chosen group, mark separation gives $(CA)^{-Cq}\le |\sigma c_k|\le(CA)^{Cq}$. At the embedding of the chosen group the norm identity gives
\[
 \frac{1}{l(CA)^{Cd}}\le |\sigma c_k|\le \frac{T(CA)^{Cd}}{l}.
\]
It follows that $|\sigma y|\le(CA)^{Cq}$ outside that group, and $|\sigma y|\le T(CA)^{Cd}$ in it. Here and below the absolute constants in powers of $CA$ may increase.

Choose any one of the other groups. Replace its actual roots by their nearby marks in the two products $b_k^q\sigma G(t_k)=\prod_{\alpha\text{ in group}}(a_k-b_k\alpha)$. The ratio of the resulting products is a rational number $r$ of magnitude and reduced denominator at most $(CA)^{Cq}$. Each rational factor has denominator at most $A$ and numerator at most $2A^2$. Telescoping the products and using separation to bound the denominator of the ratio gives $|\sigma y-r|\le (CA)^{Cq}K/l$ at this embedding. Multiplying this bound by the bounds on the other conjugates yields
\[
 |\operatorname{Nm}_{E/\mathbb Q}(y-r)|\le \frac{TK(CA)^{Cd}}{l}.
\]
If $y-r\ne0$, the same absolute norm is at least $1/[T\operatorname{den}(r)^e]$. In fact multiplying $y-r$ by the product of its two summands' denominator ideals makes it integral, and those ideals have norms at most $T$ and $\operatorname{den}(r)^e$. Since $qe=d$, the two norm bounds force $y=r$ for $l$ above a sufficiently large absolute power of $K$. But $\operatorname{Nm}(y)=n_i/n_j$ has valuation one at the private prime of $i$. The norm of a rational element of $E$ is its $e$-th power. This rules out the large range of $l$ and proves the height bound. Only a prime of valuation one in the norm ratio of some pair from one group is needed in this argument.

## The monic $d-1$-mark case

Choose a companion mark $i$ in the group containing the large root $\beta$. Put $y=b_i^qG(t_i)$. The coefficients of $G$ are integral since its roots are algebraic integers, so $y\in\mathcal O_E$. Its conjugate in the group containing $\beta$ is at most $K(CA)^{Cq}$ in magnitude. The nearby root gives a factor of size at most $AK/B$, the large root gives a factor of size $O(AB)$, and the other factors have size $O(A^2)$. All other conjugates have magnitude at most $(CA)^{Cq}$.

In one of the groups with only bounded roots, replace the roots by their nearby marks as before. The resulting value $r$ is rational of magnitude and denominator at most $(CA)^{Cq}$, with $|\sigma y-r|\le(CA)^{Cq}K/B$ at that embedding. Thus $|\operatorname{Nm}(y-r)|\le K^2(CA)^{Cd}/B$, whereas if $y-r\ne0$ its norm has magnitude at least $\operatorname{den}(r)^{-e}$. Above a sufficiently large absolute power of $K$ this forces $y=r$. The norm of $y$ is $n_i$, whose prime of valuation one precludes a rational $y$. This proves the height bound in the monic case. The argument needs this prime only for one companion mark of the large root.

With additional missing marks the interpolation leaves further free coefficients. The root grouping above uses the precise number of marks in each case.

## High-height quartics with unit or square norms

Let $Q_n(Y)=Y^2+2nY-5n-6$ and set
\[
 F_n(x)=x^2Q_n(x+x^{-1})=x^4+2nx^3-(5n+4)x^2+2nx+1.
\]
If $n\equiv2\pmod3$, its reduction is $x^4+x^3+x^2+x+1$, irreducible because the order of three modulo five is four. A root $\alpha$ generates a quadratic tower with intermediate generator $\alpha+\alpha^{-1}$. The three marks $0,2,1/2$ have homogeneous value one, using $4Q_n(5/2)=1$ at the reciprocal pair. The coefficient height grows with $n$.

For each sufficiently large odd input $N$, first take $\gcd(15,N)$. A nonunit gives a proper divisor. Otherwise choose $n\ge N$ by CRT with $n\equiv2\pmod3$ and $n\equiv-46/15\pmod N$. The evaluation $F_n(3)=46+15n$ vanishes modulo $N$ and $F_n'(3)=84+26n\equiv64/15\pmod N$ is a unit. This gives the quartic tower with three unit-norm marks and a simple modular reduction in polynomial bit work. The identities give no productive square relation.

For the primitive nonmonic case take $F_n=x^2[1+n(2(x+x^{-1})-5)(3(x+x^{-1})-10)]$ with $n>0$ and $n\equiv3\pmod{11}$. Its coefficients $6n,-35n,62n+1,-35n,6n$ have gcd one. Modulo eleven its monic normalization is $x^4+7x^3+7x+1$, coprime to $x^{121}-x$ and hence irreducible. The same intermediate generator gives a quadratic tower. The marks $2,1/2,3,1/3$ have homogeneous values $4,4,9,9$, while the leading coefficient grows without bound.

## The unique affine root prescription

The private-row construction also prescribes exactly one affine root, simple, modulo each assigned prime. A nontrivial complete quadratic tower cannot meet that prescription in a monic model. At any rational prime $p$, each $\mathbb Q_p$ factor degree is a power of two, since degrees multiply along completed quadratic towers. The total degree is even, so the number of local degree-one factors is even. Any simple root modulo $p$ lifts to a linear factor by Hensel's lemma. A second $\mathbb Q_p$ root is integral by monicity and reduces to a different affine root by uniqueness of the lift. For a primitive nonmonic model, the same argument uses projective roots with primitive $p$-adic coordinates. The additional root can be outside the marked set, so the local restriction still permits a private valuation among selected marks.
