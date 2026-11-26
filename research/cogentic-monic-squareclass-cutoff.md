# A cutoff for square-class characters in the growing-degree monic fields

Under Dedekind GRH, exhaustive degree-one Legendre probes recover exactly the square-class kernel of any finite list of nonzero marked integral elements in a monic number field. The cutoff below is polynomial in the field degree, the bit length of the defining discriminant, and the total bit length of the marked norms. In the [monic one-third schedule](cogentic-monic-pair.md#homogeneous-norm-scale) the cutoff and the bit cost are $\exp(O(W))$ for $\exp(O(W))$ marks. The proof uses quadratic extensions of the original field of degree at most twice the original degree. It uses neither a normal closure over $\mathbb Q$ nor a multiquadratic extension joining the marks.

## Statement and probes

Let $f\in\mathbb Z[X]$ be monic irreducible of degree $d$, put $K=\mathbb Q(\alpha)$ with $f(\alpha)=0$, and let $\gamma_i=a_i-b_i\alpha\ne0$ for $1\le i\le R$. Write $n_i=|N_{K/\mathbb Q}\gamma_i|$ and
\[
    B_{\rm bad}=2|\operatorname{disc}(f)|\prod_i n_i,\qquad
    M=10+d+\operatorname{bitlength}(|\operatorname{disc}(f)|)
             +\sum_i\operatorname{bitlength}(n_i).
\]
Additional rational primes may be excluded by multiplying $B_{\rm bad}$ by any specified positive integer and adding its bit length to $M$. Put $t=\lceil\log_2(2M)\rceil$ and $X=(10^6 M t^2)^2$.

For every odd rational prime $p\le X$ coprime to $B_{\rm bad}$ and every $r\in\mathbb F_p$ with $f(r)=0$, take one binary row whose $i$th entry is zero or one according as the Legendre symbol of $a_i-b_i r$ is $+1$ or $-1$. All roots are simple and entries are nonzero before applying the Legendre symbol. Indeed, $p\nmid\operatorname{disc}(f)$ implies $p$ divides neither the field discriminant nor $[\mathcal O_K:\mathbb Z[\alpha]]$, and reducing at a root gives a degree-one ideal of $\mathcal O_K$ above $p$. Conversely every such ideal is represented by a root, since $\mathbb Z[\alpha]/p\mathbb Z[\alpha]\simeq\mathcal O_K/p\mathcal O_K$. The norm exclusion makes every column a local unit at every prime above $p$.

Assume GRH for $\zeta_K$ and for the Dedekind zeta functions of the nontrivial quadratic extensions $K(\sqrt{\beta})$ with $\beta=\prod_i\gamma_i^{e_i}$, $e\in\mathbb F_2^R$ represented by binary entries. The row kernel is
\[
       \left\{e\in\mathbb F_2^R:\prod_i\gamma_i^{e_i}\in K^{\times 2}\right\}.
\]
For every vector outside the kernel, at least $X/(4\log X)$ of the prime-ideal probes detect it, in particular at least $X/(4d\log X)$ distinct rational primes have detecting probes. Thus rank recovery does not require finding an ideal with a prescribed tuple of character values.

## Uniform quadratic discriminant and inert-prime count

For a nonsquare $\beta$ put $E=K(\sqrt\beta)$. It has degree $2d$ over $\mathbb Q$. The order $\mathcal O_K[\sqrt\beta]$ has relative trace discriminant $(4\beta)$ in its basis $1,\sqrt\beta$. Its absolute discriminant has absolute value $|\Delta_K|^2\,4^d\prod_{i:e_i=1}n_i$. The field discriminant divides this order discriminant, so
\[
   \log|\Delta_K|\le M,\qquad
   \log|\Delta_E|\le
   2\log|\operatorname{disc}(f)|+d\log4+\sum_i\log n_i\le 2M.
\]
Every prime ideal over a rational prime $p\nmid B_{\rm bad}$ is unramified in $E/K$. At a degree-one ideal, the quadratic extension is inert precisely when its Legendre symbol of $\beta$ is $-1$. This follows by factoring $T^2-\beta$ in the residue field. The order discriminant is a local unit there, so the order is the maximal order at that prime for this reduction.

Write $\psi_F(x)=\sum_{\mathfrak p,j\ge1:\,N\mathfrak p^j\le x}\log N\mathfrak p$ for a number field $F$. Corollary 1.2 of Grenié–Molteni gives, for $x\ge100$ under GRH for $\zeta_F$,
\[
 |\psi_F(x)-x|\le\sqrt x\left[
     \left(\frac{\log x}{2\pi}+2\right)\log|\Delta_F|
     +\left(\frac{\log^2 x}{8\pi}+2\right)[F:\mathbb Q]\right].
\]
[Grenié and Molteni, *Explicit versions of the prime ideal theorem for Dedekind zeta functions under GRH*, Corollary 1.2](https://sites.unimi.it/molteni/research/papers-pdf/33-molteni-Explicit_versions_of_the_prime_ideal_theorem_for_Dedekind_zeta_functions_under_GRH.pdf)

In $\psi_F(x)$ the total contribution at norms $p^j$ with rational $j\ge2$ is at most $[F:\mathbb Q]\sqrt x\log x$. For every $p^j$, the contributing residue degrees divide $j$ and their sum is at most $[F:\mathbb Q]$. There are at most $\lfloor\log x/\log p\rfloor$ such powers per prime $p\le\sqrt x$. The contribution at norms $p$ with $p\mid B_{\rm bad}$ is at most $[F:\mathbb Q]\log B_{\rm bad}$. These two deletions apply to each field separately.

After deleting both types from $2\psi_K(x)-\psi_E(x)$, a good degree-one ideal of $K$ contributes $2\log p$ if inert and zero if split. An ideal of larger residue degree cannot contribute a prime of degree one in $E$. With $\mathcal I_\beta(x)$ denoting the good degree-one inert primes of $K$ above $p\le x$, it follows that
\[
  2\sum_{\mathfrak p\in\mathcal I_\beta(x)}\log N\mathfrak p
      \ \ge\ x
           -\sqrt x\bigl[4M(\log x+2)+4d(\log^2 x+2)+4d\log x\bigr]
           -4d\log B_{\rm bad}.
\]
At $x=X$, the elementary inequalities $\log X\le20t$, $d\le M$ and $\log B_{\rm bad}\le M$ make the sum of the two errors less than $X/2$. Thus the weighted inert sum is at least $X/4$ and each term weighs at most $\log X$. An odd prime contributes at most $d$ ideals to this sum. This proves the asserted counts uniformly in $e$.

If $\beta$ is a square in $K$, its square root has valuation zero at all probe ideals, and every row annihilates $e$ by reduction. If $\beta$ is a nonsquare, a good inert prime supplies a row with dot product one, since the Legendre symbol is multiplicative. This gives the kernel equality. No union bound over the $2^R$ products is needed, since the cutoff bounds every product by the same discriminant and exclusion estimates.

## Deterministic cost and scope

The marked norms are the absolute homogeneous values $|b_i^d f(a_i/b_i)|$, with the homogeneous evaluation formula used also at $b_i=0$. The discriminant is an integer resultant of $f,f'$ up to sign. Computing both types of integer by direct polynomial arithmetic and determinants has bit cost polynomial in their input descriptions, and computing or using $B_{\rm bad}$ does not require factoring it. Sieve the primes through $X$, test the bad-prime condition by remainders, and find simple roots by scanning all $r\in[0,p)$ with Horner evaluation. This uses at most $X^2$ residue evaluations. For each of at most $dX$ root rows compute the symbols by Euler's criterion, then perform incremental Gaussian elimination over $\mathbb F_2$. An upper bound for the bit cost is
\[
 \operatorname{poly}(\text{input bit length})+
 X^2\operatorname{poly}(d,M,\log X)+
 dX\bigl(R\operatorname{poly}(M,\log X)+O(R^2)\bigr).
\]
There is no construction of $K$'s maximal order or of any extension $E$ in this algorithm. The row space requires at most $R$ pivot rows. For two fields, run the procedure for each field and stack the rows. Its kernel consists of combinations square in both fields. If both scans must exclude the norms and defining discriminants of both fields, multiply the exclusions for the other field into that scan's $B_{\rm bad}$.

On the monic pair schedule, $d$ and $d+1$ are polynomial in $L=\log N$ and the coefficient bit lengths are $O(V)$. Hadamard's inequality on the Sylvester determinant gives $\log|\operatorname{disc}(f)|=O(d(\log d+\log\|f\|_\infty))=O(L)$. Each nonzero homogeneous norm has $O(V)$ bits for marks of height $\exp(O(W))$, and even the entire bounded grid has only $\exp(O(W))$ points. Thus $M=O(L+RV)=\exp(O(W))$. The displayed cutoff and exhaustive bit cost are consequently $\exp(O(W))$.

The analytic assumption is Dedekind GRH for the specified extensions, or equivalently GRH for $\zeta_K$ and the corresponding quadratic Hecke $L$-functions using $\zeta_E=\zeta_K L_K(s,\chi)$. The Dirichlet hypothesis for characters over $\mathbb Q$ used by the other Cogentic arguments does not furnish these estimates in general. The probes certify square-class membership under this assumption. Constructing square roots, supplying a nontrivial productive dependency, and proving a complete factoring bound are separate steps.

A finite check in $\mathbb Q(\sqrt2)$ used the columns $\sqrt2,2,3,6,2+\sqrt2$. The 22 good root probes through $101$ gave exactly the kernel generated by the column for $2$ and the sum of the columns for $3$ and $6$. This agrees with the two visible square relations and independence of the classes of $\sqrt2$, $3$, and $1+\sqrt2$. Valuations over $2$ and $3$ detect the first two classes and the norm $-1$ detects the remaining unit.
