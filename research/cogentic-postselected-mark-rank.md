# Rank consequences of clean marks chosen after the fields are fixed

One can enumerate and test every integer mark in the fixed-schedule grid in $\exp(O(H))$ bit operations once both coefficient tuples are fixed. The conclusions below hold for any subset of retained common smooth marks, even if selected adaptively after the norms and row labels are known. They give an ordinary incidence-rank lower bound and exclude sparse dual obstructions to target and logarithm rank. They also show why a few explicitly constructed smooth marks, or a list consisting only of protected-root marks, cannot supply an order certificate by themselves. The supply of enough suitable marks for a fixed constructed pair remains open.

## Ordinary rank and the minimum size of a cancellation

Let $S\subseteq[1,A]$ be the chosen set of distinct clean marks. Use squarefree band smooth values at both fields, discarding forbidden prime divisors and nonsimple rows as in the extractor. Ordinary rows have labels $(i,p,r)$, where $i$ is the field, $p$ is in $(\sqrt B,B]$ and $r$ is its root residue. The first field's protected target rows at $\ell$ are kept out of the ordinary matrix. The second field has no root modulo $\ell$. Write $S_i(a)$ for the ordinary support in field $i$ of column $a$, and let $w_i=\min_{a\in S}|S_i(a)|$.

A common row of two distinct columns forces $p\mid a-a'$. The primes shared in one field are distinct and their product divides $|a-a'|$. Hence each pair shares at most
\[
     c_i=\left\lfloor\frac{2\log A}{\log B}\right\rfloor
\]
ordinary rows in that field. One can replace $c_i$ by the exact maximum overlap for the selected columns. The fixed-schedule marked heights give $w_i=\Omega(V/H)$ because each norm factor is at most $B$ and the protected factor costs at most one entry. In particular $w_i>c_i$ eventually. [Fixed heights and band](cogentic-deterministic-two-thirds.md#the-grid-its-sieve-and-its-real-roots)

If a nonzero coefficient vector cancels all ordinary rows and uses $s$ marks, each ordinary row at each supported mark must occur in another supported column. In field $i$ the other $s-1$ columns can cover at most $c_i(s-1)$ such rows. Hence
\[
                         s\ \ge\ 1+\max_i \lceil w_i/c_i\rceil
\]
over any coefficient field, with no nonzero cancellation if $c_i=0<w_i$ in either field. This applies even if $S$ itself is large. On this schedule it requires $\Omega(V/H)$ nonzero mark coefficients for any protected-target relation with nonzero exponent. Thus knowing how to construct one or two smooth marks does not supply a target relation without other columns. [Prescribed smooth mark construction](cogentic-cofactor-point-construction.md) · [Target equations](cogentic-collective-field-extraction.md)

There is also a lower bound on rank in a large observed set. In any one chosen field, or across both, let $c$ be the corresponding pairwise overlap bound and assume the ordinary column weights exceed $c$. Let $r$ be the incidence rank over any field. Restrict the columns to $r$ independent rows. Their restricted supports are distinct, because equality on a row basis would give identical original columns. Two restricted supports still meet in at most $c$ entries. At most $\sum_{j\le c}\binom rj$ supports have size at most $c$. Each larger support can be assigned one $(c+1)$-subset, and no two receive the same subset. Thus
\[
               |S|\le\sum_{j=0}^{c+1}\binom rj\le(r+1)^{c+1}.
\]
In particular $r\ge |S|^{1/(c+1)}-1$. Either single field yields this with its own $c_i$, and the joint rank is at least the larger single-field bound. This gives exponential ordinary rank on the $H$ scale for exponentially many observed marks. Ordinary column rank alone neither produces a cancellation nor places the target vector in its required image.

## Which dual obstructions require many ordinary rows

Let $S_0$ be the off-target selected marks and $S_j$ the marks in the $j$th protected residue class modulo $\ell$. Let $n_0=|S_0|$ and $n_j=|S_j|$. An ordinary row covers at most $A/\sqrt B+1$ marks in $S_0$ and at most $A/(\ell\sqrt B)+1$ in each $S_j$. For the second bound, its prime differs from $\ell$, so the joint root conditions give one CRT class modulo $p\ell$. Denote these respective upper bounds by $M_0$ and $M_j$. They can be replaced by the actual largest coverage observed in each class.

Consider any real left dependency of the matrix of ordinary incidence, protected incidence, the field-sum row, and the trace-zero logarithm rows. In the common-mark parametrization it gives, on $S$,
\[
  g(a)+\sum_{r\ \mathrm{ordinary}} c_r\,1_r(a)
          +\sum_j b_j\,1_{S_j}(a)=0,\qquad
  g(x)=b+\sum_{\theta}h_\theta\log|x-\theta| .
\]
Here the roots from both fields are real and distinct as in the fixed schedule. The coefficients within each field sum to zero because the logarithm rows are trace-zero. Put $D_{\rm arch}$ for the total number of roots. If some $h_\theta$ is nonzero, then $g'$ is a nonzero rational function, with numerator degree at most $D_{\rm arch}-2$ after multiplying by $\prod_\theta(x-\theta)$. The highest term vanishes because $\sum_\theta h_\theta=0$, and distinct roots ensure that the residues cannot cancel identically. Rolle's theorem on the root-free intervals gives at most $2D_{\rm arch}-1$ distinct zeros of $g$ across all of them. In any one root-free interval the bound is $D_{\rm arch}-1$. If all $h_\theta=0$, one zero suffices to make $g$ identically zero.

Suppose the ordinary coefficient support has size $k$. At least $n_0-kM_0$ off-target marks avoid every supported ordinary row. If
\[
             n_0-kM_0>2D_{\rm arch}-1 ,
             \qquad n_j>kM_j\quad\text{for every protected class }j ,
\]
the first inequality makes $g$ identically zero, and each subsequent inequality gives a mark forcing $b_j=0$. Thus any dependency involving logarithm or protected coefficients needs at least
\[
       \min\!\left\{
          \frac{n_0-(2D_{\rm arch}-1)}{M_0},
          \min_j\frac{n_j}{M_j}\right\}
\]
ordinary rows whenever this bound is positive. The off-target test can instead be made in a single root-free grid interval, with its own mark count, coverage bound and smaller zero bound. The protected coverage tests can similarly use a favorable subinterval in each class.

For instance, measured populations $n_0\ge A\exp(-(\sigma+o(1))H)$ and $n_j\ge (A/\ell)\exp(-(\sigma+o(1))H)$ for every protected class give a lower bound $\exp((500-\sigma+o(1))H)$ when $\sigma<500$. This uses only the observed marks and the arithmetic row labels. Dense ordinary dependencies are still possible, so the argument is weaker than full Gram positivity. In the other direction, if all selected marks are protected, their protected row sum equals the field-sum row on those columns. The field-sum equation then forces the target exponent to be zero, regardless of the number of protected marks. Off-target marks are therefore essential.

## Exact check on a fixed pair

Take $N=77$, $m=9$, $P_1=X^2-158$, $P_2=X^2-312$, mark bound $3000$ and band $(\sqrt{499},499]$. Both polynomials are irreducible, have distinct real roots, and take values divisible by $77$ at $9$ with unit derivatives. The prime $\ell=131$ has first-field roots $17,114$ and no second-field root. Enumerating the unit marks and testing the squarefree band norms and simple rows gives nine marks, namely $1,7,11,17,25,77,85,115,245$. The two protected classes are both represented, by $17$ and $245$. The maximum ordinary overlap is one and every column has a private ordinary row, so the ordinary matrix has rank nine and allows no target cancellation. This checks directly that hitting every protected residue in the selected smooth set does not give a target relation.
