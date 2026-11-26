# Size and mark-length limits for exact conductor interpolation

An exact CRT sign supplies a splitting pair of integer residues when the prime-power partition is given. Even in a conductor with all signs available, the smallest such integer pair can have no representation by ordinary primitive marks. The obstruction below uses the common Eisenstein prime of the growing-degree monic pair.

## Least-height integer interpolation

Let $N=D_+D_-$ be odd with $D_+,D_->1$ coprime. A mixed sign is $+1$ on $D_+$ and $-1$ on $D_-$. If integer units $A,B$ modulo $N$ give this ratio, then $A-B$ and $A+B$ are nonzero multiples of $D_+$ and $D_-$, respectively. Consequently
\[
2\max(|A|,|B|)=|A-B|+|A+B|\ge D_++D_-.
\]
Equality is attained by $A=(D_++D_-)/2$ and $B=(D_--D_+)/2$. Both are units modulo $N$. The integer construction needs the partition as input.

For integral polynomial representatives of degree at most $k$ and coefficient height $H$, the evaluations at a common argument $m>1$ have absolute value at most $H\sum_{i=0}^k m^i$. Thus the same lower bound applies to a pair of such evaluations. On the [monic schedule](cogentic-monic-pair.md), $\log m\sim V$ and $\log N\sim d\log m$. For $H=\exp(O(W))$, even a balanced partition requires $k\ge(1/2-o(1))d$, and when $\max(D_+,D_-)=N^{1-o(1)}$ it requires $k\ge(1-o(1))d$. Signed rational polynomial representatives obey the same test after cross-multiplying their numerator and denominator evaluations, provided those denominators are units. If each cross product consists of at most $k$ ordinary linear marks of height $A_0$, its evaluation is at most $[A_0(1+m)]^k$. Taking $A_0=\exp(O(W))$ gives the same degree-scale lower bounds on the number of factors.

Given the partition one can write the half-sums in base $m$ using digits below $m$, with coefficient height $\exp(O(V))$ and $O(\log N)$ encoding bits. The height restriction concerns bounded coefficient search and representation by marks. The size of the integers alone does not make their arithmetic expensive.

## The least-height pair fails the primitive mark test

Take odd $d\ge3$, odd $m$, $N=m^d+2$, and
\[
F=X^d+2,\qquad G=F+(X-m)X^d.
\]
Assume a coprime nontrivial partition $N=D_+D_-$. Both polynomials are Eisenstein at two, with degrees $d,d+1$. At their unique primes above two, the normalized valuations send the generators $\alpha,\beta$ to one and send $2$ to $d,d+1$, respectively. A primitive mark $a-bX$ with odd $a$ has valuation zero on both sides. If $a$ is even, $b$ is odd and its valuation is one on both sides, since the rational term has strictly greater valuation than the generator term.

Suppose a signed word in primitive marks, multiplied by a common rational scalar $c$, represents $(A^2,B^2)$ in the two fields. Write $n$ for the signed sum of exponents of the even-$a$ marks and $t=v_2(c)$. The two valuation equations are
\[
n+dt=2d\,v_2(A),\qquad
n+(d+1)t=2(d+1)\,v_2(B).
\]
For the least-height half-sums, $A$ and $B$ have opposite parity because $A-B=D_+$ is odd. With only primitive marks and a shared sign, $t=0$ and the two equations are incompatible. Even allowing arbitrary rational content, elimination gives
\[
n=2d(d+1)\bigl(v_2(A)-v_2(B)igr).
\]
Hence any representing word uses at least $2d(d+1)$ even-$a$ mark occurrences, counted with repetition and with the absolute lengths of its numerator and denominator. Multiplying both roots by one rational scalar preserves the valuation difference and the same length lower bound. A pool excluding the norms divisible by two therefore cannot represent this pair even with rational content.

At height $A_0=\exp(\Theta(W))$, a direct list of all words at even the degree-scale length from the integer bound can already have $\exp(\Theta(dW))=\exp(\Theta(V))$ distinct multisets of factors. The valuation bound further raises the length required for this particular interpolation. These are restrictions on interpolation and enumeration. They impose no corresponding lower bound on an algorithm that computes a relation from a supplied lattice.

## The canonical conductor polynomial also fails to split

Set $H_m=(X^d-m^d)/(X-m)$. For the half-sums above, $A^2-B^2=N$. The unique representative of degree below $2d+1$ over $\mathbb Q$ of the two constant squares is
\[
\tfrac12 T,\qquad T=2B^2+G H_m.
\]
Indeed $G\equiv-2(X-m)\pmod F$ and $(X-m)H_m\equiv -N\pmod F$, while $G H_m\equiv0\pmod G$. The polynomial $T$ is monic of degree $2d$. Modulo two it is $X^{d+1}(1+X+\cdots+X^{d-1})$. The second factor has degree $d-1>0$ and no root in $\mathbb F_2$ since $d$ is odd. If $T$ split into rational linear factors, monicity would make its roots integers and force its reduction to split into linear factors too. Thus canonical conductor interpolation gives a square pair whose representative is outside the signed linear-factor group in $\mathbb Q(X)$.

As a separate degree test, suppose a signed word $P/Q$ is a simultaneous square with representatives $U_i/V_i$ in the two fields. If $\max(2\deg U_i+\deg Q,2\deg V_i+\deg P)$ is below the degree of either corresponding defining polynomial, then the congruence $U_i^2Q=V_i^2P$ is already an identity over $\mathbb Q[X]$. In this case $P/Q$ is a rational square in $\mathbb Q(X)$. Because all the mark reductions are units, the rational-function root can be taken as a product of the same primitive linear factors with halved exponents and a rational scalar. Its evaluations agree at $m$, so the [sign class](cogentic-square-kernel-splitting.md) is trivial.

For a finite check, $d=3$, $m=11$ gives $N=1333=31\cdot43$, unit derivatives at the common argument, and half-sums $A=37$, $B=6$. The gcd of $A-B$ and $N$ is $31$. Direct polynomial reduction verifies the two square residues of $T/2$, and $T\bmod2=X^4(X^2+X+1)$. The signed mark count forced by the valuation equations is $-24$.

The valuation obstruction applies to the least-height constant roots and their common scalar multiples. The same modular sign can have different lifts, including integers of equal two-adic valuation and nonconstant field elements. This argument leaves such lifts and their ordinary mark representations open. [Conductor gluing and the mark lattice](cogentic-conductor-signs.md)
