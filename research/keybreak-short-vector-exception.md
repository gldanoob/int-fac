# A short-vector exception bound for small modular squares

Let $N$ be a positive integer tending to infinity. Fix $2/3<a<1$ and $1-a<s<a/2$, and put $X=N^a$, $T=N^s$, $V=TX/N$. For a unit $z\bmod N$, write $u$ for its least positive square residue and consider the lattice
$$
\Lambda_z=\left\{(t/T,h/X):t,h\in\mathbb Z,\ h\equiv tz\pmod N\right\}.
$$
It has determinant $1/V$. There is an $\eta>0$ depending only on $a,s$ such that
$$
\#\{z\in(\mathbb Z/N\mathbb Z)^\times : u\le X,\
                 \lambda_1(\Lambda_z)\le N^\eta/V\}=O(N^{a-\gamma})
$$
for some $\gamma>0$ depending only on $a,s,\eta$. The norm in $\lambda_1$ can be Euclidean or the sup norm. This is an unconditional bound uniform in $N$. It counts exceptions for the lattice shape without a smoothness or distribution hypothesis.

## Primitive short vectors

Write $A=N^{1-a+\eta}$ and $B=N^{1-s+\eta}$. Choose
$$
0<2\eta<\min\{a+s-1,\ 3a/2-1,\ s\}.
$$
A short vector gives a nonzero pair $(t,h)$ with $|t|\le A$ and $|h|\le B$. Divide out any common factor in the integer lattice coordinates $(t,(tz-h)/N)$, using an integer lift of $z$, to obtain a primitive lattice vector no longer than the first. Both $A,B<N$. If $t=0$ then $N\mid h$, which forces the zero vector. If $h=0$, the same conclusion follows from $N\mid tz$ and the fact that $z$ is a unit. Negate the vector if needed to arrange $t>0$.

Let $g=\gcd(t,N)$. Because $\gcd(t,(tz-h)/N)=1$, we also have $\gcd(t,h)=g$. Thus $M=N/g$, $t'=t/g$ and $h'=h/g$ satisfy
$$
\gcd(t',M)=\gcd(t',h')=1,\qquad
h'^2=kM+t'^2u,\qquad
1\le t'\le A/g,\quad 0<|h'|\le B/g
$$
for an integer $k$. In particular, the square residue occupies one congruence class $u\bmod M$ for fixed $(t',h')$. For $g<N/X$, this class has at most one representative $1\le u\le X$.

## Counting when $g<N/X$

If $k=0$, coprimality forces $t'=1$ and then $u=h'^2$. The contribution is $O(\sqrt X)$ for each $g$. If $k\ne0$, reducing the displayed identity modulo $t'^2$ constrains $h'$ to the square roots of $kM$. Any root in a counted pair is a unit modulo $t'$, and therefore $kM$ is a unit modulo $t'^2$ if the class occurs. There are at most $2^{\omega(t')+1}$ such roots. The same bound allows $t'=1$. Indeed, a unit square has at most two roots modulo an odd prime power and at most four modulo a power of two, by CRT and the factorization of a difference of squares.

Fix $t'$ and consider $|h'|\le t'\sqrt X$ first. There are $O(t'^2 X/M)$ permissible nonzero integers $k$, since $|k|M\le t'^2X$. Counting both signs of $h'$ within its full range costs $N^{o(1)}(1+\sqrt X/t')$ for each $k$. Here $t'\le A\le\sqrt X$, by the inequalities on $a,\eta$, so the result is
$$
O\!\left(N^{o(1)}\,\frac{t'X^{3/2}}{M}\right).
$$

For $|h'|>t'\sqrt X$, use the dyadic bins $Y\le |h'|<2Y$ starting at $Y=t'\sqrt X$ and ending at $Y\le B/g$. Each bin has $O(Y^2/M)$ possible nonzero integers $k$. For given $k$, the condition $1\le u\le X$ puts $h'^2$ in an interval of length at most $t'^2X$, so its preimage in the bin has length $O(t'^2X/Y)$ on each sign. Counting residue classes modulo $t'^2$ costs $N^{o(1)}(1+X/Y)$ per $k$. Since $Y\le B/g\le X$, this is $O(N^{o(1)}X/Y)$, and the bin contributes $O(N^{o(1)}YX/M)$. When the bound on the magnitude of $k$ is less than 1 the nonzero count is zero. In particular neither estimate loses an additive $1$ in the $k$ count.

Sum the small range over $t'\le A/g$, and sum the dyadic large range using $\sum_Y Y\ll B/g$. For fixed $g$ the resulting estimate is
$$
O\!\left(N^{o(1)}\left(\sqrt X+\frac{A^2X^{3/2}}{Ng}
                                      +\frac{ABX}{Ng}\right)\right).
$$
Here and in the following estimates a divisor count and factors of the form $2^{\omega(m)}$ for $m\le N$ are uniformly $N^{o(1)}$. To see the divisor estimate, fix $\epsilon>0$. For large enough primes $p$, the contribution $e+1$ for an exponent $e$ is at most $p^{\epsilon e}$, and the finitely many smaller primes together contribute a fixed power of $\log N$.

## The large-gcd range and the power saving

For $g\ge N/X$, count all pairs $(t',h')$ in the given ranges and all representatives of the single class $u\bmod M$. This bounds the number for fixed $g$ by
$$
O\!\left(\frac{AB}{g^2}\left(1+\frac{Xg}{N}\right)\right)
=O\!\left(\frac{ABX^2}{N^2}\right),
$$
since $1\le Xg/N$ and $1/g\le X/N$. The same bound applies if a coordinate range is empty.

Finally, there are at most $2^{\omega(N)+1}$ unit roots $z$ of any one $u$. Counting all divisors $g$ and applying this root bound gives the claimed exception estimate in the more explicit form
$$
N^{o(1)}\,O\!\left(\sqrt X+\frac{ABX}{N}
                 +\frac{A^2X^{3/2}}{N}+\frac{ABX^2}{N^2}\right).
$$
The four exponents are $a/2$, $1-s+2\eta$, $1-a/2+2\eta$, and $a-s+2\eta$. The choice of $\eta$ makes every one strictly smaller than $a$. The bound thus applies also to any subset of residues selected by a further condition, but comparison with the size of such a subset requires an independent lower bound on that size.
