# A deterministic monic pair at the one-third norm scale

For every odd integer $N\ge9$, the construction below gives two monic irreducible integer polynomials of consecutive degrees with a common argument $m$ at which both values equal $N$. It uses exact arithmetic and no input factorization. [Constructive replay](../experiments/cogentic-monic-pair.py)

## Construction and carry

Take $d\ge2$ and the greatest odd integer $m\le N^{1/d}$, with $m\ge3$. Then $m^d\le N<(m+2)^d$. Put $K=(N-m^d)/2$ and write $K=mq+r$ with $0\le r<m$. If $r$ is odd, use $c_0=r$. If $r$ is even, use $c_0=r-m$ and increment $q$. In both cases $c_0$ is odd and $K=c_0+mq$. This also handles the case $K=0$, where $c_0=-m$ and the new quotient is one.

Extract exactly $d-2$ ordinary base-$m$ digits from the quotient, giving $c_1,\ldots,c_{d-2}$, and set $c_{d-1}$ to the remaining quotient. The highest coefficient is allowed to exceed one radix digit. In particular, rounding down to an odd $m$ does not force a polynomial of larger degree. The identity $K=\sum_{i=0}^{d-1}c_i m^i$ is exact. Define

$$
F(X)=X^d+2\sum_{i=0}^{d-1}c_iX^i,\qquad
G(X)=F(X)+(X-m)X^d.
$$

The coefficient of $X^d$ in $G$ is $1-m$, which is even. Both polynomials have all nonleading coefficients even and constant $2c_0\equiv2\pmod4$. Eisenstein's criterion at two gives irreducibility. Their fields have degrees $d$ and $d+1$, hence are distinct. Both evaluations at $m$ give exactly $N$ and induce evaluation homomorphisms from their power orders to $\mathbb Z/N\mathbb Z$.

## Height and construction cost

All digits except possibly $c_{d-1}$ have absolute value at most $m$. Ordinary division after the parity carry gives

$$
0\le m^{d-1}c_{d-1}\le K+m<d(m+2)^{d-1}+m.
$$

The last bound follows by telescoping $(m+2)^d-m^d$. When $d=2$, the sharper bound $K<2m+2$ follows by expanding $(m+2)^2-m^2$. Since $m\ge3$, the initial quotient $\lfloor K/m\rfloor$ is at most two. The parity carry adds at most one, giving $c_1\le3\le m$. When $m\ge4d$, it gives $c_{d-1}<d\exp(2(d-1)/m)+1<2d+1\le m$. Thus $F$ and $G$ both have coefficient height at most $2m$ in these cases.

Let $\ell$ be the binary bit length of $N$ and $j$ the binary bit length of $\ell$. The replay takes $d=\max(2,\lfloor(\ell/j)^{1/3}\rfloor)$. At degree two, odd $N\ge9$ gives $m\ge3$. For $d\ge3$, $\ell\ge d^3j$, so the positive real $d$th root of $N$ is at least $2^{(\ell-1)/d}\ge2^{d^2-1}$. Rounding down to an odd integer loses less than two, giving $m\ge4d$. All scheduled inputs therefore satisfy the coefficient height bound, including perfect powers.

Binary search finds the integer $d$th root with $O(\ell/d)$ power comparisons in an interval ending at $2^{\lceil\ell/d\rceil}$. Each comparison via repeated squaring takes $O(\log d)$ multiplications on $O(\ell+d)$-bit integers. The carry and digit extraction take $O(d)$ arithmetic operations at the same bit size. This gives deterministic polynomial bit complexity, and the coefficient list has $O(d\log m)=O(\log N)$ bits.

## Homogeneous norm scale

For natural logarithms put $L=\log N$, $W=L^{1/3}(\log L)^{2/3}$ and $V=L^{2/3}(\log L)^{1/3}$. Then $d\sim(L/\log L)^{1/3}$ and $\log m=(1+o(1))V$. For either polynomial $P$ of degree $e\in\{d,d+1\}$ and every grid mark with $|a|,|b|\le A$, its homogeneous value is bounded by

$$
|b^eP(a/b)|\le 2m(e+1)A^e,
$$

interpreted as the binary form also when $b=0$. For $A\le\exp(cW)$ with fixed $c>0$, this is at most $\exp((1+c+o(1))V)$. The construction thus supplies fields and norm sizes compatible with one-third parameter scales. The power-order maps above require separate work to use with maximal orders, and the construction gives no smoothness or rank bounds. In particular, the two binary forms obey $G_{\rm hom}(a,b)=bF_{\rm hom}(a,b)+(a-mb)a^d$ even though their fields are distinct. The existing [variable-multiple field construction](cogentic-variable-multiple-lattice.md) has different local distribution requirements and uses coefficient sampling to address them.

Evaluating $G$ on the roots of monic $F$ gives $|\operatorname{Res}(F,G)|=N|F(0)|^d$. If $\gcd(F(0),N)=1$, any common root $x$ modulo $N$ is a unit, since $F(x)\equiv F(0)\pmod p$ whenever $p$ divides both $x$ and $N$. Then $(x-m)x^d\equiv0\pmod N$ implies $x\equiv m\pmod N$. These identities describe the raw pair.
