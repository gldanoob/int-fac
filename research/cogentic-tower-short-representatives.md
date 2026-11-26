# Exact square relations in a supplied tower of quadratic fields

Let $\mathbb Q=F_0\subset F_1\subset\cdots\subset F_k$ be a supplied tower with $F_j=F_{j-1}(\sqrt{D_j})$, each step quadratic. Given $n$ nonzero elements of $F_k$ in the tensor basis, the complete binary square kernel and roots for its basis can be computed deterministically in time polynomial in $n$, $d=2^k$, and the bit lengths of the explicit tower and columns. The radicands may lie anywhere in their respective lower fields. There is no restriction on the prime ideals dividing the columns. The improvement over the [earlier growing-depth estimate](https://github.com/gldanoob/int-fac/blob/132367e/research/cogentic-quadratic-tower-square-kernel.md) comes from replacing each long product by an element of the same squareclass before descending to the next field.

## An exact representative for each subset

At a node with field $K$ and nonzero columns $z_i$, write $[z]$ for the class modulo squares in that field. Maintain a procedure $R(v)$ for a binary mask $v$ with
$$[R(v)]=\left[\prod_{i:v_i=1}z_i\right].$$
At the top, multiply the selected input columns. At a rational leaf compute the complete kernel of the stored rational columns by a gcd-free basis, the sign row, exact integer square tests and binary elimination.

Consider a step $K=F(\sqrt D)$. Its first child has columns $N_{K/F}(z_i)$ and representative $R_1(v)=N_{K/F}(R(v))$. Recursively compute its kernel basis $v_1,\dots,v_s$. For every basis mask set $\beta_i=R(v_i)$. Its relative norm is a square in $F$. For such a $\beta$, choose a relative norm root $t$ with $\delta(\beta)=\operatorname{Tr}_{K/F}\beta+2t\ne0$. At least one sign works. The identity
$$(\beta+t)^2=\delta(\beta)\beta$$
shows that the class of $\delta(\beta)$ in $K$ equals $[\beta]$.

The second child has the stored columns $\delta_i=\delta(\beta_i)$ followed by $D$. For a mask $(w,e)$ its representative is computed as follows.

1. Lift $w$ to the parent mask $v=\bigoplus_{i:w_i=1}v_i$. Compute $s_0=\delta(R(v))$ using the parent procedure. The relative norm is square because $v$ belongs to the first child's kernel.
2. Form $B=D^e\prod_{i:w_i=1}\delta_i$ **temporarily in $F$**. The classes of $B$ and $s_0$ agree in $K$, including when masks overlap.
3. Test whether $B/s_0$ is a square in $F$. If so return $s_0$. Otherwise return $s_0D$.

For $x\in F^\times$, expansion of $(a+b\sqrt D)^2=x$ gives $ab=0$. Consequently $\ker(F^\times/F^{\times2}\to K^\times/K^{\times2})=\langle[D]\rangle$. This proves step 3, including the appended-radicand case $w=0,e=1$. The test distinguishes the two possible classes in the child. A comparison only in $K$ would lose this information.

Compute the kernel of this second child, project away $e$, and lift through the independent masks $v_i$. Projection is injective since $D$ is nonsquare in $F$. Every square mask at the parent belongs to the norm kernel, and its joint product of descended classes is trivial precisely when it equals one of $[1],[D]$ in $F$. The lifted vectors therefore form a basis of the full parent kernel. For a root certificate at the top, multiply the actual original columns for the returned mask and take an exact square root of that product.

## Work and heights

Let $H\ge1$ bound the absolute logarithmic heights of the original columns and $A\ge1$ bound those of the supplied radicands. At depth zero the original representative has height at most $nH$. If all parent representatives and stored columns have height at most $T$, norm-child heights are at most $2T$. For a relative trace, $h(\operatorname{Tr}\beta)\le2h(\beta)+\log2$ and $h(t)=h(N\beta)/2\le h(\beta)$. Thus both choices retained by the scalar child have height at most $3T+A+3\log2$. These bounds give
$$T_j=O\bigl(3^j(nH+A+1)\bigr)$$
at depth $j$. The intermediate $B$ can be larger by a factor $n+k$ in height. It is used only in a single square test at this node. Descendants receive the selected short representative. This is the step that removes the previous product of mask lengths down a path.

There are fewer than $2d$ nodes. Each has width at most $n+k$ and constructs at most that many basis representatives. Each representative query follows a single ancestor path of length at most $k$ once the parent masks and stored columns have been constructed. Thus $O(d(n+k)(k+1))$ representative steps suffice in addition to the binary kernels, rational gcd refinements and final certificates. A step can involve $O(n+k)$ field multiplications and mask operations of polynomial size. Since $3^k=d^{\log_2 3}$, all retained and temporary heights are polynomial in the stated parameters.

An exact single-element square test is cheaper than a square-kernel call. At $K=F(\sqrt D)$ write $z=a+b\sqrt D$. For $b=0$ test $a$ and $a/D$ in $F$. Otherwise take a lower-field root $t$ of $a^2-Db^2$ if it exists, and test $(a+t)/2$ and $(a-t)/2$ for squareness in $F$. A successful choice yields the two coefficients of the root as $u$ and $b/(2u)$. The zero case is handled directly. There are at most three lower calls per level. The formulas for $a,b$ from $z$ and its conjugate bound their heights by a constant times $h(z)+h(D)+1$. The recursion therefore takes polynomial bit work in $d$, the tower description, and the argument height. The tensor multiplication tables and conversion from absolute height to rational coefficient size likewise cost polynomially in the degree and the explicit presentation, by the trace-dual argument in the earlier tower analysis. The input heights themselves are polynomially bounded by the supplied tensor data: a successive square root halves the height of its radicand and a tensor expansion is a sum of at most $d$ monomials. More explicitly, if $a_j=h(\sqrt{D_j})$ and all rational coefficients have height at most $C$, the sum-height inequality applied term by term naively multiplies previous $a_i$ by the number of monomials. Instead clear the rational denominators once, and bound the local absolute value of the sum by the product of $\max(1,|\sqrt{D_i}|_v)$ at each place times the local bound for all its rational coefficients (and the number of terms at archimedean places). This gives $2a_j\le O(d(C+1))+\sum_{i<j}a_i$ and hence polynomial heights over $k=\log_2 d$ levels.

For one integer $N$, take $W=(\log N)^{1/3}(\log\log N)^{2/3}$. For $d$ polynomial in $\log N$ and $n$ and input bit lengths bounded by $\exp(O(W))$, the local square-kernel stage is within $\exp(O(W))$ even with unrestricted ideal support. This is a bound on a supplied field and a supplied set of marks. A factoring algorithm must also construct suitable fields and marks from that same $N$, and prove that the resulting relations distinguish prime factors often enough.
