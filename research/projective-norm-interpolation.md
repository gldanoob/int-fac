# Projective height bounds for rational-side norm relations

Let \(F\in\mathbb Z[X,Y]\) be homogeneous of degree \(d\ge1\) and let \(0\ne F(m,n)\equiv0\pmod N\). If \(|F(a,b)|\le Y_0\), then **at most \(d\) distinct rational projective points** can simultaneously satisfy
\[
       |m b-n a|<\left(\frac{N}{(d+1)Y_0}\right)^{1/d}.
\]
Use primitive integer representatives of the marked points. These hypotheses include homogeneous norms of the form \(b^d f(a/b)\) at a rational modular root. In particular, enlarging the permitted mark denominators or translating the entire grid cannot by itself place more than \(d\) small-norm marks in progressions of a smaller determinant. Cogentic's univariate perturbation at \((a,1)\) uses \(|m-a|\) in the evaluation modulus. [Cogentic, Lemmas 7.3, 8.1 and 9.4](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf)

Indeed let \(z_i=(a_i,b_i)\), \(0\le i\le d\), be distinct projective points, and write \([z,z']\) for the determinant. The forms \(\prod_{j\ne i}[z,z_j]/[z_i,z_j]\) are a Lagrange basis of the \((d+1)\)-dimensional vector space of homogeneous degree-\(d\) binary forms over \(\mathbb Q\). Hence
\[
     F(m,n)=\sum_{i=0}^d F(z_i)\prod_{j\ne i}\frac{[(m,n),z_j]}{[z_i,z_j]}.
\]
Each denominator determinant is a nonzero integer. With \(R=\max_j|[(m,n),z_j]|\), taking absolute values gives \(N\le(d+1)Y_0R^d\). This includes points at infinity. For integer marks \((a_i,1)\) ordered by increasing \(a_i\) and integer target \((m,1)\), the denominator of the \(i\)th basis value has magnitude at least \(i!(d-i)!\), giving the stronger \(N\,d!\le Y_0(2R)^d\).

The exceptional count of \(d\) can occur even with a primitive irreducible polynomial and a composite input. For \(f(T)=1+59(T-1)(T-2)(T-3)(T-4)\), the reciprocal polynomial is Eisenstein at 59. Here \(f(5)=1417=13\cdot109\), all four marked values are 1, and all four determinants are at most 4, with \(5\cdot 4^4<1417\). In the two-thirds schedule \(d\sim x(L/\log L)^{1/3}\), \(L=\log N\), \(V=L^{2/3}(\log L)^{1/3}\) and \(\log Y_0=O(V)\); the bound forces \(\log |mb-na|\ge (1/x+o(1))V\) at all but \(d\) small-norm marks. The conclusion concerns progressions retaining the full determinant factor. More general perturbations can mix several residue classes, and the bound gives no lower bound on factoring time.

There is also a restriction on canceling rational residues by short balanced products over the integers. Suppose \(|a|,|b|\le A\), \(b>0\), \(\gcd(a,b)=1\) for every available mark, and \(\gcd(m,n)=1\), \(mn\ne0\). If \(\max(|m|,|n|)>2(2A)^k\), then each product of \(k\) integers \(mb-na\), with repetition allowed, determines its multiset of marks. To see this, subtract the two polynomials \(\prod_{i=1}^k(b_iT-a_i)\) and \(\prod_{i=1}^k(b'_iT-a'_i)\) from a claimed collision. Their difference has coefficients of magnitude at most \(2(2A)^k\) by the coefficient \(\ell^1\) bound. If this difference is nonzero, remove any power of \(T\) and apply the rational-root theorem at \(m/n\). The numerator divides the nonzero constant term, and the denominator divides the leading coefficient, contradicting the height condition. Unique factorization and the primitive positive-leading-coefficient convention recover exactly the multiset when the two polynomials agree. The claim is about exact equality of rational-side integers. Congruences modulo \(N\) can supply useful collisions without an integer equality.

The [exact replay](../experiments/projective-norm-interpolation.py) verifies 720 general homogeneous interpolations, 720 integer-grid factorial bounds, the irreducible quartic example, and 145,162 balanced products across sixteen small combinations of heights and product lengths.

## A height bound from any selected set of small marks

For a homogeneous binary form $F$ of degree $d$, write $\|F\|_1$ for the sum of its absolute coefficients. Take any $d+1$ distinct projective integral marks $z_i=(a_i,b_i)$. The same interpolation identity, now retaining the coefficient vector, gives
$$
 \|F\|_1\le\sum_i |F(z_i)|\prod_{j\ne i}
          \frac{|a_j|+|b_j|}{|[z_i,z_j]|}.
$$
Each numerator factor is the coefficient sum of one linear form, and coefficient sums are submultiplicative. Thus marks of coordinate height at most $A$ and homogeneous values at most $T$ force $\|F\|_1\le(d+1)T(2A)^d$. This improves the previous determinant estimate with $A^{d^2}$ and holds for an arbitrary subset, however close its slopes are. For instance $(M X-(M-1)Y)^d-2(Y-X)^d$ has values $j^d-2$ at $(M-1+j,M+j)$ for $0\le j\le d$ but leading coefficient $M^d-2(-1)^d$. The unimodular change of variables takes $X^d-2Y^d$ to this irreducible form. At fixed $d$, the exponent $d$ on $A$ is necessary.

A small leading coefficient replaces one finite mark by the point at infinity. There is also a version with a large radix. Take $d$ finite marks with $1\le b_i\le A$, $|a_i|\le A$, and the extra point $z_*=(m,1)$ with $|m|\ge2A$ and $|m|\ge2$. In every finite-mark term the extra factor is at most $(|m|+1)/(|m|-A)\le3$. At the radix the denominator product is at least $(|m|-A)^d$. Hence
$$
 \|F\|_1\le 3dT(2A)^{d-1}
       + |F(m,1)|\left(\frac{2A}{|m|-A}\right)^d.
$$
With $d-1$ finite marks one may use *both* $z_*$ and $(1,0)$. The finite terms are bounded by $3(d-1)T(2A)^{d-2}$, the radix term by $|F(m,1)|(2A/(|m|-A))^{d-1}$, and the term from infinity by $|F(1,0)|(|m|+1)(2A)^{d-1}$. Here $d\ge2$. These estimates use the actual evaluated multiple, including its size.

For single-input NFS put $L=\log X$, $D=(L/\log L)^{1/3}$, $W=D\log L$ and $V=DW$. If $d=O(D)$, $\log A=O(W)$ and $\log T=O(V)$, the unconditioned $d+1$-mark estimate forces $\log\|F\|_1=O(V)$. Combine this with the [tower count](cogentic-full-tower-height-scarcity.md). Under its rational radix size and nonzero divisibility hypotheses, only $X^{o(1)}$ inputs in $[X,2X)$ can have even one admissible tower polynomial with $d+1$ such small homogeneous values. This applies also when every input chooses different marks and a different field. A monic polynomial needs only $d$ finite small marks for this conclusion. At a natural integer radix with $\log |m|=O(V)$, $|m|\ge2A$, $\log^+(|F(m,1)|/|m|^d)=O(V)$ and $\log^+|F(1,0)|=O(V)$, even $d-1$ finite small marks suffice. These statements bound absolute homogeneous values. Large smooth values, nonlinear marks, and exact square relations that use fewer distinct marks require separate analyses.
