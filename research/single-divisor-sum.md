# Deterministic factoring from one divisor sum

Let $b=\max(3,\lceil\log_2(N+1)\rceil)$. Given $N\ge2$ and the single integer $M=\sigma(N)$ in binary, there is a deterministic algorithm returning the complete prime factorization of $N$ in
$$
\exp\!\left(O_\delta\big(\sqrt{b\log b}\big)\right)
$$
bit operations. The analytic input is a fixed $0<\delta\le1/2$ such that the Dedekind zeta functions used below have no zeros in $\Re(s)>1-\delta$. Cureton–Thorner report this for all number fields with $\delta=1/32$. All bounds below keep their dependence on the varying cyclotomic index. Computing the supplied divisor sum from $N$ remains outside the bound. [Cureton–Thorner, Theorem 1.1](https://hexagonmath.org/pdf/2610.00200v2#page=3)

Bach–Miller–Shallit proved randomized polynomial-time complete factorization from the same single value. Their general algorithm guesses a prime multiplicity and varies a polynomial of corresponding degree. Bach–Shallit subsequently gave randomized splitting from a cyclotomic multiple. Źrałek's deterministic cyclotomic result has fixed-field and smoothness conditions. The [fixed-index splitting proof](cyclotomic-order-multiples.md) in this repository gives polynomial time for bounded prime multiplicities. The estimate here handles unbounded multiplicities. Publication priority for this deterministic bound is unverified. [Bach–Miller–Shallit, Theorem 2 and §4](https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf) · [Bach–Shallit](https://doi.org/10.1090/S0025-5718-1989-0947467-1) · [Źrałek, Theorem 5.5](https://arxiv.org/pdf/0707.4102#page=11)

## A uniform prime-index split

Let $n\mid N$ contain distinct primes $p,q$ with $\Phi_k(p)\mid M$, where $3\le k\le b$ is an odd prime. The following search takes $b^{O_\delta(k)}$ bit operations when $\log(2M)=O(b)$. For the actual oracle value, $\sigma(N)\le N^2$. Trial division within the search handles all sufficiently small prime divisors, including $k$.

**Conductor.** Take $L=\mathbb Q(\zeta_k,\sqrt[k]p,\sqrt[k]q)$. Since $p,q\ne k$, valuations in $\mathbb Q(\zeta_k)$ show that $p,q$ generate a subgroup of order $k^2$ modulo $k$th powers. Thus $[L:\mathbb Q]=k^2(k-1)$. The power bases in the three generating fields give a tensor-product order of full rank. Its discriminant bounds the field discriminant and gives
$$
\log |D_L|=O\big(k^3(\log(2k)+\log(pq))\big).
$$
Indeed the cyclotomic polynomial has discriminant of absolute value $k^{k-2}$, and $X^k-t$ has discriminant of absolute value $k^kt^{k-1}$. The respective powers in the product discriminant are $k^2,k(k-1),k(k-1)$.

Choose a Frobenius element that fixes $\zeta_k,\sqrt[k]q$ and sends $\sqrt[k]p$ to $\zeta_k\sqrt[k]p$. All its conjugates retain these splitting conditions. Frei–Sofos–Widmer give a least-prime bound $O_\delta((\log |D_L|)^{1/\delta}(\log\log |D_L|)^{2/\delta})$ with uniform, effective dependence for fixed $\delta$. It gives a prime $\ell\le b^{O_\delta(1)}$ congruent to $1\bmod k$ at which $q$ is a $k$th power and $p$ is a nonpower. The unique degree-$k$ field $K\subset\mathbb Q(\zeta_\ell)$ is totally real, $p$ is inert and $q$ splits completely. Its discriminant is $D=\ell^{k-1}$ by the conductor–discriminant formula. The algorithm enumerates all possible $\ell$, returning any proper common factor with $n$. [Frei–Sofos–Widmer, Corollary 1.2](https://arxiv.org/html/2610.18491v2#S1.SS1) · [Milne, Theorem V.3.27](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=174)

**A witness of bounded norm.** At two of the $k$ components of $\mathcal O_K/q\mathcal O_K$, multiply the two Legendre symbols to obtain a quadratic character $\chi$. It is surjective by CRT and trivial on rational scalars. There is an integral $\alpha$ with $\chi(\alpha)=-1$ and $A=|\operatorname{Nm}\alpha|\le b^{O_\delta(k)}$, or trial division to that bound already splits $n$. To see this, a global unit of character $-1$ works with $A=1$. Otherwise the character descends to principal ideals coprime to $q$. The kernel on these principal ideals contains the ray principal ideals modulo $q\mathcal O_K$ and has index $2h_K$ in the full ideal group coprime to $q$. Its class field $E/K$ has conductor dividing $q\mathcal O_K$, hence
$$
\log |D_E|\le 2h_K(\log D+k\log q).
$$
Minkowski's ideal-class bound provides an integral representative of norm at most $\sqrt D$ in every class. There are at most $D\zeta_K(2)\le D\zeta(2)^k$ ideals of this norm or smaller, by the Euler product. Thus $h_K\le b^{O_\delta(k)}$. Apply the same Chebotarev corollary to $E/K$ and the nonidentity element in the order-two kernel over the ordinary ideal class group. This gives a principal prime ideal with norm at most $b^{O_\delta(k)}$. Any generator has the required character. A prime over $q$ within that bound already makes $q$ small enough for trial division. [Milne, Theorem V.1.7 and Corollary V.3.7](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=159)

**Two short integral elements.** Write $\alpha_i$ for the real embeddings and take $C=2D^{1/(2k)}$. Subdivide $[0,1]$ into equal steps of length $1/m$ with $m\ge1+\max_i |\log|\alpha_i||$. At each mesh point $t$ choose a nonzero $x_t\in\mathcal O_K$ with
$$
|(x_t)_i|\le C|\alpha_i|^t\quad(1\le i\le k).
$$
The product of the coordinate radii is $C^kA^t>\sqrt D$, so Minkowski applies. Take $x_0=1$, $x_1=\alpha$. All these elements have absolute norm at most $C^kA$. Assume the prime divisors of $n$ exceed this bound and the bound $R^k$ below, as smaller divisors are found by trial division. The character is therefore defined at every $x_t$, and some adjacent pair $x,y$ has opposite signs.

Set $m_i=\max(|x_i|,|y_i|)$. The mesh bound gives $\prod_i m_i\le(eC)^k A$. With
$$
R=2 e C (\sqrt D\, A)^{1/k},
$$
the product of the radii $R/m_i$ exceeds $\sqrt D$. Apply Minkowski again to find $v\ne0$ in $\mathcal O_K$ with $|v_i|\le R/m_i$. Both $vx$ and $vy$ are integral, with all conjugates of absolute value at most $R$. Their nonzero norms are at most $R^k$, so $v$ is also a unit modulo $q$ and the opposite signs persist. One of the two products has character $-1$. Since $D\le b^{O_\delta(k)}$ and $A\le b^{O_\delta(k)}$, **$R\le b^{O_\delta(1)}$ uniformly in $k$**. Only the existence of one such product is used. The algorithm searches for it without constructing $\alpha$, its units, or the mesh.

**Coefficient search.** Let $H$ be the index-$k$ subgroup of $(\mathbb Z/\ell)^\times$, let $s=|H|$, and put $\eta_j=\sum_{a\in C_j}\zeta_\ell^a$ for its cosets $C_j$. These periods form an integral basis of $K$. Indeed the nontrivial $\ell$th roots of unity form an integral basis of the full field, and its $H$-invariant integral vectors are exactly those with constant coordinates on each coset. The real embedding matrix $V$ of the periods satisfies
$$
(V^{\mathsf T}V)_{ij}=\operatorname{Tr}_{K/\mathbb Q}(\eta_i\overline{\eta_j})
=\ell\,\mathbf 1_{i=j}-s .
$$
To verify the equality, take the full cyclotomic trace and divide by $s$. Among the $s^2$ terms $\zeta_\ell^{a-b}$ there are $s\mathbf 1_{i=j}$ with $a=b$. The traces of the two types are $\ell-1$ and $-1$. As $ks=\ell-1$, the singular values of $V$ are $1$ in the constant direction and $\sqrt\ell$ on its orthogonal complement. A witness whose conjugates all have absolute value at most $R$ consequently has every period coefficient bounded by $\sqrt{k}R$. The search has at most $(2\lfloor\sqrt{k}R\rfloor+1)^k=b^{O_\delta(k)}$ candidates. Arithmetic can be performed by cyclic convolution modulo $X^\ell-1$ followed by reduction modulo $1+X+\cdots+X^{\ell-1}$. Direct convolution costs polynomial time in $b$ here. [Bernstein, §4.7.2, prime-conductor period arithmetic](https://doi.org/10.1007/s40993-022-00402-0)

Put $d=M/2^{v_2(M)}$. At the inert $p$, the projective group has odd order $(p^k-1)/(p-1)=\Phi_k(p)$ dividing $d$. The selected witness to the power $d$ is scalar there. At the split $q$ its two components still have opposite quadratic signs, so this power is nonscalar. In the period basis a scalar has all coordinates equal because $\sum_j\eta_j=-1$. The gcd of $n$ and all coordinate differences thus returns a proper divisor, including for nonsquarefree $n$. All hidden-field norm bounds used for trial division and the box search can be replaced by the effective majorants above. Equivalently, dovetail trial division and searches over conductors and coefficient boxes, giving each search stage increasing bounds. For finite unsuccessful prime indices use the bounded search or run them in parallel with successful indices.

For $k=2$ use the [one-$p+1$ splitting algorithm](p-plus-one-multiples.md#two-small-primes-and-a-quadratic-equation). Its two index-eight prescriptions each involve at most three quadratic Dirichlet characters. Their fixed fields compose to an extension of degree at most eight and discriminant polynomial in the character modulus. Applying the same Chebotarev bound to these multiquadratic fields replaces both least-prime estimates by effective $b^{O_\delta(1)}$ bounds. Any enumerated prime divisor of $n$ gives a split directly.

## Complete factorization with the original value

Choose $T=\max(2,\lfloor\sqrt{b/\log b}\rfloor)$. Trial divide $N$ through $\lceil 2^{b/T}\rceil$, removing all powers of every prime found. For every remaining prime $p$ with original multiplicity $a=v_p(N)$ we have $a<T$, since $p^a\le N<2^b$. Select any prime $k\mid a+1$. Then $k\le T$ and
$$
\Phi_k(p)\mid (1+p+\cdots+p^a)\mid M .
$$
For each residual composite with at least two distinct prime divisors, try the prime indices up to $T$. At least one succeeds. Use the original $M$ throughout the recursion, since the divisibility above depends only on the original multiplicity. Overlap between the prime factors of the two children preserves the promise. Test primes and handle prime powers by integer roots. The tree has $O(b)$ nodes and each search costs $b^{O_\delta(T)}$. Together with trial division this gives the stated bound. When all original multiplicities are bounded by a fixed $E$, one can skip the initial $2^{b/T}$ trial division and use $T=E+1$ directly for polynomial time.

## Exact arithmetic replay

This Python check verifies the period Gram matrix using traces of roots of unity. It then runs the scalar test on $N=5^2\cdot13$ and $N=3^4\cdot23$ with the respective original divisor sums. The quintic case returns the composite divisor $9$.

~~~python
from math import gcd

for ell, k, g, p, q, expected in [(7, 3, 3, 5, 13, 5), (11, 5, 2, 3, 23, 9)]:
    size = (ell - 1) // k
    subgroup = {pow(g, k * j, ell) for j in range(size)}
    cosets = [{pow(g, i, ell) * h % ell for h in subgroup} for i in range(k)]
    for i, left in enumerate(cosets):
        for j, right in enumerate(cosets):
            trace = sum(ell - 1 if a == b else -1 for a in left for b in right)
            assert trace == size * (ell * (i == j) - size)

    n = p ** (k - 1) * q
    sigma = sum(p ** i for i in range(k)) * (q + 1)
    odd = sigma // (sigma & -sigma)

    def multiply(a, b):
        return [sum(a[j] * b[(i - j) % ell] for j in range(ell)) % n
                for i in range(ell)]

    base = [int(i == 0 or i in subgroup) for i in range(ell)]
    power = [1] + [0] * (ell - 1)
    for bit in bin(odd)[2:]:
        power = multiply(power, power)
        if bit == "1":
            power = multiply(power, base)
    coefficients = [power[min(c)] - power[0] for c in cosets]
    assert gcd(n, *(v - coefficients[0] for v in coefficients)) == expected
~~~
