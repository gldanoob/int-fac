# Deterministic factoring from one divisor sum

Let $b=\max(3,\lceil\log_2(N+1)\rceil)$. Given $N\ge2$ and the single integer $M=\sigma(N)$ in binary, there is a deterministic algorithm returning the complete prime factorization of $N$ in
$$
\exp\!\left(O_\delta\big(b^{1/3}(\log b)^{2/3}\big)\right)
$$
bit operations. The analytic input is a fixed $0<\delta\le1/2$ such that the Dedekind zeta functions used below have no zeros in $\Re(s)>1-\delta$. Cureton–Thorner report this for all number fields with $\delta=1/32$. All bounds below keep their dependence on the varying cyclotomic index. For any fixed bound on the number of distinct prime factors, the running time is polynomial in $b$, allowing arbitrary multiplicities. Computing the supplied divisor sum from $N$ remains outside these bounds. [Cureton–Thorner, Theorem 1.1](https://hexagonmath.org/pdf/2610.00200v2#page=3)

Bach–Miller–Shallit proved randomized polynomial-time complete factorization from the same single value. Their general algorithm guesses a prime multiplicity and varies a polynomial of corresponding degree. Bach–Shallit subsequently gave randomized splitting from a cyclotomic multiple. Źrałek's deterministic cyclotomic result has fixed-field and smoothness conditions. The [fixed-index splitting proof](cyclotomic-order-multiples.md) in this repository gives polynomial time for bounded prime multiplicities. The estimate here handles unbounded multiplicities. Publication priority for this deterministic bound is unverified. [Bach–Miller–Shallit, Theorem 2 and §4](https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf) · [Bach–Shallit](https://doi.org/10.1090/S0025-5718-1989-0947467-1) · [Źrałek, Theorem 5.5](https://arxiv.org/pdf/0707.4102#page=11)

With access to additional values on powers of the original input, a short nonadaptive block gives unconditional deterministic polynomial-time complete factorization for arbitrary multiplicities. [Power-sum decoder](divisor-sums-on-powers.md)

A separate argument gives unconditional polynomial average bit cost over integers of each bit length from the single supplied value, with arbitrary prime multiplicities. [Average-case algorithm, proof and replay](average-single-divisor-sum.md)

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

Take an integer cutoff $2\le T\le b$. Each original prime $p^e\parallel N$ with $e<T$ has a prime $k\mid e+1$ for which
$$
k\le T,\qquad \Phi_k(p)\mid(1+p+\cdots+p^e)\mid M .
$$
At each composite node try every prime $k\le T$ up to the effective search bounds above. Recurse on both children of any proper split. Record prime leaves, recognize powers of a single prime by integer roots and primality tests, and stop a branch after all its bounded searches fail. This takes $b^{O_\delta(T)}$ bit operations over $O(b)$ nodes. A prime of original exponent $e<T$ cannot occur in a stopped branch, since any second prime there would guarantee a split. The children of a gcd split may share prime divisors. Remove the **full original power** of every discovered prime from $N$ when forming the residual $m$. Dividing $M$ by the product of the divisor sums of these original powers gives $S=\sigma(m)$. This accounts for overlapping branches exactly. If all original exponents are bounded by $E$, setting $T=E+1$ (capped at $b$) already finishes in polynomial time for fixed $E$.

For arbitrary inputs first remove all primes through $Y$, with
$$
Y=2^{\left\lceil(\lceil\log_2(8b)\rceil+2\lceil b/T\rceil)/(T+1)\right\rceil}.
$$
Include these primes among the recorded divisors. If $m>1$ remains after the bounded searches, write $R=\operatorname{rad}(m)=\prod_{p\mid m}p$. Every $p^e\parallel m$ has $e\ge T$, so $R^T\le m<2^b$. With $U=\sum_{p^e\parallel m}p^{-e-1}$ we have $U<bY^{-T-1}\le1/(8R^2)$. Euler's products give
$$
\frac{m}{S}=\frac{\varphi(R)}{R}\prod_{p^e\parallel m}(1-p^{-e-1})^{-1},
\qquad
0<\frac{m}{S}-\frac{\varphi(R)}{R}\le\frac{U}{1-U}<\frac{1}{2R^2}.
$$
Here $\prod(1-u_j)\ge1-\sum u_j$. By Legendre's continued-fraction criterion the reduced form $C/D$ of $\varphi(R)/R$ occurs among the convergents of the known $m/S$, because $D\le R$. Enumerate all $O(b)$ convergents, retaining those with $D\mid m$. For each positive $C$ try $mC/D$ as a common exponent in Miller's bounded deterministic factorization algorithm. For the true convergent the exponent is exactly $\varphi(m)$, which works on every divisor of $m$. Verify all proposed factors by integer division and primality testing. The same fixed zero-free strip yields Miller's polynomial witness bound via quadratic character prescribed signs and the Chebotarev estimate above. [Miller, Lemmas 2A, 2B and 5](https://www.cs.cmu.edu/~glmiller/Publications/Papers/Mi76.pdf#page=11)

The trial division costs $2^{O(1+b/T^2+(\log b)/T)}\operatorname{poly}(b)$ bit operations. Choosing $T=\max(2,\lceil (b/\log b)^{1/3}\rceil)$ balances this with $b^{O_\delta(T)}$ and proves the cube-root bound. For comparison, Źrałek recovers a factorization at the same subexponential scale using a chain of numerical totient queries. Harvey–Hittmeir find all $r$-power divisors from $N$ alone in $N^{1/(4r)}\operatorname{poly}(b)$ time. Morain–Renault–Smith give continued-fraction recovery from one $\sigma(N)$ for certain squarefree inputs with separated prime factors. [Źrałek, Corollary 8.2](https://arxiv.org/pdf/0707.4102#page=18) · [Harvey–Hittmeir, Theorem 1.1](https://doi.org/10.1007/s40993-022-00387-w) · [Morain–Renault–Smith, Theorem 5.5](https://arxiv.org/pdf/1802.08444#page=13)

## A bounded number of distinct primes

Suppose $\omega(N)\le h$. Trial divide only through $16h$, then use the same bounded searches with $T=\min(b,3^h)$. When $T=b$ every original exponent is smaller than $T$. Otherwise every prime of the residual $m$ exceeds $16h$ and has exponent at least $T=3^h$. These two properties persist after stripping any collection of its prime powers.

Order the residual primes $p_1<\cdots<p_s$, where $s\le h$, and put $R_j=p_1\cdots p_j$. Choose the first $i$ such that $i=s$ or $p_{i+1}>16hR_i^2$. Before this index, $R_{j+1}\le16hR_j^3$, whence
$$
R_i\le(16h)^{(3^{i-1}-1)/2}p_1^{3^{i-1}},\qquad
R_i^2\le p_1^{3^i-1}.
$$
In particular $U\le h p_1^{-T-1}<1/(16R_i^2)$. Passing from $\varphi(R_i)/R_i$ to $\varphi(R_s)/R_s$ changes the value by at most $\sum_{j>i}1/p_j<1/(16R_i^2)$, with zero change for $i=s$. Thus
$$
\left|\frac m{\sigma(m)}-\frac{\varphi(R_i)}{R_i}\right|
\le \frac{U}{1-U}+\sum_{j>i}\frac1{p_j}<\frac1{2R_i^2}.
$$
The reduced prefix fraction $C/D=\varphi(R_i)/R_i$ is a convergent. Its denominator divides $R_i$, and $p_i\mid D$ since $p_i$ exceeds every integer $p_j-1$ for $j\le i$. Moreover $E=mC/D=(m/R_i)\varphi(R_i)$ is a multiple of every $p-1$ for $p\mid D$. As $D$ is squarefree, $\lambda(D)\mid E$.

Try each convergent with $D>1$, $D\mid m$, and $C>0$. Run bounded Miller factorization of $D$ with exponent $mC/D$, accepting any certified prime divisor of $m$. The guaranteed convergent yields at least $p_i$ if used for complete factorization of $D$. Strip the full power of a recovered prime, divide $\sigma(m)$ by its divisor sum and repeat. There are at most $h$ iterations, each polynomial in $b$. The initial searches give a total time of $b^{O_\delta(3^h)}$ for fixed $h$, without an upper bound on any prime multiplicity.

### Two prime divisors by integer polynomial arithmetic

For $N=p^u q^v$ with distinct primes, the single exact divisor sum admits an elementary deterministic polynomial-time decoder without an analytic hypothesis. Try all positive $u,v\le b$ and set
$$
B(X)=1+X+\cdots+X^u,\quad A(X)=MX^u-NB(X),\quad C(X)=X^u(M-B(X)).
$$
For the true multiplicities, $M(q-1)=B(p)(q^{v+1}-1)$ and $p^u q^v=N$ give $A(p)q=C(p)$. Consequently $p$ is an integer root of
$$
P(X)=X^u C(X)^v-N A(X)^v.
$$
The first term has degree $u+2uv$ and the second has degree at most $uv$, so the polynomial is nonzero for every guess. Its coefficients have polynomial bit length by direct expansion. List rational linear factors over $\mathbb Q$ using deterministic polynomial factorization and test their positive integer roots by divisibility and primality. Strip the full power of each prime found. On the promised inputs the other block is a prime power. The argument also covers equal multiplicities. The classical polynomial-factorization theorem applies to binary integer coefficients. [Lenstra–Lenstra–Lovász](https://doi.org/10.1007/BF01457454)

The following PARI/GP check exercises the integral-root identity for six exponent values at each prime and independently extracts the two hidden primes from a divisor sum by trying exponent pairs.

~~~gp
twoPrimeRoots(n,m,u,v) = {
  my(b=sum(i=0,u,x^i),a=m*x^u-n*b,c=x^u*(m-b));
  nfroots(,x^u*c^v-n*a^v)
};
{
  for(u=1,6,for(v=1,6,
    my(n=11^u*17^v);
    if(!setsearch(Set(twoPrimeRoots(n,sigma(n),u,v)),11),error("two-prime identity"))));
  my(n=4084101,m=sigma(n),hits=List());
  for(u=1,logint(n,2),for(v=1,logint(n,2),
    foreach(twoPrimeRoots(n,m,u,v),r,
      if(denominator(r)==1 && r>1 && n%r==0 && isprime(r),listput(hits,r)));
    if(#Set(Vec(hits))==2,break(2))));
  if(Set(Vec(hits))!=Vec(factor(n)[,1]),error("unknown multiplicities"));
}
~~~

### Unconditional recovery with at most three high-multiplicity primes

Suppose $m$ has at most three distinct prime factors and all its exponents are at least $27$. From $m$ and $S=\sigma(m)$ alone, complete deterministic factorization takes polynomial time in $\log m$ without a zero-free hypothesis. Strip primes through $48$, dividing $S$ by the divisor sum of each full power removed. The prefix estimate above with $h=3$ and $T=27$ uses only elementary inequalities. For each residual $m>1$ it supplies a nonempty prefix of the sorted primes, of product $R_i$, satisfying
$$
\left|\frac mS-\frac{\varphi(R_i)}{R_i}\right|<\frac1{2R_i^2}.
$$
This precision at each residual is also sufficient if it holds at smaller multiplicities. Record prime powers by integer roots and primality testing. At every other residual enumerate the convergents $C/D$ with $C>0$, $D>1$ and $D\mid m$. The proof considers the convergent of the guaranteed prefix. Its denominator is squarefree and contains the largest prefix prime.

Put $W=\gcd(m,D^{\lfloor\log_2 m\rfloor})$. It consists of the full prime powers of $m$ supported on $D$. If $W<m$, one of $W$ and $m/W$ is a power of a single prime, because they are coprime and together have at most three distinct prime factors. If $W=m$ at the guaranteed convergent, $D$ contains all prime factors, so the prefix is the entire radical $R=D$ and $C=\varphi(R)$. Divide $m$ by $R$ as many times as possible, say $e$ times. If the quotient $m'$ exceeds 1, then $1<\gcd(R,m')<R$. This partitions the squarefree radical into two nonempty sets, one of size one. Test both parts for primality. This treats every unequal-multiplicity case.

It remains to split $m=R^e$ with known $R$ and $C=\varphi(R)$. For two distinct primes their sum is $R+1-C$, giving a quadratic. For three distinct primes let $t$ denote their sum. Expanding the totient gives their sum of pairwise products as $t+R-1-C$. Define
$$
f_t(X)=X^3-tX^2+(t+R-1-C)X-R,\qquad B_e(X)=\sum_{j=0}^eX^j,
$$
$$
H(t)=\operatorname{Res}_X(f_t(X),B_e(X))-S.
$$
At the true $t$ the resultant is the product of $B_e$ at the three primes, so $H(t)=0$. In fact $H$ has degree exactly $e$ and leading coefficient $e+1$. As $t\to+\infty$, the rescaled polynomial $t^{-3}f_t(tX)$ has a simple limiting root at $1$, giving one root $\sim t$. Also $t^{-1}f_t(X)$ tends to $X(1-X)$ on bounded intervals, giving two roots tending to $0$ and $1$. The three factors $B_e$ at these roots are asymptotic to $t^e$, $1$, and $e+1$ respectively. This proves that $H$ is nonzero, including for incorrect positive candidates $R,C$.

One polynomial construction evaluates the Sylvester determinant at the integers $t=0,\ldots,e$ and interpolates. The matrix size is $e+3$ and its entries have $O(\log m+\log(e+1))$ bits. Hadamard's bound and exact interpolation give polynomial bit cost and coefficient size, as $e\le\log_2 m$. For every positive integral root of $H$, find the rational linear factors of $f_t$ and test each candidate prime directly against $m$. Accepting any certified prime divisor, even from an earlier convergent, permits stripping its full power and updating $S$ exactly. At most three such recoveries are needed. The polynomial factorization and integer-root steps use classical deterministic algorithms. [Lenstra–Lenstra–Lovász](https://doi.org/10.1007/BF01457454)

A second consequence covers $m=(pqr)^e$ for $e\ge2$ and $p,q,r\in[P,KP]$ with fixed $K$, including $e=2$. Try every exact exponent $e$ to obtain candidate radicals $R$ by integer roots. For the correct choice, $U\le3P^{-e-1}$ and $R\le K^3P^3$, so $|Rm/S-\varphi(R)|\le RU/(1-U)=O(K^3)$ for $P\ge2$. Try each integer in this bounded interval as $C$ and apply the same cubic resultant. This proof needs only the stated comparability bound or an enumeration of candidate totients in order of distance from $Rm/S$ until the three verified primes are recovered.

The [GP replay](../experiments/sigma-triprime.gp) searches convergents from the supplied $m,S$ and tests all of the cases. For $m=(53\cdot59\cdot67)^{28}$ it extracts the integer root $t=179$ of a degree-28 resultant with leading coefficient 29. Other fixtures recover a prime from a proper prefix, denominator cancellation, unequal valuations and a two-prime residual.

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

The [continued-fraction GP replay](../experiments/sigma-tail.gp) accepts only $m$ and its divisor sum. It tries convergents in order, using primality tests, integer roots and the [existing chain of squarings](../experiments/lucas-carmichael.gp) with prime bases through 31 to recover a certified prime from a denominator dividing $m$. The small fixtures strip every recovered prime power. On $53^{28}59^{30}107^{36}$ the factor $53$ cancels from the full ratio, giving the composite denominator $59\cdot107$. On $53^{28}59^{30}(2^{31}-1)^{36}$ the first successful denominator is the proper prefix $53\cdot59$. The finite base cutoff bounds the experiment.

Run the optional sweep from the repository root in GP. It checks the complete recovery of all 2,240 inputs obtained by choosing three of seven primes and assigning each one of four multiplicities from 27 through 256.

~~~gp
read("experiments/lucas-carmichael.gp");
read("experiments/sigma-tail.gp");
if(checkSigmaTailSweep()!=2240,error("divisor-sum sweep"));
~~~

## An interval or residue class for the divisor sum

Suppose only that the single original value $\sigma(N)$ belongs to
$$
\{A+Bt:0\le t<H\},\qquad A,B,H\ge1 .
$$
Under the same zero-free input, complete factorization costs
$$
O(\sqrt H)\,\exp\!\big(O_\delta(\sqrt{b\log b})\big)\,
\operatorname{poly}(\log(2+A+BH)).
$$
In particular an approximation with absolute error at most $E$ gives at most $2\lceil E\rceil+1$ candidates. Knowing a congruence modulo $B$ and an interval of width $W$ gives at most $1+\lfloor W/B\rfloor$ candidates. Bound the searches even on incorrect advice and verify every returned proper divisor. The guarantee applies whenever a candidate is the original divisor sum.

Partition the candidates by $v=v_2(A+Bt)$. Solving $A+Bt\equiv 2^v\bmod 2^{v+1}$ gives one progression of indices $t$ for each nonempty class. Dividing that class by $2^v$ gives odd candidates $a+ci$, $0\le i<h\le H$. There are $O(\log(2+A+BH))$ possible valuations. For this progression bound use $T=\max(2,\lfloor\sqrt{b/\log b}\rfloor)$ and trial divide through $\lceil 2^{b/T}\rceil$. Every remaining prime has original exponent $e<T$, since $p^e\le N<2^b$. The bounded searches over prime indices through $T$ therefore suffice at every composite node containing two distinct primes. The procedure below searches all exponent candidates in each valuation class.

For odd prime $k$, fix a generator $\rho$ of $\operatorname{Gal}(K/\mathbb Q)$, and in the proof choose the two Legendre-symbol components at $q$ to be adjacent under $\rho$. For each candidate $\alpha$ compute $g=\alpha/\rho(\alpha)$ modulo $n$. If the norm of $\alpha$ shares a proper factor with $n$, return it. Discard the candidate if its norm is divisible by $n$. Otherwise the inverse exists. For the promised witness, the norm is a unit at $p,q$ and one fixed component of $g$ at $q$ is a nonsquare. At $p$ the true stripped divisor sum kills $g$, since $\alpha$ to that power is scalar. Thus at $p$ some factor of
$$
\prod_{i=0}^{h-1}(g^{a+ci}-1)
$$
vanishes, while at that component of $q$ **every** factor is nonzero. Taking the gcd of $n$ with all integral coordinates of the product separates the two primes.

To compute the gcd, put $s=\lfloor\sqrt h\rfloor$ and form the monic polynomial
$$
F(X)=\prod_{i=0}^{s-1}(X-g^{-ci})
$$
over $\mathcal O_K/n\mathcal O_K$. Evaluate it at $g^{a+csj}$ for every complete block, multiply the results, and test the final fewer than $s$ factors directly as part of the same product. This differs from the displayed product by a unit. Monic product and remainder trees give $O(\sqrt h\,\operatorname{poly}(k,\log n,\log(2+A+BH)))$ bit operations with fast polynomial multiplication. For example one can convolve in the outer variable over the full cyclotomic ring by Kronecker substitution and ordinary fast integer multiplication, then reduce in the cyclotomic variable. No division by an evaluated difference is needed. [Related monic product-tree order search](p-plus-one-multiples.md#a-bounded-missing-multiplier)

For $k=2$ use the quadratic norm-one witness from the one-$p+1$ proof. Its orders at the two chosen inert primes have distinct 2-adic valuations. For each candidate class with valuation $v$, apply the same product computation to the exponents $2^j(a+ci)$ for each $0\le j\le v$. At either chosen prime the residue ring is a field. The product vanishes precisely when some $a+ci$ covers the odd order part and $j$ reaches the local 2-adic order valuation. At $p$ the correct class reaches that threshold by $v$. If the product also vanishes at $q$ by $v$, its first vanishing index there differs from the first vanishing index at $p$. This argument includes hits at different progression terms.

An alternative bound for the progression is
$$
\left(\sqrt H\,\exp\!\big(O_\delta(b^{1/3}(\log b)^{2/3})\big)+H\right)
\operatorname{poly}(b,\log(2+A+BH)).
$$
Use the cube-root choice of $T,Y$ for the searches above. The correct candidate still guarantees every split needed to remove all original exponents below $T$. Once the search tree stops, strip the full powers of the discovered primes as in the exact algorithm. Among the $H$ original candidates, try each divisible by the product of their divisor sums, applying continued-fraction recovery to the resulting residual candidate in polynomial time. The true value completes factorization. For $H\le\exp(O(b^{1/3}(\log b)^{2/3}))$ the overall bound retains the cube-root scale.

This small PARI/GP replay evaluates the block polynomial directly. The cubic example tests a class containing $217=\sigma(325)/2$. In the quadratic example the order at $5$ is $6$, and the order at $13$ is $7$. Exponents $14$ and $18$ give the two hits in the full block. Stripping a factor of two isolates $13$.

~~~gp
apProductGcd(n,g,a,step,count,degree) = {
  my(width=sqrtint(count),blocks=count\width, roots=vector(width,i,g^(-step*(i-1))));
  my(poly=prod(i=1,width,'x-roots[i]), value=g^0);
  for(j=0,blocks-1, value*=subst(poly,'x,g^(a+step*j*width)));
  for(t=width*blocks,count-1,value*=g^(a+step*t)-1);
  my(w=liftall(value));
  gcd(concat([n],vector(degree,i,polcoef(w,i-1,'y))))
};
{
  my(z=Mod(Mod(1,325)*y,y^3+y^2-2*y-1),g=(1+z)/(z^2-1));
  if(apProductGcd(325,g,191,2,28,3)!=5,error("cubic progression"));
  z=Mod(Mod(1,65)*y,y^2-2); g=(1+3*z)/(1-3*z);
  if(apProductGcd(65,g,10,4,4,2)!=65 || apProductGcd(65,g,5,2,4,2)!=13,
    error("quadratic progression"));
}
~~~

## Consequences using the input alone

*Perfect and multiply perfect numbers.* Since $\sigma(N)/N=\sum_{d\mid N}1/d\le1+\log N$, enumerate the $O(b)$ positive integers $j\le1+\log N$ as possible abundancies, using $jN$ as the supplied value. Run the bounded factorization search for each and, upon complete factorization, compute the actual $\sigma(N)$ by the product formula. Accept exactly when $N\mid\sigma(N)$, or check $\sigma(N)=2N$ when recognizing perfect numbers. This gives deterministic recognition on all inputs and complete factorization on yes-instances in $\exp(O_\delta(b^{1/3}(\log b)^{2/3}))$ bit operations. The same reasoning handles an integer interval of offsets about $jN$ by the progression search. Bach–Miller–Shallit gave randomized polynomial-time recognition for these families and for amicable pairs. [Bach–Miller–Shallit, Theorems 7–9](https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf#page=9)

*An arbitrary input.* The summatory function $S(x)=\sum_{m\le x}\sigma(m)$ gives the exact value as $S(N)-S(N-1)$. Tulsyan gives a $2^{O(b/\sqrt{\log b})}$ algorithm for $S(x)$ under the stated counting-engine assumptions. Two evaluations followed by the single-value algorithm retain that exponent. Li's analytic algorithm for an isolated divisor summatory value computes the unweighted sum of divisor counts in expected time $N^{9/28+o(1)}$. Bruin's fast modular-form coefficient theorem takes the index in factored form. His Eisenstein-series example explains the factoring problem for an unfactored semiprime index. For balanced $N=pq$, even the elementary approximation $N+1$ misses $\sigma(N)$ by $p+q=\Theta(\sqrt N)$. An uncertainty interval on that scale still costs $N^{1/4}$ in the progression bound. To improve the leaderboard exponent by this route, a sufficient target is an interval or congruence computable in $2^{o(b/\sqrt{\log b})}$ time leaving $H=2^{o(b/\sqrt{\log b})}$ candidates. The sources checked here leave this evaluator open. [Tulsyan, v2](https://hexagonmath.org/pdf/2611.00115v2) · [Li, abstract and Theorem 1](https://arxiv.org/abs/2609.29949) · [Bruin, Theorem 1.1 and Remarks](https://www.numdam.org/item/10.5802/pmb.a-133.pdf#page=2)

*One-bit modular queries.* There is also a nonadaptive reduction of computing $\sigma(N)$ to the parity of its least residue modulo small odd primes on slightly larger inputs. Choose consecutive odd primes $\ell$ until their product exceeds $N^2$. The prime number theorem gives $\ell=O(b)$ and $\sum_\ell\lceil\log_2\ell\rceil=O(b)$. Write $x=\sigma(N)\bmod\ell$, $0\le x<\ell$. For $1\le j\le u=\lceil\log_2\ell\rceil$ use the query at $Nr$ with a prime $r\nmid N$ satisfying $r+1\equiv2^j\bmod\ell$. When $2^j\equiv1\bmod\ell$ use $N$ itself. In the other cases $r$ can be chosen of size $b^{O(1)}$. Indeed choose an auxiliary prime $L>\max(b+2,\ell)$ of size $O(b)$ and impose each possible nonzero residue on $r\bmod L$ along with the given reduced class modulo $\ell$. Linnik's bound yields $L-1$ distinct candidate primes of polynomial size, exceeding the number of prime factors of $N$. Direct enumeration with a gcd finds one. [Xylouris, Theorem 1.1](https://www.impan.pl/shop/publication/transaction/download/product/83078)

By multiplicativity, the query bit is the parity of $2^j x\bmod\ell$, hence the parity of $\lfloor2^j x/\ell\rfloor$. The $u$ bits give $D=\lfloor2^u x/\ell\rfloor$, and $x$ is the only integer in $[\ell D/2^u,\ell(D+1)/2^u)$. CRT recovers $\sigma(N)$ from all $x$. This uses $O(b)$ exact one-bit queries on inputs of at most $b+O(\log b)$ bits. Computing these modular bits at arbitrary composite indices remains a separate cost. Ordinary parity of $\sigma(N)$ has the elementary square-or-twice-square test.

The following GP replay checks the one-bit reconstruction with direct divisor sums supplying the oracle bits. It tests the multiplier coprimality condition, repeated powers, and CRT reconstruction.

~~~gp
{
  for(n=2,300,
    my(ans=Mod(0,1));
    forprime(ell=3,200,
      my(u=logint(ell,2)+1,digits=0);
      for(j=1,u,
        my(t=(2^j-1)%ell,r=1);
        if(t,forprime(s=2,100000,
          if(s%ell==t && n%s,r=s;break));
          if(r==1,error("multiplier search")));
        digits=2*digits+(sigma(n*r)%ell)%2
      );
      ans=chinese(ans,Mod((ell*digits+2^u-1)\2^u,ell));
      if(component(ans,1)>n^2,break)
    );
    if(lift(ans)!=sigma(n),error("one-bit CRT at ",n))
  );
  print("one-bit divisor-sum reconstruction passed for 2 through 300")
}
~~~

Even on balanced semiprimes the residue of $N$ alone at a fixed odd prime $\ell$ leaves many possibilities for the modular query. Fix $N\equiv c\ne0\pmod\ell$. Writing $p\equiv x$ and $q\equiv c/x$, we obtain
$$
\sigma(pq)\equiv 1+c+x+c/x\pmod\ell.
$$
Two nonzero values $x,y$ give the same result exactly when $x=y$ or $xy=c$. The involution $x\mapsto c/x$ has $1+(c/\ell)$ fixed points, so there are exactly $(\ell+(c/\ell))/2$ distinct answers for the full residue, with $(c/\ell)$ the Legendre symbol. All occur for distinct primes $p,q\in(X,2X]$ for every sufficiently large $X$ by the prime number theorem in fixed arithmetic progressions. CRT realizes the choices independently for any fixed finite list of odd primes, even with the residue of $N$ prescribed at every listed prime. This obstruction concerns using only those prescribed residues of the input.
