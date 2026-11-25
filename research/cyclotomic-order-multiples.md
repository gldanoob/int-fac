# Deterministic splitting from one cyclotomic multiple

Fix an integer $k\ge3$. Let $N$ have at least two distinct prime divisors, and let $M>0$ be divisible by $\Phi_k(p)$ for one unknown prime $p\mid N$. Under the uniform zero-free hypothesis below, the following deterministic search returns a proper divisor of $N$ in polynomial time in $\log N+\log M$. The exponent of the time bound may depend on $k$. Repeated prime divisors and arbitrary extra factors in $M$ are allowed.

For $k=3$ this removes both congruence restrictions in the [conductor-seven proof](cubic-order-multiples.md). For example, that field is inert at both primes of $85=5\cdot17$, and its projective group at each prime is killed by $31\cdot307$. The new search can split 85 even with that common exponent. The theorem gives a split on the supplied promise. Producing a suitable $M$ from an arbitrary $N$ remains open.

## The search uses integer polynomials

Write $d=M/2^{v_2(M)}$. At heights $T=1,2,4,\ldots$, run both steps.

1. Try all integer divisors from $2$ through $\min(T,N-1)$, returning any proper divisor.
2. For every monic $f\in\mathbb Z[X]$ of degree $2\le s\le k$ with its other coefficients in $[-T,T]$, compute $X^d\bmod(f,N)$. Return the gcd of $N$ and its $s-1$ nonconstant coefficients whenever this gcd is strictly between $1$ and $N$.

At fixed $k$ a round costs $O_k((2T+1)^k\,\mathrm{poly}(\log N+\log M+\log(2T)))$ bit operations. There is no irreducibility test. Every returned gcd is valid. We prove that some successful round has $T\le(2+\log N)^{O_k(1)}$. In the proof, call any quantity bounded this way *small*. If a prime divisor of $N$ divides a nonzero small integer, trial division already succeeds at a small height. This observation will cover all exceptional denominators and indices.

## Choosing a field in which the primes behave differently

The analytic input is a fixed $\delta>0$, independent of the fields, such that their Dedekind zeta functions have no zeros in $\Re(s)>1-\delta$. Frei, Sofos and Widmer, Corollary 1.2, then gives prime ideals with prescribed Frobenius in an interval $(x/2,x]$ once $x\gg_\delta(\log |D_L|)^{1/\delta}(\log\log |D_L|)^{2/\delta}$ for a Galois extension $L/K$. Its lower count is $|C|x/(4|G|\log x)$ for a conjugacy class $C$. Their bound is uniform in the degree. Cureton and Thorner, Theorem 1.1, reports the required strip with $\delta=1/32$ for all number fields. The proof here uses that number-field statement, which is stronger in scope than a result for rational Dirichlet characters alone. [Frei–Sofos–Widmer, Corollary 1.2](https://arxiv.org/html/2610.18491v2#S1.SS1) · [Cureton–Thorner, version 2](https://hexagonmath.org/pdf/2610.00200v2#page=3)

Choose a second prime $q\ne p$ dividing $N$. Trial division covers primes dividing $2k$. Over $F=\mathbb Q(\zeta_{2k})$, the classes of $p,q$ generate a copy of $(\mathbb Z/k)^2$ in $F^\times/F^{\times k}$, by valuations at primes over $p$ and $q$, both unramified. In $L=F(p^{1/k},q^{1/k})$ choose the automorphism over $F$ multiplying $p^{1/k}$ by a primitive $k$th root and fixing $q^{1/k}$. Kummer theory gives this automorphism. The extension is Galois over $\mathbb Q$. Its degree is bounded in terms of $k$, and $\log|D_L|=O_k(1+\log N)$ by the discriminant of the order with product basis from $F$, $X^k-p$, and $X^k-q$.

Chebotarev gives a small rational prime $\ell$ in the chosen conjugacy class. Thus $\ell\equiv1\pmod{2k}$, the class of $p$ generates $\mathbb F_\ell^\times/\mathbb F_\ell^{\times k}$, and $q$ is a $k$th power modulo $\ell$. These conditions hold for every conjugate of the chosen automorphism. In the degree-$k$ subfield $K$ of $\mathbb Q(\zeta_\ell)$, $p$ is inert and $q$ splits completely. This field is totally real since $-1$ is a $k$th power modulo $\ell$. Its discriminant is $\ell^{k-1}$ by the conductor–discriminant formula. This use of a varying cyclotomic field follows the conductor selection in Bach and Shallit. The search above never constructs $K$. [Bach–Shallit, §§6–8](https://www.ams.org/journals/mcom/1989-52-185/S0025-5718-1989-0947467-1/S0025-5718-1989-0947467-1.pdf)

## A bounded algebraic integer with prescribed quadratic signs

Put $\mathfrak m=pq\mathcal O_K$. A sign character here is a homomorphism $(\mathcal O_K/\mathfrak m)^\times\to\{\pm1\}$ trivial on rational residue units. For every nontrivial such character $\chi$ there is an algebraic integer with sign $-1$ whose conjugates all have small absolute value, unless trial division already succeeds.

First obtain an integral $z$ of small absolute norm with $\chi(z)=-1$. A global unit with this sign suffices. Otherwise the ray exact sequence induces a nontrivial character on $H=\ker(\mathrm{Cl}_{\mathfrak m}(K)\to\mathrm{Cl}(K))$ because $H$ is the quotient of the residue units by the image of global units. The kernel of this character, regarded as a subgroup of the full ray group, defines an abelian extension $E/K$ of degree $2h_K$, with $h_K$ the ordinary class number. Minkowski's bound represents each ideal class by an integral ideal of norm $O_k(\sqrt{|D_K|})$. There are polynomially many sublattices of bounded index in fixed rank, as one sees from Hermite normal form. Thus $h_K$ is small. The extension has finite conductor dividing $\mathfrak m$, so
$$
\log |D_E|\le 2h_K(\log |D_K|+k\log(pq)).
$$
This is small even though $|D_E|$ itself may be large. [Milne, Chapter V, ray exact sequence](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=159) · [Existence theorem](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=167) · [Conductor–discriminant formula](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=174)

Apply the same Chebotarev bound over $K$ to the nonidentity element of $H/\ker\chi$. Increase $x$ within a polynomial in $2+\log |D_E|+h_K$ so its lower count exceeds $2k$. A prime ideal with this Frobenius then exists away from $pq$. Its ordinary ideal class is trivial and it has small norm. Any integral generator $z$ has the prescribed sign, since the character was trivial on global units.

Small norm alone allows large conjugates. Write $b=|\mathrm{Nm}(z)|$, choose $C\ge1$ with $C^k>\sqrt{|D_K|}$ and $C^k\ge b$, with $C$ small. In the $k$ real embeddings put
$$
w_i(t)=|z_i|^t/b^{t/k},\quad 0\le t\le1,\qquad \prod_i w_i(t)=1.
$$
Subdivide the path finely enough that every adjacent ratio $w_i(t')/w_i(t)\le2$. At each point Minkowski gives a nonzero integral $a_t$ with $|(a_t)_i|\le Cw_i(t)$, since the box has volume $(2C)^k$ and the lattice covolume is $\sqrt{|D_K|}$. Use $a_0=1$ and $a_1=z$, both inside their boxes. The integer norm has magnitude between $1$ and $C^k$, so $|(a_t)_i|\ge w_i(t)/C^{k-1}$. For each adjacent pair
$$
y_t=|\mathrm{Nm}(a_t)|\,a_{t'}/a_t
$$
is integral and has all conjugates bounded by $2C^{2k}$. The factors telescope to $z$ times a rational integer with prime factors at most $C^k$. Trial division covers all failures of invertibility at $p,q$. The rational multipliers have trivial character, so some $y_t$ has sign $-1$. Only existence enters the running time. The algorithm enumerates neither the path nor units.

For two independent sign characters, the joint images of bounded elements span $\mathbb F_2^2$. Otherwise a nontrivial product of the characters would vanish on every bounded element, contrary to the preceding paragraph applied to each of the three products. Multiplying at most two such elements gives any specified sign pair, still with small conjugates.

## Projection to the cyclotomic order

Let $\sigma$ be Frobenius at $p$, a generator of $\mathrm{Gal}(K/\mathbb Q)$, and set
$$
U(X)=(X^k-1)/\Phi_k(X)=\sum_i u_i X^i,\qquad
\beta=\prod_i \sigma^i(\alpha)^{u_i}.
$$
Here $\alpha$ will be a bounded integral unit modulo $pq$. At $p$ the image of $\beta$ in $\mathbb F_{p^k}$ is $\alpha^{U(p)}$, so its order divides $\Phi_k(p)$. If $k$ is not a power of two this order is odd, since $\Phi_k(p)\equiv\Phi_k(1)\equiv1\bmod2$. If $k=2^j$ with $j\ge2$, then $\Phi_k(p)=p^{2^{j-1}}+1\equiv2\pmod8$. Requiring $\alpha$ to be a square at $p$ makes $\beta$ a square in the image of the power map $u\mapsto u^{U(p)}$, hence of odd order there. The quadratic character imposing this requirement is trivial on $\mathbb F_p^\times$ because $k$ is even.

At $q$, label the $k$ components cyclically under $\sigma$. Take the product of the quadratic signs in two adjacent components of $\beta$. As a character of $\alpha$ its exponent vector is $(1+X)U(X)$ in $\mathbb F_2[X]/(X^k-1)$, up to cyclic relabeling. This vector is nonzero because its polynomial is monic of degree $k-\varphi(k)+1<k$ for $k\ge3$. The character is trivial on diagonal scalars and can take either sign by choosing the components separately. For power-of-two indices it is independent of the sign at $p$ by CRT. The bounded-element argument therefore gives $\alpha$ with the product of the two signs at $q$ equal to $-1$ and, when required, positive sign at $p$.

The odd part $d$ of $M$ now kills $\beta$ at $p$, whereas $\beta^d$ has mixed signs at $q$ and consequently is nonscalar. A rational integer $A=|\mathrm{Nm}(\alpha)|^{\sum_{u_i<0}|u_i|}$ clears the denominators of $\beta$. All conjugates of $\gamma=A\beta$ are small because $k$ is fixed, all conjugates of $\alpha$ are small, and their product is a nonzero integer. Thus $\gamma^d$ is scalar at $p$ and nonscalar at $q$, with small prime divisors of $A$ covered by trial division.

## Why the polynomial search finds it

Let $f$ be the minimal polynomial of $\gamma$. Its degree $s$ is in $[2,k]$ by the nonscalar reduction. Its coefficients and its nonzero discriminant are small by the bounds on its roots. Outside primes dividing that discriminant, the power basis of $\mathbb Z[\gamma]$ gives the full integer ring of $\mathbb Q(\gamma)$ locally. Reduction of this subfield's integer ring embeds into $\mathcal O_K/t\mathcal O_K$ at each rational prime $t$, since $t\mathcal O_K\cap\mathbb Q(\gamma)=t\mathcal O_{\mathbb Q(\gamma)}$. Hence for this $f$, every nonconstant coefficient of $X^d\bmod f$ vanishes modulo $p$, and at least one survives modulo $q$. If either prime divides the discriminant, the trial step already splits $N$ within the bound. In all cases a small height suffices, including when other prime divisors or repeated powers occur in $N$.

## One divisor sum for bounded multiplicities

Fix $B\ge2$. Suppose each original exponent $e=v_p(N)>0$ has $e+1$ divisible by some prime $s\le B$. One value $M=\sigma(N)$ suffices for complete deterministic polynomial-time factorization under the same analytic input. Indeed, $\Phi_s(p)\mid (p^{e+1}-1)/(p-1)\mid M$. At every composite cofactor with two distinct primes, run the searches for the finitely many indices in parallel, reusing the original $M$. For $s=2$ use the [one-prime $p+1$ splitter](p-plus-one-multiples.md), whose Dirichlet prime-coset input also follows from a fixed zero-free strip by Chebotarev in the corresponding bounded-index abelian extension. Handle primes, powers and factors of two directly. Every prime in a cofactor retains its original promise regardless of how previous gcds divided its multiplicity. In particular this covers all inputs of bounded prime multiplicity, including cubefree integers with an arbitrary mix of first and second powers.

Bach–Miller–Shallit give randomized complete factorization from a single divisor sum for arbitrary multiplicities. Bach–Shallit give randomized splitting from a cyclotomic multiple. Źrałek's deterministic cyclotomic theorem uses a smooth value and a suitable fixed field. Publication priority for the deterministic result above has not been established. [Bach–Miller–Shallit, Theorem 2](https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf) · [Bach–Shallit](https://doi.org/10.1090/S0025-5718-1989-0947467-1) · [Źrałek, Theorem 5.5](https://arxiv.org/pdf/0707.4102#page=11)

## Finite checks

The height-one regression runs the polynomial search on indices $3,4,5,6$. It splits $85$ with $M=2^8\cdot31\cdot307$, handles a repeated prime in $2057=11^2\cdot17$, and splits $55$ even though the successful polynomial gives the identity at the full exponent. The quartic field example $N=235$, $M=26$ has $f=X^4+47X^3-164X^2+47X+1$. In its quotient $X^{13}=141+220X+115X^3\pmod{235}$, giving the factor $5$. At $47$ the roots $13,18,29,34$ have signs $-,+,-,+$. These are finite arithmetic checks. The uniform witness bound is a paper proof. [PARI/GP regression](../experiments/cyclotomic-multiples.gp)
