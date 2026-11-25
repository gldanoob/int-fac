# Point orders on rational CM curves over balanced semiprimes

Let $X<p<q\le 2X$ be primes and set $N=pq$. For a fraction tending to one of these pairs, on **every twist at all thirteen rational CM $j$-invariants**, the part of the local group order accessible to prescribed scalar tests has size $X^{o(1)}$. This holds at both prime factors and allows input-dependent scalars built from polynomials and fractional powers of $N$. On the same density-one set, prescribed rational point coordinates and a class of coordinates computed from $N$ cannot give different identity tests at the two factors. All estimates below are unconditional.

Earlier work in this repository treated two supersingular families on a set of primes of relative density tending to zero. The proof here also counts ordinary CM reductions, bounds the order of the actual marked point, and permits arbitrary twists chosen after seeing $N$. The question it addresses is whether stage one of the elliptic curve method can guarantee a factor by varying these curves, scalars and starting points. [Round 2](round-2.md#a-worst-case-obstruction-for-those-two-curve-families) · [Lenstra, *Factoring integers with elliptic curves*](https://annals.math.princeton.edu/1987/126-3/p09)

## Scalar schedules and possible local orders

Fix $0<\epsilon\le 1/2$. For each size $X$, prescribe a cutoff $Y=X^{o(1)}$ and a list of nonzero integer polynomials $F_i(U,V)$, integers $1\le a_i\le G=X^{o(1)}$, and real $\alpha_i\in[\epsilon,1-\epsilon]$. The sum of one plus the total degree and log absolute content over the polynomial list is $D=X^{o(1)}$. An admissible scalar test multiplies a point by any positive $Y$-smooth integer times a product of any of the nonzero values

$$E_i(N)=F_i\big(N,\lfloor(a_iN)^{\alpha_i}\rfloor\big)$$

with arbitrary nonnegative multiplicities. Signs have no effect on the identity test. An identically zero scalar gives the identity at both factors. These schedules include ordinary polynomial exponents and lists of fixed integers of total binary length $X^{o(1)}$. When addition chains test intermediate multiples or compare two multiples of the same point, include their nonzero indices and the relevant sums or differences in the schedule. An equality of abscissas tests equality up to sign.

There is an $R=X^{o(1)}$, depending only on the schedules and $X$, for which the following holds on a fraction $1-o(1)$ of the pairs. For each $t\in\{p,q\}$, each good short Weierstrass model $E/\mathbb F_t$ whose $j$ is the reduction of a rational CM invariant, and every admissible scalar $M$,

$$\gcd(M,\#E(\mathbb F_t))\le R.$$

In particular the cofactor left in the group order has size $X^{1-o(1)}$. The input-dependent choice of twist and of a listed test is unrestricted. With uniform random local points the probability of any identity hit in $X^{o(1)}$ trials at a given factor is $X^{-1+o(1)}$ or less. Indeed each kernel has at most $R^2$ points. The probability statement assumes uniform local sampling for each trial, or conditional uniformity when successive choices depend on previous outcomes.

**CM orders.** For all sufficiently large primes $p$, every group order in question belongs to a set $\mathcal A(p)$ of bounded size. Include $p+1$ and all the integers $\operatorname{Norm}(1-\pi)$ obtained from algebraic integers $\pi$ of norm $p$ in the nine imaginary quadratic fields of fundamental discriminants

$$-3,-4,-7,-8,-11,-19,-43,-67,-163.$$

These fields contain the thirteen rational CM orders, including the nonmaximal orders of discriminants $-12,-16,-27,-28$. At inert primes the reduction is supersingular by Deuring, giving trace zero for $p>3$. At ordinary primes the geometric endomorphism algebra is the CM field, which contains the Frobenius endomorphism $\pi$ of every twist. Its characteristic polynomial gives $\#E(\mathbb F_p)=1+p-\operatorname{Tr}(\pi)$. This argument uses the maximal order only to overcount the possible Frobenius elements. There are at most two prime ideals above $p$ and at most six unit multiples of each generator in each field. The finite exceptional primes of the fixed reference curves and discriminants can be omitted. [Classification of the thirteen invariants](https://www.sciencedirect.com/science/article/pii/S0022247X24011144) · [Akbary–Murty, §2](https://www.cs.uleth.ca/~akbary/greatestrevised2.pdf) · [Deuring reduction criterion](https://arxiv.org/abs/2203.08401)

**Small primes in ordinary orders.** Write $S_Z(n)=\prod_{\ell\le Z}\ell^{v_\ell(n)}$, over rational primes. Uniformly for cutoffs $2\le Z=X^{o(1)}$ and $p$ uniform over primes in $(X,2X]$,

$$\mathbb E_p\sum_{n\in\mathcal A(p)}\log S_Z(n)\ll \log(2Z)+o(1).$$

For $p+1$ this is the shifted-prime Brun–Titchmarsh bound. For a fixed ordinary CM field $K$ sum over every $\pi$ of norm $p$, allowing repeated values of $n$. In the factorization of $(1-\pi)$, each prime ideal power $\mathfrak l^h\mid(1-\pi)$ has weight $\log\mathrm N\mathfrak l$ and contributes if the rational prime below $\mathfrak l$ is at most $Z$. Put $L=\mathrm N\mathfrak l$. When $L^h\le\sqrt X$, Schaal's Brun–Titchmarsh theorem over $K$, with the archimedean disk $|\pi|\le\sqrt{2X}$ and residue $1\bmod\mathfrak l^h$, bounds the count of prime elements by

$$\ll_K \frac{X}{\log X}\frac{1}{L^{h-1}(L-1)}.$$

Summing in $h$ contributes $O(\log L/L)$ for this prime ideal after dividing by the number of primes in the dyadic interval. There are at most two ideals above $\ell$, with $L\in\{\ell,\ell^2\}$. Summing in rational primes gives $O(\log(2Z))$. For the remaining powers $\sqrt X<L^h\ll X$, points in the coset $1+\mathfrak l^h$ have mutual distance at least $\sqrt{L^h}$ in the complex plane, since the norm of any nonzero difference is a multiple of $L^h$. Disk packing bounds their number by $O(1+X/L^h)=O(\sqrt X)$. The sum of the weights for all powers of one ideal up to $O(X)$ is $O(\log X)$. Thus these large powers contribute $O(Z\log^2 X/\sqrt X)=o(1)$ to the expectation. The rational estimate for $p+1$ follows with $p\equiv-1\bmod\ell^h$ and the one-dimensional integer count. [Schaal, number field Brun–Titchmarsh](https://www.sciencedirect.com/science/article/pii/0022314X70900521) · [Cojocaru, Theorem 3.8, explicit uniformity in the ideal](https://www.alinacarmencojocaru.com/cojocaru-MathAnn-2008.pdf#page=10) · [Shifted-prime proof](cyclotomic-supply.md#subexponential-lists-at-fixed-cyclotomic-indices)

**Large scheduled divisors.** Write $b=1+\log X$, $Q=\lceil((D+1)b^4)^4\rceil$ and $Z=\max(2,Y,Q^4)$. Discard the $O(\sqrt X)$ primes with $p\mid n$ for some $n\in\mathcal A(p)$. For large $p$ this would force $n=p$ and $\operatorname{Tr}(\pi)=1$, a line containing $O_K(\sqrt X)$ elements of the integer lattice in the disk. For each $\ell>Z$ dividing a scalar polynomial's content, the integer $p+1$ captures $O(1+X/\ell)$ primes, and the ordinary possibilities capture $O_K(1+X/\ell)$ by packing in the cosets $1+\mathfrak l$ above $\ell$. There are $O(D)$ such primes $\ell$. Their discarded fraction is $O(Db(1/Z+1/X))=o(1)$.

Fix any remaining $p$. There are $O(b)$ prime divisors of $\prod_{n\in\mathcal A(p)}n$. For each one above $Z$, and each polynomial $F_i$ of positive degree $r_i$, the polynomial $F_i(pV,W)$ is nonzero modulo $\ell$. The floor-graph count gives at most $O_\epsilon(r_iX\log(2Q)/\sqrt Q)$ integers $X<v\le2X$ for which $\ell\mid E_i(pv)$. That count requires only $\ell>Q^4$, $\ell\nmid p$ and the nonzero polynomial condition. A nonzero constant outside its content has no hits. A union bound and the prime number theorem discard an $O_\epsilon(Db^2\log(2Q)/\sqrt Q)=o(1)$ fraction of partners. For polynomials of $N$ alone the simpler univariate bound $r_i(1+X/\ell)$ suffices. Exchange $p,q$ and remove the diagonal. On all surviving pairs every gcd in the theorem divides $S_Z(n)$ for the corresponding $n$. Markov's inequality with $\log R=\sqrt{b\log(2Z)}$ proves the claim simultaneously for the two prime positions and the whole bounded set $\mathcal A(t)$. [Floor-graph congruence bound and proof](2026-11-25-handoff/cyclotomic-supply/audit.md#scheduled-algebraic-powers-do-not-generically-give-full-order-multiples)

## Actual starting points, including adaptive twists

For a finite point $P=(x,y)$ on $y^2=x^3+Ax+B$ in characteristic greater than three, use the following normalized abscissa.

$$w(P)=\begin{cases} Ax/B & AB\ne0,\\ x^2/A & B=0,\\ x^3/B & A=0.\end{cases}$$

A change $(x,y,A,B)\mapsto(u^2x,u^3y,u^4A,u^6B)$ preserves $w$. On a fixed geometric curve its fibers are single orbits under automorphisms fixing the identity. This follows from the two choices of sign of $y$ in the generic case and the additional fourth or sixth roots of unity in the two special cases. Thus every point in one fiber has the same geometric order. Omit the finitely many primes where distinct rational $j$ values merge or a fixed reference model has bad reduction.

Prescribe a list, of total marked-coordinate description length $X^{o(1)}$, of either rational constants $z$ or expressions

$$z=H\big(\lfloor(aN)^\alpha\rfloor\big),\qquad 1\le a\le X^{o(1)},\qquad \epsilon\le\alpha\le1-\epsilon,$$

where $H$ is a nonconstant rational function over $\mathbb Q$ of degree $X^{o(1)}$, with numerator and denominator supplied as integer polynomials. Require the chosen affine marks to be defined at both factors. A formula $H(N,V)$ specializing to one of these functions at $N=0$ gives the same local marks where its denominator is invertible. For each probe use the same prescribed $j$ and formula at both factors. Both its twist and its choice among the listed probes may depend on $N$.

On a fraction $1-o(1)$ of balanced pairs, every admissible test gives the same identity decision at both prime factors for all these marks. Each nonconstant floor mark misses the identity at both. For constant marks the exact geometric torsion order, when finite, determines the decision. The same conclusions apply to the predicate that an endpoint has order dividing any fixed $k$ after including $k$ in the scalar schedule.

**Rational constants.** Fix a rational reference curve $E_j$ for each $j$. A rational $w=z$ lifts geometrically to a point $P$ in an extension $L/\mathbb Q$ of degree at most six. Solve a polynomial of degree at most three for $x$ and a quadratic for $y$. The absolute logarithmic heights of the coordinates are $O(1+h(z))$. For a nontorsion lift and $m\ge1$, the height of $x([m]P)$ is $O((m+1)^C(1+h(z)))$ for an absolute $C$ over the finite reference list. One direct proof uses a binary addition chain. Each doubling or addition of the fixed $P$ increases the coordinate heights by at most a constant multiple of the previous heights plus $O(1+h(z))$, using the rational group law. The chain has $O(\log(2m))$ steps and nontorsion excludes the exceptional equality with $\pm P$ at an addition after doubling.

At good primes a finite rational point of $E_j(L)$ reduces to the identity precisely where its abscissa has negative valuation on the integral short model. The log norm of the denominator ideal of $x([m]P)$ is at most $[L:\mathbb Q] h(x([m]P))$. Sum this bound over all marks and all $1\le m\le R$. The number of underlying rational primes removed is at most $X^{o(1)}$. Remove also prime divisors of the listed rational denominators. For every remaining prime, the reduction of the chosen lift is finite and has order larger than $R$, and every geometric point on any twist with the same $w$ has that order. This proves the nontorsion case.

The orders of all torsion lifts in degree at most six are uniformly bounded. Choose two different fixed good primes $s_1,s_2$ for the reference models. Reduction at a place over $s_i$ injects prime-to-$s_i$ torsion into $E_j(\mathbb F_{s_i^f})$ for some $f\le6$. The group sizes are bounded in terms of the two fixed primes and the thirteen curves. Use one bound for the prime-to-$s_1$ part and the second for the $s_1$-primary part. At all larger good rational primes reduction preserves the entire order. All twists with the prescribed $w$ therefore give the same identity decision for a common integer $M$.

In particular this covers any list of marked rational CM curves and points having total explicit binary length $X^{o(1)}$. Their values of $w$ form an allowed rational list. No global lift of the starting point on the particular chosen twist is required by the criterion.

**Moving marks.** At a good prime $p$, on a fixed reference curve the image under $w$ of all finite points of order at most $R$ has at most $\sum_{m\le R}m^2=O(R^3)$ elements over an algebraic closure. The same finite set covers every twist. Reduction of a prescribed nonconstant rational $H$ remains nonconstant after excluding $X^{o(1)}$ total primes. Indeed one nonzero minor of its numerator and denominator coefficient vectors witnesses nonproportionality. Also exclude primes making an entire denominator polynomial zero. Every finite target has at most $\deg H$ preimages where the denominator is nonzero.

For fixed $p$, put $T=a^\alpha X^{2\alpha}$. The function $v\mapsto(apv)^\alpha$ on $X<v\le2X$ has range $O(T)$ and derivative comparable to $T/X$, with constants depending only on $\epsilon$. Its integer part takes any specified residue modulo $p$ on at most

$$O_\epsilon((1+T/X)(1+X/T))\le X^{1-2\epsilon+o(1)}$$

integer values of $v$, counted with multiplicity. The number of marks, degrees, twists' common target values and $j$-invariants together give a factor $X^{o(1)}$. Thus $o(X/\log X)$ partners at each prime need removal. Apply this argument in both positions and intersect with the scalar conclusions. This also permits a prescribed $X^{o(1)}$ list of additive shifts inside $H$.

## Exact checks and scope

The replay tests 3,754 twist models at primes from 167 through 997. It checks every point count against a Frobenius norm list obtained independently from $t^2-4p=Df^2$ in the ordinary case. The models include 2,030 ordinary curves, 1,724 supersingular curves and 15 occurrences of the excluded trace one. Another 1,812 local checks verify $v_\ell(\operatorname{Norm}(1-\pi))=\sum_{\mathfrak l\mid\ell} f_{\mathfrak l}v_{\mathfrak l}(1-\pi)$, including ramified primes.

Among the 8,392 primes in $(100000,200000]$, all 512 simultaneous quadratic sign patterns occur, with 7 to 28 primes per pattern and 15 simultaneously inert. The replay checks the trace on 468 inert twist models and enumerates every point on 26 models at $p=3167$. At scalar 24, the largest union of normalized abscissas killed across twists at one $j$ has 47 elements. Two rational nontorsion examples give 2,400 comparisons of multiplication with reduction of rational denominators, with 113 actual reductions to the identity.

For $p=14423$, $q=18191$, scalar $\operatorname{lcm}(1,\ldots,11)=27720$, and normalized abscissas $\lfloor\sqrt N\rfloor$, $\lfloor\sqrt[3]N\rfloor$, $\lfloor\sqrt{2N}\rfloor+1$, $\lfloor\sqrt[3]{3N}\rfloor-1$, all 208 available local lifts on the thirteen invariants and their twists miss the identity. Each of the four marked values misses at both prime factors. Run `gp -fq experiments/rational-cm-obstruction.gp` from the repository root. [Exact replay](../experiments/rational-cm-obstruction.gp)

The density result concerns smooth elliptic multiplication and the specified identity or bounded-order tests. Constructing a model with a singular coefficient, directly exposing a factor while constructing the points, arbitrary comparisons of unrelated points, non-CM curves, and scalars or coordinates outside the formulas above require their own analysis. The remaining algorithmic question is how to choose sufficiently varied geometric curves or order information from $N$ with a deterministic guarantee.
