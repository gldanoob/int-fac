# Cyclotomic multiples computed from the input

For an infinite family of semiprimes, $N^2+N+1$ supplies the multiple needed by the deterministic polynomial-time splitter under its stated zero-free hypothesis. [Cyclotomic splitting theorem](cyclotomic-order-multiples.md) Both prime factors grow as positive powers of $N$ on this family. For balanced semiprimes, a different result limits this strategy. Given any fixed finite list of polynomial exponents and cyclotomic indices, a positive proportion of balanced prime pairs share only bounded gcds between **every** exponent and the full orders at **both** primes.

## An infinite family with a cubic multiple

Take any odd prime $p\equiv2\pmod 3$, put $A=p^2+p+1$, and let $u$ be the odd part of $p^2-1$. Choose the least prime $q$ satisfying

$$
q\equiv1\pmod A,\qquad q\equiv2\pmod u,\qquad q\equiv3\pmod8.
$$

These classes are compatible and reduced. In fact $A$ is odd, $\gcd(A,p+1)=1$, and $\gcd(A,p-1)=\gcd(3,p-1)=1$. Dirichlet's theorem supplies infinitely many starting primes $p$. Linnik's least-prime theorem gives $A<q\ll(8uA)^L$ for an absolute $L$. In particular $p^2<q\ll p^{4L}$, so the smaller factor $p$ of $N=pq$ grows at least as a fixed positive power of $N$. [Xylouris, introduction and Theorem 1.1](https://www.impan.pl/shop/publication/transaction/download/product/83078)

Since $N\equiv p\pmod A$, the integer $M=N^2+N+1$ is a positive multiple of $A$. Feed $N,M$ and the fixed index $3$ to the splitter. It returns one prime factor. Integer division gives the other. Computing $M$ takes polynomial time from $N$ alone. The CRT construction establishes the promise without supplying $p$ or $q$ to the algorithm. Bach–Shallit give an expected polynomial-time algorithm with the supplied multiple under their GRH hypotheses. The deterministic bound here uses the analytic inputs in the splitter. [Bach–Shallit, *Factoring with cyclotomic polynomials*](https://doi.org/10.1090/S0025-5718-1989-0947467-1) · [Deterministic splitting theorem](cyclotomic-order-multiples.md)

The simpler public choice $E=N^2-1$ leaves large residuals at both primes. We have $q^2-1\equiv3\pmod u$ and $v_2(q^2-1)=3$, giving $\gcd(p^2-1,q^2-1)\le24$. For either sign, $\gcd(p\pm1,E)=\gcd(p\pm1,q^2-1)\le24$, and the same holds with $p,q$ exchanged. The numerical residual $(t\pm1)/\gcd(t\pm1,E)$ is thus at least $(t-1)/24$ at each $t\in\{p,q\}$.

## A limit for every fixed list of polynomial exponents

Fix nonzero $P_1,\ldots,P_s\in\mathbb Z[X]$ and positive indices $k_1,\ldots,k_m$. For every $\epsilon>0$ there is a constant $C$ depending only on these lists and $\epsilon$ such that the following holds for all sufficiently large $X$. Among unordered distinct prime pairs $X<p,q\le2X$, a fraction at least $1-\epsilon$ satisfies

$$
\gcd\big(\Phi_{k_j}(t),P_i(pq)\big)\le C
\quad\text{for all }i,j,\quad t\in\{p,q\}.
$$

In particular, each residual $\Phi_{k_j}(t)/\gcd(\Phi_{k_j}(t),P_i(N))$ has size $\gg N^{\varphi(k_j)/2}$ on this set. The assertion concerns the size of the missing factor of a full cyclotomic value. The smoothness of the residual, the order at a particular algebraic element, and the behavior of input-specific exponent choices require separate estimates.

**Root counts.** For any fixed primitive polynomial $F\in\mathbb Z[X]$ squarefree over $\mathbb Q$, the number of roots modulo each prime power $\ell^a$ is $O_F(1)$. For nonconstant $F$, choose $U,V\in\mathbb Z[X]$ and $D\ne0$ with $UF+VF'=D$. Outside the prime divisors of $D$, there are at most $\deg F$ roots modulo $\ell$, each lifting uniquely. At a prime $\ell\mid D$ put $r=v_\ell(D)$. For $a\le2r+1$ the trivial bound is $\ell^{2r+1}$. For $a>2r+1$, every root $x$ satisfies $v_\ell(F'(x))\le r$. If $x,y$ are two roots agreeing modulo $\ell^{r+1}$, the factorization of $F(y)-F(x)$ by $y-x$ shows that they agree modulo $\ell^{a-r}$. Thus each class modulo $\ell^{r+1}$ contains at most $\ell^r$ roots modulo $\ell^a$. Only finitely many primes divide $D$.

**Mean log gcd.** Choose ordered primes $p,q$ independently and uniformly in $(X,2X]$. First take one primitive squarefree $F$ and one $\Phi_k$. The expectation of $\log\gcd(\Phi_k(p),F(pq))$ is the sum, over prime powers $d=\ell^a$, of $\log\ell$ times the probability that $d$ divides both values.

For $d\le\sqrt X$, the condition $d\mid\Phi_k(p)$ puts $p$ in $O_k(1)$ residue classes. Once $p$ is fixed, $p$ is a unit modulo $d$ and $d\mid F(pq)$ puts $q$ in $O_F(1)$ classes. All occupied classes are reduced because the primes exceed $d$. The prime number theorem gives $\asymp X/\log X$ choices in total at each step. The interval Brun–Titchmarsh inequality bounds the count in one reduced class by $\ll X/(\varphi(d)\log X)$ in this range. Thus the contribution is at most a constant times $\sum_{\ell,a\ge1}\log\ell/\varphi(\ell^a)^2$, with $\ell$ restricted to primes. This sum converges by a geometric sum in $a$ and comparison with $\sum_{n\ge2}(\log n)/n^2$. [Montgomery–Vaughan, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3)

For $d>\sqrt X$, fix $p$ and sum over $d\mid\Phi_k(p)$. Every such $d$ is coprime to $p$ since $\Phi_k(0)=\pm1$. Among all integers in $(X,2X]$ there are $O_F(1+X/d)=O_F(\sqrt X)$ admissible $q$ for each $d$. The sum of $\log\ell$ over all prime powers $\ell^a\mid\Phi_k(p)$ is exactly $\log\Phi_k(p)=O_k(\log X)$. Dividing by the number of primes in the interval bounds this part of the conditional expectation by $O_{F,k}(X^{-1/2}\log^2 X)$, uniformly in $p$.

For an arbitrary nonconstant $P_i$, write $P_i=c\prod_j f_j^{e_j}$ over the integers with distinct primitive irreducibles and set $F=\prod_j f_j$. For any positive $H$ and integer $z$,
$$
\gcd(H,P_i(z))\le |c|\gcd(H,F(z))^{\max_j e_j},
$$
as follows prime by prime. Constant $P_i$ give bounded gcds directly. Summing the bounded mean log gcds over the fixed lists and both prime positions gives $O(1)$. The event $p=q$ has probability tending to zero, so conditioning on distinctness preserves a bounded mean. Markov's inequality then gives the stated $C$ for unordered pairs. Taking larger and larger $X$ gives infinitely many distinct semiprimes.

The earlier two-shift obstruction supplies a large **prime divisor** of the residuals for one choice of exponent. Here Brun–Titchmarsh controls the **entire gcd** for any fixed polynomial list. Pomerance–Sorenson count integers factored by the randomized smoothness-based methods for the first two indices. The estimate here concerns balanced semiprimes and fixed polynomial exponents. [Two-shift obstruction](p-plus-one-multiples.md#why-the-two-public-shifts-do-not-cover-all-inputs) · [Pomerance–Sorenson, Theorem 2.1](https://math.dartmouth.edu/~carlp/PDF/paper100.pdf)

## Lists chosen by input size

The number of exponents and their degrees can even grow polynomially in the bit length. Write $b=\log X$, fix $A>0$ and a finite list of indices $k$. For each $X$ choose a nonzero $P_X\in\mathbb Z[T]$ independently of the specific prime pair. Suppose $\deg P_X\le b^A$ and $\log(2|\operatorname{content}(P_X)|)\le b^A$. For a fraction tending to one of the balanced pairs, simultaneously at every listed index and both prime factors $t$,

$$
\log\gcd(\Phi_k(t),P_X(N))\le (\log b)^2.
$$

This allows a product of scheduled polynomials, including a size-dependent constant exponent. For example, $\operatorname{lcm}(1,\ldots,\lfloor b^c\rfloor)\prod_{j\le b^c}(N^j-1)$ satisfies the hypotheses for every fixed $c>0$ with a suitable $A$. The residual then has size at least $\gg_k N^{\varphi(k)/2}\exp(- (\log b)^2)$ on a fraction tending to one. If the list is selected by the bit length of $N$, at most three different bit lengths occur in $X^2<N\le4X^2$. Multiplying their schedules adds degrees and, by Gauss's lemma, adds log absolute contents. Both bounds remain polynomial in $b$. Choices that use further information about the specific input require a different argument.

**Proof.** Set $Y=b^{A+5}$. First estimate the entire contribution of primes $\ell\le Y$ to $\log\Phi_k(p)$. For $d=\ell^a\le\sqrt X$, the root bound and Brun–Titchmarsh above give probability $O_k(1/\varphi(d))$ that $d\mid\Phi_k(p)$. Summing $\log\ell/\varphi(\ell^a)$ first over $a$ gives $O(\log\ell/\ell)$ for each prime. The prime number theorem and partial summation give $\sum_{\ell\le Y}(\log\ell)/\ell=O(\log Y)$. For $d>\sqrt X$, only powers up to $O_k(X^{\varphi(k)})$ occur. Their total log weight for each $\ell$ is $O_k(b)$. Each power captures $O_k(\sqrt X+1)$ integers in the interval, so the large-power contribution to the expectation is $O_k(Yb^2/\sqrt X)=o(1)$. The expected log of the full $Y$-smooth part is therefore $O_{k,A}(\log b)$. Markov's inequality bounds the probability it exceeds $(\log b)^2$ by $O_{k,A}(1/\log b)$.

For $\ell>Y$ dividing the content, the root count for $\Phi_k$ bounds the number of admissible $p$ by $O_k(X/Y+1)$ per prime. There are $O(b^A)$ such primes. For the remaining primes, fix $p$. There are $O_k(b)$ prime divisors of $\Phi_k(p)$, all coprime to $p$. Modulo each $\ell>Y$ outside the content, $P_X(pT)$ is a nonzero polynomial of degree at most $b^A$. Thus at most $b^A(X/Y+1)$ integers $q$ in the interval are admissible at that prime. A union bound, dividing in each case by $\asymp X/b$ prime candidates, gives a total exceptional probability $O_k(b^{A+2}(1/Y+1/X))=o(1)$. Exchange $p,q$, sum over the fixed indices, and discard the diagonal. On the same good pairs every prime above $Y$ in a selected $\Phi_k(t)$ survives in its residual. At least one exists for large $X$ because the entire small-prime contribution has logarithm at most $(\log b)^2$. Choosing $A$ larger also allows $Y$ to exceed any specified fixed power of $b$. The fixed-list result above gives the stronger constant gcd bound at any prescribed positive exceptional fraction.

### Subexponential lists at fixed cyclotomic indices

The obstruction also applies at the time scale of the factoring benchmark. Keep the list of indices $k$ fixed. Allow the total polynomial degree and the bit length of the absolute content of the product polynomial to be as large as $D=X^{o(1)}$. Let $Y_0=X^{o(1)}$ be any prescribed cutoff, for example the benchmark time itself at inputs of size $X^2$. On a fraction tending to one of the balanced pairs, at both primes and all the chosen indices, the residual has logarithm $(1-o(1))\log\Phi_k(t)$ and contains a prime greater than $Y_0$.

Indeed set $b=\log X$, $Y=\max(2,Y_0,D)b^5$. Then $Y=X^{o(1)}$. The proof above bounds the expected logarithm of the entire $Y$-smooth part of $\Phi_k(p)$ by $O_k(\log Y)+O_k(Yb^2/\sqrt X)$. By Markov it is at most $\sqrt{b\log Y}=o(b)$ outside a set of density $o(1)$. The large-prime union bound for primes dividing the content or the primitive polynomial value is $O_k(Db^2(1/Y+1/X))=o(1)$. Thus the part above $Y$ survives in full, and its logarithm is $\log\Phi_k(p)-o(b)$. The same proof handles the other prime and the fixed finite list of indices. It leaves open exponents constructed from input-specific arithmetic beyond membership in a prescribed list and methods exploiting orders of individual elements.

### Simultaneously growing cyclotomic indices

The same conclusion holds simultaneously for **every** $1\le k\le K$ with $K=X^{o(1)}$. Both $K$ and the polynomial schedule may depend on $X$. On a fraction tending to one of the balanced pairs,
$$
\max_{1\le k\le K,\ t=p,q}
\frac{\log\gcd(\Phi_k(t),P_X(pq))}{\log\Phi_k(t)}=o(1),
$$
and every residual has a prime factor exceeding any prescribed $Y_0=X^{o(1)}$. In particular a deterministic subexponential budget for precomputing a polynomial list and choosing indices, by itself, does not supply a small residual on all inputs.

Set $Z=\max(2,Y_0,K^2(D+1))b^5=X^{o(1)}$, where $b=\log X$ and $D\ge1$ bounds the total degree and log absolute content. First control the full $Z$-smooth part of $\Phi_k(p)$. At primes $\ell\nmid k$, all roots of $\Phi_k$ are simple and have exact order $k$ modulo $\ell$. Thus $\ell\equiv1\bmod k$ is necessary and each prime power has at most $\varphi(k)$ roots. If $\ell\mid k$, write $k=k'\ell^j$ with $\ell\nmid k'$. At an odd such $\ell$, any root implies that the order of $p$ modulo $\ell$ is $k'$, by reducing the cyclotomic identity modulo $\ell$. Lifting the exponent in $p^{k'\ell^j}-1$ and subtracting the valuation at $k'\ell^{j-1}$ gives exactly one factor of $\ell$ in the quotient, of which $\Phi_k(p)$ is a divisor. At $\ell=2$ a root requires $k'=1$, and $p^{2^{j-1}}+1$ is $2\bmod8$ for $j\ge2$. Hence the ramified-prime contribution is at most $\log k$, except for $k=2,\ell=2$, which we include in the simple one-root estimates for $X+1$.

If a simple-root contribution at $\ell\le Z$ has $\ell^{v_\ell(\Phi_k(p))}>X^{1/4}$, its first power $d$ crossing $X^{1/4}$ already has this divisibility. For each $\ell,k$ that power admits at most $O(\varphi(k)(X^{3/4}+1))$ integers $p$ in the interval. Summing over $\ell,k$ and dividing by the number of primes shows this happens anywhere with probability $O(K^2 Z b X^{-1/4})=o(1)$.

Let $S_k$ sum $\log\ell$ for the remaining simple prime powers dividing $\Phi_k(p)$, truncated at $X^{1/4}$, with $\ell\le Z$. Uniformly in $k$,
$$
\mathbb E S_k^2 \ll (\log Z+\log^2(2k))^2 .
$$
For distinct primes the lcm of two truncated powers is at most $\sqrt X$. CRT and interval Brun–Titchmarsh bound their joint divisibility probability by $O(\varphi(k)^2/(\varphi(d_1)\varphi(d_2)))$. For two powers of the same prime, the larger one suffices. Summing $\sum_{a\ge1}(2a-1)/\varphi(\ell^a)\ll1/\ell$ bounds the diagonal contribution by $O(\varphi(k)\sum (\log\ell)^2/\ell)$ over eligible primes. The required first-power estimate is
$$
\varphi(k)\sum_{\ell\le Z,\ \ell\equiv1\bmod k}\frac{\log\ell}{\ell}
\ll \log Z+\log^2(2k).
$$
Up to $k^2$, sum over integers $1+jk$ using $\varphi(k)\le k$. Above $k^2$, Brun–Titchmarsh gives $\pi(t;k,1)\ll t/(\varphi(k)\log t)$, and partial summation gives the bound. The exception at 2 costs an absolute constant. This proves the second moment since the diagonal has only one additional factor of at most $\log Z$. [Montgomery–Vaughan, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3)

Now $\log\Phi_k(p)\ge\varphi(k)\log(p-1)$ from the distances to its complex roots. The elementary bound $\varphi(k)\gg k^{3/4}$ follows from $1-1/\ell\ge\ell^{-1/4}$ for primes $\ell\ge5$, treating 2 and 3 with an absolute constant. Summing the second moments of $(S_k+\log(2k))/\log\Phi_k(p)$ over $k\le K$ gives $O((1+\log Z)^2/b^2)=o(1)$ because $\sum_k(1+\log^4(2k))/\varphi(k)^2$ converges. Markov bounds the maximum simultaneously by a quantity tending to zero outside a set of vanishing density.

Finally, a content prime $\ell>Z$ divides some $\Phi_k(p)$ at at most $O(K^2(X/Z+1))$ integers $p$ per prime, by the finite-field root bound. Outside the content, condition on $p$. Across all indices the product of the $\Phi_k(p)$ has logarithm $O(K^2 b)$ by $\Phi_k(p)\le(p+1)^{\varphi(k)}$. Each of its large prime divisors leaves at most $D(X/Z+1)$ possible integers $q$ with $P_X(pq)\equiv0\bmod\ell$. Both union bounds together cost $O(DK^2b^2(1/Z+1/X))=o(1)$ in probability. Thus every tested cyclotomic value retains its full part above $Z$ on the good pairs. The argument applies to both prime positions and survives exclusion of the diagonal.

## Exponents that use an integer square root of the input

For each size $X$, choose nonzero polynomials $F_i(U,V)\in\mathbb Z[U,V]$ and positive integer multipliers $a_i\le G$. The choices may vary with $X$. Assume $G,K,Y_0=X^{o(1)}$ and
$$
\sum_i\big(1+\deg F_i+\log(2|\operatorname{content}(F_i)|)\big)\le D=X^{o(1)}.
$$
At the actual input $N=pq$, evaluate the exponents
$$
E_i(N)=F_i(N,\lfloor\sqrt{a_iN}\rfloor).
$$
There is a cutoff $Z\ge Y_0$ with $Z=X^{o(1)}$ such that, on a fraction tending to one of balanced prime pairs, every prime $\ell>Z$ dividing any $\Phi_k(t)$, $k\le K$ and $t\in\{p,q\}$, is coprime to **every** $E_i(N)$. The full part above $Z$ therefore survives in the residual even if the algorithm selects entries after seeing the input or multiplies the entries together. Simultaneously the maximum of $\log\gcd(\Phi_k(t),\prod_i E_i(N))/\log\Phi_k(t)$ tends to zero on these pairs. When $G,D,Y_0$ are polynomial in $\log X$ and the indices are fixed, the log gcd is at most $(\log\log X)^2$ on a fraction tending to one.

This covers the residuals $a_iN-(\lfloor\sqrt{a_iN}\rfloor+j_i)^2$ used as candidate exponents, with scheduled integer offsets $j_i$. Lehman's algorithm uses a related square-root window to detect a perfect square and find a factor. Its perfect-square test is outside the exponent divisibility assertion here. [Lehman, *Factoring large integers*](https://doi.org/10.1090/S0025-5718-1974-0340163-2)

**A congruence on one curved graph.** Write $b=\log X$. Put
$$
Q=\lceil(D+1)(K+1)^2(1+b)^4\rceil,\qquad H=Q^2,\qquad
Z=\max(Y_0,16(1+\sqrt G)H).
$$
All three parameters are $X^{o(1)}$. Fix $p\in(X,2X]$, $1\le a\le G$, and a prime $\ell>Z$ coprime to $p$ and to the content of a nonzero polynomial $F$. Write $r=\deg F$. The number of integers $v\in(X,2X]$ such that
$$
F(pv,\lfloor\sqrt{apv}\rfloor)\equiv0\pmod\ell
$$
is $O(rX/Q)$ with an absolute implied constant for sufficiently large $X$. A nonzero constant modulo $\ell$ has no hits.

To see this, partition the interval of integers into blocks of length $H$, with one possibly shorter final block. Let $s$ be the first integer in a block and $g(v)=\sqrt{apv}$. Dirichlet approximation supplies a reduced fraction $u/d$ with $1\le d\le Q$ and $|g'(s)-u/d|\le1/(dQ)$. Throughout the interval $|g'|\le\sqrt G$ and $|g''|\asymp\sqrt a/X$. Taylor's formula puts every integer $d\lfloor g(v)\rfloor-uv$ in an interval of length
$$
O(d+H/Q+d\sqrt G\,H^2/X)=O(Q).
$$
Thus each block lies on $O(Q)$ parallel lines in the $(v,\lfloor g(v)\rfloor)$ plane.

The polynomial $F(pV,Y)$ is nonzero over $\mathbb F_\ell$. It has at most $r$ distinct nonvertical line factors. Call a rational slope exceptional if its reduction modulo $\ell$ equals the slope of one of them. All possible reduced fractions above satisfy $|u|\le(1+\sqrt G)Q$. Their pairwise cross-determinants have magnitude less than $\ell$, so different fractions give different slopes modulo $\ell$. There are at most $r$ exceptional fractions. For each one, the corresponding block starts must satisfy $|g'(s)-u/d|\le1/Q$. Monotonicity and $|g''|\gg1/X$ restrict those starts to an interval of length $O(X/Q)$. The union of those blocks contains $O(X/Q+H)$ integers per fraction.

On every other block, restricting $F(pV,Y)$ to any of the parallel lines gives a nonzero univariate polynomial of degree at most $r$. Each intercept therefore has at most $r$ hits because the block has fewer than $\ell$ integers. The total from these blocks is $O((X/H+1)Qr)$. Adding the exceptional blocks gives $O(rX/Q)$ since $Q^3=X^{o(1)}$. Related lattice-point estimates use rational tangent slopes for convex curves. Here the elementary block bound also allows arbitrary coefficients of $F$ outside its content. [Huxley, *The rational points close to a curve*](https://www.numdam.org/article/ASNSP_1994_4_21_3_357_0.pdf)

**Application to the cyclotomic values.** There are $O(D)$ primes dividing any content. The preceding finite-field root counts bound the chance that any such prime above $Z$ divides a tested value by $O(DK^2b(1/Z+1/X))=o(1)$. For the other primes, condition on $p$. The product of the cyclotomic values at $p$ across $k\le K$ has $O(K^2 b)$ distinct prime factors and all are coprime to $p$. For each such $\ell>Z$, sum the curved-graph bound over the menu and divide by the $\asymp X/b$ prime candidates for $q$. The probability of any hit is $O(DK^2 b^2/Q)=o(1)$. Exchange $p,q$ and discard the diagonal. The smooth-part estimate above applies at this $Z$, which proves both the relative bound and the sharper fixed-index statement when $Z$ is polynomial in $b$.

**Finite check.** Fix $p=46273$ and $\ell=10111\mid\Phi_3(p)$. For $32768<v\le65536$, use $Q=7$ and the polynomial $(2Y-v-p+2)(Y^2-apv-7)$. Its sole exceptional slope is $1/2$. For $a=1,4,37$, the numbers of hits on ordinary blocks were $0,3,7$, respectively. Exceptional blocks contributed $610,0,0$. The most distinct intercepts in one block were $12,13,13$. This example exercises the need to account for the tangents parallel to a line factor. The following GP block checks the counts with integer arithmetic.

~~~gp
{
  my(x0=32768,p=46273,ell=10111,Q=7,H=Q^2);
  if(!isprime(p)||!isprime(ell)||(p^2+p+1)%ell,error("cubic prime"));
  foreach([1,4,37],a,
    my(good=0,bad=0,most=0,direct=0);
    forstep(v0=x0+1,2*x0,H,
      my(u,d=0);
      for(e=1,Q,
        u=(sqrtint(e^2*a*p\v0)+1)\2;
        my(w=e^2*Q^2*a*p);
        if(gcd(u,e)==1 && 4*v0*max(0,u*Q-1)^2<=w && w<=4*v0*(u*Q+1)^2,d=e;break)
      );
      if(!d,error("missing slope"));
      my(lines=Map(),hits=Map());
      for(v=v0,min(v0+H-1,2*x0),
        my(y=sqrtint(a*p*v),z=d*y-u*v,nv=0);
        mapput(lines,z,1);
        if((2*y-v-p+2)*(y^2-a*p*v-7)%ell==0,
          mapisdefined(hits,z,&nv); mapput(hits,z,nv+1);
          if(2*u==d,bad++,good++;if(nv>=3,error("line root bound")))
        )
      );
      most=max(most,#lines)
    );
    for(v=x0+1,2*x0,my(y=sqrtint(a*p*v));direct+=((2*y-v-p+2)*(y^2-a*p*v-7)%ell==0));
    if(direct!=good+bad,error("direct count"));
    print([a,good,bad,most])
  )
}
~~~

## Reproduce the cubic supply and fixed-list checks

From the repository root, run the following PARI/GP block. It constructs the least $q$ for three choices of $p$, then supplies only $N,N^2+N+1$ to the degree-three search. In the balanced sample it counts pairs satisfying all 36 bounds for three exponents, six indices, and both prime factors. The threshold 48 is an example for this finite interval.

~~~gp
read("experiments/cyclotomic-multiples.gp");
{
  foreach([5,23,47],p,
    my(a=p^2+p+1,u=(p^2-1)>>valuation(p^2-1,2));
    my(q=lift(chinese([Mod(1,a),Mod(2,u),Mod(3,8)])));
    while(!isprime(q),q+=8*u*a);
    my(n=p*q,m=n^2+n+1);
    if(m%a || gcd(p^2-1,q^2-1)>24 || splitCyclotomicBox(n,m,3,1)[1]!=p,
      error("cubic supply at ",n));
    print([p,q,n])
  );
  my(total=0,small=0);
  forprime(p=501,1000,forprime(q=p+1,1000,
    my(n=p*q,largest=0);
    foreach([p,q],t,for(k=1,6,
      my(h=subst(polcyclo(k),x,t));
      foreach([n^6-1,n^2+n+1,(n-1)^2],e,largest=max(largest,gcd(h,e)))
    ));
    total++;
    if(largest<=48,small++)
  ));
  if([small,total]!=[570,2628],error("balanced sample"));
  print([small,total])
}
~~~

Expected outputs are $[5,683,3415]$, $[23,549683,12642709]$, $[47,8635283,405858301]$ and $[570,2628]$.
