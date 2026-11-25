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

## Reproduce two finite checks

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
