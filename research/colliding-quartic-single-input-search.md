# Searching for a square relation in the colliding quartic

The [quartic that splits 4123](cogentic-sparse-smooth-tower-marks.md#a-collision-that-gives-a-factor-on-a-particular-input) admits a two-parameter search from a single integer. Each trial uses just integer products and gcds. In the nonsingular parameter range below, exactly half of the valid pairs split a product of two distinct odd primes. The cost lies in finding a valid pair. On balanced large semiprimes, independent uniform parameter trials take expected time of order the input's *value* to obtain a productive pair.

## Classification and the two integer tests

Let $Q=X(X-B)$ and $P=Q^2+S$ be irreducible over the rationals, with $B\ne0$ and $S>0$. Put $\gamma=Q(\alpha)$ for a root $\alpha$ of $P$. The quadratic field $E=\mathbf Q(\gamma)$ has $\gamma^2=-S$ and $K=E(\sqrt{B^2+4\gamma})$. Squaring in a quadratic extension shows that $\gamma$ is square in $K$ exactly when $\gamma$ or $(B^2+4\gamma)/\gamma$ is square in $E$.

* In the first case $S=4v^4$ for a nonzero rational $v$, by comparing coefficients in $(v+w\gamma)^2=\gamma$. The root is $v+\gamma/(2v)$. At a rational-side square $Q(m)=z^2\pmod N$, its two sign tests are the numerators $z^2\pm2vz+2v^2$. Their product is $z^4+4v^4$.
* In the second case write $(B^2+4\gamma)/\gamma=(u+c\gamma)^2$. Comparing coefficients gives $u^2-Sc^2=4$ and $2uc=-B^2/S$. Thus $|u|>2$ and
  $$
  S=\frac{B^4}{4u^2(u^2-4)},\qquad c=-\frac{2u(u^2-4)}{B^2}.
  $$
  A square root of $\gamma$ is $(2\alpha-B)/(u+c\gamma)$. The shape $u=4$ and scale $B=12$ recover $S=27$.

Consider an odd $N$ and a simple modular evaluation $m$ where $B,m,Q(m)$ and all displayed denominators are units. Given a rational-side root $z^2=Q(m)\pmod N$, set $s=z/m$. Conversely a proposed slope $s$ with $1-s^2$ a unit gives $m=B/(1-s^2)$ and $z=ms$. Write $s=a/b$ and $u=x/y$, with $b,y$ units. Define integers
$$
 H_\pm=(b^2-a^2)^2y^2+2a^2b^2x^2\ \pm\ 2ab(a^2+b^2)xy .
$$
In addition to invertible denominators, assume $2abxy(b^4-a^4)(x^2-4y^2)$ is a unit. This includes the simple-root condition $2m-B\ne0$ at every prime of $N$. If a test of these conditions exposes a proper gcd, that gcd already splits the input. The following counts concern trials passing the conditions.

With $a=s,b=y=1,x=u$, the product $H_-H_+$ is $(1-s^2)^4+4u^2(u^2-4)s^4$. Therefore $P(m)=0\pmod N$ precisely when $N\mid H_-H_+$. Homogenizing multiplies the factors only by units. Their difference is a unit, so each prime power in $N$ divides exactly one of the two factors at a valid pair. At primes dividing $H_-$, the field root evaluates to $+z$, and at those dividing $H_+$ it evaluates to $-z$. Indeed, before homogenization,
$$
 (2m-B)\mp z(u+cz^2)
 = B\frac{(s^2\pm su+1)H_\mp}{(1-s^2)^3}.
$$
The denominator of the field root is a unit since $(u+cQ(m))^2=(2m-B)^2/Q(m)$. Thus $\gcd(N,H_-)$ gives exactly the partition of prime powers obtained by comparing the two square roots.

Every admissible residue $u$ can be lifted to an integer $u>2$. Choosing $B=2u(u^2-4)$ gives $S=4u^2(u^2-4)^3$, a positive nonsquare integer since $(u-1)^2<u^2-4<u^2$ for $u\ge3$. Then $\gamma$ is nonsquare in $E$ by its norm and $B^2+4\gamma$ has that same nonsquare class in $E$. The resulting quartic is irreducible and realizes the search. This lift costs polynomial bit work in $\log N$.

## How often uniform trials work

For an odd prime $p$, put $D(s)=-s^4+6s^2-1$ and let $\chi_p$ be the quadratic character, extended by zero at zero. Define
$$
 h_p=\sum_{s\in\mathbf F_p,\;s(s^4-1)\ne0}(1+\chi_p(D(s))).
$$
There are exactly $h_p$ valid residue pairs on each sign branch. For each permitted $s$, the equation $H_\pm(s,1,u,1)=0$ is quadratic in $u$ with discriminant $4s^2D(s)$. Its roots automatically avoid $u=0,\pm2$ by the product identity. The branches are disjoint and $u\mapsto-u$ exchanges them. In odd characteristic $D$ has no multiple roots. The smooth projective model of $w^2=D(s)$ has genus one, so the Hasse bound, after discarding at most two points at infinity and at most ten above the excluded slopes, gives $h_p=p+O(\sqrt p)$.

For $N=pq$ with distinct odd primes, draw $s,u$ independently and uniformly modulo $N$. By the Chinese remainder theorem there are $4h_p h_q$ admissible roots among $N^2$ trials and exactly $2h_p h_q$ split by the branch gcd. Thus for balanced growing primes the productive probability is $(2+o(1))/N$. Half the valid samples split when the valid set is nonempty. Repeated independent trials therefore require $(1+o(1))N/2$ proposals on average for this mechanism. This count excludes incidental proper gcds during unit checks or from $H_-$ when $H_-H_+$ is nonzero modulo $N$. Retaining the immediate gcds improves the search. In the replay this version first takes one gcd with the product in the unit screen, skipping the pair if that gcd is all of $N$. On passing the screen it tries both branch gcds, even at an invalid evaluation. For $p,q\ge5$ write $C_p=(p-1-\gcd(4,p-1))(p-3)$ for the number of clean pairs, $D_p=p^2-C_p$ for the singular pairs, and $Z_p=C_p-2h_p$ for clean pairs on neither branch. The exact number of trials giving a proper gcd is
$$
 N^2-D_pD_q-Z_pZ_q-2h_p h_q .
$$
A miss requires singularity at both primes, or both clean with the same branch status (neither, minus or plus). Expanding with $h_p=p+O(\sqrt p)$ gives success probability $\Theta(1/p+1/q)$ for large primes. Thus retaining these partial hits costs $\Theta(\sqrt N)$ uniform proposals on comparable semiprimes. A sampler generating points directly would require its own analysis.

## Height obstruction and replay

If $|a|,|b|\le A$ and $|x|,|y|\le U$, each branch integer has magnitude at most $7A^4U^2$. For nonzero rational $s\ne\pm1$, neither branch can vanish over the rationals. A rational zero would force $D(s)=w^2$. Set $j=(s^2-1)/(2s)$, $h=(s^2+1)/(2s)$ and $v=w/(2s)$. Then $h^2=1+j^2$ and $v^2=1-j^2$. The absolute values of $(h+v)/j,(h-v)/j,2/j$ would give a rational right triangle of area one, contrary to Fermat's right triangle theorem. [Fermat's theorem and its proof](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/congnumber.pdf)

Consequently a prime divisor larger than $7A^4U^2$ cannot divide either branch. On a balanced semiprime, even an input-dependent choice of parameters with $A,U=N^{o(1)}$ misses both primes for sufficiently large inputs. This height argument permits using a short rational representative of a large residue as either parameter. Fast methods generating residues of large rational height remain outside its scope.

The [standalone replay](../experiments/colliding-quartic-search.py) counts every residue pair for five semiprimes and compares with the character formula. Its height-four search starts with $N=4123$ alone and finds $19$ on candidate six. The same search exhausts ten candidate pairs on $1009\cdot1013$ with no split. Each run constructs its candidates afresh. These checks give a search with a measured cost and expose the remaining requirement of a faster method to generate productive parameters.

## A fixed rational square class supplies a simple evaluation for every input

Changing the target from $\gamma$ to $\gamma/5$ makes it possible to construct an irreducible quartic and matching rational and algebraic squares in polynomial time for every $N\ge7$ coprime to $30$. Trial division handles the excluded primes. The construction also determines the sign everywhere, which explains precisely what remains to obtain a factor.

Take $u=N+4$, $D=u^2(u^2-20)$, $v=-u(u^2-20)/40$, and define
$$
 m=D,\qquad B=-4D,\qquad Q=X(X-B),\qquad P=Q^2+1600D^3 .
$$
All coefficients have $O(\log N)$ bits. Here $Q(m)=5D^2$ as an integer. Since $P(m)=25D^3(u^2-4)(u^2-16)$, we have $N\mid P(m)$. Moreover $D\equiv-64\pmod N$, so $P'(m)=60D^3$ is a unit.

For a root $\alpha$ write $\gamma=Q(\alpha)$. In $E=\mathbf Q(\gamma)$ an exact identity is
$$
 B^2+4\gamma=(\gamma/5)(u+v\gamma/D^2)^2 .
$$
It follows by comparing coefficients using $\gamma^2=-1600D^3$. The norm of $\gamma/5$ from $E$ is $64D^3$, nonsquare since $(u-1)^2<u^2-20<u^2$ for $u\ge11$. Hence the quadratic for $\alpha$ over $E$ is irreducible and $P$ has degree four as a minimal polynomial. The field root $(2\alpha-B)/(u+v\gamma/D^2)$ of $\gamma/5$ evaluates to $6D/(u+5v)\equiv D\pmod N$. The rational-side root is also $D$.

More generally take any integer lift $u\ge11$ with $D$ invertible modulo $N$. A valid evaluation in this chart requires $u\equiv2,4,-2$ or $-4$ at each prime power dividing $N$. These four roots are disjoint locally since $N$ is coprime to $30$. Their respective values of $u+5v$ are $6,6,-6,-6$. Thus the positive-sign component of $N$ is exactly $\gcd((u-2)(u-4),N)$. For a uniform residue $u$, exactly $4^{\omega(N)}$ residues give valid evaluations and $4^{\omega(N)}-2^{\omega(N)+1}$ give mixed signs; here $\omega(N)$ counts distinct prime factors. This distinguishes the universal construction of a square relation from constructing one that splits the input. Neither the coefficient sizes nor the marked norms in this construction satisfy a general smoothness guarantee.

## Replacing uniform parameters by rational functions of random residues

The inverse-linear success bound extends to proposals obtained from polynomial or rational formulas. Fix $N=pq$ for distinct odd primes. Draw any number of independent uniform residues $T_1,\ldots,T_k$ modulo $N$. The formulas and their integer coefficients may depend on $N$. After composing the two branch tests with the formulas and clearing denominators, let $G_-,G_+\in\mathbb Z[T_1,\ldots,T_k]$ have total degrees $d_-,d_+$. Ignore samples with nonunit denominators, or retain any proper gcd they expose as a separate success. Restrict square-relation success to unit evaluations where the two branches are disjoint.

If neither polynomial vanishes identically as a polynomial modulo either prime, the probability of a productive *square relation* is at most $2d_-d_+/N$. Indeed the root fraction of a nonzero degree-$d$ polynomial on a uniform field grid is at most $d/p$, by induction on the number of variables. For the assignment minus at $p$ and plus at $q$, CRT independence multiplies the bounds $d_-/p$ and $d_+/q$. The reverse assignment gives the other term. In particular even $N^{o(1)}$ adaptive attempts of degrees $N^{o(1)}$ with fresh uniform seeds have total success probability at most $N^{-1+o(1)}$, as long as the hypotheses hold conditional on each past history.

The exceptional polynomial cases are informative. If every coefficient of one branch vanishes modulo just one prime, the gcd of $N$ with those coefficients gives a factor when the coefficients are explicitly available. If every coefficient vanishes modulo $N$, that branch holds globally on every valid sample, precluding mixed signs. This argument concerns degree and seed distribution. A short modular circuit can have very large degree, and biased seeds or samples constrained to an algebraic curve need a separate analysis.
