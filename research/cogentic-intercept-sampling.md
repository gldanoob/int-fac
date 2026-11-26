# A smaller cyclic sampler and a support bound for dropping the intercept

For the [cyclic one-intercept search](cogentic-one-intercept.md), the inverse-prime construction has an explicit bias-$\epsilon$ sampler with at most $\epsilon^{-2}\operatorname{poly}(\log(2M/\epsilon))$ points on the cyclic group of order $M$. The earlier estimate for the same construction used $\epsilon^{-6}\operatorname{poly}(\log(2M/\epsilon))$. This reduces the product of the three auxiliary list-size bounds from $\epsilon^{-18}$ to $\epsilon^{-6}$, up to polynomial factors in $\log(2M/\epsilon)$.

If the Fourier transfer must work for arbitrary pairs of unary evaluation functions, a distribution must have support of order at least $\min(M/\epsilon^2,M^2)$ for one field. An arithmetic sampler that handles just the smoothness and row-presence tests could use smaller support.

## Summing the individual inverse-prime errors

Let $M\ge 2$ be a power of two. Choose a prime $r\in(T,2T]$ uniformly, then choose $j\in\{0,\ldots,r-1\}$ uniformly and output $jr^{-1}\bmod M$. Here $T\ge2$ is an integer. Uniformity over the prime and then the numerator assigns weight $1/(rP(T))$ to a listed pair, where $P(T)$ counts primes in $(T,2T]$.

Fix a nonzero frequency $k\in\{1,\ldots,M-1\}$. Write $r r^{-1}=1+hM$ using the representative $r^{-1}\in[0,M)$. Let $s\in[-(r-1)/2,(r-1)/2]$ be congruent to $kh\pmod r$. The conditional Fourier coefficient at frequency $k$ is a geometric average with angle $(s+k/M)/r$. Its absolute value is bounded by
\[
 w_s=\frac{2}{1+|s|}.
\]
For $|s|\le1$ use the trivial bound one. For $|s|\ge2$, the distance of $s+k/M$ to $r\mathbb Z$ is at least $|s|-1$. The geometric-sum formula and $|\sin(\pi t)|\ge2\operatorname{dist}(t,\mathbb Z)$ bound the coefficient by $1/(2(|s|-1))\le w_s$.

For a **fixed** $s$, the primes that obtain it all divide $k+sM$, since $hM\equiv-1\pmod r$. This integer is nonzero and has absolute value less than $TM$, as $|s|\le T-1$. Its distinct prime divisors greater than $T$ number at most $\log(TM)/\log T$. The bias at every nonzero frequency is therefore at most
\[
 \frac{\log(TM)}{P(T)\log T}
 \left(2+4\sum_{d=1}^{T-1}\frac1{1+d}\right)
 \le \frac{\log(TM)(2+4\log T)}{P(T)\log T}.
\]
The saving comes from charging each possible residue separately with its geometric decay. By the prime number theorem $P(T)\gg T/\log T$, so this bias is $O(\log(TM)\log(2T)/T)$. Taking
\[
 T=O\big(\epsilon^{-1}(1+\log M+\log(1/\epsilon))^2\big)
\]
with a large enough constant suffices for $0<\epsilon\le1/4$. An integer-only algorithm doubles $T=2^j$ from 2, sieves the primes, and stops once
\[
 (2+4j)\operatorname{bitlength}(TM)\le\epsilon j P(T).
\]
This rational comparison certifies the same upper bound and stops within the displayed order. A sieve, modular inversions, and enumeration of the numerators take $O(T^2\operatorname{poly}(\log(2TM)))$ bit operations. Repeated output points can be retained. The list weights are used in the comparison proof, and the coefficient search only needs the listed points.

Use this support for each of the independent shift and slope draws in the earlier construction. The remaining full intercept keeps the Fourier pairing, so all comparisons there use the same precision. For an unweighted one-field pair of evaluations the upper support bound is $O(M\epsilon^{-2}\operatorname{poly}(\log(2M/\epsilon)))$. For the weighted two-field factoring sweep the auxiliary triple has size $O(\epsilon^{-6}\operatorname{poly}(\log(2M/\epsilon)))$, before the extractor and the remaining loops polynomial in $A,B$. With $\log M=\Theta(V)$ and $\epsilon=\exp(-CH)$, the exponent of the auxiliary-list work bound falls from $18CH+O(\log V)$ to $6CH+O(\log V)$ in this enumeration. The sweep still has the full $M$ term.

## Why the universal two-evaluation comparison needs a large support

Consider two marks $a,b$ of opposite parity. The map $(x,y)\mapsto(x+ay,x+by)$ is a bijection on $(\mathbb Z/M\mathbb Z)^2$. For uniform independent coefficients the output pair is uniform on $M^2$ pairs. A weighted sampler for the two coefficients induces a probability matrix $P=(p_{ij})$ on these pairs. Set $D_{ij}=p_{ij}-M^{-2}$ and
\[
 \Delta=\max_{A,B\subseteq\mathbb Z/M\mathbb Z}
            \left|\sum_{i\in A,j\in B}D_{ij}\right|.
\]
The comparison for arbitrary indicator functions $F(x+ay)G(x+by)$ requires $\Delta\le\epsilon$. Let $S$ be the number of positive entries of $P$.

Suppose $\Delta\le1/4$. If $g$ rows have mass at least $1/(2M)$, testing all other rows against the full column set shows that $(M-g)/(2M)\le\Delta$, hence $g\ge M/2$. For such a row $i$, with $d_i$ positive entries and total mass $r_i$, Cauchy–Schwarz and the triangle inequality give
\[
 \|D_{i,*}\|_2\ge r_i/\sqrt{d_i}-M^{-3/2}
                 \ge (2M\sqrt{d_i})^{-1}-M^{-3/2}.
\]
By convexity of $t^{-1/2}$ and $\sum_i d_i=S$, these rows contribute at least $g^{3/2}/(2M\sqrt S)-gM^{-3/2}$. Therefore $\sum_i\|D_{i,*}\|_2\ge (4\sqrt2)^{-1}\sqrt{M/S}-M^{-1/2}$.

For independent uniform column signs $\xi_j$, put $Z_i=\sum_j D_{ij}\xi_j$. The second and fourth moments are $\mathbb E Z_i^2=\|D_{i,*}\|_2^2$ and $\mathbb E Z_i^4\le3\|D_{i,*}\|_2^4$. Hölder's inequality gives $\mathbb E|Z_i|\ge\|D_{i,*}\|_2/\sqrt3$. Some column sign vector therefore satisfies $\sum_i |Z_i|\ge\sum_i\|D_{i,*}\|_2/\sqrt3$. Choosing each row sign to match $Z_i$ expresses this absolute sum as a signed sum of four rectangles, at most $4\Delta$. Combining the inequalities yields
\[
 S\ \ge\ \frac{M}{32\big(4\sqrt3\,\Delta+M^{-1/2}\big)^2}.
\]
This argument allows arbitrary positive weights. It also applies to a sampler for two fields by making the other field's factors constant and projecting the support. With $\epsilon=\exp(-CH)$ and $\log M=\Theta(V)$, the required support is $\Omega(M/\epsilon^2)$. Thus fooling the larger unary-function class cannot certify a list of $\exp(O(H))$ tuples. The arithmetic smoothness indicators need a separate argument.

An [integer replay](../experiments/cogentic-intercept-sampling.py) checks the residue counts and domination by the rational harmonic budget. It also obtains exact maximum rectangle discrepancies in small affine evaluation matrices and checks a rational relaxation of the support bound. The asymptotic statements follow from the estimates above.

## One low-intercept word for all generator primes

Assume the scalar counting and score hypotheses of the [high-bit selection](cogentic-scalar-divisor-count.md#fixing-the-high-bits-before-the-intercept-search). Use a common bound $h_*$ on the original marked heights over all generator primes and both fields. The same $R$ then works for every target, although the selected box origins can differ. On the displayed schedule,
\[
                  \log R\le(50000.5+o(1))V.
\]
The shorter boxes give one complete randomized factoring trial with at most $\log_2 R$ common fair bits and cost $\exp(O(H))$. A certified bound on the failed fraction also lets the deterministic search stop after a prefix of $o(R)$ intercepts. The leading two-thirds exponent bound from the box width is unchanged.

In the high-bit bisections, require score mean error at most $L^{-3}$ per estimate. The $O(V)$ bisections now accumulate $O(VL^{-3})=o(1)$ true mean increase. Taking larger fixed constants in the scalar precision and the power of $B$ in $R$ gives the stronger tolerance at the same $\exp(O(H))$ cost. The score mean in each selected box is therefore $o(1)$ uniformly in the generator prime. The score approximation at the initial box also provides a computable upper bound $u_\ell$ for the selected box mean, by adding the certified initial error and twice the error per bisection. In particular $u_\ell=o(1)$ uniformly.

Let $M$ be the common power of two in $[4(A+1)R,8(A+1)R]$ from the box construction and put $w(x)=(M/R)1_{[0,R)}(x)$, using ordinary representatives. For target $\ell$, the torus variables are deviations from its own box origins. Draw a uniform $x$ on the torus and use $x+s$ as the other intercept, with the three auxiliary draws $s,y_1,y_2$ independent on the short list. Put $W=w(x)w(x+s)w(y_1)w(y_2)$. Define $P_\ell$ to equal the target score on the box and zero wherever $W=0$. The Fourier comparison gives
\[
         \mathbb E[WP_\ell] \le u_\ell+L^{-3}.
\]
Increasing the fixed bias constant absorbs both the absolute coefficient sum of the score and all the box Fourier norms. For each $x\in[0,R)$, independence gives
\[
 \mathbb E[W\mid x]=\frac MR\,\mathbb E_s w(x+s)
                               \big(\mathbb E_y w(y)\big)^2
                   \ \ge\ \frac{M}{8R}.
\]
Each of the three expected weights is at least $1/2$, by the bias bound and the $A$-norm of $w$.

For a fixed target, call $x$ failed if enumerating the short triples yields no checked order for that target. Every in-box supported tuple above a failed $x$ has $P_\ell\ge1$, by the score implication. Consequently the failed fraction among the $R$ intercepts is at most $8(u_\ell+L^{-3})$. Average this bound over the generator primes in $(B/2,B]$, and denote the resulting computable bound by $\rho=o(1)$. A common uniformly random $x\in[0,R)$ has expected failed fraction of bases at most $\rho$, even if the box origins differ. Markov's inequality gives probability at most $4\rho$ of failing more than a quarter of the bases.

A set of successful bases of density at least three quarters suffices for complete factoring. For each pair of distinct prime factors of the preprocessed modulus, the quadratic-character sign argument supplies a fraction $1/2-o(1)$ of all bases with distinct two-adic local orders for that pair, uniformly over pairs. Thus the successful bases intersect every pair's distinguishing set. This deterministic intersection argument applies to all pairs at once. Each checked order gives the prime-power gcd partitions in the [complete one-intercept trial](cogentic-one-intercept.md#extracting-all-primes-with-one-intercept). Refining these partitions identifies every prime power of the same modulus, including multiplicities. Primality and multiplication checks confirm completion. The trial on the preprocessed modulus already separates every pair. Bounded inputs use the original finite fallback.

On the displayed schedule, the Gaussian mean of the score is $O(1/d)$ uniformly in the target. Item 2 of the [centered moment estimates](cogentic-deterministic-two-thirds.md#centering-the-discarded-rows-and-the-rank-certificate) gives $\mathbb E C-1=O(e^{-50z^2})$ and $\operatorname{Var}(C)=O(\sum_{p>d}p^{-2}+e^{-7z^2})$, where $C=\widehat C$ and $z=\log L$. Thus the expectation of $64(C-1)^2$ is $O(1/d)$ by the variance-plus-squared-bias identity and $\sum_{p>d}p^{-2}\le\sum_{n>d}n^{-2}\le 1/d$. For the remaining terms, the [score formula and moment bounds](cogentic-conditional-score.md#a-computable-nonnegative-score) give at most $L^{O(1)}(B^{-0.05}e^{0.07T_0}+e^{-0.002T_0})=o(1/d)$ after the displayed score normalizations, since $T_0=(7/0.15)z^2$, $\log B\asymp H$ and $d=O(L^{1/3})$. The uniform original box has point masses bounded by an absolute constant times those of the Gaussian. The certified bound $u_\ell$ exceeds its initial box mean by at most $O(VL^{-3})=o(1/d)$. The additional torus expectation error is $L^{-3}=o(1/d)$, so the resulting computable bound is $\rho=O(1/d)$.

For any prefix of $S$ intercepts, its expected failed fraction under a uniform draw is at most $\rho R/S$. For success probability $1-o(1)$ take the least power of two $S\le R$ with $S^2\ge\rho R^2$, capped at $R$ and with minimum one. Then the failed fraction has expectation at most $\sqrt\rho$ when $\rho\le1$, and $S/R\le 2\sqrt\rho+1/R=o(1)$. For constant success probability, instead take the least power of two at least $8\rho R$, capped at $R$ and with minimum one. This gives at least one-half success probability for sufficiently large inputs. Enumeration then completes factoring in $(1+\rho R)\exp(O(H))$ bit operations. On the displayed schedule the constant-probability prefix uses $O(1+R/d)$ intercepts. The available bound on $\rho$ leaves the $\exp((50000.5+o(1))V)$ deterministic upper bound.

The average miss bound alone cannot guarantee that a deterministic list of at most $\lfloor\rho R\rfloor$ intercepts hits any successful target. Abstract failure sets can put every listed intercept in the failure set of every target while keeping the average miss fraction at most $\rho$. For an adaptive list, take the intercepts on its all-failure transcript and use that same failure set. A shorter guarantee needs information about the arithmetic distribution of the failures.

The [integer replay](../experiments/cogentic-intercept-sampling.py) checks the weighted intercept marginal and both prefix estimates for 64 targets with differing box origins. It uses toy scores with exactly known failure sets.

## An arithmetic obstruction for a few affine lines

Replacing the full intercept by one affine function of its field's slope, or by a short list of such functions, can erase an entire squarefree band-smoothness test. The obstruction below uses synthetic values of the affine constant $C$. The step has the Cogentic form and the test has its height and bit bounds. The statement concerns the arithmetic test family and ordinary integer lines in coefficient coordinates. It gives no assertion about the allowable constants in a single fixed Cogentic instance or the value of that instance's full score.

Suppose $\log A\asymp\log B\asymp H$, $A$ is a power of two, $\log m=\Theta(V)$, $P_0=\prod_{p\le d}p$ with $d=O(H)$, and $\ell\in(B/2,B]$ is prime. Let $\mathscr L$ be $k$ integer lines $x=u_i+v_i y$ with $O(V)$-bit coefficients and $v_i\ne-m$, where
\[
                         1\le k\le\frac{\log A}{3\log V}.
\]
Fix any power of two $X$ with $\log X=\Theta(V)$. For all sufficiently large inputs there are an integer $1\le a\le A$, a nonnegative $O(V)$-bit constant $C$, and a positive step $D=P_0\ell(m-a)$ such that the test
\[
                  1_{\{C+D(x+ay)\text{ is a squarefree product of primes in }(\sqrt B,B]\}}
\]
has uniform mean at least $\exp(-cH)$ on $[0,X)\times[0,X/A)$ for a fixed $c>0$, and vanishes at every point of $\mathscr L$ in this box. The line list may depend on the prescribed box. The choice of sign of $D$ fixes a representative for the absolute norm test.

**Congruences on the lines.** Choose distinct primes $p_i\in(V^2,2V^2]$, avoiding the prime divisors of $m+v_i$. There are $\gg V^2/\log V$ primes to choose from by the prime number theorem, while a nonzero $O(V)$-bit integer forbids $O(V/\log V)$ primes in this range. These primes exceed $d$, lie below $\sqrt B$ and differ from $\ell$. Their product $Q$ satisfies $\log Q\le3k\log V\le\log A$. Pick $a$ by $a\equiv-v_i\pmod{p_i}$ in $[1,Q]$. The same choice works inside any prescribed interval of at least $Q$ consecutive possible marks. Then $p_i\nmid D$ because $m-a\equiv m+v_i\not\equiv0\pmod{p_i}$. Impose $C\equiv-Du_i\pmod{p_i}$. On line $i$ the norm is divisible by $p_i$, a forbidden prime, for every integer $y$.

**Positive mass on the prescribed box.** Let $t$ be the largest integer with $4B^t\le DX$. Products of $t$ distinct primes from $(B/2,B]$ coprime to $D$ are at least $(B/2)^t$ and at most $B^t$. Their dyadic size intervals number at most $t+2$. Write $J$ for the number of these eligible primes. The coprimality condition deletes at most $O(V/\log B)$ primes. By uniqueness of the products, some interval $[Z,2Z)$ with $Z$ a power of two and some unit residue $r$ modulo $D$ contain at least $\binom Jt/((t+2)D)$ products. Because $DX<4B^{t+1}$ and $Z\ge (B/2)^t/2$, one has $Z>DX/(8B2^t)$. Take $C$ in $[0,DQ)$ satisfying $C\equiv r\pmod D$ and the prescribed congruences modulo all $p_i$. This is possible because $\gcd(D,Q)=1$, and $C<Z/4$ for large inputs since $X=\exp(\Theta(V))$ and $BQ2^t=\exp(O(H))$. For every selected product $n$ and every integer $0\le y\le Z/(4AD)$, the integer $x=(n-C)/D-ay$ lies in $[0,X)$ and gives that product. Indeed $x\ge Z/(2D)$ and $x\le B^t/D\le X/4$. These slopes constitute at least $Z/(4DX)>1/(32B2^t)$ of all slopes in the box. The uniform mean is at least
\[
       \frac{\binom Jt}{32X(t+2)DB2^t}
       \ \ge\ \frac{\binom Jt}{128(t+2)B^{t+2}2^t}
       \ \ge\ e^{-cH}.
\]
The last bound follows from $J\gg B/\log B$, $\binom Jt\ge(J/t)^t$, $t=O(V/H)$ and $(V/H)\log L=H$. A further $O(V/\log B)$ band-prime omissions leave the same bound. All the marked norms in the prescribed box have $O(V)$ bits since $C<DQ$, $a\le A$ and $\log(DX)=O(V)$.

For a prescribed mark $a$, a larger obstruction applies to a list of fibers $x+ay=u_i$. Any list of $k\le\log X/(6\log V)$ such fibers can be made entirely nonsmooth by the same construction. Choose $p_i$ avoiding $m-a$ and impose the congruences on $C$ with $a$ already fixed. The line step no longer requires $Q\le A$. Instead $Q\le\sqrt X$ follows from the bound on $k$, so $C<DQ\le D\sqrt X<Z/4$ for sufficiently large inputs. The counting argument gives the same lower bound on the full-box test mean. This applies to selectors that choose a short, test-independent list of values of $x+ay$ and keep any number of slopes at those values.

This rules out a comparison with error $\exp(-C_1H)$ for sufficiently large $C_1$ if it must work uniformly for these box-and-test instances and all support confined to the proposed lines. The list can contain arbitrarily many points per line. The result applies to line lists fixed before this constructed instance. It does not preclude a rule that chooses its lines from the test, that wraps them modulo a torus and uses many resulting ordinary lines, or that handles the given score without preserving individual test means.

The [integer replay](../experiments/cogentic-intercept-sampling.py) checks both crossing lines and parallel fibers, enumerates all slope positions on the tested lines, and finds accepted points in the same prescribed boxes by multiplying actual band primes.
