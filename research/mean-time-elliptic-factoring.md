# Complete deterministic factoring in subexponential mean time

There is a deterministic algorithm which, given an integer $N\ge2$ alone, returns its **complete factorization** on every input. Averaging its actual bit cost over all positive integers of each bit length $b$ gives
$$
               \exp\!\big(O(\sqrt{b\log(2b)})\big).
$$
The same bound holds for the arithmetic mean over distinct balanced prime pairs $X<p,q\le2X$, with $b\asymp\log X$. The proof uses ordinary RH for an exceptional-prime estimate and Dirichlet GRH for the pointwise choice of rational marks. These are precisely the hypotheses covered by Alpöge's November 20 theorem and Sutherland's independent Lean checks. The deduction here is a paper proof. Local computations check its sampling, elliptic arithmetic, and finite complete-factorization examples. The benchmark concerns the maximum over all inputs, for which the earlier bound still applies. [Exact analytic statements independently checked by Sutherland](https://math.mit.edu/~drew/grh/) · [Alpöge's announcement](https://alpo.ge/remark.pdf) · [Worst-case benchmark](https://bigospeedrun.com/integer-factoring)

Lenstra's method samples curves and Lenstra–Pomerance's rigorous per-input expected bound samples class-group relations. The mean here averages a deterministic computation, including its slow cases, over the input distribution. We use the marked Legendre curves of the [density-one algorithm](legendre-average-factoring.md), a sharper count of exceptional primes, and explicit small-bias sets on a binary cube. The earlier deterministic mean-time result [with a supplied divisor sum](average-single-divisor-sum.md) uses additional input. [Lenstra, §2](https://pages.cs.wisc.edu/~cs812-1/Lenstra1987.pdf) · [Lenstra–Pomerance, Theorem and §7](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/rigorous.pdf)

## Almost every prime, with a square-root exceptional count

For $P$ a large power of two set $L=\log P$, $B(L)=\sqrt{L\log L}$, $Y=\exp(C B(L))$ and $V=\exp(1000L\log L/\log Y)$ with a sufficiently large absolute $C$. Call $p\in(P,2P]$ good if its central Hasse interval $|n-(p+1)|\le\sqrt p$ contains $\sqrt P/V$ distinct integers $n=4m$ with $m$ odd and $Y$-smooth. On ordinary RH, **the number of bad primes is at most**
$$
                         P^{1/2}\exp(O(B(L))).
$$

Use the measures and smooth weights from the [many-prime convolution](many-prime-hasse-intervals.md). In that construction replace the input scale by $P$, set $J=\lfloor L/(2\log Y)\rfloor$ and keep $T=P/4$, $z_0=Y/2$, $Z=3T/(Yz_0^{J-1})$. Thus $Z\gg\sqrt P$ and $\log Z=(1/2+o(1))L$. The same binomial construction supplies distinct cofactors in $[Z,1.11Z]$ of reciprocal mass at least $V^{-1/50}$. Let $P_1(t)=\sum_r(\log r) W(r/Y)r^{-1-it}$ and $P_0(t)=\int W(r/Y)r^{-it}\,dr/r$. With $D(t)=\sum_{m\in\mathcal M}m^{-1-it}$ the transforms of the discrete measure $\mu$ and its continuous-prime counterpart $\nu$ are $D(t)P_1(t)^J$ and $D(t)P_0(t)^J$. Each prime slot in $\nu$ uses $W(r/Y)dr/r$. The cofactor remains discrete. Both measures have total mass $\le O(1)^{J+1}$.

For $h=1/(100\sqrt P)$, the positive convolution $(\nu*K_h)(\log x)$ is uniformly at least $V^{-1/10}$ on $T\le x\le2T$. Restrict $J-1$ slots to $[z_0,z_0(1+1/(10J))]$, of mass $\gg1/J$ each. In the remaining slot, the center $x/(m\prod_{i<J}r_i)$ is in the interior of $[Y/4,7Y/10]$ and a relative $h/4$ interval has continuous mass $\gg h$. Multiplication by the positive kernel on that interval gives the bound since $J\log J\le L\log L/(2\log Y)$. This lower bound works at the short scale $h$ itself.

Put $T_0=V^4$. Uniformly for $|t|\le P^2$, the smoothed explicit formula on RH gives
$$
                 |P_1(t)-P_0(t)|\ll Y^{-1/2}L^3.
$$
The zero sum is $O(Y^{-1/2}\log(2+|t|))$ by the unit-height zero count and rapid decay of the transform of $W$. Higher prime powers cost $O(Y^{-1/2}\log^2Y)$, and the trivial-zero terms are smaller. For $|t|\le T_0$ compare the two products directly. Their inverse Fourier integrals after applying the short kernel differ by at most
$$
       O(T_0 J C_1^J Y^{-1/2}L^3)=o(V^{-1/10})
$$
for an absolute $C_1$, on increasing $C$. This is a uniform error at every center. On $T_0\le|t|\le P^2$, choose a sufficiently large fixed number of integrations by parts in $P_0(t)$ to give $|P_0(t)|\le O(Y^{-1/2})$. This is possible because $\log T_0/\log Y=4000/C^2$. Both transforms then satisfy
$$
              |P_i(t)|^{2J}\le Y^{-J}L^{O(J)}
              \le P^{-1/2}\exp(O(B(L))).
$$
Here the integer rounding of $J$ costs at most one factor of $Y$.

The Dirichlet-polynomial mean value theorem on dyadic frequency intervals, together with the smooth decay of $\widehat K(ht)$, gives
$$
 \int_{\mathbb R}|D(t)\widehat K(ht)|^2\,dt
 \ll (Z+1/h)\sum_{m\in\mathcal M}m^{-2}\ll 1.
$$
For example integrate first through $1/h$ and then over successive doubled intervals, bounding the kernel by a fixed inverse fourth power. Beyond $P^2$ the trivial total-mass bounds and the same smooth-transform decay contribute $O(P^{-2})$ to the squared integral. By Plancherel the high-frequency error therefore has squared integral $\ll P^{-1/2}\exp(O(B(L)))$. Outside a set of logarithmic measure of this size times $O(V^{1/5})$, the discrete short convolution is $\gg V^{-1/10}$. At $s\asymp P$ its atom is at most $P^{-1}(C_2 L)^J$ because each ordered prime choice divides $s$ and determines its cofactor. As $J\log(C_2L)\le (1/100)\log V$ eventually, a good center supplies at least $\sqrt P/V$ orders. The disjoint real intervals $|x-(p+1)/4|\le1/16$ each have logarithmic measure $\gg 1/P$ and every good center in one gives the required central Hasse estimate. There is also an interval cover. For an interior bad prime $p$, all centers with $|4x-(p+1)|\le\sqrt P/4$ must be exceptional: the entire positive-kernel window then stays inside its central Hasse interval. A maximal disjoint selection of these center intervals contains at most $\exp(O(B(L)))$ members since each has logarithmic measure $\gg P^{-1/2}$. Bounded enlargements cover all bad primes, and two more intervals cover the boundary strips. Thus $\exp(O(B(L)))$ intervals of length $O(\sqrt P)$ suffice. Computing their locations from $P$ is a separate problem.

With a fixed strip $\Re\rho\le1-\delta$ for $0<\delta\le1/2$ the same calculation gives $P^{1-\delta}\exp(O_\delta(B(L)))$ exceptional primes. The exponent $1/2$ is used in the cost accounting below. [Classical explicit formula](https://people.maths.ox.ac.uk/greenbj/papers/primenumbers.pdf) · [Montgomery–Vaughan's mean value estimate](https://doi.org/10.1112/jlms/s2-8.1.73)

## A deterministic search with a summable cost per stage

For a cofactor $d$, write $b=\mathrm{bits}(d)$. Test primality and perfect powers in polynomial time. An exact power gives a smaller root with its known multiplicity. Search through $\exp(C_3\sqrt{b\log(2b)})$ for small factors first, with a fixed large constant specified by the mark-height bound below. In parallel with the remaining search, double a Pollard–Strassen cutoff. If the least prime is $p$, that search takes $O(\sqrt p\,\mathrm{poly}(b))$ bit operations to find a proper factor. Inspect a nonunit block directly, including when its product vanishes modulo all of $d$. [Small-factor extraction from factorial blocks](average-single-divisor-sum.md) · [Costa–Harvey](https://arxiv.org/pdf/1201.2116)

Take the odd smoothness scalar and rational marked curves of the [Legendre construction](legendre-average-factoring.md). Set its smooth cutoff using $Y$ at $L=\log d$ and use the [polynomial-size rational conic menu](pointwise-conic-marks.md). It contains two choices $c_+,c_-$ supplying both twist signs for **each** ordered pair of distinct prime factors $p,q$. For each $c$ enumerate the first $H=\lceil V(\log d)^6\rceil$ distinct marks of its conic using the indicated degree-four parametrization. Their numerators, denominators and nonzero cross-differences have magnitudes polynomial in $b,H$. The initial cutoff can be chosen to exceed all of them. The total cost to test all $c$ and marks at one parameter, including gcd-checked scalar multiplication, is $\exp(O(\sqrt{b\log(2b)}))$. Every actual split is checked by division.

For a good prime $p\in(P,2P]$ remaining after the small-factor stage there are at least $p/V(\log P)^4$ successful parameter residues for each applicable pair $c_+,c_-$. Use the fixed prefix of $\lceil V(\log P)^6\rceil$ marks per conic in this estimate. Lenstra's central trace lower bound, the full rational two-torsion mass and the elementary second moment of the Legendre characters give this count. At a successful parameter a tested point has odd smooth order at $p$ and even order at $q$, or a bad reduction at $q$ gives a factor. This argument only uses the two specified prime divisors, so repeated prime powers and further factors in $d$ are allowed. The possible signs at other prime factors have no effect on correctness. [Curve and point details](legendre-average-factoring.md#obtaining-sufficiently-many-parameters-at-one-prime)

To generate the parameter residues, try $1\le k\le b$ and $0\le j\le b$ with seed $z=\lfloor d/2^j\rfloor\bmod 2^k$. Interpret $k$-bit words as integers. At stage $a=1,2,\ldots,b$, put $Q=2^a$. Over $\mathbb F_Q$, choose a fixed nonzero binary linear functional $\ell$ and use all $Q^2$ shifts
$$
    s(u,v)_i=\ell(vu^i),\qquad u,v\in\mathbb F_Q,\quad 0\le i< k .
$$
Try $\lambda=z\mathbin{\mathrm{XOR}}s(u,v)$ for each. A representation of the field can be built in $O(Q\,\mathrm{poly}(a))$ time by enumerating monic polynomials and applying the deterministic irreducibility test. Thus a whole stage costs $4^a\exp(O(\sqrt{b\log(2b)}))$. The shift distribution has bias at most $(k-1)/Q$ at every nonzero binary character. Averaging over $v$ kills that character unless its nonzero polynomial in $u$ vanishes. For a target set of cube density $\gamma$, the proportion of initial words missing the whole set of shifts is consequently at most
$$
                      \frac{k^2}{4^a\gamma}.
$$
Indeed on each missed word the convolution of the indicator with the shift distribution vanishes, whereas its squared distance from the constant $\gamma$ has mean at most $k^2\gamma/4^a$ by Parseval. At $a=b$ the shifts cover every $k$-bit word: choose $u$ of degree $b$ and vary $v$, using independence of $1,u,\ldots,u^{k-1}$ and nondegeneracy of $(v,w)\mapsto\ell(vw)$. The fallback can continue independently. [Alon, Goldreich, Håstad and Peralta's small-bias constructions](https://johanhastad.se/almostindep.pdf)

## Charging the entire running time

Consider the one-split work on a dyad $X<d\le2X$ and put $b_*=\lceil\log_2(2X+1)\rceil$, $T_*=\exp(O(\sqrt{b_*\log(2b_*)}))$. Small-factor preprocessing is within $T_*$. If the least prime $p$ is bad, charging the factorial search to multiples of $p$ yields normalized cost at most
$$
  O(\mathrm{poly}(b_*))\sum_{\substack{p\le\sqrt{2X}\\p\text{ bad}}}p^{-1/2}\le T_*.
$$
On each prime dyad the exceptional count cancels $P^{-1/2}$ up to $\exp(O(\sqrt{\log P\log\log P}))$. There are $O(b_*)$ dyads. This step counts the entire slow path even when the elliptic search would also succeed.

If the least prime $p$ is good and $d$ is neither prime nor a prime power, write $d=pqA$ with a distinct prime $q\ge p$. Use $p\in(P,2P]$, $q\in(U,2U]$ for powers of two $U\ge P$. Choose $2^k=2P$ and $j=\lfloor\log_2(pA)\rfloor$. The cube contains every residue at $p$ and has size less than twice $p$, so the parameter target for a given applicable pair of conics has density $\gamma\ge 1/(2V(\log P)^4)$. The integer map $q\mapsto\lfloor (pA/2^j)q\rfloor$ is injective and its range on the dyad has length at most $2U+1$. Each reduced cube word occurs $O(U/P)$ times. The witnessing conics may depend on $q$. For fixed $p$ use the union of missed starting words over all pairs of rational conics from the public height bound at $b_*$ that have the required two respective signs at $p$ and are nondegenerate at $p$. There are polynomially many such pairs. Equivalently take only pairs that are admissible for at least one cofactor in this dyad after preprocessing. On the chosen prefix of marks each target depends on $p$ and the two conics alone.

Consequently for fixed $p,A,U$, the number of prime partners reaching stage $a+1$ is at most
$$
                 O\!\left(U\min\{1,\mathrm{poly}(b_*)V(\log P)^4/4^a\}\right).
$$
This is an upper bound obtained by counting all integer partners in the missed residue set. It includes any correlation between the factors and their conic signs. Multiplying by the next stage's cost, then summing over $a\le b_*$, bounds the total cost on those partners by $U T_*$. The stage cost grows by four and the bound on the missed proportion decreases by four. For fixed $p,U$, there are at most $2X/(pU)$ positive choices of $A$. Sum over $p$ and the $O(b_*)$ partner dyads. The total is at most $X T_*$, as $\sum_{p\le2X}1/p\le1+\log(2X)$. Overcounting decompositions of a cofactor only raises this bound. Prime powers and primes cost polynomial time to recognize. This proves the one-split mean bound over ordinary integers. Restricting the same dyadic argument to balanced semiprimes costs at most a further polynomial in $\log X$ upon normalizing by their number.

Recursively split and verify cofactors, retaining the multiplicities of exact powers. For any input $N$, every visited cofactor divides $N$ and there are at most $2\log_2(2N)$ visits. Let $t(d)$ bound the cost of one visit. The mean over $X<N\le2X$ is at most $O(\log(2X))\sum_{d\le2X}t(d)/d$, because at most $3X/d$ integers in the dyad are multiples of $d$. The one-split estimate on each dyad bounds this sum by $T_*$ after polynomial factors. This includes inputs with many factors, repeated factors and failed elliptic searches. The algorithm can be interleaved with the existing unrestricted deterministic algorithm to retain its worst-case guarantee.

## Independent finite replay

Lean 4 checks the exact finite missed-start inequality from the integer character bias bounds. The file proves Walsh–Parseval, the convolution identity for an arbitrary list of shifts, and the variance estimate without invoking an external Fourier library. For $A$ target words in a cube of size $D$, list length $m$ and unnormalized nontrivial character sums bounded by $B$, its theorem is $\#\mathrm{miss}\, A m^2\le D(D-A)B^2$. The polynomial-root bound for the field sampler and the analytic exceptional-prime theorem are on paper. [Lean proof](../formal/CubeSampler.lean)

The checker reconstructs all 2,467 nontrivial character biases in its sampled binary fields by direct polynomial root counts. It checks 174 exact target-set inequalities, including full coverage at matching word and extension degrees. A singleton example with 256 integer partners has 3, 2, 13, 45 and 126 newly reached partners over its first five stages. The remaining 67 stay in the cost accounting. A separate integer-only marked-curve run completely factors all 300 toy inputs, with 306 elliptic or gcd splits and verification of the prime product. These runs use reduced parameters. They do not measure the asymptotic mean. [Binary-field sampler, prime-slot and factoring replay](../experiments/mean-time-ecm.py)

The convolution check compares 2,016 ordered tuples with 616 distinct product atoms, bounds every atom's multiplicity and counts the exact orders in 528 prime-centered windows, 89 occupied. The wider Legendre tests independently check 64,728 nonsingular models, 17,756 rational marked points and the resulting group orders. [Local finite-field checks](../experiments/moving-legendre.gp) · [Whole-cofactor checks](../experiments/moving-legendre.py)
