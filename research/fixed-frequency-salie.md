# Reducing diagonal Salié queries to frequency one

For odd $n$ and a unit $t$ let $W_n(t)=\sum_{r^2=1\bmod n}e_n(2tr)$ be the real normalized Salié sum. Each sign $\operatorname{sgn}W_n(t)$ is computable from $O(\log n)$ **nonadaptive sign queries at frequency one** on odd moduli at most $n^3$, with deterministic polynomial additional work. The same reduction expresses $\log|W_n(t)|$ as an alternating sum of frequency-one log magnitudes and explicitly known terms. Thus an inverse-polylogarithmic approximation to a single real number per odd modulus, $\log|W_m(1)|$, is polynomial-time equivalent to complete integer factoring. These are reductions to an evaluator. The cost of computing the fixed-frequency sum directly on an unfactored modulus remains open.

### A descent with a known power of three

The two roots at each odd prime power $D$ give the local factor $2\cos(4\pi t/D)$, which is nonzero on the odd unit grid. For odd coprime $a,b$, CRT gives
$$
 W_{ab}(1)=W_a(b^{-1}\bmod a) W_b(a^{-1}\bmod b).
$$
The trace is even in its frequency. Set $W_1=1$. Ordinary twisted multiplicativity and the Salié root evaluation are classical. The fixed-frequency sign of an ordinary untwisted Kloosterman sum on squarefree moduli has also been studied as a distribution problem. [Salié formula and normalization](salie-and-quarter-parity.md) · [Jones, twisted multiplicativity of Salié sums](https://link.springer.com/article/10.1007/s40687-025-00544-4) · [Fouvry–Michel, ordinary Kloosterman sign changes](https://doi.org/10.4007/annals.2007.165.675)

Remove the power of three from $n$ first. If $n=3^h n_0$ with $3\nmid n_0$, the known $3^h$ factor is evaluated at $t n_0^{-1}$ and the residual frequency at $n_0$ is $t(3^h)^{-1}$. Stop at residual modulus one. At a remaining step write the current modulus as $n$, coprime to six. Let $m$ be the unique positive odd representative below $n$ of $\pm t^{-1}\bmod n$. If $m\le3n/4$, set $B=1$. Otherwise put $d=n-m$, $s=v_3(d)$, $B=3^{s+1}$, and replace $m$ by the positive odd representative of $\pm(Bt)^{-1}\bmod n$. Now
$$
                         m\le 3n/4.
$$
In fact $3m=jn\pm d/3^s$ for an integer $j$. Since $d/3^s$ is prime to three and is smaller than $n/4$, the only possibilities are $j=1,2$. Hence $m\le(2n+d/3^s)/3<3n/4$. Also $B\le3d<3n/4$. Move any further factor of three from $m$ into $B$, preserving $Bm$. The integers $n,B,m$ are now pairwise coprime.

One query at the odd modulus $v=nBm\le n^3$ gives the product identity
$$
 W_v(1)=W_n(t)\,W_B((nm)^{-1})\,W_m((nB)^{-1}).
$$
The $B$ factor is known because $B$ is a power of three. The last term is another instance with modulus at most $3n/4$. Recursion terminates in $O(\log n)$ steps. Every modulus and known phase is computed by integer arithmetic on the original input, so the queries may all be issued together. Taking signs gives a product of signs. Taking log magnitudes gives an alternating sum, with coefficients of absolute value one. At odd prime-power blocks the sign of the known cosine is computed by integer comparison with the two quarter boundaries.

### Consequences for the evaluator

* **Exact signs.** The original-modulus sign decoder for inputs with $R$ distinct odd primes now needs only frequency-one sign queries on varying odd moduli. Its work and query bounds remain $2^{O(R)}\operatorname{poly}(b)$ or $2^{O(\sqrt b)}$ for arbitrary $b$-bit inputs. In particular these fixed-frequency signs suffice in deterministic polynomial time for two-prime inputs, where the complete factors also yield every individual centered floor-sum parity bit. The auxiliary moduli in the descent may have more prime divisors than the input. [Original-modulus decoder](kloosterman-localization.md#sign-decoding-with-logarithmically-many-prime-factors) · [Transfer to Salié sums](salie-and-quarter-parity.md)
* **Log magnitudes.** Suppose the answer at $m$ approximates $\log|W_m(1)|$ to absolute error at most $2^{-20}/(1+\log_2 m)^2$. The descent reconstructs the variable-frequency log magnitude to absolute error less than $2^{-14}$. Each dyadic size range contains at most three current moduli since $(3/4)^3<1/2$, and each queried modulus is at least the corresponding current modulus. Summing the promised errors over these ranges is bounded by $3\cdot2^{-20}\sum_{j\ge0}(1+j)^{-2}$. Compute the known cosine logs to the same per-stage accuracy. The extra initial power of three contributes at most one additional term. All this fits inside the stated error. Comparing the reconstructed value with zero gives a valid answer to the fixed magnitude-gap problem, since the permitted band is $1\pm2^{-12}$ in magnitude. Combining with the earlier threshold reduction therefore gives complete deterministic polynomial-time factoring on arbitrary integers. Conversely, given the factors of $m$, multiply or sum the local cosine magnitudes in polynomial time. Each local magnitude is at least $2/D$ on a block of size $D$, so polynomial working precision suffices. The promised approximation has an encoding of $O(\log\log(3m))$ bits since $|\log|W_m(1)||\le\log m$. The sign of $W_m(1)$ is unnecessary for this magnitude reduction. [Variable-frequency gap reduction](kloosterman-threshold.md) · [Original twisted-modulus transfer](salie-and-quarter-parity.md#the-shifted-comparison-at-one-dyadic-center)

The replay tested all units at odd moduli through 259 and twenty further cases with deliberately large powers of three in $n-m$. All 13,722 transfers agreed in exact integer sign and to numerical tolerance in log magnitude. An independent enumeration of roots checked 195 of the frequency-one values directly. The longest list in this finite sample contained nine queries. [Replay](../experiments/salie-fixed-frequency.py)

### A single fixed-frequency bit with randomized prime generation

There is also an **unconditional Las Vegas polynomial-time reduction from complete factoring to one fixed bit per odd modulus**. The bit compares $|W_v(1)|$ with one, allowing either answer inside the fixed band $[1-2^{-14},1+2^{-14}]$. Randomness is used only to construct two known auxiliary prime-power blocks. Every accepted construction preserves the required gap, including on adversarial answers in the band. Given the factors, the local cosine product gives a valid bit in deterministic polynomial time. The deterministic descent above instead uses an inverse-polylogarithmic approximation and requires no prime search.

To transfer the earlier variable-frequency gap query at $(n,t)$, put $a=t^{-1}\bmod n$. Take $B=\ell^e$ with a new prime $\ell$ and $e\in\{1,2\}$, and a second new prime $r$, requiring $Br\equiv a\pmod n$. Then $v=nBr$ satisfies
$$
 |W_v(1)|=|W_n(t)|\;4|\cos(2\pi x)\cos(2\pi x_r)|,
 \qquad x=\frac{2(nr)^{-1}\bmod B}{B},\quad
 x_r=\frac{2(nB)^{-1}\bmod r}{r}.
$$
Writing $y=(2t\bmod n)/n$, CRT also gives $y+x+x_r\equiv2/v\pmod1$. Choose a real $x_0$ with $4|\cos(2\pi x_0)\cos(2\pi(y+x_0))|=1$. Such a choice exists for every $y$: for $C=\cos(2\pi y)$ choose $\cos(4\pi x_0+2\pi y)=\operatorname{sgn}(C)/2-C$, choosing either sign at zero. The target cosine belongs to $[-1/2,1/2]$. Approximate $x_0$ to error $1/B$ and choose an integer $u$ near $Bx_0$ coprime to $B$. Its circular phase error is at most $3/B$. Prescribe
$$
                r\equiv a B^{-1}\pmod n,\qquad r\equiv 2(nu)^{-1}\pmod B .
$$
This sets $x=u/B$. The two cosines have bounded derivatives and their product was calibrated to one. For all sufficiently large $\ell$ the absolute log of the auxiliary gain is below $2^{-16}$, uniformly in $y$. These constants can be enforced by an absolute lower cutoff on $\ell$. Computing the calibrated class takes polynomial time. If the original magnitude lies outside $1\pm2^{-12}$, the fixed-frequency magnitude lies outside $1\pm2^{-14}$ on the same side. This is sufficient for the complete-factoring threshold decoder. [Gap contract and decoding proof](kloosterman-threshold.md)

Here is how to find the two primes without assuming GRH. Fix a sufficiently large effective absolute constant $C_0$. On each attempt choose $e=1$ or 2 with equal probability. Choose a uniform reduced residue $b\bmod n$ and one uniform lift $\ell\in(n,n^{C_0}]$ of $b$. Test primality and restart on failure. For $Q=nB$ choose one uniform lift $r\in(Q,Q^{C_0}]$ in the calibrated reduced class modulo $Q$, again testing primality. Sampling a unit can be done by ordinary rejection; its expected cost is polynomial since $n/\varphi(n)=O(\log(2n))$. Bounded input sizes can be treated directly. All integers have $O(\log n)$ bits.

For the success bound take $Y=n^{1+2C_0}$, an upper bound on both progression moduli. Landau–Page gives at most one primitive real character of conductor at most $Y$ with a zero $\beta>1-c/\log Y$, for a sufficiently small effective absolute $c$. Outside this exceptional character, every reduced class used above has prime-sampling probability $\gg1/\log n$. To see this use Thorner–Zaman's uniform prime-count formula at $x=m^{C_0}$ for the progression modulus $m=n$ or $Q$. Choosing $C_0$ sufficiently large makes its relative error at most one half. A possible real-zero multiplier is $1-\chi(b)x^{\beta-1}/\beta$. For zeros below the Landau–Page cutoff this stays bounded below, since $m\ge n$ and $\log Y=O(\log n)$. Above the cutoff a class with $\chi(b)=-1$ also has this lower bound. Removing primes at most $m$ costs at most $m\log m$ in prime weight. Increasing the absolute minimum input handles the finitely many small values. [Thorner–Zaman, Corollary 1.4 and Remark 1.5](https://arxiv.org/pdf/2108.10878#page=3) · [Landau–Page, Lemma 7.1](https://arxiv.org/pdf/1412.5029#page=32) · [Deterministic primality test](https://doi.org/10.4007/annals.2004.160.781)

If the exceptional conductor divides $n$ and $\chi(a)=+1$, the choices $e=1$ and $\chi(b)=-1$ make both prime classes favorable. If $\chi(a)=-1$, use $e=2$ and $\chi(b)=-1$. Then $\chi(B)=+1$ and the last prime class is favorable as well. Each required choice has probability $1/4$ before the two primality tests. If the exceptional conductor does not divide $n$, one can exclude its $O(\log n)$ prime divisors from the successful first prime choices at negligible cost. The character can then occur in neither progression. The sampler need not identify any exceptional character. Thus the two tests succeed together with probability $\gg1/(\log n)^2$ per attempt. Every accepted pair has the desired CRT properties and the prime searches have expected polynomial cost.

The finite replay constructs prime and prime-square calibrations at 360 inputs, independently checks the full local product, and sees both threshold outcomes. The largest observed absolute log gain error was below $1.21\times10^{-7}$. The finite search uses sequential progression lifts for reproducibility; the runtime bound uses the randomized sampler above. [PARI/GP replay](../experiments/salie-fixed-gap.gp)

### What the fixed frequency measures on two and three prime blocks

For an odd $n\ge64$ with exactly two prime-power blocks, choose either mixed root $r^2\equiv1\pmod n$. Then
$$
 W_n(1)>1\quad\Longleftrightarrow\quad
             3\min(2r\bmod n,-2r\bmod n)<n .
$$
The trace is positive since the two-block difference-of-squares test has $4^2<n$. Its value is $2\cos(4\pi/n)+2\cos(4\pi r/n)$. Write $z=\|2r/n\|$. When $z\ge1/3$ the second cosine is at most $-1/2$. For $1/4\le z<1/3$, the distance to $1/3$ is at least $1/(3n)$, and the derivative of the cosine has absolute value at least $\pi\sqrt3$ there. This margin exceeds $1-\cos(4\pi/n)\le8\pi^2/n^2$ for $n\ge64$. For $z<1/4$ the second cosine is positive. Thus the comparison is an exact one-third interval bit for the mixed root. [Two-block small-frequency sign test](salie-and-quarter-parity.md#evaluating-the-unshifted-sign-at-low-frequencies)

Fix a large prime $q$ and choose $p$ uniformly from the primes in $(q/2,q)$. The limiting distribution of $W_{pq}(1)$ on $[0,4]$ has cumulative distribution $F(z)=(2/\pi)\arcsin(\sqrt z/2)$. In particular the comparison with one returns its upper outcome with probability $2/3+O_\epsilon(q^{-1/48+\epsilon})$. Indeed $r=2p(p^{-1}\bmod q)-1$ is a mixed root, and $2r/(pq)=4(p^{-1}\bmod q)/q-2/(pq)$. The prime-sum estimate for inverses gives interval discrepancy $O_\epsilon(q^{-1/48+\epsilon})$ by the interval Fourier norm bound. The trace differs by $O(q^{-2})$ from $2+2\cos(2\pi u)$ on this inverse grid. This limiting function has the displayed arcsine distribution, and moving its argument in the cumulative distribution by $O(q^{-2})$ costs $O(1/q)$ uniformly, including at the two endpoints. The same decision-tree argument as for the centered bit bounds prediction accuracy by $2/3+O(q^{-\gamma})$ for algorithms reading at most a sufficiently small constant times $\log q$ individual bits of $pq$, even when $q$ is supplied. The target set now has measure $2/3$ and is still a bounded union of intervals. [Inverse-prime bound and input-probe proof](centered-bit-probes.md)

A prime lift gives an exact statement about frequency-one **signs**. For any odd $P>1$ and any prime $\ell>8$ coprime to $P$, write $b=\ell^{-1}\bmod P$ and $s(x)=\operatorname{sgn}\cos(2\pi x)$. Then
$$
              \operatorname{sgn}W_{P\ell}(1)
                   =\operatorname{sgn}W_P(b)\,s(2b/P).
$$
Indeed $P^{-1}/\ell+b/P=1+1/(P\ell)$ with both inverses taken in their standard positive residue ranges. The last prime's cosine sign equals $s(2b/P)$ because the phase perturbation $2/(P\ell)$ is smaller than the distance $1/(4P)$ from an odd grid point to a quarter boundary. CRT gives the identity. As $\ell$ varies over primes, $b$ is uniform on units of the fixed modulus $P$. Thus if $P$ has two large prime-power blocks $U,V$, the limiting proportion of negative frequency-one signs on $P\ell$ is exactly the public-comparison error fraction at $P$, namely $1/4+O(1/U+1/V)$. The earlier triangle formula gives the finite-$P$ fraction exactly. In particular all three prime factors can grow along examples with a negative sign at frequency one. [Finite unit-grid formula](salie-and-quarter-parity.md#a-comparison-that-works-without-the-factors)

For $q=1{,}000{,}003$, 24,623 of 36,960 covered prime choices gave the upper magnitude outcome. The integer interval test agreed with the numerical trace at all 42,050 tested two-prime inputs. A separate check of 1,191 prime lifts saw 274 negative signs. [Fixed-frequency replay](../experiments/salie-fixed-frequency.py)
