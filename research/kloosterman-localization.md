# Localizing a mixed root from coarse Kloosterman sums

Let $n$ be odd with exactly two distinct prime divisors, including arbitrary positive multiplicities, and set $Q=n^2$. The complete factorization of $n$ follows from $O(\log n)$ classical Kloosterman sums at modulus $Q$, each given with absolute error at most $n/128$. All arithmetic outside the queries costs polynomial time in $\log n$. The required error is a fixed constant after division by $\sqrt Q$. This gives an alternative to evaluating the [fixed-width floor sums](floor-sum-and-log-parity.md#nonadaptive-queries-for-two-distinct-prime-divisors). Its unknown cost is approximating each sum on an unfactored input.

Exact sign queries at the original square modulus give complete factoring in polynomial time for logarithmically many distinct prime factors, and in deterministic $2^{O(\sqrt b)}$ time and queries for arbitrary prime support, where $b$ is the input bit length. [Proof for sign queries](#sign-decoding-with-logarithmically-many-prime-factors)

For arbitrary prime support, a separate deterministic polynomial-time reduction uses only fixed-threshold comparison bits after adding known prime factors to the base of the square modulus. [All-input threshold reduction](kloosterman-threshold.md)

## Stationary phase at a square modulus

For a unit $t\bmod n$, define $e_Q(z)=\exp(2\pi iz/Q)$ and
$$
K(t)=\sum_{u\bmod Q}^{*}e_Q(t(u+u^{-1})).
$$
Group terms by $u=v+jn$, $0\le j<n$. Inversion modulo $Q$ gives $u^{-1}=v^{-1}-jnv^{-2}$. The sum over $j$ is zero unless $v^2=1\bmod n$, when it has $n$ identical terms. Each surviving class has exactly one lift $w$ with $w^2=1\bmod Q$, since $2v$ is a unit modulo $n$. Using these lifts as representatives gives
$$
K(t)/n=\sum_{w^2=1\bmod Q} e_Q(2tw).
$$
This grouping is the classical stationary-phase evaluation at even prime-power exponents applied directly at the square modulus. The derivation does not need the prime factors to write the identity. [Williams, *Note on the Kloosterman sum*](https://people.math.carleton.ca/~williams/papers/pdf/040.pdf) · [Milićević, discussion of stationary phase](https://pure.mpg.de/rest/items/item_3118941_1/component/file_3118943/content)

The four roots are $1,-1,r,-r$, with $r$ having opposite signs on the two prime-power components. Subtract $2\cos(4\pi t/Q)$ from the normalized answer and divide by two. The result estimates $h(t)=\cos(4\pi tr/Q)$ within $1/128$, including rounding the known term to error less than $1/256$. Conversely a known factorization gives all four terms by CRT to any requested precision.

## Keeping the error bounded through doubling

Choose $c$ among powers of two until the estimate of $h(c)$ has absolute value at most $3/4$. Such a $c$ occurs after $O(\log Q)$ doublings. Indeed the distance of $2cr/Q$ to the nearest integer is initially between $1/Q$ and $1/2$. A distance in $[1/8,3/8]$ gives $|h(c)|\le1/\sqrt2$. A distance above $3/8$ drops below $1/4$ on the next doubling, and any positive distance below $1/8$ doubles until it reaches $[1/8,1/4)$. All residues here are nonzero modulo the odd $Q$.

Choose the representative angle $\phi\in[0,\pi]$ of $\pm4\pi cr/Q$, so its sine is positive. Write $a$ for the estimate of $\cos\phi$ at the chosen anchor. Both $\sin\phi$ and $\sqrt{1-a^2}$ exceed $3/5$. For each $0\le j\le J=\lceil\log_2 Q\rceil$, obtain estimates $v$ of $\cos(2^j\phi)$ and $w$ of $\cos((2^j+e)\phi)$, with $e=+1$ or $-1$. Choose the sign so $2^j+e$ is a unit modulo $n$. For $j=0$, take $+1$. For $j>0$, the two odd choices are coprime. If both have a nontrivial gcd with $n$, each gcd contains just one prime type, so integer roots and primality tests already recover both primes. Otherwise both required frequencies are units. The sine estimate is
$$
e\,(av-w)/\sqrt{1-a^2}.
$$
The numerator differs from its exact counterpart by less than $3/128+1/128^2$. The denominator error is less than $2/(128\cdot(6/5))$ by the difference of squares. After division the sine error is less than $1/12$, and the cosine error is at most $1/128$. The resulting point in the plane lies within $1/10$ of the unit vector at angle $2^j\phi$.

Take the nearest of 32 equally spaced directions, recording it as $z_j$ in turns modulo one. A grid direction is within $\pi/32$ in Euclidean distance of the true vector. Thus the chosen direction is within $2/10+\pi/32<2\sin(\pi/16)$ of the true vector, giving circular error less than $1/16$ turn. The strict slack allows fixed-precision arithmetic in this step. Trigonometric evaluation of known rational angles can use ordinary Taylor bounds after reduction modulo one.

Start at $z_J$ and go backwards. At stage $j$, take the one of the two modular halves of the current value nearer to $z_j$. The correct half is within $1/16+1/32<1/4$ of $z_j$ and the alternatives differ by $1/2$, so the chosen half has at most half the previous error. This gives $\phi/(2\pi)$ modulo one within $2^{-J}/16$. Multiply by $Q$ and round to the nearest integer to recover $\pm2cr\bmod Q$. The inverse of $2c$ gives a mixed root, and the gcds of its two neighbors with $n$ give the two prime-power blocks. The modular halving calculation uses $O(\log Q)$ bits.

## A check on truncating the stationary points

Over unit frequencies $t\bmod Q$ the functions $e_Q(2tw)$ at distinct roots are orthogonal. Some odd prime $p\mid n$ sees opposite signs for $w,w'$, so $p\nmid2(w-w')$ while $p^2\mid Q$. The sum over units modulo the full $p$-part of $Q$ vanishes by grouping lifts modulo the preceding power of $p$. CRT gives the vanishing inner product over $Q$. For inputs with two prime divisors, retaining only the known roots $\pm1$ therefore has mean squared error 2 on the normalized sum. The pointwise squared error is at most 4, so at least one third of all unit frequencies have absolute error at least 1. This is a bound on that truncation across frequencies. The decoder uses a particular set of frequencies.

Bruin's approximation algorithms concern finite fields and quantum computation. The stationary-phase identity above still requires finding the mixed-root contribution at this integer modulus to get a fast classical evaluator. [Bruin, *On quantum computation of Kloosterman sums*](https://arxiv.org/abs/1807.03600)

For the dyadic frequencies specifically, the omitted pair contributes $2\cos\theta$ and then $2\cos(2\theta)$. The identity $\cos(2\theta)=2\cos^2\theta-1$ shows that one of these two normalized errors has magnitude at least 1.

## Signs at the original square modulus

For odd $n$ with at most a fixed number of distinct prime divisors, complete deterministic factoring is polynomial-time equivalent to computing the **exact sign** of $K(t)$ at unit frequencies of the original modulus $n^2$. For an arbitrary $b$-bit odd input, the forward reduction takes $2^{O(\sqrt{b\log(2b)})}$ bit operations and sign queries. All query frequencies are nonadaptive. With a coarse value of $K(t)/n$ to absolute error $1/128$ in place of the sign, the corresponding bounds are polynomial for $O(\log b)$ distinct primes, and $2^{O(\sqrt b)}$ for arbitrary inputs. These are costs outside the oracle. The original-modulus sign is a parity of local quarter-interval tests.

Write $n=tm$ after trial division to an explicit bound $B$ below, with all prime factors of $t$ removed from $m$. Write $Q=m^2$, $D_i=p_i^{2e_i}$ for its $r$ residual prime-power components and $c_i=(Q/D_i)^{-1}\bmod D_i$. Use the auxiliary functions on all residues
$$
F(v)=\prod_i2\cos(2\pi\,2c_iv/D_i),\qquad
S(v)=\prod_i s_{D_i}(2c_iv),\qquad s_D(x)=\operatorname{sgn}\cos(2\pi x/D).
$$
For units, stationary phase identifies $F$ with the normalized sum and $S$ with its sign. Exactly,
$$
S(v)=(-1)^{\sum_i\lfloor4c_i v/D_i+1/2\rfloor}.
$$
Odd denominators preclude ties. The factors of $n$ therefore evaluate the sign by integer arithmetic. Conversely, an original-modulus query can sample the residual at any unit $v\bmod Q$. Impose $T\equiv vt^2\bmod Q$ and $2T\equiv n^2/D\bmod D$ for each known component $D\mid t^2$ of full prime-power order. Its cosine is $2\cos(2\pi/D)>1$ since $D\ge9$. The product of the known components preserves the sign. For coarse values divide by that product. Its magnitude is between 1 and $2^b$, so $O(b)$ fractional working bits with a sufficiently large constant keep the resulting absolute error below $1/100$.

**Fourier coefficients.** Write $k=\lfloor D/4\rfloor$. On the cyclic group modulo $D$ we have $s_D=2\,1_{[-k,k]}-1$. With normalized Fourier coefficients,
$$
\widehat s_D(1)=\widehat s_D(-1)=\frac{2\sin((2k+1)\pi/D)}{D\sin(\pi/D)}
=\frac{1}{D\sin(\pi/(2D))}\ge\frac{2}{\pi}.
$$
For other nonzero frequencies $h$ the absolute value is at most $2/(D|\sin(\pi h/D)|)$. Summing gives $\|\widehat s_D\|_1\le C(1+\log D)$ for an absolute $C$. CRT makes each global Fourier coefficient of $S$ a product of local coefficients. For every root $w^2=1\bmod Q$, the coefficient at $f=2w$ uses precisely the local modes $\pm1$. Indeed the CRT idempotents are $(Q/D_i)c_i$, so independent choices of signs give exactly these global frequencies. Hence all $2^r$ desired coefficients exceed $\nu=2^{-r}$, and the whole coefficient absolute sum is bounded by $T_0=(C'(1+b))^r$. For $F$, the same desired coefficients all equal one, the other coefficients vanish, and $T_0=2^r$.

**Deterministic sampling.** Use an integer upper bound $R$ for $r$ to evaluate the preceding bounds before factoring $m$. In the sign case use $\nu=2^{-R}$ and $T_0=(C'(1+b))^R$. In the coarse case use $\nu=1$ and $T_0=2^R$. Set $L=\lceil10^5 T_0/\nu\rceil$, enumerate the small-bias dilations at bias $\nu/(10^5T_0)$, and search a frequency mesh with spacing at most $\nu/(10^5T_0 L)$. The Fejér kernel and its weighted phase samples are as in the threshold proof. If the least prime in $m$ exceeds $L$, every nonzero frequency difference has additive order greater than $L$. For each desired frequency some enumerated dilation gives interference at most
$$
T_0\left((L+1)^{-1}+\nu/(10^5T_0)\right).
$$
The move to the nearest mesh point costs at most $2\pi L T_0$ times the spacing. Both bounds hold after every common translation. [Kernel, deterministic dilation set and inversion](kloosterman-threshold.md#a-deterministic-set-of-dilations-and-translations)

For each dilation the shifts $0,1,2,\ldots,2^{\lceil\log_2Q\rceil}$ (powers of two after zero) and indices $-L\le k\le L$ specify at most $U=(2L+1)(2b+3)$ locations. Choose $B>RU+L$. Some integer $s\in[0,RU]$ translates all locations to units. Each residual prime exceeds $RU$, and for any one location it forbids at most one candidate translation. There are at most $rU$ forbidden candidates altogether. The decoder finds the first good $s$ by gcds. This avoids requiring any sign answer at a nonunit.

At the tag of a desired frequency the translated, weighted samples approximate $\widehat S(f)e_Q((s+u)f)$ or $\widehat F(f)e_Q((s+u)f)$. The error is below $\nu/64$, including sample and numerical error: the sign is exact, and the coarse case has $\nu=1$. Dividing each dyadic phase sample by its zero-shift anchor and applying modular halving as above recovers $f$ exactly. One may skip anchors of magnitude below $\nu/2$. Test each proposal by squaring $w=f/2\bmod Q$. For verified roots, partition each current block $d$ of $m$ by $\gcd(d,w-1)$ and the complementary quotient. Every pair of distinct prime powers has opposite signs at some recovered root. Their unitary splits separate all blocks, whose prime bases are recovered by integer roots and primality testing.

For a promised bound $R$, the search and trial division to $B=RU+L+1$ are polynomial in $b,T_0/\nu,R$. For the all-input sign bound choose $B=2^{\lceil A\sqrt{b\log_2(2b)}\rceil}$ at the outset and $R=\lfloor b/\log_2 B\rfloor$. For a sufficiently large absolute $A$ this $B$ exceeds $RU+L$, since $\log_2 L=O(1+R\log(2b))$. In the coarse case take $B=2^{\lceil A\sqrt b\rceil}$ and use $\log_2 L=O(1+R)$. Small inputs and $m=1$ are immediate. The padded comparison theorem gives a polynomial all-input reduction with a different oracle. [Padded threshold proof](kloosterman-threshold.md)

The finite sign replay queried the original square modulus and verified all eight, sixteen and eight roots in three fixtures. The bases were $8{,}813{,}740{,}459$, $18{,}359{,}021{,}376{,}097$ and $18{,}094{,}609{,}162{,}327$, respectively. They took 70,488, 92,915 and 92,958 distinct unit sign queries. The third included $2053^2$. Literal inverse sums check both signs at $105^2$. The three larger oracles compute exact local quarter comparisons from the fixture factors. The decoder uses one public dilation, a floating-point FFT and exact root and gcd checks. [Replay with the shared frequency decoder](../experiments/kloosterman-threshold.py)

## Sign decoding with logarithmically many prime factors

For an odd $b$-bit input with at most $R$ distinct prime factors, the exact-sign reduction at the original square modulus takes $2^{O(R)}\operatorname{poly}(b)$ deterministic work and nonadaptive unit queries. Consequently it is polynomial for $R=O(\log b)$. Without a promise on the prime support, the bound is $2^{O(\sqrt b)}$ including trial division. The improvement comes from approximating the sign product on the particular translated sample sets used for phase recovery.

Let $r\le R$ denote the number of residual prime-power components after trial division, $h=R+\lceil\log_2(2+b)\rceil$, and $s(x)=\operatorname{sgn}\cos(2\pi x)$ on the unit circle. We evaluate it only away from its two jumps. Let $s_j$ be its Fejér mean with multiplier $(1-|k|/2^j)_+$ on Fourier mode $k$. Then $s_0=0$. For $j\ge1$ put $\Delta_j=s_j-s_{j-1}$. If $d(x)$ is the circular distance to the nearer jump, there is an absolute $C$ such that
$$
\|\widehat{\Delta_j}\|_1\le C,\qquad
|\Delta_j(x)|\le C2^{-j}/d(x).
$$
Indeed the nonzero Fourier coefficients of the square wave are bounded by $1/|k|$. Up to $2^{j-1}$ the multiplier difference is $|k|/2^j$ and the remaining frequencies occupy just the next dyadic interval. For the pointwise estimate the averaging kernel $n^{-1}|\sum_{u=0}^{n-1}e^{2\pi iuy}|^2$ has integral one and is $O(1/(n\|y\|^2))$. Its integral outside distance $d(x)$ is $O(1/(n d(x)))$. Within that distance the square wave is constant. This also proves $s=\sum_{j\ge1}\Delta_j$ at all the required points.

At $x_i=2c_iv/D_i\bmod1$, telescope each square wave and retain only products whose total dyadic level is at most $4U$, where $U=Ah$ and $A$ is a sufficiently large fixed integer. Call the resulting trigonometric polynomial $P(v)$. Pullback to a finite cyclic group adds coefficients that alias to the same mode, so it cannot increase their absolute sum. Counting level tuples gives
$$
T=\|\widehat P\|_1\le C^r\binom{4U+r}{r}
   \le 2^{O((1+\log A)h)} .
$$
The proof uses these hidden coordinates to describe $P$. The algorithm evaluates only the original sign. Truncation by the sum of levels is the classical sparse-grid construction. [Smolyak on product quadrature](https://www.mathnet.ru/eng/dan27586) · [Temlyakov on hyperbolic-cross approximation](https://arxiv.org/abs/1412.8647)

Set $u_i=\lfloor\log_2(1/d(x_i))\rfloor$. On $\sum_i u_i\le U$ the discarded terms have total absolute value at most $C_1^r2^{-U}$. Indeed their bound is $(2C)^r2^U\sum_{k>4U}\binom{k+r-1}{r-1}2^{-k}$, and factoring out $2^{-2U}$ leaves at most $(1-2^{-1/2})^{-r}$. The estimate is pointwise on this good set.

To control the complement, let the sample argument have any translate of an $\epsilon$-biased distribution on the cyclic group, with $\epsilon=2^{-2Ah}$. Uniform measure works too. The bad set lies in a union over $v_i\ge0$, $\sum v_i=U$, of rectangles $d(x_i)\le2^{-v_i}$. For a single local grid and radius $\rho=2^{-v_i}$, use the constant one for $\rho\ge1/8$. For smaller $\rho$, majorize the two short intervals by two triangular functions of radius $2\rho$ and height two centered at the jumps. Each unshifted height-one tent has nonnegative Fourier coefficients summing to one, as follows by convolving two equal intervals. Translation and grid restriction keep its coefficient absolute sum at most one. The majorant thus has absolute sum at most four, and its uniform grid mean is $O(\rho)$: when $\rho<1/(4D_i)$ the event is empty and we can use zero, and otherwise the grid-point count gives $O(\rho+1/D_i)=O(\rho)$.

The axes are independent by CRT under uniform measure. The product majorant therefore has mean at most $C_2^r2^{-U}$ and Fourier norm at most $4^r$. Bias increases its expected value by at most $4^r\epsilon$ under any common translation. There are at most $\binom{U+r}{r}$ rectangles. On the bad set use the global estimate $|S-P|\le 1+T$. Combining this with the good-set bound gives
$$
\mathbb E |S-P|\le C_1^r2^{-U}
 +(1+T)\binom{U+r}{r}(C_2^r2^{-U}+4^r\epsilon)
 \le 2^{-Ah/2}=:\eta
$$
for $A$ sufficiently large, since the positive prefactors have log-size $O((1+\log A)h)$. This argument applies to every translate and also to uniform measure. In particular each desired coefficient of $P$ differs from the corresponding coefficient of $S$ by at most $\eta$.

Use the preceding Fejér frequency decoder with a public upper bound $2^{O((1+\log A)h)}$ on $T$ and scale $\nu=2^{-R}$. Its dilation isolation and mesh estimates apply to $P$. For a fixed good dilation and for each shift $u$, the nonnegative weights sum to one, so the expected weighted difference between the sign samples and the samples of $P$ on the row $s+ka+u$ is at most $\eta$ over the second, $\epsilon$-biased translation support. Markov's inequality and a union bound over at most $2b+3$ shifts give probability below $1/4$ of any row exceeding $\nu/512$, increasing $A$ if needed. This bound is independent of the mesh point. The probability of *any* nonunit is at most $(2L+1)(2b+3)r(1/B+\epsilon)$, where $B$ is the trial cutoff: for each prime divisor its divisibility indicator has mean $1/p$ and Fourier norm one. Choose $B=2^{C_3 h}$ with $C_3$ large enough for the $1/B$ term and for $B>L$. The $\epsilon$ term is small because $\log_2 L=O((1+\log A)h)$ whereas $-\log_2\epsilon=2Ah$. Some enumerated translation has all unit samples and all rows within the error allowance. The decoder tries every translation with unit rows. Isolation, mesh and approximation errors together are less than $\nu/64$ at the desired tag, while the desired coefficient has magnitude at least $\nu-\eta$. The anchored phase and exact root checks therefore apply.

Both small-bias enumerations, the mesh, the window and the trial cutoff are $2^{O(h)}$. In the all-input case choose $R=\lceil\sqrt b\rceil$ in advance. Removing primes through the resulting $B$ leaves at most $b/\log_2 B\le R$ prime types, which is all the proof uses. This gives the claimed $2^{O(\sqrt b)}$ bound.

The finite approximation check compares the truncated sign product with exact quarter signs at all 11,025 CRT grid points of local orders 9, 25 and 49. At total levels 4, 8, 12 and 16 the mean absolute errors are 0.821246, 0.294281, 0.056493 and 0.007498. This checks a full small uniform grid. The bound for every translated small-bias support is analytic. [Approximation and decoder replay](../experiments/kloosterman-threshold.py)

## Replay

This Python block evaluates the original finite sum on three small inputs. The decoder sees only values rounded to a grid of spacing $1/128$. A second check uses enumerated stationary roots with deterministic perturbations of magnitude $1/128$ on a wider range.

~~~python
from fractions import Fraction
from math import atan2, cos, gcd, pi, sqrt

def decode(n, normalized):
    Q = n*n

    def estimate(t):
        t %= Q
        assert gcd(t, n) == 1
        return (normalized(t) - 2*cos(2*pi*((2*t) % Q)/Q))/2

    c = 1
    while abs(a := estimate(c)) > 0.75:
        c *= 2
        assert c <= 8*Q
    directions = []
    for j in range(Q.bit_length()+1):
        power = 1 << j
        sign = 1 if gcd(power+1,n) == 1 else -1
        if gcd(power+sign,n) != 1:
            return gcd(power-1,n)
        v = estimate(c*power)
        w = estimate(c*(power+sign))
        sine = sign*(a*v-w)/sqrt(1-a*a)
        directions.append(Fraction(round(32*atan2(sine,v)/(2*pi)) % 32,32))
    phase = directions.pop()
    for target in reversed(directions):
        candidates = (phase/2,(phase+1)/2)
        phase = min(candidates, key=lambda z: min((z-target)%1,(target-z)%1))
    root = round(phase*Q)*pow(2*c,-1,Q) % Q
    assert root*root % Q == 1
    return gcd(root-1,n)

for n in (15,35,45):
    Q = n*n
    angles = [(v+pow(v,-1,Q)) % Q for v in range(Q) if gcd(v,n)==1]
    def direct(t):
        exact = sum(cos(2*pi*(t*x % Q)/Q) for x in angles)/n
        return round(128*exact)/128
    divisor = decode(n,direct)
    assert 1 < divisor < n and n % divisor == 0

cases = 0
for n in range(15,400,2):
    roots = [r for r in range(n) if r*r % n == 1]
    if len(roots) != 4:
        continue
    Q = n*n
    lifted = [(r - (r*r-1)*pow(2*r,-1,Q)) % Q for r in roots]
    for noise in (1,-1):
        def noisy(t):
            values = (cos(2*pi*(2*t*r % Q)/Q) for r in lifted)
            return sum(values) + noise*(-1 if t.bit_count()%2 else 1)/128
        divisor = decode(n,noisy)
        assert 1 < divisor < n and n % divisor == 0
    cases += 1
print(cases, "two-prime inputs checked with both noise patterns")
~~~
