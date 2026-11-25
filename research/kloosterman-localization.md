# Localizing a mixed root from coarse Kloosterman sums

Let $n$ be odd with exactly two distinct prime divisors, including arbitrary positive multiplicities, and set $Q=n^2$. The complete factorization of $n$ follows from $O(\log n)$ classical Kloosterman sums at modulus $Q$, each given with absolute error at most $n/128$. All arithmetic outside the queries costs polynomial time in $\log n$. The required error is a fixed constant after division by $\sqrt Q$. This gives an alternative to evaluating the [fixed-width floor sums](floor-sum-and-log-parity.md#nonadaptive-queries-for-two-distinct-prime-divisors). Its unknown cost is approximating each sum on an unfactored input.

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
