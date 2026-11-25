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
