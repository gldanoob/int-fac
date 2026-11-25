# How many input bits predict a centered floor-sum parity?

Fix a large odd prime $q$. Draw $p$ uniformly from the primes in $(q/2,q)$ and write $n=pq$. An algorithm knows $q$ and may choose individual binary digits of $n$ to read, adaptively and with unrestricted computation between reads. There are absolute constants $\kappa,\gamma>0$ such that any algorithm reading at most $\kappa\log_2 q$ digits predicts the first informative centered floor-sum bit with probability at most $1/2+O(q^{-\gamma})$. The same estimate holds if the bit length of $n$ is supplied. Thus a constant prediction advantage requires reading a linear number of input bits. This bound concerns input access. The time needed after reading the input remains open. [Centered floor sum and informative bit](floor-sum-and-log-parity.md#nonadaptive-queries-for-two-distinct-prime-divisors)

More generally, let the algorithm predict a word of $h\ge1$ consecutive informative bits, starting at a dyadic center $c=2^j\le q$. Its probability of getting the entire word right is $2^{-h}+O(q^{-\gamma})$, uniformly in $h$ and $j$. The center may even be selected at the leaf where the prediction is made. Fixing the random coins gives the same result for randomized trees with the stated probe limit.

## The mixed root as an inverse modulo a prime

Take $a=p^{-1}\bmod q$ and $s=2pa-1$. This is $-1$ modulo $p$ and $1$ modulo $q$. Either sign of $s$ gives the same informative bits. At center $c$ the bit is one when the fractional part of $cs/n$ lies in the outer quarters. Its first $h$ successive answers specify a union of two reflected dyadic intervals, each of length $2^{-h-1}$. Indeed the first binary digit can take either value, and the adjacent equality bits fix the other $h$ digits. The odd modulus prevents ties.

We have $cs/n=2ca/q-c/(pq)$. Replacing this angle by $2ca/q$ changes membership in a given pair of intervals only within $2/q$ of an endpoint, since $p>q/2$ and $c\le q$. As $p$ varies the residues $2ca\bmod q$ are distinct. Each given word therefore incurs $O(1)$ exceptions, uniformly even for very narrow intervals.

## Cancellation with prescribed input digits

Write $e_q(x)=\exp(2\pi i x/q)$. The unsmoothed prime-sum estimate of Fouvry, Kowalski and Michel gives, for every $\epsilon>0$, uniformly in $A\ne0\bmod q$ and $B\bmod q$,

$$
\left|\sum_{\substack{p\in I\\p\text{ prime}}} e_q(Ap^{-1}+Bp)\right|\ll_\epsilon q^{1-1/48+\epsilon}
$$

for every interval $I\subset(q/2,q)$. Subtract two prefix estimates. The rational phase has a simple pole at zero, so its rank-one Artin–Schreier sheaf is wildly ramified there. The exceptional additive-linear and Kummer twists in their theorem are tame there. The conductor is bounded uniformly in $A,B$. The authors identify this family explicitly in Remark 1.6. [Fouvry–Kowalski–Michel, Theorem 1.5, equation (1.3)](https://people.math.ethz.ch/~kowalski/weights-over-primes.pdf#page=3)

Use Fourier coefficients normalized by the group order. On a cyclic group of size $Q$, the indicator of an interval has Fourier $\ell^1$ norm $O(1+\log Q)$. The same bound holds after multiplication on the representatives $0,\ldots,Q-1$ by $\exp(2\pi i\theta x)$ for any real $\theta$. This follows by summing the geometric progression bound $\min(1,1/(2Q\|\theta-t/Q\|))$ over the frequencies $t$, with the nearest term bounded by one.

A leaf fixing $d$ distinct digits of a $b$-bit integer has digit indicator $F$ of Fourier $\ell^1$ norm at most $[C(1+b/d)]^d$ on the group of size $2^b$, with norm one if $d=0$. To see this, cut the digit positions immediately above each fixed digit, starting at the least significant end. In each resulting block of length $v_i$, its top digit is fixed and the allowed values form an interval. Free high digits extend the period without changing the norm. Write the integer as $2^v y+z$, with $z$ its lowest block. At frequency $t$ the normalized Fourier coefficient factors into the higher-block coefficient at $t\bmod 2^{b-v}$ and the normalized interval sum over $z$ at real frequency $t/2^b$. Summing over all lifts of a fixed higher-block frequency costs at most $C(1+v)$ by the modulated interval estimate. Iteration gives $\prod_i C(1+v_i)\le[C(1+b/d)]^d$. Digit restrictions and their Fourier norms also appear in Bourgain's work on primes with prescribed digits. [Bourgain, §1](https://arxiv.org/pdf/1105.3895#page=2)

For one leaf, expand $F(qp)$ using this norm bound. Each term is a real-frequency linear phase in $p$. Expanding it on $0,\ldots,q-1$ costs another $O(1+\log q)$ in Fourier norm. Expand the indicator of the two target intervals on the $q$-grid at $2cp^{-1}$. Its constant coefficient is $2^{-h}+O(1/q)$ and the remaining coefficients have total absolute value $O(1+\log q)$. Each nonconstant term now has the prime-sum bound above since $2c$ is invertible modulo $q$.

There are at most $2^D$ leaves for depth $D$. The function $[C(1+b/d)]^d$ is increasing for $d\ge1$ and $C\ge1$. Dividing by the number of primes in $(q/2,q)$, which is asymptotic to $q/(2\log q)$, gives a total error bounded by

$$
O_\epsilon\!\left(q^{-1/48+\epsilon}\,[2C(1+b/D)]^D\right)
$$

for $D\ge1$, absorbing logarithms by slightly reducing $\epsilon$. Use $b=\lceil2\log_2 q\rceil$ with leading zero padding. Taking $D\le\kappa\log_2 q$ for a sufficiently small absolute $\kappa$ makes the error $O(q^{-\gamma})$. If the true length of $n$ is given, it partitions the prime interval at powers of two divided by $q$. There are at most two subintervals and the same prime-sum bound applies to each.

## Finite check

For $q=1{,}000{,}003$ there are 36,960 possible $p$. Exhausting all adaptive depth-two binary decision trees gives a best first-bit score of 18,901 out of 36,960 (51.14%). The calculation uses all choices for the first position, all choices for each of the two second positions, and exact majority at the four leaves. This checks the prediction model at one modulus. The power saving above comes from the prime-sum theorem.

~~~python
from math import isqrt

q = 1_000_003
sieve = bytearray(b'\x01')*(q+1)
for d in range(2, isqrt(q)+1):
    if sieve[d]:
        sieve[d*d::d] = bytes((q-d*d)//d+1)
assert sieve[q]
primes = [p for p in range(q//2+1, q) if sieve[p]]

def first_bit(p):
    n = p*q
    s = (2*p*pow(p,-1,q)-1) % n
    assert s%p == p-1 and s%q == 1
    return int(4*min(s,n-s) < n)

def mask(pred):
    return int.from_bytes(bytes(map(pred,primes)), 'little')

truth = mask(first_bit)
cols = [mask(lambda p: ((q*p) >> j) & 1) for j in range((q*q).bit_length())]
rows = mask(lambda p: 1)

def majority(r):
    ones = (r & truth).bit_count()
    return max(ones, r.bit_count()-ones)

def best_one(r):
    return max(majority(r & col)+majority(r & ~col) for col in cols)

best_two = max(best_one(rows & col)+best_one(rows & ~col) for col in cols)
assert (len(primes), best_two) == (36960, 18901)
~~~
