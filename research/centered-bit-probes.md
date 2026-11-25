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

## Rational functions and quadratic-character probes

The predictor can also ask either of the following questions about the hidden prime $p$ in $\mathbb F_q$. At each node it may choose new coefficients using $q$ and all preceding answers.

- Is $R(p)$ a nonzero square, for any rational function $R$ of degree at most $D$?
- Is the standard representative of $R(p)$ in a chosen interval of residues, for any rational function of degree at most $D$ that is regular at zero?

Here $D=q^{o(1)}$. Values at poles can be assigned a fixed bit. There is an absolute $\kappa>0$ such that a tree with at most $\kappa\log_2 q$ digit and quadratic-character probes combined and at most $\kappa\log_2 q/\log_2\log_2 q$ interval probes still predicts any whole informative word with probability $2^{-h}+O(q^{-\gamma})$ for some $\gamma>0$. The budgets apply along each path. The word and center can be chosen at its leaf as above. This is a restriction on information obtained from the hidden input. The arithmetic between probes can be unrestricted.

Fix a leaf with $d$ digit probes, $s$ character probes and $u$ interval probes. Remove constant queries. At most $O((s+u)D)$ candidate primes are zeros or poles requiring special treatment. Away from these, the indicator of one character answer is $(1\pm\chi(R(p)))/2$, with $\chi$ the quadratic character. Expanding their product has coefficient absolute sum at most one. Each term is a single quadratic character of a product of the rational functions. An interval's Fourier expansion, including for the complementary answer, costs $O(1+\log q)$ in coefficient absolute sum. The $d$ digit restrictions use the same joint expansion as above. Completing its real frequencies modulo $q$ adds only a linear phase in $p$.

After subtracting $2^{-h}$ times the leaf mass, the nonconstant target Fourier modes involve trace functions of the form
$$
\chi(S(x))\, e_q\!\left(A/x+Bx+\sum_{i=1}^u a_iR_i(x)\right),\qquad A\ne0 .
$$
The additive phase retains its simple pole at zero, because every interval function is regular there. Its Artin–Schreier sheaf is wild at zero, and the quadratic factor is tame there, including when $S$ has a pole or zero. Thus the rank-one sheaf is nonexceptional for Fouvry–Kowalski–Michel. Its conductor is $O(1+(s+u)D)$ by counting singularities and pole orders. Theorem 1.5 has polynomial dependence on the conductor, so this costs $q^{o(1)}$. Omitting a finite set from each trace sum costs its cardinality, with the same total coefficient bounds. The $O(1)$ endpoint exceptions for the target word and the $O(1/q)$ constant-coefficient error are harmless. [Fouvry–Kowalski–Michel, conductor and Theorem 1.5](https://people.math.ethz.ch/~kowalski/weights-over-primes.pdf#page=3)

The leaf's joint discrepancy is therefore at most $q^{-1/48+\epsilon+o(1)}[C(1+b/d)]^d[C(1+\log q)]^u$, after dividing by the number of candidate primes. Use one for the digit factor at $d=0$. Summing over at most $2^{d_{\max}+s_{\max}+u_{\max}}$ leaves gives a power saving for sufficiently small $\kappa$. This controls overall success even when a particular leaf is rare.

The same proof allows a pole at zero in an interval function if the coefficient of $X^{-1}$ in its Laurent expansion is zero. The phase still has nonzero $X^{-1}$ coefficient, and its highest surviving pole order is between one and $q-1$, which suffices for wild ramification. Allowing the unshifted reciprocal removes the bound: a single middle-half interval test on $2/p\bmod q$, followed by complementation, gives the first informative bit exactly for $p>4$. The angular correction $1/(pq)$ is then less than $1/(4q)$, the minimum possible distance from a $q$-grid point to a quarter boundary.

## Finite check

For $q=1{,}000{,}003$ there are 36,960 possible $p$. Exhausting all adaptive depth-two binary decision trees gives a best first-bit score of 18,901 out of 36,960 (51.14%). The calculation uses all choices for the first position, all choices for each of the two second positions, and exact majority at the four leaves. Four interval probes alone scored 18,676, four quadratic-character probes alone scored 18,725, and the combined 48-probe menu scored 18,901. This checks the prediction model at one modulus. The power saving above comes from the prime-sum theorem.

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
    other = (2*q*pow(q,-1,p)-1) % n
    assert s+other == n and s%p == p-1 and s%q == 1
    return int(4*min(s,n-s) < n)

def mask(pred):
    return int.from_bytes(bytes(map(pred,primes)), 'little')

truth = mask(first_bit)
cols = [mask(lambda p: ((q*p) >> j) & 1) for j in range((q*q).bit_length())]
rows = mask(lambda p: 1)

def majority(r):
    ones = (r & truth).bit_count()
    return max(ones, r.bit_count()-ones)

def best_two(probes):
    def best_one(r):
        return max(majority(r & c)+majority(r & ~c) for c in probes)
    return max(best_one(rows & c)+best_one(rows & ~c) for c in probes)

def inv_or_zero(x):
    return pow(x,-1,q) if x%q else 0

intervals = [mask(lambda p: q//4 <= (p*p+1)%q < 3*q//4),
             mask(lambda p: q//8 <= (p**3+17)%q < 5*q//8),
             mask(lambda p: q//4 <= inv_or_zero(p+1) < 3*q//4),
             mask(lambda p: q//8 <= inv_or_zero(p+7) < 5*q//8)]
characters = [mask(lambda p,f=f: pow(f(p)%q,(q-1)//2,q)==1) for f in
              (lambda p:p, lambda p:p+1, lambda p:p*p+1,
               lambda p:(p+5)*inv_or_zero(p+7))]
assert len(primes) == 36960
assert [best_two(v) for v in (cols, intervals, characters, cols+intervals+characters)] == [
    18901, 18676, 18725, 18901]
assert truth == mask(lambda p: 4*min(v:=2*pow(p,-1,q)%q,q-v) < q)
~~~

## Advice stored before the center is chosen

Fix a large odd prime $q$, draw $p$ uniformly from the primes in $(q/2,q)$, and let $N=pq$. A predictor knows $q$ and can first store an arbitrary $d$-bit message depending on $p,q$. After that it sees the query center and has access only to $q$, that center, and its message. Let $C$ be any public set of $T$ distinct centers in $[1,q/8]$. For a uniform center in $C$, the predictor's mean accuracy on the informative centered floor bit satisfies
$$
 \Pr[\text{correct}]\le\frac12+O\!\left(\sqrt{\frac{2^d(\log q)^3}{T}}\right).
$$
The same second-moment bound gives an $O(2^d(\log q)^3/(T\delta^2))$ fraction of possible $p$ for which the chosen message has advantage at least $\delta$. Thus inverse-polylogarithmic advantage on a positive fraction of inputs requires $d\ge\log_2 T-O(\log\log q)$. At $T=\lfloor q/12\rfloor$ this is within $O(\log\log q)$ of the bits needed to identify the smaller prime completely. The preprocessing can read all of $N$ and perform unrestricted computation. The restriction is the size of the message available *after* the center is known. [Factoring from biased answers on short centers](floor-sum-and-log-parity.md#factoring-from-imperfect-answers-at-short-centers)

To prove the bound, put $G=\mathbb F_q^\times$, $a=2p^{-1}\bmod q$ and $F(y)=\operatorname{sgn}\cos(2\pi y/q)$ on $G$. At all the specified centers the true sign is exactly $F(ca)$. Indeed the mixed-root angle differs from $ca/q$ modulo one by $c/(pq)<1/(4q)$, and every point of the $q$-grid is at least $1/(4q)$ from a quarter boundary. All centers are units. The known rational-root contribution to the centered parity is constant over these short centers.

Each message specifies an arbitrary word $u(c)\in\{-1,1\}$ on $C$. Extend it by zero to $G$. For $a\in G$ let $S_u(a)=\sum_{c\in G}u(c)F(ac)$. For every multiplicative character $\chi$ of $G$,
$$
 \left|\sum_{y\in G}F(y)\overline{\chi(y)}\right|\ll\sqrt q\log q .
$$
For the principal character the signed count has absolute value at most two. For a nonprincipal character, express the two outer intervals by additive Fourier series on $\mathbb F_q$. Their normalized Fourier absolute sums are $O(\log q)$ by the geometric series formula. Each nonzero additive twist of $\chi$ has Gauss sum of magnitude $\sqrt q$, and the zero twist vanishes. This is the usual completion proof of Pólya–Vinogradov. [Pomerance, character sums on intervals](https://math.dartmouth.edu/~carlp/pv.pdf)

Multiplicative Parseval applied to the correlation and $\sum_c|u(c)|^2=T$ now gives $\sum_{a\in G}|S_u(a)|^2\ll q(\log q)^2T$. Distinct candidate primes give distinct $a$, and there are $\asymp q/\log q$ such primes. Therefore $\mathbb E_p|S_u(a)/T|^2\ll(\log q)^3/T$ for every fixed word. Bound the squared maximum over the $2^d$ words by the sum of their squares. Cauchy–Schwarz and Markov's inequality give the two assertions. Conditioning on independent random coins gives the same bounds for randomized encoders or decoders. More generally for a fixed distribution of centers with probabilities $w_c$, the same proof replaces $1/T$ by $\sum_c w_c^2$.

At $q=65{,}537$ the replay uses 3,030 possible smaller primes and 4,096 centers. For explicit menus of 1, 4, 16 and 64 words, exact integer agreement scores gave mean best accuracies of 50.01%, 50.23%, 50.81% and 52.32%. These are results for the indicated menus. The replay checks the spectral inequality for each of the 64 words and independently validates 192 correlations against the actual mixed-root angles. [Finite multiplicative Fourier replay](../experiments/short-center-advice.py)
