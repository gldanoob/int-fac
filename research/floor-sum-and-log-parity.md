# Factoring from quadratic floor-sum parity and discrete-log parity

One exact bit of a univariate quadratic floor sum replaces the two disk counts at each midpoint of the planar reduction. The coefficient stays fixed throughout a split. A separate reduction recovers an order multiple from one exact bit per discrete logarithm on prescribed targets. Both bounds count oracle calls and polynomial-time decoding. The cost of producing the bits on an unfactored input remains open here. [Planar disk reduction](box-count-parity.md#two-planar-disks-suffice) · [Order-multiple reduction](order-and-crt-reductions.md#a-linear-number-of-queries-on-one-cofactor)

## A quadratic floor sum for the roots above a cutoff

Let $n\ge3$ be odd, $k=(n-1)/2$, $a=\lfloor9n/4\rfloor$, $q=an+1$, and $f(t)=\lfloor at^2/q\rfloor$. For every integer $0\le h\le k$,
$$
S(h):=\sum_{t=h+1}^{2n-h-1}f(t)
\equiv \#\{x:h<x\le k,\ x^2\equiv1\pmod n\}\pmod2.
$$
The coefficient $a/q=[0;n,a]$ has two continued-fraction partial quotients after the initial zero. The denominator has $2\log_2 n+O(1)$ bits.

**Proof.** Pair $x$ with $v=2n-x$ for $h<x<n$. From $a/q=1/n-1/(nq)$ and $v^2=x^2+4n(n-x)$,
$$
f(x)=\left\lfloor\frac{x^2-x^2/q}{n}\right\rfloor,\qquad
f(v)=4(n-x)+\left\lfloor\frac{x^2-v^2/q}{n}\right\rfloor .
$$
We have $q>2n^2$, so $0<x^2/q<1$ and $0<v^2/q<2$. Also
$$
\left(\frac{3n-1}{2}\right)^2<q<\left(\frac{3n+1}{2}\right)^2.
$$
Indeed $9n^2/4-n+1<q\le9n^2/4+1$, and $n\ge3$. The bounding squares are consecutive integer squares. Hence $v^2/q>1$ exactly when $x\le k$, and equality never occurs. Writing $x^2=jn+r$ with $0\le r<n$, the two floors after removing $4(n-x)$ differ exactly when $r=1$ and $x\le k$. In that case their difference is one. For $r=0$ both positive subtractions lower the quotient by one. Since $4(n-x)$ is even, the pair has the required parity. The unpaired midpoint contributes $f(n)=n-1$, also even.

**Bisection.** After removing powers of two, handling primes and reducing perfect powers to their bases, an odd residual composite $n$ has $\omega(n)\ge2$ distinct prime divisors. The two signs at each odd prime power give $2^{\omega(n)}$ roots of one by CRT. Pairing $x$ with $n-x$ and removing $1$ leaves $2^{\omega(n)-1}-1$ roots in $[2,k]$. Thus $S(1)$ is odd and $S(k)=0$. In a retained interval $[L,H]$ with odd root count, query $S(M)\bmod2$ at $M=\lfloor(L+H)/2\rfloor$. Keep $[L,M]$ if the cached $S(L-1)$ and $S(M)$ have different parities. Otherwise keep $[M+1,H]$ and cache the new left endpoint bit. Each decision costs one interval-sum parity query.

**Stopping radius.** Stop when $H-L\le2\lfloor\sqrt n\rfloor$. With $c=\lfloor(L+H)/2\rfloor$ the largest possible $|x-c|$ is $\lceil(H-L)/2\rceil\le\lfloor\sqrt n\rfloor$. Apply Coppersmith's **Corollary 1** to the monic quadratic $P(z)=(c+z)^2-1$ modulo the full $n$. It lists all $|z|\le X$ for $X\le n^{1/2}$ in polynomial time at degree two. The corollary reaches the inclusive endpoint by covering the range with translated intervals inside the smaller bound of Theorem 1. Filter the list to $L\le c+z\le H$ and verify the congruence. At least one root survives, and every surviving $x$ has mixed CRT signs, so $1<\gcd(x-1,n)<n$. Halving an initial interval of at most $n/2$ integers down to this diameter takes at most $\tfrac12\log_2 n+O(1)$ queried midpoints per split. Recursing on the factors gives complete factoring. [Coppersmith, §6, Corollary 1, p. 243](https://www.di.ens.fr/~fouque/ens-rennes/coppersmith.pdf#page=11)

## Nonadaptive queries for two distinct prime divisors

Suppose the odd $b$-bit integer $n$ has exactly two distinct prime divisors, with arbitrary positive multiplicities. The complete factorization follows from $\lceil b/2\rceil-1$ floor-sum parity queries chosen before seeing any answers. Every sum uses the same coefficient and interval length. Only the center changes.

**Centered sum.** Fix integers $1\le c\le K$, $0\le m\le n/4$, and put
$$
a=K^2n,\qquad q=an+1,\qquad C=Knc,\qquad F(t)=\lfloor at^2/q\rfloor.
$$
Then
$$
\sum_{t=C-m}^{C+m} F(t)-F(C)
\equiv \#\{1\le x\le m:x^2\equiv c^2\pmod n\}\pmod 2 .
$$
Indeed, $C^2=c^2(q-1)$, so for $1\le x\le m$ the two values $(C\pm x)^2/q$ lie strictly on opposite sides of $c^2$, each at distance less than one. The signed numerators of their deviations are $\pm2Cx+x^2-c^2$. Their signs follow from $x< C$ and $2C>c^2$. Their absolute values are at most $K^2n^2/2+n^2/16+K^2<q$ for $n\ge3$. Since $a/q=(1-1/q)/n$ and $C$ is a multiple of $n$,
$$
F(C\pm x)=\frac{C^2\pm2Cx}{n}
 +\left\lfloor\frac{x^2-(C\pm x)^2/q}{n}\right\rfloor.
$$
The integer terms have even sum. The two floors differ precisely when $x^2-c^2$ is divisible by $n$, in which case they differ by one.

**Digit recovery.** Let $r$ be the unique mixed root of one in $[2,\lfloor n/2\rfloor]$. Use $D=\lceil b/2\rceil$, $K=2^D$, $m=\lfloor n/4\rfloor$, and issue the centered query for each $c=2^j$ with $0\le j\le D-2$. The four roots of $c^2$ modulo $n$ are $\pm c,\pm cr$. Remove the known contribution of $\pm c$ from the centered root count. The remaining bit says whether the fractional part of $2^j r/n$ lies in the first or last quarter of $[0,1)$. The odd denominator precludes dyadic ties. The bit is one precisely when binary digits $j+1$ and $j+2$ of $r/n$ are equal. Digit one is zero since $r<n/2$. Successive equalities therefore supply the first $D$ digits.

Read those digits as $W$. The half-open interval $[nW/K,n(W+1)/K)$ contains $r$ and has length $n/K<\sqrt n$. Intersect with $[2,\lfloor n/2\rfloor]$ and use the translated monic quadratic from the preceding section to recover $r$. The gcds of $r-1$ and $r+1$ with $n$ are the two prime-power blocks. Integer roots and primality tests finish the factorization. The equality tests require only polynomial decoding. The coefficient $a/q=[0;n,a]$ has $q<4n^3+1$, and every endpoint has $O(b)$ bits. The upstream interval-count reduction supplies the mixed-root formulation, and Coppersmith supplies the short-interval recovery. The centered identity gives the translated fixed-length queries. The time to evaluate them on an unfactored input remains open. [Upstream quadratic-congruence reduction](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/quadratic-congruence-factor-recovery.md) · [Coppersmith, Corollary 1](https://www.di.ens.fr/~fouque/ens-rennes/coppersmith.pdf#page=11)

The Lean proof checks the symmetric pair and the complete centered sum for all integers satisfying the stated bounds, including radius zero. It also proves that the outer-quarter predicate gives adjacent-bit equality and that decoding $j$ such answers yields $\lfloor 2^{j+1}r/n\rfloor$ when the first digit is zero. Run `make check` at the repository root. [CenteredFloor.lean](../formal/CenteredFloor.lean)

## What the floor-sum formulas evaluate

- Schinzel extends Lerch's exact formulas for fractional parts of rational quadratics summed over a **complete** residue system. Corollary 1 expresses the unshifted complete sum in terms of class numbers. Here the individual endpoint $h$ carries the root information. Over a full period $0\le t<q$, pairing $t$ and $q-t$ gives $f(q-t)-f(t)=a(q-2t)$. For odd $q$ the full parity is $a(q-1)/2\bmod2$ (zero in this family since $a$ is then even). For even $q$ the pairs cancel and the parity is $\lfloor aq/4\rfloor\bmod2$ from $t=q/2$. For instance $n=7$ gives $(a,q)=(15,106)$ and odd full-period parity. [Schinzel, *An extension of some formulae of Lerch*, pp. 111–112](https://dml.cz/bitstream/handle/10338.dmlcz/120576/ActaOstrav_10-2002-1_12.pdf)
- The Euclidean floor-sum recursion for an affine numerator closes because interchanging rows and columns gives another affine threshold. For $at^2/q$ the inverse threshold is $\lceil\sqrt{qy/a}\rceil$ on the positive axis. Even the two-partial-quotient coefficients above retain the factoring reduction. [Affine floor-sum recursion and proof](https://atcoder.jp/contests/practice2/editorial/579)
- Hiary's Theorem 1.1 evaluates one truncated quadratic exponential sum to inverse-polynomial absolute error at polylogarithmic cost. Writing the congruence indicator as $n^{-1}\sum_{j=0}^{n-1}\exp(2\pi i j(x^2-1)/n)$ introduces $n$ frequencies. Even constant absolute error below $1/2$ per frequency would permit rounding their normalized sum. The outstanding cost is evaluating the frequencies together. Huang–Li's Theorem 1 gives an asymptotic for the incomplete sum of $\lfloor x^2/n\rfloor$ with an error on the square-root scale for interval length comparable to $n$. Extracting the parity requires finer information. [Hiary, Theorem 1.1](https://arxiv.org/pdf/0711.5002#page=2) · [Huang–Li, Theorem 1](https://arxiv.org/pdf/1902.06047#page=2)

## Cost of rounding a nonnegative Fourier approximation

Consider one of the two-prime queries above. Write $m=\lfloor n/4\rfloor$ and let $A$ be the number of $1\le x\le m$ with $x^2\equiv c^2\pmod n$. Each of $\{\pm c\}$ and $\{\pm cr\}$ contributes at most one, so $0\le A\le2$.

Suppose an evaluator replaces the congruence indicator by a real function $K$ on $\mathbb Z/n$ with $K(z)\ge0$ everywhere and $K(0)=1$. It sums $K(x^2-c^2)$ by its $s$ nonzero Fourier coefficients, replaces any $E$ individual summands by their exact indicators, and rounds the result to recover $A$ with absolute error less than $1/2$ before rounding. The frequencies and the corrections may depend on the input and the target. Either a nonzero frequency has a proper gcd with $n$, immediately giving a factor, or
$$
 m < 3.9071(s-1)\sqrt n+Es+\tfrac52s.
$$
In particular the second case requires $s+E=\Omega(\sqrt n)$ even if evaluating each incomplete Gauss sum costs a single operation.

To prove the inequality, normalize the Fourier coefficients by $1/n$ and write $\mu=\widehat K(0)$. Positivity gives $|\widehat K(j)|\le\mu$, whence $K(z)\le s\mu$ for every $z$ and $1\le s\mu$. Each unit frequency $j$ contributes a translated quadratic Gauss sum of magnitude less than $3.9071\sqrt n$, by Korolev's corollary for the partial sum starting at $x=1$. The translation by $-c^2$ contributes a phase of absolute value one. Thus the corrected estimate is at least $\mu(m-3.9071(s-1)\sqrt n-Es)$. It must also be smaller than $A+1/2\le5/2$. Dividing by $\mu$ proves the bound. It applies to summing a pointwise nonnegative approximation and recovering the integer count by rounding. Direct parity evaluation, signed kernels, and methods combining frequencies without listing them remain open. [Korolev, *On incomplete Gaussian sums*, §1, corollary](https://www.mathnet.ru/links/c311880710d7aa0eba8e347d76690a07/tm3644.pdf#page=2)

For $n=101\cdot103$, the three-frequency example $K(z)=\cos^2(\pi jz/n)$ already shows the effect at every center. For each of $j=1,213$, at least 1,266 of the 2,600 summands exceed $1/2$ at each tested center, while $A$ is one or two. After any 100 individual corrections the estimate still exceeds 583. The replay checks the strict cosine inequality using integer residues.

## An order multiple from canonical discrete-log parity

Given a unit $u\bmod n$, let $b$ be the bit length of $n$ and $g=u^{2^b}\bmod n$. Write $\operatorname{ord}_n(u)=2^s r$ with $r$ odd. Since $\operatorname{ord}_n(u)<n<2^b$, the element $g$ has order $r$. If $g=1$, return the order multiple $2^b$. Otherwise $r>1$. The oracle input is $(n,g,y)$ with $y\in\langle g\rangle$, and its answer is the parity of the **least nonnegative** exponent $e$ with $g^e=y$. Adding the odd order $r$ to an exponent flips its parity, so the choice of representative matters.

Generate $y_j=g^{2^j}$ by successive squaring for $1\le j\le2b$. All targets are determined before receiving any answers. Their canonical exponents are $e_j=2^j\bmod r$. The division $2^j=r\lfloor2^j/r\rfloor+e_j$ gives
$$
e_j\bmod2=\lfloor2^j/r\rfloor\bmod2.
$$
These are the first $2b$ digits after the binary point of $1/r$. Read them in order as an integer $D=\lfloor M/r\rfloor$ with $M=2^{2b}$. Since $M>r^2$, $D\ge r$. Writing $M=Dr+w$ with $0\le w<r\le D$ yields $\lfloor M/D\rfloor=r$. Return $2^b r$, a positive multiple of $\operatorname{ord}_n(u)$ of at most $2b$ bits.

Schnorr gives the shift-bit identity relating the parity of $2^j x\bmod r$ to the digits of $x/r$ for odd $r$. The deduction here sets $x=1$ and reconstructs the unknown denominator. It uses $2b$ exact one-bit answers per nontrivial projected base. Composing with the repository's order-multiple reduction under its stated Dirichlet GRH input gives at most $2b^2$ bit queries for a $b$-bit factoring input and polynomial work outside the queries. Nonadaptivity applies within each base. Pomykała–Źrałek's bounded discrete-log reduction instead requests a full exponent $x\le(1-\epsilon)n$ when one exists. [Schnorr, §2, identity preceding Proposition 2](https://eccc.weizmann.ac.il/report/1998/033/download/) · [Order-multiple factoring and query count](order-and-crt-reductions.md#a-linear-number-of-queries-on-one-cofactor) · [Pomykała–Źrałek, published abstract](https://link.springer.com/article/10.1007/s00037-012-0037-5)

## Replay in memory

The Python command compares the floor sums with direct root counts at every cutoff for every odd $n$ from 3 through 1501. The discrete-log check enumerates each generated subgroup to supply independent canonical parity bits.

~~~sh
python3 -B - <<'PY'
from math import gcd, isqrt

tails = 0
for n in range(3, 1502, 2):
    a = 9*n // 4
    q = a*n + 1
    prefix = [0]
    for t in range(2*n):
        prefix.append(prefix[-1] ^ ((a*t*t // q) & 1))
    roots = 0
    for h in range(n//2, -1, -1):
        assert prefix[2*n-h] ^ prefix[h+1] == roots
        roots ^= int(h*h % n == 1)
        tails += 1
    if n <= 75:
        full = sum(a*t*t // q for t in range(q))
        expected = a*((q-1)//2) if q % 2 else a*q//4
        assert (full - expected) % 2 == 0
assert tails == 282375

# Every centered sum is evaluated literally. Direct enumeration supplies the reference root.
cases = queries = 0
for n in range(3, 1502, 2):
    roots = [x for x in range(2, n//2+1) if x*x % n == 1]
    if len(roots) != 1:
        continue
    r, = roots
    D = (n.bit_length()+1)//2
    K = 1 << D
    a, m = K*K*n, n//4
    q = a*n+1
    digit = word = 0
    for j in range(D-1):
        c = 1 << j
        C = K*n*c
        total = sum(a*t*t//q for t in range(C-m, C+m+1))
        rootbit = (total - a*C*C//q) % 2
        assert rootbit == sum((x*x-c*c) % n == 0 for x in range(1, m+1)) % 2
        same = rootbit ^ int(min(c % n, (-c) % n) <= m)
        digit ^= 1 ^ same
        word = 2*word + digit
        queries += 1
    lo, hi = (n*word+K-1)//K, (n*(word+1)-1)//K
    assert lo <= r <= hi and hi-lo <= isqrt(n)
    assert gcd(r-1,n)*gcd(r+1,n) == n
    cases += 1
assert (cases, queries) == (393, 1629)

n = 101*103
near_counts = []
for frequency in (1, 213):
    assert gcd(frequency, n) == 1
    for c in (1, 2, 4, 8, 16, 32):
        residues = [frequency*(x*x-c*c) % n for x in range(1, n//4+1)]
        assert residues.count(0) in (1, 2)
        near_counts.append(sum(4*min(z,n-z) < n for z in residues))
assert min(near_counts) == 1266

recovered = trivial = 0
for n in range(3, 300, 2):
    b = n.bit_length()
    for u in range(1, min(n, 25)):
        if gcd(n, u) != 1:
            continue
        g = pow(u, 1 << b, n)
        if g == 1:
            trivial += 1
            continue
        logs = {1: 0}
        y = g
        while y not in logs:
            logs[y] = len(logs)
            y = y*g % n
        y, digits = g, 0
        for j in range(2*b):
            y = y*y % n
            digits = 2*digits + (logs[y] & 1)
        r = (1 << (2*b)) // digits
        assert r == len(logs) and pow(u, r << b, n) == 1
        recovered += 1
assert (recovered, trivial) == (2479, 369)
print(tails, cases, queries, recovered, trivial)
PY
~~~

The PARI/GP command bisects with the actual floor sums and checks the recovered root and proper gcd on four inputs. It covers the terminal interval with translated calls of radius $\lfloor\sqrt n/4\rfloor$ to keep each lattice small.

~~~sh
gp -fq <<'GP'
tail(n,h) = { my(a=9*n\4, q=a*n+1); sum(t=h+1,2*n-h-1,a*t^2\q)%2 };
split(n) = {
  my(lo=2, hi=n\2, leftbit=1, mid, bit, w=max(1,sqrtint(n)\4), c, root, d);
  while(hi-lo > 2*sqrtint(n),
    mid=(lo+hi)\2; bit=tail(n,mid);
    if(leftbit!=bit, hi=mid, lo=mid+1; leftbit=bit));
  forstep(start=lo,hi,2*w+1,
    c=start+w;
    foreach(zncoppersmith((x+c)^2-1,n,w), z,
      root=c+z;
      if(start<=root && root<=hi && root^2%n==1,
        d=gcd(root-1,n); if(1<d && d<n, return([root,d])))));
  error("no proper split for ",n);
};
inputs=[105,315,1155,1022117];
got=apply(split,inputs);
if(got!=[[41,5],[134,7],[274,21],[510553,1013]],error("unexpected splits",got));
print(got)
GP
~~~
