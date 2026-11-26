# Stage two with two shifted factor windows

A residual order can be covered when it divides a product of two odd integers in two specified intervals, even when both intervals are centered far above a bounded residual-order cutoff. The two-list search takes soft-linear work in the sum of the widths and a logarithmic setup in the centers. A global match gives a verified order multiple for the original base and therefore a split when that base has unequal local two-heights. Montgomery used square-index lists for the two torus methods. The Brent–Suyama extension uses higher powers, and the finite-difference recurrence constructs the lists efficiently. Here the list placement guarantees coverage of a specified rectangle of large-factor pairs. [Brent–Kruppa–Zimmermann, §8.2.4](https://members.loria.fr/PZimmermann/papers/Chap8.pdf) · [Separation with a supplied multiplier](p-plus-one-multiples.md#a-bounded-missing-multiplier)

## Difference-of-squares lists

Let $\gamma$ be a unit of norm one in a quadratic algebra over $\mathbb Z/N\mathbb Z$, étale at the primes dividing odd $N$. Let $w=\gamma^E$ for a public stage-one exponent $E$. Assume that at one prime the order of $w$ divides $uv$, where $u,v$ are odd and
\[
                 u\in[A,A+W_1],\qquad v\in[C,C+W_2].
\]
Neither factor must be prime. If only the residual odd part satisfies the promise, include a power of two that kills the two-part in $E$. This power can use the ordinary group-size bound. This permits both original two-heights to remain distinct for the final extraction on $\gamma$.

Write $i=(u+v)/2$ and $j=(v-u)/2$. Then $uv=i^2-j^2$. Put $i$ in the interval between $(A+C)/2$ and $(A+C+W_1+W_2)/2$, rounding inwards. Put $j$ in the interval between $(C-A-W_1)/2$ and $(C-A+W_2)/2$, again rounding inwards. Take absolute values for the second interval, since only its squares enter the search. Assume $W_1<2C$ and $W_2<2A$, which gives $i>|j|$ for all crossed pairs. Thus both $i^2-j^2$ and $i^2+j^2$ are nonzero. The lists may include extra pairs whose two implied factors are outside the designated windows. Any split or verified order multiple they supply is usable.

Starting from $w^{a^2}$ and $w^{2a+1}$ at one endpoint $a$, generate a consecutive list of square powers using
\[
       w^{(a+1)^2}=w^{a^2}w^{2a+1},\qquad
       w^{2(a+1)+1}=w^{2a+1}w^2 .
\]
The base powers at the endpoints cost $O(\log(2A+2C+2W_1+2W_2))$ modular multiplications. The subsequent recurrence takes two multiplications per entry. The same formula with increments $2ha+h^2$ and $2h^2$ works on a list of stride $h$. In particular, congruence restrictions putting both odd factors in known classes of a common even modulus give arithmetic-progression lists for the half-sum and half-difference.

## Local matches, global certificates and cost

Use the trace of each power as its list label. At a good prime, norm-one elements with equal trace coincide or are inverses. Therefore a trace match at a prime for a crossed pair tests exponents $i^2-j^2$ or $i^2+j^2$. The promised pair has equal group elements locally. A proper gcd of a trace difference splits immediately. If the traces are equal modulo $N$, take gcds of the coordinate differences between the two powers and between the first power and the conjugate of the second. Each prime dividing $N$ occurs in at least one of these gcds. Either one is proper, or at least one is $N$ and gives a nonzero verified multiplier for $w$. This check also works for prime powers: a partial valuation can already provide a proper gcd, and gcd $N$ verifies the claimed equality on the full modulus.

If a right trace occurs twice, apply the same checked comparison before keeping a representative or returning its successful certificate. The right indices can be chosen nonnegative and distinct, so such a certificate also has nonzero exponent. A global certificate $K$ for $w$ gives the verified multiplier $EK$ of $\gamma$. Starting at the odd part of that multiplier and squaring separates any pair whose original two-heights differ. For searches requiring only a proper divisor or an order multiple, a global certificate already meets the contract. If a global certificate fails to split and an exhaustive local search is wanted, keep one representative for each checked right trace. A checked global coincidence is a literal equality up to inversion. On a left row with an exact trace match, use the derivative of the deduplicated right product to remove the exact factor. Every remaining nonunit evaluation yields a proper gcd by locating a nonzero trace difference. The same product-tree descent works when a product gcd is $N$. [Monic collision trees and saturated buckets](cogentic-unit-collision-search.md#exact-product-buckets-with-global-hits-removed)

The resulting work is soft-linear in $W_1+W_2+1$ and logarithmic in the two centers, up to the cost of stage one and polynomial factors in $\log N$. For a single window of exponent multiples near a large target, the ordinary additive giant and baby lists already give square-root width, using consecutive blocks in the shifted window. Several windows can share the same baby list. If their total length is $W$ and their number is $J$, choose width $\asymp\sqrt W$ and use $O(\sqrt W+J)$ giant steps, padding each final block where an extra exponent is harmless. Only the starting giant of each interval needs binary powering in its center. A shifted first hit certifies a multiple. When two successive exact global identity hits are recovered in one contiguous interval, their difference is the exact global order. A trace equality alone needs the signed verification above. [Prior shifted interval](round-2.md#constructing-the-upstream-deep-root-from-a-shifted-order-interval) · [Prior prefix test](p-plus-one-multiples.md#a-bounded-missing-multiplier)

The two-factor linear width is consistent with a capacity bound on separated-list methods. Suppose two disjoint prime catalogues have $m_1,m_2$ candidates, each at least $P$. A nonzero tested exponent of absolute size at most $P^C$ is divisible by at most $C$ distinct candidate primes, so it covers at most $O(C^2)$ residual products from the two catalogues. A pair of trace probes gives at most two exponents. Covering all $m_1m_2$ products by such probes needs list lengths whose sum is $\Omega(\sqrt{m_1m_2}/C)$. This is a coverage bound on the stated separated representation. When the two catalogues have comparable cardinalities close to their interval widths up to logarithms, a square root of the sum of widths is too small in this model.

## A source of promised local orders

For the fixed Gaussian ratio $\gamma=(2+i)/(2-i)$ and any odd $r=uv>30$, the Lucas number $((2+i)^r-(2-i)^r)/(2i)$ has a primitive prime divisor $p$ by Bilu–Hanrot–Voutier. The Lucas parameters are $4,5$ and the conjugate ratio is nontorsion. The primitive divisor is away from $2,5$, and at it the order of $\gamma$ is exactly $r$. In particular $p\ge r-1$. Choose $q\in(p,2p]$ with $q\equiv3\pmod{40}$. The fixed Gaussian character calculation makes the two-height of $\gamma$ equal two at $q$, whereas it is zero at $p$. For $w=\gamma^4$, excluding $q$ with order at most $D$ costs at most $O(D^2/\log p)$ primes. Each such $q$ divides the product of the norms of $(2+i)^{4j}-(2-i)^{4j}$ over $1\le j\le D$, whose log size is $O(D^2)$. Thus for $D=o(\sqrt r)$ the ordinary prime theorem in this progression supplies a balanced partner with both residual orders beyond $D$. This constructs examples for any supplied windows containing the factors $u,v$. The windows are part of the promise. [Bilu–Hanrot–Voutier, primitive divisors](https://oskar-bordeaux.fr/handle/20.500.12278/166397) · [Gaussian norm-one order comparison](cogentic-cm-torus.md#which-prime-bases-split-the-input)

## Exact local and global examples

In both cases use $\gamma=(3+4i)/5$.

- For $N=10917580628039872667017=80138044891\cdot136234676587$, use $E=4$, $u=100129$ and $v=200087$. Search $u$ in $[100000,100130]$ and $v$ in $[200000,200130]$. The pair $i=150108,j=49979$ gives an equality of powers modulo $80138044891$ and a proper trace gcd.
- For $N=57702000070454398675817=80070802051\cdot720637218467$, use $E=36$ and the intervals $[100000,100010]$, $[200166,200180]$. Here $u=100003,v=200171$ and $i=150087,j=50084$. The match is global. The multiplier $36uv$ is verified for $\gamma$, and the gcd chain starting at its odd part gives $80070802051$.

Run `python3 -B experiments/cogentic-torus-shifted-windows.py` in the repository's Sage-enabled Python environment. The replay uses the existing torus arithmetic and monic collision backend. [Exact replay](../experiments/cogentic-torus-shifted-windows.py)

The two interval endpoints are public inputs to the Gaussian search. For example, the following run uses the modulus and the intervals above.

~~~sh
python3 -B experiments/cogentic-torus-shifted-windows.py 57702000070454398675817 --exponent 36 --first 100000 100010 --second 200166 200180
~~~
