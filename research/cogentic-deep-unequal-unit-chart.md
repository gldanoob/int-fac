# A fixed unequal-power chart splits five ninths of balanced pairs at unrestricted depth

Use base $3$ and exponents $(i,k)=(1,-2)$ in the [unit chart](cogentic-unit-corrected-family.md). Among unordered distinct primes $p,q\in[Y,2Y]$, the proportion for which some repeated-squaring depth gives a proper gcd tends to $5/9$. If only depths through $\exp(\log Y/(300\log\log Y))$ are tried, the proportion tends to zero. Both statements are unconditional.

## The two signed collisions

Write $t=3^{2^j}\bmod N$ and $C=(t-1)/(t+1)$. Since $A=tC$ and $B=C/t$, the ratio is $-tAB^2=-C^3$. Where the chart is eligible, its signed gcds are the gcds of $t^2+3$ and $3t^2+1$, respectively. This follows from
\[
 C^3+1=\frac{2t(t^2+3)}{(t+1)^3},\qquad
 C^3-1=-\frac{2(3t^2+1)}{(t+1)^3}.
\]

At a prime $r>3$, write $\operatorname{ord}_r(3)=2^{h_r}m_r$ with $m_r$ odd. The two congruences are precisely $3^{2^{j+1}-1}=-1$ and $3^{2^{j+1}+1}=-1$. Either odd exponent can give $-1$ only when $h_r=1$. In that case the tests are $2^{j+1}=1$ and $2^{j+1}=-1$ modulo $m_r$, respectively. For $m_r>1$ put
\[
 d_r=\operatorname{ord}_{(\mathbf Z/m_r\mathbf Z)^\times/\{1,-1\}}(2).
\]
Either sign hits exactly at depths with $d_r\mid j+1$. When $m_r>1$, the order of $t$ is divisible by $m_r$ at every depth, so $t$ cannot be $1$, $-1$, or a square root of $-1$. The chart is therefore eligible throughout.

If just one factor has $h_r=1$, any depth with $d_r\mid j+1$ at that factor gives a divisor. If both factors have $h_r=1$ and $d_p\ne d_q$, take $j+1=\min(d_p,d_q)$. Both witnesses have $j+1\le 2Y$. With equal periods $d$, a split exists exactly when the signs of $2^d\bmod m_p$ and $2^d\bmod m_q$ differ. For example, at $271$ and $307$, the orders of $3$ are $30$ and $34$. Taking $j=3$ gives $2^{j+1}=1\pmod {15}$ and $2^{j+1}=-1\pmod {17}$, so the two signed gcds give the two factors.

## The density of the unrestricted search

The set of primes with $h_r=1$ has density $1/3$. On the layer $s=v_2(r-1)\ge1$, this condition says that $3$ is a $2^{s-1}$-th power and fails to be a $2^s$-th power. For $r\equiv1\pmod {2^b}$ and $a\le b$, the $2^a$-th power condition means complete splitting in $\mathbf Q(\zeta_{2^b},3^{1/2^a})$. Its degree is $2^{b-1+a}$ for $b\ge1$, by Eisenstein at a prime over $3$ in the cyclotomic field. Inclusion and exclusion over $a=s-1,s$ and $b=s,s+1$ gives layer density $4^{-s}$ by Chebotarev. The omitted layers $s\ge S$ lie in $1\pmod {2^S}$, so their upper density tends to zero. These natural densities hold also on $[Y,2Y]$ by subtracting the prime counts up to $Y$ from those up to $2Y$. [Moree on densities of divisibility of multiplicative orders](https://arxiv.org/abs/math/0407421)

To see that the periods coincide on only $o(1)$ of pairs, set $L=\log Y$, $W=\exp(L/(100\log L))$, and $Z=L^6$. Almost all $r\in[Y,2Y]$ have $m_r>Y^{1/3}$. Indeed, primes with $2^{h_r}>Y^{1/12}$ lie in a single class modulo a power of two greater than $Y^{1/12}$. Every remaining prime with $m_r\le Y^{1/3}$ divides some $3^{2^h n}-1$ with $2^h\le Y^{1/12}$ and $1\le n\le Y^{1/3}$. The sum of the logs of these integers is $O(Y^{3/4})$.

Almost all those $m_r$ have a prime divisor $\ell>W$. For $V\ge3$ and $U\ge1$, the reciprocal sum over $V$-smooth integers $d\ge U$ is
\[
 \sum_d\frac1d\le U^{-1/\log V}
 \prod_{\ell\le V}\left(1-\ell^{-1+1/\log V}\right)^{-1}
 \ll U^{-1/\log V}(\log V)^e,
\]
with the implied constant taken uniformly for large $V$. The product bound follows by taking logs, using $\ell^{1/\log V}\le e$ and the reciprocal prime sum. Apply the estimate with $V=W$, $U=Y^{1/3}$. Each $d\mid r-1$ occurs for at most $2Y/d$ integers $r\in[Y,2Y]$. The resulting bound is $o(Y/\log Y)$, so almost all $r-1$ have $W$-smooth part less than $Y^{1/3}$.

For almost all $r$, any prime $\ell>W$ dividing $r-1$ has both $\operatorname{ord}_\ell(2)>\ell^{1/3}$ and $Z$-smooth part of $\ell-1$ less than $\ell^{1/3}$. In a dyadic interval $[B,2B]$, the first exception divides the product of $2^n-1$ for $1\le n\le(2B)^{1/3}$, so it has reciprocal sum $O(B^{-1/3}/\log B)$. The second has reciprocal sum $O((\log Z)^e B^{-1/(3\log Z)})$ by the smooth-divisor estimate. Summing across $W<\ell\le2Y$ gives $o(1/\log Y)$ in total. Counting the integer multiples in $r-1$ again gives $o(Y/\log Y)$ exceptions.

For such an $r$, take a prime $\ell>W$ dividing $m_r$. The order of $2$ modulo $\ell$ has a prime divisor $v>Z$ and divides $2d_r$, so $v\mid d_r$. Also $d_r\mid\varphi(m_r)\mid\varphi(r-1)$. If $d_p=d_q$ for two such primes, some $v>Z$ divides both $\varphi(p-1)$ and $\varphi(q-1)$. For a fixed $v$, the condition $v\mid\varphi(r-1)$ implies $v^2\mid r-1$ or $u\mid r-1$ for some prime $u\equiv1\pmod v$. Counting integers in these classes gives $O(Y\log Y/v)$ possibilities for $r$, since $\sum_{k\le2Y/v}1/(kv+1)\ll\log Y/v$. The proportion of prime pairs sharing any such $v$ is therefore $O(L^4/Z)=o(1)$.

Outside the exceptional primes and pairs accounted for above, a split exists exactly when at least one factor has $h_r=1$. This gives $1-(1-1/3)^2=5/9$.

## Testing a depth cutoff

Take any $D\le W^{1/3}$. For a prime $r$ with a divisor $\ell>W$ of $m_r$, a collision at depth $j\le D$ forces $\ell\mid 2^{j+1}-1$ or $\ell\mid 2^{j+1}+1$. The product of these positive integers for $0\le j\le D$ has log size $O((D+1)^2)$. Each of its distinct prime divisors $\ell>W$ therefore costs at least $\log W$, and at most $2Y/W$ integers $r$ have that divisor in $r-1$. The proportion of primes reached is $O((D+1)^2\log Y/(W\log W))=o(1)$, in addition to the $o(1)$ already excluded. This applies even if the algorithm chooses the depth adaptively within the cutoff. The argument and the $5/9$ density concern this fixed base and exponent pair. A density estimate uniform over the other unequal-power charts remains open here.
