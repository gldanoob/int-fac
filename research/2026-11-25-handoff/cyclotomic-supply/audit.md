# Order multiples computed from the input

## Large overlap between the two cyclotomic values

Fix $k\ge3$, set $d=\varphi(k)$, and take $N=pq$ for distinct primes with $1/2\le p/q\le2$. Write $L=\log N$. Suppose
$$
\gcd(\Phi_k(p),\Phi_k(q))\ \ge N^{d/2}/B,\qquad B\ge1.
$$
Then deterministic factoring from $N$ takes $O_k(B^{1/d}(\log N)^{C_k})$ bit operations. The cutoff $B$ can be known as part of the public promise, or tried at powers of two.

Strip every prime dividing $k$ from the overlap, losing a factor at most $k$. For $k\ge3$ the valuation at any such prime in a nonzero cyclotomic value is at most one. Indeed for $k=\ell^a k_0$ with $\ell\nmid k_0$, a root modulo $\ell$ requires order $k_0$. For odd $\ell$, the difference of the valuations at the powers $\ell^a k_0$ and $\ell^{a-1}k_0$ is one by lifting the exponent, and $\Phi_k$ divides their cyclotomic quotient. For $\ell=2$ a root requires $k_0=1$, and $t^{2^{a-1}}+1\equiv2\bmod8$ for odd $t$ and $a\ge2$.

For each remaining prime power $\ell^a$ in the overlap, $p$ and $q$ both have exact order $k$ modulo $\ell^a$. Their order already equals $k$ modulo $\ell$ by squarefreeness of $T^k-1$ there, and it divides $k$ modulo $\ell^a$. Such an $\ell$ is odd, since $k\ge3$ cannot divide $2-1$. In the cyclic unit group there is a unique class $j\in(\mathbb Z/k\mathbb Z)^\times$ with $q=p^j\bmod\ell^a$. Gather the prime powers into $d$ pairwise coprime divisors $D_j$. Each is also coprime to $p$.

For each $j$ put $m_j=k/\gcd(k,j+1)$ and $d_j=\varphi(m_j)$, including $\varphi(1)=1$. The integer ring of $\mathbb Q(\zeta_k^{j+1})$ is $\mathbb Z[\zeta_k^{j+1}]$. Consequently the coefficients of the minimal polynomial of $\zeta_k$ over this subfield can be lifted to integer polynomials in $U$. Let $Q_j(U,T)$ denote the resulting monic polynomial of degree $e_j=d/d_j$ in $T$. Then $\Phi_k(T)$ divides $Q_j(T^{j+1},T)$ and $\Phi_{m_j}(T^{j+1})$ in $\mathbb Z[T]$. Modulo $D_j$, $N=pq\equiv p^{j+1}$, proving
$$
D_j\mid Q_j(N,p),\qquad D_j\mid M_j:=\Phi_{m_j}(N).
$$
These public polynomials depend only on $k$. One can compute each as a product of the conjugate linear polynomials over the fixed cyclotomic subfield, then express its coefficients in the integral power basis. The order of repeated public moduli is immaterial because the hidden divisors are pairwise coprime.

Guess dyadic lower bounds $A_j\le D_j<2A_j$ and a bin $P\le p<2P$, using the public row $(T,N,P)$ as well. There are only $(\log N)^{O_k(1)}$ choices. The simultaneous univariate lattice theorem gives constant-factor radius with logarithm at least
$$
\frac{(\log P)^2}{L}+
 \sum_{j}\frac{(\log A_j)^2}{e_j\log M_j}.
$$
Here $\log P=L/2+O(1)$, every $e_j\log M_j=dL+O_k(1)$, and the sum of $\log A_j$ is at least $dL/2-\log B-O_k(1)$. Cauchy–Schwarz bounds the radius logarithm from below by
$$
L/4+\frac{(dL/2-\log B)_+^2}{d^2L}-O_k(1)
 \ \ge\ L/2-\frac{\log B}{d}-O_k(1).
$$
Subdivide the balanced factor interval into that many guaranteed-radius windows and verify candidates by division. The window radius can be computed using rational lower bounds for each logarithm, with error $O_k(1)$ in the displayed exponent and polynomial bit cost. Where the radius is below one, test individual integers. Failed cutoff guesses can be tried before a final fallback, so returned factors are always verifiable. This proof does not assert the existence of infinitely many balanced prime pairs with a given small deficit.

For $k=3$, the construction is explicit. After stripping 3, split the overlap into $D_+\mid q-p$ and $D_-\mid q+p+1$. The three monic rows are $(T,N)$, $(T+N+1,\Phi_3(N))$, and $(\Phi_3(T),N-1)$. For $k=4$ use the two extra rows $(\Phi_4(T),N+1)$ and $(\Phi_4(T),N-1)$, with $D_+\mid q-p$ and $D_-\mid q+p$. For $k=6$ use $(T-N-1,\Phi_3(N))$ and $(\Phi_6(T),N-1)$, with $D_+\mid q-p$ and $D_-\mid q+p-1$.

## A complementary arithmetic progression

Suppose $N=pq$, $b=1+\lfloor\log_2 N\rfloor$, and $\Phi_k(p)^r\mid q-a$ with public integers $k\ge3,r\ge1,a\ge1$, $k,r\le b^{O(1)}$, and $a\le N b^{O(1)}$ with $N\nmid a$. Put $d=\varphi(k)$, $s=rd+1$. There is an unconditional deterministic algorithm with bit cost $N^{1/(4s)}\operatorname{poly}(b,k,r)$. It suffices to schedule polynomially many candidate $k,r,a$. A proper $\gcd(a,N)$ already gives a factor; assume $\gcd(a,N)=1$.

Take $F(U,V)=V^d\Phi_k(U/V)$ and public $M=NF(N,a)^r$. Since $N\equiv ap\bmod\Phi_k(p)^r$, already $F(N,a)\equiv a^d\Phi_k(p)\bmod\Phi_k(p)$. Therefore $D=p\Phi_k(p)^r$ divides $M$ as well as $N-ap$. The highest $U$-coefficient of $F$ is one, so $\gcd(a,F(N,a))=1$; $N-ap$ can be made monic modulo $M$. With $2^i\le p<2^{i+1}$,
$$
D\ge(2^{i-1})^s,\qquad \log_2 M\le s(b+O(\log b)).
$$
Use the monic linear unknown-divisor bound at $M$, subdividing the bin into windows with radius $2^{s(i-1)^2/(b+O(\log b))-O(1)}$, capped at the bin length. For a sufficiently large positive constant in the denominator the count is bounded by
$$
\operatorname{poly}(b)\max_i 2^{\,i-s(i-1)^2/(b+O(\log b))}
\le \operatorname{poly}(b) N^{1/(4s)}.
$$
All arithmetic has polynomial bit size; in particular the modulus has $O(s(b+\log b))$ bits. The bound can use exact integer comparisons against the bit length of $M$. When $a$ is fixed, a weaker bound comes from trial to $p\ll N^{1/s}$, using product trees. The promised algorithm is useful even if the quotient $(q-a)/\Phi_k(p)^r$ is too large to enumerate. For growing $s$, this yields a stronger exponent than the trial range alone, but the family itself then has a correspondingly smaller factor.

## Scheduled algebraic powers do not generically give full order multiples

Fix $\epsilon>0$. For each balanced size $X$, schedule integer multipliers $1\le a_i\le G$, powers $\alpha_i\in[\epsilon,1-\epsilon]$, and nonzero $F_i(U,Y)\in\mathbb Z[U,Y]$. All of $G,K,Y_0$ and the sum $D$ of one plus degree plus log absolute content for the polynomials are $X^{o(1)}$. Consider the exponents $E_i(N)=F_i(N,\lfloor(a_iN)^{\alpha_i}\rfloor)$. Then for a cutoff $Z\ge Y_0$ with $Z=X^{o(1)}$, on a fraction tending to one of balanced prime pairs, every prime $\ell>Z$ dividing any $\Phi_k(t)$, $k\le K$, $t\in\{p,q\}$, is coprime to every $E_i(N)$. On these good pairs the maximum relative log gcd tends to zero, by the established second-moment smooth-part estimate. This includes fixed rational powers above and below $1/2$. The bound permits very large non-content polynomial coefficients. The floor curve is analyzed independently of its evaluation complexity.

Here is the congruence count needed in place of the square-root slope injectivity argument. Set $Q\ge2$, $H=Q^2$, and $\ell>Q^4$, with $Q=X^{o(1)}$. Fix $p,a,\alpha$ in the above ranges and put $g(v)=(apv)^\alpha$, $S=a^\alpha X^{2\alpha-1}$. On $X<v\le2X$, $g'\asymp_\epsilon S$, $-g''\asymp_\epsilon S/X$, and $X^{-1+2\epsilon}\le S\le X^{1-2\epsilon+o(1)}$. Suppose $F(pV,Y)$ is nonzero modulo $\ell$, where $F$ has total degree $r\ge1$.

If $S\le Q^{-1/2}$, there are $O_\epsilon(1+XS)$ occupied integer levels of $\lfloor g(v)\rfloor$; every level is an interval of $O_\epsilon(1+1/S)$ integers. For at most $r$ residue classes of the level, the specialization in $V$ is the zero polynomial modulo $\ell$. The integers in their levels number $O_\epsilon(r((1+XS)/\ell+1)(1+1/S))$. At other levels, the univariate root bound and disjoint intervals give in total $O_\epsilon(r(X/\ell+1+XS))$. Both totals are $O_\epsilon(rX/\sqrt Q)$.

If $S>Q^{-1/2}$, divide integer $v$ into blocks of length $H$. At each start $s_0$ choose a reduced rational $u/d$ with $1\le d\le Q$ and $|g'(s_0)-u/d|\le1/(dQ)$. The integers $d\lfloor g(v)\rfloor-uv$ within that block range over $O_\epsilon(d+H/Q+d S H^2/X)=O_\epsilon(Q)$ values by Taylor. Each value describes a line modulo $\ell$. Unless the slope reduces to one of at most $r$ nonvertical line-factor slopes of $F(pV,Y)$, a line accounts for at most $r$ congruence hits in the block, since $H<\ell$. The contribution from such ordinary blocks is $O_\epsilon(r X/Q)$.

For one exceptional slope modulo $\ell$, and each denominator $d$, the candidate numerators are in one residue class modulo $\ell$, within an interval of length $O_\epsilon(dS+1)$. There are $O_\epsilon(dS/\ell+1)$ candidates. Each slope's derivative tolerance restricts its block starts to an interval of length $O_\epsilon(X/(SdQ))$ since the derivative is monotone with $|g''|\gg_\epsilon S/X$. The total number of integers in the union of exceptional blocks is bounded by $r$ times
$$
O_\epsilon\!\left(\sum_{d\le Q}(dS/\ell+1)(X/(SdQ)+H)\right)
 =O_\epsilon(X/\ell+X\log(2Q)/(SQ)+HQ^2 S/\ell+HQ).
$$
This is $O_\epsilon(X\log(2Q)/\sqrt Q)$, accounting for collisions between genuinely different rational slopes that reduce to the same slope modulo $\ell$.

Take $b=1+\log X$, $Q=\lceil((D+1)(K+1)^2 b^4)^4\rceil$ and $Z=\max(Y_0,Q^4)$. Remove exceptional primes dividing polynomial contents as in the ordinary polynomial schedule. After fixing $p$, the product of cyclotomic values has $O(K^2 b)$ distinct prime factors, all coprime to $p$, so the preceding bound followed by the prime number theorem costs $O_\epsilon(DK^2 b^2\log(2Q)/\sqrt Q)=o(1)$ over the whole menu. Swap $p,q$ and discard the diagonal. The square-root argument's established smooth-part bound at $Z=X^{o(1)}$ finishes the proof. For fixed indices and polynomial-in-$b$ parameters the same estimate gives log gcd at most $(\log b)^2$ on density one.

Run the exact small arithmetic replays with `gp -fq supply.gp` and `python graph.py`. The latter uses floor and tangent comparisons entirely in integers and exercises modular slope aliases alongside long constant floor levels.
