# Hasse order windows from a public factor-gap bound

For distinct odd primes \(p<q\) with \(N=pq\), suppose a public bound \(D\) satisfies \(q-p\le D\). A shifted baby-step–giant-step search covers the Hasse order range with soft \(O(\sqrt{1+D+N^{1/4}})\) work, where soft notation here also allows polynomial factors in \(\log N\). A direct divisor-window search is at least as fast under the same information. A known large cofactor of the curve order changes the comparison. Merely dividing the Hasse window by each possible cofactor in a whole dyadic shell does not in general shorten the union enough to help. [Shifted order searches](cogentic-torus-shifted-windows.md)

## Full Hasse coverage and the direct factor window

Put \(s=\sqrt N\). Since \(q-p\le D\), one has \(s-D\le p\le s\le q\le s+D\). Every curve of good reduction at \(p\) therefore has
\[
    n_p=\#E(\mathbb F_p)\in
     [s-D+1-2\sqrt s,\ s+1+2\sqrt s].
\]
For an integer interval of positive indices of length \(W\), write every index as a difference of a baby index \(0\le i<b\) and a giant index with step \(b=\lceil\sqrt W\rceil\), allowing a bounded final padding. The corresponding elliptic lists have total length \(O(\sqrt W)\). Checked group operations and monic product trees recover a proper gcd or a verified global annihilator if a point has a local hit. A full abscissa match checks both ordinates to distinguish equality and inversion. For a menu covering a point whose local two-heights differ, any verified global annihilator suffices after taking its odd part and running the doubling chain. The local hit at \(n_p\) itself is guaranteed without smoothness. The interval radius from Hasse is still of order \(N^{1/4}\) even when the factor-gap bound is much smaller. [Elliptic collision and annihilator checks](cogentic-moving-elliptic-separation.md) · [Unequal two-heights in the fixed Gaussian twists](cogentic-cm-linear-forms.md)

The input already places \(p\) in the interval of integers in \([s-D,s]\). Truncate its lower endpoint at 2 if needed. For this interval of length \(D+O(1)\), the monic polynomial
\[
                         \prod_{i=0}^{b-1}(X+i),
                \qquad b=\lceil\sqrt{D+1}\rceil ,
\]
evaluated at block starts, gives a direct factor search in soft \(O(\sqrt{D+1})\) work. A proper gcd of a block product splits immediately. If the gcd is \(N\), scan that block, truncated if necessary to lie below \(N\); at least one member has a proper gcd. Thus the unpadded Hasse window gives no faster deterministic coverage from this gap promise. [Hittmeir, §3, shifted Strassen product-tree search](https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf)

There is an even shorter multiplicative order window for \(p,q\) close. Write \(S=p+q\); then
\[
 0<S-2s=\frac{(q-p)^2}{S+2s}\le \frac{D^2}{4s},\qquad
                    \varphi(N)=N+1-S .
\]
The ordinary Fermat search costs \(O(1+D^2/s)\) square tests. With the separating multiplicative unit already supplied by the [power-order construction](cogentic-separating-power-order-units.md), apply the same shifted search to its powers in the interval for \(\varphi(N)\). Any local hit gives a proper gcd or an annihilator whose odd part and doubling chain split the two primes. This costs soft \(O(1+D/N^{1/4})\) at the same Dirichlet RH input as the separating menu. Thus for an \(\exp(O(H))\) budget it handles \(D\le N^{1/4}\exp(O(H))\), whereas plain Hasse coverage has a polynomial floor \(N^{1/8}\). The cancellation of the first-order gap comes from the classical multiplicative relation \(u^{p+q}=u^{N+1}\bmod N\), which Hittmeir uses in the Lawrence–Lehman setting. It does not use an elliptic trace. On a trace-zero twist at both primes the corresponding product \((p+1)(q+1)=N+1+S\) has the same width. [Hittmeir, §§1 and 4](https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf)

## What cofactor information would help

Suppose the curve order is \(n_p=mr\), with a known positive cofactor \(m\). After replacing \(P\) by \([m]P\), the residual order divides \(r\). A window \([X-W,X+W]\) for \(n_p\) gives an interval for \(r\) of length \(O(1+W/m)\), regardless of whether \(r\) is prime. A local hit in that interval likewise certifies a multiplier after reinstating \(m\). From the balanced-factor Hasse window this search is within the one-third budget when
\[
                 m\ \ge\ (D+N^{1/4})\exp(-O(H)).
\]
For a known menu \(\mathcal M\) of cofactor candidates one can first power by their lcm, sharing one baby list among the resulting intervals. This costs, up to logarithmic factors in the description,
\[
            O\!\left(|\mathcal M|+
                       \sqrt{\sum_{m\in\mathcal M}(1+W/m)}\right).
\]
The additive term accounts for the shifted giant-list starts and the lcm description. This is a conditional gain for a sparse menu of sufficiently large cofactors. The rational two-torsion and a public smooth multiplier in the present curve families do not identify such a cofactor.

For example, at scale \(D\asymp N^{3/8}\), a known \(m\asymp N^{1/4}\) at a separating curve gives residual-window work of order \(N^{1/16}\), compared with \(N^{1/8}\) for the multiplicative sum window. This comparison uses the added order-divisibility information. A gap estimate alone gives neither that divisor nor its size.

For a whole dyadic cofactor shell, put
\[
 I_m=[(X-W)/m,(X+W)/m],\qquad M\le m\le 2M .
\]
If \(4MW<X-W\), then \(I_m,I_{m+1}\) are disjoint, since \(2mW<X-W\) implies \((X+W)/(m+1)<(X-W)/m\). When also \(M\le cW\) for a sufficiently small absolute \(c\), each interval has \(\gg W/M\) integers. Their union has \(\gg W\) integers, even though each separate interval was shortened by a factor of order \(M\). In the narrow-gap Hasse regime \(W\asymp\sqrt X\), this applies throughout the shells up to a small constant times \(\sqrt X\). Once \(M\gg X/W\), the residual index is itself \(O(W)\), which the existing bounded residual search already covers in soft \(O(\sqrt W)\) work. This is a limit of covering candidates using only the public size windows. It leaves open sparsity from additional arithmetic information on the particular order or its smooth part. [Bounded residual orders](cogentic-elliptic-residual-order.md)

## Batched weighted gap windows

For a prime $p\mid N$, write $Q=N/p$, allowing composite $Q$. A public triple $(a,b,D)$ covering $|aQ-bp|\le D$ gives an integer $s=aQ+bp$ with $4abN\le s^2\le4abN+D^2$. The corresponding interval for $e=aN+b-s$ contains $(p-1)(aQ-b)$. Every unit raised to that exponent equals one modulo $p$. This is the weighted Lawrence–Lehman search. [Hittmeir](https://arxiv.org/abs/2006.16729)

The [weighted-window replay](../experiments/cogentic-weighted-gap-windows.py) shares a baby table of width $h=\lceil\sqrt{\sum_i W_i}\rceil$ among the intervals of integer lengths $W_i$. Each coordinate first checks for a proper gcd between baby and giant values. If that search finds none, the covered exponent matches in every coordinate modulo $N$. With joint order at least $h$, each giant tuple matches at most one baby index. Test every such index in its window by recovering $s$ and checking both integer roots of the discriminant. On $2701$, one global match fails that test before a later window yields $37$.

To obtain joint order $h$ deterministically, try prime bases up to $S=\min(\lfloor\sqrt N\rfloor,B^4)$ for $B$ the input bit length. Divisors end the search. Keep a base when the least common multiple of the known orders increases, or use one base of order at least $h$. If all orders divide a period below $h$, then every size-$k$ product of distinct tested primes is a root of the period-th power equation modulo every prime divisor $p$ of $N$. When $\binom{\pi(S)}k$ exceeds the period, these distinct integers cannot all lie below $p$. A divisor up to $S^k$ can be found by block products and multipoint evaluation. If the tested primes already reach $\sqrt N$ the trial divisions suffice. Otherwise $S=B^4$ and for large $B$, $\pi(S)/B\ge\sqrt S$. For $h<\sqrt N$, the first qualifying $k$ is at most $B$ and minimality gives $S^{(k-1)/2}\le h$. Thus $S^k\le Sh^2$. If $h\ge\sqrt N$, search directly through $\lfloor\sqrt N\rfloor$. Up to factors polynomial in the bit lengths of the input and weights, the work is soft $O(h+K)$ for $K$ triples. Uniform one-third coverage would require producing a small enough list for every input.
