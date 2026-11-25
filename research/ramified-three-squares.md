# Factoring from one designated bit of a three-square count

Let $C(m)$ count ordered triples of positive integers with square sum $m$, for $m\equiv3\pmod8$. Fix a rational $0<\alpha<1/2$. From the **one binary digit** of $C(m)$ at position $\lfloor\alpha\log_2m\rfloor$, with the units digit in position zero, an unconditional deterministic algorithm recovers the complete factorization of a $b$-bit integer. The index itself specifies the digit. The arithmetic outside the oracle costs $2^{O(b/\log(2b))}$. All queried indices have $O_\alpha(b)$ bits, and there are $\exp(O(\log^2(2b)))$ queries for fixed $\alpha$. A bound $2^{O(b/(\log b)^{1/2+\epsilon})}$ for this digit would therefore improve the all-input benchmark for any fixed $0<\epsilon\le1/2$.

Two ingredients give the reduction. Split-prime padding recovers the entire count using one designated digit from each padded index. Ramifying the odd-valuation prime factors of the factoring input then gives a recursion through smaller class numbers and divisor sums. For a squarefree semiprime two exact counts already suffice with polynomial overhead. With one exact count there is also an unconditional polynomial **average** bit cost over uniform integers of each bit length. Computing the digit or exact count from an unrestricted index remains the outstanding operation.

## Counts under multiplication by split primes

Write $m=d f^2$ with $d$ positive and squarefree. Then $d\equiv3\pmod8$ and $-d$ is fundamental. Gauss's three-square identity gives $C(m)=3H(m)$, including $C(3)=1$. Indeed all coordinates are odd, so each positive triple has eight signed copies. The Hurwitz product formula gives

$$
C(m)=C(d)\prod_{p^h\parallel f}L_h(p,1-(-d/p)),\qquad
L_h(p,c)=p^h+c(1+p+\cdots+p^{h-1}).
$$

In particular $C(ms^2)=sC(m)$ whenever every prime of the odd integer $s$ is coprime to $m$ and splits for $-d$. For any positive even $y$, the integer $s=1+my^2$ has this property. Each prime $p\mid s$ is odd, avoids $my$, and satisfies $-m\equiv(y^{-1})^2\pmod p$. This constructs the multiplier without its factorization. [Chen–Garvan, §2, formula (2.1)](https://arxiv.org/pdf/2010.14315#page=5)

## Recovering all digits from one index-determined digit

Put $b=\lfloor\log_2m\rfloor+1$. Since each positive pair $(x,y)$ determines at most one positive $z$, $C(m)\le m<2^b$. Recover the $b$ low bits of $mC(m)$, then multiply by the inverse of the odd integer $m$ modulo $2^b$. For bit $i$, choose $k\equiv i\pmod2$ with $k-i\ge b$. For a positive $z\equiv1\pmod{2^{i+1}}$, set

$$
y=2^{(k-i)/2}z,\qquad s=1+my^2,\qquad M=ms^2.
$$

Modulo $2^{k+1}$ the count $C(M)$ equals $C(m)+2^{k-i}mC(m)$. The first summand lies below $2^{k-i}$, so bit $k$ of $C(M)$ is precisely bit $i$ of $mC(m)$.

To put $k$ at the designated position, set $L=\lceil k/\alpha\rceil$ and require $2^L\le M<2^{L+1}$. This interval implies $\lfloor\alpha\log_2 M\rfloor=k$ because $2\alpha<1$. Choose $k=O_\alpha(b)$ of the specified parity sufficiently large that $k/\alpha>2k+7b+32$ and $k-i\ge b$. For $1\le z\le 1+16\cdot2^{i+1}$ we have $M<2^{2k+7b+32}$. Find the first $z$ on the progression $1+2^{i+1}t$ for which $M\ge2^L$ by doubling and binary search on $t$. At this crossing successive $z$ values differ by a factor at most $17/16$. Successive $M$ values therefore differ by a factor at most $(17/16)^4<2$, placing the first hit in the required interval. All computations use integers of $O_\alpha(b)$ bits. There are $b$ nonadaptive bit queries, which can all be prepared before seeing any answers. The replay starts with the smallest eligible $k$ and increments by two when the first hit crosses the upper endpoint.

For example, at $m=3$, $\alpha=2/5$, the queries for bits zero and one of $mC(m)$ are $1{,}774{,}083$ and $507$. Their multipliers are $769$ and $13$. The counts at these indices are $769$ and $13$, so positions eight and three each return one. Thus $mC(m)\equiv3\pmod4$ and $C(3)=1$.

## Extracting repeated prime factors

At any recursive call strip $2,3,5,7$ to full multiplicity, keeping the factors. Return immediately on a prime or on one. For the remaining $n$, let $a$ be the representative of $3n\bmod8$ in $\{1,3,5,7\}$. It is squarefree, coprime to $n$, and $an\equiv3\pmod8$. Query $C_0=C(an)$ and factor $C_0$ by the same algorithm.

This call shrinks the bit length by a constant factor once $n$ is sufficiently large. For each $x\le\sqrt m$, the number of representations of $m-x^2>0$ by two squares is at most $4\tau(m-x^2)$, by the two-square divisor formula. The divisor bound gives $C(m)\le m^{1/2+o(1)}$. Use trial division to finish $n$ whenever $C_0^4\ge n^3$. This branch occurs on only finitely many $n$. [Two-square divisor formula](https://dlmf.nist.gov/27.13#iv) · [Ramanujan, *Highly Composite Numbers*, §5](https://ramanujan.sirinudi.org/Volumes/published/ram15.html)

For each $p^e\parallel n$ with $e\ge2$, let $h=\lfloor e/2\rfloor$. The product formula gives a divisor $D=L_h(p,c)$ of $C_0$, with $c\in\{0,1,2\}$. This includes the ramified case $c=1$ when $e$ is odd. The inequality $p^h\le D\le(p+2)^h$ places $p$ among the three integers ending at $\lfloor D^{1/h}\rfloor$. Enumerate the divisors of $C_0$ from its recursive factorization and every $1\le h\le b/2$. For the three candidates, verify primality and $p^2\mid n$ before extracting the full power. Every repeated prime has a witness. The remaining $s$ is squarefree.

## Factoring the squarefree remainder

If $s>1$ is composite, select $a'$ by the same mod-eight rule applied to $s$. Each prime dividing $s$ ramifies in $-a's$. Consequently

$$
\sigma(s)=\frac{C(a's^3)}{C(a's)}=\prod_{p\mid s}(p+1).
$$

The denominator from the preceding step can be reused when $s=n$. For a promised semiprime $s=pq$ the two counts determine $p+q=\sigma(s)-s-1$. Solving the quadratic by an integer square root finishes in polynomial time.

In general recursively factor the odd part $u$ of $\sigma(s)$. Since $s$ has at least two odd prime factors,

$$
u\le s\prod_{p\mid s}\frac{1+1/p}{2}\le (2/3)^2s<s/2.
$$

The known power of two completes the factorization of $\sigma(s)$. Enumerate its divisors $D$ and test whether $D-1$ is a prime dividing $s$. This recovers every factor. Each recursive node thus has at most one child of at most $b-1$ bits and another of at most $4b/5$ bits for sufficiently large $b$. Unroll a chain of the first children. Its $O(b)$ nodes start at most $O(b)$ smaller chains. After $O(\log b)$ such levels all inputs have bounded length. This gives $\exp(O(\log^2(2b)))$ nodes. Each node enumerates at most $2^{O(b/\log(2b))}$ divisors and spends polynomial time per divisor. Exact-count indices have at most $3b+3$ bits. The digit reduction preserves linear bit length and multiplies the query count by at most $O(b)$.

## Polynomial overhead from the verified Dirichlet GRH

At an odd cofactor $n$ coprime to $3,5,7$, take $a$ as above. If $p^e\parallel n$ and $e$ is odd, the prime $p$ ramifies at both indices $an$ and $an^3$. Its conductor exponents are $(e-1)/2$ and $(3e-1)/2$. They differ by the odd number $e$, so one is odd. For odd $h$ the local sum $L_h(p,1)=1+p+\cdots+p^h$ is divisible by $p+1$. Thus the single product $M=C(an)C(an^3)$ covers every odd-valuation prime of $n$. For instance, at $n=11^3\cdot13^2$ the counts are $540$ and $123831345$, and the first one supplies the factor $12$.

Apply the one-prime $p+1$ splitter using the proved Dirichlet GRH with this same $M$ throughout the current round. Stop a square branch and record a prime branch. For a nonsquare that is a prime power take its base. For any other nonsquare branch $x$, obtain a proper divisor $u$, put $v=x/u$ and $g=\gcd(u,v)$, and recurse on $u/g,v/g$. They are coprime with product $x/g^2$, so their odd-valuation prime sets partition that of $x$. Remove the full powers of the recorded primes from $n$, take the square root of what remains, and start another round. Each round halves the largest remaining exponent. Stripping $2,3,5,7$ initially, and carrying multiplicities through the roots, gives at most $1+\lfloor\log_2\max_p v_p(N)\rfloor$ pairs of exact counts and $O(b\log(2b))$ designated-digit queries. All indices still have $O_\alpha(b)$ bits and all arithmetic outside the queries is polynomial. The replay uses three pairs on $11^3 13^6 17^4 19^8$. [Splitter, hypotheses and recursion](p-plus-one-multiples.md#consequences-for-complete-factorization) · [Lamzouri–Li–Soundararajan, Theorem 1.4](https://arxiv.org/pdf/1309.3595#page=3)

## Average cost with a single exact count

Strip $2,3,5,7$ from the original input $N$ and call the remaining integer $n$. Choose $a$ as above and supply just $C(an^3)$ when $n>1$. For each $p\parallel n$, the fundamental part of $an^3$ is divisible by $p$ and the conductor has $p$ to exponent one. Thus $p+1$ divides the supplied count. Its bit length is $O(\log N)$. The $k=2$ average splitting theorem in this repository uses only these divisibilities on original multiplicity-one primes. At cutoff $L$, the extra fraction with an unextracted repeated prime costs $O(\sum_{p>L}p^{-2})=O(1/L)$ in the original uniform distribution. The theorem's deterministic stage and its terminating fallback therefore give polynomial mean bit cost beyond this one count. The ordinary four-square count is related to the ordinary divisor sum in Bach–Miller–Shallit. The ramified index here uses three squares. [Average splitting theorem and runtime tail](average-cyclotomic-splitting.md) · [Bach–Miller–Shallit, §6](https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf)

## Prior work and reproduction

The earlier three-square reduction uses small character twists, low-bit counts and a least-prime estimate from Dirichlet GRH. Its one-bit variant returns the parity of a remainder modulo a separately chosen small prime. The present fixed binary position uses the norm multiplier above. The divisor enumeration here yields a larger deterministic overhead and uses a descending recursion to remove the least-prime hypothesis. Morain, Renault and Smith give polynomial deterministic recoveries from arithmetic oracles under size conditions on factors. A search of these sources did not establish priority for the fixed-digit or ramified recursions. [Earlier count reductions](hurwitz-polynomial-reductions.md) · [Morain–Renault–Smith](https://arxiv.org/abs/1802.08444)

Run `gp -fq experiments/ramified-three-squares.gp` at the repository root. The replay enumerates 64 positive-triple counts directly. It checks exact recovery from 120 designated digits at three fractions, with padded inputs through 144 bits, and directly compares six padded counts with PARI's Hurwitz evaluator. The other padded counts use an independent evaluator which factors the index and computes its fundamental class number. The recursive factoring routine receives only a count callback and the given integer. Across 358 inputs its small and structured fixtures cover repeated prime powers, the squarefree branch, removal of $2,3,5,7$, and a complete factorization through the single-digit interface. A separate sweep checks 912 multiplicity-one divisibilities at the cubic index. The asymptotic statements above are paper arguments. [PARI/GP decoder and tests](../experiments/ramified-three-squares.gp)
