# Extracting a hidden common divisor on arbitrary sets of multiples

Fix \(r\ge1\). Let \(\mathcal N\) be **any set of \(J\ge1\) distinct positive integers** of at most \(b\) bits, all divisible by an integer \(K\ge2\). An algorithm receiving just \(N\) certifies its prime factors with full multiplicities. If \(P\) is the largest prime divisor of \(K\), then its time \(T_K(N)\) to emit every prime factor of \(K\) satisfies
\[
 \left(\frac1J\sum_{N\in\mathcal N}T_K(N)^r\right)^{1/r}
 \le b^{O_r(1)}
 \min\!\left\{\sqrt P,
       \mathcal L(P)\left(1+\frac{P^{3+(r-1)/2}}{J}\right)^{1/r}\right\}.
\]
Here \(\mathcal L(p)=\exp(O_r(\sqrt{\log(2p)\log(2+\log(2p))}))\).
More precisely, the numerator can be replaced by
\(\max_{p\mid K}p^{d(p)+(r-1)/2}\), where \(d(p)=1\) for primes qualifying for the prime-field Hasse count, \(d(p)=2\) for the remaining primes qualifying over \(\mathbb F_{p^2}\), and \(d(p)=3\) otherwise. The earlier shifted-interval bound has \(P^{3r}/J\) in the unrestricted case. Here the set of multiples can be arbitrarily sparse or irregularly spaced. On dyadic intervals, complete factoring of the residual uses the earlier separate divisor-sum estimate. [Local arithmetic and source hypotheses](quadratic-elliptic-partners.md) · [Streaming extraction and residual bit cost](common-divisor-partners.md)

## Absolute counts for a fixed target

Fix a prime \(p\) and its dyad \(D<p\le2D\). The local arithmetic supplies a public family of eligible targets in a binary cube of width \(w=d\log_2(2D)\), for \(d=d(p)\), each of density at least \(1/\mathcal L(p)\). Each depends only on the specified prime, dyad, public parameters and the size schedule. For a fixed input bit length \(b_0\le b\), the number of public parameter choices whose targets have to be hit is \(b^{O(1)}\). Hitting all the eligible targets for \(p\) forces the algorithm to certify \(p\) on every \(N\) in this class divisible by \(p\). This uses the sign witness for every other prime \(q\), and replay of the same word in each child when a proper gcd leaves \(p,q\) together. The word always comes from the original input. The one-, two- and three-coordinate machines and their finite treatment of small primes are dovetailed. [Sign witnesses and processing every child](common-divisor-partners.md#a-search-that-preserves-witnesses-through-successive-splits)

First enlarge a target \(G\) to \(G'\) by including all starting words whose fixed menu of binary shifts hits \(G\). Use the explicit small-bias construction from the arithmetic-mean search. Its missed fraction is at most \(w^2/(4^a\gamma)\) for \(\gamma=|G|/2^w\). A public \(a\) with \(4^a\ge4w^2\mathcal L(p)\) thus gives \(|G'|\ge 3\cdot2^w/4\) at \(\mathcal L(p)\,\mathrm{poly}(b)\) cost per starting word. Use a dyadic upper bound for \(\mathcal L(p)\), increasing the fixed constant as necessary. The algorithm only enumerates the shifts and executes the local tests. [Small-bias estimate](mean-time-elliptic-factoring.md#a-deterministic-search-with-a-summable-cost-per-stage)

At stage \(i\), \(0\le i<w\), project \(G'\) onto the first \(w-i\) bits, giving \(G_i\) of density at least \(3/4\). Enumerate all \(2^i\) suffixes for every prefix produced by the following decoder. Use the binary representation of the original \(N\), padded to length \(n=\max(b_0,w+c_0)\) for a sufficiently large absolute constant \(c_0\). Put \(k=w-i+c_0\), so \(k\le n\).

Use the explicit constant-error extractor of Ta-Shma, Umans and Zuckerman with error \(1/4\). Its seed has
\[
 e=O\!\left(\log(n+2)+\log^2(k+2)(\log\log(k+4))^2\right)
\]
bits and its output has at least \(k+e-c_0\) bits. Keep \(w-i\) output bits and enumerate all \(2^e\) seeds. This costs \(b^{O(1)}\exp(O((\log(w+2))^3))\) per stage prefix menu, absorbed by \(b^{O(1)}\mathcal L(p)\). In particular the seed's dependence on the length of the original input remains logarithmic even when that length is arbitrarily large compared with \(p\). The input length, the dyad and the dimension are known in each copy. [Ta-Shma–Umans–Zuckerman, Corollary 5.8(2)](https://users.cms.caltech.edu/~umans/papers/TUZ01-final.pdf#page=17)

For a fixed target, **fewer than \(2^k=O(p^d/2^i)\) strings of length \(n\)** miss every stage-\(i\) prefix in \(G_i\). Otherwise the uniform distribution on any \(2^k\) of them would have min-entropy \(k\) while its extracted distribution assigns zero probability to \(G_i\). Uniform strings give \(G_i\) probability at least \(3/4\), exceeding the allowed error. Padding is injective at every fixed \(b_0\). After the union over \(b_0\) and public targets, at most \(b^{O(1)}p^d/2^i\) distinct eligible multiples of \(p\), throughout the entire bit range, remain unrecognized after stage \(i\). The same count applies to any subset of those multiples.

## From the count to running time

All stages through \(i\) in the correct dyad require \(2^i b^{O(1)}\mathcal L(p)\) bit operations including the conic and scalar tests, replay on unresolved blocks, and deterministic scheduling. The parallel Pollard–Strassen search emits every \(p\mid N\) by \(b^{O(1)}\sqrt p\). Take \(h=\lceil\log_2\sqrt p\rceil\), less than \(w\) for large \(p\). Charge successive stages through \(h\) to the preceding miss counts, then charge the fallback on the remaining inputs to the stage-\(h\) miss count. After absorbing the polynomial and \(\mathcal L(p)\) factors, the resulting upper bound on the sum of the \(r\)-th powers of the extraction times for \(p\) is
\[
 J+O_r\!\left(p^d\sum_{i=0}^h 2^{(r-1)i}\right)
       \le J+b^{O_r(1)}p^{d+(r-1)/2}.
\]
The logarithmic sum at \(r=1\) is included. For the primes of \(K\), take the maximum of their individual extraction times, bounded in \(L^r\) by the sum of at most \(b\) norms. No one copy needs to identify \(d(p)\) or \(K\). The deterministic factorial cap gives the other term of the minimum. The same machine works for every \(r\), as the menu, stages and fallback are independent of \(r\). [Factorial search and its bit complexity](https://arxiv.org/pdf/1201.2116)

For comparison, a pure counting argument cannot usually replace the \(1/2^i\) decay by its \(r\)-th power while retaining the absolute \(O(p^d)\) prefactor. In an abstract domain of \(M\) parameters, examine any \(\lfloor M/(2t)\rfloor\) master strings on their all-failure transcripts, each testing at most \(t\) parameters. Their union omits at least half the domain. Choosing a target there makes all those failures genuine. The arithmetic targets and their certified gcds carry additional information beyond this density argument.

The [integer replay](../experiments/extractor-common-divisors.py) checks all 255 nonempty target sets in a three-bit local domain against an eight-bit source family. It verifies all 765 projected suffix tests by direct decoding. Across every target and three powers of the time cost, it checks 5,355 upper bounds for arbitrary subsets by selecting the most costly masters of each indicated size. The finite arithmetic of the local witnesses and the composite factor tree has separate [quadratic-field](../experiments/quadratic-elliptic-partners.py) and [genus-two](../experiments/common-divisor-partners.gp) replays.
