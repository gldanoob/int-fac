# A fair proposal for short rational representatives

Let the odd input be \(N\), let \(X=\lfloor N^a\rfloor\), and choose a power of two \(T=2^J\) between \(N^s/2\) and \(N^s\), for fixed rational \(2/3<a<1\) and \(1-a<s<a/2\). Take \(I=[\lceil X/8\rceil,\lfloor X/4\rfloor]\). The proposal assigns the same unconditional probability to each primitive pair
\[
 T\le t<2T,\quad t\text{ odd},\quad (t,N)=(h,N)=(t,h)=1,\quad h\in I,\quad
 1\le u=(h/t)^2\bmod N\le X .
\]
It returns \(z=h/t\bmod N\) on that pair. Its work is polynomial in the input length in expectation. It uses only randomness generated for the current input.

1. Choose \(j\) uniformly from \(0,\ldots,J\). Independently generate uniform factored integers \(d\in[1,2^{j+1}]\) and \(e\in[1,2T/2^j]\). Keep \(2^j\le d<2^{j+1}\), squarefree \(d\), and odd \(t=de\in[T,2T)\) coprime to \(N\). The prime factors of the two draws give the factorization of \(t\). Each ordered pair with these properties has probability \(1/[4T(J+1)]\). For a fixed \(t\), exactly \(2^{\omega(t)}\) choices survive, one for every squarefree divisor. All ranges can be sampled without materializing them. Uniform generation with the factorization takes polynomial expected time. [Kalai, Generating Random Factored Numbers, Easily](https://www.microsoft.com/en-us/research/publication/generating-random-factored-numbers-easily/)
2. Independently choose \(k\) uniformly from the integers in
   \[
   \mathcal K=\left[\left\lfloor((\min I)^2-4T^2X)/N\right\rfloor,\quad
                   \left\lfloor(\max I)^2/N\right\rfloor\right].
   \]
   For large \(N\), this interval is positive, has size \(\Theta(X^2/N)\), and covers every \(k=(h^2-t^2u)/N\) in the claim. Reject unless \(kN\) is a unit square modulo \(t^2\). Test at each prime divisor of \(t\), find one square root modulo the prime, and lift it uniquely by Hensel to the doubled prime power exponent. Choose an independent fair sign at each prime and combine by CRT. A random nonresidue found by the Euler test supplies Tonelli–Shanks with expected polynomial work. Each root modulo \(t^2\) then has probability \(2^{-\omega(t)}\).
3. Intersect \(I\) with the integer interval \(\sqrt{kN}<h\le\sqrt{kN+t^2X}\). Draw one of eight slots uniformly. Use that slot of the increasing list in the selected residue class modulo \(t^2\), rejecting an empty slot. The interval after intersection has length at most \(4t^2\) because \(h_1+h_2\ge X/4\) in \(I\) and the difference of squares is at most \(t^2X\). The list and selected entry use integer square roots and Euclidean quotients. Check unit \(h\), then return \(z\) and \(u=(h^2-kN)/t^2\). Only \(u\) is needed for the public descent.

For each displayed pair, \(u\) and \(k\) are unique as \(X<N\). Its congruences and coprimality imply \((kN,t)=1\), so it occurs. Conversely, every returned pair satisfies the claim. Its exact mass is
\[
 c_N=\frac{1}{32T(J+1)|\mathcal K|}.
\]
Any deterministic predicate on \(z\) can be applied as a final rejection with this same weight on the surviving pairs. For this proof all nonunit tests may reject. A separately verified proper divisor can optionally end an epoch earlier.

For a fixed work cap, couple the bounded sampler to the first accepted elementary Kalai proposal. Each proposal draws a nonincreasing chain of uniform integers, keeps its primes, and tests its final product with the acceptance coin in Kalai's algorithm. Its chain has an arbitrarily strong inverse-polynomial tail after \(O(\log N)\) steps with sufficiently large constant, since each nontrivial draw has probability at least \(1/3\) of halving the current value. The number of independent elementary proposals needed is geometric with mean polynomial in \(\log N\) by Kalai's result. Cap the number of proposals at a polynomial giving tail \(N^{-A}\) for any fixed \(A\), and use a union bound for the chain lengths. Uniform integer rejection and each search for a prime nonresidue have geometric tails as well. Thus the bounded implementation agrees with the ideal on all but \(O(N^{-A})\) of its coins. This coupling accommodates any dependence of generator runtime on its output. Deterministic polynomial primality testing suffices.
