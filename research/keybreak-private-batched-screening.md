# Batched screening of private candidates for one input

Product and remainder trees move the cost of a *supplied* prime base from each candidate to the whole list. The independent private sampler does not supply a useful base this way. The permitted prime bands are beyond the affordable explicit cutoff, and both reuse of discovered prime factors and compression of packed curve moduli have quantitative obstructions. The comparison concerns lists of private candidates for a single target. [Private band stages](keybreak-private-band-stages.md) · [Enlarged lattice comparison](keybreak-enlarged-private-lattice.md#shared-factors-and-sieve-cutoffs)

## What the trees compute and charge

Let \(m_1,\ldots,m_K\) be the positive cofactors presented to a stage and \(L=\sum_i\operatorname{bitlength}(m_i)\). Given a verified prime list \(\mathcal P\) of aggregate bit length \(W\), form the unpowered product \(A=\prod_{p\in\mathcal P}p\) and reduce it at every leaf through a remainder tree. The full part of \(m_i\) supported on this base is
\[
s_i=\gcd\bigl(m_i,\ (A\bmod m_i)^{2^{e_i}}\bmod m_i\bigr),
\qquad 2^{e_i}\ge\operatorname{bitlength}(m_i).
\]
This retains all powers of primes in the base, including powers exceeding the cutoff. Product formation, remaindering and local squaring cost \(\widetilde O(W+L)\) bit operations. Bernstein's separate batch factorization distributes the tagged prime factors to the leaves in \(\widetilde O(W+L)\) as well. Powers of all base primes need never be stored in \(A\). For the complete base through \(z\), the product has \(\Theta(z)\) bits, by the Chebyshev bounds. A segmented sieve can pay for enumeration within \(\widetilde O(z)\) bit work on this input. The prime number theorem gives the same bit length for a full dyadic or fixed leading-exponent band ending at \(z\). [Bernstein, Algorithm 2.1, Theorem 2.3 and earlier batch factorization](https://cr.yp.to/factorization/smoothparts-20040510.pdf)

For the base consisting of other candidate values, form \(P=\prod_i m_i\) and reduce modulo \(m_i^2\). The output
\[
\gcd\left(m_i,\frac{P\bmod m_i^2}{m_i}\right)
=\gcd\left(m_i,\prod_{j\ne i}m_j\right)
\]
has exactly the support that repeats across distinct records. This also costs \(\widetilde O(L)\). Squaring locally as above can saturate the returned support to the full shared part of each cofactor. Neither operation introduces a new prime that appears in a single record. Taking a base of verified prime factors from earlier candidates has the same support restriction on later candidates.

At a stage of size \(K=\exp((k+o(1))H)\), \(L\) has exponent \(k\) when operands have input-polynomial bit lengths and there are \(K\) nontrivial records. An explicit base with \(W=\exp((w+o(1))H)\) then makes the *entire* tree coefficient \(\max(k,w)\). If an independent cheap predicate safely retains only a population of exponent \(k'\) for an expensive recognizer of coefficient \(e\), the combined charge is \(\max(k,w,k'+e)\), with no product between the full list size and the prime-base size. In the actual private sampler every required factor is at least \(Y_{\min}=\exp(\Theta(DH))\) for a fixed band grid, including grids with a small fixed first endpoint. The complete prime base for any permitted band therefore costs more than any \(\exp(O(H))\) budget. A complete base of size \(\exp(O(H))\) detects only primes below the private bands. It can reject some candidates by forbidden factors. The padded-prefix examples use only larger primes and attain the same leading population at that gate. [Padded-prefix population](keybreak-enlarged-private-lattice.md#occupancy-and-one-hidden-root-per-square)

## Distinct high-prime support in the independent list

Use the original bounded representatives with \(m_i\le X=O(\sqrt N)\), and the rough-input event of the private prepass with \(2^{\omega(N)}=\exp(o(H))\). Independent slots sample unit roots, then expose their public squares. Every pair with bounded positive coordinates names at most one square and receives probability at most \(O(2^{\omega(N)}/N)\) from a fresh private slot. The same estimate applies to the uniform raw slots with rejected nonunits. Hence the probability that a specified coordinate is divisible by a specified prime \(p\) is at most \(O(2^{\omega(N)}/p)\), by counting at most \(O(X^2/p)\) pairs. Within a representative the two coordinates are coprime. Across distinct slots, independence and summation give
\[
\Pr(\text{some prime }>z\text{ occurs in two different records})
\ll K^2\,2^{2\omega(N)}\sum_{p>z}p^{-2}
=O(K^2 2^{2\omega(N)}/z).
\tag{1}
\]
This statement is about the raw independent list, so it holds for arbitrary sublists selected afterward. In particular, at \(z=Y_{\min}\) it gives \(\exp(-\Omega(DH))\) failure for any \(K=\exp(O(H))\). Also, a menu of \(M_0\) permitted primes fixed before a fresh slot hits it with probability at most \(O(2^{\omega(N)}M_0/Y_{\min})\), even when the menu was built from earlier slots. [Private square fibers](keybreak-private-band-stages.md#the-shapes-counted-below)

A stronger modulus-size consequence uses \(z=\exp((2k+\eta)H)\) for any fixed \(\eta>0\). Equation (1) excludes repetitions above \(z\) except with probability \(\exp(({-\eta}+o(1))H)\). Fix any \(\epsilon>0\). For a raw coordinate, the probability that its \(z\)-smooth part exceeds \(X^\epsilon\) is at most
\[
O(2^{\omega(N)}) X^{-\epsilon s}
  \prod_{p\le z}(1-p^{-1+s})^{-1},
\qquad s=\frac{\log u}{\log z},\quad u=\frac{\log X}{\log z}.
\]
Indeed count multiples of all such smooth divisors, then use Rankin. Here \(u=\Theta(D^2)\). The Euler product has logarithm \(O(\log\log z+u)=o(u\log u)\), by the same Chebyshev and partial-summation estimate used for the private shapes. The bound is \(\exp(-\Omega(DH))\), even after a union bound over the whole list. For any adapted sublist \(I\) and divisors \(m_i'\mid m_i\), both conclusions together give
\[
\sum_{i\in I}\log m_i' - |I|\epsilon\log X
\ \le\ \log\operatorname{lcm}_{i\in I}(m_i')
\ \le\ \sum_{i\in I}\log m_i'.
\tag{2}
\]
Every high-prime valuation is counted in full in the lcm, and the total low-prime loss is bounded by the low-prime mass of each original coordinate. In any active list with positive mean residual bit fraction, this rules out a leading reduction of operand bits by lcm packing. The argument allows the cofactors and active list to be chosen from all previous public screening results. It needs no independence after selection.

## What one shared stage-one curve saves

For ordinary stage-one ECM with cutoff \(B_1\), the common multiplier \(E=\operatorname{lcm}(1,\ldots,\lfloor B_1\rfloor)\) has \(\Theta(B_1)\) bits. It may be built once. A binary-chain projective scalar multiplication then uses \(O(B_1)\) ring operations per curve. One can perform each curve over a common product modulus, then take all coordinate gcds against the reduced projective coordinate using a remainder tree. Pairwise coprime moduli admit independent local curve parameters from one uniform packed draw by CRT. Using an lcm permits the same ring evaluations on overlapping moduli, sharing parameters at their common primes. Projective formulas or split-on-failure conventions preserve the ordinary verified-gcd interface. [Lenstra–Pomerance, §7](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf#page=19)

If \(L_j^*\) is the bit length of the packed active modulus for curve \(j\), then the arithmetic bound for this implementation is
\[
\widetilde O\left(B_1+\sum_{j=1}^{R} B_1 L_j^*\right).
\]
Remaindering and gcd outputs fit in the same bound. Alternatively one can run the same addition chain over each active cofactor separately and charge its bit lengths in place of \(L_j^*\). Equation (2) shows that lcm packing does not change the leading operand exponent on the lists to which its bit-fraction condition applies. As a concrete comparison, at \(B_1=\exp((c+o(1))T_y)\) and \(R=\exp((e+o(1))T_y)\), \(T_y=\sqrt{\log y\log\log y}\), a full unresolved list of exponent \(k\) costs \(k+(c+e)T_y/H\) in either implementation. Running one common setup instead of one setup per cofactor does not change that term.

Charging this curve term only to successful candidates would require independent information to prune the unresolved list early. Even if an explicit permitted base could provide that information, its creation would enter the entire-list term. In a model with at most \(\tau\) conditional probability of detecting a genuine pass per curve and true pass density \(\rho\), assigning \(R\) curves per unresolved candidate gives expected detected passes at most \(K\rho\min(1,R\tau)\), by the union bound. Fewer rounds can therefore require more raw candidates, and the two charges must be counted together. This last comparison assumes the per-curve upper bound, rather than claiming one from the recognition theorem. The results exclude reuse by the explicit-base, repeated-prime and packed stage-one mechanisms above. They leave an arithmetic method that directly selects promising private lattice positions open.
