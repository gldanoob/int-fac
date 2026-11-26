# The ramified row above two in full-grid parity

The raw, derivative-repaired and planted monic pairs are all Eisenstein at two. Their full-grid parity computation can therefore admit the prime above two in each field while retaining the exclusions at every odd prime dividing either polynomial discriminant. This recovers \(r-1\) independent parity dependencies from \(r\) planted norm-two marks whenever the grid contains those marks. [Full-grid algorithm](cogentic-monic-large-primes.md) · [Planted pair](cogentic-planted-norm-two.md) · [Exact replay](../experiments/cogentic-monic-ramified-two.py)

## The local ideal calculation

Let \(H\) be one of the defining polynomials of degree \(d\ge2\) and let \(\theta\) be its root in \(K\). For every prime ideal \(\mathfrak p\) of the maximal order above 2, the equation \(H(\theta)=0\) reduces to \(\theta^d=0\) in the residue field. Thus \(\theta\in\mathfrak p\). Write \(\theta^d=-2U(\theta)\) with \(U(0)\) odd, which makes \(U(\theta)\) a unit at \(\mathfrak p\). For the valuation normalized to have value group \(\mathbb Z\),
\[
 d\,v_{\mathfrak p}(\theta)=v_{\mathfrak p}(2)=e(\mathfrak p/2).
\]
Since \(v_{\mathfrak p}(\theta)\ge1\), the degree formula \(\sum_{\mathfrak p\mid2}e(\mathfrak p/2)f(\mathfrak p/2)=d\) gives exactly one prime ideal above 2, with \(e=d\), \(f=1\) and \(v_{\mathfrak p}(\theta)=1\).

For a primitive grid mark \((a,b)\), odd \(a\) makes \(a-b\theta\) a unit at this prime. If \(a\) is even, then \(b\) is odd and the valuation is one, since the terms have valuations \(v_{\mathfrak p}(a)\ge d\) and \(v_{\mathfrak p}(b\theta)=1\). The rational norm valuation agrees with the ideal valuation because \(f=1\). Equivalently, the homogeneous norm of an even-numerator mark is \(2\bmod 4\), since every term above the constant is divisible by 4. The fixed residue root is zero.

The grid option `include_ramified_two=True` requires monic degree at least two and verifies Eisenstein at two for each polynomial. It strips the two-part of the common discriminant exclusion. For each retained even numerator it removes one factor of two before bounded trial division and records the row \((i,2,0)\) for field \(i\). The two row vectors have identical entries across the grid, and their field identities describe two distinct prime ideals. All ordinary root and residual-square rules apply to the remaining odd norm. Since 2 is in the factor base, the argument discarding private odd rows beyond twice the squared grid height applies without change. The default grid call uses the original exclusion at two.

An Eisenstein polynomial at another rational prime also gives a single degree-one prime ideal there. This option admits only 2, and the proof that the valuation is at most one on primitive marks uses the local Eisenstein condition and the corresponding congruences. Arbitrary odd ramified or index primes remain excluded.

## Planted parity dependencies

Assume all cuts \(t_j\) lie in the numerator interval. Each \((t_j,1)\) passes the unit condition by construction and has norm 2 in both fields. The new matrix has exactly the same nonzero column \((1,2,0)+(2,2,0)\) at all \(r\) cuts, where the sum denotes the two row entries. The \(r-1\) pairs consisting of the first cut and one other cut form independent dependency vectors. Their span consists of the even subsets of planted cuts. The vectors are also independent of the entire legacy kernel, since the legacy grid contains only odd numerators. The polynomial discriminants are even because the reductions modulo 2 have a repeated root. Thus adding the ramified row increases nullity by at least \(r-1\) independently of how many other relations the grid contains.

This is a lower bound for ideal parity. The even products of planted elements can still give nonsquare unit classes. For the derivative bump that separates the real signatures, every nonempty subset of planted marks has a nonsquare product in each field, even with a common sign choice. The explicit parity dependencies therefore leave a separate square-class condition. [Planted unit signatures](cogentic-planted-unit-signatures.md)

## Fixed-grid comparisons

The comparison uses the full parity cutoff \(Y=8192\), the in-base cutoff \(B=151\), and marks \(|a|\le64\), \(1\le b\le64\). The replay independently computes maximal orders and their discriminant identities in PARI. It checks the decomposition of 2, the prime-ideal and rational norm valuations at 2 for every retained mark, and all odd ideal rows by complete principal ideal factorization. It also checks directly that the odd part of the discriminant exclusion holds in both fields.

| Family | Input | Planted cuts | Legacy columns | Legacy nullity | Ramified columns | Ramified nullity |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Raw cubic/quartic | 323 | 0 | 564 | 1 | 916 | 7 |
| Repaired quadratic/cubic | 17 | 0 | 449 | 0 | 728 | 18 |
| Repaired quadratic/cubic | 67 | 0 | 666 | 9 | 1057 | 137 |
| Planted degrees 6/7 | 85 | 2 | 20 | 0 | 38 | 1 |
| Planted degrees 6/7 | 631 | 2 | 29 | 0 | 45 | 1 |
| Planted degrees 9/10 | 15629 | 3 | 6 | 0 | 11 | 2 |
| Planted degrees 12/13 | 5764807 | 4 | 2 | 0 | 6 | 3 |

The remaining eleven raw fixtures and three repaired fixtures keep their legacy nullities. The four planted fixtures attain exactly \(r-1\), so their new kernels are spanned by the planted pairs. In all 21 fixtures the legacy columns equal the odd-numerator part of the augmented columns. PARI independently verifies 16,970 field columns. A general bound on productive square dependencies in these augmented kernels remains open.
