# Sampling short modular squares by local linearization

Fix \(2/3<a<1\) and let \(N\) be odd. Take \(X=\lfloor N^a\rfloor\), \(B=\lfloor\sqrt X\rfloor\), and \(V=BX/N\). The sampler below takes polynomial bit work per trial and has success probability \(\gg 1/\log N\), uniformly in \(N\) for sufficiently large \(N\). Conditional on success its root is within \(N^{-\Omega(1)}\) in total variation of the uniform unit \(z\bmod N\) whose positive square residue lies in \([1,X]\). The sampler uses no factorization of \(N\).

Vallée previously gave polynomial-time quasi-uniform sampling at the two-thirds scale; Gentry's §4.1 made the law exactly uniform for intervals of width at least \(8N^{2/3}\). These results already establish the sampling capability required by the factoring schedule. A representative drawn uniformly in the half interval can be given an independent sign for odd \(N\). Rejecting nonunits preserves uniformity on unit roots. The zero residue is excluded by taking the lower endpoint to be 1. The unit count and the corresponding unrestricted quadratic count show that rejection has inverse-polylogarithmic acceptance for \(X\asymp N^{2/3}\), tending to one on the rough branch. For a fixed schedule, \(X=\lceil 8N^{2/3}\rceil\) changes the prescribed coordinate bit length by only \(O(1)\) from the leading width \(2/3\). The present floor-sum procedure gives an alternative implementation for every fixed \(a>2/3\). The cost improvement comes from combining short-square sampling with the charged KeyBreak descent. [Vallée, STOC 1989](https://doi.org/10.1145/73007.73016) · [Gentry, §§3–4](https://www.iacr.org/cryptodb/archive/2004/CRYPTO/1334/1334.pdf#page=8)

## Padded proposals

Draw a center \(b\bmod N\) uniformly and use the offsets \(0\le r<B\). If \(z=b+r\bmod N\) has square residue in \([1,X]\), then \(b^2+2br\bmod N\) lies in the circular integer interval \(J=[-B^2,X+1)\): subtract \(r^2\) from that square residue. The interval length \(B^2+X+1<N\) for large \(N\). Let \(K_b\) be the number of offsets hitting \(J\).

Put \(L=\lceil4V\rceil\). Reject the center if \(K_b>L\). Otherwise draw one uniformly padded slot from \(1,\ldots,L\), rejecting slots beyond \(K_b\). Unrank the chosen offset in the increasing list of hits, and verify that \(z\) is a unit and that its positive square residue lies in \([1,X]\). Every surviving center and offset has the same unconditional mass \(1/(NL)\).

To implement the count, for a circular interval \([l,u)\) of integer length less than \(N\) the indicator of a congruence hit by \(y\) is
\[
\left\lfloor\frac{y-l}{N}\right\rfloor
-\left\lfloor\frac{y-u}{N}\right\rfloor .
\]
For \(y=b^2+2br\), summing on any prefix in \(r\) is the difference of two linear floor sums, computed by Euclidean division even when an intercept is negative. Binary search on this monotone prefix count unranks any slot in polynomial bit work. The algorithm need not generate the list explicitly.

## Overflow cannot discard a good root

In scales \(B,X\), write
\[
\Lambda_w=\{(t/B,h/X): t,h\in\mathbb Z,\ h\equiv wt\bmod N\}.
\]
Its determinant is \(1/V\). Suppose \(z=b+r\bmod N\) with \(0\le r<B\). The linear map sending an element of \(\Lambda_{2b}\) to
\[
(2t/B,(h+2rt)/X)
\]
takes values in \(\Lambda_z\), since \(h+2rt\equiv 2zt\bmod N\). Its matrix in normalized coordinates is \(\bigl(\begin{smallmatrix}2&0\\2rB/X&1\end{smallmatrix}\bigr)\). It is injective and has operator norm at most \(4\) because \(B^2\le X\). No equality of lattice indices is required. In particular \(\lambda_1(\Lambda_{2b})\ge\lambda_1(\Lambda_z)/4\) in the Euclidean norm.

The candidates of center \(b\) are points of the translate of \(\Lambda_{2b}\) by \((0,b^2/X)\) in a rectangle with horizontal interval \([0,1)\) and vertical interval \(J/X\). There is exactly one vertical lift for each hit. The rectangle has area \(2+o(1)\) and bounded diameter, so the [translated rectangle discrepancy](keybreak-generic-lattice-weights.md#uniform-rectangle-discrepancy) gives
\[
 K_b=(2+o(1))V+O(1+\lambda_1(\Lambda_{2b})^{-1}).
\]
Call a unit root good if \(\lambda_1(\Lambda_z)>N^\eta/V\) for a fixed \(\eta>0\) as below. Then every center representing that root has \(K_b\le3V\) for large \(N\), since \(V\to\infty\). Thus no representation of a good root overflows.

## Endpoint and output distribution

The [short-vector exception proof](keybreak-short-vector-exception.md) applies at the endpoint \(s=a/2\) corresponding to \(B=N^{s+o(1)}\). In that proof the bounds on the integer coordinates become \(N^{1-a+\eta+o(1)}\) and \(N^{1-a/2+\eta+o(1)}\), respectively. Choose \(0<2\eta<\min(3a/2-1,a/2)\). The first is then at most \(\sqrt X\), and the second is at most \(X\), as required in the two dyadic counts. The four final exponents of the exception count are, up to \(o(1)\),
\[
a/2,\qquad 1-a/2+2\eta,\qquad 1-a/2+2\eta,\qquad a/2+2\eta .
\]
All are strictly less than \(a\). The integer floor in \(B\) has no effect on these strict inequalities. The proof therefore gives \(O(N^{a-\gamma})\) nongood roots for a fixed \(\gamma>0\). This argument uses \(a>2/3\), including to make \(V\) grow.

Let \(\mathcal Z\) be the unit root population. By the [complete quadratic sum count](keybreak-primitive-denominator-discrepancy.md#large-divisors-and-the-unit-population), \(|\mathcal Z|=X\varphi(N)/N+O(N^{1/2+o(1)})\). In particular the bad fraction is \(N^{-\Omega(1)}\) since \(\varphi(N)/N\gg1/\log N\). Each element of \(\mathcal Z\) has exactly \(B\) representations as \(b+r\bmod N\) with the stated offset range. Good roots keep all \(B\) representations, and every other root keeps at most \(B\). Consequently the conditional root law is the uniform law on \(\mathcal Z\) thinned only on its bad fraction. Its total variation distance from uniform is at most that fraction. The trial acceptance probability is \((1-o(1))B|\mathcal Z|/(NL)\), of order \(\varphi(N)/N\). Independent trials with a polynomial cap give negligible probability of no output. If the root is to remain private, only the required square residue is exposed; the center, slot and offset are internal sampler data.
