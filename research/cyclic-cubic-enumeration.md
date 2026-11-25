# Exact near-linear enumeration of square-discriminant cubics

Given integer box height $H\ge1$, the algorithm lists the triples $(a,b,c)\in[-H,H]^3$ for which $X^3+aX^2+bX+c$ has positive square discriminant. The deterministic bit cost is $H^{1+o(1)}$. Requiring $c=-A^3$ for a positive integer $A$ is a final filter. For this restricted list, an optional rational-root test needs only the divisors of $A^3$, whose prime factors can be found from a sieve through $H^{1/3}$.

For cubic-order factoring, retain the negative-cube list and use the existing trial-division and odd-exponent coefficient-gcd tests. Under the uniform Dedekind zero-free strip of the order-splitting theorem, this list contains a successful polynomial by a coefficient height polynomial in the input bit length, unless trial division has already succeeded. The theorem constructs a cyclic cubic extension with a suitable integral element $\alpha$. Its projection $\beta=\sigma(\alpha)/\alpha$ has norm one. After multiplying by a positive denominator $A$, the integral element $A\beta$ has norm $A^3$. Its mixed quadratic signs at the split prime force it to be nonrational. Its degree-three minimal polynomial therefore has constant term $-A^3$ and positive square discriminant. The proof applies to every supplied positive multiple of $p^2+p+1$. Through height $H$, candidate generation and the number of modular coefficient-gcd tests are each bounded by $H^{1+o(1)}$. [Order-splitting proof and trial division](cyclotomic-order-multiples.md#projection-to-the-cyclotomic-order)

The implementation uses exact integer and rational arithmetic. Two independent checks enumerate Eisenstein norms across the full $(a,b)$ box and directly substitute into the ordinary cubic discriminant. [Angular enumerator and checks](../experiments/cyclic-cubic-enumeration.py)

## Eisenstein factorization

Write
$$
 I=a^2-3b,\qquad J=2a^3-9ab+27c,\qquad 4I^3=J^2+27\Delta .
$$
For $\Delta=d^2>0$ with $d>0$, the Eisenstein integer $z=(J+3d\sqrt{-3})/2$ has norm $I^3$. The identity modulo four shows that $J,d$ have the same parity. If $\omega=(-1+\sqrt{-3})/2$ and $z=u+v\omega$, then $J=2u-v$, $v=3d$, and $I>0$.

The Eisenstein integers are norm-Euclidean, hence have unique factorization. For an inert rational prime $\ell\equiv2\pmod3$, its norm is $\ell^2$, so the exponent in $z$ is a multiple of three. For the ramified prime choose $\pi=1-\omega$, of norm three, with $3$ a unit times $\pi^2$. The exponent of $\pi$ in $z$ is also a multiple of three, since the exponent of three in $N(z)$ is just that exponent. For a split prime, choose the two factors $\pi,\bar\pi$ with $\pi\bar\pi=\ell$. Their exponent residues modulo three are either $(0,0),(2,1),(1,2)$. The latter two are supplied by $\ell\pi$ and $\ell\bar\pi$, respectively.

Thus $z=\epsilon N(\eta)\eta\lambda_1^3$, where $\eta$ contains at most one prime factor above each split rational prime, each to exponent one. In particular $\eta$ is primitive as an integer coordinate vector. Absorb the unit $\epsilon$ into $\eta$, and write $\lambda_1=r\lambda$, where $r>0$ is the gcd of the two coordinates and $\lambda$ is primitive. This gives
$$
 z=N(\eta)\eta(r\lambda)^3,\qquad I=r^2N(\eta)N(\lambda).
$$
The implementation permits every primitive $\eta$; the squarefree prime-factor condition is unnecessary for correctness because every generated pair still gives a cube norm. The factor exponents and $r$ are fixed for the displayed UFD decomposition, but this relaxed search can supply further representations. The work bounds count the candidates before deduplication. The two roles are both searched when the norm bins differ. When they coincide, searching one fixed assignment of roles suffices because each vector ranges over that same bin. Axis charts can overlap at their edges, and changing Eisenstein associates can also give duplicate triples. Final lexicographic sort and consecutive deduplication remove all repetitions with deterministic overhead.

## Angle restriction

Put $g=2I^{3/2}-|J|$. It satisfies $0<g\le 2I^{3/2}$ and
$$
 g=\frac{27\Delta}{2I^{3/2}+|J|}\ll\frac{H^2}{\sqrt I}.
$$
For $I\le H$, use $g\le2I^{3/2}$. For $I\ge H$, we have $a^2\le I+3H$, and the discriminant formula gives $\Delta\le(23I+100H)H^2$. Indeed $4|a|^3|c|\le4a^2H^2$ and $18|abc|\le18a^2H^2$ for integer $a$. Hence $2048H^2/\sqrt I$ is an upper bound in both ranges.

The algorithm loops over $r$, dyadic norm bins $[S,2S),[B,2B)$ with $S\le B$, and gap bins. Write $L=r^2SB$, so $L\le I<4L$. The first gap bin is $0<g\le64H$, and the later bins double the upper endpoint $D$. The test $g\le D$ is the integer comparison $4I^3\le(D+|J|)^2$. The last bin is the first to reach the bound from the preceding paragraph or $2I^{3/2}<16L^{3/2}$, whichever is smaller. Every processed $D$ is $O(H^2/\sqrt L)$, including the first bin since $L\le H^2+3H$.

The angle of $z$ is near either real ray. In fact $\sin^2(\arg z)\le g/I^{3/2}$. For $D/L^{3/2}$ small, this implies
$$
 |v|\le\kappa |2u-v|,qquad
 \kappa\asymp \sqrt D/L^{3/4},
$$
where $\kappa$ can be rounded up to a dyadic rational. The code rounds up $\sqrt{D/(L\lfloor\sqrt L\rfloor)}$; if the ratio under this square root is at least $1/16$, it permits the whole circle. The wider cone is harmless, and the total angular length is still $O(\sqrt D/L^{3/4})$.

For each of the $O(S)$ possibilities for the smaller vector, the larger vector appears to the first or third power in $z$. Its direction therefore lies in a bounded number of sectors of combined angular length $O(\sqrt D/L^{3/4})$. Use four charts, according to which of the two integer coordinates dominates and its sign. The other coordinate divided by the magnitude of the dominant coordinate is a slope $t\in[-1,1]$. In each chart the angle map of $t$ and its inverse have bounded derivatives: the unscaled complex vector is linear in $t$, its norm is between $3/4$ and $3$, and the angle derivative has magnitude $(\sqrt3/2)/N(w(t))$. The same upper bound times three applies after cubing.

The cone boundary equations are $v\pm\kappa(2u-v)=0$. After multiplication by the fixed smaller factor, the phase is strictly monotone in the chart. In each grid segment of length $1/4$ its change is below $\pi$, so each boundary equation has at most one crossing there. Opposite signs bracket the crossing, and endpoint zeros are retained directly. Bisect with exact rational arithmetic, retaining both root brackets and all intervening intervals that pass a midpoint sign test. An outward error $O(H^{-6})$ in slope suffices. This algorithm produces a bounded number of intervals of total length $O(\sqrt D/L^{3/4}+H^{-6})$.

## Exact reporting of primitive vectors

A primitive vector corresponds to a reduced fraction with denominator at most $Q=\lfloor2\sqrt B\rfloor$ in one of the slope intervals. Distinct fractions have spacing at least $1/Q^2$. The least such fraction at or above an interval endpoint is the upper continued-fraction bracket at denominator bound $Q$. When the next convergent exceeds $Q$, the final convergent and the largest allowed intermediate convergent bracket the endpoint and have determinant one. Their denominator sum exceeds $Q$, which prevents another reduced fraction of denominator at most $Q$ between them. If the endpoint itself has an allowed denominator, start there.

After $n/d$, obtain the next fraction $m/e$ by choosing the largest $e\le Q$ with $dm-ne=1$, or equivalently $ne\equiv-1\pmod d$. The resulting $e>Q-d$ again makes the pair consecutive. Extended Euclid gives the needed congruence, with $e=Q$ when $d=1$. Each start or successor costs $(\log H)^{O(1)}$ bit operations. The list has $O(1+B\sqrt D/L^{3/4})$ fractions per smaller vector. The code checks the norm bin and gap bin exactly after recovering the vector, and discards $v\le0$ and $v$ not divisible by three.

The per-job cost for pairs, before recovering coefficients, is therefore bounded up to polylogarithmic factors by
$$
 S+SB\sqrt D/L^{3/4}=S+L^{1/4}\sqrt D/r^2.
$$
This includes the expense of examining smaller vectors with empty intervals. All smaller vectors have norm $O(H)$; precomputing them by scanning the Eisenstein lattice disk costs $H^{1+o(1)}$. The relaxed representation causes no false positives because every resulting $I,J,v>0$ satisfies $4I^3=J^2+3v^2$, and the code requires $3\mid v$.

## Recovering the coefficients and bounding the work

Put $P(x)=x^3-3Ix$. An admissible $a$ satisfies $|P(a)+J|\le27H$. The three monotone integer blocks around $\pm\sqrt I$ can each be searched by two binary searches. For every reported integer calculate
$$
 b=(a^2-I)/3,\qquad c=(P(a)+J)/27
$$
and check divisibility and the box bounds.

For $I\ge H^{2/3}$, the cubic inequality implies $|a|=O(\sqrt I)$. In a gap bin beyond the first, $g>D/2\ge64H$, so $P(a)$ stays a distance $\gg D$ from both critical values $\pm2I^{3/2}$. Factoring
$$
 P(x)\pm2I^{3/2}=(x\mp\sqrt I)^2(x\pm2\sqrt I)
$$
shows that both distances $|a\mp\sqrt I|$ are $\gg\sqrt D/I^{1/4}$. At least one is $\ge\sqrt I$; hence $|P'(a)|\gg I^{1/4}\sqrt D$ throughout every admissible real interval. The program examines $O(1+H/(L^{1/4}\sqrt D))$ integers. In the first bin, one of the two factored products is $O(H)$. In the $\sqrt I$-neighborhood of its double root this restricts $x$ to width $O(\sqrt H/I^{1/4})$, and outside it the simple root lies within $O(H/I)$. The latter width is no larger for $I\ge H^{2/3}$. Thus the same integer-count bound holds with $D=64H$.

Multiplying the pair bound by the integer-count bound gives $O(H/r)$ per job, up to polylogarithmic factors. Indeed $L^{1/4}\sqrt D=O(H)$, and its product with the translation length $H/(L^{1/4}\sqrt D)$ is $H$. Also $S\le\sqrt L/r$, and $S\sqrt H/L^{1/4}\le\sqrt H L^{1/4}/r=O(H/r)$. Summing over the polylogarithmically many bins and over $1\le r\le O(H)$ gives $H^{1+o(1)}$.

For small $I\le H^{2/3}$, use an ordinary sieve and enumerate all Eisenstein elements of norm $I^3$ using exact prime factorization, as in the independent norm generator but only for these smaller $I$. An Eisenstein lattice disk of norm bound $H^{2/3}$ supplies a generator of each split rational prime up to this bound. Inert and ramified primes have unique exponent choices, and a split prime power $\ell^m\parallel I$ gives $3m+1$ choices. This is $I^{o(1)}$ elements per $I$, up to the six units. The inequality $|P(a)+J|\le27H$ implies $|a|=O(H^{1/3})$, so this part also costs $H^{1+o(1)}$.

For historical comparison, Xiao's Theorem 1.1 gives an $O(H\log^2 H)$ count for irreducible cubics in the same coefficient box. His proof uses related Eisenstein angular restrictions. The reporting step here uses exact Farey intervals, and the argument includes reducible cubics of positive square discriminant. [Xiao, *On monic abelian cubics*, §4](https://arxiv.org/pdf/1906.08625)

## Replay

From the repository root, run `python3 -B experiments/cyclic-cubic-enumeration.py`. The complete positive-square lists match both independent generators at eight heights through 64. At height 32 there are 1,333 positive-square cubics, including 184 with negative-cube constants. At height 64 the corresponding counts are 3,860 and 438. Pass `--list 64` to emit the negative-cube triples in lexicographic order. In the conductor-seven field, the projection from $X^3+X^2-2X-1$ has minimal polynomial $X^3-3X^2-4X-1$, discriminant 49 and norm one. Seven supplied multiples all split the same input 65 with this height-four polynomial. [Literal projection and gcd replay](../experiments/cyclotomic-multiples.gp)
