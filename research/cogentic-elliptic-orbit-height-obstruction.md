# Height obstruction for short elliptic orbit searches

On a fixed elliptic curve, a rank-$r$ rational orbit box of radius $B$ supplies local factoring hits at only $O((B+1)^{r+2}/\log X)$ primes in $(X,2X]$. This counts the actual chord, tangent, chart and sign comparisons as well as hits of the main divisor. For the two independent steps on the four-mark chart it gives $O((B+1)^4/\log X)$. In particular the bounded two-list search misses a density-one set of balanced semiprimes at every one-third numerical cutoff, even if a larger finite library covers every local root condition. [Four-mark curve](cogentic-elliptic-mark-cycle.md) · [Modular branch checks](../experiments/cogentic-elliptic-cycle-split.py) · [Batched tests](cogentic-elliptic-batch-search.md)

## Counting prime support of a rational orbit

Let $E/\mathbb Q$ be fixed and let the points range over finitely many translates of
\[
               \biggl\{\sum_{j=1}^r i_j R_j:\ |i_j|\le C B\biggr\}
\]
for fixed rational $R_j$ and fixed $C$. Include other finitely many fixed-rank orbits separately. The canonical height quadratic form and its bounded difference from the $x$-coordinate height give $h(x(Q))=O((B+1)^2)$ at every finite rational point in the box. The same bound for $h(y(Q))$ follows from the Weierstrass equation. For a fixed rational function $f$ on the curve, or a fixed finite list of such functions, its defined nonzero value has numerator and denominator of log size $O((B+1)^2)$. This follows by writing it as a quotient of fixed polynomials in $x,y$ and clearing denominators. Finite points can also be represented by primitive integral projective coordinates of the same log size. [Silverman, canonical heights](https://www.math.brown.edu/johsilve/Wyoming/WyomingEllipticCurveJune7.pdf#page=80)

Take the product of the absolute nonzero numerators, denominators and projective denominators for these $O((B+1)^r)$ points. Each prime in the dyad dividing it costs at least $\log X$ of the total $O((B+1)^{r+2})$ logarithm. Fixed bad primes can be added to the list at constant cost. In particular, a prime outside the list has the following properties. Each rational finite point remains finite, each defined rational nonzero test value remains a unit, and an identically zero value remains zero. A rational point equal to $O$ stays at $O$ on every component.

## Exceptional additions and the final chart

The modular implementation uses a short Weierstrass model with $a_1=a_3=0$. Work at good odd primes. Write $U,V$ for the exact rational point operands corresponding to a proposed group operation. Use the box above large enough to include $U\pm V$, $2U$, and all the sums and differences tested by the chart. This only changes its radius by a fixed factor and its set of translates by a fixed finite set. The rank-two chart uses separately the row $P+iR_1$, the column $jR_2$, and their sums. The extra multiples of $P$ used by the replay form a rank-one sequence, with their own additions.

| Modular comparison | Rational prime-support test |
| --- | --- |
| An operand is locally at infinity | Its nonzero projective denominator vanishes at that prime. An exact rational $O$ follows the identity branch at every prime. |
| A nonvertical chord needs $x(V)-x(U)$ invertible | Equality of the reduced $x$ coordinates forces $V=U$ or $V=-U$ locally. If $U,V$ have unequal rational $x$ coordinates, both $U-V$ and $U+V$ are nonzero rational points, and one reduces to $O$. |
| Equal $x$ coordinates with mixed signs | If the equality is local only, the preceding row already accounts for it. If $x(U)=x(V)$ over $\mathbb Q$, then $V=U$ or $V=-U$ over $\mathbb Q$. The exact sign holds at every prime. Any additional local equality of signs away from exact two-torsion has $2U$ reducing to $O$. |
| Tangent requires $2y(U)$ invertible | For a rational point outside two-torsion, $y(U)=0$ locally exactly when $2U$ reduces to $O$. Exact rational two-torsion doubles to $O$ globally. |
| Invert the $x$ coordinate to obtain the chart $m=51-8976/x$ | A zero of nonzero rational $x$ lies in its numerator support. The rational zero is the excluded chart at every prime. |
| Test the divisor, marked factors or the two signs | Use the nonzero numerator of the corresponding fixed rational function of the output point, including $F(m)$ and $B(m)(1-2A(m))\pm y_{\rm chart}$. A rational zero gives the full modulus wherever its denominator is a unit. |

For primes outside this support, the chord, tangent and identity branches agree with the exact rational group operation. Induction then identifies every modular operand and result with the corresponding rational point reduction on every component. If the prime factors of an input all avoid the support, every displayed gcd is either one or the full modulus. This covers the test that takes a sign gcd only after the divisor has vanished at the full modulus. A rational point placed on a divisor can give a zero there on every reduction. A proper sign gcd still requires a nonzero value in the prime support, or an earlier exceptional denominator.

The same support applies to a product or resultant tree whose local root test is membership of a translated divisor. For the four-mark divisor, let $D$ be the finite set of points with $H(x)=0$, closed under negation. For a finite column point $V$, the projected coordinates of $D-V$ give candidate $x$ roots. If a translated point is $O$, then $V\in D$ locally, a single-point divisor test. Otherwise a row coordinate $x(U)$ equals one of those projected roots exactly when $U+V$ or $-U+V$ lies in $D$. These signed sums are in the same enlarged orbit box. One can equivalently inspect the chord numerator
\[
       n=(y(V)-y(U))^2-(a_2+x(U)+x(V))(x(V)-x(U))^2
\]
and denominator $d=(x(V)-x(U))^2$. A resultant with the linear polynomial $dZ-n$ tests $d^{\deg H}H(n/d)$ on the unit-denominator branch. The exceptional branch is the chord row above. Monic products and remainders used to batch these tests add no inversions of variable coefficients. A product can combine local hits or contain exact global hits, but extracting a proper gcd of one of the represented tests still uses this same support. The bound concerns these specified gcd branches and the stated translated-root predicate.

In the batched right-list preprocessing, duplicate abscissas use the same ordinate sign tests as in the table. For distinct right abscissas the derivative of their monic product evaluates to the product of the other abscissa differences, so its gcd and the subsequent tree descent also use the chord support.

There is an equivalent replay using a quadratic in the sum abscissa and taking its resultant with $H$. For unequal finite abscissas the two roots are $x(U+V)$ and $x(U-V)$. When $x(U)=x(V)=u$, its homogeneous specialization has one root at infinity and the other at the tangent abscissa if $f(u)\ne0$, where $y^2=f(x)$ is the curve. Indeed its affine specialization is $-4f(u)Z+f'(u)^2-4f(u)(2u+a_2)$. If $f(u)=0$, it is the nonzero constant $f'(u)^2$ at good primes, with both homogeneous roots at infinity. The sextic $H$ is nonzero at infinity outside fixed bad primes. An equality of abscissas at only one prime is already a chord event. For an exact rational equality, the finite root, when present, is $x(2U)$. If one list operand is exactly $O$, the root test is $H$ at the other point. In particular the top $x$ coefficient of the right-leaf resultant at a finite $V$ is $H(x(V))^2$: dividing its quadratic by $x^2$ as $x\to\infty$ gives $(Z-x(V))^2$. Thus the replay's degree-coefficient test for an infinity row is also covered. [Augmented filter and exact leaves](cogentic-elliptic-batch-search.md#a-polynomial-for-one-addition)

## Consequences for prime supply

For $p,q\in(X,2X]$, a successful search needs at least one prime in the support. The proportion of balanced prime pairs meeting it is
\[
             O\!\left(\frac{(B+1)^{r+2}}{X}\right)
\]
by the prime number theorem. For rank two a positive proportion therefore requires $B\gg X^{1/4}$ under a common per-dyad radius bound. An explicit two-list search of that radius has lists of length at least $N^{1/8-o(1)}$ when $N=pq\asymp X^2$. This is an obstruction to such bounded-range supply even with quasi-linear arithmetic in the list sizes. Allowing a catalogue of charts gives the sum of the support bounds. More generally, if the total logarithmic weight of all nonzero rational witness values in a dyad catalogue is $X^{o(1)}$, then only $X^{o(1)}$ primes there can be hit. Selection among these entries may depend on the full input.

A fixed number field for the points and functions gives the same estimate, with constants depending on the field. Use absolute heights and the ideals of numerator and denominator in place of rational integers. Their total logarithmic norm for a nonzero value is at most twice the field degree times its absolute height. Each rational prime below a prime ideal in the support again costs at least $\log X$. All choices among the finitely many conjugate lifts can be included over one fixed normal extension. Exact zero values reduce to zero through every compatible specialization.

A chart presented as a fixed rational function of $N$ can also fall under this obstruction. If its model, marked points and test functions have valid good specialization at $N=0$, then at every prime $p\mid N$ their local reductions come from that one specialization, away from its fixed exceptional primes. The same holds for a second parameter taken from a small catalogue with bounded aggregate specialized heights. Singular specialization and genuinely larger input-dependent chart choices require separate estimates.

## Availability of divisor roots

For the fixed sextic $F=X+AB(A-1)$ the displayed irreducibility certificate at 13 makes its Galois action transitive. Modulo 3 the factorization is $X(X^5+X^4+X^3-X^2+X+1)$ with irreducible quintic, as checked by the gcd with $X^9-X$. Modulo 23 the factors are $X+3$, $X^2-5$, and the irreducible cubic $X^3-7X-3$. These are squarefree factorizations. The 5-cycle rules out imprimitive block sizes two and three, and cubing the second Frobenius gives a transposition. A primitive subgroup containing a transposition is the full symmetric group, since the components of the graph of conjugate transpositions give an invariant block system. Thus the Galois group is $S_6$.

At a good root $m$ of $F$ the identity $AB=(B(1-2A))^2$ gives two curve points after the Möbius transformation, except at finitely many primes where chart data are singular or nonunits. The rootless density is therefore $265/720=53/144$ by Chebotarev, and the local divisor has a point at density $91/144$. This counts availability before imposing an orbit box. For any finite collection of covers isomorphic to this zero cover over quadratic extensions, take the multiquadratic compositum $K$ of the isomorphism fields and the splitting field $L$ of $F$. The intersection $L\cap K$ is fixed by $A_6$. The 130 even derangements in $S_6$ each lift to an automorphism of $LK$ acting trivially on $K$. Their primes have density $130/[LK:\mathbb Q]>0$ and miss all the covers simultaneously. An actual intersective library can have different covers. The rational-height count still applies to its short orbit evaluations. [Sextic irreducibility](cogentic-square-mark-cycle.md#a-productive-sextic) · [Chebotarev's theorem](https://www.college-de-france.fr/media/jean-pierre-serre/UPL9140953003901187132_14___Lectures_on_N_X.pdf)

## Short binary indices give a different problem

The radius bound is numerical. A vector of $O(\log N)$-bit indices can represent multiples of numerical size comparable to $p$ and therefore can have very large rational height. Its reduction can still be evaluated by binary doubling and addition using polynomially many modular operations. There is a precise sufficient certificate at this index scale. For each prime $p$ define
\[
       \Lambda_p=\{\mathbf i\in\mathbb Z^r:\textstyle\sum i_jR_j=O\pmod p\}.
\]
Its index is at most $\#E(\mathbb F_p)\le(\sqrt p+1)^2$. If $\Lambda_p\ne\Lambda_q$, a vector from a Hermite-normal-form basis of one lattice lies outside the other. Its coefficients are bounded by the corresponding lattice index. The modular group computation then gives a proper divisor either at an exceptional denominator or at the projective infinity test on the result. Thus a separating vector, when it exists, has short binary length. The supply problem is to find such vectors from $N$ uniformly, including inputs on which a given pair of orbit lattices agrees.

The finite arithmetic check verified the factor certificates at $3,13,23$, counted the derangements, and checked both boundary identities of the quadratic resultant by exact polynomial expansion.
