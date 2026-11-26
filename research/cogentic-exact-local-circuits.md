# Exact local relations in overlapping fields

Four quadratic fields with overlapping marks certify an order multiple and split $77$. Each field has only one finite-null mark direction, whose logarithms vanish identically. The example combines exact identities and rational evaluation labels, so it needs no full logarithmic Gram in any field. Interlaced marks give such individual identities in growing degree. Two separate bounds limit their use on arbitrary inputs. [Collective extraction](cogentic-collective-field-extraction.md) · [Order rank from rational labels](cogentic-rational-label-order-rank.md)

## Local conditions for collective extraction

At an ordinary prime $p$ coprime to the leading coefficient of $F$, squarefreeness of $F(a)$ suffices to identify its valuation row, even at a multiple root modulo $p$. The element $a-\theta$ is $p$-integral, and $v_p(\operatorname{Norm}(a-\theta))=v_p(F(a))$. If this valuation is one, exactly one prime ideal above $p$ divides $a-\theta$, with valuation one and residue degree one. For another squarefree mark $b$ divisible at $p$, that ideal is the same if and only if $a\equiv b\pmod p$. The forward implication follows by subtracting the two elements, and the reverse follows because an ideal above $p$ contains $a-b$ when $p\mid a-b$. Thus $(p,a\bmod p)$ gives the ordinary valuation row. This relaxation leaves the completely split target-prime condition in place.

The extractor also needs only the particular archimedean direction of the target. Let $V$ denote the integer finite, balance and matching rows, let $U$ denote the logarithm rows, and let $Vc_0=-E_0b$ for an integral vector $c_0$ and $E_0>0$. If $c_j$ is an integral spanning list for the kernel of $V$ over the rationals, the exact additional condition is
\[
 Uc_0\in\operatorname{span}_{\mathbb R}\{Uc_j\}.
\]
All these log vectors belong to the same product lattice of field-unit logarithms. Coordinate vectors in a lattice basis are integral, so real span membership here implies rational span membership. Clearing the denominators gives an integral target solution with zero logarithms. The membership test is effective even when the log image has deficient rank. Greedily select an independent tuple from $Uc_j$, then test whether $Uc_0$ increases its rank. Apply the unit-lattice exterior norm gap to that tuple and to its augmentation by $Uc_0$. In the span of an independent tuple the lattice intersection has covolume bounded below by the same packing argument, so the index and rational reconstruction bounds apply in the smaller dimension. The existing extraction precision estimates therefore still give polynomial bit cost in the explicit input dimensions. Equivalently, the real stacked rows need only have every dependency annihilate the augmented target vector $(b,0)$.

## Interlaced integer marks give exact identities

Let $k$ be an odd prime, take $W>h>0$ and set
\[
 A(X)=\prod_{j=0}^{k-1}(X-a-jW),\qquad B(X)=A(X-h),\qquad
 F(X)=\frac{A(X)-B(X)}h .
\]
The degree is $k-1$, with leading coefficient $k$. Signs of $F$ alternate at successive roots of $A$ because the two mark lists interlace, giving $k-1$ distinct real roots. At a root $\theta$ of $F$, the vector $+1$ on the roots of $A$ and $-1$ on those of $B$ gives $A(\theta)/B(\theta)=1$. The mark values, in absolute value, are products of $k-1$ cross differences taken from the nonzero $|jW-h|$ with $|j|<k$. The factor for $j=0$ cancels the denominator $h$.

One can make the marks squarefree and the field irreducible in growing degree. Choose a prime $p$ in a primitive-root class modulo $k$. Under the Dirichlet RH hypothesis, a bounded polynomial search in $k$ finds such a prime. [Bach and Sorenson, least primes in residue classes](https://doi.org/10.1090/S0025-5718-96-00763-6)

Let $L$ be the product of the primes at most $2k$ together with $p$, and choose $W=L2^j$ with $L^2\le2^j<2L^2$. Search for $h=1+Lt$ in $(W/3,2W/3)$. All the cross differences are pairwise coprime because a common prime would divide $W(j-j')$, hence would divide $L$, whereas $h\equiv1\bmod L$. They are also coprime to $k$. To ensure squarefreeness, for each offset and each prime $r>2k$ outside $L$, the condition $r^2\mid jW-h$ removes one class of $t\bmod r^2$. The excluded fraction is at most
\[
 O\!\left(k\sum_{r>2k}\frac1{r^2}+\frac{k\sqrt{kW}}{W/L}\right)=o(1),
\]
where the sum is over primes and only $r\le\sqrt{kW}$ need be tested. Thus enumeration and trial division take $\exp(O(k))$ operations. The marks relative to $a$ and the ordinary norm primes have size $\exp(O(k))$, with log norm heights $O(k^2)$.

Modulo $k$, $F$ is constant one by $W\equiv0\bmod k$, $h\equiv1\bmod k$ and the prime-power identity in characteristic $k$. This removes the only possible content prime. Modulo $p$ the polynomial has degree $k-1$, and the equation for its roots becomes $((X-a)/(X-a-h))^k=1$. The quotient omits the root of unity one. Frobenius permutes the remaining $k-1$ roots in a single orbit because $p$ is primitive modulo $k$. The polynomial is therefore primitive and irreducible over the rationals.

## Four fields that split 77

Take $N=77$ and $m=0$. Use the preceding formula with $k=3$ and the following four triples. In each row apply the displayed affine map to both lists of marks and transport $F$ by the inverse map. The column $F(0)/77$ refers to the base polynomial, before the affine map. Every transported field still evaluates to zero modulo $77$ at $m=0$.

| $(a,W,h)$ | Affine map | $F(0)/77$ | Discriminant | Absolute marked polynomial values, in the order $A$ then $B$ |
| --- | --- | ---: | ---: | --- |
| $(38,21,16)$ | $x$ | 170 | 4524 | $2146,185,130,130,185,2146$ |
| $(12,56,33)$ | $x-77$ | 241 | 34365 | $12905,2047,1817,1817,2047,12905$ |
| $(9,63,44)$ | $154-x$ | 299 | 41820 | $18190,2033,1558,1558,2033,18190$ |
| $(23,70,9)$ | $77-x$ | 307 | 58557 | $11771,4819,7991,7991,4819,11771$ |

The discriminants are positive nonsquares. The norm values are squarefree and coprime to $3\cdot77$. All evaluation marks are units modulo $77$. Actual mark overlaps include $80$ in fields 1 and 2, $38$ in fields 1 and 3, $-25$ in fields 3 and 4, and $54$ in fields 1 and 4. The six-column finite matrix in each row has rank five, with kernel generated by its signed mark vector. For a direct rank check, the following pairs of column indices occur as ordinary prime-residue rows. In each field they form a spanning tree.

| Field | Two-entry row supports |
| --- | --- |
| 1 | $35,24,34,16,15$ |
| 2 | $16,35,24,34,15$ |
| 3 | $16,35,24,34,15$ |
| 4 | $35,24,15,26,34$ |

For example $35$ denotes the pair of columns $3,5$. Since the generator has zero logarithms, the finite-null log image in every field is zero.

For a mark $u$, take the smaller positive representative of $u$ and $-u$ modulo $77$, and use its ordinary prime factorization. Taking the product on $A$ divided by the product on $B$ in each row gives
\[
 R_1=54/23,\qquad R_2=45/32,\qquad R_3=3/80,\qquad R_4=23/100.
\]
The respective congruences are $-1,-1,1,1$ modulo $77$. Canceling the primes $3,5,23$ in these four ratios forces the coefficient vector to be a multiple of $(3,-1,-7,3)$. For this vector
\[
 R_1^3R_2^{-1}R_3^{-7}R_4^3=2^{30}\equiv1\pmod{77},
 \qquad \gcd(2^{15}-1,77)=7 .
\]
All four rows are needed to isolate the prime $2$ in this rational-label span. This certificate uses the rational evaluation labels to cancel factors beyond equal marks. [Exact replay](../experiments/cogentic-exact-local-circuits.py)

## Limits on producing the local relations for a fixed input

In any exact finite-null relation in a single helper, a prime dividing the squarefree norm at a positively weighted support mark $a$ must occur at a negatively weighted support mark $b$ in the same prime-residue row. Hence the absolute norm at $a$ divides the product of the differences $|a-b|$ over the negatively weighted marks. The same holds with the signs reversed. If marks lie in an interval of length $A$ and every used norm has magnitude at least $X_-$, each sign needs at least $\log X_-/\log A$ marks. On the fixed schedule this is of order $D=V/H$. For a designated target field the same argument holds after omitting the compensated target prime from these products.

Independently planting that many marks with the existing cofactor CRT requires a much larger interval. The necessary cofactor congruences have period $\operatorname{lcm}(m-a_j)$ because the coefficient multiplying the cofactor at each mark is invertible. For $r$ distinct marks in $[0,A]$ one has
\[
 \log\operatorname{lcm}(m-a_j)
 \ \ge\ r\log(m-A)-\binom r2\log A .
\]
Indeed each pairwise gcd divides a nonzero difference of marks, and the product divided by all pairwise gcds is at most the least common multiple, prime by prime. If there are $\Omega(D)$ marks, take a fixed small positive multiple of $D$ as a subset. With $\log m\sim V/x$, $\log A\sim aH$ and $DV=\log N$, the displayed bound is then $\Omega(\log N)$. This blocks full independent CRT coverage at the short cofactor widths. It leaves correlated prescriptions within a small part of the period available.

There is a separate counting limit for exact identities with bounded exponents. With $b$ input bits, allow $O(D)$ integer marks of magnitude $\exp(O(H))$, exponents bounded by a fixed constant, and all integral $m$ of magnitude $\exp(O(V))$. A nontrivial balanced exact identity in a field forces its defining polynomial to divide the sum or difference of the two corresponding mark products. There are $\exp(O(V))$ possible such polynomials, with degree $O(D)$ and log coefficient height $O(V)$. Each supplies at most $O(D)$ primitive irreducible factors up to sign. The elementary polynomial root bound gives root size at most $\exp(O(V))$ for every factor, whose leading coefficient divides that of the original polynomial. Consequently each factor evaluated at any candidate $m$ has log magnitude $O(DV)=O(b)$, and is nonzero for degree at least two. Each such value has only $\exp(o(b))$ positive divisors. Thus the entire bounded-coefficient exact-circuit family can specialize at only $\exp(o(b))$ different $b$-bit moduli. The interlaced fields supply explicit local identities and a finite extraction, while a uniform improvement of the factoring exponent still requires a source of local directions for the actual target modulus.
