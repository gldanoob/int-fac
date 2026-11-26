# Common missed primes for symmetric and alternating elliptic charts

Any fixed finite menu of the four-mark polynomials with full symmetric or alternating Galois groups misses a positive density of primes, even if their splitting fields intersect. The two fixed sextics each miss exactly $53/144$ of the primes. A degree-ten resolvent of one sextic covers all its missed unramified primes, but its field cannot be realized by any of the four-mark polynomials. [Four-mark square identity](cogentic-square-mark-cycle.md) · [Elliptic reduction and rational orbit](cogentic-elliptic-mark-cycle.md)

## From a chart hit to a Frobenius fixed point

Put $A=(X-51)(X-95)$, $B=(X-57)(X-85)$, and let $T\in\mathbb Z[X]$. The polynomials in the family are
\[
 F_T=X+AB(T+AT^2),\qquad S_T=1+2AT,
 \qquad A-BS_T^2=-4F_T.
\]
At an odd prime and a value $x$ with $A(x)B(x)\ne0$, a root $F_T(x)=0$ is equivalent to a point of $y^2=A(x)B(x)$ with $y=B(x)S_T(x)$. For $p\nmid4845$, a root $F_T(x)=0$ automatically has $A(x)B(x)\ne0$. If either factor vanished, the formula for $F_T$ would force $x=0$, where $A(0)=B(0)=4845$. For a fixed monic irreducible $F_T$, outside its discriminant primes, the reduction has a root exactly when Frobenius fixes one of its roots in characteristic zero. In a compositum of the splitting fields of a finite menu, the primes that all charts miss correspond to the Galois elements whose projections have no fixed points in any of the root actions. [Chebotarev density theorem](https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf)

## A common derangement without disjointness

More generally, suppose finitely many monic irreducible polynomials of degrees $n_i\ge5$ have Galois groups $S_{n_i}$ or $A_{n_i}$ in their natural root actions. The Galois group $G$ of the compositum of their splitting fields is a subgroup of the product that surjects onto each factor. Its commutator subgroup $G'$ is a subgroup of the product of the $A_{n_i}$ that still surjects onto every factor, since each $A_{n_i}$ is perfect.

Such a subgroup is a product of simple factors linked diagonally by isomorphisms. For the induction, project off the last factor. The kernel in the last simple group is normal by surjectivity, so it is either the full last factor or trivial. In the first case the last factor is independent. In the second case the subgroup is the graph of a surjection from the earlier product to the last factor. The images of its simple factors are commuting normal subgroups of the last factor. Exactly one can be nontrivial, and that restriction is an isomorphism. Distinct alternating groups in the range have distinct orders, so each diagonal block links actions of the same degree.

In each $A_n$ there is a derangement whose automorphic images are all derangements. This follows by using order and centralizer size in $A_n$, which every automorphism preserves.

- For even $n=k+2$, take cycle type $(k,2)$, which has order $k$ and centralizer of order $k$ in $A_n$. Another element of $A_n$ with these invariants has at least two even cycles. Its centralizer in $S_n$ has order $2k$ because an even-length cycle gives an odd element of the centralizer. The product of its nontrivial cycle lengths is at least $2k$, since their least common multiple is $k$ and at least two are even. The centralizer formula then gives equality and shows all cycle lengths are distinct, including at most one fixed point. There are exactly two even lengths. If neither is 2, they are at least 4 and 6, and their sum is at most half their product minus two. Adding each further odd length preserves this inequality, contradicting total degree $k+2$ even with one fixed point. If there is a 2-cycle, the other nontrivial lengths are at least three and have product $k$. If there are two or more of them their sum is at most $k-3$, again too small. The type is therefore $(k,2)$.
- For odd $n$, take an $n$-cycle, of order and centralizer size $n$ in $A_n$. Any matching element has odd cycle lengths with least common multiple $n$. Their product is an odd multiple of $n$ at most $2n$, by the centralizer formula in $S_n$, so it equals $n$. Two or more nontrivial lengths would leave at least three fixed points, since the product of integers at least three exceeds their sum by at least three. Their factorial would force the centralizer in $S_n$ to exceed $2n$. Thus the element must be an $n$-cycle.

Choose one such element on each diagonal block of $G'$. Its images are derangements in every root action. The resulting conjugacy class has positive Chebotarev density and misses the entire menu. In particular for any fixed balance ratio greater than one, sufficiently large multiplicative intervals contain two distinct such primes. Their product defeats the fixed menu even if a different chart is allowed at each prime and the rational evaluation bases can vary arbitrarily with unit denominators. This argument leaves menus with exceptional Galois groups and growing or input-dependent menus open.

## Exact densities for the first charts

The factorizations below are all squarefree.

| Polynomial | Irreducible prime | A degree-one and a degree-$(n-1)$ factor | A transposition after powering |
|---|---:|---:|---:|
| $F_{-1}$ | 13 | 3 | 2, degrees $1,2,3$ |
| $F_1$ | 11 | 5 | 2, degrees $1,2,3$ |
| $F_{X+1}$ | 7 | 23 | 19, degrees $1,2,5$ |

In particular both sextics reduce modulo 2 to $X(X^2+X+1)(X^3+X^2+1)$, and cubing its Frobenius gives a transposition. The fifth power does the same for the octic row. Irreducibility makes each root action transitive. The stabilizer of the fixed point of an $(n-1)$-cycle is transitive on the other roots, so each group is doubly transitive. It therefore contains all conjugate transpositions and is the full symmetric group. The modular entries can be checked by repeated powering and polynomial gcds. In particular $F_{-1}\bmod 3=X(X^5+X^4+X^3+2X^2+X+1)$, with the quintic irreducible. The octic row also applies to $T=X+c$ whenever $c\equiv1\pmod{7\cdot19\cdot23}$. [Sextic irreducibility replay](cogentic-square-mark-cycle.md#a-productive-sextic)

Exactly $265$ of the $720$ permutations in $S_6$ have no fixed point, by inclusion–exclusion. Each sextic consequently misses a density $265/720=53/144$. For the two sextics together, the splitting fields have trivial intersection. Each $S_6$ has only one nontrivial proper quotient, its sign quotient, and the quadratic sign fields differ since Frobenius at 3 is even for $F_{-1}$ and odd for $F_1$. The two splitting fields cannot be equal for the same reason. Hence the density missed by both is $(53/144)^2$.

## A covering resolvent and its local obstruction

Let $\alpha_1,\ldots,\alpha_6$ be the roots of $F_{-1}$. For each unordered partition $I\mid I^c$ into two triples take the algebraic integer
\[
     \eta_{I\mid I^c}=\left(\sum_{i\in I}\alpha_i-\sum_{i\in I^c}\alpha_i\right)^2.
\]
The ten values are distinct. Equality of two squares would yield a rational linear root relation of coefficient sum zero, unless the partitions were the same. Applying each transposition to such a relation and subtracting forces its two coefficients to agree. All coefficients would then be equal and of sum zero, so the relation is trivial. The polynomial whose roots are these ten values is monic integral and irreducible because $S_6$ acts transitively on the partitions.

The sextic's derangements have types $(6),(4,2),(3,3),(2,2,2)$. In the even-cycle types, alternating two colors on each cycle gives a partition into triples that the permutation swaps. In type $(3,3)$, the cycles themselves are the triples. Every derangement thus fixes a resolvent root. Any other Frobenius already fixes a sextic root. This pair of polynomials has a root in at least one member at every prime unramified in the sextic splitting field. A Frobenius-fixed algebraic integer reduces to an element of the base residue field even when different roots of the displayed resolvent have the same residue.

The resolvent field has no degree-one place at 3. At that unramified prime the $(5,1)$ Frobenius cannot preserve a partition into triples. It has odd order so it cannot swap the triples, and neither triple can contain its orbit of size five. Every $F_T$, however, has simple root zero modulo 3 because $A(0)=B(0)=4845\equiv0\pmod3$ and $F_T\equiv X\pmod{(3,X^2)}$. Hensel lifting gives a $\mathbb Q_3$ embedding whenever $F_T$ is irreducible. This excludes the degree-ten resolvent field for every primitive generator of that field. The covering property alone supplies neither the fixed four-mark identity nor a mixed-sign modular root comparison.
