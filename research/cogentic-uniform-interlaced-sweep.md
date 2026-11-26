# A deterministic sweep for exact interlaced relations

A fixed chart search splits all twelve small semiprimes in its first cohort. Its same short window misses all six larger semiprimes. Extending the origin window and reducing every evaluation label to a short rational representative splits those six as well. Every large-cohort split comes from a certified order multiple, with no proper gcd from any screening step. [Interlaced field identities](cogentic-exact-local-circuits.md) · [Exact sweep](../experiments/cogentic-uniform-interlaced-sweep.py)

## A common-root search that only uses the input integer

Use degree two with evaluation $m=0$. For each step $2\le W\le160$ and offset $1\le h<W$, take the two triples of marks $a+jW$ and $a+jW+h$, $0\le j\le2$. As in the interlaced construction, let $F$ be the difference of their monic products divided by $h$. It has leading coefficient three. Put $\Delta=4W^2-h^2$ and $z=2(a+W)+h$. Then
\[
 F(0)=(3z^2-\Delta)/4,\qquad \operatorname{disc}(F)=3\Delta .
\]
Reject a square discriminant and $W^2\equiv h^2\pmod3$, the latter being the content test. Check squarefreeness of the three distinct absolute norm numerators
\[
 (W+h)(2W+h),\quad (W-h)(W+h),\quad (W-h)(2W-h).
\]
The norms on the translated triple appear in reverse order. The factors in these tests are at most $479$. A public sieve supplies their factorizations. This keeps 1,408 of 12,720 shapes, before any input modulus is read.

For a mark cap $A$, index the odd or even center candidates $1\le z\le2A$ by $3z^2\bmod N$. Each shape joins its $\Delta\bmod N$ to these buckets. Its feasible $a=(z-h)/2-W$ is then determined by parity and the requirement that all six marks lie in $[1,A]$. Since $N$ is odd, every feasible match gives $N\mid F(0)$. This finds the same roots as scanning all origins of all retained shapes. The implementation makes $O(A+\#\mathrm{shapes})$ dictionary lookups and visits $J$ shape-center matches, including those rejected by parity and window tests. Sorting the two lists gives a deterministic worst-case comparison bound with an additional logarithmic factor. The program checks norm and mark invertibility and uses every nonunit screening result only to reject the candidate.

## Rational evaluation labels and order extraction

An accepted six-mark word has product of its first three residues divided by the product of the other three equal to one modulo $N$. A mark may use any signed rational representative of its residue with invertible denominator. For a public height cap $C$, start the Euclidean algorithm with $N$ and the absolute centered residue $r$. Keep the coefficient of $r$ alongside each remainder. Stop at the first positive remainder $u\le C$, whose coefficient $v$ gives $u\equiv rv\pmod N$. Reject the chart if any $|v|>C$ or any denominator is a nonunit. The retained labels then have a prime valuation vector computed by a sieve through $C$, with the sign dropped. If $r>C$, the Euclidean determinant identity gives $|v|<N/C$. Thus a cap at least $\lceil\sqrt N\rceil$ guarantees the height bound. The wide sweep uses the smaller fixed cap 512 and counts its height misses.

Collect the signed sums of the label valuation vectors. Exact rational elimination keeps the provenance of each pivot and tests which single-prime vectors lie in the span. For such a prime $\ell$, clear the rational coefficient denominators to exhibit $E e_\ell$ as an integral sum of chart rows. This is checked by integer vector addition, so even a large exponent is never expanded as an integer power. The sign-free projection gives $\ell^{2E}\equiv1\pmod N$, which is verified directly. The splitting stage tests gcds after prime division of this exponent, using the same fixed list $2,3,5,7,11,13,17,19$. A trial with no projected vector, or with no proper gcd from the verified exponent, is a miss.

## Fixed cohorts and charged misses

The first cohort consists of products of the first twelve adjacent pairs of primes starting at $11$, independently of the chart search. The larger cohort similarly takes the first six adjacent pairs starting at $521$. These lists define the test inputs. The search receives only the resulting integers. The small and the short large-cohort runs both have $A=C=600$. The wide run on the larger cohort uses $A=128(1+\lfloor\sqrt N\rfloor)$ and $C=512$. All other bounds and the generator list are fixed. The implementation completes the full chart search even after it could have returned a hit.

| Cohort and window | Inputs | Root matches $J$ | Feasible charts | Admitted charts | Inputs split |
| --- | ---: | ---: | ---: | ---: | ---: |
| Small, short | 12 | 38,258 | 10,487 | 4,776 | 12 |
| Larger, short | 6 | 39 | 21 | 21 | 0 |
| Larger, wide | 6 | 3,854 | 1,956 | 1,601 | 6 |

The short small-cohort run rejects 5,711 charts on the norm screen and skips seven nonunit generators. Those screens could disclose proper gcds, which are excluded from the reported results. In both large-cohort runs there are no nonunit rejections. In the wide run all 355 rejected feasible charts fail the rational-label height cap. The hidden factors exceed 512, while every wide label and every prime in a marked value is at most 512. If a mark itself were a nonunit on an accepted shape, $N\mid F(0)$ would force a hidden factor of $N$ into that marked value. This gives a separate reason that these screening steps do not disclose factors in the wide run.

For example $N=272483$ has 671 root matches and 343 feasible charts in the wide window. Of these 337 are admitted and their rational-label row rank is 97. The exact elimination finds an 86-chart certificate for the valuation direction $86645694232138633020\,e_2$. Starting from twice this exponent, the first division by two still gives residue one and the next gives
\[
 2^{43322847116069316510}\equiv271961\pmod{272483},\qquad
 \gcd(271961-1,272483)=523 .
\]
The first-cohort input $221$ already splits in the short window using an eleven-chart certificate for $96\,e_2$.

The full root index can contain different signed center classes for the same discriminant. Comparing two such roots is a separate possible factorization route. A control at $272483$ kept only the first admissible class $\{z,-z\}\bmod N$ for each $\Delta\bmod N$ in the relation pool. It dropped 81 extra charts and kept 256. The resulting 89-chart certificate gives exponent $1142603024707663005240$ for the direction $e_2$, and the same order-exponent procedure splits off 523. Neither run compares pairs of centers by gcd.

The wide search scans order $\sqrt N$ center candidates. On this fixed quadratic chart with positive marks at most $A$, the real roots also lie in $[1,A]$, so $0<F(0)\le3A^2$. When $N>3A^2$ no such chart specializes. The finite sweep establishes that these small local relations can combine beyond a constructed modulus. The origin and label bounds do not supply a subexponential worst-case search.
