# Exact chart transport and integer lifts of square generators

Write $\ell=a-bm$ for the integer evaluation associated with a primitive mark. An exact chart rebase $m'=m+t$, $a'=a+tb$, $b'=b$ gives $a'-b'm'=\ell$. More generally a unimodular basis change acting on the mark and contragrediently on the evaluation functional preserves the integer label. It cannot change the rational matching matrix. A grid change may admit other marks, which is a different operation.

A linear integer lift of the evaluation functional has coefficients $(1+uN,-m+vN)$ with integers $u,v$. Its change on a mark is $N(ua+vb)$. If it still evaluates the integer $1$ to $1$, then $u=0$ and it is just a common base lift. Since $m<N/2$ on this schedule, every nonzero shift of $m$ by a multiple of $N$ has larger absolute value. An independent lift of each mark need not come from this linear chart. For two lifted labels $L=\ell+kN$, $L'=\ell'+k'N$,

$$
    b'L-bL' = ab'-a'b+(m'-m)bb' + N(b'k-bk').
$$

The bounded determinant argument from the [original matcher](cogentic-sheared-local-squares.md) survives when $b'k=bk'$. Without this condition, it no longer forces large repeated primes to correspond to the same sheared mark. It gives no structural exclusion of new matches for independent lifts.

A separate short-height exclusion concerns transporting rational square factors. Suppose two original labels satisfy $|\ell|,|\ell'|\le U$ and $|x|,|y|\le T$. If $2UT^2<N$, then $x^2\ell\equiv y^2\ell'\pmod N$ implies the integer equality. A congruence through such small scaling factors was therefore already present in the original rational classes. This does not exclude a relation involving longer products of local generators.

## Fixed integer-lift experiment

Before collection, fix the three 40-bit integers in [the published scaling cohort](cogentic-sheared-size-scaling.md), in their original order. Use its six quadratic fields at height 64 and their exact field-square generators, with the original generator order. There is no field or grid change. Record the original exact-label rational nullity on all generators and separately on exactly the generators retained by the lift rule.

For each field-square generator, evaluate its signed mark product modulo $N$. Take the centered representative $c\in[-(N-1)/2,(N-1)/2]$. Among $c+kN$ in order $k=0,1,-1,2,-2,\ldots,128,-128$, retain the first whose absolute value is 251-smooth. Drop generators without such a representative. Use the exact sign and prime parity of each retained integer label. Eliminate in inherited column order and check at most 32 basis vectors, stopping at the first verified proper gcd. If the lift-only basis is exhausted without a split and budget remains, append public witnesses in increasing $t$ order. Take $u=\lceil\sqrt N\rceil+t$ for $0\le t\le63$, and retain $(u^2-N,u)$ only if $u$ is a unit and $u^2-N$ is positive and 251-smooth. Any proper gcd of $u$ with $N$ is recorded separately. Test only newly created candidate rows, sharing the original 32-test and wall budgets. This records whether the lift-only domain already suffices. Use one process per input in sequence with a 15-second wall cap including collection and lift search. No retries, mark-gcd searches, cap changes or alternate lift assignments. Validate any returned certificate independently after all inputs finish.

This is a fixed representative per local basis generator. It need not extend to an integer chart on the marks. For an admitted dependency, XOR the original masks in each field to obtain one exact square there. To recover the product of the original generator roots, multiply that field root by the evaluation of the half-product of repeated marks and signs. This accounts for every factor removed by the XOR. Divide the resulting root product by the exact positive square root of the product of the chosen lifted labels. The square of the normalized residue is one because every lift is congruent to its original evaluation. A proper difference gcd is checked directly. Enumeration of lifts and exact trial division fit $\exp(O(W))$ bit work if the number of generators and both bounds are $\exp(O(W))$. The construction does not guarantee smooth representatives or productive signs.

## Fixed-run outcome

The amended plan `d336d0a1d5b4591890f06375e07502f6a94a020d` was published before the search. The three inputs completed once, in order, with the limits above. [Replay](../experiments/cogentic-sheared-integer-lifts.py) · [Full records](../experiments/cogentic-sheared-integer-lift-results.jsonl)

| Input | Local generators | Retained lifts | Full / retained original nullity | Lift nullity | Public witnesses | Extended nullity | Seconds |
| ---: | ---: | ---: | :--- | ---: | ---: | ---: | ---: |
| 892461594611 | 45 | 0 | 0 / 0 | 0 | 4 | 0 | 0.864 |
| 804097083799 | 351 | 6 | 0 / 0 | 0 | 4 | 0 | 1.544 |
| 810761370127 | 177 | 2 | 0 / 0 | 0 | 1 | 0 | 1.129 |

All cases exhausted the lifted matching space. There were no exact candidate queries, proper public gcds, or square certificates. Appending the nine public witnesses supplied no new dependency. The three cohorts' prime labels were regenerated separately with PARI after the run. The arithmetic path was independently checked on the existing $N=65$ lift example, where PARI confirmed the two field roots, and on a repeated-generator control that normalizes to a trivial modular sign.

A noncentral lift has absolute value at least $(N+1)/2$. If it is $B$-smooth it must contain at least $\log(N/2)/\log B$ prime factors counted with multiplicity. The recorded scarcity at the small bounds is consistent with that exact size burden. The result leaves open other fixed assignments and longer products. It supplies no reason to alter the time or candidate caps in this study.
