# Nearby odd bases on the frozen quadratic grid

A first comparison on the [ten frozen inputs](cogentic-monic-degree-grid.md) produced two exact square splits at height 256 using the scheduled degree $d=2$. This follow-up retains that degree and tests two nearby odd arguments per input. It begins with rank-only measurements for the original arguments. All construction choices use the public integers and coefficients. The search receives none of the fixture factors. [Replay](../experiments/cogentic-monic-nearby-bases.py)

## Why the original columns differ

Write the quadratic as $F=X^2+sX+C$ and the cubic as $G=F+(X-m)X^2$. The two original successes have the smallest absolute quadratic discriminants and the fewest occupied quadratic parity rows per retained joint column. The table gives the actual occupied odd-valuation rows in each field, and the number of columns remaining after all singleton-row eliminations. Each eliminated column is forced out of every dependency. An empty core therefore proves full column rank. A nonempty core can still have full column rank, as exact elimination confirms for four of the eight failures.

| Public integer | $C$ | $s^2-4C$ | Columns | Quadratic / cubic rows | Core columns | Nullity |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 341854927 | 11806 | −47224 | 7010 | 4347 / 5858 | 0 | 0 |
| 824552227 | 1002 | −4008 | 12832 | 5281 / 7733 | 4682 | 1659 |
| 647911657 | 5542 | −22164 | 9462 | 4378 / 7061 | 1944 | 247 |
| 641626049 | 17150 | −68596 | 7298 | 4401 / 5490 | 714 | 0 |
| 310556537 | 21654 | −86612 | 7983 | 4653 / 6170 | 402 | 0 |
| 449508911 | 26510 | −106040 | 7788 | 4706 / 5887 | 0 | 0 |
| 2363084519 | 55198 | −220792 | 8042 | 4688 / 5953 | 985 | 0 |
| 929070139 | −21218 | 84888 | 5169 | 3626 / 4789 | 0 | 0 |
| 516173501 | −24898 | 99596 | 6470 | 4105 / 5159 | 0 | 0 |
| 422536969 | −12166 | 48668 | 7944 | 4407 / 6057 | 875 | 0 |

For a negative quadratic discriminant, completion of the square gives $F_{\rm hom}(a,b)\ge (C-s^2/4)b^2$. A quadratic norm at most the parity prime cutoff 131,072 can therefore use denominators at most 11 and 4 on the two successes, versus at most three on each other positive-$C$ baseline. For the negative-$C$ cases the cubic gives a different restriction. If $|a|\le H$ and $b\ge1$, set $t=a/b$. Then

$$
 b^{-3}G_{\rm hom}(a,b)\le -(m-1-H)t^2+st+C\le C+\frac{s^2}{4(m-1-H)}.
$$

Here the correction is less than one, so the cubic has absolute norm greater than $(|C|-1)b^3$ throughout those boxes. These inequalities bound small norms, not smooth norms of arbitrary size. The occupied rows and exact kernel are the rank diagnostics. Neither the total row count nor the small-prime root score alone separates all outcomes. In particular, the sum of occupied rows exceeds the column count even for the original successes.

## Frozen shifts and exact outcomes

Before any collection, form $m'=m-2j$ for $j=1,2$. At each $m'$, recompute the parity-corrected base digits of $(N-m'^2)/2$ and use the same monic quadratic and cubic formulas. Odd $m'$ makes the parity carry valid, so the construction preserves monicity, Eisenstein at two and exact common value $N$. If $s=2q$ and $C=2c$, the shifted half-constant is the unique odd representative of $c+2jq+2j^2$ modulo $2m'$, in $[-m',m')$. A wrap subtracts $2\ell m'$ from the translated half-constant $c+2jq+2j^2$ to put it in that interval, with a compensating change in the linear term. Equivalently, the new quadratic is

$$
 F_{m'}(X)=F_m(X+2j)+4\ell(X-m').
$$

Here $\ell=0$ on all 20 planned shifts and no derivative repair was needed in any executed case. Thus the quadratic discriminant is unchanged. Its marks are sheared from $(a,b)$ to $(a+2jb,b)$. The cubic is genuinely changed, since $G_{m'}(X)-G_m(X+2j)=-4j(X-m')(X+j)$. A new dependency can therefore occur even when the quadratic discriminant stays fixed.

For each input rank the two shifts by the exact rational sum of their counts of eligible simple affine roots in both fields, weighted by $1/(p+1)$ at each odd prime $p\le43$. Prefer smaller $j$ at a tie. This order was frozen before examining any relation set. The packed collector, height 256, prime cutoff 131,072, mark-local checks and ramified row at two match the preceding comparison. Use the compact parity core, normalized probes through 257, a total of at most three exact joint queries per input across both shifts, and stop on the first verified square split. The five-second exact oracle budget applies per attempted pair. No direct mark gcd is used as a split. A dash in the survivor column means zero parity and no probe stage.

| Public integer | $j$ | Columns | Core columns | Nullity | Survivors | Exact queries | Square divisor |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 341854927 | 1 | 9004 | 1794 | 177 | 177 | 2 | 33071 |
| 824552227 | 2 | 10418 | 2773 | 545 | 543 | 3 | 42703 |
| 647911657 | 1 | 14101 | 5667 | 2365 | 2363 | 2 | 30931 |
| 641626049 | 2 | 9380 | 1898 | 212 | 208 | 1 | 43651 |
| 310556537 | 2 | 8634 | 1113 | 0 | — | 0 | — |
| 310556537 | 1 | 8408 | 1045 | 0 | — | 0 | — |
| 449508911 | 2 | 7375 | 0 | 0 | — | 0 | — |
| 449508911 | 1 | 7283 | 0 | 0 | — | 0 | — |
| 2363084519 | 1 | 4957 | 0 | 0 | — | 0 | — |
| 2363084519 | 2 | 5910 | 0 | 0 | — | 0 | — |
| 929070139 | 2 | 4810 | 0 | 0 | — | 0 | — |
| 929070139 | 1 | 4375 | 0 | 0 | — | 0 | — |
| 516173501 | 2 | 6203 | 0 | 0 | — | 0 | — |
| 516173501 | 1 | 7361 | 0 | 0 | — | 0 | — |
| 422536969 | 2 | 8150 | 847 | 0 | — | 0 | — |
| 422536969 | 1 | 7894 | 514 | 0 | — | 0 | — |

The shifted rule split four inputs, including two of the original eight zero-parity failures. The recorded run took 49.0 seconds including ten baseline ranks. All other inputs exhausted the two shifts at zero parity. The script emits the full signed support and modular residues, and the independent maximal-order square check runs after all solver trials. The two new certificates have 562 and 551 marks. Their two residues are respectively $(242175348,187740482)$ and $(618466023,521735407)$, with square residues 230393263 and 259877656. The verified difference gcds are 33071 and 43651. The rule is a bounded empirical improvement on this frozen set. A uniform supply or sign theorem remains open.
