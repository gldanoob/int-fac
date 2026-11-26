# The fifth mixed candidate at 358395019

A targeted continuation on the same admitted height-256 grid split $358395019=16333\cdot21943$ on its fifth exact candidate. The four earlier ratios and supports match the [frozen validation](cogentic-monic-fresh-validation.md). This run was designed after that validation and its split is outside the frozen 3/10 result.

## Predeclared continuation

Use the same scheduled argument $m=18931$, three fields $F,G,G+4(X-m)$, unsigned primitive marks, packed mark-local collector and prime cutoff $2\cdot256^2$. Start with the same normalized probes through 257. Visit a basis in increasing support size, with ties in original elimination order. If a nonsquare is detected, double the probe cutoff, intersect with the new rows, sort that basis by the same rule and reuse previous exact mask tests. The caps were 1,024 completed exact tests, 45 seconds for adaptive probing and exact recovery, and 70 seconds wall time for the whole command. The search took no factor data.

The admitted column counts were $(28884,14738,15561)$, with core counts $(2405,1730,1277)$. The stacked ideal kernel had dimension 315 and the normalized probes left dimension 308. All three admitted two-field ideal intersections had nullity zero. The first round reached the split, so longer probes were unnecessary.

| Exact test | Field support sizes | Normalized ratio modulo $358395019$ |
| ---: | ---: | ---: |
| 1 | 664, 548, 234 | $-1$ |
| 2 | 678, 560, 212 | $1$ |
| 3 | 668, 566, 222 | $-1$ |
| 4 | 668, 578, 214 | $1$ |
| 5 | 668, 566, 238 | $305753761$ |

The fifth root tuple reduces to $(348400712,81297179,105631730)$. The product of the common point residues taken at half multiplicity is $3388789$. The normalized ratio has square one, and its difference from one gives gcd 16333. PARI independently recovered each exact field root and verified the CRT split. Search wall time was about 4.3 seconds. [Saved support and residues](../experiments/cogentic-monic-mixed-followup-certificate.json)

## Complete decision on admitted rows

The importable `decide` in the [follow-up driver](../experiments/cogentic-monic-mixed-admitted-complete.py) takes the three fields, common root and their admitted point rows. It tests the full unsigned intersection basis, including any pair-supported directions. The original frozen four-candidate prefix agrees here because its pair-supported span was zero. If a round's entire basis consists of exact squares and every ratio is global, the basis spans the exact unsigned square kernel and all its ratios are global by the [mixed sign homomorphism](cogentic-monic-mixed-complete.md#normalization-and-signs). A cap reports the number of exact tests and independent certified roots instead. The probe separation and termination argument applies to this finite admitted subspace as it does to the full grid.

The parity computation is complete relative to supplied correct rows for the admitted conservative columns. The decision leaves all excluded columns, other fields and signed products outside its domain. The positive witness does not require any negative search claim beyond that domain.

```sh
timeout 70s python3 -B experiments/cogentic-monic-mixed-admitted-complete.py
```
