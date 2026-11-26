# Bounded extraction with automatically scheduled degrees

The ordered holdout inputs are $187,209,247,299,391,437,10403$. The replay takes the degree from the existing schedule and runs the [common-root repair](cogentic-monic-index.md) on the resulting pair. A proper derivative gcd ends the case as a direct split. For an accepted pair, scan primitive marks with $|a|\le64$ and $1\le b\le64$ and retain simultaneous norms smooth at bound $151$, excluding primes dividing either polynomial discriminant. A nonunit mark value $a-bm$ contributes to a separate count of direct proper gcds and is omitted from the relation matrix. The remainder of the scan proceeds even after a direct mark gcd.

The parity extraction checks the first $\min(255,2^k-1)$ mask combinations of the GP kernel basis of nullity $k$, in increasing numerical order. Each candidate uses both common signs, exact field square tests and derivative-cleared evaluation. Finite unit correction takes each field's exact root for the positive sign if present, then the negative sign, and searches $1$ and $X+c$ for $-8\le c\le8$ if both signs supply no root. The word search keeps at most four distinct power-order units across both fields, drawn from each product support's original and reflected marks. At most 128 words are tested in increasing total absolute exponent, with total at most eight. All seven GP cases share a 15-second timeout. The inputs and bounds were fixed before execution.

The existing manual cubic/quartic $323$ fixture serves as a positive unit-correction control. For a separate uncorrected-square control search, scan odd $N$ from $9$ through $255$ in order, using each automatic degree and the same repair and search limits. Skip cases where repair returns a direct factor and stop at the first case with an uncorrected square split, or after the fixed range. This control search also uses a 15-second GP timeout.

## Holdout results

Run `python3 -B experiments/cogentic-scheduled-split.py` from the repository root. All seven automatic degrees were two. The first six pairs passed derivative repair at shift $t=0$. The last case returned the proper derivative gcd $103$ at $m=101$, before relation collection.

| $N$ | Common argument | First proper mark gcd | Mark gcds | Retained marks | Parity nullity | Dependencies tested |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 187 | 13 | 11 | 658 | 8 | 0 | 0 |
| 209 | 13 | 11 | 631 | 53 | 0 | 0 |
| 247 | 15 | 13 | 581 | 27 | 0 | 0 |
| 299 | 17 | 23 | 548 | 8 | 0 | 0 |
| 391 | 19 | 17 | 468 | 22 | 0 | 0 |
| 437 | 19 | 23 | 456 | 23 | 0 | 0 |

The holdout finished in about half a second. It yielded six direct mark splits and one derivative split. The six relation matrices had full column rank, so both square extraction counts were zero. The direct gcds are finite small-input successes. In particular the broad mark grid encounters many nonunit residues for these moduli.

For each accepted pair the GP output gives $N$, the lower degree, $m$, the repair shift, the proper mark gcd count and first such certificate, the retained mark count, parity nullity, masks tested, the signed-square results, the unit-correction results, and the number of tested dependencies supported on more than one mark. Signed-square results contain the number of simultaneous exact square sign choices, the number yielding a proper divisor and the first certificate. Unit-correction results contain the number of dependencies supplying two base roots, the number of unit words tested, the number of dependencies yielding a proper divisor and the first certificate. A pair of identical sign corrections is counted under signed squares only.

## Extraction controls

The ordered uncorrected-square control search timed out under the fixed bound. A rerun that printed progress completed the accepted cases through $81$ before timing out. There was no uncorrected square split among the reported cases. The automatic $N=27$ control retained 73 marks and had nullity 18. All 255 tested masks had support on multiple marks. There were 127 simultaneous exact square sign choices and 1,088 unit words tested. All checked congruences yielded trivial difference gcds. This agrees with the fact that an odd prime power has only the two trivial square roots of one.

The manual $N=323$ control reached one dependency and split only through unit correction. Its 16th tested word yields roots with residues $72$ and $4$, both squaring to $16$ modulo $323$, and the difference gcd returns $17$. The [unit correction proof](cogentic-monic-unit-corrections.md) gives the corresponding exact polynomial identities.

Both exact extraction controls can be replayed from the `experiments` directory.

```sh
gp -fq <<'GP'
cogentic_as_library=1;
read("cogentic-quadratic-order.gp");
read("cogentic-monic-pair-relations.gp");
read("cogentic-monic-unit-corrections.gp");
read("cogentic-scheduled-split.gp");
iferr(print(scheduled_split(27,2,5,0,[[2,0,1],[2,0,-4,1]])),err,print(err);quit(1));
iferr(print(scheduled_split(323,3,5,0,[[-2,0,8,1],[-2,0,8,-4,1]])),err,print(err);quit(1));
GP
```

The replay uses PARI for maximal-order initialization, ideal verification and exact field square tests. Every returned root is squared and checked in its polynomial quotient. For its modular image the replay first multiplies the root by the polynomial derivative, checks integrality of the reduced coefficients, and then divides by the invertible derivative value modulo $N$. Every proposed split passes a modular congruence and proper gcd check. The fixed grid, mask budget and candidate units give no dependency-supply or square-extraction success guarantee as $N$ grows.
