# Preregistered sheared quadratic squareclass matching

The experiment uses the eight frozen public products in order, separate from the previous frozen and fresh cohorts. The generator samples two distinct primes in $[9000,50000]$, requires ratio at most two and a 29–32-bit product, and excludes previously used public inputs and any reuse of a prime within the new cohort. The public inputs and search schedule are fixed before any relation collection. The search reads only the products. [Frozen inputs](../experiments/cogentic-sheared-inputs.json) · [Separate generator](../experiments/cogentic-sheared-cohort.py)

Each input uses height 64 and the six exact-value quadratic fields, in base order $m=\lfloor\sqrt N\rfloor-j$ for $j=0,1,2$, and slope order $u=0,-1$. The constant is $N-m^2-um$. Each field uses all primitive modular unit marks in its own box and the existing exact discriminant-supported local square kernel. The global matching compares the rational squareclasses of the integer evaluations $a-bm$, with a sign coordinate for $-1$, across the different base arguments. The bounded prime cutoff is $(2+\max j)H^2=16{,}384$. The identical signed integer evaluation incidence on the same local generators serves as the control.

After preparing every field and its local square basis, admit fields greedily by the increase in matching nullity. Break ties by greater local square dimension, then the fixed candidate order. Test new matching basis vectors in elimination order and stop at the first verified proper square-root gcd or 32 exact certificate attempts. Record all public inputs and any failures or ceilings. Each input has a 15-second wall limit including preparation. No separate mark-gcd screen runs. A proper derivative gcd, if one occurs, is recorded separately from a square certificate.

## Bounded matching across base arguments

Write $M=\lfloor\sqrt N\rfloor$. At base $m=M-j$ the primitive mark $(a,b)$ has integer evaluation $s=(a+jb)-bM$. Its sheared coordinates $(a+jb,b)$ are still primitive. If a rational prime $p$ divides two evaluations of unit marks, their denominators are invertible modulo $p$. Therefore $p$ divides
[
(a+jb)b'-(a'+j'b')b=ab'-a'b+(j-j')bb'.
]
The determinant has absolute value at most $(2+J)H^2$ for shift spread $J=\max j-\min j$. Above that bound it vanishes, forcing equality of the primitive sheared pairs and hence of the integer evaluations. After stripping the bounded primes, distinct nonunit residuals are pairwise coprime. Record the sign, bounded prime valuation parities, and one row for each distinct nonsquare residual. A residual contributes a nonzero rational squareclass because it has an odd prime exponent unique to its group. This computes all rational squareclass dependencies on the evaluations without factoring any large residual. [Bounded norm squareclasses](cogentic-quadratic-grid-norms.md)

Each basis vector in a local field square space gives one column in the evaluation matrix by taking the XOR of the marked evaluation classes, including the field's sign. A kernel vector selects local generators. XOR the selected masks in each field, since repeated marks and repeated signs drop out by squares. The remaining local products are exact field squares. Recover their roots $r_i$ and evaluate them modulo $N$ using the unit derivatives. The product $S$ of the corresponding signed evaluations is an exact positive integer square by the rational incidence test, so $R=\prod_i r_i/\sqrt S\pmod N$ has $R^2=1$. A proper $\gcd(R-1,N)$ certifies the split.

Appending generator columns preserves the previous elimination dependencies in order. Thus greedy admission needs to test only the newly created basis vectors. The rank scores use all prepared local bases. Admission selects which matching dependencies to verify first. For a fixed tuple of local fields, the normalized root map on the full matching kernel is multiplicative up to global sign, since canceling a repeated generator removes exactly its known square evaluation. Therefore a full basis would decide whether this finite domain has a productive sign. The benchmark's attempt cap limits this decision when a nontrivial matching kernel has a long basis. An empty matching kernel exhausts the chosen domain immediately. All local preparation and rational matching steps take polynomial work in the explicit marked input size and bit lengths. [Mixed-field normalization](cogentic-monic-mixed-complete.md)

## Frozen results

The freeze commit `55f5c1239340897ccc9ff44fb2ec9a8631eac9a4` fixes the public inputs and schedule. All eight cases finished in 1.87–2.88 seconds each. The identical signed integer evaluation kernel had dimension zero in every case. Rational matching produced seven splits, and every certificate uses evaluations with odd multiplicity in the identity-incidence model. Six certificates use two fields, including two with different base arguments. The final input uses one field. The unsplit case has nonzero local square dimension in all six fields and zero rational matching nullity. [Machine-readable results and certificates](../experiments/cogentic-sheared-results.jsonl)

| Public integer | Local square dimensions in candidate order | Rational match nullity | Attempts | Factors | Seconds |
| ---: | :--- | ---: | ---: | :--- | ---: |
| 788,001,211 | 628, 290, 772, 164, 319, 227 | 332 | 2 | 26,711 × 29,501 | 2.166 |
| 762,863,713 | 384, 358, 325, 107, 726, 550 | 350 | 1 | 25,633 × 29,761 | 2.015 |
| 543,805,489 | 645, 667, 343, 155, 585, 183 | 451 | 1 | 18,913 × 28,753 | 2.521 |
| 1,736,396,443 | 1,103, 722, 393, 285, 380, 253 | 670 | 5 | 38,053 × 45,631 | 2.209 |
| 1,929,208,469 | 386, 352, 419, 251, 277, 176 | 0 | 0 | — | 1.918 |
| 707,157,739 | 859, 652, 378, 212, 747, 187 | 727 | 2 | 22,279 × 31,741 | 2.884 |
| 391,681,673 | 525, 864, 677, 405, 359, 13 | 706 | 1 | 16,333 × 23,981 | 1.954 |
| 810,221,771 | 1,110, 606, 189, 388, 298, 271 | 615 | 1 | 25,913 × 31,267 | 1.872 |

Run `python experiments/cogentic-sheared-local-squares.py` to repeat the search. Add `--verify experiments/cogentic-sheared-results.jsonl` to verify the saved certificates without repeating it. The verifier independently recovers all 13 local roots in PARI, checks the exact integer square normalizations and proper gcds, and then checks the regenerated fixture factors. The search stage receives no fixture labels. No input hit the time or query limit, and no derivative gcd was used as a split. [Search and verifier](../experiments/cogentic-sheared-local-squares.py)

These are finite outcomes for a fixed small-input schedule. Rational matching expands what one can do with existing local squares. The centered quadratic density obstruction still applies when every local primitive mark has an odd private ideal valuation and the sign is nonsquare. On that density-one family the local spaces already vanish, regardless of the evaluation matching rule. [Centered-grid density obstruction](cogentic-centered-quadratic-density.md)
