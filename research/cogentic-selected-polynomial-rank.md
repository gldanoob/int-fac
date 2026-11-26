# Exact finite rank scoring for quadratic coefficient selection

The replay compares three choices in the same four-coefficient box. The original conditional-expectation selector counts joint squarefree band marks. The unperturbed control takes the zero tuple. The rank method exhaustively scores every tuple before running the extractor on the chosen tuple. [Replay](../experiments/cogentic-selected-polynomial-split.py)

For each coefficient tuple, the rank method uses the extractor's homogeneous grid of height 250 and smoothness bound 300. The grid uses identical marks in both fields. It uses the same coprimality checks and excludes primes whose squares divide the corresponding discriminant. A column records both fields' valuations with separate coordinates for each field, prime and root. The score counts how many eligible rational-prime targets lie in the exact rational column span. Each target has a one at both first-field roots of its prime and zero elsewhere. Different targets use disjoint coordinates and so contribute independent directions. The tie-breaks maximize the column nullity, then rank, then choose the lexicographically first coefficient tuple.

For each field’s eight coefficient choices, the scorer screens nonsmooth norms by repeated gcd with the factor-base product and caches the smooth marks. It joins the two fields’ records to build the exact matrix for each of the 64 pairs. It uses no modular order tests or factorizations of the input to choose coefficients. It runs the same bounded extractor on each selected pair and on both controls. Python checks each returned divisor and modular squaring chain, and compares the extractor's reported column count and rank with the scorer wherever it returns a certificate. The rank replay also checks examples where both target rows occur but their sum is outside the span, and where two independent directions and one repeated column put it in the span. [Rank scorer](../experiments/cogentic-selected-polynomial-rank.gp)

## Results

| Batch | Exact rank score | Smooth-mark selector | Unperturbed |
| --- | ---: | ---: | ---: |
| Original | 3/6 | 1/6 | 3/6 |
| Holdout | 3/6 | 2/6 | 1/6 |

On the original batch, the rank score and unperturbed control both split 77, 143 and 221. The smooth-mark selector split 77. Its two joint marks for 143 gave a matrix with 68 independent columns and zero eligible targets in its span. The rank choice for that input had 31 targets, rank 131 and 427 columns, and certified divisor 11. The largest target count among all 64 tuples was zero for each of 10001, 10203 and 10403, so none of the tuples can pass the extractor's rational-span check at these limits.

The fixed holdout is 187, 299, 437, 11021, 11663 and 12317. The rank score split the first three. The smooth-mark selector split 187 and 299, and the unperturbed control split 299. Every tuple had zero reachable targets for each of the three larger holdout inputs.

On holdout input 437, the unperturbed matrix had rank 132 and zero reachable targets. The exact score chose $(0,0,0,1)$ with lower rank 127 and 32 reachable targets, and verified divisor 19. The smooth-mark control also had zero reachable targets.

This finite comparison pays for full relation collection across the coefficient box. It gives no bound for replacing that work with conditional expectations or for achieving deterministic $L_N[1/3]$ factoring.

## Smaller norms on the fixed grid

The old box has slopes of magnitude at least $(N-7)/2$. For every searched $(a,b)$, $|a/b|\le H$ and $b\ne0$. Completing the square gives

$$
a^2+sab+cb^2 = b^2\left((a/b+s/2)^2+|s^2-4c|/4\right)
\ge b^2\left((N-7)/4-H\right)^2
$$

when $H\le(N-7)/4$. At $H=250$, every old norm on these six inputs exceeds five million. The grid stays far from the vertex of every old polynomial, including those with smaller discriminants inside the box.

The separate replay uses the existing extractor's small-slope convention with the single fixed pair $(s_1,s_2)=(0,-1)$. Set $m=\lfloor\sqrt N\rfloor$, $r=N-m^2$ and $c_i=r-s_i m$, so both polynomials equal $N$ at $m$. For nonsquare $N$, $1\le r\le2m$ and $1\le c_i\le3m$. The discriminants are negative and the two norms at $(1,1)$ are at most $3m$. This choice uses only $N$ and runs once per input, with the same height, smoothness bound, and identical-mark extractor as the three prior controls. [Replay](../experiments/cogentic-selected-polynomial-recenter.py)

| Input | Reachable targets | Rank | Columns | Verified divisor |
| ---: | ---: | ---: | ---: | ---: |
| 10001 | 27 | 108 | 470 | 137 |
| 10203 | 25 | 116 | 792 | 19 |
| 10403 | 33 | 133 | 442 | 103 |
| 11021 | 30 | 127 | 502 | 107 |
| 11663 | 29 | 125 | 339 | 109 |
| 12317 | 29 | 128 | 465 | 109 |

The smaller-norm pair split all six prespecified misses. The norm comparison explains the geometric difference between these parameter choices. It gives no uniform lower bound for smooth marks, rank, or certified splits.

The pair is used only when both discriminants are negative and their product is not a perfect square. The first test excludes square inputs such as 9. The second excludes coincident quadratic fields, as for 88 with discriminants $-28$ and $-63$. The exact tests and both fixtures are in the replay. For each returned certificate Python checks the annihilating exponent, recomputes the modular squaring chain and verifies the proper divisor.

A separate fixed fresh batch used products of primes $(127,131)$, $(127,193)$, $(137,139)$, $(137,251)$, $(151,157)$ and $(151,331)$. These products supplied the input fixtures. Coefficient selection received just the six integers.

| Fresh input | Reachable targets | Rank | Columns | Verified divisor |
| ---: | ---: | ---: | ---: | ---: |
| 16637 | 0 | 62 | 62 | — |
| 24511 | 0 | 77 | 77 | — |
| 19043 | 31 | 123 | 415 | 139 |
| 34387 | 0 | 81 | 81 | — |
| 23707 | 22 | 100 | 137 | 151 |
| 49981 | 25 | 118 | 122 | 151 |

The fresh batch split 3/6 with the same limits. The three misses had full column rank and no eligible target in the column span. `make check-one-third` runs both batches.
