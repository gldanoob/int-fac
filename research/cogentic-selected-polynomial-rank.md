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
