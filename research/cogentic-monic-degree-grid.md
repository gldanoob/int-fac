# Degree and height on the frozen monic parity grid

The ten frozen semiprimes compare deterministic degree selection with two manual degree changes. All cases use the packed lattice collector on the same ordered public inputs. The degree parameter $d$ produces polynomials of degrees $d$ and $d+1$. The scheduled choice is $d=2$ for every input. [Frozen inputs and earlier height replay](cogentic-monic-blind-grid.md) · [Packed lattice collector](cogentic-monic-lattice-sieve.md)

## Fixed comparison

The seven batches were fixed before collection. Each ran all ten inputs in the existing order. At heights 64 and 128, the order was scheduled degree, then manual degree 3, then manual degree 4. The final batch used the scheduled degree at height 256. The prior manual-degree-3 result at height 256 supplies a reference from the same inputs and collection options.

Every run uses the repaired common root, primitive unit marks in $|a|\le H$, $1\le b\le H$, cutoff $2H^2$, mark-local acceptance, and the ramified row at two. Reference smoothness uses bound 151. A nonzero parity kernel would proceed to the normalized probes through 257, with up to 32 exact joint square tests and the five-second exact oracle budget. The replay logs degree, height, cutoff, shift, the exact column rank and nullity, and outcome for every input. Fixture factors enter only the final validation after all batches. [Runnable benchmark](../experiments/cogentic-monic-degree-grid.py)

For rank, delete any column hit by a row with exactly one live entry, since that row forces the column's coefficient to zero in every dependency. Each deletion removes one rank, and the remaining nullity is computed by the existing packed binary elimination. The replay compares this calculation against direct packed elimination for all 30 height-64 cases. A separate full-matrix check also matched all ten height-256 ranks. The rank totals add the ranks of the separate input matrices.

## Rank and split results

| Height | Degree mode | Prime cutoff | Columns | Total rank | Total nullity | 151-smooth | Inputs split | Seconds |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | Scheduled (2) | 8,192 | 2,732 | 2,732 | 0 | 16 | 0 | 1.46 |
| 64 | Manual 3 | 8,192 | 2,590 | 2,590 | 0 | 31 | 0 | 1.44 |
| 64 | Manual 4 | 8,192 | 1,522 | 1,522 | 0 | 44 | 0 | 1.44 |
| 128 | Scheduled (2) | 32,768 | 15,521 | 15,521 | 0 | 17 | 0 | 3.74 |
| 128 | Manual 3 | 32,768 | 12,044 | 12,044 | 0 | 31 | 0 | 4.11 |
| 128 | Manual 4 | 32,768 | 5,748 | 5,748 | 0 | 44 | 0 | 3.98 |
| 256 | Scheduled (2) | 131,072 | 79,998 | 78,092 | 1,906 | 19 | 2 | 25.74 |
| 256 | Manual 3, earlier run | 131,072 | 53,766 | 53,766 | 0 | 31 | 0 | 17.7 |

Each cell below gives the rank at the indicated height and degree. At height 256 and scheduled degree, the column count is the sum of the last rank and its nullity. For all smaller grids the column count equals rank.

| Public integer | 64 / 2 | 64 / 3 | 64 / 4 | 128 / 2 | 128 / 3 | 128 / 4 | 256 / 2 | 256 / 2 nullity | Factors from exact squares |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| 341,854,927 | 223 | 274 | 213 | 1,291 | 1,308 | 739 | 7,010 | 0 | — |
| 824,552,227 | 527 | 203 | 185 | 2,630 | 894 | 653 | 11,173 | 1,659 | 19,309 × 42,703 |
| 647,911,657 | 336 | 262 | 127 | 1,827 | 1,233 | 476 | 9,215 | 247 | 20,947 × 30,931 |
| 641,626,049 | 263 | 286 | 148 | 1,411 | 1,257 | 583 | 7,298 | 0 | — |
| 310,556,537 | 270 | 231 | 79 | 1,540 | 1,144 | 351 | 7,983 | 0 | — |
| 449,508,911 | 240 | 352 | 216 | 1,486 | 1,545 | 811 | 7,788 | 0 | — |
| 2,363,084,519 | 265 | 260 | 83 | 1,545 | 1,211 | 362 | 8,042 | 0 | — |
| 929,070,139 | 132 | 215 | 95 | 962 | 1,084 | 392 | 5,169 | 0 | — |
| 516,173,501 | 209 | 239 | 207 | 1,285 | 1,162 | 708 | 6,470 | 0 | — |
| 422,536,969 | 267 | 268 | 169 | 1,544 | 1,206 | 673 | 7,944 | 0 | — |

The 68 zero-nullity cases reached no exact queries. The two nonzero-nullity cases survived the probes and returned verified splits before both searches hit the five-second oracle deadline while extending their square bases. They completed six and four square queries respectively. No derivative split, discriminant error, or collection error occurred. The final validation checked every result against the frozen fixture.

For the first split, the sign is $-1$, the square residue is 117,335,942, and the two root evaluations are 423,486,851 and 382,876,298. Their difference gives gcd 42,703. For the second, the sign is $+1$, the square residue is 67,165,888, and the root evaluations are 52,717,150 and 10,969,779. Their difference gives gcd 20,947. The finite fixtures retain the full 477- and 516-mark supports, coefficients, and residues. [Exact split fixtures](../experiments/cogentic-monic-degree-certificates.json)

Doubling height from 64 to 128 raised total rank by factors of 3.78–5.68, a larger change than switching degree at either fixed height. All three degree choices still gave independent columns. At height 256, selecting the scheduled quadratic/cubic pair instead of the earlier manual cubic/quartic pair made the difference between two verified splits and none. The scheduled pair also required the larger grid to reach any dependency. The observed split gain therefore depended on both parameters. Because the cutoff scales with height, this benchmark measures the combined change in mark box and prime cutoff. The plan covered manual degree 4 only through height 128.
