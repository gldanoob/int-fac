# Complete ideal coverage on the frozen monic grid

Complete ideal parity retained 61 additional marks across four of the ten frozen semiprimes at height 32. Each additional column increased rank by one, leaving every kernel trivial. The conservative and complete matrices agreed on the shared marks after relabeling ideal rows within each field and rational prime. [Runnable benchmark](../experiments/cogentic-monic-blind-exact.py) · [Frozen inputs](cogentic-monic-blind-grid.md)

## Fixed comparison

The timing pilot used the first public input. Complete collection took 0.349 seconds at height 32, and its height-64 run was still collecting when the pilot's 14-second wall limit expired. The comparison then fixed height 32 and cutoff 2,048 for all ten inputs. It ran them serially with one isolated process and six seconds of wall time per input, keeping the conservative result if the complete arm reached the cap. The scheduled degree yields quadratic and cubic fields in every case. Both arms use the same common-root derivative repair and primitive unit box. The comparison uses only the public integers.

The conservative arm uses bounded trial division, mark-local admission, and the ramified row above two. The complete arm computes exact local ideal valuations at all named singular primes and tests the parity of the private residual without factoring it. Both arms apply the same probes through 257 and allow at most three exact dyadic square queries when their parity kernel is nonzero. To compare ideal rows modulo naming differences, the replay compares the multiset of mark supports grouped by field and rational prime. It also records the named local primes responsible for each extra mark and whether the unstripped tail met a singular derivative. [Complete collector](../experiments/cogentic-monic-exact-grid.py) · [Exact dyadic square oracle](../experiments/cogentic-monic-dyadic-ascent.py)

## Results

The reported columns equal parity rank in every arm. The per-arm timings include rank and setup specific to that arm. The outer wall time includes process launch and SageMath import. The first arm took 0.471 seconds in total and the complete arm took 5.347 seconds, about 11.4 times longer. The ten isolated cases totaled 25.107 seconds of wall time.

| Public integer | Conservative rank | Complete rank | Added marks | Repeated singular norm prime in added marks | Conservative seconds | Complete seconds |
| ---: | ---: | ---: | ---: | :--- | ---: | ---: |
| 341,854,927 | 37 | 37 | 0 | — | 0.052 | 0.438 |
| 824,552,227 | 82 | 82 | 0 | — | 0.049 | 0.736 |
| 647,911,657 | 56 | 56 | 0 | — | 0.049 | 0.387 |
| 641,626,049 | 41 | 70 | 29 | Cubic, 3 | 0.047 | 0.891 |
| 310,556,537 | 34 | 34 | 0 | — | 0.048 | 0.294 |
| 449,508,911 | 34 | 34 | 0 | — | 0.049 | 0.797 |
| 2,363,084,519 | 45 | 45 | 0 | — | 0.045 | 0.804 |
| 929,070,139 | 22 | 37 | 15 | Quadratic, 3 | 0.042 | 0.278 |
| 516,173,501 | 30 | 43 | 13 | Cubic, 3 | 0.045 | 0.316 |
| 422,536,969 | 36 | 40 | 4 | Quadratic, 23 | 0.045 | 0.406 |
| **Total** | **417** | **478** | **61** | | **0.471** | **5.347** |

All ten cases finished within their limits. There were no derivative gcd splits, positive nullities, square queries, or verified splits. Every conservative mark was retained in the complete arm. Every additional mark had a repeated norm prime at a multiple root below the cutoff. No singular tail above the cutoff contributed to the increase. A separate PARI reference check on the 61 recovered marks confirmed that both private tails had even ideal valuations and that the counts of odd named-ideal rows agreed. These results give a finite coverage gain at height 32, while the larger boxes needed for the earlier frozen split certificates were outside this timing plan. [Independent PARI reference](../experiments/cogentic-all-ideal-reference.gp) · [Earlier height-256 splits](cogentic-monic-degree-grid.md)

The existing control at 895 exercised the benchmark's nonzero-kernel path. At the same height, complete nullity was 61 and the dyadic oracle verified a split after two calls. The control is outside the frozen totals.
