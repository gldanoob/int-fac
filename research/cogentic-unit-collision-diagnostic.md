# Local unit-chart collisions on a frozen nine-input cohort

The [published freeze](cogentic-unit-collision-search.md#proposed-fresh-cohort-diagnostic) is commit `97a4f5e5ae2c67d9f31e3861029744a33fd8d2a0`. It fixes three fresh balanced semiprimes at each of 40, 48, and 64 bits, parameters $t=2,3,5,7$, and left and right lengths 1,024, 4,096, and 16,384 respectively. Each of the 36 chart boxes has one matched control containing two sequences of public hash-generated units. The input order and concatenation used to generate the public cohort were unchanged.

The freeze described a 256-bit hash without naming the algorithm. SHA-256 was explicitly fixed for the controls before any search arm started, with the bytes, counters, and acceptance rules already fixed by the plan. The solver receives only the public integers. Each arm runs by itself in a child process with an eight-second wall cap. Reported wall times include startup and Sage import, and the computation times begin after imports. A timed-out arm has no computation time or claimed result. [Frozen plan](../experiments/cogentic-unit-collision-search.json) · [Runner](../experiments/cogentic-unit-collision-diagnostic.py)

Both arms use the same signed cross-difference detector. A local split records the first distinct modular pair giving a proper signed gcd, with its indices, residues, sign, product-bucket gcd, divisor, and cofactor. The separate square pass records equality of a pair of squares modulo all of $N$ and whether such a pair gives a proper gcd. The exact signed equality pass keeps the first $x_i\equiv\pm y_j\pmod N$ by increasing $i$ and $j$, with the positive sign first. A global square alignment need not be an exact signed root equality. [Detector and proof](cogentic-unit-collision-search.md) · [All 72 arm records](../experiments/cogentic-unit-collision-search-results.jsonl)

## Results

All 72 arms finished. Every chart was eligible, with zero parameter gcds, time caps, or process errors. The run took 121.5938 seconds of summed wall time and 44.4258 seconds of summed computation time. The slowest arm took 2.5968 seconds including startup and 1.5178 seconds for the longest computation.

| Bits | Arm | Length per side | Local splits / arms | Inputs split / inputs | Wall seconds | Computation seconds |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: |
| 40 | Chart | 1,024 | 12 / 12 | 3 / 3 | 13.6895 | 0.8732 |
| 40 | Control | 1,024 | 12 / 12 | 3 / 3 | 13.8081 | 0.9154 |
| 48 | Chart | 4,096 | 12 / 12 | 3 / 3 | 16.7708 | 3.9321 |
| 48 | Control | 4,096 | 12 / 12 | 3 / 3 | 16.8432 | 4.0501 |
| 64 | Chart | 16,384 | 1 / 12 | 1 / 3 | 29.9289 | 16.9373 |
| 64 | Control | 16,384 | 3 / 12 | 2 / 3 | 30.5533 | 17.7177 |

No arm had full square agreement, a productive fully aligned pair, or exact signed residue equality. The 52 proper gcds all came from local overlaps. The following are the first successful control witnesses in each size group. In each row the sign is $+1$ and the displayed divisor is exactly $\gcd(x_i-y_j,N)$.

| Bits | $N$ | $t$ | $(i,j)$ | $x_i$ | $y_j$ | Divisor |
| ---: | ---: | ---: | :--- | ---: | ---: | ---: |
| 40 | 945981244529 | 2 | (0, 111) | 729168852684 | 49965022036 | 957499 |
| 48 | 182527886769227 | 2 | (1292, 615) | 76061606041427 | 175929493046385 | 12777277 |
| 64 | 17253711084100655413 | 3 | (12046, 3080) | 2299255474957762922 | 15651410299244668596 | 4212658481 |

At 64 bits the chart split $13993257964720210747$ at $t=7$ with $(i,j,\epsilon)=(1624,2890,-1)$, using $x_i=5012737854383032760$ and $y_j=4320637964924201180$. The sum gcd is $3596220319$ with cofactor $3891101413$. Controls split this input at $t=5,7$ and split the first 64-bit input at $t=3$. Both sets of boxes exhausted every parameter on $14613749908045635547$. The archived result records all first signed local witnesses from both arms and reserves a separate field for exact signed equality. [Complete result log](../experiments/cogentic-unit-collision-search-results.jsonl)

Each saved split was checked directly by computing the stated signed gcd and validating both roots as units. After collection, a separate verifier regenerated the input factors and used CRT residue sets to confirm the status and witnesses for every arm. The detector's fixed brute-force and prime-power controls also pass. The chart achieved the same yield as the control at the two smaller lengths and fewer splits at the largest. This small diagnostic supplies finite local-collision certificates, with no observed chart advantage or evidence of full corrected-square supply at these bounds. [Independent verifier](../experiments/cogentic-unit-collision-verify.py)

Run `python experiments/cogentic-unit-collision-diagnostic.py` to repeat all 72 arms and print their JSONL records.

Conditioning on the signed right-hand control lists and treating each left list as independent uniform unit draws, the expected numbers of local control hits were 11.873, 11.913 and 2.890 across the twelve arms at the three sizes. The observed counts were 12, 12 and 3. The corresponding expected counts for productive global square comparisons were below 0.000030 at every size. These figures come from exact CRT set sizes followed by the independent-draw probability calculation. [Derivation](cogentic-unit-collision-search.md#exact-calibration-for-independent-uniform-unit-lists) · [Independent computation](../experiments/cogentic-unit-collision-verify.py)
