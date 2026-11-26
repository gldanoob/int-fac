# Preregistered size scaling for different-base rational matching

This study freezes nine public integers and all search limits before relation collection. It is separate from the [original eight 29–32-bit inputs](cogentic-sheared-local-squares.md). [Frozen public inputs](../experiments/cogentic-sheared-scaling-inputs.json) · [Deterministic generator](../experiments/cogentic-sheared-scaling-cohort.py)

For sizes $s=40,48,64$ in that order, write $k=s/2$. Use SHA-256 of the literal ASCII seed `int-fac/sheared-size-scaling/v1/c15e471` followed by an unsigned eight-byte big-endian counter, starting at zero and continuing across sizes. Interpreting the hash as the unsigned integer $w$, start at the odd integer $3\cdot2^{k-2}+2(w\bmod 2^{k-3})+1$. Use PARI `nextprime` and confirm the returned prime with exact `isprime`, iterating past candidates that fail. Reject candidates outside $[3\cdot2^{k-2},2^k)$ and repeated primes in that size. Accept the first six distinct primes in each size and multiply consecutive pairs. All products have exactly $s$ bits and ratios below $4/3$. The generator prints only the public products. Their factors are regenerated only for validation after every search.

Run the existing `cogentic-sheared-local-squares.py N` single-input matcher serially in the frozen order, once per integer. Keep height 64, bases $\lfloor\sqrt N\rfloor-j$ for $j=0,1,2$, slopes $0,-1$ in each base, and the published exact local kernels, field ordering, and rational matching. The bounded prime cutoff is 16,384. The identical signed integer evaluation incidence on the same generators is the control. The cap is 32 exact candidate tests and 15 seconds of wall time per input including preparation. No retry, cap increase, or preliminary mark gcd is allowed. A proper derivative gcd is recorded separately. Preserve the prepared dimensions if available on timeout, all final statuses and timings, and complete square certificates. Independently verify every returned certificate with the existing PARI square-root check and the separately regenerated labels after all searches.

## Results

The freeze commit `70639b1332ca2044d8fc5e2950c848b72a2ee1eb` was published before collection. The serial run used an isolated copy of the exact `73d245f` matcher and its dependencies. The wall-limit wrapper kills the complete matcher process group on timeout, including any active PARI child. [Scaling runner](../experiments/cogentic-sheared-scaling.py) · [Full result log](../experiments/cogentic-sheared-scaling-results.jsonl)

| Bits | Public integer | Six local square dimensions | Rational nullity | Identical nullity | Exact tests | Seconds |
| ---: | ---: | :--- | ---: | ---: | ---: | ---: |
| 40 | 892461594611 | 0, 2, 42, 0, 0, 1 | 0 | 0 | 0 | 0.771 |
| 40 | 804097083799 | 156, 71, 60, 20, 44, 0 | 0 | 0 | 0 | 1.092 |
| 40 | 810761370127 | 78, 65, 33, 0, 1, 0 | 0 | 0 | 0 | 0.886 |
| 48 | 205066872659269 | 1, 0, 0, 0, 0, 0 | 0 | 0 | 0 | 0.937 |
| 48 | 205063046499067 | 105, 0, 0, 0, 0, 0 | 0 | 0 | 0 | 1.132 |
| 48 | 229958080448773 | 0, 0, 0, 0, 0, 0 | 0 | 0 | 0 | 0.916 |
| 64 | 12074979886925780983 | 0, 0, 0, 0, 0, 0 | 0 | 0 | 0 | 1.557 |
| 64 | 13075727516228214437 | 0, 0, 0, 0, 0, 0 | 0 | 0 | 0 | 1.570 |
| 64 | 15225739601983240301 | 0, 0, 0, 0, 0, 0 | 0 | 0 | 0 | 1.565 |

All nine cases exhausted the finite matching domain. No input hit the time cap or candidate cap. There were no derivative gcds or square certificates. Separate PARI prime generation reproduced the nine labelled products. An untimed verification recomputed every local square kernel and the two matching kernels, checking the saved fields, dimensions, order, query counts and status against the exact repeat. No field square certificate was available for independent checking. The total measured runtime was 10.43 seconds.

The 40-bit group still had 573 local square dimensions in total and the 48-bit group had 106. None gave a rational squareclass dependency. At 64 bits the local kernels themselves vanished. Thus the fixed grid failed at two different stages as input size increased. Raising only the exact candidate budget would have no effect on these nine outcomes. The earlier seven splits among eight 29–32-bit inputs and the zero splits here concern distinct frozen cohorts with the same small grid limits. They do not give a uniform cutoff beyond which the matcher fails.

To replay the pinned solver independently of later CLI changes, extract its experiment directory and copy in the scaling runner and public input list.

```sh
scaling_dir=$(mktemp -d)
git archive 73d245f experiments | tar -x -C "$scaling_dir"
cp experiments/cogentic-sheared-scaling.py experiments/cogentic-sheared-scaling-inputs.json "$scaling_dir/experiments/"
python3 -B "$scaling_dir/experiments/cogentic-sheared-scaling.py"
```

Run `python3 -B experiments/cogentic-sheared-scaling.py --verify experiments/cogentic-sheared-scaling-results.jsonl` from the current checkout to repeat the exact algebraic checks on all saved records and independently verify any certificates. This verification does not change the measured search outcomes or timings.
