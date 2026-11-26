# Blind cubic/quartic grid benchmark

Ten distinct semiprimes were fixed before the solver ran. The generation pass used Python `Random(20261127)` to sample 20 distinct primes from the ascending list of primes in $[9000,50000]$, and multiplied consecutive pairs. It printed only the public integers listed below. The [replay](../experiments/cogentic-monic-blind-grid.py) solves those frozen integers and regenerates their factors only after every solver call, for validation. The factor range was 10,337–48,817, above both the grid height and the parity prime cutoff. The inputs have 29–32 bits.

The preset uses manual degrees three and four, the raw monic pair with common-root derivative repair, and primitive marks with $|a|\le64$, $1\le b\le64$. It keeps the explicit ramified row at two and uses mark-local acceptance at the other primes. Complete parity includes every odd valuation at primes through 8192, and permits an unfactored residual tail only if it is a square accepted by the mark-local derivative test. The reference smooth count uses bound 151. The search applies normalized Legendre probes through 257 to the parity kernel augmented by a shared sign, with at most 32 exact joint square queries and five seconds for the per-input exact oracle. A mark-label gcd only controls unit eligibility. It does not count as a square split. A proper derivative gcd would likewise be reported separately.

| Public integer | Parity columns | Fully 151-smooth | Parity nullity | Probe rows | Survivors | Exact queries | Square splits |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 341854927 | 274 | 1 | 0 | 66 | 0 | 0 | 0 |
| 824552227 | 203 | 2 | 0 | 95 | 0 | 0 | 0 |
| 647911657 | 262 | 3 | 0 | 95 | 0 | 0 | 0 |
| 641626049 | 286 | 2 | 0 | 98 | 0 | 0 | 0 |
| 310556537 | 231 | 3 | 0 | 95 | 0 | 0 | 0 |
| 449508911 | 352 | 8 | 0 | 96 | 0 | 0 | 0 |
| 2363084519 | 260 | 5 | 0 | 106 | 0 | 0 | 0 |
| 929070139 | 215 | 2 | 0 | 93 | 0 | 0 | 0 |
| 516173501 | 239 | 2 | 0 | 83 | 0 | 0 | 0 |
| 422536969 | 268 | 3 | 0 | 97 | 0 | 0 | 0 |

Every parity column set was independent. In each case the normalized probes rejected the remaining sign-only vector. No exact square query was reached, so this experiment measures the relation supply barrier rather than the success rate of verified square roots. All ten cases completed without a cap or derivative split. The recorded solver times were 0.18–0.22 seconds per input, about 2.0 seconds in total. These outcomes apply to the frozen limits and the ten predeclared cases.

## Prespecified height scaling

The same ten public integers were replayed in the fixed order $H=128$ then $H=256$ with the [packed collector](cogentic-monic-lattice-sieve.md), prime cutoff $2H^2$, mark-local acceptance and the ramified row at two. The field choices, 151-smooth reference bound, probe cutoff 257, 32-query cap and five-second oracle budget were retained. The `--scale` replay flag runs both heights serially in one Python process and validates against fixture factors only after both batches end. The factors still exceed every grid height, while some lie below the larger parity cutoffs. No direct mark gcd was used as a split.

| Public integer | Columns at 64 | Columns at 128 | Columns at 256 | Fully 151-smooth at each height |
| ---: | ---: | ---: | ---: | ---: |
| 341854927 | 274 | 1308 | 5890 | 1 |
| 824552227 | 203 | 894 | 4013 | 2 |
| 647911657 | 262 | 1233 | 5591 | 3 |
| 641626049 | 286 | 1257 | 5612 | 2 |
| 310556537 | 231 | 1144 | 5011 | 3 |
| 449508911 | 352 | 1545 | 6827 | 8 |
| 2363084519 | 260 | 1211 | 5420 | 5 |
| 929070139 | 215 | 1084 | 4853 | 2 |
| 516173501 | 239 | 1162 | 5011 | 2 |
| 422536969 | 268 | 1206 | 5538 | 3 |
| Total | 2590 | 12044 | 53766 | 31 |

The joint parity rank equaled the column count in every case, at both larger heights. Thus the nullity remained zero and there were no new dependencies relative to $H=64$. The same 66–106 probe rows per input rejected the sign-only vector. Each case had zero survivors, zero exact queries, zero verified squares and zero square splits. No derivative gcd split or cap was hit. The two larger batches took about 4.5 and 17.7 seconds of measured solver time, respectively. The increase in columns reflects both the larger grid and its larger parity prime cutoff. These fixed runs do not estimate the effect of changing either parameter alone.
