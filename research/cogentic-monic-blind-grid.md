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
