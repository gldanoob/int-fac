# Preregistered fresh monic-grid validation

This cohort and portfolio are fixed before any relation search on these inputs. They test the nearby-base gains found at commit `413a062` on a separate cohort. The existing ten inputs are unchanged. [Public integers](../experiments/cogentic-monic-fresh-inputs.json) · [Separate generator and validator](../experiments/cogentic-monic-fresh-cohort.py)

## Input generation

Use the literal ASCII seed `int-fac/monic-fresh/v1/413a062`. At counter values starting at zero, hash the seed followed by the eight-byte big-endian counter. The high and low 16-byte halves of SHA-256, read as unsigned big-endian integers, index the ascending primes in the inclusive range 9000–50000 after reduction modulo the list length. Sort the two resulting primes as $p\le q$. Accept their product if they are distinct, $q\le2p$, the product has 29–32 bits, neither prime was used by an earlier accepted pair, and the product is absent from the original frozen ten. Stop after ten acceptances. The search reads only the public list below. The labelled generator is used separately after all solver rounds to validate returned divisors.

| Order | Public integer |
| ---: | ---: |
| 1 | 409623281 |
| 2 | 1684014223 |
| 3 | 311206417 |
| 4 | 452714791 |
| 5 | 358395019 |
| 6 | 301171561 |
| 7 | 1407769453 |
| 8 | 906100297 |
| 9 | 1357861651 |
| 10 | 1247093831 |

## Fixed portfolio

Run the following rounds serially in the public order. Later rounds receive only integers without an earlier exact square split. A construction or mark gcd is recorded separately and does not qualify as an exact square split. An error or exhausted budget ends that attempt. The search never retries a capped case at a larger limit.

1. Use the raw automatic monic pair at height 256. For these bit sizes the scheduled degree is two. Use packed collection with cutoff $2H^2=131072$, mark-local acceptance, the explicit ramified row at two, and the compact ideal-parity core. Use normalized probes through 257 and at most three joint square queries, with a five-second exact oracle budget. Stop on the first verified square split.
2. On unresolved inputs, run the public rule from `413a062` at the same height, cutoff, parity and probe settings. Try $m-2j$ for $j=1,2$ in decreasing order of the exact simple-affine-root score through 43, with smaller $j$ first at a tie. Use a combined cap of three exact joint square queries per input across the two shifts, with a five-second oracle budget per pair. Stop on the first verified square split.
3. On remaining inputs, run the mixed-grid producer with the raw automatic pair $F,G$ and the third field $G+4(X-m)$ at the same argument, without nearby-base shifts. Use the producer's fixed packed height-256 mixed-parity and probe settings, at most four exact candidate tests and a five-second exact-root budget. Stop on its first verified square split. Any later experimentation has a different scope from this validation.

Record all attempted outcomes and skipped stages, ideal-parity dimensions, probe survivors, query counts, field parameters and runtimes. Keep the full support and residue data for any exact square split and verify the congruence and proper divisor. Positive outcomes on this cohort are finite validations of the fixed portfolio. They give no uniform relation-supply guarantee.
