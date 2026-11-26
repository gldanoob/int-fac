# Frozen relation-supply test at the automatic degree-three boundary

This plan fixes the public inputs, grids and checks before any relation collection. Let $L$ be the input bit length and $k$ the bit length of $L$. The [automatic schedule](cogentic-monic-pair.md#height-and-construction-cost) first reaches degree three when $L\ge27k$. For $k\le7$, the largest eligible $L$ is $2^k-1<27k$. For $k=8$, the first eligible $L$ is 216. The raw fields on this cohort therefore have degrees three and four.

Use the literal ASCII seed `int-fac/monic-216/v1/18e2e46`. Hash it with each eight-byte big-endian counter from zero. If the hash is the unsigned integer $u$, take the odd start $3\cdot2^{106}+2(u\bmod2^{105})+1$. Use the PARI `nextprime` sequence from that start until `isprime` verifies the candidate. Reject repeated candidates and candidates outside $[3\cdot2^{106},2^{108})$. Accept the first six distinct primes and multiply consecutive pairs. Every product has exactly 216 bits and the ratio of its two primes is below $4/3$. The generator emits only the three public integers. The benchmark reads those integers from the frozen list and never calls the generator or passes prime factors into the search. [Public inputs](../experiments/cogentic-monic-216-inputs.json) · [Generator and separate validation](../experiments/cogentic-monic-216-inputs.py)

Run both raw fields separately at heights 64 and 128 in that order, on the public integers in listed order. Use the packed primitive unit-mark collector with cutoff $2H^2$, mark-local acceptance, and the explicit ramified row at two. The reference fully smooth bound is 151. Record per-field accepted marks, their intersection and the compact joint ideal-parity rank. A rejected tail or mark is outside this sufficient collector's coverage. In particular the replay does not treat its singular or unresolved composite-tail exclusions as impossibility statements about the actual maximal-order valuations.

At the end, run the private-row construction on the same public integers with $h=3,r=1$. It uses degrees four and five and is a separate explicit construction, not a modification of the raw-grid counts. Check its actual odd private row and its marked norms. Count any proper construction gcd separately. Run no square search, prime-bound expansion, or input-dependent retries.

## Raw coverage

The frozen plan was published before the run. The [benchmark](../experiments/cogentic-monic-216-benchmark.py) reads only the public integers. All nine records, including the defining coefficients, discriminants and the single-field witnesses, are in the [result log](../experiments/cogentic-monic-216-results.jsonl). The labels A, B and C denote the three inputs in public order.

| Input | Height | Primitive unit marks | Accepted cubic / quartic marks | Joint marks | Joint rank / nullity |
| :--- | ---: | ---: | ---: | ---: | ---: |
| A | 64 | 5039 | 0 / 0 | 0 | 0 / 0 |
| B | 64 | 5039 | 0 / 0 | 0 | 0 / 0 |
| C | 64 | 5039 | 0 / 0 | 0 | 0 / 0 |
| A | 128 | 20087 | 0 / 0 | 0 | 0 / 0 |
| B | 128 | 20087 | 2 / 0 | 0 | 0 / 0 |
| C | 128 | 20087 | 0 / 0 | 0 | 0 / 0 |

All primitive marks are units modulo these inputs. Indeed $m<2^{72}$ and $H\le128$ give $0<|a-bm|\le H(m+1)<2^{80}$, whereas each defining prime is at least $3\cdot2^{106}$. No fully 151-smooth mark survived in either field. The raw rounds took about 2.5 seconds total. The construction rounds gave the same private odd row at the cubic parameter $h=3$ but in their degree-four field. Its mark $(0,1)$ has norms $182=2\cdot7\cdot13$ and $170=2\cdot5\cdot17$. The simple root zero at 13 and the rational norm exponent one certify exactly one degree-one prime ideal with valuation one. This proves a genuine rank-one joint column for the separately planted pair on each input. It supplies no square dependency.

## A sufficient obstruction for the two single-field survivors

The two accepted cubic marks at height 128 are $(-110,19)$ and $(89,111)$. Their occupied cubic parities are independent, since each contains odd rows absent from the other. Both cubic norms factor entirely through 32768. After removing every prime at most 32768 from the corresponding quartic norms, the remainders are respectively $55605504932219541283488648961$ and $5606482759898348059932680681$. Both remainders are nonsquares by exact integer square-root tests.

For each remainder, there is therefore a rational prime $p>2H^2$ with odd quartic norm exponent. The norm exponent is a sum of ideal valuations weighted by residue degrees, so at least one actual prime ideal above $p$ has odd valuation. If that ideal divided two primitive marked elements, its residue field would give $a/b=a'/b'$ because a divisible denominator would force the numerator divisible as well. Thus $p\mid ab'-a'b$. Distinct primitive marks with positive denominators have nonzero determinant, of absolute value at most $2H^2$. This contradicts $p>2H^2$. The odd ideal valuation is private on the whole grid and rules out participation of either of these two marks in a joint even-parity relation, including at index primes. No factorization of the quartic remainders is needed for this argument. The other conservative collector rejections give no corresponding impossibility statement here.

The exact relation $G_{\rm hom}-bF_{\rm hom}=(a-bm)a^3$ also gives $\max(|F_{\rm hom}|,|G_{\rm hom}|)\ge(m-H)|a|^3/2$ at nonzero $a$. At each frozen input this requires at least ten prime factors with multiplicity on one side if both norms are 151-smooth. Even at the larger prime cutoffs it requires at least six factors for $H=64$ and five for $H=128$ on that side if both norms are entirely cutoff-smooth. This size condition is compatible with smoothness and does not predict a frequency. The measurements show zero joint columns at the first automatic degree-three boundary under the tested sufficient criterion, while explicit planting supplies one. They leave full ideal coverage and larger grids open.
