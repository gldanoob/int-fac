# Integer factoring research handoff, November 25, 2026

The strongest result factors an integer completely in deterministic polynomial **average** time given one exact divisor sum $\sigma(N^j)$ for any fixed $j\ge1$. The average is over all integers of a given bit length. For unrestricted input consisting only of $N$, improving the deterministic bound $2^{O(b/\sqrt{\log b})}$ remains open. Here $b$ is the bit length of $N$. [Average-time proof](../average-cyclotomic-splitting.md) · [08:00 handoff](../2026-11-25-0800-handoff.md) · [Research index](../../README.md)

## Results already on main

| Input or promise | Result and evidence |
| --- | --- |
| A supplied multiple of $\Phi_k(p)$ for one unknown prime factor, fixed $k\ge2$ | Deterministic polynomial average time to find a proper factor. Coverage of all but one distinct prime suffices for complete factoring. The cost counts the bit length of the multiple. [Proof and arithmetic checks](../average-cyclotomic-splitting.md) |
| Exactly $M=p^2+p+1$ | An explicit pair with 1,410-bit $p$ and 414-bit $q$ defeats all 1,452 height-five monic quadratic and cubic probes. Height six splits it. There is also a balanced height-five miss with two orders supplied. [Certificates](../cyclotomic-order-multiples.md) |
| Balanced primes and an arbitrary supplied cubic multiple | Public cubic characters give limiting worst-multiplier mean two field tests. A suitable polylogarithmic conductor cutoff has exceptional fraction $O_\epsilon(X^{-1+\epsilon})$ for primes of scale $X$. [Public character selection and cutoff](../public-cubic-characters.md) |
| Linear shifts in a finite algebra | An interval of $O_k(\sqrt p)$ shifts generates the unit group under the pointwise theorem's hypotheses. A universal list of order $\log X$ within that interval scale suffices, and logarithmic length can be necessary. [Generation and optimal list length](../small-algebra-generators.md) |
| Noisy parity at uniformly sampled short centers, two prime-power blocks | An inverse-polynomial prediction advantage suffices for a zero-error randomized reduction with chosen queries. In the precomputed-advice model, inverse-polynomial advantage needs at least $\log_2 T-O(\log\log q)$ bits for $T$ possible centers. [Oracle reduction](../floor-sum-and-log-parity.md) · [Advice lower bound and its model](../centered-bit-probes.md) |

The earlier handoff covers divisor-sum blocks, Kloosterman and Salié thresholds, and quadratic resolvent ranks. Upstream supplies both the written constructor for $\alpha=1/2$ and the Lean proof of the factoring-machine bound. This handoff used source inspection for that question. [Earlier handoff](../2026-11-25-0800-handoff.md) · [Upstream constructor](https://github.com/1337isnot1337/integer-factoring/blob/e91442d3/research/half-top-constructor.md) · [Upstream theorem](https://github.com/1337isnot1337/integer-factoring/blob/e91442d3/formal-appendix/HalfTheorem.lean)

## Material recovered at closeout

| Topic | Finding | Status |
| --- | --- | --- |
| Height-six cubic fields | There are 369 fields. For two independent primes with fixed quadratic and cyclic characters, the largest limiting probability of equal irreducibility masks is $14213\cdot5^{57}/3^{128}$, about $8.365\times10^{-18}$. | Field enumeration, exceptional line arrangements and exact optimization replayed. The density is a limiting statement for conditioned primes. [Derivation](height-six/proof.md) |
| Finite height-six search | All 163,458 recorded masks are distinct. Their minimum Hamming distance is seven. The certified pair attaining seven already splits at height three. | All 2,366 literal quadratic and cubic powers for the pair were replayed. The archive contains every complete row and the calculation of the minimum. [Data, certificates and commands](height-six/sample/README.md) |
| Fixed-center quarter parity | For an odd product of two distinct prime powers, quarter-root parity at $n\ell$ for a chosen auxiliary prime gives a zero-error randomized polynomial-time factoring reduction. | The exact lifts and local Fourier identities passed 135 finite cases. The algorithm requires the parity oracle. The bounded-support extension has a written argument awaiting independent review. [Argument and extension](quarter-parity/fixed-center.md) |
| Cyclotomic information from $N$ alone | For balanced $N=pq$ with $\gcd(\Phi_k(p),\Phi_k(q))\ge N^{\varphi(k)/2}/B$, the bound is $O_k(B^{1/\varphi(k)}\operatorname{poly}(\log N))$. A complementary progression gives a bound of $N^{1/(4(1+r\varphi(k)))}$ times polynomial factors. A density argument also covers schedules using $\lfloor(aN)^\alpha\rfloor$. | The bounds have explicit promises. Checks covered 86 relative-congruence classes, a lattice recovery, three progression fixtures and finite slope cases. [Proofs and hypotheses](cyclotomic-supply/audit.md) |
| Projective orders at rational primes | Under the stated Kummer independence condition, splitting degrees and the cyclotomic residue class determine the simultaneous two-primary order law. Cyclotomic entanglement changes one cubic density from $1/12$ to $1/8$. | The phase enumeration covered 40 profiles. The prime replay compared four fields through 250,000. [Density calculation](projective-orders/proof.md) · [Prime counts](projective-orders/replay.log) |

Additional arguments give direct joint generation at $pq$ for one divisor sum, small generators via smooth products, and uniform split markers for cyclic cubic conductors. The full average-time theorem and its quantifiers are in the linked main report. [Joint generation](alternative-arguments/joint-generation.md) · [Smooth products](alternative-arguments/smooth-proof.md) · [Uniform markers](alternative-arguments/uniform-markers.md) · [Main theorem](../average-cyclotomic-splitting.md)

## Where to resume

1. **Height six.** The quartic norm construction produces an explicit primitive irreducible polynomial. A subsequent proof identifies 16 cubics that split at its prime values and verifies them on three certified primes. A pair matching on the remaining 54 active fields still needs a literal powering certificate. No pair in the archived scan gives a height-six miss. [Quartic construction and splitting proof](height-six/quartic/README.md)
2. **Quarter parity.** Review the uniform prime-progression and Fourier estimates for growing support in the fixed-center draft. An efficient evaluator of the quarter bit from the integer alone would remove the oracle assumption. [Fixed-center proof](quarter-parity/fixed-center.md) · [Direct evaluator results](../floor-sum-and-log-parity.md)
3. **Order supply.** The overlap theorem would have wider algorithmic consequences with a quantitative supply of prime pairs having a small overlap deficit, or with a way to guarantee comparably useful divisibility on general inputs. [Order supply](cyclotomic-supply/audit.md)

## Reproduce the checks

From the repository root, use Lean 4, PARI/GP, Python 3 and a C++20 compiler. The repository suite and the following targeted checks passed at closeout. The analytic deductions in the Markdown reports are written proofs. The replay programs check the stated finite identities, counts and witnesses.

```sh
make check
h=research/2026-11-25-handoff
python3 "$h/quarter-parity/fixed-center-replay.py"
python3 "$h/cyclotomic-supply/graph.py"
gp -fq "$h/cyclotomic-supply/supply.gp"
gp -fq "$h/cyclotomic-supply/overlap.gp"
(cd "$h/projective-orders" && python3 cycles.py && python3 profiles.py && gp -fq square-replay.gp && gp -fq replay.gp)
```

The height-six instructions cover the field list, both optimized character profiles, the raw sample, the nearest pair and the quartic fixture. [Height-six replays](height-six/sample/README.md)
