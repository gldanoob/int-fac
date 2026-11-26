# Mixed primitive relations on two frozen semiprimes

A fixed three-field search split both of the first two semiprimes that the scheduled pair and the nearby-base search had left unsplit. The new certificates use only primitive grid marks. At height 256 every two-field ideal-parity kernel on the corresponding admitted columns was zero, even before square-class probes. PARI independently recovered all six field roots in the two splitting certificates. [Earlier scheduled grid](cogentic-monic-degree-grid.md) · [Nearby bases](cogentic-monic-nearby-bases.md) · [Mixed-field criterion](cogentic-mixed-square-graphs.md)

## Fixed search

Using several number fields in the number field sieve goes back to Coppersmith. Here the shared rows record the parity of individual primitive marks. This finite comparison also computes the rank for each two-field restriction and checks the mixed square roots exactly. [Coppersmith, *Modifications to the Number Field Sieve*](https://research.ibm.com/publications/modifications-to-the-number-field-sieve)

The inputs were $310556537$ and $449508911$, in that order. Before collection, the plan fixed heights 128 and 256, prime cutoff $2H^2$, and three fields with the original scheduled root $m$. The fields are the raw quadratic $F$, raw cubic $G$, and $G+4(X-m)$. All are monic Eisenstein at two, evaluate to $N$ at $m$, and had unit derivatives on both inputs. No input factors enter the search.

Collect each field's marks independently with the packed lattice collector, mark-local checks and the ramified row at two. Each column is a field and primitive point $(a,b)$ with $|a|\le H$, $1\le b\le H$, and $a-bm$ a modular unit. Stack its local ideal-parity rows with one row keyed by the primitive point and shared across the fields. This row requires an even total incidence for the point. Delete singleton rows and their forced-zero columns before binary elimination. Then apply the normalized degree-one Legendre probes through 257 to each field projection of the surviving basis.

For each two-field comparison, restrict the same kernel to vectors vanishing on the excluded field. This dimension measures simultaneous parity on the two fields. Equivalently, take the intersection of the two admitted point sets and stack their two ideal matrices on the common columns. Independent rank calculations using this second construction also gave zero. Since every pair contains a cubic, the negative sign alone cannot give a field square if the point support is empty.

After probes, consider basis representatives of the quotient by the span of all two-field supported vectors. In increasing support size, test at most four representatives with a five-second exact dyadic root budget for each input and height. In the observed grids the pair span was zero, so each tested nonzero vector used three fields. The dyadic test verifies the square identity before returning a root. The entire frozen replay was run under a 75-second wall timeout.

## Results

The three entries in each column count or core count refer to $F,G,G+4(X-m)$, respectively.

| Input | Height | Admitted columns | Core columns | Mixed ideal nullity | After probes | Exact tests | Divisor |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 310556537 | 128 | 7728, 3641, 3191 | 0, 0, 0 | 0 | 0 | 0 | |
| 310556537 | 256 | 35076, 17054, 15361 | 3045, 2119, 1818 | 395 | 387 | 1 | 20149 |
| 449508911 | 128 | 7085, 3836, 3000 | 0, 0, 0 | 0 | 0 | 0 | |
| 449508911 | 256 | 32588, 17785, 14616 | 2586, 1911, 1438 | 191 | 183 | 2 | 24659 |

At height 256 the pair intersections, in order $(F,G)$, $(F,G+4(X-m))$, and $(G,G+4(X-m))$, had 7983, 7225 and 3567 columns on the first input, and 7788, 6548 and 3527 on the second. All six restricted ideal nullities were zero. These ranks concern the collector's admitted columns. The collector is conservative at some singular primes, so the ranks do not cover the full all-ideal grid. The dyadic and independent PARI verifications apply to the exact emitted square certificates.

The height-256 searches took about 4–5 seconds each, including collection, elimination, probes and root recovery. The first candidate on the second input was square in all three fields and had normalized root residue one. The second candidate split it.

## Certificate normalization

In a surviving tuple, each selected point appears in two of the three field supports. If $A_1,A_2,A_3$ are the modular residues of their exact field roots and $T$ is the product of $a-bm$ taken once per selected point, then
\[
(A_1A_2A_3)^2=T^2\pmod N.
\]
The normalized residue $z=A_1A_2A_3/T$ gives the proper divisor $\gcd(z-1,N)$. No mark gcd is used as a split.

| Input | Field support sizes | $T$ | $z$ | Divisor and cofactor |
| ---: | ---: | ---: | ---: | ---: |
| 310556537 | 804, 624, 340 | 177188168 | 96130880 | $20149\cdot15413$ |
| 449508911 | 918, 714, 450 | 445025539 | 266909017 | $24659\cdot18229$ |

The saved certificates contain every point and reduced root. The independent checker constructs each number field in PARI, recovers its square root and verifies that the root evaluates to the saved residue up to sign. It then checks incidence, normalization and the divisor. [Frozen certificates](../experiments/cogentic-monic-mixed-certificates.json) · [Independent verifier](../experiments/cogentic-monic-mixed-certificate-check.py)

Replay the frozen search or run a single public input:

```sh
timeout 75s python3 -B experiments/cogentic-monic-mixed-grid.py
python3 -B experiments/cogentic-monic-mixed-grid.py 310556537 --height 256
python3 -B experiments/cogentic-monic-mixed-certificate-check.py
```

The search module also exposes `search(n, height=256, query_cap=4, time_cap=5)`. The time cap measures the exact-root stage. Use the certificate-file option to save full supports for a replay. The two inputs were selected from prior pair-search failures, so these outcomes measure a conditional improvement on those fixtures. A broad success rate and a uniform relation-supply bound remain open.
