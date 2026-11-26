# Near-root public witnesses on the size-scaling cohort

The public menu added no rational matching dependency on the nine published 40-, 48- and 64-bit semiprimes. All nine field-only, public-only and combined squareclass matrices had zero nullity. Their CRT sign images were therefore exactly zero without reaching the root oracle. This was a secondary experiment on a cohort with known field-only outcomes. [Preregistered plan](cogentic-sheared-qs-witness-plan.md) · [Published cohort](cogentic-sheared-size-scaling.md) · [Result log](../experiments/cogentic-sheared-qs-witness-results.jsonl)

## Fixed menu and exact squareclass encoding

The plan was committed before collection as `81261314fc6bf8280cd395c6c894a833766c5a4f`. Keep the six height-64 fields and add the auxiliary witnesses
\[
(E_j,r_j)=(r_j^2-N,r_j),\qquad
r_j=\lceil\sqrt N\rceil+j,\quad -32\le j\le32.
\]
Each input admitted all 65 witnesses. Their labels need not satisfy the determinant cutoff that applies to the field marks.

The measured encoder factors only the auxiliary label magnitudes. For $N<2^{64}$ the distance of $r_j$ from $\sqrt N$ is less than 33, so $|E_j|<2^{39}$ and exhaustive trial division uses primes at most $2^{20}$. Take the union of the auxiliary prime factors above 16,384 and extract those primes from every field mark and auxiliary label. Record their exponent parities as separate rows. The existing bounded field parity code applies to the reduced labels because removing primes preserves the coprimality of distinct pre-existing large residuals. All remaining public prime factors are at most 16,384. This gives exact joint rows even when auxiliary primes split a formerly composite field atom.

## Results and controls

| Input bits | Field-local square dimensions summed over the six fields | Public witnesses per input | Field-only, public-only, full nullities |
| ---: | ---: | ---: | :--- |
| 40 | 45, 351, 177 | 65 | 0, 0, 0 on each input |
| 48 | 1, 105, 0 | 65 | 0, 0, 0 on each input |
| 64 | 0, 0, 0 | 65 | 0, 0, 0 on each input |

Every case completed, with per-input wall times from 0.86 to 1.74 seconds and 11.22 seconds total. All six fields passed the admission checks on each input. The shared 32-query cap and 15-second wall cap did not bind. The published field-only results are unchanged.

If $U$ and $V$ are the rational squareclass spans of the field and public columns, then the combined nullity minus the two restricted nullities is $\dim(U\cap V)$. It was zero here, including at the input with 351 local squares. Thus this menu failed at rational compatibility, before the CRT sign stage. A larger exact-root budget would not affect this experiment.

After the run, the verifier regenerated the nine factor labels and recomputed the three ranks with a separate gcd-free joint encoder. It also checks a positive control at $N=93$, where one field label 28 and the public label 7 produce a productive matching dependency even though both restricted kernels are zero. [Rational root matching](cogentic-rational-root-matching.md)

```sh
python3 -B experiments/cogentic-sheared-qs-witnesses.py
python3 -B experiments/cogentic-sheared-qs-witnesses.py --verify experiments/cogentic-sheared-qs-witness-results.jsonl
```
