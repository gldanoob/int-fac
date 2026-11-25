# Height-six search data and certificates

The completed sample contains **163,458 distinct 70-bit masks**. Each records irreducibility at the 70 active cubic fields on one fixed character profile. The other 299 field bits are fixed. The closest pair differs in seven fields. It gives a factor from $x^3-x^2-3x-3$ at height three. [Nearest pair](best-pair.json) · [Complete compressed data](masks.txt.gz) · [Limiting profile calculation](../proof.md)

## Data and provenance

Each line contains the candidate index $j$, the low 64 bits and the high six bits in decimal. The candidate integer is $Aj^2+Bj+C$ using the three coefficients in the construction file. Field entries give a discriminant and the constant, linear and quadratic coefficients of a monic reduced cubic. Bit zero corresponds to the first field. The original scanners used PARI's Baillie–PSW probable-prime test. The nearest pair received separate primality proofs. [Parameters and ordered fields](construction.json) · [Pilot scanner](birthday.cpp) · [Worker scanner](birthday-sqrt.cpp)

| Source | Complete rows | First index | Last index |
| --- | ---: | ---: | ---: |
| Pilot | 951 | 1,000,000,477 | 1,000,249,659 |
| Worker 0 | 81,308 | 1,000,250,467 | 1,021,338,389 |
| Worker 1 | 81,199 | 1,025,250,335 | 1,046,531,219 |

Each stopped worker left one incomplete trailing record. The archive contains all complete records in their original order. The SHA-256 of the **decompressed bytes** is `a687213dc843cf3c516e743c5d621565a5af1604ce568bd17a3c4c99687edd41`.

## What the finite sample establishes

The two 744-bit primes at indices 1,005,166,825 and 1,008,991,053 have active masks at distance seven. To rule out a smaller distance, partition the 70 positions into seven disjoint blocks of ten. A pair with at most six differences agrees on at least one entire block. Comparing pairs in all matching buckets took 262,773,441 comparisons, including pairs visited in multiple buckets. Restricting the same data to height four gives 632 equal-mask pairs among 29 active fields. At height five there are zero among 42 active fields. [Distance verifier](exact-nearest.cpp) · [Projection and index verifier](check-sample.py)

With $M=\operatorname{lcm}(p^2+p+1,q^2+q+1)$, the direct replay proves both primes, recomputes the active masks, then computes every coefficient gcd from the literal modular powers. Across the 2,197 cubics, the counts irreducible at neither prime, $p$ only, $q$ only and both are respectively 1,891, 12, 18 and 276. The gcd outcomes below include the 169 quadratics as well. [Prime and field checks](verify-best.log) · [Literal power results](literal-best-clean.log)

| Degree | gcd 1 | gcd $p$ | gcd $q$ | gcd $pq$ |
| --- | ---: | ---: | ---: | ---: |
| 2 | 164 | 0 | 0 | 5 |
| 3 | 1,886 | 12 | 18 | 281 |

The 30 proper splits occur at exact heights 3, 4, 5 and 6 with counts 2, 2, 6 and 20. The candidate sequence is thin. A search probability for it would require a separate distribution result. [Fixed-profile prime density](../proof.md)

## Replay

Run these commands in the enclosing `height-six` directory. The two collision-profile commands reproduce the text fixtures next to the scripts. The distance check uses standard C++20 and reads the decompressed data on standard input.

```sh
gp -fq enumerate.gp | diff - fields6.txt
gp -fq check-blocks.gp
python3 collision-profile.py 0
python3 collision-profile.py 1
python3 norm-bases.py
python3 sample/check-sample.py
c++ -std=c++20 -O3 sample/exact-nearest.cpp -o /tmp/int-fac-nearest
gzip -dc sample/masks.txt.gz | /tmp/int-fac-nearest
gp -fq sample/verify-best.gp
gp -fq sample/literal-best.gp
```

For the original search, `python3 sample/build.py` regenerates the quadratic and field parameters. Both scanner sources use PARI development headers and a 64-bit Linux ABI. The pilot takes arguments `begin end params.txt output`. The worker takes the same arguments followed by `sqrt.txt`. Their intervals include the start and exclude the end. Both were rebuilt and reproduced the first nine archived rows on $10^9\le j<10^9+2000$. The closeout rechecked the entire saved dataset and the certified pair.
