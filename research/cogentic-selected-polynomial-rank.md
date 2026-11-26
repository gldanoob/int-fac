# Exact finite rank scoring for quadratic coefficient selection

The replay compares three choices in the same four-coefficient box. The original conditional-expectation selector counts joint squarefree band marks. The unperturbed control takes the zero tuple. The rank method exhaustively scores every tuple before running the extractor on the chosen tuple. [Replay](../experiments/cogentic-selected-polynomial-split.py)

For each coefficient tuple, the rank method uses the extractor's homogeneous grid of height 250 and smoothness bound 300. The grid uses identical marks in both fields. It uses the same coprimality checks and excludes primes whose squares divide the corresponding discriminant. A column records both fields' valuations with separate coordinates for each field, prime and root. The score counts how many eligible rational-prime targets lie in the exact rational column span. Each target has a one at both first-field roots of its prime and zero elsewhere. Different targets use disjoint coordinates and so contribute independent directions. The tie-breaks maximize the column nullity, then rank, then choose the lexicographically first coefficient tuple.

For each field’s eight coefficient choices, the scorer screens nonsmooth norms by repeated gcd with the factor-base product and caches the smooth marks. It joins the two fields’ records to build the exact matrix for each of the 64 pairs. It uses no modular order tests or factorizations of the input to choose coefficients. It runs the same bounded extractor on each selected pair and on both controls. Python checks each returned divisor and modular squaring chain, and compares the extractor's reported column count and rank with the scorer wherever it returns a certificate. The rank replay also checks examples where both target rows occur but their sum is outside the span, and where two independent directions and one repeated column put it in the span. [Rank scorer](../experiments/cogentic-selected-polynomial-rank.gp)

## Results

| Batch | Exact rank score | Smooth-mark selector | Unperturbed |
| --- | ---: | ---: | ---: |
| Original | 3/6 | 1/6 | 3/6 |
| Holdout | 3/6 | 2/6 | 1/6 |

On the original batch, the rank score and unperturbed control both split 77, 143 and 221. The smooth-mark selector split 77. Its two joint marks for 143 gave a matrix with 68 independent columns and zero eligible targets in its span. The rank choice for that input had 31 targets, rank 131 and 427 columns, and certified divisor 11. The largest target count among all 64 tuples was zero for each of 10001, 10203 and 10403, so none of the tuples can pass the extractor's rational-span check at these limits.

The fixed holdout is 187, 299, 437, 11021, 11663 and 12317. The rank score split the first three. The smooth-mark selector split 187 and 299, and the unperturbed control split 299. Every tuple had zero reachable targets for each of the three larger holdout inputs.

On holdout input 437, the unperturbed matrix had rank 132 and zero reachable targets. The exact score chose $(0,0,0,1)$ with lower rank 127 and 32 reachable targets, and verified divisor 19. The smooth-mark control also had zero reachable targets.

This finite comparison pays for full relation collection across the coefficient box. It gives no bound for replacing that work with conditional expectations or for achieving deterministic $L_N[1/3]$ factoring.

## Smaller norms on the fixed grid

The old box has slopes of magnitude at least $(N-7)/2$. For every searched $(a,b)$, $|a/b|\le H$ and $b\ne0$. Completing the square gives

$$
a^2+sab+cb^2 = b^2\left((a/b+s/2)^2+|s^2-4c|/4\right)
\ge b^2\left((N-7)/4-H\right)^2
$$

when $H\le(N-7)/4$. At $H=250$, every old norm on these six inputs exceeds five million. The grid stays far from the vertex of every old polynomial, including those with smaller discriminants inside the box.

The separate replay uses the existing extractor's small-slope convention with the single fixed pair $(s_1,s_2)=(0,-1)$. Set $m=\lfloor\sqrt N\rfloor$, $r=N-m^2$ and $c_i=r-s_i m$, so both polynomials equal $N$ at $m$. For nonsquare $N$, $1\le r\le2m$ and $1\le c_i\le3m$. The discriminants are negative and the two norms at $(1,1)$ are at most $3m$. This choice uses only $N$ and runs once per input, with the same height, smoothness bound, and identical-mark extractor as the three prior controls. [Replay](../experiments/cogentic-selected-polynomial-recenter.py)

| Input | Reachable targets | Rank | Columns | Verified divisor |
| ---: | ---: | ---: | ---: | ---: |
| 10001 | 27 | 108 | 470 | 137 |
| 10203 | 25 | 116 | 792 | 19 |
| 10403 | 33 | 133 | 442 | 103 |
| 11021 | 30 | 127 | 502 | 107 |
| 11663 | 29 | 125 | 339 | 109 |
| 12317 | 29 | 128 | 465 | 109 |

The smaller-norm pair split all six prespecified misses. The norm comparison explains the geometric difference between these parameter choices. It gives no uniform lower bound for smooth marks, rank, or certified splits.

The original fixed pair is admissible when both discriminants are negative and their product is nonsquare. Square inputs such as 9 fail the first condition. Input 88 gives coincident quadratic fields with discriminants $-28$ and $-63$, so it fails the second condition. The fallback below handles this case. For each returned certificate Python checks the annihilating exponent, recomputes the modular squaring chain and verifies the proper divisor.

A separate fixed fresh batch used products of primes $(127,131)$, $(127,193)$, $(137,139)$, $(137,251)$, $(151,157)$ and $(151,331)$. These products supplied the input fixtures. Coefficient selection received just the six integers.

| Fresh input | Reachable targets | Rank | Columns | Verified divisor |
| ---: | ---: | ---: | ---: | ---: |
| 16637 | 0 | 62 | 62 | — |
| 24511 | 0 | 77 | 77 | — |
| 19043 | 31 | 123 | 415 | 139 |
| 34387 | 0 | 81 | 81 | — |
| 23707 | 22 | 100 | 137 | 151 |
| 49981 | 25 | 118 | 122 | 151 |

The fresh batch split 3/6 with the same limits. The three misses had full column rank and no eligible target in the column span. `make check-one-third` runs both batches.


## Admissible pair for every nonsquare input

For every nonsquare integer $N\ge2$, take $m=\lfloor\sqrt N\rfloor$, $r=N-m^2$ and $f_s(X)=X^2+sX+r-sm$. For $s=0,-1,-2$, the absolute discriminants are respectively

$$
4r,\qquad 4r+4m-1,\qquad 4(r+2m-1).
$$

All three are positive, and each polynomial equals $N$ at $m$. Each constant lies in $[1,4m]$, since $1\le r\le2m$. The slopes have absolute value at most two.

Two negative discriminants define the same quadratic field exactly when their absolute values have the same positive squarefree part. Suppose all three have the same squarefree part $d$. The middle absolute discriminant is $3\pmod4$, so $d$ is odd and greater than one. Since $d$ is odd, it divides $r$ and $r+2m-1$. It also divides $4r+4m-1$, so it divides both $2m-1$ and $4m-1$. Their combination $(4m-1)-2(2m-1)=1$ contradicts $d>1$.

Keep slope zero and try slope $-1$ first, then $-2$ if the first discriminant product is an exact square. For a candidate slope $s$, compute `t = isqrt(abs(D0*Ds))` and keep the pair if `t*t != abs(D0*Ds)`. At most two integer square-root tests select two distinct imaginary fields. The implementation needs no squarefree-part computations. Input 88 takes the fallback and yields discriminants $-28$ and $-96$. The two factoring batches retain all their earlier choices. This argument guarantees admissibility and coefficient size. The relation span still depends on the input and the search limits.

## Norm lower bound and the one-third scale

Write $Q_s(a,b)=a^2+sab+(r-sm)b^2$ for the homogeneous norm at slope $s\in\{0,-1,-2\}$. Completing the square gives

$$
Q_s(a,b)=(a+sb/2)^2+(r-sm-s^2/4)b^2\ \ge\ rb^2.
$$

Indeed, $-sm-s^2/4$ is respectively $0$, $m-1/4$ and $2m-1$. This bound holds at every integer mark, including every primitive mark with $b\ne0$. Take the infinite nonsquare family $N=m^2+m+1$ for $m\ge2$. Here $\lfloor\sqrt N\rfloor=m$, and $r=m+1>\sqrt N$. The subfamily $m\equiv1\pmod6$, $m\ge7$ consists of odd composites divisible by three. On the whole family, each searched norm exceeds $\sqrt N$, independently of grid height. This is a constraint on the norm formula, including on inputs which other factoring methods can split directly.

Set $W=(\log N)^{1/3}(\log\log N)^{2/3}$ and $V=(\log N)^{2/3}(\log\log N)^{1/3}$. With smoothness bound $B=\exp(\beta W)$ for fixed $\beta>0$, a $B$-smooth norm on this family has at least $\log N/(2\beta W)$ prime factors counted with multiplicity. For a squarefree band mark these factors must be distinct. The norm formula also precludes an $\exp(O(V))$ norm bound even if the grid is restricted to one mark. These conclusions follow from size alone.

**Smoothness heuristic.** If each norm of size $X$ has the Dickman-model smoothness rate $\exp(-(1+o(1))u\log u)$ for $u=\log X/\log B$, then a height $H=\exp(O(W))$ gives a modeled per-mark rate $\exp(-(1/(3\beta)+o(1))V)$ on this family. Indeed, $\sqrt N<Q_s(a,b)\le(4m+3)H^2$ for $|a|,|b|\le H$ and $b\ne0$, so $\log X=(1/2+o(1))\log N$ uniformly. The $O(H^2)$ marks then give vanishing modeled expectation for even one smooth norm. This prediction uses no independence between the two fields or between marks. Its input is the unproved application of a random-integer smoothness model to the norm values. The exact size bound alone leaves the actual smooth counts and ranks open. [De Bruijn’s Dickman asymptotic](https://pure.tue.nl/ws/files/2416706/597496.pdf)
