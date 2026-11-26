# KeyBreak’s randomized factoring bounds

KeyBreak's 26 November 2026 manuscript studies complete classical factorization of each fixed integer, including prime multiplicities. Randomness enters the running time. The algorithm terminates on every tape and verifies the output. All constants below are leading coefficients in expected bit complexity at the same $L_N[1/3]$ scale. The SHA-256 of the 144-page copy examined here is `2b534eaf77fb2b9712018879059d8d4667c40c0a4adf2fff90efc22fb356cfc9`. [Theorems 1.1 and 1.2](https://crypto.sjtu.edu.cn/factoring.pdf#page=3)

| Analysis | Coefficient | Basis |
| --- | ---: | --- |
| Cogentic, Theorem 1.1 | 105 | Unconditional as stated in the manuscript |
| KeyBreak, Theorem 1.1 | $10^{13}$ | Unconditional as stated in the manuscript |
| KeyBreak, Theorem 1.2 | 2.97 | GRH for primitive Dirichlet characters, including zeta |
| This repository, entrywise concentration | $2(8/3)^{2/3}=3.845998854153089\ldots$ | Local paper argument using Dirichlet smooth-window, moment and exact extraction results |
| This repository, high trace moments on the full grid | $2(16/9)^{2/3}=2.93504644346189\ldots$ | Local paper argument with Dirichlet GRH, a finite-order moment estimate and the same exact extractor |

The later full-grid argument averages a two-prime congruence error over the residues that actually occur in the trace sum. This permits $c>b$ where the old pointwise estimate used $c>2b$. Together with transposed extraction, it gives the local manuscript coefficient $2(3/2)^{2/3}=2.6207413942\ldots$ under the original Gaussian, smoothness and extraction hypotheses. A fixed rational schedule with even trace order 32 gives 2.70. [Averaged trace proof](cogentic-averaged-projective-trace.md) · [Fixed schedule](../experiments/cogentic-variable-multiple-costs.py)

KeyBreak Table 1 prints Cogentic's 105 as a decimal integer. The exponent 13 in its own unconditional bound is a superscript. The entrywise value first appears in commit `8188b63`. The same bound follows from optimizing the three costs of the full projective grid. A strict rational schedule yields 3.8459988542. [KeyBreak Table 1](https://crypto.sjtu.edu.cn/factoring.pdf#page=4) · [Original Cogentic manuscript](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/integer_factorization/paper.pdf) · [Original local derivation](https://github.com/gldanoob/int-fac/blob/8188b6333f8d1154ffb00535a7de5698f24a394c/research/cogentic-variable-multiple-lattice.md#L68) · [Exact local optimization](cogentic-variable-multiple-costs.md)

KeyBreak follows prime ideals through a multilevel descent. It bounds both the supply of relations for each ideal and how often earlier relations request it, using the same random polynomial. Its GRH branch uses bounded genus-two smoothness tests. The largest budget is algebraic smoothness recognition at $62/25+\sqrt{76313/322500}=2.966445739\ldots$, followed by raw proposals and rational testing at $237/80=2.9625$. The analysis charges $57/20=2.85$ for dense elimination, products, and the public root. Theorem H.9 states success probability at least $1/512$ per epoch on sufficiently large nonterminal inputs. This is an asymptotic analysis. [Proof outline](https://crypto.sjtu.edu.cn/factoring.pdf#page=3) · [Table 2 and Theorem H.9](https://crypto.sjtu.edu.cn/factoring.pdf#page=143)

The pinned readable GRH dependency in the combined two-thirds build exports both primitive Dirichlet GRH and the zeta statement. These cover the hypothesis KeyBreak states. The descent, relation counts, and bit-cost analysis of KeyBreak remain at manuscript level here. A smaller projective grid gives a separate manuscript-level deduction around 2.8845, conditional on the underlying pointwise moment and algebraic extraction estimates. The fixed-menu transfer and transposed-extraction bounds now have written arguments. [Combined Lean build](cogentic-worst-case-verification.md#combined-build-with-the-readable-grh-proof) · [Candidate and open proof obligations](cogentic-thin-denominator-candidate.md)


## How many moments suffice for the comparison?

For a fixed even trace order $k$, put $\rho=2(xc+1/x)/(3b)$. On the full grid the effective count of jointly smooth columns has log coefficient $2c-\rho$. The repeated-position term in the trace bound requires $k(2c-\rho-b)>2b$. The numerator progression estimate also requires $c>2b$. Approaching $b=c/2$ and $x=1/\sqrt c$ from the feasible region gives $c^{3/2}=16k/(9k-6)$ at the boundary. Thus the limiting full-grid coefficient along this family is $2(16k/(9k-6))^{2/3}$ for each even $k>2$. The sieve term $2c$ bounds the other two terms near this boundary for $k>2$ (strictly for the retained-column term). Letting $k$ grow recovers the coefficient in the table. [High-moment rank and cost argument](cogentic-projective-trace.md#randomized-coefficient)

A single fixed schedule already gives the comparisons below. Each row satisfies the strict trace and grid inequalities in exact rational arithmetic. In the smaller-grid row, the effective count has log coefficient $b+\eta$, where $\eta=0.078$. That row checks the proposed cost formula only. [Exact rational replay](../experiments/cogentic-variable-multiple-costs.py)

| Grid | $k$ | $c$ | $b$ | $x$ | Cost coefficient |
| --- | ---: | ---: | ---: | ---: | ---: |
| Full | 38 | 1.48496 | 0.74247 | 0.82062 | 2.96992 |
| Full | 44 | 1.4826 | 0.74129 | 0.82127 | 2.9652 |
| Smaller, candidate | 24 | 1.8714 | 0.93569 | 0.731 | 2.96307 |

The second full-grid schedule also falls below the largest cost in KeyBreak’s published parameter choice, approximately 2.966446. These comparisons concern leading coefficients on paper. Neither the rational replay nor the numerical comparison verifies the arithmetic estimates or measures a runtime at finite input sizes.
