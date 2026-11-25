# One reusable advice string for the finite-coin factorer

For every fixed \(\eta>0\), an advice string of length
\[
                 b+(1+\eta)k_b+O(1)
\]
suffices to factor every positive integer below \(2^b\) deterministically in \(L_{2^b}[1/3,O(1)]\) bit operations per input. Here \(k_b=O(b^{2/3}(\log b)^{1/3})\) is a computable common upper bound for the number of random bits in the [one-intercept complete factoring trial](cogentic-one-intercept.md) at these lengths. One may take the maximum of its integer schedule lengths, or use a monotone envelope of the same order obtained by rounding an upper bound on that schedule. The decoder is uniform and expands the advice to polynomially many \(k_b\)-bit trials. The choice of advice is nonuniform. The earlier [finite-coin counting argument](cogentic-finite-coins.md) uses a list of independent seeds.

The uniform statement behind the advice concerns a fixed input \(N\). For any auxiliary length \(n\le b^{O(1)}\) with \(n\ge K=\lceil(1+\eta)k_b\rceil\), a deterministic decoder succeeds for **all but fewer than \(2^K\)** among the \(2^n\) possible auxiliary strings. Consequently, if an auxiliary string conditioned on this input has point masses at most \(2^{-h}\), its failure probability is less than \(2^{K-h}\). No random bits are needed by the decoder. In any set of \(J\) distinct auxiliary strings, at most \(\min(J,2^K-1)\) fail. This includes shifted integer intervals whose entries all have an injective \(n\)-bit encoding. The auxiliary strings are additional inputs in this statement.

## Expanding the advice

For a target \(2\le N<2^b\) undergoing the extractor, let \(G_N\subseteq\{0,1\}^{k_b}\) be the intercept strings at which the complete, verified algorithm succeeds within its single-trial clock. Ignore surplus bits on shorter inputs. Its proved uniform success probability is \(1-o(1)\) as the input length grows. To make the statement uniform even for small targets, use trial division for inputs of at most \(\lceil\log_2(b+2)\rceil\) bits at a cost polynomial in \(b\). For the remaining targets \(|G_N|/2^{k_b}\ge 1/2\) for all sufficiently large \(b\). For finitely many \(b\) outside this asymptotic range a verified trial-division fallback has bounded cost. The complete-trial property ensures a single string suffices for each target, including its prime powers.

Use Guruswami, Umans and Vadhan's explicit \((K,1/4)\) extractor
\[
       E:\{0,1\}^n\times\{0,1\}^{d_0}\longrightarrow\{0,1\}^{m_0}.
\]
Choose their loss constant \(\alpha=\eta/(1+\eta)\). Theorem 1.5 gives \(m_0\ge(1-\alpha)K\ge k_b\) and \(d_0\le\log_2 n+O_\eta(\log(K+2))\). Extractor evaluation takes polynomial time. Truncate its output to \(k_b\) bits to obtain \(E'\), and enumerate every \(z\in\{0,1\}^{d_0}\). For each \(z\) run the complete verified trial on \(E'(a,z)\). The total number of trials is polynomial in \(b\). The ordinary seeded-extractor guarantee suffices because we average over the seed in the proof and enumerate it in execution. [Guruswami–Umans–Vadhan, Theorem 1.5](https://scholar.harvard.edu/files/salil/files/acm2009.pdf#page=4)

If at least \(2^K\) strings \(a\) fail this list for the same \(N\), take \(X\) uniform on any \(2^K\) of them. This source has min-entropy \(K\), yet \(\Pr(E'(X,U_{d_0})\in G_N)=0\). Uniform \(k_b\)-bit strings land there with probability at least \(1/2\). This contradicts statistical distance at most \(1/4\), also valid after truncation. This proves the exceptional count and its assertion for arbitrary conditional point masses.

For the advice theorem take \(n=b+K\). The fewer than \(2^b\) targets exclude fewer than \(2^{b+K}\) master strings in total. Fix one of the survivors. With \(n=b+K+t\) for an integer \(t\ge1\), choosing one uniformly random master string instead succeeds **simultaneously** on every target with probability exceeding \(1-2^{-t}\). Either length includes all smaller input lengths in the same choice.

## What density alone implies

Consider arbitrary dense tests indexed by \(b\) bits, on a trial space of \(2^{k_b}\) points. Fix any proposed advice decoder which supplies at most \(2^{k_b-1}\) trial points per advice string, independent of the test label. If its advice width is at most \(b\), assign to each advice string its own label and give that label the complement of its decoded list as its success set. Every label is still at least half successful, and every advice is defeated by its assigned label. The same proof permits label-dependent decoding by taking the complement of the list decoded on the assigned label. This certifies the leading \(b\) term for a generic density-only argument with short trial lists. The arithmetic structure of the actual factoring tests could admit shorter universal advice or uniform generation.

The [integer replay](../experiments/cogentic-extractor-advice.py) computes the exact largest statistical-distance error over all flat sources of 32 strings in a toy 256-point multiplier family, by sorting the hit counts for all 256 output events. The largest error is \(173/512\). All 163 events of uniform mass at least one half have fewer than 32 exceptional masters, all 163 tested unions of eight such exceptional sets have a common survivor, and an eight-label example verifies the list obstruction.
