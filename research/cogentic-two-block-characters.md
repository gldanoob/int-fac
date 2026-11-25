# Summing greedy smooth blocks without a factor of the factor-base size

Cogentic's proof of Proposition 9.3(2) uses two initial blocks of prime factors to estimate nonprincipal characters in a smooth-number progression. Its count over the two largest primes of those blocks costs \(B^2\), with \(B\) the factor-base bound. At the saddle this factor can be replaced by a polynomial in \(\log B\) and the smoothness parameter. The estimate below applies to an arbitrary set of eligible characters at each frequency. [Pinned paper, page 48](https://raw.githubusercontent.com/google-research/google-research/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=48)

Let \(q\ge1\), let \(\mathcal P\subseteq[2,B]\) be a finite set of primes coprime to \(q\), and write \(s=\alpha+it\), \(0<\alpha\le1\). A block is a nonempty squarefree \(\mathcal P\)-product \(a\) satisfying \(a/P^+(a)\le q<a\), so \(q<a\le qB\). For a Dirichlet character \(\chi\bmod q\) write
\[
 C_\chi(z)=\prod_{p\in\mathcal P,\,p>z}(1+\chi(p)p^{-s}),\qquad
 S_\chi=\sum_{\substack{a,b\ {\rm blocks}\\ P^+(a)<P^-(b)}}
    \chi(ab)(ab)^{-s}C_\chi(P^+(b)).
\]
This is the Dirichlet polynomial for the source's two greedy prefixes. Indeed each contributing integer has its primes in increasing order, with \(a\) the first prefix exceeding \(q\), \(b\) the first prefix of the remainder exceeding \(q\), and the remaining primes greater than \(P^+(b)\). Any supported integer greater than \(q^2B^2\) has both prefixes.

For any set \(\mathcal X\) of characters with
\(\max_{\chi\in\mathcal X,z}|C_\chi(z)|\le M\), we have
\[
 \sum_{\chi\in\mathcal X}|S_\chi|
 \ll M\left(1+\sum_{p\in\mathcal P} p^{-\alpha}\right)
    \varphi(q)q^{1-2\alpha}B^{2(1-\alpha)}(\log(2B))^3.
\]
The maximum need only include the cutoffs at an eligible prime and the endpoint above all primes. The bound holds even when all eligible primes are omitted.

To prove this, truncate the double sum at \(P^+(b)\le z\), omitting \(C_\chi\), and call the sum \(S_\chi(z)\). When a single prime \(p\) crosses the cutoff, the change in \(C_\chi\) is \(\chi(p)p^{-s}C_\chi(p)\) up to sign. Its magnitude is at most \(p^{-\alpha}M\). Discrete partial summation, applying the triangle inequality at each cutoff before summing over characters, reduces the claim to a uniform bound for \(\sum_\chi |S_\chi(z)|\), including the endpoint.

Index the primes by increasing size and pad this list to a power of two with unused indices. For each strict pair of indices there is a unique smallest dyadic interval containing them both. Its left child contains the first index and its right child contains the second. Thus \(S_\chi(z)\) is a sum of \(A_{I,\chi}B_{I,\chi}\) over dyadic parent intervals \(I\). Here the first sum groups blocks by \(P^+(a)\) in the left child. The second groups blocks by \(P^-(b)\) in the right child and \(P^+(b)\le z\). At each given level the first lists are pairwise disjoint, and so are the second lists.

For any such disjoint lists, first restrict to blocks of sizes \(T<a\le2T\), where \(T=q2^j\) and \(q\le T\le qB\). At most \(1+T/q\) of these integers lie in a specified residue class. Character orthogonality on the reduced residues, Cauchy–Schwarz, and disjointness of the lists give
\[
 \sum_I\sum_{\chi\bmod q}|A_{I,\chi,T}|^2
 \le \varphi(q)(1+T/q)\sum_{T<a\le2T} a^{-2\alpha}
 \ll\frac{\varphi(q)}q T^{2-2\alpha}
 \le \varphi(q)q^{1-2\alpha}B^{2(1-\alpha)}\,O(1).
\]
Adding the \(O(\log(2B))\) product-size slices in the joint Euclidean norm costs its square in the bound above. Apply the same estimate to the second lists and then Cauchy–Schwarz to the character-and-interval sum at each level. Summing the \(O(\log(2B))\) levels contributes the third logarithm. This bound is uniform in \(z\), as required.

In the source's application \((1-\alpha)\log B=\lambda_Y=\log u_Y+\log\log u_Y+O(1)\) and \(\sum_{p\in\mathcal P}p^{-\alpha}\ll u_Y\). Also \(\varphi(q)q^{1-2\alpha}\le q^{2(1-\alpha)}\). Using the source's uniform remainder Euler-product saving \(M\le e^{-.04u}\zeta_{\mathcal P}^{\rm sf}(\alpha)\), the resulting bound has only the costs \(q^{2(1-\alpha)}\), a polynomial in \(u,\log(2B)\), and the same Mellin integration as before. In particular this step no longer needs \(u\) to dominate \(\log B\). The term \(q^{2(1-\alpha)}\) continues to charge the arithmetic progression modulus.

A finite exact replay forms the consecutive prime blocks independently, recovers their ordered pairs by dyadic siblings, verifies summation by parts with rational coefficients, and computes the disjoint-list orthogonality estimate in residue classes. [Exact replay](../experiments/cogentic-two-block-characters.py)
