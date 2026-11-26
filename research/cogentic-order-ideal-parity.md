# Ideal parity in arbitrary-degree explicit orders

Given a monic irreducible \(P\in\mathbb Z[X]\) and a list of nonzero explicit elements \(z_i\) in \(K=\mathbb Q[X]/P\), one can compute the full binary kernel of the maximal-order valuation vectors
\[
 \bigl(v_{\mathfrak p}(z_i)\bmod 2\bigr)_{\mathfrak p}
\]
in deterministic polynomial bit time in the combined explicit input. The algorithm needs neither a maximal-order basis nor a factorization of a discriminant or norm. Its named local ideal computations use only primes through \(\max(2d,d(d-1))\), where \(d=\deg P\). One may append a row for the sign of the rational norm if desired. This extends the [cubic order algorithm](cogentic-cubic-order-kernel.md), and uses the same [tame-profile comparison](cogentic-monic-singular-ideals.md) for the unnamed primes.

## Coprime invertible ideals in an overorder

Write \(\alpha=X\bmod P\) and start with \(B=\mathbb Z[\alpha]\). Scale each column by a rational square so that its representative \(\xi_i\) is in \(B\), and form the principal ideals \(\xi_iB\). Maintain the distinct proper integral ideals currently used to express these principals as products. They start invertible. If \(I,J\) are different and \(C=I+J\ne B\), compute the colon \(D=B:C\). Buchmann–Lenstra's invertibility criterion says that \(C\) is invertible exactly when \(D:D=B\). If it is invertible, replace \(I,J\) by \(C,IC^{-1},JC^{-1}\), omitting the unit ideal and merging duplicates while recording the product identities. If it is noninvertible, replace \(B\) by the strict overorder \(D:D\) and restart on the original principals in the enlarged order. [Buchmann–Lenstra, Proposition 2.5](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/buchlen/to.pdf#page=10)

An invertible \(B\)-ideal is principal over \(B\otimes\mathbb Z_p\) for every \(p\), since a rank-one projective module on a semilocal ring is free. Multiplication by a local generator gives
\[
 [B:I]=[\mathcal O_K:I\mathcal O_K],
\]
by using its determinant in the two ambient lattices locally and then taking the product of the local indices. The same argument proves multiplicativity of the index norm for invertible ideals. Thus the sum of the logarithms of distinct proper ideal norms decreases by at least \(\log 2\) at each refinement between restarts. The number of restarts is at most \(\log_2|\operatorname{disc}(P)|\), because each strict enlargement at least doubles the index in the original order and its square divides \(\operatorname{disc}(P)\). The resulting final atoms \(I_j\) are invertible and pairwise comaximal in \(B\), so their extensions are pairwise comaximal in \(\mathcal O_K\). Every \(\xi_i B\) is an explicitly known product of their powers.

It remains to decide whether every exponent of \(I_j\mathcal O_K\) is even, separately for each \(j\). If an atom has any odd exponent, its column exponents modulo two form one constraint on the input masks. If it has only even exponents, it adds no constraint. The comaximality proves that these rows give exactly the full ideal kernel.

## A short list of local generators

Fix an invertible integral atom \(I\) and a \(\mathbb Z\)-basis \(a_0,\ldots,a_{d-1}\). Put \(m=[B:I]\). At each named \(p\le T=\max(2d,d(d-1))\) dividing \(m\), compute the \(p\)-maximal overorder of \(B\), find the prime ideals above \(p\) by semisimple residue-algebra splitting, and test the extended ideal against the prime-ideal powers. The valuations are bounded by \(v_p(m)\). The field scan uses time polynomial in \(p\), which suffices for this cutoff. [Named-prime lattice construction](cogentic-monic-singular-ideals.md#known-rational-primes)

For the remaining unnamed primes, consider the \(d(d-1)+1\) elements
\[
 \gamma_t=\sum_{i=0}^{d-1}t^i a_i,\qquad 0\le t\le d(d-1).
\]
For a prime ideal \(\mathfrak p\mid p\) of \(\mathcal O_K\), divide the \(a_i\) locally by a generator of \(I\mathcal O_{K,\mathfrak p}\) and reduce them modulo \(\mathfrak p\). At least one residue is nonzero because the \(a_i\) generate the ideal there. The resulting nonzero polynomial over the residue field has degree at most \(d-1\), and rules out at most \(d-1\) values of \(t\bmod p\). There are at most \(d\) primes above \(p\). Since \(p>T\), the scanned integers are distinct modulo \(p\), and some \(\gamma_t\) has exactly the valuation of \(I\) at all primes above \(p\).

The integer \(h_t=|\mathrm N_{K/\mathbb Q}\gamma_t|/m\) is the index of \(\gamma_t B\) in \(I\). Its \(p\)-valuation is the sum of the residue-degree-weighted excesses \(v_{\mathfrak p}(\gamma_t)-v_{\mathfrak p}(I\mathcal O_K)\), each nonnegative. Thus a prime belongs to the support covered by \(\gamma_t\) exactly when \(p\nmid h_t\). Repeated gcd with \(h_t\) removes the entire support of \(h_t\) from the current unresolved part of \(m\), leaving a modulus for this \(\gamma_t\) on which its parity is exactly the parity of \(I\). After testing that modulus, divide it out of the unresolved part. The covering proof ensures that the scan finishes, including when the norm has unknown repeated prime powers.

## Parity of a generator that lies in a proper subfield

For an integral generator candidate \(\gamma=\gamma_t\ne0\), work in the explicit étale algebra \(E=K[Y]/(Y^2-\gamma)\), with basis \(\alpha^i,\alpha^iY\) for \(0\le i<d\). Scan \(z=Y+j\alpha\) for \(0\le j\le\binom{2d}{2}\) and accept the first squarefree characteristic polynomial of multiplication by \(z\). Above each embedding of \(K\), the two values of \(Y\) are distinct as \(\gamma\ne0\). Any two distinct points among these \(2d\) points collide for at most one \(j\). Thus a squarefree polynomial is found and is the full primitive polynomial of \(E\). Both \(\alpha\) and \(Y\) are integral, so this polynomial is monic integral even if the provided coordinates of \(\gamma\) in the original power basis have denominators. [Power-basis construction and coefficient bounds](cogentic-monic-square-extraction.md)

Factor this polynomial over \(\mathbb Q\) using deterministic rational polynomial factorization. If it splits, \(E\cong K\times K\) and \(\gamma\) is a field square, so its valuations are even. Otherwise \(E\) is a degree-\(2d\) field, and the [composite tame-profile test](cogentic-monic-singular-ideals.md#computing-the-weighted-sums-over-composite-inputs) applies to the original power order of \(K\) and the new power order of \(E\). At unnamed odd primes it decides whether the relative quadratic extension is unramified everywhere on the modulus support, which is equivalent to all the valuations of \(\gamma\) there being even. The profile is taken after the Buchmann–Lenstra overorder construction, so the new primitive polynomial may have index primes on this support. [Lenstra–Lenstra–Lovász, Theorem 3.6](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1982f/art.pdf) · [Buchmann–Lenstra, Algorithm 6.6 and Theorem 6.7](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/buchlen/to.pdf#page=32)

## Bit complexity and scope

The order and ideal calculations are rational lattice operations with polynomial bit cost. Overorders have polynomial-sized descriptions by the discriminant index bound. Every retained integral ideal in a refinement has index no greater than the product of the original column norms, and its Hermite basis over its current order has polynomial bit length. A colon is a lattice of simultaneous linear integrality conditions in dimension \(d\). The parameters \(t,j\) in the two scans are \(O(d^2)\), so the coefficients \(t^i\), the cover multiplication matrix, and its characteristic polynomial have polynomial bit length. There are polynomially many atoms, local generators, gcd reductions, and binary elimination operations. [Buchmann–Lenstra, Sections 5.8–5.9](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/buchlen/to.pdf#page=28)

With polynomial-sized raw radix field data and \(\exp(O(W))\) explicit columns this step fits in \(\exp(O(W))\) bit time. It applies to columns sharing unnamed prime ideals, since those are resolved by the coprime atom step. The output is the ideal-square kernel. Exact field-square dependencies and productive modular signs still require controlling the residual square classes and their images.

Run `python3 -B experiments/cogentic-order-ideal-parity.py` in a Python environment with SageMath. The replay compares all 1,920 masks, with and without a norm sign row, against named prime valuations in degrees one, two, four and six. It separately checks a quartic element in a proper quadratic subfield at a 150-bit composite, its square, and a scaled power order whose atom computation enlarges the order by index equal to the sixth power of that composite. Only the small comparison fixtures use the known-prime oracle. [Replay](../experiments/cogentic-order-ideal-parity.py)
