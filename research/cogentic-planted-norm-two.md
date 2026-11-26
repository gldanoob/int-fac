# Planting a growing set of simultaneous norm-two relations

For every sufficiently large odd \(N\), a deterministic polynomial-bit-time construction either finds a proper divisor or produces a pair of monic Eisenstein polynomials with a common root modulo \(N\). It prescribes \(r\) primitive marks at which both polynomial values are exactly 2. Here \(r\) grows on the same scale as the field degrees. The associated unit ratios have at least \(\binom{h+r-2}{r-1}\) distinct common images modulo \(N\). [Executable construction](../experiments/cogentic-planted-norm-two.py)

Let \(L=\log N\), \(W=L^{1/3}(\log L)^{2/3}\), and \(V=L^{2/3}(\log L)^{1/3}\). Take \(h\) from the [monic degree schedule](cogentic-monic-pair.md), so \(h\sim(L/\log L)^{1/3}\), and let \(m\) be the largest odd integer with \(m^h\le N\). Put \(r=\lfloor h/2\rfloor\), take the cuts \(t_j=2j\) for \(0\le j<r\), and set \(P(X)=\prod_j(X-t_j)\). For sufficiently large \(N\), \(0<m-t_j<N\) for all \(j\). Testing each \(\gcd(m-t_j,N)\) gives either a proper divisor or an invertible \(P(m)\).

Choose the unique odd \(T\) in \([0,2N)\) congruent to \(-2/P(m)\) modulo \(N\). Construct a monic \(Q=X^h+2\sum_{i<h}c_iX^i\) with \(Q(m)=T\) by taking \(h-1\) Euclidean base-\(m\) remainders of \((T-m^h)/2\) and keeping the final signed quotient as the highest digit. The lower digits are less than \(m\). Since \(N<(m+2)^h=(1+o(1))m^h\), the final quotient is \(O(m)\), including when the initial integer is negative.

For \(s=0,1,2\) form

\[
 F_s=PQ+2+4s(X-m)P,\qquad G_s=F_s+(X-m)PX^h.
\]

Both have value \(P(m)T+2\) at \(m\), a positive multiple of \(N\). Both have value 2 at every \(t_j\). Modulo 2, \(P=X^r\) and \(Q=X^h\), so \(F_s=X^{h+r}\) and \(G_s=X^{h+r+1}\) modulo 2. Both constant terms are exactly 2. This proves irreducibility by Eisenstein and gives two distinct fields of consecutive degrees. At \(m\), each derivative has been shifted by \(4sP(m)\). Its gcd with \(N\) is proper, one, or \(N\). For either derivative, the last outcome occurs for at most one \(s\), since \(4P(m)\) and the nonzero differences \(1,2\) are units. Thus a test either factors \(N\) or finds an \(s\) with both derivatives invertible. The [integral reduction maps](cogentic-monic-index.md) then exist for both fields.

The coefficient 1-norm of \(P\) is at most \((1+2r)^r\). Multiplication and addition in the displayed formulas give both polynomials logarithmic height at most \(\log m+O(h\log h)=(1+o(1))V\). At \(|a|,|b|\le\exp(cW)\) both homogeneous values are at most \(\exp((1+\tfrac32c+o(1))V)\) for fixed \(c>0\), since their degrees are \(h+r+O(1)\). The integer root, gcd tests, modular inverse, digit extraction, and polynomial products all use polynomially many operations on integers with polynomially many bits in \(L\).

## Power-order units and their common images

For either defining polynomial \(H\), let \(\alpha\) denote its root. The principal element \(t_j-\alpha\) has signed norm \(H(t_j)=2\). For any cut \(t\), \((H(X)-2)/(X-t)\) is an integer polynomial, which at \(\alpha\) equals \(-2/(\alpha-t)\). Since \(t\) is even, both

\[
 u_t=(\alpha-t)/\alpha=1-t/\alpha,\qquad
 u_t^{-1}=\alpha/(\alpha-t)=1+t/(\alpha-t)
\]

belong to the power order. Thus \(u_t\) is an explicit norm-one unit in each field and both reductions give \((m-t)/m\bmod N\).

Take products of the \(r-1\) nonconstant units with nonnegative exponents and total degree at most \(h-1\). Pad each with zero cuts to length \(h-1\). After multiplying by the common denominator \(m^{h-1}\), the numerator is a product of exactly \(h-1\) integers \(m-t_j\). Each numerator lies between 1 and \(m^{h-1}<N\). Distinct exponent vectors give different monic polynomials \(\prod(X-t_j)\) with multiplicities, by unique factorization. Each coefficient has absolute value at most \((1+2r)^{h-1}\), which is \(o(m)\) since \(h\log h=O(W)=o(V)\). Two such polynomials agreeing at \(m\) have a difference with constant coefficient divisible by \(m\) and of absolute value less than \(m\). Removing that zero coefficient and repeating proves equality of all coefficients. The numerator residues are therefore distinct, giving the stated binomial count in \((\mathbb Z/N)^\times\).

This supplies \(r\) genuinely simultaneous smooth primitive marks on *every* surviving input, and explicit units in both fields with shared residue images. The binomial count concerns distinct modular values. The resulting products can have the same square class. In particular, when all aggregate exponents are even the two canonical half-products have the same reduction, giving a trivial difference gcd. Productive square dependencies on every input remain open. [Criterion for a productive basis relation](cogentic-square-kernel-splitting.md)
