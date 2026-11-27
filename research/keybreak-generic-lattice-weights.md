# Uniform primitive counts on generic two-dimensional KeyBreak lattices

Let \(N\) be odd, let \(z\) be a unit modulo \(N\), and take positive scales \(T,X\). Put \(V=TX/N\) and assume \(V\ge1\). In normalized coordinates the lattice is
\[
\Lambda_z=\{(t/T,h/X): t,h\in\mathbb Z,\ h\equiv zt\bmod N\},
\qquad \det\Lambda_z=1/V.
\]
Take the Euclidean shortest length \(\lambda=\lambda_1(\Lambda_z)\). Let \(C_z\) count the points in \(1\le t/T<2,\ 1/8\le h/X\le1/4\) with \(t\) odd and \(\gcd(t,h)=1\). Then, with an absolute implied constant,
\[
 C_z=\frac{V}{2\pi^2}
 +O\left(
   V\lambda+1+\frac{\log(2+\lambda^{-1})}{\lambda}
   +V\sum_{p\mid N}\frac1p+\omega(N)(1+\lambda^{-1})
 \right).
\]
Either choice of inclusion for the upper edge in \(h\) has the same bound. This gives a uniform point count on the lattices passing the shortest-length filter. It does not estimate how often a sampler hits that set.

## Uniform rectangle discrepancy

For any translate of a two-dimensional lattice of shortest length \(\lambda'\), and any rectangle of diameter \(O(R)\), the point count differs from area divided by lattice determinant by \(O(1+R/\lambda')\). To see this, use a shortest lattice vector as the first basis vector and reduce the second along it to longitudinal component at most \(\lambda'/2\). The transverse line spacing \(s\) satisfies \(s\ge\sqrt3\,\lambda'/2\) since the second vector has length at least \(\lambda'\). On each line the lattice is a progression of spacing \(\lambda'\), so replacing its count by the chord length divided by \(\lambda'\) costs \(O(1+R/s)\) altogether. The rectangle chord length as a function of transverse coordinate has total variation \(O(R)\), including its possible endpoint jumps. The shifted Riemann sum with mesh \(s\) differs from the area divided by \(s\) by \(O(R)\). Multiplying by \(1/\lambda'\) finishes the bound, including boundary points and translated cosets.

## Primitivity and the odd-coordinate density

In the unscaled basis \((1,z),(0,N)\), the lattice coefficients of \((t,h)\) are \(t\) and \(j=(h-zt)/N\). Lattice primitivity means \(\gcd(t,j)=1\). For \(t\) odd this gcd is odd, so Möbius inversion uses only odd \(d\). The points with \(d\mid t,j\) are \(d\) times lattice points. Since \(d\) is odd, the latter points still have odd first integer coordinate. This is a coset of the index-two sublattice with even first integer coordinate. Its shortest length is at least \(\lambda\).

The original rectangle has area \(1/8\). The scaled count for each odd \(d\) is therefore \(V/(16d^2)+O(1+1/(d\lambda))\). There are no terms for \(d>C/\lambda\) with a fixed sufficiently large constant \(C\): dividing a point by such \(d\) would give a nonzero lattice point shorter than \(\lambda\). The accumulated errors are \(O(1+\lambda^{-1}\log(2+\lambda^{-1}))\), and extending the main term to all odd \(d\) costs \(O(V\lambda)\). Its Euler product is
\[
\frac{V}{16}\prod_{p\ {\rm odd}}(1-p^{-2})=\frac{V}{2\pi^2}.
\]

Any point with \(\gcd(t,h)=1\) is lattice-primitive. Conversely, a lattice-primitive point can have a common prime in \(t,h\) only at a prime dividing \(N\). Indeed at \(p\nmid N\), the congruence \(h=zt+Nj\) shows \(p\mid t,h\) exactly when \(p\mid t,j\). At \(p\mid N\), the shared-prime condition reduces to \(p\mid t\). This is an index-\(p\) sublattice with shortest length at least \(\lambda\), so at most \(O(V/p+1+\lambda^{-1})\) points of the rectangle lie in it, even before filtering parity and primitivity. Summing these upper bounds gives the claimed correction.

## Generic filter and finite check

For rational \(T,X\) given with polynomial bit length, a rational basis for \(\Lambda_z\) allows exact two-dimensional Gauss reduction after clearing denominators. One can compare \(\lambda^2\) with a rational squared threshold, or use the sup norm with absolute-factor slack since the norms differ by at most \(\sqrt 2\). The estimate is uniform in \(z\) and needs no factorization of \(N\) in the lattice filter.

If \(\lambda\ge N^\eta/V\) for fixed \(\eta>0\) and \(V=N^{O(1)}\), then
\[
\frac{C_z}{V}=\frac{1}{2\pi^2}
 +O\left(V^{-1/2}+N^{-\eta}\log N+\sum_{p\mid N}1/p\right).
\]
Here \(\lambda=O(V^{-1/2})\) by the two-dimensional lattice bound, and \(\omega(N)\le \log_2 N\). A nonempty generic class has \(V\gg N^{2\eta}\) by the same shortest-length bound. On a rough branch where \(\min_{p\mid N}\log p/H\to\infty\), one has \(\sum_{p\mid N}1/p=\exp(-\omega(H))\), by multiplying the largest reciprocal by at most \(\log_2 N\). The [existing rough-input prepass](keybreak-private-shape-work.md#ensuring-the-count-suffices-on-every-input) has this separation on its rough branch.

As a direct integer check, for \(N=1000003\) and \(T=X=300000\), enumeration gives counts \(4576\) and \(4597\) for \(z=314159\) and \(271828\). The leading term is \(4559.44\). This fixture enumerates \(t\) in the box, uses the unique \(h\) in \([0,N)\), and tests the two edges and ordinary gcd directly.

## Exact density for all odd moduli

The shared-prime correction can be included in the main term. For every odd $N$ and unit $z$, write $j=(h-zt)/N$ in the lattice coordinates above. The condition $\gcd(t,h)=1$ is equivalent to the pair of conditions

\[
 (t,N)=1,\qquad (t,j)=1.
\]

In one direction, a prime dividing $t$ and $N$ would also divide $h$, and a prime dividing $t$ and $j$ would divide $h$. In the other direction, a prime dividing $t$ and $h$ must divide $Nj$ by the lattice identity. When $t$ is odd and a unit modulo $N$, the lattice Möbius variable $d\mid(t,j)$ is automatically prime to $2N$. After scaling by $d$, both oddness and the unit condition apply to $t'=t/d$ as before. Expand the latter condition as a Möbius sum over $e\mid\operatorname{rad}(N)$. Requiring $e\mid t'$ with $t'$ odd gives the coset $t'\equiv e\pmod{2e}$, of lattice index $2e$. Its shortest lattice length is at least $\lambda$. Thus the contribution for each $(d,e)$ before applying its Möbius sign is

\[
 \frac{V}{16ed^2}+O\left(1+\frac{1}{d\lambda}\right).
\]

As before $d\le C/\lambda$ for every contributing point. Extend the main sum in $d$ to infinity, at a cost $O(V\lambda)$ per $e$. Summing the errors gives the following bound, with an absolute implied constant:

\[
 C_z=\kappa_N V+O\left(\tau(N)\left[V\lambda+1+
                   \frac{\log(2+\lambda^{-1})}{\lambda}\right]\right),
 \qquad
 \kappa_N=\frac{1}{16}\frac{\varphi(N)}N\prod_{p\nmid 2N}(1-p^{-2})
          =\frac{1}{2\pi^2}\prod_{p\mid N}\frac{p}{p+1}.
\]

The factor $1/e$ in the first main term is essential. The identity $\sum_{e\mid N}\mu(e)/e=\varphi(N)/N$ gives the displayed product. Also $\varphi(N)/N\ge 1/(1+\omega(N))$, by ordering the prime divisors and using $p_i\ge i+1$. In particular $\kappa_N\gg1/\log(2N)$. This proof uses the factorization of $N$ only in its analysis.

## Total variation without the shortest-vector filter

Take $X=N^{a+o(1)}$ and $T=N^{s+o(1)}$ with fixed $2/3<a<1$ and $1-a<s<a/2$. Let $\mathcal Z$ be the unit residues whose positive square residue is at most $X$. The complete Gauss-sum argument for the unit population gives $|\mathcal Z|=X\varphi(N)/N+O(N^{1/2+o(1)})$ for this range. That part of the argument only needs $a>1/2$. Choose $\eta>0$ with

\[
 2\eta<\min\{a+s-1,3a/2-1,s\}.
\]

For $\lambda>N^\eta/V$, the preceding pointwise bound yields $C_z=\kappa_N V(1+O(N^{-\eta+o(1)}))$. Here $\lambda\ll V^{-1/2}$ by the shortest-vector bound, $a+s-1>2\eta$, and $\tau(N)=N^{o(1)}$. On the other hand, the short-vector exception estimate bounds the number of $z\in\mathcal Z$ with $\lambda\le N^\eta/V$ by $O(N^{a-\gamma})$ for any fixed positive

\[
 \gamma<\min\{a/2,a+s-1-2\eta,3a/2-1-2\eta,s-2\eta\}.
\]

Its argument allows factors of $N$ in the short lattice vector. [Unit short-square population](keybreak-primitive-denominator-discrepancy.md#large-divisors-and-the-unit-population) · [Short-vector exceptions](keybreak-short-vector-exception.md)

For every $z$, including those exceptions, one has $C_z\ll V$. Indeed any two distinct counted ordinary primitive pairs are noncollinear as positive integer vectors. Their normalized determinant is a nonzero multiple of $N/(TX)=1/V$. The normalized vectors have bounded lengths and lie in a fixed angular interval, so their angular separation is $\gg 1/V$. The number of such directions is $O(V)$ for $V\ge1$. Consequently the exceptional residues contribute at most $O(VN^{a-\gamma})$ to the sum of $|C_z-\kappa_NV|$. Dividing the total error by $\kappa_NV|\mathcal Z|$ gives

\[
 \frac{\sum_{z\in\mathcal Z}|C_z-\kappa_NV|}{\kappa_NV|\mathcal Z|}
 \ll N^{-\min(\eta,\gamma)+o(1)}.
\]

Thus the output from an equal-weight primitive pair conditional on success has polynomially small total variation distance to uniform on $\mathcal Z$, even if the sampler keeps every exceptional lattice. The equal-weight denominator proposal has pair mass of order $1/(V X\log N)$ in this range. Since the total number of pairs is asymptotic to $\kappa_NV|\mathcal Z|$, its acceptance probability is at least a reciprocal polynomial in $\log N$. It can therefore be repeated with a polynomial cap. Its bounded-to-ideal coupling can be taken smaller than any prescribed inverse polynomial in $N$, so conditioning on acceptance preserves the stated power saving. This controls repeated draws as well. Over $\exp(O(H))=N^{o(1)}$ independent samples with $H=(\log N)^{1/3}(\log\log N)^{2/3}$, the sum of the per-sample errors still saves a power of $N$. Subsequent public computations can be coupled through the reported squares if the auxiliary pair data are kept private. [Equal-weight proposal and its coupling](keybreak-factored-denominator-proposal.md)
