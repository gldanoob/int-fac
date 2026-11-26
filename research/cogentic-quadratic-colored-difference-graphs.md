# Prescribed quadratic colors on short difference graphs

Under Dirichlet RH, every prescribed coloring of the oriented differences of a fixed number of free integer coordinates occurs with positive density at a polylogarithmic height. The colors are the two Legendre bits at any two distinct unknown odd prime divisors of \(N\). A menu with \(\exp(O(H))\) tuples can cover graphs with a fixed positive multiple of \(\log H\) vertices, where \(H=(\log N)^{1/3}(\log\log N)^{2/3}\). Only an additive Fourier estimate and a two-variable convolution bound are needed.

## Fourier bounds at short heights

Write \(L=\log N\). Let \(p,q\mid N\) be distinct odd primes with \(p,q>T\), and take any of
\(\chi_p,\chi_q,\chi_p\chi_q\), the nonprincipal character factors of the color test. Let \(e(t)=\exp(2\pi it)\) and put
\[
 \delta=\frac1T\max_{\chi}\sup_{\alpha\in\mathbb R}
               \left|\sum_{n\le T}\chi(n)e(\alpha n)\right|.
\]
For \(2\le R\le\sqrt T\) and the heights below,
\[
 \delta\ll \frac1{\log(2T)}
        +\frac{(\log(2R))^{3/2}}{\sqrt R}
        + R\,\frac{\Psi(T,L^3)}T,                              \tag{1}
\]
with absolute constants. Here \(\Psi(T,y)\) counts integers up to \(T\) all of whose prime divisors are at most \(y\).

Use a reduced approximation \(a/r\) with \(r\le Q=\lfloor T/R\rfloor\) and \(|\alpha-a/r|\le 1/(rQ)\), by Dirichlet approximation. Since \(r\le Q\), the usual \(1/r^2\) condition holds. If \(r\ge R\), Montgomery–Vaughan's Corollary 1 for \(1\)-bounded multiplicative functions gives the first two terms in (1), with the parameter replaced by an absolute constant multiple at endpoints if needed. [Montgomery–Vaughan, *Exponential sums with multiplicative coefficients*](https://doi.org/10.1007/BF01390204)

If \(r<R\), split the sum at frequency \(a/r\) into its \(r\) residue classes. A prefix in one such class \(n\equiv c\bmod r\) can be bounded by writing \(n=dm\), with \(d=\gcd(c,r)\), and applying character orthogonality on the units modulo \(r/d\). The twists of \(\chi\) that result are all nonprincipal. Each small modulus is coprime to \(pq\), since \(r\le T<p,q\). The product character has a modulus between \(\min(p,q)\) and \(NR\); the Granville–Soundararajan estimate applies also to imprimitive characters. Every endpoint in the prefix is at most \(T\), hence below that modulus. Their Theorem 2 bounds all such sums by \(O(\Psi(T,L^3))\), since
\[
 (\log(NR))^2(\log\log(NR))^{20}\le L^3
\]
for large \(N\) and in the stated ranges. The rational frequency is constant in each class. Summation by parts for the remaining phase costs \(O(1+T|\alpha-a/r|)=O(1+R/r)\), so the \(r\) classes together cost \(O(R\Psi(T,L^3))\). [Granville–Soundararajan, *Large character sums*, Theorem 2](https://arxiv.org/pdf/math/9903196#page=4)

For \(T=\lceil L^C\rceil\) take \(R\) to be a large fixed constant. The fixed-exponent smooth-number density is \(\Psi(T,L^3)/T=\rho(C/3)+o(1)\), for the Dickman function \(\rho\) with \(\rho(u)\to0\). Choosing \(R\) first and then a sufficiently large fixed \(C\) makes \(\delta\) smaller than any prescribed positive constant. For \(T=\lfloor\exp(H/k)\rfloor\) with \(2\le k=O(\log H)\), take \(R=\lceil(\log T)^8\rceil\). Rankin's bound on the line \(\sigma=9/10\) gives
\[
 \Psi(T,L^3)\le T^{9/10}\prod_{\ell\le L^3,\ \ell\text{ prime}}
                  (1-\ell^{-9/10})^{-1}
            \le T^{9/10}\exp(O(L^{3/10})).
\]
Here \(L^{3/10}=o(\log T)\), so (1) gives \(\delta\ll1/\log T\).

## A color on one edge

Choose one orientation for each unordered pair of vertices. Prescribing the reverse orientation as well requires adding \(L(-1)\) to its two Legendre bits. For distinct \(x,y\in[1,T]\) all differences are units at \(p,q\). The indicator for the label \(\gamma=(\gamma_p,\gamma_q)\) on \(x-y\) is
\[
 \frac14(1+(-1)^{\gamma_p}\chi_p(x-y))(1+(-1)^{\gamma_q}\chi_q(x-y)).
\]
On the diagonal set the indicator to zero. The characters themselves are zero there.

Embed \([1,T]\) in the cyclic group of order \(2T+1\). Extend \(d\mapsto\chi(d)\) on \(|d|<T\) to this group by zero elsewhere. Its unnormalized Fourier coefficients have absolute value at most \(2T\delta+2\) by the positive and negative parts and \(\chi(-d)=\chi(-1)\chi(d)\). Thus its convolution operator has that same \(\ell^2\) norm. In particular for \(X,Y\subseteq[1,T]\) and either orientation the color count \(e_\gamma(X,Y)\) satisfies
\[
 \left|e_\gamma(X,Y)-\frac{|X||Y|}{4}\right|
   \ll (T\delta+1)\sqrt{|X||Y|}+\frac{|X\cap Y|}{4}.             \tag{2}
\]
The same convolution bound applies to one character and any bounded unary weights on \(X,Y\).

For a fixed graph, expand the product of the displayed four-term functions on the entire product box. This agrees with the indicator product whenever the coordinates are distinct. If a term contains a nonprincipal character on edge \(ij\), first fix every coordinate except \(x_i,x_j\). All other edge factors that remain are now bounded unary functions of \(x_i\) or \(x_j\). The convolution bound gives normalized error \(O(\delta+1/T)\) for that term, uniformly over the fixed coordinates. The absolute expansion weights across all terms sum to one. For \(k\) vertices and \(m=\binom k2\) specified edges, the constant term is \(4^{-m}\), and removing tuples with coincident coordinates costs \(O(k^2/T)\). Hence the density is \(4^{-m}+O(\delta+k^2/T)\) on \([1,T]^k\). The polylogarithmic choice in (1), with small enough constant error for this \(k\), proves positive density. The argument also works in separate vertex intervals each having fixed positive relative length, with the expected constant term taken relative to the product of those intervals.

## Growing graphs within the enumeration budget

For \(k\ge2\) let each vertex start with a prescribed coordinate set of size at least \(M\). One can use \(M=T\) for free vertices or \(M=\lfloor T/k\rfloor\) for disjoint ordered consecutive blocks. Put \(\epsilon=k^{-2}\). In the current candidate set \(Y\) of any future vertex call a proposed next coordinate bad if it has fewer than \((1-\epsilon)|Y|/4\) neighbors of the required color. For the set \(D\) of bad coordinates, (2) bounds the deficit by
\[
 \epsilon |D||Y|/4
     \ll (T\delta+1)\sqrt{|D||Y|}+|D|/4.
\]
When \(|Y|\ge 2/\epsilon\), the diagonal error can be absorbed, yielding \(|D|\ll (T\delta+1)^2/(\epsilon^2|Y|)\).

Process vertices in order, restrict each future set to the corresponding neighbors, and keep choices good for every future vertex. After \(i-1\) choices every candidate set has size at least \(M((1-\epsilon)/4)^{i-1}\). The union of the bad sets at a stage thus occupies at most
\[
 O\!\left(k^5(T/M)^2(\delta+1/T)^2\,16^k\right)
\]
of the current candidate set. For any fixed \(0<c<1/\log 4\), take \(k\le c\log H\) and \(T=\lfloor\exp(H/k)\rfloor\). The last bound is \(o(1/k)\), even with the disjoint blocks, by \(\delta\ll k/H\). At least a \(1-1/k\) fraction of the current candidates are therefore good at each step. Multiplying the choice counts gives \(\gg 4^{-\binom k2}M^k\) tuples of each prescribed pattern. The factor \((1-\epsilon)^{\binom k2}\) and the product of the good fractions are bounded below by absolute constants. All coordinates in a realized pattern are distinct by the diagonal convention.

Enumerating all \(T^k\le e^H\) tuples works without knowing which colors occur. One may trial divide through \(T\) first and check differences by gcd. This supplies the color pattern simultaneously for every remaining pair of distinct prime divisors, with no selection based on secret labels. The same enumeration with fixed \(k\) and polylogarithmic \(T\) takes polynomial bit time in \(\log N\).

## Free differences and fixed roots

The key convolution step uses that the endpoints of the tested edge are separate free variables. It supplies all pairwise colors required to build a varying marked elliptic curve from the free coordinates. Fixing the three roots of a given elliptic curve instead prescribes the forms \(v,u-e_1v,u-e_2v,u-e_3v\) in two variables. Fixing a variable pair there does not leave the other forms unary, and the difference-graph argument does not establish those fixed-root patterns. They have a separate short-linear-form construction. Neither graph density nor the fixed-root pattern theorem implies smoothness of the resulting curve orders. [Moving curves](cogentic-moving-elliptic-separation.md) · [Fixed marked CM forms](cogentic-cm-linear-forms.md)
