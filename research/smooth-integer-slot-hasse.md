# Smooth integer factors longer than the smoothness cutoff

For \(L=\log P\), \(\ell=\log L\), write
\[
       u=C L^{2/3}\frac{\log\ell}{\ell^{2/3}},\qquad
       Y=e^u,\qquad V=\exp(1000L\ell/u).
\]
For every fixed \(25/32<\sigma<1\) a sufficiently large \(C\) gives at least \(\sqrt P/V\) distinct orders \(4m\) in \(|4m-(p+1)|\le\sqrt p\), with \(m\) odd and \(Y\)-smooth, for all but \(P^{\sigma+o(1)}\) primes \(P<p\le2P\). Using classical estimates alone, the deterministic complete factoring algorithm has mean bit cost
\[
  \exp\!\left(O\!\left(b^{2/3}
       \frac{\log\log(4b)}{(\log(2b))^{2/3}}\right)\right)
\]
over ordinary \(b\)-bit integers and balanced semiprimes. The larger smooth factors used in its analysis preserve the same algorithmic scalar cutoff \(Y\). The proved ordinary Riemann hypothesis gives the stronger \(\exp(O(\sqrt{b\log(2b)}))\) mean bound in the [ordinary-RH proof](mean-time-elliptic-factoring.md). [Verification of ordinary RH and Dirichlet GRH](https://math.mit.edu/~drew/grh/)

## Phase concentration for dense subsets of integers

Fix \(\kappa=1/1000\), take \(k=\kappa\ell/\log\ell\), and use the even integer \(Z=2\lfloor\exp(ku)/2\rfloor\). From the odd integers in \((Z,2Z]\) retain those that are \(Y\)-smooth and have \(\Omega(r)\le\lceil100\ell\rceil\). Their proportion among all odd integers in the interval is at least \(D=L^{-1/200}\) for all sufficiently large \(P\).

Indeed Hildebrand's uniform estimate gives \(\Psi(cZ,Y)=(1+o(1))cZ\rho(k)\) for \(c\in\{1/2,1,2\}\). Its hypotheses hold already in de Bruijn's range \(k\le (\log Y)^{3/5-\varepsilon}\) with \(\varepsilon=1/10\). The change in the argument of \(\rho\) is \(O(1/u)\), giving ratio \(1+o(1)\) by Corollary 2.4 of Hildebrand–Tenenbaum, since \(\xi(k)=O(\log(k+1))\). Subtracting the even contribution gives \(\Psi(2Z,Y)-2\Psi(Z,Y)+\Psi(Z/2,Y)=(1+o(1))Z\rho(k)/2\). The Dickman asymptotic gives \(\rho(k)=L^{-\kappa+o(1)}\), since \(k\log k=(\kappa+o(1))\ell\). The [elementary moment bound](integer-slot-hasse-intervals.md#a-short-product-of-odd-integers) removes at most an \(O(L^{-10})\) proportion for the cutoff on \(\Omega\), as \(\log Z\ll L\). [Hildebrand's original theorem](https://doi.org/10.1016/0022-314X(86)90013-2) · [Hildebrand–Tenenbaum, Theorem 1.1, (1.7) and Corollary 2.4](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.101.pdf)

Put \(H_0=\lceil100/D\rceil\). At every \(L^8\le |t|\le\sqrt P L^4\) and every \(1\le j\le H_0\), the average of \(r^{-ijt}\) over all the odd integers in \((Z,2Z]\) has modulus at most \(L^{-1}\), for sufficiently large \(C,P\). If \(j|t|<Z/2\), the monotone-phase estimate gives \(O(1/(j|t|))\). Otherwise Ford's Corollary 2A gives an upper bound \(10.463\exp(-\log^3(Z/2)/(133.66\log^2(j|t|)))\). Here \(\log Z=(\kappa C+o(1))L^{2/3}\ell^{1/3}\) and \(\log(j|t|)\le(1/2+o(1))L\). The exponent thus saves at least \(((4/133.66)(\kappa C)^3+o(1))\ell\), which can exceed \(2\ell\). [Ford, Corollary 2A](https://arxiv.org/pdf/1910.08209#page=4) · [Small-frequency telescoping argument](integer-slot-hasse-intervals.md#a-short-product-of-odd-integers)

Use the Fejér kernel \(F_h(\theta)=h^{-1}|\sum_{j=0}^{h-1}e^{ij\theta}|^2\) at \(h=H_0\). Its constant Fourier coefficient is one and the sum of its coefficients is \(h\). The expectation of every translate under the full odd phase distribution is at most \(1+h/L<2\). For circular distance \(|\theta|\le1/h\), rotating the summands about their middle phase gives \(F_h(\theta)\ge h\cos^2(1/2)>h/2\). Thus at most \(4/h\le D/25\) of all odd integers have their phase in any arc of radius \(1/h\). For the uniform law on retained integers, the arc can contain at most \(1/25\) of its mass. Choosing the arc centered at the argument of its mean shows that its transform \(I(t)\) obeys
\[
                     |I(t)|\le1-cD^2
\]
for a fixed \(c>0\). This conclusion applies to every subcollection of relative density at least \(D\) in the full odd interval. The zero mean case also satisfies the inequality.

## Substitution in the integral and in the atom count

Use \(R=\lceil L^{1/50}\rceil\) of these smooth integer factors, with prime-slot parameters \(x_0,J,s,w\) chosen as in the [integer-factor argument](integer-slot-hasse-intervals.md#a-short-product-of-odd-integers). Then \(R\log Z=o(L)\), \(R\log2=o(w)\), and hence \(Js=(1-o(1))L\). The comparison lower bound remains \(\gg1/L\). At high frequencies the integer transform satisfies \(|I(t)|^R\le \exp(-c L^{1/100})\).

Use \(d_c=K\log\ell/u\) in the [three high-frequency estimates](integer-slot-hasse-intervals.md#three-high-frequency-bounds). Now \(L d_c^{3/2}=(K/C)^{3/2}\ell\). Ford's global zero count therefore gives a fixed power of \(L\) for the measure of the extreme frequency set, which \(\exp(-c L^{1/100})\) absorbs. In the local zero bound, \(\log(\ell+Lv^{3/2})=O(\log\ell+\log(v/d_c))\) for every \(v\ge d_c\). With \(s d_c\asymp K\log\ell\) and large fixed \(K\), the proof of the remaining prime-slot bounds goes through. More explicitly, the constants in the logarithm include \(O(\log(2+K/C))\), which is fixed once \(K,C\) are chosen. All the low-frequency, compact-density, mean-square and positive-kernel estimates retain their previous margins. At the low frequencies \(u\ell^{-2/3}(\log\ell)^{-1/3}\gg J+\ell\), as required by the direct product comparison.

Each retained integer factor has mass at most \(4D^{-1}/r\), since the set contains at least \(DZ/2\) elements. The count of ordered assignments to these factors is at most \(R^{R\lceil100\ell\rceil}\) after fixing the prime slots. The logarithm of the extra factor in the atom bound is
\[
  R\log(4/D)+R\lceil100\ell\rceil\log R=O(L^{1/50}\ell^2)=o(L\ell/u).
\]
Thus \(V\) still absorbs the full multiplicity, and \(\log V=o(u)\). The value \(\sigma=167/200\) gives the same summable charge for the pointwise backup at exponent \(31/200\). [Complete integer implementation and mean charge](zero-density-hasse-intervals.md#complete-deterministic-factoring-in-classical-mean-time) · [Finite smooth counts and arc-concentration checks](../experiments/smooth-integer-slot-hasse.py)
