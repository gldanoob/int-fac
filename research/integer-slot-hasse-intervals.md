# Integer factors and the classical mean cost of deterministic factoring

Let \(P\) be large, \(L=\log P\), \(\ell=\log L\), and \(25/32<\sigma<1\) fixed. There is a constant \(C=C(\sigma)\) such that, with
\[
 u=CL^{2/3},\qquad Y=e^u,\qquad V=\exp(1000 L\ell/u),
\]
all but \(P^{\sigma+o(1)}\) primes \(P<p\le 2P\) have at least \(\sqrt P/V\) distinct integers \(n=4m\) in \(|n-(p+1)|\le\sqrt p\), with \(m\) odd and \(Y\)-smooth. The [two elliptic searches and their recursive charge](zero-density-hasse-intervals.md#complete-deterministic-factoring-in-classical-mean-time) then give deterministic complete factoring with mean bit cost \(\exp(O(b^{2/3}))\) on ordinary \(b\)-bit integers and on balanced semiprimes. This deduction uses classical estimates published through 2025. A [stronger mean estimate](mean-time-elliptic-factoring.md) follows from the proved ordinary Riemann hypothesis. [Independent verification of ordinary RH and Dirichlet GRH](https://math.mit.edu/~drew/grh/)

## A short product of odd integers

Set \(T_0=L^8\), \(T_1=\sqrt P L^4\), \(H=L^4\), and take the even integer \(Z=2\lfloor e^{u/2}/2\rfloor\). Use the uniform probability on odd \(r\) in \((Z,2Z]\) satisfying \(\Omega(r)\le B=\lceil 100\ell\rceil\), where \(\Omega\) counts prime factors with multiplicity. Write \(I(t)\) for the Fourier transform on logarithms. Every such integer is \(Y\)-smooth. The probability of the discarded elements in the original uniform measure is \(O(L^{-10})\). Indeed, for \(v=1+1/\log(2Z)\),
\[
 \sum_{r\le 2Z}(3/2)^{\Omega(r)}
 \le (2Z)^v\prod_p(1-(3/2)p^{-v})^{-1}
 \ll Z\zeta(v)^{3/2}\ll Z(\log(2Z))^{3/2}.
\]
The ratio of the two Euler products is bounded since the terms after the linear term in their logarithms sum absolutely, uniformly for \(v>1\). Markov's inequality proves the tail bound. In particular, each retained element has probability at most \(4/Z\le8/r\), and trimming changes the transform by \(O(L^{-10})\).

For sufficiently large \(C\) and \(P\),
\[
                   |I(t)|\le1/2 \qquad(T_0\le |t|\le T_1).                 \tag{1}
\]
For \(Z/2\le |t|\le T_1\) use Ford's Corollary 2A with \(q=2\), its principal character, and \(N=Z\). Its hypotheses \(q\le N\) and \(2\le N\le q|t|\) hold. After dividing by \(Z/2\), the bound for all the odd integers is
\[
 10.463\exp\!\left(-\frac{\log^3(Z/2)}{133.66\log^2 |t|}\right).
\]
The exponent in the denominator form is uniformly at least \((1+o(1))C^3/(2\cdot133.66)\) in absolute value. Choose \(C\) so the displayed bound is at most \(1/4\). For \(T_0\le |t|<Z/2\), consecutive odd integers give monotone phase increments \(\theta_r=|t|\log(1+2/r)\asymp |t|/Z\) between zero and one. Summation by parts gives an unnormalized sum \(O(Z/|t|)\). In detail, write each summand as a first difference divided by \(1-e^{i\theta_r}\) and telescope. The real part of this reciprocal is constant and its imaginary part is monotone of size \(O(Z/|t|)\). This proves (1) after restoring the conditioning. [Ford, Corollary 2A](https://arxiv.org/pdf/1910.08209#page=4)

Use \(R=\lceil100\ell\rceil\) of these independent integer factors. Fix \(25/32<\sigma_0<\sigma\) and \(\xi,e,a,A_*\) as in the [wide prime construction](wide-prime-hasse-intervals.md#a-probability-measure-on-prime-logarithms). Put
\[
 x_0=P\sqrt 2/4,\quad J=\lceil(1+\xi)L/u\rceil,
 \qquad s=\frac{\log x_0-R\log Z}{J},\qquad w=\xi s.
\]
Here \(Js=(1-o(1))L\), \(s\asymp u\), and \(s+w\le u\). The discrete and comparison measures have transforms \(I^R Q^J\) and \(I^R Q_0^J\), using the same wide prime transform \(Q\) and continuous transform \(Q_0\). Smooth both by the same compactly supported kernel of logarithmic width \(h=1/(100\sqrt P)\). For every choice of the integer factors, the shift from the nominal center \(R\log Z\) is at most \(R\log 2=o(w)\). Thus the local central-limit argument there gives a uniform comparison density \(\gg1/L\) throughout \([\log(P/4),\log(P/2)]\) and a fixed neighborhood of its endpoints. The integer factor has total mass exactly one. Its transform has modulus at most one on the whole real line.

## Three high-frequency bounds

Keep the explicit formula, Gevrey truncation and low-frequency estimate in the [wide prime argument](wide-prime-hasse-intervals.md#locating-zeros-within-the-resolution-of-a-prime-slot). For \(|t|\le T_0\), the low-height zero-free region yields an error \(O(L^{O(1)}\exp[-c u\ell^{-2/3}(\log\ell)^{-1/3}])\) for one prime slot. This remains negligible after multiplication by \(T_0 J C_0^J\) for any fixed \(C_0\). At \(t=0\) it also gives \(Q(0)^J=1+o(1)\). The kernel controls the integral beyond \(T_1\). On \(T_0\le|t|\le T_1\) put
\[
                              d_c=K\log\ell/u
\]
with a fixed sufficiently large \(K\). The letter \(K\) in \(d_c\) denotes a constant independent of the smoothing kernel.

1. If some zero \(\rho\) with \(|\Im\rho-t|\le H\) has \(\Re\rho>1-d_c\), these frequencies have total measure \(O(L^{20})\) for all sufficiently large \(P\). Ford's uniform estimate \(N(1-d,T)\ll T^{58.05d^{3/2}}(\log T)^{15}\) applies at \(T=T_1+H\). Here \(Ld_c^{3/2}=O((\log\ell)^{3/2})=o(\ell)\), so there are at most \(L^{15+o(1)}\) such zeros. Each accounts for an interval of length \(2H\), with a factor two covering negative ordinates. By (1), the discrete absolute integral over their union is \(O(L^{20}2^{-R}Q(0)^J)=o(L^{-1})\). [Ford, consequence (iii) of Theorem 1](https://arxiv.org/pdf/1910.08209#page=2)

2. On all other high frequencies any lower bound \(d\in[d_c,1-\sigma_0]\) for the depths \(1-\Re\rho\) of the retained zeros gives \(|Q(t)|\le\exp(-asd)\). To verify uniformity, the local count in one frequency bin of width \(1/w\) and a real-part layer of depths \([v,2v]\) remains \(O(\ell+Lv^{3/2})\) for \(v\ge d_c\), since \(1/w\le d_c\). Writing \(v=h_0 d_c\), \(h_0\ge1\), the logarithm of this count, including its fixed constants, is \(O(\log\ell+\log h_0)\), by \(Ld_c^{3/2}=o(\ell)\). Since \(s d_c\asymp K\log\ell\), choosing \(K\) large absorbs the count, geometric summation over real-part layers, and all remainders exactly as in the wide prime argument. Group the frequencies containing some zero with \(\Re\rho>\sigma_0\) by bins of width \(1/L\) for the largest such real part \(\beta\), using the lower bin endpoint. For \(\delta=1-\beta\) take \(d=\max(d_c,\delta-1/L)\). Their measure is at most \(L^{O(1)}\exp(g\delta L)\), where \(A_*/2<g<a\), by the same compact-mesh and upper-strip density estimates. Because \(Js=(1-o(1))L\), summing the absolute integral gives \(O(L^{O(1)}\exp(-c' Ld_c))=o(1/L)\). [Local zero count and exceptional-frequency integration](wide-prime-hasse-intervals.md#locating-zeros-within-the-resolution-of-a-prime-slot)

3. On the remaining high frequencies take \(d=1-\sigma_0\). Exactly \(\lfloor J/2\rfloor\) prime slots give the squared pointwise bound \(P^{-a(1-\sigma_0)+o(1)}\). The complementary prime slots form a Dirichlet polynomial of length at most \(P^{(1+\xi)/2+o(1)}\) with square-sum at most \(P^{-(1-\xi)/2+o(1)}\). Bound \(|I(t)|^R\le1\) before applying the mean-value inequality to the complementary prime polynomial. Its squared integral costs \(P^{\xi+o(1)}\). The continuous transform is negligible throughout the high frequencies by the Gevrey bound for \(Q_0\). The same Plancherel and disjoint-center argument gives the exceptional-prime exponent \(\sigma\). [Mean-square and center estimates](wide-prime-hasse-intervals.md#the-exceptional-prime-count-and-mean-cost)

## Distinct orders and scalar size

For a discrete atom of product \(m\asymp P\), each prime slot can be assigned at most \(\log m/(s-w)=O(J)\) prime divisors. Once the \(J\) prime slots have been assigned, the remaining integer \(v\) is determined. A retained representation has \(\Omega(v)\le R B\). Label its prime factors with multiplicity. Every ordered factorization into \(R\) positive integers occurs among the at most \(R^{\Omega(v)}\) assignments of these labels to slots. Since the slot probabilities are bounded by \(8/r\) and the prime-slot numerators are bounded, the total atom is at most
\[
           m^{-1}(C_1J)^J 8^R R^{RB}.
\]
The logarithm of the extra integer factor is \(O(\ell^2\log\ell)=o(L\ell/u)\). All multiplicities together cost at most \(V^{1/50}\) for sufficiently large \(P\). Comparing the convolution lower bound \(\gg1/L\) to the kernel height \(O(\sqrt P)\) yields more than \(\sqrt P/V\) distinct orders as claimed. No integer factors or zero ordinates enter the implemented factoring algorithm. The stage cutoffs satisfy \(\log Y=O(L^{2/3})\) and \(\log V=O(L^{1/3}\log L)=O(L^{2/3})\). With \(\sigma=167/200\) the pointwise backup at exponent \(31/200\) again leaves the summable margin \(1/100\). [Exact finite coefficient and mass checks](../experiments/integer-slot-hasse.py) · [Complete factoring and recursive charge](zero-density-hasse-intervals.md#complete-deterministic-factoring-in-classical-mean-time)
