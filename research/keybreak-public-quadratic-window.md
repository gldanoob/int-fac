# Public square relations in a short quadratic window

One can enumerate \(\Theta(X^2/N)\) pairs \(h^2\equiv u\pmod N\) with a known positive root \(h\asymp X\) and \(0<u\le X\), where \(X=\sqrt N\exp(tH)\) and \(H=(\log N)^{1/3}(\log\log N)^{2/3}\). Only \(u\) needs private-band recognition. The counted one-coordinate products include sufficiently many modular squares on the same accepted field. A separate short-root estimate would be needed to guarantee that any appreciable fraction occur in the enumeration. An average over varying inputs gives the expected leading density, with no uniform single-input conclusion.

## Exact enumeration and certification

Take \(t>0\) fixed and round \(X\) to an integer. Let \(I=[X/8,X/4]\cap\mathbb Z\), and for each integer \(k\) for which \((kN,kN+X]\) intersects the squares of \(I\), intersect \(I\) with
\[
 [\lfloor\sqrt{kN}\rfloor+1,\ \lfloor\sqrt{kN+X}\rfloor].
\]
It suffices to loop over the enlarged range from \(\lfloor(\min I)^2/N\rfloor\) through \(\lfloor(\max I)^2/N\rfloor\). Since \(X<N\) for large \(N\), every output has \(k=\lfloor h^2/N\rfloor\) and is output once. Throughout the interval the difference between successive squares is between constant multiples of \(X\), so each \(k\) yields \(O(1)\) candidates. For every \(k\) with \(\sqrt{kN}\) between \(\min I\) and \(\max I-1\), the first square above \(kN\) differs from it by at most \(2\sqrt{kN}+1<X\). Those interior values of \(k\) number \(\Theta(X^2/N)\). This proves a uniform raw count and time \(\exp((2t+o(1))H)\) before recognition, including integer square roots, bit-length checks and gcds. Any shell with fixed positive endpoints times \(X\) has the same upper count. For shells farther from zero, a lower count does not follow from the unit spacing argument.

A nonunit \(h\) in this shell gives a proper gcd. If two different unit roots in the shell have the same \(u\), then \(h-h'\) and \(h+h'\) are both nonzero modulo \(N\). Their product is zero modulo \(N\), so the gcd checks give a proper divisor. In a full enumeration one can detect such collisions by a sort at quasilinear cost in the record length. Thus on no split the residuals are distinct. The same gcd check applies to a residual that is itself an integer square, since its positive integer root is much smaller than the shell. Removing repeated residue records does not require guessing their distribution.

A squarefree \(u\) that passes the prescribed band tests can be sent to the same top-prime descent on the same sampled field, once for each recorded prime factor. For a completed descent with certified identities \(p=q_p\psi(\gamma_p)\pmod N\), multiplying them gives a public row
\[
 \left(\prod_{p\mid u}q_p\right)\psi\left(\prod_{p\mid u}\gamma_p\right)
 \equiv h^2\pmod N .
\]
The row has a known comparison root and zero private label. It still pays for all bounded search attempts and needs the usual algebraic occurrence records, character tests and exact square certification. Even pairwise distinct residuals give no rank or private-law overlap bound after descent. [KeyBreak, §H.5 and the top descent](https://crypto.sjtu.edu.cn/factoring.pdf#page=135) · [Public span requirements](keybreak-public-span-schedule.md)

## There are enough modular-square products before the root restriction

Write \(L=\log N\) and \(D=(L/\log L)^{1/3}\). On the rough-input branch, the prepass gives \(\omega(N)=O(D\sqrt{\log L})\). Fix a staged recipe with \(\Theta(D)\) total prime choices, dyadic prime bands in \(\exp(\Theta(DH))\), and two-coordinate loss weights \(w_i\). Adjust the logarithmic length allocation to a power of two at most \(X\). Adding \(O(H)\) to the coordinate log size changes its leading band fractions and exponents by \(o(1)\). Let \(S_j=\sum_{i<j}w_i\) and \(S=S_J\), where \(J\) is the number of stages. The H.20 counting construction supplies a set of one-coordinate products of size at least \(X\exp(-(S/2+o(1))H)\). A matching upper exponent follows from the one-coordinate version of the staged Rankin bound. [Staged shape count and prefix estimates](keybreak-private-band-stages.md) · [Rough-input case](keybreak-private-shape-work.md#ensuring-the-count-suffices-on-every-input)

In fact the same leading lower bound holds for the products that are squares modulo \(N\). Use the quantitative mean in Proposition G.12, with the G.11 bound and its original rapidly growing \(A\), to bound the expected bad-parent fraction by \(D^{-\omega(1)}\) in each of the prescribed dyadic bands. Markov and the polynomial number of bands give one field with bad fraction at most \(D^{-B_0}\) in every band, for any fixed \(B_0>0\). Use this only where the same rational-error hypotheses for those bands hold. Under Dirichlet GRH, the prime sum of each nontrivial quadratic character modulo \(N\) over a dyad at \(P=\exp(\Theta(DH))\) is \(O(\sqrt P\operatorname{polylog}(NP))\), uniformly in the character. Removing bad parents and primes of \(N\) makes the normalized character mean on the remaining primes \(O(D^{-B_0})\). If the recognizer separately requires an exceptional-prime deletion of size \(\exp(-\Omega(\sqrt{\log P\log\log P}))\), this also fits the same bound. [KeyBreak, Propositions G.11–G.12](https://crypto.sjtu.edu.cn/factoring.pdf#page=121) · [Elliptic recognition eligibility](keybreak-private-elliptic-recognition.md)

For every fixed ordered tuple of bands in the H.20 central coefficient, sample a prime uniformly and independently at each position from the good primes of its band. With \(m=\Theta(D)\) positions, the product's character means have modulus at most \((O(D^{-B_0}))^m\) on all nontrivial quadratic characters. Character orthogonality shows that the probability of each square class is
\[
 2^{-\omega(N)}\left(1+O\big(2^{\omega(N)}(O(D^{-B_0}))^m\big)\right)
 = 2^{-\omega(N)}(1+o(1)).
\]
The absolute probability of repeated prime choices is at most \(O(m^2/\min_i |\mathcal P_i|)=\exp(-\Omega(DH))\), with \(\mathcal P_i\) the eligible primes in a selected dyad. This is smaller than the square-class probability. Sum the resulting square-class lower count over the original band tuples and divide by \(m!\), exactly as for unrestricted square classes. The factor \(2^{-\omega(N)}=\exp(o(H))\) leaves the leading one-coordinate loss unchanged. This counts distinct targets in each class at the same leading scale. It does not place their roots in \(I\).

## The short-root distribution is a separate condition

For a fixed eligible set \(\mathcal S\subseteq [1,X]\) of units, the exact quantity needed is
\[
 \sum_{u\in\mathcal S}\#\{h\in I:h^2\equiv u\pmod N\}.
\]
Quadratic characters modulo \(N\) test for the existence of a root over the full residue ring. The count of square-class targets above does not control these short representatives. Sampling uniformly from all modular roots and testing whether the residual is at most \(X\) has raw success at most \(2^{\omega(N)}X/\varphi(N)=N^{-1/2}\exp(O(H))\) conditional on a unit. Sampling \(k\) or subwindows within a fixed cap changes how a fixed deterministic set is drawn. It cannot prove a lower bound for the set's intersection with \(\mathcal S\).

Even for an ordinary interval \(J'\subseteq[1,X]\), standard additive completion of the quadratic sum gives only
\[
 \#\{h\in I:h^2\bmod N\in J'\}
 =\frac{|I||J'|}{N}+O(\sqrt N\,\tau(N)\log^2 N).
\]
Indeed the complete sum with frequency \(a\) and any linear twist has absolute value at most \(\sqrt{N\gcd(a,N)}\), by squaring and summing the resulting linear phases for odd \(N\). Completing in \(h\) costs \(O(\log N)\), while the Fourier coefficient of \(J'\) is \(O(N/\min(a,N-a))\). Grouping by divisors of \(N\) bounds the remaining weighted harmonic sum by \(O(\tau(N)\log N)\). This error exceeds the raw scale \(X^2/N\). The exact raw count uses the square spacing argument instead. Restricting to the good products requires new information about their intersections with the enumerated candidates. For example, when \(N=M^2-C\) with a fixed positive odd \(C\), the square multipliers \(k=b^2\) in the shell have first positive residual \(Cb^2\), since \(\lfloor b\sqrt N\rfloor+1=bM\) for \(b=\exp(O(H))\). This subfamily has a common rational square class and is no model for random residuals. The example makes no claim about the full shell.

Existing smooth-polynomial estimates do not give the needed uniform result. The quadratic-polynomial estimates of de la Bretèche and Drappeau for friable outputs give upper bounds. Balog, Blomer, Dartyge and Tenenbaum prove lower bounds for fixed binary forms in a two-dimensional box. Setting \(k=b^2\) here would use a growing coefficient \(N\) and the narrow strip \(0<h^2-Nb^2\le X\), with only \(O(1)\) possible \(h\) per \(b\). Martin's conditional smooth-value asymptotic assumes a prime-values conjecture and concerns a different parameter range. These results provide no lower bound for the fixed \(N\) strip. [De la Bretèche–Drappeau](https://doi.org/10.4171/JEMS/951) · [Balog–Blomer–Dartyge–Tenenbaum](https://tenenb.perso.math.cnrs.fr/PPP/friableforms.pdf) · [Martin](https://arxiv.org/abs/math/9909180)

## An input-average count and the conditional work

There is a uniform estimate when varying the input is allowed. Let \(N\) range over odd integers in \([M,2M]\), let \(K=\exp((2t+o(1))H_M)\) with \(H_M=(\log M)^{1/3}(\log\log M)^{2/3}\), and set \(X_M=\sqrt{MK}\). Fix a set \(\mathcal S\subseteq[1,X_M]\) independently of the varying \(N\), with every prime factor at least \(P=\exp(\Omega(D_MH_M))\) and with \(O(D_M)\) prime factors counted with multiplicity. Here \(D_M=(\log M/\log\log M)^{1/3}\). For each \(u\in\mathcal S\), Dirichlet GRH gives \(\gg K/\log K\) primes \(k\in[K,2K]\) with \((u/k)=1\), uniformly because the character conductor is at most \(4X_M\) and the prime-sum error is \(O(\sqrt K\operatorname{polylog}(MK))\). When \(u\) is a square, all such primes except its divisors qualify.

For each such \((u,k)\), choose \(h\) in
\[
 [\sqrt{kM+u},\sqrt{2kM+u}]
\]
with \(h^2\equiv u\pmod k\) and parity opposite to \(u\), which makes \(N=(h^2-u)/k\) odd. There are \(\gg\sqrt{M/K}\) choices from either root class modulo \(k\), since the interval length is \(\Theta(\sqrt{MK})\) and the joint congruence has modulus \(2k\). Excluding \(h\) divisible by any prime of \(u\) loses relative \(O(D_M/P+D_M\sqrt{K/M})=o(1)\). Every remaining \(h\) is a unit for its resulting \(N\). Each counted solution is a valid record for its input, and \(h\asymp X_M\). Summing and dividing by the number of odd inputs gives mean at least
\[
 \gg \frac{|\mathcal S|\sqrt{K/M}}{\log K}.
\]
For \(|\mathcal S|=X_M\exp(-(S/2+o(1))H_M)\), this has leading exponent \(2t-S/2\). The calculation does not hold the input fixed or allow \(\mathcal S\) to depend on each input's field. The root shell in the average calculation can be any fixed constant enlargement containing the displayed intervals.

For a single-input reduction at the expected density, one would need at least \(\exp((2t-S/2-o(1))H)\) good residuals in an enumerated shell and upper prefix counts \(\exp((2t-S_j/2+o(1))H)\) for the staged tests. Under those additional premises, \(2t=b+S/2\) at the level of leading coefficients would target \(\exp((b+o(1))H)\) launches, with slack for subleading factors. If stage \(j\) costs \(\exp((c_j+o(1))H)\) per call, its leading coefficient is then \(b+(S-S_j)/2+c_j\). This is the proposed one-coordinate saving. The existing Rankin prefix bound counts integers up to \(X\), far larger than the window list, and cannot justify any of these window prefix counts. The rigorous unfiltered charge takes the whole list at every stage. The work and completion of the top descents and their parity rank remain separate, even under the stated supply and prefix premises.
