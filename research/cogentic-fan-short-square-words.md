# Short field-square words in a single-input fan

Fix one integer \(N\), one \(m\), and a degree-\(d\) polynomial \(f\in\mathbb Z[X]\) of leading coefficient \(c_d\ne0\), with \(f(m)=N\). Let \(f_j=f+j(X-m)\), with indices in an interval of \(J\) consecutive integers and \(d\ge2\). Use the irreducible \(f_j\) of degree \(d\) and write \(K_j=\mathbb Q(\alpha_j)\) for their fields. Take a menu of \(Q\) distinct primitive pairs \((a,b)\) with \(b>0\) and \(a-bm\ne0\). A word is a subset of the menu, and it is a field square at \(j\) if \(\prod_i(a_i-b_i\alpha_j)\in K_j^{\times2}\). The rational relation label \(a-bm\) is independent of \(j\). The following bounds apply before filtering for smoothness or matching rational squareclasses. [Exact rational root matching](cogentic-mnfs-sign-map.md#comparing-field-roots-for-one-integer-from-scratch)

## Separate norm squareclasses

For mark \(i\) put
\[
 F_i(j)=b_i^d f_j(a_i/b_i)=U_i+jT_i,\qquad
 T_i=(a_i-b_i m)b_i^{d-1}.
\]
Then \(F_i(j)=c_d\,\operatorname{Norm}_{K_j/\mathbb Q}(a_i-b_i\alpha_j)\). For a fixed word of \(k\) distinct marks, put
\[
 D_i=|c_d|\prod_{h\ne i}|a_i b_h-a_h b_i|.
\]
Each \(D_i\) is nonzero. If the word is a field square at index \(j\), each \(F_i(j)\) has signed squarefree part supported on the prime divisors of \(D_i\).

Indeed, \(\alpha_j\) is integral at every prime ideal above \(p\nmid c_d\). If two marks vanish in the same residue field above \(p\), then their determinant \(a_i b_h-a_h b_i\) vanishes modulo \(p\). For \(p\nmid D_i\), at each prime ideal where the \(i\)-th mark has positive valuation, every other mark is a unit. The square-word equality forces that valuation to be even. The residue-degree-weighted sum of those valuations is \(v_p(F_i(j))\), hence is even. This holds at ramified primes and when two different prime ideals above \(p\) divide two different marks. Each \(F_i(j)\) is nonzero by irreducibility.

In the usual schedule \(H=(\log N)^{1/3}(\log\log N)^{2/3}\), assume \(\log\max(2,|a_i|,b_i)=O(H)\) and \(\log\max(2,|c_d|)=O(H)\). Then for fixed \(k\) there are \(2^{1+\omega(D_i)}=\exp(o(H))\) signed possibilities for the \(i\)-th squareclass, since \(\omega(n)=O(\log n/\log\log n)\) for \(n\ge3\). Assume also \(\log J=O(H)\), \(d\le(\log N)^{O(1)}\), and polylogarithmic bit lengths in \(N\) for \(m,c_d\) and the coefficients of \(f\).

## Simultaneous bound in the index interval

For a prescribed word with \(1\le k\le3\), let \(s\) be the number of distinct rational roots \(-U_i/T_i\) among its affine norms. The number of indices at which the word is a field square is at most
\[
 \min\{J,\;J^{1/2^s}\exp(o(H))\}.
\]
Keep one mark for each distinct root and fix the signed squarefree parts \(e_1,\ldots,e_s\) of its norms. There are \(\exp(o(H))\) candidate lists.

For odd primes \(p\) outside the finite set dividing one of the \(e_i,T_i\) or the cross-determinants \(U_i T_h-U_h T_i\) of the selected forms, the conditions that each \(e_i^{-1}F_i(j)\) be a square modulo \(p\), allowing zero, restrict \(j\) to at most
\[
 \nu(p)=p/2^s+O_s(\sqrt p)
\]
classes. Expand the product of \(1+\chi(e_i^{-1}F_i(j))\), where \(\chi\) is the quadratic character, and allow an error of at most \(O_s(1)\) at the roots. The one-form sums are zero and the two-form sums have absolute value one because the roots are distinct. For three distinct roots, the cubic character sum is the trace up to sign of the elliptic curve \(y^2=\prod_i e_i^{-1}F_i(x)\), so its absolute value is at most \(2\sqrt p\). [Hasse's inequality](https://www.sciencedirect.com/science/article/pii/S072308692300035X)

The excluded primes divide a nonzero integer \(L\) of logarithm \((\log N)^{O(1)}\). Their sum of \((\log p)/p\) is \(O(\log\log N)\). Split at \(\max(3,\log(3|L|))\) and use the prime harmonic sum below the split and \(\sum_{p\mid L}\log p\le\log |L|\) above it. For the good primes up to \(P\), the reciprocal residue bound consequently gives
\[
 \sum_{p\le P\ {\rm good}}\frac{\log p}{\nu(p)}
 \ \ge\ 2^s\log P-O(\log\log N).
\]
The \(O_s(\sqrt p)\) term costs \(O_s(1)\) in this sum because \(\sum_p(\log p)/p^{3/2}\) converges. One can take integer upper bounds for \(\nu(p)\) throughout.

If \(A\) is the nonempty set of surviving indices and \(n=|A|\), the log of the product of the ordered nonzero differences is at most \(n(n-1)\log J\). At each good prime, Cauchy–Schwarz counts at least \(n^2/\nu(p)-n\) such differences divisible by \(p\). Summing the log contributions and rearranging gives
\[
 n\left(\sum_{p\le P\ {\rm good}}\frac{\log p}{\nu(p)}-\log J\right)
 \ \le\ \sum_{p\le P\ {\rm good}}\log p-\log J .
\]
With \(P=J^{1/2^s}(\log N)^C\) and a sufficiently large constant \(C\), the left parenthesis is at least one. The prime sum on the right is \(O(P)\). Sum over the candidate squareclass lists to obtain the bound. [Gallagher's larger sieve](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/18/0/97714/a-larger-sieve)

## Counts across the menu

If several marks give the same rational index root \(j_0\), their distinct ratios \(a_i/b_i\) are roots of the degree-\(d\) polynomial \(f+j_0(X-m)\) over \(\mathbb Q\). There are at most \(d\) such marks. For any \(Q\)-mark menu, the number of pairs \((j,\text{word})\) is thus at most
\[
\begin{array}{ll}
 k=2: & \exp(o(H))\bigl(Q^2J^{1/4}+QJ^{1/2}\bigr),\\[2mm]
 k=3: & \exp(o(H))\bigl(Q^3J^{1/8}+Q^2J^{1/4}+QJ^{1/2}\bigr).
\end{array}
\]
To count words with \(s\) different roots, choose a representative for each group and at most \(k-s\) further marks from groups of size at most \(d\). This gives \(O_k(Q^s d^{k-s})\) words, and the factor \(d^{k-s}\) is \(\exp(o(H))\). The same argument applies to any prescribed set of rational cycle candidates by counting its words separately for each \(s\), or to a menu selected using this same \(N\). It bounds local table entries. A matched bucket still needs a nonzero sign image.

## Growing-degree examples with exact squares

For a two-mark example use \(P_2(X)=(1-2X)(3-2X)\) and \(g_2(X)=X^u+2X+2\). For three marks use \(P_3(X)=(1-2X)(3-2X)(7-2X)\) and \(g_3(X)=X^u+8X+6\). Set \(u=2^t\), \(t\ge4\), \(f=g_k^2-P_k\), and \(m=2^e\). The expansions are
\[
\begin{aligned}
 f_{[2]}(X)&=X^{2u}+4X^{u+1}+4X^u+16X+1,\\
 f_{[3]}(X)&=X^{2u}+16X^{u+1}+12X^u+8X^3+20X^2+158X+15.
\end{aligned}
\]
For sufficiently large \(e\) these are base-\(m\) digits, and \(N=f(m)\) lies in \([m^{2u},2m^{2u})\). The bit-length rule \(m=\lfloor 2^{(n-1)/(2u)}\rfloor\) recovers \(m\) at degree \(2u\), where \(n\) is the bit length of \(N\). With \(e\) of order \(u^2\log u\), the degree is on the ordinary NFS scale. In both cases \(f(X+1)\equiv X^{2u}\pmod 2\) and \(f(1)\equiv2\pmod4\), so the unshifted member \(f\) is irreducible by shifted Eisenstein.

At this member the marks of \(P_k\) are distinct primitive pairs in growing degree, and \(P_k(\alpha)=g_k(\alpha)^2\). Their homogeneous norm values are squares: at a root \(a/2\) of \(P_k\), the value is \((2^u g_k(a/2))^2\). These values have logarithm \(O(u)\), so they pass any algebraic smoothness bound of size \(\exp(\Theta(H))\) on this schedule. For the pair, take \(t\equiv4\bmod 10\) and \(e\equiv60\bmod 132\), which give \(13\mid N\) and \(23\mid N\). For the triple, take \(t\) even and \(e\equiv1\bmod12\), which give \(5\mid N\) and \(7\mid N\). In both cases \(N\) is odd. The modular checks can use \(u=16\) for each listed prime, since the specified exponents preserve \(m\) and \(m^u\) modulo that prime. The root \(g_k(m)\) is nonzero at those primes.

These examples supply squares in a valid digit fan with growing degree and algebraically smooth norms. The rational smoothness of the marks and the presence of a second root with a different sign pattern remain unproved. The exhibited word gives the globally evaluated square \(P_k(m)\equiv g_k(m)^2\bmod N\).

## A word whose length grows with the input

Keep the same coefficient, degree and index-height bounds. Suppose one prescribed word has $k=o(\log H)$ distinct marks, and that the number $s$ of its distinct affine index roots tends to infinity. The total number of fan indices at which the word is a field square is $\exp(o(H))$, including when the fan itself has length $\exp(\Theta(H))$.

To prove this, fix any integer $r$ before taking the limit and select $r$ marks with different index roots once $s\ge r$. Each selected mark's determinant product still includes all the other marks of the full word. Its log size is $O(kH)$, so the number of signed squareclasses at each of these $r$ positions is $\exp(O(1+kH/\log(2+kH)))=\exp(o(H))$. This selection avoids multiplying a class-count penalty for every position of the growing word. At good odd primes, expansion of the $r$ quadratic characters gives at most $p/2^r+O_r(\sqrt p)$ allowed residues. For each nonempty subset the distinct linear factors make the character polynomial squarefree, giving the Weil bound $(j-1)\sqrt p$ for $j$ factors. The larger-sieve proof above now bounds the number of indices by $J^{1/2^r}\exp(o_r(H))$. Since $\log J/H$ is bounded and fixed $r$ can be arbitrarily large, the stated bound follows. It is per prescribed word. Many different words can still contribute at the same index. [Weil's character-sum bound](https://doi.org/10.1073/pnas.34.5.204)
