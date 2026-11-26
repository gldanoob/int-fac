# Almost all balanced semiprimes evade bounded unit-chart collisions

On the unit chart, trying every small rational parameter and every pair of small integer powers yields a local split on a vanishing proportion of balanced semiprimes. This holds for the signed gcd search, which only needs coincidence modulo one prime divisor. A second bound applies to equal-power words on the repeated-squaring library, allowing arbitrarily many modular squarings. [Unit-chart construction](cogentic-unit-corrected-family.md) · [Finite collision diagnostic](cogentic-unit-collision-diagnostic.md)

Take distinct primes \(p,q\in[Y,2Y]\) and \(N=pq\). Proportions refer to all unordered pairs in this dyadic interval as \(Y\to\infty\). For rational \(t\) in lowest terms, write \(H(t)\) for the maximum absolute numerator or denominator. The eligible chart gives root ratio
\[
 \rho=-tA^i/B^j,\qquad A=\frac{t(t-1)}{t+1},\qquad B=\frac{t-1}{t(t+1)}.
\]
The search compares the two corrected roots at both signs. It may also return proper gcds from the eligibility checks.

## Every small rational parameter and bounded pair of powers

For \(T\ge2\), \(E\ge0\), the proportion of inputs on which any \(H(t)\le T\), \(|i|,|j|\le E\) gives a proper divisor is
\[
       O\!\left(\frac{T^2(E+1)^3\log(2T)}{Y}\right).
\]
In particular, if \(T,E=Y^{o(1)}\), this proportion is at most \(Y^{-1+o(1)}\). This covers one-third-size numerical power bounds even when the choice of parameters and powers within the box depends on \(N\).

Write \(t=c/d\). The log heights of \(A=c(c-d)/(d(c+d))\) and \(B=d(c-d)/(c(c+d))\) are at most \(\log(2T^2)\). Thus \(\log H(\rho)=O((E+1)\log(2T))\). If \(\rho=\pm1\) over the rationals, the two unit roots agree up to the same global sign, so neither signed difference yields a proper divisor. Otherwise each numerator of \(\rho\pm1\) is nonzero and bounded by \(2H(\rho)\). A local collision forces \(p\) or \(q\) to divide one of these numerators. Across the \(O(T^2(E+1)^2)\) choices, the sum of the logarithms of all possible prime divisors is at most \(O(T^2(E+1)^3\log(2T))\). The nonzero eligibility numerators and denominators \(c,d,c-d,c+d,c^2+d^2\) add at most \(O(T^2\log(2T))\). Identically zero tests cannot yield a proper gcd. A prime in the interval costs at least \(\log Y\) of this total, and the interval contains \(\asymp Y/\log Y\) primes. Counting pairs with at least one exceptional prime proves the bound.

## Every repeated square, on equal-power words

Allow \(t=a^{2^j}\bmod N\) for every \(2\le a\le T\) and any \(j\ge0\). For equal powers \(i\) the ratio is \(-t^{2i+1}\). If \(T,E=Y^{o(1)}\), at most a proportion \(Y^{-1/2+o(1)}\) of the balanced inputs give a proper divisor by any signed local equality with \(|i|\le E\), or by a parameter gcd.

Fix \(h\ge1\). At a prime \(r\nmid a\) with \(v_2(r-1)\le h\), equality up to sign implies that the odd part of the order of \(a\bmod r\) divides \(k=|2i+1|\). Thus \(r\mid a^{2^h k}-1\), uniformly in the number of squarings. A prime dividing \(t\pm1\) or \(t^2+1\) also meets this condition with \(k=1\). Base gcds are impossible once \(T<Y\). For all \(a,k\) these positive integers have total log size \(O(2^h T(E+1)^2\log(2T))\). The primes excluded by the height assumption lie in \(1\bmod 2^{h+1}\), which has \(O(Y/2^h+1)\) integers in the interval. Taking \(h=\lfloor(\log_2 Y)/2\rfloor\) and counting both kinds of prime gives the stated fraction. This elementary estimate needs no hypothesis on zeros of zeta functions.

The polynomial-size library's guaranteed equal-power witness has small **bit length**. Its exponent may have large numerical value. These counts explain how that existence result coexists with failure of the bounded search on almost all balanced semiprimes. Unequal powers after input-dependent modular squarings, or pooled words drawn from many charts, have a larger range of rational evaluations.
