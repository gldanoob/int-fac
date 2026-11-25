# Odd smooth numbers in every central Hasse interval

Fix \(\theta>1/(4\sqrt e)=0.1516326649\ldots\). For every sufficiently large prime \(p\) there are \(\gg_\theta\sqrt p\) distinct integers \(n\) satisfying

\[
 |n-(p+1)|\le\sqrt p,\qquad n=4s,\qquad
 s\text{ odd},\qquad P^+(s)\le p^\theta .
\]

Here \(P^+(s)\) is the largest prime factor of \(s\). One may take \(\theta=31/200=0.155\). Harman's published Theorem 1 gives the lower bound for smooth integers without the parity restriction. The local modification of his proof below imposes oddness. No hypothesis on zeros of zeta or Dirichlet \(L\)-functions is needed. [Harman, *Integers without large prime factors in short intervals and arithmetic progressions*, Acta Arith. 91 (1999), 279–289](https://matwbn.icm.edu.pl/ksiazki/aa/aa91/aa9137.pdf)

## The square-root interval and parity

Harman's Theorem 1 states that for every \(\epsilon>0\), all sufficiently large \(x\), and \(u\ge x^{1/(4\sqrt e)+\epsilon}\),

\[
 \Psi(x+\sqrt x,u)-\Psi(x,u)\gg_\epsilon\sqrt x.
\]

Use \(x=(p+1-\sqrt p)/4\). Since \(\sqrt x\le\sqrt p/2\), every \(s\in(x,x+\sqrt x]\) gives \(4s\) in the specified central interval. It suffices to establish the same short-interval lower bound with \(s\) odd. Choose the proof parameters with enough slack that the final smoothness exponent stays below \(\theta\). [Theorem 1, p. 279](https://matwbn.icm.edu.pl/ksiazki/aa/aa91/aa9137.pdf#page=1)

Follow the proof of Lemma 1 and its application on p. 286. It counts products \(rmn\), where \(r=ku\) has all its prime factors above \(x^{1/10}\), and \(a_n\) in (2.4) restricts every prime factor of \(n\) to \([x^{\eta^2},x^\beta]\). Thus \(r,n\) are odd for large \(x\). In both \(E(M,N)\) and \(F(M,N)\) in (2.5) retain only odd \(m\). The same representation bound \(T\) applies to this subset. [Lemma 1, pp. 281–284](https://matwbn.icm.edu.pl/ksiazki/aa/aa91/aa9137.pdf#page=3) · [Choice of the four factors, p. 286](https://matwbn.icm.edu.pl/ksiazki/aa/aa91/aa9137.pdf#page=8)

**Transfer of the initial count.** In \(E\) the unweighted factor \(m\) is the free variable \(l\) of the short-interval estimate on pp. 284–286. Its odd restriction is the difference of the unrestricted sum and the sum with \(m=2m'\). The latter uses the intervals \(I/2,B/2\), the free dyadic range \([M/2,M)\), and the same transfer ratio \(\lambda=y/x\). To verify the short-interval estimate after scaling, formula (3.2) now has phase \((Y/2)h/d\) and truncation \(H\ll 2d x^\eta/y\) on a dyadic block of products of size \(d\). Lemma 3 applies with size parameter \(x/2\). In its proof on p. 285 the grouped variable has size \(\asymp yx^{-5\eta}\) and \(H\ll N x^{-4\eta}\), so \(H\le N\) for both choices. The other input inequality \(N^2 M\le x^{1-\eta}\) has slack when the paper's parameters satisfy \(\epsilon>3\eta\). Every monomial on the right of (3.3) changes by at most a constant. The resulting \(O(MN x^{-\eta})\) estimate retains its power saving. The dyadic free-variable endpoints can be retained in both transfers as in (2.1). Equivalently the floor-function discrepancy in Lemma 2 is evaluated first at \(Y/d\) and then at \(Y/(2d)\). This argument also permits any fixed replacement \(y=c\sqrt x\), \(0<c\le1\), since fixed factors only change the constants in the same bounds. [Lemmas 2 and 3, formulas (3.1)–(3.6), pp. 284–286](https://matwbn.icm.edu.pl/ksiazki/aa/aa91/aa9137.pdf#page=6)

In the long-interval counterpart, for fixed \(r,n\) the allowed \(m\)'s form an interval. The odd count is half the total up to an absolute endpoint error. There are \(O(x^{1-\alpha+o(1)})\) relevant pairs on a block since \(rn\le 2x/M\) and \(M\ge x^\alpha\). This error remains lower order after multiplication by \(\lambda\) and summation over dyadic blocks. Thus the leading lower bound for \(\sum E\) on p. 283 acquires a factor \(1/2\).

**Transfer of the rejected count.** For \(F\), replace \(c_m\) by \(c_m[2\nmid m]\), where \(c_m\) detects a prime divisor \(p'\ge x^\beta\) of \(m\). In the upper sieve on \(n\), Harman applies (2.1) with coefficient \(a_{dm}=c_m\) for each sieve divisor \(d\), leaving \(n/d\) free. The altered coefficient obeys the identical bound, so the transfer itself needs no new estimate. In its long-interval upper bound on p. 283, write \(m=p'v\). Since \(p'\) is odd, the inner harmonic sum restricts \(v\) to odd integers. For any interval of positive integers,

\[
 \sum_{a\le v\le b,\ 2\nmid v}\frac1v
 =\frac12\sum_{a\le v\le b}\frac1v+O(1).
\]

This follows from the alternating harmonic sum, uniformly even when \(a<1\). The extra contribution in the double sum is \(O(\sum_{x^\beta\le p'\le x^{\alpha+\epsilon}}1/p')=O_\epsilon(1)\). The leading inner term is of size \(\epsilon\log x\) in the upper bound, before multiplication by \(1/(\eta^2\log x)\) from (2.6). Thus the leading upper bound for \(\sum F\) also acquires a factor \(1/2\), with additional relative scale \(O_\epsilon(1/\log x)\). The strict positive margin \(1-2\log((\alpha+\epsilon)/\beta)\) at the end of Lemma 1 survives. [The upper sieve and its harmonic sum, pp. 282–283](https://matwbn.icm.edu.pl/ksiazki/aa/aa91/aa9137.pdf#page=4)

The result gives a positive constant times \(\sqrt x\) weighted products. Harman has \(b_r<32\), and each represented integer at most \(2x\) has only boundedly many divisors made from primes above \(x^{1/10}\), by counting its prime factors with multiplicity. Hence it gives \(\gg\sqrt x\) distinct odd smooth integers. Removing trace zero in the Hasse application discards at most one order.

## Exact finite checks

The replay checks the floor-function transfer with odd free variables, the uniform alternating harmonic error and the central-interval endpoints using integer arithmetic. These finite identities verify the parity manipulation and its scaling. Harman's asymptotic estimate supplies the density. [Integer and rational controls](../experiments/pointwise-odd-smooth-hasse.py)
