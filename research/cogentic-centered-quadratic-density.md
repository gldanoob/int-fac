# Private prime ideals on almost all centered quadratic grids

Fix a balance ratio \(R>1\). Among products \(N=pq\) in \([X,2X]\) of distinct primes with \(1\le q/p\le R\), a proportion tending to one has the following property. Write \(L=\log X\), \(W=L^{1/3}(\log L)^{2/3}\), \(V=L^{2/3}(\log L)^{1/3}\), and \(M=\lfloor\sqrt N\rfloor\). For fixed \(c,C>0\), take any integer offset and slope \(|j|,|s|\le e^{CW}\) and set
\[
 m=M+j,\qquad P=X_0^2+sX_0+N-m^2-sm .
\]
Thus \(P(m)=N\) exactly. The polynomial is irreducible and has a simple root modulo \(N\) in the sense \(\gcd(P'(m),N)=1\). Every primitive direction \(|a|,b\le H=\lfloor e^{cW}\rfloor\), \(b>0\), gives a unit modulo \(N\). Its field element \(a-b\alpha\) has an odd valuation at a prime ideal private to that direction. In particular none of these fields has a productive ordinary mark relation on the grid. This holds simultaneously over the stated parameter range, including choices made after seeing \(N\).

For fixed constants the exceptional proportion is \(\exp(-\Omega_c(V))\). One density-one family also works for **every** fixed choice of one-third constants, by taking the larger simultaneous envelope described below. This obstruction applies to the [centered quadratic decision](cogentic-quadratic-square-kernel.md#complete-primitive-grids-over-several-quadratic-fields). It leaves different fields, independent unit corrections and algorithms outside the ordinary mark search open.

## A count of possible norms

Put \(y=2H^2\). Let \(E(T,y)\) count positive integers at most \(T\) whose valuations at all rational primes above \(y\) are even. For \(0<\lambda\le1/4\), summing the Euler product at \(1-\lambda\) gives
\[
 E(T,y)\le T^{1-\lambda}\zeta(2-2\lambda)
              \prod_{p\le y}(1-p^{-1+\lambda})^{-1}.
\]
Indeed each eligible integer contributes at least one after multiplication by \(T^{1-\lambda}\), and the unbounded geometric series at each prime above \(y\) contains only even powers. The zeta factor is bounded absolutely. The logarithm of the displayed product is \(O(y^\lambda\log\log(3y))\). This follows from \(-\log(1-t)\ll t\) for \(t\le2^{-3/4}\), and \(\sum_{p\le y}1/p\le e\log\zeta(1+1/\log y)\le e\log(1+\log y)\).

Freeze \(M,j,s,a,b\) and vary \(r=N-M^2\) over a square block \(0\le r\le 2M\). The signed norm and the polynomial discriminant are
\[
 Q(r)=a^2+sab+b^2(r-2Mj-j^2-sm),\qquad
 \Delta(r)=(2m+s)^2-4(M^2+r).
\]
Each is an injective affine function of \(r\). Uniformly their absolute values are at most \(T=M\exp(O_{c,C}(W))\). Either form takes the value zero at most once and has absolute value counted by \(E(T,y)\) at most \(2E(T,y)\) times. Take \(\lambda=(\log\log M)/(4\log y)\), which is below \(1/4\) for large \(M\). Then \(y^\lambda=(\log M)^{1/4}\) and
\[
 \lambda\log M=(1/(16c)+o(1))V.
\]
Both \(\log(T/M)\) and the Euler-product logarithm are \(o(V)\). The exceptional count for one form is therefore at most \(M\exp(-(1/(16c)+o(1))V)\). There are only \(\exp(O_{c,C}(W))\) tuples per block, and \(O(\sqrt X)\) blocks. Thus, except for \(X\exp(-\Omega_c(V))\) integers in the interval, every listed norm and every listed discriminant has a prime greater than \(y\) with odd valuation. In particular each \(\Delta\) is a nonsquare and its rational square class differs from that of \(-1\).

The same proof allows \(\log H\) and \(\log(2+\max(|j|,|s|))\) to be bounded by \(L^{5/12}\). Use this common upper envelope for the grid, shifts and slopes, and take its corresponding \(y\). The loss in the size and number of forms is now \(O(L^{5/12})\), while \(\lambda\log M\gg L^{7/12}\log L\). This supplies one density-one family for all fixed \(c,C\).

## From norm divisors to failure of the grid search

An odd valuation of the norm at a prime \(\ell>2H^2\) forces an odd valuation at some prime ideal over \(\ell\). A prime ideal dividing two different primitive marks would divide their nonzero integer determinant, of magnitude at most \(2H^2\). Thus even all-ideal parity in a field forces every primitive exponent even. The extra shared sign cannot alone be square in a listed quadratic field because \(\Delta\) has an odd valuation above \(y\). The same argument rules out mixing primitive marks across these fields at a common base: each individual field already forces all its mark exponents even. Rational contents of size at most \(H\) do not affect a private valuation. Any rational square class they generate which becomes a square in one field must already be a rational square, since the only other possibility is the class of \(\Delta\). These statements use the maximal-order valuation of the actual element and also hold at singular residue roots. [Mixed square normalization](cogentic-monic-mixed-complete.md)

The balanced semiprime population is \(\gg_R X/(\log X)^2\) by the prime number theorem: choose both primes in a fixed narrow subinterval of \((\sqrt X,\sqrt{2X})\) with endpoint ratio below \(R\). All the factors of the balanced semiprimes in the full population are comparable to \(\sqrt X\). At fixed \(M,j,s,a,b\), either possible gcd input \(2m+s\) or \(a-bm\) is nonzero and of size at most \(M\exp(O(W))\) in the fixed-constant regime. Each has at most a bounded number of prime divisors comparable to \(\sqrt X\). Each such prime divides \(M^2+r\) for at most \(O_R(1)\) values of \(r\) per block. Summing costs \(X^{1/2+o(1)}\) inputs even for the larger envelope. Dividing both exceptional counts by the semiprime lower bound proves the assertion.

The [finite replay](../experiments/cogentic-centered-quadratic-density.py) checks a 255-bit balanced semiprime, 35 fields and 17,885 primitive field-mark combinations at height 20. It verifies the two input primes, derivative and mark gcds, and a nonsquare residual beyond the determinant cutoff for every norm and discriminant.
