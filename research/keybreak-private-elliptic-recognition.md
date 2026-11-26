# Elliptic-curve recognition for the private prime bands

For one fixed input, KeyBreak's private-coordinate count only needs a positive fraction of the primes in each prescribed dyadic band. This permits an elliptic-curve smoothness test for the private coordinates under RH. The upper work coefficient, in units of $\sqrt{\log y\log\log y}$ at cutoff $y$, can be taken to be $1.4143$ instead of $2.0001$. Keep the original genus-two method on public algebraic tests and on the preliminary first-split pass. The argument below is a manuscript proof. Its smooth-number estimate is derived here; the elliptic-curve splitting theorem is an existing result. [Lenstra and Pomerance, Theorem 7.1](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf#page=19) · [KeyBreak H.3–H.5](https://crypto.sjtu.edu.cn/factoring.pdf#page=129)

## Smooth numbers near almost all integer centers

Fix $c>0$, put $U=\log X$, $T_X=\sqrt{U\log U}$, and $B=cT_X$. Assume RH for the Riemann zeta function. For each sufficiently large $X$, all but $O_{A,c}(X/(\log X)^A)$ **integers** $p\in[X,2X]$ satisfy, for every fixed $A>0$,
$$
 \#\{n:\ |n-p|<\sqrt p,\ P^+(n)\le e^B\}
 \ \ge\ \sqrt p\,\exp\bigl(-(1/(2c)+o(1))T_X\bigr).
$$
The asymptotic loss is uniform on the indicated dyad. We count products of primes in a logarithmic interval wide enough to retain the leading smoothness density.

**Twisted prime sum.** For $2\le v\le e^B$ and $|t|\le X^3$,
$$
 \sum_{q\le v,\ q\ {\rm prime}}(\log q)q^{-it}
       =\frac{v^{1-it}}{1-it}+O_c(v^{2/3}U^C)
$$
for an absolute fixed $C$ and large $X$. Apply truncated Perron to $-\zeta'/\zeta(s+it)$ at $v'=\lfloor v\rfloor+1/2$ and height $2X^3$, starting at $1+1/\log v'$. The coefficients have modulus at most $\log n$. At the half-integer the usual Perron remainder is $O(v'\log^2(2v')/X^3)$ up to an extra logarithm, by summing the reciprocal distance from $v'$. Shift to $\Re s=2/3$, picking up only the residue at $1-it$. The log derivative is bounded by a power of $U$ on the new vertical line and the horizontal segments. Indeed the zeros on $\Re s=1/2$ are separated horizontally from this strip by $1/6$, the local zero count is logarithmic, and the pole of zeta stays away from the integration edges. The vertical integral is $O(v'^{2/3}U^C)$ including the $1/s$ integration. The horizontal integrals are $O(v'U^C/X^3)$. The main term changes by $O(1)$ on replacing $v'$ by $v$, since its derivative has modulus one. Removing prime powers costs $O(v^{1/2}\log^2(2v))$. [RH log-derivative bounds](https://doi.org/10.1007/s00209-021-02820-9)

**Choice of prime products.** Set $r=(U+1)/B$ and $k=\lceil r(1+2/\log r)\rceil$. Put $m=(U+(\log 2)/2)/k$, $\Delta=m/\log k$, $a=m-\Delta$, $b=m+\Delta$. Then $b\le B$ eventually, $ka=(1-o(1))U$, and $k\sim U/B$. On log-prime positions in $[a,b]$ place mass $(\log q)/(2\Delta q)$ at $\log q$. Call this positive measure $\mu$ and let $\nu$ be Lebesgue probability measure on $[a,b]$. By the twisted estimate and partial summation with the weight $1/v$,
$$
 \sup_{|t|\le X^3}|\widehat\mu(t)-\widehat\nu(t)|\le \epsilon,
 \qquad \epsilon=e^{-a/3}U^{O(1)} .
$$
Here the transform uses $e^{-itu}$, so $|\widehat\nu(t)|\le\min(1,1/(\Delta |t|))$. In the integrated error the factor is $\int_{e^a}^{e^b}v^{-4/3}dv\ll e^{-a/3}$, independent of $t$. In particular $\mu(\mathbb R)\le1+\epsilon$.

**Mean-square comparison.** Let $h=1/(10\sqrt X)$, and let $K_h$ be the triangular density of mass one on $[-h,h]$. The squared $L^2$ distance of the smoothed $k$-fold convolutions $\mu^{*k}*K_h$ and $\nu^{*k}*K_h$ is $O_{A,c}(U^{-A})$ for every fixed $A$. By Plancherel, at $|t|\le1$ the transform difference before smoothing is at most $k\epsilon(1+\epsilon)^{k-1}$. For $1<|t|\le X^3$ its square is at most
$$
 O(4^k)\big((\Delta |t|)^{-2k}+\epsilon^{2k}\big).
$$
The integral of the first term is $O(4^k\Delta^{-2k}/(2k-1))$. For the second use $\int |\widehat K_h|^2=O(h^{-1})$; its total is at most $\exp(-2ka/3+U/2+o(U))=X^{-1/6+o(1)}$. The $o(U)$ includes $O(k\log U)$. For $|t|>X^3$ the mass bound gives $|\widehat\mu(t)|^k=O(1)$, and $|\widehat K_h(t)|\ll (h|t|)^{-2}$ makes this tail $O(h^{-4}X^{-9})$. All three ranges are smaller than any fixed negative power of $U$.

**Central density and exceptional integers.** The continuous $k$-fold uniform convolution is symmetric and unimodal with support of length $2k\Delta$, so its density at $km$ is at least $1/(2k\Delta)$. At displacement $|s|\le2$ its density is at least $(1-|s|/(k\Delta))^{k-1}$ times the central density: contract the central hyperplane slice of the cube $[-\Delta,\Delta]^k$ about the origin by linear scale $1-|s|/(k\Delta)$, and translate by $s/k$ in each coordinate. The resulting slice lies in the cube and has the required sum. Thus throughout the log dyad and a fixed small enlargement the continuous reference smoothed by $K_h$ has density $\gg1/(k\Delta)$. By the mean-square estimate the set on this enlarged interval where the discrete smoothed density is less than half that bound has measure $O_{A,c}(U^{-A})$ for arbitrary $A$.

Place disjoint log neighborhoods of radius $1/(10X)$ around the integer centers $\log p$ in the dyad. Except for $O_{A,c}(XU^{-A})$ centers, the neighborhood contains a point where the discrete density has the stated lower bound. Every contributing product $n$ at this point obeys $|n-p|<\sqrt p$ for large $X$ by the support of the tent. Each distinct $n$ has at most $k!$ ordered prime representations. Its contribution to the density is at most $h^{-1}k!(b/(2\Delta))^k/n$. Hence the number of distinct contributing smooth integers is at least
$$
 C_0\frac{hX}{k\Delta\,k!\,(b/(2\Delta))^k}.
$$
Here $C_0>0$ is absolute. Taking logarithms, $k\log k=(1/(2c)+o(1))T_X$, while $k\log(b/(2\Delta))=O(k\log\log k)=o(T_X)$. This proves the claim, including its strength for integer centers that happen to be prime. No unproved density assumption about the distribution of the primes among exceptional real centers enters.

## Transfer to the private-coordinate procedure

Use $c=1/\sqrt2$ and $T_y=\sqrt{\log y\log\log y}$. Call a prime eligible for the counting argument if its Hasse interval contains at least $\sqrt p\exp[-(1/(2c)+o(1))T_p]$ integers smooth up to $\exp(cT_p)$, with the uniform error from the proof above. In a complete dyadic band $(P,2P]$, its complement has $O_A(P/(\log P)^A)$ members since $T_P\le T_p$ and $T_p/T_P\to1$. Take $A>2$. The earlier single-field event supplies at least three quarters good top parents in each prescribed band. Intersecting with the elliptic-eligible primes leaves at least half of every large band's primes. The H.20 product count only loses a constant factor per selected prime, or $\exp(O(k_0))=\exp(o(H))$ across a coordinate. These are counting sets; the program need not decide their membership.

Use the elliptic-curve method in Lenstra–Pomerance Theorem 7.1 with private stage cutoff $y$, per-curve work parameter $w\ge\exp(cT_y)$ and number of curves at least $\exp((1/(2c)+\eta)T_y)$ times a polynomial confidence allowance, with a small fixed $\eta>0$. Test primes, unit factors and powers exactly and remove small factors as usual. On a composite with at least two distinct primes whose **least prime** $p\le y$ belongs to the counted bands and is eligible, the theorem gives failure probability at most $c_6^{\#\text{curves}\,\psi_0(p,w)/(\sqrt p\log y)}$, $0<c_6<1$, irrespective of the larger factors. Recurse after proper splits, verify each claimed prime and use the same stage gates on certified band products. For a counted good shape, if any factor at most $y$ remains, the least remaining prime is at most $y$ and is itself eligible. This property holds on every unresolved divisor of a counted shape. Recursing therefore recovers every required small factor with high probability without a test for eligibility. A composite with all primes above $y$ may exhaust its budget and contribute no acceptable factors. Other private shapes can only advance by exhibiting true certified divisors, so the previous Rankin upper bounds for stage survivors still hold, even on tapes where the recognizer misses small factors. All searches are local to the public square or other public data before extraction. Neither retaining a shape nor timing the capped procedure depends on the unrevealed private root.

The first-stage running time is $O(\#\text{curves}\,w\log y(\log a_0)^2)$ in bit operations up to polynomial implementation factors, where $a_0$ is the current positive integer cofactor. Using the source's dyadic $k_y=\lceil\sqrt{b(y)b(b(y))}\rceil$, take $w=2^{\lceil .70711k_y\rceil}$ and a curve cap $2^{\lceil .70717k_y\rceil}L_c$, for example. Both exponents strictly exceed the needed $1/\sqrt2$ coefficients. Their sum is below $1.4143$, and $k_y\log 2=(1+o(1))T_y$. The polynomial factor $L_c$ covers all tree-node and virtual-slot confidence costs. The loss bound is needed only on the counted shapes; all schedules charge the finite work on every input and on unsuccessful attempts. The admissible Hasse intervals need no per-input table. For an implementation of the random draws with finite bits, use polynomially capped rejection for uniform scalar ranges and charge timeouts via the original confidence budget. Small inputs are covered by the existing fallback. This argument improves the private screening cost alone. Algebraic smoothness recognition still uses the all-primes genus-two guarantee. [Lenstra and Pomerance, §7](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf#page=19)
