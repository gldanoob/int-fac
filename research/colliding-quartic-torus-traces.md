# Norm-one traces in the class-five quartic

Traces of powers of \(2+\sqrt3\) give a class-five quartic split exactly when three adjacent signed norm-one tests cover all prime factors with mixed signs. The successful exponent then gives a divisor by an ordinary coefficient gcd, without constructing the quartic. For a semiprime the existence of such an exponent has an exact criterion in terms of the two local orders. [Class-five construction](colliding-quartic-single-input-search.md#a-fixed-rational-square-class-supplies-a-simple-evaluation-for-every-input) · [Norm-one order certificates](cogentic-cm-torus.md)

## The two independent local choices

Assume \(N\) is coprime to 30. A class-five parameter satisfies \((u^2-4)(u^2-16)=0\bmod N\). Its two independent square roots of one are
\[
              S=\frac{u(28-u^2)}{48},\qquad J=\frac{u^2-10}{6}.
\]
The four linear roots \(2,4,-2,-4\) are disjoint modulo every prime dividing \(N\). Checking them gives \(u=S(3+J)\), and this formula conversely realizes every pair \((S,J)\) of modular square roots of one. The quartic sign is \(S\); the magnitude choice is \(J\). In particular, any mixed square root of one becomes a productive quartic parameter by taking \(u=2S\). The quartic sign extraction recovers the same square root of one from a productive parameter.

## The three adjacent exponents

Work in \(R_N=(\mathbb Z/N\mathbb Z)[\xi]/(\xi^2-3)\). Put \(\tau=2+\xi\), \(h=\tau^k\), and \(u_k=h+h^{-1}\). Norm one makes \(u_k\) a scalar. For each \(\epsilon\in\{1,-1\}\), the exact identity is
\[
 (u_k-2\epsilon)(u_k-4\epsilon)
 =h^{-2}(h-\epsilon)^2(\tau^{k-1}-\epsilon)(\tau^{k+1}-\epsilon).
\]
Indeed \(h(u_k-2\epsilon)=(h-\epsilon)^2\) and \(h(u_k-4\epsilon)=(h-\epsilon\tau)(h-\epsilon\tau^{-1})\). This holds over prime powers as well.

At a prime \(p>5\), the norm-one group in the residue algebra is cyclic of order \(p-(3/p)\). If 3 is square, projection to either component identifies this group with \(\mathbb F_p^\times\). If 3 is nonsquare, it is the kernel of the norm from \(\mathbb F_{p^2}^\times\). In either case the sign-\(\epsilon\) branch holds exactly when \(\tau^j=\epsilon\) for some \(j\in\{k-1,k,k+1\}\). This follows from the identity in a field, with the other component in the split case determined by inversion. The two signs are disjoint. For any mixed class-five parameter generated this way, pick a prime on its positive branch. At least one of the three shifted powers is one at that prime, while none is one at a prime on the negative branch. Thus a proper divisor is returned by one of the three gcds of \(N\) with both coefficients of \(\tau^j-1\). The power \(\tau^k\) and the adjacent powers use binary exponentiation and two multiplications. For an exponent menu, running these ordinary order tests on the shifted menu captures every productive quartic comparison and also permits partial local hits. This is a Lucas trace for the fixed norm-one base in the usual \(p\pm1\) setting. [Williams's Lucas-sequence method](https://doi.org/10.1090/S0025-5718-1982-0658227-7)

There is a multiplicity distinction at prime powers. Write \(a_j\) for the minimum of the two \(p\)-adic coefficient valuations of \(\tau^j-\epsilon\). After removing \(p^{a_j}\), the remaining element is a unit in the local quadratic algebra. For \(a_j=0\) this follows from the split-field description above, since norm one forces both components of \(\tau^j-\epsilon\) to vanish together. When \(0<a_j<\infty\), the norm-one equation forces the remaining element to have trace zero modulo \(p\). A nonzero trace-zero element is a nonzero multiple of \(\xi\), hence is a unit. The valuation of the scalar product on the left is therefore \(2a_k+a_{k-1}+a_{k+1}\), with infinite valuations for zero factors. The central condition can hold modulo \(p^e\) when the central coefficient vanishes only to order \(\lceil e/2\rceil\). A coefficient gcd may then extract only part of a prime power, which is still a proper divisor in the mixed case.

## Which semiprimes admit a mixed trace

For distinct primes \(p,q>5\), write \(m_p,m_q\) for the local orders of \(\tau\), \(s_p,s_q\) for their two-adic valuations, and \(g=\gcd(m_p,m_q)\). A mixed class-five trace exists at some integer exponent if and only if one of the following holds.

- \(s_p\ne s_q\).
- \(s_p=s_q>0\) and \(g\in\{2,4\}\).

For a positive sign at \(p\) and a negative sign at \(q\), the two exponent requirements are
\[
       k\equiv i\pmod {m_p},\qquad
       k\equiv m_q/2+j\pmod {m_q},\qquad
       i,j\in\{-1,0,1\}.
\]
The negative branch needs \(s_q>0\). The two classes are compatible exactly when \(m_q/2\equiv i-j\pmod g\). If \(s_q>s_p\), the half-order is zero modulo \(g\), so even the unshifted choice works. If \(0<s_q\le s_p\), the half-order is \(g/2\) modulo \(g\). Its least absolute representative lies in \([-2,2]\) exactly for \(g=2,4\). Applying the same argument in the other orientation proves the criterion.

An unshifted comparison of \(\tau^k\) with \(\pm1\) can mix signs exactly in the unequal-height case. The shifts add the equal-height case with \(g=2,4\), which necessarily has different full orders. Indeed \(\tau\) cannot have order one or two since its \(\xi\)-coefficient is one at every good prime, and order four would force trace zero instead of four. Equal full orders therefore never supply a mixed quartic trace. When the full orders differ, an ordinary unshifted identity test at one of the two exact orders already gives a proper gcd, even on examples that admit no mixed quartic trace.

If a public factored multiplier annihilates the base at one prime, test it directly and then remove prime factors while the annihilation remains global. A proper gcd appears if the two local orders differ. In particular, the usual exponent built from primes through a bound suffices if at least one local element order is smooth through that bound and the two orders differ. This requires smoothness only for the chosen base. The quartic supplies no exponent from \(N\) on inputs outside the usual order-finding promises. [Bounded missing multipliers and trace search](p-plus-one-multiples.md#a-bounded-missing-multiplier)

For a consecutive cap \(1\le k\le H\), a mixed trace would imply a positive local identity exponent at most \(H+1\). A zero shifted exponent is the identity at every prime and cannot occur on a mixed trace. The existing product-tree trace search finds the least positive local identity exponent up to that cap in \(\widetilde O(\sqrt{H+1})\) modular work. If the least hit occurs at all prime factors, their orders all equal that least exponent and every trace-sign profile agrees. Otherwise its scalar trace gcd already gives a proper factor. This bounded search captures every productive quartic trace in the interval.

## Exact fixtures

| \(N\) | Local primes and orders | Exponent | \(u_k\bmod N\) | Positive-sign gcd |
|---:|---|---:|---:|---:|
| 187 | \((11,10),(17,18)\) | 9 | 15 | 11 |
| 2353 | \((13,12),(181,20)\) | 11 | 901 | 13 |
| 401227 | \((607,32),(661,60)\) | 240 | 341739 | 661 |

The first two fixtures give the equal-height cases \(g=2,4\). For \(N=401227\), the two full norm-one group orders are \(608=32\cdot19\) and \(660=60\cdot11\). The chosen base has 5-smooth order on both sides. The ordinary gcd at exponent 240 gives 661.

For \(11\cdot241\), the orders are 10 and 30. No mixed quartic trace exists at any exponent, and the ordinary order test at exponent ten gives 11. At \(37\cdot73\), both orders equal 36 and the trace-sign profiles agree at all exponents. Finally, at \(11^2\cdot17=2057\), the trace at exponent 35 is 361. The negative branch gcd is \(121\), whereas the central coefficient gcd with \(\tau^{35}+1\) is \(11\), showing the prime-power multiplicity in the middle factor.
