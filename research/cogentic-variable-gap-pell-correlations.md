# Pell lifts for variable-gap unit comparisons

A Pell identity allows two consecutive-pair units with distinct variable gaps to have the same rational value. It also gives a separate family with congruent values and opposite local root signs, with distinct squared gaps at every prime of the input. The latter family has an input-only split in polynomial bit time, without computing elliptic or multiplicative group orders. Its inputs are recognizable from a quartic formula. [Fixed-gap genus bound](cogentic-cross-gap-unit-correlations.md) · [Consecutive-pair power-order units](cogentic-quintic-unit-target-two.md)

## An integral lift of the unit value

Let \(d=(u-1)D\) and suppose \(V^2-4uD^2=1\). For
\[
 x=\frac{1+2uD-V}{2},\qquad A(X)=X(X-1),\qquad
 C_d(X)=(X-d)(X-d-1),
\]
one has \(A(x)=uC_d(x)\). Indeed the discriminant of \(A(X)-uC_d(X)\) is \((1-u)^2+4ud^2=(u-1)^2V^2\), giving the displayed root. If \(V\) is an odd integer and \(u,D\) are integral then so is \(x\). When \(u=\delta s^2\), the same lift gives \(P=(x,sC_d(x))\) on \(\delta y^2=A(x)C_d(x)\), with signed root \(y/C_d(x)=s\).

For an odd integer \(w\ge5\), set \(\delta=(w^2-1)/4\). At \(u=\delta\), use the two Pell solutions \((V,D)=(w,1)\) and \((2w^2-1,2w)\). The two resulting gaps are distinct integral polynomial functions of \(w\). The two units have exact common value \(\delta\), and their displayed roots both equal one on the common twist. Thus the rational family exists once the gaps can vary, with a uniform sign on its admissible reductions.

## A specialization with mixed signs

Work formally with \(\eta^2=\delta\) and put \(\epsilon=w+2\eta\), of norm one. Then
\[
 \epsilon^4=V_4+2s_4\eta,qquad
 V_4=8w^4-8w^2+1,\qquad s_4=8w^3-4w.
\]
Use \((u_1,V_1,D_1)=(\delta,2w^2-1,2w)\) for the first lift and \((u_2,V_2,D_2)=(\delta s_4^2,V_4,1)\) for the second. Their signed roots are \(1,s_4\). Define
\[
 A_-=4w^2-2w-1,\qquad A_+=4w^2+2w-1,\qquad
 N=A_-A_+=16w^4-12w^2+1 .
\]
The identities \(s_4-1=(2w+1)A_-\) and \(s_4+1=(2w-1)A_+\) give opposite signs on the two factors. They are coprime because both are odd, their difference is \(4w\), and each is \(-1\) modulo \(w\). The signed gcds with \(N\) return exactly \(A_-,A_+\), since \(s_4-1\) reduces to \(-2\) on \(A_+\) and \(s_4+1\) to \(2\) on \(A_-\). Neither factor needs to be prime. Their ratio tends to one.

At these specializations, \(u_1\equiv u_2\equiv\delta\pmod N\), so the squared gaps differ by \((\delta-1)^2(4w^2-1)\) modulo \(N\). The factor \(4w^2-1\) is a unit since \(N=(4w^2-1)^2-4w^2\). A single progression ensures that \(\delta\), the squared-gap difference, and all mark and argument differences are units. For the polynomial \(N(w)\), take resultants with the numerators after clearing powers of two of
\[
 \delta,\quad d_1^2-d_2^2,\quad
 d_i,\ d_i-1,\ d_i+1,\ x_i,\ x_i-1,\ x_i-d_i,\ x_i-d_i-1
 \quad (i=1,2).
\]
All are nonzero. Their product has odd prime support \(\{3,5,11,19,29,31,41\}\). At \(w=5\), \(N=9701=89\cdot109\) avoids this support. Hence every \(w\ge5\) congruent to 5 modulo \(2\cdot3\cdot5\cdot11\cdot19\cdot29\cdot31\cdot41\) is eligible, by specialization of the Sylvester determinant. [Resultants](https://ocw.mit.edu/courses/6-972-algebraic-techniques-and-semidefinite-optimization-spring-2006/46bf636ecc6195991e396703bfe1a1ae_lecture_06.pdf)

There is also a torus description of the supply on this family. At a good odd prime choose \(\eta\) in the algebraic closure. For powers \(\epsilon^j=V_j+2s_j\eta\), one has \(\epsilon^j-\epsilon^{-j}=4s_j\eta\). Equality \(s_i=s_j\) therefore gives \(\epsilon^{i-j}=1\) or \(\epsilon^{i+j}=-1\), by factoring the difference after clearing denominators. For \(s_i=-s_j\) the conditions are \(\epsilon^{i+j}=1\) or \(\epsilon^{i-j}=-1\). At primes of \(A_-\) the trace \(2w\) cannot be \(-1\) and \(\epsilon\ne1\). The roots of \(\epsilon^3=1\) are therefore excluded and \(\epsilon^5=-1\). At primes of \(A_+\) the trace cannot be \(1\) and \(\epsilon\ne-1\), so \(\epsilon^3=-1\) is excluded and \(\epsilon^5=1\). The polynomial input family supplies these short relations directly.

## Auxiliary fields and norm certificates

With \(W_i=AC_{d_i}\), take \(F_i=W_iG_i-W_i'\) with
\[
        G_1=X^3+8X^2+a_1X+b_1,\qquad
        G_2=X^7+3X^2+a_2X+b_2.
\]
On the progression above, require \(a_i,b_i\equiv0\pmod{11}\). The reductions of \(F_i\) modulo 11 then have prime degrees 7 and 11. Each has no root modulo 11 and divides \(X^{11^k}-X\) for its degree \(k\), as checked by successive modular powers. Over \(\mathbb Z/N\mathbb Z\), impose \(F_i(x_i)=0\) and \(F_i'(x_i)=1\). The first equation fixes \(G_i(x_i)=W_i'(x_i)/W_i(x_i)\). The second then fixes \(G_i'(x_i)\), determining \(a_i\) and afterwards \(b_i\). CRT gives both requirements because \(11\nmid N\). This constructs two distinct monic irreducible fields with simple modular evaluation maps. Their two block ratios are units in their power orders by the inverse identity for consecutive pairs.

The four absolute norms in each field are \(d_i(d_i+1),d_i(d_i-1),d_i(d_i-1),d_i(d_i+1)\), from the derivatives at the marks. Whenever the gaps and their neighbors are small or already factored, all the norm factors are therefore certified by these public integers. For \(w=5\) the gaps are \(50,5762399\), the arguments are \(36,5760000\), and the common unit residue is \(6\). The two signed roots \(1,980\) give the factors 89 and 109. The coefficients \((a_1,b_1,a_2,b_2)=(1254,14421,13827,18502)\) realize the chart conditions. The factorizations used for the norms are

| Gap | \(d-1\) | \(d\) | \(d+1\) |
| ---: | ---: | ---: | ---: |
| 50 | \(7^2\) | \(2\cdot5^2\) | \(3\cdot17\) |
| 5762399 | \(2\cdot1201\cdot2399\) | \(1009\cdot5711\) | \(2^5\cdot3\cdot5^2\cdot7^4\) |

From \(N\) alone one can recover a candidate \(w\) by checking \(4N+5=(8w^2-3)^2\) with integer square roots and verify the progression and quartic formula. The signed gcd split and the field construction then take polynomial bit time. The same recognizable formula gives the two factors directly. The family establishes variable-gap comparisons with explicit norm formulas and finite smooth-norm fixtures. A general one-third bound on the prime factors of \(d_i,d_i\pm1\), and the supply of productive comparisons on arbitrary inputs, remain open.
