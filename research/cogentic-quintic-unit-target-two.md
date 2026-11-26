# A two-block quintic order unit evaluating to two

Two translated blocks of consecutive pairs give a genuine unit in the power order, with public modular value \(2\) and no auxiliary factorization. The construction uses fixed marks \(0,1,6,7\) and evaluation argument \(21\). It allows coefficient bit length \(O(\log N)\).

## The power-order identity

Let \(A(Z)=(Z-a)(Z-a-1)\) and \(B(Z)=(Z-b)(Z-b-1)\) with disjoint integer root sets. Set \(W=AB\) and \(F=WG-W'\), with \(G\in\mathbb Z[Z]\). At an algebraic integer root \(\theta\) of \(F\) distinct from the four marks, write \(A,B,A',B',G\) for the values at \(\theta\). Then
\[
  AB'=B(AG-A'),\qquad A'B=A(BG-B').
\]
The discriminant identities \(B'^2-4B=A'^2-4A=1\) give the explicit polynomial expressions
\[
   \frac AB=B'(AG-A')-4A,\qquad
   \frac BA=A'(BG-B')-4B .
\]
Their product is one. Thus \(A(\theta)/B(\theta)\) is a unit of \(\mathbb Z[\theta]\) itself. The polynomial identities avoid any need to compute a maximal order or to interpret reduction of an algebraic fraction with a nonunit denominator.

## Fixed marks, modular target and irreducibility

Use \(a=0,\ b=6\) and take \(G(Z)=Z+C\). At \(Z=21\),
\[
 A(21)=420,\qquad B(21)=210,\qquad W(21)=88200,\qquad W'(21)=20790 .
\]
These values come from the small Pell solution \(41^2-2\cdot29^2=-1\), giving \(21\cdot20=2\cdot15\cdot14\). Preprocessing tests the fixed primes \(2,3,5,7,11\), and reports a proper divisor if one occurs on a composite input. With these primes excluded, use CRT to choose
\[
        C\equiv 20790\cdot 88200^{-1}-21 \pmod N,\qquad C\equiv6\pmod{11}.
\]
This gives \(F(21)\equiv0\bmod N\). Also \(F\bmod11=f_0(Z)=Z^5+3Z^4+Z-2\). The values of \(f_0\) on \(0,\ldots,10\), reduced modulo 11, are
\[
 9,3,3,3,1,9,8,2,6,1,10.
\]
Starting from \(Z\), the successive 11th powers modulo \(f_0\) are
\[
\begin{split}
&-Z^4-2Z^3-Z^2-5Z+5,\\
&3Z^4+2Z^3-3Z^2-5Z-5,\\
&3Z^4+3Z^3+2Z^2+4Z-1,\\
&-5Z^4-3Z^3+2Z^2+5Z-2,\qquad Z.
\end{split}
\]
Thus \(f_0\) divides \(Z^{11^5}-Z\) and has no linear factor. Since 5 is prime, it is irreducible. The monic lift \(F\) is irreducible as well. The public ring map \(\mathbb Z[\theta]\to\mathbb Z/N\mathbb Z\) sends \(\theta\) to 21 and sends the unit to 2. For a prescribed integer evaluation argument \(m\), replace \(Z\) by \(X-m+21\).

The unit has norm one, since
\[
       \frac{F(0)F(1)}{F(6)F(7)}
                    =\frac{42(-30)}{30(-42)}=1 .
\]
It is nontorsion. The only roots of unity in a quintic field are \(\pm1\), and equality to either sign would give a polynomial relation of degree at most two for \(\theta\). This construction realizes a fixed small rational target as the image of a genuine order unit. It supplies no bound on the order of \(2\) in the finite unit group, and the CRT choice of \(C\) need not satisfy a subexponential height restriction.
