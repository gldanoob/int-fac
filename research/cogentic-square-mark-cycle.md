# Exact squares on a four-mark cycle

A four-cycle of prime-product marks can give a square unit with a productive reduction. A fixed sextic splits $9703$ into $31$ and $313$ by comparing its algebraic square root with an integer square root. The same four marks give irreducible square-unit fields specializing at a fixed integer for every modulus coprime to $210$. For a semiprime, constructing a specialization with mixed signs in this family is equivalent to finding a proper divisor.

## Constructing the cycle square

Take distinct marks $a_{ij}=q_i r_j$ from four distinct primes and put
\[
 A=(X-a_{11})(X-a_{22}),\qquad B=(X-a_{12})(X-a_{21}).
\]
The constant terms agree, so
\[
 A-B=\delta X,\qquad \delta=(q_1-q_2)(r_2-r_1).
\]
Let $D$ be the monic product of any additional, distinct mark factors and set $F=X+ABD Q$. For irreducible monic $F$ with a root $\theta$, the norm of $a_{ij}-\theta$ has absolute value $a_{ij}$. For each of the four primes $p$, the two marks containing $p$ give $F\equiv X\bmod X^2$ over $\mathbb F_p$. The zero root is simple, so Hensel lifting gives a unique prime above $p$ at which $\theta$ reduces to zero, with residue degree one. The norm gives valuation one at this prime in each marked linear factor containing $p$. The alternating product $A(\theta)/B(\theta)$ is therefore a unit. It is in the square class of $-\theta D(\theta)Q(\theta)$, since their ratio is $1/(B(\theta)D(\theta)Q(\theta))^2$.

For any polynomial $S$, the exact identity $A-BS^2=\delta F$ is equivalent to $S^2=1-\delta ADQ$. If $q_2-q_1=r_2-r_1=2$, then $\delta=-4$. For this choice an integral family is
\[
 Q_T=T+ADT^2,\qquad S_T=1+2ADT,\qquad
 A-BS_T^2=-4F_T,\qquad F_T=X+ABD Q_T.
\]
The polynomial $F_T$ is monic when $T$ has leading coefficient $1$ or $-1$. At a root $\theta$, the square root of the cycle unit is $S_T(\theta)$ up to sign.

For odd marks this exhausts the exact identities $A-BS^2=-4F$ with $Q\in\mathbb Z[X]$ and $S\in\mathbb Q[X]$. The equality $S^2=1+4ADQ$ forces $S\in\mathbb Z[X]$ by Gauss's lemma and $S\equiv1\pmod 2$ by reduction in $\mathbb F_2[X]$. Write $U=(S-1)/2$. At every root $a$ of $AD$, $U(a)$ is $0$ or $-1$. All these values agree modulo two because every $a$ is odd, so they all coincide. After a global sign change in $S$ if needed, $U$ vanishes at the roots of $AD$, and $U=ADT$ in $\mathbb Z[X]$.

The exact identity also has a form for longer balanced cycles. Let $A,B$ be the equal-degree products of the two sets of alternating marks, with $A(0)=B(0)$, and put $C=(A-B)/X$. For $F=X+ABD Q$, any polynomial square-root representative $S\in\mathbb Q[X]$ has a quotient $H=(A-BS^2)/F$. Reducing $H F=A-BS^2$ modulo $B$ gives $H\equiv C\pmod B$, since $X$ is invertible modulo $B$. Writing $H=C+B H_1$ gives the exact equation
\[
 S^2=1-CADQ-H_1 F.
\]
If $\deg S<\deg F/2$, then $\deg H<\deg B$ and $H=C$. In particular the preceding classification applies to every such representative for the four marks with $\delta=-4$. The choice $S=1+CADT$, $Q=-2T-CADT^2$ gives one exact identity with $H=C$ for any cycle. It yields a monic $F$ when $C$ has leading coefficient $-1$ and $T$ has leading coefficient $1$ or $-1$. For any nonconstant $S$, comparing degrees also gives $2\deg S+\deg B\ge\deg F$. The sextic below attains equality.

## A productive sextic

Take $q_1=3,q_2=5,r_1=17,r_2=19$, $D=1$ and $T=-1$. Then
\[
 A=(X-51)(X-95),\qquad B=(X-57)(X-85),\qquad
 F=X+AB(A-1),\qquad S=1-2A.
\]
Modulo $13$, $F$ becomes $f=X^6-5X^5+3X^4-X^3-5X^2+4X-2$. All remainders and gcds in the certificate are taken over $\mathbb F_{13}$.

| $d$ | $(X^{13^d}-X)\bmod f$ | gcd with $f$ |
| --- | --- | --- |
| 2 | $5X^5+3X^4-4X^3-3X^2+2X+6$ | $1$ |
| 3 | $4X^5+2X^4-4X^3-5X^2-X+5$ | $1$ |
| 6 | $0$ | $f$ |

The zero remainder for $d=6$ gives squarefreeness and forces every irreducible factor to have degree dividing six. The other two rows exclude factors of degrees one, two and three. The monic sextic is irreducible over $\mathbb Q$.

At $m=50$, the marked factors have absolute values $1,45,7,35$, and $A(m)=45$, $B(m)=245$. The full product is $A(m)B(m)=105^2$. Set $N=9703$. Since $F(m)=485150=50N$, evaluation induces a map $\mathbb Z[\theta]\to\mathbb Z/N$. All four marked factors are invertible modulo $N$. The algebraic square root of $A(\theta)B(\theta)$ is $B(\theta)S(\theta)$, which evaluates to $-21805$. Comparing with the integer root $105$ gives
\[
 \gcd(N,-21805-105)=313,\qquad \gcd(N,-21805+105)=31.
\]
The example uses two fixed twin-prime pairs. The specialization below uses these same pairs for every input modulus.

## Specializing the family at an input modulus

Keep the same marks and $m=50$. If $t=T(50)$, direct substitution gives
\[
 F_T(50)=25(315t+2)(63t+1),\qquad S_T(50)=1+90t.
\]
For $\gcd(N,210)=1$, both linear factors have unit slopes modulo $N$, and their two roots $-2/315$ and $-1/63$ differ by a unit. Choose either root modulo $N$, then take $T=X+c$ with $c\equiv t-50\pmod N$ and $c\equiv1\pmod7$. These congruences are compatible, and every resulting $F_T$ is monic and irreducible. Modulo seven it is
\[
 f_7=X^8+2X^7+X^6-X^5+3X^4-3X^3+3X+2.
\]
The remainder of $X^{7^8}-X$ is zero. The remainder of $X^{7^4}-X$ is $3X^7-3X^6+3X^5-2X^4-3X^3-X^2+2X+3$, which has gcd one with $f_7$. This gives irreducibility by the same degree test.

The two prescribed classes modulo $N$ give $S_T(50)=3/7$ and $S_T(50)=-3/7$, respectively, so $B(50)S_T(50)$ agrees globally with one sign of $105$. To get a different class satisfying $F_T(50)\equiv0\pmod N$, one must assign different linear factors to different prime-power divisors of $N$. Any such class exposes a factor by $\gcd(N,315t+2)$ or $\gcd(N,63t+1)$. Conversely, a coprime factorization of $N$ allows such a class by the Chinese remainder theorem. This is an equivalence with finding a proper divisor for an odd semiprime coprime to $210$. For the numerical sextic, $t=-1$ makes the linear factors $-313$ and $-62$.

For two members of the same family,
\[
 F_{T_1}-F_{T_2}=ABD(T_1-T_2)\bigl(1+AD(T_1+T_2)\bigr).
\]
If they both specialize at $m$ modulo an odd $N$ and $A(m)B(m)D(m)$ is invertible, the gcd of $N$ with the difference of their reduced square roots is exactly $\gcd(N,T_1(m)-T_2(m))$. In particular the two constant choices $T=1,-1$ have defining values that differ by the unit $2A(m)B(m)D(m)$, so at most one specializes at such an $m$ for $N>1$.

Adjoining a formal square root of a nonsquare cycle unit also leaves a residue choice. A map on the order generated by the base elements extends to its quadratic algebra on a symbol $\eta$ with $\eta^2=A(\theta)/B(\theta)$ by assigning to $\eta$ a square root of the reduced unit. When one reference root is already known and the reduced unit is invertible, a root with mixed signs relative to it again yields a factor. The productive sextic above has its square root in the original field and uses an independently computed integer square root of the rational product.
