# Uniform separation by a menu of moving elliptic curves

Under Dirichlet RH, an odd input $N$ has a deterministic polynomial-bit-time menu with the following guarantee. For every pair of distinct prime divisors $p,q$, either menu construction finds a proper divisor or some curve in the menu has full rational two-torsion, one explicit rational point, and stacked Kummer rank three on those three generators at $p,q$. The menu does not need the primes or their characters. This supplies the separation condition in the elliptic saturation splitter. The odd local exponent still needs to be covered on a separating curve. [Fixed-curve saturation](cogentic-elliptic-local-halves.md) · [Odd-class norm construction](cogentic-cm-torus.md#a-uniform-discriminant-menu-for-smooth-p1-or-p-1)

The same norm-lift conditions allow a single fixed marking at the reciprocal coordinate $c=1/b$. A conic gives many rational choices of the same marking while keeping the absolute local traces fixed. [Reciprocal marking and twist family](cogentic-fixed-marking-twists.md)

## Four choices of a marked coordinate

Take four distinct integers $x_0,\ldots,x_3$. For each marked index $m$ set
\[
 D_m=\prod_{i\ne m}(x_m-x_i),\qquad
 E_m:\ Y^2=\prod_{i\ne m}(X-D_m x_i),\qquad
 R_m=(D_m x_m,D_m^2).
\]
Substitution gives $Y^2=D_m^4$, and all three torsion points $(D_m x_i,0)$ are rational. Assume that all pairwise differences are units modulo the two odd primes. This gives good reduction and distinct torsion points at both.

For one of these primes let $b_{ij}$ be the quadratic character bit of $x_i-x_j$, with a negative symbol represented by one. Put $\omega=\sum_{i\ne m}b_{mi}$, and write $i,j,k$ for the other indices in increasing order. For columns $(R_m,T_i,T_j)$ the two Kummer rows associated to $D_m x_i,D_m x_j$ are
\[
 \begin{pmatrix}
 \omega+b_{mi} & b_{ij}+b_{ik} & \omega+b_{ji}\\
 \omega+b_{mj} & \omega+b_{ij} & b_{ji}+b_{jk}
 \end{pmatrix}.
\]
At an affine point different from the row's own two-torsion point, the entry uses the class of the coordinate difference. At the row's own two-torsion point it uses the derivative of the cubic there, and the factor $D_m^2$ is a square. These maps kill doubles and can be evaluated in either reduction for the proof. The modular algorithm only uses the public points and group law. [Rational two-torsion and Kummer maps](cogentic-elliptic-local-halves.md#including-the-two-known-torsion-points)

For a rational unit $w$ at both primes let $L(w)$ denote its pair of Legendre bits, encoded by the integers $0,1,2,3$ with the first-prime bit first. Analyze the normalized coordinates $(0,1,b,-1)$, and put $z=L(-1)$, $a=L(b)$, $h=L(b-1)$. Stacking the two rows at each prime gives a $4$ by $3$ matrix. The following conditions each force at least one of the four markings to give rank three, for every possible $L(2)$ and $L(b+1)$.

| $z$ | Sufficient choices of $(a,h)$ |
|---|---|
| $0$ | $(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)$ |
| $1$ | $(2,0),(3,0)$ |
| $2$ | $(1,0),(3,0)$ |
| $3$ | $(1,0),(2,0)$ |

Here is a finite check of all entries. Encode each difference by the pair of bits, with XOR as addition. For an ordered pair of indices $r>s$ the labels are
\[
 (b_{10},b_{20},b_{21},b_{30},b_{31},b_{32})
       =(0,a,h,z,z+L(2),z+L(b+1)).
\]
For the reverse direction add $z$. For each line in the table, each listed pair, and each of the 16 choices of the two unrestricted labels, form the four marking matrices by the displayed row formula. A marking has rank three exactly when the XOR span of its four rows has eight elements. The maximum rank across the four markings is three in every case.

## Prescribing the two adjacent square classes

Fix distinct prime divisors $p,q$ in the proof. In the first line of the table choose $a,h$ independent. In the other three lines choose $h=0$ and $a\notin\{0,z\}$. In either case $a\ne0$, $a\ne h$, and $a\ne z$. The public algorithm does not make these choices. It tries all entries in the following menu.

Let $Q=\lceil\log_2(2N)\rceil^6$ and trial divide through $Q$. Enumerate primes $s\le Q$ with $s\equiv3\pmod4$, and each odd prime $\ell\le Q$ that splits in $\mathbb Q(\sqrt{-s})$. The prime discriminant $-s$ gives odd class number $h_s$. Compute $h_s$ by reduced forms and find a generator of the $h_s$th power of a prime above $\ell$ by exact Gauss reduction of its integral ideal lattice. Write the generator as $(u+v\sqrt{-s})/2$. Its norm identity is
\[
                       4\ell^{h_s}=u^2+s v^2.
\]
This is the same polynomial-bit-time calculation as in the [varying norm-torus menu](cogentic-cm-torus.md#a-uniform-discriminant-menu-for-smooth-p1-or-p-1), including the class number computation and the oddness proof. The [norm generator](../experiments/cogentic-varying-norm-torus.py) returns the coordinates $(a_0,b_0)$ in the basis $1,(1+\sqrt{-s})/2$, so $u=2a_0+b_0$ and $v=b_0$.

Dirichlet RH gives a choice of $s$ with $L(s)=h$ and a choice of $\ell$ with $L(\ell)=a$. For the first choice the characters of conductors $4,p,q$ are independent. For the second the splitting character is $(\ell/s)$ by quadratic reciprocity, independent of the characters at $p,q$. In both cases expand the three prescribed signs by character orthogonality. The explicit-formula bound for each nonprincipal prime sum gives a positive count in $(Q/2,Q]$ for all sufficiently large $N$, uniformly in $p,q$ and the chosen $s$. Indeed the main von Mangoldt weight is $Q/16$ and the error is $O(\sqrt Q\log^2(4NQ))$. Prime powers and omitted primes are lower-order terms. This is the same uniform character estimate used for the [norm-torus menu](cogentic-cm-torus.md#a-uniform-discriminant-menu-for-smooth-p1-or-p-1).

Use the four integral coordinates
\[
                 (0,\ u^2,\ 4\ell^{h_s},\ -u^2)
\]
and all four markings. Neither $u$ nor $v$ is zero. Otherwise the norm identity would contradict either $h_s$ odd or $s\ne\ell$. The coordinates are therefore distinct over the rationals. They are the normalized coordinates above multiplied by $u^2$, with
\[
                  b=4\ell^{h_s}/u^2,\qquad b-1=s(v/u)^2.
\]
Scaling all four coordinates by a common scalar multiplies the Weierstrass roots and the point's abscissa by its fourth power and the ordinate by its sixth power. It preserves the Kummer labels at primes where that scalar is a unit. Since $h_s$ is odd, the two labels of the normalized coordinates are exactly $a,h$ when all differences are units at $p,q$.

Check the gcd with $N$ of each of the three integers $u$, $v$, $4\ell^{h_s}+u^2$ individually. A proper gcd ends the search and a full gcd discards that menu entry. For the separating choice of $s,\ell$, each full gcd is impossible even modulo the product $pq$. If both primes divide $u$, the norm identity forces $a=h$. If both divide $v$, it forces $a=0$. If both divide $4\ell^{h_s}+u^2$, it forces $a=z$. All contradict the chosen labels. The small primes $2,s,\ell$ have already been tested. Thus the winning entry either exposes a divisor or all pairwise differences are units at both primes. In the latter case the finite rank certificate applies. The guard tests separate gcds because different primes of $N$ could divide different differences.

The menu has polynomially many entries and all coefficients have polynomial bit length in $\log N$. Small inputs below the uniform analytic threshold can be handled by trial division. The argument uses no estimates for shifted quadratic characters.

The finite check verifies all 192 stated Boolean configurations and tests the norm lifts at $(p,q)=(53,73),(53,59),(59,67)$. For example, $(s,\ell)=(3,13)$ in the first pair gives $(u,v)=(-7,1)$ and the integral coordinates $(0,49,52,-49)$.

## The remaining order condition

At each good prime the subgroup generated by the public point and the two torsion points has quotient by doubles of dimension two, since it contains the whole two-torsion. Thus its integer relation lattice contains a nonzero parity class. When the stacked matrix has rank three, no nonzero parity relation can be common to both primes. The same argument applies after multiplying the public point by any odd scalar, with its Kummer labels unchanged.

Run the existing saturation splitter on each public curve with the odd multiplier \(\prod_{3\le r\le B,\ r\ \mathrm{prime}}r^{\lfloor\log_r(4N)\rfloor}\), where $B=\exp(O((\log N)^{1/3}(\log\log N)^{2/3}))$. Hasse's bound makes this sufficient for any $B$-smooth odd local exponent. The split is guaranteed if **some menu entry that separates a pair also has its odd generated-group exponent covered at one of those two primes**. The menu supplies separation uniformly, and it gives no bound on the odd exponents of the separating entries. [Saturation and modular gcd checks](cogentic-elliptic-local-halves.md#finding-a-relation-after-an-odd-public-power)
