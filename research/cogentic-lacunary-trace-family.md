# A two-by-two subset-product trace split on balanced semiprimes

For every fixed positive odd $\nu$, a finite library of two-by-two Hankel minors gives polynomial-bit-time splits on infinitely many balanced semiprimes. Each minor uses four exact pair-product traces, at exponents $0,1,E,E+1$ with $E$ a fixed affine function of $N^\nu$. On the constructed family all four traces are units, and the three product nodes have no local collision. The split comes from modular cancellation in the determinant. The family also admits direct tailored scalar and quadratic tests. [Subset-product traces](cogentic-subset-product-traces.md) · [Balanced affine prime forms](cogentic-balanced-shift-products.md)

## A fixed trace identity

Take the generator list $(56,21,24)$ and subset size two. Its three products are $168$ times $3,8,7$. Put $S_j=e_2(56^j,21^j,24^j)\bmod N$. The elementary symmetric recursion computes one trace using three modular powers and fixed-size arithmetic. Define
\[
\Delta_E=\det\begin{pmatrix}S_0&S_E\\S_1&S_{E+1}\end{pmatrix}
=168^{E+1}\,3\left(2\cdot8^E+7^E-3\cdot3^E\right)\pmod N.
\]
It is a minor of the Hankel matrix with row offsets $0,1$ and column offsets $0,E$. Its matrix size is two, while $E$ can be numerically large. Computing the four traces uses $O(\log E)$ modular multiplications.

At a prime $p\equiv73\pmod{168}$ the Legendre symbols of $3,8,7$ are respectively $+1,+1,-1$. For $3$ and $8$ this follows from $p\equiv1\pmod{24}$. For $7$ use reciprocity and the nonsquare $3\bmod7$. If $E\equiv1+(p-1)/2\pmod{p-1}$, the bracket in $\Delta_E$ becomes $16-7-9=0$. The trace entries at $p$ are units because, after removing the powers of $168$, they are $3,18,4,24$. The signed effective nodes $3,8,-7$ remain distinct modulo every sufficiently large $p$.

## A finite public library for balanced prime pairs

Fix a sufficiently large number $h$ of linear forms for Maynard's theorem with two prime values. Choose $h$ distinct fixed primes $\ell_i\equiv1\pmod4$, all greater than $h$ and in a common interval $(Y,1.1Y)$ for some fixed $Y$. Write $M=\prod_i\ell_i$ and choose slopes $a_i=168M^2/\ell_i$. Use a common positive intercept $b$ with
\[
b\equiv73\pmod{168},\qquad b\equiv1\pmod M,qquad
b\equiv1\pmod r\quad\text{for primes }r\le h\text{ with }r\nmid168.
\]
The fixed congruences are compatible. Enlarge $b$ within their common progression as needed below. For primes through $h$, setting the argument to zero makes all form values units. At larger primes each form excludes at most one class, since its slope and intercept are coprime. The tuple $a_i x+b$ is therefore admissible. Maynard's Theorem 3.4 supplies $\gg X/(\log X)^h$ values of $x$ in an interval of length comparable to $X$ with at least two prime values. The constants are fixed, so the interval can be chosen with all form values in $(X,2X]$ after rescaling by the least slope. Each pair of indices yields an injective list of products along the parameter. Thus the same lower bound counts distinct balanced semiprimes, up to a fixed multiplicity. [Maynard, Theorem 3.4](https://ora.ox.ac.uk/objects/uuid%3Aa08a24aa-e17c-4323-8aea-a1782d68c694/files/m19d2e3b9605819f668974f67909377e6#page=4)

Orient a pair of prime values as $p=a_i x+b$, $q=a_j x+b$ with $\ell_i<\ell_j$. Define the fixed shift and exponent
\[
s=b-\frac{\ell_i(b-1)}{\ell_j},\qquad
E=1+\frac{\ell_j(N^\nu-s^\nu)}4.
\]
The shift is a positive integer greater than one. Both $N$ and $s$ are $1\bmod4$, so the exponent is an integer. The affine relation gives
\[
q-s=\frac{\ell_i}{\ell_j}(p-1),\qquad
\ell_j(N-s)=(p-1)(\ell_j q+\ell_i).
\]
The last coefficient is $2\bmod4$. Also $(N^\nu-s^\nu)/(N-s)\equiv\nu\pmod4$ is odd. It follows that $E\equiv1+(p-1)/2\pmod{p-1}$, giving the vanishing minor at $p$. The splitting algorithm enumerates the fixed pair indices and computes the minors and gcds from $N$. It can skip a candidate if the exponent is nonintegral or nonpositive.

## A fixed resultant keeps the minor nonzero at the other prime

Put $C=\ell_i-\ell_j(s-1)$. The affine relation gives $\ell_i N\equiv C\pmod{q-1}$. Thus
\[
T E\equiv K\pmod{q-1},\qquad
T=4\ell_i^\nu,\qquad
K=T+\ell_j\bigl(C^\nu-(\ell_i s)^\nu\bigr).
\]
Here $T,K$ depend only on the prescribed constants. Because $\nu$ is odd and $C$ tends to minus infinity with $b$, choose $b$ large enough that $K/T\le-2$ for every allowed pair.

If the minor also vanished at $q$, the two units $X_0=(8/3)^E$ and $Y_0=(7/3)^E$ in $\mathbb F_q$ would satisfy
\[
X_0^T=(8/3)^K,\qquad Y_0^T=(7/3)^K,\qquad 2X_0+Y_0=3 .
\]
The corresponding system over $\mathbb C$ has no solution. The first two equations force $|X_0|\le(3/8)^2$ and $|Y_0|\le(3/7)^2$, so $|2X_0+Y_0|<3$. Substitute $Y_0=3-2X_0$ and take the resultant of the resulting two univariate polynomials after clearing denominators. It is a fixed nonzero integer, and the modular system can hold only at primes dividing that integer or the cleared denominators. Discarding such $q$ removes finitely many instances. Thus $\gcd(\Delta_E,N)=p$ on the remaining pairs.

The same argument even keeps $S_E$ and $S_{E+1}$ nonzero modulo $q$. After dividing by the appropriate powers of 168 and 3, vanishing would impose $1+X_0+Y_0=0$ or $3+8X_0+7Y_0=0$. Both are impossible over $\mathbb C$ since $(3/8)^2+(3/7)^2<1$ and $9/8+9/7<3$. Two more fixed nonzero resultants exclude those cases. The other two trace entries are fixed units for large primes. Finally, the original product nodes have pairwise coprime differences with $N$ once both primes exceed the largest difference.

## Scope of the scalar comparison

One can arrange that any prescribed finite set of direct tests $\gcd(a^{F(N)}\pm1,N)$ misses the family, for fixed rational bases $a\ne0,\pm1$ and fixed nonzero integer polynomials $F$. This includes any prescribed finite list of $N^j\pm1$ and their products. For $d=\deg F$, homogenization gives
\[
\ell_j^dF(N)\equiv\ell_j^dF(s)\pmod{p-1},\qquad
\ell_i^dF(N)\equiv\ell_i^dF(C/\ell_i)\pmod{q-1}.
\]
Both $s$ and $C/\ell_i$ are nonconstant affine functions of $b$, so one can avoid all zero right sides when fixing $b$. A sign hit at either factor would force the order of a fixed base to divide twice the corresponding fixed nonzero integer. Only finitely many primes support such an order. Even the individual power tests at the active exponent $E$ miss on sufficiently large pairs. At $p$, $a^E=a(a/p)$ cannot equal a sign unless $a\equiv\pm1$. At $q$, a sign hit would imply $a^{2K}=1$ for the fixed nonzero $K$ above.

The family nevertheless has an efficient tailored scalar test. The exponent $4(E-1)$ is a multiple of $p-1$, and its product by $T$ is congruent to the fixed nonzero $4(K-T)$ modulo $q-1$. Hence a fixed base such as 2 splits these instances after discarding finitely many primes at $q$. The pair constants also give the quadratic identity
\[
\ell_i p^2+(\ell_j s-\ell_i)p-\ell_j N=0,
\]
so testing its discriminant over the same library supplies another direct splitter. The result identifies a trace signal beyond the stated fixed direct tests, with no uniform gain over tailored shifts. It requires neither a short subset-product collision in the given menu nor reconstruction of a full moment recurrence.

## Exact check

For a two-form arithmetic fixture take $\ell_i=13$, $\ell_j=17$, $b=31825$. The slopes are 631176 and 482664, with shift 7489. At $x=2$ the primes are 1294177 and 997153, giving $N=1290492478081$. For $\nu=1$ the exponent is 5484593000017 and the four traces are $3,3024,204939398163,225548490184$. The determinant residue is 376294904520 with gcd 1294177. The congruences, unit traces and gcds were checked for 561 concrete prime pairs of these two forms at each of $\nu=1,3,5$. This check concerns the displayed identities, while the large admissible tuple supplies the infinite family.

The independent arithmetic fixture at $\nu=3$ uses $\ell_i=109$, $\ell_j=113$, $b=3842905$, and $x=26$. The primes are 6083317033 and 5868114409, with product 35697600335862428497 and shift 136033. The four traces are $3,3024,28582259396518296565,5830306937943421828$. Each is a unit. The Hankel determinant and the tailored base-two scalar both give gcd 6083317033. The signed gcds for $N\pm1,N^2\pm1$ on the bases $2,3,7,8,11,13,17$ are all one.
