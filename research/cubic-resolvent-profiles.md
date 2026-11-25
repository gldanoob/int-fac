# How many cubic splitting conditions can a norm field impose?

Consider a finite family of monic irreducible cubics over the rationals. At an unramified prime outside their polynomial discriminants, we want *all* family members to have a root modulo the prime. This is a sufficient local condition in the construction of hard examples for the cubic order search. A polynomial can also miss a factor for other reasons. [Role of the local condition](cyclotomic-order-multiples.md#a-lower-bound-on-the-search-height)

Allow a rational congruence class and one degree-one prime in a field $L$ satisfying prescribed abelian Artin conditions over $L$. This includes constraints from a ray class. On a specified attainable quadratic-character profile, the minimum possible degree of $L$ that can force the desired local condition is exactly
$$
                    2^r,
$$
where $r$ is the binary rank of the quadratic resolvent squareclasses that split on that profile. We allow selection of the abelian conditions and further rational congruences, and require a nonempty set of qualifying unramified primes. Additional inequalities on a generator or several simultaneous choices of prime ideals are outside this statement.

For the monic cubics with three coefficients in $[-5,5]$ the minimum over profiles is **$2^{28}$ for $p\equiv2\pmod3$ and $2^{13}$ for $p\equiv1\pmod3$**. A single rational prime can satisfy every splitting condition without belonging to a low-degree prescription that forces it.

## Why the rank gives the exact degree

For a noncyclic irreducible cubic let $E_i$ be its $S_3$ splitting field, $K_i$ its quadratic subfield and $\chi_i$ the associated quadratic character. The permutation of the three roots has sign $\chi_i(p)$. A negative sign gives a transposition and one root. A positive sign permits the identity or a three-cycle, and we need the identity. Call the corresponding quadratic classes active. The cyclic cubic fields must also split, an abelian condition over the rationals. The descriptions of prime splitting by cycle type and of densities use qualitative Chebotarev. [Stevenhagen and Lenstra, §2–3](https://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf)

Choose $r$ independent active classes and one $E_i$ over each. Let $B/\mathbb Q$ be a finite abelian extension containing all quadratic resolvents and the rational congruence data. Set $F=B\prod_{i=1}^r E_i$, $A=\operatorname{Gal}(B/\mathbb Q)$ and $G=\operatorname{Gal}(F/\mathbb Q)$. Its kernel over $B$ is
$$
                    V=\mathbb F_3^r .
$$
Indeed $E_i\cap B=K_i$, so this kernel embeds into the product of the order-three coordinates and surjects onto each. Conjugation by $A$ acts on coordinate $i$ by $\chi_i$. These are distinct nontrivial characters. Averaging against each character over their elementary abelian two-group of sign changes projects onto the corresponding coordinate over $\mathbb F_3$. All projections belong to the kernel.

Suppose a degree-$d$ field $L$, possibly non-Galois, is used to impose the conditions. Let $H$ be the image of $\operatorname{Gal}(FL/L)$ in $G$, put $W=H\cap V$, and write $S$ for its image in $A$. Then
$$
[A:S][V:W]=[G:H]=[F\cap L:\mathbb Q]\le d .
$$
The action of $S$ on $W$ factors through an elementary abelian two-group. The fixed part of $W$ has dimension at most the number of the selected $\chi_i$ trivial on $S$. Independence bounds that number by $\log_2[A:S]$. Every other eigenspace belongs to $[H,H]$. Indeed a lift acting by inversion gives the commutator $-2w=w$ on an inverted eigenvector. Thus $[H,H]\cap V$ contains a subspace of dimension at least
$$
r-\log_3[V:W]-\log_2[A:S]\ \ge\ r-\log_2 d.
$$

These commutators preserve an abelian Artin condition even if $L$ and its ray extension are non-Galois over the rationals. Lift the commutators to the compositum over $L$ with the abelian extension specifying the condition. They still fix that abelian extension, fix $B$, and have the specified projection on $V$. Starting with a Frobenius lift for an attainable degree-one prime, multiply it by one of these lifts. In a normal closure over the rationals the resulting element fixes $L$ and selects the same abelian Artin value at a degree-one prime of $L$. Chebotarev realizes its conjugacy class. If all active cubic coordinates of the initial element were identities, any nonzero change in $V$ gives a three-cycle in at least one selected field. Hence forcing the entire family requires $d\ge2^r$. The dimension counts freedom on marked Frobenius lifts. [Chebotarev and residue degree](https://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf)

For equality take $L$ to be the multiquadratic compositum of *all* active quadratic resolvents. Its degree is $2^r$. Over $L$, the compositum of every active $E_i$ and all cyclic cubic fields is abelian of three-power degree: each constituent has degree at most three and is cyclic. Prescribe identity there. The multiquadratic field of all resolvents has two-power degree over $L$ and meets this extension in exactly $L$. The chosen quadratic profile fixes $L$, so it and the identity are compatible and occur by Chebotarev. The finite abelian extension over $L$ is contained in a ray class field; if a single ray class is needed, choose an attaining prime's class. Rational quadratic conditions can be written as residue restrictions by quadratic reciprocity. This proves attainability of the degree bound. [Artin reciprocity and ray class fields](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

## The height-five calculation

Enumerate irreducible cubics using the rational-root test. Discard square discriminants and remove square factors from the other discriminants. This gives 196 distinct nontrivial squareclasses. Fixing $p\bmod3$ sets the value of $(-3/p)$; the remaining independent sign variables are $(-1/p)$ and $(\ell/p)$ for the other primes in the discriminants after eliminating 3. Every assignment occurs at unramified primes by quadratic reciprocity, CRT and Dirichlet. In particular one may choose the residue modulo eight to set $(-1/p)$ and $(2/p)$ separately.

The replay eliminates one sign variable at a time. For a fixed assignment on the remaining boundary of a group of rows, it keeps every possible subspace supported entirely on that boundary. For each such subspace it records the least rank already charged on the eliminated coordinates. When combining disjoint groups of eliminated coordinates, the charged ranks add and their boundary subspaces sum. Eliminating coordinate $v$ charges one precisely when the current boundary subspace projects nontrivially onto $v$. The new boundary subspace is its intersection with $v=0$. Minimizing over both sign values gives the exact global rank and an attaining assignment.

The quadratic class $[-3]$ is itself in the box. On the $p\equiv2$ branch it is inactive and projecting modulo it is injective on the active span. On the $p\equiv1$ branch it is active and one adds one to the projected rank. On the first branch at least 31 distinct resolvents split. All 8,192 assignments attaining this count have rank 31. Minimizing rank directly gives 28 and 13 on the two respective branches. Thus minimizing the number of splitting conditions and minimizing the degree of a suitable norm field can lead to different character profiles.

Run `python3 -B experiments/cubic-resolvent-profiles.py`. The height-two check exhausts all sign assignments and compares both minima to the elimination algorithm. At height five the replay checks rank witnesses against the original squareclasses. A separate PARI/GP field enumeration using `polredabs` on each irreducible gives 213 distinct cubic fields, four cyclic, and the same 196 nontrivial squareclasses. The computation concerns a finite polynomial family and does not construct a height-five failure for the order search. [Exact replay](../experiments/cubic-resolvent-profiles.py)

## Bounds as the coefficient height grows

Let $r_H(p)$ be the binary rank of the split, nontrivial quadratic resolvent classes from the monic cubic box of height $H$. For all sufficiently large $H$ and all primes outside the polynomial discriminants, the following unconditional bounds hold with absolute implied constants:
$$
\begin{array}{c|c}
p\bmod3 & r_H(p)\\\hline
2 & \displaystyle\gg H^{6/5}/\log H\\[2pt]
1 & \displaystyle\gg H^{3/2}/(\log H)^3 .
\end{array}
$$
Thus a degree-one prime condition in a single norm field with abelian Artin data requires field degree at least $2^{\Omega(H^{6/5}/\log H)}$ to force reducibility throughout the box on either branch. Even after fixing any attainable rational congruence profile, the limiting proportion having a root for every cubic is at most $3^{-r}$ when the profile fixes the resolvent signs with active rank $r$. Over the abelian field of the profile, the $r$ independent cyclic order-three coordinates are equidistributed by Chebotarev and all must be trivial. Subdividing a progression by the resolvent signs gives the same uniform branch bound. The density is taken with $H$ fixed and the prime range tending to infinity.

**A small defining polynomial for a cubic field.** If the field discriminant is $D$, the weighted Minkowski lattice has covolume $\sqrt{|D|}$ and the primitive vector 1 has length $\sqrt3$. Orthogonal projection perpendicular to 1 gives a rank-two lattice of covolume $\sqrt{|D|/3}$. A disk of radius $|D|^{1/4}$ has area greater than four times this covolume. Lift a nonzero lattice point in this disk to an algebraic integer. It generates the cubic field and its conjugates are within $2|D|^{1/4}$ of each other. Subtract the nearest integer to a real conjugate. One conjugate then has magnitude at most $1/2$, so the elementary symmetric functions bound the coefficient height of its monic polynomial by $9\sqrt{|D|}$. The same translation gives height $O(R^2)$ for an integral cubic generator whose conjugates all have magnitude at most $R\ge1$. [Martinet on the projected lattice, §5](https://jamartin.perso.math.cnrs.fr/Othertexts/discgeom.pdf)

**Mirror fields for $p\equiv2\pmod3$.** For a large prime $\ell\equiv4a^3\pmod9$, $a\in\{1,-1\}$, choose an even $n=(\ell/4)^{1/3}+O(1)$ strictly above the real cube root with
$$
\ell\equiv a+3n\pmod{27},\qquad v_3(4n^3-\ell)=3.
$$
The first congruence fixes $n$ modulo nine, with $n\equiv a\pmod3$. On this progression $4n^3\equiv a+3n\pmod{27}$, and adding nine to $n$ changes $4n^3$ by $27n^2\bmod81$. Choose a permissible class modulo 27 and then its even lift modulo 54.

Put $f=X^3+3nX^2-\ell$. Its possible rational roots $\pm1,\pm\ell$ are excluded by $3n+1<\ell$ and reduction modulo $\ell^2$ at the latter two. The polynomial $g(X)=f(a+3X)/27$ is monic integral. Its positive discriminant $\ell(4n^3-\ell)/27$ is prime to three and $O(\ell^{5/3})$. At two, $f$ reduces to the squarefree polynomial $X^3+1$. At a prime $s>3$, total ramification would make $f$ the cube of a linear factor modulo $s$: each conjugate would have the same residue in the degree-one residue field of the unique prime. Comparison of its zero linear coefficient, constant and quadratic coefficients would force $s=\ell$ and $s\mid n$, impossible. All remaining ramification is tame and partial, with discriminant exponent one. At $\ell$ the simple unit root $-3n$ lifts; the remaining monic quadratic reduces to $X^2$ and its constant term has valuation one, so it is Eisenstein. The field discriminant $D$ is therefore positive, odd, squarefree, prime to three and divisible by $\ell$.

The fundamental-discriminant cubic correspondence and Scholz reflection give a cubic field of discriminant $-3D$. Both fields have monic defining polynomials of height $O(\ell^{5/6})$ by the projection bound. For markers $Y<\ell\le2Y$ in the two indicated progressions, every $D=O(Y^{5/3})$ contains just its own marker, since a product of two markers exceeds $Y^2$. At $p\equiv2\pmod3$ the signs of $D$ and $-3D$ are opposite. One split class per pair gives independent vectors by projection onto the marker primes. The prime number theorem in these fixed progressions gives $\gg Y/\log Y$ pairs. Take $Y$ to be a sufficiently small constant times $H^{6/5}$. [Mantilla-Soler, Corollary 4.2 and Theorem 6.8](https://arxiv.org/pdf/1104.4598#page=17)

**Three negative classes for $p\equiv1\pmod3$.** Take primes in $(Y,2Y]$ congruent to one modulo 49. Form disjoint adjacent pairs. Their gaps sum to at most $Y$, so $\gg Y/\log Y$ pairs have gaps $O(\log Y)$ by the prime number theorem in this fixed progression. For such a pair write the primes as $u=m-h$ and $v=m+h$.

For $\ell=u,v$, take $t\equiv10\pmod{49}$ nearest to $3\sqrt\ell$ and $c=t^2-9\ell=O(\sqrt Y)$. Then $c\equiv42\pmod{49}$, and $X^3-3cX-2tc$ is Eisenstein at seven and has discriminant $-3\ell(18c)^2$. Its roots have size $O(\max(\sqrt{|c|},|tc|^{1/3}))=O(Y^{1/3})$, by comparing the leading term with the two others. Translation near its real root gives height $O(Y^{2/3})$.

For the pair use $P=X^3-3h^2X-2mh^2$, of discriminant $-108h^4uv$. Any integral root $z$ would satisfy
$$
(z+h)^2(z-2h)=2u h^2 .
$$
For large $Y$, the right side has $u$-adic valuation one, so $u\mid z-2h$. The root bound gives $|z|=O(h+(Yh^2)^{1/3})=o(Y)$, forcing $z=2h$, a contradiction. This irreducible polynomial gives the quadratic class $-3uv$ with translated height $O(Y^{2/3}(\log Y)^{4/3})$. The classes $-3u,-3v,-3uv$ have product $-3$ modulo squares. At $p\equiv1\pmod3$ at least one splits. Every choice gives independent vectors across disjoint pairs. Taking $Y$ proportional to $H^{3/2}/(\log H)^2$ with a sufficiently small constant proves the second bound.

An upper bound for the **minimum** active rank on the $p\equiv1$ branch is $O(H^2/\log H)$. All cubic polynomial discriminants have absolute value $O(H^4)$. Choose a quadratic profile making $-1$ and every prime up to the square root of that bound positive, and each larger prime in a discriminant negative. There is at most one such large prime in any discriminant and it occurs to exponent one. All active classes are supported on primes up to $O(H^2)$ and on the sign. The profile is attainable and has $(-3/p)=1$.

The PARI/GP replay certifies four mirror pairs, checks three triples and verifies the Frobenius sign against roots at 150 small-prime instances. At $\ell=1031$ it gives field discriminants $1{,}182{,}557$ and $-3{,}547{,}671$ with monic heights 48 and 106. In the close pair $1{,}000{,}001{,}213$, $1{,}000{,}001{,}311$, the three translated heights are $106{,}612{,}623$, $106{,}542{,}681$ and $853{,}884{,}720$. Run `gp -fq experiments/cubic-resolvent-growth.gp`. [Exact number-field and polynomial checks](../experiments/cubic-resolvent-growth.gp)
