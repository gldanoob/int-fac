# How many cubic splitting conditions can a norm field impose?

Consider a finite family of monic irreducible cubics over the rationals. At an unramified prime outside their polynomial discriminants, we want *all* family members to have a root modulo the prime. This is a sufficient local condition in the construction of hard examples for the cubic order search. A polynomial can also miss a factor for other reasons. [Role of the local condition](cyclotomic-order-multiples.md#a-lower-bound-on-the-search-height)

Allow a rational congruence class and one degree-one prime in a field $L$ satisfying prescribed abelian Artin conditions over $L$. This includes constraints from a ray class. On a specified attainable quadratic-character profile, the minimum possible degree of $L$ that can force the desired local condition is exactly
$$
                    2^r,
$$
where $r$ is the binary rank of the quadratic resolvent squareclasses that split on that profile. We allow selection of the abelian conditions and further rational congruences, and require a nonempty set of qualifying unramified primes. Additional inequalities on a generator or several simultaneous choices of prime ideals are outside this statement.

For the monic cubics with three coefficients in $[-5,5]$ the minimum over profiles is **$2^{28}$ for $p\equiv2\pmod3$ and $2^{13}$ for $p\equiv1\pmod3$**. A single rational prime can satisfy every splitting condition without belonging to a low-degree prescription that forces it.

## Why the rank gives the exact degree

For a noncyclic irreducible cubic let $E_i$ be its $S_3$ splitting field, $K_i$ its quadratic subfield and $\chi_i$ the associated quadratic character. The permutation of the three roots has sign $\chi_i(p)$. A negative sign gives a transposition and one root. A positive sign permits the identity or a three-cycle, and we need the identity. Call the corresponding quadratic classes active. The cyclic cubic fields must also split, an abelian condition over the rationals. The descriptions of prime splitting by cycle type and of densities use qualitative Chebotarev. [Lenstra, §§2–3](https://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf)

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

The exact minimum ranks through height 13 are as follows.

| Height | $p\equiv2\pmod3$ | $p\equiv1\pmod3$ |
|---:|---:|---:|
| 1 | 0 | 0 |
| 2 | 0 | 2 |
| 3 | 4 | 6 |
| 4 | 14 | 9 |
| 5 | 28 | 13 |
| 6 | 46 | 14 |
| 7 | 64 | 18 |
| 8 | 83 | 25 |
| 9 | 101 | 27 |
| 10 | 136 | 30 |
| 11 | 176 | 39 |
| 12 | 215 | 42 |
| 13 | 267 | 45 |

The larger computation prunes boundary states by subspace dimension. If $(U,a)$ and $(V,b)$ have boundary spans $U,V$ and previously charged ranks $a,b$, discard the second whenever $a+\dim(U+V)-\dim V\le b$. For every possible later span $W$, the excess $\dim(U+W)-\dim(V+W)$ is bounded by $\dim(U+V+W)-\dim(V+W)\le\dim(U+V)-\dim V$. A sign variable may be fixed before elimination to fit memory. Its coordinate still belongs to the active vectors, so compute the joint span of all residual components before charging the final rank. The native search exhausted 4,096 conditioned assignments on each height-13 branch. Its upper witnesses were checked against a fresh enumeration of the original integer polynomials.

Run `python3 -B experiments/cubic-rank-frontier.py --verify-only 1 2 3 4 5 6 7 8 9 10 11 12 13` to check all 26 attaining sign profiles. Omit `--verify-only` to recompute the lower bounds with the Python implementation. Its running time increases sharply with height; `--cut` controls how many signs are fixed per subproblem. The four certificate columns give height, residue modulo three, rank and the hexadecimal mask of negative signs in increasing prime order, with $-1$ first. [Exact rank replay](../experiments/cubic-rank-frontier.py) · [Attaining sign profiles](../experiments/cubic-rank-frontier.txt)

## Several Galois fields with separate Artin conditions

Let each base field $L_j$ be Galois over $\mathbb Q$. Allow degree-one primes in each $L_j$ with separate abelian Artin conditions, as well as rational congruences. An active quadratic resolvent $K$ is covered if $K\subseteq L_j$ for at least one $j$. Containment in the compositum of several bases can leave it uncovered.

Group the cubic splitting fields by their quadratic resolvent $K$. Write $w_K$ for the dimension over $\mathbb F_3$ of their joint cubic Galois group over $K$. It counts independent cubic extensions with that resolvent. On any attainable fixed profile, the relative density of eligible rational primes that split every cubic above the **uncovered active** resolvents is exactly
$$
                         3^{-\sum_K w_K},
$$
with the sum over those resolvents. In particular any uncovered active resolvent prevents the prescription from forcing the whole family.

For the proof let $B/\mathbb Q$ be abelian and contain all resolvents and rational congruence data. Over $B$ the joint cubic kernel is the product of the blocks $V_K=\mathbb F_3^{w_K}$. Indeed inversion by a lift of the nontrivial automorphism of $K$ makes each cubic block its own commutator with that lift, so adjoining $B$ preserves its full rank. The quadratic-character projections used above separate the blocks.

Let $R_j$ be the rational normal closure of the abelian extension specifying the Artin condition over $L_j$. Each conjugate is abelian over the same field $L_j$, so $R_j/L_j$ is abelian. Work in one finite Galois extension $E/\mathbb Q$ containing all these fields and cubic closures. Put $H_j=\mathrm{Gal}(E/L_j)$, start with $T_0=\mathrm{Gal}(E/B)$, and take
$$
                       T_j=[H_j,[H_j,T_{j-1}]] .
$$
All the groups in this recursion are normal over $\mathbb Q$. The inner commutator belongs to both $H_j$ and $T_{j-1}$, hence $T_j$ fixes $R_j$ and every field already fixed by $T_{j-1}$. For an uncovered $K$, some $h\in H_j$ acts on $V_K$ by inversion. Commuting with $h$ sends each projected vector $v$ to $-2v=v$ in characteristic three. Each commutator therefore preserves surjectivity onto $V_K$. Normality and the distinct character projections give simultaneous surjectivity onto their product. The uncovered blocks over $B$ are consequently linearly disjoint from $B\prod_j R_j$ over $B$.

Existence of a suitable prime above a rational prime specifies a conjugacy-stable subset in this last extension. Over each eligible element, every possible value on the uncovered blocks occurs exactly once in their joint extension. The active sign makes the identity the unique value with a root in each cubic. Chebotarev gives the displayed relative density. For covered $K$, one can impose splitting through the abelian extension obtained by adjoining its cubic closures to a base containing $K$, provided the joint prescription is attainable. For bases chosen as composita of active quadratic fields and rational data chosen freely, attainability follows by the coprime-degree argument above. Requiring principal ideals, positive generators or integral norm representations introduces additional compatibility conditions. [Chebotarev density theorem](https://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf) · [Artin reciprocity](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

At height five, the minimum numbers of separate **quadratic** base fields on the two branches are therefore **31** and **24**. The first branch has 8,192 minimizing profiles and the second has 12. There is also an exact count for biquadratic fields on a given profile. Let $t$ be the maximum number of pairwise disjoint triples $a,b,ab$ among the $n$ active classes. The minimum number of quadratic or biquadratic fields covering them is $\lceil(n-t)/2\rceil$. Assign each class to one field in a cover. Every field assigned three classes consumes a whole triple. Conversely pack the triples and pair the leftovers. At all 8,192 first-branch minimum-count profiles the classes are independent and 16 fields suffice. Of the 12 second-branch minimum-count profiles, four require 11 fields and eight require 12.

Optimizing over **all** height-five profiles gives the same global minima, 16 and 11. Minimize the number of active classes minus the number of selected triples, imposing the quadratic profile equations, disjointness and activity of all three selected vertices. The exact minima of this integer objective are 31 and 22. Independent min-plus elimination had boundary widths 16 and 21. A second replay using Z3 regenerates the 196 classes from the polynomial box; it finds assignments at the stated bounds and proves the immediately smaller bounds infeasible on both branches. [Global cover replay](../experiments/cubic-biquadratic-cover.py)

At height six the global minima rise to **31 and 20** in the same branch order. The upper witnesses pack five disjoint triples among 67 active classes and nine among 49, respectively. For the lower bound assign nonnegative rational vertex weights whose sum on every eligible triple is at least one. Subtracting the total active weight from the class count then lower-bounds the integer objective. Exact elimination with denominator 300,000 leaves 36,136 and 1,340 assignments of the signs occurring in eligible triples within the candidate bounds. An exact disjoint-triple search excludes objectives at most 60 and 38. Rounding up half the objective proves the stated field counts. [Integer certificate replay](../experiments/cubic-biquadratic-cover-h6.py) · [Weights and upper witnesses](../experiments/cubic-biquadratic-cover-h6.json)

A finite check uses $L_1=\mathbb Q(i)$ and $L_2=\mathbb Q(\sqrt3)$. Require complete splitting in the closures of $X^3-3X^2-2$ and $X^3-6X^2-3X+2$, respectively. Their quadratic resolvents are $L_1,L_2$. The radical $X^3-2$ has the uncovered resolvent $\mathbb Q(\sqrt{-3})$, which is inside $L_1L_2$. Of the 250 qualifying primes $p\equiv1\pmod{12}$ below 100,000, the radical stays irreducible at 177 and splits at 73. The density theorem gives one third in the limit. [PARI/GP replay](../experiments/cubic-resolvent-growth.gp) · [Height-five cover replay](../experiments/cubic-resolvent-profiles.py)

### Nonnormal cubic bases

For a nonnormal cubic base $L$ with normal closure $N_L$, the rational normal closure of an abelian extension of $L$ is abelian over $N_L$. Indeed each conjugate extension becomes abelian after base change to $N_L$. Consequently any quadratic resolvent outside every base's normal closure retains its entire independent cubic block by the preceding commutator argument. Here eligibility is determined by Frobenius in the joint normal closure of the Artin fields, which is all the independence proof needs. An $S_3$ cubic base can thus affect only its own quadratic resolvent. In particular the height-five minima 31 and 24 also hold when bases of degree at most three are allowed. Quadratic bases achieve the bounds. A cyclic cubic base covers no quadratic resolvent, and a nonnormal cubic has only one in its normal closure.

Within a shared resolvent, different cubic directions can interact. The following example uses three nonisomorphic cubic base fields, each with a single existential requirement on a degree-one prime. Let $X=\mathbb F_3^2$, let the sign involution act on $X$ by inversion, and put $A=X^2\oplus\mathbb F_3^2$ with coordinates $(u,v,b,c)$. Translations $x\in X$ act on $A$ by adding $xb,xc$ to $u,v$, respectively. The involution negates $b,c$ and fixes $u,v$. These actions define $G=A\rtimes(X\rtimes C_2)$. It is solvable of order $2\cdot3^8$ and occurs over $\mathbb Q$ by Shafarevich's theorem. [Schmidt and Wingberg](https://arxiv.org/abs/math/9809211)

Let $l_1,l_2$ be the coordinate functionals of $X$ and $l_3=l_1+l_2$. For each $j$ use the cubic field fixed by the inverse image $H_j$ of the reflection subgroup in the quotient $(l_j(X),\mathrm{sign})\simeq S_3$. The three rational normal closures are distinct and have the same quadratic resolvent. The map $H_j\to\mathbb F_3^2$ sending an element to $(l_j(u),l_j(v))$ is an abelian quotient, since the translation component lies in $\ker l_j$. At positive quadratic sign, degree one in all bases forces the old coordinate $x=0$, so Frobenius lies in $A$. The possible Artin values in base $j$ are
$$
                      (l_j(u)+t_j b,\;l_j(v)+t_j c),\qquad t_j\in\mathbb F_3,
$$
by conjugating with coset representatives. Prescribe $(0,0)$ in the first two bases and $(0,1)$ in the third. Adding the first two equations and subtracting the third gives $(t_1+t_2-t_3)b=0$ and $(t_1+t_2-t_3)c=-1$. Thus $b=0$ and $c\ne0$ throughout the eligible set. It contains $u=v=b=0,c=1$, so Chebotarev gives positive density. The extra $S_3$ quotient $(b,\mathrm{sign})$, independent of the old two cubic coordinates over the resolvent, must split. The one using $c$ must be inert. The finite replay finds 18 admissible elements among all 729 in $A$. These are existential Artin conditions in abstract cubic fields; the specific fields in the height-five box were only used for the covering count above. [Group check](../experiments/cubic-resolvent-profiles.py)

## Bounds as the coefficient height grows

Let $r_H(p)$ be the binary rank of the split, nontrivial quadratic resolvent classes from the monic cubic box of height $H$. For all sufficiently large $H$ and all primes outside the polynomial discriminants, the following unconditional bounds hold with absolute implied constants:
$$
\begin{array}{c|c}
p\bmod3 & r_H(p)\\\hline
2 & \displaystyle\gg H^2/\log H\\[2pt]
1 & \displaystyle\gg H^{3/2}/(\log H)^3 .
\end{array}
$$
Thus a degree-one prime condition in a single norm field with abelian Artin data requires field degree at least $2^{\Omega(H^2/\log H)}$ on the first branch and $2^{\Omega(H^{3/2}/(\log H)^3)}$ on the second. Even after fixing any attainable rational congruence profile, the limiting proportion having a root for every cubic is at most $3^{-r}$ when the profile fixes the resolvent signs with active rank $r$. Over the abelian field of the profile, the $r$ independent cyclic order-three coordinates are equidistributed by Chebotarev and all must be trivial. Subdividing a progression by the resolvent signs gives the same uniform branch bound. The density is taken with $H$ fixed and the prime range tending to infinity.

**A small defining polynomial for a cubic field.** If the field discriminant is $D$, the weighted Minkowski lattice has covolume $\sqrt{|D|}$ and the primitive vector 1 has length $\sqrt3$. Orthogonal projection perpendicular to 1 gives a rank-two lattice of covolume $\sqrt{|D|/3}$. A disk of radius $|D|^{1/4}$ has area greater than four times this covolume. Lift a nonzero lattice point in this disk to an algebraic integer. It generates the cubic field and its conjugates are within $2|D|^{1/4}$ of each other. Subtract the nearest integer to a real conjugate. One conjugate then has magnitude at most $1/2$, so the elementary symmetric functions bound the coefficient height of its monic polynomial by $9\sqrt{|D|}$. The same translation gives height $O(R^2)$ for an integral cubic generator whose conjugates all have magnitude at most $R\ge1$. [Martinet on the projected lattice, §5](https://jamartin.perso.math.cnrs.fr/Othertexts/discgeom.pdf)

**Two ray class fields for each independent prime.** Take primes $\ell\equiv13\pmod{40}$. There are noncyclic cubic fields with the two respective quadratic resolvents $\ell$ and $-3\ell$, with defining heights at most $90\sqrt\ell$ for both fields. The discriminants of the quadratic fields are $D=\ell$ and $D'=-3\ell$. In the real quadratic field of discriminant $D$, the rational primes 2 and 5 are inert. In the residue unit groups $\mathbb F_{2^2}^{\times}$ and $\mathbb F_{5^2}^{\times}$, the elements of order three give two independent directions on which quadratic conjugation acts by inversion. The image of the global units has cyclic three-primary part, because the global unit rank is one. The exact ray class sequence modulo 10 therefore puts a nontrivial three-primary subgroup in the part of the ray class group on which conjugation acts by inversion. That part has a cyclic quotient of order three, even when a surviving local element itself becomes a cube in the class group. Decomposition into plus and minus parts is valid since two is invertible on a finite three-group. This is also the rank bound in Mayer's ring class formula. [Mayer, Theorem 2.1](https://arxiv.org/pdf/1403.3906#page=6)

In the imaginary quadratic field of discriminant $D'$, three is ramified and the global units are $\{\pm1\}$. The ring modulo three is $\mathbb F_3[\epsilon]/(\epsilon^2)$, with conjugation sending $\epsilon$ to $-\epsilon$. The unit $1+\epsilon$ supplies the required minus direction already at modulus three. In both cases the available cyclic cubic quotient gives an $S_3$ extension over the rationals. If its relative conductor is $f\mathcal O_K$, the cubic subfield has discriminant $D_K f^2$. Here $f$ divides 10 in the real case and 3 in the imaginary case. The height bound above applies with $|D_K|f^2$, giving respective heights at most $90\sqrt\ell$ and $27\sqrt{3\ell}$. The construction only needs a conductor dividing the indicated modulus. [Cohen and Morra, §1](https://arxiv.org/pdf/1003.1869#page=2) · [Artin reciprocity](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

Take $\ell\le(H/90)^2$. On the branch $p\equiv2\pmod3$ the symbols of $\ell$ and $-3\ell$ have opposite signs. Whichever class is active contains its own prime marker, absent from all the other pairs. The prime number theorem for the fixed progression gives $\gg H^2/\log H$ independent active classes. On **either** branch, the positive classes $\ell$ alone have independent signs as rational primes vary outside the discriminants. If there are $m$ markers then the active rank is at least a binomial $(m,1/2)$ variable in the limiting distribution. The fraction of profiles with rank below $m/3$ is at most $\exp(-c m)$ for an absolute $c>0$. This last estimate allows exceptional profiles on the second branch.

More generally, on any profile requiring a *fixed* quadratic squareclass $a$ to be negative, the same $\gg_a H^2/\log H$ lower bound holds. Choose two fixed primes $s_1,s_2\equiv1\pmod3$ splitting in $\mathbb Q(\sqrt a)$ and markers $\ell\equiv1\pmod{4s_1s_2}$ away from $a$. Both $\mathbb Q(\sqrt\ell)$ and $\mathbb Q(\sqrt{a\ell})$ split at these two primes. Each split pair of residue fields supplies one independent anti-invariant three-direction in the ray unit group. The global unit rank is at most one and the finitely many exceptional quadratic unit groups are avoided. A conductor dividing $s_1s_2$ hence suffices for both cubic fields. Their heights are $O_a(\sqrt\ell)$.

The ray-class replay constructs 14 cubic fields. It checks conjugation on the ray quotient, the conductor, the cubic discriminant and the height. For $\ell=100{,}213$ the conductors are 10 and 3 and the attained heights are 397 and 579. A separate tame-only test uses $s_1=7,s_2=13$. For $\ell=2549$ the imaginary cubic already has conductor 1. [PARI/GP construction](../experiments/cubic-ray-markers.gp)

**Mirror fields with conductor one for $p\equiv2\pmod3$.** For a large prime $\ell\equiv4a^3\pmod9$, $a\in\{1,-1\}$, choose an even $n=(\ell/4)^{1/3}+O(1)$ strictly above the real cube root with
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
