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
