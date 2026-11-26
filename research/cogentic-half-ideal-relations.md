# Principal relations from half-ideal lattices

Explicit half ideals let a square search distinguish a class obstruction from a unit obstruction. A simple exact reduction can certify relations among nonprincipal half ideals, lowering the rank bound for subsequent complete square tests. A separate example uses principal generators found in their ideal lattices to split $371=7\cdot53$ with unit corrections. Its original marked elements and their negatives are nonsquares. [Ideal square roots](cogentic-maximal-ideal-roots.md) · [Replay](../experiments/cogentic-half-ideal-relations.gp)

## Compressing the half-ideal classes

Let $O$ be a supplied maximal order. Take a list of nonzero even-ideal products $\beta_j$ with explicit integral half ideals $I_j^2=(\beta_j)$. Each ideal class $[I_j]$ has order dividing two. The products may come from a basis of the ideal-parity kernel, so the original marks need no separate description of their prime-ideal support. For each $j$ choose any nonzero $x_j\in I_j$ and set
\[
J_j=(x_j)I_j^{-1}.
\]
This is an integral ideal obtained by a lattice quotient. It has class $[I_j]^{-1}=[I_j]$ and its square is principal with the known generator $x_j^2/\beta_j$. In particular, $J_j=O$ certifies that $x_j$ generates $I_j$. If $J_i=J_j$, then $x_i x_j/(x_j^2/\beta_j)$ generates $I_i I_j$. Equality of residual ideals is exact HNF equality.

One can group the $J_j$ by equality, omitting $O$. Zero incidence on these residual labels gives a binary subspace of certified principal combinations, because even powers of every label have known generators. If there are $s$ distinct nonunit labels, the rank of the half-class image is at most $s$. More generally, each independent verified principal relation decreases the upper bound $k-b$ on this class rank by one, where $k$ is the number of basis products and $b$ is the rank of the certified principal relations on them. This bound concerns the actual half ideals, so it can be smaller than a rank bound using the full original prime-ideal support.

There is a stronger integer relation test when residual ideals overlap. Refine the $J_j$ into pairwise coprime ideal atoms by ideal sums and quotients. Let $A$ be the integer atom-exponent matrix of the $J_j$. Let $L$ have columns given by exact principal relations on these atoms, each supplied with its principal generator. Since every $J_j^2$ has its known generator, include its principal relation $2A_j$. On a binary mask $v$, the condition
\[
Av\in L\mathbb Z^{\#L}+2A\mathbb Z^k
\]
certifies a principal combination. Let $H$ be a column Hermite basis of the lattice on the right and solve $HY=2A$. The solution is integral because the lattice contains $2A$. It is unique since the columns of $H$ are independent, even if its rank is smaller than the ambient atom count. Then $Av$ belongs to the certified principal lattice exactly when $Yv$ is even coordinatewise. Thus the binary test is the matrix $Y\bmod2$. For a passing mask, $Yv/2$ gives its coordinates in $H$. Tracking the Hermite transformation expresses these coordinates in the supplied principal relations, hence gives a product of known generators. This may be kept in a compact exponent representation if its expansion would be large. Ordinary parity of the atom exponents would be insufficient by itself, since a nonzero order-two class can be a double of an order-four class.

These certified kernels may omit genuine principal relations when the residual ideals have additional class equivalences. The upper bounds remain valid because the lattice and generators prove every relation they use. Computing the row rank uses no factorization of the residual norms. [Gcd-free ideal atoms](cogentic-cubic-square-resolvent.md#fixed-field-algorithm-using-ideal-lattices)

## Exact unit residuals and growth-range cost

For a certified principal combination let $I_v=(g)$ and $I_v^2=(\beta_v)$. The exact quotient $\beta_v/g^2$ is an order unit. The original product is a field square exactly when this unit is a field square. A square root of the unit is itself a unit by integrality of it and its inverse. For constructing corrected squares, multiplying $\beta_v$ by $g^2/\beta_v$ gives $g^2$ directly. A modular factor still requires alignment of the correction residues and differing root signs at primes of $N$. [Unit alignment criterion](cogentic-monic-unit-corrections.md#criterion-once-base-corrections-are-available)

If the certified principal relation rank is $b$, the unresolved square-class rank is at most
\[
(k-b)+r_1+r_2 ,
\]
where $r_1,r_2$ are the real and complex-pair signature counts. Indeed the half-class image has rank at most $k-b$, and its kernel consists of unit classes. This bounds [complete adaptive square search](cogentic-adaptive-square-kernel.md) for the original domain, including any principal masks that the certificate missed. For several fields sum the corresponding rank bounds. A total residual of $O(W)$ gives unconditional one-third work on explicit one-third-size inputs.

Short-element search is one way to produce certificates. In the HNF basis of a half ideal, enumerate coefficient vectors of height at most $B$. Compare each candidate's principal lattice to the half ideal, or compute its residual lattice exactly. This takes at most $(2B+1)^d$ trials in degree $d$. With $B$ polynomial in $\log N$ and $d\log\log N=O(W)$, this stage itself fits the one-third scale per supplied half ideal. Repeated residuals or small certified atom presentations then give a measurable rank bound. The height and rank guarantees for what this search finds are instance-dependent.

An odd-degree extension can also transfer a supplied principal generator back. If $[L:K]=e$ is odd and $IO_L=(a)$, taking the ideal norm gives $I^e=(\operatorname{Nm}_{L/K}a)$. When $I^2=(\beta)$, the element $\operatorname{Nm}_{L/K}a/\beta^{(e-1)/2}$ generates $I$. The same formula descends a supplied square root of $\beta$ in $L$. Equivalently, extension in odd degree cannot kill a nonzero order-two class. This supplies a certificate from a known upstairs generator without guaranteeing that one can be found.

## Exact quadratic reduction without factoring the norm

In an imaginary quadratic field, the positive definite integral norm form of an ideal $I$ is
\[
Q_I(x,y)=\frac{\operatorname{Nm}_{K/\mathbb Q}(x v_1+y v_2)}{\operatorname N(I)}
\]
for an integral basis $v_1,v_2$ of $I$. Its coefficients come from three multiplication determinants. Gauss reduction changes the two basis vectors until the coefficients satisfy $|b|\le a\le c$. The first basis vector then attains the exact minimum of $Q_I$ on nonzero integer vectors, since $a x^2+bxy+c y^2\ge a(x^2-|xy|+y^2)\ge a$. This minimum is one exactly when $I$ is principal, by equality of norms for the contained principal ideal. The same reduction also returns an exact norm-minimizing element even when $I$ is nonprincipal.

The replay takes $K=\mathbb Q(\sqrt{-5})$ and obtains the half ideals of $2+\sqrt{-5}$ and $2$ from their principal lattices. Their respective ideal norms are 3 and 2, and both reduced norm-form minima are 2, certifying both nonprincipal. The reduction finds $x_1=x-1$ and $x_2=2$ up to sign, where $x=\sqrt{-5}$. Their exact ideal quotients $J_1,J_2$ coincide with the second half ideal. Thus their product is principal, generated by $x-1$ up to sign. The remaining unit is $-1$:
\[
(x-1)^2=-2(2+x).
\]
For these two basis products the half-class rank is exactly one, and the remaining sign distinguishes the ordinary product from its negative.

A second check uses $x=\sqrt{-14}$ and the ideal $\mathfrak p=(3,1+x)$. The recovered half ideal of $(5+2x)$ is $\mathfrak p^2$. The norm minimum certifies $\mathfrak p^2$ nonprincipal, while its square is principal with generator $5+2x$. Taking $x_j=5+2x$ leaves the residual $J_j=\mathfrak p^2$. In the one-atom presentation $A=[2]$ and $H=[4]$, so $Y=[1]$ retains the nontrivial half-class row. The original exponent parity $A\bmod2$ would erase it.

## Productive half-ideal generators at 371

The corrected squares can be planted without choosing prime factors. For positive $k_+>k_-$ of the same parity, put $2m=k_+^2-k_-^2$ and take $F_\pm=X^2\pm X-k_\pm^2$. Both values at $m$ are the same integer. In each quotient, the primitive mark $-X$ has negative square norm, and $(k_\pm-X)^2/(-X)=2k_\pm\mp1-2X$ is an integral unit of norm $-1$. Thus these parameters provide base corrected squares. Whether their residues align productively depends on the parameters and the unit powers used.

Take $N=371$, $m=20$ and
\[
F=X^2+X-49,\qquad G=X^2-X-9 .
\]
Both evaluate to $N$ at $m$ with derivative units. Their prime discriminants 197 and 37 certify the supplied maximal power bases. Use the common primitive mark $-X$. The field norms are $-49$ and $-9$, so neither sign can be a square in either field. Both principal ideals are squares.

The replay computes both half-ideal HNFs, enumerates basis coefficients of height one, and checks candidate principal generators by exact HNF equality. It finds two candidates per field up to sign. The successful generators are $7-\alpha$ and $3-\beta$. Their corrections are $u_F=13-2\alpha$ and $u_G=7-2\beta$, each checked by its integral multiplication matrix and norm. Enumerating correction powers at total absolute exponent at most four yields the roots
\[
r_F=7-\alpha,\qquad r_G=(3-\beta)u_G^4 .
\]
They reduce to 358 and 225. Their squares both reduce to 169, and the difference gcd is $\gcd(133,371)=7$. The replay verifies that each corrected field element is an exact square with a unit correction and verifies both reductions. The lattice and modular steps receive no factorization of the input.

Run from `experiments` with `gp -fq < cogentic-half-ideal-relations.gp`. The productive example concerns a unit-corrected relation. Its original signed one-mark kernel is trivial, and the search bounds cover only the specified coordinate box and unit words.
