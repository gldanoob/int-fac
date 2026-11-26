# Relative-order searches for several norm-one bases

A deterministic search can distinguish the relation lattices of several norm-one bases at hidden prime factors without an order multiple. If the generated subgroup at one prime has size at most \(U\), each generator costs soft \(O(\sqrt U)\) modular work. The search either returns a proper divisor or computes the same full relation lattice at every prime divisor. This covers noncyclic joint images even when each base has the same large order at both primes. [Boxed scalar order search](cogentic-boxed-order-relations.md) · [Class-five traces](colliding-quartic-torus-traces.md)

## A least relative order at the hidden primes

Let \(g_1,\ldots,g_t\) be explicit units of norm one in a quadratic algebra over \(\mathbb Z/N\mathbb Z\), with odd \(N\) coprime to the discriminant. At a prime \(p\mid N\), write \(G_{j,p}=\langle g_1,\ldots,g_j\rangle\) for the reduced group. Assume \(|G_{t,p}|\le U\) for one hidden prime. In a torus with radicand \(D\), one can always use \(U=\lfloor\sqrt N\rfloor+1\) on a composite because the group at its least prime divisor has order \(p-(D/p)\le p+1\).

Maintain relations for the initial \(j-1\) bases and relative orders \(r_i=[G_{i,p}:G_{i-1,p}]\), common at every prime in the absence of a split. The exponent box \(0\le a_i<r_i\) represents every element of \(G_{j-1,p}\) exactly once at each prime. Its size is \(D_{j-1}=\prod_{i<j} r_i\), with \(D_0=1\). To add \(g_j\), test
\[
         \left(\prod_{i<j}g_i^{a_i}\right)g_j^b=1,qquad
         0\le a_i<r_i,quad 1\le b\le\left\lfloor U/D_{j-1}\right\rfloor.
\]
The volume is at most \(U\), and at least one word is an identity at the promised prime by Lagrange's theorem in the quotient by \(G_{j-1,p}\).

The box test returns a proper divisor, a global relation, or a certificate that no local relation occurs in the box. Use prefix bisection in \(b\) to obtain the least possible \(b\) and one matching coefficient vector in the absence of a split. Every local relation in a tested prefix is global unless the test returns a divisor. Hence this least positive \(b\) is the relative order at every prime, and its coefficient vector is forced by the normal form for the previous generators. Append the relation and set \(r_j=b\). Induction shows that the resulting triangular relations generate the full kernel of \(\mathbb Z^t\to G_{t,p}\) at every prime. In fact the same relations generate the kernel modulo \(N\): they hold there, and the global kernel is contained in each prime-local kernel. This proof allows repeated prime divisors of \(N\).

Each finite-field norm-one group is cyclic. If the global image on the distinct prime reductions is noncyclic, its projection kernels cannot all agree, since agreement would identify it with one cyclic image. The search therefore splits in this case. It also splits some cyclic images with different kernels. The relative test can find a difference even when every individual base has the same order at every prime.

## Batched comparison and cost

Use the mixed-radix cut of the boxed scalar search on the interval widths. Translate the final coordinate by one and split at the first coordinate where the cumulative product of widths reaches the square root of the box volume. Quotient and remainder at that coordinate give at most two pairs of lists, each of size \(O(\sqrt U)\). Compute partial products on the left and inverses of partial products on the right, so a local relation is equality of the two quadratic coordinate tuples.

Search for proper gcds between nonidentical residues of each coordinate separately with the scalar product and remainder trees. A local tuple equality that is unequal globally forces a proper gcd in at least one coordinate. A gcd caused by just one coordinate, even with no full tuple match, also gives a valid factor. After both coordinate searches miss, sort full pairs to recover an exact tuple match or conclude that no local relation occurs. Exact equal coordinate buckets are removed by the existing derivative test. This avoids both the inverse ambiguity of comparing traces and polynomial arithmetic over a quadratic coefficient ring. [Scalar collision backend](cogentic-unit-collision-search.md#exact-product-buckets-with-global-hits-removed)

The search uses \(O(\log(2U))\) prefix tests per generator. Comparing the two scalar projections and sorting full tuples take soft \(O(\sqrt U)\) work per prefix. Only \(O(\log(2U))\) previous radices can exceed one. Keep their axes, and encode each exponent tuple by its mixed-radix index until a match is recovered. Thus setup, word evaluation and recovery contribute only logarithmic factors and the total cost is \(\widetilde O(t\sqrt U)\) modular work, with bit overhead polynomial in \(\log N\). If \(U\) is supplied by geometric doubling, a round whose full prefix has no local relation at some stage can be abandoned. The total work up to the first sufficient cap remains soft \(O(t\sqrt U)\). The unconditional choice \(U=\lfloor\sqrt N\rfloor+1\) gives a factor-or-common-kernel search in soft \(O(tN^{1/4})\) work. A one-third bound would need stronger arithmetic information that reduces the explored volume.

## A generic bound on the relative search

Let \(\ell\) be a prime. In a model that exposes only equality of the two local coordinates, take \(g=(1,1)\), \(h=(x,y)\) in additive coordinates in \(\mathbb F_\ell^2\), with \(x,y\) hidden. Permit an arbitrary exponent pair \((a,b)\) per probe, which gives local values \(a+bx,a+by\). Two distinct probed exponent pairs modulo \(\ell\) can coincide in one local coordinate for at most one value of its hidden slope. Repeating an exponent pair gives equalities at both coordinates regardless of the slopes.

Follow the transcript with no equalities between distinct pairs. For \(Q\) queried pairs there are at most \(\binom Q2\) exceptional slopes. If at least two slopes remain, both \(x=y\) and \(x\ne y\) realize this transcript. Therefore a deterministic equality-based test cannot always distinguish the common kernel from rank two before \(\Omega(\sqrt\ell)\) probes. The same reasoning applies to exhibiting a separating relation with a single extra verification probe. The model already permits separate local equality tests and arbitrary-size exponents. Its bound does not apply to algorithms using arithmetic properties of the residue encodings. [Shoup's generic collision method](https://www.shoup.net/papers/dlbounds1.pdf)

## Exact rough-order fixtures

Take \(D=3\), \(g=2+\sqrt3\) and \(h=(a+\sqrt3)/(a-\sqrt3)\) with the public integer \(a\) shown below. In each row both bases have the listed order at both primes. The relative logarithms are used only to verify the resulting relations.

| Prime factors | \(a\) | Common individual order | Local exponents \(h=g^x\) |
|---|---:|---:|---|
| \(263,523\) | 13 | 131 | \(79,124\) |
| \(2557,5113\) | 17 | 2556 | \(709,1579\) |

The first joint image is \(C_{131}\times C_{131}\). The second has a nontrivial two-primary kernel on each projection. The search with \(U=\lfloor\sqrt N\rfloor+1\) reaches the relative stage in both rows and splits there. In the second row \((hg^{-709})^{213}\) is \(+1\) at 2557 and \(-1\) at 5113, since \(1579-709=870\) and \(2556/\gcd(2556,870)=426\). Its trace is \(13053487\) modulo \(13073941\), giving a class-five parameter. The relative relation already gives a factor before taking this additional power. An independent check with the monic collision backend also tested 170 small searches, including moduli with repeated primes and a complete common-kernel outcome.

Run the public-input search with SageMath available in Python.

```sh
python3 -B experiments/cogentic-torus-relative-order-search.py 13073941 --bases 3 17
```

The arguments to `--bases` are the public parameters in \((a+\sqrt3)/(a-\sqrt3)\), with \(a=3\) giving \(g\). The command reports a factor or the search status in JSON, together with the box cap, number of prefixes tested, and total list entries built on this input. `--bound` sets the box cap. A common-kernel outcome lists all relative orders and the relations as pairs of one-based base indices and exponents. Omit \(N\) for the self-check. [Implementation](../experiments/cogentic-torus-relative-order-search.py)
