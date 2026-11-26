# Merging compatible quadratic evaluation charts

Two lists of marks in different presentations of the same quadratic field can have additional square words together. Merge the lists before local square elimination when their reduction maps agree after transport. This strictly enlarges the domain of rational root matching. In the example below, both separate signed square spaces vanish and the merged space splits 93. [Rational root matching](cogentic-rational-root-matching.md) · [Quadratic square kernel](cogentic-quadratic-square-kernel.md)

## Deciding compatibility without factoring

Let $P_i=X^2+b_iX+c_i$ be monic irreducible quadratics, with $\Delta_i=b_i^2-4c_i$, and let $m_i$ be simple roots modulo an odd $N$. Set $r_i=2m_i+b_i\bmod N$, so that $r_i^2=\Delta_i\bmod N$ and $r_i$ is a unit. The fields are isomorphic exactly when $\Delta_i/\Delta_0$ is a rational square. The test uses integer square roots on the reduced numerator and denominator.

For an isomorphic chart let $t_i$ be a rational square root of $\Delta_i/\Delta_0$ and put $\lambda=\sqrt{\Delta_0}$. Its numerator and denominator are units modulo $N$ because both discriminants are units. Transport the generator to $(-b_i+t_i\lambda)/2$. The two choices of sign for $t_i$ are the two isomorphisms. Compare $r_i$ with $t_i r_0\bmod N$. Their ratio has square one. If the ratio is a global sign, choose the sign of $t_i$ that gives equality. If the ratio has mixed signs, $\gcd(r_i-t_i r_0,N)$ is a proper factor, obtained directly from the two charts without any mark calculation. These are the only cases for odd $N$.

After alignment, compute a single quadratic square kernel on all the transported mark occurrences in $\mathbb Q(\lambda)$. Retain each occurrence's original integer label $a-bm_i$ for the subsequent rational matching. Transport preserves its value modulo $N$. Arguments chosen as different integer lifts of the same residue can change its rational squareclass. This is why the representative chart need not replace the original labels.

Every transported mark is integral, and a field square root of a product of integral elements is integral. If a root is $x+y\lambda$, its traces against $1,\lambda$ give $2x,2\Delta_0 y\in\mathbb Z$. Thus it reduces by evaluating $\lambda$ at $r_0$ and using unit denominators. The existing quadratic kernel takes arbitrary rational field coordinates, so rational affine transport needs no new norm or ideal computation. For explicit input pools, grouping, transporting, computing the local kernels and performing rational matching take polynomial bit time. A library of $\exp(O(W))$ explicit charts and marks with polynomial bit lengths keeps the one-third cost bound.

## Exact dimension gain

Give chart $i$ a binary exponent space $V_i$ on its own occurrences and write $I_i$ for its image in the common field squareclass group. Include the sign as an occurrence in each chart if the separate computation uses that convention. The old local space is $K_0=\bigoplus_i\ker(V_i\to I_i)$. The merged space $K$ is the kernel of the sum of these maps on $\bigoplus_i V_i$. Consequently

\[
\dim K-\dim K_0
=\sum_i \dim I_i-\dim\left(\sum_i I_i\right).
\]

Indeed, after quotienting by $K_0$, the extra space is exactly the tuples in $\bigoplus I_i$ whose classes sum to zero. For two charts the gain is $\dim(I_1\cap I_2)$. If $\psi$ is the map from exponent masks to rational classes of the retained labels, the gain that survives rational matching is the displayed number minus $\dim\psi(K)-\dim\psi(K_0)$. These are dimensions of square spaces. A proper split still depends on the normalized sign of a resulting root.

## A strict example

Take $N=93$, with these two charts.

| Polynomial | Argument | Primitive mark | Integer label | Norm |
|---|---:|---|---:|---:|
| $F=X^2+20X+72$ | 1 | $-7-X$ | $-8$ | $-19$ |
| $G=X^2+18X+53=F(X-1)$ | 2 | $-172-35X$ | $-242$ | $-13851$ |

The common discriminant is 112 and the derivatives at the two arguments are both the unit 22. The negative norms exclude each signed mark from being a square separately. Since the field is real, minus one is also a nonsquare. The translation $\beta=\alpha+1$ is compatible with the reductions. In the first field its transported second mark satisfies

\[
-207-35\alpha=(-7-\alpha)(9-2\alpha),
\qquad
9-2\alpha=(\alpha+9)^2.
\]

Thus the two mark classes agree and give one new local dimension on the unsigned occurrences. If each chart contains its own minus-one occurrence, the duplicated sign gives a second local dimension and only a global sign on normalization. The two-mark product is the square with root $(-7-\alpha)(\alpha+9)$. Its integer labels multiply to $1936=44^2$ and its root reduces to $-80$. The gcds of $-80-44,-80+44$ with $93$ are $31,3$.

Changing only the second argument to $95$ preserves the reduction and the local kernel. Its label becomes $-3497$, and $(-8)(-3497)$ is nonsquare, so this lift removes that rational match. Changing the second argument instead to $11$ gives another simple root of $G$ modulo $93$, with derivative $40$. The two discriminant roots $22$ and $40$ already give a proper gcd before any merging.

Run `python3 -B experiments/cogentic-compatible-quadratic-charts.py` to check the exact square-space dimensions, fractional discriminant transport, both label lifts and the incompatible-sign case. [Replay](../experiments/cogentic-compatible-quadratic-charts.py)
