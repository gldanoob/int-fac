# Exact square roots from explicit power-basis products

Let $P\in\mathbb Z[X]$ be monic and irreducible of degree $e$, let $K=\mathbb Q(\alpha)$ with $P(\alpha)=0$, and let $q\in K$ have an explicit reduced rational power-basis representative. There is a deterministic square test that returns an explicit root when one exists, in bit complexity polynomial in the combined input size. The algorithm uses rational polynomial factorization and never computes a maximal order. [Finite replay](../experiments/cogentic-monic-index.py)

## Reduction to rational polynomial factorization

Return zero for $q=0$. Otherwise write $q=Q(\alpha)/h$ with $Q\in\mathbb Z[X]$, $\deg Q<e$, and $h>0$. Work in the rational algebra

$$\mathcal B=K[Y]/(Y^2-hQ(\alpha)).$$

The basis consists of $\alpha^i$ and $\alpha^iY$ for $0\le i<e$. Multiplication by $\alpha$ and $Y$ has integer matrices computed by reduction modulo the two defining equations. Over $\mathbb C$, evaluation at the $2e$ solutions of those equations gives a product of $2e$ copies of $\mathbb C$. In each pair above a fixed root of $P$, the two $Y$ coordinates are distinct because $q\ne0$.

Choose $z=Y+t\alpha$ by scanning the integers $0\le t\le\binom{2e}{2}$ and testing whether the coordinate columns of $1,z,\ldots,z^{2e-1}$ are independent over $\mathbb Q$. Each pair of distinct complex points forbids at most one $t$. At an allowed $t$ these powers are independent by the Vandermonde determinant. Their independence certifies that $z$ generates $\mathcal B$, so the characteristic polynomial $f(T)$ of multiplication by $z$ is also its minimal polynomial, monic and squarefree of degree $2e$. Computing $f$ can equivalently use a rational linear solve expressing $z^{2e}$ in the power basis of $z$.

Factor $f$ deterministically over $\mathbb Q$ by Lenstra, Lenstra and Lovász. If $q$ is a nonsquare in $K$, $Y^2-h^2q$ is irreducible over $K$, so $\mathcal B$ is a field and $f$ is irreducible. If $q$ is a square, $\mathcal B\cong K\times K$ as a $K$-algebra and $f=f_1f_2$ with two distinct monic irreducible factors of degree $e$. [Lenstra, Lenstra and Lovász, Theorem 3.6](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1982f/art.pdf)

In the split case solve $u f_1+v f_2=1$ over $\mathbb Q[T]$ with $\deg u,\deg v<e$. The element $j=u(z)f_1(z)$ is an idempotent with component values zero and one. In the two components, $Y$ has opposite values, so $(2j-1)Y$ is diagonal and has square $h^2q$. Reduce its coordinates in the original basis, check that every $Y$ coefficient is zero, and divide the remaining coordinates by $h$. The resulting $\beta\in K$ is the required root. The exact equality $\beta^2=q$ can be checked by monic reduction.

## Bit bounds and modular use

Write $H\ge2$ for the height bound on $P$ and $S$ for the total bit length of $Q$ and $h$. A common denominator has polynomial size in any explicit list of rational coefficients. Entries of the two multiplication matrices have $O(S+e\log(eH))$ bits by ordinary monic reduction. The trial matrices for multiplication by $z$ have the same bound since $t=O(e^2)$. The coordinate vectors through $z^{2e}$ have $O(e(S+e\log(eH)))$ bits, by bounding each matrix multiplication in the maximum norm. Exact determinant and linear-system operations have polynomial bit complexity by fraction-free elimination. The coefficient bits of $f$ have a polynomial bound by the determinant formula for the characteristic polynomial. Those of $f_i$ also have a polynomial bound, for example by bounding their roots using the root bound for $f$ and expanding the elementary symmetric functions. The Bézout equation is a rational linear system with $2e$ unknowns. Evaluating the output polynomials at $z$ needs only polynomially many matrix multiplications, with polynomial intermediate and final bit lengths.

For a product $q\in\mathbb Z[\alpha]$ of $R$ bounded linear marks as in the [common-root repair](cogentic-monic-index.md), the reduced explicit product has $O(eRV)$ bits. If $R\le\exp(O(W))$, the square test and root recovery cost $\exp(O(W))$. Every returned square root is integral, so multiply by $P'(\alpha)$, reduce, and divide its coefficient denominators over $\mathbb Z$ before evaluating at $m$. The only modular denominator in this formula is the unit $P'(m)$. This gives a certified square root image for each field with a good common root, even when the root itself has a power-basis denominator sharing a prime with $N$.

For example, at $N=895$ and $m=29$ the raw cubic is $P=X^3-28X^2+54$. The element

$$\gamma=\frac{\alpha^2-\alpha+3}{15}+\alpha+1$$

has square $8\alpha^2+2\alpha-12\in\mathbb Z[\alpha]$. The extraction replay returns $\gamma$ or $-\gamma$, and derivative-clearing evaluates it to $\pm502\bmod895$, with square $509$. The denominator $15$ is a nonunit, while $502$ is a unit. This calculation handles an explicitly given product. Finding qualifying products and proving that their common-root images split $N$ require separate arguments.
