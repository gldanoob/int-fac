# Full-grid parity through basis-only splitting

## Search an integer

From the repository root, run the driver with Python 3 and PARI/GP installed.

```sh
python3 -B experiments/cogentic-monic-kernel-driver.py 247
python3 -B experiments/cogentic-monic-kernel-driver.py 247 --degree 3 --relations-only
python3 -B experiments/cogentic-monic-kernel-driver.py 85 --degree 4 --planted --height 8 --relations-only
python3 -B experiments/cogentic-monic-kernel-driver.py 895 --degree 2 --height 20 --relations-only --all-ideals
```

The first command uses the scheduled degree and returns the direct factor 13. The second skips the preliminary mark gcds and searches for square relations. At height 64, it retains 945 marks, finds joint parity dimension 14, and verifies a signed square basis of dimension 14. Its certificates give both 13 and 19. The third command searches the planted norm-two family. Its two signed parity candidates are removed by local probes, giving a trivial square kernel on the included marks.

The JSON result identifies construction and mark gcds separately from square certificates. Each square certificate lists the marks, common sign, two residues, their common square and a proper divisor. The search checks the congruence and divisibility. A single-input run uses the [mark-local test and square-tail rule](cogentic-monic-local-roots.md), includes the [known dyadic ideals](cogentic-monic-ramified-two.md), and applies the [leading-unit probes](cogentic-monic-square-probes.md) through 257 before exact arithmetic. The default box height is 64 and the exact query cap is 128, adjustable with `--height` and `--queries`. A cap reports incomplete search. A completely exhausted basis only covers the admitted marks in that box. The single-input command has no wall-clock cutoff.

The single-input search uses the projective root-lattice collector at heights of at least 128 or inputs of at least 255 bits. With either collector the row identities and order agree. A search with the default preliminary gcd checks returns at the first verified split. The relation-only mode examines the supplied basis up to its query limit. [Sieve comparison](cogentic-monic-lattice-sieve.md)

The fourth command uses SageMath to compute complete ideal parity. At named small primes it constructs a local order, and at large composite residuals it tests private valuations without factoring the residual. At height 20 on 895 it admits 151 columns, finds seven parity dependencies and verifies five independent simultaneous squares. One certificate gives residues 572 and 502 with common square 509 modulo 895 and difference gcd 5. The faster default admits 63 columns and finds zero dependencies on this same grid. The separate PARI reference independently factors norms and checks these finite examples. [Exact parity and private valuations](cogentic-monic-singular-ideals.md)

## Original fixed comparison

Run `python3 -B experiments/cogentic-monic-kernel-driver.py` from the repository root. The bounded cubic and quartic replay uses the original five fixtures followed by the seven fixed holdouts. It repairs the common root before collecting relations. A proper derivative gcd returns a direct factor. The grid discards nonunit mark residues and extracts no direct factors from them. [Derivative repair](cogentic-monic-index.md)

For accepted pairs the driver reuses the full parity collector at $|a|\le64$, $1\le b\le64$, base bound $151$, and private-prime cutoff $8192$. Residuals above the cutoff are handled by exact integer square tests. The arithmetic control checks that $17\cdot8209^2$ contributes the same bounded parity as $17$ and $17\cdot8209^3$ is rejected. This residual rule also applies in the grid since a large odd ideal row is private. The successful marks at $247$ involve an even valuation at $433$, above the base bound and below the private-prime cutoff. [Full grid parity](cogentic-monic-large-primes.md)

The adaptive step processes the shared sign coordinate $-1$, followed by the ideal-parity basis in its returned order. Each incoming mask is tested against sums of the earlier independent class representatives. The first exact simultaneous square produces a basis vector. Exhausting those sums establishes a new independent class. The driver skips this step when the mark parity dimension is zero. The sign-only class cannot be a square in the cubic field, where the norm of $-1$ is negative. Each case allows 128 completed joint queries and five seconds of wall time for the exact-square phase. Discriminant computation has its own five-second cap. The results identify any resource cap and list the partial basis counts where available. [Adaptive recovery proof](cogentic-adaptive-square-kernel.md)

The GP oracle works in the polynomial quotient. For nonzero product $q(X)$ modulo $P$, it searches integer $t$ up to $\binom{2\deg P}{2}$ for which $\operatorname{Res}_X(P(X),(Y-tX)^2-q(X))$ is squarefree of degree $2\deg P$. This represents multiplication by the separating generator $Y=\sqrt q+tX$. One irreducible factor means there is no square root. In the split case, a degree-$\deg P$ factor describes one copy of the field. Its class $z$ of $Y$ determines a unique class $\alpha$ of $X$ via the linear gcd of $P(X)$ and $(z-tX)^2-q(X)$ over that factor field. A rational linear solve expresses $z-t\alpha$ in the basis of powers of $\alpha$. The oracle verifies the resulting square by reduction modulo $P$. Derivative clearing gives the modular root even when its original power-basis denominator is a nonunit. At the existing $N=895$ square fixture the returned root has coefficient denominator $15$ and evaluates to $502$ modulo $895$, with square $509$. The integrality check uses the scalar denominator of the cleared polynomial's coefficients. The driver needs no maximal-order initialization. [Exact square algebra](cogentic-monic-square-extraction.md)

The driver tests only emitted square-basis vectors for a proper gcd. For each vector it checks the two root evaluations square to the signed mark product and checks exact divisibility by any proposed factor. A complete basis whose root ratios are all trivial proves that every signed relation in the collected square kernel has a trivial ratio. [Basis-only splitting](cogentic-square-kernel-splitting.md)

| Input | Retained columns | Mark parity dimension | Exact joint tests | Square basis size | Outcome |
| ---: | ---: | ---: | ---: | ---: | --- |
| 35 | | | | | Direct derivative gcd $7$ |
| 77 | | | | | Direct derivative gcd $11$ |
| 143 | 187 | 0 | 0 | 0 | Zero parity |
| 221 | 314 | 0 | 0 | 0 | Zero parity |
| 323 | 564 | 1 | 3 | 0 | Trivial signed square kernel |
| 187 | 451 | 0 | 0 | 0 | Zero parity |
| 209 | | | | | Direct derivative gcd $19$ |
| 247 | 437 | 1 | 3 | 1 | Basis split, gcd $19$ |
| 299 | 123 | 0 | 0 | 0 | Zero parity |
| 391 | | | | | Direct derivative gcd $17$ |
| 437 | 75 | 0 | 0 | 0 | Zero parity |
| 10403 | 243 | 0 | 0 | 0 | Zero parity |

At $247$, the emitted square vector uses sign $-1$ and marks $(-31,3)$ and $(-1,1)$. Its root residues are $149$ and $111$, with common square $218$. Their difference gives $\gcd(38,247)=19$ and cofactor $13$. The full replay took under one second on the test machine. The signed square computation at $323$ leaves its known nontrivial unit correction outside the driver. The caps and the observed finite ranks give no uniform bound for future inputs. [Unit correction at 323](cogentic-monic-unit-corrections.md)
