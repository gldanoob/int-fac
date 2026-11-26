# Restricting quadratic descent to the discriminant support

For a monic irreducible quadratic $P=X^2+uX+v$ with discriminant $D=u^2-4v$, the full square kernel of primitive grid marks can be recovered using two binary kernels. The first uses exact ideal parity away from $2D$ and signed rational norm classes on $2D$. The second uses only rational classes supported on $2D$. This gives an exact alternative to the [two-stage unrestricted quadratic descent](cogentic-quadratic-square-kernel.md) and leaves prime ideals over discriminant primes out of the first stage. [Implementation and replay](../experiments/cogentic-quadratic-supported-kernel.py)

## Factor-free support splitting

For a positive integer $M$ and support integer $S=|2D|$, initialize $g=\gcd(M,S)$ and $c=M/g$. Repeatedly move $\gcd(g,c)$ from $c$ to $g$ until they are coprime. Their product stays equal to $M$. At each prime in both, the exponent in $g$ doubles or reaches its full value in $M$. There are at most $O(\log\log(2M))$ rounds. At the end $g$ contains exactly the prime powers of $M$ supported on $S$, with no factorization of either input. Apply the same operation to a rational numerator and denominator to obtain its supported class and its coprime factor.

## Bounded conjugate rows and private ideals

For each marked element $z=a-b\alpha$, take the signed norm $a^2+uab+vb^2$. Separate its absolute norm into parts supported on and away from $2D$. Keep the norm sign with the supported part. Use the signed gcd-free rational squareclass columns for these supported parts.

If an odd $p\nmid 2D$ divides a primitive mark norm, then $b$ is a unit modulo $p$ and $a/b$ is a simple residue root. Hensel gives one degree-one prime ideal dividing the mark at that root, with exponent equal to the rational norm valuation. A rational prime can have two such rows, one for each conjugate root. For $p\le2H^2$, retain both row identities and sieve them by the residue lattices on the box $|a|\le H$, $1\le b\le H$. For an unfactored residual coprime to $2D$ after this sieve, require its absolute value to be an exact square. If a remaining prime has odd valuation, its ideal is private to that mark. Two distinct primitive marks sharing that ideal would give a nonzero determinant $ab'-a'b$ divisible by $p$, with absolute value at most $2H^2$. Every square word consequently has zero coefficient at a rejected mark.

For example, in the height-one box for $X^2+12$, the marks $(1,1)$ and $(-1,1)$ both have norm 13. Their rational norm classes cancel in the two-mark product. They correspond to different conjugate ideals above 13, so both columns are deleted by the private test. A rational norm kernel on its own can keep such columns, including when conjugate marks have exactly equal norms. [Rational-only bounded norm parity](cogentic-quadratic-grid-norms.md)

The combined first kernel has square rational norm and even ideal valuations at every $p\nmid 2D$. All actual square words lie in it. The added generator $-1$, when requested, has positive square norm and empty ideal column. No ramified or index-prime ideal decompositions are needed.

## Supported descent is exact

For each first-kernel basis word, form its product $\beta$, write $N(\beta)=t^2$, and choose the sign of $t$ so that $s=\operatorname{Tr}(\beta)+2t\ne0$. The identity $(\beta+t)^2=s\beta$ represents the class of $\beta$ by the rational scalar $s$. At an ideal $\mathfrak p$ over $p\nmid 2D$, the product has even valuation, so $v_{\mathfrak p}(s)$ is even. The prime $p$ is unramified, giving $v_{\mathfrak p}(s)=v_p(s)$. Thus the rational factor of $s$ coprime to $2D$ is a square. The implementation verifies this by exact square tests on the positive coprime parts of the numerator and denominator, then discards them. It retains the sign.

Include $D$ as the auxiliary rational scalar in the second gcd-free kernel. Its projection gives precisely the first-kernel words whose scalar is square in the quadratic field. Compute each returned root from the original product as in the unrestricted descent. This detects the remaining constraints even when the first stage has left the ideal valuations at all primes dividing $2D$ unresolved. Restricting an arbitrary norm-only basis by stripping scalars would require an additional away-parity argument or the full scalar calculation. The square check in `supported_scalars` rejects a nonsquare coprime factor in such a call.

The trial-prime list is bounded by $2H^2$. The code reuses the [lattice sieve](cogentic-monic-lattice-sieve.md) for the finite-field roots and visits, and it does not factor the discriminant or the unfactored tails. The polynomial bit work in the box size, prime bound, and explicit field size has the same $\exp(O(W))$ bound when $H\le\exp(O(W))$. The supported nonsquare atoms in the second stage use at most as many independent rational valuation rows as there are distinct primes dividing $2D$, plus one sign row. The code still pays to construct the selected products and exact roots.

## Replay

Run `python3 -B experiments/cogentic-quadratic-supported-kernel.py`. It retains only primitive marks whose images are units modulo the input and includes the common sign generator. On the first four grids it checked exact equality of the full solution spaces against the unrestricted quadratic kernel. On the largest grid it verified every returned exact root. Figures below are from one local run. Scalar bits sum the numerator and denominator bit lengths before and after support stripping.

| Input | Height | Marks | First-kernel dimension | Square nullity | Scalar bits before / after | Unrestricted / supported seconds |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 77 | 12 | 149 | 60 | 58 | 792 / 470 | 0.014 / 0.037 |
| 221 | 16 | 270 | 110 | 107 | 2,464 / 1,247 | 0.047 / 0.043 |
| 895 | 24 | 590 | 256 | 254 | 7,033 / 2,823 | 0.313 / 0.063 |
| 10403 | 32 | 1,293 | 451 | 449 | 21,880 / 4,249 | 2.749 / 0.115 |
| 895 | 64 | 4,162 | 2,270 | 2,268 | 133,105 / 34,765 | omitted / 0.512 |

On the centered $895$ height-24 grid, the packed rational norm stage gave dimension 405 in a separate comparison. Its unrestricted descent and second binary kernel took about 0.225 seconds. The ideal rows and support reduction brought the first dimension to 256 and the resulting square nullity remained 254. The supported first stage took about 0.033 seconds and its descent and second kernel took about 0.012 seconds. These are arithmetic checks for one quadratic field. They do not establish how many of the square words give productive modular signs on arbitrary inputs.
