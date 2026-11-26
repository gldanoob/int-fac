# Square roots of ideals from a maximal order

Given an explicit maximal integral basis of a number field and the lattice of a nonzero integral ideal, one can decide whether the ideal is a square and return its exact square-root ideal in deterministic polynomial bit time. The field degree may vary. The algorithm uses integer lattice arithmetic, integer square roots, and arithmetic at primes no greater than the field degree. The discriminant and the ideal norm may both be unfactored. This generalizes the [cubic different test](cogentic-cubic-different-kernel.md) and provides actual half-ideal lattices for the residual class-group step of the factoring search. An ideal square can have a nonsquare generator. [Adaptive square-kernel recovery](cogentic-adaptive-square-kernel.md)

## A squarefree ideal covering all ramified rational primes

Write $B=\mathcal O_K$, $d=[K:\mathbb Q]$, and let $\mathfrak D=(B:B^\vee)$ be the different, with $B^\vee$ the trace dual. All three lattices are available from the multiplication table and the inverse trace matrix. Let $s$ be the largest Smith invariant of $B/\mathfrak D$, the exponent of its additive group. Locally $v_p(s)=\max_{\mathfrak p\mid p}\lceil v_{\mathfrak p}(\mathfrak D)/e_{\mathfrak p}\rceil$, since $s$ is the least positive integer with $sB\subseteq\mathfrak D$.

For $p>d$ every branch is tame. The local different exponent is $e_{\mathfrak p}-1$. Therefore $v_p(s)$ is one if some branch ramifies and zero otherwise. Divide $s$ by every prime power with prime at most $d$ by bounded trial division and call the result $r$. It is the squarefree product of all ramified rational primes above $d$, with no need to separate them. Then
\[
 J_{\rm large}= (rB):(\mathfrak D+rB)
\]
is exactly $\sqrt{rB}$. At $p\mid r$ the numerator exponent $e_{\mathfrak p}$ exceeds the denominator exponent $e_{\mathfrak p}-1$ by one, including at unramified companions. All other exponents vanish. The tame different formula holds without a Galois hypothesis. [Sutherland, Theorem 12.27](https://math.mit.edu/classes/18.785/2021fa/LectureNotes12.pdf#page=10)

For each $p\le d$ dividing $s$, compute the kernel of $x\mapsto x^{p^j}$ in $B/pB$, with $p^j\ge d$. This $\mathbb F_p$-linear map kills every nilpotent because the nilpotence index is at most the dimension $d$, and a nonzero element of a residual field survives. The kernel lifts to $\sqrt{pB}$ by adjoining $pB$ to integer lifts of its vectors. Multiply these small radicals and $J_{\rm large}$ to get $J$. Its nonzero valuations are all one, at **every** prime ideal lying over a ramified rational prime. This covers both wild branches and unramified companions without decomposing any unnamed prime. For degree one and an empty ramification set the product is the unit ideal.

## Extracting the ideal root

Start with $A=I$, $H=B$. Compute the ideal sum $L=A+J$. If $L\ne B$, divide $A$ by $L$ by an exact ideal quotient. Set $L'=A+J$ on the new remainder. If $L'\ne L$, a branch of original odd valuation has lost its last factor in the first half of this pair. Return nonsquare. Otherwise multiply $H$ by $L$, divide $A$ once more by $L$, and repeat. In each pair the two layers contain exactly the branches with remaining valuation at least one and at least two. The procedure stops after at most $1+\log_2\mathrm N I$ layers. At $L=B$, $H$ is the root on the support above ramified rational primes and $A$ is the unramified remainder.

In the supplied order basis use ideal lattice columns and compute Smith form $UAV=\operatorname{diag}(s_i)$. At each rational prime in the support of $A$, $p$ is a uniformizer in every branch. A local ideal exponent $a$ at residue degree $f$ therefore contributes $f$ copies of $a$ among the $p$-exponents of the Smith invariants, including zero entries. The remainder is a square exactly when each $s_i$ is a square integer. In that case an actual root lattice for the remainder is
\[
 U^{-1}\operatorname{diag}(\sqrt{s_i})\mathbb Z^d.
\]

To verify this formula, work over $\mathbb Z_p$. There is a branch-adapted basis of $B\otimes\mathbb Z_p$ in which $A$ is diagonal with entries $p^{a_i}$ and the true root uses $p^{a_i/2}$. Sort the local exponents in the Smith ordering. A transition matrix $T$ between two such diagonalizing bases preserves the ambient lattice and the lattice with diagonal $p^{a_i}$. Thus $v_p(T_{ij})\ge\max(0,a_i-a_j)$, with the same bound for entries of $T^{-1}$. These inequalities imply preservation of the lattice with diagonal $p^{a_i/2}$. The computed Smith basis therefore recovers the true half-lattice at every $p$. Multiplying by $H$ gives the desired ideal. The implementation also squares it and compares the resulting HNF with the input.

All sums, products and exact quotients of integral ideals use Hermite forms and the supplied multiplication matrices. For the trace dual and ideal quotients one solves linear lattice membership conditions. The determinant bounds for the different and input bound the intermediate ideal lattices and their bit lengths. The Smith form with unimodular transformations can be computed with polynomial bit complexity, and matrix sizes and the number of layers are polynomial in the explicit input length. The supplied basis is an input hypothesis. Closure and a unit are checked by the implementation, while finding or proving maximality remains a distinct task.

For a list of marked elements, clear coordinate denominators by rational squares and refine their principal ideals into pairwise coprime ideal atoms by repeated sums and exact quotients. Each nonsquare atom contributes its exponent-parity row; a square atom contributes zero. The displayed single-ideal procedure supplies this decision in any degree. Already computed half-ideals are exact witnesses for ideal parity. A field square must still clear global unit and class-group obstructions before its reduction can yield a factor. [Gcd-free ideal matrix](cogentic-cubic-square-resolvent.md#fixed-field-algorithm-using-ideal-lattices)

## Executable checks

From `experiments`, load `cogentic-order-lattices.gp` in PARI/GP. Use `data=order_square_data(P,basis)` once for a monic irreducible polynomial and a supplied maximal basis in its power coordinates. Then `order_ideal_square_root(data,A)` returns either the root as an ideal HNF in that same basis or zero for a nonsquare. The input is a full nonsingular integral ideal matrix. All field-specific preparation is reusable. [Implementation](../experiments/cogentic-order-lattices.gp)

The independent fixture constructs ideals from explicit PARI prime-ideal decompositions solely for comparison. It compares the returned root lattice or nonsquare decision on 804 exponent arrays in degrees two through six. These include a biquadratic field with two ramified branches over the same large rational prime. A separate 150-bit composite tame support is tested from a supplied quadratic basis, with different valuations at its two hidden primes. [Replay](../experiments/cogentic-maximal-ideal-roots.gp)
