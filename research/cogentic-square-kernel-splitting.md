# A basis test for simultaneous square relations

Let $N>1$ be odd and put $R=\mathbb Z/N\mathbb Z$. For each of two number fields, work in a subring $A_i$ with a specified reduction $\rho_i:A_i\to R$. For example, a common polynomial root defines a map on each power order, which extends to its localization at the elements whose residues are units. Use these localizations so that every element with a unit residue is invertible in $A_i$. A root of a relation must belong to the chosen ring or be provided with an expression whose reduction is defined there.

For $1\le j\le k$, suppose column $j$ specifies two elements $u_{ij}\in A_i^\times$ with the same residue. More generally allow different residues and supply a unit $q_j\in R^\times$ satisfying
\[
\rho_1(u_{1j})=q_j^2\rho_2(u_{2j}).
\]
Use $q_j=1$ for an ordinary mark evaluated at the common root, assuming its residue is a unit. This presentation also allows paired unit corrections and one-sided unit corrections whose residue ratios come with explicit square roots.

For $v\in\mathbb F_2^k$, set $U_i(v)=\prod_{j:v_j=1}u_{ij}$. Let $K$ consist of those $v$ for which $U_i(v)=r_i(v)^2$ with $r_i(v)\in A_i$ for both fields. The roots are units because the products are units. Addition of supports gives the exact root formula
\[
r_i(v+w)=\frac{r_i(v)r_i(w)}{\prod_{j:v_j=w_j=1}u_{ij}}.
\]
This is one valid choice of root on the sum, and its division is safe on the selected residue branch. Thus $K$ is a vector space. The square kernel of the fields alone can be used if its roots admit the required reduction. An ideal-parity kernel can be larger because it omits the square-class obstruction from units and other field data.

Define $Q(v)=\prod_{j:v_j=1}q_j$ and write $\mu_2(R)=\{z\in R^\times:z^2=1\}$. The normalized ratio
\[
\chi(v)=\left[\frac{\rho_1(r_1(v))}{\rho_2(r_2(v))Q(v)}\right]
\in \mu_2(R)/\{1,-1\}
\]
is well defined. Its square is one by the column identities. Both possible roots of a nonzero field element differ only by sign, so choosing the other root in either field leaves the class unchanged. In a product of roots, each overlap contributes the residue ratio $q_j^2$ in the division that clears that overlap. Also $Q(v+w)=Q(v)Q(w)/\prod_{j:v_j=w_j=1}q_j^2$. These contributions cancel, proving $\chi(v+w)=\chi(v)\chi(w)$.

The same argument gives an intrinsic value when relation exponents are integers. If the exponent vector is changed by $2t$, multiply the root in each field by $\prod_j u_{ij}^{t_j}$. Its residue ratio changes by $\prod_jq_j^{2t_j}$, exactly the change in $Q$. This also permits negative exponents, using the localization at unit residues.

## Extraction from a supplied basis

Suppose $v_1,\ldots,v_s$ is a basis of $K$ and the two roots for each basis vector are supplied with valid reductions. If any relation in $K$ has a nontrivial class, some basis vector has a nontrivial class by the homomorphism. For that vector output
\[
D=\gcd(A-B,N),\qquad
A=\rho_1(r_1(v_j)),\qquad B=\rho_2(r_2(v_j))Q(v_j).
\]
Here $A$ and $B$ are units and $A^2=B^2$. Since $N$ is odd, each prime power $p^e\parallel N$ divides exactly one of $A-B$ and $A+B$. Indeed their product is zero modulo $p^e$, and a prime dividing both would divide $2A$ and $2B$. A nontrivial class means $A\ne B$ and $A\ne-B$ modulo $N$, so both sides receive some prime-power factors and $1<D<N$. This works with repeated prime factors. For an odd prime power the quotient $\mu_2(R)/\{1,-1\}$ is trivial.

For a fixed affine slice $v_0+L\subseteq K$, test the anchor $v_0$ and the sums $v_0+b_j$ for a basis of $L$. If the anchor is trivial, the classes of these sums are precisely the classes of the directions. Their roots are recovered from the anchor and direction roots by the overlap formula. In the modular certificate the same overlap divisor $\prod_{j:v_j=w_j=1}\rho_1(u_{1j})$ divides both $A(v)A(w)$ and $B(v)B(w)$ as a unit in $R$, so the new certificate can also be formed directly from the residues. This covers a requirement that specific mark coordinates stay fixed while correction coordinates vary.

Once the basis root residues are available, testing costs at most $O(sk)$ modular multiplications and $s$ binary gcd computations on $O(\log N)$-bit numbers. Each $q_j$ can be checked using a square and a modular multiplication against its two column residues, without factoring $N$. A witness consists of the binary basis vector and the two reduced roots $A,B$. The square congruence, proper gcd and exact division by $D$ certify the factor. If roots are given as rational power-basis polynomials with scalar denominators coprime to $N$, Horner evaluation and a modular inverse give the residues at cost polynomial in the input encoding. The same holds for explicit expressions using only operations and divisions with unit reduced denominators.

The basis test needs a spanning set of the simultaneous square relations with roots. A parity basis without these witnesses does not provide one. It also needs the chosen column square roots $q_j$ as data. Replacing such a root by another with a different modular sign class can change $\chi$, so the statement tests one fixed choice of these roots. For example, supplying a nontrivial square root of unity for an equal-residue column already supplies a factor certificate. The proof gives a polynomial extraction step after the input relations are supplied, and leaves relation supply and the growing-degree square-kernel computation open. [Finite example with unit corrections](cogentic-monic-unit-corrections.md)
