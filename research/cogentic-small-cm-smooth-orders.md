# Smooth-order limits for elliptic curves with small CM discriminants

Fix \(b>0\), put \(L=\log X\), and set
\[
 W=L^{1/3}(\log L)^{2/3},\qquad
 V=L^{2/3}(\log L)^{1/3},\qquad
 B=\exp(bW).
\]
For a positive integer \(n\), let \(n_{\le B}\) be its full divisor supported on primes at most \(B\). For any fixed \(z\ge 0\), outside \(o(X/\log X)\) primes \(p\in[X,2X]\), every ordinary \(E/\mathbb F_p\) with \(|\operatorname{disc}\mathbb Q(\pi_E)|\le\exp(zW)\) has
\[
       \bigl(\#E(\mathbb F_p)\bigr)_{\le B}
                 \le \exp(C_{b,z}V).
\]
The same conclusion includes every supersingular elliptic curve and, with a change of constant, every supersingular abelian surface and every abelian surface isogenous **over \(\mathbb F_p\)** to a product of two eligible elliptic curves. The bounds are unconditional. In particular the allowed curves, twists, and discriminants may all be selected after seeing an input integer. [Earlier result for the thirteen rational CM invariants](rational-cm-obstruction.md)

## Counting all ordinary orders

For an ordinary elliptic curve over \(\mathbb F_p\), the Frobenius \(\pi\) belongs to the maximal order of its imaginary quadratic field \(K=\mathbb Q(\pi)\), and
\[
         \operatorname{Nm}(\pi)=p,\qquad
         \operatorname{Nm}(1-\pi)=p+1-\operatorname{Tr}(\pi)
                             =\#E(\mathbb F_p).
\]
The characteristic polynomial has trace \(t\) with \(|t|\le2\sqrt p\) and satisfies \(t^2-4p=f^2\operatorname{disc}(K)\) for the index \(f=[\mathcal O_K:\mathbb Z[\pi]]\). Thus a fixed field allows at most six traces at \(p\): when \(p\) splits, \((\pi)\) must be one of the two primes over \(p\), and its generators differ by the at most six units. More precisely this gives at most twelve possible \(\pi\), with conjugate pairs having the same trace. Ramified or inert \(p\) cannot be the reduction prime of an ordinary curve with this Frobenius field. The count below fixes the **order** instead of the prime and uses the maximal order, so a varying conductor imposes no additional cost. For an ordinary reduction of a characteristic-zero CM curve, the CM field is the ordinary endomorphism field and therefore equals \(\mathbb Q(\pi)\). [Sutherland, ordinary and supersingular curves](https://math.mit.edu/classes/18.783/2021/LectureNotes13.pdf) · [Sutherland, ring class fields and ordinary CM reduction](https://math.mit.edu/classes/18.783/2022/LectureNotes21.pdf)

For each \(K\) and integer \(n>0\), there are at most \(6\tau(n)\) elements \(\beta\in\mathcal O_K\) of norm \(n\). An ideal of norm \(\ell^a\) has at most \(a+1\) choices when \(\ell\) splits and at most one when it ramifies or is inert. A principal ideal has at most six generators. Each \(\beta=1-\pi\) specifies a single \(p=\operatorname{Nm}(1-\beta)\), so this bounds the possible primes for the order \(n\), including all charts and twists.

Let \(Z\ge1\), \(H\ge1\), and \(0<\delta\le1/4\). If \(n_{\le B}\ge H\), some \(B\)-smooth integer \(d\ge H\) divides \(n\). Since \(n\le3X\) for large \(X\), using \(\tau(dm)\le\tau(d)\tau(m)\) gives
\[
 \sum_{\substack{n\le3X\\ n_{\le B}\ge H}}\tau(n)
   \ll X\log X\sum_{\substack{d\ge H\\d\ B\text{-smooth}}}
                         \frac{\tau(d)}d
   \le X\log X\, H^{-\delta}
                 \prod_{\ell\le B}(1-\ell^{-1+\delta})^{-2},
\]
where the product runs over primes. Its logarithm is \(O(B^\delta\log\log(3B))\) by the reciprocal-prime bound. The number of ordinary reduction primes in the exceptional set is consequently at most
\[
 O\!\left(ZX\log X\,H^{-\delta}
                    \exp(O(B^\delta\log\log(3B)))\right).
\]
Here \(O(Z)\) is simply the number of fundamental discriminants under consideration. The estimate counts all possible local orders before any model or point is chosen. For the claimed \(Z=\exp(zW)\), use \(\delta=(\log L)/(4\log B)\) and \(H=\exp(C_{b,z}V)\). The Euler product then has logarithm \(o(W)\), whereas \(\delta\log H=C_{b,z}W/(4b)\). A sufficiently large constant makes the exceptional proportion tend to zero.

For the stronger requirement that the full order have \(B\)-smooth part with complementary factor at most \(\exp(O(W))\), one can take \(H=X\exp(-O(W))\) by the Hasse lower bound. Take \(\delta=((2/3)\log L-2\log\log L)/\log B\). The exceptional proportion for ordinary curves is then at most
\[
         Z\exp\!\left(-\bigl(2/(3b)-o(1)\bigr)V\right).
\]
In particular, searching all fundamental discriminants up to \(\exp(o(V))\) cannot supply such an ordinary group order for most primes. Restricting the catalog to any ramification pattern, twist class, or ring class polynomial only reduces the set of attainable orders.

## Supersingular elliptic curves and abelian surfaces

Write \(P_p(S)\) for the characteristic polynomial of Frobenius. For a supersingular abelian variety over \(\mathbb F_p\), all roots have \(p\)-adic valuation \(1/2\); each is \(\sqrt p\) times a root of unity. The \(k\)-th elementary symmetric coefficient, being an integer, is therefore divisible by \(p^{\lceil k/2\rceil}\). In dimension one the trace vanishes for \(p>4\), since it is divisible by \(p\) and of absolute value at most \(2\sqrt p\). Thus all supersingular elliptic orders are \(p+1\). The preceding bound applies to these orders by counting each \(n=p+1\) at most once, so replacing \(Z\) by \(Z+1\) includes this case and gives the same bound on nearly smooth full orders. [Zhu, Frobenius roots of supersingular abelian varieties](https://www.nsm.buffalo.edu/~hjzhu/Papers/paper2.pdf)

In dimension two write
\[
          P_p(S)=S^4+a_1S^3+a_2S^2+pa_1S+p^2 .
\]
For \(p>16\), divisibility by \(p\) and \(|a_1|\le4\sqrt p\) give \(a_1=0\). Divisibility by \(p\) and \(|a_2|\le6p\) give \(a_2=cp\) for an integer \(|c|\le6\). Hence the order \(P_p(1)\) is \(p^2+cp+1\) from a fixed list. For \(c=\pm2\), this is \((p\pm1)^2\). Apply the shifted-integer count used for \(p+1\) to both signs before squaring.

For each other \(c\), let \(\rho_c(d)\) be the number of roots of \(S^2+cS+1\bmod d\). Then \(\rho_c(d)\ll_c\tau(d)\). At primes outside \(2(c^2-4)\), this follows by simple-root lifting. At a prime dividing \(2(c^2-4)\), the number of roots modulo \(\ell^a\) is bounded independently of \(a\). Indeed \((2S+c)^2\equiv c^2-4\bmod\ell^a\), the right side is fixed and nonzero, and once \(a>v_\ell(c^2-4)\) a solution has prescribed valuation. The remaining unit square-root congruence has at most two roots for odd \(\ell\) and four for \(\ell=2\) up to the bounded factor from the removed valuation and the map \(S\mapsto2S+c\). Multiplication over primes gives the claimed root bound.

If the smooth part of \(p^2+cp+1\) reaches \(H\), multiplication by its prime factors one at a time gives a smooth divisor \(d\in[H,HB]\). Counting all integers \(p\in[X,2X]\) in the root classes yields
\[
 \sum_{\substack{H\le d\le HB\\d\ B\text{-smooth}}}
                 \rho_c(d)(X/d+1)
 \ll_c X H^{-\delta}\exp(O(B^\delta\log\log(3B)))
              + HB\log(2HB).
\]
For \(H=\exp(C_{b,z}V)\), this is \(o(X/\log X)\) with the same choice of \(\delta\). The sum over the fixed list of polynomials gives the claim for all supersingular abelian surfaces. For an abelian surface isogenous over \(\mathbb F_p\) to an eligible elliptic product, its order is the product of the two elliptic orders, so their two bounds multiply. This product argument requires the isogeny over the base field.

## Point orders and the factoring criterion

For a balanced semiprime with both factors in this density-one set, let \(G=A(\mathbb F_p)\) for any of the eligible curves or surfaces at one factor. A scalar \(M\) made from a \(B\)-smooth multiplier and a remaining multiplier at most \(\exp(O(W))\) satisfies
\[
       \gcd(M,\#G)\le (\#G)_{\le B}\exp(O(W))=X^{o(1)}.
\]
Its identity kernel is contained in the torsion of order dividing \(\gcd(M,\#G)\) and hence has size \(X^{o(1)}\), since an abelian variety of dimension \(g\) has at most \(d^{2g}\) geometric \(d\)-torsion points. In particular a uniform local point lands in the kernel with probability at most \(X^{-g+o(1)}\), even on a curve chosen using the input. The same bound applies per trial if the point is conditionally uniform once the curve and scalar are fixed. A specially selected point can still lie in the small torsion subgroup. The count gives no distribution estimate for points created from the input by a deterministic formula.

Thus CRT interpolation among small CM discriminants cannot force a smooth **group** order at either hidden prime for most balanced inputs. A method using exceptional points would require a separate argument producing or exposing their small torsion. The obstruction leaves unrestricted ordinary elliptic Frobenius fields and ordinary simple genus-two Jacobians outside its scope.
