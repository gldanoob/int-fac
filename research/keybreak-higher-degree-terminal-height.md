# Terminal polynomial mark heights under the KeyBreak coefficient law

Fix a mark degree \(k\), set \(D=(\log N/\log\log N)^{1/3}\) and \(H=D\log\log N\), and take \(d\sim\delta D\). In the KeyBreak field law, the usual rational and resultant heights hold from below simultaneously over all integer marks of degree \(k\) and coefficient height at most \(\exp(O(H))\). This includes marks selected after seeing the field, with no root separation or balance condition on their coefficients. The claim concerns heights, not smooth-value counts. [KeyBreak §G.2 and equation (G.4)](https://crypto.sjtu.edu.cn/factoring.pdf#page=105) · [Charged terminal comparison](keybreak-higher-degree-terminal-budget.md)

## Rational height

In the source, \(Q\) is a prime in \((3M/4,M]\) and, conditional on \(Q\), \(r\) is uniform over the integers in \((M/2,3M/4]\). Thus \(\log Q=\log M+O(1)\) and \(r/Q\) lies in a bounded real interval. For a homogeneous mark \(P(X,Y)=\sum_{j=0}^k c_jX^jY^{k-j}\) with \(c_k\ne0\), put \(G_k=P(r,Q)=Q^kP(r/Q,1)\). In particular \(G_k\equiv c_k r^k\bmod Q\). The linear convention \(P(X,Y)=aY-b'X\) gives \(G_1=Qa-rb'\); reduction modulo \(N\) evaluates \(P(\theta,1)\) at \(r/Q\) when \(Q\) is a unit. The integer \(G_k\) is not normalized by removing any factor of \(N\).

For a real or complex polynomial \(f\) of degree \(k\) with leading coefficient \(\ell\ne0\), every real \(t\) satisfying \(|f(t)|\le T\) lies within complex distance \((T/|\ell|)^{1/k}\) of a root. The real sublevel set therefore fits inside \(k\) intervals of length \(2(T/|\ell|)^{1/k}\). For \(f=P(X,1)\) its leading coefficient has modulus at least one. For fixed \(P,Q\) this counts \(O_k(M\eta^{1/k}+1)\) integers \(r\) with \(|P(r/Q,1)|\le\eta\). For any fixed \(C_W\), union over the at most \(\exp(((k+1)C_W+o(1))H)\) marks of height at most \(\exp(C_WH)\). Taking \(\eta=\exp(-K H)\) with fixed \(K>k(k+1)C_W\) gives failure probability \(\exp(-\Omega(H))\) and, uniformly on success,
\[
\log |G_k|=k\log M+O_{k,C_W}(H).
\]
For failure \(\exp(-\Omega(DH))\), take \(\eta=\exp(-\epsilon DH)\) for a fixed \(\epsilon>0\), allowing a deficit \(\epsilon DH\) in the height.

## Resultant via one Gaussian line

Conditional on the environment \(Q,r\), the ideal field law has
\[
F_{\rm raw}(X,Y)=F_0(X,Y)+2(QX-rY)R(X,Y),
\]
where the degree-\((d-1)\) form \(R\) has isotropic integer Gaussian coefficients of parameter \(\sigma\), with \(\log\sigma=\Theta(DH)\). The proof uses the binary resultant with nominal degrees. On the continuing paths where \(F_{\rm raw}\) is primitive, this is the field model's actual form. A proper content divisor of \(N=F_{\rm raw}(r,Q)\) already splits \(N\), and the usual coefficient bound excludes content \(N\) for large inputs. The total variation error of the original finite sampler can be added once to the failure probability.

Let \(W_P=\max_j|c_j|\). Inverting the fixed Vandermonde matrix at \(0,1,\ldots,k\) gives \(z\) in this set with \(|P(z,1)|\ge c_k^* W_P\) for a constant \(c_k^*>0\) depending only on \(k\). It is important to allow a linear combination of field coefficient directions. For instance the single monomial \(X^jY^{d-1-j}\) contributes a product of powers of the two endpoint coefficients of \(P\). Both can be small even when an interior coefficient attains \(W_P\). Set \(U=(X-zY)^{d-1}\), with \(\|U\|_2\le(k+1)^{d-1}\).

Condition on a coset of \(\mathbb Z U\) in the coefficient space. The conditional scalar \(t\) in \(R=R_1+tU\) is a shifted discrete Gaussian of parameter \(\sigma/\|U\|_2\) by completing the square. Its point masses are \(O(\|U\|_2/\sigma)\) uniformly in the center, by counting the integers within one parameter of the center. The resultant as a polynomial in \(t\) has degree \(k\) when \(G_k\ne0\); by homogeneity and multiplicativity its leading coefficient has modulus
\[
2^k\, |G_k|\, |P(z,1)|^{d-1}.
\]
The sublevel interval count and the atom bound now give, for \(0<\rho\le1\),
\[
\Pr\left\{|\operatorname{Res}(F_{\rm raw},P)|
 \le \rho\,\frac{2^k |G_k|\, |P(z,1)|^{d-1}\sigma^k}{\|U\|_2^k}
 \ \middle|\ Q,r\right\}
 \ll_k \rho^{1/k}+\frac{\|U\|_2}{\sigma}.
\]
The estimate is uniform in the affine shift \(F_0\) and the Gaussian coset. Conditional on a prescribed full coefficient class modulo \(J\), the same argument on the lines \(\mathbb Z(JU)\) keeps the leading scale and replaces the second error by \(J\|U\|_2/\sigma\). It also holds for any union of these full classes of positive probability, including a root prescription. This conditional claim is for the ideal discrete Gaussian; using total variation after a rare conditioning event would require accounting for its probability.

The line-scale logarithm is \(\log |G_k|+k\log\sigma+(d-1)\log W_P-O_k(d)\), where the bounded loss also includes \(2^k\). Choose \(\rho=\exp(-\epsilon DH)\). A union over the full mark box gives failure \(\exp(-\Omega(DH))\) conditional on an admissible environment with all \(G_k\ne0\). Thus the usual lower leading coefficient is \(kA+\delta v_P\), where \(A=(\log M+\log\sigma)/(DH)\) and \(v_P=\log W_P/H\), in the sense of an arbitrarily small fixed deficit with high probability. This matches the ordinary Mahler upper ledger when the field coefficients have height \(\exp((A+o(1))DH)\). A physically shorter mark costs only its actual \(v_P\). The bound provides no smoothness density or pointwise count of proposals at an incoming root.
