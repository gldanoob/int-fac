# Splitting with one multiple of a cubic torus order

Write $H_t=\Phi_3(t)=t^2+t+1$. A positive multiple of $H_p$ at one unknown prime divisor $p$ gives a deterministic split under the following congruence hypotheses. The proof uses the scalar norm at the prime $3$. The local group calculation below identifies exactly which part of the order the scalar norm can control.

## The fixed-field splitting theorem

Assume Dirichlet GRH. Let $N,M$ be positive integers. Suppose $N$ has distinct prime divisors $p,q$ such that

- $H_p\mid M$,
- $p\bmod 7\in\{2,3,4,5\}$, and
- at least one of $p,q$ is $1\bmod 3$.

Given only $N,M$ in binary, a deterministic algorithm returns a divisor $g$ with $1<g<N$ in time polynomial in $\log N+\log M$. The theorem allows repeated prime factors in $N$, arbitrary extra factors in $M$, and either splitting type at an unramified $q$. It guarantees one proper split. Complete factorization by recursion would require a splitting guarantee for each remaining composite cofactor.

If $2$, $3$, or $7$ divides $N$, trial division already gives a proper factor. In the proof below take $\gcd(N,42)=1$.

## What the scalar norm controls

At a prime $t$ inert in a cubic field, the projective group $P_t=\mathbb F_{t^3}^{\times}/\mathbb F_t^\times$ is cyclic of order $H_t$. The map $[\alpha]\mapsto\alpha^{t-1}$ identifies it with the norm-one torus. If $g$ generates $\mathbb F_{t^3}^\times$ and $\alpha=g^a$, then

$$
\operatorname{ord}([\alpha])=\frac{H_t}{\gcd(H_t,a)},\qquad
\operatorname{Nm}(\alpha)=(g^{H_t})^a,\qquad
\gcd(H_t,t-1)=\gcd(3,t-1).
$$

The exact norm fixes $a\bmod(t-1)$. For any prime $s\ne3$ dividing $H_t$, CRT still allows every value of $a\bmod s^{v_s(H_t)}$ in that norm fiber. Both trivial and full $s$-primary order occur. In particular $H_t$ is odd, so a quadratic character cannot distinguish two such components by their $2$-parts. No fixed finite list of candidate primes always meets $H_t$: Dirichlet's theorem gives primes $t$ congruent to $-1$ modulo their product, for which $H_t$ is $1$ modulo every prime on the list.

If $t\equiv1\bmod3$, substitution of $t=1+3k$ gives $H_t\equiv3\bmod9$. Since $g^{H_t}$ generates $\mathbb F_t^\times$, the projective order is divisible by $3$ exactly when $\operatorname{Nm}(\alpha)$ is a noncube modulo $t$. If $t\equiv2\bmod3$, then $3\nmid H_t$. At a completely split prime the projective unit group is $(\mathbb F_t^\times)^3/\mathbb F_t^\times$ with diagonal scalars, of order $(t-1)^2$. Thus at $t\equiv2\bmod3$ both unramified splitting types in a cyclic cubic field have projective order prime to $3$.

## The field and the witnesses

Take $K=\mathbb Q(\zeta_7)^+$ with integral basis $1,\theta,\theta^2$, where $f(\theta)=0$ for $f(X)=X^3-X^2-2X+1$. This totally real cyclic cubic field has discriminant $49$. The Frobenius of $t\ne7$ is the class of $t$ in $(\mathbb Z/7)^\times/\{\pm1\}$. Thus $t\equiv\pm1\bmod7$ splits completely, and $t\equiv\pm2,\pm3\bmod7$ is inert. In particular the covered prime $p$ is inert. [LMFDB field data, including discriminant and power-basis index](https://www.lmfdb.org/NumberField/data/3.3.49.1)

Use a prime $r\equiv1\bmod7$ coprime to $N$. When $q\equiv1\bmod3$, prescribe $r$ to be a noncube at $q$ and, if $p\equiv1\bmod3$, a cube at $p$. When $q\equiv2\bmod3$, the hypothesis gives $p\equiv1\bmod3$; prescribe $r$ to be a noncube at $p$. To impose a noncube, choose one of the two nontrivial values of a cubic Dirichlet character at that prime. These are consistent conditions on distinct prime components. In either case CRT gives a nonempty coset of index at most $6\cdot3\cdot3=54$ modulo $7N$. The least-prime-in-a-coset bound gives an effective $r=O((\log(7N))^2)$ under Dirichlet GRH. The conditions at the unknown $p,q$ are used only to prove existence. The algorithm enumerates the small primes $r\equiv1\bmod7$ coprime to $N$. [Lamzouri–Li–Soundararajan, Theorem 1.4](https://arxiv.org/pdf/1309.3595#page=3)

For each such $r$, an element $\alpha$ of norm $r$ can be found by a small coefficient search. To see the bound, take a prime ideal above $r$ of norm $r$. In the three real embeddings its lattice has covolume $7r$. The ball $\sum_i|x_i|\le R$ with $R^3=48r$ has volume $8R^3/6>8\cdot7r$. Minkowski's theorem gives a nonzero element in the ball. Its absolute norm is a positive multiple of $r$ and is at most $(R/3)^3<2r$, hence equals $r$. Change its sign if necessary. The roots of $f$ lie in $(-2,-1),(0,1),(1,2)$. The power-basis embedding matrix has entries of absolute value at most $4$ and determinant of absolute value $7$, so every inverse entry has absolute value at most $32/7$. Each integral coefficient of the resulting element is bounded by $(32/7)R<17r^{1/3}$. Enumerating that box and testing the norm takes polynomial time in $\log N$. Any element of norm $r$ works for the prescribed local conditions.

## The two gcd tests

Put $d=M/3^{v_3(M)}$. For $e=d,M$, compute $\alpha^e=A_e+B_e\theta+C_e\theta^2$ in $\mathcal O_K/N\mathcal O_K$ and return any proper factor among

$$
G(e)=\gcd(N,B_e,C_e).
$$

For each $t\mid N$ prime, $\alpha$ is a unit modulo $t$ because its norm is coprime to $N$. The integral basis shows that $t\mid G(e)$ exactly when $\alpha^e$ is scalar modulo $t$, or equivalently when $[\alpha]^e=1$ in the projective group. The algorithm runs both tests for each candidate without knowing which case applies.

- **If $q\equiv1\bmod3$**, the projective order at $p$ divides $H_p$ and is prime to $3$, by the cube prescription when needed. It divides $d$. At $q$, a scalar equality $\alpha^d=c$ would imply $r^d=c^3$ by taking norms, impossible since $r$ is a noncube and $3\nmid d$. This argument also holds when $q$ splits. Hence $p\mid G(d)$ and $q\nmid G(d)$.
- **If $q\equiv2\bmod3$**, the prescribed noncube at $p$ makes the projective order there divisible by $3$. Therefore $p\mid G(M)$ and $p\nmid G(d)$. If $q\nmid G(M)$, the endpoint $G(M)$ splits $N$. Otherwise the projective order at $q$ divides $M$. It is prime to $3$ whether $q$ splits or is inert, so it divides $d$. Now $q\mid G(d)$ and $p\nmid G(d)$.

The fixed rank of the ring gives polynomial bit cost for the modular powers and gcds. Removing powers of $3$ is the only decomposition of $M$ used.

## Scope of the obstruction

Even a common exponent may return the whole modulus at the endpoint. Both $5$ and $17$ are inert in $K$. For $N=85$ and $M=H_5H_{17}=31\cdot307$, one has $\gcd(M,N)=1$, whereas $G(M)=85$ for every $\alpha$ of norm coprime to $85$. A gcd detects a difference in local scalar behavior once a witness supplies it. The norm-fiber argument explains why a prescribed scalar norm cannot force that difference at any $s\ne3$ through two inert components.

Bach–Shallit give a randomized cyclotomic factoring algorithm with a supplied multiple of $\Phi_k(p)$. Their useful-conductor argument for $k=3$ involves whether the hidden $p$ is a cube modulo a varying conductor prime, a splitting condition in $\mathbb Q(\zeta_3,\sqrt[3]{p})$. The fixed-index Dirichlet argument above instead varies $r$ against fixed characters modulo $p,q$. Źrałek's deterministic Theorem 5.5 assumes a fixed cyclic field, inertness at the covered prime, and smoothness of the cyclotomic value. For a general unfactored $H_p$ multiple, choosing the field and finding a separating witness beyond the stated congruences remain unresolved by this argument. [Bach–Shallit, §§7–8](https://doi.org/10.1090/S0025-5718-1989-0947467-1) · [Źrałek, Theorem 5.5](https://arxiv.org/pdf/0707.4102#page=11)

## Varying the conductor

The [fixed-index cyclotomic theorem](cyclotomic-order-multiples.md) now supplies the conductor and a bounded witness for all pairs of primes using a uniform Dedekind zero-free strip. The following discussion records the original proof obligations.

One way to separate two primes that are both $2\bmod3$ would be to choose a cyclic cubic field $K$ in which $p$ is inert and $q$ splits. The projective order at $p$ is odd. At $q$ a unit whose three components have mixed quadratic characters has even projective order. Testing the odd part of $M$ already separates them, as long as such a unit can be constructed. For cubic conductor $\ell$, the desired Frobenius conditions concern the Kummer compositum $\mathbb Q(\zeta_3,\sqrt[3]p,\sqrt[3]q)$, of bounded degree. Bach–Shallit use this type of conductor selection. The reported uniform zero-free strip for Dedekind zeta functions and finite-order Hecke characters suggests a way to bound the prime and witness searches. [Bach–Shallit, §§6–7](https://www.ams.org/journals/mcom/1989-52-185/S0025-5718-1989-0947467-1/S0025-5718-1989-0947467-1.pdf) · [Cureton–Thorner, Theorem 1.1 and Corollary 1.2](https://hexagonmath.org/pdf/2610.00200v2#page=3)

For the second search, the quotient of two component Legendre symbols is a nontrivial character on residue units at the split prime. A full generating set of residue units would necessarily contain a separating witness. One possible construction would lift small prime-ideal generators of the ray class group, enumerate relations in the ordinary ideal class group, and include the images of global units. To turn this into a time bound one needs uniform estimates for the varying conductor, uniform bit complexity for computing generators of principal ideals and units in the varying cubic field, and a search executable without knowing either prime. The fixed-field theorem above avoids all three requirements; the subsequent proof handles them by showing that an exhaustive polynomial search contains a witness.

## One fixed witness for three quarters of the split primes

Fix this conductor-seven field and take $\alpha=3+\theta$, of norm $29$. For any fixed inert prime $p\ne 29$, let $q$ vary over primes that split completely in $K$. A relative density $3/4$ of those $q$ give $\alpha$ mixed quadratic signs in the three components modulo $q$. For every such $q$ and every positive multiple $M$ of $H_p$, the single gcd $G(M/2^{v_2(M)})$ splits $pq$. Indeed $H_p$ is odd, so the power is scalar at $p$. Raising to an odd power preserves the mixed signs at $q$, which preclude a scalar. Here density refers to the limit as $q$ varies for a fixed field and element. It supplies no guarantee for a specified split $q$.

To compute the density, let $\alpha_1,\alpha_2,\alpha_3$ be the Galois conjugates of $\alpha$. Its principal ideal is a prime of norm $29$. Since $29\equiv1\bmod 7$, its three conjugates are the distinct primes of $K$ over $29$. Valuation modulo two at these primes gives the three coordinate vectors, proving that the $\alpha_i$ are independent in $K^\times/K^{\times2}$. Thus $L=K(\sqrt{\alpha_1},\sqrt{\alpha_2},\sqrt{\alpha_3})$ is Galois over $\mathbb Q$ with $\operatorname{Gal}(L/K)\cong\{\pm1\}^3$. At an unramified split $q$ away from $2\cdot29$, the three residue signs are the Frobenius sign vector at a prime over $q$, up to permutation. Mixed signs form a union of conjugacy classes of size six in the subgroup of size eight. Chebotarev gives relative density $6/8$ among split primes, or density $1/4$ among all rational primes.

The same argument gives mixed signs at relative density $1-2^{1-k}$ for any fixed Galois field of degree $k\ge2$. Choose an auxiliary rational prime splitting completely and, by the ideal Chinese remainder theorem, an integral element of valuation exactly one at one prime above it and zero at every other. The $k$ conjugates then have independent square classes. Of the $2^k$ sign vectors, only the two constant vectors lack mixed signs. The cubic factoring assertion uses in addition the odd projective exponent $H_p$ at the fixed inert prime.

## PARI/GP replay

From the repository root, extract the GP block and run it directly.

~~~sh
awk '/^~~~gp$/ {body=1; next} /^~~~$/ {body=0} body' research/cubic-order-multiples.md | gp -q -f
~~~

The fixture uses $\alpha=3+\theta$ of norm $29$. It checks the forward split at $N=65$, both reverse gcd outcomes at $p=19$ with $q=5$ inert and $q=41$ split, and the common-exponent obstruction at $N=85$. Inflating $M$ in the reverse cases also exercises removal of multiple powers of $3$.

~~~gp
f = x^3 - x^2 - 2*x + 1;
H(t) = t^2 + t + 1;
{
powerpoly(n, e) =
  my(a = Mod(Mod(1,n)*(x+3), f));
  return(liftall(a^e));
}
{
scalargcd(n, e) =
  my(a = powerpoly(n,e));
  return(gcd(n,gcd(polcoef(a,1),polcoef(a,2))));
}
{
checkfixture() =
  my(m, d, q);
  if(poldisc(f) != 49 || polresultant(f,x+3) != 29, error("field or norm"));
  if(Mod(29,13)^4 == 1 || Mod(29,19)^6 == 1, error("expected noncubes"));
  m = 3*H(5);
  d = m/3^valuation(m,3);
  if(powerpoly(65,d) != 9+55*x+45*x^2 || scalargcd(65,d) != 5, error("forward"));
  for(i=1,2,
    q = [5,41][i];
    m = H(19);
    if(scalargcd(19*q,m) != 19, error("reverse endpoint at q=",q));
    m *= 9*if(q==5,H(q),q-1);
    d = m/3^valuation(m,3);
    if(scalargcd(19*q,m) != 19*q || scalargcd(19*q,d) != q,
      error("reverse stripped exponent at q=",q));
  );
  m = H(5)*H(17);
  if(gcd(85,m) != 1 || scalargcd(85,m) != 85, error("common exponent"));
  my(qs=[13,41,197],signs=[[-1,-1,1],[-1,-1,-1],[1,1,1]]);
  for(i=1,#qs,
    q=qs[i];
    my(v=Vec(apply(t->kronecker(lift(t)+3,q),polrootsmod(f,q))));
    if(v!=signs[i],error("conjugate signs at q=",q))
  );
  if(scalargcd(5*13,m)!=5,error("fixed mixed-sign witness"));
  print("OK: forward, reverse (inert and split), common-exponent obstruction");
}
iferr(checkfixture(), err, print(err); quit(1));
~~~
