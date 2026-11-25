# A ring class polynomial that selects the primes 11 modulo 12

Let $X\ge5$ and let $j\ge2$ be the first integer with $(j+1)2^{-j/2}<1/(4X)$. Write $H_D$ for the monic ring class polynomial of discriminant $D$. The single nonzero integer

$$
                       U_j=H_{-3\cdot4^j}(1728)
$$

satisfies, simultaneously at **every** prime $3<p\le X$,

$$
                         p\mid U_j\quad\Longleftrightarrow\quad p\equiv11\pmod {12}.
$$

The result uses unconditional theorems on ordinary and supersingular reduction and on the spectrum of supersingular isogeny graphs. It gives a public arithmetic target for worst-case factoring. Producing its residue modulo an input integer in subexponential time remains open here. The literature gives algorithms to construct class polynomials, including modulo an arbitrary integer, and theorems on the prime factorization of differences of singular moduli. [Sutherland, class polynomials modulo an integer](https://arxiv.org/abs/0903.2785) · [Lauter–Viray, arbitrary discriminants](https://arxiv.org/abs/1206.6942)

## Two distinct CM fields

Take different imaginary quadratic fields with fundamental discriminants $D_1,D_2$, and fix a prime $\ell$. Write $\Phi_m(A,B)$ for the symmetric classical modular polynomial for cyclic isogenies of degree $m$. The integer

$$
 V_j(D_1,D_2)=
     \prod_{H_{D_1}(a)=0}\prod_{H_{D_2}(b)=0}\Phi_{\ell^j}(a,b)
$$

is nonzero since isogenous complex elliptic curves have isomorphic rational endomorphism algebras. It is integral by symmetry and integrality of singular moduli. For a prime $p\ge5$ not dividing $\ell D_1D_2$, it can vanish modulo $p$ only if $p$ is inert in both fields. If one field splits, its curves reduce to ordinary curves with that same endomorphism algebra. The other curves are supersingular or ordinary with a different endomorphism algebra. No pair of these reductions is isogenous. If both fields are inert, every reduction is supersingular. This argument permits repeated roots of the class polynomials modulo $p$. [CM reduction and horizontal isogenies](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec22.pdf) · [The modular equation in characteristic coprime to its level](https://msp.org/obs/2013/1-1/obs-v1-n1-p26-p.pdf)

There is a single depth $j=2\log_\ell X+O_\ell(\log\log(3X))$ that suffices at all the simultaneously inert primes $p\le X$. For fixed $p$ let $B$ be the adjacency matrix on geometric supersingular $j$-invariants, counting each cyclic subgroup kernel separately. Its row sum is $\ell+1$. Dual isogenies give reversibility for stationary weights $\pi_E$ proportional to $1/|\operatorname{Aut}(E)|$. For $p\ge5$ the automorphism orders lie between two and six and there are $\lfloor p/12\rfloor+O(1)\le p$ vertices, hence $\min_E\pi_E\ge1/(3p)$. The Brandt matrix spectrum off its simple constant eigenspace lies in $[-2\sqrt\ell,2\sqrt\ell]$. This formulation allows the unequal directed multiplicities at $0$ and $1728$. [Jao–Miller–Venkatesan, supersingular Brandt operator](https://djao.math.uwaterloo.ca/wiki/images/9/91/Asiacrypt-2005.pdf) · [Charles–Goren–Lauter, connectivity and Ramanujan estimate](https://www.math.mcgill.ca/goren/PAPERSpublic/FinalRamanujan.pdf) · [Supersingular vertex count and multiplicities](https://bpb-us-e1.wpmucdn.com/sites.psu.edu/dist/a/166357/files/2023/06/cycles.pdf)

Let $C_j$ count cyclic $\ell^j$-isogeny kernels. Excluding immediate dual steps gives

$$
 C_0=I,\quad C_1=B,\quad C_2=B^2-(\ell+1)I,\qquad
 C_{j+1}=BC_j-\ell C_{j-1}\quad(j\ge2).
$$

For length two there are $\ell+1$ ways to take an edge and immediately undo it. For a fixed cyclic length $j-1\ge1$ prefix there are $\ell$ permissible outgoing edges before the final undo. A chain without such a reversal has cyclic kernel. The row sum is $c_j=(\ell+1)\ell^{j-1}$ for $j\ge1$. On a nonconstant eigenvector of eigenvalue $\lambda$ the eigenvalue of $C_j$ for $j\ge2$ is

$$
 \ell^{j/2}\left(U_j^*\!\left(\frac{\lambda}{2\sqrt\ell}\right)-
             \ell^{-1}U_{j-2}^*\!\left(\frac{\lambda}{2\sqrt\ell}\right)\right),
$$

where $U_k^*$ denotes the Chebyshev polynomial of the second kind. Its absolute value on $[-1,1]$ is at most $k+1$. Thus $C_j/c_j$ has nonconstant operator norm at most $(j+1)\ell^{-j/2}$ in $L^2(\pi)$. For vertices $v,w$ the error of the normalized matrix entry from $\pi_w$ is at most this norm times $\sqrt{\pi_w/\pi_v}$, by testing against the point indicators. If $(j+1)\ell^{-j/2}<1/(4X)$, every entry is positive for every $p\le X$. In particular every pair of CM reductions is linked by a cyclic isogeny of precisely this degree, so $p\mid V_j(D_1,D_2)$.

For $D_1=-3,D_2=-4,\ell=2$ the two complex invariants are $0,1728$. Since $2$ is inert in the Eisenstein integers, every cyclic descending chain from $0$ ends at conductor $2^j$ at depth $j$. Conversely a curve with this conductor ascends to maximal conductor in $j$ steps. The class number formula gives $h(-3\cdot4^j)=2^{j-1}$ for $j\ge1$. All its roots are conjugate, and there are $3\cdot2^{j-1}$ cyclic kernels, hence $\Phi_{2^j}(0,Y)=H_{-3\cdot4^j}(Y)^3$. Simultaneous inertia away from $2,3$ is exactly the residue class $11\bmod12$. [Horizontal and descending isogenies](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec22.pdf) · [The first step from 0 and reduction classes](https://doi.org/10.1080/10586458.2021.1926009)

## Factoring consequences and evaluation cost

Given the residue of $V_j$ modulo $N$, with $X=N$, compute $\gcd(N,V_j^{\,b}\bmod N)$ where $b=\mathrm{bits}(N)$. After the primes of $6\ell D_1D_2$ are removed, this returns the product of the full prime powers of $N$ whose bases are inert in both fields. For balanced semiprimes and fixed fields $-3,-4$ it gives a proper split on limiting proportion $2(1/4)(3/4)=3/8$ of distinct prime pairs, by the prime number theorem in the four reduced classes modulo 12. This population statement presupposes the residue.

A polynomial-sized menu of field pairs suffices to separate **every** two distinct remaining primes $p,q\mid N$. Enumerate discriminants $D=-r$ from primes $r\equiv3\bmod4$ through $Cb^2$, removing trial factors in this range first. By CRT the prescriptions $r\equiv3\bmod4$, $(-r/p)=-1$ and $(-r/q)=1$ form a nonempty coset of index eight in the units modulo $4pq$. The least prime in a bounded-index coset is $O(\log^2(4pq))$ by the Dirichlet GRH coset bound, using Alpöge’s theorem for Dirichlet characters over the rationals. To obtain a second distinct prime with the same signs, apply the theorem again on the units modulo $4pqr$, pulling back the same coset and thereby excluding the first prime. Two such distinct negative discriminants make $p$ inert in both and $q$ split. Enumerate all pairs and refine the current list of coprime blocks using each gcd. Primality tests and integer roots then separate prime powers. Outside evaluating the scalars the work is polynomial in $b$. [Lamzouri–Li–Soundararajan, Theorem 1.4](https://arxiv.org/abs/1309.3595) · [Alpöge’s theorem](https://alpo.ge/remark.pdf) · [Sutherland’s independent verification of the precise statements](https://math.mit.edu/~drew/grh/)

There are two concrete reasons to distinguish the residue problem from printing these integers or enumerating paths.

- For the fixed $0,1728$ sequence at the depth for $X$, the integer is divisible by every prime $11\bmod12$ through $X$. The prime number theorem in this fixed progression already requires $\Omega(X)$ bits to write it.
- Suppose reductions with distinct CM fields meet by a cyclic isogeny of degree $m=\ell^j$ in characteristic $p\nmid mD_1D_2$. Both are supersingular. In the endomorphism ring of the source, take the pure elements $a=2\alpha-\operatorname{Tr}\alpha$ from a generator $\alpha$ of the first maximal quadratic order, and $c=\widehat\phi(2\beta-\operatorname{Tr}\beta)\phi$ from a generator $\beta$ of the second. Then $a^2=D_1$ and $c^2=m^2D_2$. They do not commute since their quadratic fields differ. If $t=\operatorname{Tr}(ac)$, the lattice on $1,a,c,ac$ is an order by $ac+ca=t$. Its reduced discriminant, by the trace determinant, is $4D_1D_2m^2-t^2>0$. The maximal quaternion order has reduced discriminant $p$, which divides this integer. Thus $p\le4|D_1D_2|m^2$. For polylogarithmic discriminants a level below $\sqrt p/\operatorname{poly}(\log p)$ cannot reach that prime. Explicit kernel enumeration has degree $(\ell+1)\ell^{j-1}$. For $0,1728$, Boscardin and Spindler prove the sharper $p<3m^2$ and the diameter bound for paths of length at most their chosen depth. The scalar above uses cyclic paths at exactly one depth. Direct compressed evaluation remains open. [Boscardin–Spindler, Proposition 29 and Theorem 30](https://athene-forschung.unibw.de/doc/153065/153065.pdf#page=20) · [Simultaneous quadratic embeddings and their discriminants](https://sites.math.washington.edu/~bviray/papers/LV_SingularModuliArbitraryDiscriminants.pdf)

## Exact finite checks

The PARI/GP replay constructs $H_{-3\cdot4^j}(1728)$ for $1\le j\le9$ and independently verifies five of the polynomial identities by taking integer resultants of the degree-two-level modular polynomial and removing reversed steps. Across 2,709 prime checks through 2,000, every selected prime greater than three lies in the claimed class. At level $j=9$ the first omitted prime in the class is 479. A fixed shallow level need not cover the entire class. [Executable replay](../experiments/cm-isogeny-prime-filters.gp)

The replay separately builds all 19 supersingular graphs at $p\equiv11\bmod12$ below 400 over $\mathbb F_{p^2}$. For 171 pairs of prime and depth the integer divisibility agreed with positive path count. At the stated theorem depth every one of 6,734 ordered endpoint pairs had positive cyclic count. Three other pairs of CM fields gave another 508 prime checks, and a gcd on a composite with repeated factors recovered $11^2 23^3=1,472,207$.
