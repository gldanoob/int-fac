// Compile with typst compile randomized-one-input-factoring.typ.
#set document(title: "Randomized factoring with leading coefficient below two")
#set page(paper: "us-letter", margin: (x: 80pt, top: 72pt, bottom: 70pt),
  numbering: "1", footer-descent: 19pt)
#set text(font: "New Computer Modern", size: 10.9pt, lang: "en")
#set par(justify: true, leading: 0.52em, spacing: 0.55em, first-line-indent: 16pt)
#show math.equation.where(block: true): set block(above: 6pt, below: 6pt)
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => block(above: 14pt, below: 7pt, sticky: true)[
  #set text(size: 14.4pt, weight: "bold")
  #if it.numbering != none [#counter(heading).display("1")#h(10pt)]#it.body
]
#show heading.where(level: 2): it => block(above: 13pt, below: 7pt, sticky: true)[
  #set text(size: 12pt, weight: "bold")
  #counter(heading).display("1.1")#h(8pt)#it.body
]

#let repo = "https://github.com/gldanoob/int-fac/blob/explore/randomized-one-third/"
#let note(file, label) = link(repo + "research/" + file + ".md", label)
#let lean(file, label) = link(repo + "formal/cogentic/Cogentic/" + file + ".lean", label)
#let core(file, label) = link(repo + "formal/cogentic/" + file + ".lean", label)

#v(33pt)
#align(center)[
  #set par(leading: 9pt)
  #text(size: 17.3pt, weight: "bold")[Randomized factoring#linebreak()with leading coefficient below two]
  #v(12pt)
  #text(size: 12pt)[November 27, 2026]
]
#v(23pt)
#align(center, text(size: 10pt, weight: "bold")[Abstract])
#block(inset: (x: 27pt), above: 5pt, below: 6pt)[
  #set text(size: 10pt)
  #set par(leading: 5.1pt)
  #h(14pt)We study the expected bit complexity of factoring a single integer $N$ with all setup charged to that input. We adapt KeyBreak’s multilevel descent by narrowing the public polynomial coefficients and counting products of primes in short intervals. The resulting manuscript bound is $L_N thin [1\/3,C_*]$ with $C_* = 1.9839824118071388229 dots$. A fixed rational schedule already gives a coefficient below $1.984578735$. The analysis uses the verified Dirichlet critical-line theorem. Lean checks the scalar optimization and several components of the algorithm. Verification of the full expected-time bound remains open.
]

= Introduction

The algorithm constructs two square roots of the same residue modulo $N$. When their signs agree at some prime factors and differ at others, a greatest common divisor splits $N$. Narrower public polynomial coefficients reduce the descent cost. Estimates for products of primes in short intervals show that enough usable relations remain.

KeyBreak’s multilevel descent gives a coefficient of $2.97$ under the critical-line theorem for Dirichlet $L$-functions, including zeta [1, Thm. 1.2]. Alpöge’s Lean proof of that theorem has been independently checked [2]. Our analysis combines KeyBreak’s analytic arguments with estimates for the modified field distribution and sampler [3–5].

== Main result

Write $H(N) = (log N)^(1/3) (log log N)^(2/3)$ with natural logarithms, and use
$ L_N thin [alpha,c] = exp((c+o(1))(log N)^alpha (log log N)^(1-alpha)). $

*Theorem 1.1* (Single-input factorization, manuscript bound). _There is one classical randomized algorithm that, on each integer $N >= 2$, terminates on every random tape and returns the prime factorization with multiplicities. Its expected bit complexity satisfies_
$ EE T(N) <= L_N thin [1\/3,C_*], quad C_* = 1.9839824118071388229 dots . $

Equivalently, for every $epsilon > 0$, all sufficiently large $N$ satisfy $EE T(N) <= exp((C_*+epsilon)H(N))$. In big-$O$ notation this gives $EE T(N) = exp(O(H(N)))$. The expectation is over independent fair bits. The bit count includes setup, failed searches, verification and recursion. A fixed rational schedule with 4,096 stages yields the explicit ceiling in the abstract [3, 6].

= Private rows from reduced forms

Preprocess even integers, primes and prime powers. A bounded elliptic-curve pass finds a proper divisor with high probability when a sufficiently small prime factor is present. The pass costs $exp(o(H(N)))$. For the remaining analysis take $N$ odd with at least two distinct prime divisors. Use proper ideal classes of the order $ZZ[sqrt(-N)]$. Draw a nearly uniform class, square it and reduce to a primitive form with leading coefficient $A <= 2 sqrt(N/3)$. The reduction computes a private unit $z$ with $z^2 equiv A mod N$. For instance, if the unreduced form is $[a,2b,(b^2+N)/a]$ with $a=q^2$, and $(x,y)$ is the first column of the reduction matrix, then
$ a A = (a x + b y)^2 + N y^2, quad
   z equiv (a x + b y) q^(-1) mod N . $
The inverse exists because the accepted seeds are units. The algorithm verifies the congruence and passes only $A$ to the public search [3].

For a uniform class, the preimages of a fixed squared class form a coset of the 2-torsion subgroup. Twisting by the ideal classes associated with coprime divisors of $N$ gives every relative Chinese remainder sign, and a fair independent global sign gives the uniform law on all roots of $A$. A whole-transcript total-variation comparison transfers that ideal law to the capped sampler. The private stage tests use prescribed prime size bands. To count usable $A$, the analysis multiplies the quadratic genus-character biases over the ordered prime slots. The principal-genus fraction cancels against the index of the squared classes. Upper bounds on the number passing each prefix limit the screening work [3].

= The public fields and the top predicate

In each split call let $M = floor(N^(1/d))$ for the scheduled degree parameter $d$. Choose a fresh public prime multiplier $k$ in $[M^c,2M^c]$ for a sufficiently large fixed integer $c$. Sample an odd-degree defining homogeneous polynomial $F$ using $k N$. Increase the physical degree to $d' = d + L_0$ for a fixed even increment $L_0$ and keep the radix $M$. At the chosen evaluation pair $(r,Q)$, the exact identity $F(r,Q)=k N$ still supplies an evaluation map modulo $N$. The larger physical degree is used in the norm heights and child-cutoff recurrence. For a fixed schedule this changes their leading ratios by $o(1)$ [3, 4].

A mark is a prescribed prime and root of the defining polynomial modulo that prime. A top relation is obtained by searching lattice points satisfying its mark and testing both a rational value and an algebraic cofactor. Qualifying child primes and their roots become marks for the next level. At the top, restrict the prime denominators of search points to a narrow interval so the cofactor sizes are comparable to a common scale $X$. Require the top cofactor to lie in a squarefree product set $cal(S) subset [X,2X]$, with each prime below the local child cutoff $y$. Interior levels retain the ordinary smoothness tests [1, 3, 4].

*Prime-bin count.* Put $u_0 = log X / log y$ and choose $m = ceil(u_0 (1 + 1/log u_0))$. Split a logarithmic band below $y$ into $J$ disjoint bins of equal log width $Delta$ of order $1/m$. Select all size-$m$ subsets with a common index sum that maximizes their number. There are at least $binom(J,m)/(m J)$ such subsets, by pigeonhole. Position the bins so the product of the lower endpoints for each pattern is $X$. If those endpoints are $a_i$, the products stay between $X$ and $X exp(m Delta) <= 2X$. Unique factorization makes the pattern counts additive. The RH prime estimate contributes a factor comparable to $Delta a_i/log y$ per bin. Since $J Delta$ is of order $log y/log u_0$, the count gives, for an absolute constant $c_1>0$,
$ |cal(S)|/X >= 1/(m J) (c_1/(m log u_0))^m
    = exp(-(1+o(1)) u_0 log u_0). $
The ordinary smooth-number upper bound gives the same leading logarithmic density. The predicate uses bin membership and the index sum after bounded factorization, and needs no table of eligible primes or products [3, 4].

*Changing the distribution.* The one-point estimate is normalized by $mu = |cal(S)|/X$ itself. On each bin pattern the Dirichlet character bounds multiply, giving relative cancellation $X^(-1/2) V^(o(1))$ on the top size-$V$ box scale. A truncated Perron integral transfers the bound to product prefixes. Prescribing a child prime removes one free prime and gives the same estimate at the divided size, with the completion density at most a polynomial multiple of $mu$ in the normalized incidence bound [4].

The two-mark transfer also needs control over the actual pair distribution. The multiplier and the Cartesian phases give nearly uniform marginal progression phases, including when a child root is already prescribed. Parseval controls average Fourier energy over the progression grid. Cauchy–Schwarz on the two marginals handles their determinant constraint. The coefficient width is $V_(max)^chi$ up to polynomial factors in the input bit length, where $V_(max)$ is the largest top box scale. The relative grid energy saves $V^(-(chi-1)+o(1))$ in a size-$V$ box, enough to absorb Gaussian variation for a sufficiently small angular cutoff and any fixed $chi > 1$. The near-parallel pairs discarded in this estimate have power-small frequency. These are averaged estimates for the new top law. The interior deletion recurrence uses KeyBreak's estimates with the multiplier fixed [1, 4].

= Shared descent and the square comparison

The incoming-root estimate matters because the descent chooses its own child marks. A statement about a random mark alone would leave open whether the search repeatedly introduces the exceptional marks. The recurrence bounds weighted bad-child incidences. Combining this bound with the ordinary first and second moments yields an inverse-polynomial success probability per independent public field draw, outside a small deterministic exceptional set of parent primes in each used dyadic band. A polynomial pool of independent full public environments and fields then covers the retained primes with high probability. The algorithm tries a bounded search in each field as needed and charges the entire pool, including failed searches and elliptic recognition. Sharing the pool across private rows concerns many operations for the *same* input. Each recursive call builds and pays for its own setup [1, 3, 5].

Keep every descent subtree in its chosen field so that its large-ideal valuations cancel there. One completed row gives a checked product identity for the private value $A$, with a rational correction and field-labelled components. More completed rows than parity columns guarantee a nonempty dependency. The signed norms, occurrence parities, ideal parities and quadratic characters certify a square separately in each used field. In particular the occurrence column makes the leading-coefficient factor in its norm formula a square. Odd field degree lets the signed norm-square condition remove the rational squareclass left by the ideal and character tests. The exact field roots and the rational correction evaluate to a public root $w$ [1, 5].

All public choices, including the dependency and $w$, are made before accessing the private roots. For a nonempty binary dependency the product $z_*$ uses at least one independent uniform root sign vector in the ideal experiment. Conditional on the public transcript, its ratio to the checked public root is uniform on the solutions of $v^2=1$ modulo $N$. If $N$ has $s$ distinct prime divisors, CRT gives $2^s$ vectors of signs on the odd prime powers. The two constant vectors are the only failures of $gcd(z_*-w,N)$. The success probability is therefore $1-2^(1-s) >= 1/2$. This calculation also covers repeated prime factors. A proper divisor is verified before recursion [3, 5].

= The two active costs

For the scalar schedule, measure leading log work in units of $H(N)$. Write $b$ for the factor-base and row exponent, $u>0$ for the private screening parameter, and $C$ for a candidate ceiling. At the boundary $chi = 1$, the private screening and terminal low-descent requirements reduce to
$ b+p(u) <= C, quad p(u)=2/(9u^2)+2u/3, $
$ 6b(C-b) >= (3/4)u^2 + 4 sqrt(C). $
At the minimizing point both constraints are equalities. Substituting $b=C-p(u)$ and requiring stationarity in $u$ gives
$ 6(C-2b)p'(u)=-(3/2)u . $
Root isolation and the supporting-tangent inequality give
$ 1.9839824118071388228 < C_* < 1.9839824118071388230 . $
Here the infimum concerns these cost inequalities. The other budget and geometry inequalities have strict room at the limiting point, with top and high ratios $1.43$ and $1.636$. Costing the finite rational schedule at $chi=1.01$ bounds private screening by $1.984578735$, low raw work by $1.984515433$, and all other leading charges by smaller values [6].

= From fixed schedules to one algorithm

The analytic transfer uses only widths with $chi>1$. Given any positive excess, fix rational parameters with $chi$ close enough to 1, use a sufficiently fine finite grid, and choose positive slack in the analytic guards. Then take the input limit with that schedule fixed. This order gives fixed schedules with expected splitter exponents arbitrarily close to $C_*$ [3, 6].

The manuscript obtains a single algorithm by enumerating finite schedule encodings. In phase $r$ give each index $j <= r$ a fresh execution of $2^(r-j)$ charged steps. Also advance trial division with $2^r$ steps, giving termination on every tape. Suppose a fixed valid index has expected split work $E_j(N)$ on the current composite. Once $2^(r-j) >= 4 max(1,E_j(N))$, Markov bounds its conditional miss probability by $1/4$ in every fresh phase. Total phase budgets grow by a factor of two, so the remaining expected budget is a convergent geometric sum. The resulting expected charge is $O(2^j max(1,E_j(N)))$ up to polynomial bookkeeping. For each fixed index the overhead contributes only $o(H(N))$ to the logarithm of the expected cost. Taking the infimum over fixed indices yields the asserted limsup bound. Every verified proper split has two smaller factors, and the full tree has $O(log N)$ nodes. Applying the per-input bound and charged primality tests throughout the tree preserves the coefficient [3, 7].

= Verification status

Lean proves the exact infimum characterization and decimal enclosure for the two-inequality scalar model. It also checks the finite 4,096-stage private screening gate, arithmetic pieces of the private root and split verification, the finite pool coverage argument, and probability and cost lemmas for restarts and recursion. The separate `RandomizedWithGRH` target links the shorter Dirichlet proof to sharp prime-bin supply, product character bounds and unit progression counts [2, 7].

The key remaining formal lemma is a uniform per-call expected-work bound for the actual hard-input splitter. It must connect its executable, capped searches and recognizers to a verified split probability on each sufficiently large fixed input, with the charged epoch budget. The existing recursion and restart theorems lift such a per-call bound. The full analytic transfer and complexity result are at manuscript level [3, 7].

#heading(numbering: none)[References]

#text(size: 10pt)[
  #set par(first-line-indent: 0pt, hanging-indent: 13pt, spacing: 7pt)
  [1] The KeyBreak Cryptanalysis Agent. #link("https://crypto.sjtu.edu.cn/factoring.pdf")[_Provable Integer Factorization via Multilevel Descent: Approaching Heuristic Bounds_]. 26 November 2026. Thm. 1.2 and Apps. E, G–H. Pinned SHA-256 `2b534eaf77fb2b9712018879059d8d4667c40c0a4adf2fff90efc22fb356cfc9`.

  [2] A. Sutherland, independent verification of #link("https://math.mit.edu/~drew/grh/")[Alpöge’s Lean proof of RH and Dirichlet GRH] and of the #link("https://math.mit.edu/~drew/shortgrh/")[shorter proof] at #link("https://github.com/lsernau/grh-lean/tree/72fead10")[commit 72fead10].

  [3] Repository manuscripts on the #note("keybreak-balanced-class-integration", [balanced single-input construction]) and #note("keybreak-quadratic-class-integration", [private quadratic-class sampler]).

  [4] Repository manuscripts on #note("keybreak-prime-product-grid-variance", [prime-bin supply and progression variance]), #note("keybreak-mixed-strip-moment", [multiplier-averaged pair estimates]), and #note("keybreak-balanced-strip-transfer", [incidence transfer]).

  [5] Repository manuscript on the #note("keybreak-polynomial-top-field-pool", [public field pool and field-labelled extraction]).

  [6] #note("keybreak-single-root-width-one-limit", [Finite and limiting cost derivation]) and #lean("RandomizedBalancedEnvelopeInfimum", [Lean scalar infimum]).

  [7] #core("RandomizedFactoring", [Randomized Lean checks]), #core("RandomizedWithGRH", [prime-bin GRH target]), #lean("RandomizedWidthOneGate", [finite gate]), and #lean("RandomizedSplitWork", [split-tree work]).
]
