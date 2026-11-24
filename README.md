# Deterministic integer factoring research

Research handoff, 2026-11-24. The goal is one deterministic algorithm that returns the smallest prime factor of every integer $N\ge2$. This workspace contains a finite covering theorem and two class-group experiments. A faster uniform worst-case factoring bound remains open here.

## Reproduce the checks

Run from this directory. The checked versions were Lean 4.36.0 and PARI/GP 2.19.1 (development build 31357-780bfb18cf).

```sh
lean TapeCover.lean
gp -fq square-walk.gp <<'GP'
print(checkWalks())
print(squareWalk(24823,19,0,1))
print(squareCollision(24823,19))
GP
```

On the original machine the installed Lean binary is `~/.elan/toolchains/leanprover--lean4---stable/bin/lean`. Calling it directly avoids an elan network check. Lean exits successfully with no output. GP should print the following.

```text
[120, 108, 111, 113]
[1, 30, 12, 11]
[103, 11, 29]
```

## Target and assumptions

For $b$-bit inputs, the top leaderboard entry reports a Lean-verified deterministic running time of $2^{O(b/\sqrt{\log b})}$. The board's score is $1/2$. Its linked source is the place to compare exact machine and output specifications. The older Harvey–Hittmeir bound is $N^{1/5+o(1)}$. This project has checked its own Lean file. The leaderboard proof was not independently rebuilt here. [Leaderboard and scoring rules](https://bigospeedrun.com/integer-factoring) · [Leading entry's repository](https://github.com/1337isnot1337/integer-factoring) · [Harvey–Hittmeir](https://doi.org/10.1090/mcom/3708)

Lenstra–Pomerance gives an unconditional randomized algorithm for complete factorization with expected running time $e^{(1+o(1))\sqrt{\ln N\ln\ln N}}$ on each input. The proposed use of GRH is conditional. No accepted proof of GRH was identified, and it would imply ordinary RH, which Clay lists as open. [Lenstra–Pomerance](https://cr.yp.to/bib/1992/lenstra.pdf) · [Clay Mathematics Institute](https://www.claymath.org/millennium-problems/)

## Finite tape cover

Let $T(b)$ bound the expected runtime for each input of length $b$. Markov's inequality gives a success probability of at least $1/2$ when a run is stopped after $2T(b)$ steps (round the cap up). A bounded run with a fair-bit tape needs only a finite prefix. A list of $b+1$ independent tapes misses any fixed input with probability at most $2^{-(b+1)}$. A union bound over at most $2^b$ inputs leaves probability at most $1/2$ of missing any input. One list per length therefore works.

The alternate finite proof in [TapeCover.lean](TapeCover.lean) counts missed tape/input pairs. For any residual input list, some tape leaves at most half uncovered. Iterating gives a cover. The theorem `finiteTapeCover` takes a nonempty finite tape pool, a Boolean success function, and the per-input half-density bound. It returns a cover from that pool of size at most $k$ whenever the input list has length below $2^k$. The Lean file proves the counting and iteration. The application of Markov's inequality to the randomized factoring machine is a paper argument.

A uniform tape generator with seed length $O(b/(\log b)^{0.6})$, generation plus execution cost $2^{O(\sqrt{b\log b})}$ per seed, and at least one success for every input would give score at least $0.6$ by exhaustive seed search. Any fixed exponent above $1/2$ in place of $0.6$ suffices. The cover theorem supplies existence without a generator or construction time. For an arbitrary half-dense success predicate on $M$ tapes, a deterministic membership search can receive $\lfloor M/2\rfloor$ failures before its first success. Any faster construction needs additional structure.

## Deterministic class-group relations

[Square-walk experiment](square-walk.gp) implements a restricted search for a divisor. The domain used here is odd squarefree $N\equiv3\pmod4$, so $D=-N$ is an odd fundamental discriminant. Write $C_D$ for the group of reduced primitive positive binary quadratic forms. In this domain every nonidentity class of order two gives a nontrivial coprime split of $N$. This follows from the odd-discriminant case of Theorem 2.5 and the formulas in §2.4. Algorithm 10.1 of the paper collects signed prime-form relations from random exponent vectors. [Lenstra–Pomerance, §§2 and 10](https://cr.yp.to/bib/1992/lenstra.pdf)

The function `squareWalk(n,bound,depth,pairs)` starts at every split prime form $f_q$ for primes $q\le B$. With `pairs=1` it also starts at each product of two distinct such forms. At each level it squares the current root $z$. If the reduced form $z^2=(a,b,c)$ has leading coefficient supported on the base, trial division and the middle coefficient give a signed vector $v$ with $z^2=\prod f_q^{v_q}$. The program checks that equality for each accepted row. It deduplicates roots and stops after the specified depth, or at orbit exhaustion for depth zero.

Put the vectors in the columns of $A$. For a binary kernel vector $u$, lift its entries to 0 or 1 and compute
$$
w(u)=\prod_j z_j^{u_j}\prod_q f_q^{-(Au)_q/2}.
$$
The coordinates of $Au$ are even and $w(u)^2=1$. Testing one binary kernel basis suffices. Indeed $u+v$ differs from its bitwise sum modulo two by twice the coordinatewise overlap, whose contribution cancels using the defining square relations. Thus $w$ is a homomorphism on the binary kernel. If every basis image is principal, every dependency from these rows maps to the principal form. The return value is the divisor (1 for a miss), number of distinct roots visited, number of smooth rows, and binary nullity.

## Recovering a collision discarded by the smoothness test

If distinct reduced forms $x,y$ have $x^2=y^2$, their quotient is a nonidentity class of order two. The routine `squareCollision(n,bound,depth)` records one root for each square in a single seed's orbit. It tests every split prime up to the bound until it finds a factor. Equal roots close an orbit. The return value records the divisor, successful seed prime and squaring count on that seed. A miss returns `[1,0,0]`.

For $N=24823=103\cdot241$ and $B=19$, even the pair-seeded smooth walk exhausts all its orbits with 30 distinct roots, 12 smooth rows and 11 independent dependencies. Every dependency gives the identity. Yet the prime form $g=(11,9,566)$ has order 58 and generates the full class group. On squaring 29 times from this seed, the routine finds the following explicit witness.

| Form | Reduced representative |
| --- | --- |
| $x=g$ | $(11,9,566)$ |
| $y=g^{2^{28}}$ | $(64,-3,97)$ |
| $x^2=y^2$ | $(58,57,121)$ |
| $xy^{-1}$ | $(86,69,86)$ |

The common square has leading coefficient $58=2\cdot29$, so it failed the bound-19 smoothness test. The quotient has equal outer coefficients and gives $2\cdot86-69=103$ and $2\cdot86+69=241$. This example isolates a loss of information even with a generating base.

For a seed of order $2^e m$ with $m$ odd and $e\ge1$, its squaring orbit has tail length $e$ and period $r=\operatorname{ord}_m(2)$ (use $r=1$ for $m=1$). Indeed for $i<j$, equality of $g^{2^i}$ and $g^{2^j}$ is equivalent to $2^e m\mid 2^i(2^{j-i}-1)$. At the first repeated square, the predecessors are distinct, so the routine finds a split after exactly $e+r$ squarings on this seed. For the example, $e=1$, $m=29$ and $r=28$. Squaring permutes an odd-order subgroup, so this single-orbit collision search cannot split from an odd-order seed. The argument is on paper. GP checks the concrete witnesses.

GRH gives prime-ideal generators of norm $O((\log |D|)^2)$ for this fundamental discriminant. Inert prime ideals in the quadratic field are principal and a small ramified prime already divides $N$. Therefore, for composite squarefree $N$ in this domain, checking small ramified primes and taking sufficiently many split primes gives a factor or includes an even-order seed, since $C_D$ has even order. The GP experiment fixes $B$ and only tries split primes. With a depth cap $K$, trying all seeds costs at most $K$ squarings per seed. The unknown is how soon a useful collision occurs. The generator theorem alone supplies no sufficiently small bound here for $\operatorname{ord}_m(2)$. [Grenié–Molteni on class group generators](https://doi.org/10.1090/mcom/3281)

## Exhaustive finite tests

These counts cover every pair of distinct primes $101\le p<q\le211$ with $pq\equiv3\pmod4$. Each run used $B=19$ and exhausted its indicated orbits or found a factor. The algorithms took only $N$ and the search parameters. The test used $p,q$ to check every reported divisor.

| Search | Inputs split out of 120 |
| --- | ---: |
| Smooth relations, single-prime seeds | 108 |
| Smooth relations, single and pair seeds | 111 |
| Equal-square collision, single-prime seeds | 113 |

Two other cases identify distinct failure modes.

- For $11227=103\cdot109$, the single-seed smooth search obtained four smooth rows from seven roots, with binary nullity three and trivial image. A pair seed added one root and one smooth row and the new dependency exposed 103.
- For $17947=131\cdot137$, the class number is 22. Its only split primes up to 19 are 7 and 11, both giving order-11 forms. All products stay in the odd-order subgroup. The prime 23 gives an order-22 seed and a split after 11 squarings. Increasing the bound to 43 includes it.

Class numbers and seed orders above were checked separately on the small examples. Neither search uses a class number, a factorization of the class number, or the factors of its input. These tests measure coverage for the specified finite family. They establish no asymptotic rate or practical speed record.

## Where to continue

1. Use the exponent criterion to price a proposed walk. One sufficient intermediate result for this discriminant family would be a bounded list of small seeds, constructible within budget, containing an even-order seed with $e+\operatorname{ord}_m(2)\le2^{O(b/(\log b)^{0.6})}$. Charge for all seeds and form operations. An unconditional leaderboard result also needs an unconditional way to get the seeds and an argument covering the other input classes.
2. For relation-based variants, preserve equal nonsmooth squares and track the image of the dependency space. Use 24,823 to check claims based on smooth-row counts or nullity. The number of dependencies can grow while their entire image stays trivial.
3. When varying the discriminant, distinguish the order of one useful seed from the entire class number. Lenstra–Pomerance §11 gives families where every eligible discriminant multiple has a large prime divisor of its class number. A proof that depends on finding a smooth whole class number must address their obstruction. [Lenstra–Pomerance, Theorem 11.1](https://cr.yp.to/bib/1992/lenstra.pdf)

## Parallel follow-up

The [parallel research handoff](swarm-research.md) contains the arbitrary-input divisor-coefficient reduction, the exact-order reduction, the shared class-group collision experiment, a smoothness cutoff bound, and a Lean-checked cost inequality for regrouping the pinned clique network. It includes the source links and commands for reproducing the checks.

The [second parallel search](swarm-round-2.md) gives an equal-order elliptic-curve split, a batch algorithm for multiplicative-order probes, explicit limits on curve schedules and digit representations, and a carry-free CRT construction with an open join-cost bound. The [PARI/GP checks](swarm-round-2.gp) reproduce the principal finite results.
