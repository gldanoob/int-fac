# Blueprint: discharging `HardEpochAsymptoticBound (E s) D` for valid balanced schedules

Target: `Cogentic/RandomizedEpochAssembly.lean`, hypothesis of
`serialized_assembled_balancedEnvelopeInfimum_from_critical_line`:
`∀ s D, s.Valid D → HardEpochAsymptoticBound (E s) D`.

Sources. "KB" means the pinned KeyBreak PDF (`~/.cache/intfac-combined/sjtu-factoring.pdf`). The text
dump `sjtu-factoring.txt` is next to it, and page numbers are the printed ones, which match the
`#page=` links in the notes. "R/x" means `research/keybreak-x.md`. "L/X" means
`formal/cogentic/Cogentic/RandomizedX.lean`. Modules marked (repair) do not compile yet.

---------------------------------------------------------------------------------------------------
## 0. Two interface findings to resolve before any formalization (read first)

**0.1 The hypothesis can be met by a trivial epoch, so as stated it has no algorithmic content.**
`HardEpochData.data : good → TranscriptData` is an arbitrary (noncomputable) function of the
public transcript. Nothing charges the cost of computing `publicRoot` to `pubWork`, and
`observe` shows the public the squares `x.2 j ^ 2` (L/HiddenOutputLaw:16). Take the following
epoch for every N:
`Coins = Unit`, `Label = Unit`, `Public = (ZMod N)ˣ`, `trace _ s = s ()`,
`good = {t | IsSquare t}`, `data t = ⟨{()}, 1, Classical.choose (t is a square), (), _, odd 1⟩`,
`ideal = actual = uniform`, `pubWork = 0`.
- CongruenceCheck: `(x.2 ())^2 = t = publicRoot^2`.
- HiddenUniform: holds because the law is uniform.
- Choose γ = 1, ε = 0, W_pub = 0. Then 1/2 ≥ exp(-(δ/4)·scale n) eventually.

So `HardEpochAsymptoticBound E C` holds for every C. With C = 0 the fixed-schedule theorem would
claim an L[1/3, ε] factoring algorithm. I did not compile this instance (no Lean builds were
allowed), but every step unfolds the definitions in §3–4 of EpochAssembly directly.

Consequence: formalizing the analytic tree below is pointless unless the interface is changed.
Minimal fix:
- `trace`, the membership decision for `good`, and `data` must be outputs of programs in a fixed
  costed model, i.e. a deep embedding or cost monad over bit operations with no `Classical.choose`.
- `pubWork x` must be at least the model cost of running those programs on `x`.

The same self-reported-cost pattern (`Option β × ℕ`) appears throughout: CappedEpoch, InputDriver,
SmallPrimePrepass. So this is a project-level [INFRA] item, about 2–5k lines.

**0.2 The bound is required on every hard n, but the manuscripts only prove it on rough n.**
KB H.8 (p.141) and Theorem G.1 (p.106) assume a B-rough input. So do the direct class sampler
(TV ≤ polylog/p_min, R/direct-reduced-class-sampler) and H.5 (p.134). Inputs with a prime factor
below `roughThreshold` go to a prepass. A prepass factor cannot be returned through
`HardEpochData`: success only comes from the hidden-sign gcd in `certifiedEpochTrial`. The same
holds for gcd exits during setup or sampling (Q | N, content, leading coefficient, gcd(A, N)).
The fix is to restate the top theorem through `SmallPrimePrepass.combined_epoch_asymptotic_logB`
or `factor_expected_from_prepass_and_rough_epoch` (already [LEAN]) and require
`HardEpochAsymptoticBound` only on `IsRough (roughThreshold n) n`.
The prepass itself is then a new leaf (P1 below): a genus-two (KB H.3) or ECM partial factorer
up to exp((log n)^{2/3}). Its cost must be exp(o(H)). Trial division in Lean
(`trialPrepass_mean_work_le_exp`) only reaches B ≤ exp(ε·scale).

---------------------------------------------------------------------------------------------------
## 1. One epoch on a fixed rough hard input N (as it must be defined in Lean)

Notation:
- n = bit length, D = (log N/loglog N)^{1/3}, H = (log N)^{1/3}(loglog N)^{2/3} (`scale`).
- Λ = D·loglog N.
- Schedule s: χ = 1.01, top ratio λ_T = 1.43, high ratio λ_H = 1.636, a 4096-knot private grid,
  ECM coefficients s1 = s2 = .7071067… (R/single-root-width-one-limit, "Exact fixed grid").

Lean shape:
- `Sample = Coins × (Label → (ZMod N)ˣ)`.
- `Label = Fin R_shape` (private slots).
- `Coins` = every public random block (finite, fixed-width rejection blocks; KB H.8 (H.31), p.140).
- The private sampler's internal randomness is NOT part of `Coins`: it is marginalized.
- `ideal` = exact distributions. `actual` = capped fair-bit implementations.

| # | Step (public/private) | What it computes; charge | Source |
|---|---|---|---|
| S0 | public, deterministic | Integer parameters from (N, s): d (KB §2.2 p.6); d' = d+L0 (L0 even); M = ⌊N^{1/d}⌋; tiered cutoffs Y0>…>Yj=B and V(e), c(e,λ); T_H; stage bands L_j, k_j, J_j; σ = 2^{⌈χ log2 Vmax⌉}·n^{10}; per-top-band prime-bin strip data (X_*=2^a, y=2^e, k_s, bin spacing 1/(2k_s), index sum A by subset-count DP); caps R_shape, T_Search, P_raw, A_occ, column bound C, L_conf (KB (H.30)–(H.32) p.140–141); pool size P = D^{C0+c}. Charge: poly(n)·exp(o(Λ)) | R/narrow-class-integration "Integer scales and cost"; R/balanced-class-integration ¶2–3; L/BalancedRationalSchedule |
| S1 | public coins | Field pool, j = 1..P: prime Q_j∈(3M/4,M] and r_j∈(M/2,3M/4], with bounded rejection, primality test, gcd(Q_j,N); prime multiplier k_j∈[M^C,2M^C], gcd with N; centered base-Q digits F̂ with F̂(r,Q)=k_jN, parity correction irreducible mod 2; discrete Gaussian perturbation, width σ (KB Lemma H.1); setup screens gcd(content, lc, F'(m_N), N). Data: F_j∈Z[X,Y]_{d'}, m_N = rQ^{-1} mod N | R/multiplier-residue-phases §Height; KB §2.2 p.6, H.1 p.126 |
| S2 | public coins | Character probes per field: (2d')!·poly(n) prime/root proposals at S-bit size, signs compressed by random m-bit masks. Charge: coefficient "Characters" 1.891 | R/cumulative-character-probes; KB E.3 p.87–89, H.6 p.136 |
| S3 | **private** | For each slot i < R_shape: direct reduced-class sampler for disc −4N (or −8N), capped; square the ideal (formula for b mod a); Gauss-reduce to [A_i,2b',C'], keeping column (x,y); z_i = (ax+by)/q mod N, times a fair sign; check z_i² ≡ A_i; nonunit A_i → reject. Label value h_i := z_i. The public sees only A_i, the canonical representative of z_i² (A_i ≤ 2√(N/3) < N). Form/ideal data are discarded | R/quadratic-class-integration; R/direct-reduced-class-sampler; L/ReducedFormRoot, L/ReducedFormMinimum |
| S4 | public | Staged private screening of A_i: at each of 4096 stages, ECM (Lenstra–Pomerance Thm 7.1) with w = 2^{⌈.70711k_y⌉} and 2^{⌈.70717k_y⌉}·L_c curves; recursive verified splitting, early abort. Accept iff A_i is a counted shape (squarefree, k_j primes in band group j, H.18–H.20 recipe). Charges: "Raw private slots" 1.9819, "Staged screening" 1.98458 | R/private-elliptic-recognition; R/private-band-stages; KB H.5 p.134; L/WidthOneGate, L/PrivateFloor |
| S5 | public coins | Descent of each top prime p of an accepted A_i. Try fields in public order, a fresh bounded Search per field. Search: uniform points in the special-prime lattice box (KB H.2 p.127). Denominator b is prime in (2V/3,(2V/3)(1+1/d')], with a ≡ sb (mod p). Rational side: G(P) is p·B-smooth. Algebraic side: F(P) ∈ S, the balanced prime-bin strip (top), or Y_{i+1}-smooth (interior). Recognition: genus-two partial factorer to B (KB H.3), then recursive ECM up to the local child cutoff. Each child q>B with odd valuation becomes a request in the same field. Quotas q_s, M_c, caps T_Search (KB H.4 p.132). Charges: top/high/low raw and algebraic (1.870, 1.983, 1.9845, 1.967, 1.910, 1.736) | R/polynomial-top-field-pool; R/balanced-strip-transfer; R/public-elliptic-recognition; R/tiered-descent; KB §2.2 p.6–7 |
| S6 | public | Row records for completed trees: private index i (multiplicity 1); shared rational columns (sign, factor base, each Q_j); per field: occurrence parity E_j, small good ideals, signed norm columns, compressed characters. Keep up to C+1 rows | R/polynomial-top-field-pool §Field-labelled rows; KB E.6 p.94, H.8 p.140 |
| S7 | public | Sparse F2 dependency (Krylov/Padé–Wiedemann) giving a nonempty mask I | L/TaggedSolver, L/Pade*, L/FieldExtraction §4 |
| S8 | public | Per field: exact square root in Z[β_j], β_j = A_jα_j (E.16–E.19, H.7 Hensel); evaluate at A_j m_N mod N through the verified unit denominators; multiply by √(rational correction). Y = product. **Check Y² ≡ ∏_{i∈I} A_i (mod N).** Charge: "Sparse solve and extraction" 1.8896 | KB E.4 p.89, H.7 p.138; L/FieldExtraction |
| S9 | private, last | gcd(∏_{i∈I} z_i − Y, N) = `certifiedEpochTrial` | KB (H.33)–(H.34) p.141, Thm E.5 p.91; L/EpochSuccess |

Lean fields:
- `trace` = S0–S8 as a function of (Coins, squares). `Public` = (I, Y, check bit), or the full transcript.
- `good` = {S7 found I ≠ ∅ and the S8 check passed}.
- `data t = ⟨I, 1, Y, some i∈I⟩`.
- `pubWork` = the model cost of S0–S8 plus the capped cost of S3. All steps are capped, so the cost
  is bounded on every tape (KB Table 2, p.143).

---------------------------------------------------------------------------------------------------
## 2. Dependency tree: conjuncts of `HardEpochAsymptoticBound` → leaves

Tags: [LEAN] proved (module.theorem); [LEAN-R] stated in a module under repair;
[FORM] proved on paper, formalizable with current Mathlib; [INFRA] proved on paper or in the
literature, needs large missing infrastructure; [GAP] not actually proved (sketched, or "the same
argument works").

### C1. `CongruenceCheck` (about 0.3k lines)
- L1 [FORM, trivial] If `good` requires the public check Y² = ∏_{i∈I}(observed square i), then
  (∏z_i)² = ∏z_i² = Y² follows from the definition of `observe`. No number theory is needed;
  the number-field work only affects γ.
- Alternative route: `HardEpochData.ofMultiField_congruenceCheck` [LEAN].

### C2. `HiddenUniform` (about 2–4k lines)
- L2 [LEAN] Uniform law on a square fiber / global sign fiber:
  `ClassSignFibers.square_tag_uniform`, `square_global_sign_uniform`; also `UnitaryDivisorSign`,
  `TargetGenus.target_uniform`.
- L3 [LEAN] z² ≡ A (mod N) and A ≤ 2√(N/3): `ReducedFormRoot`, `ReducedFormMinimum`.
- L4 [INFRA-moderate] The class group of primitive forms of disc −4N or −8N for non-maximal orders
  (form composition, or forms ↔ invertible ideals of Z[√−N]). Includes the ideal-squaring formula
  and the claim that changing the ideal representative changes the root only by a global sign
  (R/reduced-form-root-signs). Lean only has an abstract `CommGroup G`, and FormGroup (repair)
  only has reduced forms and counts. Mathlib has `ClassGroup R` for domains but no forms bridge.
- L5 [FORM] The product law over slots plus independent public coins gives the coordinatewise
  flip invariance required by `HiddenUniform`. Restricting to classes with unit A is a union of
  G[2]-cosets, so it preserves the invariance. Lean pattern: E.5 proof (p.91–92);
  `HiddenSplitLaw`, `SignCount`.

### C3. ε ≥ TV(ideal, actual) (about 2–4k lines)
- L6 [LEAN-R] Direct sampler conditional law is exactly uniform; missing fraction
  ≤ polylog(N)/p_min: `DirectClassSampler.directRetryConditionalPMF_eq_uniform`,
  `directRetryConditionalPMF_tv_le`, `missing_root_sum_le_log_pow`. Rough-branch smallness:
  `SmallPrimePrepass.poly_log_two_mul_div_exp_logB_tendsto_zero` [LEAN].
- L7 [LEAN-R] Class-number lower bound √N/log N under GRH, used to normalize L6:
  `FormGroup.reducedForms_card_lower_from_critical_line`.
- L8 [LEAN] Fair-bit rejection blocks: `UniformBits`. TV of transcripts under maps:
  `SamplerTransfer.mapped_transcript_transfer`, `FiniteSupportTV`.
- L9 [FORM] Finite discrete Gaussian sampler with TV e^{−n^{10}} and conditional cost O(qε)
  (KB Lemma H.1 p.126; R/root-congruence-scope).
- L10 [FORM] Per-slot TV e^{−ω(H)} times exp(O(H)) slots is o(1).
  Requires p_min ≥ exp((log n)^{2/3}), i.e. depends on 0.2.

### C4. W_pub: mean pubWork ≤ exp((D+δ/2)·scale) (about 8–20k lines)
The cost is bounded on every tape, so the mean bound follows from the pointwise bound.
- L11 [LEAN] Scalar schedule certificates and staged screening sums:
  `BalancedRationalSchedule`, `RandomizedEpochAssembly.balancedSchedule_multistage_screening_cost_le_exp`,
  `WidthOneGate`, `BalancedEnvelopeInfimum`, `BalancedScalarMargins`.
- L12 [FORM, large] The integer schedule realizes the scalar exponents with o(H) error: tiered
  recurrence, O(log D) levels, band widths o(E_j), floors, d'/d → 1.
  Sources: R/narrow-class-integration "Integer scales and cost"; R/tiered-descent;
  analogues of KB (H.30)–(H.35).
- L13 [FORM] Per-call cost formulas:
  - ECM: #curves·w·poly (R/private-elliptic-recognition last section);
  - genus-two: (H.5) p.129;
  - lattice sampling: H.2;
  - characters: (2d)!·poly;
  - linear algebra: `PadeCost`, `SparseProducts` [LEAN];
  - root reconstruction: H.7 p.138.
- L14 [LEAN] Summation and asymptotic combiners: `eventually_finset_sum_le_exp`, `trialBudget_*`.
- L15 [FORM, after 0.1] The cost model charges every step of S0–S8.
- L16 [LEAN] Rankin prefix upper bounds controlling stage survivors:
  `ReducedFormSupply.certified_prefix_rankin_bound` (repair), `SmoothDensity.smoothCount_rankin_upper` (repair).

### C5. γ ≤ P_ideal(trace ∈ good), with γ ≥ 1/4 − o(1) (KB H.8 chain, p.141)
Then use `hardEpochAsymptoticBound_of_const_hit` [LEAN] with ε ≤ 1/1024 + o(1).

**C5.a Field pool covers almost all primes in every used dyad** (R/polynomial-top-field-pool)
- L17 [LEAN] Paley–Zygmund + second-moment cut + bad-child Markov give hit probability ≥ D^{−C0};
  dyad trimming; pool union bound. Theorems in `FieldPoolDescent`: `pmf_survivor_event_prob_ge`,
  `survivor_ratio_ge`, `dyad_trimming_of_avg`, `pmf_trimmed_dyads_survivor_pool_coverage`;
  `PoolCoverage.poolMissMass_le_card_mul`.
- L18 First moment E[Z_p | g] ≥ a·τ̄_p on rational-good g, with τ_p ≍ τ̄_p = μT'_0ρ_p/p.
  - L18.1 [LEAN] Prime-bin strip progression counts under GRH:
    `PrimeBinProgression`, `PrimeBinLogTwist.primeBin_logTwist_from_critical_line`,
    `ProductPerron.primeBin_product_prefix_from_critical_line`,
    `TopStripMoments.centeredBinProducts_pruned_progression_from_critical_line`.
  - L18.2 [LEAN-R] Strip density −log μ = (1+o(1))u log u, lower bound:
    `SmoothDensity.eventually_centeredBinProducts_density_from_critical_line`.
    The matching upper bound uses Harper's Smooth Numbers Result 3 and Hildebrand: [INFRA],
    but only an upper bound is needed and Rankin [LEAN] may suffice.
  - L18.3 [LEAN-R] One-point Gaussian progression kernel at width σ:
    `EllipticAndGaussian.gaussian_residue_class_prob_*`, `single_root_progression_conditioning`.
  - L18.4 [INFRA] Rational-good environments at the shrunken denominator interval (KB Lemma G.3
    p.107; large sieve, cell progressions under RH; R/balanced-ideal-pair-audit §1). On paper it is
    proved, but it needs RH prime counts in cells and a large-sieve inequality (not in Mathlib).
  - L18.5 [FORM] The KB G.4–G.6 one-point comparison (p.109–111) applied uniformly in the
    multiplier k.
- L19 Second moment E[Z_p² | g] ≤ D^{c0}·τ̄_p² at narrow width σ = V^{1.01}
  (KB's G.19 needs about σ ≥ V²; R/narrow-class-integration says G.19 "can fail").
  - L19.1 [LEAN-R] Affine two-mark phase coset, exact marginal unit uniformity, GRH prime-multiplier
    equidistribution: `MultiplierPhases.perturbation_affine_coset_iff`, `marginalPhase_exact_uniform`,
    `prime_multiplier_equidistribution_from_critical_line`.
  - L19.2 [LEAN] Averaged Parseval/prefix energy and the two-marginal Cauchy–Schwarz:
    `PrimeProductPlancherel.primeBinProducts_mellin_energy_from_critical_line`,
    `PrimeGridPrefixEnergy.primeBinProducts_gridPrefix_from_critical_line`,
    `TopStripMoments.coupled_mode_cauchy_schwarz`, `primeBinProducts_averaged_coupled_abel_from_critical_line`,
    `MarginalModes`.
  - L19.3 [LEAN-R] Mahalanobis tile and lattice normalizer bounds:
    `EllipticAndGaussian.mahalanobis_2d_lattice_mass_bounds`, `mahalanobis_2d_discarded_radius_rpow_le`.
  - L19.4 [GAP] Poisson quotient for the actual discrete Gaussian two-mark law. Claimed pieces:
    denominator 1+O(V^{−c'}) per multiplier; injective step-frequency grid; short dual modes
    σ‖w‖ ≤ (log X)²; twisted-Gaussian variation loss V^{2ζ}.
    Sources: R/mixed-strip-moment §Denominator, plus R/narrow-top-moment, R/gaussian-variation,
    R/dual-major-arc-count. Each step is a paragraph. Poisson summation on ℝ² lattices with
    correlated Gaussians is also [INFRA] (Mathlib only has 1-D Schwartz Poisson summation).
  - L19.5 [GAP] Ideal zero-mode bound D^{O(1)}μ_q² + o(μ²): ellipse covering, layer-cake,
    removal of period primes (R/balanced-ideal-pair-audit §One-point/§Prime factors;
    R/balanced-strip-transfer ¶4). Uses RH short-interval prime counts. The argument is sketched.
  - L19.6 [GAP] Thin and small-determinant pairs: a "fixed negative-power frequency on the
    rational-good region" (R/balanced-class-integration ¶5; R/thin-top-pairs). It gets one line in
    the balanced note.
  - L19.7 [LEAN] Mean of the ratio of numerator to denominator over the multiplier:
    `TopStripMoments.ratio_expectation_le`; prime restoration: `pruned_prime_pair_restoration_*`.
  - L19.8 [FORM] Diagonal term for η < 1/50 (R/balanced-class-integration ¶6; `DiagonalTransfer` [LEAN]).
- L20 Bad-child mass δ_1 < D^{−B} for every B
  - L20.1 [LEAN] Recurrence algebra δ_i ≤ ε_i + 4M_iK_i√δ_{i+1} and the top square-root step:
    `FieldPoolDescent.internal_linear_recurrence_*`, `top_sqrt_of_internal_linear_bound`,
    `iterated_sqrt_recurrence_pow_bound`; incidence identities: `WeightedIncidence`.
  - L20.2 [INFRA] Interior concentration ε_i ≤ D^{−2A} with A = D^{1/48}, moments of growing
    order (KB Thm 3.1, G.8, G.10, App. C). Needs: smooth-number saddle point, Hildebrand–Tenenbaum
    Ψ(x,y) asymptotics, truncated geometric CRT laws; GRH sharp smooth-character sums (KB Lemma
    G.2 p.106, via Harper/Soundararajan-type results); conditional densities D_UP. This is the
    deepest KB input, and I took it on trust from the unrefereed preprint.
  - L20.3 [FORM/GAP-mild] Applying the interior G.11 at each fixed multiplier k, then averaging in k
    (R/balanced-strip-transfer ¶"Apply the interior G.11"). The interior guard χv0 > 2v1 keeps the
    original pointwise comparison. Plausible, but the uniformity in k is asserted, not checked.
  - L20.4 [GAP] Top G.12 under the incoming-child-root law. Needs (2) of R/balanced-strip-transfer
    and the child-root-conditioned two-point bound ≤ D^{O(1)} on incoming-good parts
    ("item 3", R/polynomial-top-field-pool). The note itself warns that the unconditioned bound
    does not imply it (a factor q can be lost). For the balanced strip it is only asserted to follow
    "using (1)".
  - L20.5 [LEAN-R] Divided-strip ratio μ_q/μ ≤ D^{O(1)}:
    `TopStripMoments.centeredBinProducts_dividedStrip_ratio_from_supply`.
- L21 Elliptic-exceptional deletion fraction η = exp(−cT_B) per dyad
  - L21.1 [LEAN] Counting rich centres: `HasseIncidence.rich_hasse_centres_mul_le`.
    [LEAN-R] `EllipticAndGaussian.dyadic_hasse_exceptional_fraction_le`, `exceptional_band_weight_sum_le`.
  - L21.2 [FORM, large] RH implies smooth numbers within √p of almost all integer centres:
    twisted ζ'/ζ prime sum with Perron shifted to Re s = 2/3; Fourier L² comparison of k-fold
    convolutions; tent smoothing (R/private-elliptic-recognition §1). I checked the exponent
    bookkeeping and found no error. Needs Perron and RH log-derivative bounds; L/ProductPerron
    gives a start. About 5–10k lines.
- L22 [LEAN-R] Setup rejection without a factor is O(1/σ); derivative uniqueness:
  `MultiplierPhases.card_derivative_zero_le_one_of_diam_lt`, `derivative_failure_fraction_Ico`,
  `formContent_proper_divisor_of_prime_multiplier`.

**C5.b Private supply (H.5 analogue): a slot gives a counted shape with all parents covered, with probability ≥ exp(−(S+o(1))H)**
- L23 [LEAN-R] Split-prime band counts and genus-character bias under GRH, stable under deletion;
  principal-genus tuple fraction; repeated-prime collisions. Theorems in `ReducedFormSupply`:
  `splitPrimeBin_genus_bias_after_deletion_from_critical_line`, `principal_genus_distinct_tuple_fraction_lower`.
- L24 [LEAN-R] |G| = √N·exp(o(H)), upper and lower bounds:
  `FormGroup.reducedForms_card_le_sqrt_mul_log_pow`, `reducedForms_card_lower_from_critical_line`.
- L25 [INFRA-moderate] Principal genus = G². Every squarefree principal-genus product of split primes
  is the leading coefficient of a reduced form in G². Needs genus theory for disc −8N
  (R/quadratic-class-integration §Alternative). `TargetGenus` and `EvenDiscriminantGenus` [LEAN]
  have the abstract group and ambiguous-form pieces; form composition is still L4.
- L26 [FORM] H.20 subset-coefficient band count and slot loss exp(O(k0)) = exp(o(H))
  (KB H.5 p.134–135; R/private-band-stages). Partial: `BalancedAllocation`, `PrivateFloor` [LEAN].
- L27 Private ECM recognition: it suffices to find the least eligible prime
  - L27.1 [INFRA] Lenstra–Pomerance Thm 7.1 (failure ≤ c6^{#curves·ψ0/(√p log y)}). Needs elliptic
    curves over Z/nZ with gcd exits, the Hasse bound, and Deuring/Lenstra counts of curves with
    given order (Hurwitz class numbers). Mathlib has the Weierstrass group law over fields only.
  - L27.2 [LEAN-R] Recursive splitting soundness and failure ≤ δ_small + log2(m)·δ_split
    (abstract splitter): `EllipticAndGaussian.twoStageRecognizer_fail_le`, `recursiveEllipticFactor_*`.
  - L27.3 [FORM] Eligible primes (L21.2) ∩ good parents ≥ 1/2 of each band.

**C5.c Descent completes on covered primes (H.4 with pool)**
- L28 [LEAN] Backward-induction opportunity bounds, 3/4 recognition factor, union over the tree:
  `FieldPoolDescent.opportunity_prob_ge`, `elliptic_survivor_opportunity_prob_ge`,
  `pmf_bounded_search_fail_le_exp`.
- L29 [FORM] Uniform sampling and counting of lattice points in boxes (KB Lemma H.2 p.127).
  Partial: `LatticeWindow`, `AffineWindow`, `LatticePrimitive`.
- L30 [INFRA] Genus-two partial factorer to B (KB Prop. H.3 p.129). Needs:
  - genus-two Jacobians over F_p and Cantor arithmetic mod n;
  - the LPP order-fibre theorem ([43] Thm 1.1);
  - the RH short-interval smooth asymptotic (Younis arXiv:2409.05761, Thm 1.3, h ≥ x^{7/10});
  - Hildebrand–Tenenbaum (H.7).
  Younis is an external preprint and [33, genus2rh] is unpublished. Same INFRA for P1 (prepass).
- L31 [FORM] Covered good candidates pass recognition with probability ≥ 3/4, and enlarged quotas
  absorb the survivor fraction D^{−O(1)} (R/public-elliptic-recognition §Executing).
- L32 [FORM] Chernoff: R_shape slots give C+1 rows except with probability exp(−c(C+1)) (H.8 proof).

**C5.d Algebra after rows (about 5–15k lines, excluding Chebotarev)**
- L33 [LEAN] Rows > columns give a nonempty mask; the sparse solver failure fraction is bounded:
  `FieldExtraction.nonempty_mask_of_taggedSolverSucceeds`, `sparse_pade_nonempty_mask_failure_fraction_le`,
  `SparseDependency.binary_dependency_of_padded_minimal_annihilator`.
- L34 [INFRA] Character separation: every nonrational class in H_D is detected with probability
  ≥ 1 − 1/128. Needs:
  - unconditional effective Chebotarev (Lagarias–Odlyzko Thm 1.3) with Stark's exceptional-zero
    lemma (KB E.3 p.87–88; R/cumulative-character-probes);
  - |H_D| bound via S-units and 2-torsion of the S-class group (Lemma E.2).
  Mathlib has no Chebotarev or Dedekind-zeta zero theory. The mask compression is [FORM]
  (`ProbeCount` [LEAN]). This is the single biggest infrastructure item off the analytic core.
- L35 [LEAN] Odd degree: a square norm and a rational class give a square; homogeneous norm (E.7);
  scaled coordinates; occurrence-parity cancellation; multi-field assembly:
  `FieldExtraction.isSquare_of_odd_finrank_norm_sq`, `isSquare_norm_iff_isSquare_hom_prod_of_even_sum`,
  `isSquare_field_product_of_odd_degree_and_even_parity`, `labelProduct_sq_eq_assembled_publicRoot`.
- L36 [FORM/INFRA-moderate] Even good-ideal valuations, trivial characters and an even E_j column
  give a rational class (definition of H_D, Theorem E.4 p.89). Uses Dedekind valuations in
  non-maximal orders Z[β], with bad primes registered (R/polynomial-top-field-pool last section).
- L37 [FORM] Exact root by Hensel lifting and its evaluation map to Z/N (KB H.7 p.138, E.16–E.19).
  Partial: `EvaluationMaps`, `EvaluationNorm` [LEAN].
- L38 [LEAN] Final hidden sign probability ≥ 1/2: `assembledAttempt_hit_prob_ge`,
  `multiField_epoch_verified_split_probability_half`.

**C5.e Recognizer coupling**
- L39 [FORM] Recognizer errors in an adaptive first-error union bound ≤ 1/1024 (KB H.8 p.141).
  `trace` is shared by the ideal and actual laws, so this goes into γ, not ε.

**Prepass (needed by 0.2)**
- P1 [INFRA] An exp(o(H))-cost partial factorer that finds a factor ≤ exp((log n)^{2/3}) with
  probability ≥ exp(−δH). This is L30 at cutoff exp((log n)^{2/3}). ECM cannot replace it without
  the all-primes Hasse smoothness conjecture.

### Leaf counts (L1–L39, sub-leaves L18.x–L27.x counted separately, plus P1, plus interface items 0.1 and 0.2)
- [LEAN] 16
- [LEAN-R] 10
- [FORM] 16, including L20.3, which is also flagged [GAP-mild]
- [INFRA] 9, counting L4/L25/L36 as moderate and including P1
- [GAP] 5 (L19.4, L19.5, L19.6, L20.4, plus L20.3 as mild)
- Interface [GAP] 2 (0.1 vacuity, 0.2 rough-only)

---------------------------------------------------------------------------------------------------
## 3. Size estimates (Lean lines, order of magnitude) and order of attack

| Subtree | Estimate | Notes |
|---|---|---|
| 0.1 Cost semantics, epoch as a program | 3–8k | Prerequisite; reuse UniformBits, CappedTape, PadeCost counters |
| 0.2 Rough-branch restatement | 0.5k | Lemmas exist in SmallPrimePrepass |
| S0–S9 definitions (trace, good, data) | 5–10k | Lattice reduction, Gauss reduction, Padé exist |
| C1 | 0.3k | Trivial once `good` checks Y² |
| C2 | 2–4k without L4; +5–15k for L4 | Abstract sign fibers done |
| C3 | 2–4k | Mostly existing pieces |
| C4 | 8–20k | Long but elementary; scalar part done |
| C5.a+b, without INFRA leaves | 20–40k | Much of it is [LEAN]/[LEAN-R] glue |
| L19.4–6, L20.4 (GAP) | unknown; first write the proofs on paper | 10–30k once written |
| L20.2 KB concentration + G.2 + saddle point | 30–80k | Hildebrand–Tenenbaum, GRH smooth character sums |
| L27.1 ECM (LP Thm 7.1) | 20–50k | Hasse, Deuring counts, curves over Z/n |
| L30/P1 genus-two (H.3) | 50–100k+ | LPP fibre theorem, Younis; research-scale |
| L34 Chebotarev + Stark | 20–50k | Dedekind zeta zeros, explicit formula |
| L18.4 large sieve / G.3 | 5–15k | |
| Total | about 2·10^5 to 4·10^5 | Dominated by INFRA |

Suggested order. Each step is self-contained and on the critical path.
1. **0.1 and 0.2 first**. Without them the target is trivially true (§0).
2. Define the epoch concretely (S0–S9) in the cost model. Prove C1, C2 modulo L4, C3, and the
   pointwise C4. This is elementary and checks that the definitions are right.
3. Write a structure `EpochAnalyticInputs` whose fields are the named leaf statements, as Props
   with manuscript citations (L18.4, L19.4–6, L20.2, L20.4, L21.2, L27.1, L30, L34, L4/L25/L36).
   Prove `HardEpochAsymptoticBound` from it using the [LEAN] glue (L17, L20.1, L28, L33, L35, L38).
   This replaces one opaque hypothesis with an auditable list.
4. Close the [FORM] leaves cheapest first: L26, L29, L32, L37, L39, L21.2, L12/L13; then finish the
   [LEAN-R] repairs (L6, L7, L22–L24).
5. Get the [GAP] leaves written as complete paper proofs (L19.4–6, L20.4) before any Lean work on them.
6. INFRA last, ordered by reuse: Perron/RH explicit-formula toolkit (feeds L21.2, L30, L34) →
   ECM → Chebotarev → smooth-number asymptotics/KB App. C → genus two.

---------------------------------------------------------------------------------------------------
## 4. Most serious gaps (confidence = my confidence that it is a real gap at the stated level)

1. **Interface vacuity (0.1)**, about 95%. The hypothesis holds for a trivial epoch because
   `data`/`publicRoot` is free and noncomputable. The end-to-end theorem therefore certifies no
   algorithm. Only the instance check was not compiled.
2. **Hard-but-not-rough inputs (0.2)**, about 85%. The hypothesis quantifies over all odd composite
   non-prime-powers. The manuscripts prove epoch success only for B-rough inputs, and the epoch
   interface cannot return prepass or gcd-exit factors.
3. **Top second moment at narrow width χ ≈ 1.01 (L19.4–L19.6)**, about 80% "not a complete proof".
   This is the new analytic content behind going from 2.97/2.03 down to 1.984. It is spread over
   about six local notes, each a paragraph (Poisson quotient for the actual narrow law, dual-mode
   injectivity, twisted-Gaussian variation, thin pairs). KB's own G.19 needs σ ≳ V², and the local
   note concedes that G.19 can fail. I have no strong view on whether it is true.
4. **Child-root-conditioned two-point bound for the balanced strip (L20.4)**, about 70%. The pool
   note says this is exactly what an unconditioned bound does not give (a factor q can be lost).
   The balanced note asserts it from (1) without a displayed proof.
5. **External or unrefereed foundations (L20.2, L30, P1)**, about 50% that something there would
   fail under scrutiny. These are the KB preprint itself (G.2/G.10 concentration, H.3), the use of
   Younis' RH short-interval theorem down to w = (log x)^{K0}, and the unpublished genus2rh
   manuscript. They are not gaps in the local adaptation, but they are unverified and are the
   largest INFRA items.
6. Minor: L20.3 (uniformity of G.11 in the multiplier, about 35%) and L18.2's upper density
   (Harper Result 3 range, about 20%).
