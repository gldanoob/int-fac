# Independent audit: the five serious gaps in `research/randomized-epoch-blueprint.md` §4

Pinned tree: worktree `/home/gldanoob/dev/int-fac-randomized`, branch
`explore/randomized-one-third`, commit `0bcb1db`, Lean `leanprover/lean4:v4.33.1`
(`formal/cogentic/lean-toolchain`). This audit is read-only with respect to Lean: no
`.lean` file was edited. All line numbers are from the pinned commit.

Scope: items 1–5 of blueprint §4 ("Most serious gaps"). Item 6 (the `L20.3`/`L18.2`
minor items) is out of scope except where it bears on item 5.

## Verdict summary

| # | Blueprint gap | Verdict | Classification | Lean anchor |
|---|---|---|---|---|
| 1 | Interface vacuity (`0.1`) | **True.** A zero-work oracle epoch satisfies `HardEpochAsymptoticBound _ 0`; the instance is now kernel-checked. | (i) interface bug; the blueprint's "not compiled" caveat is (iv) discharged | `Cogentic/RandomizedEpochAssembly.lean:331,343–344,582–594`; `Cogentic/RandomizedEpochVacuity.lean:23–39,45,78–86` |
| 2 | Hard-but-not-rough inputs (`0.2`) | **True.** The endpoint hypothesis is over all odd composite non-prime-powers, with no roughness premise; the epoch can only return a hidden-sign gcd factor. Rough-branch glue exists but is not wired into the endpoint. | (i) interface bug; prepass instance is (ii)/(iii) | `RandomizedEpochAssembly.lean:424–427,582–584,681–690`; `RandomizedSmallPrimePrepass.lean:45,150,564,582,696,732,753,957–958` |
| 3 | Narrow-width top second moment (`L19.4–L19.6`) | **True as stated: no complete formal proof.** The second moment enters only as the explicit hypotheses `hf`/`hg` of an abstract Cauchy–Schwarz lemma; no Lean declaration proves G.19 at `χ ≈ 1.01`. | (ii) missing paper proof; (iii) for 2-D lattice Poisson | `RandomizedTopStripMoments.lean:597–603,897`; `RandomizedEllipticAndGaussian.lean:60,677,1354,1651` |
| 4 | Child-root-conditioned two-point bound (`L20.4`) | **True.** The top G.12 comparison is an explicit hypothesis `htop`; only the recurrence algebra is formalized. There is no Lean statement of the conditioned two-point bound. | (ii) missing paper proof | `RandomizedFieldPoolDescent.lean:561,608–614,692,737,963`; `RandomizedTopStripMoments.lean:137` |
| 5 | External/unrefereed foundations (`L20.2`, `L30`, `P1`) | **True.** No interior-concentration theorem, no genus-two/Jacobian module, no ECM theorem. The counted trial prepass is provably too weak for the `exp((log n)^{2/3})` cutoff. | (ii) missing paper proof; (iii) missing Mathlib infrastructure | `RandomizedFieldPoolDescent.lean:561,692`; `RandomizedEllipticAndGaussian.lean:2218,2288–2301`; `RandomizedSmallPrimePrepass.lean:145–151,899–900,957–958` |

---

## 1. Interface vacuity (`0.1`) — confirmed, now kernel-checked

**What the Lean statement says.** `HardEpochData` stores the transcript verifier data as
an unconstrained function and the cost as an arbitrary `ℕ`-valued function:

- `Cogentic/RandomizedEpochAssembly.lean:331` — `structure HardEpochData (N : ℕ)`.
- `:343` — `data : good → TranscriptData Label N`.
- `:344` — `pubWork : Coins × (Label → (ZMod N)ˣ) → ℕ`.

`HardEpochAsymptoticBound` (`:582–594`) constrains only the *mean* of `pubWork`
(`:589`), the hit mass `γ` (`:591–592`), the total variation (`:593`), and the final
`γ/2 − ε` (`:594`). It never relates `pubWork` to the cost of computing `trace`, the
membership test for `good`, or `data`.

**The oracle instance.** `Cogentic/RandomizedEpochVacuity.lean` now supplies exactly the
blueprint's counterexample:

- `:23–39` — `oracleEpoch` with `Coins := Unit`, `Label := Unit`,
  `Public := (ZMod N)ˣ`, `ideal = actual = uniform`, `trace := fun _ s => s ()`;
- `:31` — `good := squareSet N`;
- `:35` — `publicRoot := Classical.choose (Finset.mem_image.mp t.2)` (free choice of a
  square root);
- `:39` — `pubWork := fun _ => 0`;
- `:45` — `theorem oracleEpoch_bound : HardEpochAsymptoticBound oracleEpoch 0`;
- `:78–86` — `oracle_end_to_end`, which applies
  `serialized_assembled_epoch_from_critical_line` at `C = 0` and yields expected cost
  `exp((0 + ε) * scale n)` for every `ε > 0`.

`RandomizedEpochVacuity` is imported into the audit file at
`formal/cogentic/RandomizedFactoring.lean:153`; its two `#print axioms` lines are active
at `:237–238`. The blueprint's qualifier "I did not compile this instance" is therefore
**out of date**: the instance is compiled and kernel-checked.

**Classification.** The defect is an (i) interface bug. The audit claim itself is (iv)
already discharged by `oracleEpoch_bound`. The bug is *not* fixed: `assembledAttempt`
(`:424–427`) charges only `E.pubWork x + certifiedEpochTrial` and cannot see the cost of
producing `data`.

**What remains.** Replace the free `data`/`pubWork` pair by outputs of programs in a
fixed costed model (deep embedding or cost monad over bit operations), with
`pubWork x ≥` the model cost of running `trace`, the `good` test and `data` on `x`, and
no `Classical.choose`. Blueprint estimate: 3–8k lines (§3) or 2–5k lines (§0.1).

## 2. Hard-but-not-rough inputs (`0.2`) — confirmed; the glue exists but is not wired

**What the Lean statement says.** The endpoint hypothesis quantifies over every odd
composite non-prime-power, with no roughness premise:

- `Cogentic/RandomizedEpochAssembly.lean:582–584` —
  `HardEpochAsymptoticBound E C` is
  `∀ δ > 0, ∀ᶠ n, ∀ hN, Odd n → ¬n.Prime → ¬IsPrimePow n → ...`.
- `:681–690` — `serialized_assembled_epoch_from_critical_line` consumes
  `HardEpochAsymptoticBound E C` directly (`:684`), so the endpoint inherits the
  all-hard-inputs quantifier.

**Why the epoch cannot absorb a prepass or gcd exit.** `assembledAttempt` (`:424–427`)
returns whatever `certifiedEpochTrial` returns:
`let res := certifiedEpochTrial hN E.trace E.good E.data x`. In
`Cogentic/RandomizedEpochSuccess.lean:22–31`, `epochTrial` only uses
`data.publicRoot` through `comparisonRatio` and `verifiedTrial`; it has no path that
returns a factor found during setup, sampling, or a trial prepass. `HardEpochData` has no
field carrying a prepass factor. This is precisely the blueprint's claim.

**The rough-branch glue is [LEAN], but unused by the endpoint.**

- `Cogentic/RandomizedSmallPrimePrepass.lean:45` — `def IsRough (B : ℝ) (n : ℕ) : Prop`.
- `:145–151` — `logB n = (log n)^(2/3)` and `roughThreshold n = exp (logB n)`.
- `:564–595` — `combined_epoch_asymptotic` with the rough hypothesis at `:581–582`
  (`IsRough (B n) n`) and the small-prime branch at `:573–580`.
- `:696–728` — `combined_epoch_asymptotic_logB`, the specialization to
  `roughThreshold`.
- `:732–768` — `factor_expected_from_prepass_and_rough_epoch`, whose rough hypothesis is
  at `:752–753` (`IsRough (B n) n`).

None of these is called by `serialized_assembled_epoch_from_critical_line`. The
reduction from "all hard inputs" to "rough inputs + prepass" is proved but not composed
with the endpoint.

**The counted trial prepass is too weak for `P1`.** `:957–961` states
`trialPrepass_mean_work_le_exp` under the hypothesis `hB : ∀ ε > 0, ∀ᶠ n,
(B n : ℝ) ≤ exp (ε * scale n)` (`:958`). With `scale n = (log n)^{1/3}
(loglog n)^{2/3}`, the required cutoff `roughThreshold n = exp((log n)^{2/3})`
(`:145–151`) has exponent ratio `(log n)^{2/3} / (ε · scale n) → ∞`, so `hB` is false
for that cutoff. `trialPrepass_work_le` (`:899–900`) gives the matching
`54 · B · n.size²` cost, i.e. `exp((log n)^{2/3} + o(1))`. Trial division therefore
cannot discharge `P1`.

**Classification.** (i) interface bug at the endpoint; the missing concrete prepass is
(ii)/(iii). The rough-branch restatement itself is already [LEAN].

**What remains.** Restate the endpoint through `combined_epoch_asymptotic_logB` or
`factor_expected_from_prepass_and_rough_epoch`, then supply a real `preEpoch`/`preAttempt`
meeting `hPreWork`/`hSmall` — the genus-two (KB H.3) or ECM partial factorer `P1` with
`exp(o(H))` cost. Blueprint estimate: 0.5k lines for the restatement, plus the `P1`
infrastructure.

## 3. Narrow-width top second moment (`L19.4–L19.6`) — no complete proof in Lean

**What is formalized.** The averaged Fourier/GRH input and the abstract Cauchy–Schwarz
step are present, but the second moment itself is an assumption:

- `Cogentic/RandomizedTopStripMoments.lean:597–603` —
  `coupled_mode_cauchy_schwarz` takes
  `hf : ∑ w o * ∑ a, f o a ^ 2 ≤ E₁ ^ 2` (`:601`) and the analogous `hg` (`:602`) as
  hypotheses. It does not prove either energy bound.
- `:897–947` — `primeBinProducts_averaged_coupled_abel_from_critical_line` is the GRH
  grid-prefix/Abel assembly (blueprint `L19.2`), not the narrow-width G.19 bound. It
  still assumes the marginal, row/column-zero, variation and `V` hypotheses
  (`:924–931`).

**What is missing.**

- `L19.4` (Poisson quotient for the actual discrete Gaussian two-mark law): the Poisson
  identities are one-dimensional. In the randomized module,
  `Cogentic/RandomizedEllipticAndGaussian.lean:60` is the private
  `shifted_gaussian_poisson`, reused at `:143`; the public one-dimensional residue bound
  is `:677` (`gaussian_residue_class_prob_interval`). The tree also has the public 1-D
  `Cogentic/ConditionalGaussian.lean:45` (`shifted_gaussian_poisson`). There is no 2-D
  correlated-Gaussian Poisson statement.
- `L19.5` (ideal zero-mode bound): the Mahalanobis *geometry* is present —
  `:1354` (`mahalanobis_2d_lattice_mass_bounds`) and `:1651`
  (`mahalanobis_2d_discarded_radius_rpow_le`) — but those are the `L19.3` pieces. No
  theorem bounds the ideal zero mode.
- `L19.6` (thin and small-determinant pairs): no declaration.

The `χ ≈ 1.01` scalar gate at
`Cogentic/RandomizedBalancedFiniteSchedule.lean:139` (`hχu : p.χ ≤ 1.01`) and
`Cogentic/RandomizedWidthOneGate.lean:140` is a *cost/schedule* gate, not the second
moment; it does not substitute for G.19.

**Classification.** (ii) missing paper proof, with (iii) missing Mathlib
infrastructure for 2-D lattice Poisson summation. The blueprint's "not a complete proof"
is accurate; the formal development is conditional exactly where the blueprint says it
is.

**What remains.** Write the Poisson quotient, dual-mode injectivity, twisted-Gaussian
variation, and thin-pair arguments as complete paper proofs first; then formalize them.
The abstract `coupled_mode_cauchy_schwarz` and the Mahalanobis geometry are reusable.

## 4. Child-root-conditioned two-point bound (`L20.4`) — assumed, not proved

**What is formalized.** Only the recurrence algebra and the unconditional divided-strip
ratio:

- `Cogentic/RandomizedFieldPoolDescent.lean:561` —
  `internal_linear_recurrence_bound` (G.11 algebra);
- `:608–614` — `top_sqrt_of_internal_linear_bound`, with the top G.12 comparison as the
  explicit hypothesis `htop : δ_top ≤ C_top * (√(δ_int 0) + √ε_in + η)` (`:612`);
- `:692` — `iterated_sqrt_recurrence_pow_bound` (iterated square-root algebra);
- `:737` — `opportunity_prob_ge`; `:963` — `pmf_descentTree_from_elliptic_opportunities`
  (both take per-node opportunity/survivor probabilities as hypotheses);
- `Cogentic/RandomizedTopStripMoments.lean:137` —
  `centeredBinProducts_dividedStrip_ratio_from_supply` is the unconditional divided-strip
  ratio `L20.5`, not the conditioned two-point bound.

No Lean declaration states the bound "top G.12 under the incoming-child-root law" or the
required "child-root-conditioned two-point bound ≤ D^{O(1)} on incoming-good parts". The
`ε_in`/`htop` hypotheses are exactly where that input would enter.

**Classification.** (ii) missing paper proof. The formal glue is conditional and not
wrong; the gap is the analytic inequality, not an interface defect.

**What remains.** Produce the paper proof that the unconditioned bound upgrades to the
child-root-conditioned bound (the blueprint warns a factor `q` can be lost), then expose
it as a named `Prop` and discharge `htop`. The `L20.5` ratio theorem removes the easy
`q`-factor bookkeeping but does not supply the conditioned two-point estimate.

## 5. External or unrefereed foundations (`L20.2`, `L30`, `P1`) — absent or hypothesis-only

**`L20.2` interior concentration.** There is no theorem bounding
`ε_i ≤ D^{−2A}`. The recurrence consumers take `ε_rat`/`ε_in` as hypotheses
(`Cogentic/RandomizedFieldPoolDescent.lean:561,692`). `Cogentic/RandomizedSmoothDensity`
contains the density lower bounds (`:413`, `:622`) and the Rankin upper bound
(`:884`, `smoothCount_rankin_upper`), but density is not the KB G.8/G.10 interior
concentration. Missing: smooth-number saddle point, Hildebrand–Tenenbaum asymptotics,
truncated geometric CRT laws, GRH smooth-character sums.

**`L30` genus-two partial factorer.** There is no genus-two/Jacobian/Cantor module in
`formal/cogentic/Cogentic` (a case-insensitive search for
`genus two|genus_two|genus2|Jacobian|Cantor` matches only unrelated text in
`RandomizedEllipticAndGaussian.lean`). No declaration states KB Prop. H.3 or the LPP
order-fibre theorem.

**`L27.1` ECM.** ECM is abstracted, never proved:
`Cogentic/RandomizedEllipticAndGaussian.lean:2288–2303`
(`twoStageRecognizer_fail_le`) assumes an arbitrary `ellipticSplit` and the failure bound
`hsplit_fail` at `:2299–2301`; `:2218`
(`recursiveEllipticFactor_fail_le_log2`) is the recursive bookkeeping. The Lenstra–Pomerance
Thm 7.1 bound is not in Lean; `:1766`
(`dyadic_hasse_exceptional_fraction_le`) is a Hasse-incidence count, not an ECM runtime
theorem.

**`P1` prepass.** As in §2, `trialPrepass_mean_work_le_exp`
(`Cogentic/RandomizedSmallPrimePrepass.lean:957–958`) only covers
`B ≤ exp(ε · scale n)`, which excludes the required
`roughThreshold = exp((log n)^{2/3})` (`:145–151`). There is no genus-two prepass.

**Classification.** (ii) missing paper proof for KB G.2/G.8/G.10, H.3 and the
`genus2rh`/Younis inputs; (iii) missing Mathlib infrastructure for Dedekind-zeta/Perron
machinery, smooth-number asymptotics, curves over `Z/n`, and 2-D lattice Poisson.

**What remains.** Keep these as named, cited `Prop` leaves in an
`EpochAnalyticInputs`-style structure rather than one opaque hypothesis; do not claim
the numerical bound. This matches the blueprint's suggested order (paper proofs for
`L19.4–6`/`L20.4`, then INFRA ordered by reuse).

---

## Prioritized remaining work

Ordered by dependency, not by expected effort. "Exit criterion" is the check that
retires the row.

| Priority | Work item | Gap | Why here | Exit criterion | Rough size |
|---|---|---|---|---|---|
| P0 | Replace free `data`/`pubWork` with a costed program model; forbid `Classical.choose` in `data`; require `pubWork ≥` model cost | 1 | Without it the endpoint certifies no algorithm, so later analytic work cannot change the headline | A costed `HardEpochData` variant whose `oracleEpoch` fails the cost condition; vacuity theorem no longer applies | 3–8k lines |
| P1 | Wire the endpoint through `combined_epoch_asymptotic_logB` / `factor_expected_from_prepass_and_rough_epoch`; require `HardEpochAsymptoticBound` only on `IsRough` | 2 | Cheap and already [LEAN]; removes the all-inputs mismatch | Endpoint theorem has an `IsRough` premise plus a prepass epoch interface | ~0.5k lines |
| P2 | Build the concrete prepass epoch (`P1`/`L30` genus-two, or ECM) with `exp(o(H))` cost and success `≥ exp(−δH)` | 2, 5 | The rough restatement is useless without it; `trialPrepass` is provably too weak | An instance of the prepass interface meeting `hPreWork`/`hSmall` at `roughThreshold` | 50–100k+ lines |
| P3 | Write complete paper proofs of `L19.4–L19.6` (2-D Poisson quotient, dual-mode injectivity, twisted-Gaussian variation, thin pairs) | 3 | The narrow-width second moment is the main new analytic claim behind 1.984 | A named `Prop` per leaf with displayed constants, then `htop`/`hf`/`hg` discharged | 10–30k lines after paper |
| P4 | Write the child-root-conditioned two-point proof (`L20.4`) | 4 | Needed for the top G.12 step; the note itself flags the unconditioned bound as insufficient | `htop` discharged from a named conditioned-two-point `Prop` | included above |
| P5 | Expose `L20.2` concentration and the remaining external inputs as explicit `Prop` fields; do not hide them in one hypothesis | 5 | Makes the residual trust auditable; enables parallel work | `EpochAnalyticInputs` structure and a reduction theorem depending only on its fields | 2–5k lines glue |
| P6 | Formalize `L20.2` KB G.2/G.8/G.10, then ECM/Chebotarev/genus-two infrastructure | 5 | Largest INFRA; do after the paper-level leaves are stable | Compiled leaves replacing the corresponding `Prop` fields | 100k+ lines |

## Exact reproduction commands

All Lean commands assume:

```sh
cd /home/gldanoob/dev/int-fac-randomized/formal/cogentic
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
```

### Gap 1 — interface vacuity / oracle epoch

```sh
grep -n "structure HardEpochData\|data : good\|pubWork :\|def HardEpochAsymptoticBound\|mean (E n hN).actual" Cogentic/RandomizedEpochAssembly.lean
grep -n "oracleEpoch\|pubWork := fun _ => 0\|Classical.choose\|oracleEpoch_bound\|oracle_end_to_end" Cogentic/RandomizedEpochVacuity.lean
flock /tmp/intfac-lean.lock -c 'cd /home/gldanoob/dev/int-fac-randomized/formal/cogentic && LEAN_NUM_THREADS=1 lake env lean Cogentic/RandomizedEpochVacuity.lean'
```

The compile prints the axioms of `oracleEpoch_bound` and `oracle_end_to_end`
(`RandomizedEpochVacuity.lean:88–89`).

### Gap 2 — all-hard-inputs quantifier vs. rough branch

```sh
grep -n "Odd n → ¬n.Prime → ¬IsPrimePow n" Cogentic/RandomizedEpochAssembly.lean Cogentic/RandomizedSmallPrimePrepass.lean
grep -n "def IsRough\|roughThreshold\|combined_epoch_asymptotic\|factor_expected_from_prepass_and_rough_epoch\|trialPrepass_mean_work_le_exp" Cogentic/RandomizedSmallPrimePrepass.lean
grep -n "certifiedEpochTrial\|assembledAttempt" Cogentic/RandomizedEpochAssembly.lean Cogentic/RandomizedEpochSuccess.lean
flock /tmp/intfac-lean.lock -c 'cd /home/gldanoob/dev/int-fac-randomized/formal/cogentic && LEAN_NUM_THREADS=1 lake env lean Cogentic/RandomizedSmallPrimePrepass.lean'
```

### Gap 3 — narrow-width second moment

```sh
grep -n "theorem coupled_mode_cauchy_schwarz\|hf :\|hg :\|primeBinProducts_averaged_coupled_abel_from_critical_line" Cogentic/RandomizedTopStripMoments.lean
grep -n "shifted_gaussian_poisson\|gaussian_residue_class_prob_interval\|mahalanobis_2d_lattice_mass_bounds\|mahalanobis_2d_discarded_radius_rpow_le" Cogentic/RandomizedEllipticAndGaussian.lean
grep -rn "theorem .*poisson\|theorem .*Poisson\|two-point\|twoPoint" Cogentic/Randomized*.lean
flock /tmp/intfac-lean.lock -c 'cd /home/gldanoob/dev/int-fac-randomized/formal/cogentic && LEAN_NUM_THREADS=1 lake env lean Cogentic/RandomizedTopStripMoments.lean'
```

### Gap 4 — child-root-conditioned two-point bound

```sh
grep -n "htop :\|theorem top_sqrt_of_internal_linear_bound\|theorem iterated_sqrt_recurrence_pow_bound\|theorem pmf_descentTree_from_elliptic_opportunities" Cogentic/RandomizedFieldPoolDescent.lean
grep -rn -i "child.root\|childRoot\|conditioned.*two.point\|two.point.*conditioned" Cogentic/Randomized*.lean
flock /tmp/intfac-lean.lock -c 'cd /home/gldanoob/dev/int-fac-randomized/formal/cogentic && LEAN_NUM_THREADS=1 lake env lean Cogentic/RandomizedFieldPoolDescent.lean'
```

### Gap 5 — external/unrefereed foundations

```sh
grep -rn -i "genus.two\|genus_two\|genus2\|Jacobian\|Cantor\|Lenstra" Cogentic/*.lean
grep -n "hsplit_fail\|ellipticSplit :" Cogentic/RandomizedEllipticAndGaussian.lean
grep -n "hB :\|trialPrepass_work_le\|trialPrepass_mean_work_le_exp" Cogentic/RandomizedSmallPrimePrepass.lean
grep -rn -i "concentration\|Hildebrand\|Tenenbaum\|saddle" Cogentic/Randomized*.lean
flock /tmp/intfac-lean.lock -c 'cd /home/gldanoob/dev/int-fac-randomized/formal/cogentic && LEAN_NUM_THREADS=1 lake env lean Cogentic/RandomizedEllipticAndGaussian.lean'
```

### End-to-end audit target

```sh
cd /home/gldanoob/dev/int-fac-randomized
make -n check-randomized-end-to-end
flock /tmp/intfac-lean.lock -c 'cd /home/gldanoob/dev/int-fac-randomized && PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1 make check-randomized-end-to-end'
```

## Changes since the blueprint was written

- Blueprint §4.1 says the vacuity instance was "not compiled". It is now compiled:
  `Cogentic/RandomizedEpochVacuity.lean:45,78` and the audit file's active prints at
  `RandomizedFactoring.lean:237–238`. The claim is verified; the interface bug remains.
- Blueprint §4.2's suggested fix is already available as [LEAN] glue
  (`combined_epoch_asymptotic_logB`, `factor_expected_from_prepass_and_rough_epoch`) but
  is not composed with the endpoint. The residual is the concrete prepass (`P1`), not the
  rough-branch restatement.
- Blueprint §4.5's "Rankin may suffice" for the `L18.2` upper density is now concrete:
  `RandomizedSmoothDensity.smoothCount_rankin_upper` at `:884`. That does not address
  the `L20.2` interior concentration, which remains absent.
- The `L19.2`/`L20.1`/`L20.5` [LEAN] components cited in the blueprint are present in
  the expected files. None of them closes gaps 3–5.

## Recorded run (2026-11-27)

Commands:

```sh
cd /home/gldanoob/dev/int-fac-randomized
make -n check-randomized-end-to-end
flock /tmp/intfac-lean.lock -c 'cd /home/gldanoob/dev/int-fac-randomized && PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1 make check-randomized-end-to-end'
```

`make -n` output:

```text
cd formal/cogentic && "lake" env lean Cogentic/RandomizedEpochVacuity.lean
cd formal/cogentic && "lake" env lean RandomizedFactoring.lean
```

The real run exited 0 and produced 82 `#print axioms` lines, all of the form
`depends on axioms: [propext, Classical.choice, Quot.sound]`. Full output:

```text
cd formal/cogentic && "lake" env lean Cogentic/RandomizedEpochVacuity.lean
'Cogentic.RandomizedEpochAssembly.Vacuity.oracleEpoch_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedEpochAssembly.Vacuity.oracle_end_to_end' depends on axioms: [propext, Classical.choice, Quot.sound]
cd formal/cogentic && "lake" env lean RandomizedFactoring.lean
'Cogentic.Randomized.finite_grid_schedule_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.elliptic_recognition_cost_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedSignCount.proper_sign_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedSparseSchedule.private_gate_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedSparseSchedule.terminal_costs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedSparseSchedule.other_costs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedCRTSigns.proper_gcd_of_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.exact_finite_grid_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.algebraicCost_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedOddSplit.hidden_split_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.radix_only_search_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.free_rational_search_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.terminal_search_gnfs_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.terminal_gnfs_equality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.sharp_strict_scaled_finite_schedule_infimum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedSamplerTransfer.mapped_transcript_indicator_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedSamplerTransfer.deficient_weights_totalVariation_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.Randomized.cutoff_crossing_cost_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.sharp_classSchedule_infimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedReducedFormRoot.normalized_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedReducedFormMinimum.leading_square_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedClassSignFibers.square_global_sign_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedFormDivisor.normalize_private_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.zmod_quadratic_normalized_not_global_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedGenusMixing.identity_mass_bias' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.half_width_at_least_353_stages' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedEvenDiscriminantGenus.primitive_reduced_ambiguous_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedTargetGenus.target_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedFormReduction.Result.first_column' depends on axioms: [propext]
'Cogentic.RandomizedFormReduction.strictSwapCount_le_log2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedReductionSteps.gauss_strict_swap_count_le_log2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedQuadraticTargetRoot.targeted_first_column_root_mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedGenusMixing.equal_label_pair_count_after_deleting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedConductorCount.unsaturated_prefix' depends on axioms: [propext, Quot.sound]
'Cogentic.Randomized.narrow_envelope_37_20_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedFormReductionSize.reduce_size_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.narrow_envelope_endpoint_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.narrow_envelope_endpoint_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedRectangularAbel.norm_sum_le_prefix_bound_mul_variation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.Randomized.survivorMoment_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedPoolCoverage.poolMissMass_le_card_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedMarginalModes.coupled_mode_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.balanced_envelope_endpoint_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.balanced_envelope_endpoint_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedWidthOneGate.fixed_stage_gate_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedTopCoefficientDet.det_quadratic_topProjection_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedPrimeDetNullity.finrank_ker_eq_one_of_dvd_not_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedCubicBoxChart.card_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedSubsetFiber.card_le_choose_mul_card_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedFixedMoebius.transform_norm_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedPrimitiveQuadraticRoot.square_discriminant_of_common_multiple' depends on axioms: [propext,
 Quot.sound]
'Cogentic.Randomized.prime_dvd_quadraticPencilMap_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedClassMajority.card_goodChoices_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedWeightedIncidence.sum_incident_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedCenteredBoxRatio.card_centeredBox_dilate_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedSplitWork.expected_work_le_log2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.primeBin_product_from_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.primeBin_product_prefix_from_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.Randomized.balanced_finite_private_low_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.Randomized.serviceStates_at_deadline' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedUniformBits.expectedCoins_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedHiddenOutputLaw.comparisonRatio_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedEpochKernel.repeatedKernel_mean_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedCostedFactorLaw.expectedCost_eventually_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedInputDriver.factor_expected_from_hard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedSerializedDriver.serializedFactor_expected_eventually' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedInputDriver.serialized_epoch_from_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedEpochSuccess.epoch_verified_split_probability_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.Randomized.primeBinProducts_gridPrefix_from_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedEpochAssembly.serialized_assembled_epoch_from_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedEpochAssembly.serialized_assembled_balancedEnvelopeInfimum_from_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedUniversalSchedule.serialized_balancedEnvelopeInfimum_from_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedFieldExtraction.multiField_epoch_verified_split_probability_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedWholeTreeTape.fairSerializedFactorTree_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedWholeTreeTape.fair_whole_tree_from_critical_line' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedFieldPoolDescent.pmf_descentTree_from_elliptic_opportunities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.Randomized.pruned_prime_pair_restoration_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedSmallPrimePrepass.trialPrepass_mean_work_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Cogentic.RandomizedEpochAssembly.Vacuity.oracleEpoch_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cogentic.RandomizedEpochAssembly.Vacuity.oracle_end_to_end' depends on axioms: [propext, Classical.choice, Quot.sound]
```
