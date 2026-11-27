import Cogentic.RandomizedEpochAnalyticInputs

/-!
# Paper-level statements for the twelve randomized analytic leaves

`Cogentic.RandomizedEpochAnalyticInputs.C5Inputs` records one *loss slot* per
analytic leaf of `research/randomized-epoch-blueprint.md` §2, and each slot is
the weakened eventuality `≤ exp (-2 * scale n)`.  The slots are the right objects
for the arithmetic assembly, but they are not the manuscript's statements: the
paper proves, for instance, `ε_i ≤ D^{-2A}` with `A = D^{1/48}` (L20.2), an ECM
failure bound `c₆^{#curves · ψ₀ / (√p log y)}` (L27.1), and
effective-Chebotarev errors of size `exp (-c H / log H)` (L34).  This file
separates the two layers.

`PaperAnalyticAssumptions E C` has exactly twelve fields, one per leaf.  Each
field carries

* the leaf's *deficit* `loss`, the real number that the C5 ledger charges;
* the manuscript's own rate statement about that deficit; and
* only where the manuscript rate does not by itself beat the ledger rate, an
  explicit extra estimate.  `L21.2`, `L27.1`, and `L34` are the three such
  leaves: their quoted rates are `exp (-c H / log H)`, a curve-count rate, and
  an effective-Chebotarev error, none of which is `≤ exp (-2 H)`.  The paper's
  actual counting (union bounds over dyads, curves, and probes) does yield the
  stronger `D^{-B}` form, but the current `HardEpochData` interface does not
  expose that counting, so the stronger form is an explicit field rather than a
  silently assumed axiom.

Throughout, the paper's size `D` is read as `exp (scale n)`, i.e. `log D` is the
ledger's `H = scale n`; this is the convention already implicit in `C5Inputs`
(whose docstrings translate the paper's `D^{-B}` into
`exp (-(2 : ℝ) * scale n)`).

The main result `epochAnalyticInputs_of_paperAssumptions` composes the twelve
paper fields with C1-C4 and the C5 `hitMass` bridge into the existing
`EpochAnalyticInputs` ledger, and
`hardEpochAsymptoticBound_of_paperAssumptions` feeds that into
`hardEpochAsymptoticBound_of_analyticInputs`.  Nothing here proves a paper lemma;
the file is the auditable reduction from the manuscript's statements to the
kernel-checked ledger.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedPaperLeafStatements

open Filter Real
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The two generic paper-leaf shapes -/

/-- The manuscript's standard conclusion for a C5 leaf: for every `B`, the
deficit is at most `D^{-B}`, with `D` read as `exp (scale n)`.  This is the
paper's shape (`D^{-B}` for every `B`), not the ledger's single-instant
`exp (-2 * scale n)`. -/
def SubexpLoss (loss : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, 0 < B → ∀ᶠ n : ℕ in atTop, loss n ≤ exp (-B * scale n)

/-- A leaf whose manuscript conclusion is already `D^{-B}` for every `B`.
The ledger slot is the `B = 2` instance. -/
structure SubexpLeaf where
  /-- The real deficit charged to the C5 ledger for this leaf. -/
  loss : ℕ → ℝ
  /-- The deficit is a loss, hence nonnegative. -/
  loss_nonneg : ∀ n, 0 ≤ loss n
  /-- Manuscript statement: `loss n ≤ D^{-B}` for every `B > 0`. -/
  paper : SubexpLoss loss

/-- The `B = 2` instance of the paper statement is exactly the ledger slot. -/
theorem SubexpLeaf.slot (h : SubexpLeaf) :
    ∀ᶠ n : ℕ in atTop, h.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  h.paper 2 (by norm_num)

/-- A leaf whose manuscript rate does **not** imply the ledger slot on its own.
`paper` is the quoted rate (`exp (-(c * rate n))`, e.g. `exp (-c H / log H)` for
L21.2/L34 or `c₆^m` for L27.1), and `ledger` is the explicit extra estimate that
the paper's actual counting supplies and that the ledger consumes.  This is the
"add the missing estimate as a field, not as an axiom" branch of the design. -/
structure RatedLeaf where
  /-- The real deficit charged to the C5 ledger for this leaf. -/
  loss : ℕ → ℝ
  /-- The deficit is a loss, hence nonnegative. -/
  loss_nonneg : ∀ n, 0 ≤ loss n
  /-- The paper's rate function `T` in the failure bound `exp (-(c * T n))`. -/
  rate : ℕ → ℝ
  /-- The rate constant. -/
  c : ℝ
  /-- The rate constant is positive. -/
  c_pos : 0 < c
  /-- Manuscript statement, at the manuscript's own rate. -/
  paper : ∀ᶠ n : ℕ in atTop, loss n ≤ exp (-(c * rate n))
  /-- Explicit extra estimate: the paper's counting yields `D^{-B}` for every
  `B`, in particular the ledger's `B = 2`.  This is *not* derivable from
  `paper` when the manuscript rate is only `exp (-c H / log H)`. -/
  ledger : ∀ᶠ n : ℕ in atTop, loss n ≤ exp (-(2 : ℝ) * scale n)

/-- The ledger slot of a `RatedLeaf` is its explicit extra estimate. -/
theorem RatedLeaf.slot (h : RatedLeaf) :
    ∀ᶠ n : ℕ in atTop, h.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  h.ledger

/-- When the manuscript rate *does* dominate the ledger rate, the quoted rate
alone suffices.  (`L21.2`, `L27.1`, and `L34` do not satisfy `hdom` at their
quoted rates, which is why `RatedLeaf` carries `ledger`.) -/
theorem RatedLeaf.slot_of_rate_dominates (h : RatedLeaf)
    (hdom : ∀ B : ℝ, 0 < B → ∀ᶠ n : ℕ in atTop, B * scale n ≤ h.c * h.rate n) :
    ∀ᶠ n : ℕ in atTop, h.loss n ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [h.paper, hdom 2 (by norm_num)] with n hpaper hrate
  exact hpaper.trans (exp_le_exp.mpr (by nlinarith only [hrate]))

/-- L20.2's manuscript shape: the interior concentration
`ε_i ≤ D^{-2A}` with `A = D^{a}` (`a = 1/48` in the paper).  With `log D = scale n`
this is `exp (-2 * exp (a * scale n) * scale n)`, which is far stronger than the
ledger slot. -/
structure ConcentrationLeaf where
  /-- The real deficit charged to the C5 ledger for this leaf. -/
  loss : ℕ → ℝ
  /-- The deficit is a loss, hence nonnegative. -/
  loss_nonneg : ∀ n, 0 ≤ loss n
  /-- The exponent `a` in `A = D^a`; the manuscript has `a = 1/48`. -/
  a : ℝ
  /-- The concentration exponent is positive. -/
  a_pos : 0 < a
  /-- Manuscript statement: `loss n ≤ D^{-2A}` with `A = D^a`. -/
  paper : ∀ᶠ n : ℕ in atTop,
    loss n ≤ exp (-(2 : ℝ) * exp (a * scale n) * scale n)

/-- The manuscript concentration bound implies the ledger slot. -/
theorem ConcentrationLeaf.slot (h : ConcentrationLeaf) :
    ∀ᶠ n : ℕ in atTop, h.loss n ≤ exp (-(2 : ℝ) * scale n) := by
  filter_upwards [h.paper, scale_grows.eventually_ge_atTop 1] with n hpaper hs
  have hs0 : 0 ≤ scale n := zero_le_one.trans hs
  have hA : 1 ≤ exp (h.a * scale n) :=
    one_le_exp (mul_nonneg h.a_pos.le hs0)
  have hmul : scale n ≤ exp (h.a * scale n) * scale n := by
    simpa using mul_le_mul_of_nonneg_right hA hs0
  exact hpaper.trans (exp_le_exp.mpr (by nlinarith only [hmul]))

/-- L4/L25/L36's manuscript shape: the class-group, principal-genus, and
valuation inputs are *exact* identifications (form composition, `principal genus
= G²`, even valuations giving a rational class), so they contribute no analytic
error and the ledger slot is the zero deficit. -/
structure AlgebraicLeaf where
  /-- The real deficit charged to the C5 ledger for this leaf. -/
  loss : ℕ → ℝ
  /-- The deficit is a loss, hence nonnegative. -/
  loss_nonneg : ∀ n, 0 ≤ loss n
  /-- The manuscript input is an identity, so the deficit is zero. -/
  loss_zero : ∀ n, loss n = 0

/-- An exact algebraic leaf satisfies the ledger slot. -/
theorem AlgebraicLeaf.slot (h : AlgebraicLeaf) :
    ∀ᶠ n : ℕ in atTop, h.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  Eventually.of_forall fun n => by
    rw [h.loss_zero n]
    exact (exp_pos _).le

/-- P1's manuscript shape: a partial factorer below `exp ((log n)^{2/3})` that
succeeds with probability `≥ exp (-δ H)` for every `δ > 0` and costs
`exp (o(H))`.  The success side is exactly the `SubexpLoss` shape; the cost
exponent is recorded for audit, but the C5 ledger does not consume it (C4
charges the work). -/
structure P1Leaf where
  /-- The real deficit charged to the C5 ledger for this leaf. -/
  loss : ℕ → ℝ
  /-- The deficit is a loss, hence nonnegative. -/
  loss_nonneg : ∀ n, 0 ≤ loss n
  /-- Manuscript statement: the miss probability is `≤ exp (-δ H)` for every
  `δ > 0`. -/
  paper : SubexpLoss loss
  /-- The prepass cost exponent, i.e. the prepass costs `exp (costExponent n)` up
  to polynomial factors. -/
  costExponent : ℕ → ℝ
  /-- The cost exponent is nonnegative. -/
  costExponent_nonneg : ∀ n, 0 ≤ costExponent n
  /-- Manuscript statement: the prepass cost is `exp (o(H))`. -/
  cost_sublinear : ∀ δ : ℝ, 0 < δ →
    ∀ᶠ n : ℕ in atTop, costExponent n ≤ δ * scale n

/-- P1's `δ = 2` instance is the ledger slot. -/
theorem P1Leaf.slot (h : P1Leaf) :
    ∀ᶠ n : ℕ in atTop, h.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  h.paper 2 (by norm_num)

/-! ## The twelve paper leaf assumptions -/

/-- The paper-level analytic assumptions behind `EpochAnalyticInputs E C`.

`E` and `C` index the structure exactly as they index `EpochAnalyticInputs`, so
that wave-2's endpoint can quantify over an epoch family and a cost exponent.
At the current `HardEpochData` interface the manuscript's leaf statements do not
mention the epoch data at all: `HardEpochData` exposes only the transcript
verifier, and the field pool, moment functionals, and recognizer events that the
paper's leaves quantify over are not part of it.  That is why the leaves are
recorded as deficits on the input size, and why the C5.a-e assembly bridge is a
separate hypothesis (`hitMass`) rather than a field here.

Every field cites the blueprint item and the KeyBreak (KB) manuscript lemma it
transcribes. -/
structure PaperAnalyticAssumptions (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) where
  /-- **L18.4** (blueprint §2, C5.a, `[INFRA]`): rational-good environments at
  the shrunken denominator interval.  KB Lemma G.3 p.107 (large sieve); RH prime
  counts in cells; `research/balanced-ideal-pair-audit.md` §1.  The manuscript
  proves `D^{-B}` for every `B`. -/
  l18_4 : SubexpLeaf
  /-- **L19.4** (blueprint §2, C5.a, `[GAP]`): Poisson quotient for the actual
  discrete Gaussian two-mark law at narrow width `σ = V^{1.01}`.  KB G.19;
  `research/mixed-strip-moment.md` §Denominator,
  `research/narrow-top-moment.md`, `research/gaussian-variation.md`,
  `research/dual-major-arc-count.md`.  The manuscript's raw statement is a
  second-moment bound; the deficit recorded here is the resulting `D^{-B}` loss,
  whose conversion is the [LEAN] ratio/Paley–Zygmund assembly of L19.7/L19.8 in
  `RandomizedTopStripMoments` (`ratio_expectation_le`,
  `coupled_mode_cauchy_schwarz`). -/
  l19_4 : SubexpLeaf
  /-- **L19.5** (blueprint §2, C5.a, `[GAP]`): ideal zero-mode bound
  `D^{O(1)} μ_q² + o(μ²)`.  KB G.19; `research/balanced-ideal-pair-audit.md`
  §One-point/§Prime factors, `research/balanced-strip-transfer.md` ¶4.  Same
  conversion to the `D^{-B}` deficit as L19.4. -/
  l19_5 : SubexpLeaf
  /-- **L19.6** (blueprint §2, C5.a, `[GAP]`): thin and small-determinant pairs,
  a fixed negative-power frequency on the rational-good region.  KB G.19;
  `research/balanced-class-integration.md` ¶5, `research/thin-top-pairs.md`. -/
  l19_6 : SubexpLeaf
  /-- **L20.2** (blueprint §2, C5.a, `[INFRA]`): interior concentration
  `ε_i ≤ D^{-2A}` with `A = D^{1/48}`.  KB Thm 3.1, G.8, G.10, App. C, and
  Lemma G.2 p.106; smooth-number saddle point, Hildebrand–Tenenbaum,
  truncated geometric CRT laws, GRH smooth-character sums.  Recorded as the
  concentration shape (`a = 1/48`). -/
  l20_2 : ConcentrationLeaf
  /-- **L20.4** (blueprint §2, C5.a, `[GAP]`): top G.12 under the incoming
  child-root law, including the child-root-conditioned two-point bound
  `≤ D^{O(1)}` on incoming-good parts.  KB G.12;
  `research/balanced-strip-transfer.md` (2) and
  `research/polynomial-top-field-pool.md` "item 3".  The `D^{O(1)}` constant is
  turned into `D^{-B}` for every `B` by the [LEAN] iterated square-root
  recurrence of L20.1 (`internal_linear_recurrence_bound`,
  `top_sqrt_of_internal_linear_bound`, `iterated_sqrt_recurrence_pow_bound` in
  `RandomizedFieldPoolDescent`); the deficit recorded here is that conclusion. -/
  l20_4 : SubexpLeaf
  /-- **L21.2** (blueprint §2, C5.a, `[FORM, large]`): under RH, smooth numbers
  lie within `√p` of almost all integer centres, giving deletion fraction
  `η = exp (-c T_B)` per dyad.  `research/private-elliptic-recognition.md` §1
  (twisted `ζ'/ζ` prime sum, Perron at `Re s = 2/3`, Fourier `L²` comparison,
  tent smoothing).  `rate` is the paper's `T_B`; because
  `T_B ≈ H / log H`, the quoted rate does not by itself give the ledger's
  `exp (-2 H)`, so `ledger` records the stronger estimate the paper's dyadic
  union bound supplies. -/
  l21_2 : RatedLeaf
  /-- **L27.1** (blueprint §2, C5.b, `[INFRA]`): Lenstra–Pomerance Thm 7.1,
  ECM failure `≤ c₆^{#curves · ψ₀ / (√p log y)}`.  Requires elliptic curves over
  `Z/nZ` with gcd exits, the Hasse bound, and Deuring/Lenstra curve counts;
  `research/private-elliptic-recognition.md`.  `rate` is the Thm 7.1 exponent at
  the paper's curve count; `ledger` records the `D^{-B}` deficit obtained after
  the L27.2/L27.3 recursive-splitting assembly (`twoStageRecognizer_fail_le`,
  `recursiveEllipticFactor_fail_le_log2`, `[LEAN]`). -/
  l27_1 : RatedLeaf
  /-- **L30** (blueprint §2, C5.c, `[INFRA]`): genus-two partial factorer to `B`.
  KB Prop. H.3 p.129: genus-two Jacobians over `F_p`, Cantor arithmetic mod `n`,
  the LPP order-fibre theorem, Younis' RH short-interval smooth asymptotic, and
  Hildebrand–Tenenbaum; `research/public-elliptic-recognition.md`.  The success
  probability `≥ exp (-δ H)` for every `δ > 0` is exactly the `SubexpLoss`
  shape. -/
  l30 : SubexpLeaf
  /-- **L34** (blueprint §2, C5.d, `[INFRA]`): character separation: every
  nonrational class in `H_D` is detected with probability `≥ 1 - 1/128`.  KB
  E.3 p.87–88; unconditional effective Chebotarev (Lagarias–Odlyzko Thm 1.3)
  with Stark's exceptional-zero lemma; `research/cumulative-character-probes.md`.
  The effective error is `exp (-c H / log H)`, which does not reach
  `exp (-2 H)`; `ledger` is the explicit `D^{-B}` headroom that the paper's
  `1/128` slack and probe count supply. -/
  l34 : RatedLeaf
  /-- **L4/L25/L36** (blueprint §2, C2 and C5.b/C5.d, `[INFRA-moderate]`): class
  groups of non-maximal orders (form composition / invertible ideals, the
  ideal-squaring formula, global-sign invariance), principal genus `= G²` for
  disc `-8N`, and even good-ideal valuations with trivial characters giving a
  rational class (KB E.4 p.89).  `research/quadratic-class-integration.md`
  §Alternative, `research/polynomial-top-field-pool.md` last section.  These are
  exact identifications and carry zero analytic loss. -/
  l4_l25_l36 : AlgebraicLeaf
  /-- **P1** (blueprint §0.2 and §2 "Prepass", `[INFRA]`): an `exp (o(H))`-cost
  partial factorer below `exp ((log n)^{2/3})` that succeeds with probability
  `≥ exp (-δ H)` for every `δ > 0`.  KB Prop. H.3 p.129; this is L30 at the
  prepass cutoff, and ECM cannot replace it without the all-primes Hasse
  smoothness conjecture.  The success side implies the ledger slot; the cost
  exponent is recorded for audit. -/
  p1 : P1Leaf

/-! ## The loss ledger induced by the paper statements -/

/-- The C5 loss ledger assembled from the twelve paper fields.  This is a
genuine choice of `C5LossSlots`, so the paper statements and the ledger are not
the same objects: the ledger is a specialization of the paper statements. -/
def PaperAnalyticAssumptions.slots
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) : C5LossSlots
  | .rationalGoodEnvironments => P.l18_4.loss
  | .poissonQuotient => P.l19_4.loss
  | .idealZeroMode => P.l19_5.loss
  | .thinPairs => P.l19_6.loss
  | .interiorConcentration => P.l20_2.loss
  | .topChildLaw => P.l20_4.loss
  | .ellipticExceptional => P.l21_2.loss
  | .ecmRecognition => P.l27_1.loss
  | .genusTwoPartialFactorer => P.l30.loss
  | .characterSeparation => P.l34.loss
  | .classGroupGenus => P.l4_l25_l36.loss
  | .prepass => P.p1.loss

/-- Each paper leaf implies its `C5Inputs` loss slot. -/
theorem PaperAnalyticAssumptions.slot_le
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (k : C5Leaf) :
    ∀ᶠ n : ℕ in atTop, P.slots k n ≤ exp (-(2 : ℝ) * scale n) := by
  cases k
  · exact P.l18_4.slot
  · exact P.l19_4.slot
  · exact P.l19_5.slot
  · exact P.l19_6.slot
  · exact P.l20_2.slot
  · exact P.l20_4.slot
  · exact P.l21_2.slot
  · exact P.l27_1.slot
  · exact P.l30.slot
  · exact P.l34.slot
  · exact P.l4_l25_l36.slot
  · exact P.p1.slot

/-- Build the C5 ledger from the paper fields and the C5.a-e `hitMass` bridge.

`hitMass` is the same field as in `C5Inputs`: the ideal law's good-transcript
mass is at least `1/4` minus the total loss.  It is kept as a parameter because
it is the one C5 ingredient that concerns the concrete epoch (the field pool and
the recognizer events) and is therefore not a manuscript leaf statement. -/
def PaperAnalyticAssumptions.toC5Inputs
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C)
    (hitMass : ∀ n (hN : 3 ≤ n), HardInput n →
      (1 / 4 : ℝ) - P.slots.total n ≤
        ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal) :
    C5Inputs E where
  slots := P.slots
  l18_4 := P.slot_le .rationalGoodEnvironments
  l19_4 := P.slot_le .poissonQuotient
  l19_5 := P.slot_le .idealZeroMode
  l19_6 := P.slot_le .thinPairs
  l20_2 := P.slot_le .interiorConcentration
  l20_4 := P.slot_le .topChildLaw
  l21_2 := P.slot_le .ellipticExceptional
  l27_1 := P.slot_le .ecmRecognition
  l30 := P.slot_le .genusTwoPartialFactorer
  l34 := P.slot_le .characterSeparation
  l4_l25_l36 := P.slot_le .classGroupGenus
  p1 := P.slot_le .prepass
  hitMass := hitMass

/-! ## The reduction -/

/-- **Main reduction.**  The twelve paper-level leaf statements, together with
C1-C4 and the C5 `hitMass` bridge, give the existing `EpochAnalyticInputs`
ledger.  No paper lemma is proved: the twelve `paper` fields are hypotheses, and
the only work done here is the `B = 2` specialization, the L20.2 concentration
conversion, and the assembly of the C5 record. -/
def epochAnalyticInputs_of_paperAssumptions
    (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ)
    (P : PaperAnalyticAssumptions E C)
    (c1 : C1Inputs E) (c2 : C2Inputs E) (c3 : C3Inputs E) (c4 : C4Inputs E C)
    (hitMass : ∀ n (hN : 3 ≤ n), HardInput n →
      (1 / 4 : ℝ) - P.slots.total n ≤
        ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal) :
    EpochAnalyticInputs E C where
  c1 := c1
  c2 := c2
  c3 := c3
  c4 := c4
  c5 := P.toC5Inputs hitMass

/-- The paper ledger sums to `≤ exp (-scale n)`, by the [LEAN] finite-sum
combiner already used in `C5Inputs.total_le_exp_neg_scale`. -/
theorem paper_total_le_exp_neg_scale
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C)
    (hitMass : ∀ n (hN : 3 ≤ n), HardInput n →
      (1 / 4 : ℝ) - P.slots.total n ≤
        ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal) :
    ∀ᶠ n : ℕ in atTop, P.slots.total n ≤ exp (-(1 : ℝ) * scale n) :=
  (P.toC5Inputs hitMass).total_le_exp_neg_scale

/-- The paper-level endpoint: the twelve manuscript leaves plus C1-C4 and the
C5 bridge imply `HardEpochAsymptoticBound E C` through the wave-1 reduction. -/
theorem hardEpochAsymptoticBound_of_paperAssumptions
    (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ)
    (P : PaperAnalyticAssumptions E C)
    (c1 : C1Inputs E) (c2 : C2Inputs E) (c3 : C3Inputs E) (c4 : C4Inputs E C)
    (hitMass : ∀ n (hN : 3 ≤ n), HardInput n →
      (1 / 4 : ℝ) - P.slots.total n ≤
        ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal) :
    HardEpochAsymptoticBound E C :=
  hardEpochAsymptoticBound_of_analyticInputs E C
    (epochAnalyticInputs_of_paperAssumptions E C P c1 c2 c3 c4 hitMass)

/-! ## Axiom audit -/

#print axioms SubexpLeaf.slot
#print axioms RatedLeaf.slot_of_rate_dominates
#print axioms ConcentrationLeaf.slot
#print axioms AlgebraicLeaf.slot
#print axioms P1Leaf.slot
#print axioms PaperAnalyticAssumptions.slot_le
#print axioms PaperAnalyticAssumptions.toC5Inputs
#print axioms epochAnalyticInputs_of_paperAssumptions
#print axioms paper_total_le_exp_neg_scale
#print axioms hardEpochAsymptoticBound_of_paperAssumptions

end Cogentic.RandomizedPaperLeafStatements
