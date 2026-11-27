import Cogentic.RandomizedEpochAssembly
import Cogentic.RandomizedFieldPoolDescent
import Cogentic.RandomizedFieldExtraction
import Cogentic.RandomizedEpochSuccess
import Cogentic.RandomizedReducedFormSupply
import Cogentic.RandomizedTopStripMoments

/-!
# Auditable analytic inputs for `HardEpochAsymptoticBound`

`RandomizedEpochAssembly.HardEpochAsymptoticBound E C` currently hides the whole
analytic tree behind one opaque hypothesis.  This file replaces it, at the current
`HardEpochData` interface, by a bundle of named inputs:

* `C1Inputs`  -- the public congruence check (blueprint C1, L1).
* `C2Inputs`  -- conditional hidden-sign uniformity (blueprint C2, L2-L5, L4).
* `C3Inputs`  -- the ideal/actual total-variation budget (blueprint C3, L6-L10).
* `C4Inputs`  -- the expected public-work budget (blueprint C4, L11-L16).
* `C5Inputs`  -- the good-transcript mass and its leaf-by-leaf loss ledger
  (blueprint C5, leaves L17-L39 and P1).

The `C5Inputs` ledger has one real-valued loss slot per named analytic leaf
(L18.4, L19.4-L19.6, L20.2, L20.4, L21.2, L27.1, L30, L34, L4/L25/L36, P1).
Each leaf is an *unproved* hypothesis saying that its slot is eventually
`≤ exp (-2 * scale n)`.  The existing cost combiner
`RandomizedEpochAssembly.eventually_finset_sum_le_exp` sums the ledger, and the
`hitMass` field is the single C5.a-e assembly bridge (paper glue L17/L28/L38)
relating the summed loss to the ideal good-transcript mass.

**What is and is not proved.**  The analytic leaves are not proved here: their
statements are the `Prop` fields of `C5Inputs`.  What *is* proved is that those
leaves, together with the C1-C4 interfaces and the C5 assembly bridge, imply
`HardEpochAsymptoticBound E C`.  The numerical combination (nonnegativity of
`γ`, the `γ / 2 - ε` margin, and the finite-sum loss bound) is fully discharged.
C1 and C2 are additionally discharged for the concrete constructor
`HardEpochData.ofMultiField` from `ofMultiField_congruenceCheck` and
`ofMultiField_hiddenUniform`.

The file contains no `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedEpochAnalyticInputs

open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedOneThirdAsymptotic
open Filter Real
open scoped BigOperators ENNReal

/-- The hard-input side conditions used throughout `HardEpochAsymptoticBound`:
odd, not prime, and not a prime power. -/
def HardInput (n : ℕ) : Prop := Odd n ∧ ¬ n.Prime ∧ ¬ IsPrimePow n

/-! ## C1: the public congruence check -/

/-- C1 of the blueprint.  `CongruenceCheck` is L1: the public transcript records
`Y² = ∏_{i ∈ I} (observed square i)`, so the hidden label product squares to the
public root.  For `HardEpochData.ofMultiField` this is discharged by
`HardEpochData.ofMultiField_congruenceCheck`
(`RandomizedEpochAssembly`, from the global product identity in
`RandomizedFieldExtraction`). -/
structure C1Inputs (E : ∀ n, 3 ≤ n → HardEpochData n) where
  /-- L1: `CongruenceCheck` on every hard input. -/
  congruenceCheck : ∀ n (hN : 3 ≤ n), HardInput n → (E n hN).CongruenceCheck

/-- C2 of the blueprint.  `HiddenUniform` is the conditional flip invariance of
the ideal law on every good transcript.  Its support in the blueprint is L2-L5:
`ClassSignFibers.square_tag_uniform` / `square_global_sign_uniform`,
`ReducedFormRoot`/`ReducedFormMinimum` (L3), the non-maximal-order class-group
and ideal-squaring infrastructure of `research/reduced-form-root-signs.md`
and `research/quadratic-class-integration.md` (L4), and the product/flip law
(L5).  L4 is the `INFRA-moderate` input; L25/L36 are its C5 counterparts. -/
structure C2Inputs (E : ∀ n, 3 ≤ n → HardEpochData n) where
  /-- L2-L5 (including L4, the non-maximal-order class group): `HiddenUniform`
  on every hard input. -/
  hiddenUniform : ∀ n (hN : 3 ≤ n), HardInput n → (E n hN).HiddenUniform

/-! ## C3: total variation of the actual sampler -/

/-- C3 of the blueprint: the actual (capped fair-bit) epoch law is within
`ε` of the ideal law.  Provenance: `research/quadratic-class-integration.md`,
`research/direct-reduced-class-sampler.md`, `RandomizedDirectClassSampler`
(L6), `FormGroup.reducedForms_card_lower_from_critical_line` (L7),
`RandomizedUniformBits`/`RandomizedSamplerTransfer` (L8), the finite discrete
Gaussian sampler of KB Lemma H.1 (L9), and the per-slot `exp (-ω(H))` loss
(L10, which is where the rough-input condition of blueprint 0.2 enters). -/
structure C3Inputs (E : ∀ n, 3 ≤ n → HardEpochData n) where
  /-- The per-input TV budget `ε_n`. -/
  epsilon : ℕ → ℝ
  /-- L6-L10: `ε_n` is nonnegative. -/
  epsilon_nonneg : ∀ n, 0 ≤ epsilon n
  /-- L6-L10: the blueprint's TV budget is at most `1/32`; the manuscript's
  actual bound is `1/1024 + o(1)`, so this is a weakening of the same input. -/
  epsilon_le : ∀ n, epsilon n ≤ 1 / 32
  /-- L6-L10: ideal-to-actual total variation is at most `ε_n`. -/
  tv_le : ∀ n (hN : 3 ≤ n), HardInput n →
    pmfTotalVariation (E n hN).ideal (E n hN).actual ≤ epsilon n

/-! ## C4: expected public work -/

/-- C4 of the blueprint: the mean charged public work is `≤ exp ((C + δ/2) H)`.
Provenance: `RandomizedBalancedRationalSchedule` and
`RandomizedEpochAssembly.balancedSchedule_multistage_screening_cost_le_exp`
(L11), the integer-schedule realization of the scalar exponents
(`research/narrow-class-integration.md` "Integer scales and cost",
`research/tiered-descent.md`) (L12), the per-call cost formulas of
`research/private-elliptic-recognition.md`, `research/polynomial-top-field-pool.md`
and `RandomizedPadeCost`/`RandomizedSparseProducts` (L13), the summation
combiners `eventually_finset_sum_le_exp` / `eventually_mean_finset_sum_le_exp`
(L14), the cost model charging every step S0-S8 (L15, the blueprint 0.1 item),
and the Rankin prefix bounds in `RandomizedReducedFormSupply`
(`certified_prefix_rankin_bound`, L16). -/
structure C4Inputs (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) where
  /-- L11-L16: for every `δ > 0`, eventually on every hard input the mean public
  work is at most `exp ((C + δ/2) * scale n)`. -/
  work_le : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (hN : 3 ≤ n), HardInput n →
    mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
      ENNReal.ofReal (exp ((C + δ / 2) * scale n))

/-! ## C5: good-transcript mass and the named analytic leaves -/

/-- The named analytic leaves of blueprint C5, plus the prepass leaf P1 of
blueprint 0.2. -/
inductive C5Leaf
  | rationalGoodEnvironments   -- L18.4
  | poissonQuotient            -- L19.4
  | idealZeroMode              -- L19.5
  | thinPairs                  -- L19.6
  | interiorConcentration      -- L20.2
  | topChildLaw                -- L20.4
  | ellipticExceptional        -- L21.2
  | ecmRecognition             -- L27.1
  | genusTwoPartialFactorer    -- L30
  | characterSeparation        -- L34
  | classGroupGenus            -- L4 / L25 / L36
  | prepass                    -- P1
  deriving DecidableEq

/-- Explicit enumeration of all `C5Leaf` constructors.  (An explicit `Finset`
is used instead of `Finset.univ`, because the `Fintype` derived instance for
this enum is not definitionally well formed in the pinned toolchain.) -/
def allC5Leaves : Finset C5Leaf :=
  { .rationalGoodEnvironments, .poissonQuotient, .idealZeroMode, .thinPairs,
    .interiorConcentration, .topChildLaw, .ellipticExceptional, .ecmRecognition,
    .genusTwoPartialFactorer, .characterSeparation, .classGroupGenus, .prepass }

/-- Real loss ledger indexed by the named C5 leaves. -/
abbrev C5LossSlots := C5Leaf → ℕ → ℝ

/-- Total C5 loss at input size `n`. -/
noncomputable def C5LossSlots.total (slots : C5LossSlots) (n : ℕ) : ℝ :=
  ∑ k ∈ allC5Leaves, slots k n

/-- C5 of the blueprint: the ideal law puts mass at least `1/4 - (sum of all
leaf losses)` on good transcripts, and each leaf loss is subexponential.

The leaf fields are the auditable placeholders.  Each says that its slot is
eventually `≤ exp (-2 * scale n)`; the blueprint's leaves are generally much
stronger (`D^{-B}` for every `B`, `exp (-c T_B)`, etc.), so these fields are
weakenings chosen to make the arithmetic assembly below explicit.  The field
`hitMass` is *not* a leaf: it is the C5.a-e assembly bridge supplied by the
[LEAN] combinatorics of `RandomizedFieldPoolDescent` (L17, L20.1, L28), the
rank/prefix supply in `RandomizedReducedFormSupply`, the top-strip moments in
`RandomizedTopStripMoments`, and the final hidden-sign probability
`HardEpochData.multiField_epoch_verified_split_probability_half` /
`assembledAttempt_hit_prob_ge` (L38).  It is the one remaining paper-level
bridge at the current `HardEpochData` interface, because that interface does
not expose the field pool, the moment functionals, or the recognizer events. -/
structure C5Inputs (E : ∀ n, 3 ≤ n → HardEpochData n) where
  /-- Loss ledger indexed by `C5Leaf`. -/
  slots : C5LossSlots
  /-- L18.4 (`research/balanced-ideal-pair-audit.md` §1, KB Lemma G.3 p.107):
  rational-good environments at the shrunken denominator interval, including
  the RH prime counts in cells and the large-sieve inequality.  Lean-facing
  loss slot. -/
  l18_4 : ∀ᶠ n : ℕ in atTop,
    slots .rationalGoodEnvironments n ≤ exp (-(2 : ℝ) * scale n)
  /-- L19.4 (`research/mixed-strip-moment.md` §Denominator,
  `research/narrow-top-moment.md`, `research/gaussian-variation.md`,
  `research/dual-major-arc-count.md`): Poisson quotient for the actual discrete
  Gaussian two-mark law.  Lean-facing loss slot. -/
  l19_4 : ∀ᶠ n : ℕ in atTop,
    slots .poissonQuotient n ≤ exp (-(2 : ℝ) * scale n)
  /-- L19.5 (`research/balanced-ideal-pair-audit.md` §One-point/§Prime factors,
  `research/balanced-strip-transfer.md` ¶4): ideal zero-mode bound
  `D^{O(1)} μ_q² + o(μ²)`.  Lean-facing loss slot. -/
  l19_5 : ∀ᶠ n : ℕ in atTop,
    slots .idealZeroMode n ≤ exp (-(2 : ℝ) * scale n)
  /-- L19.6 (`research/balanced-class-integration.md` ¶5,
  `research/thin-top-pairs.md`): thin and small-determinant pairs.  Lean-facing
  loss slot. -/
  l19_6 : ∀ᶠ n : ℕ in atTop,
    slots .thinPairs n ≤ exp (-(2 : ℝ) * scale n)
  /-- L20.2 (KB Thm 3.1, G.8, G.10, App. C; `research/balanced-class-integration.md`):
  interior concentration `ε_i ≤ D^{-2A}` with `A = D^{1/48}`, growing-order
  moments, smooth-number saddle point, Hildebrand-Tenenbaum, and GRH
  smooth-character sums (KB Lemma G.2 p.106).  Lean-facing loss slot. -/
  l20_2 : ∀ᶠ n : ℕ in atTop,
    slots .interiorConcentration n ≤ exp (-(2 : ℝ) * scale n)
  /-- L20.4 (`research/balanced-strip-transfer.md` (2) and
  `research/polynomial-top-field-pool.md` "item 3"): top G.12 under the
  incoming-child-root law, including the child-root-conditioned two-point bound
  on incoming-good parts.  Lean-facing loss slot. -/
  l20_4 : ∀ᶠ n : ℕ in atTop,
    slots .topChildLaw n ≤ exp (-(2 : ℝ) * scale n)
  /-- L21.2 (`research/private-elliptic-recognition.md` §1): RH implies smooth
  numbers within `√p` of almost all integer centres; twisted `ζ'/ζ` prime sum,
  Perron at `Re s = 2/3`, Fourier `L²` comparison, tent smoothing.  Lean-facing
  loss slot. -/
  l21_2 : ∀ᶠ n : ℕ in atTop,
    slots .ellipticExceptional n ≤ exp (-(2 : ℝ) * scale n)
  /-- L27.1 (Lenstra-Pomerance Thm 7.1; `research/private-elliptic-recognition.md`):
  ECM recognition failure `≤ c₆^{#curves · ψ₀ / (√p log y)}`, requiring
  elliptic curves over `Z/nZ`, Hasse, and Deuring/Lenstra curve counts.
  Lean-facing loss slot. -/
  l27_1 : ∀ᶠ n : ℕ in atTop,
    slots .ecmRecognition n ≤ exp (-(2 : ℝ) * scale n)
  /-- L30 (KB Prop. H.3 p.129; `research/public-elliptic-recognition.md`):
  genus-two partial factorer to `B`, including genus-two Jacobians, Cantor
  arithmetic mod `n`, the LPP order-fibre theorem, Younis'
  RH short-interval smooth asymptotic, and Hildebrand-Tenenbaum.  Lean-facing
  loss slot. -/
  l30 : ∀ᶠ n : ℕ in atTop,
    slots .genusTwoPartialFactorer n ≤ exp (-(2 : ℝ) * scale n)
  /-- L34 (KB E.3 p.87-88; `research/cumulative-character-probes.md`): character
  separation `≥ 1 - 1/128`, via effective Chebotarev (Lagarias-Odlyzko Thm 1.3)
  and Stark's exceptional-zero lemma; mask compression is already [LEAN] in
  `RandomizedProbeCount`.  Lean-facing loss slot. -/
  l34 : ∀ᶠ n : ℕ in atTop,
    slots .characterSeparation n ≤ exp (-(2 : ℝ) * scale n)
  /-- L4/L25/L36 (`research/quadratic-class-integration.md` §Alternative,
  `research/polynomial-top-field-pool.md` last section): class groups of
  non-maximal orders, principal genus `= G²`, even good-ideal valuations and
  trivial characters giving a rational class.  Lean-facing loss slot. -/
  l4_l25_l36 : ∀ᶠ n : ℕ in atTop,
    slots .classGroupGenus n ≤ exp (-(2 : ℝ) * scale n)
  /-- P1 (blueprint §0.2; KB H.3 p.129): an `exp (o(H))`-cost partial factorer
  below `exp ((log n)^{2/3})`, needed to pass hard-but-not-rough inputs to the
  rough epoch through `RandomizedSmallPrimePrepass`.  Lean-facing loss slot. -/
  p1 : ∀ᶠ n : ℕ in atTop,
    slots .prepass n ≤ exp (-(2 : ℝ) * scale n)
  /-- C5.a-e assembly bridge (paper glue L17/L28/L38, with the [LEAN]
  combinators in `RandomizedFieldPoolDescent`, `RandomizedReducedFormSupply`,
  `RandomizedTopStripMoments`, and `RandomizedEpochSuccess`): the ideal law's
  good-transcript mass is at least `1/4` minus the total leaf loss. -/
  hitMass : ∀ n (hN : 3 ≤ n), HardInput n →
    (1 / 4 : ℝ) - slots.total n ≤
      ((E n hN).ideal.toOuterMeasure
        {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal

namespace C5Inputs

variable {E : ∀ n, 3 ≤ n → HardEpochData n}

/-- Each named leaf slot is eventually `≤ exp (-2 * scale n)`.  This is just the
field projection, written uniformly over `C5Leaf`. -/
theorem leaf_bound (I : C5Inputs E) :
    ∀ k : C5Leaf, ∀ᶠ n : ℕ in atTop,
      I.slots k n ≤ exp (-(2 : ℝ) * scale n) := by
  intro k
  cases k
  · exact I.l18_4
  · exact I.l19_4
  · exact I.l19_5
  · exact I.l19_6
  · exact I.l20_2
  · exact I.l20_4
  · exact I.l21_2
  · exact I.l27_1
  · exact I.l30
  · exact I.l34
  · exact I.l4_l25_l36
  · exact I.p1

/-- Finite-sum cost combiner: the total C5 loss is eventually
`≤ exp (-scale n)`.  This instantiates
`RandomizedEpochAssembly.eventually_finset_sum_le_exp` at the `C5Leaf` ledger. -/
theorem total_le_exp_neg_scale (I : C5Inputs E) :
    ∀ᶠ n : ℕ in atTop, I.slots.total n ≤ exp (-(1 : ℝ) * scale n) := by
  have h := eventually_finset_sum_le_exp allC5Leaves
    (fun k n => I.slots k n) (fun _ => -(2 : ℝ)) (D := -(1 : ℝ))
    (by intro k _; norm_num)
    (by intro k _; exact I.leaf_bound k)
  simpa [C5LossSlots.total] using h

end C5Inputs

/-! ## The bundled analytic inputs -/

/-- The full auditable input bundle for `HardEpochAsymptoticBound E C`.
The C1-C5 fields are grouped exactly as in blueprint §2. -/
structure EpochAnalyticInputs (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) where
  /-- C1: public congruence check (L1). -/
  c1 : C1Inputs E
  /-- C2: conditional hidden-sign uniformity (L2-L5, including L4). -/
  c2 : C2Inputs E
  /-- C3: ideal/actual total variation (L6-L10). -/
  c3 : C3Inputs E
  /-- C4: expected public work (L11-L16). -/
  c4 : C4Inputs E C
  /-- C5: good mass and the named analytic leaf ledger (L17-L39, P1). -/
  c5 : C5Inputs E

/-- **Main reduction.**  The named analytic inputs imply
`HardEpochAsymptoticBound E C`.

The only nontrivial numerical step is the C5 margin: choose
`γ = 1/4 - totalLoss` and `ε = C3.epsilon`.  Since the leaf ledger is eventually
`≤ exp (-scale)`, it is eventually `≤ 1/16`, so `γ ≥ 3/16`; with `ε ≤ 1/32`
this gives `γ / 2 - ε ≥ 1/16`, which eventually dominates
`exp (-(δ/4) * scale)`. -/
theorem hardEpochAsymptoticBound_of_analyticInputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ)
    (I : EpochAnalyticInputs E C) :
    HardEpochAsymptoticBound E C := by
  intro δ hδ
  filter_upwards [I.c4.work_le δ hδ,
    I.c5.total_le_exp_neg_scale,
    eventually_exp_neg_le_const (c := (1 / 16 : ℝ)) (by norm_num)
      (show (0 : ℝ) < 1 by norm_num),
    eventually_exp_neg_le_const (c := (1 / 4 : ℝ)) (by norm_num)
      (show (0 : ℝ) < 1 by norm_num),
    eventually_exp_neg_le_const (c := (1 / 16 : ℝ)) (by norm_num)
      (show (0 : ℝ) < δ / 4 by positivity)]
    with n hwork hloss hloss16 hloss4 hmargin
  intro hN hodd hprime hnpp
  have hhard : HardInput n := ⟨hodd, hprime, hnpp⟩
  have hloss16' : I.c5.slots.total n ≤ 1 / 16 := hloss.trans hloss16
  have hloss4' : I.c5.slots.total n ≤ 1 / 4 := hloss.trans hloss4
  refine ⟨I.c1.congruenceCheck n hN hhard,
    I.c2.hiddenUniform n hN hhard,
    exp ((C + δ / 2) * scale n), (1 / 4 : ℝ) - I.c5.slots.total n,
    I.c3.epsilon n, ?_, ?_, le_rfl, ?_, I.c3.tv_le n hN hhard, ?_⟩
  · -- `0 ≤ γ`
    linarith only [hloss4']
  · -- mean public work
    exact hwork hN hhard
  · -- good-transcript mass
    exact I.c5.hitMass n hN hhard
  · -- the `γ / 2 - ε` margin
    have hε := I.c3.epsilon_le n
    linarith only [hmargin, hloss16', hε]

/-! ## Discharging C1 and C2 for `HardEpochData.ofMultiField` -/

/-- The `ofMultiField` constructor as an `n`-indexed epoch family with fixed
public/private type parameters. -/
noncomputable def ofMultiFieldFamily
    {Coins Label FieldId Public : Type}
    [Fintype Coins] [Fintype Label] [DecidableEq Label] [DecidableEq Public]
    (ideal actual : ∀ n, PMF (Coins × (Label → (ZMod n)ˣ)))
    (trace : ∀ n, Coins → (Label → (ZMod n)ˣ) → Public)
    (good : ∀ _n, Finset Public)
    (extract : ∀ n, good n → PublicMultiFieldTranscript Label FieldId n)
    (pubWork : ∀ n, Coins × (Label → (ZMod n)ˣ) → ℕ) :
    ∀ n, 3 ≤ n → HardEpochData n :=
  fun n _ =>
    HardEpochData.ofMultiField (ideal n) (actual n) (trace n) (good n)
      (extract n) (pubWork n)

/-- C1 for `ofMultiField`: the global product identity discharges the public
congruence check via `HardEpochData.ofMultiField_congruenceCheck`. -/
theorem c1Inputs_ofMultiField
    {Coins Label FieldId Public : Type}
    [Fintype Coins] [Fintype Label] [DecidableEq Label] [DecidableEq Public]
    {ideal actual : ∀ n, PMF (Coins × (Label → (ZMod n)ˣ))}
    {trace : ∀ n, Coins → (Label → (ZMod n)ˣ) → Public}
    {good : ∀ _n, Finset Public}
    {extract : ∀ n, good n → PublicMultiFieldTranscript Label FieldId n}
    {pubWork : ∀ n, Coins × (Label → (ZMod n)ˣ) → ℕ}
    (hglobal : ∀ n (t : good n) x, observe (trace n) x = t.val →
      (∏ i ∈ (extract n t).mask, (x.2 i) ^ 2) =
        (extract n t).ratCorr * ∏ j ∈ (extract n t).fields, (extract n t).fieldProd j) :
    C1Inputs (ofMultiFieldFamily ideal actual trace good extract pubWork) where
  congruenceCheck := by
    intro n hN _
    exact HardEpochData.ofMultiField_congruenceCheck (ideal n) (actual n)
      (trace n) (good n) (extract n) (pubWork n) (hglobal n)

/-- C2 for `ofMultiField`: coordinatewise sign symmetry on every mask element
discharges `HiddenUniform` via `HardEpochData.ofMultiField_hiddenUniform`. -/
theorem c2Inputs_ofMultiField
    {Coins Label FieldId Public : Type}
    [Fintype Coins] [Fintype Label] [DecidableEq Label] [DecidableEq Public]
    {ideal actual : ∀ n, PMF (Coins × (Label → (ZMod n)ˣ))}
    {trace : ∀ n, Coins → (Label → (ZMod n)ˣ) → Public}
    {good : ∀ _n, Finset Public}
    {extract : ∀ n, good n → PublicMultiFieldTranscript Label FieldId n}
    {pubWork : ∀ n, Coins × (Label → (ZMod n)ˣ) → ℕ}
    (huniform : ∀ n (t : good n) x y, observe (trace n) x = t.val → x.1 = y.1 →
      ∀ i ∈ (extract n t).mask, (x.2 i) ^ 2 = (y.2 i) ^ 2 →
      (∀ j, j ≠ i → x.2 j = y.2 j) → ideal n x = ideal n y) :
    C2Inputs (ofMultiFieldFamily ideal actual trace good extract pubWork) where
  hiddenUniform := by
    intro n hN _
    exact HardEpochData.ofMultiField_hiddenUniform (ideal n) (actual n)
      (trace n) (good n) (extract n) (pubWork n) (huniform n)

/-- Bundle the analytic inputs for the concrete `ofMultiField` epoch, with C1
and C2 already discharged from the extractor's product and sign-symmetry data.
The remaining C3/C4/C5 fields are explicit arguments. -/
noncomputable def epochAnalyticInputs_ofMultiField
    {Coins Label FieldId Public : Type}
    [Fintype Coins] [Fintype Label] [DecidableEq Label] [DecidableEq Public]
    {ideal actual : ∀ n, PMF (Coins × (Label → (ZMod n)ˣ))}
    {trace : ∀ n, Coins → (Label → (ZMod n)ˣ) → Public}
    {good : ∀ _n, Finset Public}
    {extract : ∀ n, good n → PublicMultiFieldTranscript Label FieldId n}
    {pubWork : ∀ n, Coins × (Label → (ZMod n)ˣ) → ℕ}
    {C : ℝ}
    (hglobal : ∀ n (t : good n) x, observe (trace n) x = t.val →
      (∏ i ∈ (extract n t).mask, (x.2 i) ^ 2) =
        (extract n t).ratCorr * ∏ j ∈ (extract n t).fields, (extract n t).fieldProd j)
    (huniform : ∀ n (t : good n) x y, observe (trace n) x = t.val → x.1 = y.1 →
      ∀ i ∈ (extract n t).mask, (x.2 i) ^ 2 = (y.2 i) ^ 2 →
      (∀ j, j ≠ i → x.2 j = y.2 j) → ideal n x = ideal n y)
    (c3 : C3Inputs (ofMultiFieldFamily ideal actual trace good extract pubWork))
    (c4 : C4Inputs (ofMultiFieldFamily ideal actual trace good extract pubWork) C)
    (c5 : C5Inputs (ofMultiFieldFamily ideal actual trace good extract pubWork)) :
    EpochAnalyticInputs (ofMultiFieldFamily ideal actual trace good extract pubWork) C where
  c1 := c1Inputs_ofMultiField hglobal
  c2 := c2Inputs_ofMultiField huniform
  c3 := c3
  c4 := c4
  c5 := c5

/-- **Reduction for the concrete multi-field epoch.**  C1 and C2 are discharged
from the extractor data; C3, C4, and the C5 leaf ledger remain explicit. -/
theorem hardEpochAsymptoticBound_ofMultiField_analyticInputs
    {Coins Label FieldId Public : Type}
    [Fintype Coins] [Fintype Label] [DecidableEq Label] [DecidableEq Public]
    {ideal actual : ∀ n, PMF (Coins × (Label → (ZMod n)ˣ))}
    {trace : ∀ n, Coins → (Label → (ZMod n)ˣ) → Public}
    {good : ∀ _n, Finset Public}
    {extract : ∀ n, good n → PublicMultiFieldTranscript Label FieldId n}
    {pubWork : ∀ n, Coins × (Label → (ZMod n)ˣ) → ℕ}
    {C : ℝ}
    (hglobal : ∀ n (t : good n) x, observe (trace n) x = t.val →
      (∏ i ∈ (extract n t).mask, (x.2 i) ^ 2) =
        (extract n t).ratCorr * ∏ j ∈ (extract n t).fields, (extract n t).fieldProd j)
    (huniform : ∀ n (t : good n) x y, observe (trace n) x = t.val → x.1 = y.1 →
      ∀ i ∈ (extract n t).mask, (x.2 i) ^ 2 = (y.2 i) ^ 2 →
      (∀ j, j ≠ i → x.2 j = y.2 j) → ideal n x = ideal n y)
    (c3 : C3Inputs (ofMultiFieldFamily ideal actual trace good extract pubWork))
    (c4 : C4Inputs (ofMultiFieldFamily ideal actual trace good extract pubWork) C)
    (c5 : C5Inputs (ofMultiFieldFamily ideal actual trace good extract pubWork)) :
    HardEpochAsymptoticBound
      (ofMultiFieldFamily ideal actual trace good extract pubWork) C :=
  hardEpochAsymptoticBound_of_analyticInputs _ C
    (epochAnalyticInputs_ofMultiField hglobal huniform c3 c4 c5)

/-- The analytic inputs also give the actual assembled-attempt hit probability
bound, by feeding `HardEpochData.assembledAttempt_hit_prob_ge`
(the `RandomizedEpochSuccess` verified-split glue) with the C1/C2/C3/C5 fields.
This is the exact conclusion that the end-to-end ratio assembly consumes. -/
theorem assembledAttempt_hit_prob_ge_of_analyticInputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ)
    (I : EpochAnalyticInputs E C) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (hN : 3 ≤ n), HardInput n →
      exp (-(δ / 4) * scale n) ≤
        (((E n hN).actual.map ((E n hN).assembledAttempt hN)).toOuterMeasure
          {o | o.1 ≠ none}).toReal := by
  filter_upwards [I.c5.total_le_exp_neg_scale,
    eventually_exp_neg_le_const (c := (1 / 16 : ℝ)) (by norm_num)
      (show (0 : ℝ) < 1 by norm_num),
    eventually_exp_neg_le_const (c := (1 / 4 : ℝ)) (by norm_num)
      (show (0 : ℝ) < 1 by norm_num),
    eventually_exp_neg_le_const (c := (1 / 16 : ℝ)) (by norm_num)
      (show (0 : ℝ) < δ / 4 by positivity)]
    with n hloss hloss16 hloss4 hmargin
  intro hN hhard
  have hodd : Odd n := hhard.1
  have hnpp : ¬ IsPrimePow n := hhard.2.2
  have hloss16' : I.c5.slots.total n ≤ 1 / 16 := hloss.trans hloss16
  have hloss4' : I.c5.slots.total n ≤ 1 / 4 := hloss.trans hloss4
  have hγ0 : 0 ≤ (1 / 4 : ℝ) - I.c5.slots.total n := by linarith only [hloss4']
  have hε := I.c3.epsilon_le n
  have hmargin' : exp (-(δ / 4) * scale n) ≤
      ((1 / 4 : ℝ) - I.c5.slots.total n) / 2 - I.c3.epsilon n := by
    linarith only [hmargin, hloss16', hε]
  exact hmargin'.trans
    ((E n hN).assembledAttempt_hit_prob_ge hN hodd hnpp
      (I.c1.congruenceCheck n hN hhard) (I.c2.hiddenUniform n hN hhard)
      hγ0 (I.c5.hitMass n hN hhard) (I.c3.tv_le n hN hhard))

/-- Composition with the existing epoch-to-ratio assembly: the analytic inputs
also give the `(W, S)` work-to-hit ratio premise for `0 ≤ C`. -/
theorem assembled_epoch_ratio_of_analyticInputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) {C : ℝ} (hC : 0 ≤ C)
    (I : EpochAnalyticInputs E C) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬ n.Prime → ¬ IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epochLaw E n) (fun a => ((epochAttempt E n a).2 + 1 : ℕ)) + 1 ≤
            ENNReal.ofReal W ∧
          S ≤ (((epochLaw E n).map (epochAttempt E n)).toOuterMeasure
            {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n) :=
  assembled_epoch_ratio_eventually E hC (hardEpochAsymptoticBound_of_analyticInputs E C I)

/-! ## Axiom audit -/

#print axioms hardEpochAsymptoticBound_of_analyticInputs
#print axioms c1Inputs_ofMultiField
#print axioms c2Inputs_ofMultiField
#print axioms epochAnalyticInputs_ofMultiField
#print axioms hardEpochAsymptoticBound_ofMultiField_analyticInputs
#print axioms assembledAttempt_hit_prob_ge_of_analyticInputs
#print axioms assembled_epoch_ratio_of_analyticInputs

end Cogentic.RandomizedEpochAnalyticInputs
