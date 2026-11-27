import Cogentic.RandomizedConcreteHitMass
import Cogentic.RandomizedFieldExtraction
import Cogentic.RandomizedEvaluationMaps

/-!
# The C5.d algebra stage: L34–L37 decomposition and `StageBudget` reduction

`Cogentic.RandomizedConcreteHitMass.HitMassInputs.algebra` is the C5.d algebra
stage.  In the blueprint it is the conjunction of four post-row algebraic events:

* **L34** effective Chebotarev character separation: every nonrational class in
  `H_D` is detected by the selected probes with probability at least
  `1 - 1/128` (KB E.3 p.87–88; Lagarias–Odlyzko Theorem 1.3, Stark's
  exceptional-zero lemma; `research/keybreak-cumulative-character-probes.md`).
  Mathlib has no Chebotarev or Dedekind-zeta zero theory, so the numerical
  failure bound is kept as an explicit `Prop`.
* **L35** odd-degree norm-square algebra: E.1, the homogeneous norm formula E.7,
  scaled coordinates E.16–E.19, occurrence-parity cancellation, and multi-field
  assembly.  These are already proved in
  `Cogentic.RandomizedFieldExtraction`; the file below discharges the L35
  sub-stage from those theorems.
* **L36** even good-ideal valuations, trivial characters and an even `E_j`
  column give a rational class (definition of `H_D`, Theorem E.4 p.89).  This
  uses Dedekind valuations in the non-maximal orders `Z[β]`; it is kept as an
  explicit `Prop`.
* **L37** exact root by Hensel lifting together with its evaluation map to
  `Z/N` (KB H.7 p.138, E.16–E.19).  The evaluation-map separation half is
  available in `Cogentic.RandomizedEvaluationMaps`; the file below discharges
  that half from `card_le_degree_or_proper_gcd_of_injective_images`.

L33 (nonempty binary mask and sparse-solver failure fraction) is already fully
discharged in `RandomizedFieldExtraction` by
`nonempty_mask_of_taggedSolverSucceeds` and
`sparse_pade_nonempty_mask_failure_fraction_le`; it carries no remaining C5.d
loss budget, so the decomposition below covers only L34–L37.

The decomposition is a genuine union bound over four named sub-stages, not a
restatement of the algebra stage.  If the four sub-stage failure masses are
`lossC`, `lossO`, `lossV`, `lossH`, then

```
P(¬ algebra) ≤ lossC + lossO + lossV + lossH,
```

which is exactly a `StageBudget` whose `ok` is the conjunction of the four
events and whose `loss` is that explicit sum.  No sub-stage loss is set to zero:
each is a nonnegative parameter, and the two sub-stages that are discharged
from existing theorems merely show their failure event is empty, hence below
any nonnegative budget.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

open Finset
open scoped BigOperators Polynomial

namespace Cogentic.RandomizedC5Algebra

open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedEvaluationMaps

/-! ## Section 1: Finite-PMF helper for a deterministic sub-stage -/

section PMFHelpers

variable {Ω : Type*} [Fintype Ω]

/-- The empty event has zero mass. -/
theorem pmfProb_false (μ : PMF Ω) : pmfProb μ (fun _ => False) = 0 := by
  rw [pmfProb_eq_sum_filter]
  simp

/-- A sub-stage which holds on every sample has failure mass at most any
explicit nonnegative budget.  The budget is a parameter, not `0` by fiat. -/
theorem fail_le_of_forall (μ : PMF Ω) {E : Ω → Prop} {loss : ℝ}
    (h : ∀ ω, E ω) (hloss : 0 ≤ loss) :
    pmfProb μ (fun ω => ¬ E ω) ≤ loss := by
  have hiff : ∀ ω, (¬ E ω) ↔ False :=
    fun ω => ⟨fun hx => hx (h ω), False.elim⟩
  rw [pmfProb_congr μ hiff, pmfProb_false]
  exact hloss

end PMFHelpers

/-! ## Section 2: The four explicit sub-stage inputs

Each `Prop` below is the smallest numerical statement the C5.d stage needs for
that leaf: the ideal failure mass of the named event is bounded by a numerical
loss.  For L34 and L36 this is the paper-level input (Chebotarev and Dedekind
valuations respectively); for L35 and L37 the `Prop` is *proved* below from the
existing algebra/evaluation theorems. -/

section StageProps

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]

/-- **L34 (Chebotarev character separation).**  The paper-level statement that
the effective-Chebotarev probe stage fails on ideal mass at most `loss`. -/
def ChebotarevSeparation (ok : D.Sample → Prop) (loss : ℝ) : Prop :=
  pmfProb D.ideal (fun x => ¬ ok x) ≤ loss

/-- **L35 (odd-degree norm-square algebra).**  The failure bound for the
odd-degree square-certification stage.  The stage itself is discharged from
`RandomizedFieldExtraction.isSquare_of_odd_finrank_norm_sq` in Section 4. -/
def OddDegreeSeparation (ok : D.Sample → Prop) (loss : ℝ) : Prop :=
  pmfProb D.ideal (fun x => ¬ ok x) ≤ loss

/-- **L36 (even valuations and trivial characters).**  The paper-level statement
that the Dedekind-valuation / character-parity stage fails on ideal mass at most
`loss`. -/
def EvenValuationClass (ok : D.Sample → Prop) (loss : ℝ) : Prop :=
  pmfProb D.ideal (fun x => ¬ ok x) ≤ loss

/-- **L37 (Hensel root and evaluation map).**  The failure bound for the exact
Hensel root and its `Z/N` evaluation stage.  The evaluation-map half is
discharged from `RandomizedEvaluationMaps` in Section 5. -/
def HenselEvaluation (ok : D.Sample → Prop) (loss : ℝ) : Prop :=
  pmfProb D.ideal (fun x => ¬ ok x) ≤ loss

end StageProps

/-! ## Section 3: The C5.d algebra inputs and the `StageBudget` reduction -/

/-- **The four C5.d sub-stages.**  `algebraOk` is the conjunction of the four
events; `totalLoss` is the sum of the four explicit nonnegative losses.  The four
`…_fail_le` fields are the explicit paper-level `Prop`s (or, for L35/L37, the
discharged versions proved in Sections 4–5). -/
structure C5AlgebraInputs {N : ℕ} (D : ConcreteEpochData N) [Fintype D.Sample] where
  /-- L34: Chebotarev character-separation event. -/
  chebotarevOk : D.Sample → Prop
  /-- L34: numerical separation loss. -/
  chebotarevLoss : ℝ
  chebotarevLoss_nonneg : 0 ≤ chebotarevLoss
  chebotarev_fail_le : ChebotarevSeparation chebotarevOk chebotarevLoss
  /-- L35: odd-degree norm-square event. -/
  oddDegreeOk : D.Sample → Prop
  /-- L35: numerical algebra loss. -/
  oddDegreeLoss : ℝ
  oddDegreeLoss_nonneg : 0 ≤ oddDegreeLoss
  oddDegree_fail_le : OddDegreeSeparation oddDegreeOk oddDegreeLoss
  /-- L36: even-valuation / rational-class event. -/
  valuationOk : D.Sample → Prop
  /-- L36: numerical valuation loss. -/
  valuationLoss : ℝ
  valuationLoss_nonneg : 0 ≤ valuationLoss
  valuation_fail_le : EvenValuationClass valuationOk valuationLoss
  /-- L37: Hensel-root / evaluation-map event. -/
  henselOk : D.Sample → Prop
  /-- L37: numerical Hensel / evaluation loss. -/
  henselLoss : ℝ
  henselLoss_nonneg : 0 ≤ henselLoss
  hensel_fail_le : HenselEvaluation henselOk henselLoss

namespace C5AlgebraInputs

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]

/-- The C5.d algebra success event: all four sub-stages hold. -/
def algebraOk (I : C5AlgebraInputs D) (x : D.Sample) : Prop :=
  I.chebotarevOk x ∧ I.oddDegreeOk x ∧ I.valuationOk x ∧ I.henselOk x

/-- The total C5.d loss: the sum of the four explicit sub-stage losses. -/
noncomputable def totalLoss (I : C5AlgebraInputs D) : ℝ :=
  I.chebotarevLoss + I.oddDegreeLoss + I.valuationLoss + I.henselLoss

/-- The total loss is nonnegative because each sub-stage loss is. -/
theorem totalLoss_nonneg (I : C5AlgebraInputs D) : 0 ≤ I.totalLoss := by
  unfold totalLoss
  linarith only [I.chebotarevLoss_nonneg, I.oddDegreeLoss_nonneg,
    I.valuationLoss_nonneg, I.henselLoss_nonneg]

/-- The algebra event is definitionally the four-way conjunction. -/
theorem algebraOk_iff (I : C5AlgebraInputs D) (x : D.Sample) :
    I.algebraOk x ↔
      I.chebotarevOk x ∧ I.oddDegreeOk x ∧ I.valuationOk x ∧ I.henselOk x :=
  Iff.rfl

/-! ### The four sub-lemmas -/

/-- **L34 sub-lemma.**  Chebotarev character separation fails on mass at most
`chebotarevLoss`. -/
theorem chebotarev_stage_fail_le (I : C5AlgebraInputs D) :
    pmfProb D.ideal (fun x => ¬ I.chebotarevOk x) ≤ I.chebotarevLoss :=
  I.chebotarev_fail_le

/-- **L35 sub-lemma.**  The odd-degree algebra stage fails on mass at most
`oddDegreeLoss`. -/
theorem oddDegree_stage_fail_le (I : C5AlgebraInputs D) :
    pmfProb D.ideal (fun x => ¬ I.oddDegreeOk x) ≤ I.oddDegreeLoss :=
  I.oddDegree_fail_le

/-- **L36 sub-lemma.**  The even-valuation / rational-class stage fails on mass
at most `valuationLoss`. -/
theorem valuation_stage_fail_le (I : C5AlgebraInputs D) :
    pmfProb D.ideal (fun x => ¬ I.valuationOk x) ≤ I.valuationLoss :=
  I.valuation_fail_le

/-- **L37 sub-lemma.**  The Hensel-root / evaluation stage fails on mass at most
`henselLoss`. -/
theorem hensel_stage_fail_le (I : C5AlgebraInputs D) :
    pmfProb D.ideal (fun x => ¬ I.henselOk x) ≤ I.henselLoss :=
  I.hensel_fail_le

/-! ### Union bound and the `StageBudget` -/

/-- **C5.d failure bound.**  The complement of the four-way conjunction is
contained in the four-way disjunction of the sub-stage failures. -/
theorem algebra_fail_le (I : C5AlgebraInputs D) :
    pmfProb D.ideal (fun x => ¬ I.algebraOk x) ≤ I.totalLoss := by
  have hmono : pmfProb D.ideal (fun x => ¬ I.algebraOk x) ≤
      pmfProb D.ideal (fun x =>
        ¬ I.chebotarevOk x ∨ ¬ I.oddDegreeOk x ∨
          ¬ I.valuationOk x ∨ ¬ I.henselOk x) := by
    apply pmfProb_mono
    intro x hx
    unfold algebraOk at hx
    by_cases h1 : I.chebotarevOk x
    · by_cases h2 : I.oddDegreeOk x
      · by_cases h3 : I.valuationOk x
        · exact Or.inr (Or.inr (Or.inr (fun h4 => hx ⟨h1, h2, h3, h4⟩)))
        · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inl h2)
    · exact Or.inl h1
  have h1 := pmfProb_or_le_add D.ideal
    (fun x => ¬ I.chebotarevOk x)
    (fun x => ¬ I.oddDegreeOk x ∨ ¬ I.valuationOk x ∨ ¬ I.henselOk x)
  have h2 := pmfProb_or_le_add D.ideal
    (fun x => ¬ I.oddDegreeOk x)
    (fun x => ¬ I.valuationOk x ∨ ¬ I.henselOk x)
  have h3 := pmfProb_or_le_add D.ideal
    (fun x => ¬ I.valuationOk x) (fun x => ¬ I.henselOk x)
  have hc : pmfProb D.ideal (fun x => ¬ I.chebotarevOk x) ≤ I.chebotarevLoss :=
    I.chebotarev_fail_le
  have ho : pmfProb D.ideal (fun x => ¬ I.oddDegreeOk x) ≤ I.oddDegreeLoss :=
    I.oddDegree_fail_le
  have hv : pmfProb D.ideal (fun x => ¬ I.valuationOk x) ≤ I.valuationLoss :=
    I.valuation_fail_le
  have hh : pmfProb D.ideal (fun x => ¬ I.henselOk x) ≤ I.henselLoss :=
    I.hensel_fail_le
  unfold totalLoss
  linarith only [hmono, h1, h2, h3, hc, ho, hv, hh]

/-- **The C5.d `StageBudget`.**  This is the reduction consumed by
`RandomizedConcreteHitMass.HitMassInputs.algebra`: the event is the four-way
conjunction and the loss is the explicit sum of the L34–L37 losses. -/
noncomputable def stageBudget (I : C5AlgebraInputs D) : StageBudget D where
  ok := I.algebraOk
  loss := I.totalLoss
  loss_nonneg := I.totalLoss_nonneg
  fail_le := I.algebra_fail_le

end C5AlgebraInputs

/-! ## Section 4: Discharging L35 from the existing odd-degree algebra

The odd-degree stage is deterministic once the algebraic certificate is present:
`RandomizedFieldExtraction.isSquare_of_odd_finrank_norm_sq` turns an odd-degree
square norm and a rational squareclass into a square in the field.  Consequently
the failure event is empty and is charged to any explicit nonnegative budget. -/

section OddDegreeStage

open Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Module.Finite k K]

/-- The certificate consumed by `isSquare_of_odd_finrank_norm_sq`: an odd-degree
finite field extension, a rational squareclass `γ = r * δ^2`, and a square norm.
This packages E.1, E.7, the scaled-coordinate identity E.16–E.19, and the
occurrence-parity cancellation as one algebraic datum. -/
structure OddDegreeSquareCertificate (γ : K) where
  /-- The rational squareclass representative. -/
  r : k
  /-- The square factor. -/
  δ : K
  /-- The extension degree is odd. -/
  hodd : Odd (Module.finrank k K)
  /-- `γ` lies in the rational squareclass of `r`. -/
  hclass : γ = algebraMap k K r * δ ^ 2
  /-- The field norm of `γ` is a square in the base field. -/
  hnorm : IsSquare (Algebra.norm k γ)

/-- **L35 certificate.**  An `OddDegreeSquareCertificate` proves that `γ` is a
square in `K`; this is `isSquare_of_odd_finrank_norm_sq`. -/
theorem OddDegreeSquareCertificate.isSquare {γ : K}
    (c : OddDegreeSquareCertificate (k := k) (K := K) γ) : IsSquare γ :=
  isSquare_of_odd_finrank_norm_sq c.hodd c.hclass c.hnorm

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]

/-- **L35 discharge.**  If every ideal sample carries an odd-degree square
certificate for its field product `γ`, then the L35 event
`IsSquare (γ x)` holds on every sample.  Its failure mass is therefore at most
any explicit nonnegative loss. -/
theorem oddDegreeSeparation_of_certificates
    (γ : D.Sample → K)
    (cert : ∀ x, OddDegreeSquareCertificate (k := k) (K := K) (γ x))
    {loss : ℝ} (hloss : 0 ≤ loss) :
    OddDegreeSeparation (D := D) (fun x => IsSquare (γ x)) loss := by
  unfold OddDegreeSeparation
  exact fail_le_of_forall D.ideal (fun x => (cert x).isSquare) hloss

end OddDegreeStage

/-! ## Section 5: Discharging L37's evaluation-map half

`RandomizedEvaluationMaps.card_le_degree_or_proper_gcd_of_injective_images`
is the existing L37 evaluation-map alternative: a finite catalog of distinct
evaluation maps into `ZMod N` either has at most `deg F` elements or exposes a
proper divisor of `N` through a generator-image difference.  This proves the
Hensel/evaluation event on every sample, leaving only the exact Hensel lift
itself as part of the explicit L37 loss budget. -/

section EvaluationStage

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]
variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]

/-- **L37 evaluation-map discharge.**  Under the monogenic evaluation-catalog
hypotheses at each sample, the event "the catalog is degree-bounded or a proper
divisor is found" holds on every sample, so its failure mass is at most any
explicit nonnegative loss.  The catalog data (`F`, `θ`, the evaluation maps) may
depend on the sample; only the finite index type is fixed. -/
theorem henselEvaluation_of_evaluationCatalog
    (F : D.Sample → ℤ[X]) (hmonic : ∀ x, (F x).Monic)
    (θ : D.Sample → A)
    (hroot : ∀ x, (F x).eval₂ (Int.castRingHom A) (θ x) = 0)
    {hN : 1 < N} [NeZero N]
    (e : D.Sample → ι → A →+* ZMod N)
    (himg : ∀ x, Function.Injective (fun i => e x i (θ x)))
    {loss : ℝ} (hloss : 0 ≤ loss) :
    HenselEvaluation (D := D)
      (fun x =>
        Fintype.card ι ≤ (F x).natDegree ∨
          ∃ i j, let g := (e x i (θ x) - e x j (θ x)).val.gcd N
            1 < g ∧ g < N ∧ g ∣ N) loss := by
  unfold HenselEvaluation
  refine fail_le_of_forall D.ideal (fun x => ?_) hloss
  exact card_le_degree_or_proper_gcd_of_injective_images
    hN (F x) (hmonic x) (θ x) (hroot x) (e x) (himg x)

end EvaluationStage

/-! ## Axiom audit -/

#print axioms pmfProb_false
#print axioms fail_le_of_forall
#print axioms C5AlgebraInputs.totalLoss_nonneg
#print axioms C5AlgebraInputs.chebotarev_stage_fail_le
#print axioms C5AlgebraInputs.oddDegree_stage_fail_le
#print axioms C5AlgebraInputs.valuation_stage_fail_le
#print axioms C5AlgebraInputs.hensel_stage_fail_le
#print axioms C5AlgebraInputs.algebra_fail_le
#print axioms C5AlgebraInputs.stageBudget
#print axioms OddDegreeSquareCertificate.isSquare
#print axioms oddDegreeSeparation_of_certificates
#print axioms henselEvaluation_of_evaluationCatalog

end Cogentic.RandomizedC5Algebra
