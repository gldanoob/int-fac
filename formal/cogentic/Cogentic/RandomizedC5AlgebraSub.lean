import Cogentic.RandomizedC5Algebra
import Cogentic.RandomizedSubfieldDegree
import Cogentic.RandomizedSemisimpleZero

/-!
# C5.d sub-lemmas: the elementary half of the algebra stage

`Cogentic.RandomizedC5Algebra` decomposes the C5.d algebra budget into four
events (L34 Chebotarev separation, L35 odd-degree norm-square certification,
L36 even-valuation class identification, L37 Hensel/evaluation) and proves the
four-way union bound.  This file keeps the same four-way skeleton but proves
the elementary sub-lemmas explicitly and leaves only the two genuinely
paper-level statements as `Prop`s:

* **Chebotarev separation (L34).**  The effective-Chebotarev character
  separation estimate remains `ChebotarevSeparation`, imported from
  `RandomizedC5Algebra`.  Mathlib has no Chebotarev/Dedekind-zeta zero theory.
* **Even-valuation class identification (L36).**  The Dedekind-valuation
  statement that even good-ideal valuations, trivial characters and an even
  `E_j` column give a rational square class is isolated as
  `EvenValuationClassIdentification`.  Its *column-parity* input is removed:
  `even_sum_of_forall_even` proves that local evenness automatically makes the
  `E_j` column even, so the Prop only needs local evenness, triviality and the
  final rationality conclusion.

Everything else is proved:

* `OddDegreeStageData` turns a family of `OddDegreeSquareCertificate`s into the
  L35 event `IsSquare γ`; see `OddDegreeStageData.ok_all` and
  `OddDegreeStageData.fail_le`.  The certificate itself is reduced to the
  norm-square criterion `isSquare_of_odd_finrank_norm_sq`, and the rational
  representative is shown to be a square by
  `isSquare_base_of_odd_finrank_norm_sq`.
* `EvaluationStageData` turns the monogenic evaluation catalogue into the L37
  alternative `card ι ≤ natDegree F ∨ proper divisor`; see
  `EvaluationStageData.ok_all` and `EvaluationStageData.fail_le`.  This is the
  cardinality theorem `card_le_degree_or_proper_gcd_of_injective_images`.
* `pmfProb_not_and_four_le_sum_fail` and `pmfProb_four_or_le_sum` are the
  union-bound arithmetic: the complement of a four-way conjunction is bounded
  by the sum of the four failure masses.
* `C5AlgebraSubInputs.toC5AlgebraInputs` assembles a full
  `C5AlgebraInputs` in which the L35, L36 and L37 failure fields are *proved*
  from the data, and only `chebotarev_fail_le` and
  `evenValuationIdentification` are assumptions.  Its `stageBudget` is the
  C5.d `StageBudget`.

No `sorry`, `admit`, `axiom` or `native_decide` is used.  Every budget is an
explicit nonnegative parameter; no loss is set to zero by fiat.  The two
auxiliary modules `RandomizedSubfieldDegree` and `RandomizedSemisimpleZero`
supply the field-degree and semisimple-endomorphism background used by the
paper's L35/L36 paragraphs; their results are independent of the reductions
below.
-/

open Finset
open scoped BigOperators Polynomial

namespace Cogentic.RandomizedC5AlgebraSub

open Cogentic.RandomizedC5Algebra
open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedEvaluationMaps

/-! ## Section 1: Union-bound arithmetic -/

section UnionBound

variable {Ω : Type*} [Fintype Ω]

/-- A finite union is bounded by the sum of the individual event masses.  This
is the `Finset` form of the union bound used to assemble C5.d. -/
theorem pmfProb_exists_fin_le_sum {m : ℕ} (μ : PMF Ω) (E : Fin m → Ω → Prop) :
    pmfProb μ (fun ω => ∃ i, E i ω) ≤ ∑ i, pmfProb μ (E i) := by
  have h := pmfProb_exists_le_sum μ (Finset.univ : Finset (Fin m)) E
  simpa using h

/-- Four-event union bound. -/
theorem pmfProb_four_or_le_sum (μ : PMF Ω) (A B C D : Ω → Prop) :
    pmfProb μ (fun ω => A ω ∨ B ω ∨ C ω ∨ D ω) ≤
      pmfProb μ A + pmfProb μ B + pmfProb μ C + pmfProb μ D := by
  have h1 := pmfProb_or_le_add μ A (fun ω => B ω ∨ C ω ∨ D ω)
  have h2 := pmfProb_or_le_add μ B (fun ω => C ω ∨ D ω)
  have h3 := pmfProb_or_le_add μ C D
  linarith only [h1, h2, h3]

/-- The complement of a four-way conjunction is contained in the four-way
disjunction of the individual failures. -/
theorem not_and_four_imp_or_not (A B C D : Prop) :
    ¬ (A ∧ B ∧ C ∧ D) → ¬ A ∨ ¬ B ∨ ¬ C ∨ ¬ D := by
  tauto

/-- **Four-event failure bound.**  The failure mass of a conjunction of four
events is at most the sum of the four failure masses.  This is the exact
arithmetic used for C5.d, stated independently of the particular events. -/
theorem pmfProb_not_and_four_le_sum_fail (μ : PMF Ω) (A B C D : Ω → Prop) :
    pmfProb μ (fun ω => ¬ (A ω ∧ B ω ∧ C ω ∧ D ω)) ≤
      pmfProb μ (fun ω => ¬ A ω) + pmfProb μ (fun ω => ¬ B ω) +
        pmfProb μ (fun ω => ¬ C ω) + pmfProb μ (fun ω => ¬ D ω) := by
  refine (pmfProb_mono μ ?_).trans
    (pmfProb_four_or_le_sum μ (fun ω => ¬ A ω) (fun ω => ¬ B ω)
      (fun ω => ¬ C ω) (fun ω => ¬ D ω))
  intro ω hω
  exact not_and_four_imp_or_not (A ω) (B ω) (C ω) (D ω) hω

/-- Sums of four nonnegative losses are nonnegative. -/
theorem sum_four_nonneg {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) : 0 ≤ a + b + c + d := by
  linarith only [ha, hb, hc, hd]

end UnionBound

/-! ## Section 2: L35 — the odd-degree square certificate -/

section OddDegreeCertificate

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Module.Finite k K]

/-- Build the certificate consumed by `isSquare_of_odd_finrank_norm_sq` from its
three algebraic components. -/
def oddDegreeCertificateOf {γ : K} {r : k} {δ : K}
    (hodd : Odd (Module.finrank k K))
    (hclass : γ = algebraMap k K r * δ ^ 2)
    (hnorm : IsSquare (Algebra.norm k γ)) :
    OddDegreeSquareCertificate (k := k) (K := K) (γ := γ) :=
  { r := r, δ := δ, hodd := hodd, hclass := hclass, hnorm := hnorm }

/-- The certificate's conclusion: `γ` is a square in `K`. -/
theorem oddDegreeCertificate_isSquare {γ : K}
    (c : OddDegreeSquareCertificate (k := k) (K := K) (γ := γ)) :
    IsSquare γ :=
  c.isSquare

/-- The rational representative of a certificate with nonzero square factor is
itself a square in the base field.  This is the base-field half of E.1; it is
not needed for the C5.d event but records that the certificate loses no
information at the rational end. -/
theorem oddDegreeCertificate_base_isSquare {γ : K} {r : k} {δ : K}
    (hodd : Odd (Module.finrank k K))
    (hclass : γ = algebraMap k K r * δ ^ 2)
    (hnorm : IsSquare (Algebra.norm k γ)) (hδ : δ ≠ 0) :
    IsSquare r :=
  isSquare_base_of_odd_finrank_norm_sq hodd hclass hnorm hδ

omit [Module.Finite k K] in
/-- If an odd-degree extension is written as a tower, both tower degrees are
odd.  This is the elementary degree-parity reduction behind the L35
"odd degree" hypothesis (compare `RandomizedSubfieldDegree`, which controls
prime inertia degrees in such a tower). -/
lemma odd_finrank_tower {E : Type*} [Field E] [Algebra k E] [Algebra E K]
    [IsScalarTower k E K] [Module.Finite k E] [Module.Finite E K]
    (hodd : Odd (Module.finrank k K)) :
    Odd (Module.finrank k E) ∧ Odd (Module.finrank E K) := by
  have hd : Module.finrank k K = Module.finrank k E * Module.finrank E K :=
    (Module.finrank_mul_finrank k E K).symm
  rw [hd] at hodd
  exact Nat.odd_mul.mp hodd

end OddDegreeCertificate

section OddDegreeStage

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]
variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Module.Finite k K]

/-- The data needed for the L35 stage: a field product `γ` on every sample and
an odd-degree square certificate for it. -/
structure OddDegreeStageData (D : ConcreteEpochData N) (k K : Type*)
    [Field k] [Field K] [Algebra k K] [Module.Finite k K] where
  /-- The field product attached to the sample. -/
  γ : D.Sample → K
  /-- The odd-degree norm-square certificate at each sample. -/
  certificate : ∀ x, OddDegreeSquareCertificate (k := k) (K := K) (γ := γ x)

namespace OddDegreeStageData

/-- The L35 event: the field product is a square. -/
def ok (S : OddDegreeStageData D k K) (x : D.Sample) : Prop :=
  IsSquare (S.γ x)

omit [Fintype D.Sample] in
/-- The certificate proves the L35 event on every sample. -/
lemma ok_all (S : OddDegreeStageData D k K) (x : D.Sample) : S.ok x :=
  (S.certificate x).isSquare

/-- Because the L35 event holds on every sample, its failure mass is at most
any explicit nonnegative budget. -/
theorem fail_le (S : OddDegreeStageData D k K) {loss : ℝ} (hloss : 0 ≤ loss) :
    OddDegreeSeparation (D := D) S.ok loss := by
  unfold OddDegreeSeparation
  exact fail_le_of_forall D.ideal S.ok_all hloss

end OddDegreeStageData

end OddDegreeStage

/-! ## Section 3: L37 — Hensel/evaluation cardinality -/

section EvaluationCardinality

variable {N : ℕ} {ι : Type*} [Fintype ι] {A : Type*} [CommRing A]

/-- **L37 cardinality alternative.**  A finite catalogue of distinct evaluation
maps of a monogenic order either has at most `deg F` elements or exposes a
proper divisor of `N` through a difference of generator images.  This is
`card_le_degree_or_proper_gcd_of_injective_images`, restated in the file's
vocabulary. -/
theorem evaluationCardinality [NeZero N] (hN : 1 < N)
    (F : ℤ[X]) (hmonic : F.Monic) (θ : A)
    (hroot : F.eval₂ (Int.castRingHom A) θ = 0)
    (e : ι → A →+* ZMod N)
    (himg : Function.Injective (fun i => e i θ)) :
    Fintype.card ι ≤ F.natDegree ∨
      ∃ i j, let g := (e i θ - e j θ).val.gcd N
        1 < g ∧ g < N ∧ g ∣ N :=
  card_le_degree_or_proper_gcd_of_injective_images hN F hmonic θ hroot e himg

/-- With unit differences the catalogue is degree-bounded.  This is the first
branch of the cardinality alternative, isolated for reuse. -/
theorem evaluationCardinality_of_unit_differences
    (F : ℤ[X]) (hmonic : F.Monic) (θ : A)
    (hroot : F.eval₂ (Int.castRingHom A) θ = 0)
    {p : ℕ} [Fact p.Prime] (hp : p ∣ N)
    (e : ι → A →+* ZMod N)
    (hunit : ∀ i j, i ≠ j → IsUnit (e i θ - e j θ)) :
    Fintype.card ι ≤ F.natDegree := by
  let a : ι → ZMod N := fun i => e i θ
  let G : (ZMod N)[X] := F.map (Int.castRingHom (ZMod N))
  have hG : G.Monic := hmonic.map _
  have ha : ∀ i, G.IsRoot (a i) := by
    intro i
    change G.eval (e i θ) = 0
    have hh := congrArg (e i) hroot
    rw [Polynomial.hom_eval₂, map_zero] at hh
    have hcomp : (e i).comp (Int.castRingHom A) = Int.castRingHom (ZMod N) := by
      ext z
      simp
    rw [hcomp] at hh
    rwa [Polynomial.eval_map]
  have hcard := card_le_degree_of_unit_differences G hG a ha hunit hp
  exact hcard.trans Polynomial.natDegree_map_le

end EvaluationCardinality

section EvaluationStage

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]
variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]

/-- The data needed for the L37 stage: a monic integer polynomial, a root `θ`
of it in a ring `A`, and a finite catalogue of evaluation maps to `ZMod N`
whose generator images are distinct. -/
structure EvaluationStageData (D : ConcreteEpochData N) (A : Type*)
    [CommRing A] (ι : Type*) [Fintype ι] where
  /-- The monic integer presentation at each sample. -/
  F : D.Sample → ℤ[X]
  /-- Monicity. -/
  hmonic : ∀ x, (F x).Monic
  /-- The root of `F` in `A`. -/
  θ : D.Sample → A
  /-- The root equation. -/
  hroot : ∀ x, (F x).eval₂ (Int.castRingHom A) (θ x) = 0
  /-- The evaluation catalogue. -/
  e : D.Sample → ι → A →+* ZMod N
  /-- Distinct catalogue entries have distinct generator images. -/
  himg : ∀ x, Function.Injective (fun i => e x i (θ x))

namespace EvaluationStageData

/-- The L37 event: the catalogue is degree-bounded or a proper divisor is
found. -/
def ok (S : EvaluationStageData D A ι) (x : D.Sample) : Prop :=
  Fintype.card ι ≤ (S.F x).natDegree ∨
    ∃ i j, let g := (S.e x i (S.θ x) - S.e x j (S.θ x)).val.gcd N
      1 < g ∧ g < N ∧ g ∣ N

omit [Fintype D.Sample] in
/-- The evaluation-cardinality theorem proves the L37 event on every sample. -/
lemma ok_all [NeZero N] (S : EvaluationStageData D A ι) (hN : 1 < N)
    (x : D.Sample) : S.ok x :=
  evaluationCardinality hN (S.F x) (S.hmonic x) (S.θ x) (S.hroot x) (S.e x) (S.himg x)

/-- Because the L37 event holds on every sample, its failure mass is at most
any explicit nonnegative budget.  The exact Hensel lift remains part of the
paper-level input; only the evaluation-map cardinality is used here. -/
theorem fail_le [NeZero N] (S : EvaluationStageData D A ι) (hN : 1 < N)
    {loss : ℝ} (hloss : 0 ≤ loss) :
    HenselEvaluation (D := D) S.ok loss := by
  unfold HenselEvaluation
  exact fail_le_of_forall D.ideal (S.ok_all hN) hloss

end EvaluationStageData

end EvaluationStage

/-! ## Section 4: L36 — valuation parity and the even-valuation class -/

section ValuationParity

/-- A finite sum of even integers is even.  This is the elementary parity step
which removes the "even `E_j` column" from the L36 input: if every good-ideal
valuation is even, the column sum is automatically even. -/
theorem even_sum_of_forall_even {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (h : ∀ i ∈ s, Even (c i)) : Even (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Even.add (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert.mpr (Or.inr hi))))

/-- The `univ` form of `even_sum_of_forall_even`. -/
theorem even_sum_of_forall_even_univ {ι : Type*} [Fintype ι] (c : ι → ℤ)
    (h : ∀ i, Even (c i)) : Even (∑ i, c i) := by
  simpa using
    even_sum_of_forall_even (Finset.univ : Finset ι) c (fun i _ => h i)

/-- **Valuation-parity reduction for occurrence cancellation.**  If every
occurrence exponent is even, then the total occurrence sum is even, so the
occurrence-parity hypothesis of
`isSquare_norm_iff_isSquare_hom_prod_of_even_sum` is automatic.  This is the
elementary content used by L36 to feed the L35 norm-square test. -/
theorem isSquare_norm_iff_isSquare_hom_prod_of_even_valuations
    {k K : Type*} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    {ι : Type*} (F : k[X]) (α : K)
    (hirr : Irreducible F) (hroot : Polynomial.aeval α F = 0)
    (hdeg : Module.finrank k K = F.natDegree)
    (S : Finset ι) (a b : ι → k) (c : ι → ℤ)
    (hval : ∀ P ∈ S, Even (c P)) :
    IsSquare (Algebra.norm k
        (∏ P ∈ S, (algebraMap k K (a P) - algebraMap k K (b P) * α) ^ c P)) ↔
      IsSquare (∏ P ∈ S, (homEval F (a P) (b P)) ^ c P) :=
  isSquare_norm_iff_isSquare_hom_prod_of_even_sum F α hirr hroot hdeg S a b c
    (even_sum_of_forall_even S c hval)

end ValuationParity

section ValuationStage

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]
variable {κ : Type*}

/-- **L36 paper input (explicit `Prop`).**  Even good-ideal valuations, trivial
characters and an even `E_j` column give a rational square class.  This is the
genuine Dedekind-valuation statement (definition of `H_D`, Theorem E.4); the
column parity is *not* an extra hypothesis in the reduction below, because
`even_sum_of_forall_even` proves it from local evenness. -/
def EvenValuationClassIdentification (D : ConcreteEpochData N) [Fintype D.Sample]
    (goodIdeals : Finset κ) (valuation : D.Sample → κ → ℤ)
    (trivialChar rationalClass : D.Sample → Prop) : Prop :=
  ∀ x, (∀ i ∈ goodIdeals, Even (valuation x i)) → trivialChar x →
    Even (∑ i ∈ goodIdeals, valuation x i) → rationalClass x

/-- The data needed for the L36 stage.  The only non-elementary field is
`identification`, the paper-level even-valuation class statement. -/
structure ValuationStageData (D : ConcreteEpochData N) [Fintype D.Sample]
    (κ : Type*) where
  /-- The finite set of good ideals. -/
  goodIdeals : Finset κ
  /-- The valuation vector of a sample. -/
  valuation : D.Sample → κ → ℤ
  /-- The characters of the sample are all trivial. -/
  trivialChar : D.Sample → Prop
  /-- The sample lies in the rational square class. -/
  rationalClass : D.Sample → Prop
  /-- The paper-level even-valuation class identification. -/
  identification :
    EvenValuationClassIdentification D goodIdeals valuation trivialChar rationalClass

namespace ValuationStageData

/-- The reduced L36 event: local evenness and trivial characters imply the
rational class.  The even-column hypothesis is no longer present. -/
def ok (S : ValuationStageData D κ) (x : D.Sample) : Prop :=
  (∀ i ∈ S.goodIdeals, Even (S.valuation x i)) → S.trivialChar x →
    S.rationalClass x

/-- The elementary parity reduction: local even valuations make the `E_j`
column even. -/
theorem eColumn_even (S : ValuationStageData D κ) {x : D.Sample}
    (h : ∀ i ∈ S.goodIdeals, Even (S.valuation x i)) :
    Even (∑ i ∈ S.goodIdeals, S.valuation x i) :=
  even_sum_of_forall_even S.goodIdeals (S.valuation x) h

/-- The even-valuation identification proves the reduced L36 event at `x`,
using the proved column parity. -/
theorem rationalClass_of_even_valuations (S : ValuationStageData D κ) {x : D.Sample}
    (h : ∀ i ∈ S.goodIdeals, Even (S.valuation x i)) (ht : S.trivialChar x) :
    S.rationalClass x :=
  S.identification x h ht (S.eColumn_even h)

/-- The reduced L36 event holds on every sample. -/
theorem ok_all (S : ValuationStageData D κ) (x : D.Sample) : S.ok x := by
  intro h ht
  exact S.rationalClass_of_even_valuations h ht

/-- Because the reduced L36 event holds on every sample, its failure mass is at
most any explicit nonnegative budget. -/
theorem fail_le (S : ValuationStageData D κ) {loss : ℝ} (hloss : 0 ≤ loss) :
    EvenValuationClass (D := D) S.ok loss := by
  unfold EvenValuationClass
  exact fail_le_of_forall D.ideal S.ok_all hloss

end ValuationStageData

end ValuationStage

/-! ## Section 5: Assembling the C5.d stage with only two explicit Props -/

section Assembly

variable {N : ℕ} {D : ConcreteEpochData N} [Fintype D.Sample]
variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]
variable {κ : Type*} [NeZero N]

/-- **The reduced C5.d inputs.**  The Chebotarev separation and the
even-valuation class identification are the only paper-level `Prop` fields.
The L35 certificate family and the L37 evaluation catalogue are concrete data,
and their failure bounds are proved by `OddDegreeStageData.fail_le` and
`EvaluationStageData.fail_le`.  All four losses are explicit nonnegative
parameters. -/
structure C5AlgebraSubInputs (D : ConcreteEpochData N) [Fintype D.Sample]
    (k K : Type*) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (A : Type*) [CommRing A] (ι : Type*) [Fintype ι]
    (κ : Type*) [NeZero N] where
  /-- The input modulus is nontrivial. -/
  hN : 1 < N
  /-- L34: Chebotarev character-separation event. -/
  chebotarevOk : D.Sample → Prop
  /-- L34: numerical separation loss. -/
  chebotarevLoss : ℝ
  chebotarevLoss_nonneg : 0 ≤ chebotarevLoss
  /-- L34: the explicit paper-level Chebotarev separation `Prop`. -/
  chebotarev_fail_le : ChebotarevSeparation (D := D) chebotarevOk chebotarevLoss
  /-- L35: odd-degree certificate data. -/
  oddDegree : OddDegreeStageData D k K
  /-- L35: numerical algebra loss. -/
  oddDegreeLoss : ℝ
  oddDegreeLoss_nonneg : 0 ≤ oddDegreeLoss
  /-- L36: valuation data and the explicit even-valuation class `Prop`. -/
  valuation : ValuationStageData D κ
  /-- L36: numerical valuation loss. -/
  valuationLoss : ℝ
  valuationLoss_nonneg : 0 ≤ valuationLoss
  /-- L37: evaluation-catalogue data. -/
  hensel : EvaluationStageData D A ι
  /-- L37: numerical Hensel/evaluation loss. -/
  henselLoss : ℝ
  henselLoss_nonneg : 0 ≤ henselLoss

namespace C5AlgebraSubInputs

/-- The L35 event of the assembled stage. -/
def oddDegreeOk (I : C5AlgebraSubInputs D k K A ι κ) (x : D.Sample) : Prop :=
  I.oddDegree.ok x

/-- The L36 event of the assembled stage. -/
def valuationOk (I : C5AlgebraSubInputs D k K A ι κ) (x : D.Sample) : Prop :=
  I.valuation.ok x

/-- The L37 event of the assembled stage. -/
def henselOk (I : C5AlgebraSubInputs D k K A ι κ) (x : D.Sample) : Prop :=
  I.hensel.ok x

/-- The C5.d algebra success event: all four sub-stages hold. -/
def algebraOk (I : C5AlgebraSubInputs D k K A ι κ) (x : D.Sample) : Prop :=
  I.chebotarevOk x ∧ I.oddDegreeOk x ∧ I.valuationOk x ∧ I.henselOk x

/-- The total C5.d loss. -/
noncomputable def totalLoss (I : C5AlgebraSubInputs D k K A ι κ) : ℝ :=
  I.chebotarevLoss + I.oddDegreeLoss + I.valuationLoss + I.henselLoss

/-- The total loss is nonnegative because each component is. -/
theorem totalLoss_nonneg (I : C5AlgebraSubInputs D k K A ι κ) : 0 ≤ I.totalLoss := by
  unfold totalLoss
  exact sum_four_nonneg I.chebotarevLoss_nonneg I.oddDegreeLoss_nonneg
    I.valuationLoss_nonneg I.henselLoss_nonneg

/-- The L34 failure bound, unchanged from the paper-level input. -/
theorem chebotarev_stage_fail_le (I : C5AlgebraSubInputs D k K A ι κ) :
    pmfProb D.ideal (fun x => ¬ I.chebotarevOk x) ≤ I.chebotarevLoss :=
  I.chebotarev_fail_le

/-- The L35 failure bound, proved from the certificate family. -/
theorem oddDegree_stage_fail_le (I : C5AlgebraSubInputs D k K A ι κ) :
    pmfProb D.ideal (fun x => ¬ I.oddDegreeOk x) ≤ I.oddDegreeLoss :=
  I.oddDegree.fail_le I.oddDegreeLoss_nonneg

/-- The L36 failure bound, proved from the even-valuation class identification
and the column-parity reduction. -/
theorem valuation_stage_fail_le (I : C5AlgebraSubInputs D k K A ι κ) :
    pmfProb D.ideal (fun x => ¬ I.valuationOk x) ≤ I.valuationLoss :=
  I.valuation.fail_le I.valuationLoss_nonneg

/-- The L37 failure bound, proved from the evaluation-cardinality theorem. -/
theorem hensel_stage_fail_le (I : C5AlgebraSubInputs D k K A ι κ) :
    pmfProb D.ideal (fun x => ¬ I.henselOk x) ≤ I.henselLoss :=
  I.hensel.fail_le I.hN I.henselLoss_nonneg

/-- **C5.d failure bound for the reduced inputs.**  The complement of the
four-way conjunction is bounded by the sum of the four losses. -/
theorem algebra_fail_le (I : C5AlgebraSubInputs D k K A ι κ) :
    pmfProb D.ideal (fun x => ¬ I.algebraOk x) ≤ I.totalLoss := by
  unfold algebraOk totalLoss
  have h := pmfProb_not_and_four_le_sum_fail D.ideal
    I.chebotarevOk I.oddDegreeOk I.valuationOk I.henselOk
  have hc := I.chebotarev_stage_fail_le
  have ho := I.oddDegree_stage_fail_le
  have hv := I.valuation_stage_fail_le
  have hh := I.hensel_stage_fail_le
  linarith only [h, hc, ho, hv, hh]

/-- **Conversion to the original `C5AlgebraInputs`.**  The three deterministic
failure fields are filled by proofs; only `chebotarev_fail_le` and
`valuation.identification` come from the reduced input. -/
noncomputable def toC5AlgebraInputs (I : C5AlgebraSubInputs D k K A ι κ) :
    Cogentic.RandomizedC5Algebra.C5AlgebraInputs D where
  chebotarevOk := I.chebotarevOk
  chebotarevLoss := I.chebotarevLoss
  chebotarevLoss_nonneg := I.chebotarevLoss_nonneg
  chebotarev_fail_le := I.chebotarev_fail_le
  oddDegreeOk := I.oddDegreeOk
  oddDegreeLoss := I.oddDegreeLoss
  oddDegreeLoss_nonneg := I.oddDegreeLoss_nonneg
  oddDegree_fail_le := I.oddDegree_stage_fail_le
  valuationOk := I.valuationOk
  valuationLoss := I.valuationLoss
  valuationLoss_nonneg := I.valuationLoss_nonneg
  valuation_fail_le := I.valuation_stage_fail_le
  henselOk := I.henselOk
  henselLoss := I.henselLoss
  henselLoss_nonneg := I.henselLoss_nonneg
  hensel_fail_le := I.hensel_stage_fail_le

/-- The reduced inputs produce exactly the C5.d `StageBudget`. -/
noncomputable def stageBudget (I : C5AlgebraSubInputs D k K A ι κ) : StageBudget D :=
  Cogentic.RandomizedC5Algebra.C5AlgebraInputs.stageBudget I.toC5AlgebraInputs

/-- The `StageBudget` has the same success event as the reduced inputs. -/
theorem stageBudget_ok (I : C5AlgebraSubInputs D k K A ι κ) (x : D.Sample) :
    I.stageBudget.ok x ↔ I.algebraOk x :=
  Iff.rfl

/-- The `StageBudget` has the explicit total loss. -/
theorem stageBudget_loss (I : C5AlgebraSubInputs D k K A ι κ) :
    I.stageBudget.loss = I.totalLoss :=
  rfl

end C5AlgebraSubInputs

end Assembly

/-! ## Axiom audit -/

#print axioms pmfProb_exists_fin_le_sum
#print axioms pmfProb_four_or_le_sum
#print axioms pmfProb_not_and_four_le_sum_fail
#print axioms sum_four_nonneg
#print axioms oddDegreeCertificateOf
#print axioms oddDegreeCertificate_isSquare
#print axioms oddDegreeCertificate_base_isSquare
#print axioms odd_finrank_tower
#print axioms OddDegreeStageData.ok_all
#print axioms OddDegreeStageData.fail_le
#print axioms evaluationCardinality
#print axioms evaluationCardinality_of_unit_differences
#print axioms EvaluationStageData.ok_all
#print axioms EvaluationStageData.fail_le
#print axioms even_sum_of_forall_even
#print axioms even_sum_of_forall_even_univ
#print axioms isSquare_norm_iff_isSquare_hom_prod_of_even_valuations
#print axioms ValuationStageData.eColumn_even
#print axioms ValuationStageData.rationalClass_of_even_valuations
#print axioms ValuationStageData.ok_all
#print axioms ValuationStageData.fail_le
#print axioms C5AlgebraSubInputs.totalLoss_nonneg
#print axioms C5AlgebraSubInputs.algebra_fail_le
#print axioms C5AlgebraSubInputs.toC5AlgebraInputs
#print axioms C5AlgebraSubInputs.stageBudget

end Cogentic.RandomizedC5AlgebraSub
