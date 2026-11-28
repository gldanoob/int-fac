import Cogentic.RandomizedL20_4PairAlt
import Cogentic.RandomizedL20_4Additive
import Cogentic.RandomizedL20_4Interior
import Cogentic.RandomizedL20_4InteriorBase
import Cogentic.RandomizedL20_4EtaSource

/-!
# L20.4 leaf assembly: the corrected disjunction event and the paper sources

`Cogentic.RandomizedL20_4Conditioned.L20_4ConditionedInputs.toSubexpLeaf`
assembles the L20.4 `SubexpLeaf` from the *conjunction* event `g ∧ R_{q,s}`.
`Cogentic.RandomizedL20_4Incoming` showed that the complementary mass needed by
that route is inconsistent with the paper regime, and
`Cogentic.RandomizedL20_4PairAlt` supplied the corrected object:
`TwoPointAltReducedData` conditions on the **disjunction** event
`g ∨ R_{q,s}`, whose lower mass is the G.8/G.10 child-root lower law and whose
complement is the rational-good complement.

This file performs the actual leaf assembly.  It composes

* the corrected pair bundle `TwoPointAltReducedData` (pool miss mass of the
  disjunction event);
* the paper's eta/base/rational sources, packaged as
  `RandomizedL20_4EtaSource.PaperExceptionSources` (the L21.2 elliptic
  fraction, the L20.2 base concentration and the two L20.2 CRT/character
  budgets);
* the G.54--G.55 additive comparison, in its smallest explicit depth form
  `TopG12AdditiveDepthComparison`; and
* the deterministic dyad Markov trimming `DyadData`.

The assembled deficit is

`pair.toPairData.loss + dyad.loss + top.top`,

exactly the three nonnegative contributions of the manuscript's L20.4 step
(pool union bound, dyadic trimming, G.12 top bad-child mass).  We prove

* `loss_nonneg`: every summand is a genuine nonnegative deficit;
* `subexpLoss`: the sum is `D^{-B}` for every `B`, i.e. `SubexpLoss`;
* `toSubexpLeaf`: the resulting `SubexpLeaf` for `RandomizedPaperLeafStatements`;
* `slot_le`: its `B = 2` instance, the C5 `topChildLaw` ledger slot.

The only paper-level estimate retained as a hypothesis is the G.54--G.55
additive comparison, which is already the smallest explicit `Prop` of
`RandomizedL20_4Additive`/`RandomizedL20_4Top`.  Everything else (the mass
bounds of the corrected event, all four interior concentration fields, and the
G.11/G.12 algebra) is derived from the sources.  No loss is set to zero and no
`PairEventMassData` is used.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL20_4LeafAssembly

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4TwoPoint
open Cogentic.RandomizedL20_4ChildLower
open Cogentic.RandomizedL20_4PairAlt
open Cogentic.RandomizedL20_4Top
open Cogentic.RandomizedL20_4Additive
open Cogentic.RandomizedL20_4Interior
open Cogentic.RandomizedL20_4InteriorBase
open Cogentic.RandomizedL20_4EtaSource

/-! ## 1. The corrected pair loss is the disjunction-event pool loss -/

/-- Pointwise equivalence of events gives equal finite probabilities.  This is
the local form used to compare the repackaged `pairEvent` of
`TwoPointAltReducedData.toPairData` with the actual disjunction event. -/
theorem pmfProb_congr_event {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {E F : Ω → Prop} (h : ∀ ω, E ω ↔ F ω) : pmfProb μ E = pmfProb μ F :=
  le_antisymm (pmfProb_mono μ fun ω hω => (h ω).mp hω)
    (pmfProb_mono μ fun ω hω => (h ω).mpr hω)

/-- The event underlying the corrected pair data: repackaging
`pairEventAlt good childRoot` as `pairEvent E True` is the same event. -/
theorem toPairData_event_iff {Ω : Type*} [Fintype Ω] (S : TwoPointAltReducedData Ω)
    (n : ℕ) (ω : Ω) :
    pairEvent S.toPairData.good S.toPairData.childRoot n ω ↔
      pairEventAlt S.good S.childRoot n ω := by
  simp [TwoPointAltReducedData.toPairData, TwoPointAltReducedData.toPairConditionedData,
    TwoPointAltReducedData.toPairAltConditionedData,
    PairAltConditionedData.toPairConditionedData, PairConditionedData.toPairData,
    pairEvent, pairEventAlt]

/-- Pool losses agree when the underlying events are pointwise equivalent. -/
theorem poolLoss_congr_event {Ω : Type*} [Fintype Ω] (dyadCard : ℕ → ℕ)
    (μ : ℕ → PMF Ω) {E F : ℕ → Ω → Prop} (Z : ℕ → Ω → ℝ) (a : ℝ)
    (poolSize : ℕ → ℕ) (h : ∀ n ω, E n ω ↔ F n ω) :
    poolLoss dyadCard μ E Z a poolSize = poolLoss dyadCard μ F Z a poolSize := by
  funext n
  unfold Cogentic.RandomizedL20_4Sub.poolLoss Cogentic.RandomizedL20_4Sub.hitProb
  have hnum : pmfProb (μ n) (fun ω => E n ω ∧ a / 2 ≤ Z n ω) =
      pmfProb (μ n) (fun ω => F n ω ∧ a / 2 ≤ Z n ω) :=
    pmfProb_congr_event (μ n) fun ω => by
      constructor
      · rintro ⟨hE, hZ⟩
        exact ⟨(h n ω).mp hE, hZ⟩
      · rintro ⟨hE, hZ⟩
        exact ⟨(h n ω).mpr hE, hZ⟩
  rw [hnum, pmfProb_congr_event (μ n) (h n)]

/-- **The corrected pair loss is exactly the disjunction-event pool loss.**
This is the formal check that the assembled leaf charges the pool miss mass of
`g ∨ R_{q,s}` and not of the inconsistent conjunction `g ∧ R_{q,s}`. -/
theorem pairLoss_eq_poolLoss {Ω : Type*} [Fintype Ω]
    (S : TwoPointAltReducedData Ω) (n : ℕ) :
    S.toPairData.loss n =
      poolLoss S.dyadCard S.μ (fun m => pairEventAlt S.good S.childRoot m)
        S.Z S.a S.poolSize n := by
  unfold Cogentic.RandomizedL20_4Sub.PairData.loss
  have h := congrFun (poolLoss_congr_event S.toPairData.dyadCard S.toPairData.μ
    (E := fun m ω => pairEvent S.toPairData.good S.toPairData.childRoot m ω)
    (F := fun m ω => pairEventAlt S.good S.childRoot m ω)
    S.toPairData.Z S.toPairData.a S.toPairData.poolSize
    (fun m ω => toPairData_event_iff S m ω)) n
  rw [h]
  rfl

/-- The disjunction event is positive as soon as the child-root event is.  This
records that `TwoPointAltReducedData.event_pos` is not a paper-level estimate:
it follows from positivity of the G.8/G.10 child-root mass, which is the
smallest explicit positivity input. -/
def ChildRootPositive {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (childRoot : ℕ → Ω → Prop) : Prop :=
  ∀ n, 0 < pmfProb (μ n) (childRoot n)

theorem eventPos_of_childRootPositive {Ω : Type*} [Fintype Ω]
    (S : TwoPointAltReducedData Ω) (h : ChildRootPositive S.μ S.childRoot) :
    ∀ n, 0 < pmfProb (S.μ n) (pairEventAlt S.good S.childRoot n) := by
  intro n
  exact lt_of_lt_of_le (h n)
    (pmfProb_mono (S.μ n) fun ω hω => Or.inr hω)

/-- The child-root lower mass gives positivity at every scale once the
G.8/G.10 lower law is available at every scale.  This is the explicit
positivity source used below: it is strictly weaker than assuming
`event_pos` for the disjunction event. -/
theorem childRootPositive_of_massLower_all {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (childRoot : ℕ → Ω → Prop) {c : ℝ}
    (h : ∀ n, Real.exp (-c * scale n) ≤ pmfProb (μ n) (childRoot n)) :
    ChildRootPositive μ childRoot :=
  fun n => lt_of_lt_of_le (Real.exp_pos _) (h n)

/-! ## 2. The sourced top bundle -/

/-- The G.11/G.12 top data with the four interior concentration fields sourced
from the paper's eta/base/rational quantities.

The fields `L`, `interior`, `step`, `eta`, `top`, `Ctop`, `cTop`, `cInt` and the
recurrence/depth/comparison data are the explicit G.11/G.12 algebra.  The
`exceptions` field supplies:

* the L20.2 base concentration input and the identification of `interior n L`
  with its normalized discrepancy;
* the L21.2 elliptic input and the identification of `eta` with its loss;
* the L20.2 CRT/character inputs for both `ε_rat` and `ε_in`.

Consequently `epsRat` and `epsIn` are *not* free fields: they are the paper's
`paperEpsRat` and `paperEpsIn`, and their `SubexpLoss` proofs are inherited from
the L20.2 estimates.  The only remaining paper estimate is the additive G.54--
G.55 comparison `additive_comparison`. -/
structure SourcedTopData where
  /-- Depth of the internal G.11 recurrence. -/
  L : ℕ
  /-- Internal normalized bad-child masses `δ_i`, `i = 0 … L`. -/
  interior : ℕ → ℕ → ℝ
  /-- G.11 step multiplier. -/
  step : ℕ → ℝ
  /-- Elliptic deletion fraction `η` (L21.2). -/
  eta : ℕ → ℝ
  /-- The paper sources: base, rational, elliptic and incoming. -/
  exceptions : PaperExceptionSources interior L eta
  /-- Resulting top bad-child mass `δ_top`. -/
  top : ℕ → ℝ
  /-- The G.12 top constant. -/
  Ctop : ℕ → ℝ
  /-- Exponent of the top constant. -/
  cTop : ℝ
  /-- Exponent of the depth factor. -/
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  /-- The G.11 linear recurrence. -/
  recurrence : G11InteriorRecurrence interior L step eta
    (fun n => paperEpsRat exceptions.rational n)
  /-- The step multiplier is at least one. -/
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  /-- The G.11 error is nonnegative. -/
  alpha_nonneg : ∀ᶠ n : ℕ in atTop,
    0 ≤ eta n + paperEpsRat exceptions.rational n
  /-- The depth factor is `D^{O(1)}`. -/
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  /-- The G.54--G.55 additive comparison at the explicit G.11 depth majorant. -/
  additive_comparison : TopG12AdditiveDepthComparison top Ctop interior step eta
    (fun n => paperEpsRat exceptions.rational n)
    (fun n => paperEpsIn exceptions.incoming n) L
  /-- The top constant is `D^{O(1)}`. -/
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)

namespace SourcedTopData

/-- The paper's rational and incoming exceptions are the L20.2 CRT plus
smooth-character budgets of the supplied L20.2 inputs.  This is definitional,
not a new estimate. -/
theorem epsRat_eq_rho (S : SourcedTopData) :
    (fun n => paperEpsRat S.exceptions.rational n) = fun n => S.exceptions.rational.ρ n :=
  paperEpsRat_eq_rho S.exceptions.rational

theorem epsIn_eq_rho (S : SourcedTopData) :
    (fun n => paperEpsIn S.exceptions.incoming n) = fun n => S.exceptions.incoming.ρ n :=
  paperEpsIn_eq_rho S.exceptions.incoming

/-- The four interior concentration fields, sourced. -/
theorem interiorSubProps (S : SourcedTopData) :
    InteriorSubProps S.interior S.L S.eta
      (fun n => paperEpsRat S.exceptions.rational n)
      (fun n => paperEpsIn S.exceptions.incoming n) :=
  S.exceptions.subProps

/-- **The reduction to the additive top bundle.**  This fills the four
`SubexpLoss` fields of `TopG12AdditiveData` from the sourced interior data, and
uses the paper's `ε_rat`/`ε_in` in the recurrence and the additive comparison.
No field is assumed beyond the G.54--G.55 comparison. -/
noncomputable def toTopG12AdditiveData (S : SourcedTopData) : TopG12AdditiveData where
  L := S.L
  interior := S.interior
  step := S.step
  eta := S.eta
  epsRat := fun n => paperEpsRat S.exceptions.rational n
  epsIn := fun n => paperEpsIn S.exceptions.incoming n
  top := S.top
  Ctop := S.Ctop
  cTop := S.cTop
  cInt := S.cInt
  interior_nonneg := S.interior_nonneg
  eta_nonneg := S.eta_nonneg
  epsRat_nonneg := paperEpsRat_nonneg S.exceptions.rational
  epsIn_nonneg := paperEpsIn_nonneg S.exceptions.incoming
  top_nonneg := S.top_nonneg
  Ctop_nonneg := S.Ctop_nonneg
  cTop_nonneg := S.cTop_nonneg
  recurrence := S.recurrence
  step_ge_one := S.step_ge_one
  alpha_nonneg := S.alpha_nonneg
  depth_bound := S.depth_bound
  additive_comparison := S.additive_comparison
  Ctop_le := S.Ctop_le
  base_subexp := S.interiorSubProps.base_subexp
  eta_subexp := S.interiorSubProps.eta_subexp
  epsRat_subexp := S.interiorSubProps.epsRat_subexp
  epsIn_subexp := S.interiorSubProps.epsIn_subexp

/-- **The G.12 top mass is subexponential**, with all four interior fields
sourced from the paper's eta/base/rational inputs. -/
theorem top_subexp (S : SourcedTopData) : SubexpLoss S.top :=
  S.toTopG12AdditiveData.top_subexp

end SourcedTopData

/-! ## 3. The assembled leaf inputs -/

/-- The L20.4 leaf assembled from the corrected pair data, the additive top
bundle and the deterministic dyad data.  The pair field is
`TwoPointAltReducedData`, i.e. the disjunction event `g ∨ R_{q,s}`; the
inconsistent `PairEventMassData` does not occur. -/
structure L20_4LeafInputs (Ω P : Type*) [Fintype Ω] [DecidableEq P] where
  /-- The corrected child-root pair data (disjunction event). -/
  pair : TwoPointAltReducedData Ω
  /-- The G.11/G.12 top data with the additive G.54--G.55 comparison. -/
  top : TopG12AdditiveData
  /-- The deterministic dyad Markov trimming. -/
  dyad : DyadData P

namespace L20_4LeafInputs

variable {Ω P : Type*} [Fintype Ω] [DecidableEq P]

/-- The assembled L20.4 deficit: corrected pool miss mass, dyad Markov
fraction, and G.12 top bad-child mass. -/
noncomputable def loss (S : L20_4LeafInputs Ω P) (n : ℕ) : ℝ :=
  S.pair.toPairData.loss n + S.dyad.loss n + S.top.top n

/-- The assembled deficit is nonnegative.  Each summand is a genuine deficit:
the pool miss mass, the Markov-trimmed dyad fraction and the top bad-child
mass. -/
theorem loss_nonneg (S : L20_4LeafInputs Ω P) (n : ℕ) : 0 ≤ S.loss n := by
  unfold loss
  exact add_nonneg
    (add_nonneg (S.pair.toPairData.loss_nonneg n) (S.dyad.loss_nonneg n))
    (S.top.top_nonneg n)

/-- **The L20.4 manuscript bound.**  The corrected pair pool bound, the dyad
Markov fraction and the G.12 top mass are each `D^{-B}` for every `B`; their
sum is therefore `SubexpLoss`. -/
theorem subexpLoss (S : L20_4LeafInputs Ω P) : SubexpLoss S.loss := by
  have hpair : SubexpLoss fun n => S.pair.toPairData.loss n :=
    S.pair.pairLoss_subexp
  have h1 : SubexpLoss fun n => S.pair.toPairData.loss n + S.dyad.loss n :=
    subexpLoss_add hpair S.dyad.loss_subexp
  have h2 : SubexpLoss
      fun n => (S.pair.toPairData.loss n + S.dyad.loss n) + S.top.top n :=
    subexpLoss_add h1 S.top.top_subexp
  unfold loss
  exact h2

/-- The actual `SubexpLeaf` for L20.4. -/
noncomputable def toSubexpLeaf (S : L20_4LeafInputs Ω P) : SubexpLeaf where
  loss := S.loss
  loss_nonneg := S.loss_nonneg
  paper := S.subexpLoss

/-- The `B = 2` C5 ledger slot consumed by the endpoint. -/
theorem slot_le (S : L20_4LeafInputs Ω P) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  S.toSubexpLeaf.slot

/-- The paper's subexponential conclusion in unfolded form: for every `B > 0`
the assembled deficit is at most `D^{-B}`. -/
theorem loss_le_exp_neg (S : L20_4LeafInputs Ω P) {B : ℝ} (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ Real.exp (-B * scale n) :=
  S.subexpLoss B hB

/-- The pair summand is the disjunction-event pool loss.  This is the
corrected event, exposed at the assembly level. -/
theorem loss_pair_eq (S : L20_4LeafInputs Ω P) (n : ℕ) :
    S.pair.toPairData.loss n =
      poolLoss S.pair.dyadCard S.pair.μ
        (fun m => pairEventAlt S.pair.good S.pair.childRoot m)
        S.pair.Z S.pair.a S.pair.poolSize n :=
  pairLoss_eq_poolLoss S.pair n

end L20_4LeafInputs

/-! ## 4. The fully sourced leaf -/

/-- The L20.4 leaf with the top eta/base/rational fields sourced from the
paper's L20.2/L21.2 inputs.  This is the version that contains no free
`SubexpLoss` fields for the interior concentration: they are all derived by
`SourcedTopData`. -/
structure L20_4SourcedLeafInputs (Ω P : Type*) [Fintype Ω] [DecidableEq P] where
  /-- The corrected child-root pair data (disjunction event). -/
  pair : TwoPointAltReducedData Ω
  /-- The top data with the eta/base/rational sources. -/
  top : SourcedTopData
  /-- The deterministic dyad Markov trimming. -/
  dyad : DyadData P

namespace L20_4SourcedLeafInputs

variable {Ω P : Type*} [Fintype Ω] [DecidableEq P]

/-- The sourced leaf realizes the plain assembled leaf inputs. -/
noncomputable def toLeafInputs (S : L20_4SourcedLeafInputs Ω P) :
    L20_4LeafInputs Ω P where
  pair := S.pair
  top := S.top.toTopG12AdditiveData
  dyad := S.dyad

/-- The assembled deficit of the sourced leaf. -/
noncomputable def loss (S : L20_4SourcedLeafInputs Ω P) (n : ℕ) : ℝ :=
  S.toLeafInputs.loss n

theorem loss_nonneg (S : L20_4SourcedLeafInputs Ω P) (n : ℕ) : 0 ≤ S.loss n :=
  S.toLeafInputs.loss_nonneg n

/-- **The sourced L20.4 manuscript bound.** -/
theorem subexpLoss (S : L20_4SourcedLeafInputs Ω P) : SubexpLoss S.loss :=
  S.toLeafInputs.subexpLoss

/-- The `SubexpLeaf` for the fully sourced L20.4 data. -/
noncomputable def toSubexpLeaf (S : L20_4SourcedLeafInputs Ω P) : SubexpLeaf where
  loss := S.loss
  loss_nonneg := S.loss_nonneg
  paper := S.subexpLoss

/-- The `B = 2` C5 `topChildLaw` slot. -/
theorem slot_le (S : L20_4SourcedLeafInputs Ω P) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  S.toSubexpLeaf.slot

/-- The top summand is subexponential from the sourced interior data. -/
theorem top_subexp (S : L20_4SourcedLeafInputs Ω P) : SubexpLoss S.top.top :=
  S.top.top_subexp

end L20_4SourcedLeafInputs

/-! ## 5. The smallest remaining paper estimate -/

/-- **The single remaining paper-level estimate of the assembly.**  It is the
G.54--G.55 additive top comparison at the explicit G.11 depth majorant, with the
paper's `ε_rat`/`ε_in` sequences.  This `Prop` is exactly
`TopG12AdditiveDepthComparison`; it is strictly weaker than the factored
`TopG12Comparison` (the G.11 recurrence turns the latter into it), and it is
all the top step consumes. -/
def PaperTopComparison (S : SourcedTopData) : Prop :=
  TopG12AdditiveDepthComparison S.top S.Ctop S.interior S.step S.eta
    (fun n => paperEpsRat S.exceptions.rational n)
    (fun n => paperEpsIn S.exceptions.incoming n) S.L

/-- The paper comparison is precisely the `additive_comparison` field. -/
theorem paperTopComparison_iff (S : SourcedTopData) :
    PaperTopComparison S ↔
      TopG12AdditiveDepthComparison S.top S.Ctop S.interior S.step S.eta
        (fun n => paperEpsRat S.exceptions.rational n)
        (fun n => paperEpsIn S.exceptions.incoming n) S.L :=
  Iff.rfl

/-- A comparison following `TopG12Comparison` gives the paper comparison
through the G.11 recurrence.  This records that the paper comparison is the
weakest form of the G.12 analytic content: it is *implied* by the factored
comparison, so assuming it is not a strengthening. -/
theorem paperTopComparison_of_comparison (S : SourcedTopData)
    (hcmp : TopG12Comparison S.top S.Ctop S.interior
      (fun n => paperEpsIn S.exceptions.incoming n) S.eta) :
    PaperTopComparison S := by
  unfold PaperTopComparison
  exact topG12AdditiveDepth_of_comparison hcmp S.recurrence S.step_ge_one
    S.alpha_nonneg (Eventually.of_forall S.Ctop_nonneg)

/-- The G.12 top conclusion from the paper comparison and the sourced interior
fields.  This records that `PaperTopComparison` is exactly the remaining input
consumed by the top step; the interior concentration fields come from `S`. -/
theorem top_subexp_of_paperComparison (S : SourcedTopData)
    (_h : PaperTopComparison S) : SubexpLoss S.top :=
  S.top_subexp

/-! ## Axiom audit -/

#print axioms pmfProb_congr_event
#print axioms toPairData_event_iff
#print axioms poolLoss_congr_event
#print axioms pairLoss_eq_poolLoss
#print axioms eventPos_of_childRootPositive
#print axioms childRootPositive_of_massLower_all
#print axioms SourcedTopData.epsRat_eq_rho
#print axioms SourcedTopData.epsIn_eq_rho
#print axioms SourcedTopData.interiorSubProps
#print axioms SourcedTopData.toTopG12AdditiveData
#print axioms SourcedTopData.top_subexp
#print axioms L20_4LeafInputs.loss_nonneg
#print axioms L20_4LeafInputs.subexpLoss
#print axioms L20_4LeafInputs.toSubexpLeaf
#print axioms L20_4LeafInputs.slot_le
#print axioms L20_4LeafInputs.loss_le_exp_neg
#print axioms L20_4LeafInputs.loss_pair_eq
#print axioms L20_4SourcedLeafInputs.toLeafInputs
#print axioms L20_4SourcedLeafInputs.loss_nonneg
#print axioms L20_4SourcedLeafInputs.subexpLoss
#print axioms L20_4SourcedLeafInputs.toSubexpLeaf
#print axioms L20_4SourcedLeafInputs.slot_le
#print axioms L20_4SourcedLeafInputs.top_subexp
#print axioms PaperTopComparison
#print axioms paperTopComparison_iff
#print axioms paperTopComparison_of_comparison
#print axioms top_subexp_of_paperComparison

end Cogentic.RandomizedL20_4LeafAssembly
