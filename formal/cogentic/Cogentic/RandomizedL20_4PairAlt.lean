import Cogentic.RandomizedL20_4Incoming
import Cogentic.RandomizedL20_4TwoPoint
import Cogentic.RandomizedL20_4ChildLower

/-!
# L20.4 pair-alt: the corrected co-large pair event

`Cogentic.RandomizedL20_4EventMass` bundled the pair event as the conjunction
`g ∧ R_{q,s}` and tried to bound its complement through the incoming failure
mass `Pr(g ∧ ¬R_{q,s}) ≤ D^{-cIn}`.  `Cogentic.RandomizedL20_4Incoming` shows
that this is impossible in the paper regime: when `4 ≤ q n` eventually, the
Gaussian root-residue upper bound gives `Pr(R_{q,s}) ≤ 3/(2q)`, so the
conjunction is a `1/q`-event and its complement is co-large.

This file uses the *other* mass split that is actually supplied by the paper.

## The corrected event

The paper supplies the lower child-root mass

`Pr(R_{q,s}) ≥ D^{-cR}`

(isolated as `RandomizedL20_4ChildLower.ChildRootMassLower`; the Gaussian
residue-class lower bound is one route to it), together with the rational-good
complement `Pr(¬g) ≤ D^{-cG}`.  The event that these two control is the
**disjunction**

`E n = g n ∨ R_{q,s} n`.

It has the two properties needed by the conditioned-moment reductions:

* `Pr(E) ≥ Pr(R_{q,s}) ≥ D^{-cR}` (`eventMassLower_pairEventAlt_of_childRootMassLower`);
* `Pr(¬E) = Pr(¬g ∧ ¬R_{q,s}) ≤ Pr(¬g) ≤ D^{-cG}`
  (`complementMassUpper_pairEventAlt_of_good`).

Both bounds are proved from the explicit lower child-root law and the
rational-good complement.  No incoming failure mass and no zero mass is used:
`event_pos` remains an explicit positivity field.

## Rebuilt bundles

`PairAltConditionedData` is the direct disjunction-event analogue of
`PairConditionedData`; `TwoPointAltReducedData` is the analogue of
`TwoPointReducedData` with `ChildRootMassLower` in place of the false incoming
complement.  Both expose `EventMassLower` and `ComplementMassUpper` for the new
event and convert to the existing `PairData`/`ChildRootPairInputs` chain, so the
pool miss estimate `pairLoss_subexp` is inherited rather than assumed.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero mass.
-/

namespace Cogentic.RandomizedL20_4PairAlt

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4TwoPoint
open Cogentic.RandomizedL20_4ChildLower

/-! ## 1. The corrected event and the paper's lower child-root mass -/

/-- The corrected pair event: rational-good environments *or* the prescribed
child root.  Its complement is the small event `¬g ∧ ¬R_{q,s}`, and its mass is
at least the paper's child-root mass. -/
def pairEventAlt {Ω : Type*} (good childRoot : ℕ → Ω → Prop) (n : ℕ) (ω : Ω) : Prop :=
  good n ω ∨ childRoot n ω

/-! ## 2. The two mass bounds for the disjunction event -/

/-- **The disjunction event has the child-root lower mass.**  Since
`R_{q,s} ⊆ g ∨ R_{q,s}`, monotonicity of the probability gives
`Pr(g ∨ R) ≥ Pr(R) ≥ D^{-cR}`. -/
theorem eventMassLower_pairEventAlt_of_childRootMassLower {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ}
    (h : ChildRootMassLower μ childRoot c) :
    EventMassLower μ (fun n => pairEventAlt good childRoot n) c := by
  unfold ChildRootMassLower EventMassLower at *
  filter_upwards [h] with n hn
  exact hn.trans (pmfProb_mono (μ n) fun ω hω => Or.inr hω)

/-- **The complement of the disjunction event is controlled by the
rational-good complement.**  Exactly,
`¬(g ∨ R) = ¬g ∧ ¬R ⊆ ¬g`, hence its mass is at most `D^{-cG}`. -/
theorem complementMassUpper_pairEventAlt_of_good {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ}
    (h : ComplementMassUpper μ good c) :
    ComplementMassUpper μ (fun n => pairEventAlt good childRoot n) c := by
  unfold ComplementMassUpper at *
  filter_upwards [h] with n hn
  refine (pmfProb_mono (μ n) ?_).trans hn
  intro ω hω
  exact (not_or.mp hω).1

/-- Exponent monotonicity for complement masses: a bound at `c₁` gives a bound
at every smaller exponent `c₂`, because `scale n ≥ 0` eventually. -/
theorem complementMassUpper_mono {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) {c₁ c₂ : ℝ} (hc : c₂ ≤ c₁)
    (h : ComplementMassUpper μ E c₁) :
    ComplementMassUpper μ E c₂ := by
  unfold ComplementMassUpper at *
  filter_upwards [h, scale_grows.eventually_ge_atTop 0] with n hn hH
  exact hn.trans (Real.exp_le_exp.mpr (by nlinarith))

/-- The disjunction-event complement at any exponent below the rational-good
exponent. -/
theorem complementMassUpper_pairEventAlt_of_good_le {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {cG cB : ℝ}
    (h : ComplementMassUpper μ good cG) (hc : cB ≤ cG) :
    ComplementMassUpper μ (fun n => pairEventAlt good childRoot n) cB :=
  complementMassUpper_mono μ _ hc
    (complementMassUpper_pairEventAlt_of_good μ good childRoot h)

/-- The two mass bounds for the corrected event, packaged together. -/
theorem pairEventAlt_mass_bounds {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {cR cG : ℝ}
    (hR : ChildRootMassLower μ childRoot cR)
    (hG : ComplementMassUpper μ good cG) :
    EventMassLower μ (fun n => pairEventAlt good childRoot n) cR ∧
      ComplementMassUpper μ (fun n => pairEventAlt good childRoot n) cG :=
  ⟨eventMassLower_pairEventAlt_of_childRootMassLower μ good childRoot hR,
    complementMassUpper_pairEventAlt_of_good μ good childRoot hG⟩

/-- **The corrected mass bounds from the Gaussian lower law.**  This is the
concrete route from the paper's Gaussian residue-class lower estimate and the
rational-good complement to both mass bounds for `g ∨ R_{q,s}`.  It is available
in the large-modulus regime where `IncomingRootComplement` is false. -/
theorem pairEventAlt_mass_bounds_of_gaussianRoot {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ} {cR cG : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (hgood : ComplementMassUpper μ good cG) :
    EventMassLower μ (fun n => pairEventAlt good childRoot n) cR ∧
      ComplementMassUpper μ (fun n => pairEventAlt good childRoot n) cG :=
  pairEventAlt_mass_bounds μ good childRoot
    (childRootMassLower_of_gaussianRoot μ childRoot hres hmod) hgood

/-- Pointwise description of the complement of the corrected event: it is the
intersection of the two failure events `¬g ∧ ¬R_{q,s}`. -/
theorem not_pairEventAlt_iff {Ω : Type*} (good childRoot : ℕ → Ω → Prop)
    (n : ℕ) (ω : Ω) :
    ¬ pairEventAlt good childRoot n ω ↔ ¬ good n ω ∧ ¬ childRoot n ω := by
  simp only [pairEventAlt, not_or]

/-- The complement of the corrected event is contained in the rational-bad
event.  This is the pointwise form of the complement bound. -/
theorem not_pairEventAlt_imp_not_good {Ω : Type*} (good childRoot : ℕ → Ω → Prop)
    (n : ℕ) (ω : Ω) :
    ¬ pairEventAlt good childRoot n ω → ¬ good n ω :=
  fun hω => (not_or.mp hω).1

/-! ## 3. Repackaging as an event of the existing `pairEvent` shape

The parent chain (`PairConditionedData`, `PairData`, `ChildRootPairInputs`)
always writes its event as `pairEvent good childRoot = good ∧ childRoot`.  An
arbitrary event `E` of the corrected form can be presented in that shape by
taking `good := E` and `childRoot := True`; the conjunction is then
propositionally `E`.  The following small lemmas make that repackaging
transparent. -/

theorem pairEvent_true_eq {Ω : Type*} (E : ℕ → Ω → Prop) (n : ℕ) :
    (fun ω => pairEvent E (fun _ _ => True) n ω) = E n := by
  funext ω
  simp [pairEvent]

theorem eventMassLower_pairEvent_true {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) {c : ℝ}
    (h : EventMassLower μ E c) :
    EventMassLower μ (fun n => pairEvent E (fun _ _ => True) n) c := by
  unfold EventMassLower at *
  filter_upwards [h] with n hn
  simpa [pairEvent_true_eq E n] using hn

theorem complementMassUpper_pairEvent_true {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) {c : ℝ}
    (h : ComplementMassUpper μ E c) :
    ComplementMassUpper μ (fun n => pairEvent E (fun _ _ => True) n) c := by
  unfold ComplementMassUpper at *
  filter_upwards [h] with n hn
  simpa [pairEvent_true_eq E n] using hn

theorem offEventHeightUpper_pairEvent_true {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) {c : ℝ}
    (h : OffEventHeightUpper μ E Z c) :
    OffEventHeightUpper μ (fun n => pairEvent E (fun _ _ => True) n) Z c := by
  unfold OffEventHeightUpper at *
  filter_upwards [h] with n hn ω hω
  exact hn ω (fun hE => hω ⟨hE, trivial⟩)

theorem eventPos_pairEvent_true {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop)
    (h : ∀ n, 0 < pmfProb (μ n) (E n)) :
    ∀ n, 0 < pmfProb (μ n) (pairEvent E (fun _ _ => True) n) := by
  intro n
  simpa [pairEvent_true_eq E n] using h n

/-! ## 4. The corrected conditioned bundle -/

/-- The disjunction-event analogue of `PairConditionedData`.  Every event-facing
field refers to `pairEventAlt`, and the complement exponent is supplied by the
rational-good complement rather than by an incoming failure mass. -/
structure PairAltConditionedData (Ω : Type*) [Fintype Ω] where
  /-- The field/trial law. -/
  μ : ℕ → PMF Ω
  /-- Rational-good environments. -/
  good : ℕ → Ω → Prop
  /-- The prescribed child root event `R_{q,s}`. -/
  childRoot : ℕ → Ω → Prop
  /-- The normalized top height `H^det_{0,J}/B₁(q)`. -/
  Z : ℕ → Ω → ℝ
  /-- The fixed Paley--Zygmund mean constant. -/
  a : ℝ
  a_pos : 0 < a
  /-- The ordinary first-moment constant. -/
  a₀ : ℝ
  a₀_pos : 0 < a₀
  /-- The target conditioned mean is at most half the ordinary mean. -/
  a_le : a ≤ a₀ / 2
  /-- Exponent of the ordinary second moment. -/
  cU : ℝ
  cU_nonneg : 0 ≤ cU
  /-- Exponent of the corrected-event mass lower bound. -/
  cE : ℝ
  cE_nonneg : 0 ≤ cE
  /-- Exponent of the off-event height cut. -/
  cV : ℝ
  /-- Exponent of the complement mass upper bound. -/
  cB : ℝ
  /-- The complement decays faster than the height grows. -/
  cV_lt_cB : cV < cB
  /-- Exponent of the dyad cardinality. -/
  cDyad : ℝ
  cDyad_nonneg : 0 ≤ cDyad
  dyadCard : ℕ → ℕ
  dyadCard_le : ∀ᶠ n : ℕ in atTop,
    (dyadCard n : ℝ) ≤ Real.exp (cDyad * scale n)
  poolSize : ℕ → ℕ
  poolSize_ge : ∀ᶠ n : ℕ in atTop,
    Real.exp ((cU + cE + cDyad + 2) * scale n) ≤ (poolSize n : ℝ)
  /-- The corrected event has positive mass at every scale. -/
  event_pos : ∀ n, 0 < pmfProb (μ n) (pairEventAlt good childRoot n)
  /-- The ordinary (unconditioned) second moment. -/
  uncond_two_point : UnconditionedTwoPoint μ Z cU
  /-- The corrected-event mass lower bound. -/
  event_mass_lower : EventMassLower μ (fun n => pairEventAlt good childRoot n) cE
  /-- The ordinary one-point lower bound. -/
  uncond_mean_lower : UnconditionedMeanLower μ Z a₀
  /-- The off-event height cut. -/
  off_event_height : OffEventHeightUpper μ (fun n => pairEventAlt good childRoot n) Z cV
  /-- The corrected-event complement mass upper bound. -/
  complement_mass_upper : ComplementMassUpper μ (fun n => pairEventAlt good childRoot n) cB

namespace PairAltConditionedData

variable {Ω : Type*} [Fintype Ω]

/-- The conditioned two-point bound derived from the ordinary bound and the
explicit conditioning loss `cE`. -/
theorem twoPoint (S : PairAltConditionedData Ω) :
    ConditionedTwoPoint S.μ (fun n => pairEventAlt S.good S.childRoot n) S.Z
      (S.cU + S.cE) :=
  conditionedTwoPoint_of_unconditioned S.μ _ S.Z S.uncond_two_point S.event_mass_lower

/-- The conditioned mean lower bound derived from the ordinary one-point bound,
the off-event height cut and the explicit event/complement masses. -/
theorem meanLower (S : PairAltConditionedData Ω) :
    ConditionedMeanLower S.μ (fun n => pairEventAlt S.good S.childRoot n) S.Z S.a :=
  conditionedMeanLower_of_unconditioned S.μ _ S.Z S.a₀_pos S.a_le S.cV_lt_cB
    S.event_mass_lower S.complement_mass_upper S.off_event_height S.uncond_mean_lower

/-- **Repackaging into the existing `PairConditionedData`.**  The event is
presented as `good := pairEventAlt …`, `childRoot := True`; all event-facing
fields are transported by the `pairEvent_true` lemmas. -/
noncomputable def toPairConditionedData (S : PairAltConditionedData Ω) :
    Cogentic.RandomizedL20_4Conditioned.PairConditionedData Ω where
  μ := S.μ
  good := fun n ω => pairEventAlt S.good S.childRoot n ω
  childRoot := fun _ _ => True
  Z := S.Z
  a := S.a
  a_pos := S.a_pos
  a₀ := S.a₀
  a₀_pos := S.a₀_pos
  a_le := S.a_le
  cU := S.cU
  cU_nonneg := S.cU_nonneg
  cE := S.cE
  cE_nonneg := S.cE_nonneg
  cV := S.cV
  cB := S.cB
  cV_lt_cB := S.cV_lt_cB
  cDyad := S.cDyad
  cDyad_nonneg := S.cDyad_nonneg
  dyadCard := S.dyadCard
  dyadCard_le := S.dyadCard_le
  poolSize := S.poolSize
  poolSize_ge := S.poolSize_ge
  event_pos := eventPos_pairEvent_true S.μ _ S.event_pos
  uncond_two_point := S.uncond_two_point
  event_mass_lower := eventMassLower_pairEvent_true S.μ _ S.event_mass_lower
  uncond_mean_lower := S.uncond_mean_lower
  off_event_height := offEventHeightUpper_pairEvent_true S.μ _ S.Z S.off_event_height
  complement_mass_upper := complementMassUpper_pairEvent_true S.μ _ S.complement_mass_upper

/-- The corrected bundle realizes the existing `PairData` and therefore inherits
the pool miss estimate. -/
noncomputable def toPairData (S : PairAltConditionedData Ω) : PairData Ω :=
  S.toPairConditionedData.toPairData

theorem pairLoss_subexp (S : PairAltConditionedData Ω) :
    SubexpLoss S.toPairData.loss :=
  S.toPairData.loss_subexp

end PairAltConditionedData

/-! ## 5. The corrected two-point reduced bundle -/

/-- The disjunction-event analogue of `TwoPointReducedData`.  The false incoming
complement is replaced by the paper's lower child-root mass
`ChildRootMassLower`; the pair complement is *derived* from the rational-good
complement, not assumed.  The remaining one-point/height fields are unchanged.
-/
structure TwoPointAltReducedData (Ω : Type*) [Fintype Ω] where
  /-- The field/trial law. -/
  μ : ℕ → PMF Ω
  /-- Rational-good environments. -/
  good : ℕ → Ω → Prop
  /-- The prescribed child root event `R_{q,s}`. -/
  childRoot : ℕ → Ω → Prop
  /-- The normalized top height `H^det_{0,J}/B₁(q)`. -/
  Z : ℕ → Ω → ℝ
  /-- The fixed Paley--Zygmund mean constant. -/
  a : ℝ
  a_pos : 0 < a
  /-- The ordinary first-moment lower constant. -/
  a₀ : ℝ
  a₀_pos : 0 < a₀
  /-- The target conditioned mean is at most half the ordinary mean. -/
  a_le : a ≤ a₀ / 2
  /-- Exponent of the ordinary first-moment upper bound. -/
  cM : ℝ
  cM_nonneg : 0 ≤ cM
  /-- Exponent of the pointwise height cut. -/
  cV : ℝ
  cV_nonneg : 0 ≤ cV
  /-- Exponent of the corrected-event complement mass. -/
  cB : ℝ
  /-- The complement decays faster than the height grows. -/
  cV_lt_cB : cV < cB
  /-- Exponent of the child-root mass lower bound. -/
  cR : ℝ
  cR_nonneg : 0 ≤ cR
  /-- Exponent of the rational-good complement. -/
  cG : ℝ
  /-- The derived complement exponent is at most the rational-good exponent. -/
  cB_le_cG : cB ≤ cG
  /-- The ordinary one-point upper bound. -/
  mean_upper : UnconditionedMeanUpper μ Z cM
  /-- The deterministic pointwise height cut. -/
  height_upper : NormalizedHeightUpper Z cV
  /-- Positivity of the normalized height. -/
  Z_nonneg : NormalizedHeightNonneg Z
  /-- The paper's actual lower child-root mass. -/
  child_root_mass_lower : ChildRootMassLower μ childRoot cR
  /-- The rational-good complement is `D^{-cG}`. -/
  good_complement : ComplementMassUpper μ good cG
  /-- The ordinary one-point lower bound. -/
  mean_lower : UnconditionedMeanLower μ Z a₀
  /-- Exponent of the dyad cardinality. -/
  cDyad : ℝ
  cDyad_nonneg : 0 ≤ cDyad
  dyadCard : ℕ → ℕ
  dyadCard_le : ∀ᶠ n : ℕ in atTop,
    (dyadCard n : ℝ) ≤ Real.exp (cDyad * scale n)
  poolSize : ℕ → ℕ
  /-- The pool is large relative to the derived exponent
  `cM + cV + cR`. -/
  poolSize_ge : ∀ᶠ n : ℕ in atTop,
    Real.exp ((cM + cV + cR + cDyad + 2) * scale n) ≤ (poolSize n : ℝ)
  /-- The corrected event has positive mass at every scale. -/
  event_pos : ∀ n, 0 < pmfProb (μ n) (pairEventAlt good childRoot n)

namespace TwoPointAltReducedData

variable {Ω : Type*} [Fintype Ω]

/-- The reduced unconditioned second-moment bound.  Its exponent is `cM + cV`,
the sum of the one-point and height-cut exponents. -/
theorem uncondTwoPoint (S : TwoPointAltReducedData Ω) :
    UnconditionedTwoPoint S.μ S.Z (S.cM + S.cV) :=
  unconditionedTwoPoint_of_meanUpper_height S.μ S.Z S.mean_upper S.Z_nonneg
    S.height_upper

/-- The corrected pair event has mass at least `D^{-cR}`, directly from the
paper's lower child-root mass. -/
theorem eventMassLower (S : TwoPointAltReducedData Ω) :
    EventMassLower S.μ (fun n => pairEventAlt S.good S.childRoot n) S.cR :=
  eventMassLower_pairEventAlt_of_childRootMassLower S.μ S.good S.childRoot
    S.child_root_mass_lower

/-- The corrected pair-complement bound, derived from the rational-good
complement at exponent `cG` and monotonicity to `cB`. -/
theorem complementMassUpper (S : TwoPointAltReducedData Ω) :
    ComplementMassUpper S.μ (fun n => pairEventAlt S.good S.childRoot n) S.cB :=
  complementMassUpper_pairEventAlt_of_good_le S.μ S.good S.childRoot
    S.good_complement S.cB_le_cG

/-- **The corrected reduction to `PairAltConditionedData`.**  The event-mass and
complement fields are derived from `ChildRootMassLower` and `good_complement`;
the two-point exponent becomes `cM + cV` and the event exponent is `cR`. -/
noncomputable def toPairAltConditionedData (S : TwoPointAltReducedData Ω) :
    PairAltConditionedData Ω where
  μ := S.μ
  good := S.good
  childRoot := S.childRoot
  Z := S.Z
  a := S.a
  a_pos := S.a_pos
  a₀ := S.a₀
  a₀_pos := S.a₀_pos
  a_le := S.a_le
  cU := S.cM + S.cV
  cU_nonneg := add_nonneg S.cM_nonneg S.cV_nonneg
  cE := S.cR
  cE_nonneg := S.cR_nonneg
  cV := S.cV
  cB := S.cB
  cV_lt_cB := S.cV_lt_cB
  cDyad := S.cDyad
  cDyad_nonneg := S.cDyad_nonneg
  dyadCard := S.dyadCard
  dyadCard_le := S.dyadCard_le
  poolSize := S.poolSize
  poolSize_ge := by
    simpa [add_assoc, add_left_comm, add_comm] using S.poolSize_ge
  event_pos := S.event_pos
  uncond_two_point := S.uncondTwoPoint
  event_mass_lower := S.eventMassLower
  uncond_mean_lower := S.mean_lower
  off_event_height := offEventHeightUpper_of_heightUpper S.μ _ S.Z S.height_upper
  complement_mass_upper := S.complementMassUpper

/-- The corrected reduced bundle realizes the existing `PairConditionedData`
through the repackaging of Section 3. -/
noncomputable def toPairConditionedData (S : TwoPointAltReducedData Ω) :
    Cogentic.RandomizedL20_4Conditioned.PairConditionedData Ω :=
  S.toPairAltConditionedData.toPairConditionedData

/-- The resulting `PairData` is the parent realization, so the corrected bundle
composes with the existing chain. -/
noncomputable def toPairData (S : TwoPointAltReducedData Ω) : PairData Ω :=
  S.toPairConditionedData.toPairData

/-- **The pool loss of the corrected data is `SubexpLoss`.**  This is the
existing `PairData.loss_subexp` applied after the reduction; it confirms that the
corrected event and its two derived mass bounds really produce the pool miss
estimate. -/
theorem pairLoss_subexp (S : TwoPointAltReducedData Ω) :
    SubexpLoss S.toPairData.loss :=
  S.toPairData.loss_subexp

end TwoPointAltReducedData

/-! ## 6. Corrected-name aliases

These aliases let consumers refer to the disjunction-event bundles by the names
of the structures they replace.  The originals remain untouched. -/

/-- Corrected replacement for `RandomizedL20_4TwoPoint.TwoPointReducedData`. -/
abbrev TwoPointReducedData (Ω : Type*) [Fintype Ω] := TwoPointAltReducedData Ω

/-- Corrected replacement for `RandomizedL20_4Conditioned.PairConditionedData`. -/
abbrev PairConditionedData (Ω : Type*) [Fintype Ω] := PairAltConditionedData Ω

/-! ## Axiom audit -/

#print axioms childRootMassLower_of_gaussianRoot
#print axioms eventMassLower_pairEventAlt_of_childRootMassLower
#print axioms complementMassUpper_pairEventAlt_of_good
#print axioms complementMassUpper_mono
#print axioms complementMassUpper_pairEventAlt_of_good_le
#print axioms pairEventAlt_mass_bounds
#print axioms pairEventAlt_mass_bounds_of_gaussianRoot
#print axioms not_pairEventAlt_iff
#print axioms eventMassLower_pairEvent_true
#print axioms complementMassUpper_pairEvent_true
#print axioms offEventHeightUpper_pairEvent_true
#print axioms eventPos_pairEvent_true
#print axioms PairAltConditionedData.twoPoint
#print axioms PairAltConditionedData.meanLower
#print axioms PairAltConditionedData.toPairConditionedData
#print axioms PairAltConditionedData.toPairData
#print axioms PairAltConditionedData.pairLoss_subexp
#print axioms TwoPointAltReducedData.uncondTwoPoint
#print axioms TwoPointAltReducedData.eventMassLower
#print axioms TwoPointAltReducedData.complementMassUpper
#print axioms TwoPointAltReducedData.toPairAltConditionedData
#print axioms TwoPointAltReducedData.toPairConditionedData
#print axioms TwoPointAltReducedData.toPairData
#print axioms TwoPointAltReducedData.pairLoss_subexp

end Cogentic.RandomizedL20_4PairAlt
