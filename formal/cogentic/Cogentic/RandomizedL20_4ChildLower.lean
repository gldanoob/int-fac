import Cogentic.RandomizedL20_4Incoming

/-!
# L20.4 child lower: the G.8/G.10 child-root lower law

`Cogentic.RandomizedL20_4Incoming` showed that the Gaussian root-residue
estimate

`(1 - q/σ)/q ≤ Pr(R_{q,s}) ≤ (1 + q/σ)/q`

supplies an *upper* bound on the prescribed child-root event `R_{q,s}`.  Hence
its complement is co-large, and the co-large failure input

`IncomingRootComplement μ good childRoot cIn`,  i.e.

`Pr(g ∧ ¬R_{q,s}) ≤ D^{-cIn}`,

is false whenever `4 ≤ q` eventually
(`not_incomingRootComplement_of_four_le_modulus`).  The paper does not need that
false co-large statement: it needs a *lower* bound on the child-root event, the
G.8 one-point density comparison together with the G.10 concentration lower
half.

## What is done here

1. **The child lower law.**  `ChildRootMassLower μ childRoot cR` is defined as
   the single explicit mass inequality

   `D^{-cR} ≤ Pr(R_{q,s})` eventually

   (`childRootMassLower_iff_explicitMass`).  It is definitionally the existing
   `EventMassLower`, so no auxiliary event, bad set, or zero mass is introduced.

2. **The Gaussian estimate proves it.**  The lower half of the residue-class
   interval, `(1 - q/σ)/q ≥ 1/(2q)`, together with `2q ≤ D^{cR}`, gives
   `ChildRootMassLower` (`childRootMassLower_of_gaussianRoot`).  In particular
   it holds in the very regime `4 ≤ q` where the incoming complement fails
   (`childRootMassLower_consistent_of_four_le_modulus`,
   `childRootMassLower_and_not_incomingRootComplement_of_four_le_modulus`).

3. **The pair-event mass follows from it.**  With the rational-good complement
   `Pr(¬g) ≤ D^{-cG}` and `cR < cG`, the pair event `g ∧ R_{q,s}` has mass at
   least `D^{-(cR+1)}`
   (`eventMassLower_pairEvent_of_childRootMassLower`).  This uses the lower law
   directly and never mentions `IncomingRootComplement`.

4. **The replacement at the mass level.**  `ChildRootLowerMassData` is the
   smallest replacement bundle: it keeps the child lower law and the
   rational-good complement, and for the *upper* side it keeps the direct
   pair-complement bound.  The split of the pair complement into
   `Pr(¬g) + Pr(g ∧ ¬R)` is not used, precisely because a lower bound on `R`
   cannot bound `Pr(g ∧ ¬R)` from above.  The bundle derives both pair-event
   masses (`ChildRootLowerMassData.pairEvent_mass_bounds`).

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-mass: the child lower
exponent `cR` and every absorption constant are explicit.
-/

namespace Cogentic.RandomizedL20_4ChildLower

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned
open Cogentic.RandomizedL20_4TwoPoint
open Cogentic.RandomizedL20_4Mean
open Cogentic.RandomizedL20_4EventMass
open Cogentic.RandomizedL20_4Incoming

/-! ## 1. The smallest explicit child-root lower law -/

/-- **The G.8/G.10 child-root lower law.**  The prescribed child-root event
`R_{q,s}` carries mass at least `D^{-cR}` eventually:

`Pr(R_{q,s}) ≥ exp (-cR * scale n)`.

This is the lower estimate the paper actually uses, and it is exactly the
existing `EventMassLower` predicate: no bad event, no complement, and no
auxiliary structure is added.  The exponent `cR` is the `q`-loss of the child
root. -/
def ChildRootMassLower {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (childRoot : ℕ → Ω → Prop) (cR : ℝ) : Prop :=
  EventMassLower μ childRoot cR

/-- The lower law written in its primitive mass form.  This is an `Iff.rfl`
because `ChildRootMassLower` is *defined* to be that inequality. -/
theorem childRootMassLower_iff_explicitMass {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (childRoot : ℕ → Ω → Prop) (cR : ℝ) :
    ChildRootMassLower μ childRoot cR ↔
      ∀ᶠ n : ℕ in atTop,
        Real.exp (-cR * scale n) ≤ pmfProb (μ n) (childRoot n) :=
  Iff.rfl

/-- The lower law is definitionally the existing `EventMassLower`.  This records
that the new name introduces no mathematical content beyond the explicit mass
bound. -/
theorem childRootMassLower_iff_eventMassLower {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (childRoot : ℕ → Ω → Prop) (cR : ℝ) :
    ChildRootMassLower μ childRoot cR ↔ EventMassLower μ childRoot cR :=
  Iff.rfl

/-- Eliminate the child lower law to a mass lower bound. -/
theorem eventMassLower_of_childRootMassLower {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (childRoot : ℕ → Ω → Prop) {cR : ℝ}
    (h : ChildRootMassLower μ childRoot cR) :
    EventMassLower μ childRoot cR :=
  h

/-- Introduce the child lower law from a mass lower bound. -/
theorem childRootMassLower_of_eventMassLower {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (childRoot : ℕ → Ω → Prop) {cR : ℝ}
    (h : EventMassLower μ childRoot cR) :
    ChildRootMassLower μ childRoot cR :=
  h

/-- Exponent monotonicity: a lower bound at the smaller exponent `c₁` gives one
at every larger exponent `c₂`, since `exp (-c₂ * scale) ≤ exp (-c₁ * scale)` for
large `n`.  Thus `cR` may be taken as the smallest exponent for which the
G.8/G.10 estimate is available: the estimate gets weaker as the exponent grows. -/
theorem childRootMassLower_mono {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (childRoot : ℕ → Ω → Prop) {c₁ c₂ : ℝ}
    (hc : c₁ ≤ c₂) (h : ChildRootMassLower μ childRoot c₁) :
    ChildRootMassLower μ childRoot c₂ := by
  unfold ChildRootMassLower EventMassLower at *
  filter_upwards [h, scale_grows.eventually_ge_atTop 0] with n hn hH
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans hn

/-! ## 2. The Gaussian estimate proves the child lower law -/

/-- **The child lower law from the Gaussian residue-class interval.**  The lower
half of `gaussian_residue_class_prob_interval` is at least `1/(2q)` when
`2q ≤ σ`, and `2q ≤ D^{cR}` turns this into `D^{-cR}`.  This is the explicit
G.8/G.10 lower estimate used by the paper. -/
theorem childRootMassLower_of_gaussianRoot {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ} {cR : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR) :
    ChildRootMassLower μ childRoot cR :=
  eventMassLower_of_gaussianRoot μ childRoot hres hmod

/-- **The child lower law survives the obstruction.**  Under the Gaussian
root-residue identification and the modulus bounds, `ChildRootMassLower` holds
in the regime `4 ≤ q n` eventually.  The hypothesis `hq4` is retained to make
the regime explicit; the lower law does not need it. -/
theorem childRootMassLower_consistent_of_four_le_modulus {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ} {cR : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (_hq4 : ∀ᶠ n : ℕ in atTop, 4 ≤ q n) :
    ChildRootMassLower μ childRoot cR :=
  childRootMassLower_of_gaussianRoot μ childRoot hres hmod

/-! ## 3. The pair-event lower mass from the child lower law -/

/-- **The pair event has mass at least `D^{-(cR+1)}`.**  From
`Pr(R_{q,s}) ≥ D^{-cR}` and `Pr(¬g) ≤ D^{-cG}` with `cR < cG`, the elementary
subadditivity `Pr(g ∧ R) ≥ Pr(R) - Pr(¬g)` gives the bound.  The `+1` absorbs
the eventual difference `1 - D^{-(cG-cR)} ≥ D^{-1}`.

This is the pair-event lower mass the paper needs, and it is proved from the
*lower* child law only. -/
theorem eventMassLower_pairEvent_of_childRootMassLower {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {cR cG : ℝ}
    (hRG : cR < cG)
    (hroot : ChildRootMassLower μ childRoot cR)
    (hgood : ComplementMassUpper μ good cG) :
    EventMassLower μ (fun n => pairEvent good childRoot n) (cR + 1) :=
  eventMassLower_pairEvent_of_root_complement μ good childRoot hRG
    (eventMassLower_of_childRootMassLower μ childRoot hroot) hgood

/-- The same pair-event lower mass directly from the Gaussian residue-class
estimate and the rational-good complement.  No `IncomingRootComplement` (and no
co-large child complement) appears. -/
theorem eventMassLower_pairEvent_of_gaussianRoot_childLower
    {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ} {cR cG : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (hgood : ComplementMassUpper μ good cG) (hRG : cR < cG) :
    EventMassLower μ (fun n => pairEvent good childRoot n) (cR + 1) :=
  eventMassLower_pairEvent_of_childRootMassLower μ good childRoot hRG
    (childRootMassLower_of_gaussianRoot μ childRoot hres hmod) hgood

/-- **The replacement in the problematic regime.**  Whenever `4 ≤ q n`
eventually, the Gaussian lower bound makes the child lower law true, while the
incoming-root complement is false for every positive exponent.  This is the
precise sense in which `ChildRootMassLower` replaces the false
`IncomingRootComplement`: the lower law is the available direction of the
Gaussian interval. -/
theorem childRootMassLower_and_not_incomingRootComplement_of_four_le_modulus
    {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ} {cR cG cIn : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (hgood : ComplementMassUpper μ good cG)
    (hcG : 0 < cG) (hcIn : 0 < cIn)
    (hq4 : ∀ᶠ n : ℕ in atTop, 4 ≤ q n) :
    ChildRootMassLower μ childRoot cR ∧
      ¬ IncomingRootComplement μ good childRoot cIn :=
  ⟨childRootMassLower_consistent_of_four_le_modulus μ childRoot hres hmod hq4,
    Cogentic.RandomizedL20_4Incoming.not_incomingRootComplement_of_four_le_modulus
      μ good childRoot hres hmod hgood hcG hcIn hq4⟩

/-! ## 4. The replacement bundle: child lower plus the direct pair complement -/

/-- **The smallest mass-level replacement for `PairEventMassData`.**  The lower
side is the child lower law; the rational-good complement is kept; the upper
side is the *direct* pair-complement bound.  The false incoming failure field is
gone, and no attempt is made to bound `Pr(g ∧ ¬R_{q,s})` from above by the lower
bound on `R_{q,s}`.  This is the different event split that remains valid in the
`4 ≤ q` regime. -/
structure ChildRootLowerMassData {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) (cR cG cB : ℝ) : Prop where
  /-- The G.8/G.10 lower bound on the child root. -/
  child_root_lower : ChildRootMassLower μ childRoot cR
  /-- The rational-good complement. -/
  good_complement : ComplementMassUpper μ good cG
  /-- The direct pair-complement bound. -/
  pair_complement : ComplementMassUpper μ (fun n => pairEvent good childRoot n) cB

namespace ChildRootLowerMassData

variable {Ω : Type*} [Fintype Ω]
variable {μ : ℕ → PMF Ω} {good childRoot : ℕ → Ω → Prop}
variable {cR cG cB : ℝ}

/-- The pair-event lower mass from the child lower law. -/
theorem pairEvent_eventMassLower
    (S : ChildRootLowerMassData μ good childRoot cR cG cB) (hRG : cR < cG) :
    EventMassLower μ (fun n => pairEvent good childRoot n) (cR + 1) :=
  eventMassLower_pairEvent_of_childRootMassLower μ good childRoot hRG
    S.child_root_lower S.good_complement

/-- The pair-event complement, taken directly. -/
theorem pairEvent_complementMassUpper
    (S : ChildRootLowerMassData μ good childRoot cR cG cB) :
    ComplementMassUpper μ (fun n => pairEvent good childRoot n) cB :=
  S.pair_complement

/-- **Both pair-event masses from the replacement bundle.**  The lower mass
comes from the child lower law; the upper complement is the direct pair
complement.  This is the pair-event mass statement that replaces the
incompatible incoming-root decomposition. -/
theorem pairEvent_mass_bounds
    (S : ChildRootLowerMassData μ good childRoot cR cG cB) (hRG : cR < cG) :
    EventMassLower μ (fun n => pairEvent good childRoot n) (cR + 1) ∧
      ComplementMassUpper μ (fun n => pairEvent good childRoot n) cB :=
  ⟨S.pairEvent_eventMassLower hRG, S.pairEvent_complementMassUpper⟩

/-- Equality of the lower law with the explicit mass inequality, specialized to
the bundle.  This exposes exactly what the replacement consumes. -/
theorem pairEvent_eventMassLower_of_explicit
    (S : ChildRootLowerMassData μ good childRoot cR cG cB) (hRG : cR < cG)
    (hexp : ∀ᶠ n : ℕ in atTop,
      Real.exp (-cR * scale n) ≤ pmfProb (μ n) (childRoot n)) :
    EventMassLower μ (fun n => pairEvent good childRoot n) (cR + 1) :=
  eventMassLower_pairEvent_of_childRootMassLower μ good childRoot hRG
    ((childRootMassLower_iff_explicitMass μ childRoot cR).mpr hexp)
    S.good_complement

end ChildRootLowerMassData

/-! ## Axiom audit -/

#print axioms childRootMassLower_iff_explicitMass
#print axioms childRootMassLower_iff_eventMassLower
#print axioms eventMassLower_of_childRootMassLower
#print axioms childRootMassLower_of_eventMassLower
#print axioms childRootMassLower_mono
#print axioms childRootMassLower_of_gaussianRoot
#print axioms childRootMassLower_consistent_of_four_le_modulus
#print axioms eventMassLower_pairEvent_of_childRootMassLower
#print axioms eventMassLower_pairEvent_of_gaussianRoot_childLower
#print axioms childRootMassLower_and_not_incomingRootComplement_of_four_le_modulus
#print axioms ChildRootLowerMassData.pairEvent_eventMassLower
#print axioms ChildRootLowerMassData.pairEvent_complementMassUpper
#print axioms ChildRootLowerMassData.pairEvent_mass_bounds
#print axioms ChildRootLowerMassData.pairEvent_eventMassLower_of_explicit

end Cogentic.RandomizedL20_4ChildLower
