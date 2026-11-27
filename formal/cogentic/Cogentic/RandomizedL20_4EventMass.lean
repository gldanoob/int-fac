import Cogentic.RandomizedL20_4TwoPoint
import Cogentic.RandomizedL20_4Mean

/-!
# L20.4 event mass: the pair-event lower mass and complement mass

`Cogentic.RandomizedL20_4TwoPoint` reduced the ordinary two-point input to
one-point estimates and kept the pair-event mass fields
`event_mass_lower`/`event_mass_upper` explicit.  `Cogentic.RandomizedL20_4Mean`
decomposed the complement of the pair event into its two primitive failure
masses.  This file closes the loop on the two mass fields of the pair event
`g ∧ R_{q,s}`.

## The two masses

1. **Lower mass.**  The incoming-root probability is the Gaussian residue-class
   mass of the prescribed root modulo `q`.  The existing estimate
   `Cogentic.RandomizedEllipticAndGaussian.gaussian_residue_class_prob_interval`
   gives, for `σ ≥ q`,
   `(1 - q/σ)/q ≤ Pr(a mod q)`.
   With `2q ≤ σ` this is at least `1/(2q)`, and with `2q ≤ D^{cR}` it is at
   least `D^{-cR}`.  Subtracting the rational-good failure mass `≤ D^{-cG}`
   (`cR < cG`) leaves at least `D^{-(cR+1)}` on `g ∧ R_{q,s}`:

   `eventMassLower_pairEvent_of_gaussianRoot`,
   exponent `cR + 1` (the `+1` is the explicit half-mass absorption).

2. **Upper complement.**  The complement of `g ∧ R_{q,s}` splits exactly into
   `¬g` together with `g ∧ ¬R_{q,s}`.  A union bound gives

   `Pr(¬(g ∧ R)) ≤ Pr(¬g) + Pr(g ∧ ¬R) ≤ D^{-cG} + D^{-cIn} ≤ D^{-cB}`

   whenever `cB + 1 ≤ cG` and `cB + 1 ≤ cIn`, using `2 ≤ D`:

   `complementMassUpper_pairEvent_of_components`.

## Why the incoming-root failure mass is an explicit input

`Pr(g ∧ ¬R_{q,s})` is the G.12 incoming exceptional mass `ε̄^in_{0,J}`.  It is
not a consequence of the Gaussian *lower* bound on `Pr(R_{q,s})`: that bound only
says the root event is not too small, and in fact the residue-class interval
bounds `Pr(R_{q,s})` from *above* by `(1 + q/σ)/q`, so the failure mass
`1 - Pr(R_{q,s})` is close to one.  The complement estimate is therefore a
genuine co-large-event statement, kept as the named sub-`Prop`
`IncomingRootComplement` and never replaced by zero.

## Reduction to `TwoPointReducedData`

`PairEventMassData` has exactly the fields of `TwoPointReducedData` except that
the single field `complement_mass_upper` is replaced by

* the incoming-root failure mass `IncomingRootComplement μ good childRoot cIn`,
  and
* the two explicit exponent inequalities `cB + 1 ≤ cG`, `cB + 1 ≤ cIn`.

Its `toTwoPointReducedData` derives `complement_mass_upper` from those fields
and transports every other field unchanged, so any consumer of
`TwoPointReducedData` can use this strictly finer input bundle.  The derived
pair-event lower mass and complement mass are exposed directly as
`PairEventMassData.eventMassLower` and `PairEventMassData.complementMassUpper`.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero loss: both exponents are
explicit and the component masses are retained.
-/

namespace Cogentic.RandomizedL20_4EventMass

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

/-! ## 1. The explicit incoming-root sub-`Prop` -/

/-- The incoming-root failure mass on rational-good environments: the mass of
`g ∧ ¬R_{q,s}`.  This is the G.12 incoming exceptional mass `ε̄^in_{0,J}`.  It
is the second primitive component of the pair-event complement and is *not*
implied by the Gaussian residue-class lower bound on `Pr(R_{q,s})`. -/
def IncomingRootComplement {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω) ≤
      Real.exp (-c * scale n)

/-! ## 2. The pair-event lower mass from the Gaussian root residue -/

/-- **The pair event `g ∧ R_{q,s}` has mass at least `D^{-(cR+1)}`.**  The
Gaussian residue-class estimate gives the incoming-root mass `≥ D^{-cR}`; the
rational-good complement is at most `D^{-cG}` with `cR < cG`; the difference is
at least `D^{-(cR+1)}`.  This composes
`eventMassLower_of_gaussianRoot` with
`eventMassLower_pairEvent_of_root_complement`, so the Gaussian interval and the
half-mass absorption are both retained. -/
theorem eventMassLower_pairEvent_of_gaussianRoot {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {muG sigma : ℕ → ℝ} {cR cG : ℝ}
    (hres : GaussianRootResidue μ childRoot a q muG sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (hgood : ComplementMassUpper μ good cG)
    (hRG : cR < cG) :
    EventMassLower μ (fun n => pairEvent good childRoot n) (cR + 1) :=
  eventMassLower_pairEvent_of_root_complement μ good childRoot hRG
    (eventMassLower_of_gaussianRoot μ childRoot hres hmod) hgood

/-! ## 3. The pair-event complement from the two component masses -/

/-- **The complement of the pair event is at most `D^{-cB}`.**  The exact split
`¬(g ∧ R) = ¬g ∪ (g ∧ ¬R)` together with the two component bounds
`Pr(¬g) ≤ D^{-cG}` and `Pr(g ∧ ¬R) ≤ D^{-cIn}` gives the pair complement bound
at exponent `cB` whenever `cB + 1 ≤ cG` and `cB + 1 ≤ cIn`.  The unit lost is
the explicit union-bound factor `2 ≤ D`. -/
theorem complementMassUpper_pairEvent_of_components {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {cG cIn cB : ℝ}
    (hG : ComplementMassUpper μ good cG)
    (hIn : IncomingRootComplement μ good childRoot cIn)
    (hcG : cB + 1 ≤ cG) (hcIn : cB + 1 ≤ cIn) :
    ComplementMassUpper μ (fun n => pairEvent good childRoot n) cB :=
  (complementMassUpper_pairEvent_iff_pairComplement μ good childRoot).mpr
    (pairComplementMassUpper_of_components μ good childRoot hG hIn hcG hcIn)

/-- The two pair-event mass statements together, from the Gaussian root
primitives and the two component masses.  The two exponents are `cR + 1` and
`cB`; both are explicit and neither mass is set to zero. -/
theorem pairEvent_mass_bounds {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {muG sigma : ℕ → ℝ} {cR cG cIn cB : ℝ}
    (hres : GaussianRootResidue μ childRoot a q muG sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (hgood : ComplementMassUpper μ good cG)
    (hRG : cR < cG)
    (hIn : IncomingRootComplement μ good childRoot cIn)
    (hcG : cB + 1 ≤ cG) (hcIn : cB + 1 ≤ cIn) :
    EventMassLower μ (fun n => pairEvent good childRoot n) (cR + 1) ∧
      ComplementMassUpper μ (fun n => pairEvent good childRoot n) cB :=
  ⟨eventMassLower_pairEvent_of_gaussianRoot μ good childRoot hres hmod hgood hRG,
    complementMassUpper_pairEvent_of_components μ good childRoot hgood hIn hcG hcIn⟩

/-! ## 4. The reduced input bundle and its realization of `TwoPointReducedData` -/

/-- The child-root pair data of `TwoPointReducedData` with the single
pair-complement field replaced by its two explicit components and the two
exponent comparisons.  All other fields are exactly those of
`TwoPointReducedData`; in particular the Gaussian root-residue identification,
the root modulus bounds and the rational-good complement are unchanged. -/
structure PairEventMassData (Ω : Type*) [Fintype Ω] where
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
  /-- Exponent of the pair-event complement mass. -/
  cB : ℝ
  /-- The pair-event complement decays faster than the height grows. -/
  cV_lt_cB : cV < cB
  /-- The prescribed root modulo the field. -/
  aRes : ℕ → ℤ
  /-- The root modulus. -/
  q : ℕ → ℕ
  /-- The Gaussian center. -/
  muG : ℕ → ℝ
  /-- The Gaussian width. -/
  sigma : ℕ → ℝ
  /-- Exponent of the root-mass lower bound. -/
  cR : ℝ
  cR_nonneg : 0 ≤ cR
  /-- Exponent of the rational-good complement. -/
  cG : ℝ
  /-- The root mass dominates the rational-good complement. -/
  cR_lt_cG : cR < cG
  /-- The ordinary one-point upper bound. -/
  mean_upper : UnconditionedMeanUpper μ Z cM
  /-- The deterministic pointwise height cut. -/
  height_upper : NormalizedHeightUpper Z cV
  /-- Positivity of the normalized height. -/
  Z_nonneg : NormalizedHeightNonneg Z
  /-- The child-root mass is the Gaussian residue-class mass. -/
  gaussian_root : GaussianRootResidue μ childRoot aRes q muG sigma
  /-- The explicit modulus and width bounds. -/
  root_modulus : RootModulusPolynomial q sigma cR
  /-- The rational-good complement is `D^{-cG}`. -/
  good_complement : ComplementMassUpper μ good cG
  /-- The ordinary one-point lower bound. -/
  mean_lower : UnconditionedMeanLower μ Z a₀
  /-- Exponent of the incoming-root failure mass. -/
  cIn : ℝ
  /-- The pair-complement exponent is one unit below the rational-good bound. -/
  cB_le_cG : cB + 1 ≤ cG
  /-- The pair-complement exponent is one unit below the incoming-root bound. -/
  cB_le_cIn : cB + 1 ≤ cIn
  /-- The incoming-root failure mass `Pr(g ∧ ¬R_{q,s})` is `D^{-cIn}`. -/
  incoming_complement : IncomingRootComplement μ good childRoot cIn
  /-- Exponent of the dyad cardinality. -/
  cDyad : ℝ
  cDyad_nonneg : 0 ≤ cDyad
  dyadCard : ℕ → ℕ
  dyadCard_le : ∀ᶠ n : ℕ in atTop,
    (dyadCard n : ℝ) ≤ Real.exp (cDyad * scale n)
  poolSize : ℕ → ℕ
  /-- The pool is large relative to the derived exponent
  `cM + cV + (cR + 1)`. -/
  poolSize_ge : ∀ᶠ n : ℕ in atTop,
    Real.exp ((cM + cV + (cR + 1) + cDyad + 2) * scale n) ≤ (poolSize n : ℝ)
  /-- The pair event has positive mass at every scale. -/
  event_pos : ∀ n, 0 < pmfProb (μ n) (pairEvent good childRoot n)

namespace PairEventMassData

variable {Ω : Type*} [Fintype Ω]

/-- The pair-event lower mass of the reduced bundle: exponent `cR + 1` from the
Gaussian root residue and the rational-good complement. -/
theorem eventMassLower (S : PairEventMassData Ω) :
    EventMassLower S.μ (fun n => pairEvent S.good S.childRoot n) (S.cR + 1) :=
  eventMassLower_pairEvent_of_gaussianRoot S.μ S.good S.childRoot
    S.gaussian_root S.root_modulus S.good_complement S.cR_lt_cG

/-- The pair-event complement bound of the reduced bundle, derived from the two
component masses at the cost of one explicit unit of exponent. -/
theorem complementMassUpper (S : PairEventMassData Ω) :
    ComplementMassUpper S.μ (fun n => pairEvent S.good S.childRoot n) S.cB :=
  complementMassUpper_pairEvent_of_components S.μ S.good S.childRoot
    S.good_complement S.incoming_complement S.cB_le_cG S.cB_le_cIn

/-- **The reduction to `TwoPointReducedData`.**  The pair complement field is
derived from the two component masses; every other field is transported
unchanged. -/
noncomputable def toTwoPointReducedData (S : PairEventMassData Ω) :
    TwoPointReducedData Ω where
  μ := S.μ
  good := S.good
  childRoot := S.childRoot
  Z := S.Z
  a := S.a
  a_pos := S.a_pos
  a₀ := S.a₀
  a₀_pos := S.a₀_pos
  a_le := S.a_le
  cM := S.cM
  cM_nonneg := S.cM_nonneg
  cV := S.cV
  cV_nonneg := S.cV_nonneg
  cB := S.cB
  cV_lt_cB := S.cV_lt_cB
  aRes := S.aRes
  q := S.q
  muG := S.muG
  sigma := S.sigma
  cR := S.cR
  cR_nonneg := S.cR_nonneg
  cG := S.cG
  cR_lt_cG := S.cR_lt_cG
  mean_upper := S.mean_upper
  height_upper := S.height_upper
  Z_nonneg := S.Z_nonneg
  gaussian_root := S.gaussian_root
  root_modulus := S.root_modulus
  good_complement := S.good_complement
  mean_lower := S.mean_lower
  complement_mass_upper := S.complementMassUpper
  cDyad := S.cDyad
  cDyad_nonneg := S.cDyad_nonneg
  dyadCard := S.dyadCard
  dyadCard_le := S.dyadCard_le
  poolSize := S.poolSize
  poolSize_ge := S.poolSize_ge
  event_pos := S.event_pos

/-- The reduction composes with `TwoPointReducedData.toPairConditionedData`. -/
noncomputable def toPairConditionedData (S : PairEventMassData Ω) :
    PairConditionedData Ω :=
  S.toTwoPointReducedData.toPairConditionedData

/-- The reduction composes with the existing `PairData` chain. -/
noncomputable def toPairData (S : PairEventMassData Ω) : PairData Ω :=
  S.toTwoPointReducedData.toPairData

/-- **The pool loss of the reduced bundle is `SubexpLoss`**, inherited from
`TwoPointReducedData.pairLoss_subexp`.  Thus the two component masses really
produce the pool miss estimate, not merely a renamed assumption set. -/
theorem pairLoss_subexp (S : PairEventMassData Ω) :
    SubexpLoss S.toPairData.loss :=
  S.toTwoPointReducedData.pairLoss_subexp

end PairEventMassData

/-! ## Axiom audit -/

#print axioms eventMassLower_pairEvent_of_gaussianRoot
#print axioms complementMassUpper_pairEvent_of_components
#print axioms pairEvent_mass_bounds
#print axioms PairEventMassData.eventMassLower
#print axioms PairEventMassData.complementMassUpper
#print axioms PairEventMassData.toTwoPointReducedData
#print axioms PairEventMassData.toPairConditionedData
#print axioms PairEventMassData.toPairData
#print axioms PairEventMassData.pairLoss_subexp

end Cogentic.RandomizedL20_4EventMass
