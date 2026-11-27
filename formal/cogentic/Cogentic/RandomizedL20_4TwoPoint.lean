import Cogentic.RandomizedL20_4Conditioned
import Cogentic.RandomizedEllipticAndGaussian

/-!
# L20.4 two-point: reducing the unconditioned second moment and the event mass

`Cogentic.RandomizedL20_4Conditioned` reduced the two child-root-conditioned
inputs `ConditionedTwoPoint` and `ConditionedMeanLower` to ordinary estimates
plus the explicit conditioning loss.  The remaining ordinary inputs there are

* `UnconditionedTwoPoint` — the ordinary second moment of the normalized top
  height is `D^{c_U}`;
* `EventMassLower` — the conditioning event `g ∧ R_{q,s}` has mass at least
  `D^{-c_E}`.

This file reduces those two `Prop`s to strictly smaller explicit estimates.

## The second-moment reduction

A sufficient route to the ordinary two-point bound uses the upper height cut
(G.55) and the ordinary one-point upper bound.  (The paper's two-mark estimate
is a different route to the same conclusion; the one-point route recorded here
has strictly smaller hypotheses.)  We state exactly those:

* `UnconditionedMeanUpper μ Z cM` —
  `E[Z] ≤ D^{cM}` eventually;
* `NormalizedHeightUpper Z cV` — the deterministic pointwise cut
  `Z(ω) ≤ D^{cV}` eventually;
* `NormalizedHeightNonneg Z` — `0 ≤ Z(ω)`.

Then `E[Z²] = E[Z · Z] ≤ D^{cV} E[Z] ≤ D^{cM+cV}`, which is
`unconditionedTwoPoint_of_meanUpper_height`.  Both inputs are one-point
statements, hence strictly weaker than the second-moment bound itself; no
estimate is replaced by `0`.

The Hasse incidence count (`RandomizedHasseIncidence.rich_hasse_centres_mul_le`,
in fraction form `RandomizedL20_4Conditioned.hasse_rich_fraction_le`) is the
deterministic dyadic trimming input of the surrounding L20.4 pool assembly: it
bounds how many primes can be rich in Hasse-window witnesses.  It is not
consumed by these two one-point/mass statements; the probabilistic side uses
the finite-law infrastructure (`pmfExpect`, `pmfProb`, `condExpect`) shared with
`RandomizedEpochPool`.

## The event-mass reduction

The incoming-root probability is the Gaussian residue-class probability of the
prescribed child root modulo `q`.  The existing Gaussian estimate
`Cogentic.RandomizedEllipticAndGaussian.gaussian_residue_class_prob_interval`
gives, for `σ ≥ q`,

`(1 - q/σ)/q ≤ Pr(a mod q) ≤ (1 + q/σ)/q`.

We isolate the two explicit ingredients:

* `GaussianRootResidue μ childRoot a q σ` — the modelling identification of the
  child-root mass with the Gaussian residue-class mass `Z_a / Z`;
* `RootModulusPolynomial q σ cR` — the arithmetic bounds `q > 0`,
  `2q ≤ σ` and `2q ≤ D^{cR}`.

With `2q ≤ σ` the Gaussian lower bound is at least `1/(2q)`, and the modulus
bound turns that into `D^{-cR}`.  This is
`eventMassLower_of_gaussianRoot`.  It uses the existing Gaussian estimate; the
only non-analytic field is the explicit identification `GaussianRootResidue`.

To pass from the root event `R_{q,s}` to the pair event `g ∧ R_{q,s}` we also
use the explicit rational-good complement bound

* `ComplementMassUpper μ good cG` with `cR < cG`.

Then `Pr(g ∧ R) ≥ Pr(R) - Pr(¬g) ≥ D^{-cR} - D^{-cG} ≥ D^{-(cR+1)}`, which is
`eventMassLower_pairEvent_of_root_complement`.  The extra `+1` is the explicit
half-mass absorption, not a discarded factor.

## The reduction to `PairConditionedData`

`TwoPointReducedData` has exactly the fields of `PairConditionedData` except
that `uncond_two_point` and `event_mass_lower` are replaced by the sub-`Prop`s
above.  Its `toPairConditionedData` derives the two missing fields and produces
the parent structure, so any later consumer of `PairConditionedData` can use
this strictly finer input bundle.  Consequently the pool loss of the resulting
`PairData` is `SubexpLoss` (`pairLoss_subexp`).

No `sorry`, `admit`, `axiom`, `native_decide`, or zero loss: every exponent is
explicit and the Gaussian interval, the height cut, the complement mass and
the `+1` from the half-mass comparison are all retained.
-/

namespace Cogentic.RandomizedL20_4TwoPoint

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned

/-! ## 1. The one-point sub-`Prop`s for the unconditioned second moment -/

/-- The ordinary first moment of the normalized top height is at most
`D^{c}`.  This is the one-point upper bound (G.55/D^{O(1)}) that replaces the
full second-moment input. -/
def UnconditionedMeanUpper {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (Z : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, pmfExpect (μ n) (Z n) ≤ Real.exp (c * scale n)

/-- The deterministic pointwise upper height cut: `Z(ω) ≤ D^{c}` at every
outcome.  This is the upper cut of the pool note, stated without any
exceptional set. -/
def NormalizedHeightUpper {Ω : Type*} (Z : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ ω : Ω, Z n ω ≤ Real.exp (c * scale n)

/-- Positivity of the normalized top height.  This is a modelling fact, not an
analytic estimate. -/
def NormalizedHeightNonneg {Ω : Type*} (Z : ℕ → Ω → ℝ) : Prop :=
  ∀ n ω, 0 ≤ Z n ω

/-- **The ordinary two-point bound from the one-point upper bound and the
pointwise height cut.**  If `E[Z] ≤ D^{cM}`, `Z ≥ 0`, and `Z ≤ D^{cV}`
pointwise, then `E[Z²] ≤ D^{cM+cV}`.  The exponent `cM + cV` is the sum of the
two one-point exponents; nothing is absorbed into a constant. -/
theorem unconditionedTwoPoint_of_meanUpper_height {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (Z : ℕ → Ω → ℝ) {cM cV : ℝ}
    (hmean : UnconditionedMeanUpper μ Z cM)
    (hZ : NormalizedHeightNonneg Z)
    (hheight : NormalizedHeightUpper Z cV) :
    UnconditionedTwoPoint μ Z (cM + cV) := by
  unfold UnconditionedTwoPoint UnconditionedMeanUpper NormalizedHeightUpper at *
  filter_upwards [hmean, hheight] with n hm hh
  have hterm : ∀ ω : Ω,
      pmfWeight (μ n) ω * Z n ω ^ 2 ≤
        pmfWeight (μ n) ω * (Z n ω * Real.exp (cV * scale n)) := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (pmfWeight_nonneg (μ n) ω)
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (hh ω) (hZ n ω)
  calc pmfExpect (μ n) (fun ω => Z n ω ^ 2)
      = ∑ ω : Ω, pmfWeight (μ n) ω * Z n ω ^ 2 := rfl
    _ ≤ ∑ ω : Ω, pmfWeight (μ n) ω * (Z n ω * Real.exp (cV * scale n)) :=
        Finset.sum_le_sum fun ω _ => hterm ω
    _ = (∑ ω : Ω, pmfWeight (μ n) ω * Z n ω) * Real.exp (cV * scale n) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ω _
        ring
    _ = pmfExpect (μ n) (Z n) * Real.exp (cV * scale n) := rfl
    _ ≤ Real.exp (cM * scale n) * Real.exp (cV * scale n) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = Real.exp ((cM + cV) * scale n) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ## 2. The Gaussian root-mass sub-`Prop`s -/

/-- The Gaussian residue-class mass of the prescribed root `a` modulo `q`:
the ratio `Z_a / Z` of the residue-class sum to the full discrete Gaussian sum.
This is exactly the quantity bounded by
`Cogentic.RandomizedEllipticAndGaussian.gaussian_residue_class_prob_interval`. -/
noncomputable def gaussianRootMass (a : ℕ → ℤ) (q : ℕ → ℕ)
    (mu sigma : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑' k : ℤ, if (k : ZMod (q n)) = (a n : ZMod (q n)) then
      Cogentic.RandomizedEllipticAndGaussian.coeffGaussian k (mu n) (sigma n) else 0) /
    (∑' k : ℤ,
      Cogentic.RandomizedEllipticAndGaussian.coeffGaussian k (mu n) (sigma n))

/-- The child-root event `R_{q,s}` is modelled by the Gaussian residue class of
the prescribed root.  This is the explicit modelling identification; the
analytic content is supplied by the Gaussian residue-class estimate. -/
def GaussianRootResidue {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (a : ℕ → ℤ) (q : ℕ → ℕ) (mu sigma : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, pmfProb (μ n) (E n) = gaussianRootMass a q mu sigma n

/-- The explicit arithmetic side of the Gaussian root estimate: `q > 0`,
`2q ≤ σ` (so the residue-class lower bound is at least `1/(2q)`), and
`2q ≤ D^{cR}` (so `1/(2q) ≥ D^{-cR}`). -/
def RootModulusPolynomial (q : ℕ → ℕ) (sigma : ℕ → ℝ) (cR : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    0 < q n ∧ 2 * (q n : ℝ) ≤ sigma n ∧
      2 * (q n : ℝ) ≤ Real.exp (cR * scale n)

/-- **The child-root mass is `D^{-cR}` from the Gaussian residue-class
estimate.**  The Gaussian interval
`(1 - q/σ)/q ≤ Z_a/Z` is at least `1/(2q)` when `2q ≤ σ`; the modulus bound
`2q ≤ D^{cR}` then gives `1/(2q) ≥ D^{-cR}`.  The lower bound is exactly the
`EventMassLower` statement for the root event. -/
theorem eventMassLower_of_gaussianRoot {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) {a : ℕ → ℤ} {q : ℕ → ℕ}
    {mu sigma : ℕ → ℝ} {cR : ℝ}
    (hres : GaussianRootResidue μ E a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR) :
    EventMassLower μ E cR := by
  unfold EventMassLower GaussianRootResidue RootModulusPolynomial at *
  filter_upwards [hres, hmod] with n hres' hmod'
  obtain ⟨hq, hσ2, hqexp⟩ := hmod'
  have hqR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hq
  have hσpos : (0 : ℝ) < sigma n := by
    have : (0 : ℝ) < 2 * (q n : ℝ) := by positivity
    linarith
  have hσq : (q n : ℝ) ≤ sigma n := by linarith
  have hint := Cogentic.RandomizedEllipticAndGaussian.gaussian_residue_class_prob_interval
    (a n) (q n) hq (mu n) (sigma n) hσq
  have hlow : (1 - (q n : ℝ) / sigma n) / (q n : ℝ) ≤
      gaussianRootMass a q mu sigma n := by
    simpa [gaussianRootMass] using hint.1
  have hqσ : (q n : ℝ) / sigma n ≤ 1 / 2 := by
    rw [div_le_iff₀ hσpos]
    linarith
  have hhalf : (1 : ℝ) / 2 ≤ 1 - (q n : ℝ) / sigma n := by linarith
  have hdiv : (1 / 2 : ℝ) / (q n : ℝ) ≤
      (1 - (q n : ℝ) / sigma n) / (q n : ℝ) :=
    div_le_div_of_nonneg_right hhalf hqR.le
  have hhalfq : Real.exp (-cR * scale n) ≤ (1 / 2 : ℝ) / (q n : ℝ) := by
    have hqle : (q n : ℝ) ≤ (1 / 2) * Real.exp (cR * scale n) := by linarith
    have hmul : Real.exp (-cR * scale n) * (q n : ℝ) ≤ 1 / 2 := by
      have h1 : Real.exp (-cR * scale n) * (q n : ℝ) ≤
          Real.exp (-cR * scale n) * ((1 / 2) * Real.exp (cR * scale n)) :=
        mul_le_mul_of_nonneg_left hqle (Real.exp_pos _).le
      have h2 : Real.exp (-cR * scale n) * ((1 / 2) * Real.exp (cR * scale n)) =
          1 / 2 := by
        have hprod : Real.exp (-cR * scale n) * Real.exp (cR * scale n) = 1 := by
          rw [← Real.exp_add, show -cR * scale n + cR * scale n = 0 by ring,
            Real.exp_zero]
        calc Real.exp (-cR * scale n) * ((1 / 2) * Real.exp (cR * scale n))
            = (1 / 2) * (Real.exp (-cR * scale n) * Real.exp (cR * scale n)) := by
                ring
          _ = 1 / 2 := by rw [hprod, mul_one]
      exact h1.trans_eq h2
    rw [le_div_iff₀ hqR]
    linarith
  calc Real.exp (-cR * scale n)
      ≤ (1 / 2 : ℝ) / (q n : ℝ) := hhalfq
    _ ≤ (1 - (q n : ℝ) / sigma n) / (q n : ℝ) := hdiv
    _ ≤ gaussianRootMass a q mu sigma n := hlow
    _ = pmfProb (μ n) (E n) := hres'.symm

/-! ## 3. Passing from the root event to the pair event -/

/-- The scalar comparison `D^{-cR} - D^{-cG} ≥ D^{-(cR+1)}` eventually when
`cR < cG`.  Both terms on the left tend to zero, so their sum is eventually at
most one. -/
theorem eventually_exp_neg_add_exp_neg_le_one {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * scale n) + Real.exp (-(1 : ℝ) * scale n) ≤ 1 := by
  have h1 := eventually_exp_sub_mul_le_half (cV := 0) (cB := 1) zero_lt_one one_pos
  have h2 := eventually_exp_sub_mul_le_half (cV := 0) (cB := c) hc one_pos
  filter_upwards [h1, h2] with n h1' h2'
  have h1'' : Real.exp (-(1 : ℝ) * scale n) ≤ 1 / 2 := by
    simpa using h1'
  have h2'' : Real.exp (-c * scale n) ≤ 1 / 2 := by
    simpa using h2'
  linarith

/-- Elementary subadditivity of the finite probability mass:
`Pr(A) ≤ Pr(A ∧ B) + Pr(¬B)`.  Equivalently
`Pr(A) - Pr(¬B) ≤ Pr(A ∧ B)`. -/
theorem pmfProb_and_ge_sub {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B] :
    pmfProb μ A - pmfProb μ (fun ω => ¬ B ω) ≤
      pmfProb μ (fun ω => A ω ∧ B ω) := by
  classical
  rw [pmfProb_eq_sum_filter, pmfProb_eq_sum_filter, pmfProb_eq_sum_filter]
  let w : Ω → ℝ := pmfWeight μ
  have hsplit : (∑ ω ∈ Finset.univ.filter A, w ω) =
      (∑ ω ∈ Finset.univ.filter (fun ω => A ω ∧ B ω), w ω) +
        (∑ ω ∈ Finset.univ.filter (fun ω => A ω ∧ ¬ B ω), w ω) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ.filter A)
      (p := B) (f := w)]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext ω
      simp [Finset.mem_filter]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext ω
      simp [Finset.mem_filter]
  have hle : (∑ ω ∈ Finset.univ.filter (fun ω => A ω ∧ ¬ B ω), w ω) ≤
      ∑ ω ∈ Finset.univ.filter (fun ω => ¬ B ω), w ω := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter] at hω ⊢
      exact ⟨Finset.mem_univ _, hω.2.2⟩
    · intro ω _ _
      exact pmfWeight_nonneg μ ω
  linarith

/-- **The pair-event mass from the root mass and the rational-good complement.**
If the root event has mass at least `D^{-cR}` and the complement of `good` has
mass at most `D^{-cG}` with `cR < cG`, then the pair event `good ∧ childRoot`
has mass at least `D^{-(cR+1)}`.  The `+1` is the explicit half-mass absorption
in `D^{-cR} - D^{-cG} ≥ D^{-(cR+1)}`. -/
theorem eventMassLower_pairEvent_of_root_complement {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {cR cG : ℝ}
    (hRG : cR < cG)
    (hroot : EventMassLower μ childRoot cR)
    (hgood : ComplementMassUpper μ good cG) :
    EventMassLower μ (fun n => pairEvent good childRoot n) (cR + 1) := by
  classical
  unfold EventMassLower ComplementMassUpper at *
  have hc : 0 < cG - cR := sub_pos.mpr hRG
  filter_upwards [hroot, hgood, eventually_exp_neg_add_exp_neg_le_one hc] with
    n hroot' hgood' hscalar
  have hprob : pmfProb (μ n) (childRoot n) -
      pmfProb (μ n) (fun ω => ¬ good n ω) ≤
        pmfProb (μ n) (fun ω => pairEvent good childRoot n ω) := by
    simpa [pairEvent, and_comm] using
      pmfProb_and_ge_sub (μ n) (childRoot n) (good n)
  have hfac : Real.exp (-cR * scale n) * Real.exp (-(cG - cR) * scale n) =
      Real.exp (-cG * scale n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hstep : Real.exp (-(cR + 1) * scale n) ≤
      Real.exp (-cR * scale n) - Real.exp (-cG * scale n) := by
    have h1 : Real.exp (-(1 : ℝ) * scale n) ≤
        1 - Real.exp (-(cG - cR) * scale n) := by
      linarith [hscalar]
    have hmul := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-cR * scale n)).le
    have hprod : Real.exp (-cR * scale n) * Real.exp (-(1 : ℝ) * scale n) =
        Real.exp (-(cR + 1) * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (-(cR + 1) * scale n)
        = Real.exp (-cR * scale n) * Real.exp (-(1 : ℝ) * scale n) := hprod.symm
      _ ≤ Real.exp (-cR * scale n) *
            (1 - Real.exp (-(cG - cR) * scale n)) := hmul
      _ = Real.exp (-cR * scale n) -
            Real.exp (-cR * scale n) * Real.exp (-(cG - cR) * scale n) := by ring
      _ = Real.exp (-cR * scale n) - Real.exp (-cG * scale n) := by rw [hfac]
  calc Real.exp (-(cR + 1) * scale n)
      ≤ Real.exp (-cR * scale n) - Real.exp (-cG * scale n) := hstep
    _ ≤ pmfProb (μ n) (childRoot n) -
          pmfProb (μ n) (fun ω => ¬ good n ω) := by linarith
    _ ≤ pmfProb (μ n) (fun ω => pairEvent good childRoot n ω) := hprob

/-- A pointwise height cut is in particular a cut off any event. -/
theorem offEventHeightUpper_of_heightUpper {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) {c : ℝ}
    (h : NormalizedHeightUpper Z c) :
    OffEventHeightUpper μ E Z c := by
  unfold OffEventHeightUpper NormalizedHeightUpper at *
  filter_upwards [h] with n hn ω _
  exact hn ω

/-! ## 4. The reduced input bundle and its realization of `PairConditionedData` -/

/-- The child-root pair data with the unconditioned two-point bound and the
event-mass lower bound replaced by the explicit sub-`Prop`s of Sections 1--3.
All other fields are exactly those of `PairConditionedData`. -/
structure TwoPointReducedData (Ω : Type*) [Fintype Ω] where
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
  /-- The pair-event complement mass upper bound. -/
  complement_mass_upper : ComplementMassUpper μ (fun n => pairEvent good childRoot n) cB
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

namespace TwoPointReducedData

variable {Ω : Type*} [Fintype Ω]

/-- The reduced unconditioned second-moment bound.  Its exponent is
`cM + cV`, the sum of the one-point and height-cut exponents. -/
theorem uncondTwoPoint (S : TwoPointReducedData Ω) :
    UnconditionedTwoPoint S.μ S.Z (S.cM + S.cV) :=
  unconditionedTwoPoint_of_meanUpper_height S.μ S.Z S.mean_upper S.Z_nonneg
    S.height_upper

/-- The reduced pair-event mass lower bound.  Its exponent is `cR + 1`, the
Gaussian root exponent plus the explicit half-mass loss. -/
theorem eventMassLower (S : TwoPointReducedData Ω) :
    EventMassLower S.μ (fun n => pairEvent S.good S.childRoot n) (S.cR + 1) :=
  eventMassLower_pairEvent_of_root_complement S.μ S.good S.childRoot S.cR_lt_cG
    (eventMassLower_of_gaussianRoot S.μ S.childRoot S.gaussian_root S.root_modulus)
    S.good_complement

/-- **The reduction to `PairConditionedData`.**  The derived two-point and
event-mass fields replace their parent counterparts; every other field is
transported unchanged, and the parent exponents are
`cU = cM + cV`, `cE = cR + 1`. -/
noncomputable def toPairConditionedData (S : TwoPointReducedData Ω) :
    PairConditionedData Ω where
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
  cE := S.cR + 1
  cE_nonneg := by linarith [S.cR_nonneg]
  cV := S.cV
  cB := S.cB
  cV_lt_cB := S.cV_lt_cB
  cDyad := S.cDyad
  cDyad_nonneg := S.cDyad_nonneg
  dyadCard := S.dyadCard
  dyadCard_le := S.dyadCard_le
  poolSize := S.poolSize
  poolSize_ge := S.poolSize_ge
  event_pos := S.event_pos
  uncond_two_point := S.uncondTwoPoint
  event_mass_lower := S.eventMassLower
  uncond_mean_lower := S.mean_lower
  off_event_height := offEventHeightUpper_of_heightUpper S.μ _ S.Z S.height_upper
  complement_mass_upper := S.complement_mass_upper

/-- The resulting `PairData` is the parent realization of
`PairConditionedData`, so the reduction composes with the existing chain. -/
noncomputable def toPairData (S : TwoPointReducedData Ω) : PairData Ω :=
  S.toPairConditionedData.toPairData

/-- **The pool loss of the reduced data is `SubexpLoss`.**  This is the existing
`L20_4Sub.PairData.loss_subexp` applied after the reduction; it confirms that
the two replaced fields are the only pair-side inputs it consumed. -/
theorem pairLoss_subexp (S : TwoPointReducedData Ω) :
    SubexpLoss S.toPairData.loss :=
  S.toPairData.loss_subexp

end TwoPointReducedData

/-! ## Axiom audit -/

#print axioms unconditionedTwoPoint_of_meanUpper_height
#print axioms eventMassLower_of_gaussianRoot
#print axioms eventually_exp_neg_add_exp_neg_le_one
#print axioms pmfProb_and_ge_sub
#print axioms eventMassLower_pairEvent_of_root_complement
#print axioms offEventHeightUpper_of_heightUpper
#print axioms TwoPointReducedData.uncondTwoPoint
#print axioms TwoPointReducedData.eventMassLower
#print axioms TwoPointReducedData.toPairConditionedData
#print axioms TwoPointReducedData.toPairData
#print axioms TwoPointReducedData.pairLoss_subexp

end Cogentic.RandomizedL20_4TwoPoint
