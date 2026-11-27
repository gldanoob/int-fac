import Cogentic.RandomizedL20_4EventMass
import Cogentic.RandomizedEllipticAndGaussian

/-!
# L20.4 incoming: the incoming-root failure mass

`Cogentic.RandomizedL20_4EventMass` kept the incoming-root failure mass
`Pr(g ∧ ¬R_{q,s})` as the named sub-`Prop`

`IncomingRootComplement μ good childRoot cIn`

and used it, together with the rational-good complement, to bound the complement
of the pair event `g ∧ R_{q,s}`.  This file does three things.

## 1. Exact mass algebra

The failure mass is *not* an independent quantity.  It satisfies the exact
identity

`Pr(g ∧ ¬R) = Pr(g) - Pr(g ∧ R)`,

and equivalently `IncomingRootComplement` says that the pair event together with
the rational-bad event covers all but `D^{-cIn}` of the total mass
(`incomingRootComplement_iff_pairEvent_add_compl`).  With the rational-good
complement it therefore gives the *lower* bound
`Pr(g ∧ R) ≥ 1 - D^{-cIn} - D^{-cG}` (`pairEventMass_ge_of_incomingRoot`).
This is the missing converse direction of the pair-event mass lower bound: it
shows that the incoming failure mass and a *small* pair event cannot both hold.

## 2. The smallest explicit complement-mass input

`IncomingRootComplement` is exactly equivalent to the existence of an explicit
bad event `Bad` with

* `g ∧ ¬R ⊆ Bad` eventually, and
* `Pr(Bad) ≤ D^{-cIn}` eventually

(`incomingRootComplement_iff_exists_bad`).  The canonical choice
`Bad = g ∧ ¬R` recovers the definition, and any such `Bad` gives the desired
bound by monotonicity (`incomingRootComplement_of_bad`).  This is the smallest
explicit input: no structure of `Bad` is required beyond containing the failure
set and carrying the mass.  The single-event sufficient condition is
`ComplementMassUpper μ childRoot cIn`, i.e. the *root event itself* must be
co-large (`incomingRootComplement_of_complementMassUpper_childRoot`).

## 3. The Gaussian root-residue estimate does **not** imply it

The Gaussian interval of
`Cogentic.RandomizedEllipticAndGaussian.gaussian_residue_class_prob_interval`

`(1 - q/σ)/q ≤ Pr(R_{q,s}) ≤ (1 + q/σ)/q`

gives only an *upper* bound on the root probability, hence a *lower* bound on
the failure mass.  Concretely, from `2q ≤ σ` we obtain

`Pr(g ∧ ¬R) ≤ Pr(¬R) = 1 - Pr(R) ≤ 1 - 1/(2q)`

(`incomingMass_le_one_sub_half_inv`); the failure mass is co-large, not small.
Combining this with the rational-good complement and the *assumed* incoming
bound `Pr(g ∧ ¬R) ≤ D^{-cIn}` forces the modulus to be bounded:

`q n ≤ 3` eventually (`modulus_le_three_of_incomingRootComplement`).

Consequently, whenever `4 ≤ q n` eventually, `IncomingRootComplement` is false
for every positive exponent (`not_incomingRootComplement_of_four_le_modulus`),
and in particular no `PairEventMassData` can exist in that regime
(`PairEventMassData.false_of_four_le_modulus`).  The same argument applied to
the root event shows that `ComplementMassUpper μ childRoot cIn` is likewise
impossible for large `q` (`not_complementMassUpper_childRoot_of_four_le_modulus`).

Thus the only consistent explicit complement-mass input for the pair event is
the pair-complement bound itself (or, equivalently, a bad-event mass bound
containing its complement, `ComplementMassUpper_pairEvent_of_bad`).  The
decomposition into `Pr(¬g) + Pr(g ∧ ¬R)` is valid as an identity but *cannot*
be used to manufacture the pair complement bound from the Gaussian estimate in
the regime where the prescribed child root is a `1/q`-event.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-mass: every exponent is
explicit and all masses are retained.
-/

namespace Cogentic.RandomizedL20_4Incoming

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

/-! ## 1. Exact mass algebra -/

/-- The exact decomposition of the incoming failure mass:
`Pr(g ∧ ¬R) = Pr(g) - Pr(g ∧ R)`.  This is the finite-`PMF` identity behind
`IncomingRootComplement`; it makes the failure mass a difference of two
probabilities rather than an independent estimate. -/
theorem pmfProb_incoming_eq_good_sub_pair {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (good childRoot : Ω → Prop) :
    pmfProb μ (fun ω => good ω ∧ ¬ childRoot ω) =
      pmfProb μ good - pmfProb μ (fun ω => good ω ∧ childRoot ω) := by
  classical
  have hnot := pmfProb_not_and μ good childRoot
  have hpair := pmfProb_compl μ (fun ω => good ω ∧ childRoot ω)
  have hgood := pmfProb_compl μ good
  linarith

/-- **Co-large form of `IncomingRootComplement`.**  The failure mass is at most
`D^{-c}` iff the pair event together with the rational-bad event covers all but
`D^{-c}` of the probability mass.  No estimate is lost in this rewriting. -/
theorem incomingRootComplement_iff_pairEvent_add_compl {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ} :
    IncomingRootComplement μ good childRoot c ↔
      ∀ᶠ n : ℕ in atTop,
        1 - Real.exp (-c * scale n) ≤
          pmfProb (μ n) (pairEvent good childRoot n) +
            pmfProb (μ n) (fun ω => ¬ good n ω) := by
  unfold IncomingRootComplement
  constructor
  · intro h
    filter_upwards [h] with n hn
    have hid := pmfProb_incoming_eq_good_sub_pair (μ n) (good n) (childRoot n)
    have hgood := pmfProb_compl (μ n) (good n)
    have hpair : pmfProb (μ n) (pairEvent good childRoot n) =
        pmfProb (μ n) (fun ω => good n ω ∧ childRoot n ω) := rfl
    rw [hpair]
    linarith
  · intro h
    filter_upwards [h] with n hn
    have hid := pmfProb_incoming_eq_good_sub_pair (μ n) (good n) (childRoot n)
    have hgood := pmfProb_compl (μ n) (good n)
    have hpair : pmfProb (μ n) (pairEvent good childRoot n) =
        pmfProb (μ n) (fun ω => good n ω ∧ childRoot n ω) := rfl
    rw [hpair] at hn
    linarith

/-- **The pair event is co-large when the incoming failure is small.**  With the
rational-good complement `Pr(¬g) ≤ D^{-cG}`, the incoming bound
`Pr(g ∧ ¬R) ≤ D^{-cIn}` forces `Pr(g ∧ R) ≥ 1 - D^{-cIn} - D^{-cG}`.  This is
the direction opposite to the pair-event lower mass and records exactly why a
small incoming failure mass is incompatible with a small root event. -/
theorem pairEventMass_ge_of_incomingRoot {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {cG cIn : ℝ}
    (hgood : ComplementMassUpper μ good cG)
    (hIn : IncomingRootComplement μ good childRoot cIn) :
    ∀ᶠ n : ℕ in atTop,
      1 - Real.exp (-cIn * scale n) - Real.exp (-cG * scale n) ≤
        pmfProb (μ n) (pairEvent good childRoot n) := by
  have heq :=
    (incomingRootComplement_iff_pairEvent_add_compl μ good childRoot).mp hIn
  filter_upwards [heq, hgood] with n hn hg
  linarith

/-! ## 2. The smallest explicit bad-event input -/

/-- A bad-event presentation of the incoming failure mass: an explicit event
`Bad` containing `g ∧ ¬R` and carrying mass at most `D^{-c}`.  This is the
smallest possible input shape: only containment and the mass bound are used. -/
structure IncomingRootBadData {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) (c : ℝ) where
  /-- The explicit bad event. -/
  Bad : ℕ → Ω → Prop
  /-- Every good outcome with a failing root lies in `Bad`. -/
  subset : ∀ᶠ n : ℕ in atTop, ∀ ω, good n ω → ¬ childRoot n ω → Bad n ω
  /-- The bad event has mass at most `D^{-c}`. -/
  mass : ∀ᶠ n : ℕ in atTop,
    pmfProb (μ n) (Bad n) ≤ Real.exp (-c * scale n)

/-- A bad-event mass bound containing the failure set implies
`IncomingRootComplement`, by monotonicity of the probability. -/
theorem incomingRootComplement_of_bad {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ}
    (S : IncomingRootBadData μ good childRoot c) :
    IncomingRootComplement μ good childRoot c := by
  unfold IncomingRootComplement
  filter_upwards [S.subset, S.mass] with n hsub hmass
  exact (pmfProb_mono (μ n) (fun ω hω => hsub ω hω.1 hω.2)).trans hmass

/-- **Characterization by a bad event.**  `IncomingRootComplement` is exactly the
existence of an explicit bad event containing `g ∧ ¬R` with mass `≤ D^{-c}`.
The canonical witness is `Bad = g ∧ ¬R` itself, so no information is added or
lost; this is the smallest explicit complement-mass input. -/
theorem incomingRootComplement_iff_exists_bad {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ} :
    IncomingRootComplement μ good childRoot c ↔
      ∃ Bad : ℕ → Ω → Prop,
        (∀ᶠ n : ℕ in atTop, ∀ ω, good n ω → ¬ childRoot n ω → Bad n ω) ∧
        (∀ᶠ n : ℕ in atTop,
          pmfProb (μ n) (Bad n) ≤ Real.exp (-c * scale n)) := by
  constructor
  · intro h
    refine ⟨fun n ω => good n ω ∧ ¬ childRoot n ω, ?_, h⟩
    exact Eventually.of_forall fun n ω hg hr => ⟨hg, hr⟩
  · rintro ⟨Bad, hsub, hmass⟩
    exact incomingRootComplement_of_bad μ good childRoot ⟨Bad, hsub, hmass⟩

/-- The single-event sufficient condition: if the root event itself has
complement mass at most `D^{-c}`, then the good-failure mass is at most
`D^{-c}`.  This is the smallest *single-event* input, but it is incompatible
with the Gaussian root estimate for large `q` (see
`not_complementMassUpper_childRoot_of_four_le_modulus`). -/
theorem incomingRootComplement_of_complementMassUpper_childRoot
    {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) {c : ℝ}
    (h : ComplementMassUpper μ childRoot c) :
    IncomingRootComplement μ good childRoot c :=
  incomingRootComplement_of_bad μ good childRoot
    { Bad := fun n ω => ¬ childRoot n ω
      subset := Eventually.of_forall fun _ _ _ hr => hr
      mass := h }

/-- Exponent monotonicity: a bound at exponent `c₁` gives one at every smaller
exponent `c₂`.  This is the sense in which `cIn` can be taken as the smallest
exponent for which the input is available. -/
theorem incomingRootComplement_mono {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c₁ c₂ : ℝ}
    (hc : c₂ ≤ c₁) (h : IncomingRootComplement μ good childRoot c₁) :
    IncomingRootComplement μ good childRoot c₂ := by
  unfold IncomingRootComplement at *
  filter_upwards [h, scale_grows.eventually_ge_atTop 0] with n hn hH
  exact hn.trans (Real.exp_le_exp.mpr (by nlinarith))

/-- A full subexponential bound on the failure mass gives the input at every
positive exponent. -/
theorem incomingRootComplement_of_subexpLoss {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ} (hc : 0 < c)
    (h : SubexpLoss fun n =>
      pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω)) :
    IncomingRootComplement μ good childRoot c :=
  h c hc

/-- Rewording as a complement-mass upper bound for the event `¬g ∨ R`.  This is
the exact event-level form of `IncomingRootComplement`. -/
theorem incomingRootComplement_iff_complementMassUpper_not_or
    {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) {c : ℝ} :
    IncomingRootComplement μ good childRoot c ↔
      ComplementMassUpper μ (fun n ω => ¬ good n ω ∨ childRoot n ω) c := by
  unfold IncomingRootComplement ComplementMassUpper
  constructor <;> intro h <;> filter_upwards [h] with n hn
  · simpa only [not_or, not_not] using hn
  · simpa only [not_or, not_not] using hn

/-! ## 3. What the Gaussian root-residue estimate actually gives -/

/-- Any positive constant eventually dominates `exp (-δ * scale n)`. -/
theorem eventually_exp_neg_le_const {bound δ : ℝ} (hbound : 0 < bound) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-δ * scale n) ≤ bound := by
  filter_upwards [scale_grows.eventually_ge_atTop ((-Real.log bound) / δ)] with n hn
  have hmul : -Real.log bound ≤ δ * scale n := by
    have := (div_le_iff₀ hδ).mp hn
    linarith
  calc Real.exp (-δ * scale n) ≤ Real.exp (Real.log bound) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = bound := Real.exp_log hbound

/-- The upper half of the Gaussian residue-class interval, in the exact form of
`gaussianRootMass`. -/
theorem gaussianRootMass_le_upper {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ}
    {n : ℕ} (hq : 0 < q n) (hσq : (q n : ℝ) ≤ sigma n) :
    gaussianRootMass a q mu sigma n ≤
      (1 + (q n : ℝ) / sigma n) / (q n : ℝ) := by
  have hint :=
    Cogentic.RandomizedEllipticAndGaussian.gaussian_residue_class_prob_interval
      (a n) (q n) hq (mu n) (sigma n) hσq
  simpa [gaussianRootMass] using hint.2

/-- **What the Gaussian estimate gives for the incoming failure mass.**  From
`2q ≤ σ` the root event has mass at least `1/(2q)`, so its complement, and hence
`g ∧ ¬R`, has mass at most `1 - 1/(2q)`.  This is the sharpest upper bound on the
failure mass supplied by the Gaussian interval, and its right-hand side is
co-large: the estimate permits the failure mass to be almost one, not
`D^{-cIn}`. -/
theorem incomingMass_le_one_sub_half_inv {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ} {cR : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR) :
    ∀ᶠ n : ℕ in atTop,
      pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω) ≤
        1 - (1 / 2 : ℝ) / (q n : ℝ) := by
  filter_upwards [hres, hmod] with n hres' hmod'
  obtain ⟨hq, hσ2, _⟩ := hmod'
  have hqR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hq
  have hσpos : (0 : ℝ) < sigma n := by linarith
  have hσq : (q n : ℝ) ≤ sigma n := by linarith
  have hint :=
    Cogentic.RandomizedEllipticAndGaussian.gaussian_residue_class_prob_interval
      (a n) (q n) hq (mu n) (sigma n) hσq
  have hlow : (1 - (q n : ℝ) / sigma n) / (q n : ℝ) ≤
      gaussianRootMass a q mu sigma n := by
    simpa [gaussianRootMass] using hint.1
  have hqσ : (q n : ℝ) / sigma n ≤ 1 / 2 := by
    rw [div_le_iff₀ hσpos]
    linarith
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (q n : ℝ) / sigma n := by linarith
  have hhalfq : (1 / 2 : ℝ) / (q n : ℝ) ≤ gaussianRootMass a q mu sigma n :=
    (div_le_div_of_nonneg_right hhalf hqR.le).trans hlow
  have hmono : pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω) ≤
      pmfProb (μ n) (fun ω => ¬ childRoot n ω) :=
    pmfProb_mono (μ n) (fun _ hω => hω.2)
  have hcompl := pmfProb_compl (μ n) (childRoot n)
  have hbound : pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω) ≤
      1 - gaussianRootMass a q mu sigma n := by
    calc pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω)
        ≤ pmfProb (μ n) (fun ω => ¬ childRoot n ω) := hmono
      _ = 1 - pmfProb (μ n) (childRoot n) := hcompl
      _ = 1 - gaussianRootMass a q mu sigma n := by rw [hres']
  linarith

/-- **`IncomingRootComplement` forces a bounded modulus.**  Under the Gaussian
root-residue identification, the root-modulus bounds `0 < q` and `2q ≤ σ`, the
rational-good complement, and a positive incoming exponent, the assumed failure
bound `Pr(g ∧ ¬R) ≤ D^{-cIn}` can hold only if `q n ≤ 3` eventually.

Indeed the complement hypothesis makes `Pr(g ∧ R)` close to one, while the
Gaussian interval bounds it by `3/(2q)`, so `1/2 ≤ 3/(2q)`. -/
theorem modulus_le_three_of_incomingRootComplement {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ} {cR cG cIn : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (hgood : ComplementMassUpper μ good cG)
    (hIn : IncomingRootComplement μ good childRoot cIn)
    (hcG : 0 < cG) (hcIn : 0 < cIn) :
    ∀ᶠ n : ℕ in atTop, q n ≤ 3 := by
  have hpair := pairEventMass_ge_of_incomingRoot μ good childRoot hgood hIn
  filter_upwards [hres, hmod, hpair,
    eventually_exp_neg_le_const (bound := (1 / 4 : ℝ)) (δ := cG) (by norm_num) hcG,
    eventually_exp_neg_le_const (bound := (1 / 4 : ℝ)) (δ := cIn) (by norm_num) hcIn]
    with n hres' hmod' hpair' hGsmall hInSmall
  obtain ⟨hq, hσ2, _⟩ := hmod'
  have hqR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hq
  have hσpos : (0 : ℝ) < sigma n := by linarith
  have hσq : (q n : ℝ) ≤ sigma n := by linarith
  have hupper := gaussianRootMass_le_upper (a := a) (q := q) (mu := mu)
    (sigma := sigma) (n := n) hq hσq
  have hqσ : (q n : ℝ) / sigma n ≤ 1 / 2 := by
    rw [div_le_iff₀ hσpos]
    linarith
  have hnum : 1 + (q n : ℝ) / sigma n ≤ 1 + 1 / 2 := by linarith
  have hupper' : gaussianRootMass a q mu sigma n ≤ 3 / (2 * (q n : ℝ)) := by
    calc gaussianRootMass a q mu sigma n
        ≤ (1 + (q n : ℝ) / sigma n) / (q n : ℝ) := hupper
      _ ≤ (1 + 1 / 2) / (q n : ℝ) :=
          div_le_div_of_nonneg_right hnum hqR.le
      _ = 3 / (2 * (q n : ℝ)) := by
          field_simp [hqR.ne']
          ring
  have hprLe : pmfProb (μ n) (pairEvent good childRoot n) ≤
      3 / (2 * (q n : ℝ)) := by
    calc pmfProb (μ n) (pairEvent good childRoot n)
        ≤ pmfProb (μ n) (childRoot n) :=
          pmfProb_mono (μ n) (fun _ hω => hω.2)
      _ = gaussianRootMass a q mu sigma n := hres'
      _ ≤ 3 / (2 * (q n : ℝ)) := hupper'
  have hhalf : (1 / 2 : ℝ) ≤ pmfProb (μ n) (pairEvent good childRoot n) := by
    have hconst : (1 : ℝ) - 1 / 4 - 1 / 4 ≤
        pmfProb (μ n) (pairEvent good childRoot n) := by linarith
    norm_num at hconst
    exact hconst
  have hqle : (q n : ℝ) ≤ 3 := by
    have hineq : (1 / 2 : ℝ) ≤ 3 / (2 * (q n : ℝ)) := hhalf.trans hprLe
    have h2q : (0 : ℝ) < 2 * (q n : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hineq h2q.le
    rw [div_mul_cancel₀ _ h2q.ne'] at hmul
    nlinarith
  exact_mod_cast hqle

/-- **The Gaussian estimate is incompatible with a small failure mass at large
modulus.**  If `4 ≤ q n` eventually, then `IncomingRootComplement` is false for
every positive incoming exponent. -/
theorem not_incomingRootComplement_of_four_le_modulus {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop)
    {a : ℕ → ℤ} {q : ℕ → ℕ} {mu sigma : ℕ → ℝ} {cR cG cIn : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (hgood : ComplementMassUpper μ good cG)
    (hcG : 0 < cG) (hcIn : 0 < cIn)
    (hq4 : ∀ᶠ n : ℕ in atTop, 4 ≤ q n) :
    ¬ IncomingRootComplement μ good childRoot cIn := by
  intro hIn
  have hle3 := modulus_le_three_of_incomingRootComplement μ good childRoot
    hres hmod hgood hIn hcG hcIn
  obtain ⟨n, hn4, hn3⟩ := (hq4.and hle3).exists
  omega

/-- The Gaussian estimate also contradicts a co-large *root* event at large
modulus.  Consequently the sufficient condition
`ComplementMassUpper μ childRoot cIn` cannot repair the incoming bound. -/
theorem not_complementMassUpper_childRoot_of_four_le_modulus
    {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (childRoot : ℕ → Ω → Prop) {a : ℕ → ℤ} {q : ℕ → ℕ}
    {mu sigma : ℕ → ℝ} {cR c : ℝ}
    (hres : GaussianRootResidue μ childRoot a q mu sigma)
    (hmod : RootModulusPolynomial q sigma cR)
    (hc : 0 < c) (hq4 : ∀ᶠ n : ℕ in atTop, 4 ≤ q n) :
    ¬ ComplementMassUpper μ childRoot c := by
  intro hC
  have hbig : ∀ᶠ n : ℕ in atTop,
      (5 / 8 : ℝ) ≤ pmfProb (μ n) (fun ω => ¬ childRoot n ω) := by
    filter_upwards [hres, hmod, hq4] with n hres' hmod' hq4'
    obtain ⟨hq, hσ2, _⟩ := hmod'
    have hqR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hq
    have hσpos : (0 : ℝ) < sigma n := by linarith
    have hσq : (q n : ℝ) ≤ sigma n := by linarith
    have hupper := gaussianRootMass_le_upper (a := a) (q := q) (mu := mu)
      (sigma := sigma) (n := n) hq hσq
    have hqσ : (q n : ℝ) / sigma n ≤ 1 / 2 := by
      rw [div_le_iff₀ hσpos]
      linarith
    have hnum : 1 + (q n : ℝ) / sigma n ≤ 1 + 1 / 2 := by linarith
    have hupper' : gaussianRootMass a q mu sigma n ≤ 3 / (2 * (q n : ℝ)) := by
      calc gaussianRootMass a q mu sigma n
          ≤ (1 + (q n : ℝ) / sigma n) / (q n : ℝ) := hupper
        _ ≤ (1 + 1 / 2) / (q n : ℝ) :=
            div_le_div_of_nonneg_right hnum hqR.le
        _ = 3 / (2 * (q n : ℝ)) := by
            field_simp [hqR.ne']
            ring
    have hqr : (4 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq4'
    have hsmall : 3 / (2 * (q n : ℝ)) ≤ 3 / 8 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q n : ℝ))]
      nlinarith
    have hcompl := pmfProb_compl (μ n) (childRoot n)
    calc (5 / 8 : ℝ) = 1 - 3 / 8 := by norm_num
      _ ≤ 1 - 3 / (2 * (q n : ℝ)) := by linarith
      _ ≤ 1 - gaussianRootMass a q mu sigma n := by linarith
      _ = pmfProb (μ n) (fun ω => ¬ childRoot n ω) := by
          rw [hcompl, hres']
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hbig, hC,
      eventually_exp_neg_le_const (bound := (1 / 4 : ℝ)) (δ := c) (by norm_num) hc]
      with n hge hle hsmall
    linarith
  obtain ⟨n, hn⟩ := hcontra.exists
  exact hn

/-! ## 4. The direct pair-complement input (the consistent alternative) -/

/-- A bad-event presentation of the *pair*-event complement.  This is the
smallest explicit complement-mass input that survives the obstruction above:
it is exactly equivalent to `ComplementMassUpper` for the pair event and does
not decompose into the impossible `Pr(g ∧ ¬R)` bound. -/
structure PairComplementBadData {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) (c : ℝ) where
  /-- The explicit bad event. -/
  Bad : ℕ → Ω → Prop
  /-- Every outcome outside the pair event lies in `Bad`. -/
  subset : ∀ᶠ n : ℕ in atTop,
    ∀ ω, ¬ pairEvent good childRoot n ω → Bad n ω
  /-- The bad event has mass at most `D^{-c}`. -/
  mass : ∀ᶠ n : ℕ in atTop,
    pmfProb (μ n) (Bad n) ≤ Real.exp (-c * scale n)

/-- The pair-complement bound from an explicit bad event. -/
theorem complementMassUpper_pairEvent_of_bad {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ}
    (S : PairComplementBadData μ good childRoot c) :
    ComplementMassUpper μ (fun n => pairEvent good childRoot n) c :=
  complementMassUpper_of_subset_bad μ _ S.Bad S.subset S.mass

/-- Characterization: the pair-complement bound is exactly the existence of an
explicit bad event containing the complement of the pair event.  This is the
direct input consumed by `TwoPointReducedData.complement_mass_upper`, and it is
the smallest consistent explicit complement-mass statement. -/
theorem complementMassUpper_pairEvent_iff_exists_bad {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ} :
    ComplementMassUpper μ (fun n => pairEvent good childRoot n) c ↔
      ∃ Bad : ℕ → Ω → Prop,
        (∀ᶠ n : ℕ in atTop,
          ∀ ω, ¬ pairEvent good childRoot n ω → Bad n ω) ∧
        (∀ᶠ n : ℕ in atTop,
          pmfProb (μ n) (Bad n) ≤ Real.exp (-c * scale n)) := by
  constructor
  · intro h
    refine ⟨fun n ω => ¬ pairEvent good childRoot n ω, ?_, h⟩
    exact Eventually.of_forall fun _ _ hω => hω
  · rintro ⟨Bad, hsub, hmass⟩
    exact complementMassUpper_pairEvent_of_bad μ good childRoot ⟨Bad, hsub, hmass⟩

/-! ## Axiom audit -/

#print axioms pmfProb_incoming_eq_good_sub_pair
#print axioms incomingRootComplement_iff_pairEvent_add_compl
#print axioms pairEventMass_ge_of_incomingRoot
#print axioms incomingRootComplement_of_bad
#print axioms incomingRootComplement_iff_exists_bad
#print axioms incomingRootComplement_of_complementMassUpper_childRoot
#print axioms incomingRootComplement_mono
#print axioms incomingRootComplement_of_subexpLoss
#print axioms incomingRootComplement_iff_complementMassUpper_not_or
#print axioms eventually_exp_neg_le_const
#print axioms gaussianRootMass_le_upper
#print axioms incomingMass_le_one_sub_half_inv
#print axioms modulus_le_three_of_incomingRootComplement
#print axioms not_incomingRootComplement_of_four_le_modulus
#print axioms not_complementMassUpper_childRoot_of_four_le_modulus
#print axioms complementMassUpper_pairEvent_of_bad
#print axioms complementMassUpper_pairEvent_iff_exists_bad

end Cogentic.RandomizedL20_4Incoming

namespace Cogentic.RandomizedL20_4EventMass
namespace PairEventMassData

variable {Ω : Type*} [Fintype Ω]

/-- **Every `PairEventMassData` forces a bounded child modulus.**  The bundle's
Gaussian root-residue field, root-modulus bounds, rational-good complement and
incoming failure field together imply `q n ≤ 3` eventually.  This is the exact
arithmetic consequence of the incoming complement in the reduced bundle. -/
theorem modulus_le_three (S : PairEventMassData Ω) :
    ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), S.q n ≤ 3 := by
  have hcB : 0 < S.cB := lt_of_le_of_lt S.cV_nonneg S.cV_lt_cB
  have hcG : 0 < S.cG := by linarith [S.cB_le_cG]
  have hcIn : 0 < S.cIn := by linarith [S.cB_le_cIn]
  exact Cogentic.RandomizedL20_4Incoming.modulus_le_three_of_incomingRootComplement
    S.μ S.good S.childRoot S.gaussian_root S.root_modulus S.good_complement
    S.incoming_complement hcG hcIn

/-- **No `PairEventMassData` has unbounded child modulus.**  In the regime
`4 ≤ q n` eventually, the Gaussian root-residue field, the root-modulus bounds
and the two mass fields are mutually inconsistent.  The proof combines
`modulus_le_three` with the bundle's exponent comparisons `cV < cB`,
`cB + 1 ≤ cG` and `cB + 1 ≤ cIn`. -/
theorem false_of_four_le_modulus (S : PairEventMassData Ω)
    (hq : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), 4 ≤ S.q n) : False := by
  obtain ⟨n, hn4, hn3⟩ := (hq.and S.modulus_le_three).exists
  omega

#print axioms modulus_le_three
#print axioms false_of_four_le_modulus

end PairEventMassData
end Cogentic.RandomizedL20_4EventMass
