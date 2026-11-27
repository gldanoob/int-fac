import Cogentic.RandomizedL20_4Conditioned
import Cogentic.RandomizedEpochPool
import Cogentic.RandomizedHasseIncidence

/-!
# L20.4 mean: reducing the ordinary mean, height and complement inputs

`Cogentic.RandomizedL20_4Conditioned` reduced the conditioned L20.4 inputs to
the conditioned bundle `PairConditionedData`.  That bundle still carries three
*ordinary-law* fields which were only named, not derived:

* `UnconditionedMeanLower` — the ordinary first moment of the normalized top
  height is at least a fixed `a₀`;
* `OffEventHeightUpper` — off the conditioning event the normalized height is at
  most `D^{c_V}`;
* `ComplementMassUpper` — the complement of the conditioning event has mass at
  most `D^{-c_B}`.

This file proves that each of them is a consequence of strictly smaller,
explicit statements, and then reassembles `PairConditionedData` from the reduced
bundle.

## 1. The ordinary mean is the pool first-moment field

The paper's ordinary one-point estimate is *per prime*:
`a · τ_p ≤ E[Z_p]` on the rational-good part of a dyad.  This is exactly
`RandomizedEpochPool.PoolCoverageInputs.hmean`.  Summing it over the dyad and
normalizing by a deterministic reference mass gives the aggregate ordinary mean.
The reduction `unconditionedMeanLower_of_poolAggregate` keeps the dyad, the
per-prime references `τ_p`, the aggregation variables `Z_p` and the
normalization all explicit.  `unconditionedMeanLower_of_poolPrime` records the
literal `τ = 1`, single-prime specialization.

## 2. The off-event height cut is deterministic

`OffEventHeightUpper` is not a probabilistic estimate: it says the event contains
every point where the height exceeds `D^{c_V}`.  The smallest explicit inputs are
therefore

* a deterministic upper bound `H ≤ D^{c_H}` on the raw top count, and
* a deterministic lower bound `B ≥ D^{-c_P}` on the normalizing strip profile,

with `Z = H / B`.  `offEventHeightUpper_of_heightDiv` proves
`Z ≤ D^{c_H+c_P}`.  `exists_offEventHeightUpper_of_complement` records the
logical point that, if one is free to enlarge the condition event, the height cut
can always be arranged at no cost to `EventMassLower` or `ComplementMassUpper`;
the deterministic cut is used below only to keep the paper's event fixed.

## 3. The complement mass is a co-large-event statement

`ComplementMassUpper` is equivalent to the event carrying all but `D^{-c_B}` of
the mass (`complementMassUpper_iff_eventMass_ge`).  For the actual pair event
`g ∧ R_{q,s}` it splits exactly into

* the rational-good failure mass `Pr(¬g)`, and
* the incoming-root failure mass `Pr(g ∧ ¬R_{q,s})`,

(`complementMassUpper_pairEvent_iff_pairComplement`).  A union bound reduces the
pair mass to the two primitive masses with one unit of exponent lost
(`pairComplementMassUpper_of_components`).  The second primitive is the G.12
incoming exceptional mass `ε̄^in_{0,J}`; the first is the ordinary rational-good
failure.  This is where the strong content of `ComplementMassUpper` sits: it is
a co-large-event hypothesis, not a consequence of the pool first/second moment
estimates.  The file states it explicitly rather than deriving it from a bound
that does not exist.

## 4. Reassembly

`PairMeanData` bundles the three reduced inputs (pool mean data, deterministic
height/profile cut, and a subexponential mass bound on an explicit bad event
containing the complement).  `PairConditionedBase` carries the remaining fields
of `PairConditionedData`, and `PairConditionedBase.toPairConditionedData`
reassembles the parent bundle.  `pairLoss_subexp` then feeds the result through
`PairConditionedData.toPairData` and `PairData.loss_subexp`, so the reduction
really produces the pool miss estimate and not merely a renamed assumption set.

The Hasse incidence estimate `hasse_rich_fraction_le` is *not* used as a mean
bound: it controls dyad cardinalities and trimming, not `E[Z]`.  The ordinary
mean comes from the pool `hmean`; this file makes that division explicit.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss.
-/

namespace Cogentic.RandomizedL20_4Mean

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned

/-! ## 1. Finite-`PMF` algebra -/

/-- Expectation is additive over a finite sum of variables. -/
theorem pmfExpect_sum {Ω ι : Type*} [Fintype Ω] (μ : PMF Ω) (s : Finset ι)
    (X : ι → Ω → ℝ) :
    pmfExpect μ (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, pmfExpect μ (X i) := by
  unfold pmfExpect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- Expectation commutes with division by a constant. -/
theorem pmfExpect_div_const {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (X : Ω → ℝ)
    (c : ℝ) :
    pmfExpect μ (fun ω => X ω / c) = pmfExpect μ X / c := by
  unfold pmfExpect
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- The complement of an event carries the remaining mass. -/
theorem pmfProb_compl {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop) :
    pmfProb μ (fun ω => ¬ E ω) = 1 - pmfProb μ E := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := E)
    (f := fun ω => pmfWeight μ ω)
  rw [← pmfProb_eq_sum_filter, ← pmfProb_eq_sum_filter] at hsplit
  rw [pmfWeight_sum_eq_one μ] at hsplit
  linarith

/-- The probability of a union is at most the sum of the probabilities. -/
theorem pmfProb_or_le {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E F : Ω → Prop) :
    pmfProb μ (fun ω => E ω ∨ F ω) ≤ pmfProb μ E + pmfProb μ F := by
  classical
  simp only [pmfProb_eq_sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω <;> by_cases hF : F ω <;>
    simp [hE, hF, pmfWeight_nonneg μ ω]

/-- Exact decomposition of the complement of a conjunction. -/
theorem pmfProb_not_and {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E F : Ω → Prop) :
    pmfProb μ (fun ω => ¬ (E ω ∧ F ω)) =
      pmfProb μ (fun ω => ¬ E ω) + pmfProb μ (fun ω => E ω ∧ ¬ F ω) := by
  classical
  simp only [pmfProb_eq_sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF]

/-! ## 2. `UnconditionedMeanLower` from the pool first moment -/

/-- Summing the pool per-prime first moment over a dyad.  This is the exact
finite-sum step from `PoolCoverageInputs.hmean` to a dyad aggregate. -/
theorem pmfExpect_dyadSum_ge {Ω ι : Type*} [Fintype Ω] (μ : PMF Ω)
    (Zp : ι → Ω → ℝ) (τ : ι → ℝ) (s : Finset ι) {a : ℝ}
    (hmean : ∀ p ∈ s, a * τ p ≤ pmfExpect μ (Zp p)) :
    a * (∑ p ∈ s, τ p) ≤ pmfExpect μ (fun ω => ∑ p ∈ s, Zp p ω) := by
  rw [pmfExpect_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun p hp => hmean p hp

/-- `PoolCoverageInputs.hmean`, restricted to one used dyad and one fixed
rational-good cutoff, is a per-prime first-moment lower bound. -/
theorem hmean_of_poolCoverage {Ω ι P : Type*} [Fintype Ω] [DecidableEq P]
    (I : Cogentic.RandomizedEpochPool.PoolCoverageInputs Ω ι P)
    (d : ι) (hd : d ∈ I.dyads) (a : ℝ) (ha : a ≤ I.a)
    (hgood : ∀ p ∈ I.dyad d, I.err_rat p ≤ I.θ_rat) :
    ∀ p ∈ I.dyad d, a * I.τ p ≤ pmfExpect I.μ (I.Z p) := by
  intro p hp
  have hτ : 0 ≤ I.τ p := (I.hτ d hd p hp).le
  exact (mul_le_mul_of_nonneg_right ha hτ).trans (I.hmean d hd p hp (hgood p hp))

/-- Per-scale version of `hmean_of_poolCoverage`: a family of pool inputs whose
dyad first moments are bounded below at every scale gives the eventual
per-prime hypothesis consumed by `PairMeanData.pool_hmean`. -/
theorem pool_hmean_eventually_of_poolCoverage {Ω ι P : Type*} [Fintype Ω]
    [DecidableEq P] (I : ℕ → Cogentic.RandomizedEpochPool.PoolCoverageInputs Ω ι P)
    (d : ℕ → ι) (hd : ∀ n, d n ∈ (I n).dyads) (a : ℝ) (ha : ∀ n, a ≤ (I n).a)
    (hgood : ∀ n p, p ∈ (I n).dyad (d n) → (I n).err_rat p ≤ (I n).θ_rat) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ (I n).dyad (d n),
      a * (I n).τ p ≤ pmfExpect ((I n).μ) ((I n).Z p) :=
  Eventually.of_forall fun n =>
    hmean_of_poolCoverage (I n) (d n) (hd n) a (ha n) (hgood n)

/-- **Ordinary mean from the pool first moment.**  If the aggregate normalized
height is the dyad sum divided by a deterministic reference `norm`, the per-prime
pool means are at least `a · τ_p`, and the normalized reference mass is at least
`a₀`, then the ordinary mean is at least `a₀`.  The dyad, the per-prime
references and the normalization are all explicit. -/
theorem unconditionedMeanLower_of_poolAggregate {Ω ι : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (Z : ℕ → Ω → ℝ) {a a₀ : ℝ}
    (τ : ℕ → ι → ℝ) (s : ℕ → Finset ι) (Zp : ℕ → ι → Ω → ℝ)
    (norm : ℕ → ℝ)
    (norm_pos : ∀ᶠ n : ℕ in atTop, 0 < norm n)
    (hmean : ∀ᶠ n : ℕ in atTop, ∀ p ∈ s n, a * τ n p ≤ pmfExpect (μ n) (Zp n p))
    (Z_eq : ∀ᶠ n : ℕ in atTop, ∀ ω, Z n ω = (∑ p ∈ s n, Zp n p ω) / norm n)
    (ref_le : ∀ᶠ n : ℕ in atTop, a₀ ≤ a * (∑ p ∈ s n, τ n p) / norm n) :
    UnconditionedMeanLower μ Z a₀ := by
  unfold UnconditionedMeanLower
  filter_upwards [hmean, norm_pos, Z_eq, ref_le] with n hmean' hpos hZ hnorm
  have hdyad : a * (∑ p ∈ s n, τ n p) ≤
      pmfExpect (μ n) (fun ω => ∑ p ∈ s n, Zp n p ω) :=
    pmfExpect_dyadSum_ge (μ n) (Zp n) (τ n) (s n) fun p hp => hmean' p hp
  have hcongr : pmfExpect (μ n) (Z n) =
      pmfExpect (μ n) (fun ω => (∑ p ∈ s n, Zp n p ω) / norm n) := by
    unfold pmfExpect
    apply Finset.sum_congr rfl
    intro ω _
    rw [hZ ω]
  rw [hcongr, pmfExpect_div_const]
  calc a₀ ≤ a * (∑ p ∈ s n, τ n p) / norm n := hnorm
    _ ≤ pmfExpect (μ n) (fun ω => ∑ p ∈ s n, Zp n p ω) / norm n :=
        div_le_div_of_nonneg_right hdyad hpos.le

/-- **The `τ = 1` single-prime specialization.**  This is the literal shape in
which `PoolCoverageInputs.hmean` is quoted in the pool note. -/
theorem unconditionedMeanLower_of_poolPrime {Ω ι P : Type*} [Fintype Ω]
    [DecidableEq P] (I : Cogentic.RandomizedEpochPool.PoolCoverageInputs Ω ι P)
    (d : ι) (hd : d ∈ I.dyads) (p : P) (hp : p ∈ I.dyad d)
    (hgood : I.err_rat p ≤ I.θ_rat) (hτ : I.τ p = 1) :
    UnconditionedMeanLower (fun _ => I.μ) (fun _ => I.Z p) I.a := by
  unfold UnconditionedMeanLower
  filter_upwards with n
  simpa [hτ] using I.hmean d hd p hp hgood

/-! ## 3. `OffEventHeightUpper` from a deterministic height/profile cut -/

/-- The deterministic inputs behind the off-event height cut: a nonnegative raw
top count bounded by `D^{c_H}`, a positive strip profile bounded below by
`D^{-c_P}`, and `Z = H/B`. -/
structure HeightDivCut (Ω : Type*) where
  /-- Raw top count. -/
  H : ℕ → Ω → ℝ
  /-- Normalizing strip profile. -/
  B : ℕ → Ω → ℝ
  /-- Height exponent. -/
  cH : ℝ
  /-- Profile exponent. -/
  cP : ℝ
  H_nonneg : ∀ n ω, 0 ≤ H n ω
  H_le : ∀ᶠ n : ℕ in atTop, ∀ ω, H n ω ≤ Real.exp (cH * scale n)
  B_ge : ∀ᶠ n : ℕ in atTop, ∀ ω, Real.exp (-cP * scale n) ≤ B n ω

/-- **The off-event height cut is a deterministic division estimate.**  If
`Z = H/B`, `H ≤ D^{c_H}` and `B ≥ D^{-c_P}`, then `Z ≤ D^{c_H+c_P}` at every
point, hence off any event. -/
theorem offEventHeightUpper_of_heightDiv {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (S : HeightDivCut Ω)
    (hZ : ∀ᶠ n : ℕ in atTop, ∀ ω, Z n ω = S.H n ω / S.B n ω) :
    OffEventHeightUpper μ E Z (S.cH + S.cP) := by
  unfold OffEventHeightUpper
  filter_upwards [S.H_le, S.B_ge, hZ] with n hH hB hZn
  intro ω _
  rw [hZn ω]
  have hHnn : 0 ≤ S.H n ω := S.H_nonneg n ω
  have hHle : S.H n ω ≤ Real.exp (S.cH * scale n) := hH ω
  have hBle : Real.exp (-S.cP * scale n) ≤ S.B n ω := hB ω
  have hdiv : S.H n ω / S.B n ω ≤
      Real.exp (S.cH * scale n) / Real.exp (-S.cP * scale n) :=
    div_le_div₀ (Real.exp_pos _).le hHle (Real.exp_pos _) hBle
  have heq : Real.exp (S.cH * scale n) / Real.exp (-S.cP * scale n) =
      Real.exp ((S.cH + S.cP) * scale n) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  exact hdiv.trans (le_of_eq heq)

/-- **The height cut can be bought for free by enlarging the event.**  If an
event has the required mass lower and complement upper bounds, then adjoining the
set `{Z > D^{c_V}}` preserves both bounds and makes `OffEventHeightUpper` hold
verbatim.  Thus the only genuine complement content is the mass bound, not the
pointwise height cut. -/
theorem exists_offEventHeightUpper_of_complement {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E₀ : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) {cE cB cV : ℝ}
    (hE : EventMassLower μ E₀ cE)
    (hC : ComplementMassUpper μ E₀ cB) :
    ∃ E : ℕ → Ω → Prop,
      EventMassLower μ E cE ∧ ComplementMassUpper μ E cB ∧
        OffEventHeightUpper μ E Z cV := by
  classical
  refine ⟨fun n ω => E₀ n ω ∨ Real.exp (cV * scale n) < Z n ω, ?_, ?_, ?_⟩
  · unfold EventMassLower at *
    filter_upwards [hE] with n hn
    exact hn.trans (pmfProb_mono (μ n) fun ω hω => Or.inl hω)
  · unfold ComplementMassUpper at *
    filter_upwards [hC] with n hn
    exact (pmfProb_mono (μ n) fun ω hω => by
      intro hconj
      exact hω (Or.inl hconj)).trans hn
  · unfold OffEventHeightUpper
    filter_upwards with n ω hω
    exact le_of_not_gt fun hgt => hω (Or.inr hgt)

/-! ## 4. `ComplementMassUpper` as a co-large-event statement -/

/-- **Exact co-large form.**  The complement has mass at most `D^{-c}` iff the
event itself carries all but `D^{-c}` of the mass. -/
theorem complementMassUpper_iff_eventMass_ge {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) (c : ℝ) :
    ComplementMassUpper μ E c ↔
      ∀ᶠ n : ℕ in atTop, 1 - Real.exp (-c * scale n) ≤ pmfProb (μ n) (E n) := by
  unfold ComplementMassUpper
  constructor
  · intro h
    filter_upwards [h] with n hn
    rw [pmfProb_compl] at hn
    linarith
  · intro h
    filter_upwards [h] with n hn
    rw [pmfProb_compl]
    linarith

/-- A mass bound on an explicit bad event transfers to any event whose
complement is contained in that bad event. -/
theorem complementMassUpper_of_subset_bad {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E Bad : ℕ → Ω → Prop) {c : ℝ}
    (hsub : ∀ᶠ n : ℕ in atTop, ∀ ω, ¬ E n ω → Bad n ω)
    (hbad : ∀ᶠ n : ℕ in atTop, pmfProb (μ n) (Bad n) ≤ Real.exp (-c * scale n)) :
    ComplementMassUpper μ E c := by
  unfold ComplementMassUpper
  filter_upwards [hsub, hbad] with n hsub' hbad'
  exact (pmfProb_mono (μ n) fun ω hω => hsub' ω hω).trans hbad'

/-- Union bound for complement masses: the complement of an intersection is
bounded by the two complement masses, at the cost of one unit of exponent. -/
theorem complementMassUpper_and {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E₁ E₂ : ℕ → Ω → Prop) {c₁ c₂ cB : ℝ}
    (h₁ : ComplementMassUpper μ E₁ c₁) (h₂ : ComplementMassUpper μ E₂ c₂)
    (hc₁ : cB + 1 ≤ c₁) (hc₂ : cB + 1 ≤ c₂) :
    ComplementMassUpper μ (fun n ω => E₁ n ω ∧ E₂ n ω) cB := by
  unfold ComplementMassUpper at *
  filter_upwards [h₁, h₂, scale_grows.eventually_ge_atTop (Real.log 2)]
    with n h₁' h₂' hH
  have hunion : pmfProb (μ n) (fun ω => ¬ (E₁ n ω ∧ E₂ n ω)) ≤
      pmfProb (μ n) (fun ω => ¬ E₁ n ω) + pmfProb (μ n) (fun ω => ¬ E₂ n ω) :=
    (pmfProb_mono (μ n) fun ω hω => by tauto).trans
      (pmfProb_or_le (μ n) (fun ω => ¬ E₁ n ω) (fun ω => ¬ E₂ n ω))
  have hH0 : 0 ≤ scale n := le_trans (Real.log_nonneg (by norm_num)) hH
  have hmul₁ : (cB + 1) * scale n ≤ c₁ * scale n :=
    mul_le_mul_of_nonneg_right hc₁ hH0
  have hmul₂ : (cB + 1) * scale n ≤ c₂ * scale n :=
    mul_le_mul_of_nonneg_right hc₂ hH0
  have hle₁ : Real.exp (-c₁ * scale n) ≤ Real.exp (-(cB + 1) * scale n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hle₂ : Real.exp (-c₂ * scale n) ≤ Real.exp (-(cB + 1) * scale n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have htwo : (2 : ℝ) ≤ Real.exp (scale n) := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (scale n) := Real.exp_le_exp.mpr hH
  calc pmfProb (μ n) (fun ω => ¬ (E₁ n ω ∧ E₂ n ω))
      ≤ pmfProb (μ n) (fun ω => ¬ E₁ n ω) + pmfProb (μ n) (fun ω => ¬ E₂ n ω) :=
        hunion
    _ ≤ Real.exp (-c₁ * scale n) + Real.exp (-c₂ * scale n) := add_le_add h₁' h₂'
    _ ≤ Real.exp (-(cB + 1) * scale n) + Real.exp (-(cB + 1) * scale n) :=
        add_le_add hle₁ hle₂
    _ = 2 * Real.exp (-(cB + 1) * scale n) := by ring
    _ ≤ Real.exp (scale n) * Real.exp (-(cB + 1) * scale n) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-cB * scale n) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- A subexponential bound on the complement probability is exactly a
`ComplementMassUpper` at every positive exponent.  This is the form in which the
pool miss mass and the dyadic trimming deficits are quoted. -/
theorem complementMassUpper_of_subexpLoss {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) {c : ℝ} (hc : 0 < c)
    (h : SubexpLoss fun n => pmfProb (μ n) (fun ω => ¬ E n ω)) :
    ComplementMassUpper μ E c :=
  h c hc

/-- A subexponential bound on the mass of an explicit bad event, in the
`SubexpLoss` vocabulary. -/
theorem eventually_bad_mass_le_of_subexpLoss {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (Bad : ℕ → Ω → Prop) {c : ℝ} (hc : 0 < c)
    (h : SubexpLoss fun n => pmfProb (μ n) (Bad n)) :
    ∀ᶠ n : ℕ in atTop, pmfProb (μ n) (Bad n) ≤ Real.exp (-c * scale n) :=
  h c hc

/-- The primitive pair-complement estimate: rational-good failure mass plus
incoming-root failure mass on rational-good environments. -/
def PairComplementMassUpper {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    pmfProb (μ n) (fun ω => ¬ good n ω) +
      pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω) ≤
        Real.exp (-c * scale n)

/-- The complement of the pair event is exactly the sum of the two primitive
failure masses. -/
theorem complementMassUpper_pairEvent_iff_pairComplement {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {c : ℝ} :
    ComplementMassUpper μ (fun n => pairEvent good childRoot n) c ↔
      PairComplementMassUpper μ good childRoot c := by
  have hpt : ∀ n : ℕ,
      (pmfProb (μ n) (fun ω => ¬ pairEvent good childRoot n ω) ≤
        Real.exp (-c * scale n)) ↔
      (pmfProb (μ n) (fun ω => ¬ good n ω) +
        pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω) ≤
          Real.exp (-c * scale n)) := by
    intro n
    change (pmfProb (μ n) (fun ω => ¬ (good n ω ∧ childRoot n ω)) ≤
        Real.exp (-c * scale n)) ↔
      (pmfProb (μ n) (fun ω => ¬ good n ω) +
        pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω) ≤
          Real.exp (-c * scale n))
    rw [pmfProb_not_and]
  unfold ComplementMassUpper PairComplementMassUpper
  constructor
  · intro h
    filter_upwards [h] with n hn
    exact (hpt n).mp hn
  · intro h
    filter_upwards [h] with n hn
    exact (hpt n).mpr hn

/-- **Two primitive complement masses.**  A subexponential bound on `Pr(¬g)` and
on the incoming exceptional mass `Pr(g ∧ ¬R_{q,s})` gives the pair complement
bound, losing one unit of exponent to the union bound. -/
theorem pairComplementMassUpper_of_components {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (good childRoot : ℕ → Ω → Prop) {cG cR cB : ℝ}
    (hG : ComplementMassUpper μ good cG)
    (hR : ∀ᶠ n : ℕ in atTop,
      pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω) ≤
        Real.exp (-cR * scale n))
    (hcG : cB + 1 ≤ cG) (hcR : cB + 1 ≤ cR) :
    PairComplementMassUpper μ good childRoot cB := by
  unfold PairComplementMassUpper ComplementMassUpper at *
  filter_upwards [hG, hR, scale_grows.eventually_ge_atTop (Real.log 2)]
    with n hG' hR' hH
  have hH0 : 0 ≤ scale n := le_trans (Real.log_nonneg (by norm_num)) hH
  have hmulG : (cB + 1) * scale n ≤ cG * scale n :=
    mul_le_mul_of_nonneg_right hcG hH0
  have hmulR : (cB + 1) * scale n ≤ cR * scale n :=
    mul_le_mul_of_nonneg_right hcR hH0
  have hleG : Real.exp (-cG * scale n) ≤ Real.exp (-(cB + 1) * scale n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hleR : Real.exp (-cR * scale n) ≤ Real.exp (-(cB + 1) * scale n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have htwo : (2 : ℝ) ≤ Real.exp (scale n) := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (scale n) := Real.exp_le_exp.mpr hH
  calc pmfProb (μ n) (fun ω => ¬ good n ω) +
        pmfProb (μ n) (fun ω => good n ω ∧ ¬ childRoot n ω)
      ≤ Real.exp (-cG * scale n) + Real.exp (-cR * scale n) := add_le_add hG' hR'
    _ ≤ Real.exp (-(cB + 1) * scale n) + Real.exp (-(cB + 1) * scale n) :=
        add_le_add hleG hleR
    _ = 2 * Real.exp (-(cB + 1) * scale n) := by ring
    _ ≤ Real.exp (scale n) * Real.exp (-(cB + 1) * scale n) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-cB * scale n) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ## 5. The reduced mean bundle -/

/-- The three reduced ordinary-law inputs of `PairConditionedData`.

* `pool_hmean` is exactly `PoolCoverageInputs.hmean` summed over a dyad, with the
  aggregation `Z_eq` and reference comparison `ref_le` kept explicit.
* `H_le` and `B_ge` are the deterministic height/profile cut.
* `bad_mass` is a subexponential bound on an explicit bad event containing the
  complement of the conditioning event; `compl_subset` is the only structural
  link to the event. -/
structure PairMeanData (Ω ι : Type*) [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ)
    (cV cB a₀ : ℝ) where
  /- Pool first-moment data. -/
  aPool : ℝ
  aPool_nonneg : 0 ≤ aPool
  τ : ℕ → ι → ℝ
  s : ℕ → Finset ι
  Zp : ℕ → ι → Ω → ℝ
  norm : ℕ → ℝ
  norm_pos : ∀ᶠ n : ℕ in atTop, 0 < norm n
  pool_hmean : ∀ᶠ n : ℕ in atTop, ∀ p ∈ s n,
    aPool * τ n p ≤ pmfExpect (μ n) (Zp n p)
  Z_eq : ∀ᶠ n : ℕ in atTop, ∀ ω, Z n ω = (∑ p ∈ s n, Zp n p ω) / norm n
  ref_le : ∀ᶠ n : ℕ in atTop,
    a₀ ≤ aPool * (∑ p ∈ s n, τ n p) / norm n
  /- Deterministic height/profile cut. -/
  H : ℕ → Ω → ℝ
  B : ℕ → Ω → ℝ
  cH : ℝ
  cP : ℝ
  cV_eq : cV = cH + cP
  H_nonneg : ∀ n ω, 0 ≤ H n ω
  H_le : ∀ᶠ n : ℕ in atTop, ∀ ω, H n ω ≤ Real.exp (cH * scale n)
  B_ge : ∀ᶠ n : ℕ in atTop, ∀ ω, Real.exp (-cP * scale n) ≤ B n ω
  Z_div : ∀ᶠ n : ℕ in atTop, ∀ ω, Z n ω = H n ω / B n ω
  /- Complement mass. -/
  Bad : ℕ → Ω → Prop
  bad_mass : ∀ᶠ n : ℕ in atTop,
    pmfProb (μ n) (Bad n) ≤ Real.exp (-cB * scale n)
  compl_subset : ∀ᶠ n : ℕ in atTop, ∀ ω, ¬ E n ω → Bad n ω

namespace PairMeanData

variable {Ω ι : Type*} [Fintype Ω] {μ : ℕ → PMF Ω} {E : ℕ → Ω → Prop}
  {Z : ℕ → Ω → ℝ} {cV cB a₀ : ℝ}

/-- The ordinary mean, from the pool first moment. -/
theorem unconditionedMeanLower (S : PairMeanData Ω ι μ E Z cV cB a₀) :
    UnconditionedMeanLower μ Z a₀ :=
  unconditionedMeanLower_of_poolAggregate μ Z S.τ S.s S.Zp S.norm S.norm_pos
    S.pool_hmean S.Z_eq S.ref_le

/-- The off-event height cut, from the deterministic height/profile bound. -/
theorem offEventHeightUpper (S : PairMeanData Ω ι μ E Z cV cB a₀) :
    OffEventHeightUpper μ E Z cV := by
  have hcut := offEventHeightUpper_of_heightDiv μ E Z
    { H := S.H, B := S.B, cH := S.cH, cP := S.cP, H_nonneg := S.H_nonneg,
      H_le := S.H_le, B_ge := S.B_ge } S.Z_div
  simpa [S.cV_eq] using hcut

/-- The complement mass bound, from the explicit bad event. -/
theorem complementMassUpper (S : PairMeanData Ω ι μ E Z cV cB a₀) :
    ComplementMassUpper μ E cB :=
  complementMassUpper_of_subset_bad μ E S.Bad S.compl_subset S.bad_mass

end PairMeanData

/-! ## 6. Reassembly into `PairConditionedData` -/

/-- All fields of `PairConditionedData` except the three ordinary-law inputs
that `PairMeanData` supplies. -/
structure PairConditionedBase (Ω : Type*) [Fintype Ω] where
  μ : ℕ → PMF Ω
  good : ℕ → Ω → Prop
  childRoot : ℕ → Ω → Prop
  Z : ℕ → Ω → ℝ
  a : ℝ
  a_pos : 0 < a
  a₀ : ℝ
  a₀_pos : 0 < a₀
  a_le : a ≤ a₀ / 2
  cU : ℝ
  cU_nonneg : 0 ≤ cU
  cE : ℝ
  cE_nonneg : 0 ≤ cE
  cV : ℝ
  cB : ℝ
  cV_lt_cB : cV < cB
  cDyad : ℝ
  cDyad_nonneg : 0 ≤ cDyad
  dyadCard : ℕ → ℕ
  dyadCard_le : ∀ᶠ n : ℕ in atTop,
    (dyadCard n : ℝ) ≤ Real.exp (cDyad * scale n)
  poolSize : ℕ → ℕ
  poolSize_ge : ∀ᶠ n : ℕ in atTop,
    Real.exp ((cU + cE + cDyad + 2) * scale n) ≤ (poolSize n : ℝ)
  event_pos : ∀ n, 0 < pmfProb (μ n) (pairEvent good childRoot n)
  uncond_two_point : UnconditionedTwoPoint μ Z cU
  event_mass_lower : EventMassLower μ (pairEvent good childRoot) cE

namespace PairConditionedBase

variable {Ω : Type*} [Fintype Ω]

/-- **Reduction to `PairConditionedData`.**  The parent bundle is reassembled
from the remaining fields and the three reduced ordinary-law inputs. -/
noncomputable def toPairConditionedData {ι : Type*} (B : PairConditionedBase Ω)
    (M : PairMeanData Ω ι B.μ (fun n => pairEvent B.good B.childRoot n) B.Z
      B.cV B.cB B.a₀) : PairConditionedData Ω where
  μ := B.μ
  good := B.good
  childRoot := B.childRoot
  Z := B.Z
  a := B.a
  a_pos := B.a_pos
  a₀ := B.a₀
  a₀_pos := B.a₀_pos
  a_le := B.a_le
  cU := B.cU
  cU_nonneg := B.cU_nonneg
  cE := B.cE
  cE_nonneg := B.cE_nonneg
  cV := B.cV
  cB := B.cB
  cV_lt_cB := B.cV_lt_cB
  cDyad := B.cDyad
  cDyad_nonneg := B.cDyad_nonneg
  dyadCard := B.dyadCard
  dyadCard_le := B.dyadCard_le
  poolSize := B.poolSize
  poolSize_ge := B.poolSize_ge
  event_pos := B.event_pos
  uncond_two_point := B.uncond_two_point
  event_mass_lower := B.event_mass_lower
  uncond_mean_lower := M.unconditionedMeanLower
  off_event_height := M.offEventHeightUpper
  complement_mass_upper := M.complementMassUpper

/-- The reassembled bundle realizes the reduced `PairData` and therefore inherits
the pool miss estimate. -/
theorem pairLoss_subexp {ι : Type*} (B : PairConditionedBase Ω)
    (M : PairMeanData Ω ι B.μ (fun n => pairEvent B.good B.childRoot n) B.Z
      B.cV B.cB B.a₀) :
    SubexpLoss (B.toPairConditionedData M).toPairData.loss :=
  (B.toPairConditionedData M).toPairData.loss_subexp

end PairConditionedBase

/-! ## Axiom audit -/

#print axioms pmfExpect_sum
#print axioms pmfExpect_div_const
#print axioms pmfProb_compl
#print axioms pmfProb_or_le
#print axioms pmfProb_not_and
#print axioms pmfExpect_dyadSum_ge
#print axioms hmean_of_poolCoverage
#print axioms pool_hmean_eventually_of_poolCoverage
#print axioms unconditionedMeanLower_of_poolAggregate
#print axioms unconditionedMeanLower_of_poolPrime
#print axioms offEventHeightUpper_of_heightDiv
#print axioms exists_offEventHeightUpper_of_complement
#print axioms complementMassUpper_iff_eventMass_ge
#print axioms complementMassUpper_of_subset_bad
#print axioms complementMassUpper_and
#print axioms complementMassUpper_of_subexpLoss
#print axioms eventually_bad_mass_le_of_subexpLoss
#print axioms complementMassUpper_pairEvent_iff_pairComplement
#print axioms pairComplementMassUpper_of_components
#print axioms PairMeanData.unconditionedMeanLower
#print axioms PairMeanData.offEventHeightUpper
#print axioms PairMeanData.complementMassUpper
#print axioms PairConditionedBase.toPairConditionedData
#print axioms PairConditionedBase.pairLoss_subexp

end Cogentic.RandomizedL20_4Mean
