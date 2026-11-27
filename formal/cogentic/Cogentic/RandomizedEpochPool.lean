import Cogentic.RandomizedFieldPoolDescent

/-!
# L17 Field-Pool Coverage Assembly (C5.a input)

This file packages the field-pool machinery of
`Cogentic.RandomizedFieldPoolDescent` into one auditable coverage theorem matching
blueprint L17:

* Paley–Zygmund first/second-moment lower bound (`pmf_paley_zygmund`);
* upper second-moment cut (`pmf_upper_cut_prob_le`);
* bad-child Markov cut (`pmf_bad_child_cut_prob_le`);
* their combination into a survivor event (`pmf_survivor_event_prob_ge`);
* the pointwise survivor ratio (`survivor_ratio_ge`);
* deterministic dyad trimming from dyad-average errors (`dyad_trimming_of_avg`);
* the polynomial field-pool union bound (`poolMissMass_le_card_mul_exp`,
  `pmf_trimmed_dyads_survivor_pool_coverage`).

`PoolCoverageInputs` records exactly the analytic and combinatorial hypotheses.  From it
we derive

* a cardinality bound on the trimmed (bad) primes of every used dyad,
* a lower bound on the retained fraction of every used dyad,
* a per-prime hit probability lower bound `a ^ 2 / (16 * M)`,
* the pool miss-mass bound `|AllGood| * (1 - q) ^ K ≤ |AllGood| * exp (-q * K)`, and
* the dyad-summed exponential bound
  `(∑ d, |Good d|) * exp (-(a ^ 2 / (16 * M)) * K)`.

The resulting `PoolCoverageInputs.coverage` theorem is intended to be consumed directly
as the C5.a field of a future `EpochAnalyticInputs` structure.  No analytic leaf is
reproved here; every quantitative step is delegated to the existing lemmas.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace Cogentic.RandomizedEpochPool

open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedPoolCoverage

variable {Ω ι P : Type*} [Fintype Ω] [DecidableEq P]

/-- Hypotheses feeding the L17 field-pool coverage theorem.

The first-moment hypothesis is `hmean`, the second-moment hypothesis is `hsecond`, both
only required on primes of a used dyad whose rational error is at most `θ_rat`.  The
bad-child Markov hypothesis enters through `hsum_bad`, the dyad trimming hypothesis
through `hsum_rat` and `hsum_bad`.  The pool union bound is applied in the conclusions
below. -/
structure PoolCoverageInputs (Ω ι P : Type*) [Fintype Ω] [DecidableEq P] where
  /-- The finite probability space of one field-pool draw. -/
  μ : PMF Ω
  /-- Number of independent pool draws. -/
  K : ℕ
  /-- The set of used dyads. -/
  dyads : Finset ι
  /-- The primes belonging to each used dyad. -/
  dyad : ι → Finset P
  /-- First-moment field-pool counting variable. -/
  Z : P → Ω → ℝ
  /-- Bad-child incidence variable. -/
  B : P → Ω → ℝ
  /-- Reference counting scale. -/
  τ : P → ℝ
  /-- Per-prime rational-good error. -/
  err_rat : P → ℝ
  /-- First-moment constant. -/
  a : ℝ
  /-- Second-moment constant. -/
  M : ℝ
  /-- Average rational-good error budget per dyad. -/
  δ_rat : ℝ
  /-- Average bad-child error budget per dyad. -/
  δ_bad : ℝ
  /-- Rational-good cutoff. -/
  θ_rat : ℝ
  ha : 0 < a
  hM : 0 < M
  hθ_rat : 0 < θ_rat
  hτ : ∀ d ∈ dyads, ∀ p ∈ dyad d, 0 < τ p
  hB : ∀ d ∈ dyads, ∀ p ∈ dyad d, ∀ ω, 0 ≤ B p ω
  herr_rat_nn : ∀ d ∈ dyads, ∀ p ∈ dyad d, 0 ≤ err_rat p
  hsum_rat : ∀ d ∈ dyads, ∑ p ∈ dyad d, err_rat p ≤ δ_rat * ((dyad d).card : ℝ)
  hsum_bad : ∀ d ∈ dyads,
    ∑ p ∈ dyad d, pmfExpect μ (B p) / τ p ≤ δ_bad * ((dyad d).card : ℝ)
  hmean : ∀ d ∈ dyads, ∀ p ∈ dyad d, err_rat p ≤ θ_rat →
    a * τ p ≤ pmfExpect μ (Z p)
  hsecond : ∀ d ∈ dyads, ∀ p ∈ dyad d, err_rat p ≤ θ_rat →
    pmfExpect μ (fun ω => Z p ω ^ 2) ≤ M * τ p ^ 2

namespace PoolCoverageInputs

variable (I : PoolCoverageInputs Ω ι P)

/-- The canonical bad-child cutoff `a ^ 3 / (64 * M)`. -/
noncomputable def θ_bad : ℝ := I.a ^ 3 / (64 * I.M)

/-- The canonical upper cut `sqrt (8 * M ^ 2 / a ^ 2)`. -/
noncomputable def U : ℝ := Real.sqrt (8 * I.M ^ 2 / I.a ^ 2)

/-- Per-prime averaged bad-child error `E[B_p] / τ_p`. -/
noncomputable def err_bad (p : P) : ℝ := pmfExpect I.μ (I.B p) / I.τ p

/-- Deterministic trimmed set of a used dyad. -/
noncomputable def Bad (d : ι) : Finset P :=
  badDyadPrimes (I.dyad d) I.err_rat I.err_bad I.θ_rat I.θ_bad

/-- Retained (non-trimmed) primes of a used dyad. -/
noncomputable def Good (d : ι) : Finset P := I.dyad d \ I.Bad d

/-- All retained primes across all used dyads. -/
noncomputable def AllGood : Finset P := I.dyads.biUnion I.Good

/-- The L17 hit event for a prime: survivor lower bound, upper cut, and ratio bound. -/
noncomputable def hit (p : P) (ω : Ω) : Prop :=
  I.a * I.τ p / 4 ≤ I.Z p ω - I.B p ω ∧
    I.Z p ω ≤ I.U * I.τ p ∧
    I.a / (4 * I.U) ≤ (I.Z p ω - I.B p ω) / I.Z p ω

theorem θ_bad_pos : 0 < I.θ_bad := by
  unfold θ_bad
  exact div_pos (pow_pos I.ha 3) (mul_pos (by norm_num) I.hM)

theorem U_pos : 0 < I.U := by
  unfold U
  apply Real.sqrt_pos.mpr
  have ha2 : 0 < I.a ^ 2 := pow_pos I.ha 2
  have hM2 : 0 < I.M ^ 2 := pow_pos I.hM 2
  exact div_pos (mul_pos (by norm_num) hM2) ha2

theorem U_sq : I.U ^ 2 = 8 * I.M ^ 2 / I.a ^ 2 := by
  unfold U
  have ha2 : 0 < I.a ^ 2 := pow_pos I.ha 2
  exact Real.sq_sqrt (le_of_lt (div_pos (mul_pos (by norm_num) (pow_pos I.hM 2)) ha2))

theorem err_bad_nonneg (d : ι) (hd : d ∈ I.dyads) {p : P} (hp : p ∈ I.dyad d) :
    0 ≤ I.err_bad p := by
  unfold err_bad
  exact div_nonneg
    (Finset.sum_nonneg fun ω _ =>
      mul_nonneg (pmfWeight_nonneg I.μ ω) (I.hB d hd p hp ω))
    (I.hτ d hd p hp).le

/-! ## Per-prime moment chain -/

/-- The three moment bounds underlying the survivor event: Paley–Zygmund lower bound,
upper second-moment cut, and bad-child Markov cut. -/
theorem moment_bounds (d : ι) (hd : d ∈ I.dyads) {p : P} (hp : p ∈ I.dyad d)
    (hrat : I.err_rat p ≤ I.θ_rat) {U ε : ℝ} (hU : 0 < U)
    (hbad : pmfExpect I.μ (I.B p) ≤ ε * I.τ p) :
    I.a ^ 2 / (4 * I.M) ≤
        pmfProb I.μ (fun ω => I.a * I.τ p / 2 ≤ I.Z p ω) ∧
      pmfProb I.μ (fun ω => U * I.τ p < I.Z p ω) ≤ I.M / U ^ 2 ∧
      pmfProb I.μ (fun ω => I.a * I.τ p / 4 < I.B p ω) ≤ 4 * ε / I.a := by
  have hτp := I.hτ d hd p hp
  refine ⟨?_, ?_, ?_⟩
  · exact pmf_paley_zygmund (μ := I.μ) (Z := I.Z p) (a := I.a) (M := I.M)
      (τ := I.τ p) I.ha I.hM hτp (I.hmean d hd p hp hrat) (I.hsecond d hd p hp hrat)
  · exact pmf_upper_cut_prob_le (μ := I.μ) (Z := I.Z p) (M := I.M) (τ := I.τ p)
      (U := U) hτp hU (I.hsecond d hd p hp hrat)
  · exact pmf_bad_child_cut_prob_le (μ := I.μ) (B := I.B p) (a := I.a) (τ := I.τ p)
      (ε := ε) I.ha hτp (I.hB d hd p hp) hbad

/-- The combined survivor-event probability bound, upgraded to the L17 hit event by the
pointwise survivor ratio. -/
theorem survivor_prob_ge (d : ι) (hd : d ∈ I.dyads) {p : P} (hp : p ∈ I.dyad d)
    (hrat : I.err_rat p ≤ I.θ_rat) {ε : ℝ}
    (hbad : pmfExpect I.μ (I.B p) ≤ ε * I.τ p) :
    I.a ^ 2 / (4 * I.M) - I.M / I.U ^ 2 - 4 * ε / I.a ≤
      pmfProb I.μ (I.hit p) := by
  have hτp := I.hτ d hd p hp
  have hU := I.U_pos
  have hraw := pmf_survivor_event_prob_ge (μ := I.μ) (Z := I.Z p) (B := I.B p)
    (a := I.a) (M := I.M) (τ := I.τ p) (U := I.U) (ε := ε)
    I.ha I.hM hτp hU (I.hB d hd p hp) (I.hmean d hd p hp hrat)
    (I.hsecond d hd p hp hrat) hbad
  refine hraw.trans (pmfProb_mono I.μ ?_)
  intro ω hω
  exact ⟨hω.1, hω.2,
    (survivor_ratio_ge I.ha hτp hU (I.hB d hd p hp ω) hω.1 hω.2).2⟩

/-- On the hit event the survivor ratio is positive and bounded below. -/
theorem hit_ratio (d : ι) (hd : d ∈ I.dyads) {p : P} (hp : p ∈ I.dyad d) {ω : Ω}
    (hω : I.hit p ω) :
    0 < I.Z p ω ∧ I.a / (4 * I.U) ≤ (I.Z p ω - I.B p ω) / I.Z p ω :=
  survivor_ratio_ge I.ha (I.hτ d hd p hp) I.U_pos (I.hB d hd p hp ω) hω.1 hω.2.1

/-- Every retained prime is hit with probability at least `a ^ 2 / (16 * M)`. -/
theorem single_prime_hit_prob (d : ι) (hd : d ∈ I.dyads) {p : P}
    (hp : p ∈ I.Good d) :
    I.a ^ 2 / (16 * I.M) ≤ pmfProb I.μ (I.hit p) := by
  have hpJ : p ∈ I.dyad d := (Finset.mem_sdiff.mp hp).1
  have htrim : I.err_rat p ≤ I.θ_rat ∧ I.err_bad p ≤ I.θ_bad :=
    dyad_trimming_good (I.dyad d) I.err_rat I.err_bad I.θ_rat I.θ_bad hp
  have hτp := I.hτ d hd p hpJ
  have hbad_exp : pmfExpect I.μ (I.B p) ≤ I.θ_bad * I.τ p := by
    exact (div_le_iff₀ hτp).mp (by simpa only [err_bad] using htrim.2)
  have hcanon := (pmf_survivor_canonical (μ := I.μ) (Z := I.Z p) (B := I.B p)
    (a := I.a) (M := I.M) (τ := I.τ p) (ε := I.θ_bad)
    I.ha I.hM hτp (I.hB d hd p hpJ) (I.hmean d hd p hpJ htrim.1)
    (I.hsecond d hd p hpJ htrim.1) hbad_exp le_rfl).2
  exact hcanon

/-! ## Dyad trimming -/

/-- The average-form trimming hypothesis yields a deterministic bad subset of each used
dyad which removes at most the stated fraction and leaves both errors below their
cutoffs. -/
theorem exists_trimmed_dyad (d : ι) (hd : d ∈ I.dyads) (hne : (I.dyad d).Nonempty) :
    ∃ Bad ⊆ I.dyad d,
      (Bad.card : ℝ) ≤
          (I.δ_rat / I.θ_rat + I.δ_bad / I.θ_bad) * ((I.dyad d).card : ℝ) ∧
      ∀ p ∈ I.dyad d \ Bad,
        I.err_rat p ≤ I.θ_rat ∧ I.err_bad p ≤ I.θ_bad := by
  have hcard : (0 : ℝ) < ((I.dyad d).card : ℝ) :=
    Nat.cast_pos.mpr hne.card_pos
  have havg_rat : (∑ p ∈ I.dyad d, I.err_rat p) / ((I.dyad d).card : ℝ) ≤ I.δ_rat :=
    (div_le_iff₀ hcard).mpr (I.hsum_rat d hd)
  have havg_bad : (∑ p ∈ I.dyad d, I.err_bad p) / ((I.dyad d).card : ℝ) ≤ I.δ_bad :=
    (div_le_iff₀ hcard).mpr (I.hsum_bad d hd)
  exact dyad_trimming_of_avg (I.dyad d) hne I.err_rat I.err_bad
    I.hθ_rat I.θ_bad_pos (I.herr_rat_nn d hd)
    (fun p hp => I.err_bad_nonneg d hd hp) havg_rat havg_bad

/-- Cardinality of the canonical trimmed set of each used dyad. -/
theorem bad_card_le (d : ι) (hd : d ∈ I.dyads) :
    ((I.Bad d).card : ℝ) ≤
      (I.δ_rat / I.θ_rat + I.δ_bad / I.θ_bad) * ((I.dyad d).card : ℝ) := by
  unfold Bad
  exact badDyadPrimes_card_le (I.dyad d) I.err_rat I.err_bad I.hθ_rat I.θ_bad_pos
    (I.herr_rat_nn d hd) (fun p hp => I.err_bad_nonneg d hd hp)
    (I.hsum_rat d hd) (I.hsum_bad d hd)

/-- Every used dyad retains at least the stated fraction of its primes. -/
theorem good_card_lower (d : ι) (hd : d ∈ I.dyads) :
    ((I.dyad d).card : ℝ) *
        (1 - (I.δ_rat / I.θ_rat + I.δ_bad / I.θ_bad)) ≤
      ((I.Good d).card : ℝ) := by
  have hsub : I.Bad d ⊆ I.dyad d := badDyadPrimes_subset _ _ _ _ _
  have hcard : ((I.Good d).card : ℝ) =
      ((I.dyad d).card : ℝ) - ((I.Bad d).card : ℝ) := by
    unfold Good
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  rw [hcard]
  nlinarith [I.bad_card_le d hd]

/-! ## Pool union bound -/

theorem allGood_hit_prob {p : P} (hp : p ∈ I.AllGood) :
    I.a ^ 2 / (16 * I.M) ≤ pmfProb I.μ (I.hit p) := by
  obtain ⟨d, hd, hpd⟩ := Finset.mem_biUnion.mp hp
  exact I.single_prime_hit_prob d hd hpd

/-- Cardinality form of the pool union bound: the probability that `K` independent
draws miss some retained prime is at most `|AllGood| * (1 - q) ^ K`, where
`q = a ^ 2 / (16 * M)`. -/
theorem missMass_le_card_mul :
    poolMissMass (pmfWeight I.μ) I.K I.AllGood I.hit ≤
      (I.AllGood.card : ℝ) * (1 - I.a ^ 2 / (16 * I.M)) ^ I.K :=
  (poolMissMass_le_card_mul_exp (pmfWeight I.μ) I.K I.AllGood I.hit
    (I.a ^ 2 / (16 * I.M)) (pmfWeight_nonneg I.μ) (pmfWeight_sum_eq_one I.μ)
    (fun p hp => by
      rw [← pmfProb_eq_eventMass]
      exact I.allGood_hit_prob hp)).1

/-- Exponential form of the pool union bound with the explicit cardinality factor. -/
theorem missMass_le_card_mul_exp :
    poolMissMass (pmfWeight I.μ) I.K I.AllGood I.hit ≤
      (I.AllGood.card : ℝ) *
        Real.exp (-(I.a ^ 2 / (16 * I.M)) * (I.K : ℝ)) := by
  obtain ⟨h1, h2⟩ := poolMissMass_le_card_mul_exp (pmfWeight I.μ) I.K I.AllGood I.hit
    (I.a ^ 2 / (16 * I.M)) (pmfWeight_nonneg I.μ) (pmfWeight_sum_eq_one I.μ)
    (fun p hp => by
      rw [← pmfProb_eq_eventMass]
      exact I.allGood_hit_prob hp)
  exact h1.trans h2

/-- The assembled L17 bound with the cardinality factor expanded over the used dyads. -/
theorem missMass_le_trimmed_exp :
    poolMissMass (pmfWeight I.μ) I.K I.AllGood I.hit ≤
      (∑ d ∈ I.dyads, ((I.Good d).card : ℝ)) *
        Real.exp (-(I.a ^ 2 / (16 * I.M)) * (I.K : ℝ)) := by
  have hmain := pmf_trimmed_dyads_survivor_pool_coverage (μ := I.μ) (K := I.K)
    (dyads := I.dyads) (dyad := I.dyad) (Z := I.Z) (B := I.B) (τ := I.τ)
    (err_rat := I.err_rat) (a := I.a) (M := I.M) (δ_rat := I.δ_rat)
    (δ_bad := I.δ_bad) (θ_rat := I.θ_rat)
    I.ha I.hM I.hθ_rat I.hτ I.hB I.herr_rat_nn I.hsum_rat I.hsum_bad I.hmean I.hsecond
  exact hmain.2

/-- Complete L17 coverage package: the trimmed fraction of every used dyad is bounded,
and the trimmed pool misses a retained prime with at most the stated exponential bound. -/
theorem coverage :
    (∀ d ∈ I.dyads,
        ((I.Bad d).card : ℝ) ≤
          (I.δ_rat / I.θ_rat + I.δ_bad / I.θ_bad) * ((I.dyad d).card : ℝ)) ∧
      poolMissMass (pmfWeight I.μ) I.K I.AllGood I.hit ≤
        (∑ d ∈ I.dyads, ((I.Good d).card : ℝ)) *
          Real.exp (-(I.a ^ 2 / (16 * I.M)) * (I.K : ℝ)) :=
  ⟨fun d hd => I.bad_card_le d hd, I.missMass_le_trimmed_exp⟩

end PoolCoverageInputs

#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.moment_bounds
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.survivor_prob_ge
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.single_prime_hit_prob
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.exists_trimmed_dyad
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.bad_card_le
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.good_card_lower
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.missMass_le_card_mul
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.missMass_le_card_mul_exp
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.missMass_le_trimmed_exp
#print axioms Cogentic.RandomizedEpochPool.PoolCoverageInputs.coverage

end Cogentic.RandomizedEpochPool
