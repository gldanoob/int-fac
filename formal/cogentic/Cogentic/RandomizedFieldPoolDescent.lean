import Cogentic.RandomizedPoolCoverage
import Cogentic.RandomizedSurvivorMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset Real
open scoped BigOperators ENNReal

namespace Cogentic.RandomizedFieldPoolDescent

/-!
# Polynomial Field-Pool Coverage, Survivor Moments, Multilevel Incidence, and H.4 Transfer

This file formalizes the quantitative probabilistic core of the polynomial field-pool and
public elliptic recognition transfer (KeyBreak Propositions G.10–G.12 and Lemma H.4):

1. Finite Paley–Zygmund + upper second-moment cut + bad-child Markov survivor probability
   and survivor-ratio lower bound over a finite probability space `μ : PMF Ω`.
2. Deterministic dyad exceptional-prime trimming by Markov's inequality across `p ∈ J`.
3. Polynomial field-pool union bound across all used dyads, connecting directly to
   `Cogentic.RandomizedPoolCoverage.poolMissMass_le_card_mul` with exponential tail bounds.
4. Multilevel bad-child incidence recurrences (both the KeyBreak G.11 linear internal
   recurrence with G.12 top square-root bound and the iterated square-root recurrence).
5. H.4 bounded-search opportunity transfer (incorporating the `3 / 4` elliptic recognition
   factor and survivor fraction) and union bound over a bounded-degree depth-`L` descent tree.
-/

/-! ## Section 1: Finite PMF Helpers and Paley–Zygmund Survivor Probability -/

section FinitePMFSurvivor

variable {Ω : Type*} [Fintype Ω]

/-- Real-valued probability mass of a single outcome under a finite `PMF`. -/
noncomputable def pmfWeight (μ : PMF Ω) (ω : Ω) : ℝ :=
  (μ ω).toReal

/-- Expectation of a real-valued random variable under a finite `PMF`. -/
noncomputable def pmfExpect (μ : PMF Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, pmfWeight μ ω * X ω

/-- Event probability under a finite `PMF`, matching `PMF.toOuterMeasure`. -/
noncomputable def pmfProb (μ : PMF Ω) (E : Ω → Prop) : ℝ :=
  (μ.toOuterMeasure {ω | E ω}).toReal

omit [Fintype Ω] in
theorem pmfWeight_nonneg (μ : PMF Ω) (ω : Ω) : 0 ≤ pmfWeight μ ω :=
  ENNReal.toReal_nonneg

theorem pmfWeight_sum_eq_one (μ : PMF Ω) : ∑ ω : Ω, pmfWeight μ ω = 1 := by
  have htsum : ∑ ω : Ω, μ ω = 1 := by
    simpa only [tsum_fintype] using μ.tsum_coe
  have h := congrArg ENNReal.toReal htsum
  rw [ENNReal.toReal_sum (fun ω _ => μ.apply_ne_top ω), ENNReal.toReal_one] at h
  exact h

theorem pmfProb_eq_sum_filter (μ : PMF Ω) (E : Ω → Prop) [DecidablePred E] :
    pmfProb μ E = ∑ ω ∈ Finset.univ.filter E, pmfWeight μ ω := by
  have hs : (↑(Finset.univ.filter E) : Set Ω) = {ω | E ω} := by
    ext ω
    simp
  unfold pmfProb pmfWeight
  rw [← hs, PMF.toOuterMeasure_apply_finset, ENNReal.toReal_sum (fun ω _ => μ.apply_ne_top ω)]

theorem pmfProb_eq_eventMass (μ : PMF Ω) (E : Ω → Prop) :
    pmfProb μ E = Cogentic.RandomizedPoolCoverage.eventMass (pmfWeight μ) E := by
  classical
  rw [pmfProb_eq_sum_filter, Cogentic.RandomizedPoolCoverage.eventMass, Finset.sum_filter]

omit [Fintype Ω] in
theorem pmfProb_nonneg (μ : PMF Ω) (E : Ω → Prop) : 0 ≤ pmfProb μ E :=
  ENNReal.toReal_nonneg

theorem pmfProb_le_one (μ : PMF Ω) (E : Ω → Prop) : pmfProb μ E ≤ 1 := by
  classical
  rw [pmfProb_eq_sum_filter, ← pmfWeight_sum_eq_one μ]
  exact Finset.sum_le_univ_sum_of_nonneg (pmfWeight_nonneg μ)

theorem pmfProb_mono (μ : PMF Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    pmfProb μ E ≤ pmfProb μ F := by
  classical
  rw [pmfProb_eq_sum_filter, pmfProb_eq_sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun ω hω => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩)
    (fun ω _ _ => pmfWeight_nonneg μ ω)

theorem pmfProb_exists_le_sum {ι : Type*} (μ : PMF Ω) (s : Finset ι) (E : ι → Ω → Prop) :
    pmfProb μ (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, pmfProb μ (E i) := by
  classical
  simp_rw [pmfProb_eq_sum_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  have hterm : ∀ i, 0 ≤ if E i ω then pmfWeight μ ω else 0 := fun i => by
    split_ifs <;> simp [pmfWeight_nonneg]
  by_cases hex : ∃ i ∈ s, E i ω
  · rw [if_pos hex]
    obtain ⟨i, hi, hEi⟩ := hex
    have hsingle := Finset.single_le_sum (f := fun i => if E i ω then pmfWeight μ ω else 0)
      (fun j _ => hterm j) hi
    simpa only [if_pos hEi] using hsingle
  · rw [if_neg hex]
    exact Finset.sum_nonneg fun i _ => hterm i

/-- Finite Paley–Zygmund lower bound with reference scale `τ > 0`. -/
theorem pmf_paley_zygmund (μ : PMF Ω) (Z : Ω → ℝ) {a M τ : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hτ : 0 < τ)
    (hmean : a * τ ≤ pmfExpect μ Z)
    (hsecond : pmfExpect μ (fun ω => Z ω ^ 2) ≤ M * τ ^ 2) :
    a ^ 2 / (4 * M) ≤ pmfProb μ (fun ω => a * τ / 2 ≤ Z ω) := by
  classical
  let large := Finset.univ.filter (fun ω => a * τ / 2 ≤ Z ω)
  have hlargeMean : a * τ / 2 ≤ ∑ ω ∈ large, pmfWeight μ ω * Z ω := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => show
        pmfWeight μ ω * Z ω ≤
          (if a * τ / 2 ≤ Z ω then pmfWeight μ ω * Z ω else 0) + (a * τ / 2) * pmfWeight μ ω by
      have hw := pmfWeight_nonneg μ ω
      split_ifs with hZ
      · linarith [mul_nonneg (show 0 ≤ a * τ / 2 by positivity) hw]
      · nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge hZ) hw])
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum,
      pmfWeight_sum_eq_one μ, mul_one] at h
    unfold pmfExpect at hmean
    linarith
  have hCS : (∑ ω ∈ large, pmfWeight μ ω * Z ω) ^ 2 ≤
      (∑ ω ∈ large, pmfWeight μ ω) * ∑ ω ∈ large, pmfWeight μ ω * Z ω ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul large
      (fun ω _ => pmfWeight_nonneg μ ω)
      (fun ω _ => mul_nonneg (pmfWeight_nonneg μ ω) (sq_nonneg _))
      (fun _ _ => by ring_nf; rfl)
  have hsub : ∑ ω ∈ large, pmfWeight μ ω * Z ω ^ 2 ≤ M * τ ^ 2 :=
    (Finset.sum_le_univ_sum_of_nonneg (fun ω => mul_nonneg (pmfWeight_nonneg μ ω) (sq_nonneg _))).trans
      hsecond
  have hmul : (∑ ω ∈ large, pmfWeight μ ω) * (∑ ω ∈ large, pmfWeight μ ω * Z ω ^ 2) ≤
      (∑ ω ∈ large, pmfWeight μ ω) * (M * τ ^ 2) :=
    mul_le_mul_of_nonneg_left hsub (Finset.sum_nonneg fun ω _ => pmfWeight_nonneg μ ω)
  have hsq : (a * τ / 2) ^ 2 ≤ (∑ ω ∈ large, pmfWeight μ ω * Z ω) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlargeMean 2
  have hkey : (a * τ / 2) ^ 2 ≤ (∑ ω ∈ large, pmfWeight μ ω) * (M * τ ^ 2) :=
    hsq.trans (hCS.trans hmul)
  have hkey' : a ^ 2 * τ ^ 2 ≤ (∑ ω ∈ large, pmfWeight μ ω) * (4 * M) * τ ^ 2 := by
    nlinarith
  have hcancel : a ^ 2 ≤ (∑ ω ∈ large, pmfWeight μ ω) * (4 * M) :=
    le_of_mul_le_mul_right hkey' (sq_pos_of_pos hτ)
  rw [pmfProb_eq_sum_filter]
  exact (div_le_iff₀ (by positivity)).mpr hcancel

/-- Second-moment Markov upper-tail cut `Pr[Z > U * τ] ≤ M / U^2`. -/
theorem pmf_upper_cut_prob_le (μ : PMF Ω) (Z : Ω → ℝ) {M τ U : ℝ}
    (hτ : 0 < τ) (hU : 0 < U)
    (hsecond : pmfExpect μ (fun ω => Z ω ^ 2) ≤ M * τ ^ 2) :
    pmfProb μ (fun ω => U * τ < Z ω) ≤ M / U ^ 2 := by
  classical
  have hsum : (U * τ) ^ 2 * pmfProb μ (fun ω => U * τ < Z ω) ≤
      pmfExpect μ (fun ω => Z ω ^ 2) := by
    rw [pmfProb_eq_sum_filter, Finset.sum_filter, Finset.mul_sum]
    unfold pmfExpect
    apply Finset.sum_le_sum
    intro ω _
    have hw := pmfWeight_nonneg μ ω
    split_ifs with hZ
    · have hsq : (U * τ) ^ 2 ≤ Z ω ^ 2 := pow_le_pow_left₀ (by positivity) hZ.le 2
      nlinarith [mul_le_mul_of_nonneg_left hsq hw]
    · rw [mul_zero]
      exact mul_nonneg hw (sq_nonneg _)
  have hbound : (U * τ) ^ 2 * pmfProb μ (fun ω => U * τ < Z ω) ≤ M * τ ^ 2 :=
    hsum.trans hsecond
  have hcancel : U ^ 2 * pmfProb μ (fun ω => U * τ < Z ω) ≤ M := by
    apply le_of_mul_le_mul_right _ (sq_pos_of_pos hτ)
    linarith [hbound]
  exact (le_div_iff₀ (sq_pos_of_pos hU)).mpr (by linarith)

/-- First-moment Markov cut for nonnegative bad-child incidence `Pr[B > a * τ / 4] ≤ 4 * ε / a`. -/
theorem pmf_bad_child_cut_prob_le (μ : PMF Ω) (B : Ω → ℝ) {a τ ε : ℝ}
    (ha : 0 < a) (hτ : 0 < τ)
    (hB : ∀ ω, 0 ≤ B ω)
    (hbad : pmfExpect μ B ≤ ε * τ) :
    pmfProb μ (fun ω => a * τ / 4 < B ω) ≤ 4 * ε / a := by
  classical
  have hsum : (a * τ / 4) * pmfProb μ (fun ω => a * τ / 4 < B ω) ≤ pmfExpect μ B := by
    rw [pmfProb_eq_sum_filter, Finset.sum_filter, Finset.mul_sum]
    unfold pmfExpect
    apply Finset.sum_le_sum
    intro ω _
    have hw := pmfWeight_nonneg μ ω
    split_ifs with hcut
    · nlinarith [mul_le_mul_of_nonneg_left hcut.le hw]
    · rw [mul_zero]
      exact mul_nonneg hw (hB ω)
  have hbound : (a * τ / 4) * pmfProb μ (fun ω => a * τ / 4 < B ω) ≤ ε * τ :=
    hsum.trans hbad
  have hcancel : a * pmfProb μ (fun ω => a * τ / 4 < B ω) ≤ 4 * ε := by
    apply le_of_mul_le_mul_right _ hτ
    linarith [hbound]
  exact (le_div_iff₀ ha).mpr (by linarith)

/-- Combined survivor event probability bound from Paley–Zygmund, the upper second-moment cut,
and the bad-child Markov cut. -/
theorem pmf_survivor_event_prob_ge (μ : PMF Ω) (Z B : Ω → ℝ) {a M τ U ε : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hτ : 0 < τ) (hU : 0 < U)
    (hB : ∀ ω, 0 ≤ B ω)
    (hmean : a * τ ≤ pmfExpect μ Z)
    (hsecond : pmfExpect μ (fun ω => Z ω ^ 2) ≤ M * τ ^ 2)
    (hbad : pmfExpect μ B ≤ ε * τ) :
    a ^ 2 / (4 * M) - M / U ^ 2 - 4 * ε / a ≤
      pmfProb μ (fun ω => a * τ / 4 ≤ Z ω - B ω ∧ Z ω ≤ U * τ) := by
  classical
  have hpz := pmf_paley_zygmund μ Z ha hM hτ hmean hsecond
  have hup := pmf_upper_cut_prob_le μ Z hτ hU hsecond
  have hbc := pmf_bad_child_cut_prob_le μ B ha hτ hB hbad
  have hunion :
      pmfProb μ (fun ω => a * τ / 2 ≤ Z ω) ≤
        pmfProb μ (fun ω => a * τ / 4 ≤ Z ω - B ω ∧ Z ω ≤ U * τ) +
        pmfProb μ (fun ω => U * τ < Z ω) +
        pmfProb μ (fun ω => a * τ / 4 < B ω) := by
    simp_rw [pmfProb_eq_sum_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have hw := pmfWeight_nonneg μ ω
    have h1 : 0 ≤ if a * τ / 4 ≤ Z ω - B ω ∧ Z ω ≤ U * τ then pmfWeight μ ω else 0 := by
      split_ifs <;> simp [hw]
    have h2 : 0 ≤ if U * τ < Z ω then pmfWeight μ ω else 0 := by
      split_ifs <;> simp [hw]
    have h3 : 0 ≤ if a * τ / 4 < B ω then pmfWeight μ ω else 0 := by
      split_ifs <;> simp [hw]
    by_cases hz : a * τ / 2 ≤ Z ω
    · rw [if_pos hz]
      by_cases hu : U * τ < Z ω
      · rw [if_pos hu]; linarith
      · by_cases hb : a * τ / 4 < B ω
        · rw [if_pos hb]; linarith
        · have hs : a * τ / 4 ≤ Z ω - B ω ∧ Z ω ≤ U * τ := ⟨by linarith, le_of_not_gt hu⟩
          rw [if_pos hs]; linarith
    · rw [if_neg hz]; linarith
  linarith

/-- Pointwise survivor-ratio lower bound on the survivor event. -/
theorem survivor_ratio_ge {a τ U z b : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (hU : 0 < U)
    (hb : 0 ≤ b) (hsurv : a * τ / 4 ≤ z - b) (hupper : z ≤ U * τ) :
    0 < z ∧ a / (4 * U) ≤ (z - b) / z := by
  have hz_pos : 0 < z := by linarith [show 0 < a * τ / 4 by positivity]
  refine ⟨hz_pos, ?_⟩
  rw [div_le_div_iff₀ (by positivity) hz_pos]
  nlinarith [show 0 < a * τ / 4 by positivity, mul_le_mul_of_nonneg_left hupper ha.le]

/-- Canonical choice `U = sqrt(8 * M^2 / a^2)` and `ε ≤ a^3 / (64 * M)` yields survivor
probability at least `a^2 / (16 * M)` together with survivor ratio at least `a / (4 * U)`. -/
theorem pmf_survivor_canonical (μ : PMF Ω) (Z B : Ω → ℝ) {a M τ ε : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hτ : 0 < τ)
    (hB : ∀ ω, 0 ≤ B ω)
    (hmean : a * τ ≤ pmfExpect μ Z)
    (hsecond : pmfExpect μ (fun ω => Z ω ^ 2) ≤ M * τ ^ 2)
    (hbad : pmfExpect μ B ≤ ε * τ)
    (hε : ε ≤ a ^ 3 / (64 * M)) :
    let U := Real.sqrt (8 * M ^ 2 / a ^ 2)
    0 < U ∧
      a ^ 2 / (16 * M) ≤
        pmfProb μ (fun ω =>
          a * τ / 4 ≤ Z ω - B ω ∧ Z ω ≤ U * τ ∧ a / (4 * U) ≤ (Z ω - B ω) / Z ω) := by
  intro U
  have harg : 0 < 8 * M ^ 2 / a ^ 2 := by positivity
  have hU : 0 < U := Real.sqrt_pos.mpr harg
  have hUsq : U ^ 2 = 8 * M ^ 2 / a ^ 2 := Real.sq_sqrt harg.le
  have hup_eq : M / U ^ 2 = a ^ 2 / (8 * M) := by
    rw [hUsq]
    field_simp
  have hbad_le : 4 * ε / a ≤ a ^ 2 / (16 * M) := by
    have hmul := mul_le_mul_of_nonneg_left hε (show 0 ≤ (4 : ℝ) / a by positivity)
    have hrhs : 4 / a * (a ^ 3 / (64 * M)) = a ^ 2 / (16 * M) := by field_simp; ring
    have hlhs : 4 / a * ε = 4 * ε / a := by ring
    linarith
  have hbase := pmf_survivor_event_prob_ge μ Z B ha hM hτ hU hB hmean hsecond hbad
  have hprob : a ^ 2 / (16 * M) ≤
      pmfProb μ (fun ω => a * τ / 4 ≤ Z ω - B ω ∧ Z ω ≤ U * τ) := by
    have hcalc : a ^ 2 / (4 * M) - a ^ 2 / (8 * M) - a ^ 2 / (16 * M) = a ^ 2 / (16 * M) := by
      field_simp; ring
    linarith
  refine ⟨hU, hprob.trans (pmfProb_mono μ ?_)⟩
  intro ω ⟨hsurv, hupper⟩
  exact ⟨hsurv, hupper, (survivor_ratio_ge ha hτ hU (hB ω) hsurv hupper).2⟩

end FinitePMFSurvivor

/-! ## Section 2: Dyad Exceptional-Prime Trimming (Markov Across `p ∈ J`) -/

section DyadTrimming

variable {P : Type*} [DecidableEq P]

/-- Deterministic exceptional subset of a dyad `J` where either the rational error
exceeds `θ_rat` or the bad-child error exceeds `θ_bad`. -/
noncomputable def badDyadPrimes (J : Finset P) (err_rat err_bad : P → ℝ)
    (θ_rat θ_bad : ℝ) : Finset P := by
  classical
  exact J.filter (fun p => θ_rat < err_rat p ∨ θ_bad < err_bad p)

omit [DecidableEq P] in
theorem badDyadPrimes_subset (J : Finset P) (err_rat err_bad : P → ℝ)
    (θ_rat θ_bad : ℝ) :
    badDyadPrimes J err_rat err_bad θ_rat θ_bad ⊆ J := by
  classical
  exact Finset.filter_subset _ _

theorem dyad_trimming_good (J : Finset P) (err_rat err_bad : P → ℝ)
    (θ_rat θ_bad : ℝ) {p : P}
    (hp : p ∈ J \ badDyadPrimes J err_rat err_bad θ_rat θ_bad) :
    err_rat p ≤ θ_rat ∧ err_bad p ≤ θ_bad := by
  classical
  rw [Finset.mem_sdiff, badDyadPrimes, Finset.mem_filter] at hp
  have hnot : ¬ (θ_rat < err_rat p ∨ θ_bad < err_bad p) := fun h => hp.2 ⟨hp.1, h⟩
  exact ⟨le_of_not_gt fun h => hnot (Or.inl h), le_of_not_gt fun h => hnot (Or.inr h)⟩

omit [DecidableEq P] in
private theorem filter_gt_card_le_of_sum_le (J : Finset P) (f : P → ℝ) {δ θ : ℝ}
    (hθ : 0 < θ) (hf : ∀ p ∈ J, 0 ≤ f p)
    (hsum : ∑ p ∈ J, f p ≤ δ * (J.card : ℝ)) :
    ((J.filter (fun p => θ < f p)).card : ℝ) ≤ (δ / θ) * (J.card : ℝ) := by
  classical
  let B := J.filter (fun p => θ < f p)
  have hmarkov : θ * (B.card : ℝ) ≤ ∑ p ∈ J, f p := by
    calc
      θ * (B.card : ℝ) = ∑ _p ∈ B, θ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ B, f p := Finset.sum_le_sum fun p hp => (Finset.mem_filter.mp hp).2.le
      _ ≤ ∑ p ∈ J, f p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp _ => hf p hp)
  have hle : θ * (B.card : ℝ) ≤ δ * (J.card : ℝ) := hmarkov.trans hsum
  calc
    (B.card : ℝ) ≤ (δ * (J.card : ℝ)) / θ := (le_div_iff₀ hθ).mpr (by linarith)
    _ = (δ / θ) * (J.card : ℝ) := by ring

/-- Dyad exceptional-prime trimming by Markov's inequality across `p ∈ J`. -/
theorem badDyadPrimes_card_le (J : Finset P) (err_rat err_bad : P → ℝ)
    {δ_rat δ_bad θ_rat θ_bad : ℝ}
    (hθ_rat : 0 < θ_rat) (hθ_bad : 0 < θ_bad)
    (herr_rat : ∀ p ∈ J, 0 ≤ err_rat p)
    (herr_bad : ∀ p ∈ J, 0 ≤ err_bad p)
    (hsum_rat : ∑ p ∈ J, err_rat p ≤ δ_rat * (J.card : ℝ))
    (hsum_bad : ∑ p ∈ J, err_bad p ≤ δ_bad * (J.card : ℝ)) :
    ((badDyadPrimes J err_rat err_bad θ_rat θ_bad).card : ℝ) ≤
      (δ_rat / θ_rat + δ_bad / θ_bad) * (J.card : ℝ) := by
  classical
  let B_rat := J.filter (fun p => θ_rat < err_rat p)
  let B_bad := J.filter (fun p => θ_bad < err_bad p)
  have hsub : badDyadPrimes J err_rat err_bad θ_rat θ_bad ⊆ B_rat ∪ B_bad := by
    intro p hp
    rw [badDyadPrimes, Finset.mem_filter] at hp
    rcases hp.2 with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp.1, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp.1, h2⟩)
  have hcard : ((badDyadPrimes J err_rat err_bad θ_rat θ_bad).card : ℝ) ≤
      (B_rat.card : ℝ) + (B_bad.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le B_rat B_bad)
  have h1 := filter_gt_card_le_of_sum_le J err_rat hθ_rat herr_rat hsum_rat
  have h2 := filter_gt_card_le_of_sum_le J err_bad hθ_bad herr_bad hsum_bad
  linarith

/-- Average-form dyad trimming: for a nonempty dyad `J` with dyad averages at most `δ_rat`
and `δ_bad`, there exists a deterministic subset `Bad ⊆ J` of size at most
`(δ_rat / θ_rat + δ_bad / θ_bad) * |J|` outside which both per-prime errors meet their cutoffs. -/
theorem dyad_trimming_of_avg (J : Finset P) (hJ : J.Nonempty) (err_rat err_bad : P → ℝ)
    {δ_rat δ_bad θ_rat θ_bad : ℝ}
    (hθ_rat : 0 < θ_rat) (hθ_bad : 0 < θ_bad)
    (herr_rat : ∀ p ∈ J, 0 ≤ err_rat p)
    (herr_bad : ∀ p ∈ J, 0 ≤ err_bad p)
    (havg_rat : (∑ p ∈ J, err_rat p) / (J.card : ℝ) ≤ δ_rat)
    (havg_bad : (∑ p ∈ J, err_bad p) / (J.card : ℝ) ≤ δ_bad) :
    ∃ Bad ⊆ J,
      (Bad.card : ℝ) ≤ (δ_rat / θ_rat + δ_bad / θ_bad) * (J.card : ℝ) ∧
      ∀ p ∈ J \ Bad, err_rat p ≤ θ_rat ∧ err_bad p ≤ θ_bad := by
  have hcard_pos : (0 : ℝ) < (J.card : ℝ) := Nat.cast_pos.mpr hJ.card_pos
  have hsum_rat : ∑ p ∈ J, err_rat p ≤ δ_rat * (J.card : ℝ) :=
    (div_le_iff₀ hcard_pos).mp havg_rat
  have hsum_bad : ∑ p ∈ J, err_bad p ≤ δ_bad * (J.card : ℝ) :=
    (div_le_iff₀ hcard_pos).mp havg_bad
  refine ⟨badDyadPrimes J err_rat err_bad θ_rat θ_bad,
    badDyadPrimes_subset J err_rat err_bad θ_rat θ_bad,
    badDyadPrimes_card_le J err_rat err_bad hθ_rat hθ_bad herr_rat herr_bad hsum_rat hsum_bad,
    fun p hp => dyad_trimming_good J err_rat err_bad θ_rat θ_bad hp⟩

end DyadTrimming

/-! ## Section 3: Polynomial Field-Pool Union Bound Across Used Dyads -/

section PolynomialFieldPool

open Cogentic.RandomizedPoolCoverage

/-- Standard elementary exponential bound `(1 - q)^K ≤ exp(-q * K)` for `q ≤ 1`. -/
theorem one_sub_pow_le_exp_neg_mul {q : ℝ} (hq : q ≤ 1) (K : ℕ) :
    (1 - q) ^ K ≤ Real.exp (-q * (K : ℝ)) := by
  have hnonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq
  have hstep : 1 - q ≤ Real.exp (-q) := by
    have h := Real.add_one_le_exp (-q)
    linarith
  calc
    (1 - q) ^ K ≤ (Real.exp (-q)) ^ K := pow_le_pow_left₀ hnonneg hstep K
    _ = Real.exp ((K : ℝ) * (-q)) := (Real.exp_nat_mul (-q) K).symm
    _ = Real.exp (-q * (K : ℝ)) := by ring_nf

/-- Exponential field-pool union bound directly extending
`Cogentic.RandomizedPoolCoverage.poolMissMass_le_card_mul`. Arbitrary dependence across
primes within a single draw is permitted. -/
theorem poolMissMass_le_card_mul_exp {Ω P : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (K : ℕ) (Good : Finset P) (hit : P → Ω → Prop) (q_hit : ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω) (htotal : (∑ ω, weight ω) = 1)
    (hhit : ∀ p ∈ Good, q_hit ≤ eventMass weight (hit p)) :
    poolMissMass weight K Good hit ≤ (Good.card : ℝ) * (1 - q_hit) ^ K ∧
      (Good.card : ℝ) * (1 - q_hit) ^ K ≤ (Good.card : ℝ) * Real.exp (-q_hit * (K : ℝ)) := by
  have hcard := poolMissMass_le_card_mul weight K Good hit q_hit hweight htotal hhit
  refine ⟨hcard, ?_⟩
  by_cases hne : Good.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    have hle1 : eventMass weight (hit p₀) ≤ 1 := by
      classical
      unfold eventMass
      rw [← htotal]
      exact Finset.sum_le_sum fun ω _ => by split_ifs <;> simp [hweight]
    have hq1 : q_hit ≤ 1 := (hhit p₀ hp₀).trans hle1
    exact mul_le_mul_of_nonneg_left (one_sub_pow_le_exp_neg_mul hq1 K) (Nat.cast_nonneg _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- `PMF`-form polynomial field-pool union bound for a set `Good` of non-exceptional primes. -/
theorem pmf_poolMissMass_le_card_mul_exp {Ω P : Type*} [Fintype Ω]
    (μ : PMF Ω) (K : ℕ) (Good : Finset P) (hit : P → Ω → Prop) (q_hit : ℝ)
    (hhit : ∀ p ∈ Good, q_hit ≤ pmfProb μ (hit p)) :
    poolMissMass (pmfWeight μ) K Good hit ≤ (Good.card : ℝ) * (1 - q_hit) ^ K ∧
      (Good.card : ℝ) * (1 - q_hit) ^ K ≤ (Good.card : ℝ) * Real.exp (-q_hit * (K : ℝ)) := by
  apply poolMissMass_le_card_mul_exp (pmfWeight μ) K Good hit q_hit
    (pmfWeight_nonneg μ) (pmfWeight_sum_eq_one μ)
  intro p hp
  rw [← pmfProb_eq_eventMass]
  exact hhit p hp

/-- Union bound across all used dyads: if every non-exceptional prime `p ∈ Good d` across all
dyads `d ∈ dyads` is hit with probability at least `q_hit` in one draw, then `K` independent
draws miss at least one retained prime across all used dyads with probability at most
`|⋃_{d ∈ dyads} Good d| * (1 - q_hit)^K ≤ (∑ d ∈ dyads, |Good d|) * exp(-q_hit * K)`. -/
theorem pmf_multiDyad_poolMissMass_le_exp {Ω ι P : Type*} [Fintype Ω] [DecidableEq P]
    (μ : PMF Ω) (K : ℕ) (dyads : Finset ι) (Good : ι → Finset P)
    (hit : P → Ω → Prop) (q_hit : ℝ)
    (hhit : ∀ d ∈ dyads, ∀ p ∈ Good d, q_hit ≤ pmfProb μ (hit p)) :
    let AllGood := dyads.biUnion Good
    poolMissMass (pmfWeight μ) K AllGood hit ≤ (AllGood.card : ℝ) * (1 - q_hit) ^ K ∧
      (AllGood.card : ℝ) * (1 - q_hit) ^ K ≤
        (∑ d ∈ dyads, ((Good d).card : ℝ)) * Real.exp (-q_hit * (K : ℝ)) := by
  intro AllGood
  have hall : ∀ p ∈ AllGood, q_hit ≤ pmfProb μ (hit p) := by
    intro p hp
    obtain ⟨d, hd, hpd⟩ := Finset.mem_biUnion.mp hp
    exact hhit d hd p hpd
  obtain ⟨h1, h2⟩ := pmf_poolMissMass_le_card_mul_exp μ K AllGood hit q_hit hall
  refine ⟨h1, h2.trans ?_⟩
  have hcard : (AllGood.card : ℝ) ≤ ∑ d ∈ dyads, ((Good d).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  exact mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le

/-- End-to-end connection of dyad trimming (Section 2), Paley–Zygmund canonical survivor
probability (Section 1), and the multi-dyad polynomial field-pool union bound (Section 3). -/
theorem pmf_trimmed_dyads_survivor_pool_coverage {Ω ι P : Type*} [Fintype Ω] [DecidableEq P]
    (μ : PMF Ω) (K : ℕ) (dyads : Finset ι) (dyad : ι → Finset P)
    (Z B : P → Ω → ℝ) (τ err_rat : P → ℝ)
    {a M δ_rat δ_bad θ_rat : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hθ_rat : 0 < θ_rat)
    (hτ : ∀ d ∈ dyads, ∀ p ∈ dyad d, 0 < τ p)
    (hB : ∀ d ∈ dyads, ∀ p ∈ dyad d, ∀ ω, 0 ≤ B p ω)
    (herr_rat_nn : ∀ d ∈ dyads, ∀ p ∈ dyad d, 0 ≤ err_rat p)
    (hsum_rat : ∀ d ∈ dyads, ∑ p ∈ dyad d, err_rat p ≤ δ_rat * ((dyad d).card : ℝ))
    (hsum_bad : ∀ d ∈ dyads,
      ∑ p ∈ dyad d, pmfExpect μ (B p) / τ p ≤ δ_bad * ((dyad d).card : ℝ))
    (hmean : ∀ d ∈ dyads, ∀ p ∈ dyad d, err_rat p ≤ θ_rat →
      a * τ p ≤ pmfExpect μ (Z p))
    (hsecond : ∀ d ∈ dyads, ∀ p ∈ dyad d, err_rat p ≤ θ_rat →
      pmfExpect μ (fun ω => Z p ω ^ 2) ≤ M * τ p ^ 2) :
    let θ_bad := a ^ 3 / (64 * M)
    let U := Real.sqrt (8 * M ^ 2 / a ^ 2)
    let Bad (d : ι) := badDyadPrimes (dyad d) err_rat (fun p => pmfExpect μ (B p) / τ p) θ_rat θ_bad
    let Good (d : ι) := dyad d \ Bad d
    let AllGood := dyads.biUnion Good
    let hit (p : P) (ω : Ω) :=
      a * τ p / 4 ≤ Z p ω - B p ω ∧ Z p ω ≤ U * τ p ∧ a / (4 * U) ≤ (Z p ω - B p ω) / Z p ω
    (∀ d ∈ dyads, ((Bad d).card : ℝ) ≤ (δ_rat / θ_rat + δ_bad / θ_bad) * ((dyad d).card : ℝ)) ∧
      poolMissMass (pmfWeight μ) K AllGood hit ≤
        (∑ d ∈ dyads, ((Good d).card : ℝ)) * Real.exp (-(a ^ 2 / (16 * M)) * (K : ℝ)) := by
  intro θ_bad U Bad Good AllGood hit
  have hθ_bad : 0 < θ_bad := by positivity
  have hbad_cards : ∀ d ∈ dyads,
      ((Bad d).card : ℝ) ≤ (δ_rat / θ_rat + δ_bad / θ_bad) * ((dyad d).card : ℝ) := by
    intro d hd
    apply badDyadPrimes_card_le (dyad d) err_rat (fun p => pmfExpect μ (B p) / τ p)
      hθ_rat hθ_bad (herr_rat_nn d hd) _ (hsum_rat d hd) (hsum_bad d hd)
    intro p hp
    exact div_nonneg
      (Finset.sum_nonneg fun ω _ => mul_nonneg (pmfWeight_nonneg μ ω) (hB d hd p hp ω))
      (hτ d hd p hp).le
  have hhit : ∀ d ∈ dyads, ∀ p ∈ Good d, a ^ 2 / (16 * M) ≤ pmfProb μ (hit p) := by
    intro d hd p hp
    have hpJ : p ∈ dyad d := (Finset.mem_sdiff.mp hp).1
    obtain ⟨hrat, hbad_div⟩ := dyad_trimming_good (dyad d) err_rat
      (fun q => pmfExpect μ (B q) / τ q) θ_rat θ_bad hp
    have hτp := hτ d hd p hpJ
    have hbad_exp : pmfExpect μ (B p) ≤ θ_bad * τ p := (div_le_iff₀ hτp).mp hbad_div
    exact (pmf_survivor_canonical μ (Z p) (B p) ha hM hτp (hB d hd p hpJ)
      (hmean d hd p hpJ hrat) (hsecond d hd p hpJ hrat) hbad_exp le_rfl).2
  obtain ⟨h1, h2⟩ := pmf_multiDyad_poolMissMass_le_exp μ K dyads Good hit (a ^ 2 / (16 * M)) hhit
  exact ⟨hbad_cards, h1.trans h2⟩

end PolynomialFieldPool

/-! ## Section 4: Multilevel Bad-Child Incidence Recurrence (KeyBreak G.11–G.12) -/

section MultilevelIncidence

/-- Exact closed-form bound for a finite-depth inhomogeneous linear recurrence
`δ i ≤ M i * δ (i + 1) + A i` over `L` levels. -/
theorem linear_recurrence_bound (δ M A : ℕ → ℝ) (L : ℕ)
    (hM : ∀ i < L, 0 ≤ M i)
    (hrec : ∀ i < L, δ i ≤ M i * δ (i + 1) + A i) :
    δ 0 ≤ (∏ j ∈ Finset.range L, M j) * δ L +
      ∑ i ∈ Finset.range L, (∏ j ∈ Finset.range i, M j) * A i := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hM' : ∀ i < L, 0 ≤ M i := fun i hi => hM i (Nat.lt_succ_of_lt hi)
    have hrec' : ∀ i < L, δ i ≤ M i * δ (i + 1) + A i := fun i hi => hrec i (Nat.lt_succ_of_lt hi)
    have hprev := ih hM' hrec'
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range L, M j :=
      Finset.prod_nonneg fun j hj => hM' j (Finset.mem_range.mp hj)
    have hstep := mul_le_mul_of_nonneg_left (hrec L (Nat.lt_succ_self L)) hprod_nn
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    linarith

/-- KeyBreak G.11 linear internal recurrence with uniform step multiplier `C_step`
and per-level elliptic/rational error `η + ε_rat`: exact geometric sum form. -/
theorem internal_linear_recurrence_exact (δ : ℕ → ℝ) (L : ℕ) {C_step η ε_rat : ℝ}
    (hC : 0 ≤ C_step)
    (hrec : ∀ i < L, δ i ≤ C_step * (δ (i + 1) + η + ε_rat)) :
    δ 0 ≤ C_step ^ L * δ L +
      (∑ i ∈ Finset.range L, C_step ^ (i + 1)) * (η + ε_rat) := by
  have hlin := linear_recurrence_bound δ (fun _ => C_step) (fun _ => C_step * (η + ε_rat)) L
    (fun _ _ => hC)
    (fun i hi => by linarith [hrec i hi])
  simp only [Finset.prod_const, Finset.card_range] at hlin
  calc
    δ 0 ≤ C_step ^ L * δ L + ∑ i ∈ Finset.range L, C_step ^ i * (C_step * (η + ε_rat)) := hlin
    _ = C_step ^ L * δ L + (∑ i ∈ Finset.range L, C_step ^ (i + 1)) * (η + ε_rat) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring

/-- KeyBreak G.11 linear internal recurrence closed-form bound for `1 ≤ C_step`. -/
theorem internal_linear_recurrence_bound (δ : ℕ → ℝ) (L : ℕ) {C_step η ε_rat : ℝ}
    (hC : 1 ≤ C_step) (hα : 0 ≤ η + ε_rat)
    (hrec : ∀ i < L, δ i ≤ C_step * (δ (i + 1) + η + ε_rat)) :
    δ 0 ≤ C_step ^ L * (δ L + (L : ℝ) * (η + ε_rat)) := by
  have hexact := internal_linear_recurrence_exact δ L (by linarith) hrec
  have hsum : ∑ i ∈ Finset.range L, C_step ^ (i + 1) ≤ (L : ℝ) * C_step ^ L := by
    calc
      ∑ i ∈ Finset.range L, C_step ^ (i + 1) ≤ ∑ _i ∈ Finset.range L, C_step ^ L := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_right₀ hC (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      _ = (L : ℝ) * C_step ^ L := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmul := mul_le_mul_of_nonneg_right hsum hα
  linarith

/-- Sharper geometric-series closed form for the linear internal recurrence when `2 ≤ C_step`. -/
theorem internal_linear_recurrence_geom_bound (δ : ℕ → ℝ) (L : ℕ) {C_step η ε_rat : ℝ}
    (hC : 2 ≤ C_step) (hα : 0 ≤ η + ε_rat)
    (hrec : ∀ i < L, δ i ≤ C_step * (δ (i + 1) + η + ε_rat)) :
    δ 0 ≤ C_step ^ L * (δ L + 2 * (η + ε_rat)) := by
  have hexact := internal_linear_recurrence_exact δ L (by linarith) hrec
  have hgeom : ∑ i ∈ Finset.range L, C_step ^ (i + 1) ≤ 2 * C_step ^ L := by
    have hmul : (C_step - 1) * ∑ i ∈ Finset.range L, C_step ^ i = C_step ^ L - 1 := by
      rw [mul_comm]
      exact geom_sum_mul C_step L
    have hsum_eq : ∑ i ∈ Finset.range L, C_step ^ (i + 1) =
        C_step * ∑ i ∈ Finset.range L, C_step ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ']
    have hsub_pos : 0 < C_step - 1 := by linarith
    have hstep : (C_step - 1) * ∑ i ∈ Finset.range L, C_step ^ (i + 1) ≤
        (C_step - 1) * (2 * C_step ^ L) := by
      rw [hsum_eq]
      have h1 : (C_step - 1) * (C_step * ∑ i ∈ Finset.range L, C_step ^ i) =
          C_step * (C_step ^ L - 1) := by
        linarith [congrArg (C_step * ·) hmul]
      rw [h1]
      have hCpow : 0 ≤ C_step ^ L := by positivity
      nlinarith
    exact le_of_mul_le_mul_left hstep hsub_pos
  have hmul := mul_le_mul_of_nonneg_right hgeom hα
  linarith

/-- KeyBreak G.12 top-level square-root bound combined with the G.11 linear internal recurrence
over `L` internal levels (`δ_int 0 = δ_1` down to base level `δ_int L = δ_{L+1}`). -/
theorem top_sqrt_of_internal_linear_bound (δ_int : ℕ → ℝ) (L : ℕ)
    {δ_top C_top C_step η ε_rat ε_in : ℝ}
    (hC_top : 0 ≤ C_top) (hC_step : 1 ≤ C_step) (hα : 0 ≤ η + ε_rat)
    (hrec : ∀ i < L, δ_int i ≤ C_step * (δ_int (i + 1) + η + ε_rat))
    (htop : δ_top ≤ C_top * (Real.sqrt (δ_int 0) + Real.sqrt ε_in + η)) :
    δ_top ≤ C_top * (Real.sqrt (C_step ^ L * (δ_int L + (L : ℝ) * (η + ε_rat))) +
      Real.sqrt ε_in + η) := by
  have hint := internal_linear_recurrence_bound δ_int L hC_step hα hrec
  have hsqrt := Real.sqrt_le_sqrt hint
  have hinner : Real.sqrt (δ_int 0) + Real.sqrt ε_in + η ≤
      Real.sqrt (C_step ^ L * (δ_int L + (L : ℝ) * (η + ε_rat))) + Real.sqrt ε_in + η := by
    linarith
  exact htop.trans (mul_le_mul_of_nonneg_left hinner hC_top)

/-- Iterated square-root recurrence over `L` levels: if `δ i ≤ C_step * (√(δ (i + 1)) + η + ε_rat)`
for all `i < L` with `1 ≤ C_step`, `0 ≤ δ L`, and `0 ≤ η + ε_rat ≤ 1`, then
`δ 0 ≤ (2 * C_step)^2 * (δ L + η + ε_rat)^(1 / 2^L)`. -/
theorem iterated_sqrt_recurrence_bound (δ : ℕ → ℝ) (L : ℕ) {C_step η ε_rat : ℝ}
    (hC : 1 ≤ C_step) (hδL : 0 ≤ δ L)
    (hα0 : 0 ≤ η + ε_rat) (hα1 : η + ε_rat ≤ 1)
    (hrec : ∀ i < L, δ i ≤ C_step * (Real.sqrt (δ (i + 1)) + η + ε_rat)) :
    δ 0 ≤ (2 * C_step) ^ 2 * (δ L + η + ε_rat) ^ ((1 : ℝ) / (2 : ℝ) ^ L) := by
  induction L generalizing δ with
  | zero =>
    simp only [pow_zero, div_one, Real.rpow_one]
    have hcoeff : 1 ≤ (2 * C_step) ^ 2 := by nlinarith
    have hsum_nn : 0 ≤ δ 0 + η + ε_rat := by linarith
    have hle : δ 0 ≤ δ 0 + η + ε_rat := by linarith
    calc
      δ 0 ≤ 1 * (δ 0 + η + ε_rat) := by linarith
      _ ≤ (2 * C_step) ^ 2 * (δ 0 + η + ε_rat) := mul_le_mul_of_nonneg_right hcoeff hsum_nn
  | succ L ih =>
    let α := η + ε_rat
    have hih : δ 1 ≤ (2 * C_step) ^ 2 * (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ L) := by
      have h := ih (fun i => δ (i + 1)) hδL (fun i hi => hrec (i + 1) (Nat.succ_lt_succ hi))
      simpa only [α, add_assoc] using h
    have hbase_nn : 0 ≤ δ (L + 1) + α := by linarith
    have hexp_pos : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ (L + 1) := by positivity
    have hexp_le1 : (1 : ℝ) / (2 : ℝ) ^ (L + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have hsqrt_step :
        Real.sqrt (δ 1) ≤
          (2 * C_step) * (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) := by
      calc
        Real.sqrt (δ 1)
            ≤ Real.sqrt ((2 * C_step) ^ 2 * (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ L)) :=
          Real.sqrt_le_sqrt hih
        _ = Real.sqrt ((2 * C_step) ^ 2) *
              Real.sqrt ((δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ L)) :=
          Real.sqrt_mul (sq_nonneg _) _
        _ = (2 * C_step) * ((δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ L)) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_sq (by linarith), Real.sqrt_eq_rpow]
        _ = (2 * C_step) * (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) := by
          rw [← Real.rpow_mul hbase_nn]
          congr 2
          rw [pow_succ]
          ring
    have hα_step : α ≤ (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) := by
      have hα_pow : α ≤ α ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) := by
        rcases eq_or_lt_of_le (show 0 ≤ α from hα0) with h0 | hpos
        · rw [← h0, Real.zero_rpow hexp_pos.ne']
        · simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_ge hpos (show α ≤ 1 from hα1) hexp_le1
      exact hα_pow.trans (Real.rpow_le_rpow (show 0 ≤ α from hα0) (by linarith) hexp_pos.le)
    have hrpow_nn : 0 ≤ (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) :=
      Real.rpow_nonneg hbase_nn _
    have hstep0 : δ 0 ≤ C_step * (Real.sqrt (δ 1) + α) := by
      simpa only [α, add_assoc] using hrec 0 (Nat.zero_lt_succ L)
    calc
      δ 0 ≤ C_step * (Real.sqrt (δ 1) + α) := hstep0
      _ ≤ C_step * ((2 * C_step) * (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) +
            (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1))) :=
        mul_le_mul_of_nonneg_left (add_le_add hsqrt_step hα_step) (by linarith)
      _ = (C_step * (2 * C_step + 1)) * (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) := by
        ring
      _ ≤ (2 * C_step) ^ 2 * (δ (L + 1) + α) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) := by
        apply mul_le_mul_of_nonneg_right _ hrpow_nn
        nlinarith
      _ = (2 * C_step) ^ 2 * (δ (L + 1) + η + ε_rat) ^ ((1 : ℝ) / (2 : ℝ) ^ (L + 1)) := by
        simp only [α, add_assoc]

/-- Corollary of `iterated_sqrt_recurrence_bound` expressing the `L`-level propagation
in both the `(2 * C_step)^(2^L)` prefactor form (for `1 ≤ L`) and the `2^L`-th power form. -/
theorem iterated_sqrt_recurrence_pow_bound (δ : ℕ → ℝ) (L : ℕ) {C_step η ε_rat : ℝ}
    (hL : 1 ≤ L) (hC : 1 ≤ C_step) (hδ0 : 0 ≤ δ 0) (hδL : 0 ≤ δ L)
    (hα0 : 0 ≤ η + ε_rat) (hα1 : η + ε_rat ≤ 1)
    (hrec : ∀ i < L, δ i ≤ C_step * (Real.sqrt (δ (i + 1)) + η + ε_rat)) :
    δ 0 ≤ (2 * C_step) ^ (2 ^ L) * (δ L + η + ε_rat) ^ ((1 : ℝ) / (2 : ℝ) ^ L) ∧
      δ 0 ^ (2 ^ L) ≤ (2 * C_step) ^ (2 ^ (L + 1)) * (δ L + η + ε_rat) := by
  have hmain := iterated_sqrt_recurrence_bound δ L hC hδL hα0 hα1 hrec
  have hbase_nn : 0 ≤ δ L + η + ε_rat := by linarith
  have h2L : 2 ≤ 2 ^ L := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hpref : (2 * C_step) ^ 2 ≤ (2 * C_step) ^ (2 ^ L) :=
    pow_le_pow_right₀ (by linarith) h2L
  have hfirst : δ 0 ≤ (2 * C_step) ^ (2 ^ L) * (δ L + η + ε_rat) ^ ((1 : ℝ) / (2 : ℝ) ^ L) :=
    hmain.trans (mul_le_mul_of_nonneg_right hpref (Real.rpow_nonneg hbase_nn _))
  have hpow : δ 0 ^ (2 ^ L) ≤ (2 * C_step) ^ (2 ^ (L + 1)) * (δ L + η + ε_rat) := by
    calc
      δ 0 ^ (2 ^ L)
          ≤ ((2 * C_step) ^ 2 * (δ L + η + ε_rat) ^ ((1 : ℝ) / (2 : ℝ) ^ L)) ^ (2 ^ L) :=
        pow_le_pow_left₀ hδ0 hmain (2 ^ L)
      _ = ((2 * C_step) ^ 2) ^ (2 ^ L) *
            ((δ L + η + ε_rat) ^ ((1 : ℝ) / (2 : ℝ) ^ L)) ^ (2 ^ L) := by
        rw [mul_pow]
      _ = (2 * C_step) ^ (2 ^ (L + 1)) * (δ L + η + ε_rat) := by
        congr 1
        · rw [← pow_mul, pow_succ']
        · rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_nn]
          have hne : ((2 : ℝ) ^ L) ≠ 0 := by positivity
          have hexp : (1 : ℝ) / (2 : ℝ) ^ L * ((2 ^ L : ℕ) : ℝ) = 1 := by
            push_cast
            exact one_div_mul_cancel hne
          rw [hexp, Real.rpow_one]
  exact ⟨hfirst, hpow⟩

end MultilevelIncidence

/-! ## Section 5: H.4 Bounded-Search Opportunity Transfer and Descent-Tree Union Bound -/

section BoundedSearchTransfer

open Cogentic.RandomizedPoolCoverage

/-- Transfer verified candidate probability, survivor fraction, and elliptic recognition
factor into a per-trial verified-opportunity lower bound. -/
theorem opportunity_prob_ge {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (Ver Surv GoodOpp : Ω → Prop) {p_ver s_surv p_rec : ℝ}
    (hs_surv : 0 ≤ s_surv) (hp_rec : 0 ≤ p_rec)
    (hver : p_ver ≤ pmfProb μ Ver)
    (hsurv : s_surv * pmfProb μ Ver ≤ pmfProb μ Surv)
    (hrec : p_rec * pmfProb μ Surv ≤ pmfProb μ GoodOpp) :
    p_rec * s_surv * p_ver ≤ pmfProb μ GoodOpp := by
  calc
    p_rec * s_surv * p_ver = p_rec * (s_surv * p_ver) := by ring
    _ ≤ p_rec * (s_surv * pmfProb μ Ver) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hver hs_surv) hp_rec
    _ ≤ p_rec * pmfProb μ Surv := mul_le_mul_of_nonneg_left hsurv hp_rec
    _ ≤ pmfProb μ GoodOpp := hrec

/-- Specialization of `opportunity_prob_ge` to the `≥ 3/4` elliptic recognition factor
and survivor fraction `≥ c / U`. -/
theorem elliptic_survivor_opportunity_prob_ge {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (Ver Surv GoodOpp : Ω → Prop) {p_ver c U : ℝ}
    (hc : 0 ≤ c) (hU : 0 < U)
    (hver : p_ver ≤ pmfProb μ Ver)
    (hsurv : (c / U) * pmfProb μ Ver ≤ pmfProb μ Surv)
    (hrec : (3 / 4 : ℝ) * pmfProb μ Surv ≤ pmfProb μ GoodOpp) :
    (3 * c / (4 * U)) * p_ver ≤ pmfProb μ GoodOpp := by
  have h := opportunity_prob_ge μ Ver Surv GoodOpp (by positivity) (by norm_num) hver hsurv hrec
  have heq : (3 / 4 : ℝ) * (c / U) * p_ver = (3 * c / (4 * U)) * p_ver := by ring
  linarith

/-- Single-state H.4 bounded-search failure bound: if each independent trial completes a
good opportunity with probability at least `p_opp`, then `T` independent trials all fail
with probability at most `(1 - p_opp)^T ≤ exp(-p_opp * T)`. -/
theorem pmf_bounded_search_fail_le_exp {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (GoodOpp : Ω → Prop) (T : ℕ) {p_opp : ℝ}
    (hopp : p_opp ≤ pmfProb μ GoodOpp) :
    eventMass (iidWeight (pmfWeight μ) T) (fun draw => ∀ t : Fin T, ¬ GoodOpp (draw t)) ≤
      (1 - p_opp) ^ T ∧
      (1 - p_opp) ^ T ≤ Real.exp (-p_opp * (T : ℝ)) := by
  rw [iid_missMass_eq_pow (pmfWeight μ) T GoodOpp (pmfWeight_sum_eq_one μ),
    ← pmfProb_eq_eventMass]
  have hle1 : pmfProb μ GoodOpp ≤ 1 := pmfProb_le_one μ GoodOpp
  have hnonneg : 0 ≤ 1 - pmfProb μ GoodOpp := sub_nonneg.mpr hle1
  have hpow : (1 - pmfProb μ GoodOpp) ^ T ≤ (1 - p_opp) ^ T :=
    pow_le_pow_left₀ hnonneg (sub_le_sub_left hopp 1) T
  exact ⟨hpow, one_sub_pow_le_exp_neg_mul (hopp.trans hle1) T⟩

/-- Finite rooted descent tree whose internal nodes branch to lists of child subtrees. -/
inductive DescentTree (α : Type*) where
  | node (label : α) (children : List (DescentTree α))

/-- Total number of nodes (with multiplicity) in a descent tree. -/
def DescentTree.size {α : Type*} : DescentTree α → ℕ
  | .node _ cs => 1 + (cs.map DescentTree.size).sum

/-- Finset of distinct node labels occurring in a descent tree. -/
def DescentTree.nodes {α : Type*} [DecidableEq α] : DescentTree α → Finset α
  | .node a cs => insert a (cs.foldr (fun t acc => t.nodes ∪ acc) ∅)

/-- Predicate asserting that every node has at most `b` children and depth at most `L`. -/
def DescentTree.Bounded {α : Type*} (b : ℕ) : ℕ → DescentTree α → Prop
  | 0, .node _ cs => cs = []
  | L + 1, .node _ cs => cs.length ≤ b ∧ ∀ c ∈ cs, c.Bounded b L

/-- Upper bound `∑_{k=0}^L b^k` on the node count of a depth-`L`, degree-`b` tree. -/
def treeNodeCap (b L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (L + 1), b ^ k

theorem treeNodeCap_zero (b : ℕ) : treeNodeCap b 0 = 1 := by
  simp [treeNodeCap]

theorem treeNodeCap_succ (b L : ℕ) : treeNodeCap b (L + 1) = 1 + b * treeNodeCap b L := by
  unfold treeNodeCap
  rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ']

private theorem list_sum_le_length_mul {α : Type*} (l : List α) (f : α → ℕ) (M : ℕ)
    (hf : ∀ x ∈ l, f x ≤ M) : (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have hx : f x ≤ M := hf x (by simp)
    have hxs : (xs.map f).sum ≤ xs.length * M := ih fun y hy => hf y (by simp [hy])
    omega

theorem DescentTree.size_le_treeNodeCap {α : Type*} {b L : ℕ} {t : DescentTree α}
    (ht : t.Bounded b L) : t.size ≤ treeNodeCap b L := by
  induction L generalizing t with
  | zero =>
    cases t with
    | node a cs =>
      have hcs : cs = [] := ht
      subst hcs
      simp [DescentTree.size, treeNodeCap_zero]
  | succ L ih =>
    cases t with
    | node a cs =>
      obtain ⟨hlen, hchild⟩ := ht
      have hsum : (cs.map DescentTree.size).sum ≤ cs.length * treeNodeCap b L :=
        list_sum_le_length_mul cs DescentTree.size (treeNodeCap b L) (fun c hc => ih (hchild c hc))
      have hmul : cs.length * treeNodeCap b L ≤ b * treeNodeCap b L :=
        Nat.mul_le_mul_right _ hlen
      rw [DescentTree.size, treeNodeCap_succ]
      omega

private theorem foldr_union_card_le {α : Type*} [DecidableEq α] (cs : List (DescentTree α)) :
    (cs.foldr (fun t acc => DescentTree.nodes t ∪ acc) ∅).card ≤
      (cs.map fun c => (DescentTree.nodes c).card).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

private theorem list_map_sum_le_of_le {β : Type*} (l : List β) (f g : β → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem DescentTree.nodes_card_le_size {α : Type*} [DecidableEq α] (t : DescentTree α) :
    t.nodes.card ≤ t.size := by
  match t with
  | .node a cs =>
    have hsum : (cs.map fun c => (DescentTree.nodes c).card).sum ≤
        (cs.map DescentTree.size).sum :=
      list_map_sum_le_of_le cs (fun c => (DescentTree.nodes c).card) DescentTree.size
        fun c hc =>
          have : sizeOf c < sizeOf (DescentTree.node a cs) := by
            have := List.sizeOf_lt_of_mem hc
            simp only [DescentTree.node.sizeOf_spec]
            omega
          c.nodes_card_le_size
    calc
      (DescentTree.node a cs).nodes.card
          = (insert a (cs.foldr (fun c acc => DescentTree.nodes c ∪ acc) ∅)).card := by
            rw [DescentTree.nodes]
      _ ≤ (cs.foldr (fun c acc => DescentTree.nodes c ∪ acc) ∅).card + 1 := Finset.card_insert_le _ _
      _ ≤ (cs.map DescentTree.size).sum + 1 :=
        Nat.add_le_add_right ((foldr_union_card_le cs).trans hsum) 1
      _ = (DescentTree.node a cs).size := by rw [DescentTree.size, Nat.add_comm]
termination_by sizeOf t

theorem DescentTree.nodes_card_le_treeNodeCap {α : Type*} [DecidableEq α]
    {b L : ℕ} {t : DescentTree α} (ht : t.Bounded b L) :
    t.nodes.card ≤ treeNodeCap b L :=
  t.nodes_card_le_size.trans (t.size_le_treeNodeCap ht)

/-- For `1 ≤ b`, `treeNodeCap b L ≤ (L + 1) * b^L`. -/
theorem treeNodeCap_le_mul_pow {b : ℕ} (hb : 1 ≤ b) (L : ℕ) :
    treeNodeCap b L ≤ (L + 1) * b ^ L := by
  unfold treeNodeCap
  calc
    ∑ k ∈ Finset.range (L + 1), b ^ k ≤ ∑ _k ∈ Finset.range (L + 1), b ^ L := by
      apply Finset.sum_le_sum
      intro k hk
      exact Nat.pow_le_pow_right hb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (L + 1) * b ^ L := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- For `2 ≤ b`, `treeNodeCap b L ≤ 2 * b^L`. -/
theorem treeNodeCap_le_two_mul_pow {b : ℕ} (hb : 2 ≤ b) (L : ℕ) :
    (treeNodeCap b L : ℝ) ≤ 2 * (b : ℝ) ^ L := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hcast : (treeNodeCap b L : ℝ) = ∑ k ∈ Finset.range (L + 1), (b : ℝ) ^ k := by
    unfold treeNodeCap
    push_cast
    rfl
  rw [hcast]
  have hgeom : ((b : ℝ) - 1) * ∑ k ∈ Finset.range (L + 1), (b : ℝ) ^ k = (b : ℝ) ^ (L + 1) - 1 := by
    rw [mul_comm]
    exact geom_sum_mul (b : ℝ) (L + 1)
  have hsub_pos : 0 < (b : ℝ) - 1 := by linarith
  apply le_of_mul_le_mul_left _ hsub_pos
  rw [hgeom, pow_succ]
  have hbpow : 0 ≤ (b : ℝ) ^ L := by positivity
  nlinarith

/-- Union bound over all nodes of a bounded-degree depth-`L` descent tree:
if each node's bounded search of `T` trials fails with probability at most `(1 - p_opp)^T`
(with `p_opp ≤ 1`), then the probability that ANY node in the descent tree fails is at most
`treeNodeCap b L * (1 - p_opp)^T ≤ treeNodeCap b L * exp(-p_opp * T)`. -/
theorem pmf_descentTree_fail_le_exp {Ω Node : Type*} [Fintype Ω] [DecidableEq Node]
    (μ : PMF Ω) (t : DescentTree Node) {b L T : ℕ} {p_opp : ℝ}
    (ht : t.Bounded b L) (hp : p_opp ≤ 1)
    (Fail : Node → Ω → Prop)
    (hnode : ∀ v ∈ t.nodes, pmfProb μ (Fail v) ≤ (1 - p_opp) ^ T) :
    pmfProb μ (fun ω => ∃ v ∈ t.nodes, Fail v ω) ≤ (treeNodeCap b L : ℝ) * (1 - p_opp) ^ T ∧
      (treeNodeCap b L : ℝ) * (1 - p_opp) ^ T ≤
        (treeNodeCap b L : ℝ) * Real.exp (-p_opp * (T : ℝ)) := by
  have hpow_nn : 0 ≤ (1 - p_opp) ^ T := pow_nonneg (sub_nonneg.mpr hp) T
  have hcard : (t.nodes.card : ℝ) ≤ (treeNodeCap b L : ℝ) := by
    exact_mod_cast t.nodes_card_le_treeNodeCap ht
  have hunion : pmfProb μ (fun ω => ∃ v ∈ t.nodes, Fail v ω) ≤
      (treeNodeCap b L : ℝ) * (1 - p_opp) ^ T := by
    calc
      pmfProb μ (fun ω => ∃ v ∈ t.nodes, Fail v ω)
          ≤ ∑ v ∈ t.nodes, pmfProb μ (Fail v) := pmfProb_exists_le_sum μ t.nodes Fail
      _ ≤ ∑ _v ∈ t.nodes, (1 - p_opp) ^ T := Finset.sum_le_sum hnode
      _ = (t.nodes.card : ℝ) * (1 - p_opp) ^ T := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (treeNodeCap b L : ℝ) * (1 - p_opp) ^ T := mul_le_mul_of_nonneg_right hcard hpow_nn
  exact ⟨hunion, mul_le_mul_of_nonneg_left (one_sub_pow_le_exp_neg_mul hp T) (Nat.cast_nonneg _)⟩

/-- Branching-factor `b ≥ 2` exponential failure bound over a depth-`L` descent tree,
combining the `3/4` elliptic recognition factor and survivor fraction `c / U`. -/
theorem pmf_descentTree_elliptic_fail_le_exp {Ω Node : Type*} [Fintype Ω] [DecidableEq Node]
    (μ : PMF Ω) (t : DescentTree Node) {b L T : ℕ} {p_ver c U : ℝ}
    (hb : 2 ≤ b) (ht : t.Bounded b L)
    (hp_opp_le1 : (3 * c / (4 * U)) * p_ver ≤ 1)
    (Fail : Node → Ω → Prop)
    (hnode : ∀ v ∈ t.nodes,
      pmfProb μ (Fail v) ≤ (1 - (3 * c / (4 * U)) * p_ver) ^ T) :
    pmfProb μ (fun ω => ∃ v ∈ t.nodes, Fail v ω) ≤
      2 * (b : ℝ) ^ L * Real.exp (-((3 * c / (4 * U)) * p_ver) * (T : ℝ)) := by
  obtain ⟨h1, h2⟩ := pmf_descentTree_fail_le_exp μ t ht hp_opp_le1 Fail hnode
  have hcap := treeNodeCap_le_two_mul_pow hb L
  exact (h1.trans h2).trans (mul_le_mul_of_nonneg_right hcap (Real.exp_pos _).le)

/-- End-to-end H.4 descent-tree transfer: when every node `v` of a bounded-degree depth-`L`
descent tree has verified-candidate probability `≥ p_ver`, survivor fraction `≥ c / U`,
and elliptic recognition probability `≥ 3/4` in its trial law `μ_step v`, and the global
failure event `Fail v` is controlled by `T` independent trials from `μ_step v`, then
the probability that ANY node in the tree fails is at most
`2 * b^L * exp(-(3 * c / (4 * U) * p_ver) * T)` (for `2 ≤ b`). -/
theorem pmf_descentTree_from_elliptic_opportunities {Ω Ω_step Node : Type*}
    [Fintype Ω] [Fintype Ω_step] [DecidableEq Node]
    (μ : PMF Ω) (μ_step : Node → PMF Ω_step) (t : DescentTree Node) {b L T : ℕ} {p_ver c U : ℝ}
    (hb : 2 ≤ b) (ht : t.Bounded b L) (hc : 0 ≤ c) (hU : 0 < U)
    (Ver Surv GoodOpp : Node → Ω_step → Prop)
    (Fail : Node → Ω → Prop)
    (hver : ∀ v ∈ t.nodes, p_ver ≤ pmfProb (μ_step v) (Ver v))
    (hsurv : ∀ v ∈ t.nodes, (c / U) * pmfProb (μ_step v) (Ver v) ≤ pmfProb (μ_step v) (Surv v))
    (hrec : ∀ v ∈ t.nodes, (3 / 4 : ℝ) * pmfProb (μ_step v) (Surv v) ≤ pmfProb (μ_step v) (GoodOpp v))
    (hfail : ∀ v ∈ t.nodes,
      pmfProb μ (Fail v) ≤
        eventMass (iidWeight (pmfWeight (μ_step v)) T)
          (fun draw => ∀ k : Fin T, ¬ GoodOpp v (draw k))) :
    pmfProb μ (fun ω => ∃ v ∈ t.nodes, Fail v ω) ≤
      2 * (b : ℝ) ^ L * Real.exp (-((3 * c / (4 * U)) * p_ver) * (T : ℝ)) := by
  have hroot_mem : ∀ v ∈ t.nodes, (3 * c / (4 * U)) * p_ver ≤ pmfProb (μ_step v) (GoodOpp v) :=
    fun v hv => elliptic_survivor_opportunity_prob_ge (μ_step v) (Ver v) (Surv v) (GoodOpp v)
      hc hU (hver v hv) (hsurv v hv) (hrec v hv)
  have hne : t.nodes.Nonempty := by
    cases t with
    | node a cs => exact ⟨a, by simp [DescentTree.nodes]⟩
  obtain ⟨v₀, hv₀⟩ := hne
  have hp_opp_le1 : (3 * c / (4 * U)) * p_ver ≤ 1 :=
    (hroot_mem v₀ hv₀).trans (pmfProb_le_one (μ_step v₀) (GoodOpp v₀))
  apply pmf_descentTree_elliptic_fail_le_exp μ t hb ht hp_opp_le1 Fail
  intro v hv
  exact (hfail v hv).trans
    (pmf_bounded_search_fail_le_exp (μ_step v) (GoodOpp v) T (hroot_mem v hv)).1

end BoundedSearchTransfer

#print axioms pmf_paley_zygmund
#print axioms pmf_upper_cut_prob_le
#print axioms pmf_bad_child_cut_prob_le
#print axioms pmf_survivor_event_prob_ge
#print axioms survivor_ratio_ge
#print axioms pmf_survivor_canonical
#print axioms badDyadPrimes_card_le
#print axioms dyad_trimming_of_avg
#print axioms poolMissMass_le_card_mul_exp
#print axioms pmf_poolMissMass_le_card_mul_exp
#print axioms pmf_multiDyad_poolMissMass_le_exp
#print axioms pmf_trimmed_dyads_survivor_pool_coverage
#print axioms linear_recurrence_bound
#print axioms internal_linear_recurrence_bound
#print axioms internal_linear_recurrence_geom_bound
#print axioms top_sqrt_of_internal_linear_bound
#print axioms iterated_sqrt_recurrence_bound
#print axioms iterated_sqrt_recurrence_pow_bound
#print axioms opportunity_prob_ge
#print axioms elliptic_survivor_opportunity_prob_ge
#print axioms pmf_bounded_search_fail_le_exp
#print axioms DescentTree.size_le_treeNodeCap
#print axioms DescentTree.nodes_card_le_treeNodeCap
#print axioms pmf_descentTree_fail_le_exp
#print axioms pmf_descentTree_elliptic_fail_le_exp
#print axioms pmf_descentTree_from_elliptic_opportunities

end Cogentic.RandomizedFieldPoolDescent
