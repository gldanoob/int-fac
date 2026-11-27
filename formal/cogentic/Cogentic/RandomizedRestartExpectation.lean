import Cogentic.RandomizedRestartBudget
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace Cogentic.Randomized

open MeasureTheory
open scoped ENNReal

/-- The charge for phases reached on one sample path. Infinite charge is allowed
before taking the expectation. -/
noncomputable def dyadicRestartCharge {Ω : Type*} (T : ℝ) (reach : ℕ → Set Ω) (ω : Ω) :
    ℝ≥0∞ :=
  ∑' j : ℕ, (reach j).indicator (fun _ ↦ ENNReal.ofReal (T * (2 : ℝ)^j)) ω

private theorem dyadicRestartCharge_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 ≤ T)
    (reach : ℕ → Set Ω) (hmeas : ∀ j, MeasurableSet (reach j)) :
    (∫⁻ ω, dyadicRestartCharge T reach ω ∂μ) =
      ∑' j : ℕ, ENNReal.ofReal (T * (2 : ℝ)^j * (μ (reach j)).toReal) := by
  unfold dyadicRestartCharge
  rw [lintegral_tsum (fun j ↦ (measurable_const.indicator (hmeas j)).aemeasurable)]
  congr 1
  funext j
  have hbudget : 0 ≤ T * (2 : ℝ)^j := by positivity
  rw [lintegral_indicator_const (hmeas j), ENNReal.ofReal_mul hbudget,
    ENNReal.ofReal_toReal (measure_ne_top μ _)]

/-- A local conditional failure rate of at most one quarter bounds the expected
charge of doubling phase budgets by twice the first budget. The local assumption
is expressed in joint-mass form, so it also covers zero-probability reach events. -/
theorem dyadicRestartCharge_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 ≤ T)
    (reach : ℕ → Set Ω) (hmeas : ∀ j, MeasurableSet (reach j))
    (hnested : ∀ j, reach (j + 1) ⊆ reach j)
    (hrate : ∀ j, μ (reach (j + 1) ∩ reach j) ≤ ENNReal.ofReal (1/4) * μ (reach j)) :
    (∫⁻ ω, dyadicRestartCharge T reach ω ∂μ) ≤ ENNReal.ofReal (2*T) := by
  let p (j : ℕ) := (μ (reach j)).toReal
  have hp0 : p 0 ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := reach 0))
    simpa [p] using h
  have hpstep (j : ℕ) : p (j + 1) ≤ (1/4 : ℝ) * p j := by
    have hr := hrate j
    rw [Set.inter_eq_left.mpr (hnested j)] at hr
    have hf : ENNReal.ofReal (1/4) * μ (reach j) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)
    have := ENNReal.toReal_mono hf hr
    simpa [p, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/4 : ℝ))]
      using this
  have hnonneg (j : ℕ) : 0 ≤ p j := ENNReal.toReal_nonneg
  obtain ⟨hsum, hle⟩ := dyadic_restart_tail_tsum_le T hT p hnonneg
    (quarter_survival_le p hp0 hpstep)
  rw [dyadicRestartCharge_integral μ T hT reach hmeas,
    ← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity) hsum]
  exact ENNReal.ofReal_le_ofReal hle

/-- A deterministic prefix through the phases before the threshold, followed by
the same local restart guarantee, costs at most three threshold budgets in expectation. -/
theorem dyadicRestartCharge_with_prefix_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) (ha : 0 ≤ a) (m : ℕ)
    (reach : ℕ → Set Ω) (hmeas : ∀ j, MeasurableSet (reach j))
    (hnested : ∀ j, reach (j + 1) ⊆ reach j)
    (hrate : ∀ j, μ (reach (j + 1) ∩ reach j) ≤ ENNReal.ofReal (1/4) * μ (reach j)) :
    ENNReal.ofReal (∑ j ∈ Finset.range m, a * (2 : ℝ)^j) +
      (∫⁻ ω, dyadicRestartCharge (a * (2 : ℝ)^m) reach ω ∂μ) ≤
      ENNReal.ofReal (3 * (a * (2 : ℝ)^m)) := by
  apply (add_le_add le_rfl
    (dyadicRestartCharge_integral_le μ _ (by positivity) reach hmeas hnested hrate)).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), dyadic_restart_prefix_sum]
  exact ENNReal.ofReal_le_ofReal (by linarith only [ha])

/-- Markov's inequality on the reach event bounds the joint mass of proceeding. -/
theorem restart_quarter_rate_of_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {reach next : Set Ω}
    (hnext : MeasurableSet next) {runtime : Ω → ℝ≥0∞} (hruntime : Measurable runtime)
    {E : ℝ} (hE : 0 < E) {cap : ℝ≥0∞} (hcap : ENNReal.ofReal (4*E) ≤ cap)
    (hproceed : ∀ ω ∈ next, cap < runtime ω)
    (hmean : (∫⁻ ω in reach, runtime ω ∂μ) ≤ ENNReal.ofReal E * μ reach) :
    μ (next ∩ reach) ≤ ENNReal.ofReal (1/4) * μ reach := by
  have hmarkov : ENNReal.ofReal (4*E) * μ (next ∩ reach) ≤ ENNReal.ofReal E * μ reach := by
    rw [← Measure.restrict_apply hnext]
    calc
      _ ≤ ENNReal.ofReal (4*E) * μ.restrict reach {ω | ENNReal.ofReal (4*E) ≤ runtime ω} :=
        mul_le_mul_right (measure_mono fun ω hω ↦ hcap.trans (hproceed ω hω).le) _
      _ ≤ _ := mul_meas_ge_le_lintegral hruntime _
      _ ≤ _ := hmean
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ reach)) hmarkov
  have hbudget : 0 ≤ 4*E := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hbudget, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hE.le] at hreal
  have hquarter : (μ (next ∩ reach)).toReal ≤ (1/4 : ℝ) * (μ reach).toReal := by
    apply (mul_le_mul_iff_of_pos_left hE).mp
    linarith only [hreal]
  have h := ENNReal.ofReal_le_ofReal hquarter
  rwa [ENNReal.ofReal_toReal (measure_ne_top μ _), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4),
    ENNReal.ofReal_toReal (measure_ne_top μ _)] at h

/-- Conditional mean bounds yield both the dyadic expectation bound and almost
sure failure to reach infinitely many restart phases. -/
theorem dyadicRestartCharge_integral_le_of_conditional_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 ≤ T)
    (reach : ℕ → Set Ω) (hmeas : ∀ j, MeasurableSet (reach j))
    (hnested : ∀ j, reach (j + 1) ⊆ reach j)
    (runtime : ℕ → Ω → ℝ≥0∞) (hruntime : ∀ j, Measurable (runtime j))
    (E : ℕ → ℝ) (hE : ∀ j, 0 < E j) (cap : ℕ → ℝ≥0∞)
    (hcap : ∀ j, ENNReal.ofReal (4 * E j) ≤ cap j)
    (hproceed : ∀ j ω, ω ∈ reach (j + 1) → cap j < runtime j ω)
    (hmean : ∀ j, (∫⁻ ω in reach j, runtime j ω ∂μ) ≤ ENNReal.ofReal (E j) * μ (reach j)) :
    (∫⁻ ω, dyadicRestartCharge T reach ω ∂μ) ≤ ENNReal.ofReal (2*T) ∧
      μ (⋂ j, reach j) = 0 := by
  have hrate (j : ℕ) : μ (reach (j + 1) ∩ reach j) ≤ ENNReal.ofReal (1/4) * μ (reach j) :=
    restart_quarter_rate_of_mean μ (hmeas (j + 1)) (hruntime j) (hE j) (hcap j)
      (hproceed j) (hmean j)
  refine ⟨dyadicRestartCharge_integral_le μ T hT reach hmeas hnested hrate, ?_⟩
  have hsurvive (j : ℕ) : μ (reach j) ≤ (ENNReal.ofReal (1/4))^j := by
    induction j with
    | zero => simp only [pow_zero]; exact prob_le_one
    | succ j ih =>
      rw [pow_succ', ← Set.inter_eq_left.mpr (hnested j)]
      exact (hrate j).trans (mul_le_mul_right ih _)
  have hlimit := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show ENNReal.ofReal (1/4) < 1 by norm_num)
  have hbound (j : ℕ) : μ (⋂ i, reach i) ≤ (ENNReal.ofReal (1/4))^j :=
    (measure_mono (Set.iInter_subset reach j)).trans (hsurvive j)
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
    (Filter.Eventually.of_forall hbound)) bot_le

end Cogentic.Randomized
