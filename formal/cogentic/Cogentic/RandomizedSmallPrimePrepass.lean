import Cogentic.RandomizedEpochFactorization
import Cogentic.RandomizedSplitVerification
import Mathlib.Data.Nat.Factorization.Basic

namespace Cogentic.RandomizedSmallPrimePrepass

open Filter Real
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedCappedEpoch
open Cogentic.RandomizedEpochKernel
open Cogentic.RandomizedSplitVerification
open Cogentic.RandomizedInputDriver
open BinaryDivision
open scoped BigOperators ENNReal Topology

/-!
# Small-Prime Prepass and Rough-Branch Input Split

Every composite hard input `n` splits into two complementary cases relative to a
threshold `B`:
1. `HasSmallPrimeFactor B n`: `n` has a prime factor `p ≤ B`, handled by a small-prime
   prepass.
2. `IsRough B n`: every prime factor `p ∣ n` satisfies `p > B`, giving explicit upper
   bounds on `ω(n)`, `∑_{p ∣ n} 1/p`, and `∏_{p ∣ n} (1 + 4 / (p - 1))`.

At the regime `logB n = (log n)^(2/3)`, `B_0(n) = exp(logB n)`:
- `ω(n) ≤ log n / logB n = o(scale n)` on the rough branch,
- `(log (2n))^k / exp(logB n) → 0` for every fixed `k`,
- `sqrt(logB n * log(logB n)) = o(scale n)` so an `L_p[1/2, O(1)]` prepass fits in
  `exp(o(scale n))`.

We also prove a general epoch-composition theorem combining a small-prime prepass with
a rough-branch main epoch, and construct a verified counted trial-division prepass
reusing `RandomizedSplitVerification.verify`.
-/

section RoughBranchArithmetic

/-- `n` has a prime factor at most `B`. -/
def HasSmallPrimeFactor (B : ℝ) (n : ℕ) : Prop :=
  ∃ p ∈ n.primeFactors, (p : ℝ) ≤ B

/-- Every prime factor of `n` is strictly larger than `B`. -/
def IsRough (B : ℝ) (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, B < (p : ℝ)

theorem not_hasSmallPrimeFactor_iff_isRough (B : ℝ) (n : ℕ) :
    ¬ HasSmallPrimeFactor B n ↔ IsRough B n := by
  unfold HasSmallPrimeFactor IsRough
  push Not
  rfl

theorem hasSmallPrimeFactor_or_isRough (B : ℝ) (n : ℕ) :
    HasSmallPrimeFactor B n ∨ IsRough B n := by
  by_cases h : HasSmallPrimeFactor B n
  · exact Or.inl h
  · exact Or.inr ((not_hasSmallPrimeFactor_iff_isRough B n).mp h)

theorem isRough_le {B : ℝ} {n : ℕ} (h : IsRough B n) :
    ∀ p ∈ n.primeFactors, B ≤ (p : ℝ) :=
  fun p hp => (h p hp).le

/-- On a `B`-rough positive integer, `B ^ ω(n) ≤ ∏_{p ∣ n} p ≤ n`. -/
theorem pow_primeFactors_card_le {B : ℝ} {n : ℕ} (hB : 0 ≤ B) (hn : 0 < n)
    (hrough : ∀ p ∈ n.primeFactors, B ≤ (p : ℝ)) :
    B ^ n.primeFactors.card ≤ (n : ℝ) := by
  calc
    B ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, B := by
      rw [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) :=
      Finset.prod_le_prod (fun _ _ => hB) (fun p hp => hrough p hp)
    _ = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
    _ ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- If every prime factor of `n` is at least `B > 1`, then `ω(n) ≤ log n / log B`. -/
theorem primeFactors_card_le_log_div {B : ℝ} {n : ℕ} (hB : 1 < B)
    (hrough : ∀ p ∈ n.primeFactors, B ≤ (p : ℝ)) :
    (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hBpos : 0 < B := zero_lt_one.trans hB
    have hlogB : 0 < Real.log B := Real.log_pos hB
    have hpow : B ^ n.primeFactors.card ≤ (n : ℝ) :=
      pow_primeFactors_card_le hBpos.le hn hrough
    have hlog := Real.log_le_log (pow_pos hBpos _) hpow
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ hlogB).mpr hlog

/-- If every prime factor of `n` is at least `B > 1`, then
`∑_{p ∣ n} 1/p ≤ (log n / log B) / B`. -/
theorem sum_inv_primeFactors_le {B : ℝ} {n : ℕ} (hB : 1 < B)
    (hrough : ∀ p ∈ n.primeFactors, B ≤ (p : ℝ)) :
    ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) ≤ (Real.log n / Real.log B) / B := by
  have hBpos : 0 < B := zero_lt_one.trans hB
  calc
    ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)
        ≤ ∑ _p ∈ n.primeFactors, (1 : ℝ) / B :=
      Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le hBpos (hrough p hp)
    _ = (n.primeFactors.card : ℝ) / B := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ (Real.log n / Real.log B) / B :=
      div_le_div_of_nonneg_right (primeFactors_card_le_log_div hB hrough) hBpos.le

/-- If every prime factor of `n` is at least `B > 1`, then
`∏_{p ∣ n} (1 + 4 / (p - 1)) ≤ exp (4 * (log n / log B) / (B - 1))`. -/
theorem prod_one_add_four_div_pred_le_exp {B : ℝ} {n : ℕ} (hB : 1 < B)
    (hrough : ∀ p ∈ n.primeFactors, B ≤ (p : ℝ)) :
    ∏ p ∈ n.primeFactors, (1 + 4 / ((p : ℝ) - 1)) ≤
      Real.exp (4 * (Real.log n / Real.log B) / (B - 1)) := by
  have hB1 : 0 < B - 1 := sub_pos.mpr hB
  calc
    ∏ p ∈ n.primeFactors, (1 + 4 / ((p : ℝ) - 1))
        ≤ ∏ _p ∈ n.primeFactors, Real.exp (4 / (B - 1)) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro p hp
        have hp1 : 0 < (p : ℝ) - 1 := hB1.trans_le (sub_le_sub_right (hrough p hp) 1)
        positivity
      · intro p hp
        have hsub : B - 1 ≤ (p : ℝ) - 1 := sub_le_sub_right (hrough p hp) 1
        have hdiv : 4 / ((p : ℝ) - 1) ≤ 4 / (B - 1) :=
          div_le_div_of_nonneg_left (by norm_num) hB1 hsub
        calc
          1 + 4 / ((p : ℝ) - 1) = 4 / ((p : ℝ) - 1) + 1 := add_comm _ _
          _ ≤ Real.exp (4 / ((p : ℝ) - 1)) := Real.add_one_le_exp _
          _ ≤ Real.exp (4 / (B - 1)) := Real.exp_le_exp.mpr hdiv
    _ = Real.exp (∑ _p ∈ n.primeFactors, 4 / (B - 1)) := by
      rw [Real.exp_sum]
    _ = Real.exp (4 * (n.primeFactors.card : ℝ) / (B - 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      ring
    _ ≤ Real.exp (4 * (Real.log n / Real.log B) / (B - 1)) := by
      apply Real.exp_le_exp.mpr
      have hcard := primeFactors_card_le_log_div hB hrough
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcard (by norm_num)) hB1.le

end RoughBranchArithmetic

section AsymptoticRoughRegime

/-- Logarithm of the rough-branch prime threshold: `(log n)^(2/3)`. -/
noncomputable def logB (n : ℕ) : ℝ :=
  (Real.log n) ^ (2/3 : ℝ)

/-- Rough-branch prime threshold `B_0(n) = exp((log n)^(2/3))`. -/
noncomputable def roughThreshold (n : ℕ) : ℝ :=
  Real.exp (logB n)

private theorem log_nat_grows : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem logLog_nat_grows : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
  tendsto_log_atTop.comp log_nat_grows

theorem logB_grows : Tendsto logB atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/3)).comp log_nat_grows

theorem roughThreshold_grows : Tendsto roughThreshold atTop atTop :=
  tendsto_exp_atTop.comp logB_grows

/-- On the rough branch `p_min ≥ exp(logB n)`, the prime-factor count bound
`log n / logB n` is `o(scale n)`. -/
theorem log_div_logB_isLittleO_scale :
    Asymptotics.IsLittleO atTop (fun n : ℕ => Real.log n / logB n) scale := by
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  have hrpow : Tendsto (fun n : ℕ => (Real.log (Real.log n)) ^ (2/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/3)).comp logLog_nat_grows
  filter_upwards [log_nat_grows.eventually_ge_atTop 1,
    logLog_nat_grows.eventually_ge_atTop 1,
    hrpow.eventually_ge_atTop (1 / ε)] with n hlog hloglog hbig
  have hlogpos : 0 < Real.log n := zero_lt_one.trans_le hlog
  have hlogBpos : 0 < logB n := rpow_pos_of_pos hlogpos _
  have hdiv : Real.log n / logB n = (Real.log n) ^ (1/3 : ℝ) := by
    rw [div_eq_iff hlogBpos.ne']
    unfold logB
    rw [← rpow_add hlogpos]
    norm_num
  have hpow13 : 0 ≤ (Real.log n) ^ (1/3 : ℝ) := rpow_nonneg hlogpos.le _
  have hscale0 : 0 ≤ scale n := by
    unfold scale
    exact mul_nonneg hpow13 (rpow_nonneg (zero_le_one.trans hloglog) _)
  have hone : 1 ≤ ε * (Real.log (Real.log n)) ^ (2/3 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hbig hε.le
    rwa [mul_one_div_cancel hε.ne'] at this
  rw [hdiv, Real.norm_of_nonneg hpow13, Real.norm_of_nonneg hscale0]
  unfold scale
  calc
    (Real.log n) ^ (1/3 : ℝ) = (Real.log n) ^ (1/3 : ℝ) * 1 := (mul_one _).symm
    _ ≤ (Real.log n) ^ (1/3 : ℝ) * (ε * (Real.log (Real.log n)) ^ (2/3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hone hpow13
    _ = ε * ((Real.log n) ^ (1/3 : ℝ) * (Real.log (Real.log n)) ^ (2/3 : ℝ)) := by ring

/-- For every fixed `k : ℕ`, `(log (2n))^k / exp(logB n) → 0`. This controls the
missing-class fraction `poly(log n) / p_min` on the rough branch. -/
theorem poly_log_two_mul_div_exp_logB_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => (Real.log (2 * n)) ^ k / Real.exp (logB n)) atTop (𝓝 0) := by
  have hupper :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ k * ((logB n) ^ (2 * k) * Real.exp (-logB n)))
        atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (logB n) ^ (2 * k) * Real.exp (-logB n)) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * k)).comp logB_grows
    simpa using h0.const_mul ((2 : ℝ) ^ k)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have h2n : (1 : ℝ) ≤ 2 * (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact div_nonneg (pow_nonneg (Real.log_nonneg h2n) k) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (2 : ℕ), logB_grows.eventually_ge_atTop 1] with n hn hB1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have h2_le_n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog2_le : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2_le_n
    have hlog_nonneg : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hlog2n : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log n := by
      rw [Real.log_mul (by norm_num) hn_pos.ne']
      linarith
    have hlog2n_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_nonneg (by linarith)
    have hlog_eq : Real.log n = (logB n) ^ (3/2 : ℝ) := by
      unfold logB
      rw [← rpow_mul hlog_nonneg]
      norm_num
    have hlog_le_sq : Real.log n ≤ (logB n) ^ 2 := by
      rw [hlog_eq]
      calc
        (logB n) ^ (3/2 : ℝ) ≤ (logB n) ^ (2 : ℝ) :=
          rpow_le_rpow_of_exponent_le hB1 (by norm_num)
        _ = (logB n) ^ 2 := by norm_cast
    have hpow : (Real.log (2 * (n : ℝ))) ^ k ≤ (2 : ℝ) ^ k * (logB n) ^ (2 * k) := by
      calc
        (Real.log (2 * (n : ℝ))) ^ k ≤ (2 * Real.log n) ^ k :=
          pow_le_pow_left₀ hlog2n_nonneg hlog2n k
        _ = (2 : ℝ) ^ k * (Real.log n) ^ k := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ k * ((logB n) ^ 2) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog_nonneg hlog_le_sq k) (by positivity)
        _ = (2 : ℝ) ^ k * (logB n) ^ (2 * k) := by rw [← pow_mul]
    rw [div_eq_mul_inv, ← Real.exp_neg, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le

/-- The `L_p[1/2, O(1)]` exponent at `p = exp(logB n)` is `o(scale n)`. -/
theorem sqrt_logB_mul_log_logB_isLittleO_scale :
    Asymptotics.IsLittleO atTop
      (fun n : ℕ => Real.sqrt (logB n * Real.log (logB n))) scale := by
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  have hrpow : Tendsto (fun n : ℕ => (Real.log (Real.log n)) ^ (1/6 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/6)).comp logLog_nat_grows
  filter_upwards [log_nat_grows.eventually_ge_atTop 1,
    logLog_nat_grows.eventually_ge_atTop 1,
    hrpow.eventually_ge_atTop (Real.sqrt (2/3 : ℝ) / ε)] with n hlog hloglog hbig
  have hlogpos : 0 < Real.log n := zero_lt_one.trans_le hlog
  have hloglogpos : 0 < Real.log (Real.log n) := zero_lt_one.trans_le hloglog
  have hlogB_pos : 0 < logB n := rpow_pos_of_pos hlogpos _
  have hlog_logB : Real.log (logB n) = (2/3 : ℝ) * Real.log (Real.log n) := by
    unfold logB
    exact Real.log_rpow hlogpos (2/3 : ℝ)
  have hsqrt_eq :
      Real.sqrt (logB n * Real.log (logB n)) =
        Real.sqrt (2/3 : ℝ) * (Real.log n) ^ (1/3 : ℝ) * (Real.log (Real.log n)) ^ (1/2 : ℝ) := by
    rw [hlog_logB, show logB n * ((2/3 : ℝ) * Real.log (Real.log n)) =
      (2/3 : ℝ) * logB n * Real.log (Real.log n) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    congr 1
    congr 1
    · rw [Real.sqrt_eq_rpow]
      unfold logB
      rw [← rpow_mul hlogpos.le]
      norm_num
    · rw [Real.sqrt_eq_rpow]
  have hcoeff : Real.sqrt (2/3 : ℝ) ≤ ε * (Real.log (Real.log n)) ^ (1/6 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hbig hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have hpow13 : 0 ≤ (Real.log n) ^ (1/3 : ℝ) := rpow_nonneg hlogpos.le _
  have hpow12 : 0 ≤ (Real.log (Real.log n)) ^ (1/2 : ℝ) := rpow_nonneg hloglogpos.le _
  have hscale0 : 0 ≤ scale n := by
    unfold scale
    exact mul_nonneg hpow13 (rpow_nonneg hloglogpos.le _)
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hscale0, hsqrt_eq]
  calc
    Real.sqrt (2/3 : ℝ) * (Real.log n) ^ (1/3 : ℝ) * (Real.log (Real.log n)) ^ (1/2 : ℝ)
        ≤ (ε * (Real.log (Real.log n)) ^ (1/6 : ℝ)) *
            (Real.log n) ^ (1/3 : ℝ) * (Real.log (Real.log n)) ^ (1/2 : ℝ) := by
      gcongr
    _ = ε * ((Real.log n) ^ (1/3 : ℝ) *
          ((Real.log (Real.log n)) ^ (1/2 : ℝ) * (Real.log (Real.log n)) ^ (1/6 : ℝ))) := by
      ring
    _ = ε * scale n := by
      unfold scale
      rw [← rpow_add hloglogpos]
      norm_num

/-- On the rough branch `p_min > exp(logB n)`, eventually `ω(n) ≤ ε * scale n`. -/
theorem eventually_rough_primeFactors_card_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, IsRough (roughThreshold n) n →
      (n.primeFactors.card : ℝ) ≤ ε * scale n := by
  filter_upwards [logB_grows.eventually_ge_atTop 1,
    log_div_logB_isLittleO_scale.def hε,
    scale_grows.eventually_ge_atTop 0] with n hB1 hsmall hs
  intro hrough
  have hthresh : 1 < roughThreshold n := by
    unfold roughThreshold
    exact Real.one_lt_exp_iff.mpr (by linarith)
  have hcard := primeFactors_card_le_log_div hthresh (isRough_le hrough)
  have hlog_thresh : Real.log (roughThreshold n) = logB n := Real.log_exp _
  rw [hlog_thresh] at hcard
  change ‖Real.log n / logB n‖ ≤ ε * ‖scale n‖ at hsmall
  rw [Real.norm_of_nonneg (div_nonneg (Real.log_natCast_nonneg n) (by linarith)),
    Real.norm_of_nonneg hs] at hsmall
  exact hcard.trans hsmall

/-- Any `exp(c * sqrt(logB n * log(logB n)))` prepass budget fits inside `exp(ε * scale n)`. -/
theorem eventually_exp_sqrt_logB_le_exp_scale {c ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (c * Real.sqrt (logB n * Real.log (logB n))) ≤ Real.exp (ε * scale n) := by
  have hδ : 0 < ε / (|c| + 1) := by positivity
  filter_upwards [sqrt_logB_mul_log_logB_isLittleO_scale.def hδ,
    scale_grows.eventually_ge_atTop 0] with n hsmall hs
  apply Real.exp_le_exp.mpr
  change ‖Real.sqrt (logB n * Real.log (logB n))‖ ≤ (ε / (|c| + 1)) * ‖scale n‖ at hsmall
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hs] at hsmall
  have hc : c ≤ |c| + 1 := (le_abs_self c).trans (by linarith)
  calc
    c * Real.sqrt (logB n * Real.log (logB n))
        ≤ (|c| + 1) * Real.sqrt (logB n * Real.log (logB n)) :=
      mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
    _ ≤ (|c| + 1) * (ε / (|c| + 1) * scale n) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = ε * scale n := by
      rw [← mul_assoc, mul_div_cancel₀ _ (by positivity)]

/-- On the rough branch `p_min > exp(logB n)`, the local root-sum Euler product
`∏_{p ∣ n} (1 + 4 / (p - 1))` is eventually at most `exp ε`. -/
theorem eventually_rough_prod_one_add_four_div_pred_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, IsRough (roughThreshold n) n →
      ∏ p ∈ n.primeFactors, (1 + 4 / ((p : ℝ) - 1)) ≤ Real.exp ε := by
  have htend := poly_log_two_mul_div_exp_logB_tendsto_zero 1
  have hsmall := (Metric.tendsto_atTop.mp htend) (ε / 8) (by positivity)
  obtain ⟨N₀, hN₀⟩ := hsmall
  filter_upwards [eventually_ge_atTop (max N₀ 2), logB_grows.eventually_ge_atTop 1,
    roughThreshold_grows.eventually_ge_atTop 2] with n hn hB1 hthresh2
  intro hrough
  have hthresh1 : 1 < roughThreshold n := by linarith
  have hprod := prod_one_add_four_div_pred_le_exp hthresh1 (isRough_le hrough)
  rw [show Real.log (roughThreshold n) = logB n from Real.log_exp _] at hprod
  refine hprod.trans (Real.exp_le_exp.mpr ?_)
  have hnN₀ : N₀ ≤ n := (le_max_left ..).trans hn
  have hn2 : 2 ≤ n := (le_max_right ..).trans hn
  have hdist := hN₀ n hnN₀
  rw [Real.dist_eq, sub_zero, pow_one] at hdist
  have hlog_le : Real.log n ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hratio_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) / Real.exp (logB n) :=
    div_nonneg (Real.log_nonneg (by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith)) (Real.exp_pos _).le
  rw [abs_of_nonneg hratio_nonneg] at hdist
  have hdiv_logB : Real.log n / logB n ≤ Real.log n :=
    div_le_self (Real.log_natCast_nonneg n) hB1
  have hhalf : roughThreshold n / 2 ≤ roughThreshold n - 1 := by linarith
  have hexp_pos : 0 < roughThreshold n := Real.exp_pos _
  calc
    4 * (Real.log n / logB n) / (roughThreshold n - 1)
        ≤ 4 * Real.log (2 * (n : ℝ)) / (roughThreshold n / 2) := by
      refine div_le_div₀ (mul_nonneg (by norm_num) ((Real.log_natCast_nonneg n).trans hlog_le))
        (mul_le_mul_of_nonneg_left (hdiv_logB.trans hlog_le) (by norm_num))
        (by positivity) hhalf
    _ = 8 * (Real.log (2 * (n : ℝ)) / Real.exp (logB n)) := by
      unfold roughThreshold
      ring
    _ ≤ 8 * (ε / 8) := by linarith
    _ = ε := by ring

end AsymptoticRoughRegime

section EpochComposition

/-- Independent product epoch running a prepass randomness draw and a main epoch draw. -/
noncomputable def combEpoch {α β : Type*} (preEpoch : PMF α) (mainEpoch : PMF β) :
    PMF (α × β) :=
  preEpoch.bind fun a => mainEpoch.map fun b => (a, b)

/-- Run `preAttempt` first; if it splits `n`, return immediately (charging `+1` for
the branch); otherwise run `mainAttempt` and return its result with accumulated cost. -/
def combAttempt {α β γ : Type*} (preAttempt : α → Option γ × ℕ)
    (mainAttempt : β → Option γ × ℕ) (ab : α × β) : Option γ × ℕ :=
  let r₁ := preAttempt ab.1
  match r₁.1 with
  | some y => (some y, r₁.2 + 1)
  | none =>
    let r₂ := mainAttempt ab.2
    (r₂.1, r₁.2 + 1 + r₂.2)

private theorem failFlag_le_one {γ : Type*} (o : Option γ) : failFlag o ≤ 1 := by
  cases o <;> simp [failFlag]

private theorem mean_failFlag_le_one {α γ : Type*} (p : PMF α) (f : α → Option γ × ℕ) :
    mean p (fun a => failFlag (f a).1) ≤ 1 := by
  rw [← mean_const p 1]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (failFlag_le_one (f a).1) (p a)

private theorem outerMeasure_success_le_one {α γ : Type*} (p : PMF α)
    (f : α → Option γ × ℕ) :
    (p.map f).toOuterMeasure {o | o.1 ≠ none} ≤ 1 := by
  rw [← one_sub_failure_eq_success p f]
  exact tsub_le_self

/-- Exact expected cost of the combined epoch: prepass cost plus failure-weighted main cost. -/
theorem combEpoch_mean_work_eq {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → Option γ × ℕ) (g : β → Option γ × ℕ) :
    mean (combEpoch p q) (fun ab => ((combAttempt f g ab).2 + 1 : ℕ)) =
      mean p (fun a => ((f a).2 + 1 : ℕ)) + 1 +
        mean p (fun a => failFlag (f a).1) * mean q (fun b => ((g b).2 : ℕ)) := by
  let z : ℝ≥0∞ := mean q (fun b => ((g b).2 : ℕ))
  have hmul :
      mean p (fun a => failFlag (f a).1 * z) =
        mean p (fun a => failFlag (f a).1) * z := by
    simp only [mean, ← mul_assoc, ENNReal.tsum_mul_right]
  rw [combEpoch, mean_bind]
  have hinner :
      (fun a => mean (q.map fun b => (a, b)) (fun ab => ((combAttempt f g ab).2 + 1 : ℕ))) =
      (fun a => (((f a).2 + 1 : ℕ) : ℝ≥0∞) + 1 + failFlag (f a).1 * z) := by
    funext a
    rw [mean_map]
    cases h : (f a).1 with
    | some y =>
      simp only [combAttempt, h, failFlag, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
      rw [mean_const]
    | none =>
      simp only [combAttempt, h, failFlag, one_mul, Nat.cast_add, Nat.cast_one]
      have hrew :
          (fun b => (((f a).2 : ℝ≥0∞) + 1 + ((g b).2 : ℝ≥0∞) + 1)) =
          (fun b => (((f a).2 : ℝ≥0∞) + 1 + 1) + ((g b).2 : ℝ≥0∞)) := by
        funext b; ring
      rw [hrew, mean_add, mean_const]
  rw [hinner, mean_add, mean_add, mean_const, hmul]

/-- Universal expected-work upper bound for the combined epoch. -/
theorem combEpoch_mean_work_le {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → Option γ × ℕ) (g : β → Option γ × ℕ) :
    mean (combEpoch p q) (fun ab => ((combAttempt f g ab).2 + 1 : ℕ)) + 1 ≤
      (mean p (fun a => ((f a).2 + 1 : ℕ)) + 1) +
        (mean q (fun b => ((g b).2 + 1 : ℕ)) + 1) := by
  rw [combEpoch_mean_work_eq]
  have hf := mean_failFlag_le_one p f
  have hq : 1 + mean p (fun a => failFlag (f a).1) * mean q (fun b => ((g b).2 : ℕ)) ≤
      mean q (fun b => ((g b).2 + 1 : ℕ)) + 1 := by
    calc
      1 + mean p (fun a => failFlag (f a).1) * mean q (fun b => ((g b).2 : ℕ))
          ≤ 1 + 1 * mean q (fun b => ((g b).2 : ℕ)) :=
        add_le_add le_rfl (mul_le_mul_left hf _)
      _ = mean q (fun b => ((g b).2 : ℕ)) + 1 := by rw [one_mul, add_comm]
      _ ≤ mean q (fun b => ((g b).2 + 1 : ℕ)) + 1 := by
        refine add_le_add ?_ le_rfl
        refine ENNReal.tsum_le_tsum fun b => mul_le_mul_right ?_ (q b)
        exact Nat.cast_le.mpr (Nat.le_succ _)
  calc
    mean p (fun a => ((f a).2 + 1 : ℕ)) + 1 +
        mean p (fun a => failFlag (f a).1) * mean q (fun b => ((g b).2 : ℕ)) + 1
        = (mean p (fun a => ((f a).2 + 1 : ℕ)) + 1) +
            (1 + mean p (fun a => failFlag (f a).1) * mean q (fun b => ((g b).2 : ℕ))) := by
      ring
    _ ≤ (mean p (fun a => ((f a).2 + 1 : ℕ)) + 1) +
          (mean q (fun b => ((g b).2 + 1 : ℕ)) + 1) :=
      add_le_add le_rfl hq

/-- If the prepass succeeds with probability `1`, the main epoch is never invoked. -/
theorem combEpoch_mean_work_of_pre_sure {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → Option γ × ℕ) (g : β → Option γ × ℕ)
    (hsure : (p.map f).toOuterMeasure {o | o.1 ≠ none} = 1) :
    mean (combEpoch p q) (fun ab => ((combAttempt f g ab).2 + 1 : ℕ)) + 1 =
      (mean p (fun a => ((f a).2 + 1 : ℕ)) + 1) + 1 := by
  rw [← one_sub_failure_eq_success p f] at hsure
  have hfail : mean p (fun a => failFlag (f a).1) = 0 := by
    by_contra hne
    have hlt : 1 - mean p (fun a => failFlag (f a).1) < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hne
    exact hlt.ne hsure
  rw [combEpoch_mean_work_eq, hfail, zero_mul, add_zero]

/-- Exact failure probability of the combined epoch: product of the two failure probabilities. -/
theorem combEpoch_fail_eq {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → Option γ × ℕ) (g : β → Option γ × ℕ) :
    mean (combEpoch p q) (fun ab => failFlag (combAttempt f g ab).1) =
      mean p (fun a => failFlag (f a).1) * mean q (fun b => failFlag (g b).1) := by
  let fq := mean q (fun b => failFlag (g b).1)
  have hmul : mean p (fun a => failFlag (f a).1 * fq) =
      mean p (fun a => failFlag (f a).1) * fq := by
    simp only [mean, ← mul_assoc, ENNReal.tsum_mul_right]
  rw [combEpoch, mean_bind, ← hmul]
  congr 1
  funext a
  rw [mean_map]
  cases h : (f a).1 with
  | some y =>
    simp only [combAttempt, h, failFlag, zero_mul]
    exact mean_const q 0
  | none =>
    simp only [combAttempt, h, failFlag, one_mul]
    rfl

theorem combEpoch_success_ge_pre {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → Option γ × ℕ) (g : β → Option γ × ℕ) :
    (p.map f).toOuterMeasure {o | o.1 ≠ none} ≤
      ((combEpoch p q).map (combAttempt f g)).toOuterMeasure {o | o.1 ≠ none} := by
  rw [← one_sub_failure_eq_success, ← one_sub_failure_eq_success, combEpoch_fail_eq]
  refine tsub_le_tsub_left ?_ 1
  calc
    mean p (fun a => failFlag (f a).1) * mean q (fun b => failFlag (g b).1)
        ≤ mean p (fun a => failFlag (f a).1) * 1 :=
      mul_le_mul_right (mean_failFlag_le_one q g) _
    _ = mean p (fun a => failFlag (f a).1) := mul_one _

theorem combEpoch_success_ge_main {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → Option γ × ℕ) (g : β → Option γ × ℕ) :
    (q.map g).toOuterMeasure {o | o.1 ≠ none} ≤
      ((combEpoch p q).map (combAttempt f g)).toOuterMeasure {o | o.1 ≠ none} := by
  rw [← one_sub_failure_eq_success, ← one_sub_failure_eq_success, combEpoch_fail_eq]
  refine tsub_le_tsub_left ?_ 1
  calc
    mean p (fun a => failFlag (f a).1) * mean q (fun b => failFlag (g b).1)
        ≤ 1 * mean q (fun b => failFlag (g b).1) :=
      mul_le_mul_left (mean_failFlag_le_one p f) _
    _ = mean q (fun b => failFlag (g b).1) := one_mul _

theorem combEpoch_success_toReal_ge_pre {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → Option γ × ℕ) (g : β → Option γ × ℕ) :
    ((p.map f).toOuterMeasure {o | o.1 ≠ none}).toReal ≤
      (((combEpoch p q).map (combAttempt f g)).toOuterMeasure {o | o.1 ≠ none}).toReal :=
  ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (outerMeasure_success_le_one _ _))
    (combEpoch_success_ge_pre p q f g)

theorem combEpoch_success_toReal_ge_main {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → Option γ × ℕ) (g : β → Option γ × ℕ) :
    ((q.map g).toOuterMeasure {o | o.1 ≠ none}).toReal ≤
      (((combEpoch p q).map (combAttempt f g)).toOuterMeasure {o | o.1 ≠ none}).toReal :=
  ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (outerMeasure_success_le_one _ _))
    (combEpoch_success_ge_main p q f g)

private theorem one_le_of_mean_succ_add_one_le {α γ : Type*} (q : PMF α)
    (g : α → Option γ × ℕ) {W : ℝ}
    (hW : mean q (fun b => ((g b).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W) :
    1 ≤ W := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal W := (le_add_left le_rfl).trans hW
  rw [← ENNReal.ofReal_one] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (by
    by_contra h
    push Not at h
    rw [ENNReal.ofReal_of_nonpos h.le] at h1
    simp at h1)).mp h1

/-- General prepass + rough-branch epoch combiner:
Given a prepass of cost `exp(o(scale n))` that handles inputs with a prime factor `≤ B n`
(either with probability `1`, or with inverse success probability `≤ exp(o(scale n))`
when the main epoch also has expected cost `≤ exp((C + δ) * scale n)`), and a main epoch
achieving ratio `≤ exp((C + δ) * scale n)` on `B n`-rough hard inputs, the combined epoch
achieves ratio `≤ exp((C + δ) * scale n)` on ALL hard inputs. -/
theorem combined_epoch_asymptotic {α β : ℕ → Type}
    (B : ℕ → ℝ)
    (preEpoch : ∀ n, PMF (α n)) (preAttempt : ∀ n, α n → Option (Factors n) × ℕ)
    (mainEpoch : ∀ n, PMF (β n)) (mainAttempt : ∀ n, β n → Option (Factors n) × ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hPreWork : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      mean (preEpoch n) (fun a => ((preAttempt n a).2 + 1 : ℕ)) + 1 ≤
        ENNReal.ofReal (Real.exp (ε * scale n)))
    (hSmall : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n → HasSmallPrimeFactor (B n) n →
      ∃ S_pre : ℝ, 0 < S_pre ∧
        S_pre ≤ (((preEpoch n).map (preAttempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        1 / S_pre ≤ Real.exp (δ * scale n) ∧
        (1 ≤ S_pre ∨
          mean (mainEpoch n) (fun b => ((mainAttempt n b).2 + 1 : ℕ)) + 1 ≤
            ENNReal.ofReal (Real.exp ((C + δ) * scale n))))
    (hRough : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n → IsRough (B n) n →
      ∃ W S : ℝ, 0 < S ∧
        mean (mainEpoch n) (fun b => ((mainAttempt n b).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
        S ≤ (((mainEpoch n).map (mainAttempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        W / S ≤ Real.exp ((C + δ) * scale n)) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      ∃ W S : ℝ, 0 < S ∧
        mean (combEpoch (preEpoch n) (mainEpoch n))
          (fun ab => ((combAttempt (preAttempt n) (mainAttempt n) ab).2 + 1 : ℕ)) + 1 ≤
          ENNReal.ofReal W ∧
        S ≤ (((combEpoch (preEpoch n) (mainEpoch n)).map
          (combAttempt (preAttempt n) (mainAttempt n))).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        W / S ≤ Real.exp ((C + δ) * scale n) := by
  intro δ hδ
  have hδ4 : 0 < δ / 4 := by positivity
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [hPreWork (δ / 4) hδ4, hSmall (δ / 4) hδ4, hRough (δ / 4) hδ4,
    scale_grows.eventually_ge_atTop (max 0 (Real.log 2 / (δ / 2)))]
    with n hpw hsm hrg hs_big
  intro hodd hnotprime hnotpp
  have hs0 : 0 ≤ scale n := (le_max_left ..).trans hs_big
  have htwo_le : (2 : ℝ) ≤ Real.exp (δ / 2 * scale n) := by
    have hlog2 : Real.log 2 ≤ δ / 2 * scale n := by
      have h1 := (le_max_right 0 (Real.log 2 / (δ / 2))).trans hs_big
      have h2 := (div_le_iff₀ hδ2).mp h1
      linarith
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (δ / 2 * scale n) := Real.exp_le_exp.mpr hlog2
  have hpre_work := hpw hodd hnotprime hnotpp
  have hexp_ge_one : (1 : ℝ) ≤ Real.exp (δ / 4 * scale n) :=
    Real.one_le_exp (mul_nonneg hδ4.le hs0)
  rcases hasSmallPrimeFactor_or_isRough (B n) n with hsmall | hrough
  · obtain ⟨S_pre, hS_pos, hS_prob, hS_inv, hsure_or_main⟩ :=
      hsm hodd hnotprime hnotpp hsmall
    rcases hsure_or_main with hsure | hmain_work
    · have hmu_le : ((preEpoch n).map (preAttempt n)).toOuterMeasure {o | o.1 ≠ none} ≤ 1 :=
        outerMeasure_success_le_one _ _
      have hmu_ne_top : ((preEpoch n).map (preAttempt n)).toOuterMeasure {o | o.1 ≠ none} ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hmu_le
      have hmu_ge : (1 : ℝ≥0∞) ≤
          ((preEpoch n).map (preAttempt n)).toOuterMeasure {o | o.1 ≠ none} := by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_le_iff_le_toReal hmu_ne_top).mpr (hsure.trans hS_prob)
      have hmu_eq : ((preEpoch n).map (preAttempt n)).toOuterMeasure {o | o.1 ≠ none} = 1 :=
        le_antisymm hmu_le hmu_ge
      refine ⟨Real.exp (δ / 4 * scale n) + 1, S_pre, hS_pos, ?_,
        hS_prob.trans (combEpoch_success_toReal_ge_pre ..), ?_⟩
      · rw [combEpoch_mean_work_of_pre_sure (preEpoch n) (mainEpoch n)
          (preAttempt n) (mainAttempt n) hmu_eq]
        rw [ENNReal.ofReal_add (Real.exp_pos _).le zero_le_one, ENNReal.ofReal_one]
        exact add_le_add hpre_work le_rfl
      · calc
          (Real.exp (δ / 4 * scale n) + 1) / S_pre
              ≤ (Real.exp (δ / 4 * scale n) + 1) / 1 :=
            div_le_div_of_nonneg_left (by positivity) zero_lt_one hsure
          _ = Real.exp (δ / 4 * scale n) + 1 := div_one _
          _ ≤ 2 * Real.exp (δ / 4 * scale n) := by linarith
          _ ≤ Real.exp (δ / 2 * scale n) * Real.exp (δ / 4 * scale n) :=
            mul_le_mul_of_nonneg_right htwo_le (Real.exp_pos _).le
          _ = Real.exp ((3 * δ / 4) * scale n) := by
            rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp ((C + δ) * scale n) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hs0)
    · refine ⟨Real.exp (δ / 4 * scale n) + Real.exp ((C + δ / 4) * scale n), S_pre, hS_pos, ?_,
        hS_prob.trans (combEpoch_success_toReal_ge_pre ..), ?_⟩
      · refine (combEpoch_mean_work_le ..).trans ?_
        rw [ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        exact add_le_add hpre_work hmain_work
      · have hle_exp : Real.exp (δ / 4 * scale n) ≤ Real.exp ((C + δ / 4) * scale n) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hs0)
        calc
          (Real.exp (δ / 4 * scale n) + Real.exp ((C + δ / 4) * scale n)) / S_pre
              = (Real.exp (δ / 4 * scale n) + Real.exp ((C + δ / 4) * scale n)) * (1 / S_pre) := by
            rw [mul_one_div]
          _ ≤ (2 * Real.exp ((C + δ / 4) * scale n)) * Real.exp (δ / 4 * scale n) :=
            mul_le_mul (by linarith) hS_inv (by positivity) (by positivity)
          _ = 2 * Real.exp ((C + δ / 2) * scale n) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2; ring
          _ ≤ Real.exp (δ / 2 * scale n) * Real.exp ((C + δ / 2) * scale n) :=
            mul_le_mul_of_nonneg_right htwo_le (Real.exp_pos _).le
          _ = Real.exp ((C + δ) * scale n) := by
            rw [← Real.exp_add]; congr 1; ring
  · obtain ⟨W_m, S_m, hSm_pos, hWm_work, hSm_prob, hratio⟩ :=
      hrg hodd hnotprime hnotpp hrough
    have hWm_ge_one : 1 ≤ W_m := one_le_of_mean_succ_add_one_le _ _ hWm_work
    refine ⟨Real.exp (δ / 4 * scale n) + W_m, S_m, hSm_pos, ?_,
      hSm_prob.trans (combEpoch_success_toReal_ge_main ..), ?_⟩
    · refine (combEpoch_mean_work_le ..).trans ?_
      rw [ENNReal.ofReal_add (Real.exp_pos _).le (zero_le_one.trans hWm_ge_one)]
      exact add_le_add hpre_work hWm_work
    · calc
        (Real.exp (δ / 4 * scale n) + W_m) / S_m
            ≤ (Real.exp (δ / 4 * scale n) * W_m + W_m) / S_m := by
          apply div_le_div_of_nonneg_right _ hSm_pos.le
          have : Real.exp (δ / 4 * scale n) ≤ Real.exp (δ / 4 * scale n) * W_m :=
            le_mul_of_one_le_right (Real.exp_pos _).le hWm_ge_one
          linarith
        _ = (Real.exp (δ / 4 * scale n) + 1) * (W_m / S_m) := by ring
        _ ≤ (2 * Real.exp (δ / 4 * scale n)) * Real.exp ((C + δ / 4) * scale n) :=
          mul_le_mul (by linarith) hratio (div_nonneg (zero_le_one.trans hWm_ge_one) hSm_pos.le)
            (by positivity)
        _ = 2 * Real.exp ((C + δ / 2) * scale n) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2; ring
        _ ≤ Real.exp (δ / 2 * scale n) * Real.exp ((C + δ / 2) * scale n) :=
          mul_le_mul_of_nonneg_right htwo_le (Real.exp_pos _).le
        _ = Real.exp ((C + δ) * scale n) := by
          rw [← Real.exp_add]; congr 1; ring

/-- Specialization of `combined_epoch_asymptotic` to the canonical threshold
`roughThreshold n = exp((log n)^(2/3))`. -/
theorem combined_epoch_asymptotic_logB {α β : ℕ → Type}
    (preEpoch : ∀ n, PMF (α n)) (preAttempt : ∀ n, α n → Option (Factors n) × ℕ)
    (mainEpoch : ∀ n, PMF (β n)) (mainAttempt : ∀ n, β n → Option (Factors n) × ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hPreWork : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      mean (preEpoch n) (fun a => ((preAttempt n a).2 + 1 : ℕ)) + 1 ≤
        ENNReal.ofReal (Real.exp (ε * scale n)))
    (hSmall : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n → HasSmallPrimeFactor (roughThreshold n) n →
      ∃ S_pre : ℝ, 0 < S_pre ∧
        S_pre ≤ (((preEpoch n).map (preAttempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        1 / S_pre ≤ Real.exp (δ * scale n) ∧
        (1 ≤ S_pre ∨
          mean (mainEpoch n) (fun b => ((mainAttempt n b).2 + 1 : ℕ)) + 1 ≤
            ENNReal.ofReal (Real.exp ((C + δ) * scale n))))
    (hRough : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n → IsRough (roughThreshold n) n →
      ∃ W S : ℝ, 0 < S ∧
        mean (mainEpoch n) (fun b => ((mainAttempt n b).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
        S ≤ (((mainEpoch n).map (mainAttempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        W / S ≤ Real.exp ((C + δ) * scale n)) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      ∃ W S : ℝ, 0 < S ∧
        mean (combEpoch (preEpoch n) (mainEpoch n))
          (fun ab => ((combAttempt (preAttempt n) (mainAttempt n) ab).2 + 1 : ℕ)) + 1 ≤
          ENNReal.ofReal W ∧
        S ≤ (((combEpoch (preEpoch n) (mainEpoch n)).map
          (combAttempt (preAttempt n) (mainAttempt n))).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        W / S ≤ Real.exp ((C + δ) * scale n) :=
  combined_epoch_asymptotic roughThreshold preEpoch preAttempt mainEpoch mainAttempt
    hC hPreWork hSmall hRough

/-- Direct wiring of the combined prepass + rough-branch epoch into the full recursive
factorization driver `RandomizedInputDriver.factor_expected_from_epoch`. -/
theorem factor_expected_from_prepass_and_rough_epoch {α β : ℕ → Type}
    [∀ n, Fintype (α n)] [∀ n, Fintype (β n)]
    (k : ℕ) (prep : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n ∧
      (RandomizedPreprocessing.run k n).2 ≤ (10000 * (k + 1)) ^ 32 * (n.log2 + 2) ^ 32)
    (B : ℕ → ℝ)
    (preEpoch : ∀ n, PMF (α n)) (preAttempt : ∀ n, α n → Option (Factors n) × ℕ)
    (mainEpoch : ∀ n, PMF (β n)) (mainAttempt : ∀ n, β n → Option (Factors n) × ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hPreWork : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      mean (preEpoch n) (fun a => ((preAttempt n a).2 + 1 : ℕ)) + 1 ≤
        ENNReal.ofReal (Real.exp (ε * scale n)))
    (hSmall : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n → HasSmallPrimeFactor (B n) n →
      ∃ S_pre : ℝ, 0 < S_pre ∧
        S_pre ≤ (((preEpoch n).map (preAttempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        1 / S_pre ≤ Real.exp (δ * scale n) ∧
        (1 ≤ S_pre ∨
          mean (mainEpoch n) (fun b => ((mainAttempt n b).2 + 1 : ℕ)) + 1 ≤
            ENNReal.ofReal (Real.exp ((C + δ) * scale n))))
    (hRough : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n → IsRough (B n) n →
      ∃ W S : ℝ, 0 < S ∧
        mean (mainEpoch n) (fun b => ((mainAttempt n b).2 + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
        S ≤ (((mainEpoch n).map (mainAttempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        W / S ≤ Real.exp ((C + δ) * scale n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (factor k (fun m hm => (prep m hm).1)
        (epochHard (fun n => combEpoch (preEpoch n) (mainEpoch n))
          (fun n => combAttempt (preAttempt n) (mainAttempt n))) n hn)
        (fun out => out.2) ≤ ENNReal.ofReal (Real.exp ((C + ε) * scale n)) :=
  factor_expected_from_epoch k prep
    (fun n => combEpoch (preEpoch n) (mainEpoch n))
    (fun n => combAttempt (preAttempt n) (mainAttempt n))
    hC
    (combined_epoch_asymptotic B preEpoch preAttempt mainEpoch mainAttempt
      hC hPreWork hSmall hRough)

end EpochComposition

section CountedTrialDivisionPrepass

/-- Test a single candidate divisor `d ≤ n` using `RandomizedSplitVerification.verify`
and package any verified split into `Factors n`. -/
def checkDivisor (n d : ℕ) (hn : 0 < n) (hdn : d ≤ n) : Option (Factors n) × ℕ :=
  let res := verify n d
  match hres : res.1 with
  | none => (none, res.2 + 1)
  | some qword =>
    have hprop : TwoThirdsSearch.ProperDivisor n d := by
      have hspec := (verify_spec hn (Nat.size_le_size hdn)).1
      have hsome : some (value qword) =
          (open scoped Classical in
            if TwoThirdsSearch.ProperDivisor n d then some (n / d) else none) := by
        rw [show (verify n d).1 = some qword from hres] at hspec
        exact hspec
      by_contra hnot
      rw [if_neg hnot] at hsome
      simp at hsome
    have hq : value qword = n / d := by
      have hspec := (verify_spec hn (Nat.size_le_size hdn)).1
      have hsome : some (value qword) =
          (open scoped Classical in
            if TwoThirdsSearch.ProperDivisor n d then some (n / d) else none) := by
        rw [show (verify n d).1 = some qword from hres] at hspec
        exact hspec
      rw [if_pos hprop] at hsome
      exact Option.some.inj hsome
    have hprod : d * value qword = n := by
      rw [hq, Nat.mul_div_cancel' hprop.2.2]
    have hd2 : 2 ≤ d := hprop.1
    have hq2 : 2 ≤ value qword := by
      by_contra hlt
      have hle : value qword ≤ 1 := by omega
      have hmul : d * value qword ≤ d * 1 := Nat.mul_le_mul_left d hle
      have : n ≤ d := by linarith
      exact hprop.2.1.not_ge this
    (some ⟨(d, value qword), hd2, hq2, hprod⟩, res.2 + 1)

theorem checkDivisor_spec {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    ((checkDivisor n d hn hdn).1 ≠ none ↔ TwoThirdsSearch.ProperDivisor n d) ∧
      (checkDivisor n d hn hdn).2 ≤ verifierBudget n + 1 := by
  obtain ⟨hval, hcost⟩ := verify_spec hn (Nat.size_le_size hdn)
  unfold checkDivisor
  dsimp only
  split
  next hres =>
    rw [hres] at hval
    simp only [Option.map_none] at hval
    refine ⟨?_, Nat.add_le_add_right hcost 1⟩
    simp only [ne_eq, not_true_eq_false, false_iff]
    intro hprop
    rw [if_pos hprop] at hval
    simp at hval
  next qword hres =>
    rw [hres] at hval
    simp only [Option.map_some] at hval
    refine ⟨?_, Nat.add_le_add_right hcost 1⟩
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    by_contra hnot
    rw [if_neg hnot] at hval
    simp at hval

/-- Scan candidate divisors from `m` down to `2`, stopping on the first verified proper
divisor. -/
def trialPrepassAux (n : ℕ) (hn : 0 < n) : (m : ℕ) → m ≤ n → Option (Factors n) × ℕ
  | 0, _ => (none, 0)
  | 1, _ => (none, 0)
  | m + 2, hm =>
    let step := checkDivisor n (m + 2) hn hm
    match step.1 with
    | some fac => (some fac, step.2)
    | none =>
      let rest := trialPrepassAux n hn (m + 1) (by omega)
      (rest.1, step.2 + rest.2)

theorem trialPrepassAux_work_le (n : ℕ) (hn : 0 < n) :
    ∀ (m : ℕ) (hm : m ≤ n), (trialPrepassAux n hn m hm).2 ≤ m * (verifierBudget n + 1)
  | 0, _ => by simp [trialPrepassAux]
  | 1, _ => by simp [trialPrepassAux]
  | m + 2, hm => by
    unfold trialPrepassAux
    dsimp only
    have hstep := (checkDivisor_spec hn hm).2
    cases h : (checkDivisor n (m + 2) hn hm).1 with
    | some fac =>
      dsimp only
      calc
        (checkDivisor n (m + 2) hn hm).2 ≤ 1 * (verifierBudget n + 1) := by simpa using hstep
        _ ≤ (m + 2) * (verifierBudget n + 1) :=
          Nat.mul_le_mul_right _ (by omega)
    | none =>
      dsimp only
      have ih := trialPrepassAux_work_le n hn (m + 1) (by omega)
      calc
        (checkDivisor n (m + 2) hn hm).2 + (trialPrepassAux n hn (m + 1) (by omega)).2
            ≤ (verifierBudget n + 1) + (m + 1) * (verifierBudget n + 1) :=
          Nat.add_le_add hstep ih
        _ = (m + 2) * (verifierBudget n + 1) := by ring

theorem trialPrepassAux_complete {n : ℕ} (hn : 0 < n) :
    ∀ {m : ℕ} (hm : m ≤ n) {d : ℕ},
      TwoThirdsSearch.ProperDivisor n d → d ≤ m → (trialPrepassAux n hn m hm).1 ≠ none
  | 0, _, d, hd, hdm => by have := hd.1; omega
  | 1, _, d, hd, hdm => by have := hd.1; omega
  | m + 2, hm, d, hd, hdm => by
    unfold trialPrepassAux
    dsimp only
    cases h : (checkDivisor n (m + 2) hn hm).1 with
    | some fac => simp
    | none =>
      dsimp only
      have hne : d ≠ m + 2 := by
        intro heq
        subst heq
        exact ((checkDivisor_spec hn hm).1.mpr hd) h
      exact trialPrepassAux_complete hn (by omega) hd (by omega)

/-- Concrete counted bounded trial-division prepass testing all candidate divisors
`2 ≤ d ≤ min B n` via `RandomizedSplitVerification.verify`. -/
def trialPrepass (B n : ℕ) : Option (Factors n) × ℕ :=
  if hn : 2 ≤ n then
    trialPrepassAux n (by omega) (min B n) (Nat.min_le_right B n)
  else
    (none, 0)

/-- Exact quadratic-in-bit-length gate cost bound `O(B * n.size^2)` for `trialPrepass`. -/
theorem trialPrepass_work_le (B n : ℕ) :
    (trialPrepass B n).2 ≤ 54 * B * n.size ^ 2 := by
  unfold trialPrepass
  split_ifs with hn
  · have hpos : 0 < n := by omega
    have haux := trialPrepassAux_work_le n hpos (min B n) (Nat.min_le_right B n)
    have hquad := verifierBudget_le_quadratic hpos
    have hs1 : 1 ≤ n.size := Nat.size_pos.mpr hpos
    have hs2 : 1 ≤ n.size ^ 2 := by
      simpa using Nat.pow_le_pow_left hs1 2
    have hbud : verifierBudget n + 1 ≤ 54 * n.size ^ 2 := by omega
    calc
      (trialPrepassAux n hpos (min B n) (Nat.min_le_right B n)).2
          ≤ min B n * (verifierBudget n + 1) := haux
      _ ≤ B * (54 * n.size ^ 2) := Nat.mul_le_mul (Nat.min_le_left B n) hbud
      _ = 54 * B * n.size ^ 2 := by ring
  · exact Nat.zero_le _

/-- `trialPrepass B n` splits every composite `n` having a prime factor `p ≤ B`. -/
theorem trialPrepass_splits_of_small_prime {B n p : ℕ} (hn : 2 ≤ n) (hcomp : ¬ n.Prime)
    (hp : p ∈ n.primeFactors) (hpB : p ≤ B) :
    (trialPrepass B n).1 ≠ none := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hp_le_n : p ≤ n := Nat.le_of_dvd (by omega) hp_dvd
  have hp_lt_n : p < n := lt_of_le_of_ne hp_le_n fun heq => hcomp (heq ▸ hp_prime)
  have hprop : TwoThirdsSearch.ProperDivisor n p := ⟨hp_prime.one_lt, hp_lt_n, hp_dvd⟩
  unfold trialPrepass
  rw [dif_pos hn]
  exact trialPrepassAux_complete (by omega) (Nat.min_le_right B n) hprop
    (le_min hpB hp_le_n)

theorem trialPrepass_splits_of_hasSmallPrimeFactor {B n : ℕ} (hn : 2 ≤ n) (hcomp : ¬ n.Prime)
    (hsmall : HasSmallPrimeFactor (B : ℝ) n) :
    (trialPrepass B n).1 ≠ none := by
  obtain ⟨p, hp, hpB⟩ := hsmall
  exact trialPrepass_splits_of_small_prime hn hcomp hp (by exact_mod_cast hpB)

/-- Trivial deterministic epoch wrapper for `trialPrepass`. -/
noncomputable def trialPrepassEpoch (_n : ℕ) : PMF Unit :=
  PMF.pure ()

def trialPrepassAttempt (B : ℕ → ℕ) (n : ℕ) (_ : Unit) : Option (Factors n) × ℕ :=
  trialPrepass (B n) n

/-- On every composite input having a prime factor `≤ B`, `trialPrepass` succeeds with
probability `1`. -/
theorem trialPrepass_success_prob_one {B n : ℕ} (hn : 2 ≤ n) (hcomp : ¬ n.Prime)
    (hsmall : HasSmallPrimeFactor (B : ℝ) n) :
    (((PMF.pure ()).map (fun _ : Unit => trialPrepass B n)).toOuterMeasure {o | o.1 ≠ none}) = 1 := by
  have hsplit := trialPrepass_splits_of_hasSmallPrimeFactor hn hcomp hsmall
  rw [← one_sub_failure_eq_success, mean_pure]
  cases h : (trialPrepass B n).1 with
  | none => exact absurd h hsplit
  | some fac => simp [failFlag]

/-- Whenever the trial-division cutoff `B n` grows sub-exponentially in `scale n`,
the counted `trialPrepass` has expected epoch cost `≤ exp(ε * scale n)`. -/
theorem trialPrepass_mean_work_le_exp {B : ℕ → ℕ}
    (hB : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (B n : ℝ) ≤ Real.exp (ε * scale n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      mean (trialPrepassEpoch n) (fun a => ((trialPrepassAttempt B n a).2 + 1 : ℕ)) + 1 ≤
        ENNReal.ofReal (Real.exp (ε * scale n)) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [eventually_ge_atTop (2 : ℕ), hB (ε / 2) hε2,
    eventually_bitPoly_le_exp (A := 56) hε2 2,
    scale_grows.eventually_ge_atTop 0] with n hn hBn hpoly hs0
  rw [trialPrepassEpoch, mean_pure]
  have hwork : (trialPrepass (B n) n).2 ≤ 54 * B n * n.size ^ 2 :=
    trialPrepass_work_le (B n) n
  have hsize : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  have hbits_ge1 : (1 : ℝ) ≤ (n.log2 : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) n.log2]
  have hworkR : (((trialPrepass (B n) n).2 + 1 : ℕ) : ℝ) + 1 ≤
      Real.exp (ε * scale n) := by
    have h1 : ((trialPrepass (B n) n).2 : ℝ) ≤ 54 * (B n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 := by
      have hcast : ((trialPrepass (B n) n).2 : ℝ) ≤ 54 * (B n : ℝ) * (n.size : ℝ) ^ 2 := by
        exact_mod_cast hwork
      have hsR : (n.size : ℝ) ≤ (n.log2 : ℝ) + 1 := by exact_mod_cast hsize
      exact hcast.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hsR 2) (by positivity))
    have hBge : (B n : ℝ) ≤ Real.exp (ε / 2 * scale n) := hBn
    have hexp1 : (1 : ℝ) ≤ Real.exp (ε / 2 * scale n) :=
      Real.one_le_exp (mul_nonneg hε2.le hs0)
    have hsq1 : (1 : ℝ) ≤ ((n.log2 : ℝ) + 1) ^ 2 := one_le_pow₀ hbits_ge1
    calc
      (((trialPrepass (B n) n).2 + 1 : ℕ) : ℝ) + 1
          = ((trialPrepass (B n) n).2 : ℝ) + 2 := by push_cast; ring
      _ ≤ 54 * (B n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 + 2 := by linarith
      _ ≤ 54 * Real.exp (ε / 2 * scale n) * ((n.log2 : ℝ) + 1) ^ 2 +
            2 * Real.exp (ε / 2 * scale n) * ((n.log2 : ℝ) + 1) ^ 2 := by
        refine add_le_add ?_ ?_
        · gcongr
        · have : (1 : ℝ) ≤ Real.exp (ε / 2 * scale n) * ((n.log2 : ℝ) + 1) ^ 2 :=
            one_le_mul_of_one_le_of_one_le hexp1 hsq1
          linarith
      _ = (56 * ((n.log2 : ℝ) + 1) ^ 2) * Real.exp (ε / 2 * scale n) := by ring
      _ ≤ Real.exp (ε / 2 * scale n) * Real.exp (ε / 2 * scale n) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = Real.exp (ε * scale n) := by
        rw [← Real.exp_add]; congr 1; ring
  have hcast_eq :
      ((((trialPrepassAttempt B n ()).2 + 1 : ℕ) : ℝ≥0∞) + 1) =
        ENNReal.ofReal ((((trialPrepass (B n) n).2 + 1 : ℕ) : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
    rfl
  rw [hcast_eq]
  exact ENNReal.ofReal_le_ofReal hworkR

end CountedTrialDivisionPrepass

#print axioms pow_primeFactors_card_le
#print axioms primeFactors_card_le_log_div
#print axioms sum_inv_primeFactors_le
#print axioms prod_one_add_four_div_pred_le_exp
#print axioms log_div_logB_isLittleO_scale
#print axioms poly_log_two_mul_div_exp_logB_tendsto_zero
#print axioms sqrt_logB_mul_log_logB_isLittleO_scale
#print axioms eventually_rough_primeFactors_card_le
#print axioms eventually_exp_sqrt_logB_le_exp_scale
#print axioms eventually_rough_prod_one_add_four_div_pred_le
#print axioms combEpoch_mean_work_eq
#print axioms combEpoch_mean_work_le
#print axioms combEpoch_mean_work_of_pre_sure
#print axioms combEpoch_fail_eq
#print axioms combEpoch_success_ge_pre
#print axioms combEpoch_success_ge_main
#print axioms combined_epoch_asymptotic
#print axioms combined_epoch_asymptotic_logB
#print axioms factor_expected_from_prepass_and_rough_epoch
#print axioms checkDivisor_spec
#print axioms trialPrepass_work_le
#print axioms trialPrepass_splits_of_small_prime
#print axioms trialPrepass_splits_of_hasSmallPrimeFactor
#print axioms trialPrepass_success_prob_one
#print axioms trialPrepass_mean_work_le_exp

end Cogentic.RandomizedSmallPrimePrepass
