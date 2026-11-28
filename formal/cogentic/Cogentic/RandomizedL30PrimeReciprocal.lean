import Cogentic.RandomizedL30RankinEuler
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option maxHeartbeats 4000000

/-!
# L30: the prime-reciprocal Rankin saddle estimate

`Cogentic/RandomizedL30RankinEuler` isolates the remaining analytic input of the
sharp L30 upper density as the predicate `PrimeReciprocalSaddleUpper C p ε`:
at the paper cutoff `Y = exp ((1+ε) t_p)` and at the saddle tilt
`α = 1 - s / log Y`, `s = log u + log log u + 1`, the tilted prime mass obeys

`∑_{q ≤ Y} q^{-α} ≤ C e^s / s`.

This file proves that estimate unconditionally for every `p` with
`PaperDensityGrowth p` and every `ε > 0`, with the explicit constant
`C = rankinPrimeConstant = 32`, and composes it with the Euler-product reduction
of `Cogentic/RandomizedL30RankinEuler` to obtain the sharp L30 upper density
with constant `1`.

The analytic input is Chebyshev's explicit bound `π(x) ≤ 2 (log 4) x / log x + √x`
(`Chebyshev.pi_le_log4_mul_div`) together with Abel summation
(`sum_mul_eq_sub_integral_mul₁`):

`∑_{q ≤ Y} q^{-α} = Y^{-α} π(Y) + α ∫_2^Y t^{-α-1} π(t) dt`.

The remaining integral `∫_2^Y t^{-α}/log t dt` is estimated directly: split at
`T = exp (1/β)` with `β = 1 - α` and integrate by parts once more, giving the
sharp bound `≤ 2 e^s/s` plus a term `log (1/β) = log (log Y / s)` that is
absorbed for large `n` using `PaperDensityGrowth`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, mass or
error is set to zero.
-/

namespace Cogentic.RandomizedL30PrimeReciprocal

open Filter Real MeasureTheory
open scoped Classical BigOperators
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30SharpRankin
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30RankinEuler
open Cogentic.Randomized

noncomputable section

/-! ## 1. Abel summation against the prime-counting function -/

/-- The indicator of the primes, used as the coefficient sequence in Abel
summation. -/
def primeIndicator : ℕ → ℝ := fun k => if k.Prime then 1 else 0

theorem primeIndicator_zero : primeIndicator 0 = 0 := by
  simp [primeIndicator, Nat.not_prime_zero]

theorem primeIndicator_one : primeIndicator 1 = 0 := by
  simp [primeIndicator, Nat.not_prime_one]

/-- The prime-counting function as a real-valued function of a real argument. -/
def primeCountingFloor (t : ℝ) : ℝ := (Nat.primeCounting ⌊t⌋₊ : ℝ)

theorem monotone_primeCountingFloor : Monotone primeCountingFloor := by
  intro a b hab
  unfold primeCountingFloor
  exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono hab)

theorem sum_primeIndicator_eq_primeCounting (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N, primeIndicator k) = (Nat.primeCounting N : ℝ) := by
  have hsum : (∑ k ∈ Finset.Icc 0 N, primeIndicator k)
      = (((Finset.Icc 0 N).filter Nat.Prime).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k.Prime <;> simp [primeIndicator, hk]
  rw [hsum]
  have hcard : (Finset.Icc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hk⟩, hp⟩
      exact ⟨hk, hp⟩
    · rintro ⟨hk, hp⟩
      exact ⟨⟨Nat.zero_le _, hk⟩, hp⟩
  rw [hcard, Nat.primesLE_card_eq_primeCounting]

theorem filter_Icc_zero_prime_eq_filter_Icc_two_prime (N : ℕ) :
    (Finset.Icc 0 N).filter Nat.Prime = (Finset.Icc 2 N).filter Nat.Prime := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hk⟩, hp⟩
    exact ⟨⟨hp.two_le, hk⟩, hp⟩
  · rintro ⟨⟨h2, hk⟩, hp⟩
    exact ⟨⟨by omega, hk⟩, hp⟩

theorem sum_filter_prime_eq_sum_ite (N : ℕ) (g : ℕ → ℝ) :
    (∑ q ∈ (Finset.Icc 2 N).filter Nat.Prime, g q) =
      ∑ k ∈ Finset.Icc 0 N, if k.Prime then g k else 0 := by
  rw [← filter_Icc_zero_prime_eq_filter_Icc_two_prime N, Finset.sum_filter]

/-- **Abel summation for the tilted prime mass.**  For `Y ≥ 2` and any tilt `α`,
the tilted prime mass equals the Chebyshev boundary term minus the Abel integral. -/
theorem prime_sum_rpow_eq_primeCounting_abel {α Y : ℝ} (hY : 2 ≤ Y) :
    (∑ q ∈ (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime, (q : ℝ) ^ (-α)) =
      Y ^ (-α) * primeCountingFloor Y -
        ∫ t in Set.Ioc 2 Y,
          deriv (fun t : ℝ => t ^ (-α)) t * primeCountingFloor t := by
  have hYpos : 0 < Y := by linarith
  have habel :
      (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊,
          (fun t : ℝ => t ^ (-α)) ↑k * primeIndicator k) =
        Y ^ (-α) * (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, primeIndicator k) -
          ∫ t in Set.Ioc 2 Y,
            deriv (fun t : ℝ => t ^ (-α)) t *
              (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeIndicator k) := by
    refine sum_mul_eq_sub_integral_mul₁ (f := fun t : ℝ => t ^ (-α))
      primeIndicator primeIndicator_zero primeIndicator_one Y ?_ ?_
    · intro z hz
      have hz2 : (2 : ℝ) ≤ z := hz.1
      have hzpos : z ≠ 0 := by linarith
      fun_prop
    · refine ContinuousOn.integrableOn_Icc ?_
      refine ContinuousOn.congr (f := fun u : ℝ => -α * u ^ (-α - 1)) ?_ ?_
      · refine ContinuousOn.const_mul ?_ _
        exact ContinuousOn.rpow_const continuousOn_id
          (fun u hu => Or.inl (by simpa using ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)))
      · intro u hu
        rw [Real.deriv_rpow_const]
  -- rewrite the left-hand side as the filtered prime sum
  have hL : (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊,
      (fun t : ℝ => t ^ (-α)) ↑k * primeIndicator k) =
      ∑ q ∈ (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime, (q : ℝ) ^ (-α) := by
    rw [sum_filter_prime_eq_sum_ite (⌊Y⌋₊) (fun q => (q : ℝ) ^ (-α))]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k.Prime <;> simp [primeIndicator, hk]
  rw [← hL, habel]
  congr 1
  · simp [primeCountingFloor, sum_primeIndicator_eq_primeCounting]
  · refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro t _
    change deriv (fun t : ℝ => t ^ (-α)) t *
        (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeIndicator k) =
      deriv (fun t : ℝ => t ^ (-α)) t * primeCountingFloor t
    rw [sum_primeIndicator_eq_primeCounting]
    rfl

/-! ## 2. Chebyshev's bound and the prime mass estimate -/

/-- Chebyshev's explicit prime-counting bound in the form used below,
`π(x) ≤ 2 (log 4) x / log x + √x`. -/
theorem pi_le_two_log4_mul_div_add_sqrt {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2 * Real.log 4 * x / Real.log x + Real.sqrt x := by
  have h := Chebyshev.pi_le_log4_mul_div (x := x) hx
  have hlogsqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (by linarith)
  rw [hlogsqrt] at h
  have hdiv : Real.log 4 * x / (Real.log x / 2) = 2 * Real.log 4 * x / Real.log x := by
    field_simp
  rw [hdiv] at h
  exact h

/-- **The tilted prime mass is bounded by Chebyshev's estimate.**  For every tilt
`α ∈ (1/2, 1)` and every `Y ≥ 2`,

`∑_{q ≤ Y} q^{-α} ≤ 2 (log 4) Y^{1-α}/log Y + Y^{1/2-α}
   + α (2 (log 4) ∫_2^Y t^{-α}/log t + ∫_2^Y t^{-α-1/2})`. -/
theorem prime_sum_rpow_le {α Y : ℝ} (hα0 : (1 / 2 : ℝ) < α) (hα1 : α < 1)
    (hY : 2 ≤ Y) :
    (∑ q ∈ (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime, (q : ℝ) ^ (-α)) ≤
      2 * Real.log 4 * Y ^ (1 - α) / Real.log Y + Y ^ (1 / 2 - α) +
        α * (2 * Real.log 4 * (∫ t in (2 : ℝ)..Y, t ^ (-α) / Real.log t) +
          ∫ t in (2 : ℝ)..Y, t ^ (-α - 1 / 2)) := by
  have hαpos : 0 < α := by linarith
  have hYpos : 0 < Y := by linarith
  have hY1 : 1 < Y := by linarith
  have hlogYpos : 0 < Real.log Y := Real.log_pos hY1
  have hlogYne : Real.log Y ≠ 0 := ne_of_gt hlogYpos
  have hYne : Y ≠ 0 := ne_of_gt hYpos
  rw [prime_sum_rpow_eq_primeCounting_abel hY, ← intervalIntegral.integral_of_le hY]
  -- boundary term
  have hboundary : Y ^ (-α) * primeCountingFloor Y ≤
      2 * Real.log 4 * Y ^ (1 - α) / Real.log Y + Y ^ (1 / 2 - α) := by
    have hp := pi_le_two_log4_mul_div_add_sqrt hY1
    have h1 : Y ^ (-α) * primeCountingFloor Y ≤
        Y ^ (-α) * (2 * Real.log 4 * Y / Real.log Y + Real.sqrt Y) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    refine h1.trans ?_
    rw [mul_add]
    have h2 : Y ^ (-α) * (2 * Real.log 4 * Y / Real.log Y) =
        2 * Real.log 4 * Y ^ (1 - α) / Real.log Y := by
      rw [show Y ^ (-α) * (2 * Real.log 4 * Y / Real.log Y)
          = 2 * Real.log 4 * (Y ^ (-α) * Y) / Real.log Y by ring]
      rw [← Real.rpow_add_one hYne]
      rw [show -α + 1 = 1 - α by ring]
    have h3 : Y ^ (-α) * Real.sqrt Y = Y ^ (1 / 2 - α) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hYpos]
      congr 1
      ring
    rw [h2, h3]
  -- derivative identity
  have hderiv_eq :
      (∫ t in (2 : ℝ)..Y, deriv (fun t : ℝ => t ^ (-α)) t * primeCountingFloor t)
        = -α * ∫ t in (2 : ℝ)..Y, t ^ (-α - 1) * primeCountingFloor t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Real.deriv_rpow_const]
    ring
  -- integral bound
  have hint_le : (∫ t in (2 : ℝ)..Y, t ^ (-α - 1) * primeCountingFloor t) ≤
      2 * Real.log 4 * (∫ t in (2 : ℝ)..Y, t ^ (-α) / Real.log t) +
        ∫ t in (2 : ℝ)..Y, t ^ (-α - 1 / 2) := by
    have hpt : ∀ t ∈ Set.Icc (2 : ℝ) Y,
        t ^ (-α - 1) * primeCountingFloor t ≤
          2 * Real.log 4 * (t ^ (-α) / Real.log t) + t ^ (-α - 1 / 2) := by
      intro t ht
      have ht2 : 2 ≤ t := ht.1
      have ht1 : 1 < t := by linarith
      have htpos : 0 < t := by linarith
      have htne : t ≠ 0 := ne_of_gt htpos
      have hlogpos : 0 < Real.log t := Real.log_pos ht1
      have hmul := mul_le_mul_of_nonneg_left (pi_le_two_log4_mul_div_add_sqrt ht1)
        (by positivity : (0 : ℝ) ≤ t ^ (-α - 1))
      refine hmul.trans_eq ?_
      rw [mul_add]
      have hA : t ^ (-α - 1) * (2 * Real.log 4 * t / Real.log t) =
          2 * Real.log 4 * (t ^ (-α) / Real.log t) := by
        rw [show t ^ (-α - 1) * (2 * Real.log 4 * t / Real.log t)
            = 2 * Real.log 4 * (t ^ (-α - 1) * t) / Real.log t by ring]
        rw [← Real.rpow_add_one htne]
        rw [show -α - 1 + 1 = -α by ring]
        ring
      have hB : t ^ (-α - 1) * Real.sqrt t = t ^ (-α - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add htpos]
        congr 1
        ring
      rw [hA, hB]
    have hIntL : IntervalIntegrable (fun t : ℝ => t ^ (-α - 1) * primeCountingFloor t)
        volume (2 : ℝ) Y := by
      have hpc : IntervalIntegrable primeCountingFloor volume (2 : ℝ) Y :=
        monotone_primeCountingFloor.intervalIntegrable
      refine hpc.continuousOn_mul ?_
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le hY] at hu
        exact hu.1
      exact Or.inl (ne_of_gt (by linarith))
    have hIntA : IntervalIntegrable
        (fun t : ℝ => 2 * Real.log 4 * (t ^ (-α) / Real.log t)) volume (2 : ℝ) Y := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.const_mul ?_ _
      refine ContinuousOn.div ?_ ?_ ?_
      · refine ContinuousOn.rpow_const continuousOn_id ?_
        intro u hu
        have hu2 : (2 : ℝ) ≤ u := by
          rw [Set.uIcc_of_le hY] at hu
          exact hu.1
        exact Or.inl (ne_of_gt (by linarith))
      · refine ContinuousOn.log continuousOn_id ?_
        intro u hu
        have hu2 : (2 : ℝ) ≤ u := by
          rw [Set.uIcc_of_le hY] at hu
          exact hu.1
        simpa using ne_of_gt (by linarith : (0 : ℝ) < u)
      · intro u hu
        have hu2 : (2 : ℝ) ≤ u := by
          rw [Set.uIcc_of_le hY] at hu
          exact hu.1
        exact ne_of_gt (Real.log_pos (by linarith))
    have hIntB : IntervalIntegrable (fun t : ℝ => t ^ (-α - 1 / 2)) volume (2 : ℝ) Y := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le hY] at hu
        exact hu.1
      exact Or.inl (ne_of_gt (by linarith))
    have hmono := intervalIntegral.integral_mono_on hY hIntL
      (hIntA.add hIntB) hpt
    -- rewrite the right-hand integral
    have hright : (∫ t in (2 : ℝ)..Y,
          2 * Real.log 4 * (t ^ (-α) / Real.log t) + t ^ (-α - 1 / 2))
        = 2 * Real.log 4 * (∫ t in (2 : ℝ)..Y, t ^ (-α) / Real.log t) +
          ∫ t in (2 : ℝ)..Y, t ^ (-α - 1 / 2) := by
      rw [intervalIntegral.integral_add hIntA hIntB, intervalIntegral.integral_const_mul]
    rw [hright] at hmono
    exact hmono
  have hderiv_le : -α * (2 * Real.log 4 * (∫ t in (2 : ℝ)..Y, t ^ (-α) / Real.log t) +
      ∫ t in (2 : ℝ)..Y, t ^ (-α - 1 / 2)) ≤
      ∫ t in (2 : ℝ)..Y, deriv (fun t : ℝ => t ^ (-α)) t * primeCountingFloor t := by
    rw [hderiv_eq]
    exact mul_le_mul_of_nonpos_left hint_le (by linarith : -α ≤ 0)
  linarith [hboundary, hderiv_le]

/-- The `√x` remainder in Chebyshev's bound contributes only a constant. -/
theorem integral_rpow_neg_half_le {α Y : ℝ} (hα : (1 / 2 : ℝ) < α) (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, t ^ (-α - 1 / 2)) ≤ Real.sqrt 2 / (α - 1 / 2) := by
  have hden : 0 < α - 1 / 2 := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (2 : ℝ) Y := by
    rw [Set.uIcc_of_le hY]
    intro h
    linarith [h.1]
  have hr : -α - 1 / 2 ≠ (-1 : ℝ) := by
    intro h
    linarith
  rw [integral_rpow (Or.inr ⟨hr, h0⟩)]
  have hexp : -α - 1 / 2 + 1 = 1 / 2 - α := by ring
  rw [hexp]
  have heq : (Y ^ (1 / 2 - α) - 2 ^ (1 / 2 - α)) / (1 / 2 - α)
      = (2 ^ (1 / 2 - α) - Y ^ (1 / 2 - α)) / (α - 1 / 2) := by
    rw [show (1 / 2 - α) = -(α - 1 / 2) by ring, div_neg, ← neg_div, neg_sub]
  rw [heq]
  have hYnonneg : 0 ≤ Y ^ (1 / 2 - α) := by positivity
  have hnum : 2 ^ (1 / 2 - α) - Y ^ (1 / 2 - α) ≤ 2 ^ (1 / 2 - α) := by linarith
  have step1 : (2 ^ (1 / 2 - α) - Y ^ (1 / 2 - α)) / (α - 1 / 2) ≤
      2 ^ (1 / 2 - α) / (α - 1 / 2) :=
    div_le_div_of_nonneg_right hnum hden.le
  have hpow : 2 ^ (1 / 2 - α) ≤ Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : 1 / 2 - α ≤ 1 / 2)
  exact step1.trans (div_le_div_of_nonneg_right hpow hden.le)

/-! ## 3. The logarithmic integral at the saddle -/

/-- The mass of `t^{β-1}/log t` below `exp (1/β)` costs only `log (1/β)`. -/
theorem integral_small_rpow_div_log_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2) :
    (∫ t in (2 : ℝ)..(Real.exp (1 / β)), t ^ (β - 1) / Real.log t) ≤
      Real.exp 1 * (Real.log (1 / β) + 1) := by
  have hβne : β ≠ 0 := ne_of_gt hβ0
  have hT2 : 2 ≤ Real.exp (1 / β) := by
    have hle : (2 : ℝ) ≤ 1 / β := by
      rw [le_div_iff₀ hβ0]
      linarith
    calc (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
      _ ≤ Real.exp (1 / β) := Real.exp_le_exp.mpr hle
  have hT1 : 1 < Real.exp (1 / β) := lt_of_lt_of_le one_lt_two hT2
  have hTpos : 0 < Real.exp (1 / β) := Real.exp_pos _
  have hTpow : (Real.exp (1 / β)) ^ β = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hTpos, Real.log_exp]
    congr 1
    field_simp
  have hpt : ∀ t ∈ Set.Icc (2 : ℝ) (Real.exp (1 / β)),
      t ^ (β - 1) / Real.log t ≤ Real.exp 1 * (t ^ (-1 : ℝ) / Real.log t) := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
    have htT : t ≤ Real.exp (1 / β) := ht.2
    have hpow : t ^ β ≤ Real.exp 1 := by
      have h := Real.rpow_le_rpow (le_of_lt htpos) htT (le_of_lt hβ0)
      rwa [hTpow] at h
    have hdiv : t ^ (β - 1) ≤ Real.exp 1 * t ^ (-1 : ℝ) := by
      rw [Real.rpow_sub_one (ne_of_gt htpos), Real.rpow_neg_one]
      rw [show Real.exp 1 * t⁻¹ = Real.exp 1 / t by ring]
      exact div_le_div_of_nonneg_right hpow htpos.le
    rw [show Real.exp 1 * (t ^ (-1 : ℝ) / Real.log t) =
        (Real.exp 1 * t ^ (-1 : ℝ)) / Real.log t by ring]
    exact div_le_div_of_nonneg_right hdiv hlogpos.le
  have hIntL : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t)
      volume (2 : ℝ) (Real.exp (1 / β)) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Real.exp (1 / β))] at hu
        exact hu.1
      exact Or.inl (ne_of_gt (by linarith))
    · refine ContinuousOn.log continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Real.exp (1 / β))] at hu
        exact hu.1
      simpa using ne_of_gt (by linarith : (0 : ℝ) < u)
    · intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Real.exp (1 / β))] at hu
        exact hu.1
      exact ne_of_gt (Real.log_pos (by linarith))
  have hIntR : IntervalIntegrable
      (fun t : ℝ => Real.exp 1 * (t ^ (-1 : ℝ) / Real.log t))
      volume (2 : ℝ) (Real.exp (1 / β)) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.div ?_ ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Real.exp (1 / β))] at hu
        exact hu.1
      exact Or.inl (ne_of_gt (by linarith))
    · refine ContinuousOn.log continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Real.exp (1 / β))] at hu
        exact hu.1
      simpa using ne_of_gt (by linarith : (0 : ℝ) < u)
    · intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Real.exp (1 / β))] at hu
        exact hu.1
      exact ne_of_gt (Real.log_pos (by linarith))
  have hmono := intervalIntegral.integral_mono_on hT2 hIntL hIntR hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hcongr : (∫ t in (2 : ℝ)..(Real.exp (1 / β)), t ^ (-1 : ℝ) / Real.log t)
      = ∫ t in (2 : ℝ)..(Real.exp (1 / β)), t⁻¹ / Real.log t :=
    intervalIntegral.integral_congr fun t _ => by rw [Real.rpow_neg_one]
  rw [hcongr, integral_inv_div_log (by norm_num : (1 : ℝ) < 2) hT1,
    Real.log_exp] at hmono
  have hconst : -Real.log (Real.log 2) ≤ 1 := by
    have hhalf : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h1 : Real.exp (-1) < Real.log 2 := lt_trans Real.exp_neg_one_lt_half hhalf
    have h2 : Real.log (Real.exp (-1)) < Real.log (Real.log 2) :=
      Real.log_lt_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    linarith
  nlinarith [Real.exp_pos 1, hconst]

/-- Derivative of `t ↦ t^β / (β log t)`. -/
theorem hasDerivAt_rpow_div_log {β t : ℝ} (hβ0 : 0 < β) (ht : 0 < t)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt (fun s : ℝ => s ^ β / (β * Real.log s))
      (t ^ (β - 1) / Real.log t - t ^ (β - 1) / (β * (Real.log t) ^ 2)) t := by
  have hβne : β ≠ 0 := ne_of_gt hβ0
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h1 : HasDerivAt (fun s : ℝ => s ^ β) (β * t ^ (β - 1)) t := by
    simpa using Real.hasDerivAt_rpow_const (x := t) (p := β) (Or.inl ht0)
  have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
  have h2' : HasDerivAt (fun s : ℝ => β * Real.log s) (β * t⁻¹) t := h2.const_mul β
  have h5 : HasDerivAt (fun s : ℝ => s ^ β / (β * Real.log s))
      ((β * t ^ (β - 1) * (β * Real.log t) - t ^ β * (β * t⁻¹)) / (β * Real.log t) ^ 2) t :=
    h1.div h2' (mul_ne_zero hβne hlog)
  have hval : ((β * t ^ (β - 1) * (β * Real.log t) - t ^ β * (β * t⁻¹)) /
        (β * Real.log t) ^ 2) =
      t ^ (β - 1) / Real.log t - t ^ (β - 1) / (β * (Real.log t) ^ 2) := by
    have hpow : t ^ (β - 1) = t ^ β / t := Real.rpow_sub_one ht0 β
    rw [hpow]
    field_simp
  rw [hval] at h5
  exact h5

/-- **The tail of the logarithmic integral.**  For `T = exp (1/β)` and `Y = exp L`
with `0 < β ≤ 1/2` and `T² ≤ Y`, the tail `∫_T^Y t^{β-1}/log t` is at most
`2 Y^β/(β log Y) + 2 e²`.  The proof is one integration by parts plus the
observation that `1/log²t ≤ β²` below `T²` and `1/log²t ≤ (β/2)/log t` above it. -/
theorem integral_tail_rpow_div_log_le {β L : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2)
    (hL : 2 / β ≤ L) :
    (∫ t in (Real.exp (1 / β))..(Real.exp L), t ^ (β - 1) / Real.log t)
      ≤ 2 * Real.exp (β * L) / (β * L) + 2 * (Real.exp 1) ^ 2 := by
  have hβne : β ≠ 0 := ne_of_gt hβ0
  have hLpos : 0 < L := by
    have : 0 < 2 / β := by positivity
    linarith
  set T := Real.exp (1 / β)
  set Y := Real.exp L
  have hTpos : 0 < T := Real.exp_pos _
  have hYpos : 0 < Y := Real.exp_pos _
  have hT1 : 1 < T := Real.one_lt_exp_iff.mpr (by positivity)
  have hT2 : 2 ≤ T := by
    have hle : (2 : ℝ) ≤ 1 / β := by
      rw [le_div_iff₀ hβ0]
      linarith
    calc (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
      _ ≤ T := Real.exp_le_exp.mpr hle
  have hTY : T ≤ Y := by
    apply Real.exp_le_exp.mpr
    have h1β : (1 : ℝ) / β ≤ 2 / β :=
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hβ0.le
    exact le_trans h1β hL
  have hTT2 : T ≤ T ^ 2 := by nlinarith
  have hT2Y : T ^ 2 ≤ Y := by
    rw [pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : 1 / β + 1 / β = 2 / β := by ring
    rw [this]
    exact hL
  have hlogT : Real.log T = 1 / β := Real.log_exp _
  have hlogY : Real.log Y = L := Real.log_exp _
  have hTβ : T ^ β = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hTpos, hlogT]
    congr 1
    field_simp
  -- derivative data
  have hderiv : ∀ t ∈ Set.uIcc T Y,
      HasDerivAt (fun s : ℝ => s ^ β / (β * Real.log s))
        (t ^ (β - 1) / Real.log t - t ^ (β - 1) / (β * (Real.log t) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hTY] at ht
    exact hasDerivAt_rpow_div_log hβ0 (by linarith [ht.1])
      (by
        apply Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1])
        linarith [ht.1])
  have hdiff : ∀ t ∈ Set.uIcc T Y,
      DifferentiableAt ℝ (fun s : ℝ => s ^ β / (β * Real.log s)) t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hcontG : ContinuousOn (fun t : ℝ => t ^ (β - 1) / Real.log t) (Set.uIcc T Y) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le hTY] at hu
        exact le_trans hT2 hu.1
      exact Or.inl (ne_of_gt (by linarith))
    · refine ContinuousOn.log continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le hTY] at hu
        exact le_trans hT2 hu.1
      simpa using ne_of_gt (by linarith : (0 : ℝ) < u)
    · intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le hTY] at hu
        exact le_trans hT2 hu.1
      exact ne_of_gt (Real.log_pos (by linarith))
  have hcontH : ContinuousOn (fun t : ℝ => t ^ (β - 1) / (Real.log t) ^ 2)
      (Set.uIcc T Y) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le hTY] at hu
        exact le_trans hT2 hu.1
      exact Or.inl (ne_of_gt (by linarith))
    · refine (ContinuousOn.log continuousOn_id ?_).pow 2
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le hTY] at hu
        exact le_trans hT2 hu.1
      simpa using ne_of_gt (by linarith : (0 : ℝ) < u)
    · intro u hu
      have hu2 : (2 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le hTY] at hu
        exact le_trans hT2 hu.1
      exact pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith)))
  have hcontD : ContinuousOn
      (fun t : ℝ => t ^ (β - 1) / Real.log t - t ^ (β - 1) / (β * (Real.log t) ^ 2))
      (Set.uIcc T Y) := by
    refine ContinuousOn.congr
      (f := fun t : ℝ => t ^ (β - 1) / Real.log t -
        (1 / β) * (t ^ (β - 1) / (Real.log t) ^ 2)) ?_ ?_
    · exact hcontG.sub (hcontH.const_mul (1 / β))
    · intro t _
      field_simp
  have hIntDeriv : IntervalIntegrable
      (deriv (fun s : ℝ => s ^ β / (β * Real.log s))) volume T Y :=
    hcontD.intervalIntegrable.congr
      (fun t ht => ((hderiv t (Set.uIoc_subset_uIcc ht)).deriv).symm)
  have hparts : (∫ t in T..Y, deriv (fun s : ℝ => s ^ β / (β * Real.log s)) t)
      = Y ^ β / (β * Real.log Y) - T ^ β / (β * Real.log T) :=
    intervalIntegral.integral_deriv_eq_sub hdiff hIntDeriv
  have hIntH : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / (Real.log t) ^ 2)
      volume T Y := hcontH.intervalIntegrable
  have hIntG : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t)
      volume T Y := hcontG.intervalIntegrable
  have hIntH1 : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / (Real.log t) ^ 2)
      volume T (T ^ 2) :=
    hIntH.mono_set (by
      rw [Set.uIcc_of_le hTT2, Set.uIcc_of_le hTY]
      exact Set.Icc_subset_Icc le_rfl hT2Y)
  have hIntH2 : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / (Real.log t) ^ 2)
      volume (T ^ 2) Y :=
    hIntH.mono_set (by
      rw [Set.uIcc_of_le hT2Y, Set.uIcc_of_le hTY]
      exact Set.Icc_subset_Icc hTT2 le_rfl)
  have hIntG1 : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t)
      volume T (T ^ 2) :=
    hIntG.mono_set (by
      rw [Set.uIcc_of_le hTT2, Set.uIcc_of_le hTY]
      exact Set.Icc_subset_Icc le_rfl hT2Y)
  have hIntG2 : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t)
      volume (T ^ 2) Y :=
    hIntG.mono_set (by
      rw [Set.uIcc_of_le hT2Y, Set.uIcc_of_le hTY]
      exact Set.Icc_subset_Icc hTT2 le_rfl)
  -- integration by parts
  have hg_eq : (∫ t in T..Y, t ^ (β - 1) / Real.log t)
      = (Y ^ β / (β * Real.log Y) - T ^ β / (β * Real.log T)) +
        (1 / β) * (∫ t in T..Y, t ^ (β - 1) / (Real.log t) ^ 2) := by
    calc
      (∫ t in T..Y, t ^ (β - 1) / Real.log t)
          = ∫ t in T..Y, (deriv (fun s : ℝ => s ^ β / (β * Real.log s)) t +
              (1 / β) * (t ^ (β - 1) / (Real.log t) ^ 2)) := by
            refine intervalIntegral.integral_congr fun t ht => ?_
            rw [(hderiv t ht).deriv]
            ring
      _ = (∫ t in T..Y, deriv (fun s : ℝ => s ^ β / (β * Real.log s)) t) +
            ∫ t in T..Y, (1 / β) * (t ^ (β - 1) / (Real.log t) ^ 2) :=
            intervalIntegral.integral_add hIntDeriv (hIntH.const_mul _)
      _ = _ := by rw [hparts, intervalIntegral.integral_const_mul]
  -- the lower piece, bounded pointwise by `β² t^{β-1}`
  have hpart1 : (∫ t in T..T ^ 2, t ^ (β - 1) / (Real.log t) ^ 2) ≤
      β * (Real.exp 1) ^ 2 := by
    have hpt : ∀ t ∈ Set.Icc T (T ^ 2),
        t ^ (β - 1) / (Real.log t) ^ 2 ≤ β ^ 2 * t ^ (β - 1) := by
      intro t ht
      have hTle : T ≤ t := ht.1
      have htpos : 0 < t := lt_of_lt_of_le hTpos hTle
      have hlogt : 1 / β ≤ Real.log t := by
        rw [← hlogT]
        exact Real.log_le_log hTpos hTle
      have hlogpos : 0 < Real.log t := lt_of_lt_of_le (one_div_pos.mpr hβ0) hlogt
      have h1 : 1 ≤ β * Real.log t := by
        have h := mul_le_mul_of_nonneg_left hlogt hβ0.le
        rwa [mul_one_div, div_self (ne_of_gt hβ0)] at h
      have hkey : 1 ≤ (β * Real.log t) ^ 2 := by nlinarith
      have hpos : 0 < t ^ (β - 1) := Real.rpow_pos_of_pos htpos _
      rw [div_le_iff₀ (pow_pos hlogpos 2)]
      nlinarith
    have hInt1 : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / (Real.log t) ^ 2)
        volume T (T ^ 2) := hIntH1
    have hInt2 : IntervalIntegrable (fun t : ℝ => β ^ 2 * t ^ (β - 1))
        volume T (T ^ 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.const_mul ?_ _
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu
      rw [Set.uIcc_of_le hTT2] at hu
      exact Or.inl (ne_of_gt (by linarith [hTpos, hu.1]))
    have hmono := intervalIntegral.integral_mono_on hTT2 hInt1 hInt2 hpt
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < β - 1))] at hmono
    have hT2β : (T ^ 2) ^ β = (Real.exp 1) ^ 2 := by
      rw [pow_two, Real.mul_rpow (le_of_lt hTpos) (le_of_lt hTpos), hTβ]
      ring
    rw [show β - 1 + 1 = β by ring, hT2β, hTβ] at hmono
    have hfin : β ^ 2 * (((Real.exp 1) ^ 2 - Real.exp 1) / β) ≤
        β * (Real.exp 1) ^ 2 := by
      rw [show β ^ 2 * (((Real.exp 1) ^ 2 - Real.exp 1) / β) =
          β * ((Real.exp 1) ^ 2 - Real.exp 1) by field_simp]
      nlinarith [Real.exp_pos 1]
    linarith
  -- the upper piece: `1/log²t ≤ (β/2)/log t`
  have hpart2 : (∫ t in T ^ 2..Y, t ^ (β - 1) / (Real.log t) ^ 2) ≤
      (β / 2) * (∫ t in T ^ 2..Y, t ^ (β - 1) / Real.log t) := by
    have hpt : ∀ t ∈ Set.Icc (T ^ 2) Y,
        t ^ (β - 1) / (Real.log t) ^ 2 ≤
          (β / 2) * (t ^ (β - 1) / Real.log t) := by
      intro t ht
      have hT2le : T ^ 2 ≤ t := ht.1
      have htpos : 0 < t := lt_of_lt_of_le (by positivity) hT2le
      have hlogt : 2 / β ≤ Real.log t := by
        have hlogT2 : Real.log (T ^ 2) = 2 / β := by
          rw [Real.log_pow]
          push_cast
          rw [hlogT]
          ring
        rw [← hlogT2]
        exact Real.log_le_log (by positivity) hT2le
      have hlogpos : 0 < Real.log t := lt_of_lt_of_le (by positivity) hlogt
      have hle : 1 / Real.log t ≤ β / 2 := by
        rw [div_le_iff₀ hlogpos]
        have h2 : (β / 2) * (2 / β) ≤ (β / 2) * Real.log t :=
          mul_le_mul_of_nonneg_left hlogt (by positivity)
        have hβ2 : (β / 2) * (2 / β) = 1 := by field_simp
        linarith
      have hnn : 0 ≤ t ^ (β - 1) / Real.log t := by positivity
      have hEq : t ^ (β - 1) / (Real.log t) ^ 2 =
          (t ^ (β - 1) / Real.log t) * (1 / Real.log t) := by
        field_simp
      rw [hEq]
      calc (t ^ (β - 1) / Real.log t) * (1 / Real.log t)
          ≤ (t ^ (β - 1) / Real.log t) * (β / 2) :=
            mul_le_mul_of_nonneg_left hle hnn
        _ = (β / 2) * (t ^ (β - 1) / Real.log t) := by ring
    have hInt2 : IntervalIntegrable
        (fun t : ℝ => (β / 2) * (t ^ (β - 1) / Real.log t)) volume (T ^ 2) Y :=
      hIntG2.const_mul _
    have hmono := intervalIntegral.integral_mono_on hT2Y hIntH2 hInt2 hpt
    rwa [intervalIntegral.integral_const_mul] at hmono
  have hHsplit : (∫ t in T..Y, t ^ (β - 1) / (Real.log t) ^ 2)
      = (∫ t in T..T ^ 2, t ^ (β - 1) / (Real.log t) ^ 2) +
        (∫ t in T ^ 2..Y, t ^ (β - 1) / (Real.log t) ^ 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hIntH1 hIntH2]
  have hJ2_le : (∫ t in T..Y, t ^ (β - 1) / (Real.log t) ^ 2) ≤
      β * (Real.exp 1) ^ 2 +
        (β / 2) * (∫ t in T..Y, t ^ (β - 1) / Real.log t) := by
    rw [hHsplit]
    have hg_split : (∫ t in T..Y, t ^ (β - 1) / Real.log t)
        = (∫ t in T..T ^ 2, t ^ (β - 1) / Real.log t) +
          (∫ t in T ^ 2..Y, t ^ (β - 1) / Real.log t) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hIntG1 hIntG2]
    have hg_nonneg : 0 ≤ ∫ t in T..T ^ 2, t ^ (β - 1) / Real.log t := by
      refine intervalIntegral.integral_nonneg hTT2 ?_
      intro u hu
      have hu2 : (2 : ℝ) ≤ u := le_trans hT2 hu.1
      exact div_nonneg (Real.rpow_pos_of_pos (by linarith) _).le
        (Real.log_pos (by linarith)).le
    have htail : (∫ t in T ^ 2..Y, t ^ (β - 1) / Real.log t) ≤
        (∫ t in T..Y, t ^ (β - 1) / Real.log t) := by
      rw [hg_split]
      linarith
    have hscaled : (β / 2) * (∫ t in T ^ 2..Y, t ^ (β - 1) / Real.log t) ≤
        (β / 2) * (∫ t in T..Y, t ^ (β - 1) / Real.log t) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    linarith [hpart1, hpart2, hscaled]
  -- solve for the tail
  have hmain : (∫ t in T..Y, t ^ (β - 1) / Real.log t) ≤
      2 * (Y ^ β / (β * Real.log Y)) + 2 * (Real.exp 1) ^ 2 := by
    have h1 : (1 / β) * (∫ t in T..Y, t ^ (β - 1) / (Real.log t) ^ 2) ≤
        (Real.exp 1) ^ 2 + (1 / 2) * (∫ t in T..Y, t ^ (β - 1) / Real.log t) := by
      have hmul := mul_le_mul_of_nonneg_left hJ2_le (le_of_lt (one_div_pos.mpr hβ0))
      calc (1 / β) * (∫ t in T..Y, t ^ (β - 1) / (Real.log t) ^ 2)
          ≤ (1 / β) * (β * (Real.exp 1) ^ 2 +
              (β / 2) * (∫ t in T..Y, t ^ (β - 1) / Real.log t)) := hmul
        _ = (Real.exp 1) ^ 2 +
              (1 / 2) * (∫ t in T..Y, t ^ (β - 1) / Real.log t) := by
            field_simp
    have h2 : (∫ t in T..Y, t ^ (β - 1) / Real.log t) ≤
        (Y ^ β / (β * Real.log Y) - T ^ β / (β * Real.log T)) +
          ((Real.exp 1) ^ 2 +
            (1 / 2) * (∫ t in T..Y, t ^ (β - 1) / Real.log t)) := by
      rw [hg_eq]
      linarith
    have hFT : 0 ≤ T ^ β / (β * Real.log T) := by
      have : 0 < Real.log T := by rw [hlogT]; positivity
      positivity
    nlinarith [h2]
  rw [hlogY] at hmain
  have hYβ : Y ^ β = Real.exp (β * L) := by
    rw [Real.rpow_def_of_pos hYpos, hlogY]
    congr 1
    ring
  rw [hYβ] at hmain
  convert hmain using 1 <;> ring

/-- `t ↦ t^{β-1}/log t` is interval integrable away from `1`. -/
theorem intervalIntegrable_rpow_div_log {β a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div ?_ ?_ ?_
  · refine ContinuousOn.rpow_const continuousOn_id ?_
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact Or.inl (ne_of_gt (by linarith [hu.1]))
  · refine ContinuousOn.log continuousOn_id ?_
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    simpa using ne_of_gt (by linarith [hu.1])
  · intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact ne_of_gt (Real.log_pos (by linarith [hu.1]))

/-- **The complete logarithmic-integral bound at the saddle.**  For `0 < β ≤ 1/2`
and `2/β ≤ L`,

`∫_2^{e^L} t^{β-1}/log t dt ≤ e (log (1/β) + 1) + 2 e^{βL}/(βL) + 2 e²`. -/
theorem integral_rpow_div_log_le {β L : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2)
    (hL : 2 / β ≤ L) :
    (∫ t in (2 : ℝ)..(Real.exp L), t ^ (β - 1) / Real.log t)
      ≤ Real.exp 1 * (Real.log (1 / β) + 1) +
        (2 * Real.exp (β * L) / (β * L) + 2 * (Real.exp 1) ^ 2) := by
  have hT2 : 2 ≤ Real.exp (1 / β) := by
    have hle : (2 : ℝ) ≤ 1 / β := by
      rw [le_div_iff₀ hβ0]
      linarith
    calc (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
      _ ≤ Real.exp (1 / β) := Real.exp_le_exp.mpr hle
  have hTY : Real.exp (1 / β) ≤ Real.exp L := by
    apply Real.exp_le_exp.mpr
    have h1β : (1 : ℝ) / β ≤ 2 / β :=
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hβ0.le
    exact le_trans h1β hL
  have hInt1 : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t)
      volume (2 : ℝ) (Real.exp (1 / β)) :=
    intervalIntegrable_rpow_div_log le_rfl hT2
  have hInt2 : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t)
      volume (Real.exp (1 / β)) (Real.exp L) :=
    intervalIntegrable_rpow_div_log hT2 hTY
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2]
  linarith [integral_small_rpow_div_log_le hβ0 hβ1,
    integral_tail_rpow_div_log_le hβ0 hβ1 hL]

/-! ## 4. Growth of the paper schedule -/

/-- Eventually `L = log Y` is at least `4 s` at the saddle. -/
theorem eventually_four_mul_saddleS_le_logCutoff {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      4 * rankinSaddleS (paperDensityU p ε n) ≤
        Real.log (smoothCutoff (paperT p) (paperError ε) n) := by
  have hu := tendsto_paperDensityU_of_growth h hε
  have hlogu := Real.tendsto_log_atTop.comp hu
  have hloglogu := Real.tendsto_log_atTop.comp hlogu
  have hα : 0 < 1 + ε := by positivity
  filter_upwards [eventually_paperDensityU_mul_log_le_paperT h hε,
    hu.eventually_ge_atTop (max 2 (8 / (1 + ε) ^ 2)),
    hlogu.eventually_ge_atTop 2,
    hloglogu.eventually_ge_atTop 0] with n hmul hubig hlu2 hllu0
  set u := paperDensityU p ε n with hu_def
  have hlu2' : (2 : ℝ) ≤ Real.log u := by rw [hu_def]; exact hlu2
  have hllu0' : 0 ≤ Real.log (Real.log u) := by rw [hu_def]; exact hllu0
  set t := paperT p n with ht_def
  have hu2 : 2 ≤ u := le_trans (le_max_left _ _) hubig
  have hupos : 0 < u := by linarith
  have hlogupos : 0 < Real.log u := by linarith
  have hs_le : rankinSaddleS u ≤ 2 * Real.log u := by
    unfold rankinSaddleS
    have hllule : Real.log (Real.log u) + 1 ≤ Real.log u := by
      have := Real.log_le_sub_one_of_pos hlogupos
      linarith
    linarith
  have hu8 : 8 ≤ (1 + ε) ^ 2 * u := by
    have h8 : 8 / (1 + ε) ^ 2 ≤ u := le_trans (le_max_right _ _) hubig
    rw [div_le_iff₀ (by positivity : 0 < (1 + ε) ^ 2)] at h8
    linarith
  have hmain : (1 + ε) ^ 2 * u * Real.log u ≤ (1 + ε) * t := by
    have h := mul_le_mul_of_nonneg_left hmul hα.le
    nlinarith [h]
  have h8log : 8 * Real.log u ≤ (1 + ε) ^ 2 * u * Real.log u := by
    nlinarith [hlogupos, hu8]
  rw [show Real.log (smoothCutoff (paperT p) (paperError ε) n) = (1 + ε) * t by
    simp [smoothCutoff, paperError, t]]
  have h4 : 4 * rankinSaddleS u ≤ 8 * Real.log u := by linarith
  linarith

/-- The saddle scale `s = log u + log log u + 1` tends to infinity. -/
theorem tendsto_rankinSaddleS_of_growth {p : ℕ → ℝ} (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => rankinSaddleS (paperDensityU p ε n)) atTop atTop := by
  have hu := tendsto_paperDensityU_of_growth h hε
  have hlogu : Tendsto (fun n => Real.log (paperDensityU p ε n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu
  have hloglogu : Tendsto (fun n => Real.log (Real.log (paperDensityU p ε n)))
      atTop atTop := Real.tendsto_log_atTop.comp hlogu
  have hsum : Tendsto (fun n => Real.log (paperDensityU p ε n) +
      Real.log (Real.log (paperDensityU p ε n)) + 1) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlogu
    filter_upwards [hloglogu.eventually_ge_atTop (-1)] with n hn
    linarith
  simpa [rankinSaddleS] using hsum

/-- Eventually `log log Y` is at most `2 s`. -/
theorem eventually_logLogCutoff_le_two_mul_saddleS {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      Real.log (Real.log (smoothCutoff (paperT p) (paperError ε) n)) ≤
        2 * rankinSaddleS (paperDensityU p ε n) := by
  have hu := tendsto_paperDensityU_of_growth h hε
  have hs := tendsto_rankinSaddleS_of_growth h hε
  have hα : 0 < 1 + ε := by positivity
  filter_upwards [eventually_paperT_le_two_mul_paperDensityU_log h hε,
    eventually_paperT_pos_of_growth h,
    hu.eventually_ge_atTop (Real.exp 1),
    hs.eventually_ge_atTop
      (Real.log 2 + 2 * Real.log (1 + ε) - 1)] with n htle htpos hubig hsbig
  set u := paperDensityU p ε n with hu_def
  set t := paperT p n with ht_def
  have hu1 : 1 < u := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    rw [hu_def]; linarith
  have hlogu1 : 1 ≤ Real.log u := by
    have h := Real.log_le_log (Real.exp_pos 1) hubig
    rwa [Real.log_exp] at h
  have hlogupos : 0 < Real.log u := lt_of_lt_of_le zero_lt_one hlogu1
  have hllu : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hlogu1
  have htpos' : 0 < t := by rw [ht_def]; exact htpos
  have htle' : t ≤ 2 * (1 + ε) * (u * Real.log u) := by
    rw [ht_def, hu_def]; exact htle
  have hL : Real.log (smoothCutoff (paperT p) (paperError ε) n) = (1 + ε) * t := by
    rw [ht_def]; simp [smoothCutoff, paperError]
  have hlogL : Real.log (Real.log (smoothCutoff (paperT p) (paperError ε) n)) =
      Real.log (1 + ε) + Real.log t := by
    rw [hL, Real.log_mul hα.ne' htpos'.ne']
  have hargpos : 0 < 2 * (1 + ε) * (u * Real.log u) := by positivity
  have hlogt : Real.log t ≤ Real.log (2 * (1 + ε) * (u * Real.log u)) := by
    apply Real.log_le_log htpos'
    exact htle'
  have hlogarg : Real.log (2 * (1 + ε) * (u * Real.log u)) =
      Real.log 2 + Real.log (1 + ε) + Real.log u + Real.log (Real.log u) := by
    rw [show 2 * (1 + ε) * (u * Real.log u) = (2 * (1 + ε)) * (u * Real.log u) by ring,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hlogupos.ne']
    ring
  have hs_eq : rankinSaddleS u = Real.log u + Real.log (Real.log u) + 1 := rfl
  rw [hlogarg] at hlogt
  rw [hs_eq] at hsbig ⊢
  rw [hlogL]
  linarith

/-! ## 5. The unconditional prime-reciprocal saddle estimate -/

/-- **The prime-reciprocal Rankin saddle estimate, unconditionally.**  For every
sequence `p` with `PaperDensityGrowth p` and every `ε > 0`, the tilted prime mass
at the paper cutoff and the saddle tilt is at most
`rankinPrimeConstant = 32` times `e^s / s`. -/
theorem primeReciprocalSaddleUpper_rankinPrimeConstant {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    PrimeReciprocalSaddleUpper rankinPrimeConstant p ε := by
  have hu := tendsto_paperDensityU_of_growth h hε
  have hs := tendsto_rankinSaddleS_of_growth h hε
  have hM1 : Tendsto (fun n => Real.exp (rankinSaddleS (paperDensityU p ε n)) /
      rankinSaddleS (paperDensityU p ε n)) atTop atTop := by
    have h' := (tendsto_exp_div_pow_atTop 1).comp hs
    convert h' using 1
    ext n
    simp [pow_one]
  have hM2 : Tendsto (fun n => Real.exp (rankinSaddleS (paperDensityU p ε n)) /
      (rankinSaddleS (paperDensityU p ε n)) ^ 2) atTop atTop :=
    (tendsto_exp_div_pow_atTop 2).comp hs
  have hlog4le : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog4pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hexp1le : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hexp1pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp1sq : (Real.exp 1) ^ 2 ≤ 9 := by nlinarith
  have hsqrt2le : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  filter_upwards [hs.eventually_ge_atTop 2,
    eventually_two_mul_rankinSaddleS_lt_log_cutoff h hε,
    eventually_four_mul_saddleS_le_logCutoff h hε,
    eventually_logLogCutoff_le_two_mul_saddleS h hε,
    hM2.eventually_ge_atTop 3,
    hM1.eventually_ge_atTop 100] with n hs2 h2s hfour hloglog hM2big hM100
  set u := paperDensityU p ε n with hu_def
  set Y := smoothCutoff (paperT p) (paperError ε) n with hY_def
  set L := Real.log Y with hL_def
  set s := rankinSaddleS u with hs_def
  set β := s / L with hβ_def
  set M := Real.exp s / s with hM_def
  have hspos : 0 < s := by linarith
  have hYpos : 0 < Y := by
    rw [hY_def]
    exact Real.exp_pos _
  have hY_eq : Y = Real.exp L := by
    rw [hL_def, Real.exp_log hYpos]
  have hL_eq : L = (1 + ε) * paperT p n := by
    rw [hL_def, hY_def]
    simp [smoothCutoff, paperError]
  have hY2 : 2 ≤ Y := by
    rw [hY_eq]
    have hL4 : 4 ≤ L := by
      have : 2 * s ≤ L := le_of_lt h2s
      linarith
    calc (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp 4]
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL4
  have hLpos : 0 < L := by
    rw [hL_def]
    exact Real.log_pos (by linarith)
  have hβpos : 0 < β := by
    rw [hβ_def]
    exact div_pos hspos hLpos
  have hβhalf : β < 1 / 2 := by
    rw [hβ_def, div_lt_iff₀ hLpos]
    linarith
  have hβquarter : β ≤ 1 / 4 := by
    rw [hβ_def, div_le_iff₀ hLpos]
    linarith
  have hβle : β ≤ 1 := by linarith
  have hβL : β * L = s := by
    rw [hβ_def]
    field_simp
  have h2βL : 2 / β ≤ L := by
    rw [hβ_def]
    field_simp
    nlinarith [hs2, hLpos]
  have hMpos : 0 < M := by
    rw [hM_def]
    positivity
  have hMge : 3 * s ≤ M := by
    have hMeq : M = (Real.exp s / s ^ 2) * s := by
      rw [hM_def]
      field_simp
    rw [hMeq]
    exact mul_le_mul_of_nonneg_right hM2big hspos.le
  have hlogL_le : Real.log L ≤ 2 * s := by
    simpa [hL_def, hs_def] using hloglog
  have hlogβ_le : Real.log (1 / β) ≤ 2 * s := by
    have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
    have hlog : Real.log (1 / β) = Real.log L - Real.log s := by
      rw [hβ_def, one_div, inv_div]
      rw [Real.log_div hLpos.ne' hspos.ne']
    linarith
  have hlogβ : Real.log (1 / β) + 1 ≤ M := by linarith
  -- the Chebyshev estimate
  have hα0 : (1 / 2 : ℝ) < 1 - β := by linarith
  have hα1 : 1 - β < 1 := by linarith
  have hS := prime_sum_rpow_le (α := 1 - β) hα0 hα1 hY2
  -- the two integrals
  have hJeq : (∫ t in (2 : ℝ)..Y, t ^ (-(1 - β)) / Real.log t)
      = ∫ t in (2 : ℝ)..Real.exp L, t ^ (β - 1) / Real.log t := by
    rw [hY_eq]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show -(1 - β) = β - 1 by ring]
  have hJle : (∫ t in (2 : ℝ)..Y, t ^ (-(1 - β)) / Real.log t) ≤
      Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2 := by
    rw [hJeq]
    have hJ := integral_rpow_div_log_le (β := β) (L := L) hβpos hβhalf.le h2βL
    rw [hβL] at hJ
    have hJ' : (∫ t in (2 : ℝ)..Real.exp L, t ^ (β - 1) / Real.log t) ≤
        Real.exp 1 * (Real.log (1 / β) + 1) + (2 * M + 2 * (Real.exp 1) ^ 2) := by
      simpa [hM_def, mul_div_assoc] using hJ
    have h1 : Real.exp 1 * (Real.log (1 / β) + 1) ≤ Real.exp 1 * M :=
      mul_le_mul_of_nonneg_left hlogβ hexp1pos.le
    linarith
  have hKle : (∫ t in (2 : ℝ)..Y, t ^ (-(1 - β) - 1 / 2)) ≤ 4 * Real.sqrt 2 := by
    have hK := integral_rpow_neg_half_le (α := 1 - β) hα0 hY2
    have hden : (1 / 4 : ℝ) ≤ (1 - β) - 1 / 2 := by linarith
    have hdenpos : (0 : ℝ) < 1 / 4 := by norm_num
    have hstep : Real.sqrt 2 / ((1 - β) - 1 / 2) ≤ Real.sqrt 2 / (1 / 4) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg 2) hdenpos hden
    have hval : Real.sqrt 2 / (1 / 4 : ℝ) = 4 * Real.sqrt 2 := by
      field_simp
    rw [hval] at hstep
    exact hK.trans hstep
  -- assemble
  have hterm1 : 2 * Real.log 4 * Y ^ (1 - (1 - β)) / Real.log Y ≤ 2 * Real.log 4 * M := by
    have hYβ : Y ^ (1 - (1 - β)) = Real.exp s := by
      rw [show 1 - (1 - β) = β by ring, hY_eq,
        Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp]
      congr 1
      linarith [hβL]
    rw [hYβ, ← hL_def]
    have hratio : Real.exp s / L = M * β := by
      rw [hM_def, hβ_def]
      field_simp
    rw [show 2 * Real.log 4 * Real.exp s / L = 2 * Real.log 4 * (Real.exp s / L) by ring,
      hratio]
    have hh : M * β ≤ M := by
      simpa using mul_le_mul_of_nonneg_left hβle (le_of_lt hMpos)
    have hlog4nn : 0 ≤ 2 * Real.log 4 := by positivity
    exact mul_le_mul_of_nonneg_left hh hlog4nn
  have hterm2 : Y ^ (1 / 2 - (1 - β)) ≤ 1 := by
    have hY1 : 1 < Y := by linarith
    have hexp : 1 / 2 - (1 - β) < 0 := by linarith
    exact le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hY1 hexp)
  have hJnonneg : 0 ≤ ∫ t in (2 : ℝ)..Y, t ^ (-(1 - β)) / Real.log t := by
    refine intervalIntegral.integral_nonneg (by linarith) ?_
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    exact div_nonneg (Real.rpow_pos_of_pos (by linarith) _).le
      (Real.log_pos (by linarith)).le
  have hKnonneg : 0 ≤ ∫ t in (2 : ℝ)..Y, t ^ (-(1 - β) - 1 / 2) := by
    refine intervalIntegral.integral_nonneg (by linarith) ?_
    intro t ht
    exact (Real.rpow_pos_of_pos (by linarith [ht.1]) _).le
  have hSmain : (∑ q ∈ (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime, (q : ℝ) ^ (-(1 - β))) ≤
      2 * Real.log 4 * M + 1 +
        (2 * Real.log 4 * (Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2) +
          4 * Real.sqrt 2) := by
    have hbracket : 2 * Real.log 4 *
        (∫ t in (2 : ℝ)..Y, t ^ (-(1 - β)) / Real.log t) +
          ∫ t in (2 : ℝ)..Y, t ^ (-(1 - β) - 1 / 2) ≤
        2 * Real.log 4 * (Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2) +
          4 * Real.sqrt 2 := by
      have h1 : 2 * Real.log 4 *
          (∫ t in (2 : ℝ)..Y, t ^ (-(1 - β)) / Real.log t) ≤
          2 * Real.log 4 * (Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hJle (by positivity)
      linarith
    refine hS.trans ?_
    have hcoef : (1 - β) ≤ 1 := by linarith
    have hbr : 0 ≤ 2 * Real.log 4 *
        (∫ t in (2 : ℝ)..Y, t ^ (-(1 - β)) / Real.log t) +
          ∫ t in (2 : ℝ)..Y, t ^ (-(1 - β) - 1 / 2) := by positivity
    have hmul := mul_le_mul hcoef le_rfl hbr (by norm_num : (0 : ℝ) ≤ 1)
    calc
      2 * Real.log 4 * Y ^ (1 - (1 - β)) / Real.log Y +
          Y ^ (1 / 2 - (1 - β)) +
            (1 - β) * (2 * Real.log 4 *
              (∫ t in (2 : ℝ)..Y, t ^ (-(1 - β)) / Real.log t) +
              ∫ t in (2 : ℝ)..Y, t ^ (-(1 - β) - 1 / 2))
          ≤ 2 * Real.log 4 * M + 1 +
              (2 * Real.log 4 *
                (∫ t in (2 : ℝ)..Y, t ^ (-(1 - β)) / Real.log t) +
                ∫ t in (2 : ℝ)..Y, t ^ (-(1 - β) - 1 / 2)) := by
            linarith
      _ ≤ 2 * Real.log 4 * M + 1 +
              (2 * Real.log 4 * (Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2) +
                4 * Real.sqrt 2) := by linarith
  -- numeric closure
  have hcoef1 : 2 * Real.log 4 ≤ 4 := by linarith
  have hcoef2 : 2 * Real.log 4 * (Real.exp 1 + 2) ≤ 20 := by
    have hsum : Real.exp 1 + 2 ≤ 5 := by linarith
    have := mul_le_mul hcoef1 hsum (by positivity) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have hconst : 1 + 4 * Real.log 4 * (Real.exp 1) ^ 2 + 4 * Real.sqrt 2 ≤ 82 := by
    have h1 : 4 * Real.log 4 ≤ 8 := by linarith
    have hprod : 4 * Real.log 4 * (Real.exp 1) ^ 2 ≤ 8 * 9 :=
      mul_le_mul h1 hexp1sq (sq_nonneg _) (by norm_num)
    have h2 : 4 * Real.sqrt 2 ≤ 8 := by linarith
    linarith
  have hfinal : (∑ q ∈ (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime, (q : ℝ) ^ (-(1 - β))) ≤
      rankinPrimeConstant * Real.exp s / s := by
    have hm : 2 * Real.log 4 * M + 1 +
        (2 * Real.log 4 * (Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2) +
          4 * Real.sqrt 2) ≤ 32 * M := by
      have h1 : 2 * Real.log 4 * (Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2) ≤
          2 * Real.log 4 * ((Real.exp 1 + 2) * M) +
            2 * Real.log 4 * (2 * (Real.exp 1) ^ 2) := by
        have : Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2 =
            (Real.exp 1 + 2) * M + 2 * (Real.exp 1) ^ 2 := by ring
        rw [this]
        ring_nf
        nlinarith [hlog4pos]
      have h2 : 2 * Real.log 4 * ((Real.exp 1 + 2) * M) ≤ 20 * M := by
        rw [show 2 * Real.log 4 * ((Real.exp 1 + 2) * M) =
            (2 * Real.log 4 * (Real.exp 1 + 2)) * M by ring]
        exact mul_le_mul_of_nonneg_right hcoef2 hMpos.le
      have h3 : 2 * Real.log 4 * (2 * (Real.exp 1) ^ 2) ≤ 72 := by
        have h0 : 2 * Real.log 4 * (Real.exp 1) ^ 2 ≤ 36 := by
          have := mul_le_mul hcoef1 hexp1sq (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
          linarith
        rw [show 2 * Real.log 4 * (2 * (Real.exp 1) ^ 2) =
            2 * (2 * Real.log 4 * (Real.exp 1) ^ 2) by ring]
        linarith
      have h4 : 2 * Real.log 4 * M ≤ 4 * M :=
        mul_le_mul_of_nonneg_right hcoef1 hMpos.le
      have h5 : 4 * Real.sqrt 2 ≤ 8 := by linarith
      have hA : 2 * Real.log 4 *
          (Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2) ≤ 24 * M := by
        linarith [h1, h2, h3, hM100]
      have hE : 2 * Real.log 4 * M + 1 +
          (2 * Real.log 4 * (Real.exp 1 * M + 2 * M + 2 * (Real.exp 1) ^ 2) +
            4 * Real.sqrt 2) ≤ 4 * M + 1 + (24 * M + 8) := by
        linarith [hA, h4, h5]
      nlinarith [hE, hM100, hMpos]
    refine hSmain.trans ?_
    rw [show rankinPrimeConstant * Real.exp s / s = 32 * M by
      rw [hM_def, rankinPrimeConstant]
      ring]
    exact hm
  refine ⟨1 - β, hα0, hα1, ?_, hfinal⟩
  rw [show 1 - (1 - β) = β by ring, hβL]

/-- **The sharp paper-scale smooth upper bound, unconditionally.** -/
theorem paperScaleSmoothUpperSharp_one_unconditional {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    PaperScaleSmoothUpperSharp 1 p ε :=
  paperScaleSmoothUpperSharp_one_of_primeReciprocal_explicit h hε
    (primeReciprocalSaddleUpper_rankinPrimeConstant h hε)

/-- **The sharp global odd upper density, unconditionally.** -/
theorem globalOddUpperDensitySharp_one_unconditional {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    GlobalOddUpperDensitySharp 1 p ε :=
  globalOddUpperDensitySharp_one_of_primeReciprocal_explicit h hε
    (primeReciprocalSaddleUpper_rankinPrimeConstant h hε)

/-- **The Rankin saddle-point envelope, unconditionally.**  The Euler-product
reduction `rankinSaddlePointUpper_one_of_primeReciprocal` turns the prime mass
estimate into the saddle envelope with the explicit constant
`rankinEulerConstant = 128`. -/
theorem rankinSaddlePointUpper_unconditional {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    RankinSaddlePointUpper rankinEulerConstant p ε :=
  rankinSaddlePointUpper_one_of_primeReciprocal
    (primeReciprocalSaddleUpper_rankinPrimeConstant h hε)

/-! ## Axiom audit -/

#print axioms prime_sum_rpow_eq_primeCounting_abel
#print axioms pi_le_two_log4_mul_div_add_sqrt
#print axioms prime_sum_rpow_le
#print axioms integral_rpow_neg_half_le
#print axioms integral_small_rpow_div_log_le
#print axioms integral_tail_rpow_div_log_le
#print axioms integral_rpow_div_log_le
#print axioms eventually_four_mul_saddleS_le_logCutoff
#print axioms eventually_logLogCutoff_le_two_mul_saddleS
#print axioms rankinSaddlePointUpper_unconditional
#print axioms primeReciprocalSaddleUpper_rankinPrimeConstant
#print axioms paperScaleSmoothUpperSharp_one_unconditional
#print axioms globalOddUpperDensitySharp_one_unconditional

end

end Cogentic.RandomizedL30PrimeReciprocal
