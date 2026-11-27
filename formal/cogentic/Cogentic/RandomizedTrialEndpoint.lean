import Cogentic.RandomizedSmallPrimePrepass

/-!
# An unconditional end-to-end trial-division endpoint

This file packages the counted trial-division prepass
`Cogentic.RandomizedSmallPrimePrepass.trialPrepass` as a standalone randomized
factoring algorithm with cutoff `B n = Nat.sqrt n`.

The resulting theorem is deliberately weak but completely unconditional:

* every successful output is a verified nontrivial factorization of `n`;
* on every composite `n ≥ 2` the success probability is exactly `1`;
* the expected charged work is at most `54 * sqrt n * (log₂ n + 1)^2 + 2`,
  hence `exp((1/2 + ε) log n)` for every `ε > 0` and all sufficiently large `n`.

In particular there is no `HardEpochAsymptoticBound` or any other epoch
hypothesis.  The honest exponent is `1/2` (in the natural logarithm), not the
`L[1/3]` shape of the main analytic development; trial division to `sqrt n`
cannot do better than this on its own.
-/

namespace Cogentic.RandomizedTrialEndpoint

open Filter Real
open scoped ENNReal Topology

open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochKernel
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSmallPrimePrepass

/-- A standalone randomized factoring algorithm in the cost model: a per-input
PMF of epochs and a charged attempt returning either a verified factorization
or failure. -/
structure RandomizedFactorAlgorithm where
  epoch : ∀ _n : ℕ, PMF Unit
  attempt : ∀ n : ℕ, Unit → Option (Factors n) × ℕ

namespace RandomizedFactorAlgorithm

/-- Probability (mass) that one epoch succeeds on input `n`. -/
noncomputable def successMass (A : RandomizedFactorAlgorithm) (n : ℕ) : ℝ≥0∞ :=
  ((A.epoch n).map (A.attempt n)).toOuterMeasure {o | o.1 ≠ none}

/-- Expected charged work of one epoch, including the unit branching charge. -/
noncomputable def expectedWork (A : RandomizedFactorAlgorithm) (n : ℕ) : ℝ≥0∞ :=
  mean (A.epoch n) (fun a => ((A.attempt n a).2 + 1 : ℕ)) + 1

end RandomizedFactorAlgorithm

/-- The concrete deterministic cutoff `B n = ⌊√n⌋`. -/
def trialSqrtCutoff (n : ℕ) : ℕ := Nat.sqrt n

/-- Trial division up to `⌊√n⌋`, driven by a single deterministic epoch. -/
noncomputable def trialSqrtAlgorithm : RandomizedFactorAlgorithm where
  epoch := trialPrepassEpoch
  attempt := fun n => trialPrepassAttempt trialSqrtCutoff n

/-! ## Small prime factor below the square root -/

/-- Every composite `n ≥ 2` has a prime factor at most `⌊√n⌋`. -/
theorem exists_primeFactor_le_sqrt {n : ℕ} (hn : 2 ≤ n) (hcomp : ¬ n.Prime) :
    ∃ p ∈ n.primeFactors, p ≤ Nat.sqrt n := by
  have hpos : 0 < n := by omega
  refine ⟨n.minFac, ?_, ?_⟩
  · rw [Nat.mem_primeFactors]
    exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩
  · have hdiv : n.minFac ≤ n / n.minFac := Nat.minFac_le_div hpos hcomp
    have hmul : n.minFac * (n / n.minFac) = n :=
      Nat.mul_div_cancel' (Nat.minFac_dvd n)
    have hsq : n.minFac * n.minFac ≤ n := by
      calc
        n.minFac * n.minFac ≤ n.minFac * (n / n.minFac) :=
          Nat.mul_le_mul_left _ hdiv
        _ = n := hmul
    exact Nat.le_sqrt.mpr hsq

/-- Consequently the square-root cutoff has a small prime factor on every
composite input. -/
theorem hasSmallPrimeFactor_sqrt {n : ℕ} (hn : 2 ≤ n) (hcomp : ¬ n.Prime) :
    HasSmallPrimeFactor ((Nat.sqrt n : ℕ) : ℝ) n := by
  obtain ⟨p, hp, hle⟩ := exists_primeFactor_le_sqrt hn hcomp
  exact ⟨p, hp, by exact_mod_cast hle⟩

/-! ## Correctness and success probability -/

/-- Any successful output of the square-root trial-division attempt is a
verified nontrivial factorization of `n`. -/
theorem trialSqrt_attempt_correct {n : ℕ} (fac : Factors n)
    (_h : (trialSqrtAlgorithm.attempt n ()).1 = some fac) :
    2 ≤ fac.val.1 ∧ 2 ≤ fac.val.2 ∧ fac.val.1 * fac.val.2 = n :=
  fac.property

/-- On every composite input the square-root trial-division epoch succeeds with
probability exactly `1`. -/
theorem trialSqrt_successMass_eq_one {n : ℕ} (hn : 2 ≤ n) (hcomp : ¬ n.Prime) :
    trialSqrtAlgorithm.successMass n = 1 := by
  unfold RandomizedFactorAlgorithm.successMass
  simpa [trialSqrtAlgorithm, trialSqrtCutoff, trialPrepassEpoch, trialPrepassAttempt]
    using trialPrepass_success_prob_one (B := Nat.sqrt n) hn hcomp
      (hasSmallPrimeFactor_sqrt hn hcomp)

/-! ## Expected work -/

/-- Explicit finite expected-work bound for the square-root cutoff, with no
asymptotic or epoch hypothesis. -/
theorem trialSqrt_expectedWork_le (n : ℕ) :
    trialSqrtAlgorithm.expectedWork n ≤
      ENNReal.ofReal (54 * (Nat.sqrt n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 + 2) := by
  unfold RandomizedFactorAlgorithm.expectedWork
  simp only [trialSqrtAlgorithm, trialSqrtCutoff, trialPrepassEpoch,
    trialPrepassAttempt, mean_pure]
  have hwork := trialPrepass_work_le (Nat.sqrt n) n
  have hsize : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  have hsizeR : (n.size : ℝ) ≤ (n.log2 : ℝ) + 1 := by exact_mod_cast hsize
  have hworkR : ((trialPrepass (Nat.sqrt n) n).2 : ℝ) ≤
      54 * (Nat.sqrt n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 := by
    have hcast : ((trialPrepass (Nat.sqrt n) n).2 : ℝ) ≤
        54 * (Nat.sqrt n : ℝ) * (n.size : ℝ) ^ 2 := by
      exact_mod_cast hwork
    exact hcast.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hsizeR 2) (by positivity))
  have htarget : (((trialPrepass (Nat.sqrt n) n).2 + 1 : ℕ) : ℝ) + 1 ≤
      54 * (Nat.sqrt n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 + 2 := by
    push_cast
    linarith
  have hcast_eq :
      ((((trialPrepass (Nat.sqrt n) n).2 + 1 : ℕ) : ℝ≥0∞) + 1) =
        ENNReal.ofReal ((((trialPrepass (Nat.sqrt n) n).2 + 1 : ℕ) : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [hcast_eq]
  exact ENNReal.ofReal_le_ofReal htarget

/-- A small helper: on the relevant range the `L[1/3]` scale is below `log n`. -/
private theorem scale_le_log_of_one_le {n : ℕ} (hlog : 1 ≤ Real.log n) :
    scale n ≤ Real.log n := by
  have hlogpos : 0 < Real.log n := lt_of_lt_of_le zero_lt_one hlog
  have hllog_nonneg : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlog
  have hllog_le : Real.log (Real.log n) ≤ Real.log n := Real.log_le_self hlogpos.le
  calc
    scale n = (Real.log n) ^ (1 / 3 : ℝ) * (Real.log (Real.log n)) ^ (2 / 3 : ℝ) := rfl
    _ ≤ (Real.log n) ^ (1 / 3 : ℝ) * (Real.log n) ^ (2 / 3 : ℝ) := by
      gcongr
    _ = (Real.log n) ^ ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by
      rw [Real.rpow_add hlogpos]
    _ = Real.log n := by norm_num

/-- Unconditional honest asymptotic bound: for every positive `ε`, the expected
work of square-root trial division is eventually at most
`exp((1/2 + ε) log n)`.  This is an `L[1/2, 1/2]` bound, not an `L[1/3]` one. -/
theorem trialSqrt_expectedWork_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      trialSqrtAlgorithm.expectedWork n ≤
        ENNReal.ofReal (Real.exp ((1 / 2 + ε) * Real.log n)) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hlog_tendsto : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
    hlog_tendsto.eventually_ge_atTop 1,
    hlog_tendsto.eventually_ge_atTop ((2 * Real.log 110) / ε),
    eventually_bitPoly_le_exp (A := 110) hε2 2] with n hn hlog1 hbig hpoly
  have hlogpos : 0 < Real.log n := lt_of_lt_of_le zero_lt_one hlog1
  have hscale_le : scale n ≤ Real.log n := scale_le_log_of_one_le hlog1
  have hpoly' : ((n.log2 : ℝ) + 1) ^ 2 ≤ Real.exp ((ε / 2) * Real.log n) := by
    have hpoly0 : 0 ≤ ((n.log2 : ℝ) + 1) ^ 2 := by positivity
    have hle : ((n.log2 : ℝ) + 1) ^ 2 ≤ 110 * ((n.log2 : ℝ) + 1) ^ 2 := by
      nlinarith
    refine hle.trans (hpoly.trans ?_)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hscale_le hε2.le)
  have hsqrt : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast (show 0 < n by omega))]
    congr 1
    ring
  have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ n by omega)
  have hnat : (Nat.sqrt n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have h := Real.nat_sqrt_le_real_sqrt (a := n)
    linarith
  have hlog110 : Real.log 110 ≤ (ε / 2) * Real.log n := by
    have hbig' : 2 * Real.log 110 ≤ Real.log n * ε := by
      exact (div_le_iff₀ hε).mp hbig
    have htwo : 2 * Real.log 110 ≤ 2 * ((ε / 2) * Real.log n) := by
      calc
        2 * Real.log 110 ≤ Real.log n * ε := hbig'
        _ = 2 * ((ε / 2) * Real.log n) := by ring
    linarith
  refine (trialSqrt_expectedWork_le n).trans (ENNReal.ofReal_le_ofReal ?_)
  have hpoly_ge1 : 1 ≤ ((n.log2 : ℝ) + 1) ^ 2 := by
    have hb : (1 : ℝ) ≤ (n.log2 : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n.log2
      linarith
    exact one_le_pow₀ hb
  have hstep1 : 54 * (Nat.sqrt n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 + 2 ≤
      110 * Real.sqrt (n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 := by
    have hA : 54 * (Nat.sqrt n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 ≤
        108 * Real.sqrt (n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnat (by norm_num : (0 : ℝ) ≤ 54))
        (show 0 ≤ ((n.log2 : ℝ) + 1) ^ 2 by positivity)
      nlinarith
    have hB : (2 : ℝ) ≤ 2 * Real.sqrt (n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 := by
      nlinarith
    nlinarith
  have hstep2 : 110 * Real.sqrt (n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 ≤
      110 * Real.exp (Real.log n / 2) * Real.exp ((ε / 2) * Real.log n) := by
    rw [hsqrt]
    gcongr
  have hstep3 : 110 * Real.exp (Real.log n / 2) * Real.exp ((ε / 2) * Real.log n) ≤
      Real.exp ((1 / 2 + ε) * Real.log n) := by
    calc
      110 * Real.exp (Real.log n / 2) * Real.exp ((ε / 2) * Real.log n)
          = Real.exp (Real.log 110) * Real.exp (Real.log n / 2) *
              Real.exp ((ε / 2) * Real.log n) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 110)]
      _ = Real.exp (Real.log 110 + (Real.log n / 2 + (ε / 2) * Real.log n)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            ring_nf
      _ ≤ Real.exp ((ε / 2) * Real.log n +
            (Real.log n / 2 + (ε / 2) * Real.log n)) := by
            exact Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp ((1 / 2 + ε) * Real.log n) := by
            congr 1
            ring
  exact hstep1.trans (hstep2.trans hstep3)

/-! ## End-to-end statements -/

/-- Pointwise unconditional end-to-end guarantee for square-root trial division:
correctness of every successful output, success probability `1` on composites,
and the explicit finite expected-work bound. -/
theorem trialSqrt_endpoint (n : ℕ) (hn : 2 ≤ n) (hcomp : ¬ n.Prime) :
    trialSqrtAlgorithm.successMass n = 1 ∧
    (∀ fac : Factors n, (trialSqrtAlgorithm.attempt n ()).1 = some fac →
      2 ≤ fac.val.1 ∧ 2 ≤ fac.val.2 ∧ fac.val.1 * fac.val.2 = n) ∧
    trialSqrtAlgorithm.expectedWork n ≤
      ENNReal.ofReal (54 * (Nat.sqrt n : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 + 2) :=
  ⟨trialSqrt_successMass_eq_one hn hcomp,
    fun fac h => trialSqrt_attempt_correct fac h,
    trialSqrt_expectedWork_le n⟩

/-- The headline unconditional asymptotic endpoint: for every `ε > 0` and all
sufficiently large composite `n`, square-root trial division succeeds with
probability `1`, is correct on every success, and has expected work at most
`exp((1/2 + ε) log n)`.  No epoch hypothesis occurs anywhere. -/
theorem trialSqrt_endpoint_asymptotic :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (_hn : 2 ≤ n), ¬ n.Prime →
      trialSqrtAlgorithm.successMass n = 1 ∧
      (∀ fac : Factors n, (trialSqrtAlgorithm.attempt n ()).1 = some fac →
        2 ≤ fac.val.1 ∧ 2 ≤ fac.val.2 ∧ fac.val.1 * fac.val.2 = n) ∧
      trialSqrtAlgorithm.expectedWork n ≤
        ENNReal.ofReal (Real.exp ((1 / 2 + ε) * Real.log n)) := by
  intro ε hε
  filter_upwards [trialSqrt_expectedWork_le_exp hε] with n hcost
  intro hn hcomp
  exact ⟨trialSqrt_successMass_eq_one hn hcomp,
    fun fac h => trialSqrt_attempt_correct fac h, hcost⟩

/-- Existential form of the unconditional endpoint. -/
theorem exists_trialSqrt_endpoint :
    ∃ A : RandomizedFactorAlgorithm,
      (∀ n (_hn : 2 ≤ n) (_hcomp : ¬ n.Prime),
        A.successMass n = 1 ∧
        (∀ fac : Factors n, (A.attempt n ()).1 = some fac →
          2 ≤ fac.val.1 ∧ 2 ≤ fac.val.2 ∧ fac.val.1 * fac.val.2 = n)) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        A.expectedWork n ≤
          ENNReal.ofReal (Real.exp ((1 / 2 + ε) * Real.log n))) := by
  refine ⟨trialSqrtAlgorithm, ?_, ?_⟩
  · intro n hn hcomp
    exact ⟨trialSqrt_successMass_eq_one hn hcomp,
      fun fac h => trialSqrt_attempt_correct fac h⟩
  · intro ε hε
    exact trialSqrt_expectedWork_le_exp hε

#print axioms exists_primeFactor_le_sqrt
#print axioms hasSmallPrimeFactor_sqrt
#print axioms trialSqrt_successMass_eq_one
#print axioms trialSqrt_expectedWork_le
#print axioms trialSqrt_expectedWork_le_exp
#print axioms trialSqrt_endpoint
#print axioms trialSqrt_endpoint_asymptotic
#print axioms exists_trialSqrt_endpoint

end Cogentic.RandomizedTrialEndpoint
