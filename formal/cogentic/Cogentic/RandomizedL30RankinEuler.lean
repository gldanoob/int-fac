import Cogentic.RandomizedL30SharpRankin

set_option maxHeartbeats 4000000

/-!
# L30: the Euler-product half of the Rankin saddle point

`Cogentic/RandomizedL30SharpRankin` isolates the analytic input of the sharp
Rankin upper bound as

* `RankinEulerSaddleUpper A p ε` — the Euler-product envelope for *every*
  tilt `α ∈ (1/2, 1)`, and
* `RankinSaddlePointUpper A p ε` — the same envelope only at the optimal
  saddle tilt `α = 1 - s / log Y`, `s = log u + log log u + 1`.

This file supplies the Euler-product half from the explicit prime-reciprocal
saddle estimate

`∑_{q ≤ Y, q prime} q^{-α} ≤ C e^s / s`,

which is the classical Chebyshev/partial-summation estimate for the tilted
prime mass.  The reduction is the elementary inequality

`log ∏_{q ≤ Y} (1 - q^{-α})^{-1} ≤ 4 ∑_{q ≤ Y} q^{-α}`,

valid for every `α > 1/2` because `q^{-α} ≤ 2^{-1/2} < 3/4`.

## Why the saddle-point form, not the all-tilt form

The predicate `RankinEulerSaddleUpper A p ε` is *not* the right Euler-product
input.  It quantifies over every `α ∈ (1/2, 1)`, in particular over
`α = 1 - 1 / log Y`, where the right-hand side is the constant `A e` while

`log ∏_{q ≤ Y} (1 - q^{-1})^{-1} ~ log log Y`

tends to infinity.  Thus the all-tilt envelope is false, while the saddle-point
tilt `s = log u + log log u + 1` has `s → ∞` and the envelope is the genuine
Rankin/Chebyshev estimate.  Accordingly the file proves

* `rankinSaddlePointUpper_of_primeReciprocal` — prime-reciprocal saddle
  estimate ⇒ `RankinSaddlePointUpper (4 C)`,
* `rankinSaddlePointUpper_one_of_primeReciprocal` — the explicit constant
  `C = 32` gives `RankinSaddlePointUpper 128`,
* `paperScaleSmoothUpperSharp_one_of_primeReciprocal` — the sharp paper-scale
  smooth upper bound with `C = 1`,
* `globalOddUpperDensitySharp_one_of_primeReciprocal` — the odd-density
  transfer with `C = 1`.

The prime-reciprocal saddle estimate is stated as the explicit predicate
`PrimeReciprocalSaddleUpper C p ε`.  It is the only analytic input left; it
follows from Chebyshev's bound `π(x) ≤ K x / log x` (`Chebyshev.eventually_primeCounting_le`)
together with partial summation on dyadic bands.  No `sorry`, `admit`, `axiom`
or `native_decide` is used, and no count, mass or error is set to zero.
-/

namespace Cogentic.RandomizedL30RankinEuler

open Filter Real
open scoped Classical BigOperators
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30SharpRankin
open Cogentic.RandomizedL30Sharp
open Cogentic.Randomized

noncomputable section

/-! ## 1. The explicit constant and the missing prime-reciprocal input -/

/-- The explicit constant used in the prime-reciprocal saddle envelope.  It is
deliberately generous: Chebyshev's `θ(x) ≤ (log 4) x` gives a constant below
`32` after partial summation. -/
def rankinPrimeConstant : ℝ := 32

theorem rankinPrimeConstant_pos : 0 < rankinPrimeConstant := by
  norm_num [rankinPrimeConstant]

/-- The explicit constant in the resulting Euler-product envelope:
`4 * rankinPrimeConstant = 128`. -/
def rankinEulerConstant : ℝ := 4 * rankinPrimeConstant

theorem rankinEulerConstant_pos : 0 < rankinEulerConstant := by
  unfold rankinEulerConstant rankinPrimeConstant
  norm_num

/-- **The prime-reciprocal Rankin saddle estimate.**  At every large paper
scale there is a tilt `α ∈ (0,1)` at the saddle `(1-α) log Y = s` for which the
tilted prime mass is at most `C e^s / s`.

This is the Chebyshev/partial-summation estimate for `∑_{q ≤ Y} q^{-α}`.  It is
the only analytic input which is not already present in the tree; the rest of
the Rankin Euler-product bound is elementary. -/
def PrimeReciprocalSaddleUpper (C : ℝ) (p : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∃ α : ℝ,
    (1 / 2 : ℝ) < α ∧ α < 1 ∧
      (1 - α) * Real.log (smoothCutoff (paperT p) (paperError ε) n) =
        rankinSaddleS (paperDensityU p ε n) ∧
      (∑ q ∈ (Finset.Icc 2 ⌊smoothCutoff (paperT p) (paperError ε) n⌋₊).filter
          Nat.Prime, (q : ℝ) ^ (-α)) ≤
        C * Real.exp (rankinSaddleS (paperDensityU p ε n)) /
          rankinSaddleS (paperDensityU p ε n)

/-! ## 2. The elementary Euler-product bound -/

/-- `2^{-1/2} < 3/4`.  This is the only numerical input to the convergence of
the logarithm of the Euler product. -/
theorem rpow_neg_half_two_lt_three_quarters :
    (2 : ℝ) ^ (-(1 / 2 : ℝ)) < (3 : ℝ) / 4 := by
  have hsq : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = (-1 : ℝ) by norm_num]
    rw [Real.rpow_neg_one]
    norm_num
  have hlt : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 < ((3 : ℝ) / 4) ^ 2 := by
    rw [hsq]
    norm_num
  exact (sq_lt_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4)).mp hlt

/-- **The Euler product is controlled by the tilted prime mass.**  For every
tilt `α > 1/2`,

`log ∏_{q ≤ Y} (1 - q^{-α})^{-1} ≤ 4 ∑_{q ≤ Y, q prime} q^{-α}`.

The proof only uses `-log (1-x) ≤ x/(1-x) ≤ 4x` for `0 < x < 3/4`, and
`q^{-α} ≤ 2^{-1/2} < 3/4` for `q ≥ 2`. -/
theorem log_eulerProduct_le_four_mul_primeSum {Y α : ℝ} (hα0 : (1 / 2 : ℝ) < α) :
    Real.log
        (∏ q ∈ (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime,
          (1 - (q : ℝ) ^ (-α))⁻¹)
      ≤ 4 * ∑ q ∈ (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime,
          (q : ℝ) ^ (-α) := by
  classical
  let P : Finset ℕ := (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime
  have hterm (q : ℕ) (hq : q ∈ P) :
      Real.log ((1 - (q : ℝ) ^ (-α))⁻¹) ≤ 4 * (q : ℝ) ^ (-α) := by
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqprime.two_le
    have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
    have hxpos : (0 : ℝ) < (q : ℝ) ^ (-α) := Real.rpow_pos_of_pos hqpos _
    have hx34 : (q : ℝ) ^ (-α) ≤ (3 : ℝ) / 4 := by
      have h1 : (q : ℝ) ^ (-α) ≤ (2 : ℝ) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hq2
          (by linarith : -α ≤ 0)
      have h2 : (2 : ℝ) ^ (-α) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : -α ≤ -(1 / 2 : ℝ))
      exact h1.trans (h2.trans rpow_neg_half_two_lt_three_quarters.le)
    have h1mx : 0 < 1 - (q : ℝ) ^ (-α) := by linarith
    calc
      Real.log ((1 - (q : ℝ) ^ (-α))⁻¹)
          ≤ (1 - (q : ℝ) ^ (-α))⁻¹ - 1 :=
            Real.log_le_sub_one_of_pos (inv_pos.mpr h1mx)
      _ = (q : ℝ) ^ (-α) / (1 - (q : ℝ) ^ (-α)) := by
            field_simp
            ring
      _ ≤ 4 * (q : ℝ) ^ (-α) := by
            rw [div_le_iff₀ h1mx]
            nlinarith [hxpos, hx34]
  have hfac : ∀ q ∈ P, (1 - (q : ℝ) ^ (-α))⁻¹ ≠ 0 := by
    intro q hq
    apply inv_ne_zero
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqprime.two_le
    have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
    have hx1 : (q : ℝ) ^ (-α) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith : (1 : ℝ) < (q : ℝ))
        (by linarith : -α < 0)
    linarith
  calc
    Real.log
        (∏ q ∈ (Finset.Icc 2 ⌊Y⌋₊).filter Nat.Prime,
          (1 - (q : ℝ) ^ (-α))⁻¹)
        = ∑ q ∈ P, Real.log ((1 - (q : ℝ) ^ (-α))⁻¹) := Real.log_prod hfac
    _ ≤ ∑ q ∈ P, 4 * (q : ℝ) ^ (-α) := Finset.sum_le_sum hterm
    _ = 4 * ∑ q ∈ P, (q : ℝ) ^ (-α) := by
          rw [← Finset.mul_sum]

/-! ## 3. From the prime-reciprocal saddle input to the Rankin saddle -/

/-- **The prime-reciprocal saddle estimate gives the Rankin saddle envelope.**
The constant is multiplied by `4`; no other loss occurs. -/
theorem rankinSaddlePointUpper_of_primeReciprocal
    {C : ℝ} (_hC : 0 ≤ C) {p : ℕ → ℝ} {ε : ℝ}
    (hP : PrimeReciprocalSaddleUpper C p ε) :
    RankinSaddlePointUpper (4 * C) p ε := by
  filter_upwards [hP] with n hn
  obtain ⟨α, hαhalf, hα1, htilt, hsum⟩ := hn
  refine ⟨α, by linarith, hα1, htilt, ?_⟩
  have hlog := log_eulerProduct_le_four_mul_primeSum
    (Y := smoothCutoff (paperT p) (paperError ε) n) (α := α) hαhalf
  have hstep : 4 * (∑ q ∈ (Finset.Icc 2
        ⌊smoothCutoff (paperT p) (paperError ε) n⌋₊).filter Nat.Prime,
        (q : ℝ) ^ (-α))
      ≤ 4 * (C * Real.exp (rankinSaddleS (paperDensityU p ε n)) /
          rankinSaddleS (paperDensityU p ε n)) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)
  calc
    Real.log (rankinEulerProduct (paperT p) (paperError ε) α n)
        = Real.log
            (∏ q ∈ (Finset.Icc 2
                ⌊smoothCutoff (paperT p) (paperError ε) n⌋₊).filter
                Nat.Prime, (1 - (q : ℝ) ^ (-α))⁻¹) := rfl
    _ ≤ 4 * (∑ q ∈ (Finset.Icc 2
          ⌊smoothCutoff (paperT p) (paperError ε) n⌋₊).filter Nat.Prime,
          (q : ℝ) ^ (-α)) := hlog
    _ ≤ 4 * (C * Real.exp (rankinSaddleS (paperDensityU p ε n)) /
          rankinSaddleS (paperDensityU p ε n)) := hstep
    _ = (4 * C) * Real.exp (rankinSaddleS (paperDensityU p ε n)) /
          rankinSaddleS (paperDensityU p ε n) := by ring

/-- **The explicit constant form.**  The prime constant `32` gives the Euler
constant `128`. -/
theorem rankinSaddlePointUpper_one_of_primeReciprocal
    {p : ℕ → ℝ} {ε : ℝ} (hP : PrimeReciprocalSaddleUpper rankinPrimeConstant p ε) :
    RankinSaddlePointUpper rankinEulerConstant p ε := by
  have h := rankinSaddlePointUpper_of_primeReciprocal
    (C := rankinPrimeConstant) rankinPrimeConstant_pos.le hP
  simpa [rankinEulerConstant] using h

/-! ## 4. The sharp upper density with `C = 1` -/

/-- **The sharp paper-scale smooth upper bound with constant `1`.**  Composing
the Rankin saddle envelope with
`paperScaleSmoothUpperSharp_one_of_saddle` gives the sharp exponent and the
explicit constant `C = 1`. -/
theorem paperScaleSmoothUpperSharp_one_of_primeReciprocal
    {C : ℝ} (hC : 0 ≤ C) {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ}
    (hε : 0 < ε) (hP : PrimeReciprocalSaddleUpper C p ε) :
    PaperScaleSmoothUpperSharp 1 p ε :=
  paperScaleSmoothUpperSharp_one_of_saddle h hε
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC)
    (rankinSaddlePointUpper_of_primeReciprocal hC hP)

/-- The explicit-constant form of the sharp paper-scale smooth upper bound. -/
theorem paperScaleSmoothUpperSharp_one_of_primeReciprocal_explicit
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    (hP : PrimeReciprocalSaddleUpper rankinPrimeConstant p ε) :
    PaperScaleSmoothUpperSharp 1 p ε :=
  paperScaleSmoothUpperSharp_one_of_saddle h hε rankinEulerConstant_pos.le
    (rankinSaddlePointUpper_one_of_primeReciprocal hP)

/-- **The sharp global odd upper density with constant `1`.**  This is the
parity transfer of `paperScaleSmoothUpperSharp_one_of_primeReciprocal`. -/
theorem globalOddUpperDensitySharp_one_of_primeReciprocal
    {C : ℝ} (hC : 0 ≤ C) {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ}
    (hε : 0 < ε) (hP : PrimeReciprocalSaddleUpper C p ε) :
    GlobalOddUpperDensitySharp 1 p ε :=
  globalOddUpperDensitySharp_of_paperScaleSharp h
    (paperScaleSmoothUpperSharp_one_of_primeReciprocal hC h hε hP)

/-- The explicit-constant form of the sharp odd-density transfer. -/
theorem globalOddUpperDensitySharp_one_of_primeReciprocal_explicit
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε)
    (hP : PrimeReciprocalSaddleUpper rankinPrimeConstant p ε) :
    GlobalOddUpperDensitySharp 1 p ε :=
  globalOddUpperDensitySharp_of_paperScaleSharp h
    (paperScaleSmoothUpperSharp_one_of_primeReciprocal_explicit h hε hP)

/-- **The original all-tilt composition.**  This records the exact composition
with `paperScaleSmoothUpperSharp_one_of_eulerSaddle` requested by the sharp
Rankin reduction.  The hypothesis `RankinEulerSaddleUpper A p ε` quantifies over
*every* tilt `α ∈ (1/2,1)`; as explained in the module docstring this all-tilt
form is over-strong (at `α = 1 - 1/log Y` its right-hand side is bounded while
the Euler product grows like `log log Y`).  The sound Euler-product input proved
in this file is `PrimeReciprocalSaddleUpper`, which feeds the saddle-point
composition above. -/
theorem paperScaleSmoothUpperSharp_one_of_rankinEulerSaddle
    {A : ℝ} (hA : 0 ≤ A) {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ}
    (hε : 0 < ε) (hE : RankinEulerSaddleUpper A p ε) :
    PaperScaleSmoothUpperSharp 1 p ε :=
  paperScaleSmoothUpperSharp_one_of_eulerSaddle h hε hA hE

/-! ## Axiom audit -/

#print axioms rpow_neg_half_two_lt_three_quarters
#print axioms log_eulerProduct_le_four_mul_primeSum
#print axioms rankinSaddlePointUpper_of_primeReciprocal
#print axioms rankinSaddlePointUpper_one_of_primeReciprocal
#print axioms paperScaleSmoothUpperSharp_one_of_primeReciprocal
#print axioms paperScaleSmoothUpperSharp_one_of_primeReciprocal_explicit
#print axioms globalOddUpperDensitySharp_one_of_primeReciprocal
#print axioms globalOddUpperDensitySharp_one_of_primeReciprocal_explicit
#print axioms paperScaleSmoothUpperSharp_one_of_rankinEulerSaddle

end

end Cogentic.RandomizedL30RankinEuler
