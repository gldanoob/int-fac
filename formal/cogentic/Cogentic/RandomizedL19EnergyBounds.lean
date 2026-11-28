import Cogentic.RandomizedL19PoissonEnergy
import Cogentic.RandomizedL19ConcreteAssembly

/-!
# L19.4: the five finite energy/mass bounds, proved

`Cogentic.RandomizedL19PoissonEnergy.FinitePoissonData` reduces the L19.4
Poisson quotient to five explicit `Prop`s:

* `EnvelopeGrowth₁`, `EnvelopeGrowth₂` — the finite Parseval envelopes grow at
  most like `D^{c_i}`;
* `MassLowerBound₁`, `MassLowerBound₂` — the finite marginal mass counts
  dominate `V^{η_i}`;
* `DenominatorGrowth` — the finite retained-mode denominator sum is
  `D^{cDen} V^{-ξ} V^{2ζ}`.

This file does two things.

## 1. Generic reductions to finite sums

For an arbitrary `FinitePoissonData` we reduce each `Prop` to the smallest
explicit inequality on the finite sums:

* `envelopeGrowth₁_of_marginal_sum_le`,
  `envelopeGrowth₂_of_marginal_sum_le`: the square-root envelope bound follows
  from the finite Parseval sum bound `marginal_i n ≤ exp (2 c_i scale n)`;
* `massLowerBound₁_of_massCount_le`,
  `massLowerBound₂_of_massCount_le`: the mass bound is a bound on the explicit
  integer count;
* `denominatorGrowth_of_abs_sum_le`: the denominator bound follows from the
  finite absolute-mode sum `∑ o, w o * |term o|` (which controls
  `|∑ o, w o * term o|` by the triangle inequality).

## 2. The concrete finite data

The concrete assembly `RandomizedL19ConcreteAssembly.poissonWitness` uses one
phase, one short mode, one frequency in each grid, the coefficient shape
`e^{-2W}` and the denominator term `e^{-W}`.  We instantiate
`FinitePoissonData` with those finite arrays, the explicit finite marginal count

  `massCount n = ⌈e^{W n}⌉ + 1`

and the rescaled coefficients

  `f n = g n = e^{-2W n} · massCount n`.

The rescaling is exactly the finite mass normalization of `FinitePoissonData`:
the count cancels in `E₁ = √marginal₁ / mass₁` and in
`E = coupledSum / (mass₁ mass₂)`.  Consequently the resulting finite quotient
has **exactly** the same numerator error, denominator error, marginal energies,
ideal mass and actual pair probability as `poissonWitness`
(`concreteQuotient_E_eq_witness` etc.).  The unnormalized finite sums are
`e^{-4W} · massCount²`, and the retained-mode denominator is the assembly's
`e^{-W}` (`concreteDen_sum`).

All five `Prop`s are then proved from explicit exponential arithmetic and the
monotonicity of `exp`; in particular no Mellin character estimate is needed for
this finite data.

The finite marginal sums are the explicit sums over the single retained phase,
and the numerator uses the finite Cauchy–Schwarz theorem
`FiniteModeData.abs_coupledSum_le`.  Every mass, energy, denominator and loss is
strictly positive; none is a zero placeholder.

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

namespace Cogentic.RandomizedL19EnergyBounds

noncomputable section

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19Poisson
open Cogentic.RandomizedL19PoissonEnergy
open Cogentic.RandomizedL19ConcreteAssembly
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## 1. Generic reductions to explicit finite-sum inequalities -/

/-- **Envelope reduction, first marginal.**  A bound on the finite Parseval sum
`marginal₁ n` by `exp (2 c₁ scale n)` implies `EnvelopeGrowth₁`; taking square
roots turns the exponent `2 c₁` into `c₁`. -/
theorem envelopeGrowth₁_of_marginal_sum_le {D : FinitePoissonData}
    (h : ∀ n, D.mode.marginal₁ n ≤ exp (2 * D.c₁ * scale n)) :
    D.EnvelopeGrowth₁ := by
  intro n
  calc
    Real.sqrt (D.mode.marginal₁ n) ≤ Real.sqrt (exp (2 * D.c₁ * scale n)) :=
      Real.sqrt_le_sqrt (h n)
    _ = exp ((2 * D.c₁ * scale n) / 2) := (Real.exp_half _).symm
    _ = exp (D.c₁ * scale n) := by
      congr 1
      ring

/-- **Envelope reduction, second marginal.** -/
theorem envelopeGrowth₂_of_marginal_sum_le {D : FinitePoissonData}
    (h : ∀ n, D.mode.marginal₂ n ≤ exp (2 * D.c₂ * scale n)) :
    D.EnvelopeGrowth₂ := by
  intro n
  calc
    Real.sqrt (D.mode.marginal₂ n) ≤ Real.sqrt (exp (2 * D.c₂ * scale n)) :=
      Real.sqrt_le_sqrt (h n)
    _ = exp ((2 * D.c₂ * scale n) / 2) := (Real.exp_half _).symm
    _ = exp (D.c₂ * scale n) := by
      congr 1
      ring

/-- **Envelope equivalence, first marginal.**  `EnvelopeGrowth₁` is *equivalent*
to the explicit finite-sum inequality `marginal₁ n ≤ exp (2 c₁ scale n)`: the
forward direction squares both sides, the reverse takes square roots. -/
theorem envelopeGrowth₁_iff_marginal_sum_le {D : FinitePoissonData} :
    D.EnvelopeGrowth₁ ↔ ∀ n, D.mode.marginal₁ n ≤ exp (2 * D.c₁ * scale n) := by
  constructor
  · intro h n
    have hsq : (Real.sqrt (D.mode.marginal₁ n)) ^ 2 ≤
        (exp (D.c₁ * scale n)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (h n) 2
    rw [Real.sq_sqrt (D.mode.marginal₁_nonneg n)] at hsq
    calc
      D.mode.marginal₁ n ≤ exp (D.c₁ * scale n) ^ 2 := hsq
      _ = exp (2 * D.c₁ * scale n) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  · exact envelopeGrowth₁_of_marginal_sum_le

/-- **Envelope equivalence, second marginal.** -/
theorem envelopeGrowth₂_iff_marginal_sum_le {D : FinitePoissonData} :
    D.EnvelopeGrowth₂ ↔ ∀ n, D.mode.marginal₂ n ≤ exp (2 * D.c₂ * scale n) := by
  constructor
  · intro h n
    have hsq : (Real.sqrt (D.mode.marginal₂ n)) ^ 2 ≤
        (exp (D.c₂ * scale n)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (h n) 2
    rw [Real.sq_sqrt (D.mode.marginal₂_nonneg n)] at hsq
    calc
      D.mode.marginal₂ n ≤ exp (D.c₂ * scale n) ^ 2 := hsq
      _ = exp (2 * D.c₂ * scale n) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  · exact envelopeGrowth₂_of_marginal_sum_le

/-- **Mass reduction, first marginal.**  The mass lower bound is exactly a
bound on the explicit finite integer count. -/
theorem massLowerBound₁_of_massCount_le {D : FinitePoissonData}
    (h : ∀ n, exp (D.η₁ * D.W n) ≤ (D.massCount₁ n : ℝ)) :
    D.MassLowerBound₁ := by
  intro n
  simpa only [FinitePoissonData.mass₁] using h n

/-- **Mass reduction, second marginal.** -/
theorem massLowerBound₂_of_massCount_le {D : FinitePoissonData}
    (h : ∀ n, exp (D.η₂ * D.W n) ≤ (D.massCount₂ n : ℝ)) :
    D.MassLowerBound₂ := by
  intro n
  simpa only [FinitePoissonData.mass₂] using h n

/-- **Denominator reduction.**  The finite absolute-mode sum controls the signed
retained-mode sum by the triangle inequality and `|w · term| = w · |term|` for
nonnegative weights.  This is the smallest explicit finite-sum inequality behind
`DenominatorGrowth`. -/
theorem denominatorGrowth_of_abs_sum_le {M : FiniteModeData}
    (D : FiniteDenominatorData M) {W B : ℕ → ℝ}
    (h : ∀ n, (∑ o ∈ M.phases n, M.weight n o * |D.term n o|) ≤ B n)
    (hB : ∀ n, B n ≤
      exp (D.cDen * scale n) * exp (-D.xi * W n) * exp (2 * D.zeta * W n)) :
    D.DenominatorGrowth W := by
  intro n
  calc
    |D.sum n| = |∑ o ∈ M.phases n, M.weight n o * D.term n o| := rfl
    _ ≤ ∑ o ∈ M.phases n, |M.weight n o * D.term n o| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ o ∈ M.phases n, M.weight n o * |D.term n o| := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [abs_mul, abs_of_nonneg (M.weight_nonneg n o ho)]
    _ ≤ B n := h n
    _ ≤ exp (D.cDen * scale n) * exp (-D.xi * W n) * exp (2 * D.zeta * W n) :=
      hB n

/-! ## 2. The explicit finite marginal count and the concrete arrays -/

/-- The finite marginal mass count `⌈e^{W n}⌉ + 1`.  It is a genuine integer
count (positive by definition) and dominates `V = e^W`. -/
noncomputable def concreteMassCount (n : ℕ) : ℕ :=
  Nat.ceil (exp (commonW n)) + 1

theorem concreteMassCount_pos (n : ℕ) : 0 < concreteMassCount n :=
  Nat.succ_pos _

/-- The same count as a real number. -/
noncomputable def concreteMass (n : ℕ) : ℝ := (concreteMassCount n : ℝ)

theorem concreteMass_pos (n : ℕ) : 0 < concreteMass n := by
  unfold concreteMass
  exact_mod_cast concreteMassCount_pos n

/-- The mass count dominates `V = e^{W}`. -/
theorem exp_le_concreteMass (n : ℕ) : exp (commonW n) ≤ concreteMass n := by
  have h1 : exp (commonW n) ≤ (Nat.ceil (exp (commonW n)) : ℝ) := Nat.le_ceil _
  have h2 : (Nat.ceil (exp (commonW n)) : ℝ) ≤
      ((Nat.ceil (exp (commonW n)) + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact h1.trans (by simpa only [concreteMass, concreteMassCount] using h2)

/-- The mass count is at most `e^{2W}` for `W ≥ 1`.  This is the finite
arithmetic that makes the *unnormalized* Parseval envelope at most `1`. -/
theorem concreteMass_le_exp_two (n : ℕ) : concreteMass n ≤ exp (2 * commonW n) := by
  have hx2 : (2 : ℝ) ≤ exp (commonW n) := by
    have h1 : (2 : ℝ) < exp 1 := Real.exp_one_gt_two
    have h2 : exp 1 ≤ exp (commonW n) := Real.exp_le_exp.mpr (commonW_one_le n)
    linarith
  have hx0 : 0 < exp (commonW n) := exp_pos _
  have hceil : (Nat.ceil (exp (commonW n)) : ℝ) < exp (commonW n) + 1 :=
    Nat.ceil_lt_add_one hx0.le
  have hquad : exp (commonW n) + 2 ≤ exp (commonW n) ^ 2 := by
    nlinarith only [hx2, hx0]
  have hsq : exp (commonW n) ^ 2 = exp (2 * commonW n) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold concreteMass concreteMassCount
  push_cast
  linarith

/-- The concrete finite mode data: one retained phase, one short mode, one
frequency in each grid, with coefficients `e^{-2W} · massCount`.  The weights
are the explicit unnormalized phase weights `1`. -/
noncomputable def concreteMode : FiniteModeData where
  Ω := Unit
  S := Unit
  A := Unit
  B := Unit
  instS := inferInstance
  instA := inferInstance
  instB := inferInstance
  phases := fun _ => {()}
  weight := fun _ _ => 1
  weight_nonneg := by
    intro n o ho
    norm_num
  inj₁ := Function.Embedding.refl Unit
  inj₂ := Function.Embedding.refl Unit
  f := fun n _ _ => exp (-(2 * commonW n)) * concreteMass n
  g := fun n _ _ => exp (-(2 * commonW n)) * concreteMass n

/-- The concrete retained-mode denominator: one term `e^{-W}` with
`ξ = 1/100`, `ζ = 0`, `cDen = 0`.  These are the exponents of the concrete
assembly witness. -/
noncomputable def concreteDen : FiniteDenominatorData concreteMode where
  term := fun n _ => exp (-(commonW n))
  xi := 1 / 100
  xi_pos := by norm_num
  xi_le_narrow := by norm_num
  zeta := 0
  zeta_nonneg := by norm_num
  variation_gap := by norm_num
  cDen := 0

/-- **The concrete finite Poisson data.**  It uses the common scale `commonW`
of the concrete assembly, the marks `2, 3`, the narrow width
`σ = e^{101W/100}`, the ideal mass `ν = 1/2`, the single-phase one-mode finite
arrays, the retained-mode denominator `e^{-W}`, and the explicit marginal
counts `⌈e^W⌉ + 1`. -/
noncomputable def concreteData : FinitePoissonData where
  W := commonW
  W_nonneg := commonW_nonneg
  W_dominates := commonW_dominates
  mark₁ := fun _ => 2
  mark₂ := fun _ => 3
  mark₁_prime := by
    intro n
    exact Nat.prime_two
  mark₂_prime := by
    intro n
    exact Nat.prime_three
  mark_distinct := by
    intro n
    norm_num
  mark_le := by
    intro n
    have hlog : Real.log 3 ≤ commonW n := by
      have h13 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith
      have hW2 : (2 : ℝ) ≤ commonW n := by
        have := commonW_three_le n
        linarith
      linarith
    have h3 : (3 : ℝ) ≤ Real.exp (commonW n) :=
      (Real.log_le_iff_le_exp (x := 3) (y := commonW n) (by norm_num)).mp hlog
    norm_num
    exact h3
  sigma := fun n => exp (commonW n) ^ (101 / 100 : ℝ)
  sigma_pos := by
    intro n
    exact Real.rpow_pos_of_pos (exp_pos _) _
  sigma_narrow := by
    intro n
    rfl
  nu := fun _ => 1 / 2
  nu_nonneg := by
    intro n
    norm_num
  nu_le_one := by
    intro n
    norm_num
  mode := concreteMode
  den := concreteDen
  massCount₁ := concreteMassCount
  massCount₂ := concreteMassCount
  massCount₁_pos := concreteMassCount_pos
  massCount₂_pos := concreteMassCount_pos
  c₁ := 0
  c₂ := 0
  η₁ := 1
  η₂ := 1
  η₁_pos := by norm_num
  η₂_pos := by norm_num

/-! ## 3. The explicit finite sums -/

/-- The first finite Parseval sum of the concrete data:
`marginal₁ n = e^{-4W n} · massCount n ^ 2`. -/
theorem concreteMode_marginal₁ (n : ℕ) :
    concreteMode.marginal₁ n = exp (-(4 * commonW n)) * concreteMass n ^ 2 := by
  letI := concreteMode.instA
  unfold FiniteModeData.marginal₁
  change (∑ o ∈ ({()} : Finset Unit), (1 : ℝ) * ∑ a : Unit,
      (exp (-(2 * commonW n)) * concreteMass n) ^ 2) =
    exp (-(4 * commonW n)) * concreteMass n ^ 2
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [mul_pow]
  rw [show exp (-(2 * commonW n)) ^ 2 = exp (-(4 * commonW n)) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]

/-- The second finite Parseval sum is the same explicit expression. -/
theorem concreteMode_marginal₂ (n : ℕ) :
    concreteMode.marginal₂ n = exp (-(4 * commonW n)) * concreteMass n ^ 2 := by
  letI := concreteMode.instB
  unfold FiniteModeData.marginal₂
  change (∑ o ∈ ({()} : Finset Unit), (1 : ℝ) * ∑ b : Unit,
      (exp (-(2 * commonW n)) * concreteMass n) ^ 2) =
    exp (-(4 * commonW n)) * concreteMass n ^ 2
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [mul_pow]
  rw [show exp (-(2 * commonW n)) ^ 2 = exp (-(4 * commonW n)) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]

/-- The signed finite coupled sum is `e^{-4W n} · massCount n ^ 2`. -/
theorem concreteMode_coupledSum (n : ℕ) :
    concreteMode.coupledSum n = exp (-(4 * commonW n)) * concreteMass n ^ 2 := by
  letI := concreteMode.instS
  unfold FiniteModeData.coupledSum
  change (∑ o ∈ ({()} : Finset Unit), (1 : ℝ) * ∑ s : Unit,
      (exp (-(2 * commonW n)) * concreteMass n) *
        (exp (-(2 * commonW n)) * concreteMass n)) =
    exp (-(4 * commonW n)) * concreteMass n ^ 2
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [show (exp (-(2 * commonW n)) * concreteMass n) *
        (exp (-(2 * commonW n)) * concreteMass n) =
      (exp (-(2 * commonW n)) * concreteMass n) ^ 2 by ring]
  rw [mul_pow]
  rw [show exp (-(2 * commonW n)) ^ 2 = exp (-(4 * commonW n)) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]

/-- **Finite Cauchy–Schwarz for the concrete arrays.**  The signed coupled sum is
bounded by the product of the two finite Parseval envelopes; this is the generic
`FiniteModeData.abs_coupledSum_le` applied to the concrete one-phase data. -/
theorem concreteMode_abs_coupledSum_le (n : ℕ) :
    |concreteMode.coupledSum n| ≤
      Real.sqrt (concreteMode.marginal₁ n) *
        Real.sqrt (concreteMode.marginal₂ n) :=
  concreteMode.abs_coupledSum_le n

/-- The retained-mode denominator sum is `e^{-W n}`. -/
theorem concreteDen_sum (n : ℕ) : concreteDen.sum n = exp (-(commonW n)) := by
  simp only [FiniteDenominatorData.sum, concreteMode, concreteDen,
    Finset.sum_singleton, one_mul]

/-- The square root of a normalized concrete marginal sum is `e^{-2W} · mass`. -/
theorem concrete_sqrt_marginal (n : ℕ) :
    Real.sqrt (exp (-(4 * commonW n)) * concreteMass n ^ 2) =
      exp (-(2 * commonW n)) * concreteMass n := by
  have hm0 : 0 ≤ concreteMass n := (concreteMass_pos n).le
  have hfac : exp (-(4 * commonW n)) * concreteMass n ^ 2 =
      (exp (-(2 * commonW n)) * concreteMass n) ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hfac, Real.sqrt_sq (mul_nonneg (exp_pos _).le hm0)]

/-! ## 4. The five residual `Prop`s for the concrete data -/

/-- **`EnvelopeGrowth₁` for the concrete data.**  The finite first Parseval
envelope is `e^{-2W} · massCount ≤ 1` because `massCount ≤ e^{2W}`, and the
right-hand side with `c₁ = 0` is `1`. -/
theorem concrete_envelopeGrowth₁ : concreteData.EnvelopeGrowth₁ := by
  intro n
  have hm : concreteMass n ≤ exp (2 * commonW n) := concreteMass_le_exp_two n
  calc
    Real.sqrt (concreteData.mode.marginal₁ n) =
        Real.sqrt (exp (-(4 * commonW n)) * concreteMass n ^ 2) := by
      rw [show concreteData.mode = concreteMode from rfl, concreteMode_marginal₁ n]
    _ = exp (-(2 * commonW n)) * concreteMass n := concrete_sqrt_marginal n
    _ ≤ exp (-(2 * commonW n)) * exp (2 * commonW n) :=
      mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ = exp ((0 : ℝ) * scale n) := by
      rw [← Real.exp_add]
      rw [show -(2 * commonW n) + 2 * commonW n = 0 by ring]
      rw [show (0 : ℝ) * scale n = 0 by ring]
    _ = exp (concreteData.c₁ * scale n) := by
      rw [show concreteData.c₁ = 0 from rfl]

/-- **`EnvelopeGrowth₂` for the concrete data.** -/
theorem concrete_envelopeGrowth₂ : concreteData.EnvelopeGrowth₂ := by
  intro n
  have hm : concreteMass n ≤ exp (2 * commonW n) := concreteMass_le_exp_two n
  calc
    Real.sqrt (concreteData.mode.marginal₂ n) =
        Real.sqrt (exp (-(4 * commonW n)) * concreteMass n ^ 2) := by
      rw [show concreteData.mode = concreteMode from rfl, concreteMode_marginal₂ n]
    _ = exp (-(2 * commonW n)) * concreteMass n := concrete_sqrt_marginal n
    _ ≤ exp (-(2 * commonW n)) * exp (2 * commonW n) :=
      mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ = exp ((0 : ℝ) * scale n) := by
      rw [← Real.exp_add]
      rw [show -(2 * commonW n) + 2 * commonW n = 0 by ring]
      rw [show (0 : ℝ) * scale n = 0 by ring]
    _ = exp (concreteData.c₂ * scale n) := by
      rw [show concreteData.c₂ = 0 from rfl]

/-- **`MassLowerBound₁` for the concrete data.**  The explicit count
`⌈e^W⌉ + 1` dominates `e^W`. -/
theorem concrete_massLowerBound₁ : concreteData.MassLowerBound₁ := by
  apply massLowerBound₁_of_massCount_le
  intro n
  have h := exp_le_concreteMass n
  simpa only [concreteData, concreteMass, one_mul] using h

/-- **`MassLowerBound₂` for the concrete data.** -/
theorem concrete_massLowerBound₂ : concreteData.MassLowerBound₂ := by
  apply massLowerBound₂_of_massCount_le
  intro n
  have h := exp_le_concreteMass n
  simpa only [concreteData, concreteMass, one_mul] using h

/-- **`DenominatorGrowth` for the concrete data.**  With `ξ = 1/100`,
`ζ = 0`, `cDen = 0`, the single retained-mode term `e^{-W}` satisfies
`e^{-W} ≤ e^{-W/100}` because `W ≥ 0`. -/
theorem concrete_denominatorGrowth : concreteData.DenominatorGrowth := by
  intro n
  have hsum : concreteData.den.sum n = exp (-(commonW n)) := by
    rw [show concreteData.den = concreteDen from rfl]
    exact concreteDen_sum n
  rw [hsum, abs_of_nonneg (exp_pos _).le]
  rw [show concreteData.den.cDen = 0 from rfl,
    show concreteData.den.xi = 1 / 100 from rfl,
    show concreteData.den.zeta = 0 from rfl,
    show concreteData.W n = commonW n from rfl]
  rw [show (0 : ℝ) * scale n = 0 by ring, Real.exp_zero, one_mul]
  rw [show 2 * (0 : ℝ) * commonW n = 0 by ring, Real.exp_zero, mul_one]
  apply Real.exp_le_exp.mpr
  have hW : 0 ≤ commonW n := commonW_nonneg n
  nlinarith

/-! ## 5. The bundled analytic inputs and the assembled quotient -/

/-- The five concrete bounds, bundled as the `AnalyticInputs` of the finite
data.  No field is assumed: each is the theorem proved above. -/
theorem concreteAnalyticInputs : concreteData.AnalyticInputs where
  growth₁ := concrete_envelopeGrowth₁
  mass₁ := concrete_massLowerBound₁
  growth₂ := concrete_envelopeGrowth₂
  mass₂ := concrete_massLowerBound₂
  denominator := concrete_denominatorGrowth

/-- The assembled Poisson quotient from the concrete finite data. -/
noncomputable def concreteQuotient : PoissonQuotientInputs :=
  concreteAnalyticInputs.toPoissonQuotient

/-- The assembled quotient keeps the finite numerator error. -/
theorem concreteQuotient_E : concreteQuotient.E = concreteData.E := rfl

/-- The assembled quotient keeps the finite denominator error. -/
theorem concreteQuotient_A : concreteQuotient.A = concreteData.A := rfl

/-- The assembled quotient keeps the first finite marginal energy. -/
theorem concreteQuotient_E₁ : concreteQuotient.E₁ = concreteData.E₁ := rfl

/-- The assembled quotient keeps the second finite marginal energy. -/
theorem concreteQuotient_E₂ : concreteQuotient.E₂ = concreteData.E₂ := rfl

/-! ## 6. The finite data realize the concrete assembly witness -/

/-- The first normalized finite energy is exactly `e^{-2W}`, the first marginal
energy of `poissonWitness`. -/
theorem concreteData_E₁_eq (n : ℕ) :
    concreteData.E₁ n = exp (-(2 * commonW n)) := by
  unfold FinitePoissonData.E₁
  rw [show concreteData.mode = concreteMode from rfl, concreteMode_marginal₁ n]
  rw [show concreteData.mass₁ n = concreteMass n from rfl]
  rw [concrete_sqrt_marginal n]
  exact mul_div_cancel_right₀ _ (concreteMass_pos n).ne'

/-- The second normalized finite energy is exactly `e^{-2W}`. -/
theorem concreteData_E₂_eq (n : ℕ) :
    concreteData.E₂ n = exp (-(2 * commonW n)) := by
  unfold FinitePoissonData.E₂
  rw [show concreteData.mode = concreteMode from rfl, concreteMode_marginal₂ n]
  rw [show concreteData.mass₂ n = concreteMass n from rfl]
  rw [concrete_sqrt_marginal n]
  exact mul_div_cancel_right₀ _ (concreteMass_pos n).ne'

/-- The normalized finite numerator error is exactly `e^{-4W}`. -/
theorem concreteData_E_eq (n : ℕ) :
    concreteData.E n = exp (-(4 * commonW n)) := by
  unfold FinitePoissonData.E
  rw [show concreteData.mode = concreteMode from rfl, concreteMode_coupledSum n]
  rw [show concreteData.mass₁ n = concreteMass n from rfl,
    show concreteData.mass₂ n = concreteMass n from rfl]
  have hm : concreteMass n ≠ 0 := (concreteMass_pos n).ne'
  field_simp [hm]

/-- The finite retained-mode denominator error is exactly `e^{-W}`. -/
theorem concreteData_A_eq (n : ℕ) :
    concreteData.A n = exp (-(commonW n)) := by
  unfold FinitePoissonData.A
  rw [show concreteData.den = concreteDen from rfl]
  exact concreteDen_sum n

/-- The finite ideal mass is `1/2`, as in the assembly witness. -/
theorem concreteData_nu_eq (n : ℕ) : concreteData.nu n = poissonWitness.nu n := rfl

/-- The finite actual pair probability is exactly the assembly witness's
`(1/2 + e^{-4W}) / (1 + e^{-W})`. -/
theorem concreteData_actual_eq (n : ℕ) :
    concreteData.actual n = poissonWitness.actual n := by
  unfold FinitePoissonData.actual
  rw [concreteData_nu_eq n, concreteData_E_eq n, concreteData_A_eq n]
  rfl

/-- The concrete finite quotient has the same numerator error as the assembly
witness. -/
theorem concreteQuotient_E_eq_witness :
    concreteQuotient.E = poissonWitness.E := by
  funext n
  rw [concreteQuotient_E]
  exact concreteData_E_eq n

/-- The concrete finite quotient has the same denominator error as the assembly
witness. -/
theorem concreteQuotient_A_eq_witness :
    concreteQuotient.A = poissonWitness.A := by
  funext n
  rw [concreteQuotient_A]
  exact concreteData_A_eq n

/-- The concrete finite quotient has the same first marginal energy. -/
theorem concreteQuotient_E₁_eq_witness :
    concreteQuotient.E₁ = poissonWitness.E₁ := by
  funext n
  rw [concreteQuotient_E₁]
  exact concreteData_E₁_eq n

/-- The concrete finite quotient has the same second marginal energy. -/
theorem concreteQuotient_E₂_eq_witness :
    concreteQuotient.E₂ = poissonWitness.E₂ := by
  funext n
  rw [concreteQuotient_E₂]
  exact concreteData_E₂_eq n

/-- The concrete finite quotient has the same actual pair probability. -/
theorem concreteQuotient_actual_eq_witness :
    concreteQuotient.actual = poissonWitness.actual := by
  funext n
  rw [show concreteQuotient.actual n = concreteData.actual n from rfl]
  exact concreteData_actual_eq n

/-- The concrete finite quotient has the same ideal mass. -/
theorem concreteQuotient_nu_eq_witness :
    concreteQuotient.nu = poissonWitness.nu := by
  funext n
  rw [show concreteQuotient.nu n = concreteData.nu n from rfl]
  exact concreteData_nu_eq n

/-- **The L19.4 loss is literally the assembly witness's absolute Poisson
error.** -/
theorem concreteQuotient_loss_eq_witness :
    concreteQuotient.loss = poissonWitness.loss := by
  unfold PoissonQuotientInputs.loss
  funext n
  rw [concreteQuotient_actual_eq_witness, concreteQuotient_nu_eq_witness]

/-! ## 7. Positivity of the concrete quantities -/

theorem concreteData_mass₁_pos (n : ℕ) : 0 < concreteData.mass₁ n :=
  concreteData.mass₁_pos n

theorem concreteData_mass₂_pos (n : ℕ) : 0 < concreteData.mass₂ n :=
  concreteData.mass₂_pos n

theorem concreteData_E₁_pos (n : ℕ) : 0 < concreteData.E₁ n := by
  rw [concreteData_E₁_eq n]
  positivity

theorem concreteData_E₂_pos (n : ℕ) : 0 < concreteData.E₂ n := by
  rw [concreteData_E₂_eq n]
  positivity

theorem concreteData_E_pos (n : ℕ) : 0 < concreteData.E n := by
  rw [concreteData_E_eq n]
  positivity

theorem concreteData_A_pos (n : ℕ) : 0 < concreteData.A n := by
  rw [concreteData_A_eq n]
  positivity

/-- The concrete numerator obeys the finite Cauchy–Schwarz bound; this is the
generic `FiniteModeData.abs_coupledSum_le` specialized to the concrete arrays. -/
theorem concreteData_abs_E_le (n : ℕ) :
    |concreteData.E n| ≤ concreteData.E₁ n * concreteData.E₂ n :=
  concreteData.abs_E_le n

/-- **The concrete L19.4 loss is strictly positive.**  The numerator error
`e^{-4W}` is strictly smaller than `(1/2) e^{-W}` because `W ≥ 1`. -/
theorem concreteQuotient_loss_pos (n : ℕ) : 0 < concreteQuotient.loss n := by
  rw [concreteQuotient_loss_eq_witness]
  unfold PoissonQuotientInputs.loss
  have hW : 1 ≤ commonW n := commonW_one_le n
  have hhalf : Real.exp (-3 : ℝ) < 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.exp (Real.log (1 / 2)) from
      (Real.exp_log (by norm_num)).symm]
    apply Real.exp_lt_exp.mpr
    rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by
      rw [one_div, Real.log_inv]]
    nlinarith [Real.log_two_lt_d9]
  have hmono : Real.exp (-(3 * commonW n)) ≤ Real.exp (-3 : ℝ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hlt3 : Real.exp (-(3 * commonW n)) < 1 / 2 := lt_of_le_of_lt hmono hhalf
  have hmul := mul_lt_mul_of_pos_right hlt3 (Real.exp_pos (-(commonW n)))
  have hlt4 : Real.exp (-(4 * commonW n)) <
      (1 / 2) * Real.exp (-(commonW n)) := by
    rw [← Real.exp_add, show -(3 * commonW n) + -(commonW n) =
      -(4 * commonW n) by ring] at hmul
    linarith
  have hneg : poissonWitness.actual n - poissonWitness.nu n < 0 := by
    rw [poissonWitness_error_eq]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  rw [abs_of_neg hneg]
  linarith

/-! ## 8. L19.4 for the concrete finite data -/

/-- **The concrete L19.4 loss is `SubexpLoss`.**  This is the full reduction
from the five finite `Prop`s to the manuscript's L19.4 statement. -/
theorem concrete_subexpLoss : SubexpLoss concreteQuotient.loss :=
  concreteAnalyticInputs.subexpLoss

/-- **The `B = 2` C5 slot for the concrete finite data.** -/
theorem concrete_slot_le :
    ∀ᶠ n : ℕ in atTop, concreteQuotient.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  concreteAnalyticInputs.slot_le

/-- The concrete finite data as an L19.4 `SubexpLeaf`. -/
noncomputable def concreteSubexpLeaf : SubexpLeaf :=
  concreteAnalyticInputs.toSubexpLeaf

/-! ## Signature report -/

#check envelopeGrowth₁_iff_marginal_sum_le
#check envelopeGrowth₂_iff_marginal_sum_le
#check concrete_envelopeGrowth₁
#check concrete_massLowerBound₁
#check concrete_envelopeGrowth₂
#check concrete_massLowerBound₂
#check concrete_denominatorGrowth
#check concreteAnalyticInputs
#check concreteQuotient
#check concrete_subexpLoss
#check concrete_slot_le
#check concreteMode_abs_coupledSum_le
#check concreteData_E₁_eq
#check concreteData_E₂_eq
#check concreteData_E_eq
#check concreteData_A_eq
#check concreteQuotient_loss_eq_witness
#check concreteQuotient_loss_pos

/-! ## Axiom audit -/

#print axioms envelopeGrowth₁_iff_marginal_sum_le
#print axioms envelopeGrowth₂_iff_marginal_sum_le
#print axioms envelopeGrowth₁_of_marginal_sum_le
#print axioms envelopeGrowth₂_of_marginal_sum_le
#print axioms massLowerBound₁_of_massCount_le
#print axioms massLowerBound₂_of_massCount_le
#print axioms denominatorGrowth_of_abs_sum_le
#print axioms concreteMassCount_pos
#print axioms concreteMass_pos
#print axioms exp_le_concreteMass
#print axioms concreteMass_le_exp_two
#print axioms concreteMode_abs_coupledSum_le
#print axioms concreteMode_marginal₁
#print axioms concreteMode_marginal₂
#print axioms concreteMode_coupledSum
#print axioms concreteDen_sum
#print axioms concrete_sqrt_marginal
#print axioms concrete_envelopeGrowth₁
#print axioms concrete_envelopeGrowth₂
#print axioms concrete_massLowerBound₁
#print axioms concrete_massLowerBound₂
#print axioms concrete_denominatorGrowth
#print axioms concreteAnalyticInputs
#print axioms concreteQuotient
#print axioms concreteData_E₁_eq
#print axioms concreteData_E₂_eq
#print axioms concreteData_E_eq
#print axioms concreteData_A_eq
#print axioms concreteData_actual_eq
#print axioms concreteQuotient_loss_eq_witness
#print axioms concreteData_E₁_pos
#print axioms concreteData_E₂_pos
#print axioms concreteData_E_pos
#print axioms concreteData_A_pos
#print axioms concreteData_abs_E_le
#print axioms concreteQuotient_loss_pos
#print axioms concrete_subexpLoss
#print axioms concrete_slot_le
#print axioms concreteSubexpLeaf

end

end Cogentic.RandomizedL19EnergyBounds
