import Cogentic.RandomizedL19ZeroModeFinite
import Cogentic.RandomizedL19EnergyMassFinite

/-!
# L19.5: a concrete `ZeroModeCertificate` from finite spectral data

`Cogentic.RandomizedL19ZeroMode.ZeroModeCertificate` records the ideal zero mode
as

`zeroMode n = retained n + discarded n`,

where `retained` is the layer-cake second moment of a finite family of spectral
boxes and `discarded` is the genuinely positive residual mass.  The residual
coefficient `ρ` is assembled from an inner-ellipse discard and a period-prime
deletion.

This file builds a *literal* certificate.  All the finite-dimensional spectral
data are chosen explicitly:

* the mark scale is `W n = (n + 1) (|scale n| + 1)`, so `W = D^{O(1)}` and
  `W n ≥ 1` for every `n`;
* the spectrum is the diagonal operator on `Fin 2 → ℝ` with eigenvalues
  `1` and `1 / 10000`;
* the spectral coefficients of the zero-mode vector are `exp (-(i+1)^2 W n)`;
* the retained box is the lowest eigenmode `i = 0` with mass `exp (-W n)`;
* the discarded part is the exact spectral tail
  `(1 / 10000) exp (-8 W n)`, which is strictly positive;
* the inner-ellipse discard uses `T₁ = T₂ = 1`, zero centers and correlation,
  discard exponent `a = 2`, and lattice mesh `(1 / 100) exp (-3 W n)`;
* the period-prime residual is instantiated with period `1`; the general
  collapse lemma `periodPrimeResidual_residual_eq_zero` proves that on this
  ledger *every* period-prime residual vanishes, because `scale 2 < 0` forces
  `cN = 0`.  The genuine zero-mode error is therefore the ellipse discard,
  which is strictly positive.

The main results are:

* `concreteZeroModeCertificate : ZeroModeCertificate concreteW`, with every
  field proved;
* `concrete_rho_pos`, `concrete_retained_pos`, `concrete_tail_pos`,
  `concrete_zeroMode_pos`: the retained part, the discarded tail, the residual
  `ρ`, and the full zero mode are all strictly positive;
* `concreteRho_ge`: the quantitative lower bound
  `(1/20000) exp (-6 W n) ≤ ρ n`, so the residual is not merely nonnegative;
* `concreteEllipseMass_ge` and `concreteEllipseMass_le_seven`: two-sided
  explicit bounds for the actual lattice Gaussian ratio, proved from
  `mahalanobis_2d_lattice_mass_half` / `mahalanobis_2d_inner_ellipse_mass_le`;
* `retainedBoxSpectralBound` and `spectralTailBound`, the two named
  finite-spectral interface predicates (`RetainedBoxSpectralBound`,
  `SpectralTailBound`), both discharged unconditionally for the concrete data,
  and packaged together in `concrete_spectral_inputs`;
* `concrete_subexpLoss` and `concrete_slot_le`, the downstream L19.5 `SubexpLoss`
  and C5 `B = 2` slot.

No `sorry`, `admit`, `axiom`, or `native_decide` appears.  No mass, count,
coefficient, or error is set to zero by fiat: the discarded tail and the ellipse
discard ratio are strictly positive, and the period-prime collapse is a theorem,
not an assumption.
-/

namespace Cogentic.RandomizedL19ZeroModeConcrete

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Filter Real
open scoped BigOperators Classical
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19ZeroMode
open Cogentic.RandomizedL19ZeroModeFinite
open Cogentic.RandomizedEllipticAndGaussian
open Cogentic.RandomizedL19EnergyMassFinite

/-! ## 1. The concrete mark scale `W = log V` -/

/-- The concrete logarithmic mark scale `W n = (n + 1) (|scale n| + 1)`.
It is nonnegative, at least `1`, and dominates every fixed multiple of
`scale n`. -/
noncomputable def concreteW (n : ℕ) : ℝ := ((n : ℝ) + 1) * (|scale n| + 1)

theorem concreteW_nonneg (n : ℕ) : 0 ≤ concreteW n := by
  unfold concreteW
  positivity

theorem concreteW_zero : concreteW 0 = 1 := by
  norm_num [concreteW, scale_zero]

theorem concreteW_one : concreteW 1 = 2 := by
  norm_num [concreteW, scale_one]

theorem concreteW_one_le (n : ℕ) : 1 ≤ concreteW n := by
  unfold concreteW
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h2 : (1 : ℝ) ≤ |scale n| + 1 := by
    have := abs_nonneg (scale n)
    linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ ((n : ℝ) + 1) * (|scale n| + 1) := by
      exact mul_le_mul h1 h2 (by norm_num) (by positivity)

theorem concreteW_dominates : DominatesScale concreteW := by
  intro c hc
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (scale_grows.eventually_ge_atTop (0 : ℝ))
  refine Filter.eventually_atTop.mpr ⟨max N (Nat.ceil c), fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnc : c ≤ (n : ℝ) + 1 := by
    have hceil : (Nat.ceil c : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast ((le_max_right _ _).trans hn)
    have := Nat.le_ceil c
    linarith
  have hs : 0 ≤ scale n := hN n hnN
  unfold concreteW
  calc c * scale n ≤ ((n : ℝ) + 1) * scale n :=
        mul_le_mul_of_nonneg_right hnc hs
    _ ≤ ((n : ℝ) + 1) * (|scale n| + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [le_abs_self (scale n)]

/-! ## 2. The ledger scale at the small indices -/

/-- At the exceptional index `n = 2` the ledger scale is at least `-1`.
The real-power convention contributes `cos (2π/3) = -1/2`. -/
theorem scale_two_ge_neg_one : -1 ≤ scale 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_one_gt_two
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hloglog2_neg : Real.log (Real.log 2) < 0 :=
    Real.log_neg hlog2pos hlog2lt1
  have hloglog2_ge : -1 ≤ Real.log (Real.log 2) := by
    have hmono : Real.log (1 / 2) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (by norm_num) hlog2half
    have hhalf : Real.log (1 / 2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    have hneg : -1 ≤ -Real.log 2 := by linarith
    linarith
  unfold scale
  simp only [Nat.cast_ofNat]
  rw [Real.rpow_def_of_neg hloglog2_neg]
  have hcos : Real.cos ((2 / 3 : ℝ) * π) = -(1 / 2) := by
    have harg : (2 / 3 : ℝ) * π = π - π / 3 := by ring
    rw [harg, Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [hcos]
  have h1 : (Real.log 2) ^ (1 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one hlog2pos.le hlog2lt1.le (by norm_num)
  have h1nonneg : 0 ≤ (Real.log 2) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg hlog2pos.le _
  have harg_nonneg : 0 ≤ -Real.log (Real.log 2) := by linarith
  have harg_le1 : -Real.log (Real.log 2) ≤ 1 := by linarith
  have hlog_nonpos : Real.log (Real.log (Real.log 2)) ≤ 0 := by
    rw [← Real.log_neg_eq_log]
    exact Real.log_nonpos harg_nonneg harg_le1
  have hexp_le : Real.exp (Real.log (Real.log (Real.log 2)) * (2 / 3 : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hexp_nonneg : 0 ≤ Real.exp (Real.log (Real.log (Real.log 2)) * (2 / 3 : ℝ)) :=
    (Real.exp_pos _).le
  have hprod0 : 0 ≤ (Real.log 2) ^ (1 / 3 : ℝ) *
      Real.exp (Real.log (Real.log (Real.log 2)) * (2 / 3 : ℝ)) :=
    mul_nonneg h1nonneg hexp_nonneg
  have hprod1 : (Real.log 2) ^ (1 / 3 : ℝ) *
      Real.exp (Real.log (Real.log (Real.log 2)) * (2 / 3 : ℝ)) ≤ 1 := by
    calc (Real.log 2) ^ (1 / 3 : ℝ) *
          Real.exp (Real.log (Real.log (Real.log 2)) * (2 / 3 : ℝ))
        ≤ 1 * 1 := mul_le_mul h1 hexp_le hexp_nonneg (by norm_num)
      _ = 1 := by ring
  nlinarith [hprod0, hprod1]

theorem scale_ge_neg_one (n : ℕ) : -1 ≤ scale n := by
  by_cases hn3 : 3 ≤ n
  · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (le_of_lt (scale_pos_of_three_le hn3))
  · have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [scale_zero]; norm_num
    · rw [scale_one]; norm_num
    · exact scale_two_ge_neg_one

/-! ## 3. The concrete diagonal spectral model -/

/-- The two eigenvalues of the diagonal spectral model: `1` and `1/10000`. -/
noncomputable def eigenvalue (i : Fin 2) : ℝ := if i = 0 then 1 else 1 / 10000

theorem eigenvalue_nonneg (i : Fin 2) : 0 ≤ eigenvalue i := by
  fin_cases i <;> norm_num [eigenvalue]

theorem eigenvalue_zero : eigenvalue 0 = 1 := by simp [eigenvalue]

theorem eigenvalue_one : eigenvalue 1 = 1 / 10000 := by
  simp [eigenvalue]

/-- The spectral coefficients `exp (-(i+1)^2 W n)` of the zero-mode vector. -/
noncomputable def coefficient (n : ℕ) (i : Fin 2) : ℝ :=
  Real.exp (-(((i : ℕ) + 1 : ℝ) ^ 2) * concreteW n)

theorem coefficient_pos (n : ℕ) (i : Fin 2) : 0 < coefficient n i :=
  Real.exp_pos _

theorem coefficient_nonneg (n : ℕ) (i : Fin 2) : 0 ≤ coefficient n i :=
  (coefficient_pos n i).le

theorem coefficient_zero (n : ℕ) : coefficient n 0 = Real.exp (-concreteW n) := by
  simp [coefficient]

theorem coefficient_one (n : ℕ) :
    coefficient n 1 = Real.exp (-4 * concreteW n) := by
  simp [coefficient]
  norm_num

/-- The diagonal operator `x ↦ (λᵢ xᵢ)`, the concrete spectral model. -/
noncomputable def spectralOperator : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x i := eigenvalue i * x i
  map_add' x y := by
    funext i
    simp [mul_add]
  map_smul' c x := by
    funext i
    simp [mul_left_comm]

theorem spectralOperator_apply (x : Fin 2 → ℝ) (i : Fin 2) :
    spectralOperator x i = eigenvalue i * x i := rfl

/-- Coordinate vector of the spectral basis. -/
noncomputable def basisVec (i : Fin 2) : Fin 2 → ℝ := fun j => if j = i then 1 else 0

theorem basisVec_ne_zero (i : Fin 2) : basisVec i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [basisVec] at this

/-- **The coordinate vectors are genuine eigenvectors of the diagonal
operator**, with the stated eigenvalues. -/
theorem spectralOperator_hasEigenvector (i : Fin 2) :
    Module.End.HasEigenvector spectralOperator (eigenvalue i) (basisVec i) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · funext j
    by_cases h : j = i
    · subst h
      simp [spectralOperator, basisVec]
    · simp [spectralOperator, basisVec, h]
  · exact basisVec_ne_zero i

/-- The Rayleigh energy of a spectral vector is its eigenvalue-weighted `ℓ²`
mass. -/
theorem energy_eq_sum_mul_apply (x : Fin 2 → ℝ) :
    (∑ i, x i * spectralOperator x i) = ∑ i, eigenvalue i * x i ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spectralOperator_apply]
  ring

/-- The spectral energies of the concrete zero-mode vector. -/
noncomputable def spectralEnergy (n : ℕ) : ℝ :=
  ∑ i : Fin 2, eigenvalue i * coefficient n i ^ 2

theorem spectralEnergy_nonneg (n : ℕ) : 0 ≤ spectralEnergy n := by
  unfold spectralEnergy
  exact Finset.sum_nonneg fun i _ => mul_nonneg (eigenvalue_nonneg i) (sq_nonneg _)

/-! ## 4. The retained box and the discarded spectral tail -/

/-- The mass of a spectral box: `√λᵢ · cᵢ`. -/
noncomputable def boxMass (n : ℕ) (i : Fin 2) : ℝ :=
  Real.sqrt (eigenvalue i) * coefficient n i

theorem boxMass_nonneg (n : ℕ) (i : Fin 2) : 0 ≤ boxMass n i :=
  mul_nonneg (Real.sqrt_nonneg _) (coefficient_nonneg n i)

/-- The retained box is the lowest eigenmode `i = 0`. -/
noncomputable def retainedBox : Finset (Fin 2) := {0}

/-- The retained part of the zero mode: the layer-cake second moment of the
retained box mass. -/
noncomputable def retained (n : ℕ) : ℝ :=
  ∑ i ∈ retainedBox, boxMass n i ^ 2

theorem retainedBox_card : retainedBox.card = 1 := by
  simp [retainedBox]

theorem retained_eq_coefficient_sq (n : ℕ) :
    retained n = coefficient n 0 ^ 2 := by
  rw [retained, retainedBox, Finset.sum_singleton]
  rw [boxMass, eigenvalue_zero, Real.sqrt_one, one_mul]

theorem retained_nonneg (n : ℕ) : 0 ≤ retained n := by
  rw [retained_eq_coefficient_sq]
  positivity

theorem retained_pos (n : ℕ) : 0 < retained n := by
  rw [retained_eq_coefficient_sq]
  exact pow_pos (coefficient_pos n 0) 2

theorem retained_eq_exp (n : ℕ) :
    retained n = Real.exp (-2 * concreteW n) := by
  rw [retained_eq_coefficient_sq, coefficient_zero, pow_two, ← Real.exp_add]
  rw [Real.exp_eq_exp]
  ring

/-- The discarded spectral tail: the energy in the higher eigenmode `i = 1`. -/
noncomputable def spectralTail (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.erase (0 : Fin 2), eigenvalue i * coefficient n i ^ 2

theorem spectralTail_nonneg (n : ℕ) : 0 ≤ spectralTail n := by
  unfold spectralTail
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (eigenvalue_nonneg i) (sq_nonneg _)

theorem spectralTail_eq (n : ℕ) :
    spectralTail n = (1 / 10000) * Real.exp (-8 * concreteW n) := by
  have herase : (Finset.univ.erase (0 : Fin 2)) = {1} := by
    ext i
    fin_cases i <;> simp
  rw [spectralTail, herase, Finset.sum_singleton, eigenvalue_one, coefficient_one]
  rw [pow_two, ← Real.exp_add]
  congr 1
  rw [Real.exp_eq_exp]
  ring

theorem spectralTail_pos (n : ℕ) : 0 < spectralTail n := by
  rw [spectralTail_eq]
  positivity

/-- **The spectral splitting identity**: the full spectral energy is the
retained lowest mode plus the discarded tail. -/
theorem spectralEnergy_eq_retained_add_tail (n : ℕ) :
    spectralEnergy n = retained n + spectralTail n := by
  have h0 : (0 : Fin 2) ∈ Finset.univ := Finset.mem_univ _
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 2))
    (fun i => eigenvalue i * coefficient n i ^ 2) h0
  unfold spectralEnergy
  rw [← hsplit]
  rw [spectralTail]
  rw [eigenvalue_zero, retained_eq_coefficient_sq]
  ring

/-- The retained box bound: the only finite-spectral input is that the retained
box mass is at most `exp (cb · scale) · μ_q`.  For the concrete data this is
proved at `cb = 0`, `μ_q = 1`. -/
def RetainedBoxSpectralBound (W : ℕ → ℝ) (cb : ℝ) (muq : ℕ → ℝ) : Prop :=
  ∀ n, Real.sqrt (eigenvalue 0) * coefficient n 0 ≤ Real.exp (cb * scale n) * muq n

theorem retainedBoxSpectralBound :
    RetainedBoxSpectralBound concreteW 0 (fun _ => 1) := by
  intro n
  rw [eigenvalue_zero, Real.sqrt_one, one_mul, coefficient_zero]
  simp only [zero_mul, Real.exp_zero, one_mul]
  rw [Real.exp_le_one_iff]
  linarith [concreteW_nonneg n]

/-! ## 5. The period-prime collapse on the ledger -/

/-- **The period-prime residual collapses on the ledger scale.**

`PeriodPrimeResidual` requires `(period n : ℝ) ≤ exp (cN · scale n)` with
`cN ≥ 0`.  At `n = 2` the ledger scale is negative, so `exp (cN · scale 2) ≤ 1`.
Since the period is a nonzero natural, this forces `period 2 = 1`, then
`cN = 0`, then `period n = 1` for every `n`, and finally the prime-factor count
is zero.

Thus on this ledger the period-prime deletion contributes no mass; the genuine
residual comes from the discarded inner ellipse.  This is a theorem about the
existing interface, not a choice of zero. -/
theorem periodPrimeResidual_residual_eq_zero {W : ℕ → ℝ}
    (P : PeriodPrimeResidual W) (n : ℕ) : P.residual n = 0 := by
  have hpos : (1 : ℝ) ≤ (P.period 2 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (P.period_ne_zero 2)
  have hle : (P.period 2 : ℝ) ≤ Real.exp (P.cN * scale 2) := P.period_poly 2
  have hexp_le_one : Real.exp (P.cN * scale 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hs : scale 2 ≤ 0 := scale_two_neg.le
    nlinarith [P.cN_nonneg]
  have hexp_one : Real.exp (P.cN * scale 2) = 1 :=
    le_antisymm hexp_le_one (hpos.trans hle)
  have hcN : P.cN = 0 := by
    have hzero : P.cN * scale 2 = 0 := (Real.exp_eq_one_iff _).mp hexp_one
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_lt scale_two_neg)
  have hperiod : P.period n = 1 := by
    have h := P.period_poly n
    rw [hcN] at h
    have h1 : (P.period n : ℝ) ≤ 1 := by simpa using h
    have h2 : 1 ≤ P.period n := Nat.one_le_iff_ne_zero.mpr (P.period_ne_zero n)
    exact_mod_cast le_antisymm h1 (by exact_mod_cast h2)
  have hcard : (P.period n).primeFactors.card = 0 := by
    rw [hperiod]
    simp
  have hres := P.residual_le n
  rw [hcard, Nat.cast_zero, zero_mul] at hres
  exact le_antisymm hres (P.residual_nonneg n)

/-- The concrete period-prime certificate.  The period is `1`, `cN = 0`, and
the exceptional-prime mass is `exp (-W n)`.  The period-prime residual is
`0` by the collapse lemma, not by fiat. -/
noncomputable def concretePeriodPrime : PeriodPrimeResidual concreteW where
  period := fun _ => 1
  period_ne_zero := by intro n; norm_num
  cN := 0
  cN_nonneg := le_rfl
  period_poly := by
    intro n
    simp
  cP := 1
  cP_pos := by norm_num
  exceptionMass := fun n => Real.exp (-concreteW n)
  exceptionMass_nonneg := fun n => (Real.exp_pos _).le
  exceptionMass_le := by
    intro n
    simp
  residual := fun n => ((1 : ℕ).primeFactors.card : ℝ) * Real.exp (-concreteW n)
  residual_nonneg := by
    intro n
    positivity
  residual_le := by
    intro n
    exact le_rfl

theorem concretePeriodPrime_residual_eq_zero (n : ℕ) :
    concretePeriodPrime.residual n = 0 :=
  periodPrimeResidual_residual_eq_zero concretePeriodPrime n

/-! ## 6. The concrete inner-ellipse geometry -/

/-- The lattice mesh `δ_n = (1/100) exp (-3 W n)`.  It is positive, at most
`1/10`, and at most `V^{-2}` for `V = exp (W n)`. -/
noncomputable def geomMesh (n : ℕ) : ℝ := (1 / 100) * Real.exp (-3 * concreteW n)

theorem geomMesh_pos (n : ℕ) : 0 < geomMesh n := by
  unfold geomMesh
  positivity

theorem geomMesh_nonneg (n : ℕ) : 0 ≤ geomMesh n := (geomMesh_pos n).le

theorem geomMesh_le_tenth (n : ℕ) : geomMesh n ≤ 1 / 10 := by
  have hexp_le : Real.exp (-3 * concreteW n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [concreteW_nonneg n]
  have hexp_pos : 0 < Real.exp (-3 * concreteW n) := Real.exp_pos _
  unfold geomMesh
  nlinarith

/-- The Mahalanobis mesh of the concrete geometry is exactly `geomMesh`. -/
theorem mahalanobisMesh_concrete (n : ℕ) :
    mahalanobisMesh 1 1 0 (geomMesh n) (geomMesh n) = geomMesh n := by
  unfold mahalanobisMesh
  norm_num

/-- `(exp W)^{-2} = exp (-2 W)`. -/
theorem exp_rpow_neg_two (n : ℕ) :
    (Real.exp (concreteW n)) ^ (-2 : ℝ) = Real.exp (-2 * concreteW n) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  ring_nf

theorem geomMesh_le_rpow (n : ℕ) :
    geomMesh n ≤ (Real.exp (concreteW n)) ^ (-2 : ℝ) := by
  rw [exp_rpow_neg_two]
  -- (1/100) e^{-3W} ≤ e^{-2W}
  have hW : 0 ≤ concreteW n := concreteW_nonneg n
  have hfac : Real.exp (-3 * concreteW n) =
      Real.exp (-concreteW n) * Real.exp (-2 * concreteW n) := by
    rw [← Real.exp_add]
    ring_nf
  have hexp_le : Real.exp (-concreteW n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexp2_pos : 0 < Real.exp (-2 * concreteW n) := Real.exp_pos _
  rw [geomMesh, hfac]
  calc (1 / 100) * (Real.exp (-concreteW n) * Real.exp (-2 * concreteW n))
      ≤ (1 / 100) * (1 * Real.exp (-2 * concreteW n)) := by
        gcongr
    _ = (1 / 100) * Real.exp (-2 * concreteW n) := by ring
    _ ≤ 1 * Real.exp (-2 * concreteW n) := by
        gcongr
        norm_num
    _ = Real.exp (-2 * concreteW n) := by ring

/-- The concrete discarded inner-ellipse ratio. -/
noncomputable def concreteEllipseMass (n : ℕ) : ℝ :=
  ellipseDiscardRatio 1 1 0 0 0 (geomMesh n) (geomMesh n)
    (Real.exp (concreteW n)) 2 (0, 0)

/-! ## 7. The lattice Gaussian sums -/

/-- The concrete lattice points. -/
noncomputable def concreteLat (n : ℕ) (k : ℤ × ℤ) : ℝ × ℝ :=
  ((0 : ℝ) + (k.1 : ℝ) * geomMesh n, (0 : ℝ) + (k.2 : ℝ) * geomMesh n)

/-- The Mahalanobis radius of a concrete lattice point. -/
noncomputable def concreteRad (n : ℕ) (k : ℤ × ℤ) : ℝ :=
  euclidNorm2 (mahalanobisCoord 1 1 0 0 0 (concreteLat n k))

/-- The concrete Gaussian lattice weight. -/
noncomputable def concreteG (n : ℕ) (k : ℤ × ℤ) : ℝ :=
  gaussian2D 1 1 0 0 0 (concreteLat n k)

/-- The concrete inner-ellipse numerator. -/
noncomputable def concreteInner (n : ℕ) (k : ℤ × ℤ) : ℝ :=
  if concreteRad n k < (Real.exp (concreteW n)) ^ (-2 : ℝ) then concreteG n k else 0

theorem concreteEllipseMass_eq_ratio (n : ℕ) :
    concreteEllipseMass n =
      (∑' k : ℤ × ℤ, concreteInner n k) / (∑' k : ℤ × ℤ, concreteG n k) := by
  unfold concreteEllipseMass ellipseDiscardRatio concreteInner concreteRad concreteG concreteLat
  rfl

theorem concreteG_tsum_eq (n : ℕ) :
    (∑' k : ℤ × ℤ, concreteG n k) =
      ∑' k : ℤ × ℤ, gaussian2D 1 1 0 0 0 (concreteLat n k) := rfl

theorem concreteG_summable (n : ℕ) : Summable (concreteG n) := by
  have h := (mahalanobis_2d_lattice_mass_bounds 1 1 0 0 0 (geomMesh n) (geomMesh n) (0,0)
    (by norm_num) (by norm_num) (by simp) (geomMesh_pos n) (geomMesh_pos n)).1
  rw [show concreteG n = fun k : ℤ × ℤ => gaussian2D 1 1 0 0 0 (concreteLat n k) from rfl]
  simpa only [concreteLat] using h

theorem concreteG_nonneg (n : ℕ) (k : ℤ × ℤ) : 0 ≤ concreteG n k := by
  unfold concreteG gaussian2D
  positivity

theorem concreteG_tsum_ge (n : ℕ) :
    1 / (2 * geomMesh n * geomMesh n) ≤ ∑' k : ℤ × ℤ, concreteG n k := by
  have h := mahalanobis_2d_lattice_mass_half 1 1 0 0 0 (geomMesh n) (geomMesh n) (0,0)
    (by norm_num) (by norm_num) (by simp) (geomMesh_pos n) (geomMesh_pos n)
    (by rw [mahalanobisMesh_concrete]; exact geomMesh_le_tenth n)
  rw [concreteG_tsum_eq]
  norm_num at h
  have heq : 1 / (2 * geomMesh n * geomMesh n) =
      (geomMesh n)⁻¹ * ((geomMesh n)⁻¹ * (1 / 2)) := by
    have h0 : geomMesh n ≠ 0 := (geomMesh_pos n).ne'
    field_simp
  rw [heq]
  simpa only [concreteLat, zero_add] using h

theorem concreteG_tsum_le (n : ℕ) :
    (∑' k : ℤ × ℤ, concreteG n k) ≤ 2 / (geomMesh n * geomMesh n) := by
  have h := (mahalanobis_2d_lattice_mass_bounds 1 1 0 0 0 (geomMesh n) (geomMesh n) (0,0)
    (by norm_num) (by norm_num) (by simp) (geomMesh_pos n) (geomMesh_pos n)).2.2
  have hδ := geomMesh_le_tenth n
  have hδ0 := geomMesh_nonneg n
  have hpi : π ≤ 3.15 := Real.pi_lt_d2.le
  have hterm1 : π * geomMesh n ≤ 3.15 * (1 / 10) :=
    mul_le_mul hpi hδ hδ0 (by norm_num)
  have hsq : (geomMesh n) ^ 2 ≤ (1 / 10) ^ 2 :=
    pow_le_pow_left₀ hδ0 hδ 2
  have hterm2 : π * (geomMesh n) ^ 2 ≤ 3.15 * (1 / 10) ^ 2 :=
    mul_le_mul hpi hsq (sq_nonneg _) (by norm_num)
  have hbound : 1 + π * geomMesh n + π * (geomMesh n) ^ 2 ≤ 2 := by
    nlinarith
  have hZ : ((1 : ℝ) * 1 * Real.sqrt (1 - 0 ^ 2)) = 1 := by norm_num
  rw [hZ, mahalanobisMesh_concrete, div_one] at h
  have hdiv : geomMesh n * geomMesh n * (∑' k : ℤ × ℤ, concreteG n k) ≤ 2 := by
    rw [concreteG_tsum_eq]
    have hle := h.trans hbound
    simpa only [concreteLat] using hle
  have hpos : 0 < geomMesh n * geomMesh n := mul_pos (geomMesh_pos n) (geomMesh_pos n)
  rw [le_div_iff₀ hpos]
  calc (∑' k : ℤ × ℤ, concreteG n k) * (geomMesh n * geomMesh n)
      = geomMesh n * geomMesh n * (∑' k : ℤ × ℤ, concreteG n k) := by ring
    _ ≤ 2 := hdiv

/-! ## 8. Two-sided bounds for the actual ellipse ratio -/

theorem concreteInner_nonneg (n : ℕ) (k : ℤ × ℤ) : 0 ≤ concreteInner n k := by
  unfold concreteInner
  split_ifs
  · exact concreteG_nonneg n k
  · exact le_rfl

theorem concreteInner_le_G (n : ℕ) (k : ℤ × ℤ) : concreteInner n k ≤ concreteG n k := by
  unfold concreteInner
  split_ifs
  · exact le_rfl
  · exact concreteG_nonneg n k

theorem concreteInner_summable (n : ℕ) : Summable (concreteInner n) :=
  Summable.of_nonneg_of_le (concreteInner_nonneg n) (concreteInner_le_G n)
    (concreteG_summable n)

theorem concreteInner_zero (n : ℕ) : concreteInner n 0 = 1 := by
  have hrad : concreteRad n 0 = 0 := by
    unfold concreteRad concreteLat mahalanobisCoord euclidNorm2
    norm_num
  have hlt : concreteRad n 0 < (Real.exp (concreteW n)) ^ (-2 : ℝ) := by
    rw [hrad]
    exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  unfold concreteInner
  rw [if_pos hlt]
  unfold concreteG gaussian2D
  rw [show euclidNorm2 (mahalanobisCoord 1 1 0 0 0 (concreteLat n 0)) = 0 from hrad]
  norm_num

theorem concreteInner_tsum_ge_one (n : ℕ) :
    1 ≤ ∑' k : ℤ × ℤ, concreteInner n k := by
  have hsum := (concreteInner_summable n).sum_le_tsum
    ({0} : Finset (ℤ × ℤ)) (fun k _ => concreteInner_nonneg n k)
  have h0 : (∑ k ∈ ({0} : Finset (ℤ × ℤ)), concreteInner n k) = 1 := by
    rw [Finset.sum_singleton, concreteInner_zero]
  linarith

/-- **Lower bound for the actual discarded ratio.**  The origin contributes
`1` to the numerator, and the full lattice mass is at most `2 / δ²`; hence the
ratio is at least `δ² / 2`. -/
theorem concreteEllipseMass_ge (n : ℕ) :
    geomMesh n ^ 2 / 2 ≤ concreteEllipseMass n := by
  rw [concreteEllipseMass_eq_ratio]
  have hnum := concreteInner_tsum_ge_one n
  have hden_upper := concreteG_tsum_le n
  have hden_pos : 0 < ∑' k : ℤ × ℤ, concreteG n k := by
    have hlower := concreteG_tsum_ge n
    have hpos : 0 < 1 / (2 * geomMesh n * geomMesh n) :=
      div_pos zero_lt_one
        (mul_pos (mul_pos (by norm_num) (geomMesh_pos n)) (geomMesh_pos n))
    exact lt_of_lt_of_le hpos hlower
  have hone : 1 / (2 / (geomMesh n * geomMesh n)) ≤
      1 / (∑' k : ℤ × ℤ, concreteG n k) :=
    one_div_le_one_div_of_le hden_pos hden_upper
  have hratio : 1 / (∑' k : ℤ × ℤ, concreteG n k) ≤
      (∑' k : ℤ × ℤ, concreteInner n k) / (∑' k : ℤ × ℤ, concreteG n k) :=
    div_le_div_of_nonneg_right hnum hden_pos.le
  have h0 : geomMesh n ≠ 0 := (geomMesh_pos n).ne'
  calc geomMesh n ^ 2 / 2 = 1 / (2 / (geomMesh n * geomMesh n)) := by
        field_simp
    _ ≤ 1 / (∑' k : ℤ × ℤ, concreteG n k) := hone
    _ ≤ (∑' k : ℤ × ℤ, concreteInner n k) / (∑' k : ℤ × ℤ, concreteG n k) := hratio

theorem concreteEllipseMass_pos (n : ℕ) : 0 < concreteEllipseMass n := by
  have h := concreteEllipseMass_ge n
  have hpos : 0 < geomMesh n ^ 2 / 2 :=
    div_pos (pow_pos (geomMesh_pos n) 2) (by norm_num)
  exact lt_of_lt_of_le hpos h

theorem concreteEllipseMass_nonneg (n : ℕ) : 0 ≤ concreteEllipseMass n :=
  (concreteEllipseMass_pos n).le

/-- **Upper bound for the actual discarded ratio**, in the sharp
`2π (V^{-2} + δ)²` form. -/
theorem concreteEllipseMass_le_inner (n : ℕ) :
    concreteEllipseMass n ≤
      2 * π * ((Real.exp (concreteW n)) ^ (-2 : ℝ) + geomMesh n) ^ 2 := by
  rw [concreteEllipseMass_eq_ratio]
  have hr0 : 0 ≤ (Real.exp (concreteW n)) ^ (-2 : ℝ) :=
    Real.rpow_nonneg (Real.exp_pos _).le _
  have h := mahalanobis_2d_inner_ellipse_mass_le 1 1 0 0 0 (geomMesh n) (geomMesh n) (0,0)
    (by norm_num) (by norm_num) (by simp) (geomMesh_pos n) (geomMesh_pos n)
    (by rw [mahalanobisMesh_concrete]; exact geomMesh_le_tenth n)
    ((Real.exp (concreteW n)) ^ (-2 : ℝ)) hr0
  simpa only [concreteInner, concreteRad, concreteG, concreteLat, mahalanobisMesh_concrete,
    zero_add] using h

/-- **Sharp explicit upper bound** `7 exp (-4 W n)` for the actual discarded
ratio. -/
theorem concreteEllipseMass_le_seven (n : ℕ) :
    concreteEllipseMass n ≤ 7 * Real.exp (-4 * concreteW n) := by
  refine (concreteEllipseMass_le_inner n).trans ?_
  rw [exp_rpow_neg_two]
  have hW : 0 ≤ concreteW n := concreteW_nonneg n
  have hexp_le : Real.exp (-3 * concreteW n) ≤ Real.exp (-2 * concreteW n) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hmul : (1 / 100) * Real.exp (-3 * concreteW n) ≤
      (1 / 100) * Real.exp (-2 * concreteW n) :=
    mul_le_mul_of_nonneg_left hexp_le (by norm_num)
  have hplus : Real.exp (-2 * concreteW n) + geomMesh n ≤
      (101 / 100) * Real.exp (-2 * concreteW n) := by
    unfold geomMesh
    nlinarith [Real.exp_pos (-2 * concreteW n)]
  have hplus_nonneg : 0 ≤ Real.exp (-2 * concreteW n) + geomMesh n :=
    add_nonneg (Real.exp_pos _).le (geomMesh_nonneg n)
  have hsq : (Real.exp (-2 * concreteW n) + geomMesh n) ^ 2 ≤
      ((101 / 100) * Real.exp (-2 * concreteW n)) ^ 2 :=
    pow_le_pow_left₀ hplus_nonneg hplus 2
  have hcoef : 2 * π * ((101 / 100) ^ 2) ≤ 7 := by
    have hpi : π ≤ 3.15 := Real.pi_lt_d2.le
    nlinarith
  have hexp_sq : ((101 / 100) * Real.exp (-2 * concreteW n)) ^ 2 =
      (101 / 100) ^ 2 * Real.exp (-4 * concreteW n) := by
    rw [mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    rw [Real.exp_eq_exp]
    ring
  calc 2 * π * (Real.exp (-2 * concreteW n) + geomMesh n) ^ 2
      ≤ 2 * π * ((101 / 100) * Real.exp (-2 * concreteW n)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (2 * π * (101 / 100) ^ 2) * Real.exp (-4 * concreteW n) := by
        rw [hexp_sq]; ring
    _ ≤ 7 * Real.exp (-4 * concreteW n) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

/-! ## 9. The residual certificate -/

/-- The concrete inner-ellipse certificate: unit marginal scales, zero centers
and correlation, discard exponent `a = 2`, and lattice mesh `geomMesh`. -/
noncomputable def concreteEllipse : EllipseDiscardData concreteW where
  T₁ := fun _ => 1
  T₂ := fun _ => 1
  c₁ := fun _ => 0
  c₂ := fun _ => 0
  ρ := fun _ => 0
  h₁ := geomMesh
  h₂ := geomMesh
  x₀ := fun _ => (0, 0)
  a := 2
  a_pos := by norm_num
  hT₁ := by intro n; norm_num
  hT₂ := by intro n; norm_num
  hρ := by intro n; simp
  hh₁ := geomMesh_pos
  hh₂ := geomMesh_pos
  hδ10 := by
    intro n
    rw [mahalanobisMesh_concrete]
    exact geomMesh_le_tenth n
  hδr := by
    intro n
    rw [mahalanobisMesh_concrete]
    exact geomMesh_le_rpow n
  discardedMass := concreteEllipseMass
  discardedMass_eq := by intro n; rfl

theorem concreteEllipse_discardedMass_eq (n : ℕ) :
    concreteEllipse.discardedMass n = concreteEllipseMass n := rfl

theorem concreteEllipse_discardedMass_le_eight_pi (n : ℕ) :
    concreteEllipse.discardedMass n ≤ 8 * π * Real.exp (-4 * concreteW n) := by
  change concreteEllipseMass n ≤ 8 * π * Real.exp (-4 * concreteW n)
  have h := concreteEllipse.discardedMass_le n
  rw [concreteEllipse_discardedMass_eq] at h
  rw [show concreteEllipse.a = (2 : ℝ) from rfl] at h
  norm_num at h
  have hExp : Real.exp (-(4 * concreteW n)) = Real.exp (-4 * concreteW n) := by
    rw [Real.exp_eq_exp]
    ring
  rw [hExp] at h
  exact h

/-- The residual `ρ` of the concrete certificate: the ellipse discard plus the
(provably vanishing) period-prime residual. -/
noncomputable def concreteRho (n : ℕ) : ℝ :=
  concreteEllipse.discardedMass n + concretePeriodPrime.residual n

theorem concreteRho_eq_ellipseMass (n : ℕ) :
    concreteRho n = concreteEllipseMass n := by
  rw [concreteRho, concreteEllipse_discardedMass_eq, concretePeriodPrime_residual_eq_zero,
    add_zero]

theorem concreteRho_nonneg (n : ℕ) : 0 ≤ concreteRho n := by
  rw [concreteRho, concreteEllipse_discardedMass_eq]
  exact add_nonneg (concreteEllipseMass_nonneg n) (concretePeriodPrime.residual_nonneg n)

theorem concreteRho_pos (n : ℕ) : 0 < concreteRho n := by
  rw [concreteRho_eq_ellipseMass]
  exact concreteEllipseMass_pos n

theorem concreteRho_le_seven (n : ℕ) :
    concreteRho n ≤ 7 * Real.exp (-4 * concreteW n) := by
  rw [concreteRho_eq_ellipseMass]
  exact concreteEllipseMass_le_seven n

/-- The elementary exponential comparison `C e^{-4W} ≤ e^{-W/4}`. -/
theorem const_mul_exp_neg_four_le {C W : ℝ}
    (hC : C ≤ Real.exp ((15 / 4) * W)) :
    C * Real.exp (-4 * W) ≤ Real.exp (-(1 / 4) * W) := by
  calc C * Real.exp (-4 * W)
      ≤ Real.exp ((15 / 4) * W) * Real.exp (-4 * W) :=
        mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ = Real.exp ((15 / 4) * W + -4 * W) := by rw [← Real.exp_add]
    _ = Real.exp (-(1 / 4) * W) := by
        rw [Real.exp_eq_exp]
        ring

theorem seven_le_exp_fifteen_quarter {W : ℝ} (hW : 1 ≤ W) :
    (7 : ℝ) ≤ Real.exp ((15 / 4) * W) := by
  have h3 : (3 : ℝ) ≤ (15 / 4) * W := by nlinarith
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have he : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have hcube : Real.exp 3 = Real.exp 1 ^ 3 := by
      simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 3
    rw [hcube]
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
  exact (by norm_num : (7 : ℝ) ≤ 8).trans (h8.trans (Real.exp_le_exp.mpr h3))

theorem seven_mul_exp_neg_four_le {W : ℝ} (hW : 1 ≤ W) :
    (7 : ℝ) * Real.exp (-4 * W) ≤ Real.exp (-(1 / 4) * W) :=
  const_mul_exp_neg_four_le (seven_le_exp_fifteen_quarter hW)

theorem twenty_one_le_exp_fifteen_quarter {W : ℝ} (hW : 3 ≤ W) :
    (21 : ℝ) ≤ Real.exp ((15 / 4) * W) := by
  have h11 : (11 : ℝ) ≤ (15 / 4) * W := by nlinarith
  have h21 : (21 : ℝ) ≤ Real.exp 11 := by
    have he : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have hpow : Real.exp 11 = Real.exp 1 ^ 11 := by
      simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 11
    rw [hpow]
    calc (21 : ℝ) ≤ 2 ^ 11 := by norm_num
      _ ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) he.le 11
  exact h21.trans (Real.exp_le_exp.mpr h11)

theorem twenty_one_mul_exp_neg_four_le {W : ℝ} (hW : 3 ≤ W) :
    (21 : ℝ) * Real.exp (-4 * W) ≤ Real.exp (-(1 / 4) * W) :=
  const_mul_exp_neg_four_le (twenty_one_le_exp_fifteen_quarter hW)

/-- **The residual bound with the concrete exponents**
`c₀ = 1/100`, `η = 1/4`.  It holds for every ledger index. -/
theorem concreteRho_le_exp (n : ℕ) :
    concreteRho n ≤
      Real.exp (2 * (1 / 100) * scale n) * Real.exp (-(1 / 4) * concreteW n) := by
  have hsharp := concreteRho_le_seven n
  by_cases hn3 : 3 ≤ n
  · have hscale : 0 ≤ scale n := (scale_pos_of_three_le hn3).le
    have hone : 1 ≤ Real.exp (2 * (1 / 100) * scale n) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    calc concreteRho n ≤ 7 * Real.exp (-4 * concreteW n) := hsharp
      _ ≤ Real.exp (-(1 / 4) * concreteW n) :=
          seven_mul_exp_neg_four_le (concreteW_one_le n)
      _ ≤ Real.exp (2 * (1 / 100) * scale n) *
            Real.exp (-(1 / 4) * concreteW n) :=
          le_mul_of_one_le_left (Real.exp_pos _).le hone
  · have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn with rfl | rfl | rfl
    · have h := seven_mul_exp_neg_four_le (W := concreteW 0)
        (by rw [concreteW_zero])
      simpa [concreteW, scale_zero] using hsharp.trans h
    · have h := seven_mul_exp_neg_four_le (W := concreteW 1)
        (by rw [concreteW_one]; exact one_le_two)
      simpa [concreteW, scale_one] using hsharp.trans h
    · have hW3 : (3 : ℝ) ≤ concreteW 2 := by
        unfold concreteW
        norm_num
      have h21 := twenty_one_mul_exp_neg_four_le hW3
      have htail : (7 : ℝ) * Real.exp (-4 * concreteW 2) ≤
          (1 / 3) * Real.exp (-(1 / 4) * concreteW 2) := by
        nlinarith
      have he1 : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
        have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
        calc (1 / 3 : ℝ) ≤ 1 / Real.exp 1 :=
              one_div_le_one_div_of_le (Real.exp_pos 1) he3.le
          _ = (Real.exp 1)⁻¹ := by rw [one_div]
          _ = Real.exp (-1) := by rw [Real.exp_neg]
      have harg : (-1 : ℝ) ≤ 2 * (1 / 100) * scale 2 := by
        have := scale_two_ge_neg_one
        nlinarith
      have hone : (1 / 3 : ℝ) ≤ Real.exp (2 * (1 / 100) * scale 2) :=
        he1.trans (Real.exp_le_exp.mpr harg)
      calc concreteRho 2 ≤ 7 * Real.exp (-4 * concreteW 2) := hsharp
        _ ≤ (1 / 3) * Real.exp (-(1 / 4) * concreteW 2) := htail
        _ ≤ Real.exp (2 * (1 / 100) * scale 2) *
              Real.exp (-(1 / 4) * concreteW 2) :=
            mul_le_mul_of_nonneg_right hone (Real.exp_pos _).le

/-- The concrete residual certificate. -/
noncomputable def concreteResidual : ZeroModeResidualCertificate concreteW where
  W_nonneg := concreteW_nonneg
  ellipse := concreteEllipse
  period := concretePeriodPrime
  rho := concreteRho
  rho_nonneg := concreteRho_nonneg
  c0 := 1 / 100
  c0_pos := by norm_num
  eta := 1 / 4
  eta_pos := by norm_num
  eta_le_ellipse := by
    norm_num [concreteEllipse]
  eta_le_period := by
    norm_num [concretePeriodPrime]
  period_exp_le := by
    norm_num [concretePeriodPrime]
  rho_eq := by
    intro n
    rfl
  S := Real.log (16 * π) / (1 / 100)
  S_nonneg := by
    apply div_nonneg
    · apply Real.log_nonneg
      nlinarith [Real.pi_gt_three]
    · norm_num
  S_ge_const := le_rfl
  rho_initial := by
    intro n _
    exact concreteRho_le_exp n

/-! ## 10. The covering data and the full certificate -/

/-- The concrete covering data: one retained spectral box, the lowest
eigenmode, with `cb = cc = 0` and `μ_q = 1`. -/
noncomputable def concreteCovering : ZeroModeCoveringData concreteW where
  ι := Fin 2
  fintype := inferInstance
  decidableEq := inferInstance
  boxes := retainedBox
  boxMass := boxMass
  boxMass_nonneg := fun n i _ => boxMass_nonneg n i
  retained := retained
  retained_nonneg := retained_nonneg
  retained_eq := by intro n; rfl
  cb := 0
  cc := 0
  muq := fun _ => 1
  muq_nonneg := by intro n; norm_num
  muq_pos := by intro n; norm_num
  boxMass_le := by
    intro n i hi
    have hi0 : i = 0 := by simpa [retainedBox] using hi
    subst hi0
    exact retainedBoxSpectralBound n
  coverCount := fun _ => 1
  coverCount_nonneg := by intro n; norm_num
  coverCount_ge := by
    intro n
    rw [retainedBox_card]
    norm_num
  coverCount_le := by
    intro n
    simp

/-- The only discarded-spectral input of the certificate, as an explicit
predicate: the spectral tail is at most `ρ μ²`. -/
def SpectralTailBound (W : ℕ → ℝ) (tail rho mu : ℕ → ℝ) : Prop :=
  ∀ n, tail n ≤ rho n * mu n ^ 2

theorem geomMesh_sq (n : ℕ) :
    geomMesh n ^ 2 = (1 / 10000) * Real.exp (-6 * concreteW n) := by
  have hfac : (Real.exp (-3 * concreteW n)) ^ 2 =
      Real.exp (-6 * concreteW n) := by
    rw [pow_two, ← Real.exp_add]
    rw [Real.exp_eq_exp]
    ring
  unfold geomMesh
  rw [mul_pow, hfac]
  norm_num

/-- **The concrete discarded-spectral bound.**  The tail is
`10⁻⁶ exp (-8 W n)`, while the lower bound for `ρ` is
`δ²/2 = 5 · 10⁻⁵ exp (-6 W n)`; hence the tail is far below `ρ μ²`. -/
theorem spectralTail_le_rho_mu_sq (n : ℕ) :
    spectralTail n ≤ concreteRho n * (2 : ℝ) ^ 2 := by
  rw [concreteRho_eq_ellipseMass]
  have htail := spectralTail_eq n
  have hW : 0 ≤ concreteW n := concreteW_nonneg n
  have he : Real.exp (-8 * concreteW n) ≤ Real.exp (-6 * concreteW n) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hlow := concreteEllipseMass_ge n
  have h4 : (2 / 10000) * Real.exp (-6 * concreteW n) ≤
      concreteEllipseMass n * 4 := by
    have h := mul_le_mul_of_nonneg_right hlow (by norm_num : (0 : ℝ) ≤ 4)
    rw [geomMesh_sq] at h
    have h2 : ((1 / 10000) * Real.exp (-6 * concreteW n) / 2) * 4 =
        (2 / 10000) * Real.exp (-6 * concreteW n) := by ring
    rw [h2] at h
    exact h
  calc spectralTail n = (1 / 10000) * Real.exp (-8 * concreteW n) := htail
    _ ≤ (1 / 10000) * Real.exp (-6 * concreteW n) :=
        mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ (2 / 10000) * Real.exp (-6 * concreteW n) := by
        have hc : (1 / 10000 : ℝ) ≤ 2 / 10000 := by norm_num
        exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ ≤ concreteEllipseMass n * 4 := h4
    _ = concreteEllipseMass n * (2 : ℝ) ^ 2 := by norm_num

theorem spectralTailBound :
    SpectralTailBound concreteW spectralTail concreteRho (fun _ => 2) :=
  spectralTail_le_rho_mu_sq

/-- **The concrete L19.5 certificate.**  Every field is proved from the
finite spectral data, the explicit Mahalanobis lattice geometry, and the
period-prime collapse. -/
noncomputable def concreteZeroModeCertificate : ZeroModeCertificate concreteW where
  W_nonneg := concreteW_nonneg
  W_dominates := concreteW_dominates
  mu := fun _ => 2
  mu_pos := by intro n; norm_num
  covering := concreteCovering
  cq := 0
  muq_le := by
    intro n
    simp [concreteCovering]
  retained := retained
  retained_nonneg := retained_nonneg
  retained_eq := by intro n; rfl
  discarded := spectralTail
  discarded_nonneg := spectralTail_nonneg
  zeroMode := spectralEnergy
  zeroMode_nonneg := spectralEnergy_nonneg
  zeroMode_eq := spectralEnergy_eq_retained_add_tail
  residual := concreteResidual
  discarded_le := by
    intro n
    exact spectralTail_le_rho_mu_sq n

/-! ## 11. Positive errors and downstream consequences -/

theorem concrete_retained_pos (n : ℕ) : 0 < concreteZeroModeCertificate.retained n :=
  retained_pos n

theorem concrete_tail_pos (n : ℕ) : 0 < concreteZeroModeCertificate.discarded n :=
  spectralTail_pos n

theorem concrete_rho_pos (n : ℕ) : 0 < concreteZeroModeCertificate.residual.rho n :=
  concreteRho_pos n

theorem concrete_zeroMode_pos (n : ℕ) : 0 < concreteZeroModeCertificate.zeroMode n := by
  rw [concreteZeroModeCertificate.zeroMode_eq n]
  exact add_pos (retained_pos n) (spectralTail_pos n)

/-- **Quantitative lower bound for the genuine residual**: the actual ellipse
ratio is at least `(1/20000) exp (-6 W n)`, so it is bounded away from zero for
every ledger index. -/
theorem concreteRho_ge (n : ℕ) :
    (1 / 20000) * Real.exp (-6 * concreteW n) ≤ concreteRho n := by
  rw [concreteRho_eq_ellipseMass]
  have h := concreteEllipseMass_ge n
  rw [geomMesh_sq] at h
  have h2 : (1 / 10000) * Real.exp (-6 * concreteW n) / 2 =
      (1 / 20000) * Real.exp (-6 * concreteW n) := by ring
  rwa [h2] at h

theorem concrete_zero_mode_bound (n : ℕ) :
    concreteZeroModeCertificate.zeroMode n ≤
      Real.exp ((2 * concreteCovering.cb + concreteCovering.cc) * scale n) *
          concreteCovering.muq n ^ 2 +
        concreteZeroModeCertificate.residual.rho n * concreteZeroModeCertificate.mu n ^ 2 :=
  concreteZeroModeCertificate.zero_mode_bound n

theorem concrete_rho_bound (n : ℕ) :
    concreteZeroModeCertificate.residual.rho n ≤
      Real.exp ((2 * concreteResidual.c0) * scale n) *
        Real.exp (-concreteResidual.eta * concreteW n) :=
  concreteZeroModeCertificate.rho_bound n

theorem concrete_subexpLoss :
    SubexpLoss concreteZeroModeCertificate.toIdealZeroModeInputs.loss :=
  concreteZeroModeCertificate.subexpLoss

theorem concrete_slot_le :
    ∀ᶠ n : ℕ in atTop,
      concreteZeroModeCertificate.toIdealZeroModeInputs.loss n ≤
        Real.exp (-(2 : ℝ) * scale n) :=
  concreteZeroModeCertificate.slot_le

/-- **The reduction to the two finite-spectral predicates.**  The retained box
bound and the discarded-tail bound are the only spectral inputs of the concrete
certificate; both are discharged. -/
theorem concrete_spectral_inputs :
    RetainedBoxSpectralBound concreteW 0 (fun _ => 1) ∧
      SpectralTailBound concreteW spectralTail concreteRho (fun _ => 2) :=
  ⟨retainedBoxSpectralBound, spectralTailBound⟩

/-! ## Axiom audit -/

#print axioms concreteW_dominates
#print axioms scale_two_ge_neg_one
#print axioms spectralOperator_hasEigenvector
#print axioms spectralEnergy_eq_retained_add_tail
#print axioms periodPrimeResidual_residual_eq_zero
#print axioms concreteEllipseMass_ge
#print axioms concreteEllipseMass_le_seven
#print axioms concreteRho_le_exp
#print axioms concreteRho_ge
#print axioms concreteRho_pos
#print axioms concreteInner_tsum_ge_one
#print axioms spectralTail_le_rho_mu_sq
#print axioms concreteZeroModeCertificate
#print axioms concrete_zeroMode_pos
#print axioms concrete_zero_mode_bound
#print axioms concrete_rho_bound
#print axioms concrete_spectral_inputs
#print axioms concrete_subexpLoss
#print axioms concrete_slot_le

end Cogentic.RandomizedL19ZeroModeConcrete
