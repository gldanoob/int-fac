import Cogentic.RandomizedPaperEndpointWave15
import Cogentic.RandomizedL19ZeroModeConcrete
import Cogentic.RandomizedL19ThinWiring

/-!
# L19 concrete assembly: an inhabitant of `Wave15L19Inputs`

`Cogentic.RandomizedPaperEndpointWave15.Wave15L19Inputs` collects the three L19
leaves at one common logarithmic mark scale `W = log V`:

* the L19.4 Poisson quotient `I` together with the two marginal energy
  certificates `M₁`, `M₂` (and their exponent/energy identifications), the
  coupled-numerator certificate `Dnum` and the denominator certificate `Dden`;
* the L19.5 zero-mode certificate `zeroMode : ZeroModeCertificate I.W`;
* the L18.4 determinant/volume data `thinData : ThinLatticeData` with the scale
  adapter `thinData.W = I.W`.

This file builds such an inhabitant explicitly, at the single common scale

  `commonW n = concreteW n + 2`,

where `concreteW n = (n+1)(|scale n| + 1)` is the scale of the concrete
zero-mode construction of `RandomizedL19ZeroModeConcrete`.

## The three components

* **L19.4 (Poisson/energy).**  `poissonWitness`, `poissonM₁`, `poissonM₂`,
  `poissonDnum` and `poissonDden` are a literal `PoissonQuotientInputs` at
  `commonW` together with its marginal, numerator and denominator certificates
  (one phase, one short mode and constant coefficient `e^{-2W}`).  Their
  Poisson errors are the genuine geometric sequences `E = e^{-4W}`,
  `A = e^{-W}` and the marginal energies are `E₁ = E₂ = e^{-2W}`; the loss is
  the actual `|actual - ν| > 0`, not a placeholder.
* **L19.5 (zero mode).**  `commonZeroModeCertificate` is a copy of the concrete
  finite-spectral construction of `RandomizedL19ZeroModeConcrete` presented at
  `commonW`: the Mahalanobis inner-ellipse geometry and the period-prime
  deletion are the same explicit data, with the lattice mesh
  `(1/100) e^{-3W}` and the actual discard ratio
  `ellipseDiscardRatio 1 1 0 0 0 h h (e^W) 2 (0,0)`.  The spectral trunk is a
  single unit-mass retained box (`μ = μ_q = 1`, `cb = cc = 0`); the discarded
  part is the actual residual mass `ρ μ²` with `μ = 1`.  `ρ` is strictly
  positive (`commonRho_pos`), so the L19.5 loss is strictly positive
  (`common_zeroMode_loss_pos`).
* **L19.6 (thin).**  `commonThinData` is a literal `ThinLatticeData` at
  `commonW`: the box is the one-column mark box
  `S n = {(1, j+1) : 0 ≤ j < K n}` with `q = 1`, denominator interval `[0, K n]`,
  `bmin = 1` and `L = K n + 1`, where
  `K n = ⌈e^{2W n}/(1+W n)⌉ + 1`.  Both `mark_count` and `power_margin` are
  proved from these choices.  The thin and small-determinant fractions are then
  the actual normalized lattice counts, and the L19.6 loss `thin + smallDet` is
  strictly positive by `Wave15L19Inputs.thin_loss_pos`.

## The scale obstruction (the exact equality needed)

The scale is *not* `concreteW`.  The concrete zero-mode certificate
`concreteZeroModeCertificate` lives at `concreteW`, and the one-column thin
construction can equally be presented there, but **no** `PoissonQuotientInputs`
can live at `concreteW`: its two prime marks must be distinct primes below
`exp (concreteW 0) = exp 1 < 3`, and the only such prime is `2`.  This is
`no_poissonQuotientInputs_at_concreteW` (and
`no_wave15L19Inputs_at_concreteW`).  Consequently the exact equality that would
be needed to feed the *given* certificate directly into the common-scale slot
is

  `commonW = concreteW`   (equivalently `concreteW n + 2 = concreteW n`),

which is false (`commonW_ne_concreteW`).  The file therefore proves the L19.5
certificate again at `commonW`, keeping every geometric ingredient of the
concrete construction; the equality that *does* hold, and is proved here, is
`commonZeroModeCertificate : ZeroModeCertificate commonW` together with
`commonThinData.W = commonW` and `poissonWitness.W = commonW`.

If one insisted on `W = concreteW`, the fields that remain (and are in fact
impossible) are exactly the Poisson-side ones: `I`, `M₁`, `M₂`, the exponent and
energy adapters `hc₁, hη₁, hE₁, hc₂, hη₂, hE₂`, `Dnum` and `Dden`.  The
zero-mode field is available at `concreteW` (`concreteZeroModeCertificate`),
and the thin one-column construction is scale-generic (it only needs
`W ≥ 1`), which is why only the Poisson side obstructs the common scale.

## What remains

Nothing of `Wave15L19Inputs` remains: `wave15L19Concrete` is a literal
inhabitant.  The only departure from "use the existing concrete zero-mode
certificate verbatim" is the scale: the same construction is re-presented at
`commonW` (the mesh, the ellipse geometry and the period-prime data are
identical, only `W` is shifted and the spectral trunk is the unit box).  See
the docstrings of `commonZeroModeCertificate` and
`no_poissonQuotientInputs_at_concreteW`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count,
mass or error is set to zero.
-/

namespace Cogentic.RandomizedL19ConcreteAssembly

noncomputable section

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19Poisson
open Cogentic.RandomizedL19ZeroMode
open Cogentic.RandomizedL19ZeroModeConcrete
open Cogentic.RandomizedEllipticAndGaussian
open Cogentic.RandomizedL19Thin
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL18_4ThinFinish
open Cogentic.RandomizedPaperEndpointWave15

/-! ## 1. The common scale -/

/-- The common logarithmic mark scale `W = concreteW + 2`; the shift makes the
two prime marks `2, 3` fit under `exp W` (`exp (commonW n) ≥ exp 3 > 3`). -/
abbrev commonW : ℕ → ℝ := fun n => concreteW n + 2

theorem commonW_nonneg (n : ℕ) : 0 ≤ commonW n := by
  have h := concreteW_nonneg n
  unfold commonW
  linarith

theorem commonW_one_le (n : ℕ) : 1 ≤ commonW n := by
  have h := concreteW_one_le n
  unfold commonW
  linarith

theorem commonW_three_le (n : ℕ) : 3 ≤ commonW n := by
  have h := concreteW_one_le n
  unfold commonW
  linarith

theorem commonW_dominates : DominatesScale commonW := by
  intro c hc
  filter_upwards [concreteW_dominates c hc] with n hn
  unfold commonW
  linarith

theorem commonW_eq_concreteW_add_two (n : ℕ) : commonW n = concreteW n + 2 := rfl

/-! ## 2. The L19.4 Poisson/energy witness at `commonW`

This is the explicit Poisson quotient of `RandomizedWave14Satisfiable` presented
directly at `commonW` (so that this file does not depend on that module).  The
errors are the genuine geometric sequences `E = e^{-4W}`, `A = e^{-W}` and the
marginal energies are `E₁ = E₂ = e^{-2W}`. -/

/-- The explicit Poisson quotient at `commonW`. -/
noncomputable def poissonWitness : PoissonQuotientInputs where
  W := commonW
  W_nonneg := commonW_nonneg
  W_dominates := commonW_dominates
  mark₁ := fun _ => 2
  mark₂ := fun _ => 3
  mark₁_prime := by intro n; exact Nat.prime_two
  mark₂_prime := by intro n; exact Nat.prime_three
  mark_distinct := by intro n; norm_num
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
  sigma := fun n => Real.exp (commonW n) ^ (101 / 100 : ℝ)
  sigma_pos := by
    intro n
    exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  sigma_narrow := by intro n; rfl
  nu := fun _ => 1 / 2
  actual := fun n => (1 / 2 + Real.exp (-(4 * commonW n))) /
    (1 + Real.exp (-(commonW n)))
  nu_nonneg := by intro n; norm_num
  nu_le_one := by intro n; norm_num
  E := fun n => Real.exp (-(4 * commonW n))
  A := fun n => Real.exp (-(commonW n))
  actual_eq := by intro n; rfl
  E₁ := fun n => Real.exp (-(2 * commonW n))
  E₂ := fun n => Real.exp (-(2 * commonW n))
  E₁_nonneg := by intro n; positivity
  E₂_nonneg := by intro n; positivity
  c₁ := 0
  c₂ := 0
  η₁ := 1
  η₂ := 1
  η₁_pos := by norm_num
  η₂_pos := by norm_num
  E₁_bound := by
    intro n
    rw [show Real.exp (0 * scale n) = 1 by simp]
    have hle : Real.exp (-(2 * commonW n)) ≤
        Real.exp (-(1 * commonW n)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [commonW_nonneg n]
    simpa [one_mul] using hle
  E₂_bound := by
    intro n
    rw [show Real.exp (0 * scale n) = 1 by simp]
    have hle : Real.exp (-(2 * commonW n)) ≤
        Real.exp (-(1 * commonW n)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [commonW_nonneg n]
    simpa [one_mul] using hle
  numerator_energy := by
    intro n
    rw [abs_of_nonneg (by positivity)]
    rw [show Real.exp (-(4 * commonW n)) =
        Real.exp (-(2 * commonW n)) * Real.exp (-(2 * commonW n)) by
      rw [← Real.exp_add]
      congr 1
      ring]
  cA := 0
  ηA := 1
  ηA_pos := by norm_num
  A_bound := by
    intro n
    rw [show Real.exp (0 * scale n) = 1 by simp]
    have hle : Real.exp (-(commonW n)) ≤
        Real.exp (-(1 * commonW n)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    simpa [one_mul] using hle

/-- The first marginal energy certificate. -/
noncomputable def poissonM₁ : EnergyScaleInputs commonW where
  W_nonneg := commonW_nonneg
  W_dominates := commonW_dominates
  c := 0
  η := 1
  η_pos := by norm_num
  energy := fun n => Real.exp (-(2 * commonW n))
  envelope := fun n => Real.exp (-(commonW n))
  mass := fun n => Real.exp (commonW n)
  energy_nonneg := by intro n; positivity
  envelope_nonneg := by intro n; positivity
  mass_pos := by intro n; positivity
  energy_le_envelope := by
    intro n
    rw [show Real.exp (-(commonW n)) / Real.exp (commonW n) =
        Real.exp (-(2 * commonW n)) by
      rw [← Real.exp_sub]
      congr 1
      ring]
  envelope_poly := by
    intro n
    rw [show Real.exp (0 * scale n) = 1 by simp]
    exact Real.exp_le_one_iff.mpr (by linarith [commonW_nonneg n])
  mass_lower := by intro n; rw [one_mul]

/-- The second marginal energy certificate. -/
noncomputable def poissonM₂ : EnergyScaleInputs commonW := poissonM₁

/-- The finite coupled-mode data: one phase, one short mode, one frequency in
each grid, with constant coefficient `e^{-2W}`. -/
noncomputable def poissonDnum : CoupledNumeratorData poissonWitness where
  Ω := Unit
  S := Unit
  A := Unit
  B := Unit
  fintypeS := inferInstance
  fintypeA := inferInstance
  fintypeB := inferInstance
  phases := fun _ => {()}
  weight := fun _ _ => 1
  weight_nonneg := by intro n o ho; norm_num
  inj₁ := Function.Embedding.refl Unit
  inj₂ := Function.Embedding.refl Unit
  f := fun n _ _ => Real.exp (-(2 * commonW n))
  g := fun n _ _ => Real.exp (-(2 * commonW n))
  numerator_eq := by
    intro n
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [show poissonWitness.E n = Real.exp (-(4 * commonW n)) from rfl]
    rw [show Real.exp (-(2 * commonW n)) * Real.exp (-(2 * commonW n)) =
        Real.exp (-(4 * commonW n)) by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring
  marginal₁ := by
    intro n
    simp only [Finset.univ_unique, Finset.sum_singleton, pow_two]
    rw [show poissonWitness.E₁ n = Real.exp (-(2 * commonW n)) from rfl]
    simpa using le_rfl
  marginal₂ := by
    intro n
    simp only [Finset.univ_unique, Finset.sum_singleton, pow_two]
    rw [show poissonWitness.E₂ n = Real.exp (-(2 * commonW n)) from rfl]
    simpa using le_rfl

/-- The retained-mode denominator data. -/
noncomputable def poissonDden : PoissonDenominatorData poissonWitness where
  xi := 1 / 100
  xi_pos := by norm_num
  xi_le_narrow := by norm_num
  zeta := 0
  zeta_nonneg := by norm_num
  variation_gap := by norm_num
  cDen := 0
  denominator_raw := by
    intro n
    rw [show Real.exp (0 * scale n) = 1 by simp]
    rw [show 2 * (0 : ℝ) * poissonWitness.W n = 0 by ring, Real.exp_zero, mul_one]
    have hA : poissonWitness.A n = Real.exp (-(commonW n)) := rfl
    rw [hA, abs_of_nonneg (by positivity)]
    have hle : Real.exp (-(commonW n)) ≤
        Real.exp (-(1 / 100) * commonW n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [commonW_nonneg n]
    simpa [poissonWitness, one_mul] using hle

/-! ## 3. The L19.5 zero-mode certificate at `commonW` -/

/-- The lattice mesh `δ_n = (1/100) e^{-3 W n}` of the shifted concrete
geometry. -/
noncomputable def commonMesh (n : ℕ) : ℝ := (1 / 100) * Real.exp (-3 * commonW n)

theorem commonMesh_pos (n : ℕ) : 0 < commonMesh n := by
  unfold commonMesh
  positivity

theorem commonMesh_nonneg (n : ℕ) : 0 ≤ commonMesh n := (commonMesh_pos n).le

theorem commonMesh_le_tenth (n : ℕ) : commonMesh n ≤ 1 / 10 := by
  have hexp_le : Real.exp (-3 * commonW n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [commonW_nonneg n]
  have hexp_pos : 0 < Real.exp (-3 * commonW n) := Real.exp_pos _
  unfold commonMesh
  nlinarith

/-- The Mahalanobis mesh of the shifted geometry is exactly `commonMesh`. -/
theorem mahalanobisMesh_common (n : ℕ) :
    mahalanobisMesh 1 1 0 (commonMesh n) (commonMesh n) = commonMesh n := by
  unfold mahalanobisMesh
  norm_num

theorem exp_rpow_neg_two_common (n : ℕ) :
    (Real.exp (commonW n)) ^ (-2 : ℝ) = Real.exp (-2 * commonW n) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  ring

/-- The mesh is below the discarded radius `V^{-2}` for `V = e^W`. -/
theorem commonMesh_le_rpow (n : ℕ) :
    commonMesh n ≤ (Real.exp (commonW n)) ^ (-2 : ℝ) := by
  rw [exp_rpow_neg_two_common]
  have hW : 0 ≤ commonW n := commonW_nonneg n
  have hfac : Real.exp (-3 * commonW n) =
      Real.exp (-commonW n) * Real.exp (-2 * commonW n) := by
    rw [← Real.exp_add]
    ring_nf
  have hexp_le : Real.exp (-commonW n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexp2_pos : 0 < Real.exp (-2 * commonW n) := Real.exp_pos _
  unfold commonMesh
  rw [hfac]
  calc (1 / 100) * (Real.exp (-commonW n) * Real.exp (-2 * commonW n))
      ≤ (1 / 100) * (1 * Real.exp (-2 * commonW n)) := by
        gcongr
    _ = (1 / 100) * Real.exp (-2 * commonW n) := by ring
    _ ≤ 1 * Real.exp (-2 * commonW n) := by
        gcongr
        norm_num
    _ = Real.exp (-2 * commonW n) := by ring

/-- The lattice points of the shifted concrete geometry. -/
noncomputable def commonLat (n : ℕ) (k : ℤ × ℤ) : ℝ × ℝ :=
  ((0 : ℝ) + (k.1 : ℝ) * commonMesh n,
    (0 : ℝ) + (k.2 : ℝ) * commonMesh n)

/-- The Mahalanobis radius of a lattice point. -/
noncomputable def commonRad (n : ℕ) (k : ℤ × ℤ) : ℝ :=
  euclidNorm2 (mahalanobisCoord 1 1 0 0 0 (commonLat n k))

/-- The Gaussian lattice weight. -/
noncomputable def commonG (n : ℕ) (k : ℤ × ℤ) : ℝ :=
  gaussian2D 1 1 0 0 0 (commonLat n k)

/-- The inner-ellipse numerator: the Gaussian weight of the lattice points of
Mahalanobis radius `< V^{-2}`. -/
noncomputable def commonInner (n : ℕ) (k : ℤ × ℤ) : ℝ :=
  if commonRad n k < (Real.exp (commonW n)) ^ (-2 : ℝ) then commonG n k else 0

/-- The actual discarded inner-ellipse ratio at `commonW`. -/
noncomputable def commonEllipseMass (n : ℕ) : ℝ :=
  ellipseDiscardRatio 1 1 0 0 0 (commonMesh n) (commonMesh n)
    (Real.exp (commonW n)) 2 (0, 0)

theorem commonEllipseMass_eq_ratio (n : ℕ) :
    commonEllipseMass n =
      (∑' k : ℤ × ℤ, commonInner n k) / (∑' k : ℤ × ℤ, commonG n k) := by
  unfold commonEllipseMass ellipseDiscardRatio commonInner commonRad commonG commonLat
  rfl

theorem commonG_tsum_eq (n : ℕ) :
    (∑' k : ℤ × ℤ, commonG n k) =
      ∑' k : ℤ × ℤ, gaussian2D 1 1 0 0 0 (commonLat n k) := rfl

theorem commonG_summable (n : ℕ) : Summable (commonG n) := by
  have h := (mahalanobis_2d_lattice_mass_bounds 1 1 0 0 0 (commonMesh n) (commonMesh n)
    (0, 0) (by norm_num) (by norm_num) (by simp) (commonMesh_pos n) (commonMesh_pos n)).1
  rw [show commonG n = fun k : ℤ × ℤ => gaussian2D 1 1 0 0 0 (commonLat n k) from rfl]
  simpa only [commonLat] using h

theorem commonG_nonneg (n : ℕ) (k : ℤ × ℤ) : 0 ≤ commonG n k := by
  unfold commonG gaussian2D
  positivity

theorem commonG_tsum_ge (n : ℕ) :
    1 / (2 * commonMesh n * commonMesh n) ≤ ∑' k : ℤ × ℤ, commonG n k := by
  have h := mahalanobis_2d_lattice_mass_half 1 1 0 0 0 (commonMesh n) (commonMesh n)
    (0, 0) (by norm_num) (by norm_num) (by simp) (commonMesh_pos n) (commonMesh_pos n)
    (by rw [mahalanobisMesh_common]; exact commonMesh_le_tenth n)
  rw [commonG_tsum_eq]
  norm_num at h
  have heq : 1 / (2 * commonMesh n * commonMesh n) =
      (commonMesh n)⁻¹ * ((commonMesh n)⁻¹ * (1 / 2)) := by
    have h0 : commonMesh n ≠ 0 := (commonMesh_pos n).ne'
    field_simp
  rw [heq]
  simpa only [commonLat, zero_add] using h

theorem commonG_tsum_le (n : ℕ) :
    (∑' k : ℤ × ℤ, commonG n k) ≤ 2 / (commonMesh n * commonMesh n) := by
  have h := (mahalanobis_2d_lattice_mass_bounds 1 1 0 0 0 (commonMesh n) (commonMesh n)
    (0, 0) (by norm_num) (by norm_num) (by simp) (commonMesh_pos n) (commonMesh_pos n)).2.2
  have hδ := commonMesh_le_tenth n
  have hδ0 := commonMesh_nonneg n
  have hpi : π ≤ 3.15 := Real.pi_lt_d2.le
  have hterm1 : π * commonMesh n ≤ 3.15 * (1 / 10) :=
    mul_le_mul hpi hδ hδ0 (by norm_num)
  have hsq : (commonMesh n) ^ 2 ≤ (1 / 10) ^ 2 :=
    pow_le_pow_left₀ hδ0 hδ 2
  have hterm2 : π * (commonMesh n) ^ 2 ≤ 3.15 * (1 / 10) ^ 2 :=
    mul_le_mul hpi hsq (sq_nonneg _) (by norm_num)
  have hbound : 1 + π * commonMesh n + π * (commonMesh n) ^ 2 ≤ 2 := by
    nlinarith
  have hZ : ((1 : ℝ) * 1 * Real.sqrt (1 - 0 ^ 2)) = 1 := by norm_num
  rw [hZ, mahalanobisMesh_common, div_one] at h
  have hdiv : commonMesh n * commonMesh n * (∑' k : ℤ × ℤ, commonG n k) ≤ 2 := by
    rw [commonG_tsum_eq]
    have hle := h.trans hbound
    simpa only [commonLat] using hle
  have hpos : 0 < commonMesh n * commonMesh n :=
    mul_pos (commonMesh_pos n) (commonMesh_pos n)
  rw [le_div_iff₀ hpos]
  calc (∑' k : ℤ × ℤ, commonG n k) * (commonMesh n * commonMesh n)
      = commonMesh n * commonMesh n * (∑' k : ℤ × ℤ, commonG n k) := by ring
    _ ≤ 2 := hdiv

theorem commonInner_nonneg (n : ℕ) (k : ℤ × ℤ) : 0 ≤ commonInner n k := by
  unfold commonInner
  split_ifs
  · exact commonG_nonneg n k
  · exact le_rfl

theorem commonInner_le_G (n : ℕ) (k : ℤ × ℤ) : commonInner n k ≤ commonG n k := by
  unfold commonInner
  split_ifs
  · exact le_rfl
  · exact commonG_nonneg n k

theorem commonInner_summable (n : ℕ) : Summable (commonInner n) :=
  Summable.of_nonneg_of_le (commonInner_nonneg n) (commonInner_le_G n)
    (commonG_summable n)

theorem commonInner_zero (n : ℕ) : commonInner n 0 = 1 := by
  have hrad : commonRad n 0 = 0 := by
    unfold commonRad commonLat mahalanobisCoord euclidNorm2
    norm_num
  have hlt : commonRad n 0 < (Real.exp (commonW n)) ^ (-2 : ℝ) := by
    rw [hrad]
    exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  unfold commonInner
  rw [if_pos hlt]
  unfold commonG gaussian2D
  rw [show euclidNorm2 (mahalanobisCoord 1 1 0 0 0 (commonLat n 0)) = 0 from hrad]
  norm_num

theorem commonInner_tsum_ge_one (n : ℕ) :
    1 ≤ ∑' k : ℤ × ℤ, commonInner n k := by
  have hsum := (commonInner_summable n).sum_le_tsum
    ({0} : Finset (ℤ × ℤ)) (fun k _ => commonInner_nonneg n k)
  have h0 : (∑ k ∈ ({0} : Finset (ℤ × ℤ)), commonInner n k) = 1 := by
    rw [Finset.sum_singleton, commonInner_zero]
  linarith

/-- **Lower bound for the actual discarded ratio**: the origin contributes `1`
and the full lattice mass is at most `2/δ²`, hence the ratio is at least
`δ²/2`.  In particular it is strictly positive. -/
theorem commonEllipseMass_ge (n : ℕ) :
    commonMesh n ^ 2 / 2 ≤ commonEllipseMass n := by
  rw [commonEllipseMass_eq_ratio]
  have hnum := commonInner_tsum_ge_one n
  have hden_upper := commonG_tsum_le n
  have hden_pos : 0 < ∑' k : ℤ × ℤ, commonG n k := by
    have hlower := commonG_tsum_ge n
    have hpos : 0 < 1 / (2 * commonMesh n * commonMesh n) :=
      div_pos zero_lt_one
        (mul_pos (mul_pos (by norm_num) (commonMesh_pos n)) (commonMesh_pos n))
    exact lt_of_lt_of_le hpos hlower
  have hone : 1 / (2 / (commonMesh n * commonMesh n)) ≤
      1 / (∑' k : ℤ × ℤ, commonG n k) :=
    one_div_le_one_div_of_le hden_pos hden_upper
  have hratio : 1 / (∑' k : ℤ × ℤ, commonG n k) ≤
      (∑' k : ℤ × ℤ, commonInner n k) / (∑' k : ℤ × ℤ, commonG n k) :=
    div_le_div_of_nonneg_right hnum hden_pos.le
  have h0 : commonMesh n ≠ 0 := (commonMesh_pos n).ne'
  calc commonMesh n ^ 2 / 2 = 1 / (2 / (commonMesh n * commonMesh n)) := by
        field_simp
    _ ≤ 1 / (∑' k : ℤ × ℤ, commonG n k) := hone
    _ ≤ (∑' k : ℤ × ℤ, commonInner n k) / (∑' k : ℤ × ℤ, commonG n k) := hratio

theorem commonEllipseMass_pos (n : ℕ) : 0 < commonEllipseMass n := by
  have h := commonEllipseMass_ge n
  have hpos : 0 < commonMesh n ^ 2 / 2 :=
    div_pos (pow_pos (commonMesh_pos n) 2) (by norm_num)
  exact lt_of_lt_of_le hpos h

theorem commonEllipseMass_nonneg (n : ℕ) : 0 ≤ commonEllipseMass n :=
  (commonEllipseMass_pos n).le

/-- The inner-ellipse discard data of the shifted concrete geometry. -/
noncomputable def commonEllipse : EllipseDiscardData commonW where
  T₁ := fun _ => 1
  T₂ := fun _ => 1
  c₁ := fun _ => 0
  c₂ := fun _ => 0
  ρ := fun _ => 0
  h₁ := commonMesh
  h₂ := commonMesh
  x₀ := fun _ => (0, 0)
  a := 2
  a_pos := by norm_num
  hT₁ := by intro n; norm_num
  hT₂ := by intro n; norm_num
  hρ := by intro n; simp
  hh₁ := commonMesh_pos
  hh₂ := commonMesh_pos
  hδ10 := by
    intro n
    rw [mahalanobisMesh_common]
    exact commonMesh_le_tenth n
  hδr := by
    intro n
    rw [mahalanobisMesh_common]
    exact commonMesh_le_rpow n
  discardedMass := commonEllipseMass
  discardedMass_eq := by intro n; rfl

theorem commonEllipse_discardedMass_eq (n : ℕ) :
    commonEllipse.discardedMass n = commonEllipseMass n := rfl

/-- The actual discarded ratio is at most `8π e^{-4W}` (the generic
`EllipseDiscardData.discardedMass_le` at `a = 2`). -/
theorem commonEllipseMass_le_eight_pi (n : ℕ) :
    commonEllipseMass n ≤ 8 * π * Real.exp (-4 * commonW n) := by
  have h := commonEllipse.discardedMass_le n
  rw [commonEllipse_discardedMass_eq] at h
  rw [show commonEllipse.a = (2 : ℝ) from rfl] at h
  norm_num at h
  have hExp : Real.exp (-(4 * commonW n)) = Real.exp (-4 * commonW n) := by
    rw [Real.exp_eq_exp]
    ring
  rw [hExp] at h
  exact h

/-- The period-prime deletion of the shifted concrete geometry: period `1`,
`cN = 0`, `cP = 1`; the period-prime residual collapses to zero. -/
noncomputable def commonPeriodPrime : PeriodPrimeResidual commonW where
  period := fun _ => 1
  period_ne_zero := by intro n; norm_num
  cN := 0
  cN_nonneg := le_rfl
  period_poly := by intro n; simp
  cP := 1
  cP_pos := by norm_num
  exceptionMass := fun n => Real.exp (-commonW n)
  exceptionMass_nonneg := fun n => (Real.exp_pos _).le
  exceptionMass_le := by intro n; simp
  residual := fun n => ((1 : ℕ).primeFactors.card : ℝ) * Real.exp (-commonW n)
  residual_nonneg := by intro n; positivity
  residual_le := by intro n; exact le_rfl

theorem commonPeriodPrime_residual_eq_zero (n : ℕ) :
    commonPeriodPrime.residual n = 0 := by
  unfold commonPeriodPrime
  simp

/-- The actual residual `ρ` of the shifted concrete construction. -/
noncomputable def commonRho (n : ℕ) : ℝ :=
  commonEllipse.discardedMass n + commonPeriodPrime.residual n

theorem commonRho_eq_ellipseMass (n : ℕ) :
    commonRho n = commonEllipseMass n := by
  rw [commonRho, commonEllipse_discardedMass_eq, commonPeriodPrime_residual_eq_zero,
    add_zero]

theorem commonRho_nonneg (n : ℕ) : 0 ≤ commonRho n := by
  rw [commonRho, commonEllipse_discardedMass_eq]
  exact add_nonneg (commonEllipseMass_nonneg n) (commonPeriodPrime.residual_nonneg n)

theorem commonRho_pos (n : ℕ) : 0 < commonRho n := by
  rw [commonRho_eq_ellipseMass]
  exact commonEllipseMass_pos n

/-- **The residual bound at `commonW`**, with the concrete exponents
`c₀ = 1/100`, `η = 1/4`.  The constant `8π` is absorbed by the shift
`commonW = concreteW + 2`, which makes `exp ((15/4) W)` dominate `8π`. -/
theorem commonRho_le_exp (n : ℕ) :
    commonRho n ≤
      Real.exp (2 * (1 / 100) * scale n) * Real.exp (-(1 / 4) * commonW n) := by
  have hW3 : 3 ≤ commonW n := commonW_three_le n
  -- `32 ≤ exp 5`
  have hexp5 : (32 : ℝ) ≤ Real.exp 5 := by
    have h2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have hpow : Real.exp 5 = Real.exp 1 ^ 5 := by
      simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 5
    rw [hpow]
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h2.le 5
  have hpi : π ≤ 3.15 := Real.pi_lt_d2.le
  have h8 : 8 * π ≤ 32 := by nlinarith
  have harg : (5 : ℝ) ≤ (15 / 4) * commonW n - 1 / 50 := by nlinarith
  have hexp_le : 8 * π ≤ Real.exp ((15 / 4) * commonW n - 1 / 50) :=
    h8.trans (hexp5.trans (Real.exp_le_exp.mpr harg))
  have heq : Real.exp ((15 / 4) * commonW n - 1 / 50) =
      Real.exp ((15 / 4) * commonW n) * Real.exp (-(1 / 50)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [heq] at hexp_le
  have hmul := mul_le_mul_of_nonneg_right hexp_le
    (Real.exp_pos (-(15 / 4) * commonW n)).le
  have hcancel : Real.exp ((15 / 4) * commonW n) * Real.exp (-(1 / 50)) *
      Real.exp (-(15 / 4) * commonW n) = Real.exp (-(1 / 50)) := by
    have harg' : (15 / 4) * commonW n + (-(1 / 50)) + (-(15 / 4) * commonW n) =
        -(1 / 50) := by ring
    calc Real.exp ((15 / 4) * commonW n) * Real.exp (-(1 / 50)) *
          Real.exp (-(15 / 4) * commonW n)
        = Real.exp (((15 / 4) * commonW n + (-(1 / 50))) +
            (-(15 / 4) * commonW n)) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ = Real.exp (-(1 / 50)) := by rw [harg']
  rw [hcancel] at hmul
  have hfac : Real.exp (-4 * commonW n) =
      Real.exp (-(15 / 4) * commonW n) * Real.exp (-(1 / 4) * commonW n) := by
    rw [← Real.exp_add]
    ring_nf
  have hstep1 : 8 * π * Real.exp (-4 * commonW n) ≤
      Real.exp (-(1 / 50)) * Real.exp (-(1 / 4) * commonW n) := by
    rw [hfac]
    have hrearr : (8 * π) * (Real.exp (-(15 / 4) * commonW n) *
        Real.exp (-(1 / 4) * commonW n)) =
        (8 * π * Real.exp (-(15 / 4) * commonW n)) *
          Real.exp (-(1 / 4) * commonW n) := by ring
    rw [hrearr]
    exact mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
  refine (commonRho_eq_ellipseMass n ▸ commonEllipseMass_le_eight_pi n).trans ?_
  refine hstep1.trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  have hscale := scale_ge_neg_one n
  linarith

/-- The residual certificate at `commonW`. -/
noncomputable def commonResidual : ZeroModeResidualCertificate commonW where
  W_nonneg := commonW_nonneg
  ellipse := commonEllipse
  period := commonPeriodPrime
  rho := commonRho
  rho_nonneg := commonRho_nonneg
  c0 := 1 / 100
  c0_pos := by norm_num
  eta := 1 / 4
  eta_pos := by norm_num
  eta_le_ellipse := by
    norm_num [commonEllipse]
  eta_le_period := by
    norm_num [commonPeriodPrime]
  period_exp_le := by
    norm_num [commonPeriodPrime]
  rho_eq := by intro n; rfl
  S := Real.log (16 * π) / (1 / 100)
  S_nonneg := by
    apply div_nonneg
    · apply Real.log_nonneg
      nlinarith [Real.pi_gt_three]
    · norm_num
  S_ge_const := le_rfl
  rho_initial := by
    intro n _
    exact commonRho_le_exp n

/-- The covering data at `commonW`: one unit-mass retained box, `cb = cc = 0`,
`μ_q = 1`. -/
noncomputable def commonCovering : ZeroModeCoveringData commonW where
  ι := Unit
  fintype := inferInstance
  decidableEq := inferInstance
  boxes := Finset.univ
  boxMass := fun _ _ => 1
  boxMass_nonneg := by intro n i _; norm_num
  retained := fun _ => 1
  retained_nonneg := by intro n; norm_num
  retained_eq := by intro n; simp
  cb := 0
  cc := 0
  muq := fun _ => 1
  muq_nonneg := by intro n; norm_num
  muq_pos := by intro n; norm_num
  boxMass_le := by intro n i _; simp
  coverCount := fun _ => 1
  coverCount_nonneg := by intro n; norm_num
  coverCount_ge := by intro n; simp
  coverCount_le := by intro n; simp

/-- **The L19.5 zero-mode certificate at the common scale `commonW`.**  It is
the concrete finite-spectral construction re-presented at `commonW`: one unit
retained box, `μ = 1`, `μ_q = 1`, the actual Mahalanobis inner-ellipse discard
`ρ = ellipseDiscardRatio 1 1 0 0 0 h h (e^W) 2 (0,0)` and the collapsed
period-prime deletion.  Both the retained and the discarded parts are
strictly positive (the discarded part is the actual residual mass `ρ μ²`). -/
noncomputable def commonZeroModeCertificate : ZeroModeCertificate commonW where
  W_nonneg := commonW_nonneg
  W_dominates := commonW_dominates
  mu := fun _ => 1
  mu_pos := by intro n; norm_num
  covering := commonCovering
  cq := 0
  muq_le := by intro n; simp [commonCovering]
  retained := fun _ => 1
  retained_nonneg := by intro n; norm_num
  retained_eq := by intro n; rfl
  discarded := fun n => commonRho n
  discarded_nonneg := commonRho_nonneg
  zeroMode := fun n => 1 + commonRho n
  zeroMode_nonneg := by
    intro n
    have h := commonRho_nonneg n
    linarith
  zeroMode_eq := by intro n; rfl
  residual := commonResidual
  discarded_le := by
    intro n
    have hrho : commonResidual.rho = commonRho := rfl
    simpa [hrho] using (le_refl (commonRho n))

theorem common_retained_pos (n : ℕ) :
    0 < commonZeroModeCertificate.retained n := by
  norm_num [commonZeroModeCertificate]

theorem common_discarded_pos (n : ℕ) :
    0 < commonZeroModeCertificate.discarded n :=
  commonRho_pos n

theorem common_zeroMode_pos (n : ℕ) :
    0 < commonZeroModeCertificate.zeroMode n := by
  show 0 < 1 + commonRho n
  have h := commonRho_nonneg n
  linarith

/-- The L19.5 loss is exactly the actual residual `ρ`, hence strictly positive. -/
theorem common_zeroMode_loss_eq (n : ℕ) :
    commonZeroModeCertificate.toIdealZeroModeInputs.loss n = commonRho n := by
  have hcz : commonZeroModeCertificate.toIdealZeroModeInputs.cz = 0 := by
    change 2 * commonZeroModeCertificate.covering.cb +
      commonZeroModeCertificate.covering.cc = 0
    rw [show commonZeroModeCertificate.covering.cb = 0 from rfl,
      show commonZeroModeCertificate.covering.cc = 0 from rfl]
    norm_num
  have hcq : commonZeroModeCertificate.toIdealZeroModeInputs.cq = 0 := by
    change commonZeroModeCertificate.cq = 0
    rfl
  have hK : commonZeroModeCertificate.toIdealZeroModeInputs.K n = 1 := by
    rw [IdealZeroModeInputs.K, hcz, hcq]
    norm_num
  have hz : commonZeroModeCertificate.toIdealZeroModeInputs.zeroMode n = 1 + commonRho n := rfl
  have hm : commonZeroModeCertificate.toIdealZeroModeInputs.mu n = 1 := rfl
  have hval :
      commonZeroModeCertificate.toIdealZeroModeInputs.zeroMode n /
          commonZeroModeCertificate.toIdealZeroModeInputs.mu n ^ 2 -
        commonZeroModeCertificate.toIdealZeroModeInputs.K n = commonRho n := by
    rw [hz, hm, hK]
    ring
  unfold IdealZeroModeInputs.loss
  rw [hval, max_eq_right (commonRho_nonneg n)]

theorem common_zeroMode_loss_pos (n : ℕ) :
    0 < commonZeroModeCertificate.toIdealZeroModeInputs.loss n := by
  rw [common_zeroMode_loss_eq]
  exact commonRho_pos n

/-! ## 4. The L19.6 thin data at `commonW` -/

/-- The mark count `K n = ⌈e^{2W n}/(1+W n)⌉ + 1` making the rational/volume
lower count hold for the one-column box. -/
noncomputable def commonThinK (n : ℕ) : ℕ :=
  Nat.ceil (Real.exp (2 * commonW n) / (1 + commonW n)) + 1

theorem commonThinK_pos (n : ℕ) : 0 < commonThinK n := by
  unfold commonThinK
  exact Nat.succ_pos _

/-- The one-column mark set `S n = {(1, 1), …, (1, K n)}`. -/
noncomputable def commonThinS (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (commonThinK n)).image (fun j : ℕ => ((1 : ℤ), (j : ℤ) + 1))

theorem commonThinS_card (n : ℕ) : (commonThinS n).card = commonThinK n := by
  rw [commonThinS, Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro a b h
  have h2 : (a : ℤ) + 1 = (b : ℤ) + 1 := by
    simpa using (Prod.ext_iff.mp h).2
  have h3 : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast h3

theorem mem_commonThinS {n : ℕ} {P : ℤ × ℤ} :
    P ∈ commonThinS n ↔ ∃ j : ℕ, j < commonThinK n ∧ P = ((1 : ℤ), (j : ℤ) + 1) := by
  rw [commonThinS, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_range.mp hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_range.mpr hj, rfl⟩

/-- The one-column determinant box at `commonW`. -/
noncomputable def commonThinBox (n : ℕ) : LatticeBox where
  S := commonThinS n
  q := 1
  q_pos := by norm_num
  lo := 0
  hi := (commonThinK n : ℤ)
  lo_le_hi := by positivity
  bmin := 1
  bmin_pos := by norm_num
  L := (commonThinK n : ℝ) + 1
  level_bound := by
    have hz : (((commonThinK n : ℤ) - 0 : ℤ) : ℝ) = (commonThinK n : ℝ) := by
      push_cast
      ring
    rw [hz]
    norm_num
  prim := by
    intro P hP
    rw [mem_commonThinS] at hP
    obtain ⟨j, hj, rfl⟩ := hP
    exact isCoprime_one_left
  den_pos := by
    intro P hP
    rw [mem_commonThinS] at hP
    obtain ⟨j, hj, rfl⟩ := hP
    omega
  box := by
    intro P hP
    rw [mem_commonThinS] at hP
    obtain ⟨j, hj, rfl⟩ := hP
    constructor <;> omega
  bmin_le := by
    intro P hP
    rw [mem_commonThinS] at hP
    obtain ⟨j, hj, rfl⟩ := hP
    omega
  det_dvd := by
    intro P hP Q hQ
    exact one_dvd _

theorem commonThinBox_S (n : ℕ) : (commonThinBox n).S = commonThinS n := rfl

theorem commonThinBox_card (n : ℕ) :
    (commonThinBox n).S.card = commonThinK n := by
  rw [commonThinBox_S, commonThinS_card]

theorem commonThinBox_q (n : ℕ) : (commonThinBox n).q = 1 := rfl

/-- **The L19.6 determinant/volume data at the common scale `commonW`.**  The
box is the one-column mark box, `ρ = 1`, `q = 1`; `mark_count` and
`power_margin` are proved from `K n = ⌈e^{2W n}/(1+W n)⌉ + 1` and
`commonW n ≥ 3`. -/
noncomputable def commonThinData : ThinLatticeData where
  W := commonW
  box := commonThinBox
  dens := fun _ => 1
  W_nonneg := commonW_nonneg
  W_dominates := commonW_dominates
  dens_pos := by intro n; norm_num
  dens_le_one := by intro n; norm_num
  mark_count := by
    intro n
    have hcard : ((commonThinBox n).S.card : ℝ) = (commonThinK n : ℝ) := by
      rw [commonThinBox_card]
    rw [hcard]
    rw [commonThinBox_q]
    norm_num
    have hden : denomScale commonW n ^ 2 = Real.exp (2 * commonW n) := by
      unfold denomScale
      rw [pow_two, ← Real.exp_add]
      ring_nf
    rw [hden]
    have hceil := Nat.le_ceil (Real.exp (2 * commonW n) / (1 + commonW n))
    unfold commonThinK
    push_cast
    linarith
  power_margin := by
    intro n
    have hW : 3 ≤ commonW n := commonW_three_le n
    rw [commonThinBox_q]
    norm_num
    have hden : denomScale commonW n ^ 2 = Real.exp (2 * commonW n) := by
      unfold denomScale
      rw [pow_two, ← Real.exp_add]
      ring_nf
    have hcell : cellMesh commonW n = Real.exp (commonW n / 4) := rfl
    rw [hden, hcell]
    have hdiv : Real.exp (2 * commonW n) / Real.exp (commonW n / 4) =
        Real.exp ((7 / 4) * commonW n) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hdiv]
    have hone_le_exp : 1 + commonW n ≤ Real.exp (commonW n) := by
      have := Real.add_one_le_exp (commonW n)
      linarith
    have htwo_exp : 2 * Real.exp (commonW n) ≤
        Real.exp ((7 / 4) * commonW n) := by
      have hfac : Real.exp ((7 / 4) * commonW n) =
          Real.exp (commonW n) * Real.exp ((3 / 4) * commonW n) := by
        rw [← Real.exp_add]
        ring_nf
      rw [hfac]
      have hthree : (2 : ℝ) ≤ Real.exp ((3 / 4) * commonW n) := by
        have h2e : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
        have hmono : Real.exp 1 ≤ Real.exp ((3 / 4) * commonW n) :=
          Real.exp_le_exp.mpr (by nlinarith)
        linarith
      calc 2 * Real.exp (commonW n) = Real.exp (commonW n) * 2 := by ring
        _ ≤ Real.exp (commonW n) * Real.exp ((3 / 4) * commonW n) :=
            mul_le_mul_of_nonneg_left hthree (Real.exp_pos _).le
    have hfirst : 2 * (1 + commonW n) ≤ 2 * Real.exp (commonW n) := by
      linarith only [hone_le_exp]
    exact hfirst.trans htwo_exp

theorem commonThinData_W : commonThinData.W = commonW := rfl

theorem commonThinData_thin_pos (n : ℕ) : 0 < commonThinData.thin n :=
  commonThinData.thin_pos n

theorem commonThinData_smallDet_pos (n : ℕ) : 0 < commonThinData.smallDet n :=
  commonThinData.smallDet_pos n

/-! ## 5. The assembled `Wave15L19Inputs` -/

/-- **An explicit inhabitant of `Wave15L19Inputs`**, at the single common scale
`commonW = concreteW + 2`: the Poisson witness and its marginal/numerator/
denominator certificates of `RandomizedWave14Satisfiable`, the shifted concrete
zero-mode certificate, and the one-column thin data.  The scale adapter is
`rfl`. -/
noncomputable def wave15L19Concrete : Wave15L19Inputs where
  I := poissonWitness
  M₁ := poissonM₁
  M₂ := poissonM₂
  hc₁ := rfl
  hη₁ := rfl
  hE₁ := by intro n; rfl
  hc₂ := rfl
  hη₂ := rfl
  hE₂ := by intro n; rfl
  Dnum := poissonDnum
  Dden := poissonDden
  zeroMode := commonZeroModeCertificate
  thinData := commonThinData
  thin_W := rfl

/-- The assembled Poisson component is the explicit witness at `commonW`. -/
theorem wave15L19Concrete_I : wave15L19Concrete.I = poissonWitness := rfl

/-- The assembled Poisson scale is the common scale. -/
theorem wave15L19Concrete_poisson_W : wave15L19Concrete.I.W = commonW := rfl

/-- The assembled zero-mode component is the shifted concrete certificate. -/
theorem wave15L19Concrete_zeroMode :
    wave15L19Concrete.zeroMode = commonZeroModeCertificate := rfl

/-- The assembled thin component is the one-column data at `commonW`. -/
theorem wave15L19Concrete_thinData : wave15L19Concrete.thinData = commonThinData := rfl

/-- **The scale adapter**, literally: the thin data and the Poisson interface
carry the same `W = commonW`. -/
theorem wave15L19Concrete_thin_W : wave15L19Concrete.thinData.W = wave15L19Concrete.I.W :=
  wave15L19Concrete.thin_W

/-- All three components of the assembled certificate use the same `W`. -/
theorem wave15L19Concrete_common_scale :
    wave15L19Concrete.I.W = commonW ∧
      wave15L19Concrete.zeroMode.toIdealZeroModeInputs.W = commonW ∧
        wave15L19Concrete.thinData.toLatticeThinInputs.W = commonW :=
  ⟨rfl, rfl, rfl⟩

/-- The assembled L19.6 loss is the actual normalized thin plus small-determinant
count. -/
theorem wave15L19Concrete_thin_loss_eq (n : ℕ) :
    wave15L19Concrete.toL19FullCertificate.toL19Inputs.thin.loss n =
      commonThinData.thin n + commonThinData.smallDet n :=
  Wave15L19Inputs.thin_loss_eq wave15L19Concrete n

/-- The assembled L19.6 loss is strictly positive. -/
theorem wave15L19Concrete_thin_loss_pos (n : ℕ) :
    0 < wave15L19Concrete.toL19FullCertificate.toL19Inputs.thin.loss n :=
  Wave15L19Inputs.thin_loss_pos wave15L19Concrete n

/-- The assembled L19.5 loss is strictly positive. -/
theorem wave15L19Concrete_zeroMode_loss_pos (n : ℕ) :
    0 < wave15L19Concrete.toL19FullCertificate.toL19Inputs.zeroMode.loss n := by
  rw [show wave15L19Concrete.toL19FullCertificate.toL19Inputs.zeroMode =
      commonZeroModeCertificate.toIdealZeroModeInputs from rfl]
  exact common_zeroMode_loss_pos n

/-- The assembled Poisson loss is the genuine absolute Poisson error. -/
theorem wave15L19Concrete_poisson_loss_eq (n : ℕ) :
    wave15L19Concrete.toL19FullCertificate.toL19Inputs.poisson.loss n =
      |poissonWitness.actual n - poissonWitness.nu n| := rfl

/-- The actual Poisson error is exactly
`(e^{-4W} - (1/2) e^{-W}) / (1 + e^{-W})`. -/
theorem poissonWitness_error_eq (n : ℕ) :
    poissonWitness.actual n - poissonWitness.nu n =
      (Real.exp (-(4 * commonW n)) - (1 / 2) * Real.exp (-(commonW n))) /
        (1 + Real.exp (-(commonW n))) := by
  rw [show poissonWitness.actual n =
      (1 / 2 + Real.exp (-(4 * commonW n))) / (1 + Real.exp (-(commonW n))) from rfl,
    show poissonWitness.nu n = (1 / 2 : ℝ) from rfl]
  field_simp
  ring

/-- **The Poisson loss is strictly positive**: the numerator error `e^{-4W}` is
strictly smaller than `(1/2) e^{-W}` because `W ≥ 1`. -/
theorem wave15L19Concrete_poisson_loss_pos (n : ℕ) :
    0 < wave15L19Concrete.toL19FullCertificate.toL19Inputs.poisson.loss n := by
  rw [wave15L19Concrete_poisson_loss_eq]
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

/-! ## 6. The scale obstruction: the exact equality that cannot hold -/

/-- The shift is genuine: the common scale is not the concrete zero-mode
scale. -/
theorem commonW_ne_concreteW : commonW ≠ concreteW := by
  intro h
  have h0 := congrFun h 0
  rw [show commonW 0 = 3 by
    rw [commonW_eq_concreteW_add_two, concreteW_zero]
    norm_num, concreteW_zero] at h0
  norm_num at h0

/-- **The exact equality needed to use `concreteZeroModeCertificate` directly**
is `commonW = concreteW`; it is false. -/
theorem exact_scale_equality_needed :
    ¬ (∀ n, commonW n = concreteW n) := by
  intro h
  exact commonW_ne_concreteW (funext h)

/-- **No Poisson quotient can live at `concreteW`.**  At `n = 0` the two
distinct prime marks would both have to be primes below
`exp (concreteW 0) = exp 1 < 3`, and the only such prime is `2`. -/
theorem no_poissonQuotientInputs_at_concreteW (I : PoissonQuotientInputs)
    (hW : I.W = concreteW) : False := by
  have hle : (max (I.mark₁ 0) (I.mark₂ 0) : ℝ) ≤ Real.exp (concreteW 0) := by
    simpa [hW] using I.mark_le 0
  have hexp : Real.exp (concreteW 0) < 3 := by
    rw [concreteW_zero]
    exact Real.exp_one_lt_three
  have hm1 : (I.mark₁ 0 : ℝ) < 3 :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) hle) hexp
  have hm2 : (I.mark₂ 0 : ℝ) < 3 :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) hle) hexp
  have h1 : I.mark₁ 0 = 2 := by
    have hge := (I.mark₁_prime 0).two_le
    have hlt : I.mark₁ 0 < 3 := by exact_mod_cast hm1
    omega
  have h2 : I.mark₂ 0 = 2 := by
    have hge := (I.mark₂_prime 0).two_le
    have hlt : I.mark₂ 0 < 3 := by exact_mod_cast hm2
    omega
  exact I.mark_distinct 0 (h1.trans h2.symm)

/-- Consequently no `Wave15L19Inputs` can use `concreteW` as the common scale. -/
theorem no_wave15L19Inputs_at_concreteW (C : Wave15L19Inputs)
    (hW : C.I.W = concreteW) : False :=
  no_poissonQuotientInputs_at_concreteW C.I hW

/-- **The remaining-field report.**  Every field of `Wave15L19Inputs` is
supplied by the explicit assembly at `commonW`. -/
theorem wave15L19Concrete_fields :
    Nonempty (EnergyScaleInputs wave15L19Concrete.I.W) ∧
      Nonempty (EnergyScaleInputs wave15L19Concrete.I.W) ∧
      Nonempty (CoupledNumeratorData wave15L19Concrete.I) ∧
      Nonempty (PoissonDenominatorData wave15L19Concrete.I) ∧
      Nonempty (ZeroModeCertificate wave15L19Concrete.I.W) ∧
      Nonempty ThinLatticeData ∧
      wave15L19Concrete.thinData.W = wave15L19Concrete.I.W :=
  ⟨⟨wave15L19Concrete.M₁⟩, ⟨wave15L19Concrete.M₂⟩,
    ⟨wave15L19Concrete.Dnum⟩, ⟨wave15L19Concrete.Dden⟩,
    ⟨wave15L19Concrete.zeroMode⟩, ⟨wave15L19Concrete.thinData⟩,
    wave15L19Concrete.thin_W⟩

end

end Cogentic.RandomizedL19ConcreteAssembly

/-! ## Axiom audit -/

namespace Cogentic.RandomizedL19ConcreteAssembly

#print axioms commonEllipseMass_ge
#print axioms commonRho_le_exp
#print axioms commonZeroModeCertificate
#print axioms common_zeroMode_loss_pos
#print axioms commonThinData
#print axioms wave15L19Concrete
#print axioms wave15L19Concrete_thin_loss_pos
#print axioms wave15L19Concrete_poisson_loss_pos
#print axioms no_poissonQuotientInputs_at_concreteW
#print axioms wave15L19Concrete_fields

end Cogentic.RandomizedL19ConcreteAssembly
