import Cogentic.RandomizedL19Poisson
import Cogentic.RandomizedL19Energy

/-!
# L19.4: the Poisson quotient from concrete finite energy and mass data

`Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs` records the L19.4
Poisson quotient, but leaves four analytic proof fields:

* `E₁_bound`, `E₂_bound` — the two marginal-energy envelopes;
* `numerator_energy` — the coupled-mode error bound;
* `A_bound` — the retained-mode denominator bound.

`RandomizedL19Poisson` and `RandomizedL19Energy` reduce the last three to the
finite coupled-mode data `CoupledNumeratorData`, the explicit denominator data
`PoissonDenominatorData`, and the scalar certificates `EnergyScaleInputs`.

This file performs the concrete assembly.  The finite data are:

* a finite phase/multiplier set `phases n` with nonnegative weights `weight n`;
* two finite frequency grids and arrays `f`, `g` on a common short-mode type,
  giving the *finite* Parseval sums `marginal₁`, `marginal₂` and the signed
  coupled sum `coupledSum`;
* two *finite* marginal mass counts `massCount₁`, `massCount₂`;
* a finite retained-mode denominator array `term`, giving the finite denominator
  sum `A n = ∑ o, weight n o * term n o`.

The marginal energies are the actual normalized finite energies

  `E₁ n = √(marginal₁ n) / mass₁ n`,  `E₂ n = √(marginal₂ n) / mass₂ n`,

and the Poisson numerator error is the normalized finite coupled sum

  `E n = coupledSum n / (mass₁ n * mass₂ n)`.

The Poisson identity is *definitional*: `actual n` is defined to be
`(nu n + E n) / (1 + A n)`, so `actual_eq` is `rfl`.  The loss is therefore the
genuine absolute Poisson error `|actual n - nu n|`; no error, mass, or loss is
set to zero.

## What is proved unconditionally

The finite second-moment computation proves, without any analytic hypothesis:

* the **energy identities** `M.energy n = M.envelope n / M.mass n` for both
  marginal certificates (the right-hand side is the finite Parseval sum divided
  by the finite mass);
* the **numerator bound** `|E n| ≤ E₁ n * E₂ n`, by applying the coupled-mode
  Cauchy–Schwarz inequality to the finite arrays;
* the **denominator reduction** from the retained-mode finite sum to
  `|A n| ≤ D^{cDen} V^{-(ξ-2ζ)}`.

## The remaining analytic estimates

Exactly five explicit `Prop`s remain, each stated about the concrete finite
data:

* `EnvelopeGrowth₁`, `EnvelopeGrowth₂`: the finite Parseval energies grow at
  most like `D^{c_i}`;
* `MassLowerBound₁`, `MassLowerBound₂`: the finite marginal counts dominate
  `V^{η_i}`;
* `DenominatorGrowth`: the finite retained-mode denominator sum is
  `D^{cDen} V^{-ξ} V^{2ζ}`.

`FinitePoissonData.toPoissonQuotient` is the proven reduction from these five
`Prop`s to a fully discharged `PoissonQuotientInputs`, and
`FinitePoissonData.AnalyticInputs.subexpLoss` / `slot_le` give the L19.4
`SubexpLoss` and `B = 2` C5 slot bounds.

Nothing here is a `sorry`, an `admit`, an `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL19PoissonEnergy

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19Poisson
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements

/-! ## 1. Finite phase, mode and denominator data -/

/-- The finite coupled-mode data of the Poisson numerator: a finite phase set
with nonnegative weights, a common short-mode index type embedded in two finite
frequency grids, and the two arrays `f`, `g`.  This is the concrete data behind
`RandomizedL19Poisson.CoupledNumeratorData`, with the phases, weights and arrays
fixed rather than merely quantified. -/
structure FiniteModeData where
  /-- The finite phase/multiplier index type. -/
  Ω : Type
  /-- The common short-mode index type. -/
  S : Type
  /-- The first frequency grid. -/
  A : Type
  /-- The second frequency grid. -/
  B : Type
  /-- The short-mode type is finite. -/
  [instS : Fintype S]
  /-- The first frequency grid is finite. -/
  [instA : Fintype A]
  /-- The second frequency grid is finite. -/
  [instB : Fintype B]
  /-- The retained phase sets. -/
  phases : ℕ → Finset Ω
  /-- The multiplier/phase weights. -/
  weight : ℕ → Ω → ℝ
  /-- The weights are nonnegative on the retained phases. -/
  weight_nonneg : ∀ n o, o ∈ phases n → 0 ≤ weight n o
  /-- The embedding of the short modes into the first grid. -/
  inj₁ : S ↪ A
  /-- The embedding of the short modes into the second grid. -/
  inj₂ : S ↪ B
  /-- The first coordinate array. -/
  f : ℕ → Ω → A → ℝ
  /-- The second coordinate array. -/
  g : ℕ → Ω → B → ℝ

namespace FiniteModeData

/-- The finite first marginal Parseval sum. -/
noncomputable def marginal₁ (D : FiniteModeData) (n : ℕ) : ℝ :=
  letI := D.instA
  ∑ o ∈ D.phases n, D.weight n o * ∑ a, D.f n o a ^ 2

/-- The finite second marginal Parseval sum. -/
noncomputable def marginal₂ (D : FiniteModeData) (n : ℕ) : ℝ :=
  letI := D.instB
  ∑ o ∈ D.phases n, D.weight n o * ∑ b, D.g n o b ^ 2

/-- The signed finite coupled-mode numerator sum (the unnormalized numerator
error). -/
noncomputable def coupledSum (D : FiniteModeData) (n : ℕ) : ℝ :=
  letI := D.instS
  ∑ o ∈ D.phases n, D.weight n o *
    ∑ s, D.f n o (D.inj₁ s) * D.g n o (D.inj₂ s)

/-- The finite coupled sum written with the short-mode instance made explicit. -/
theorem coupledSum_eq (D : FiniteModeData) (n : ℕ) :
    D.coupledSum n =
      letI := D.instS
      ∑ o ∈ D.phases n, D.weight n o *
        ∑ s, D.f n o (D.inj₁ s) * D.g n o (D.inj₂ s) := rfl

/-- The first finite Parseval sum is nonnegative. -/
theorem marginal₁_nonneg (D : FiniteModeData) (n : ℕ) : 0 ≤ D.marginal₁ n := by
  letI := D.instA
  unfold marginal₁
  apply Finset.sum_nonneg
  intro o ho
  exact mul_nonneg (D.weight_nonneg n o ho)
    (Finset.sum_nonneg fun a _ => sq_nonneg (D.f n o a))

/-- The second finite Parseval sum is nonnegative. -/
theorem marginal₂_nonneg (D : FiniteModeData) (n : ℕ) : 0 ≤ D.marginal₂ n := by
  letI := D.instB
  unfold marginal₂
  apply Finset.sum_nonneg
  intro o ho
  exact mul_nonneg (D.weight_nonneg n o ho)
    (Finset.sum_nonneg fun b _ => sq_nonneg (D.g n o b))

/-- **Finite coupled-mode Cauchy–Schwarz.**  The absolute value of the finite
coupled sum is at most the product of the two finite Parseval energies.  This is
the actual finite second-moment computation; it uses only the triangle
inequality and Cauchy–Schwarz on the finite arrays. -/
theorem abs_coupledSum_le (D : FiniteModeData) (n : ℕ) :
    |D.coupledSum n| ≤ Real.sqrt (D.marginal₁ n) * Real.sqrt (D.marginal₂ n) := by
  have h1 := D.marginal₁_nonneg n
  have h2 := D.marginal₂_nonneg n
  refine @abs_le_coupled_modes D.Ω D.S D.A D.B D.instS D.instA D.instB
    (D.phases n) (D.weight n) (D.weight_nonneg n)
    D.inj₁ D.inj₂ (D.f n) (D.g n)
    (D.coupledSum n) (Real.sqrt (D.marginal₁ n))
    (Real.sqrt (D.marginal₂ n)) (D.coupledSum_eq n)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ?_ ?_
  · rw [Real.sq_sqrt h1]
    exact le_rfl
  · rw [Real.sq_sqrt h2]
    exact le_rfl

end FiniteModeData

/-- The finite retained-mode denominator data.  The denominator error is the
finite sum `∑ o, weight n o * term n o`; `xi` is the width-ratio separation,
`zeta` the twisted-Gaussian variation exponent, and `cDen` the polynomial
constant of the retained-mode envelope. -/
structure FiniteDenominatorData (M : FiniteModeData) where
  /-- The finite retained-mode array. -/
  term : ℕ → M.Ω → ℝ
  /-- Width-ratio separation exponent `ξ > 0`. -/
  xi : ℝ
  /-- The separation exponent is positive. -/
  xi_pos : 0 < xi
  /-- The narrow width `σ = V^{101/100}` supplies any separation `ξ ≤ 1/100`. -/
  xi_le_narrow : xi ≤ 1 / 100
  /-- Twisted-Gaussian variation exponent `ζ`. -/
  zeta : ℝ
  /-- The variation exponent is nonnegative. -/
  zeta_nonneg : 0 ≤ zeta
  /-- **Denominator gain** `2ζ < ξ`. -/
  variation_gap : 2 * zeta < xi
  /-- Exponent of `D` in the retained-mode denominator envelope. -/
  cDen : ℝ

namespace FiniteDenominatorData

variable {M : FiniteModeData}

/-- The finite retained-mode denominator sum. -/
noncomputable def sum (D : FiniteDenominatorData M) (n : ℕ) : ℝ :=
  ∑ o ∈ M.phases n, M.weight n o * D.term n o

/-- The denominator decay exponent `ηA = ξ - 2ζ`. -/
noncomputable def etaA (D : FiniteDenominatorData M) : ℝ := D.xi - 2 * D.zeta

/-- **`ηA > 0`**, from the paper's condition `2ζ < ξ`. -/
theorem etaA_pos (D : FiniteDenominatorData M) : 0 < D.etaA := by
  unfold etaA
  linarith only [D.variation_gap]

/-- The single remaining analytic estimate for the denominator: the finite
retained-mode sum is `D^{cDen} V^{-ξ} V^{2ζ}`.  This is exactly the retained-mode
estimate of `research/keybreak-mixed-strip-moment.md` §"Denominator of the
Poisson quotient", with the polynomial `o(1)` absorbed into `D^{cDen}`. -/
def DenominatorGrowth (D : FiniteDenominatorData M) (W : ℕ → ℝ) : Prop :=
  ∀ n, |D.sum n| ≤
    exp (D.cDen * scale n) * exp (-D.xi * W n) * exp (2 * D.zeta * W n)

/-- **Denominator reduction.**  The retained-mode estimate implies the L19.4
ledger shape with `cA = cDen` and `ηA = ξ - 2ζ`; the proof is the paper's
identity `V^{-ξ} V^{2ζ} = V^{-(ξ-2ζ)}`. -/
theorem A_bound (D : FiniteDenominatorData M) {W : ℕ → ℝ}
    (h : D.DenominatorGrowth W) (n : ℕ) :
    |D.sum n| ≤ exp (D.cDen * scale n) * exp (-D.etaA * W n) := by
  have hfac : exp (-D.xi * W n) * exp (2 * D.zeta * W n) =
      exp (-(D.xi - 2 * D.zeta) * W n) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    |D.sum n| ≤ exp (D.cDen * scale n) * exp (-D.xi * W n) *
        exp (2 * D.zeta * W n) := h n
    _ = exp (D.cDen * scale n) *
        (exp (-D.xi * W n) * exp (2 * D.zeta * W n)) := by ring
    _ = exp (D.cDen * scale n) * exp (-(D.xi - 2 * D.zeta) * W n) := by
      rw [hfac]
    _ = exp (D.cDen * scale n) * exp (-D.etaA * W n) := by
      simp only [etaA]

end FiniteDenominatorData

/-! ## 2. Concrete finite Poisson data -/

/-- The concrete finite data of the L19.4 Poisson quotient.  It contains the
finite mode data, the finite denominator data, the two finite marginal mass
counts, and the narrow-width/mark data of `PoissonQuotientInputs`.  No analytic
estimate is hidden in the structure: the five explicit `Prop`s below are stated
separately. -/
structure FinitePoissonData where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- `log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `log D = scale n`. -/
  W_dominates : DominatesScale W
  /-- The first prime mark denominator. -/
  mark₁ : ℕ → ℕ
  /-- The second prime mark denominator. -/
  mark₂ : ℕ → ℕ
  /-- The first mark is prime. -/
  mark₁_prime : ∀ n, (mark₁ n).Prime
  /-- The second mark is prime. -/
  mark₂_prime : ∀ n, (mark₂ n).Prime
  /-- Distinct prime marks. -/
  mark_distinct : ∀ n, mark₁ n ≠ mark₂ n
  /-- Both marks lie in the top scale `O(V)`. -/
  mark_le : ∀ n, (max (mark₁ n) (mark₂ n) : ℝ) ≤ exp (W n)
  /-- The discrete Gaussian width. -/
  sigma : ℕ → ℝ
  /-- The width is positive. -/
  sigma_pos : ∀ n, 0 < sigma n
  /-- **Narrow width**: `σ = V^{1.01}` with `V = exp W`. -/
  sigma_narrow : ∀ n, sigma n = exp (W n) ^ (101 / 100 : ℝ)
  /-- The ideal normalized mass `ν(f)`. -/
  nu : ℕ → ℝ
  /-- `ν` is a normalized mass. -/
  nu_nonneg : ∀ n, 0 ≤ nu n
  /-- `ν` is at most one. -/
  nu_le_one : ∀ n, nu n ≤ 1
  /-- The finite coupled-mode data of the numerator. -/
  mode : FiniteModeData
  /-- The finite retained-mode denominator data. -/
  den : FiniteDenominatorData mode
  /-- The first finite marginal mass count. -/
  massCount₁ : ℕ → ℕ
  /-- The second finite marginal mass count. -/
  massCount₂ : ℕ → ℕ
  /-- The first count is positive. -/
  massCount₁_pos : ∀ n, 0 < massCount₁ n
  /-- The second count is positive. -/
  massCount₂_pos : ∀ n, 0 < massCount₂ n
  /-- Exponent in `E₁ = D^{c₁}`. -/
  c₁ : ℝ
  /-- Exponent in `E₂ = D^{c₂}`. -/
  c₂ : ℝ
  /-- Marginal decay exponent of `E₁` in `V`. -/
  η₁ : ℝ
  /-- Marginal decay exponent of `E₂` in `V`. -/
  η₂ : ℝ
  /-- The first marginal decay is genuine. -/
  η₁_pos : 0 < η₁
  /-- The second marginal decay is genuine. -/
  η₂_pos : 0 < η₂

namespace FinitePoissonData

variable (D : FinitePoissonData)

/-- The finite first marginal mass `mass₁ = massCount₁`. -/
noncomputable def mass₁ (n : ℕ) : ℝ := (D.massCount₁ n : ℝ)

/-- The finite second marginal mass `mass₂ = massCount₂`. -/
noncomputable def mass₂ (n : ℕ) : ℝ := (D.massCount₂ n : ℝ)

/-- The finite first mass is positive. -/
theorem mass₁_pos (n : ℕ) : 0 < D.mass₁ n := by
  unfold mass₁
  exact_mod_cast D.massCount₁_pos n

/-- The finite second mass is positive. -/
theorem mass₂_pos (n : ℕ) : 0 < D.mass₂ n := by
  unfold mass₂
  exact_mod_cast D.massCount₂_pos n

/-- The normalized finite first marginal energy `E₁ = √marginal₁ / mass₁`. -/
noncomputable def E₁ (n : ℕ) : ℝ := Real.sqrt (D.mode.marginal₁ n) / D.mass₁ n

/-- The normalized finite second marginal energy `E₂ = √marginal₂ / mass₂`. -/
noncomputable def E₂ (n : ℕ) : ℝ := Real.sqrt (D.mode.marginal₂ n) / D.mass₂ n

/-- The normalized finite Poisson numerator error
`E = coupledSum / (mass₁ mass₂)`. -/
noncomputable def E (n : ℕ) : ℝ :=
  D.mode.coupledSum n / (D.mass₁ n * D.mass₂ n)

/-- The finite retained-mode denominator error. -/
noncomputable def A (n : ℕ) : ℝ := D.den.sum n

/-- The actual two-mark pair probability, **defined** as the Poisson quotient
of `ν + E` by `1 + A`.  The Poisson identity is therefore definitional. -/
noncomputable def actual (n : ℕ) : ℝ := (D.nu n + D.E n) / (1 + D.A n)

/-- The first finite energy is nonnegative. -/
theorem E₁_nonneg (n : ℕ) : 0 ≤ D.E₁ n :=
  div_nonneg (Real.sqrt_nonneg _) (D.mass₁_pos n).le

/-- The second finite energy is nonnegative. -/
theorem E₂_nonneg (n : ℕ) : 0 ≤ D.E₂ n :=
  div_nonneg (Real.sqrt_nonneg _) (D.mass₂_pos n).le

/-- The numerator error is the normalized finite coupled sum. -/
theorem E_eq (n : ℕ) :
    D.E n = D.mode.coupledSum n / (D.mass₁ n * D.mass₂ n) := rfl

/-- The denominator error is the finite retained-mode sum. -/
theorem A_eq (n : ℕ) :
    D.A n = ∑ o ∈ D.mode.phases n, D.mode.weight n o * D.den.term n o := rfl

/-- **The finite numerator bound, unconditionally.**  The normalized coupled sum
is bounded by the product of the two normalized finite energies.  This is the
finite second-moment computation of L19.2/L19.4. -/
theorem abs_E_le (n : ℕ) : |D.E n| ≤ D.E₁ n * D.E₂ n := by
  have hc := D.mode.abs_coupledSum_le n
  have hm₁ := D.mass₁_pos n
  have hm₂ := D.mass₂_pos n
  have hmpos : 0 < D.mass₁ n * D.mass₂ n := mul_pos hm₁ hm₂
  calc
    |D.E n| = |D.mode.coupledSum n| / (D.mass₁ n * D.mass₂ n) := by
      unfold E
      rw [abs_div, abs_of_pos hmpos]
    _ ≤ (Real.sqrt (D.mode.marginal₁ n) * Real.sqrt (D.mode.marginal₂ n)) /
        (D.mass₁ n * D.mass₂ n) :=
      div_le_div_of_nonneg_right hc hmpos.le
    _ = D.E₁ n * D.E₂ n := by
      unfold E₁ E₂
      rw [div_mul_div_comm]

/-- **The finite numerator error is genuinely the finite mode sum.**  A nonzero
coupled mode sum gives a nonzero numerator error. -/
theorem E_ne_zero_of_coupledSum_ne_zero {n : ℕ}
    (h : D.mode.coupledSum n ≠ 0) : D.E n ≠ 0 := by
  unfold E
  exact div_ne_zero h (mul_ne_zero (D.mass₁_pos n).ne' (D.mass₂_pos n).ne')

/-- **The first finite energy is nonzero when a retained coefficient is.**  This
records that `E₁` is the actual normalized Parseval energy, not a zero
placeholder: a nonzero retained coefficient with positive weight forces it
positive. -/
theorem E₁_pos_of_coeff {n : ℕ} {o : D.mode.Ω} (ho : o ∈ D.mode.phases n)
    (hw : 0 < D.mode.weight n o) {a : D.mode.A} (hf : D.mode.f n o a ≠ 0) :
    0 < D.E₁ n := by
  have hmarg : 0 < D.mode.marginal₁ n := by
    letI := D.mode.instA
    unfold FiniteModeData.marginal₁
    have hinner : 0 < ∑ a, D.mode.f n o a ^ 2 :=
      Finset.sum_pos' (fun a _ => sq_nonneg _)
        ⟨a, Finset.mem_univ a, sq_pos_of_ne_zero hf⟩
    have hterm : 0 < D.mode.weight n o * ∑ a, D.mode.f n o a ^ 2 :=
      mul_pos hw hinner
    exact lt_of_lt_of_le hterm (Finset.single_le_sum
      (f := fun o => D.mode.weight n o * ∑ a, D.mode.f n o a ^ 2)
      (fun o ho => mul_nonneg (D.mode.weight_nonneg n o ho)
        (Finset.sum_nonneg fun a _ => sq_nonneg (D.mode.f n o a))) ho)
  unfold E₁
  exact div_pos (Real.sqrt_pos.mpr hmarg) (D.mass₁_pos n)

/-- **The energy identity for the first marginal certificate.**  The certificate
energy is exactly the finite Parseval envelope divided by the finite mass. -/
theorem energy_identity₁ (n : ℕ) :
    (Real.sqrt (D.mode.marginal₁ n)) / D.mass₁ n = D.E₁ n := rfl

/-- **The energy identity for the second marginal certificate.** -/
theorem energy_identity₂ (n : ℕ) :
    (Real.sqrt (D.mode.marginal₂ n)) / D.mass₂ n = D.E₂ n := rfl

/-- The concrete finite first marginal mass lower bound
`V^{η₁} ≤ mass₁`. -/
def MassLowerBound₁ : Prop := ∀ n, exp (D.η₁ * D.W n) ≤ D.mass₁ n

/-- The concrete finite second marginal mass lower bound
`V^{η₂} ≤ mass₂`. -/
def MassLowerBound₂ : Prop := ∀ n, exp (D.η₂ * D.W n) ≤ D.mass₂ n

/-- The single remaining analytic estimate for the first marginal: the finite
Parseval envelope grows at most like `D^{c₁}`. -/
def EnvelopeGrowth₁ : Prop :=
  ∀ n, Real.sqrt (D.mode.marginal₁ n) ≤ exp (D.c₁ * scale n)

/-- The single remaining analytic estimate for the second marginal: the finite
Parseval envelope grows at most like `D^{c₂}`. -/
def EnvelopeGrowth₂ : Prop :=
  ∀ n, Real.sqrt (D.mode.marginal₂ n) ≤ exp (D.c₂ * scale n)

/-- The remaining analytic estimate for the denominator. -/
def DenominatorGrowth : Prop := D.den.DenominatorGrowth D.W

/-! ### 2.1 The two `EnergyScaleInputs` certificates -/

/-- **The first marginal `EnergyScaleInputs` certificate.**  The energy is the
normalized finite Parseval energy, the envelope is the finite Parseval sum, and
the mass is the finite count.  The energy identity is definitional; the only
analytic input is `EnvelopeGrowth₁`, and the mass input is `MassLowerBound₁`. -/
noncomputable def M₁ (hgrowth : D.EnvelopeGrowth₁) (hmass : D.MassLowerBound₁) :
    EnergyScaleInputs D.W where
  W_nonneg := D.W_nonneg
  W_dominates := D.W_dominates
  c := D.c₁
  η := D.η₁
  η_pos := D.η₁_pos
  energy := D.E₁
  envelope := fun n => Real.sqrt (D.mode.marginal₁ n)
  mass := D.mass₁
  energy_nonneg := D.E₁_nonneg
  envelope_nonneg := fun _ => Real.sqrt_nonneg _
  mass_pos := D.mass₁_pos
  energy_le_envelope := fun _ => le_rfl
  envelope_poly := hgrowth
  mass_lower := hmass

/-- **The second marginal `EnergyScaleInputs` certificate.** -/
noncomputable def M₂ (hgrowth : D.EnvelopeGrowth₂) (hmass : D.MassLowerBound₂) :
    EnergyScaleInputs D.W where
  W_nonneg := D.W_nonneg
  W_dominates := D.W_dominates
  c := D.c₂
  η := D.η₂
  η_pos := D.η₂_pos
  energy := D.E₂
  envelope := fun n => Real.sqrt (D.mode.marginal₂ n)
  mass := D.mass₂
  energy_nonneg := D.E₂_nonneg
  envelope_nonneg := fun _ => Real.sqrt_nonneg _
  mass_pos := D.mass₂_pos
  energy_le_envelope := fun _ => le_rfl
  envelope_poly := hgrowth
  mass_lower := hmass

/-- The first certificate's energy is literally `E₁`. -/
@[simp] theorem M₁_energy (hgrowth : D.EnvelopeGrowth₁) (hmass : D.MassLowerBound₁) :
    (D.M₁ hgrowth hmass).energy = D.E₁ := rfl

/-- **The first certificate's energy identity**: the certificate energy is the
finite Parseval envelope divided by the finite marginal mass. -/
theorem M₁_energy_identity (hgrowth : D.EnvelopeGrowth₁) (hmass : D.MassLowerBound₁)
    (n : ℕ) :
    (D.M₁ hgrowth hmass).energy n =
      (D.M₁ hgrowth hmass).envelope n / (D.M₁ hgrowth hmass).mass n := rfl

/-- The first certificate's polynomial exponent is literally `c₁`. -/
@[simp] theorem M₁_c (hgrowth : D.EnvelopeGrowth₁) (hmass : D.MassLowerBound₁) :
    (D.M₁ hgrowth hmass).c = D.c₁ := rfl

/-- The first certificate's decay exponent is literally `η₁`. -/
@[simp] theorem M₁_η (hgrowth : D.EnvelopeGrowth₁) (hmass : D.MassLowerBound₁) :
    (D.M₁ hgrowth hmass).η = D.η₁ := rfl

/-- The second certificate's energy is literally `E₂`. -/
@[simp] theorem M₂_energy (hgrowth : D.EnvelopeGrowth₂) (hmass : D.MassLowerBound₂) :
    (D.M₂ hgrowth hmass).energy = D.E₂ := rfl

/-- **The second certificate's energy identity**. -/
theorem M₂_energy_identity (hgrowth : D.EnvelopeGrowth₂) (hmass : D.MassLowerBound₂)
    (n : ℕ) :
    (D.M₂ hgrowth hmass).energy n =
      (D.M₂ hgrowth hmass).envelope n / (D.M₂ hgrowth hmass).mass n := rfl

/-- The second certificate's polynomial exponent is literally `c₂`. -/
@[simp] theorem M₂_c (hgrowth : D.EnvelopeGrowth₂) (hmass : D.MassLowerBound₂) :
    (D.M₂ hgrowth hmass).c = D.c₂ := rfl

/-- The second certificate's decay exponent is literally `η₂`. -/
@[simp] theorem M₂_η (hgrowth : D.EnvelopeGrowth₂) (hmass : D.MassLowerBound₂) :
    (D.M₂ hgrowth hmass).η = D.η₂ := rfl

/-- **The first marginal decay bound**, derived from the finite certificate. -/
theorem E₁_bound (hgrowth : D.EnvelopeGrowth₁) (hmass : D.MassLowerBound₁) (n : ℕ) :
    D.E₁ n ≤ exp (D.c₁ * scale n) * exp (-D.η₁ * D.W n) :=
  (D.M₁ hgrowth hmass).bound n

/-- **The second marginal decay bound**, derived from the finite certificate. -/
theorem E₂_bound (hgrowth : D.EnvelopeGrowth₂) (hmass : D.MassLowerBound₂) (n : ℕ) :
    D.E₂ n ≤ exp (D.c₂ * scale n) * exp (-D.η₂ * D.W n) :=
  (D.M₂ hgrowth hmass).bound n

/-- **The product of the two finite marginal energies is `SubexpLoss`.**  This is
the scalar L19.2 → L19.4 step, using only the two `EnergyScaleInputs`
certificates. -/
theorem marginalProduct_subexpLoss
    (hgrowth₁ : D.EnvelopeGrowth₁) (hmass₁ : D.MassLowerBound₁)
    (hgrowth₂ : D.EnvelopeGrowth₂) (hmass₂ : D.MassLowerBound₂) :
    SubexpLoss (fun n => D.E₁ n * D.E₂ n) :=
  subexpLoss_marginal_product D.W_dominates D.η₁_pos D.η₂_pos
    D.E₁_nonneg D.E₂_nonneg (D.E₁_bound hgrowth₁ hmass₁)
    (D.E₂_bound hgrowth₂ hmass₂)

/-- **The numerator error is `SubexpLoss`.**  The unconditional finite
Cauchy–Schwarz bound `|E| ≤ E₁ E₂` upgrades the marginal decay to the signed
numerator itself. -/
theorem abs_E_subexpLoss
    (hgrowth₁ : D.EnvelopeGrowth₁) (hmass₁ : D.MassLowerBound₁)
    (hgrowth₂ : D.EnvelopeGrowth₂) (hmass₂ : D.MassLowerBound₂) :
    SubexpLoss (fun n => |D.E n|) :=
  subexpLoss_of_eventually_le (Eventually.of_forall D.abs_E_le)
    (D.marginalProduct_subexpLoss hgrowth₁ hmass₁ hgrowth₂ hmass₂)

/-- **The denominator error is `SubexpLoss`** once the retained-mode estimate
holds. -/
theorem abs_A_subexpLoss (hden : D.DenominatorGrowth) :
    SubexpLoss (fun n => |D.A n|) := by
  apply subexpLoss_of_eventually_le
    (g := fun n => exp (D.den.cDen * scale n) * exp (-D.den.etaA * D.W n))
  · exact Eventually.of_forall fun n => D.den.A_bound hden n
  · exact subexpLoss_exp_mul_exp_neg D.W_dominates (C := D.den.cDen) D.den.etaA_pos

/-! ### 2.2 The assembled Poisson quotient -/

/-- **The L19.4 Poisson quotient from the finite data.**  All four analytic
fields of `PoissonQuotientInputs` are discharged: `E₁_bound`/`E₂_bound` from the
two `EnergyScaleInputs` certificates, `numerator_energy` from the finite
Cauchy–Schwarz computation, and `A_bound` from the retained-mode denominator
reduction.  The five `Prop` arguments are the only remaining estimates. -/
noncomputable def toPoissonQuotient
    (hgrowth₁ : D.EnvelopeGrowth₁) (hmass₁ : D.MassLowerBound₁)
    (hgrowth₂ : D.EnvelopeGrowth₂) (hmass₂ : D.MassLowerBound₂)
    (hden : D.DenominatorGrowth) : PoissonQuotientInputs :=
  { W := D.W
    W_nonneg := D.W_nonneg
    W_dominates := D.W_dominates
    mark₁ := D.mark₁
    mark₂ := D.mark₂
    mark₁_prime := D.mark₁_prime
    mark₂_prime := D.mark₂_prime
    mark_distinct := D.mark_distinct
    mark_le := D.mark_le
    sigma := D.sigma
    sigma_pos := D.sigma_pos
    sigma_narrow := D.sigma_narrow
    nu := D.nu
    nu_nonneg := D.nu_nonneg
    nu_le_one := D.nu_le_one
    E := D.E
    A := D.A
    actual := D.actual
    actual_eq := fun _ => rfl
    E₁ := D.E₁
    E₂ := D.E₂
    E₁_nonneg := D.E₁_nonneg
    E₂_nonneg := D.E₂_nonneg
    c₁ := D.c₁
    c₂ := D.c₂
    η₁ := D.η₁
    η₂ := D.η₂
    η₁_pos := D.η₁_pos
    η₂_pos := D.η₂_pos
    E₁_bound := fun n => D.E₁_bound hgrowth₁ hmass₁ n
    E₂_bound := fun n => D.E₂_bound hgrowth₂ hmass₂ n
    numerator_energy := D.abs_E_le
    cA := D.den.cDen
    ηA := D.den.etaA
    ηA_pos := D.den.etaA_pos
    A_bound := D.den.A_bound hden }

/-- The assembled quotient keeps the finite numerator error `E`. -/
@[simp] theorem toPoissonQuotient_E (hgrowth₁ : D.EnvelopeGrowth₁)
    (hmass₁ : D.MassLowerBound₁) (hgrowth₂ : D.EnvelopeGrowth₂)
    (hmass₂ : D.MassLowerBound₂) (hden : D.DenominatorGrowth) :
    (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).E = D.E := rfl

/-- The assembled quotient keeps the finite denominator error `A`. -/
@[simp] theorem toPoissonQuotient_A (hgrowth₁ : D.EnvelopeGrowth₁)
    (hmass₁ : D.MassLowerBound₁) (hgrowth₂ : D.EnvelopeGrowth₂)
    (hmass₂ : D.MassLowerBound₂) (hden : D.DenominatorGrowth) :
    (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).A = D.A := rfl

/-- The assembled quotient keeps the two finite marginal energies. -/
@[simp] theorem toPoissonQuotient_E₁ (hgrowth₁ : D.EnvelopeGrowth₁)
    (hmass₁ : D.MassLowerBound₁) (hgrowth₂ : D.EnvelopeGrowth₂)
    (hmass₂ : D.MassLowerBound₂) (hden : D.DenominatorGrowth) :
    (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).E₁ = D.E₁ := rfl

/-- The assembled quotient keeps the second finite marginal energy. -/
@[simp] theorem toPoissonQuotient_E₂ (hgrowth₁ : D.EnvelopeGrowth₁)
    (hmass₁ : D.MassLowerBound₁) (hgrowth₂ : D.EnvelopeGrowth₂)
    (hmass₂ : D.MassLowerBound₂) (hden : D.DenominatorGrowth) :
    (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).E₂ = D.E₂ := rfl

/-- **The Poisson identity of the assembled quotient is definitional.** -/
theorem toPoissonQuotient_actual_eq (hgrowth₁ : D.EnvelopeGrowth₁)
    (hmass₁ : D.MassLowerBound₁) (hgrowth₂ : D.EnvelopeGrowth₂)
    (hmass₂ : D.MassLowerBound₂) (hden : D.DenominatorGrowth) (n : ℕ) :
    (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).actual n =
      ((D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).nu n +
        (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).E n) /
        (1 + (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).A n) :=
  (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).actual_eq n

/-- The loss is the genuine absolute Poisson error, definitionally. -/
theorem loss_eq (hgrowth₁ : D.EnvelopeGrowth₁) (hmass₁ : D.MassLowerBound₁)
    (hgrowth₂ : D.EnvelopeGrowth₂) (hmass₂ : D.MassLowerBound₂)
    (hden : D.DenominatorGrowth) (n : ℕ) :
    (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden).loss n =
      |D.actual n - D.nu n| := rfl

/-! ### 2.3 The bundled remaining estimates -/

/-- The five explicit `Prop`s that remain after the finite computation.  This is
only a convenient bundle; each field is separately stated above. -/
structure AnalyticInputs : Prop where
  /-- Polynomial growth of the first finite Parseval envelope. -/
  growth₁ : D.EnvelopeGrowth₁
  /-- `V^{η₁} ≤ mass₁` for the first finite mass. -/
  mass₁ : D.MassLowerBound₁
  /-- Polynomial growth of the second finite Parseval envelope. -/
  growth₂ : D.EnvelopeGrowth₂
  /-- `V^{η₂} ≤ mass₂` for the second finite mass. -/
  mass₂ : D.MassLowerBound₂
  /-- The retained-mode denominator estimate. -/
  denominator : D.DenominatorGrowth

/-- **The proven reduction from the five explicit estimates to L19.4.**  The
quotient has all four analytic fields discharged, hence its loss is
`SubexpLoss` and its `B = 2` slot is genuine. -/
noncomputable def AnalyticInputs.toPoissonQuotient (H : D.AnalyticInputs) :
    PoissonQuotientInputs :=
  D.toPoissonQuotient H.growth₁ H.mass₁ H.growth₂ H.mass₂ H.denominator

/-- **L19.4 `SubexpLoss` from the finite data and the five explicit estimates.** -/
theorem AnalyticInputs.subexpLoss (H : D.AnalyticInputs) :
    SubexpLoss H.toPoissonQuotient.loss :=
  H.toPoissonQuotient.subexpLoss

/-- **The `B = 2` C5 slot from the finite data and the five explicit estimates.** -/
theorem AnalyticInputs.slot_le (H : D.AnalyticInputs) :
    ∀ᶠ n : ℕ in atTop,
      H.toPoissonQuotient.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  H.toPoissonQuotient.slot_le

/-- The assembled leaf for the finite certificate. -/
noncomputable def AnalyticInputs.toSubexpLeaf (H : D.AnalyticInputs) : SubexpLeaf :=
  H.toPoissonQuotient.toSubexpLeaf

/-! ## 3. Consistency with the paper's denominator certificate -/

/-- The finite denominator data, read in the paper's `PoissonDenominatorData`
form for the assembled quotient.  This shows that the retained-mode estimate
used above is literally the existing denominator interface, with the same
exponents `cDen`, `ξ`, `ζ`. -/
noncomputable def toPoissonDenominatorData
    (hgrowth₁ : D.EnvelopeGrowth₁) (hmass₁ : D.MassLowerBound₁)
    (hgrowth₂ : D.EnvelopeGrowth₂) (hmass₂ : D.MassLowerBound₂)
    (hden : D.DenominatorGrowth) :
    PoissonDenominatorData
      (D.toPoissonQuotient hgrowth₁ hmass₁ hgrowth₂ hmass₂ hden) where
  xi := D.den.xi
  xi_pos := D.den.xi_pos
  xi_le_narrow := D.den.xi_le_narrow
  zeta := D.den.zeta
  zeta_nonneg := D.den.zeta_nonneg
  variation_gap := D.den.variation_gap
  cDen := D.den.cDen
  denominator_raw := hden

end FinitePoissonData

/-! ## 4. Axiom audit -/

#print axioms FiniteModeData.marginal₁_nonneg
#print axioms FiniteModeData.marginal₂_nonneg
#print axioms FiniteModeData.abs_coupledSum_le
#print axioms FiniteDenominatorData.etaA_pos
#print axioms FiniteDenominatorData.A_bound
#print axioms FinitePoissonData.abs_E_le
#print axioms FinitePoissonData.E_eq
#print axioms FinitePoissonData.A_eq
#print axioms FinitePoissonData.E_ne_zero_of_coupledSum_ne_zero
#print axioms FinitePoissonData.E₁_pos_of_coeff
#print axioms FinitePoissonData.energy_identity₁
#print axioms FinitePoissonData.energy_identity₂
#print axioms FinitePoissonData.E₁_bound
#print axioms FinitePoissonData.E₂_bound
#print axioms FinitePoissonData.marginalProduct_subexpLoss
#print axioms FinitePoissonData.abs_E_subexpLoss
#print axioms FinitePoissonData.abs_A_subexpLoss
#print axioms FinitePoissonData.M₁
#print axioms FinitePoissonData.M₂
#print axioms FinitePoissonData.M₁_energy_identity
#print axioms FinitePoissonData.M₂_energy_identity
#print axioms FinitePoissonData.toPoissonQuotient
#print axioms FinitePoissonData.toPoissonQuotient_actual_eq
#print axioms FinitePoissonData.loss_eq
#print axioms FinitePoissonData.AnalyticInputs.toPoissonQuotient
#print axioms FinitePoissonData.AnalyticInputs.subexpLoss
#print axioms FinitePoissonData.AnalyticInputs.slot_le
#print axioms FinitePoissonData.toPoissonDenominatorData

end Cogentic.RandomizedL19PoissonEnergy
