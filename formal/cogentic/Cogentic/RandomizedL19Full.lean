import Cogentic.RandomizedL19Energy
import Cogentic.RandomizedL19Poisson
import Cogentic.RandomizedL19ZeroMode
import Cogentic.RandomizedL19Thin

/-!
# L19 full certificate: the three narrow-width leaves assembled

This file composes the three reduced L19 certificates into the single
`RandomizedL19SecondMoment.L19Inputs` record consumed by the C5 ledger:

* **L19.4** — the Poisson quotient.  `RandomizedL19Energy` supplies the two
  marginal `EnergyScaleInputs` certificates that discharge `E₁_bound` /
  `E₂_bound` (`PoissonQuotientInputs.replaceMarginalBounds`);
  `RandomizedL19Poisson` supplies the coupled-mode numerator certificate
  (`CoupledNumeratorData`) and the denominator certificate
  (`PoissonDenominatorData`), which discharge `numerator_energy` and `A_bound`
  (`PoissonQuotientInputs.replaceNumeratorAndDenominator`).
* **L19.5** — the ideal zero mode.  `RandomizedL19ZeroMode.ZeroModeCertificate`
  supplies `IdealZeroModeInputs` through `toIdealZeroModeInputs`, with
  `zero_mode_bound` and `rho_bound` proved from the covering/layer-cake, the
  ellipse-discard, and the period-prime certificates.
* **L19.6** — thin and small-determinant pairs.
  `RandomizedL19Thin.LatticeThinInputs` supplies `ThinPairInputs` through
  `toThinPairInputs`, with both bound fields proved from the L18.4
  determinant-strip lattice count and `smallDet ≤ thin`.

The certificate keeps one common logarithmic mark scale `W = log V`: the two
Poisson marginal certificates are indexed by `I.W`, the zero-mode certificate is
a `ZeroModeCertificate I.W`, and the thin certificate is tied to `I.W` by the
explicit field `thin_W`.

## What is proved

`L19FullCertificate.toL19Inputs` builds the literal `L19Inputs` from the three
replacements, and

* `L19FullCertificate.leaves` proves that its `L19Leaves` are exactly the three
  certificate leaves;
* `L19FullCertificate.slots_bounds` proves the three eventual `B = 2` C5 slot
  bounds for `toL19Inputs.slots`;
* `L19FullCertificate.slots_bounds_loss` restates those bounds directly in terms
  of the three certificate losses;
* the `*_W` lemmas are the explicit scale adapters showing that all three
  assembled records carry the same `W = log V`, and `poisson_loss_eq` records
  that the assembled Poisson loss is literally the original one (the
  replacements only change proof fields).

No `sorry`, `admit`, `axiom`, or `native_decide` appears, and no error, mass,
fraction, or loss is set to zero.
-/

namespace Cogentic.RandomizedL19Full

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19Poisson
open Cogentic.RandomizedL19ZeroMode
open Cogentic.RandomizedL19Thin

/-- **The full L19 certificate.**

It collects the reduced data of the three leaves at one common logarithmic mark
scale `W = log V`:

* the Poisson interface `I` together with the two marginal scale certificates
  `M₁`, `M₂` (with their exponent/energy equalities) and the coupled-numerator
  and denominator certificates `Dnum`, `Dden`;
* the zero-mode certificate at `I.W`;
* the L18.4 lattice thin certificate, tied to `I.W` by `thin_W`.

The equality fields are the only adapters needed: every analytic proof field of
`PoissonQuotientInputs` used by L19.4 is replaced, and the zero-mode and thin
records are converted by their existing `toIdealZeroModeInputs` /
`toThinPairInputs` constructors. -/
structure L19FullCertificate where
  /-- The Poisson quotient interface of L19.4. -/
  I : PoissonQuotientInputs
  /-- The first marginal energy scale certificate (L19.2/L19.4). -/
  M₁ : EnergyScaleInputs I.W
  /-- The second marginal energy scale certificate (L19.2/L19.4). -/
  M₂ : EnergyScaleInputs I.W
  /-- Exponent identification for the first marginal certificate. -/
  hc₁ : M₁.c = I.c₁
  /-- Decay-exponent identification for the first marginal certificate. -/
  hη₁ : M₁.η = I.η₁
  /-- Energy identification for the first marginal certificate. -/
  hE₁ : ∀ n, M₁.energy n = I.E₁ n
  /-- Exponent identification for the second marginal certificate. -/
  hc₂ : M₂.c = I.c₂
  /-- Decay-exponent identification for the second marginal certificate. -/
  hη₂ : M₂.η = I.η₂
  /-- Energy identification for the second marginal certificate. -/
  hE₂ : ∀ n, M₂.energy n = I.E₂ n
  /-- The coupled-mode numerator certificate (L19.2/L19.4). -/
  Dnum : CoupledNumeratorData I
  /-- The Poisson denominator certificate (L19.4). -/
  Dden : PoissonDenominatorData I
  /-- The zero-mode certificate of L19.5, at the common scale `W = log V`. -/
  zeroMode : ZeroModeCertificate I.W
  /-- The L18.4 lattice thin/small-determinant certificate of L19.6. -/
  thin : LatticeThinInputs
  /-- Scale adapter: the thin certificate uses the same `W = log V`. -/
  thin_W : thin.W = I.W

namespace L19FullCertificate

variable (C : L19FullCertificate)

/-! ## 1. L19.4: the two energy replacements and the two Poisson replacements -/

/-- The Poisson record with its two marginal-energy proof fields discharged by
the energy scale certificates. -/
noncomputable def poissonEnergy : PoissonQuotientInputs :=
  C.I.replaceMarginalBounds C.M₁ C.M₂ C.hc₁ C.hη₁ C.hE₁ C.hc₂ C.hη₂ C.hE₂

/-- The Poisson record with all four analytic proof fields discharged: the two
marginal energies (`E₁_bound`, `E₂_bound`), the coupled numerator
(`numerator_energy`), and the denominator (`A_bound`, with `cA = cDen` and
`ηA = ξ - 2ζ`). -/
noncomputable def poisson : PoissonQuotientInputs :=
  C.poissonEnergy.replaceNumeratorAndDenominator C.Dnum C.Dden

/-- The assembled Poisson record keeps the original marginal energies. -/
@[simp] theorem poisson_E₁ : C.poisson.E₁ = C.I.E₁ := rfl

/-- The assembled Poisson record keeps the original second marginal energy. -/
@[simp] theorem poisson_E₂ : C.poisson.E₂ = C.I.E₂ := rfl

/-- The assembled Poisson record keeps the original actual pair probability. -/
@[simp] theorem poisson_actual : C.poisson.actual = C.I.actual := rfl

/-- The assembled Poisson record keeps the original ideal mass. -/
@[simp] theorem poisson_nu : C.poisson.nu = C.I.nu := rfl

/-- The assembled Poisson record keeps the original `W = log V`. -/
@[simp] theorem poisson_W : C.poisson.W = C.I.W := rfl

/-- **The L19.4 loss is literally the original one.**  The replacements change
only proof fields (and the denominator exponents), never `actual`, `nu`, or
their difference. -/
theorem poisson_loss_eq : C.poisson.loss = C.I.loss := rfl

/-- The assembled Poisson record satisfies the original Poisson identity. -/
theorem poisson_identity (n : ℕ) :
    C.poisson.actual n = (C.poisson.nu n + C.poisson.E n) / (1 + C.poisson.A n) :=
  C.poisson.actual_eq n

/-- The assembled narrow width is still `σ = V^{1.01}`. -/
theorem poisson_sigma_narrow (n : ℕ) :
    C.poisson.sigma n = exp (C.poisson.W n) ^ (101 / 100 : ℝ) :=
  C.poisson.sigma_narrow n

/-- The assembled denominator is eventually below `1/2`, so the quotient is
uniformly well defined. -/
theorem poisson_eventually_abs_A_le_half :
    ∀ᶠ n : ℕ in atTop, |C.poisson.A n| ≤ 1 / 2 := by
  filter_upwards [C.poisson.eventually_epsDen_le_half] with n hn
  exact (C.poisson.A_bound n).trans hn

/-! ## 2. L19.5 and L19.6 conversions -/

/-- The L19.5 `IdealZeroModeInputs` produced by the zero-mode certificate. -/
noncomputable def zeroModeInputs : IdealZeroModeInputs :=
  C.zeroMode.toIdealZeroModeInputs

/-- The L19.6 `ThinPairInputs` produced by the lattice thin certificate. -/
noncomputable def thinInputs : ThinPairInputs :=
  C.thin.toThinPairInputs

/-- Scale adapter: the L19.5 inputs use the common `W = log V`. -/
@[simp] theorem zeroModeInputs_W : C.zeroModeInputs.W = C.I.W := rfl

/-- Scale adapter: the L19.6 inputs use the lattice certificate's `W`, which the
certificate ties to `I.W`. -/
theorem thinInputs_W : C.thinInputs.W = C.I.W := C.thin_W

/-! ## 3. The composed `L19Inputs` -/

/-- **The composed L19 inputs.**  Every analytic field of the three leaves is the
one proved in the corresponding reduced certificate. -/
noncomputable def toL19Inputs : L19Inputs where
  poisson := C.poisson
  zeroMode := C.zeroModeInputs
  thin := C.thinInputs

/-- The assembled Poisson component is exactly `C.poisson`. -/
@[simp] theorem toL19Inputs_poisson : C.toL19Inputs.poisson = C.poisson := rfl

/-- The assembled zero-mode component is exactly the certificate conversion. -/
@[simp] theorem toL19Inputs_zeroMode :
    C.toL19Inputs.zeroMode = C.zeroModeInputs := rfl

/-- The assembled thin component is exactly the certificate conversion. -/
@[simp] theorem toL19Inputs_thin : C.toL19Inputs.thin = C.thinInputs := rfl

/-- Scale adapter: all three composed components use the common `W = log V`. -/
theorem toL19Inputs_W :
    C.toL19Inputs.poisson.W = C.I.W ∧
      C.toL19Inputs.zeroMode.W = C.I.W ∧
      C.toL19Inputs.thin.W = C.I.W :=
  ⟨C.poisson_W, C.zeroModeInputs_W, C.thinInputs_W⟩

/-! ## 4. `L19Inputs.leaves` -/

/-- **The leaves of the composed inputs.**  This is the literal `L19Leaves`
record of `toL19Inputs`, with each component identified with the corresponding
certificate leaf. -/
theorem leaves :
    C.toL19Inputs.leaves =
      { l19_4 := C.poisson.toSubexpLeaf
        l19_5 := C.zeroModeInputs.toSubexpLeaf
        l19_6 := C.thinInputs.toSubexpLeaf } := rfl

/-- The L19.4 leaf of the composition. -/
theorem leaves_l19_4 :
    C.toL19Inputs.leaves.l19_4 = C.poisson.toSubexpLeaf := rfl

/-- The L19.5 leaf of the composition. -/
theorem leaves_l19_5 :
    C.toL19Inputs.leaves.l19_5 = C.zeroModeInputs.toSubexpLeaf := rfl

/-- The L19.6 leaf of the composition. -/
theorem leaves_l19_6 :
    C.toL19Inputs.leaves.l19_6 = C.thinInputs.toSubexpLeaf := rfl

/-- **The three manuscript leaf statements survive the composition.**  Each leaf's
`paper` field is the genuine `SubexpLoss` statement of its reduced certificate. -/
theorem leaves_paper :
    SubexpLoss C.poisson.loss ∧
      SubexpLoss C.zeroModeInputs.loss ∧
      SubexpLoss C.thinInputs.loss :=
  ⟨C.poisson.subexpLoss, C.zeroMode.subexpLoss, C.thin.subexpLoss⟩

/-- The three `B = 2` slot bounds at the level of the leaves. -/
theorem leaves_slot :
    (∀ᶠ n : ℕ in atTop, C.poisson.loss n ≤ exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop, C.zeroModeInputs.loss n ≤ exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop, C.thinInputs.loss n ≤ exp (-(2 : ℝ) * scale n)) :=
  ⟨C.poisson.slot_le, C.zeroMode.slot_le, C.thin.slot_le⟩

/-! ## 5. `L19Inputs.slots_bounds` -/

/-- The L19.4 slot of `toL19Inputs.slots` is the assembled Poisson loss. -/
@[simp] theorem toL19Inputs_slots_poisson (rest : C5LossSlots) :
    C.toL19Inputs.slots rest .poissonQuotient = C.poisson.loss := rfl

/-- The L19.5 slot of `toL19Inputs.slots` is the assembled zero-mode loss. -/
@[simp] theorem toL19Inputs_slots_zeroMode (rest : C5LossSlots) :
    C.toL19Inputs.slots rest .idealZeroMode = C.zeroModeInputs.loss := rfl

/-- The L19.6 slot of `toL19Inputs.slots` is the assembled thin-pair loss. -/
@[simp] theorem toL19Inputs_slots_thin (rest : C5LossSlots) :
    C.toL19Inputs.slots rest .thinPairs = C.thinInputs.loss := rfl

/-- **`L19Inputs.slots_bounds` for the composed inputs.**  The three L19 slots of
the assembled C5 ledger are eventually at most `exp (-2 · scale n)`. -/
theorem slots_bounds (rest : C5LossSlots) :
    (∀ᶠ n : ℕ in atTop,
        C.toL19Inputs.slots rest .poissonQuotient n ≤ exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        C.toL19Inputs.slots rest .idealZeroMode n ≤ exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        C.toL19Inputs.slots rest .thinPairs n ≤ exp (-(2 : ℝ) * scale n)) :=
  C.toL19Inputs.slots_bounds rest

/-- **The three slot bounds in terms of the certificate losses.**  This is
`slots_bounds` with the ledger slots unfolded to the Poisson, zero-mode, and
thin-pair losses of the certificate. -/
theorem slots_bounds_loss (_rest : C5LossSlots) :
    (∀ᶠ n : ℕ in atTop, C.poisson.loss n ≤ exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop, C.zeroModeInputs.loss n ≤ exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop, C.thinInputs.loss n ≤ exp (-(2 : ℝ) * scale n)) :=
  ⟨C.poisson.slot_le, C.zeroMode.slot_le, C.thin.slot_le⟩

/-- The L19.4 slot bound of the assembled ledger. -/
theorem slots_poisson (rest : C5LossSlots) :
    ∀ᶠ n : ℕ in atTop,
      C.toL19Inputs.slots rest .poissonQuotient n ≤ exp (-(2 : ℝ) * scale n) :=
  C.toL19Inputs.slots_poisson rest

/-- The L19.5 slot bound of the assembled ledger. -/
theorem slots_zeroMode (rest : C5LossSlots) :
    ∀ᶠ n : ℕ in atTop,
      C.toL19Inputs.slots rest .idealZeroMode n ≤ exp (-(2 : ℝ) * scale n) :=
  C.toL19Inputs.slots_zeroMode rest

/-- The L19.6 slot bound of the assembled ledger. -/
theorem slots_thin (rest : C5LossSlots) :
    ∀ᶠ n : ℕ in atTop,
      C.toL19Inputs.slots rest .thinPairs n ≤ exp (-(2 : ℝ) * scale n) :=
  C.toL19Inputs.slots_thin rest

end L19FullCertificate

/-! ## Axiom audit -/

#print axioms L19FullCertificate.poissonEnergy
#print axioms L19FullCertificate.poisson
#print axioms L19FullCertificate.poisson_loss_eq
#print axioms L19FullCertificate.poisson_identity
#print axioms L19FullCertificate.poisson_sigma_narrow
#print axioms L19FullCertificate.poisson_eventually_abs_A_le_half
#print axioms L19FullCertificate.zeroModeInputs
#print axioms L19FullCertificate.thinInputs
#print axioms L19FullCertificate.thinInputs_W
#print axioms L19FullCertificate.toL19Inputs
#print axioms L19FullCertificate.toL19Inputs_W
#print axioms L19FullCertificate.leaves
#print axioms L19FullCertificate.leaves_l19_4
#print axioms L19FullCertificate.leaves_l19_5
#print axioms L19FullCertificate.leaves_l19_6
#print axioms L19FullCertificate.leaves_paper
#print axioms L19FullCertificate.leaves_slot
#print axioms L19FullCertificate.slots_bounds
#print axioms L19FullCertificate.slots_bounds_loss
#print axioms L19FullCertificate.slots_poisson
#print axioms L19FullCertificate.slots_zeroMode
#print axioms L19FullCertificate.slots_thin

end Cogentic.RandomizedL19Full
