import Cogentic.RandomizedL20_4Conditioned
import Cogentic.RandomizedL20_2
import Cogentic.RandomizedL19SecondMoment

/-!
# L20.4 interior: sourcing the base and rational concentration fields

`Cogentic.RandomizedL20_4Conditioned.InteriorSubProps` isolates the four
`D^{-B}` inputs of the G.11/G.12 interior step:

* `base_subexp` — the G.11 internal base mass `δ_L` (pool-note item 2);
* `eta_subexp` — the L21.2 elliptic deletion fraction;
* `epsRat_subexp` — the G.11 rational error `ε_rat`;
* `epsIn_subexp` — the G.12 incoming exceptional mass.

The elliptic field is already discharged from `RandomizedL21_2`
(`subexpLoss_of_L21_2`).  This file reduces the remaining fields to the
existing L20.2 interior-concentration analysis, i.e. to the smooth-number
concentration estimate and the explicit CRT/smooth-character exception budget.

## The explicit sub-`Prop`s

There are only three source statements, each a single eventual inequality:

1. **Base.**  The G.11 base mass is bounded by the L20.2 normalized interior
   discrepancy (`BaseFromConcentration`):
   `interior n L ≤ I.loss n`.
2. **Rational and incoming exceptions.**  The G.11 rational error and the G.12
   incoming exception are bounded by the L20.2 CRT plus smooth-character budget
   `I.ρ n = I.crtError n + I.charError n` (`RationalFromExceptions` and
   `IncomingFromExceptions`).
3. **Elliptic.**  The elliptic fraction is the L21.2 exceptional fraction
   (`EllipticFromL21_2`): `eta n = I₂₁.loss n`.

No inequality is identified with zero, and no term is dropped.  The two L20.2
sources are genuine existing estimates:

* `L20_2Inputs.loss_le_paper` bounds `I.loss` by
  `exp (-2 * D^{1/48} * log D)`, which is `D^{-B}` for every `B`
  (`loss_subexp_of_L20_2`);
* `TruncatedGeometricCRTLaw` and `SmoothCharacterSumBound` bound `I.crtError`
  and `I.charError` by `exp (-c * D * log D)`, so `I.ρ` is `D^{-B}` for every
  `B` (`rho_subexp_of_L20_2`).

The resulting structure `InteriorSourceData` therefore proves
`InteriorSubProps` without any new analytic `Prop` beyond the three source
inequalities above.  `TopInteriorData` adds the remaining (already explicit)
G.11/G.12 recurrence and comparison fields and proves the reduction to
`TopConditionedData`, hence to `TopData` and to the G.12 top `SubexpLoss`.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss.
-/

namespace Cogentic.RandomizedL20_4Interior

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub
open Cogentic.RandomizedL20_4Conditioned

/-! ## 1. The L20.2 concentration loss is subexponential -/

/-- The exponent `exp (-c * D * log D)` with `D = exp (scale n)` is a
`SubexpLoss` for every `c > 0`.  Indeed `c * exp (scale n)` eventually beats any
fixed `B`, and `scale n ≥ 0`, so `B * scale n ≤ c * exp (scale n) * scale n`. -/
theorem subexpLoss_exp_neg_paperD {c : ℝ} (hc : 0 < c) :
    SubexpLoss
      (fun n : ℕ => Real.exp (-c * Cogentic.RandomizedL20_2.paperD n * scale n)) := by
  intro B hB
  have hexp : Tendsto (fun n : ℕ => Real.exp (scale n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp scale_grows
  have hBc : 0 < B / c := div_pos hB hc
  have hbig : ∀ᶠ n : ℕ in atTop, B / c ≤ Real.exp (scale n) :=
    hexp.eventually_ge_atTop (B / c)
  filter_upwards [hbig, scale_grows.eventually_ge_atTop 0] with n hbig' hH
  apply Real.exp_le_exp.mpr
  have hB_le : B ≤ c * Real.exp (scale n) := by
    calc B ≤ Real.exp (scale n) * c := (div_le_iff₀ hc).mp hbig'
      _ = c * Real.exp (scale n) := mul_comm _ _
  have hneg : -c * Real.exp (scale n) ≤ -B := by linarith
  have hmul := mul_le_mul_of_nonneg_right hneg hH
  simpa [Cogentic.RandomizedL20_2.paperD, mul_assoc] using hmul

/-- The L20.2 normalized interior discrepancy is a `SubexpLoss`.  The paper
bound is `exp (-2 * D^{1/48} * log D)`, and `D^{1/48} = exp ((1/48) log D)`
dominates every fixed constant. -/
theorem loss_subexp_of_L20_2 (I : Cogentic.RandomizedL20_2.L20_2Inputs) :
    SubexpLoss I.loss := by
  intro B hB
  have hexp : Tendsto (fun n : ℕ => Real.exp (I.a * scale n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (scale_grows.const_mul_atTop I.a_pos)
  have hhalf : ∀ᶠ n : ℕ in atTop, B / 2 ≤ Real.exp (I.a * scale n) :=
    hexp.eventually_ge_atTop (B / 2)
  have hbig : ∀ᶠ n : ℕ in atTop, B ≤ 2 * Real.exp (I.a * scale n) := by
    filter_upwards [hhalf] with n hn
    linarith
  filter_upwards [I.loss_le_paper, hbig, scale_grows.eventually_ge_atTop 0]
    with n hloss hlarge hH
  refine hloss.trans (Real.exp_le_exp.mpr ?_)
  have hA : I.A n = Real.exp (I.a * scale n) := by
    simp [Cogentic.RandomizedL20_2.L20_2Inputs.A, Cogentic.RandomizedL20_2.paperA]
  have hneg : -2 * I.A n ≤ -B := by
    rw [hA]
    linarith
  simpa using mul_le_mul_of_nonneg_right hneg hH

/-- The L20.2 CRT error is a `SubexpLoss` (the truncated geometric CRT law). -/
theorem crtError_subexp_of_L20_2 (I : Cogentic.RandomizedL20_2.L20_2Inputs) :
    SubexpLoss I.crtError := by
  refine subexpLoss_of_eventually_le ?_ (subexpLoss_exp_neg_paperD I.crt_law.1)
  exact Eventually.of_forall fun n => (I.crt_law.2 n).2

/-- The L20.2 smooth-character error is a `SubexpLoss` (Lemma G.2). -/
theorem charError_subexp_of_L20_2 (I : Cogentic.RandomizedL20_2.L20_2Inputs) :
    SubexpLoss I.charError := by
  refine subexpLoss_of_eventually_le ?_ (subexpLoss_exp_neg_paperD I.char_sum.1)
  exact Eventually.of_forall fun n => (I.char_sum.2 n).2

/-- The L20.2 CRT plus smooth-character budget `ρ = crtError + charError` is a
`SubexpLoss`.  This is the rational/exception budget of the G.11/G.12 step. -/
theorem rho_subexp_of_L20_2 (I : Cogentic.RandomizedL20_2.L20_2Inputs) :
    SubexpLoss I.ρ := by
  have h : SubexpLoss (fun n => I.crtError n + I.charError n) :=
    subexpLoss_add (crtError_subexp_of_L20_2 I) (charError_subexp_of_L20_2 I)
  exact h

/-! ## 2. The smallest explicit analytic source `Prop`s -/

/-- The G.11 internal base mass is bounded by the L20.2 normalized interior
concentration loss.  This is the smooth-number side of the interior estimate. -/
def BaseFromConcentration (interior : ℕ → ℕ → ℝ) (L : ℕ)
    (I : Cogentic.RandomizedL20_2.L20_2Inputs) : Prop :=
  ∀ᶠ n : ℕ in atTop, interior n L ≤ I.loss n

/-- The G.11 rational error `ε_rat` is bounded by the L20.2 CRT plus
smooth-character budget.  This is the character/exception side of the interior
estimate. -/
def RationalFromExceptions (epsRat : ℕ → ℝ)
    (I : Cogentic.RandomizedL20_2.L20_2Inputs) : Prop :=
  ∀ᶠ n : ℕ in atTop, epsRat n ≤ I.ρ n

/-- The G.12 incoming exceptional mass is bounded by the same L20.2 CRT plus
smooth-character budget. -/
def IncomingFromExceptions (epsIn : ℕ → ℝ)
    (I : Cogentic.RandomizedL20_2.L20_2Inputs) : Prop :=
  ∀ᶠ n : ℕ in atTop, epsIn n ≤ I.ρ n

/-- The elliptic deletion fraction is exactly the L21.2 exceptional fraction. -/
def EllipticFromL21_2 (eta : ℕ → ℝ)
    (I : Cogentic.RandomizedL21_2.L21_2Inputs) : Prop :=
  ∀ n : ℕ, eta n = I.loss n

/-! ## 3. Sourcing `InteriorSubProps` -/

/-- The interior source data: one L20.2 input for the base mass, one L20.2 input
for the rational/exception budget, one L21.2 input for the elliptic fraction, and
the explicit source inequalities.  The incoming exceptional mass is retained as
an explicit `SubexpLoss`; it can also be sourced from the rational budget by
`subProps_of_incoming`. -/
structure InteriorSourceData (interior : ℕ → ℕ → ℝ) (L : ℕ)
    (eta epsRat epsIn : ℕ → ℝ) where
  /-- The L20.2 smooth-number concentration input controlling the base mass. -/
  base : Cogentic.RandomizedL20_2.L20_2Inputs
  /-- The base mass is bounded by the L20.2 interior loss. -/
  base_from : BaseFromConcentration interior L base
  /-- The L20.2 CRT/smooth-character input controlling the rational error. -/
  rational : Cogentic.RandomizedL20_2.L20_2Inputs
  /-- The rational error is bounded by the L20.2 CRT/character budget. -/
  rational_from : RationalFromExceptions epsRat rational
  /-- The L21.2 elliptic input. -/
  elliptic : Cogentic.RandomizedL21_2.L21_2Inputs
  /-- The elliptic fraction is the L21.2 exceptional fraction. -/
  elliptic_from : EllipticFromL21_2 eta elliptic
  /-- The incoming exceptional mass is a `D^{-B}` loss. -/
  epsIn_subexp : SubexpLoss epsIn

namespace InteriorSourceData

variable {interior : ℕ → ℕ → ℝ} {L : ℕ} {eta epsRat epsIn : ℕ → ℝ}

/-- The base field of `InteriorSubProps`. -/
theorem base_subexp (S : InteriorSourceData interior L eta epsRat epsIn) :
    SubexpLoss fun n => interior n L :=
  subexpLoss_of_eventually_le S.base_from (loss_subexp_of_L20_2 S.base)

/-- The elliptic field of `InteriorSubProps`, from L21.2. -/
theorem eta_subexp (S : InteriorSourceData interior L eta epsRat epsIn) :
    SubexpLoss eta := by
  intro B hB
  filter_upwards
    [Cogentic.RandomizedL20_4Conditioned.subexpLoss_of_L21_2 S.elliptic B hB]
    with n hn
  simpa [S.elliptic_from n] using hn

/-- The rational field of `InteriorSubProps`, from the L20.2 CRT/character
budget. -/
theorem epsRat_subexp (S : InteriorSourceData interior L eta epsRat epsIn) :
    SubexpLoss epsRat :=
  subexpLoss_of_eventually_le S.rational_from (rho_subexp_of_L20_2 S.rational)

/-- **The four interior fields, sourced.**  Base and rational are reduced to the
L20.2 smooth/character estimates, the elliptic field to L21.2, and the incoming
exception is the explicit `SubexpLoss` field. -/
theorem subProps (S : InteriorSourceData interior L eta epsRat epsIn) :
    InteriorSubProps interior L eta epsRat epsIn where
  base_subexp := S.base_subexp
  eta_subexp := S.eta_subexp
  epsRat_subexp := S.epsRat_subexp
  epsIn_subexp := S.epsIn_subexp

/-- If the incoming exceptional mass is also controlled by the L20.2 rational
budget, then the explicit `SubexpLoss` hypothesis for it is unnecessary. -/
theorem subProps_of_incoming (S : InteriorSourceData interior L eta epsRat epsIn)
    (incoming : Cogentic.RandomizedL20_2.L20_2Inputs)
    (hin : IncomingFromExceptions epsIn incoming) :
    InteriorSubProps interior L eta epsRat epsIn where
  base_subexp := S.base_subexp
  eta_subexp := S.eta_subexp
  epsRat_subexp := S.epsRat_subexp
  epsIn_subexp := subexpLoss_of_eventually_le hin (rho_subexp_of_L20_2 incoming)

end InteriorSourceData

/-! ## 4. The reduced top bundle -/

/-- The G.11/G.12 top data with the interior concentration replaced by the
explicit source data of §3.  All remaining fields are the already-explicit
recurrence, depth and G.12 comparison inputs of `TopConditionedData`. -/
structure TopInteriorData where
  /-- Depth of the internal G.11 recurrence. -/
  L : ℕ
  /-- Internal normalized bad-child masses `δ_i`. -/
  interior : ℕ → ℕ → ℝ
  /-- G.11 step multiplier. -/
  step : ℕ → ℝ
  /-- Elliptic deletion fraction `η`. -/
  eta : ℕ → ℝ
  /-- G.11 rational error `ε_rat`. -/
  epsRat : ℕ → ℝ
  /-- G.12 incoming exceptional mass. -/
  epsIn : ℕ → ℝ
  /-- Resulting top bad-child mass. -/
  top : ℕ → ℝ
  /-- G.12 top constant. -/
  Ctop : ℕ → ℝ
  /-- Exponent of the top constant. -/
  cTop : ℝ
  /-- Exponent of the depth factor. -/
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  epsRat_nonneg : ∀ n, 0 ≤ epsRat n
  epsIn_nonneg : ∀ n, 0 ≤ epsIn n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  recurrence : G11InteriorRecurrence interior L step eta epsRat
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  comparison : TopG12Comparison top Ctop interior epsIn eta
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)
  /-- The sourced interior concentration fields. -/
  sources : InteriorSourceData interior L eta epsRat epsIn

namespace TopInteriorData

/-- The sourced interior fields realize `InteriorSubProps`. -/
theorem concentration (S : TopInteriorData) :
    InteriorSubProps S.interior S.L S.eta S.epsRat S.epsIn :=
  S.sources.subProps

/-- **The reduction to `TopConditionedData`.**  The sourced interior
concentration replaces the four raw `SubexpLoss` fields; every other field is
unchanged. -/
noncomputable def toTopConditionedData (S : TopInteriorData) : TopConditionedData where
  L := S.L
  interior := S.interior
  step := S.step
  eta := S.eta
  epsRat := S.epsRat
  epsIn := S.epsIn
  top := S.top
  Ctop := S.Ctop
  cTop := S.cTop
  cInt := S.cInt
  interior_nonneg := S.interior_nonneg
  eta_nonneg := S.eta_nonneg
  epsRat_nonneg := S.epsRat_nonneg
  epsIn_nonneg := S.epsIn_nonneg
  top_nonneg := S.top_nonneg
  Ctop_nonneg := S.Ctop_nonneg
  cTop_nonneg := S.cTop_nonneg
  recurrence := S.recurrence
  step_ge_one := S.step_ge_one
  alpha_nonneg := S.alpha_nonneg
  depth_bound := S.depth_bound
  comparison := S.comparison
  Ctop_le := S.Ctop_le
  concentration := S.concentration

/-- The reduction passes through to the existing `TopData`. -/
noncomputable def toTopData (S : TopInteriorData) : TopData :=
  S.toTopConditionedData.toTopData

/-- **The G.12 top mass is subexponential**, now with the base and rational
interior fields sourced from the existing L20.2 estimates (and the elliptic
field from L21.2). -/
theorem top_subexp (S : TopInteriorData) : SubexpLoss S.top :=
  S.toTopData.loss_subexp

end TopInteriorData

/-! ## Axiom audit -/

#print axioms subexpLoss_exp_neg_paperD
#print axioms loss_subexp_of_L20_2
#print axioms crtError_subexp_of_L20_2
#print axioms charError_subexp_of_L20_2
#print axioms rho_subexp_of_L20_2
#print axioms InteriorSourceData.base_subexp
#print axioms InteriorSourceData.eta_subexp
#print axioms InteriorSourceData.epsRat_subexp
#print axioms InteriorSourceData.subProps
#print axioms InteriorSourceData.subProps_of_incoming
#print axioms TopInteriorData.concentration
#print axioms TopInteriorData.toTopConditionedData
#print axioms TopInteriorData.toTopData
#print axioms TopInteriorData.top_subexp

end Cogentic.RandomizedL20_4Interior
