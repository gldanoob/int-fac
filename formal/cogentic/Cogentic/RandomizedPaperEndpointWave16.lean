import Cogentic.RandomizedPaperEndpointWave15
import Cogentic.RandomizedL21_2ReferenceBound
import Cogentic.RandomizedL21_2StripBound

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-!
# Wave 16: the paper endpoint with the L21.2 reference Perron and contour
remainders discharged

`Cogentic.RandomizedPaperEndpointWave15.Wave15Inputs` still contains the whole
assembled L21.2 data record `L21_2LeafData`.  Two of that record's analytic
fields are not really independent inputs any more:

* `referencePerron : ReferencePerronBound X c Kref (Cper - 1)` is proved
  unconditionally by
  `Cogentic.RandomizedL21_2ReferenceBound.referencePerronBound` (the truncated
  Perron formula holds at every height `T ≥ 1`, so the `T = X^3 + 1` regime of
  L21.2 needs no side condition);
* `horizontalRemainder : HorizontalRemainderBound X c Kcont (Cper - 1)` is
  proved from the Riemann hypothesis alone by the pole-free strip route of
  `Cogentic.RandomizedL21_2StripBound`: `stripZetaBoundOffPole_of_RH` gives the
  `ζ'/ζ` bound on the part of the strip that the contour visits,
  `contourRemainderBound_of_stripOffPole` turns it into the contour remainder,
  and the exact contour identity converts that into the horizontal estimate.

This file isolates a new L21.2 record `Wave16L21_2Inputs` in which

* the reference-Perron constant is the *explicit* constant
  `wave16Kref X n = refConstant wave16Cper X n` obtained from the
  unconditional theorem, so no reference-Perron hypothesis remains;
* the horizontal constant is `fun _ => (3 * exp 1 / π) * stripK`, so no
  horizontal/contour hypothesis remains;
* every other `L21_2LeafData` field is kept verbatim.

The only remaining adapter is the numerical comparison

```
wave16Kref X n + (3 * exp 1 / π) * stripK + Ktail n
  ≤ (Kline / π) * (1 + log (X n ^ 3 / perronRe)),
```

which is exactly the `Ksum_le` field of `L21_2LeafData` after substituting the
two proved constants.  It is the smallest explicit adapter that the assembled
record still needs, because the line-bound constant `Kline` is a single real
number while the explicit reference constant of
`RandomizedL21_2ReferenceBound` grows with `X n`.  The reduction
`Wave16L21_2Inputs.toL21_2LeafData` proves it.

The wave-16 inputs `Wave16Inputs` are `Wave15Inputs` with the L21.2 field
replaced by `Wave16L21_2Inputs`; all other fields are unchanged.  The file
proves

* `Wave16L21_2Inputs.toL21_2LeafData` : the assembled L21.2 record from the
  reduced data;
* `Wave16Inputs.toWave15Inputs` : the wave-15 inputs;
* `Wave16Inputs.toFullyDischargedInputs` : the fully discharged inputs;
* `serialized_assembled_balancedEnvelopeInfimum_from_wave16Inputs` : the
  endpoint.

No loss, count, mass or error is set to zero, and no `sorry`, `admit`, `axiom`
or `native_decide` is used.
-/

namespace Cogentic.RandomizedPaperEndpointWave16

open Cogentic.Randomized
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedC5Algebra
open Cogentic.RandomizedC5Coupling
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedC5GoodIff
open Cogentic.RandomizedC5HitMassFinish
open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL18_4ThinFinish
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL19Poisson
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Thin
open Cogentic.RandomizedL19ZeroMode
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Abel
open Cogentic.RandomizedL21_2Density
open Cogentic.RandomizedL21_2Fourier
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2ReferenceBound
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2StripBound
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL4
open Cogentic.RandomizedL4BitBudget
open Cogentic.RandomizedL4Bands
open Cogentic.RandomizedL4Sub
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real
open scoped BigOperators ENNReal

set_option warn.classDefReducibility false

universe u

/-! ## The explicit reference-Perron constant -/

/-- The absolute truncated-Perron constant extracted from
`truncatedPerron_vonMangoldt_twist`.  Its defining property is
`wave16TruncatedPerronBound`. -/
noncomputable def wave16Cper : ℝ :=
  Classical.choose truncatedPerron_vonMangoldt_twist

/-- The extracted truncated-Perron constant is positive. -/
theorem wave16Cper_pos : 0 < wave16Cper :=
  (Classical.choose_spec truncatedPerron_vonMangoldt_twist).1

/-- **The unconditional truncated-Perron estimate** at the extracted constant. -/
theorem wave16TruncatedPerronBound : TruncatedPerronErrorBound wave16Cper :=
  (Classical.choose_spec truncatedPerron_vonMangoldt_twist).2

/-- The explicit reference-Perron constant of the unconditional theorem. -/
noncomputable def wave16Kref (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  refConstant wave16Cper X n

/-- The explicit reference constant is nonnegative on the L21.2 bands. -/
theorem wave16Kref_nonneg {X : ℕ → ℝ} {n : ℕ} (hX : 1 < X n) :
    0 ≤ wave16Kref X n := by
  unfold wave16Kref refConstant
  have hC : 0 < 2 * wave16Cper + 2 := by linarith [wave16Cper_pos]
  have hX' : 0 < X n + 1 := by linarith
  have hU : 0 < (bandLog X n) ^ 2 + 1 := by nlinarith [sq_nonneg (bandLog X n)]
  exact mul_nonneg (mul_nonneg hC.le hX'.le) hU.le

/-! ## The off-pole strip route -/

/-- **The pole-free strip bound at any exponent `C ≥ 1`.**  The proved bound has
exponent `1`; since `bandLog X n ≥ 3 ≥ 1`, it can be weakened to any larger
exponent, which is what the assembled record's `Cper - 1` needs. -/
theorem stripZetaBoundOffPole_of_RH_exponent {X : ℕ → ℝ} {C : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n)
    (hRH : RiemannZetaZerosOnLine) (hC : 1 ≤ C) :
    StripZetaBoundOffPole X (fun _ => stripK) C := by
  have h1 := stripZetaBoundOffPole_of_RH hX hU hRH
  filter_upwards [h1] with n hn
  intro s hre1 hre2 him1 him2
  have hL1 : 1 ≤ bandLog X n := le_trans (by norm_num) (hU n)
  calc
    ‖logDeriv riemannZeta s‖ ≤ stripK * (bandLog X n) ^ (1 : ℝ) :=
      hn s hre1 hre2 him1 him2
    _ = stripK * bandLog X n := by rw [Real.rpow_one]
    _ ≤ stripK * (bandLog X n) ^ C :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hL1 hC) stripK_nonneg

/-- **The horizontal estimate from the contour remainder.**  On the L21.2 range
`|t| ≤ X^3 < X^3 + 1` the exact contour identity
`zetaShiftContourIdentity` identifies the horizontal remainder with the contour
remainder, so `ContourRemainderBound` gives `HorizontalRemainderBound` with the
same constant and exponent. -/
theorem horizontalRemainderBound_of_contourRemainder
    {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ} {C : ℝ}
    (hX : ∀ n, 1 < X n) (hRH : RiemannZetaZerosOnLine)
    (h : ContourRemainderBound X c K C) :
    HorizontalRemainderBound X c K C := by
  filter_upwards [h] with n hn
  intro v t hv hvB ht
  have hv1 : 1 < v := lt_of_lt_of_le one_lt_two hv
  have hXpos : 0 < X n := lt_trans zero_lt_one (hX n)
  have h3nonneg : 0 ≤ X n ^ 3 := pow_nonneg hXpos.le 3
  have hT : 0 < X n ^ 3 + 1 := by linarith
  have ht' : |t| < X n ^ 3 + 1 := by linarith
  have hid := zetaShiftContourIdentity (v := v) (t := t) (T := X n ^ 3 + 1)
    hv1 hT ht' (stripNoZeros_of_RH hRH)
  have hnorm : ‖horizRemainder v t (X n ^ 3 + 1)‖ =
      ‖refZetaSum v t (X n ^ 3 + 1) - verticalZetaSum v t (X n ^ 3 + 1) -
        twistedMain v t‖ := by
    simp only [hid]
  rw [hnorm]
  exact hn v t hv hvB ht

/-! ## The reduced L21.2 record -/

/-- **The wave-16 L21.2 data.**  It is `L21_2LeafData` with the reference-Perron
and horizontal-remainder hypotheses removed.  The reference constant is the
explicit `wave16Kref` of the unconditional theorem and the horizontal constant
is `(3 e / π) * stripK` of the off-pole strip bound.  The single numerical
adapter `Ksum_le` is exactly the comparison that the assembled record needs. -/
structure Wave16L21_2Inputs where
  /-- The finite Fourier/tent discrepancy profile. -/
  profile : TentProfile
  /-- The stage-one constant `c`. -/
  c : ℝ
  /-- The final Perron exponent.  The line bound is taken at `Cper - 1`. -/
  Cper : ℝ
  /-- The absolute vertical-line constant. -/
  Kline : ℝ
  /-- Vertical-tail constant. -/
  Ktail : ℕ → ℝ
  /-- The centre sequence of the short-interval count. -/
  p : ℕ → ℝ
  X_gt_one : ∀ n, 1 < profile.X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3`. -/
  U_ge_three : ∀ n, 3 ≤ bandLog profile.X n
  /-- `Cper ≥ 3`. -/
  Cper_ge_three : 3 ≤ Cper
  Kline_nonneg : 0 ≤ Kline
  Ktail_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Ktail n
  /-- **The numerical adapter.**  The explicit reference constant of
  `referencePerronBound` plus the off-pole horizontal constant plus the vertical
  tail fit under the line-bound constant.  This is the `Ksum_le` field of
  `L21_2LeafData` at the two proved constants. -/
  Ksum_le : ∀ᶠ n : ℕ in atTop,
    wave16Kref profile.X n + (3 * Real.exp 1 / Real.pi) * stripK + Ktail n ≤
      (Kline / Real.pi) * (1 + Real.log (profile.X n ^ 3 / perronRe))
  /-- The Riemann hypothesis for `ζ`, used by the off-pole strip route. -/
  hRH : RiemannZetaZerosOnLine
  /-- The standard `ζ'/ζ` line bound at `Re s = 2/3`. -/
  lineBound : VerticalLineBound profile.X (fun _ => Kline) (Cper - 1)
  /-- The vertical-tail estimate. -/
  verticalTail : VerticalTailBound profile.X Ktail (Cper - 1)
  /-- The centre is eventually larger than one. -/
  p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < p n
  /-- The literal short-interval smooth count. -/
  localCount : ShortIntervalSmoothCountLower p c profile.X
  /-- `b ≤ B`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf profile.X c n ≤ logCutoff c profile.X n
  /-- `e^a ≥ 2`. -/
  a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf profile.X c n
  /-- Low-frequency energy bound. -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.lowEnergy n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n)
  /-- Middle-frequency energy bound. -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.middleEnergy n ≤ Real.exp (-((1 / c) - δ) * paperRate profile.X n)
  /-- High-frequency energy bound. -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n)
  /-- Two-scale separation. -/
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog profile.X n
  /-- `log X ≤ exp (scale n)`. -/
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog profile.X n ≤ Real.exp (scale n)

namespace Wave16L21_2Inputs

/-- The horizontal constant produced by the off-pole strip bound. -/
noncomputable def wave16Kcont : ℕ → ℝ :=
  fun _ => (3 * Real.exp 1 / Real.pi) * stripK

variable (D : Wave16L21_2Inputs)

/-- **The assembled L21.2 record.**  The reference-Perron field is
`referencePerronBound_of_errorBound` at the extracted constant `wave16Cper`; the
horizontal field is
`horizontalRemainderBound_of_contourRemainder` applied to
`contourRemainderBound_of_stripOffPole` at the pole-free strip bound; all other
fields are passed through. -/
noncomputable def toL21_2LeafData : L21_2LeafData where
  profile := D.profile
  c := D.c
  Cper := D.Cper
  Kline := D.Kline
  Kref := refConstant wave16Cper D.profile.X
  Kcont := wave16Kcont
  Ktail := D.Ktail
  p := D.p
  X_gt_one := D.X_gt_one
  c_pos := D.c_pos
  c_le_one := D.c_le_one
  U_ge_three := D.U_ge_three
  Cper_ge_three := D.Cper_ge_three
  Kline_nonneg := D.Kline_nonneg
  Kref_nonneg := Eventually.of_forall fun n => wave16Kref_nonneg (D.X_gt_one n)
  Kcont_nonneg := Eventually.of_forall fun _ => by
    unfold wave16Kcont
    exact mul_nonneg (by positivity) stripK_nonneg
  Ktail_nonneg := D.Ktail_nonneg
  Ksum_le := D.Ksum_le
  hRH := D.hRH
  lineBound := D.lineBound
  referencePerron := by
    have h := referencePerronBound_of_errorBound (X := D.profile.X) (c := D.c)
      wave16TruncatedPerronBound wave16Cper_pos.le D.X_gt_one D.U_ge_three
      D.c_le_one
    exact h
  horizontalRemainder :=
    horizontalRemainderBound_of_contourRemainder D.X_gt_one D.hRH
      (contourRemainderBound_of_stripOffPole D.hRH
        (stripZetaBoundOffPole_of_RH_exponent D.X_gt_one D.U_ge_three D.hRH
          (by linarith [D.Cper_ge_three]))
        D.X_gt_one (fun _ => stripK_nonneg)
        (Eventually.of_forall fun _ => le_rfl))
  verticalTail := D.verticalTail
  p_gt_one := D.p_gt_one
  localCount := D.localCount
  b_le_B := D.b_le_B
  a_ge_log_two := D.a_ge_log_two
  fourierLow := D.fourierLow
  fourierMiddle := D.fourierMiddle
  fourierTail := D.fourierTail
  U_dominates := D.U_dominates
  U_le_exp := D.U_le_exp

/-- The reference-Perron field of the assembled record is the unconditional
bound. -/
theorem toL21_2LeafData_referencePerron :
    ReferencePerronBound D.profile.X D.c (wave16Kref D.profile.X) (D.Cper - 1) :=
  D.toL21_2LeafData.referencePerron

/-- The horizontal field of the assembled record is the off-pole strip bound. -/
theorem toL21_2LeafData_horizontalRemainder :
    HorizontalRemainderBound D.profile.X D.c wave16Kcont (D.Cper - 1) :=
  D.toL21_2LeafData.horizontalRemainder

end Wave16L21_2Inputs

/-! ## The wave-16 inputs -/

/-- The C5 ledger of the wave-16 inputs: the wave-15 ledger with the L21.2
record read from the reduced `Wave16L21_2Inputs`. -/
noncomputable def wave16Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : Wave16L21_2Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (l4N l4Bits : ℕ) (l4N_odd : Odd l4N) (l4Bits_budget : 2 ^ l4Bits ≤ l4N)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave15Slots l18_4 l19 l20_2 l20_4 l21_2.toL21_2LeafData l27_data l27_finish
    l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1

/-- **The wave-16 ledger is the wave-15 ledger at the assembled L21.2 record.** -/
theorem wave16Slots_eq
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : Wave16L21_2Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (l4N l4Bits : ℕ) (l4N_odd : Odd l4N) (l4Bits_budget : 2 ^ l4Bits ≤ l4N)
    (p1 : SubexpPrepassInput) :
    wave16Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish l30 l34
        l4N l4Bits l4N_odd l4Bits_budget p1 =
      wave15Slots l18_4 l19 l20_2 l20_4 l21_2.toL21_2LeafData l27_data
        l27_finish l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1 :=
  rfl

/-- **The wave-16 inputs.**  They are the wave-15 inputs with the assembled
L21.2 record replaced by the reduced `Wave16L21_2Inputs`, whose reference-Perron
and horizontal-remainder fields are proved rather than assumed.  Every other
field is passed through unchanged. -/
structure Wave16Inputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate, with the L19.6 thin slot built from
  `ThinLatticeData`. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- L21.2: RH smooth numbers near integer centres, with the reference-Perron
  and horizontal-remainder fields discharged. -/
  l21_2 : Wave16L21_2Inputs
  /-- The odd modulus of the L4 split-band realization. -/
  l4N : ℕ
  /-- The explicit bit budget of the L4 band. -/
  l4Bits : ℕ
  /-- The L4 modulus is odd. -/
  l4N_odd : Odd l4N
  /-- **The L4 bit budget**: the budgeted band is inside the modulus. -/
  l4Bits_budget : 2 ^ l4Bits ≤ l4N
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- L30: the sourced counts and the H.3 failure data. -/
  l30 : Wave14L30Inputs
  /-- L34: the explicit Chebotarev-side counting inputs. -/
  l34 : L34ChebotarevSidesInputs
  /-- P1: the explicit `exp (o(H))`-cost prepass. -/
  p1 : SubexpPrepassInput
  /-- C1: the public congruence check (L1). -/
  c1 : C1Inputs E
  /-- C2: conditional hidden-sign uniformity (L2–L5, including L4). -/
  c2 : C2Inputs E
  /-- C3: the ideal/actual total-variation budget (L6–L10). -/
  c3 : C3Inputs E
  /-- C4: the expected public-work budget (L11–L16). -/
  c4 : C4Inputs E D
  /-- The concrete epoch family underlying the C5 certificate. -/
  concrete : ∀ n, 3 ≤ n → ConcreteEpochData n
  /-- Adapter: the ambient epoch is the concrete family's `toHardEpochData`. -/
  concrete_eq : ∀ n (hN : 3 ≤ n), E n hN = (concrete n hN).toHardEpochData
  /-- **The C5 data assembled by `c5FullOfCount`.** -/
  c5Data : Wave15C5Data concrete
  /-- Adapter: the concrete C5 loss is dominated by the wave-16 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave16Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish
        l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1).total n

namespace Wave16Inputs

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The wave-15 inputs from the wave-16 inputs.**  Only the L21.2 record
changes: its two discharged analytic fields are supplied by
`Wave16L21_2Inputs.toL21_2LeafData`. -/
noncomputable def toWave15Inputs (I : Wave16Inputs E D) : Wave15Inputs E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21_2 := I.l21_2.toL21_2LeafData
  l4N := I.l4N
  l4Bits := I.l4Bits
  l4N_odd := I.l4N_odd
  l4Bits_budget := I.l4Bits_budget
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
  l34 := I.l34
  p1 := I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5Data := I.c5Data
  loss_le := by
    intro n hN
    simpa only [wave16Slots] using I.loss_le n hN

/-- **The wave-16 ledger is the wave-15 ledger of the reduction.** -/
theorem toWave15Inputs_slots (I : Wave16Inputs E D) :
    I.toWave15Inputs.toFullyDischargedInputs.toPaperAnalyticAssumptions.slots =
      wave16Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_finish I.l30 I.l34 I.l4N I.l4Bits I.l4N_odd I.l4Bits_budget I.p1 := by
  rw [Wave15Inputs.toFullyDischargedInputs_slots]
  rfl

/-- **The fully discharged inputs from the wave-16 inputs.** -/
noncomputable def toFullyDischargedInputs (I : Wave16Inputs E D) :
    FullyDischargedInputs E D :=
  I.toWave15Inputs.toFullyDischargedInputs

/-- **The paper endpoint inputs from the wave-16 inputs.** -/
noncomputable def toPaperEndpointInputs (I : Wave16Inputs E D) :
    PaperEndpointInputs E D :=
  I.toFullyDischargedInputs.toPaperEndpointInputs

/-- The paper record produced by the wave-16 inputs has the wave-16 ledger. -/
theorem toPaperEndpointInputs_paper_slots (I : Wave16Inputs E D) :
    I.toPaperEndpointInputs.paper.slots =
      wave16Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_finish I.l30 I.l34 I.l4N I.l4Bits I.l4N_odd I.l4Bits_budget I.p1 :=
  I.toWave15Inputs_slots

end Wave16Inputs

/-! ## The endpoint -/

/-- **Wave-16 paper endpoint.**  Under the critical-line hypothesis for
Dirichlet L-functions, there is one universal serialized factoring algorithm
such that, for every balanced-schedule epoch family which, at every valid
ceiling, carries

* the full L18.4 certificate,
* the L19 certificate with its thin slot built from `ThinLatticeData`,
* the L20.2 paper-mass concentration source,
* the sourced L20.4 disjunction-event data,
* the reduced L21.2 data, with the reference-Perron bound and the horizontal
  contour remainder proved from `RiemannZetaZerosOnLine` and the off-pole strip
  bound,
* the proved L4 bit-budget split-band realization (`Odd N`, `2 ^ bits ≤ N`),
* the L27.1 stage-one finish data,
* the explicit L30 short-interval count, global binomial lower bound and H.3
  failure data,
* the L34 explicit Chebotarev-side counting inputs,
* P1 with an explicit `exp (o(H))` cost rate,
* C1–C4, and
* the C5 certificate assembled by `c5FullOfCount`,

the kernel-checked driver always outputs a permutation of `n.primeFactorsList`
and has expected serialized bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`, where
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof applies
`serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs` to
`Wave16Inputs.toFullyDischargedInputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave16Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        Wave16Inputs (E s) D) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ :=
    serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toFullyDischargedInputs⟩

/-! ## Axiom audit -/

#print axioms wave16Cper
#print axioms wave16Cper_pos
#print axioms wave16TruncatedPerronBound
#print axioms wave16Kref
#print axioms wave16Kref_nonneg
#print axioms stripZetaBoundOffPole_of_RH_exponent
#print axioms horizontalRemainderBound_of_contourRemainder
#print axioms Wave16L21_2Inputs.wave16Kcont
#print axioms Wave16L21_2Inputs.toL21_2LeafData
#print axioms Wave16L21_2Inputs.toL21_2LeafData_referencePerron
#print axioms Wave16L21_2Inputs.toL21_2LeafData_horizontalRemainder
#print axioms wave16Slots
#print axioms wave16Slots_eq
#print axioms Wave16Inputs.toWave15Inputs
#print axioms Wave16Inputs.toWave15Inputs_slots
#print axioms Wave16Inputs.toFullyDischargedInputs
#print axioms Wave16Inputs.toPaperEndpointInputs
#print axioms Wave16Inputs.toPaperEndpointInputs_paper_slots
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave16Inputs

end Cogentic.RandomizedPaperEndpointWave16
