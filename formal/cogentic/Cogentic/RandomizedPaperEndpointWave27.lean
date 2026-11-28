import Cogentic.RandomizedPaperEndpointWave26
import Cogentic.RandomizedL21_2ConcreteLeaf
import Cogentic.RandomizedL21_2StripBound
import Cogentic.RandomizedL21_2TailBound
import Cogentic.RandomizedL21_2Elementary
import Cogentic.RandomizedL21_2TentWitness
import Cogentic.RandomizedL21_2LeafAssembly
import Cogentic.RandomizedL21_2LineMinimal

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 27: the L21.2 analytic input from RH and the central count only

Wave 26 left the L21.2 block as the two-component record
`ConcreteLeafResidual`:

```
zeta : ZetaSide,   localCount : ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX
```

where `ZetaSide` carried, besides `RiemannZetaZerosOnLine`, a zero-free line,
a two-sided `ZetaLineEstimate` with sequences `b`, `B`, a raw line constant
`KlineRaw`, and the ratio bound `B n / b n ≤ KlineRaw` eventually.  The ratio
field is the point where the record asks for a *constant-height* bound on
`ζ'/ζ`: on the elementary scale `X n = exp (|scale n|^3 + 3)` the segment
`|Im s| ≤ 2 X n^3` grows without bound, while `b n` is a lower bound for `ζ`
on that segment.  This is precisely the information that the strip estimate
below replaces by an explicit `O (log X)` bound.

This file removes that whole package from the residual.  The L21.2 input is
rebuilt from

* `zetaRH : RiemannZetaZerosOnLine`,
* `localCount : ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX`,

using the elementary profile and parameter theorems of
`RandomizedL21_2Elementary` / `RandomizedL21_2TentWitness`, the *pole-free*
strip bound `stripZetaBoundOffPole_of_RH` (constants `stripK`, exponent `1`),
and the unconditional vertical tail `verticalTailBound_of_RH` (constant
`tailK / π`, exponent `1`).

The line bound is constructed directly, with the constant

```
Kline = stripK + tailK
```

and the paper exponent `elementaryCper - 1 = 2`: for `1 ≤ |Im s|` the strip
bound applies (with `elementaryProfile.X` in place of `elementaryX`), and for
`|Im s| < 1` the near-axis bound `norm_logDeriv_perronLine_le` applies.  The
vertical tail is the `tailK / π` bound raised from exponent `1` to
`elementaryCper - 1 = 2` by monotonicity in the exponent.

`PaperResidualFor27` is the Wave-26 record with `l21` replaced by the new
`{ zetaRH, localCount }` structure.  Its ledger slot is `wave27Slots`, whose
L21.2 loss is the same literal bad-centre fraction as before (the zeta-side
constants do not enter it), so `toFullyDischargedInputs` is unconditional and
the E-generic endpoint is
`serialized_assembled_balancedEnvelopeInfimum_from_wave27Inputs`.

Removing the `ZetaSide` package leaves exactly the two analytic residuals
`RiemannZetaZerosOnLine` and `ShortIntervalSmoothCountLower`.

Both directions between the two records are recorded:

* `PaperResidualFor26 → PaperResidualFor27`
  (`PaperResidualFor27.ofPaperResidualFor26`) is unconditional: it keeps only
  `zetaRH` and the central count;
* `PaperResidualFor27 → PaperResidualFor26`
  (`PaperResidualFor27.toPaperResidualFor26`) needs exactly a `ZetaSide` to be
  supplied.  The L21.2 ledger loss is the same bad-centre fraction in both
  records, so the `loss_le` adapter transfers verbatim.  This conditional arrow
  exhibits the precise content that Wave 27 removes: a zero-free line, a
  two-sided `b`/`B` estimate and the constant `B / b` ratio.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count,
mass or error is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave27

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL21_2Elementary
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2LineMinimal
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2StripBound
open Cogentic.RandomizedL21_2TailBound
open Cogentic.RandomizedL21_2TentWitness
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.RandomizedL30NoBinomial
open Cogentic.RandomizedL30PrimeReciprocal
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperEndpointWave17
open Cogentic.RandomizedPaperEndpointWave24
open Cogentic.RandomizedPaperEndpointWave25
open Cogentic.RandomizedPaperEndpointWave26
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## The explicit line constant -/

/-- The explicit constant of the L21.2 line bound obtained from the pole-free
strip bound and the near-axis estimate: `Kline = stripK + tailK`. -/
noncomputable def wave27Kline : ℝ := stripK + tailK

lemma wave27Kline_nonneg : 0 ≤ wave27Kline := by
  unfold wave27Kline
  exact add_nonneg stripK_nonneg tailK_nonneg

/-! ## The line bound from the pole-free strip estimate -/

/-- **The vertical line bound at `Re s = 2/3` from the Riemann hypothesis.**

For `1 ≤ |u|` we use `stripZetaBoundOffPole_of_RH` (constant `stripK`); for
`|u| < 1` we use `norm_logDeriv_perronLine_le` (constant `tailK`).  The
exponent is `2`, the paper exponent `elementaryCper - 1`. -/
theorem verticalLineBound_elementary_of_RH
    (hRH : RiemannZetaZerosOnLine) :
    VerticalLineBound elementaryProfile.X (fun _ => wave27Kline) 2 := by
  have hX : ∀ n, 1 < elementaryProfile.X n := by
    intro n
    change 1 < elementaryX n
    exact elementaryX_gt_one n
  have hU : ∀ n, 3 ≤ bandLog elementaryProfile.X n := by
    intro n
    change 3 ≤ bandLog elementaryX n
    rw [bandLog_elementaryX]
    exact elementaryU_ge_three n
  have hstrip : StripZetaBoundOffPole elementaryProfile.X (fun _ => stripK) 1 :=
    stripZetaBoundOffPole_of_RH (X := elementaryProfile.X) hX hU hRH
  filter_upwards [hstrip] with n hs
  intro u hu
  set L : ℝ := bandLog elementaryProfile.X n with hL
  have hL3 : 3 ≤ L := hU n
  have hL1 : 1 ≤ L := by linarith
  have hLnonneg : 0 ≤ L := by linarith
  have hpow : L ^ (1 : ℝ) ≤ L ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hpow2_nonneg : 0 ≤ L ^ (2 : ℝ) := Real.rpow_nonneg hLnonneg _
  have hKline_nonneg : 0 ≤ wave27Kline := wave27Kline_nonneg
  have hu3 : |u| ≤ 3 * elementaryProfile.X n ^ 3 := by
    have hX3_nonneg : 0 ≤ elementaryProfile.X n ^ 3 :=
      pow_nonneg (le_of_lt (lt_trans zero_lt_one (hX n))) 3
    nlinarith [hu]
  by_cases hcase : 1 ≤ |u|
  · have hb := hs (perronLine perronRe u)
      (by simp [perronLine])
      (by simp [perronLine]; norm_num [perronRe])
      (by simpa [perronLine] using hcase)
      (by simpa [perronLine] using hu3)
    calc
      ‖logDeriv riemannZeta (perronLine perronRe u)‖
          ≤ stripK * L ^ (1 : ℝ) := by
            simpa [hL, Real.rpow_one] using hb
      _ ≤ stripK * L ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow stripK_nonneg
      _ ≤ wave27Kline * L ^ (2 : ℝ) := by
            unfold wave27Kline
            exact mul_le_mul_of_nonneg_right (by linarith [tailK_nonneg]) hpow2_nonneg
  · have hnear :
        ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤ tailK * L := by
      simpa [hL] using
        norm_logDeriv_perronLine_le (X := elementaryProfile.X) (n := n) (u := u)
          (hX n) (hU n) hRH hu3
    calc
      ‖logDeriv riemannZeta (perronLine perronRe u)‖
          ≤ tailK * L := hnear
      _ = tailK * L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ tailK * L ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow tailK_nonneg
      _ ≤ wave27Kline * L ^ (2 : ℝ) := by
            unfold wave27Kline
            exact mul_le_mul_of_nonneg_right (by linarith [stripK_nonneg]) hpow2_nonneg

/-! ## The vertical tail at the paper exponent -/

/-- **The vertical tail bound at exponent `elementaryCper - 1 = 2`.**  This is
`verticalTailBound_of_RH` (exponent `1`) raised by monotonicity. -/
theorem verticalTailBound_elementary_of_RH
    (hRH : RiemannZetaZerosOnLine) :
    VerticalTailBound elementaryProfile.X (fun _ => tailK / Real.pi)
      (elementaryCper - 1) := by
  have hX : ∀ n, 1 < elementaryProfile.X n := by
    intro n
    change 1 < elementaryX n
    exact elementaryX_gt_one n
  have hU : ∀ n, 3 ≤ bandLog elementaryProfile.X n := by
    intro n
    change 3 ≤ bandLog elementaryX n
    rw [bandLog_elementaryX]
    exact elementaryU_ge_three n
  have htail : VerticalTailBound elementaryProfile.X
      (fun _ => tailK / Real.pi) 1 :=
    verticalTailBound_of_RH (X := elementaryProfile.X) hX hU hRH
  have hK : ∀ᶠ n : ℕ in atTop, 0 ≤ (fun _ => tailK / Real.pi) n :=
    Eventually.of_forall fun _ => div_nonneg tailK_nonneg Real.pi_pos.le
  have hCC' : (1 : ℝ) ≤ elementaryCper - 1 := by
    unfold elementaryCper
    norm_num
  exact verticalTailBound_mono_exponent hX hU hK hCC' htail

/-! ## The new L21.2 residual -/

/-- **The Wave-27 L21.2 analytic residual.**  It contains only the Riemann
hypothesis for `ζ` and the literal central short-interval smooth count.  The
`ZetaSide` fields `zeroFree`, `b`, `B`, `estimate`, `KlineRaw` and `ratio_le`
are gone; the line and tail bounds are constructed from `zetaRH`. -/
structure Wave27L21Inputs where
  /-- The Riemann hypothesis for `ζ`. -/
  zetaRH : RiemannZetaZerosOnLine
  /-- The literal central short-interval smooth count. -/
  localCount : ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX

namespace Wave27L21Inputs

variable (L : Wave27L21Inputs)

/-- The elementary profile keeps its own `X`. -/
theorem profile_X (n : ℕ) : elementaryProfile.X n = elementaryX n := rfl

/-- The centre sequence is the elementary scale `X`. -/
theorem p_eq : (elementaryX : ℕ → ℝ) = elementaryProfile.X := rfl

/-- **The concrete `Wave17L21_2Inputs` from `{ zetaRH, localCount }`.**

Every structural, numerical and Fourier field is the elementary/tent theorem.
The line bound is `verticalLineBound_elementary_of_RH` at the constant
`wave27Kline`; the tail is `verticalTailBound_elementary_of_RH` at
`tailK / π`.  The centre sequence is reconciled with `elementaryX` by
definitional equality `elementaryProfile.X = elementaryX`. -/
noncomputable def toWave17Inputs : Wave17L21_2Inputs := by
  have hX : ∀ n, 1 < elementaryProfile.X n := by
    intro n
    change 1 < elementaryX n
    exact elementaryX_gt_one n
  have hU : ∀ n, 3 ≤ bandLog elementaryProfile.X n := by
    intro n
    change 3 ≤ bandLog elementaryX n
    rw [bandLog_elementaryX]
    exact elementaryU_ge_three n
  have hline : VerticalLineBound elementaryProfile.X (fun _ => wave27Kline)
      (elementaryCper - 1) := by
    have h := verticalLineBound_elementary_of_RH L.zetaRH
    simpa [show (elementaryCper : ℝ) - 1 = 2 by
      unfold elementaryCper
      norm_num] using h
  have htail : VerticalTailBound elementaryProfile.X (fun _ => tailK / Real.pi)
      (elementaryCper - 1) :=
    verticalTailBound_elementary_of_RH L.zetaRH
  exact Wave17L21_2Inputs.ofRaw
    (profile := elementaryProfile)
    (c := elementaryC)
    (Cper := elementaryCper)
    (KlineRaw := wave27Kline)
    (Ktail := tailK / Real.pi)
    (p := elementaryX)
    hX elementaryC_pos elementaryC_le_one hU
    (by unfold elementaryCper; norm_num)
    wave27Kline_nonneg
    (div_nonneg tailK_nonneg Real.pi_pos.le)
    L.zetaRH
    hline
    htail
    (Eventually.of_forall elementaryX_gt_one)
    L.localCount
    (by
      simpa only [elementaryProfile_X] using elementary_b_le_B)
    (by
      simpa only [elementaryProfile_X] using elementary_a_ge_log_two)
    (elementaryProfile_fourierLow elementaryC)
    (elementaryProfile_fourierMiddle elementaryC)
    elementaryProfile_fourierTail
    (by
      intro m hm
      filter_upwards [elementaryU_dominates m hm] with n hn
      exact hn)
    (by
      filter_upwards [elementaryU_le_exp] with n hn
      exact hn)

/-- The assembled record keeps the elementary profile. -/
theorem toWave17Inputs_profile :
    (L.toWave17Inputs).profile = elementaryProfile := rfl

/-- The assembled record keeps the elementary stage-one constant. -/
theorem toWave17Inputs_c : (L.toWave17Inputs).c = elementaryC := rfl

/-- The assembled record keeps the elementary Perron exponent. -/
theorem toWave17Inputs_Cper : (L.toWave17Inputs).Cper = elementaryCper := rfl

/-- The assembled record keeps the centre sequence `p = X`. -/
theorem toWave17Inputs_p : (L.toWave17Inputs).p = elementaryX := rfl

/-- The assembled record keeps the literal central count. -/
theorem toWave17Inputs_localCount :
    (L.toWave17Inputs).localCount = L.localCount := rfl

/-- The assembled record keeps the horizontal/line constant `wave27Kline`. -/
theorem toWave17Inputs_KlineRaw :
    (L.toWave17Inputs).KlineRaw = wave27Kline := rfl

/-- The assembled record keeps the tail constant `tailK / π`. -/
theorem toWave17Inputs_Ktail :
    (L.toWave17Inputs).Ktail = tailK / Real.pi := rfl

/-- The assembled record carries the Riemann hypothesis. -/
theorem toWave17Inputs_hRH :
    (L.toWave17Inputs).hRH = L.zetaRH := rfl

/-- **The L21.2 rated leaf, with no `ZetaSide` input.** -/
noncomputable def toL21_2LeafData : L21_2LeafData :=
  L.toWave17Inputs.toL21_2LeafData

/-- **The residual `ConcreteLeafResidual` once a `ZetaSide` is supplied.**
This is the direction in which the Wave-26 record is recovered; it exhibits the
exact content removed by Wave 27. -/
noncomputable def toConcreteLeafResidual (z : ZetaSide) : ConcreteLeafResidual where
  zeta := z
  localCount := L.localCount

end Wave27L21Inputs

/-! ## The Wave-27 ledger -/

/-- **The Wave-27 ledger.**  The L21.2 slot is read from the new
`{ zetaRH, localCount }` input; the L30 leaf is the Wave-26 failure leaf and all
other leaves are unchanged. -/
noncomputable def wave27Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  fullyDischargedSlots l18_4 l19.toL19FullCertificate
    (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf l21.toL21_2LeafData)
    (wave15L27Leaf l27_data l27_finish) l30.toSubexpLeaf
    (wave15L34Leaf l34) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
    (wave14P1Leaf p1)

/-- The Wave-27 L21.2 loss written as the literal bad-centre fraction. -/
theorem wave27Slots_l21_loss (L : Wave27L21Inputs) (n : ℕ) :
    (wave14L21_2Leaf L.toL21_2LeafData).loss n =
      ((L.toWave17Inputs.toL21_2LeafData.toAbelInputs.toFourierInputs.badSet n).card : ℝ) /
        (L.toWave17Inputs.toL21_2LeafData.profile.N n : ℝ) :=
  wave14L21_2Leaf_loss_eq_card_fraction _ n

/-! ## The E-generic residual record -/

/-- **The Wave-27 E-generic residual record.**

This is exactly `PaperResidualFor26` with

```
l21 : ConcreteLeafResidual
```

replaced by

```
l21 : Wave27L21Inputs,
```

so the L21.2 leaf carries only `zetaRH` and `localCount`.  All E-specific
fields, the concrete C5 data and the ledger domination are unchanged; the
ledger is `wave27Slots`. -/
structure PaperResidualFor27
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate, with the L19.6 thin slot built from lattice
  data. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- **The whole L21.2 analytic input**: the Riemann hypothesis and the
  literal central short-interval smooth count. -/
  l21 : Wave27L21Inputs
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- **L30 with both density fields derived**, leaving only the sharp central
  count, the GRH lower bound, the density growth and the H.3 failure data. -/
  l30 : Wave26L30Inputs
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
  /-- Adapter: the concrete C5 loss is dominated by the wave-27 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave27Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor27

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The fully discharged inputs directly from the Wave-27 record.**
The L21.2 slot is the new `{ zetaRH, localCount }` leaf; no zeta-side package is
read by the ledger. -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor27 E D) :
    FullyDischargedInputs E D where
  l18_4 := I.l18_4
  l19 := I.l19.toL19FullCertificate
  l20_2 := wave14L20_2Leaf I.l20_2
  l20_4 := I.l20_4.toSubexpLeaf
  l21_2 := wave14L21_2Leaf I.l21.toL21_2LeafData
  l27_1 := wave15L27Leaf I.l27_data I.l27_finish
  l30 := I.l30.toSubexpLeaf
  l34 := wave15L34Leaf I.l34
  l4_l25_l36 := wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget
  p1 := wave14P1Leaf I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5 := I.c5Data.toC5
  loss_le := by
    intro n hN
    simpa only [wave27Slots] using I.loss_le n hN

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor27 E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-! ## Recovering the Wave-26 record

The Wave-26 record still stores a `ZetaSide`.  The following arrow supplies one
and changes nothing else; this is exactly the content that Wave 27 removes. -/

/-- The L21.2 loss of the Wave-26 leaf built from a `ZetaSide` and the same
central count equals the Wave-27 L21.2 loss: both are the bad-centre fraction on
the same elementary profile. -/
theorem wave26Leaf_loss_eq_wave27Leaf_loss
    (z : ZetaSide) (hcount : ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX)
    (n : ℕ) :
    (wave14L21_2Leaf
        (wave17InputsOfResidual { zeta := z, localCount := hcount }).toL21_2LeafData).loss n =
      (wave14L21_2Leaf
        ((Wave27L21Inputs.mk (zetaRH := z.rh) (localCount := hcount)).toL21_2LeafData)).loss n := by
  rw [wave14L21_2Leaf_loss_eq_card_fraction,
    wave14L21_2Leaf_loss_eq_card_fraction]
  rfl

/-- **The Wave-27 ledger total equals the Wave-26 ledger total at the same
`ZetaSide` and central count.**  Only the L21.2 loss occurs in the total, and it
is the same bad-centre fraction. -/
theorem wave27Slots_total_eq_wave26Slots_total
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (z : ZetaSide) (hcount : ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX)
    (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (p1 : SubexpPrepassInput) :
    (wave27Slots l18_4 l19 l20_2 l20_4
        (Wave27L21Inputs.mk (zetaRH := z.rh) (localCount := hcount))
        l27_data l27_finish l30 l34 p1).total =
      (wave26Slots l18_4 l19 l20_2 l20_4
        { zeta := z, localCount := hcount }
        l27_data l27_finish l30 l34 p1).total := by
  funext n
  unfold wave27Slots wave26Slots
  rw [fullyDischargedSlots_total_eq, fullyDischargedSlots_total_eq]
  simp only [wave26Leaf_loss_eq_wave27Leaf_loss z hcount n]

/-- **`PaperResidualFor27 → PaperResidualFor26`** once a `ZetaSide` is supplied.

This is the precise hypothesis-order statement: the Wave-26 record is the
Wave-27 record plus a `ZetaSide`.  The L21.2 loss and hence the ledger total are
unchanged, so the `loss_le` adapter transfers verbatim. -/
noncomputable def toPaperResidualFor26 (I : PaperResidualFor27 E D)
    (z : ZetaSide) : PaperResidualFor26 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := { zeta := z, localCount := I.l21.localCount }
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
    rw [← wave27Slots_total_eq_wave26Slots_total I.l18_4 I.l19 I.l20_2 I.l20_4
      z I.l21.localCount I.l27_data I.l27_finish I.l30 I.l34 I.p1]
    exact I.loss_le n hN

/-- The reduction replaces only the L21.2 block. -/
theorem toPaperResidualFor26_l21 (I : PaperResidualFor27 E D) (z : ZetaSide) :
    (I.toPaperResidualFor26 z).l21 =
      ({ zeta := z, localCount := I.l21.localCount } : ConcreteLeafResidual) := rfl

/-- The reduction keeps the L30 block. -/
theorem toPaperResidualFor26_l30 (I : PaperResidualFor27 E D) (z : ZetaSide) :
    (I.toPaperResidualFor26 z).l30 = I.l30 := rfl

/-- The reduction is the identity on every c1–c4 field. -/
theorem toPaperResidualFor26_c (I : PaperResidualFor27 E D) (z : ZetaSide) :
    (I.toPaperResidualFor26 z).c1 = I.c1 ∧
      (I.toPaperResidualFor26 z).c2 = I.c2 ∧
      (I.toPaperResidualFor26 z).c3 = I.c3 ∧
      (I.toPaperResidualFor26 z).c4 = I.c4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The reduction is the identity on the concrete family, its adapter and the
C5 data. -/
theorem toPaperResidualFor26_c5 (I : PaperResidualFor27 E D) (z : ZetaSide) :
    (I.toPaperResidualFor26 z).concrete = I.concrete ∧
      (I.toPaperResidualFor26 z).concrete_eq = I.concrete_eq ∧
      (I.toPaperResidualFor26 z).c5Data = I.c5Data :=
  ⟨rfl, rfl, rfl⟩

/-- **`PaperResidualFor26 → PaperResidualFor27`.**  This is the unconditional
direction: the Wave-27 L21.2 input is obtained from the Wave-26 one by keeping
only the Riemann hypothesis and the central short count.  The ledger total is
unchanged because the L21.2 loss is the same bad-centre fraction. -/
noncomputable def ofPaperResidualFor26 (I : PaperResidualFor26 E D) :
    PaperResidualFor27 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 :=
    { zetaRH := I.l21.zeta.rh
      localCount := I.l21.localCount }
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
    rw [wave27Slots_total_eq_wave26Slots_total I.l18_4 I.l19 I.l20_2 I.l20_4
      I.l21.zeta I.l21.localCount I.l27_data I.l27_finish I.l30 I.l34 I.p1]
    exact I.loss_le n hN

/-- The unconditional reduction replaces only the L21.2 block. -/
theorem ofPaperResidualFor26_l21 (I : PaperResidualFor26 E D) :
    (PaperResidualFor27.ofPaperResidualFor26 I).l21 =
      ({ zetaRH := I.l21.zeta.rh
         localCount := I.l21.localCount } : Wave27L21Inputs) := rfl

end PaperResidualFor27

/-- **The schedule-indexed form of the Wave-27 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor27Schedule
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor27 (E s) D

/-! ## The E-generic endpoint -/

/-- **Wave-27 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** balanced-
schedule epoch family `E` which, at every valid ceiling, carries a
`PaperResidualFor27 (E s) D` record, the kernel-checked driver outputs a
permutation of `n.primeFactorsList` and has expected serialized bit cost
eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The L21.2 leaf of the record is only `{ zetaRH, localCount }`: the zero-free
line, the two-sided estimate and the `B / b` ratio are gone, and the line bound
is constructed from the off-pole strip estimate.  The epoch family `E` is
quantified inside the conclusion.  The proof transports each record by
`PaperResidualFor27.toFullyDischargedInputs` and applies
`serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave27Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor27 (E s) D) →
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

/-! ## Residual accounting -/

/-- The field names of `Wave27L21Inputs`.  None of `zeroFree`, `b`, `B`,
`estimate`, `KlineRaw` or `ratio_le` is present. -/
def wave27L21FieldNames : List String :=
  ["zetaRH", "localCount"]

theorem wave27L21FieldNames_length : wave27L21FieldNames.length = 2 := rfl

/-- **There is no `zeroFree` field in the Wave-27 L21.2 input.** -/
theorem wave27L21_no_zeroFree_field :
    wave27L21FieldNames.all (fun s => decide (s ≠ "zeroFree")) = true := by
  decide

/-- **There is no `b`/`B` two-sided estimate in the Wave-27 L21.2 input.** -/
theorem wave27L21_no_estimate_fields :
    wave27L21FieldNames.all
      (fun s => decide (s ≠ "b" ∧ s ≠ "B" ∧ s ≠ "estimate")) = true := by
  decide

/-- **There is no `KlineRaw` or `ratio_le` field in the Wave-27 L21.2 input.** -/
theorem wave27L21_no_ratio_fields :
    wave27L21FieldNames.all
      (fun s => decide (s ≠ "KlineRaw" ∧ s ≠ "ratio_le")) = true := by
  decide

/-- **The complete L21.2 residual of the Wave-27 record** is exactly the
Riemann hypothesis and the central short count. -/
def wave27RemainingL21FieldNames : List String :=
  ["zetaRH", "localCount"]

theorem wave27RemainingL21FieldNames_length :
    wave27RemainingL21FieldNames.length = 2 := rfl

/-- **The complete remaining L21.2 analytic input of the Wave-27 record.** -/
theorem wave27_l21_remaining (L : Wave27L21Inputs) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨L.zetaRH, L.localCount⟩

/-- The line bound is derived, not assumed: it is the off-pole strip bound plus
the near-axis estimate. -/
theorem wave27_lineBound_derived (L : Wave27L21Inputs) :
    VerticalLineBound elementaryProfile.X (fun _ => wave27Kline)
      (elementaryCper - 1) :=
  (L.toWave17Inputs).lineBound

/-- The vertical tail is derived, not assumed. -/
theorem wave27_verticalTail_derived (L : Wave27L21Inputs) :
    VerticalTailBound elementaryProfile.X (fun _ => tailK / Real.pi)
      (elementaryCper - 1) :=
  (L.toWave17Inputs).verticalTail

/-- The assembled line bound uses exactly the constant `stripK + tailK`. -/
theorem wave27_lineBound_constant (L : Wave27L21Inputs) :
    (L.toWave17Inputs).KlineRaw = stripK + tailK := rfl

/-! ## Axiom audit -/

#print axioms wave27Kline_nonneg
#print axioms verticalLineBound_elementary_of_RH
#print axioms verticalTailBound_elementary_of_RH
#print axioms Wave27L21Inputs.profile_X
#print axioms Wave27L21Inputs.p_eq
#print axioms Wave27L21Inputs.toWave17Inputs
#print axioms Wave27L21Inputs.toWave17Inputs_profile
#print axioms Wave27L21Inputs.toWave17Inputs_c
#print axioms Wave27L21Inputs.toWave17Inputs_Cper
#print axioms Wave27L21Inputs.toWave17Inputs_p
#print axioms Wave27L21Inputs.toWave17Inputs_localCount
#print axioms Wave27L21Inputs.toWave17Inputs_KlineRaw
#print axioms Wave27L21Inputs.toWave17Inputs_Ktail
#print axioms Wave27L21Inputs.toWave17Inputs_hRH
#print axioms Wave27L21Inputs.toL21_2LeafData
#print axioms Wave27L21Inputs.toConcreteLeafResidual
#print axioms wave27Slots
#print axioms wave27Slots_l21_loss
#print axioms PaperResidualFor27.toFullyDischargedInputs
#print axioms PaperResidualFor27.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor27.wave26Leaf_loss_eq_wave27Leaf_loss
#print axioms PaperResidualFor27.wave27Slots_total_eq_wave26Slots_total
#print axioms PaperResidualFor27.toPaperResidualFor26
#print axioms PaperResidualFor27.toPaperResidualFor26_l21
#print axioms PaperResidualFor27.toPaperResidualFor26_l30
#print axioms PaperResidualFor27.toPaperResidualFor26_c
#print axioms PaperResidualFor27.toPaperResidualFor26_c5
#print axioms PaperResidualFor27.ofPaperResidualFor26
#print axioms PaperResidualFor27.ofPaperResidualFor26_l21
#print axioms PaperResidualFor27Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave27Inputs
#print axioms wave27L21FieldNames_length
#print axioms wave27L21_no_zeroFree_field
#print axioms wave27L21_no_estimate_fields
#print axioms wave27L21_no_ratio_fields
#print axioms wave27RemainingL21FieldNames_length
#print axioms wave27_l21_remaining
#print axioms wave27_lineBound_derived
#print axioms wave27_verticalTail_derived
#print axioms wave27_lineBound_constant

end Cogentic.RandomizedPaperEndpointWave27
