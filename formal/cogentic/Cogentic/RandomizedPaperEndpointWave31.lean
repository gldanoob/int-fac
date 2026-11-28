import Cogentic.RandomizedPaperEndpointWave29
import Cogentic.RandomizedL30Dickman

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 31: the Wave-29 L30 sharp count is replaced by the Buchstab and parity fields

The Wave-26 L30 counts `Wave26L30Counts` still carried the single analytic
field

```
short_interval : YounisOddPaperSharpIntervalCount c p ε,
```

the sharp odd-half central short-interval count.  `Cogentic.RandomizedL30Dickman`
decomposed exactly this statement into two independent explicit analytic
inputs:

* `BuchstabLargePrimeShortIntervalLower c p ε` — the large-prime
  (`P > sqrt y`) part of the one-prime Buchstab convolution already has the
  sharp size `c p^{3/2} ρ(u)`, and
* `CentralOddHalfParity θ p ε` — at least a `θ` fraction of the central smooth
  integers satisfy the odd-half parity `m % 4 = 2`.

The composition
`sharpCentralOddSmoothIntervalCount_of_buchstabLargePrime_parity` derives
`YounisOddPaperSharpIntervalCount (θ * c) p ε` from those two fields.

## What is defined and proved

* `Wave31L30Counts` is `Wave26L30Counts` with `short_interval` removed, and with
  the two fields `hbuchstab` and `hparity` added, together with the paper
  choice `θ = 1/2 ∨ θ = 3/8`.  The **effective** paper count constant is
  therefore `θ * c`, not `c`: the field `c` below is the Buchstab constant and
  the arithmetic side condition is adjusted to `A * C ≤ θ * c`.

  The field `p_ge_two : ∀ n, 2 ≤ p n` is the elementary pointwise nonnegativity
  of the prime scale.  Wave 26 derived only the eventual form from
  `PaperDensityGrowth`; the interval-count bridge used here is stated
  pointwise, so the pointwise form is recorded explicitly.  It is arithmetic
  data, not an analytic residual.

* `Wave31L30Counts.short_interval` derives
  `YounisOddPaperSharpIntervalCount (θ * c) p ε` by
  `sharpCentralOddSmoothIntervalCount_of_buchstabLargePrime_parity`.
  It is a theorem of the record, not a field.

* `Wave31L30Inputs` keeps the Cantor/H.5 cost data and the H.3 failure data
  unchanged, so the ledger loss is still the actual H.3 failure probability.
  `toWave26L30Inputs` fills the removed `short_interval` with the derived
  theorem and sets the Wave-26 constant to `θ * c`.

* `PaperResidualFor31` is the Wave-29 E-generic record with
  `l30 : Wave31L30Inputs`; `toPaperResidualFor29` transports it back, and

  `serialized_assembled_balancedEnvelopeInfimum_from_wave31Inputs`

  is the E-generic endpoint, with `E` quantified inside the conclusion.

## The exact residual list

Compared with Wave 29, the single L30 entry `short_interval` is replaced by
`hbuchstab` and `hparity`.  The full list has 24 entries:

```
[zetaRH, localCount, hbuchstab, hparity,
 hurwitzClassNumber, siegelLower, hasse, waterhouseTrace, killMass, curveBudget,
 zeroFree, cheb, range, beta0_le_half,
 l18_4, l19, l20_2, l20_4, c1, c2, c3, c4, concrete, p1]
```

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss,
probability or error is set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedPaperEndpointWave31

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
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27KillLaw
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30Dickman
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
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34BelowOne
open Cogentic.RandomizedL34DedekindStrip
open Cogentic.RandomizedL34ZeroFreeArithmetic
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34DedekindGRH
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34Range
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
open Cogentic.RandomizedPaperEndpointWave27
open Cogentic.RandomizedPaperEndpointWave28
open Cogentic.RandomizedPaperEndpointWave29
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## 1. The Wave-31 L30 counts -/

/-- **The Wave-31 L30 counts: the sharp central count is decomposed.**

Compared with `Wave26L30Counts`:

* `short_interval` is removed;
* it is replaced by the two explicit Dickman/Buchstab fields
  `hbuchstab : BuchstabLargePrimeShortIntervalLower c p ε` and
  `hparity : CentralOddHalfParity θ p ε`, with the paper parity fraction
  `θ = 1/2 ∨ θ = 3/8`;
* the effective paper count constant is `θ * c`, so the arithmetic side
  condition becomes `A * C ≤ θ * c` (the field `c` is the Buchstab constant);
* the elementary pointwise `p_ge_two` is recorded because the interval-count
  bridge is stated pointwise (Wave 26 derived only the eventual form).

All other fields are copied verbatim from Wave 26. -/
structure Wave31L30Counts where
  /-- The prime whose genus-two order is counted. -/
  p : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The constant paper error underlying the sharp density statements. -/
  ε : ℝ
  /-- The relative error is the constant paper error. -/
  err_eq : err = paperError ε
  /-- The prime is pointwise at least two.  (Elementary data; Wave 26 only
  needed and derived the eventual form.) -/
  p_ge_two : ∀ n, 2 ≤ p n
  /-- The relative short-interval density constant. -/
  A : ℝ
  /-- The global smooth lower-bound constant. -/
  B : ℝ
  /-- The large-prime Buchstab constant. -/
  c : ℝ
  /-- The global odd upper-density constant. -/
  C : ℝ
  /-- The odd-half parity fraction. -/
  θ : ℝ
  /-- `A > 0`. -/
  A_pos : 0 < A
  /-- `B > 0`. -/
  B_pos : 0 < B
  /-- The arithmetic relation `A B ≥ 4`. -/
  AB_ge_four : 4 ≤ A * B
  /-- The paper count dominates the relative density constant, at the
  **effective** constant `θ * c` produced by the parity transfer. -/
  AC_le : A * C ≤ θ * c
  /-- The paper parity fraction is one of the two values `1/2` and `3/8`. -/
  θ_paper : θ = 1 / 2 ∨ θ = 3 / 8
  /-- **The missing large-prime Buchstab short-interval lower bound.** -/
  hbuchstab : BuchstabLargePrimeShortIntervalLower c p ε
  /-- **The missing odd-half parity fraction.** -/
  hparity : CentralOddHalfParity θ p ε
  /-- Paper density growth of `p`; an elementary growth hypothesis, used by the
  unconditional sharp upper-density theorem and by the GRH lower bound. -/
  growth : PaperDensityGrowth p
  /-- `ε > 0`. -/
  ε_pos : 0 < ε
  /-- **The arithmetic constant bound replacing the analytic upper density.** -/
  l30C_ge_one : 1 ≤ C
  /-- **The arithmetic constant bound needed by the GRH global lower bound.** -/
  l30B_le_eighth : B ≤ 1 / 8

namespace Wave31L30Counts

variable (S : Wave31L30Counts)

/-- The parity fraction is nonnegative.  This is the hypothesis consumed by
`sharpCentralOddSmoothIntervalCount_of_buchstabLargePrime_parity`. -/
theorem theta_nonneg : 0 ≤ S.θ := by
  rcases S.θ_paper with h | h <;> rw [h] <;> norm_num

/-- The parity fraction is positive. -/
theorem theta_pos : 0 < S.θ := by
  rcases S.θ_paper with h | h <;> rw [h] <;> norm_num

/-- **The sharp central interval count, derived from the Buchstab estimate and
the parity fraction.**  The derived constant is `θ * c`; this is why the
record's effective paper constant is `θ * c` rather than the Buchstab
constant `c`. -/
theorem short_interval :
    YounisOddPaperSharpIntervalCount (S.θ * S.c) S.p S.ε :=
  sharpCentralOddSmoothIntervalCount_of_buchstabLargePrime_parity
    S.p_ge_two S.theta_nonneg S.hbuchstab S.hparity

/-- The `1/2` specialisation of the derived short count. -/
theorem short_interval_half (h : S.θ = 1 / 2) :
    YounisOddPaperSharpIntervalCount ((1 / 2) * S.c) S.p S.ε := by
  simpa only [h] using S.short_interval

/-- The `3/8` specialisation of the derived short count. -/
theorem short_interval_three_eighths (h : S.θ = 3 / 8) :
    YounisOddPaperSharpIntervalCount ((3 / 8) * S.c) S.p S.ε := by
  simpa only [h] using S.short_interval

/-- **The derived sharp global odd upper density.** -/
theorem sharpUpper :
    GlobalOddUpperDensitySharp S.C S.p S.ε :=
  globalOddUpperDensitySharp_of_one_le S.growth S.ε_pos S.l30C_ge_one

/-- **The derived global odd lower bound**, eventual at the paper scale. -/
theorem globalLower (line : DirichletLZerosOnLine) :
    EventuallyYounisOddGlobalLower S.B S.p (paperT S.p) S.err := by
  have h := eventually_younisOddGlobalLower_paper_of_le line S.p S.growth
    S.ε_pos S.l30B_le_eighth
  simpa only [S.err_eq] using h

/-- The relative error is at least `-1`. -/
theorem err_ge_neg_one (n : ℕ) : -1 ≤ S.err n := by
  rw [S.err_eq]
  dsimp [paperError]
  linarith [S.ε_pos]

/-- The prime is eventually at least two. -/
theorem eventually_p_ge_two : ∀ᶠ n in atTop, 2 ≤ S.p n :=
  Filter.Eventually.of_forall S.p_ge_two

/-- **The Wave-26 counts with the removed field restored by the derived
theorem.**  The Wave-26 `c` is the effective constant `θ * c`, and its
`short_interval` is `S.short_interval`. -/
noncomputable def toWave26L30Counts : Wave26L30Counts where
  p := S.p
  err := S.err
  ε := S.ε
  err_eq := S.err_eq
  A := S.A
  B := S.B
  c := S.θ * S.c
  C := S.C
  A_pos := S.A_pos
  B_pos := S.B_pos
  AB_ge_four := S.AB_ge_four
  AC_le := S.AC_le
  short_interval := S.short_interval
  growth := S.growth
  ε_pos := S.ε_pos
  l30C_ge_one := S.l30C_ge_one
  l30B_le_eighth := S.l30B_le_eighth

/-- The transport carries the derived short count. -/
theorem toWave26L30Counts_short_interval :
    (S.toWave26L30Counts).short_interval = S.short_interval := rfl

/-- The transport changes only the effective constant, from `θ * c` to the
Wave-26 field `c`. -/
theorem toWave26L30Counts_c :
    (S.toWave26L30Counts).c = S.θ * S.c := rfl

end Wave31L30Counts

/-! ## 2. The Wave-31 L30 inputs -/

/-- **The Wave-31 L30 replacement.**  The counts are `Wave31L30Counts`; the
Cantor/H.5 cost data and the H.3 failure data are unchanged from Wave 26. -/
structure Wave31L30Inputs where
  /-- The central count with the Buchstab and parity fields. -/
  counts : Wave31L30Counts
  /-- The Cantor/H.5 cost and correctness data. -/
  cantor : CantorCostInputs
  /-- The H.3 failure data, including the useful-prime split bound. -/
  failure : FailureData

namespace Wave31L30Inputs

variable (I : Wave31L30Inputs)

/-- **The Wave-26 L30 inputs, with `short_interval` derived.** -/
noncomputable def toWave26L30Inputs : Wave26L30Inputs where
  counts := I.counts.toWave26L30Counts
  cantor := I.cantor
  failure := I.failure

/-- The transport leaves the counts' derived short count unchanged. -/
theorem toWave26L30Inputs_short_interval :
    I.toWave26L30Inputs.counts.short_interval = I.counts.short_interval := rfl

/-- The transport leaves the Cantor and failure data unchanged. -/
theorem toWave26L30Inputs_data :
    I.toWave26L30Inputs.cantor = I.cantor ∧
      I.toWave26L30Inputs.failure = I.failure :=
  ⟨rfl, rfl⟩

/-- The L30 ledger leaf: the actual H.3 failure probability. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  I.failure.toSubexpLeaf

/-- **The L30 loss is the actual H.3 failure probability**, unchanged from
Wave 29. -/
theorem loss_eq (n : ℕ) : I.toSubexpLeaf.loss n = I.failure.failure n := rfl

/-- The L30 loss of the transported Wave-26 inputs is the same failure
probability. -/
theorem toWave26L30Inputs_loss_eq (n : ℕ) :
    I.toWave26L30Inputs.toSubexpLeaf.loss n = I.failure.failure n := rfl

end Wave31L30Inputs

/-! ## 3. The Wave-31 ledger -/

/-- **The Wave-31 ledger.**  It is the Wave-29 ledger at the Wave-26 record
obtained by deriving `short_interval` from the Buchstab and parity fields.  The
L30 leaf reads only the H.3 failure probability, which is unchanged. -/
noncomputable def wave31Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
    l30.toWave26L30Inputs l34 p1

/-- The Wave-31 ledger is definitionally the Wave-29 ledger at the derived
`short_interval`. -/
theorem wave31Slots_eq_wave29Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : Wave27L21Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave31L30Inputs) (l34 : Wave28L34Inputs)
    (p1 : SubexpPrepassInput) :
    wave31Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave29Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30.toWave26L30Inputs l34 p1 := rfl

/-- The L30 loss of the Wave-31 ledger is exactly the H.3 failure
probability. -/
theorem wave31Slots_l30_loss_eq (l30 : Wave31L30Inputs) (n : ℕ) :
    l30.toWave26L30Inputs.toSubexpLeaf.loss n = l30.failure.failure n := rfl

/-! ## 4. The Wave-31 E-generic residual record -/

/-- **The Wave-31 E-generic residual record.**  It is the Wave-29 record with
`l30 : Wave26L30Inputs` replaced by `l30 : Wave31L30Inputs`, whose L30 analytic
content is the Buchstab estimate `hbuchstab` and the parity fraction
`hparity`; the sharp central count is derived.  All other fields are copied
verbatim, and the ledger is `wave31Slots`. -/
structure PaperResidualFor31
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
  /-- **The L21.2 analytic input**: the Riemann hypothesis and the literal
  central short-interval smooth count. -/
  l21 : Wave27L21Inputs
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- **L30 with the sharp count derived** from the Buchstab estimate and the
  parity fraction, leaving the H.3 failure data. -/
  l30 : Wave31L30Inputs
  /-- **L34 with the Stark field derived** from `β₀ ≤ 1/2` and the paper's
  arithmetic `2 ≤ 4 F log|Δ|`. -/
  l34 : Wave28L34Inputs
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
  /-- Adapter: the concrete C5 loss is dominated by the Wave-31 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave31Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor31

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor31 E D → PaperResidualFor29 E D`.**  Only the L30 block
changes: `short_interval` is derived from `hbuchstab` and `hparity` by
`Wave31L30Inputs.toWave26L30Inputs`.  The ledger is definitionally the Wave-29
ledger (`wave31Slots_eq_wave29Slots`), so the C5 loss adapter transfers
unchanged. -/
noncomputable def toPaperResidualFor29 (I : PaperResidualFor31 E D) :
    PaperResidualFor29 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30.toWave26L30Inputs
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
    simpa only [wave31Slots] using I.loss_le n hN

/-- The transport changes only the L30 block. -/
theorem toPaperResidualFor29_l30 (I : PaperResidualFor31 E D) :
    (I.toPaperResidualFor29).l30 = I.l30.toWave26L30Inputs := rfl

/-- The transported `short_interval` is the derived theorem, not an assumed
field. -/
theorem toPaperResidualFor29_l30_short_interval (I : PaperResidualFor31 E D) :
    (I.toPaperResidualFor29).l30.counts.short_interval =
      I.l30.counts.short_interval := rfl

/-- The transport keeps the L21, L34 and P1 blocks. -/
theorem toPaperResidualFor29_l21_l34_p1 (I : PaperResidualFor31 E D) :
    (I.toPaperResidualFor29).l21 = I.l21 ∧
      (I.toPaperResidualFor29).l34 = I.l34 ∧
      (I.toPaperResidualFor29).p1 = I.p1 :=
  ⟨rfl, rfl, rfl⟩

/-- The transport leaves the failure probability unchanged. -/
theorem toPaperResidualFor29_l30_loss_eq (I : PaperResidualFor31 E D) (n : ℕ) :
    (I.toPaperResidualFor29).l30.toSubexpLeaf.loss n =
      I.l30.failure.failure n := rfl

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor31 E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toPaperResidualFor29.toFullyDischargedInputs⟩

end PaperResidualFor31

/-- **The schedule-indexed form of the Wave-31 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor31Schedule
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor31 (E s) D

/-! ## 5. The E-generic endpoint -/

/-- **Wave-31 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** balanced
schedule epoch family `E` which, at every valid ceiling, carries a
`PaperResidualFor31 (E s) D` record, the kernel-checked driver outputs a
permutation of `n.primeFactorsList` and has expected serialized bit cost
eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The L30 block of the record carries only the Buchstab large-prime estimate and
the odd-half parity fraction; the sharp central count is derived.  The epoch
family `E` is quantified inside the conclusion. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave31Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor31 (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave29Inputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toPaperResidualFor29⟩

/-! ## 6. Residual accounting -/

/-- The field names of `Wave31L30Counts`.  `short_interval` is absent; the two
added analytic fields are `hbuchstab` and `hparity`, and `θ`/`θ_paper` record
the paper parity fraction. -/
def wave31L30CountsFieldNames : List String :=
  ["p", "err", "ε", "err_eq", "p_ge_two", "A", "B", "c", "C", "θ",
   "A_pos", "B_pos", "AB_ge_four", "AC_le", "θ_paper",
   "hbuchstab", "hparity", "growth", "ε_pos", "l30C_ge_one", "l30B_le_eighth"]

theorem wave31L30CountsFieldNames_length :
    wave31L30CountsFieldNames.length = 21 := rfl

/-- **There is no analytic `short_interval` field in the Wave-31 counts**: it is
derived from `hbuchstab` and `hparity`. -/
theorem wave31L30_no_shortInterval_field :
    wave31L30CountsFieldNames.all (fun s => decide (s ≠ "short_interval")) = true := by
  decide

/-- **The residual L30 analytic list is exactly the Buchstab estimate and the
parity fraction.** -/
def wave31RemainingL30FieldNames : List String :=
  ["hbuchstab", "hparity"]

theorem wave31RemainingL30FieldNames_length :
    wave31RemainingL30FieldNames.length = 2 := rfl

/-- **The complete remaining L30 analytic input of the Wave-31 record** is the
Buchstab large-prime estimate together with the odd-half parity fraction.  The
sharp central count is a theorem of the record. -/
theorem wave31_l30_remaining (S : Wave31L30Counts) :
    BuchstabLargePrimeShortIntervalLower S.c S.p S.ε ∧
      CentralOddHalfParity S.θ S.p S.ε :=
  ⟨S.hbuchstab, S.hparity⟩

/-- **The sharp central count is derived**, with the effective constant
`θ * c`. -/
theorem wave31_l30_short_interval_derived (S : Wave31L30Counts) :
    YounisOddPaperSharpIntervalCount (S.θ * S.c) S.p S.ε :=
  S.short_interval

/-- The same residual statement for the E-generic record. -/
theorem wave31_l30_remaining_of_record (I : PaperResidualFor31 E D) :
    BuchstabLargePrimeShortIntervalLower I.l30.counts.c I.l30.counts.p
        I.l30.counts.ε ∧
      CentralOddHalfParity I.l30.counts.θ I.l30.counts.p I.l30.counts.ε :=
  wave31_l30_remaining I.l30.counts

/-- **The sharp upper density is not a residual field**: it is a theorem for
every record, with no line hypothesis. -/
theorem wave31_sharpUpper_derived (S : Wave31L30Counts) :
    GlobalOddUpperDensitySharp S.C S.p S.ε :=
  S.sharpUpper

/-- **The global lower bound is the GRH density theorem**, not a field. -/
theorem wave31_globalLower_derived (S : Wave31L30Counts)
    (line : DirichletLZerosOnLine) :
    EventuallyYounisOddGlobalLower S.B S.p (paperT S.p) S.err :=
  S.globalLower line

/-- The field names of `PaperResidualFor31`. -/
def wave31FieldNames : List String :=
  ["l18_4", "l19", "l20_2", "l20_4", "l21", "l27_data", "l27_finish",
   "l30", "l34", "p1", "c1", "c2", "c3", "c4", "concrete", "concrete_eq",
   "c5Data", "loss_le"]

theorem wave31FieldNames_length : wave31FieldNames.length = 18 := rfl

/-- **The exact combined residual list (analytic fields only).**

Compared with Wave 29, the single L30 entry `short_interval` is replaced by
`hbuchstab` (the large-prime Buchstab short-interval lower bound) and
`hparity` (the odd-half parity fraction).  The first line is
`RiemannZetaZerosOnLine` and the two L21/L30 analytic blocks; the second the
L27 class-number/Siegel/Hasse/Waterhouse/kill-law/budget block; the third the
L34 zero-free/effective-Chebotarev/range block; the fourth the L18.4/L19/L20
certificates, C1–C4/concrete and P1. -/
def wave31RemainingFieldNames : List String :=
  ["zetaRH", "localCount", "hbuchstab", "hparity",
   "hurwitzClassNumber", "siegelLower", "hasse", "waterhouseTrace",
   "killMass", "curveBudget",
   "zeroFree", "cheb", "range", "beta0_le_half",
   "l18_4", "l19", "l20_2", "l20_4", "c1", "c2", "c3", "c4", "concrete", "p1"]

theorem wave31RemainingFieldNames_length :
    wave31RemainingFieldNames.length = 24 := rfl

/-- The residual list does not contain the generic sharp count. -/
theorem wave31_no_shortInterval_residual :
    wave31RemainingFieldNames.all (fun s => decide (s ≠ "short_interval")) = true := by
  decide

/-- The residual list contains the two explicit Dickman/Buchstab entries. -/
theorem wave31_residual_has_buchstab_parity :
    wave31RemainingFieldNames.contains "hbuchstab" = true ∧
      wave31RemainingFieldNames.contains "hparity" = true :=
  ⟨by decide, by decide⟩

/-- **The complete remaining L21.2 analytic input** is exactly the Riemann
hypothesis and the central short count. -/
theorem wave31_l21_remaining (I : PaperResidualFor31 E D) :
    RiemannZetaZerosOnLine ∧
      ShortIntervalSmoothCountLower elementaryX elementaryC elementaryX :=
  ⟨I.l21.zetaRH, I.l21.localCount⟩

/-- **The complete remaining L34 analytic input**, with the Stark field derived
by the Wave-28 block. -/
theorem wave31_l34_remaining (I : PaperResidualFor31 E D) :
    DedekindZeroFreeInput I.l34.beta0 I.l34.zeroRealPart I.l34.cz
        I.l34.discLog ∧
      ChebotarevResidualInput I.l34.C I.l34.cZ (cutoff I.l34.T) I.l34.degree
        I.l34.count I.l34.liX I.l34.liBeta0 ∧
      ChebotarevT6RangeInput I.l34.K I.l34.T I.l34.degree I.l34.discLog ∧
      (∀ n, I.l34.beta0 n ≤ 1 / 2) :=
  wave29_l34_remaining I.toPaperResidualFor29

/-- The L30 loss of the record is exactly the H.3 failure probability, and the
L34 loss is exactly the actual probe miss: the reduction does not change any
loss. -/
theorem wave31_losses (I : PaperResidualFor31 E D) (n : ℕ) :
    (wave15L34Leaf I.l34.toL34ChebotarevSidesInputs).loss n = I.l34.actualMiss n ∧
      I.l30.toWave26L30Inputs.toSubexpLeaf.loss n = I.l30.failure.failure n :=
  ⟨wave29Slots_l34_loss_eq I.l34 n, Wave31L30Inputs.toWave26L30Inputs_loss_eq I.l30 n⟩

/-! ## Axiom audit -/

#print axioms Wave31L30Counts.theta_nonneg
#print axioms Wave31L30Counts.theta_pos
#print axioms Wave31L30Counts.short_interval
#print axioms Wave31L30Counts.short_interval_half
#print axioms Wave31L30Counts.short_interval_three_eighths
#print axioms Wave31L30Counts.sharpUpper
#print axioms Wave31L30Counts.globalLower
#print axioms Wave31L30Counts.err_ge_neg_one
#print axioms Wave31L30Counts.eventually_p_ge_two
#print axioms Wave31L30Counts.toWave26L30Counts
#print axioms Wave31L30Counts.toWave26L30Counts_short_interval
#print axioms Wave31L30Counts.toWave26L30Counts_c
#print axioms Wave31L30Inputs.toWave26L30Inputs
#print axioms Wave31L30Inputs.toWave26L30Inputs_short_interval
#print axioms Wave31L30Inputs.toWave26L30Inputs_data
#print axioms Wave31L30Inputs.toSubexpLeaf
#print axioms Wave31L30Inputs.loss_eq
#print axioms Wave31L30Inputs.toWave26L30Inputs_loss_eq
#print axioms wave31Slots
#print axioms wave31Slots_eq_wave29Slots
#print axioms wave31Slots_l30_loss_eq
#print axioms PaperResidualFor31.toPaperResidualFor29
#print axioms PaperResidualFor31.toPaperResidualFor29_l30
#print axioms PaperResidualFor31.toPaperResidualFor29_l30_short_interval
#print axioms PaperResidualFor31.toPaperResidualFor29_l21_l34_p1
#print axioms PaperResidualFor31.toPaperResidualFor29_l30_loss_eq
#print axioms PaperResidualFor31.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor31Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave31Inputs
#print axioms wave31L30CountsFieldNames_length
#print axioms wave31L30_no_shortInterval_field
#print axioms wave31RemainingL30FieldNames_length
#print axioms wave31_l30_remaining
#print axioms wave31_l30_short_interval_derived
#print axioms wave31_l30_remaining_of_record
#print axioms wave31_sharpUpper_derived
#print axioms wave31_globalLower_derived
#print axioms wave31FieldNames_length
#print axioms wave31RemainingFieldNames_length
#print axioms wave31_no_shortInterval_residual
#print axioms wave31_residual_has_buchstab_parity
#print axioms wave31_l21_remaining
#print axioms wave31_l34_remaining
#print axioms wave31_losses

end Cogentic.RandomizedPaperEndpointWave31
