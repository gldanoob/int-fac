import Cogentic.RandomizedPaperEndpointWave24
import Cogentic.RandomizedL30PrimeReciprocal

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 25: removing the L30 sharp-upper analytic field

The Wave-24 E-generic record `PaperResidualFor` still carries the L30 block
`Wave14L30Inputs`, whose counts contain the analytic field

```
global_upper : GlobalOddUpperDensitySharp C p ε.
```

That field is now *unconditional* in the arithmetic parameters: for every
`p` with `PaperDensityGrowth p` and every `ε > 0`, the sharp global odd upper
density at constant `1` is the theorem
`RandomizedL30PrimeReciprocal.paperScaleSmoothUpperSharp_one_unconditional`
(composed with `globalOddUpperDensitySharp_of_paperScaleSharp`), and the
predicate is monotone in the constant `C`.  Hence, whenever the arithmetic
constant satisfies `1 ≤ C`, the field is derived rather than assumed.

This file makes that reduction explicit:

* `Wave25L30Counts` is `Wave14L30Counts` with the analytic `global_upper` field
  replaced by the arithmetic field `l30C_ge_one : 1 ≤ C`, and with the two
  elementary hypotheses used by the derivation, `growth : PaperDensityGrowth p`
  and `ε_pos : 0 < ε`;
* `globalOddUpperDensitySharp_mono` proves monotonicity in `C`, and
  `Wave25L30Counts.sharpUpper` derives
  `GlobalOddUpperDensitySharp C p ε` from the unconditional constant-`1`
  theorem and `1 ≤ C`;
* `Wave25L30Inputs` is `Wave14L30Inputs` with `counts : Wave25L30Counts`;
  `Wave25L30Inputs.toWave14L30Inputs` fills `global_upper` with the derived
  proof and leaves every other field unchanged;
* `PaperResidualFor25` is the Wave-24 E-generic record with
  `l30 : Wave25L30Inputs`; `PaperResidualFor25.toPaperResidualFor` transports it
  to the Wave-24 record, and
  `serialized_assembled_balancedEnvelopeInfimum_from_wave25Inputs` is the
  E-generic endpoint obtained from the Wave-24 endpoint.  The epoch family `E`
  stays quantified inside the conclusion.

The remaining L30 analytic fields are stated explicitly:
`l30SharpCentral` (`short_interval`) and `l30Binomial` (`global_binomial`).
No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss,
probability or error is set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave25

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30PrimeReciprocal
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL34ChebotarevSides
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
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit
open Cogentic.RandomizedC1C2FromConcrete
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver

universe u

/-! ## Monotonicity of the sharp global upper density in the constant -/

/-- **`GlobalOddUpperDensitySharp` is monotone in the constant `C`.**

The right-hand side is `C * exp (…)` with a nonnegative exponential factor, so
increasing `C` can only weaken the eventual upper bound. -/
theorem globalOddUpperDensitySharp_mono {C C' : ℝ} (hCC' : C ≤ C')
    {p : ℕ → ℝ} {ε : ℝ}
    (h : GlobalOddUpperDensitySharp C p ε) :
    GlobalOddUpperDensitySharp C' p ε := by
  filter_upwards [h] with n hn
  have hexp : 0 ≤
      Real.exp (-(paperDensityU p ε n * Real.log (paperDensityU p ε n))) :=
    (Real.exp_pos _).le
  exact hn.trans (mul_le_mul_of_nonneg_right hCC' hexp)

/-- **The sharp global odd upper density from the unconditional constant-`1`
bound and `1 ≤ C`.**  This is the exact composition used by the Wave-25 L30
counts. -/
theorem globalOddUpperDensitySharp_of_one_le {p : ℕ → ℝ} {ε : ℝ}
    (hgrowth : PaperDensityGrowth p) (hε : 0 < ε) {C : ℝ} (hC : 1 ≤ C) :
    GlobalOddUpperDensitySharp C p ε :=
  globalOddUpperDensitySharp_mono hC
    (globalOddUpperDensitySharp_of_paperScaleSharp hgrowth
      (paperScaleSmoothUpperSharp_one_unconditional hgrowth hε))

/-! ## The Wave-25 L30 counts -/

/-- **The Wave-25 L30 counts.**

It is the Wave-14 sourced counts with the analytic sharp-upper field
`global_upper : GlobalOddUpperDensitySharp C p ε` *removed*, replaced by

* the arithmetic inequality `l30C_ge_one : 1 ≤ C`;
* the elementary hypotheses `growth : PaperDensityGrowth p` and
  `ε_pos : 0 < ε` needed to invoke the unconditional constant-`1` theorem.

Every other field (`p`, `err`, `ε`, the constants `A`, `B`, `c`, `C`, the
sharp local interval count `short_interval`, the explicit binomial lower bound
`global_binomial` and the LPP superset) is copied verbatim. -/
structure Wave25L30Counts where
  /-- The prime whose genus-two order is counted. -/
  p : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The constant paper error underlying the sharp density statements. -/
  ε : ℝ
  /-- The relative error is the constant paper error. -/
  err_eq : err = paperError ε
  /-- The prime is at least two. -/
  p_ge_two : ∀ n, 2 ≤ p n
  /-- The relative error is at least `-1`, as in the paper's `1 + o(1)` regime. -/
  err_ge_neg_one : ∀ n, -1 ≤ err n
  /-- The finite set of quintic models attached to each order. -/
  fibreModels : ℕ → ℕ → Finset ℕ
  /-- The relative short-interval density constant. -/
  A : ℝ
  /-- The global smooth lower-bound constant. -/
  B : ℝ
  /-- The paper short-count constant. -/
  c : ℝ
  /-- The global odd upper-density constant. -/
  C : ℝ
  /-- `A > 0`. -/
  A_pos : 0 < A
  /-- `B > 0`. -/
  B_pos : 0 < B
  /-- The arithmetic relation `A B ≥ 4`. -/
  AB_ge_four : 4 ≤ A * B
  /-- The paper count dominates the relative density constant. -/
  AC_le : A * C ≤ c
  /-- **Younis's sharp paper interval count** at `t = t_p`, with the true
  exponent `u log u`. -/
  short_interval : YounisOddPaperSharpIntervalCount c p ε
  /-- **The explicit global odd binomial lower bound.** -/
  global_binomial : GlobalOddBinomialCount B p (paperT p) err
  /-- **The explicit raw LPP model superset.** -/
  lpp_superset : LPPModelSuperset p (paperT p) err fibreModels
  /-- Paper density growth of `p`; an elementary growth hypothesis, used by the
  unconditional sharp upper-density theorem. -/
  growth : PaperDensityGrowth p
  /-- `ε > 0`. -/
  ε_pos : 0 < ε
  /-- **The arithmetic constant bound replacing the analytic upper density.**
  `1 ≤ C`, so the unconditional constant-`1` bound implies the bound at `C`. -/
  l30C_ge_one : 1 ≤ C

namespace Wave25L30Counts

variable (S : Wave25L30Counts)

/-- **The derived sharp global odd upper density.**

This is not a field: it follows from
`paperScaleSmoothUpperSharp_one_unconditional` at `S.growth`, `S.ε_pos` and
from the arithmetic inequality `S.l30C_ge_one`, together with monotonicity in
the constant. -/
theorem sharpUpper :
    GlobalOddUpperDensitySharp S.C S.p S.ε :=
  globalOddUpperDensitySharp_of_one_le S.growth S.ε_pos S.l30C_ge_one

/-- The sharp upper-density field is genuinely unconditional: the record
supplies `S.growth`, `S.ε_pos` and `S.l30C_ge_one`, and no other hypothesis is
needed. -/
theorem sharpUpper_unconditional :
    GlobalOddUpperDensitySharp S.C S.p S.ε :=
  S.sharpUpper

/-- The remaining sharp central interval-count field (`l30SharpCentral`). -/
theorem l30SharpCentral :
    YounisOddPaperSharpIntervalCount S.c S.p S.ε :=
  S.short_interval

/-- The remaining explicit binomial lower-bound field (`l30Binomial`). -/
theorem l30Binomial :
    GlobalOddBinomialCount S.B S.p (paperT S.p) S.err :=
  S.global_binomial

/-- **The wave-14 counts from the wave-25 counts.**  The only changed field is
`global_upper`, which is filled with the derived proof `S.sharpUpper`; every
other field is passed through unchanged. -/
noncomputable def toWave14L30Counts : Wave14L30Counts where
  p := S.p
  err := S.err
  ε := S.ε
  err_eq := S.err_eq
  p_ge_two := S.p_ge_two
  err_ge_neg_one := S.err_ge_neg_one
  fibreModels := S.fibreModels
  A := S.A
  B := S.B
  c := S.c
  C := S.C
  A_pos := S.A_pos
  B_pos := S.B_pos
  AB_ge_four := S.AB_ge_four
  AC_le := S.AC_le
  short_interval := S.short_interval
  global_upper := S.sharpUpper
  global_binomial := S.global_binomial
  lpp_superset := S.lpp_superset

/-- The derived `global_upper` field is exactly `S.sharpUpper`. -/
theorem toWave14L30Counts_global_upper :
    S.toWave14L30Counts.global_upper = S.sharpUpper := rfl

/-- The transport leaves the prime sequence unchanged. -/
theorem toWave14L30Counts_p : S.toWave14L30Counts.p = S.p := rfl

/-- The transport leaves the upper-density constant unchanged. -/
theorem toWave14L30Counts_C : S.toWave14L30Counts.C = S.C := rfl

/-- The transport leaves the paper error unchanged. -/
theorem toWave14L30Counts_ε : S.toWave14L30Counts.ε = S.ε := rfl

end Wave25L30Counts

/-! ## The Wave-25 L30 inputs -/

/-- **The Wave-25 L30 replacement.**  The counts field is `Wave25L30Counts`; the
Cantor/H.5 data and the H.3 failure data are unchanged. -/
structure Wave25L30Inputs where
  /-- The short-interval/LPP/global-lower counts with the sharp upper field
  derived rather than assumed. -/
  counts : Wave25L30Counts
  /-- The Cantor/H.5 cost and correctness data. -/
  cantor : CantorCostInputs
  /-- The H.3 failure data, including the useful-prime split bound. -/
  failure : FailureData

namespace Wave25L30Inputs

variable (I : Wave25L30Inputs)

/-- **The wave-14 L30 inputs from the wave-25 inputs.**  The analytic upper
density is derived; the Cantor and failure data are unchanged. -/
noncomputable def toWave14L30Inputs : Wave14L30Inputs where
  counts := I.counts.toWave14L30Counts
  cantor := I.cantor
  failure := I.failure

/-- **The wave-13 L30 bundle**, obtained by composing the transport with the
wave-14 reduction. -/
noncomputable def toWave13L30Inputs : Wave13L30Inputs :=
  I.toWave14L30Inputs.toWave13L30Inputs

/-- The derived sharp upper density carried by the wave-25 inputs. -/
theorem sharpUpper :
    GlobalOddUpperDensitySharp I.counts.C I.counts.p I.counts.ε :=
  I.counts.sharpUpper

/-- The L30 ledger leaf is unchanged by the reduction. -/
theorem toWave14L30Inputs_toSubexpLeaf :
    I.toWave14L30Inputs.toSubexpLeaf = I.failure.toSubexpLeaf := rfl

/-- The L30 loss is still the actual H.3 failure probability. -/
theorem loss_eq (n : ℕ) :
    I.toWave14L30Inputs.toSubexpLeaf.loss n = I.failure.failure n := rfl

end Wave25L30Inputs

/-! ## The Wave-25 ledger -/

/-- **The wave-25 ledger.**  It is the wave-24 ledger at the transported
wave-14 L30 inputs; since the transport only fills the sharp upper field with a
proof, the numerical ledger is literally the same. -/
noncomputable def wave25Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : ConcreteLeafResidual) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave25L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave24Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
    l30.toWave14L30Inputs l34 p1

/-- The wave-25 ledger is definitionally the wave-24 ledger of the transport. -/
theorem wave25Slots_eq_wave24Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : ConcreteLeafResidual) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave25L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (p1 : SubexpPrepassInput) :
    wave25Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 =
      wave24Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30.toWave14L30Inputs l34 p1 := rfl

/-! ## The E-generic residual record -/

/-- **The Wave-25 E-generic residual record.**

This is exactly `PaperResidualFor` with

```
l30 : Wave14L30Inputs
```

replaced by

```
l30 : Wave25L30Inputs,
```

i.e. the L30 sharp global upper density is no longer assumed, only the
arithmetic inequality `1 ≤ C` (together with the elementary growth and
positivity data) is.  All E-specific fields, the concrete C5 data and the
ledger domination are unchanged; the ledger is `wave25Slots`, the wave-24
ledger of the transported L30 inputs. -/
structure PaperResidualFor25
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
  /-- **The whole L21.2 analytic input**: the zeta side and the literal central
  short-interval smooth count. -/
  l21 : ConcreteLeafResidual
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- **L30 with the sharp global upper density derived**, leaving only the
  sharp central count, the binomial lower bound and the H.3 failure data. -/
  l30 : Wave25L30Inputs
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
  /-- Adapter: the concrete C5 loss is dominated by the wave-25 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave25Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor25

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **`PaperResidualFor25 E D → PaperResidualFor E D`.**

The only L30 change is `l30 := I.l30.toWave14L30Inputs`, which fills the
`global_upper` field with the derived proof.  Every other field is passed
through unchanged, and the ledger domination is the same statement unfolded by
`wave25Slots`. -/
noncomputable def toPaperResidualFor (I : PaperResidualFor25 E D) :
    PaperResidualFor E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30.toWave14L30Inputs
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
    simpa only [wave25Slots] using I.loss_le n hN

/-- **The Wave-17 inputs directly from the Wave-25 residue.** -/
noncomputable def toWave17Inputs (I : PaperResidualFor25 E D) :
    Wave17Inputs E D :=
  I.toPaperResidualFor.toWave17Inputs

/-- **The fully discharged inputs from the Wave-25 residue.** -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor25 E D) :
    FullyDischargedInputs E D :=
  I.toPaperResidualFor.toFullyDischargedInputs

/-- The reduction keeps the whole L30 block: the transported counts are
`I.l30.counts.toWave14L30Counts`. -/
theorem toPaperResidualFor_l30 (I : PaperResidualFor25 E D) :
    I.toPaperResidualFor.l30 = I.l30.toWave14L30Inputs := rfl

/-- **The sharp global upper density is derived, not assumed.**  The transported
Wave-14 field is exactly the Wave-25 derived proof. -/
theorem toPaperResidualFor_l30_global_upper (I : PaperResidualFor25 E D) :
    I.toPaperResidualFor.l30.counts.global_upper =
      I.l30.counts.sharpUpper := rfl

/-- **Unconditional sharp upper density from the Wave-25 record.**  There are no
extra hypotheses: `sharpUpper` uses only `l30Growth`, `l30ε_pos` and
`l30C_ge_one`, all of which are fields of `Wave25L30Counts`. -/
theorem l30SharpUpper_unconditional (I : PaperResidualFor25 E D) :
    GlobalOddUpperDensitySharp I.l30.counts.C I.l30.counts.p I.l30.counts.ε :=
  I.l30.sharpUpper

/-- The reduction is the identity on every c1–c4 field. -/
theorem toPaperResidualFor_c (I : PaperResidualFor25 E D) :
    I.toPaperResidualFor.c1 = I.c1 ∧ I.toPaperResidualFor.c2 = I.c2 ∧
      I.toPaperResidualFor.c3 = I.c3 ∧ I.toPaperResidualFor.c4 = I.c4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The reduction is the identity on the concrete family, its adapter and the
C5 data. -/
theorem toPaperResidualFor_c5 (I : PaperResidualFor25 E D) :
    I.toPaperResidualFor.concrete = I.concrete ∧
      I.toPaperResidualFor.concrete_eq = I.concrete_eq ∧
      I.toPaperResidualFor.c5Data = I.c5Data :=
  ⟨rfl, rfl, rfl⟩

/-- The record is nonempty as a Wave-24 `PaperResidualFor`. -/
theorem nonempty_paperResidualFor (I : PaperResidualFor25 E D) :
    Nonempty (PaperResidualFor E D) :=
  ⟨I.toPaperResidualFor⟩

/-- The record is nonempty as a `Wave17Inputs`. -/
theorem nonempty_wave17Inputs (I : PaperResidualFor25 E D) :
    Nonempty (Wave17Inputs E D) :=
  ⟨I.toWave17Inputs⟩

end PaperResidualFor25

/-- **The schedule-indexed form of the Wave-25 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor25Schedule
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor25 (E s) D

/-! ## The E-generic endpoint -/

/-- **Wave-25 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** balanced-
schedule epoch family `E` which, at every valid ceiling, carries a
`PaperResidualFor25 (E s) D` record, the kernel-checked driver outputs a
permutation of `n.primeFactorsList` and has expected serialized bit cost
eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The epoch family `E` is quantified inside the conclusion, exactly as in the
Wave-24 endpoint; it is **not** specialized.  The proof transports each record
by `PaperResidualFor25.toPaperResidualFor` and applies
`serialized_assembled_balancedEnvelopeInfimum_from_wave24Inputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave25Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor25 (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave24Inputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toPaperResidualFor⟩

/-! ## Residual accounting -/

/-- The field names of the Wave-25 L30 counts.  Note that `global_upper` (the
analytic sharp upper density) is absent; `l30C_ge_one` is present instead. -/
def wave25L30CountsFieldNames : List String :=
  ["p", "err", "ε", "err_eq", "p_ge_two", "err_ge_neg_one", "fibreModels",
   "A", "B", "c", "C", "A_pos", "B_pos", "AB_ge_four", "AC_le",
   "short_interval", "global_binomial", "lpp_superset", "growth", "ε_pos",
   "l30C_ge_one"]

theorem wave25L30CountsFieldNames_length :
    wave25L30CountsFieldNames.length = 21 := rfl

/-- **There is no analytic `global_upper` field in the Wave-25 counts.** -/
theorem wave25L30_no_globalUpper_field :
    wave25L30CountsFieldNames.all (fun s => decide (s ≠ "global_upper")) = true := by
  decide

/-- The two remaining L30 analytic fields.  `l30SharpCentral` is the sharp
central interval count, `l30Binomial` the explicit global odd binomial lower
bound; the sharp global upper density is no longer among them. -/
def wave25RemainingL30FieldNames : List String :=
  ["l30SharpCentral", "l30Binomial"]

theorem wave25RemainingL30FieldNames_length :
    wave25RemainingL30FieldNames.length = 2 := rfl

/-- **The complete remaining L30 analytic input of the Wave-25 record.** -/
theorem wave25_l30_remaining (S : Wave25L30Counts) :
    YounisOddPaperSharpIntervalCount S.c S.p S.ε ∧
      GlobalOddBinomialCount S.B S.p (paperT S.p) S.err :=
  ⟨S.l30SharpCentral, S.l30Binomial⟩

/-- **The sharp upper density is not a residual field of the Wave-25 record**:
it is a theorem for every record. -/
theorem wave25_sharpUpper_derived {D : ℝ} (I : PaperResidualFor25 E D) :
    I.toPaperResidualFor.l30.counts.global_upper =
      globalOddUpperDensitySharp_mono I.l30.counts.l30C_ge_one
        (globalOddUpperDensitySharp_of_paperScaleSharp I.l30.counts.growth
          (paperScaleSmoothUpperSharp_one_unconditional I.l30.counts.growth
            I.l30.counts.ε_pos)) :=
  rfl

/-! ## Axiom audit -/

#print axioms globalOddUpperDensitySharp_mono
#print axioms globalOddUpperDensitySharp_of_one_le
#print axioms Wave25L30Counts.sharpUpper
#print axioms Wave25L30Counts.sharpUpper_unconditional
#print axioms Wave25L30Counts.l30SharpCentral
#print axioms Wave25L30Counts.l30Binomial
#print axioms Wave25L30Counts.toWave14L30Counts
#print axioms Wave25L30Counts.toWave14L30Counts_global_upper
#print axioms Wave25L30Inputs.toWave14L30Inputs
#print axioms Wave25L30Inputs.toWave13L30Inputs
#print axioms Wave25L30Inputs.sharpUpper
#print axioms Wave25L30Inputs.toWave14L30Inputs_toSubexpLeaf
#print axioms Wave25L30Inputs.loss_eq
#print axioms wave25Slots
#print axioms wave25Slots_eq_wave24Slots
#print axioms PaperResidualFor25.toPaperResidualFor
#print axioms PaperResidualFor25.toWave17Inputs
#print axioms PaperResidualFor25.toFullyDischargedInputs
#print axioms PaperResidualFor25.toPaperResidualFor_l30
#print axioms PaperResidualFor25.toPaperResidualFor_l30_global_upper
#print axioms PaperResidualFor25.l30SharpUpper_unconditional
#print axioms PaperResidualFor25.toPaperResidualFor_c
#print axioms PaperResidualFor25.toPaperResidualFor_c5
#print axioms PaperResidualFor25.nonempty_paperResidualFor
#print axioms PaperResidualFor25.nonempty_wave17Inputs
#print axioms PaperResidualFor25Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave25Inputs
#print axioms wave25L30CountsFieldNames_length
#print axioms wave25L30_no_globalUpper_field
#print axioms wave25RemainingL30FieldNames_length
#print axioms wave25_l30_remaining
#print axioms wave25_sharpUpper_derived

end Cogentic.RandomizedPaperEndpointWave25
