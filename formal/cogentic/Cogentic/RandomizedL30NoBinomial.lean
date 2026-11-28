import Cogentic.RandomizedL30LeafFromGRH
import Cogentic.RandomizedPaperEndpointWave13

set_option maxHeartbeats 2000000

/-!
# L30: the Wave-14 counts without the explicit binomial hypothesis

`Cogentic.RandomizedPaperEndpointWave14.Wave14L30Counts` carries the explicit
finite-set lower bound

* `global_binomial : GlobalOddBinomialCount B p (paperT p) err`

whose only use inside the record is to derive the pointwise global odd smooth
lower bound

* `global_lower : YounisOddGlobalLower B p (paperT p) err`

through `younisOddGlobalLower_of_binomialCount`.  The binomial count is
strictly stronger than the lower bound, but it is *not* needed by any consumer
of the record: `Wave14L30Counts.toWave13Counts` consumes only `global_lower`,
and `Cogentic.RandomizedL30SmoothDensity` proves the global lower bound
directly from `DirichletLZerosOnLine` plus the elementary growth hypothesis
`PaperDensityGrowth p` (`eventually_younisOddGlobalLower_paper`, with constant
`1/8`).

This file therefore builds the binomial-free variant

* `Wave14L30CountsNoBinomial`, whose fields are exactly those of
  `Wave14L30Counts` with `global_binomial` replaced by the pointwise
  `global_lower : YounisOddGlobalLower B p (paperT p) err`;

* `Wave14L30InputsNoBinomial`, `wave14SlotsNoBinomial` and
  `Wave14InputsNoBinomial`, the corresponding L30 bundle, ledger and
  E-generic endpoint record.

The adapters are

* `Wave14L30CountsNoBinomial.toWave13Counts` — the actual consumer, with no
  binomial field (this is the field-by-field replacement of
  `Wave14L30Counts.toWave13Counts`);
* `Wave14L30CountsNoBinomial.toWave14L30Counts` — the round trip: the
  binomial-free record plus an explicit `GlobalOddBinomialCount` gives back a
  literal `Wave14L30Counts`.  This shows the two records differ only by the
  binomial field, which the ledger never reads;
* `Wave14L30CountsNoBinomial.ofWave14L30Counts` — the forgetful direction,
  deriving the pointwise lower bound from the binomial count;
* `EventuallyL30Counts.toWave14L30CountsNoBinomial` — the eventual GRH leaf
  shifted to a pointwise record exactly as `EventuallyL30Counts.toWave13L30Counts`
  does, with **no** `hbin` argument;
* `ofPaperGRHWithB_noBinomial` — the fully GRH-sourced record, whose only
  premises are the GRH line hypothesis, `PaperDensityGrowth`, `0 < ε`,
  `0 < B ≤ 1/8`, `0 < A` with `4 ≤ A B`, `A C ≤ c`, and the sharp central
  count and sharp upper density.

The endpoint theorem
`serialized_assembled_balancedEnvelopeInfimum_from_wave14InputsNoBinomial`
mirrors `serialized_assembled_balancedEnvelopeInfimum_from_wave14Inputs` and
has no binomial hypothesis anywhere in the E-generic record.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss,
mass or error is set to zero.  The sharp central count, the sharp global upper
density, the canonical LPP superset and the H.3 failure data are kept exactly
as in wave 14.
-/

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
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL4
open Cogentic.RandomizedL4Bands
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Filter Real
open scoped BigOperators ENNReal

set_option warn.classDefReducibility false

universe u

namespace Cogentic.RandomizedL30NoBinomial

/-! ## 1. The binomial-free counts record -/

/-- **The wave-14 L30 counting data without the explicit binomial bound.**
Field for field this is `Wave14L30Counts`, except that the binomial lower bound
`global_binomial : GlobalOddBinomialCount B p (paperT p) err` is replaced by the
pointwise global odd smooth lower bound `global_lower` that it was used to
derive.  The sharp central interval count, the sharp global upper density, the
canonical LPP superset and every arithmetic side condition are unchanged. -/
structure Wave14L30CountsNoBinomial where
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
  /-- **The sharp global odd smooth upper density** at `u log u`. -/
  global_upper : GlobalOddUpperDensitySharp C p ε
  /-- **The pointwise global odd smooth lower bound.**  This is the field that
  `global_binomial` was used to prove; it is supplied directly here. -/
  global_lower : YounisOddGlobalLower B p (paperT p) err
  /-- **The explicit raw LPP model superset.** -/
  lpp_superset : LPPModelSuperset p (paperT p) err fibreModels

namespace Wave14L30CountsNoBinomial

variable (S : Wave14L30CountsNoBinomial)

/-- The paper scale is nonnegative (it is a square root). -/
theorem paperT_nonneg (n : ℕ) : 0 ≤ paperT S.p n :=
  Real.sqrt_nonneg _

/-- The relative error is nonnegative at the paper scale. -/
theorem one_add_err_mul_nonneg (n : ℕ) :
    0 ≤ (1 + S.err n) * paperT S.p n :=
  mul_nonneg (by linarith [S.err_ge_neg_one n]) (S.paperT_nonneg n)

/-- **The sharp paper-scale interval count.** -/
theorem paperSharpIntervalCount :
    YounisOddPaperSharpIntervalCount S.c S.p S.ε :=
  S.short_interval

/-- **The global odd lower bound carried by the record.**  This is a field, not
something derived from a binomial count. -/
theorem younisOddGlobalLower :
    YounisOddGlobalLower S.B S.p (paperT S.p) S.err :=
  S.global_lower

/-- **The raw LPP count from the explicit model superset.** -/
theorem lppRawLogModelCount :
    LPPRawLogModelCount S.p (paperT S.p) S.err S.fibreModels :=
  lppRawLogModelCount_of_modelSuperset S.p_ge_two S.lpp_superset

/-- **The LPP normalization** for the canonical polylogarithmic loss. -/
theorem lppNormalization :
    LPPNormalization S.p (paperT S.p) S.err (lppLogLoss S.p) :=
  lpp_normalization_logLoss S.p_ge_two (fun n => S.paperT_nonneg n)
    S.err_ge_neg_one

/-- The relative short-interval density, derived from the sharp interval count
and the sharp global odd upper density by `paperRelative_of_sharpUpper`. -/
theorem younisRelative :
    EventuallyYounisOddSharpRelativeShortInterval S.A S.p S.ε :=
  paperRelative_of_sharpUpper S.A_pos.le S.AC_le
    S.paperSharpIntervalCount S.global_upper

/-- **The wave-13 L30 counts.**  This is the consumer of the record and it
never mentions `global_binomial`: its `global_lower` is exactly the field
carried here.  The canonical loss is `lppLogLoss`; no count is set to zero. -/
noncomputable def toWave13Counts : Wave13L30Counts where
  p := S.p
  err := S.err
  ε := S.ε
  err_eq := S.err_eq
  p_ge_two := S.p_ge_two
  fibreModels := S.fibreModels
  Q := lppLogLoss S.p
  A := S.A
  B := S.B
  c := S.c
  C := S.C
  A_pos := S.A_pos
  B_pos := S.B_pos
  AB_ge_four := S.AB_ge_four
  AC_le := S.AC_le
  short_interval := S.paperSharpIntervalCount
  global_upper := S.global_upper
  global_lower := S.global_lower
  lpp_normalization := S.lppNormalization
  lpp_raw := S.lppRawLogModelCount

/-- **The binomial field is not read by the ledger consumer.**  The global
lower bound of `toWave13Counts` is definitionally the pointwise field
`global_lower`. -/
theorem toWave13Counts_global_lower :
    S.toWave13Counts.global_lower = S.global_lower :=
  rfl

/-- The derived Younis short-interval count carried by the record (at the
common shifted index). -/
theorem younisShortIntervalCount :
    YounisShortIntervalCount S.toWave13Counts.toYounisLPPInputs.p
      S.toWave13Counts.toYounisLPPInputs.t
      S.toWave13Counts.toYounisLPPInputs.err :=
  S.toWave13Counts.younisShortIntervalCount

/-- The derived LPP per-order fibre count carried by the record (at the common
shifted index). -/
theorem lppOrderFibreCount :
    LPPOrderFibreCount S.toWave13Counts.toYounisLPPInputs.p
      S.toWave13Counts.toYounisLPPInputs.t
      S.toWave13Counts.toYounisLPPInputs.err
      S.toWave13Counts.toYounisLPPInputs.fibreModels :=
  S.toWave13Counts.lppOrderFibreCount

/-- **The round trip to the literal wave-14 record.**  Given the explicit
binomial count, the binomial-free record constructs a valid
`Wave14L30Counts`.  Every other field, including the sharp central count and
the canonical LPP superset, is passed through unchanged; the point of the
binomial-free file is that no ledger consumer needs the extra argument. -/
noncomputable def toWave14L30Counts
    (hbin : GlobalOddBinomialCount S.B S.p (paperT S.p) S.err) :
    Wave14L30Counts where
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
  short_interval := S.paperSharpIntervalCount
  global_upper := S.global_upper
  global_binomial := hbin
  lpp_superset := S.lpp_superset

/-- **On the field the ledger reads, the round trip changes nothing.**  The
pointwise global lower bound of the reconstructed `Wave14L30Counts` is the
direct field of the binomial-free record (the two proofs are proofs of the same
proposition).  In particular the binomial bound is used only to re-derive a
field that is already present. -/
theorem toWave14L30Counts_toWave13Counts_global_lower
    (S : Wave14L30CountsNoBinomial)
    (hbin : GlobalOddBinomialCount S.B S.p (paperT S.p) S.err) :
    (S.toWave14L30Counts hbin).toWave13Counts.global_lower =
      S.toWave13Counts.global_lower :=
  Subsingleton.elim _ _

/-- The forgetful direction: a literal `Wave14L30Counts` gives the
binomial-free record, with `global_lower` derived from `global_binomial` by
`younisOddGlobalLower_of_binomialCount`. -/
noncomputable def ofWave14L30Counts (S : Wave14L30Counts) :
    Wave14L30CountsNoBinomial where
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
  global_upper := S.global_upper
  global_lower := younisOddGlobalLower_of_binomialCount S.global_binomial
  lpp_superset := S.lpp_superset

end Wave14L30CountsNoBinomial

/-! ## 2. The L30 bundle, ledger and E-generic inputs -/

/-- **The L30 bundle without the binomial hypothesis.**  The counts are the
binomial-free record; the Cantor/H.5 cost data and the H.3 failure data are
unchanged. -/
structure Wave14L30InputsNoBinomial where
  /-- The short-interval/LPP/global-lower counts. -/
  counts : Wave14L30CountsNoBinomial
  /-- The Cantor/H.5 cost and correctness data. -/
  cantor : CantorCostInputs
  /-- The H.3 failure data, including the useful-prime split bound. -/
  failure : FailureData

namespace Wave14L30InputsNoBinomial

variable (I : Wave14L30InputsNoBinomial)

/-- **The wave-13 L30 bundle.**  Built directly from the binomial-free counts,
so no `GlobalOddBinomialCount` appears anywhere. -/
noncomputable def toWave13L30Inputs : Wave13L30Inputs where
  counts := I.counts.toWave13Counts
  cantor := I.cantor
  failure := I.failure

/-- The reduced `AnalyticInputs`, with both counting fields discharged. -/
noncomputable def toAnalyticInputs : AnalyticInputs :=
  I.counts.toWave13Counts.toYounisLPPInputs.toAnalyticInputs I.cantor

/-- The reduced `L30Sub.PaperInputs`. -/
noncomputable def toPaperInputs : PaperInputs :=
  I.toAnalyticInputs.toPaperInputs

/-- The L30 ledger leaf: the actual H.3 failure probability. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  I.failure.toSubexpLeaf

/-- **The L30 loss is the actual H.3 failure probability.** -/
theorem loss_eq (n : ℕ) : I.toSubexpLeaf.loss n = I.failure.failure n :=
  rfl

/-- The Younis short-interval count carried by the record (at the common
shifted index). -/
theorem younisShortIntervalCount :
    YounisShortIntervalCount I.counts.toWave13Counts.toYounisLPPInputs.p
      I.counts.toWave13Counts.toYounisLPPInputs.t
      I.counts.toWave13Counts.toYounisLPPInputs.err :=
  I.counts.younisShortIntervalCount

/-- The LPP per-order fibre count carried by the record (at the common shifted
index). -/
theorem lppOrderFibreCount :
    LPPOrderFibreCount I.counts.toWave13Counts.toYounisLPPInputs.p
      I.counts.toWave13Counts.toYounisLPPInputs.t
      I.counts.toWave13Counts.toYounisLPPInputs.err
      I.counts.toWave13Counts.toYounisLPPInputs.fibreModels :=
  I.counts.lppOrderFibreCount

/-- **The round trip to the literal wave-14 L30 bundle**, given the explicit
binomial count. -/
noncomputable def toWave14L30Inputs
    (hbin : GlobalOddBinomialCount I.counts.B I.counts.p
      (paperT I.counts.p) I.counts.err) : Wave14L30Inputs where
  counts := I.counts.toWave14L30Counts hbin
  cantor := I.cantor
  failure := I.failure

/-- The forgetful direction from the literal wave-14 L30 bundle. -/
noncomputable def ofWave14L30Inputs (I : Wave14L30Inputs) :
    Wave14L30InputsNoBinomial where
  counts := Wave14L30CountsNoBinomial.ofWave14L30Counts I.counts
  cantor := I.cantor
  failure := I.failure

end Wave14L30InputsNoBinomial

/-- The L30 leaf used by the binomial-free wave ledger. -/
noncomputable def wave14L30LeafNoBinomial (I : Wave14L30InputsNoBinomial) :
    SubexpLeaf :=
  I.toSubexpLeaf

/-! ## 3. The binomial-free ledger -/

/-- The C5 ledger of the binomial-free wave-14 inputs.  It is exactly
`wave14Slots` with the L30 bundle fed through the binomial-free counts. -/
noncomputable def wave14SlotsNoBinomial
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : L21_2LeafData) (l27_data : L27_1Inputs)
    (l27_waterhouse : L27WaterhouseInputs l27_data)
    (l30 : Wave14L30InputsNoBinomial) (l34 : Wave13L34Inputs)
    (l4N : ℕ) (l4N_odd : Odd l4N) (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave13Slots l18_4 l19 (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf l21_2) l27_data l27_waterhouse l30.toWave13L30Inputs l34
    l4N l4N_odd (wave14P1Leaf p1)

/-- **The binomial-free ledger, term by term.**  Same twelve genuine slots as
`wave14Slots_total_eq`; no slot is dropped or set to zero. -/
theorem wave14SlotsNoBinomial_total_eq
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : L21_2LeafData) (l27_data : L27_1Inputs)
    (l27_waterhouse : L27WaterhouseInputs l27_data)
    (l30 : Wave14L30InputsNoBinomial) (l34 : Wave13L34Inputs)
    (l4N : ℕ) (l4N_odd : Odd l4N) (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave14SlotsNoBinomial l18_4 l19 l20_2 l20_4 l21_2 l27_data
        l27_waterhouse l30 l34 l4N l4N_odd p1).total n =
      l18_4.toInputs.loss n + l19.toL19Inputs.poisson.loss n +
        l19.toL19Inputs.zeroMode.loss n + l19.toL19Inputs.thin.loss n +
        (wave14L20_2Leaf l20_2).loss n + l20_4.toSubexpLeaf.loss n +
        (wave14L21_2Leaf l21_2).loss n +
        (wave13L27Leaf l27_data l27_waterhouse).loss n +
        (wave13L30Leaf l30.toWave13L30Inputs).loss n +
        (wave13L34Leaf l34).loss n +
        (wave13L4Leaf l4N l4N_odd).loss n + (wave14P1Leaf p1).loss n := by
  simpa only [wave14SlotsNoBinomial] using
    wave13Slots_total_eq l18_4 l19 (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
      (wave14L21_2Leaf l21_2) l27_data l27_waterhouse l30.toWave13L30Inputs l34
      l4N l4N_odd (wave14P1Leaf p1) n

/-- **The binomial-free E-generic inputs.**  The fields are those of
`Wave14Inputs` with `l30` replaced by `Wave14L30InputsNoBinomial`.  In
particular there is no `GlobalOddBinomialCount` hypothesis in the record. -/
structure Wave14InputsNoBinomial
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate. -/
  l19 : L19FullCertificate
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- L21.2: RH smooth numbers near integer centres, assembled. -/
  l21_2 : L21_2LeafData
  /-- The odd modulus of the L4 split-band realization. -/
  l4N : ℕ
  /-- The L4 modulus is odd. -/
  l4N_odd : Odd l4N
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The Waterhouse/Siegel data proving the L27.1 Deuring input. -/
  l27_waterhouse : L27WaterhouseInputs l27_data
  /-- L30: the binomial-free counts and the H.3 failure data. -/
  l30 : Wave14L30InputsNoBinomial
  /-- L34: the Dedekind strip, classical Stark and Chebotarev data. -/
  l34 : Wave13L34Inputs
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
  concrete_eq : ∀ n hN, E n hN = (concrete n hN).toHardEpochData
  /-- The W45 C5 certificate. -/
  c5 : ∀ n hN, @C5FullInputs n (concrete n hN) (sampleFintype hN (concrete n hN))
  /-- Adapter: the concrete C5 loss is dominated by the binomial-free ledger. -/
  loss_le : ∀ n hN,
    c5TotalLoss hN (concrete n hN) (c5 n hN) ≤
      (wave14SlotsNoBinomial l18_4 l19 l20_2 l20_4 l21_2 l27_data
        l27_waterhouse l30 l34 l4N l4N_odd p1).total n

namespace Wave14InputsNoBinomial

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The wave-13 inputs made from the binomial-free records.**  Every field is
passed through; the L30 bundle goes directly to `Wave13L30Inputs`, so the
binomial count is never required. -/
noncomputable def toWave13Inputs (I : Wave14InputsNoBinomial E D) :
    Wave13Inputs E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := wave14L20_2Leaf I.l20_2
  l20_4 := I.l20_4.toSubexpLeaf
  l21_2 := wave14L21_2Leaf I.l21_2
  l4N := I.l4N
  l4N_odd := I.l4N_odd
  l27_data := I.l27_data
  l27_waterhouse := I.l27_waterhouse
  l30 := I.l30.toWave13L30Inputs
  l34 := I.l34
  p1 := wave14P1Leaf I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5 := I.c5
  loss_le := by
    intro n hN
    simpa only [wave14SlotsNoBinomial] using I.loss_le n hN

/-- **The fully discharged inputs made from the binomial-free records.** -/
noncomputable def toFullyDischargedInputs (I : Wave14InputsNoBinomial E D) :
    FullyDischargedInputs E D :=
  I.toWave13Inputs.toFullyDischargedInputs

/-- **The binomial-free ledger is the fully discharged ledger.** -/
theorem toFullyDischargedInputs_slots (I : Wave14InputsNoBinomial E D) :
    I.toFullyDischargedInputs.toPaperAnalyticAssumptions.slots =
      wave14SlotsNoBinomial I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_waterhouse I.l30 I.l34 I.l4N I.l4N_odd I.p1 := by
  change I.toWave13Inputs.toFullyDischargedInputs.toPaperAnalyticAssumptions.slots = _
  rw [Wave13Inputs.toFullyDischargedInputs_slots]
  rfl

/-- **The paper endpoint inputs from the binomial-free records.** -/
noncomputable def toPaperEndpointInputs (I : Wave14InputsNoBinomial E D) :
    PaperEndpointInputs E D :=
  I.toFullyDischargedInputs.toPaperEndpointInputs

/-- The paper record produced by the binomial-free inputs has the
binomial-free ledger. -/
theorem toPaperEndpointInputs_paper_slots (I : Wave14InputsNoBinomial E D) :
    I.toPaperEndpointInputs.paper.slots =
      wave14SlotsNoBinomial I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_waterhouse I.l30 I.l34 I.l4N I.l4N_odd I.p1 :=
  I.toFullyDischargedInputs_slots

/-- The forgetful direction: a literal wave-14 input record gives the
binomial-free record.  This shows the binomial-free record is a strict
relaxation of `Wave14Inputs` (and that no information is lost for the ledger,
by `toWave13Inputs`). -/
noncomputable def ofWave14Inputs (I : Wave14Inputs E D) :
    Wave14InputsNoBinomial E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21_2 := I.l21_2
  l4N := I.l4N
  l4N_odd := I.l4N_odd
  l27_data := I.l27_data
  l27_waterhouse := I.l27_waterhouse
  l30 := Wave14L30InputsNoBinomial.ofWave14L30Inputs I.l30
  l34 := I.l34
  p1 := I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5 := I.c5
  loss_le := by
    intro n hN
    exact I.loss_le n hN

end Wave14InputsNoBinomial

/-! ## 4. The E-generic endpoint without the binomial hypothesis -/

/-- **Wave-14 paper endpoint, binomial-free.**  This is
`serialized_assembled_balancedEnvelopeInfimum_from_wave14Inputs` with the
`l30Binomial` hypothesis removed from the E-generic record: the L30 stage only
needs the pointwise global lower bound, which
`RandomizedL30SmoothDensity.eventually_younisOddGlobalLower_paper` supplies.

Under the critical-line hypothesis for Dirichlet L-functions, there is one
universal serialized factoring algorithm such that, for every
balanced-schedule epoch family carrying the full L18.4 and L19 certificates,
the L20.2/L20.4/L21.2 sources, P1, the L4 split-band realization, the L27
Waterhouse/Siegel data, the binomial-free L30 counts, the L34 data, C1–C4 and
the W45 C5 certificate, the kernel-checked driver always outputs a permutation
of `n.primeFactorsList` and has expected serialized bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`.

The proof is `serialized_assembled_balancedEnvelopeInfimum_from_wave13Inputs`
applied to `Wave14InputsNoBinomial.toWave13Inputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave14InputsNoBinomial
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        Wave14InputsNoBinomial (E s) D) →
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
    serialized_assembled_balancedEnvelopeInfimum_from_wave13Inputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toWave13Inputs⟩

/-! ## 5. From the eventual GRH leaf, with no binomial hypothesis -/

end Cogentic.RandomizedL30NoBinomial

namespace Cogentic.RandomizedL30LeafFromGRH

open Cogentic.RandomizedL30NoBinomial

/-- **The binomial-free wave-14 counts from the eventual L30 leaf.**  This is
exactly `EventuallyL30Counts.toWave13L30Counts`'s shift construction, but
producing the wave-14-shaped record: the eventual global lower bound
`S.global_lower` is made pointwise by shifting `p` by the common tail
threshold, and the canonical LPP family is inserted unconditionally.  Unlike
`EventuallyL30Counts.toWave14L30Counts`, there is **no** `hbin` argument. -/
noncomputable def EventuallyL30Counts.toWave14L30CountsNoBinomial
    (S : EventuallyL30Counts) : Wave14L30CountsNoBinomial := by
  classical
  have hglobE : EventuallyYounisOddGlobalLower S.B S.p (paperT S.p)
      (paperError S.ε) := by
    simpa only [S.err_eq] using S.global_lower
  let h := S.p_ge_two.and (S.err_ge_neg_one.and
    (S.short_interval.and (S.global_upper.and hglobE)))
  let N := eventuallyShift h
  let P : ℕ → ℝ := fun n => S.p (n + N)
  let E : ℕ → ℝ := paperError S.ε
  have hspec : ∀ n,
      (2 ≤ S.p (n + N)) ∧ (-1 ≤ S.ε) ∧
        (S.c * ((centralOrderInterval S.p (n + N)).card : ℝ) *
            Real.exp (-(paperDensityU S.p S.ε (n + N) *
              Real.log (paperDensityU S.p S.ε (n + N)))) ≤
          centralOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N)) ∧
        (globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N) /
            S.p (n + N) ^ 2 ≤
          S.C * Real.exp (-(paperDensityU S.p S.ε (n + N) *
            Real.log (paperDensityU S.p S.ε (n + N))))) ∧
        (S.B * S.p (n + N) ^ 2 *
            Real.exp (-(1 + S.ε) * paperT S.p (n + N)) ≤
          globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N)) := by
    intro n
    have h' := eventuallyShift_spec h n
    simpa only [h, N, S.err_eq, paperError] using h'
  refine
    { p := P
      err := E
      ε := S.ε
      err_eq := by simp only [E]
      p_ge_two := fun n => (hspec n).1
      err_ge_neg_one := fun n => (hspec n).2.1
      fibreModels := fun n m => lppModelMultiples P n m
      A := S.A
      B := S.B
      c := S.c
      C := S.C
      A_pos := S.A_pos
      B_pos := S.B_pos
      AB_ge_four := S.AB_ge_four
      AC_le := S.AC_le
      short_interval := Filter.Eventually.of_forall fun n => ?_
      global_upper := Filter.Eventually.of_forall fun n => ?_
      global_lower := fun n => ?_
      lpp_superset := fun n m hm => subset_rfl }
  · exact (hspec n).2.2.1
  · exact (hspec n).2.2.2.1
  · exact (hspec n).2.2.2.2

/-- **The binomial-free wave-14 L30 bundle from the eventual leaf.** -/
noncomputable def EventuallyL30Inputs.toWave14L30InputsNoBinomial
    (I : EventuallyL30Inputs) : Wave14L30InputsNoBinomial where
  counts := I.counts.toWave14L30CountsNoBinomial
  cantor := I.cantor
  failure := I.failure

/-- The bundle loss is still the actual H.3 failure probability. -/
theorem EventuallyL30Inputs.toWave14L30InputsNoBinomial_loss_eq
    (I : EventuallyL30Inputs) (n : ℕ) :
    (I.toWave14L30InputsNoBinomial).toSubexpLeaf.loss n =
      I.failure.failure n :=
  rfl

end Cogentic.RandomizedL30LeafFromGRH

namespace Cogentic.RandomizedL30NoBinomial

/-- **The fully GRH-sourced binomial-free counts record.**  The premises are
exactly: the GRH line hypothesis, `PaperDensityGrowth p`, `0 < ε`,
`0 < B ≤ 1/8`, `0 < A` with `4 ≤ A B`, `A C ≤ c`, the sharp central interval
count and the sharp global upper density.  The global lower bound is the
proved `eventually_younisOddGlobalLower_paper_of_le`; no binomial count is
assumed. -/
noncomputable def ofPaperGRHWithB_noBinomial
    (line : DirichletLZerosOnLine) (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) (hBle : B ≤ 1 / 8)
    (A : ℝ) (hA : 0 < A) (hAB : 4 ≤ A * B)
    (c C : ℝ) (hAC : A * C ≤ c)
    (hshort : YounisOddPaperSharpIntervalCount c p ε)
    (hupper : GlobalOddUpperDensitySharp C p ε) :
    Wave14L30CountsNoBinomial :=
  (EventuallyL30Counts.ofPaperGRHWithB line p h hε hB hBle A hA hAB c C hAC
    hshort hupper).toWave14L30CountsNoBinomial

/-- **The `B = 1/8` specialization**, matching
`EventuallyL30Counts.ofPaperGRH`.  Here `A ≥ 32` is forced by `4 ≤ A / 8`. -/
noncomputable def ofPaperGRH_noBinomial
    (line : DirichletLZerosOnLine) (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε : ℝ} (hε : 0 < ε)
    (A : ℝ) (hA : 0 < A) (hA32 : 32 ≤ A)
    (c C : ℝ) (hAC : A * C ≤ c)
    (hshort : YounisOddPaperSharpIntervalCount c p ε)
    (hupper : GlobalOddUpperDensitySharp C p ε) :
    Wave14L30CountsNoBinomial :=
  ofPaperGRHWithB_noBinomial line p h hε (B := 1 / 8) (by norm_num) (by norm_num)
    A hA (by nlinarith) c C hAC hshort hupper

/-! ## Axiom audit -/

#print axioms Wave14L30CountsNoBinomial.paperT_nonneg
#print axioms Wave14L30CountsNoBinomial.one_add_err_mul_nonneg
#print axioms Wave14L30CountsNoBinomial.paperSharpIntervalCount
#print axioms Wave14L30CountsNoBinomial.younisOddGlobalLower
#print axioms Wave14L30CountsNoBinomial.lppRawLogModelCount
#print axioms Wave14L30CountsNoBinomial.lppNormalization
#print axioms Wave14L30CountsNoBinomial.younisRelative
#print axioms Wave14L30CountsNoBinomial.toWave13Counts
#print axioms Wave14L30CountsNoBinomial.toWave13Counts_global_lower
#print axioms Wave14L30CountsNoBinomial.younisShortIntervalCount
#print axioms Wave14L30CountsNoBinomial.lppOrderFibreCount
#print axioms Wave14L30CountsNoBinomial.toWave14L30Counts
#print axioms Wave14L30CountsNoBinomial.toWave14L30Counts_toWave13Counts_global_lower
#print axioms Wave14L30CountsNoBinomial.ofWave14L30Counts
#print axioms Wave14L30InputsNoBinomial.toWave13L30Inputs
#print axioms Wave14L30InputsNoBinomial.toAnalyticInputs
#print axioms Wave14L30InputsNoBinomial.toPaperInputs
#print axioms Wave14L30InputsNoBinomial.toSubexpLeaf
#print axioms Wave14L30InputsNoBinomial.loss_eq
#print axioms Wave14L30InputsNoBinomial.younisShortIntervalCount
#print axioms Wave14L30InputsNoBinomial.lppOrderFibreCount
#print axioms Wave14L30InputsNoBinomial.toWave14L30Inputs
#print axioms Wave14L30InputsNoBinomial.ofWave14L30Inputs
#print axioms wave14L30LeafNoBinomial
#print axioms wave14SlotsNoBinomial
#print axioms wave14SlotsNoBinomial_total_eq
#print axioms Wave14InputsNoBinomial.toWave13Inputs
#print axioms Wave14InputsNoBinomial.toFullyDischargedInputs
#print axioms Wave14InputsNoBinomial.toFullyDischargedInputs_slots
#print axioms Wave14InputsNoBinomial.toPaperEndpointInputs
#print axioms Wave14InputsNoBinomial.toPaperEndpointInputs_paper_slots
#print axioms Wave14InputsNoBinomial.ofWave14Inputs
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave14InputsNoBinomial
#print axioms EventuallyL30Counts.toWave14L30CountsNoBinomial
#print axioms EventuallyL30Inputs.toWave14L30InputsNoBinomial
#print axioms EventuallyL30Inputs.toWave14L30InputsNoBinomial_loss_eq
#print axioms ofPaperGRHWithB_noBinomial
#print axioms ofPaperGRH_noBinomial

end Cogentic.RandomizedL30NoBinomial
