import Cogentic.RandomizedPaperEndpointWave13
import Cogentic.RandomizedL20_2ConcentrationLeaf
import Cogentic.RandomizedL20_4LeafAssembly
import Cogentic.RandomizedL21_2LeafAssembly
import Cogentic.RandomizedP1Prepass
import Cogentic.RandomizedL30ShortInterval
import Cogentic.RandomizedL30GlobalLower

/-!
# Wave 14: the paper endpoint with the L20.2, L20.4, L21.2, P1 and L30 leaves
sourced

`Cogentic.RandomizedPaperEndpointWave13.Wave13Inputs` still takes five of the
twelve paper leaves opaquely:

* `l20_2 : ConcentrationLeaf`;
* `l20_4 : SubexpLeaf`;
* `l21_2 : RatedLeaf`;
* `p1 : P1Leaf`;
* and the counting half of `Wave13L30Inputs` (the Younis/LPP bundle).

The intervening waves have reduced each of these to explicit records that are
already proved to imply the corresponding leaf:

* **L20.2** — `RandomizedL20_2ConcentrationLeaf.SaddleConcentrationSource` keeps
  only the finite-cell concentration data; the saddle scale and saddle mean are
  the *proved* paper-mass lower bounds, and the CRT tail is the proved
  `geometricCRTError`.  Its `toConcentrationLeaf` has the genuine normalized
  mean discrepancy as loss.
* **L20.4** — `RandomizedL20_4LeafAssembly.L20_4SourcedLeafInputs` bundles the
  corrected disjunction-event pair data, the fully sourced top data
  (`SourcedTopData`, with `ε_rat`, `ε_in`, `η` and the base concentration all
  derived from the L20.2/L21.2 sources) and the deterministic dyad trimming.  Its
  loss is `pair.loss + dyad.loss + top.top`.
* **L21.2** — `RandomizedL21_2LeafAssembly.L21_2LeafData.ratedLeaf` is the
  assembled rated leaf; its loss is the literal bad-centre fraction
  `badCount / (X + 1)`.
* **P1** — `RandomizedP1Prepass.SubexpPrepassInput.toP1Leaf` has the genuine
  miss probability as loss and the explicit `exp (o(H))` cost exponent.
* **L30 counts** — `RandomizedL30ShortInterval` supplies the explicit
  fixed-density short-interval count, `RandomizedL30GlobalLower` supplies the
  explicit global odd binomial count and the canonical LPP raw/normalization
  data.  Their composition gives the paper short count, the global lower bound
  and the LPP per-order fibre count with no analytic input left in the bundle.

The new record `Wave14Inputs` therefore replaces those five fields by

* `l20_2 : SaddleConcentrationSource`;
* `l20_4 : Wave14L20_4Source` (a type-erased carrier for
  `L20_4SourcedLeafInputs`);
* `l21_2 : L21_2LeafData`;
* `p1 : SubexpPrepassInput`;
* `l30 : Wave14L30Inputs` (short-interval count, global binomial lower bound,
  LPP superset/normalization, Cantor/H.5 data and the H.3 failure data),

while keeping the two certificates, L27, L34, L4, C1–C4, the W45 C5
certificate and the three concrete adapters exactly as in wave 13.

The file proves

* `Wave14Inputs.toWave13Inputs` : the wave-13 record;
* `Wave14Inputs.toFullyDischargedInputs` : the fully discharged inputs;
* `Wave14Inputs.toFullyDischargedInputs_slots` : the ledger identity;
* `Wave14Inputs.toPaperEndpointInputs` : the paper endpoint inputs;
* `serialized_assembled_balancedEnvelopeInfimum_from_wave14Inputs` : the
  endpoint, obtained by composing with
  `RandomizedPaperEndpointWave13
  .serialized_assembled_balancedEnvelopeInfimum_from_wave13Inputs`.

Every loss is a genuine nonnegative deficit.  No `sorry`, `admit`, `axiom` or
`native_decide` is used, and no loss, count, mass or error is set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave14

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
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL4
open Cogentic.RandomizedL4Bands
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real
open scoped BigOperators ENNReal

set_option warn.classDefReducibility false

universe u

/-! ## L20.2: the paper-mass concentration source -/

/-- The L20.2 ledger leaf, built from the paper-mass concentration source.  Its
loss is the normalized mean discrepancy against the paper-mass saddle mean. -/
noncomputable def wave14L20_2Leaf (S : SaddleConcentrationSource) :
    ConcentrationLeaf :=
  S.toConcentrationLeaf

/-- **The L20.2 loss is the genuine normalized discrepancy.** -/
theorem wave14L20_2Leaf_loss (S : SaddleConcentrationSource) (n : ℕ) :
    (wave14L20_2Leaf S).loss n =
      |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| /
        paperSaddleMass n :=
  S.loss_eq n

/-- The manuscript concentration rate for the sourced leaf. -/
theorem wave14L20_2Leaf_paper (S : SaddleConcentrationSource) :
    ∀ᶠ n : ℕ in atTop,
      (wave14L20_2Leaf S).loss n ≤
        Real.exp (-(2 : ℝ) * Real.exp (S.a * scale n) * scale n) :=
  S.paper_bound

/-! ## L20.4: the sourced disjunction-event leaf -/

/-- A type-erased carrier for `L20_4SourcedLeafInputs`.  The source is indexed by
the finite probability space `Ω` and the dyad parameter type `P`; the carrier
keeps those explicit so that the whole endpoint record need not mention them. -/
structure Wave14L20_4Source where
  /-- The finite probability space of the pool data. -/
  Ω : Type u
  /-- The dyad parameter type. -/
  P : Type u
  /-- The probability space is finite. -/
  instΩ : Fintype Ω
  /-- The dyad parameter type has decidable equality. -/
  instP : DecidableEq P
  /-- The sourced L20.4 data. -/
  data : @L20_4SourcedLeafInputs Ω P instΩ instP

namespace Wave14L20_4Source

variable (S : Wave14L20_4Source)

/-- The L20.4 ledger leaf, built from the sourced data. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  @L20_4SourcedLeafInputs.toSubexpLeaf S.Ω S.P S.instΩ S.instP S.data

/-- **The L20.4 loss is the assembled genuine deficit**
`pair.loss + dyad.loss + top.top`. -/
theorem loss_eq (n : ℕ) : S.toSubexpLeaf.loss n =
    @L20_4SourcedLeafInputs.loss S.Ω S.P S.instΩ S.instP S.data n :=
  rfl

/-- The loss is nonnegative: each of the three summands is a genuine deficit. -/
theorem loss_nonneg (n : ℕ) : 0 ≤ S.toSubexpLeaf.loss n :=
  S.toSubexpLeaf.loss_nonneg n

/-- The manuscript `D^{-B}` bound for the sourced L20.4 leaf. -/
theorem subexpLoss : SubexpLoss S.toSubexpLeaf.loss :=
  S.toSubexpLeaf.paper

end Wave14L20_4Source

/-! ## L21.2: the assembled rated leaf -/

/-- The L21.2 ledger leaf, built from the assembled rated data. -/
noncomputable def wave14L21_2Leaf (D : L21_2LeafData) : RatedLeaf :=
  D.ratedLeaf

/-- **The L21.2 loss is the literal bad-centre fraction.** -/
theorem wave14L21_2Leaf_loss_eq_badFraction (D : L21_2LeafData) (n : ℕ) :
    (wave14L21_2Leaf D).loss n =
      D.toAbelInputs.toFourierInputs.badCount n /
        (D.toAbelInputs.toFourierInputs.X n + 1) :=
  D.ratedLeaf_loss_eq_badFraction n

/-- The L21.2 loss written as the fraction of bad sampled centres. -/
theorem wave14L21_2Leaf_loss_eq_card_fraction (D : L21_2LeafData) (n : ℕ) :
    (wave14L21_2Leaf D).loss n =
      ((D.toAbelInputs.toFourierInputs.badSet n).card : ℝ) /
        (D.profile.N n : ℝ) :=
  D.ratedLeaf_loss_eq_card_fraction n

/-- The manuscript rate `exp (-(c/64) T_X)` for the sourced L21.2 leaf. -/
theorem wave14L21_2Leaf_loss_le_manuscript (D : L21_2LeafData) :
    ∀ᶠ n : ℕ in atTop,
      (wave14L21_2Leaf D).loss n ≤ Real.exp (-((D.c / 64) * D.T n)) :=
  D.ratedLeaf_loss_le_manuscript

/-- The `D^{-B}` ledger slot of the sourced L21.2 leaf. -/
theorem wave14L21_2Leaf_loss_le_ledger (D : L21_2LeafData) :
    ∀ᶠ n : ℕ in atTop,
      (wave14L21_2Leaf D).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  D.ratedLeaf_loss_le_ledger

/-! ## P1: the explicit subexponential prepass -/

/-- The P1 ledger leaf, built from the explicit prepass input. -/
noncomputable def wave14P1Leaf (I : SubexpPrepassInput) : P1Leaf :=
  I.toP1Leaf

/-- **The P1 loss is the genuine prepass miss probability.** -/
theorem wave14P1Leaf_loss (I : SubexpPrepassInput) (n : ℕ) :
    (wave14P1Leaf I).loss n = I.miss n :=
  I.toP1Leaf_loss n

/-- The P1 success statement in manuscript form. -/
theorem wave14P1Leaf_paper (I : SubexpPrepassInput) :
    SubexpLoss (wave14P1Leaf I).loss :=
  (wave14P1Leaf I).paper

/-- The prepass cost exponent is the explicit little-o rate. -/
theorem wave14P1Leaf_cost_sublinear (I : SubexpPrepassInput) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      (wave14P1Leaf I).costExponent n ≤ δ * scale n :=
  (wave14P1Leaf I).cost_sublinear

/-! ## L30: the short-interval count and the global binomial lower bound -/

/-- **The sourced L30 counts.**  Compared with `Wave13L30Counts`, the opaque
paper short count is replaced by the explicit fixed-density short-interval count
of `RandomizedL30ShortInterval`, the global lower bound by the explicit binomial
count of `RandomizedL30GlobalLower`, and the raw/normalized LPP pair by the
explicit model superset.  The polylogarithmic loss is the canonical
`lppLogLoss`, so the normalization is proved rather than assumed. -/
structure Wave14L30Counts where
  /-- The prime whose genus-two order is counted. -/
  p : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
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
  /-- **The paper-scale short-interval count**, carrying the local density
  factor `exp (-(1+ε) t_p)`.  (The fixed-density form `c p^{3/2} ≤ count` would
  force `c ≤ 1` and is incompatible with `A B ≥ 4` and `A C ≤ c` whenever
  `B ≤ C`; the paper statement is the density form used here.) -/
  short_interval : YounisOddPaperShortCount c p (paperT p) err
  /-- The global odd smooth upper density. -/
  global_upper : GlobalOddUpperDensity C p (paperT p) err
  /-- **The explicit global odd binomial lower bound.** -/
  global_binomial : GlobalOddBinomialCount B p (paperT p) err
  /-- **The explicit raw LPP model superset.** -/
  lpp_superset : LPPModelSuperset p (paperT p) err fibreModels

namespace Wave14L30Counts

variable (S : Wave14L30Counts)

/-- The paper scale is nonnegative (it is a square root). -/
theorem paperT_nonneg (n : ℕ) : 0 ≤ paperT S.p n :=
  Real.sqrt_nonneg _

/-- The relative error is nonnegative at the paper scale. -/
theorem one_add_err_mul_nonneg (n : ℕ) :
    0 ≤ (1 + S.err n) * paperT S.p n :=
  mul_nonneg (by linarith [S.err_ge_neg_one n]) (S.paperT_nonneg n)

/-- **The paper-scale short count.** -/
theorem paperShortCount :
    YounisOddPaperShortCount S.c S.p (paperT S.p) S.err :=
  S.short_interval

/-- **The global odd lower bound from the explicit binomial count.** -/
theorem younisOddGlobalLower :
    YounisOddGlobalLower S.B S.p (paperT S.p) S.err :=
  younisOddGlobalLower_of_binomialCount S.global_binomial

/-- **The raw LPP count from the explicit model superset.** -/
theorem lppRawLogModelCount :
    LPPRawLogModelCount S.p (paperT S.p) S.err S.fibreModels :=
  lppRawLogModelCount_of_modelSuperset S.p_ge_two S.lpp_superset

/-- **The LPP normalization** for the canonical polylogarithmic loss. -/
theorem lppNormalization :
    LPPNormalization S.p (paperT S.p) S.err (lppLogLoss S.p) :=
  lpp_normalization_logLoss S.p_ge_two (fun n => S.paperT_nonneg n)
    S.err_ge_neg_one

/-- The relative short-interval density, derived from the paper short count and
the global odd upper density. -/
theorem younisRelative :
    YounisOddRelativeShortInterval S.A S.p (paperT S.p) S.err :=
  paperRelative_of_paperShortCount S.A_pos.le S.p_ge_two S.AC_le
    S.paperShortCount S.global_upper

/-- **The wave-13 counts from the explicit short-interval and global-lower
data.**  The canonical loss is `lppLogLoss`; no count is set to zero. -/
noncomputable def toWave13Counts : Wave13L30Counts where
  p := S.p
  err := S.err
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
  short_interval := S.paperShortCount
  global_upper := S.global_upper
  global_lower := S.younisOddGlobalLower
  lpp_normalization := S.lppNormalization
  lpp_raw := S.lppRawLogModelCount

/-- The derived Younis short-interval count carried by the record. -/
theorem younisShortIntervalCount :
    YounisShortIntervalCount S.p (paperT S.p) S.err :=
  S.toWave13Counts.younisShortIntervalCount

/-- The derived LPP per-order fibre count carried by the record. -/
theorem lppOrderFibreCount :
    LPPOrderFibreCount S.p (paperT S.p) S.err S.fibreModels :=
  S.toWave13Counts.lppOrderFibreCount

end Wave14L30Counts

/-- **The L30 replacement.**  The sourced counts, the Cantor/H.5 cost data, and
the H.3 failure data.  The ledger leaf is `failure.toSubexpLeaf`, the actual
failure probability; no count, cost or failure probability is set to zero. -/
structure Wave14L30Inputs where
  /-- The short-interval/LPP/global-lower counts. -/
  counts : Wave14L30Counts
  /-- The Cantor/H.5 cost and correctness data. -/
  cantor : CantorCostInputs
  /-- The H.3 failure data, including the useful-prime split bound. -/
  failure : FailureData

namespace Wave14L30Inputs

variable (I : Wave14L30Inputs)

/-- **The wave-13 L30 bundle from the sourced counts.** -/
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

/-- The L30 ledger leaf. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  I.failure.toSubexpLeaf

/-- **The L30 loss is the actual H.3 failure probability.** -/
theorem loss_eq (n : ℕ) : I.toSubexpLeaf.loss n = I.failure.failure n :=
  rfl

/-- The Younis short-interval count carried by the record. -/
theorem younisShortIntervalCount :
    YounisShortIntervalCount I.counts.p (paperT I.counts.p) I.counts.err :=
  I.counts.younisShortIntervalCount

/-- The LPP per-order fibre count carried by the record. -/
theorem lppOrderFibreCount :
    LPPOrderFibreCount I.counts.p (paperT I.counts.p) I.counts.err
      I.counts.fibreModels :=
  I.counts.lppOrderFibreCount

end Wave14L30Inputs

/-- The L30 leaf used by the wave ledger. -/
noncomputable def wave14L30Leaf (I : Wave14L30Inputs) : SubexpLeaf :=
  I.toSubexpLeaf

/-! ## The wave-14 ledger -/

/-- The C5 ledger of the wave-14 inputs: the two certificates, the leaves
produced from the wave records (L20.2, L20.4, L21.2, L27, L30, L34, L4, P1). -/
noncomputable def wave14Slots
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : L21_2LeafData) (l27_data : L27_1Inputs)
    (l27_waterhouse : L27WaterhouseInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : Wave13L34Inputs)
    (l4N : ℕ) (l4N_odd : Odd l4N) (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave13Slots l18_4 l19 (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf l21_2) l27_data l27_waterhouse l30.toWave13L30Inputs l34
    l4N l4N_odd (wave14P1Leaf p1)

/-- **The wave-14 ledger, term by term.**  The total is the sum of the two
certificate losses, the four remaining paper losses, and the eight produced
leaves.  In particular no slot is dropped or set to zero. -/
theorem wave14Slots_total_eq
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : L21_2LeafData) (l27_data : L27_1Inputs)
    (l27_waterhouse : L27WaterhouseInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : Wave13L34Inputs)
    (l4N : ℕ) (l4N_odd : Odd l4N) (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave14Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_waterhouse
        l30 l34 l4N l4N_odd p1).total n =
      l18_4.toInputs.loss n + l19.toL19Inputs.poisson.loss n +
        l19.toL19Inputs.zeroMode.loss n + l19.toL19Inputs.thin.loss n +
        (wave14L20_2Leaf l20_2).loss n + l20_4.toSubexpLeaf.loss n +
        (wave14L21_2Leaf l21_2).loss n +
        (wave13L27Leaf l27_data l27_waterhouse).loss n +
        (wave13L30Leaf l30.toWave13L30Inputs).loss n +
        (wave13L34Leaf l34).loss n +
        (wave13L4Leaf l4N l4N_odd).loss n + (wave14P1Leaf p1).loss n := by
  simpa only [wave14Slots] using
    wave13Slots_total_eq l18_4 l19 (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
      (wave14L21_2Leaf l21_2) l27_data l27_waterhouse l30.toWave13L30Inputs l34
      l4N l4N_odd (wave14P1Leaf p1) n

/-- **The wave-14 inputs.**  The five sourced leaves are explicit records; the
other fields are exactly those of `Wave13Inputs`. -/
structure Wave14Inputs
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
  /-- L30: the sourced counts and the H.3 failure data. -/
  l30 : Wave14L30Inputs
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
  /-- Adapter: the concrete C5 loss is dominated by the wave-14 ledger. -/
  loss_le : ∀ n hN,
    c5TotalLoss hN (concrete n hN) (c5 n hN) ≤
      (wave14Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_waterhouse
        l30 l34 l4N l4N_odd p1).total n

namespace Wave14Inputs

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The wave-13 inputs made from the wave-14 records.**  The five sourced
leaves are the proved wave reductions; every other field is passed through. -/
noncomputable def toWave13Inputs (I : Wave14Inputs E D) : Wave13Inputs E D where
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
    simpa only [wave14Slots] using I.loss_le n hN

/-- **The fully discharged inputs made from the wave-14 records.** -/
noncomputable def toFullyDischargedInputs (I : Wave14Inputs E D) :
    FullyDischargedInputs E D :=
  I.toWave13Inputs.toFullyDischargedInputs

/-- **The wave-14 ledger is the fully discharged ledger.** -/
theorem toFullyDischargedInputs_slots (I : Wave14Inputs E D) :
    I.toFullyDischargedInputs.toPaperAnalyticAssumptions.slots =
      wave14Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_waterhouse I.l30 I.l34 I.l4N I.l4N_odd I.p1 := by
  change I.toWave13Inputs.toFullyDischargedInputs.toPaperAnalyticAssumptions.slots = _
  rw [Wave13Inputs.toFullyDischargedInputs_slots]
  rfl

/-- **The paper endpoint inputs from the wave-14 inputs.** -/
noncomputable def toPaperEndpointInputs (I : Wave14Inputs E D) :
    PaperEndpointInputs E D :=
  I.toFullyDischargedInputs.toPaperEndpointInputs

/-- The paper record produced by the wave-14 inputs has the wave-14 ledger. -/
theorem toPaperEndpointInputs_paper_slots (I : Wave14Inputs E D) :
    I.toPaperEndpointInputs.paper.slots =
      wave14Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_waterhouse I.l30 I.l34 I.l4N I.l4N_odd I.p1 :=
  I.toFullyDischargedInputs_slots

end Wave14Inputs

/-! ## The endpoint -/

/-- **Wave-14 paper endpoint.**  Under the critical-line hypothesis for
Dirichlet L-functions, there is one universal serialized factoring algorithm
such that, for every balanced-schedule epoch family which, at every valid
ceiling, carries

* the full L18.4 certificate,
* the full L19 certificate,
* the L20.2 paper-mass concentration source,
* the sourced L20.4 disjunction-event data,
* the assembled L21.2 rated data,
* P1 with an explicit `exp (o(H))` cost rate,
* the proved L4 split-band realization,
* the L27 Waterhouse/Siegel data,
* the explicit L30 short-interval count, global binomial lower bound and H.3
  failure data,
* the L34 Dedekind strip, classical Stark and Chebotarev data,
* C1–C4, and
* the W45 C5 certificate,

the kernel-checked driver always outputs a permutation of `n.primeFactorsList`
and has expected serialized bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`, where
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof is
`RandomizedPaperEndpointWave13
.serialized_assembled_balancedEnvelopeInfimum_from_wave13Inputs` applied to
`Wave14Inputs.toWave13Inputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave14Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        Wave14Inputs (E s) D) →
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

/-! ## Axiom audit -/

#print axioms wave14L20_2Leaf
#print axioms wave14L20_2Leaf_loss
#print axioms wave14L20_2Leaf_paper
#print axioms Wave14L20_4Source.toSubexpLeaf
#print axioms Wave14L20_4Source.loss_eq
#print axioms Wave14L20_4Source.loss_nonneg
#print axioms Wave14L20_4Source.subexpLoss
#print axioms wave14L21_2Leaf
#print axioms wave14L21_2Leaf_loss_eq_badFraction
#print axioms wave14L21_2Leaf_loss_eq_card_fraction
#print axioms wave14L21_2Leaf_loss_le_manuscript
#print axioms wave14L21_2Leaf_loss_le_ledger
#print axioms wave14P1Leaf
#print axioms wave14P1Leaf_loss
#print axioms wave14P1Leaf_paper
#print axioms wave14P1Leaf_cost_sublinear
#print axioms Wave14L30Counts.paperT_nonneg
#print axioms Wave14L30Counts.one_add_err_mul_nonneg
#print axioms Wave14L30Counts.paperShortCount
#print axioms Wave14L30Counts.younisOddGlobalLower
#print axioms Wave14L30Counts.lppRawLogModelCount
#print axioms Wave14L30Counts.lppNormalization
#print axioms Wave14L30Counts.younisRelative
#print axioms Wave14L30Counts.toWave13Counts
#print axioms Wave14L30Counts.younisShortIntervalCount
#print axioms Wave14L30Counts.lppOrderFibreCount
#print axioms Wave14L30Inputs.toWave13L30Inputs
#print axioms Wave14L30Inputs.toAnalyticInputs
#print axioms Wave14L30Inputs.toPaperInputs
#print axioms Wave14L30Inputs.toSubexpLeaf
#print axioms Wave14L30Inputs.loss_eq
#print axioms Wave14L30Inputs.younisShortIntervalCount
#print axioms Wave14L30Inputs.lppOrderFibreCount
#print axioms wave14L30Leaf
#print axioms wave14Slots
#print axioms wave14Slots_total_eq
#print axioms Wave14Inputs.toWave13Inputs
#print axioms Wave14Inputs.toFullyDischargedInputs
#print axioms Wave14Inputs.toFullyDischargedInputs_slots
#print axioms Wave14Inputs.toPaperEndpointInputs
#print axioms Wave14Inputs.toPaperEndpointInputs_paper_slots
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave14Inputs

end Cogentic.RandomizedPaperEndpointWave14
