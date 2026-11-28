import Cogentic.RandomizedPaperEndpointWave14
import Cogentic.RandomizedL4BitBudget
import Cogentic.RandomizedL18_4ThinFinish
import Cogentic.RandomizedL19Full
import Cogentic.RandomizedL27StageOneFinish
import Cogentic.RandomizedL34ChebotarevSides
import Cogentic.RandomizedC5HitMassFinish

/-!
# Wave 15: the paper endpoint with the L4 bit budget, the L27.1 stage-one
finish, the L34 Chebotarev sides, the C5 count certificate and the L19.6
`ThinLatticeData` thin slot

`Cogentic.RandomizedPaperEndpointWave14.Wave14Inputs` still takes five pieces
of data at the level of the wave-14 reductions:

* the L4 algebraic leaf, parameterized by an odd modulus `l4N` and proved by the
  *maximal* split band `fullSplitBand l4N`;
* the L27.1 leaf, parameterized by `L27_1Inputs` together with the concrete
  Waterhouse data `L27WaterhouseInputs`;
* the L34 leaf, parameterized by the wave-13 `Wave13L34Inputs`;
* the whole W45 C5 certificate `c5 : C5FullInputs`;
* the L19.6 thin certificate `L19FullCertificate.thin : LatticeThinInputs`.

The intervening reductions replace each of these by strictly smaller proved
data:

* **L4** — `RandomizedL4BitBudget.realized_fullSplitBand_of_bitBudget` realizes
  every principal-genus injective tuple of the paper's *budgeted* band
  `paperSplitBand N k` from the two scalar hypotheses `Odd N` and
  `2 ^ k ≤ N`.  The cardinality form
  `unrealizedTuples_card_eq_zero_of_realized` then gives the L4 ledger slot.
  Thus the L4 loss is computed from a genuine bit-budget realization: no
  separate maximal-band assumption is used, only oddness and the explicit
  budget `2 ^ k ≤ N`.
* **L27.1** — `RandomizedL27StageOneFinish.L27StageOneFinishInputs` bundles the
  kill-mass/gcd-cover data, the Hurwitz/Deuring block, Hasse's theorem, the
  curve budget and the `log₂` multiplier.  Its `toRatedLeaf` proves every
  numeric stage-one field, so the L27 ledger leaf is `I.loss` with the two caps
  `exp (-2H)` and `exp (-(cRate/2) rate)` *proved*, not assumed.
* **L34** — `RandomizedL34ChebotarevSides.L34ChebotarevSidesInputs` fixes the
  cutoff `x = 2^(T^6)`, eliminates `h*` and `m`, and reduces the Chebotarev
  estimates to explicit scalar `Prop`s.  Its `ratedLeaf` has loss *exactly* the
  actual probe miss `actualMiss`.
* **C5** — `RandomizedC5HitMassFinish.c5FullOfCount` assembles a `C5FullInputs`
  from a pool budget, two stage budgets, the recognizer coupling, the uniform
  law, the H.8 half-mass count and the coupling/identity interface.  The total
  loss is the explicit positive sum of the five C5 slots.
* **L19.6 thin** — `RandomizedL18_4ThinFinish.ThinLatticeData` builds
  `LatticeThinInputs` from the determinant/volume count.  Its thin and
  small-determinant fractions are actual normalized lattice counts (both
  strictly positive), not free zeroes.

The new record `Wave15Inputs` therefore replaces the five wave-14 fields by

* `l4N`/`l4N_odd` plus the explicit bit budget `l4Bits`/`l4Bits_budget`;
* `l27_data`/`l27_finish : L27StageOneFinishInputs l27_data`;
* `l34 : L34ChebotarevSidesInputs`;
* `l19 : Wave15L19Inputs`, a copy of `L19FullCertificate` whose `thin` field is
  the `LatticeThinData`-built `LatticeThinInputs`;
* `c5Data : Wave15C5Data concrete`, assembled by `c5FullOfCount`,

while keeping L18.4, L20.2, L20.4, L21.2, L30, P1, C1–C4, the concrete-family
adapters and the C5 ledger bridge.

The file proves

* `Wave15L4Loss_zero` : the budgeted L4 defect is zero, from
  `realized_fullSplitBand_of_bitBudget`;
* `Wave15L27Leaf_loss`, `Wave15L34Leaf_loss_eq` : the genuine L27/L34 deficits;
* `Wave15C5Data.toC5_totalLoss` : the C5 total is the explicit positive sum;
* `Wave15L19Inputs.thin_loss_eq` and positivity of the thin slot;
* `wave15Slots` / `wave15Slots_total_eq` : the wave-15 ledger, term by term;
* `Wave15Inputs.toFullyDischargedInputs` : the fully discharged inputs;
* `Wave15Inputs.toFullyDischargedInputs_slots` : the ledger identity;
* `serialized_assembled_balancedEnvelopeInfimum_from_wave15Inputs` : the
  endpoint, obtained by composing with
  `RandomizedPaperEndpointFullyDischarged
  .serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs`.

Every loss is a genuine nonnegative deficit.  The L4 slot is the *proved*
algebraic identity (zero defect) of the bit-budget realization, not a discarded
estimate; the L27, L30, L34 and L19.6 losses are actual failure probabilities or
actual normalized counts and are positive at the same places as in the paper.
No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count,
mass or error is set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave15

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
open Cogentic.RandomizedL21_2LeafAssembly
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
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real
open scoped BigOperators ENNReal

set_option warn.classDefReducibility false

universe u

/-! ## L4: the paper's bit-budget split band -/

/-- The genuine algebraic defect of the paper's bit-budget band: the number of
realized principal-genus injective tuples of `paperSplitBand N bits` that fail
to lift to a reduced form of discriminant `-8N`. -/
noncomputable def wave15L4Loss (N bits : ℕ) : ℕ → ℝ :=
  fun _ => ((unrealizedTuples (N := N) (paperSplitBand N bits)).card : ℝ)

/-- The L4 defect as the literal unrealised-tuple cardinality. -/
theorem wave15L4Loss_eq_card (N bits n : ℕ) :
    wave15L4Loss N bits n =
      ((unrealizedTuples (N := N) (paperSplitBand N bits)).card : ℝ) :=
  rfl

/-- **The bit-budget L4 defect is zero.**  This is
`realized_fullSplitBand_of_bitBudget`: from `Odd N` and `2 ^ bits ≤ N`, every
principal-genus injective tuple of the paper's budgeted band is realized, so the
unrealised-tuple set is empty by
`unrealizedTuples_card_eq_zero_of_realized`.  No maximal-band or separate
realization assumption is used. -/
theorem wave15L4Loss_zero {N bits : ℕ} (hN : Odd N) (hbits : 2 ^ bits ≤ N)
    (n : ℕ) : wave15L4Loss N bits n = 0 := by
  unfold wave15L4Loss
  exact unrealizedTuples_card_eq_zero_of_realized
    (fun t hgenus hinj => realized_fullSplitBand_of_bitBudget hN hbits t hgenus hinj)

/-- The L4/L25/L36 ledger leaf from the proved bit-budget realization.  Its
zero deficit is the exactness of the Cox/squaring/split-band supply bridge on
the paper's budgeted band. -/
noncomputable def wave15L4Leaf (N bits : ℕ) (hN : Odd N) (hbits : 2 ^ bits ≤ N) :
    AlgebraicLeaf where
  loss := wave15L4Loss N bits
  loss_nonneg := fun n => (wave15L4Loss_zero hN hbits n).ge
  loss_zero := wave15L4Loss_zero hN hbits

/-- The ledger loss of the bit-budget L4 leaf. -/
theorem wave15L4Leaf_loss (N bits : ℕ) (hN : Odd N) (hbits : 2 ^ bits ≤ N)
    (n : ℕ) : (wave15L4Leaf N bits hN hbits).loss n = 0 :=
  wave15L4Loss_zero hN hbits n

/-! ## L27.1: the stage-one finish bundle -/

/-- The L27.1 ledger leaf from `L27StageOneFinishInputs`.  Its loss is literally
`L27_1Inputs.loss`, and both stage-one caps are proved in
`RandomizedL27StageOneFinish`. -/
noncomputable def wave15L27Leaf (I : L27_1Inputs)
    (F : L27StageOneFinishInputs I) : RatedLeaf :=
  F.toRatedLeaf

/-- **The L27.1 loss is the literal ECM deficit `I.loss`.** -/
theorem wave15L27Leaf_loss (I : L27_1Inputs) (F : L27StageOneFinishInputs I)
    (n : ℕ) : (wave15L27Leaf I F).loss n = I.loss n :=
  rfl

/-- The L27.1 `exp (-2H)` ledger slot, proved from the finish bundle. -/
theorem wave15L27Leaf_slot (I : L27_1Inputs) (F : L27StageOneFinishInputs I) :
    ∀ᶠ n : ℕ in atTop,
      (wave15L27Leaf I F).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  (wave15L27Leaf I F).slot

/-- The manuscript-rate cap carried by the finish bundle. -/
theorem wave15L27Leaf_paper (I : L27_1Inputs) (F : L27StageOneFinishInputs I) :
    ∀ᶠ n : ℕ in atTop,
      (wave15L27Leaf I F).loss n ≤
        Real.exp (-((wave15L27Leaf I F).c * (wave15L27Leaf I F).rate n)) :=
  (wave15L27Leaf I F).paper

/-! ## L34: the explicit Chebotarev sides -/

/-- The L34 ledger leaf from the explicit Chebotarev-side counting inputs. -/
noncomputable def wave15L34Leaf (S : L34ChebotarevSidesInputs) : RatedLeaf :=
  S.ratedLeaf

/-- **The L34 loss is exactly the actual probe miss.**  The mask slack cancels
against the paper's `1/128` allowance, leaving the genuine `actualMiss`. -/
theorem wave15L34Leaf_loss_eq (S : L34ChebotarevSidesInputs) (n : ℕ) :
    (wave15L34Leaf S).loss n = S.actualMiss n :=
  S.ratedLeaf_loss_eq n

/-- The L34 loss is nonnegative. -/
theorem wave15L34Leaf_loss_nonneg (S : L34ChebotarevSidesInputs) (n : ℕ) :
    0 ≤ (wave15L34Leaf S).loss n :=
  S.ratedLeaf_loss_nonneg n

/-- **The L34 loss is genuinely positive** wherever the probe stage actually
fails with positive probability. -/
theorem wave15L34Leaf_loss_pos (S : L34ChebotarevSidesInputs) {n : ℕ}
    (h : 0 < S.actualMiss n) : 0 < (wave15L34Leaf S).loss n :=
  S.ratedLeaf_loss_pos h

/-- The L34 `exp (-2H)` ledger slot. -/
theorem wave15L34Leaf_slot (S : L34ChebotarevSidesInputs) :
    ∀ᶠ n : ℕ in atTop,
      (wave15L34Leaf S).loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  S.ratedLeaf_slot

/-! ## C5: the count-assembled certificate -/

/-- **The explicit data behind `c5FullOfCount`.**  The pool coverage budget, the
two stage budgets, the recognizer coupling, the uniform ideal law, the H.8
half-mass count and the coupling/success interface.  The C5 certificate itself is
then *constructed*, not assumed. -/
structure Wave15C5Data
    (concrete : ∀ n, 3 ≤ n → ConcreteEpochData n) where
  /-- The C5.a pool-coverage budget. -/
  pool : ∀ n (_hN : 3 ≤ n), PoolCoverageBudget
  /-- The C5.b survivor-recurrence stage budget. -/
  survivor : ∀ n (hN : 3 ≤ n), StageBudget (concrete n hN)
  /-- The C5.c descent stage budget. -/
  descent : ∀ n (hN : 3 ≤ n), StageBudget (concrete n hN)
  /-- The C5.e recognizer coupling. -/
  coupling : ∀ n (hN : 3 ≤ n), CouplingInputs (concrete n hN)
  /-- The ideal law is uniform on the concrete finite sample space. -/
  huniform : ∀ n (hN : 3 ≤ n) (x : (concrete n hN).Sample),
    pmfWeight (concrete n hN).ideal x =
      (@Fintype.card ((concrete n hN).Sample)
        (sampleFintype hN (concrete n hN)) : ℝ)⁻¹
  /-- **The H.8 half-mass count.** -/
  hcount : ∀ n (hN : 3 ≤ n),
    @HalfMassCount n (concrete n hN) (sampleFintype hN (concrete n hN))
  /-- A successful transcript always passed the recognizer coupling. -/
  hcoupling : ∀ n (hN : 3 ≤ n) (x : (concrete n hN).Sample),
    solverSuccess (concrete n hN) x → ¬ (coupling n hN).fail x

namespace Wave15C5Data

variable {concrete : ∀ n, 3 ≤ n → ConcreteEpochData n}

/-- **The W45 C5 certificate assembled by `c5FullOfCount`.**  The event
identification is *proved* from the uniform law and the coupling interface. -/
noncomputable def toC5 (C : Wave15C5Data concrete) :
    ∀ n (hN : 3 ≤ n), @C5FullInputs n (concrete n hN) (sampleFintype hN (concrete n hN)) :=
  fun n hN =>
    @c5FullOfCount n (concrete n hN) (sampleFintype hN (concrete n hN))
      (C.pool n hN) (C.survivor n hN) (C.descent n hN) (C.coupling n hN)
      (C.huniform n hN) (C.hcount n hN) (C.hcoupling n hN)

/-- **The C5 total loss is the explicit five-slot sum**, with every summand a
proved nonnegative budget.  In particular the hit-mass bound is not a
zero-mass artifact. -/
theorem toC5_totalLoss (C : Wave15C5Data concrete) (n : ℕ) (hN : 3 ≤ n) :
    c5TotalLoss hN (concrete n hN) (C.toC5 n hN) =
      (C.pool n hN).loss + (C.survivor n hN).loss + (C.descent n hN).loss +
        (@algebraMass n (concrete n hN) (sampleFintype hN (concrete n hN)) +
          1 + 1 + 1) + (C.coupling n hN).loss := by
  unfold c5TotalLoss
  simpa only [Wave15C5Data.toC5] using
    @c5FullOfCount_totalLoss n (concrete n hN) (sampleFintype hN (concrete n hN))
      (C.pool n hN) (C.survivor n hN)
      (C.descent n hN) (C.coupling n hN) (C.huniform n hN) (C.hcount n hN)
      (C.hcoupling n hN)

/-- **The C5 total loss is positive** whenever the pool loss is positive: the
coupling loss is always positive and the algebra mass is nonnegative. -/
theorem toC5_totalLoss_pos (C : Wave15C5Data concrete) (n : ℕ) (hN : 3 ≤ n)
    (hpool : 0 < (C.pool n hN).loss) :
    0 < c5TotalLoss hN (concrete n hN) (C.toC5 n hN) := by
  rw [C.toC5_totalLoss n hN]
  have ha : 0 ≤ @algebraMass n (concrete n hN) (sampleFintype hN (concrete n hN)) :=
    @algebraMass_nonneg n (concrete n hN) (sampleFintype hN (concrete n hN))
  have hC : 0 < (C.coupling n hN).loss := (C.coupling n hN).loss_pos
  have hs : 0 ≤ (C.survivor n hN).loss := (C.survivor n hN).loss_nonneg
  have hd : 0 ≤ (C.descent n hN).loss := (C.descent n hN).loss_nonneg
  linarith only [hpool, ha, hC, hs, hd]

end Wave15C5Data

/-! ## L19.6: the `ThinLatticeData` thin certificate -/

/-- **The L19 full certificate with its L19.6 `thin` field sourced by
`ThinLatticeData`.**  This is exactly `L19FullCertificate`, except that the
`thin : LatticeThinInputs` field is replaced by the determinant/volume data
`thinData : ThinLatticeData` and the scale adapter.  The thin and
small-determinant fractions are therefore the actual normalized lattice counts
of `RandomizedL18_4ThinFinish`. -/
structure Wave15L19Inputs where
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
  /-- **The L18.4 determinant/volume data behind the L19.6 thin certificate.** -/
  thinData : ThinLatticeData
  /-- Scale adapter: the thin data uses the same `W = log V`. -/
  thin_W : thinData.W = I.W

namespace Wave15L19Inputs

variable (C : Wave15L19Inputs)

/-- **The full L19 certificate**, with the thin slot built from
`ThinLatticeData.toLatticeThinInputs`. -/
noncomputable def toL19FullCertificate : L19FullCertificate where
  I := C.I
  M₁ := C.M₁
  M₂ := C.M₂
  hc₁ := C.hc₁
  hη₁ := C.hη₁
  hE₁ := C.hE₁
  hc₂ := C.hc₂
  hη₂ := C.hη₂
  hE₂ := C.hE₂
  Dnum := C.Dnum
  Dden := C.Dden
  zeroMode := C.zeroMode
  thin := C.thinData.toLatticeThinInputs
  thin_W := C.thin_W

/-- The L19.6 thin-pair component supplied by the thin data. -/
noncomputable def toThinPairInputs :
    Cogentic.RandomizedL19SecondMoment.ThinPairInputs :=
  C.thinData.toLatticeThinInputs.toThinPairInputs

/-- **The L19.6 loss is the actual normalized thin plus small-determinant
count.** -/
theorem thin_loss_eq (n : ℕ) :
    C.toL19FullCertificate.toL19Inputs.thin.loss n =
      C.thinData.thin n + C.thinData.smallDet n :=
  rfl

/-- **The L19.6 thin fraction is genuinely positive**: it is at least `1/R` from
the diagonal pairs, with `R` the positive rational-good mark count. -/
theorem thin_pos (n : ℕ) : 0 < C.thinData.thin n :=
  C.thinData.thin_pos n

/-- **The L19.6 small-determinant fraction is genuinely positive.** -/
theorem smallDet_pos (n : ℕ) : 0 < C.thinData.smallDet n :=
  C.thinData.smallDet_pos n

/-- The L19.6 thin-pair loss is genuinely positive. -/
theorem thin_loss_pos (n : ℕ) :
    0 < C.toL19FullCertificate.toL19Inputs.thin.loss n := by
  rw [C.thin_loss_eq n]
  exact add_pos_of_pos_of_nonneg (C.thin_pos n) (C.smallDet_pos n).le

end Wave15L19Inputs

/-! ## The wave-15 ledger -/

/-- The C5 ledger of the wave-15 inputs: the two certificates, the L27.1 leaf
from the stage-one finish bundle, the L34 leaf from the Chebotarev sides, the L4
leaf from the bit-budget realization, and the remaining produced leaves. -/
noncomputable def wave15Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : L21_2LeafData) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (l4N l4Bits : ℕ) (l4N_odd : Odd l4N) (l4Bits_budget : 2 ^ l4Bits ≤ l4N)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  fullyDischargedSlots l18_4 l19.toL19FullCertificate
    (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf l21_2) (wave15L27Leaf l27_data l27_finish)
    l30.toSubexpLeaf (wave15L34Leaf l34)
    (wave15L4Leaf l4N l4Bits l4N_odd l4Bits_budget) (wave14P1Leaf p1)

/-- **The wave-15 ledger, term by term.**  The total is the sum of the two
certificate losses, the three L19 certificate losses, and the eight produced
leaves; in particular no slot is dropped or set to zero. -/
theorem wave15Slots_total_eq
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : L21_2LeafData) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (l4N l4Bits : ℕ) (l4N_odd : Odd l4N) (l4Bits_budget : 2 ^ l4Bits ≤ l4N)
    (p1 : SubexpPrepassInput) (n : ℕ) :
    (wave15Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish
        l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1).total n =
      l18_4.toInputs.loss n + l19.toL19FullCertificate.toL19Inputs.poisson.loss n +
        l19.toL19FullCertificate.toL19Inputs.zeroMode.loss n +
        l19.toL19FullCertificate.toL19Inputs.thin.loss n +
        (wave14L20_2Leaf l20_2).loss n + l20_4.toSubexpLeaf.loss n +
        (wave14L21_2Leaf l21_2).loss n +
        (wave15L27Leaf l27_data l27_finish).loss n +
        l30.toSubexpLeaf.loss n + (wave15L34Leaf l34).loss n +
        (wave15L4Leaf l4N l4Bits l4N_odd l4Bits_budget).loss n +
        (wave14P1Leaf p1).loss n := by
  simpa only [wave15Slots] using
    fullyDischargedSlots_total_eq l18_4 l19.toL19FullCertificate
      (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf (wave14L21_2Leaf l21_2)
      (wave15L27Leaf l27_data l27_finish) l30.toSubexpLeaf
      (wave15L34Leaf l34) (wave15L4Leaf l4N l4Bits l4N_odd l4Bits_budget)
      (wave14P1Leaf p1) n

/-- **The wave-15 inputs.**  The five sourced pieces replace the corresponding
wave-14 fields; the other fields are exactly those of `Wave14Inputs`. -/
structure Wave15Inputs
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
  /-- L21.2: RH smooth numbers near integer centres, assembled. -/
  l21_2 : L21_2LeafData
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
  /-- The L27.1 stage-one finish data (kill law, Hurwitz block, Hasse, budget,
  `log₂` multiplier). -/
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
  /-- Adapter: the concrete C5 loss is dominated by the wave-15 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave15Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish
        l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1).total n

namespace Wave15Inputs

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The fully discharged inputs made from the wave-15 records.**  The L4, L27,
L34, C5 and L19.6 thin fields are the proved wave-15 constructions; every other
field is passed through. -/
noncomputable def toFullyDischargedInputs (I : Wave15Inputs E D) :
    FullyDischargedInputs E D where
  l18_4 := I.l18_4
  l19 := I.l19.toL19FullCertificate
  l20_2 := wave14L20_2Leaf I.l20_2
  l20_4 := I.l20_4.toSubexpLeaf
  l21_2 := wave14L21_2Leaf I.l21_2
  l27_1 := wave15L27Leaf I.l27_data I.l27_finish
  l30 := I.l30.toSubexpLeaf
  l34 := wave15L34Leaf I.l34
  l4_l25_l36 := wave15L4Leaf I.l4N I.l4Bits I.l4N_odd I.l4Bits_budget
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
    simpa only [wave15Slots] using I.loss_le n hN

/-- **The wave-15 ledger is the fully discharged ledger.** -/
theorem toFullyDischargedInputs_slots (I : Wave15Inputs E D) :
    I.toFullyDischargedInputs.toPaperAnalyticAssumptions.slots =
      wave15Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_finish I.l30 I.l34 I.l4N I.l4Bits I.l4N_odd I.l4Bits_budget I.p1 := by
  rw [FullyDischargedInputs.toPaperAnalyticAssumptions_slots]
  rfl

/-- **The paper endpoint inputs from the wave-15 inputs.** -/
noncomputable def toPaperEndpointInputs (I : Wave15Inputs E D) :
    PaperEndpointInputs E D :=
  I.toFullyDischargedInputs.toPaperEndpointInputs

/-- The paper record produced by the wave-15 inputs has the wave-15 ledger. -/
theorem toPaperEndpointInputs_paper_slots (I : Wave15Inputs E D) :
    I.toPaperEndpointInputs.paper.slots =
      wave15Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_finish I.l30 I.l34 I.l4N I.l4Bits I.l4N_odd I.l4Bits_budget I.p1 :=
  I.toFullyDischargedInputs_slots

end Wave15Inputs

/-! ## The endpoint -/

/-- **Wave-15 paper endpoint.**  Under the critical-line hypothesis for
Dirichlet L-functions, there is one universal serialized factoring algorithm
such that, for every balanced-schedule epoch family which, at every valid
ceiling, carries

* the full L18.4 certificate,
* the L19 certificate with its thin slot built from `ThinLatticeData`,
* the L20.2 paper-mass concentration source,
* the sourced L20.4 disjunction-event data,
* the assembled L21.2 rated data,
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

The proof is
`RandomizedPaperEndpointFullyDischarged
.serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs` applied
to `Wave15Inputs.toFullyDischargedInputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave15Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        Wave15Inputs (E s) D) →
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

#print axioms wave15L4Loss
#print axioms wave15L4Loss_eq_card
#print axioms wave15L4Loss_zero
#print axioms wave15L4Leaf
#print axioms wave15L4Leaf_loss
#print axioms wave15L27Leaf
#print axioms wave15L27Leaf_loss
#print axioms wave15L27Leaf_slot
#print axioms wave15L27Leaf_paper
#print axioms wave15L34Leaf
#print axioms wave15L34Leaf_loss_eq
#print axioms wave15L34Leaf_loss_nonneg
#print axioms wave15L34Leaf_loss_pos
#print axioms wave15L34Leaf_slot
#print axioms Wave15C5Data.toC5
#print axioms Wave15C5Data.toC5_totalLoss
#print axioms Wave15C5Data.toC5_totalLoss_pos
#print axioms Wave15L19Inputs.toL19FullCertificate
#print axioms Wave15L19Inputs.toThinPairInputs
#print axioms Wave15L19Inputs.thin_loss_eq
#print axioms Wave15L19Inputs.thin_pos
#print axioms Wave15L19Inputs.smallDet_pos
#print axioms Wave15L19Inputs.thin_loss_pos
#print axioms wave15Slots
#print axioms wave15Slots_total_eq
#print axioms Wave15Inputs.toFullyDischargedInputs
#print axioms Wave15Inputs.toFullyDischargedInputs_slots
#print axioms Wave15Inputs.toPaperEndpointInputs
#print axioms Wave15Inputs.toPaperEndpointInputs_paper_slots
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave15Inputs

end Cogentic.RandomizedPaperEndpointWave15
