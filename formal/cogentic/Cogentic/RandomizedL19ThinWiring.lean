import Cogentic.RandomizedL19Full
import Cogentic.RandomizedL19ThinFinite
import Cogentic.RandomizedL18_4ThinFinish

/-!
# L19.6 wiring: the thin certificate at the Poisson scale `W = log V`

`Cogentic.RandomizedL19Full.L19FullCertificate` carries the L19.6 thin
certificate as a `LatticeThinInputs` together with the scale adapter

`thin_W : thin.W = I.W`.

`Cogentic.RandomizedL18_4ThinFinish.ThinLatticeData` (and a fortiori a
`RandomizedL18_4.ThinAggregate`) constructs a `LatticeThinInputs` whose scale is
the scale of the underlying `L18_4Inputs`.  This file bridges the two records:

* `ThinWiring W` is the L18.4 determinant/volume data **presented at a chosen
  scale `W`**: a `ThinLatticeData` plus the single equality `data.W = W`;
* `ThinWiring.thinCertificate` is the L19.6 `LatticeThinInputs` extracted from
  that data.  Its scale adapter is *exactly* the carried equality
  (`thinCertificate_W`), so no scale information is hidden;
* `L19FullCertificate.withThin` rebuilds an `L19FullCertificate` with its L19.6
  thin field replaced by such a concrete certificate, without changing any
  other field.  The rebuilt thin and small-determinant fractions are the actual
  normalized lattice counts, hence strictly positive
  (`withThin_thinInputs_thin_pos`, `withThin_thinInputs_smallDet_pos`), and the
  L19.6 loss `thin + smallDet` is nonzero.

## The scale reduction

The Poisson interface `PoissonQuotientInputs` and the L18.4 lattice data
`L18_4Inputs` carry *separate* scale fields, so there is no definitional
identification between them.  The smallest explicit equality is

`hW : base.W = W`

for the chosen common scale `W` (in the application, `W = I.W` of the Poisson
interface).  `ThinWiring.ofThinAggregateEq` consumes exactly this equality and
produces a `ThinWiring W`; conversely `ThinWiring.data_scale_eq` returns it.
`ThinWiring.thinCertificate_W` then proves the adapter with no further
hypothesis, and `ThinWiring.ofThinAggregate` records the concrete case where the
aggregate already lives at `W` (there `W_eq` is `rfl`).

`ThinLatticeData.castW` records the same reduction at the level of the lattice
data: reindexing along `hW : C.W = W` changes only the scale, and the genuine
thin and small-determinant fractions are preserved (`castW_thin`,
`castW_smallDet`).

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and neither fraction
is set to zero.
-/

/-! ## 1. Reindexing the L18.4 thin data along a scale equality -/

namespace Cogentic.RandomizedL18_4ThinFinish

noncomputable section

open Filter Real
open Cogentic.RandomizedL18_4

/-- **Reindex `ThinLatticeData` along an equality of logarithmic scales.**

The lattice box, the reference density, and both pair fractions describe the
same underlying counts; only the scale field and the `denomScale W`/cutoff
expressions are rewritten.  This is the smallest bookkeeping that presents the
L18.4 thin certificate at a chosen `W = log V`. -/
def ThinLatticeData.castW (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) : ThinLatticeData where
  W := W
  box := C.box
  dens := C.dens
  W_nonneg := hW ▸ C.W_nonneg
  W_dominates := hW ▸ C.W_dominates
  dens_pos := C.dens_pos
  dens_le_one := C.dens_le_one
  mark_count := hW ▸ C.mark_count
  power_margin := hW ▸ C.power_margin

/-- The reindexed data carries the chosen scale. -/
@[simp] theorem ThinLatticeData.castW_W (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) : (C.castW hW).W = W := rfl

/-- Reindexing does not change the lattice box. -/
@[simp] theorem ThinLatticeData.castW_box (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) : (C.castW hW).box = C.box := rfl

/-- Reindexing does not change the reference density. -/
@[simp] theorem ThinLatticeData.castW_dens (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) : (C.castW hW).dens = C.dens := rfl

/-- Reindexing does not change the geometric modulus. -/
@[simp] theorem ThinLatticeData.castW_q (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) (n : ℕ) : (C.castW hW).q n = C.q n := rfl

/-- Reindexing does not change the per-level solution bound. -/
@[simp] theorem ThinLatticeData.castW_L (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) (n : ℕ) : (C.castW hW).L n = C.L n := rfl

/-- Reindexing does not change the per-level solution bound as a function. -/
@[simp] theorem ThinLatticeData.castW_L_fun (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) : (C.castW hW).L = C.L := rfl

/-- Reindexing does not change the retained mark set. -/
@[simp] theorem ThinLatticeData.castW_S (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) (n : ℕ) : (C.castW hW).S n = C.S n := rfl

/-- Reindexing does not change the retained mark count. -/
@[simp] theorem ThinLatticeData.castW_R (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) (n : ℕ) : (C.castW hW).R n = C.R n := rfl

/-- Reindexing does not change the actual normalized thin fraction: the strip
count is the same combinatorial count, re-expressed at the equal scale. -/
theorem ThinLatticeData.castW_thin (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) : (C.castW hW).thin = C.thin := by
  funext n
  simp only [ThinLatticeData.thin, ThinLatticeData.stripPairs]
  rw [ThinLatticeData.castW_W, ThinLatticeData.castW_L_fun,
    ThinLatticeData.castW_dens, ThinLatticeData.castW_S, ThinLatticeData.castW_R, hW]

/-- Reindexing does not change the actual normalized small-determinant
fraction. -/
@[simp] theorem ThinLatticeData.castW_smallDet (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) : (C.castW hW).smallDet = C.smallDet := rfl

/-- The reindexed data has the same positive thin fraction. -/
theorem ThinLatticeData.castW_thin_pos (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) (n : ℕ) : 0 < (C.castW hW).thin n := by
  rw [C.castW_thin hW]
  exact C.thin_pos n

/-- The reindexed data has the same positive small-determinant fraction. -/
theorem ThinLatticeData.castW_smallDet_pos (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) (n : ℕ) : 0 < (C.castW hW).smallDet n :=
  C.smallDet_pos n

/-- The reindexed data has the same `smallDet ≤ thin` inclusion. -/
theorem ThinLatticeData.castW_smallDet_le_thin (C : ThinLatticeData) {W : ℕ → ℝ}
    (hW : C.W = W) (n : ℕ) :
    (C.castW hW).smallDet n ≤ (C.castW hW).thin n := by
  rw [C.castW_thin hW]
  exact C.smallDet_le_thin n

end

end Cogentic.RandomizedL18_4ThinFinish

/-! ## 2. A thin certificate at a chosen scale -/

namespace Cogentic.RandomizedL19ThinWiring

noncomputable section

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Thin
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL18_4ThinFinish

/-- **The L18.4 thin data presented at a chosen scale `W = log V`.**

The single equality field `W_eq` is the *smallest* explicit residual when the
lattice scale and the Poisson scale are different record fields.  When the
aggregate is already indexed by the target scale, `W_eq` is `rfl`
(`ThinWiring.ofThinAggregate`). -/
structure ThinWiring (W : ℕ → ℝ) where
  /-- The concrete determinant/volume data produced by L18.4. -/
  data : ThinLatticeData
  /-- The only scale identification: the data scale is the chosen `W`. -/
  W_eq : data.W = W

namespace ThinWiring

variable {W : ℕ → ℝ}

/-- The explicit scale equality carried by a wiring. -/
theorem data_scale_eq (T : ThinWiring W) : T.data.W = W := T.W_eq

/-- **The L19.6 thin certificate extracted from the lattice data.** -/
def thinCertificate (T : ThinWiring W) : LatticeThinInputs :=
  T.data.toLatticeThinInputs

/-- **The scale adapter.**  The thin certificate produced by the wiring uses the
chosen scale `W = log V`; the proof is exactly the carried equality.  This is
the `thin_W` field required by `L19FullCertificate`. -/
theorem thinCertificate_W (T : ThinWiring W) : T.thinCertificate.W = W :=
  T.W_eq

/-- The thin certificate's scale is the data scale (definitionally), and the
adapter converts it to the chosen scale. -/
theorem thinCertificate_W_eq_data (T : ThinWiring W) :
    T.thinCertificate.W = T.data.W := rfl

/-- The thin certificate's fraction is the actual normalized strip count. -/
@[simp] theorem thinCertificate_thin_eq (T : ThinWiring W) (n : ℕ) :
    T.thinCertificate.thin n = T.data.thin n := rfl

/-- The thin certificate's small-determinant fraction is the actual normalized
zero-determinant count. -/
@[simp] theorem thinCertificate_smallDet_eq (T : ThinWiring W) (n : ℕ) :
    T.thinCertificate.smallDet n = T.data.smallDet n := rfl

/-- **The thin fraction is genuinely positive**: it is the normalized
determinant-strip pair count, not a zero placeholder. -/
theorem thinCertificate_thin_pos (T : ThinWiring W) (n : ℕ) :
    0 < T.thinCertificate.thin n :=
  T.data.thin_pos n

/-- **The small-determinant fraction is genuinely positive**: it is the
normalized zero-determinant pair count, at least the diagonal `1/R`. -/
theorem thinCertificate_smallDet_pos (T : ThinWiring W) (n : ℕ) :
    0 < T.thinCertificate.smallDet n :=
  T.data.smallDet_pos n

/-- The small-determinant pairs are a sub-collection of the thin pairs. -/
theorem thinCertificate_smallDet_le_thin (T : ThinWiring W) (n : ℕ) :
    T.thinCertificate.smallDet n ≤ T.thinCertificate.thin n :=
  T.data.smallDet_le_thin n

/-- The L19.6 loss `thin + smallDet` is strictly positive. -/
theorem thinCertificate_loss_pos (T : ThinWiring W) (n : ℕ) :
    0 < T.thinCertificate.toThinPairInputs.loss n := by
  have h1 : 0 < T.thinCertificate.toThinPairInputs.thin n :=
    T.thinCertificate_thin_pos n
  have h2 : 0 < T.thinCertificate.toThinPairInputs.smallDet n :=
    T.thinCertificate_smallDet_pos n
  simpa [Cogentic.RandomizedL19SecondMoment.ThinPairInputs.loss] using add_pos h1 h2

/-- The thin fraction is nonzero at every stage. -/
theorem thinCertificate_thin_ne_zero (T : ThinWiring W) (n : ℕ) :
    T.thinCertificate.thin n ≠ 0 :=
  ne_of_gt (T.thinCertificate_thin_pos n)

/-- The small-determinant fraction is nonzero at every stage. -/
theorem thinCertificate_smallDet_ne_zero (T : ThinWiring W) (n : ℕ) :
    T.thinCertificate.smallDet n ≠ 0 :=
  ne_of_gt (T.thinCertificate_smallDet_pos n)

/-- The L19.6 loss is nonzero at every stage. -/
theorem thinCertificate_loss_ne_zero (T : ThinWiring W) (n : ℕ) :
    T.thinCertificate.toThinPairInputs.loss n ≠ 0 :=
  ne_of_gt (T.thinCertificate_loss_pos n)

/-- The proved thin bound at the chosen scale, with the explicit exponent
`η = 1/4`. -/
theorem thinCertificate_thin_bound (T : ThinWiring W) (n : ℕ) :
    T.thinCertificate.thin n ≤
      exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * W n) := by
  simpa only [T.thinCertificate_W] using T.thinCertificate.thin_bound n

/-- The proved small-determinant bound at the chosen scale, with the explicit
exponent `η = 1/4`. -/
theorem thinCertificate_smallDet_bound (T : ThinWiring W) (n : ℕ) :
    T.thinCertificate.smallDet n ≤
      exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * W n) := by
  simpa only [T.thinCertificate_W] using T.thinCertificate.smallDet_bound n

/-- The L19.6 `SubexpLoss` of the wired certificate. -/
theorem thinCertificate_subexpLoss (T : ThinWiring W) :
    SubexpLoss T.thinCertificate.toThinPairInputs.loss :=
  T.thinCertificate.subexpLoss

/-- The C5 `B = 2` slot of the wired certificate. -/
theorem thinCertificate_slot_le (T : ThinWiring W) :
    ∀ᶠ n : ℕ in atTop,
      T.thinCertificate.toThinPairInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  T.thinCertificate.slot_le

/-- **The concrete scale choice.**  If the L18.4 data already carries the
chosen scale, the residual equality is `rfl` and the wiring introduces no new
hypothesis. -/
def ofData (C : ThinLatticeData) : ThinWiring C.W where
  data := C
  W_eq := rfl

/-- **The aggregate route at the aggregate's own scale.**  This is the
`ThinLatticeData.ofThinAggregate` adapter, so consumers that already carry the
L18.4 determinant aggregate need no new counting input. -/
def ofThinAggregate {I : L18_4Inputs} (A : ThinAggregate I) : ThinWiring I.W where
  data := ThinLatticeData.ofThinAggregate A
  W_eq := rfl

/-- **The aggregate route at an explicitly identified scale.**  The only
hypothesis is the function equality `I.W = W`; everything else is the L18.4
determinant/volume count. -/
def ofThinAggregateEq {I : L18_4Inputs} (A : ThinAggregate I) {W : ℕ → ℝ}
    (hW : I.W = W) : ThinWiring W where
  data := ThinLatticeData.ofThinAggregate A
  W_eq := hW

/-- **The scale reduction.**  For an L18.4 aggregate, the thin certificate can be
stated at `W` with the single explicit equality `I.W = W`, and then the adapter
`thin.W = W` follows from exactly that equality. -/
theorem thinCertificate_W_of_aggregate {I : L18_4Inputs} (A : ThinAggregate I)
    {W : ℕ → ℝ} (hW : I.W = W) :
    (ofThinAggregateEq A hW).thinCertificate.W = W :=
  hW

/-- In the concrete case `W = I.W`, the adapter holds with no equality
hypothesis at all: the data scale is definitionally the aggregate scale. -/
theorem thinCertificate_W_of_aggregate_self {I : L18_4Inputs}
    (A : ThinAggregate I) :
    (ofThinAggregate A).thinCertificate.W = I.W :=
  rfl

end ThinWiring

end

end Cogentic.RandomizedL19ThinWiring

/-! ## 3. Rebuilding the `L19FullCertificate` thin field -/

namespace Cogentic.RandomizedL19Full

namespace L19FullCertificate

noncomputable section

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Thin
open Cogentic.RandomizedL19ThinWiring
open Cogentic.RandomizedL18_4

variable (C : L19FullCertificate)

/-- **Rebuild the L19.6 thin field from concrete L18.4 lattice data.**

Every field other than `thin` and `thin_W` is inherited from `C`; the thin field
is the certificate extracted from `T`, whose scale is `C.I.W` by the wiring.
Thus the resulting record is again a full `L19FullCertificate` with the same
Poisson, zero-mode, and coupled-mode data, but with `thin` equal to the actual
determinant-strip and zero-determinant counts. -/
def withThin (T : ThinWiring C.I.W) : L19FullCertificate where
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
  thin := T.thinCertificate
  thin_W := T.thinCertificate_W

/-- The rebuilt certificate keeps the Poisson interface. -/
@[simp] theorem withThin_I (T : ThinWiring C.I.W) : (C.withThin T).I = C.I := rfl

/-- The rebuilt certificate keeps the Poisson record. -/
@[simp] theorem withThin_poisson (T : ThinWiring C.I.W) :
    (C.withThin T).poisson = C.poisson := rfl

/-- The rebuilt certificate keeps the zero-mode certificate. -/
@[simp] theorem withThin_zeroMode (T : ThinWiring C.I.W) :
    (C.withThin T).zeroMode = C.zeroMode := rfl

/-- The rebuilt certificate's thin field is the wired certificate. -/
@[simp] theorem withThin_thin (T : ThinWiring C.I.W) :
    (C.withThin T).thin = T.thinCertificate := rfl

/-- **The adapter of the rebuilt certificate.**  The L19.6 thin field uses the
Poisson scale `C.I.W`. -/
theorem withThin_thin_W (T : ThinWiring C.I.W) :
    (C.withThin T).thin.W = C.I.W :=
  (C.withThin T).thin_W

/-- The L19.6 `ThinPairInputs` of the rebuilt certificate uses `C.I.W`. -/
theorem withThin_thinInputs_W (T : ThinWiring C.I.W) :
    (C.withThin T).thinInputs.W = C.I.W :=
  (C.withThin T).thinInputs_W

/-- All three composed components of the rebuilt certificate use `C.I.W`. -/
theorem withThin_toL19Inputs_W (T : ThinWiring C.I.W) :
    (C.withThin T).toL19Inputs.poisson.W = C.I.W ∧
      (C.withThin T).toL19Inputs.zeroMode.W = C.I.W ∧
        (C.withThin T).toL19Inputs.thin.W = C.I.W :=
  (C.withThin T).toL19Inputs_W

/-- The rebuilt thin fraction is the actual normalized strip count. -/
@[simp] theorem withThin_thinInputs_thin_eq (T : ThinWiring C.I.W) (n : ℕ) :
    (C.withThin T).thinInputs.thin n = T.data.thin n := rfl

/-- The rebuilt small-determinant fraction is the actual normalized
zero-determinant count. -/
@[simp] theorem withThin_thinInputs_smallDet_eq (T : ThinWiring C.I.W) (n : ℕ) :
    (C.withThin T).thinInputs.smallDet n = T.data.smallDet n := rfl

/-- **The rebuilt thin fraction is genuinely nonzero.** -/
theorem withThin_thinInputs_thin_pos (T : ThinWiring C.I.W) (n : ℕ) :
    0 < (C.withThin T).thinInputs.thin n :=
  T.thinCertificate_thin_pos n

/-- **The rebuilt small-determinant fraction is genuinely nonzero.** -/
theorem withThin_thinInputs_smallDet_pos (T : ThinWiring C.I.W) (n : ℕ) :
    0 < (C.withThin T).thinInputs.smallDet n :=
  T.thinCertificate_smallDet_pos n

/-- The rebuilt thin fraction is nonzero at every stage. -/
theorem withThin_thinInputs_thin_ne_zero (T : ThinWiring C.I.W) (n : ℕ) :
    (C.withThin T).thinInputs.thin n ≠ 0 :=
  ne_of_gt (C.withThin_thinInputs_thin_pos T n)

/-- The rebuilt small-determinant fraction is nonzero at every stage. -/
theorem withThin_thinInputs_smallDet_ne_zero (T : ThinWiring C.I.W) (n : ℕ) :
    (C.withThin T).thinInputs.smallDet n ≠ 0 :=
  ne_of_gt (C.withThin_thinInputs_smallDet_pos T n)

/-- **The rebuilt L19.6 loss is genuinely nonzero.**  It is the sum of the two
actual normalized pair fractions, not a zero placeholder. -/
theorem withThin_thinInputs_loss_pos (T : ThinWiring C.I.W) (n : ℕ) :
    0 < (C.withThin T).thinInputs.loss n := by
  have h1 : 0 < (C.withThin T).thinInputs.thin n :=
    C.withThin_thinInputs_thin_pos T n
  have h2 : 0 < (C.withThin T).thinInputs.smallDet n :=
    C.withThin_thinInputs_smallDet_pos T n
  simpa [Cogentic.RandomizedL19SecondMoment.ThinPairInputs.loss] using add_pos h1 h2

/-- The rebuilt L19.6 loss is nonzero at every stage. -/
theorem withThin_thinInputs_loss_ne_zero (T : ThinWiring C.I.W) (n : ℕ) :
    (C.withThin T).thinInputs.loss n ≠ 0 :=
  ne_of_gt (C.withThin_thinInputs_loss_pos T n)

/-- The rebuilt thin field satisfies the L19.6 bound with the explicit exponent
`η = 1/4` at the Poisson scale. -/
theorem withThin_thinInputs_thin_bound (T : ThinWiring C.I.W) (n : ℕ) :
    (C.withThin T).thinInputs.thin n ≤
      exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * C.I.W n) :=
  T.thinCertificate_thin_bound n

/-- The rebuilt small-determinant field satisfies the L19.6 bound with the
explicit exponent `η = 1/4` at the Poisson scale. -/
theorem withThin_thinInputs_smallDet_bound (T : ThinWiring C.I.W) (n : ℕ) :
    (C.withThin T).thinInputs.smallDet n ≤
      exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * C.I.W n) :=
  T.thinCertificate_smallDet_bound n

/-- The rebuilt L19.6 component still carries the `SubexpLoss` statement. -/
theorem withThin_thinInputs_subexpLoss (T : ThinWiring C.I.W) :
    SubexpLoss (C.withThin T).thinInputs.loss :=
  T.thinCertificate_subexpLoss

/-- The rebuilt L19.6 component still meets the C5 `B = 2` slot. -/
theorem withThin_thinInputs_slot_le (T : ThinWiring C.I.W) :
    ∀ᶠ n : ℕ in atTop,
      (C.withThin T).thinInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  T.thinCertificate_slot_le

/-- **The rebuilt certificate still satisfies the three C5 slot bounds.** -/
theorem withThin_slots_bounds (T : ThinWiring C.I.W) (rest : C5LossSlots) :
    (∀ᶠ n : ℕ in atTop,
        (C.withThin T).toL19Inputs.slots rest .poissonQuotient n ≤
          exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        (C.withThin T).toL19Inputs.slots rest .idealZeroMode n ≤
          exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        (C.withThin T).toL19Inputs.slots rest .thinPairs n ≤
          exp (-(2 : ℝ) * scale n)) :=
  (C.withThin T).slots_bounds rest

/-- **The rebuilt certificate still proves the three manuscript leaf
statements.**  The L19.6 entry is the `SubexpLoss` of the wired thin
certificate. -/
theorem withThin_leaves_paper (T : ThinWiring C.I.W) :
    SubexpLoss (C.withThin T).poisson.loss ∧
      SubexpLoss (C.withThin T).zeroModeInputs.loss ∧
        SubexpLoss (C.withThin T).thinInputs.loss :=
  (C.withThin T).leaves_paper

/-- The rebuilt L19.6 leaf is exactly the wired certificate's leaf. -/
theorem withThin_leaves_l19_6 (T : ThinWiring C.I.W) :
    (C.withThin T).toL19Inputs.leaves.l19_6 =
      T.thinCertificate.toSubexpLeaf :=
  rfl

/-- **Rebuild from a concrete L18.4 aggregate.**  The only extra hypothesis is
the explicit scale equality `I.W = C.I.W`; the L19.6 thin field is then the
determinant/volume certificate of the aggregate. -/
def withThinOfAggregate {I : L18_4Inputs} (A : ThinAggregate I)
    (hW : I.W = C.I.W) : L19FullCertificate :=
  C.withThin (ThinWiring.ofThinAggregateEq A hW)

/-- The aggregate-built certificate carries the Poisson scale in its thin
field. -/
theorem withThinOfAggregate_thin_W {I : L18_4Inputs} (A : ThinAggregate I)
    (hW : I.W = C.I.W) :
    (C.withThinOfAggregate A hW).thin.W = C.I.W :=
  (C.withThinOfAggregate A hW).thin_W

/-- The aggregate-built certificate has genuinely nonzero thin and
small-determinant fractions, inherited from the concrete lattice counts. -/
theorem withThinOfAggregate_thinInputs_pos {I : L18_4Inputs}
    (A : ThinAggregate I) (hW : I.W = C.I.W) (n : ℕ) :
    0 < (C.withThinOfAggregate A hW).thinInputs.thin n ∧
      0 < (C.withThinOfAggregate A hW).thinInputs.smallDet n :=
  ⟨(C.withThinOfAggregate A hW).withThin_thinInputs_thin_pos
      (ThinWiring.ofThinAggregateEq A hW) n,
    (C.withThinOfAggregate A hW).withThin_thinInputs_smallDet_pos
      (ThinWiring.ofThinAggregateEq A hW) n⟩

end

end L19FullCertificate

end Cogentic.RandomizedL19Full

/-! ## Axiom audit -/

namespace Cogentic.RandomizedL19ThinWiring

#print axioms Cogentic.RandomizedL18_4ThinFinish.ThinLatticeData.castW
#print axioms Cogentic.RandomizedL18_4ThinFinish.ThinLatticeData.castW_W
#print axioms Cogentic.RandomizedL18_4ThinFinish.ThinLatticeData.castW_thin
#print axioms Cogentic.RandomizedL18_4ThinFinish.ThinLatticeData.castW_smallDet
#print axioms Cogentic.RandomizedL18_4ThinFinish.ThinLatticeData.castW_thin_pos
#print axioms Cogentic.RandomizedL18_4ThinFinish.ThinLatticeData.castW_smallDet_pos
#print axioms Cogentic.RandomizedL18_4ThinFinish.ThinLatticeData.castW_smallDet_le_thin
#print axioms ThinWiring.data_scale_eq
#print axioms ThinWiring.thinCertificate
#print axioms ThinWiring.thinCertificate_W
#print axioms ThinWiring.thinCertificate_W_eq_data
#print axioms ThinWiring.thinCertificate_thin_pos
#print axioms ThinWiring.thinCertificate_smallDet_pos
#print axioms ThinWiring.thinCertificate_loss_pos
#print axioms ThinWiring.thinCertificate_thin_bound
#print axioms ThinWiring.thinCertificate_smallDet_bound
#print axioms ThinWiring.thinCertificate_subexpLoss
#print axioms ThinWiring.thinCertificate_slot_le
#print axioms ThinWiring.ofData
#print axioms ThinWiring.ofThinAggregate
#print axioms ThinWiring.ofThinAggregateEq
#print axioms ThinWiring.thinCertificate_W_of_aggregate
#print axioms ThinWiring.thinCertificate_W_of_aggregate_self

end Cogentic.RandomizedL19ThinWiring

namespace Cogentic.RandomizedL19Full

#print axioms L19FullCertificate.withThin
#print axioms L19FullCertificate.withThin_thin_W
#print axioms L19FullCertificate.withThin_thinInputs_W
#print axioms L19FullCertificate.withThin_toL19Inputs_W
#print axioms L19FullCertificate.withThin_thinInputs_thin_pos
#print axioms L19FullCertificate.withThin_thinInputs_smallDet_pos
#print axioms L19FullCertificate.withThin_thinInputs_loss_pos
#print axioms L19FullCertificate.withThin_thinInputs_thin_bound
#print axioms L19FullCertificate.withThin_thinInputs_smallDet_bound
#print axioms L19FullCertificate.withThin_thinInputs_subexpLoss
#print axioms L19FullCertificate.withThin_thinInputs_slot_le
#print axioms L19FullCertificate.withThin_slots_bounds
#print axioms L19FullCertificate.withThin_leaves_paper
#print axioms L19FullCertificate.withThin_leaves_l19_6
#print axioms L19FullCertificate.withThinOfAggregate
#print axioms L19FullCertificate.withThinOfAggregate_thin_W
#print axioms L19FullCertificate.withThinOfAggregate_thinInputs_pos

end Cogentic.RandomizedL19Full
