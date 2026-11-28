import Cogentic.RandomizedL18_4ThinAggregate
import Cogentic.RandomizedL19Thin

/-!
# L18.4 thin finish: `LatticeThinInputs` from the determinant/volume count

`Cogentic.RandomizedL19Thin.LatticeThinInputs` is the L19.6 thin/small-determinant
certificate.  It bundles

* a `Cogentic.RandomizedL18_4.ThinPairInputs` (the determinant-strip count at the
  free cutoff, the rational-good mark count, and the fixed power margin);
* the common logarithmic scale `W = log V` with `DominatesScale W`;
* a nonnegative thin fraction, a nonnegative small-determinant fraction, and the
  inclusion `smallDet ≤ thin`.

The determinant-level count already proved in
`Cogentic.RandomizedL18_4ThinAggregate` supplies the whole strip estimate: one
determinant level meets a box of denominator diameter `O(V)` in at most
`L₀ = O(1)` points (`PrimitiveMark.det_level_card_le`), and the determinant
levels `D ∈ qℤ` with `|D| ≤ X` number at most `2X/q`
(`level_card_le`).  Mathlib's geometry-of-numbers
(`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`)
is an *existence* theorem and does not give the upper lattice-point count needed
here; the arithmetic level count is the sharp available machinery, and it is
what this file uses.

This file reduces `LatticeThinInputs` to the smallest explicit data:

1. a family of determinant boxes `box n : LatticeBox`;
2. the rational-good mark lower count
   `ρ V²/(q(1 + log V)) ≤ R` (the rational/volume count);
3. the fixed power margin `2q(1 + log V) ≤ ρ V²/K` (the determinant cutoff
   inequality).

The thin fraction is *defined* as the actual normalized strip-pair count at the
free cutoff `K_det = 4L₀(1 + log V)/ρ · K`, so its strip bound is not an extra
hypothesis.  The small-determinant fraction is the actual normalized
zero-determinant pair count; it is nonzero (`smallDet_pos`) and is a genuine
sub-collection of the thin pairs (`smallDet_le_thin`), because the zero
determinant level consists of the diagonal pairs (`PrimitiveMark.det_level_zero`
plus primitivity, exactly as in `zero_partner_card_le`).

Nothing here is a `sorry`, an `admit`, an `axiom` or a `native_decide`; neither
the mark count nor the pair count is set to zero.
-/

namespace Cogentic.RandomizedL18_4ThinFinish

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Thin
open Finset

noncomputable section

/-! ## 1. The minimal determinant/volume data -/

/-- **The determinant/volume data behind `LatticeThinInputs`.**

The two numerical fields are exactly the remaining explicit inequalities:

* `mark_count`: the rational-good box contains at least `ρ V²/(q(1 + log V))`
  primitive marks (the rational/volume count);
* `power_margin`: the determinant cutoff `K_det` is still inside the strip
  range, `2q(1 + log V) ≤ ρ V²/K` (the fixed power margin).

Everything else is the actual lattice box, the reference density, and the scale
`W = log V`; no fraction or error is a free zero. -/
structure ThinLatticeData where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- The determinant lattice box of retained primitive marks at each stage. -/
  box : ℕ → LatticeBox
  /-- The reference density `ρ` of the numerator progression. -/
  dens : ℕ → ℝ
  /-- `log V ≥ 0`. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `scale`. -/
  W_dominates : DominatesScale W
  /-- The reference density is positive. -/
  dens_pos : ∀ n, 0 < dens n
  /-- The reference density is at most one. -/
  dens_le_one : ∀ n, dens n ≤ 1
  /-- **The rational-good mark count / volume count.**  The retained box has at
  least `ρ V²/(q (1 + log V))` marks. -/
  mark_count : ∀ n,
    dens n * (denomScale W n ^ 2 / (((box n).q : ℝ) * (1 + W n))) ≤
      ((box n).S.card : ℝ)
  /-- **The fixed power margin.**  The free determinant cutoff
  `K_det = 4L₀(1 + log V)/ρ · K` still carries a determinant level:
  `2q(1 + log V) ≤ ρ V²/K`. -/
  power_margin : ∀ n,
    2 * ((box n).q : ℝ) * (1 + W n) ≤
      dens n * denomScale W n ^ 2 / cellMesh W n

namespace ThinLatticeData

/-- The ordered pairs on the zero determinant level. -/
def zeroDetPairSet (T : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (T.product T).filter fun r => det r.1 r.2 = 0

/-- **The determinant/volume data of an existing `ThinAggregate`.**  The
aggregate already proves the strip count, the rational-good mark count and the
power margin, so it is a `ThinLatticeData` without further assumptions. -/
noncomputable def ofThinAggregate {I : L18_4Inputs} (A : ThinAggregate I) :
    ThinLatticeData where
  W := I.W
  box := A.box
  dens := A.dens
  W_nonneg := I.W_nonneg
  W_dominates := I.W_dominates
  dens_pos := A.dens_pos
  dens_le_one := A.dens_le_one
  mark_count := fun n => by
    simpa [ThinAggregate.q, ThinAggregate.R] using A.mark_count n
  power_margin := A.power_margin

variable (C : ThinLatticeData)

/-- The geometric modulus `q` of the root lattice. -/
def q (n : ℕ) : ℝ := ((C.box n).q : ℝ)

/-- The per-determinant-level solution bound `L₀ = 1 + ⌊diam/‖P‖⌋`. -/
def L (n : ℕ) : ℝ := (C.box n).L

/-- The retained mark set. -/
def S (n : ℕ) : Finset (ℤ × ℤ) := (C.box n).S

/-- The number of retained marks. -/
def R (n : ℕ) : ℝ := ((C.box n).S.card : ℝ)

/-- The ordered strip pairs at cutoff `k`. -/
def stripPairs (n : ℕ) (k : ℝ) : ℝ :=
  ((stripPairSet (C.S n) (denomScale C.W n ^ 2 / k)).card : ℝ)

/-- The thin fraction: the normalized strip-pair count at the free cutoff. -/
def thin (n : ℕ) : ℝ :=
  C.stripPairs n (thinCutoff C.W C.L C.dens n) / C.R n ^ 2

/-- The number of ordered zero-determinant pairs. -/
def zeroDetPairs (C : ThinLatticeData) (n : ℕ) : ℝ :=
  ((ThinLatticeData.zeroDetPairSet (C.S n)).card : ℝ)

/-- The small-determinant fraction: the normalized zero-determinant pair count.
This is a genuine sub-fraction of the thin pairs and is not set to zero. -/
def smallDet (n : ℕ) : ℝ := C.zeroDetPairs n / C.R n ^ 2

/-! ## 2. Positivity of the box data -/

theorem q_pos (n : ℕ) : 0 < C.q n := by
  rw [q]
  exact_mod_cast (C.box n).q_pos

/-- The per-level bound is at least one. -/
theorem L_ge_one (n : ℕ) : 1 ≤ C.L n := by
  have hb : (0 : ℝ) < ((C.box n).bmin : ℝ) := by
    exact_mod_cast (C.box n).bmin_pos
  have hd : (0 : ℝ) ≤ ((C.box n).hi - (C.box n).lo : ℤ) := by
    exact_mod_cast sub_nonneg.mpr (C.box n).lo_le_hi
  have h0 : (0 : ℝ) ≤
      ((C.box n).hi - (C.box n).lo : ℤ) / ((C.box n).bmin : ℝ) :=
    div_nonneg hd hb.le
  have := (C.box n).level_bound
  rw [L]
  linarith

/-- The free determinant cutoff is positive. -/
theorem thinCutoff_pos (n : ℕ) : 0 < thinCutoff C.W C.L C.dens n := by
  have hL : 0 < C.L n := lt_of_lt_of_le zero_lt_one (C.L_ge_one n)
  have hdens := C.dens_pos n
  have hW : 0 < 1 + C.W n := by linarith [C.W_nonneg n]
  have hK : 0 < cellMesh C.W n := by unfold cellMesh; exact exp_pos _
  unfold thinCutoff
  positivity

/-- The retained mark count is positive: the rational-good volume count is
strictly positive.  This is the "nonzero count" kept throughout the file. -/
theorem R_pos (n : ℕ) : 0 < C.R n := by
  have hV : 0 < denomScale C.W n := by unfold denomScale; exact exp_pos _
  have hq := C.q_pos n
  have h1W : 0 < 1 + C.W n := by linarith [C.W_nonneg n]
  have hpos : 0 < C.dens n *
      (denomScale C.W n ^ 2 / (C.q n * (1 + C.W n))) :=
    mul_pos (C.dens_pos n) (div_pos (pow_pos hV 2) (mul_pos hq h1W))
  have hle : C.dens n *
      (denomScale C.W n ^ 2 / (C.q n * (1 + C.W n))) ≤ C.R n := by
    simpa [q, R] using C.mark_count n
  exact lt_of_lt_of_le hpos hle

/-! ## 3. The determinant-strip count and the power margin -/

/-- **The determinant-strip / volume count.**  At cutoff `k` the number of
ordered pairs with `|det| ≤ V²/k` is at most `(1 + 2L₀V²/(qk)) R`.  This is
`stripPairSet_card_le`: the zero level contributes at most one partner per mark
and the `2V²/(qk)` nonzero determinant levels contribute at most `L₀` each. -/
theorem strip_count (n : ℕ) {k : ℝ} (hk : 0 < k) :
    C.stripPairs n k ≤
      (1 + 2 * C.L n * (denomScale C.W n ^ 2 / (C.q n * k))) * C.R n := by
  have hX : 0 ≤ denomScale C.W n ^ 2 / k := div_nonneg (sq_nonneg _) hk.le
  have h := stripPairSet_card_le (C.box n) hX
  have harg : (denomScale C.W n ^ 2 / k) / ((C.box n).q : ℝ) =
      denomScale C.W n ^ 2 / (C.q n * k) := by
    rw [q]
    have hq : ((C.box n).q : ℝ) ≠ 0 := by
      exact_mod_cast (C.box n).q_pos.ne'
    field_simp
  rw [harg] at h
  simpa [stripPairs, L, S, R, q] using h

/-- **The cutoff is inside the strip range.**  The power margin is exactly the
statement that the free cutoff still carries one determinant level. -/
theorem cutoff_in_range (n : ℕ) :
    1 ≤ 2 * C.L n *
      (denomScale C.W n ^ 2 / (C.q n * thinCutoff C.W C.L C.dens n)) := by
  have hK : 0 < cellMesh C.W n := by unfold cellMesh; exact exp_pos _
  have hL : 0 < C.L n := lt_of_lt_of_le zero_lt_one (C.L_ge_one n)
  have hdens : 0 < C.dens n := C.dens_pos n
  have hq : 0 < C.q n := C.q_pos n
  have h1W : 0 < 1 + C.W n := by linarith [C.W_nonneg n]
  have hthin_ne : thinCutoff C.W C.L C.dens n ≠ 0 :=
    (C.thinCutoff_pos n).ne'
  have hcell_ne : cellMesh C.W n ≠ 0 := hK.ne'
  have hL_ne : C.L n ≠ 0 := hL.ne'
  have hdens_ne : C.dens n ≠ 0 := hdens.ne'
  have h1W_ne : (1 + C.W n) ≠ 0 := h1W.ne'
  have hq_ne : C.q n ≠ 0 := hq.ne'
  have hid : 2 * C.L n *
        (denomScale C.W n ^ 2 / (C.q n * thinCutoff C.W C.L C.dens n)) =
      C.dens n * denomScale C.W n ^ 2 /
        (2 * C.q n * (1 + C.W n) * cellMesh C.W n) := by
    unfold thinCutoff
    field_simp
    ring
  rw [hid]
  rw [le_div_iff₀ (by positivity)]
  have hp := C.power_margin n
  have hmul := mul_le_mul_of_nonneg_right hp hK.le
  rw [div_mul_cancel₀ _ hcell_ne] at hmul
  simpa [q, mul_assoc] using hmul

/-- **The power-margin reduction is exact.**  Substituting the free cutoff
`K_det = 4L₀(1 + log V)/ρ · K` into `2L₀V²/(qK_det)` leaves
`ρV²/(2q(1 + log V)K)`, so `cutoff_in_range` is *equivalent* to the explicit
determinant inequality `2q(1 + log V) ≤ ρV²/K`.  No loss is hidden in the
reduction. -/
theorem cutoff_in_range_iff_power_margin (n : ℕ) :
    (1 ≤ 2 * C.L n *
        (denomScale C.W n ^ 2 / (C.q n * thinCutoff C.W C.L C.dens n))) ↔
      2 * C.q n * (1 + C.W n) ≤
        C.dens n * denomScale C.W n ^ 2 / cellMesh C.W n := by
  have hK : 0 < cellMesh C.W n := by unfold cellMesh; exact exp_pos _
  have hL : 0 < C.L n := lt_of_lt_of_le zero_lt_one (C.L_ge_one n)
  have hdens : 0 < C.dens n := C.dens_pos n
  have hq : 0 < C.q n := C.q_pos n
  have h1W : 0 < 1 + C.W n := by linarith [C.W_nonneg n]
  have hthin_ne : thinCutoff C.W C.L C.dens n ≠ 0 :=
    (C.thinCutoff_pos n).ne'
  have hcell_ne : cellMesh C.W n ≠ 0 := hK.ne'
  have hL_ne : C.L n ≠ 0 := hL.ne'
  have hdens_ne : C.dens n ≠ 0 := hdens.ne'
  have h1W_ne : (1 + C.W n) ≠ 0 := h1W.ne'
  have hq_ne : C.q n ≠ 0 := hq.ne'
  have hid : 2 * C.L n *
        (denomScale C.W n ^ 2 / (C.q n * thinCutoff C.W C.L C.dens n)) =
      C.dens n * denomScale C.W n ^ 2 /
        (2 * C.q n * (1 + C.W n) * cellMesh C.W n) := by
    unfold thinCutoff
    field_simp
    ring
  rw [hid, le_div_iff₀ (by positivity), le_div_iff₀ hK]
  constructor
  · intro h
    simpa [mul_assoc] using h
  · intro h
    simpa [mul_assoc] using h

/-! ## 4. The `ThinPairInputs` record -/

/-- **The determinant-strip `ThinPairInputs`.**  The `thin` field is the actual
normalized strip count, so `thin_le_pairFraction` is definitional; `strip_count`
is `stripPairSet_card_le`, `mark_count` is the rational-good volume count, and
`cutoff_in_range` is the power margin. -/
noncomputable def toThinPairInputs : ThinPairInputs C.W C.thin where
  q := C.q
  dens := C.dens
  R := C.R
  L := C.L
  thinPairs := C.stripPairs
  W_nonneg := C.W_nonneg
  q_pos := C.q_pos
  dens_pos := C.dens_pos
  dens_le_one := C.dens_le_one
  R_pos := C.R_pos
  L_ge_one := C.L_ge_one
  thinPairs_nonneg := fun _ _ => Nat.cast_nonneg _
  thin_le_pairFraction := fun _ => le_rfl
  strip_count := fun n k hk => C.strip_count n hk
  cutoff_in_range := C.cutoff_in_range
  mark_count := fun n => by
    simpa [q, R] using C.mark_count n

/-- **`thin_pair_fraction` from the determinant/volume count**: the normalized
strip count is at most `1/K = V^{-1/4}`. -/
theorem thin_pair_fraction (n : ℕ) : C.thin n ≤ 1 / cellMesh C.W n :=
  C.toThinPairInputs.thin_pair_fraction n

/-! ## 5. The zero-determinant / small-determinant fraction -/

/-- The zero determinant level is contained in every nonnegative strip. -/
theorem zeroDetPairSet_subset_strip (T : Finset (ℤ × ℤ)) {X : ℝ} (hX : 0 ≤ X) :
    zeroDetPairSet T ⊆ stripPairSet T X := by
  intro r hr
  rw [zeroDetPairSet, Finset.mem_filter] at hr
  rw [stripPairSet, Finset.mem_filter]
  refine ⟨hr.1, ?_⟩
  rw [hr.2]
  simpa using hX

/-- The diagonal is a zero-determinant pair. -/
theorem diag_mem_zeroDetPairSet {T : Finset (ℤ × ℤ)} {P : ℤ × ℤ} (hP : P ∈ T) :
    (P, P) ∈ zeroDetPairSet T := by
  rw [zeroDetPairSet, Finset.mem_filter]
  refine ⟨Finset.mem_product.mpr ⟨hP, hP⟩, ?_⟩
  simp [det]

/-- The number of zero-determinant pairs is at least the number of marks: every
mark is its own diagonal partner. -/
theorem R_le_zeroDetPairs (n : ℕ) : C.R n ≤ C.zeroDetPairs n := by
  have hsub : (C.S n).image (fun P => (P, P)) ⊆ zeroDetPairSet (C.S n) := by
    intro r hr
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hr
    exact diag_mem_zeroDetPairSet hP
  have hcard := Finset.card_le_card hsub
  have himg : ((C.S n).image (fun P => (P, P))).card = (C.S n).card :=
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  rw [himg] at hcard
  unfold zeroDetPairs R
  exact_mod_cast hcard

/-- The normalized zero-determinant fraction is nonnegative. -/
theorem smallDet_nonneg (n : ℕ) : 0 ≤ C.smallDet n := by
  unfold smallDet zeroDetPairs
  exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- **The zero-determinant fraction is nonzero.**  It is at least `1/R`, the
diagonal contribution of the paper, and `R > 0`. -/
theorem smallDet_pos (n : ℕ) : 0 < C.smallDet n := by
  have hR := C.R_pos n
  have hz : 0 < C.zeroDetPairs n := lt_of_lt_of_le hR (C.R_le_zeroDetPairs n)
  unfold smallDet
  exact div_pos hz (pow_pos hR 2)

/-- **The small-determinant fraction is a sub-collection of the thin pairs.**
The zero determinant level is contained in the strip `|det| ≤ V²/K_det`, so its
normalized count is at most the normalized strip count. -/
theorem smallDet_le_thin (n : ℕ) : C.smallDet n ≤ C.thin n := by
  have hcut : 0 < thinCutoff C.W C.L C.dens n := C.thinCutoff_pos n
  have hX : 0 ≤ denomScale C.W n ^ 2 / thinCutoff C.W C.L C.dens n :=
    div_nonneg (sq_nonneg _) hcut.le
  have hcard : C.zeroDetPairs n ≤ C.stripPairs n (thinCutoff C.W C.L C.dens n) := by
    unfold zeroDetPairs stripPairs
    exact_mod_cast Finset.card_le_card (zeroDetPairSet_subset_strip (C.S n) hX)
  unfold smallDet thin
  exact div_le_div_of_nonneg_right hcard (sq_nonneg _)

/-- The normalized strip count is nonnegative. -/
theorem thin_nonneg (n : ℕ) : 0 ≤ C.thin n := by
  unfold thin stripPairs
  exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- The normalized strip count is nonzero: it is at least `1/R`. -/
theorem thin_pos (n : ℕ) : 0 < C.thin n := by
  have hR := C.R_pos n
  have hle : C.R n ≤ C.stripPairs n (thinCutoff C.W C.L C.dens n) := by
    have hcut : 0 < thinCutoff C.W C.L C.dens n := C.thinCutoff_pos n
    have hX : 0 ≤ denomScale C.W n ^ 2 / thinCutoff C.W C.L C.dens n :=
      div_nonneg (sq_nonneg _) hcut.le
    have hsub : (C.S n).image (fun P => (P, P)) ⊆
        stripPairSet (C.S n) (denomScale C.W n ^ 2 / thinCutoff C.W C.L C.dens n) := by
      intro r hr
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hr
      have hz : (P, P) ∈ zeroDetPairSet (C.S n) := diag_mem_zeroDetPairSet hP
      exact zeroDetPairSet_subset_strip (C.S n) hX hz
    have hcard := Finset.card_le_card hsub
    have himg : ((C.S n).image (fun P => (P, P))).card = (C.S n).card :=
      Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
    rw [himg] at hcard
    unfold stripPairs R
    exact_mod_cast hcard
  unfold thin
  exact div_pos (lt_of_lt_of_le hR hle) (pow_pos hR 2)

/-! ## 6. The L19.6 lattice thin certificate -/

/-- **`LatticeThinInputs` from the determinant/volume count.**  The thin field is
the actual normalized strip count (nonzero), the small-determinant field is the
actual normalized zero-determinant count (nonzero and `≤ thin`), and the lattice
record is `toThinPairInputs`. -/
noncomputable def toLatticeThinInputs : LatticeThinInputs where
  W := C.W
  thin := C.thin
  smallDet := C.smallDet
  lattice := C.toThinPairInputs
  W_dominates := C.W_dominates
  thin_nonneg := C.thin_nonneg
  smallDet_nonneg := C.smallDet_nonneg
  smallDet_le_thin := C.smallDet_le_thin

/-- **The L19.6 `LatticeThinInputs` of an existing `ThinAggregate`.**  This is
the direct adapter for consumers that already carry the L18.4 determinant
aggregate: no new counting hypothesis is introduced. -/
noncomputable def latticeThinInputsOfAggregate {I : L18_4Inputs}
    (A : ThinAggregate I) : LatticeThinInputs :=
  (ofThinAggregate A).toLatticeThinInputs

/-- The proved L19.6 thin bound, with the explicit exponent `η = 1/4`. -/
theorem thin_bound (n : ℕ) :
    C.thin n ≤ exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * C.W n) :=
  C.toLatticeThinInputs.thin_bound n

/-- The proved L19.6 small-determinant bound, with the explicit exponent
`η = 1/4`. -/
theorem smallDet_bound (n : ℕ) :
    C.smallDet n ≤ exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * C.W n) :=
  C.toLatticeThinInputs.smallDet_bound n

/-- The L19.6 subexponential deficit from the determinant/volume count.  The
loss is `thin + smallDet`, both genuine normalized counts. -/
theorem subexpLoss : SubexpLoss C.toLatticeThinInputs.toThinPairInputs.loss :=
  C.toLatticeThinInputs.subexpLoss

/-- The L19.6 `SubexpLeaf` from the determinant/volume count. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  C.toLatticeThinInputs.toSubexpLeaf

/-- The L19.6 C5 `B = 2` slot from the determinant/volume count. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    C.toLatticeThinInputs.toThinPairInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  C.toLatticeThinInputs.slot_le

end ThinLatticeData

/-! ## Axiom audit -/

#print axioms ThinLatticeData.q_pos
#print axioms ThinLatticeData.L_ge_one
#print axioms ThinLatticeData.thinCutoff_pos
#print axioms ThinLatticeData.R_pos
#print axioms ThinLatticeData.strip_count
#print axioms ThinLatticeData.cutoff_in_range
#print axioms ThinLatticeData.cutoff_in_range_iff_power_margin
#print axioms ThinLatticeData.toThinPairInputs
#print axioms ThinLatticeData.thin_pair_fraction
#print axioms ThinLatticeData.zeroDetPairSet_subset_strip
#print axioms ThinLatticeData.diag_mem_zeroDetPairSet
#print axioms ThinLatticeData.R_le_zeroDetPairs
#print axioms ThinLatticeData.smallDet_nonneg
#print axioms ThinLatticeData.smallDet_pos
#print axioms ThinLatticeData.smallDet_le_thin
#print axioms ThinLatticeData.thin_nonneg
#print axioms ThinLatticeData.thin_pos
#print axioms ThinLatticeData.toLatticeThinInputs
#print axioms ThinLatticeData.thin_bound
#print axioms ThinLatticeData.smallDet_bound
#print axioms ThinLatticeData.subexpLoss
#print axioms ThinLatticeData.toSubexpLeaf
#print axioms ThinLatticeData.ofThinAggregate
#print axioms ThinLatticeData.latticeThinInputsOfAggregate
#print axioms ThinLatticeData.slot_le

end

end Cogentic.RandomizedL18_4ThinFinish
