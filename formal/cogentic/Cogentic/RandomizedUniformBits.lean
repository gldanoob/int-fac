import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

/-! Rejection sampling from independent blocks of fair bits. -/

namespace Cogentic.RandomizedUniformBits

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

/-- Each attempt consumes the least number of bits whose patterns cover the range. -/
abbrev width (m : ℕ) : ℕ := Nat.clog 2 m

abbrev blockCount (m : ℕ) : ℕ := 2 ^ width m

abbrev Blocks (m : ℕ) := ℕ → Fin (blockCount m)

/-- Encode a block in little-endian order. -/
def encodeBlock {k : ℕ} (b : Fin k → Bool) : Fin (2 ^ k) :=
  ((BitVec.ofBoolListLE (List.ofFn b)).cast (List.length_ofFn)).toFin

private theorem encodeBlock_injective (k : ℕ) : Function.Injective (@encodeBlock k) := by
  intro a b hab
  funext i
  have h := congrArg (fun x : Fin (2 ^ k) ↦ (BitVec.ofFin x).getLsbD i.val) hab
  simpa only [encodeBlock, BitVec.ofFin_toFin, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
    dif_pos, Option.getD_some] using h

private noncomputable def fairCoin : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

private noncomputable def fairBlock (k : ℕ) : Measure (Fin k → Bool) :=
  Measure.pi fun _ ↦ fairCoin

local instance (k : ℕ) : Nonempty (Fin (2 ^ k)) :=
  ⟨⟨0, by positivity⟩⟩

private noncomputable def uniformBlock (k : ℕ) : Measure (Fin (2 ^ k)) :=
  (PMF.uniformOfFintype (Fin (2 ^ k))).toMeasure

private instance : IsProbabilityMeasure fairCoin := inferInstanceAs
  (IsProbabilityMeasure (PMF.uniformOfFintype Bool).toMeasure)

private instance (k : ℕ) : IsProbabilityMeasure (fairBlock k) := inferInstanceAs
  (IsProbabilityMeasure (Measure.pi fun _ : Fin k ↦ fairCoin))

private instance (k : ℕ) : IsProbabilityMeasure (uniformBlock k) := inferInstanceAs
  (IsProbabilityMeasure (PMF.uniformOfFintype (Fin (2 ^ k))).toMeasure)

private theorem uniformBlock_singleton (k : ℕ) (x : Fin (2 ^ k)) :
    uniformBlock k {x} = (↑(2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
  simp [uniformBlock, PMF.uniformOfFintype_apply]

private theorem map_encodeBlock (k : ℕ) :
    (fairBlock k).map encodeBlock = uniformBlock k := by
  have hinj := encodeBlock_injective k
  have hsurj : Function.Surjective (@encodeBlock k) :=
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩).2
  apply Measure.ext_of_singleton
  intro x
  obtain ⟨b, rfl⟩ := hsurj x
  have hb : encodeBlock ⁻¹' {encodeBlock b} = {b} := by
    ext a
    exact hinj.eq_iff
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hb,
    uniformBlock_singleton, fairBlock, Measure.pi_singleton]
  simp [fairCoin, PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- Independent fair coins indexed by attempt and bit within that attempt. -/
noncomputable def coins (m : ℕ) : Measure (ℕ → Fin (width m) → Bool) :=
  Measure.infinitePi fun _ ↦ fairBlock (width m)

instance (m : ℕ) : IsProbabilityMeasure (coins m) := inferInstanceAs
  (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ fairBlock (width m))))

/-- The induced measure on streams of encoded blocks. -/
noncomputable def blockStream (m : ℕ) : Measure (Blocks m) :=
  Measure.infinitePi fun _ ↦ uniformBlock (width m)

instance (m : ℕ) : IsProbabilityMeasure (blockStream m) := inferInstanceAs
  (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ uniformBlock (width m))))

/-- Encoding the independent fair-bit blocks gives independent uniform integers. -/
theorem map_coins_encode (m : ℕ) :
    (coins m).map (fun bits j ↦ encodeBlock (bits j)) = blockStream m := by
  rw [coins, Measure.infinitePi_map_pi _ (fun _ ↦ measurable_of_countable _), blockStream]
  simp only [map_encodeBlock]

private theorem blockCount_lt_double {m : ℕ} (hm : 0 < m) : blockCount m < 2 * m := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm) with he | hm'
  · subst m
    decide
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hm'
  have hwidth := Nat.clog_pos (by decide : 1 < 2) hm'
  change 2 ^ Nat.clog 2 m < 2 * m
  calc
    2 ^ Nat.clog 2 m = 2 ^ (Nat.clog 2 m).pred * 2 :=
      (congrArg (fun j : ℕ ↦ (2 : ℕ) ^ j) (Nat.succ_pred_eq_of_pos hwidth).symm).trans
        (pow_succ _ _)
    _ < 2 * m := by omega

private abbrev acceptedBlock {m : ℕ} (x : Fin m) : Fin (blockCount m) :=
  x.castLE (Nat.le_pow_clog (by decide) m)

private def rejected (m : ℕ) : Set (Fin (blockCount m)) := {b | m ≤ b.val}

private theorem rejected_eq_compl (m : ℕ) :
    rejected m = (Set.range (@acceptedBlock m))ᶜ := by
  ext b
  simp [rejected]

private theorem acceptedBlock_injective (m : ℕ) :
    Function.Injective (@acceptedBlock m) :=
  fun _ _ h ↦ Fin.ext (congrArg (fun t : Fin (blockCount m) ↦ t.val) h)

noncomputable def acceptProb (m : ℕ) : ℝ≥0∞ := (m : ℝ≥0∞) / (blockCount m : ℝ≥0∞)

noncomputable def rejectProb (m : ℕ) : ℝ≥0∞ := 1 - acceptProb m

private theorem acceptProb_le_one (m : ℕ) : acceptProb m ≤ 1 := by
  rw [acceptProb, ENNReal.div_le_iff (by positivity) (by simp), one_mul]
  exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) m

private theorem acceptProb_inv_lt_two {m : ℕ} (hm : 0 < m) :
    (acceptProb m)⁻¹ < 2 := by
  rw [acceptProb, ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by positivity)),
    ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp))]
  change (blockCount m : ℝ≥0∞) < ((2 : ℕ) : ℝ≥0∞) * (m : ℝ≥0∞)
  exact_mod_cast blockCount_lt_double hm

private theorem rejectProb_lt_one {m : ℕ} (hm : 0 < m) : rejectProb m < 1 :=
  ENNReal.sub_lt_self (by simp) (by simp) (by
    intro hzero
    simpa [hzero] using acceptProb_inv_lt_two hm)

private theorem uniformBlock_rejected (m : ℕ) :
    uniformBlock (width m) (rejected m) = rejectProb m := by
  classical
  rw [rejected_eq_compl, measure_compl MeasurableSet.of_discrete (measure_ne_top _ _),
    measure_univ, rejectProb, acceptProb, uniformBlock,
    PMF.toMeasure_uniformOfFintype_apply _ MeasurableSet.of_discrete]
  rw [Set.card_range_of_injective (acceptedBlock_injective m), Fintype.card_fin, Fintype.card_fin]

/-- The first n blocks all fail the acceptance test. -/
def rejectPrefix (m n : ℕ) : Set (Blocks m) :=
  (Finset.range n : Set ℕ).pi fun _ ↦ rejected m

private theorem measurableSet_rejectPrefix (m n : ℕ) :
    MeasurableSet (rejectPrefix m n) :=
  MeasurableSet.pi (Finset.countable_toSet _) fun _ _ ↦ MeasurableSet.of_discrete

theorem blockStream_rejectPrefix (m n : ℕ) :
    blockStream m (rejectPrefix m n) = (rejectProb m) ^ n := by
  rw [blockStream, rejectPrefix, Measure.infinitePi_pi _ (fun _ _ ↦ MeasurableSet.of_discrete)]
  simp [uniformBlock_rejected]

/-- Block j is the first successful block and encodes x. -/
def acceptAt {m : ℕ} (j : ℕ) (x : Fin m) : Set (Blocks m) :=
  (Finset.range (j + 1) : Set ℕ).pi fun i ↦
    if i = j then {acceptedBlock x} else rejected m

theorem mem_acceptAt {m j : ℕ} {x : Fin m} {s : Blocks m} :
    s ∈ acceptAt j x ↔ s j = acceptedBlock x ∧ ∀ i < j, m ≤ (s i).val := by
  simp only [acceptAt, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro hs
    exact ⟨by simpa using hs j (by omega),
      fun i hi ↦ by simpa [ne_of_lt hi, rejected] using hs i (by omega)⟩
  · rintro ⟨hj, h⟩ i hi
    by_cases he : i = j
    · simpa [he] using hj
    · simpa [he, rejected] using h i (by omega)

private theorem measurableSet_acceptAt {m : ℕ} (j : ℕ) (x : Fin m) :
    MeasurableSet (acceptAt j x) :=
  MeasurableSet.pi (Finset.countable_toSet _) fun _ _ ↦ MeasurableSet.of_discrete

theorem blockStream_acceptAt {m : ℕ} (j : ℕ) (x : Fin m) :
    blockStream m (acceptAt j x) =
      (rejectProb m)^j * (↑(blockCount m) : ℝ≥0∞)⁻¹ := by
  rw [blockStream, acceptAt, Measure.infinitePi_pi _ (fun _ _ ↦ MeasurableSet.of_discrete),
    Finset.prod_range_succ, if_pos rfl, uniformBlock_singleton]
  congr 1
  calc
    _ = ∏ _i ∈ Finset.range j, rejectProb m := Finset.prod_congr rfl fun i hi ↦ by
      rw [if_neg (ne_of_lt (Finset.mem_range.mp hi)), uniformBlock_rejected]
    _ = _ := by simp

/-- Read until the first accepted block. None represents an infinite rejection path. -/
noncomputable def draw {m : ℕ} (s : Blocks m) : Option (Fin m) :=
  open Classical in
  if h : ∃ i, (s i).val < m then
    some ⟨(s (Nat.find h)).val, Nat.find_spec h⟩
  else none

private theorem draw_fiber {m : ℕ} (x : Fin m) :
    draw ⁻¹' {some x} = ⋃ j, acceptAt j x := by
  classical
  ext s
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, mem_acceptAt, draw]
  split_ifs with h
  · constructor
    · intro hs
      exact ⟨Nat.find h, Fin.ext (congrArg (fun y : Fin m ↦ y.val) (Option.some.inj hs)),
        fun i hi ↦ Nat.le_of_not_lt (Nat.find_min h hi)⟩
    · rintro ⟨j, hj, hp⟩
      have ha : (s j).val < m := by simp [hj]
      have hfind : Nat.find h = j := (Nat.find_eq_iff h).mpr
        ⟨ha, fun i hi ↦ Nat.not_lt_of_ge (hp i hi)⟩
      exact congrArg some (Fin.ext (by simpa [hfind] using congrArg Fin.val hj))
  · simp only [false_iff, not_exists]
    rintro j ⟨hj, _⟩
    exact h ⟨j, by simp [hj]⟩

private theorem draw_none_fiber (m : ℕ) :
    (@draw m) ⁻¹' {none} = ⋂ n, rejectPrefix m n := by
  classical
  ext s
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, draw, rejectPrefix,
    Set.mem_pi, Finset.mem_coe, Finset.mem_range, rejected, Set.mem_ofPred_eq]
  split_ifs with h
  · simp only [false_iff, not_forall]
    obtain ⟨n, hn⟩ := h
    exact ⟨n + 1, n, by omega, Nat.not_le_of_lt hn⟩
  · simpa only [true_iff] using fun _ i _ ↦ Nat.le_of_not_lt (fun hi ↦ h ⟨i, hi⟩)

instance (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

theorem measurable_draw (m : ℕ) : Measurable (@draw m) := by
  apply measurable_to_countable'
  intro x
  cases x with
  | none =>
    rw [draw_none_fiber]
    exact MeasurableSet.iInter (measurableSet_rejectPrefix m)
  | some x =>
    rw [draw_fiber]
    exact MeasurableSet.iUnion fun j ↦ measurableSet_acceptAt j x

private theorem acceptAt_pairwise {m : ℕ} (x : Fin m) :
    Pairwise (Function.onFun Disjoint fun j ↦ acceptAt j x) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro s hi hj
  obtain ⟨hi, hip⟩ := mem_acceptAt.mp hi
  obtain ⟨hj, hjp⟩ := mem_acceptAt.mp hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (Nat.not_le_of_lt (by simp [hi])) (hjp i hlt)
  · exact (Nat.not_le_of_lt (by simp [hj])) (hip j hgt)

theorem draw_uniform {m : ℕ} (x : Fin m) :
    (blockStream m).map draw {some x} = (m : ℝ≥0∞)⁻¹ := by
  rw [Measure.map_apply (measurable_draw _) (measurableSet_singleton _), draw_fiber,
    measure_iUnion (acceptAt_pairwise x) (fun j ↦ measurableSet_acceptAt j x)]
  simp only [blockStream_acceptAt, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  have hm : 0 < m := Nat.zero_lt_of_lt x.isLt
  rw [rejectProb, ENNReal.sub_sub_cancel (by simp) (acceptProb_le_one _), acceptProb,
    ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by positivity)), ENNReal.div_eq_inv_mul,
    mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by simp), mul_one]

theorem draw_terminates {m : ℕ} (hm : 0 < m) :
    (blockStream m).map draw {none} = 0 := by
  rw [Measure.map_apply (measurable_draw _) (measurableSet_singleton _), draw_none_fiber]
  have h := tendsto_measure_iInter_atTop
    (fun n ↦ (measurableSet_rejectPrefix m n).nullMeasurableSet)
    (show Antitone (rejectPrefix m) from fun _ _ hle _ hs i hi ↦
      hs i (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hle)))
    ⟨0, measure_ne_top _ _⟩ (μ := blockStream m)
  have hc : (blockStream m) ∘ rejectPrefix m = fun n ↦ rejectProb m ^ n :=
    funext (blockStream_rejectPrefix m)
  rw [hc] at h
  exact tendsto_nhds_unique h (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (rejectProb_lt_one hm))

/-- A block is read exactly when all previous blocks have been rejected. -/
noncomputable def bitsUsed (m : ℕ) (s : Blocks m) : ℝ≥0∞ :=
  ∑' n, (rejectPrefix m n).indicator (fun _ ↦ (width m : ℝ≥0∞)) s

theorem bitsUsed_of_acceptAt {m j : ℕ} {x : Fin m} {s : Blocks m}
    (h : s ∈ acceptAt j x) :
    bitsUsed m s = ((j + 1 : ℕ) : ℝ≥0∞) * (width m : ℝ≥0∞) := by
  obtain ⟨hj, hp⟩ := mem_acceptAt.mp h
  have hn (n : ℕ) : s ∈ rejectPrefix m n ↔ n ≤ j := by
    simp only [rejectPrefix, Set.mem_pi, Finset.mem_coe, Finset.mem_range, rejected,
      Set.mem_ofPred_eq]
    constructor
    · intro hr
      by_contra! hlt
      exact (Nat.not_le_of_lt (by simp [hj])) (hr j hlt)
    · intro hle i hi
      exact hp i (hi.trans_le hle)
  unfold bitsUsed
  rw [tsum_eq_sum (s := Finset.range (j + 1)) (fun n hnmem ↦
    Set.indicator_of_notMem (fun hr ↦ hnmem (Finset.mem_range.mpr (Nat.lt_succ_of_le ((hn n).mp hr)))) _)]
  rw [Finset.sum_congr rfl (fun n hmem ↦
    Set.indicator_of_mem ((hn n).mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hmem))) _),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem expectedBits (m : ℕ) :
    ∫⁻ s, bitsUsed m s ∂blockStream m = (width m : ℝ≥0∞) * (acceptProb m)⁻¹ := by
  unfold bitsUsed
  rw [lintegral_tsum (fun n ↦
    (measurable_const.indicator (measurableSet_rejectPrefix m n)).aemeasurable)]
  simp only [lintegral_indicator_const (measurableSet_rejectPrefix _ _),
    blockStream_rejectPrefix, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  rw [rejectProb, ENNReal.sub_sub_cancel (by simp) (acceptProb_le_one _)]

theorem expectedBits_lt {m : ℕ} (hm : 1 < m) :
    ∫⁻ s, bitsUsed m s ∂blockStream m < 2 * (width m : ℝ≥0∞) := by
  rw [expectedBits, mul_comm (2 : ℝ≥0∞)]
  have hw := Nat.clog_pos (by decide : 1 < 2) hm
  exact ENNReal.mul_lt_mul_right (by positivity : (width m : ℝ≥0∞) ≠ 0)
    (by simp) (acceptProb_inv_lt_two (m := m) (by omega))

@[simp] theorem bitsUsed_one (s : Blocks 1) : bitsUsed 1 s = 0 := by
  simp [bitsUsed]

private theorem measurable_encode (m : ℕ) :
    Measurable (fun (bits : ℕ → Fin (width m) → Bool) j ↦ encodeBlock (bits j)) :=
  measurable_pi_lambda _ fun j ↦ (measurable_of_countable (@encodeBlock (width m))).comp (measurable_pi_apply j)

/-- Given a fair bit tape, the rejection sampler returns an index in the range. -/
noncomputable def drawCoins {m : ℕ} (bits : ℕ → Fin (width m) → Bool) : Option (Fin m) :=
  draw (fun j ↦ encodeBlock (bits j))

@[simp] theorem drawCoins_one (bits : ℕ → Fin (width 1) → Bool) :
    drawCoins bits = some 0 := by
  have hx : ∃ j, (encodeBlock (bits j)).val < 1 := ⟨0, (encodeBlock (bits 0)).isLt⟩
  unfold drawCoins draw
  rw [dif_pos hx]
  exact congrArg some (Subsingleton.elim _ _)

theorem drawCoins_uniform {m : ℕ} (x : Fin m) :
    (coins m).map drawCoins {some x} = (m : ℝ≥0∞)⁻¹ := by
  change (coins m).map (draw ∘ fun bits j ↦ encodeBlock (bits j)) _ = _
  rw [← Measure.map_map (measurable_draw m) (measurable_encode m), map_coins_encode]
  exact draw_uniform x

theorem drawCoins_terminates {m : ℕ} (hm : 0 < m) :
    (coins m).map (@drawCoins m) {none} = 0 := by
  change (coins m).map (draw ∘ fun bits j ↦ encodeBlock (bits j)) _ = _
  rw [← Measure.map_map (measurable_draw m) (measurable_encode m), map_coins_encode]
  exact draw_terminates hm

theorem expectedCoins (m : ℕ) :
    (∫⁻ bits, bitsUsed m (fun j ↦ encodeBlock (bits j)) ∂coins m) =
      (width m : ℝ≥0∞) * (acceptProb m)⁻¹ := by
  have hb : Measurable (bitsUsed m) :=
    Measurable.tsum fun n ↦ measurable_const.indicator (measurableSet_rejectPrefix m n)
  rw [← lintegral_map hb (measurable_encode m), map_coins_encode, expectedBits]

theorem expectedCoins_lt {m : ℕ} (hm : 1 < m) :
    (∫⁻ bits, bitsUsed m (fun j ↦ encodeBlock (bits j)) ∂coins m) <
      2 * (width m : ℝ≥0∞) := by
  rw [expectedCoins, ← expectedBits]
  exact expectedBits_lt hm

end Cogentic.RandomizedUniformBits
