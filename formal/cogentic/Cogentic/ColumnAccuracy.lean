import Cogentic.MarkSeparation
import Cogentic.ArchPrecision

namespace Cogentic.Construction

private theorem mark_distance_upper {s : Marking.Input} {rel : Marking.Relations}
    (stage : Marking.stageOne s = some rel) {a : ℕ} (ha : a ∈ rel.marks)
    (side : Bool) (j : Fin s.degree) (x : ℝ)
    (hx : x ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ)) :
    |(a:ℝ)/s.A-x| ≤ 2 := by
  have eligible := ((Marking.retained_iff stage a).mp ha).1
  simp only [Marking.Input.eligibleMarks,Finset.mem_sort,Finset.mem_filter] at eligible
  have fit := eligible.2.2.1
  have Ap : 0 < s.A := eligible.2.1.trans fit
  have ratio : (a:ℝ)/s.A ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast fit)
  have dp : 0 < s.degree := Nat.zero_lt_of_lt j.isLt
  let k := 2*j.val+(if side then 2 else 1)
  have upper : k ≤ 4*s.degree := by dsimp [k]; cases side <;> simp <;> omega
  have cent : (k:ℝ)/(4*s.degree) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by exact_mod_cast upper)
  have wid := pow_le_one₀ (n := (19*s.K₁.log2+19)/20)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
  change (((((k:ℚ)/(4*s.degree))-(1/2:ℚ)^((19*s.K₁.log2+19)/20)):ℚ):ℝ) ≤ x ∧
    x ≤ (((((k:ℚ)/(4*s.degree))+(1/2:ℚ)^((19*s.K₁.log2+19)/20)):ℚ):ℝ) at hx
  push_cast at hx
  rw [abs_le]
  constructor <;> linarith [hx.1,hx.2,show (0:ℝ) ≤ (a:ℝ)/s.A by positivity,
    show (0:ℝ) ≤ (k:ℝ)/(4*s.degree) by positivity]

noncomputable def markLogAt {d : ℕ} (x : Bool → Fin d → ℝ) (a A : ℕ) (side : Bool) (k : ℕ) : ℝ :=
  if h : k < d then Real.log (|(a:ℝ)/A-x side ⟨k,h⟩|) else 0

private theorem markLogAt_fin {d : ℕ} (x : Bool → Fin d → ℝ) (a A : ℕ) (side : Bool) (k : Fin d) :
    markLogAt x a A side k.val = Real.log (|(a:ℝ)/A-x side k|) := dif_pos k.isLt

/-- Uniform precision of the actual returned column matrix at every retained
mark, relative to the Helmert coordinates of the certified real roots. -/
theorem constructed_column_accuracy {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 10004 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    ∀ {rel}, Marking.stageOne s = some rel →
    let P := TryPair.localBits s rel
    ∃ (x : Bool → Fin s.degree → ℝ) (cols : Vector (Vector ℚ (2*s.degree-2)) rel.marks.length),
      (∀ side j, x side j ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ) ∧
        RootLogs.normalized s.A (s.coeffs side) (x side j) = 0) ∧ Concrete.markColumns s rel = some cols ∧
      ∀ i row,
        let side := decide (s.degree-1 ≤ row.val)
        let j := row.val%(s.degree-1)+1
        let z := helmertCoordinate (markLogAt x (rel.marks.get i) s.A side) j
        |((cols.get i).get row:ℝ)-z| ≤ (1/2:ℝ)^P ∧ |z| ≤ 2*s.degree*((s.L₀:ℝ)+1) := by
  intro s rel stage P
  obtain ⟨r,x,v,roots,logs,_⟩ := constructed_mark_logs hn big target box stage
  have eq := Concrete.markColumns_values s rel r v (fun side j => (roots side j).1)
    (fun i side j => (logs i side j).1)
  dsimp only at eq
  refine ⟨x,_,fun side j => ⟨(roots side j).2.1,(roots side j).2.2.1⟩,eq,?_⟩
  intro i row side j z
  have dp : 2 ≤ s.degree := by change 2 ≤ Fixed.d (n.log2+1); omega
  have jlt : j < s.degree := by
    have m := Nat.mod_lt row.val (by omega : 0 < s.degree-1)
    dsimp [j]; omega
  have jp : 1 ≤ j := Nat.succ_pos _
  let L := markLogAt x (rel.marks.get i) s.A side
  have entry (k : ℕ) (hk : k ≤ j) : k < s.degree := hk.trans_lt jlt
  have bounds (k : ℕ) (hk : k ≤ j) : |L k| ≤ s.L₀+1 := by
    let ix : Fin s.degree := ⟨k,entry k hk⟩
    have mem := (roots side ix).2.1
    have sep := retained_bracket_separation hn big stage _ (rel.marks.get_mem i) side ix _ mem
    change 2*(1/2:ℝ)^(s.L₀+1) ≤ |(rel.marks.get i:ℝ)/s.A-x side ix| at sep
    have pos := pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (s.L₀+1)
    have low : (1/2:ℝ)^(s.L₀+1) ≤ |(rel.marks.get i:ℝ)/s.A-x side ix| := by linarith
    have id : L k = Real.log (|(rel.marks.get i:ℝ)/s.A-x side ix|) := markLogAt_fin x _ _ side ix
    rw [id]
    exact ArchPrecision.separated_log_bound low (mark_distance_upper stage (rel.marks.get_mem i) side ix _ mem)
  have acc := ArchPrecision.projected_mark_precision (d := s.degree) (R := rel.rows.length+1)
    (b := s.L₀) (by omega) (Nat.succ_pos _) (Nat.succ_pos _) jp jlt.le (Vector.ofFn (v i side)) L
  simp only [Vector.get_eq_getElem,Vector.getElem_ofFn]
  refine acc ?_ bounds
  intro k hk
  let ix : Fin s.degree := ⟨k,entry k hk⟩
  have h := (logs i side ix).2
  have z0 : L k = Real.log (|(rel.marks.get i:ℝ)/s.A-x side ix|) := markLogAt_fin x _ _ side ix
  rw [z0]
  simpa [Vector.toArray_ofFn,entry k hk,ix,s,TryPair.localBits] using h

end Cogentic.Construction
