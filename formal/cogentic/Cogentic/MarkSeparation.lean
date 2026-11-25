import Cogentic.ConstructionBrackets
import Cogentic.Concrete

namespace Cogentic.Construction

theorem grid_separation {d A W a : ℕ} (scale : 16*d ≤ W) (grid : onGrid d A W a)
    (side : Bool) (j : Fin d) :
    (W:ℚ)⁻¹ ≤ |(a:ℚ)/A-center d side j.val| := by
  let t := (a:ℚ)/A
  let w := (W:ℚ)⁻¹
  let k := 2*j.val+(if side then 2 else 1)
  have dp : 0 < d := Nat.zero_lt_of_lt j.isLt
  have wp : 0 < W := by omega
  have small : w ≤ 1/(16*(d:ℚ)) := by
    simpa only [w,one_div] using one_div_le_one_div_of_le (by positivity : (0:ℚ)<16*d)
      (by exact_mod_cast scale : (16:ℚ)*d ≤ W)
  have room : 4*w ≤ 1/(4*(d:ℚ)) := by
    calc 4*w ≤ 4*(1/(16*(d:ℚ))) := by linarith
         _ = _ := by ring
  have cap : w ≤ 1/4 := small.trans (one_div_le_one_div_of_le (by norm_num) (by
    have : (1:ℚ) ≤ d := by exact_mod_cast dp
    linarith))
  have pos : 0 ≤ w := by dsimp [w]; positivity
  have kn : k ≤ 2*d := by dsimp [k]; cases side <;> simp <;> omega
  have kr : (k:ℚ)/(4*d) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have : (k:ℚ) ≤ 2*d := by exact_mod_cast kn
    linarith
  change w ≤ |t-(k:ℚ)/(4*d)|
  simp only [onGrid,Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true,
    List.mem_append,List.mem_map,targets] at grid
  rcases grid with base | ⟨r,mem,interval⟩
  · exact (show w ≤ t-(k:ℚ)/(4*d) by linarith [base.1]).trans (le_abs_self _)
  · have repr : ∃ l : ℕ, r = (l:ℚ)/(4*d) := by
      rcases mem with ⟨i,_,eq⟩ | ⟨i,_,eq⟩
      · exact ⟨2*i+1,eq.symm⟩
      · exact ⟨2*i+2,eq.symm⟩
    obtain ⟨l,rfl⟩ := repr
    change (l:ℚ)/(4*d)+w ≤ t ∧ t ≤ (l:ℚ)/(4*d)+2*w at interval
    rcases le_or_gt k l with later | earlier
    · have order := div_le_div_of_nonneg_right (show (k:ℚ) ≤ l by exact_mod_cast later)
          (show (0:ℚ) ≤ 4*d by positivity)
      exact (show w ≤ t-(k:ℚ)/(4*d) by linarith [interval.1]).trans (le_abs_self _)
    · have order : (l:ℚ)/(4*d)+1/(4*d) ≤ (k:ℚ)/(4*d) := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast earlier
      exact (show w ≤ -(t-(k:ℚ)/(4*d)) by linarith [interval.2]).trans (neg_le_abs _)

/-- All retained marks stay far enough from every real root bracket to pass
the actual logarithm guard, uniformly in the coefficient box. -/
theorem retained_bracket_separation {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 10004 ≤ Fixed.d (n.log2+1)) :
    let b := n.log2+1
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    ∀ {rel}, Marking.stageOne s = some rel → ∀ a ∈ rel.marks, ∀ side (j : Fin s.degree) (x : ℝ),
      x ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ) →
      2*(1/2:ℝ)^(b+1) ≤ |(a:ℝ)/s.A-x| := by
  intro b s rel stage a ha side j x hx
  let W := Fixed.invWidth b
  let h := Fixed.h b
  let c := center s.degree side j.val
  let δ := (1/2:ℝ)^(95*h)
  have params := Fixed.stage_guards hn big
  have hp : 0 < h := Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _)) (Nat.succ_pos _)
  have eligible := ((Marking.retained_iff stage a).mp ha).1
  simp only [Marking.Input.eligibleMarks,Finset.mem_sort,Finset.mem_filter,List.mem_toFinset] at eligible
  have grid : onGrid s.degree s.A W a = true := by
    have ok := (List.mem_filter.mp eligible.1).2
    simp only [Bool.and_eq_true] at ok
    exact ok.1
  have gap := grid_separation params.roots.1 grid side j
  have gapR : (W:ℝ)⁻¹ ≤ |(a:ℝ)/s.A-c| := by
    have cast := (Rat.cast_le (K := ℝ)).mpr gap
    push_cast at cast
    exact cast
  have br : (19*s.K₁.log2+19)/20 = 95*h := by
    change (19*(2^(100*h)).log2+19)/20 = 95*h
    rw [Nat.log2_two_pow]; omega
  change (((c-(1/2:ℚ)^((19*s.K₁.log2+19)/20)):ℚ):ℝ) ≤ x ∧
    x ≤ (((c+(1/2:ℚ)^((19*s.K₁.log2+19)/20)):ℚ):ℝ) at hx
  rw [br] at hx
  push_cast at hx
  have near : |x-(c:ℝ)| ≤ δ := abs_le.mpr ⟨by dsimp [δ]; linarith [hx.1],by dsimp [δ]; linarith [hx.2]⟩
  have wr : (W:ℝ)⁻¹ = (1/2:ℝ)^(3*h) := by simp [W,Fixed.invWidth,h]
  have half : δ ≤ (W:ℝ)⁻¹/2 := by
    rw [wr,show (1/2:ℝ)^(3*h)/2 = (1/2:ℝ)^(3*h+1) by rw [pow_succ]; ring]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have widths := params.roots.2.2
  have floor : (1/2:ℝ)^b ≤ (W:ℝ)⁻¹/2 := by
    rw [one_div_pow,← one_div,div_div]
    apply one_div_le_one_div_of_le (by dsimp [W,Fixed.invWidth]; positivity)
    exact_mod_cast (show W*2 ≤ 2^b by simpa [Nat.mul_comm] using widths)
  have tri := abs_sub_le ((a:ℝ)/s.A) x (c:ℝ)
  rw [pow_succ]
  linarith

/-- Both families of roots and every mark logarithm used by the numerical
extractor exist at the implemented precisions. The real roots in the error
bound are common to all marks. -/
theorem constructed_mark_logs {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 10004 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    ∀ {rel}, Marking.stageOne s = some rel →
    let P := TryPair.localBits s rel
    ∃ (r : Bool → Fin s.degree → ℚ) (x : Bool → Fin s.degree → ℝ)
      (v : Fin rel.marks.length → Bool → Fin s.degree → ℚ),
      (∀ side j, RootLogs.isolate s side j (2*P) = some (r side j) ∧
        x side j ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ) ∧
        RootLogs.normalized s.A (s.coeffs side) (x side j) = 0 ∧ |(r side j:ℝ)-x side j| ≤ (1/2:ℝ)^(2*P)) ∧
      (∀ i side j, RootLogs.markLog s.A (rel.marks.get i) (r side j) s.L₀ (2*P+16) = some (v i side j) ∧
        |(v i side j:ℝ)-Real.log (|(rel.marks.get i:ℝ)/s.A-x side j|)| ≤
          (1/2:ℝ)^(2*P+16)+(1/2:ℝ)^(2*P)/(1/2:ℝ)^(s.L₀+1)) ∧
      (Concrete.markColumns s rel).isSome := by
  intro s rel stage P
  have roots := fun side j => constructed_isolate hn big target box side j (2*P)
  choose r ok x inside zero near using roots
  have dp : 1 ≤ s.degree := by change 1 ≤ Fixed.d (n.log2+1); omega
  have bp : 1 ≤ s.L₀ := Nat.succ_pos _
  have bits : s.L₀+1 ≤ 2*P := by
    have fit : s.L₀ ≤ (64*s.degree^3*(rel.rows.length+1))*s.L₀ :=
      Nat.le_mul_of_pos_left _ (by positivity)
    change s.L₀+1 ≤ 2*(64*s.degree^3*(rel.rows.length+1)*s.L₀)
    omega
  have error := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) bits
  have logs (i : Fin rel.marks.length) side j :=
    RootLogs.markLog_of_separated (bits := 2*P+16) (near side j) error
      (retained_bracket_separation hn big stage _ (rel.marks.get_mem i) side j _ (inside side j))
  choose v computed close using logs
  refine ⟨r,x,v,fun side j => ⟨ok side j,inside side j,zero side j,near side j⟩,
    fun i side j => ⟨computed i side j,close i side j⟩,?_⟩
  rw [Concrete.markColumns_values s rel r v ok computed]; rfl

end Cogentic.Construction
