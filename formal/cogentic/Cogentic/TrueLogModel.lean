import Cogentic.MarkSeparation
import Cogentic.RootGridEnergy

/-! Error from replacing the two fields' actual bracket roots by their nominal
centers inside the empirical Gram on retained marks. -/

namespace Cogentic.Construction
open scoped BigOperators
open Real

/-- The error at a retained mark is at most twice the root bracket radius
divided by the mark interval width. The fixed parameters give 2·2^(-92h). -/
theorem retained_true_log_error {n ell a b c d : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1)) :
    let bits := n.log2+1
    let s := TryPair.fixedInput n ell (construct n ell a b c d)
    ∀ {rel}, Marking.stageOne s = some rel → ∀ mark ∈ rel.marks, ∀ side (j : Fin s.degree) (x : ℝ),
      x ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ) →
      abs (log |(mark:ℝ)/s.A-x| - log |(mark:ℝ)/s.A-(center s.degree side j.val:ℝ)|) ≤
        2*(1/2:ℝ)^(92*Fixed.h bits) := by
  intro bits s rel marked mark included side j x hx
  let h := Fixed.h bits
  let W := Fixed.invWidth bits
  let w := (1/2:ℝ)^(3*h)
  let rad := (1/2:ℝ)^(95*h)
  let ctr := center s.degree side j.val
  let pt := (mark:ℝ)/s.A
  have hpos : 0 < h := Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _)) (Nat.succ_pos _)
  have eligible := ((Marking.retained_iff marked mark).mp included).1
  simp only [Marking.Input.eligibleMarks,Finset.mem_sort,Finset.mem_filter,List.mem_toFinset] at eligible
  have grid : onGrid s.degree s.A W mark = true := by
    have good := (List.mem_filter.mp eligible.1).2
    simp only [Bool.and_eq_true] at good
    exact good.1
  have dist : w ≤ |pt-(ctr:ℝ)| := by
    have rat := grid_separation (Fixed.stage_guards hn big).roots.1 grid side j
    have cast := (Rat.cast_le (K:=ℝ)).mpr rat
    push_cast at cast
    have eq : (W:ℝ)⁻¹ = w := by simp [W,Fixed.invWidth,w,h]
    rw [←eq]
    exact cast
  have br : (19*s.K₁.log2+19)/20 = 95*h := by
    change (19*(2^(100*h)).log2+19)/20 = 95*h
    rw [Nat.log2_two_pow]; omega
  change (((ctr-(1/2:ℚ)^((19*s.K₁.log2+19)/20)):ℚ):ℝ) ≤ x ∧
    x ≤ (((ctr+(1/2:ℚ)^((19*s.K₁.log2+19)/20)):ℚ):ℝ) at hx
  rw [br] at hx
  push_cast at hx
  have near : |x-(ctr:ℝ)| ≤ rad := abs_le.mpr ⟨by dsimp [rad]; linarith [hx.1],
    by dsimp [rad]; linarith [hx.2]⟩
  have tiny : rad ≤ w/2 := by
    rw [show w/2=(1/2:ℝ)^(3*h+1) by rw [pow_succ]; dsimp [w]; ring]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have dist' : w/2 ≤ |pt-x| := by linarith [abs_sub_le pt x ctr]
  have wp : 0 < w/2 := by dsimp [w]; positivity
  have lip := RootLogs.log_lipschitz wp dist' (by linarith : w/2 ≤ |pt-(ctr:ℝ)|)
  have err : abs (|pt-x| - |pt-(ctr:ℝ)|) ≤ rad := by
    calc
      _ ≤ |(pt-x)-(pt-(ctr:ℝ))| := abs_abs_sub_abs_le ..
      _ = |x-(ctr:ℝ)| := by rw [show (pt-x)-(pt-(ctr:ℝ)) = -(x-(ctr:ℝ)) by ring,abs_neg]
      _ ≤ _ := near
  have result := lip.trans (div_le_div_of_nonneg_right err wp.le)
  have exp : 95*h = 3*h+92*h := by omega
  have cancel : rad/(w/2) = 2*(1/2:ℝ)^(92*h) := by
    dsimp [rad,w]
    rw [exp,pow_add]
    field_simp
  exact result.trans_eq cancel

/-- Squared error of a full linear score under arbitrary nonnegative retained
mark weights. This comparison applies before the Gram weights are normalized. -/
theorem weighted_log_score_error {α β : Type*} [Fintype α] [Fintype β]
    (weight : α → ℝ) (old new : α → β → ℝ) (v : β → ℝ) (ε : ℝ)
    (mass : ∀ a, 0 ≤ weight a) (bound : ∀ a i, |new a i-old a i| ≤ ε) :
    ∑ a, weight a*(∑ i, (new a i-old a i)*v i)^2 ≤
      (∑ a, weight a)*(Fintype.card β*ε^2)*(∑ i, (v i)^2) := by
  have each (a) : (∑ i, (new a i-old a i)*v i)^2 ≤ (Fintype.card β*ε^2)*(∑ i, (v i)^2) := by
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => new a i-old a i) v
    have E : ∑ i, (new a i-old a i)^2 ≤ (Fintype.card β:ℝ)*ε^2 := by
      have row (i) : (new a i-old a i)^2 ≤ ε^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (bound a i) 2
      simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => row i)
    exact cs.trans (mul_le_mul_of_nonneg_right E (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  simpa only [← Finset.sum_mul,mul_assoc] using Finset.sum_le_sum (s:=Finset.univ)
    (fun a _ => mul_le_mul_of_nonneg_left (each a) (mass a))

end Cogentic.Construction

#print axioms Cogentic.Construction.retained_true_log_error
